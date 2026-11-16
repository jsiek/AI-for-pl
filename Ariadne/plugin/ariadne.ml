(* Ariadne: ghost liveness instrumentation for use-after-free.

   With -ariadne, for every function definition:
   - before every memory access that RTE would check, add
       assert live: !dead(__heap, \base_addr(&lv));
   - for every address-taken variable x (locals at the start of their
     block, formals and globals at the start of the body), add
       admit stack: !heap(\base_addr(&x));
   and abort if any call to malloc/calloc/realloc/free remains.

   The ghost model (__heap, heap, dead) and the allocator contracts come
   from share/ariadne_alloc.h; see plan.md section 10 and
   m1a/README.md. *)

open Cil_types

module Self = Plugin.Register (struct
  let name = "Ariadne"
  let shortname = "ariadne"
  let help = "ghost liveness instrumentation for use-after-free"
end)

module Enabled = Self.False (struct
  let option_name = "-ariadne"
  let help =
    "add a live assert before every memory access and a stack admit for \
     every address-taken variable (needs ariadne_alloc.h)"
end)

let emitter =
  Emitter.create "ariadne" [ Emitter.Code_annot ] ~correctness:[] ~tuning:[]

(* -------------------------------------------------------------------- *)
(* The ghost model                                                      *)
(* -------------------------------------------------------------------- *)

type model = { heap : logic_info; dead : logic_info; version : varinfo }

let find_predicate name arity =
  match
    List.filter
      (fun li -> List.length li.l_profile = arity)
      (Logic_env.find_all_logic_functions name)
  with
  | [ li ] -> li
  | _ ->
    Self.abort "predicate %s/%d not found; include ariadne_alloc.h" name arity

let find_version () =
  let found = ref None in
  Globals.Vars.iter (fun vi _ -> if vi.vname = "__heap" then found := Some vi);
  match !found with
  | Some vi -> vi
  | None -> Self.abort "ghost variable __heap not found; include ariadne_alloc.h"

let find_model () =
  { heap = find_predicate "heap" 1;
    dead = find_predicate "dead" 2;
    version = find_version () }

(* \base_addr(addr), at the current program point. *)
let base_addr ~loc addr =
  Logic_const.term ~loc
    (Tbase_addr (Logic_const.here_label, addr))
    (Ctype Cil_const.charPtrType)

let addr_of_lval ~loc lv =
  Logic_utils.expr_to_term ~coerce:false (Cil.mkAddrOrStartOf ~loc lv)

let named name p = { p with pred_name = [ name ] }

(* !dead(__heap, \base_addr(addr)) *)
let live_pred m ~loc addr =
  let version =
    Logic_utils.numeric_coerce Linteger
      (Logic_const.tvar ~loc (Cil.cvar_to_lvar m.version))
  in
  named "live"
    (Logic_const.pnot ~loc
       (Logic_const.papp ~loc (m.dead, [], [ version; base_addr ~loc addr ])))

(* !heap(\base_addr(&x)) *)
let stack_pred m ~loc vi =
  let addr = addr_of_lval ~loc (Cil.var vi) in
  named "stack"
    (Logic_const.pnot ~loc
       (Logic_const.papp ~loc (m.heap, [], [ base_addr ~loc addr ])))

let add_annot kind kf stmt p =
  Annotations.add_code_annot emitter ~kf stmt
    (Logic_const.new_code_annotation
       (AAssert ([], Logic_const.toplevel_predicate ~kind p)))

(* -------------------------------------------------------------------- *)
(* Raw allocation is not allowed                                        *)
(* -------------------------------------------------------------------- *)

let raw_allocators = [ "malloc"; "calloc"; "realloc"; "free"; "aligned_alloc" ]

(* Any use of a raw allocator is refused, not only direct calls: taking
   its address and calling through a pointer would bypass the ghost model.
   CIL keeps `T *p = malloc(...)` as Local_init/ConsInit, whose callee is
   not an ordinary variable use, so that form is matched explicitly. *)
let check_no_raw_allocation () =
  let found = ref [] in
  let record vi =
    if List.mem vi.vname raw_allocators then begin
      let loc = Current_loc.get () in
      if not (List.mem (vi.vname, loc) !found) then
        found := (vi.vname, loc) :: !found
    end
  in
  let visitor =
    object
      inherit Visitor.frama_c_inplace
      method! vinst i =
        (match i with
         | Local_init (_, ConsInit (vi, _, _), _) -> record vi
         | _ -> ());
        Cil.DoChildren
      method! vvrbl vi = record vi; Cil.SkipChildren
    end
  in
  Visitor.visitFramacFileSameGlobals visitor (Ast.get ());
  List.iter
    (fun (name, loc) ->
       Self.error ~source:(fst loc)
         "use of %s; use the ariadne allocators (ariadne_alloc.h)" name)
    (List.rev !found);
  if !found <> [] then Self.abort "raw allocation calls remain"

(* -------------------------------------------------------------------- *)
(* Instrumentation                                                      *)
(* -------------------------------------------------------------------- *)

type counts = { mutable accesses : int; mutable admits : int }

(* Variables whose storage a pointer may reach.  CIL sets vaddrof for &x,
   but not when only a field's address is taken (&s.f), so every struct,
   union, and array variable is included too.  Admitting !heap(&x) for an
   extra variable is harmless: it holds for every variable. *)
let address_taken vi =
  not vi.vghost
  && (vi.vaddrof || Ast_types.is_struct_or_union vi.vtype
      || Ast_types.is_array vi.vtype)

(* One live assert per distinct l-value accessed by a statement. *)
let instrument_accesses m counts kf fd =
  let seen = Hashtbl.create 17 in
  let flags = { RteGen.Flags.none with mem_access = true; remove_trivial = true } in
  let on_alarm kf stmt ~invalid:_ = function
    | Alarms.Memory_access (lv, _) ->
      let key = (stmt.sid, Format.asprintf "%a" Printer.pp_lval lv) in
      if not (Hashtbl.mem seen key) then begin
        Hashtbl.add seen key ();
        let loc = Cil_datatype.Stmt.loc stmt in
        add_annot Assert kf stmt (live_pred m ~loc (addr_of_lval ~loc lv));
        counts.accesses <- counts.accesses + 1
      end
    | _ -> ()
  in
  List.iter (fun s -> RteGen.Visit.iter_stmt ~flags on_alarm kf s s) fd.sallstmts

let admit_vars m counts kf stmt vars =
  List.iter
    (fun vi ->
       if address_taken vi then begin
         let loc = Cil_datatype.Stmt.loc stmt in
         add_annot Admit kf stmt (stack_pred m ~loc vi);
         counts.admits <- counts.admits + 1
       end)
    vars

let address_taken_globals () =
  let gs = ref [] in
  Globals.Vars.iter (fun vi _ -> if address_taken vi then gs := vi :: !gs);
  List.rev !gs

(* Locals at the start of their own block; formals and globals at the start
   of the function body. *)
let instrument_stack m counts globals kf fd =
  (match fd.sbody.bstmts with
   | first :: _ -> admit_vars m counts kf first (fd.sformals @ globals)
   | [] -> ());
  let visitor =
    object
      inherit Visitor.frama_c_inplace
      method! vblock b =
        (match b.bstmts with
         | first :: _ -> admit_vars m counts kf first b.blocals
         | [] -> ());
        Cil.DoChildren
    end
  in
  ignore (Visitor.visitFramacBlock visitor fd.sbody)

let run () =
  if Enabled.get () then begin
    Enabled.off ();
    check_no_raw_allocation ();
    let m = find_model () in
    let counts = { accesses = 0; admits = 0 } in
    let globals = address_taken_globals () in
    Globals.Functions.iter (fun kf ->
        match kf.fundec with
        | Definition (fd, _) ->
          instrument_accesses m counts kf fd;
          instrument_stack m counts globals kf fd
        | Declaration _ -> ());
    Self.result "%d live asserts, %d stack admits"
      counts.accesses counts.admits
  end

let () = Boot.Main.extend run
