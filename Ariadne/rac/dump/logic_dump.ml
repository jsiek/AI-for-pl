(* logic_dump: write the ACSL logic definitions of a C file as JSON.

   With -logic-dump <file.json>, after parsing and typing, every global
   logic declaration (predicate, logic function, inductive, lemma, axiom,
   axiomatic, logic type) is written to <file.json> as a typed tree:
   Frama-C's own parser and type checker do the work, so the generator
   (../gen_twins.py) never parses ACSL text.  Each term and predicate
   node carries its kind, its operands, its logic type, and its text as
   printed by Frama-C ("pp", for diagnostics).  Constructs the generator
   has no rule for are still dumped (kind "other" with "pp"), so it can
   name them in a diagnostic. *)

open Cil_types

module Self = Plugin.Register (struct
  let name = "Logic_dump"
  let shortname = "logic-dump"
  let help = "dump ACSL logic definitions as JSON (for gen_twins.py)"
end)

module Out = Self.Empty_string (struct
  let option_name = "-logic-dump"
  let arg_name = "file.json"
  let help = "write the global logic declarations to file.json"
end)

let str fmt x = Format.asprintf "%a" fmt x
let s x = `String x
let lst f l = `List (List.map f l)

let label l = s (str Printer.pp_logic_label l)

(* C pointee of a pointer type, unrolled to its struct, if any. *)
let rec ctype t =
  match (Ast_types.unroll t).tnode with
  | TPtr p ->
    let comp =
      match (Ast_types.unroll p).tnode with
      | TComp ci -> s ci.cname
      | _ -> `Null
    in
    `Assoc [ "k", s "ptr"; "c", s (str Printer.pp_typ t);
             "to", s (str Printer.pp_typ p); "comp", comp;
             "pointee", ctype p ]
  | TInt _ | TEnum _ -> `Assoc [ "k", s "cint"; "c", s (str Printer.pp_typ t) ]
  | TComp ci ->
    `Assoc [ "k", s "comp"; "c", s (str Printer.pp_typ t); "comp", s ci.cname ]
  | _ -> `Assoc [ "k", s "c"; "c", s (str Printer.pp_typ t) ]

and ltype = function
  | Ctype t -> ctype t
  | Ltype (ti, [ e ]) when ti.lt_name = "\\list" ->
    `Assoc [ "k", s "list"; "elem", ltype e ]
  | Linteger -> `Assoc [ "k", s "integer" ]
  | Lboolean -> `Assoc [ "k", s "boolean" ]
  | Lreal -> `Assoc [ "k", s "real" ]
  | t -> `Assoc [ "k", s "other"; "pp", s (str Printer.pp_logic_type t) ]

let lvar v = `Assoc [ "name", s v.lv_name; "type", ltype v.lv_type ]

let rec term t =
  let node =
    match t.term_node with
    | TConst (Integer (z, _)) -> [ "n", s "int"; "v", s (Z.to_string z) ]
    | Tnull -> [ "n", s "null" ]
    | TLval lv -> [ "n", s "lval" ] @ tlval lv
    | TAddrOf lv -> [ "n", s "addrof" ] @ tlval lv
    | TStartOf lv -> [ "n", s "startof" ] @ tlval lv
    | TUnOp (op, a) ->
      [ "n", s "unop"; "op", s (str Printer.pp_unop op); "a", term a ]
    | TBinOp (op, a, b) ->
      [ "n", s "binop"; "op", s (str Printer.pp_binop op);
        "a", term a; "b", term b ]
    | TCast (implicit, ty, a) ->
      [ "n", s "cast"; "implicit", `Bool implicit; "to", ltype ty;
        "a", term a ]
    | Tapp (li, labels, args) ->
      [ "n", s "app"; "f", s li.l_var_info.lv_name;
        "labels", lst label labels; "args", lst term args ]
    | TDataCons (c, args) ->
      [ "n", s "ctor"; "c", s c.ctor_name; "args", lst term args ]
    | Tif (c, a, b) ->
      [ "n", s "if"; "c", pred c; "a", term a; "b", term b ]
    | Tat (a, l) -> [ "n", s "at"; "label", label l; "a", term a ]
    | Tbase_addr (l, a) -> [ "n", s "base_addr"; "label", label l; "a", term a ]
    | Toffset (l, a) -> [ "n", s "offset"; "label", label l; "a", term a ]
    | _ -> [ "n", s "other" ]
  in
  `Assoc (node @ [ "ty", ltype t.term_type; "pp", s (str Printer.pp_term t) ])

and tlval (host, off) =
  let h =
    match host with
    | TVar v ->
      `Assoc [ "h", s "var"; "name", s v.lv_name;
               "c", `Bool (v.lv_origin <> None) ]
    | TResult _ -> `Assoc [ "h", s "result" ]
    | TMem t -> `Assoc [ "h", s "mem"; "t", term t ]
  in
  let rec offs = function
    | TNoOffset -> []
    | TField (f, o) -> `Assoc [ "o", s "field"; "f", s f.fname ] :: offs o
    | TIndex (t, o) -> `Assoc [ "o", s "index"; "t", term t ] :: offs o
    | TModel (m, o) -> `Assoc [ "o", s "model"; "f", s m.mi_name ] :: offs o
  in
  [ "host", h; "off", `List (offs off) ]

and pred p =
  let un k l t = [ "p", s k; "label", label l; "t", term t ] in
  let node =
    match p.pred_content with
    | Ptrue -> [ "p", s "true" ]
    | Pfalse -> [ "p", s "false" ]
    | Papp (li, labels, args) ->
      [ "p", s "app"; "f", s li.l_var_info.lv_name;
        "labels", lst label labels; "args", lst term args ]
    | Prel (r, a, b) ->
      [ "p", s "rel"; "op", s (str Printer.pp_relation r);
        "a", term a; "b", term b ]
    | Pand (a, b) -> [ "p", s "and"; "a", pred a; "b", pred b ]
    | Por (a, b) -> [ "p", s "or"; "a", pred a; "b", pred b ]
    | Pxor (a, b) -> [ "p", s "xor"; "a", pred a; "b", pred b ]
    | Pimplies (a, b) -> [ "p", s "implies"; "a", pred a; "b", pred b ]
    | Piff (a, b) -> [ "p", s "iff"; "a", pred a; "b", pred b ]
    | Pnot a -> [ "p", s "not"; "a", pred a ]
    | Pif (c, a, b) -> [ "p", s "if"; "c", pred c; "a", pred a; "b", pred b ]
    | Pforall (vs, b) -> [ "p", s "forall"; "vars", lst lvar vs; "body", pred b ]
    | Pexists (vs, b) -> [ "p", s "exists"; "vars", lst lvar vs; "body", pred b ]
    | Pat (a, l) -> [ "p", s "at"; "label", label l; "a", pred a ]
    | Pvalid (l, t) -> un "valid" l t
    | Pvalid_read (l, t) -> un "valid_read" l t
    | Pinitialized (l, t) -> un "initialized" l t
    | Pfreeable (l, t) -> un "freeable" l t
    | Pdangling (l, t) -> un "dangling" l t
    | Pallocable (l, t) -> un "allocable" l t
    | Pobject_pointer (l, t) -> un "object_pointer" l t
    | Pseparated ts -> [ "p", s "separated"; "ts", lst term ts ]
    | _ -> [ "p", s "other" ]
  in
  `Assoc (node @ [ "pp", s (str Printer.pp_predicate p) ])

let loc (l : location) =
  let p = fst l in
  [ "file", s (Filepath.to_string (Filepos.path p));
    "line", `Int (Filepos.line p); "end_line", `Int (Filepos.line (snd l)) ]

let logic_info li l =
  let kind, body =
    match li.l_body with
    | LBnone | LBreads _ -> "decl", []
    | LBterm t -> "func", [ "body", term t ]
    | LBpred p -> "pred", [ "body", pred p ]
    | LBinductive cases ->
      "inductive",
      [ "cases",
        lst (fun (n, labels, _, p) ->
            `Assoc [ "name", s n; "labels", lst label labels; "pred", pred p ])
          cases ]
  in
  `Assoc
    ([ "kind", s kind; "name", s li.l_var_info.lv_name;
       "labels", lst label li.l_labels;
       "params", lst lvar li.l_profile;
       "ret", (match li.l_type with None -> `Null | Some t -> ltype t) ]
     @ body @ loc l)

let rec annot axiomatic = function
  | Dfun_or_pred (li, l) ->
    [ (match logic_info li l with
        | `Assoc a -> `Assoc (a @ [ "axiomatic", axiomatic ])
        | j -> j) ]
  | Dlemma (n, labels, _, tp, _, l) ->
    [ `Assoc ([ "kind", s (if tp.tp_kind = Admit then "axiom" else "lemma");
                "name", s n; "labels", lst label labels;
                "pred", pred tp.tp_statement; "axiomatic", axiomatic ]
              @ loc l) ]
  | Daxiomatic (n, ds, _, _) -> List.concat_map (annot (s n)) ds
  | Dmodule (n, ds, _, _, _) -> List.concat_map (annot (s n)) ds
  | Dtype (ti, l) -> [ `Assoc ([ "kind", s "type"; "name", s ti.lt_name ] @ loc l) ]
  | _ -> []

let run () =
  if Out.get () <> "" then begin
    let decls =
      List.concat_map
        (function GAnnot (ga, _) -> annot `Null ga | _ -> [])
        (Ast.get ()).globals
    in
    Yojson.Basic.to_file (Out.get ()) (`Assoc [ "decls", `List decls ]);
    Self.feedback "%d logic declarations written to %s"
      (List.length decls) (Out.get ())
  end

let () = Boot.Main.extend run
