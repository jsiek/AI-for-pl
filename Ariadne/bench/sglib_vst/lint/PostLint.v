(* The leak-freedom lint's checker (owner, R10, 2026-11-17), in Ltac2,
   on Coq's elaborated terms (not the source text), so no spelling of a
   postcondition can hide from it.  post_lint.py drives it: for each
   funspec of the given modules it unfolds the modules' own definitions
   (cbv delta on those constants, beta, zeta, match) and calls [report].

   A postcondition (the Post argument of every NDmk_funspec /
   mk_funspec in the term) fails if it contains
   - TT (any constant whose name is TT: seplog's or predicates_hered's);
   - an existential (exp, at either layer) whose binder type mentions
     mpred (predicates_hered.pred) after full reduction, or whose type
     is open (depends on a bound variable: fail closed);
   - !! P (prop) anywhere except as one operand of a conjunction (&&)
     whose other operand is not a prop: a bare prop is absorbing (TT is
     !! True);
   - an unapplied or partial connective (andp, prop, exp), or a
     connective outside the known set: wand, ewand, imp (fail closed).
   A funspec term in which no NDmk_funspec / mk_funspec is found fails
   (fail closed: nothing could be examined).  The funspec of _main must
   mention mem_mgr in its postcondition. *)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Ref List Array String Ident Env Std RedFlags Message
  Constr Proj.

Ltac2 rec last_id (l : ident list) : string :=
  match l with
  | [] => ""
  | x :: t => match t with [] => Ident.to_string x | _ => last_id t end
  end.

Ltac2 name_of (t : constr) : string :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Constant c _ => last_id (Env.path (Std.ConstRef c))
  | Constr.Unsafe.Ind i _ => last_id (Env.path (Std.IndRef i))
  | Constr.Unsafe.Constructor c _ =>
      last_id (Env.path (Std.ConstructRef c))
  | Constr.Unsafe.Proj p _ _ =>
      match Proj.to_constant p with
      | Some c => last_id (Env.path (Std.ConstRef c))
      | None => "<projection>"
      end
  | _ => ""
  end.

Ltac2 head_name (t : constr) : string :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ => name_of f
  | _ => name_of t
  end.

Ltac2 add (errs : string list Ref.ref) (m : string) : unit :=
  Ref.set errs (m :: Ref.get errs).

Ltac2 is_prop (t : constr) : bool := String.equal (head_name t) "prop".

(* does the (closed, fully reduced) type mention mpred? *)
Ltac2 rec mentions_mpred (found : bool Ref.ref) (t : constr) : unit :=
  let n := name_of t in
  (if Bool.or (String.equal n "pred") (String.equal n "mpred")
   then Ref.set found true else ());
  Constr.Unsafe.iter (mentions_mpred found) t.

Ltac2 check_binder (errs : string list Ref.ref) (ty : constr) : unit :=
  if Constr.Unsafe.is_closed ty then
    let nf := Std.eval_cbv RedFlags.all ty in
    let found := Ref.ref false in
    mentions_mpred found ty; mentions_mpred found nf;
    if Ref.get found then add errs "an existential over mpred" else ()
  else add errs "an existential over an open type (fail closed)".

Ltac2 check_name (errs : string list Ref.ref) (n : string) : unit :=
  if String.equal n "TT" then add errs "TT"
  else if Bool.or (String.equal n "wand")
            (Bool.or (String.equal n "ewand") (String.equal n "imp"))
  then add errs (String.app "the connective " (String.app n
                  " (unknown construct: fail closed)"))
  else if Bool.or (String.equal n "andp")
            (Bool.or (String.equal n "prop") (String.equal n "exp"))
  then add errs (String.app "an unapplied " (String.app n
                  " (fail closed)"))
  else ().

Ltac2 rec scan (errs : string list Ref.ref) (allow_prop : bool)
    (t : constr) : unit :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      let n := name_of f in
      let len := Array.length args in
      if String.equal n "andp" then
        if Int.ge len 2 then
          let x := Array.get args (Int.sub len 2) in
          let y := Array.get args (Int.sub len 1) in
          (if Bool.and (is_prop x) (is_prop y)
           then add errs "a conjunction of two props (absorbing)" else ());
          Array.iter (scan errs false)
            (Array.sub args 0 (Int.sub len 2));
          scan errs true x; scan errs true y
        else add errs "a partial andp (fail closed)"
      else if String.equal n "prop" then
        if allow_prop then Array.iter (scan errs false) args
        else add errs "!! P outside a conjunction (absorbing, like TT)"
      else if String.equal n "exp" then
        if Int.ge len 2 then
          check_binder errs (Array.get args (Int.sub len 2));
          Array.iter (scan errs false) args
        else add errs "a partial exp (fail closed)"
      else (scan errs false f; Array.iter (scan errs false) args)
  | Constr.Unsafe.Constant _ _ => check_name errs (name_of t)
  | Constr.Unsafe.Proj _ _ c => check_name errs (name_of t); scan errs false c
  | _ => Constr.Unsafe.iter (scan errs false) t
  end.

Ltac2 rec mentions (n : string) (found : bool Ref.ref) (t : constr) : unit :=
  (if String.equal (name_of t) n then Ref.set found true else ());
  Constr.Unsafe.iter (mentions n found) t.

(* find every funspec constructor; [main] is true under (_main, _) *)
Ltac2 rec funspecs (errs : string list Ref.ref) (count : int Ref.ref)
    (main : bool) (t : constr) : unit :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      let n := name_of f in
      let len := Array.length args in
      if Bool.or (String.equal n "NDmk_funspec") (String.equal n "mk_funspec")
      then
        if Int.ge len 5 then
          let post := Array.get args 4 in
          Ref.set count (Int.add (Ref.get count) 1);
          scan errs false post;
          (if main then
             let found := Ref.ref false in
             mentions "mem_mgr" found post;
             if Ref.get found then ()
             else add errs "main's postcondition does not hold mem_mgr"
           else ())
        else add errs "a partial funspec constructor (fail closed)"
      else if Bool.and (String.equal n "pair") (Int.ge len 4) then
        let m := String.equal (head_name (Array.get args 2)) "_main" in
        funspecs errs count false f;
        Array.iter (funspecs errs count m) args
      else (funspecs errs count main f;
            Array.iter (funspecs errs count main) args)
  | _ => Constr.Unsafe.iter (funspecs errs count main) t
  end.

(* unfold exactly the given constants (the modules' own definitions) *)
Ltac2 unfold_locals (refs : Std.reference list) (t : constr) : constr :=
  Std.eval_cbv { Std.rStrength := Std.Norm; Std.rBeta := true;
                 Std.rMatch := true; Std.rFix := false; Std.rCofix := false;
                 Std.rZeta := true; Std.rDelta := false;
                 Std.rConst := refs } t.

Ltac2 report (name : string) (t : constr) : unit :=
  let errs := Ref.ref [] in
  let count := Ref.ref 0 in
  funspecs errs count false t;
  (if Int.equal (Ref.get count) 0
   then add errs "no postcondition found (fail closed)" else ());
  match Ref.get errs with
  | [] => Message.print (Message.concat (Message.of_string "POSTLINT OK ")
            (Message.concat (Message.of_string name)
              (Message.concat (Message.of_string " ")
                (Message.of_int (Ref.get count)))))
  | es => List.iter (fun e => Message.print
            (Message.concat (Message.of_string "POSTLINT FAIL ")
              (Message.concat (Message.of_string name)
                (Message.concat (Message.of_string ": ")
                  (Message.of_string e))))) (List.rev es)
  end.
