(* Trusted spec of `fflush` (owner-approved; ../TRUSTED_SPECS.md), with its
   body axiom, as VST's own body_malloc. *)
Definition fflush_spec :=
 DECLARE _fflush
 WITH f : val, own : bool, gv : globals
 PRE [ FILEp ]
   PROP ()
   PARAMS (f) GLOBALS (gv)
   SEP (if own then FILE_handle f else !! std_stream gv f && emp)
 POST [ tint ] EX r : int,
   PROP () RETURN (Vint r)
   SEP (if own then FILE_handle f else emp).

Axiom body_fflush : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "fflush"
    (mksignature (AST.Xptr :: nil) AST.Xint cc_default)) (snd fflush_spec).
