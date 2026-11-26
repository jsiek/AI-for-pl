(* Trusted spec of `fclose` (owner-approved; ../TRUSTED_SPECS.md), with its
   body axiom, as VST's own body_malloc. *)
Definition fclose_spec :=
 DECLARE _fclose
 WITH f : val
 PRE [ FILEp ]
   PROP () PARAMS (f)
   SEP (FILE_handle f)
 POST [ tint ] EX r : int,
   PROP () RETURN (Vint r)
   SEP ().

Axiom body_fclose : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "fclose"
    (mksignature (AST.Xptr :: nil) AST.Xint cc_default)) (snd fclose_spec).
