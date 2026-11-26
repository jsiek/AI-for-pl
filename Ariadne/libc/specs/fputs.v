(* Trusted spec of `fputs` (owner-approved; ../TRUSTED_SPECS.md), with its
   body axiom, as VST's own body_malloc. *)
Definition fputs_spec :=
 DECLARE _fputs
 WITH sh : share, str : val, s : list byte, f : val, own : bool, gv : globals
 PRE [ tptr tschar, FILEp ]
   PROP (readable_share sh)
   PARAMS (str; f) GLOBALS (gv)
   SEP (cstring sh s str;
        if own then FILE_handle f else !! std_stream gv f && emp)
 POST [ tint ] EX r : int,
   PROP () RETURN (Vint r)
   SEP (cstring sh s str;
        if own then FILE_handle f else emp).

Axiom body_fputs : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "fputs"
    (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xint cc_default)) (snd fputs_spec).
