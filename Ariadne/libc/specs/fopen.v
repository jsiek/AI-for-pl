(* Trusted spec of `fopen` (owner-approved; ../TRUSTED_SPECS.md), with its
   body axiom, as VST's own body_malloc. *)
Definition fopen_spec :=
 DECLARE _fopen
 WITH sh1 : share, sh2 : share, path : val, mode : val, sp : list byte, sm : list byte
 PRE [ tptr tschar, tptr tschar ]
   PROP (readable_share sh1; readable_share sh2)
   PARAMS (path; mode)
   SEP (cstring sh1 sp path; cstring sh2 sm mode)
 POST [ FILEp ] EX f : val,
   PROP () RETURN (f)
   SEP (cstring sh1 sp path; cstring sh2 sm mode;
        if eq_dec f nullval then emp else FILE_handle f).

Axiom body_fopen : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "fopen"
    (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xptr cc_default)) (snd fopen_spec).
