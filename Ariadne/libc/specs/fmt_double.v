(* Trusted spec of `fmt_double` (owner-approved; ../TRUSTED_SPECS.md), with its
   body axiom, as VST's own body_malloc. *)
Definition fmt_double_spec :=
 DECLARE _fmt_double
 WITH buf : val, n : Z, v : float
 PRE [ tptr tschar, size_t, tdouble ]
   PROP (0 < n <= Ptrofs.max_unsigned)
   PARAMS (buf; Vptrofs (Ptrofs.repr n); Vfloat v)
   SEP (data_at_ Ews (tarray tschar n) buf)
 POST [ tvoid ] EX s : list byte,
   PROP () RETURN ()
   SEP (cstringn Ews s n buf).

Axiom body_fmt_double : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "fmt_double"
    (mksignature (AST.Xptr :: AST.Xlong :: AST.Xfloat :: nil) AST.Xvoid cc_default))
    (snd fmt_double_spec).
