(* Trusted spec of `strtod` (owner-approved; ../TRUSTED_SPECS.md), with its
   body axiom, as VST's own body_malloc. *)
Definition strtod_spec :=
 DECLARE _strtod
 WITH sh : share, str : val, s : list byte, endptr : val
 PRE [ tptr tschar, tptr (tptr tschar) ]
   PROP (readable_share sh)
   PARAMS (str; endptr)
   SEP (cstring sh s str;
        if eq_dec endptr nullval then emp else data_at_ Ews (tptr tschar) endptr)
 POST [ tdouble ] EX d : float, EX k : Z,
   PROP (0 <= k <= Zlength s)
   RETURN (Vfloat d)
   SEP (cstring sh s str;
        if eq_dec endptr nullval then emp
        else data_at Ews (tptr tschar) (offset_val k str) endptr).

Axiom body_strtod : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "strtod"
    (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xfloat cc_default)) (snd strtod_spec).
