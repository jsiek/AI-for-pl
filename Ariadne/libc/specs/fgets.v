(* Trusted spec of `fgets` (owner-approved; ../TRUSTED_SPECS.md), with its
   body axiom, as VST's own body_malloc. *)
Definition fgets_spec :=
 DECLARE _fgets
 WITH buf : val, n : Z, f : val, own : bool, gv : globals
 PRE [ tptr tschar, tint, FILEp ]
   PROP (0 < n <= Int.max_signed)
   PARAMS (buf; Vint (Int.repr n); f) GLOBALS (gv)
   SEP (data_at_ Ews (tarray tschar n) buf;
        if own then FILE_handle f else !! std_stream gv f && emp)
 POST [ tptr tschar ] EX r : val,
   PROP () RETURN (r)
   SEP (if eq_dec r nullval then data_at_ Ews (tarray tschar n) buf
        else !! (r = buf) && EX s : list byte, cstringn Ews s n buf;
        if own then FILE_handle f else emp).

Axiom body_fgets : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "fgets"
    (mksignature (AST.Xptr :: AST.Xint :: AST.Xptr :: nil) AST.Xptr cc_default))
    (snd fgets_spec).
