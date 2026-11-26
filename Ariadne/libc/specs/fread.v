(* Trusted spec of `fread` (owner-approved; ../TRUSTED_SPECS.md), with its
   body axiom, as VST's own body_malloc. *)
Definition fread_spec :=
 DECLARE _fread
 WITH buf : val, size : Z, nmemb : Z, f : val, own : bool, gv : globals
 PRE [ tptr tvoid, size_t, size_t, FILEp ]
   PROP (0 < size; 0 <= nmemb; size * nmemb <= Ptrofs.max_unsigned)
   PARAMS (buf; Vptrofs (Ptrofs.repr size); Vptrofs (Ptrofs.repr nmemb); f)
   GLOBALS (gv)
   SEP (data_at_ Ews (tarray tschar (size * nmemb)) buf;
        if own then FILE_handle f else !! std_stream gv f && emp)
 POST [ size_t ] EX k : Z, EX bytes : list byte,
   PROP (0 <= k <= nmemb; Zlength bytes = (k * size)%Z)
   RETURN (Vptrofs (Ptrofs.repr k))
   SEP (data_at Ews (tarray tschar (size * nmemb))
          (map Vbyte bytes ++ Zrepeat Vundef (size * (nmemb - k))) buf;
        if own then FILE_handle f else emp).

Axiom body_fread : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "fread"
    (mksignature (AST.Xptr :: AST.Xlong :: AST.Xlong :: AST.Xptr :: nil) AST.Xlong
       cc_default)) (snd fread_spec).
