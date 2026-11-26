(* Trusted spec of `perror` (owner-approved; ../TRUSTED_SPECS.md), with its
   body axiom, as VST's own body_malloc. *)
Definition perror_spec :=
 DECLARE _perror
 WITH sh : share, str : val, s : list byte
 PRE [ tptr tschar ]
   PROP (readable_share sh)
   PARAMS (str)
   SEP (cstring sh s str)
 POST [ tvoid ]
   PROP () RETURN ()
   SEP (cstring sh s str).

Axiom body_perror : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "perror"
    (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default)) (snd perror_spec).
