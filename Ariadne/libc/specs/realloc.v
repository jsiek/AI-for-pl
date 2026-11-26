(* Trusted spec of `realloc` (owner-approved; ../TRUSTED_SPECS.md), with its
   body axiom, as VST's own body_malloc. *)
(* `t` and `old` are one WITH component, since old's type depends on t. *)
Definition realloc_spec :=
 DECLARE _realloc
 WITH told : {t : type & list (reptype t)}, p : val, n : Z, m : Z, gv : globals
 PRE [ tptr tvoid, size_t ]
   PROP (0 < m; sizeof (projT1 told) * m <= Ptrofs.max_unsigned;
         p = nullval -> n = 0 /\ projT2 told = [])
   PARAMS (p; Vptrofs (Ptrofs.repr (sizeof (projT1 told) * m))) GLOBALS (gv)
   SEP (mem_mgr gv;
        if eq_dec p nullval then emp
        else malloc_token Ews (tarray (projT1 told) n) p *
             data_at Ews (tarray (projT1 told) n) (projT2 told) p)
 POST [ tptr tvoid ] EX q : val,
   PROP () RETURN (q)
   SEP (mem_mgr gv;
        if eq_dec q nullval then
          (if eq_dec p nullval then emp
           else malloc_token Ews (tarray (projT1 told) n) p *
                data_at Ews (tarray (projT1 told) n) (projT2 told) p)
        else malloc_token Ews (tarray (projT1 told) m) q *
             data_at Ews (tarray (projT1 told) m)
               (sublist 0 (Z.min n m) (projT2 told) ++
                Zrepeat (default_val (projT1 told)) (m - Z.min n m)) q).

Axiom body_realloc : forall {Espec : OracleKind},
  body_lemma_of_funspec (EF_external "realloc"
    (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr cc_default)) (snd realloc_spec).
