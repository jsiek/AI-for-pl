import extrinsic.LogicalRelation

namespace Extrinsic

theorem compat_app :
  ∀ {Γ A B} (L M : Term),
    LogicalRel Γ (.fn A B) L L →
    LogicalRel Γ A M M →
    LogicalRel Γ B (.app L M) (.app L M)
  | Γ, A, B, L, M, Lrel, Mrel => by
      intro ρ γ env
      rcases Lrel ρ γ env with ⟨VL, WL, vL, wL, lSteps, rSteps, hFun⟩
      rcases Mrel ρ γ env with ⟨VM, WM, vM, wM, mSteps, mStepsR, hArg⟩
      rcases lSteps with ⟨lSteps⟩
      rcases rSteps with ⟨rSteps⟩
      rcases mSteps with ⟨mSteps⟩
      rcases mStepsR with ⟨mStepsR⟩
      cases vL <;> cases wL <;> simp [VRel] at hFun
      case vLam.vLam =>
        rcases hFun vM wM hArg with ⟨VB, redL, WB, redR, vb, wb, hVB⟩
        rcases redL with ⟨redL⟩
        rcases redR with ⟨redR⟩
        exact ⟨VB, WB, vb, wb,
          ⟨multi_trans
            (multi_trans
              (by simpa [subst] using app_multi lSteps Value.vLam mSteps)
              (by simpa using beta_lam_multi vM))
            redL⟩,
          ⟨multi_trans
            (multi_trans
              (by simpa [subst] using app_multi rSteps Value.vLam mStepsR)
              (by simpa using beta_lam_multi wM))
            redR⟩,
          hVB⟩

theorem compat_true :
  ∀ {Γ}, LogicalRel Γ .bool .ttrue .ttrue
  | Γ => by
      intro ρ γ env
      exact VRel_to_ERel (A := .bool) (ρ := ρ) (V := .ttrue) (W := .ttrue)
        .vTrue .vTrue trivial

theorem compat_suc :
  ∀ {Γ} (M : Term),
    LogicalRel Γ .nat M M →
    LogicalRel Γ .nat (.suc M) (.suc M)
  | Γ, M, Mrel => by
      intro ρ γ env
      rcases Mrel ρ γ env with ⟨V, W, v, w, mSteps, nSteps, hVW⟩
      rcases mSteps with ⟨mSteps⟩
      rcases nSteps with ⟨nSteps⟩
      exact ⟨.suc V, .suc W, .vSuc v, .vSuc w,
        ⟨suc_multi mSteps⟩,
        ⟨suc_multi nSteps⟩,
        by simpa [VRel, VNatRel] using hVW⟩

theorem compat_case :
  ∀ {Γ A} (L M N : Term),
    LogicalRel Γ .nat L L →
    LogicalRel Γ A M M →
    LogicalRel (.nat :: Γ) A N N →
    LogicalRel Γ A (.natCase L M N) (.natCase L M N)
  | Γ, A, L, M, N, Lrel, Mrel, Nrel => by
      intro ρ γ env
      rcases Lrel ρ γ env with ⟨VL, WL, v, w, lSteps, rSteps, hNat⟩
      rcases lSteps with ⟨lSteps⟩
      rcases rSteps with ⟨rSteps⟩
      cases v <;> cases w <;> simp [VRel, VNatRel] at hNat
      case vZero.vZero =>
        rcases Mrel ρ γ env with ⟨VM, WM, vM, wM, mSteps, mStepsR, hM⟩
        rcases mSteps with ⟨mSteps⟩
        rcases mStepsR with ⟨mStepsR⟩
        exact ⟨VM, WM, vM, wM,
          ⟨multi_trans
            (multi_trans
              (by simpa [subst] using
                case_multi (M := subst γ.gamma1 M) (N := subst (exts γ.gamma1) N) lSteps)
              (by simpa using
                case_zero_multi (M := subst γ.gamma1 M) (N := subst (exts γ.gamma1) N)))
            mSteps⟩,
          ⟨multi_trans
            (multi_trans
              (by simpa [subst] using
                case_multi (M := subst γ.gamma2 M) (N := subst (exts γ.gamma2) N) rSteps)
              (by simpa using
                case_zero_multi (M := subst γ.gamma2 M) (N := subst (exts γ.gamma2) N)))
            mStepsR⟩,
          hM⟩
      case vSuc.vSuc =>
        rename_i V vV W wW
        have hVW : VRel .nat ρ V W vV wW := by
          simpa [VRel, VNatRel] using hNat
        rcases Nrel ρ (extendRelEnv γ V W)
            (extendRelEnv_related (Γ := Γ) (A := .nat) (ρ := ρ) (γ := γ)
              (V := V) (W := W) env vV wW hVW) with
          ⟨VB, WB, vb, wb, nSteps, nStepsR, hVB⟩
        rcases nSteps with ⟨nSteps⟩
        rcases nStepsR with ⟨nStepsR⟩
        have hBetaL :
            (.natCase (.suc V) (subst γ.gamma1 M) (subst (exts γ.gamma1) N)) —↠
              subst (V • γ.gamma1) N := by
          have h :
              (.natCase (.suc V) (subst γ.gamma1 M) (subst (exts γ.gamma1) N)) —↠
                singleSubst (subst (exts γ.gamma1) N) V :=
            .step _ (.beta_suc vV) (.refl _)
          simpa [exts_sub_cons_tm] using h
        have hBetaR :
            (.natCase (.suc W) (subst γ.gamma2 M) (subst (exts γ.gamma2) N)) —↠
              subst (W • γ.gamma2) N := by
          have h :
              (.natCase (.suc W) (subst γ.gamma2 M) (subst (exts γ.gamma2) N)) —↠
                singleSubst (subst (exts γ.gamma2) N) W :=
            .step _ (.beta_suc wW) (.refl _)
          simpa [exts_sub_cons_tm] using h
        exact ⟨VB, WB, vb, wb,
          ⟨multi_trans
            (multi_trans
              (by simpa [subst] using
                case_multi (M := subst γ.gamma1 M) (N := subst (exts γ.gamma1) N) lSteps)
              hBetaL)
            nSteps⟩,
          ⟨multi_trans
            (multi_trans
              (by simpa [subst] using
                case_multi (M := subst γ.gamma2 M) (N := subst (exts γ.gamma2) N) rSteps)
              hBetaR)
            nStepsR⟩,
          hVB⟩

theorem compat_zero :
  ∀ {Γ}, LogicalRel Γ .nat .zero .zero
  | Γ => by
      intro ρ γ env
      exact VRel_to_ERel (A := .nat) (ρ := ρ) (V := .zero) (W := .zero)
        .vZero .vZero trivial

theorem compat_lam :
  ∀ {Γ A B} (N : Term),
    LogicalRel (A :: Γ) B N N →
    LogicalRel Γ (.fn A B) (.lam N) (.lam N)
  | Γ, A, B, N, Nrel => by
      intro ρ γ env
      refine ⟨.lam (subst (exts γ.gamma1) N), .lam (subst (exts γ.gamma2) N),
        .vLam, .vLam, ⟨.refl _⟩, ⟨.refl _⟩, ?_⟩
      intro V W v w hVW
      rcases Nrel ρ (extendRelEnv γ V W)
          (extendRelEnv_related (Γ := Γ) (A := A) (ρ := ρ) (γ := γ) (V := V) (W := W)
            env v w hVW) with
        ⟨VB, WB, vb, wb, mSteps, nSteps, hVB⟩
      rcases mSteps with ⟨mSteps⟩
      rcases nSteps with ⟨nSteps⟩
      exact ⟨VB, WB, vb, wb,
        ⟨by simpa [extendRelEnv, exts_sub_cons_tm] using mSteps⟩,
        ⟨by simpa [extendRelEnv, exts_sub_cons_tm] using nSteps⟩,
        hVB⟩

theorem compat_false :
  ∀ {Γ}, LogicalRel Γ .bool .tfalse .tfalse
  | Γ => by
      intro ρ γ env
      exact VRel_to_ERel (A := .bool) (ρ := ρ) (V := .tfalse) (W := .tfalse)
        .vFalse .vFalse trivial

theorem compat_if :
  ∀ {Γ A} (L M N : Term),
    LogicalRel Γ .bool L L →
    LogicalRel Γ A M M →
    LogicalRel Γ A N N →
    LogicalRel Γ A (.ite L M N) (.ite L M N)
  | Γ, A, L, M, N, Lrel, Mrel, Nrel => by
      intro ρ γ env
      rcases Lrel ρ γ env with ⟨VL, WL, v, w, lSteps, rSteps, hBool⟩
      rcases Mrel ρ γ env with ⟨VM, WM, vM, wM, mSteps, mStepsR, hM⟩
      rcases Nrel ρ γ env with ⟨VN, WN, vN, wN, nSteps, nStepsR, hN⟩
      rcases lSteps with ⟨lSteps⟩
      rcases rSteps with ⟨rSteps⟩
      rcases mSteps with ⟨mSteps⟩
      rcases mStepsR with ⟨mStepsR⟩
      rcases nSteps with ⟨nSteps⟩
      rcases nStepsR with ⟨nStepsR⟩
      cases v <;> cases w <;> simp [VRel, VBoolRel] at hBool
      case vTrue.vTrue =>
        exact ⟨VM, WM, vM, wM,
          ⟨multi_trans
            (by simpa [subst] using
              if_true_multi (M := subst γ.gamma1 M) (N := subst γ.gamma1 N) lSteps)
            mSteps⟩,
          ⟨multi_trans
            (by simpa [subst] using
              if_true_multi (M := subst γ.gamma2 M) (N := subst γ.gamma2 N) rSteps)
            mStepsR⟩,
          hM⟩
      case vFalse.vFalse =>
        exact ⟨VN, WN, vN, wN,
          ⟨multi_trans
            (by simpa [subst] using
              if_false_multi (M := subst γ.gamma1 M) (N := subst γ.gamma1 N) lSteps)
            nSteps⟩,
          ⟨multi_trans
            (by simpa [subst] using
              if_false_multi (M := subst γ.gamma2 M) (N := subst γ.gamma2 N) rSteps)
            nStepsR⟩,
          hN⟩

theorem compat_var :
  ∀ {Γ A x},
    HasTypeVar Γ x A →
    LogicalRel Γ A (.var x) (.var x)
  | _, _, _, .Z => by
      intro ρ γ env
      simpa [LogicalRel, GRel, subst] using env.1
  | _, _, _, .S hx => by
      intro ρ γ env
      simpa [LogicalRel, GRel, subst, tailRelEnv] using
        (compat_var hx ρ (tailRelEnv γ) env.2)

theorem compat_tapp :
  ∀ {Γ A B} (M : Term),
    LogicalRel Γ (.all A) M M →
    LogicalRel Γ (substOneT A B) (.tapp M) (.tapp M)
  | Γ, A, B, M, Mrel => by
      intro ρ γ env
      rcases Mrel ρ γ env with ⟨V, W, v, w, mSteps, nSteps, hAll⟩
      cases v <;> try cases hAll
      cases w <;> try cases hAll
      rcases hAll (substT ρ.rho1 B) (substT ρ.rho2 B) (VRel B ρ) with
        ⟨VB, WB, vb, wb, mSteps', nSteps', hVB⟩
      rcases mSteps with ⟨mSteps⟩
      rcases nSteps with ⟨nSteps⟩
      rcases mSteps' with ⟨mSteps'⟩
      rcases nSteps' with ⟨nSteps'⟩
      have SR :
          SubstRel (singleTyEnv B) ρ
            (extendRelSub ρ (substT ρ.rho1 B) (substT ρ.rho2 B) (VRel B ρ)) :=
        { varTo := by
            intro α V' W' v' w' h
            cases α <;> simpa [VRel, extendRelSub, singleTyEnv] using h
        , varFrom := by
            intro α V' W' v' w' h
            cases α <;> simpa [VRel, extendRelSub, singleTyEnv] using h }
      exact ⟨VB, WB, vb, wb,
        ⟨multi_trans (by simpa [subst] using tapp_multi mSteps)
          (multi_trans (by simpa using (beta_tlam_multi (N := _))) mSteps')⟩,
        ⟨multi_trans (by simpa [subst] using tapp_multi nSteps)
          (multi_trans (by simpa using (beta_tlam_multi (N := _))) nSteps')⟩,
        VRel_subst (A := A) (σ := singleTyEnv B) (ρ := ρ)
          (ρ' := extendRelSub ρ (substT ρ.rho1 B) (substT ρ.rho2 B) (VRel B ρ))
          SR hVB⟩

theorem compat_tlam :
  ∀ {Γ A} (N : Term),
    LogicalRel (liftCtx Γ) A N N →
    LogicalRel Γ (.all A) (.tlam N) (.tlam N)
  | Γ, A, N, Nrel => by
      intro ρ γ env
      refine ⟨.tlam (subst (up γ.gamma1) N), .tlam (subst (up γ.gamma2) N),
        .vTlam, .vTlam, ⟨.refl _⟩, ⟨.refl _⟩, ?_⟩
      intro A₁ A₂ R
      have hLift :
          GRel (liftCtx Γ) (extendRelSub ρ A₁ A₂ R) γ :=
        liftRelEnv_related (Γ := Γ) (A₁ := A₁) (A₂ := A₂) (ρ := ρ) (γ := γ) R env
      have hN : ERel A (extendRelSub ρ A₁ A₂ R) (subst γ.gamma1 N) (subst γ.gamma2 N) :=
        Nrel (extendRelSub ρ A₁ A₂ R) γ hLift
      have hup1 : up γ.gamma1 = γ.gamma1 := by
        funext i
        simp [up, renameTT]
      have hup2 : up γ.gamma2 = γ.gamma2 := by
        funext i
        simp [up, renameTT]
      simpa [ERel, hup1, hup2] using hN

theorem fundamental :
  ∀ {Δ Γ A} (M : Term),
    HasType Δ Γ M A →
    LogicalRel Γ A M M
  | _, _, _, _, .t_var hx =>
      compat_var hx
  | _, _, _, _, .t_lam _ hN =>
      compat_lam _ (fundamental _ hN)
  | _, _, _, _, .t_app hL hM =>
      compat_app _ _ (fundamental _ hL) (fundamental _ hM)
  | _, _, _, _, .t_true =>
      compat_true
  | _, _, _, _, .t_false =>
      compat_false
  | _, _, _, _, .t_zero =>
      compat_zero
  | _, _, _, _, .t_suc hM =>
      compat_suc _ (fundamental _ hM)
  | _, _, _, _, .t_case hL hM hN =>
      compat_case _ _ _ (fundamental _ hL) (fundamental _ hM) (fundamental _ hN)
  | _, _, _, _, .t_if hL hM hN =>
      compat_if _ _ _ (fundamental _ hL) (fundamental _ hM) (fundamental _ hN)
  | _, _, _, _, .t_tlam hN =>
      compat_tlam _ (fundamental _ hN)
  | _, _, _, _, .t_tapp hM _ =>
      compat_tapp _ (fundamental _ hM)

end Extrinsic
