import extrinsic.LogicalRelation

namespace Extrinsic

theorem compat_app :
  ∀ {Γ A B} (L M : Term),
    LogicalRel Γ (A ⇒ B) L L →
    LogicalRel Γ A M M →
    LogicalRel Γ B (L ∙ M) (L ∙ M)
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
  ∀ {Γ}, LogicalRel Γ 𝔹 ˋtrue ˋtrue
  | Γ => by
      intro ρ γ env
      exact VRel_to_ERel (A := 𝔹) (ρ := ρ) (V := ˋtrue) (W := ˋtrue)
        .vTrue .vTrue trivial

theorem compat_suc :
  ∀ {Γ} (M : Term),
    LogicalRel Γ ℕ M M →
    LogicalRel Γ ℕ (ˋsuc M) (ˋsuc M)
  | Γ, M, Mrel => by
      intro ρ γ env
      rcases Mrel ρ γ env with ⟨V, W, v, w, mSteps, nSteps, hVW⟩
      rcases mSteps with ⟨mSteps⟩
      rcases nSteps with ⟨nSteps⟩
      exact ⟨ˋsuc V, ˋsuc W, .vSuc v, .vSuc w,
        ⟨suc_multi mSteps⟩,
        ⟨suc_multi nSteps⟩,
        by simpa [VRel, VNatRel] using hVW⟩

theorem compat_case :
  ∀ {Γ A} (L M N : Term),
    LogicalRel Γ ℕ L L →
    LogicalRel Γ A M M →
    LogicalRel (ℕ :: Γ) A N N →
    LogicalRel Γ A (caseₜ L [zero⇒ M |suc⇒ N]) (caseₜ L [zero⇒ M |suc⇒ N])
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
        have hVW : VRel ℕ ρ V W vV wW := by
          simpa [VRel, VNatRel] using hNat
        rcases Nrel ρ (extendRelEnv γ V W)
            (extendRelEnv_related (Γ := Γ) (A := ℕ) (ρ := ρ) (γ := γ)
              (V := V) (W := W) env vV wW hVW) with
          ⟨VB, WB, vb, wb, nSteps, nStepsR, hVB⟩
        rcases nSteps with ⟨nSteps⟩
        rcases nStepsR with ⟨nStepsR⟩
        have hBetaL :
            (caseₜ (ˋsuc V) [zero⇒ (subst γ.gamma1 M) |suc⇒ (subst (exts γ.gamma1) N)]) —↠
              subst (V • γ.gamma1) N := by
          have h :
              (caseₜ (ˋsuc V) [zero⇒ (subst γ.gamma1 M) |suc⇒ (subst (exts γ.gamma1) N)]) —↠
                singleSubst (subst (exts γ.gamma1) N) V :=
            .step _ (.beta_suc vV) (.refl _)
          simpa [exts_sub_cons_tm] using h
        have hBetaR :
            (caseₜ (ˋsuc W) [zero⇒ (subst γ.gamma2 M) |suc⇒ (subst (exts γ.gamma2) N)]) —↠
              subst (W • γ.gamma2) N := by
          have h :
              (caseₜ (ˋsuc W) [zero⇒ (subst γ.gamma2 M) |suc⇒ (subst (exts γ.gamma2) N)]) —↠
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
  ∀ {Γ}, LogicalRel Γ ℕ ˋzero ˋzero
  | Γ => by
      intro ρ γ env
      exact VRel_to_ERel (A := ℕ) (ρ := ρ) (V := ˋzero) (W := ˋzero)
        .vZero .vZero trivial

theorem compat_lam :
  ∀ {Γ A B} (N : Term),
    LogicalRel (A :: Γ) B N N →
    LogicalRel Γ (A ⇒ B) (ƛ N) (ƛ N)
  | Γ, A, B, N, Nrel => by
      intro ρ γ env
      refine ⟨ƛ (subst (exts γ.gamma1) N), ƛ (subst (exts γ.gamma2) N),
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
  ∀ {Γ}, LogicalRel Γ 𝔹 ˋfalse ˋfalse
  | Γ => by
      intro ρ γ env
      exact VRel_to_ERel (A := 𝔹) (ρ := ρ) (V := ˋfalse) (W := ˋfalse)
        .vFalse .vFalse trivial

theorem compat_if :
  ∀ {Γ A} (L M N : Term),
    LogicalRel Γ 𝔹 L L →
    LogicalRel Γ A M M →
    LogicalRel Γ A N N →
    LogicalRel Γ A (ˋif L then M else N) (ˋif L then M else N)
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
    LogicalRel Γ A (ˋx) (ˋx)
  | _, _, _, .Z => by
      intro ρ γ env
      simpa [LogicalRel, GRel, subst] using env.1
  | _, _, _, .S hx => by
      intro ρ γ env
      simpa [LogicalRel, GRel, subst, tailRelEnv] using
        (compat_var hx ρ (tailRelEnv γ) env.2)

theorem compat_tapp :
  ∀ {Γ A B} (M : Term),
    LogicalRel Γ (∀ₜ A) M M →
    LogicalRel Γ (A [ B ]ₜ) (M ∙[]) (M ∙[])
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
    LogicalRel Γ (∀ₜ A) (Λ N) (Λ N)
  | Γ, A, N, Nrel => by
      intro ρ γ env
      refine ⟨Λ (subst (up γ.gamma1) N), Λ (subst (up γ.gamma2) N),
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
    Δ ⊢ Γ ⊢ M ⦂ A →
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
