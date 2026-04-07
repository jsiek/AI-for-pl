import extrinsic.LogicalRelation

namespace Extrinsic

theorem compat_app :
  ∀ {Γ A B} (L M : Term),
    Γ ⊨ L ≈ L ⦂ (A ⇒ B) →
    Γ ⊨ M ≈ M ⦂ A →
    Γ ⊨ (L ∙ M) ≈ (L ∙ M) ⦂ B
  | Γ, A, B, L, M, Lrel, Mrel => by
      intro ρ γ env
      rcases Lrel ρ γ env with ⟨VL, WL, vL, wL, lSteps, rSteps, hFun⟩
      rcases Mrel ρ γ env with ⟨VM, WM, vM, wM, mSteps, mStepsR, hArg⟩
      rcases lSteps with ⟨lSteps⟩
      rcases rSteps with ⟨rSteps⟩
      rcases mSteps with ⟨mSteps⟩
      rcases mStepsR with ⟨mStepsR⟩
      cases vL <;> cases wL <;> simp [𝒱] at hFun
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
  ∀ {Γ}, Γ ⊨ ˋtrue ≈ ˋtrue ⦂ 𝔹
  | Γ => by
      intro ρ γ env
      exact 𝒱_to_𝓔 (A := 𝔹) (ρ := ρ) (V := ˋtrue) (W := ˋtrue)
        .vTrue .vTrue trivial

theorem compat_suc :
  ∀ {Γ} (M : Term),
    Γ ⊨ M ≈ M ⦂ ℕ →
    Γ ⊨ (ˋsuc M) ≈ (ˋsuc M) ⦂ ℕ
  | Γ, M, Mrel => by
      intro ρ γ env
      rcases Mrel ρ γ env with ⟨V, W, v, w, mSteps, nSteps, hVW⟩
      rcases mSteps with ⟨mSteps⟩
      rcases nSteps with ⟨nSteps⟩
      exact ⟨ˋsuc V, ˋsuc W, .vSuc v, .vSuc w,
        ⟨suc_multi mSteps⟩,
        ⟨suc_multi nSteps⟩,
        by simpa [𝒱, 𝒱nat] using hVW⟩

theorem compat_case :
  ∀ {Γ A} (L M N : Term),
    Γ ⊨ L ≈ L ⦂ ℕ →
    Γ ⊨ M ≈ M ⦂ A →
    (ℕ :: Γ) ⊨ N ≈ N ⦂ A →
    Γ ⊨ (caseₜ L [zero⇒ M |suc⇒ N]) ≈ (caseₜ L [zero⇒ M |suc⇒ N]) ⦂ A
  | Γ, A, L, M, N, Lrel, Mrel, Nrel => by
      intro ρ γ env
      rcases Lrel ρ γ env with ⟨VL, WL, v, w, lSteps, rSteps, hNat⟩
      rcases lSteps with ⟨lSteps⟩
      rcases rSteps with ⟨rSteps⟩
      cases v <;> cases w <;> simp [𝒱, 𝒱nat] at hNat
      case vZero.vZero =>
        rcases Mrel ρ γ env with ⟨VM, WM, vM, wM, mSteps, mStepsR, hM⟩
        rcases mSteps with ⟨mSteps⟩
        rcases mStepsR with ⟨mStepsR⟩
        exact ⟨VM, WM, vM, wM,
          ⟨multi_trans
            (multi_trans
              (by simpa [subst] using
                case_multi (M := subst γ.left M) (N := subst (exts γ.left) N) lSteps)
              (by simpa using
                case_zero_multi (M := subst γ.left M) (N := subst (exts γ.left) N)))
            mSteps⟩,
          ⟨multi_trans
            (multi_trans
              (by simpa [subst] using
                case_multi (M := subst γ.right M) (N := subst (exts γ.right) N) rSteps)
              (by simpa using
                case_zero_multi (M := subst γ.right M) (N := subst (exts γ.right) N)))
            mStepsR⟩,
          hM⟩
      case vSuc.vSuc =>
        rename_i V vV W wW
        have hVW : 𝒱 ℕ ρ V W vV wW := by
          simpa [𝒱, 𝒱nat] using hNat
        rcases Nrel ρ (extendRelEnv γ V W)
            (extendRelEnv_related (Γ := Γ) (A := ℕ) (ρ := ρ) (γ := γ)
              (V := V) (W := W) env vV wW hVW) with
          ⟨VB, WB, vb, wb, nSteps, nStepsR, hVB⟩
        rcases nSteps with ⟨nSteps⟩
        rcases nStepsR with ⟨nStepsR⟩
        have hBetaL :
            (caseₜ (ˋsuc V) [zero⇒ (subst γ.left M) |suc⇒ (subst (exts γ.left) N)]) —↠
              subst (V • γ.left) N := by
          have h :
              (caseₜ (ˋsuc V) [zero⇒ (subst γ.left M) |suc⇒ (subst (exts γ.left) N)]) —↠
                singleSubst (subst (exts γ.left) N) V :=
            .step _ (.beta_suc vV) (.refl _)
          simpa [exts_sub_cons_tm] using h
        have hBetaR :
            (caseₜ (ˋsuc W) [zero⇒ (subst γ.right M) |suc⇒ (subst (exts γ.right) N)]) —↠
              subst (W • γ.right) N := by
          have h :
              (caseₜ (ˋsuc W) [zero⇒ (subst γ.right M) |suc⇒ (subst (exts γ.right) N)]) —↠
                singleSubst (subst (exts γ.right) N) W :=
            .step _ (.beta_suc wW) (.refl _)
          simpa [exts_sub_cons_tm] using h
        exact ⟨VB, WB, vb, wb,
          ⟨multi_trans
            (multi_trans
              (by simpa [subst] using
                case_multi (M := subst γ.left M) (N := subst (exts γ.left) N) lSteps)
              hBetaL)
            nSteps⟩,
          ⟨multi_trans
            (multi_trans
              (by simpa [subst] using
                case_multi (M := subst γ.right M) (N := subst (exts γ.right) N) rSteps)
              hBetaR)
            nStepsR⟩,
          hVB⟩

theorem compat_zero :
  ∀ {Γ}, Γ ⊨ ˋzero ≈ ˋzero ⦂ ℕ
  | Γ => by
      intro ρ γ env
      exact 𝒱_to_𝓔 (A := ℕ) (ρ := ρ) (V := ˋzero) (W := ˋzero)
        .vZero .vZero trivial

theorem compat_lam :
  ∀ {Γ A B} (N : Term),
    (A :: Γ) ⊨ N ≈ N ⦂ B →
    Γ ⊨ (ƛ N) ≈ (ƛ N) ⦂ (A ⇒ B)
  | Γ, A, B, N, Nrel => by
      intro ρ γ env
      refine ⟨ƛ (subst (exts γ.left) N), ƛ (subst (exts γ.right) N),
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
  ∀ {Γ}, Γ ⊨ ˋfalse ≈ ˋfalse ⦂ 𝔹
  | Γ => by
      intro ρ γ env
      exact 𝒱_to_𝓔 (A := 𝔹) (ρ := ρ) (V := ˋfalse) (W := ˋfalse)
        .vFalse .vFalse trivial

theorem compat_if :
  ∀ {Γ A} (L M N : Term),
    Γ ⊨ L ≈ L ⦂ 𝔹 →
    Γ ⊨ M ≈ M ⦂ A →
    Γ ⊨ N ≈ N ⦂ A →
    Γ ⊨ (ˋif L then M else N) ≈ (ˋif L then M else N) ⦂ A
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
      cases v <;> cases w <;> simp [𝒱, 𝒱bool] at hBool
      case vTrue.vTrue =>
        exact ⟨VM, WM, vM, wM,
          ⟨multi_trans
            (by simpa [subst] using
              if_true_multi (M := subst γ.left M) (N := subst γ.left N) lSteps)
            mSteps⟩,
          ⟨multi_trans
            (by simpa [subst] using
              if_true_multi (M := subst γ.right M) (N := subst γ.right N) rSteps)
            mStepsR⟩,
          hM⟩
      case vFalse.vFalse =>
        exact ⟨VN, WN, vN, wN,
          ⟨multi_trans
            (by simpa [subst] using
              if_false_multi (M := subst γ.left M) (N := subst γ.left N) lSteps)
            nSteps⟩,
          ⟨multi_trans
            (by simpa [subst] using
              if_false_multi (M := subst γ.right M) (N := subst γ.right N) rSteps)
            nStepsR⟩,
          hN⟩

theorem compat_var :
  ∀ {Γ A x},
    HasTypeVar Γ x A →
    Γ ⊨ (ˋx) ≈ (ˋx) ⦂ A
  | _, _, _, .Z => by
      intro ρ γ env
      simpa [𝒢, subst] using env.1
  | _, _, _, .S hx => by
      intro ρ γ env
      simpa [𝒢, subst, tailRelEnv] using
        (compat_var hx ρ (tailRelEnv γ) env.2)

theorem compat_tapp :
  ∀ {Γ A B} (M : Term),
    Γ ⊨ M ≈ M ⦂ (∀ₜ A) →
    Γ ⊨ (M ∙[]) ≈ (M ∙[]) ⦂ (A [ B ]ₜ)
  | Γ, A, B, M, Mrel => by
      intro ρ γ env
      rcases Mrel ρ γ env with ⟨V, W, v, w, mSteps, nSteps, hAll⟩
      cases v <;> try cases hAll
      cases w <;> try cases hAll
      rcases hAll (substT ρ.left B) (substT ρ.right B) (𝒱 B ρ) with
        ⟨VB, WB, vb, wb, mSteps', nSteps', hVB⟩
      rcases mSteps with ⟨mSteps⟩
      rcases nSteps with ⟨nSteps⟩
      rcases mSteps' with ⟨mSteps'⟩
      rcases nSteps' with ⟨nSteps'⟩
      have SR :
          SubstRel (singleTyEnv B) ρ
            (extendRelSub ρ (substT ρ.left B) (substT ρ.right B) (𝒱 B ρ)) :=
        { varTo := by
            intro α V' W' v' w' h
            cases α <;> simpa [𝒱, extendRelSub, singleTyEnv] using h
        , varFrom := by
            intro α V' W' v' w' h
            cases α <;> simpa [𝒱, extendRelSub, singleTyEnv] using h }
      exact ⟨VB, WB, vb, wb,
        ⟨multi_trans (by simpa [subst] using tapp_multi mSteps)
          (multi_trans (by simpa using (beta_tlam_multi (N := _))) mSteps')⟩,
        ⟨multi_trans (by simpa [subst] using tapp_multi nSteps)
          (multi_trans (by simpa using (beta_tlam_multi (N := _))) nSteps')⟩,
        𝒱_subst (A := A) (σ := singleTyEnv B) (ρ := ρ)
          (ρ' := extendRelSub ρ (substT ρ.left B) (substT ρ.right B) (𝒱 B ρ))
          SR hVB⟩

theorem compat_tlam :
  ∀ {Γ A} (N : Term),
    (liftCtx Γ) ⊨ N ≈ N ⦂ A →
    Γ ⊨ (Λ N) ≈ (Λ N) ⦂ (∀ₜ A)
  | Γ, A, N, Nrel => by
      intro ρ γ env
      refine ⟨Λ (subst (up γ.left) N), Λ (subst (up γ.right) N),
        .vTlam, .vTlam, ⟨.refl _⟩, ⟨.refl _⟩, ?_⟩
      intro A₁ A₂ R
      have hLift :
          𝒢 (liftCtx Γ) (extendRelSub ρ A₁ A₂ R) γ :=
        liftRelEnv_related (Γ := Γ) (A₁ := A₁) (A₂ := A₂) (ρ := ρ) (γ := γ) R env
      have hN : 𝓔 A (extendRelSub ρ A₁ A₂ R) (subst γ.left N) (subst γ.right N) :=
        Nrel (extendRelSub ρ A₁ A₂ R) γ hLift
      have hup1 : up γ.left = γ.left := by
        funext i
        simp [up, renameTT]
      have hup2 : up γ.right = γ.right := by
        funext i
        simp [up, renameTT]
      simpa [𝓔, hup1, hup2] using hN

theorem fundamental :
  ∀ {Δ Γ A} (M : Term),
    Δ ⊢ Γ ⊢ M ⦂ A →
    Γ ⊨ M ≈ M ⦂ A
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
