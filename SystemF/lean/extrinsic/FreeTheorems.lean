import extrinsic.Parametricity

namespace Extrinsic

def idR {A : Ty} (V : Term) : Rel A A :=
  fun V' W' _ _ _ _ => V = V' ∧ V = W'

def CtxWf (Δ : TyCtx) (Γ : Ctx) : Type :=
  ∀ {x A}, HasTypeVar Γ x A → WfTy Δ A

def ctxWf_nil {Δ : TyCtx} : CtxWf Δ [] := by
  intro x A h
  cases h

def ctxWf_cons {Δ : TyCtx} {Γ : Ctx} {A : Ty}
    (hA : WfTy Δ A) (hΓ : CtxWf Δ Γ) : CtxWf Δ (A :: Γ) := by
  intro x B hx
  cases hx with
  | Z =>
      exact hA
  | S hx' =>
      exact hΓ hx'

def ctxWf_lift {Δ : TyCtx} {Γ : Ctx}
    (hΓ : CtxWf Δ Γ) : CtxWf (Δ + 1) (liftCtx Γ) := by
  intro x A hx
  rcases lookup_map_inv (Γ := Γ) (x := x) (B := A) (f := renameT Nat.succ) hx with
    ⟨B, ⟨hB, hEq⟩⟩
  have hBwf : WfTy Δ B := hΓ hB
  have hShift : TyRenameWf Δ (Δ + 1) Nat.succ := by
    intro i hi
    exact Nat.succ_lt_succ hi
  exact Eq.ndrec
    (motive := fun T => WfTy (Δ + 1) T)
    (renameT_preserves_WfTy hBwf hShift)
    hEq.symm

def typing_wf :
  ∀ {Δ Γ M A}, CtxWf Δ Γ → Δ ⊢ Γ ⊢ M ⦂ A → WfTy Δ A
  | _, _, _, _, hΓ, .t_var h =>
      hΓ h
  | _, _, _, _, hΓ, .t_lam hA hN =>
      .fn hA (typing_wf (ctxWf_cons hA hΓ) hN)
  | _, _, _, _, hΓ, .t_app hL hM =>
      match typing_wf hΓ hL with
      | .fn _ hB => hB
  | _, _, _, _, _, .t_true =>
      .bool
  | _, _, _, _, _, .t_false =>
      .bool
  | _, _, _, _, _, .t_zero =>
      .nat
  | _, _, _, _, hΓ, .t_suc hM =>
      match typing_wf hΓ hM with
      | .nat => .nat
  | _, _, _, _, hΓ, .t_case hL hM hN =>
      typing_wf hΓ hM
  | _, _, _, _, hΓ, .t_if hL hM hN =>
      typing_wf hΓ hM
  | _, _, _, _, hΓ, .t_tlam hN =>
      .all (typing_wf (ctxWf_lift hΓ) hN)
  | _, _, _, _, hΓ, .t_tapp hM hB =>
      match typing_wf hΓ hM with
      | .all hBody =>
          have hσ : TySubstWf (_ + 1) _ (singleTyEnv _) := by
            intro X hX
            cases X with
            | zero =>
                simpa [singleTyEnv] using hB
            | succ X =>
                have hX' : X < _ := Nat.lt_of_succ_lt_succ hX
                simpa [singleTyEnv] using (WfTy.var (Δ := _) (X := X) hX')
          by
            simpa [substOneT] using substT_preserves_WfTy hBody hσ

theorem free_theorem_id :
  ∀ {A : Ty} (M V : Term),
    0 ⊢ [] ⊢ M ⦂ (∀ₜ (#0 ⇒ #0)) →
    0 ⊢ [] ⊢ V ⦂ A →
    Value V →
    Nonempty ((Term.app (Term.tapp M A) V) —↠ V)
  | A, M, V, hM, hV, vV => by
      have hAwf : WfTy 0 A :=
        typing_wf (Δ := 0) (Γ := []) (M := V) (A := A) ctxWf_nil hV
      have hRel : [] ⊨ M ≈ M ⦂ (∀ₜ (#0 ⇒ #0)) :=
        fundamental M hM
      have hEval :
          𝓔 (∀ₜ (#0 ⇒ #0)) emptyRelSub
            (substTT emptyRelSub.left (subst emptyRelEnv.left M))
            (substTT emptyRelSub.right (subst emptyRelEnv.right M)) :=
        hRel emptyRelSub emptyRelEnv 𝒢_empty
      simp only [𝓔] at hEval
      rcases hEval with ⟨_, _, VM, WM, vM, wM, mSteps, _, hAll⟩
      rcases mSteps with ⟨mSteps⟩
      cases vM <;> cases wM <;> simp [𝒱] at hAll
      case vTlam.vTlam =>
        rcases hAll with ⟨_, _, hAll⟩
        have hFunEval := hAll A A hAwf hAwf (idR V)
        simp only [𝓔] at hFunEval
        rcases hFunEval with ⟨_, _, F1, F2, vf, wf, fSteps1, _, hFun⟩
        rcases fSteps1 with ⟨fSteps1⟩
        cases vf <;> cases wf <;> simp [𝒱] at hFun
        case vLam.vLam =>
          rcases hFun with ⟨_, _, hFun⟩
          have hResEval := hFun vV vV hV hV (by simp [extendRelSub, idR])
          simp only [𝓔] at hResEval
          rcases hResEval with ⟨_, _, R1, R2, _, _, appSteps1, _, hRes⟩
          rcases appSteps1 with ⟨appSteps1⟩
          have hTappSub :
              Term.tapp (substTT emptyRelSub.left (subst emptyRelEnv.left M)) A —↠ _ :=
            multi_trans
              (tapp_multi (A := A) mSteps)
              (multi_trans
                (beta_tlam_multi (N := _) (A := A))
                fSteps1)
          have hAppSub :
              Term.app (Term.tapp (substTT emptyRelSub.left (subst emptyRelEnv.left M)) A) V —↠ R1 :=
            multi_trans
              (app_multi hTappSub .vLam (.refl V))
              (multi_trans (beta_lam_multi vV) appSteps1)
          have hMSub :
              substTT emptyRelSub.left (subst emptyRelEnv.left M) = M := by
            have hSubId : subst emptyRelEnv.left M = M := by
              simpa [emptyRelEnv] using sub_id M
            have hTTId :
                substTT emptyRelSub.left M = M :=
              substTT_id_typed (hM := hM) (hσ := by
                intro α hα
                exact False.elim (Nat.not_lt_zero α hα))
            calc
              substTT emptyRelSub.left (subst emptyRelEnv.left M)
                  = substTT emptyRelSub.left M := by
                      simpa [hSubId]
              _ = M := hTTId
          have hApp :
              Term.app (Term.tapp M A) V —↠ R1 := by
            exact Eq.ndrec
              (motive := fun T => Term.app (Term.tapp T A) V —↠ R1)
              hAppSub
              hMSub
          have hId : V = R1 ∧ V = R2 := by
            have hRes' := hRes
            simp [𝒱] at hRes'
            rcases hRes' with ⟨_, ⟨_, hId⟩⟩
            exact hId
          exact ⟨by simpa [hId.1.symm] using hApp⟩

def neg : Term :=
  ƛ[ 𝔹 ] (ˋif ˋ0 then ˋfalse else ˋtrue)

def flip : Term :=
  ƛ[ ℕ ] (caseₜ ˋ0 [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero])

def R : Rel 𝔹 ℕ :=
  fun V W _ _ _ _ =>
    (V = ˋtrue ∧ W = ˋsuc ˋzero) ∨
    (V = ˋfalse ∧ W = ˋzero)

theorem neg_flip_related :
  𝒱 (#0 ⇒ #0)
    (extendRelSub emptyRelSub 𝔹 ℕ .bool .nat R)
    neg flip Value.vLam Value.vLam
  := by
    unfold neg flip
    let ρ : RelSub := extendRelSub emptyRelSub 𝔹 ℕ .bool .nat R
    simp [𝒱, substT, ρ]
    refine Exists.intro ?_ ?_
    · simpa [substT] using
        (HasType.t_lam (Δ := 0) (Γ := []) (A := 𝔹) (B := 𝔹)
          .bool
          (HasType.t_if
            (HasType.t_var (Δ := 0) (Γ := [𝔹]) (i := 0) (A := 𝔹) HasTypeVar.Z)
            .t_false
            .t_true))
    · refine Exists.intro ?_ ?_
      · simpa [substT] using
          (HasType.t_lam (Δ := 0) (Γ := []) (A := ℕ) (B := ℕ)
            .nat
            (HasType.t_case
              (HasType.t_var (Δ := 0) (Γ := [ℕ]) (i := 0) (A := ℕ) HasTypeVar.Z)
              (HasType.t_suc (HasType.t_zero))
              (HasType.t_var (Δ := 0) (Γ := [ℕ, ℕ]) (i := 0) (A := ℕ) HasTypeVar.Z)))
      · intro V W vV wW hVT hWT hRel
        rcases hRel with hTrueOne | hFalseZero
        · rcases hTrueOne with ⟨hVeq, hWeq⟩
          have hL :
              0 ⊢ [] ⊢ singleSubst (ˋif ˋ0 then ˋfalse else ˋtrue) V ⦂ 𝔹 := by
            cases hVeq
            simpa [singleSubst, singleEnv, subst] using
              (HasType.t_if
                (HasType.t_true)
                (HasType.t_false)
                (HasType.t_true))
          have hR :
              0 ⊢ [] ⊢ singleSubst (caseₜ ˋ0 [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) W ⦂ ℕ := by
            cases hWeq
            simpa [singleSubst, singleEnv, subst] using
              (HasType.t_case
                (HasType.t_suc (HasType.t_zero))
                (HasType.t_suc (HasType.t_zero))
                (HasType.t_zero))
          have redL : Nonempty (singleSubst (ˋif ˋ0 then ˋfalse else ˋtrue) V —↠ ˋfalse) := by
            refine ⟨?_⟩
            cases hVeq
            simpa [singleSubst, singleEnv, subst] using
              (show (ˋif ˋtrue then ˋfalse else ˋtrue) —↠ ˋfalse from
                .step _ .beta_true (.refl _))
          have redR : Nonempty (singleSubst (caseₜ ˋ0 [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) W —↠ ˋzero) := by
            refine ⟨?_⟩
            cases hWeq
            simpa [singleSubst, singleEnv, subst] using
              (show (caseₜ (ˋsuc ˋzero) [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) —↠ ˋzero from
                .step _ (.beta_suc .vZero) (.refl _))
          have hOut :
              𝒱 (#0) ρ ˋfalse ˋzero .vFalse .vZero := by
            exact ⟨.t_false, ⟨.t_zero, Or.inr ⟨rfl, rfl⟩⟩⟩
          exact ⟨hL, hR, ˋfalse, ˋzero, .vFalse, .vZero, redL, redR, hOut⟩
        · rcases hFalseZero with ⟨hVeq, hWeq⟩
          have hL :
              0 ⊢ [] ⊢ singleSubst (ˋif ˋ0 then ˋfalse else ˋtrue) V ⦂ 𝔹 := by
            cases hVeq
            simpa [singleSubst, singleEnv, subst] using
              (HasType.t_if
                (HasType.t_false)
                (HasType.t_false)
                (HasType.t_true))
          have hR :
              0 ⊢ [] ⊢ singleSubst (caseₜ ˋ0 [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) W ⦂ ℕ := by
            cases hWeq
            simpa [singleSubst, singleEnv, subst] using
              (HasType.t_case
                (HasType.t_zero)
                (HasType.t_suc (HasType.t_zero))
                (HasType.t_zero))
          have redL : Nonempty (singleSubst (ˋif ˋ0 then ˋfalse else ˋtrue) V —↠ ˋtrue) := by
            refine ⟨?_⟩
            cases hVeq
            simpa [singleSubst, singleEnv, subst] using
              (show (ˋif ˋfalse then ˋfalse else ˋtrue) —↠ ˋtrue from
                .step _ .beta_false (.refl _))
          have redR : Nonempty (singleSubst (caseₜ ˋ0 [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) W —↠ (ˋsuc ˋzero)) := by
            refine ⟨?_⟩
            cases hWeq
            simpa [singleSubst, singleEnv, subst] using
              (show (caseₜ ˋzero [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) —↠ (ˋsuc ˋzero) from
                .step _ .beta_zero (.refl _))
          have hOut :
              𝒱 (#0) ρ ˋtrue (ˋsuc ˋzero) .vTrue (.vSuc .vZero) := by
            exact ⟨.t_true, ⟨.t_suc .t_zero, Or.inl ⟨rfl, rfl⟩⟩⟩
          exact ⟨hL, hR, ˋtrue, ˋsuc ˋzero, .vTrue, .vSuc .vZero, redL, redR, hOut⟩

theorem free_theorem_rep :
  ∀ (M : Term),
    0 ⊢ [] ⊢ M ⦂ (∀ₜ (#0 ⇒ ((#0 ⇒ #0) ⇒ #0))) →
    ∃ V, ∃ W, ∃ (_v : Value V), ∃ (_w : Value W),
      Nonempty ((Term.app (Term.app (Term.tapp M 𝔹) Term.ttrue) neg) —↠ V) ∧
      Nonempty ((Term.app (Term.app (Term.tapp M ℕ) (Term.suc Term.zero)) flip) —↠ W) ∧
      (∃ (hV : 0 ⊢ [] ⊢ V ⦂ 𝔹), ∃ (hW : 0 ⊢ [] ⊢ W ⦂ ℕ), R V W _v _w hV hW)
  | M, hM => by
      have hRel :
          [] ⊨ M ≈ M ⦂ (∀ₜ (#0 ⇒ ((#0 ⇒ #0) ⇒ #0))) :=
        fundamental M hM
      have hEval :
          𝓔 (∀ₜ (#0 ⇒ ((#0 ⇒ #0) ⇒ #0))) emptyRelSub
            (substTT emptyRelSub.left (subst emptyRelEnv.left M))
            (substTT emptyRelSub.right (subst emptyRelEnv.right M)) :=
        hRel emptyRelSub emptyRelEnv 𝒢_empty
      simp only [𝓔] at hEval
      rcases hEval with ⟨_, _, VM, WM, vM, wM, mSteps, nSteps, hAll⟩
      rcases mSteps with ⟨mSteps⟩
      rcases nSteps with ⟨nSteps⟩
      cases vM <;> cases wM <;> simp [𝒱] at hAll
      case vTlam.vTlam =>
        rcases hAll with ⟨_, _, hAll⟩
        have hFunEval := hAll 𝔹 ℕ .bool .nat R
        simp only [𝓔] at hFunEval
        rcases hFunEval with ⟨_, _, F1, F2, vf, wf, fSteps1, fSteps2, hFun⟩
        rcases fSteps1 with ⟨fSteps1⟩
        rcases fSteps2 with ⟨fSteps2⟩
        cases vf <;> cases wf <;> simp [𝒱] at hFun
        case vLam.vLam =>
          rcases hFun with ⟨_, _, hFun⟩
          have hFun2Eval := hFun
            .vTrue
            (.vSuc .vZero)
            .t_true
            (.t_suc .t_zero)
            (Or.inl ⟨rfl, rfl⟩)
          simp only [𝓔] at hFun2Eval
          rcases hFun2Eval with ⟨_, _, G1, G2, vg, wg, gSteps1, gSteps2, hFun2⟩
          rcases gSteps1 with ⟨gSteps1⟩
          rcases gSteps2 with ⟨gSteps2⟩
          cases vg <;> cases wg <;> simp [𝒱] at hFun2
          case vLam.vLam =>
            rcases hFun2 with ⟨_, _, hFun2⟩
            have hResEval := hFun2 .vLam .vLam neg_flip_related
            simp only [𝓔] at hResEval
            rcases hResEval with ⟨_, _, Vres, Wres, vRes, wRes, resSteps1, resSteps2, hRes⟩
            rcases resSteps1 with ⟨resSteps1⟩
            rcases resSteps2 with ⟨resSteps2⟩
            have hMSubL :
                substTT emptyRelSub.left (subst emptyRelEnv.left M) = M := by
              have hSubId : subst emptyRelEnv.left M = M := by
                simpa [emptyRelEnv] using sub_id M
              have hTTId :
                  substTT emptyRelSub.left M = M :=
                substTT_id_typed (hM := hM) (hσ := by
                  intro α hα
                  exact False.elim (Nat.not_lt_zero α hα))
              calc
                substTT emptyRelSub.left (subst emptyRelEnv.left M)
                    = substTT emptyRelSub.left M := by simpa [hSubId]
                _ = M := hTTId
            have hMSubR :
                substTT emptyRelSub.right (subst emptyRelEnv.right M) = M := by
              have hSubId : subst emptyRelEnv.right M = M := by
                simpa [emptyRelEnv] using sub_id M
              have hTTId :
                  substTT emptyRelSub.right M = M :=
                substTT_id_typed (hM := hM) (hσ := by
                  intro α hα
                  exact False.elim (Nat.not_lt_zero α hα))
              calc
                substTT emptyRelSub.right (subst emptyRelEnv.right M)
                    = substTT emptyRelSub.right M := by simpa [hSubId]
                _ = M := hTTId
            have hAppLSub :
                Term.app (Term.app (Term.tapp (substTT emptyRelSub.left (subst emptyRelEnv.left M)) 𝔹) ˋtrue) neg —↠ Vres := by
              have hTapp :=
                multi_trans
                  (tapp_multi (A := 𝔹) mSteps)
                  (multi_trans
                    (beta_tlam_multi (N := _) (A := 𝔹))
                    fSteps1)
              have hApp1 :=
                multi_trans
                  (app_multi hTapp .vLam (.refl ˋtrue))
                  (multi_trans (beta_lam_multi .vTrue) gSteps1)
              exact multi_trans
                (app_multi hApp1 .vLam (.refl neg))
                (multi_trans (beta_lam_multi .vLam) resSteps1)
            have hAppRSub :
                Term.app
                  (Term.app (Term.tapp (substTT emptyRelSub.right (subst emptyRelEnv.right M)) ℕ) (ˋsuc ˋzero))
                  flip —↠ Wres := by
              have hTapp :=
                multi_trans
                  (tapp_multi (A := ℕ) nSteps)
                  (multi_trans
                    (beta_tlam_multi (N := _) (A := ℕ))
                    fSteps2)
              have hApp1 :=
                multi_trans
                  (app_multi hTapp .vLam (.refl (ˋsuc ˋzero)))
                  (multi_trans (beta_lam_multi (.vSuc .vZero)) gSteps2)
              exact multi_trans
                (app_multi hApp1 .vLam (.refl flip))
                (multi_trans (beta_lam_multi .vLam) resSteps2)
            have hAppL :
                Term.app (Term.app (Term.tapp M 𝔹) Term.ttrue) neg —↠ Vres := by
              exact Eq.ndrec
                (motive := fun T => Term.app (Term.app (Term.tapp T 𝔹) Term.ttrue) neg —↠ Vres)
                hAppLSub
                hMSubL
            have hAppR :
                Term.app (Term.app (Term.tapp M ℕ) (Term.suc Term.zero)) flip —↠ Wres := by
              exact Eq.ndrec
                (motive := fun T =>
                  Term.app (Term.app (Term.tapp T ℕ) (Term.suc Term.zero)) flip —↠ Wres)
                hAppRSub
                hMSubR
            have hR :
                ∃ (hV : 0 ⊢ [] ⊢ Vres ⦂ 𝔹),
                  ∃ (hW : 0 ⊢ [] ⊢ Wres ⦂ ℕ),
                    R Vres Wres vRes wRes hV hW := by
              simpa [𝒱, extendRelSub] using hRes
            exact ⟨Vres, Wres, vRes, wRes, ⟨hAppL⟩, ⟨hAppR⟩, hR⟩

end Extrinsic
