import extrinsic.Parametricity

namespace Extrinsic

-- File Charter:
--   * Ports free-theorem statements to the extrinsic System F setting.
--   * Reuses the extrinsic logical relation to state relation witnesses.

def idR {A : Ty} (V : Term) : Rel A A :=
  fun V' W' _ _ _ _ => V = V' ∧ V = W'

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
    have hCore :
        ∃ (hV : 0 ⊢ [] ⊢ (ƛ[ 𝔹 ] (ˋif ˋ0 then ˋfalse else ˋtrue)) ⦂ (𝔹 ⇒ 𝔹)),
          ∃ (hW : 0 ⊢ [] ⊢ (ƛ[ ℕ ] (caseₜ ˋ0 [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero])) ⦂ (ℕ ⇒ ℕ)),
            ∀ {V W} (vV : Value V) (wW : Value W) (hVT : 0 ⊢ [] ⊢ V ⦂ 𝔹) (hWT : 0 ⊢ [] ⊢ W ⦂ ℕ),
              R V W vV wW hVT hWT →
                𝓔 (#0)
                  (extendRelSub emptyRelSub 𝔹 ℕ .bool .nat R)
                  (singleSubst (ˋif ˋ0 then ˋfalse else ˋtrue) V)
                  (singleSubst (caseₜ ˋ0 [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) W) := by
      exact Exists.intro
        (HasType.t_lam (Δ := 0) (Γ := []) (A := 𝔹) (B := 𝔹)
          .bool
          (HasType.t_if
            (HasType.t_var (Δ := 0) (Γ := [𝔹]) (i := 0) (A := 𝔹) HasTypeVar.Z)
            .t_false
            .t_true))
        (Exists.intro
          (HasType.t_lam (Δ := 0) (Γ := []) (A := ℕ) (B := ℕ)
            .nat
            (HasType.t_case
              (HasType.t_var (Δ := 0) (Γ := [ℕ]) (i := 0) (A := ℕ) HasTypeVar.Z)
              (HasType.t_suc (HasType.t_zero))
              (HasType.t_zero)))
          (by
            intro V W vV wW hVT hWT hRel
            cases hRel with
            | inl hTrueOne =>
              rcases hTrueOne with ⟨rfl, rfl⟩
              have hL : 0 ⊢ [] ⊢ singleSubst (ˋif ˋ0 then ˋfalse else ˋtrue) ˋtrue ⦂ 𝔹 := by
                simpa [singleSubst, singleEnv, subst] using
                  (HasType.t_if (A := 𝔹) hVT .t_false .t_true)
              have hR : 0 ⊢ [] ⊢ singleSubst (caseₜ ˋ0 [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) (ˋsuc ˋzero) ⦂ ℕ := by
                simpa [singleSubst, singleEnv, subst] using
                  (HasType.t_case (A := ℕ) hWT (.t_suc .t_zero) (.t_zero))
              have redL : Nonempty (singleSubst (ˋif ˋ0 then ˋfalse else ˋtrue) ˋtrue —↠ ˋfalse) := by
                exact ⟨by
                  simpa [singleSubst, singleEnv, subst] using
                    (show (ˋif ˋtrue then ˋfalse else ˋtrue) —↠ ˋfalse from
                      .step _ .beta_true (.refl _))⟩
              have redR :
                  Nonempty (singleSubst (caseₜ ˋ0 [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) (ˋsuc ˋzero) —↠ ˋzero) := by
                exact ⟨by
                  simpa [singleSubst, singleEnv, subst] using
                    (show (caseₜ (ˋsuc ˋzero) [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) —↠ ˋzero from
                      .step _ (.beta_suc .vZero) (.refl _))⟩
              have hOut :
                  𝒱 (#0)
                    (extendRelSub emptyRelSub 𝔹 ℕ .bool .nat R)
                    ˋfalse ˋzero .vFalse .vZero := by
                simpa [𝒱, extendRelSub] using
                  (show ∃ (hV : 0 ⊢ [] ⊢ ˋfalse ⦂ 𝔹), ∃ (hW : 0 ⊢ [] ⊢ ˋzero ⦂ ℕ),
                      R ˋfalse ˋzero .vFalse .vZero hV hW from
                    ⟨.t_false, ⟨.t_zero, Or.inr ⟨rfl, rfl⟩⟩⟩)
              have hE :
                  𝓔 (#0)
                    (extendRelSub emptyRelSub 𝔹 ℕ .bool .nat R)
                    (singleSubst (ˋif ˋ0 then ˋfalse else ˋtrue) ˋtrue)
                    (singleSubst (caseₜ ˋ0 [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) (ˋsuc ˋzero)) := by
                unfold 𝓔
                exact Exists.intro hL
                  (Exists.intro hR
                    (Exists.intro ˋfalse
                      (Exists.intro ˋzero
                        (Exists.intro Value.vFalse
                          (Exists.intro Value.vZero
                            (And.intro redL (And.intro redR hOut)))))))
              exact hE
            | inr hFalseZero =>
              rcases hFalseZero with ⟨rfl, rfl⟩
              have hL : 0 ⊢ [] ⊢ singleSubst (ˋif ˋ0 then ˋfalse else ˋtrue) ˋfalse ⦂ 𝔹 := by
                simpa [singleSubst, singleEnv, subst] using
                  (HasType.t_if (A := 𝔹) hVT .t_false .t_true)
              have hR : 0 ⊢ [] ⊢ singleSubst (caseₜ ˋ0 [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) ˋzero ⦂ ℕ := by
                simpa [singleSubst, singleEnv, subst] using
                  (HasType.t_case (A := ℕ) hWT (.t_suc .t_zero) (.t_zero))
              have redL : Nonempty (singleSubst (ˋif ˋ0 then ˋfalse else ˋtrue) ˋfalse —↠ ˋtrue) := by
                exact ⟨by
                  simpa [singleSubst, singleEnv, subst] using
                    (show (ˋif ˋfalse then ˋfalse else ˋtrue) —↠ ˋtrue from
                      .step _ .beta_false (.refl _))⟩
              have redR :
                  Nonempty (singleSubst (caseₜ ˋ0 [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) ˋzero —↠ (ˋsuc ˋzero)) := by
                exact ⟨by
                  simpa [singleSubst, singleEnv, subst] using
                    (show (caseₜ ˋzero [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) —↠ (ˋsuc ˋzero) from
                      .step _ .beta_zero (.refl _))⟩
              have hOut :
                  𝒱 (#0)
                    (extendRelSub emptyRelSub 𝔹 ℕ .bool .nat R)
                    ˋtrue (ˋsuc ˋzero) .vTrue (.vSuc .vZero) := by
                simpa [𝒱, extendRelSub] using
                  (show ∃ (hV : 0 ⊢ [] ⊢ ˋtrue ⦂ 𝔹), ∃ (hW : 0 ⊢ [] ⊢ (ˋsuc ˋzero) ⦂ ℕ),
                      R ˋtrue (ˋsuc ˋzero) .vTrue (.vSuc .vZero) hV hW from
                    ⟨.t_true, ⟨.t_suc .t_zero, Or.inl ⟨rfl, rfl⟩⟩⟩)
              have hE :
                  𝓔 (#0)
                    (extendRelSub emptyRelSub 𝔹 ℕ .bool .nat R)
                    (singleSubst (ˋif ˋ0 then ˋfalse else ˋtrue) ˋfalse)
                    (singleSubst (caseₜ ˋ0 [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) ˋzero) := by
                unfold 𝓔
                exact Exists.intro hL
                  (Exists.intro hR
                    (Exists.intro ˋtrue
                      (Exists.intro (ˋsuc ˋzero)
                        (Exists.intro Value.vTrue
                          (Exists.intro (Value.vSuc Value.vZero)
                            (And.intro redL (And.intro redR hOut)))))))
              exact hE))
    simpa [neg, flip, 𝒱, substT, extendRelSub] using hCore

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
