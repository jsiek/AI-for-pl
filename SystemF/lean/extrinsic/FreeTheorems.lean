import extrinsic.Parametricity

namespace Extrinsic

def idR {A : Ty} (V : Term) : Rel A A :=
  fun V' W' _ _ => V = V' ∧ V = W'

theorem free_theorem_id :
  ∀ {A : Ty} (M V : Term),
    0 ⊢ [] ⊢ M ⦂ (∀ₜ (#0 ⇒ #0)) →
    0 ⊢ [] ⊢ V ⦂ A →
    Value V →
    Nonempty (((M ∙[]) ∙ V) —↠ V)
  | A, M, V, hM, _, vV => by
      have hRel : LogicalRel [] (∀ₜ (#0 ⇒ #0)) M M :=
        fundamental M hM
      have hEval :
          ERel (∀ₜ (#0 ⇒ #0)) emptyRelSub
            (subst emptyRelEnv.gamma1 M) (subst emptyRelEnv.gamma2 M) :=
        hRel emptyRelSub emptyRelEnv GRel_empty
      rcases hEval with ⟨_, _, vM, wM, mSteps, _, hAll⟩
      rcases mSteps with ⟨mSteps⟩
      cases vM <;> cases wM <;> simp [VRel] at hAll
      case vTlam.vTlam =>
        rename_i N1 N2
        rcases hAll A A (idR V) with ⟨F1, fSteps1, _, _, vf, wf, hFun⟩
        rcases fSteps1 with ⟨fSteps1⟩
        cases vf <;> cases wf <;> try (cases (by simpa [VRel] using hFun : False))
        case vLam.vLam =>
          have hArgRel :
              VRel (#0) (extendRelSub emptyRelSub A A (idR V)) V V vV vV := by
            simp [VRel, extendRelSub, idR]
          rcases hFun vV vV hArgRel with ⟨R1, appSteps1, R2, _, _, _, hRes⟩
          rcases appSteps1 with ⟨appSteps1⟩
          have hTappSub :=
            multi_trans (tapp_multi mSteps) (multi_trans (beta_tlam_multi (N := _)) fSteps1)
          have hSub : subst emptyRelEnv.gamma1 M = M := by
            simpa [emptyRelEnv, id] using sub_id M
          have hApp : (((M ∙[]) ∙ V)) —↠ R1 :=
            multi_trans
              (app_multi (by simpa [hSub] using hTappSub) .vLam (.refl V))
              (multi_trans (beta_lam_multi vV) appSteps1)
          have hId : V = R1 ∧ V = R2 := by
            simpa [VRel, extendRelSub, idR] using hRes
          exact ⟨by simpa [hId.1.symm] using hApp⟩

def neg : Term :=
  ƛ (ˋif ˋ0 then ˋfalse else ˋtrue)

def flip : Term :=
  ƛ (caseₜ ˋ0 [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero])

def R : Rel 𝔹 ℕ :=
  fun V W _ _ =>
    (V = ˋtrue ∧ W = ˋsuc ˋzero) ∨
    (V = ˋfalse ∧ W = ˋzero)

theorem neg_flip_related :
  VRel (#0 ⇒ #0) (extendRelSub emptyRelSub 𝔹 ℕ R) neg flip Value.vLam Value.vLam := by
  intro V W vV wW hVW
  have hVW' : R V W vV wW := by
    simpa [VRel, extendRelSub] using hVW
  rcases hVW' with hTrueOne | hFalseZero
  case inl =>
    rcases hTrueOne with ⟨hV, hW⟩
    have hNeg : Nonempty (singleSubst (ˋif ˋ0 then ˋfalse else ˋtrue) V —↠ ˋfalse) := by
      refine ⟨?_⟩
      cases hV
      simpa [singleSubst, singleEnv, subst] using
        (show (ˋif ˋtrue then ˋfalse else ˋtrue) —↠ ˋfalse from
          .step _ .beta_true (.refl _))
    have hFlip : Nonempty (singleSubst (caseₜ ˋ0 [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) W —↠ ˋzero) := by
      refine ⟨?_⟩
      cases hW
      simpa [singleSubst, singleEnv, subst] using
        (show (caseₜ (ˋsuc ˋzero) [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) —↠ ˋzero from
          .step _ (.beta_suc .vZero) (.refl _))
    have hR : VRel (#0) (extendRelSub emptyRelSub 𝔹 ℕ R) ˋfalse ˋzero .vFalse .vZero := by
      simpa [VRel, extendRelSub, R]
    exact ⟨ˋfalse, ˋzero, Value.vFalse, Value.vZero, hNeg, hFlip, hR⟩
  case inr =>
    rcases hFalseZero with ⟨hV, hW⟩
    have hNeg : Nonempty (singleSubst (ˋif ˋ0 then ˋfalse else ˋtrue) V —↠ ˋtrue) := by
      refine ⟨?_⟩
      cases hV
      simpa [singleSubst, singleEnv, subst] using
        (show (ˋif ˋfalse then ˋfalse else ˋtrue) —↠ ˋtrue from
          .step _ .beta_false (.refl _))
    have hFlip : Nonempty (singleSubst (caseₜ ˋ0 [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) W —↠ (ˋsuc ˋzero)) := by
      refine ⟨?_⟩
      cases hW
      simpa [singleSubst, singleEnv, subst] using
        (show (caseₜ ˋzero [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) —↠ (ˋsuc ˋzero) from
          .step _ .beta_zero (.refl _))
    have hR : VRel (#0) (extendRelSub emptyRelSub 𝔹 ℕ R) ˋtrue (ˋsuc ˋzero) .vTrue (.vSuc .vZero) := by
      simpa [VRel, extendRelSub, R]
    exact ⟨ˋtrue, ˋsuc ˋzero, Value.vTrue, (Value.vSuc Value.vZero), hNeg, hFlip, hR⟩

theorem free_theorem_rep :
  ∀ (M : Term),
    0 ⊢ [] ⊢ M ⦂ (∀ₜ (#0 ⇒ ((#0 ⇒ #0) ⇒ #0)) ) →
    ∃ V, ∃ W, ∃ (v : Value V), ∃ (w : Value W),
      Nonempty ((((M ∙[]) ∙ ˋtrue) ∙ neg) —↠ V) ∧
      Nonempty ((((M ∙[]) ∙ (ˋsuc ˋzero)) ∙ flip) —↠ W) ∧
      R V W v w
  | M, hM => by
      have hRel :
          LogicalRel [] (∀ₜ (#0 ⇒ ((#0 ⇒ #0) ⇒ #0)) ) M M :=
        fundamental M hM
      have hEval :
          ERel (∀ₜ (#0 ⇒ ((#0 ⇒ #0) ⇒ #0)) ) emptyRelSub
            (subst emptyRelEnv.gamma1 M) (subst emptyRelEnv.gamma2 M) :=
        hRel emptyRelSub emptyRelEnv GRel_empty
      rcases hEval with ⟨_, _, vM, wM, mSteps, nSteps, hAll⟩
      rcases mSteps with ⟨mSteps⟩
      rcases nSteps with ⟨nSteps⟩
      cases vM <;> cases wM <;> simp [VRel] at hAll
      case vTlam.vTlam =>
        rename_i N1 N2
        rcases hAll 𝔹 ℕ R with ⟨F1, fSteps1, F2, fSteps2, vf, wf, hFun⟩
        rcases fSteps1 with ⟨fSteps1⟩
        rcases fSteps2 with ⟨fSteps2⟩
        cases vf <;> cases wf <;> try (cases (by simpa [VRel] using hFun : False))
        case vLam.vLam =>
          have hArgRel :
              VRel (#0) (extendRelSub emptyRelSub 𝔹 ℕ R)
                ˋtrue (ˋsuc ˋzero) .vTrue (.vSuc .vZero) := by
            simpa [VRel, extendRelSub, R]
          rcases hFun .vTrue (.vSuc .vZero) hArgRel with
            ⟨G1, gSteps1, G2, gSteps2, vg, wg, hFun2⟩
          rcases gSteps1 with ⟨gSteps1⟩
          rcases gSteps2 with ⟨gSteps2⟩
          cases vg <;> cases wg <;> try (cases (by simpa [VRel] using hFun2 : False))
          case vLam.vLam =>
            have hNegFlipArg :
                ∀ {V' W' : Term} (v' : Value V') (w' : Value W'),
                  (extendRelSub emptyRelSub 𝔹 ℕ R).rhoR 0 V' W' v' w' →
                    ∃ VB,
                      Nonempty (singleSubst (ˋif ˋ0 then ˋfalse else ˋtrue) V' —↠ VB) ∧
                        ∃ x,
                          Nonempty (singleSubst (caseₜ ˋ0 [zero⇒ (ˋsuc ˋzero) |suc⇒ ˋzero]) W' —↠ x) ∧
                            ∃ x_1 x_2, (extendRelSub emptyRelSub 𝔹 ℕ R).rhoR 0 VB x x_1 x_2 := by
              intro V' W' v' w' hR0
              have hRelV : VRel (#0) (extendRelSub emptyRelSub 𝔹 ℕ R) V' W' v' w' := by
                simpa [VRel, extendRelSub] using hR0
              rcases neg_flip_related v' w' hRelV with
                ⟨VB, WB, vb, wb, hL, hR, hVW⟩
              exact ⟨VB, hL, WB, hR, vb, wb, by simpa [VRel, extendRelSub] using hVW⟩
            rcases hFun2 (V' := neg) (W' := flip) .vLam .vLam hNegFlipArg with
              ⟨Vres, resSteps1, Wres, resSteps2, vRes, wRes, hRes⟩
            rcases resSteps1 with ⟨resSteps1⟩
            rcases resSteps2 with ⟨resSteps2⟩
            have hSub1 : subst emptyRelEnv.gamma1 M = M := by
              simpa [emptyRelEnv, id] using sub_id M
            have hSub2 : subst emptyRelEnv.gamma2 M = M := by
              simpa [emptyRelEnv, id] using sub_id M
            have hAppL1Sub := by
              have hTapp :=
                multi_trans (tapp_multi mSteps) (multi_trans (beta_tlam_multi (N := _)) fSteps1)
              exact multi_trans
                (app_multi hTapp .vLam (.refl ˋtrue))
                (multi_trans (beta_lam_multi .vTrue) gSteps1)
            have hAppL2Sub : ((((subst emptyRelEnv.gamma1 M) ∙[]) ∙ ˋtrue) ∙ neg) —↠ Vres := by
              exact multi_trans
                (app_multi hAppL1Sub .vLam (.refl neg))
                (multi_trans (beta_lam_multi .vLam) resSteps1)
            have hAppR1Sub := by
              have hTapp :=
                multi_trans (tapp_multi nSteps) (multi_trans (beta_tlam_multi (N := _)) fSteps2)
              exact multi_trans
                (app_multi hTapp .vLam (.refl (ˋsuc ˋzero)))
                (multi_trans (beta_lam_multi (.vSuc .vZero)) gSteps2)
            have hAppR2Sub : ((((subst emptyRelEnv.gamma2 M) ∙[]) ∙ (ˋsuc ˋzero)) ∙ flip) —↠ Wres := by
              exact multi_trans
                (app_multi hAppR1Sub .vLam (.refl flip))
                (multi_trans (beta_lam_multi .vLam) resSteps2)
            have hAppL2 : ((((M ∙[]) ∙ ˋtrue) ∙ neg) —↠ Vres) := by
              simpa [hSub1] using hAppL2Sub
            have hAppR2 : ((((M ∙[]) ∙ (ˋsuc ˋzero)) ∙ flip) —↠ Wres) := by
              simpa [hSub2] using hAppR2Sub
            have hR : R Vres Wres vRes wRes := by
              simpa [VRel, extendRelSub] using hRes
            exact ⟨Vres, Wres, vRes, wRes, ⟨hAppL2⟩, ⟨hAppR2⟩, hR⟩

end Extrinsic
