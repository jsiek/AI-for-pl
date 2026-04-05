import extrinsic.Parametricity

namespace Extrinsic

def idR {A : Ty} (V : Term) : Rel A A :=
  fun V' W' _ _ => V = V' ∧ V = W'

theorem free_theorem_id :
  ∀ {A : Ty} (M V : Term),
    HasType 0 [] M (.all (.fn (.var 0) (.var 0))) →
    HasType 0 [] V A →
    Value V →
    Nonempty ((.app (.tapp M) V) —↠ V)
  | A, M, V, hM, _, vV => by
      have hRel : LogicalRel [] (.all (.fn (.var 0) (.var 0))) M M :=
        fundamental M hM
      have hEval :
          ERel (.all (.fn (.var 0) (.var 0))) emptyRelSub
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
              VRel (.var 0) (extendRelSub emptyRelSub A A (idR V)) V V vV vV := by
            simp [VRel, extendRelSub, idR]
          rcases hFun vV vV hArgRel with ⟨R1, appSteps1, R2, _, _, _, hRes⟩
          rcases appSteps1 with ⟨appSteps1⟩
          have hTappSub :=
            multi_trans (tapp_multi mSteps) (multi_trans (beta_tlam_multi (N := _)) fSteps1)
          have hSub : subst emptyRelEnv.gamma1 M = M := by
            simpa [emptyRelEnv, id] using sub_id M
          have hApp : (.app (.tapp M) V) —↠ R1 :=
            multi_trans
              (app_multi (by simpa [hSub] using hTappSub) .vLam (.refl V))
              (multi_trans (beta_lam_multi vV) appSteps1)
          have hId : V = R1 ∧ V = R2 := by
            simpa [VRel, extendRelSub, idR] using hRes
          exact ⟨by simpa [hId.1.symm] using hApp⟩

def neg : Term :=
  .lam (.ite (.var 0) .tfalse .ttrue)

def flip : Term :=
  .lam (.natCase (.var 0) (.suc .zero) .zero)

def R : Rel .bool .nat :=
  fun V W _ _ =>
    (V = .ttrue ∧ W = .suc .zero) ∨
    (V = .tfalse ∧ W = .zero)

theorem neg_flip_related :
  VRel (.fn (.var 0) (.var 0)) (extendRelSub emptyRelSub .bool .nat R) neg flip Value.vLam Value.vLam := by
  intro V W vV wW hVW
  have hVW' : R V W vV wW := by
    simpa [VRel, extendRelSub] using hVW
  rcases hVW' with hTrueOne | hFalseZero
  case inl =>
    rcases hTrueOne with ⟨hV, hW⟩
    have hNeg : Nonempty (singleSubst (.ite (.var 0) .tfalse .ttrue) V —↠ .tfalse) := by
      refine ⟨?_⟩
      cases hV
      simpa [singleSubst, singleEnv, subst] using
        (show (.ite .ttrue .tfalse .ttrue) —↠ .tfalse from
          .step _ .beta_true (.refl _))
    have hFlip : Nonempty (singleSubst (.natCase (.var 0) (.suc .zero) .zero) W —↠ .zero) := by
      refine ⟨?_⟩
      cases hW
      simpa [singleSubst, singleEnv, subst] using
        (show (.natCase (.suc .zero) (.suc .zero) .zero) —↠ .zero from
          .step _ (.beta_suc .vZero) (.refl _))
    have hR : VRel (.var 0) (extendRelSub emptyRelSub .bool .nat R) .tfalse .zero .vFalse .vZero := by
      simpa [VRel, extendRelSub, R]
    exact ⟨Term.tfalse, Term.zero, Value.vFalse, Value.vZero, hNeg, hFlip, hR⟩
  case inr =>
    rcases hFalseZero with ⟨hV, hW⟩
    have hNeg : Nonempty (singleSubst (.ite (.var 0) .tfalse .ttrue) V —↠ .ttrue) := by
      refine ⟨?_⟩
      cases hV
      simpa [singleSubst, singleEnv, subst] using
        (show (.ite .tfalse .tfalse .ttrue) —↠ .ttrue from
          .step _ .beta_false (.refl _))
    have hFlip : Nonempty (singleSubst (.natCase (.var 0) (.suc .zero) .zero) W —↠ (.suc .zero)) := by
      refine ⟨?_⟩
      cases hW
      simpa [singleSubst, singleEnv, subst] using
        (show (.natCase .zero (.suc .zero) .zero) —↠ (.suc .zero) from
          .step _ .beta_zero (.refl _))
    have hR : VRel (.var 0) (extendRelSub emptyRelSub .bool .nat R) .ttrue (.suc .zero) .vTrue (.vSuc .vZero) := by
      simpa [VRel, extendRelSub, R]
    exact ⟨Term.ttrue, (Term.suc Term.zero), Value.vTrue, (Value.vSuc Value.vZero), hNeg, hFlip, hR⟩

theorem free_theorem_rep :
  ∀ (M : Term),
    HasType 0 [] M (.all (.fn (.var 0) (.fn (.fn (.var 0) (.var 0)) (.var 0)))) →
    ∃ V, ∃ W, ∃ (v : Value V), ∃ (w : Value W),
      Nonempty ((.app (.app (.tapp M) .ttrue) neg) —↠ V) ∧
      Nonempty ((.app (.app (.tapp M) (.suc .zero)) flip) —↠ W) ∧
      R V W v w
  | M, hM => by
      have hRel :
          LogicalRel [] (.all (.fn (.var 0) (.fn (.fn (.var 0) (.var 0)) (.var 0)))) M M :=
        fundamental M hM
      have hEval :
          ERel (.all (.fn (.var 0) (.fn (.fn (.var 0) (.var 0)) (.var 0)))) emptyRelSub
            (subst emptyRelEnv.gamma1 M) (subst emptyRelEnv.gamma2 M) :=
        hRel emptyRelSub emptyRelEnv GRel_empty
      rcases hEval with ⟨_, _, vM, wM, mSteps, nSteps, hAll⟩
      rcases mSteps with ⟨mSteps⟩
      rcases nSteps with ⟨nSteps⟩
      cases vM <;> cases wM <;> simp [VRel] at hAll
      case vTlam.vTlam =>
        rename_i N1 N2
        rcases hAll .bool .nat R with ⟨F1, fSteps1, F2, fSteps2, vf, wf, hFun⟩
        rcases fSteps1 with ⟨fSteps1⟩
        rcases fSteps2 with ⟨fSteps2⟩
        cases vf <;> cases wf <;> try (cases (by simpa [VRel] using hFun : False))
        case vLam.vLam =>
          have hArgRel :
              VRel (.var 0) (extendRelSub emptyRelSub .bool .nat R)
                .ttrue (.suc .zero) .vTrue (.vSuc .vZero) := by
            simpa [VRel, extendRelSub, R]
          rcases hFun .vTrue (.vSuc .vZero) hArgRel with
            ⟨G1, gSteps1, G2, gSteps2, vg, wg, hFun2⟩
          rcases gSteps1 with ⟨gSteps1⟩
          rcases gSteps2 with ⟨gSteps2⟩
          cases vg <;> cases wg <;> try (cases (by simpa [VRel] using hFun2 : False))
          case vLam.vLam =>
            have hNegFlipArg :
                ∀ {V' W' : Term} (v' : Value V') (w' : Value W'),
                  (extendRelSub emptyRelSub .bool .nat R).rhoR 0 V' W' v' w' →
                    ∃ VB,
                      Nonempty (singleSubst (.ite (.var 0) .tfalse .ttrue) V' —↠ VB) ∧
                        ∃ x,
                          Nonempty (singleSubst (.natCase (.var 0) (.suc .zero) .zero) W' —↠ x) ∧
                            ∃ x_1 x_2, (extendRelSub emptyRelSub .bool .nat R).rhoR 0 VB x x_1 x_2 := by
              intro V' W' v' w' hR0
              have hRelV : VRel (.var 0) (extendRelSub emptyRelSub .bool .nat R) V' W' v' w' := by
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
                (app_multi hTapp .vLam (.refl .ttrue))
                (multi_trans (beta_lam_multi .vTrue) gSteps1)
            have hAppL2Sub : (.app (.app (.tapp (subst emptyRelEnv.gamma1 M)) .ttrue) neg) —↠ Vres := by
              exact multi_trans
                (app_multi hAppL1Sub .vLam (.refl neg))
                (multi_trans (beta_lam_multi .vLam) resSteps1)
            have hAppR1Sub := by
              have hTapp :=
                multi_trans (tapp_multi nSteps) (multi_trans (beta_tlam_multi (N := _)) fSteps2)
              exact multi_trans
                (app_multi hTapp .vLam (.refl (.suc .zero)))
                (multi_trans (beta_lam_multi (.vSuc .vZero)) gSteps2)
            have hAppR2Sub : (.app (.app (.tapp (subst emptyRelEnv.gamma2 M)) (.suc .zero)) flip) —↠ Wres := by
              exact multi_trans
                (app_multi hAppR1Sub .vLam (.refl flip))
                (multi_trans (beta_lam_multi .vLam) resSteps2)
            have hAppL2 : (.app (.app (.tapp M) .ttrue) neg) —↠ Vres := by
              simpa [hSub1] using hAppL2Sub
            have hAppR2 : (.app (.app (.tapp M) (.suc .zero)) flip) —↠ Wres := by
              simpa [hSub2] using hAppR2Sub
            have hR : R Vres Wres vRes wRes := by
              simpa [VRel, extendRelSub] using hRes
            exact ⟨Vres, Wres, vRes, wRes, ⟨hAppL2⟩, ⟨hAppR2⟩, hR⟩

end Extrinsic
