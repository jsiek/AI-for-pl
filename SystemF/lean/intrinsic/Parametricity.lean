import intrinsic.LogicalRelation

namespace Intrinsic

set_option autoImplicit false

abbrev ClosedERel (A : Ty ∅) (M N : Closed A) : Prop :=
  ERel A emptyRelSub M N

theorem compat_true_closed : ClosedERel TBool (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) := by
  have hV : VRel TBool emptyRelSub
      (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ))
      (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ))
      Value.vTrue Value.vTrue := by
    simp [VRel, VBoolRel]
  exact VRel_to_ERel Value.vTrue Value.vTrue hV

theorem compat_false_closed : ClosedERel TBool (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ)) (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ)) := by
  have hV : VRel TBool emptyRelSub
      (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ))
      (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ))
      Value.vFalse Value.vFalse := by
    simp [VRel, VBoolRel]
  exact VRel_to_ERel Value.vFalse Value.vFalse hV

theorem compat_zero_closed : ClosedERel TNat (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)) (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)) := by
  have hV : VRel TNat emptyRelSub
      (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
      (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
      Value.vZero Value.vZero := by
    simp [VRel, VNatRel]
  exact VRel_to_ERel Value.vZero Value.vZero hV

def sucMulti {Δ : TyCtx} {Γ : Ctx Δ} {M N : Term Δ Γ TNat} :
    MultiStep M N → MultiStep (Term.tsuc M) (Term.tsuc N) := by
  intro h
  induction h with
  | refl M =>
      exact MultiStep.refl _
  | step L s hLN ih =>
      exact MultiStep.step _ (Step.xiSuc s) ih

theorem compat_suc_closed {M N : Closed TNat} :
    ClosedERel TNat M N → ClosedERel TNat (Term.tsuc M) (Term.tsuc N) := by
  intro h
  rcases h with ⟨V, W, v, w, hMV, hNW, hVW⟩
  rcases hMV with ⟨mv⟩
  rcases hNW with ⟨nw⟩
  have hSuc : VRel TNat emptyRelSub (Term.tsuc V) (Term.tsuc W) (Value.vSuc v) (Value.vSuc w) := by
    simpa [VRel, VNatRel] using hVW
  exact Exists.intro (Term.tsuc V)
    (Exists.intro (Term.tsuc W)
      (Exists.intro (Value.vSuc v)
        (Exists.intro (Value.vSuc w)
          (And.intro ⟨sucMulti mv⟩ (And.intro ⟨sucMulti nw⟩ hSuc)))))

end Intrinsic
