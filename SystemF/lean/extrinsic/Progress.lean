import extrinsic.Reduction

namespace Extrinsic

-- File Charter:
--   * Progress theorem for well-typed closed extrinsic System F terms.
--   * Defines canonical-form witnesses for function, boolean, and natural values.
--   * Powers evaluation and type-safety wrappers.

inductive Progress (M : Term) : Type where
  | done : Value M → Progress M
  | step : ∀ {N}, M —→ N → Progress M

inductive CanonBool (V : Term) : Type where
  | isTrue : V = Term.ttrue → CanonBool V
  | isFalse : V = Term.tfalse → CanonBool V

inductive CanonNat (V : Term) : Type where
  | isZero : V = Term.zero → CanonNat V
  | isSuc : (W : Term) → V = Term.suc W → Value W → CanonNat V

def canonical_fn :
  ∀ {Δ V A B},
    Value V →
    Δ ⊢ [] ⊢ V ⦂ (A ⇒ B) →
    Σ A', {N : Term // V = Term.lam A' N}
  | _, _, _, _, .vLam, .t_lam _ _ => ⟨_, ⟨_, rfl⟩⟩
  | _, _, _, _, .vTrue, h => by cases h
  | _, _, _, _, .vFalse, h => by cases h
  | _, _, _, _, .vZero, h => by cases h
  | _, _, _, _, .vSuc _, h => by cases h
  | _, _, _, _, .vTlam, h => by cases h

def canonical_bool :
  ∀ {Δ V},
    Value V →
    Δ ⊢ [] ⊢ V ⦂ 𝔹 →
    CanonBool V
  | _, _, .vLam, h => by cases h
  | _, _, .vTrue, .t_true => .isTrue rfl
  | _, _, .vFalse, .t_false => .isFalse rfl
  | _, _, .vZero, h => by cases h
  | _, _, .vSuc _, h => by cases h
  | _, _, .vTlam, h => by cases h

def canonical_nat :
  ∀ {Δ V},
    Value V →
    Δ ⊢ [] ⊢ V ⦂ ℕ →
    CanonNat V
  | _, _, .vLam, h => by cases h
  | _, _, .vTrue, h => by cases h
  | _, _, .vFalse, h => by cases h
  | _, _, .vZero, .t_zero => .isZero rfl
  | _, _, .vSuc vW, .t_suc _ => .isSuc _ rfl vW
  | _, _, .vTlam, h => by cases h

def canonical_all :
  ∀ {Δ V A},
    Value V →
    Δ ⊢ [] ⊢ V ⦂ (∀ₜ A) →
    {N : Term // V = Term.tlam N}
  | _, _, _, .vLam, h => by cases h
  | _, _, _, .vTrue, h => by cases h
  | _, _, _, .vFalse, h => by cases h
  | _, _, _, .vZero, h => by cases h
  | _, _, _, .vSuc _, h => by cases h
  | _, _, _, .vTlam, .t_tlam _ => ⟨_, rfl⟩

def progress :
  ∀ {Δ M A},
    Δ ⊢ [] ⊢ M ⦂ A →
    Progress M
  | _, _, _, .t_var h => by
      cases h
  | _, _, _, .t_lam _ _ => .done .vLam
  | _, _, _, .t_app hL hM => by
      cases progress hL with
      | step sL =>
          exact .step (.xi_app₁ sL)
      | done vL =>
          cases progress hM with
          | step sM =>
              exact .step (.xi_app₂ vL sM)
          | done vM =>
              let hcan := canonical_fn vL hL
              let ⟨A', hLam⟩ := hcan
              let ⟨N, hEq⟩ := hLam
              cases hEq
              exact .step (.beta_lam (A := A') vM)
  | _, _, _, .t_true => .done .vTrue
  | _, _, _, .t_false => .done .vFalse
  | _, _, _, .t_zero => .done .vZero
  | _, _, _, .t_suc hM => by
      cases progress hM with
      | step sM => exact .step (.xi_suc sM)
      | done vM => exact .done (.vSuc vM)
  | _, _, _, .t_case hL hM hN => by
      cases progress hL with
      | step sL =>
          exact .step (.xi_case sL)
      | done vL =>
          cases canonical_nat vL hL with
          | isZero h0 =>
              cases h0
              exact .step .beta_zero
          | isSuc V hEq vV =>
              cases hEq
              exact .step (.beta_suc vV)
  | _, _, _, .t_if hL hM hN => by
      cases progress hL with
      | step sL =>
          exact .step (.xi_if sL)
      | done vL =>
          cases canonical_bool vL hL with
          | isTrue ht =>
              cases ht
              exact .step .beta_true
          | isFalse hf =>
              cases hf
              exact .step .beta_false
  | _, _, _, .t_tlam _ => .done .vTlam
  | _, _, _, .t_tapp hM hB => by
      cases progress hM with
      | step sM =>
          exact .step (.xi_tapp sM)
      | done vM =>
          let hcan := canonical_all vM hM
          let ⟨N, hEq⟩ := hcan
          cases hEq
          exact .step (.beta_tlam (A := _))

end Extrinsic
