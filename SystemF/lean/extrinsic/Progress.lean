import extrinsic.Reduction

namespace Extrinsic

inductive Progress (M : Term) : Type where
  | done : Value M → Progress M
  | step : ∀ {N}, M —→ N → Progress M

inductive CanonBool (V : Term) : Type where
  | isTrue : V = .ttrue → CanonBool V
  | isFalse : V = .tfalse → CanonBool V

inductive CanonNat (V : Term) : Type where
  | isZero : V = .zero → CanonNat V
  | isSuc : (W : Term) → V = .suc W → Value W → CanonNat V

def canonical_fn :
  ∀ {Δ V A B},
    Value V →
    HasType Δ [] V (.fn A B) →
    {N : Term // V = .lam N}
  | _, _, _, _, .vLam, .t_lam _ _ => ⟨_, rfl⟩
  | _, _, _, _, .vTrue, h => by cases h
  | _, _, _, _, .vFalse, h => by cases h
  | _, _, _, _, .vZero, h => by cases h
  | _, _, _, _, .vSuc _, h => by cases h
  | _, _, _, _, .vTlam, h => by cases h

def canonical_bool :
  ∀ {Δ V},
    Value V →
    HasType Δ [] V .bool →
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
    HasType Δ [] V .nat →
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
    HasType Δ [] V (.all A) →
    {N : Term // V = .tlam N}
  | _, _, _, .vLam, h => by cases h
  | _, _, _, .vTrue, h => by cases h
  | _, _, _, .vFalse, h => by cases h
  | _, _, _, .vZero, h => by cases h
  | _, _, _, .vSuc _, h => by cases h
  | _, _, _, .vTlam, .t_tlam _ => ⟨_, rfl⟩

def progress :
  ∀ {Δ M A},
    HasType Δ [] M A →
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
              let ⟨N, hEq⟩ := hcan
              cases hEq
              exact .step (.beta_lam vM)
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
          exact .step .beta_tlam

end Extrinsic
