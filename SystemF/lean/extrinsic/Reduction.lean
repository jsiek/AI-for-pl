import extrinsic.Terms

namespace Extrinsic

inductive Value : Term → Type where
  | vLam {N} : Value (.lam N)
  | vTrue : Value .ttrue
  | vFalse : Value .tfalse
  | vZero : Value .zero
  | vSuc {V} : Value V → Value (.suc V)
  | vTlam {N} : Value (.tlam N)

inductive Step : Term → Term → Type where
  | xi_app₁ {L L' M} :
      Step L L' →
      Step (.app L M) (.app L' M)
  | xi_app₂ {V M M'} :
      Value V →
      Step M M' →
      Step (.app V M) (.app V M')
  | beta_lam {N W} :
      Value W →
      Step (.app (.lam N) W) (singleSubst N W)
  | xi_suc {M M'} :
      Step M M' →
      Step (.suc M) (.suc M')
  | xi_if {L L' M N} :
      Step L L' →
      Step (.ite L M N) (.ite L' M N)
  | xi_case {L L' M N} :
      Step L L' →
      Step (.natCase L M N) (.natCase L' M N)
  | beta_true {M N} :
      Step (.ite .ttrue M N) M
  | beta_false {M N} :
      Step (.ite .tfalse M N) N
  | beta_zero {M N} :
      Step (.natCase .zero M N) M
  | beta_suc {V M N} :
      Value V →
      Step (.natCase (.suc V) M N) (singleSubst N V)
  | xi_tapp {M M'} :
      Step M M' →
      Step (.tapp M) (.tapp M')
  | beta_tlam {N} :
      Step (.tapp (.tlam N)) N

inductive MultiStep : Term → Term → Type where
  | refl (M) : MultiStep M M
  | step (L) {M N} : Step L M → MultiStep M N → MultiStep L N

infix:50 " —→ " => Step
infix:50 " —↠ " => MultiStep

noncomputable section

def multi_trans {M N L : Term} :
    M —↠ N → N —↠ L → M —↠ L := by
  intro h₁ h₂
  induction h₁ with
  | refl _ => exact h₂
  | step K hK hKN ih => exact .step K hK (ih h₂)

def app_right_multi {V M M' : Term} :
    Value V → M —↠ M' → (.app V M) —↠ (.app V M') := by
  intro vV h
  induction h with
  | refl => exact .refl _
  | step K hK hKN ih => exact .step _ (.xi_app₂ vV hK) ih

def app_multi {L L' M M' : Term} :
    L —↠ L' → Value L' → M —↠ M' → (.app L M) —↠ (.app L' M') := by
  intro hL vL hM
  induction hL generalizing M M' with
  | refl =>
      exact app_right_multi vL hM
  | step K hK hKL ih =>
      exact .step _ (.xi_app₁ hK) (ih (M := M) (M' := M') vL hM)

def suc_multi {M N : Term} :
    M —↠ N → (.suc M) —↠ (.suc N) := by
  intro h
  induction h with
  | refl => exact .refl _
  | step K hK hKN ih => exact .step _ (.xi_suc hK) ih

def case_multi {L L' M N : Term} :
    L —↠ L' → (.natCase L M N) —↠ (.natCase L' M N) := by
  intro h
  induction h with
  | refl => exact .refl _
  | step K hK hKN ih => exact .step _ (.xi_case hK) ih

def if_true_multi_aux {L T M N : Term} :
    L —↠ T → T = .ttrue → (.ite L M N) —↠ M
  | .refl _, hT => by
      cases hT
      exact .step _ .beta_true (.refl _)
  | .step K hK hKT, hT =>
      .step _ (.xi_if hK) (if_true_multi_aux hKT hT)

def if_true_multi {L M N : Term} : L —↠ .ttrue → (.ite L M N) —↠ M := by
  intro h
  exact if_true_multi_aux h rfl

def if_false_multi_aux {L T M N : Term} :
    L —↠ T → T = .tfalse → (.ite L M N) —↠ N
  | .refl _, hT => by
      cases hT
      exact .step _ .beta_false (.refl _)
  | .step K hK hKF, hT =>
      .step _ (.xi_if hK) (if_false_multi_aux hKF hT)

def if_false_multi {L M N : Term} : L —↠ .tfalse → (.ite L M N) —↠ N := by
  intro h
  exact if_false_multi_aux h rfl

def tapp_multi {M M' : Term} :
    M —↠ M' → (.tapp M) —↠ (.tapp M') := by
  intro h
  induction h with
  | refl => exact .refl _
  | step K hK hKN ih => exact .step _ (.xi_tapp hK) ih

def beta_lam_multi {N W : Term} :
    Value W → (.app (.lam N) W) —↠ singleSubst N W := by
  intro vW
  exact .step _ (.beta_lam vW) (.refl _)

def case_zero_multi {M N : Term} :
    (.natCase .zero M N) —↠ M := by
  exact .step _ .beta_zero (.refl _)

def beta_tlam_multi {N : Term} :
    (.tapp (.tlam N)) —↠ N := by
  exact .step _ .beta_tlam (.refl _)

end

end Extrinsic
