import extrinsic.Terms

namespace Extrinsic

inductive Value : Term → Type where
  | vLam {A : Ty} {N : Term} : Value (Term.lam A N)
  | vTrue : Value Term.ttrue
  | vFalse : Value Term.tfalse
  | vZero : Value Term.zero
  | vSuc {V : Term} : Value V → Value (Term.suc V)
  | vTlam {N : Term} : Value (Term.tlam N)

inductive Step : Term → Term → Type where
  | xi_app₁ {L L' M : Term} :
      Step L L' →
      Step (Term.app L M) (Term.app L' M)
  | xi_app₂ {V M M' : Term} :
      Value V →
      Step M M' →
      Step (Term.app V M) (Term.app V M')
  | beta_lam {A : Ty} {N W : Term} :
      Value W →
      Step (Term.app (Term.lam A N) W) (singleSubst N W)
  | xi_suc {M M' : Term} :
      Step M M' →
      Step (Term.suc M) (Term.suc M')
  | xi_if {L L' M N : Term} :
      Step L L' →
      Step (Term.ite L M N) (Term.ite L' M N)
  | xi_case {L L' M N : Term} :
      Step L L' →
      Step (Term.natCase L M N) (Term.natCase L' M N)
  | beta_true {M N : Term} :
      Step (Term.ite Term.ttrue M N) M
  | beta_false {M N : Term} :
      Step (Term.ite Term.tfalse M N) N
  | beta_zero {M N : Term} :
      Step (Term.natCase Term.zero M N) M
  | beta_suc {V M N : Term} :
      Value V →
      Step (Term.natCase (Term.suc V) M N) (singleSubst N V)
  | xi_tapp {M M' : Term} {A : Ty} :
      Step M M' →
      Step (Term.tapp M A) (Term.tapp M' A)
  | beta_tlam {N : Term} {A : Ty} :
      Step (Term.tapp (Term.tlam N) A) (substOneTT N A)

inductive MultiStep : Term → Term → Type where
  | refl (M : Term) : MultiStep M M
  | step (L : Term) {M N : Term} : Step L M → MultiStep M N → MultiStep L N

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
    Value V → M —↠ M' → (Term.app V M) —↠ (Term.app V M') := by
  intro vV h
  induction h with
  | refl => exact .refl _
  | step K hK hKN ih => exact .step _ (.xi_app₂ vV hK) ih

def app_multi {L L' M M' : Term} :
    L —↠ L' → Value L' → M —↠ M' → (Term.app L M) —↠ (Term.app L' M') := by
  intro hL vL hM
  induction hL generalizing M M' with
  | refl =>
      exact app_right_multi vL hM
  | step K hK hKL ih =>
      exact .step _ (.xi_app₁ hK) (ih (M := M) (M' := M') vL hM)

def suc_multi {M N : Term} :
    M —↠ N → (Term.suc M) —↠ (Term.suc N) := by
  intro h
  induction h with
  | refl => exact .refl _
  | step K hK hKN ih => exact .step _ (.xi_suc hK) ih

def case_multi {L L' M N : Term} :
    L —↠ L' → (Term.natCase L M N) —↠ (Term.natCase L' M N) := by
  intro h
  induction h with
  | refl => exact .refl _
  | step K hK hKN ih => exact .step _ (.xi_case hK) ih

def if_true_multi_aux {L T M N : Term} :
    L —↠ T → T = Term.ttrue → (Term.ite L M N) —↠ M
  | .refl _, hT => by
      cases hT
      exact .step _ .beta_true (.refl _)
  | .step K hK hKT, hT =>
      .step _ (.xi_if hK) (if_true_multi_aux hKT hT)

def if_true_multi {L M N : Term} : L —↠ Term.ttrue → (Term.ite L M N) —↠ M := by
  intro h
  exact if_true_multi_aux h rfl

def if_false_multi_aux {L T M N : Term} :
    L —↠ T → T = Term.tfalse → (Term.ite L M N) —↠ N
  | .refl _, hT => by
      cases hT
      exact .step _ .beta_false (.refl _)
  | .step K hK hKF, hT =>
      .step _ (.xi_if hK) (if_false_multi_aux hKF hT)

def if_false_multi {L M N : Term} : L —↠ Term.tfalse → (Term.ite L M N) —↠ N := by
  intro h
  exact if_false_multi_aux h rfl

def tapp_multi {M M' : Term} {A : Ty} :
    M —↠ M' → (Term.tapp M A) —↠ (Term.tapp M' A) := by
  intro h
  induction h with
  | refl => exact .refl _
  | step K hK hKN ih => exact .step _ (.xi_tapp hK) ih

def beta_lam_multi {A : Ty} {N W : Term} :
    Value W → (Term.app (Term.lam A N) W) —↠ singleSubst N W := by
  intro vW
  exact .step _ (.beta_lam vW) (.refl _)

def case_zero_multi {M N : Term} :
    (Term.natCase Term.zero M N) —↠ M := by
  exact .step _ .beta_zero (.refl _)

def beta_tlam_multi {N : Term} {A : Ty} :
    (Term.tapp (Term.tlam N) A) —↠ substOneTT N A := by
  exact .step _ .beta_tlam (.refl _)

end

end Extrinsic
