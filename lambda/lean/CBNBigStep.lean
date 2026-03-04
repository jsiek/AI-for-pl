import Lambda
import CBNReduction

namespace CBNBigStep

open Lambda

/-- Big-step (natural semantics) evaluation with call-by-name strategy. -/
inductive Eval : Term → Term → Type where
  | var : ∀ {i}, Eval (.var i) (.var i)
  | lam : ∀ {N}, Eval (.lam N) (.lam N)
  | app : ∀ {L M N V},
      Eval L (.lam N) →
      Eval (single_subst N M) V →
      Eval (.app L M) V

infix:20 " ⇓ " => Eval

def eval_to_multistep {M N : Term} : Eval M N → CbnMultiStep M N
  | .var => .refl _
  | .lam => .refl _
  | .app (L := L) (M := M) (N := N) (V := V) hL hBody =>
      let hsL : CbnMultiStep (.app L M) (.app (.lam N) M) := cbn_appL_cong (eval_to_multistep hL)
      let hsBeta : CbnMultiStep (.app (.lam N) M) (single_subst N M) :=
        .step _ .β_lam (.refl _)
      cbn_multi_trans hsL (cbn_multi_trans hsBeta (eval_to_multistep hBody))

/-- If `M` takes one call-by-name step to `N`, and `N` evaluates to value `V`,
then `M` also evaluates to `V`. -/
def cbn_step_bigstep_value {M N V : Term} :
  CbnStep M N → Eval N V → Value V → Eval M V
  | .xi_app1 s, .app hL hBody, _ =>
      .app (cbn_step_bigstep_value s hL .lam) hBody
  | .β_lam, hEval, _ =>
      .app .lam hEval

def eval_value {M V : Term} : Eval M V → Value V
  | .var => .var
  | .lam => .lam
  | .app _ hBody => eval_value hBody

def value_eval {V : Term} : Value V → Eval V V
  | .var => .var
  | .lam => .lam

def cbn_multistep_bigstep {M N V : Term} :
  CbnMultiStep M N → Eval N V → Eval M V
  | .refl _, hEval => hEval
  | .step _ s ms, hEval =>
      let hMid : Eval _ V := cbn_multistep_bigstep ms hEval
      cbn_step_bigstep_value s hMid (eval_value hMid)

def cbn_multistep_to_value_bigstep {M V : Term} :
  CbnMultiStep M V → Value V → Eval M V
  | hSteps, hVal => cbn_multistep_bigstep hSteps (value_eval hVal)

end CBNBigStep
