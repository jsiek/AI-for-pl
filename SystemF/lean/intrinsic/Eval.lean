import intrinsic.Reduction

namespace Intrinsic

set_option autoImplicit false

structure EvalResult {A : Ty ∅} (M : Closed A) : Type where
  term : Closed A
  trace : M —↠ term
  value : Value term

def varIndex {Δ : TyCtx} {Γ : Ctx Δ} {A : Ty Δ} : HasVar Γ A → Nat
  | HasVar.Z => 0
  | HasVar.S x => varIndex x + 1

def renderTy {Δ : TyCtx} (A : Ty Δ) : String :=
  reprStr A

def renderTerm {Δ : TyCtx} {Γ : Ctx Δ} {A : Ty Δ} : Term Δ Γ A → String
  | Term.ttrue => "true"
  | Term.tfalse => "false"
  | Term.tzero => "0"
  | Term.tsuc N => "(suc " ++ renderTerm N ++ ")"
  | Term.tcaseNat L M N =>
      "(case " ++ renderTerm L ++ " of 0 => " ++ renderTerm M ++ " | suc => " ++ renderTerm N ++ ")"
  | Term.tite L M N =>
      "(if " ++ renderTerm L ++ " then " ++ renderTerm M ++ " else " ++ renderTerm N ++ ")"
  | Term.var x => "x" ++ toString (varIndex x)
  | Term.lam B N => "(lam :" ++ renderTy B ++ ". " ++ renderTerm N ++ ")"
  | Term.app L M => "(" ++ renderTerm L ++ " " ++ renderTerm M ++ ")"
  | Term.tlam N => "(tlam. " ++ renderTerm N ++ ")"
  | Term.tapp N B => "(" ++ renderTerm N ++ " [" ++ renderTy B ++ "])"

def renderValue {Δ : TyCtx} {Γ : Ctx Δ} {A : Ty Δ} {M : Term Δ Γ A} : Value M → String
  | Value.vZero => "vZero"
  | Value.vSuc v => "vSuc(" ++ renderValue v ++ ")"
  | Value.vTrue => "vTrue"
  | Value.vFalse => "vFalse"
  | Value.vLam => "vLam"
  | Value.vTlam => "vTlam"

def traceLength {Δ : TyCtx} {Γ : Ctx Δ} {A : Ty Δ}
    {M N : Term Δ Γ A} : M —↠ N → Nat
  | MultiStep.refl _ => 0
  | MultiStep.step _ _ ms => traceLength ms + 1

structure EvalSnapshot : Type where
  term : String
  steps : Nat
  value : String
  deriving Repr

def snapshotOf {A : Ty ∅} {M : Closed A} (r : EvalResult M) : EvalSnapshot :=
  { term := renderTerm r.term
    steps := traceLength r.trace
    value := renderValue r.value }

def eval {A : Ty ∅} (fuel : Nat) (M : Closed A) : Option (EvalResult M) :=
  match fuel with
  | 0 =>
      match progress M with
      | Progress.done v => some (EvalResult.mk M (MultiStep.refl M) v)
      | Progress.step _ => none
  | fuel + 1 =>
      match progress M with
      | Progress.done v => some (EvalResult.mk M (MultiStep.refl M) v)
      | Progress.step (N := N) s =>
          match eval fuel N with
          | none => none
          | some r =>
              some (EvalResult.mk r.term (MultiStep.step M s r.trace) r.value)

def evalView? {A : Ty ∅} (fuel : Nat) (M : Closed A) : Option EvalSnapshot :=
  (eval fuel M).map snapshotOf

def evalView {A : Ty ∅} (fuel : Nat) (M : Closed A) : String :=
  match evalView? fuel M with
  | none => s!"none (fuel exhausted at {fuel})"
  | some snap => s!"some {reprStr snap}"

end Intrinsic
