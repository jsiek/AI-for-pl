import intrinsic.Terms

namespace Intrinsic

set_option autoImplicit false

inductive Value : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty Δ} → Term Δ Γ A → Type where
  | vZero : {Δ : TyCtx} → {Γ : Ctx Δ} → Value (Term.tzero (Δ := Δ) (Γ := Γ))
  | vSuc : {Δ : TyCtx} → {Γ : Ctx Δ} → {V : Term Δ Γ TNat} →
      Value V → Value (Term.tsuc V)
  | vTrue : {Δ : TyCtx} → {Γ : Ctx Δ} → Value (Term.ttrue (Δ := Δ) (Γ := Γ))
  | vFalse : {Δ : TyCtx} → {Γ : Ctx Δ} → Value (Term.tfalse (Δ := Δ) (Γ := Γ))
  | vLam : {Δ : TyCtx} → {Γ : Ctx Δ} → {A B : Ty Δ} → {N : Term Δ (Γ , A) B} →
      Value (Term.lam A N)
  | vTlam : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty (Δ ,α)} →
      {N : Term (Δ ,α) (liftCtx Γ) A} →
      Value (Term.tlam N)

inductive Step : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty Δ} →
    Term Δ Γ A → Term Δ Γ A → Type where
  | xiSuc : {Δ : TyCtx} → {Γ : Ctx Δ} → {M M' : Term Δ Γ TNat} →
      Step M M' → Step (Term.tsuc M) (Term.tsuc M')
  | xiCaseNat : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty Δ} →
      {L L' : Term Δ Γ TNat} → {M : Term Δ Γ A} → {N : Term Δ (Γ , TNat) A} →
      Step L L' → Step (Term.tcaseNat L M N) (Term.tcaseNat L' M N)
  | xiIf : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty Δ} →
      {L L' : Term Δ Γ TBool} → {M N : Term Δ Γ A} →
      Step L L' → Step (Term.tite L M N) (Term.tite L' M N)
  | xiApp1 : {Δ : TyCtx} → {Γ : Ctx Δ} → {A B : Ty Δ} →
      {L L' : Term Δ Γ (A ⇒ B)} → {M : Term Δ Γ A} →
      Step L L' → Step (Term.app L M) (Term.app L' M)
  | xiApp2 : {Δ : TyCtx} → {Γ : Ctx Δ} → {A B : Ty Δ} →
      {V : Term Δ Γ (A ⇒ B)} → {M M' : Term Δ Γ A} →
      Value V → Step M M' → Step (Term.app V M) (Term.app V M')
  | xiTapp : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty (Δ ,α)} →
      {M M' : Term Δ Γ (∀ₜ A)} → {B : Ty Δ} →
      Step M M' → Step (Term.tapp M B) (Term.tapp M' B)
  | betaLam : {Δ : TyCtx} → {Γ : Ctx Δ} → {A B : Ty Δ} →
      {N : Term Δ (Γ , A) B} → {W : Term Δ Γ A} →
      Value W → Step (Term.app (Term.lam A N) W) (singleSubst N W)
  | betaZero : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty Δ} →
      {M : Term Δ Γ A} → {N : Term Δ (Γ , TNat) A} →
      Step (Term.tcaseNat (Term.tzero (Δ := Δ) (Γ := Γ)) M N) M
  | betaSuc : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty Δ} →
      {V : Term Δ Γ TNat} → {M : Term Δ Γ A} → {N : Term Δ (Γ , TNat) A} →
      Value V → Step (Term.tcaseNat (Term.tsuc V) M N) (singleSubst N V)
  | betaTrue : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty Δ} →
      {M N : Term Δ Γ A} →
      Step (Term.tite (Term.ttrue (Δ := Δ) (Γ := Γ)) M N) M
  | betaFalse : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty Δ} →
      {M N : Term Δ Γ A} →
      Step (Term.tite (Term.tfalse (Δ := Δ) (Γ := Γ)) M N) N
  | betaTlam : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty (Δ ,α)} →
      {N : Term (Δ ,α) (liftCtx Γ) A} → {B : Ty Δ} →
      Step (Term.tapp (Term.tlam N) B) (instT N B)

infix:50 " —→ " => Step

inductive Progress : {A : Ty ∅} → Closed A → Type where
  | step : {A : Ty ∅} → {M N : Closed A} → Step M N → Progress M
  | done : {A : Ty ∅} → {M : Closed A} → Value M → Progress M

open Progress

def progress {A : Ty ∅} (M : Closed A) : Progress M :=
  match M with
  | Term.tzero => done Value.vZero
  | Term.ttrue => done Value.vTrue
  | Term.tfalse => done Value.vFalse
  | Term.tsuc N =>
      match progress N with
      | step sN => step (Step.xiSuc sN)
      | done vN => done (Value.vSuc vN)
  | @Term.tcaseNat _ _ A L M N =>
      match progress L with
      | step sL => step (Step.xiCaseNat (A := A) sL)
      | done vL =>
          match vL with
          | Value.vZero => step (Step.betaZero (A := A))
          | Value.vSuc v => step (Step.betaSuc (A := A) v)
  | @Term.tite _ _ A L M N =>
      match progress L with
      | step sL => step (Step.xiIf (A := A) sL)
      | done vL =>
          match vL with
          | Value.vTrue => step (Step.betaTrue (A := A))
          | Value.vFalse => step (Step.betaFalse (A := A))
  | Term.var x => nomatch x
  | @Term.lam _ _ A B N =>
      done Value.vLam
  | @Term.app _ _ A B L M =>
      match progress L with
      | step sL => step (Step.xiApp1 (A := A) (B := B) sL)
      | done vL =>
          match progress M with
          | step sM => step (Step.xiApp2 (A := A) (B := B) vL sM)
          | done vM =>
              match vL with
              | Value.vLam => step (Step.betaLam (A := A) (B := B) vM)
  | @Term.tlam _ _ A N =>
      done Value.vTlam
  | @Term.tapp _ _ A N B =>
      match progress N with
      | step sN => step (Step.xiTapp (A := A) (B := B) sN)
      | done vN =>
          match vN with
          | Value.vTlam => step (Step.betaTlam (A := A) (B := B))

inductive MultiStep : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty Δ} →
    Term Δ Γ A → Term Δ Γ A → Type where
  | refl : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty Δ} → (M : Term Δ Γ A) → MultiStep M M
  | step : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty Δ} →
      (L : Term Δ Γ A) → {M N : Term Δ Γ A} →
      Step L M → MultiStep M N → MultiStep L N

infix:50 " —↠ " => MultiStep

postfix:max " ∎" => MultiStep.refl
notation:2 L " —→⟨ " s " ⟩ " ms => MultiStep.step L s ms
notation:1 "begin " ms => ms

noncomputable def multiTrans {Δ : TyCtx} {Γ : Ctx Δ} {A : Ty Δ} {L M N : Term Δ Γ A} :
    MultiStep L M → MultiStep M N → MultiStep L N := by
  intro h₁ h₂
  induction h₁ with
  | refl _ =>
      exact h₂
  | step L s hLM ih =>
      exact MultiStep.step L s (ih h₂)

end Intrinsic
