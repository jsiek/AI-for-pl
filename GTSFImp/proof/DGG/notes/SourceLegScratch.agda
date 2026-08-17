module SourceLegScratch where

-- Root-only scratch for the SOURCE-LEG addendum.
-- It records the literal gradual source pair, their source typings, the
-- source-term imprecision derivation, and executable compile/trace gates back
-- to the existing InitialPairScratch runtime checkpoints.

open import Data.Bool using (false)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (proj₁)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TermCtx using (Z; S)
open import TyStore using (store-empty)
open import Consistency using
  (Env∼; idᶜ; instᵐ; genᵐ; flipᵐ; _⊢_∼_; _∼_; id; _!;
   ？_; _↦_;
   ∀ᶜ_; inst_; gen_; X∼★ᵍ; ★∼Xᵍ)
import Imprecision as I
import GradualTerms as G
open import GradualTerms
  using ()
  renaming (_∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_)
import GradualTermImprecision as GTI
import Conversion as Conv
import Primitives
open import Compile using (compile)
open import CastTerms using (Term; _⟨_⟩; _↑_)
open import Eval using (step?)
open import Reduction using (keep; bind)
import proof.DGG.ExampleTerms as Ex
import proof.DGG.OneStep as Step
import proof.DGG.ReachabilityCatalog as RC
import proof.DGG.ReachabilityScreen as RS
import proof.DGG.notes.InitialPairScratch as IP

------------------------------------------------------------------------
-- Source types and consistencies
------------------------------------------------------------------------

ℕ₀ : Ty 0
ℕ₀ = ‵ `ℕ

X⇒X : ∀ {Δ} → Ty (suc Δ)
X⇒X = ＇ Fin.zero ⇒ ＇ Fin.zero

∀X⇒X : ∀ {Δ} → Ty Δ
∀X⇒X = `∀ X⇒X

★⇒★ᵗ : ∀ {Δ} → Ty Δ
★⇒★ᵗ = ★ ⇒ ★

X∈X⇒X : ∀ {Δ} → Fin.zero ∈ᵗ X⇒X {Δ}
X∈X⇒X = ∈-fun-left var-∈

★∼ℕ : ★ ∼ ℕ₀
★∼ℕ = ？ (id (‵ `ℕ))

★∼★ : ∀ {Δ} → ★ ∼ ★
★∼★ {Δ = Δ} = id {μ = idᶜ {Δ = Δ}} ★

X∼X : ∀ {Δ} → idᶜ {Δ = suc Δ} ⊢ ＇ Fin.zero ∼ ＇ Fin.zero
X∼X = id (＇ Fin.zero)

inst-X! : ∀ {Δ} {μ : Env∼ Δ}
  → instᵐ μ ⊢ ＇ Fin.zero ∼ ★
inst-X! =
  _! ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ G∼★ = X∼★ᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Ans = nonstar-X ⦄

flip-inst-★?X : ∀ {Δ} {μ : Env∼ Δ}
  → flipᵐ (instᵐ μ) ⊢ ★ ∼ ＇ Fin.zero
flip-inst-★?X =
  ？_ ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ ★∼G = ★∼Xᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Bns = nonstar-X ⦄

gen-★?X : ∀ {Δ} {μ : Env∼ Δ}
  → genᵐ μ ⊢ ★ ∼ ＇ Fin.zero
gen-★?X =
  ？_ ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ ★∼G = ★∼Xᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Bns = nonstar-X ⦄

flip-gen-X! : ∀ {Δ} {μ : Env∼ Δ}
  → flipᵐ (genᵐ μ) ⊢ ＇ Fin.zero ∼ ★
flip-gen-X! =
  _! ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ G∼★ = X∼★ᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Ans = nonstar-X ⦄

∀X⇒X∼∀X⇒X : ∀ {Δ} → ∀X⇒X {Δ} ∼ ∀X⇒X {Δ}
∀X⇒X∼∀X⇒X = ∀ᶜ (id (＇ Fin.zero) ↦ id (＇ Fin.zero))

∀X⇒X∼★⇒★ : ∀ {Δ} → ∀X⇒X {Δ} ∼ ★⇒★ᵗ {Δ}
∀X⇒X∼★⇒★ =
  inst_ ⦃ Anv = nonvar-fun ⦄ ⦃ z∈A = X∈X⇒X ⦄
    (flip-inst-★?X ↦ inst-X!) (λ ())

★⇒★∼∀X⇒X : ∀ {Δ} → ★⇒★ᵗ {Δ} ∼ ∀X⇒X {Δ}
★⇒★∼∀X⇒X =
  gen_ ⦃ Bnv = nonvar-fun ⦄ ⦃ z∈B = X∈X⇒X ⦄
    (flip-gen-X! ↦ gen-★?X) (λ ())

------------------------------------------------------------------------
-- Literal source syntax
------------------------------------------------------------------------

ℓ-inner : G.Label
ℓ-inner = 90

ℓ-body : G.Label
ℓ-body = 91

ℓ-outer : G.Label
ℓ-outer = 92

polyIdᴳ : ∀ {Δ} → G.GTerm Δ
polyIdᴳ = G.Λ (G.ƛ ＇ Fin.zero ⇒ G.` 0)

dynIdᴳ : ∀ {Δ} → G.GTerm Δ
dynIdᴳ = G.ƛ ★ ⇒ G.` 0

P-polyᴳ : G.GTerm 0
P-polyᴳ =
  G.Λ
    (G.ƛ ＇ Fin.zero ⇒
      (((G.` 1) G.`[ ＇ Fin.zero ]) G.·[ ℓ-inner ] G.` 0))

P-bodyᴳ : G.GTerm 0
P-bodyᴳ = (P-polyᴳ G.`[ ★ ]) G.·[ ℓ-body ] G.$ (Primitives.κℕ 0)

P-funᴳ : G.GTerm 0
P-funᴳ = G.ƛ ∀X⇒X ⇒ P-bodyᴳ

Pᴳ : G.GTerm 0
Pᴳ = P-funᴳ G.·[ ℓ-outer ] polyIdᴳ

Q-innerᴳ : G.GTerm 0
Q-innerᴳ =
  G.ƛ ★ ⇒ (((G.` 1) G.`[ ★ ]) G.·[ ℓ-inner ] G.` 0)

Q-bodyᴳ : G.GTerm 0
Q-bodyᴳ = Q-innerᴳ G.·[ ℓ-body ] G.$ (Primitives.κℕ 0)

Q-funᴳ : G.GTerm 0
Q-funᴳ = G.ƛ ∀X⇒X ⇒ Q-bodyᴳ

Qᴳ : G.GTerm 0
Qᴳ = Q-funᴳ G.·[ ℓ-outer ] dynIdᴳ

------------------------------------------------------------------------
-- Source typings
------------------------------------------------------------------------

polyId⊢ᴳ : ∀ {Δ Γ} → Δ ∣ Γ ⊢ᴳ polyIdᴳ ⦂ ∀X⇒X
polyId⊢ᴳ =
  G.⊢Λ {zero∈A = X∈X⇒X}
    (G.ƛ ＇ Fin.zero ⇒ G.` 0)
    (G.⊢ƛ (G.⊢` Z))

dynId⊢ᴳ : ∀ {Δ Γ} → Δ ∣ Γ ⊢ᴳ dynIdᴳ ⦂ ★⇒★ᵗ
dynId⊢ᴳ = G.⊢ƛ (G.⊢` Z)

P-inner-app⊢ᴳ :
  1 ∣ ＇ Fin.zero ∷ ∀X⇒X ∷ [] ⊢ᴳ
    (((G.` 1) G.`[ ＇ Fin.zero ]) G.·[ ℓ-inner ] G.` 0)
    ⦂ ＇ Fin.zero
P-inner-app⊢ᴳ =
  G.⊢· (G.⊢• (G.⊢` (S Z))) (G.⊢` Z) X∼X

P-poly⊢ᴳ :
  0 ∣ ∀X⇒X ∷ [] ⊢ᴳ P-polyᴳ ⦂ ∀X⇒X
P-poly⊢ᴳ =
  G.⊢Λ {zero∈A = X∈X⇒X}
    (G.ƛ ＇ Fin.zero ⇒
      (((G.` 1) G.`[ ＇ Fin.zero ]) G.·[ ℓ-inner ] G.` 0))
    (G.⊢ƛ P-inner-app⊢ᴳ)

P-body⊢ᴳ : 0 ∣ ∀X⇒X ∷ [] ⊢ᴳ P-bodyᴳ ⦂ ★
P-body⊢ᴳ =
  G.⊢· (G.⊢• P-poly⊢ᴳ) (G.⊢$ (Primitives.κℕ 0)) ★∼ℕ

P-fun⊢ᴳ : 0 ∣ [] ⊢ᴳ P-funᴳ ⦂ ∀X⇒X ⇒ ★
P-fun⊢ᴳ = G.⊢ƛ P-body⊢ᴳ

P⊢ᴳ : 0 ∣ [] ⊢ᴳ Pᴳ ⦂ ★
P⊢ᴳ = G.⊢· P-fun⊢ᴳ polyId⊢ᴳ ∀X⇒X∼∀X⇒X

Q-inner-app⊢ᴳ :
  0 ∣ ★ ∷ ∀X⇒X ∷ [] ⊢ᴳ
    (((G.` 1) G.`[ ★ ]) G.·[ ℓ-inner ] G.` 0) ⦂ ★
Q-inner-app⊢ᴳ =
  G.⊢· (G.⊢• (G.⊢` (S Z))) (G.⊢` Z) ★∼★

Q-inner⊢ᴳ : 0 ∣ ∀X⇒X ∷ [] ⊢ᴳ Q-innerᴳ ⦂ ★⇒★ᵗ
Q-inner⊢ᴳ = G.⊢ƛ Q-inner-app⊢ᴳ

Q-body⊢ᴳ : 0 ∣ ∀X⇒X ∷ [] ⊢ᴳ Q-bodyᴳ ⦂ ★
Q-body⊢ᴳ =
  G.⊢· Q-inner⊢ᴳ (G.⊢$ (Primitives.κℕ 0)) ★∼ℕ

Q-fun⊢ᴳ : 0 ∣ [] ⊢ᴳ Q-funᴳ ⦂ ∀X⇒X ⇒ ★
Q-fun⊢ᴳ = G.⊢ƛ Q-body⊢ᴳ

Q⊢ᴳ : 0 ∣ [] ⊢ᴳ Qᴳ ⦂ ★
Q⊢ᴳ = G.⊢· Q-fun⊢ᴳ dynId⊢ᴳ ∀X⇒X∼★⇒★

------------------------------------------------------------------------
-- Source imprecision
------------------------------------------------------------------------

∀X⇒X⊑∀X⇒X : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ ∀X⇒X ⊑ ∀X⇒X
∀X⇒X⊑∀X⇒X = I.∀⊑∀ (I.⇒⊑⇒ I.X⊑X I.X⊑X)

∀X⇒X⊑★⇒★ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ ∀X⇒X ⊑ ★⇒★ᵗ
∀X⇒X⊑★⇒★ =
  I.∀⊑ nonvar-fun X∈X⇒X
    (I.⇒⊑⇒ (I.X⊑★ refl) (I.X⊑★ refl))

★⇒★⊑★⇒★ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ ★⇒★ᵗ ⊑ ★⇒★ᵗ
★⇒★⊑★⇒★ = I.⇒⊑⇒ I.★⊑★ I.★⊑★

∀X⇒X⊑∀X⇒X₀ : I.idᵐ {Δ = 0} I.⊢ ∀X⇒X ⊑ ∀X⇒X
∀X⇒X⊑∀X⇒X₀ = ∀X⇒X⊑∀X⇒X

∀X⇒X⊑∀X⇒Xᵢ :
  I.instᵐ (I.idᵐ {Δ = 0}) I.⊢ ∀X⇒X ⊑ ∀X⇒X
∀X⇒X⊑∀X⇒Xᵢ = ∀X⇒X⊑∀X⇒X

∀X⇒X⊑★⇒★₀ : I.idᵐ {Δ = 0} I.⊢ ∀X⇒X ⊑ ★⇒★ᵗ
∀X⇒X⊑★⇒★₀ = ∀X⇒X⊑★⇒★

★⇒★⊑★⇒★₀ : I.idᵐ {Δ = 0} I.⊢ ★⇒★ᵗ ⊑ ★⇒★ᵗ
★⇒★⊑★⇒★₀ = ★⇒★⊑★⇒★

X⊑★₁ : I.instᵐ (I.idᵐ {Δ = 0}) I.⊢ ＇ Fin.zero ⊑ ★
X⊑★₁ = I.X⊑★ refl

X⇒X⊑★⇒★₁ :
  I.instᵐ (I.idᵐ {Δ = 0}) I.⊢ X⇒X ⊑ ★⇒★ᵗ
X⇒X⊑★⇒★₁ = I.⇒⊑⇒ X⊑★₁ X⊑★₁

γ-g : GTI.CtxImp I.idᵐ
γ-g = GTI.ctx-imp ∀X⇒X ∀X⇒X ∀X⇒X⊑∀X⇒X₀ ∷ []

γ-g-inst : GTI.CtxImp (I.instᵐ I.idᵐ)
γ-g-inst = GTI.ctx-imp ∀X⇒X ∀X⇒X ∀X⇒X⊑∀X⇒Xᵢ ∷ []

γ-g-inst-lift : GTI.LiftCtxⁱ (I.instᵐ I.idᵐ) γ-g γ-g-inst
γ-g-inst-lift = GTI.lift-∷ GTI.lift-[]

polyId⊑dynIdᴳ :
  I.idᵐ GTI.∣ [] ⊢ᴳ polyIdᴳ ⊑ dynIdᴳ
    ⦂ ∀X⇒X ⊑ ★⇒★ᵗ ∶ ∀X⇒X⊑★⇒★₀
polyId⊑dynIdᴳ =
  GTI.Λ⊑ᴳ nonvar-fun X∈X⇒X GTI.lift-[]
    (G.ƛ ＇ Fin.zero ⇒ G.` 0)
    (dynId⊢ᴳ {Δ = 0} {Γ = []})
    (GTI.ƛ⊑ƛᴳ (GTI.x⊑xᴳ GTI.Zⁱ))

P-poly-body⊑Q-inner-body :
  I.instᵐ I.idᵐ GTI.∣
    GTI.ctx-imp (＇ Fin.zero) ★ X⊑★₁ ∷ γ-g-inst ⊢ᴳ
    (((G.` 1) G.`[ ＇ Fin.zero ]) G.·[ ℓ-inner ] G.` 0)
    ⊑ (((G.` 1) G.`[ ★ ]) G.·[ ℓ-inner ] G.` 0)
    ⦂ ＇ Fin.zero ⊑ ★ ∶ X⊑★₁
P-poly-body⊑Q-inner-body =
  GTI.·⊑·ᴳ
      (GTI.[]⊑[]ᴳ
        (GTI.x⊑xᴳ (GTI.Sⁱ GTI.Zⁱ))
      X⊑★₁
      X⇒X⊑★⇒★₁)
    (GTI.x⊑xᴳ GTI.Zⁱ)
    (id (＇ Fin.zero))
    (id ★)

P-poly-lam⊑Q-inner-lam :
  I.instᵐ I.idᵐ GTI.∣ γ-g-inst ⊢ᴳ
    (G.ƛ ＇ Fin.zero ⇒
      (((G.` 1) G.`[ ＇ Fin.zero ]) G.·[ ℓ-inner ] G.` 0))
    ⊑ G.renameᵗᴳ Fin.suc Q-innerᴳ
    ⦂ X⇒X ⊑ ★⇒★ᵗ ∶ X⇒X⊑★⇒★₁
P-poly-lam⊑Q-inner-lam =
  GTI.ƛ⊑ƛᴳ P-poly-body⊑Q-inner-body

P-poly⊑Q-inner :
  I.idᵐ GTI.∣ γ-g ⊢ᴳ P-polyᴳ ⊑ Q-innerᴳ
    ⦂ ∀X⇒X ⊑ ★⇒★ᵗ ∶ ∀X⇒X⊑★⇒★₀
P-poly⊑Q-inner =
  GTI.Λ⊑ᴳ nonvar-fun X∈X⇒X γ-g-inst-lift
    (G.ƛ ＇ Fin.zero ⇒
      (((G.` 1) G.`[ ＇ Fin.zero ]) G.·[ ℓ-inner ] G.` 0))
    Q-inner⊢ᴳ
    P-poly-lam⊑Q-inner-lam

P-callee⊑Q-callee :
  I.idᵐ GTI.∣ γ-g ⊢ᴳ (P-polyᴳ G.`[ ★ ]) ⊑ Q-innerᴳ
    ⦂ ★⇒★ᵗ ⊑ ★⇒★ᵗ ∶ ★⇒★⊑★⇒★₀
P-callee⊑Q-callee =
  GTI.[]⊑ᴳ P-poly⊑Q-inner I.★⊑★ ★⇒★⊑★⇒★₀

P-body⊑Q-body :
  I.idᵐ GTI.∣ γ-g ⊢ᴳ P-bodyᴳ ⊑ Q-bodyᴳ
    ⦂ ★ ⊑ ★ ∶ I.★⊑★
P-body⊑Q-body =
  GTI.·⊑·ᴳ P-callee⊑Q-callee
    (GTI.κ⊑κᴳ (Primitives.κℕ 0)) ★∼ℕ ★∼ℕ

P-fun⊑Q-fun :
  I.idᵐ GTI.∣ [] ⊢ᴳ P-funᴳ ⊑ Q-funᴳ
    ⦂ ∀X⇒X ⇒ ★ ⊑ ∀X⇒X ⇒ ★
    ∶ I.⇒⊑⇒ ∀X⇒X⊑∀X⇒X₀ I.★⊑★
P-fun⊑Q-fun = GTI.ƛ⊑ƛᴳ P-body⊑Q-body

P⊑Qᴳ :
  I.idᵐ GTI.∣ [] ⊢ᴳ Pᴳ ⊑ Qᴳ ⦂ ★ ⊑ ★ ∶ I.★⊑★
P⊑Qᴳ =
  GTI.·⊑·ᴳ P-fun⊑Q-fun polyId⊑dynIdᴳ
    ∀X⇒X∼∀X⇒X ∀X⇒X∼★⇒★

P⊑Q-source-typing-gate : GTI.gradual-term-imprecision-source-typing P⊑Qᴳ
  ≡ P⊢ᴳ
P⊑Q-source-typing-gate = refl

P⊑Q-target-typing-gate : GTI.gradual-term-imprecision-target-typing P⊑Qᴳ
  ≡ Q⊢ᴳ
P⊑Q-target-typing-gate = refl

------------------------------------------------------------------------
-- Compilation and executable gates
------------------------------------------------------------------------

Pᶜ : Term 0
Pᶜ = RC.compile-screen P⊢ᴳ

Qᶜ : Term 0
Qᶜ = RC.compile-screen Q⊢ᴳ

Pᶜ-standard : Term 0
Pᶜ-standard = proj₁ (compile {Σ = store-empty} P⊢ᴳ)

Qᶜ-standard : Term 0
Qᶜ-standard = proj₁ (compile {Σ = store-empty} Q⊢ᴳ)

Pᶜ-skeleton-gate : RC.skeleton Pᶜ ≡ RC.skeleton Pᶜ-standard
Pᶜ-skeleton-gate = refl

Qᶜ-skeleton-gate : RC.skeleton Qᶜ ≡ RC.skeleton Qᶜ-standard
Qᶜ-skeleton-gate = refl

P-step₀ : Step.OneStep store-empty Pᶜ
P-step₀ = Step.from-just-step (step? store-empty Pᶜ) refl

P₁ : Term (Step.Δ′ P-step₀)
P₁ = Step.next P-step₀

P-step₀-change : Step.change P-step₀ ≡ keep
P-step₀-change = refl

P-store₁ = Step.store-after P-step₀

P-step₁ : Step.OneStep P-store₁ P₁
P-step₁ = Step.from-just-step (step? P-store₁ P₁) refl

P₂ : Term (Step.Δ′ P-step₁)
P₂ = Step.next P-step₁

P-store₂ = Step.store-after P-step₁

P-step₂ : Step.OneStep P-store₂ P₂
P-step₂ = Step.from-just-step (step? P-store₂ P₂) refl

P₃ : Term (Step.Δ′ P-step₂)
P₃ = Step.next P-step₂

P-store₃ = Step.store-after P-step₂

P-step₃ : Step.OneStep P-store₃ P₃
P-step₃ = Step.from-just-step (step? P-store₃ P₃) refl

P₄ : Term (Step.Δ′ P-step₃)
P₄ = Step.next P-step₃

P-store₄ = Step.store-after P-step₃

P-step₄ : Step.OneStep P-store₄ P₄
P-step₄ = Step.from-just-step (step? P-store₄ P₄) refl

P₅ : Term (Step.Δ′ P-step₄)
P₅ = Step.next P-step₄

P-store₅ = Step.store-after P-step₄

P-step₅ : Step.OneStep P-store₅ P₅
P-step₅ = Step.from-just-step (step? P-store₅ P₅) refl

P₆ : Term (Step.Δ′ P-step₅)
P₆ = Step.next P-step₅

P-store₆ = Step.store-after P-step₅

P-step₆ : Step.OneStep P-store₆ P₆
P-step₆ = Step.from-just-step (step? P-store₆ P₆) refl

P₇ : Term (Step.Δ′ P-step₆)
P₇ = Step.next P-step₆

P-store₇ = Step.store-after P-step₆

P-step₇ : Step.OneStep P-store₇ P₇
P-step₇ = Step.from-just-step (step? P-store₇ P₇) refl

P₈ : Term (Step.Δ′ P-step₇)
P₈ = Step.next P-step₇

P-store₈ = Step.store-after P-step₇

P-step₈ : Step.OneStep P-store₈ P₈
P-step₈ = Step.from-just-step (step? P-store₈ P₈) refl

P₉ : Term (Step.Δ′ P-step₈)
P₉ = Step.next P-step₈

P-store₉ = Step.store-after P-step₈

P-step₉ : Step.OneStep P-store₉ P₉
P-step₉ = Step.from-just-step (step? P-store₉ P₉) refl

P₁₀ : Term (Step.Δ′ P-step₉)
P₁₀ = Step.next P-step₉

P-store₁₀ = Step.store-after P-step₉

P-step₁₀ : Step.OneStep P-store₁₀ P₁₀
P-step₁₀ = Step.from-just-step (step? P-store₁₀ P₁₀) refl

P₁₁ : Term (Step.Δ′ P-step₁₀)
P₁₁ = Step.next P-step₁₀

P-store₁₁ = Step.store-after P-step₁₀

P-step₁₁ : Step.OneStep P-store₁₁ P₁₁
P-step₁₁ = Step.from-just-step (step? P-store₁₁ P₁₁) refl

P₁₂ : Term (Step.Δ′ P-step₁₁)
P₁₂ = Step.next P-step₁₁

P-store₁₂ = Step.store-after P-step₁₁

P-step₁₂ : Step.OneStep P-store₁₂ P₁₂
P-step₁₂ = Step.from-just-step (step? P-store₁₂ P₁₂) refl

P₁₃ : Term (Step.Δ′ P-step₁₂)
P₁₃ = Step.next P-step₁₂

P-store₁₃ = Step.store-after P-step₁₂

P-step₁₃ : Step.OneStep P-store₁₃ P₁₃
P-step₁₃ = Step.from-just-step (step? P-store₁₃ P₁₃) refl

P₁₄ : Term (Step.Δ′ P-step₁₃)
P₁₄ = Step.next P-step₁₃

P-store₁₄ = Step.store-after P-step₁₃

P₁₄-no-step : Step.hasStep? (step? P-store₁₄ P₁₄) ≡ false
P₁₄-no-step = refl

P₁₄-tagged-zero-skeleton-gate :
  RC.skeleton P₁₄ ≡
  RC.skeleton (IP.taggedZeroᶜ {Δ = Step.Δ′ P-step₁₃})
P₁₄-tagged-zero-skeleton-gate = refl

P₁₄-not-two-seal-skeleton :
  RC.skeleton P₁₄ ≢ RC.skeleton IP.P-two-seal-result-context
P₁₄-not-two-seal-skeleton ()

initialpair-P-two-seal-state-gate : IP.P₇ ≡ IP.P-two-seal-result-context
initialpair-P-two-seal-state-gate = IP.P₇-two-seal-state-gate

Q-step₀ : Step.OneStep store-empty Qᶜ
Q-step₀ = Step.from-just-step (step? store-empty Qᶜ) refl

Q₁ : Term (Step.Δ′ Q-step₀)
Q₁ = Step.next Q-step₀

Q-step₀-change : Step.change Q-step₀ ≡ keep
Q-step₀-change = refl

Q₁-initialpair-gate : Q₁ ≡ IP.Qᶜ
Q₁-initialpair-gate = refl

Q₁-initialpair-skeleton-gate : RC.skeleton Q₁ ≡ RC.skeleton IP.Qᶜ
Q₁-initialpair-skeleton-gate = refl

Q₁-tagged-seal-gate :
  IP.Q₆ ≡ (IP.Q-generated-tagged-input ⟨ IP.X? ⟩)
    ↑ Conv.unseal Fin.zero ★
Q₁-tagged-seal-gate = IP.Q₆-generated-tagged-input-gate
