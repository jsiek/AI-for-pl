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
  (Env∼; idᶜ; instᵐ; genᵐ; _⊢_∼_; _∼_; id; _!; ？_; _↦_;
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
import proof.DGG.Examples as Ex
import proof.DGG.ReachabilityCatalog as RC
import proof.DGG.ReachabilityScreen as RS
import InitialPairScratch as IP

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

gen-★?X : ∀ {Δ} {μ : Env∼ Δ}
  → genᵐ μ ⊢ ★ ∼ ＇ Fin.zero
gen-★?X =
  ？_ ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ ★∼G = ★∼Xᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Bns = nonstar-X ⦄

∀X⇒X∼∀X⇒X : ∀ {Δ} → ∀X⇒X {Δ} ∼ ∀X⇒X {Δ}
∀X⇒X∼∀X⇒X = ∀ᶜ (id (＇ Fin.zero) ↦ id (＇ Fin.zero))

∀X⇒X∼★⇒★ : ∀ {Δ} → ∀X⇒X {Δ} ∼ ★⇒★ᵗ {Δ}
∀X⇒X∼★⇒★ =
  inst_ ⦃ Anv = nonvar-fun ⦄ ⦃ z∈A = X∈X⇒X ⦄
    (inst-X! ↦ inst-X!) (λ ())

★⇒★∼∀X⇒X : ∀ {Δ} → ★⇒★ᵗ {Δ} ∼ ∀X⇒X {Δ}
★⇒★∼∀X⇒X =
  gen_ ⦃ Bnv = nonvar-fun ⦄ ⦃ z∈B = X∈X⇒X ⦄
    (gen-★?X ↦ gen-★?X) (λ ())

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

P-step₀ : Ex.OneStep store-empty Pᶜ
P-step₀ = Ex.from-just-step (step? store-empty Pᶜ) refl

P₁ : Term (Ex.OneStep.Δ′ P-step₀)
P₁ = Ex.OneStep.next P-step₀

P-step₀-change : Ex.OneStep.change P-step₀ ≡ keep
P-step₀-change = refl

P-store₁ = Ex.store-after P-step₀

P-step₁ : Ex.OneStep P-store₁ P₁
P-step₁ = Ex.from-just-step (step? P-store₁ P₁) refl

P₂ : Term (Ex.OneStep.Δ′ P-step₁)
P₂ = Ex.OneStep.next P-step₁

P-store₂ = Ex.store-after P-step₁

P-step₂ : Ex.OneStep P-store₂ P₂
P-step₂ = Ex.from-just-step (step? P-store₂ P₂) refl

P₃ : Term (Ex.OneStep.Δ′ P-step₂)
P₃ = Ex.OneStep.next P-step₂

P-store₃ = Ex.store-after P-step₂

P-step₃ : Ex.OneStep P-store₃ P₃
P-step₃ = Ex.from-just-step (step? P-store₃ P₃) refl

P₄ : Term (Ex.OneStep.Δ′ P-step₃)
P₄ = Ex.OneStep.next P-step₃

P-store₄ = Ex.store-after P-step₃

P-step₄ : Ex.OneStep P-store₄ P₄
P-step₄ = Ex.from-just-step (step? P-store₄ P₄) refl

P₅ : Term (Ex.OneStep.Δ′ P-step₄)
P₅ = Ex.OneStep.next P-step₄

P-store₅ = Ex.store-after P-step₄

P-step₅ : Ex.OneStep P-store₅ P₅
P-step₅ = Ex.from-just-step (step? P-store₅ P₅) refl

P₆ : Term (Ex.OneStep.Δ′ P-step₅)
P₆ = Ex.OneStep.next P-step₅

P-store₆ = Ex.store-after P-step₅

P-step₆ : Ex.OneStep P-store₆ P₆
P-step₆ = Ex.from-just-step (step? P-store₆ P₆) refl

P₇ : Term (Ex.OneStep.Δ′ P-step₆)
P₇ = Ex.OneStep.next P-step₆

P-store₇ = Ex.store-after P-step₆

P-step₇ : Ex.OneStep P-store₇ P₇
P-step₇ = Ex.from-just-step (step? P-store₇ P₇) refl

P₈ : Term (Ex.OneStep.Δ′ P-step₇)
P₈ = Ex.OneStep.next P-step₇

P-store₈ = Ex.store-after P-step₇

P-step₈ : Ex.OneStep P-store₈ P₈
P-step₈ = Ex.from-just-step (step? P-store₈ P₈) refl

P₉ : Term (Ex.OneStep.Δ′ P-step₈)
P₉ = Ex.OneStep.next P-step₈

P-store₉ = Ex.store-after P-step₈

P-step₉ : Ex.OneStep P-store₉ P₉
P-step₉ = Ex.from-just-step (step? P-store₉ P₉) refl

P₁₀ : Term (Ex.OneStep.Δ′ P-step₉)
P₁₀ = Ex.OneStep.next P-step₉

P-store₁₀ = Ex.store-after P-step₉

P-step₁₀ : Ex.OneStep P-store₁₀ P₁₀
P-step₁₀ = Ex.from-just-step (step? P-store₁₀ P₁₀) refl

P₁₁ : Term (Ex.OneStep.Δ′ P-step₁₀)
P₁₁ = Ex.OneStep.next P-step₁₀

P-store₁₁ = Ex.store-after P-step₁₀

P-step₁₁ : Ex.OneStep P-store₁₁ P₁₁
P-step₁₁ = Ex.from-just-step (step? P-store₁₁ P₁₁) refl

P₁₂ : Term (Ex.OneStep.Δ′ P-step₁₁)
P₁₂ = Ex.OneStep.next P-step₁₁

P-store₁₂ = Ex.store-after P-step₁₁

P-step₁₂ : Ex.OneStep P-store₁₂ P₁₂
P-step₁₂ = Ex.from-just-step (step? P-store₁₂ P₁₂) refl

P₁₃ : Term (Ex.OneStep.Δ′ P-step₁₂)
P₁₃ = Ex.OneStep.next P-step₁₂

P-store₁₃ = Ex.store-after P-step₁₂

P-step₁₃ : Ex.OneStep P-store₁₃ P₁₃
P-step₁₃ = Ex.from-just-step (step? P-store₁₃ P₁₃) refl

P₁₄ : Term (Ex.OneStep.Δ′ P-step₁₃)
P₁₄ = Ex.OneStep.next P-step₁₃

P-store₁₄ = Ex.store-after P-step₁₃

P₁₄-no-step : Ex.hasStep? (step? P-store₁₄ P₁₄) ≡ false
P₁₄-no-step = refl

P₁₄-tagged-zero-skeleton-gate :
  RC.skeleton P₁₄ ≡
  RC.skeleton (IP.taggedZeroᶜ {Δ = Ex.OneStep.Δ′ P-step₁₃})
P₁₄-tagged-zero-skeleton-gate = refl

P₁₄-not-two-seal-skeleton :
  RC.skeleton P₁₄ ≢ RC.skeleton IP.P-two-seal-result-context
P₁₄-not-two-seal-skeleton ()

initialpair-P-two-seal-state-gate : IP.P₇ ≡ IP.P-two-seal-result-context
initialpair-P-two-seal-state-gate = IP.P₇-two-seal-state-gate

Q-step₀ : Ex.OneStep store-empty Qᶜ
Q-step₀ = Ex.from-just-step (step? store-empty Qᶜ) refl

Q₁ : Term (Ex.OneStep.Δ′ Q-step₀)
Q₁ = Ex.OneStep.next Q-step₀

Q-step₀-change : Ex.OneStep.change Q-step₀ ≡ keep
Q-step₀-change = refl

Q₁-initialpair-gate : Q₁ ≡ IP.Qᶜ
Q₁-initialpair-gate = refl

Q₁-initialpair-skeleton-gate : RC.skeleton Q₁ ≡ RC.skeleton IP.Qᶜ
Q₁-initialpair-skeleton-gate = refl

Q₁-tagged-seal-gate :
  IP.Q₆ ≡ (IP.Q-generated-tagged-input ⟨ IP.X? ⟩)
    ↑ Conv.unseal Fin.zero ★
Q₁-tagged-seal-gate = IP.Q₆-generated-tagged-input-gate
