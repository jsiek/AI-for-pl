{-# OPTIONS --safe #-}

module proof.DGG.Examples.MatchedInstantiation where

-- File Charter:
--   * Checks the matched polymorphic-instantiation source pair from Example 4
--     in proof/DGG/Examples/README.md.
--   * Gives source typing and imprecision, ordinary compiler outputs, and one
--     simulation checkpoint after every more-precise reduction.
--   * Records the paired runtime allocation with representations ℕ and ★ and
--     exposes the matched reveal/conceal boundaries used to calibrate world
--     rebasing and representation imprecision.

import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
import Data.Nat as Nat
open import Data.Product using (proj₁; proj₂)
open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TermCtx using (Z)
open import Consistency
open import GradualTerms renaming (_∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_)
import GradualTermImprecision as GTI
import Imprecision as I
open import TyStore using (TyStore; store-empty; store-bind; Z∋)
open import TyStore using (_∋_⦂_)
import Conversion as Conv
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _⊢_⦂_)
import CastTerms as C
open C using (Ctx; _,ˢ_)
open import Compile using (compile)
open import Primitives using (κℕ)
open import Reduction using
  (keep; bind; []; _∷_; _—↠[_]_; _—→[_]⟨_⟩_; _∎[])
open import Eval using (step?; value?)
import Example as Ex
import proof.DGG.OneStep as Step
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.World
open import proof.DGG.ImpLadder using (impLadderDefault)

open GTI using () renaming
  (_∣_⊢ᴳ_⊑_⦂_⊑_∶_ to _∣_⊢ᴳ²_⊑_⦂_⊑_∶_)


------------------------------------------------------------------------
-- Source programs
------------------------------------------------------------------------

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

X⇒X : ∀ {Δ} → Ty (Nat.suc Δ)
X⇒X = ＇ Fin.zero ⇒ ＇ Fin.zero

∀X⇒X : ∀ {Δ} → Ty Δ
∀X⇒X = `∀ X⇒X

X∈X⇒X : ∀ {Δ} → Fin.zero ∈ᵗ X⇒X {Δ}
X∈X⇒X = ∈-fun-left var-∈

ℓ-app : Label
ℓ-app = 0

more-precise : GTerm 0
more-precise =
  ((Λ (ƛ ＇ Fin.zero ⇒ ` 0)) `[ ℕᵗ ]) ·[ ℓ-app ] $ (κℕ 42)

less-precise : GTerm 0
less-precise =
  ((Λ (ƛ ＇ Fin.zero ⇒ ` 0)) `[ ★ ]) ·[ ℓ-app ] $ (κℕ 42)


------------------------------------------------------------------------
-- Source typing and imprecision
------------------------------------------------------------------------

more-precise-⊢ : 0 ∣ [] ⊢ᴳ more-precise ⦂ ℕᵗ
more-precise-⊢ =
  ⊢·
    (⊢•
      (⊢Λ {zero∈A = X∈X⇒X}
        (ƛ ＇ Fin.zero ⇒ ` 0) (⊢ƛ (⊢` Z))))
    (⊢$ (κℕ 42))
    (id (‵ `ℕ))

less-precise-⊢ : 0 ∣ [] ⊢ᴳ less-precise ⦂ ★
less-precise-⊢ =
  ⊢·
    (⊢•
      (⊢Λ {zero∈A = X∈X⇒X}
        (ƛ ＇ Fin.zero ⇒ ` 0) (⊢ƛ (⊢` Z))))
    (⊢$ (κℕ 42))
    (？ (id (‵ `ℕ)))

ℕ⊑★ : ∀ {Δ} {μ : I.ImpEnv Δ} → μ I.⊢ ℕᵗ ⊑ ★
ℕ⊑★ = I.ι⊑★

X⇒X⊑X⇒X : ∀ {Δ} {μ : I.ImpEnv (Nat.suc Δ)}
  → μ I.⊢ X⇒X ⊑ X⇒X
X⇒X⊑X⇒X = I.⇒⊑⇒ I.X⊑X I.X⊑X

∀X⇒X⊑∀X⇒X : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ ∀X⇒X ⊑ ∀X⇒X
∀X⇒X⊑∀X⇒X = I.∀⊑∀ X⇒X⊑X⇒X

ℕ⇒ℕ⊑★⇒★ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ (ℕᵗ ⇒ ℕᵗ) ⊑ (★ ⇒ ★)
ℕ⇒ℕ⊑★⇒★ = I.⇒⊑⇒ ℕ⊑★ ℕ⊑★

source-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ² more-precise ⊑ less-precise
    ⦂ ℕᵗ ⊑ ★ ∶ ℕ⊑★
source-imprecision =
  GTI.·⊑·ᴳ
    {pA = ℕ⊑★} {pB = ℕ⊑★} {pC = I.ι⊑ι}
    (GTI.[]⊑[]ᴳ {p = X⇒X⊑X⇒X}
      (GTI.Λ⊑Λᴳ GTI.lift-[]
        (ƛ ＇ Fin.zero ⇒ ` 0) (ƛ ＇ Fin.zero ⇒ ` 0)
        X∈X⇒X X∈X⇒X
        (GTI.ƛ⊑ƛᴳ {pA = I.X⊑X} {pB = I.X⊑X}
          (GTI.x⊑xᴳ GTI.Zⁱ)))
      ℕ⊑★ ℕ⇒ℕ⊑★⇒★)
    (GTI.κ⊑κᴳ (κℕ 42))
    (id (‵ `ℕ)) (？ (id (‵ `ℕ)))


------------------------------------------------------------------------
-- Ordinary compiler outputs
------------------------------------------------------------------------

more-precise-compiled : Term 0
more-precise-compiled =
  proj₁ (compile {Σ = store-empty} more-precise-⊢)

more-precise-compiled-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ more-precise-compiled ⦂ ℕᵗ
more-precise-compiled-⊢ =
  proj₂ (compile {Σ = store-empty} more-precise-⊢)

less-precise-compiled : Term 0
less-precise-compiled =
  proj₁ (compile {Σ = store-empty} less-precise-⊢)

less-precise-compiled-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ less-precise-compiled ⦂ ★
less-precise-compiled-⊢ =
  proj₂ (compile {Σ = store-empty} less-precise-⊢)

more-precise-eval :
  Ex.evalNat Ex.gas more-precise-compiled-⊢ ≡ just 42
more-precise-eval = refl

-- evalNat recognizes only bare natural constants.  The checked reduction
-- below records the actual dynamic result, 42 tagged by ℕ!.
less-precise-evalNat-observer :
  Ex.evalNat Ex.gas less-precise-compiled-⊢ ≡ Data.Maybe.nothing
less-precise-evalNat-observer = refl


------------------------------------------------------------------------
-- Operational checkpoints
------------------------------------------------------------------------

more-checkpoint₀ : Term 0
more-checkpoint₀ = more-precise-compiled

less-checkpoint₀ : Term 0
less-checkpoint₀ = less-precise-compiled

more-step₀ : Step.OneStep store-empty more-checkpoint₀
more-step₀ = Step.from-just-step (step? store-empty more-checkpoint₀) refl

less-step₀ : Step.OneStep store-empty less-checkpoint₀
less-step₀ = Step.from-just-step (step? store-empty less-checkpoint₀) refl

more-checkpoint₁ : Term (Step.Δ′ more-step₀)
more-checkpoint₁ = Step.next more-step₀

less-checkpoint₁ : Term (Step.Δ′ less-step₀)
less-checkpoint₁ = Step.next less-step₀

more-store₁ : TyStore (Step.Δ′ more-step₀)
more-store₁ = Step.store-after more-step₀

less-store₁ : TyStore (Step.Δ′ less-step₀)
less-store₁ = Step.store-after less-step₀

more-step₁ : Step.OneStep more-store₁ more-checkpoint₁
more-step₁ =
  Step.from-just-step (step? more-store₁ more-checkpoint₁) refl

more-checkpoint₂ : Term (Step.Δ′ more-step₁)
more-checkpoint₂ = Step.next more-step₁

less-checkpoint₂ : Term (Step.Δ′ less-step₀)
less-checkpoint₂ = less-checkpoint₁

more-store₂ : TyStore (Step.Δ′ more-step₁)
more-store₂ = Step.store-after more-step₁

more-step₂ : Step.OneStep more-store₂ more-checkpoint₂
more-step₂ =
  Step.from-just-step (step? more-store₂ more-checkpoint₂) refl

less-step₁ : Step.OneStep less-store₁ less-checkpoint₂
less-step₁ =
  Step.from-just-step (step? less-store₁ less-checkpoint₂) refl

more-checkpoint₃ : Term (Step.Δ′ more-step₂)
more-checkpoint₃ = Step.next more-step₂

less-checkpoint₃ : Term (Step.Δ′ less-step₁)
less-checkpoint₃ = Step.next less-step₁

more-store₃ : TyStore (Step.Δ′ more-step₂)
more-store₃ = Step.store-after more-step₂

less-store₃ : TyStore (Step.Δ′ less-step₁)
less-store₃ = Step.store-after less-step₁

more-step₃ : Step.OneStep more-store₃ more-checkpoint₃
more-step₃ =
  Step.from-just-step (step? more-store₃ more-checkpoint₃) refl

less-step₂ : Step.OneStep less-store₃ less-checkpoint₃
less-step₂ =
  Step.from-just-step (step? less-store₃ less-checkpoint₃) refl

more-checkpoint₄ : Term (Step.Δ′ more-step₃)
more-checkpoint₄ = Step.next more-step₃

less-checkpoint₄ : Term (Step.Δ′ less-step₂)
less-checkpoint₄ = Step.next less-step₂

more-store₄ : TyStore (Step.Δ′ more-step₃)
more-store₄ = Step.store-after more-step₃

less-store₄ : TyStore (Step.Δ′ less-step₂)
less-store₄ = Step.store-after less-step₂

more-step₄ : Step.OneStep more-store₄ more-checkpoint₄
more-step₄ =
  Step.from-just-step (step? more-store₄ more-checkpoint₄) refl

less-step₃ : Step.OneStep less-store₄ less-checkpoint₄
less-step₃ =
  Step.from-just-step (step? less-store₄ less-checkpoint₄) refl

more-checkpoint₅ : Term (Step.Δ′ more-step₄)
more-checkpoint₅ = Step.next more-step₄

less-checkpoint₅ : Term (Step.Δ′ less-step₃)
less-checkpoint₅ = Step.next less-step₃

more-checkpoint₀↠₁ :
  more-checkpoint₀ —↠[ bind (‵ `ℕ) ∷ [] ] more-checkpoint₁
more-checkpoint₀↠₁ =
  more-checkpoint₀
  —→[ bind (‵ `ℕ) ]⟨ Step.reduction more-step₀ ⟩
  more-checkpoint₁ ∎[]

less-checkpoint₀↠₁ :
  less-checkpoint₀ —↠[ bind ★ ∷ [] ] less-checkpoint₁
less-checkpoint₀↠₁ =
  less-checkpoint₀
  —→[ bind ★ ]⟨ Step.reduction less-step₀ ⟩
  less-checkpoint₁ ∎[]

more-checkpoint₁↠₂ :
  more-checkpoint₁ —↠[ keep ∷ [] ] more-checkpoint₂
more-checkpoint₁↠₂ =
  more-checkpoint₁
  —→[ keep ]⟨ Step.reduction more-step₁ ⟩
  more-checkpoint₂ ∎[]

less-checkpoint₁↠₂ : less-checkpoint₁ —↠[ [] ] less-checkpoint₂
less-checkpoint₁↠₂ = less-checkpoint₁ ∎[]

more-checkpoint₂↠₃ :
  more-checkpoint₂ —↠[ keep ∷ [] ] more-checkpoint₃
more-checkpoint₂↠₃ =
  more-checkpoint₂
  —→[ keep ]⟨ Step.reduction more-step₂ ⟩
  more-checkpoint₃ ∎[]

less-checkpoint₂↠₃ :
  less-checkpoint₂ —↠[ keep ∷ [] ] less-checkpoint₃
less-checkpoint₂↠₃ =
  less-checkpoint₂
  —→[ keep ]⟨ Step.reduction less-step₁ ⟩
  less-checkpoint₃ ∎[]

more-checkpoint₃↠₄ :
  more-checkpoint₃ —↠[ keep ∷ [] ] more-checkpoint₄
more-checkpoint₃↠₄ =
  more-checkpoint₃
  —→[ keep ]⟨ Step.reduction more-step₃ ⟩
  more-checkpoint₄ ∎[]

less-checkpoint₃↠₄ :
  less-checkpoint₃ —↠[ keep ∷ [] ] less-checkpoint₄
less-checkpoint₃↠₄ =
  less-checkpoint₃
  —→[ keep ]⟨ Step.reduction less-step₂ ⟩
  less-checkpoint₄ ∎[]

more-checkpoint₄↠₅ :
  more-checkpoint₄ —↠[ keep ∷ [] ] more-checkpoint₅
more-checkpoint₄↠₅ =
  more-checkpoint₄
  —→[ keep ]⟨ Step.reduction more-step₄ ⟩
  more-checkpoint₅ ∎[]

less-checkpoint₄↠₅ :
  less-checkpoint₄ —↠[ keep ∷ [] ] less-checkpoint₅
less-checkpoint₄↠₅ =
  less-checkpoint₄
  —→[ keep ]⟨ Step.reduction less-step₃ ⟩
  less-checkpoint₅ ∎[]

more-checkpoint₅-value : C.Value more-checkpoint₅
more-checkpoint₅-value =
  Step.from-just-value (value? more-checkpoint₅) refl

less-checkpoint₅-value : C.Value less-checkpoint₅
less-checkpoint₅-value =
  Step.from-just-value (value? less-checkpoint₅) refl

more-checkpoint₅-result : more-checkpoint₅ ≡ C.$ (κℕ 42)
more-checkpoint₅-result = refl

less-checkpoint₅-result :
  less-checkpoint₅ ≡ C.$ (κℕ 42) C.⟨ id (‵ `ℕ) ! ⟩
less-checkpoint₅-result = refl


------------------------------------------------------------------------
-- The paired allocation world
------------------------------------------------------------------------

base-context : Ctx
base-context = ⟨ 0 , store-empty , [] ⟩

matched-world :
  (base-context ,ˢ ℕᵗ) ⊑ᶜ (base-context ,ˢ ★)
matched-world = bindBothStarᶜ emptyᶜ ℕ⊑★ (λ ())

source-member : store-bind store-empty ℕᵗ ∋ Fin.zero ⦂ ℕᵗ
source-member = Z∋ refl

target-member : store-bind store-empty ★ ∋ Fin.zero ⦂ ★
target-member = Z∋ refl

source-arrow-reveal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ]
    (Conv.seal Fin.zero ℕᵗ Conv.↦↑ Conv.unseal Fin.zero ℕᵗ)
source-arrow-reveal⊢ =
  Conv.⊢↑-⇒ (Conv.⊢↓-seal source-member)
    (Conv.⊢↑-unseal source-member)

target-arrow-reveal⊢ :
  store-bind store-empty ★ Conv.⊢↑[ Fin.zero ⦂ ★ ]
    (Conv.seal Fin.zero ★ Conv.↦↑ Conv.unseal Fin.zero ★)
target-arrow-reveal⊢ =
  Conv.⊢↑-⇒ (Conv.⊢↓-seal target-member)
    (Conv.⊢↑-unseal target-member)

source-reveal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ]
    Conv.unseal Fin.zero ℕᵗ
source-reveal⊢ = Conv.⊢↑-unseal source-member

target-reveal⊢ :
  store-bind store-empty ★ Conv.⊢↑[ Fin.zero ⦂ ★ ]
    Conv.unseal Fin.zero ★
target-reveal⊢ = Conv.⊢↑-unseal target-member

source-conceal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↓[ Fin.zero ⦂ ℕᵗ ]
    Conv.seal Fin.zero ℕᵗ
source-conceal⊢ = Conv.⊢↓-seal source-member

target-conceal⊢ :
  store-bind store-empty ★ Conv.⊢↓[ Fin.zero ⦂ ★ ]
    Conv.seal Fin.zero ★
target-conceal⊢ = Conv.⊢↓-seal target-member


------------------------------------------------------------------------
-- Cast-term imprecision at every checkpoint
------------------------------------------------------------------------

checkpoint₀-imprecision :
  emptyᶜ CTI.⊢² more-checkpoint₀ ⊑ less-checkpoint₀ ∶ ℕ⊑★
checkpoint₀-imprecision =
  CTI.·⊑·²
    (CTI.•⊑•²
      ∀X⇒X⊑∀X⇒X
      (CTI.Λ⊑Λ²
        (C.ƛ (C.` 0))
        (C.ƛ (C.` 0))
        (CTI.ƛ⊑ƛ² {pA = I.X⊑X} {pB = I.X⊑X}
          (CTI.x⊑x² {p = I.X⊑X} Z Z))
        ∀X⇒X⊑∀X⇒X)
      ℕ⊑★
      ℕ⇒ℕ⊑★⇒★)
    (CTI.cast⊑cast²
      (id (‵ `ℕ))
      (id (‵ `ℕ) !)
      (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
      ℕ⊑★)

checkpoint₀-ladder : String
checkpoint₀-ladder = impLadderDefault checkpoint₀-imprecision

checkpoint₁-imprecision :
  matched-world CTI.⊢² more-checkpoint₁ ⊑ less-checkpoint₁ ∶ ℕ⊑★
checkpoint₁-imprecision =
  CTI.·⊑·²
    (CTI.reveal⊑reveal²
      source-arrow-reveal⊢
      target-arrow-reveal⊢
      refl
      refl
      ℕ⊑★
      (CTI.ƛ⊑ƛ² {pA = I.X⊑X} {pB = I.X⊑X}
        (CTI.x⊑x² {p = I.X⊑X} Z Z))
      ℕ⇒ℕ⊑★⇒★)
    (CTI.cast⊑cast²
      (id (‵ `ℕ))
      (id (‵ `ℕ) !)
      (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
      ℕ⊑★)

checkpoint₁-ladder : String
checkpoint₁-ladder = impLadderDefault checkpoint₁-imprecision

checkpoint₂-imprecision :
  matched-world CTI.⊢² more-checkpoint₂ ⊑ less-checkpoint₂ ∶ ℕ⊑★
checkpoint₂-imprecision =
  CTI.·⊑·²
    (CTI.reveal⊑reveal²
      source-arrow-reveal⊢
      target-arrow-reveal⊢
      refl
      refl
      ℕ⊑★
      (CTI.ƛ⊑ƛ² {pA = I.X⊑X} {pB = I.X⊑X}
        (CTI.x⊑x² {p = I.X⊑X} Z Z))
      ℕ⇒ℕ⊑★⇒★)
    (CTI.⊑cast²
      (id (‵ `ℕ) !)
      (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
      ℕ⊑★)

checkpoint₂-ladder : String
checkpoint₂-ladder = impLadderDefault checkpoint₂-imprecision

checkpoint₃-imprecision :
  matched-world CTI.⊢² more-checkpoint₃ ⊑ less-checkpoint₃ ∶ ℕ⊑★
checkpoint₃-imprecision =
  CTI.reveal⊑reveal²
    source-reveal⊢
    target-reveal⊢
    refl
    refl
    ℕ⊑★
    (CTI.·⊑·²
      (CTI.ƛ⊑ƛ² {pA = I.X⊑X} {pB = I.X⊑X}
        (CTI.x⊑x² {p = I.X⊑X} Z Z))
      (CTI.conceal⊑conceal²
        source-conceal⊢
        target-conceal⊢
        refl
        refl
        ℕ⊑★
        (CTI.⊑cast²
          (id (‵ `ℕ) !)
          (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
          ℕ⊑★)
        I.X⊑X))
    ℕ⊑★

checkpoint₃-ladder : String
checkpoint₃-ladder = impLadderDefault checkpoint₃-imprecision

checkpoint₄-imprecision :
  matched-world CTI.⊢² more-checkpoint₄ ⊑ less-checkpoint₄ ∶ ℕ⊑★
checkpoint₄-imprecision =
  CTI.reveal⊑reveal²
    source-reveal⊢
    target-reveal⊢
    refl
    refl
    ℕ⊑★
    (CTI.conceal⊑conceal²
      source-conceal⊢
      target-conceal⊢
      refl
      refl
      ℕ⊑★
      (CTI.⊑cast²
        (id (‵ `ℕ) !)
        (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
        ℕ⊑★)
      I.X⊑X)
    ℕ⊑★

checkpoint₄-ladder : String
checkpoint₄-ladder = impLadderDefault checkpoint₄-imprecision

checkpoint₅-imprecision :
  matched-world CTI.⊢² more-checkpoint₅ ⊑ less-checkpoint₅ ∶ ℕ⊑★
checkpoint₅-imprecision =
  CTI.⊑cast²
    (id (‵ `ℕ) !)
    (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
    ℕ⊑★

checkpoint₅-ladder : String
checkpoint₅-ladder = impLadderDefault checkpoint₅-imprecision


------------------------------------------------------------------------
-- Pinned generated ladders
------------------------------------------------------------------------

checkpoint₀-ladder-pinned :
  checkpoint₀-ladder ≡
    "⟨⟩\n" ++
    "source term  A          ηᴸA        ⊑ costs          ηᴿB        B          target term\n" ++
    "───────────  ─────────  ─────────  ───────────────  ─────────  ─────────  ───────────\n" ++
    "□₁ · □₂      ℕ          ℕ          ι⊑★              ★          ★          □₁ · □₂\n" ++
    "├ □ [ ℕ ]    (ℕ ⇒ ℕ)    (ℕ ⇒ ℕ)    ι⊑★, ι⊑★         (★ ⇒ ★)    (★ ⇒ ★)    ├ □ [ ★ ]\n" ++
    "│ Λ□         ∀ (X ⇒ X)  ∀ (X ⇒ X)  ∀(X ≈ X, X ≈ X)  ∀ (X ⇒ X)  ∀ (X ⇒ X)  │ Λ□\n" ++
    "│ λx. □      (X ⇒ X)    (X ⇒ X)    X ≈ X, X ≈ X     (X ⇒ X)    (X ⇒ X)    │ λx. □\n" ++
    "│ x          X          X          X ≈ X            X          X          │ x\n" ++
    "└ □ ⟨ ℕ↦ℕ ⟩  ℕ          ℕ          ι⊑★              ★          ★          └ □ ⟨ ℕ↦★ ⟩\n" ++
    "  42         ℕ          ℕ          ℕ⊑ℕ              ℕ          ℕ            42"
checkpoint₀-ladder-pinned = refl
checkpoint₁-ladder-pinned :
  checkpoint₁-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] X′↦★⟩\n" ++
    "source term           A        ηᴸA      ⊑ costs                            ηᴿB      B          target term\n" ++
    "────────────────────  ───────  ───────  ─────────────────────────────────  ───────  ─────────  ─────────────────────\n" ++
    "□₁ · □₂               ℕ        ℕ        ι⊑★                                ★        ★          □₁ · □₂\n" ++
    "├ □ ↑ unseal X ⇒-rev  (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ι⊑★, ι⊑★ + matched reveal partner  (★ ⇒ ★)  (★ ⇒ ★)    ├ □ ↑ unseal X′ ⇒-rev\n" ++
    "│ λx. □               (X ⇒ X)  (X ⇒ X)  X ≈ X, X ≈ X                       (X ⇒ X)  (X′ ⇒ X′)  │ λx. □\n" ++
    "│ x                   X        X        X ≈ X                              X        X′         │ x\n" ++
    "└ □ ⟨ ℕ↦ℕ ⟩           ℕ        ℕ        ι⊑★                                ★        ★          └ □ ⟨ ℕ↦★ ⟩\n" ++
    "  42                  ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ            42"
checkpoint₁-ladder-pinned = refl
checkpoint₂-ladder-pinned :
  checkpoint₂-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] X′↦★⟩\n" ++
    "source term           A        ηᴸA      ⊑ costs                            ηᴿB      B          target term\n" ++
    "────────────────────  ───────  ───────  ─────────────────────────────────  ───────  ─────────  ─────────────────────\n" ++
    "□₁ · □₂               ℕ        ℕ        ι⊑★                                ★        ★          □₁ · □₂\n" ++
    "├ □ ↑ unseal X ⇒-rev  (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ι⊑★, ι⊑★ + matched reveal partner  (★ ⇒ ★)  (★ ⇒ ★)    ├ □ ↑ unseal X′ ⇒-rev\n" ++
    "│ λx. □               (X ⇒ X)  (X ⇒ X)  X ≈ X, X ≈ X                       (X ⇒ X)  (X′ ⇒ X′)  │ λx. □\n" ++
    "│ x                   X        X        X ≈ X                              X        X′         │ x\n" ++
    "└ ─                   ℕ        ℕ        ι⊑★                                ★        ★          └ □ ⟨ ℕ↦★ ⟩\n" ++
    "  42                  ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ            42"
checkpoint₂-ladder-pinned = refl
checkpoint₃-ladder-pinned :
  checkpoint₃-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] X′↦★⟩\n" ++
    "source term   A        ηᴸA      ⊑ costs                          ηᴿB      B          target term\n" ++
    "────────────  ───────  ───────  ───────────────────────────────  ───────  ─────────  ─────────────\n" ++
    "□ ↑ unseal X  ℕ        ℕ        ι⊑★ + matched reveal partner     ★        ★          □ ↑ unseal X′\n" ++
    "□₁ · □₂       X        X        X ≈ X                            X        X′         □₁ · □₂\n" ++
    "├ λx. □       (X ⇒ X)  (X ⇒ X)  X ≈ X, X ≈ X                     (X ⇒ X)  (X′ ⇒ X′)  ├ λx. □\n" ++
    "│ x           X        X        X ≈ X                            X        X′         │ x\n" ++
    "└ □ ↓ seal X  X        X        X ≈ X + matched conceal partner  X        X′         └ □ ↓ seal X′\n" ++
    "  ─           ℕ        ℕ        ι⊑★                              ★        ★            □ ⟨ ℕ↦★ ⟩\n" ++
    "  42          ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ            42"
checkpoint₃-ladder-pinned = refl
checkpoint₄-ladder-pinned :
  checkpoint₄-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] X′↦★⟩\n" ++
    "source term   A  ηᴸA  ⊑ costs                          ηᴿB  B   target term\n" ++
    "────────────  ─  ───  ───────────────────────────────  ───  ──  ─────────────\n" ++
    "□ ↑ unseal X  ℕ  ℕ    ι⊑★ + matched reveal partner     ★    ★   □ ↑ unseal X′\n" ++
    "□ ↓ seal X    X  X    X ≈ X + matched conceal partner  X    X′  □ ↓ seal X′\n" ++
    "─             ℕ  ℕ    ι⊑★                              ★    ★   □ ⟨ ℕ↦★ ⟩\n" ++
    "42            ℕ  ℕ    ℕ⊑ℕ                              ℕ    ℕ   42"
checkpoint₄-ladder-pinned = refl
checkpoint₅-ladder-pinned :
  checkpoint₅-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] X′↦★⟩\n" ++
    "source term  A  ηᴸA  ⊑ costs  ηᴿB  B  target term\n" ++
    "───────────  ─  ───  ───────  ───  ─  ───────────\n" ++
    "─            ℕ  ℕ    ι⊑★      ★    ★  □ ⟨ ℕ↦★ ⟩\n" ++
    "42           ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  42"
checkpoint₅-ladder-pinned = refl
