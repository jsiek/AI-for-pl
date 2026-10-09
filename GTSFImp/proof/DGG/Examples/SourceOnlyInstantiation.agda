{-# OPTIONS --safe #-}

module proof.DGG.Examples.SourceOnlyInstantiation where

-- File Charter:
--   * Checks the source-only polymorphic-instantiation pair from Example 5
--     in proof/DGG/Examples/README.md.
--   * Gives source typing and imprecision, ordinary compiler outputs, and one
--     simulation checkpoint after every more-precise reduction.
--   * Records the left-only runtime allocation and the active reveal/conceal
--     boundaries whose center has no target occupant.

import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
import Data.Nat as Nat
open import Data.Product using (proj₁; proj₂)
open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

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
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; revealGeneratorPosition; concealGeneratorPosition)
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
less-precise = (ƛ ★ ⇒ ` 0) ·[ ℓ-app ] $ (κℕ 42)


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
    (⊢ƛ (⊢` Z))
    (⊢$ (κℕ 42))
    (？ (id (‵ `ℕ)))

ℕ⊑★ : ∀ {Δ} {μ : I.ImpEnv Δ} → μ I.⊢ ℕᵗ ⊑ ★
ℕ⊑★ = I.ι⊑★

X⇒X⊑★⇒★ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → I.instᵐ μ I.⊢ X⇒X ⊑ (★ ⇒ ★)
X⇒X⊑★⇒★ = I.⇒⊑⇒ (I.X⊑★ refl) (I.X⊑★ refl)

∀X⇒X⊑★⇒★ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ ∀X⇒X ⊑ (★ ⇒ ★)
∀X⇒X⊑★⇒★ = I.∀⊑ nonvar-fun X∈X⇒X X⇒X⊑★⇒★

ℕ⇒ℕ⊑★⇒★ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ (ℕᵗ ⇒ ℕᵗ) ⊑ (★ ⇒ ★)
ℕ⇒ℕ⊑★⇒★ = I.⇒⊑⇒ ℕ⊑★ ℕ⊑★

source-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ² more-precise ⊑ less-precise
    ⦂ ℕᵗ ⊑ ★ ∶ ℕ⊑★
source-imprecision =
  GTI.·⊑·ᴳ
    (GTI.[]⊑ᴳ
      (GTI.Λ⊑ᴳ nonvar-fun X∈X⇒X GTI.lift-[]
        (ƛ ＇ Fin.zero ⇒ ` 0)
        (⊢ƛ (⊢` Z))
        (GTI.ƛ⊑ƛᴳ {pA = I.X⊑★ refl} {pB = I.X⊑★ refl}
          (GTI.x⊑xᴳ GTI.Zⁱ)))
      ℕ⊑★
      ℕ⇒ℕ⊑★⇒★)
    (GTI.κ⊑κᴳ (κℕ 42))
    (id (‵ `ℕ))
    (？ (id (‵ `ℕ)))


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

more-precise-compiled-shape :
  more-precise-compiled ≡
    ((C.Λ (C.ƛ (C.` 0))) C.⦂∀ X⇒X [ ℕᵗ ]) C.·
      (C.$ (κℕ 42) C.⟨ id (‵ `ℕ) ⟩)
more-precise-compiled-shape = refl

less-precise-compiled-shape :
  less-precise-compiled ≡
    (C.ƛ (C.` 0)) C.·
      (C.$ (κℕ 42) C.⟨ id (‵ `ℕ) ! ⟩)
less-precise-compiled-shape = refl

more-precise-eval :
  Ex.evalNat Ex.gas more-precise-compiled-⊢ ≡ just 42
more-precise-eval = refl

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

more-checkpoint₁ : Term (Step.Δ′ more-step₀)
more-checkpoint₁ = Step.next more-step₀

less-checkpoint₁ : Term 0
less-checkpoint₁ = less-checkpoint₀

more-store₁ : TyStore (Step.Δ′ more-step₀)
more-store₁ = Step.store-after more-step₀

more-step₁ : Step.OneStep more-store₁ more-checkpoint₁
more-step₁ =
  Step.from-just-step (step? more-store₁ more-checkpoint₁) refl

more-checkpoint₂ : Term (Step.Δ′ more-step₁)
more-checkpoint₂ = Step.next more-step₁

less-checkpoint₂ : Term 0
less-checkpoint₂ = less-checkpoint₁

more-store₂ : TyStore (Step.Δ′ more-step₁)
more-store₂ = Step.store-after more-step₁

more-step₂ : Step.OneStep more-store₂ more-checkpoint₂
more-step₂ =
  Step.from-just-step (step? more-store₂ more-checkpoint₂) refl

more-checkpoint₃ : Term (Step.Δ′ more-step₂)
more-checkpoint₃ = Step.next more-step₂

less-checkpoint₃ : Term 0
less-checkpoint₃ = less-checkpoint₂

more-store₃ : TyStore (Step.Δ′ more-step₂)
more-store₃ = Step.store-after more-step₂

more-step₃ : Step.OneStep more-store₃ more-checkpoint₃
more-step₃ =
  Step.from-just-step (step? more-store₃ more-checkpoint₃) refl

less-step₀ : Step.OneStep store-empty less-checkpoint₃
less-step₀ =
  Step.from-just-step (step? store-empty less-checkpoint₃) refl

more-checkpoint₄ : Term (Step.Δ′ more-step₃)
more-checkpoint₄ = Step.next more-step₃

less-checkpoint₄ : Term (Step.Δ′ less-step₀)
less-checkpoint₄ = Step.next less-step₀

more-store₄ : TyStore (Step.Δ′ more-step₃)
more-store₄ = Step.store-after more-step₃

more-step₄ : Step.OneStep more-store₄ more-checkpoint₄
more-step₄ =
  Step.from-just-step (step? more-store₄ more-checkpoint₄) refl

more-checkpoint₅ : Term (Step.Δ′ more-step₄)
more-checkpoint₅ = Step.next more-step₄

less-checkpoint₅ : Term (Step.Δ′ less-step₀)
less-checkpoint₅ = less-checkpoint₄

more-checkpoint₀↠₁ :
  more-checkpoint₀ —↠[ bind (‵ `ℕ) ∷ [] ] more-checkpoint₁
more-checkpoint₀↠₁ =
  more-checkpoint₀
  —→[ bind (‵ `ℕ) ]⟨ Step.reduction more-step₀ ⟩
  more-checkpoint₁ ∎[]

less-checkpoint₀↠₁ : less-checkpoint₀ —↠[ [] ] less-checkpoint₁
less-checkpoint₀↠₁ = less-checkpoint₀ ∎[]

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

less-checkpoint₂↠₃ : less-checkpoint₂ —↠[ [] ] less-checkpoint₃
less-checkpoint₂↠₃ = less-checkpoint₂ ∎[]

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
  —→[ keep ]⟨ Step.reduction less-step₀ ⟩
  less-checkpoint₄ ∎[]

more-checkpoint₄↠₅ :
  more-checkpoint₄ —↠[ keep ∷ [] ] more-checkpoint₅
more-checkpoint₄↠₅ =
  more-checkpoint₄
  —→[ keep ]⟨ Step.reduction more-step₄ ⟩
  more-checkpoint₅ ∎[]

less-checkpoint₄↠₅ : less-checkpoint₄ —↠[ [] ] less-checkpoint₅
less-checkpoint₄↠₅ = less-checkpoint₄ ∎[]

more-reduction :
  more-checkpoint₀ —↠[
    bind (‵ `ℕ) ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]
    more-checkpoint₅
more-reduction =
  more-checkpoint₀
  —→[ bind (‵ `ℕ) ]⟨ Step.reduction more-step₀ ⟩
  more-checkpoint₁
  —→[ keep ]⟨ Step.reduction more-step₁ ⟩
  more-checkpoint₂
  —→[ keep ]⟨ Step.reduction more-step₂ ⟩
  more-checkpoint₃
  —→[ keep ]⟨ Step.reduction more-step₃ ⟩
  more-checkpoint₄
  —→[ keep ]⟨ Step.reduction more-step₄ ⟩
  more-checkpoint₅ ∎[]

less-reduction :
  less-checkpoint₀ —↠[ keep ∷ [] ] less-checkpoint₅
less-reduction =
  less-checkpoint₀
  —→[ keep ]⟨ Step.reduction less-step₀ ⟩
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
-- The source-only allocation world
------------------------------------------------------------------------

base-context : Ctx
base-context = ⟨ 0 , store-empty , [] ⟩

source-only-world : (base-context ,ˢ ℕᵗ) ⊑ᶜ base-context
source-only-world = bindLeftᶜ emptyᶜ ℕᵗ

source-member : store-bind store-empty ℕᵗ ∋ Fin.zero ⦂ ℕᵗ
source-member = Z∋ refl

source-arrow-reveal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ]
    (Conv.seal Fin.zero ℕᵗ Conv.↦↑ Conv.unseal Fin.zero ℕᵗ)
source-arrow-reveal⊢ =
  Conv.⊢↑-⇒ (Conv.⊢↓-seal source-member)
    (Conv.⊢↑-unseal source-member)

source-reveal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ]
    Conv.unseal Fin.zero ℕᵗ
source-reveal⊢ = Conv.⊢↑-unseal source-member

source-conceal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↓[ Fin.zero ⦂ ℕᵗ ]
    Conv.seal Fin.zero ℕᵗ
source-conceal⊢ = Conv.⊢↓-seal source-member

source-arrow-reveal-active :
  revealGeneratorPosition source-arrow-reveal⊢ ≢ generator-absent
source-arrow-reveal-active ()

source-reveal-active :
  revealGeneratorPosition source-reveal⊢ ≢ generator-absent
source-reveal-active ()

source-conceal-active :
  concealGeneratorPosition source-conceal⊢ ≢ generator-absent
source-conceal-active ()

source-unoccupied : ∀ Xᴿ
  → toRenameⁱ (ηᴿᶜ source-only-world) Xᴿ
    ≢ toRenameⁱ (ηᴸᶜ source-only-world) Fin.zero
source-unoccupied ()


------------------------------------------------------------------------
-- Cast-term imprecision at every checkpoint
------------------------------------------------------------------------

checkpoint₀-imprecision :
  emptyᶜ CTI.⊢² more-checkpoint₀ ⊑ less-checkpoint₀ ∶ ℕ⊑★
checkpoint₀-imprecision =
  CTI.·⊑·²
    (CTI.•⊑²
      ∀X⇒X⊑★⇒★
      (CTI.Λ⊑²
        nonvar-fun
        X∈X⇒X
        (C.ƛ (C.` 0))
        (C.⊢ƛ (C.⊢` Z))
        (CTI.ƛ⊑ƛ² {pA = I.X⊑★ refl} {pB = I.X⊑★ refl}
          (CTI.x⊑x² {p = I.X⊑★ refl} Z Z))
        ∀X⇒X⊑★⇒★)
      ℕ⊑★
      ℕ⇒ℕ⊑★⇒★)
    (CTI.cast⊑cast²
      (id (‵ `ℕ))
      (id (‵ `ℕ) !)
      (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
      ℕ⊑★)

checkpoint₀-ladder : String
checkpoint₀-ladder = impLadderDefault checkpoint₀-imprecision

checkpoint₀-ladder-pinned :
  checkpoint₀-ladder ≡
    "⟨⟩\n" ++
    "source term  A          ηᴸA        ⊑ costs                           ηᴿB      B        target term\n" ++
    "───────────  ─────────  ─────────  ────────────────────────────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂      ℕ          ℕ          ι⊑★                               ★        ★        □₁ · □₂\n" ++
    "├ □ [ ℕ ]    (ℕ ⇒ ℕ)    (ℕ ⇒ ℕ)    ι⊑★, ι⊑★                          (★ ⇒ ★)  (★ ⇒ ★)  ├ ─\n" ++
    "│ Λ□         ∀ (X ⇒ X)  ∀ (X ⇒ X)  ∀⊑(mark X⊑★ at X, mark X⊑★ at X)  (★ ⇒ ★)  (★ ⇒ ★)  │ ─\n" ++
    "│ λx. □      (X ⇒ X)    (X ⇒ X)    mark X⊑★ at X, mark X⊑★ at X      (★ ⇒ ★)  (★ ⇒ ★)  │ λx. □\n" ++
    "│ x          X          X          mark X⊑★ at X                     ★        ★        │ x\n" ++
    "└ □ ⟨ ℕ↦ℕ ⟩  ℕ          ℕ          ι⊑★                               ★        ★        └ □ ⟨ ℕ↦★ ⟩\n" ++
    "  42         ℕ          ℕ          ℕ⊑ℕ                               ℕ        ℕ          42"
checkpoint₀-ladder-pinned = refl
checkpoint₁-function :
  source-only-world CTI.⊢²
    (C.ƛ (C.` 0)) C.↑
      (Conv.seal Fin.zero ℕᵗ Conv.↦↑
        Conv.unseal Fin.zero ℕᵗ)
    ⊑ C.ƛ (C.` 0) ∶ ℕ⇒ℕ⊑★⇒★
checkpoint₁-function =
  CTI.reveal⊑-only²
    source-arrow-reveal⊢
    source-arrow-reveal-active
    refl
    source-unoccupied
    ℕ⊑★
    (CTI.ƛ⊑ƛ² {pA = I.X⊑★ refl} {pB = I.X⊑★ refl}
      (CTI.x⊑x² {p = I.X⊑★ refl} Z Z))
    ℕ⇒ℕ⊑★⇒★

checkpoint₁-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₁ ⊑ less-checkpoint₁ ∶ ℕ⊑★
checkpoint₁-imprecision =
  CTI.·⊑·²
    checkpoint₁-function
    (CTI.cast⊑cast²
      (id (‵ `ℕ))
      (id (‵ `ℕ) !)
      (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
      ℕ⊑★)

checkpoint₁-ladder : String
checkpoint₁-ladder = impLadderDefault checkpoint₁-imprecision

checkpoint₁-ladder-pinned :
  checkpoint₁-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term           A        ηᴸA      ⊑ costs                       ηᴿB      B        target term\n" ++
    "────────────────────  ───────  ───────  ────────────────────────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂               ℕ        ℕ        ι⊑★                           ★        ★        □₁ · □₂\n" ++
    "├ □ ↑ unseal X ⇒-rev  (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ι⊑★, ι⊑★ + target unoccupied  (★ ⇒ ★)  (★ ⇒ ★)  ├ ─\n" ++
    "│ λx. □               (X ⇒ X)  (X ⇒ X)  mark X⊑★ at X, mark X⊑★ at X  (★ ⇒ ★)  (★ ⇒ ★)  │ λx. □\n" ++
    "│ x                   X        X        mark X⊑★ at X                 ★        ★        │ x\n" ++
    "└ □ ⟨ ℕ↦ℕ ⟩           ℕ        ℕ        ι⊑★                           ★        ★        └ □ ⟨ ℕ↦★ ⟩\n" ++
    "  42                  ℕ        ℕ        ℕ⊑ℕ                           ℕ        ℕ          42"
checkpoint₁-ladder-pinned = refl
checkpoint₂-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₂ ⊑ less-checkpoint₂ ∶ ℕ⊑★
checkpoint₂-imprecision =
  CTI.·⊑·²
    checkpoint₁-function
    (CTI.⊑cast²
      (id (‵ `ℕ) !)
      (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
      ℕ⊑★)

checkpoint₂-ladder : String
checkpoint₂-ladder = impLadderDefault checkpoint₂-imprecision

checkpoint₂-ladder-pinned :
  checkpoint₂-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term           A        ηᴸA      ⊑ costs                       ηᴿB      B        target term\n" ++
    "────────────────────  ───────  ───────  ────────────────────────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂               ℕ        ℕ        ι⊑★                           ★        ★        □₁ · □₂\n" ++
    "├ □ ↑ unseal X ⇒-rev  (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ι⊑★, ι⊑★ + target unoccupied  (★ ⇒ ★)  (★ ⇒ ★)  ├ ─\n" ++
    "│ λx. □               (X ⇒ X)  (X ⇒ X)  mark X⊑★ at X, mark X⊑★ at X  (★ ⇒ ★)  (★ ⇒ ★)  │ λx. □\n" ++
    "│ x                   X        X        mark X⊑★ at X                 ★        ★        │ x\n" ++
    "└ ─                   ℕ        ℕ        ι⊑★                           ★        ★        └ □ ⟨ ℕ↦★ ⟩\n" ++
    "  42                  ℕ        ℕ        ℕ⊑ℕ                           ℕ        ℕ          42"
checkpoint₂-ladder-pinned = refl
checkpoint₃-argument :
  source-only-world CTI.⊢²
    C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ
    ⊑ C.$ (κℕ 42) C.⟨ id {μ = idᶜ {Δ = 0}} (‵ `ℕ) ! ⟩
      ∶ I.X⊑★ refl
checkpoint₃-argument =
  CTI.conceal⊑-only²
    source-conceal⊢
    source-conceal-active
    refl
    source-unoccupied
    ℕ⊑★
    (CTI.⊑cast²
      (id (‵ `ℕ) !)
      (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
      ℕ⊑★)
    (I.X⊑★ refl)

checkpoint₃-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₃ ⊑ less-checkpoint₃ ∶ ℕ⊑★
checkpoint₃-imprecision =
  CTI.reveal⊑-only²
    source-reveal⊢
    source-reveal-active
    refl
    source-unoccupied
    ℕ⊑★
    (CTI.·⊑·²
      (CTI.ƛ⊑ƛ² {pA = I.X⊑★ refl} {pB = I.X⊑★ refl}
        (CTI.x⊑x² {p = I.X⊑★ refl} Z Z))
      checkpoint₃-argument)
    ℕ⊑★

checkpoint₃-ladder : String
checkpoint₃-ladder = impLadderDefault checkpoint₃-imprecision

checkpoint₃-ladder-pinned :
  checkpoint₃-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term   A        ηᴸA      ⊑ costs                            ηᴿB      B        target term\n" ++
    "────────────  ───────  ───────  ─────────────────────────────────  ───────  ───────  ───────────\n" ++
    "□ ↑ unseal X  ℕ        ℕ        ι⊑★ + target unoccupied            ★        ★        ─\n" ++
    "□₁ · □₂       X        X        mark X⊑★ at X                      ★        ★        □₁ · □₂\n" ++
    "├ λx. □       (X ⇒ X)  (X ⇒ X)  mark X⊑★ at X, mark X⊑★ at X       (★ ⇒ ★)  (★ ⇒ ★)  ├ λx. □\n" ++
    "│ x           X        X        mark X⊑★ at X                      ★        ★        │ x\n" ++
    "└ □ ↓ seal X  X        X        mark X⊑★ at X + target unoccupied  ★        ★        └ ─\n" ++
    "  ─           ℕ        ℕ        ι⊑★                                ★        ★          □ ⟨ ℕ↦★ ⟩\n" ++
    "  42          ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ          42"
checkpoint₃-ladder-pinned = refl
checkpoint₄-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₄ ⊑ less-checkpoint₄ ∶ ℕ⊑★
checkpoint₄-imprecision =
  CTI.reveal⊑-only²
    source-reveal⊢
    source-reveal-active
    refl
    source-unoccupied
    ℕ⊑★
    checkpoint₃-argument
    ℕ⊑★

checkpoint₄-ladder : String
checkpoint₄-ladder = impLadderDefault checkpoint₄-imprecision

checkpoint₄-ladder-pinned :
  checkpoint₄-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term   A  ηᴸA  ⊑ costs                            ηᴿB  B  target term\n" ++
    "────────────  ─  ───  ─────────────────────────────────  ───  ─  ───────────\n" ++
    "□ ↑ unseal X  ℕ  ℕ    ι⊑★ + target unoccupied            ★    ★  ─\n" ++
    "□ ↓ seal X    X  X    mark X⊑★ at X + target unoccupied  ★    ★  ─\n" ++
    "─             ℕ  ℕ    ι⊑★                                ★    ★  □ ⟨ ℕ↦★ ⟩\n" ++
    "42            ℕ  ℕ    ℕ⊑ℕ                                ℕ    ℕ  42"
checkpoint₄-ladder-pinned = refl
checkpoint₅-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₅ ⊑ less-checkpoint₅ ∶ ℕ⊑★
checkpoint₅-imprecision =
  CTI.⊑cast²
    (id (‵ `ℕ) !)
    (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
    ℕ⊑★

checkpoint₅-ladder : String
checkpoint₅-ladder = impLadderDefault checkpoint₅-imprecision

checkpoint₅-ladder-pinned :
  checkpoint₅-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term  A  ηᴸA  ⊑ costs  ηᴿB  B  target term\n" ++
    "───────────  ─  ───  ───────  ───  ─  ───────────\n" ++
    "─            ℕ  ℕ    ι⊑★      ★    ★  □ ⟨ ℕ↦★ ⟩\n" ++
    "42           ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  42"
checkpoint₅-ladder-pinned = refl
