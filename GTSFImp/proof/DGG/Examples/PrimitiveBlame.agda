{-# OPTIONS --safe #-}

module proof.DGG.Examples.PrimitiveBlame where

-- File Charter:
--   * Checks the reflexive primitive program whose dynamic left operand
--     encounters a bad Boolean-to-natural tag check.
--   * Gives source typing and imprecision, ordinary compiler outputs, and one
--     simulation checkpoint after every source-side reduction.
--   * Exercises the primitive and source-blame CTI constructors in a trusted
--     source-compiled execution.

open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (proj₁; proj₂)
open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TermCtx using (Z)
open import Consistency
open import GradualTerms renaming (_∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_)
import GradualTermImprecision as GTI
import Imprecision as I
open import TyStore using (TyStore; store-empty)
open import CastTerms using (Term; ⟨_,_,_⟩; _⊢_⦂_)
import CastTerms as C
open import Compile using (compile)
open import Primitives using (addℕ; κℕ; κ𝔹)
open import Reduction using
  (keep; []; _∷_; _—↠[_]_; _—→[_]⟨_⟩_; _∎[])
open import Eval using (step?)
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

𝔹ᵗ : ∀ {Δ} → Ty Δ
𝔹ᵗ = ‵ `𝔹

ℓ-app : Label
ℓ-app = 0

ℓ-add : Label
ℓ-add = 1

more-precise : GTerm 0
more-precise =
  ((ƛ ★ ⇒ ` 0) ·[ ℓ-app ] $ (κ𝔹 true))
    ⊕[ addℕ at ℓ-add ] $ (κℕ 1)

less-precise : GTerm 0
less-precise =
  ((ƛ ★ ⇒ ` 0) ·[ ℓ-app ] $ (κ𝔹 true))
    ⊕[ addℕ at ℓ-add ] $ (κℕ 1)


------------------------------------------------------------------------
-- Source typing and imprecision
------------------------------------------------------------------------

★∼𝔹 : ∀ {Δ} → idᶜ {Δ = Δ} ⊢ ★ ∼ 𝔹ᵗ
★∼𝔹 = ？ (id (‵ `𝔹))

★∼ℕ : ∀ {Δ} → idᶜ {Δ = Δ} ⊢ ★ ∼ ℕᵗ
★∼ℕ = ？ (id (‵ `ℕ))

more-precise-⊢ : 0 ∣ [] ⊢ᴳ more-precise ⦂ ℕᵗ
more-precise-⊢ =
  ⊢⊕ addℕ
    (⊢· (⊢ƛ (⊢` Z)) (⊢$ (κ𝔹 true)) ★∼𝔹)
    ★∼ℕ
    (⊢$ (κℕ 1))
    (id (‵ `ℕ))

less-precise-⊢ : 0 ∣ [] ⊢ᴳ less-precise ⦂ ℕᵗ
less-precise-⊢ = more-precise-⊢

source-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ² more-precise ⊑ less-precise
    ⦂ ℕᵗ ⊑ ℕᵗ ∶ I.ι⊑ι
source-imprecision =
  GTI.⊕⊑⊕ᴳ addℕ
    (GTI.·⊑·ᴳ
      (GTI.ƛ⊑ƛᴳ {pA = I.★⊑★} {pB = I.★⊑★}
        (GTI.x⊑xᴳ GTI.Zⁱ))
      (GTI.κ⊑κᴳ (κ𝔹 true))
      ★∼𝔹
      ★∼𝔹)
    ★∼ℕ
    ★∼ℕ
    (GTI.κ⊑κᴳ (κℕ 1))
    (id (‵ `ℕ))
    (id (‵ `ℕ))


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
  ⟨ 0 , store-empty , [] ⟩ ⊢ less-precise-compiled ⦂ ℕᵗ
less-precise-compiled-⊢ =
  proj₂ (compile {Σ = store-empty} less-precise-⊢)

compiled-shape :
  more-precise-compiled ≡
    ((((C.ƛ (C.` 0)) C.·
        (C.$ (κ𝔹 true) C.⟨ id (‵ `𝔹) ! ⟩))
      C.⟨ ？ (id (‵ `ℕ)) ⟩)
      C.⊕[ addℕ ]
      (C.$ (κℕ 1) C.⟨ id (‵ `ℕ) ⟩))
compiled-shape = refl

compiled-pair-equal : more-precise-compiled ≡ less-precise-compiled
compiled-pair-equal = refl

more-precise-eval :
  Ex.evalNat Ex.gas more-precise-compiled-⊢ ≡ nothing
more-precise-eval = refl

less-precise-eval :
  Ex.evalNat Ex.gas less-precise-compiled-⊢ ≡ nothing
less-precise-eval = refl


------------------------------------------------------------------------
-- Operational checkpoints
------------------------------------------------------------------------

more-checkpoint₀ : Term 0
more-checkpoint₀ = more-precise-compiled

less-checkpoint₀ : Term 0
less-checkpoint₀ = less-precise-compiled

more-step₀ : Step.OneStep store-empty more-checkpoint₀
more-step₀ =
  Step.from-just-step (step? store-empty more-checkpoint₀) refl

less-step₀ : Step.OneStep store-empty less-checkpoint₀
less-step₀ =
  Step.from-just-step (step? store-empty less-checkpoint₀) refl

more-checkpoint₁ : Term (Step.Δ′ more-step₀)
more-checkpoint₁ = Step.next more-step₀

less-checkpoint₁ : Term (Step.Δ′ less-step₀)
less-checkpoint₁ = Step.next less-step₀

more-step₁ : Step.OneStep (Step.store-after more-step₀) more-checkpoint₁
more-step₁ =
  Step.from-just-step
    (step? (Step.store-after more-step₀) more-checkpoint₁) refl

less-step₁ : Step.OneStep (Step.store-after less-step₀) less-checkpoint₁
less-step₁ =
  Step.from-just-step
    (step? (Step.store-after less-step₀) less-checkpoint₁) refl

more-checkpoint₂ : Term (Step.Δ′ more-step₁)
more-checkpoint₂ = Step.next more-step₁

less-checkpoint₂ : Term (Step.Δ′ less-step₁)
less-checkpoint₂ = Step.next less-step₁

more-step₂ : Step.OneStep (Step.store-after more-step₁) more-checkpoint₂
more-step₂ =
  Step.from-just-step
    (step? (Step.store-after more-step₁) more-checkpoint₂) refl

less-step₂ : Step.OneStep (Step.store-after less-step₁) less-checkpoint₂
less-step₂ =
  Step.from-just-step
    (step? (Step.store-after less-step₁) less-checkpoint₂) refl

more-checkpoint₃ : Term (Step.Δ′ more-step₂)
more-checkpoint₃ = Step.next more-step₂

less-checkpoint₃ : Term (Step.Δ′ less-step₂)
less-checkpoint₃ = Step.next less-step₂

more-checkpoint₀↠₁ :
  more-checkpoint₀ —↠[ keep ∷ [] ] more-checkpoint₁
more-checkpoint₀↠₁ =
  more-checkpoint₀
  —→[ keep ]⟨ Step.reduction more-step₀ ⟩
  more-checkpoint₁ ∎[]

less-checkpoint₀↠₁ :
  less-checkpoint₀ —↠[ keep ∷ [] ] less-checkpoint₁
less-checkpoint₀↠₁ =
  less-checkpoint₀
  —→[ keep ]⟨ Step.reduction less-step₀ ⟩
  less-checkpoint₁ ∎[]

more-checkpoint₁↠₂ :
  more-checkpoint₁ —↠[ keep ∷ [] ] more-checkpoint₂
more-checkpoint₁↠₂ =
  more-checkpoint₁
  —→[ keep ]⟨ Step.reduction more-step₁ ⟩
  more-checkpoint₂ ∎[]

less-checkpoint₁↠₂ :
  less-checkpoint₁ —↠[ keep ∷ [] ] less-checkpoint₂
less-checkpoint₁↠₂ =
  less-checkpoint₁
  —→[ keep ]⟨ Step.reduction less-step₁ ⟩
  less-checkpoint₂ ∎[]

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
  —→[ keep ]⟨ Step.reduction less-step₂ ⟩
  less-checkpoint₃ ∎[]

more-reduction :
  more-checkpoint₀ —↠[ keep ∷ keep ∷ keep ∷ [] ] more-checkpoint₃
more-reduction =
  more-checkpoint₀
  —→[ keep ]⟨ Step.reduction more-step₀ ⟩
  more-checkpoint₁
  —→[ keep ]⟨ Step.reduction more-step₁ ⟩
  more-checkpoint₂
  —→[ keep ]⟨ Step.reduction more-step₂ ⟩
  more-checkpoint₃ ∎[]

less-reduction :
  less-checkpoint₀ —↠[ keep ∷ keep ∷ keep ∷ [] ] less-checkpoint₃
less-reduction =
  less-checkpoint₀
  —→[ keep ]⟨ Step.reduction less-step₀ ⟩
  less-checkpoint₁
  —→[ keep ]⟨ Step.reduction less-step₁ ⟩
  less-checkpoint₂
  —→[ keep ]⟨ Step.reduction less-step₂ ⟩
  less-checkpoint₃ ∎[]

more-final : more-checkpoint₃ ≡ C.blame
more-final = refl

less-final : less-checkpoint₃ ≡ C.blame
less-final = refl


------------------------------------------------------------------------
-- Cast-term imprecision at every checkpoint
------------------------------------------------------------------------

bool-cast-imprecision :
  emptyᶜ CTI.⊢²
    C.$ (κ𝔹 true) C.⟨ id {μ = idᶜ} (‵ `𝔹) ! ⟩
    ⊑ C.$ (κ𝔹 true) C.⟨ id {μ = idᶜ} (‵ `𝔹) ! ⟩ ∶ I.★⊑★
bool-cast-imprecision =
  CTI.cast⊑cast²
    (id (‵ `𝔹) !)
    (id (‵ `𝔹) !)
    (CTI.κ⊑κ² (κ𝔹 true) I.ι⊑ι)
    I.★⊑★

one-cast-imprecision :
  emptyᶜ CTI.⊢²
    C.$ (κℕ 1) C.⟨ id {μ = idᶜ} (‵ `ℕ) ⟩
    ⊑ C.$ (κℕ 1) C.⟨ id {μ = idᶜ} (‵ `ℕ) ⟩ ∶ I.ι⊑ι
one-cast-imprecision =
  CTI.cast⊑cast²
    (id (‵ `ℕ))
    (id (‵ `ℕ))
    (CTI.κ⊑κ² (κℕ 1) I.ι⊑ι)
    I.ι⊑ι

checkpoint₀-imprecision :
  emptyᶜ CTI.⊢² more-checkpoint₀ ⊑ less-checkpoint₀ ∶ I.ι⊑ι
checkpoint₀-imprecision =
  CTI.⊕⊑⊕² addℕ
    (CTI.cast⊑cast²
      (？ (id (‵ `ℕ)))
      (？ (id (‵ `ℕ)))
      (CTI.·⊑·²
        (CTI.ƛ⊑ƛ²
          (CTI.x⊑x² {p = I.★⊑★} Z Z))
        bool-cast-imprecision)
      I.ι⊑ι)
    one-cast-imprecision
    I.ι⊑ι

checkpoint₀-ladder : String
checkpoint₀-ladder = impLadderDefault checkpoint₀-imprecision

checkpoint₀-ladder-pinned :
  checkpoint₀-ladder ≡
    "⟨⟩\n" ++
    "source term    A        ηᴸA      ⊑ costs   ηᴿB      B        target term\n" ++
    "─────────────  ───────  ───────  ────────  ───────  ───────  ───────────\n" ++
    "□₁ + □₂        ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        □₁ + □₂\n" ++
    "├ □ ⟨ ★↦ℕ ⟩    ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        □ ⟨ ★↦ℕ ⟩\n" ++
    "│ □₁ · □₂      ★        ★        ★⊑★       ★        ★        □₁ · □₂\n" ++
    "│ ├ λ♯0. □     (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★  (★ ⇒ ★)  (★ ⇒ ★)  λ♯0. □\n" ++
    "│ │ ♯0         ★        ★        ★⊑★       ★        ★        ♯0\n" ++
    "│ └ □ ⟨ 𝔹↦★ ⟩  ★        ★        ★⊑★       ★        ★        □ ⟨ 𝔹↦★ ⟩\n" ++
    "│   true       𝔹        𝔹        𝔹⊑𝔹       𝔹        𝔹        true\n" ++
    "└ □ ⟨ ℕ↦ℕ ⟩    ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        □ ⟨ ℕ↦ℕ ⟩\n" ++
    "  1            ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        1"
checkpoint₀-ladder-pinned = refl

checkpoint₁-imprecision :
  emptyᶜ CTI.⊢² more-checkpoint₁ ⊑ less-checkpoint₁ ∶ I.ι⊑ι
checkpoint₁-imprecision =
  CTI.⊕⊑⊕² addℕ
    (CTI.cast⊑cast²
      (？ (id (‵ `ℕ)))
      (？ (id (‵ `ℕ)))
      bool-cast-imprecision
      I.ι⊑ι)
    one-cast-imprecision
    I.ι⊑ι

checkpoint₁-ladder : String
checkpoint₁-ladder = impLadderDefault checkpoint₁-imprecision

checkpoint₁-ladder-pinned :
  checkpoint₁-ladder ≡
    "⟨⟩\n" ++
    "source term  A  ηᴸA  ⊑ costs  ηᴿB  B  target term\n" ++
    "───────────  ─  ───  ───────  ───  ─  ───────────\n" ++
    "□₁ + □₂      ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  □₁ + □₂\n" ++
    "├ □ ⟨ ★↦ℕ ⟩  ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  □ ⟨ ★↦ℕ ⟩\n" ++
    "│ □ ⟨ 𝔹↦★ ⟩  ★  ★    ★⊑★      ★    ★  □ ⟨ 𝔹↦★ ⟩\n" ++
    "│ true       𝔹  𝔹    𝔹⊑𝔹      𝔹    𝔹  true\n" ++
    "└ □ ⟨ ℕ↦ℕ ⟩  ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  □ ⟨ ℕ↦ℕ ⟩\n" ++
    "  1          ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  1"
checkpoint₁-ladder-pinned = refl

checkpoint₂-imprecision :
  emptyᶜ CTI.⊢² more-checkpoint₂ ⊑ less-checkpoint₂ ∶ I.ι⊑ι
checkpoint₂-imprecision =
  CTI.⊕⊑⊕² addℕ
    (CTI.blame⊑² C.⊢blame I.ι⊑ι)
    one-cast-imprecision
    I.ι⊑ι

checkpoint₂-ladder : String
checkpoint₂-ladder = impLadderDefault checkpoint₂-imprecision

checkpoint₂-ladder-pinned :
  checkpoint₂-ladder ≡
    "⟨⟩\n" ++
    "source term  A  ηᴸA  ⊑ costs  ηᴿB  B  target term\n" ++
    "───────────  ─  ───  ───────  ───  ─  ───────────\n" ++
    "□₁ + □₂      ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  □₁ + □₂\n" ++
    "├ blame      ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  blame\n" ++
    "└ □ ⟨ ℕ↦ℕ ⟩  ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  □ ⟨ ℕ↦ℕ ⟩\n" ++
    "  1          ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  1"
checkpoint₂-ladder-pinned = refl

checkpoint₃-imprecision :
  emptyᶜ CTI.⊢² more-checkpoint₃ ⊑ less-checkpoint₃ ∶ I.ι⊑ι
checkpoint₃-imprecision =
  CTI.blame⊑² C.⊢blame (I.ι⊑ι {ι = `ℕ})

checkpoint₃-ladder : String
checkpoint₃-ladder = impLadderDefault checkpoint₃-imprecision

checkpoint₃-ladder-pinned :
  checkpoint₃-ladder ≡
    "⟨⟩\n" ++
    "source term  A  ηᴸA  ⊑ costs  ηᴿB  B  target term\n" ++
    "───────────  ─  ───  ───────  ───  ─  ───────────\n" ++
    "blame        ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  blame"
checkpoint₃-ladder-pinned = refl
