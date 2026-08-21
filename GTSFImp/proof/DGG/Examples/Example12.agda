module proof.DGG.Examples.Example12 where

-- File Charter:
--   * Gives source-language programs whose ordinary compilations contain the
--     inst/gen cast sequence that drives Cambridge26 Example 12.
--   * Checks both source typings and their gradual term-imprecision proof.
--   * Records the exact ordinary compiler outputs, a paired checkpoint after
--     every more-precise step, and checked whole-term reductions to 7.
--   * Does not claim that the hand-written pre-allocation Example 12 terms are
--     literal compiler reducts; call-by-value fires inst before exposing that
--     nested-cast checkpoint.
--   * Keeps the operational checkpoints grounded only in the source language,
--     compiler, and trusted reduction semantics.  The initial checkpoint also
--     checks the live cast-term relation and pins its generated Imp Ladder.

import Data.Fin as Fin
open import Data.List using (List; []; _∷_)
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
open import TyStore using (store-empty; store-bind)
open import Conversion using (seal; unseal; _↦↑_)
open import CastTerms using (Term; ⟨_,_,_⟩; _⊢_⦂_)
import CastTerms as C
open import Compile using (compile)
open import Primitives using (κℕ)
open import Reduction using
  (keep; bind; applyEnv; []; _∷_; _—↠[_]_; _—→[_]⟨_⟩_; _∎[])
open import Eval using (step?; value?)
open import proof.DGG.Examples.Source using (cast)
import proof.DGG.ExampleTerms as CastExample12
import proof.DGG.OneStep as Step
import Example as Ex
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.World using (emptyᶜ)
open import proof.DGG.ImpLadder using
  (Row; row; renderTable; obstructionRow; impLadderDefault)

open GTI using () renaming
  (_∣_⊢ᴳ_⊑_⦂_⊑_∶_ to _∣_⊢ᴳ²_⊑_⦂_⊑_∶_)

------------------------------------------------------------------------
-- Types and consistency
------------------------------------------------------------------------

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

X⇒X : ∀ {Δ} → Ty (Nat.suc Δ)
X⇒X = ＇ Fin.zero ⇒ ＇ Fin.zero

∀X⇒X : ∀ {Δ} → Ty Δ
∀X⇒X = `∀ X⇒X

star⇒star : ∀ {Δ} → Ty Δ
star⇒star = ★ ⇒ ★

X∈X⇒X : ∀ {Δ} → Fin.zero ∈ᵗ X⇒X {Δ}
X∈X⇒X = ∈-fun-left var-∈

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

flip-inst-★?X : ∀ {Δ} {μ : Env∼ Δ}
  → flipᵐ (instᵐ μ) ⊢ ★ ∼ ＇ Fin.zero
flip-inst-★?X =
  ？_ ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ ★∼G = ★∼Xᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Bns = nonstar-X ⦄

flip-gen-X! : ∀ {Δ} {μ : Env∼ Δ}
  → flipᵐ (genᵐ μ) ⊢ ＇ Fin.zero ∼ ★
flip-gen-X! =
  _! ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ G∼★ = X∼★ᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Ans = nonstar-X ⦄

∀X⇒X∼∀X⇒X : ∀ {Δ} → ∀X⇒X {Δ} ∼ ∀X⇒X
∀X⇒X∼∀X⇒X = ∀ᶜ (id (＇ Fin.zero) ↦ id (＇ Fin.zero))

★⇒★∼∀X⇒X : ∀ {Δ} → star⇒star {Δ} ∼ ∀X⇒X
★⇒★∼∀X⇒X =
  gen_ ⦃ Bnv = nonvar-fun ⦄ ⦃ z∈B = X∈X⇒X ⦄
    (flip-gen-X! ↦ gen-★?X) (λ ())

∀X⇒X∼★⇒★ : ∀ {Δ} → ∀X⇒X {Δ} ∼ star⇒star
∀X⇒X∼★⇒★ =
  inst_ ⦃ Anv = nonvar-fun ⦄ ⦃ z∈A = X∈X⇒X ⦄
    (flip-inst-★?X ↦ inst-X!) (λ ())

------------------------------------------------------------------------
-- Source programs
------------------------------------------------------------------------

ℓ-body : Label
ℓ-body = 0

ℓ-inner : Label
ℓ-inner = 1

ℓ-outer : Label
ℓ-outer = 2

more-precise : GTerm 0
more-precise =
  (ƛ ∀X⇒X ⇒
    (((` 0) `[ ℕᵗ ]) ·[ ℓ-body ] $ (κℕ 7)))
  ·[ ℓ-outer ]
  cast ℓ-inner ∀X⇒X (Λ (ƛ ＇ Fin.zero ⇒ ` 0))

less-precise : GTerm 0
less-precise =
  (ƛ ∀X⇒X ⇒
    (((` 0) `[ ℕᵗ ]) ·[ ℓ-body ] $ (κℕ 7)))
  ·[ ℓ-outer ]
  cast ℓ-inner star⇒star (Λ (ƛ ＇ Fin.zero ⇒ ` 0))

------------------------------------------------------------------------
-- Source typing
------------------------------------------------------------------------

more-precise-⊢ : 0 ∣ [] ⊢ᴳ more-precise ⦂ ℕᵗ
more-precise-⊢ =
  ⊢·
    (⊢ƛ (⊢· (⊢• (⊢` Z)) (⊢$ (κℕ 7)) (id (‵ `ℕ))))
    (⊢·
      (⊢ƛ (⊢` Z))
      (⊢Λ {zero∈A = X∈X⇒X}
        (ƛ ＇ Fin.zero ⇒ ` 0) (⊢ƛ (⊢` Z)))
      ∀X⇒X∼∀X⇒X)
    ∀X⇒X∼∀X⇒X

less-precise-⊢ : 0 ∣ [] ⊢ᴳ less-precise ⦂ ℕᵗ
less-precise-⊢ =
  ⊢·
    (⊢ƛ (⊢· (⊢• (⊢` Z)) (⊢$ (κℕ 7)) (id (‵ `ℕ))))
    (⊢·
      (⊢ƛ (⊢` Z))
      (⊢Λ {zero∈A = X∈X⇒X}
        (ƛ ＇ Fin.zero ⇒ ` 0) (⊢ƛ (⊢` Z)))
      ★⇒★∼∀X⇒X)
    ∀X⇒X∼★⇒★

------------------------------------------------------------------------
-- Source imprecision
------------------------------------------------------------------------

ℕ⊑ℕ : ∀ {Δ} {μ : I.ImpEnv Δ} → μ I.⊢ ℕᵗ ⊑ ℕᵗ
ℕ⊑ℕ = I.ι⊑ι

X⇒X⊑X⇒X : ∀ {Δ} {μ : I.ImpEnv (Nat.suc Δ)}
  → μ I.⊢ X⇒X ⊑ X⇒X
X⇒X⊑X⇒X = I.⇒⊑⇒ I.X⊑X I.X⊑X

∀X⇒X⊑∀X⇒X : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ ∀X⇒X ⊑ ∀X⇒X
∀X⇒X⊑∀X⇒X = I.∀⊑∀ X⇒X⊑X⇒X

∀X⇒X⊑★⇒★ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ ∀X⇒X ⊑ star⇒star
∀X⇒X⊑★⇒★ =
  I.∀⊑ nonvar-fun X∈X⇒X
    (I.⇒⊑⇒ (I.X⊑★ refl) (I.X⊑★ refl))

source-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ² more-precise ⊑ less-precise
    ⦂ ℕᵗ ⊑ ℕᵗ ∶ ℕ⊑ℕ
source-imprecision =
  GTI.·⊑·ᴳ
    {pA = ∀X⇒X⊑∀X⇒X} {pC = ∀X⇒X⊑★⇒★}
    (GTI.ƛ⊑ƛᴳ
      {pA = ∀X⇒X⊑∀X⇒X} {pB = ℕ⊑ℕ}
      (GTI.·⊑·ᴳ {pA = ℕ⊑ℕ} {pB = ℕ⊑ℕ} {pC = ℕ⊑ℕ}
        (GTI.[]⊑[]ᴳ {p = X⇒X⊑X⇒X}
          (GTI.x⊑xᴳ GTI.Zⁱ) ℕ⊑ℕ
          (I.⇒⊑⇒ ℕ⊑ℕ ℕ⊑ℕ))
        (GTI.κ⊑κᴳ (κℕ 7))
        (id (‵ `ℕ)) (id (‵ `ℕ))))
    (GTI.·⊑·ᴳ
      {pA = ∀X⇒X⊑★⇒★} {pB = ∀X⇒X⊑★⇒★}
      {pC = ∀X⇒X⊑∀X⇒X}
      (GTI.ƛ⊑ƛᴳ
        {pA = ∀X⇒X⊑★⇒★} {pB = ∀X⇒X⊑★⇒★}
        (GTI.x⊑xᴳ GTI.Zⁱ))
      (GTI.Λ⊑Λᴳ {p = X⇒X⊑X⇒X} GTI.lift-[]
        (ƛ ＇ Fin.zero ⇒ ` 0)
        (ƛ ＇ Fin.zero ⇒ ` 0)
        X∈X⇒X X∈X⇒X
        (GTI.ƛ⊑ƛᴳ {pA = I.X⊑X} {pB = I.X⊑X}
          (GTI.x⊑xᴳ GTI.Zⁱ)))
      ∀X⇒X∼∀X⇒X ★⇒★∼∀X⇒X)
    ∀X⇒X∼∀X⇒X ∀X⇒X∼★⇒★

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

more-precise-compiled-shape :
  more-precise-compiled ≡
    (C.ƛ
      ((C.` 0 C.⦂∀ X⇒X [ ℕᵗ ]) C.·
        (C.$ (κℕ 7) C.⟨ id (‵ `ℕ) ⟩))) C.·
    (((C.ƛ (C.` 0)) C.·
      ((C.Λ (C.ƛ (C.` 0))) C.⟨ ∀X⇒X∼∀X⇒X ⟩)) C.⟨
      ∀X⇒X∼∀X⇒X ⟩)
more-precise-compiled-shape = refl

less-precise-compiled-shape :
  less-precise-compiled ≡
    (C.ƛ
      ((C.` 0 C.⦂∀ X⇒X [ ℕᵗ ]) C.·
        (C.$ (κℕ 7) C.⟨ id (‵ `ℕ) ⟩))) C.·
    (((C.ƛ (C.` 0)) C.·
      ((C.Λ (C.ƛ (C.` 0))) C.⟨ ∀X⇒X∼★⇒★ ⟩)) C.⟨
      ★⇒★∼∀X⇒X ⟩)
less-precise-compiled-shape = refl

more-precise-eval :
  Ex.evalNat Ex.gas more-precise-compiled-⊢ ≡ just 7
more-precise-eval = refl

less-precise-eval :
  Ex.evalNat Ex.gas less-precise-compiled-⊢ ≡ just 7
less-precise-eval = refl

------------------------------------------------------------------------
-- Paired operational checkpoints
------------------------------------------------------------------------

-- Milestone 1, C0: ordinary compiler images.

more-checkpoint₀ : Term 0
more-checkpoint₀ = more-precise-compiled

less-checkpoint₀ : Term 0
less-checkpoint₀ = less-precise-compiled

checkpoint₀-imprecision :
  emptyᶜ CTI.⊢² more-checkpoint₀ ⊑ less-checkpoint₀ ∶ ℕ⊑ℕ
checkpoint₀-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.·⊑·²
        (CTI.•⊑•²
          ∀X⇒X⊑∀X⇒X
          (CTI.x⊑x² Z Z)
          ℕ⊑ℕ
          (I.⇒⊑⇒ ℕ⊑ℕ ℕ⊑ℕ))
        (CTI.cast⊑cast²
          (id (‵ `ℕ))
          (id (‵ `ℕ))
          (CTI.κ⊑κ² (κℕ 7) ℕ⊑ℕ)
          ℕ⊑ℕ)))
    (CTI.cast⊑cast² {p = ∀X⇒X⊑★⇒★}
      ∀X⇒X∼∀X⇒X
      ★⇒★∼∀X⇒X
      (CTI.·⊑·²
        (CTI.ƛ⊑ƛ²
          (CTI.x⊑x² Z Z))
        (CTI.cast⊑cast²
          ∀X⇒X∼∀X⇒X
          ∀X⇒X∼★⇒★
          (CTI.Λ⊑Λ²
            (C.ƛ (C.` 0))
            (C.ƛ (C.` 0))
            (CTI.ƛ⊑ƛ² {pA = I.X⊑X} {pB = I.X⊑X}
              (CTI.x⊑x² {p = I.X⊑X} Z Z))
            ∀X⇒X⊑∀X⇒X)
          ∀X⇒X⊑★⇒★))
      ∀X⇒X⊑∀X⇒X)

checkpoint₀-ladder : String
checkpoint₀-ladder = impLadderDefault checkpoint₀-imprecision

checkpoint₀-ladder-pinned :
  checkpoint₀-ladder ≡
    "⟨⟩\n" ++
    "source term                        A                            ηᴸA                          ⊑ costs                                                                 ηᴿB                  B                    target term\n" ++
    "─────────────────────────────────  ───────────────────────────  ───────────────────────────  ──────────────────────────────────────────────────────────────────────  ───────────────────  ───────────────────  ─────────────────────────\n" ++
    "□₁ · □₂                            ℕ                            ℕ                            ℕ⊑ℕ                                                                     ℕ                    ℕ                    □₁ · □₂\n" ++
    "├ λ♯0. □                           (∀ (♭0 ⇒ ♭0) ⇒ ℕ)            (∀ (♭0 ⇒ ♭0) ⇒ ℕ)            ∀(♭0 ≈ ♭0, ♭0 ≈ ♭0), ℕ⊑ℕ                                                (∀ (♭0 ⇒ ♭0) ⇒ ℕ)    (∀ (♭0 ⇒ ♭0) ⇒ ℕ)    λ♯0. □\n" ++
    "│ □₁ · □₂                          ℕ                            ℕ                            ℕ⊑ℕ                                                                     ℕ                    ℕ                    □₁ · □₂\n" ++
    "│ ├ □ [ ℕ ]                        (ℕ ⇒ ℕ)                      (ℕ ⇒ ℕ)                      ℕ⊑ℕ, ℕ⊑ℕ                                                                (ℕ ⇒ ℕ)              (ℕ ⇒ ℕ)              □ [ ℕ ]\n" ++
    "│ │ ♯0                             ∀ (♭0 ⇒ ♭0)                  ∀ (♭0 ⇒ ♭0)                  ∀(♭0 ≈ ♭0, ♭0 ≈ ♭0)                                                     ∀ (♭0 ⇒ ♭0)          ∀ (♭0 ⇒ ♭0)          ♯0\n" ++
    "│ └ □ ⟨ ℕ↦ℕ ⟩                      ℕ                            ℕ                            ℕ⊑ℕ                                                                     ℕ                    ℕ                    □ ⟨ ℕ↦ℕ ⟩\n" ++
    "│   7                              ℕ                            ℕ                            ℕ⊑ℕ                                                                     ℕ                    ℕ                    7\n" ++
    "└ □ ⟨ ∀ (♭0 ⇒ ♭0)↦∀ (♭0 ⇒ ♭0) ⟩    ∀ (♭0 ⇒ ♭0)                  ∀ (♭0 ⇒ ♭0)                  ∀(♭0 ≈ ♭0, ♭0 ≈ ♭0)                                                     ∀ (♭0 ⇒ ♭0)          ∀ (♭0 ⇒ ♭0)          □ ⟨ (★ ⇒ ★)↦∀ (♭0 ⇒ ♭0) ⟩\n" ++
    "  □₁ · □₂                          ∀ (♭0 ⇒ ♭0)                  ∀ (♭0 ⇒ ♭0)                  ∀⊑(mark X⊑★ at ♭0, mark X⊑★ at ♭0)                                      (★ ⇒ ★)              (★ ⇒ ★)              □₁ · □₂\n" ++
    "  ├ λ♯0. □                         (∀ (♭0 ⇒ ♭0) ⇒ ∀ (♭0 ⇒ ♭0))  (∀ (♭0 ⇒ ♭0) ⇒ ∀ (♭0 ⇒ ♭0))  ∀⊑(mark X⊑★ at ♭0, mark X⊑★ at ♭0), ∀⊑(mark X⊑★ at ♭0, mark X⊑★ at ♭0)  ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))  λ♯0. □\n" ++
    "  │ ♯0                             ∀ (♭0 ⇒ ♭0)                  ∀ (♭0 ⇒ ♭0)                  ∀⊑(mark X⊑★ at ♭0, mark X⊑★ at ♭0)                                      (★ ⇒ ★)              (★ ⇒ ★)              ♯0\n" ++
    "  └ □ ⟨ ∀ (♭0 ⇒ ♭0)↦∀ (♭0 ⇒ ♭0) ⟩  ∀ (♭0 ⇒ ♭0)                  ∀ (♭0 ⇒ ♭0)                  ∀⊑(mark X⊑★ at ♭0, mark X⊑★ at ♭0)                                      (★ ⇒ ★)              (★ ⇒ ★)              □ ⟨ ∀ (♭0 ⇒ ♭0)↦(★ ⇒ ★) ⟩\n" ++
    "    Λ□                             ∀ (♭0 ⇒ ♭0)                  ∀ (♭0 ⇒ ♭0)                  ∀(♭0 ≈ ♭0, ♭0 ≈ ♭0)                                                     ∀ (♭0 ⇒ ♭0)          ∀ (♭0 ⇒ ♭0)          Λ□\n" ++
    "    λ♯0. □                         (♭0 ⇒ ♭0)                    (♭0 ⇒ ♭0)                    ♭0 ≈ ♭0, ♭0 ≈ ♭0                                                        (♭0 ⇒ ♭0)            (♭0 ⇒ ♭0)            λ♯0. □\n" ++
    "    ♯0                             ♭0                           ♭0                           ♭0 ≈ ♭0                                                                 ♭0                   ♭0                   ♯0"
checkpoint₀-ladder-pinned = refl

-- Milestone 2, C1-C2: both source-level identity applications beta-reduce.
-- The less-precise side first performs its target-only ★ and alias
-- allocations.

more-checkpoint₁ : Term 0
more-checkpoint₁ =
  (C.ƛ
    ((C.` 0 C.⦂∀ X⇒X [ ℕᵗ ]) C.·
      (C.$ (κℕ 7) C.⟨ id {μ = idᶜ {Δ = 0}} (‵ `ℕ) ⟩))) C.·
  (((C.Λ (C.ƛ (C.` 0))) C.⟨ ∀X⇒X∼∀X⇒X ⟩) C.⟨
    ∀X⇒X∼∀X⇒X ⟩)

less-checkpoint₁ : Term 2
less-checkpoint₁ =
  (C.ƛ
    ((C.` 0 C.⦂∀ X⇒X [ ℕᵗ ]) C.·
      (C.$ (κℕ 7) C.⟨
        id {μ = renameEnv∼ wk↪ᵗ
          (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} (‵ `ℕ) ⟩))) C.·
  (((((C.ƛ (C.` 0)) C.↑
      (seal 0 (＇ 1) ↦↑ unseal 0 (＇ 1))) C.↑
      (seal 1 ★ ↦↑ unseal 1 ★)) C.⟨
      id {μ = flipᵐ (applyEnv (bind (＇ 0))
        (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ↦
      id {μ = applyEnv (bind (＇ 0))
        (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} ★ ⟩) C.⟨
    (gen_ {μ = extᵐ (extᵐ (idᶜ {Δ = 0}))}
      ⦃ z∈B = ∈-fun-left var-∈ ⦄
      ((id {μ = flipᵐ (genᵐ (extᵐ (extᵐ (idᶜ {Δ = 0}))))}
          (＇ 0) !)
        ↦
       (？_ {μ = genᵐ (extᵐ (extᵐ (idᶜ {Δ = 0})))}
          (id (＇ 0))))
      (λ ())) ⟩)

-- This is a display fixture, not a partial term-imprecision derivation.  Its
-- ordinary prefix follows the forced two-sided rules outside-in.  The three
-- `?` cells are exactly the unavailable boundary-state transitions.

checkpoint₁-obstruction-rows : List Row
checkpoint₁-obstruction-rows =
  row "□₁ · □₂" "ℕ" "ℕ" "ℕ⊑ℕ" "ℕ" "ℕ" "□₁ · □₂" ∷
  row "├ λh. □" "((∀ X. X ⇒ X) ⇒ ℕ)" "((∀ X. X ⇒ X) ⇒ ℕ)"
    "∀(X≈X, X≈X), ℕ⊑ℕ" "((∀ X. X ⇒ X) ⇒ ℕ)"
    "((∀ X. X ⇒ X) ⇒ ℕ)" "λh. □" ∷
  row "│ □₁ · □₂" "ℕ" "ℕ" "ℕ⊑ℕ" "ℕ" "ℕ" "□₁ · □₂" ∷
  row "│ ├ □ [ ℕ ]" "(ℕ ⇒ ℕ)" "(ℕ ⇒ ℕ)" "ℕ⊑ℕ, ℕ⊑ℕ"
    "(ℕ ⇒ ℕ)" "(ℕ ⇒ ℕ)" "□ [ ℕ ]" ∷
  row "│ │ h" "∀ X. X ⇒ X" "∀ X. X ⇒ X" "∀(X≈X, X≈X)"
    "∀ X. X ⇒ X" "∀ X. X ⇒ X" "h" ∷
  row "│ └ □ ⟨ ℕ↦ℕ ⟩" "ℕ" "ℕ" "ℕ⊑ℕ" "ℕ" "ℕ"
    "□ ⟨ ℕ↦ℕ ⟩" ∷
  row "│   7" "ℕ" "ℕ" "ℕ⊑ℕ" "ℕ" "ℕ" "7" ∷
  row "└ □ ⟨ (∀ X. X ⇒ X)↦(∀ X. X ⇒ X) ⟩" "∀ X. X ⇒ X"
    "∀ X. X ⇒ X" "∀(X≈X, X≈X)" "∀ X. X ⇒ X" "∀ X. X ⇒ X"
    "□ ⟨ (★ ⇒ ★)↦(∀ X. X ⇒ X) ⟩" ∷
  row "  □ ⟨ (∀ X. X ⇒ X)↦(∀ X. X ⇒ X) ⟩" "∀ X. X ⇒ X"
    "∀ X. X ⇒ X" "∀⊑(mark X⊑★ at X, mark X⊑★ at X)"
    "(★ ⇒ ★)" "(★ ⇒ ★)" "□ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩" ∷
  obstructionRow "  Λ□" "∀ X. X ⇒ X" "∀ X. X ⇒ X"
    "∀⊑(mark X⊑★ at X, mark X⊑★ at X)"
    "pending → source-fresh-behind active" "(★ ⇒ ★)" "(★ ⇒ ★)" "─" ∷
  obstructionRow "  ─" "(X ⇒ X)" "(X ⇒ X)" "X⊑★, X⊑★"
    "ExactTargetBoundary(stable, α : ★)" "(★ ⇒ ★)" "(★ ⇒ ★)"
    "□ ↑ unseal α ⇒-rev" ∷
  obstructionRow "  ─" "(X ⇒ X)" "(X ⇒ X)" "X≈X, X≈X"
    "ExactTargetBoundary(push α, β : α)" "(X ⇒ X)" "(α ⇒ α)"
    "□ ↑ unseal β ⇒-rev" ∷
  row "  λx. □" "(X ⇒ X)" "(X ⇒ X)" "X≈X, X≈X"
    "(X ⇒ X)" "(β ⇒ β)" "λx. □" ∷
  row "  x" "X" "X" "X≈X" "X" "β" "x" ∷ []

checkpoint₁-obstruction-ladder : String
checkpoint₁-obstruction-ladder = renderTable checkpoint₁-obstruction-rows

checkpoint₁-obstruction-ladder-pinned :
  checkpoint₁-obstruction-ladder ≡
    "source term                        A                   ηᴸA                 ⊑ costs                                                                    ηᴿB                 B                   target term\n" ++
    "─────────────────────────────────  ──────────────────  ──────────────────  ─────────────────────────────────────────────────────────────────────────  ──────────────────  ──────────────────  ──────────────────────────\n" ++
    "□₁ · □₂                            ℕ                   ℕ                   ℕ⊑ℕ                                                                        ℕ                   ℕ                   □₁ · □₂\n" ++
    "├ λh. □                            ((∀ X. X ⇒ X) ⇒ ℕ)  ((∀ X. X ⇒ X) ⇒ ℕ)  ∀(X≈X, X≈X), ℕ⊑ℕ                                                           ((∀ X. X ⇒ X) ⇒ ℕ)  ((∀ X. X ⇒ X) ⇒ ℕ)  λh. □\n" ++
    "│ □₁ · □₂                          ℕ                   ℕ                   ℕ⊑ℕ                                                                        ℕ                   ℕ                   □₁ · □₂\n" ++
    "│ ├ □ [ ℕ ]                        (ℕ ⇒ ℕ)             (ℕ ⇒ ℕ)             ℕ⊑ℕ, ℕ⊑ℕ                                                                   (ℕ ⇒ ℕ)             (ℕ ⇒ ℕ)             □ [ ℕ ]\n" ++
    "│ │ h                              ∀ X. X ⇒ X          ∀ X. X ⇒ X          ∀(X≈X, X≈X)                                                                ∀ X. X ⇒ X          ∀ X. X ⇒ X          h\n" ++
    "│ └ □ ⟨ ℕ↦ℕ ⟩                      ℕ                   ℕ                   ℕ⊑ℕ                                                                        ℕ                   ℕ                   □ ⟨ ℕ↦ℕ ⟩\n" ++
    "│   7                              ℕ                   ℕ                   ℕ⊑ℕ                                                                        ℕ                   ℕ                   7\n" ++
    "└ □ ⟨ (∀ X. X ⇒ X)↦(∀ X. X ⇒ X) ⟩  ∀ X. X ⇒ X          ∀ X. X ⇒ X          ∀(X≈X, X≈X)                                                                ∀ X. X ⇒ X          ∀ X. X ⇒ X          □ ⟨ (★ ⇒ ★)↦(∀ X. X ⇒ X) ⟩\n" ++
    "  □ ⟨ (∀ X. X ⇒ X)↦(∀ X. X ⇒ X) ⟩  ∀ X. X ⇒ X          ∀ X. X ⇒ X          ∀⊑(mark X⊑★ at X, mark X⊑★ at X)                                           (★ ⇒ ★)             (★ ⇒ ★)             □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  Λ□                               ∀ X. X ⇒ X          ∀ X. X ⇒ X          ∀⊑(mark X⊑★ at X, mark X⊑★ at X) + ? pending → source-fresh-behind active  (★ ⇒ ★)             (★ ⇒ ★)             ─\n" ++
    "  ─                                (X ⇒ X)             (X ⇒ X)             X⊑★, X⊑★ + ? ExactTargetBoundary(stable, α : ★)                            (★ ⇒ ★)             (★ ⇒ ★)             □ ↑ unseal α ⇒-rev\n" ++
    "  ─                                (X ⇒ X)             (X ⇒ X)             X≈X, X≈X + ? ExactTargetBoundary(push α, β : α)                            (X ⇒ X)             (α ⇒ α)             □ ↑ unseal β ⇒-rev\n" ++
    "  λx. □                            (X ⇒ X)             (X ⇒ X)             X≈X, X≈X                                                                   (X ⇒ X)             (β ⇒ β)             λx. □\n" ++
    "  x                                X                   X                   X≈X                                                                        X                   β                   x"
checkpoint₁-obstruction-ladder-pinned = refl

-- C2 is after the outer source-level identity applications.

more-checkpoint₂ : Term 0
more-checkpoint₂ =
  ((((C.Λ (C.ƛ (C.` 0))) C.⟨ ∀X⇒X∼∀X⇒X ⟩) C.⟨
      ∀X⇒X∼∀X⇒X ⟩) C.⦂∀ X⇒X [ ℕᵗ ]) C.·
  (C.$ (κℕ 7) C.⟨ id {μ = idᶜ {Δ = 0}} (‵ `ℕ) ⟩)

less-checkpoint₂ : Term 2
less-checkpoint₂ =
  (((((C.ƛ (C.` 0)) C.↑
      (seal 0 (＇ 1) ↦↑ unseal 0 (＇ 1))) C.↑
      (seal 1 ★ ↦↑ unseal 1 ★)) C.⟨
      id {μ = flipᵐ (applyEnv (bind (＇ 0))
        (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ↦
      id {μ = applyEnv (bind (＇ 0))
        (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} ★ ⟩) C.⟨
    (gen_ {μ = extᵐ (extᵐ (idᶜ {Δ = 0}))}
      ⦃ z∈B = ∈-fun-left var-∈ ⦄
      ((id {μ = flipᵐ (genᵐ (extᵐ (extᵐ (idᶜ {Δ = 0}))))}
          (＇ 0) !)
        ↦
       (？_ {μ = genᵐ (extᵐ (extᵐ (idᶜ {Δ = 0})))}
          (id (＇ 0))))
      (λ ())) ⟩ C.⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) C.·
  (C.$ (κℕ 7) C.⟨
    id {μ = renameEnv∼ wk↪ᵗ
      (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} (‵ `ℕ) ⟩)

-- Milestone 3, C3-C4: the two administrative universal casts move through
-- type application.  At C4 both sides expose natural-number allocation.

more-checkpoint₃ : Term 0
more-checkpoint₃ =
  ((((C.Λ (C.ƛ (C.` 0))) C.⟨ ∀X⇒X∼∀X⇒X ⟩)
      C.⦂∀ X⇒X [ ℕᵗ ]) C.⟨
      id {μ = flipᵐ (idᶜ {Δ = 0})} (‵ `ℕ) ↦
      id {μ = idᶜ {Δ = 0}} (‵ `ℕ) ⟩) C.·
  (C.$ (κℕ 7) C.⟨ id {μ = idᶜ {Δ = 0}} (‵ `ℕ) ⟩)

less-checkpoint₃ : Term 2
less-checkpoint₃ = less-checkpoint₂

more-checkpoint₄ : Term 0
more-checkpoint₄ =
  ((((C.Λ (C.ƛ (C.` 0))) C.⦂∀ X⇒X [ ℕᵗ ]) C.⟨
      id {μ = flipᵐ (idᶜ {Δ = 0})} (‵ `ℕ) ↦
      id {μ = idᶜ {Δ = 0}} (‵ `ℕ) ⟩) C.⟨
    id {μ = flipᵐ (idᶜ {Δ = 0})} (‵ `ℕ) ↦
    id {μ = idᶜ {Δ = 0}} (‵ `ℕ) ⟩) C.·
  (C.$ (κℕ 7) C.⟨ id {μ = idᶜ {Δ = 0}} (‵ `ℕ) ⟩)

less-checkpoint₄ : Term 2
less-checkpoint₄ = less-checkpoint₂

-- Milestone 4, C5: paired natural-number allocation extends both stores.

more-checkpoint₅ : Term 1
more-checkpoint₅ =
  ((((C.ƛ (C.` 0)) C.↑
      (seal 0 (‵ `ℕ) ↦↑ unseal 0 (‵ `ℕ))) C.⟨
      id {μ = flipᵐ (extᵐ (λ _ → ★∼X∼★))}
        (‵ `ℕ) ↦
      id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩) C.⟨
    id {μ = flipᵐ (extᵐ (λ _ → ★∼X∼★))}
      (‵ `ℕ) ↦
    id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩) C.·
  (C.$ (κℕ 7) C.⟨
    id {μ = renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})} (‵ `ℕ) ⟩)

less-checkpoint₅ : Term 3
less-checkpoint₅ =
  ((((((C.ƛ (C.` 0)) C.↑
      (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2))) C.↑
      (seal 2 ★ ↦↑ unseal 2 ★)) C.⟨
      id {μ = flipᵐ (renameEnv∼ wk↪ᵗ
        (applyEnv (bind (＇ 0))
          (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))))} ★ ↦
      id {μ = renameEnv∼ wk↪ᵗ
        (applyEnv (bind (＇ 0))
          (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ⟩) C.⟨
    (id {μ = flipᵐ (genᵐ
        (applyEnv (bind (＇ 0))
          (applyEnv (bind ★) (idᶜ {Δ = 0}))))}
      (＇ 0) !)
    ↦ (？_ {μ = genᵐ
        (applyEnv (bind (＇ 0))
          (applyEnv (bind ★) (idᶜ {Δ = 0})))}
      (id (＇ 0))) ⟩) C.↑
    (seal 0 (‵ `ℕ) ↦↑ unseal 0 (‵ `ℕ))) C.·
  (C.$ (κℕ 7) C.⟨
    id {μ = renameEnv∼ wk↪ᵗ
      (renameEnv∼ wk↪ᵗ
        (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} (‵ `ℕ) ⟩)

-- C6 through C10 push the administrative identity function casts while the
-- target waits at the checked direct-trace state right₃.

more-checkpoint₆ : Term 1
more-checkpoint₆ =
  ((((C.ƛ (C.` 0)) C.↑
      (seal 0 (‵ `ℕ) ↦↑ unseal 0 (‵ `ℕ))) C.⟨
      id {μ = flipᵐ (extᵐ (λ _ → ★∼X∼★))}
        (‵ `ℕ) ↦
      id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩) C.⟨
    id {μ = flipᵐ (extᵐ (λ _ → ★∼X∼★))}
      (‵ `ℕ) ↦
    id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩) C.·
  C.$ (κℕ 7)

more-checkpoint₇ : Term 1
more-checkpoint₇ =
  ((((C.ƛ (C.` 0)) C.↑
      (seal 0 (‵ `ℕ) ↦↑ unseal 0 (‵ `ℕ))) C.⟨
    id {μ = flipᵐ (extᵐ (λ _ → ★∼X∼★))}
      (‵ `ℕ) ↦
    id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩) C.·
    (C.$ (κℕ 7) C.⟨
      id {μ = flipᵐ (extᵐ (λ _ → ★∼X∼★))}
        (‵ `ℕ) ⟩)) C.⟨
  id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩

more-checkpoint₈ : Term 1
more-checkpoint₈ =
  ((((C.ƛ (C.` 0)) C.↑
      (seal 0 (‵ `ℕ) ↦↑ unseal 0 (‵ `ℕ))) C.⟨
    id {μ = flipᵐ (extᵐ (λ _ → ★∼X∼★))}
      (‵ `ℕ) ↦
    id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩) C.·
    C.$ (κℕ 7)) C.⟨
  id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩

more-checkpoint₉ : Term 1
more-checkpoint₉ =
  ((((C.ƛ (C.` 0)) C.↑
      (seal 0 (‵ `ℕ) ↦↑ unseal 0 (‵ `ℕ))) C.·
    (C.$ (κℕ 7) C.⟨
      id {μ = flipᵐ (extᵐ (λ _ → ★∼X∼★))}
        (‵ `ℕ) ⟩)) C.⟨
  id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩) C.⟨
  id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩

more-checkpoint₁₀ : Term 1
more-checkpoint₁₀ =
  ((((C.ƛ (C.` 0)) C.↑
      (seal 0 (‵ `ℕ) ↦↑ unseal 0 (‵ `ℕ))) C.·
    C.$ (κℕ 7)) C.⟨
  id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩) C.⟨
  id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩

less-checkpoint₆ less-checkpoint₇ less-checkpoint₈ : Term 3
less-checkpoint₉ less-checkpoint₁₀ : Term 3
less-checkpoint₆ = CastExample12.right₃
less-checkpoint₇ = CastExample12.right₃
less-checkpoint₈ = CastExample12.right₃
less-checkpoint₉ = CastExample12.right₃
less-checkpoint₁₀ = CastExample12.right₃

-- Milestone 5, C11-C12: both sides expose the shared X reveal.  C12 is after
-- the term beta step and compares the complete whole-term boundary stacks.

more-checkpoint₁₁ : Term 1
more-checkpoint₁₁ =
  (((((C.ƛ (C.` 0)) C.·
      (C.$ (κℕ 7) C.↓ seal 0 (‵ `ℕ))) C.↑
      unseal 0 (‵ `ℕ)) C.⟨
      id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩) C.⟨
    id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩)

less-checkpoint₁₁ : Term 3
less-checkpoint₁₁ = CastExample12.right₄

more-checkpoint₁₂ : Term 1
more-checkpoint₁₂ =
  ((((C.$ (κℕ 7) C.↓ seal 0 (‵ `ℕ)) C.↑
      unseal 0 (‵ `ℕ)) C.⟨
      id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩) C.⟨
    id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩)

less-checkpoint₁₂ : Term 3
less-checkpoint₁₂ = CastExample12.right₁₀

-- Milestone 6, C13-C15: the source shared boundary has cancelled and the
-- target catches all remaining boundary work.  C15 is the common result.

more-checkpoint₁₃ : Term 1
more-checkpoint₁₃ =
  (C.$ (κℕ 7) C.⟨
    id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩) C.⟨
  id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩

less-checkpoint₁₃ : Term 3
less-checkpoint₁₃ = CastExample12.right-final

more-checkpoint₁₄ : Term 1
more-checkpoint₁₄ =
  C.$ (κℕ 7) C.⟨
    id {μ = extᵐ (λ _ → ★∼X∼★)} (‵ `ℕ) ⟩

less-checkpoint₁₄ : Term 3
less-checkpoint₁₄ = CastExample12.right-final

more-checkpoint₁₅ : Term 1
more-checkpoint₁₅ = C.$ (κℕ 7)

less-checkpoint₁₅ : Term 3
less-checkpoint₁₅ = CastExample12.right-final

------------------------------------------------------------------------
-- One checked more-precise step per checkpoint
------------------------------------------------------------------------

more-checkpoint₀↠₁ :
  more-checkpoint₀ —↠[ keep ∷ [] ] more-checkpoint₁
more-checkpoint₀↠₁ =
  more-checkpoint₀
  —→[ keep ]⟨ Step.reduction
    (Step.from-just-step {Σ = store-empty}
      (step? store-empty more-checkpoint₀) refl) ⟩
  more-checkpoint₁ ∎[]

more-checkpoint₁↠₂ :
  more-checkpoint₁ —↠[ keep ∷ [] ] more-checkpoint₂
more-checkpoint₁↠₂ =
  more-checkpoint₁
  —→[ keep ]⟨ Step.reduction
    (Step.from-just-step {Σ = store-empty}
      (step? store-empty more-checkpoint₁) refl) ⟩
  more-checkpoint₂ ∎[]

more-checkpoint₂↠₃ :
  more-checkpoint₂ —↠[ keep ∷ [] ] more-checkpoint₃
more-checkpoint₂↠₃ =
  more-checkpoint₂
  —→[ keep ]⟨ Step.reduction
    (Step.from-just-step {Σ = store-empty}
      (step? store-empty more-checkpoint₂) refl) ⟩
  more-checkpoint₃ ∎[]

more-checkpoint₃↠₄ :
  more-checkpoint₃ —↠[ keep ∷ [] ] more-checkpoint₄
more-checkpoint₃↠₄ =
  more-checkpoint₃
  —→[ keep ]⟨ Step.reduction
    (Step.from-just-step {Σ = store-empty}
      (step? store-empty more-checkpoint₃) refl) ⟩
  more-checkpoint₄ ∎[]

more-checkpoint₄↠₅ :
  more-checkpoint₄ —↠[ bind (‵ `ℕ) ∷ [] ] more-checkpoint₅
more-checkpoint₄↠₅ =
  more-checkpoint₄
  —→[ bind (‵ `ℕ) ]⟨ Step.reduction
    (Step.from-just-step {Σ = store-empty}
      (step? store-empty more-checkpoint₄) refl) ⟩
  more-checkpoint₅ ∎[]

more-checkpoint₅↠₆ :
  more-checkpoint₅ —↠[ keep ∷ [] ] more-checkpoint₆
more-checkpoint₅↠₆ =
  more-checkpoint₅
  —→[ keep ]⟨ Step.reduction
    (Step.from-just-step {Σ = store-bind store-empty (‵ `ℕ)}
      (step? (store-bind store-empty (‵ `ℕ)) more-checkpoint₅) refl) ⟩
  more-checkpoint₆ ∎[]

more-checkpoint₆↠₇ :
  more-checkpoint₆ —↠[ keep ∷ [] ] more-checkpoint₇
more-checkpoint₆↠₇ =
  more-checkpoint₆
  —→[ keep ]⟨ Step.reduction
    (Step.from-just-step {Σ = store-bind store-empty (‵ `ℕ)}
      (step? (store-bind store-empty (‵ `ℕ)) more-checkpoint₆) refl) ⟩
  more-checkpoint₇ ∎[]

more-checkpoint₇↠₈ :
  more-checkpoint₇ —↠[ keep ∷ [] ] more-checkpoint₈
more-checkpoint₇↠₈ =
  more-checkpoint₇
  —→[ keep ]⟨ Step.reduction
    (Step.from-just-step {Σ = store-bind store-empty (‵ `ℕ)}
      (step? (store-bind store-empty (‵ `ℕ)) more-checkpoint₇) refl) ⟩
  more-checkpoint₈ ∎[]

more-checkpoint₈↠₉ :
  more-checkpoint₈ —↠[ keep ∷ [] ] more-checkpoint₉
more-checkpoint₈↠₉ =
  more-checkpoint₈
  —→[ keep ]⟨ Step.reduction
    (Step.from-just-step {Σ = store-bind store-empty (‵ `ℕ)}
      (step? (store-bind store-empty (‵ `ℕ)) more-checkpoint₈) refl) ⟩
  more-checkpoint₉ ∎[]

more-checkpoint₉↠₁₀ :
  more-checkpoint₉ —↠[ keep ∷ [] ] more-checkpoint₁₀
more-checkpoint₉↠₁₀ =
  more-checkpoint₉
  —→[ keep ]⟨ Step.reduction
    (Step.from-just-step {Σ = store-bind store-empty (‵ `ℕ)}
      (step? (store-bind store-empty (‵ `ℕ)) more-checkpoint₉) refl) ⟩
  more-checkpoint₁₀ ∎[]

more-checkpoint₁₀↠₁₁ :
  more-checkpoint₁₀ —↠[ keep ∷ [] ] more-checkpoint₁₁
more-checkpoint₁₀↠₁₁ =
  more-checkpoint₁₀
  —→[ keep ]⟨ Step.reduction
    (Step.from-just-step {Σ = store-bind store-empty (‵ `ℕ)}
      (step? (store-bind store-empty (‵ `ℕ)) more-checkpoint₁₀) refl) ⟩
  more-checkpoint₁₁ ∎[]

more-checkpoint₁₁↠₁₂ :
  more-checkpoint₁₁ —↠[ keep ∷ [] ] more-checkpoint₁₂
more-checkpoint₁₁↠₁₂ =
  more-checkpoint₁₁
  —→[ keep ]⟨ Step.reduction
    (Step.from-just-step {Σ = store-bind store-empty (‵ `ℕ)}
      (step? (store-bind store-empty (‵ `ℕ)) more-checkpoint₁₁) refl) ⟩
  more-checkpoint₁₂ ∎[]

more-checkpoint₁₂↠₁₃ :
  more-checkpoint₁₂ —↠[ keep ∷ [] ] more-checkpoint₁₃
more-checkpoint₁₂↠₁₃ =
  more-checkpoint₁₂
  —→[ keep ]⟨ Step.reduction
    (Step.from-just-step {Σ = store-bind store-empty (‵ `ℕ)}
      (step? (store-bind store-empty (‵ `ℕ)) more-checkpoint₁₂) refl) ⟩
  more-checkpoint₁₃ ∎[]

more-checkpoint₁₃↠₁₄ :
  more-checkpoint₁₃ —↠[ keep ∷ [] ] more-checkpoint₁₄
more-checkpoint₁₃↠₁₄ =
  more-checkpoint₁₃
  —→[ keep ]⟨ Step.reduction
    (Step.from-just-step {Σ = store-bind store-empty (‵ `ℕ)}
      (step? (store-bind store-empty (‵ `ℕ)) more-checkpoint₁₃) refl) ⟩
  more-checkpoint₁₄ ∎[]

more-checkpoint₁₄↠₁₅ :
  more-checkpoint₁₄ —↠[ keep ∷ [] ] more-checkpoint₁₅
more-checkpoint₁₄↠₁₅ =
  more-checkpoint₁₄
  —→[ keep ]⟨ Step.reduction
    (Step.from-just-step {Σ = store-bind store-empty (‵ `ℕ)}
      (step? (store-bind store-empty (‵ `ℕ)) more-checkpoint₁₄) refl) ⟩
  more-checkpoint₁₅ ∎[]

------------------------------------------------------------------------
-- Less-precise catch-up between adjacent checkpoints
------------------------------------------------------------------------

less-checkpoint₀↠₁ :
  less-checkpoint₀ —↠[
    bind ★ ∷ bind (＇ 0) ∷ keep ∷ [] ] less-checkpoint₁
less-checkpoint₀↠₁ =
  less-checkpoint₀
  —→[ bind ★ ]⟨ Step.reduction
    (Step.from-just-step {Σ = store-empty}
      (step? store-empty less-checkpoint₀) refl) ⟩
  (C.ƛ
    ((C.` 0 C.⦂∀ X⇒X [ ℕᵗ ]) C.·
      (C.$ (κℕ 7) C.⟨
        id {μ = renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})} (‵ `ℕ) ⟩))) C.·
  (((C.ƛ (C.` 0)) C.·
    ((((C.Λ (C.ƛ (C.` 0))) C.⦂∀ X⇒X [ ＇ 0 ]) C.↑
      (seal 0 ★ ↦↑ unseal 0 ★)) C.⟨
      id {μ = flipᵐ (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} ★ ↦
      id {μ = renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})} ★ ⟩)) C.⟨
    (gen_ {μ = extᵐ (idᶜ {Δ = 0})}
      ⦃ z∈B = ∈-fun-left var-∈ ⦄
      ((id {μ = flipᵐ (genᵐ (extᵐ (idᶜ {Δ = 0})))}
          (＇ 0) !)
        ↦
       (？_ {μ = genᵐ (extᵐ (idᶜ {Δ = 0}))}
          (id (＇ 0))))
      (λ ())) ⟩)
  —→[ bind (＇ 0) ]⟨ Step.reduction
    (Step.from-just-step {Σ = store-bind store-empty ★}
      (step? (store-bind store-empty ★)
        ((C.ƛ
          ((C.` 0 C.⦂∀ X⇒X [ ℕᵗ ]) C.·
            (C.$ (κℕ 7) C.⟨
              id {μ = renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})}
                (‵ `ℕ) ⟩))) C.·
         (((C.ƛ (C.` 0)) C.·
           ((((C.Λ (C.ƛ (C.` 0))) C.⦂∀ X⇒X [ ＇ 0 ]) C.↑
             (seal 0 ★ ↦↑ unseal 0 ★)) C.⟨
             id {μ = flipᵐ (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} ★ ↦
             id {μ = renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})} ★ ⟩)) C.⟨
           (gen_ {μ = extᵐ (idᶜ {Δ = 0})}
             ⦃ z∈B = ∈-fun-left var-∈ ⦄
             ((id {μ = flipᵐ (genᵐ (extᵐ (idᶜ {Δ = 0})))}
                 (＇ 0) !)
               ↦
              (？_ {μ = genᵐ (extᵐ (idᶜ {Δ = 0}))}
                 (id (＇ 0))))
             (λ ())) ⟩))) refl) ⟩
  (C.ƛ
    ((C.` 0 C.⦂∀ X⇒X [ ℕᵗ ]) C.·
      (C.$ (κℕ 7) C.⟨
        id {μ = renameEnv∼ wk↪ᵗ
          (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} (‵ `ℕ) ⟩))) C.·
  (((C.ƛ (C.` 0)) C.·
    (((((C.ƛ (C.` 0)) C.↑
      (seal 0 (＇ 1) ↦↑ unseal 0 (＇ 1))) C.↑
      (seal 1 ★ ↦↑ unseal 1 ★)) C.⟨
      id {μ = flipᵐ (applyEnv (bind (＇ 0))
        (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ↦
      id {μ = applyEnv (bind (＇ 0))
        (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} ★ ⟩)) C.⟨
    (gen_ {μ = extᵐ (extᵐ (idᶜ {Δ = 0}))}
      ⦃ z∈B = ∈-fun-left var-∈ ⦄
      ((id {μ = flipᵐ (genᵐ (extᵐ (extᵐ (idᶜ {Δ = 0}))))}
          (＇ 0) !)
        ↦
       (？_ {μ = genᵐ (extᵐ (extᵐ (idᶜ {Δ = 0})))}
          (id (＇ 0))))
      (λ ())) ⟩))
  —→[ keep ]⟨ Step.reduction
    (Step.from-just-step {Σ =
      store-bind (store-bind store-empty ★) (＇ 0)}
      (step? (store-bind (store-bind store-empty ★) (＇ 0))
        ((C.ƛ
          ((C.` 0 C.⦂∀ X⇒X [ ℕᵗ ]) C.·
            (C.$ (κℕ 7) C.⟨
              id {μ = renameEnv∼ wk↪ᵗ
                (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))}
                (‵ `ℕ) ⟩))) C.·
         (((C.ƛ (C.` 0)) C.·
           (((((C.ƛ (C.` 0)) C.↑
             (seal 0 (＇ 1) ↦↑ unseal 0 (＇ 1))) C.↑
             (seal 1 ★ ↦↑ unseal 1 ★)) C.⟨
             id {μ = flipᵐ (applyEnv (bind (＇ 0))
               (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ↦
             id {μ = applyEnv (bind (＇ 0))
               (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} ★ ⟩)) C.⟨
           (gen_ {μ = extᵐ (extᵐ (idᶜ {Δ = 0}))}
             ⦃ z∈B = ∈-fun-left var-∈ ⦄
             ((id {μ = flipᵐ
                 (genᵐ (extᵐ (extᵐ (idᶜ {Δ = 0}))))}
                 (＇ 0) !)
               ↦
              (？_ {μ = genᵐ (extᵐ (extᵐ (idᶜ {Δ = 0})))}
                 (id (＇ 0))))
             (λ ())) ⟩)))) refl) ⟩
  less-checkpoint₁ ∎[]

less-checkpoint₁↠₂ :
  less-checkpoint₁ —↠[ keep ∷ [] ] less-checkpoint₂
less-checkpoint₁↠₂ =
  less-checkpoint₁
  —→[ keep ]⟨ Step.reduction
    (Step.from-just-step {Σ =
      store-bind (store-bind store-empty ★) (＇ 0)}
      (step? (store-bind (store-bind store-empty ★) (＇ 0))
        less-checkpoint₁) refl) ⟩
  less-checkpoint₂ ∎[]

less-checkpoint₂↠₃ :
  less-checkpoint₂ —↠[ [] ] less-checkpoint₃
less-checkpoint₂↠₃ = less-checkpoint₂ ∎[]

less-checkpoint₃↠₄ :
  less-checkpoint₃ —↠[ [] ] less-checkpoint₄
less-checkpoint₃↠₄ = less-checkpoint₃ ∎[]

less-checkpoint₄↠₅ :
  less-checkpoint₄ —↠[ bind (‵ `ℕ) ∷ [] ] less-checkpoint₅
less-checkpoint₄↠₅ =
  less-checkpoint₄
  —→[ bind (‵ `ℕ) ]⟨ Step.reduction
    (Step.from-just-step {Σ =
      store-bind (store-bind store-empty ★) (＇ 0)}
      (step? (store-bind (store-bind store-empty ★) (＇ 0))
        less-checkpoint₄) refl) ⟩
  less-checkpoint₅ ∎[]

less-checkpoint₅↠₆ :
  less-checkpoint₅ —↠[ keep ∷ [] ] less-checkpoint₆
less-checkpoint₅↠₆ =
  less-checkpoint₅
  —→[ keep ]⟨ Step.reduction
    (Step.from-just-step {Σ = store-bind
      (store-bind (store-bind store-empty ★) (＇ 0)) (‵ `ℕ)}
      (step? (store-bind
        (store-bind (store-bind store-empty ★) (＇ 0)) (‵ `ℕ))
        less-checkpoint₅) refl) ⟩
  less-checkpoint₆ ∎[]

less-checkpoint₆↠₇ :
  less-checkpoint₆ —↠[ [] ] less-checkpoint₇
less-checkpoint₆↠₇ = less-checkpoint₆ ∎[]

less-checkpoint₇↠₈ :
  less-checkpoint₇ —↠[ [] ] less-checkpoint₈
less-checkpoint₇↠₈ = less-checkpoint₇ ∎[]

less-checkpoint₈↠₉ :
  less-checkpoint₈ —↠[ [] ] less-checkpoint₉
less-checkpoint₈↠₉ = less-checkpoint₈ ∎[]

less-checkpoint₉↠₁₀ :
  less-checkpoint₉ —↠[ [] ] less-checkpoint₁₀
less-checkpoint₉↠₁₀ = less-checkpoint₉ ∎[]

less-checkpoint₁₀↠₁₁ :
  less-checkpoint₁₀ —↠[ keep ∷ [] ] less-checkpoint₁₁
less-checkpoint₁₀↠₁₁ =
  less-checkpoint₁₀
  —→[ keep ]⟨ Step.reduction CastExample12.right-step₃ ⟩
  less-checkpoint₁₁ ∎[]

less-checkpoint₁₁↠₁₂ :
  less-checkpoint₁₁ —↠[
    keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]
    less-checkpoint₁₂
less-checkpoint₁₁↠₁₂ =
  less-checkpoint₁₁
  —→[ keep ]⟨ Step.reduction CastExample12.right-step₄ ⟩
  CastExample12.right₅
  —→[ keep ]⟨ Step.reduction CastExample12.right-step₅ ⟩
  CastExample12.right₆
  —→[ keep ]⟨ Step.reduction CastExample12.right-step₆ ⟩
  CastExample12.right₇
  —→[ keep ]⟨ Step.reduction CastExample12.right-step₇ ⟩
  CastExample12.right₈
  —→[ keep ]⟨ Step.reduction CastExample12.right-step₈ ⟩
  CastExample12.right₉
  —→[ keep ]⟨ Step.reduction CastExample12.right-step₉ ⟩
  less-checkpoint₁₂ ∎[]

less-checkpoint₁₂↠₁₃ :
  less-checkpoint₁₂ —↠[
    keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ] less-checkpoint₁₃
less-checkpoint₁₂↠₁₃ =
  less-checkpoint₁₂
  —→[ keep ]⟨ Step.reduction CastExample12.right-step₁₀ ⟩
  CastExample12.right₁₁
  —→[ keep ]⟨ Step.reduction CastExample12.right-step₁₁ ⟩
  CastExample12.right₁₂
  —→[ keep ]⟨ Step.reduction CastExample12.right-step₁₂ ⟩
  CastExample12.right₁₃
  —→[ keep ]⟨ Step.reduction CastExample12.right-step₁₃ ⟩
  CastExample12.right₁₄
  —→[ keep ]⟨ Step.reduction CastExample12.right-step₁₄ ⟩
  less-checkpoint₁₃ ∎[]

less-checkpoint₁₃↠₁₄ :
  less-checkpoint₁₃ —↠[ [] ] less-checkpoint₁₄
less-checkpoint₁₃↠₁₄ = less-checkpoint₁₃ ∎[]

less-checkpoint₁₄↠₁₅ :
  less-checkpoint₁₄ —↠[ [] ] less-checkpoint₁₅
less-checkpoint₁₄↠₁₅ = less-checkpoint₁₄ ∎[]

------------------------------------------------------------------------
-- Common final value
------------------------------------------------------------------------

more-checkpoint₁₅-is-7 : more-checkpoint₁₅ ≡ C.$ (κℕ 7)
more-checkpoint₁₅-is-7 = refl

less-checkpoint₁₅-is-7 : less-checkpoint₁₅ ≡ C.$ (κℕ 7)
less-checkpoint₁₅-is-7 = refl

more-checkpoint₁₅-value : C.Value more-checkpoint₁₅
more-checkpoint₁₅-value =
  Step.from-just-value (value? more-checkpoint₁₅) refl

less-checkpoint₁₅-value : C.Value less-checkpoint₁₅
less-checkpoint₁₅-value = CastExample12.right-final-value
