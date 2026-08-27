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
--   * Keeps the operational checkpoints grounded in the source language,
--     compiler, trusted reduction semantics, and the live cast-term relation.
--     Every checkpoint pins its generated Imp Ladder.

import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
import Data.Nat as Nat
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TermCtx using (Z)
open import Consistency
open import GradualTerms renaming (_∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_)
import GradualTermImprecision as GTI
import Imprecision as I
open import TyStore using
  (store-empty; store-bind; _∋_⦂_; Z∋; S-bind∋)
import Conversion as Conv
open import Conversion using (seal; unseal; _↦↑_)
open import CastTerms using (Ctx; Term; ⟨_,_,_⟩; _,ˢ_; ⇑ᵉᵗ; _⊢_⦂_)
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
open import proof.DGG.World
open import proof.DGG.SourceRebase using (source-rebase-now)
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; revealGeneratorPosition; concealGeneratorPosition)
open import proof.DGG.ImpLadder using (impLadderDefault)

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
    "source term                    A                        ηᴸA                      ⊑ costs                                                             ηᴿB                  B                    target term\n" ++
    "─────────────────────────────  ───────────────────────  ───────────────────────  ──────────────────────────────────────────────────────────────────  ───────────────────  ───────────────────  ───────────────────────────\n" ++
    "□₁ · □₂                        ℕ                        ℕ                        ℕ⊑ℕ                                                                 ℕ                    ℕ                    □₁ · □₂\n" ++
    "├ λx. □                        (∀ (X ⇒ X) ⇒ ℕ)          (∀ (X ⇒ X) ⇒ ℕ)          ∀(X ≈ X, X ≈ X), ℕ⊑ℕ                                                (∀ (X ⇒ X) ⇒ ℕ)      (∀ (X ⇒ X) ⇒ ℕ)      ├ λx. □\n" ++
    "│ □₁ · □₂                      ℕ                        ℕ                        ℕ⊑ℕ                                                                 ℕ                    ℕ                    │ □₁ · □₂\n" ++
    "│ ├ □ [ ℕ ]                    (ℕ ⇒ ℕ)                  (ℕ ⇒ ℕ)                  ℕ⊑ℕ, ℕ⊑ℕ                                                            (ℕ ⇒ ℕ)              (ℕ ⇒ ℕ)              │ ├ □ [ ℕ ]\n" ++
    "│ │ x                          ∀ (X ⇒ X)                ∀ (X ⇒ X)                ∀(X ≈ X, X ≈ X)                                                     ∀ (X ⇒ X)            ∀ (X ⇒ X)            │ │ x\n" ++
    "│ └ □ ⟨ ℕ↦ℕ ⟩                  ℕ                        ℕ                        ℕ⊑ℕ                                                                 ℕ                    ℕ                    │ └ □ ⟨ ℕ↦ℕ ⟩\n" ++
    "│   7                          ℕ                        ℕ                        ℕ⊑ℕ                                                                 ℕ                    ℕ                    │   7\n" ++
    "└ □ ⟨ ∀ (X ⇒ X)↦∀ (X ⇒ X) ⟩    ∀ (X ⇒ X)                ∀ (X ⇒ X)                ∀(X ≈ X, X ≈ X)                                                     ∀ (X ⇒ X)            ∀ (X ⇒ X)            └ □ ⟨ (★ ⇒ ★)↦∀ (X ⇒ X) ⟩\n" ++
    "  □₁ · □₂                      ∀ (X ⇒ X)                ∀ (X ⇒ X)                ∀⊑(mark X⊑★ at X, mark X⊑★ at X)                                    (★ ⇒ ★)              (★ ⇒ ★)                □₁ · □₂\n" ++
    "  ├ λx. □                      (∀ (X ⇒ X) ⇒ ∀ (X ⇒ X))  (∀ (X ⇒ X) ⇒ ∀ (X ⇒ X))  ∀⊑(mark X⊑★ at X, mark X⊑★ at X), ∀⊑(mark X⊑★ at X, mark X⊑★ at X)  ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))    ├ λx. □\n" ++
    "  │ x                          ∀ (X ⇒ X)                ∀ (X ⇒ X)                ∀⊑(mark X⊑★ at X, mark X⊑★ at X)                                    (★ ⇒ ★)              (★ ⇒ ★)                │ x\n" ++
    "  └ □ ⟨ ∀ (X ⇒ X)↦∀ (X ⇒ X) ⟩  ∀ (X ⇒ X)                ∀ (X ⇒ X)                ∀⊑(mark X⊑★ at X, mark X⊑★ at X)                                    (★ ⇒ ★)              (★ ⇒ ★)                └ □ ⟨ ∀ (X ⇒ X)↦(★ ⇒ ★) ⟩\n" ++
    "    Λ□                         ∀ (X ⇒ X)                ∀ (X ⇒ X)                ∀(X ≈ X, X ≈ X)                                                     ∀ (X ⇒ X)            ∀ (X ⇒ X)                Λ□\n" ++
    "    λx. □                      (X ⇒ X)                  (X ⇒ X)                  X ≈ X, X ≈ X                                                        (X ⇒ X)              (X ⇒ X)                  λx. □\n" ++
    "    x                          X                        X                        X ≈ X                                                               X                    X                        x"
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


------------------------------------------------------------------------
-- Checkpoint 1 world and conversion evidence
------------------------------------------------------------------------

example12-base-context : Ctx
example12-base-context = ⟨ 0 , store-empty , [] ⟩

checkpoint₁-alpha-world :
  example12-base-context ⊑ᶜ (example12-base-context ,ˢ ★)
checkpoint₁-alpha-world =
  bindRightᶜ emptyᶜ ★ (inj₁ refl)

checkpoint₁-beta-fresh :
  RightBindFreshᶜ checkpoint₁-alpha-world (＇ Fin.zero)
checkpoint₁-beta-fresh =
  inj₂ (Fin.suc Fin.zero , refl , λ ())

checkpoint₁-world :
  example12-base-context ⊑ᶜ
    ((example12-base-context ,ˢ ★) ,ˢ ＇ Fin.zero)
checkpoint₁-world =
  bindRightᶜ checkpoint₁-alpha-world
    (＇ Fin.zero) checkpoint₁-beta-fresh

checkpoint₁-outside-world :
  ⇑ᵉᵗ example12-base-context ⊑ᶜ
    ((example12-base-context ,ˢ ★) ,ˢ ＇ Fin.zero)
checkpoint₁-outside-world = liftLeftᶜ checkpoint₁-world

checkpoint₁-alpha-ok :
  PivotUpdateᵗ
    (ηᴸᶜ checkpoint₁-outside-world)
    Fin.zero
    (toRenameⁱ (ηᴿᶜ checkpoint₁-outside-world)
      (Fin.suc Fin.zero))
checkpoint₁-alpha-ok =
  repointⁱ (ηᴸᶜ checkpoint₁-outside-world) Fin.zero
    (toRenameⁱ (ηᴿᶜ checkpoint₁-outside-world)
      (Fin.suc Fin.zero))
    (λ ())
    (λ { Fin.zero zero≠zero eq → zero≠zero refl })

checkpoint₁-alpha-representation :
  (＇ Fin.zero) ⊑ᵀ⟨ checkpoint₁-outside-world ⟩ ★
checkpoint₁-alpha-representation = I.X⊑★ refl

checkpoint₁-alpha-current :
  ⇑ᵉᵗ example12-base-context ⊑ᶜ
    ((example12-base-context ,ˢ ★) ,ˢ ＇ Fin.zero)
checkpoint₁-alpha-current =
  rebaseSourceᶜ checkpoint₁-outside-world Fin.zero
    (Fin.suc Fin.zero) checkpoint₁-alpha-ok
    open-frameᶜ
    checkpoint₁-alpha-representation

checkpoint₁-beta-ok :
  PivotUpdateᵗ
    (ηᴸᶜ checkpoint₁-alpha-current)
    Fin.zero
    (toRenameⁱ (ηᴿᶜ checkpoint₁-alpha-current) Fin.zero)
checkpoint₁-beta-ok =
  repointⁱ (ηᴸᶜ checkpoint₁-alpha-current) Fin.zero
    (toRenameⁱ (ηᴿᶜ checkpoint₁-alpha-current) Fin.zero)
    (λ ())
    (λ { Fin.zero zero≠zero eq → zero≠zero refl })

checkpoint₁-beta-representation :
  (＇ Fin.zero) ⊑ᵀ⟨ checkpoint₁-alpha-current ⟩
    (＇ (Fin.suc Fin.zero))
checkpoint₁-beta-representation = I.X⊑X

checkpoint₁-beta-current :
  ⇑ᵉᵗ example12-base-context ⊑ᶜ
    ((example12-base-context ,ˢ ★) ,ˢ ＇ Fin.zero)
checkpoint₁-beta-current =
  rebaseSourceᶜ checkpoint₁-alpha-current Fin.zero Fin.zero
    checkpoint₁-beta-ok open-frameᶜ checkpoint₁-beta-representation

checkpoint₁-beta-member :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    ∋ Fin.zero ⦂ ＇ (Fin.suc Fin.zero)
checkpoint₁-beta-member = Z∋ refl

checkpoint₁-alpha-member :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    ∋ Fin.suc Fin.zero ⦂ ★
checkpoint₁-alpha-member = S-bind∋ (Z∋ refl) refl

checkpoint₁-beta-reveal⊢ :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    Conv.⊢↑[ Fin.zero ⦂ ＇ (Fin.suc Fin.zero) ]
      (seal Fin.zero (＇ (Fin.suc Fin.zero)) ↦↑
        unseal Fin.zero (＇ (Fin.suc Fin.zero)))
checkpoint₁-beta-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-seal checkpoint₁-beta-member)
    (Conv.⊢↑-unseal checkpoint₁-beta-member)

checkpoint₁-alpha-reveal⊢ :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    Conv.⊢↑[ Fin.suc Fin.zero ⦂ ★ ]
      (seal (Fin.suc Fin.zero) ★ ↦↑
        unseal (Fin.suc Fin.zero) ★)
checkpoint₁-alpha-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-seal checkpoint₁-alpha-member)
    (Conv.⊢↑-unseal checkpoint₁-alpha-member)

checkpoint₁-beta-active :
  revealGeneratorPosition checkpoint₁-beta-reveal⊢
    ≢ generator-absent
checkpoint₁-beta-active ()

checkpoint₁-alpha-active :
  revealGeneratorPosition checkpoint₁-alpha-reveal⊢
    ≢ generator-absent
checkpoint₁-alpha-active ()


------------------------------------------------------------------------
-- Checkpoint 1 term imprecision
------------------------------------------------------------------------

checkpoint₁-imprecision :
  checkpoint₁-world CTI.⊢²
    more-checkpoint₁ ⊑ less-checkpoint₁ ∶ ℕ⊑ℕ
checkpoint₁-imprecision =
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
    (CTI.cast⊑cast²
      ∀X⇒X∼∀X⇒X
      (gen_ {μ = extᵐ (extᵐ (idᶜ {Δ = 0}))}
        ⦃ z∈B = ∈-fun-left var-∈ ⦄
        ((id {μ = flipᵐ (genᵐ (extᵐ (extᵐ (idᶜ {Δ = 0}))))}
            (＇ 0) !)
          ↦
         (？_ {μ = genᵐ (extᵐ (extᵐ (idᶜ {Δ = 0})))}
            (id (＇ 0))))
        (λ ()))
      (CTI.cast⊑cast²
        ∀X⇒X∼∀X⇒X
        (id {μ = flipᵐ (applyEnv (bind (＇ 0))
              (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ↦
          id {μ = applyEnv (bind (＇ 0))
              (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} ★)
        (CTI.Λ⊑²
          nonvar-fun
          X∈X⇒X
          (C.ƛ (C.` 0))
          (C.⊢reveal checkpoint₁-alpha-reveal⊢
            (C.⊢reveal checkpoint₁-beta-reveal⊢
              (C.⊢ƛ (C.⊢` Z))))
          (CTI.⊑reveal-rebase²
            checkpoint₁-alpha-reveal⊢
            (source-rebase-now checkpoint₁-alpha-ok
              checkpoint₁-alpha-representation)
            (CTI.⊑reveal-rebase²
              checkpoint₁-beta-reveal⊢
              (source-rebase-now checkpoint₁-beta-ok
                checkpoint₁-beta-representation)
              (CTI.ƛ⊑ƛ² {pA = I.X⊑X} {pB = I.X⊑X}
                (CTI.x⊑x² {p = I.X⊑X} Z Z))
              (I.⇒⊑⇒ I.X⊑X I.X⊑X))
            (I.⇒⊑⇒ (I.X⊑★ refl) (I.X⊑★ refl)))
          ∀X⇒X⊑★⇒★)
        ∀X⇒X⊑★⇒★)
      ∀X⇒X⊑∀X⇒X)

checkpoint₁-ladder : String
checkpoint₁-ladder = impLadderDefault checkpoint₁-imprecision

checkpoint₁-ladder-pinned :
  checkpoint₁-ladder ≡
    "⟨X: ─ ⊑[X⊑★] X′↦＇Y′ │ Y: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                  A                ηᴸA              ⊑ costs                                       ηᴿB              B                target term\n" ++
    "───────────────────────────  ───────────────  ───────────────  ────────────────────────────────────────────  ───────────────  ───────────────  ─────────────────────────\n" ++
    "□₁ · □₂                      ℕ                ℕ                ℕ⊑ℕ                                           ℕ                ℕ                □₁ · □₂\n" ++
    "├ λx. □                      (∀ (Z ⇒ Z) ⇒ ℕ)  (∀ (Z ⇒ Z) ⇒ ℕ)  ∀(Z ≈ Z, Z ≈ Z), ℕ⊑ℕ                          (∀ (Z ⇒ Z) ⇒ ℕ)  (∀ (Z ⇒ Z) ⇒ ℕ)  ├ λx. □\n" ++
    "│ □₁ · □₂                    ℕ                ℕ                ℕ⊑ℕ                                           ℕ                ℕ                │ □₁ · □₂\n" ++
    "│ ├ □ [ ℕ ]                  (ℕ ⇒ ℕ)          (ℕ ⇒ ℕ)          ℕ⊑ℕ, ℕ⊑ℕ                                      (ℕ ⇒ ℕ)          (ℕ ⇒ ℕ)          │ ├ □ [ ℕ ]\n" ++
    "│ │ x                        ∀ (Z ⇒ Z)        ∀ (Z ⇒ Z)        ∀(Z ≈ Z, Z ≈ Z)                               ∀ (Z ⇒ Z)        ∀ (Z ⇒ Z)        │ │ x\n" ++
    "│ └ □ ⟨ ℕ↦ℕ ⟩                ℕ                ℕ                ℕ⊑ℕ                                           ℕ                ℕ                │ └ □ ⟨ ℕ↦ℕ ⟩\n" ++
    "│   7                        ℕ                ℕ                ℕ⊑ℕ                                           ℕ                ℕ                │   7\n" ++
    "└ □ ⟨ ∀ (Z ⇒ Z)↦∀ (Z ⇒ Z) ⟩  ∀ (Z ⇒ Z)        ∀ (Z ⇒ Z)        ∀(Z ≈ Z, Z ≈ Z)                               ∀ (Z ⇒ Z)        ∀ (Z ⇒ Z)        └ □ ⟨ (★ ⇒ ★)↦∀ (Z ⇒ Z) ⟩\n" ++
    "  □ ⟨ ∀ (Z ⇒ Z)↦∀ (Z ⇒ Z) ⟩  ∀ (Z ⇒ Z)        ∀ (Z ⇒ Z)        ∀⊑(mark X⊑★ at Z, mark X⊑★ at Z)              (★ ⇒ ★)          (★ ⇒ ★)            □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  Λ□                         ∀ (Z ⇒ Z)        ∀ (Z ⇒ Z)        ∀⊑(mark X⊑★ at Z, mark X⊑★ at Z)              (★ ⇒ ★)          (★ ⇒ ★)            ─\n" ++
    "  ─                          (Z ⇒ Z)          (Z ⇒ Z)          mark X⊑★ at Z, mark X⊑★ at Z + source rebase  (★ ⇒ ★)          (★ ⇒ ★)            □ ↑ unseal Y′ ⇒-rev\n" ++
    "  ─                          (Z ⇒ Z)          (Y ⇒ Y)          Y ≈ Y, Y ≈ Y + source rebase                  (Y ⇒ Y)          (Y′ ⇒ Y′)          □ ↑ unseal X′ ⇒-rev\n" ++
    "  λx. □                      (Z ⇒ Z)          (X ⇒ X)          X ≈ X, X ≈ X                                  (X ⇒ X)          (X′ ⇒ X′)          λx. □\n" ++
    "  x                          Z                X                X ≈ X                                         X                X′                 x"
checkpoint₁-ladder-pinned = refl
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
-- Cast-term imprecision before the paired natural-number allocation
------------------------------------------------------------------------

checkpoint₂-imprecision :
  checkpoint₁-world CTI.⊢²
    more-checkpoint₂ ⊑ less-checkpoint₂ ∶ ℕ⊑ℕ
checkpoint₂-imprecision =
  CTI.·⊑·²
    (CTI.•⊑•²
      ∀X⇒X⊑∀X⇒X
      (CTI.cast⊑cast²
        ∀X⇒X∼∀X⇒X
        (gen_ {μ = extᵐ (extᵐ (idᶜ {Δ = 0}))}
          ⦃ z∈B = ∈-fun-left var-∈ ⦄
          ((id {μ = flipᵐ (genᵐ (extᵐ (extᵐ (idᶜ {Δ = 0}))))}
              (＇ 0) !)
            ↦
           (？_ {μ = genᵐ (extᵐ (extᵐ (idᶜ {Δ = 0})))}
              (id (＇ 0))))
          (λ ()))
        (CTI.cast⊑cast²
          ∀X⇒X∼∀X⇒X
          (id {μ = flipᵐ (applyEnv (bind (＇ 0))
                (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ↦
            id {μ = applyEnv (bind (＇ 0))
                (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} ★)
          (CTI.Λ⊑²
            nonvar-fun
            X∈X⇒X
            (C.ƛ (C.` 0))
            (C.⊢reveal checkpoint₁-alpha-reveal⊢
              (C.⊢reveal checkpoint₁-beta-reveal⊢
                (C.⊢ƛ (C.⊢` Z))))
            (CTI.⊑reveal-rebase²
              checkpoint₁-alpha-reveal⊢
              (source-rebase-now checkpoint₁-alpha-ok
                checkpoint₁-alpha-representation)
              (CTI.⊑reveal-rebase²
                checkpoint₁-beta-reveal⊢
                (source-rebase-now checkpoint₁-beta-ok
                  checkpoint₁-beta-representation)
                (CTI.ƛ⊑ƛ² {pA = I.X⊑X} {pB = I.X⊑X}
                  (CTI.x⊑x² {p = I.X⊑X} Z Z))
                (I.⇒⊑⇒ I.X⊑X I.X⊑X))
              (I.⇒⊑⇒ (I.X⊑★ refl) (I.X⊑★ refl)))
            ∀X⇒X⊑★⇒★)
          ∀X⇒X⊑★⇒★)
        ∀X⇒X⊑∀X⇒X)
      ℕ⊑ℕ
      (I.⇒⊑⇒ ℕ⊑ℕ ℕ⊑ℕ))
    (CTI.cast⊑cast²
      (id (‵ `ℕ))
      (id {μ = renameEnv∼ wk↪ᵗ
        (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} (‵ `ℕ))
      (CTI.κ⊑κ² (κℕ 7) ℕ⊑ℕ)
      ℕ⊑ℕ)

checkpoint₂-ladder : String
checkpoint₂-ladder = impLadderDefault checkpoint₂-imprecision

checkpoint₂-ladder-pinned :
  checkpoint₂-ladder ≡
    "⟨X: ─ ⊑[X⊑★] X′↦＇Y′ │ Y: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                  A          ηᴸA        ⊑ costs                                       ηᴿB        B          target term\n" ++
    "───────────────────────────  ─────────  ─────────  ────────────────────────────────────────────  ─────────  ─────────  ─────────────────────────\n" ++
    "□₁ · □₂                      ℕ          ℕ          ℕ⊑ℕ                                           ℕ          ℕ          □₁ · □₂\n" ++
    "├ □ [ ℕ ]                    (ℕ ⇒ ℕ)    (ℕ ⇒ ℕ)    ℕ⊑ℕ, ℕ⊑ℕ                                      (ℕ ⇒ ℕ)    (ℕ ⇒ ℕ)    ├ □ [ ℕ ]\n" ++
    "│ □ ⟨ ∀ (Z ⇒ Z)↦∀ (Z ⇒ Z) ⟩  ∀ (Z ⇒ Z)  ∀ (Z ⇒ Z)  ∀(Z ≈ Z, Z ≈ Z)                               ∀ (Z ⇒ Z)  ∀ (Z ⇒ Z)  │ □ ⟨ (★ ⇒ ★)↦∀ (Z ⇒ Z) ⟩\n" ++
    "│ □ ⟨ ∀ (Z ⇒ Z)↦∀ (Z ⇒ Z) ⟩  ∀ (Z ⇒ Z)  ∀ (Z ⇒ Z)  ∀⊑(mark X⊑★ at Z, mark X⊑★ at Z)              (★ ⇒ ★)    (★ ⇒ ★)    │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "│ Λ□                         ∀ (Z ⇒ Z)  ∀ (Z ⇒ Z)  ∀⊑(mark X⊑★ at Z, mark X⊑★ at Z)              (★ ⇒ ★)    (★ ⇒ ★)    │ ─\n" ++
    "│ ─                          (Z ⇒ Z)    (Z ⇒ Z)    mark X⊑★ at Z, mark X⊑★ at Z + source rebase  (★ ⇒ ★)    (★ ⇒ ★)    │ □ ↑ unseal Y′ ⇒-rev\n" ++
    "│ ─                          (Z ⇒ Z)    (Y ⇒ Y)    Y ≈ Y, Y ≈ Y + source rebase                  (Y ⇒ Y)    (Y′ ⇒ Y′)  │ □ ↑ unseal X′ ⇒-rev\n" ++
    "│ λx. □                      (Z ⇒ Z)    (X ⇒ X)    X ≈ X, X ≈ X                                  (X ⇒ X)    (X′ ⇒ X′)  │ λx. □\n" ++
    "│ x                          Z          X          X ≈ X                                         X          X′         │ x\n" ++
    "└ □ ⟨ ℕ↦ℕ ⟩                  ℕ          ℕ          ℕ⊑ℕ                                           ℕ          ℕ          └ □ ⟨ ℕ↦ℕ ⟩\n" ++
    "  7                          ℕ          ℕ          ℕ⊑ℕ                                           ℕ          ℕ            7"
checkpoint₂-ladder-pinned = refl
checkpoint₃-imprecision :
  checkpoint₁-world CTI.⊢²
    more-checkpoint₃ ⊑ less-checkpoint₃ ∶ ℕ⊑ℕ
checkpoint₃-imprecision =
  CTI.·⊑·²
    (CTI.cast⊑²
      (id {μ = flipᵐ (idᶜ {Δ = 0})} (‵ `ℕ) ↦
        id {μ = idᶜ {Δ = 0}} (‵ `ℕ))
      (CTI.•⊑•²
        ∀X⇒X⊑∀X⇒X
        (CTI.cast⊑cast²
          ∀X⇒X∼∀X⇒X
          (gen_ {μ = extᵐ (extᵐ (idᶜ {Δ = 0}))}
            ⦃ z∈B = ∈-fun-left var-∈ ⦄
            ((id {μ = flipᵐ
                (genᵐ (extᵐ (extᵐ (idᶜ {Δ = 0}))))}
                (＇ 0) !)
              ↦
             (？_ {μ = genᵐ (extᵐ (extᵐ (idᶜ {Δ = 0})))}
                (id (＇ 0))))
            (λ ()))
          (CTI.⊑cast²
            (id {μ = flipᵐ (applyEnv (bind (＇ 0))
                  (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ↦
              id {μ = applyEnv (bind (＇ 0))
                  (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} ★)
            (CTI.Λ⊑²
              nonvar-fun
              X∈X⇒X
              (C.ƛ (C.` 0))
              (C.⊢reveal checkpoint₁-alpha-reveal⊢
                (C.⊢reveal checkpoint₁-beta-reveal⊢
                  (C.⊢ƛ (C.⊢` Z))))
              (CTI.⊑reveal-rebase²
                checkpoint₁-alpha-reveal⊢
                (source-rebase-now checkpoint₁-alpha-ok
                  checkpoint₁-alpha-representation)
                (CTI.⊑reveal-rebase²
                  checkpoint₁-beta-reveal⊢
                  (source-rebase-now checkpoint₁-beta-ok
                    checkpoint₁-beta-representation)
                  (CTI.ƛ⊑ƛ² {pA = I.X⊑X} {pB = I.X⊑X}
                    (CTI.x⊑x² {p = I.X⊑X} Z Z))
                  (I.⇒⊑⇒ I.X⊑X I.X⊑X))
                (I.⇒⊑⇒ (I.X⊑★ refl) (I.X⊑★ refl)))
              ∀X⇒X⊑★⇒★)
            ∀X⇒X⊑★⇒★)
          ∀X⇒X⊑∀X⇒X)
        ℕ⊑ℕ
        (I.⇒⊑⇒ ℕ⊑ℕ ℕ⊑ℕ))
      (I.⇒⊑⇒ ℕ⊑ℕ ℕ⊑ℕ))
    (CTI.cast⊑cast²
      (id (‵ `ℕ))
      (id {μ = renameEnv∼ wk↪ᵗ
        (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} (‵ `ℕ))
      (CTI.κ⊑κ² (κℕ 7) ℕ⊑ℕ)
      ℕ⊑ℕ)

checkpoint₃-ladder : String
checkpoint₃-ladder = impLadderDefault checkpoint₃-imprecision

checkpoint₃-ladder-pinned :
  checkpoint₃-ladder ≡
    "⟨X: ─ ⊑[X⊑★] X′↦＇Y′ │ Y: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                  A          ηᴸA        ⊑ costs                                       ηᴿB        B          target term\n" ++
    "───────────────────────────  ─────────  ─────────  ────────────────────────────────────────────  ─────────  ─────────  ─────────────────────────\n" ++
    "□₁ · □₂                      ℕ          ℕ          ℕ⊑ℕ                                           ℕ          ℕ          □₁ · □₂\n" ++
    "├ □ ⟨ (ℕ ⇒ ℕ)↦(ℕ ⇒ ℕ) ⟩      (ℕ ⇒ ℕ)    (ℕ ⇒ ℕ)    ℕ⊑ℕ, ℕ⊑ℕ                                      (ℕ ⇒ ℕ)    (ℕ ⇒ ℕ)    ├ ─\n" ++
    "│ □ [ ℕ ]                    (ℕ ⇒ ℕ)    (ℕ ⇒ ℕ)    ℕ⊑ℕ, ℕ⊑ℕ                                      (ℕ ⇒ ℕ)    (ℕ ⇒ ℕ)    │ □ [ ℕ ]\n" ++
    "│ □ ⟨ ∀ (Z ⇒ Z)↦∀ (Z ⇒ Z) ⟩  ∀ (Z ⇒ Z)  ∀ (Z ⇒ Z)  ∀(Z ≈ Z, Z ≈ Z)                               ∀ (Z ⇒ Z)  ∀ (Z ⇒ Z)  │ □ ⟨ (★ ⇒ ★)↦∀ (Z ⇒ Z) ⟩\n" ++
    "│ ─                          ∀ (Z ⇒ Z)  ∀ (Z ⇒ Z)  ∀⊑(mark X⊑★ at Z, mark X⊑★ at Z)              (★ ⇒ ★)    (★ ⇒ ★)    │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "│ Λ□                         ∀ (Z ⇒ Z)  ∀ (Z ⇒ Z)  ∀⊑(mark X⊑★ at Z, mark X⊑★ at Z)              (★ ⇒ ★)    (★ ⇒ ★)    │ ─\n" ++
    "│ ─                          (Z ⇒ Z)    (Z ⇒ Z)    mark X⊑★ at Z, mark X⊑★ at Z + source rebase  (★ ⇒ ★)    (★ ⇒ ★)    │ □ ↑ unseal Y′ ⇒-rev\n" ++
    "│ ─                          (Z ⇒ Z)    (Y ⇒ Y)    Y ≈ Y, Y ≈ Y + source rebase                  (Y ⇒ Y)    (Y′ ⇒ Y′)  │ □ ↑ unseal X′ ⇒-rev\n" ++
    "│ λx. □                      (Z ⇒ Z)    (X ⇒ X)    X ≈ X, X ≈ X                                  (X ⇒ X)    (X′ ⇒ X′)  │ λx. □\n" ++
    "│ x                          Z          X          X ≈ X                                         X          X′         │ x\n" ++
    "└ □ ⟨ ℕ↦ℕ ⟩                  ℕ          ℕ          ℕ⊑ℕ                                           ℕ          ℕ          └ □ ⟨ ℕ↦ℕ ⟩\n" ++
    "  7                          ℕ          ℕ          ℕ⊑ℕ                                           ℕ          ℕ            7"
checkpoint₃-ladder-pinned = refl
checkpoint₄-imprecision :
  checkpoint₁-world CTI.⊢²
    more-checkpoint₄ ⊑ less-checkpoint₄ ∶ ℕ⊑ℕ
checkpoint₄-imprecision =
  CTI.·⊑·²
    (CTI.cast⊑²
      (id {μ = flipᵐ (idᶜ {Δ = 0})} (‵ `ℕ) ↦
        id {μ = idᶜ {Δ = 0}} (‵ `ℕ))
      (CTI.cast⊑²
        (id {μ = flipᵐ (idᶜ {Δ = 0})} (‵ `ℕ) ↦
          id {μ = idᶜ {Δ = 0}} (‵ `ℕ))
        (CTI.•⊑•²
          ∀X⇒X⊑∀X⇒X
          (CTI.⊑cast²
            (gen_ {μ = extᵐ (extᵐ (idᶜ {Δ = 0}))}
              ⦃ z∈B = ∈-fun-left var-∈ ⦄
              ((id {μ = flipᵐ
                  (genᵐ (extᵐ (extᵐ (idᶜ {Δ = 0}))))}
                  (＇ 0) !)
                ↦
               (？_ {μ = genᵐ
                  (extᵐ (extᵐ (idᶜ {Δ = 0})))} (id (＇ 0))))
              (λ ()))
            (CTI.⊑cast²
              (id {μ = flipᵐ (applyEnv (bind (＇ 0))
                    (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ↦
                id {μ = applyEnv (bind (＇ 0))
                    (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} ★)
              (CTI.Λ⊑²
                nonvar-fun
                X∈X⇒X
                (C.ƛ (C.` 0))
                (C.⊢reveal checkpoint₁-alpha-reveal⊢
                  (C.⊢reveal checkpoint₁-beta-reveal⊢
                    (C.⊢ƛ (C.⊢` Z))))
                (CTI.⊑reveal-rebase²
                  checkpoint₁-alpha-reveal⊢
                  (source-rebase-now checkpoint₁-alpha-ok
                    checkpoint₁-alpha-representation)
                  (CTI.⊑reveal-rebase²
                    checkpoint₁-beta-reveal⊢
                    (source-rebase-now checkpoint₁-beta-ok
                      checkpoint₁-beta-representation)
                    (CTI.ƛ⊑ƛ² {pA = I.X⊑X} {pB = I.X⊑X}
                      (CTI.x⊑x² {p = I.X⊑X} Z Z))
                    (I.⇒⊑⇒ I.X⊑X I.X⊑X))
                  (I.⇒⊑⇒ (I.X⊑★ refl) (I.X⊑★ refl)))
                ∀X⇒X⊑★⇒★)
              ∀X⇒X⊑★⇒★)
            ∀X⇒X⊑∀X⇒X)
          ℕ⊑ℕ
          (I.⇒⊑⇒ ℕ⊑ℕ ℕ⊑ℕ))
        (I.⇒⊑⇒ ℕ⊑ℕ ℕ⊑ℕ))
      (I.⇒⊑⇒ ℕ⊑ℕ ℕ⊑ℕ))
    (CTI.cast⊑cast²
      (id (‵ `ℕ))
      (id {μ = renameEnv∼ wk↪ᵗ
        (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} (‵ `ℕ))
      (CTI.κ⊑κ² (κℕ 7) ℕ⊑ℕ)
      ℕ⊑ℕ)

checkpoint₄-ladder : String
checkpoint₄-ladder = impLadderDefault checkpoint₄-imprecision

checkpoint₄-ladder-pinned :
  checkpoint₄-ladder ≡
    "⟨X: ─ ⊑[X⊑★] X′↦＇Y′ │ Y: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term              A          ηᴸA        ⊑ costs                                       ηᴿB        B          target term\n" ++
    "───────────────────────  ─────────  ─────────  ────────────────────────────────────────────  ─────────  ─────────  ─────────────────────────\n" ++
    "□₁ · □₂                  ℕ          ℕ          ℕ⊑ℕ                                           ℕ          ℕ          □₁ · □₂\n" ++
    "├ □ ⟨ (ℕ ⇒ ℕ)↦(ℕ ⇒ ℕ) ⟩  (ℕ ⇒ ℕ)    (ℕ ⇒ ℕ)    ℕ⊑ℕ, ℕ⊑ℕ                                      (ℕ ⇒ ℕ)    (ℕ ⇒ ℕ)    ├ ─\n" ++
    "│ □ ⟨ (ℕ ⇒ ℕ)↦(ℕ ⇒ ℕ) ⟩  (ℕ ⇒ ℕ)    (ℕ ⇒ ℕ)    ℕ⊑ℕ, ℕ⊑ℕ                                      (ℕ ⇒ ℕ)    (ℕ ⇒ ℕ)    │ ─\n" ++
    "│ □ [ ℕ ]                (ℕ ⇒ ℕ)    (ℕ ⇒ ℕ)    ℕ⊑ℕ, ℕ⊑ℕ                                      (ℕ ⇒ ℕ)    (ℕ ⇒ ℕ)    │ □ [ ℕ ]\n" ++
    "│ ─                      ∀ (Z ⇒ Z)  ∀ (Z ⇒ Z)  ∀(Z ≈ Z, Z ≈ Z)                               ∀ (Z ⇒ Z)  ∀ (Z ⇒ Z)  │ □ ⟨ (★ ⇒ ★)↦∀ (Z ⇒ Z) ⟩\n" ++
    "│ ─                      ∀ (Z ⇒ Z)  ∀ (Z ⇒ Z)  ∀⊑(mark X⊑★ at Z, mark X⊑★ at Z)              (★ ⇒ ★)    (★ ⇒ ★)    │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "│ Λ□                     ∀ (Z ⇒ Z)  ∀ (Z ⇒ Z)  ∀⊑(mark X⊑★ at Z, mark X⊑★ at Z)              (★ ⇒ ★)    (★ ⇒ ★)    │ ─\n" ++
    "│ ─                      (Z ⇒ Z)    (Z ⇒ Z)    mark X⊑★ at Z, mark X⊑★ at Z + source rebase  (★ ⇒ ★)    (★ ⇒ ★)    │ □ ↑ unseal Y′ ⇒-rev\n" ++
    "│ ─                      (Z ⇒ Z)    (Y ⇒ Y)    Y ≈ Y, Y ≈ Y + source rebase                  (Y ⇒ Y)    (Y′ ⇒ Y′)  │ □ ↑ unseal X′ ⇒-rev\n" ++
    "│ λx. □                  (Z ⇒ Z)    (X ⇒ X)    X ≈ X, X ≈ X                                  (X ⇒ X)    (X′ ⇒ X′)  │ λx. □\n" ++
    "│ x                      Z          X          X ≈ X                                         X          X′         │ x\n" ++
    "└ □ ⟨ ℕ↦ℕ ⟩              ℕ          ℕ          ℕ⊑ℕ                                           ℕ          ℕ          └ □ ⟨ ℕ↦ℕ ⟩\n" ++
    "  7                      ℕ          ℕ          ℕ⊑ℕ                                           ℕ          ℕ            7"
checkpoint₄-ladder-pinned = refl
------------------------------------------------------------------------
-- The paired X allocation and the surviving target alias chain
------------------------------------------------------------------------

checkpoint₅-world :
  (example12-base-context ,ˢ ℕᵗ) ⊑ᶜ
    (((example12-base-context ,ˢ ★) ,ˢ ＇ Fin.zero) ,ˢ ℕᵗ)
checkpoint₅-world = bindBothStarᶜ checkpoint₁-world ℕ⊑ℕ (λ ())

checkpoint₅-source-X-member :
  store-bind store-empty ℕᵗ ∋ Fin.zero ⦂ ℕᵗ
checkpoint₅-source-X-member = Z∋ refl

checkpoint₅-target-X-member :
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) ℕᵗ
    ∋ Fin.zero ⦂ ℕᵗ
checkpoint₅-target-X-member = Z∋ refl

checkpoint₅-target-beta-member :
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) ℕᵗ
    ∋ Fin.suc Fin.zero ⦂ ＇ (Fin.suc (Fin.suc Fin.zero))
checkpoint₅-target-beta-member =
  S-bind∋ checkpoint₁-beta-member refl

checkpoint₅-target-alpha-member :
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) ℕᵗ
    ∋ Fin.suc (Fin.suc Fin.zero) ⦂ ★
checkpoint₅-target-alpha-member =
  S-bind∋ checkpoint₁-alpha-member refl

checkpoint₅-alpha-ok :
  PivotUpdateᵗ
    (ηᴸᶜ checkpoint₅-world)
    Fin.zero
    (toRenameⁱ (ηᴿᶜ checkpoint₅-world)
      (Fin.suc (Fin.suc Fin.zero)))
checkpoint₅-alpha-ok =
  repointⁱ (ηᴸᶜ checkpoint₅-world) Fin.zero
    (toRenameⁱ (ηᴿᶜ checkpoint₅-world)
      (Fin.suc (Fin.suc Fin.zero)))
    (λ ())
    (λ { Fin.zero zero≠zero eq → zero≠zero refl })

checkpoint₅-alpha-representation :
  (＇ Fin.zero) ⊑ᵀ⟨ checkpoint₅-world ⟩ ★
checkpoint₅-alpha-representation = I.X⊑★ refl

checkpoint₅-alpha-current :
  (example12-base-context ,ˢ ℕᵗ) ⊑ᶜ
    (((example12-base-context ,ˢ ★) ,ˢ ＇ Fin.zero) ,ˢ ℕᵗ)
checkpoint₅-alpha-current =
  rebaseSourceᶜ checkpoint₅-world Fin.zero
    (Fin.suc (Fin.suc Fin.zero)) checkpoint₅-alpha-ok
    open-frameᶜ
    checkpoint₅-alpha-representation

checkpoint₅-beta-ok :
  PivotUpdateᵗ
    (ηᴸᶜ checkpoint₅-alpha-current)
    Fin.zero
    (toRenameⁱ (ηᴿᶜ checkpoint₅-alpha-current)
      (Fin.suc Fin.zero))
checkpoint₅-beta-ok =
  repointⁱ (ηᴸᶜ checkpoint₅-alpha-current) Fin.zero
    (toRenameⁱ (ηᴿᶜ checkpoint₅-alpha-current)
      (Fin.suc Fin.zero))
    (λ ())
    (λ { Fin.zero zero≠zero eq → zero≠zero refl })

checkpoint₅-beta-representation :
  (＇ Fin.zero) ⊑ᵀ⟨ checkpoint₅-alpha-current ⟩
    (＇ (Fin.suc (Fin.suc Fin.zero)))
checkpoint₅-beta-representation = I.X⊑X

checkpoint₅-beta-current :
  (example12-base-context ,ˢ ℕᵗ) ⊑ᶜ
    (((example12-base-context ,ˢ ★) ,ˢ ＇ Fin.zero) ,ˢ ℕᵗ)
checkpoint₅-beta-current =
  rebaseSourceᶜ checkpoint₅-alpha-current Fin.zero
    (Fin.suc Fin.zero) checkpoint₅-beta-ok
    open-frameᶜ
    checkpoint₅-beta-representation

checkpoint₅-source-X-arrow-reveal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ]
    (seal Fin.zero ℕᵗ ↦↑ unseal Fin.zero ℕᵗ)
checkpoint₅-source-X-arrow-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-seal checkpoint₅-source-X-member)
    (Conv.⊢↑-unseal checkpoint₅-source-X-member)

checkpoint₅-target-X-arrow-reveal⊢ :
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) ℕᵗ
    Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ]
      (seal Fin.zero ℕᵗ ↦↑ unseal Fin.zero ℕᵗ)
checkpoint₅-target-X-arrow-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-seal checkpoint₅-target-X-member)
    (Conv.⊢↑-unseal checkpoint₅-target-X-member)

checkpoint₅-target-beta-arrow-reveal⊢ :
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) ℕᵗ
    Conv.⊢↑[
      Fin.suc Fin.zero ⦂ ＇ (Fin.suc (Fin.suc Fin.zero)) ]
      (seal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))) ↦↑
        unseal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))))
checkpoint₅-target-beta-arrow-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-seal checkpoint₅-target-beta-member)
    (Conv.⊢↑-unseal checkpoint₅-target-beta-member)

checkpoint₅-target-alpha-arrow-reveal⊢ :
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) ℕᵗ
    Conv.⊢↑[ Fin.suc (Fin.suc Fin.zero) ⦂ ★ ]
      (seal (Fin.suc (Fin.suc Fin.zero)) ★ ↦↑
        unseal (Fin.suc (Fin.suc Fin.zero)) ★)
checkpoint₅-target-alpha-arrow-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-seal checkpoint₅-target-alpha-member)
    (Conv.⊢↑-unseal checkpoint₅-target-alpha-member)

checkpoint₅-source-X-reveal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ]
    unseal Fin.zero ℕᵗ
checkpoint₅-source-X-reveal⊢ =
  Conv.⊢↑-unseal checkpoint₅-source-X-member

checkpoint₅-target-X-reveal⊢ :
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) ℕᵗ
    Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ] unseal Fin.zero ℕᵗ
checkpoint₅-target-X-reveal⊢ =
  Conv.⊢↑-unseal checkpoint₅-target-X-member

checkpoint₅-source-X-conceal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↓[ Fin.zero ⦂ ℕᵗ ]
    seal Fin.zero ℕᵗ
checkpoint₅-source-X-conceal⊢ =
  Conv.⊢↓-seal checkpoint₅-source-X-member

checkpoint₅-target-X-conceal⊢ :
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) ℕᵗ
    Conv.⊢↓[ Fin.zero ⦂ ℕᵗ ] seal Fin.zero ℕᵗ
checkpoint₅-target-X-conceal⊢ =
  Conv.⊢↓-seal checkpoint₅-target-X-member

checkpoint₅-alpha-active :
  revealGeneratorPosition checkpoint₅-target-alpha-arrow-reveal⊢
    ≢ generator-absent
checkpoint₅-alpha-active ()

checkpoint₅-beta-active :
  revealGeneratorPosition checkpoint₅-target-beta-arrow-reveal⊢
    ≢ generator-absent
checkpoint₅-beta-active ()

checkpoint₅-source-id-argument :
  flipᵐ (extᵐ (λ (_ : TyVar 0) → ★∼X∼★)) ⊢ ℕᵗ ∼ ℕᵗ
checkpoint₅-source-id-argument = id (‵ `ℕ)

checkpoint₅-source-id-result :
  extᵐ (λ (_ : TyVar 0) → ★∼X∼★) ⊢ ℕᵗ ∼ ℕᵗ
checkpoint₅-source-id-result = id (‵ `ℕ)

checkpoint₅-source-id-function :
  extᵐ (λ (_ : TyVar 0) → ★∼X∼★) ⊢
    (ℕᵗ ⇒ ℕᵗ) ∼ (ℕᵗ ⇒ ℕᵗ)
checkpoint₅-source-id-function =
  checkpoint₅-source-id-argument ↦ checkpoint₅-source-id-result

checkpoint₅-target-id-function :
  renameEnv∼ wk↪ᵗ
    (applyEnv (bind (＇ Fin.zero))
      (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))) ⊢
    (★ ⇒ ★) ∼ (★ ⇒ ★)
checkpoint₅-target-id-function = id ★ ↦ id ★

checkpoint₅-target-gen-function :
  genᵐ
    (applyEnv (bind (＇ Fin.zero))
      (applyEnv (bind ★) (idᶜ {Δ = 0}))) ⊢
    (★ ⇒ ★) ∼ (＇ Fin.zero ⇒ ＇ Fin.zero)
checkpoint₅-target-gen-function =
  (id { μ = flipᵐ (genᵐ
      (applyEnv (bind (＇ Fin.zero))
        (applyEnv (bind ★) (idᶜ {Δ = 0})))) }
    (＇ Fin.zero) !)
  ↦
  (？_ { μ = genᵐ
      (applyEnv (bind (＇ Fin.zero))
        (applyEnv (bind ★) (idᶜ {Δ = 0}))) }
    (id (＇ Fin.zero)))

checkpoint₅-function-payload :
  checkpoint₅-world CTI.⊢²
    C.ƛ (C.` 0) ⊑
    ((((C.ƛ (C.` 0)) C.↑
      (seal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))) ↦↑
        unseal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))))) C.↑
      (seal (Fin.suc (Fin.suc Fin.zero)) ★ ↦↑
        unseal (Fin.suc (Fin.suc Fin.zero)) ★)) C.⟨
      checkpoint₅-target-id-function ⟩) C.⟨
      checkpoint₅-target-gen-function ⟩ ∶
      I.⇒⊑⇒ I.X⊑X I.X⊑X
checkpoint₅-function-payload =
  CTI.⊑cast²
    checkpoint₅-target-gen-function
    (CTI.⊑cast²
      checkpoint₅-target-id-function
      (CTI.⊑reveal-rebase²
        checkpoint₅-target-alpha-arrow-reveal⊢
        (source-rebase-now checkpoint₅-alpha-ok
          checkpoint₅-alpha-representation)
        (CTI.⊑reveal-rebase²
          checkpoint₅-target-beta-arrow-reveal⊢
          (source-rebase-now checkpoint₅-beta-ok
            checkpoint₅-beta-representation)
          (CTI.ƛ⊑ƛ² {pA = I.X⊑X} {pB = I.X⊑X}
            (CTI.x⊑x² {p = I.X⊑X} Z Z))
          (I.⇒⊑⇒ I.X⊑X I.X⊑X))
        (I.⇒⊑⇒ (I.X⊑★ refl) (I.X⊑★ refl)))
      (I.⇒⊑⇒ (I.X⊑★ refl) (I.X⊑★ refl)))
    (I.⇒⊑⇒ I.X⊑X I.X⊑X)

checkpoint₅-function-revealed :
  checkpoint₅-world CTI.⊢²
    ((C.ƛ (C.` 0)) C.↑
      (seal Fin.zero ℕᵗ ↦↑ unseal Fin.zero ℕᵗ)) ⊑
    ((((((C.ƛ (C.` 0)) C.↑
      (seal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))) ↦↑
        unseal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))))) C.↑
      (seal (Fin.suc (Fin.suc Fin.zero)) ★ ↦↑
        unseal (Fin.suc (Fin.suc Fin.zero)) ★)) C.⟨
      checkpoint₅-target-id-function ⟩) C.⟨
      checkpoint₅-target-gen-function ⟩) C.↑
      (seal Fin.zero ℕᵗ ↦↑ unseal Fin.zero ℕᵗ)) ∶
      I.⇒⊑⇒ ℕ⊑ℕ ℕ⊑ℕ
checkpoint₅-function-revealed =
  CTI.reveal⊑reveal²
    checkpoint₅-source-X-arrow-reveal⊢
    checkpoint₅-target-X-arrow-reveal⊢
    refl
    refl
    ℕ⊑ℕ
    checkpoint₅-function-payload
    (I.⇒⊑⇒ ℕ⊑ℕ ℕ⊑ℕ)

checkpoint₅-function-single-cast :
  checkpoint₅-world CTI.⊢²
    (((C.ƛ (C.` 0)) C.↑
      (seal Fin.zero ℕᵗ ↦↑ unseal Fin.zero ℕᵗ)) C.⟨
      checkpoint₅-source-id-function ⟩) ⊑
    ((((((C.ƛ (C.` 0)) C.↑
      (seal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))) ↦↑
        unseal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))))) C.↑
      (seal (Fin.suc (Fin.suc Fin.zero)) ★ ↦↑
        unseal (Fin.suc (Fin.suc Fin.zero)) ★)) C.⟨
      checkpoint₅-target-id-function ⟩) C.⟨
      checkpoint₅-target-gen-function ⟩) C.↑
      (seal Fin.zero ℕᵗ ↦↑ unseal Fin.zero ℕᵗ)) ∶
      I.⇒⊑⇒ ℕ⊑ℕ ℕ⊑ℕ
checkpoint₅-function-single-cast =
  CTI.cast⊑² checkpoint₅-source-id-function
    checkpoint₅-function-revealed (I.⇒⊑⇒ ℕ⊑ℕ ℕ⊑ℕ)

checkpoint₅-function-double-cast :
  checkpoint₅-world CTI.⊢²
    ((((C.ƛ (C.` 0)) C.↑
      (seal Fin.zero ℕᵗ ↦↑ unseal Fin.zero ℕᵗ)) C.⟨
      checkpoint₅-source-id-function ⟩) C.⟨
      checkpoint₅-source-id-function ⟩) ⊑
    ((((((C.ƛ (C.` 0)) C.↑
      (seal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))) ↦↑
        unseal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))))) C.↑
      (seal (Fin.suc (Fin.suc Fin.zero)) ★ ↦↑
        unseal (Fin.suc (Fin.suc Fin.zero)) ★)) C.⟨
      checkpoint₅-target-id-function ⟩) C.⟨
      checkpoint₅-target-gen-function ⟩) C.↑
      (seal Fin.zero ℕᵗ ↦↑ unseal Fin.zero ℕᵗ)) ∶
      I.⇒⊑⇒ ℕ⊑ℕ ℕ⊑ℕ
checkpoint₅-function-double-cast =
  CTI.cast⊑² checkpoint₅-source-id-function
    checkpoint₅-function-single-cast
    (I.⇒⊑⇒ ℕ⊑ℕ ℕ⊑ℕ)


------------------------------------------------------------------------
-- Cast-term imprecision after the paired natural-number allocation
------------------------------------------------------------------------

checkpoint₅-imprecision :
  checkpoint₅-world CTI.⊢²
    more-checkpoint₅ ⊑ less-checkpoint₅ ∶ ℕ⊑ℕ
checkpoint₅-imprecision =
  CTI.·⊑·²
    checkpoint₅-function-double-cast
    (CTI.cast⊑cast²
      (id { μ = renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}) } (‵ `ℕ))
      (id { μ = renameEnv∼ wk↪ᵗ
        (renameEnv∼ wk↪ᵗ
          (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))) } (‵ `ℕ))
      (CTI.κ⊑κ² (κℕ 7) ℕ⊑ℕ)
      ℕ⊑ℕ)

checkpoint₅-ladder : String
checkpoint₅-ladder = impLadderDefault checkpoint₅-imprecision

checkpoint₅-ladder-pinned :
  checkpoint₅-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] X′↦ℕ │ Y: ─ ⊑[X⊑★] Y′↦＇Z′ │ Z: ─ ⊑[X⊑★] Z′↦★⟩\n" ++
    "source term              A        ηᴸA      ⊑ costs                                       ηᴿB      B          target term\n" ++
    "───────────────────────  ───────  ───────  ────────────────────────────────────────────  ───────  ─────────  ─────────────────────────\n" ++
    "□₁ · □₂                  ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          □₁ · □₂\n" ++
    "├ □ ⟨ (ℕ ⇒ ℕ)↦(ℕ ⇒ ℕ) ⟩  (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                                      (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)    ├ ─\n" ++
    "│ □ ⟨ (ℕ ⇒ ℕ)↦(ℕ ⇒ ℕ) ⟩  (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                                      (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)    │ ─\n" ++
    "│ □ ↑ unseal X ⇒-rev     (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ + matched reveal partner             (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)    │ □ ↑ unseal X′ ⇒-rev\n" ++
    "│ ─                      (X ⇒ X)  (X ⇒ X)  X ≈ X, X ≈ X                                  (X ⇒ X)  (X′ ⇒ X′)  │ □ ⟨ (★ ⇒ ★)↦(X′ ⇒ X′) ⟩\n" ++
    "│ ─                      (X ⇒ X)  (X ⇒ X)  mark X⊑★ at X, mark X⊑★ at X                  (★ ⇒ ★)  (★ ⇒ ★)    │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "│ ─                      (X ⇒ X)  (X ⇒ X)  mark X⊑★ at X, mark X⊑★ at X + source rebase  (★ ⇒ ★)  (★ ⇒ ★)    │ □ ↑ unseal Z′ ⇒-rev\n" ++
    "│ ─                      (X ⇒ X)  (Z ⇒ Z)  Z ≈ Z, Z ≈ Z + source rebase                  (Z ⇒ Z)  (Z′ ⇒ Z′)  │ □ ↑ unseal Y′ ⇒-rev\n" ++
    "│ λx. □                  (X ⇒ X)  (Y ⇒ Y)  Y ≈ Y, Y ≈ Y                                  (Y ⇒ Y)  (Y′ ⇒ Y′)  │ λx. □\n" ++
    "│ x                      X        Y        Y ≈ Y                                         Y        Y′         │ x\n" ++
    "└ □ ⟨ ℕ↦ℕ ⟩              ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          └ □ ⟨ ℕ↦ℕ ⟩\n" ++
    "  7                      ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ            7"
checkpoint₅-ladder-pinned = refl
checkpoint₆-imprecision :
  checkpoint₅-world CTI.⊢²
    more-checkpoint₆ ⊑ less-checkpoint₆ ∶ ℕ⊑ℕ
checkpoint₆-imprecision =
  CTI.·⊑·²
    checkpoint₅-function-double-cast
    (CTI.κ⊑κ² (κℕ 7) ℕ⊑ℕ)

checkpoint₆-ladder : String
checkpoint₆-ladder = impLadderDefault checkpoint₆-imprecision

checkpoint₆-ladder-pinned :
  checkpoint₆-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] X′↦ℕ │ Y: ─ ⊑[X⊑★] Y′↦＇Z′ │ Z: ─ ⊑[X⊑★] Z′↦★⟩\n" ++
    "source term              A        ηᴸA      ⊑ costs                                       ηᴿB      B          target term\n" ++
    "───────────────────────  ───────  ───────  ────────────────────────────────────────────  ───────  ─────────  ─────────────────────────\n" ++
    "□₁ · □₂                  ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          □₁ · □₂\n" ++
    "├ □ ⟨ (ℕ ⇒ ℕ)↦(ℕ ⇒ ℕ) ⟩  (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                                      (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)    ├ ─\n" ++
    "│ □ ⟨ (ℕ ⇒ ℕ)↦(ℕ ⇒ ℕ) ⟩  (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                                      (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)    │ ─\n" ++
    "│ □ ↑ unseal X ⇒-rev     (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ + matched reveal partner             (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)    │ □ ↑ unseal X′ ⇒-rev\n" ++
    "│ ─                      (X ⇒ X)  (X ⇒ X)  X ≈ X, X ≈ X                                  (X ⇒ X)  (X′ ⇒ X′)  │ □ ⟨ (★ ⇒ ★)↦(X′ ⇒ X′) ⟩\n" ++
    "│ ─                      (X ⇒ X)  (X ⇒ X)  mark X⊑★ at X, mark X⊑★ at X                  (★ ⇒ ★)  (★ ⇒ ★)    │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "│ ─                      (X ⇒ X)  (X ⇒ X)  mark X⊑★ at X, mark X⊑★ at X + source rebase  (★ ⇒ ★)  (★ ⇒ ★)    │ □ ↑ unseal Z′ ⇒-rev\n" ++
    "│ ─                      (X ⇒ X)  (Z ⇒ Z)  Z ≈ Z, Z ≈ Z + source rebase                  (Z ⇒ Z)  (Z′ ⇒ Z′)  │ □ ↑ unseal Y′ ⇒-rev\n" ++
    "│ λx. □                  (X ⇒ X)  (Y ⇒ Y)  Y ≈ Y, Y ≈ Y                                  (Y ⇒ Y)  (Y′ ⇒ Y′)  │ λx. □\n" ++
    "│ x                      X        Y        Y ≈ Y                                         Y        Y′         │ x\n" ++
    "└ 7                      ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          └ 7"
checkpoint₆-ladder-pinned = refl
checkpoint₇-imprecision :
  checkpoint₅-world CTI.⊢²
    more-checkpoint₇ ⊑ less-checkpoint₇ ∶ ℕ⊑ℕ
checkpoint₇-imprecision =
  CTI.cast⊑²
    checkpoint₅-source-id-result
    (CTI.·⊑·²
      checkpoint₅-function-single-cast
      (CTI.cast⊑²
        checkpoint₅-source-id-argument
        (CTI.κ⊑κ² (κℕ 7) ℕ⊑ℕ)
        ℕ⊑ℕ))
    ℕ⊑ℕ

checkpoint₇-ladder : String
checkpoint₇-ladder = impLadderDefault checkpoint₇-imprecision

checkpoint₇-ladder-pinned :
  checkpoint₇-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] X′↦ℕ │ Y: ─ ⊑[X⊑★] Y′↦＇Z′ │ Z: ─ ⊑[X⊑★] Z′↦★⟩\n" ++
    "source term              A        ηᴸA      ⊑ costs                                       ηᴿB      B          target term\n" ++
    "───────────────────────  ───────  ───────  ────────────────────────────────────────────  ───────  ─────────  ─────────────────────────\n" ++
    "□ ⟨ ℕ↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          ─\n" ++
    "□₁ · □₂                  ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          □₁ · □₂\n" ++
    "├ □ ⟨ (ℕ ⇒ ℕ)↦(ℕ ⇒ ℕ) ⟩  (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                                      (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)    ├ ─\n" ++
    "│ □ ↑ unseal X ⇒-rev     (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ + matched reveal partner             (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)    │ □ ↑ unseal X′ ⇒-rev\n" ++
    "│ ─                      (X ⇒ X)  (X ⇒ X)  X ≈ X, X ≈ X                                  (X ⇒ X)  (X′ ⇒ X′)  │ □ ⟨ (★ ⇒ ★)↦(X′ ⇒ X′) ⟩\n" ++
    "│ ─                      (X ⇒ X)  (X ⇒ X)  mark X⊑★ at X, mark X⊑★ at X                  (★ ⇒ ★)  (★ ⇒ ★)    │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "│ ─                      (X ⇒ X)  (X ⇒ X)  mark X⊑★ at X, mark X⊑★ at X + source rebase  (★ ⇒ ★)  (★ ⇒ ★)    │ □ ↑ unseal Z′ ⇒-rev\n" ++
    "│ ─                      (X ⇒ X)  (Z ⇒ Z)  Z ≈ Z, Z ≈ Z + source rebase                  (Z ⇒ Z)  (Z′ ⇒ Z′)  │ □ ↑ unseal Y′ ⇒-rev\n" ++
    "│ λx. □                  (X ⇒ X)  (Y ⇒ Y)  Y ≈ Y, Y ≈ Y                                  (Y ⇒ Y)  (Y′ ⇒ Y′)  │ λx. □\n" ++
    "│ x                      X        Y        Y ≈ Y                                         Y        Y′         │ x\n" ++
    "└ □ ⟨ ℕ↦ℕ ⟩              ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          └ ─\n" ++
    "  7                      ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ            7"
checkpoint₇-ladder-pinned = refl
checkpoint₈-imprecision :
  checkpoint₅-world CTI.⊢²
    more-checkpoint₈ ⊑ less-checkpoint₈ ∶ ℕ⊑ℕ
checkpoint₈-imprecision =
  CTI.cast⊑²
    checkpoint₅-source-id-result
    (CTI.·⊑·²
      checkpoint₅-function-single-cast
      (CTI.κ⊑κ² (κℕ 7) ℕ⊑ℕ))
    ℕ⊑ℕ

checkpoint₈-ladder : String
checkpoint₈-ladder = impLadderDefault checkpoint₈-imprecision

checkpoint₈-ladder-pinned :
  checkpoint₈-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] X′↦ℕ │ Y: ─ ⊑[X⊑★] Y′↦＇Z′ │ Z: ─ ⊑[X⊑★] Z′↦★⟩\n" ++
    "source term              A        ηᴸA      ⊑ costs                                       ηᴿB      B          target term\n" ++
    "───────────────────────  ───────  ───────  ────────────────────────────────────────────  ───────  ─────────  ─────────────────────────\n" ++
    "□ ⟨ ℕ↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          ─\n" ++
    "□₁ · □₂                  ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          □₁ · □₂\n" ++
    "├ □ ⟨ (ℕ ⇒ ℕ)↦(ℕ ⇒ ℕ) ⟩  (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                                      (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)    ├ ─\n" ++
    "│ □ ↑ unseal X ⇒-rev     (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ + matched reveal partner             (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)    │ □ ↑ unseal X′ ⇒-rev\n" ++
    "│ ─                      (X ⇒ X)  (X ⇒ X)  X ≈ X, X ≈ X                                  (X ⇒ X)  (X′ ⇒ X′)  │ □ ⟨ (★ ⇒ ★)↦(X′ ⇒ X′) ⟩\n" ++
    "│ ─                      (X ⇒ X)  (X ⇒ X)  mark X⊑★ at X, mark X⊑★ at X                  (★ ⇒ ★)  (★ ⇒ ★)    │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "│ ─                      (X ⇒ X)  (X ⇒ X)  mark X⊑★ at X, mark X⊑★ at X + source rebase  (★ ⇒ ★)  (★ ⇒ ★)    │ □ ↑ unseal Z′ ⇒-rev\n" ++
    "│ ─                      (X ⇒ X)  (Z ⇒ Z)  Z ≈ Z, Z ≈ Z + source rebase                  (Z ⇒ Z)  (Z′ ⇒ Z′)  │ □ ↑ unseal Y′ ⇒-rev\n" ++
    "│ λx. □                  (X ⇒ X)  (Y ⇒ Y)  Y ≈ Y, Y ≈ Y                                  (Y ⇒ Y)  (Y′ ⇒ Y′)  │ λx. □\n" ++
    "│ x                      X        Y        Y ≈ Y                                         Y        Y′         │ x\n" ++
    "└ 7                      ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          └ 7"
checkpoint₈-ladder-pinned = refl
checkpoint₉-imprecision :
  checkpoint₅-world CTI.⊢²
    more-checkpoint₉ ⊑ less-checkpoint₉ ∶ ℕ⊑ℕ
checkpoint₉-imprecision =
  CTI.cast⊑²
    checkpoint₅-source-id-result
    (CTI.cast⊑²
      checkpoint₅-source-id-result
      (CTI.·⊑·²
        checkpoint₅-function-revealed
        (CTI.cast⊑²
          checkpoint₅-source-id-argument
          (CTI.κ⊑κ² (κℕ 7) ℕ⊑ℕ)
          ℕ⊑ℕ))
      ℕ⊑ℕ)
    ℕ⊑ℕ

checkpoint₉-ladder : String
checkpoint₉-ladder = impLadderDefault checkpoint₉-imprecision

checkpoint₉-ladder-pinned :
  checkpoint₉-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] X′↦ℕ │ Y: ─ ⊑[X⊑★] Y′↦＇Z′ │ Z: ─ ⊑[X⊑★] Z′↦★⟩\n" ++
    "source term           A        ηᴸA      ⊑ costs                                       ηᴿB      B          target term\n" ++
    "────────────────────  ───────  ───────  ────────────────────────────────────────────  ───────  ─────────  ─────────────────────────\n" ++
    "□ ⟨ ℕ↦ℕ ⟩             ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          ─\n" ++
    "□ ⟨ ℕ↦ℕ ⟩             ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          ─\n" ++
    "□₁ · □₂               ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          □₁ · □₂\n" ++
    "├ □ ↑ unseal X ⇒-rev  (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ + matched reveal partner             (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)    ├ □ ↑ unseal X′ ⇒-rev\n" ++
    "│ ─                   (X ⇒ X)  (X ⇒ X)  X ≈ X, X ≈ X                                  (X ⇒ X)  (X′ ⇒ X′)  │ □ ⟨ (★ ⇒ ★)↦(X′ ⇒ X′) ⟩\n" ++
    "│ ─                   (X ⇒ X)  (X ⇒ X)  mark X⊑★ at X, mark X⊑★ at X                  (★ ⇒ ★)  (★ ⇒ ★)    │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "│ ─                   (X ⇒ X)  (X ⇒ X)  mark X⊑★ at X, mark X⊑★ at X + source rebase  (★ ⇒ ★)  (★ ⇒ ★)    │ □ ↑ unseal Z′ ⇒-rev\n" ++
    "│ ─                   (X ⇒ X)  (Z ⇒ Z)  Z ≈ Z, Z ≈ Z + source rebase                  (Z ⇒ Z)  (Z′ ⇒ Z′)  │ □ ↑ unseal Y′ ⇒-rev\n" ++
    "│ λx. □               (X ⇒ X)  (Y ⇒ Y)  Y ≈ Y, Y ≈ Y                                  (Y ⇒ Y)  (Y′ ⇒ Y′)  │ λx. □\n" ++
    "│ x                   X        Y        Y ≈ Y                                         Y        Y′         │ x\n" ++
    "└ □ ⟨ ℕ↦ℕ ⟩           ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          └ ─\n" ++
    "  7                   ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ            7"
checkpoint₉-ladder-pinned = refl
checkpoint₁₀-imprecision :
  checkpoint₅-world CTI.⊢²
    more-checkpoint₁₀ ⊑ less-checkpoint₁₀ ∶ ℕ⊑ℕ
checkpoint₁₀-imprecision =
  CTI.cast⊑²
    checkpoint₅-source-id-result
    (CTI.cast⊑²
      checkpoint₅-source-id-result
      (CTI.·⊑·²
        checkpoint₅-function-revealed
        (CTI.κ⊑κ² (κℕ 7) ℕ⊑ℕ))
      ℕ⊑ℕ)
    ℕ⊑ℕ

checkpoint₁₀-ladder : String
checkpoint₁₀-ladder = impLadderDefault checkpoint₁₀-imprecision

checkpoint₁₀-ladder-pinned :
  checkpoint₁₀-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] X′↦ℕ │ Y: ─ ⊑[X⊑★] Y′↦＇Z′ │ Z: ─ ⊑[X⊑★] Z′↦★⟩\n" ++
    "source term           A        ηᴸA      ⊑ costs                                       ηᴿB      B          target term\n" ++
    "────────────────────  ───────  ───────  ────────────────────────────────────────────  ───────  ─────────  ─────────────────────────\n" ++
    "□ ⟨ ℕ↦ℕ ⟩             ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          ─\n" ++
    "□ ⟨ ℕ↦ℕ ⟩             ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          ─\n" ++
    "□₁ · □₂               ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          □₁ · □₂\n" ++
    "├ □ ↑ unseal X ⇒-rev  (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ + matched reveal partner             (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)    ├ □ ↑ unseal X′ ⇒-rev\n" ++
    "│ ─                   (X ⇒ X)  (X ⇒ X)  X ≈ X, X ≈ X                                  (X ⇒ X)  (X′ ⇒ X′)  │ □ ⟨ (★ ⇒ ★)↦(X′ ⇒ X′) ⟩\n" ++
    "│ ─                   (X ⇒ X)  (X ⇒ X)  mark X⊑★ at X, mark X⊑★ at X                  (★ ⇒ ★)  (★ ⇒ ★)    │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "│ ─                   (X ⇒ X)  (X ⇒ X)  mark X⊑★ at X, mark X⊑★ at X + source rebase  (★ ⇒ ★)  (★ ⇒ ★)    │ □ ↑ unseal Z′ ⇒-rev\n" ++
    "│ ─                   (X ⇒ X)  (Z ⇒ Z)  Z ≈ Z, Z ≈ Z + source rebase                  (Z ⇒ Z)  (Z′ ⇒ Z′)  │ □ ↑ unseal Y′ ⇒-rev\n" ++
    "│ λx. □               (X ⇒ X)  (Y ⇒ Y)  Y ≈ Y, Y ≈ Y                                  (Y ⇒ Y)  (Y′ ⇒ Y′)  │ λx. □\n" ++
    "│ x                   X        Y        Y ≈ Y                                         Y        Y′         │ x\n" ++
    "└ 7                   ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          └ 7"
checkpoint₁₀-ladder-pinned = refl
checkpoint₁₁-imprecision :
  checkpoint₅-world CTI.⊢²
    more-checkpoint₁₁ ⊑ less-checkpoint₁₁ ∶ ℕ⊑ℕ
checkpoint₁₁-imprecision =
  CTI.cast⊑²
    checkpoint₅-source-id-result
    (CTI.cast⊑²
      checkpoint₅-source-id-result
      (CTI.reveal⊑reveal²
        checkpoint₅-source-X-reveal⊢
        checkpoint₅-target-X-reveal⊢
        refl
        refl
        ℕ⊑ℕ
        (CTI.·⊑·²
          checkpoint₅-function-payload
          (CTI.conceal⊑conceal²
            checkpoint₅-source-X-conceal⊢
            checkpoint₅-target-X-conceal⊢
            refl
            refl
            ℕ⊑ℕ
            (CTI.κ⊑κ² (κℕ 7) ℕ⊑ℕ)
            I.X⊑X))
        ℕ⊑ℕ)
      ℕ⊑ℕ)
    ℕ⊑ℕ

checkpoint₁₁-ladder : String
checkpoint₁₁-ladder = impLadderDefault checkpoint₁₁-imprecision

checkpoint₁₁-ladder-pinned :
  checkpoint₁₁-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] X′↦ℕ │ Y: ─ ⊑[X⊑★] Y′↦＇Z′ │ Z: ─ ⊑[X⊑★] Z′↦★⟩\n" ++
    "source term   A        ηᴸA      ⊑ costs                                       ηᴿB      B          target term\n" ++
    "────────────  ───────  ───────  ────────────────────────────────────────────  ───────  ─────────  ─────────────────────────\n" ++
    "□ ⟨ ℕ↦ℕ ⟩     ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          ─\n" ++
    "□ ⟨ ℕ↦ℕ ⟩     ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ          ─\n" ++
    "□ ↑ unseal X  ℕ        ℕ        ℕ⊑ℕ + matched reveal partner                  ℕ        ℕ          □ ↑ unseal X′\n" ++
    "□₁ · □₂       X        X        X ≈ X                                         X        X′         □₁ · □₂\n" ++
    "├ ─           (X ⇒ X)  (X ⇒ X)  X ≈ X, X ≈ X                                  (X ⇒ X)  (X′ ⇒ X′)  ├ □ ⟨ (★ ⇒ ★)↦(X′ ⇒ X′) ⟩\n" ++
    "│ ─           (X ⇒ X)  (X ⇒ X)  mark X⊑★ at X, mark X⊑★ at X                  (★ ⇒ ★)  (★ ⇒ ★)    │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "│ ─           (X ⇒ X)  (X ⇒ X)  mark X⊑★ at X, mark X⊑★ at X + source rebase  (★ ⇒ ★)  (★ ⇒ ★)    │ □ ↑ unseal Z′ ⇒-rev\n" ++
    "│ ─           (X ⇒ X)  (Z ⇒ Z)  Z ≈ Z, Z ≈ Z + source rebase                  (Z ⇒ Z)  (Z′ ⇒ Z′)  │ □ ↑ unseal Y′ ⇒-rev\n" ++
    "│ λx. □       (X ⇒ X)  (Y ⇒ Y)  Y ≈ Y, Y ≈ Y                                  (Y ⇒ Y)  (Y′ ⇒ Y′)  │ λx. □\n" ++
    "│ x           X        Y        Y ≈ Y                                         Y        Y′         │ x\n" ++
    "└ □ ↓ seal X  X        X        X ≈ X + matched conceal partner               X        X′         └ □ ↓ seal X′\n" ++
    "  7           ℕ        ℕ        ℕ⊑ℕ                                           ℕ        ℕ            7"
checkpoint₁₁-ladder-pinned = refl
checkpoint₅-target-beta-conceal⊢ :
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) ℕᵗ
    Conv.⊢↓[
      Fin.suc Fin.zero ⦂ ＇ (Fin.suc (Fin.suc Fin.zero)) ]
      seal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero)))
checkpoint₅-target-beta-conceal⊢ =
  Conv.⊢↓-seal checkpoint₅-target-beta-member

checkpoint₅-target-alpha-conceal⊢ :
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) ℕᵗ
    Conv.⊢↓[ Fin.suc (Fin.suc Fin.zero) ⦂ ★ ]
      seal (Fin.suc (Fin.suc Fin.zero)) ★
checkpoint₅-target-alpha-conceal⊢ =
  Conv.⊢↓-seal checkpoint₅-target-alpha-member

checkpoint₅-target-beta-reveal⊢ :
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) ℕᵗ
    Conv.⊢↑[
      Fin.suc Fin.zero ⦂ ＇ (Fin.suc (Fin.suc Fin.zero)) ]
      unseal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero)))
checkpoint₅-target-beta-reveal⊢ =
  Conv.⊢↑-unseal checkpoint₅-target-beta-member

checkpoint₅-target-alpha-reveal⊢ :
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) ℕᵗ
    Conv.⊢↑[ Fin.suc (Fin.suc Fin.zero) ⦂ ★ ]
      unseal (Fin.suc (Fin.suc Fin.zero)) ★
checkpoint₅-target-alpha-reveal⊢ =
  Conv.⊢↑-unseal checkpoint₅-target-alpha-member

checkpoint₅-beta-conceal-active :
  concealGeneratorPosition checkpoint₅-target-beta-conceal⊢
    ≢ generator-absent
checkpoint₅-beta-conceal-active ()

checkpoint₅-alpha-conceal-active :
  concealGeneratorPosition checkpoint₅-target-alpha-conceal⊢
    ≢ generator-absent
checkpoint₅-alpha-conceal-active ()

checkpoint₅-beta-reveal-active :
  revealGeneratorPosition checkpoint₅-target-beta-reveal⊢
    ≢ generator-absent
checkpoint₅-beta-reveal-active ()

checkpoint₅-alpha-reveal-active :
  revealGeneratorPosition checkpoint₅-target-alpha-reveal⊢
    ≢ generator-absent
checkpoint₅-alpha-reveal-active ()

checkpoint₅-target-X-tag :
  flipᵐ
    (genᵐ
      (applyEnv (bind (＇ Fin.zero))
        (applyEnv (bind ★) (idᶜ {Δ = 0})))) ⊢
    ＇ Fin.zero ∼ ★
checkpoint₅-target-X-tag = id (＇ Fin.zero) !

checkpoint₅-target-id-star :
  renameEnv∼ wk↪ᵗ
    (applyEnv (bind (＇ Fin.zero))
      (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))) ⊢ ★ ∼ ★
checkpoint₅-target-id-star = id ★

checkpoint₅-target-X-untag :
  genᵐ
    (applyEnv (bind (＇ Fin.zero))
      (applyEnv (bind ★) (idᶜ {Δ = 0}))) ⊢
    ★ ∼ ＇ Fin.zero
checkpoint₅-target-X-untag = ？ (id (＇ Fin.zero))

checkpoint₁₂-X-sealed :
  checkpoint₅-world CTI.⊢²
    (C.$ (κℕ 7) C.↓ seal Fin.zero ℕᵗ) ⊑
    (C.$ (κℕ 7) C.↓ seal Fin.zero ℕᵗ) ∶ I.X⊑X
checkpoint₁₂-X-sealed =
  CTI.conceal⊑conceal²
    checkpoint₅-source-X-conceal⊢
    checkpoint₅-target-X-conceal⊢
    refl
    refl
    ℕ⊑ℕ
    (CTI.κ⊑κ² (κℕ 7) ℕ⊑ℕ)
    I.X⊑X

checkpoint₁₂-X-tagged :
  checkpoint₅-world CTI.⊢²
    (C.$ (κℕ 7) C.↓ seal Fin.zero ℕᵗ) ⊑
    ((C.$ (κℕ 7) C.↓ seal Fin.zero ℕᵗ) C.⟨
      checkpoint₅-target-X-tag ⟩) ∶ I.X⊑★ refl
checkpoint₁₂-X-tagged =
  CTI.⊑cast² checkpoint₅-target-X-tag checkpoint₁₂-X-sealed
    (I.X⊑★ refl)

checkpoint₁₂-alpha-concealed :
  checkpoint₅-alpha-current CTI.⊢²
    (C.$ (κℕ 7) C.↓ seal Fin.zero ℕᵗ) ⊑
    (((C.$ (κℕ 7) C.↓ seal Fin.zero ℕᵗ) C.⟨
      checkpoint₅-target-X-tag ⟩) C.↓
      seal (Fin.suc (Fin.suc Fin.zero)) ★) ∶ I.X⊑X
checkpoint₁₂-alpha-concealed =
  CTI.⊑conceal-rebase²
    checkpoint₅-target-alpha-conceal⊢
    (source-rebase-now checkpoint₅-alpha-ok
      checkpoint₅-alpha-representation)
    checkpoint₁₂-X-tagged
    I.X⊑X

checkpoint₁₂-beta-concealed :
  checkpoint₅-beta-current CTI.⊢²
    (C.$ (κℕ 7) C.↓ seal Fin.zero ℕᵗ) ⊑
    ((((C.$ (κℕ 7) C.↓ seal Fin.zero ℕᵗ) C.⟨
      checkpoint₅-target-X-tag ⟩) C.↓
      seal (Fin.suc (Fin.suc Fin.zero)) ★) C.↓
      seal (Fin.suc Fin.zero)
        (＇ (Fin.suc (Fin.suc Fin.zero)))) ∶ I.X⊑X
checkpoint₁₂-beta-concealed =
  CTI.⊑conceal-rebase²
    checkpoint₅-target-beta-conceal⊢
    (source-rebase-now checkpoint₅-beta-ok
      checkpoint₅-beta-representation)
    checkpoint₁₂-alpha-concealed
    I.X⊑X

checkpoint₁₂-beta-revealed :
  checkpoint₅-alpha-current CTI.⊢²
    (C.$ (κℕ 7) C.↓ seal Fin.zero ℕᵗ) ⊑
    (((((C.$ (κℕ 7) C.↓ seal Fin.zero ℕᵗ) C.⟨
      checkpoint₅-target-X-tag ⟩) C.↓
      seal (Fin.suc (Fin.suc Fin.zero)) ★) C.↓
      seal (Fin.suc Fin.zero)
        (＇ (Fin.suc (Fin.suc Fin.zero)))) C.↑
      unseal (Fin.suc Fin.zero)
        (＇ (Fin.suc (Fin.suc Fin.zero)))) ∶ I.X⊑X
checkpoint₁₂-beta-revealed =
  CTI.⊑reveal-rebase²
    checkpoint₅-target-beta-reveal⊢
    (source-rebase-now checkpoint₅-beta-ok
      checkpoint₅-beta-representation)
    checkpoint₁₂-beta-concealed
    I.X⊑X

checkpoint₁₂-alpha-revealed :
  checkpoint₅-world CTI.⊢²
    (C.$ (κℕ 7) C.↓ seal Fin.zero ℕᵗ) ⊑
    ((((((C.$ (κℕ 7) C.↓ seal Fin.zero ℕᵗ) C.⟨
      checkpoint₅-target-X-tag ⟩) C.↓
      seal (Fin.suc (Fin.suc Fin.zero)) ★) C.↓
      seal (Fin.suc Fin.zero)
        (＇ (Fin.suc (Fin.suc Fin.zero)))) C.↑
      unseal (Fin.suc Fin.zero)
        (＇ (Fin.suc (Fin.suc Fin.zero)))) C.↑
      unseal (Fin.suc (Fin.suc Fin.zero)) ★) ∶ I.X⊑★ refl
checkpoint₁₂-alpha-revealed =
  CTI.⊑reveal-rebase²
    checkpoint₅-target-alpha-reveal⊢
    (source-rebase-now checkpoint₅-alpha-ok
      checkpoint₅-alpha-representation)
    checkpoint₁₂-beta-revealed
    (I.X⊑★ refl)

checkpoint₁₂-id-star :
  checkpoint₅-world CTI.⊢²
    (C.$ (κℕ 7) C.↓ seal Fin.zero ℕᵗ) ⊑
    (((((((C.$ (κℕ 7) C.↓ seal Fin.zero ℕᵗ) C.⟨
      checkpoint₅-target-X-tag ⟩) C.↓
      seal (Fin.suc (Fin.suc Fin.zero)) ★) C.↓
      seal (Fin.suc Fin.zero)
        (＇ (Fin.suc (Fin.suc Fin.zero)))) C.↑
      unseal (Fin.suc Fin.zero)
        (＇ (Fin.suc (Fin.suc Fin.zero)))) C.↑
      unseal (Fin.suc (Fin.suc Fin.zero)) ★) C.⟨
      checkpoint₅-target-id-star ⟩) ∶ I.X⊑★ refl
checkpoint₁₂-id-star =
  CTI.⊑cast² checkpoint₅-target-id-star
    checkpoint₁₂-alpha-revealed (I.X⊑★ refl)

checkpoint₁₂-X-untagged :
  checkpoint₅-world CTI.⊢²
    (C.$ (κℕ 7) C.↓ seal Fin.zero ℕᵗ) ⊑
    ((((((((C.$ (κℕ 7) C.↓ seal Fin.zero ℕᵗ) C.⟨
      checkpoint₅-target-X-tag ⟩) C.↓
      seal (Fin.suc (Fin.suc Fin.zero)) ★) C.↓
      seal (Fin.suc Fin.zero)
        (＇ (Fin.suc (Fin.suc Fin.zero)))) C.↑
      unseal (Fin.suc Fin.zero)
        (＇ (Fin.suc (Fin.suc Fin.zero)))) C.↑
      unseal (Fin.suc (Fin.suc Fin.zero)) ★) C.⟨
      checkpoint₅-target-id-star ⟩) C.⟨
      checkpoint₅-target-X-untag ⟩) ∶ I.X⊑X
checkpoint₁₂-X-untagged =
  CTI.⊑cast² checkpoint₅-target-X-untag
    checkpoint₁₂-id-star I.X⊑X

checkpoint₁₂-X-roundtrip :
  checkpoint₅-world CTI.⊢²
    ((C.$ (κℕ 7) C.↓ seal Fin.zero ℕᵗ) C.↑
      unseal Fin.zero ℕᵗ) ⊑
    (((((((((C.$ (κℕ 7) C.↓ seal Fin.zero ℕᵗ) C.⟨
      checkpoint₅-target-X-tag ⟩) C.↓
      seal (Fin.suc (Fin.suc Fin.zero)) ★) C.↓
      seal (Fin.suc Fin.zero)
        (＇ (Fin.suc (Fin.suc Fin.zero)))) C.↑
      unseal (Fin.suc Fin.zero)
        (＇ (Fin.suc (Fin.suc Fin.zero)))) C.↑
      unseal (Fin.suc (Fin.suc Fin.zero)) ★) C.⟨
      checkpoint₅-target-id-star ⟩) C.⟨
      checkpoint₅-target-X-untag ⟩) C.↑
      unseal Fin.zero ℕᵗ) ∶ ℕ⊑ℕ
checkpoint₁₂-X-roundtrip =
  CTI.reveal⊑reveal²
    checkpoint₅-source-X-reveal⊢
    checkpoint₅-target-X-reveal⊢
    refl
    refl
    ℕ⊑ℕ
    checkpoint₁₂-X-untagged
    ℕ⊑ℕ

checkpoint₁₂-imprecision :
  checkpoint₅-world CTI.⊢²
    more-checkpoint₁₂ ⊑ less-checkpoint₁₂ ∶ ℕ⊑ℕ
checkpoint₁₂-imprecision =
  CTI.cast⊑² checkpoint₅-source-id-result
    (CTI.cast⊑² checkpoint₅-source-id-result
      checkpoint₁₂-X-roundtrip ℕ⊑ℕ)
    ℕ⊑ℕ

checkpoint₁₂-ladder : String
checkpoint₁₂-ladder = impLadderDefault checkpoint₁₂-imprecision

checkpoint₁₂-ladder-pinned :
  checkpoint₁₂-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] X′↦ℕ │ Y: ─ ⊑[X⊑★] Y′↦＇Z′ │ Z: ─ ⊑[X⊑★] Z′↦★⟩\n" ++
    "source term   A  ηᴸA  ⊑ costs                          ηᴿB  B   target term\n" ++
    "────────────  ─  ───  ───────────────────────────────  ───  ──  ─────────────\n" ++
    "□ ⟨ ℕ↦ℕ ⟩     ℕ  ℕ    ℕ⊑ℕ                              ℕ    ℕ   ─\n" ++
    "□ ⟨ ℕ↦ℕ ⟩     ℕ  ℕ    ℕ⊑ℕ                              ℕ    ℕ   ─\n" ++
    "□ ↑ unseal X  ℕ  ℕ    ℕ⊑ℕ + matched reveal partner     ℕ    ℕ   □ ↑ unseal X′\n" ++
    "─             X  X    X ≈ X                            X    X′  □ ⟨ ★↦X′ ⟩\n" ++
    "─             X  X    mark X⊑★ at X                    ★    ★   □ ⟨ ★↦★ ⟩\n" ++
    "─             X  X    mark X⊑★ at X + source rebase    ★    ★   □ ↑ unseal Z′\n" ++
    "─             X  Z    Z ≈ Z + source rebase            Z    Z′  □ ↑ unseal Y′\n" ++
    "─             X  Y    Y ≈ Y + source rebase            Y    Y′  □ ↓ seal Y′\n" ++
    "─             X  Z    Z ≈ Z + source rebase            Z    Z′  □ ↓ seal Z′\n" ++
    "─             X  X    mark X⊑★ at X                    ★    ★   □ ⟨ X′↦★ ⟩\n" ++
    "□ ↓ seal X    X  X    X ≈ X + matched conceal partner  X    X′  □ ↓ seal X′\n" ++
    "7             ℕ  ℕ    ℕ⊑ℕ                              ℕ    ℕ   7"
checkpoint₁₂-ladder-pinned = refl
checkpoint₁₃-imprecision :
  checkpoint₅-world CTI.⊢²
    more-checkpoint₁₃ ⊑ less-checkpoint₁₃ ∶ ℕ⊑ℕ
checkpoint₁₃-imprecision =
  CTI.cast⊑² checkpoint₅-source-id-result
    (CTI.cast⊑² checkpoint₅-source-id-result
      (CTI.κ⊑κ² (κℕ 7) ℕ⊑ℕ) ℕ⊑ℕ)
    ℕ⊑ℕ

checkpoint₁₃-ladder : String
checkpoint₁₃-ladder = impLadderDefault checkpoint₁₃-imprecision

checkpoint₁₃-ladder-pinned :
  checkpoint₁₃-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] X′↦ℕ │ Y: ─ ⊑[X⊑★] Y′↦＇Z′ │ Z: ─ ⊑[X⊑★] Z′↦★⟩\n" ++
    "source term  A  ηᴸA  ⊑ costs  ηᴿB  B  target term\n" ++
    "───────────  ─  ───  ───────  ───  ─  ───────────\n" ++
    "□ ⟨ ℕ↦ℕ ⟩    ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  ─\n" ++
    "□ ⟨ ℕ↦ℕ ⟩    ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  ─\n" ++
    "7            ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  7"
checkpoint₁₃-ladder-pinned = refl
checkpoint₁₄-imprecision :
  checkpoint₅-world CTI.⊢²
    more-checkpoint₁₄ ⊑ less-checkpoint₁₄ ∶ ℕ⊑ℕ
checkpoint₁₄-imprecision =
  CTI.cast⊑² checkpoint₅-source-id-result
    (CTI.κ⊑κ² (κℕ 7) ℕ⊑ℕ) ℕ⊑ℕ

checkpoint₁₄-ladder : String
checkpoint₁₄-ladder = impLadderDefault checkpoint₁₄-imprecision

checkpoint₁₄-ladder-pinned :
  checkpoint₁₄-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] X′↦ℕ │ Y: ─ ⊑[X⊑★] Y′↦＇Z′ │ Z: ─ ⊑[X⊑★] Z′↦★⟩\n" ++
    "source term  A  ηᴸA  ⊑ costs  ηᴿB  B  target term\n" ++
    "───────────  ─  ───  ───────  ───  ─  ───────────\n" ++
    "□ ⟨ ℕ↦ℕ ⟩    ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  ─\n" ++
    "7            ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  7"
checkpoint₁₄-ladder-pinned = refl
checkpoint₁₅-imprecision :
  checkpoint₅-world CTI.⊢²
    more-checkpoint₁₅ ⊑ less-checkpoint₁₅ ∶ ℕ⊑ℕ
checkpoint₁₅-imprecision = CTI.κ⊑κ² (κℕ 7) ℕ⊑ℕ

checkpoint₁₅-ladder : String
checkpoint₁₅-ladder = impLadderDefault checkpoint₁₅-imprecision

checkpoint₁₅-ladder-pinned :
  checkpoint₁₅-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] X′↦ℕ │ Y: ─ ⊑[X⊑★] Y′↦＇Z′ │ Z: ─ ⊑[X⊑★] Z′↦★⟩\n" ++
    "source term  A  ηᴸA  ⊑ costs  ηᴿB  B  target term\n" ++
    "───────────  ─  ───  ───────  ───  ─  ───────────\n" ++
    "7            ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  7"
checkpoint₁₅-ladder-pinned = refl
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
