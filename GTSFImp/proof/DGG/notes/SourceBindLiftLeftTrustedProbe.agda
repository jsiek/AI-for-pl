{-# OPTIONS --safe #-}

module proof.DGG.notes.SourceBindLiftLeftTrustedProbe where

-- File Charter:
--   * Composes the Example 12 administrative polymorphic cast scaffold with
--     the source-only instantiation pair.
--   * Checks that the source programs are typed, GTI-related, and compile by
--     the ordinary compiler to first-order terminating programs.
--   * Probes whether call-by-value reaches a source-only allocation while the
--     already-evaluated function relation contains the one-sided Lambda and
--     source-rebase shape from Example 12.
--   * Checks that the reachable crossing is represented by a live source
--     pivot update whose post-rebase endpoint map is injective.

import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
import Data.Nat as Nat
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TermCtx using (Z; S)
open import Consistency
open import GradualTerms renaming (_∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_)
import GradualTermImprecision as GTI
import Imprecision as I
open import TyStore using (TyStore; store-empty; store-lift; store-bind)
open import CastTerms using (Term; ⟨_,_,_⟩; _⊢_⦂_)
import CastTerms as C
open import Compile using (compile)
open import Primitives using (κℕ)
open import Eval using (step?; value?)
import Reduction
open import Reduction using
  ([]; _∷_; _—→[_]_; _—↠[_]_; _—→[_]⟨_⟩_; _∎[])
import Example as Ex
import proof.DGG.OneStep as Step
open import proof.DGG.Examples.Source using (cast)
import proof.DGG.Examples.Example12 as Example12
open import proof.DGG.World

open GTI using () renaming
  (_∣_⊢ᴳ_⊑_⦂_⊑_∶_ to _∣_⊢ᴳ²_⊑_⦂_⊑_∶_)


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

ℕ⊑ℕ : ∀ {Δ} {μ : I.ImpEnv Δ} → μ I.⊢ ℕᵗ ⊑ ℕᵗ
ℕ⊑ℕ = I.ι⊑ι

ℕ⊑★ : ∀ {Δ} {μ : I.ImpEnv Δ} → μ I.⊢ ℕᵗ ⊑ ★
ℕ⊑★ = I.ι⊑★

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

ℕ⇒ℕ⊑★⇒ℕ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ (ℕᵗ ⇒ ℕᵗ) ⊑ (★ ⇒ ℕᵗ)
ℕ⇒ℕ⊑★⇒ℕ = I.⇒⊑⇒ ℕ⊑★ ℕ⊑ℕ


-- The scaffold evaluates before its argument because it is the function of
-- the outer application.  Its result is a closure; the less-precise closure
-- retains the administrative inst/gen payload in its body.
ℓ-body ℓ-inner ℓ-outer ℓ-final ℓ-arg : Label
ℓ-body = 0
ℓ-inner = 1
ℓ-outer = 2
ℓ-final = 3
ℓ-arg = 4

more-scaffold : GTerm 0
more-scaffold =
  (ƛ ∀X⇒X ⇒
    (ƛ ℕᵗ ⇒
      (((` 1) `[ ℕᵗ ]) ·[ ℓ-body ] ` 0)))
  ·[ ℓ-outer ]
  cast ℓ-inner ∀X⇒X (Λ (ƛ ＇ Fin.zero ⇒ ` 0))

less-scaffold : GTerm 0
less-scaffold =
  (ƛ ∀X⇒X ⇒
    (ƛ ★ ⇒
      (((` 1) `[ ℕᵗ ]) ·[ ℓ-body ] ` 0)))
  ·[ ℓ-outer ]
  cast ℓ-inner star⇒star (Λ (ƛ ＇ Fin.zero ⇒ ` 0))

more-argument : GTerm 0
more-argument =
  ((Λ (ƛ ＇ Fin.zero ⇒ ` 0)) `[ ℕᵗ ])
    ·[ ℓ-arg ] $ (κℕ 42)

less-argument : GTerm 0
less-argument = (ƛ ★ ⇒ ` 0) ·[ ℓ-arg ] $ (κℕ 42)

more-program : GTerm 0
more-program = more-scaffold ·[ ℓ-final ] more-argument

less-program : GTerm 0
less-program = less-scaffold ·[ ℓ-final ] less-argument

paired-less-argument : GTerm 0
paired-less-argument =
  ((Λ (ƛ ＇ Fin.zero ⇒ ` 0)) `[ ★ ])
    ·[ ℓ-arg ] $ (κℕ 42)

paired-less-program : GTerm 0
paired-less-program = less-scaffold ·[ ℓ-final ] paired-less-argument


more-scaffold-⊢ : 0 ∣ [] ⊢ᴳ more-scaffold ⦂ (ℕᵗ ⇒ ℕᵗ)
more-scaffold-⊢ =
  ⊢·
    (⊢ƛ
      (⊢ƛ
        (⊢·
          (⊢• (⊢` (S Z)))
          (⊢` Z)
          (id (‵ `ℕ)))))
    (⊢·
      (⊢ƛ (⊢` Z))
      (⊢Λ {zero∈A = X∈X⇒X}
        (ƛ ＇ Fin.zero ⇒ ` 0) (⊢ƛ (⊢` Z)))
      (∀ᶜ (id (＇ Fin.zero) ↦ id (＇ Fin.zero))))
    (∀ᶜ (id (＇ Fin.zero) ↦ id (＇ Fin.zero)))

less-scaffold-⊢ : 0 ∣ [] ⊢ᴳ less-scaffold ⦂ (★ ⇒ ℕᵗ)
less-scaffold-⊢ =
  ⊢·
    (⊢ƛ
      (⊢ƛ
        (⊢·
          (⊢• (⊢` (S Z)))
          (⊢` Z)
          ((id (‵ `ℕ)) !))))
    (⊢·
      (⊢ƛ (⊢` Z))
      (⊢Λ {zero∈A = X∈X⇒X}
        (ƛ ＇ Fin.zero ⇒ ` 0) (⊢ƛ (⊢` Z)))
      Example12.★⇒★∼∀X⇒X)
    Example12.∀X⇒X∼★⇒★

more-argument-⊢ : 0 ∣ [] ⊢ᴳ more-argument ⦂ ℕᵗ
more-argument-⊢ =
  ⊢·
    (⊢•
      (⊢Λ {zero∈A = X∈X⇒X}
        (ƛ ＇ Fin.zero ⇒ ` 0) (⊢ƛ (⊢` Z))))
    (⊢$ (κℕ 42))
    (id (‵ `ℕ))

less-argument-⊢ : 0 ∣ [] ⊢ᴳ less-argument ⦂ ★
less-argument-⊢ =
  ⊢· (⊢ƛ (⊢` Z)) (⊢$ (κℕ 42)) (？ (id (‵ `ℕ)))

more-program-⊢ : 0 ∣ [] ⊢ᴳ more-program ⦂ ℕᵗ
more-program-⊢ = ⊢· more-scaffold-⊢ more-argument-⊢ (id (‵ `ℕ))

less-program-⊢ : 0 ∣ [] ⊢ᴳ less-program ⦂ ℕᵗ
less-program-⊢ = ⊢· less-scaffold-⊢ less-argument-⊢ (id ★)

paired-less-argument-⊢ : 0 ∣ [] ⊢ᴳ paired-less-argument ⦂ ★
paired-less-argument-⊢ =
  ⊢·
    (⊢•
      (⊢Λ {zero∈A = X∈X⇒X}
        (ƛ ＇ Fin.zero ⇒ ` 0) (⊢ƛ (⊢` Z))))
    (⊢$ (κℕ 42))
    (？ (id (‵ `ℕ)))

paired-less-program-⊢ : 0 ∣ [] ⊢ᴳ paired-less-program ⦂ ℕᵗ
paired-less-program-⊢ =
  ⊢· less-scaffold-⊢ paired-less-argument-⊢ (id ★)


more-scaffold⊑less-scaffold :
  I.idᵐ ∣ [] ⊢ᴳ² more-scaffold ⊑ less-scaffold
    ⦂ (ℕᵗ ⇒ ℕᵗ) ⊑ (★ ⇒ ℕᵗ) ∶ ℕ⇒ℕ⊑★⇒ℕ
more-scaffold⊑less-scaffold =
  GTI.·⊑·ᴳ
    (GTI.ƛ⊑ƛᴳ
      {pA = ∀X⇒X⊑∀X⇒X} {pB = ℕ⇒ℕ⊑★⇒ℕ}
      (GTI.ƛ⊑ƛᴳ {pA = ℕ⊑★} {pB = ℕ⊑ℕ}
        (GTI.·⊑·ᴳ
          (GTI.[]⊑[]ᴳ
            (GTI.x⊑xᴳ (GTI.Sⁱ GTI.Zⁱ))
            ℕ⊑ℕ
            (I.⇒⊑⇒ ℕ⊑ℕ ℕ⊑ℕ))
          (GTI.x⊑xᴳ GTI.Zⁱ)
          (id (‵ `ℕ))
          ((id (‵ `ℕ)) !))))
    (GTI.·⊑·ᴳ
      {
      pA = ∀X⇒X⊑★⇒★} {pB = ∀X⇒X⊑★⇒★}
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
      Example12.∀X⇒X∼∀X⇒X Example12.★⇒★∼∀X⇒X)
    Example12.∀X⇒X∼∀X⇒X Example12.∀X⇒X∼★⇒★

more-argument⊑less-argument :
  I.idᵐ ∣ [] ⊢ᴳ² more-argument ⊑ less-argument
    ⦂ ℕᵗ ⊑ ★ ∶ ℕ⊑★
more-argument⊑less-argument =
  GTI.·⊑·ᴳ
    (GTI.[]⊑ᴳ
      (GTI.Λ⊑ᴳ nonvar-fun X∈X⇒X GTI.lift-[]
        (ƛ ＇ Fin.zero ⇒ ` 0)
        (⊢ƛ (⊢` Z))
        (GTI.ƛ⊑ƛᴳ {pA = I.X⊑★ refl} {pB = I.X⊑★ refl}
          (GTI.x⊑xᴳ GTI.Zⁱ)))
      ℕ⊑★
      (I.⇒⊑⇒ ℕ⊑★ ℕ⊑★))
    (GTI.κ⊑κᴳ (κℕ 42))
    (id (‵ `ℕ))
    (？ (id (‵ `ℕ)))

program-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ² more-program ⊑ less-program
    ⦂ ℕᵗ ⊑ ℕᵗ ∶ ℕ⊑ℕ
program-imprecision =
  GTI.·⊑·ᴳ more-scaffold⊑less-scaffold
    more-argument⊑less-argument (id (‵ `ℕ)) (id ★)

more-argument⊑paired-less-argument :
  I.idᵐ ∣ [] ⊢ᴳ² more-argument ⊑ paired-less-argument
    ⦂ ℕᵗ ⊑ ★ ∶ ℕ⊑★
more-argument⊑paired-less-argument =
  GTI.·⊑·ᴳ
    (GTI.[]⊑[]ᴳ
      (GTI.Λ⊑Λᴳ {p = X⇒X⊑X⇒X} GTI.lift-[]
        (ƛ ＇ Fin.zero ⇒ ` 0)
        (ƛ ＇ Fin.zero ⇒ ` 0)
        X∈X⇒X X∈X⇒X
        (GTI.ƛ⊑ƛᴳ {pA = I.X⊑X} {pB = I.X⊑X}
          (GTI.x⊑xᴳ GTI.Zⁱ)))
      ℕ⊑★
      (I.⇒⊑⇒ ℕ⊑★ ℕ⊑★))
    (GTI.κ⊑κᴳ (κℕ 42))
    (id (‵ `ℕ))
    (？ (id (‵ `ℕ)))

paired-program-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ² more-program ⊑ paired-less-program
    ⦂ ℕᵗ ⊑ ℕᵗ ∶ ℕ⊑ℕ
paired-program-imprecision =
  GTI.·⊑·ᴳ more-scaffold⊑less-scaffold
    more-argument⊑paired-less-argument (id (‵ `ℕ)) (id ★)


more-compiled : Term 0
more-compiled = proj₁ (compile {Σ = store-empty} more-program-⊢)

less-compiled : Term 0
less-compiled = proj₁ (compile {Σ = store-empty} less-program-⊢)

paired-less-compiled : Term 0
paired-less-compiled =
  proj₁ (compile {Σ = store-empty} paired-less-program-⊢)

more-compiled-⊢ : ⟨ 0 , store-empty , [] ⟩ ⊢ more-compiled ⦂ ℕᵗ
more-compiled-⊢ = proj₂ (compile {Σ = store-empty} more-program-⊢)

less-compiled-⊢ : ⟨ 0 , store-empty , [] ⟩ ⊢ less-compiled ⦂ ℕᵗ
less-compiled-⊢ = proj₂ (compile {Σ = store-empty} less-program-⊢)

paired-less-compiled-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ paired-less-compiled ⦂ ℕᵗ
paired-less-compiled-⊢ =
  proj₂ (compile {Σ = store-empty} paired-less-program-⊢)

more-final : Ex.evalNat Ex.gas more-compiled-⊢ ≡ just 42
more-final = refl

less-final : Ex.evalNat Ex.gas less-compiled-⊢ ≡ just 42
less-final = refl

paired-less-final :
  Ex.evalNat Ex.gas paired-less-compiled-⊢ ≡ just 42
paired-less-final = refl


-- Executable prefix on the more-precise side.  The first store-changing step
-- after the scaffold has become a function closure is the source-only
-- instantiation in `more-argument`.
more-step₀ : Step.OneStep store-empty more-compiled
more-step₀ = Step.from-just-step (step? store-empty more-compiled) refl

more-store₁ : TyStore (Step.Δ′ more-step₀)
more-store₁ = Step.store-after more-step₀

more-step₁ : Step.OneStep more-store₁ (Step.next more-step₀)
more-step₁ =
  Step.from-just-step (step? more-store₁ (Step.next more-step₀)) refl

more-store₂ : TyStore (Step.Δ′ more-step₁)
more-store₂ = Step.store-after more-step₁

more-step₂ : Step.OneStep more-store₂ (Step.next more-step₁)
more-step₂ =
  Step.from-just-step (step? more-store₂ (Step.next more-step₁)) refl

more-change₀ : Step.change more-step₀ ≡ Reduction.keep
more-change₀ = refl

more-change₁ : Step.change more-step₁ ≡ Reduction.keep
more-change₁ = refl

more-change₂ : Step.change more-step₂ ≡ Reduction.bind ℕᵗ
more-change₂ = refl


-- The target evaluates the same scaffold to a closure, first allocating the
-- dynamic representation and its alias.  Its argument then has only ordinary
-- pure reductions, so the source allocation above can be paired with target
-- stuttering.
less-step₀ : Step.OneStep store-empty less-compiled
less-step₀ = Step.from-just-step (step? store-empty less-compiled) refl

less-store₁ : TyStore (Step.Δ′ less-step₀)
less-store₁ = Step.store-after less-step₀

less-step₁ : Step.OneStep less-store₁ (Step.next less-step₀)
less-step₁ =
  Step.from-just-step (step? less-store₁ (Step.next less-step₀)) refl

less-store₂ : TyStore (Step.Δ′ less-step₁)
less-store₂ = Step.store-after less-step₁

less-step₂ : Step.OneStep less-store₂ (Step.next less-step₁)
less-step₂ =
  Step.from-just-step (step? less-store₂ (Step.next less-step₁)) refl

less-store₃ : TyStore (Step.Δ′ less-step₂)
less-store₃ = Step.store-after less-step₂

less-step₃ : Step.OneStep less-store₃ (Step.next less-step₂)
less-step₃ =
  Step.from-just-step (step? less-store₃ (Step.next less-step₂)) refl

less-store₄ : TyStore (Step.Δ′ less-step₃)
less-store₄ = Step.store-after less-step₃

less-change₀ : Step.change less-step₀ ≡ Reduction.bind ★
less-change₀ = refl

less-change₁ : Step.change less-step₁ ≡ Reduction.bind (＇ Fin.zero)
less-change₁ = refl

less-change₂ : Step.change less-step₂ ≡ Reduction.keep
less-change₂ = refl

less-change₃ : Step.change less-step₃ ≡ Reduction.keep
less-change₃ = refl


source-critical-more : Term 0
source-critical-more = Step.next more-step₁

source-critical-less : Term 2
source-critical-less = Step.next less-step₃

source-critical-more-store : more-store₂ ≡ store-empty
source-critical-more-store = refl

source-critical-less-store :
  less-store₄ ≡ store-bind (store-bind store-empty ★) (＇ Fin.zero)
source-critical-less-store = refl

more-prefix :
  more-compiled —↠[ Reduction.keep ∷ Reduction.keep ∷ [] ]
    source-critical-more
more-prefix =
  more-compiled
  —→[ Reduction.keep ]⟨ Step.reduction more-step₀ ⟩
  Step.next more-step₀
  —→[ Reduction.keep ]⟨ Step.reduction more-step₁ ⟩
  source-critical-more ∎[]

less-prefix :
  less-compiled —↠[
    Reduction.bind ★ ∷ Reduction.bind (＇ Fin.zero) ∷
    Reduction.keep ∷ Reduction.keep ∷ [] ] source-critical-less
less-prefix =
  less-compiled
  —→[ Reduction.bind ★ ]⟨ Step.reduction less-step₀ ⟩
  Step.next less-step₀
  —→[ Reduction.bind (＇ Fin.zero) ]⟨ Step.reduction less-step₁ ⟩
  Step.next less-step₁
  —→[ Reduction.keep ]⟨ Step.reduction less-step₂ ⟩
  Step.next less-step₂
  —→[ Reduction.keep ]⟨ Step.reduction less-step₃ ⟩
  source-critical-less ∎[]

source-critical-allocation :
  source-critical-more —→[ Reduction.bind ℕᵗ ] Step.next more-step₂
source-critical-allocation = Step.reduction more-step₂

source-critical-target-stutter :
  source-critical-less —↠[ [] ] source-critical-less
source-critical-target-stutter = source-critical-less ∎[]


paired-less-step₀ : Step.OneStep store-empty paired-less-compiled
paired-less-step₀ =
  Step.from-just-step (step? store-empty paired-less-compiled) refl

paired-less-store₁ : TyStore (Step.Δ′ paired-less-step₀)
paired-less-store₁ = Step.store-after paired-less-step₀

paired-less-step₁ :
  Step.OneStep paired-less-store₁ (Step.next paired-less-step₀)
paired-less-step₁ =
  Step.from-just-step
    (step? paired-less-store₁ (Step.next paired-less-step₀)) refl

paired-less-store₂ : TyStore (Step.Δ′ paired-less-step₁)
paired-less-store₂ = Step.store-after paired-less-step₁

paired-less-step₂ :
  Step.OneStep paired-less-store₂ (Step.next paired-less-step₁)
paired-less-step₂ =
  Step.from-just-step
    (step? paired-less-store₂ (Step.next paired-less-step₁)) refl

paired-less-store₃ : TyStore (Step.Δ′ paired-less-step₂)
paired-less-store₃ = Step.store-after paired-less-step₂

paired-less-step₃ :
  Step.OneStep paired-less-store₃ (Step.next paired-less-step₂)
paired-less-step₃ =
  Step.from-just-step
    (step? paired-less-store₃ (Step.next paired-less-step₂)) refl

paired-less-store₄ : TyStore (Step.Δ′ paired-less-step₃)
paired-less-store₄ = Step.store-after paired-less-step₃

paired-less-step₄ :
  Step.OneStep paired-less-store₄ (Step.next paired-less-step₃)
paired-less-step₄ =
  Step.from-just-step
    (step? paired-less-store₄ (Step.next paired-less-step₃)) refl

paired-less-change₀ :
  Step.change paired-less-step₀ ≡ Reduction.bind ★
paired-less-change₀ = refl

paired-less-change₁ :
  Step.change paired-less-step₁ ≡ Reduction.bind (＇ Fin.zero)
paired-less-change₁ = refl

paired-less-change₂ :
  Step.change paired-less-step₂ ≡ Reduction.keep
paired-less-change₂ = refl

paired-less-change₃ :
  Step.change paired-less-step₃ ≡ Reduction.keep
paired-less-change₃ = refl

paired-less-change₄ :
  Step.change paired-less-step₄ ≡ Reduction.bind ★
paired-less-change₄ = refl

paired-critical-less : Term 2
paired-critical-less = Step.next paired-less-step₃

paired-less-prefix :
  paired-less-compiled —↠[
    Reduction.bind ★ ∷ Reduction.bind (＇ Fin.zero) ∷
    Reduction.keep ∷ Reduction.keep ∷ [] ] paired-critical-less
paired-less-prefix =
  paired-less-compiled
  —→[ Reduction.bind ★ ]⟨ Step.reduction paired-less-step₀ ⟩
  Step.next paired-less-step₀
  —→[ Reduction.bind (＇ Fin.zero) ]⟨
    Step.reduction paired-less-step₁ ⟩
  Step.next paired-less-step₁
  —→[ Reduction.keep ]⟨ Step.reduction paired-less-step₂ ⟩
  Step.next paired-less-step₂
  —→[ Reduction.keep ]⟨ Step.reduction paired-less-step₃ ⟩
  paired-critical-less ∎[]

paired-critical-source-allocation :
  source-critical-more —→[ Reduction.bind ℕᵗ ] Step.next more-step₂
paired-critical-source-allocation = Step.reduction more-step₂

paired-critical-target-allocation :
  paired-critical-less —→[ Reduction.bind ★ ]
    Step.next paired-less-step₄
paired-critical-target-allocation = Step.reduction paired-less-step₄


-- Both critical crossings have the same four center variables, named in
-- center order X, Y, Z, X₁.  Before rebasing, the source endpoint images are
--
--   source X ↦ center X
--   source Y ↦ center Y
--
-- In the source-only crossing, the target images are target Z′ ↦ center Z and
-- target X₁′ ↦ center X₁.  In the paired crossing, they are target Y′ ↦ center
-- Y, target Z′ ↦ center Z, and target X₁′ ↦ center X₁.  Thus the surviving
-- target pivot is at center X₁.  The live pivot update changes only the first
-- source image:
--
--   source X ↦ center X₁
--   source Y ↦ center Y
--
-- This post-rebase map is not order preserving, but it is injective.

source-allocation-world :
  ⟨ 2 , store-lift (store-bind store-empty ℕᵗ) , [] ⟩ ⊑ᶜ
  ⟨ 2 , store-bind (store-bind store-empty ★) (＇ Fin.zero) , [] ⟩
source-allocation-world =
  liftLeftᶜ (bindLeftᶜ Example12.checkpoint₁-world ℕᵗ)

source-alpha-rebase-after-allocation :
  PivotUpdateᵗ
    (ηᴸᶜ source-allocation-world)
    Fin.zero
    (toRenameⁱ (ηᴿᶜ source-allocation-world) (Fin.suc Fin.zero))
source-alpha-rebase-after-allocation =
  repointⁱ (ηᴸᶜ source-allocation-world) Fin.zero
    (toRenameⁱ (ηᴿᶜ source-allocation-world) (Fin.suc Fin.zero))
    (λ ())
    (λ { Fin.zero zero≠zero eq → zero≠zero refl
       ; (Fin.suc Fin.zero) not-zero ()
       ; (Fin.suc (Fin.suc ())) })

source-before-X :
  toRenameⁱ (ηᴸᶜ source-allocation-world) Fin.zero ≡ Fin.zero
source-before-X = refl

source-before-Y :
  toRenameⁱ (ηᴸᶜ source-allocation-world) (Fin.suc Fin.zero)
    ≡ Fin.suc Fin.zero
source-before-Y = refl

source-after-X :
  toRenameⁱ (pivot-afterᵗ source-alpha-rebase-after-allocation) Fin.zero
    ≡ Fin.suc (Fin.suc (Fin.suc Fin.zero))
source-after-X =
  pivot-alignedᵗ source-alpha-rebase-after-allocation

source-after-Y :
  toRenameⁱ (pivot-afterᵗ source-alpha-rebase-after-allocation)
      (Fin.suc Fin.zero)
    ≡ Fin.suc Fin.zero
source-after-Y =
  off-pivot-fixedᵗ source-alpha-rebase-after-allocation
    (Fin.suc Fin.zero) (λ ())

paired-allocation-world :
  ⟨ 2 , store-lift (store-bind store-empty ℕᵗ) , [] ⟩ ⊑ᶜ
  ⟨ 3 , store-bind
      (store-bind (store-bind store-empty ★) (＇ Fin.zero)) ★ , [] ⟩
paired-allocation-world =
  liftLeftᶜ
    (bindBothStarᶜ Example12.checkpoint₁-world ℕ⊑★ (λ ()))

paired-alpha-rebase-after-allocation :
  PivotUpdateᵗ
    (ηᴸᶜ paired-allocation-world)
    Fin.zero
    (toRenameⁱ (ηᴿᶜ paired-allocation-world)
      (Fin.suc (Fin.suc Fin.zero)))
paired-alpha-rebase-after-allocation =
  repointⁱ (ηᴸᶜ paired-allocation-world) Fin.zero
    (toRenameⁱ (ηᴿᶜ paired-allocation-world)
      (Fin.suc (Fin.suc Fin.zero)))
    (λ ())
    (λ { Fin.zero zero≠zero eq → zero≠zero refl
       ; (Fin.suc Fin.zero) not-zero ()
       ; (Fin.suc (Fin.suc ())) })

paired-before-X :
  toRenameⁱ (ηᴸᶜ paired-allocation-world) Fin.zero ≡ Fin.zero
paired-before-X = refl

paired-before-Y :
  toRenameⁱ (ηᴸᶜ paired-allocation-world) (Fin.suc Fin.zero)
    ≡ Fin.suc Fin.zero
paired-before-Y = refl

paired-after-X :
  toRenameⁱ (pivot-afterᵗ paired-alpha-rebase-after-allocation) Fin.zero
    ≡ Fin.suc (Fin.suc (Fin.suc Fin.zero))
paired-after-X =
  pivot-alignedᵗ paired-alpha-rebase-after-allocation

paired-after-Y :
  toRenameⁱ (pivot-afterᵗ paired-alpha-rebase-after-allocation)
      (Fin.suc Fin.zero)
    ≡ Fin.suc Fin.zero
paired-after-Y =
  off-pivot-fixedᵗ paired-alpha-rebase-after-allocation
    (Fin.suc Fin.zero) (λ ())
