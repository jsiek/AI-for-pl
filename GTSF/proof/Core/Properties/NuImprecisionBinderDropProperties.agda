module proof.Core.Properties.NuImprecisionBinderDropProperties where

-- File Charter:
--   * Canonical unused-binder dropping and opening algebra for well-formed
--     indexed type imprecision.
--   * Drops source-only or paired binders from imprecision contexts and
--     transports derivations through the corresponding type opening.
--   * Contains no endpoint-MLB selection, term relation, or simulation result.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false)
open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_<_; zero; suc)
open import Data.Nat.Base using (z<s; s<s)
open import Relation.Binary.PropositionalEquality using (trans)

open import Types
open import ImprecisionWf
open import proof.Core.Properties.ImprecisionProperties using
  ( no-⇑ᵢ-zero-left
  ; no-⇑ᵢ-zero-right
  ; no-⇑ᵢ-zero-star
  ; no-⇑ᴸᵢ-zero-left
  ; un⇑ᵢ-ˣ∈
  ; un⇑ᵢ-★∈
  ; un⇑ᴸᵢ-ˣ∈
  ; ⇑ᵢ-ˣ∈
  ; ⇑ᵢ-★∈
  )
open import proof.Core.Properties.TypeProperties using
  (occurs-suc-var; occurs-zero-rename-ext)
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties

data DropAtᵢ : TyVar → ImpCtx → ImpCtx → Set where
  drop-zeroᵢ :
    ∀ {Φ} →
    DropAtᵢ zero (νᵢᶜ Φ) Φ

  drop-∀ᵢ :
    ∀ {k Φ Ψ} →
    DropAtᵢ k Φ Ψ →
    DropAtᵢ (suc k) (∀ᵢᶜ Φ) (∀ᵢᶜ Ψ)

  drop-νᵢ :
    ∀ {k Φ Ψ} →
    DropAtᵢ k Φ Ψ →
    DropAtᵢ (suc k) (νᵢᶜ Φ) (νᵢᶜ Ψ)

data DropBothAtᵢ : TyVar → TyVar → ImpCtx → ImpCtx → Set where
  drop-both-zeroᵢ :
    ∀ {Φ} →
    DropBothAtᵢ zero zero (∀ᵢᶜ Φ) Φ

  drop-both-∀ᵢ :
    ∀ {kᴸ kᴿ Φ Ψ} →
    DropBothAtᵢ kᴸ kᴿ Φ Ψ →
    DropBothAtᵢ (suc kᴸ) (suc kᴿ) (∀ᵢᶜ Φ) (∀ᵢᶜ Ψ)

  drop-both-νᵢ :
    ∀ {kᴸ kᴿ Φ Ψ} →
    DropBothAtᵢ kᴸ kᴿ Φ Ψ →
    DropBothAtᵢ (suc kᴸ) kᴿ (νᵢᶜ Φ) (νᵢᶜ Ψ)

removeAt-Wfᵢ :
  ∀ k {Δ X} →
  k < suc Δ →
  X < suc Δ →
  occurs k (＇ X) ≡ false →
  removeAtᵗ k X < Δ
removeAt-Wfᵢ zero {X = zero} k<Δ X<Δ ()
removeAt-Wfᵢ zero {X = suc X} k<Δ (s<s X<Δ) occ = X<Δ
removeAt-Wfᵢ (suc k) {Δ = zero} (s<s ()) X<Δ occ
removeAt-Wfᵢ (suc k) {Δ = suc Δ} {X = zero} (s<s k<Δ) X<Δ occ =
  z<s
removeAt-Wfᵢ (suc k) {Δ = suc Δ} {X = suc X} (s<s k<Δ)
    (s<s X<Δ) occ =
  s<s (removeAt-Wfᵢ k k<Δ X<Δ (trans (occurs-suc-var k X) occ))

drop-var-memberᵢ :
  ∀ {k Φ Ψ X Y} →
  DropAtᵢ k Φ Ψ →
  (X ˣ⊑ˣ Y) ∈ Φ →
  (removeAtᵗ k X ˣ⊑ˣ Y) ∈ Ψ
drop-var-memberᵢ drop-zeroᵢ (here ())
drop-var-memberᵢ {X = zero} drop-zeroᵢ (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
drop-var-memberᵢ {X = suc X} drop-zeroᵢ (there x∈) =
  un⇑ᴸᵢ-ˣ∈ x∈
drop-var-memberᵢ {X = zero} {Y = zero} (drop-∀ᵢ d) (here refl) =
  here refl
drop-var-memberᵢ {X = zero} {Y = suc Y} (drop-∀ᵢ d) (here ())
drop-var-memberᵢ {X = zero} (drop-∀ᵢ d) (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
drop-var-memberᵢ {X = suc X} {Y = zero} (drop-∀ᵢ d) (here ())
drop-var-memberᵢ {X = suc X} {Y = zero} (drop-∀ᵢ d) (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
drop-var-memberᵢ {X = suc X} {Y = suc Y} (drop-∀ᵢ d) (there x∈) =
  there (⇑ᵢ-ˣ∈ (drop-var-memberᵢ d (un⇑ᵢ-ˣ∈ x∈)))
drop-var-memberᵢ (drop-νᵢ d) (here ())
drop-var-memberᵢ {X = zero} (drop-νᵢ d) (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
drop-var-memberᵢ {X = suc X} (drop-νᵢ d) (there x∈) =
  there (⇑ᴸᵢ-ˣ∈ (drop-var-memberᵢ d (un⇑ᴸᵢ-ˣ∈ x∈)))

drop-star-memberᵢ :
  ∀ {k Φ Ψ X} →
  DropAtᵢ k Φ Ψ →
  occurs k (＇ X) ≡ false →
  (X ˣ⊑★) ∈ Φ →
  (removeAtᵗ k X ˣ⊑★) ∈ Ψ
drop-star-memberᵢ {X = zero} drop-zeroᵢ () x∈
drop-star-memberᵢ {X = suc X} drop-zeroᵢ occ (here ())
drop-star-memberᵢ {X = suc X} drop-zeroᵢ occ (there x∈) =
  un⇑ᴸᵢ-★∈ x∈
drop-star-memberᵢ (drop-∀ᵢ d) occ (here ())
drop-star-memberᵢ {X = zero} (drop-∀ᵢ d) occ (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x∈)
drop-star-memberᵢ {k = suc k} {X = suc X} (drop-∀ᵢ d) occ
    (there x∈) =
  there
    (⇑ᵢ-★∈
      (drop-star-memberᵢ d
        (trans (occurs-suc-var k X) occ)
        (un⇑ᵢ-★∈ x∈)))
drop-star-memberᵢ {X = zero} (drop-νᵢ d) occ (here refl) = here refl
drop-star-memberᵢ {X = zero} (drop-νᵢ d) occ (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star x∈)
drop-star-memberᵢ {k = suc k} {X = suc X} (drop-νᵢ d) occ
    (there x∈) =
  there
    (⇑ᴸᵢ-★∈
      (drop-star-memberᵢ d
        (trans (occurs-suc-var k X) occ)
        (un⇑ᴸᵢ-★∈ x∈)))

drop-both-var-memberᵢ :
  ∀ {kᴸ kᴿ Φ Ψ X Y} →
  DropBothAtᵢ kᴸ kᴿ Φ Ψ →
  occurs kᴸ (＇ X) ≡ false →
  occurs kᴿ (＇ Y) ≡ false →
  (X ˣ⊑ˣ Y) ∈ Φ →
  (removeAtᵗ kᴸ X ˣ⊑ˣ removeAtᵗ kᴿ Y) ∈ Ψ
drop-both-var-memberᵢ drop-both-zeroᵢ () occY (here refl)
drop-both-var-memberᵢ {X = zero} drop-both-zeroᵢ occX occY
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
drop-both-var-memberᵢ {X = suc X} {Y = zero} drop-both-zeroᵢ
    occX occY (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
drop-both-var-memberᵢ {X = suc X} {Y = suc Y} drop-both-zeroᵢ
    occX occY (there x∈) =
  un⇑ᵢ-ˣ∈ x∈
drop-both-var-memberᵢ (drop-both-∀ᵢ d) occX occY (here refl) =
  here refl
drop-both-var-memberᵢ {X = zero} (drop-both-∀ᵢ d) occX occY
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
drop-both-var-memberᵢ {X = suc X} {Y = zero} (drop-both-∀ᵢ d)
    occX occY (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
drop-both-var-memberᵢ {kᴸ = suc kᴸ} {kᴿ = suc kᴿ}
    {X = suc X} {Y = suc Y} (drop-both-∀ᵢ d) occX occY
    (there x∈) =
  there
    (⇑ᵢ-ˣ∈
      (drop-both-var-memberᵢ d
        (occurs-suc-falseᵢ kᴸ X occX)
        (occurs-suc-falseᵢ kᴿ Y occY)
        (un⇑ᵢ-ˣ∈ x∈)))
drop-both-var-memberᵢ (drop-both-νᵢ d) occX occY (here ())
drop-both-var-memberᵢ {X = zero} (drop-both-νᵢ d) occX occY
    (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
drop-both-var-memberᵢ {kᴸ = suc kᴸ} {X = suc X}
    (drop-both-νᵢ d) occX occY (there x∈) =
  there
    (⇑ᴸᵢ-ˣ∈
      (drop-both-var-memberᵢ d
        (occurs-suc-falseᵢ kᴸ X occX)
        occY
        (un⇑ᴸᵢ-ˣ∈ x∈)))

drop-both-star-memberᵢ :
  ∀ {kᴸ kᴿ Φ Ψ X} →
  DropBothAtᵢ kᴸ kᴿ Φ Ψ →
  occurs kᴸ (＇ X) ≡ false →
  (X ˣ⊑★) ∈ Φ →
  (removeAtᵗ kᴸ X ˣ⊑★) ∈ Ψ
drop-both-star-memberᵢ drop-both-zeroᵢ occX (here ())
drop-both-star-memberᵢ {X = zero} drop-both-zeroᵢ occX (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x∈)
drop-both-star-memberᵢ {X = suc X} drop-both-zeroᵢ occX (there x∈) =
  un⇑ᵢ-★∈ x∈
drop-both-star-memberᵢ (drop-both-∀ᵢ d) occX (here ())
drop-both-star-memberᵢ {X = zero} (drop-both-∀ᵢ d) occX
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x∈)
drop-both-star-memberᵢ {kᴸ = suc kᴸ} {X = suc X}
    (drop-both-∀ᵢ d) occX (there x∈) =
  there
    (⇑ᵢ-★∈
      (drop-both-star-memberᵢ d
        (occurs-suc-falseᵢ kᴸ X occX)
        (un⇑ᵢ-★∈ x∈)))
drop-both-star-memberᵢ {X = zero} (drop-both-νᵢ d) occX
    (here refl) =
  here refl
drop-both-star-memberᵢ {X = zero} (drop-both-νᵢ d) occX
    (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star x∈)
drop-both-star-memberᵢ {kᴸ = suc kᴸ} {X = suc X}
    (drop-both-νᵢ d) occX (there x∈) =
  there
    (⇑ᴸᵢ-★∈
      (drop-both-star-memberᵢ d
        (occurs-suc-falseᵢ kᴸ X occX)
        (un⇑ᴸᵢ-★∈ x∈)))

open-unused-atᵢ :
  ∀ {k Φ Ψ Δᴸ Δᴿ A B} →
  DropAtᵢ k Φ Ψ →
  k < suc Δᴸ →
  occurs k A ≡ false →
  Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Ψ ∣ Δᴸ ⊢ renameᵗ (removeAtᵗ k) A ⊑ B ⊣ Δᴿ
open-unused-atᵢ d k<Δ occ id★ = id★
open-unused-atᵢ d k<Δ occ (idˣ x∈ X<Δ Y<Δ) =
  idˣ (drop-var-memberᵢ d x∈) (removeAt-Wfᵢ _ k<Δ X<Δ occ) Y<Δ
open-unused-atᵢ d k<Δ occ idι = idι
open-unused-atᵢ d k<Δ occ (p ↦ q) =
  open-unused-atᵢ d k<Δ (∨-false-leftᵢ occ) p ↦
  open-unused-atᵢ d k<Δ (∨-false-rightᵢ occ) q
open-unused-atᵢ {k = k} d k<Δ occ (∀ⁱ p) =
  ∀ⁱ (open-unused-atᵢ
        (drop-∀ᵢ d)
        (s<s k<Δ)
        occ
        p)
open-unused-atᵢ d k<Δ occ (tag ι) = tag ι
open-unused-atᵢ d k<Δ occ (tag p ⇛ q) =
  tag (open-unused-atᵢ d k<Δ (∨-false-leftᵢ occ) p) ⇛
  open-unused-atᵢ d k<Δ (∨-false-rightᵢ occ) q
open-unused-atᵢ d k<Δ occ (tagˣ x∈ X<Δ) =
  tagˣ (drop-star-memberᵢ d occ x∈) (removeAt-Wfᵢ _ k<Δ X<Δ occ)
open-unused-atᵢ {k = k} d k<Δ occ
    (ν {A = A} safe occA p) =
  ν (renameNonVar (extᵗ (removeAtᵗ k)) safe)
    (trans (occurs-zero-rename-ext (removeAtᵗ k) A) occA)
    (open-unused-atᵢ (drop-νᵢ d) (s<s k<Δ) occ p)

open-unusedᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  occurs zero A ≡ false →
  νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A [ zero ]ᴿ ⊑ B ⊣ Δᴿ
open-unusedᵢ occ p = open-unused-atᵢ drop-zeroᵢ z<s occ p

open-unused-both-atᵢ :
  ∀ {kᴸ kᴿ Φ Ψ Δᴸ Δᴿ A B} →
  DropBothAtᵢ kᴸ kᴿ Φ Ψ →
  kᴸ < suc Δᴸ →
  kᴿ < suc Δᴿ →
  occurs kᴸ A ≡ false →
  occurs kᴿ B ≡ false →
  Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  Ψ ∣ Δᴸ
    ⊢ renameᵗ (removeAtᵗ kᴸ) A ⊑ renameᵗ (removeAtᵗ kᴿ) B
    ⊣ Δᴿ
open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ occA occB id★ = id★
open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ occA occB
    (idˣ x∈ X<Δ Y<Δ) =
  idˣ
    (drop-both-var-memberᵢ d occA occB x∈)
    (removeAt-Wfᵢ _ kᴸ<Δ X<Δ occA)
    (removeAt-Wfᵢ _ kᴿ<Δ Y<Δ occB)
open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ occA occB idι = idι
open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ occA occB (p ↦ q) =
  open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ
    (∨-false-leftᵢ occA)
    (∨-false-leftᵢ occB)
    p
  ↦
  open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ
    (∨-false-rightᵢ occA)
    (∨-false-rightᵢ occB)
    q
open-unused-both-atᵢ {kᴸ = kᴸ} {kᴿ = kᴿ} d kᴸ<Δ kᴿ<Δ
    occA occB (∀ⁱ p) =
  ∀ⁱ (open-unused-both-atᵢ
        (drop-both-∀ᵢ d)
        (s<s kᴸ<Δ)
        (s<s kᴿ<Δ)
        occA
        occB
        p)
open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ occA occB (tag ι) = tag ι
open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ occA occB (tag p ⇛ q) =
  tag
    (open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ
      (∨-false-leftᵢ occA)
      refl
      p)
  ⇛
  open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ
    (∨-false-rightᵢ occA)
    refl
    q
open-unused-both-atᵢ d kᴸ<Δ kᴿ<Δ occA occB (tagˣ x∈ X<Δ) =
  tagˣ
    (drop-both-star-memberᵢ d occA x∈)
    (removeAt-Wfᵢ _ kᴸ<Δ X<Δ occA)
open-unused-both-atᵢ {kᴸ = kᴸ} d kᴸ<Δ kᴿ<Δ occA occB
    (ν {A = A} safe occA′ p) =
  ν (renameNonVar (extᵗ (removeAtᵗ kᴸ)) safe)
    (trans (occurs-zero-rename-ext (removeAtᵗ kᴸ) A) occA′)
    (open-unused-both-atᵢ
      (drop-both-νᵢ d)
      (s<s kᴸ<Δ)
      kᴿ<Δ
      occA
      occB
      p)

open-unused-bothᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  occurs zero A ≡ false →
  occurs zero B ≡ false →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ →
  Φ ∣ Δᴸ ⊢ A [ zero ]ᴿ ⊑ B [ zero ]ᴿ ⊣ Δᴿ
open-unused-bothᵢ occA occB p =
  open-unused-both-atᵢ drop-both-zeroᵢ z<s z<s occA occB p
