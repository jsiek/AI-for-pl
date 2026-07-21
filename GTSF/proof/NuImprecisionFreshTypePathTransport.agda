module proof.NuImprecisionFreshTypePathTransport where

-- File Charter:
--   * Proves inverse transport of proof-relevant variable paths through type
--     renaming and excludes free variable zero from a uniformly shifted type.
--   * Proves that single-name reveal and conceal conversions under one
--     binder preserve every path to the fresh bound variable, in both
--     directions.
--   * Contains no paired conversion, type-imprecision square, postulate,
--     hole, permissive option, handler import, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; conceal-all
  ; conceal-fun
  ; conceal-id-base
  ; conceal-id-var
  ; conceal-id-★
  ; conceal-seal
  ; reveal-all
  ; reveal-fun
  ; reveal-id-base
  ; reveal-id-var
  ; reveal-id-★
  ; reveal-unseal
  )
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≢_; subst)
import Types
open import Types using (Renameᵗ; Ty; extᵗ; renameᵗ; ⇑ᵗ)
open import proof.NuImprecisionFreshTypePath using
  ( TypePath
  ; VarAtPath
  ; at-body
  ; at-codomain
  ; at-domain
  ; at-here
  )


var-at-path-rename-inverse :
  ∀ {ρ : Renameᵗ} {X p A} →
  VarAtPath X p (renameᵗ ρ A) →
  ∃[ Y ] (ρ Y ≡ X) × VarAtPath Y p A
var-at-path-rename-inverse {A = Types.＇ Y} at-here =
  Y , refl , at-here
var-at-path-rename-inverse {A = Types.‵ ι} ()
var-at-path-rename-inverse {A = Types.★} ()
var-at-path-rename-inverse {A = A Types.⇒ B}
    (at-domain x-at) =
  let Y , eq , y-at = var-at-path-rename-inverse x-at in
  Y , eq , at-domain y-at
var-at-path-rename-inverse {A = A Types.⇒ B}
    (at-codomain x-at) =
  let Y , eq , y-at = var-at-path-rename-inverse x-at in
  Y , eq , at-codomain y-at
var-at-path-rename-inverse {ρ = ρ} {A = Types.`∀ A}
    (at-body x-at)
    with var-at-path-rename-inverse x-at
var-at-path-rename-inverse {ρ = ρ} {A = Types.`∀ A}
    (at-body x-at) | zero , () , zero-at
var-at-path-rename-inverse {ρ = ρ} {A = Types.`∀ A}
    (at-body x-at) | suc Y , eq , suc-y-at =
  Y , suc-injective eq , at-body suc-y-at


NoVarAtPath : Data.Nat.ℕ → Ty → Set
NoVarAtPath X A = ∀ p → VarAtPath X p A → ⊥


no-var-at-path-shift :
  ∀ {X A} →
  NoVarAtPath X A →
  NoVarAtPath (suc X) (⇑ᵗ A)
no-var-at-path-shift noX p x-at
    with var-at-path-rename-inverse x-at
no-var-at-path-shift noX p x-at | Y , eq , y-at =
  noX p (subst (λ Z → VarAtPath Z p _) (suc-injective eq) y-at)


zero-not-at-path-shift :
  ∀ {A} →
  NoVarAtPath zero (⇑ᵗ A)
zero-not-at-path-shift p x-at
    with var-at-path-rename-inverse x-at
zero-not-at-path-shift p x-at | Y , () , y-at


mutual
  reveal-path-forward :
    ∀ {μ Δ Σ α C c A B X p} →
    RevealConversion μ Δ Σ α C c A B →
    X ≢ α →
    NoVarAtPath X C →
    VarAtPath X p A →
    VarAtPath X p B
  reveal-path-forward (reveal-id-var hY ok) X≢α noX x-at = x-at
  reveal-path-forward reveal-id-base X≢α noX ()
  reveal-path-forward reveal-id-★ X≢α noX ()
  reveal-path-forward (reveal-unseal hC α∈ ok) X≢α noX at-here =
    ⊥-elim (X≢α refl)
  reveal-path-forward (reveal-fun s↓ t↑) X≢α noX
      (at-domain x-at) =
    at-domain (conceal-path-backward s↓ X≢α noX x-at)
  reveal-path-forward (reveal-fun s↓ t↑) X≢α noX
      (at-codomain x-at) =
    at-codomain (reveal-path-forward t↑ X≢α noX x-at)
  reveal-path-forward (reveal-all s↑) X≢α noX
      (at-body x-at) =
    at-body
      (reveal-path-forward s↑
        (λ eq → X≢α (suc-injective eq))
        (no-var-at-path-shift noX) x-at)

  reveal-path-backward :
    ∀ {μ Δ Σ α C c A B X p} →
    RevealConversion μ Δ Σ α C c A B →
    X ≢ α →
    NoVarAtPath X C →
    VarAtPath X p B →
    VarAtPath X p A
  reveal-path-backward (reveal-id-var hY ok) X≢α noX x-at = x-at
  reveal-path-backward reveal-id-base X≢α noX ()
  reveal-path-backward reveal-id-★ X≢α noX ()
  reveal-path-backward (reveal-unseal hC α∈ ok) X≢α noX x-at =
    ⊥-elim (noX _ x-at)
  reveal-path-backward (reveal-fun s↓ t↑) X≢α noX
      (at-domain x-at) =
    at-domain (conceal-path-forward s↓ X≢α noX x-at)
  reveal-path-backward (reveal-fun s↓ t↑) X≢α noX
      (at-codomain x-at) =
    at-codomain (reveal-path-backward t↑ X≢α noX x-at)
  reveal-path-backward (reveal-all s↑) X≢α noX
      (at-body x-at) =
    at-body
      (reveal-path-backward s↑
        (λ eq → X≢α (suc-injective eq))
        (no-var-at-path-shift noX) x-at)

  conceal-path-forward :
    ∀ {μ Δ Σ α C c A B X p} →
    ConcealConversion μ Δ Σ α C c A B →
    X ≢ α →
    NoVarAtPath X C →
    VarAtPath X p A →
    VarAtPath X p B
  conceal-path-forward (conceal-id-var hY ok) X≢α noX x-at = x-at
  conceal-path-forward conceal-id-base X≢α noX ()
  conceal-path-forward conceal-id-★ X≢α noX ()
  conceal-path-forward (conceal-seal hC α∈ ok) X≢α noX x-at =
    ⊥-elim (noX _ x-at)
  conceal-path-forward (conceal-fun s↑ t↓) X≢α noX
      (at-domain x-at) =
    at-domain (reveal-path-backward s↑ X≢α noX x-at)
  conceal-path-forward (conceal-fun s↑ t↓) X≢α noX
      (at-codomain x-at) =
    at-codomain (conceal-path-forward t↓ X≢α noX x-at)
  conceal-path-forward (conceal-all s↓) X≢α noX
      (at-body x-at) =
    at-body
      (conceal-path-forward s↓
        (λ eq → X≢α (suc-injective eq))
        (no-var-at-path-shift noX) x-at)

  conceal-path-backward :
    ∀ {μ Δ Σ α C c A B X p} →
    ConcealConversion μ Δ Σ α C c A B →
    X ≢ α →
    NoVarAtPath X C →
    VarAtPath X p B →
    VarAtPath X p A
  conceal-path-backward (conceal-id-var hY ok) X≢α noX x-at = x-at
  conceal-path-backward conceal-id-base X≢α noX ()
  conceal-path-backward conceal-id-★ X≢α noX ()
  conceal-path-backward (conceal-seal hC α∈ ok) X≢α noX at-here =
    ⊥-elim (X≢α refl)
  conceal-path-backward (conceal-fun s↑ t↓) X≢α noX
      (at-domain x-at) =
    at-domain (reveal-path-forward s↑ X≢α noX x-at)
  conceal-path-backward (conceal-fun s↑ t↓) X≢α noX
      (at-codomain x-at) =
    at-codomain (conceal-path-backward t↓ X≢α noX x-at)
  conceal-path-backward (conceal-all s↓) X≢α noX
      (at-body x-at) =
    at-body
      (conceal-path-backward s↓
        (λ eq → X≢α (suc-injective eq))
        (no-var-at-path-shift noX) x-at)


reveal-fresh-path-forward :
  ∀ {μ Δ Σ α C c A B p} →
  RevealConversion (Coercions.extᵈ μ) (suc Δ)
    (Types.⟰ᵗ Σ) (suc α) (⇑ᵗ C) c A B →
  VarAtPath zero p A →
  VarAtPath zero p B
reveal-fresh-path-forward conversion =
  reveal-path-forward conversion (λ ()) zero-not-at-path-shift


reveal-fresh-path-backward :
  ∀ {μ Δ Σ α C c A B p} →
  RevealConversion (Coercions.extᵈ μ) (suc Δ)
    (Types.⟰ᵗ Σ) (suc α) (⇑ᵗ C) c A B →
  VarAtPath zero p B →
  VarAtPath zero p A
reveal-fresh-path-backward conversion =
  reveal-path-backward conversion (λ ()) zero-not-at-path-shift


conceal-fresh-path-forward :
  ∀ {μ Δ Σ α C c A B p} →
  ConcealConversion (Coercions.extᵈ μ) (suc Δ)
    (Types.⟰ᵗ Σ) (suc α) (⇑ᵗ C) c A B →
  VarAtPath zero p A →
  VarAtPath zero p B
conceal-fresh-path-forward conversion =
  conceal-path-forward conversion (λ ()) zero-not-at-path-shift


conceal-fresh-path-backward :
  ∀ {μ Δ Σ α C c A B p} →
  ConcealConversion (Coercions.extᵈ μ) (suc Δ)
    (Types.⟰ᵗ Σ) (suc α) (⇑ᵗ C) c A B →
  VarAtPath zero p B →
  VarAtPath zero p A
conceal-fresh-path-backward conversion =
  conceal-path-backward conversion (λ ()) zero-not-at-path-shift
