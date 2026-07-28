module proof.Quotient.NuImprecisionQuotientInstPathProperties where

-- File Charter:
--   * Proves structural inversion facts used by quotient-inst permutation
--     path semantics.
--   * Eliminates source path shapes incompatible with the source type of an
--     `inst` widening.
--   * Contains no catch-up recursion, operational simulation, or permissive
--     option.

import Coercions as C
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)
open import ForallPermutation using
  ( _≈∀_
  ; ≈∀-refl
  ; ≈∀-sym
  ; ≈∀-trans
  ; ≈∀-⇒
  ; ≈∀-∀
  ; ≈∀-swap
  )
open import ImprecisionComposition using
  ( _⊢_≈∀ˢ_
  ; source-perm-refl
  ; source-perm-sym
  ; source-perm-trans
  ; source-perm-↦
  ; source-perm-tag-⇛
  ; source-perm-∀
  ; source-perm-ν
  ; source-swap-∀∀
  ; source-swap-∀ν
  ; source-swap-ν∀
  ; source-swap-νν
  ; _↦ˢ_
  ; ∀ˢ_
  ; tag_⇛ˢ_
  ; νˢ_
  )
import NarrowWiden as NW
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; quotient-cast-widening
  ; quotient-id-widening
  )
open import Types using (TyCtx; _⇒_)
open import
  proof.WorldCoherent.Quotient.InstPath.NuImprecisionWorldCoherentQuotientRepresentativeInstPathCatchupDef
  using
  ( _↝∀_
  ; _≈∀ⁿ_
  ; element-all
  ; element-arrow-left
  ; element-arrow-right
  ; element-swap
  ; element-unswap
  ; forall-permutation-path-all
  ; forall-permutation-path-arrow-left
  ; forall-permutation-path-arrow-right
  ; forall-permutation-path-sym
  ; forall-permutation-path-trans
  ; normalize-forall-permutation
  ; path-refl
  ; path-step
  )


forall-permutation-path-length :
  ∀ {A B} →
  A ≈∀ⁿ B →
  ℕ
forall-permutation-path-length path-refl = zero
forall-permutation-path-length (path-step step rest) =
  suc (forall-permutation-path-length rest)


forall-permutation-path-trans-length :
  ∀ {A B C}
    (left : A ≈∀ⁿ B)
    (right : B ≈∀ⁿ C) →
  forall-permutation-path-length
      (forall-permutation-path-trans left right)
    ≡ forall-permutation-path-length left +
      forall-permutation-path-length right
forall-permutation-path-trans-length path-refl right = refl
forall-permutation-path-trans-length
    (path-step step rest) right =
  cong suc (forall-permutation-path-trans-length rest right)


forall-permutation-path-sym-length :
  ∀ {A B}
    (path : A ≈∀ⁿ B) →
  forall-permutation-path-length
      (forall-permutation-path-sym path)
    ≡ forall-permutation-path-length path
forall-permutation-path-sym-length path-refl = refl
forall-permutation-path-sym-length (path-step step rest) =
  trans
    (forall-permutation-path-trans-length
      (forall-permutation-path-sym rest)
      (path-step _ path-refl))
    (trans
      (cong (_+ 1)
        (forall-permutation-path-sym-length rest))
      (plus-one
        (forall-permutation-path-length rest)))
  where
  plus-one : ∀ n → n + 1 ≡ suc n
  plus-one zero = refl
  plus-one (suc n) = cong suc (plus-one n)


forall-permutation-path-arrow-left-length :
  ∀ {A A′ B}
    (path : A ≈∀ⁿ A′) →
  forall-permutation-path-length
      (forall-permutation-path-arrow-left {B = B} path)
    ≡ forall-permutation-path-length path
forall-permutation-path-arrow-left-length path-refl = refl
forall-permutation-path-arrow-left-length
    (path-step step rest) =
  cong suc (forall-permutation-path-arrow-left-length rest)


forall-permutation-path-arrow-right-length :
  ∀ {A B B′}
    (path : B ≈∀ⁿ B′) →
  forall-permutation-path-length
      (forall-permutation-path-arrow-right {A = A} path)
    ≡ forall-permutation-path-length path
forall-permutation-path-arrow-right-length path-refl = refl
forall-permutation-path-arrow-right-length
    (path-step step rest) =
  cong suc (forall-permutation-path-arrow-right-length rest)


forall-permutation-path-all-length :
  ∀ {A B}
    (path : A ≈∀ⁿ B) →
  forall-permutation-path-length
      (forall-permutation-path-all path)
    ≡ forall-permutation-path-length path
forall-permutation-path-all-length path-refl = refl
forall-permutation-path-all-length (path-step step rest) =
  cong suc (forall-permutation-path-all-length rest)


forall-permutation-cost :
  ∀ {A B} →
  A ≈∀ B →
  ℕ
forall-permutation-cost ≈∀-refl = zero
forall-permutation-cost (≈∀-sym A≈B) =
  forall-permutation-cost A≈B
forall-permutation-cost (≈∀-trans A≈B B≈C) =
  forall-permutation-cost A≈B +
    forall-permutation-cost B≈C
forall-permutation-cost (≈∀-⇒ A≈A′ B≈B′) =
  forall-permutation-cost A≈A′ +
    forall-permutation-cost B≈B′
forall-permutation-cost (≈∀-∀ A≈B) =
  forall-permutation-cost A≈B
forall-permutation-cost ≈∀-swap = 1


normalize-forall-permutation-length :
  ∀ {A B}
    (permutation : A ≈∀ B) →
  forall-permutation-path-length
      (normalize-forall-permutation permutation)
    ≡ forall-permutation-cost permutation
normalize-forall-permutation-length ≈∀-refl = refl
normalize-forall-permutation-length (≈∀-sym A≈B) =
  trans
    (forall-permutation-path-sym-length
      (normalize-forall-permutation A≈B))
    (normalize-forall-permutation-length A≈B)
normalize-forall-permutation-length
    (≈∀-trans A≈B B≈C) =
  trans
    (forall-permutation-path-trans-length
      (normalize-forall-permutation A≈B)
      (normalize-forall-permutation B≈C))
    (cong₂ _+_
      (normalize-forall-permutation-length A≈B)
      (normalize-forall-permutation-length B≈C))
normalize-forall-permutation-length
    (≈∀-⇒ A≈A′ B≈B′) =
  trans
    (forall-permutation-path-trans-length
      (forall-permutation-path-arrow-left
        (normalize-forall-permutation A≈A′))
      (forall-permutation-path-arrow-right
        (normalize-forall-permutation B≈B′)))
    (cong₂ _+_
      (trans
        (forall-permutation-path-arrow-left-length
          (normalize-forall-permutation A≈A′))
        (normalize-forall-permutation-length A≈A′))
      (trans
        (forall-permutation-path-arrow-right-length
          (normalize-forall-permutation B≈B′))
        (normalize-forall-permutation-length B≈B′)))
normalize-forall-permutation-length (≈∀-∀ A≈B) =
  trans
    (forall-permutation-path-all-length
      (normalize-forall-permutation A≈B))
    (normalize-forall-permutation-length A≈B)
normalize-forall-permutation-length ≈∀-swap = refl


sum-zero-left :
  ∀ m n →
  m + n ≡ zero →
  m ≡ zero
sum-zero-left zero n eq = refl
sum-zero-left (suc m) n ()


sum-zero-right :
  ∀ m n →
  m + n ≡ zero →
  n ≡ zero
sum-zero-right zero n eq = eq
sum-zero-right (suc m) n ()


source-permutation-shape-equal-at-zero :
  ∀ {A B s s′}
    {permutation : A ≈∀ B} →
  forall-permutation-cost permutation ≡ zero →
  permutation ⊢ s ≈∀ˢ s′ →
  s ≡ s′
source-permutation-shape-equal-at-zero
    eq source-perm-refl =
  refl
source-permutation-shape-equal-at-zero
    eq (source-perm-sym shape) =
  sym (source-permutation-shape-equal-at-zero eq shape)
source-permutation-shape-equal-at-zero
    {permutation = ≈∀-trans left right}
    eq (source-perm-trans left-shape right-shape) =
  trans
    (source-permutation-shape-equal-at-zero
      (sum-zero-left
        (forall-permutation-cost left)
        (forall-permutation-cost right) eq)
      left-shape)
    (source-permutation-shape-equal-at-zero
      (sum-zero-right
        (forall-permutation-cost left)
        (forall-permutation-cost right) eq)
      right-shape)
source-permutation-shape-equal-at-zero
    {permutation = ≈∀-⇒ left right}
    eq (source-perm-↦ domain codomain) =
  cong₂ _↦ˢ_
    (source-permutation-shape-equal-at-zero
      (sum-zero-left
        (forall-permutation-cost left)
        (forall-permutation-cost right) eq)
      domain)
    (source-permutation-shape-equal-at-zero
      (sum-zero-right
        (forall-permutation-cost left)
        (forall-permutation-cost right) eq)
      codomain)
source-permutation-shape-equal-at-zero
    {permutation = ≈∀-⇒ left right}
    eq (source-perm-tag-⇛ domain codomain) =
  cong₂ tag_⇛ˢ_
    (source-permutation-shape-equal-at-zero
      (sum-zero-left
        (forall-permutation-cost left)
        (forall-permutation-cost right) eq)
      domain)
    (source-permutation-shape-equal-at-zero
      (sum-zero-right
        (forall-permutation-cost left)
        (forall-permutation-cost right) eq)
      codomain)
source-permutation-shape-equal-at-zero
    eq (source-perm-∀ shape) =
  cong ∀ˢ_
    (source-permutation-shape-equal-at-zero eq shape)
source-permutation-shape-equal-at-zero
    eq (source-perm-ν shape) =
  cong νˢ_
    (source-permutation-shape-equal-at-zero eq shape)
source-permutation-shape-equal-at-zero
    () source-swap-∀∀
source-permutation-shape-equal-at-zero
    () source-swap-∀ν
source-permutation-shape-equal-at-zero
    () source-swap-ν∀
source-permutation-shape-equal-at-zero
    () source-swap-νν


normalized-path-refl-source-permutation-shape-equal :
  ∀ {A s s′}
    {permutation : A ≈∀ A} →
  normalize-forall-permutation permutation ≡ path-refl →
  permutation ⊢ s ≈∀ˢ s′ →
  s ≡ s′
normalized-path-refl-source-permutation-shape-equal
    {permutation = permutation} normalized shape =
  source-permutation-shape-equal-at-zero
    (trans
      (sym (normalize-forall-permutation-length permutation))
      (cong forall-permutation-path-length normalized))
    shape


source-inst-widening-arrow⊥ :
  ∀ {Φ Δᴸ Δᴿ B s u′ X Y D′ A A′}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (C.inst B s) u′ (X ⇒ Y) D′ A A′ →
  ⊥
source-inst-widening-arrow⊥
    (quotient-id-widening (() , uʷ) u′⊑)
source-inst-widening-arrow⊥
    (quotient-cast-widening mode seal★ (() , uʷ)
      mode′ seal★′ u′⊑)


data SourceInstStepView : ∀ {D E} → D ↝∀ E → Set where
  source-step-swap :
    ∀ {A} →
    SourceInstStepView (element-swap {A = A})

  source-step-unswap :
    ∀ {A} →
    SourceInstStepView (element-unswap {A = A})

  source-step-all :
    ∀ {A B} (step : A ↝∀ B) →
    SourceInstStepView (element-all step)


source-inst-step-view :
  ∀ {Φ Δᴸ Δᴿ B s u′ D E D′ A A′}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (step : D ↝∀ E) →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (C.inst B s) u′ D D′ A A′ →
  SourceInstStepView step
source-inst-step-view element-swap widening = source-step-swap
source-inst-step-view element-unswap widening = source-step-unswap
source-inst-step-view (element-arrow-left step) widening =
  ⊥-elim (source-inst-widening-arrow⊥ widening)
source-inst-step-view (element-arrow-right step) widening =
  ⊥-elim (source-inst-widening-arrow⊥ widening)
source-inst-step-view (element-all step) widening =
  source-step-all step
