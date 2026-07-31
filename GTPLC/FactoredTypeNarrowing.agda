module FactoredTypeNarrowing where

-- File Charter:
--   * Defines three-stage type narrowing between related type contexts.
--   * Factors through left narrowing, synchronized relocation, and right
--     narrowing.
--   * Keeps the two one-context mode environments and type stores explicit.
--   * Provides structural, binder, smart-extension, and generalization
--     operators for factored narrowing.

open import Data.List using (_∷_)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst)

open import Types
open import TyStore
open import Coercions
open import TypeRelocate
open import NarrowWiden using
  (_∣_∣_⊢_⦂_⊒_; _∣_∣_⊢_⊑_; _∣_∣_⊢_⊒_)
open import ImprecisionTheorems using (dualⁿ; _⨟ⁿ_)
open import proof.ImprecisionRenaming using (⇑ⁿ-ext; ⇑ⁿ-gen)
open import proof.ImprecisionModeWeakening using
  (ModeIncl; ext-inst-incl; weakenⁿ-bundle)
open import proof.ImprecisionComposition using
  (StoreIncl; weaken-storeⁿ)

------------------------------------------------------------------------
-- Factored type narrowing
------------------------------------------------------------------------

infix 4 _∣_∣_∣_∣_⊢_⊒ᶠ_
infixr 5 _⨟ᶠ_⨟ᶠ_

record _∣_∣_∣_∣_⊢_⊒ᶠ_ {Δᴸ Δᴿ}
    (μᴸ : ModeEnv) (Σᴸ : TyStore) (Φ : ImpCtx Δᴸ Δᴿ)
    (μᴿ : ModeEnv) (Σᴿ : TyStore) (A B : Ty) : Set where
  constructor _⨟ᶠ_⨟ᶠ_
  field
    {middleᴸ middleᴿ} : Ty
    leftⁿ : μᴸ ∣ Δᴸ ∣ Σᴸ ⊢ A ⊒ middleᴸ
    relocation : Φ ⊢ middleᴸ ≈ middleᴿ
    rightⁿ : μᴿ ∣ Δᴿ ∣ Σᴿ ⊢ middleᴿ ⊒ B

open _∣_∣_∣_∣_⊢_⊒ᶠ_ public

factor-src-wf : ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ A B}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ B
  → WfTy Δᴸ A
factor-src-wf ((c , c⊒) ⨟ᶠ r ⨟ᶠ q) = NarrowWiden.⊒-src-wf c⊒

factor-tgt-wf : ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ A B}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ B
  → WfTy Δᴿ B
factor-tgt-wf (p ⨟ᶠ r ⨟ᶠ (c , c⊒)) = NarrowWiden.⊒-tgt-wf c⊒

------------------------------------------------------------------------
-- Structural operators
------------------------------------------------------------------------

infixr 6 _↦ᶠ_

_↦ᶠ_ : ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ A A′ B B′}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ A′
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ B ⊒ᶠ B′
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ
      ⊢ (A ⇒ B) ⊒ᶠ (A′ ⇒ B′)
(lA ⨟ᶠ rA ⨟ᶠ qA) ↦ᶠ (lB ⨟ᶠ rB ⨟ᶠ qB)
    with dualⁿ lA | lB | dualⁿ qA | qB
... | c , c⊑ | d , d⊒ | e , e⊑ | f , f⊒ =
  (c ↦ d , c⊑ NarrowWiden.↦ d⊒) ⨟ᶠ (rA ⇒ʳ rB) ⨟ᶠ
    (e ↦ f , e⊑ NarrowWiden.↦ f⊒)

∀ᶠ_ : ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ A B}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → extᵈ μᴸ ∣ ⟰ᵗ Σᴸ ∣ bothᵢ Φ ∣ extᵈ μᴿ
      ∣ ⟰ᵗ Σᴿ
      ⊢ A ⊒ᶠ B
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ (`∀ A) ⊒ᶠ (`∀ B)
∀ᶠ ((c , c⊒) ⨟ᶠ r ⨟ᶠ (d , d⊒)) =
  (`∀ c , NarrowWiden.∀ⁿ c⊒) ⨟ᶠ ∀ʳ r ⨟ᶠ
    (`∀ d , NarrowWiden.∀ⁿ d⊒)

------------------------------------------------------------------------
-- Composition and equivalence
------------------------------------------------------------------------

infixl 6 _⨟ⁿᶠ_ _⨟ᶠⁿ_
infix 4 _≐ᶠ_

_⨟ⁿᶠ_ : ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ A B C}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → μᴸ ∣ Δᴸ ∣ Σᴸ ⊢ A ⊒ B
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ B ⊒ᶠ C
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ C
d ⨟ⁿᶠ (l ⨟ᶠ r ⨟ᶠ q) = (d ⨟ⁿ l) ⨟ᶠ r ⨟ᶠ q

_⨟ᶠⁿ_ : ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ A B C}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ B
  → μᴿ ∣ Δᴿ ∣ Σᴿ ⊢ B ⊒ C
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ C
(l ⨟ᶠ r ⨟ᶠ q) ⨟ᶠⁿ d = l ⨟ᶠ r ⨟ᶠ (q ⨟ⁿ d)

_≐ᶠ_ : ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ A B}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ B
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ B
  → Set
p ≐ᶠ q =
  (proj₁ (leftⁿ p) ≡ proj₁ (leftⁿ q))
  × (proj₁ (rightⁿ p) ≡ proj₁ (rightⁿ q))

------------------------------------------------------------------------
-- Mode and store weakening
------------------------------------------------------------------------

weaken-storeⁿ-bundle : ∀ {μ Δ Σ Π A B}
  → StoreIncl Σ Π
  → μ ∣ Δ ∣ Σ ⊢ A ⊒ B
  → μ ∣ Δ ∣ Π ⊢ A ⊒ B
weaken-storeⁿ-bundle incl (c , c⊒) = c , weaken-storeⁿ incl c⊒

weaken-modeᶠ : ∀ {Δᴸ Δᴿ μᴸ μᴸ′ μᴿ μᴿ′ Σᴸ Σᴿ A B}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → ModeIncl μᴸ μᴸ′
  → ModeIncl μᴿ μᴿ′
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ B
  → μᴸ′ ∣ Σᴸ ∣ Φ ∣ μᴿ′ ∣ Σᴿ ⊢ A ⊒ᶠ B
weaken-modeᶠ left-incl right-incl (l ⨟ᶠ r ⨟ᶠ q) =
  weakenⁿ-bundle left-incl l ⨟ᶠ r ⨟ᶠ
    weakenⁿ-bundle right-incl q

weaken-storeᶠ : ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴸ′}
    {Σᴿ Σᴿ′ A B}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → StoreIncl Σᴸ Σᴸ′
  → StoreIncl Σᴿ Σᴿ′
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ B
  → μᴸ ∣ Σᴸ′ ∣ Φ ∣ μᴿ ∣ Σᴿ′ ⊢ A ⊒ᶠ B
weaken-storeᶠ left-incl right-incl (l ⨟ᶠ r ⨟ᶠ q) =
  weaken-storeⁿ-bundle left-incl l ⨟ᶠ r ⨟ᶠ
    weaken-storeⁿ-bundle right-incl q

head-incl : ∀ {Σ X A} → StoreIncl Σ ((X , A) ∷ Σ)
head-incl X,A∈Σ = there X,A∈Σ

inst-extendᶠ : ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ Aᴸ Aᴿ A B}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → extᵈ μᴸ ∣ ⟰ᵗ Σᴸ ∣ bothᵢ Φ ∣ extᵈ μᴿ
      ∣ ⟰ᵗ Σᴿ ⊢ A ⊒ᶠ B
  → instᵈ μᴸ ∣ (zero , Aᴸ) ∷ ⟰ᵗ Σᴸ ∣ bothᵢ Φ
      ∣ instᵈ μᴿ ∣ (zero , Aᴿ) ∷ ⟰ᵗ Σᴿ ⊢ A ⊒ᶠ B
inst-extendᶠ p =
  weaken-storeᶠ head-incl head-incl
    (weaken-modeᶠ ext-inst-incl ext-inst-incl p)

head-extendᴿᶠ : ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ Aᴿ A B}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ B
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ
      ∣ (zero , Aᴿ) ∷ Σᴿ ⊢ A ⊒ᶠ B
head-extendᴿᶠ = weaken-storeᶠ (λ x → x) head-incl

------------------------------------------------------------------------
-- Binder shifts
------------------------------------------------------------------------

⇑ᶠ : ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ A B}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ B
  → extᵈ μᴸ ∣ ⟰ᵗ Σᴸ ∣ bothᵢ Φ ∣ extᵈ μᴿ
      ∣ ⟰ᵗ Σᴿ
      ⊢ ⇑ᵗ A ⊒ᶠ ⇑ᵗ B
⇑ᶠ (l ⨟ᶠ r ⨟ᶠ q) = ⇑ⁿ-ext l ⨟ᶠ ⇑ʳ r ⨟ᶠ ⇑ⁿ-ext q

⇑ᴿᶠ : ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ A B}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ B
  → μᴸ ∣ Σᴸ ∣ freshᴿ Φ ∣ genᵈ μᴿ ∣ ⟰ᵗ Σᴿ
      ⊢ A ⊒ᶠ ⇑ᵗ B
⇑ᴿᶠ (l ⨟ᶠ r ⨟ᶠ q) = l ⨟ᶠ ⇑ᴿʳ r ⨟ᶠ ⇑ⁿ-gen q

smart-⇑ᴿᶠ : ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ A B}
    {Φ : ImpCtx Δᴸ Δᴿ} {Ψ : ImpCtx Δᴸ (suc Δᴿ)}
  → SmartExtensionᵢ Φ Ψ
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ B
  → μᴸ ∣ Σᴸ ∣ Ψ ∣ genᵈ μᴿ ∣ ⟰ᵗ Σᴿ
      ⊢ A ⊒ᶠ ⇑ᵗ B
smart-⇑ᴿᶠ extension (l ⨟ᶠ r ⨟ᶠ q) =
  l ⨟ᶠ smart-⇑ᴿʳ extension r ⨟ᶠ ⇑ⁿ-gen q

smart-extendᶠ : ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ A B C}
    {Φ : ImpCtx Δᴸ Δᴿ} {Ψ : ImpCtx Δᴸ (suc Δᴿ)}
  → (extension : SmartExtensionᵢ Φ Ψ)
  → (p : μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ B)
  → genᵈ μᴿ ∣ suc Δᴿ ∣ ⟰ᵗ Σᴿ ⊢ ⇑ᵗ B ⊒ C
  → μᴸ ∣ Σᴸ ∣ Ψ ∣ genᵈ μᴿ ∣ ⟰ᵗ Σᴿ ⊢ A ⊒ᶠ C
smart-extendᶠ extension p q = smart-⇑ᴿᶠ extension p ⨟ᶠⁿ q

------------------------------------------------------------------------
-- Generalization
------------------------------------------------------------------------

narrowing-tgt-star : ∀ {μ Δ Σ c A}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ ★
  → A ≡ ★
narrowing-tgt-star (NarrowWiden.idᵃ ★ hA) = refl
narrowing-tgt-star (NarrowWiden.untag G hG allowed ())
narrowing-tgt-star
    (NarrowWiden.untag-seq G hG allowed G꞉A p A≢★) = refl

relocation-tgt-star : ∀ {Δᴸ Δᴿ A} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ A ≈ ★
  → A ≡ ★
relocation-tgt-star (idᵃ ★ ★ hA hB starᵃ) = refl

factor-right-middle-nonstar :
    ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ A B}
    {Φ : ImpCtx Δᴸ Δᴿ}
    (p : μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ A ⊒ᶠ B)
  → A ≢ ★
  → middleᴿ p ≢ ★
factor-right-middle-nonstar
    ((c , c⊒) ⨟ᶠ r ⨟ᶠ q) A≢★ middleᴿ≡★ =
  A≢★ (narrowing-tgt-star c⊒★)
  where
  middleᴸ≡★ = relocation-tgt-star
    (subst (λ C → _ ⊢ _ ≈ C) middleᴿ≡★ r)

  c⊒★ =
    subst (λ C → _ ∣ _ ∣ _ ⊢ c ⦂ _ ⊒ C) middleᴸ≡★ c⊒

genᶠ : ∀ {Δᴸ Δᴿ μᴸ μᴿ Σᴸ Σᴿ A B C}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → NonVar A
  → zero ∈ᵗ A
  → (p : μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ B ⊒ᶠ C)
  → genᵈ μᴿ ∣ suc Δᴿ ∣ ⟰ᵗ Σᴿ ⊢ ⇑ᵗ C ⊒ A
  → B ≢ ★
  → μᴸ ∣ Σᴸ ∣ Φ ∣ μᴿ ∣ Σᴿ ⊢ B ⊒ᶠ (`∀ A)
genᶠ nonvarA zero∈A p@(l ⨟ᶠ r ⨟ᶠ q) d B≢★
    with ⇑ⁿ-gen q ⨟ⁿ d
... | c , c⊒ =
  l ⨟ᶠ r ⨟ᶠ
    (gen c , NarrowWiden.gen nonvarA zero∈A (≈-tgt-wf r) c⊒
      (factor-right-middle-nonstar p B≢★))
