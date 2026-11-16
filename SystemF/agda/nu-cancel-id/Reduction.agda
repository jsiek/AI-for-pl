module nu-cancel-id.Reduction where

-- File Charter:
--   * VALUES AND SMALL-STEP REDUCTION of νF₁ᶜ (notes/CancelIdSketch.md
--     §8 in strong-rep-nu, the named-type version).
--   * §1 values, split by the type they can have: `Fun` (arrow or `∀`
--     type), `Sealed` (a seal under reveal layers carrying `idᶜ`:
--     variable type), and constants.  An `idᶜ` layer that hides is a
--     value only over a `Fun`, and never as the outer half of a
--     CancelId pair.
--   * §2 shifting for allocation (by `renameʳ`, which moves only the
--     cells named by boundaries), §3 TyBeta's instantiation `_•⟶_`, §4
--     the step relation, §5 runs.  Beta's `N [ W ]` is single
--     substitution, derived from parallel substitution in
--     nu-cancel-id.TermSubst.
--   * A step records what it allocates (`Alloc`): TyBeta allocates one
--     unnamed cell at the head of the store, and every sibling of the
--     redex shifts (`↑ᵃ`).

open import Data.Bool using (false)
open import Data.List using (_∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)
open import Data.Product using (∃-syntax)

open import nu-cancel-id.Types
open import nu-cancel-id.Ctx
open import nu-cancel-id.Terms
open import nu-cancel-id.TermSubst public
  using (renameʳ; crossΛ; substᵐ; _[_];
         Hit; hit; miss; sucHit; hitVar; fromHit)

private
  variable
    Γ : Ctx
    s : Sign
    α β : ℕ
    A P : Ty
    c d : Conv
    k : Const
    L L′ M M′ N V W F : Term

------------------------------------------------------------------------
-- 1. Values
------------------------------------------------------------------------

data Value : Term → Set
data Fun : Term → Set
data Sealed : Term → Set

data Fun where
  F-ƛ   : Fun (ƛ A ∙ N)
  F-Λ   : Fun (Λ N)
  F-↦   : Value V → Fun ([ s , α ] V ⟨ c ↦ d ⟩)
  F-∀   : Value V → Fun ([ s , α ] V ⟨ ∀ᶜ c ⟩)
  F-id⁺ : Fun F → Fun ([ ⁺ , α ] F ⟨ idᶜ ⟩)
  -- not the left-hand side of CancelId
  F-id⁻ : Fun F → (∀ {F′} → ¬ (F ≡ [ ⁺ , α ] F′ ⟨ idᶜ ⟩))
    → Fun ([ ⁻ , α ] F ⟨ idᶜ ⟩)

-- a seal, under any number of reveal layers carrying `idᶜ`
data Sealed where
  S-seal : Value W → Sealed ([ ⁻ , α ] W ⟨ seal ⟩)
  S-rev  : Sealed V → Sealed ([ ⁺ , α ] V ⟨ idᶜ ⟩)

data Value where
  V-$      : Value ($ k)
  V-fun    : Fun V → Value V
  V-sealed : Sealed V → Value V

------------------------------------------------------------------------
-- 2. Allocation.  Every sibling of the redex shifts past the new cell.
------------------------------------------------------------------------

data Alloc : Set where
  keep : Alloc
  new  : Ty → Alloc

-- the context after a step
infixr 5 _⨾_
_⨾_ : Alloc → Ctx → Ctx
keep  ⨾ Γ = Γ
new P ⨾ Γ = (pay P ∷ store Γ) ∣ (false ∷ flags Γ)

↑ᵃ : Alloc → Term → Term
↑ᵃ keep    M = M
↑ᵃ (new P) M = renameʳ suc M

↑ᵛ : Alloc → ℕ → ℕ
↑ᵛ keep    α = α
↑ᵛ (new P) α = suc α

------------------------------------------------------------------------
-- 3. TyBeta's instantiation: strip one `∀` from every layer of a
--    `∀`-typed tower.  The `Λ`'s cell becomes the allocated cell, so
--    the body is unchanged; each layer's entry moves past the new cell.
------------------------------------------------------------------------

infix 4 _•⟶_
data _•⟶_ : Term → Term → Set where
  inst-Λ  : Λ N •⟶ N
  inst-∀  : V •⟶ N
    → [ s , α ] V ⟨ ∀ᶜ c ⟩ •⟶ [ s , suc α ] N ⟨ c ⟩
  inst-id : V •⟶ N
    → [ s , α ] V ⟨ idᶜ ⟩ •⟶ [ s , suc α ] N ⟨ idᶜ ⟩

------------------------------------------------------------------------
-- 4. Reduction
------------------------------------------------------------------------

infix 3 _⊢_⟶_∣_
data _⊢_⟶_∣_ : Ctx → Term → Term → Alloc → Set where
  β-ƛ       : Value W
    → Γ ⊢ (ƛ A ∙ N) · W ⟶ N [ W ] ∣ keep
  wrap      : Value V → Value W
    → Γ ⊢ ([ s , α ] V ⟨ c ↦ d ⟩) · W
          ⟶ [ s , α ] (V · [ flip s , α ] W ⟨ c ⟩) ⟨ d ⟩ ∣ keep
  wrap-id   : Value ([ s , α ] V ⟨ idᶜ ⟩) → Value W
    → Γ ⊢ ([ s , α ] V ⟨ idᶜ ⟩) · W
          ⟶ [ s , α ] (V · [ flip s , α ] W ⟨ idᶜ ⟩) ⟨ idᶜ ⟩ ∣ keep
  tyβ       : flags Γ ⊢ A ⇝ P → Value V → V •⟶ N
    → Γ ⊢ ν A · V ⟨ d ⟩ ⟶ [ ⁺ , zero ] N ⟨ d ⟩ ∣ new P
  id-$      : Γ ⊢ [ s , α ] ($ k) ⟨ idᶜ ⟩ ⟶ $ k ∣ keep
  cancel-□  : Value W
    → Γ ⊢ [ ⁺ , α ] ([ ⁻ , α ] W ⟨ seal ⟩) ⟨ unseal ⟩ ⟶ W ∣ keep
  -- the reveal is a value, so that over a constant, Id fires first
  cancel-id : Value ([ ⁺ , α ] V ⟨ idᶜ ⟩)
    → Γ ⊢ [ ⁻ , α ] ([ ⁺ , α ] V ⟨ idᶜ ⟩) ⟨ idᶜ ⟩ ⟶ V ∣ keep
  -- a hide moves inward: below a seal, or below a reveal of another cell
  sink      : α ≢ β → Value V
    → Γ ⊢ [ ⁻ , α ] ([ ⁻ , β ] V ⟨ seal ⟩) ⟨ idᶜ ⟩
          ⟶ [ ⁻ , β ] ([ ⁻ , α ] V ⟨ idᶜ ⟩) ⟨ seal ⟩ ∣ keep
  swap      : α ≢ β → Sealed V
    → Γ ⊢ [ ⁻ , α ] ([ ⁺ , β ] V ⟨ idᶜ ⟩) ⟨ idᶜ ⟩
          ⟶ [ ⁺ , β ] ([ ⁻ , α ] V ⟨ idᶜ ⟩) ⟨ idᶜ ⟩ ∣ keep
  -- an unseal moves inward through a reveal of another cell
  push      : Sealed V
    → Γ ⊢ [ ⁺ , α ] ([ ⁺ , β ] V ⟨ idᶜ ⟩) ⟨ unseal ⟩
          ⟶ [ ⁺ , β ] ([ ⁺ , α ] V ⟨ unseal ⟩) ⟨ idᶜ ⟩ ∣ keep
  ξ-·₁      : ∀ {a} → Γ ⊢ L ⟶ L′ ∣ a
    → Γ ⊢ L · M ⟶ L′ · ↑ᵃ a M ∣ a
  ξ-·₂      : ∀ {a} → Value V → Γ ⊢ M ⟶ M′ ∣ a
    → Γ ⊢ V · M ⟶ ↑ᵃ a V · M′ ∣ a
  ξ-ν       : ∀ {a} → Γ ⊢ L ⟶ L′ ∣ a
    → Γ ⊢ ν A · L ⟨ c ⟩ ⟶ ν A · L′ ⟨ c ⟩ ∣ a
  ξ-[]      : ∀ {a} → interior s α Γ ⊢ M ⟶ M′ ∣ a
    → Γ ⊢ [ s , α ] M ⟨ c ⟩ ⟶ [ s , ↑ᵛ a α ] M′ ⟨ c ⟩ ∣ a

------------------------------------------------------------------------
-- 5. Runs: the context grows by each step's allocation
------------------------------------------------------------------------

infix  3 _∎
infixr 2 _—→⟨_⟩_
infix  1 _⊢_—↠_⊣_

data _⊢_—↠_⊣_ : Ctx → Term → Term → Ctx → Set where
  _∎      : ∀ M → Γ ⊢ M —↠ M ⊣ Γ
  _—→⟨_⟩_ : ∀ M {M′ N Γ′ a}
    → Γ ⊢ M ⟶ M′ ∣ a
    → a ⨾ Γ ⊢ M′ —↠ N ⊣ Γ′
    → Γ ⊢ M —↠ N ⊣ Γ′
