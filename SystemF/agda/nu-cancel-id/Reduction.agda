module nu-cancel-id.Reduction where

-- File Charter:
--   * VALUES AND SMALL-STEP REDUCTION of νF₁ᶜ (notes/CancelIdSketch.md
--     §3 in strong-rep-nu).
--   * §1 values, split by the type they can have: `Fun` (arrow or `∀`
--     type), `Sealed` (a seal head over a value: variable type), and
--     constants.  An `idᶜ` layer is a value only over a `Fun`, and never
--     as the outer half of a CancelId pair; over a sealed value only as
--     the second seal head.
--   * §2 shifting for allocation (`renameʳ`, which moves only scope
--     entries), §3 Beta's substitution of a closed value (a copy that
--     crosses a `Λ` is wrapped in `[ ⁻ , 0 ] … ⟨ idᶜ ⟩`, the hiding
--     boundary of strong-rep-nu's `crossΛᴹ`), §4 TyBeta's instantiation
--     `_•⟶_`, §5 the step relation.
--   * A step records what it allocates (`Alloc`): TyBeta allocates one
--     unnamed cell at the head of the store, and every sibling of the
--     redex shifts (`↑ᵃ`).

open import Data.Bool using (false)
open import Data.List using (_∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; compare; less; equal; greater)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)
open import Data.Product using (∃-syntax)

open import nu-cancel-id.Types
open import nu-cancel-id.Ctx
open import nu-cancel-id.Terms

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

-- the two seal heads of cell α, over a value
data Sealed where
  S-seal : Value W → Sealed ([ ⁻ , α ] W ⟨ seal ⟩)
  S-hid  : Value W → Sealed ([ ⁺ , α ] ([ ⁻ , α ] W ⟨ seal ⟩) ⟨ idᶜ ⟩)

data Value where
  V-$      : Value ($ k)
  V-fun    : Fun V → Value V
  V-sealed : Sealed V → Value V

------------------------------------------------------------------------
-- 2. Representation renaming.  It moves the cells named by scope
--    entries.  Annotations are NAMED types and stay put: allocation
--    adds an unnamed cell, so no name position moves.
------------------------------------------------------------------------

renameʳ : Renameᵗ → Term → Term
renameʳ ρ (` x)               = ` x
renameʳ ρ ($ k)               = $ k
renameʳ ρ (ƛ A ∙ N)           = ƛ A ∙ renameʳ ρ N
renameʳ ρ (L · M)             = renameʳ ρ L · renameʳ ρ M
renameʳ ρ (Λ N)               = Λ renameʳ (extᵗ ρ) N
renameʳ ρ (ν A · L ⟨ c ⟩)     = ν A · renameʳ ρ L ⟨ c ⟩
renameʳ ρ ([ s , α ] M ⟨ c ⟩) = [ s , ρ α ] renameʳ ρ M ⟨ c ⟩

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
-- 3. Substitution of a closed value for term variable j
------------------------------------------------------------------------

-- a copy that crosses a `Λ` hides the `Λ`'s own variable, so its holes
-- keep their scope map
crossΛ : Term → Term
crossΛ V = [ ⁻ , zero ] renameʳ suc V ⟨ idᶜ ⟩

substVar : ℕ → ℕ → Term → Term
substVar x j V with compare x j
substVar x .(suc (x + k)) V | less .x k    = ` x
substVar x .x             V | equal .x     = V
substVar .(suc (j + k)) j V | greater .j k = ` (j + k)

-- boundary bodies are term-closed, so substitution stops there
subst : ℕ → Term → Term → Term
subst j V (` x)               = substVar x j V
subst j V ($ k)               = $ k
subst j V (ƛ A ∙ N)           = ƛ A ∙ subst (suc j) V N
subst j V (L · M)             = subst j V L · subst j V M
subst j V (Λ N)               = Λ subst j (crossΛ V) N
subst j V (ν A · L ⟨ c ⟩)     = ν A · subst j V L ⟨ c ⟩
subst j V ([ s , α ] M ⟨ c ⟩) = [ s , α ] M ⟨ c ⟩

infix 8 _[_]
_[_] : Term → Term → Term
N [ V ] = subst zero V N

------------------------------------------------------------------------
-- 4. TyBeta's instantiation: strip one `∀` from every layer of a
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
-- 5. Reduction
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
  cancel-id : Value V
    → Γ ⊢ [ ⁻ , α ] ([ ⁺ , α ] V ⟨ idᶜ ⟩) ⟨ idᶜ ⟩ ⟶ V ∣ keep
  sink-seal : α ≢ β → Value V
    → Γ ⊢ [ s , α ] ([ ⁻ , β ] V ⟨ seal ⟩) ⟨ idᶜ ⟩
          ⟶ [ ⁻ , β ] ([ s , α ] V ⟨ idᶜ ⟩) ⟨ seal ⟩ ∣ keep
  sink-hid  : α ≢ β → Value V
    → Γ ⊢ [ s , α ] ([ ⁺ , β ] ([ ⁻ , β ] V ⟨ seal ⟩) ⟨ idᶜ ⟩) ⟨ idᶜ ⟩
          ⟶ [ ⁺ , β ] ([ ⁻ , β ] ([ s , α ] V ⟨ idᶜ ⟩) ⟨ seal ⟩) ⟨ idᶜ ⟩
          ∣ keep
  ξ-·₁      : ∀ {a} → Γ ⊢ L ⟶ L′ ∣ a
    → Γ ⊢ L · M ⟶ L′ · ↑ᵃ a M ∣ a
  ξ-·₂      : ∀ {a} → Value V → Γ ⊢ M ⟶ M′ ∣ a
    → Γ ⊢ V · M ⟶ ↑ᵃ a V · M′ ∣ a
  ξ-ν       : ∀ {a} → Γ ⊢ L ⟶ L′ ∣ a
    → Γ ⊢ ν A · L ⟨ c ⟩ ⟶ ν A · L′ ⟨ c ⟩ ∣ a
  ξ-[]      : ∀ {a} → interior s α Γ ⊢ M ⟶ M′ ∣ a
    → Γ ⊢ [ s , α ] M ⟨ c ⟩ ⟶ [ s , ↑ᵛ a α ] M′ ⟨ c ⟩ ∣ a

------------------------------------------------------------------------
-- 6. Runs: the context grows by each step's allocation
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
