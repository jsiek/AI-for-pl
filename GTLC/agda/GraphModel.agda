module GraphModel where

-- File Charter:
--   * The graph model with errors, specialized to the GTLC cast calculus:
--     denotational values, sets as predicates, the error monad, and the
--     operators Λ (abstraction) and ● (application).
--   * Adapted from denotational_semantics (Framework/GraphModel/), with the
--     domain cut down to GTLC's values: numerals, function entries, the empty
--     function ν, the error ω, and injections into ★ at a ground tag.
--   * A computation is a set D: it errs when ω ∈ D, it has the values ⌊ D ⌋,
--     and it diverges when it has neither.

open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _⋵_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)

open import Types

------------------------------------------------------------------------
-- Denotational values
------------------------------------------------------------------------

data Tag : Set where
  ℕᵗ : Tag
  ⇒ᵗ : Tag

tagTy : Tag → Ty
tagTy ℕᵗ = ℕ
tagTy ⇒ᵗ = ★ ⇒ ★

infixr 7 _⟼_

data Val : Set where
  nat : Nat → Val                  -- a numeral
  _⟼_ : List Val → Val → Val       -- an entry of a function's graph
  ν   : Val                        -- the empty function
  ω   : Val                        -- the error (blame)
  tag : Tag → Val → Val            -- an injection into ★

------------------------------------------------------------------------
-- Sets as predicates
------------------------------------------------------------------------

𝒫 : Set₁
𝒫 = Val → Set

infix 4 _∈_ _⊆_

_∈_ : Val → 𝒫 → Set
d ∈ D = D d

_⊆_ : 𝒫 → 𝒫 → Set
D ⊆ E = ∀ d → d ∈ D → d ∈ E

mem : List Val → 𝒫
mem V d = d ⋵ V

⌈_⌉ : Val → 𝒫
⌈ v ⌉ d = d ≡ v

-- the values of D
⌊_⌋ : 𝒫 → 𝒫
⌊ D ⌋ d = d ∈ D × d ≢ ω

-- D has a value
Conv : 𝒫 → Set
Conv D = ∃[ d ] (d ∈ D × d ≢ ω)

-- D holds no error (a record, so that D can be inferred from it)
record ValSet (D : 𝒫) : Set where
  constructor valset
  field
    ω∉ : ¬ (ω ∈ D)
open ValSet public

------------------------------------------------------------------------
-- The error monad
------------------------------------------------------------------------

infixl 5 _≫=_

-- D ≫= F errs when D does, and is F on the values of D when D has one.
_≫=_ : 𝒫 → (𝒫 → 𝒫) → 𝒫
(D ≫= F) w = (w ≡ ω × ω ∈ D) ⊎ (Conv D × w ∈ F ⌊ D ⌋)

-- D, provided that X has a value
guard : 𝒫 → 𝒫 → 𝒫
guard X D w = Conv X × w ∈ D

------------------------------------------------------------------------
-- Abstraction and application
------------------------------------------------------------------------

-- a finite list without ω: what a binder binds
NoErr : List Val → Set
NoErr V = ¬ (ω ⋵ V)

Λ : (𝒫 → 𝒫) → 𝒫
Λ F (V ⟼ w) = w ∈ F (mem V) × V ≢ [] × NoErr V
Λ F ν = ⊤
Λ F (nat n) = ⊥
Λ F ω = ⊥
Λ F (tag t d) = ⊥

infixl 6 _●_

_●_ : 𝒫 → 𝒫 → 𝒫
(D ● E) w = Σ[ V ∈ List Val ] ((V ⟼ w) ∈ D × mem V ⊆ E × V ≢ [])

------------------------------------------------------------------------
-- Injections into ★
------------------------------------------------------------------------

tagᴾ : Tag → 𝒫 → 𝒫
tagᴾ t X (tag t′ v) = t′ ≡ t × v ∈ X
tagᴾ t X (nat n) = ⊥
tagᴾ t X (V ⟼ w) = ⊥
tagᴾ t X ν = ⊥
tagᴾ t X ω = ⊥

untag : Tag → 𝒫 → 𝒫
untag t D v = tag t v ∈ D
