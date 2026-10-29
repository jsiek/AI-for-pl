module Denot.GraphModel where

-- File Charter:
--   * A graph model with errors and a seal counter for GTSFImp's cast
--     calculus (notes/denotational-dgg.md, Section 9, step 2), ported
--     from PolyG's `GraphModel`.
--   * Values (`Val`) never contain errors; a computation produces results
--     (`Res`): a value with the counter it ends at, or `err` (blame).
--     Divergence is the absence of results.
--   * Closures are graphs.  A function entry maps a finite list of
--     arguments and a starting counter to a result.  A polymorphic entry
--     maps the seal that its instantiation creates to the result of the
--     body, which starts one counter later.  The empty closures `νλ` and
--     `ν∀` make a cast or conversion at a function or `∀` type denote
--     nothing on a value of the wrong kind, like the stuck term it is.
--   * Closed grounds (`VGround`) are base types, `★ ⇒ ★`, `∀★`, and seals:
--     a type variable used as a tag is a seal at run time.
--   * Consistency as in PolyG: function abstraction binds only consistent
--     argument lists.
--   * Set-level operations: bind, function and polymorphic abstraction
--     and elimination, sealing, tagging and projection, and primitives.

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _⋵_)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types using (Base)
open import Primitives using (Const; Prim; δ)

Seal : Set
Seal = ℕ

------------------------------------------------------------------------
-- Closed grounds
------------------------------------------------------------------------

data VGround : Set where
  gι : Base → VGround
  g⇒ : VGround
  g∀ : VGround
  gσ : Seal → VGround

------------------------------------------------------------------------
-- Values and results
------------------------------------------------------------------------

infixr 7 _⟼_at_ _⟼∀_

mutual
  data Val : Set where
    vconst : Const → Val
    sealᵛ  : Seal → Val → Val        -- a sealed value
    injᵛ   : VGround → Val → Val     -- an injection into ★
    _⟼_at_ : List Val → Res → ℕ → Val
                                     -- function entry: arguments U at
                                     -- counter m give a result
    _⟼∀_   : Seal → Res → Val        -- polymorphic entry, instantiated
                                     -- at a fresh seal
    νλ     : Val                     -- the empty function
    ν∀     : Val                     -- the empty polymorphic value

  data Res : Set where
    ret : Val → ℕ → Res              -- a value, ending at a counter
    err : Res                        -- blame

------------------------------------------------------------------------
-- Consistency
------------------------------------------------------------------------

infix 5 _~_ _~ᴿ_ _≈_ _~*_

mutual
  _~_ : Val → Val → Set
  vconst κ ~ vconst κ′ = κ ≡ κ′
  sealᵛ σ u ~ sealᵛ σ′ u′ = σ ≡ σ′ × u ~ u′
  injᵛ G u ~ injᵛ H u′ = G ≡ H × u ~ u′
  (U ⟼ r at m) ~ (U′ ⟼ r′ at m′) = m ≡ m′ → U ≈ U′ → r ~ᴿ r′
  (U ⟼ r at m) ~ νλ = ⊤
  νλ ~ (U′ ⟼ r′ at m′) = ⊤
  νλ ~ νλ = ⊤
  (σ ⟼∀ r) ~ (σ′ ⟼∀ r′) = σ ≡ σ′ → r ~ᴿ r′
  (σ ⟼∀ r) ~ ν∀ = ⊤
  ν∀ ~ (σ′ ⟼∀ r′) = ⊤
  ν∀ ~ ν∀ = ⊤
  _ ~ _ = ⊥

  _~ᴿ_ : Res → Res → Set
  ret v m ~ᴿ ret v′ m′ = m ≡ m′ × v ~ v′
  err ~ᴿ err = ⊤
  _ ~ᴿ _ = ⊥

  -- every element of the first list is consistent with every element
  -- of the second
  _≈_ : List Val → List Val → Set
  [] ≈ V = ⊤
  (u ∷ U) ≈ V = u ~* V × U ≈ V

  _~*_ : Val → List Val → Set
  u ~* [] = ⊤
  u ~* (v ∷ V) = u ~ v × u ~* V

------------------------------------------------------------------------
-- Sets
------------------------------------------------------------------------

𝒱 : Set₁
𝒱 = Val → Set

ℛ : Set₁
ℛ = Res → Set

infix 4 _∈_ _⊆_ _∈ᴿ_ _⊆ᴿ_

_∈_ : Val → 𝒱 → Set
v ∈ D = D v

_⊆_ : 𝒱 → 𝒱 → Set
D ⊆ E = ∀ v → v ∈ D → v ∈ E

_∈ᴿ_ : Res → ℛ → Set
r ∈ᴿ R = R r

_⊆ᴿ_ : ℛ → ℛ → Set
R ⊆ᴿ S = ∀ r → r ∈ᴿ R → r ∈ᴿ S

mem : List Val → 𝒱
mem U v = v ⋵ U

⌈_⌉ : Val → 𝒱
⌈ v ⌉ u = u ≡ v

Conv : 𝒱 → Set
Conv D = ∃[ v ] (v ∈ D)

Consistent : 𝒱 → Set
Consistent D = ∀ u v → u ∈ D → v ∈ D → u ~ v

Consistentᴿ : ℛ → Set
Consistentᴿ R = ∀ r s → r ∈ᴿ R → s ∈ᴿ R → r ~ᴿ s

------------------------------------------------------------------------
-- Results
------------------------------------------------------------------------

-- the results that return a value of D at counter n
retᴿ : 𝒱 → ℕ → ℛ
retᴿ D n (ret v m) = m ≡ n × v ∈ D
retᴿ D n err = ⊥

errᴿ : ℛ
errᴿ (ret v m) = ⊥
errᴿ err = ⊤

∅ᴿ : ℛ
∅ᴿ r = ⊥

-- the values that R returns at counter m
⌊_⌋ : ℛ → ℕ → 𝒱
⌊ R ⌋ m v = ret v m ∈ᴿ R

infixl 5 _≫=_

-- bind: errors propagate; each group of values with the same final
-- counter is passed to the continuation
_≫=_ : ℛ → (𝒱 → ℕ → ℛ) → ℛ
(R ≫= K) r =
  (r ≡ err × err ∈ᴿ R) ⊎ (Σ[ m ∈ ℕ ] (Conv (⌊ R ⌋ m) × r ∈ᴿ K (⌊ R ⌋ m) m))

-- R, provided v is in D
guard : Val → 𝒱 → ℛ → ℛ
guard v D R r = v ∈ D × r ∈ᴿ R

------------------------------------------------------------------------
-- Functions
------------------------------------------------------------------------

Λᶠ : (𝒱 → ℕ → ℛ) → 𝒱
Λᶠ F (U ⟼ r at m) = r ∈ᴿ F (mem U) m × U ≢ [] × U ≈ U
Λᶠ F νλ = ⊤
Λᶠ F (vconst κ) = ⊥
Λᶠ F (sealᵛ σ v) = ⊥
Λᶠ F (injᵛ G v) = ⊥
Λᶠ F (σ ⟼∀ r) = ⊥
Λᶠ F ν∀ = ⊥

infixl 6 _●[_]_

_●[_]_ : 𝒱 → ℕ → 𝒱 → ℛ
(D ●[ m ] E) r = Σ[ U ∈ List Val ] ((U ⟼ r at m) ∈ D × mem U ⊆ E × U ≢ [])

------------------------------------------------------------------------
-- Polymorphic values
------------------------------------------------------------------------

-- the body for seal σ starts from counter σ + 1
Λᴾ : (Seal → ℛ) → 𝒱
Λᴾ F (σ ⟼∀ r) = r ∈ᴿ F σ
Λᴾ F ν∀ = ⊤
Λᴾ F (vconst κ) = ⊥
Λᴾ F (sealᵛ σ v) = ⊥
Λᴾ F (injᵛ G v) = ⊥
Λᴾ F (U ⟼ r at m) = ⊥
Λᴾ F νλ = ⊥

infixl 6 _◆_

-- instantiation at the fresh seal σ
_◆_ : 𝒱 → Seal → ℛ
(D ◆ σ) r = (σ ⟼∀ r) ∈ D

------------------------------------------------------------------------
-- Seals and tags
------------------------------------------------------------------------

sealᴾ : Seal → 𝒱 → 𝒱
sealᴾ σ D (sealᵛ σ′ v) = σ′ ≡ σ × v ∈ D
sealᴾ σ D (vconst κ) = ⊥
sealᴾ σ D (injᵛ G v) = ⊥
sealᴾ σ D (U ⟼ r at m) = ⊥
sealᴾ σ D (σ′ ⟼∀ r) = ⊥
sealᴾ σ D νλ = ⊥
sealᴾ σ D ν∀ = ⊥

unsealᴾ : Seal → 𝒱 → 𝒱
unsealᴾ σ D v = sealᵛ σ v ∈ D

injᴾ : VGround → 𝒱 → 𝒱
injᴾ G D (injᵛ H v) = H ≡ G × v ∈ D
injᴾ G D (vconst κ) = ⊥
injᴾ G D (sealᵛ σ v) = ⊥
injᴾ G D (U ⟼ r at m) = ⊥
injᴾ G D (σ ⟼∀ r) = ⊥
injᴾ G D νλ = ⊥
injᴾ G D ν∀ = ⊥

-- the payloads of D tagged G
untag : VGround → 𝒱 → 𝒱
untag G D v = injᵛ G v ∈ D

-- the projection from ★ to G at counter m: the payloads tagged G, and
-- err for any other tag
proj : VGround → 𝒱 → ℕ → ℛ
proj G D m (ret v m′) = m′ ≡ m × injᵛ G v ∈ D
proj G D m err = Σ[ H ∈ VGround ] Σ[ v ∈ Val ] (injᵛ H v ∈ D × H ≢ G)

------------------------------------------------------------------------
-- Primitives
------------------------------------------------------------------------

δᴾ : Prim → 𝒱 → 𝒱 → 𝒱
δᴾ op D E (vconst κ″) =
  Σ[ κ ∈ Const ] Σ[ κ′ ∈ Const ]
    (vconst κ ∈ D × vconst κ′ ∈ E × δ op κ κ′ κ″)
δᴾ op D E (sealᵛ σ v) = ⊥
δᴾ op D E (injᵛ G v) = ⊥
δᴾ op D E (U ⟼ r at m) = ⊥
δᴾ op D E (σ ⟼∀ r) = ⊥
δᴾ op D E νλ = ⊥
δᴾ op D E ν∀ = ⊥
