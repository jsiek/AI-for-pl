module GraphModel where

-- File Charter:
--   * A graph model with errors and a seal counter, for PolyCν
--     (PolyG/notes/denotational-graduality.md, Section 3).
--   * Values (`Val`) never contain errors; a computation produces results
--     (`Res`): a value together with the counter it ends at, or `err`.
--     Divergence is the absence of results.
--   * Closures are graphs: a function entry maps a finite list of
--     arguments and a starting counter to a result; a Λν entry maps the
--     seal its instantiation creates to the result of the body.  There
--     are two empty closures, one for functions (νλ) and one for Λν
--     (ν∀), so that a cast applied to the wrong kind of value denotes
--     nothing, like the stuck term it is.
--   * Consistency, as in the compiler-correctness development: function
--     abstraction binds only consistent argument lists.
--   * Set-level operations: bind (grouping results by their final
--     counter), function abstraction and application, Λν abstraction and
--     instantiation, sealing, tagging, and tag tests.

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _⋵_)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types

------------------------------------------------------------------------
-- Values and results
------------------------------------------------------------------------

infixr 7 _⟼_at_ _⟼∀_

mutual
  data Val : Set where
    vtrue  : Val
    vfalse : Val
    sealᵛ  : Seal → Val → Val        -- a sealed value
    injᵛ   : Ground → Val → Val      -- an injection into ★ (closed ground)
    _⟼_at_ : List Val → Res → ℕ → Val
                                     -- function entry: arguments U at
                                     -- counter m give a result
    _⟼∀_   : Seal → Res → Val        -- Λν entry: instantiated at a fresh
                                     -- seal
    νλ     : Val                     -- the empty function
    ν∀     : Val                     -- the empty Λν

  data Res : Set where
    ret : Val → ℕ → Res              -- a value, ending at a counter
    err : Res                        -- a dynamic type error

------------------------------------------------------------------------
-- Consistency
------------------------------------------------------------------------

infix 5 _~_ _~ᴿ_ _≈_ _~*_

mutual
  _~_ : Val → Val → Set
  vtrue ~ vtrue = ⊤
  vfalse ~ vfalse = ⊤
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

-- consistent sets
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

Λ : (𝒱 → ℕ → ℛ) → 𝒱
Λ F (U ⟼ r at m) = r ∈ᴿ F (mem U) m × U ≢ [] × U ≈ U
Λ F νλ = ⊤
Λ F vtrue = ⊥
Λ F vfalse = ⊥
Λ F (sealᵛ σ v) = ⊥
Λ F (injᵛ G v) = ⊥
Λ F (σ ⟼∀ r) = ⊥
Λ F ν∀ = ⊥

infixl 6 _●[_]_

_●[_]_ : 𝒱 → ℕ → 𝒱 → ℛ
(D ●[ m ] E) r = Σ[ U ∈ List Val ] ((U ⟼ r at m) ∈ D × mem U ⊆ E × U ≢ [])

------------------------------------------------------------------------
-- Polymorphic functions
------------------------------------------------------------------------

-- the body for seal σ starts from counter σ + 1
Λᴾ : (Seal → ℛ) → 𝒱
Λᴾ F (σ ⟼∀ r) = r ∈ᴿ F σ
Λᴾ F ν∀ = ⊤
Λᴾ F vtrue = ⊥
Λᴾ F vfalse = ⊥
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
sealᴾ σ D vtrue = ⊥
sealᴾ σ D vfalse = ⊥
sealᴾ σ D (injᵛ G v) = ⊥
sealᴾ σ D (U ⟼ r at m) = ⊥
sealᴾ σ D (σ′ ⟼∀ r) = ⊥
sealᴾ σ D νλ = ⊥
sealᴾ σ D ν∀ = ⊥

unsealᴾ : Seal → 𝒱 → 𝒱
unsealᴾ σ D v = sealᵛ σ v ∈ D

injᴾ : Ground → 𝒱 → 𝒱
injᴾ G D (injᵛ H v) = H ≡ G × v ∈ D
injᴾ G D vtrue = ⊥
injᴾ G D vfalse = ⊥
injᴾ G D (sealᵛ σ v) = ⊥
injᴾ G D (U ⟼ r at m) = ⊥
injᴾ G D (σ ⟼∀ r) = ⊥
injᴾ G D νλ = ⊥
injᴾ G D ν∀ = ⊥

-- the payloads of D tagged G
untag : Ground → 𝒱 → 𝒱
untag G D v = injᵛ G v ∈ D

-- is(G)?: true for a value tagged G, false for one tagged otherwise
testᴾ : Ground → 𝒱 → 𝒱
testᴾ G D vtrue = Σ[ v ∈ Val ] (injᵛ G v ∈ D)
testᴾ G D vfalse = Σ[ H ∈ Ground ] Σ[ v ∈ Val ] (injᵛ H v ∈ D × H ≢ G)
testᴾ G D (sealᵛ σ v) = ⊥
testᴾ G D (injᵛ H v) = ⊥
testᴾ G D (U ⟼ r at m) = ⊥
testᴾ G D (σ ⟼∀ r) = ⊥
testᴾ G D νλ = ⊥
testᴾ G D ν∀ = ⊥

-- the projection from ★ to G at counter m: the payloads tagged G, and
-- err for any other tag
proj : Ground → 𝒱 → ℕ → ℛ
proj G D m (ret v m′) = m′ ≡ m × injᵛ G v ∈ D
proj G D m err = Σ[ H ∈ Ground ] Σ[ v ∈ Val ] (injᵛ H v ∈ D × H ≢ G)

-- the two branches of a conditional
condᴿ : 𝒱 → ℛ → ℛ → ℛ
condᴿ D R S r = (vtrue ∈ D × r ∈ᴿ R) ⊎ (vfalse ∈ D × r ∈ᴿ S)
