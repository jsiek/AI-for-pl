module GraphModel where

-- File Charter:
--   * A graph model with errors and a seal counter, for PolyCν
--     (PolyG/notes/denotational-graduality.md, Section 3).
--   * Values (`Val`) never contain errors; a computation produces results
--     (`Res`): a value together with the counter it ends at, or `err`.
--     Divergence is the absence of results.
--   * A seal is a number together with the (closed) label of the
--     instantiation that created it; a sealed value carries its seal's
--     label, and a Λν entry records the label it was instantiated with.
--     Two related programs label corresponding instantiations alike, so
--     the label is the precision derivation relating a seal's contents.
--   * Closures are graphs: a function entry maps a finite list of
--     arguments and a starting counter to a result; a Λν entry maps the
--     seal its instantiation creates to the result of the body.
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
    sealᵛ  : Seal → Prec → Val → Val -- a value sealed at a labelled seal
    injᵛ   : Ground → Val → Val      -- an injection into ★ (closed ground)
    _⟼_at_ : List Val → Res → ℕ → Val
                                     -- function entry: arguments U at
                                     -- counter m give a result
    _⟼∀_   : Seal × Prec → Res → Val -- Λν entry: instantiated at a fresh
                                     -- labelled seal
    ν      : Val                     -- the empty closure

  data Res : Set where
    ret : Val → ℕ → Res              -- a value, ending at a counter
    err : Res                        -- a dynamic type error

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

guard : 𝒱 → ℛ → ℛ
guard D R r = Conv D × r ∈ᴿ R

------------------------------------------------------------------------
-- Functions
------------------------------------------------------------------------

Λ : (𝒱 → ℕ → ℛ) → 𝒱
Λ F (U ⟼ r at m) = r ∈ᴿ F (mem U) m × U ≢ []
Λ F ν = ⊤
Λ F vtrue = ⊥
Λ F vfalse = ⊥
Λ F (sealᵛ σ B v) = ⊥
Λ F (injᵛ G v) = ⊥
Λ F (σB ⟼∀ r) = ⊥

infixl 6 _●[_]_

_●[_]_ : 𝒱 → ℕ → 𝒱 → ℛ
(D ●[ m ] E) r = Σ[ U ∈ List Val ] ((U ⟼ r at m) ∈ D × mem U ⊆ E × U ≢ [])

------------------------------------------------------------------------
-- Polymorphic functions
------------------------------------------------------------------------

Λᴾ : (Seal × Prec → ℛ) → 𝒱
Λᴾ F (σB ⟼∀ r) = r ∈ᴿ F σB
Λᴾ F ν = ⊤
Λᴾ F vtrue = ⊥
Λᴾ F vfalse = ⊥
Λᴾ F (sealᵛ σ B v) = ⊥
Λᴾ F (injᵛ G v) = ⊥
Λᴾ F (U ⟼ r at m) = ⊥

infixl 6 _◆_

-- instantiation at a fresh labelled seal
_◆_ : 𝒱 → Seal × Prec → ℛ
(D ◆ σB) r = (σB ⟼∀ r) ∈ D

------------------------------------------------------------------------
-- Seals and tags
------------------------------------------------------------------------

sealᴾ : Seal → Prec → 𝒱 → 𝒱
sealᴾ σ B D (sealᵛ σ′ B′ v) = σ′ ≡ σ × B′ ≡ B × v ∈ D
sealᴾ σ B D vtrue = ⊥
sealᴾ σ B D vfalse = ⊥
sealᴾ σ B D (injᵛ G v) = ⊥
sealᴾ σ B D (U ⟼ r at m) = ⊥
sealᴾ σ B D (σB ⟼∀ r) = ⊥
sealᴾ σ B D ν = ⊥

unsealᴾ : Seal → Prec → 𝒱 → 𝒱
unsealᴾ σ B D v = sealᵛ σ B v ∈ D

injᴾ : Ground → 𝒱 → 𝒱
injᴾ G D (injᵛ H v) = H ≡ G × v ∈ D
injᴾ G D vtrue = ⊥
injᴾ G D vfalse = ⊥
injᴾ G D (sealᵛ σ B v) = ⊥
injᴾ G D (U ⟼ r at m) = ⊥
injᴾ G D (σB ⟼∀ r) = ⊥
injᴾ G D ν = ⊥

-- the payloads of D tagged G
untag : Ground → 𝒱 → 𝒱
untag G D v = injᵛ G v ∈ D

-- is(G)?: true for a value tagged G, false for one tagged otherwise
testᴾ : Ground → 𝒱 → 𝒱
testᴾ G D vtrue = Σ[ v ∈ Val ] (injᵛ G v ∈ D)
testᴾ G D vfalse = Σ[ H ∈ Ground ] Σ[ v ∈ Val ] (injᵛ H v ∈ D × H ≢ G)
testᴾ G D (sealᵛ σ B v) = ⊥
testᴾ G D (injᵛ H v) = ⊥
testᴾ G D (U ⟼ r at m) = ⊥
testᴾ G D (σB ⟼∀ r) = ⊥
testᴾ G D ν = ⊥

-- the projection from ★ to G at counter m: the payloads tagged G, and
-- err for any other tag
proj : Ground → 𝒱 → ℕ → ℛ
proj G D m (ret v m′) = m′ ≡ m × injᵛ G v ∈ D
proj G D m err = Σ[ H ∈ Ground ] Σ[ v ∈ Val ] (injᵛ H v ∈ D × H ≢ G)

-- the two branches of a conditional
condᴿ : 𝒱 → ℛ → ℛ → ℛ
condᴿ D R S r = (vtrue ∈ D × r ∈ᴿ R) ⊎ (vfalse ∈ D × r ∈ᴿ S)
