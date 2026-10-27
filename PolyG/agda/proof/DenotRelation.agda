module proof.DenotRelation where

-- File Charter:
--   * The two relations between denotations used in the denotational
--     proof of graduality (PolyG/notes/denotational-graduality.md,
--     Sections 5 and 6).  The more precise program is on the left.
--       reflection   (▹): a finite list of left values is matched,
--                         jointly and under one world, by a right set;
--       preservation (◃): a finite list of right values is matched by a
--                         left set (or the left errs).
--   * A world is a list of closed precision derivations: entry σ relates
--     the contents of seal σ on the two sides.  Seals are created in
--     lockstep, so a seal has the same number on both sides.  A
--     computation's world is existential; closures quantify over future
--     worlds.
--   * Lists, not single elements: an existential world must cover every
--     element that a later step uses together.  The relations are
--     defined by recursion on a fuel bound on the total size of the list
--     (`suc (sizeᴸ L)` suffices), and then on the precision derivation
--     (the `tag` clause of ▹ keeps the list).
--   * What a value carries (the ground of an injection, the derivation
--     of a seal) is closed and is read at the fixed seal environment θ₀.

open import Data.Empty using (⊥)
open import Data.Empty.Polymorphic using () renaming (⊥ to ⊥₁)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁)
import Level
open import Level using (Lift)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_; yes; no)

open import Types
open import GraphModel
open import Denotation

Lift₁ : Set → Set₁
Lift₁ = Lift (Level.suc Level.zero)

------------------------------------------------------------------------
-- Worlds
------------------------------------------------------------------------

World : Set
World = List Prec

infix 4 _∋ʷ_⦂_ _⊑ʷ_

-- W ∋ʷ σ ⦂ q: seal σ's contents are related by the closed derivation q
data _∋ʷ_⦂_ : World → Seal → Prec → Set where
  Zʷ : ∀ {W q} → (q ∷ W) ∋ʷ zero ⦂ q
  Sʷ : ∀ {W q q′ σ} → W ∋ʷ σ ⦂ q → (q′ ∷ W) ∋ʷ suc σ ⦂ q

-- a future world
_⊑ʷ_ : World → World → Set
W ⊑ʷ W′ = Σ[ X ∈ World ] (W′ ≡ W ++ X)

-- the reflexive derivation of a ground type: how the payloads of two
-- values in ★ with the same tag are related
gp : Ground → Prec
gp G = idᵖ (groundTy G)

------------------------------------------------------------------------
-- Sizes and list helpers
------------------------------------------------------------------------

mutual
  sizeᵛ : Val → ℕ
  sizeᵛ vtrue = 1
  sizeᵛ vfalse = 1
  sizeᵛ (sealᵛ σ u) = suc (sizeᵛ u)
  sizeᵛ (injᵛ G u) = suc (sizeᵛ u)
  sizeᵛ (U ⟼ r at m) = suc (sizeᴸ U + sizeᴿ r)
  sizeᵛ (σ ⟼∀ r) = suc (sizeᴿ r)
  sizeᵛ νλ = 1
  sizeᵛ ν∀ = 1

  sizeᴿ : Res → ℕ
  sizeᴿ (ret v m) = sizeᵛ v
  sizeᴿ err = 1

  sizeᴸ : List Val → ℕ
  sizeᴸ [] = zero
  sizeᴸ (v ∷ L) = sizeᵛ v + sizeᴸ L

sizeᴿᴸ : List Res → ℕ
sizeᴿᴸ [] = zero
sizeᴿᴸ (r ∷ Rs) = sizeᴿ r + sizeᴿᴸ Rs

-- the shape of each element, for each kind of precision derivation
IsBool : 𝒱 → Val → Set
IsBool D vtrue = vtrue ∈ D
IsBool D vfalse = vfalse ∈ D
IsBool D (sealᵛ σ u) = ⊥
IsBool D (injᵛ G u) = ⊥
IsBool D (U ⟼ r at m) = ⊥
IsBool D (σ ⟼∀ r) = ⊥
IsBool D νλ = ⊥
IsBool D ν∀ = ⊥

data IsInj : Val → Set where
  is-inj : ∀ {G u} → IsInj (injᵛ G u)

data IsInjAt (G : Ground) : Val → Set where
  is-inj-at : ∀ {u} → IsInjAt G (injᵛ G u)

data IsSealAt (σ : Seal) : Val → Set where
  is-seal-at : ∀ {u} → IsSealAt σ (sealᵛ σ u)

data IsFun : Val → Set where
  is-entry : ∀ {U r m} → IsFun (U ⟼ r at m)
  is-νλ : IsFun νλ

data IsPoly : Val → Set where
  is-pentry : ∀ {σ r} → IsPoly (σ ⟼∀ r)
  is-ν∀ : IsPoly ν∀

-- the payloads tagged G
untagᴸ : Ground → List Val → List Val
untagᴸ G [] = []
untagᴸ G (injᵛ H u ∷ L) with G ≟G H
... | yes _ = u ∷ untagᴸ G L
... | no _ = untagᴸ G L
untagᴸ G (vtrue ∷ L) = untagᴸ G L
untagᴸ G (vfalse ∷ L) = untagᴸ G L
untagᴸ G (sealᵛ σ u ∷ L) = untagᴸ G L
untagᴸ G ((U ⟼ r at m) ∷ L) = untagᴸ G L
untagᴸ G ((σ ⟼∀ r) ∷ L) = untagᴸ G L
untagᴸ G (νλ ∷ L) = untagᴸ G L
untagᴸ G (ν∀ ∷ L) = untagᴸ G L

-- the contents sealed at σ
unsealᴸ : Seal → List Val → List Val
unsealᴸ σ [] = []
unsealᴸ σ (sealᵛ σ′ u ∷ L) with σ ≟ℕ σ′
... | yes _ = u ∷ unsealᴸ σ L
... | no _ = unsealᴸ σ L
unsealᴸ σ (vtrue ∷ L) = unsealᴸ σ L
unsealᴸ σ (vfalse ∷ L) = unsealᴸ σ L
unsealᴸ σ (injᵛ G u ∷ L) = unsealᴸ σ L
unsealᴸ σ ((U ⟼ r at m) ∷ L) = unsealᴸ σ L
unsealᴸ σ ((σ′ ⟼∀ r) ∷ L) = unsealᴸ σ L
unsealᴸ σ (νλ ∷ L) = unsealᴸ σ L
unsealᴸ σ (ν∀ ∷ L) = unsealᴸ σ L

-- the arguments and results of the function entries at counter m
argsAt : ℕ → List Val → List Val
argsAt m [] = []
argsAt m ((U ⟼ r at m′) ∷ L) with m ≟ℕ m′
... | yes _ = U ++ argsAt m L
... | no _ = argsAt m L
argsAt m (vtrue ∷ L) = argsAt m L
argsAt m (vfalse ∷ L) = argsAt m L
argsAt m (sealᵛ σ u ∷ L) = argsAt m L
argsAt m (injᵛ G u ∷ L) = argsAt m L
argsAt m ((σ ⟼∀ r) ∷ L) = argsAt m L
argsAt m (νλ ∷ L) = argsAt m L
argsAt m (ν∀ ∷ L) = argsAt m L

resultsAt : ℕ → List Val → List Res
resultsAt m [] = []
resultsAt m ((U ⟼ r at m′) ∷ L) with m ≟ℕ m′
... | yes _ = r ∷ resultsAt m L
... | no _ = resultsAt m L
resultsAt m (vtrue ∷ L) = resultsAt m L
resultsAt m (vfalse ∷ L) = resultsAt m L
resultsAt m (sealᵛ σ u ∷ L) = resultsAt m L
resultsAt m (injᵛ G u ∷ L) = resultsAt m L
resultsAt m ((σ ⟼∀ r) ∷ L) = resultsAt m L
resultsAt m (νλ ∷ L) = resultsAt m L
resultsAt m (ν∀ ∷ L) = resultsAt m L

-- the results of the Λν entries at seal σ
bodiesAt : Seal → List Val → List Res
bodiesAt σ [] = []
bodiesAt σ ((σ′ ⟼∀ r) ∷ L) with σ ≟ℕ σ′
... | yes _ = r ∷ bodiesAt σ L
... | no _ = bodiesAt σ L
bodiesAt σ (vtrue ∷ L) = bodiesAt σ L
bodiesAt σ (vfalse ∷ L) = bodiesAt σ L
bodiesAt σ (sealᵛ σ′ u ∷ L) = bodiesAt σ L
bodiesAt σ (injᵛ G u ∷ L) = bodiesAt σ L
bodiesAt σ ((U ⟼ r at m) ∷ L) = bodiesAt σ L
bodiesAt σ (νλ ∷ L) = bodiesAt σ L
bodiesAt σ (ν∀ ∷ L) = bodiesAt σ L

-- the values a list of results returns at counter m
valuesAt : ℕ → List Res → List Val
valuesAt m [] = []
valuesAt m (ret v m′ ∷ Rs) with m ≟ℕ m′
... | yes _ = v ∷ valuesAt m Rs
... | no _ = valuesAt m Rs
valuesAt m (err ∷ Rs) = valuesAt m Rs

HasErr : List Res → Set
HasErr Rs = Any (_≡ err) Rs

------------------------------------------------------------------------
-- Reflection: a list of left values justified by a right set
------------------------------------------------------------------------

mutual
  -- the relation at fuel k (meaningful when sizeᴸ L < k)
  Rel▹ : ℕ → World → SEnv → Prec → List Val → 𝒱 → Set₁
  Rel▹ k W θ p [] D′ = ⊤₁
  Rel▹ zero W θ p (v ∷ L) D′ = ⊥₁
  Rel▹ (suc k) W θ ★⊑ L@(v ∷ _) D′ =
    Lift₁ (All IsInj L)
    × (∀ G → Rel▹ k W θ₀ (gp G) (untagᴸ G L) (untag G D′))
  Rel▹ (suc k) W θ (tag G p) L@(v ∷ _) D′ =
    Rel▹ (suc k) W θ p L (untag (⟦ G ⟧ᴳ θ) D′)
  Rel▹ (suc k) W θ (‵⊑ α) L@(v ∷ _) D′ =
    Lift₁ (All (IsSealAt (⟦ α ⟧ₙ θ)) L)
    × Σ[ q ∈ Prec ] (Lift₁ (W ∋ʷ ⟦ α ⟧ₙ θ ⦂ q)
        × Rel▹ k W θ₀ q (unsealᴸ (⟦ α ⟧ₙ θ) L)
                        (unsealᴾ (⟦ α ⟧ₙ θ) D′))
  Rel▹ (suc k) W θ 𝔹⊑ L@(v ∷ _) D′ = Lift₁ (All (IsBool D′) L)
  Rel▹ (suc k) W θ (p ⇒⊑ q) L@(v ∷ _) D′ =
    Lift₁ (All IsFun L) × Lift₁ (νλ ∈ D′)
    × (∀ m W′ → W ⊑ʷ W′ → length W′ ≡ m → ∀ E′ → Consistent E′
         → Rel▹ k W′ θ p (argsAt m L) E′
         → Rel▹ᶜ k W′ θ q (resultsAt m L) (D′ ●[ m ] E′))
  Rel▹ (suc k) W θ (∀⊑ p) L@(v ∷ _) D′ =
    Lift₁ (All IsPoly L) × Lift₁ (ν∀ ∈ D′)
    × (∀ σ W′ q′ → W ⊑ʷ W′ → length W′ ≡ σ
         → Rel▹ᶜ k (W′ ++ (q′ ∷ [])) (σ •ᵗ θ) p (bodiesAt σ L) (D′ ◆ σ))

  -- a list of left results: for each counter at which it returns
  -- values, one future world relates them all
  Rel▹ᶜ : ℕ → World → SEnv → Prec → List Res → ℛ → Set₁
  Rel▹ᶜ k W θ p Rs R′ =
    ∀ m → valuesAt m Rs ≢ []
    → Σ[ W′ ∈ World ] (Lift₁ (W ⊑ʷ W′) × Lift₁ (length W′ ≡ m)
        × Rel▹ k W′ θ p (valuesAt m Rs) (⌊ R′ ⌋ m))

infix 4 _∣_⊢_⊢_▹_ _∣_⊢_⊢_▹ᶜ_

_∣_⊢_⊢_▹_ : World → SEnv → Prec → List Val → 𝒱 → Set₁
W ∣ θ ⊢ p ⊢ L ▹ D′ = Rel▹ (suc (sizeᴸ L)) W θ p L D′

_∣_⊢_⊢_▹ᶜ_ : World → SEnv → Prec → List Res → ℛ → Set₁
W ∣ θ ⊢ p ⊢ Rs ▹ᶜ R′ = Rel▹ᶜ (suc (sizeᴿᴸ Rs)) W θ p Rs R′

------------------------------------------------------------------------
-- Preservation: a list of right values justified by a left set
------------------------------------------------------------------------

mutual
  Rel◃ : ℕ → World → SEnv → Prec → 𝒱 → List Val → Set₁
  Rel◃ k W θ p D [] = ⊤₁
  Rel◃ zero W θ p D (v′ ∷ L′) = ⊥₁
  Rel◃ (suc k) W θ ★⊑ D L′@(v′ ∷ _) =
    Lift₁ (All IsInj L′)
    × (∀ G → Rel◃ k W θ₀ (gp G) (untag G D) (untagᴸ G L′))
  Rel◃ (suc k) W θ (tag G p) D L′@(v′ ∷ _) =
    Lift₁ (All (IsInjAt (⟦ G ⟧ᴳ θ)) L′)
    × Rel◃ k W θ p D (untagᴸ (⟦ G ⟧ᴳ θ) L′)
  Rel◃ (suc k) W θ (‵⊑ α) D L′@(v′ ∷ _) =
    Lift₁ (All (IsSealAt (⟦ α ⟧ₙ θ)) L′)
    × Σ[ q ∈ Prec ] (Lift₁ (W ∋ʷ ⟦ α ⟧ₙ θ ⦂ q)
        × Rel◃ k W θ₀ q (unsealᴾ (⟦ α ⟧ₙ θ) D)
                        (unsealᴸ (⟦ α ⟧ₙ θ) L′))
  Rel◃ (suc k) W θ 𝔹⊑ D L′@(v′ ∷ _) = Lift₁ (All (IsBool D) L′)
  Rel◃ (suc k) W θ (p ⇒⊑ q) D L′@(v′ ∷ _) =
    Lift₁ (All IsFun L′) × Lift₁ (νλ ∈ D)
    × (∀ m W′ → W ⊑ʷ W′ → length W′ ≡ m → ∀ E → Consistent E
         → Rel◃ k W′ θ p E (argsAt m L′)
         → Rel◃ᶜ k W′ θ q (D ●[ m ] E) (resultsAt m L′))
  Rel◃ (suc k) W θ (∀⊑ p) D L′@(v′ ∷ _) =
    Lift₁ (All IsPoly L′) × Lift₁ (ν∀ ∈ D)
    × (∀ σ W′ q′ → W ⊑ʷ W′ → length W′ ≡ σ
         → Rel◃ᶜ k (W′ ++ (q′ ∷ [])) (σ •ᵗ θ) p (D ◆ σ) (bodiesAt σ L′))

  -- a list of right results: the left errs, or the list has no error
  -- and, for each counter at which it returns values, one future world
  -- relates them all
  Rel◃ᶜ : ℕ → World → SEnv → Prec → ℛ → List Res → Set₁
  Rel◃ᶜ k W θ p R Rs′ =
    Lift₁ (err ∈ᴿ R)
    ⊎ (Lift₁ (¬ HasErr Rs′)
       × (∀ m → valuesAt m Rs′ ≢ []
          → Σ[ W′ ∈ World ] (Lift₁ (W ⊑ʷ W′) × Lift₁ (length W′ ≡ m)
              × Rel◃ k W′ θ p (⌊ R ⌋ m) (valuesAt m Rs′))))

infix 4 _∣_⊢_⊢_◃_ _∣_⊢_⊢_◃ᶜ_

_∣_⊢_⊢_◃_ : World → SEnv → Prec → 𝒱 → List Val → Set₁
W ∣ θ ⊢ p ⊢ D ◃ L′ = Rel◃ (suc (sizeᴸ L′)) W θ p D L′

_∣_⊢_⊢_◃ᶜ_ : World → SEnv → Prec → ℛ → List Res → Set₁
W ∣ θ ⊢ p ⊢ R ◃ᶜ Rs′ = Rel◃ᶜ (suc (sizeᴿᴸ Rs′)) W θ p R Rs′
