module proof.DenotRelation where

-- File Charter:
--   * The two relations between denotations used in the denotational
--     proof of graduality (PolyG/notes/denotational-graduality.md).  The
--     more precise program is on the left.
--       θ ⊢ p ⊢ r ▹ R′   reflection: a left result is matched by the
--                         right set (an error on the left is fine);
--       θ ⊢ p ⊢ R ◃ r′   preservation: a right result is matched by the
--                         left set, or the left set errs.
--   * θ maps the type variables of p to seals.  The two programs create
--     seals in lockstep and label corresponding instantiations alike, so
--     a seal on the left is the same seal (number and label) on the
--     right, and its label is the precision derivation that relates its
--     contents.  There are no worlds.
--   * Each relation is defined by recursion on its element, and then on
--     the precision derivation (the `tag` clause keeps the element).
--     Functions are related through application to whole argument sets.

open import Data.Empty.Polymorphic using () renaming (⊥ to ⊥₁)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁)
import Level
open import Level using (Lift)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types
open import GraphModel
open import Denotation

Lift₁ : Set → Set₁
Lift₁ = Lift (Level.suc Level.zero)

-- the seal environment used for what a value carries (the label of a
-- seal, the ground of an injection): these are closed, and reading them
-- at a fixed environment makes the relations invariant under
-- substitution
θ₀ : SEnv
θ₀ i = zero

-- the reflexive derivation of a ground type: how the payloads of two
-- values in ★ with the same tag are related
gp : Ground → Prec
gp G = idᵖ (groundTy G)

------------------------------------------------------------------------
-- Reflection: a left element justified by a right set
------------------------------------------------------------------------

infix 4 _⊢_⊢_▹_ _⊢_⊢_▹ᵛ_ _⊢_⊢_▹*_

mutual
  _⊢_⊢_▹_ : SEnv → Prec → Res → ℛ → Set₁
  θ ⊢ p ⊢ ret v m ▹ R′ = θ ⊢ p ⊢ v ▹ᵛ ⌊ R′ ⌋ m
  θ ⊢ p ⊢ err ▹ R′ = ⊤₁

  _⊢_⊢_▹ᵛ_ : SEnv → Prec → Val → 𝒱 → Set₁
  θ ⊢ ★⊑ ⊢ vtrue ▹ᵛ D′ = ⊥₁
  θ ⊢ ★⊑ ⊢ vfalse ▹ᵛ D′ = ⊥₁
  θ ⊢ ★⊑ ⊢ sealᵛ σ ℓ u ▹ᵛ D′ = ⊥₁
  θ ⊢ ★⊑ ⊢ injᵛ G u ▹ᵛ D′ = θ₀ ⊢ gp G ⊢ u ▹ᵛ untag G D′
  θ ⊢ ★⊑ ⊢ U ⟼ r at m ▹ᵛ D′ = ⊥₁
  θ ⊢ ★⊑ ⊢ σℓ ⟼∀ r ▹ᵛ D′ = ⊥₁
  θ ⊢ ★⊑ ⊢ ν ▹ᵛ D′ = ⊥₁
  θ ⊢ tag G p ⊢ u ▹ᵛ D′ = θ ⊢ p ⊢ u ▹ᵛ untag (⟦ G ⟧ᴳ θ) D′
  θ ⊢ ‵⊑ α ⊢ vtrue ▹ᵛ D′ = ⊥₁
  θ ⊢ ‵⊑ α ⊢ vfalse ▹ᵛ D′ = ⊥₁
  θ ⊢ ‵⊑ α ⊢ sealᵛ σ ℓ u ▹ᵛ D′ =
    Lift₁ (σ ≡ ⟦ α ⟧# θ) × θ₀ ⊢ ℓ ⊢ u ▹ᵛ unsealᴾ σ ℓ D′
  θ ⊢ ‵⊑ α ⊢ injᵛ G u ▹ᵛ D′ = ⊥₁
  θ ⊢ ‵⊑ α ⊢ U ⟼ r at m ▹ᵛ D′ = ⊥₁
  θ ⊢ ‵⊑ α ⊢ σℓ ⟼∀ r ▹ᵛ D′ = ⊥₁
  θ ⊢ ‵⊑ α ⊢ ν ▹ᵛ D′ = ⊥₁
  θ ⊢ 𝔹⊑ ⊢ vtrue ▹ᵛ D′ = Lift₁ (vtrue ∈ D′)
  θ ⊢ 𝔹⊑ ⊢ vfalse ▹ᵛ D′ = Lift₁ (vfalse ∈ D′)
  θ ⊢ 𝔹⊑ ⊢ sealᵛ σ ℓ u ▹ᵛ D′ = ⊥₁
  θ ⊢ 𝔹⊑ ⊢ injᵛ G u ▹ᵛ D′ = ⊥₁
  θ ⊢ 𝔹⊑ ⊢ U ⟼ r at m ▹ᵛ D′ = ⊥₁
  θ ⊢ 𝔹⊑ ⊢ σℓ ⟼∀ r ▹ᵛ D′ = ⊥₁
  θ ⊢ 𝔹⊑ ⊢ ν ▹ᵛ D′ = ⊥₁
  θ ⊢ p ⇒⊑ q ⊢ vtrue ▹ᵛ D′ = ⊥₁
  θ ⊢ p ⇒⊑ q ⊢ vfalse ▹ᵛ D′ = ⊥₁
  θ ⊢ p ⇒⊑ q ⊢ sealᵛ σ ℓ u ▹ᵛ D′ = ⊥₁
  θ ⊢ p ⇒⊑ q ⊢ injᵛ G u ▹ᵛ D′ = ⊥₁
  θ ⊢ p ⇒⊑ q ⊢ U ⟼ r at m ▹ᵛ D′ =
    Lift₁ (ν ∈ D′)
    × (∀ E′ → U ≢ [] → θ ⊢ p ⊢ U ▹* E′ → θ ⊢ q ⊢ r ▹ (D′ ●[ m ] E′))
  θ ⊢ p ⇒⊑ q ⊢ σℓ ⟼∀ r ▹ᵛ D′ = ⊥₁
  θ ⊢ p ⇒⊑ q ⊢ ν ▹ᵛ D′ = Lift₁ (ν ∈ D′)
  θ ⊢ ∀⊑ p ⊢ vtrue ▹ᵛ D′ = ⊥₁
  θ ⊢ ∀⊑ p ⊢ vfalse ▹ᵛ D′ = ⊥₁
  θ ⊢ ∀⊑ p ⊢ sealᵛ σ ℓ u ▹ᵛ D′ = ⊥₁
  θ ⊢ ∀⊑ p ⊢ injᵛ G u ▹ᵛ D′ = ⊥₁
  θ ⊢ ∀⊑ p ⊢ U ⟼ r at m ▹ᵛ D′ = ⊥₁
  θ ⊢ ∀⊑ p ⊢ (σ , ℓ) ⟼∀ r ▹ᵛ D′ =
    Lift₁ (ν ∈ D′) × (σ •ᵗ θ) ⊢ p ⊢ r ▹ (D′ ◆ (σ , ℓ))
  θ ⊢ ∀⊑ p ⊢ ν ▹ᵛ D′ = Lift₁ (ν ∈ D′)

  _⊢_⊢_▹*_ : SEnv → Prec → List Val → 𝒱 → Set₁
  θ ⊢ p ⊢ [] ▹* D′ = ⊤₁
  θ ⊢ p ⊢ (u ∷ U) ▹* D′ = θ ⊢ p ⊢ u ▹ᵛ D′ × θ ⊢ p ⊢ U ▹* D′

------------------------------------------------------------------------
-- Preservation: a right element justified by a left set
------------------------------------------------------------------------

infix 4 _⊢_⊢_◃_ _⊢_⊢_◃ᵛ_ _⊢_⊢_◃*_

mutual
  _⊢_⊢_◃_ : SEnv → Prec → ℛ → Res → Set₁
  θ ⊢ p ⊢ R ◃ ret v′ m = Lift₁ (err ∈ᴿ R) ⊎ θ ⊢ p ⊢ ⌊ R ⌋ m ◃ᵛ v′
  θ ⊢ p ⊢ R ◃ err = Lift₁ (err ∈ᴿ R)

  _⊢_⊢_◃ᵛ_ : SEnv → Prec → 𝒱 → Val → Set₁
  θ ⊢ ★⊑ ⊢ D ◃ᵛ vtrue = ⊥₁
  θ ⊢ ★⊑ ⊢ D ◃ᵛ vfalse = ⊥₁
  θ ⊢ ★⊑ ⊢ D ◃ᵛ sealᵛ σ ℓ u′ = ⊥₁
  θ ⊢ ★⊑ ⊢ D ◃ᵛ injᵛ G u′ = θ₀ ⊢ gp G ⊢ untag G D ◃ᵛ u′
  θ ⊢ ★⊑ ⊢ D ◃ᵛ U′ ⟼ r′ at m = ⊥₁
  θ ⊢ ★⊑ ⊢ D ◃ᵛ σℓ ⟼∀ r′ = ⊥₁
  θ ⊢ ★⊑ ⊢ D ◃ᵛ ν = ⊥₁
  θ ⊢ tag G p ⊢ D ◃ᵛ vtrue = ⊥₁
  θ ⊢ tag G p ⊢ D ◃ᵛ vfalse = ⊥₁
  θ ⊢ tag G p ⊢ D ◃ᵛ sealᵛ σ ℓ u′ = ⊥₁
  θ ⊢ tag G p ⊢ D ◃ᵛ injᵛ H u′ =
    Lift₁ (H ≡ ⟦ G ⟧ᴳ θ) × θ ⊢ p ⊢ D ◃ᵛ u′
  θ ⊢ tag G p ⊢ D ◃ᵛ U′ ⟼ r′ at m = ⊥₁
  θ ⊢ tag G p ⊢ D ◃ᵛ σℓ ⟼∀ r′ = ⊥₁
  θ ⊢ tag G p ⊢ D ◃ᵛ ν = ⊥₁
  θ ⊢ ‵⊑ α ⊢ D ◃ᵛ vtrue = ⊥₁
  θ ⊢ ‵⊑ α ⊢ D ◃ᵛ vfalse = ⊥₁
  θ ⊢ ‵⊑ α ⊢ D ◃ᵛ sealᵛ σ ℓ u′ =
    Lift₁ (σ ≡ ⟦ α ⟧# θ) × θ₀ ⊢ ℓ ⊢ unsealᴾ σ ℓ D ◃ᵛ u′
  θ ⊢ ‵⊑ α ⊢ D ◃ᵛ injᵛ G u′ = ⊥₁
  θ ⊢ ‵⊑ α ⊢ D ◃ᵛ U′ ⟼ r′ at m = ⊥₁
  θ ⊢ ‵⊑ α ⊢ D ◃ᵛ σℓ ⟼∀ r′ = ⊥₁
  θ ⊢ ‵⊑ α ⊢ D ◃ᵛ ν = ⊥₁
  θ ⊢ 𝔹⊑ ⊢ D ◃ᵛ vtrue = Lift₁ (vtrue ∈ D)
  θ ⊢ 𝔹⊑ ⊢ D ◃ᵛ vfalse = Lift₁ (vfalse ∈ D)
  θ ⊢ 𝔹⊑ ⊢ D ◃ᵛ sealᵛ σ ℓ u′ = ⊥₁
  θ ⊢ 𝔹⊑ ⊢ D ◃ᵛ injᵛ G u′ = ⊥₁
  θ ⊢ 𝔹⊑ ⊢ D ◃ᵛ U′ ⟼ r′ at m = ⊥₁
  θ ⊢ 𝔹⊑ ⊢ D ◃ᵛ σℓ ⟼∀ r′ = ⊥₁
  θ ⊢ 𝔹⊑ ⊢ D ◃ᵛ ν = ⊥₁
  θ ⊢ p ⇒⊑ q ⊢ D ◃ᵛ vtrue = ⊥₁
  θ ⊢ p ⇒⊑ q ⊢ D ◃ᵛ vfalse = ⊥₁
  θ ⊢ p ⇒⊑ q ⊢ D ◃ᵛ sealᵛ σ ℓ u′ = ⊥₁
  θ ⊢ p ⇒⊑ q ⊢ D ◃ᵛ injᵛ G u′ = ⊥₁
  θ ⊢ p ⇒⊑ q ⊢ D ◃ᵛ U′ ⟼ r′ at m =
    Lift₁ (ν ∈ D)
    × (∀ E → U′ ≢ [] → θ ⊢ p ⊢ E ◃* U′ → θ ⊢ q ⊢ (D ●[ m ] E) ◃ r′)
  θ ⊢ p ⇒⊑ q ⊢ D ◃ᵛ σℓ ⟼∀ r′ = ⊥₁
  θ ⊢ p ⇒⊑ q ⊢ D ◃ᵛ ν = Lift₁ (ν ∈ D)
  θ ⊢ ∀⊑ p ⊢ D ◃ᵛ vtrue = ⊥₁
  θ ⊢ ∀⊑ p ⊢ D ◃ᵛ vfalse = ⊥₁
  θ ⊢ ∀⊑ p ⊢ D ◃ᵛ sealᵛ σ ℓ u′ = ⊥₁
  θ ⊢ ∀⊑ p ⊢ D ◃ᵛ injᵛ G u′ = ⊥₁
  θ ⊢ ∀⊑ p ⊢ D ◃ᵛ U′ ⟼ r′ at m = ⊥₁
  θ ⊢ ∀⊑ p ⊢ D ◃ᵛ (σ , ℓ) ⟼∀ r′ =
    Lift₁ (ν ∈ D) × (σ •ᵗ θ) ⊢ p ⊢ (D ◆ (σ , ℓ)) ◃ r′
  θ ⊢ ∀⊑ p ⊢ D ◃ᵛ ν = Lift₁ (ν ∈ D)

  _⊢_⊢_◃*_ : SEnv → Prec → 𝒱 → List Val → Set₁
  θ ⊢ p ⊢ D ◃* [] = ⊤₁
  θ ⊢ p ⊢ D ◃* (u′ ∷ U′) = θ ⊢ p ⊢ D ◃ᵛ u′ × θ ⊢ p ⊢ D ◃* U′
