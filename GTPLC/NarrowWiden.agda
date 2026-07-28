module NarrowWiden where

-- File Charter:
--   * Grammar of GTPLC narrowing and widening coercions.
--   * Defines only the mutually recursive syntactic classifications.

open import Types
open import Coercions

------------------------------------------------------------------------
-- Narrowing grammar
------------------------------------------------------------------------

mutual

  data Crossⁿ : Coercion → Set where
    id : Crossⁿ id
    _↦_ : ∀ {s t} → Widening s → Narrowing t → Crossⁿ (s ↦ t)
    `∀ : ∀ {s} → Narrowing s → Crossⁿ (`∀ s)

  data NonIdCrossⁿ : Coercion → Set where
    _↦ˡ_ : ∀ {s t}
      → NonIdʷ s → Narrowing t → NonIdCrossⁿ (s ↦ t)
    _↦ʳ_ : ∀ {s t}
      → Widening s → NonIdⁿ t → NonIdCrossⁿ (s ↦ t)
    `∀ : ∀ {s} → NonIdⁿ s → NonIdCrossⁿ (`∀ s)

  data GenSafe : Coercion → Set where
    _↦_ : ∀ {s t} → Widening s → Narrowing t → GenSafe (s ↦ t)
    `∀ : ∀ {s} → Narrowing s → GenSafe (`∀ s)
    gen : ∀ {s} → GenSafe s → GenSafe (gen s)

  data Narrowing : Coercion → Set where
    cross : ∀ {g} → Crossⁿ g → Narrowing g
    id : Narrowing id
    gen : ∀ {s} → GenSafe s → Narrowing (gen s)
    _？ : (G : Tag) → Narrowing (G ？)
    _？︔_ : ∀ {g} → (G : Tag) → NonIdCrossⁿ g → Narrowing ((G ？) ︔ g)
    fun-？︔gen : ∀ {s} → GenSafe s → Narrowing (((★⇒★ ？) ︔ gen s))
    seal : (α : TyVar) → Narrowing (seal α)
    _︔seal_ : ∀ {s} → NonIdⁿ s → (α : TyVar) → Narrowing (s ︔ seal α)

  data NonIdⁿ : Coercion → Set where
    cross : ∀ {g} → NonIdCrossⁿ g → NonIdⁿ g
    gen : ∀ {s} → GenSafe s → NonIdⁿ (gen s)
    _？ : (G : Tag) → NonIdⁿ (G ？)
    _？︔_ : ∀ {g} → (G : Tag) → NonIdCrossⁿ g → NonIdⁿ ((G ？) ︔ g)
    fun-？︔gen : ∀ {s} → GenSafe s → NonIdⁿ (((★⇒★ ？) ︔ gen s))
    seal : (α : TyVar) → NonIdⁿ (seal α)
    _︔seal_ : ∀ {s} → NonIdⁿ s → (α : TyVar) → NonIdⁿ (s ︔ seal α)

------------------------------------------------------------------------
-- Widening grammar
------------------------------------------------------------------------

  data Crossʷ : Coercion → Set where
    id : Crossʷ id
    _↦_ : ∀ {s t} → Narrowing s → Widening t → Crossʷ (s ↦ t)
    `∀ : ∀ {s} → Widening s → Crossʷ (`∀ s)

  data NonIdCrossʷ : Coercion → Set where
    _↦ˡ_ : ∀ {s t} → NonIdⁿ s → Widening t → NonIdCrossʷ (s ↦ t)
    _↦ʳ_ : ∀ {s t} → Narrowing s → NonIdʷ t → NonIdCrossʷ (s ↦ t)
    `∀ : ∀ {s} → NonIdʷ s → NonIdCrossʷ (`∀ s)

  data InstSafe : Coercion → Set where
    _↦_ : ∀ {s t} → Narrowing s → Widening t → InstSafe (s ↦ t)
    `∀ : ∀ {s} → Widening s → InstSafe (`∀ s)
    inst : ∀ {s} → InstSafe s → InstSafe (inst s)

  data Widening : Coercion → Set where
    cross : ∀ {g} → Crossʷ g → Widening g
    id : Widening id
    inst : ∀ {s} → InstSafe s → Widening (inst s)
    _! : (G : Tag) → Widening (G !)
    _︔_! : ∀ {g} → NonIdCrossʷ g → (G : Tag) → Widening (g ︔ (G !))
    inst_︔★⇒★! : ∀ {s} → InstSafe s → Widening (inst s ︔ (★⇒★ !))
    unseal : (α : TyVar) → Widening (unseal α)
    unseal_︔_ : (α : TyVar) → ∀ {s} → NonIdʷ s → Widening ((Coercions.unseal α) ︔ s)

  data NonIdʷ : Coercion → Set where
    cross : ∀ {g} → NonIdCrossʷ g → NonIdʷ g
    inst : ∀ {s} → InstSafe s → NonIdʷ (inst s)
    _! : (G : Tag) → NonIdʷ (G !)
    _︔_! : ∀ {g} → NonIdCrossʷ g → (G : Tag) → NonIdʷ (g ︔ (G !))
    inst_︔★⇒★! : ∀ {s} → InstSafe s → NonIdʷ (inst s ︔ (★⇒★ !))
    unseal : (α : TyVar) → NonIdʷ (unseal α)
    unseal_︔_ : (α : TyVar) → ∀ {s} → NonIdʷ s
      → NonIdʷ ((Coercions.unseal α) ︔ s)
