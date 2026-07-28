module NarrowWiden where

-- File Charter:
--   * Grammar of GTPLC narrowing and widening coercions.
--   * Defines partial raw composition of narrowing and widening coercions.

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_; ∃-syntax)

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
    _？︔_ : ∀ {g}
      → (G : Tag) → NonIdCrossⁿ g → Narrowing ((G ？) ︔ g)
    fun-？︔gen : ∀ {s}
      → GenSafe s → Narrowing (((★⇒★ ？) ︔ gen s))
    seal : (α : TyVar) → Narrowing (seal α)
    _︔seal_ : ∀ {s}
      → NonIdⁿ s → (α : TyVar) → Narrowing (s ︔ seal α)

  data NonIdⁿ : Coercion → Set where
    cross : ∀ {g} → NonIdCrossⁿ g → NonIdⁿ g
    gen : ∀ {s} → GenSafe s → NonIdⁿ (gen s)
    _？ : (G : Tag) → NonIdⁿ (G ？)
    _？︔_ : ∀ {g}
      → (G : Tag) → NonIdCrossⁿ g → NonIdⁿ ((G ？) ︔ g)
    fun-？︔gen : ∀ {s}
      → GenSafe s → NonIdⁿ (((★⇒★ ？) ︔ gen s))
    seal : (α : TyVar) → NonIdⁿ (seal α)
    _︔seal_ : ∀ {s}
      → NonIdⁿ s → (α : TyVar) → NonIdⁿ (s ︔ seal α)

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
    inst_︔★⇒★! : ∀ {s}
      → InstSafe s → Widening (inst s ︔ (★⇒★ !))
    unseal : (α : TyVar) → Widening (unseal α)
    unseal_︔_ : (α : TyVar) → ∀ {s}
      → NonIdʷ s → Widening ((Coercions.unseal α) ︔ s)

  data NonIdʷ : Coercion → Set where
    cross : ∀ {g} → NonIdCrossʷ g → NonIdʷ g
    inst : ∀ {s} → InstSafe s → NonIdʷ (inst s)
    _! : (G : Tag) → NonIdʷ (G !)
    _︔_! : ∀ {g} → NonIdCrossʷ g → (G : Tag) → NonIdʷ (g ︔ (G !))
    inst_︔★⇒★! : ∀ {s}
      → InstSafe s → NonIdʷ (inst s ︔ (★⇒★ !))
    unseal : (α : TyVar) → NonIdʷ (unseal α)
    unseal_︔_ : (α : TyVar) → ∀ {s} → NonIdʷ s
      → NonIdʷ ((Coercions.unseal α) ︔ s)

coercionⁿ : ∀{c} → Narrowing c → Coercion
coercionⁿ {c} n = c

coercionʷ : ∀{c} → Widening c → Coercion
coercionʷ {c} w = c

------------------------------------------------------------------------
-- Renaming narrowing and widening
------------------------------------------------------------------------

mutual
  renameCrossⁿ : (ρ : Renameᵗ) → ∀ {s}
    → Crossⁿ s
    → Crossⁿ (renameᶜ ρ s)
  renameCrossⁿ ρ id = id
  renameCrossⁿ ρ (sʷ ↦ tⁿ) = renameʷ ρ sʷ ↦ renameⁿ ρ tⁿ
  renameCrossⁿ ρ (`∀ sⁿ) = `∀ (renameⁿ (extᵗ ρ) sⁿ)

  renameNonIdCrossⁿ : (ρ : Renameᵗ) → ∀ {s}
    → NonIdCrossⁿ s
    → NonIdCrossⁿ (renameᶜ ρ s)
  renameNonIdCrossⁿ ρ (sʷ ↦ˡ tⁿ) =
    renameNonIdʷ ρ sʷ ↦ˡ renameⁿ ρ tⁿ
  renameNonIdCrossⁿ ρ (sʷ ↦ʳ tⁿ) =
    renameʷ ρ sʷ ↦ʳ renameNonIdⁿ ρ tⁿ
  renameNonIdCrossⁿ ρ (`∀ sⁿ) =
    `∀ (renameNonIdⁿ (extᵗ ρ) sⁿ)

  renameGenSafe : (ρ : Renameᵗ) → ∀ {s}
    → GenSafe s
    → GenSafe (renameᶜ ρ s)
  renameGenSafe ρ (sʷ ↦ tⁿ) =
    renameʷ ρ sʷ ↦ renameⁿ ρ tⁿ
  renameGenSafe ρ (`∀ sⁿ) = `∀ (renameⁿ (extᵗ ρ) sⁿ)
  renameGenSafe ρ (gen sⁿ) =
    gen (renameGenSafe (extᵗ ρ) sⁿ)

  renameⁿ : (ρ : Renameᵗ) → ∀ {s}
    → Narrowing s
    → Narrowing (renameᶜ ρ s)
  renameⁿ ρ (cross sⁿ) = cross (renameCrossⁿ ρ sⁿ)
  renameⁿ ρ id = id
  renameⁿ ρ (gen sⁿ) = gen (renameGenSafe (extᵗ ρ) sⁿ)
  renameⁿ ρ (G ？) = renameᵍ ρ G ？
  renameⁿ ρ (G ？︔ sⁿ) =
    renameᵍ ρ G ？︔ renameNonIdCrossⁿ ρ sⁿ
  renameⁿ ρ (fun-？︔gen sⁿ) =
    fun-？︔gen (renameGenSafe (extᵗ ρ) sⁿ)
  renameⁿ ρ (seal α) = seal (ρ α)
  renameⁿ ρ (sⁿ ︔seal α) =
    renameNonIdⁿ ρ sⁿ ︔seal ρ α

  renameNonIdⁿ : (ρ : Renameᵗ) → ∀ {s}
    → NonIdⁿ s
    → NonIdⁿ (renameᶜ ρ s)
  renameNonIdⁿ ρ (cross sⁿ) =
    cross (renameNonIdCrossⁿ ρ sⁿ)
  renameNonIdⁿ ρ (gen sⁿ) =
    gen (renameGenSafe (extᵗ ρ) sⁿ)
  renameNonIdⁿ ρ (G ？) = renameᵍ ρ G ？
  renameNonIdⁿ ρ (G ？︔ sⁿ) =
    renameᵍ ρ G ？︔ renameNonIdCrossⁿ ρ sⁿ
  renameNonIdⁿ ρ (fun-？︔gen sⁿ) =
    fun-？︔gen (renameGenSafe (extᵗ ρ) sⁿ)
  renameNonIdⁿ ρ (seal α) = seal (ρ α)
  renameNonIdⁿ ρ (sⁿ ︔seal α) =
    renameNonIdⁿ ρ sⁿ ︔seal ρ α

  renameCrossʷ : (ρ : Renameᵗ) → ∀ {s}
    → Crossʷ s
    → Crossʷ (renameᶜ ρ s)
  renameCrossʷ ρ id = id
  renameCrossʷ ρ (sⁿ ↦ tʷ) = renameⁿ ρ sⁿ ↦ renameʷ ρ tʷ
  renameCrossʷ ρ (`∀ sʷ) = `∀ (renameʷ (extᵗ ρ) sʷ)

  renameNonIdCrossʷ : (ρ : Renameᵗ) → ∀ {s}
    → NonIdCrossʷ s
    → NonIdCrossʷ (renameᶜ ρ s)
  renameNonIdCrossʷ ρ (sⁿ ↦ˡ tʷ) =
    renameNonIdⁿ ρ sⁿ ↦ˡ renameʷ ρ tʷ
  renameNonIdCrossʷ ρ (sⁿ ↦ʳ tʷ) =
    renameⁿ ρ sⁿ ↦ʳ renameNonIdʷ ρ tʷ
  renameNonIdCrossʷ ρ (`∀ sʷ) =
    `∀ (renameNonIdʷ (extᵗ ρ) sʷ)

  renameInstSafe : (ρ : Renameᵗ) → ∀ {s}
    → InstSafe s
    → InstSafe (renameᶜ ρ s)
  renameInstSafe ρ (sⁿ ↦ tʷ) =
    renameⁿ ρ sⁿ ↦ renameʷ ρ tʷ
  renameInstSafe ρ (`∀ sʷ) = `∀ (renameʷ (extᵗ ρ) sʷ)
  renameInstSafe ρ (inst sʷ) =
    inst (renameInstSafe (extᵗ ρ) sʷ)

  renameʷ : (ρ : Renameᵗ) → ∀ {s}
    → Widening s
    → Widening (renameᶜ ρ s)
  renameʷ ρ (cross sʷ) = cross (renameCrossʷ ρ sʷ)
  renameʷ ρ id = id
  renameʷ ρ (inst sʷ) = inst (renameInstSafe (extᵗ ρ) sʷ)
  renameʷ ρ (G !) = renameᵍ ρ G !
  renameʷ ρ (sʷ ︔ G !) =
    renameNonIdCrossʷ ρ sʷ ︔ renameᵍ ρ G !
  renameʷ ρ (inst sʷ ︔★⇒★!) =
    Widening.inst_︔★⇒★! (renameInstSafe (extᵗ ρ) sʷ)
  renameʷ ρ (unseal α) = unseal (ρ α)
  renameʷ ρ (Widening.unseal_︔_ α sʷ) =
    Widening.unseal_︔_ (ρ α) (renameNonIdʷ ρ sʷ)

  renameNonIdʷ : (ρ : Renameᵗ) → ∀ {s}
    → NonIdʷ s
    → NonIdʷ (renameᶜ ρ s)
  renameNonIdʷ ρ (cross sʷ) =
    cross (renameNonIdCrossʷ ρ sʷ)
  renameNonIdʷ ρ (inst sʷ) =
    inst (renameInstSafe (extᵗ ρ) sʷ)
  renameNonIdʷ ρ (G !) = renameᵍ ρ G !
  renameNonIdʷ ρ (sʷ ︔ G !) =
    renameNonIdCrossʷ ρ sʷ ︔ renameᵍ ρ G !
  renameNonIdʷ ρ (inst sʷ ︔★⇒★!) =
    NonIdʷ.inst_︔★⇒★! (renameInstSafe (extᵗ ρ) sʷ)
  renameNonIdʷ ρ (unseal α) = unseal (ρ α)
  renameNonIdʷ ρ (NonIdʷ.unseal_︔_ α sʷ) =
    NonIdʷ.unseal_︔_ (ρ α) (renameNonIdʷ ρ sʷ)

------------------------------------------------------------------------
-- Grammar views and wrappers
------------------------------------------------------------------------

mutual
  nonIdⁿ? : ∀ {s} → Narrowing s → Maybe (NonIdⁿ s)
  nonIdⁿ? (cross sⁿ) with nonIdCrossⁿ? sⁿ
  nonIdⁿ? (cross sⁿ) | just sⁿ′ = just (cross sⁿ′)
  nonIdⁿ? (cross sⁿ) | nothing = nothing
  nonIdⁿ? id = nothing
  nonIdⁿ? (gen sⁿ) = just (gen sⁿ)
  nonIdⁿ? (G ？) = just (G ？)
  nonIdⁿ? (G ？︔ sⁿ) = just (G ？︔ sⁿ)
  nonIdⁿ? (fun-？︔gen sⁿ) = just (fun-？︔gen sⁿ)
  nonIdⁿ? (seal α) = just (seal α)
  nonIdⁿ? (sⁿ ︔seal α) = just (sⁿ ︔seal α)

  nonIdCrossⁿ? : ∀ {s} → Crossⁿ s → Maybe (NonIdCrossⁿ s)
  nonIdCrossⁿ? id = nothing
  nonIdCrossⁿ? (sʷ ↦ tⁿ) with nonIdʷ? sʷ
  nonIdCrossⁿ? (sʷ ↦ tⁿ) | just sʷ′ =
    just (sʷ′ ↦ˡ tⁿ)
  nonIdCrossⁿ? (sʷ ↦ tⁿ) | nothing with nonIdⁿ? tⁿ
  nonIdCrossⁿ? (sʷ ↦ tⁿ) | nothing | just tⁿ′ =
    just (sʷ ↦ʳ tⁿ′)
  nonIdCrossⁿ? (sʷ ↦ tⁿ) | nothing | nothing = nothing
  nonIdCrossⁿ? (`∀ sⁿ) with nonIdⁿ? sⁿ
  nonIdCrossⁿ? (`∀ sⁿ) | just sⁿ′ = just (`∀ sⁿ′)
  nonIdCrossⁿ? (`∀ sⁿ) | nothing = nothing

  nonIdʷ? : ∀ {s} → Widening s → Maybe (NonIdʷ s)
  nonIdʷ? (cross sʷ) with nonIdCrossʷ? sʷ
  nonIdʷ? (cross sʷ) | just sʷ′ = just (cross sʷ′)
  nonIdʷ? (cross sʷ) | nothing = nothing
  nonIdʷ? id = nothing
  nonIdʷ? (inst sʷ) = just (inst sʷ)
  nonIdʷ? (G !) = just (G !)
  nonIdʷ? (sʷ ︔ G !) = just (sʷ ︔ G !)
  nonIdʷ? (inst sʷ ︔★⇒★!) = just (inst sʷ ︔★⇒★!)
  nonIdʷ? (unseal α) = just (unseal α)
  nonIdʷ? (Widening.unseal_︔_ α sʷ) =
    just (NonIdʷ.unseal_︔_ α sʷ)

  nonIdCrossʷ? : ∀ {s} → Crossʷ s → Maybe (NonIdCrossʷ s)
  nonIdCrossʷ? id = nothing
  nonIdCrossʷ? (sⁿ ↦ tʷ) with nonIdⁿ? sⁿ
  nonIdCrossʷ? (sⁿ ↦ tʷ) | just sⁿ′ =
    just (sⁿ′ ↦ˡ tʷ)
  nonIdCrossʷ? (sⁿ ↦ tʷ) | nothing with nonIdʷ? tʷ
  nonIdCrossʷ? (sⁿ ↦ tʷ) | nothing | just tʷ′ =
    just (sⁿ ↦ʳ tʷ′)
  nonIdCrossʷ? (sⁿ ↦ tʷ) | nothing | nothing = nothing
  nonIdCrossʷ? (`∀ sʷ) with nonIdʷ? sʷ
  nonIdCrossʷ? (`∀ sʷ) | just sʷ′ = just (`∀ sʷ′)
  nonIdCrossʷ? (`∀ sʷ) | nothing = nothing

mutual
  nonIdⁿ→narrowing : ∀ {s} → NonIdⁿ s → Narrowing s
  nonIdⁿ→narrowing (cross sⁿ) = cross (nonIdCrossⁿ→cross sⁿ)
  nonIdⁿ→narrowing (gen sⁿ) = gen sⁿ
  nonIdⁿ→narrowing (G ？) = G ？
  nonIdⁿ→narrowing (G ？︔ sⁿ) = G ？︔ sⁿ
  nonIdⁿ→narrowing (fun-？︔gen sⁿ) = fun-？︔gen sⁿ
  nonIdⁿ→narrowing (seal α) = seal α
  nonIdⁿ→narrowing (sⁿ ︔seal α) = sⁿ ︔seal α

  nonIdCrossⁿ→cross : ∀ {s} → NonIdCrossⁿ s → Crossⁿ s
  nonIdCrossⁿ→cross (sʷ ↦ˡ tⁿ) =
    nonIdʷ→widening sʷ ↦ tⁿ
  nonIdCrossⁿ→cross (sʷ ↦ʳ tⁿ) =
    sʷ ↦ nonIdⁿ→narrowing tⁿ
  nonIdCrossⁿ→cross (`∀ sⁿ) = `∀ (nonIdⁿ→narrowing sⁿ)

  nonIdʷ→widening : ∀ {s} → NonIdʷ s → Widening s
  nonIdʷ→widening (cross sʷ) = cross (nonIdCrossʷ→cross sʷ)
  nonIdʷ→widening (inst sʷ) = inst sʷ
  nonIdʷ→widening (G !) = G !
  nonIdʷ→widening (sʷ ︔ G !) = sʷ ︔ G !
  nonIdʷ→widening (inst sʷ ︔★⇒★!) = inst sʷ ︔★⇒★!
  nonIdʷ→widening (unseal α) = unseal α
  nonIdʷ→widening (NonIdʷ.unseal_︔_ α sʷ) =
    Widening.unseal_︔_ α sʷ

  nonIdCrossʷ→cross : ∀ {s} → NonIdCrossʷ s → Crossʷ s
  nonIdCrossʷ→cross (sⁿ ↦ˡ tʷ) =
    nonIdⁿ→narrowing sⁿ ↦ tʷ
  nonIdCrossʷ→cross (sⁿ ↦ʳ tʷ) =
    sⁿ ↦ nonIdʷ→widening tʷ
  nonIdCrossʷ→cross (`∀ sʷ) = `∀ (nonIdʷ→widening sʷ)

genSafe→narrowing : ∀ {s} → GenSafe s → Narrowing s
genSafe→narrowing (sʷ ↦ tⁿ) = cross (sʷ ↦ tⁿ)
genSafe→narrowing (`∀ sⁿ) = cross (`∀ sⁿ)
genSafe→narrowing (gen sⁿ) = Narrowing.gen sⁿ

genSafe? : ∀ {s} → Narrowing s → Maybe (GenSafe s)
genSafe? (cross id) = nothing
genSafe? (cross (sʷ ↦ tⁿ)) = just (sʷ ↦ tⁿ)
genSafe? (cross (`∀ sⁿ)) = just (`∀ sⁿ)
genSafe? id = nothing
genSafe? (gen sⁿ) = just (GenSafe.gen sⁿ)
genSafe? (G ？) = nothing
genSafe? (G ？︔ sⁿ) = nothing
genSafe? (fun-？︔gen sⁿ) = nothing
genSafe? (seal α) = nothing
genSafe? (sⁿ ︔seal α) = nothing

instSafe→widening : ∀ {s} → InstSafe s → Widening s
instSafe→widening (sⁿ ↦ tʷ) = cross (sⁿ ↦ tʷ)
instSafe→widening (`∀ sʷ) = cross (`∀ sʷ)
instSafe→widening (inst sʷ) = Widening.inst sʷ

instSafe? : ∀ {s} → Widening s → Maybe (InstSafe s)
instSafe? (cross id) = nothing
instSafe? (cross (sⁿ ↦ tʷ)) = just (sⁿ ↦ tʷ)
instSafe? (cross (`∀ sʷ)) = just (`∀ sʷ)
instSafe? id = nothing
instSafe? (inst sʷ) = just (InstSafe.inst sʷ)
instSafe? (G !) = nothing
instSafe? (sʷ ︔ G !) = nothing
instSafe? (inst sʷ ︔★⇒★!) = nothing
instSafe? (unseal α) = nothing
instSafe? (Widening.unseal_︔_ α sʷ) = nothing

wrap-？ⁿ : ∀ {s}
  → (G : Tag)
  → Crossⁿ s
  → ∃[ u ] Narrowing u
wrap-？ⁿ {s = s} G sⁿ with nonIdCrossⁿ? sⁿ
wrap-？ⁿ {s = s} G sⁿ | just sⁿ′ =
  ((G ？) ︔ s) , (G ？︔ sⁿ′)
wrap-？ⁿ G sⁿ | nothing = (G ？) , (G ？)

wrap-sealⁿ : ∀ {s}
  → Narrowing s
  → (α : TyVar)
  → ∃[ u ] Narrowing u
wrap-sealⁿ {s = s} sⁿ α with nonIdⁿ? sⁿ
wrap-sealⁿ {s = s} sⁿ α | just sⁿ′ =
  (s ︔ Coercions.seal α) , (sⁿ′ ︔seal α)
wrap-sealⁿ sⁿ α | nothing =
  Coercions.seal α , Narrowing.seal α

wrap-!ʷ : ∀ {s}
  → Crossʷ s
  → (G : Tag)
  → ∃[ u ] Widening u
wrap-!ʷ {s = s} sʷ G with nonIdCrossʷ? sʷ
wrap-!ʷ {s = s} sʷ G | just sʷ′ =
  (s ︔ (G !)) , (sʷ′ ︔ G !)
wrap-!ʷ sʷ G | nothing = (G !) , (G !)

wrap-unsealʷ : (α : TyVar)
  → ∀ {s}
  → Widening s
  → ∃[ u ] Widening u
wrap-unsealʷ α {s = s} sʷ with nonIdʷ? sʷ
wrap-unsealʷ α {s = s} sʷ | just sʷ′ =
  (Coercions.unseal α ︔ s) , Widening.unseal_︔_ α sʷ′
wrap-unsealʷ α sʷ | nothing =
  Coercions.unseal α , Widening.unseal α

------------------------------------------------------------------------
-- Composition of Narrowings and Widenings
------------------------------------------------------------------------

infixl 7 _⨟ⁿ_
infixl 7 _⨟ʷ_

private
  infixr 6 _⇒ⁿ_
  infixr 6 _⇒ʷ_

  _⇒ⁿ_ : Maybe (∃[ u ] Widening u)
    → Maybe (∃[ v ] Narrowing v)
    → Maybe (∃[ c ] Crossⁿ c)
  (just (u , uʷ)) ⇒ⁿ (just (v , vⁿ)) =
    just ((u ↦ v) , (uʷ ↦ vⁿ))
  (just (u , uʷ)) ⇒ⁿ nothing = nothing
  nothing ⇒ⁿ (just (v , vⁿ)) = nothing
  nothing ⇒ⁿ nothing = nothing

  _⇒ʷ_ : Maybe (∃[ u ] Narrowing u)
    → Maybe (∃[ v ] Widening v)
    → Maybe (∃[ c ] Crossʷ c)
  (just (u , uⁿ)) ⇒ʷ (just (v , vʷ)) =
    just ((u ↦ v) , (uⁿ ↦ vʷ))
  (just (u , uⁿ)) ⇒ʷ nothing = nothing
  nothing ⇒ʷ (just (v , vʷ)) = nothing
  nothing ⇒ʷ nothing = nothing

  sizeᶜ : Coercion → ℕ
  sizeᶜ id = 1
  sizeᶜ (s ︔ t) = suc (sizeᶜ s + sizeᶜ t)
  sizeᶜ (s ↦ t) = suc (sizeᶜ s + sizeᶜ t)
  sizeᶜ (`∀ s) = suc (sizeᶜ s)
  sizeᶜ (G !) = 1
  sizeᶜ (G ？) = 1
  sizeᶜ (seal α) = 1
  sizeᶜ (unseal α) = 1
  sizeᶜ (gen s) = suc (sizeᶜ s)
  sizeᶜ (inst s) = suc (sizeᶜ s)
  sizeᶜ error = 1

  mutual
    composeⁿ : ∀ {s t}
      → ℕ
      → Narrowing s
      → Narrowing t
      → Maybe (∃[ u ] Narrowing u)
    composeⁿ zero sⁿ tⁿ = nothing
    composeⁿ {s = s} (suc fuel) sⁿ id = just (s , sⁿ)
    composeⁿ {s = s} (suc fuel) sⁿ (cross id) =
      just (s , sⁿ)
    composeⁿ {t = t} (suc fuel) id tⁿ = just (t , tⁿ)
    composeⁿ {t = t} (suc fuel) (cross id) tⁿ =
      just (t , tⁿ)
    composeⁿ (suc fuel) (cross sⁿ) (cross tⁿ)
        with composeCrossⁿ fuel sⁿ tⁿ
    composeⁿ (suc fuel) (cross sⁿ) (cross tⁿ)
        | just (u , uⁿ) =
      just (u , cross uⁿ)
    composeⁿ (suc fuel) (cross sⁿ) (cross tⁿ)
        | nothing = nothing
    composeⁿ (suc fuel) (G ？) (cross tⁿ) =
      just (wrap-？ⁿ G tⁿ)
    composeⁿ (suc fuel) (G ？︔ sⁿ) (cross tⁿ)
        with composeCrossⁿ fuel (nonIdCrossⁿ→cross sⁿ) tⁿ
    composeⁿ (suc fuel) (G ？︔ sⁿ) (cross tⁿ)
        | just (u , uⁿ) =
      just (wrap-？ⁿ G uⁿ)
    composeⁿ (suc fuel) (G ？︔ sⁿ) (cross tⁿ)
        | nothing = nothing
    composeⁿ (suc fuel) (gen sⁿ) (cross (`∀ tⁿ))
        with composeⁿ fuel (genSafe→narrowing sⁿ) tⁿ
    composeⁿ (suc fuel) (gen sⁿ) (cross (`∀ tⁿ))
        | just (u , uⁿ) with genSafe? uⁿ
    composeⁿ (suc fuel) (gen sⁿ) (cross (`∀ tⁿ))
        | just (u , uⁿ) | just uᵍ =
      just (Coercions.gen u , Narrowing.gen uᵍ)
    composeⁿ (suc fuel) (gen sⁿ) (cross (`∀ tⁿ))
        | just (u , uⁿ) | nothing = nothing
    composeⁿ (suc fuel) (gen sⁿ) (cross (`∀ tⁿ))
        | nothing = nothing
    composeⁿ (suc fuel) (fun-？︔gen sⁿ) (cross (`∀ tⁿ))
        with composeⁿ fuel (genSafe→narrowing sⁿ) tⁿ
    composeⁿ (suc fuel) (fun-？︔gen sⁿ) (cross (`∀ tⁿ))
        | just (u , uⁿ) with genSafe? uⁿ
    composeⁿ (suc fuel) (fun-？︔gen sⁿ) (cross (`∀ tⁿ))
        | just (u , uⁿ) | just uᵍ =
      just (((★⇒★ ？) ︔ Coercions.gen u) , fun-？︔gen uᵍ)
    composeⁿ (suc fuel) (fun-？︔gen sⁿ) (cross (`∀ tⁿ))
        | just (u , uⁿ) | nothing = nothing
    composeⁿ (suc fuel) (fun-？︔gen sⁿ) (cross (`∀ tⁿ))
        | nothing = nothing
    composeⁿ (suc fuel) (★⇒★ ？) (gen tⁿ) =
      just (((★⇒★ ？) ︔ Coercions.gen _) , fun-？︔gen tⁿ)
    composeⁿ (suc fuel) (cross sⁿ) (gen tⁿ)
        with composeⁿ fuel (renameⁿ suc (cross sⁿ))
               (genSafe→narrowing tⁿ)
    composeⁿ (suc fuel) (cross sⁿ) (gen tⁿ)
        | just (u , uⁿ) with genSafe? uⁿ
    composeⁿ (suc fuel) (cross sⁿ) (gen tⁿ)
        | just (u , uⁿ) | just uᵍ =
      just (Coercions.gen u , Narrowing.gen uᵍ)
    composeⁿ (suc fuel) (cross sⁿ) (gen tⁿ)
        | just (u , uⁿ) | nothing = nothing
    composeⁿ (suc fuel) (cross sⁿ) (gen tⁿ)
        | nothing = nothing
    composeⁿ (suc fuel) (gen sⁿ) (gen tⁿ)
        with composeⁿ fuel (renameⁿ suc (Narrowing.gen sⁿ))
               (genSafe→narrowing tⁿ)
    composeⁿ (suc fuel) (gen sⁿ) (gen tⁿ)
        | just (u , uⁿ) with genSafe? uⁿ
    composeⁿ (suc fuel) (gen sⁿ) (gen tⁿ)
        | just (u , uⁿ) | just uᵍ =
      just (Coercions.gen u , Narrowing.gen uᵍ)
    composeⁿ (suc fuel) (gen sⁿ) (gen tⁿ)
        | just (u , uⁿ) | nothing = nothing
    composeⁿ (suc fuel) (gen sⁿ) (gen tⁿ)
        | nothing = nothing
    composeⁿ (suc fuel) (★⇒★ ？︔ sⁿ) (gen tⁿ)
        with composeⁿ fuel
               (renameⁿ suc (cross (nonIdCrossⁿ→cross sⁿ)))
               (genSafe→narrowing tⁿ)
    composeⁿ (suc fuel) (★⇒★ ？︔ sⁿ) (gen tⁿ)
        | just (u , uⁿ) with genSafe? uⁿ
    composeⁿ (suc fuel) (★⇒★ ？︔ sⁿ) (gen tⁿ)
        | just (u , uⁿ) | just uᵍ =
      just (((★⇒★ ？) ︔ Coercions.gen u) , fun-？︔gen uᵍ)
    composeⁿ (suc fuel) (★⇒★ ？︔ sⁿ) (gen tⁿ)
        | just (u , uⁿ) | nothing = nothing
    composeⁿ (suc fuel) (★⇒★ ？︔ sⁿ) (gen tⁿ)
        | nothing = nothing
    composeⁿ (suc fuel) (fun-？︔gen sⁿ) (gen tⁿ)
        with composeⁿ fuel (renameⁿ suc (Narrowing.gen sⁿ))
               (genSafe→narrowing tⁿ)
    composeⁿ (suc fuel) (fun-？︔gen sⁿ) (gen tⁿ)
        | just (u , uⁿ) with genSafe? uⁿ
    composeⁿ (suc fuel) (fun-？︔gen sⁿ) (gen tⁿ)
        | just (u , uⁿ) | just uᵍ =
      just (((★⇒★ ？) ︔ Coercions.gen u) , fun-？︔gen uᵍ)
    composeⁿ (suc fuel) (fun-？︔gen sⁿ) (gen tⁿ)
        | just (u , uⁿ) | nothing = nothing
    composeⁿ (suc fuel) (fun-？︔gen sⁿ) (gen tⁿ)
        | nothing = nothing
    composeⁿ (suc fuel) sⁿ (seal α) =
      just (wrap-sealⁿ sⁿ α)
    composeⁿ (suc fuel) sⁿ (tⁿ ︔seal α)
        with composeⁿ fuel sⁿ (nonIdⁿ→narrowing tⁿ)
    composeⁿ (suc fuel) sⁿ (tⁿ ︔seal α)
        | just (u , uⁿ) =
      just (wrap-sealⁿ uⁿ α)
    composeⁿ (suc fuel) sⁿ (tⁿ ︔seal α)
        | nothing = nothing
    composeⁿ (suc fuel) sⁿ tⁿ = nothing

    composeCrossⁿ : ∀ {s t}
      → ℕ
      → Crossⁿ s
      → Crossⁿ t
      → Maybe (∃[ u ] Crossⁿ u)
    composeCrossⁿ zero sⁿ tⁿ = nothing
    composeCrossⁿ {s = s} (suc fuel) sⁿ id =
      just (s , sⁿ)
    composeCrossⁿ {t = t} (suc fuel) id tⁿ =
      just (t , tⁿ)
    composeCrossⁿ (suc fuel) (s₁ʷ ↦ s₂ⁿ) (t₁ʷ ↦ t₂ⁿ) =
      composeʷ fuel t₁ʷ s₁ʷ ⇒ⁿ composeⁿ fuel s₂ⁿ t₂ⁿ
    composeCrossⁿ (suc fuel) (`∀ sⁿ) (`∀ tⁿ)
        with composeⁿ fuel sⁿ tⁿ
    composeCrossⁿ (suc fuel) (`∀ sⁿ) (`∀ tⁿ)
        | just (u , uⁿ) =
      just (`∀ u , `∀ uⁿ)
    composeCrossⁿ (suc fuel) (`∀ sⁿ) (`∀ tⁿ)
        | nothing = nothing
    composeCrossⁿ (suc fuel) (s₁ʷ ↦ s₂ⁿ) (`∀ tⁿ) =
      nothing
    composeCrossⁿ (suc fuel) (`∀ sⁿ) (t₁ʷ ↦ t₂ⁿ) =
      nothing

    composeʷ : ∀ {s t}
      → ℕ
      → Widening s
      → Widening t
      → Maybe (∃[ u ] Widening u)
    composeʷ zero sʷ tʷ = nothing
    composeʷ {s = s} (suc fuel) sʷ id = just (s , sʷ)
    composeʷ {s = s} (suc fuel) sʷ (cross id) =
      just (s , sʷ)
    composeʷ {t = t} (suc fuel) id tʷ = just (t , tʷ)
    composeʷ {t = t} (suc fuel) (cross id) tʷ =
      just (t , tʷ)
    composeʷ (suc fuel) (cross sʷ) (cross tʷ)
        with composeCrossʷ fuel sʷ tʷ
    composeʷ (suc fuel) (cross sʷ) (cross tʷ)
        | just (u , uʷ) =
      just (u , cross uʷ)
    composeʷ (suc fuel) (cross sʷ) (cross tʷ)
        | nothing = nothing
    composeʷ (suc fuel) (cross sʷ) (G !) =
      just (wrap-!ʷ sʷ G)
    composeʷ (suc fuel) (cross sʷ) (tʷ ︔ G !)
        with composeCrossʷ fuel sʷ (nonIdCrossʷ→cross tʷ)
    composeʷ (suc fuel) (cross sʷ) (tʷ ︔ G !)
        | just (u , uʷ) =
      just (wrap-!ʷ uʷ G)
    composeʷ (suc fuel) (cross sʷ) (tʷ ︔ G !)
        | nothing = nothing
    composeʷ (suc fuel) (cross (`∀ sʷ)) (inst tʷ)
        with composeʷ fuel sʷ (instSafe→widening tʷ)
    composeʷ (suc fuel) (cross (`∀ sʷ)) (inst tʷ)
        | just (u , uʷ) with instSafe? uʷ
    composeʷ (suc fuel) (cross (`∀ sʷ)) (inst tʷ)
        | just (u , uʷ) | just uⁱ =
      just (Coercions.inst u , Widening.inst uⁱ)
    composeʷ (suc fuel) (cross (`∀ sʷ)) (inst tʷ)
        | just (u , uʷ) | nothing = nothing
    composeʷ (suc fuel) (cross (`∀ sʷ)) (inst tʷ)
        | nothing = nothing
    composeʷ (suc fuel) (inst sʷ) (cross tʷ)
        with composeʷ fuel (instSafe→widening sʷ)
               (renameʷ suc (cross tʷ))
    composeʷ (suc fuel) (inst sʷ) (cross tʷ)
        | just (u , uʷ) with instSafe? uʷ
    composeʷ (suc fuel) (inst sʷ) (cross tʷ)
        | just (u , uʷ) | just uⁱ =
      just (Coercions.inst u , Widening.inst uⁱ)
    composeʷ (suc fuel) (inst sʷ) (cross tʷ)
        | just (u , uʷ) | nothing = nothing
    composeʷ (suc fuel) (inst sʷ) (cross tʷ)
        | nothing = nothing
    composeʷ (suc fuel) (inst sʷ) (inst tʷ)
        with composeʷ fuel (instSafe→widening sʷ)
               (renameʷ suc (Widening.inst tʷ))
    composeʷ (suc fuel) (inst sʷ) (inst tʷ)
        | just (u , uʷ) with instSafe? uʷ
    composeʷ (suc fuel) (inst sʷ) (inst tʷ)
        | just (u , uʷ) | just uⁱ =
      just (Coercions.inst u , Widening.inst uⁱ)
    composeʷ (suc fuel) (inst sʷ) (inst tʷ)
        | just (u , uʷ) | nothing = nothing
    composeʷ (suc fuel) (inst sʷ) (inst tʷ)
        | nothing = nothing
    composeʷ (suc fuel) (inst sʷ) (★⇒★ !) =
      just ((Coercions.inst _ ︔ (★⇒★ !)) , inst sʷ ︔★⇒★!)
    composeʷ (suc fuel) (inst sʷ) (tʷ ︔ ★⇒★ !)
        with composeʷ fuel (instSafe→widening sʷ)
               (renameʷ suc (cross (nonIdCrossʷ→cross tʷ)))
    composeʷ (suc fuel) (inst sʷ) (tʷ ︔ ★⇒★ !)
        | just (u , uʷ) with instSafe? uʷ
    composeʷ (suc fuel) (inst sʷ) (tʷ ︔ ★⇒★ !)
        | just (u , uʷ) | just uⁱ =
      just ((Coercions.inst u ︔ (★⇒★ !)) , inst uⁱ ︔★⇒★!)
    composeʷ (suc fuel) (inst sʷ) (tʷ ︔ ★⇒★ !)
        | just (u , uʷ) | nothing = nothing
    composeʷ (suc fuel) (inst sʷ) (tʷ ︔ ★⇒★ !)
        | nothing = nothing
    composeʷ (suc fuel) (inst sʷ) (inst tʷ ︔★⇒★!)
        with composeʷ fuel (instSafe→widening sʷ)
               (renameʷ suc (Widening.inst tʷ))
    composeʷ (suc fuel) (inst sʷ) (inst tʷ ︔★⇒★!)
        | just (u , uʷ) with instSafe? uʷ
    composeʷ (suc fuel) (inst sʷ) (inst tʷ ︔★⇒★!)
        | just (u , uʷ) | just uⁱ =
      just ((Coercions.inst u ︔ (★⇒★ !)) , inst uⁱ ︔★⇒★!)
    composeʷ (suc fuel) (inst sʷ) (inst tʷ ︔★⇒★!)
        | just (u , uʷ) | nothing = nothing
    composeʷ (suc fuel) (inst sʷ) (inst tʷ ︔★⇒★!)
        | nothing = nothing
    composeʷ (suc fuel) sʷ (inst tʷ ︔★⇒★!)
        with composeʷ fuel sʷ (Widening.inst tʷ)
    composeʷ (suc fuel) sʷ (inst tʷ ︔★⇒★!)
        | just (u , uʷ) with composeʷ fuel uʷ (★⇒★ !)
    composeʷ (suc fuel) sʷ (inst tʷ ︔★⇒★!)
        | just (u , uʷ) | just (v , vʷ) =
      just (v , vʷ)
    composeʷ (suc fuel) sʷ (inst tʷ ︔★⇒★!)
        | just (u , uʷ) | nothing = nothing
    composeʷ (suc fuel) sʷ (inst tʷ ︔★⇒★!)
        | nothing = nothing
    composeʷ (suc fuel) (unseal α) tʷ =
      just (wrap-unsealʷ α tʷ)
    composeʷ (suc fuel) (Widening.unseal_︔_ α sʷ) tʷ
        with composeʷ fuel (nonIdʷ→widening sʷ) tʷ
    composeʷ (suc fuel) (Widening.unseal_︔_ α sʷ) tʷ
        | just (u , uʷ) =
      just (wrap-unsealʷ α uʷ)
    composeʷ (suc fuel) (Widening.unseal_︔_ α sʷ) tʷ
        | nothing = nothing
    composeʷ (suc fuel) sʷ tʷ = nothing

    composeCrossʷ : ∀ {s t}
      → ℕ
      → Crossʷ s
      → Crossʷ t
      → Maybe (∃[ u ] Crossʷ u)
    composeCrossʷ zero sʷ tʷ = nothing
    composeCrossʷ {s = s} (suc fuel) sʷ id =
      just (s , sʷ)
    composeCrossʷ {t = t} (suc fuel) id tʷ =
      just (t , tʷ)
    composeCrossʷ (suc fuel) (s₁ⁿ ↦ s₂ʷ) (t₁ⁿ ↦ t₂ʷ) =
      composeⁿ fuel t₁ⁿ s₁ⁿ ⇒ʷ composeʷ fuel s₂ʷ t₂ʷ
    composeCrossʷ (suc fuel) (`∀ sʷ) (`∀ tʷ)
        with composeʷ fuel sʷ tʷ
    composeCrossʷ (suc fuel) (`∀ sʷ) (`∀ tʷ)
        | just (u , uʷ) =
      just (`∀ u , `∀ uʷ)
    composeCrossʷ (suc fuel) (`∀ sʷ) (`∀ tʷ)
        | nothing = nothing
    composeCrossʷ (suc fuel) (s₁ⁿ ↦ s₂ʷ) (`∀ tʷ) =
      nothing
    composeCrossʷ (suc fuel) (`∀ sʷ) (t₁ⁿ ↦ t₂ʷ) =
      nothing

_⨟ⁿ_ : ∀ {s t} → Narrowing s → Narrowing t → Maybe (∃[ u ] Narrowing u)
sⁿ  ⨟ⁿ tⁿ =
  composeⁿ (suc (sizeᶜ (coercionⁿ sⁿ) + sizeᶜ (coercionⁿ tⁿ))) sⁿ tⁿ

_⨟ʷ_ : ∀ {s t} → Widening s → Widening t → Maybe (∃[ u ] Widening u)
sʷ ⨟ʷ tʷ =
  composeʷ (suc (sizeᶜ (coercionʷ sʷ) + sizeᶜ (coercionʷ tʷ))) sʷ tʷ

