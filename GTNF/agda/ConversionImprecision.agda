module ConversionImprecision where

-- File Charter:
--   * STRUCTURAL CONVERSION IMPRECISION `c ⊑ c′` (design.md D17),
--     read in a `World` whose left and right contexts are the two
--     conversion contexts.  The mutually defined `MidImp`, `TailImp`
--     and `ConvImp` follow Conversion's three-sort normal-form grammar.
--   * CANDIDATE CLAUSES.  Identities compare their types through the
--     world; arrows compare both components in the same direction;
--     two universals extend the world by a both-sided `X⊑X` binder;
--     matched seals and unseals name one center name; chains compare
--     componentwise.
--   * EXTENSIONS REQUIRED BY THE 28 EXAMPLE PAIRS:
--     - DEVIATION `conv-seal⊑id★` and `conv-unseal⊑id★`: C23a B3
--       compares `−X → (−Y → +X)` with
--       `id(★) → (−Y → id(★))`.  Each clause requires the left name's
--       center mark to be `X⊑★`.
--     - DEVIATION `conv-∀⊑`: C23b B0 compares
--       `∀Z.(−Y → (id(Z) → +Y))` with
--       `−X → (id(★) → +X)`.  Its premise is read under a left-only
--       binder, where `Z ⊑ ★`.
--   * DEFINITIONS ONLY.  Conversion typing remains in Conversion;
--     TermImprecision supplies the independently checked typing side
--     premises and chooses the conversion-context world.

open import Data.Nat using (ℕ)
open import Ctx using (Ctxᵗ; _∋ˡ_:=_)
open import Types using (Ty; ★)
open import Conversion
  using (Mid; Tail; Conv; id; _↦_; `∀; mid; seal; _⨾seal_; tail;
         unseal; unseal_⨾_; ⌞_⌟)
open import Imprecision using (X⊑X; X⊑★)
open import ImprecisionWorld

private
  variable
    Δ Δ′ : Ctxᵗ
    A A′ : Ty
    X X′ : ℕ
    g g′ : Mid
    t t′ : Tail
    c c′ s s′ : Conv

infix 4 _⊢ᵐ_⊑_ _⊢ᵀ_⊑_ _⊢ᶜ_⊑_

mutual
  data MidImp {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′)
      : Mid → Mid → Set where
    conv-id⊑id : A ⊑ᵂ⟨ W ⟩ A′
        --------------------------------
      → MidImp W (id A) (id A′)

    conv-↦⊑↦ : ConvImp W s s′ → ConvImp W c c′
        --------------------------------
      → MidImp W (s ↦ c) (s′ ↦ c′)

    conv-∀⊑∀ : ConvImp (W ⊕ X⊑X) c c′
        --------------------------------
      → MidImp W (`∀ c) (`∀ c′)

    -- C23b B0: the right conversion has no matching universal layer.
    conv-∀⊑ : ConvImp (W ⊕ᴸ) c ⌞ g′ ⌟
        --------------------------------
      → MidImp W (`∀ c) g′

  data TailImp {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′)
      : Tail → Tail → Set where
    conv-mid⊑mid : MidImp W g g′
        --------------------------------
      → TailImp W (mid g) (mid g′)

    conv-seal⊑seal : Joins W X X′
        --------------------------------
      → TailImp W (seal X) (seal X′)

    conv-⨾seal⊑⨾seal : TailImp W t t′ → Joins W X X′
        --------------------------------
      → TailImp W (t ⨾seal X) (t′ ⨾seal X′)

    -- C23a B3: a precise seal is absent from the dynamic conversion.
    conv-seal⊑id★ : μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
        --------------------------------
      → TailImp W (seal X) (mid (id ★))

  data ConvImp {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′)
      : Conv → Conv → Set where
    conv-tail⊑tail : TailImp W t t′
        --------------------------------
      → ConvImp W (tail t) (tail t′)

    conv-unseal⊑unseal : Joins W X X′
        --------------------------------
      → ConvImp W (unseal X) (unseal X′)

    conv-unseal⨾⊑unseal⨾ : Joins W X X′ → ConvImp W c c′
        --------------------------------
      → ConvImp W (unseal X ⨾ c) (unseal X′ ⨾ c′)

    -- C23a B3: a precise unseal is absent from the dynamic conversion.
    conv-unseal⊑id★ : μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
        --------------------------------
      → ConvImp W (unseal X) ⌞ id ★ ⌟

_⊢ᵐ_⊑_ : World Δ Δ′ → Mid → Mid → Set
W ⊢ᵐ g ⊑ g′ = MidImp W g g′

_⊢ᵀ_⊑_ : World Δ Δ′ → Tail → Tail → Set
W ⊢ᵀ t ⊑ t′ = TailImp W t t′

_⊢ᶜ_⊑_ : World Δ Δ′ → Conv → Conv → Set
W ⊢ᶜ c ⊑ c′ = ConvImp W c c′
