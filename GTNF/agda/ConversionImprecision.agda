module ConversionImprecision where

-- File Charter:
--   * STRUCTURAL CONVERSION IMPRECISION `c ⊑ c′` (design.md D17),
--     read in a `World` whose left and right contexts are the two
--     conversion contexts.  The mutually defined `MidImp`, `TailImp`
--     and `ConvImp` follow Conversion's three-sort normal-form grammar.
--   * CANDIDATE CLAUSES.  Identities compare their types through the
--     world's center and embeddings (`μʷ W ⊢ embᴸ W A ⊑ embᴿ W A′`; no
--     clause reads the pending names `πʷ`, design.md D27: they belong to
--     the term relation); arrows compare both components in the same
--     direction;
--     two universals extend the world by a both-sided `X⊑X` binder;
--     matched seals and unseals name one center name; chains compare
--     componentwise.
--   * THE ★ CLAUSES (design.md D18), mirroring type imprecision's
--     `X ⊑ ★` and `∀⊑`.  A seal or unseal of a left name marked `X⊑★`
--     may be absent on the right: `conv-seal⊑id★`, `conv-unseal⊑id★`
--     (C23a B3 compares `−X → (−Y → +X)` with
--     `id(★) → (−Y → id(★))`), and their chain forms
--     `conv-⨾seal⊑` (`t ⨾seal X ⊑ t′` from `t ⊑ t′`) and
--     `conv-unseal⨾⊑` (`unseal X ⨾ c ⊑ c′` from `c ⊑ c′`), which a
--     left-only `Merge` can produce.  `conv-∀⊑` opens a left-only
--     universal at `X⊑★` (C23b B0 compares
--     `∀Z.(−Y → (id(Z) → +Y))` with `−X → (id(★) → +X)`).
--   * DEFINITIONS ONLY.  Conversion typing remains in Conversion;
--     TermImprecision supplies the independently checked typing side
--     premises and chooses the conversion-context world.

open import Data.Nat using (ℕ)
open import Ctx using (Ctxᵗ; _∋ˡ_:=_)
open import Types using (Ty; ★)
open import Conversion
  using (Mid; Tail; Conv; id; _↦_; `∀; mid; seal; _⨾seal_; tail;
         unseal; unseal_⨾_; ⌞_⌟)
open import Imprecision using (X⊑X; X⊑★; _⊢_⊑_)
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
    conv-id⊑id : μʷ W ⊢ embᴸ W A ⊑ embᴿ W A′
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

    -- the chain form: the last seal of a precise chain is absent
    conv-⨾seal⊑ : TailImp W t t′ → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
        --------------------------------
      → TailImp W (t ⨾seal X) t′

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

    -- the chain form: the first unseal of a precise chain is absent
    conv-unseal⨾⊑ : μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★ → ConvImp W c c′
        --------------------------------
      → ConvImp W (unseal X ⨾ c) c′

_⊢ᵐ_⊑_ : World Δ Δ′ → Mid → Mid → Set
W ⊢ᵐ g ⊑ g′ = MidImp W g g′

_⊢ᵀ_⊑_ : World Δ Δ′ → Tail → Tail → Set
W ⊢ᵀ t ⊑ t′ = TailImp W t t′

_⊢ᶜ_⊑_ : World Δ Δ′ → Conv → Conv → Set
W ⊢ᶜ c ⊑ c′ = ConvImp W c c′
