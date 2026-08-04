module TypeRelocate where

-- File Charter:
--   * Defines intrinsically scoped imprecision contexts.
--   * Defines relocation of types between two related type contexts.
--   * Relates only variables synchronized on the left and right.
--   * Excludes dynamic-type narrowing, coercions, and type-store structure.
--   * Exposes endpoint well-formedness for type relocation.

open import Data.Nat using (_<_; zero; suc; z≤n; s≤s)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (subst)

open import Types
open import Coercions using
  ( ModeEnv
  ; id-onlyᵈ
  ; extᵈ
  ; genᵈ
  )
open import proof.TypeInTypeSubst using
  ( TyRenameWf
  ; TyRenameWf-ext
  ; TyRenameWf-suc
  ; renameᵗ-id
  ; renameᵗ-preserves-WfTy
  )

------------------------------------------------------------------------
-- Intrinsically scoped imprecision contexts
------------------------------------------------------------------------

data ImpCtx : TyCtx → TyCtx → Set where
  []ᵢ : ImpCtx zero zero

  bothᵢ : ∀ {Δᴸ Δᴿ}
    → ImpCtx Δᴸ Δᴿ
    → ImpCtx (suc Δᴸ) (suc Δᴿ)

  freshᴸ : ∀ {Δᴸ Δᴿ}
    → ImpCtx Δᴸ Δᴿ
    → ImpCtx (suc Δᴸ) Δᴿ

  freshᴿ : ∀ {Δᴸ Δᴿ}
    → ImpCtx Δᴸ Δᴿ
    → ImpCtx Δᴸ (suc Δᴿ)

infix 4 _⊢_≈ˣ_
infix 4 _⊢_ˣᴿ

data _⊢_≈ˣ_ : ∀ {Δᴸ Δᴿ}
    → ImpCtx Δᴸ Δᴿ → TyVar → TyVar → Set where

  hereᵢ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
      ------------------------------------
    → bothᵢ Φ ⊢ zero ≈ˣ zero

  both-thereᵢ : ∀ {Δᴸ Δᴿ X Y} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢ X ≈ˣ Y
      ----------------------------------------
    → bothᵢ Φ ⊢ suc X ≈ˣ suc Y

  freshᴸ-thereᵢ : ∀ {Δᴸ Δᴿ X Y} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢ X ≈ˣ Y
      ----------------------------------------
    → freshᴸ Φ ⊢ suc X ≈ˣ Y

  freshᴿ-thereᵢ : ∀ {Δᴸ Δᴿ X Y} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢ X ≈ˣ Y
      ----------------------------------------
    → freshᴿ Φ ⊢ X ≈ˣ suc Y

------------------------------------------------------------------------
-- Variables present only on the right
------------------------------------------------------------------------

data _⊢_ˣᴿ : ∀ {Δᴸ Δᴿ}
    → ImpCtx Δᴸ Δᴿ → TyVar → Set where

  hereᴿ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
      --------------------
    → freshᴿ Φ ⊢ zero ˣᴿ

  both-thereᴿ : ∀ {Δᴸ Δᴿ Y} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢ Y ˣᴿ
      -----------------------
    → bothᵢ Φ ⊢ suc Y ˣᴿ

  freshᴸ-thereᴿ : ∀ {Δᴸ Δᴿ Y} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢ Y ˣᴿ
      --------------------
    → freshᴸ Φ ⊢ Y ˣᴿ

  freshᴿ-thereᴿ : ∀ {Δᴸ Δᴿ Y} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢ Y ˣᴿ
      ------------------------
    → freshᴿ Φ ⊢ suc Y ˣᴿ

≈ˣ-left-bound : ∀ {Δᴸ Δᴿ X Y} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ X ≈ˣ Y
  → X < Δᴸ
≈ˣ-left-bound hereᵢ = s≤s z≤n
≈ˣ-left-bound (both-thereᵢ X≈Y) = s≤s (≈ˣ-left-bound X≈Y)
≈ˣ-left-bound (freshᴸ-thereᵢ X≈Y) = s≤s (≈ˣ-left-bound X≈Y)
≈ˣ-left-bound (freshᴿ-thereᵢ X≈Y) = ≈ˣ-left-bound X≈Y

≈ˣ-right-bound : ∀ {Δᴸ Δᴿ X Y} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ X ≈ˣ Y
  → Y < Δᴿ
≈ˣ-right-bound hereᵢ = s≤s z≤n
≈ˣ-right-bound (both-thereᵢ X≈Y) = s≤s (≈ˣ-right-bound X≈Y)
≈ˣ-right-bound (freshᴸ-thereᵢ X≈Y) = ≈ˣ-right-bound X≈Y
≈ˣ-right-bound (freshᴿ-thereᵢ X≈Y) = s≤s (≈ˣ-right-bound X≈Y)

ˣᴿ-bound : ∀ {Δᴸ Δᴿ Y} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ Y ˣᴿ
  → Y < Δᴿ
ˣᴿ-bound hereᴿ = s≤s z≤n
ˣᴿ-bound (both-thereᴿ Yᴿ) = s≤s (ˣᴿ-bound Yᴿ)
ˣᴿ-bound (freshᴸ-thereᴿ Yᴿ) = ˣᴿ-bound Yᴿ
ˣᴿ-bound (freshᴿ-thereᴿ Yᴿ) = s≤s (ˣᴿ-bound Yᴿ)

idᵢ : ∀ Δ → ImpCtx Δ Δ
idᵢ zero = []ᵢ
idᵢ (suc Δ) = bothᵢ (idᵢ Δ)

------------------------------------------------------------------------
-- The coercion mode induced on the right
------------------------------------------------------------------------

precisionMode : ∀ {Δᴸ Δᴿ} → ImpCtx Δᴸ Δᴿ → ModeEnv
precisionMode []ᵢ = id-onlyᵈ
precisionMode (bothᵢ Φ) = extᵈ (precisionMode Φ)
precisionMode (freshᴸ Φ) = precisionMode Φ
precisionMode (freshᴿ Φ) = genᵈ (precisionMode Φ)

------------------------------------------------------------------------
-- Smart extension at a polymorphic boundary
------------------------------------------------------------------------

data SmartExtensionᵢ : ∀ {Δᴸ Δᴿ}
    → (Φ : ImpCtx Δᴸ Δᴿ)
    → ImpCtx Δᴸ (suc Δᴿ)
    → Set where

  freshᵢ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
      -------------------------------------
    → SmartExtensionᵢ Φ (freshᴿ Φ)

  reuseᵢ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
      -------------------------------------------
    → SmartExtensionᵢ (freshᴸ Φ) (bothᵢ Φ)

instance
  fresh-extensionᵢ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → SmartExtensionᵢ Φ (freshᴿ Φ)
  fresh-extensionᵢ = freshᵢ

------------------------------------------------------------------------
-- Atomic type relocation
------------------------------------------------------------------------

infix 4 _⊢_≈ᵃ_

data _⊢_≈ᵃ_ : ∀ {Δᴸ Δᴿ A B}
    → ImpCtx Δᴸ Δᴿ → Atom A → Atom B → Set where

  varᵃ : ∀ {Δᴸ Δᴿ X Y} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢ X ≈ˣ Y
      -------------------
    → Φ ⊢ ＇ X ≈ᵃ ＇ Y

  baseᵃ : ∀ {Δᴸ Δᴿ ι} {Φ : ImpCtx Δᴸ Δᴿ}
      --------------------
    → Φ ⊢ ‵ ι ≈ᵃ ‵ ι

  starᵃ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
      -------------
    → Φ ⊢ ★ ≈ᵃ ★

------------------------------------------------------------------------
-- Type relocation
------------------------------------------------------------------------

infix 4 _⊢_≈_
infixr 6 _⇒ʳ_

data _⊢_≈_ {Δᴸ Δᴿ} (Φ : ImpCtx Δᴸ Δᴿ) :
    Ty → Ty → Set where

  idᵃ : ∀ {A B} (a : Atom A) (b : Atom B)
    → WfTy Δᴸ A
    → WfTy Δᴿ B
    → Φ ⊢ a ≈ᵃ b
      ----------------
    → Φ ⊢ A ≈ B

  _⇒ʳ_ : ∀ {A A′ B B′}
    → Φ ⊢ A ≈ A′
    → Φ ⊢ B ≈ B′
      ----------------------------
    → Φ ⊢ (A ⇒ B) ≈ (A′ ⇒ B′)

  ∀ʳ_ : ∀ {A B}
    → bothᵢ Φ ⊢ A ≈ B
      -----------------------
    → Φ ⊢ (`∀ A) ≈ (`∀ B)

------------------------------------------------------------------------
-- Endpoint well-formedness
------------------------------------------------------------------------

≈-src-wf : ∀ {Δᴸ Δᴿ A B} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ A ≈ B
  → WfTy Δᴸ A
≈-src-wf (idᵃ _ _ hA _ _) = hA
≈-src-wf (p ⇒ʳ q) = wf⇒ (≈-src-wf p) (≈-src-wf q)
≈-src-wf (∀ʳ p) = wf∀ (≈-src-wf p)

≈-tgt-wf : ∀ {Δᴸ Δᴿ A B} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ A ≈ B
  → WfTy Δᴿ B
≈-tgt-wf (idᵃ _ _ _ hB _) = hB
≈-tgt-wf (p ⇒ʳ q) = wf⇒ (≈-tgt-wf p) (≈-tgt-wf q)
≈-tgt-wf (∀ʳ p) = wf∀ (≈-tgt-wf p)

≈-wf : ∀ {Δᴸ Δᴿ A B} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ A ≈ B
  → WfTy Δᴸ A × WfTy Δᴿ B
≈-wf p = ≈-src-wf p , ≈-tgt-wf p

------------------------------------------------------------------------
-- Relocation under type renaming
------------------------------------------------------------------------

private

  record RenameRelocation
      {Δᴸ Δᴿ Δᴸ′ Δᴿ′}
      (ρᴸ ρᴿ : Renameᵗ)
      (Φ : ImpCtx Δᴸ Δᴿ)
      (Ψ : ImpCtx Δᴸ′ Δᴿ′) : Set where
    constructor rename-relocation
    field
      left-wfᵣ : TyRenameWf Δᴸ Δᴸ′ ρᴸ
      right-wfᵣ : TyRenameWf Δᴿ Δᴿ′ ρᴿ
      pairedᵣ : ∀ {X Y}
        → Φ ⊢ X ≈ˣ Y
        → Ψ ⊢ ρᴸ X ≈ˣ ρᴿ Y

  open RenameRelocation

  bothᵣ : ∀ {Δᴸ Δᴿ Δᴸ′ Δᴿ′ ρᴸ ρᴿ}
      {Φ : ImpCtx Δᴸ Δᴿ} {Ψ : ImpCtx Δᴸ′ Δᴿ′}
    → RenameRelocation ρᴸ ρᴿ Φ Ψ
    → RenameRelocation (extᵗ ρᴸ) (extᵗ ρᴿ)
        (bothᵢ Φ) (bothᵢ Ψ)
  bothᵣ (rename-relocation hᴸ hᴿ paired) =
    rename-relocation (TyRenameWf-ext hᴸ) (TyRenameWf-ext hᴿ)
      both-paired
    where
    both-paired : ∀ {X Y}
      → bothᵢ _ ⊢ X ≈ˣ Y
      → bothᵢ _ ⊢ extᵗ _ X ≈ˣ extᵗ _ Y
    both-paired hereᵢ = hereᵢ
    both-paired (both-thereᵢ X≈Y) = both-thereᵢ (paired X≈Y)

  freshᴿᵣ : ∀ {Δᴸ Δᴿ Δᴸ′ Δᴿ′ ρᴸ ρᴿ}
      {Φ : ImpCtx Δᴸ Δᴿ} {Ψ : ImpCtx Δᴸ′ Δᴿ′}
    → RenameRelocation ρᴸ ρᴿ Φ Ψ
    → RenameRelocation ρᴸ (extᵗ ρᴿ)
        (freshᴿ Φ) (freshᴿ Ψ)
  freshᴿᵣ (rename-relocation hᴸ hᴿ paired) =
    rename-relocation hᴸ (TyRenameWf-ext hᴿ)
      fresh-paired
    where
    fresh-paired : ∀ {X Y}
      → freshᴿ _ ⊢ X ≈ˣ Y
      → freshᴿ _ ⊢ _ ≈ˣ extᵗ _ Y
    fresh-paired (freshᴿ-thereᵢ X≈Y) =
      freshᴿ-thereᵢ (paired X≈Y)

  rename-≈ : ∀ {Δᴸ Δᴿ Δᴸ′ Δᴿ′ ρᴸ ρᴿ A B}
      {Φ : ImpCtx Δᴸ Δᴿ} {Ψ : ImpCtx Δᴸ′ Δᴿ′}
    → RenameRelocation ρᴸ ρᴿ Φ Ψ
    → Φ ⊢ A ≈ B
    → Ψ ⊢ renameᵗ ρᴸ A ≈ renameᵗ ρᴿ B
  rename-≈ r (idᵃ (＇ X) (＇ Y) hA hB (varᵃ X≈Y)) =
    idᵃ (＇ _) (＇ _)
      (renameᵗ-preserves-WfTy hA (left-wfᵣ r))
      (renameᵗ-preserves-WfTy hB (right-wfᵣ r))
      (varᵃ (pairedᵣ r X≈Y))
  rename-≈ r (idᵃ (‵ ι) (‵ .ι) hA hB baseᵃ) =
    idᵃ (‵ ι) (‵ ι)
      (renameᵗ-preserves-WfTy hA (left-wfᵣ r))
      (renameᵗ-preserves-WfTy hB (right-wfᵣ r)) baseᵃ
  rename-≈ r (idᵃ ★ ★ hA hB starᵃ) =
    idᵃ ★ ★
      (renameᵗ-preserves-WfTy hA (left-wfᵣ r))
      (renameᵗ-preserves-WfTy hB (right-wfᵣ r)) starᵃ
  rename-≈ r (p ⇒ʳ q) = rename-≈ r p ⇒ʳ rename-≈ r q
  rename-≈ r (∀ʳ p) = ∀ʳ (rename-≈ (bothᵣ r) p)

  shiftᵣ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → RenameRelocation suc suc Φ (bothᵢ Φ)
  shiftᵣ = rename-relocation TyRenameWf-suc TyRenameWf-suc
    both-thereᵢ

  right-shiftᵣ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → RenameRelocation (λ X → X) suc Φ (freshᴿ Φ)
  right-shiftᵣ = rename-relocation (λ X<Δ → X<Δ) TyRenameWf-suc
    freshᴿ-thereᵢ

  reuse-shiftᵣ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → RenameRelocation (λ X → X) suc (freshᴸ Φ) (bothᵢ Φ)
  reuse-shiftᵣ = rename-relocation (λ X<Δ → X<Δ) TyRenameWf-suc
    reuse-paired
    where
    reuse-paired : ∀ {Δᴸ Δᴿ X Y} {Φ : ImpCtx Δᴸ Δᴿ}
      → freshᴸ Φ ⊢ X ≈ˣ Y
      → bothᵢ Φ ⊢ X ≈ˣ suc Y
    reuse-paired (freshᴸ-thereᵢ X≈Y) = both-thereᵢ X≈Y

------------------------------------------------------------------------
-- Relocation under binder extension
------------------------------------------------------------------------

⇑ʳ : ∀ {Δᴸ Δᴿ A B} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ A ≈ B
  → bothᵢ Φ ⊢ ⇑ᵗ A ≈ ⇑ᵗ B
⇑ʳ = rename-≈ shiftᵣ

⇑ᴿʳ : ∀ {Δᴸ Δᴿ A B} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ A ≈ B
  → freshᴿ Φ ⊢ A ≈ ⇑ᵗ B
⇑ᴿʳ {A = A} {B = B} {Φ = Φ} p =
  subst (λ A′ → freshᴿ Φ ⊢ A′ ≈ ⇑ᵗ B)
    (renameᵗ-id A) (rename-≈ right-shiftᵣ p)

⇑ᴿ-reuseʳ : ∀ {Δᴸ Δᴿ A B} {Φ : ImpCtx Δᴸ Δᴿ}
  → freshᴸ Φ ⊢ A ≈ B
  → bothᵢ Φ ⊢ A ≈ ⇑ᵗ B
⇑ᴿ-reuseʳ {A = A} {B = B} {Φ = Φ} p =
  subst (λ A′ → bothᵢ Φ ⊢ A′ ≈ ⇑ᵗ B)
    (renameᵗ-id A) (rename-≈ reuse-shiftᵣ p)

smart-⇑ᴿʳ : ∀ {Δᴸ Δᴿ A B}
    {Φ : ImpCtx Δᴸ Δᴿ} {Ψ : ImpCtx Δᴸ (suc Δᴿ)}
  → SmartExtensionᵢ Φ Ψ
  → Φ ⊢ A ≈ B
  → Ψ ⊢ A ≈ ⇑ᵗ B
smart-⇑ᴿʳ freshᵢ p = ⇑ᴿʳ p
smart-⇑ᴿʳ reuseᵢ p = ⇑ᴿ-reuseʳ p
