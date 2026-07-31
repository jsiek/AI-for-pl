module TypeRelocate where

-- File Charter:
--   * Defines intrinsically scoped imprecision contexts.
--   * Defines relocation of types between two related type contexts.
--   * Relates paired variables and maps one-sided variables to dynamic type.
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
infix 4 _⊢_≈★
infix 4 _⊢★≈_

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
-- Variables present on only one side
------------------------------------------------------------------------

data _⊢_≈★ : ∀ {Δᴸ Δᴿ}
    → ImpCtx Δᴸ Δᴿ → TyVar → Set where

  hereᴸ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
      ----------------------
    → freshᴸ Φ ⊢ zero ≈★

  both-thereᴸ : ∀ {Δᴸ Δᴿ X} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢ X ≈★
      -------------------------
    → bothᵢ Φ ⊢ suc X ≈★

  freshᴸ-thereᴸ : ∀ {Δᴸ Δᴿ X} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢ X ≈★
      --------------------------
    → freshᴸ Φ ⊢ suc X ≈★

  freshᴿ-thereᴸ : ∀ {Δᴸ Δᴿ X} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢ X ≈★
      ----------------------
    → freshᴿ Φ ⊢ X ≈★

data _⊢★≈_ : ∀ {Δᴸ Δᴿ}
    → ImpCtx Δᴸ Δᴿ → TyVar → Set where

  hereᴿ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
      ----------------------
    → freshᴿ Φ ⊢★≈ zero

  both-thereᴿ : ∀ {Δᴸ Δᴿ Y} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢★≈ Y
      -------------------------
    → bothᵢ Φ ⊢★≈ suc Y

  freshᴸ-thereᴿ : ∀ {Δᴸ Δᴿ Y} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢★≈ Y
      ----------------------
    → freshᴸ Φ ⊢★≈ Y

  freshᴿ-thereᴿ : ∀ {Δᴸ Δᴿ Y} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢★≈ Y
      --------------------------
    → freshᴿ Φ ⊢★≈ suc Y

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

≈★-left-bound : ∀ {Δᴸ Δᴿ X} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ X ≈★
  → X < Δᴸ
≈★-left-bound hereᴸ = s≤s z≤n
≈★-left-bound (both-thereᴸ Xᴸ) = s≤s (≈★-left-bound Xᴸ)
≈★-left-bound (freshᴸ-thereᴸ Xᴸ) = s≤s (≈★-left-bound Xᴸ)
≈★-left-bound (freshᴿ-thereᴸ Xᴸ) = ≈★-left-bound Xᴸ

★≈-right-bound : ∀ {Δᴸ Δᴿ Y} {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢★≈ Y
  → Y < Δᴿ
★≈-right-bound hereᴿ = s≤s z≤n
★≈-right-bound (both-thereᴿ Yᴿ) = s≤s (★≈-right-bound Yᴿ)
★≈-right-bound (freshᴸ-thereᴿ Yᴿ) = ★≈-right-bound Yᴿ
★≈-right-bound (freshᴿ-thereᴿ Yᴿ) = s≤s (★≈-right-bound Yᴿ)

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

  left-onlyᵃ : ∀ {Δᴸ Δᴿ X} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢ X ≈★
      ---------------
    → Φ ⊢ ＇ X ≈ᵃ ★

  right-onlyᵃ : ∀ {Δᴸ Δᴿ Y} {Φ : ImpCtx Δᴸ Δᴿ}
    → Φ ⊢★≈ Y
      ---------------
    → Φ ⊢ ★ ≈ᵃ ＇ Y

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
      left-onlyᵣ : ∀ {X}
        → Φ ⊢ X ≈★
        → Ψ ⊢ ρᴸ X ≈★
      right-onlyᵣ : ∀ {Y}
        → Φ ⊢★≈ Y
        → Ψ ⊢★≈ ρᴿ Y

  open RenameRelocation

  bothᵣ : ∀ {Δᴸ Δᴿ Δᴸ′ Δᴿ′ ρᴸ ρᴿ}
      {Φ : ImpCtx Δᴸ Δᴿ} {Ψ : ImpCtx Δᴸ′ Δᴿ′}
    → RenameRelocation ρᴸ ρᴿ Φ Ψ
    → RenameRelocation (extᵗ ρᴸ) (extᵗ ρᴿ)
        (bothᵢ Φ) (bothᵢ Ψ)
  bothᵣ (rename-relocation hᴸ hᴿ paired left-only right-only) =
    rename-relocation (TyRenameWf-ext hᴸ) (TyRenameWf-ext hᴿ)
      both-paired both-left-only both-right-only
    where
    both-paired : ∀ {X Y}
      → bothᵢ _ ⊢ X ≈ˣ Y
      → bothᵢ _ ⊢ extᵗ _ X ≈ˣ extᵗ _ Y
    both-paired hereᵢ = hereᵢ
    both-paired (both-thereᵢ X≈Y) = both-thereᵢ (paired X≈Y)

    both-left-only : ∀ {X}
      → bothᵢ _ ⊢ X ≈★
      → bothᵢ _ ⊢ extᵗ _ X ≈★
    both-left-only (both-thereᴸ X≈★) = both-thereᴸ (left-only X≈★)

    both-right-only : ∀ {Y}
      → bothᵢ _ ⊢★≈ Y
      → bothᵢ _ ⊢★≈ extᵗ _ Y
    both-right-only (both-thereᴿ ★≈Y) =
      both-thereᴿ (right-only ★≈Y)

  freshᴿᵣ : ∀ {Δᴸ Δᴿ Δᴸ′ Δᴿ′ ρᴸ ρᴿ}
      {Φ : ImpCtx Δᴸ Δᴿ} {Ψ : ImpCtx Δᴸ′ Δᴿ′}
    → RenameRelocation ρᴸ ρᴿ Φ Ψ
    → RenameRelocation ρᴸ (extᵗ ρᴿ)
        (freshᴿ Φ) (freshᴿ Ψ)
  freshᴿᵣ (rename-relocation hᴸ hᴿ paired left-only right-only) =
    rename-relocation hᴸ (TyRenameWf-ext hᴿ)
      fresh-paired fresh-left-only fresh-right-only
    where
    fresh-paired : ∀ {X Y}
      → freshᴿ _ ⊢ X ≈ˣ Y
      → freshᴿ _ ⊢ _ ≈ˣ extᵗ _ Y
    fresh-paired (freshᴿ-thereᵢ X≈Y) =
      freshᴿ-thereᵢ (paired X≈Y)

    fresh-left-only : ∀ {X}
      → freshᴿ _ ⊢ X ≈★
      → freshᴿ _ ⊢ _ ≈★
    fresh-left-only (freshᴿ-thereᴸ X≈★) =
      freshᴿ-thereᴸ (left-only X≈★)

    fresh-right-only : ∀ {Y}
      → freshᴿ _ ⊢★≈ Y
      → freshᴿ _ ⊢★≈ extᵗ _ Y
    fresh-right-only hereᴿ = hereᴿ
    fresh-right-only (freshᴿ-thereᴿ ★≈Y) =
      freshᴿ-thereᴿ (right-only ★≈Y)

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
  rename-≈ r (idᵃ (＇ X) ★ hA hB (left-onlyᵃ X≈★)) =
    idᵃ (＇ _) ★
      (renameᵗ-preserves-WfTy hA (left-wfᵣ r))
      (renameᵗ-preserves-WfTy hB (right-wfᵣ r))
      (left-onlyᵃ (left-onlyᵣ r X≈★))
  rename-≈ r (idᵃ ★ (＇ Y) hA hB (right-onlyᵃ ★≈Y)) =
    idᵃ ★ (＇ _)
      (renameᵗ-preserves-WfTy hA (left-wfᵣ r))
      (renameᵗ-preserves-WfTy hB (right-wfᵣ r))
      (right-onlyᵃ (right-onlyᵣ r ★≈Y))
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
    both-thereᵢ both-thereᴸ both-thereᴿ

  right-shiftᵣ : ∀ {Δᴸ Δᴿ} {Φ : ImpCtx Δᴸ Δᴿ}
    → RenameRelocation (λ X → X) suc Φ (freshᴿ Φ)
  right-shiftᵣ = rename-relocation (λ X<Δ → X<Δ) TyRenameWf-suc
    freshᴿ-thereᵢ freshᴿ-thereᴸ freshᴿ-thereᴿ

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
