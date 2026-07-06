module GradualTermNarrowing where

-- File Charter:
--   * Source-level gradual term narrowing for GTSF.
--   * Adapts the PolyConvert gradual-term imprecision shape to GTSF's
--     coercion-indexed narrowing evidence.
--   * Keeps explicit endpoint typing and index-coercion typing projections so
--     a later compile-monotonicity proof can proceed by induction on this
--     relation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; map)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong₂)

open import Types
open import Ctx using (⤊ᵗ)
open import Coercions
open import GradualTerms
open import NarrowWiden
open import Primitives

variable
  Δ : TyCtx
  Σ : Store
  γ : CtxNrw
  A A′ B B′ C D T T′ : Ty
  p q r : Coercion
  M M′ N N′ L L′ V V′ : GTerm
  x : Var
  ℓ : Label
  op : Prim

------------------------------------------------------------------------
-- Type-variable renaming on source gradual terms
------------------------------------------------------------------------

renameᵗᴳ : Renameᵗ → GTerm → GTerm
renameᵗᴳ ρ (` x) = ` x
renameᵗᴳ ρ (ƛ A ⇒ M) = ƛ renameᵗ ρ A ⇒ renameᵗᴳ ρ M
renameᵗᴳ ρ (L ·[ ℓ ] M) = renameᵗᴳ ρ L ·[ ℓ ] renameᵗᴳ ρ M
renameᵗᴳ ρ (Λ M) = Λ (renameᵗᴳ (extᵗ ρ) M)
renameᵗᴳ ρ (M `[ T ]) = renameᵗᴳ ρ M `[ renameᵗ ρ T ]
renameᵗᴳ ρ ($ κ) = $ κ
renameᵗᴳ ρ (L ⊕[ op at ℓ ] M) =
  renameᵗᴳ ρ L ⊕[ op at ℓ ] renameᵗᴳ ρ M

⇑ᵗᴳ : GTerm → GTerm
⇑ᵗᴳ = renameᵗᴳ suc

------------------------------------------------------------------------
-- Term-context narrowing
------------------------------------------------------------------------

⇑ᵍ-entry : CtxNrwEntry → CtxNrwEntry
⇑ᵍ-entry (ctx-nrw A B p) = ctx-nrw (⇑ᵗ A) (⇑ᵗ B) (⇑ᶜ p)

⇑ᵍ : CtxNrw → CtxNrw
⇑ᵍ = map ⇑ᵍ-entry

srcCtxⁿ : CtxNrw → Ctx
srcCtxⁿ = map srcTy

tgtCtxⁿ : CtxNrw → Ctx
tgtCtxⁿ = map tgtTy

srcCtxⁿ-⇑ᵍ : ∀ γ → srcCtxⁿ (⇑ᵍ γ) ≡ ⤊ᵗ (srcCtxⁿ γ)
srcCtxⁿ-⇑ᵍ [] = refl
srcCtxⁿ-⇑ᵍ (entry ∷ γ) =
  cong₂ _∷_ refl (srcCtxⁿ-⇑ᵍ γ)

tgtCtxⁿ-⇑ᵍ : ∀ γ → tgtCtxⁿ (⇑ᵍ γ) ≡ ⤊ᵗ (tgtCtxⁿ γ)
tgtCtxⁿ-⇑ᵍ [] = refl
tgtCtxⁿ-⇑ᵍ (entry ∷ γ) =
  cong₂ _∷_ refl (tgtCtxⁿ-⇑ᵍ γ)

------------------------------------------------------------------------
-- Typed/well-indexed gradual term narrowing
------------------------------------------------------------------------

record GradualTermTypingEndpoints
    (Δ : TyCtx) (γ : CtxNrw)
    (M M′ : GTerm) (A B : Ty) : Set₁ where
  constructor gradual-term-typing-endpoints
  field
    sourceGradualTyping : Δ ∣ srcCtxⁿ γ ⊢ M ⦂ A
    targetGradualTyping : Δ ∣ tgtCtxⁿ γ ⊢ M′ ⦂ B

open GradualTermTypingEndpoints public

fun-narrow-codomainᶜ :
  Δ ∣ Σ ⊢ p ↦ q ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′) →
  Δ ∣ Σ ⊢ q ∶ᶜ B ⊒ B′
fun-narrow-codomainᶜ (cast-fun p⊢ q⊢ , cross (p⊑ ↦ q⊒)) =
  q⊢ , q⊒

infix 4 _∣_∣_⊢ᴳ_⊒_∶_⦂_⊒_

data _∣_∣_⊢ᴳ_⊒_∶_⦂_⊒_
    : TyCtx → Store → CtxNrw →
      GTerm → GTerm → Coercion → Ty → Ty → Set₁ where

  x⊒xᴳ : ∀ {x p A B}
    → {typing : GradualTermTypingEndpoints Δ γ (` x) (` x) A B}
    → Δ ∣ Σ ⊢ p ∶ᶜ A ⊒ B
    → γ ∋ x ⦂ ctx-nrw A B p
      --------------------------------
    → Δ ∣ Σ ∣ γ ⊢ᴳ ` x ⊒ ` x ∶ p ⦂ A ⊒ B

  ƛ⊒ƛᴳ : ∀ {N N′ p q A A′ B B′}
    → {typing :
        GradualTermTypingEndpoints Δ γ
          (ƛ A ⇒ N) (ƛ A′ ⇒ N′) (A ⇒ B) (A′ ⇒ B′)}
    → (p↦qᶜ : Δ ∣ Σ ⊢ p ↦ q ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′))
    → Δ ∣ Σ ∣ ctx-nrw A A′ (fun-narrow-domain-dualᶜ p↦qᶜ) ∷ γ
        ⊢ᴳ N ⊒ N′ ∶ q ⦂ B ⊒ B′
      ----------------------------------------------------
    → Δ ∣ Σ ∣ γ ⊢ᴳ ƛ A ⇒ N ⊒ ƛ A′ ⇒ N′ ∶ p ↦ q
        ⦂ A ⇒ B ⊒ A′ ⇒ B′

  ·⊒·ᴳ : ∀ {L L′ M M′ p q A A′ B B′ ℓ}
    → {typing :
        GradualTermTypingEndpoints Δ γ
          (L ·[ ℓ ] M) (L′ ·[ ℓ ] M′) B B′}
    → (p↦qᶜ : Δ ∣ Σ ⊢ p ↦ q ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′))
    → Δ ∣ Σ ∣ γ ⊢ᴳ L ⊒ L′ ∶ p ↦ q
        ⦂ A ⇒ B ⊒ A′ ⇒ B′
    → Δ ∣ Σ ∣ γ ⊢ᴳ M ⊒ M′ ∶ fun-narrow-domain-dualᶜ p↦qᶜ
        ⦂ A ⊒ A′
      -------------------------------------------------------
    → Δ ∣ Σ ∣ γ ⊢ᴳ L ·[ ℓ ] M ⊒ L′ ·[ ℓ ] M′ ∶ q ⦂ B ⊒ B′

  Λ⊒Λᴳ : ∀ {V V′ p A B}
    → {typing :
        GradualTermTypingEndpoints Δ γ (Λ V) (Λ V′) (`∀ A) (`∀ B)}
    → Δ ∣ Σ ⊢ `∀ p ∶ᶜ `∀ A ⊒ `∀ B
    → Value V
    → Value V′
    → suc Δ ∣ ⟰ᵗ Σ ∣ ⇑ᵍ γ ⊢ᴳ V ⊒ V′ ∶ p ⦂ A ⊒ B
      -------------------------------------------------
    → Δ ∣ Σ ∣ γ ⊢ᴳ Λ V ⊒ Λ V′ ∶ `∀ p ⦂ `∀ A ⊒ `∀ B

  ⊒Λᴳ : ∀ {A B N V′ p}
    → {typing : GradualTermTypingEndpoints Δ γ N (Λ V′) A (`∀ B)}
    → Δ ∣ Σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B
    → Value V′
    → suc Δ ∣ ⟰ᵗ Σ ∣ ⇑ᵍ γ
        ⊢ᴳ ⇑ᵗᴳ N ⊒ V′ ∶ p ⦂ ⇑ᵗ A ⊒ B
      --------------------------------------------------------
    → Δ ∣ Σ ∣ γ ⊢ᴳ N ⊒ Λ V′ ∶ gen A p ⦂ A ⊒ `∀ B

  []⊒[]ᴳ : ∀ {M M′ T T′ A B p q r}
    → {typing :
        GradualTermTypingEndpoints Δ γ
          (M `[ T ]) (M′ `[ T′ ]) (A [ T ]ᵗ) (B [ T′ ]ᵗ)}
    → Δ ∣ Σ ∣ γ ⊢ᴳ M ⊒ M′ ∶ `∀ p ⦂ `∀ A ⊒ `∀ B
    → Δ ∣ Σ ⊢ q ∶ᶜ T ⊒ T′
    → Δ ∣ Σ ⊢ r ∶ᶜ A [ T ]ᵗ ⊒ B [ T′ ]ᵗ
      ----------------------------------------------------------
    → Δ ∣ Σ ∣ γ ⊢ᴳ M `[ T ] ⊒ M′ `[ T′ ] ∶ r
        ⦂ A [ T ]ᵗ ⊒ B [ T′ ]ᵗ

  ⊒[]ᴳ : ∀ {M M′ T′ A B p q r}
    → {typing :
        GradualTermTypingEndpoints Δ γ M (M′ `[ T′ ]) A (B [ T′ ]ᵗ)}
    → Δ ∣ Σ ∣ γ ⊢ᴳ M ⊒ M′ ∶ gen A p ⦂ A ⊒ `∀ B
    → Δ ∣ Σ ⊢ q ∶ᶜ ★ ⊒ T′
    → Δ ∣ Σ ⊢ r ∶ᶜ A ⊒ B [ T′ ]ᵗ
      ------------------------------------------------
    → Δ ∣ Σ ∣ γ ⊢ᴳ M ⊒ M′ `[ T′ ] ∶ r ⦂ A ⊒ B [ T′ ]ᵗ

  κ⊒κᴳ : ∀ κ
    → {typing :
        GradualTermTypingEndpoints Δ γ ($ κ) ($ κ) (constTy κ) (constTy κ)}
      ---------------------------------------------------------------
    → Δ ∣ Σ ∣ γ ⊢ᴳ $ κ ⊒ $ κ ∶ id (constTy κ)
        ⦂ constTy κ ⊒ constTy κ

  ⊕⊒⊕ᴳ : ∀ {M M′ N N′ op ℓ}
    → {typing :
        GradualTermTypingEndpoints Δ γ
          (M ⊕[ op at ℓ ] N) (M′ ⊕[ op at ℓ ] N′) (‵ `ℕ) (‵ `ℕ)}
    → Δ ∣ Σ ∣ γ ⊢ᴳ M ⊒ M′ ∶ id (‵ `ℕ)
        ⦂ ‵ `ℕ ⊒ ‵ `ℕ
    → Δ ∣ Σ ∣ γ ⊢ᴳ N ⊒ N′ ∶ id (‵ `ℕ)
        ⦂ ‵ `ℕ ⊒ ‵ `ℕ
      ----------------------------------------------------------------------
    → Δ ∣ Σ ∣ γ ⊢ᴳ M ⊕[ op at ℓ ] N ⊒ M′ ⊕[ op at ℓ ] N′
        ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ

gradual-term-narrowing-term-typing :
  Δ ∣ Σ ∣ γ ⊢ᴳ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  GradualTermTypingEndpoints Δ γ M M′ A B
gradual-term-narrowing-term-typing (x⊒xᴳ {typing = typing} pᶜ x∋p) =
  typing
gradual-term-narrowing-term-typing (ƛ⊒ƛᴳ {typing = typing} p↦qᶜ N⊒N′) =
  typing
gradual-term-narrowing-term-typing
    (·⊒·ᴳ {typing = typing} p↦qᶜ L⊒L′ M⊒M′) =
  typing
gradual-term-narrowing-term-typing
    (Λ⊒Λᴳ {typing = typing} allᶜ vV vV′ V⊒V′) =
  typing
gradual-term-narrowing-term-typing (⊒Λᴳ {typing = typing} pᶜ vV′ N⊒V′) =
  typing
gradual-term-narrowing-term-typing
    ([]⊒[]ᴳ {typing = typing} M⊒M′ qᶜ rᶜ) =
  typing
gradual-term-narrowing-term-typing (⊒[]ᴳ {typing = typing} M⊒M′ qᶜ rᶜ) =
  typing
gradual-term-narrowing-term-typing (κ⊒κᴳ κ {typing = typing}) =
  typing
gradual-term-narrowing-term-typing
    (⊕⊒⊕ᴳ {typing = typing} M⊒M′ N⊒N′) =
  typing

gradual-term-narrowing-source-typing :
  Δ ∣ Σ ∣ γ ⊢ᴳ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  Δ ∣ srcCtxⁿ γ ⊢ M ⦂ A
gradual-term-narrowing-source-typing M⊒M′ =
  sourceGradualTyping (gradual-term-narrowing-term-typing M⊒M′)

gradual-term-narrowing-target-typing :
  Δ ∣ Σ ∣ γ ⊢ᴳ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  Δ ∣ tgtCtxⁿ γ ⊢ M′ ⦂ B
gradual-term-narrowing-target-typing M⊒M′ =
  targetGradualTyping (gradual-term-narrowing-term-typing M⊒M′)

gradual-term-narrowing-index-typing :
  Δ ∣ Σ ∣ γ ⊢ᴳ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  Δ ∣ Σ ⊢ p ∶ A ⊒ B
gradual-term-narrowing-index-typing (x⊒xᴳ pᶜ x∋p) =
  tag-or-idᵈ , pᶜ
gradual-term-narrowing-index-typing (ƛ⊒ƛᴳ p↦qᶜ N⊒N′) =
  tag-or-idᵈ , p↦qᶜ
gradual-term-narrowing-index-typing (·⊒·ᴳ p↦qᶜ L⊒L′ M⊒M′) =
  tag-or-idᵈ , fun-narrow-codomainᶜ p↦qᶜ
gradual-term-narrowing-index-typing (Λ⊒Λᴳ allᶜ vV vV′ V⊒V′) =
  tag-or-idᵈ , allᶜ
gradual-term-narrowing-index-typing (⊒Λᴳ pᶜ vV′ N⊒V′) =
  tag-or-idᵈ , pᶜ
gradual-term-narrowing-index-typing ([]⊒[]ᴳ M⊒M′ qᶜ rᶜ) =
  tag-or-idᵈ , rᶜ
gradual-term-narrowing-index-typing (⊒[]ᴳ M⊒M′ qᶜ rᶜ) =
  tag-or-idᵈ , rᶜ
gradual-term-narrowing-index-typing (κ⊒κᴳ (κℕ n)) =
  tag-or-idᵈ , cast-id wfBase refl , cross (id-‵ `ℕ)
gradual-term-narrowing-index-typing (⊕⊒⊕ᴳ M⊒M′ N⊒N′) =
  tag-or-idᵈ , cast-id wfBase refl , cross (id-‵ `ℕ)
