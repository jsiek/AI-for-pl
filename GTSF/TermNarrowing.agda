-- OBSOLETE
-- Replaced by the quotiented Nu imprecision development.

{-
  Term imprecision for the Nu syntax.

  Legacy note: this shared-store relation is obsolete for new work.  It remains
  only for older proof experiments that have not been part of the aggregate
  checker.

  This file mechanizes the term-imprecision relation from the cambridge22/23
  notes.  The paper presentation uses a combined environment for term variables
  and seal assumptions; here we split it into the store narrowing context from
  NarrowWiden and a term-variable context of coercions.

  Freshness side conditions from the paper are not reified here.  The paper's
  +/- cast notation is represented using NuTerms' single raw cast form and the
  coercion dual operator `-_`, with the corresponding coercion-equivalence
  premise made explicit.
-}

module TermNarrowing where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_; map)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; proj₁; ∃-syntax)

open import Types
open import Coercions
open import Primitives
open import NuTerms
open import NarrowWiden
open import NarrowWidenComposition
open import proof.NarrowWidenProperties using (StoreDetWf)

variable
  Δ : TyCtx
  Σ : Store
  σ : StoreNrw
  γ γ′ : CtxNrw
  A A′ B B′ C D : Ty
  p q r s t : Coercion
  M M′ N N′ L L′ V V′ : Term
  x : Var
  α αᵢ : TyVar

⇑ᵍ-entry : CtxNrwEntry → CtxNrwEntry
⇑ᵍ-entry (ctx-nrw A B p) = ctx-nrw (⇑ᵗ A) (⇑ᵗ B) (⇑ᶜ p)

⇑ᵍ : CtxNrw → CtxNrw
⇑ᵍ = map ⇑ᵍ-entry

srcCtxⁿ : CtxNrw → Ctx
srcCtxⁿ = map srcTy

tgtCtxⁿ : CtxNrw → Ctx
tgtCtxⁿ = map tgtTy

fun-narrow-codomainᶜ :
  Δ ∣ Σ ⊢ p ↦ q ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′) →
  Δ ∣ Σ ⊢ q ∶ᶜ B ⊒ B′
fun-narrow-codomainᶜ (cast-fun p⊢ q⊢ , cross (p⊑ ↦ q⊒)) =
  q⊢ , q⊒

infix 4 _∣_∣_⊢_⊒_∶_⦂_⊒_

------------------------------------------------------------------------
-- Typed/well-indexed term narrowing
------------------------------------------------------------------------

record TermTypingEndpoints
    (Δ : TyCtx) (σ : StoreNrw) (γ : CtxNrw)
    (M M′ : Term) (A B : Ty) : Set₁ where
  constructor term-typing-endpoints
  field
    sourceTermTyping : Δ ∣ srcStoreⁿ σ ∣ srcCtxⁿ γ ⊢ M ⦂ A
    targetTermTyping : Δ ∣ tgtStoreⁿ σ ∣ tgtCtxⁿ γ ⊢ M′ ⦂ B

open TermTypingEndpoints public

data _∣_∣_⊢_⊒_∶_⦂_⊒_
    : TyCtx → StoreNrw → CtxNrw →
      Term → Term → Coercion → Ty → Ty → Set₁ where

  extendᵗ : ∀ {M N′ p q A B C D α}
    → {typing :
        TermTypingEndpoints Δ ((α ꞉ q) ∷ σ) γ M (N′ [ α ]ᵀ) C D}
    → Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ B ⊒ A
    → Δ ∣ srcStoreⁿ ((α ꞉ q) ∷ σ) ⊢ p [ α ]ᶜ ∶ᶜ C ⊒ D
    → Δ ∣ (α ꞉= A ⊒) ∷ σ ∣ γ
        ⊢ M ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ ⦂ C ⊒ D
      ------------------------------------------------------
    → Δ ∣ (α ꞉ q) ∷ σ ∣ γ
        ⊢ M ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ ⦂ C ⊒ D

  splitᵗ : ∀ {N N′ p q A C D α αᵢ}
    → {typing :
        TermTypingEndpoints Δ
          ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ) γ
          (N [ αᵢ ]ᵀ) (N′ [ α ]ᵀ) C D}
    → Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ)
        ⊢ q ∶ᶜ ★ ⊒ A
    → Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ)
        ⊢ p [ α ]ᶜ ∶ᶜ C ⊒ D
    → Δ ∣ (α ꞉ q) ∷ σ ∣ γ
        ⊢ N [ α ]ᵀ ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ ⦂ C ⊒ D
      ----------------------------------------------------------
    → Δ ∣ (α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ ∣ γ
        ⊢ N [ αᵢ ]ᵀ ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ ⦂ C ⊒ D

  ⊒blameᵗ : ∀ {M p A B}
    → {typing : TermTypingEndpoints Δ σ γ M blame A B}
    → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B
    → Δ ∣ σ ∣ γ ⊢ M ⊒ blame ∶ p ⦂ A ⊒ B

  x⊒xᵗ : ∀ {x p A B}
    → {typing : TermTypingEndpoints Δ σ γ (` x) (` x) A B}
    → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B
    → γ ∋ x ⦂ ctx-nrw A B p
      --------------------------------
    → Δ ∣ σ ∣ γ ⊢ ` x ⊒ ` x ∶ p ⦂ A ⊒ B

  ƛ⊒ƛᵗ : ∀ {N N′ p q A A′ B B′}
    → {typing : TermTypingEndpoints Δ σ γ (ƛ N) (ƛ N′) (A ⇒ B) (A′ ⇒ B′)}
    → (p↦qᶜ : Δ ∣ srcStoreⁿ σ ⊢ p ↦ q ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′))
    → Δ ∣ σ ∣ ctx-nrw A A′ (fun-narrow-domain-dualᶜ p↦qᶜ) ∷ γ
        ⊢ N ⊒ N′ ∶ q ⦂ B ⊒ B′
      ----------------------------------------------------
    → Δ ∣ σ ∣ γ ⊢ ƛ N ⊒ ƛ N′ ∶ p ↦ q
        ⦂ A ⇒ B ⊒ A′ ⇒ B′

  ·⊒·ᵗ : ∀ {L L′ M M′ p q A A′ B B′}
    → {typing :
        TermTypingEndpoints Δ σ γ (L · M) (L′ · M′) B B′}
    → (p↦qᶜ : Δ ∣ srcStoreⁿ σ ⊢ p ↦ q ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′))
    → Δ ∣ σ ∣ γ ⊢ L ⊒ L′ ∶ p ↦ q
        ⦂ A ⇒ B ⊒ A′ ⇒ B′
    → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ fun-narrow-domain-dualᶜ p↦qᶜ
        ⦂ A ⊒ A′
      -------------------------------------------------------
    → Δ ∣ σ ∣ γ ⊢ L · M ⊒ L′ · M′ ∶ q ⦂ B ⊒ B′

  Λ⊒Λᵗ : ∀ {V V′ p A B}
    → {typing : TermTypingEndpoints Δ σ γ (Λ V) (Λ V′) (`∀ A) (`∀ B)}
    → Δ ∣ srcStoreⁿ σ ⊢ `∀ p ∶ᶜ `∀ A ⊒ `∀ B
    → Value V
    → suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ ⊢ V ⊒ V′ ∶ p ⦂ A ⊒ B
      -------------------------------------------------
    → Δ ∣ σ ∣ γ ⊢ Λ V ⊒ Λ V′ ∶ `∀ p ⦂ `∀ A ⊒ `∀ B

  ⊒Λᵗ : ∀ {A B N V′ p}
    → {typing : TermTypingEndpoints Δ σ γ N (Λ V′) A (`∀ B)}
    → Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B
    → suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ
        ⊢ ⇑ᵗᵐ N ⊒ V′ ∶ p ⦂ ⇑ᵗ A ⊒ B
      --------------------------------------------------------
    → Δ ∣ σ ∣ γ ⊢ N ⊒ Λ V′ ∶ gen A p ⦂ A ⊒ `∀ B

  ⊒⟨ν⟩ᵗ : ∀ {A B N V′ p s}
    → {typing :
        TermTypingEndpoints Δ σ γ N (V′ ⟨ gen A s ⟩) A (`∀ B)}
    → Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B
    → Inert s
    → suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ
        ⊢ ⇑ᵗᵐ N ⊒ V′ ⟨ s ⟩ ∶ p ⦂ ⇑ᵗ A ⊒ B
      -----------------------------------------------------------
    → Δ ∣ σ ∣ γ ⊢ N ⊒ V′ ⟨ gen A s ⟩ ∶ gen A p
        ⦂ A ⊒ `∀ B

  α⊒αᵗ : ∀ {L L′ p q A B C D E F}
    → γ′ ≡ ⇑ᵍ γ
    → {typing :
        TermTypingEndpoints (suc Δ) ((zero ꞉ ⇑ᶜ q) ∷ ⇑ˢ σ) γ′
          ((⇑ᵗᵐ L) •) ((⇑ᵗᵐ L′) •) C D}
    → Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ A ⊒ B
    → suc Δ ∣ srcStoreⁿ ((zero ꞉ ⇑ᶜ q) ∷ ⇑ˢ σ)
        ⊢ p ∶ᶜ C ⊒ D
    → Δ ∣ σ ∣ γ ⊢ L ⊒ L′ ∶ `∀ p ⦂ E ⊒ F
      ------------------------------------------------
    → suc Δ ∣ (zero ꞉ ⇑ᶜ q) ∷ ⇑ˢ σ ∣ γ′
        ⊢ (⇑ᵗᵐ L) • ⊒ (⇑ᵗᵐ L′) • ∶ p ⦂ C ⊒ D

  ⊒αᵗ : ∀ {L L′ p A B C D E F}
    → γ′ ≡ ⇑ᵍ γ
    → {typing :
        TermTypingEndpoints (suc Δ) ((zero ꞉= ⇑ᵗ A ⊒) ∷ ⇑ˢ σ) γ′
          (⇑ᵗᵐ L) ((⇑ᵗᵐ L′) •) C D}
    → suc Δ ∣ srcStoreⁿ ((zero ꞉= ⇑ᵗ A ⊒) ∷ ⇑ˢ σ)
        ⊢ p ∶ᶜ C ⊒ D
    → Δ ∣ σ ∣ γ ⊢ L ⊒ L′ ∶ gen B p ⦂ E ⊒ F
      -----------------------------------------------
    → suc Δ ∣ (zero ꞉= ⇑ᵗ A ⊒) ∷ ⇑ˢ σ ∣ γ′
        ⊢ ⇑ᵗᵐ L ⊒ (⇑ᵗᵐ L′) • ∶ p ⦂ C ⊒ D

  ν⊒νᵗ : ∀ {A A′ B B′ N N′ p q}
    → {typing :
        TermTypingEndpoints Δ σ γ
          (ν A N (⇑ᶜ p)) (ν A′ N′ (⇑ᶜ p)) B B′}
    → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ B ⊒ B′
    → Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ A ⊒ A′
    → suc Δ ∣ (zero ꞉ ⇑ᶜ q) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ
        ⊢ N ⊒ N′ ∶ ⇑ᶜ p ⦂ ⇑ᵗ B ⊒ ⇑ᵗ B′
      ------------------------------------------------------
    → Δ ∣ σ ∣ γ ⊢ ν A N (⇑ᶜ p) ⊒ ν A′ N′ (⇑ᶜ p) ∶ p
        ⦂ B ⊒ B′

  ⊒νᵗ : ∀ {A B B′ N N′ p}
    → {typing : TermTypingEndpoints Δ σ γ N (ν A N′ (⇑ᶜ p)) B B′}
    → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ B ⊒ B′
    → suc Δ ∣ (zero ꞉= ⇑ᵗ A ⊒) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ
        ⊢ ⇑ᵗᵐ N ⊒ N′ ∶ ⇑ᶜ p ⦂ ⇑ᵗ B ⊒ ⇑ᵗ B′
      ---------------------------------------
    → Δ ∣ σ ∣ γ ⊢ N ⊒ ν A N′ (⇑ᶜ p) ∶ p ⦂ B ⊒ B′

  ν⊒ᵗ : ∀ {N N′ p A B}
    → {typing : TermTypingEndpoints Δ σ γ (ν ★ N (⇑ᶜ p)) N′ A B}
    → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B
    → suc Δ ∣ (⊒ zero ꞉=☆) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ
        ⊢ N ⊒ ⇑ᵗᵐ N′ ∶ ⇑ᶜ p ⦂ ⇑ᵗ A ⊒ ⇑ᵗ B
      ---------------------------------------------
    → Δ ∣ σ ∣ γ ⊢ ν ★ N (⇑ᶜ p) ⊒ N′ ∶ p ⦂ A ⊒ B

  κ⊒κᵗ : ∀ κ
    → {typing :
        TermTypingEndpoints Δ σ γ ($ κ) ($ κ) (constTy κ) (constTy κ)}
      ---------------------------------------------------------------
    → Δ ∣ σ ∣ γ ⊢ $ κ ⊒ $ κ ∶ id (constTy κ)
        ⦂ constTy κ ⊒ constTy κ

  ⊕⊒⊕ᵗ : ∀ {M M′ N N′}
    → {typing :
        TermTypingEndpoints Δ σ γ
          (M ⊕[ addℕ ] N) (M′ ⊕[ addℕ ] N′) (‵ `ℕ) (‵ `ℕ)}
    → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ id (‵ `ℕ)
        ⦂ ‵ `ℕ ⊒ ‵ `ℕ
    → Δ ∣ σ ∣ γ ⊢ N ⊒ N′ ∶ id (‵ `ℕ)
        ⦂ ‵ `ℕ ⊒ ‵ `ℕ
      ----------------------------------------------------------------------
    → Δ ∣ σ ∣ γ ⊢ M ⊕[ addℕ ] N ⊒ M′ ⊕[ addℕ ] N′
        ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ

  ⊒cast+ᵗ : ∀ {M M′ q r s A B C D E Σ μ}
    → {typing : TermTypingEndpoints Δ σ γ M (M′ ⟨ - s ⟩) C D}
    → Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D
    → (wfΣ : StoreDetWf Δ Σ)
    → (q⊒ : μ ∣ Δ ∣ Σ ⊢ q ∶ A ⊒ E)
    → (s⊒ : μ ∣ Δ ∣ Σ ⊢ s ∶ E ⊒ B)
    → Δ ∣ σ ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ s⊒) ≈ r ∶ A ⊒ B
    → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ r ⦂ A ⊒ B
      -------------------------------------------------
    → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ⟨ - s ⟩ ∶ q ⦂ C ⊒ D

  ⊒cast-ᵗ : ∀ {M M′ q r s A B C D E Σ μ ν}
    → {typing : TermTypingEndpoints Δ σ γ M (M′ ⟨ s ⟩) A B}
    → Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D
    → μ ∣ Δ ∣ srcStoreⁿ σ ⊢ r ∶ A ⊒ B
    → (wfΣ : StoreDetWf Δ Σ)
    → (q⊒ : ν ∣ Δ ∣ Σ ⊢ q ∶ A ⊒ E)
    → (s⊒ : ν ∣ Δ ∣ Σ ⊢ s ∶ E ⊒ B)
    → Δ ∣ σ ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ s⊒) ≈ r ∶ A ⊒ B
    → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ q ⦂ C ⊒ D
      -------------------------------------------------
    → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ⟨ s ⟩ ∶ r ⦂ A ⊒ B

  cast+⊒ᵗ : ∀ {M M′ p r t A B C D E Σ μ ν}
    → {typing : TermTypingEndpoints Δ σ γ (M ⟨ - t ⟩) M′ A B}
    → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D
    → μ ∣ Δ ∣ srcStoreⁿ σ ⊢ r ∶ A ⊒ B
    → (wfΣ : StoreDetWf Δ Σ)
    → (t⊒ : ν ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ E)
    → (p⊒ : ν ∣ Δ ∣ Σ ⊢ p ∶ E ⊒ B)
    → Δ ∣ σ ⊢ r ≈ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} t⊒ p⊒) ∶ A ⊒ B
    → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ C ⊒ D
      -------------------------------------------------
    → Δ ∣ σ ∣ γ ⊢ M ⟨ - t ⟩ ⊒ M′ ∶ r ⦂ A ⊒ B

  cast-⊒ᵗ : ∀ {M M′ p r t A B C D E Σ μ}
    → {typing : TermTypingEndpoints Δ σ γ (M ⟨ t ⟩) M′ C D}
    → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D
    → (wfΣ : StoreDetWf Δ Σ)
    → (t⊒ : μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ E)
    → (p⊒ : μ ∣ Δ ∣ Σ ⊢ p ∶ E ⊒ B)
    → Δ ∣ σ ⊢ r ≈ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} t⊒ p⊒) ∶ A ⊒ B
    → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ r ⦂ A ⊒ B
      -------------------------------------------------
    → Δ ∣ σ ∣ γ ⊢ M ⟨ t ⟩ ⊒ M′ ∶ p ⦂ C ⊒ D

typed-term-narrowing-term-typing :
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  TermTypingEndpoints Δ σ γ M M′ A B
typed-term-narrowing-term-typing
    (extendᵗ {typing = typing} qᶜ pαᶜ M⊒N′) =
  typing
typed-term-narrowing-term-typing
    (splitᵗ {typing = typing} qᶜ pαᶜ N⊒N′) =
  typing
typed-term-narrowing-term-typing (⊒blameᵗ {typing = typing} pᶜ) =
  typing
typed-term-narrowing-term-typing (x⊒xᵗ {typing = typing} pᶜ x∋p) =
  typing
typed-term-narrowing-term-typing (ƛ⊒ƛᵗ {typing = typing} p↦qᶜ N⊒N′) =
  typing
typed-term-narrowing-term-typing
    (·⊒·ᵗ {typing = typing} p↦qᶜ L⊒L′ M⊒M′) =
  typing
typed-term-narrowing-term-typing (Λ⊒Λᵗ {typing = typing} allᶜ vV V⊒V′) =
  typing
typed-term-narrowing-term-typing (⊒Λᵗ {typing = typing} pᶜ N⊒V′) =
  typing
typed-term-narrowing-term-typing
    (⊒⟨ν⟩ᵗ {typing = typing} pᶜ i N⊒V′s) =
  typing
typed-term-narrowing-term-typing
    (α⊒αᵗ γ′≡ {typing = typing} qᶜ pαᶜ L⊒L′) =
  typing
typed-term-narrowing-term-typing
    (⊒αᵗ γ′≡ {typing = typing} pαᶜ L⊒L′) =
  typing
typed-term-narrowing-term-typing
    (ν⊒νᵗ {typing = typing} pᶜ qᶜ N⊒N′) =
  typing
typed-term-narrowing-term-typing (⊒νᵗ {typing = typing} pᶜ N⊒N′) =
  typing
typed-term-narrowing-term-typing (ν⊒ᵗ {typing = typing} pᶜ N⊒N′) =
  typing
typed-term-narrowing-term-typing (κ⊒κᵗ κ {typing = typing}) =
  typing
typed-term-narrowing-term-typing
    (⊕⊒⊕ᵗ {typing = typing} M⊒M′ N⊒N′) =
  typing
typed-term-narrowing-term-typing
    (⊒cast+ᵗ {typing = typing} qᶜ wfΣ q⊒ s⊒ q⨟s≈r M⊒M′) =
  typing
typed-term-narrowing-term-typing
    (⊒cast-ᵗ {typing = typing} qᶜ rᶜ wfΣ q⊒ s⊒ q⨟s≈r M⊒M′) =
  typing
typed-term-narrowing-term-typing
    (cast+⊒ᵗ {typing = typing} pᶜ rᶜ wfΣ t⊒ p⊒ r≈t⨟p M⊒M′) =
  typing
typed-term-narrowing-term-typing
    (cast-⊒ᵗ {typing = typing} pᶜ wfΣ t⊒ p⊒ r≈t⨟p M⊒M′) =
  typing

typed-term-narrowing-source-typing :
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  Δ ∣ srcStoreⁿ σ ∣ srcCtxⁿ γ ⊢ M ⦂ A
typed-term-narrowing-source-typing M⊒M′ =
  sourceTermTyping (typed-term-narrowing-term-typing M⊒M′)

typed-term-narrowing-target-typing :
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  Δ ∣ tgtStoreⁿ σ ∣ tgtCtxⁿ γ ⊢ M′ ⦂ B
typed-term-narrowing-target-typing M⊒M′ =
  targetTermTyping (typed-term-narrowing-term-typing M⊒M′)

typed-term-narrowing-index-typing :
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ A ⊒ B
typed-term-narrowing-index-typing (extendᵗ qᶜ pαᶜ M⊒N′) =
  tag-or-idᵈ , pαᶜ
typed-term-narrowing-index-typing (splitᵗ qᶜ pαᶜ N⊒N′) =
  tag-or-idᵈ , pαᶜ
typed-term-narrowing-index-typing (⊒blameᵗ pᶜ) =
  tag-or-idᵈ , pᶜ
typed-term-narrowing-index-typing (x⊒xᵗ pᶜ x∋p) =
  tag-or-idᵈ , pᶜ
typed-term-narrowing-index-typing (ƛ⊒ƛᵗ p↦qᶜ N⊒N′) =
  tag-or-idᵈ , p↦qᶜ
typed-term-narrowing-index-typing (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′) =
  tag-or-idᵈ , fun-narrow-codomainᶜ p↦qᶜ
typed-term-narrowing-index-typing (Λ⊒Λᵗ allᶜ vV V⊒V′) =
  tag-or-idᵈ , allᶜ
typed-term-narrowing-index-typing (⊒Λᵗ pᶜ N⊒V′) =
  tag-or-idᵈ , pᶜ
typed-term-narrowing-index-typing (⊒⟨ν⟩ᵗ pᶜ i N⊒V′s) =
  tag-or-idᵈ , pᶜ
typed-term-narrowing-index-typing
    (α⊒αᵗ γ′≡ qᶜ pαᶜ L⊒L′) =
  tag-or-idᵈ , pαᶜ
typed-term-narrowing-index-typing (⊒αᵗ γ′≡ pαᶜ L⊒L′) =
  tag-or-idᵈ , pαᶜ
typed-term-narrowing-index-typing (ν⊒νᵗ pᶜ qᶜ N⊒N′) =
  tag-or-idᵈ , pᶜ
typed-term-narrowing-index-typing (⊒νᵗ pᶜ N⊒N′) =
  tag-or-idᵈ , pᶜ
typed-term-narrowing-index-typing (ν⊒ᵗ pᶜ N⊒N′) =
  tag-or-idᵈ , pᶜ
typed-term-narrowing-index-typing (κ⊒κᵗ (κℕ n)) =
  tag-or-idᵈ , cast-id wfBase refl , cross (id-‵ `ℕ)
typed-term-narrowing-index-typing (⊕⊒⊕ᵗ M⊒M′ N⊒N′) =
  tag-or-idᵈ , cast-id wfBase refl , cross (id-‵ `ℕ)
typed-term-narrowing-index-typing (⊒cast+ᵗ qᶜ wfΣ q⊒ s⊒ q⨟s≈r M⊒M′) =
  tag-or-idᵈ , qᶜ
typed-term-narrowing-index-typing
    (⊒cast-ᵗ {μ = μ} qᶜ r⊒ wfΣ q⊒ s⊒ q⨟s≈r M⊒M′) =
  μ , r⊒
typed-term-narrowing-index-typing
    (cast+⊒ᵗ {μ = μ} pᶜ r⊒ wfΣ t⊒ p⊒ r≈t⨟p M⊒M′) =
  μ , r⊒
typed-term-narrowing-index-typing (cast-⊒ᵗ pᶜ wfΣ t⊒ p⊒ r≈t⨟p M⊒M′) =
  tag-or-idᵈ , pᶜ
