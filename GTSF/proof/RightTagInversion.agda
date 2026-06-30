module proof.RightTagInversion where

-- File Charter:
--   * Records why the old `right-tag-inversion₁` statement is not compatible
--     with filled raw casts.
--   * Provides a concrete term-narrowing derivation whose target is a raw
--     right tag `V ⟨ G ! ⟩`.
--   * Depends only on term narrowing, coercion grammar, and narrowing
--     composition side conditions; it does not depend on catchup.

open import Data.List using ([]; _∷_)
open import Data.Nat using (zero)
open import Data.Product using (_,_)
open import Agda.Builtin.Equality using (refl)

open import Types
open import Coercions
open import Primitives
open import NuTerms
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing
open import proof.NarrowWidenProperties using (StoreDetWf)

------------------------------------------------------------------------
-- Proof-strategy log
------------------------------------------------------------------------

-- 1. Direct inversion on `⊒cast+` was vacuous before filled raw casts:
--    a target `V ⟨ G ! ⟩` forced the source cast argument to be raw `G ？`,
--    and raw `G ？` was not a narrowing grammar form.
-- 2. Filling raw `G ？` with `id_G` changes that branch into a real case:
--    the cast side condition can compose with `(G ？) ︔ id_G`.
-- 3. Therefore the old conclusion `M ⊒ V ∶ G ？` is the wrong shape.  The
--    right inversion needs to expose the filled/composed narrowing instead.

------------------------------------------------------------------------
-- A concrete right-tag derivation via filled raw untag
------------------------------------------------------------------------

ℕᵗ : Ty
ℕᵗ = ‵ `ℕ

ℕ? : Coercion
ℕ? = ℕᵗ ？

ℕ?ⁿ : Coercion
ℕ?ⁿ = ℕ? ︔ id ℕᵗ

empty-store-det : ∀ {Δ} → StoreDetWf Δ []
empty-store-det =
  record
    { at = record
        { bound = λ ()
        ; wfTy = λ ()
        }
    ; wfOlder = λ ()
    ; unique = λ ()
    }

empty-store-narrowing : ∀ {Δ} → Δ ⊢ [] ꞉ [] ⊒ˢ []
empty-store-narrowing = ⊒ˢ-nil

id★⊒ : tag-or-idᵈ ∣ 0 ∣ [] ⊢ id ★ ∶ ★ ⊒ ★
id★⊒ = cast-id wf★ refl , id★

ℕ?ⁿ⊒ : tag-or-idᵈ ∣ 0 ∣ [] ⊢ ℕ?ⁿ ∶ ★ ⊒ ℕᵗ
ℕ?ⁿ⊒ =
  cast-seq (cast-untag wfBase (‵ `ℕ) refl) (cast-id wfBase refl) ,
  (‵ `ℕ) ？︔ id-‵ `ℕ

ℕ?ⁿ≈ℕ?ⁿ : 0 ∣ [] ⊢ ℕ?ⁿ ≈ ℕ?ⁿ ∶ ★ ⊒ ℕᵗ
ℕ?ⁿ≈ℕ?ⁿ =
  endpointsⁿ refl refl refl refl
    empty-store-narrowing
    (wf★ˢ , wfBaseˢ)
    (wf★ˢ , wfBaseˢ)
    (tag-or-idᵈ , ℕ?ⁿ⊒)
    (tag-or-idᵈ , ℕ?ⁿ⊒)

raw-right-tag-counterexample :
  0 ∣ [] ∣ ℕ?ⁿ ∷ [] ⊢ ` zero ⊒ ` zero ⟨ ℕᵗ ! ⟩ ∶ id ★
raw-right-tag-counterexample =
  ⊒cast+ id★⊒
    (compose-left-fillⁿ
      empty-store-det
      id★⊒
      (fill-untag-id (‵ `ℕ))
      ℕ?ⁿ⊒
      ℕ?ⁿ≈ℕ?ⁿ)
    (x⊒x ℕ?ⁿ⊒ Z)
