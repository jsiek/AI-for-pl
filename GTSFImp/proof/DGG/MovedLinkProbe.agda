module proof.DGG.MovedLinkProbe where

-- File Charter:
--   * Records the moved-target link that M2 removes from `RebaseAt`.
--   * The old inner link relocated target `Y′` from one old center to
--     another; this is now impossible because every old target center is
--     frozen by the rebase relation.
--   * The concrete worlds remain as a design record for the excluded
--     relocation.
--   * See Rationale.md, section "Seal peeling and world support".

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

open import Types
open import TyStore using
  (TyStore; store-empty; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import Consistency using
  (Env∼; X∼★; _⊢_∼_; _↪ᵗ_; empty; keep; skip; _!; id)
open import Imprecision
open import Conversion using (seal)
open import CastTerms
open import Primitives using (κℕ)
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  (World; world; _⊑ᵂ⟨_⟩_; _⊢↓[_]_; _∣_⊢²_⊑_∶_;
   RebaseAt; rebase-at; same-runtime; store-rep-imp; ⊢↓-sealˣ)

private
  X : TyVar 1
  X = Fin.zero

  Y : TyVar 2
  Y = Fin.zero

  Y′ : TyVar 2
  Y′ = Fin.suc Fin.zero

------------------------------------------------------------------------
-- Stores, embeddings, and worlds
------------------------------------------------------------------------

probe-src-store : TyStore 1
probe-src-store = store-bind store-empty ★

probe-tgt-store : TyStore 2
probe-tgt-store = store-bind (store-bind store-empty ★) ★

probe-μ : ImpEnv 3
probe-μ Fin.zero = X⊑★
probe-μ (Fin.suc Fin.zero) = X⊑★
probe-μ (Fin.suc (Fin.suc Fin.zero)) = X⊑★

η-X-a : 1 ↪ᵗ 3
η-X-a = keep (skip (skip empty))

η-X-b : 1 ↪ᵗ 3
η-X-b = skip (keep (skip empty))

η-YY′-ab : 2 ↪ᵗ 3
η-YY′-ab = keep (keep (skip empty))

η-YY′-ac : 2 ↪ᵗ 3
η-YY′-ac = keep (skip (keep empty))

-- Final placement table (a = 0, b = 1, c = 2):
--
--             X    Y    Y′
--   probe-W₁   a    a    b
--   probe-W₄   b    a    b
--   probe-W₅   a    a    c
--   probe-W₆   a    a    c
--
-- Thus Y < Y′ in every target embedding.  At the inner boundary,
-- X is re-paired from Y′ at b to Y at a while Y′ moves from b to c.

probe-W₁ : World 1 2 3
probe-W₁ =
  world η-X-a η-YY′-ab probe-μ probe-src-store probe-tgt-store

probe-W₄ : World 1 2 3
probe-W₄ =
  world η-X-b η-YY′-ab probe-μ probe-src-store probe-tgt-store

probe-W₅ : World 1 2 3
probe-W₅ =
  world η-X-a η-YY′-ac probe-μ probe-src-store probe-tgt-store

probe-W₆ : World 1 2 3
probe-W₆ = probe-W₅

probe-W₁-WF : CTI2.WFWorld probe-W₁
probe-W₁-WF Fin.zero ()

probe-W₄-WF : CTI2.WFWorld probe-W₄
probe-W₄-WF Fin.zero ()

probe-W₅-WF : CTI2.WFWorld probe-W₅
probe-W₅-WF Fin.zero ()

probe-W₆-WF : CTI2.WFWorld probe-W₆
probe-W₆-WF Fin.zero ()

------------------------------------------------------------------------
-- Store typing and casts
------------------------------------------------------------------------

probe-src-X∋ : probe-src-store ∋ X ⦂ ★
probe-src-X∋ = Z∋ refl

probe-tgt-Y∋ : probe-tgt-store ∋ Y ⦂ ★
probe-tgt-Y∋ = Z∋ refl

probe-tgt-Y′∋ : probe-tgt-store ∋ Y′ ⦂ ★
probe-tgt-Y′∋ = S-bind∋ (Z∋ refl) refl

probe-X-seal-⊢ : probe-src-store ⊢↓[ just X ] seal X ★
probe-X-seal-⊢ = ⊢↓-sealˣ probe-src-X∋

probe-Y-seal-⊢ : probe-tgt-store ⊢↓[ just Y ] seal Y ★
probe-Y-seal-⊢ = ⊢↓-sealˣ probe-tgt-Y∋

probe-Y′-seal-⊢ : probe-tgt-store ⊢↓[ just Y′ ] seal Y′ ★
probe-Y′-seal-⊢ = ⊢↓-sealˣ probe-tgt-Y′∋

private
  probe-src-env : Env∼ 1
  probe-src-env Fin.zero = X∼★

  probe-tgt-env : Env∼ 2
  probe-tgt-env Fin.zero = X∼★
  probe-tgt-env (Fin.suc Fin.zero) = X∼★

  probe-ℕ!ᴸ : probe-src-env ⊢ (‵ `ℕ) ∼ ★
  probe-ℕ!ᴸ = id (‵ `ℕ) !

  probe-ℕ!ᴿ : probe-tgt-env ⊢ (‵ `ℕ) ∼ ★
  probe-ℕ!ᴿ = id (‵ `ℕ) !

  probe-Y′! : probe-tgt-env ⊢ ＇ Y′ ∼ ★
  probe-Y′! = id { μ = probe-tgt-env } (＇ Y′) !

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

probe-V₀ : Term 1
probe-V₀ = ($ (κℕ 0)) ⟨ probe-ℕ!ᴸ ⟩

probe-V : Term 1
probe-V = probe-V₀ ↓ seal X ★

probe-M₅ : Term 2
probe-M₅ = ($ (κℕ 0)) ⟨ probe-ℕ!ᴿ ⟩

probe-M′ : Term 2
probe-M′ = probe-M₅ ↓ seal Y′ ★

probe-U : Term 2
probe-U = probe-M′ ⟨ probe-Y′! ⟩

------------------------------------------------------------------------
-- Rebase witnesses
------------------------------------------------------------------------

probe-X-Y-rep₁ : CTI2.StoreRepImp probe-W₁ X Y
probe-X-Y-rep₁ = store-rep-imp ★⊑★

probe-outer-target-rebase : RebaseAt probe-W₄ probe-W₁ X Y
probe-outer-target-rebase =
  rebase-at (same-runtime refl refl)
    (λ { {Fin.zero} X≢ → ⊥-elim (X≢ refl) })
    (λ _ → refl)
    refl probe-X-Y-rep₁

probe-X-Y′-rep₄ : CTI2.StoreRepImp probe-W₄ X Y′
probe-X-Y′-rep₄ = store-rep-imp ★⊑★

probe-X-Y-rep₅ : CTI2.StoreRepImp probe-W₅ X Y
probe-X-Y-rep₅ = store-rep-imp ★⊑★

probe-inner-source-rebase : RebaseAt probe-W₆ probe-W₅ X Y
probe-inner-source-rebase =
  CTI2.sameWorldRebaseAt refl probe-X-Y-rep₅

------------------------------------------------------------------------
-- Checkpoint 1: moved-pivot anchoring excludes the inner link
------------------------------------------------------------------------

probe-link-ill-formed :
  ¬ (RebaseAt probe-W₅ probe-W₄ X Y′)
probe-link-ill-formed rb
    with CTI2.RebaseAt.ηᴿ-frozen rb Y′
probe-link-ill-formed rb | ()

------------------------------------------------------------------------
-- Checkpoint 2: the corresponding inversion output is empty
------------------------------------------------------------------------

qOut : ＇ X ⊑ᵂ⟨ probe-W₁ ⟩ ＇ Y
qOut = X⊑X

probe-no-output :
  ¬ (probe-W₁ ∣ [] ⊢² probe-V ⊑ probe-U ∶ qOut)
probe-no-output
    (CTI2.conceal⊑² {p = p} ok mono rb sc c⊢ prem q) with p
probe-no-output
    (CTI2.conceal⊑² {p = p} ok mono rb sc c⊢ prem q) | ()
