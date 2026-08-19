module proof.DGG.TagBoundaryProbe where

-- File Charter:
--   * This probe decides the tag-boundary stratum (H-tag in
--     SealTransfer).
--   * Checkpoint 1 records that a variable-ground tag can be aligned
--     only in interior worlds even when no target variable moves.
--   * Checkpoint 2 records that the corresponding inversion output is
--     empty at the outer world.

open import Data.Empty using (⊥-elim)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality
  using (_≢_; refl)
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
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
open CTX using
  (World;
   world;
   _⊑ᵂ⟨_⟩_;
   RebaseAt;
   rebase-at;
   same-runtime;
   store-rep-imp)
open CTI2 using (_∣_⊢²_⊑_∶_)

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

probe-μ : ImpEnv 2
probe-μ Fin.zero = X⊑★
probe-μ (Fin.suc Fin.zero) = X⊑★

η-X-a : 1 ↪ᵗ 2
η-X-a = keep (skip empty)

η-X-b : 1 ↪ᵗ 2
η-X-b = skip (keep empty)

η-YY′-ab : 2 ↪ᵗ 2
η-YY′-ab = keep (keep empty)

-- Final placement table (a = 0, b = 1):
--
--             X    Y    Y′
--   probe-W₁   a    a    b
--   probe-W₄   b    a    b
--   probe-W₅   b    a    b
--
-- Only X moves, from a to b.  Both target variables remain fixed.

probe-W₁ : World 1 2 2
probe-W₁ =
  world η-X-a η-YY′-ab probe-μ probe-src-store probe-tgt-store

probe-W₄ : World 1 2 2
probe-W₄ =
  world η-X-b η-YY′-ab probe-μ probe-src-store probe-tgt-store

probe-W₅ : World 1 2 2
probe-W₅ =
  world η-X-b η-YY′-ab probe-μ probe-src-store probe-tgt-store

probe-W₁-WF : CTX.WFWorld probe-W₁
probe-W₁-WF Fin.zero ()

probe-W₄-WF : CTX.WFWorld probe-W₄
probe-W₄-WF Fin.zero ()

probe-W₅-WF : CTX.WFWorld probe-W₅
probe-W₅-WF Fin.zero ()

------------------------------------------------------------------------
-- Store typing and casts
------------------------------------------------------------------------

probe-src-X∋ : probe-src-store ∋ X ⦂ ★
probe-src-X∋ = Z∋ refl

probe-tgt-Y∋ : probe-tgt-store ∋ Y ⦂ ★
probe-tgt-Y∋ = Z∋ refl

probe-tgt-Y′∋ : probe-tgt-store ∋ Y′ ⦂ ★
probe-tgt-Y′∋ = S-bind∋ (Z∋ refl) refl

probe-X-seal-⊢ : probe-src-store Conv.⊢↓[ just X ] seal X ★
probe-X-seal-⊢ = Conv.⊢↓-sealˣ probe-src-X∋

probe-Y-seal-⊢ : probe-tgt-store Conv.⊢↓[ just Y ] seal Y ★
probe-Y-seal-⊢ = Conv.⊢↓-sealˣ probe-tgt-Y∋

probe-Y′-seal-⊢ : probe-tgt-store Conv.⊢↓[ just Y′ ] seal Y′ ★
probe-Y′-seal-⊢ = Conv.⊢↓-sealˣ probe-tgt-Y′∋

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

probe-X-Y-rep₁ : CTX.StoreRepImp probe-W₁ X Y
probe-X-Y-rep₁ = store-rep-imp ★⊑★

probe-outer-target-rebase : RebaseAt probe-W₄ probe-W₁ X Y
probe-outer-target-rebase =
  rebase-at (same-runtime refl refl)
    (λ { {Fin.zero} X≢ → ⊥-elim (X≢ refl) })
    (λ _ → refl)
    refl probe-X-Y-rep₁

probe-X-Y′-rep₄ : CTX.StoreRepImp probe-W₄ X Y′
probe-X-Y′-rep₄ = store-rep-imp ★⊑★

probe-inner-target-rebase : RebaseAt probe-W₅ probe-W₄ X Y′
probe-inner-target-rebase =
  rebase-at (same-runtime refl refl)
    (λ { {Fin.zero} X≢ → ⊥-elim (X≢ refl) })
    (λ _ → refl)
    refl probe-X-Y′-rep₄

probe-X-Y′-rep₅ : CTX.StoreRepImp probe-W₅ X Y′
probe-X-Y′-rep₅ = store-rep-imp ★⊑★

probe-inner-source-rebase : RebaseAt probe-W₅ probe-W₅ X Y′
probe-inner-source-rebase =
  CTX.sameWorldRebaseAt refl probe-X-Y′-rep₅

probe-inner-pair-rebase : RebaseAt probe-W₄ probe-W₄ X Y′
probe-inner-pair-rebase =
  CTX.sameWorldRebaseAt refl probe-X-Y′-rep₄

------------------------------------------------------------------------
-- Checkpoint 1: the interior tag-boundary input
------------------------------------------------------------------------

pIn : ＇ X ⊑ᵂ⟨ probe-W₁ ⟩ ＇ Y
pIn = X⊑X

p₄ : ＇ X ⊑ᵂ⟨ probe-W₄ ⟩ ★
p₄ = X⊑★ refl

pTag : ＇ X ⊑ᵂ⟨ probe-W₄ ⟩ ＇ Y′
pTag = X⊑X

p₅ : ＇ X ⊑ᵂ⟨ probe-W₅ ⟩ ★
p₅ = X⊑★ refl

probe-base² :
  probe-W₅ ∣ [] ⊢² probe-V₀ ⊑ probe-M₅ ∶ ★⊑★
probe-base² =
  CTI2.cast⊑cast² probe-ℕ!ᴸ probe-ℕ!ᴿ
    (CTI2.κ⊑κ² (κℕ 0) ι⊑ι) ★⊑★

probe-inner-seal² :
  probe-W₄ ∣ [] ⊢² probe-V ⊑ probe-M′ ∶ pTag
probe-inner-seal² =
  CTI2.conceal⊑conceal²
    (CTX.matched-seal-star-partner
      (CTX.rep★-nonvar-tag nonvar-base))
    (λ _ eq → eq) probe-inner-pair-rebase
    CTX.same-[] probe-X-seal-⊢ probe-Y′-seal-⊢ probe-base² pTag

probe-tag² :
  probe-W₄ ∣ [] ⊢² probe-V ⊑ probe-U ∶ p₄
probe-tag² = CTI2.⊑cast² probe-Y′! probe-inner-seal² p₄

probe-input :
  probe-W₁ ∣ [] ⊢² probe-V ⊑ (probe-U ↓ seal Y ★) ∶ pIn
probe-input =
  CTI2.⊑conceal² (λ _ eq → eq)
    (CTX.rebase-varᴿ probe-outer-target-rebase)
    CTX.same-[] probe-Y-seal-⊢ probe-tag² pIn

------------------------------------------------------------------------
-- Checkpoint 2: the outer-world output is empty
------------------------------------------------------------------------

qOut : ＇ X ⊑ᵂ⟨ probe-W₁ ⟩ ＇ Y
qOut = X⊑X

probe-no-output :
  ¬ (probe-W₁ ∣ [] ⊢² probe-V ⊑ probe-U ∶ qOut)
probe-no-output
    (CTI2.conceal⊑²-seal-star-open {p = p}
      no-target mono rb sc c⊢ prem q) with p
probe-no-output
    (CTI2.conceal⊑²-seal-star-open {p = p}
      no-target mono rb sc c⊢ prem q) | ()
probe-no-output
    (CTI2.conceal⊑²-source-ok {p = p} ok mono rb sc c⊢ prem q) with p
probe-no-output
    (CTI2.conceal⊑²-source-ok {p = p} ok mono rb sc c⊢ prem q) | ()
