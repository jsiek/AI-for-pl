module proof.DGG.SealPeelProbe where

-- File Charter:
--   * Records the seal-peeling geometry whose input previously moved an
--     old target center.
--   * M2 removes that freedom: both the outer and inner target-moving
--     rebases are now empty by `ηᴿ-frozen`.
--   * The remaining worlds and stores are kept as a design record for
--     the excluded pre-M2 input shape.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)

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
open CTI2 using
  (World; world; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_;
   RebaseAt; rebase-at; same-runtime; store-rep-imp)

private
  Xᴸ : TyVar 2
  Xᴸ = Fin.zero

  X₂ : TyVar 2
  X₂ = Fin.suc Fin.zero

  Y : TyVar 1
  Y = Fin.zero

  c0 : TyVar 3
  c0 = Fin.zero

  c1 : TyVar 3
  c1 = Fin.suc Fin.zero

  c2 : TyVar 3
  c2 = Fin.suc (Fin.suc Fin.zero)

------------------------------------------------------------------------
-- Stores, embeddings, and worlds
------------------------------------------------------------------------

probe-src-store : TyStore 2
probe-src-store = store-bind (store-bind store-empty ★) ★

probe-tgt-store : TyStore 1
probe-tgt-store = store-bind store-empty ★

probe-μ : ImpEnv 3
probe-μ Fin.zero = X⊑★
probe-μ (Fin.suc Fin.zero) = X⊑★
probe-μ (Fin.suc (Fin.suc Fin.zero)) = X⊑★

ηᴸ-main : 2 ↪ᵗ 3
ηᴸ-main = keep (keep (skip empty))

ηᴸ-moved : 2 ↪ᵗ 3
ηᴸ-moved = keep (skip (keep empty))

ηᴿ-c0 : 1 ↪ᵗ 3
ηᴿ-c0 = keep (skip (skip empty))

ηᴿ-c1 : 1 ↪ᵗ 3
ηᴿ-c1 = skip (keep (skip empty))

ηᴿ-c2 : 1 ↪ᵗ 3
ηᴿ-c2 = skip (skip (keep empty))

probe-W : World 2 1 3
probe-W =
  world ηᴸ-main ηᴿ-c0 probe-μ probe-src-store probe-tgt-store

probe-W′ : World 2 1 3
probe-W′ =
  world ηᴸ-main ηᴿ-c1 probe-μ probe-src-store probe-tgt-store

probe-W₄ : World 2 1 3
probe-W₄ =
  world ηᴸ-moved ηᴿ-c2 probe-μ probe-src-store probe-tgt-store

probe-Wᵖ : World 2 1 3
probe-Wᵖ =
  world ηᴸ-main ηᴿ-c2 probe-μ probe-src-store probe-tgt-store

probe-W-WF : CTI2.WFWorld probe-W
probe-W-WF Fin.zero ()
probe-W-WF (Fin.suc Fin.zero) ()

probe-W′-WF : CTI2.WFWorld probe-W′
probe-W′-WF Fin.zero ()
probe-W′-WF (Fin.suc Fin.zero) ()

probe-W₄-WF : CTI2.WFWorld probe-W₄
probe-W₄-WF Fin.zero ()
probe-W₄-WF (Fin.suc Fin.zero) ()

probe-Wᵖ-WF : CTI2.WFWorld probe-Wᵖ
probe-Wᵖ-WF Fin.zero ()
probe-Wᵖ-WF (Fin.suc Fin.zero) ()

------------------------------------------------------------------------
-- Store typing and casts
------------------------------------------------------------------------

probe-src-Xᴸ∋ : probe-src-store ∋ Xᴸ ⦂ ★
probe-src-Xᴸ∋ = Z∋ refl

probe-src-X₂∋ : probe-src-store ∋ X₂ ⦂ ★
probe-src-X₂∋ = S-bind∋ (Z∋ refl) refl

probe-tgt-Y∋ : probe-tgt-store ∋ Y ⦂ ★
probe-tgt-Y∋ = Z∋ refl

probe-Xᴸ-seal-⊢ : probe-src-store Conv.⊢↓[ just Xᴸ ] seal Xᴸ ★
probe-Xᴸ-seal-⊢ = Conv.⊢↓-sealˣ probe-src-Xᴸ∋

probe-X₂-seal-⊢ : probe-src-store Conv.⊢↓[ just X₂ ] seal X₂ ★
probe-X₂-seal-⊢ = Conv.⊢↓-sealˣ probe-src-X₂∋

probe-Y-seal-⊢ : probe-tgt-store Conv.⊢↓[ just Y ] seal Y ★
probe-Y-seal-⊢ = Conv.⊢↓-sealˣ probe-tgt-Y∋

private
  probe-src-env : Env∼ 2
  probe-src-env Fin.zero = X∼★
  probe-src-env (Fin.suc Fin.zero) = X∼★

  probe-tgt-env : Env∼ 1
  probe-tgt-env Fin.zero = X∼★

  probe-ℕ!ᴸ : probe-src-env ⊢ (‵ `ℕ) ∼ ★
  probe-ℕ!ᴸ = id (‵ `ℕ) !

  probe-ℕ!ᴿ : probe-tgt-env ⊢ (‵ `ℕ) ∼ ★
  probe-ℕ!ᴿ = id (‵ `ℕ) !

  probe-X₂! : probe-src-env ⊢ ＇ X₂ ∼ ★
  probe-X₂! = id {μ = probe-src-env} (＇ X₂) !

  probe-Y! : probe-tgt-env ⊢ ＇ Y ∼ ★
  probe-Y! = id {μ = probe-tgt-env} (＇ Y) !

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

probe-U₀ : Term 1
probe-U₀ = ($ (κℕ 0)) ⟨ probe-ℕ!ᴿ ⟩

probe-V₀₀ : Term 2
probe-V₀₀ = ($ (κℕ 0)) ⟨ probe-ℕ!ᴸ ⟩

probe-V₁ : Term 2
probe-V₁ = probe-V₀₀ ↓ seal X₂ ★

probe-V : Term 2
probe-V = probe-V₁ ⟨ probe-X₂! ⟩

probe-M : Term 2
probe-M = probe-V ↓ seal Xᴸ ★

probe-U₁ : Term 1
probe-U₁ = probe-U₀ ↓ seal Y ★

probe-N! : Term 1
probe-N! = probe-U₁ ⟨ probe-Y! ⟩

------------------------------------------------------------------------
-- Rebase witnesses
------------------------------------------------------------------------

probe-Xᴸ-Y-rep : CTI2.StoreRepImp probe-W Xᴸ Y
probe-Xᴸ-Y-rep = store-rep-imp ★⊑★

probe-outer-input-rebase-empty :
  RebaseAt probe-W′ probe-W Xᴸ Y → ⊥
probe-outer-input-rebase-empty rb
    with CTI2.RebaseAt.ηᴿ-frozen rb Y
probe-outer-input-rebase-empty rb | ()

probe-X₂-Y-rep′ : CTI2.StoreRepImp probe-W′ X₂ Y
probe-X₂-Y-rep′ = store-rep-imp ★⊑★

probe-inner-target-rebase-empty :
  RebaseAt probe-W₄ probe-W′ X₂ Y → ⊥
probe-inner-target-rebase-empty rb
    with CTI2.RebaseAt.ηᴿ-frozen rb Y
probe-inner-target-rebase-empty rb | ()

probe-X₂-Y-rep₄ : CTI2.StoreRepImp probe-W₄ X₂ Y
probe-X₂-Y-rep₄ = store-rep-imp ★⊑★

probe-inner-source-rebase : RebaseAt probe-W₄ probe-W₄ X₂ Y
probe-inner-source-rebase =
  CTI2.sameWorldRebaseAt refl probe-X₂-Y-rep₄
