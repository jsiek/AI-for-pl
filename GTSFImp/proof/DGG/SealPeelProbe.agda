module proof.DGG.SealPeelProbe where

-- File Charter:
--   * This probe records that inputs whose interior worlds move a
--     third-party pivot are derivable and mark-honest, so no invariant
--     excludes them.
--   * It also records that the right-injection inversion output remains
--     derivable by rebuilding link-by-link at freshly chosen premise
--     worlds, rather than by transporting interior derivations.
--   * The output rebuild uses the world where X₂ and Y are aligned, so
--     its inner source seal has a same-world variable rebase.
--   * See Rationale.md, section "Seal peeling and world support".

open import Data.Empty using (⊥-elim)
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
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  (World; world; _⊑ᵂ⟨_⟩_; _⊢↓[_]_; _∣_⊢²_⊑_∶_;
   RebaseAt; rebase-at; same-runtime; store-rep-imp; ⊢↓-sealˣ)

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

probe-Xᴸ-seal-⊢ : probe-src-store ⊢↓[ just Xᴸ ] seal Xᴸ ★
probe-Xᴸ-seal-⊢ = ⊢↓-sealˣ probe-src-Xᴸ∋

probe-X₂-seal-⊢ : probe-src-store ⊢↓[ just X₂ ] seal X₂ ★
probe-X₂-seal-⊢ = ⊢↓-sealˣ probe-src-X₂∋

probe-Y-seal-⊢ : probe-tgt-store ⊢↓[ just Y ] seal Y ★
probe-Y-seal-⊢ = ⊢↓-sealˣ probe-tgt-Y∋

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

probe-outer-input-rebase : RebaseAt probe-W′ probe-W Xᴸ Y
probe-outer-input-rebase =
  rebase-at (same-runtime refl refl)
    (λ _ → refl)
    (λ { {Fin.zero} Y≢ → ⊥-elim (Y≢ refl) })
    refl (λ _ → X₂ , refl) probe-Xᴸ-Y-rep

probe-X₂-Y-rep′ : CTI2.StoreRepImp probe-W′ X₂ Y
probe-X₂-Y-rep′ = store-rep-imp ★⊑★

probe-inner-target-rebase : RebaseAt probe-W₄ probe-W′ X₂ Y
probe-inner-target-rebase =
  rebase-at (same-runtime refl refl)
    (λ { {Fin.zero} _ → refl
       ; {Fin.suc Fin.zero} X₂≢ → ⊥-elim (X₂≢ refl) })
    (λ { {Fin.zero} Y≢ → ⊥-elim (Y≢ refl) })
    refl (λ _ → X₂ , refl) probe-X₂-Y-rep′

probe-X₂-Y-rep₄ : CTI2.StoreRepImp probe-W₄ X₂ Y
probe-X₂-Y-rep₄ = store-rep-imp ★⊑★

probe-inner-source-rebase : RebaseAt probe-W₄ probe-W₄ X₂ Y
probe-inner-source-rebase =
  CTI2.sameWorldRebaseAt refl probe-X₂-Y-rep₄

probe-output-inner-source-rebase : RebaseAt probe-W′ probe-W′ X₂ Y
probe-output-inner-source-rebase =
  CTI2.sameWorldRebaseAt refl probe-X₂-Y-rep′

------------------------------------------------------------------------
-- Checkpoint 1: the movable-interior input
------------------------------------------------------------------------

pIn : ＇ Xᴸ ⊑ᵂ⟨ probe-W ⟩ ★
pIn = X⊑★ refl

pMid : ＇ X₂ ⊑ᵂ⟨ probe-W′ ⟩ ＇ Y
pMid = X⊑X

p₄ : ＇ X₂ ⊑ᵂ⟨ probe-W₄ ⟩ ★
p₄ = X⊑★ refl

probe-base² :
  probe-W₄ ∣ [] ⊢² probe-V₀₀ ⊑ probe-U₀ ∶ ★⊑★
probe-base² =
  CTI2.cast⊑cast² probe-ℕ!ᴸ probe-ℕ!ᴿ
    (CTI2.κ⊑κ² (κℕ 0) ι⊑ι) ★⊑★

probe-inner-seal² :
  probe-W₄ ∣ [] ⊢² probe-V₁ ⊑ probe-U₀ ∶ p₄
probe-inner-seal² =
  CTI2.conceal⊑² (λ _ eq → eq)
    (CTI2.rebase-varᴸ probe-inner-source-rebase)
    CTI2.same-[] probe-X₂-seal-⊢ probe-base² p₄

probe-target-seal² :
  probe-W′ ∣ [] ⊢² probe-V₁ ⊑ probe-U₁ ∶ pMid
probe-target-seal² =
  CTI2.⊑conceal² (λ _ eq → eq)
    (CTI2.rebase-varᴿ probe-inner-target-rebase)
    CTI2.same-[] probe-Y-seal-⊢ probe-inner-seal² pMid

probe-paired-tags² :
  probe-W′ ∣ [] ⊢² probe-V ⊑ probe-N! ∶ ★⊑★
probe-paired-tags² =
  CTI2.cast⊑cast² probe-X₂! probe-Y! probe-target-seal² ★⊑★

probe-input :
  probe-W ∣ [] ⊢² probe-M ⊑ probe-N! ∶ pIn
probe-input =
  CTI2.conceal⊑² (λ _ eq → eq)
    (CTI2.rebase-varᴸ probe-outer-input-rebase)
    CTI2.same-[] probe-Xᴸ-seal-⊢ probe-paired-tags² pIn

------------------------------------------------------------------------
-- Checkpoint 2: the link-by-link inversion output
------------------------------------------------------------------------

qOut : ＇ Xᴸ ⊑ᵂ⟨ probe-W ⟩ ＇ Y
qOut = X⊑X

pᵛ : ＇ X₂ ⊑ᵂ⟨ probe-W′ ⟩ ★
pᵛ = X⊑★ refl

probe-output-base² :
  probe-W′ ∣ [] ⊢² probe-V₀₀ ⊑ probe-U₀ ∶ ★⊑★
probe-output-base² =
  CTI2.cast⊑cast² probe-ℕ!ᴸ probe-ℕ!ᴿ
    (CTI2.κ⊑κ² (κℕ 0) ι⊑ι) ★⊑★

probe-output-inner-seal² :
  probe-W′ ∣ [] ⊢² probe-V₁ ⊑ probe-U₀ ∶ pᵛ
probe-output-inner-seal² =
  CTI2.conceal⊑² (λ _ eq → eq)
    (CTI2.rebase-varᴸ probe-output-inner-source-rebase)
    CTI2.same-[] probe-X₂-seal-⊢ probe-output-base² pᵛ

probe-output-tag² :
  probe-W′ ∣ [] ⊢² probe-V ⊑ probe-U₀ ∶ ★⊑★
probe-output-tag² =
  CTI2.cast⊑² probe-X₂! probe-output-inner-seal² ★⊑★

probe-output :
  probe-W ∣ [] ⊢² probe-M ⊑ probe-U₁ ∶ qOut
probe-output =
  CTI2.conceal⊑conceal² (λ _ eq → eq)
    probe-outer-input-rebase CTI2.same-[]
    probe-Xᴸ-seal-⊢ probe-Y-seal-⊢ probe-output-tag² qOut
