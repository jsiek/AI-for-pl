module proof.DGG.ChainRideProbe where

-- File Charter:
--   * Records the pre-M2 chain-ride construction for the H-multi stratum.
--   * The old construction moved one target pivot down a chain of old
--     centers.  M2 removes that freedom by freezing every old target
--     variable in `RebaseAt`.
--   * The concrete worlds and premise remain as a design record; the
--     moving links are now proved empty.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)

open import Types
open import TyStore using
  (TyStore; store-empty; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import Consistency using
  (Env∼; X∼★; _⊢_∼_; _↪ᵗ_; empty; keep; skip; toRenameᵗ; _!; id)
open import Imprecision
open import Conversion using (seal)
open import CastTerms
open import Primitives using (κℕ)
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  (World; world; _⊑ᵂ⟨_⟩_; _⊢↓[_]_; _∣_⊢²_⊑_∶_;
   RebaseAt; rebase-at; same-runtime; store-rep-imp; ⊢↓-sealˣ)

private
  Z : TyVar 2
  Z = Fin.zero

  Z₃ : TyVar 2
  Z₃ = Fin.suc Fin.zero

  Y : TyVar 1
  Y = Fin.zero

  a : TyVar 3
  a = Fin.zero

  b : TyVar 3
  b = Fin.suc Fin.zero

  c : TyVar 3
  c = Fin.suc (Fin.suc Fin.zero)

------------------------------------------------------------------------
-- Stores, embeddings, and worlds
------------------------------------------------------------------------

sourceStore : TyStore 2
sourceStore =
  store-bind (store-bind store-empty ★) (＇ Fin.zero)

targetStore : TyStore 1
targetStore = store-bind store-empty ★

probe-μ : ImpEnv 3
probe-μ Fin.zero = X⊑★
probe-μ (Fin.suc Fin.zero) = X⊑★
probe-μ (Fin.suc (Fin.suc Fin.zero)) = X⊑★

ηᴸ-ab : 2 ↪ᵗ 3
ηᴸ-ab = keep (keep (skip empty))

ηᴸ-ac : 2 ↪ᵗ 3
ηᴸ-ac = keep (skip (keep empty))

ηᴿ-a : 1 ↪ᵗ 3
ηᴿ-a = keep (skip (skip empty))

ηᴿ-b : 1 ↪ᵗ 3
ηᴿ-b = skip (keep (skip empty))

ηᴿ-c : 1 ↪ᵗ 3
ηᴿ-c = skip (skip (keep empty))

-- Placement table (a = 0, b = 1, c = 2):
--
--       Z   Z₃   Y
--   W₁   a   b   a
--   Wₗ   a   b   b
--   W₂   a   c   c

W₁ : World 2 1 3
W₁ = world ηᴸ-ab ηᴿ-a probe-μ sourceStore targetStore

Wₗ : World 2 1 3
Wₗ = world ηᴸ-ab ηᴿ-b probe-μ sourceStore targetStore

W₂ : World 2 1 3
W₂ = world ηᴸ-ac ηᴿ-c probe-μ sourceStore targetStore

------------------------------------------------------------------------
-- Store membership and conversion typing
------------------------------------------------------------------------

probe-Z∋ : sourceStore ∋ Z ⦂ ＇ Z₃
probe-Z∋ = Z∋ refl

probe-Z₃∋ : sourceStore ∋ Z₃ ⦂ ★
probe-Z₃∋ = S-bind∋ (Z∋ refl) refl

probe-Z-seal-⊢ : sourceStore ⊢↓[ just Z ] seal Z (＇ Z₃)
probe-Z-seal-⊢ = ⊢↓-sealˣ probe-Z∋

probe-Z₃-seal-⊢ : sourceStore ⊢↓[ just Z₃ ] seal Z₃ ★
probe-Z₃-seal-⊢ = ⊢↓-sealˣ probe-Z₃∋

private
  probe-source-env : Env∼ 2
  probe-source-env Fin.zero = X∼★
  probe-source-env (Fin.suc Fin.zero) = X∼★

  probe-target-env : Env∼ 1
  probe-target-env Fin.zero = X∼★

  probe-ℕ!ᴸ : probe-source-env ⊢ (‵ `ℕ) ∼ ★
  probe-ℕ!ᴸ = id (‵ `ℕ) !

  probe-ℕ!ᴿ : probe-target-env ⊢ (‵ `ℕ) ∼ ★
  probe-ℕ!ᴿ = id (‵ `ℕ) !

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

V₀ : Term 2
V₀ = ($ (κℕ 0)) ⟨ probe-ℕ!ᴸ ⟩

V : Term 2
V = V₀ ↓ seal Z₃ ★

U : Term 1
U = ($ (κℕ 0)) ⟨ probe-ℕ!ᴿ ⟩

------------------------------------------------------------------------
-- Rebase witnesses
------------------------------------------------------------------------

probe-Z-Y-rep₁ : CTI2.StoreRepImp W₁ Z Y
probe-Z-Y-rep₁ = store-rep-imp ★⊑★

raₗ-empty : RebaseAt Wₗ W₁ Z Y → ⊥
raₗ-empty rb with CTI2.RebaseAt.ηᴿ-frozen rb Y
raₗ-empty rb | ()

probe-Z₃-Y-repₗ : CTI2.StoreRepImp Wₗ Z₃ Y
probe-Z₃-Y-repₗ = store-rep-imp ★⊑★

link₂-empty : RebaseAt W₂ Wₗ Z₃ Y → ⊥
link₂-empty rb with CTI2.RebaseAt.ηᴿ-frozen rb Y
link₂-empty rb | ()

probe-Z₃-Y-rep₂ : CTI2.StoreRepImp W₂ Z₃ Y
probe-Z₃-Y-rep₂ = store-rep-imp ★⊑★

probe-premise-rebase : RebaseAt W₂ W₂ Z₃ Y
probe-premise-rebase =
  CTI2.sameWorldRebaseAt refl probe-Z₃-Y-rep₂

probe-output-link : RebaseAt W₁ W₁ Z Y
probe-output-link = CTI2.sameWorldRebaseAt refl probe-Z-Y-rep₁

------------------------------------------------------------------------
-- Checkpoint 1: the complete H-multi input data
------------------------------------------------------------------------

p₁ : (＇ Z) ⊑ᵂ⟨ W₁ ⟩ (＇ Y)
p₁ = X⊑X

probe-moved :
  toRenameᵗ (CTI2.ηᴸʷ W₂) Z₃ ≢ toRenameᵗ (CTI2.ηᴸʷ W₁) Z₃
probe-moved ()

probe-mono₁ₗ : CTI2.ImpEnvMono W₁ Wₗ
probe-mono₁ₗ X eq = eq

probe-monoₗ₂ : CTI2.ImpEnvMono Wₗ W₂
probe-monoₗ₂ X eq = eq

probe-same₁ₗ : CTI2.SameCtx {W = W₁} {W′ = Wₗ} [] []
probe-same₁ₗ = CTI2.same-[]

probe-sameₗ₂ : CTI2.SameCtx {W = Wₗ} {W′ = W₂} [] []
probe-sameₗ₂ = CTI2.same-[]

q₂ : (＇ Z₃) ⊑ᵂ⟨ W₂ ⟩ ★
q₂ = X⊑★ refl

probe-base² : W₂ ∣ [] ⊢² V₀ ⊑ U ∶ ★⊑★
probe-base² =
  CTI2.cast⊑cast² probe-ℕ!ᴸ probe-ℕ!ᴿ
    (CTI2.κ⊑κ² (κℕ 0) ι⊑ι) ★⊑★

probe-premise : W₂ ∣ [] ⊢² V ⊑ U ∶ q₂
probe-premise =
  CTI2.conceal⊑² (λ X eq → eq)
    (CTI2.rebase-varᴸ probe-premise-rebase)
    CTI2.same-[] probe-Z₃-seal-⊢ probe-base² q₂
