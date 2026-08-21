module proof.DGG.ChainRideProbe where

-- File Charter:
--   * Records the pre-M2 chain-ride construction for the H-multi stratum.
--   * The old construction moved one target pivot down a chain of old
--     centers.  M2 removes that freedom by freezing every old target
--     variable in `RebaseAt`.
--   * Rebuilds the concrete placements with the inductive world
--     constructors.  The B′ mark discipline now rejects the old wrapper
--     transitions and the final ＇Z₃ ⊑ ★ premise before a chain ride
--     can start.

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
  (Env∼; X∼★; _⊢_∼_; toRenameᵗ; _!; id)
open import Imprecision
open import Conversion using (seal)
open import CastTerms
open import Primitives using (κℕ)
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open CTX using
  (World;
   _⊑ᵂ⟨_⟩_;
   RebaseAt;
   rebase-at;
   same-runtime;
   store-rep-imp)
open CTI2 using (_∣_⊢²_⊑_∶_)

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

-- Stores and inductively generated worlds
------------------------------------------------------------------------

sourceStore : TyStore 2
sourceStore =
  store-bind (store-bind store-empty ★) (＇ Fin.zero)

targetStore : TyStore 1
targetStore = store-bind store-empty ★

-- Placement table (a = 0, b = 1, c = 2):
--
--       Z   Z₃   Y
--   W₁   a   b   a
--   Wₗ   a   b   b
--   W₂   a   c   c
--
-- B′ makes the matched cell precise in each snapshot.  Thus the marks
-- move from a in W₁, to b in Wₗ, to c in W₂; that movement is exactly
-- what `ImpEnvMono` now forbids inside one derivation.

W∅¹ : World 0 0 1
W∅¹ = CTX.skip-centerʷ CTX.emptyʷ

W₁-base : World 1 0 2
W₁-base = CTX.leftOnlyWorld W∅¹ ★

W₁-bind : (＇ Fin.zero) ⊑ᵂ⟨ W₁-base ⟩ ★
W₁-bind = X⊑★ refl

W₁ : World 2 1 3
W₁ = CTX.bothBindWorld W₁-base (＇ Fin.zero) ★ W₁-bind

Wₗ-base : World 1 1 2
Wₗ-base = CTX.bothBindWorld W∅¹ ★ ★ ★⊑★

Wₗ : World 2 1 3
Wₗ = CTX.leftOnlyWorld Wₗ-base (＇ Fin.zero)

W₂-base : World 1 1 1
W₂-base = CTX.bothBindWorld CTX.emptyʷ ★ ★ ★⊑★

W₂ : World 2 1 3
W₂ = CTX.leftOnlyWorld (CTX.skip-centerʷ W₂-base) (＇ Fin.zero)

------------------------------------------------------------------------
-- Store membership and conversion typing
------------------------------------------------------------------------

probe-Z∋ : sourceStore ∋ Z ⦂ ＇ Z₃
probe-Z∋ = Z∋ refl

probe-Z₃∋ : sourceStore ∋ Z₃ ⦂ ★
probe-Z₃∋ = S-bind∋ (Z∋ refl) refl

probe-Z-seal-⊢ : sourceStore Conv.⊢↓[ just Z ] seal Z (＇ Z₃)
probe-Z-seal-⊢ = Conv.⊢↓-sealˣ probe-Z∋

probe-Z₃-seal-⊢ : sourceStore Conv.⊢↓[ just Z₃ ] seal Z₃ ★
probe-Z₃-seal-⊢ = Conv.⊢↓-sealˣ probe-Z₃∋

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

probe-Z-Y-rep₁ : CTX.StoreRepImp W₁ Z Y
probe-Z-Y-rep₁ = store-rep-imp ★⊑★

raₗ-empty : RebaseAt Wₗ W₁ Z Y → ⊥
raₗ-empty rb with CTX.RebaseAt.ηᴿ-frozen rb Y
raₗ-empty rb | ()

probe-Z₃-Y-repₗ : CTX.StoreRepImp Wₗ Z₃ Y
probe-Z₃-Y-repₗ = store-rep-imp ★⊑★

link₂-empty : RebaseAt W₂ Wₗ Z₃ Y → ⊥
link₂-empty rb with CTX.RebaseAt.ηᴿ-frozen rb Y
link₂-empty rb | ()

probe-Z₃-Y-rep₂ : CTX.StoreRepImp W₂ Z₃ Y
probe-Z₃-Y-rep₂ = store-rep-imp ★⊑★

probe-premise-rebase : RebaseAt W₂ W₂ Z₃ Y
probe-premise-rebase =
  CTX.sameWorldRebaseAt refl probe-Z₃-Y-rep₂

probe-output-link : RebaseAt W₁ W₁ Z Y
probe-output-link = CTX.sameWorldRebaseAt refl probe-Z-Y-rep₁

------------------------------------------------------------------------
-- Checkpoint 1: the complete H-multi input data
------------------------------------------------------------------------

p₁ : (＇ Z) ⊑ᵂ⟨ W₁ ⟩ (＇ Y)
p₁ = X⊑X

probe-moved :
  toRenameᵗ (CTX.ηᴸʷ W₂) Z₃ ≢ toRenameᵗ (CTX.ηᴸʷ W₁) Z₃
probe-moved ()

probe-mono₁ₗ-empty : CTX.ImpEnvMono W₁ Wₗ → ⊥
probe-mono₁ₗ-empty mono
    with CTX.precise-preserved mono a refl
probe-mono₁ₗ-empty mono | ()

probe-monoₗ₂-empty : CTX.ImpEnvMono Wₗ W₂ → ⊥
probe-monoₗ₂-empty mono
    with CTX.precise-preserved mono b refl
probe-monoₗ₂-empty mono | ()

q₂-empty : (＇ Z₃) ⊑ᵂ⟨ W₂ ⟩ ★ → ⊥
q₂-empty (X⊑★ ())

probe-base² : W₂ ∣ [] ⊢² V₀ ⊑ U ∶ ★⊑★
probe-base² =
  CTI2.cast⊑cast² probe-ℕ!ᴸ probe-ℕ!ᴿ
    (CTI2.κ⊑κ² (κℕ 0) ι⊑ι) ★⊑★

probe-old-conceal-premise-empty :
  (＇ Z₃) ⊑ᵂ⟨ W₂ ⟩ ★ → ⊥
probe-old-conceal-premise-empty = q₂-empty
