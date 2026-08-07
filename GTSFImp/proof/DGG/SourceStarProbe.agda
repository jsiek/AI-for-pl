module proof.DGG.SourceStarProbe where

-- File Charter:
--   * This probe merges the checked SourceStarCounterScratch and
--     SourceStarRideCounterScratch refutations into the in-repo DGG
--     probe set.
--   * Both checkpoints use the identity two-variable world, where
--     `X₀,Y₀` occupy center `0` and `X₁,Y₁` occupy center `1`.
--   * The old source-star variable-target package would need an output
--     relating the outer source pivot `X₀` to target `Y₁` while the
--     inner cast still fixes `X₁`; order preservation collapses the two
--     source centers and refutes the package.
--   * This justifies the downstream SealChain choice to expose only the
--     `★` source-star package and to handle variable targets by a
--     paired-seal reconstruction instead.

open import Data.Empty using (⊥-elim)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (¬_)

open import Types
open import TyStore using
  (TyStore; store-empty; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import Consistency using
  (Env∼; X∼★; _⊢_∼_; _↪ᵗ_; empty; keep; skip; toRenameᵗ;
   id; _!)
open import Conversion using (seal)
open import CastTerms
open import Imprecision
open import Primitives using (κℕ)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.ImprecisionConsistency using (toRenameᵗ-injective)
open CTI2 using
  (World; world; CtxImp; RebaseAt; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_;
   store-rep-imp; sourceStoreʷ; targetStoreʷ; ηᴸʷ; ηᴿʷ)

private
  X₀ : TyVar 2
  X₀ = Fin.zero

  X₁ : TyVar 2
  X₁ = Fin.suc Fin.zero

  Y₀ : TyVar 2
  Y₀ = Fin.zero

  Y₁ : TyVar 2
  Y₁ = Fin.suc Fin.zero

------------------------------------------------------------------------
-- Stores, embeddings, and worlds
------------------------------------------------------------------------

source-store : TyStore 2
source-store = store-bind (store-bind store-empty ★) ★

target-store : TyStore 2
target-store = store-bind (store-bind store-empty ★) (＇ Fin.zero)

probe-μ : ImpEnv 2
probe-μ Fin.zero = X⊑★
probe-μ (Fin.suc Fin.zero) = X⊑★

η-id : 2 ↪ᵗ 2
η-id = keep (keep empty)

-- Placement table:
--
--             X₀  X₁  Y₀  Y₁
--   W₀         0   1   0   1

W₀ : World 2 2 2
W₀ = world η-id η-id probe-μ source-store target-store

------------------------------------------------------------------------
-- Store typing, casts, and the paired inner derivation
------------------------------------------------------------------------

X₀∈ : source-store ∋ X₀ ⦂ ★
X₀∈ = Z∋ refl

X₁∈ : source-store ∋ X₁ ⦂ ★
X₁∈ = S-bind∋ (Z∋ refl) refl

Y₁∈ : target-store ∋ Y₁ ⦂ ★
Y₁∈ = S-bind∋ (Z∋ refl) refl

X₀-Y₀-rep : CTI2.StoreRepImp W₀ X₀ Y₀
X₀-Y₀-rep = store-rep-imp ★⊑★

X₁-Y₁-rep : CTI2.StoreRepImp W₀ X₁ Y₁
X₁-Y₁-rep = store-rep-imp ★⊑★

rb₀ : RebaseAt W₀ W₀ X₀ Y₀
rb₀ = CTI2.sameWorldRebaseAt refl X₀-Y₀-rep

link₁ : RebaseAt W₀ W₀ X₁ Y₁
link₁ = CTI2.sameWorldRebaseAt refl X₁-Y₁-rep

source-env : Env∼ 2
source-env Fin.zero = X∼★
source-env (Fin.suc Fin.zero) = X∼★

target-env : Env∼ 2
target-env Fin.zero = X∼★
target-env (Fin.suc Fin.zero) = X∼★

X₁! : source-env ⊢ (＇ X₁) ∼ ★
X₁! = id (＇ X₁) !

ℕ!ᴸ : source-env ⊢ (‵ `ℕ) ∼ ★
ℕ!ᴸ = id (‵ `ℕ) !

ℕ!ᴿ : target-env ⊢ (‵ `ℕ) ∼ ★
ℕ!ᴿ = id (‵ `ℕ) !

V₀ : Term 2
V₀ = ($ (κℕ 0)) ⟨ ℕ!ᴸ ⟩

U₀ : Term 2
U₀ = ($ (κℕ 0)) ⟨ ℕ!ᴿ ⟩

V : Term 2
V = V₀ ↓ seal X₁ ★

U : Term 2
U = U₀ ↓ seal Y₁ ★

base² : W₀ ∣ [] ⊢² V₀ ⊑ U₀ ∶ ★⊑★
base² =
  CTI2.cast⊑cast² ℕ!ᴸ ℕ!ᴿ
    (CTI2.κ⊑κ² (κℕ 0) ι⊑ι) ★⊑★

q₁ : ＇ X₁ ⊑ᵂ⟨ W₀ ⟩ ＇ Y₁
q₁ = X⊑X

D : W₀ ∣ [] ⊢² V ⊑ U ∶ q₁
D =
  CTI2.conceal⊑conceal² (λ Z eq → eq) link₁ CTI2.same-[]
    (CTI2.⊢↓-sealˣ X₁∈) (CTI2.⊢↓-sealˣ Y₁∈) base² q₁

private
  X₁≢X₀ : X₁ ≢ X₀
  X₁≢X₀ ()

  Y₁≢Y₀ : Y₁ ≢ Y₀
  Y₁≢Y₀ ()

------------------------------------------------------------------------
-- Checkpoint 1: the old outer-rebase source-star package is empty
------------------------------------------------------------------------

no-source-star-var-output :
  ¬ (Σ[ Wᵒ ∈ World 2 2 2 ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
      ( RebaseAt Wᵒ W₀ X₀ Y₀
      × CTI2.ImpEnvMono W₀ Wᵒ
      × CTI2.SameCtx {W = W₀} [] γᵒ
      × Σ[ qᵒ ∈ ＇ X₀ ⊑ᵂ⟨ Wᵒ ⟩ ＇ Y₁ ]
          (Wᵒ ∣ γᵒ ⊢²
            (V ⟨ X₁! ⟩) ↓ seal X₀ ★ ⊑ U ∶ qᵒ) ))
no-source-star-var-output
    (Wᵒ , γᵒ , rb , mono , sc , qᵒ , out) =
  X₁≢X₀ (toRenameᵗ-injective (ηᴸʷ Wᵒ) (sym same-center))
  where
  target-off :
    toRenameᵗ (ηᴿʷ W₀) Y₁ ≡ toRenameᵗ (ηᴿʷ Wᵒ) Y₁
  target-off = CTI2.RebaseAt.ηᴿ-frozen rb Y₁

  source-off :
    toRenameᵗ (ηᴸʷ W₀) X₁ ≡ toRenameᵗ (ηᴸʷ Wᵒ) X₁
  source-off = CTI2.RebaseAt.ηᴸ-off-pivot rb X₁≢X₀

  same-center :
    toRenameᵗ (ηᴸʷ Wᵒ) X₀ ≡ toRenameᵗ (ηᴸʷ Wᵒ) X₁
  same-center =
    trans (ECR.variable-obligation-aligns {W = Wᵒ} {X = X₀}
      {Y = Y₁} qᵒ)
      (trans (sym target-off) source-off)

------------------------------------------------------------------------
-- Checkpoint 2: the ride-style variable branch is empty
------------------------------------------------------------------------

η₂-zero : ∀ (η : 2 ↪ᵗ 2)
  → toRenameᵗ η Fin.zero ≡ Fin.zero
η₂-zero (keep (keep empty)) = refl
η₂-zero (keep (skip ()))
η₂-zero (skip (keep ()))
η₂-zero (skip (skip ()))

η₂-one : ∀ (η : 2 ↪ᵗ 2)
  → toRenameᵗ η (Fin.suc Fin.zero) ≡ Fin.suc Fin.zero
η₂-one (keep (keep empty)) = refl
η₂-one (keep (skip ()))
η₂-one (skip (keep ()))
η₂-one (skip (skip ()))

no-source-star-branch-output :
  ¬ (Σ[ Wᵒ ∈ World 2 2 2 ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
      ( CTI2.ImpEnvMono W₀ Wᵒ
      × CTI2.SameCtx {W = W₀} [] γᵒ
      × sourceStoreʷ Wᵒ ∋ X₀ ⦂ ★
      × targetStoreʷ Wᵒ ∋ Y₁ ⦂ ★
      × Σ[ qᵒ ∈ ＇ X₀ ⊑ᵂ⟨ Wᵒ ⟩ ＇ Y₁ ]
          (Wᵒ ∣ γᵒ ⊢²
            (V ⟨ X₁! ⟩) ↓ seal X₀ ★ ⊑ U ∶ qᵒ) ))
no-source-star-branch-output
    (Wᵒ , γᵒ , mono , sc , X∈ , Y∈ , qᵒ , out) =
  zero≢one same-center
  where
  zero≢one : Fin.zero ≢ Fin.suc Fin.zero
  zero≢one ()

  same-center :
    Fin.zero ≡ Fin.suc Fin.zero
  same-center =
    trans
      (sym (η₂-zero (ηᴸʷ Wᵒ)))
      (trans
        (ECR.variable-obligation-aligns {W = Wᵒ} {X = X₀}
          {Y = Y₁} qᵒ)
        (η₂-one (ηᴿʷ Wᵒ)))
