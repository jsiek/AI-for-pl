module proof.DGG.TerminusRebuildProbe where

-- File Charter:
--   * Records concrete terminus-rebuild instances for the M3 head cases.
--   * Instance A is the S = ★ base template: rebuild a `Λ⊑²` head
--     against the unsealed target value, then pair the source and target
--     seals with `conceal⊑conceal²`.  The direct source-seal/bare
--     `dyn-id` input is recorded negatively because `dyn-id` is a
--     top-level function-to-★ tag and the source seal representation is
--     not literally ★.
--   * Instance B preserves the old S = ＇Y₂ chain snapshot negatively.
--     Its endpoint stores are independently operationally possible, but its
--     direct-representation and occupied dynamic-star alignments violate the
--     live World invariants and are not reachable from a related empty-world
--     execution.
--   * This is the positive counterpart to the refuted tag-peel-first
--     family documented in `RightInjInversion2Def`: the head is rebuilt
--     at the target-chain terminus instead of against a right variable.

import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)

open import Types
open import TyStore using
  (TyStore; store-empty; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import TermCtx using (Z)
open import Consistency using
  (Env∼; X∼★; _⊢_∼_; _↪ᵗ_; empty; keep; skip; id; _↦_; _!)
open import Conversion using (seal; _⊢↓_; ⊢↓-seal)
open import CastTerms
open import Imprecision
import CastTerms as CTerms
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open CTX using
  (World;
   emptyʷ;
   bind-both-starʷ;
   _⊑ᵂ⟨_⟩_;
   RebaseAt;
   rebase-at;
   same-runtime;
   store-rep-imp)
open CTI2 using (_∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Shared tiny values
------------------------------------------------------------------------

dyn-env : ∀ {Δ} → Env∼ Δ
dyn-env _ = X∼★

fun! : ∀ {Δ} → dyn-env {Δ} ⊢ ★ ⇒ ★ ∼ ★
fun! = (id ★ ↦ id ★) !

dyn-id : ∀ {Δ} → Term Δ
dyn-id = (ƛ (` 0)) ⟨ fun! ⟩

dyn-id-⊢ : ∀ {Δ Σ Γ}
  → ⟨ Δ , Σ , Γ ⟩ ⊢ ƛ (` 0) ⦂ ★ ⇒ ★
dyn-id-⊢ = ⊢ƛ (⊢` Z)

dyn-id!-⊢ : ∀ {Δ Σ Γ}
  → ⟨ Δ , Σ , Γ ⟩ ⊢ dyn-id ⦂ ★
dyn-id!-⊢ = ⊢⟨⟩ dyn-id-⊢ fun!

dyn-id-value : ∀ {Δ} → Value (dyn-id {Δ})
dyn-id-value = (CTerms.ƛ (` 0)) CTerms.《 CTerms.inj 》

mono-refl : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → CTX.ImpEnvMono W W
mono-refl = CTX.impEnvMono-refl

------------------------------------------------------------------------
-- Instance A: the S = ★ terminus
------------------------------------------------------------------------

module InstanceA where
  X : TyVar 1
  X = Fin.zero

  Y : TyVar 1
  Y = Fin.zero

  ∀X⇒X₀ : Ty 0
  ∀X⇒X₀ = `∀ (＇ Fin.zero ⇒ ＇ Fin.zero)

  ∀X⇒X : Ty 1
  ∀X⇒X = `∀ (＇ Fin.zero ⇒ ＇ Fin.zero)

  body : Ty 2
  body = ＇ Fin.zero ⇒ ＇ Fin.zero

  source-store : TyStore 1
  source-store = store-bind store-empty ∀X⇒X₀

  target-store : TyStore 1
  target-store = store-bind store-empty ★

  env : ImpEnv 1
  env Fin.zero = X⊑★

  η-id : 1 ↪ᵗ 1
  η-id = keep empty

  -- Placement table:
  --
  --             X   Y
  --   W         0   0

  source-∀⊑★-empty : ∀X⇒X₀ ⊑ᵂ⟨ emptyʷ ⟩ ★
  source-∀⊑★-empty =
    ∀⊑ nonvar-fun (∈-fun-left var-∈)
      (⇒⊑★ (X⊑★ refl) (X⊑★ refl))

  W : World 1 1 1
  W =
    bind-both-starʷ emptyʷ ∀X⇒X₀ ★ source-∀⊑★-empty (λ ())

  X∈ : source-store ∋ X ⦂ ∀X⇒X
  X∈ = Z∋ refl

  Y∈ : target-store ∋ Y ⦂ ★
  Y∈ = Z∋ refl

  target-env : Env∼ 1
  target-env Fin.zero = X∼★

  Y! : target-env ⊢ ＇ Y ∼ ★
  Y! = id (＇ Y) !

  source-∀⊑★ : ∀X⇒X ⊑ᵂ⟨ W ⟩ ★
  source-∀⊑★ =
    ∀⊑ nonvar-fun (∈-fun-left var-∈)
      (⇒⊑★ (X⊑★ refl) (X⊑★ refl))

  X⊑Y : ＇ X ⊑ᵂ⟨ W ⟩ ＇ Y
  X⊑Y = X⊑X

  X⊑★-W : ＇ X ⊑ᵂ⟨ W ⟩ ★
  X⊑★-W = X⊑★ refl

  X-Y-rep : CTX.StoreRepImp W X Y
  X-Y-rep = store-rep-imp source-∀⊑★

  rb-X-Y : RebaseAt W W X Y
  rb-X-Y = CTX.sameWorldRebaseAt refl X-Y-rep

  target-seal-⊢ : target-store Conv.⊢↓[ just Y ] seal Y ★
  target-seal-⊢ = Conv.⊢↓-sealˣ Y∈

  source-seal-⊢ : source-store Conv.⊢↓[ just X ] seal X ∀X⇒X
  source-seal-⊢ = Conv.⊢↓-sealˣ X∈

  target-seal-⊢ᶜ : target-store ⊢↓ seal Y ★
  target-seal-⊢ᶜ = ⊢↓-seal Y∈

  U : Term 1
  U = dyn-id

  target-sealed : Term 1
  target-sealed = U ↓ seal Y ★

  target-tagged : Term 1
  target-tagged = target-sealed ⟨ Y! ⟩

  source : Term 1
  source = (Λ (ƛ (` 0))) ↓ seal X ∀X⇒X

  U-⊢ : ⟨ 1 , target-store , [] ⟩ ⊢ U ⦂ ★
  U-⊢ = dyn-id!-⊢

  target-sealed-⊢ : ⟨ 1 , target-store , [] ⟩ ⊢ target-sealed ⦂ ＇ Y
  target-sealed-⊢ = ⊢conceal target-seal-⊢ᶜ U-⊢

  target-tagged-⊢ : ⟨ 1 , target-store , [] ⟩ ⊢ target-tagged ⦂ ★
  target-tagged-⊢ = ⊢⟨⟩ target-sealed-⊢ Y!

  body-X⊑★ : ＇ Fin.zero ⊑ᵂ⟨ CTX.liftWorldLeft W ⟩ ★
  body-X⊑★ = X⊑★ refl

  body⊑★ : body ⊑ᵂ⟨ CTX.liftWorldLeft W ⟩ ★
  body⊑★ = ⇒⊑★ body-X⊑★ body-X⊑★

  body⊑★⇒★ :
    body ⊑ᵂ⟨ CTX.liftWorldLeft W ⟩ ★ ⇒ ★
  body⊑★⇒★ = ⇒⊑⇒ body-X⊑★ body-X⊑★

  body-fun² :
    CTX.liftWorldLeft W ∣ [] ⊢²
      ƛ (` 0) ⊑ ƛ (` 0) ∶ body⊑★⇒★
  body-fun² =
    CTI2.ƛ⊑ƛ²
      {A = ＇ Fin.zero} {A′ = ★}
      {pA = body-X⊑★} {pB = body-X⊑★}
      (CTI2.x⊑x² {p = body-X⊑★} CTX.Zʷ)

  body-U² :
    CTX.liftWorldLeft W ∣ [] ⊢²
      ƛ (` 0) ⊑ U ∶ body⊑★
  body-U² = CTI2.⊑cast² fun! body-fun² body⊑★

  head-U² : W ∣ [] ⊢² Λ (ƛ (` 0)) ⊑ U ∶ source-∀⊑★
  head-U² =
    CTI2.Λ⊑² nonvar-fun (∈-fun-left var-∈)
      CTX.liftᴸ-[] (ƛ (` 0)) U-⊢ body-U² source-∀⊑★


  output : W ∣ [] ⊢² source ⊑ target-sealed ∶ X⊑Y
  output =
    CTI2.conceal⊑conceal²
      (mono-refl {W = W}) rb-X-Y CTX.same-[]
      source-seal-⊢ target-seal-⊢ head-U² X⊑Y

  -- The observable tagged premise is available, but the rebuild above
  -- deliberately avoids using this tag-peel-first derivation.
  tagged-input : W ∣ [] ⊢² source ⊑ target-tagged ∶ X⊑★-W
  tagged-input = CTI2.⊑cast² Y! output X⊑★-W

------------------------------------------------------------------------
-- Instance B: the S = ＇Y₂ chain
------------------------------------------------------------------------

module InstanceB where
  X : TyVar 1
  X = Fin.zero

  Y : TyVar 2
  Y = Fin.zero

  Y₂ : TyVar 2
  Y₂ = Fin.suc Fin.zero

  source-store : TyStore 1
  source-store = store-bind store-empty ★

  target-store : TyStore 2
  target-store = store-bind (store-bind store-empty ★) (＇ Fin.zero)

  env : ImpEnv 2
  env Fin.zero = X⊑★
  env (Fin.suc Fin.zero) = X⊑★

  η-X-Y : 1 ↪ᵗ 2
  η-X-Y = keep (skip empty)

  η-X-Y₂ : 1 ↪ᵗ 2
  η-X-Y₂ = skip (keep empty)

  η-target : 2 ↪ᵗ 2
  η-target = keep (keep empty)

  -- Placement table:
  --
  --             X   Y   Y₂
  --   W         0   0   1
  --   Wᵖ        1   0   1

  OriginalWInvariants : Set
  OriginalWInvariants =
    CTX.WorldInvariants
      η-X-Y η-target env source-store target-store

  OriginalWᵖInvariants : Set
  OriginalWᵖInvariants =
    CTX.WorldInvariants
      η-X-Y₂ η-target env source-store target-store

  W-direct-representation-obstruction : OriginalWInvariants → ⊥
  W-direct-representation-obstruction inv
      with CTX.representationsImprecise inv
        {Xᴸ = X} {Xᴿ = Y} refl
  W-direct-representation-obstruction inv | ()

  Wᵖ-dynamic-star-vacancy-obstruction : OriginalWᵖInvariants → ⊥
  Wᵖ-dynamic-star-vacancy-obstruction inv =
    CTX.dynamicStarSourcesUnoccupied inv X refl refl Y₂ refl

  no-original-W-invariants : ¬ OriginalWInvariants
  no-original-W-invariants = W-direct-representation-obstruction

  no-original-Wᵖ-invariants : ¬ OriginalWᵖInvariants
  no-original-Wᵖ-invariants = Wᵖ-dynamic-star-vacancy-obstruction

  -- Both endpoint stores are independently operationally possible, but the
  -- raw alignments above cannot arise from a related empty-world execution.
  -- The old D15 chain is therefore retained as an invariant refutation, not
  -- as a positive source-star package premise.
