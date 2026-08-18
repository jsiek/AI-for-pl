module TwoPostulatesHuntScratch where

-- Scratch-only counterexample hunt for the two RightInjInversion2 helper
-- statements.  The file deliberately lives at repository root and does not
-- modify the GTSFImp development.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore using
  (TyStore; store-empty; store-bind; _∋_⦂_; Z∋; S-lift∋;
   S-bind∋)
open import Consistency using
  (Env∼; X∼★; _⊢_∼_; _↪ᵗ_; empty; keep; skip; toRenameᵗ;
   id; _!)
open import Conversion using (seal)
open import CastTerms
import CastTerms as CTerms
open import Imprecision
open import Primitives using (κℕ)
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.SealPeelToolkit as SPT
import proof.DGG.Inversion.SpineValueDef as SVD
open import proof.ImprecisionConsistency using (toRenameᵗ-injective)
open CTI2 using
  (World; world; CtxImp; RebaseAt; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_;
   sourceStoreʷ; targetStoreʷ; ηᴸʷ; ηᴿʷ; store-rep-imp)

------------------------------------------------------------------------
-- Generic empty-shape checks used by several adversarial configurations
------------------------------------------------------------------------

store-variable-distinct : ∀ {Δ} {Σ : TyStore Δ}
    {Z Z₂ : TyVar Δ}
  → Σ ∋ Z ⦂ (＇ Z₂)
  → Z₂ ≢ Z
store-variable-distinct (Z∋ {A = ＇ X} refl) ()
store-variable-distinct (Z∋ {A = ‵ ι} ())
store-variable-distinct (Z∋ {A = ★} ())
store-variable-distinct (Z∋ {A = A ⇒ B} ())
store-variable-distinct (Z∋ {A = `∀ A} ())
store-variable-distinct (S-lift∋ {A = ＇ X} X∈ refl) refl =
  store-variable-distinct X∈ refl
store-variable-distinct (S-lift∋ {A = ‵ ι} X∈ ())
store-variable-distinct (S-lift∋ {A = ★} X∈ ())
store-variable-distinct (S-lift∋ {A = A ⇒ B} X∈ ())
store-variable-distinct (S-lift∋ {A = `∀ A} X∈ ())
store-variable-distinct (S-bind∋ {A = ＇ X} X∈ refl) refl =
  store-variable-distinct X∈ refl
store-variable-distinct (S-bind∋ {A = ‵ ι} X∈ ())
store-variable-distinct (S-bind∋ {A = ★} X∈ ())
store-variable-distinct (S-bind∋ {A = A ⇒ B} X∈ ())
store-variable-distinct (S-bind∋ {A = `∀ A} X∈ ())

source-pivot-forced : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {X X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → CTI2.RebaseAt W′ W X Y
  → (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)
  → (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)
  → X₂ ≡ X
source-pivot-forced {W = W} {W′ = W′}
    {X = X} {X₂ = X₂} {Y = Y} rb q p
    with Fin._≟_ X₂ X
source-pivot-forced rb q p | yes refl = refl
source-pivot-forced {W = W} {W′ = W′}
    {X = X} {X₂ = X₂} {Y = Y} rb q p | no X₂≢X =
  ⊥-elim (X₂≢X
    (toRenameᵗ-injective (ηᴸʷ W) same-center))
  where
  same-center :
    toRenameᵗ (ηᴸʷ W) X₂ ≡ toRenameᵗ (ηᴸʷ W) X
  same-center =
    trans (CTI2.RebaseAt.ηᴸ-off-pivot rb X₂≢X)
      (trans (SVD.variable-obligation-aligns
        {W = W′} {X = X₂} {Y = Y} p)
        (trans (sym (CTI2.RebaseAt.ηᴿ-frozen rb Y))
          (sym (SVD.variable-obligation-aligns
            {W = W} {X = X} {Y = Y} q))))

source-var-chain-blocked : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {X X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → sourceStoreʷ W ∋ X ⦂ (＇ X₂)
  → CTI2.RebaseAt W′ W X Y
  → (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)
  → (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)
  → ⊥
source-var-chain-blocked X∈ rb q p =
  store-variable-distinct X∈ (source-pivot-forced rb q p)

star-source-nonstar-⊥ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {S : Ty Δᴿ}
  → ★ ⊑ᵂ⟨ W ⟩ S
  → NonStar S
  → ⊥
star-source-nonstar-⊥ {S = ＇ Y} () nonstar-X
star-source-nonstar-⊥ {S = ‵ ι} () nonstar-ι
star-source-nonstar-⊥ {S = A ⇒ B} () nonstar-⇒
star-source-nonstar-⊥ {S = `∀ A} () nonstar-∀

source-star-nonstar-store-blocked : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ} {S : Ty Δᴿ}
  → sourceStoreʷ W ∋ X ⦂ ★
  → targetStoreʷ W ∋ Y ⦂ S
  → NonVar S
  → NonStar S
  → CTI2.RebaseAt W′ W X Y
  → ⊥
source-star-nonstar-store-blocked {W = W} {Y = Y} {S = S}
    X∈ Y∈ Snv Sns rb =
  star-source-nonstar-⊥ {W = W} {S = S}
    (subst≡ (λ T → ★ ⊑ᵂ⟨ W ⟩ T)
      (SPT.resolveVar-nonvar Y∈ Snv)
      (subst≡
        (λ T → T ⊑ᵂ⟨ W ⟩ CTI2.resolveVar (targetStoreʷ W) Y)
        (SPT.resolveVar-nonvar X∈ nonvar-star)
        (CTI2.StoreRepImp.represented
          (CTI2.RebaseAt.storeRepresentations rb))))
    Sns

nonvar-right-var-obligation-empty : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {A : Ty Δᴸ} {Y : TyVar Δᴿ}
  → NonVar A
  → A ⊑ᵂ⟨ W ⟩ (＇ Y)
  → ⊥
nonvar-right-var-obligation-empty {A = ＇ X} () p
nonvar-right-var-obligation-empty {W = W} {A = ‵ ι} {Y = Y}
    nonvar-base p
    with SPT.right-var-obligation-view {W = W} {R = ‵ ι} {Y = Y} p
nonvar-right-var-obligation-empty {A = ‵ ι} nonvar-base p
    | X , () , aligned
nonvar-right-var-obligation-empty {W = W} {A = ★} {Y = Y}
    nonvar-star p
    with SPT.right-var-obligation-view {W = W} {R = ★} {Y = Y} p
nonvar-right-var-obligation-empty {A = ★} nonvar-star p
    | X , () , aligned
nonvar-right-var-obligation-empty {W = W} {A = A ⇒ B} {Y = Y}
    nonvar-fun p
    with SPT.right-var-obligation-view
      {W = W} {R = A ⇒ B} {Y = Y} p
nonvar-right-var-obligation-empty {A = A ⇒ B} nonvar-fun p
    | X , () , aligned
nonvar-right-var-obligation-empty {W = W} {A = `∀ A} {Y = Y}
    nonvar-all p
    with SPT.right-var-obligation-view {W = W} {R = `∀ A} {Y = Y} p
nonvar-right-var-obligation-empty {A = `∀ A} nonvar-all p
    | X , () , aligned

lifted-nonvar-right-var-empty : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {A : Ty (suc Δᴸ)}
    {Y : TyVar Δᴿ}
  → NonVar A
  → A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ (＇ Y)
  → ⊥
lifted-nonvar-right-var-empty {W = W} nv p =
  nonvar-right-var-obligation-empty
    {W = CTI2.liftWorldLeft X⊑★ W} nv p

------------------------------------------------------------------------
-- Placement adversary: source re-parking would drag another source var
------------------------------------------------------------------------

module SourceCrossingAttempt where
  X₀ : TyVar 2
  X₀ = Fin.zero

  X₁ : TyVar 2
  X₁ = Fin.suc Fin.zero

  Y : TyVar 1
  Y = Fin.zero

  source-store : TyStore 2
  source-store = store-bind (store-bind store-empty ★) ★

  target-store : TyStore 1
  target-store = store-bind store-empty ★

  μ : ImpEnv 3
  μ Fin.zero = X⊑★
  μ (Fin.suc Fin.zero) = X⊑★
  μ (Fin.suc (Fin.suc Fin.zero)) = X⊑★

  ηᴸ-01 : 2 ↪ᵗ 3
  ηᴸ-01 = keep (keep (skip empty))

  ηᴸ-12 : 2 ↪ᵗ 3
  ηᴸ-12 = skip (keep (keep empty))

  ηᴿ-0 : 1 ↪ᵗ 3
  ηᴿ-0 = keep (skip (skip empty))

  -- Placement table:
  --
  --             X₀  X₁  Y
  --   W          0   1  0
  --   W′         1   2  0
  --
  -- A source move that would park X₀ to the right must also move X₁.
  -- Frozen off-pivot source variables reject that before any input term
  -- can be formed.

  W : World 2 1 3
  W = world ηᴸ-01 ηᴿ-0 μ source-store target-store

  W′ : World 2 1 3
  W′ = world ηᴸ-12 ηᴿ-0 μ source-store target-store

  X₁≢X₀ : X₁ ≢ X₀
  X₁≢X₀ ()

  repark-crossing-empty : RebaseAt W′ W X₀ Y → ⊥
  repark-crossing-empty rb
      with CTI2.RebaseAt.ηᴸ-off-pivot rb X₁≢X₀
  repark-crossing-empty rb | ()

------------------------------------------------------------------------
-- Source-variable chain adversary with concrete p/q obligations
------------------------------------------------------------------------

module SourceVarChainAttempt where
  X₀ : TyVar 2
  X₀ = Fin.zero

  X₁ : TyVar 2
  X₁ = Fin.suc Fin.zero

  Y : TyVar 1
  Y = Fin.zero

  source-store : TyStore 2
  source-store =
    store-bind (store-bind store-empty ★) (＇ Fin.zero)

  target-store : TyStore 1
  target-store = store-bind store-empty ★

  μ : ImpEnv 3
  μ Fin.zero = X⊑★
  μ (Fin.suc Fin.zero) = X⊑★
  μ (Fin.suc (Fin.suc Fin.zero)) = X⊑★

  ηᴸ-W : 2 ↪ᵗ 3
  ηᴸ-W = skip (keep (keep empty))

  ηᴸ-W′ : 2 ↪ᵗ 3
  ηᴸ-W′ = keep (keep (skip empty))

  ηᴿ-1 : 1 ↪ᵗ 3
  ηᴿ-1 = skip (keep (skip empty))

  -- Placement table:
  --
  --             X₀  X₁  Y
  --   W          1   2  1
  --   W′         0   1  1
  --
  -- `q` and `p` are individually derivable, but together with a frozen
  -- `RebaseAt W′ W X₀ Y` they force X₁ = X₀.

  W : World 2 1 3
  W = world ηᴸ-W ηᴿ-1 μ source-store target-store

  W′ : World 2 1 3
  W′ = world ηᴸ-W′ ηᴿ-1 μ source-store target-store

  X₀∈ : source-store ∋ X₀ ⦂ (＇ X₁)
  X₀∈ = Z∋ refl

  q : (＇ X₀) ⊑ᵂ⟨ W ⟩ (＇ Y)
  q = X⊑X

  p : (＇ X₁) ⊑ᵂ⟨ W′ ⟩ (＇ Y)
  p = X⊑X

  input-obligations-empty : RebaseAt W′ W X₀ Y → ⊥
  input-obligations-empty rb =
    source-var-chain-blocked X₀∈ rb q p

------------------------------------------------------------------------
-- Concrete non-star target-store adversaries for S
------------------------------------------------------------------------

module NonStarSAttempts where
  X : TyVar 1
  X = Fin.zero

  Y : TyVar 1
  Y = Fin.zero

  source-store : TyStore 1
  source-store = store-bind store-empty ★

  target-store-ι : TyStore 1
  target-store-ι = store-bind store-empty (‵ `ℕ)

  target-store-⇒ : TyStore 1
  target-store-⇒ = store-bind store-empty (★ ⇒ ★)

  target-store-∀ : TyStore 1
  target-store-∀ = store-bind store-empty (`∀ ★)

  μ : ImpEnv 1
  μ Fin.zero = X⊑★

  η : 1 ↪ᵗ 1
  η = keep empty

  Wι : World 1 1 1
  Wι = world η η μ source-store target-store-ι

  W⇒ : World 1 1 1
  W⇒ = world η η μ source-store target-store-⇒

  W∀ : World 1 1 1
  W∀ = world η η μ source-store target-store-∀

  X∈ : source-store ∋ X ⦂ ★
  X∈ = Z∋ refl

  Y∈ι : target-store-ι ∋ Y ⦂ (‵ `ℕ)
  Y∈ι = Z∋ refl

  Y∈⇒ : target-store-⇒ ∋ Y ⦂ (★ ⇒ ★)
  Y∈⇒ = Z∋ refl

  Y∈∀ : target-store-∀ ∋ Y ⦂ (`∀ ★)
  Y∈∀ = Z∋ refl

  S-ι-input-empty : RebaseAt Wι Wι X Y → ⊥
  S-ι-input-empty =
    source-star-nonstar-store-blocked X∈ Y∈ι nonvar-base nonstar-ι

  S-⇒-input-empty : RebaseAt W⇒ W⇒ X Y → ⊥
  S-⇒-input-empty =
    source-star-nonstar-store-blocked X∈ Y∈⇒ nonvar-fun nonstar-⇒

  S-∀-input-empty : RebaseAt W∀ W∀ X Y → ⊥
  S-∀-input-empty =
    source-star-nonstar-store-blocked X∈ Y∈∀ nonvar-all nonstar-∀

------------------------------------------------------------------------
-- Concrete premise-head checks, including the binder-lifted shape
------------------------------------------------------------------------

module NonVarHeadAttempt where
  X : TyVar 1
  X = Fin.zero

  Y : TyVar 1
  Y = Fin.zero

  source-store : TyStore 1
  source-store = store-bind store-empty ★

  target-store : TyStore 1
  target-store = store-bind store-empty ★

  μ : ImpEnv 1
  μ Fin.zero = X⊑★

  η : 1 ↪ᵗ 1
  η = keep empty

  W : World 1 1 1
  W = world η η μ source-store target-store

  base-head-empty : (‵ `ℕ) ⊑ᵂ⟨ W ⟩ (＇ Y) → ⊥
  base-head-empty =
    nonvar-right-var-obligation-empty
      {W = W} {A = ‵ `ℕ} {Y = Y} nonvar-base

  fun-head-empty : (★ ⇒ ★) ⊑ᵂ⟨ W ⟩ (＇ Y) → ⊥
  fun-head-empty =
    nonvar-right-var-obligation-empty
      {W = W} {A = ★ ⇒ ★} {Y = Y} nonvar-fun

  all-head-empty : (`∀ ★) ⊑ᵂ⟨ W ⟩ (＇ Y) → ⊥
  all-head-empty =
    nonvar-right-var-obligation-empty
      {W = W} {A = `∀ ★} {Y = Y} nonvar-all

  lifted-fun-head-empty :
    (★ ⇒ ★) ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ (＇ Y)
    → ⊥
  lifted-fun-head-empty =
    lifted-nonvar-right-var-empty
      {W = W} {A = ★ ⇒ ★} {Y = Y} nonvar-fun

------------------------------------------------------------------------
-- Live stress instance: depth-2 target chain for both target statements
------------------------------------------------------------------------

module Depth2TargetChain where
  X : TyVar 1
  X = Fin.zero

  Y₀ : TyVar 3
  Y₀ = Fin.zero

  Y₁ : TyVar 3
  Y₁ = Fin.suc Fin.zero

  Y₂ : TyVar 3
  Y₂ = Fin.suc (Fin.suc Fin.zero)

  source-store : TyStore 1
  source-store = store-bind store-empty ★

  target-store : TyStore 3
  target-store =
    store-bind
      (store-bind (store-bind store-empty ★) (＇ Fin.zero))
      (＇ Fin.zero)

  μ : ImpEnv 3
  μ Fin.zero = X⊑★
  μ (Fin.suc Fin.zero) = X⊑★
  μ (Fin.suc (Fin.suc Fin.zero)) = X⊑★

  ηᴸ-0 : 1 ↪ᵗ 3
  ηᴸ-0 = keep (skip (skip empty))

  ηᴸ-1 : 1 ↪ᵗ 3
  ηᴸ-1 = skip (keep (skip empty))

  ηᴸ-2 : 1 ↪ᵗ 3
  ηᴸ-2 = skip (skip (keep empty))

  ηᴿ-id : 3 ↪ᵗ 3
  ηᴿ-id = keep (keep (keep empty))

  -- Placement table:
  --
  --             X   Y₀  Y₁  Y₂
  --   W₀        0    0   1   2
  --   W₁        1    0   1   2
  --   W₂        2    0   1   2

  W₀ : World 1 3 3
  W₀ = world ηᴸ-0 ηᴿ-id μ source-store target-store

  W₁ : World 1 3 3
  W₁ = world ηᴸ-1 ηᴿ-id μ source-store target-store

  W₂ : World 1 3 3
  W₂ = world ηᴸ-2 ηᴿ-id μ source-store target-store

  mono-refl : ∀ {W : World 1 3 3}
    → CTI2.ImpEnvMono W W
  mono-refl Z eq = eq

  mono₀₁ : CTI2.ImpEnvMono W₀ W₁
  mono₀₁ Z eq = eq

  mono₁₂ : CTI2.ImpEnvMono W₁ W₂
  mono₁₂ Z eq = eq

  X∈ : source-store ∋ X ⦂ ★
  X∈ = Z∋ refl

  Y₀∈ : target-store ∋ Y₀ ⦂ (＇ Y₁)
  Y₀∈ = Z∋ refl

  Y₁∈ : target-store ∋ Y₁ ⦂ (＇ Y₂)
  Y₁∈ = S-bind∋ (Z∋ refl) refl

  Y₂∈ : target-store ∋ Y₂ ⦂ ★
  Y₂∈ = S-bind∋ (S-bind∋ (Z∋ refl) refl) refl

  source-env : Env∼ 1
  source-env Fin.zero = X∼★

  target-env : Env∼ 3
  target-env Fin.zero = X∼★
  target-env (Fin.suc Fin.zero) = X∼★
  target-env (Fin.suc (Fin.suc Fin.zero)) = X∼★

  X! : source-env ⊢ (＇ X) ∼ ★
  X! = id (＇ X) !

  Y₀! : target-env ⊢ (＇ Y₀) ∼ ★
  Y₀! = id (＇ Y₀) !

  ℕ!ᴸ : source-env ⊢ (‵ `ℕ) ∼ ★
  ℕ!ᴸ = id (‵ `ℕ) !

  ℕ!ᴿ : target-env ⊢ (‵ `ℕ) ∼ ★
  ℕ!ᴿ = id (‵ `ℕ) !

  V₀ : Term 1
  V₀ = ($ (κℕ 0)) ⟨ ℕ!ᴸ ⟩

  V : Term 1
  V = V₀ ↓ seal X ★

  source-payload : Term 1
  source-payload = V ⟨ X! ⟩

  source-output : Term 1
  source-output = source-payload ↓ seal X ★

  U₀ : Term 3
  U₀ = ($ (κℕ 0)) ⟨ ℕ!ᴿ ⟩

  U₂ : Term 3
  U₂ = U₀ ↓ seal Y₂ ★

  U₁ : Term 3
  U₁ = U₂ ↓ seal Y₁ (＇ Y₂)

  target-chain : Term 3
  target-chain = U₁ ↓ seal Y₀ (＇ Y₁)

  target-tagged : Term 3
  target-tagged = target-chain ⟨ Y₀! ⟩

  U₀-value : Value U₀
  U₀-value = CTerms.$ (κℕ 0) CTerms.《 CTerms.inj 》

  U₂-value : Value U₂
  U₂-value = U₀-value CTerms.↓ CTerms.seal

  U₁-value : Value U₁
  U₁-value = U₂-value CTerms.↓ CTerms.seal

  V-spine : SVD.SpineValue V
  V-spine =
    SVD.sv-seal (SVD.sv-cast (SVD.sv-$ (κℕ 0)) CTerms.inj)

  source-payload-spine : SVD.SpineValue source-payload
  source-payload-spine = SVD.sv-cast V-spine CTerms.inj

  inert-X! : Inert X!
  inert-X! = CTerms.inj

  q₀ : (＇ X) ⊑ᵂ⟨ W₀ ⟩ (＇ Y₀)
  q₀ = X⊑X

  q₁ : (＇ X) ⊑ᵂ⟨ W₁ ⟩ (＇ Y₁)
  q₁ = X⊑X

  q₂ : (＇ X) ⊑ᵂ⟨ W₂ ⟩ (＇ Y₂)
  q₂ = X⊑X

  x-star₂ : (＇ X) ⊑ᵂ⟨ W₂ ⟩ ★
  x-star₂ = X⊑★ refl

  X-Y₀-rep : CTI2.StoreRepImp W₀ X Y₀
  X-Y₀-rep = store-rep-imp ★⊑★

  X-Y₁-rep : CTI2.StoreRepImp W₁ X Y₁
  X-Y₁-rep = store-rep-imp ★⊑★

  X-Y₂-rep : CTI2.StoreRepImp W₂ X Y₂
  X-Y₂-rep = store-rep-imp ★⊑★

  rb-X-Y₀ : RebaseAt W₀ W₀ X Y₀
  rb-X-Y₀ = CTI2.sameWorldRebaseAt refl X-Y₀-rep

  rb-Y₀ : RebaseAt W₁ W₀ X Y₀
  rb-Y₀ =
    CTI2.rebase-at (CTI2.same-runtime refl refl)
      (λ { {Fin.zero} X≢ → ⊥-elim (X≢ refl) })
      (λ _ → refl) refl X-Y₀-rep

  rb-Y₁ : RebaseAt W₂ W₁ X Y₁
  rb-Y₁ =
    CTI2.rebase-at (CTI2.same-runtime refl refl)
      (λ { {Fin.zero} X≢ → ⊥-elim (X≢ refl) })
      (λ _ → refl) refl X-Y₁-rep

  rb-X-Y₂ : RebaseAt W₂ W₂ X Y₂
  rb-X-Y₂ = CTI2.sameWorldRebaseAt refl X-Y₂-rep

  base² : W₂ ∣ [] ⊢² V₀ ⊑ U₀ ∶ ★⊑★
  base² =
    CTI2.cast⊑cast² ℕ!ᴸ ℕ!ᴿ
      (CTI2.κ⊑κ² (κℕ 0) ι⊑ι) ★⊑★

  V⊑U₂ : W₂ ∣ [] ⊢² V ⊑ U₂ ∶ q₂
  V⊑U₂ =
    CTI2.conceal⊑conceal² (mono-refl {W = W₂}) rb-X-Y₂
      CTI2.same-[] (Conv.⊢↓-sealˣ X∈)
      (Conv.⊢↓-sealˣ Y₂∈) base² q₂

  V⊑U₁ : W₁ ∣ [] ⊢² V ⊑ U₁ ∶ q₁
  V⊑U₁ =
    CTI2.⊑conceal² mono₁₂ (CTI2.rebase-varᴿ rb-Y₁)
      CTI2.same-[] (Conv.⊢↓-sealˣ Y₁∈) V⊑U₂ q₁

  chain-input : W₀ ∣ [] ⊢² V ⊑ target-chain ∶ q₀
  chain-input =
    CTI2.⊑conceal² mono₀₁ (CTI2.rebase-varᴿ rb-Y₀)
      CTI2.same-[] (Conv.⊢↓-sealˣ Y₀∈) V⊑U₁ q₀

  inner-source-seal : W₂ ∣ [] ⊢² V ⊑ U₀ ∶ x-star₂
  inner-source-seal =
    CTI2.conceal⊑² (mono-refl {W = W₂})
      (CTI2.rebase-varᴸ rb-X-Y₂)
      CTI2.same-[] (Conv.⊢↓-sealˣ X∈) base² x-star₂

  payload² : W₂ ∣ [] ⊢² source-payload ⊑ U₀ ∶ ★⊑★
  payload² = CTI2.cast⊑² X! inner-source-seal ★⊑★

  terminus-pair : W₂ ∣ [] ⊢² source-output ⊑ U₂ ∶ q₂
  terminus-pair =
    CTI2.conceal⊑conceal² (mono-refl {W = W₂}) rb-X-Y₂
      CTI2.same-[] (Conv.⊢↓-sealˣ X∈)
      (Conv.⊢↓-sealˣ Y₂∈) payload² q₂

  output-Y₁ : W₁ ∣ [] ⊢² source-output ⊑ U₁ ∶ q₁
  output-Y₁ =
    CTI2.⊑conceal² mono₁₂ (CTI2.rebase-varᴿ rb-Y₁)
      CTI2.same-[] (Conv.⊢↓-sealˣ Y₁∈) terminus-pair q₁

  chain-output : W₀ ∣ [] ⊢² source-output ⊑ target-chain ∶ q₀
  chain-output =
    CTI2.⊑conceal² mono₀₁ (CTI2.rebase-varᴿ rb-Y₀)
      CTI2.same-[] (Conv.⊢↓-sealˣ Y₀∈) output-Y₁ q₀

  source-star-chain-input-package :
    W₀ ∣ [] ⊢² V ⊑ U₁ ↓ seal Y₀ (＇ Y₁) ∶ q₀
  source-star-chain-input-package = chain-input

  source-star-chain-output-package :
    W₀ ∣ [] ⊢² (V ⟨ X! ⟩) ↓ seal X ★
      ⊑ U₁ ↓ seal Y₀ (＇ Y₁) ∶ q₀
  source-star-chain-output-package = chain-output

  tag-walk-input-package :
    W₀ ∣ [] ⊢² source-payload ⊑ target-tagged ∶ ★⊑★
  tag-walk-input-package =
    CTI2.cast⊑cast² X! Y₀! chain-input ★⊑★

  tag-walk-output-package :
    W₀ ∣ [] ⊢² source-payload ↓ seal X ★
      ⊑ U₁ ↓ seal Y₀ (＇ Y₁) ∶ q₀
  tag-walk-output-package = chain-output
