module proof.RightSealFactorCounterexample where

-- File Charter:
--   * Counterexample for exact right-seal factorization in source-left
--     cast cases.
--   * Shows that the case needed by `cast+⊒` is false even with an exact
--     `q ⨾ⁿ seal ... ≈ r` premise: `id Nat ⨾ seal ≈ seal` and
--     `seal ≈ seal ⨾ id α`, but `id α` is not itself a right-seal composite.
--   * Uses only existing coercion/narrowing infrastructure and adds no
--     postulates.

open import Agda.Builtin.Equality using (refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (z<s)
open import Data.Product using (_,_; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Types
open import Coercions
open import Primitives
open import NarrowWiden
open import NarrowWidenComposition
open import proof.NarrowWidenProperties
  using (StoreDetWf; narrowing-var-to-older⊥)

NatTy : Ty
NatTy = ‵ `ℕ

alpha0 : TyVar
alpha0 = 0

Store0 : Store
Store0 = (alpha0 , NatTy) ∷ []

Sigma0 : StoreNrw
Sigma0 = (alpha0 ꞉ id NatTy) ∷ []

seal0 : Coercion
seal0 = seal NatTy alpha0

idAlpha0 : Coercion
idAlpha0 = id (＇ alpha0)

wfStore0 : StoreDetWf 1 Store0
wfStore0 =
  record
    { at = record
        { bound = λ { (here refl) → z<s }
        ; wfTy = λ { (here refl) → wfBase }
        }
    ; wfOlder = λ { (here refl) → wfBase }
    ; unique = λ { (here refl) (here refl) → refl }
    }

Sigma0⊒ : 1 ⊢ Sigma0 ꞉ Store0 ⊒ˢ Store0
Sigma0⊒ =
  ⊒ˢ-both wfBase wfBase
    (id-onlyᵈ , (cast-id wfBase refl , cross (id-‵ `ℕ)))
    ⊒ˢ-nil

endpoints0 : EndpointWf 1 Store0 NatTy (＇ alpha0)
endpoints0 = wfBaseˢ , wfVarˢ (here refl)

idNat⊒ : seal-or-idᵈ ∣ 1 ∣ Store0 ⊢ id NatTy ∶ NatTy ⊒ NatTy
idNat⊒ = cast-id wfBase refl , cross (id-‵ `ℕ)

idAlpha0⊒ :
  seal-or-idᵈ ∣ 1 ∣ Store0 ⊢ idAlpha0 ∶ ＇ alpha0 ⊒ ＇ alpha0
idAlpha0⊒ = cast-id (wfVar z<s) refl , cross (id-＇ alpha0)

seal0⊒ : seal-or-idᵈ ∣ 1 ∣ Store0 ⊢ seal0 ∶ NatTy ⊒ ＇ alpha0
seal0⊒ = cast-seal wfBase (here refl) refl , sealⁿ NatTy alpha0

right-seal-compose :
  1 ∣ Sigma0 ⊢ id NatTy ⨾ⁿ seal0 ≈ seal0 ∶ NatTy ⊒ ＇ alpha0
right-seal-compose =
  compose-leftⁿ wfStore0 idNat⊒ seal0⊒
    (endpointsⁿ refl refl refl refl Sigma0⊒ endpoints0 endpoints0
      (seal-or-idᵈ , proj₂ (_⨟ⁿ_ {wfΣ = wfStore0} idNat⊒ seal0⊒))
      (seal-or-idᵈ , seal0⊒))

left-seal-compose :
  1 ∣ Sigma0 ⊢ seal0 ≈ seal0 ⨾ⁿ idAlpha0 ∶ NatTy ⊒ ＇ alpha0
left-seal-compose =
  compose-rightⁿ wfStore0 seal0⊒ idAlpha0⊒
    (endpointsⁿ refl refl refl refl Sigma0⊒ endpoints0 endpoints0
      (seal-or-idᵈ , seal0⊒)
      (seal-or-idᵈ ,
        proj₂ (_⨟ⁿ_ {wfΣ = wfStore0} seal0⊒ idAlpha0⊒)))

idAlpha-not-right-seal-factor :
  ∀ {q} →
  1 ∣ Sigma0 ⊢ q ⨾ⁿ seal0 ≈ idAlpha0 ∶ src q ⊒ ＇ alpha0 →
  ⊥
idAlpha-not-right-seal-factor {q = q}
    (compose-leftⁿ {Σ = Σ} {μ = μ} wfΣ q⊒
      (cast-seal hNat α∈Σ seal-ok , sealⁿ .NatTy .alpha0)
      (endpointsⁿ src-u tgt-u src-idα tgt-idα
        σ⊒ wfΣ₁ wfΣ₂ u⊒ idα⊒)) =
  narrowing-var-to-older⊥
    {μ = μ}
    {Δ = 1}
    {Σ = Σ}
    {c = q}
    {α = alpha0}
    {B = NatTy}
    wfΣ
    wfBase
    (subst (λ A → μ ∣ 1 ∣ Σ ⊢ q ∶ A ⊒ NatTy) (sym src-idα) q⊒)

Case1Factorization : Set₁
Case1Factorization =
  ∀ {q r t p B α} →
  1 ∣ Sigma0 ⊢ q ⨾ⁿ seal B α ≈ r ∶ src q ⊒ ＇ α →
  1 ∣ Sigma0 ⊢ r ≈ t ⨾ⁿ p ∶ src q ⊒ ＇ α →
  ∃[ q′ ] 1 ∣ Sigma0 ⊢ q′ ⨾ⁿ seal B α ≈ p ∶ src q′ ⊒ ＇ α

case1-factorization-is-false :
  Case1Factorization →
  ⊥
case1-factorization-is-false factor
    with factor
      {q = id NatTy}
      {r = seal0}
      {t = seal0}
      {p = idAlpha0}
      {B = NatTy}
      {α = alpha0}
      right-seal-compose
      left-seal-compose
case1-factorization-is-false factor | q′ , q′⨟seal≈idα =
  idAlpha-not-right-seal-factor q′⨟seal≈idα
