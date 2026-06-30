module proof.RightSealBroadCounterexample where

-- File Charter:
--   * Small checked counterexample to the broad claim that a tag/id-mode
--     narrowing can never be endpoint-equivalent to a right-seal composite.
--   * The counterexample uses `id ★ ⨾ seal ★ α ≈ (＇ α) ？`: the composition
--     itself is typed in seal mode, while the right endpoint witness is the
--     tag/id-mode untag-like narrowing.
--   * Uses only existing coercion/narrowing infrastructure and adds no
--     postulates.

open import Agda.Builtin.Equality using (refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (z<s)
open import Data.Product using (_,_; proj₂)

open import Types
open import Coercions
open import NarrowWiden
open import NarrowWidenComposition
open import proof.NarrowWidenProperties
  using (StoreDetWf; narrowing-var-to-older⊥)

alpha0 : TyVar
alpha0 = 0

StoreStar : Store
StoreStar = (alpha0 , ★) ∷ []

SigmaStar : StoreNrw
SigmaStar = (alpha0 ꞉ id ★) ∷ []

sealStar0 : Coercion
sealStar0 = seal ★ alpha0

untagAlpha0 : Coercion
untagAlpha0 = (＇ alpha0) ？

wfStoreStar : StoreDetWf 1 StoreStar
wfStoreStar =
  record
    { at = record
        { bound = λ { (here refl) → z<s }
        ; wfTy = λ { (here refl) → wf★ }
        }
    ; wfOlder = λ { (here refl) → wf★ }
    ; unique = λ { (here refl) (here refl) → refl }
    }

SigmaStar⊒ : 1 ⊢ SigmaStar ꞉ StoreStar ⊒ˢ StoreStar
SigmaStar⊒ =
  ⊒ˢ-both wf★ wf★
    (id-onlyᵈ , (cast-id wf★ refl , id★))
    ⊒ˢ-nil

endpointsStar : EndpointWf 1 StoreStar ★ (＇ alpha0)
endpointsStar = wf★ˢ , wfVarˢ (here refl)

idStar⊒ : seal-or-idᵈ ∣ 1 ∣ StoreStar ⊢ id ★ ∶ ★ ⊒ ★
idStar⊒ = cast-id wf★ refl , id★

sealStar⊒ : seal-or-idᵈ ∣ 1 ∣ StoreStar ⊢ sealStar0 ∶ ★ ⊒ ＇ alpha0
sealStar⊒ = cast-seal wf★ (here refl) refl , sealⁿ ★ alpha0

untagAlpha⊒ᶜ : 1 ∣ StoreStar ⊢ untagAlpha0 ∶ᶜ ★ ⊒ ＇ alpha0
untagAlpha⊒ᶜ =
  cast-untag (wfVar z<s) (＇ alpha0) refl , untag (＇ alpha0)

right-seal-compose-to-untag :
  1 ∣ SigmaStar
    ⊢ id ★ ⨾ⁿ sealStar0 ≈ untagAlpha0 ∶ src (id ★) ⊒ ＇ alpha0
right-seal-compose-to-untag =
  compose-leftⁿ wfStoreStar idStar⊒ sealStar⊒
    (endpointsⁿ refl refl refl refl SigmaStar⊒ endpointsStar endpointsStar
      (seal-or-idᵈ ,
        proj₂ (_⨟ⁿ_ {wfΣ = wfStoreStar} idStar⊒ sealStar⊒))
      (tag-or-idᵈ , untagAlpha⊒ᶜ))

BroadRightSealContradiction : Set₁
BroadRightSealContradiction =
  ∀ {Δ σ p q B C D α} →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ p ∶ src q ⊒ ＇ α →
  ⊥

broad-right-seal-contradiction-is-false :
  BroadRightSealContradiction →
  ⊥
broad-right-seal-contradiction-is-false broad =
  broad untagAlpha⊒ᶜ right-seal-compose-to-untag

right-seal-compose-source-var⊥ :
  ∀ {Δ σ q r B α} →
  Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ r ∶ ＇ α ⊒ ＇ α →
  ⊥
right-seal-compose-source-var⊥
    (compose-leftⁿ wfΣ q⊒
      (cast-seal hB α∈Σ seal-ok , sealⁿ B α)
      q⨟seal≈r) =
  narrowing-var-to-older⊥ wfΣ (StoreDetWf.wfOlder wfΣ α∈Σ) q⊒
