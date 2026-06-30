module proof.RightSealBroadCounterexample where

-- File Charter:
--   * Small checked counterexample to the broad claim that a tag/id-mode
--     narrowing can never be endpoint-equivalent to a right-seal composite.
--   * The counterexample uses `id ★ ⨾ seal ★ α ≈ (＇ α) ？`: the composition
--     itself is typed in seal mode, while the right endpoint witness is the
--     tag/id-mode untag-like narrowing.
--   * Uses only existing coercion/narrowing infrastructure and adds no
--     postulates.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (z<s)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

open import Types
open import Coercions
open import NarrowWiden
open import NarrowWidenComposition
open import proof.CoercionProperties using (coercion-src-tgtᵐ)
open import proof.NarrowWidenProperties
  using (StoreDetWf; castlike-var-var-endpoints; narrowing-var-to-older⊥)

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

right-seal-compose-left-seal-factor⊥ :
  ∀ {Δ σ q p r A B C D E F α β} →
  Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ p ∶ src q ⊒ ＇ α →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ r ≈ seal A β ⨾ⁿ p ∶ E ⊒ F →
  ⊥
right-seal-compose-left-seal-factor⊥
    {Δ = Δ} {σ = σ} {q = q} {p = p} {B = B}
    {C = C} {D = D} {α = α} {β = β}
    outer@(compose-leftⁿ wfΣ₀ q⊒ seal⊒
      (endpointsⁿ src-u tgt-u src-p tgt-p
        σ⊒ wfΣ₁ wfΣ₂ u⊒ p⊒outer))
    pᶜ
    (compose-rightⁿ wfΣ
      (cast-seal hA β∈Σ seal-ok , sealⁿ A β)
      p⊒
      r≈seal⨟p) =
  right-seal-compose-source-var⊥
    (subst
      (λ S → Δ ∣ σ ⊢ q ⨾ⁿ seal B α ≈ p ∶ S ⊒ ＇ α)
      src-q≡＇α
      outer)
  where
    pᶜ-src : src p ≡ C
    pᶜ-src = proj₁ (coercion-src-tgtᵐ (proj₁ pᶜ))

    pᶜ-tgt : tgt p ≡ D
    pᶜ-tgt = proj₂ (coercion-src-tgtᵐ (proj₁ pᶜ))

    p-src-β : src p ≡ ＇ β
    p-src-β = proj₁ (coercion-src-tgtᵐ (proj₁ p⊒))

    pᶜ-var-src :
      Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ ＇ β ⊒ D
    pᶜ-var-src =
      subst
        (λ S → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ S ⊒ D)
        (trans (sym pᶜ-src) p-src-β)
        pᶜ

    pᶜ-var :
      Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ ＇ β ⊒ ＇ α
    pᶜ-var =
      subst
        (λ T → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ ＇ β ⊒ T)
        (trans (sym pᶜ-tgt) tgt-p)
        pᶜ-var-src

    β≡α : β ≡ α
    β≡α = castlike-var-var-endpoints pᶜ-var

    src-q≡＇α : src q ≡ ＇ α
    src-q≡＇α =
      trans (sym src-p) (trans p-src-β (cong ＇_ β≡α))
