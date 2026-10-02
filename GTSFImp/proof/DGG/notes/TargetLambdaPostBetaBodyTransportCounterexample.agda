{-# OPTIONS --safe #-}

module proof.DGG.notes.TargetLambdaPostBetaBodyTransportCounterexample where

-- File Charter:
--   * Refutes direct strict-Lambda body transport from the structurally
--     aligned binder world to the plain post-beta-Lambda allocation world.
--   * Checks the live beta-inst/beta-Lambda two-allocation geometry.
--   * Constructs the required outer alpha and inner beta open-frame rebases
--     and shows that the body relation is restored only in the inner premise.
--   * Changes no production relation or proof interface.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using (★; ＇_; _⇒_)
import Imprecision as I
open import TyStore using (store-empty)
open import TermCtx using (Z)
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; _,ˢ_; ⇑ᵉᵗ; Term; ƛ_; `_)
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.SourceRebase using
  (SourceRebaseᶜ; source-rebase-now; open-source-rebase-frames)
open import proof.DGG.World


empty-context : Ctx
empty-context = ⟨ zero , store-empty , [] ⟩


base-world : empty-context ⊑ᶜ empty-context
base-world = emptyᶜ


-- beta-inst allocates target alpha with direct representation star.
alpha-allocation-world :
  empty-context ⊑ᶜ (empty-context ,ˢ ★)
alpha-allocation-world = bindRightᶜ base-world ★ (inj₁ refl)


-- Before beta-Lambda, the Lambda body binders are structurally aligned.
structural-body-world :
  ⇑ᵉᵗ empty-context ⊑ᶜ ⇑ᵉᵗ (empty-context ,ˢ ★)
structural-body-world = liftBothᶜ I.X⊑X alpha-allocation-world


alpha-name-fresh :
  RightBindFreshᶜ alpha-allocation-world (＇ Fin.zero)
alpha-name-fresh =
  inj₂ (Fin.suc Fin.zero , refl , λ ())


-- beta-Lambda allocates target beta with direct representation alpha.  The
-- source binder is then introduced independently.  This is the plain world
-- immediately after the two allocations, before either generated reveal is
-- interpreted as a source-pivot rebase.
plain-post-beta-world :
  ⇑ᵉᵗ empty-context ⊑ᶜ
    ((empty-context ,ˢ ★) ,ˢ ＇ Fin.zero)
plain-post-beta-world =
  liftLeftᶜ
    (bindRightᶜ alpha-allocation-world (＇ Fin.zero) alpha-name-fresh)


source-identity : Term (suc zero)
source-identity = ƛ (` zero)


target-identity : Term (suc (suc zero))
target-identity = ƛ (` zero)


structural-variable-imprecision :
  (＇ Fin.zero) ⊑ᵀ⟨ structural-body-world ⟩ (＇ Fin.zero)
structural-variable-imprecision = I.X⊑X


structural-body-imprecision :
  structural-body-world ⊢² source-identity ⊑ target-identity
    ∶ I.⇒⊑⇒ structural-variable-imprecision
        structural-variable-imprecision
structural-body-imprecision =
  CTI.ƛ⊑ƛ²
    {pA = structural-variable-imprecision}
    {pB = structural-variable-imprecision}
    (CTI.x⊑x² {p = structural-variable-imprecision} Z Z)


-- In the plain post-beta world, source X occupies center 0 while target beta
-- occupies center 1.  Therefore even the identity body's variable types are
-- no longer related.  This refutes a direct transport theorem whose target
-- is plain-post-beta-world.
plain-post-beta-variable-imprecision-impossible :
  (＇ Fin.zero) ⊑ᵀ⟨ plain-post-beta-world ⟩ (＇ Fin.zero) → ⊥
plain-post-beta-variable-imprecision-impossible ()


plain-post-beta-body-imprecision-impossible :
  (＇ Fin.zero ⇒ ＇ Fin.zero) ⊑ᵀ⟨ plain-post-beta-world ⟩
    (＇ Fin.zero ⇒ ＇ Fin.zero) → ⊥
plain-post-beta-body-imprecision-impossible (I.⇒⊑⇒ argument result) =
  plain-post-beta-variable-imprecision-impossible argument


------------------------------------------------------------------------
-- The live nested-frame repair
------------------------------------------------------------------------

alpha-update : PivotUpdateᵗ
    (ηᴸᶜ plain-post-beta-world) Fin.zero
    (toRenameⁱ (ηᴿᶜ plain-post-beta-world) (Fin.suc Fin.zero))
alpha-update = repointⁱ
  (ηᴸᶜ plain-post-beta-world) Fin.zero
  (toRenameⁱ (ηᴿᶜ plain-post-beta-world) (Fin.suc Fin.zero))
  (λ ())
  (λ { Fin.zero zero≠zero → ⊥-elim (zero≠zero refl) })


alpha-representation :
  (＇ Fin.zero) ⊑ᵀ⟨ plain-post-beta-world ⟩ ★
alpha-representation = I.X⊑★ refl


alpha-premise-world :
  ⇑ᵉᵗ empty-context ⊑ᶜ
    ((empty-context ,ˢ ★) ,ˢ ＇ Fin.zero)
alpha-premise-world =
  rebaseSourceᶜ plain-post-beta-world Fin.zero (Fin.suc Fin.zero)
    alpha-update open-frameᶜ alpha-representation


alpha-rebase : SourceRebaseᶜ plain-post-beta-world alpha-premise-world
    Fin.zero (Fin.suc Fin.zero)
alpha-rebase = source-rebase-now alpha-update alpha-representation


beta-update : PivotUpdateᵗ
    (ηᴸᶜ alpha-premise-world) Fin.zero
    (toRenameⁱ (ηᴿᶜ alpha-premise-world) Fin.zero)
beta-update = repointⁱ
  (ηᴸᶜ alpha-premise-world) Fin.zero
  (toRenameⁱ (ηᴿᶜ alpha-premise-world) Fin.zero)
  (λ ())
  (λ { Fin.zero zero≠zero → ⊥-elim (zero≠zero refl) })


beta-representation :
  (＇ Fin.zero) ⊑ᵀ⟨ alpha-premise-world ⟩
    (＇ Fin.suc Fin.zero)
beta-representation = I.X⊑X


beta-premise-world :
  ⇑ᵉᵗ empty-context ⊑ᶜ
    ((empty-context ,ˢ ★) ,ˢ ＇ Fin.zero)
beta-premise-world =
  rebaseSourceᶜ alpha-premise-world Fin.zero Fin.zero
    beta-update open-frameᶜ beta-representation


beta-rebase : SourceRebaseᶜ alpha-premise-world beta-premise-world
    Fin.zero Fin.zero
beta-rebase = source-rebase-now beta-update beta-representation


-- The inner beta premise realigns source X with target beta.  The exact
-- variable and identity-body witnesses rejected by the plain world are again
-- available here.
beta-source-zero-image :
  toRenameⁱ (ηᴸᶜ beta-premise-world) Fin.zero ≡ Fin.suc Fin.zero
beta-source-zero-image = refl


beta-target-zero-image :
  toRenameⁱ (ηᴿᶜ beta-premise-world) Fin.zero ≡ Fin.suc Fin.zero
beta-target-zero-image = refl


beta-premise-variable-imprecision :
  (＇ Fin.zero) ⊑ᵀ⟨ beta-premise-world ⟩ (＇ Fin.zero)
beta-premise-variable-imprecision
  rewrite beta-source-zero-image | beta-target-zero-image =
  I.X⊑X


beta-premise-function-imprecision :
  (＇ Fin.zero ⇒ ＇ Fin.zero) ⊑ᵀ⟨ beta-premise-world ⟩
    (＇ Fin.zero ⇒ ＇ Fin.zero)
beta-premise-function-imprecision =
  I.⇒⊑⇒ beta-premise-variable-imprecision
    beta-premise-variable-imprecision


beta-premise-body-imprecision :
  beta-premise-world ⊢² source-identity ⊑ target-identity
    ∶ beta-premise-function-imprecision
beta-premise-body-imprecision =
  CTI.ƛ⊑ƛ²
    {A = ＇ Fin.zero} {A′ = ＇ Fin.zero}
    {B = ＇ Fin.zero} {B′ = ＇ Fin.zero}
    {pA = beta-premise-variable-imprecision}
    {pB = beta-premise-variable-imprecision}
    (CTI.x⊑x² {A = ＇ Fin.zero} {B = ＇ Fin.zero}
      {p = beta-premise-variable-imprecision} Z Z)


plain-open-frames : openFramesᶜ plain-post-beta-world ≡ []
plain-open-frames = refl


alpha-open-frames : openFramesᶜ alpha-premise-world ≡
    (Fin.zero ↔ᶜ Fin.suc Fin.zero) ∷ []
alpha-open-frames = open-source-rebase-frames alpha-rebase


beta-open-frames : openFramesᶜ beta-premise-world ≡
    (Fin.zero ↔ᶜ Fin.zero) ∷
    (Fin.zero ↔ᶜ Fin.suc Fin.zero) ∷ []
beta-open-frames = open-source-rebase-frames beta-rebase
