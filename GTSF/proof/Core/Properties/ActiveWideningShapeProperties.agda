module proof.Core.Properties.ActiveWideningShapeProperties where

-- File Charter:
--   * Classifies non-inert coercions that carry a widening imprecision shape.
--   * Retains the exact identity, sequence, unseal, or instantiation shape
--     evidence needed by target pending-cast dispatch.
--   * Contains no cast typing, term imprecision, simulation result, postulate,
--     hole, permissive option, catch-all case, or termination bypass.

import CastImprecisionShape as CastShape
open import Coercions using
  ( Coercion
  ; Inert
  ; id
  ; unseal
  ; inst
  ; _!
  ; _↦_
  ; `∀
  ; _︔_
  )
open import Data.Empty using (⊥-elim)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; id★ˢ
  ; idˣˢ
  ; idιˢ
  ; tagιˢ
  ; tagˣˢ
  ; tag_⇛ˢ_
  ; νˢ_
  ; _↦ˢ_
  ; ∀ˢ_
  ; _；_≋_
  )
open import Relation.Nullary using (¬_)
open import Types using (Ty; TyVar; Base; ★; ＇_; ‵_; _⇒_)


data ActiveWideningShape :
    Coercion →
    ImprecisionShape →
    Set where

  active-id-var :
    ∀ {α : TyVar} →
    ActiveWideningShape (id (＇ α)) idˣˢ

  active-id-base :
    ∀ {ι : Base} →
    ActiveWideningShape (id (‵ ι)) idιˢ

  active-id-star :
    ActiveWideningShape (id ★) id★ˢ

  active-sequence :
    ∀ {c d p q r} →
    CastShape.widening CastShape.⊢ᶜ c ⦂ p →
    CastShape.widening CastShape.⊢ᶜ d ⦂ q →
    p ； q ≋ r →
    ActiveWideningShape (c ︔ d) r

  active-unseal :
    ∀ {α : TyVar} {A : Ty} →
    ActiveWideningShape (unseal α A) tagˣˢ

  active-inst :
    ∀ {B : Ty} {c p} →
    CastShape.widening CastShape.⊢ᶜ c ⦂ p →
    ActiveWideningShape (inst B c) (νˢ p)


data NonInstantiationActiveWideningShape :
    Coercion →
    ImprecisionShape →
    Set where

  non-inst-id-var :
    ∀ {α : TyVar} →
    NonInstantiationActiveWideningShape (id (＇ α)) idˣˢ

  non-inst-id-base :
    ∀ {ι : Base} →
    NonInstantiationActiveWideningShape (id (‵ ι)) idιˢ

  non-inst-id-star :
    NonInstantiationActiveWideningShape (id ★) id★ˢ

  non-inst-sequence :
    ∀ {c d p q r} →
    CastShape.widening CastShape.⊢ᶜ c ⦂ p →
    CastShape.widening CastShape.⊢ᶜ d ⦂ q →
    p ； q ≋ r →
    NonInstantiationActiveWideningShape (c ︔ d) r

  non-inst-unseal :
    ∀ {α : TyVar} {A : Ty} →
    NonInstantiationActiveWideningShape (unseal α A) tagˣˢ


active-widening-shape :
  ∀ {c shape} →
  CastShape.widening CastShape.⊢ᶜ c ⦂ shape →
  ¬ Inert c →
  ActiveWideningShape c shape
active-widening-shape CastShape.shape-id-var not-inert =
  active-id-var
active-widening-shape CastShape.shape-id-base not-inert =
  active-id-base
active-widening-shape CastShape.shape-id-star not-inert =
  active-id-star
active-widening-shape (CastShape.shape-fun {c = c} {d = d} c-shape d-shape)
    not-inert =
  ⊥-elim (not-inert (c ↦ d))
active-widening-shape (CastShape.shape-all {c = c} c-shape) not-inert =
  ⊥-elim (not-inert (`∀ c))
active-widening-shape
    (CastShape.shape-tag-var {α = α}) not-inert =
  ⊥-elim (not-inert ((＇ α) !))
active-widening-shape
    (CastShape.shape-tag-base {ι = ι}) not-inert =
  ⊥-elim (not-inert ((‵ ι) !))
active-widening-shape CastShape.shape-tag-fun not-inert =
  ⊥-elim (not-inert ((★ ⇒ ★) !))
active-widening-shape CastShape.shape-unseal not-inert =
  active-unseal
active-widening-shape (CastShape.shape-inst c-shape) not-inert =
  active-inst c-shape
active-widening-shape
    (CastShape.shape-sequence-widening c-shape d-shape composition)
    not-inert =
  active-sequence c-shape d-shape composition
