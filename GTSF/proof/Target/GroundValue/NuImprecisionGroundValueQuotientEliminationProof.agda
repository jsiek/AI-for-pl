module proof.Target.GroundValue.NuImprecisionGroundValueQuotientEliminationProof where

-- File Charter:
--   * Proves quotient elimination for ground-related value representatives.
--   * Eliminates variable/base representatives and reclassifies the sole
--     function-ground case as ordinary paired widening.
--   * Contains no source-runtime or unrestricted dequotienting principle.

import Coercions as C
open import Agda.Builtin.Equality using (refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (_,_; proj₂)
open import ImprecisionWf using
  ( id★
  ; _↦_
  ; tag_⇛_
  ; _∣_⊢_⊑_⊣_
  )
import NarrowWiden as NW
open import PairedWideningCompatibility using
  (compatible-source-inert)
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuTermImprecision using
  ( leftStoreⁱ
  ; rightStoreⁱ
  ; seal★-tag-or-id
  )
open import NuTerms using (Value)
open import QuotientedTermImprecision using
  ( conv⊑convᵀ
  ; down⊑downᵀ
  ; gen-down⊑gen-downᵀ
  ; paired-widening
  ; seal★-gen-tag-or-id
  )
open import TermTyping using
  ( cast-gen
  ; cast-tag-or-id
  )
import Types as T
open import proof.Core.Permutation.ForallPermutationProperties using
  (⊑ᵖ-ground-left)
import proof.Core.Properties.NarrowWidenProperties as NWP
open import
  proof.Target.GroundValue.NuImprecisionGroundValueQuotientEliminationDef using
  (GroundValueQuotientEliminationᵀ)
open import proof.Quotient.NuImprecisionQuotientValue using
  ( cast-value-inert
  ; inert-narrowing-target-star
  ; source-inert-quotient-down-base-impossible
  ; source-inert-quotient-down-var-impossible
  )


star-widening-to-narrowing :
  ∀ {μ Δ Σ c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ T.★ ⊑ T.★ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ T.★ ⊒ T.★
star-widening-to-narrowing (() , NW.cross (NW.id-＇ α))
star-widening-to-narrowing (() , NW.cross (NW.id-‵ ι))
star-widening-to-narrowing (() , NW.cross (sⁿ NW.↦ tʷ))
star-widening-to-narrowing (() , NW.cross (NW.`∀ tʷ))
star-widening-to-narrowing (c⊢ , NW.id★) = c⊢ , NW.id★
star-widening-to-narrowing (() , NW.inst tʷ)
star-widening-to-narrowing
    (C.cast-tag hG () tag-ok , NW.tag gG)
star-widening-to-narrowing
    (C.cast-seq s⊢ (C.cast-tag hG gG⊢ tag-ok) , sʷ NW.︔ gG !) =
  ⊥-elim
    (NWP.widening-cross-ground-source-star⊥
      gG⊢ (s⊢ , NW.strictCrossʷ→cross sʷ))
star-widening-to-narrowing (() , NW.unsealʷ α A)
star-widening-to-narrowing
    (C.cast-seq () t⊢ , NW.unseal︔_ α tʷ)


star-narrowing-to-widening :
  ∀ {μ Δ Σ c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ T.★ ⊒ T.★ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ T.★ ⊑ T.★
star-narrowing-to-widening (() , NW.cross (NW.id-＇ α))
star-narrowing-to-widening (() , NW.cross (NW.id-‵ ι))
star-narrowing-to-widening (() , NW.cross (sʷ NW.↦ tⁿ))
star-narrowing-to-widening (() , NW.cross (NW.`∀ tⁿ))
star-narrowing-to-widening (c⊢ , NW.id★) = c⊢ , NW.id★
star-narrowing-to-widening (() , NW.gen tⁿ)
star-narrowing-to-widening
    (C.cast-untag hG () tag-ok , NW.untag gG)
star-narrowing-to-widening
    (C.cast-seq (C.cast-untag hG gG⊢ tag-ok) t⊢ ,
     gG NW.？︔ tⁿ) =
  ⊥-elim
    (NWP.narrowing-cross-ground-target-star⊥
      gG⊢ (t⊢ , NW.strictCrossⁿ→cross tⁿ))
star-narrowing-to-widening (() , NW.sealⁿ A α)
star-narrowing-to-widening
    (C.cast-seq s⊢ () , sⁿ NW.︔seal α)


inert-narrowing-to-function-ground-widening :
  ∀ {μ Δ Σ C c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ C ⊒ (T.★ T.⇒ T.★) →
  C.Inert c →
  μ ∣ Δ ∣ Σ ⊢ c ∶ C ⊑ (T.★ T.⇒ T.★)
inert-narrowing-to-function-ground-widening
    (() , NW.cross (NW.id-＇ α)) inert
inert-narrowing-to-function-ground-widening
    (() , NW.cross (NW.id-‵ ι)) inert
inert-narrowing-to-function-ground-widening
    (C.cast-fun s⊢ t⊢ , NW.cross (sʷ NW.↦ tⁿ)) (s C.↦ t)
    with NWP.widening-source-star-target-star (s⊢ , sʷ)
       | NWP.narrowing-target-star-source-star (t⊢ , tⁿ)
inert-narrowing-to-function-ground-widening
    (C.cast-fun s⊢ t⊢ , NW.cross (sʷ NW.↦ tⁿ)) (s C.↦ t)
    | refl | refl =
  C.cast-fun s⊢ t⊢ ,
  NW.cross
    (proj₂ (star-widening-to-narrowing (s⊢ , sʷ)) NW.↦
     proj₂ (star-narrowing-to-widening (t⊢ , tⁿ)))
inert-narrowing-to-function-ground-widening
    (() , NW.cross (NW.`∀ tⁿ)) inert
inert-narrowing-to-function-ground-widening
    (c⊢ , NW.id★) ()
inert-narrowing-to-function-ground-widening
    (() , NW.gen tⁿ) inert
inert-narrowing-to-function-ground-widening
    (c⊢ , NW.untag gG) ()
inert-narrowing-to-function-ground-widening
    (c⊢ , gG NW.？︔ tⁿ) ()
inert-narrowing-to-function-ground-widening
    (() , NW.sealⁿ A α) inert
inert-narrowing-to-function-ground-widening
    (c⊢ , sⁿ NW.︔seal α) ()


ground-value-quotient-elimination-proofᵀ :
  GroundValueQuotientEliminationᵀ
ground-value-quotient-elimination-proofᵀ
    (T.＇ α) vV vV′
    down@(down⊑downᵀ d⊒ d′⊒ M⊑M′ qD) =
  ⊥-elim (source-inert-quotient-down-var-impossible vV down)
ground-value-quotient-elimination-proofᵀ
    (T.＇ α) vV vV′
    down@(gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ qD) =
  ⊥-elim (source-inert-quotient-down-var-impossible vV down)
ground-value-quotient-elimination-proofᵀ
    (T.‵ ι) vV vV′
    down@(down⊑downᵀ d⊒ d′⊒ M⊑M′ qD) =
  ⊥-elim (source-inert-quotient-down-base-impossible vV down)
ground-value-quotient-elimination-proofᵀ
    (T.‵ ι) vV vV′
    down@(gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ qD) =
  ⊥-elim (source-inert-quotient-down-base-impossible vV down)
ground-value-quotient-elimination-proofᵀ
    T.★⇒★ vV vV′
    (down⊑downᵀ d⊒ d′⊒ M⊑M′ qD)
    with ⊑ᵖ-ground-left T.★⇒★ qD
ground-value-quotient-elimination-proofᵀ
    T.★⇒★ vV vV′
    (down⊑downᵀ d⊒ d′⊒ M⊑M′ qD)
    | id★ ↦ id★ =
  id★ ↦ id★ ,
  conv⊑convᵀ
    (paired-widening
      cast-tag-or-id seal★-tag-or-id
      (NW.widen-mode-relax C.id-only≤tag-or-idᵈ d⊑)
      cast-tag-or-id seal★-tag-or-id
      (NW.widen-mode-relax C.id-only≤tag-or-idᵈ d′⊑)
      (compatible-source-inert (cast-value-inert vV)))
    M⊑M′
  where
  d⊑ = inert-narrowing-to-function-ground-widening
    d⊒ (cast-value-inert vV)
  d′⊑ = inert-narrowing-to-function-ground-widening
    d′⊒ (cast-value-inert vV′)
ground-value-quotient-elimination-proofᵀ
    T.★⇒★ vV vV′
    (down⊑downᵀ d⊒ d′⊒ M⊑M′ qD)
    | tag id★ ⇛ id★ =
  ⊥-elim
    (inert-narrowing-target-star d′⊒ (cast-value-inert vV′))
ground-value-quotient-elimination-proofᵀ
    T.★⇒★ vV vV′
    (gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ qD)
    with ⊑ᵖ-ground-left T.★⇒★ qD
ground-value-quotient-elimination-proofᵀ
    T.★⇒★ vV vV′
    (gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ qD)
    | id★ ↦ id★ =
  id★ ↦ id★ ,
  conv⊑convᵀ
    (paired-widening
      (cast-gen cast-tag-or-id) seal★-gen-tag-or-id d⊑
      (cast-gen cast-tag-or-id) seal★-gen-tag-or-id d′⊑
      (compatible-source-inert (cast-value-inert vV)))
    M⊑M′
  where
  d⊑ = inert-narrowing-to-function-ground-widening
    d⊒ (cast-value-inert vV)
  d′⊑ = inert-narrowing-to-function-ground-widening
    d′⊒ (cast-value-inert vV′)
ground-value-quotient-elimination-proofᵀ
    T.★⇒★ vV vV′
    (gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ qD)
    | tag id★ ⇛ id★ =
  ⊥-elim
    (inert-narrowing-target-star d′⊒ (cast-value-inert vV′))
