module proof.Target.SealTag.NuImprecisionTargetTagCancellationProof where

-- File Charter:
--   * Proves cancellation of one terminal target ground tag.
--   * Pushes cancellation through source-only binders, inert source casts,
--     paired widenings, quotient-up boundaries, and allocation prefixes.
--   * Uses source-name exclusivity and proof-index uniqueness explicitly.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

import Coercions as C
import Conversion as CV
open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; widening; shape-tag-fun)
open import ConversionIndexCompatibility using
  ( _[_↦_]ᴸ_
  ; replace-left-function
  ; replace-left-function-tag
  ; replace-left-ν
  )
open import ForallPermutation using
  (quotientᵖ; _∣_⊢_⊑ᵖ_⊣_)
open import Imprecision using (_ˣ⊑★; _ˣ⊑ˣ_)
open import ImprecisionComposition using
  ( ⌊_⌋
  ; id★ˢ
  ; tag_⇛ˢ_
  ; _；_≋_
  ; compose-right-id★
  ; comp-↦-↦
  ; comp-↦-tag
  ; comp-∀-ν
  ; comp-ν
  ; quotient-boundary-square
  ; _；⌊_⌋≋ᵖ_；_
  )
open import ImprecisionWf using
  ( id★
  ; tagˣ
  ; idˣ
  ; _↦_
  ; tag_⇛_
  ; ν
  ; _∣_⊢_⊑_⊣_
  )
import NarrowWiden as NW
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( lift-left-ctx-[]
  )
open import proof.Core.Properties.CastImprecision using
  ( seal★-tag-or-id
  )
open import NuTerms using
  ( Term
  ; Value
  ; no•-Λ
  ; no•-⟨⟩
  ; _⟨_⟩
  )
open import QuotientImprecisionCompatibility using
  ( ReductionClosedQuotientWideningCompatible
  ; compatible-allᴿ
  ; compatible-functionᴿ
  ; compatible-tagᴿ
  ; compatible-target-activeᴿ
  ; compatible-target-inert-bridgeᴿ
  ; compatible-through-representativesᴿ
  )
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; closeᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; paired-concealᵀ
  ; paired-revealᵀ
  ; paired-wideningᵀ
  ; quotient-cast-widening
  ; quotient-id-widening
  ; Λ⊑ᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; target-instantiationᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( _∣_∣_⊢_⦂_
  ; cast-tag-or-id
  ; ⊢⟨⟩↑
  ; ⊢⟨⟩↓
  ; ⊢⟨⟩⊒
  ; ⊢⟨⟩⊑
  )
import Types as T
open import proof.Compilation.GenSafeProperties using
  ( genSafeShape-atomic-impossible
  ; genSafe-source-shape
  ; genSafe-target-shape
  ; narrowing-inert-view
  ; shape-all
  ; shape-fun
  )
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using (embedded-creation-target-shapeᴱ)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( imprecision-composition-shape-transport
  ; shape-source-liftνᵢ
  )
open import proof.Core.Permutation.ForallPermutationProperties using
  (≈∀-ground-right-eq)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (⊑-source-liftνᵢ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof
  using (assumption-membership-unique-source)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessLemma using
  (assumption-membership-unique→precision-index-unique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityProof using
  (source-name-exclusive-source-only-head)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import
  proof.Target.GroundValue.NuImprecisionTargetFunctionGroundValueQuotientEliminationLemma
  using (target-function-ground-value-quotient-eliminationᵀ)
open import
  proof.Target.GroundValue.NuImprecisionTargetGroundValueQuotientEliminationProperties
  using
    ( function-ground-self-permutation-shape-equal
    ; source-ground-≈∀-left
    ; source-ground-≈∀-left-composition
    )
open import
  proof.Target.SealTag.NuImprecisionTargetGroundUniqueness using
  ( gen-safe-shape-ground-function
  ; gen-safe-shape-star-to-function
  ; target-ground-unique
  )
open import
  proof.Target.SealTag.NuImprecisionTargetTagCancellationDef using
  (TargetTagCancellationᵀ)


target-tag-typing⁻¹ :
  ∀ {Δ Σ Γ W G} →
  Δ ∣ Σ ∣ Γ ⊢ W ⟨ G C.! ⟩ ⦂ T.★ →
  Δ ∣ Σ ∣ Γ ⊢ W ⦂ G
target-tag-typing⁻¹ (⊢⟨⟩↑ () W⊢)
target-tag-typing⁻¹ (⊢⟨⟩↓ () W⊢)
target-tag-typing⁻¹
    (⊢⟨⟩⊒ mode seal★ (c⊢ , NW.cross ()) W⊢)
target-tag-typing⁻¹
    (⊢⟨⟩⊑ mode seal★
      (C.cast-tag hG gG ok , NW.tag gG′) W⊢) =
  W⊢


source-variable-ground-impossible :
  ∀ {Φ Δᴸ Δᴿ α H} →
  (∀ {β} →
    (α ˣ⊑★) ∈ Φ →
    (α ˣ⊑ˣ β) ∈ Φ →
    ⊥) →
  Φ ∣ Δᴸ ⊢ T.＇ α ⊑ T.★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ T.＇ α ⊑ H ⊣ Δᴿ →
  T.Ground H →
  ⊥
source-variable-ground-impossible exclusive
    (tagˣ source-only α<) (idˣ matched α<′ β<)
    (T.＇ β) =
  exclusive source-only matched


star-ground-impossible :
  ∀ {Φ Δᴸ Δᴿ H} →
  Φ ∣ Δᴸ ⊢ T.★ ⊑ H ⊣ Δᴿ →
  T.Ground H →
  ⊥
star-ground-impossible id★ ()


source-inert-narrowing-route :
  ∀ {Φ Δᴸ Δᴿ μ Σ c A B H} →
  (∀ {α β} →
    (α ˣ⊑★) ∈ Φ →
    (α ˣ⊑ˣ β) ∈ Φ →
    ⊥) →
  C.Inert c →
  μ ∣ Δᴸ ∣ Σ ⊢ c ∶ A ⊒ B →
  Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ T.★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ H ⊣ Δᴿ →
  T.Ground H →
  (Φ ∣ Δᴸ ⊢ A ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) ×
  H ≡ T.★ T.⇒ T.★
source-inert-narrowing-route exclusive inert (c⊢ , narrowing)
    inner-index outer-index requested ground
    with narrowing-inert-view narrowing inert
source-inert-narrowing-route exclusive inert (c⊢ , narrowing)
    inner-index outer-index requested ground
    | inj₁ safe =
  gen-safe-shape-star-to-function
    (genSafe-source-shape c⊢ safe) inner-index ,
  gen-safe-shape-ground-function
    (genSafe-target-shape c⊢ safe) requested ground
source-inert-narrowing-route exclusive inert (c⊢ , narrowing)
    inner-index outer-index requested ground
    | inj₂ (D , α , refl)
    with c⊢
source-inert-narrowing-route exclusive inert (c⊢ , narrowing)
    inner-index outer-index requested ground
    | inj₂ (D , α , refl)
    | C.cast-seal hD α∈Σ ok =
  ⊥-elim
    (source-variable-ground-impossible exclusive
      outer-index requested ground)


source-inert-widening-route :
  ∀ {Φ Δᴸ Δᴿ μ Σ c A B H} →
  C.Inert c →
  μ ∣ Δᴸ ∣ Σ ⊢ c ∶ A ⊑ B →
  Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ H ⊣ Δᴿ →
  T.Ground H →
  (Φ ∣ Δᴸ ⊢ A ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) ×
  H ≡ T.★ T.⇒ T.★
source-inert-widening-route
    (G C.!) (C.cast-tag hG gG ok , NW.tag gG′)
    inner-index requested ground =
  ⊥-elim (star-ground-impossible requested ground)
source-inert-widening-route
    (s C.↦ t)
    (C.cast-fun s⊢ t⊢ , NW.cross (sⁿ NW.↦ tʷ))
    inner-index requested T.★⇒★ =
  gen-safe-shape-star-to-function
    shape-fun inner-index ,
  refl
source-inert-widening-route
    (C.`∀ c) (C.cast-all c⊢ , NW.cross (NW.`∀ cʷ))
    inner-index requested ground =
  gen-safe-shape-star-to-function
    shape-all inner-index ,
  gen-safe-shape-ground-function
    shape-all requested ground
source-inert-widening-route
    (C.seal A α) (c⊢ , NW.cross ())
    inner-index requested ground
source-inert-widening-route
    (C.gen A c) (c⊢ , NW.cross ())
    inner-index requested ground


source-inert-widening-ground-route :
  ∀ {Φ Δᴸ Δᴿ μ Σ c A B G H} →
  C.Inert c →
  μ ∣ Δᴸ ∣ Σ ⊢ c ∶ A ⊑ B →
  Φ ∣ Δᴸ ⊢ A ⊑ G ⊣ Δᴿ →
  T.Ground G →
  Φ ∣ Δᴸ ⊢ B ⊑ H ⊣ Δᴿ →
  T.Ground H →
  G ≡ T.★ T.⇒ T.★ × H ≡ T.★ T.⇒ T.★
source-inert-widening-ground-route
    (G₀ C.!) (C.cast-tag hG₀ gG₀ ok , NW.tag gG₀′)
    inner groundG requested groundH =
  ⊥-elim (star-ground-impossible requested groundH)
source-inert-widening-ground-route
    (s C.↦ t)
    (C.cast-fun s⊢ t⊢ , NW.cross (sⁿ NW.↦ tʷ))
    inner T.★⇒★ requested T.★⇒★ =
  refl , refl
source-inert-widening-ground-route
    (C.`∀ c) (C.cast-all c⊢ , NW.cross (NW.`∀ cʷ))
    inner groundG requested groundH =
  gen-safe-shape-ground-function shape-all inner groundG ,
  gen-safe-shape-ground-function shape-all requested groundH
source-inert-widening-ground-route
    (C.seal A α) (c⊢ , NW.cross ())
    inner groundG requested groundH
source-inert-widening-ground-route
    (C.gen A c) (c⊢ , NW.cross ())
    inner groundG requested groundH


source-inert-widening-result-ground-route :
  ∀ {Φ Δᴸ Δᴿ μ Σ c A B H} →
  C.Inert c →
  μ ∣ Δᴸ ∣ Σ ⊢ c ∶ A ⊑ B →
  Φ ∣ Δᴸ ⊢ B ⊑ H ⊣ Δᴿ →
  T.Ground H →
  H ≡ T.★ T.⇒ T.★
source-inert-widening-result-ground-route
    (G C.!) (C.cast-tag hG gG ok , NW.tag gG′)
    requested ground =
  ⊥-elim (star-ground-impossible requested ground)
source-inert-widening-result-ground-route
    (s C.↦ t)
    (C.cast-fun s⊢ t⊢ , NW.cross (sⁿ NW.↦ tʷ))
    requested ground =
  gen-safe-shape-ground-function shape-fun requested ground
source-inert-widening-result-ground-route
    (C.`∀ c) (C.cast-all c⊢ , NW.cross (NW.`∀ cʷ))
    requested ground =
  gen-safe-shape-ground-function shape-all requested ground
source-inert-widening-result-ground-route
    (C.seal A α) (c⊢ , NW.cross ()) requested ground
source-inert-widening-result-ground-route
    (C.gen A c) (c⊢ , NW.cross ()) requested ground


quotient-close-target-tag-ground-route :
  ∀ {Φ Δᴸ Δᴿ μ Σ u C A G H}
    {qD : Φ ∣ Δᴸ ⊢ C ⊑ᵖ G ⊣ Δᴿ}
    {u-shape target-shape} →
  SourceNameExclusive Φ →
  C.Inert u →
  μ ∣ Δᴸ ∣ Σ ⊢ u ∶ C ⊑ A →
  (outer : Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ) →
  (requested : Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ) →
  (gG : T.Ground G) →
  (gH : T.Ground H) →
  ReductionClosedQuotientWideningCompatible
    Φ Δᴸ Δᴿ u (G C.!) qD outer u-shape target-shape →
  G ≡ T.★ T.⇒ T.★ × H ≡ T.★ T.⇒ T.★
quotient-close-target-tag-ground-route
    {G = G} exclusive inert u⊑ outer requested gG gH
    (compatible-through-representativesᴿ
      source-shape target-shape (compatible-tagᴿ G₀))
    with u⊑
quotient-close-target-tag-ground-route
    {G = G} exclusive inert u⊑ outer requested gG gH
    (compatible-through-representativesᴿ
      source-shape target-shape (compatible-tagᴿ G₀))
    | (C.cast-tag hG₀ gG₀ ok , NW.tag gG₀′) =
  ⊥-elim
    (star-ground-impossible requested gH)
quotient-close-target-tag-ground-route
    {G = G} exclusive inert u⊑ outer requested gG gH
    (compatible-through-representativesᴿ
      source-shape target-shape
      (compatible-target-activeᴿ inert-u not-inert-target)) =
  ⊥-elim (not-inert-target (G C.!))
quotient-close-target-tag-ground-route
    {G = G} exclusive inert u⊑ outer requested gG gH
    (compatible-through-representativesᴿ
      {tgt = target-equivalence}
      source-shape target-shape
      (compatible-target-inert-bridgeᴿ bridge-evidence))
    with ≈∀-ground-right-eq gG target-equivalence
quotient-close-target-tag-ground-route
    {G = G} exclusive inert u⊑ outer requested gG gH
    (compatible-through-representativesᴿ
      {tgt = target-equivalence}
      source-shape target-shape
      (compatible-target-inert-bridgeᴿ bridge-evidence))
    | refl
    with bridge-evidence (G C.!)
       | source-inert-widening-result-ground-route
           inert u⊑ requested gH
quotient-close-target-tag-ground-route
    {G = G} exclusive inert u⊑ outer requested gG gH
    (compatible-through-representativesᴿ
      {tgt = target-equivalence}
      source-shape target-shape
      (compatible-target-inert-bridgeᴿ bridge-evidence))
    | refl | bridge , source-triangle , target-triangle | refl
    with target-ground-unique exclusive outer bridge requested gG T.★⇒★
quotient-close-target-tag-ground-route
    {G = G} exclusive inert u⊑ outer requested gG gH
    (compatible-through-representativesᴿ
      {tgt = target-equivalence}
      source-shape target-shape
      (compatible-target-inert-bridgeᴿ bridge-evidence))
    | refl | bridge , source-triangle , target-triangle | refl | refl =
  refl , refl


source-inert-reveal-route :
  ∀ {Φ Δᴸ Δᴿ μ Σ α X c A B H} →
  C.Inert c →
  CV.RevealConversion μ Δᴸ Σ α X c A B →
  Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ H ⊣ Δᴿ →
  T.Ground H →
  (Φ ∣ Δᴸ ⊢ A ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) ×
  H ≡ T.★ T.⇒ T.★
source-inert-reveal-route () (CV.reveal-id-var hY ok)
    inner requested ground
source-inert-reveal-route () CV.reveal-id-base
    inner requested ground
source-inert-reveal-route () CV.reveal-id-★
    inner requested ground
source-inert-reveal-route () (CV.reveal-unseal hX α∈Σ ok)
    inner requested ground
source-inert-reveal-route (s C.↦ t) (CV.reveal-fun s↓ t↑)
    inner requested T.★⇒★ =
  gen-safe-shape-star-to-function shape-fun inner , refl
source-inert-reveal-route (C.`∀ c) (CV.reveal-all c↑)
    inner requested ground =
  gen-safe-shape-star-to-function shape-all inner ,
  gen-safe-shape-ground-function shape-all requested ground


source-inert-conceal-route :
  ∀ {Φ Δᴸ Δᴿ μ Σ α X c A B H} →
  (∀ {β γ} →
    (β ˣ⊑★) ∈ Φ →
    (β ˣ⊑ˣ γ) ∈ Φ →
    ⊥) →
  C.Inert c →
  CV.ConcealConversion μ Δᴸ Σ α X c A B →
  Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ T.★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ H ⊣ Δᴿ →
  T.Ground H →
  (Φ ∣ Δᴸ ⊢ A ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) ×
  H ≡ T.★ T.⇒ T.★
source-inert-conceal-route exclusive ()
    (CV.conceal-id-var hY ok) inner outer requested ground
source-inert-conceal-route exclusive () CV.conceal-id-base
    inner outer requested ground
source-inert-conceal-route exclusive () CV.conceal-id-★
    inner outer requested ground
source-inert-conceal-route exclusive
    (C.seal X α) (CV.conceal-seal hX α∈Σ ok)
    inner outer requested ground =
  ⊥-elim
    (source-variable-ground-impossible exclusive
      outer requested ground)
source-inert-conceal-route exclusive
    (s C.↦ t) (CV.conceal-fun s↑ t↓)
    inner outer requested T.★⇒★ =
  gen-safe-shape-star-to-function shape-fun inner , refl
source-inert-conceal-route exclusive
    (C.`∀ c) (CV.conceal-all c↓)
    inner outer requested ground =
  gen-safe-shape-star-to-function shape-all inner ,
  gen-safe-shape-ground-function shape-all requested ground


source-index-composition-target-untag-function :
  ∀ {Φ Δᴸ Δᴿ A B s} →
  AssumptionMembershipUnique Φ →
  (p★ : Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ) →
  (p⇒ : Φ ∣ Δᴸ ⊢ A ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) →
  (q★ : Φ ∣ Δᴸ ⊢ B ⊑ T.★ ⊣ Δᴿ) →
  (q⇒ : Φ ∣ Δᴸ ⊢ B ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) →
  s ； ⌊ q★ ⌋ ≋ ⌊ p★ ⌋ →
  s ； ⌊ q⇒ ⌋ ≋ ⌊ p⇒ ⌋
source-index-composition-target-untag-function
    unique (tag p₁ ⇛ p₂) (r₁ ↦ r₂)
    (tag q₁ ⇛ q₂) (s₁ ↦ s₂)
    (comp-↦-tag comp₁ comp₂)
    with assumption-membership-unique→precision-index-unique unique p₁ r₁
       | assumption-membership-unique→precision-index-unique unique p₂ r₂
       | assumption-membership-unique→precision-index-unique unique q₁ s₁
       | assumption-membership-unique→precision-index-unique unique q₂ s₂
source-index-composition-target-untag-function
    unique (tag p₁ ⇛ p₂) (r₁ ↦ r₂)
    (tag q₁ ⇛ q₂) (s₁ ↦ s₂)
    (comp-↦-tag comp₁ comp₂)
    | refl | refl | refl | refl =
  comp-↦-↦ comp₁ comp₂
source-index-composition-target-untag-function
    unique (ν safe-p★ occ-p★ p★) (ν safe-p⇒ occ-p⇒ p⇒)
    q★ q⇒ (comp-ν comp) =
  comp-ν
    (imprecision-composition-shape-transport
      refl (sym (shape-source-liftνᵢ q⇒)) refl
      (source-index-composition-target-untag-function
        (assumption-membership-unique-source unique)
        p★ p⇒
        (⊑-source-liftνᵢ q★) (⊑-source-liftνᵢ q⇒)
        (imprecision-composition-shape-transport
          refl (shape-source-liftνᵢ q★) refl comp)))
source-index-composition-target-untag-function
    unique (ν safe-p★ occ-p★ p★) (ν safe-p⇒ occ-p⇒ p⇒)
    (ν safe-q★ occ-q★ q★) (ν safe-q⇒ occ-q⇒ q⇒)
    (comp-∀-ν comp) =
  comp-∀-ν
    (source-index-composition-target-untag-function
      (assumption-membership-unique-source unique)
      p★ p⇒ q★ q⇒ comp)


source-replacement-target-untag-function :
  ∀ {Φ Δᴸ Δᴿ A B α X} →
  AssumptionMembershipUnique Φ →
  (p★ : Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ) →
  (p⇒ : Φ ∣ Δᴸ ⊢ A ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) →
  (q★ : Φ ∣ Δᴸ ⊢ B ⊑ T.★ ⊣ Δᴿ) →
  (q⇒ : Φ ∣ Δᴸ ⊢ B ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) →
  p★ [ α ↦ X ]ᴸ q★ →
  p⇒ [ α ↦ X ]ᴸ q⇒
source-replacement-target-untag-function
    unique (tag p₁ ⇛ p₂) (r₁ ↦ r₂)
    (tag q₁ ⇛ q₂) (s₁ ↦ s₂)
    (replace-left-function-tag replace₁ replace₂)
    with assumption-membership-unique→precision-index-unique unique p₁ r₁
       | assumption-membership-unique→precision-index-unique unique p₂ r₂
       | assumption-membership-unique→precision-index-unique unique q₁ s₁
       | assumption-membership-unique→precision-index-unique unique q₂ s₂
source-replacement-target-untag-function
    unique (tag p₁ ⇛ p₂) (r₁ ↦ r₂)
    (tag q₁ ⇛ q₂) (s₁ ↦ s₂)
    (replace-left-function-tag replace₁ replace₂)
    | refl | refl | refl | refl =
  replace-left-function replace₁ replace₂
source-replacement-target-untag-function
    unique (ν safe-p★ occ-p★ p★) (ν safe-p⇒ occ-p⇒ p⇒)
    (ν safe-q★ occ-q★ q★) (ν safe-q⇒ occ-q⇒ q⇒)
    (replace-left-ν replace) =
  replace-left-ν
    (source-replacement-target-untag-function
      (assumption-membership-unique-source unique)
      p★ p⇒ q★ q⇒ replace)


source-cast-index-compatible-target-untag-function :
  ∀ {Φ Δᴸ Δᴿ A B c s} →
  AssumptionMembershipUnique Φ →
  (p★ : Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ) →
  (p⇒ : Φ ∣ Δᴸ ⊢ A ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) →
  (q★ : Φ ∣ Δᴸ ⊢ B ⊑ T.★ ⊣ Δᴿ) →
  (q⇒ : Φ ∣ Δᴸ ⊢ B ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) →
  widening ⊢ᶜ c ⦂ s →
  s ； ⌊ q★ ⌋ ≋ ⌊ p★ ⌋ →
  s ； ⌊ q⇒ ⌋ ≋ ⌊ p⇒ ⌋
source-cast-index-compatible-target-untag-function
    unique p★ p⇒ q★ q⇒ c-shape comp =
  source-index-composition-target-untag-function
    unique p★ p⇒ q★ q⇒ comp


target-function-tag-index :
  ∀ {Φ Δᴸ Δᴿ A} →
  Φ ∣ Δᴸ ⊢ A ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ
target-function-tag-index (p₁ ↦ p₂) = tag p₁ ⇛ p₂
target-function-tag-index (ν safe occ p) =
  ν safe occ (target-function-tag-index p)


target-function-tag-composition-result :
  ∀ {Φ Δᴸ Δᴿ A r}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) →
  ⌊ p ⌋ ； (tag id★ˢ ⇛ˢ id★ˢ) ≋ r →
  ⌊ target-function-tag-index p ⌋ ≡ r
target-function-tag-composition-result
    (p₁ ↦ p₂) (comp-↦-tag comp₁ comp₂)
    with compose-right-id★ comp₁
       | compose-right-id★ comp₂
target-function-tag-composition-result
    (p₁ ↦ p₂) (comp-↦-tag comp₁ comp₂)
    | refl | refl = refl
target-function-tag-composition-result
    (ν safe occ p) (comp-ν comp)
    with target-function-tag-composition-result p comp
target-function-tag-composition-result
    (ν safe occ p) (comp-ν comp) | refl = refl


paired-source-cast-index-compatible-target-untag-function :
  ∀ {Φ Δᴸ Δᴿ A B c s r} →
  AssumptionMembershipUnique Φ →
  (p⇒ : Φ ∣ Δᴸ ⊢ A ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) →
  (q★ : Φ ∣ Δᴸ ⊢ B ⊑ T.★ ⊣ Δᴿ) →
  (q⇒ : Φ ∣ Δᴸ ⊢ B ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) →
  widening ⊢ᶜ c ⦂ s →
  s ； ⌊ q★ ⌋ ≋ r →
  ⌊ p⇒ ⌋ ； (tag id★ˢ ⇛ˢ id★ˢ) ≋ r →
  s ； ⌊ q⇒ ⌋ ≋ ⌊ p⇒ ⌋
paired-source-cast-index-compatible-target-untag-function
    unique p⇒ q★ q⇒ c-shape left-square right-square
    with target-function-tag-composition-result p⇒ right-square
paired-source-cast-index-compatible-target-untag-function
    unique p⇒ q★ q⇒ c-shape left-square right-square
    | refl =
  source-cast-index-compatible-target-untag-function
    unique (target-function-tag-index p⇒) p⇒ q★ q⇒
    c-shape left-square


quotient-function-tag-right-composition :
  ∀ {Φ Δᴸ Δᴿ A D s}
    (unique : AssumptionMembershipUnique Φ)
    (p★ : Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ)
    (p⇒ : Φ ∣ Δᴸ ⊢ A ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ)
    (qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ T.★ T.⇒ T.★ ⊣ Δᴿ)
    (q : Φ ∣ Δᴸ ⊢ D ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) →
  s ；⌊ p★ ⌋≋ᵖ qD ； (tag id★ˢ ⇛ˢ id★ˢ) →
  s ； ⌊ p⇒ ⌋ ≋ ⌊ q ⌋
quotient-function-tag-right-composition
    unique p★ p⇒
    (quotientᵖ source middle target) q
    (quotient-boundary-square
      source-shape left-composition target-shape right-composition)
    with ≈∀-ground-right-eq T.★⇒★ target
quotient-function-tag-right-composition
    unique p★ p⇒
    (quotientᵖ source middle target) q
    (quotient-boundary-square
      source-shape left-composition target-shape right-composition)
    | refl =
  subst
    (λ r → _ ； ⌊ p⇒ ⌋ ≋ ⌊ r ⌋)
    canonical≡q canonical-composition
  where
  target-shape-equality =
    function-ground-self-permutation-shape-equal target-shape

  right-composition′ =
    imprecision-composition-shape-transport
      refl (sym target-shape-equality) refl right-composition

  tagged-middle≡result =
    target-function-tag-composition-result middle right-composition′

  untagged-middle-composition =
    source-index-composition-target-untag-function
      unique (target-function-tag-index middle) middle p★ p⇒
      (imprecision-composition-shape-transport
        refl refl tagged-middle≡result left-composition)

  canonical =
    source-ground-≈∀-left T.★⇒★ source middle

  canonical-composition =
    source-ground-≈∀-left-composition
      T.★⇒★ source source-shape middle untagged-middle-composition

  canonical≡q =
    assumption-membership-unique→precision-index-unique
      unique canonical q


cast-coercion-injective :
  ∀ {M M′ : Term} {c c′ : C.Coercion} →
  M ⟨ c ⟩ ≡ M′ ⟨ c′ ⟩ →
  c ≡ c′
cast-coercion-injective refl = refl


target-tag-cancellation-proofᵀ : TargetTagCancellationᵀ
target-tag-cancellation-proofᵀ
    {p = ν safe-old occ-old inner-index}
    exclusive unique gH (Value.Λ vBody) (no•-Λ noBody) vW
    (Λ⊑ᵀ .occ-old liftρ lift-left-ctx-[] vBody′ inner)
    (ν safe-new occ-new requested-inner)
    with target-tag-cancellation-proofᵀ
      (source-name-exclusive-source-only-head exclusive)
      (assumption-membership-unique-source unique)
      gH vBody noBody vW inner requested-inner
target-tag-cancellation-proofᵀ
    {p = ν safe-old occ-old inner-index}
    exclusive unique gH (Value.Λ vBody) (no•-Λ noBody) vW
    (Λ⊑ᵀ .occ-old liftρ lift-left-ctx-[] vBody′ inner)
    (ν safe-new occ-new requested-inner)
    | observed-eq , canceled =
  observed-eq ,
  Λ⊑ᵀ {{safe = safe-new}} occ-new
    liftρ lift-left-ctx-[] vBody canceled
target-tag-cancellation-proofᵀ exclusive unique gH
    (Value.Λ vBody) (no•-Λ noBody) vW
    (target-instantiationᵀ embedded)
    requested =
  ⊥-elim
    (genSafeShape-atomic-impossible
      (embedded-creation-target-shapeᴱ embedded) T.★)
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (cast⊒⊑ᵀ {p = inner-index} mode seal★ c⊒
      inner outer-index c-shape comp)
    requested
    with source-inert-narrowing-route exclusive inert c⊒
      inner-index outer-index requested gH
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (cast⊒⊑ᵀ {p = inner-index} mode seal★ c⊒
      inner outer-index c-shape comp)
    requested | function-index , refl
    with target-tag-cancellation-proofᵀ exclusive unique
      T.★⇒★ vM noM vW inner function-index
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (cast⊒⊑ᵀ {p = inner-index} mode seal★ c⊒
      inner outer-index c-shape comp)
    requested | function-index , refl
    | observed-eq , canceled =
  observed-eq ,
  cast⊒⊑ᵀ mode seal★ c⊒ canceled requested c-shape
    (source-index-composition-target-untag-function
      unique outer-index requested inner-index function-index comp)
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (cast⊑⊑ᵀ {p = inner-index} mode seal★ c⊑
      inner outer-index c-shape comp)
    requested
    with source-inert-widening-route inert c⊑
      inner-index requested gH
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (cast⊑⊑ᵀ {p = inner-index} mode seal★ c⊑
      inner outer-index c-shape comp)
    requested | function-index , refl
    with target-tag-cancellation-proofᵀ exclusive unique
      T.★⇒★ vM noM vW inner function-index
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (cast⊑⊑ᵀ {p = inner-index} mode seal★ c⊑
      inner outer-index c-shape comp)
    requested | function-index , refl
    | observed-eq , canceled =
  observed-eq ,
  cast⊑⊑ᵀ mode seal★ c⊑ canceled requested c-shape
    (source-cast-index-compatible-target-untag-function
      unique inner-index function-index outer-index requested
      c-shape comp)
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (conv↑⊑ᵀ {p = inner-index} reveal inner outer-index replacement)
    requested
    with source-inert-reveal-route inert reveal
      inner-index requested gH
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (conv↑⊑ᵀ {p = inner-index} reveal inner outer-index replacement)
    requested | function-index , refl
    with target-tag-cancellation-proofᵀ exclusive unique
      T.★⇒★ vM noM vW inner function-index
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (conv↑⊑ᵀ {p = inner-index} reveal inner outer-index replacement)
    requested | function-index , refl
    | observed-eq , canceled =
  observed-eq ,
  conv↑⊑ᵀ reveal canceled requested
    (source-replacement-target-untag-function
      unique inner-index function-index outer-index requested replacement)
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (conv↓⊑ᵀ {p = inner-index} conceal inner outer-index replacement)
    requested
    with source-inert-conceal-route exclusive inert conceal
      inner-index outer-index requested gH
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (conv↓⊑ᵀ {p = inner-index} conceal inner outer-index replacement)
    requested | function-index , refl
    with target-tag-cancellation-proofᵀ exclusive unique
      T.★⇒★ vM noM vW inner function-index
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (conv↓⊑ᵀ {p = inner-index} conceal inner outer-index replacement)
    requested | function-index , refl
    | observed-eq , canceled =
  observed-eq ,
  conv↓⊑ᵀ conceal canceled requested
    (source-replacement-target-untag-function
      unique outer-index requested inner-index function-index replacement)
target-tag-cancellation-proofᵀ exclusive unique gH vV noV vW
    (⊑cast⊒ᵀ mode seal★
      (C.cast-tag hG gG ok , NW.cross ()) inner old-index
      c-shape comp)
    requested
target-tag-cancellation-proofᵀ exclusive unique gH vV noV vW
    (⊑cast⊑ᵀ {p = inner-index} mode seal★
      (C.cast-tag hG gG ok , NW.tag gG′) inner old-index
      c-shape comp)
    requested
    with target-ground-unique exclusive old-index
      inner-index requested gG gH
target-tag-cancellation-proofᵀ exclusive unique gH vV noV vW
    (⊑cast⊑ᵀ {p = inner-index} mode seal★
      (C.cast-tag hG gG ok , NW.tag gG′) inner old-index
      c-shape comp)
    requested | refl
    with assumption-membership-unique→precision-index-unique unique
      inner-index requested
target-tag-cancellation-proofᵀ exclusive unique gH vV noV vW
    (⊑cast⊑ᵀ {p = inner-index} mode seal★
      (C.cast-tag hG gG ok , NW.tag gG′) inner old-index
      c-shape comp)
    requested | refl | refl =
  refl , inner
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (paired-revealᵀ corr reveal () transport inner)
    requested
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (paired-concealᵀ corr conceal () transport inner)
    requested
target-tag-cancellation-proofᵀ {p = outer-index}
    exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (paired-wideningᵀ {p = inner-index}
      mode seal★ c⊑ c-shape
      mode′ seal★′
      (C.cast-tag hG gG ok , NW.tag gG′) c′-shape
      left-square right-square compat inner)
    requested
    with source-inert-widening-ground-route inert c⊑
      inner-index gG requested gH
target-tag-cancellation-proofᵀ {p = outer-index}
    exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (paired-wideningᵀ {p = inner-index}
      mode seal★ c⊑ c-shape
      mode′ seal★′
      (C.cast-tag hG gG ok , NW.tag gG′) c′-shape
      left-square right-square compat inner)
    requested | refl , refl
    with c′-shape
target-tag-cancellation-proofᵀ {p = outer-index}
    exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (paired-wideningᵀ {p = inner-index}
      mode seal★ c⊑ c-shape
      mode′ seal★′
      (C.cast-tag hG gG ok , NW.tag gG′) c′-shape
      left-square right-square compat inner)
    requested | refl , refl | shape-tag-fun =
  refl ,
  cast⊑⊑ᵀ mode seal★ c⊑ inner requested c-shape
    (paired-source-cast-index-compatible-target-untag-function
      unique inner-index outer-index requested c-shape
      left-square right-square)
target-tag-cancellation-proofᵀ exclusive unique gH
    (vN ⟨ inert ⟩) (no•-⟨⟩ noN) vW
    (closeᵀ quotient
      (quotient-id-widening u⊑
        (C.cast-tag hG gG ok , NW.tag gG′))
      outer-index u-shape target-shape square compatible)
    requested
    with quotient-close-target-tag-ground-route
      exclusive inert u⊑ outer-index requested gG gH compatible
target-tag-cancellation-proofᵀ exclusive unique gH
    (vN ⟨ inert ⟩) (no•-⟨⟩ noN) vW
    (closeᵀ quotient
      (quotient-id-widening u⊑
        (C.cast-tag hG gG ok , NW.tag gG′))
      outer-index u-shape target-shape square compatible)
    requested | refl , refl
    with target-function-ground-value-quotient-eliminationᵀ
      vN vW quotient
target-tag-cancellation-proofᵀ exclusive unique gH
    (vN ⟨ inert ⟩) (no•-⟨⟩ noN) vW
    (closeᵀ quotient
      (quotient-id-widening u⊑
        (C.cast-tag hG gG ok , NW.tag gG′))
      outer-index u-shape target-shape square compatible)
    requested | refl , refl | ordinary-index , ordinary
    with target-shape
target-tag-cancellation-proofᵀ exclusive unique gH
    (vN ⟨ inert ⟩) (no•-⟨⟩ noN) vW
    (closeᵀ quotient
      (quotient-id-widening u⊑
        (C.cast-tag hG gG ok , NW.tag gG′))
      outer-index u-shape target-shape square compatible)
    requested | refl , refl | ordinary-index , ordinary
    | shape-tag-fun =
  refl ,
  cast⊑⊑ᵀ cast-tag-or-id seal★-tag-or-id
    (NW.widen-mode-relax C.id-only≤tag-or-idᵈ u⊑)
    ordinary requested u-shape
    (quotient-function-tag-right-composition
      unique outer-index requested _ ordinary-index square)
target-tag-cancellation-proofᵀ exclusive unique gH
    (vN ⟨ inert ⟩) (no•-⟨⟩ noN) vW
    (closeᵀ quotient
      (quotient-cast-widening
        mode seal★ u⊑ mode′ seal★′
        (C.cast-tag hG gG ok , NW.tag gG′))
      outer-index u-shape target-shape square compatible)
    requested
    with quotient-close-target-tag-ground-route
      exclusive inert u⊑ outer-index requested gG gH compatible
target-tag-cancellation-proofᵀ exclusive unique gH
    (vN ⟨ inert ⟩) (no•-⟨⟩ noN) vW
    (closeᵀ quotient
      (quotient-cast-widening
        mode seal★ u⊑ mode′ seal★′
        (C.cast-tag hG gG ok , NW.tag gG′))
      outer-index u-shape target-shape square compatible)
    requested | refl , refl
    with target-function-ground-value-quotient-eliminationᵀ
      vN vW quotient
target-tag-cancellation-proofᵀ exclusive unique gH
    (vN ⟨ inert ⟩) (no•-⟨⟩ noN) vW
    (closeᵀ quotient
      (quotient-cast-widening
        mode seal★ u⊑ mode′ seal★′
        (C.cast-tag hG gG ok , NW.tag gG′))
      outer-index u-shape target-shape square compatible)
    requested | refl , refl | ordinary-index , ordinary
    with target-shape
target-tag-cancellation-proofᵀ exclusive unique gH
    (vN ⟨ inert ⟩) (no•-⟨⟩ noN) vW
    (closeᵀ quotient
      (quotient-cast-widening
        mode seal★ u⊑ mode′ seal★′
        (C.cast-tag hG gG ok , NW.tag gG′))
      outer-index u-shape target-shape square compatible)
    requested | refl , refl | ordinary-index , ordinary
    | shape-tag-fun =
  refl ,
  cast⊑⊑ᵀ mode seal★ u⊑ ordinary requested u-shape
    (quotient-function-tag-right-composition
      unique outer-index requested _ ordinary-index square)
target-tag-cancellation-proofᵀ exclusive unique gH vV noV vW
    (allocation-prefixᵀ prefix inner V⊢ Wtag⊢) requested
    with target-tag-cancellation-proofᵀ exclusive unique
      gH vV noV vW inner requested
target-tag-cancellation-proofᵀ exclusive unique gH vV noV vW
    (allocation-prefixᵀ prefix inner V⊢ Wtag⊢) requested
    | refl , canceled =
  refl ,
  allocation-prefixᵀ prefix canceled V⊢
    (target-tag-typing⁻¹ Wtag⊢)
target-tag-cancellation-proofᵀ exclusive unique gH vV noV vW
    (⊑cast⊑ᵀ {p = inner-index} mode seal★
      (C.cast-tag hG gG ok , NW.tag gG′) inner old-index
      c-shape comp)
    requested
    with target-ground-unique exclusive old-index
      inner-index requested gG gH
target-tag-cancellation-proofᵀ exclusive unique gH vV noV vW
    (⊑cast⊑ᵀ {p = inner-index} mode seal★
      (C.cast-tag hG gG ok , NW.tag gG′) inner old-index
      c-shape comp)
    requested | refl
    with assumption-membership-unique→precision-index-unique unique
      inner-index requested
target-tag-cancellation-proofᵀ exclusive unique gH vV noV vW
    (⊑cast⊑ᵀ {p = inner-index} mode seal★
      (C.cast-tag hG gG ok , NW.tag gG′) inner old-index
      c-shape comp)
    requested | refl | refl =
  refl , inner
