module proof.NuImprecisionWorldCoherentQuotientClassificationProof where

-- File Charter:
--   * Proves coherent classification of one terminal quotient down-up node.
--   * Refines the exhaustive quotient-value classifier with explicit
--     world-coherent packaging for store-neutral non-inst outcomes.
--   * Preserves the unique outer-inst residual with its reduction trace,
--     source value evidence, and no-runtime-bullet evidence.

import Coercions as C
import NarrowWiden as NW
import NuTerms as NT
import Types as T

open import Coercions using (_!; _？; _︔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; _×_; proj₁; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( bind
  ; blame-⟨⟩
  ; keep
  ; pure-step
  ; β-id
  ; β-inst
  ; β-seq
  ; seal-unseal
  ; tag-untag-bad
  ; tag-untag-ok
  ; ξ-⟨⟩
  ; _—→_
  ; _—→[_]_
  ; _—↠[_]_
  ; ↠-refl
  ; ↠-step
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; seal★-tag-or-id)
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; blame
  ; no•-⟨⟩
  ; _•
  ; _⟨_⟩
  )
open import QuotientedTermImprecision
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary using (no; yes)
open import TermTyping using (cast-gen; cast-tag-or-id; forget)
open import Types using (★)
open import proof.CastImprecision using
  ( strictCrossNarrowing⇒crossNarrowing
  ; strictCrossWidening⇒crossWidening
  )
open import proof.CoercionProperties using (inert-dec)
open import proof.ForallPermutationProperties using
  (⊑ᵖ-arrow-left-shape)
open import proof.NuImprecisionQuotientValue using
  ( active-double-cast-step
  ; outer-inst-allocation-trace
  ; source-inert-quotient-down-before-id-widening-impossible
  ; source-inert-quotient-down-var-impossible
  ; source-quotient-down-seal-impossible
  ; source-quotient-down-seal-tail-impossible
  ; source-quotient-down-tag-impossible
  ; source-quotient-down-unseal-impossible
  ; strict-cross-narrowing-ground-target-arrow
  ; strict-cross-widening-ground-star
  ; strict-cross-widening-inert
  ; target-inert-after-source-untag-impossible
  ; target-inert-after-source-untag-sequence-impossible
  ; target-inert-quotient-down-after-source-id-impossible
  ; left-catchup-indexed-double-cast-blameᵀ
  ; left-catchup-indexed-final-quotient-inertᵀ
  ; left-catchup-indexed-one-keep-valueᵀ
  ; left-catchup-indexed-two-keep-to-blameᵀ
  ; star-imprecision-target
  ; star-term-imprecision-target
  )
open import proof.NuImprecisionWorldCoherenceDef using (WorldCoherent)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherentQuotientClassificationDef using
  (WorldCoherentQuotientClassificationᵀ)
open import proof.NuImprecisionWorldCoherentResultDef using
  ( WorldCoherentLeftCatchupIndexedResult
  ; world-coherent-left-indexed-catchup
  )
open import proof.NuPreservation using (value-no-step)


world-coherent-quotient-outer-pureᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ L d d′ u u′}
    {D D′ A A′ : T.Ty}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  ((V ⟨ d ⟩) ⟨ u ⟩) —→ L →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  C.Inert d′ →
  C.Inert u′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ (V ⟨ d ⟩) ⊑ (V′ ⟨ d′ ⟩)
    ⦂ D ⊑ᵖ D′ ∶ qD →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  WorldCoherentLeftCatchupIndexedResult
      {N = (V ⟨ d ⟩) ⟨ u ⟩}
      {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
      {ρ = ρ} pA
  ⊎ ∃[ B ] ∃[ s ]
      (u ≡ C.inst B s) ×
      (((V ⟨ d ⟩) ⟨ u ⟩)
        —↠[ keep ∷ bind ★ ∷ [] ]
          ((NT.⇑ᵗᵐ (V ⟨ d ⟩)) •) ⟨ s ⟩) ×
      Value (V ⟨ d ⟩) × No• (V ⟨ d ⟩)
world-coherent-quotient-outer-pureᵀ
    coherent exclusive wfL (β-id vW) vV noV vV′ noV′
    inert-d′ inert-u′ down (quotient-id-widening u⊑ u′⊑) pA =
  inj₁ (⊥-elim
    (source-inert-quotient-down-before-id-widening-impossible
      vW down u⊑))
world-coherent-quotient-outer-pureᵀ
    coherent exclusive wfL (β-id vW) vV noV vV′ noV′
    inert-d′ inert-u′ down
    (quotient-cast-widening mode seal★ u⊑ mode′ seal★′ u′⊑) pA =
  inj₁ (⊥-elim
    (source-inert-quotient-down-before-id-widening-impossible
      vW down u⊑))
world-coherent-quotient-outer-pureᵀ
    coherent exclusive wfL (β-seq vW) vV noV vV′ noV′
    inert-d′ inert-u′ down
    (quotient-id-widening
      (C.cast-seq s⊢ (C.cast-tag hG gG⊢ ok) ,
        sʷ NW.︔ gG !)
      u′⊑)
    pA =
  inj₁
    (world-coherent-left-indexed-catchup
      (left-catchup-indexed-one-keep-valueᵀ
        (pure-step (β-seq vW))
        (vW ⟨ strict-cross-widening-inert sʷ ⟩ ⟨ _ ! ⟩)
        (no•-⟨⟩ (no•-⟨⟩ (no•-⟨⟩ noV))) final-relation)
      coherent
      exclusive
      wfL)
  where
  s⊑ =
    s⊢ , NW.cross (strictCrossWidening⇒crossWidening sʷ)
  G⊑★ = strict-cross-widening-ground-star gG sʷ s⊑
  G⊑A′ =
    subst (λ X → _ ∣ _ ⊢ _ ⊑ X ⊣ _)
      (sym (star-imprecision-target pA)) G⊑★
  split-relation =
    up⊑upᵀ down (quotient-id-widening s⊑ u′⊑) G⊑A′
  tag⊑ =
    NW.widen-mode-relax C.id-only≤tag-or-idᵈ
      (C.cast-tag hG gG⊢ ok , NW.tag gG)
  final-relation =
    cast⊑⊑ᵀ cast-tag-or-id seal★-tag-or-id tag⊑
      split-relation pA
world-coherent-quotient-outer-pureᵀ
    coherent exclusive wfL (β-seq vW) vV noV vV′ noV′
    inert-d′ inert-u′ down
    (quotient-id-widening
      (C.cast-seq (C.cast-unseal hA α∈Σ ok) t⊢ ,
        NW.unseal︔_ α tʷ)
      u′⊑)
    pA =
  inj₁ (⊥-elim
    (source-inert-quotient-down-var-impossible vW down))
world-coherent-quotient-outer-pureᵀ
    coherent exclusive wfL (β-seq vW) vV noV vV′ noV′
    inert-d′ inert-u′ down
    (quotient-cast-widening
      mode seal★
      (C.cast-seq s⊢ (C.cast-tag hG gG⊢ ok) ,
        sʷ NW.︔ gG !)
      mode′ seal★′ u′⊑)
    pA =
  inj₁
    (world-coherent-left-indexed-catchup
      (left-catchup-indexed-one-keep-valueᵀ
        (pure-step (β-seq vW))
        (vW ⟨ strict-cross-widening-inert sʷ ⟩ ⟨ _ ! ⟩)
        (no•-⟨⟩ (no•-⟨⟩ (no•-⟨⟩ noV))) final-relation)
      coherent
      exclusive
      wfL)
  where
  s⊑ =
    s⊢ , NW.cross (strictCrossWidening⇒crossWidening sʷ)
  G⊑★ = strict-cross-widening-ground-star gG sʷ s⊑
  G⊑A′ =
    subst (λ X → _ ∣ _ ⊢ _ ⊑ X ⊣ _)
      (sym (star-imprecision-target pA)) G⊑★
  split-relation =
    up⊑upᵀ down
      (quotient-cast-widening
        mode seal★ s⊑ mode′ seal★′ u′⊑)
      G⊑A′
  tag⊑ = C.cast-tag hG gG⊢ ok , NW.tag gG
  final-relation =
    cast⊑⊑ᵀ mode seal★ tag⊑ split-relation pA
world-coherent-quotient-outer-pureᵀ
    coherent exclusive wfL (β-seq vW) vV noV vV′ noV′
    inert-d′ inert-u′ down
    (quotient-cast-widening
      mode seal★
      (C.cast-seq (C.cast-unseal hA α∈Σ ok) t⊢ ,
        NW.unseal︔_ α tʷ)
      mode′ seal★′ u′⊑)
    pA =
  inj₁ (⊥-elim
    (source-inert-quotient-down-var-impossible vW down))
world-coherent-quotient-outer-pureᵀ
    coherent exclusive wfL (β-inst vW) vV noV vV′ noV′
    inert-d′ inert-u′ down
    (quotient-id-widening
      (C.cast-inst hB occ s⊢ , NW.inst sʷ)
      u′⊑)
    pA =
  inj₂
    (_ , _ , refl , outer-inst-allocation-trace noV vW ,
      vW , no•-⟨⟩ noV)
world-coherent-quotient-outer-pureᵀ
    coherent exclusive wfL (β-inst vW) vV noV vV′ noV′
    inert-d′ inert-u′ down
    (quotient-cast-widening mode seal★
      (C.cast-inst hB occ s⊢ , NW.inst sʷ)
      mode′ seal★′ u′⊑)
    pA =
  inj₂
    (_ , _ , refl , outer-inst-allocation-trace noV vW ,
      vW , no•-⟨⟩ noV)
world-coherent-quotient-outer-pureᵀ
    coherent exclusive wfL (tag-untag-ok vW) vV noV vV′ noV′
    inert-d′ inert-u′ down
    (quotient-id-widening u⊑ u′⊑) pA =
  inj₁ (⊥-elim (source-quotient-down-tag-impossible down))
world-coherent-quotient-outer-pureᵀ
    coherent exclusive wfL (tag-untag-ok vW) vV noV vV′ noV′
    inert-d′ inert-u′ down
    (quotient-cast-widening mode seal★ u⊑ mode′ seal★′ u′⊑) pA =
  inj₁ (⊥-elim (source-quotient-down-tag-impossible down))
world-coherent-quotient-outer-pureᵀ
    coherent exclusive wfL (tag-untag-bad vW G≢H) vV noV vV′ noV′
    inert-d′ inert-u′ down
    (quotient-id-widening u⊑ u′⊑) pA =
  inj₁ (⊥-elim (source-quotient-down-tag-impossible down))
world-coherent-quotient-outer-pureᵀ
    coherent exclusive wfL (tag-untag-bad vW G≢H) vV noV vV′ noV′
    inert-d′ inert-u′ down
    (quotient-cast-widening mode seal★ u⊑ mode′ seal★′ u′⊑) pA =
  inj₁ (⊥-elim (source-quotient-down-tag-impossible down))
world-coherent-quotient-outer-pureᵀ
    coherent exclusive wfL (seal-unseal vW) vV noV vV′ noV′
    inert-d′ inert-u′ down
    (quotient-id-widening u⊑ u′⊑) pA =
  inj₁ (⊥-elim (source-quotient-down-seal-impossible down))
world-coherent-quotient-outer-pureᵀ
    coherent exclusive wfL (seal-unseal vW) vV noV vV′ noV′
    inert-d′ inert-u′ down
    (quotient-cast-widening mode seal★ u⊑ mode′ seal★′ u′⊑) pA =
  inj₁ (⊥-elim (source-quotient-down-seal-impossible down))

world-coherent-quotient-inner-stepᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ L d d′ u u′}
    {D D′ A A′ : T.Ty}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  (V ⟨ d ⟩) —→[ keep ] L →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  C.Inert d′ →
  C.Inert u′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ (V ⟨ d ⟩) ⊑ (V′ ⟨ d′ ⟩)
    ⦂ D ⊑ᵖ D′ ∶ qD →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  WorldCoherentLeftCatchupIndexedResult
    {N = (V ⟨ d ⟩) ⟨ u ⟩}
    {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ} pA
world-coherent-quotient-inner-stepᵀ
    coherent exclusive wfL (pure-step (β-id vW)) vV noV vV′ noV′
    inert-d′ inert-u′ down widening pA =
  ⊥-elim
    (target-inert-quotient-down-after-source-id-impossible
      inert-d′ down)
world-coherent-quotient-inner-stepᵀ
    coherent exclusive wfL (pure-step (β-seq vW)) vV noV vV′ noV′
    inert-d′ inert-u′ down@(down⊑downᵀ
      (C.cast-seq s⊢ t⊢ , gG NW.？︔ gⁿ)
      d′⋒ V⊑V′ qD)
    widening pA =
  ⊥-elim
    (target-inert-after-source-untag-sequence-impossible
      inert-d′ down)
world-coherent-quotient-inner-stepᵀ
    coherent exclusive wfL (pure-step (β-seq vW)) vV noV vV′ noV′
    inert-d′ inert-u′ down@(down⊑downᵀ
      (C.cast-seq s⊢ (C.cast-seal hX α∈Σ ok) ,
        nⁿ NW.︔seal α)
      d′⋒ V⊑V′ qD)
    widening pA =
  ⊥-elim (source-quotient-down-seal-tail-impossible down)
world-coherent-quotient-inner-stepᵀ
    coherent exclusive wfL (pure-step (β-seq vW)) vV noV vV′ noV′
    inert-d′ inert-u′ down@(gen-down⊑gen-downᵀ
      (C.cast-seq s⊢ t⊢ , gG NW.？︔ gⁿ)
      d′⋒ V⊑V′ qD)
    widening pA =
  ⊥-elim
    (target-inert-after-source-untag-sequence-impossible
      inert-d′ down)
world-coherent-quotient-inner-stepᵀ
    coherent exclusive wfL (pure-step (β-seq vW)) vV noV vV′ noV′
    inert-d′ inert-u′ down@(gen-down⊑gen-downᵀ
      (C.cast-seq s⊢ (C.cast-seal hX α∈Σ ok) ,
        nⁿ NW.︔seal α)
      d′⋒ V⊑V′ qD)
    widening pA =
  ⊥-elim (source-quotient-down-seal-tail-impossible down)
world-coherent-quotient-inner-stepᵀ
    coherent exclusive wfL (pure-step (β-inst vW)) vV noV vV′ noV′
    inert-d′ inert-u′
    (down⊑downᵀ (d⊢ , NW.cross ()) d′⊒ V⊑V′ qD)
    widening pA
world-coherent-quotient-inner-stepᵀ
    coherent exclusive wfL (pure-step (β-inst vW)) vV noV vV′ noV′
    inert-d′ inert-u′
    (gen-down⊑gen-downᵀ (d⊢ , NW.cross ()) d′⊒ V⊑V′ qD)
    widening pA
world-coherent-quotient-inner-stepᵀ
    coherent exclusive wfL (pure-step (tag-untag-ok vW))
    vV noV vV′ noV′ inert-d′ inert-u′ down widening pA =
  ⊥-elim (target-inert-after-source-untag-impossible inert-d′ down)
world-coherent-quotient-inner-stepᵀ
    coherent exclusive wfL (pure-step (tag-untag-bad vW G≢H))
    vV noV vV′ noV′ inert-d′ inert-u′ down widening pA =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-two-keep-to-blameᵀ
      (↠-step (ξ-⟨⟩ (pure-step (tag-untag-bad vW G≢H)))
        (↠-step (pure-step blame-⟨⟩) ↠-refl))
      (nu-term-imprecision-target-typing
        (up⊑upᵀ down widening pA)))
    coherent
    exclusive
    wfL
world-coherent-quotient-inner-stepᵀ
    coherent exclusive wfL (pure-step (seal-unseal vW))
    vV noV vV′ noV′ inert-d′ inert-u′ down widening pA =
  ⊥-elim (source-quotient-down-unseal-impossible down)
world-coherent-quotient-inner-stepᵀ
    coherent exclusive wfL (pure-step blame-⟨⟩) () noV vV′ noV′
    inert-d′ inert-u′ down widening pA
world-coherent-quotient-inner-stepᵀ
    coherent exclusive wfL (ξ-⟨⟩ V→) vV noV vV′ noV′
    inert-d′ inert-u′ down widening pA =
  ⊥-elim (value-no-step vV V→)

world-coherent-quotient-after-source-stepᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ L d d′ u u′}
    {D D′ A A′ : T.Ty}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  C.Inert d′ →
  C.Inert u′ →
  ((V ⟨ d ⟩) ⟨ u ⟩) —→[ keep ] L →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ V ⟨ d ⟩ ⊑ V′ ⟨ d′ ⟩
    ⦂ D ⊑ᵖ D′ ∶ qD →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  WorldCoherentLeftCatchupIndexedResult
      {N = (V ⟨ d ⟩) ⟨ u ⟩}
      {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
      {ρ = ρ} pA
  ⊎ ∃[ B ] ∃[ s ]
      (u ≡ C.inst B s) ×
      (((V ⟨ d ⟩) ⟨ u ⟩)
        —↠[ keep ∷ bind ★ ∷ [] ]
          ((NT.⇑ᵗᵐ (V ⟨ d ⟩)) •) ⟨ s ⟩) ×
      Value (V ⟨ d ⟩) × No• (V ⟨ d ⟩)
world-coherent-quotient-after-source-stepᵀ
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    (pure-step source→) down widening pA =
  world-coherent-quotient-outer-pureᵀ {pA = pA}
    coherent exclusive wfL source→ vV noV vV′ noV′
    inert-d′ inert-u′ down widening pA
world-coherent-quotient-after-source-stepᵀ
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    (ξ-⟨⟩ source→) down widening pA =
  inj₁
    (world-coherent-quotient-inner-stepᵀ {pA = pA}
      coherent exclusive wfL source→ vV noV vV′ noV′
      inert-d′ inert-u′ down widening pA)

world-coherent-quotient-activeᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ d d′ u u′}
    {D D′ A A′ : T.Ty}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  C.Inert d′ →
  C.Inert u′ →
  (C.Inert d × C.Inert u → ⊥) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ V ⟨ d ⟩ ⊑ V′ ⟨ d′ ⟩
    ⦂ D ⊑ᵖ D′ ∶ qD →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  WorldCoherentLeftCatchupIndexedResult
      {N = (V ⟨ d ⟩) ⟨ u ⟩}
      {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
      {ρ = ρ} pA
  ⊎ ∃[ B ] ∃[ s ]
      (u ≡ C.inst B s) ×
      (((V ⟨ d ⟩) ⟨ u ⟩)
        —↠[ keep ∷ bind ★ ∷ [] ]
          ((NT.⇑ᵗᵐ (V ⟨ d ⟩)) •) ⟨ s ⟩) ×
      Value (V ⟨ d ⟩) × No• (V ⟨ d ⟩)
world-coherent-quotient-activeᵀ
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    source-active
    down@(down⊑downᵀ d⊒ d′⊒ V⊑V′ qD)
    widening@(quotient-id-widening u⊑ u′⊑) pA
    with active-double-cast-step vV noV
      (forget (nu-term-imprecision-source-typing V⊑V′))
      (proj₁ d⊒) (proj₁ u⊑) source-active
world-coherent-quotient-activeᵀ
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    source-active
    down@(down⊑downᵀ d⊒ d′⊒ V⊑V′ qD)
    widening@(quotient-id-widening u⊑ u′⊑) pA
    | L , source→ =
  world-coherent-quotient-after-source-stepᵀ {pA = pA}
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    source→ down widening pA
world-coherent-quotient-activeᵀ
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    source-active
    down@(down⊑downᵀ d⊒ d′⊒ V⊑V′ qD)
    widening@(quotient-cast-widening
      mode seal★ u⊑ mode′ seal★′ u′⊑) pA
    with active-double-cast-step vV noV
      (forget (nu-term-imprecision-source-typing V⊑V′))
      (proj₁ d⊒) (proj₁ u⊑) source-active
world-coherent-quotient-activeᵀ
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    source-active
    down@(down⊑downᵀ d⊒ d′⊒ V⊑V′ qD)
    widening@(quotient-cast-widening
      mode seal★ u⊑ mode′ seal★′ u′⊑) pA
    | L , source→ =
  world-coherent-quotient-after-source-stepᵀ {pA = pA}
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    source→ down widening pA
world-coherent-quotient-activeᵀ
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    source-active
    down@(gen-down⊑gen-downᵀ d⊒ d′⊒ V⊑V′ qD)
    widening@(quotient-id-widening u⊑ u′⊑) pA
    with active-double-cast-step vV noV
      (forget (nu-term-imprecision-source-typing V⊑V′))
      (proj₁ d⊒) (proj₁ u⊑) source-active
world-coherent-quotient-activeᵀ
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    source-active
    down@(gen-down⊑gen-downᵀ d⊒ d′⊒ V⊑V′ qD)
    widening@(quotient-id-widening u⊑ u′⊑) pA
    | L , source→ =
  world-coherent-quotient-after-source-stepᵀ {pA = pA}
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    source→ down widening pA
world-coherent-quotient-activeᵀ
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    source-active
    down@(gen-down⊑gen-downᵀ d⊒ d′⊒ V⊑V′ qD)
    widening@(quotient-cast-widening
      mode seal★ u⊑ mode′ seal★′ u′⊑) pA
    with active-double-cast-step vV noV
      (forget (nu-term-imprecision-source-typing V⊑V′))
      (proj₁ d⊒) (proj₁ u⊑) source-active
world-coherent-quotient-activeᵀ
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    source-active
    down@(gen-down⊑gen-downᵀ d⊒ d′⊒ V⊑V′ qD)
    widening@(quotient-cast-widening
      mode seal★ u⊑ mode′ seal★′ u′⊑) pA
    | L , source→ =
  world-coherent-quotient-after-source-stepᵀ {pA = pA}
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    source→ down widening pA

world-coherent-quotient-valueᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ d d′ u u′}
    {D D′ A A′ : T.Ty}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  C.Inert d′ →
  C.Inert u′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ V ⟨ d ⟩ ⊑ V′ ⟨ d′ ⟩
    ⦂ D ⊑ᵖ D′ ∶ qD →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  WorldCoherentLeftCatchupIndexedResult
      {N = (V ⟨ d ⟩) ⟨ u ⟩}
      {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
      {ρ = ρ} pA
  ⊎ ∃[ B ] ∃[ s ]
      (u ≡ C.inst B s) ×
      (((V ⟨ d ⟩) ⟨ u ⟩)
        —↠[ keep ∷ bind ★ ∷ [] ]
          ((NT.⇑ᵗᵐ (V ⟨ d ⟩)) •) ⟨ s ⟩) ×
      Value (V ⟨ d ⟩) × No• (V ⟨ d ⟩)
world-coherent-quotient-valueᵀ
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA
    with inert-dec _ | inert-dec _
world-coherent-quotient-valueᵀ
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA
    | yes inert-d | yes inert-u =
  inj₁
    (world-coherent-left-indexed-catchup
      (left-catchup-indexed-final-quotient-inertᵀ
        vV noV inert-d inert-u (up⊑upᵀ down widening pA))
      coherent
      exclusive
      wfL)
world-coherent-quotient-valueᵀ
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA
    | yes inert-d | no not-inert-u =
  world-coherent-quotient-activeᵀ {pA = pA}
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    (λ { (source-d , source-u) → not-inert-u source-u })
    down widening pA
world-coherent-quotient-valueᵀ
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA
    | no not-inert-d | yes inert-u =
  world-coherent-quotient-activeᵀ {pA = pA}
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    (λ { (source-d , source-u) → not-inert-d source-d })
    down widening pA
world-coherent-quotient-valueᵀ
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA
    | no not-inert-d | no not-inert-u =
  world-coherent-quotient-activeᵀ {pA = pA}
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    (λ { (source-d , source-u) → not-inert-d source-d })
    down widening pA

world-coherent-quotient-classification-proofᵀ :
  WorldCoherentQuotientClassificationᵀ
world-coherent-quotient-classification-proofᵀ {pA = pA}
    coherent exclusive wfL vV′ noV′ inert-d′ inert-u′
    down widening (inj₁ (vV , noV)) =
  world-coherent-quotient-valueᵀ {pA = pA}
    coherent exclusive wfL vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA
world-coherent-quotient-classification-proofᵀ {pA = pA}
    coherent exclusive wfL vV′ noV′ inert-d′ inert-u′
    down widening (inj₂ refl) =
  inj₁
    (world-coherent-left-indexed-catchup
      (left-catchup-indexed-double-cast-blameᵀ
        (nu-term-imprecision-target-typing
          (up⊑upᵀ down widening pA)))
      coherent
      exclusive
      wfL)
