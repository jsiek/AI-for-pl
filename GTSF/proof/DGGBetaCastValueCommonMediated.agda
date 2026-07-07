module proof.DGGBetaCastValueCommonMediated where

-- File Charter:
--   * Shared lemmas for the mediated beta-cast value proof.
--   * Contains target-cast shape contradictions and generic source-cast tail
--     wrappers used by `proof.DGGBetaCastValueMediated`.
--   * Split out to keep the value proof module smaller and cheaper to check.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Types
open import Coercions
open import NarrowWiden using
  ( cross
  ; id-＇
  ; id-‵
  ; id★
  ; sealⁿ
  ; untag
  ; _︔seal_
  ; _？︔_
  ; _∣_∣_⊢_∶_⊒_
  )
  renaming (`∀ to `∀ⁿʷ; gen to genⁿʷ)
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import Mediation
open import MediatedNarrowing
open import proof.CatchupSeparated using
  ( applyLeftChanges
  ; leftStore-applyLeftChanges
  )
open import proof.MediationProperties using
  ( left-changes-transportᵐ
  ; applyModeEnvs
  ; left-changes-narrowingˡ
  ; narrowing-dual¹-applyCoercions
  )
open import proof.ReductionProperties using
  ( applyCoercions
  ; applyTys
  ; applyTyCtxs
  )

inner-seq-index-impossible :
  ∀ {μ ΔL ΔR ρ q₁ q₂ AL BL AR BR} →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ q₁ ︔ q₂ ∶ (AL ⇒ BL) ⊒ᵐ (AR ⇒ BR) →
  ⊥
inner-seq-index-impossible
  (_ , _ , _ , _ , med-⇒ _ _ , (cast-seq () _ , _ ？︔ _))
inner-seq-index-impossible
  (_ , _ , _ , _ , _ , (cast-seq _ () , _ ︔seal _))

plus-seq-cast-impossible :
  ∀ {η Δ Σ s₁ s₂ A B C M} →
  (e : η ∣ Δ ∣ Σ ⊢ s₁ ︔ s₂ ∶ (A ⇒ B) ⊒ C) →
  Value (M ⟨ narrowing-dual¹ e ⟩) →
  ⊥
plus-seq-cast-impossible (cast-seq () _ , _ ？︔ _)
plus-seq-cast-impossible (s⊢ , _︔seal_ sⁿ α) (vM ⟨ () ⟩)

dual-id-not-fun :
  ∀ {η Δ Σ X A B c d} →
  (e : η ∣ Δ ∣ Σ ⊢ id X ∶ A ⊒ B) →
  narrowing-dual¹ e ≡ c ↦ d →
  ⊥
dual-id-not-fun (_ , cross (id-＇ α)) ()
dual-id-not-fun (_ , cross (id-‵ ι)) ()
dual-id-not-fun (_ , id★) ()

dual-seq-not-fun :
  ∀ {η Δ Σ t₁ t₂ A B c d} →
  (e : η ∣ Δ ∣ Σ ⊢ t₁ ︔ t₂ ∶ A ⊒ B) →
  narrowing-dual¹ e ≡ c ↦ d →
  ⊥
dual-seq-not-fun (_ , (＇ α) ？︔ gⁿ) ()
dual-seq-not-fun (_ , (‵ ι) ？︔ gⁿ) ()
dual-seq-not-fun (_ , ★⇒★ ？︔ gⁿ) ()
dual-seq-not-fun (_ , sⁿ ︔seal α) ()

dual-all-not-fun :
  ∀ {η Δ Σ t A B c d} →
  (e : η ∣ Δ ∣ Σ ⊢ `∀ t ∶ A ⊒ B) →
  narrowing-dual¹ e ≡ c ↦ d →
  ⊥
dual-all-not-fun (_ , cross (`∀ⁿʷ tⁿ)) ()

dual-untag-not-fun :
  ∀ {η Δ Σ G A B c d} →
  (e : η ∣ Δ ∣ Σ ⊢ G ？ ∶ A ⊒ B) →
  narrowing-dual¹ e ≡ c ↦ d →
  ⊥
dual-untag-not-fun (_ , untag (＇ α)) ()
dual-untag-not-fun (_ , untag (‵ ι)) ()
dual-untag-not-fun (_ , untag ★⇒★) ()

dual-seal-not-fun :
  ∀ {η Δ Σ X α A B c d} →
  (e : η ∣ Δ ∣ Σ ⊢ seal X α ∶ A ⊒ B) →
  narrowing-dual¹ e ≡ c ↦ d →
  ⊥
dual-seal-not-fun (_ , sealⁿ X α) ()

dual-gen-not-fun :
  ∀ {η Δ Σ X t A B c d} →
  (e : η ∣ Δ ∣ Σ ⊢ gen X t ∶ A ⊒ B) →
  narrowing-dual¹ e ≡ c ↦ d →
  ⊥
dual-gen-not-fun (_ , genⁿʷ tⁿ) ()

tag-narrowing-impossible :
  ∀ {η Δ Σ G A B} →
  η ∣ Δ ∣ Σ ⊢ G ! ∶ A ⊒ B →
  ⊥
tag-narrowing-impossible (_ , cross ())

unseal-narrowing-impossible :
  ∀ {η Δ Σ α X A B} →
  η ∣ Δ ∣ Σ ⊢ unseal α X ∶ A ⊒ B →
  ⊥
unseal-narrowing-impossible (_ , cross ())

inst-narrowing-impossible :
  ∀ {η Δ Σ X t A B} →
  η ∣ Δ ∣ Σ ⊢ inst X t ∶ A ⊒ B →
  ⊥
inst-narrowing-impossible (_ , cross ())

------------------------------------------------------------------------
-- Generic source-cast tails
------------------------------------------------------------------------

mediated-beta-cast-plus-tail :
  ∀ χs {ΔL ΔR ρ ΔL′ ρ′ N Target qᵢ q dₛ Bₒ BL BR μO ηC} →
  ΔL′ ≡ applyTyCtxs χs ΔL →
  ρ′ ≡ applyLeftChanges χs ρ →
  StoreCorr ΔL′ ΔR ρ′ →
  ΔL ∣ ΔR ∣ ρ ⊢ qᵢ ∶ᶜ BL ⊒ᵐ BR →
  μO ∣ ΔL ∣ ΔR ∣ ρ ⊢ q ∶ Bₒ ⊒ᵐ BR →
  (dₛ⊒ˡ : ηC ∣ ΔL ∣ leftStore ρ ⊢ dₛ ∶ Bₒ ⊒ BL) →
  ΔL′ ∣ ΔR ∣ ρ′ ∣ []
    ⊢ N ⊒ Target ∶ qᵢ ⦂ applyTys χs BL ⊒ᵐ BR →
  ΔL′ ∣ ΔR ∣ ρ′ ∣ []
    ⊢ N ⟨ applyCoercions χs (narrowing-dual¹ dₛ⊒ˡ) ⟩ ⊒ Target
      ∶ q ⦂ applyTys χs Bₒ ⊒ᵐ BR
mediated-beta-cast-plus-tail χs {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {N = N} {Target = Target} {qᵢ = qᵢ} {q = q} {dₛ = dₛ}
    {Bₒ = Bₒ} {BL = BL} {BR = BR} {μO = μO} {ηC = ηC}
    refl refl corr′ qᵢᶜ q⊒ dₛ⊒ˡ N⊒Target =
  let
    dₛ⊒ˡ′ :
      applyModeEnvs χs ηC ∣ applyTyCtxs χs ΔL
        ∣ leftStore (applyLeftChanges χs ρ)
        ⊢ applyCoercions χs dₛ
          ∶ applyTys χs Bₒ ⊒ applyTys χs BL
    dₛ⊒ˡ′ =
      subst
        (λ Σ →
          applyModeEnvs χs ηC ∣ applyTyCtxs χs ΔL ∣ Σ
            ⊢ applyCoercions χs dₛ
              ∶ applyTys χs Bₒ ⊒ applyTys χs BL)
        (sym (leftStore-applyLeftChanges χs ρ))
        (left-changes-narrowingˡ χs dₛ⊒ˡ)
  in
  subst
    (λ c₀ →
      applyTyCtxs χs ΔL ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
        ⊢ N ⟨ c₀ ⟩ ⊒ Target ∶ q
          ⦂ applyTys χs Bₒ ⊒ᵐ BR)
    (narrowing-dual¹-applyCoercions χs dₛ⊒ˡ dₛ⊒ˡ′)
    (cast+⊒ᵗ
      (left-changes-transportᵐ χs corr′ qᵢᶜ)
      (left-changes-transportᵐ χs corr′ q⊒)
      dₛ⊒ˡ′
      N⊒Target)

mediated-beta-cast-minus-tail :
  ∀ χs {ΔL ΔR ρ ΔL′ ρ′ N Target qᵢ q dₛ BV Bₒ BR ηC μN} →
  ΔL′ ≡ applyTyCtxs χs ΔL →
  ρ′ ≡ applyLeftChanges χs ρ →
  StoreCorr ΔL′ ΔR ρ′ →
  ΔL ∣ ΔR ∣ ρ ⊢ q ∶ᶜ Bₒ ⊒ᵐ BR →
  (dₛ⊒ˡ : ηC ∣ ΔL ∣ leftStore ρ ⊢ dₛ ∶ BV ⊒ Bₒ) →
  μN ∣ ΔL′ ∣ ΔR ∣ ρ′ ⊢ qᵢ ∶ applyTys χs BV ⊒ᵐ BR →
  ΔL′ ∣ ΔR ∣ ρ′ ∣ []
    ⊢ N ⊒ Target ∶ qᵢ ⦂ applyTys χs BV ⊒ᵐ BR →
  ΔL′ ∣ ΔR ∣ ρ′ ∣ []
    ⊢ N ⟨ applyCoercions χs dₛ ⟩ ⊒ Target
      ∶ q ⦂ applyTys χs Bₒ ⊒ᵐ BR
mediated-beta-cast-minus-tail χs {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {N = N} {Target = Target} {qᵢ = qᵢ} {q = q} {dₛ = dₛ}
    {BV = BV} {Bₒ = Bₒ} {BR = BR} {ηC = ηC}
    refl refl corr′ qᶜ dₛ⊒ˡ qᵢ⊒ N⊒Target =
  cast-⊒ᵗ
    (left-changes-transportᵐ χs corr′ qᶜ)
    qᵢ⊒
    (subst
      (λ Σ →
        applyModeEnvs χs ηC ∣ applyTyCtxs χs ΔL ∣ Σ
          ⊢ applyCoercions χs dₛ
            ∶ applyTys χs BV ⊒ applyTys χs Bₒ)
      (sym (leftStore-applyLeftChanges χs ρ))
      (left-changes-narrowingˡ χs dₛ⊒ˡ))
    N⊒Target
