module proof.DGGBetaCastValueMediated where

-- File Charter:
--   * Mediated-store DGG value/wrap core for target
--     beta-through-function-cast steps.
--   * Handles the recursive source-cast tail simulation once both source
--     application subterms have been caught up to values.
--   * Extracted from `DGGBetaCastMediated` to keep the application packaging
--     module quick to check.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using
  (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

open import Types
open import Coercions
open import NarrowWiden using
  ( cross
  ; id-＇
  ; id-‵
  ; id★
  ; dualⁿ
  ; dualʷ
  ; sealⁿ
  ; untag
  ; _︔seal_
  ; _？︔_
  ; _∣_∣_⊢_∶_⊒_
  )
  renaming (_↦_ to _↦ⁿʷ_; `∀ to `∀ⁿʷ; gen to genⁿʷ)
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import Mediation
open import MediatedNarrowing
open import proof.CatchupSeparated using
  ( applyLeftChanges
  ; applyLeftChanges-++
  ; leftStore-applyLeftChanges
  )
open import proof.CatchupMediated using (catchup-lemmaᵐ)
open import proof.LeftChangeNarrowingSeparated using
  ( applyTys-⇒
  ; applyTerms-preserves-RuntimeOK
  ; no•-cast-inv
  ; ⟨⟩-term-injective
  ; ⟨⟩-coercion-injective
  ; ↦-left-injective
  ; ↦-right-injective
  ; dualʷ-involutive-raw
  )
open import proof.MediatedLeftInsertion using
  (left-changes-term-narrowingᵐ)
open import proof.DualRawProperties using (dualⁿ-raw)
open import proof.MediationProperties using
  ( left-changes-transportᵐ
  ; applyModeEnvs
  ; left-changes-narrowingˡ
  ; narrowing-dual¹-raw
  ; narrowing-dual¹-applyCoercions
  ; rightStore-applyLeftChanges
  ; fun-narrow-domain-dual¹
  ; fun-narrow-domain-dual-typing¹
  ; fun-narrow-codomain¹
  ; fun-narrow-domain-dualᵐ-determined
  )
open import proof.ReductionProperties using
  ( applyTerms-preserves-No•
  ; applyTerms-preserves-Value
  ; applyCoercions
  ; applyCoercions-++
  ; applyTys-++
  ; applyTyCtxs-++
  ; cast-↠
  ; ↠-trans
  ; ·₁-↠
  ; ·₂-↠
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

------------------------------------------------------------------------
-- Value-shape wrap simulation
------------------------------------------------------------------------

{-# TERMINATING #-}
mediated-dgg-beta-cast-value-shape :
  ∀ {ΔL ΔR ρ L R T V′ W′ c d pᵈ p q A A′ B B′} →
  Value L →
  No• L →
  Value R →
  No• R →
  Value V′ →
  Value W′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ T ∶ p ↦ q
    ⦂ A ⇒ B ⊒ᵐ A′ ⇒ B′ →
  T ≡ V′ ⟨ c ↦ d ⟩ →
  ΔL ∣ ΔR ∣ ρ ⊢ pᵈ ∶ᶜ A ⊒ᵐ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ R ⊒ W′ ∶ pᵈ ⦂ A ⊒ᵐ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩
        ∶ q ⦂ applyTys χs B ⊒ᵐ B′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′ (⊒blameᵗ M⊢ pᶜ) ()
    p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′ (x⊒xᵗ pᶜ x∋p) ()
    p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′ (ƛ⊒ƛᵗ p↦qᶜ N⊒N′) ()
    p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′ (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′) ()
    p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {t = id X} pᶜ r⊒ t⊒ʳ M⊒M′)
    T≡V′cd p-domainᶜ R⊒W′ =
  ⊥-elim (dual-id-not-fun t⊒ʳ (⟨⟩-coercion-injective T≡V′cd))
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {t = t₁ ︔ t₂} pᶜ r⊒ t⊒ʳ M⊒M′)
    T≡V′cd p-domainᶜ R⊒W′ =
  ⊥-elim (dual-seq-not-fun t⊒ʳ (⟨⟩-coercion-injective T≡V′cd))
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {t = `∀ t} pᶜ r⊒ t⊒ʳ M⊒M′)
    T≡V′cd p-domainᶜ R⊒W′ =
  ⊥-elim (dual-all-not-fun t⊒ʳ (⟨⟩-coercion-injective T≡V′cd))
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {t = G !} pᶜ r⊒ t⊒ʳ M⊒M′)
    T≡V′cd p-domainᶜ R⊒W′ =
  ⊥-elim (tag-narrowing-impossible t⊒ʳ)
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {t = G ？} pᶜ r⊒ t⊒ʳ M⊒M′)
    T≡V′cd p-domainᶜ R⊒W′ =
  ⊥-elim (dual-untag-not-fun t⊒ʳ (⟨⟩-coercion-injective T≡V′cd))
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {t = seal A α} pᶜ r⊒ t⊒ʳ M⊒M′)
    T≡V′cd p-domainᶜ R⊒W′ =
  ⊥-elim (dual-seal-not-fun t⊒ʳ (⟨⟩-coercion-injective T≡V′cd))
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {t = unseal α A} pᶜ r⊒ t⊒ʳ M⊒M′)
    T≡V′cd p-domainᶜ R⊒W′ =
  ⊥-elim (unseal-narrowing-impossible t⊒ʳ)
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {t = gen A t} pᶜ r⊒ t⊒ʳ M⊒M′)
    T≡V′cd p-domainᶜ R⊒W′ =
  ⊥-elim (dual-gen-not-fun t⊒ʳ (⟨⟩-coercion-injective T≡V′cd))
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {t = inst A t} pᶜ r⊒ t⊒ʳ M⊒M′)
    T≡V′cd p-domainᶜ R⊒W′ =
  ⊥-elim (inst-narrowing-impossible t⊒ʳ)
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {r = id X} pᶜ
      (_ , _ , _ , _ , _ , (cast-id _ _ , cross ()))
      (cast-fun _ _ , cross (_ ↦ⁿʷ _))
      L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {r = r₁ ︔ r₂} pᶜ r⊒
      (cast-fun _ _ , cross (_ ↦ⁿʷ _))
      L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′ =
  ⊥-elim (inner-seq-index-impossible r⊒)
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {r = X ？} pᶜ
      (_ , _ , _ , _ , () , (cast-untag _ _ _ , _))
      (cast-fun _ _ , cross (_ ↦ⁿʷ _))
      L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {r = unseal α X} pᶜ
      (_ , _ , _ , _ , () , (cast-unseal _ _ _ , _))
      (cast-fun _ _ , cross (_ ↦ⁿʷ _))
      L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {r = inst X r₁} pᶜ
      (_ , _ , _ , _ , () , (cast-inst _ _ _ , _))
      (cast-fun _ _ , cross (_ ↦ⁿʷ _))
      L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d} {pᵈ = pᵈ} {p = p} {q = q} {A = A} {A′ = A′}
    {B = B} {B′ = B′}
    vL noL vR noR vV′ vW′
    (⊒cast+ᵗ {M′ = F′} {r = pᵢ ↦ qᵢ} {t = cₜ ↦ dₜ}
      {B = Aᵢ ⇒ Bᵢ}
      pᶜ r⊒ t⊒ʳ@(cast-fun cₜ⊢ dₜ⊢ , cross (cₜʷ ↦ⁿʷ dₜⁿ))
      L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′ =
  let
    target-head-eq : F′ ≡ V′
    target-head-eq = ⟨⟩-term-injective T≡V′cd

    target-cast-eq : narrowing-dual¹ t⊒ʳ ≡ c ↦ d
    target-cast-eq = ⟨⟩-coercion-injective T≡V′cd

    target-domain-eq : fun-narrow-domain-dual¹ t⊒ʳ ≡ c
    target-domain-eq = ↦-left-injective target-cast-eq

    L⊒V′ :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ L ⊒ V′ ∶ pᵢ ↦ qᵢ ⦂ A ⇒ B ⊒ᵐ Aᵢ ⇒ Bᵢ
    L⊒V′ =
      subst
        (λ F →
          ΔL ∣ ΔR ∣ ρ ∣ []
            ⊢ L ⊒ F ∶ pᵢ ↦ qᵢ ⦂ A ⇒ B ⊒ᵐ Aᵢ ⇒ Bᵢ)
        target-head-eq
        L⊒F′

    χsF , WF , ΔLF ,
      vWF , noWF , L↠WF , ΔLF≡ , ρF-corr ,
      leftF≡ , rightF≡ , rFᶜraw , WF⊒V′raw =
      catchup-lemmaᵐ (ok-no noL) vV′ L⊒V′

    ρF = applyLeftChanges χsF ρ

    corrF : StoreCorr (applyTyCtxs χsF ΔL) ΔR ρF
    corrF = subst (λ Δ → StoreCorr Δ ΔR ρF) ΔLF≡ ρF-corr

    rFᶜ :
      ΔLF ∣ ΔR ∣ ρF
        ⊢ pᵢ ↦ qᵢ ∶ᶜ applyTys χsF A ⇒ applyTys χsF B
          ⊒ᵐ Aᵢ ⇒ Bᵢ
    rFᶜ =
      subst
        (λ C₀ → ΔLF ∣ ΔR ∣ ρF ⊢ pᵢ ↦ qᵢ ∶ᶜ C₀ ⊒ᵐ Aᵢ ⇒ Bᵢ)
        (applyTys-⇒ χsF A B)
        rFᶜraw

    WF⊒V′ :
      ΔLF ∣ ΔR ∣ ρF ∣ []
        ⊢ WF ⊒ V′ ∶ pᵢ ↦ qᵢ
          ⦂ applyTys χsF A ⇒ applyTys χsF B ⊒ᵐ Aᵢ ⇒ Bᵢ
    WF⊒V′ =
      subst
        (λ C₀ →
          ΔLF ∣ ΔR ∣ ρF ∣ []
            ⊢ WF ⊒ V′ ∶ pᵢ ↦ qᵢ ⦂ C₀ ⊒ᵐ Aᵢ ⇒ Bᵢ)
        (applyTys-⇒ χsF A B)
        WF⊒V′raw

    pᶜFraw :
      applyTyCtxs χsF ΔL ∣ ΔR ∣ ρF
        ⊢ p ↦ q ∶ᶜ applyTys χsF (A ⇒ B) ⊒ᵐ A′ ⇒ B′
    pᶜFraw = left-changes-transportᵐ χsF corrF pᶜ

    pᶜF :
      ΔLF ∣ ΔR ∣ ρF
        ⊢ p ↦ q ∶ᶜ applyTys χsF A ⇒ applyTys χsF B
          ⊒ᵐ A′ ⇒ B′
    pᶜF =
      subst
        (λ C₀ →
          ΔLF ∣ ΔR ∣ ρF ⊢ p ↦ q ∶ᶜ C₀ ⊒ᵐ A′ ⇒ B′)
        (applyTys-⇒ χsF A B)
        (subst
          (λ Δ →
            Δ ∣ ΔR ∣ ρF ⊢ p ↦ q
              ∶ᶜ applyTys χsF (A ⇒ B) ⊒ᵐ A′ ⇒ B′)
          (sym ΔLF≡)
          pᶜFraw)

    p-domainFraw :
      applyTyCtxs χsF ΔL ∣ ΔR ∣ ρF
        ⊢ pᵈ ∶ᶜ applyTys χsF A ⊒ᵐ A′
    p-domainFraw = left-changes-transportᵐ χsF corrF p-domainᶜ

    p-domainF :
      ΔLF ∣ ΔR ∣ ρF
        ⊢ pᵈ ∶ᶜ applyTys χsF A ⊒ᵐ A′
    p-domainF =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ ρF
            ⊢ pᵈ ∶ᶜ applyTys χsF A ⊒ᵐ A′)
        (sym ΔLF≡)
        p-domainFraw

    RF⊒W′raw :
      applyTyCtxs χsF ΔL ∣ ΔR ∣ ρF ∣ []
        ⊢ applyTerms χsF R ⊒ W′ ∶ pᵈ
          ⦂ applyTys χsF A ⊒ᵐ A′
    RF⊒W′raw = left-changes-term-narrowingᵐ χsF corrF R⊒W′

    RF⊒W′ :
      ΔLF ∣ ΔR ∣ ρF ∣ []
        ⊢ applyTerms χsF R ⊒ W′ ∶ pᵈ
          ⦂ applyTys χsF A ⊒ᵐ A′
    RF⊒W′ =
      subst
        (λ Δ →
          Δ ∣ ΔR ∣ ρF ∣ []
            ⊢ applyTerms χsF R ⊒ W′
              ∶ pᵈ ⦂ applyTys χsF A ⊒ᵐ A′)
        (sym ΔLF≡)
        RF⊒W′raw

    target-domain-castF :
      _ ∣ ΔR ∣ rightStore ρF ⊢ fun-narrow-domain-dual¹ t⊒ʳ
        ∶ A′ ⊒ Aᵢ
    target-domain-castF =
      subst
        (λ Σ →
          _ ∣ ΔR ∣ Σ ⊢ fun-narrow-domain-dual¹ t⊒ʳ ∶ A′ ⊒ Aᵢ)
        (sym rightF≡)
        (fun-narrow-domain-dual-typing¹
          (rightStore-wf (narrowing-store-corrᵐᶜ pᶜ))
          t⊒ʳ)

    target-argument-cast :
      ΔLF ∣ ΔR ∣ ρF ∣ []
        ⊢ applyTerms χsF R ⊒ W′ ⟨ c ⟩
          ∶ fun-narrow-domain-dualᵐᶜ rFᶜ
          ⦂ applyTys χsF A ⊒ᵐ Aᵢ
    target-argument-cast =
      subst
        (λ c₀ →
          ΔLF ∣ ΔR ∣ ρF ∣ []
            ⊢ applyTerms χsF R ⊒ W′ ⟨ c₀ ⟩
              ∶ fun-narrow-domain-dualᵐᶜ rFᶜ
              ⦂ applyTys χsF A ⊒ᵐ Aᵢ)
        target-domain-eq
        (⊒cast-ᵗ
          p-domainF
          (fun-narrow-domain-dual-typingᵐᶜ rFᶜ)
          target-domain-castF
          RF⊒W′)

    inner-application :
      ΔLF ∣ ΔR ∣ ρF ∣ []
        ⊢ WF · applyTerms χsF R ⊒ V′ · (W′ ⟨ c ⟩)
          ∶ qᵢ ⦂ applyTys χsF B ⊒ᵐ Bᵢ
    inner-application =
      ·⊒·ᵗ rFᶜ WF⊒V′ target-argument-cast

    target-codomain-castF :
      _ ∣ ΔR ∣ rightStore ρF ⊢ dₜ ∶ B′ ⊒ Bᵢ
    target-codomain-castF =
      subst
        (λ Σ → _ ∣ ΔR ∣ Σ ⊢ dₜ ∶ B′ ⊒ Bᵢ)
        (sym rightF≡)
        (fun-narrow-codomain¹ t⊒ʳ)

    target-codomain-dual-eq : narrowing-dual¹ target-codomain-castF ≡ d
    target-codomain-dual-eq =
      trans
        (narrowing-dual¹-applyCoercions []
          (fun-narrow-codomain¹ t⊒ʳ)
          target-codomain-castF)
        (↦-right-injective target-cast-eq)

    target-result-cast :
      ΔLF ∣ ΔR ∣ ρF ∣ []
        ⊢ WF · applyTerms χsF R
          ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩
          ∶ q ⦂ applyTys χsF B ⊒ᵐ B′
    target-result-cast =
      subst
        (λ d₀ →
          ΔLF ∣ ΔR ∣ ρF ∣ []
            ⊢ WF · applyTerms χsF R
              ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d₀ ⟩
              ∶ q ⦂ applyTys χsF B ⊒ᵐ B′)
        target-codomain-dual-eq
        (⊒cast+ᵗ
          (fun-narrow-codomainᵐᶜ pᶜF)
          (fun-narrow-codomainᵐᶜ rFᶜ)
          target-codomain-castF
          inner-application)

    left-ready :
      L · R —↠[ χsF ] WF · applyTerms χsF R
    left-ready = ·₁-↠ noR L↠WF
  in
  χsF ,
  WF · applyTerms χsF R ,
  ΔLF ,
  ρF ,
  left-ready ,
  ΔLF≡ ,
  refl ,
  target-result-cast
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {t = id X} pᶜ r⊒ t⊒ʳ M⊒M′) ()
    p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {t = t₁ ︔ t₂} pᶜ r⊒ t⊒ʳ M⊒M′) ()
    p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {t = `∀ t} pᶜ r⊒ t⊒ʳ M⊒M′) ()
    p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {t = G !} pᶜ r⊒ t⊒ʳ M⊒M′) ()
    p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {t = G ？} pᶜ r⊒ t⊒ʳ M⊒M′) ()
    p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {t = seal A α} pᶜ r⊒ t⊒ʳ M⊒M′) ()
    p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {t = unseal α A} pᶜ r⊒ t⊒ʳ M⊒M′) ()
    p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {t = gen A t} pᶜ r⊒ t⊒ʳ M⊒M′) ()
    p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {t = inst A t} pᶜ r⊒ t⊒ʳ M⊒M′) ()
    p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d} {p = p} {q = q} {A = A} {A′ = A′} {B = B}
    {B′ = B′}
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {M′ = F′} {p = pᵢ ↦ qᵢ} {t = cₜ ↦ dₜ}
      {C = Aᵢ ⇒ Bᵢ}
      pᶜ r⊒ t⊒ʳ@(cast-fun cₜ⊢ dₜ⊢ , cross (cₜʷ ↦ⁿʷ dₜⁿ))
      L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′ =
  let
    target-head-eq : F′ ≡ V′
    target-head-eq = ⟨⟩-term-injective T≡V′cd

    target-cast-eq : cₜ ↦ dₜ ≡ c ↦ d
    target-cast-eq = ⟨⟩-coercion-injective T≡V′cd

    target-domain-cast :
      _ ∣ ΔR ∣ rightStore ρ ⊢ fun-narrow-domain-dual¹ t⊒ʳ
        ∶ Aᵢ ⊒ A′
    target-domain-cast =
      fun-narrow-domain-dual-typing¹
        (rightStore-wf (narrowing-store-corrᵐᶜ pᶜ))
        t⊒ʳ

    target-domain-dual-eq :
      narrowing-dual¹ target-domain-cast ≡ c
    target-domain-dual-eq =
      trans
        (narrowing-dual¹-raw target-domain-cast)
        (trans
          (sym (dualⁿ-raw normalᵃ (proj₂ (dualʷ normalᵃ cₜʷ))))
          (trans
            (dualʷ-involutive-raw cₜʷ)
            (↦-left-injective target-cast-eq)))

    target-codomain-eq : dₜ ≡ d
    target-codomain-eq = ↦-right-injective target-cast-eq

    target-argument-cast :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ R ⊒ W′ ⟨ c ⟩ ∶ fun-narrow-domain-dualᵐᶜ pᶜ
          ⦂ A ⊒ᵐ Aᵢ
    target-argument-cast =
      subst
        (λ c₀ →
          ΔL ∣ ΔR ∣ ρ ∣ []
            ⊢ R ⊒ W′ ⟨ c₀ ⟩ ∶ fun-narrow-domain-dualᵐᶜ pᶜ
              ⦂ A ⊒ᵐ Aᵢ)
        target-domain-dual-eq
        (⊒cast+ᵗ
          (fun-narrow-domain-dual-typingᵐᶜ pᶜ)
          p-domainᶜ
          target-domain-cast
          R⊒W′)

    inner-application :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ L · R ⊒ F′ · (W′ ⟨ c ⟩) ∶ qᵢ ⦂ B ⊒ᵐ Bᵢ
    inner-application = ·⊒·ᵗ pᶜ L⊒F′ target-argument-cast

    target-result-cast :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ L · R ⊒ (F′ · (W′ ⟨ c ⟩)) ⟨ dₜ ⟩
          ∶ q ⦂ B ⊒ᵐ B′
    target-result-cast =
      ⊒cast-ᵗ
        (fun-narrow-codomainᵐᶜ pᶜ)
        (fun-narrow-codomainᵐ r⊒)
        (fun-narrow-codomain¹ t⊒ʳ)
        inner-application

    obligation :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ L · R ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩
          ∶ q ⦂ B ⊒ᵐ B′
    obligation =
      subst
        (λ d₀ →
          ΔL ∣ ΔR ∣ ρ ∣ []
            ⊢ L · R ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d₀ ⟩
              ∶ q ⦂ B ⊒ᵐ B′)
        target-codomain-eq
        (subst
          (λ F →
            ΔL ∣ ΔR ∣ ρ ∣ []
              ⊢ L · R ⊒ (F · (W′ ⟨ c ⟩)) ⟨ dₜ ⟩
                ∶ q ⦂ B ⊒ᵐ B′)
          target-head-eq
          target-result-cast)
  in
  [] , L · R , ΔL , ρ , ↠-refl , refl , refl , obligation
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {p = id X}
      (_ , _ , _ , _ , _ , (cast-id _ _ , cross ()))
      r⊒ (cast-fun _ _ , cross (_ ↦ⁿʷ _))
      L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {p = p₁ ︔ p₂} pᶜ r⊒
      (cast-fun _ _ , cross (_ ↦ⁿʷ _))
      L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′ =
  ⊥-elim (inner-seq-index-impossible pᶜ)
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {p = X ？}
      (_ , _ , _ , _ , () , (cast-untag _ _ _ , _))
      r⊒ (cast-fun _ _ , cross (_ ↦ⁿʷ _))
      L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {p = unseal α X}
      (_ , _ , _ , _ , () , (cast-unseal _ _ _ , _))
      r⊒ (cast-fun _ _ , cross (_ ↦ⁿʷ _))
      L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (⊒cast-ᵗ {p = inst X p₁}
      (_ , _ , _ , _ , () , (cast-inst _ _ _ , _))
      r⊒ (cast-fun _ _ , cross (_ ↦ⁿʷ _))
      L⊒F′)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (cast+⊒ᵗ {s = id X} qᶜ r⊒ (cast-id _ _ , cross ()) L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (cast+⊒ᵗ {s = s₁ ︔ s₂} qᶜ r⊒ s⊒ˡ L⊒T)
    T≡V′cd p-domainᶜ R⊒W′ =
  ⊥-elim (plus-seq-cast-impossible s⊒ˡ vL)
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (cast+⊒ᵗ {s = unseal α X} qᶜ r⊒ (_ , cross ()) L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (cast+⊒ᵗ {s = inst X s} qᶜ r⊒ (_ , cross ()) L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    (vV ⟨ () ⟩) noL vR noR vV′ vW′
    (cast+⊒ᵗ {s = gen X s} qᶜ r⊒ (s⊢ , genⁿʷ sⁿ) L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (cast+⊒ᵗ {s = X !} qᶜ r⊒ (_ , cross ()) L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    (vV ⟨ () ⟩) noL vR noR vV′ vW′
    (cast+⊒ᵗ {s = seal X α} qᶜ r⊒ (s⊢ , sealⁿ .X .α) L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (cast+⊒ᵗ {q = id X}
      (_ , _ , _ , _ , _ , (cast-id _ _ , cross ()))
      r⊒ s⊒ˡ L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (cast+⊒ᵗ {q = q₁ ︔ q₂} qᶜ r⊒ (cast-fun _ _ , _) L⊒T)
    T≡V′cd p-domainᶜ R⊒W′ =
  ⊥-elim (inner-seq-index-impossible qᶜ)
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (cast+⊒ᵗ {q = X ？}
      (_ , _ , _ , _ , () , (cast-untag _ _ _ , _))
      r⊒ (cast-fun _ _ , _) L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (cast+⊒ᵗ {q = unseal α X}
      (_ , _ , _ , _ , () , (cast-unseal _ _ _ , _))
      r⊒ (cast-fun _ _ , _) L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (cast+⊒ᵗ {q = inst X q₁}
      (_ , _ , _ , _ , () , (cast-inst _ _ _ , _))
      r⊒ (cast-fun _ _ , _) L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d} {A = Aₒ} {A′ = AR} {B = Bₒ} {B′ = BR}
    vL@(vV ⟨ i ⟩) (no•-⟨⟩ noV) vR noR vV′ vW′
    (cast+⊒ᵗ {M = V} {q = pᵢ ↦ qᵢ} {r = pₒ ↦ qₒ}
      {s = cₛ ↦ dₛ} {C = AL ⇒ BL} {μ = μO} {η = ηC}
      qᶜ r⊒ s⊒ˡ@(cast-fun c⊢ d⊢ , cross (cʷ ↦ⁿʷ dⁿ)) V⊒T)
    T≡V′cd p-domainᶜ R⊒W′ =
  let
    stores = narrowing-store-corrᵐᶜ qᶜ

    cᵈ = proj₁ (dualʷ normalᵃ cʷ)
    dᵈ = proj₁ (dualⁿ normalᵃ dⁿ)

    R-c⊒W′ :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ R ⟨ cᵈ ⟩ ⊒ W′ ∶ fun-narrow-domain-dualᵐᶜ qᶜ
          ⦂ AL ⊒ᵐ AR
    R-c⊒W′ =
      cast-⊒ᵗ
        (fun-narrow-domain-dual-typingᵐᶜ qᶜ)
        p-domainᶜ
        (fun-narrow-domain-dual-typing¹ (leftStore-wf stores) s⊒ˡ)
        R⊒W′

    χsA , WRA , ΔLA , vWRA , noWRA , R↠WRA , ΔLA≡ , ρA-corr ,
      leftA≡ , rightA≡ , pdᶜᴬ , WRA⊒W′ᴬ =
      catchup-lemmaᵐ (ok-⟨⟩ (ok-no noR)) vW′ R-c⊒W′

    ρA = applyLeftChanges χsA ρ

    corrA : StoreCorr (applyTyCtxs χsA ΔL) ΔR ρA
    corrA = subst (λ Δ → StoreCorr Δ ΔR ρA) ΔLA≡ ρA-corr

    VA⊒T :
      ΔLA ∣ ΔR ∣ ρA ∣ []
        ⊢ applyTerms χsA V ⊒ T ∶ pᵢ ↦ qᵢ
          ⦂ applyTys χsA AL ⇒ applyTys χsA BL ⊒ᵐ AR ⇒ BR
    VA⊒T =
      subst
        (λ C₀ →
          ΔLA ∣ ΔR ∣ ρA ∣ []
            ⊢ applyTerms χsA V ⊒ T ∶ pᵢ ↦ qᵢ
              ⦂ C₀ ⊒ᵐ AR ⇒ BR)
        (applyTys-⇒ χsA AL BL)
        (subst
          (λ Δ →
            Δ ∣ ΔR ∣ ρA ∣ []
              ⊢ applyTerms χsA V ⊒ T ∶ pᵢ ↦ qᵢ
                ⦂ applyTys χsA (AL ⇒ BL) ⊒ᵐ AR ⇒ BR)
          (sym ΔLA≡)
          (left-changes-term-narrowingᵐ χsA corrA V⊒T))

    qᶜᴬ :
      ΔLA ∣ ΔR ∣ ρA
        ⊢ pᵢ ↦ qᵢ
          ∶ᶜ applyTys χsA AL ⇒ applyTys χsA BL ⊒ᵐ AR ⇒ BR
    qᶜᴬ =
      subst
        (λ C₀ →
          ΔLA ∣ ΔR ∣ ρA ⊢ pᵢ ↦ qᵢ ∶ᶜ C₀ ⊒ᵐ AR ⇒ BR)
        (applyTys-⇒ χsA AL BL)
        (subst
          (λ Δ →
            Δ ∣ ΔR ∣ ρA ⊢ pᵢ ↦ qᵢ
              ∶ᶜ applyTys χsA (AL ⇒ BL) ⊒ᵐ AR ⇒ BR)
          (sym ΔLA≡)
          (left-changes-transportᵐ χsA corrA qᶜ))

    pd-eq :
      fun-narrow-domain-dualᵐ qᶜᴬ ≡ fun-narrow-domain-dualᵐᶜ qᶜ
    pd-eq = fun-narrow-domain-dualᵐ-determined qᶜᴬ qᶜ

    p-domainᶜᴬ :
      ΔLA ∣ ΔR ∣ ρA
        ⊢ fun-narrow-domain-dualᵐ qᶜᴬ ∶ᶜ applyTys χsA AL ⊒ᵐ AR
    p-domainᶜᴬ =
      subst
        (λ pd →
          ΔLA ∣ ΔR ∣ ρA ⊢ pd ∶ᶜ applyTys χsA AL ⊒ᵐ AR)
        (sym pd-eq)
        pdᶜᴬ

    WRA⊒W′ :
      ΔLA ∣ ΔR ∣ ρA ∣ []
        ⊢ WRA ⊒ W′ ∶ fun-narrow-domain-dualᵐ qᶜᴬ
          ⦂ applyTys χsA AL ⊒ᵐ AR
    WRA⊒W′ =
      subst
        (λ pd →
          ΔLA ∣ ΔR ∣ ρA ∣ []
            ⊢ WRA ⊒ W′ ∶ pd ⦂ applyTys χsA AL ⊒ᵐ AR)
        (sym pd-eq)
        WRA⊒W′ᴬ

    χsT , N , ΔLT , ρT , tail-red , ΔT≡ , ρT≡ , N⊒Target =
      mediated-dgg-beta-cast-value-shape
        (applyTerms-preserves-Value χsA vV)
        (applyTerms-preserves-No• χsA noV)
        vWRA
        noWRA
        vV′
        vW′
        VA⊒T
        T≡V′cd
        p-domainᶜᴬ
        WRA⊒W′

    head-red :
      (V ⟨ cᵈ ↦ dᵈ ⟩) · R —↠[ keep ∷ [] ]
        (V · (R ⟨ cᵈ ⟩)) ⟨ dᵈ ⟩
    head-red = ↠-step (pure-step (β-↦ vV vR)) ↠-refl

    source-steps :
      (V ⟨ cᵈ ↦ dᵈ ⟩) · R —↠[ (keep ∷ χsA) ++ χsT ]
        N ⟨ applyCoercions χsT (applyCoercions χsA dᵈ) ⟩
    source-steps =
      ↠-trans
        (↠-trans head-red (cast-↠ {c = dᵈ} (·₂-↠ vV noV R↠WRA)))
        (cast-↠ {c = applyCoercions χsA dᵈ} tail-red)

    ΔLT-total≡ :
      ΔLT ≡ applyTyCtxs ((keep ∷ χsA) ++ χsT) ΔL
    ΔLT-total≡ =
      trans ΔT≡
        (trans
          (cong (applyTyCtxs χsT) ΔLA≡)
          (sym (applyTyCtxs-++ χsA χsT ΔL)))

    ρT-total≡ :
      ρT ≡ applyLeftChanges ((keep ∷ χsA) ++ χsT) ρ
    ρT-total≡ =
      trans ρT≡ (sym (applyLeftChanges-++ χsA χsT ρ))

    μN , qᵢ⊒T = typed-term-narrowing-coercionᵐ N⊒Target

    ρT-corr : StoreCorr ΔLT ΔR ρT
    ρT-corr = narrowing-store-corrᵐᶜ {μ = μN} qᵢ⊒T

    N⊒Target′ :
      ΔLT ∣ ΔR ∣ ρT ∣ []
        ⊢ N ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ qᵢ
          ⦂ applyTys (χsA ++ χsT) BL ⊒ᵐ BR
    N⊒Target′ =
      subst
        (λ X →
          ΔLT ∣ ΔR ∣ ρT ∣ []
            ⊢ N ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ qᵢ
              ⦂ X ⊒ᵐ BR)
        (sym (applyTys-++ χsA χsT BL))
        N⊒Target

    N-tail :
      ΔLT ∣ ΔR ∣ ρT ∣ []
        ⊢ N ⟨ applyCoercions (χsA ++ χsT) dᵈ ⟩
          ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩
          ∶ qₒ ⦂ applyTys (χsA ++ χsT) Bₒ ⊒ᵐ BR
    N-tail =
      mediated-beta-cast-plus-tail (χsA ++ χsT)
        ΔLT-total≡
        ρT-total≡
        ρT-corr
        (fun-narrow-codomainᵐᶜ qᶜ)
        (fun-narrow-codomainᵐ r⊒)
        (d⊢ , dⁿ)
        N⊒Target′
  in
  (keep ∷ χsA) ++ χsT ,
  N ⟨ applyCoercions χsT (applyCoercions χsA dᵈ) ⟩ ,
  ΔLT ,
  ρT ,
  source-steps ,
  ΔLT-total≡ ,
  ρT-total≡ ,
  subst
    (λ c₀ →
      ΔLT ∣ ΔR ∣ ρT ∣ []
        ⊢ N ⟨ c₀ ⟩ ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩
          ∶ qₒ ⦂ applyTys (χsA ++ χsT) Bₒ ⊒ᵐ BR)
    (applyCoercions-++ χsA χsT dᵈ)
    N-tail
mediated-dgg-beta-cast-value-shape
    (vV ⟨ () ⟩) noL vR noR vV′ vW′
    (cast-⊒ᵗ {s = id X} qᶜ r⊒ (cast-id _ _ , cross ()) L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    (vV ⟨ () ⟩) noL vR noR vV′ vW′
    (cast-⊒ᵗ {s = s₁ ︔ s₂} qᶜ r⊒ s⊒ˡ L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    (vV ⟨ () ⟩) noL vR noR vV′ vW′
    (cast-⊒ᵗ {s = X ？} qᶜ r⊒ s⊒ˡ L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    (vV ⟨ () ⟩) noL vR noR vV′ vW′
    (cast-⊒ᵗ {s = unseal α X} qᶜ r⊒ s⊒ˡ L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    (vV ⟨ () ⟩) noL vR noR vV′ vW′
    (cast-⊒ᵗ {s = inst X s} qᶜ r⊒ s⊒ˡ L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (cast-⊒ᵗ {r = id X} qᶜ
      (_ , _ , _ , _ , _ , (cast-id _ _ , cross ()))
      (cast-fun _ _ , cross (_ ↦ⁿʷ _))
      L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (cast-⊒ᵗ {r = r₁ ︔ r₂} qᶜ r⊒
      (cast-fun _ _ , cross (_ ↦ⁿʷ _))
      L⊒T)
    T≡V′cd p-domainᶜ R⊒W′ =
  ⊥-elim (inner-seq-index-impossible r⊒)
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (cast-⊒ᵗ {r = X ？} qᶜ
      (_ , _ , _ , _ , () , (cast-untag _ _ _ , _))
      (cast-fun _ _ , cross (_ ↦ⁿʷ _))
      L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (cast-⊒ᵗ {r = unseal α X} qᶜ
      (_ , _ , _ , _ , () , (cast-unseal _ _ _ , _))
      (cast-fun _ _ , cross (_ ↦ⁿʷ _))
      L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape
    vL noL vR noR vV′ vW′
    (cast-⊒ᵗ {r = inst X r₁} qᶜ
      (_ , _ , _ , _ , () , (cast-inst _ _ _ , _))
      (cast-fun _ _ , cross (_ ↦ⁿʷ _))
      L⊒T)
    T≡V′cd p-domainᶜ R⊒W′
mediated-dgg-beta-cast-value-shape {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {L = L} {R = R} {T = T} {V′ = V′} {W′ = W′} {c = c}
    {d = d} {A = Aₒ} {A′ = AR} {B = Bₒ} {B′ = BR}
    vL@(vV ⟨ i ⟩) (no•-⟨⟩ noV) vR noR vV′ vW′
    (cast-⊒ᵗ {M = V} {q = pₒ ↦ qₒ} {r = pᵢ ↦ qᵢ}
      {s = cₛ ↦ dₛ} {A = AV ⇒ BV} {μ = μO} {η = ηC}
      qᶜ r⊒ s⊒ˡ@(cast-fun c⊢ d⊢ , cross (cʷ ↦ⁿʷ dⁿ)) V⊒T)
    T≡V′cd p-domainᶜ R⊒W′ =
  let
    stores = narrowing-store-corrᵐᶜ qᶜ

    cᵈ = proj₁ (dualʷ normalᵃ cʷ)
    cᵈⁿ = proj₂ (dualʷ normalᵃ cʷ)

    cᵈ⊒ˡ : ηC ∣ ΔL ∣ leftStore ρ ⊢ cᵈ ∶ AV ⊒ Aₒ
    cᵈ⊒ˡ =
      proj₁ (fun-narrow-domain-dual-typing¹ (leftStore-wf stores) s⊒ˡ) ,
      cᵈⁿ

    R-c⊒W′ :
      ΔL ∣ ΔR ∣ ρ ∣ []
        ⊢ R ⟨ cₛ ⟩ ⊒ W′ ∶ fun-narrow-domain-dualᵐ r⊒
          ⦂ AV ⊒ᵐ AR
    R-c⊒W′ =
      subst
        (λ c₀ →
          ΔL ∣ ΔR ∣ ρ ∣ []
            ⊢ R ⟨ c₀ ⟩ ⊒ W′ ∶ fun-narrow-domain-dualᵐ r⊒
              ⦂ AV ⊒ᵐ AR)
        (dualʷ-involutive-raw cʷ)
        (cast+⊒ᵗ
          p-domainᶜ
          (fun-narrow-domain-dual-typingᵐ r⊒)
          cᵈ⊒ˡ
          R⊒W′)

    χsA , WRA , ΔLA , vWRA , noWRA , R↠WRA , ΔLA≡ , ρA-corr ,
      leftA≡ , rightA≡ , pdᶜᴬ , WRA⊒W′ᴬ =
      catchup-lemmaᵐ (ok-⟨⟩ (ok-no noR)) vW′ R-c⊒W′

    ρA = applyLeftChanges χsA ρ

    corrA : StoreCorr (applyTyCtxs χsA ΔL) ΔR ρA
    corrA = subst (λ Δ → StoreCorr Δ ΔR ρA) ΔLA≡ ρA-corr

    VA⊒T :
      ΔLA ∣ ΔR ∣ ρA ∣ []
        ⊢ applyTerms χsA V ⊒ T ∶ pᵢ ↦ qᵢ
          ⦂ applyTys χsA AV ⇒ applyTys χsA BV ⊒ᵐ AR ⇒ BR
    VA⊒T =
      subst
        (λ C₀ →
          ΔLA ∣ ΔR ∣ ρA ∣ []
            ⊢ applyTerms χsA V ⊒ T ∶ pᵢ ↦ qᵢ
              ⦂ C₀ ⊒ᵐ AR ⇒ BR)
        (applyTys-⇒ χsA AV BV)
        (subst
          (λ Δ →
            Δ ∣ ΔR ∣ ρA ∣ []
              ⊢ applyTerms χsA V ⊒ T ∶ pᵢ ↦ qᵢ
                ⦂ applyTys χsA (AV ⇒ BV) ⊒ᵐ AR ⇒ BR)
          (sym ΔLA≡)
          (left-changes-term-narrowingᵐ χsA corrA V⊒T))

    r⊒ᴬ :
      μO ∣ ΔLA ∣ ΔR ∣ ρA
        ⊢ pᵢ ↦ qᵢ
          ∶ applyTys χsA AV ⇒ applyTys χsA BV ⊒ᵐ AR ⇒ BR
    r⊒ᴬ =
      subst
        (λ C₀ →
          μO ∣ ΔLA ∣ ΔR ∣ ρA ⊢ pᵢ ↦ qᵢ ∶ C₀ ⊒ᵐ AR ⇒ BR)
        (applyTys-⇒ χsA AV BV)
        (subst
          (λ Δ →
            μO ∣ Δ ∣ ΔR ∣ ρA ⊢ pᵢ ↦ qᵢ
              ∶ applyTys χsA (AV ⇒ BV) ⊒ᵐ AR ⇒ BR)
          (sym ΔLA≡)
          (left-changes-transportᵐ χsA corrA r⊒))

    pd-eq :
      fun-narrow-domain-dualᵐ r⊒ᴬ ≡ fun-narrow-domain-dualᵐ r⊒
    pd-eq = fun-narrow-domain-dualᵐ-determined r⊒ᴬ r⊒

    p-domainᶜᴬ :
      ΔLA ∣ ΔR ∣ ρA
        ⊢ fun-narrow-domain-dualᵐ r⊒ᴬ ∶ᶜ applyTys χsA AV ⊒ᵐ AR
    p-domainᶜᴬ =
      subst
        (λ pd →
          ΔLA ∣ ΔR ∣ ρA ⊢ pd ∶ᶜ applyTys χsA AV ⊒ᵐ AR)
        (sym pd-eq)
        pdᶜᴬ

    WRA⊒W′ :
      ΔLA ∣ ΔR ∣ ρA ∣ []
        ⊢ WRA ⊒ W′ ∶ fun-narrow-domain-dualᵐ r⊒ᴬ
          ⦂ applyTys χsA AV ⊒ᵐ AR
    WRA⊒W′ =
      subst
        (λ pd →
          ΔLA ∣ ΔR ∣ ρA ∣ []
            ⊢ WRA ⊒ W′ ∶ pd ⦂ applyTys χsA AV ⊒ᵐ AR)
        (sym pd-eq)
        WRA⊒W′ᴬ

    χsT , N , ΔLT , ρT , tail-red , ΔT≡ , ρT≡ , N⊒Target =
      mediated-dgg-beta-cast-value-shape
        (applyTerms-preserves-Value χsA vV)
        (applyTerms-preserves-No• χsA noV)
        vWRA
        noWRA
        vV′
        vW′
        VA⊒T
        T≡V′cd
        p-domainᶜᴬ
        WRA⊒W′

    head-red :
      (V ⟨ cₛ ↦ dₛ ⟩) · R —↠[ keep ∷ [] ]
        (V · (R ⟨ cₛ ⟩)) ⟨ dₛ ⟩
    head-red = ↠-step (pure-step (β-↦ vV vR)) ↠-refl

    source-steps :
      (V ⟨ cₛ ↦ dₛ ⟩) · R —↠[ (keep ∷ χsA) ++ χsT ]
        N ⟨ applyCoercions χsT (applyCoercions χsA dₛ) ⟩
    source-steps =
      ↠-trans
        (↠-trans head-red (cast-↠ {c = dₛ} (·₂-↠ vV noV R↠WRA)))
        (cast-↠ {c = applyCoercions χsA dₛ} tail-red)

    ΔLT-total≡ :
      ΔLT ≡ applyTyCtxs ((keep ∷ χsA) ++ χsT) ΔL
    ΔLT-total≡ =
      trans ΔT≡
        (trans
          (cong (applyTyCtxs χsT) ΔLA≡)
          (sym (applyTyCtxs-++ χsA χsT ΔL)))

    ρT-total≡ :
      ρT ≡ applyLeftChanges ((keep ∷ χsA) ++ χsT) ρ
    ρT-total≡ =
      trans ρT≡ (sym (applyLeftChanges-++ χsA χsT ρ))

    μN , qᵢ⊒T = typed-term-narrowing-coercionᵐ N⊒Target

    ρT-corr : StoreCorr ΔLT ΔR ρT
    ρT-corr = narrowing-store-corrᵐᶜ {μ = μN} qᵢ⊒T

    qᵢ⊒′ :
      μN ∣ ΔLT ∣ ΔR ∣ ρT
        ⊢ qᵢ ∶ applyTys (χsA ++ χsT) BV ⊒ᵐ BR
    qᵢ⊒′ =
      subst
        (λ X → μN ∣ ΔLT ∣ ΔR ∣ ρT ⊢ qᵢ ∶ X ⊒ᵐ BR)
        (sym (applyTys-++ χsA χsT BV))
        qᵢ⊒T

    N⊒Target′ :
      ΔLT ∣ ΔR ∣ ρT ∣ []
        ⊢ N ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ qᵢ
          ⦂ applyTys (χsA ++ χsT) BV ⊒ᵐ BR
    N⊒Target′ =
      subst
        (λ X →
          ΔLT ∣ ΔR ∣ ρT ∣ []
            ⊢ N ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ qᵢ
              ⦂ X ⊒ᵐ BR)
        (sym (applyTys-++ χsA χsT BV))
        N⊒Target

    N-tail :
      ΔLT ∣ ΔR ∣ ρT ∣ []
        ⊢ N ⟨ applyCoercions (χsA ++ χsT) dₛ ⟩
          ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩
          ∶ qₒ ⦂ applyTys (χsA ++ χsT) Bₒ ⊒ᵐ BR
    N-tail =
      mediated-beta-cast-minus-tail (χsA ++ χsT)
        ΔLT-total≡
        ρT-total≡
        ρT-corr
        (fun-narrow-codomainᵐᶜ qᶜ)
        (d⊢ , dⁿ)
        qᵢ⊒′
        N⊒Target′
  in
  (keep ∷ χsA) ++ χsT ,
  N ⟨ applyCoercions χsT (applyCoercions χsA dₛ) ⟩ ,
  ΔLT ,
  ρT ,
  source-steps ,
  ΔLT-total≡ ,
  ρT-total≡ ,
  subst
    (λ c₀ →
      ΔLT ∣ ΔR ∣ ρT ∣ []
        ⊢ N ⟨ c₀ ⟩ ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩
          ∶ qₒ ⦂ applyTys (χsA ++ χsT) Bₒ ⊒ᵐ BR)
    (applyCoercions-++ χsA χsT dₛ)
    N-tail

mediated-dgg-beta-cast-value :
  ∀ {ΔL ΔR ρ L R V′ W′ c d pᵈ p q A A′ B B′} →
  Value L →
  No• L →
  Value R →
  No• R →
  Value V′ →
  Value W′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ L ⊒ V′ ⟨ c ↦ d ⟩ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ᵐ A′ ⇒ B′ →
  ΔL ∣ ΔR ∣ ρ ⊢ pᵈ ∶ᶜ A ⊒ᵐ A′ →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ R ⊒ W′ ∶ pᵈ ⦂ A ⊒ᵐ A′ →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ρ′ ] ∃[ C ] ∃[ D ] ∃[ r ]
    (L · R —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ρ′ ≡ applyLeftChanges χs ρ) ×
    (C ≡ applyTys χs B) ×
    (D ≡ B′) ×
    ΔL′ ∣ ΔR ∣ ρ′ ∣ []
      ⊢ N ⊒ (V′ · (W′ ⟨ c ⟩)) ⟨ d ⟩ ∶ r ⦂ C ⊒ᵐ D
mediated-dgg-beta-cast-value
    vL noL vR noR vV′ vW′ L⊒V′cd p-domainᶜ R⊒W′ =
  let
    χs , N , ΔL′ , ρ′ ,
      red , ΔL′≡ , ρ′≡ , N⊒target =
      mediated-dgg-beta-cast-value-shape
        vL noL vR noR vV′ vW′ L⊒V′cd refl p-domainᶜ R⊒W′
  in
  χs ,
  N ,
  ΔL′ ,
  ρ′ ,
  _ ,
  _ ,
  _ ,
  red ,
  ΔL′≡ ,
  ρ′≡ ,
  refl ,
  refl ,
  N⊒target
