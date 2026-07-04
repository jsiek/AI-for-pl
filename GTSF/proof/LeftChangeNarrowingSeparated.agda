module proof.LeftChangeNarrowingSeparated where

-- File Charter:
--   * Shared left-store-change transport facts for separated-store narrowing.
--   * Collects function-coercion projections, cast-shape injectivity, and the
--     left-advancement surfaces used by beta simulation and the separated DGG.
--   * Keeps these helper obligations out of the larger simulation scripts so
--     Agda can cache them independently.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; map)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; trans)

open import Types
open import Coercions
open import NarrowWiden using
  ( cross
  ; dualⁿ
  ; dualʷ
  ; Widening
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
  renaming (_↦_ to _↦ⁿʷ_)
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import TermNarrowingSeparated
open import proof.Catchup using (runtime-⇑ᵗᵐ)
open import proof.CatchupSeparated using
  ( applyLeftChanges
  )
open import proof.CoercionProperties using
  ( coercion-src-tgtᵐ
  ; dualActionOk-normal
  ; dualStoreAt-normal
  )
open import proof.NarrowWidenProperties using
  ( dualʷ-flips-typingᵐ
  )
open import proof.ReductionProperties using
  ( applyCoercions
  ; applyCoercions-dual
  )

applyTerm-preserves-RuntimeOK :
  ∀ χ {M} →
  RuntimeOK M →
  RuntimeOK (applyTerm χ M)
applyTerm-preserves-RuntimeOK keep okM = okM
applyTerm-preserves-RuntimeOK (bind A) okM = runtime-⇑ᵗᵐ okM

applyTerms-preserves-RuntimeOK :
  ∀ χs {M} →
  RuntimeOK M →
  RuntimeOK (applyTerms χs M)
applyTerms-preserves-RuntimeOK [] okM = okM
applyTerms-preserves-RuntimeOK (χ ∷ χs) okM =
  applyTerms-preserves-RuntimeOK χs (applyTerm-preserves-RuntimeOK χ okM)

applyTys-⇒ :
  ∀ χs A B →
  applyTys χs (A ⇒ B) ≡ applyTys χs A ⇒ applyTys χs B
applyTys-⇒ [] A B = refl
applyTys-⇒ (keep ∷ χs) A B = applyTys-⇒ χs A B
applyTys-⇒ (bind C ∷ χs) A B = applyTys-⇒ χs (⇑ᵗ A) (⇑ᵗ B)

applyCoercions-↦ :
  ∀ χs p q →
  applyCoercions χs (p ↦ q) ≡ applyCoercions χs p ↦ applyCoercions χs q
applyCoercions-↦ [] p q = refl
applyCoercions-↦ (keep ∷ χs) p q = applyCoercions-↦ χs p q
applyCoercions-↦ (bind A ∷ χs) p q =
  applyCoercions-↦ χs (⇑ᶜ p) (⇑ᶜ q)

applyCoercions-dual-applyCoercions :
  ∀ χs χs′ p →
  applyCoercions χs′ (applyCoercions χs (- p)) ≡
    - applyCoercions χs′ (applyCoercions χs p)
applyCoercions-dual-applyCoercions χs χs′ p =
  trans
    (cong (applyCoercions χs′) (applyCoercions-dual χs p))
    (applyCoercions-dual χs′ (applyCoercions χs p))

applyLeftCtxEntry : StoreChanges → CtxCorrEntry → CtxCorrEntry
applyLeftCtxEntry χs (ctx-entry A B p) =
  ctx-entry (applyTys χs A) B (applyCoercions χs p)

applyLeftCtx : StoreChanges → CtxCorr → CtxCorr
applyLeftCtx χs γ = map (applyLeftCtxEntry χs) γ

no•-cast-inv : ∀ {M c} → No• (M ⟨ c ⟩) → No• M
no•-cast-inv (no•-⟨⟩ noM) = noM

⟨⟩-term-injective :
  ∀ {M N : Term} {c d : Coercion} →
  M ⟨ c ⟩ ≡ N ⟨ d ⟩ →
  M ≡ N
⟨⟩-term-injective refl = refl

⟨⟩-coercion-injective :
  ∀ {M N : Term} {c d : Coercion} →
  M ⟨ c ⟩ ≡ N ⟨ d ⟩ →
  c ≡ d
⟨⟩-coercion-injective refl = refl

widen-fun-domainᵐ :
  ∀ {μ Δ Σ c d A A′ B B′} →
  μ ∣ Δ ∣ Σ ⊢ c ↦ d ∶ A ⇒ B ⊑ A′ ⇒ B′ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A′ ⊒ A
widen-fun-domainᵐ (cast-fun c⊢ _ , cross (cⁿ ↦ⁿʷ _)) = c⊢ , cⁿ

narrow-fun-codomainᵐ :
  ∀ {μ Δ Σ c d A A′ B B′} →
  μ ∣ Δ ∣ Σ ⊢ c ↦ d ∶ A ⇒ B ⊒ A′ ⇒ B′ →
  μ ∣ Δ ∣ Σ ⊢ d ∶ B ⊒ B′
narrow-fun-codomainᵐ (cast-fun _ d⊢ , cross (_ ↦ⁿʷ dⁿ)) = d⊢ , dⁿ

separated-fun-codomain :
  ∀ {μ ΔL ΔR ρ p q A A′ B B′} →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ A ⇒ B ⊒ A′ ⇒ B′ →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ q ∶ B ⊒ B′
separated-fun-codomain
    (stores , _ , _ , wf⇒ _ hB , wf⇒ _ hB′ ,
      (cast-fun _ q⊢L , cross (_ ↦ⁿʷ qⁿL)) ,
      (cast-fun _ q⊢R , cross (_ ↦ⁿʷ qⁿR))) =
  stores ,
  proj₁ (coercion-src-tgtᵐ q⊢L) ,
  proj₂ (coercion-src-tgtᵐ q⊢L) ,
  hB ,
  hB′ ,
  (q⊢L , qⁿL) ,
  (q⊢R , qⁿR)

↦-codomain : Coercion → Coercion
↦-codomain (id A) = id A
↦-codomain (c ︔ d) = c ︔ d
↦-codomain (c ↦ d) = d
↦-codomain (`∀ c) = `∀ c
↦-codomain (G !) = G !
↦-codomain (G ？) = G ？
↦-codomain (seal A α) = seal A α
↦-codomain (unseal α A) = unseal α A
↦-codomain (gen A c) = gen A c
↦-codomain (inst B c) = inst B c

↦-right-injective :
  ∀ {c c′ d d′ : Coercion} →
  c ↦ d ≡ c′ ↦ d′ →
  d ≡ d′
↦-right-injective eq = cong ↦-codomain eq

↦-domain : Coercion → Coercion
↦-domain (id A) = id A
↦-domain (c ︔ d) = c ︔ d
↦-domain (c ↦ d) = c
↦-domain (`∀ c) = `∀ c
↦-domain (G !) = G !
↦-domain (G ？) = G ？
↦-domain (seal A α) = seal A α
↦-domain (unseal α A) = unseal α A
↦-domain (gen A c) = gen A c
↦-domain (inst B c) = inst B c

↦-left-injective :
  ∀ {c c′ d d′ : Coercion} →
  c ↦ d ≡ c′ ↦ d′ →
  c ≡ c′
↦-left-injective eq = cong ↦-domain eq

separated-left-coercionᵐ :
  ∀ {μ ΔL ΔR ρ c A B} →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ A ⊒ B →
  μ ∣ ΔL ∣ leftStore ρ ⊢ c ∶ A ⊒ B
separated-left-coercionᵐ (_ , _ , _ , _ , _ , c⊒L , _) = c⊒L

separated-right-coercionᵐ :
  ∀ {μ ΔL ΔR ρ c A B} →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ A ⊒ B →
  μ ∣ ΔR ∣ rightStore ρ ⊢ c ∶ A ⊒ B
separated-right-coercionᵐ (_ , _ , _ , _ , _ , _ , c⊒R) = c⊒R

postulate
  left-change-term-narrowing :
    ∀ χs {ΔL ΔL′ ΔR ρ γ M M′ p A B} →
    ΔL′ ≡ applyTyCtxs χs ΔL →
    StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ) →
    ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
    ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ ∣ applyLeftCtx χs γ
      ⊢ applyTerms χs M ⊒ M′ ∶ applyCoercions χs p
        ⦂ applyTys χs A ⊒ B

  left-change-coercion-narrowing :
    ∀ χs {ΔL ΔL′ ΔR ρ c A B μ} →
    ΔL′ ≡ applyTyCtxs χs ΔL →
    StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ) →
    μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ A ⊒ B →
    μ ∣ ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ
      ⊢ applyCoercions χs c ∶ applyTys χs A ⊒ B

  left-change-source-coercion-narrowing :
    ∀ χs {ΔL ΔL′ ΔR ρ c A B μ} →
    ΔL′ ≡ applyTyCtxs χs ΔL →
    StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ) →
    μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ A ⊒ B →
    μ ∣ ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ
      ⊢ applyCoercions χs c ∶ applyTys χs A ⊒ applyTys χs B

  left-change-source-coercion-narrowing-dual :
    ∀ χs {ΔL ΔL′ ΔR ρ c A B μ}
      (ΔL′≡ : ΔL′ ≡ applyTyCtxs χs ΔL)
      (ρ′-corr : StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ))
      (c⊒ : μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ A ⊒ B) →
    narrowing-dual
      (left-change-source-coercion-narrowing χs ΔL′≡ ρ′-corr c⊒)
    ≡ applyCoercions χs (narrowing-dual c⊒)

  dualʷ-raw-determined :
    ∀ η {c} (cʷ₁ cʷ₂ : Widening c) →
    proj₁ (dualʷ η cʷ₁) ≡ proj₁ (dualʷ η cʷ₂)

  dualʷ-involutive-raw :
    ∀ {c} (cʷ : Widening c) →
    proj₁ (dualⁿ normalᵃ (proj₂ (dualʷ normalᵃ cʷ))) ≡ c

separated-fun-domain-dual :
  ∀ {μ ΔL ΔR ρ p q A A′ B B′} →
  (p↦q : μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ A ⇒ B ⊒ A′ ⇒ B′) →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ fun-narrow-domain-dual p↦q ∶ A ⊒ A′
separated-fun-domain-dual {μ = μ} {ΔR = ΔR} {ρ = ρ}
    {A = A} {A′ = A′}
    (stores , _ , _ , wf⇒ hA hB , wf⇒ hA′ hB′ ,
      (cast-fun p⊢L _ , cross (pʷL ↦ⁿʷ _)) ,
      (cast-fun p⊢R _ , cross (pʷR ↦ⁿʷ _))) =
  let
    pᵈ⊒L =
      dualʷ-flips-typingᵐ
        {η = normalᵃ}
        dualActionOk-normal
        dualStoreAt-normal
        (leftStore-wf stores)
        (p⊢L , pʷL)

    pᵈ⊒R =
      dualʷ-flips-typingᵐ
        {η = normalᵃ}
        dualActionOk-normal
        dualStoreAt-normal
        (rightStore-wf stores)
        (p⊢R , pʷR)
  in
  stores ,
  proj₁ (coercion-src-tgtᵐ (proj₁ pᵈ⊒L)) ,
  proj₂ (coercion-src-tgtᵐ (proj₁ pᵈ⊒L)) ,
  hA ,
  hA′ ,
  pᵈ⊒L ,
  subst
    (λ p → μ ∣ ΔR ∣ rightStore ρ ⊢ p ∶ A ⊒ A′)
    (dualʷ-raw-determined normalᵃ pʷR pʷL)
    pᵈ⊒R

advance-left-term-narrowing :
  ∀ χs {ΔL ΔL′ ΔR ρ M M′ p A B} →
  ΔL′ ≡ applyTyCtxs χs ΔL →
  StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ) →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
    ⊢ applyTerms χs M ⊒ M′ ∶ applyCoercions χs p
      ⦂ applyTys χs A ⊒ B
advance-left-term-narrowing χs ΔL′≡ ρ′-corr M⊒M′ =
  left-change-term-narrowing χs ΔL′≡ ρ′-corr M⊒M′

advance-left-function-term-narrowing :
  ∀ χs {ΔL ΔL′ ΔR ρ W W′ p q A A′ B B′} →
  ΔL′ ≡ applyTyCtxs χs ΔL →
  StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ) →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ W ⊒ W′ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ A′ ⇒ B′ →
  ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
    ⊢ applyTerms χs W ⊒ W′
      ∶ applyCoercions χs p ↦ applyCoercions χs q
      ⦂ applyTys χs A ⇒ applyTys χs B ⊒ A′ ⇒ B′
advance-left-function-term-narrowing χs {p = p} {q = q} {A = A}
    {B = B} ΔL′≡ ρ′-corr W⊒W′ =
  subst
    (λ c →
      _ ∣ _ ∣ _ ∣ [] ⊢ _ ⊒ _ ∶ c
        ⦂ applyTys χs A ⇒ applyTys χs B ⊒ _)
    (applyCoercions-↦ χs p q)
    (subst
      (λ C →
        _ ∣ _ ∣ _ ∣ [] ⊢ _ ⊒ _ ∶ applyCoercions χs (p ↦ q)
          ⦂ C ⊒ _)
      (applyTys-⇒ χs A B)
      (advance-left-term-narrowing χs ΔL′≡ ρ′-corr W⊒W′))

advance-left-lambda-narrowing :
  ∀ χs {ΔL ΔL′ ΔR ρ W N′ p q A A′ B B′} →
  ΔL′ ≡ applyTyCtxs χs ΔL →
  StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ) →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ W ⊒ ƛ N′ ∶ p ↦ q
    ⦂ A ⇒ B ⊒ A′ ⇒ B′ →
  ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
    ⊢ applyTerms χs W ⊒ ƛ N′
      ∶ applyCoercions χs p ↦ applyCoercions χs q
      ⦂ applyTys χs A ⇒ applyTys χs B ⊒ A′ ⇒ B′
advance-left-lambda-narrowing χs {p = p} {q = q} {A = A} {B = B}
    ΔL′≡ ρ′-corr W⊒ƛ =
  subst
    (λ c →
      _ ∣ _ ∣ _ ∣ [] ⊢ _ ⊒ _ ∶ c
        ⦂ applyTys χs A ⇒ applyTys χs B ⊒ _)
    (applyCoercions-↦ χs p q)
    (subst
      (λ C →
        _ ∣ _ ∣ _ ∣ [] ⊢ _ ⊒ _ ∶ applyCoercions χs (p ↦ q)
          ⦂ C ⊒ _)
      (applyTys-⇒ χs A B)
      (advance-left-term-narrowing χs ΔL′≡ ρ′-corr W⊒ƛ))
