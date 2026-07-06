module proof.LeftChangeNarrowingSeparated where

-- File Charter:
--   * Shared left-store-change transport facts for separated-store narrowing.
--   * Collects function-coercion projections, cast-shape injectivity, and the
--     left-advancement surfaces used by beta simulation and the separated DGG.
--   * Keeps these helper obligations out of the larger simulation scripts so
--     Agda can cache them independently.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; map)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

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

  -- Sibling of `left-change-source-coercion-narrowing-dual` for the
  -- function-domain dual: transporting an arrow coercion across left
  -- store changes commutes with taking its domain dual.  Packaged with
  -- the arrow-reshaped transported typing so the `sim-beta` recursion
  -- sites can consume both at once.  Approved as an extension of this
  -- postulate family (2026-07-05); to be discharged together with the
  -- rest of the family.
  left-change-fun-coercion-narrowing :
    ∀ χs {ΔL ΔL′ ΔR ρ p q A A′ B B′ μ}
      (ΔL′≡ : ΔL′ ≡ applyTyCtxs χs ΔL)
      (ρ′-corr : StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ))
      (p↦q⊒ : μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q
                ∶ (A ⇒ B) ⊒ (A′ ⇒ B′)) →
    Σ[ e ∈ (μ ∣ ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ
              ⊢ applyCoercions χs p ↦ applyCoercions χs q
                ∶ (applyTys χs A ⇒ applyTys χs B)
                  ⊒ (A′ ⇒ B′)) ]
      fun-narrow-domain-dual e ≡
        applyCoercions χs (fun-narrow-domain-dual p↦q⊒)

-- The raw domain dual is independent of which typing evidence (and
-- which mode environment) it is computed from: it only inspects the
-- left widening witness, and `dualʷ-raw-determined` identifies the
-- dual across witnesses.
fun-narrow-domain-dual-determined :
  ∀ {μ₁ μ₂ ΔL₁ ΔR₁ ρ₁ ΔL₂ ΔR₂ ρ₂ p q
     A₁ A₁′ B₁ B₁′ A₂ A₂′ B₂ B₂′} →
  (e₁ : μ₁ ∣ ΔL₁ ∣ ΔR₁ ∣ ρ₁ ⊢ p ↦ q
          ∶ (A₁ ⇒ B₁) ⊒ (A₁′ ⇒ B₁′)) →
  (e₂ : μ₂ ∣ ΔL₂ ∣ ΔR₂ ∣ ρ₂ ⊢ p ↦ q
          ∶ (A₂ ⇒ B₂) ⊒ (A₂′ ⇒ B₂′)) →
  fun-narrow-domain-dual e₁ ≡ fun-narrow-domain-dual e₂
fun-narrow-domain-dual-determined
    (_ , _ , _ , _ , _ , (_ , cross (pʷ₁ ↦ⁿʷ _)) , _)
    (_ , _ , _ , _ , _ , (_ , cross (pʷ₂ ↦ⁿʷ _)) , _) =
  dualʷ-raw-determined normalᵃ pʷ₁ pʷ₂

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

------------------------------------------------------------------------
-- Composition-witness helpers
------------------------------------------------------------------------

-- Rewrite the three raw coercion indices of a composition witness in a
-- single step; keeps the `sim-beta` clause bodies small so Agda does
-- not carry three nested subst motives over the record type.
composed-index-raws-≡ :
  ∀ {ΔL ΔR ρ s t r s′ t′ r′ A B} →
  s ≡ s′ →
  t ≡ t′ →
  r ≡ r′ →
  ΔL ∣ ΔR ∣ ρ ⊢ s ⨟ t ≈ r ∶ A ⊒ B →
  ΔL ∣ ΔR ∣ ρ ⊢ s′ ⨟ t′ ≈ r′ ∶ A ⊒ B
composed-index-raws-≡ refl refl refl comp = comp

-- Domain-dual projection of an arrow-level composition: the three
-- factor typings of an incoming composition record, once pinned to
-- arrow endpoints, yield the composition of their domain duals at the
-- same shared mode environment.
fun-domain-dual-composed :
  ∀ {ν ΔL ΔR ρ cₛ dₛ pᵢ qᵢ pₒ qₒ Aₒ Bₒ AL BL AR BR} →
  (s⊒ : ν ∣ ΔL ∣ ΔR ∣ ρ ⊢ cₛ ↦ dₛ
          ∶ (Aₒ ⇒ Bₒ) ⊒ (AL ⇒ BL)) →
  (t⊒ : ν ∣ ΔL ∣ ΔR ∣ ρ ⊢ pᵢ ↦ qᵢ
          ∶ (AL ⇒ BL) ⊒ (AR ⇒ BR)) →
  (r⊒ : ν ∣ ΔL ∣ ΔR ∣ ρ ⊢ pₒ ↦ qₒ
          ∶ (Aₒ ⇒ Bₒ) ⊒ (AR ⇒ BR)) →
  ΔL ∣ ΔR ∣ ρ
    ⊢ fun-narrow-domain-dual s⊒ ⨟ fun-narrow-domain-dual t⊒
      ≈ fun-narrow-domain-dual r⊒ ∶ Aₒ ⊒ AR
fun-domain-dual-composed s⊒ t⊒ r⊒ =
  composed-index
    (separated-fun-domain-dual s⊒)
    (separated-fun-domain-dual t⊒)
    (separated-fun-domain-dual r⊒)

-- The full site witness for wrapping a `sim-beta` argument in the
-- source function cast's domain: the incoming arrow-level composition
-- record of the matched cast constructor, projected to domain duals.
-- Hoisted out of the `sim-beta` clause bodies deliberately — matching
-- the record and normalizing the dual equations inside those huge
-- clause contexts made elaboration blow past a 14G heap.
cast-fun-comp-domain-dual :
  ∀ {μ η ΔL ΔR ρ cₛ dₛ pᵢ qᵢ pₒ qₒ Aₒ Bₒ AL BL AR BR c d} →
  ΔL ∣ ΔR ∣ ρ ⊢ (cₛ ↦ dₛ) ⨟ (pᵢ ↦ qᵢ) ≈ (pₒ ↦ qₒ)
    ∶ (Aₒ ⇒ Bₒ) ⊒ (AR ⇒ BR) →
  (t⊒ : η ∣ ΔL ∣ ΔR ∣ ρ ⊢ cₛ ↦ dₛ
          ∶ (Aₒ ⇒ Bₒ) ⊒ (AL ⇒ BL)) →
  narrowing-dual t⊒ ≡ c ↦ d →
  (pᵢ↦qᵢᶜ : ΔL ∣ ΔR ∣ ρ ⊢ pᵢ ↦ qᵢ
              ∶ᶜ (AL ⇒ BL) ⊒ (AR ⇒ BR)) →
  (p↦q⊒ : μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ pₒ ↦ qₒ
            ∶ (Aₒ ⇒ Bₒ) ⊒ (AR ⇒ BR)) →
  ΔL ∣ ΔR ∣ ρ
    ⊢ c ⨟ fun-narrow-domain-dualᶜ pᵢ↦qᵢᶜ
      ≈ fun-narrow-domain-dual p↦q⊒ ∶ Aₒ ⊒ AR
-- A composition witness transports across left store changes
-- field-wise: the source-side transport for the first factor (its
-- target is the composition's middle type) and the plain transport for
-- the second factor and the composite.
left-change-composed-index :
  ∀ χs {ΔL ΔL′ ΔR ρ s t r A B} →
  ΔL′ ≡ applyTyCtxs χs ΔL →
  StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ) →
  ΔL ∣ ΔR ∣ ρ ⊢ s ⨟ t ≈ r ∶ A ⊒ B →
  ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ
    ⊢ applyCoercions χs s ⨟ applyCoercions χs t
      ≈ applyCoercions χs r ∶ applyTys χs A ⊒ B
left-change-composed-index χs ΔL′≡ corr
    (composed-index s⊒ t⊒ r⊒) =
  composed-index
    (left-change-source-coercion-narrowing χs ΔL′≡ corr s⊒)
    (left-change-coercion-narrowing χs ΔL′≡ corr t⊒)
    (left-change-coercion-narrowing χs ΔL′≡ corr r⊒)

-- Codomain projection of an arrow-level composition: unlike the
-- domain-dual case, the raw indices are syntactic codomains, so no
-- witness bridging is needed.  The middle type of the incoming record
-- is pinned from the s-factor's target equation.
cast-fun-comp-codomain :
  ∀ {η ΔL ΔR ρ cₛ dₛ pᵢ qᵢ pₒ qₒ A₀ B₀ A₁ B₁ A₂ B₂} →
  ΔL ∣ ΔR ∣ ρ ⊢ (cₛ ↦ dₛ) ⨟ (pᵢ ↦ qᵢ) ≈ (pₒ ↦ qₒ)
    ∶ (A₀ ⇒ B₀) ⊒ (A₂ ⇒ B₂) →
  (s⊒ : η ∣ ΔL ∣ ΔR ∣ ρ ⊢ cₛ ↦ dₛ
          ∶ (A₀ ⇒ B₀) ⊒ (A₁ ⇒ B₁)) →
  ΔL ∣ ΔR ∣ ρ ⊢ dₛ ⨟ qᵢ ≈ qₒ ∶ B₀ ⊒ B₂
cast-fun-comp-codomain {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {cₛ = cₛ} {dₛ = dₛ} {pᵢ = pᵢ} {qᵢ = qᵢ}
    {A₀ = A₀} {B₀ = B₀} {A₁ = A₁} {B₁ = B₁}
    {A₂ = A₂} {B₂ = B₂}
    (composed-index {midTy = midᵏ} {νᶜᵒᵐᵖ = νᵏ} s⊒ᵏ t⊒ᵏ r⊒ᵏ)
    s⊒ =
  let
    midᵏ≡ : midᵏ ≡ A₁ ⇒ B₁
    midᵏ≡ =
      let
        _ , _ , sᵏtgt , _ , _ , _ , _ = s⊒ᵏ
        _ , _ , stgt , _ , _ , _ , _ = s⊒
      in
      trans (sym sᵏtgt) stgt

    s⊒ᵏ′ :
      νᵏ ∣ ΔL ∣ ΔR ∣ ρ ⊢ cₛ ↦ dₛ
        ∶ (A₀ ⇒ B₀) ⊒ (A₁ ⇒ B₁)
    s⊒ᵏ′ =
      subst
        (λ X → νᵏ ∣ ΔL ∣ ΔR ∣ ρ ⊢ cₛ ↦ dₛ ∶ (A₀ ⇒ B₀) ⊒ X)
        midᵏ≡
        s⊒ᵏ

    t⊒ᵏ′ :
      νᵏ ∣ ΔL ∣ ΔR ∣ ρ ⊢ pᵢ ↦ qᵢ
        ∶ (A₁ ⇒ B₁) ⊒ (A₂ ⇒ B₂)
    t⊒ᵏ′ =
      subst
        (λ X → νᵏ ∣ ΔL ∣ ΔR ∣ ρ ⊢ pᵢ ↦ qᵢ ∶ X ⊒ (A₂ ⇒ B₂))
        midᵏ≡
        t⊒ᵏ
  in
  composed-index
    (separated-fun-codomain s⊒ᵏ′)
    (separated-fun-codomain t⊒ᵏ′)
    (separated-fun-codomain r⊒ᵏ)

-- Variant for the other wrap direction: all three output raw indices
-- are `fun-narrow-domain-dual` of caller-supplied arrow evidence, so
-- no term-level cast equation is needed.  The middle type of the
-- incoming record is pinned from the s-factor's target equation.
cast-fun-comp-domain-dual₂ :
  ∀ {μ₁ μ₂ η ΔL ΔR ρ c d pₒ qₒ pᵢ qᵢ AL BL Aₒ Bₒ AR BR} →
  ΔL ∣ ΔR ∣ ρ ⊢ (c ↦ d) ⨟ (pₒ ↦ qₒ) ≈ (pᵢ ↦ qᵢ)
    ∶ (AL ⇒ BL) ⊒ (AR ⇒ BR) →
  (s⊒ : η ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ↦ d
          ∶ (AL ⇒ BL) ⊒ (Aₒ ⇒ Bₒ)) →
  (t⊒ : μ₁ ∣ ΔL ∣ ΔR ∣ ρ ⊢ pₒ ↦ qₒ
          ∶ (Aₒ ⇒ Bₒ) ⊒ (AR ⇒ BR)) →
  (r⊒ : μ₂ ∣ ΔL ∣ ΔR ∣ ρ ⊢ pᵢ ↦ qᵢ
          ∶ (AL ⇒ BL) ⊒ (AR ⇒ BR)) →
  ΔL ∣ ΔR ∣ ρ
    ⊢ fun-narrow-domain-dual s⊒ ⨟ fun-narrow-domain-dual t⊒
      ≈ fun-narrow-domain-dual r⊒ ∶ AL ⊒ AR
cast-fun-comp-domain-dual₂ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {c = c} {d = d} {pₒ = pₒ} {qₒ = qₒ}
    {AL = AL} {BL = BL} {Aₒ = Aₒ} {Bₒ = Bₒ}
    {AR = AR} {BR = BR}
    (composed-index {midTy = midᵏ} {νᶜᵒᵐᵖ = νᵏ} s⊒ᵏ t⊒ᵏ r⊒ᵏ)
    s⊒ t⊒ r⊒ =
  let
    midᵏ≡ : midᵏ ≡ Aₒ ⇒ Bₒ
    midᵏ≡ =
      let
        _ , _ , sᵏtgt , _ , _ , _ , _ = s⊒ᵏ
        _ , _ , stgt , _ , _ , _ , _ = s⊒
      in
      trans (sym sᵏtgt) stgt

    s⊒ᵏ′ :
      νᵏ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ↦ d
        ∶ (AL ⇒ BL) ⊒ (Aₒ ⇒ Bₒ)
    s⊒ᵏ′ =
      subst
        (λ X → νᵏ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ↦ d ∶ (AL ⇒ BL) ⊒ X)
        midᵏ≡
        s⊒ᵏ

    t⊒ᵏ′ :
      νᵏ ∣ ΔL ∣ ΔR ∣ ρ ⊢ pₒ ↦ qₒ
        ∶ (Aₒ ⇒ Bₒ) ⊒ (AR ⇒ BR)
    t⊒ᵏ′ =
      subst
        (λ X → νᵏ ∣ ΔL ∣ ΔR ∣ ρ ⊢ pₒ ↦ qₒ ∶ X ⊒ (AR ⇒ BR))
        midᵏ≡
        t⊒ᵏ
  in
  composed-index-raws-≡
    (fun-narrow-domain-dual-determined s⊒ᵏ′ s⊒)
    (fun-narrow-domain-dual-determined t⊒ᵏ′ t⊒)
    (fun-narrow-domain-dual-determined r⊒ᵏ r⊒)
    (fun-domain-dual-composed s⊒ᵏ′ t⊒ᵏ′ r⊒ᵏ)

cast-fun-comp-domain-dual {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ}
    {cₛ = cₛ} {dₛ = dₛ} {pᵢ = pᵢ} {qᵢ = qᵢ}
    {Aₒ = Aₒ} {Bₒ = Bₒ} {AL = AL} {BL = BL}
    {AR = AR} {BR = BR}
    (composed-index {midTy = midᵏ} {νᶜᵒᵐᵖ = νᵏ} s⊒ᵏ t⊒ᵏ r⊒ᵏ)
    t⊒@(_ , _ , _ , _ , _ , (_ , cross (cₛʷ ↦ⁿʷ _)) , _)
    cast-eq pᵢ↦qᵢᶜ p↦q⊒ =
  let
    midᵏ≡ : midᵏ ≡ AL ⇒ BL
    midᵏ≡ =
      let
        _ , tᵏsrc , _ , _ , _ , _ , _ = t⊒ᵏ
        _ , pᵢsrc , _ , _ , _ , _ , _ = pᵢ↦qᵢᶜ
      in
      trans (sym tᵏsrc) pᵢsrc

    s⊒ᵏ′ :
      νᵏ ∣ ΔL ∣ ΔR ∣ ρ ⊢ cₛ ↦ dₛ
        ∶ (Aₒ ⇒ Bₒ) ⊒ (AL ⇒ BL)
    s⊒ᵏ′ =
      subst
        (λ X → νᵏ ∣ ΔL ∣ ΔR ∣ ρ ⊢ cₛ ↦ dₛ ∶ (Aₒ ⇒ Bₒ) ⊒ X)
        midᵏ≡
        s⊒ᵏ

    t⊒ᵏ′ :
      νᵏ ∣ ΔL ∣ ΔR ∣ ρ ⊢ pᵢ ↦ qᵢ
        ∶ (AL ⇒ BL) ⊒ (AR ⇒ BR)
    t⊒ᵏ′ =
      subst
        (λ X → νᵏ ∣ ΔL ∣ ΔR ∣ ρ ⊢ pᵢ ↦ qᵢ ∶ X ⊒ (AR ⇒ BR))
        midᵏ≡
        t⊒ᵏ
  in
  composed-index-raws-≡
    (trans
      (fun-narrow-domain-dual-determined s⊒ᵏ′ t⊒)
      (↦-left-injective cast-eq))
    (fun-narrow-domain-dual-determined t⊒ᵏ′ pᵢ↦qᵢᶜ)
    (fun-narrow-domain-dual-determined r⊒ᵏ p↦q⊒)
    (fun-domain-dual-composed s⊒ᵏ′ t⊒ᵏ′ r⊒ᵏ)
