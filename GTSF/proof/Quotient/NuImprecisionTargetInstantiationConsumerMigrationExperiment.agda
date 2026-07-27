module
  proof.Quotient.NuImprecisionTargetInstantiationConsumerMigrationExperiment
  where

-- File Charter:
--   * Shadow-migrates the positive target-instantiation consumers from the
--     live fused QTI constructor to exact creation and canonical transport.
--   * Constructs the smaller relation for the direct identity post-beta
--     context, canonically transported paired-lambda leaf, and ordinary and
--     identity-mode target-widening beta-instantiation roots.
--   * Reuses the strict exact-creation transport spine for pure universal
--     fusion; framed closing is tested in its own companion experiment.
--   * Does not import the live term-imprecision relation and contains no
--     postulate, hole, permissive option, termination bypass, or catch-all.

open import Agda.Builtin.Equality using (_≡_)
open import CastImprecisionShape using
  (widening; _⊢ᶜ_⦂_)
open import Coercions using
  (Coercion; Inert; ModeEnv; id-onlyᵈ; inst)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc; zero)
open import Imprecision using
  (ImpCtx; _ˣ⊑ˣ_; ⇑ᵢ; ⇑ᴿᵢ)
open import ImprecisionComposition using
  (ImprecisionShape; νˢ_; ⌊_⌋; _；_≋_)
open import ImprecisionWf using
  (ImpAssm; _∣_⊢_⊑_⊣_; ∀ⁱ_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuReduction using
  ( StoreChanges
  ; bind
  ; keep
  ; _—↠[_]_
  )
open import NuTermImprecision using
  ( CtxImp
  ; LiftRightStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-right
  )
open import NuTerms using
  (No•; Term; Value; Λ_; _⟨_⟩; ν; renameᵗᵐ)
open import TermTyping using
  (CastMode; SealModeStore★; _∣_∣_⊢_⦂_)
open import Types using
  (Renameᵗ; Ty; TyCtx; ★; wf★; `∀; ⇑ᵗ; renameᵗ)
open import Relation.Binary.PropositionalEquality using (sym)
open import
  proof.Core.Properties.TypeProperties
  using (TyRenameWf)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using
  ( rename-assm²ᵢ
  ; ⊑-rename-at²ᵢ
  ; ⊑-target-lift-rightᵢ
  )
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
  using
  ( target-instantiationᴿ
  ; _∣_∣_∣_∣_⊢ᴿ_⊑_⦂_⊑_∶_
  )
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using
  ( StoreImpPrefixᴿ
  ; TargetInstantiationCreation
  ; exact-creationᴱ
  ; target-instantiation-creation
  )
open import
  proof.Quotient.NuImprecisionTargetInstantiationTransportExperiment
  using (target-instantiation-endpoint-transportᴿ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef
  using (RelStoreEmbeddingⁱ)
open import
  proof.Target.Administration.NuImprecisionTargetPendingLambdaAllocationTraceProof
  using (target-pending-lambda-allocation-trace-proofᵀ)


direct-identity-post-beta-contextᴿ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {W W′ : Term} {B C D : Ty} {s : Coercion} {μ : ModeEnv}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ C ⊣ suc Δᴿ}
    {f : Φ ∣ Δᴸ ⊢ `∀ D ⊑ B ⊣ Δᴿ}
    {body-shape : ImprecisionShape}
    {γ⁺ : CtxImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  StoreImpPrefixᴿ ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ inst B s ∶ `∀ C ⊑ B →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ∀ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ⁺ ρᴿ⁺ →
  Value W →
  No• W →
  Value W′ →
  No• W′ →
  Inert s →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
    ⊢ᴿ W ⊑ W′ ⦂ D ⊑ C ∶ r →
  widening ⊢ᶜ inst B s ⦂ νˢ body-shape →
  ⌊ ∀ⁱ r ⌋ ； νˢ body-shape ≋ ⌊ f ⌋ →
  Δᴸ
    ∣ leftStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ⁺)
    ∣ [] ⊢ Λ W ⦂ `∀ D →
  suc Δᴿ
    ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ⁺)
    ∣ [] ⊢ W′ ⟨ s ⟩ ⦂ ⇑ᵗ B →
  ⇑ᴿᵢ Φ
    ∣ Δᴸ ∣ suc Δᴿ
    ∣ store-right zero ★ wf★ ∷ ρᴿ⁺ ∣ γ⁺
    ⊢ᴿ Λ W ⊑ W′ ⟨ s ⟩
    ⦂ `∀ D ⊑ ⇑ᵗ B
    ∶ ⊑-target-lift-rightᵢ f
direct-identity-post-beta-contextᴿ
    prefix mode seal★ inst⊑ liftρ liftρᴿ
    vW noW vW′ noW′ inert body
    inst-shape creation-square source-typing target-typing =
  target-instantiationᴿ
    (exact-creationᴱ
      (target-instantiation-creation
        prefix mode seal★ inst⊑ liftρ liftρᴿ
        vW noW vW′ noW′ inert body
        inst-shape creation-square source-typing target-typing))


data CanonicalTargetInstantiationLeafᴿ
    {Ψ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    (ρ : StoreImp Ψ Δᴸ Δᴿ) :
    (M M′ : Term) → (A A′ : Ty) →
    (p : Ψ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) → Set₁ where

  canonical-instantiation-leafᴿ :
    ∀ {Φ₀ : ImpCtx} {Θᴸ Θᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ₀ Θᴸ Θᴿ}
      {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
        (suc Θᴸ) (suc Θᴿ)}
      {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ₀) Θᴸ (suc Θᴿ)}
      {τ σ : Renameᵗ}
      {W W′ M M′ : Term} {A A′ B C D : Ty}
      {s : Coercion} {μ : ModeEnv}
      {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
        ∣ suc Θᴸ ⊢ D ⊑ C ⊣ suc Θᴿ}
      {f : Φ₀ ∣ Θᴸ ⊢ `∀ D ⊑ B ⊣ Θᴿ}
      {p : Ψ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {body-shape : ImprecisionShape} →
    (creation :
      TargetInstantiationCreation
        {Φ = Φ₀} {Δᴸ = Θᴸ} {Δᴿ = Θᴿ}
        {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ⁺}
        {W = W} {W′ = W′} {B = B} {C = C} {D = D}
        {s = s} {μ = μ} {r = r} {f = f}
        {body-shape = body-shape}
        (StoreImpPrefixᴿ ρ₀ ρ⁺)
        (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
          ∣ suc Θᴸ ∣ suc Θᴿ ∣ ρ∀ ∣ []
          ⊢ᴿ W ⊑ W′ ⦂ D ⊑ C ∶ r)) →
    (assm :
      ∀ {a : ImpAssm} → a ∈ ⇑ᴿᵢ Φ₀ →
        rename-assm²ᵢ τ σ a ∈ Ψ) →
    (hτ : TyRenameWf Θᴸ Δᴸ τ) →
    (hσ : TyRenameWf (suc Θᴿ) Δᴿ σ) →
    RelStoreEmbeddingⁱ τ σ
      (store-right zero ★ wf★ ∷ ρᴿ⁺) ρ →
    (source-eq : renameᵗᵐ τ (Λ W) ≡ M) →
    (target-eq : renameᵗᵐ σ (W′ ⟨ s ⟩) ≡ M′) →
    (source-type-eq : renameᵗ τ (`∀ D) ≡ A) →
    (target-type-eq : renameᵗ σ (⇑ᵗ B) ≡ A′) →
    ⊑-rename-at²ᵢ assm hτ hσ
      (sym source-type-eq) (sym target-type-eq)
      (⊑-target-lift-rightᵢ f) ≡ p →
    Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ A →
    Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ A′ →
    CanonicalTargetInstantiationLeafᴿ ρ M M′ A A′ p


canonical-target-instantiation-leaf-reconstructᴿ :
  ∀ {Ψ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Ψ Δᴸ Δᴿ}
    {M M′ : Term} {A A′ : Ty}
    {p : Ψ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  CanonicalTargetInstantiationLeafᴿ ρ M M′ A A′ p →
  Ψ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p
canonical-target-instantiation-leaf-reconstructᴿ
    (canonical-instantiation-leafᴿ
      creation assm hτ hσ store-embedding
      source-eq target-eq source-type-eq target-type-eq
      index-eq source-typing target-typing) =
  target-instantiation-endpoint-transportᴿ
    creation assm hτ hσ store-embedding
    source-eq target-eq source-type-eq target-type-eq
    index-eq source-typing target-typing


private
  post-beta-tail : StoreChanges
  post-beta-tail = bind ★ ∷ keep ∷ []


record TargetWideningBetaInstantiationOutcomeᴿ
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {W W′ : Term} {B D : Ty} {s : Coercion}
    {f : Φ ∣ Δᴸ ⊢ `∀ D ⊑ B ⊣ Δᴿ} : Set₁ where
  field
    target-tail :
      ν ★ (Λ W′) s —↠[ post-beta-tail ] W′ ⟨ s ⟩

    final-relation :
      ⇑ᴿᵢ Φ
        ∣ Δᴸ ∣ suc Δᴿ
        ∣ store-right zero ★ wf★ ∷ ρᴿ⁺ ∣ []
        ⊢ᴿ Λ W ⊑ W′ ⟨ s ⟩
        ⦂ `∀ D ⊑ ⇑ᵗ B
        ∶ ⊑-target-lift-rightᵢ f

open TargetWideningBetaInstantiationOutcomeᴿ public


target-widening-beta-instantiation-rootᴿ :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ ρ∀ ρᴿ⁺ W W′ B C D s μ r f
      body-shape} →
  StoreImpPrefixᴿ ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ inst B s ∶ `∀ C ⊑ B →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ∀ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ⁺ ρᴿ⁺ →
  Value W →
  No• W →
  Value W′ →
  No• W′ →
  Inert s →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
    ⊢ᴿ W ⊑ W′ ⦂ D ⊑ C ∶ r →
  widening ⊢ᶜ inst B s ⦂ νˢ body-shape →
  ⌊ ∀ⁱ r ⌋ ； νˢ body-shape ≋ ⌊ f ⌋ →
  Δᴸ
    ∣ leftStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ⁺)
    ∣ [] ⊢ Λ W ⦂ `∀ D →
  suc Δᴿ
    ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ⁺)
    ∣ [] ⊢ W′ ⟨ s ⟩ ⦂ ⇑ᵗ B →
  TargetWideningBetaInstantiationOutcomeᴿ
    {ρᴿ⁺ = ρᴿ⁺} {W = W} {W′ = W′}
    {B = B} {D = D} {s = s} {f = f}
target-widening-beta-instantiation-rootᴿ
    prefix mode seal★ inst⊑ liftρ liftρᴿ
    vW noW vW′ noW′ inert body
    inst-shape creation-square source-typing target-typing =
  record
    { target-tail =
        target-pending-lambda-allocation-trace-proofᵀ
          {cs = []} vW′ noW′
    ; final-relation =
        target-instantiationᴿ
          (exact-creationᴱ
            (target-instantiation-creation
              prefix mode seal★ inst⊑ liftρ liftρᴿ
              vW noW vW′ noW′ inert body
              inst-shape creation-square source-typing target-typing))
    }


target-id-widening-beta-instantiation-rootᴿ :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ ρ∀ ρᴿ⁺ W W′ B C D s r f
      body-shape} →
  StoreImpPrefixᴿ ρ₀ ρ⁺ →
  CastMode id-onlyᵈ →
  SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ₀) →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ inst B s ∶ `∀ C ⊑ B →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ∀ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ⁺ ρᴿ⁺ →
  Value W →
  No• W →
  Value W′ →
  No• W′ →
  Inert s →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
    ⊢ᴿ W ⊑ W′ ⦂ D ⊑ C ∶ r →
  widening ⊢ᶜ inst B s ⦂ νˢ body-shape →
  ⌊ ∀ⁱ r ⌋ ； νˢ body-shape ≋ ⌊ f ⌋ →
  Δᴸ
    ∣ leftStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ⁺)
    ∣ [] ⊢ Λ W ⦂ `∀ D →
  suc Δᴿ
    ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ⁺)
    ∣ [] ⊢ W′ ⟨ s ⟩ ⦂ ⇑ᵗ B →
  TargetWideningBetaInstantiationOutcomeᴿ
    {ρᴿ⁺ = ρᴿ⁺} {W = W} {W′ = W′}
    {B = B} {D = D} {s = s} {f = f}
target-id-widening-beta-instantiation-rootᴿ
    prefix mode seal★ inst⊑ liftρ liftρᴿ
    vW noW vW′ noW′ inert body
    inst-shape creation-square source-typing target-typing =
  target-widening-beta-instantiation-rootᴿ
    prefix mode seal★ inst⊑ liftρ liftρᴿ
    vW noW vW′ noW′ inert body
    inst-shape creation-square source-typing target-typing
