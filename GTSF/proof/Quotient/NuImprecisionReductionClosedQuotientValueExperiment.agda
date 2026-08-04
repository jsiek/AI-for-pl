module
  proof.Quotient.NuImprecisionReductionClosedQuotientValueExperiment
  where

-- File Charter:
--   * Classifies source and target Value endpoints of every constructor in the
--     independent smaller ordinary term-imprecision relation.
--   * Excludes application, type application, primitive-operation, and `ν`
--     outer forms by indexed Value inversion.
--   * Threads Value classification through proof-only allocation prefixes and
--     one-sided term wrappers, and identifies inert outer casts.
--   * Classifies the sole embedded target-instantiation creation case and
--     derives value/no-step facts for exact and composed embeddings.
--   * Contains no legacy term-imprecision judgment, world-coherent dispatcher,
--     postulate, hole, permissive option, termination bypass, or catch-all.

open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (_—→[_]_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  )
open import NuTerms using
  (Term; Value; Λ_; _⟨_⟩; renameᵗᵐ)
open import Types using (Renameᵗ; Ty; TyCtx)
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-Value)
open import proof.DGG.Core.NuPreservation using (value-no-step)
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
  using
  ( blame⊑ᴿ
  ; x⊑xᴿ
  ; ƛ⊑ƛᴿ
  ; _·ᴿ_
  ; Λ⊑Λᴿ
  ; Λ⊑ᴿ
  ; α⊑αᴿ
  ; α⊑ᴿ
  ; ν⊑νᴿ
  ; ν⊑ᴿ
  ; κ⊑κᴿ
  ; _⊕ᴿ[_]_
  ; gen⊑groundᴿ
  ; cast⊒⊑ᴿ
  ; cast⊑⊑ᴿ
  ; ⊑cast⊒ᴿ
  ; ⊑cast⊑ᴿ
  ; conv↑⊑ᴿ
  ; conv↓⊑ᴿ
  ; ⊑conv↑ᴿ
  ; ⊑conv↓ᴿ
  ; paired-revealᴿ
  ; paired-concealᴿ
  ; target-instantiationᴿ
  ; closeᴿ
  ; paired-wideningᴿ
  ; paired-downᴿ
  ; _∣_∣_∣_∣_⊢ᴿ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴿᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using (TargetInstantiationCreation)


data SmallerSourceValueClassᴿ : Set where
  source-functionᴿ : SmallerSourceValueClassᴿ
  source-universalᴿ : SmallerSourceValueClassᴿ
  source-constantᴿ : SmallerSourceValueClassᴿ
  source-inert-castᴿ : SmallerSourceValueClassᴿ
  source-creationᴿ : SmallerSourceValueClassᴿ


data SmallerTargetValueClassᴿ : Set where
  target-blame-relatedᴿ : SmallerTargetValueClassᴿ
  target-functionᴿ : SmallerTargetValueClassᴿ
  target-universalᴿ : SmallerTargetValueClassᴿ
  target-constantᴿ : SmallerTargetValueClassᴿ
  target-groundᴿ : SmallerTargetValueClassᴿ
  target-inert-castᴿ : SmallerTargetValueClassᴿ
  target-creationᴿ : SmallerTargetValueClassᴿ


smaller-source-value-classᴿ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Value M →
  SmallerSourceValueClassᴿ
smaller-source-value-classᴿ (blame⊑ᴿ M′⊢) ()
smaller-source-value-classᴿ (x⊑xᴿ x∈) ()
smaller-source-value-classᴿ (ƛ⊑ƛᴿ hA hA′ N⊑N′) vƛ =
  source-functionᴿ
smaller-source-value-classᴿ (L⊑L′ ·ᴿ M⊑M′) ()
smaller-source-value-classᴿ
    (Λ⊑Λᴿ liftρ liftγ vV vV′ V⊑V′) vΛ =
  source-universalᴿ
smaller-source-value-classᴿ
    (Λ⊑ᴿ occ liftρ liftγ vV V⊑N′) vΛ =
  source-universalᴿ
smaller-source-value-classᴿ
    (α⊑αᴿ vL noL vL′ noL′ A⇑⊑B⇑ liftρ liftγ
      L⊑L′ allocation-prefix L•⊢ L′•⊢) ()
smaller-source-value-classᴿ
    (α⊑ᴿ vL noL h⇑A liftρ liftγ L⊑N′
      allocation-prefix L•⊢ N′⊢) ()
smaller-source-value-classᴿ
    (ν⊑νᴿ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑ liftρ liftγ
      N⊑N′ replace) ()
smaller-source-value-classᴿ
    (ν⊑ᴿ hA h⇑A s↑ liftρ liftγ N⊑N′ replace) ()
smaller-source-value-classᴿ κ⊑κᴿ vκ =
  source-constantᴿ
smaller-source-value-classᴿ (L⊑L′ ⊕ᴿ[ op ] M⊑M′) ()
smaller-source-value-classᴿ
    (gen⊑groundᴿ mode seal★ c⊒ ground vV vW W⊢ V⊑Wtag q)
    (vV′ ⟨ inert ⟩) =
  source-inert-castᴿ
smaller-source-value-classᴿ
    (cast⊒⊑ᴿ mode seal★ c⊒ M⊑M′ q shape comp)
    (vM ⟨ inert ⟩) =
  source-inert-castᴿ
smaller-source-value-classᴿ
    (cast⊑⊑ᴿ mode seal★ c⊑ M⊑M′ q shape comp)
    (vM ⟨ inert ⟩) =
  source-inert-castᴿ
smaller-source-value-classᴿ
    (⊑cast⊒ᴿ mode′ seal★′ c′⊒ M⊑M′ q shape comp) vM =
  smaller-source-value-classᴿ M⊑M′ vM
smaller-source-value-classᴿ
    (⊑cast⊑ᴿ mode′ seal★′ c′⊑ M⊑M′ q shape comp) vM =
  smaller-source-value-classᴿ M⊑M′ vM
smaller-source-value-classᴿ
    (conv↑⊑ᴿ c↑ M⊑M′ q replace) (vM ⟨ inert ⟩) =
  source-inert-castᴿ
smaller-source-value-classᴿ
    (conv↓⊑ᴿ c↓ M⊑M′ q replace) (vM ⟨ inert ⟩) =
  source-inert-castᴿ
smaller-source-value-classᴿ
    (⊑conv↑ᴿ c′↑ M⊑M′ q replace) vM =
  smaller-source-value-classᴿ M⊑M′ vM
smaller-source-value-classᴿ
    (⊑conv↓ᴿ c′↓ M⊑M′ q replace) vM =
  smaller-source-value-classᴿ M⊑M′ vM
smaller-source-value-classᴿ
    (paired-revealᴿ corresponds c↑ c′↑ replace M⊑M′)
    (vM ⟨ inert ⟩) =
  source-inert-castᴿ
smaller-source-value-classᴿ
    (paired-concealᴿ corresponds c↓ c′↓ replace M⊑M′)
    (vM ⟨ inert ⟩) =
  source-inert-castᴿ
smaller-source-value-classᴿ
    (target-instantiationᴿ embedded) vΛ =
  source-creationᴿ
smaller-source-value-classᴿ
    (closeᴿ M⊑M′ widening-pair
      u-shape u′-shape square compatible)
    (vM ⟨ inert ⟩) =
  source-inert-castᴿ
smaller-source-value-classᴿ
    (paired-wideningᴿ
      mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
      left-square right-square compatible M⊑M′)
    (vM ⟨ inert ⟩) =
  source-inert-castᴿ


smaller-target-value-classᴿ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Value M′ →
  SmallerTargetValueClassᴿ
smaller-target-value-classᴿ (blame⊑ᴿ M′⊢) vM′ =
  target-blame-relatedᴿ
smaller-target-value-classᴿ (x⊑xᴿ x∈) ()
smaller-target-value-classᴿ (ƛ⊑ƛᴿ hA hA′ N⊑N′) vƛ =
  target-functionᴿ
smaller-target-value-classᴿ (L⊑L′ ·ᴿ M⊑M′) ()
smaller-target-value-classᴿ
    (Λ⊑Λᴿ liftρ liftγ vV vV′ V⊑V′) vΛ =
  target-universalᴿ
smaller-target-value-classᴿ
    (Λ⊑ᴿ occ liftρ liftγ vV V⊑N′) vN′ =
  smaller-target-value-classᴿ V⊑N′ vN′
smaller-target-value-classᴿ
    (α⊑αᴿ vL noL vL′ noL′ A⇑⊑B⇑ liftρ liftγ
      L⊑L′ allocation-prefix L•⊢ L′•⊢) ()
smaller-target-value-classᴿ
    (α⊑ᴿ vL noL h⇑A liftρ liftγ L⊑N′
      allocation-prefix L•⊢ N′⊢) vN′ =
  smaller-target-value-classᴿ L⊑N′ vN′
smaller-target-value-classᴿ
    (ν⊑νᴿ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑ liftρ liftγ
      N⊑N′ replace) ()
smaller-target-value-classᴿ
    (ν⊑ᴿ hA h⇑A s↑ liftρ liftγ N⊑N′ replace) vN′ =
  smaller-target-value-classᴿ N⊑N′ vN′
smaller-target-value-classᴿ κ⊑κᴿ vκ =
  target-constantᴿ
smaller-target-value-classᴿ (L⊑L′ ⊕ᴿ[ op ] M⊑M′) ()
smaller-target-value-classᴿ
    (gen⊑groundᴿ mode seal★ c⊒ ground vV vW W⊢ V⊑Wtag q)
    vW′ =
  target-groundᴿ
smaller-target-value-classᴿ
    (cast⊒⊑ᴿ mode seal★ c⊒ M⊑M′ q shape comp) vM′ =
  smaller-target-value-classᴿ M⊑M′ vM′
smaller-target-value-classᴿ
    (cast⊑⊑ᴿ mode seal★ c⊑ M⊑M′ q shape comp) vM′ =
  smaller-target-value-classᴿ M⊑M′ vM′
smaller-target-value-classᴿ
    (⊑cast⊒ᴿ mode′ seal★′ c′⊒ M⊑M′ q shape comp)
    (vM′ ⟨ inert ⟩) =
  target-inert-castᴿ
smaller-target-value-classᴿ
    (⊑cast⊑ᴿ mode′ seal★′ c′⊑ M⊑M′ q shape comp)
    (vM′ ⟨ inert ⟩) =
  target-inert-castᴿ
smaller-target-value-classᴿ
    (conv↑⊑ᴿ c↑ M⊑M′ q replace) vM′ =
  smaller-target-value-classᴿ M⊑M′ vM′
smaller-target-value-classᴿ
    (conv↓⊑ᴿ c↓ M⊑M′ q replace) vM′ =
  smaller-target-value-classᴿ M⊑M′ vM′
smaller-target-value-classᴿ
    (⊑conv↑ᴿ c′↑ M⊑M′ q replace) (vM′ ⟨ inert ⟩) =
  target-inert-castᴿ
smaller-target-value-classᴿ
    (⊑conv↓ᴿ c′↓ M⊑M′ q replace) (vM′ ⟨ inert ⟩) =
  target-inert-castᴿ
smaller-target-value-classᴿ
    (paired-revealᴿ corresponds c↑ c′↑ replace M⊑M′)
    (vM′ ⟨ inert ⟩) =
  target-inert-castᴿ
smaller-target-value-classᴿ
    (paired-concealᴿ corresponds c↓ c′↓ replace M⊑M′)
    (vM′ ⟨ inert ⟩) =
  target-inert-castᴿ
smaller-target-value-classᴿ
    (target-instantiationᴿ embedded) vM′ =
  target-creationᴿ
smaller-target-value-classᴿ
    (closeᴿ M⊑M′ widening-pair
      u-shape u′-shape square compatible)
    (vM′ ⟨ inert ⟩) =
  target-inert-castᴿ
smaller-target-value-classᴿ
    (paired-wideningᴿ
      mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
      left-square right-square compatible M⊑M′)
    (vM′ ⟨ inert ⟩) =
  target-inert-castᴿ


smaller-quotient-source-value-classᴿ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ D D′}
    {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
  Value M →
  SmallerSourceValueClassᴿ
smaller-quotient-source-value-classᴿ
    (paired-downᴿ
      M⊑M′ mode d⊒ d-shape mode′ d′⊒ d′-shape square)
    (vM ⟨ inert ⟩) =
  source-inert-castᴿ


smaller-quotient-target-value-classᴿ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ D D′}
    {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
  Value M′ →
  SmallerTargetValueClassᴿ
smaller-quotient-target-value-classᴿ
    (paired-downᴿ
      M⊑M′ mode d⊒ d-shape mode′ d′⊒ d′-shape square)
    (vM′ ⟨ inert ⟩) =
  target-inert-castᴿ


smaller-source-value-no-stepᴿ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B χ N}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Value M →
  M —→[ χ ] N →
  ⊥
smaller-source-value-no-stepᴿ M⊑M′ vM M→N =
  value-no-step vM M→N


smaller-target-value-no-stepᴿ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B χ N′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Value M′ →
  M′ —→[ χ ] N′ →
  ⊥
smaller-target-value-no-stepᴿ M⊑M′ vM′ M′→N′ =
  value-no-step vM′ M′→N′


target-instantiation-creation-valuesᴿ :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ ρ∀ ρᴿ W W′ B C D s μ r f body-shape}
    {prefix-evidence : Set} {body-relation : Set₁} →
  TargetInstantiationCreation
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ}
    {W = W} {W′ = W′} {B = B} {C = C} {D = D}
    {s = s} {μ = μ} {r = r} {f = f}
    {body-shape = body-shape} prefix-evidence body-relation →
  Value (Λ W) × Value (W′ ⟨ s ⟩)
target-instantiation-creation-valuesᴿ creation =
  Λ (TargetInstantiationCreation.source-body-value creation) ,
  TargetInstantiationCreation.target-body-value creation
    ⟨ TargetInstantiationCreation.body-cast-inert creation ⟩


target-instantiation-transport-valuesᴿ :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ ρ∀ ρᴿ W W′ B C D s μ r f body-shape}
    {prefix-evidence : Set} {body-relation : Set₁} →
  (τ σ : Renameᵗ) →
  TargetInstantiationCreation
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ}
    {W = W} {W′ = W′} {B = B} {C = C} {D = D}
    {s = s} {μ = μ} {r = r} {f = f}
    {body-shape = body-shape} prefix-evidence body-relation →
  Value (renameᵗᵐ τ (Λ W)) ×
  Value (renameᵗᵐ σ (W′ ⟨ s ⟩))
target-instantiation-transport-valuesᴿ τ σ creation =
  renameᵗᵐ-preserves-Value τ (proj₁ creation-values) ,
  renameᵗᵐ-preserves-Value σ (proj₂ creation-values)
  where
    creation-values = target-instantiation-creation-valuesᴿ creation


target-instantiation-creation-source-no-stepᴿ :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ ρ∀ ρᴿ W W′ B C D s μ r f body-shape
      χ N}
    {prefix-evidence : Set} {body-relation : Set₁} →
  (creation :
    TargetInstantiationCreation
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ}
      {W = W} {W′ = W′} {B = B} {C = C} {D = D}
      {s = s} {μ = μ} {r = r} {f = f}
      {body-shape = body-shape} prefix-evidence body-relation) →
  Λ W —→[ χ ] N →
  ⊥
target-instantiation-creation-source-no-stepᴿ creation source-step =
  value-no-step
    (proj₁ (target-instantiation-creation-valuesᴿ creation))
    source-step


target-instantiation-creation-target-no-stepᴿ :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ ρ∀ ρᴿ W W′ B C D s μ r f body-shape
      χ N′}
    {prefix-evidence : Set} {body-relation : Set₁} →
  (creation :
    TargetInstantiationCreation
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ}
      {W = W} {W′ = W′} {B = B} {C = C} {D = D}
      {s = s} {μ = μ} {r = r} {f = f}
      {body-shape = body-shape} prefix-evidence body-relation) →
  W′ ⟨ s ⟩ —→[ χ ] N′ →
  ⊥
target-instantiation-creation-target-no-stepᴿ creation target-step =
  value-no-step
    (proj₂ (target-instantiation-creation-valuesᴿ creation))
    target-step


target-instantiation-transport-source-no-stepᴿ :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ ρ∀ ρᴿ W W′ B C D s μ r f body-shape
      χ N}
    {prefix-evidence : Set} {body-relation : Set₁} →
  (τ σ : Renameᵗ) →
  (creation :
    TargetInstantiationCreation
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ}
      {W = W} {W′ = W′} {B = B} {C = C} {D = D}
      {s = s} {μ = μ} {r = r} {f = f}
      {body-shape = body-shape} prefix-evidence body-relation) →
  renameᵗᵐ τ (Λ W) —→[ χ ] N →
  ⊥
target-instantiation-transport-source-no-stepᴿ
    τ σ creation source-step =
  value-no-step
    (proj₁ (target-instantiation-transport-valuesᴿ τ σ creation))
    source-step


target-instantiation-transport-target-no-stepᴿ :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ ρ∀ ρᴿ W W′ B C D s μ r f body-shape
      χ N′}
    {prefix-evidence : Set} {body-relation : Set₁} →
  (τ σ : Renameᵗ) →
  (creation :
    TargetInstantiationCreation
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ}
      {W = W} {W′ = W′} {B = B} {C = C} {D = D}
      {s = s} {μ = μ} {r = r} {f = f}
      {body-shape = body-shape} prefix-evidence body-relation) →
  renameᵗᵐ σ (W′ ⟨ s ⟩) —→[ χ ] N′ →
  ⊥
target-instantiation-transport-target-no-stepᴿ
    τ σ creation target-step =
  value-no-step
    (proj₂ (target-instantiation-transport-valuesᴿ τ σ creation))
    target-step
