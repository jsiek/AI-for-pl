module proof.Left.AllocationRuntime.NuImprecisionLeftSourceAllocationRuntimeTransportProof where

-- File Charter:
--   * Implements canonical source-allocation transport for a bullet-free
--     source and a runtime-safe target.
--   * Reuses no-bullet renaming for inert targets and recurses only through
--     the unique active target subterm.
--   * Uses the focused left/right commutation theorem at the root target
--     bullet and a private binder-general form beneath source-only `Λ`.
--   * Returns direct QTI and QTIP derivations without carriers, postulates,
--     holes, permissive options, catch-all clauses, or termination bypasses.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (subst; sym; trans)

open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  ( ImpAssm
  ; ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᴿᵢ
  ; ⇑ᴿᵢₐ
  ; _∣_⊢_⊑_⊣_
  )
open import NuTermImprecision using
  ( CtxImp
  ; LiftRightCtxⁱ
  ; LiftRightStoreⁱ
  ; StoreImp
  ; ctx-imp
  ; leftCtxⁱ
  ; leftCtxⁱ-lift-right
  ; leftStoreⁱ
  ; leftStoreⁱ-lift-right
  ; lift-right-ctx-[]
  ; lift-right-ctx-∷
  ; lift-right-store-[]
  ; lift-right-store-left
  ; lift-right-store-link
  ; lift-right-store-right
  ; lift-right-store-∷
  ; rightCtxⁱ
  ; rightStoreⁱ
  ; store-left
  ; store-link
  ; store-matched
  ; store-right
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-ƛ
  ; no•-·
  ; no•-Λ
  ; no•-ν
  ; no•-⊕
  ; no•-⟨⟩
  ; ok-no
  ; ok-•
  ; ok-·₁
  ; ok-·₂
  ; ok-ν
  ; ok-⊕₁
  ; ok-⊕₂
  ; ok-⟨⟩
  ; renameᵗᵐ
  ; ⇑ᵗᵐ
  ; _•
  )
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  ; blame⊑ᵀ
  ; x⊑xᵀ
  ; ƛ⊑ƛᵀ
  ; ·⊑·ᵀ
  ; closeᵀ
  ; Λ⊑Λᵀ
  ; Λ⊑ᵀ
  ; α⊑αᵀ
  ; α⊑ᵀ
  ; allocation-prefixᵀ
  ; ν⊑νᵀ
  ; ν⊑ᵀ
  ; κ⊑κᵀ
  ; ⊕⊑⊕ᵀ
  ; gen⊑groundᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; paired-revealᵀ
  ; paired-concealᵀ
  ; paired-wideningᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; paired-downᵀ
  ; target-instantiationᵀ
  ; nu-term-imprecision-source-typing
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using
  ( Renameᵗ
  ; Ty
  ; TyCtx
  ; WfTy
  ; extᵗ
  ; renameᵗ
  ; `∀
  ; ⇑ᵗ
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( νᵢᶜ
  ; rename-assm²-⇑ᴸᵢ
  ; rename-assm²-source-νᵢ
  ; rename-assm²ᵢ
  )
open import proof.Left.Core.NuImprecisionLeftRenameNoBulletDef using
  ( LeftRenameNoBullet
  ; left-rename-no•ᵀ
  ; left-rename-no•ᵀᵖ
  )
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using (embedded-creation-target-no-bulletᴱ)
open import proof.Left.AllocationRuntime.NuImprecisionLeftSourceAllocationRuntimeTransportDef using
  (LeftSourceAllocationRuntimeTransport)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( LeftInsertion
  ; LeftCtxRenameⁱ
  ; LeftStoreRenameⁱ
  ; left-insertion-ext
  ; left-insertion-suc
  ; left-insertion-cast-renamer
  ; left-ctx-rename-[]
  ; left-ctx-rename-∷
  ; left-rename-allocation-prefixᵀ
  ; left-rename-blameᵀ
  ; left-rename-cast⊒⊑ᵀ
  ; left-rename-cast⊑⊑ᵀ
  ; left-rename-closeᵀ
  ; left-rename-conv↑⊑ᵀ
  ; left-rename-conv↓⊑ᵀ
  ; left-rename-paired-concealᵀ
  ; left-rename-paired-downᵀ
  ; left-rename-paired-revealᵀ
  ; left-rename-paired-wideningᵀ
  ; left-rename-Λ⊑ᵀ
  ; left-rename-νᵀ
  ; left-rename-ν⊑ᵀ
  ; left-rename-⊑cast⊒ᵀ
  ; left-rename-⊑cast⊑ᵀ
  ; left-rename-⊑conv↑ᵀ
  ; left-rename-⊑conv↓ᵀ
  ; left-rename-·ᵀ
  ; left-rename-xᵀ
  ; left-seal★-renameⁱ
  ; left-store-rename-[]
  ; left-store-rename-left
  ; left-store-rename-link
  ; left-store-rename-matched
  ; left-store-rename-right
  ; left-typing-renameⁱ
  ; right-typing-left-renameⁱ
  ; right-under-left-ctx-eq
  ; rightCtxⁱ-left-rename
  ; rightStoreⁱ-left-rename
  ; ⇑ᴿᵢ-membership
  )
open import proof.Core.Permutation.ForallPermutationProperties using
  (⊑ᵖ-rename-leftᵢ)
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using
  ( cast-shape-rename
  ; rename-assm²-∀-leftᵢ
  ; shape-rename-left-atᵢ
  ; ⊑-rename-left-atᵢ
  ; ⊑-rename-leftᵢ
  )
open import proof.DGG.Core.NuProgress using (runtime-value-no•)
open import proof.Core.Properties.TypeProperties using
  ( RenameLeftInverse
  ; RenameLeftInverse-ext
  ; RenameLeftInverse-suc
  ; TyRenameWf
  ; TyRenameWf-ext
  ; TyRenameWf-suc
  ; predᵗ
  )


private
  un⇑ᴿᵢ-★∈ :
    ∀ {Φ α} → (α ˣ⊑★) ∈ ⇑ᴿᵢ Φ → (α ˣ⊑★) ∈ Φ
  un⇑ᴿᵢ-★∈ {Φ = []} ()
  un⇑ᴿᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
  un⇑ᴿᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there a∈) =
    there (un⇑ᴿᵢ-★∈ a∈)
  un⇑ᴿᵢ-★∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there a∈) =
    there (un⇑ᴿᵢ-★∈ a∈)

  un⇑ᴿᵢ-ˣ∈ :
    ∀ {Φ α β} →
    (α ˣ⊑ˣ suc β) ∈ ⇑ᴿᵢ Φ → (α ˣ⊑ˣ β) ∈ Φ
  un⇑ᴿᵢ-ˣ∈ {Φ = []} ()
  un⇑ᴿᵢ-ˣ∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there a∈) =
    there (un⇑ᴿᵢ-ˣ∈ a∈)
  un⇑ᴿᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
  un⇑ᴿᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there a∈) =
    there (un⇑ᴿᵢ-ˣ∈ a∈)

  right-base-assm :
    ∀ {Φ : ImpCtx} {τ : Renameᵗ}
      (assm : ∀ {a} → a ∈ ⇑ᴿᵢ Φ →
        rename-assm²ᵢ τ (λ X → X) a ∈ νᵢᶜ (⇑ᴿᵢ Φ)) →
    ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ νᵢᶜ Φ
  right-base-assm {Φ = Φ} {τ = τ} assm
      {a = X ˣ⊑★} a∈ =
    un⇑ᴿᵢ-★∈
      (subst (λ Θ → (τ X ˣ⊑★) ∈ Θ)
        (sym (right-under-left-ctx-eq Φ))
        (assm (⇑ᴿᵢ-membership a∈)))
  right-base-assm {Φ = Φ} {τ = τ} assm
      {a = X ˣ⊑ˣ Y} a∈ =
    un⇑ᴿᵢ-ˣ∈
      (subst (λ Θ → (τ X ˣ⊑ˣ suc Y) ∈ Θ)
        (sym (right-under-left-ctx-eq Φ))
        (assm (⇑ᴿᵢ-membership a∈)))

  left-insertion-pred : ∀ {τ} → LeftInsertion τ → Renameᵗ
  left-insertion-pred left-insertion-suc = predᵗ
  left-insertion-pred (left-insertion-ext ins) =
    extᵗ (left-insertion-pred ins)

  left-insertion-inverse :
    ∀ {τ} (ins : LeftInsertion τ) →
    RenameLeftInverse τ (left-insertion-pred ins)
  left-insertion-inverse left-insertion-suc = RenameLeftInverse-suc
  left-insertion-inverse (left-insertion-ext ins) =
    RenameLeftInverse-ext (left-insertion-inverse ins)

  left-after-right-store-factor :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴸ′ Δᴿ : TyCtx} {τ : Renameᵗ}
      {assm : ∀ {a} → a ∈ ⇑ᴿᵢ Φ →
        rename-assm²ᵢ τ (λ X → X) a ∈ νᵢᶜ (⇑ᴿᵢ Φ)}
      {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
      {ρᴸᴿ : StoreImp (νᵢᶜ (⇑ᴿᵢ Φ)) Δᴸ′ (suc Δᴿ)} →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
    LeftStoreRenameⁱ τ assm hτ ρᴿ ρᴸᴿ →
    ∃[ ρᴸ ]
      LeftStoreRenameⁱ τ (right-base-assm assm) hτ ρ ρᴸ ×
      LiftRightStoreⁱ (νᵢᶜ (⇑ᴿᵢ Φ)) ρᴸ ρᴸᴿ
  left-after-right-store-factor
      lift-right-store-[] left-store-rename-[] =
    [] , left-store-rename-[] , lift-right-store-[]
  left-after-right-store-factor
      (lift-right-store-∷
        {β = β} {B = B} {p = p} {p′ = pᴿ}
        shape-eq liftρ)
      (left-store-rename-matched
        {α′ = α′} {A′ = A′} {p = pᴿ}
        eqα eqA renameρ)
      with left-after-right-store-factor liftρ renameρ
  left-after-right-store-factor
      {τ = τ} {assm = assm} {hτ = hτ}
      (lift-right-store-∷
        {β = β} {B = B} {p = p} {p′ = pᴿ}
        shape-eq liftρ)
      (left-store-rename-matched
        {α′ = α′} {A′ = A′} {p = pᴿ}
        eqα eqA renameρ)
      | ρᴸ , renameρᴸ , liftρᴸ =
    store-matched α′ A′ β B
      (⊑-rename-left-atᵢ τ (right-base-assm assm)
        hτ eqA p) ∷ ρᴸ ,
    left-store-rename-matched eqα eqA renameρᴸ ,
    lift-right-store-∷
      (trans
        (shape-rename-left-atᵢ τ assm hτ eqA pᴿ)
        (trans shape-eq
          (sym
            (shape-rename-left-atᵢ τ
              (right-base-assm assm) hτ eqA p))))
      liftρᴸ
  left-after-right-store-factor
      (lift-right-store-left liftρ)
      (left-store-rename-left
        {α′ = α′} {A′ = A′} {hA′ = hA′}
        eqα eqA renameρ)
      with left-after-right-store-factor liftρ renameρ
  left-after-right-store-factor
      (lift-right-store-left liftρ)
      (left-store-rename-left
        {α′ = α′} {A′ = A′} {hA′ = hA′}
        eqα eqA renameρ)
      | ρᴸ , renameρᴸ , liftρᴸ =
    store-left α′ A′ hA′ ∷ ρᴸ ,
    left-store-rename-left eqα eqA renameρᴸ ,
    lift-right-store-left liftρᴸ
  left-after-right-store-factor
      (lift-right-store-right {hB = hB} liftρ)
      (left-store-rename-right renameρ)
      with left-after-right-store-factor liftρ renameρ
  left-after-right-store-factor
      (lift-right-store-right {hB = hB} liftρ)
      (left-store-rename-right renameρ)
      | ρᴸ , renameρᴸ , liftρᴸ =
    store-right _ _ hB ∷ ρᴸ ,
    left-store-rename-right renameρᴸ ,
    lift-right-store-right liftρᴸ
  left-after-right-store-factor
      (lift-right-store-link
        {β = β} {B = B} {p = p} {p′ = pᴿ}
        shape-eq liftρ)
      (left-store-rename-link
        {α′ = α′} {A′ = A′} {p = pᴿ}
        eqα eqA renameρ)
      with left-after-right-store-factor liftρ renameρ
  left-after-right-store-factor
      {τ = τ} {assm = assm} {hτ = hτ}
      (lift-right-store-link
        {β = β} {B = B} {p = p} {p′ = pᴿ}
        shape-eq liftρ)
      (left-store-rename-link
        {α′ = α′} {A′ = A′} {p = pᴿ}
        eqα eqA renameρ)
      | ρᴸ , renameρᴸ , liftρᴸ =
    store-link α′ A′ β B
      (⊑-rename-left-atᵢ τ (right-base-assm assm)
        hτ eqA p) ∷ ρᴸ ,
    left-store-rename-link eqα eqA renameρᴸ ,
    lift-right-store-link
      (trans
        (shape-rename-left-atᵢ τ assm hτ eqA pᴿ)
        (trans shape-eq
          (sym
            (shape-rename-left-atᵢ τ
              (right-base-assm assm) hτ eqA p))))
      liftρᴸ

  left-after-right-ctx-factor :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴸ′ Δᴿ : TyCtx} {τ : Renameᵗ}
      {assm : ∀ {a} → a ∈ ⇑ᴿᵢ Φ →
        rename-assm²ᵢ τ (λ X → X) a ∈ νᵢᶜ (⇑ᴿᵢ Φ)}
      {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {γᴿ : CtxImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
      {γᴸᴿ : CtxImp (νᵢᶜ (⇑ᴿᵢ Φ)) Δᴸ′ (suc Δᴿ)} →
    LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γᴿ →
    LeftCtxRenameⁱ τ assm hτ γᴿ γᴸᴿ →
    ∃[ γᴸ ]
      LeftCtxRenameⁱ τ (right-base-assm assm) hτ γ γᴸ ×
      LiftRightCtxⁱ (νᵢᶜ (⇑ᴿᵢ Φ)) γᴸ γᴸᴿ
  left-after-right-ctx-factor
      lift-right-ctx-[] left-ctx-rename-[] =
    [] , left-ctx-rename-[] , lift-right-ctx-[]
  left-after-right-ctx-factor
      (lift-right-ctx-∷
        {B = B} {p = p} {p′ = pᴿ} shape-eq liftγ)
      (left-ctx-rename-∷ {A′ = A′} {p = pᴿ}
        eqA renameγ)
      with left-after-right-ctx-factor liftγ renameγ
  left-after-right-ctx-factor
      {τ = τ} {assm = assm} {hτ = hτ}
      (lift-right-ctx-∷
        {B = B} {p = p} {p′ = pᴿ} shape-eq liftγ)
      (left-ctx-rename-∷ {A′ = A′} {p = pᴿ}
        eqA renameγ)
      | γᴸ , renameγᴸ , liftγᴸ =
    ctx-imp A′ B
      (⊑-rename-left-atᵢ τ (right-base-assm assm)
        hτ eqA p) ∷ γᴸ ,
    left-ctx-rename-∷ eqA renameγᴸ ,
    lift-right-ctx-∷
      (trans
        (shape-rename-left-atᵢ τ assm hτ eqA pᴿ)
        (trans shape-eq
          (sym
            (shape-rename-left-atᵢ τ
              (right-base-assm assm) hτ eqA p))))
      liftγᴸ

  transport-lift-right-store-back :
    ∀ {Φ Ψ Ω : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      (eq : Ψ ≡ Ω)
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρΩ : StoreImp Ω Δᴸ (suc Δᴿ)} →
    LiftRightStoreⁱ Ω ρ ρΩ →
    LiftRightStoreⁱ Ψ ρ
      (subst (λ Θ → StoreImp Θ Δᴸ (suc Δᴿ)) (sym eq) ρΩ)
  transport-lift-right-store-back refl liftρ = liftρ

  transport-lift-right-ctx-back :
    ∀ {Φ Ψ Ω : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      (eq : Ψ ≡ Ω)
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {γΩ : CtxImp Ω Δᴸ (suc Δᴿ)} →
    LiftRightCtxⁱ Ω γ γΩ →
    LiftRightCtxⁱ Ψ γ
      (subst (λ Θ → CtxImp Θ Δᴸ (suc Δᴿ)) (sym eq) γΩ)
  transport-lift-right-ctx-back refl liftγ = liftγ

  right-store-transport-back :
    ∀ {Ψ Ω : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      (eq : Ψ ≡ Ω) (ρΩ : StoreImp Ω Δᴸ Δᴿ) →
    rightStoreⁱ
      (subst (λ Θ → StoreImp Θ Δᴸ Δᴿ) (sym eq) ρΩ)
      ≡ rightStoreⁱ ρΩ
  right-store-transport-back refl ρΩ = refl

  right-ctx-transport-back :
    ∀ {Ψ Ω : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      (eq : Ψ ≡ Ω) (γΩ : CtxImp Ω Δᴸ Δᴿ) →
    rightCtxⁱ
      (subst (λ Θ → CtxImp Θ Δᴸ Δᴿ) (sym eq) γΩ)
      ≡ rightCtxⁱ γΩ
  right-ctx-transport-back refl γΩ = refl

mutual
  left-source-runtimeᵀ-generic :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴸ′ Δᴿ : TyCtx} {τ : Renameᵗ}
      {assm : ∀ {a} → a ∈ Φ →
        rename-assm²ᵢ τ (λ X → X) a ∈ νᵢᶜ Φ}
      {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp (νᵢᶜ Φ) Δᴸ′ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {γ′ : CtxImp (νᵢᶜ Φ) Δᴸ′ Δᴿ}
      {M M′ : Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    LeftRenameNoBullet →
    LeftInsertion τ →
    LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
    LeftCtxRenameⁱ τ assm hτ γ γ′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    No• M →
    RuntimeOK M′ →
    νᵢᶜ Φ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
      ⊢ᴺ renameᵗᵐ τ M ⊑ M′
      ⦂ renameᵗ τ A ⊑ B
      ∶ ⊑-rename-leftᵢ τ assm hτ p

  left-source-runtimeᵀᵖ-generic :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴸ′ Δᴿ : TyCtx} {τ : Renameᵗ}
      {assm : ∀ {a} → a ∈ Φ →
        rename-assm²ᵢ τ (λ X → X) a ∈ νᵢᶜ Φ}
      {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp (νᵢᶜ Φ) Δᴸ′ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {γ′ : CtxImp (νᵢᶜ Φ) Δᴸ′ Δᴿ}
      {M M′ : Term} {D D′ : Ty}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
    LeftRenameNoBullet →
    LeftInsertion τ →
    LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
    LeftCtxRenameⁱ τ assm hτ γ γ′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
    No• M →
    RuntimeOK M′ →
    νᵢᶜ Φ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
      ⊢ᴺᵖ renameᵗᵐ τ M ⊑ M′
      ⦂ renameᵗ τ D ⊑ᵖ D′
      ∶ ⊑ᵖ-rename-leftᵢ τ assm hτ q

  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ (blame⊑ᵀ M′⊢) noM runtime =
    left-rename-blameᵀ renameρ renameγ M′⊢
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ (x⊑xᵀ x∈) noM runtime =
    left-rename-xᵀ renameγ x∈
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ (ƛ⊑ƛᵀ hA hA′ N⊑N′) (no•-ƛ noN)
      (ok-no (no•-ƛ noN′)) =
    left-rename-no•ᵀ rename-no-bullet ins renameρ renameγ
      (no•-ƛ noN) (no•-ƛ noN′) (ƛ⊑ƛᵀ hA hA′ N⊑N′)
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ (Λ⊑Λᵀ liftρ liftγ vV vV′ V⊑V′)
      (no•-Λ noV)
      (ok-no (no•-Λ noV′)) =
    left-rename-no•ᵀ rename-no-bullet ins renameρ renameγ
      (no•-Λ noV) (no•-Λ noV′)
      (Λ⊑Λᵀ liftρ liftγ vV vV′ V⊑V′)
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ rel@(·⊑·ᵀ L⊑L′ M⊑M′)
      noLM (ok-no noL′M′) =
    left-rename-no•ᵀ rename-no-bullet ins renameρ renameγ
      noLM noL′M′ rel
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ (·⊑·ᵀ L⊑L′ M⊑M′)
      (no•-· noL noM) (ok-·₁ runtimeL noM′) =
    left-rename-·ᵀ
      (left-source-runtimeᵀ-generic rename-no-bullet ins
        renameρ renameγ L⊑L′ noL runtimeL)
      (left-rename-no•ᵀ rename-no-bullet ins
        renameρ renameγ noM noM′ M⊑M′)
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ (·⊑·ᵀ L⊑L′ M⊑M′)
      (no•-· noL noM) (ok-·₂ vL′ noL′ runtimeM) =
    left-rename-·ᵀ
      (left-rename-no•ᵀ rename-no-bullet ins
        renameρ renameγ noL noL′ L⊑L′)
      (left-source-runtimeᵀ-generic rename-no-bullet ins
        renameρ renameγ M⊑M′ noM runtimeM)
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      rel@(closeᵀ N⊑N′ widening pA
        u-shape u′-shape square compatible)
      noUp (ok-no noUp′) =
    left-rename-no•ᵀ rename-no-bullet ins renameρ renameγ
      noUp noUp′ rel
  left-source-runtimeᵀ-generic
      rename-no-bullet ins renameρ renameγ
      (closeᵀ N⊑N′ widening pA
        u-shape u′-shape square compatible)
      (no•-⟨⟩ noN)
      (ok-⟨⟩ runtimeN′) =
    left-rename-closeᵀ
      (left-insertion-cast-renamer ins) renameρ widening
      u-shape u′-shape square compatible
      (left-source-runtimeᵀᵖ-generic rename-no-bullet ins
        renameρ renameγ N⊑N′ noN runtimeN′)
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ (Λ⊑ᵀ occ liftρ liftγ vV V⊑N′)
      (no•-Λ noV) runtime =
    left-rename-Λ⊑ᵀ renameρ renameγ occ liftρ liftγ vV
      (λ liftρ′ liftγ′ renameρν renameγν →
        left-source-runtimeᵀ-generic rename-no-bullet
          (left-insertion-ext ins) renameρν renameγν
          V⊑N′ noV runtime)
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      rel@(target-instantiationᵀ embedded)
      noM runtime =
    left-rename-no•ᵀ rename-no-bullet ins renameρ renameγ
      noM (embedded-creation-target-no-bulletᴱ embedded) rel
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      (α⊑αᵀ vL noL vL′ noL′ A⇑⊑B⇑ liftρ liftγ
        L⊑L′ L•⊢ L′•⊢) () runtime
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      (α⊑ᵀ vL noL h⇑A liftρ liftγ L⊑N′ L•⊢ N′⊢) () runtime
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ (allocation-prefixᵀ prefix M⊑M′ M⊢ M′⊢)
      noM runtime =
    left-rename-allocation-prefixᵀ prefix renameρ
      (λ renameρ₀ →
        left-source-runtimeᵀ-generic rename-no-bullet ins
          renameρ₀ renameγ M⊑M′ noM runtime)
      source-typing target-typing
    where
    source-typing =
      left-typing-renameⁱ {ψ = left-insertion-pred ins}
        (left-insertion-inverse ins)
        (left-insertion-cast-renamer ins) renameρ renameγ noM M⊢

    target-typing = right-typing-left-renameⁱ renameρ renameγ M′⊢
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      rel@(ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
        liftρ liftγ N⊑N′ replace)
      noNu (ok-no noNu′) =
    left-rename-no•ᵀ rename-no-bullet ins renameρ renameγ
      noNu noNu′ rel
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
        liftρ liftγ N⊑N′ replace)
      (no•-ν noN) (ok-ν runtimeN′) =
    left-rename-νᵀ ins renameρ renameγ hA hA′ s↑ s′↑
      A⊑A′ A⇑⊑A′⇑ liftρ liftγ
      replace
      (left-source-runtimeᵀ-generic rename-no-bullet ins
        renameρ renameγ N⊑N′ noN runtimeN′)
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      (ν⊑ᵀ hA h⇑A s↑ liftρ liftγ N⊑N′ replace)
      (no•-ν noN) runtime =
    left-rename-ν⊑ᵀ ins renameρ renameγ hA h⇑A s↑
      liftρ liftγ replace
      (left-source-runtimeᵀ-generic rename-no-bullet ins
        renameρ renameγ N⊑N′ noN runtime)
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ κ⊑κᵀ noK runtime =
    κ⊑κᵀ
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ rel@(⊕⊑⊕ᵀ L⊑L′ M⊑M′)
      noPlus (ok-no noPlus′) =
    left-rename-no•ᵀ rename-no-bullet ins renameρ renameγ
      noPlus noPlus′ rel
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ (⊕⊑⊕ᵀ L⊑L′ M⊑M′)
      (no•-⊕ noL noM) (ok-⊕₁ runtimeL noM′) =
    ⊕⊑⊕ᵀ
      (left-source-runtimeᵀ-generic rename-no-bullet ins
        renameρ renameγ L⊑L′ noL runtimeL)
      (left-rename-no•ᵀ rename-no-bullet ins
        renameρ renameγ noM noM′ M⊑M′)
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ (⊕⊑⊕ᵀ L⊑L′ M⊑M′)
      (no•-⊕ noL noM) (ok-⊕₂ vL′ noL′ runtimeM) =
    ⊕⊑⊕ᵀ
      (left-rename-no•ᵀ rename-no-bullet ins
        renameρ renameγ noL noL′ L⊑L′)
      (left-source-runtimeᵀ-generic rename-no-bullet ins
        renameρ renameγ M⊑M′ noM runtimeM)
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      rel@(gen⊑groundᵀ mode seal★ c⊒ gH vV vW W⊢ V⊑Wtag q)
      noGen runtime =
    left-rename-no•ᵀ rename-no-bullet ins renameρ renameγ
      noGen (runtime-value-no• runtime vW) rel
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      (cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ q c-shape comp)
      (no•-⟨⟩ noM) runtime =
    left-rename-cast⊒⊑ᵀ
      (left-insertion-cast-renamer ins) renameρ mode seal★ c⊒
      c-shape comp
      (left-source-runtimeᵀ-generic rename-no-bullet ins
        renameρ renameγ M⊑M′ noM runtime)
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q c-shape comp)
      (no•-⟨⟩ noM) runtime =
    left-rename-cast⊑⊑ᵀ
      (left-insertion-cast-renamer ins) renameρ mode seal★ c⊑
      c-shape comp
      (left-source-runtimeᵀ-generic rename-no-bullet ins
        renameρ renameγ M⊑M′ noM runtime)
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      rel@(⊑cast⊒ᵀ mode′ seal★′ c′⊒ M⊑M′ q c′-shape comp)
      noM (ok-no noCast′) =
    left-rename-no•ᵀ rename-no-bullet ins renameρ renameγ
      noM noCast′ rel
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      (⊑cast⊒ᵀ mode′ seal★′ c′⊒ M⊑M′ q c′-shape comp)
      noM (ok-⟨⟩ runtimeM′) =
    left-rename-⊑cast⊒ᵀ renameρ mode′ seal★′ c′⊒
      c′-shape comp
      (left-source-runtimeᵀ-generic rename-no-bullet ins
        renameρ renameγ M⊑M′ noM runtimeM′)
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      rel@(⊑cast⊑ᵀ mode′ seal★′ c′⊑ M⊑M′ q c′-shape comp)
      noM (ok-no noCast′) =
    left-rename-no•ᵀ rename-no-bullet ins renameρ renameγ
      noM noCast′ rel
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      (⊑cast⊑ᵀ mode′ seal★′ c′⊑ M⊑M′ q c′-shape comp)
      noM (ok-⟨⟩ runtimeM′) =
    left-rename-⊑cast⊑ᵀ renameρ mode′ seal★′ c′⊑
      c′-shape comp
      (left-source-runtimeᵀ-generic rename-no-bullet ins
        renameρ renameγ M⊑M′ noM runtimeM′)
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      rel@(paired-revealᵀ corr conv conv′ replace M⊑M′)
      noConv (ok-no noConv′) =
    left-rename-no•ᵀ rename-no-bullet ins renameρ renameγ
      noConv noConv′ rel
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      (paired-revealᵀ corr conv conv′ replace M⊑M′)
      (no•-⟨⟩ noM) (ok-⟨⟩ runtimeM′) =
    left-rename-paired-revealᵀ ins renameρ corr conv conv′ replace
      (left-source-runtimeᵀ-generic rename-no-bullet ins
        renameρ renameγ M⊑M′ noM runtimeM′)
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      rel@(paired-concealᵀ corr conv conv′ replace M⊑M′)
      noConv (ok-no noConv′) =
    left-rename-no•ᵀ rename-no-bullet ins renameρ renameγ
      noConv noConv′ rel
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      (paired-concealᵀ corr conv conv′ replace M⊑M′)
      (no•-⟨⟩ noM) (ok-⟨⟩ runtimeM′) =
    left-rename-paired-concealᵀ ins renameρ corr conv conv′ replace
      (left-source-runtimeᵀ-generic rename-no-bullet ins
        renameρ renameγ M⊑M′ noM runtimeM′)
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      rel@(paired-wideningᵀ
        mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
        left-square right-square compatible M⊑M′)
      noConv (ok-no noConv′) =
    left-rename-no•ᵀ rename-no-bullet ins renameρ renameγ
      noConv noConv′ rel
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      (paired-wideningᵀ
        mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
        left-square right-square compatible M⊑M′)
      (no•-⟨⟩ noM) (ok-⟨⟩ runtimeM′) =
    left-rename-paired-wideningᵀ ins renameρ
      mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
      left-square right-square compatible
      (left-source-runtimeᵀ-generic rename-no-bullet ins
        renameρ renameγ M⊑M′ noM runtimeM′)
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      (conv↑⊑ᵀ c↑ M⊑M′ q replacement)
      (no•-⟨⟩ noM) runtime =
    left-rename-conv↑⊑ᵀ ins renameρ c↑
      (left-source-runtimeᵀ-generic rename-no-bullet ins
        renameρ renameγ M⊑M′ noM runtime)
      replacement
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      (conv↓⊑ᵀ c↓ M⊑M′ q replacement)
      (no•-⟨⟩ noM) runtime =
    left-rename-conv↓⊑ᵀ ins renameρ c↓
      (left-source-runtimeᵀ-generic rename-no-bullet ins
        renameρ renameγ M⊑M′ noM runtime)
      replacement
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      rel@(⊑conv↑ᵀ c′↑ M⊑M′ q replacement)
      noM (ok-no noConv′) =
    left-rename-no•ᵀ rename-no-bullet ins renameρ renameγ
      noM noConv′ rel
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      (⊑conv↑ᵀ c′↑ M⊑M′ q replacement) noM
      (ok-⟨⟩ runtimeM′) =
    left-rename-⊑conv↑ᵀ renameρ c′↑
      (left-source-runtimeᵀ-generic rename-no-bullet ins
        renameρ renameγ M⊑M′ noM runtimeM′)
      replacement
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      rel@(⊑conv↓ᵀ c′↓ M⊑M′ q replacement)
      noM (ok-no noConv′) =
    left-rename-no•ᵀ rename-no-bullet ins renameρ renameγ
      noM noConv′ rel
  left-source-runtimeᵀ-generic rename-no-bullet ins
      renameρ renameγ
      (⊑conv↓ᵀ c′↓ M⊑M′ q replacement) noM
      (ok-⟨⟩ runtimeM′) =
    left-rename-⊑conv↓ᵀ renameρ c′↓
      (left-source-runtimeᵀ-generic rename-no-bullet ins
        renameρ renameγ M⊑M′ noM runtimeM′)
      replacement

  left-source-runtimeᵀᵖ-generic rename-no-bullet ins
      renameρ renameγ
      rel@(paired-downᵀ M⊑M′
        mode d⊒ d-shape mode′ d′⊒ d′-shape square)
      noM (ok-no noM′) =
    left-rename-no•ᵀᵖ rename-no-bullet ins
      renameρ renameγ noM noM′ rel
  left-source-runtimeᵀᵖ-generic rename-no-bullet ins
      renameρ renameγ
      (paired-downᵀ M⊑M′
        mode d⊒ d-shape mode′ d′⊒ d′-shape square)
      (no•-⟨⟩ noM) (ok-⟨⟩ runtimeM′) =
    left-rename-paired-downᵀ
      (left-insertion-cast-renamer ins) renameρ
      (left-source-runtimeᵀ-generic rename-no-bullet ins
        renameρ renameγ M⊑M′ noM runtimeM′)
      mode d⊒ d-shape mode′ d′⊒ d′-shape square
private
  left-source-allocation-runtime-rootᵀ :
    LeftRenameNoBullet →
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᴸ : StoreImp (νᵢᶜ Φ) (suc Δᴸ) Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {γᴸ : CtxImp (νᵢᶜ Φ) (suc Δᴸ) Δᴿ}
      {M M′ : Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    LeftStoreRenameⁱ suc rename-assm²-source-νᵢ
      TyRenameWf-suc ρ ρᴸ →
    LeftCtxRenameⁱ suc rename-assm²-source-νᵢ
      TyRenameWf-suc γ γᴸ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    No• M →
    RuntimeOK M′ →
    νᵢᶜ Φ ∣ suc Δᴸ ∣ Δᴿ ∣ ρᴸ ∣ γᴸ
      ⊢ᴺ renameᵗᵐ suc M ⊑ M′
      ⦂ renameᵗ suc A ⊑ B
      ∶ ⊑-rename-leftᵢ
        suc rename-assm²-source-νᵢ TyRenameWf-suc p

  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ rel@(blame⊑ᵀ M′⊢) noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ rel@(x⊑xᵀ x∈) noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ rel@(ƛ⊑ƛᵀ hA hA′ N⊑N′) noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ rel@(·⊑·ᵀ L⊑L′ M⊑M′) noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(closeᵀ N⊑N′ widening pA
        u-shape u′-shape square compatible)
      noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(Λ⊑Λᵀ liftρ liftγ vV vV′ V⊑V′) noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ rel@(Λ⊑ᵀ occ liftρ liftγ vV V⊑N′)
      noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(target-instantiationᵀ embedded)
      noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet
      left-insertion-suc renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(α⊑αᵀ vL noL vL′ noL′ p↑ liftρ liftγ
        L⊑L′ L⊢ L′⊢) noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(α⊑ᵀ vL noL hA liftρ liftγ L⊑N′ L⊢ N′⊢)
      noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(allocation-prefixᵀ prefix M⊑M′ M⊢ M′⊢) noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
        liftρ liftγ N⊑N′ replace) noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(ν⊑ᵀ hA h⇑A s↑ liftρ liftγ N⊑N′ replace)
      noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ rel@κ⊑κᵀ noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ rel@(⊕⊑⊕ᵀ L⊑L′ M⊑M′) noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(gen⊑groundᵀ mode seal★ c⊒ gH vV vW W⊢ V⊑Wtag q)
      noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ q c-shape comp)
      noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q c-shape comp)
      noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(⊑cast⊒ᵀ mode seal★ c⊒ M⊑M′ q c-shape comp)
      noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(⊑cast⊑ᵀ mode seal★ c⊑ M⊑M′ q c-shape comp)
      noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(paired-revealᵀ corr conv conv′ replace M⊑M′)
      noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(paired-concealᵀ corr conv conv′ replace M⊑M′)
      noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(paired-wideningᵀ
        mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
        left-square right-square compatible M⊑M′)
      noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(conv↑⊑ᵀ c↑ M⊑M′ q replacement) noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(conv↓⊑ᵀ c↓ M⊑M′ q replacement) noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(⊑conv↑ᵀ c↑ M⊑M′ q replacement) noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime
  left-source-allocation-runtime-rootᵀ rename-no-bullet
      renameρ renameγ
      rel@(⊑conv↓ᵀ c↓ M⊑M′ q replacement) noM runtime =
    left-source-runtimeᵀ-generic rename-no-bullet left-insertion-suc
      renameρ renameγ rel noM runtime


left-source-allocation-runtime-transport-proof :
  LeftRenameNoBullet → LeftSourceAllocationRuntimeTransport
left-source-allocation-runtime-transport-proof rename-no-bullet = record
  { left-source-allocation-runtimeᵀ =
      λ renameρ renameγ noM runtime rel →
        left-source-allocation-runtime-rootᵀ rename-no-bullet
          renameρ renameγ rel noM runtime
  ; left-source-allocation-runtimeᵀᵖ =
      λ renameρ renameγ noM runtime rel →
        left-source-runtimeᵀᵖ-generic rename-no-bullet
          left-insertion-suc renameρ renameγ rel noM runtime
  }
