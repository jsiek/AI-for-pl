module
  proof.Left.AllocationRuntime.NuImprecisionLeftSourceAllocationRuntimeCommutationProof
  where

-- File Charter:
--   * Bridges the target-runtime-bullet source-allocation case from the
--     constructor-natural right-after-left world to the canonical
--     left-after-right world required by runtime transport.
--   * Factors the supplied source renaming through the pre-bullet world,
--     constructs the bullet relation at the natural world, and transports it
--     across left/right context commutation.
--   * Returns the exact QTI derivation directly and introduces no result,
--     path, view, or coherence carrier.
--   * Contains no postulate, hole, permissive option, proof irrelevance, or
--     termination bypass.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; subst; sym)

open import ImprecisionWf using
  ( ImpCtx
  ; ⇑ᴿᵢ
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
  ; Term
  ; Value
  ; renameᵗᵐ
  ; ⇑ᵗᵐ
  ; _•
  )
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; ⊑αᵀ
  ; nu-term-imprecision-source-typing
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; `∀
  ; renameᵗ
  ; ⇑ᵗ
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( νᵢᶜ
  ; rename-assm²-source-νᵢ
  )
open import proof.Left.Core.NuImprecisionLeftRenameNoBulletDef using
  ( LeftRenameNoBullet
  ; left-rename-no•ᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( LeftCtxRenameⁱ
  ; LeftStoreRenameⁱ
  ; left-ctx-rename-[]
  ; left-ctx-rename-∷
  ; left-insertion-suc
  ; left-store-rename-[]
  ; left-store-rename-left
  ; left-store-rename-link
  ; left-store-rename-matched
  ; left-store-rename-right
  ; right-under-left-ctx-eq
  ; rightCtxⁱ-left-rename
  ; rightStoreⁱ-left-rename
  ; ⊑-rename-left-atᵢ
  ; ⊑-rename-leftᵢ
  )
open import proof.Core.Properties.TypeProperties using (TyRenameWf-suc)


private
  left-store-rename-right-inv :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp (νᵢᶜ Φ) (suc Δᴸ) Δᴿ}
      {β B hB hB′} →
    LeftStoreRenameⁱ suc rename-assm²-source-νᵢ TyRenameWf-suc
      (store-right β B hB ∷ ρ) (store-right β B hB′ ∷ ρ′) →
    LeftStoreRenameⁱ suc rename-assm²-source-νᵢ
      TyRenameWf-suc ρ ρ′
  left-store-rename-right-inv
      (left-store-rename-right renameρ) = renameρ

  left-source-after-right-store-factorⁱ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
      {ρᴸᴿ : StoreImp (νᵢᶜ (⇑ᴿᵢ Φ))
        (suc Δᴸ) (suc Δᴿ)} →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
    LeftStoreRenameⁱ suc rename-assm²-source-νᵢ TyRenameWf-suc
      ρᴿ ρᴸᴿ →
    ∃[ ρᴸ ]
      LeftStoreRenameⁱ suc rename-assm²-source-νᵢ
        TyRenameWf-suc ρ ρᴸ ×
      LiftRightStoreⁱ (νᵢᶜ (⇑ᴿᵢ Φ)) ρᴸ ρᴸᴿ
  left-source-after-right-store-factorⁱ
      lift-right-store-[] left-store-rename-[] =
    [] , left-store-rename-[] , lift-right-store-[]
  left-source-after-right-store-factorⁱ
      (lift-right-store-∷ {β = β} {B = B} {p = p} liftρ)
      (left-store-rename-matched
        {α′ = α′} {A′ = A′}
        eqα eqA renameρ)
      with left-source-after-right-store-factorⁱ liftρ renameρ
  left-source-after-right-store-factorⁱ
      (lift-right-store-∷ {β = β} {B = B} {p = p} liftρ)
      (left-store-rename-matched
        {α′ = α′} {A′ = A′}
        eqα eqA renameρ)
      | ρᴸ , renameρᴸ , liftρᴸ =
    store-matched α′ A′ β B
      (⊑-rename-left-atᵢ suc rename-assm²-source-νᵢ
        TyRenameWf-suc eqA p) ∷ ρᴸ ,
    left-store-rename-matched eqα eqA renameρᴸ ,
    lift-right-store-∷ liftρᴸ
  left-source-after-right-store-factorⁱ
      (lift-right-store-left liftρ)
      (left-store-rename-left
        {α′ = α′} {A′ = A′} {hA′ = hA′}
        eqα eqA renameρ)
      with left-source-after-right-store-factorⁱ liftρ renameρ
  left-source-after-right-store-factorⁱ
      (lift-right-store-left liftρ)
      (left-store-rename-left
        {α′ = α′} {A′ = A′} {hA′ = hA′}
        eqα eqA renameρ)
      | ρᴸ , renameρᴸ , liftρᴸ =
    store-left α′ A′ hA′ ∷ ρᴸ ,
    left-store-rename-left eqα eqA renameρᴸ ,
    lift-right-store-left liftρᴸ
  left-source-after-right-store-factorⁱ
      (lift-right-store-right {hB = hB} liftρ)
      (left-store-rename-right renameρ)
      with left-source-after-right-store-factorⁱ liftρ renameρ
  left-source-after-right-store-factorⁱ
      (lift-right-store-right {hB = hB} liftρ)
      (left-store-rename-right renameρ)
      | ρᴸ , renameρᴸ , liftρᴸ =
    store-right _ _ hB ∷ ρᴸ ,
    left-store-rename-right renameρᴸ ,
    lift-right-store-right liftρᴸ
  left-source-after-right-store-factorⁱ
      (lift-right-store-link {β = β} {B = B} {p = p} liftρ)
      (left-store-rename-link
        {α′ = α′} {A′ = A′}
        eqα eqA renameρ)
      with left-source-after-right-store-factorⁱ liftρ renameρ
  left-source-after-right-store-factorⁱ
      (lift-right-store-link {β = β} {B = B} {p = p} liftρ)
      (left-store-rename-link
        {α′ = α′} {A′ = A′}
        eqα eqA renameρ)
      | ρᴸ , renameρᴸ , liftρᴸ =
    store-link α′ A′ β B
      (⊑-rename-left-atᵢ suc rename-assm²-source-νᵢ
        TyRenameWf-suc eqA p) ∷ ρᴸ ,
    left-store-rename-link eqα eqA renameρᴸ ,
    lift-right-store-link liftρᴸ

  left-source-after-right-ctx-factorⁱ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {γᴿ : CtxImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
      {γᴸᴿ : CtxImp (νᵢᶜ (⇑ᴿᵢ Φ)) (suc Δᴸ) (suc Δᴿ)} →
    LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γᴿ →
    LeftCtxRenameⁱ suc rename-assm²-source-νᵢ TyRenameWf-suc
      γᴿ γᴸᴿ →
    ∃[ γᴸ ]
      LeftCtxRenameⁱ suc rename-assm²-source-νᵢ
        TyRenameWf-suc γ γᴸ ×
      LiftRightCtxⁱ (νᵢᶜ (⇑ᴿᵢ Φ)) γᴸ γᴸᴿ
  left-source-after-right-ctx-factorⁱ
      lift-right-ctx-[] left-ctx-rename-[] =
    [] , left-ctx-rename-[] , lift-right-ctx-[]
  left-source-after-right-ctx-factorⁱ
      (lift-right-ctx-∷ {B = B} {p = p} liftγ)
      (left-ctx-rename-∷ {A′ = A′} eqA renameγ)
      with left-source-after-right-ctx-factorⁱ liftγ renameγ
  left-source-after-right-ctx-factorⁱ
      (lift-right-ctx-∷ {B = B} {p = p} liftγ)
      (left-ctx-rename-∷ {A′ = A′} eqA renameγ)
      | γᴸ , renameγᴸ , liftγᴸ =
    ctx-imp A′ B
      (⊑-rename-left-atᵢ suc rename-assm²-source-νᵢ
        TyRenameWf-suc eqA p) ∷ γᴸ ,
    left-ctx-rename-∷ eqA renameγᴸ ,
    lift-right-ctx-∷ liftγᴸ

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

  transport-target-bullet-forward :
    ∀ {Ψ Ω : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      (eq : Ψ ≡ Ω)
      {ρΩ : StoreImp Ω Δᴸ Δᴿ}
      {γΩ : CtxImp Ω Δᴸ Δᴿ}
      {N L′ : Term} {A B C′ : Ty}
      {hA : WfTy Δᴿ A}
      {pΩ : Ω ∣ Δᴸ ⊢ B ⊑ C′ ⊣ Δᴿ} →
    Ψ ∣ Δᴸ ∣ Δᴿ
      ∣ store-right zero A hA ∷
        subst (λ Θ → StoreImp Θ Δᴸ Δᴿ) (sym eq) ρΩ
      ∣ subst (λ Θ → CtxImp Θ Δᴸ Δᴿ) (sym eq) γΩ
      ⊢ᴺ N ⊑ L′ ⦂ B ⊑ C′
      ∶ subst (λ Θ → Θ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ Δᴿ)
          (sym eq) pΩ →
    Ω ∣ Δᴸ ∣ Δᴿ ∣ store-right zero A hA ∷ ρΩ ∣ γΩ
      ⊢ᴺ N ⊑ L′ ⦂ B ⊑ C′ ∶ pΩ
  transport-target-bullet-forward refl N⊑L′ = N⊑L′


left-source-allocation-runtime-target-bullet-commuteᵀ :
  LeftRenameNoBullet →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {ρᴸᴿ : StoreImp (νᵢᶜ (⇑ᴿᵢ Φ))
      (suc Δᴸ) (suc Δᴿ)}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {γᴿ : CtxImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {γᴸᴿ : CtxImp (νᵢᶜ (⇑ᴿᵢ Φ))
      (suc Δᴸ) (suc Δᴿ)}
    {N L′ : Term} {A B C′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ}
    {r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ}
    {h⇑A h⇑A′ : WfTy (suc Δᴿ) (⇑ᵗ A)} →
  LeftStoreRenameⁱ suc rename-assm²-source-νᵢ TyRenameWf-suc
    (store-right zero (⇑ᵗ A) h⇑A ∷ ρᴿ)
    (store-right zero (⇑ᵗ A) h⇑A′ ∷ ρᴸᴿ) →
  LeftCtxRenameⁱ suc rename-assm²-source-νᵢ TyRenameWf-suc
    γᴿ γᴸᴿ →
  No• N →
  Value L′ →
  No• L′ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
  LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γᴿ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ N ⊑ L′ ⦂ B ⊑ `∀ C′ ∶ q →
  suc Δᴿ
    ∣ rightStoreⁱ (store-right zero (⇑ᵗ A) h⇑A ∷ ρᴿ)
    ∣ rightCtxⁱ γᴿ ⊢ (⇑ᵗᵐ L′) • ⦂ C′ →
  νᵢᶜ (⇑ᴿᵢ Φ) ∣ suc Δᴸ ∣ suc Δᴿ
    ∣ store-right zero (⇑ᵗ A) h⇑A′ ∷ ρᴸᴿ ∣ γᴸᴿ
    ⊢ᴺ renameᵗᵐ suc N ⊑ (⇑ᵗᵐ L′) •
    ⦂ renameᵗ suc B ⊑ C′
    ∶ ⊑-rename-leftᵢ suc rename-assm²-source-νᵢ
      TyRenameWf-suc r
left-source-allocation-runtime-target-bullet-commuteᵀ
    rename-no-bullet full-renameρ
    renameγᴿ noN vL′ noL′ liftρ liftγ N⊑L′ L′•⊢
    with left-source-after-right-store-factorⁱ liftρ
           (left-store-rename-right-inv full-renameρ)
       | left-source-after-right-ctx-factorⁱ liftγ renameγᴿ
left-source-allocation-runtime-target-bullet-commuteᵀ
    rename-no-bullet
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρᴿ = ρᴿ} {ρᴸᴿ = ρᴸᴿ}
    {γᴿ = γᴿ} {γᴸᴿ = γᴸᴿ}
    {N = N} {L′ = L′} {A = A} {B = B} {C′ = C′}
    {r = r} {h⇑A = h⇑A} {h⇑A′ = h⇑A′}
    full-renameρ renameγᴿ
    noN vL′ noL′ liftρ liftγ N⊑L′ L′•⊢
    | ρᴸ , renameρᴸ , liftρᴸ
    | γᴸ , renameγᴸ , liftγᴸ =
  transport-target-bullet-forward eq natural-bullet
  where
  eq = right-under-left-ctx-eq Φ

  ρᴿᴸ =
    subst
      (λ Θ → StoreImp Θ (suc Δᴸ) (suc Δᴿ))
      (sym eq) ρᴸᴿ

  γᴿᴸ =
    subst
      (λ Θ → CtxImp Θ (suc Δᴸ) (suc Δᴿ))
      (sym eq) γᴸᴿ

  liftρᴿᴸ = transport-lift-right-store-back eq liftρᴸ
  liftγᴿᴸ = transport-lift-right-ctx-back eq liftγᴸ

  pᴸᴿ =
    ⊑-rename-leftᵢ suc rename-assm²-source-νᵢ
      TyRenameWf-suc r

  pᴿᴸ =
    subst
      (λ Θ → Θ ∣ suc Δᴸ ⊢ renameᵗ suc B ⊑ C′ ⊣ suc Δᴿ)
      (sym eq) pᴸᴿ

  body =
    left-rename-no•ᵀ rename-no-bullet left-insertion-suc
      renameρᴸ renameγᴸ noN noL′ N⊑L′

  source-typing =
    subst
      (λ Γ → suc Δᴸ ∣ leftStoreⁱ ρᴿᴸ ∣ Γ
        ⊢ renameᵗᵐ suc N ⦂ renameᵗ suc B)
      (sym (leftCtxⁱ-lift-right liftγᴿᴸ))
      (subst
        (λ Σ → suc Δᴸ ∣ Σ ∣ leftCtxⁱ γᴸ
          ⊢ renameᵗᵐ suc N ⦂ renameᵗ suc B)
        (sym (leftStoreⁱ-lift-right liftρᴿᴸ))
        (nu-term-imprecision-source-typing body))

  target-typing-desired =
    subst
      (λ Γ → suc Δᴿ
        ∣ rightStoreⁱ
          (store-right zero (⇑ᵗ A) h⇑A′ ∷ ρᴸᴿ)
        ∣ Γ ⊢ (⇑ᵗᵐ L′) • ⦂ C′)
      (sym (rightCtxⁱ-left-rename renameγᴿ))
      (subst
        (λ Σ → suc Δᴿ ∣ Σ ∣ rightCtxⁱ γᴿ
          ⊢ (⇑ᵗᵐ L′) • ⦂ C′)
        (sym (rightStoreⁱ-left-rename full-renameρ)) L′•⊢)

  target-typing =
    subst
      (λ Γ → suc Δᴿ
        ∣ rightStoreⁱ
          (store-right zero (⇑ᵗ A) h⇑A′ ∷ ρᴿᴸ)
        ∣ Γ ⊢ (⇑ᵗᵐ L′) • ⦂ C′)
      (sym (right-ctx-transport-back eq γᴸᴿ))
      (subst
        (λ Σ → suc Δᴿ ∣
          (zero , ⇑ᵗ A) ∷ Σ ∣ rightCtxⁱ γᴸᴿ
          ⊢ (⇑ᵗᵐ L′) • ⦂ C′)
        (sym (right-store-transport-back eq ρᴸᴿ))
        target-typing-desired)

  natural-bullet =
    ⊑αᵀ vL′ noL′ h⇑A′ liftρᴿᴸ liftγᴿᴸ body pᴿᴸ
      source-typing target-typing
