module
  proof.Quotient.NuImprecisionReductionClosedQuotientSingleSubstitutionExperiment
  where

-- File Charter:
--   * Derives fully indexed single-variable substitution for the independent
--     smaller ordinary relation from its parallel-substitution theorem.
--   * Builds the complete Kripke substitution environment by recursion on
--     ordinary lambdas and paired or source-only type binders.
--   * Uses only the smaller relation's own term-context and type-world
--     weakening theorems; it imports no live term-imprecision relation.
--   * Contains no postulate, hole, permissive option, termination bypass, or
--     catch-all clause.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Imprecision using
  (_ˣ⊑★; _ˣ⊑ˣ_; ⇑ᴸᵢ; ⇑ᵢ)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftCtxⁱ
  ; ctx-imp
  ; lift-ctx-[]
  ; lift-ctx-∷
  ; lift-left-ctx-[]
  ; lift-left-ctx-∷
  )
open import NuTerms using
  ( No•
  ; Substˣ
  ; Term
  ; extˢˣ
  ; no•-`
  ; renameᵗᵐ
  ; renameˣᵐ
  ; singleEnv
  ; ↑ᵗᵐ
  ; _[_]
  )
open import Types using
  (S; Ty; TyCtx; Z; renameᵗ; ⇑ᵗ; _∋_⦂_)
open import proof.Core.Properties.NuTermProperties using
  ( renameᵗᵐ-preserves-No•
  ; renameˣᵐ-preserves-No•
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (⊑-lift∀ᵢ; ⊑-source-liftνᵢ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using
  ( AssumptionMembershipUnique
  ; PrecisionIndexUnique
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessLemma
  using (assumption-membership-unique→precision-index-unique)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof
  using
  ( assumption-membership-unique-matched
  ; assumption-membership-unique-source
  )
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
  using
  ( x⊑xᴿ
  ; _∣_∣_∣_∣_⊢ᴿ_⊑_⦂_⊑_∶_
  )
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientSubstitutionExperiment
  using
  ( SmallerSubstitutionEnvironmentFamilyᴿ
  ; SmallerSubstitutionFrameᴿ
  ; smaller-parallel-term-substitutionᴿ
  ; substitution-frame-idᴿ
  ; substitution-frame-ƛᴿ
  ; substitution-frame-Λ-leftᴿ
  ; substitution-frame-Λᴿ
  )
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientTermContextShiftExperiment
  using (smaller-term-context-shiftᴿ)
open import
  proof.Quotient.NuImprecisionReductionClosedWorldRenameExperiment
  using
  ( smaller-paired-type-world-weakenᴿ
  ; smaller-source-type-world-weakenᴿ
  )


substitution-frame-preserves-uniqueᴿ :
  ∀ {Φ₀ : ImpCtx} {Δ₀ᴸ Δ₀ᴿ : TyCtx}
    {ρ₀ : StoreImp Φ₀ Δ₀ᴸ Δ₀ᴿ}
    {γ₀ δ₀ : CtxImp Φ₀ Δ₀ᴸ Δ₀ᴿ}
    {τ₀ τ₀′ : Substˣ}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {γ δ : CtxImp Φ Δᴸ Δᴿ}
    {τ τ′ : Substˣ} →
  SmallerSubstitutionFrameᴿ ρ₀ γ₀ δ₀ τ₀ τ₀′
    ρ γ δ τ τ′ →
  AssumptionMembershipUnique Φ₀ →
  AssumptionMembershipUnique Φ
substitution-frame-preserves-uniqueᴿ
    substitution-frame-idᴿ unique =
  unique
substitution-frame-preserves-uniqueᴿ
    (substitution-frame-ƛᴿ frame) unique =
  substitution-frame-preserves-uniqueᴿ frame unique
substitution-frame-preserves-uniqueᴿ
    (substitution-frame-Λᴿ frame liftρ liftγ liftδ) unique =
  assumption-membership-unique-matched
    (substitution-frame-preserves-uniqueᴿ frame unique)
substitution-frame-preserves-uniqueᴿ
    (substitution-frame-Λ-leftᴿ frame liftρ liftγ liftδ) unique =
  assumption-membership-unique-source
    (substitution-frame-preserves-uniqueᴿ frame unique)


private
  paired-unlift-lookupᴿ :
    ∀ {Φ Ψ Δᴸ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {γ↑ : CtxImp Ψ (suc Δᴸ) (suc Δᴿ)}
      {x A B p} →
    LiftCtxⁱ Ψ γ γ↑ →
    γ↑ ∋ x ⦂ ctx-imp A B p →
    ∃[ A₀ ] ∃[ B₀ ] ∃[ p₀ ]
      (γ ∋ x ⦂ ctx-imp A₀ B₀ p₀) ×
      A ≡ renameᵗ suc A₀ ×
      B ≡ renameᵗ suc B₀
  paired-unlift-lookupᴿ lift-ctx-[] ()
  paired-unlift-lookupᴿ
      (lift-ctx-∷ {A = A} {B = B} {p = p} shape liftγ) Z =
    A , B , p , Z , refl , refl
  paired-unlift-lookupᴿ
      (lift-ctx-∷ shape liftγ) (S x∈)
      with paired-unlift-lookupᴿ liftγ x∈
  paired-unlift-lookupᴿ
      (lift-ctx-∷ shape liftγ) (S x∈)
      | A , B , p , x∈₀ , refl , refl =
    A , B , p , S x∈₀ , refl , refl


  source-unlift-lookupᴿ :
    ∀ {Φ Ψ Δᴸ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {γ↑ : CtxImp Ψ (suc Δᴸ) Δᴿ}
      {x A B p} →
    LiftLeftCtxⁱ Ψ γ γ↑ →
    γ↑ ∋ x ⦂ ctx-imp A B p →
    ∃[ A₀ ] ∃[ B₀ ] ∃[ p₀ ]
      (γ ∋ x ⦂ ctx-imp A₀ B₀ p₀) ×
      A ≡ renameᵗ suc A₀ ×
      B ≡ B₀
  source-unlift-lookupᴿ lift-left-ctx-[] ()
  source-unlift-lookupᴿ
      (lift-left-ctx-∷
        {A = A} {B = B} {p = p} shape liftγ) Z =
    A , B , p , Z , refl , refl
  source-unlift-lookupᴿ
      (lift-left-ctx-∷ shape liftγ) (S x∈)
      with source-unlift-lookupᴿ liftγ x∈
  source-unlift-lookupᴿ
      (lift-left-ctx-∷ shape liftγ) (S x∈)
      | A , B , p , x∈₀ , refl , refl =
    A , B , p , S x∈₀ , refl , refl


  smaller-lambda-substitution-environmentᴿ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {γ δ : CtxImp Φ Δᴸ Δᴿ}
      {τ τ′ : Substˣ} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    (∀ {x C D q} →
      γ ∋ x ⦂ ctx-imp C D q →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
        ⊢ᴿ τ x ⊑ τ′ x ⦂ C ⊑ D ∶ q) →
    (∀ x → No• (τ x)) →
    (∀ x → No• (τ′ x)) →
    (∀ {x C D q} →
      ctx-imp A B p ∷ γ ∋ x ⦂ ctx-imp C D q →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ ctx-imp A B p ∷ δ
        ⊢ᴿ extˢˣ τ x ⊑ extˢˣ τ′ x
        ⦂ C ⊑ D ∶ q) ×
    (∀ x → No• (extˢˣ τ x)) ×
    (∀ x → No• (extˢˣ τ′ x))
  smaller-lambda-substitution-environmentᴿ related noτ noτ′ =
    (λ { Z → x⊑xᴿ Z
       ; (S x∈) →
           smaller-term-context-shiftᴿ
             (noτ _) (noτ′ _) (related x∈)
       }) ,
    (λ { zero → no•-`
       ; (suc x) → renameˣᵐ-preserves-No• suc (noτ x)
       }) ,
    λ { zero → no•-`
      ; (suc x) → renameˣᵐ-preserves-No• suc (noτ′ x)
      }


  smaller-substitution-environment-paired-type-liftᴿ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ↑ : StoreImp
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
      {γ δ : CtxImp Φ Δᴸ Δᴿ}
      {γ↑ δ↑ : CtxImp
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
      {τ τ′ : Substˣ} →
    AssumptionMembershipUnique Φ →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ↑ →
    LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ↑ →
    LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) δ δ↑ →
    (∀ {x A B p} →
      γ ∋ x ⦂ ctx-imp A B p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
        ⊢ᴿ τ x ⊑ τ′ x ⦂ A ⊑ B ∶ p) →
    (∀ x → No• (τ x)) →
    (∀ x → No• (τ′ x)) →
    (∀ {x A B p} →
      γ↑ ∋ x ⦂ ctx-imp A B p →
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ↑ ∣ δ↑
        ⊢ᴿ ↑ᵗᵐ τ x ⊑ ↑ᵗᵐ τ′ x
        ⦂ A ⊑ B ∶ p) ×
    (∀ x → No• (↑ᵗᵐ τ x)) ×
    (∀ x → No• (↑ᵗᵐ τ′ x))
  smaller-substitution-environment-paired-type-liftᴿ
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ↑ = ρ↑} {γ↑ = γ↑} {δ↑ = δ↑}
      {τ = τ} {τ′ = τ′}
      unique liftρ liftγ liftδ
      related noτ noτ′ =
    related↑ ,
    (λ x → renameᵗᵐ-preserves-No• suc (noτ x)) ,
    λ x → renameᵗᵐ-preserves-No• suc (noτ′ x)
    where
    unique↑ =
      assumption-membership-unique-matched unique

    precision↑ : PrecisionIndexUnique _
    precision↑ =
      assumption-membership-unique→precision-index-unique unique↑

    related↑ :
      ∀ {x A B p} →
      γ↑ ∋ x ⦂ ctx-imp A B p →
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ↑ ∣ δ↑
        ⊢ᴿ ↑ᵗᵐ τ x ⊑ ↑ᵗᵐ τ′ x ⦂ A ⊑ B ∶ p
    related↑ {p = p↑} x∈
        with paired-unlift-lookupᴿ liftγ x∈
    related↑ {x = x} {p = p↑} x∈
        | A , B , p , x∈₀ , refl , refl
        with precision↑ (⊑-lift∀ᵢ p) p↑
    related↑ {x = x} {p = p↑} x∈
        | A , B , p , x∈₀ , refl , refl | refl =
      smaller-paired-type-world-weakenᴿ
        unique↑ liftρ liftδ
        (noτ x) (noτ′ x) (related x∈₀)


  smaller-substitution-environment-source-type-liftᴿ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ↑ : StoreImp
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
      {γ δ : CtxImp Φ Δᴸ Δᴿ}
      {γ↑ δ↑ : CtxImp
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
      {τ τ′ : Substˣ} →
    AssumptionMembershipUnique Φ →
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ↑ →
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ↑ →
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) δ δ↑ →
    (∀ {x A B p} →
      γ ∋ x ⦂ ctx-imp A B p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
        ⊢ᴿ τ x ⊑ τ′ x ⦂ A ⊑ B ∶ p) →
    (∀ x → No• (τ x)) →
    (∀ x → No• (τ′ x)) →
    (∀ {x A B p} →
      γ↑ ∋ x ⦂ ctx-imp A B p →
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ∣ Δᴿ ∣ ρ↑ ∣ δ↑
        ⊢ᴿ ↑ᵗᵐ τ x ⊑ τ′ x
        ⦂ A ⊑ B ∶ p) ×
    (∀ x → No• (↑ᵗᵐ τ x)) ×
    (∀ x → No• (τ′ x))
  smaller-substitution-environment-source-type-liftᴿ
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ↑ = ρ↑} {γ↑ = γ↑} {δ↑ = δ↑}
      {τ = τ} {τ′ = τ′}
      unique liftρ liftγ liftδ
      related noτ noτ′ =
    related↑ ,
    (λ x → renameᵗᵐ-preserves-No• suc (noτ x)) ,
    noτ′
    where
    unique↑ =
      assumption-membership-unique-source unique

    precision↑ : PrecisionIndexUnique _
    precision↑ =
      assumption-membership-unique→precision-index-unique unique↑

    related↑ :
      ∀ {x A B p} →
      γ↑ ∋ x ⦂ ctx-imp A B p →
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ∣ Δᴿ ∣ ρ↑ ∣ δ↑
        ⊢ᴿ ↑ᵗᵐ τ x ⊑ τ′ x ⦂ A ⊑ B ∶ p
    related↑ {p = p↑} x∈
        with source-unlift-lookupᴿ liftγ x∈
    related↑ {x = x} {p = p↑} x∈
        | A , B , p , x∈₀ , refl , refl
        with precision↑ (⊑-source-liftνᵢ p) p↑
    related↑ {x = x} {p = p↑} x∈
        | A , B , p , x∈₀ , refl , refl | refl =
      smaller-source-type-world-weakenᴿ
        unique↑ liftρ liftδ
        (noτ x) (noτ′ x) (related x∈₀)


smaller-single-substitution-environmentᴿ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {V V′ : Term} {A A′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  AssumptionMembershipUnique Φ →
  No• V → No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ V ⊑ V′ ⦂ A ⊑ A′ ∶ pA →
  SmallerSubstitutionEnvironmentFamilyᴿ
    ρ (ctx-imp A A′ pA ∷ γ) γ
    (singleEnv V) (singleEnv V′)
smaller-single-substitution-environmentᴿ
    unique noV noV′ argument substitution-frame-idᴿ =
  (λ { Z → argument
     ; (S x∈) → x⊑xᴿ x∈
     }) ,
  (λ { zero → noV
     ; (suc x) → no•-`
     }) ,
  λ { zero → noV′
    ; (suc x) → no•-`
    }
smaller-single-substitution-environmentᴿ
    unique noV noV′ argument
    (substitution-frame-ƛᴿ frame)
    with smaller-single-substitution-environmentᴿ
      unique noV noV′ argument frame
smaller-single-substitution-environmentᴿ
    unique noV noV′ argument
    (substitution-frame-ƛᴿ frame)
    | related , noτ , noτ′ =
  smaller-lambda-substitution-environmentᴿ related noτ noτ′
smaller-single-substitution-environmentᴿ
    unique noV noV′ argument
    (substitution-frame-Λᴿ frame liftρ liftγ liftδ)
    with smaller-single-substitution-environmentᴿ
      unique noV noV′ argument frame
smaller-single-substitution-environmentᴿ
    unique noV noV′ argument
    (substitution-frame-Λᴿ frame liftρ liftγ liftδ)
    | related , noτ , noτ′ =
  smaller-substitution-environment-paired-type-liftᴿ
    (substitution-frame-preserves-uniqueᴿ frame unique)
    liftρ liftγ liftδ related noτ noτ′
smaller-single-substitution-environmentᴿ
    unique noV noV′ argument
    (substitution-frame-Λ-leftᴿ frame liftρ liftγ liftδ)
    with smaller-single-substitution-environmentᴿ
      unique noV noV′ argument frame
smaller-single-substitution-environmentᴿ
    unique noV noV′ argument
    (substitution-frame-Λ-leftᴿ frame liftρ liftγ liftδ)
    | related , noτ , noτ′ =
  smaller-substitution-environment-source-type-liftᴿ
    (substitution-frame-preserves-uniqueᴿ frame unique)
    liftρ liftγ liftδ related noτ noτ′


smaller-single-term-substitutionᴿ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {N N′ V V′ : Term} {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  AssumptionMembershipUnique Φ →
  No• N → No• N′ → No• V → No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ ctx-imp A A′ pA ∷ γ
    ⊢ᴿ N ⊑ N′ ⦂ B ⊑ B′ ∶ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ V ⊑ V′ ⦂ A ⊑ A′ ∶ pA →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ N [ V ] ⊑ N′ [ V′ ] ⦂ B ⊑ B′ ∶ pB
smaller-single-term-substitutionᴿ
    unique noN noN′ noV noV′ body argument =
  smaller-parallel-term-substitutionᴿ
    (smaller-single-substitution-environmentᴿ
      unique noV noV′ argument)
    noN noN′ body
