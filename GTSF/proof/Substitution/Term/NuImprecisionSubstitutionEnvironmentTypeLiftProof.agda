module proof.Substitution.Term.NuImprecisionSubstitutionEnvironmentTypeLiftProof where

-- File Charter:
--   * Proves exact paired and source-only type lifting for related no-bullet
--     substitution environments in assumption-unique worlds.
--   * Uses the existing no-bullet world/left-renaming traversals, then aligns
--     their canonical indices with the indices stored by lifted contexts.
--   * Contains no postulate, hole, catch-all, proof-irrelevance axiom, or
--     permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import ImprecisionWf using
  (_ˣ⊑★; _ˣ⊑ˣ_; ⇑ᴸᵢ; ⇑ᵢ; _∣_⊢_⊑_⊣_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; lift-left-store-[]
  ; lift-left-store-left
  ; lift-left-store-link
  ; lift-left-store-right
  ; lift-left-store-∷
  ; lift-store-[]
  ; lift-store-left
  ; lift-store-link
  ; lift-store-right
  ; lift-store-∷
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
open import NuTerms using (No•; Term; renameᵗᵐ; ↑ᵗᵐ)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( rename-assm²-source-νᵢ
  ; rename-assm²-∀ᵢ
  ; ⊑-renameᵗ²ᵢ
  )
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  ( AssumptionMembershipUnique
  ; PrecisionIndexUnique
  )
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessLemma using
  (assumption-membership-unique→precision-index-unique)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof using
  ( assumption-membership-unique-matched
  ; assumption-membership-unique-source
  )
open import proof.Left.Core.NuImprecisionLeftRenameNoBulletDef using
  (left-rename-no•ᵀ)
open import proof.Left.Core.NuImprecisionLeftRenameNoBulletProof using
  (left-rename-no-bullet)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef using
  ( RelStoreEmbeddingⁱ
  ; rel-store-embedding-[]
  ; rel-store-embedding-left
  ; rel-store-embedding-link
  ; rel-store-embedding-matched
  ; rel-store-embedding-right
  )
open import proof.Store.RelEmbedding.NuImprecisionRelCtxRenameDef using
  ( RelCtxRenameⁱ
  ; rel-ctx-rename-[]
  ; rel-ctx-rename-∷
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
  ; rel-world-embedding
  )
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using (⊑-rename-left-atᵢ; ⊑-rename-leftᵢ)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using (⊑-rename-at²ᵢ)
open import proof.Substitution.Term.NuImprecisionSubstitutionEnvironmentTypeLiftDef using
  ( QuotientedSubstitutionEnvironmentLeftTypeLiftᵀ
  ; QuotientedSubstitutionEnvironmentPairedTypeLiftᵀ
  )
open import proof.NuCore.Misc.NuImprecisionWorldEmbeddingNoBullet using
  (rel-world-embed-no•ᵀ)
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-No•)
open import proof.Core.Properties.TypePreservation using (castModeRenamer-suc)
open import proof.Core.Properties.TypeProperties using
  (RenameLeftInverse-suc; TyRenameWf-suc; predᵗ)
open import Types using (S; Ty; TyCtx; Z; renameᵗ; _∋_⦂_)


private
  paired-store-embedding :
    ∀ {Φ Ψ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ↑ : StoreImp Ψ (suc Δᴸ) (suc Δᴿ)} →
    LiftStoreⁱ Ψ ρ ρ↑ →
    RelStoreEmbeddingⁱ suc suc ρ ρ↑
  paired-store-embedding lift-store-[] =
    rel-store-embedding-[]
  paired-store-embedding (lift-store-∷ shape-eq liftρ) =
    rel-store-embedding-matched refl refl refl refl
      shape-eq (paired-store-embedding liftρ)
  paired-store-embedding (lift-store-left liftρ) =
    rel-store-embedding-left refl refl
      (paired-store-embedding liftρ)
  paired-store-embedding (lift-store-right liftρ) =
    rel-store-embedding-right refl refl
      (paired-store-embedding liftρ)
  paired-store-embedding (lift-store-link shape-eq liftρ) =
    rel-store-embedding-link refl refl refl refl
      shape-eq (paired-store-embedding liftρ)


  paired-context-rename :
    ∀ {Φ Δᴸ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {γ↑ : CtxImp
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)} →
    AssumptionMembershipUnique
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) →
    LiftCtxⁱ
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      γ γ↑ →
    RelCtxRenameⁱ suc suc rename-assm²-∀ᵢ
      TyRenameWf-suc TyRenameWf-suc γ γ↑
  paired-context-rename unique lift-ctx-[] = rel-ctx-rename-[]
  paired-context-rename unique
      (lift-ctx-∷ {p = p} {p′ = p↑} shape-eq liftγ)
      with assumption-membership-unique→precision-index-unique unique
        p↑
        (⊑-rename-at²ᵢ rename-assm²-∀ᵢ
          TyRenameWf-suc TyRenameWf-suc refl refl p)
  paired-context-rename unique
      (lift-ctx-∷ {p = p} {p′ = p↑} shape-eq liftγ)
      | refl =
    rel-ctx-rename-∷ refl refl
      (paired-context-rename unique liftγ)


  left-store-rename :
    ∀ {Φ Δᴸ Δᴿ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ↑ : StoreImp
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ} →
    AssumptionMembershipUnique
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) →
    LiftLeftStoreⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ↑ →
    LeftStoreRenameⁱ suc rename-assm²-source-νᵢ
      TyRenameWf-suc ρ ρ↑
  left-store-rename unique lift-left-store-[] =
    left-store-rename-[]
  left-store-rename unique
      (lift-left-store-∷ {p = p} {p′ = p↑} shape-eq liftρ)
      with assumption-membership-unique→precision-index-unique unique
        p↑
        (⊑-rename-left-atᵢ suc rename-assm²-source-νᵢ
          TyRenameWf-suc refl p)
  left-store-rename unique
      (lift-left-store-∷ {p = p} {p′ = p↑} shape-eq liftρ)
      | refl =
    left-store-rename-matched refl refl
      (left-store-rename unique liftρ)
  left-store-rename unique (lift-left-store-left liftρ) =
    left-store-rename-left refl refl
      (left-store-rename unique liftρ)
  left-store-rename unique (lift-left-store-right liftρ) =
    left-store-rename-right (left-store-rename unique liftρ)
  left-store-rename unique
      (lift-left-store-link {p = p} {p′ = p↑} shape-eq liftρ)
      with assumption-membership-unique→precision-index-unique unique
        p↑
        (⊑-rename-left-atᵢ suc rename-assm²-source-νᵢ
          TyRenameWf-suc refl p)
  left-store-rename unique
      (lift-left-store-link {p = p} {p′ = p↑} shape-eq liftρ)
      | refl =
    left-store-rename-link refl refl
      (left-store-rename unique liftρ)


  left-context-rename :
    ∀ {Φ Δᴸ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {γ↑ : CtxImp
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ} →
    AssumptionMembershipUnique
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) →
    LiftLeftCtxⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ↑ →
    LeftCtxRenameⁱ suc rename-assm²-source-νᵢ
      TyRenameWf-suc γ γ↑
  left-context-rename unique lift-left-ctx-[] = left-ctx-rename-[]
  left-context-rename unique
      (lift-left-ctx-∷ {p = p} {p′ = p↑} shape-eq liftγ)
      with assumption-membership-unique→precision-index-unique unique
        p↑
        (⊑-rename-left-atᵢ suc rename-assm²-source-νᵢ
          TyRenameWf-suc refl p)
  left-context-rename unique
      (lift-left-ctx-∷ {p = p} {p′ = p↑} shape-eq liftγ)
      | refl =
    left-ctx-rename-∷ refl (left-context-rename unique liftγ)


  paired-unlift-lookup :
    ∀ {Φ Ψ Δᴸ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {γ↑ : CtxImp Ψ (suc Δᴸ) (suc Δᴿ)}
      {x A B p} →
    LiftCtxⁱ Ψ γ γ↑ →
    γ↑ ∋ x ⦂ ctx-imp A B p →
    ∃[ A₀ ] ∃[ B₀ ] ∃[ p₀ ]
      (γ ∋ x ⦂ ctx-imp A₀ B₀ p₀) ×
      A ≡ renameᵗ suc A₀ × B ≡ renameᵗ suc B₀
  paired-unlift-lookup lift-ctx-[] ()
  paired-unlift-lookup
      (lift-ctx-∷ {A = A} {B = B} {p = p} shape-eq liftγ) Z =
    A , B , p , Z , refl , refl
  paired-unlift-lookup (lift-ctx-∷ shape-eq liftγ) (S x∈)
      with paired-unlift-lookup liftγ x∈
  paired-unlift-lookup (lift-ctx-∷ shape-eq liftγ) (S x∈)
      | A , B , p , x∈₀ , refl , refl =
    A , B , p , S x∈₀ , refl , refl


  left-unlift-lookup :
    ∀ {Φ Ψ Δᴸ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {γ↑ : CtxImp Ψ (suc Δᴸ) Δᴿ}
      {x A B p} →
    LiftLeftCtxⁱ Ψ γ γ↑ →
    γ↑ ∋ x ⦂ ctx-imp A B p →
    ∃[ A₀ ] ∃[ B₀ ] ∃[ p₀ ]
      (γ ∋ x ⦂ ctx-imp A₀ B₀ p₀) ×
      A ≡ renameᵗ suc A₀ × B ≡ B₀
  left-unlift-lookup lift-left-ctx-[] ()
  left-unlift-lookup
      (lift-left-ctx-∷ {A = A} {B = B} {p = p}
        shape-eq liftγ) Z =
    A , B , p , Z , refl , refl
  left-unlift-lookup
      (lift-left-ctx-∷ shape-eq liftγ) (S x∈)
      with left-unlift-lookup liftγ x∈
  left-unlift-lookup
      (lift-left-ctx-∷ shape-eq liftγ) (S x∈)
      | A , B , p , x∈₀ , refl , refl =
    A , B , p , S x∈₀ , refl , refl


quotiented-substitution-environment-paired-type-lift-proofᵀ :
  QuotientedSubstitutionEnvironmentPairedTypeLiftᵀ
quotiented-substitution-environment-paired-type-lift-proofᵀ
    {Φ} {Δᴸ} {Δᴿ} {ρ} {ρ↑} {γ} {δ} {γ↑} {δ↑} {τ} {τ′}
    unique liftρ liftγ liftδ related noτ noτ′ =
  related↑ ,
  (λ x → renameᵗᵐ-preserves-No• suc (noτ x)) ,
  λ x → renameᵗᵐ-preserves-No• suc (noτ′ x)
  where
  unique↑ = assumption-membership-unique-matched unique

  precision↑ : PrecisionIndexUnique _
  precision↑ =
    assumption-membership-unique→precision-index-unique unique↑

  lift-related :
    ∀ {M M′ : Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    No• M → No• M′ →
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ↑ ∣ δ↑
      ⊢ᴺ renameᵗᵐ suc M ⊑ renameᵗᵐ suc M′
      ⦂ renameᵗ suc A ⊑ renameᵗ suc B
      ∶ ⊑-renameᵗ²ᵢ rename-assm²-∀ᵢ
        TyRenameWf-suc TyRenameWf-suc p
  lift-related =
    rel-world-embed-no•ᵀ
      (rel-world-embedding {ψ = predᵗ} {φ = predᵗ}
        RenameLeftInverse-suc RenameLeftInverse-suc
        castModeRenamer-suc castModeRenamer-suc
        (paired-store-embedding liftρ)
        (paired-context-rename unique↑ liftδ))

  related↑ :
    ∀ {x A B p} →
    γ↑ ∋ x ⦂ ctx-imp A B p →
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ↑ ∣ δ↑
      ⊢ᴺ ↑ᵗᵐ τ x ⊑ ↑ᵗᵐ τ′ x ⦂ A ⊑ B ∶ p
  related↑ {p = p↑} x∈
      with paired-unlift-lookup liftγ x∈
  related↑ {x = x} {p = p↑} x∈
      | A , B , p , x∈₀ , refl , refl
      with precision↑
        (⊑-renameᵗ²ᵢ rename-assm²-∀ᵢ
          TyRenameWf-suc TyRenameWf-suc p)
        p↑
  related↑ {x = x} {p = p↑} x∈
      | A , B , p , x∈₀ , refl , refl | refl =
    lift-related (related x∈₀) (noτ x) (noτ′ x)


quotiented-substitution-environment-left-type-lift-proofᵀ :
  QuotientedSubstitutionEnvironmentLeftTypeLiftᵀ
quotiented-substitution-environment-left-type-lift-proofᵀ
    {Φ} {Δᴸ} {Δᴿ} {ρ} {ρ↑} {γ} {δ} {γ↑} {δ↑} {τ} {τ′}
    unique liftρ liftγ liftδ related noτ noτ′ =
  related↑ ,
  (λ x → renameᵗᵐ-preserves-No• suc (noτ x)) ,
  noτ′
  where
  unique↑ = assumption-membership-unique-source unique

  precision↑ : PrecisionIndexUnique _
  precision↑ =
    assumption-membership-unique→precision-index-unique unique↑

  lift-related :
    ∀ {M M′ : Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    No• M → No• M′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ∣ Δᴿ ∣ ρ↑ ∣ δ↑
      ⊢ᴺ renameᵗᵐ suc M ⊑ M′
      ⦂ renameᵗ suc A ⊑ B
      ∶ ⊑-rename-leftᵢ suc rename-assm²-source-νᵢ
        TyRenameWf-suc p
  lift-related =
    left-rename-no•ᵀ left-rename-no-bullet left-insertion-suc
      (left-store-rename unique↑ liftρ)
      (left-context-rename unique↑ liftδ)

  related↑ :
    ∀ {x A B p} →
    γ↑ ∋ x ⦂ ctx-imp A B p →
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ∣ Δᴿ ∣ ρ↑ ∣ δ↑
      ⊢ᴺ ↑ᵗᵐ τ x ⊑ τ′ x ⦂ A ⊑ B ∶ p
  related↑ {p = p↑} x∈
      with left-unlift-lookup liftγ x∈
  related↑ {x = x} {p = p↑} x∈
      | A , B , p , x∈₀ , refl , refl
      with precision↑
        (⊑-rename-leftᵢ suc rename-assm²-source-νᵢ
          TyRenameWf-suc p)
        p↑
  related↑ {x = x} {p = p↑} x∈
      | A , B , p , x∈₀ , refl , refl | refl =
    lift-related (noτ x) (noτ′ x) (related x∈₀)
