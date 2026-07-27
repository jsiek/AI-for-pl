module
  proof.Quotient.NuImprecisionReductionClosedWorldRenameExperiment
  where

-- File Charter:
--   * Proves that the independent reduction-closed ordinary and quotient
--     imprecision relations are preserved by structural world embeddings.
--   * Requires no-runtime-bullet endpoints only where typing transport needs
--     it, and eliminates the runtime-bullet application constructors.
--   * Composes an embedding around the single exact target-instantiation
--     residual instead of adding a transport constructor to the relation.
--   * Depends on the smaller relation and QTI-free store, context, coercion,
--     and index infrastructure; it imports no live term-imprecision relation.
--   * Contains no postulate, hole, catch-all clause, or permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import CastImprecisionShape using
  (narrowing; widening; _⊢ᶜ_⦂_)
open import Coercions using
  ( Coercion
  ; Mode
  ; ModeEnv
  ; id-only
  ; id-onlyᵈ
  ; mode≤
  ; renameᶜ
  ; seal-or-id
  ; tag-or-id
  )
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; rename-conceal-conversion
  ; rename-reveal-conversion
  )
open import ConversionIndexCompatibility using
  (_[_↦_]ᴸ_; _[_↦_]ᴿ_; _[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import Imprecision using
  (_ˣ⊑★; _ˣ⊑ˣ_; ⇑ᴸᵢ; ⇑ᵢ)
open import ImprecisionComposition using
  (⌊_⌋; _；_≋_; _；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  ( ImpAssm
  ; ImpCtx
  ; NonVar
  ; _∣_⊢_⊑_⊣_
  ; _↦_
  ; ∀ⁱ_
  ; ν
  )
open import NarrowWiden using
  ( narrow-renameᵗ
  ; widen-renameᵗ
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuTermImprecision using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; StoreCorresponds
  ; ctx-imp
  ; lift-ctx-[]
  ; lift-ctx-∷
  ; lift-left-ctx-[]
  ; lift-left-ctx-∷
  ; leftCtxⁱ
  ; leftStoreⁱ
  ; rightCtxⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; blame
  ; no•-$
  ; no•-·
  ; no•-Λ
  ; no•-ν
  ; no•-⊕
  ; no•-⟨⟩
  ; no•-ƛ
  ; no•-`
  ; no•-blame
  ; renameᵗᵐ
  )
open import TermTyping using
  (CastMode; SealModeStore★; _∣_∣_⊢_⦂_)
open import Types using
  ( Renameᵗ
  ; Ty
  ; TyCtx
  ; WfTy
  ; extᵗ
  ; occurs
  ; renameStoreᵗ
  ; renameᵗ
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.Core.Permutation.ForallPermutationProperties using
  (⊑ᵖ-rename²ᵢ)
open import
  proof.Core.Properties.ConversionIndexCompatibilityProperties
  using
  ( replace-left-rename²ᵢ
  ; replace-left-target-shape
  ; replace-left-transport-endpoints
  ; replace-paired-evidence-shape
  ; replace-paired-rename²ᵢ
  ; replace-paired-target-shape
  ; replace-paired-transport-endpoints
  ; replace-right-rename²ᵢ
  ; shape-transport-imprecision-endpoints
  ; transport-imprecision-endpoints
  )
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using
  ( cast-shape-rename
  ; imprecision-composition-shape-transport
  ; shape-lift∀ᵢ
  ; shape-rename
  ; shape-source-liftνᵢ
  )
open import
  proof.Core.Properties.NuImprecisionQuotientBoundaryProperties
  using (quotient-boundary-square-rename²)
open import proof.Core.Properties.NuTermProperties using
  ( modeRename-left-inverse
  ; renameStoreᵗ-ext-suc-cons-comm
  ; renameᵗᵐ-id
  ; renameᵗᵐ-preserves-No•
  ; renameᵗᵐ-preserves-Value
  )
open import proof.Core.Properties.CoercionProperties using
  (ModeRename; modeRename-id-only)
open import proof.Core.Properties.TypePreservation using
  ( CastModeRenamer
  ; castModeRenamer-seal★
  ; castModeRenamer-suc
  )
open import proof.Core.Properties.TypeProperties using
  ( RenameLeftInverse
  ; RenameLeftInverse-ext
  ; RenameLeftInverse-suc
  ; TyRenameWf
  ; TyRenameWf-ext
  ; TyRenameWf-suc
  ; occurs-zero-rename-ext
  ; renameᵗ-ext-suc-comm
  ; renameᵗ-ground
  ; renameᵗ-id
  ; renameᵗ-preserves-WfTy
  ; predᵗ
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( ∀ᵢᶜ
  ; rename-assm²-source-νᵢ
  ; rename-assm²-∀ᵢ
  ; rename-assm²-⇑ᴸᵢ
  ; rename-assm²-⇑ᵢ
  ; rename-assm²ᵢ
  ; ⊑-lift∀ᵢ
  ; ⊑-rename-at²ᵢ
  ; ⊑-renameᵗ²ᵢ
  ; ⊑-source-liftνᵢ
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using
  (AssumptionMembershipUnique; PrecisionIndexUnique)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessLemma
  using (assumption-membership-unique→precision-index-unique)
open import
  proof.Quotient.NuImprecisionReductionClosedCompatibilityRenameExperiment
  using
  ( reduction-closed-paired-compatible-rename²ᵢ
  ; reduction-closed-quotient-compatible-rename²ᵢ
  )
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
open import
  proof.Quotient.NuImprecisionReductionClosedWorldEmbeddingExperiment
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using (embed-creationᴱ)
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using
  ( embedded-creation-source-typingᴱ
  ; embedded-creation-target-typingᴱ
  )
open import
  proof.Quotient.NuImprecisionQuotientBoundarySupport
  using (SpineCastMode; gradual↓; id-only↓)
open import
  proof.Store.RelEmbedding.NuImprecisionRelCtxRenameDef
  using
  (RelCtxRenameⁱ; rel-ctx-rename-[]; rel-ctx-rename-∷)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingProof
  using (rel-store-embedding-correspondenceⁱ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using
  (lift-left-store-embeddingⁱ; lift-store-embeddingⁱ)


embedded-modeᴿ : Renameᵗ → ModeEnv → ModeEnv
embedded-modeᴿ ψ μ X = μ (ψ X)


rel-ctx-rename-lookupᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {x A B p} →
  RelCtxRenameⁱ τ σ assm hτ hσ γ γ′ →
  γ Types.∋ x ⦂ ctx-imp A B p →
  ∃[ A′ ] ∃[ B′ ] ∃[ eqA ] ∃[ eqB ]
    γ′ Types.∋ x ⦂ ctx-imp A′ B′
      (⊑-rename-at²ᵢ assm hτ hσ eqA eqB p)
rel-ctx-rename-lookupᴿ
    (rel-ctx-rename-∷ eqA eqB renameγ) Types.Z =
  _ , _ , eqA , eqB , Types.Z
rel-ctx-rename-lookupᴿ
    (rel-ctx-rename-∷ eqA eqB renameγ) (Types.S x∈) =
  let A′ , B′ , eqA′ , eqB′ , x∈′ =
        rel-ctx-rename-lookupᴿ renameγ x∈
  in
  A′ , B′ , eqA′ , eqB′ , Types.S x∈′


left-reveal-world-renameᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ α X c A B} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  RevealConversion (embedded-modeᴿ ψ μ) Θᴸ (leftStoreⁱ ρ′)
    (τ α) (renameᵗ τ X) (renameᶜ τ c)
    (renameᵗ τ A) (renameᵗ τ B)
left-reveal-world-renameᴿ
    {τ = τ} {ψ = ψ} {hτ = hτ} {μ = μ} emb conv =
  subst (λ Σ → RevealConversion _ _ Σ _ _ _ _ _)
    (sym (left-store-embedding-resultᴿ (store-embeddingᴿ emb)))
    (rename-reveal-conversion hτ
      (modeRename-left-inverse {ρ = τ} {ψ = ψ} {μ = μ}
        (left-inverseᴿ emb)) conv)


right-reveal-world-renameᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ β X c A B} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  RevealConversion μ Δᴿ (rightStoreⁱ ρ) β X c A B →
  RevealConversion (embedded-modeᴿ φ μ) Θᴿ (rightStoreⁱ ρ′)
    (σ β) (renameᵗ σ X) (renameᶜ σ c)
    (renameᵗ σ A) (renameᵗ σ B)
right-reveal-world-renameᴿ
    {σ = σ} {φ = φ} {hσ = hσ} {μ = μ} emb conv =
  subst (λ Σ → RevealConversion _ _ Σ _ _ _ _ _)
    (sym (right-store-embedding-resultᴿ (store-embeddingᴿ emb)))
    (rename-reveal-conversion hσ
      (modeRename-left-inverse {ρ = σ} {ψ = φ} {μ = μ}
        (right-inverseᴿ emb)) conv)


left-conceal-world-renameᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ α X c A B} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  ConcealConversion (embedded-modeᴿ ψ μ) Θᴸ (leftStoreⁱ ρ′)
    (τ α) (renameᵗ τ X) (renameᶜ τ c)
    (renameᵗ τ A) (renameᵗ τ B)
left-conceal-world-renameᴿ
    {τ = τ} {ψ = ψ} {hτ = hτ} {μ = μ} emb conv =
  subst (λ Σ → ConcealConversion _ _ Σ _ _ _ _ _)
    (sym (left-store-embedding-resultᴿ (store-embeddingᴿ emb)))
    (rename-conceal-conversion hτ
      (modeRename-left-inverse {ρ = τ} {ψ = ψ} {μ = μ}
        (left-inverseᴿ emb)) conv)


right-conceal-world-renameᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ β X c A B} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ConcealConversion μ Δᴿ (rightStoreⁱ ρ) β X c A B →
  ConcealConversion (embedded-modeᴿ φ μ) Θᴿ (rightStoreⁱ ρ′)
    (σ β) (renameᵗ σ X) (renameᶜ σ c)
    (renameᵗ σ A) (renameᵗ σ B)
right-conceal-world-renameᴿ
    {σ = σ} {φ = φ} {hσ = hσ} {μ = μ} emb conv =
  subst (λ Σ → ConcealConversion _ _ Σ _ _ _ _ _)
    (sym (right-store-embedding-resultᴿ (store-embeddingᴿ emb)))
    (rename-conceal-conversion hσ
      (modeRename-left-inverse {ρ = σ} {ψ = φ} {μ = μ}
        (right-inverseᴿ emb)) conv)


left-reveal-ν-world-renameᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ A B C s} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion (embedded-modeᴿ (extᵗ ψ) μ) (suc Θᴸ)
    ((zero , ⇑ᵗ (renameᵗ τ A)) ∷ ⟰ᵗ (leftStoreⁱ ρ′))
    zero (⇑ᵗ (renameᵗ τ A)) (renameᶜ (extᵗ τ) s)
    (renameᵗ (extᵗ τ) C) (⇑ᵗ (renameᵗ τ B))
left-reveal-ν-world-renameᴿ
    {Θᴸ = Θᴸ} {τ = τ} {ψ = ψ} {hτ = hτ}
    {ρ = ρ} {ρ′ = ρ′} {μ = μ}
    {A = A} {B = B} {C = C} {s = s} emb conv =
  subst
    (λ D → RevealConversion target-mode (suc Θᴸ) target-store
      zero (⇑ᵗ (renameᵗ τ A)) (renameᶜ (extᵗ τ) s)
      (renameᵗ (extᵗ τ) C) D)
    (renameᵗ-ext-suc-comm τ B)
    (subst
      (λ X → RevealConversion target-mode (suc Θᴸ) target-store
        zero X (renameᶜ (extᵗ τ) s)
        (renameᵗ (extᵗ τ) C)
        (renameᵗ (extᵗ τ) (⇑ᵗ B)))
      (renameᵗ-ext-suc-comm τ A)
      store-normalized)
  where
  target-mode = embedded-modeᴿ (extᵗ ψ) μ
  target-store =
    (zero , ⇑ᵗ (renameᵗ τ A)) ∷ ⟰ᵗ (leftStoreⁱ ρ′)

  store-eq =
    trans
      (renameStoreᵗ-ext-suc-cons-comm τ (leftStoreⁱ ρ) A)
      (cong ((zero , ⇑ᵗ (renameᵗ τ A)) ∷_)
        (cong ⟰ᵗ
          (sym (left-store-embedding-resultᴿ
            (store-embeddingᴿ emb)))))

  renamed =
    rename-reveal-conversion (TyRenameWf-ext hτ)
      (modeRename-left-inverse
        {ρ = extᵗ τ} {ψ = extᵗ ψ} {μ = μ}
        (RenameLeftInverse-ext (left-inverseᴿ emb)))
      conv

  store-normalized =
    subst
      (λ Σ → RevealConversion target-mode (suc Θᴸ) Σ
        zero (renameᵗ (extᵗ τ) (⇑ᵗ A))
        (renameᶜ (extᵗ τ) s) (renameᵗ (extᵗ τ) C)
        (renameᵗ (extᵗ τ) (⇑ᵗ B)))
      store-eq renamed


right-reveal-ν-world-renameᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ A B C s} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  RevealConversion μ (suc Δᴿ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion (embedded-modeᴿ (extᵗ φ) μ) (suc Θᴿ)
    ((zero , ⇑ᵗ (renameᵗ σ A)) ∷ ⟰ᵗ (rightStoreⁱ ρ′))
    zero (⇑ᵗ (renameᵗ σ A)) (renameᶜ (extᵗ σ) s)
    (renameᵗ (extᵗ σ) C) (⇑ᵗ (renameᵗ σ B))
right-reveal-ν-world-renameᴿ
    {Θᴿ = Θᴿ} {σ = σ} {φ = φ} {hσ = hσ}
    {ρ = ρ} {ρ′ = ρ′} {μ = μ}
    {A = A} {B = B} {C = C} {s = s} emb conv =
  subst
    (λ D → RevealConversion target-mode (suc Θᴿ) target-store
      zero (⇑ᵗ (renameᵗ σ A)) (renameᶜ (extᵗ σ) s)
      (renameᵗ (extᵗ σ) C) D)
    (renameᵗ-ext-suc-comm σ B)
    (subst
      (λ X → RevealConversion target-mode (suc Θᴿ) target-store
        zero X (renameᶜ (extᵗ σ) s)
        (renameᵗ (extᵗ σ) C)
        (renameᵗ (extᵗ σ) (⇑ᵗ B)))
      (renameᵗ-ext-suc-comm σ A)
      store-normalized)
  where
  target-mode = embedded-modeᴿ (extᵗ φ) μ
  target-store =
    (zero , ⇑ᵗ (renameᵗ σ A)) ∷ ⟰ᵗ (rightStoreⁱ ρ′)

  store-eq =
    trans
      (renameStoreᵗ-ext-suc-cons-comm σ (rightStoreⁱ ρ) A)
      (cong ((zero , ⇑ᵗ (renameᵗ σ A)) ∷_)
        (cong ⟰ᵗ
          (sym (right-store-embedding-resultᴿ
            (store-embeddingᴿ emb)))))

  renamed =
    rename-reveal-conversion (TyRenameWf-ext hσ)
      (modeRename-left-inverse
        {ρ = extᵗ σ} {ψ = extᵗ φ} {μ = μ}
        (RenameLeftInverse-ext (right-inverseᴿ emb)))
      conv

  store-normalized =
    subst
      (λ Σ → RevealConversion target-mode (suc Θᴿ) Σ
        zero (renameᵗ (extᵗ σ) (⇑ᵗ A))
        (renameᶜ (extᵗ σ) s) (renameᵗ (extᵗ σ) C)
        (renameᵗ (extᵗ σ) (⇑ᵗ B)))
      store-eq renamed


left-seal-world-renameᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode : CastMode μ) →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  SealModeStore★
    (CastModeRenamer.targetᵈ (left-cast-renamerᴿ emb) mode)
    (leftStoreⁱ ρ′)
left-seal-world-renameᴿ emb mode seal★ =
  subst (SealModeStore★ _)
    (sym (left-store-embedding-resultᴿ (store-embeddingᴿ emb)))
    (castModeRenamer-seal★
      (left-cast-renamerᴿ emb) mode seal★)


right-seal-world-renameᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  (mode : CastMode μ) →
  SealModeStore★ μ (rightStoreⁱ ρ) →
  SealModeStore★
    (CastModeRenamer.targetᵈ (right-cast-renamerᴿ emb) mode)
    (rightStoreⁱ ρ′)
right-seal-world-renameᴿ emb mode seal★ =
  subst (SealModeStore★ _)
    (sym (right-store-embedding-resultᴿ (store-embeddingᴿ emb)))
    (castModeRenamer-seal★
      (right-cast-renamerᴿ emb) mode seal★)


left-narrow-world-renameᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ μ′ c A B} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ModeRename τ μ μ′ →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  μ′ ∣ Θᴸ ∣ leftStoreⁱ ρ′
    ⊢ renameᶜ τ c ∶ renameᵗ τ A ⊒ renameᵗ τ B
left-narrow-world-renameᴿ
    {Θᴸ = Θᴸ} {τ = τ} {hτ = hτ}
    {ρ′ = ρ′} {c = c} {A = A} {B = B} emb mode c⊒ =
  subst
    (λ Σ → _ ∣ Θᴸ ∣ Σ
      ⊢ renameᶜ τ c ∶ renameᵗ τ A ⊒ renameᵗ τ B)
    (sym (left-store-embedding-resultᴿ (store-embeddingᴿ emb)))
    (narrow-renameᵗ hτ mode c⊒)


right-narrow-world-renameᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ μ′ c A B} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ModeRename σ μ μ′ →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  μ′ ∣ Θᴿ ∣ rightStoreⁱ ρ′
    ⊢ renameᶜ σ c ∶ renameᵗ σ A ⊒ renameᵗ σ B
right-narrow-world-renameᴿ
    {Θᴿ = Θᴿ} {σ = σ} {hσ = hσ}
    {ρ′ = ρ′} {c = c} {A = A} {B = B} emb mode c⊒ =
  subst
    (λ Σ → _ ∣ Θᴿ ∣ Σ
      ⊢ renameᶜ σ c ∶ renameᵗ σ A ⊒ renameᵗ σ B)
    (sym (right-store-embedding-resultᴿ (store-embeddingᴿ emb)))
    (narrow-renameᵗ hσ mode c⊒)


left-widen-world-renameᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ μ′ c A B} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ModeRename τ μ μ′ →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  μ′ ∣ Θᴸ ∣ leftStoreⁱ ρ′
    ⊢ renameᶜ τ c ∶ renameᵗ τ A ⊑ renameᵗ τ B
left-widen-world-renameᴿ
    {Θᴸ = Θᴸ} {τ = τ} {hτ = hτ}
    {ρ′ = ρ′} {c = c} {A = A} {B = B} emb mode c⊑ =
  subst
    (λ Σ → _ ∣ Θᴸ ∣ Σ
      ⊢ renameᶜ τ c ∶ renameᵗ τ A ⊑ renameᵗ τ B)
    (sym (left-store-embedding-resultᴿ (store-embeddingᴿ emb)))
    (widen-renameᵗ hτ mode c⊑)


right-widen-world-renameᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ μ′ c A B} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  ModeRename σ μ μ′ →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  μ′ ∣ Θᴿ ∣ rightStoreⁱ ρ′
    ⊢ renameᶜ σ c ∶ renameᵗ σ A ⊑ renameᵗ σ B
right-widen-world-renameᴿ
    {Θᴿ = Θᴿ} {σ = σ} {hσ = hσ}
    {ρ′ = ρ′} {c = c} {A = A} {B = B} emb mode c⊑ =
  subst
    (λ Σ → _ ∣ Θᴿ ∣ Σ
      ⊢ renameᶜ σ c ∶ renameᵗ σ A ⊑ renameᵗ σ B)
    (sym (right-store-embedding-resultᴿ (store-embeddingᴿ emb)))
    (widen-renameᵗ hσ mode c⊑)


spine-mode-world-renameᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  SpineCastMode (leftStoreⁱ ρ) μ →
  ∃[ μ′ ]
    (ModeRename τ μ μ′ × SpineCastMode (leftStoreⁱ ρ′) μ′)
spine-mode-world-renameᴿ {τ = τ} emb id-only↓ =
  id-onlyᵈ , modeRename-id-only τ , id-only↓
spine-mode-world-renameᴿ emb (gradual↓ mode seal★) =
  CastModeRenamer.targetᵈ (left-cast-renamerᴿ emb) mode ,
  CastModeRenamer.target-rename (left-cast-renamerᴿ emb) mode ,
  gradual↓
    (CastModeRenamer.target-mode (left-cast-renamerᴿ emb) mode)
    (left-seal-world-renameᴿ emb mode seal★)


spine-mode-target-world-renameᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {μ} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  SpineCastMode (rightStoreⁱ ρ) μ →
  ∃[ μ′ ]
    (ModeRename σ μ μ′ × SpineCastMode (rightStoreⁱ ρ′) μ′)
spine-mode-target-world-renameᴿ {σ = σ} emb id-only↓ =
  id-onlyᵈ , modeRename-id-only σ , id-only↓
spine-mode-target-world-renameᴿ emb (gradual↓ mode seal★) =
  CastModeRenamer.targetᵈ (right-cast-renamerᴿ emb) mode ,
  CastModeRenamer.target-rename (right-cast-renamerᴿ emb) mode ,
  gradual↓
    (CastModeRenamer.target-mode (right-cast-renamerᴿ emb) mode)
    (right-seal-world-renameᴿ emb mode seal★)


quotient-widening-pair-world-renameᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {u u′ D D′ A A′} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  QuotientWideningPairᴿ Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  QuotientWideningPairᴿ Θᴸ Θᴿ ρ′
    (renameᶜ τ u) (renameᶜ σ u′)
    (renameᵗ τ D) (renameᵗ σ D′)
    (renameᵗ τ A) (renameᵗ σ A′)
quotient-widening-pair-world-renameᴿ
    {τ = τ} {σ = σ} emb
    (quotient-id-wideningᴿ u⊑ u′⊑) =
  quotient-id-wideningᴿ
    (left-widen-world-renameᴿ emb (modeRename-id-only τ) u⊑)
    (right-widen-world-renameᴿ emb (modeRename-id-only σ) u′⊑)
quotient-widening-pair-world-renameᴿ emb
    (quotient-cast-wideningᴿ
      mode seal★ u⊑ mode′ seal★′ u′⊑) =
  quotient-cast-wideningᴿ
    (CastModeRenamer.target-mode (left-cast-renamerᴿ emb) mode)
    (left-seal-world-renameᴿ emb mode seal★)
    (left-widen-world-renameᴿ emb
      (CastModeRenamer.target-rename
        (left-cast-renamerᴿ emb) mode) u⊑)
    (CastModeRenamer.target-mode (right-cast-renamerᴿ emb) mode′)
    (right-seal-world-renameᴿ emb mode′ seal★′)
    (right-widen-world-renameᴿ emb
      (CastModeRenamer.target-rename
        (right-cast-renamerᴿ emb) mode′) u′⊑)


mode≤-reflᴿ : ∀ m → mode≤ m m ≡ true
mode≤-reflᴿ id-only = refl
mode≤-reflᴿ tag-or-id = refl
mode≤-reflᴿ seal-or-id = refl


castModeRenamer-idᴿ : CastModeRenamer (λ X → X)
castModeRenamer-idᴿ =
  record
    { targetᵈ = λ {μ} mode → μ
    ; target-mode = λ mode → mode
    ; target-rename = λ {μ} mode X → mode≤-reflᴿ (μ X)
    ; target-seal-source = λ mode α ok → α , ok , refl
    }


paired-context-lift-world-renameᴿ :
  ∀ {Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ↑ : CtxImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  PrecisionIndexUnique (∀ᵢᶜ Φ) →
  LiftCtxⁱ (∀ᵢᶜ Φ) γ γ↑ →
  RelCtxRenameⁱ suc suc rename-assm²-∀ᵢ
    TyRenameWf-suc TyRenameWf-suc γ γ↑
paired-context-lift-world-renameᴿ unique lift-ctx-[] =
  rel-ctx-rename-[]
paired-context-lift-world-renameᴿ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    unique
    (lift-ctx-∷ {γ = γ} {γ′ = γ↑}
      {A = A} {B = B} {p = p} {p′ = p↑}
      shape-eq liftγ) =
  subst
    (λ q →
      RelCtxRenameⁱ suc suc rename-assm²-∀ᵢ
        TyRenameWf-suc TyRenameWf-suc
        (ctx-imp A B p ∷ γ)
        (ctx-imp (⇑ᵗ A) (⇑ᵗ B) q ∷ γ↑))
    (unique renamed-p p↑)
    (rel-ctx-rename-∷ refl refl
      (paired-context-lift-world-renameᴿ unique liftγ))
  where
  renamed-p =
    ⊑-rename-at²ᵢ
      rename-assm²-∀ᵢ TyRenameWf-suc TyRenameWf-suc
      refl refl p


source-context-lift-world-renameᴿ :
  ∀ {Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ↑ : CtxImp
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  PrecisionIndexUnique ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ↑ →
  RelCtxRenameⁱ suc (λ X → X) rename-assm²-source-νᵢ
    TyRenameWf-suc (λ X< → X<) γ γ↑
source-context-lift-world-renameᴿ unique lift-left-ctx-[] =
  rel-ctx-rename-[]
source-context-lift-world-renameᴿ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    unique
    (lift-left-ctx-∷ {γ = γ} {γ′ = γ↑}
      {A = A} {B = B} {p = p} {p′ = p↑}
      shape-eq liftγ) =
  subst
    (λ q →
      RelCtxRenameⁱ suc (λ X → X) rename-assm²-source-νᵢ
        TyRenameWf-suc (λ X< → X<)
        (ctx-imp A B p ∷ γ)
        (ctx-imp (⇑ᵗ A) B q ∷ γ↑))
    (unique renamed-p p↑)
    (rel-ctx-rename-∷ refl (sym (renameᵗ-id B))
      (source-context-lift-world-renameᴿ unique liftγ))
  where
  renamed-p =
    ⊑-rename-at²ᵢ
      rename-assm²-source-νᵢ
      TyRenameWf-suc (λ X< → X<)
      refl (sym (renameᵗ-id B)) p


mutual
  smaller-world-embed-no•ᴿ :
    ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
      {assm : ∀ {a : ImpAssm} →
        a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
      {hτ : TyRenameWf Δᴸ Θᴸ τ}
      {hσ : TyRenameWf Δᴿ Θᴿ σ}
      {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
      {M M′ : Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    (emb : ReductionClosedWorldEmbeddingᴿ
      τ σ ψ φ assm hτ hσ
      {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
    No• M →
    No• M′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
      ⊢ᴿ renameᵗᵐ τ M ⊑ renameᵗᵐ σ M′
      ⦂ renameᵗ τ A ⊑ renameᵗ σ B
      ∶ ⊑-renameᵗ²ᵢ assm hτ hσ p

  smaller-quotient-world-embed-no•ᴿ :
    ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
      {assm : ∀ {a : ImpAssm} →
        a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
      {hτ : TyRenameWf Δᴸ Θᴸ τ}
      {hσ : TyRenameWf Δᴿ Θᴿ σ}
      {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
      {M M′ : Term} {D D′ : Ty}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
    (emb : ReductionClosedWorldEmbeddingᴿ
      τ σ ψ φ assm hτ hσ
      {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
    No• M →
    No• M′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴿᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
    Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
      ⊢ᴿᵖ renameᵗᵐ τ M ⊑ renameᵗᵐ σ M′
      ⦂ renameᵗ τ D ⊑ᵖ renameᵗ σ D′
      ∶ ⊑ᵖ-rename²ᵢ assm hτ hσ q

  smaller-world-embed-no•ᴿ emb no•-blame noM′
      (blame⊑ᴿ M′⊢) =
    blame⊑ᴿ (world-embedding-target-typingᴿ emb noM′ M′⊢)
  smaller-world-embed-no•ᴿ emb no•-` no•-`
      (x⊑xᴿ x∈)
      with rel-ctx-rename-lookupᴿ
        (context-embeddingᴿ emb) x∈
  smaller-world-embed-no•ᴿ emb no•-` no•-`
      (x⊑xᴿ x∈)
      | A′ , B′ , refl , refl , x∈′ =
    x⊑xᴿ x∈′
  smaller-world-embed-no•ᴿ
      {hτ = hτ} {hσ = hσ}
      emb (no•-ƛ noN) (no•-ƛ noN′)
      (ƛ⊑ƛᴿ hA hA′ N⊑N′) =
    ƛ⊑ƛᴿ
      (renameᵗ-preserves-WfTy hA hτ)
      (renameᵗ-preserves-WfTy hA′ hσ)
      (smaller-world-embed-no•ᴿ
        (world-embedding-context-∷ᴿ emb)
        noN noN′ N⊑N′)
  smaller-world-embed-no•ᴿ
      emb (no•-· noL noM) (no•-· noL′ noM′)
      (L⊑L′ ·ᴿ M⊑M′) =
    smaller-world-embed-no•ᴿ emb noL noL′ L⊑L′ ·ᴿ
    smaller-world-embed-no•ᴿ emb noM noM′ M⊑M′
  smaller-world-embed-no•ᴿ
      {τ = τ} {σ = σ}
      emb (no•-Λ noV) (no•-Λ noV′)
      (Λ⊑Λᴿ liftρ liftγ vV vV′ V⊑V′)
      with world-embedding-paired-liftᴿ emb liftρ liftγ
  smaller-world-embed-no•ᴿ
      {τ = τ} {σ = σ}
      emb (no•-Λ noV) (no•-Λ noV′)
      (Λ⊑Λᴿ liftρ liftγ vV vV′ V⊑V′)
      | ρ′∀ , γ′∀ , liftρ′ , liftγ′ , body-emb =
    Λ⊑Λᴿ liftρ′ liftγ′
      (renameᵗᵐ-preserves-Value (extᵗ τ) vV)
      (renameᵗᵐ-preserves-Value (extᵗ σ) vV′)
      (smaller-world-embed-no•ᴿ body-emb noV noV′ V⊑V′)
  smaller-world-embed-no•ᴿ
      {τ = τ} {A = Types.`∀ A}
      emb (no•-Λ noV) noN′
      (Λ⊑ᴿ {{safe}} occ liftρ liftγ vV V⊑N′)
      with world-embedding-source-liftᴿ emb liftρ liftγ
  smaller-world-embed-no•ᴿ
      {τ = τ} {A = Types.`∀ A}
      emb (no•-Λ noV) noN′
      (Λ⊑ᴿ {{safe}} occ liftρ liftγ vV V⊑N′)
      | ρ′ν , γ′ν , liftρ′ , liftγ′ , body-emb =
    Λ⊑ᴿ
      {{ImprecisionWf.renameNonVar (extᵗ τ) safe}}
      (trans (occurs-zero-rename-ext τ A) occ)
      liftρ′ liftγ′
      (renameᵗᵐ-preserves-Value (extᵗ τ) vV)
      (smaller-world-embed-no•ᴿ body-emb noV noN′ V⊑N′)
  smaller-world-embed-no•ᴿ
      {τ = τ} {σ = σ} {ψ = ψ} {φ = φ}
      emb noM noM′
      (allocation-prefixᴿ prefix M⊑M′ M⊢ M′⊢)
      with rel-store-embedding-prefix-invᴿ
        prefix (store-embeddingᴿ emb)
  smaller-world-embed-no•ᴿ
      {τ = τ} {σ = σ} {ψ = ψ} {φ = φ}
      emb noM noM′
      (allocation-prefixᴿ prefix M⊑M′ M⊢ M′⊢)
      | ρ₀′ , store-emb₀ , prefix′ =
    allocation-prefixᴿ prefix′
      (smaller-world-embed-no•ᴿ
        (reduction-closed-world-embeddingᴿ
          {τ = τ} {σ = σ} {ψ = ψ} {φ = φ}
          (left-inverseᴿ emb) (right-inverseᴿ emb)
          (left-cast-renamerᴿ emb) (right-cast-renamerᴿ emb)
          store-emb₀ (context-embeddingᴿ emb))
        noM noM′ M⊑M′)
      (world-embedding-source-typingᴿ emb noM M⊢)
      (world-embedding-target-typingᴿ emb noM′ M′⊢)
  smaller-world-embed-no•ᴿ
      {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
      emb (no•-ν noN) (no•-ν noN′)
      (ν⊑νᴿ {A = A} {A′ = A′}
        hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
        liftρ liftγ N⊑N′ replace)
      with world-embedding-paired-liftᴿ emb liftρ liftγ
  smaller-world-embed-no•ᴿ
      {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
      emb (no•-ν noN) (no•-ν noN′)
      (ν⊑νᴿ {A = A} {A′ = A′}
        hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
        liftρ liftγ N⊑N′ replace)
      | ρ′∀ , γ′∀ , liftρ′ , liftγ′ , body-emb =
    ν⊑νᴿ
      (renameᵗ-preserves-WfTy hA hτ)
      (renameᵗ-preserves-WfTy hA′ hσ)
      (left-reveal-ν-world-renameᴿ emb s↑)
      (right-reveal-ν-world-renameᴿ emb s′↑)
      (⊑-renameᵗ²ᵢ assm hτ hσ A⊑A′)
      shifted-A⊑A′
      liftρ′ liftγ′
      (smaller-world-embed-no•ᴿ emb noN noN′ N⊑N′)
      (replace-paired-target-shape target-shape-eq
        transported-replace)
    where
    renamed-A⇑⊑A′⇑ =
      ⊑-renameᵗ²ᵢ (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ) (TyRenameWf-ext hσ) A⇑⊑A′⇑

    shifted-A⊑A′ =
      transport-imprecision-endpoints
        (renameᵗ-ext-suc-comm τ A)
        (renameᵗ-ext-suc-comm σ A′)
        renamed-A⇑⊑A′⇑

    renamed-replace =
      replace-paired-rename²ᵢ
        {α = zero} {β = zero}
        (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ) (TyRenameWf-ext hσ) replace

    transported-replace =
      replace-paired-transport-endpoints
        refl refl
        (renameᵗ-ext-suc-comm τ _)
        (renameᵗ-ext-suc-comm σ _)
        (renameᵗ-ext-suc-comm τ A)
        (renameᵗ-ext-suc-comm σ A′)
        renamed-replace

    target-shape-eq =
      trans
        (shape-lift∀ᵢ (⊑-renameᵗ²ᵢ assm hτ hσ _))
        (trans
          (shape-rename assm hτ hσ _)
          (trans
            (sym (shape-lift∀ᵢ _))
            (trans
              (sym
                (shape-rename
                  (rename-assm²-⇑ᵢ assm)
                  (TyRenameWf-ext hτ) (TyRenameWf-ext hσ) _))
              (sym
                (shape-transport-imprecision-endpoints
                  (renameᵗ-ext-suc-comm τ _)
                  (renameᵗ-ext-suc-comm σ _) _)))))
  smaller-world-embed-no•ᴿ
      {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
      emb (no•-ν noN) noN′
      (ν⊑ᴿ {A = A} {{safe = safe}}
        hA h⇑A s↑ liftρ liftγ N⊑N′ replace)
      with world-embedding-source-liftᴿ emb liftρ liftγ
  smaller-world-embed-no•ᴿ
      {Θᴸ = Θᴸ}
      {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
      emb (no•-ν noN) noN′
      (ν⊑ᴿ {A = A} {{safe = safe}}
        hA h⇑A s↑ liftρ liftγ N⊑N′ replace)
      | ρ′ν , γ′ν , liftρ′ , liftγ′ , body-emb =
    ν⊑ᴿ {{ImprecisionWf.renameNonVar (extᵗ τ) safe}}
      (renameᵗ-preserves-WfTy hA hτ)
      h⇑A′
      (left-reveal-ν-world-renameᴿ emb s↑)
      liftρ′ liftγ′
      (smaller-world-embed-no•ᴿ emb noN noN′ N⊑N′)
      (replace-left-target-shape target-shape-eq
        transported-replace)
    where
    h⇑A′ : WfTy (suc Θᴸ) (⇑ᵗ (renameᵗ τ A))
    h⇑A′ =
      subst (WfTy (suc Θᴸ))
        (renameᵗ-ext-suc-comm τ A)
        (renameᵗ-preserves-WfTy h⇑A (TyRenameWf-ext hτ))

    renamed-replace =
      replace-left-rename²ᵢ
        {α = zero}
        (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) hσ replace

    transported-replace =
      replace-left-transport-endpoints
        refl refl
        (renameᵗ-ext-suc-comm τ _)
        (renameᵗ-ext-suc-comm τ A)
        renamed-replace

    target-shape-eq =
      trans
        (shape-source-liftνᵢ (⊑-renameᵗ²ᵢ assm hτ hσ _))
        (trans
          (shape-rename assm hτ hσ _)
          (trans
            (sym (shape-source-liftνᵢ _))
            (trans
              (sym
                (shape-rename
                  (rename-assm²-⇑ᴸᵢ assm)
                  (TyRenameWf-ext hτ) hσ _))
              (sym
                (shape-transport-imprecision-endpoints
                  (renameᵗ-ext-suc-comm τ _) refl _)))))
  smaller-world-embed-no•ᴿ emb no•-$ no•-$ κ⊑κᴿ =
    κ⊑κᴿ
  smaller-world-embed-no•ᴿ
      emb (no•-⊕ noL noM) (no•-⊕ noL′ noM′)
      (L⊑L′ ⊕ᴿ[ op ] M⊑M′) =
    smaller-world-embed-no•ᴿ emb noL noL′ L⊑L′
      ⊕ᴿ[ op ]
    smaller-world-embed-no•ᴿ emb noM noM′ M⊑M′
  smaller-world-embed-no•ᴿ
      {τ = τ} {σ = σ}
      emb (no•-⟨⟩ noV) noW
      (gen⊑groundᴿ mode seal★ c⊒ gH vV vW W⊢
        V⊑Wtag q) =
    gen⊑groundᴿ
      (CastModeRenamer.target-mode
        (left-cast-renamerᴿ emb) mode)
      (left-seal-world-renameᴿ emb mode seal★)
      (left-narrow-world-renameᴿ emb
        (CastModeRenamer.target-rename
          (left-cast-renamerᴿ emb) mode) c⊒)
      (renameᵗ-ground σ gH)
      (renameᵗᵐ-preserves-Value τ vV)
      (renameᵗᵐ-preserves-Value σ vW)
      (world-embedding-target-typingᴿ emb noW W⊢)
      (smaller-world-embed-no•ᴿ
        emb noV (no•-⟨⟩ noW) V⊑Wtag)
      _
  smaller-world-embed-no•ᴿ
      {τ = τ} {assm = assm} {hτ = hτ} {hσ = hσ}
      emb (no•-⟨⟩ noM) noM′
      (cast⊒⊑ᴿ mode seal★ c⊒ M⊑M′ q c-shape comp) =
    cast⊒⊑ᴿ
      (CastModeRenamer.target-mode
        (left-cast-renamerᴿ emb) mode)
      (left-seal-world-renameᴿ emb mode seal★)
      (left-narrow-world-renameᴿ emb
        (CastModeRenamer.target-rename
          (left-cast-renamerᴿ emb) mode) c⊒)
      (smaller-world-embed-no•ᴿ emb noM noM′ M⊑M′)
      _
      (cast-shape-rename τ c-shape)
      (imprecision-composition-shape-transport
        refl (shape-rename assm hτ hσ _)
        (shape-rename assm hτ hσ _) comp)
  smaller-world-embed-no•ᴿ
      {τ = τ} {assm = assm} {hτ = hτ} {hσ = hσ}
      emb (no•-⟨⟩ noM) noM′
      (cast⊑⊑ᴿ mode seal★ c⊑ M⊑M′ q c-shape comp) =
    cast⊑⊑ᴿ
      (CastModeRenamer.target-mode
        (left-cast-renamerᴿ emb) mode)
      (left-seal-world-renameᴿ emb mode seal★)
      (left-widen-world-renameᴿ emb
        (CastModeRenamer.target-rename
          (left-cast-renamerᴿ emb) mode) c⊑)
      (smaller-world-embed-no•ᴿ emb noM noM′ M⊑M′)
      _
      (cast-shape-rename τ c-shape)
      (imprecision-composition-shape-transport
        refl (shape-rename assm hτ hσ _)
        (shape-rename assm hτ hσ _) comp)
  smaller-world-embed-no•ᴿ
      {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
      emb noM (no•-⟨⟩ noM′)
      (⊑cast⊒ᴿ mode seal★ c⊒ M⊑M′ q c-shape comp) =
    ⊑cast⊒ᴿ
      (CastModeRenamer.target-mode
        (right-cast-renamerᴿ emb) mode)
      (right-seal-world-renameᴿ emb mode seal★)
      (right-narrow-world-renameᴿ emb
        (CastModeRenamer.target-rename
          (right-cast-renamerᴿ emb) mode) c⊒)
      (smaller-world-embed-no•ᴿ emb noM noM′ M⊑M′)
      _
      (cast-shape-rename σ c-shape)
      (imprecision-composition-shape-transport
        (shape-rename assm hτ hσ _) refl
        (shape-rename assm hτ hσ _) comp)
  smaller-world-embed-no•ᴿ
      {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
      emb noM (no•-⟨⟩ noM′)
      (⊑cast⊑ᴿ mode seal★ c⊑ M⊑M′ q c-shape comp) =
    ⊑cast⊑ᴿ
      (CastModeRenamer.target-mode
        (right-cast-renamerᴿ emb) mode)
      (right-seal-world-renameᴿ emb mode seal★)
      (right-widen-world-renameᴿ emb
        (CastModeRenamer.target-rename
          (right-cast-renamerᴿ emb) mode) c⊑)
      (smaller-world-embed-no•ᴿ emb noM noM′ M⊑M′)
      _
      (cast-shape-rename σ c-shape)
      (imprecision-composition-shape-transport
        (shape-rename assm hτ hσ _) refl
        (shape-rename assm hτ hσ _) comp)
  smaller-world-embed-no•ᴿ
      {assm = assm} {hτ = hτ} {hσ = hσ}
      emb (no•-⟨⟩ noM) noM′
      (conv↑⊑ᴿ conv M⊑M′ q replace) =
    conv↑⊑ᴿ
      (left-reveal-world-renameᴿ emb conv)
      (smaller-world-embed-no•ᴿ emb noM noM′ M⊑M′)
      _ (replace-left-rename²ᵢ assm hτ hσ replace)
  smaller-world-embed-no•ᴿ
      {assm = assm} {hτ = hτ} {hσ = hσ}
      emb (no•-⟨⟩ noM) noM′
      (conv↓⊑ᴿ conv M⊑M′ q replace) =
    conv↓⊑ᴿ
      (left-conceal-world-renameᴿ emb conv)
      (smaller-world-embed-no•ᴿ emb noM noM′ M⊑M′)
      _ (replace-left-rename²ᵢ assm hτ hσ replace)
  smaller-world-embed-no•ᴿ
      {assm = assm} {hτ = hτ} {hσ = hσ}
      emb noM (no•-⟨⟩ noM′)
      (⊑conv↑ᴿ conv M⊑M′ q replace) =
    ⊑conv↑ᴿ
      (right-reveal-world-renameᴿ emb conv)
      (smaller-world-embed-no•ᴿ emb noM noM′ M⊑M′)
      _ (replace-right-rename²ᵢ assm hτ hσ replace)
  smaller-world-embed-no•ᴿ
      {assm = assm} {hτ = hτ} {hσ = hσ}
      emb noM (no•-⟨⟩ noM′)
      (⊑conv↓ᴿ conv M⊑M′ q replace) =
    ⊑conv↓ᴿ
      (right-conceal-world-renameᴿ emb conv)
      (smaller-world-embed-no•ᴿ emb noM noM′ M⊑M′)
      _ (replace-right-rename²ᵢ assm hτ hσ replace)
  smaller-world-embed-no•ᴿ
      {assm = assm} {hτ = hτ} {hσ = hσ}
      emb (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (paired-revealᴿ {pX = pX}
        corr conv conv′ replace M⊑M′)
      with rel-store-embedding-correspondenceⁱ
        (store-embeddingᴿ emb) corr
  smaller-world-embed-no•ᴿ
      {assm = assm} {hτ = hτ} {hσ = hσ}
      emb (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (paired-revealᴿ {pX = pX}
        corr conv conv′ replace M⊑M′)
      | α′ , X , β′ , X′ , p′ ,
        refl , refl , refl , refl , shape-eq , corr′ =
    paired-revealᴿ corr′
      (left-reveal-world-renameᴿ emb conv)
      (right-reveal-world-renameᴿ emb conv′)
      (replace-paired-evidence-shape
        (trans shape-eq (sym (shape-rename assm hτ hσ pX)))
        (replace-paired-rename²ᵢ assm hτ hσ replace))
      (smaller-world-embed-no•ᴿ emb noM noM′ M⊑M′)
  smaller-world-embed-no•ᴿ
      {assm = assm} {hτ = hτ} {hσ = hσ}
      emb (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (paired-concealᴿ {pX = pX}
        corr conv conv′ replace M⊑M′)
      with rel-store-embedding-correspondenceⁱ
        (store-embeddingᴿ emb) corr
  smaller-world-embed-no•ᴿ
      {assm = assm} {hτ = hτ} {hσ = hσ}
      emb (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (paired-concealᴿ {pX = pX}
        corr conv conv′ replace M⊑M′)
      | α′ , X , β′ , X′ , p′ ,
        refl , refl , refl , refl , shape-eq , corr′ =
    paired-concealᴿ corr′
      (left-conceal-world-renameᴿ emb conv)
      (right-conceal-world-renameᴿ emb conv′)
      (replace-paired-evidence-shape
        (trans shape-eq (sym (shape-rename assm hτ hσ pX)))
        (replace-paired-rename²ᵢ assm hτ hσ replace))
      (smaller-world-embed-no•ᴿ emb noM noM′ M⊑M′)
  smaller-world-embed-no•ᴿ
      {τ = τ} {σ = σ} {ψ = ψ} {φ = φ}
      {assm = assm} {hτ = hτ} {hσ = hσ}
      {ρ = ρ} {ρ′ = ρ′}
      emb noM noM′ (target-instantiationᴿ creation) =
    target-instantiationᴿ
      (embed-creationᴱ creation assm hτ hσ
        (store-embeddingᴿ emb)
        (world-embedding-source-typingᴿ
          empty-emb noM
          (embedded-creation-source-typingᴱ creation))
        (world-embedding-target-typingᴿ
          empty-emb noM′
          (embedded-creation-target-typingᴱ creation)))
    where
    empty-emb :
      ReductionClosedWorldEmbeddingᴿ
        τ σ ψ φ assm hτ hσ
        {ρ = ρ} {ρ′ = ρ′} {γ = []} {γ′ = []}
    empty-emb =
      reduction-closed-world-embeddingᴿ
        {τ = τ} {σ = σ} {ψ = ψ} {φ = φ}
        (left-inverseᴿ emb) (right-inverseᴿ emb)
        (left-cast-renamerᴿ emb) (right-cast-renamerᴿ emb)
        (store-embeddingᴿ emb) rel-ctx-rename-[]
  smaller-world-embed-no•ᴿ
      {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
      emb (no•-⟨⟩ noN) (no•-⟨⟩ noN′)
      (closeᴿ N⊑N′ widen-pair u-shape u′-shape square compat) =
    closeᴿ
      (smaller-quotient-world-embed-no•ᴿ
        emb noN noN′ N⊑N′)
      (quotient-widening-pair-world-renameᴿ emb widen-pair)
      (cast-shape-rename τ u-shape)
      (cast-shape-rename σ u′-shape)
      (quotient-boundary-square-rename²
        {τ = τ} {σ = σ} {assm = assm}
        {hτ = hτ} {hσ = hσ} square)
      (reduction-closed-quotient-compatible-rename²ᵢ
        {assm = assm} hτ hσ compat)
  smaller-world-embed-no•ᴿ
      {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
      emb (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (paired-wideningᴿ
        mode seal★ c⊑ c-shape
        mode′ seal★′ c′⊑ c′-shape
        left-square right-square compat M⊑M′) =
    paired-wideningᴿ
      (CastModeRenamer.target-mode
        (left-cast-renamerᴿ emb) mode)
      (left-seal-world-renameᴿ emb mode seal★)
      (left-widen-world-renameᴿ emb
        (CastModeRenamer.target-rename
          (left-cast-renamerᴿ emb) mode) c⊑)
      (cast-shape-rename τ c-shape)
      (CastModeRenamer.target-mode
        (right-cast-renamerᴿ emb) mode′)
      (right-seal-world-renameᴿ emb mode′ seal★′)
      (right-widen-world-renameᴿ emb
        (CastModeRenamer.target-rename
          (right-cast-renamerᴿ emb) mode′) c′⊑)
      (cast-shape-rename σ c′-shape)
      (imprecision-composition-shape-transport
        refl (shape-rename assm hτ hσ _)
        refl left-square)
      (imprecision-composition-shape-transport
        (shape-rename assm hτ hσ _)
        refl refl right-square)
      (reduction-closed-paired-compatible-rename²ᵢ
        {assm = assm} hτ hσ compat)
      (smaller-world-embed-no•ᴿ emb noM noM′ M⊑M′)

  smaller-quotient-world-embed-no•ᴿ
      {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
      emb (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (paired-downᴿ
        M⊑M′ mode d⊒ d-shape
        mode′ d′⊒ d′-shape square)
      with spine-mode-world-renameᴿ emb mode
         | spine-mode-target-world-renameᴿ emb mode′
  smaller-quotient-world-embed-no•ᴿ
      {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
      emb (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (paired-downᴿ
        M⊑M′ mode d⊒ d-shape
        mode′ d′⊒ d′-shape square)
      | μ , mode-rename , modeᴿ
      | μ′ , mode-rename′ , mode′ᴿ =
    paired-downᴿ
      (smaller-world-embed-no•ᴿ emb noM noM′ M⊑M′)
      modeᴿ
      (left-narrow-world-renameᴿ emb mode-rename d⊒)
      (cast-shape-rename τ d-shape)
      mode′ᴿ
      (right-narrow-world-renameᴿ emb mode-rename′ d′⊒)
      (cast-shape-rename σ d′-shape)
      (quotient-boundary-square-rename²
        {τ = τ} {σ = σ} {assm = assm}
        {hτ = hτ} {hσ = hσ} square)


smaller-paired-type-world-weakenᴿ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ↑ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ↑ : CtxImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {M M′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  AssumptionMembershipUnique (∀ᵢᶜ Φ) →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ↑ →
  LiftCtxⁱ (∀ᵢᶜ Φ) γ γ↑ →
  No• M →
  No• M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  ∀ᵢᶜ Φ
    ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ↑ ∣ γ↑
    ⊢ᴿ renameᵗᵐ suc M ⊑ renameᵗᵐ suc M′
    ⦂ ⇑ᵗ A ⊑ ⇑ᵗ B ∶ ⊑-lift∀ᵢ p
smaller-paired-type-world-weakenᴿ
    unique liftρ liftγ noM noM′ M⊑M′ =
  smaller-world-embed-no•ᴿ
    (reduction-closed-world-embeddingᴿ
      {τ = suc} {σ = suc} {ψ = predᵗ} {φ = predᵗ}
      RenameLeftInverse-suc RenameLeftInverse-suc
      castModeRenamer-suc castModeRenamer-suc
      (lift-store-embeddingⁱ liftρ)
      (paired-context-lift-world-renameᴿ
        (assumption-membership-unique→precision-index-unique unique)
        liftγ))
    noM noM′ M⊑M′


smaller-target-type-index-transportᴿ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B B′}
    {p′ : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  (eqB : B′ ≡ B) →
  subst (λ T → Φ ∣ Δᴸ ⊢ A ⊑ T ⊣ Δᴿ) eqB p′ ≡ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B′ ∶ p′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p
smaller-target-type-index-transportᴿ refl refl M⊑M′ =
  M⊑M′


smaller-target-term-transportᴿ :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ N′ A B p} →
  M′ ≡ N′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⊑ N′ ⦂ A ⊑ B ∶ p
smaller-target-term-transportᴿ refl M⊑M′ =
  M⊑M′


smaller-source-type-world-weakenᴿ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ↑ : StoreImp
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ↑ : CtxImp
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {M M′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  AssumptionMembershipUnique ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ↑ →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ↑ →
  No• M →
  No• M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣ ρ↑ ∣ γ↑
    ⊢ᴿ renameᵗᵐ suc M ⊑ M′
    ⦂ ⇑ᵗ A ⊑ B ∶ ⊑-source-liftνᵢ p
smaller-source-type-world-weakenᴿ
    {M′ = M′} {B = B}
    unique liftρ liftγ noM noM′ M⊑M′ =
  smaller-target-term-transportᴿ (renameᵗᵐ-id M′)
    (smaller-target-type-index-transportᴿ
      (renameᵗ-id B) refl
      (smaller-world-embed-no•ᴿ
        (reduction-closed-world-embeddingᴿ
          {τ = suc} {σ = λ X → X}
          {ψ = predᵗ} {φ = λ X → X}
          RenameLeftInverse-suc (λ X → refl)
          castModeRenamer-suc castModeRenamer-idᴿ
          (lift-left-store-embeddingⁱ liftρ)
          (source-context-lift-world-renameᴿ
            (assumption-membership-unique→precision-index-unique unique)
            liftγ))
        noM noM′ M⊑M′))
