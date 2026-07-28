module
  proof.Quotient.NuImprecisionReductionClosedWorldEmbeddingExperiment
  where

-- File Charter:
--   * Defines the QTI-free relational-world embedding used by the
--     reduction-closed smaller-relation experiments.
--   * Pushes an arbitrary world embedding through term-context extension,
--     paired type-binder lifting, and source-only type-binder lifting.
--   * Inverts the experiment's store-prefix evidence through a structural
--     relational-store embedding.
--   * Depends only on type, cast-mode, store, context, and experimental
--     prefix infrastructure; it imports no term-imprecision relation.
--   * Contains no postulate, hole, catch-all clause, or permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import ImprecisionComposition using (⌊_⌋)
open import ImprecisionWf using
  ( ImpAssm
  ; ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᴸᵢ
  ; ⇑ᵢ
  ; _∣_⊢_⊑_⊣_
  )
open import Imprecision using (⇑ᴿᵢ)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
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
  ; rightStoreⁱ
  ; store-left
  ; store-link
  ; store-matched
  ; store-right
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftCtxⁱ
  ; ctx-imp
  ; leftCtxⁱ
  ; lift-ctx-[]
  ; lift-ctx-∷
  ; lift-left-ctx-[]
  ; lift-left-ctx-∷
  ; rightCtxⁱ
  )
open import NuTerms using (No•; Term; renameᵗᵐ)
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using
  (Renameᵗ; Ty; TyCtx; extᵗ; renameᵗ; renameStoreᵗ; ⇑ᵗ)
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using
  ( shape-rename
  ; shape-subst-source
  ; shape-subst-target
  )
open import proof.Core.Properties.TypePreservation using
  (CastModeRenamer; castModeRenamer-ext; typing-renameᵀ)
open import proof.Core.Properties.TypeProperties using
  ( RenameLeftInverse
  ; RenameLeftInverse-ext
  ; TyRenameWf
  ; TyRenameWf-ext
  ; TyRenameWf-suc
  ; renameᵗ-ext-suc-comm
  ; renameᵗ-preserves-WfTy
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  ( ∀ᵢᶜ
  ; rename-assm²ᵢ
  ; rename-assm²-⇑ᴸᵢ
  ; rename-assm²-⇑ᵢ
  ; ⊑-rename-at²ᵢ
  ; ⊑-renameᵗ²ᵢ
  )
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using
  (StoreImpPrefixᴿ; prefix-reflᴿ; prefix-∷ᴿ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelCtxRenameDef
  using
  ( RelCtxRenameⁱ
  ; rel-ctx-rename-[]
  ; rel-ctx-rename-∷
  )
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef
  using
  ( RelStoreEmbeddingⁱ
  ; rel-store-embedding-[]
  ; rel-store-embedding-left
  ; rel-store-embedding-link
  ; rel-store-embedding-matched
  ; rel-store-embedding-right
  )


record ReductionClosedWorldEmbeddingᴿ
    {Φ Ψ : ImpCtx} {Δᴸ Δᴿ Θᴸ Θᴿ : TyCtx}
    (τ σ ψ φ : Renameᵗ)
    (assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ)
    (hτ : TyRenameWf Δᴸ Θᴸ τ)
    (hσ : TyRenameWf Δᴿ Θᴿ σ)
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ} : Set₁ where
  constructor reduction-closed-world-embeddingᴿ
  field
    left-inverseᴿ : RenameLeftInverse τ ψ
    right-inverseᴿ : RenameLeftInverse σ φ
    left-cast-renamerᴿ : CastModeRenamer τ
    right-cast-renamerᴿ : CastModeRenamer σ
    store-embeddingᴿ : RelStoreEmbeddingⁱ τ σ ρ ρ′
    context-embeddingᴿ : RelCtxRenameⁱ τ σ assm hτ hσ γ γ′

open ReductionClosedWorldEmbeddingᴿ public


left-store-embedding-resultᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ} →
  (emb : RelStoreEmbeddingⁱ τ σ ρ ρ′) →
  leftStoreⁱ ρ′ ≡ renameStoreᵗ τ (leftStoreⁱ ρ)
left-store-embedding-resultᴿ rel-store-embedding-[] = refl
left-store-embedding-resultᴿ
    (rel-store-embedding-matched eqα eqA eqβ eqB shape-eq emb) =
  cong₂ _∷_ (cong₂ _,_ eqα eqA)
    (left-store-embedding-resultᴿ emb)
left-store-embedding-resultᴿ
    (rel-store-embedding-left eqα eqA emb) =
  cong₂ _∷_ (cong₂ _,_ eqα eqA)
    (left-store-embedding-resultᴿ emb)
left-store-embedding-resultᴿ
    (rel-store-embedding-right eqβ eqB emb) =
  left-store-embedding-resultᴿ emb
left-store-embedding-resultᴿ
    (rel-store-embedding-link eqα eqA eqβ eqB shape-eq emb) =
  left-store-embedding-resultᴿ emb


right-store-embedding-resultᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ} →
  (emb : RelStoreEmbeddingⁱ τ σ ρ ρ′) →
  rightStoreⁱ ρ′ ≡ renameStoreᵗ σ (rightStoreⁱ ρ)
right-store-embedding-resultᴿ rel-store-embedding-[] = refl
right-store-embedding-resultᴿ
    (rel-store-embedding-matched eqα eqA eqβ eqB shape-eq emb) =
  cong₂ _∷_ (cong₂ _,_ eqβ eqB)
    (right-store-embedding-resultᴿ emb)
right-store-embedding-resultᴿ
    (rel-store-embedding-left eqα eqA emb) =
  right-store-embedding-resultᴿ emb
right-store-embedding-resultᴿ
    (rel-store-embedding-right eqβ eqB emb) =
  cong₂ _∷_ (cong₂ _,_ eqβ eqB)
    (right-store-embedding-resultᴿ emb)
right-store-embedding-resultᴿ
    (rel-store-embedding-link eqα eqA eqβ eqB shape-eq emb) =
  right-store-embedding-resultᴿ emb


left-context-embedding-resultᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ} →
  RelCtxRenameⁱ τ σ assm hτ hσ γ γ′ →
  leftCtxⁱ γ′ ≡ map (renameᵗ τ) (leftCtxⁱ γ)
left-context-embedding-resultᴿ rel-ctx-rename-[] = refl
left-context-embedding-resultᴿ
    (rel-ctx-rename-∷ eqA eqB emb) =
  cong₂ _∷_ eqA (left-context-embedding-resultᴿ emb)


right-context-embedding-resultᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ} →
  RelCtxRenameⁱ τ σ assm hτ hσ γ γ′ →
  rightCtxⁱ γ′ ≡ map (renameᵗ σ) (rightCtxⁱ γ)
right-context-embedding-resultᴿ rel-ctx-rename-[] = refl
right-context-embedding-resultᴿ
    (rel-ctx-rename-∷ eqA eqB emb) =
  cong₂ _∷_ eqB (right-context-embedding-resultᴿ emb)


world-embedding-source-typingᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M : Term} {A : Ty} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  No• M →
  Δᴸ ∣ leftStoreⁱ ρ ∣ leftCtxⁱ γ ⊢ M ⦂ A →
  Θᴸ ∣ leftStoreⁱ ρ′ ∣ leftCtxⁱ γ′
    ⊢ renameᵗᵐ τ M ⦂ renameᵗ τ A
world-embedding-source-typingᴿ
    {Θᴸ = Θᴸ} {τ = τ} {ψ = ψ} {hτ = hτ}
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}
    {M = M} {A = A} emb noM M⊢ =
  subst
    (λ Γ → Θᴸ ∣ leftStoreⁱ ρ′ ∣ Γ
      ⊢ renameᵗᵐ τ M ⦂ renameᵗ τ A)
    (sym (left-context-embedding-resultᴿ
      (context-embeddingᴿ emb)))
    (subst
      (λ Σ → Θᴸ ∣ Σ ∣ map (renameᵗ τ) (leftCtxⁱ γ)
        ⊢ renameᵗᵐ τ M ⦂ renameᵗ τ A)
      (sym (left-store-embedding-resultᴿ
        (store-embeddingᴿ emb)))
      (typing-renameᵀ {ρ = τ} {ψ = ψ} hτ
        (left-inverseᴿ emb) (left-cast-renamerᴿ emb)
        noM M⊢))


world-embedding-target-typingᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M : Term} {B : Ty} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  No• M →
  Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M ⦂ B →
  Θᴿ ∣ rightStoreⁱ ρ′ ∣ rightCtxⁱ γ′
    ⊢ renameᵗᵐ σ M ⦂ renameᵗ σ B
world-embedding-target-typingᴿ
    {Θᴿ = Θᴿ} {σ = σ} {φ = φ} {hσ = hσ}
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}
    {M = M} {B = B} emb noM M⊢ =
  subst
    (λ Γ → Θᴿ ∣ rightStoreⁱ ρ′ ∣ Γ
      ⊢ renameᵗᵐ σ M ⦂ renameᵗ σ B)
    (sym (right-context-embedding-resultᴿ
      (context-embeddingᴿ emb)))
    (subst
      (λ Σ → Θᴿ ∣ Σ ∣ map (renameᵗ σ) (rightCtxⁱ γ)
        ⊢ renameᵗᵐ σ M ⦂ renameᵗ σ B)
      (sym (right-store-embedding-resultᴿ
        (store-embeddingᴿ emb)))
      (typing-renameᵀ {ρ = σ} {ψ = φ} hσ
        (right-inverseᴿ emb) (right-cast-renamerᴿ emb)
        noM M⊢))


⊑-rename-at-shapeᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ A A′ B B′}
    (assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ)
    (hτ : TyRenameWf Δᴸ Θᴸ τ)
    (hσ : TyRenameWf Δᴿ Θᴿ σ)
    (eqA : A′ ≡ renameᵗ τ A)
    (eqB : B′ ≡ renameᵗ σ B)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊ ⊑-rename-at²ᵢ assm hτ hσ eqA eqB p ⌋ ≡ ⌊ p ⌋
⊑-rename-at-shapeᴿ assm hτ hσ eqA eqB p =
  trans
    (shape-subst-target (sym eqB)
      (subst
        (λ T → _ ∣ _ ⊢ T ⊑ renameᵗ _ _ ⊣ _)
        (sym eqA)
        (⊑-renameᵗ²ᵢ assm hτ hσ p)))
    (trans
      (shape-subst-source
        (sym eqA)
        (⊑-renameᵗ²ᵢ assm hτ hσ p))
      (shape-rename assm hτ hσ p))


world-embedding-context-∷ᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {A B p} →
  ReductionClosedWorldEmbeddingᴿ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′} →
  ReductionClosedWorldEmbeddingᴿ τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′}
    {γ = ctx-imp A B p ∷ γ}
    {γ′ = ctx-imp (renameᵗ τ A) (renameᵗ σ B)
      (⊑-renameᵗ²ᵢ assm hτ hσ p) ∷ γ′}
world-embedding-context-∷ᴿ emb =
  reduction-closed-world-embeddingᴿ
    (left-inverseᴿ emb) (right-inverseᴿ emb)
    (left-cast-renamerᴿ emb) (right-cast-renamerᴿ emb)
    (store-embeddingᴿ emb)
    (rel-ctx-rename-∷ refl refl (context-embeddingᴿ emb))


rel-store-embedding-paired-liftᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {ρ∀ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  RelStoreEmbeddingⁱ τ σ ρ ρ′ →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ∀ →
  ∃[ ρ′∀ ]
    LiftStoreⁱ (∀ᵢᶜ Ψ) ρ′ ρ′∀ ×
    RelStoreEmbeddingⁱ (extᵗ τ) (extᵗ σ) ρ∀ ρ′∀
rel-store-embedding-paired-liftᴿ
    rel-store-embedding-[] lift-store-[] =
  [] , lift-store-[] , rel-store-embedding-[]
rel-store-embedding-paired-liftᴿ
    {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-matched
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-store-∷ {p′ = p∀} shape∀ liftρ)
    with rel-store-embedding-paired-liftᴿ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-paired-liftᴿ
    {τ = τ} {σ = σ} {assm = assm}
    {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-matched
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-store-∷
      {A = A} {B = B} {p′ = p∀} shape∀ liftρ)
    | ρ′∀ , liftρ′ , emb∀ =
  store-matched (suc α′) (⇑ᵗ A′) (suc β′) (⇑ᵗ B′)
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ) (TyRenameWf-ext hσ)
        eqA∀ eqB∀ p∀) ∷ ρ′∀ ,
  lift-store-∷
    (trans
      (⊑-rename-at-shapeᴿ
        (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ) (TyRenameWf-ext hσ)
        eqA∀ eqB∀ p∀)
      (trans shape∀ (sym shape-emb)))
    liftρ′ ,
  rel-store-embedding-matched
    (cong suc eqα) eqA∀ (cong suc eqβ) eqB∀
    (⊑-rename-at-shapeᴿ
      (rename-assm²-⇑ᵢ assm)
      (TyRenameWf-ext hτ) (TyRenameWf-ext hσ)
      eqA∀ eqB∀ p∀)
    emb∀
  where
  eqA∀ : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqA∀ =
    trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))

  eqB∀ : ⇑ᵗ B′ ≡ renameᵗ (extᵗ σ) (⇑ᵗ B)
  eqB∀ =
    trans (cong ⇑ᵗ eqB) (sym (renameᵗ-ext-suc-comm σ B))
rel-store-embedding-paired-liftᴿ
    {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-left
      {α′ = α′} {A′ = A′} {hA′ = hA′} eqα eqA emb)
    (lift-store-left liftρ)
    with rel-store-embedding-paired-liftᴿ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-paired-liftᴿ {τ = τ}
    (rel-store-embedding-left
      {α′ = α′} {A′ = A′} {hA′ = hA′} eqα eqA emb)
    (lift-store-left {A = A} liftρ)
    | ρ′∀ , liftρ′ , emb∀ =
  store-left (suc α′) (⇑ᵗ A′)
      (renameᵗ-preserves-WfTy hA′ TyRenameWf-suc) ∷ ρ′∀ ,
  lift-store-left liftρ′ ,
  rel-store-embedding-left (cong suc eqα) eqA∀ emb∀
  where
  eqA∀ : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqA∀ =
    trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))
rel-store-embedding-paired-liftᴿ
    {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-right
      {β′ = β′} {B′ = B′} {hB′ = hB′} eqβ eqB emb)
    (lift-store-right liftρ)
    with rel-store-embedding-paired-liftᴿ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-paired-liftᴿ {σ = σ}
    (rel-store-embedding-right
      {β′ = β′} {B′ = B′} {hB′ = hB′} eqβ eqB emb)
    (lift-store-right {B = B} liftρ)
    | ρ′∀ , liftρ′ , emb∀ =
  store-right (suc β′) (⇑ᵗ B′)
      (renameᵗ-preserves-WfTy hB′ TyRenameWf-suc) ∷ ρ′∀ ,
  lift-store-right liftρ′ ,
  rel-store-embedding-right (cong suc eqβ) eqB∀ emb∀
  where
  eqB∀ : ⇑ᵗ B′ ≡ renameᵗ (extᵗ σ) (⇑ᵗ B)
  eqB∀ =
    trans (cong ⇑ᵗ eqB) (sym (renameᵗ-ext-suc-comm σ B))
rel-store-embedding-paired-liftᴿ
    {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-link
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-store-link {p′ = p∀} shape∀ liftρ)
    with rel-store-embedding-paired-liftᴿ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-paired-liftᴿ
    {τ = τ} {σ = σ} {assm = assm}
    {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-link
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-store-link
      {A = A} {B = B} {p′ = p∀} shape∀ liftρ)
    | ρ′∀ , liftρ′ , emb∀ =
  store-link (suc α′) (⇑ᵗ A′) (suc β′) (⇑ᵗ B′)
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ) (TyRenameWf-ext hσ)
        eqA∀ eqB∀ p∀) ∷ ρ′∀ ,
  lift-store-link
    (trans
      (⊑-rename-at-shapeᴿ
        (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ) (TyRenameWf-ext hσ)
        eqA∀ eqB∀ p∀)
      (trans shape∀ (sym shape-emb)))
    liftρ′ ,
  rel-store-embedding-link
    (cong suc eqα) eqA∀ (cong suc eqβ) eqB∀
    (⊑-rename-at-shapeᴿ
      (rename-assm²-⇑ᵢ assm)
      (TyRenameWf-ext hτ) (TyRenameWf-ext hσ)
      eqA∀ eqB∀ p∀)
    emb∀
  where
  eqA∀ : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqA∀ =
    trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))

  eqB∀ : ⇑ᵗ B′ ≡ renameᵗ (extᵗ σ) (⇑ᵗ B)
  eqB∀ =
    trans (cong ⇑ᵗ eqB) (sym (renameᵗ-ext-suc-comm σ B))


rel-context-embedding-paired-liftᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {γ∀ : CtxImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  RelCtxRenameⁱ τ σ assm hτ hσ γ γ′ →
  LiftCtxⁱ (∀ᵢᶜ Φ) γ γ∀ →
  ∃[ γ′∀ ]
    LiftCtxⁱ (∀ᵢᶜ Ψ) γ′ γ′∀ ×
    RelCtxRenameⁱ
      (extᵗ τ) (extᵗ σ) (rename-assm²-⇑ᵢ assm)
      (TyRenameWf-ext hτ) (TyRenameWf-ext hσ) γ∀ γ′∀
rel-context-embedding-paired-liftᴿ
    rel-ctx-rename-[] lift-ctx-[] =
  [] , lift-ctx-[] , rel-ctx-rename-[]
rel-context-embedding-paired-liftᴿ
    (rel-ctx-rename-∷ {A′ = A′} {B′ = B′} {p = p}
      eqA eqB renameγ)
    (lift-ctx-∷ {p′ = p∀} shape∀ liftγ)
    with rel-context-embedding-paired-liftᴿ renameγ liftγ
rel-context-embedding-paired-liftᴿ
    {τ = τ} {σ = σ} {assm = assm}
    {hτ = hτ} {hσ = hσ}
    (rel-ctx-rename-∷ {A′ = A′} {B′ = B′} {p = p}
      eqA eqB renameγ)
    (lift-ctx-∷
      {A = A} {B = B} {p′ = p∀} shape∀ liftγ)
    | γ′∀ , liftγ′ , renameγ∀ =
  ctx-imp (⇑ᵗ A′) (⇑ᵗ B′)
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ) (TyRenameWf-ext hσ)
        eqA∀ eqB∀ p∀) ∷ γ′∀ ,
  lift-ctx-∷
    (trans
      (⊑-rename-at-shapeᴿ
        (rename-assm²-⇑ᵢ assm)
        (TyRenameWf-ext hτ) (TyRenameWf-ext hσ)
        eqA∀ eqB∀ p∀)
      (trans shape∀
        (sym (⊑-rename-at-shapeᴿ
          assm hτ hσ eqA eqB p))))
    liftγ′ ,
  rel-ctx-rename-∷ eqA∀ eqB∀ renameγ∀
  where
  eqA∀ : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqA∀ =
    trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))

  eqB∀ : ⇑ᵗ B′ ≡ renameᵗ (extᵗ σ) (⇑ᵗ B)
  eqB∀ =
    trans (cong ⇑ᵗ eqB) (sym (renameᵗ-ext-suc-comm σ B))


world-embedding-paired-liftᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {ρ∀ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
    {γ∀ : CtxImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ∀ →
  LiftCtxⁱ (∀ᵢᶜ Φ) γ γ∀ →
  ∃[ ρ′∀ ] ∃[ γ′∀ ]
    LiftStoreⁱ (∀ᵢᶜ Ψ) ρ′ ρ′∀ ×
    LiftCtxⁱ (∀ᵢᶜ Ψ) γ′ γ′∀ ×
    ReductionClosedWorldEmbeddingᴿ
      (extᵗ τ) (extᵗ σ) (extᵗ ψ) (extᵗ φ)
      (rename-assm²-⇑ᵢ assm)
      (TyRenameWf-ext hτ) (TyRenameWf-ext hσ)
      {ρ = ρ∀} {ρ′ = ρ′∀} {γ = γ∀} {γ′ = γ′∀}
world-embedding-paired-liftᴿ
    {assm = assm} {hτ = hτ} {hσ = hσ}
    emb liftρ liftγ
    with rel-store-embedding-paired-liftᴿ
      {assm = assm} {hτ = hτ} {hσ = hσ}
      (store-embeddingᴿ emb) liftρ
       | rel-context-embedding-paired-liftᴿ
          (context-embeddingᴿ emb) liftγ
world-embedding-paired-liftᴿ emb liftρ liftγ
    | ρ′∀ , liftρ′ , embρ∀
    | γ′∀ , liftγ′ , embγ∀ =
  ρ′∀ , γ′∀ , liftρ′ , liftγ′ ,
  reduction-closed-world-embeddingᴿ
    (RenameLeftInverse-ext (left-inverseᴿ emb))
    (RenameLeftInverse-ext (right-inverseᴿ emb))
    (castModeRenamer-ext (left-cast-renamerᴿ emb))
    (castModeRenamer-ext (right-cast-renamerᴿ emb))
    embρ∀ embγ∀


rel-store-embedding-source-liftᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ} →
  RelStoreEmbeddingⁱ τ σ ρ ρ′ →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  ∃[ ρ′ν ]
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) ρ′ ρ′ν ×
    RelStoreEmbeddingⁱ (extᵗ τ) σ ρν ρ′ν
rel-store-embedding-source-liftᴿ
    rel-store-embedding-[] lift-left-store-[] =
  [] , lift-left-store-[] , rel-store-embedding-[]
rel-store-embedding-source-liftᴿ
    {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-matched
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-left-store-∷ {p′ = pν} shapeν liftρ)
    with rel-store-embedding-source-liftᴿ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-source-liftᴿ
    {τ = τ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-matched
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-left-store-∷
      {A = A} {B = B} {p′ = pν} shapeν liftρ)
    | ρ′ν , liftρ′ , embν =
  store-matched (suc α′) (⇑ᵗ A′) β′ B′
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) hσ eqAν eqB pν) ∷ ρ′ν ,
  lift-left-store-∷
    (trans
      (⊑-rename-at-shapeᴿ
        (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) hσ eqAν eqB pν)
      (trans shapeν (sym shape-emb)))
    liftρ′ ,
  rel-store-embedding-matched
    (cong suc eqα) eqAν eqβ eqB
    (⊑-rename-at-shapeᴿ
      (rename-assm²-⇑ᴸᵢ assm)
      (TyRenameWf-ext hτ) hσ eqAν eqB pν)
    embν
  where
  eqAν : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqAν =
    trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))
rel-store-embedding-source-liftᴿ
    {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-left
      {α′ = α′} {A′ = A′} {hA′ = hA′} eqα eqA emb)
    (lift-left-store-left liftρ)
    with rel-store-embedding-source-liftᴿ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-source-liftᴿ {τ = τ}
    (rel-store-embedding-left
      {α′ = α′} {A′ = A′} {hA′ = hA′} eqα eqA emb)
    (lift-left-store-left {A = A} liftρ)
    | ρ′ν , liftρ′ , embν =
  store-left (suc α′) (⇑ᵗ A′)
      (renameᵗ-preserves-WfTy hA′ TyRenameWf-suc) ∷ ρ′ν ,
  lift-left-store-left liftρ′ ,
  rel-store-embedding-left (cong suc eqα) eqAν embν
  where
  eqAν : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqAν =
    trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))
rel-store-embedding-source-liftᴿ
    {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-right
      {β′ = β′} {B′ = B′} {hB′ = hB′} eqβ eqB emb)
    (lift-left-store-right liftρ)
    with rel-store-embedding-source-liftᴿ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-source-liftᴿ
    (rel-store-embedding-right
      {β′ = β′} {B′ = B′} {hB′ = hB′} eqβ eqB emb)
    (lift-left-store-right liftρ)
    | ρ′ν , liftρ′ , embν =
  store-right β′ B′ hB′ ∷ ρ′ν ,
  lift-left-store-right liftρ′ ,
  rel-store-embedding-right eqβ eqB embν
rel-store-embedding-source-liftᴿ
    {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-link
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-left-store-link {p′ = pν} shapeν liftρ)
    with rel-store-embedding-source-liftᴿ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb liftρ
rel-store-embedding-source-liftᴿ
    {τ = τ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-store-embedding-link
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p = p} {p′ = p′}
      eqα eqA eqβ eqB shape-emb emb)
    (lift-left-store-link
      {A = A} {B = B} {p′ = pν} shapeν liftρ)
    | ρ′ν , liftρ′ , embν =
  store-link (suc α′) (⇑ᵗ A′) β′ B′
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) hσ eqAν eqB pν) ∷ ρ′ν ,
  lift-left-store-link
    (trans
      (⊑-rename-at-shapeᴿ
        (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) hσ eqAν eqB pν)
      (trans shapeν (sym shape-emb)))
    liftρ′ ,
  rel-store-embedding-link
    (cong suc eqα) eqAν eqβ eqB
    (⊑-rename-at-shapeᴿ
      (rename-assm²-⇑ᴸᵢ assm)
      (TyRenameWf-ext hτ) hσ eqAν eqB pν)
    embν
  where
  eqAν : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqAν =
    trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))


rel-context-embedding-source-liftᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {γν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ} →
  RelCtxRenameⁱ τ σ assm hτ hσ γ γ′ →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γν →
  ∃[ γ′ν ]
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) γ′ γ′ν ×
    RelCtxRenameⁱ
      (extᵗ τ) σ (rename-assm²-⇑ᴸᵢ assm)
      (TyRenameWf-ext hτ) hσ γν γ′ν
rel-context-embedding-source-liftᴿ
    rel-ctx-rename-[] lift-left-ctx-[] =
  [] , lift-left-ctx-[] , rel-ctx-rename-[]
rel-context-embedding-source-liftᴿ
    (rel-ctx-rename-∷ {A′ = A′} {B′ = B′} {p = p}
      eqA eqB renameγ)
    (lift-left-ctx-∷ {p′ = pν} shapeν liftγ)
    with rel-context-embedding-source-liftᴿ renameγ liftγ
rel-context-embedding-source-liftᴿ
    {τ = τ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (rel-ctx-rename-∷ {A′ = A′} {B′ = B′} {p = p}
      eqA eqB renameγ)
    (lift-left-ctx-∷
      {A = A} {B = B} {p′ = pν} shapeν liftγ)
    | γ′ν , liftγ′ , renameγν =
  ctx-imp (⇑ᵗ A′) B′
      (⊑-rename-at²ᵢ (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) hσ eqAν eqB pν) ∷ γ′ν ,
  lift-left-ctx-∷
    (trans
      (⊑-rename-at-shapeᴿ
        (rename-assm²-⇑ᴸᵢ assm)
        (TyRenameWf-ext hτ) hσ eqAν eqB pν)
      (trans shapeν
        (sym (⊑-rename-at-shapeᴿ
          assm hτ hσ eqA eqB p))))
    liftγ′ ,
  rel-ctx-rename-∷ eqAν eqB renameγν
  where
  eqAν : ⇑ᵗ A′ ≡ renameᵗ (extᵗ τ) (⇑ᵗ A)
  eqAν =
    trans (cong ⇑ᵗ eqA) (sym (renameᵗ-ext-suc-comm τ A))


world-embedding-source-liftᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ}
    {γν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ} →
  (emb : ReductionClosedWorldEmbeddingᴿ
    τ σ ψ φ assm hτ hσ
    {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γν →
  ∃[ ρ′ν ] ∃[ γ′ν ]
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) ρ′ ρ′ν ×
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) γ′ γ′ν ×
    ReductionClosedWorldEmbeddingᴿ
      (extᵗ τ) σ (extᵗ ψ) φ
      (rename-assm²-⇑ᴸᵢ assm) (TyRenameWf-ext hτ) hσ
      {ρ = ρν} {ρ′ = ρ′ν} {γ = γν} {γ′ = γ′ν}
world-embedding-source-liftᴿ
    {assm = assm} {hτ = hτ} {hσ = hσ}
    emb liftρ liftγ
    with rel-store-embedding-source-liftᴿ
      {assm = assm} {hτ = hτ} {hσ = hσ}
      (store-embeddingᴿ emb) liftρ
       | rel-context-embedding-source-liftᴿ
          (context-embeddingᴿ emb) liftγ
world-embedding-source-liftᴿ emb liftρ liftγ
    | ρ′ν , liftρ′ , embρν
    | γ′ν , liftγ′ , embγν =
  ρ′ν , γ′ν , liftρ′ , liftγ′ ,
  reduction-closed-world-embeddingᴿ
    (RenameLeftInverse-ext (left-inverseᴿ emb))
    (right-inverseᴿ emb)
    (castModeRenamer-ext (left-cast-renamerᴿ emb))
    (right-cast-renamerᴿ emb)
    embρν embγν


rel-store-embedding-prefix-invᴿ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′⁺ : StoreImp Ψ Θᴸ Θᴿ} →
  StoreImpPrefixᴿ ρ₀ ρ⁺ →
  RelStoreEmbeddingⁱ τ σ ρ⁺ ρ′⁺ →
  ∃[ ρ₀′ ]
    RelStoreEmbeddingⁱ τ σ ρ₀ ρ₀′ ×
    StoreImpPrefixᴿ ρ₀′ ρ′⁺
rel-store-embedding-prefix-invᴿ prefix-reflᴿ emb =
  _ , emb , prefix-reflᴿ
rel-store-embedding-prefix-invᴿ (prefix-∷ᴿ prefix)
    (rel-store-embedding-matched
      eqα eqA eqβ eqB shape-eq emb)
    with rel-store-embedding-prefix-invᴿ prefix emb
rel-store-embedding-prefix-invᴿ (prefix-∷ᴿ prefix)
    (rel-store-embedding-matched
      eqα eqA eqβ eqB shape-eq emb)
    | ρ₀′ , emb₀ , prefix′ =
  ρ₀′ , emb₀ , prefix-∷ᴿ prefix′
rel-store-embedding-prefix-invᴿ (prefix-∷ᴿ prefix)
    (rel-store-embedding-left eqα eqA emb)
    with rel-store-embedding-prefix-invᴿ prefix emb
rel-store-embedding-prefix-invᴿ (prefix-∷ᴿ prefix)
    (rel-store-embedding-left eqα eqA emb)
    | ρ₀′ , emb₀ , prefix′ =
  ρ₀′ , emb₀ , prefix-∷ᴿ prefix′
rel-store-embedding-prefix-invᴿ (prefix-∷ᴿ prefix)
    (rel-store-embedding-right eqβ eqB emb)
    with rel-store-embedding-prefix-invᴿ prefix emb
rel-store-embedding-prefix-invᴿ (prefix-∷ᴿ prefix)
    (rel-store-embedding-right eqβ eqB emb)
    | ρ₀′ , emb₀ , prefix′ =
  ρ₀′ , emb₀ , prefix-∷ᴿ prefix′
rel-store-embedding-prefix-invᴿ (prefix-∷ᴿ prefix)
    (rel-store-embedding-link
      eqα eqA eqβ eqB shape-eq emb)
    with rel-store-embedding-prefix-invᴿ prefix emb
rel-store-embedding-prefix-invᴿ (prefix-∷ᴿ prefix)
    (rel-store-embedding-link
      eqα eqA eqβ eqB shape-eq emb)
    | ρ₀′ , emb₀ , prefix′ =
  ρ₀′ , emb₀ , prefix-∷ᴿ prefix′


paired-lift-creation-worlds-differᴿ :
  ∀ Φ →
  ∀ᵢᶜ (⇑ᴿᵢ Φ) ≡ ⇑ᴿᵢ (∀ᵢᶜ Φ) →
  ⊥
paired-lift-creation-worlds-differᴿ Φ ()
