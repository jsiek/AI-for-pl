module proof.NuImprecisionSourceBulletBase where

-- File Charter:
--   * Isolates the source-only runtime-bullet base lemmas used by the
--     `ν` imprecision simulation.
--   * Exports the polymorphic-value post-allocation step, source
--     polymorphic-value shape, indexed source `α`/`Λ` catch-up, and allocated
--     source bullet relation.
--   * Keeps local administrative embedding and post-allocation helpers private
--     and avoids depending on the main simulation or scratch modules.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; _ˣ⊑★; ⇑ᴸᵢ; ν; ⊑-src-wf)
open import NuReduction using
  ( keep
  ; pure-step
  ; β-Λ•
  ; ↠-refl
  ; ↠-step
  ; _—→[_]_
  )
open import NuTermImprecision using
  ( CtxImp
  ; LiftLeftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; leftStoreⁱ-lift-left
  ; lift-left-ctx-[]
  ; lift-left-store-[]
  ; lift-left-store-∷
  ; lift-left-store-left
  ; lift-left-store-link
  ; lift-left-store-right
  ; rightStoreⁱ
  ; rightStoreⁱ-lift-left
  ; store-left
  ; store-link
  ; store-matched
  ; store-right
  )
open import NuTerms using
  ( No•
  ; Value
  ; no•-$
  ; no•-`
  ; no•-ƛ
  ; no•-·
  ; no•-Λ
  ; no•-ν
  ; no•-⊕
  ; no•-⟨⟩
  ; no•-blame
  ; renameᵗᵐ
  ; Λ_
  ; ⇑ᵗᵐ
  ; _•
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; blame⊑ᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↓⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv⊑convᵀ
  ; down⊑downᵀ
  ; gen-down⊑gen-downᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  ; up⊑upᵀ
  ; x⊑xᵀ
  ; Λ⊑Λᵀ
  ; Λ⊑ᵀ
  ; α⊑αᵀ
  ; α⊑ᵀ
  ; κ⊑κᵀ
  ; νcast⊑νcastᵀ
  ; νcast⊑ᵀ
  ; ν⊑νᵀ
  ; ν⊑ᵀ
  ; ·⊑·ᵀ
  ; ƛ⊑ƛᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↓ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑αᵀ
  ; ⊑νcastᵀ
  ; ⊑νᵀ
  ; ⊕⊑⊕ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Relation.Binary.PropositionalEquality using
  (subst; sym)
open import Store using (StoreIncl-drop)
open import TermTyping using (_∣_∣_⊢_⦂_; ⊢•)
open import Types using
  ( WfTy
  ; `∀
  ; extᵗ
  ; renameᵗ
  ; ⇑ᵗ
  )
open import proof.MaximalLowerBoundsWf using
  (rename-assm²ᵢ; ⊑-renameᵗ²ᵢ)
open import proof.NuImprecisionRelStoreEmbeddingDef using
  ( RelStoreEmbeddingⁱ
  ; rel-store-embedding-[]
  ; rel-store-embedding-left
  ; rel-store-embedding-link
  ; rel-store-embedding-matched
  ; rel-store-embedding-right
  )
open import proof.NuImprecisionSimulationCore using
  ( RelWorldEmbeddingⁱ
  ; castModeRenamer-id
  ; nu-term-imprecision-transport-termsᵀ
  ; nu-term-imprecision-transport-typesᵀ
  ; rel-ctx-rename-[]
  ; rel-world-allocation-prefix-embedᵀ
  ; rel-world-blame-embedᵀ
  ; rel-world-cast⊒⊑-embedᵀ
  ; rel-world-cast⊑⊑-embedᵀ
  ; rel-world-conv↓⊑-embedᵀ
  ; rel-world-conv↑⊑-embedᵀ
  ; rel-world-conv⊑conv-embedᵀ
  ; rel-world-down-embedᵀ
  ; rel-world-embedding
  ; rel-world-embedding-ctx-∷ⁱ
  ; rel-world-gen-down-embedᵀ
  ; rel-world-up⊑up-embedᵀ
  ; rel-world-x-embedᵀ
  ; rel-world-Λ-embedᵀ
  ; rel-world-Λ⊑-embedᵀ
  ; rel-world-ƛ-embedᵀ
  ; rel-world-νcast⊑νcast-embedᵀ
  ; rel-world-νcast⊑-embedᵀ
  ; rel-world-ν⊑ν-embedᵀ
  ; rel-world-ν⊑-embedᵀ
  ; rel-world-⊑cast⊒-embedᵀ
  ; rel-world-⊑cast⊑-embedᵀ
  ; rel-world-⊑cast⊑id-embedᵀ
  ; rel-world-⊑conv↓-embedᵀ
  ; rel-world-⊑conv↑-embedᵀ
  ; rel-world-⊑νcast-embedᵀ
  ; rel-world-⊑ν-embedᵀ
  ; rename-assm²-idᵢ
  ; weak-one-step-index-resultᵀ
  ; ⊑-rename-id-all-bodyᵢ
  ; ⊑-rename-id-allᵢ
  ; ⊑-rename-id-arrowᵢ
  ; ⊑-rename-idᵢ
  ; ⊑ᵖ-rename²ᵢ
  )
open import proof.NuImprecisionSimulationResultDef using
  ( LeftCatchupIndexedResult
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent-invariant
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultSourceType
  ; resultStore
  ; resultTargetType
  ; resultType
  ; sourceCatchup
  ; sourceChanges
  ; sourceCtxResult
  ; sourceResult
  ; sourceStoreResult
  ; sourceTypeResult
  ; targetCtxResult
  ; targetResult
  ; targetStoreResult
  ; targetTail
  ; targetTailChanges
  ; targetTypeResult
  ; transportAllBody
  ; transportRightBody
  ; transportType
  ; weak-step-transport
  ; weak-step-type-coherence
  )
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.NuTermProperties using
  ( open0-ext-suc-cancelᵐ
  ; renameᵗᵐ-id
  ; renameᵗᵐ-preserves-Value
  )
open import proof.TypePreservation using (term-weaken)
open import proof.TypeProperties using
  (TyRenameWf; renameᵗ-id)

private
  identity-store-rel-embeddingⁱ :
    ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ} →
    RelStoreEmbeddingⁱ (λ X → X) (λ X → X) ρ ρ
  identity-store-rel-embeddingⁱ {ρ = []} =
    rel-store-embedding-[]
  identity-store-rel-embeddingⁱ
      {ρ = store-matched α A β B p ∷ ρ} =
    rel-store-embedding-matched refl (sym (renameᵗ-id A))
      refl (sym (renameᵗ-id B)) identity-store-rel-embeddingⁱ
  identity-store-rel-embeddingⁱ
      {ρ = store-left α A hA ∷ ρ} =
    rel-store-embedding-left refl (sym (renameᵗ-id A))
      identity-store-rel-embeddingⁱ
  identity-store-rel-embeddingⁱ
      {ρ = store-right β B hB ∷ ρ} =
    rel-store-embedding-right refl (sym (renameᵗ-id B))
      identity-store-rel-embeddingⁱ
  identity-store-rel-embeddingⁱ
      {ρ = store-link α A β B p ∷ ρ} =
    rel-store-embedding-link refl (sym (renameᵗ-id A))
      refl (sym (renameᵗ-id B)) identity-store-rel-embeddingⁱ

  identity-world-embeddingⁱ :
    ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ} →
    RelWorldEmbeddingⁱ
      (λ X → X) (λ X → X) (λ X → X) (λ X → X)
      rename-assm²-idᵢ (λ X<Δ → X<Δ) (λ X<Δ → X<Δ)
      {ρ = ρ} {ρ′ = ρ} {γ = []} {γ′ = []}
  identity-world-embeddingⁱ =
    rel-world-embedding (λ X → refl) (λ X → refl)
      castModeRenamer-id castModeRenamer-id
      identity-store-rel-embeddingⁱ rel-ctx-rename-[]

  paired-left-lift-rel-embeddingⁱ :
    ∀ {Φ Ψ Δᴸ Δᴿ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᵃ ρᵇ : StoreImp Ψ (suc Δᴸ) Δᴿ} →
    LiftLeftStoreⁱ Ψ ρ ρᵃ →
    LiftLeftStoreⁱ Ψ ρ ρᵇ →
    RelStoreEmbeddingⁱ (λ X → X) (λ X → X) ρᵃ ρᵇ
  paired-left-lift-rel-embeddingⁱ
      lift-left-store-[] lift-left-store-[] =
    rel-store-embedding-[]
  paired-left-lift-rel-embeddingⁱ
      (lift-left-store-∷ liftρᵃ) (lift-left-store-∷ liftρᵇ) =
    rel-store-embedding-matched refl (sym (renameᵗ-id _))
      refl (sym (renameᵗ-id _))
      (paired-left-lift-rel-embeddingⁱ liftρᵃ liftρᵇ)
  paired-left-lift-rel-embeddingⁱ
      (lift-left-store-left liftρᵃ)
      (lift-left-store-left liftρᵇ) =
    rel-store-embedding-left refl (sym (renameᵗ-id _))
      (paired-left-lift-rel-embeddingⁱ liftρᵃ liftρᵇ)
  paired-left-lift-rel-embeddingⁱ
      (lift-left-store-right liftρᵃ)
      (lift-left-store-right liftρᵇ) =
    rel-store-embedding-right refl (sym (renameᵗ-id _))
      (paired-left-lift-rel-embeddingⁱ liftρᵃ liftρᵇ)
  paired-left-lift-rel-embeddingⁱ
      (lift-left-store-link liftρᵃ)
      (lift-left-store-link liftρᵇ) =
    rel-store-embedding-link refl (sym (renameᵗ-id _))
      refl (sym (renameᵗ-id _))
      (paired-left-lift-rel-embeddingⁱ liftρᵃ liftρᵇ)

  paired-left-lift-prefix-world-embeddingⁱ :
    ∀ {Φ Ψ Δᴸ Δᴿ A}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᵃ ρᵇ : StoreImp Ψ (suc Δᴸ) Δᴿ}
      {hA : WfTy (suc Δᴸ) A} →
    LiftLeftStoreⁱ Ψ ρ ρᵃ →
    LiftLeftStoreⁱ Ψ ρ ρᵇ →
    RelWorldEmbeddingⁱ
      (λ X → X) (λ X → X) (λ X → X) (λ X → X)
      rename-assm²-idᵢ (λ X<Δ → X<Δ) (λ X<Δ → X<Δ)
      {ρ = store-left zero A hA ∷ ρᵃ}
      {ρ′ = store-left zero A hA ∷ ρᵇ}
      {γ = []} {γ′ = []}
  paired-left-lift-prefix-world-embeddingⁱ liftρᵃ liftρᵇ =
    rel-world-embedding (λ X → refl) (λ X → refl)
      castModeRenamer-id castModeRenamer-id
      (rel-store-embedding-left refl (sym (renameᵗ-id _))
        (paired-left-lift-rel-embeddingⁱ liftρᵃ liftρᵇ))
      rel-ctx-rename-[]

  mutual
    rel-world-embed-no•ᵀ :
      ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
        {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
        {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
        {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
        {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
        {M M′ A B} {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
        {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
      No• M → No• M′ →
      Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
        ⊢ᴺ renameᵗᵐ τ M ⊑ renameᵗᵐ σ M′
        ⦂ renameᵗ τ A ⊑ renameᵗ σ B
        ∶ ⊑-renameᵗ²ᵢ assm hτ hσ p

    rel-world-embed-no•ᵀᵖ :
      ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ ψ φ}
        {assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
        {hτ : TyRenameWf Δᴸ Θᴸ τ} {hσ : TyRenameWf Δᴿ Θᴿ σ}
        {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
        {γ : CtxImp Φ Δᴸ Δᴿ} {γ′ : CtxImp Ψ Θᴸ Θᴿ}
        {M M′ D D′} {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
      (emb : RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
        {ρ = ρ} {ρ′ = ρ′} {γ = γ} {γ′ = γ′}) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
      No• M → No• M′ →
      Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
        ⊢ᴺᵖ renameᵗᵐ τ M ⊑ renameᵗᵐ σ M′
        ⦂ renameᵗ τ D ⊑ᵖ renameᵗ σ D′
        ∶ ⊑ᵖ-rename²ᵢ assm hτ hσ q

    rel-world-embed-no•ᵀ emb (blame⊑ᵀ M′⊢)
        no•-blame noM′ =
      rel-world-blame-embedᵀ emb noM′ M′⊢
    rel-world-embed-no•ᵀ emb (x⊑xᵀ x∈) no•-` no•-` =
      rel-world-x-embedᵀ emb x∈
    rel-world-embed-no•ᵀ emb (ƛ⊑ƛᵀ hA hA′ N⊑N′)
        (no•-ƛ noN) (no•-ƛ noN′) =
      rel-world-ƛ-embedᵀ emb hA hA′
        (rel-world-embed-no•ᵀ
          (rel-world-embedding-ctx-∷ⁱ emb) N⊑N′ noN noN′)
    rel-world-embed-no•ᵀ emb (·⊑·ᵀ L⊑L′ M⊑M′)
        (no•-· noL noM) (no•-· noL′ noM′) =
      ·⊑·ᵀ
        (rel-world-embed-no•ᵀ emb L⊑L′ noL noL′)
        (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
    rel-world-embed-no•ᵀ emb (up⊑upᵀ N⊑N′ widening pA)
        (no•-⟨⟩ noN) (no•-⟨⟩ noN′) =
      rel-world-up⊑up-embedᵀ emb widening
        (rel-world-embed-no•ᵀᵖ emb N⊑N′ noN noN′)
    rel-world-embed-no•ᵀ emb
        (Λ⊑Λᵀ liftρ liftγ vV vV′ V⊑V′)
        (no•-Λ noV) (no•-Λ noV′)
        with rel-world-Λ-embedᵀ emb liftρ liftγ vV vV′
    rel-world-embed-no•ᵀ emb
        (Λ⊑Λᵀ liftρ liftγ vV vV′ V⊑V′)
        (no•-Λ noV) (no•-Λ noV′)
        | ρ′∀ , γ′∀ , liftρ′ , liftγ′ , body-emb , finish =
      finish (rel-world-embed-no•ᵀ body-emb V⊑V′ noV noV′)
    rel-world-embed-no•ᵀ emb (Λ⊑ᵀ occ liftρ liftγ vV V⊑N′)
        (no•-Λ noV) noN′
        with rel-world-Λ⊑-embedᵀ emb occ liftρ liftγ vV
    rel-world-embed-no•ᵀ emb (Λ⊑ᵀ occ liftρ liftγ vV V⊑N′)
        (no•-Λ noV) noN′
        | ρ′ν , γ′ν , liftρ′ , liftγ′ , body-emb , finish =
      finish (rel-world-embed-no•ᵀ body-emb V⊑N′ noV noN′)
    rel-world-embed-no•ᵀ emb
        (α⊑αᵀ vL noL vL′ noL′ pA liftρ liftγ L⊑L′ L⊢ L′⊢)
        () noM′
    rel-world-embed-no•ᵀ emb
        (α⊑ᵀ vL noL hA liftρ liftγ L⊑N′ L⊢ N′⊢) () noN′
    rel-world-embed-no•ᵀ emb
        (⊑αᵀ vL′ noL′ hA liftρ liftγ N⊑L′ r N⊢ L′⊢) noN ()
    rel-world-embed-no•ᵀ emb
        (allocation-prefixᵀ prefix M⊑M′ M⊢ M′⊢) noM noM′ =
      rel-world-allocation-prefix-embedᵀ emb prefix
        (λ emb₀ → rel-world-embed-no•ᵀ emb₀ M⊑M′ noM noM′)
        noM noM′ M⊢ M′⊢
    rel-world-embed-no•ᵀ emb
        (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
          liftρ liftγ N⊑N′)
        (no•-ν noN) (no•-ν noN′) =
      rel-world-ν⊑ν-embedᵀ emb hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
        liftρ liftγ (rel-world-embed-no•ᵀ emb N⊑N′ noN noN′)
    rel-world-embed-no•ᵀ emb
        (ν⊑ᵀ hA h⇑A s↑ liftρ liftγ N⊑N′)
        (no•-ν noN) noN′ =
      rel-world-ν⊑-embedᵀ emb hA h⇑A s↑ liftρ liftγ
        (rel-world-embed-no•ᵀ emb N⊑N′ noN noN′)
    rel-world-embed-no•ᵀ emb
        (⊑νᵀ hA h⇑A s↑ liftρ liftγ r N⊑N′)
        noN (no•-ν noN′) =
      rel-world-⊑ν-embedᵀ emb hA h⇑A s↑ liftρ liftγ r
        (rel-world-embed-no•ᵀ emb N⊑N′ noN noN′)
    rel-world-embed-no•ᵀ emb
        (νcast⊑νcastᵀ mode seal mode′ seal′ s⊑ s′⊑
          compat liftρ liftγ N⊑N′)
        (no•-ν noN) (no•-ν noN′) =
      rel-world-νcast⊑νcast-embedᵀ emb mode seal mode′ seal′
        s⊑ s′⊑ compat liftρ liftγ
        (rel-world-embed-no•ᵀ emb N⊑N′ noN noN′)
    rel-world-embed-no•ᵀ emb
        (νcast⊑ᵀ mode seal s⊑ liftρ liftγ N⊑N′)
        (no•-ν noN) noN′ =
      rel-world-νcast⊑-embedᵀ emb mode seal s⊑ liftρ liftγ
        (rel-world-embed-no•ᵀ emb N⊑N′ noN noN′)
    rel-world-embed-no•ᵀ emb
        (⊑νcastᵀ mode seal s⊑ liftρ liftγ r N⊑N′)
        noN (no•-ν noN′) =
      rel-world-⊑νcast-embedᵀ emb mode seal s⊑ liftρ liftγ r
        (rel-world-embed-no•ᵀ emb N⊑N′ noN noN′)
    rel-world-embed-no•ᵀ emb κ⊑κᵀ no•-$ no•-$ = κ⊑κᵀ
    rel-world-embed-no•ᵀ emb (⊕⊑⊕ᵀ L⊑L′ M⊑M′)
        (no•-⊕ noL noM) (no•-⊕ noL′ noM′) =
      ⊕⊑⊕ᵀ
        (rel-world-embed-no•ᵀ emb L⊑L′ noL noL′)
        (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
    rel-world-embed-no•ᵀ emb
        (cast⊒⊑ᵀ mode seal c⊒ M⊑M′ q)
        (no•-⟨⟩ noM) noM′ =
      rel-world-cast⊒⊑-embedᵀ emb mode seal c⊒
        (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
    rel-world-embed-no•ᵀ emb
        (cast⊑⊑ᵀ mode seal c⊑ M⊑M′ q)
        (no•-⟨⟩ noM) noM′ =
      rel-world-cast⊑⊑-embedᵀ emb mode seal c⊑
        (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
    rel-world-embed-no•ᵀ emb
        (⊑cast⊒ᵀ mode seal c⊒ M⊑M′ q)
        noM (no•-⟨⟩ noM′) =
      rel-world-⊑cast⊒-embedᵀ emb mode seal c⊒
        (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
    rel-world-embed-no•ᵀ emb
        (⊑cast⊑ᵀ mode seal c⊑ M⊑M′ q)
        noM (no•-⟨⟩ noM′) =
      rel-world-⊑cast⊑-embedᵀ emb mode seal c⊑
        (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
    rel-world-embed-no•ᵀ emb
        (⊑cast⊑idᵀ seal c⊑ M⊑M′ q)
        noM (no•-⟨⟩ noM′) =
      rel-world-⊑cast⊑id-embedᵀ emb c⊑
        (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
    rel-world-embed-no•ᵀ emb
        (conv⊑convᵀ cast M⊑M′)
        (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
      rel-world-conv⊑conv-embedᵀ emb cast
        (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
    rel-world-embed-no•ᵀ emb (conv↑⊑ᵀ conv M⊑M′ q)
        (no•-⟨⟩ noM) noM′ =
      rel-world-conv↑⊑-embedᵀ emb conv
        (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
    rel-world-embed-no•ᵀ emb (conv↓⊑ᵀ conv M⊑M′ q)
        (no•-⟨⟩ noM) noM′ =
      rel-world-conv↓⊑-embedᵀ emb conv
        (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
    rel-world-embed-no•ᵀ emb (⊑conv↑ᵀ conv M⊑M′ q)
        noM (no•-⟨⟩ noM′) =
      rel-world-⊑conv↑-embedᵀ emb conv
        (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
    rel-world-embed-no•ᵀ emb (⊑conv↓ᵀ conv M⊑M′ q)
        noM (no•-⟨⟩ noM′) =
      rel-world-⊑conv↓-embedᵀ emb conv
        (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)

    rel-world-embed-no•ᵀᵖ emb
        (down⊑downᵀ d⊒ d′⊒ M⊑M′ q)
        (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
      rel-world-down-embedᵀ emb d⊒ d′⊒
        (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′) q
    rel-world-embed-no•ᵀᵖ emb
        (gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ q)
        (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
      rel-world-gen-down-embedᵀ emb d⊒ d′⊒
        (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′) q

  identity-bodyᵀ :
    ∀ {Φ Δᴸ Δᴿ A B L L′ p}
      {ρ : StoreImp Φ Δᴸ Δᴿ} →
    No• L →
    No• L′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ L ⊑ L′ ⦂ A ⊑ B ∶ p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ L ⊑ L′ ⦂ A ⊑ B ∶ ⊑-rename-idᵢ p
  identity-bodyᵀ {A = A} {B = B} {L = L} {L′ = L′}
      noL noL′ L⊑L′ =
    nu-term-imprecision-transport-termsᵀ
      (renameᵗᵐ-id L) (renameᵗᵐ-id L′)
      (nu-term-imprecision-transport-typesᵀ
        (renameᵗ-id A) (renameᵗ-id B) refl
        (rel-world-embed-no•ᵀ
          identity-world-embeddingⁱ L⊑L′ noL noL′))

  paired-left-lift-prefix-bodyᵀ :
    ∀ {Φ Ψ Δᴸ Δᴿ A B C L L′ p}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᵃ ρᵇ : StoreImp Ψ (suc Δᴸ) Δᴿ}
      {hC : WfTy (suc Δᴸ) C} →
    LiftLeftStoreⁱ Ψ ρ ρᵃ →
    LiftLeftStoreⁱ Ψ ρ ρᵇ →
    No• L → No• L′ →
    Ψ ∣ suc Δᴸ ∣ Δᴿ ∣
      store-left zero C hC ∷ ρᵇ ∣ []
      ⊢ᴺ L ⊑ L′ ⦂ A ⊑ B ∶ p →
    Ψ ∣ suc Δᴸ ∣ Δᴿ ∣
      store-left zero C hC ∷ ρᵃ ∣ []
      ⊢ᴺ L ⊑ L′ ⦂ A ⊑ B ∶ ⊑-rename-idᵢ p
  paired-left-lift-prefix-bodyᵀ
      {A = A} {B = B} {L = L} {L′ = L′}
      liftρᵃ liftρᵇ noL noL′ L⊑L′ =
    nu-term-imprecision-transport-termsᵀ
      (renameᵗᵐ-id L) (renameᵗᵐ-id L′)
      (nu-term-imprecision-transport-typesᵀ
        (renameᵗ-id A) (renameᵗ-id B) refl
        (rel-world-embed-no•ᵀ
          (paired-left-lift-prefix-world-embeddingⁱ liftρᵇ liftρᵃ)
          L⊑L′ noL noL′))

  post-allocation-β-Λ•-bare :
    ∀ {V} →
    Value V →
    (⇑ᵗᵐ (Λ V)) • —→[ keep ] V
  post-allocation-β-Λ•-bare {V = V} vV =
    subst
      (λ W → (⇑ᵗᵐ (Λ V)) • —→[ keep ] W)
      (open0-ext-suc-cancelᵐ V)
      (pure-step
        (β-Λ• (renameᵗᵐ-preserves-Value (extᵗ suc) vV)))

left-catchup-indexed-prefix-α-Λᵀ :
  ∀ {Φ Δᴸ Δᴿ Aν W V′ A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᵃ ρᵇ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ}
    {ρ⁺ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ} →
  Value W →
  No• W →
  No• V′ →
  (h⇑Aν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  (liftρᵃ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρᵃ) →
  (liftρᵇ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρᵇ) →
  (prefix : StoreImpPrefix
    (store-left zero (⇑ᵗ Aν) h⇑Aν ∷ ρᵃ) ρ⁺) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ W ⊑ V′ ⦂ A ⊑ B ∶ p →
  LeftCatchupIndexedResult
    {N = (⇑ᵗᵐ (Λ W)) •} {V′ = V′} {ρ = ρ⁺} p
left-catchup-indexed-prefix-α-Λᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Aν = Aν} {W = W} {V′ = V′}
    {A = A} {B = B} {p = p} {ρᵃ = ρᵃ} {ρᵇ = ρᵇ} {ρ⁺ = ρ⁺}
    vW noW noV′ h⇑Aν liftρᵃ liftρᵇ prefix W⊑V′ =
  left-indexed-catchup
    (weak-one-step-index-resultᵀ result refl)
    (left-catchup-invariant
      (left-silent-invariant refl refl) (inj₁ (vW , noW)))
    (weak-step-transport identity-bodyᵀ)
    (weak-step-type-coherence
      ⊑-rename-id-arrowᵢ ⊑-rename-id-allᵢ)
  where
  allocated-body =
    allocation-prefixᵀ (prefix-∷ⁱ prefix-reflⁱ) W⊑V′
      (term-weaken {Δ = suc Δᴸ} {Δ′ = suc Δᴸ}
        {Σ = leftStoreⁱ ρᵇ}
        {Σ′ = (zero , ⇑ᵗ Aν) ∷ leftStoreⁱ ρᵇ}
        {Γ = []} ≤-refl StoreIncl-drop noW
        (nu-term-imprecision-source-typing W⊑V′))
      (nu-term-imprecision-target-typing W⊑V′)

  canonical-body =
    paired-left-lift-prefix-bodyᵀ
      liftρᵃ liftρᵇ noW noV′ allocated-body

  prefixed-body =
    allocation-prefixᵀ prefix canonical-body
      (term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
        noW (nu-term-imprecision-source-typing canonical-body))
      (term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
        noV′ (nu-term-imprecision-target-typing canonical-body))

  result =
    record
      { sourceChanges = keep ∷ []
      ; targetTailChanges = []
      ; sourceResult = W
      ; targetResult = V′
      ; resultCtx = (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ
      ; resultLeftCtx = suc Δᴸ
      ; resultRightCtx = _
      ; sourceCtxResult = refl
      ; targetCtxResult = refl
      ; resultStore = ρ⁺
      ; resultSourceType = A
      ; resultTargetType = B
      ; sourceTypeResult = refl
      ; targetTypeResult = refl
      ; transportType = ⊑-rename-idᵢ
      ; transportAllBody = ⊑-rename-id-all-bodyᵢ
      ; transportRightBody = ⊑-rename-idᵢ
      ; resultType = ⊑-rename-idᵢ p
      ; sourceCatchup =
          ↠-step (post-allocation-β-Λ•-bare vW) ↠-refl
      ; targetTail = ↠-refl
      ; sourceStoreResult = refl
      ; targetStoreResult = refl
      ; relatedResults = prefixed-body
      }

left-allocated-bulletᵀ :
  ∀ {Φ Δᴸ Δᴿ Aν A B′ V V′ occ r}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value V →
  No• V →
  (hAν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  (liftρ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ A ⊑ B′ ∶ ν occ r →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣
    store-left zero (⇑ᵗ Aν) hAν ∷ ρ′ ∣ []
    ⊢ᴺ (⇑ᵗᵐ V) • ⊑ V′ ⦂ A ⊑ B′ ∶ r
left-allocated-bulletᵀ
    {Aν = Aν} {V = V} {V′ = V′} {r = r}
    vV noV hAν liftρ V⊑V′ =
  α⊑ᵀ vV noV hAν liftρ lift-left-ctx-[] V⊑V′
    left-bullet-typing right-typing
  where
    left-bullet-typing =
      subst
        (λ Σ → _ ∣ (zero , ⇑ᵗ Aν) ∷ Σ ∣ []
          ⊢ (⇑ᵗᵐ V) • ⦂ _)
        (sym (leftStoreⁱ-lift-left liftρ))
        (⊢• refl refl (⊑-src-wf r) vV noV
          (nu-term-imprecision-source-typing V⊑V′))

    right-typing =
      subst
        (λ Σ → _ ∣ Σ ∣ [] ⊢ V′ ⦂ _)
        (sym (rightStoreⁱ-lift-left liftρ))
        (nu-term-imprecision-target-typing V⊑V′)
