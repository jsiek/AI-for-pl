module proof.NuCore.Misc.NuImprecisionWorldEmbeddingNoBullet where

-- File Charter:
--   * Owns the generic no-runtime-bullet transport theorems through relational
--     world embeddings.
--   * Exports the `rel-world-embed-no•ᵀ` mutual theorem family as its
--     canonical owner.
--   * Depends on `NuImprecisionSimulationCore` for world-embedding action
--     lemmas and on `QuotientedTermImprecision` for the term relations.

open import Data.List using ([])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (cong; refl; sym; trans)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuTermImprecision using (CtxImp; StoreImp)
open import NuTerms using
  ( No•
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
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; blame⊑ᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; closeᵀ
  ; conv↓⊑ᵀ
  ; conv↑⊑ᵀ
  ; gen⊑groundᵀ
  ; paired-concealᵀ
  ; paired-downᵀ
  ; paired-revealᵀ
  ; paired-wideningᵀ
  ; x⊑xᵀ
  ; Λ⊑Λᵀ
  ; Λ⊑ᵀ
  ; α⊑αᵀ
  ; α⊑ᵀ
  ; κ⊑κᵀ
  ; ν⊑νᵀ
  ; ν⊑ᵀ
  ; ·⊑·ᵀ
  ; ƛ⊑ƛᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↓ᵀ
  ; ⊑conv↑ᵀ
  ; ⊕⊑⊕ᵀ
  ; target-instantiationᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (`∀; renameᵗ; ⇑ᵗ)
open import proof.Core.Properties.CoercionProperties using (modeRename-id-only)
open import proof.Core.Properties.NuTermProperties using
  ( renameᵗᵐ-compose
  ; renameᵗᵐ-preserves-Closedᵐ
  ; renameᵗᵐ-preserves-No•
  ; renameᵗᵐ-preserves-Value
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (rename-assm²ᵢ; ⊑-renameᵗ²ᵢ)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( RelWorldEmbeddingⁱ
  ; embedding-context
  ; left-embedding-inverse
  ; rel-world-allocation-prefix-embedᵀ
  ; rel-world-blame-embedᵀ
  ; rel-world-cast⊒⊑-embedᵀ
  ; rel-world-cast⊑⊑-embedᵀ
  ; rel-world-close-embedᵀ
  ; rel-world-conv↓⊑-embedᵀ
  ; rel-world-conv↑⊑-embedᵀ
  ; rel-world-embedding
  ; rel-world-embedding-ctx-∷ⁱ
  ; rel-world-paired-down-embedᵀ
  ; rel-world-source-typing-embed
  ; rel-world-target-typing-embed
  ; left-conceal-rel-embed
  ; left-embedding-cast-renamer
  ; left-narrowing-rel-embed-mode
  ; left-reveal-rel-embed
  ; left-seal-rel-embed
  ; left-widening-rel-embed-mode
  ; rel-world-quotient-widening-pair-embed
  ; rel-world-gen⊑ground-embedᵀ
  ; rel-world-x-embedᵀ
  ; rel-world-Λ-embedᵀ
  ; rel-world-Λ⊑-embedᵀ
  ; rel-world-ƛ-embedᵀ
  ; rel-world-ν⊑ν-embedᵀ
  ; rel-world-ν⊑-embedᵀ
  ; rel-world-⊑cast⊒-embedᵀ
  ; rel-world-⊑cast⊑-embedᵀ
  ; rel-world-⊑conv↓-embedᵀ
  ; rel-world-⊑conv↑-embedᵀ
  ; right-conceal-rel-embed
  ; right-embedding-cast-renamer
  ; right-embedding-inverse
  ; right-narrowing-rel-embed-mode
  ; right-reveal-rel-embed
  ; right-seal-rel-embed
  ; right-widening-rel-embed-mode
  ; store-embedding
  )
open import proof.Core.Permutation.ForallPermutationProperties using
  (⊑ᵖ-rename²ᵢ)
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using
  ( cast-shape-rename
  ; imprecision-composition-shape-transport
  ; shape-rename
  )
open import
  proof.Core.Properties.ConversionIndexCompatibilityProperties
  using
  ( replace-paired-evidence-shape
  ; replace-paired-rename²ᵢ
  )
open import
  proof.Core.Properties.NuImprecisionQuotientBoundaryProperties
  using
  ( quotient-arrow-components-rename²-at
  ; quotient-boundary-square-rename²
  )
open import proof.Core.Properties.TypeProperties using
  (TyRenameWf; renameᵗ-compose)
open import proof.Core.Properties.TypePreservation using (CastModeRenamer)
open import
  proof.Store.RelEmbedding.NuImprecisionRelCtxRenameAlgebra
  using (compose-rel-assm²ᵢ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-composeⁱ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingProof
  using (rel-store-embedding-correspondenceⁱ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelCtxRenameDef
  using (rel-ctx-rename-[])
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
  proof.Quotient.NuImprecisionQuotientCompatibilityRename
  using (reduction-closed-paired-compatible-rename²ᵢ)

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
  rel-world-embed-no•ᵀ emb
      (closeᵀ N⊑N′ widening pA
        u-shape u′-shape square compatible)
      (no•-⟨⟩ noN) (no•-⟨⟩ noN′) =
    rel-world-close-embedᵀ
      emb widening u-shape u′-shape square compatible
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
  rel-world-embed-no•ᵀ
      {τ = τ} {σ = σ} {ψ = ψ} {φ = φ}
      {assm = assm} {hτ = hτ} {hσ = hσ}
      {ρ = ρ} {ρ′ = ρ′} emb
      (target-instantiationᵀ embedded) noM noM′ =
    target-instantiationᵀ
      (embed-creationᴱ embedded assm hτ hσ
        (store-embedding emb)
        (rel-world-source-typing-embed empty-emb noM
          (embedded-creation-source-typingᴱ embedded))
        (rel-world-target-typing-embed empty-emb noM′
          (embedded-creation-target-typingᴱ embedded)))
    where
    empty-emb :
      RelWorldEmbeddingⁱ τ σ ψ φ assm hτ hσ
        {ρ = ρ} {ρ′ = ρ′} {γ = []} {γ′ = []}
    empty-emb =
      rel-world-embedding
        {τ = τ} {σ = σ} {ψ = ψ} {φ = φ}
        (left-embedding-inverse emb)
        (right-embedding-inverse emb)
        (left-embedding-cast-renamer emb)
        (right-embedding-cast-renamer emb)
        (store-embedding emb)
        rel-ctx-rename-[]
  rel-world-embed-no•ᵀ emb
      (α⊑αᵀ vL noL vL′ noL′ pA liftρ liftγ L⊑L′ L⊢ L′⊢)
      () noM′
  rel-world-embed-no•ᵀ emb
      (α⊑ᵀ vL noL hA liftρ liftγ L⊑N′ L⊢ N′⊢) () noN′
  rel-world-embed-no•ᵀ emb
      (allocation-prefixᵀ prefix M⊑M′ M⊢ M′⊢) noM noM′ =
    rel-world-allocation-prefix-embedᵀ emb prefix
      (λ emb₀ → rel-world-embed-no•ᵀ emb₀ M⊑M′ noM noM′)
      noM noM′ M⊢ M′⊢
  rel-world-embed-no•ᵀ emb
      (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
        liftρ liftγ N⊑N′ replace)
      (no•-ν noN) (no•-ν noN′) =
    rel-world-ν⊑ν-embedᵀ emb hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
      liftρ liftγ replace
      (rel-world-embed-no•ᵀ emb N⊑N′ noN noN′)
  rel-world-embed-no•ᵀ emb
      (ν⊑ᵀ hA h⇑A s↑ liftρ liftγ N⊑N′ replace)
      (no•-ν noN) noN′ =
    rel-world-ν⊑-embedᵀ emb hA h⇑A s↑ liftρ liftγ replace
      (rel-world-embed-no•ᵀ emb N⊑N′ noN noN′)
  rel-world-embed-no•ᵀ emb κ⊑κᵀ no•-$ no•-$ = κ⊑κᵀ
  rel-world-embed-no•ᵀ emb (⊕⊑⊕ᵀ L⊑L′ M⊑M′)
      (no•-⊕ noL noM) (no•-⊕ noL′ noM′) =
    ⊕⊑⊕ᵀ
      (rel-world-embed-no•ᵀ emb L⊑L′ noL noL′)
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
  rel-world-embed-no•ᵀ emb
      (gen⊑groundᵀ mode seal★ c⊒ gH vV vW W⊢ V⊑Wtag q)
      (no•-⟨⟩ noV) noW =
    rel-world-gen⊑ground-embedᵀ emb mode seal★ c⊒ gH vV vW noW W⊢
      (rel-world-embed-no•ᵀ emb V⊑Wtag noV (no•-⟨⟩ noW))
  rel-world-embed-no•ᵀ emb
      (cast⊒⊑ᵀ mode seal c⊒ M⊑M′ q c-shape comp)
      (no•-⟨⟩ noM) noM′ =
    rel-world-cast⊒⊑-embedᵀ emb mode seal c⊒
      c-shape comp
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
  rel-world-embed-no•ᵀ emb
      (cast⊑⊑ᵀ mode seal c⊑ M⊑M′ q c-shape comp)
      (no•-⟨⟩ noM) noM′ =
    rel-world-cast⊑⊑-embedᵀ emb mode seal c⊑ c-shape comp
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
  rel-world-embed-no•ᵀ emb
      (⊑cast⊒ᵀ mode seal c⊒ M⊑M′ q c-shape comp)
      noM (no•-⟨⟩ noM′) =
    rel-world-⊑cast⊒-embedᵀ emb mode seal c⊒
      c-shape comp
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
  rel-world-embed-no•ᵀ emb
      (⊑cast⊑ᵀ mode seal c⊑ M⊑M′ q c-shape comp)
      noM (no•-⟨⟩ noM′) =
    rel-world-⊑cast⊑-embedᵀ emb mode seal c⊑
      c-shape comp
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
  rel-world-embed-no•ᵀ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb
      (paired-revealᵀ {pX = pX}
        corr conv conv′ replace M⊑M′)
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      with rel-store-embedding-correspondenceⁱ
        (store-embedding emb) corr
  rel-world-embed-no•ᵀ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb
      (paired-revealᵀ {pX = pX}
        corr conv conv′ replace M⊑M′)
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      | α′ , X , β′ , X′ , p′ ,
        refl , refl , refl , refl , shape-eq , corr′ =
    paired-revealᵀ corr′
      (left-reveal-rel-embed emb conv)
      (right-reveal-rel-embed emb conv′)
      (replace-paired-evidence-shape
        (trans shape-eq (sym (shape-rename assm hτ hσ pX)))
        (replace-paired-rename²ᵢ assm hτ hσ replace))
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
  rel-world-embed-no•ᵀ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb
      (paired-concealᵀ {pX = pX}
        corr conv conv′ replace M⊑M′)
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      with rel-store-embedding-correspondenceⁱ
        (store-embedding emb) corr
  rel-world-embed-no•ᵀ
      {assm = assm} {hτ = hτ} {hσ = hσ} emb
      (paired-concealᵀ {pX = pX}
        corr conv conv′ replace M⊑M′)
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      | α′ , X , β′ , X′ , p′ ,
        refl , refl , refl , refl , shape-eq , corr′ =
    paired-concealᵀ corr′
      (left-conceal-rel-embed emb conv)
      (right-conceal-rel-embed emb conv′)
      (replace-paired-evidence-shape
        (trans shape-eq (sym (shape-rename assm hτ hσ pX)))
        (replace-paired-rename²ᵢ assm hτ hσ replace))
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
  rel-world-embed-no•ᵀ
      {τ = τ} {σ = σ} {assm = assm}
      {hτ = hτ} {hσ = hσ} emb
      (paired-wideningᵀ
        mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
        left-square right-square compatible M⊑M′)
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
    paired-wideningᵀ
      (CastModeRenamer.target-mode
        (left-embedding-cast-renamer emb) mode)
      (left-seal-rel-embed emb mode seal★)
      (left-widening-rel-embed-mode emb
        (CastModeRenamer.target-rename
          (left-embedding-cast-renamer emb) mode) c⊑)
      (cast-shape-rename τ c-shape)
      (CastModeRenamer.target-mode
        (right-embedding-cast-renamer emb) mode′)
      (right-seal-rel-embed emb mode′ seal★′)
      (right-widening-rel-embed-mode emb
        (CastModeRenamer.target-rename
          (right-embedding-cast-renamer emb) mode′) c′⊑)
      (cast-shape-rename σ c′-shape)
      (imprecision-composition-shape-transport
        refl (shape-rename assm hτ hσ _)
        refl left-square)
      (imprecision-composition-shape-transport
        (shape-rename assm hτ hσ _)
        refl refl right-square)
      (reduction-closed-paired-compatible-rename²ᵢ
        {assm = assm} hτ hσ compatible)
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
  rel-world-embed-no•ᵀ emb
      (conv↑⊑ᵀ conv M⊑M′ q replacement)
      (no•-⟨⟩ noM) noM′ =
    rel-world-conv↑⊑-embedᵀ emb conv
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′) replacement
  rel-world-embed-no•ᵀ emb
      (conv↓⊑ᵀ conv M⊑M′ q replacement)
      (no•-⟨⟩ noM) noM′ =
    rel-world-conv↓⊑-embedᵀ emb conv
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′) replacement
  rel-world-embed-no•ᵀ emb
      (⊑conv↑ᵀ conv M⊑M′ q replacement)
      noM (no•-⟨⟩ noM′) =
    rel-world-⊑conv↑-embedᵀ emb conv
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′) replacement
  rel-world-embed-no•ᵀ emb
      (⊑conv↓ᵀ conv M⊑M′ q replacement)
      noM (no•-⟨⟩ noM′) =
    rel-world-⊑conv↓-embedᵀ emb conv
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′) replacement

  rel-world-embed-no•ᵀᵖ emb
      (paired-downᵀ
        M⊑M′ mode d⊒ d-shape mode′ d′⊒ d′-shape square)
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
    rel-world-paired-down-embedᵀ emb
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
      mode d⊒ d-shape mode′ d′⊒ d′-shape square
