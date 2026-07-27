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
  ; conv↓⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv⊑convᵀ
  ; down·up⊑down·upᵀ
  ; down⊑downᵀ
  ; gen⊑groundᵀ
  ; gen-down⊑gen-downᵀ
  ; quotient-down-applicationᵖᵀ
  ; quotient-id-down-applicationᵖᵀ
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
  ; rel-world-conv↓⊑-embedᵀ
  ; rel-world-conv↑⊑-embedᵀ
  ; rel-world-conv⊑conv-embedᵀ
  ; rel-world-down-embedᵀ
  ; rel-world-embedding
  ; rel-world-embedding-ctx-∷ⁱ
  ; rel-world-source-typing-embed
  ; rel-world-target-typing-embed
  ; left-embedding-cast-renamer
  ; left-narrowing-rel-embed-mode
  ; left-seal-rel-embed
  ; paired-widening-compatible-rename²ᵢ
  ; rel-world-quotient-widening-pair-embed
  ; rel-world-gen-down-embedᵀ
  ; rel-world-gen⊑ground-embedᵀ
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
  ; right-embedding-cast-renamer
  ; right-embedding-inverse
  ; right-narrowing-rel-embed-mode
  ; right-seal-rel-embed
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
  rel-world-embed-no•ᵀ
      {τ = τ} {σ = σ} {assm = assm}
      {hτ = hτ} {hσ = hσ} emb
      (down·up⊑down·upᵀ
        mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
        L⊑L′ M⊑M′ down-square widening
        u-shape u′-shape up-square compatible)
      (no•-⟨⟩ (no•-· noL (no•-⟨⟩ noM)))
      (no•-⟨⟩ (no•-· noL′ (no•-⟨⟩ noM′))) =
    down·up⊑down·upᵀ
      (CastModeRenamer.target-mode
        (left-embedding-cast-renamer emb) mode)
      (left-seal-rel-embed emb mode seal★)
      (left-narrowing-rel-embed-mode emb
        (CastModeRenamer.target-rename
          (left-embedding-cast-renamer emb) mode) d⊒)
      (cast-shape-rename τ d-shape)
      (CastModeRenamer.target-mode
        (right-embedding-cast-renamer emb) mode′)
      (right-seal-rel-embed emb mode′ seal★′)
      (right-narrowing-rel-embed-mode emb
        (CastModeRenamer.target-rename
          (right-embedding-cast-renamer emb) mode′) d′⊒)
      (cast-shape-rename σ d′-shape)
      (rel-world-embed-no•ᵀ emb L⊑L′ noL noL′)
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
      (quotient-boundary-square-rename² down-square)
      (rel-world-quotient-widening-pair-embed emb widening)
      (cast-shape-rename τ u-shape)
      (cast-shape-rename σ u′-shape)
      (quotient-boundary-square-rename² up-square)
      (paired-widening-compatible-rename²ᵢ hτ hσ compatible)
  rel-world-embed-no•ᵀ emb
      (up⊑upᵀ N⊑N′ widening pA u-shape u′-shape square)
      (no•-⟨⟩ noN) (no•-⟨⟩ noN′) =
    rel-world-up⊑up-embedᵀ
      emb widening u-shape u′-shape square
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
      (⊑αᵀ vL′ noL′ hA liftρ liftγ N⊑L′ r N⊢ L′⊢) noN ()
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
  rel-world-embed-no•ᵀ emb
      (⊑νᵀ hA h⇑A s↑ liftρ liftγ r N⊑N′ replace)
      noN (no•-ν noN′) =
    rel-world-⊑ν-embedᵀ emb hA h⇑A s↑ liftρ liftγ r replace
      (rel-world-embed-no•ᵀ emb N⊑N′ noN noN′)
  rel-world-embed-no•ᵀ emb
      (νcast⊑νcastᵀ mode seal mode′ seal′ s⊑ s′⊑
        compat liftρ liftγ N⊑N′ s-shape s′-shape
        left-comp right-comp)
      (no•-ν noN) (no•-ν noN′) =
    rel-world-νcast⊑νcast-embedᵀ emb mode seal mode′ seal′
      s⊑ s-shape s′⊑ s′-shape compat left-comp right-comp
      liftρ liftγ
      (rel-world-embed-no•ᵀ emb N⊑N′ noN noN′)
  rel-world-embed-no•ᵀ emb
      (νcast⊑ᵀ mode seal s⊑ liftρ liftγ N⊑N′ s-shape comp)
      (no•-ν noN) noN′ =
    rel-world-νcast⊑-embedᵀ emb mode seal s⊑ s-shape comp
      liftρ liftγ
      (rel-world-embed-no•ᵀ emb N⊑N′ noN noN′)
  rel-world-embed-no•ᵀ emb
      (⊑νcastᵀ mode seal s⊑ liftρ liftγ r N⊑N′ s-shape comp)
      noN (no•-ν noN′) =
    rel-world-⊑νcast-embedᵀ emb mode seal s⊑ s-shape
      liftρ liftγ r comp
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
  rel-world-embed-no•ᵀ emb
      (⊑cast⊑idᵀ seal c⊑ M⊑M′ q c-shape comp)
      noM (no•-⟨⟩ noM′) =
    rel-world-⊑cast⊑id-embedᵀ emb c⊑ c-shape comp
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
  rel-world-embed-no•ᵀ emb
      (conv⊑convᵀ cast M⊑M′)
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
    rel-world-conv⊑conv-embedᵀ emb cast
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
      (down⊑downᵀ
        d⊒ d-shape d′⊒ d′-shape M⊑M′ q square)
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
    rel-world-down-embedᵀ
      emb d⊒ d-shape d′⊒ d′-shape
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′) q square
  rel-world-embed-no•ᵀᵖ emb
      (gen-down⊑gen-downᵀ
        d⊒ d-shape d′⊒ d′-shape M⊑M′ q square)
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
    rel-world-gen-down-embedᵀ
      emb d⊒ d-shape d′⊒ d′-shape
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′) q square
  rel-world-embed-no•ᵀᵖ {τ = τ} {σ = σ} emb
      (quotient-id-down-applicationᵖᵀ {qF = qF}
        d⊒ d-shape d′⊒ d′-shape
        L⊑L′ components M⊑M′ square)
      (no•-· noL (no•-⟨⟩ noM))
      (no•-· noL′ (no•-⟨⟩ noM′)) =
    quotient-id-down-applicationᵖᵀ
      (left-narrowing-rel-embed-mode emb
        (modeRename-id-only τ) d⊒)
      (cast-shape-rename τ d-shape)
      (right-narrowing-rel-embed-mode emb
        (modeRename-id-only σ) d′⊒)
      (cast-shape-rename σ d′-shape)
      (rel-world-embed-no•ᵀᵖ emb L⊑L′ noL noL′)
      (quotient-arrow-components-rename²-at
        {qF = qF} components)
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
      (quotient-boundary-square-rename² square)
  rel-world-embed-no•ᵀᵖ {τ = τ} {σ = σ} emb
      (quotient-down-applicationᵖᵀ {qF = qF}
        mode seal★ d⊒ d-shape
        mode′ seal★′ d′⊒ d′-shape
        L⊑L′ components M⊑M′ square)
      (no•-· noL (no•-⟨⟩ noM))
      (no•-· noL′ (no•-⟨⟩ noM′)) =
    quotient-down-applicationᵖᵀ
      (CastModeRenamer.target-mode
        (left-embedding-cast-renamer emb) mode)
      (left-seal-rel-embed emb mode seal★)
      (left-narrowing-rel-embed-mode emb
        (CastModeRenamer.target-rename
          (left-embedding-cast-renamer emb) mode) d⊒)
      (cast-shape-rename τ d-shape)
      (CastModeRenamer.target-mode
        (right-embedding-cast-renamer emb) mode′)
      (right-seal-rel-embed emb mode′ seal★′)
      (right-narrowing-rel-embed-mode emb
        (CastModeRenamer.target-rename
          (right-embedding-cast-renamer emb) mode′) d′⊒)
      (cast-shape-rename σ d′-shape)
      (rel-world-embed-no•ᵀᵖ emb L⊑L′ noL noL′)
      (quotient-arrow-components-rename²-at
        {qF = qF} components)
      (rel-world-embed-no•ᵀ emb M⊑M′ noM noM′)
      (quotient-boundary-square-rename² square)
