module proof.NuImprecisionLeftLiftPrefixBodyProof where

-- File Charter:
--   * Proves the canonical strict `LeftLiftPrefixBodyᵀ` contract.
--   * Reconstructs the source-left lift proof from low-level world-embedding
--     support without importing the broad simulation or source-bullet modules.
--   * Keeps the generic no-runtime-bullet embedding traversal local until the
--     shared extraction is reconciled.
--   * Contains only total proof terms, with no permissive options or dispatcher
--     logic.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; _ˣ⊑★; ⇑ᴸᵢ)
open import NuTermImprecision using
  ( CtxImp
  ; LiftLeftStoreⁱ
  ; StoreImp
  ; lift-left-store-[]
  ; lift-left-store-∷
  ; lift-left-store-left
  ; lift-left-store-link
  ; lift-left-store-right
  ; store-left
  ; store-link
  ; store-matched
  ; store-right
  )
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
  ; ⇑ᵗᵐ
  )
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
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
open import Relation.Binary.PropositionalEquality using (sym)
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using
  ( WfTy
  ; renameᵗ
  ; ⇑ᵗ
  )
open import proof.MaximalLowerBoundsWf using
  ( rename-assm²-source-νᵢ
  ; rename-assm²ᵢ
  ; ⊑-renameᵗ²ᵢ
  ; ⊑-source-liftνᵢ
  )
open import proof.NuImprecisionLeftLiftPrefixBodyDef using
  (LeftLiftPrefixBodyᵀ)
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
  ; ⊑ᵖ-rename²ᵢ
  )
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.NuTermProperties using
  (renameᵗᵐ-id; renameᵗᵐ-preserves-No•)
open import proof.TypePreservation using (castModeRenamer-suc; term-weaken)
open import proof.TypeProperties using
  ( RenameLeftInverse-suc
  ; TyRenameWf
  ; TyRenameWf-suc
  ; predᵗ
  ; renameᵗ-id
  )


private
  lift-left-store-rel-embeddingⁱ :
    ∀ {Φ Δᴸ Δᴿ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
    RelStoreEmbeddingⁱ suc (λ X → X) ρ ρ′
  lift-left-store-rel-embeddingⁱ lift-left-store-[] =
    rel-store-embedding-[]
  lift-left-store-rel-embeddingⁱ (lift-left-store-∷ liftρ) =
    rel-store-embedding-matched refl refl refl
      (sym (renameᵗ-id _)) (lift-left-store-rel-embeddingⁱ liftρ)
  lift-left-store-rel-embeddingⁱ (lift-left-store-left liftρ) =
    rel-store-embedding-left refl refl
      (lift-left-store-rel-embeddingⁱ liftρ)
  lift-left-store-rel-embeddingⁱ (lift-left-store-right liftρ) =
    rel-store-embedding-right refl (sym (renameᵗ-id _))
      (lift-left-store-rel-embeddingⁱ liftρ)
  lift-left-store-rel-embeddingⁱ (lift-left-store-link liftρ) =
    rel-store-embedding-link refl refl refl
      (sym (renameᵗ-id _)) (lift-left-store-rel-embeddingⁱ liftρ)

  left-lift-world-embeddingⁱ :
    ∀ {Φ Δᴸ Δᴿ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
    RelWorldEmbeddingⁱ suc (λ X → X) predᵗ (λ X → X)
      rename-assm²-source-νᵢ TyRenameWf-suc (λ X<Δ → X<Δ)
      {ρ = ρ} {ρ′ = ρ′} {γ = []} {γ′ = []}
  left-lift-world-embeddingⁱ liftρ =
    rel-world-embedding RenameLeftInverse-suc (λ X → refl)
      castModeRenamer-suc castModeRenamer-id
      (lift-left-store-rel-embeddingⁱ liftρ) rel-ctx-rename-[]

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


left-lift-prefix-body-proofᵀ : LeftLiftPrefixBodyᵀ
left-lift-prefix-body-proofᵀ {B = B} {L′ = L′}
    liftρ prefix noL noL′ L⊑L′ =
  allocation-prefixᵀ prefix body
    (term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
      noL↑ (nu-term-imprecision-source-typing body))
    (term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
      noL′ (nu-term-imprecision-target-typing body))
  where
  body =
    nu-term-imprecision-transport-termsᵀ refl (renameᵗᵐ-id L′)
      (nu-term-imprecision-transport-typesᵀ
        refl (renameᵗ-id B) refl
        (rel-world-embed-no•ᵀ
          (left-lift-world-embeddingⁱ liftρ) L⊑L′ noL noL′))
  noL↑ = renameᵗᵐ-preserves-No• suc noL
