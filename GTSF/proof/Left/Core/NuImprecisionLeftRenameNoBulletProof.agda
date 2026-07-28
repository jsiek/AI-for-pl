module proof.Left.Core.NuImprecisionLeftRenameNoBulletProof where

-- File Charter:
--   * Implements the repaired LeftRenameNoBullet record for ordinary and
--     quotiented Nu-term imprecision.
--   * Recurses structurally through bullet-free QTI derivations and eliminates
--     runtime-bullet constructors by contradiction from No• evidence.
--   * Uses LeftInsertion to derive the cast-mode renamer and allocation typing
--     transport needed by ordinary casts, conversions, and ν-cast cases.
--   * Exposes the completed record without adding carriers, shims, postulates,
--     permissive options, or compatibility aliases.

open import Agda.Builtin.Equality using (refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  )
open import NuTerms using
  ( No•
  ; Term
  ; no•-ƛ
  ; no•-·
  ; no•-Λ
  ; no•-ν
  ; no•-⊕
  ; no•-⟨⟩
  ; renameᵗᵐ
  ; Λ_
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
  )
open import Types using
  ( Renameᵗ
  ; Ty
  ; TyCtx
  ; `∀
  ; extᵗ
  ; renameᵗ
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using (rename-assm²ᵢ)
open import proof.Left.Core.NuImprecisionLeftRenameNoBulletDef using
  (LeftRenameNoBullet)
open import proof.Core.Properties.NuCastModeRenamerProperties using
  ( LeftInsertion
  ; left-insertion-cast-renamer
  ; left-insertion-ext
  ; left-insertion-suc
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( LeftCtxRenameⁱ
  ; LeftStoreRenameⁱ
  ; left-narrowing-renameⁱ
  ; left-store-rename-[]
  ; left-store-rename-left
  ; left-store-rename-link
  ; left-store-rename-matched
  ; left-store-rename-right
  ; left-ctx-rename-∷
  ; left-ctx-rename-[]
  ; left-rename-blameᵀ
  ; left-rename-cast⊒⊑ᵀ
  ; left-rename-cast⊑⊑ᵀ
  ; left-rename-closeᵀ
  ; left-rename-conv↑⊑ᵀ
  ; left-rename-conv↓⊑ᵀ
  ; left-rename-paired-concealᵀ
  ; left-rename-paired-revealᵀ
  ; left-rename-paired-wideningᵀ
  ; left-rename-Λᵀ
  ; left-rename-Λ⊑ᵀ
  ; left-rename-νᵀ
  ; left-rename-ν⊑ᵀ
  ; left-rename-⊑cast⊒ᵀ
  ; left-rename-⊑cast⊑ᵀ
  ; left-rename-⊑conv↑ᵀ
  ; left-rename-⊑conv↓ᵀ
  ; left-rename-·ᵀ
  ; left-rename-ƛᵀ
  ; left-rename-xᵀ
  ; left-rename-allocation-prefixᵀ
  ; left-seal★-renameⁱ
  ; left-typing-renameⁱ
  ; right-typing-left-renameⁱ
  )
open import
  proof.Quotient.NuImprecisionPairedDownRenameLemma
  using (left-rename-paired-downᵀ)
open import proof.Core.Permutation.ForallPermutationProperties using
  (⊑ᵖ-rename-leftᵢ)
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using
  ( cast-shape-rename
  ; imprecision-composition-shape-transport
  ; shape-rename-left
  ; shape-subst-source
  ; ⊑-rename-leftᵢ
  )
open import proof.Core.Properties.NuTermProperties using
  ( renameᵗᵐ-compose
  ; renameᵗᵐ-preserves-Closedᵐ
  ; renameᵗᵐ-preserves-No•
  ; renameᵗᵐ-preserves-Value
  )
open import proof.Core.Properties.TypePreservation using (CastModeRenamer)
open import proof.Core.Properties.TypeProperties using
  ( RenameLeftInverse
  ; RenameLeftInverse-ext
  ; RenameLeftInverse-suc
  ; TyRenameWf
  ; TyRenameWf-ext
  ; predᵗ
  ; renameᵗ-compose
  ; renameᵗ-id
  )
open import
  proof.Store.RelEmbedding.NuImprecisionRelCtxRenameAlgebra
  using (compose-rel-assm²ᵢ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-composeⁱ)
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
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using (embed-creation-leftᴱ)
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using
  ( embedded-creation-source-typingᴱ
  ; embedded-creation-target-typingᴱ
  )

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


private
  left-store-rename-embeddingⁱ :
    ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ}
      {assm : ∀ {a} → a ∈ Φ →
        rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
      {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ} →
    LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
    RelStoreEmbeddingⁱ τ (λ X → X) ρ ρ′
  left-store-rename-embeddingⁱ left-store-rename-[] =
    rel-store-embedding-[]
  left-store-rename-embeddingⁱ {assm = assm} {hτ = hτ}
      (left-store-rename-matched {B = B} {p = p}
        eqα eqA renameρ) =
    rel-store-embedding-matched
      eqα eqA refl (sym (renameᵗ-id B))
      (trans
        (shape-subst-source
          (sym eqA) (⊑-rename-leftᵢ _ assm hτ p))
        (shape-rename-left assm hτ p))
      (left-store-rename-embeddingⁱ renameρ)
  left-store-rename-embeddingⁱ
      (left-store-rename-left eqα eqA renameρ) =
    rel-store-embedding-left eqα eqA
      (left-store-rename-embeddingⁱ renameρ)
  left-store-rename-embeddingⁱ
      (left-store-rename-right {B = B} renameρ) =
    rel-store-embedding-right
      refl (sym (renameᵗ-id B))
      (left-store-rename-embeddingⁱ renameρ)
  left-store-rename-embeddingⁱ {assm = assm} {hτ = hτ}
      (left-store-rename-link {B = B} {p = p}
        eqα eqA renameρ) =
    rel-store-embedding-link
      eqα eqA refl (sym (renameᵗ-id B))
      (trans
        (shape-subst-source
          (sym eqA) (⊑-rename-leftᵢ _ assm hτ p))
        (shape-rename-left assm hτ p))
      (left-store-rename-embeddingⁱ renameρ)


mutual
  left-rename-no•ᵀ-proof :
    ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴸ′ Δᴿ : TyCtx} {τ : Renameᵗ}
      {assm : ∀ {a} → a ∈ Φ →
        rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
      {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
      {M M′ : Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    LeftInsertion τ →
    LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
    LeftCtxRenameⁱ τ assm hτ γ γ′ →
    No• M →
    No• M′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
      ⊢ᴺ renameᵗᵐ τ M ⊑ M′
      ⦂ renameᵗ τ A ⊑ B
      ∶ ⊑-rename-leftᵢ τ assm hτ p

  left-rename-no•ᵀᵖ-proof :
    ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴸ′ Δᴿ : TyCtx} {τ : Renameᵗ}
      {assm : ∀ {a} → a ∈ Φ →
        rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
      {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
      {M M′ : Term} {D D′ : Ty}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
    LeftInsertion τ →
    LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
    LeftCtxRenameⁱ τ assm hτ γ γ′ →
    No• M →
    No• M′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
    Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
      ⊢ᴺᵖ renameᵗᵐ τ M ⊑ M′
      ⦂ renameᵗ τ D ⊑ᵖ D′
      ∶ ⊑ᵖ-rename-leftᵢ τ assm hτ q

  left-rename-no•ᵀ-proof ins renameρ renameγ noM noM′
      (blame⊑ᵀ M′⊢) =
    left-rename-blameᵀ renameρ renameγ M′⊢
  left-rename-no•ᵀ-proof ins renameρ renameγ noM noM′
      (x⊑xᵀ x∈) =
    left-rename-xᵀ renameγ x∈
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-ƛ noN) (no•-ƛ noN′) (ƛ⊑ƛᵀ hA hA′ N⊑N′) =
    left-rename-ƛᵀ hA hA′
      (left-rename-no•ᵀ-proof ins renameρ
        (left-ctx-rename-∷ refl renameγ) noN noN′ N⊑N′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-· noL noM) (no•-· noL′ noM′)
      (·⊑·ᵀ L⊑L′ M⊑M′) =
    left-rename-·ᵀ
      (left-rename-no•ᵀ-proof ins renameρ renameγ noL noL′ L⊑L′)
      (left-rename-no•ᵀ-proof ins renameρ renameγ noM noM′ M⊑M′)
  left-rename-no•ᵀ-proof {τ = τ} {assm = assm} {hτ = hτ}
      ins renameρ renameγ (no•-⟨⟩ noN) (no•-⟨⟩ noN′)
      (closeᵀ N⊑N′ widening pA
        u-shape u′-shape square compatible) =
    left-rename-closeᵀ
      (left-insertion-cast-renamer ins) renameρ widening
      u-shape u′-shape square compatible
      (left-rename-no•ᵀᵖ-proof ins renameρ renameγ
        noN noN′ N⊑N′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-Λ noV) (no•-Λ noV′)
      (Λ⊑Λᵀ liftρ liftγ vV vV′ V⊑V′) =
    left-rename-Λᵀ renameρ renameγ liftρ liftγ vV vV′
      (λ liftρ′ liftγ′ renameρ∀ renameγ∀ →
        left-rename-no•ᵀ-proof (left-insertion-ext ins)
          renameρ∀ renameγ∀ noV noV′ V⊑V′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-Λ noV) noN′
      (Λ⊑ᵀ occ liftρ liftγ vV V⊑N′) =
    left-rename-Λ⊑ᵀ renameρ renameγ occ liftρ liftγ vV
      (λ liftρ′ liftγ′ renameρν renameγν →
        left-rename-no•ᵀ-proof (left-insertion-ext ins)
          renameρν renameγν noV noN′ V⊑N′)
  left-rename-no•ᵀ-proof
      {τ = τ} {assm = assm} {hτ = hτ}
      ins renameρ renameγ noM noM′
      (target-instantiationᵀ embedded) =
    target-instantiationᵀ
      (embed-creation-leftᴱ embedded assm hτ
        (left-store-rename-embeddingⁱ renameρ)
        source-typing target-typing)
    where
    source-typing =
      (left-typing-renameⁱ {ψ = left-insertion-pred ins}
        (left-insertion-inverse ins)
        (left-insertion-cast-renamer ins)
        renameρ left-ctx-rename-[] noM
        (embedded-creation-source-typingᴱ embedded))

    target-typing =
      right-typing-left-renameⁱ renameρ left-ctx-rename-[]
        (embedded-creation-target-typingᴱ embedded)
  left-rename-no•ᵀ-proof ins renameρ renameγ ()
      noM′ (α⊑αᵀ vL noL vL′ noL′ A⇑⊑B⇑ liftρ liftγ
        L⊑L′ L•⊢ L′•⊢)
  left-rename-no•ᵀ-proof ins renameρ renameγ ()
      noM′ (α⊑ᵀ vL noL h⇑A liftρ liftγ L⊑N′ L•⊢ N′⊢)
  left-rename-no•ᵀ-proof ins renameρ renameγ noM noM′
      (allocation-prefixᵀ prefix M⊑M′ M⊢ M′⊢) =
    left-rename-allocation-prefixᵀ prefix renameρ
      (λ renameρ₀ →
        left-rename-no•ᵀ-proof ins renameρ₀ renameγ
          noM noM′ M⊑M′)
      source-typing target-typing
    where
    source-typing =
      left-typing-renameⁱ {ψ = left-insertion-pred ins}
        (left-insertion-inverse ins)
        (left-insertion-cast-renamer ins) renameρ renameγ noM M⊢

    target-typing =
      right-typing-left-renameⁱ renameρ renameγ M′⊢
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-ν noN) (no•-ν noN′)
      (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
        liftρ liftγ N⊑N′ replace) =
    left-rename-νᵀ ins renameρ renameγ hA hA′ s↑ s′↑
      A⊑A′ A⇑⊑A′⇑ liftρ liftγ
      replace
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noN noN′ N⊑N′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-ν noN) noN′
      (ν⊑ᵀ hA h⇑A s↑ liftρ liftγ N⊑N′ replace) =
    left-rename-ν⊑ᵀ ins renameρ renameγ hA h⇑A s↑
      liftρ liftγ replace
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noN noN′ N⊑N′)
  left-rename-no•ᵀ-proof ins renameρ renameγ noM noM′ κ⊑κᵀ =
    κ⊑κᵀ
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-⊕ noL noM) (no•-⊕ noL′ noM′)
      (⊕⊑⊕ᵀ L⊑L′ M⊑M′) =
    ⊕⊑⊕ᵀ
      (left-rename-no•ᵀ-proof ins renameρ renameγ noL noL′ L⊑L′)
      (left-rename-no•ᵀ-proof ins renameρ renameγ noM noM′ M⊑M′)
  left-rename-no•ᵀ-proof {assm = assm} {hτ = hτ}
      ins renameρ renameγ (no•-⟨⟩ noV) noW
      (gen⊑groundᵀ mode seal★ c⊒ gH vV vW W⊢ V⊑Wtag q) =
    gen⊑groundᵀ
      (CastModeRenamer.target-mode modeτ mode)
      (left-seal★-renameⁱ modeτ renameρ mode seal★)
      (left-narrowing-renameⁱ modeτ mode renameρ c⊒)
      gH
      (renameᵗᵐ-preserves-Value _ vV)
      vW
      (right-typing-left-renameⁱ renameρ renameγ W⊢)
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noV (no•-⟨⟩ noW) V⊑Wtag)
      _
    where
    modeτ = left-insertion-cast-renamer ins
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-⟨⟩ noM) noM′
      (cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ q c-shape comp) =
    left-rename-cast⊒⊑ᵀ
      (left-insertion-cast-renamer ins) renameρ mode seal★ c⊒
      c-shape comp
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-⟨⟩ noM) noM′
      (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q c-shape comp) =
    left-rename-cast⊑⊑ᵀ
      (left-insertion-cast-renamer ins) renameρ mode seal★ c⊑
      c-shape comp
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      noM (no•-⟨⟩ noM′)
      (⊑cast⊒ᵀ mode′ seal★′ c′⊒ M⊑M′ q c′-shape comp) =
    left-rename-⊑cast⊒ᵀ renameρ mode′ seal★′ c′⊒
      c′-shape comp
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      noM (no•-⟨⟩ noM′)
      (⊑cast⊑ᵀ mode′ seal★′ c′⊑ M⊑M′ q c′-shape comp) =
    left-rename-⊑cast⊑ᵀ renameρ mode′ seal★′ c′⊑
      c′-shape comp
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (paired-revealᵀ corr conv conv′ replace M⊑M′) =
    left-rename-paired-revealᵀ ins renameρ corr conv conv′ replace
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (paired-concealᵀ corr conv conv′ replace M⊑M′) =
    left-rename-paired-concealᵀ ins renameρ corr conv conv′ replace
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (paired-wideningᵀ
        mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
        left-square right-square compatible M⊑M′) =
    left-rename-paired-wideningᵀ ins renameρ
      mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
      left-square right-square compatible
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-⟨⟩ noM) noM′
      (conv↑⊑ᵀ c↑ M⊑M′ q replacement) =
    left-rename-conv↑⊑ᵀ ins renameρ c↑
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
      replacement
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-⟨⟩ noM) noM′
      (conv↓⊑ᵀ c↓ M⊑M′ q replacement) =
    left-rename-conv↓⊑ᵀ ins renameρ c↓
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
      replacement
  left-rename-no•ᵀ-proof ins renameρ renameγ
      noM (no•-⟨⟩ noM′)
      (⊑conv↑ᵀ c′↑ M⊑M′ q replacement) =
    left-rename-⊑conv↑ᵀ renameρ c′↑
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
      replacement
  left-rename-no•ᵀ-proof ins renameρ renameγ
      noM (no•-⟨⟩ noM′)
      (⊑conv↓ᵀ c′↓ M⊑M′ q replacement) =
    left-rename-⊑conv↓ᵀ renameρ c′↓
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
      replacement

  left-rename-no•ᵀᵖ-proof
      ins renameρ renameγ
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (paired-downᵀ M⊑M′
        mode d⊒ d-shape mode′ d′⊒ d′-shape
        square compatible) =
    left-rename-paired-downᵀ
      (left-insertion-cast-renamer ins) renameρ
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
      mode d⊒ d-shape mode′ d′⊒ d′-shape
      square compatible

left-rename-no-bullet : LeftRenameNoBullet
left-rename-no-bullet =
  record
    { left-rename-no•ᵀ = left-rename-no•ᵀ-proof
    ; left-rename-no•ᵀᵖ = left-rename-no•ᵀᵖ-proof
    }
