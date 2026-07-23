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
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using (CtxImp; StoreImp)
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
  )
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  ; blame⊑ᵀ
  ; x⊑xᵀ
  ; ƛ⊑ƛᵀ
  ; ·⊑·ᵀ
  ; up⊑upᵀ
  ; Λ⊑Λᵀ
  ; Λ⊑ᵀ
  ; α⊑αᵀ
  ; α⊑ᵀ
  ; ⊑αᵀ
  ; allocation-prefixᵀ
  ; ν⊑νᵀ
  ; ν⊑ᵀ
  ; ⊑νᵀ
  ; νcast⊑νcastᵀ
  ; νcast⊑ᵀ
  ; ⊑νcastᵀ
  ; κ⊑κᵀ
  ; ⊕⊑⊕ᵀ
  ; gen⊑groundᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑cast⊑idᵀ
  ; conv⊑convᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; down⊑downᵀ
  ; gen-down⊑gen-downᵀ
  ; ordinary-down-applicationᵖᵀ
  ; quotient-down-applicationᵖᵀ
  ; quotient-id-down-applicationᵖᵀ
  ; quotient-id-widening
  ; quotient-cast-widening
  )
open import Types using (Renameᵗ; Ty; TyCtx; extᵗ; renameᵗ)
open import proof.Core.Properties.CoercionProperties using (modeRename-id-only)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using (rename-assm²ᵢ)
open import proof.Left.Core.NuImprecisionLeftRenameNoBulletDef using
  (LeftRenameNoBullet)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( LeftInsertion
  ; LeftCtxRenameⁱ
  ; LeftStoreRenameⁱ
  ; left-insertion-suc
  ; left-insertion-ext
  ; left-insertion-cast-renamer
  ; left-narrowing-renameⁱ
  ; left-narrowing-rename-modeⁱ
  ; left-ctx-rename-∷
  ; left-rename-blameᵀ
  ; left-rename-cast⊒⊑ᵀ
  ; left-rename-cast⊑⊑ᵀ
  ; left-rename-conv⊑convᵀ
  ; left-rename-conv↑⊑ᵀ
  ; left-rename-conv↓⊑ᵀ
  ; left-rename-down⊑downᵀ
  ; left-rename-gen-down⊑gen-downᵀ
  ; left-rename-Λᵀ
  ; left-rename-Λ⊑ᵀ
  ; left-rename-νᵀ
  ; left-rename-ν⊑ᵀ
  ; left-rename-νcastᵀ
  ; left-rename-νcast⊑ᵀ
  ; left-rename-⊑cast⊒ᵀ
  ; left-rename-⊑cast⊑ᵀ
  ; left-rename-⊑cast⊑idᵀ
  ; left-rename-⊑conv↑ᵀ
  ; left-rename-⊑conv↓ᵀ
  ; left-rename-⊑νᵀ
  ; left-rename-⊑νcastᵀ
  ; left-rename-·ᵀ
  ; left-rename-ƛᵀ
  ; left-rename-xᵀ
  ; left-rename-allocation-prefixᵀ
  ; left-seal★-renameⁱ
  ; left-typing-renameⁱ
  ; left-widening-renameⁱ
  ; left-widening-rename-modeⁱ
  ; right-seal★-left-renameⁱ
  ; right-narrowing-left-renameⁱ
  ; right-typing-left-renameⁱ
  ; right-widening-left-renameⁱ
  ; ⊑-rename-leftᵢ
  ; ⊑ᵖ-rename-leftᵢ
  )
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-Value)
open import proof.Core.Properties.TypePreservation using (CastModeRenamer)
open import proof.Core.Properties.TypeProperties using
  ( RenameLeftInverse
  ; RenameLeftInverse-ext
  ; RenameLeftInverse-suc
  ; TyRenameWf
  ; TyRenameWf-ext
  ; predᵗ
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
      (up⊑upᵀ N⊑N′ (quotient-id-widening u⊑ u′⊑) pA) =
    up⊑upᵀ
      (left-rename-no•ᵀᵖ-proof ins renameρ renameγ
        noN noN′ N⊑N′)
      (quotient-id-widening
        (left-widening-rename-modeⁱ
          (modeRename-id-only τ) renameρ u⊑)
        (right-widening-left-renameⁱ renameρ u′⊑))
      (⊑-rename-leftᵢ τ assm hτ pA)
  left-rename-no•ᵀ-proof {τ = τ} {assm = assm} {hτ = hτ}
      ins renameρ renameγ (no•-⟨⟩ noN) (no•-⟨⟩ noN′)
      (up⊑upᵀ N⊑N′
        (quotient-cast-widening mode seal★ u⊑ mode′ seal★′ u′⊑)
        pA) =
    up⊑upᵀ
      (left-rename-no•ᵀᵖ-proof ins renameρ renameγ
        noN noN′ N⊑N′)
      (quotient-cast-widening
        (CastModeRenamer.target-mode modeτ mode)
        (left-seal★-renameⁱ modeτ renameρ mode seal★)
        (left-widening-renameⁱ modeτ mode renameρ u⊑)
        mode′
        (right-seal★-left-renameⁱ renameρ seal★′)
        (right-widening-left-renameⁱ renameρ u′⊑))
      (⊑-rename-leftᵢ τ assm hτ pA)
    where
    modeτ = left-insertion-cast-renamer ins
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
  left-rename-no•ᵀ-proof ins renameρ renameγ ()
      noM′ (α⊑αᵀ vL noL vL′ noL′ A⇑⊑B⇑ liftρ liftγ
        L⊑L′ L•⊢ L′•⊢)
  left-rename-no•ᵀ-proof ins renameρ renameγ ()
      noM′ (α⊑ᵀ vL noL h⇑A liftρ liftγ L⊑N′ L•⊢ N′⊢)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      noM () (⊑αᵀ vL′ noL′ h⇑A liftρ liftγ N⊑L′ r
        N⊢ L′•⊢)
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
        liftρ liftγ N⊑N′) =
    left-rename-νᵀ ins renameρ renameγ hA hA′ s↑ s′↑
      A⊑A′ A⇑⊑A′⇑ liftρ liftγ
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noN noN′ N⊑N′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-ν noN) noN′
      (ν⊑ᵀ hA h⇑A s↑ liftρ liftγ N⊑N′) =
    left-rename-ν⊑ᵀ ins renameρ renameγ hA h⇑A s↑
      liftρ liftγ
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noN noN′ N⊑N′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      noN (no•-ν noN′)
      (⊑νᵀ hA h⇑A s↑ liftρ liftγ B⊑C′ N⊑N′) =
    left-rename-⊑νᵀ renameρ renameγ hA h⇑A s↑
      liftρ liftγ B⊑C′
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noN noN′ N⊑N′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-ν noN) (no•-ν noN′)
      (νcast⊑νcastᵀ mode seal★ mode′ seal★′ s⊑ s′⊑
        compat liftρ liftγ N⊑N′) =
    left-rename-νcastᵀ ins renameρ renameγ mode seal★
      mode′ seal★′ s⊑ s′⊑ compat liftρ liftγ
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noN noN′ N⊑N′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-ν noN) noN′
      (νcast⊑ᵀ mode seal★ s⊑ liftρ liftγ N⊑N′) =
    left-rename-νcast⊑ᵀ ins renameρ renameγ mode seal★
      s⊑ liftρ liftγ
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noN noN′ N⊑N′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      noN (no•-ν noN′)
      (⊑νcastᵀ mode seal★ s⊑ liftρ liftγ B⊑C′ N⊑N′) =
    left-rename-⊑νcastᵀ renameρ renameγ mode seal★
      s⊑ liftρ liftγ B⊑C′
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
      (cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ q) =
    left-rename-cast⊒⊑ᵀ
      (left-insertion-cast-renamer ins) renameρ mode seal★ c⊒
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-⟨⟩ noM) noM′
      (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q) =
    left-rename-cast⊑⊑ᵀ
      (left-insertion-cast-renamer ins) renameρ mode seal★ c⊑
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      noM (no•-⟨⟩ noM′)
      (⊑cast⊒ᵀ mode′ seal★′ c′⊒ M⊑M′ q) =
    left-rename-⊑cast⊒ᵀ renameρ mode′ seal★′ c′⊒
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      noM (no•-⟨⟩ noM′)
      (⊑cast⊑ᵀ mode′ seal★′ c′⊑ M⊑M′ q) =
    left-rename-⊑cast⊑ᵀ renameρ mode′ seal★′ c′⊑
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      noM (no•-⟨⟩ noM′)
      (⊑cast⊑idᵀ seal★′ c′⊑ M⊑M′ q) =
    left-rename-⊑cast⊑idᵀ renameρ seal★′ c′⊑
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (conv⊑convᵀ cast M⊑M′) =
    left-rename-conv⊑convᵀ ins renameρ cast
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-⟨⟩ noM) noM′ (conv↑⊑ᵀ c↑ M⊑M′ q) =
    left-rename-conv↑⊑ᵀ ins renameρ c↑
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      (no•-⟨⟩ noM) noM′ (conv↓⊑ᵀ c↓ M⊑M′ q) =
    left-rename-conv↓⊑ᵀ ins renameρ c↓
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      noM (no•-⟨⟩ noM′) (⊑conv↑ᵀ c′↑ M⊑M′ q) =
    left-rename-⊑conv↑ᵀ renameρ c′↑
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀ-proof ins renameρ renameγ
      noM (no•-⟨⟩ noM′) (⊑conv↓ᵀ c′↓ M⊑M′ q) =
    left-rename-⊑conv↓ᵀ renameρ c′↓
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)

  left-rename-no•ᵀᵖ-proof {τ = τ} ins renameρ renameγ
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (down⊑downᵀ d⊒ d′⊒ M⊑M′ q) =
    left-rename-down⊑downᵀ renameρ d⊒ d′⊒
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀᵖ-proof ins renameρ renameγ
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ q) =
    left-rename-gen-down⊑gen-downᵀ renameρ d⊒ d′⊒
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀᵖ-proof ins renameρ renameγ
      (no•-· noL (no•-⟨⟩ noM))
      (no•-· noL′ (no•-⟨⟩ noM′))
      (ordinary-down-applicationᵖᵀ
        mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′) =
    ordinary-down-applicationᵖᵀ
      (CastModeRenamer.target-mode modeτ mode)
      (left-seal★-renameⁱ modeτ renameρ mode seal★)
      (left-narrowing-renameⁱ modeτ mode renameρ d⊒)
      mode′
      (right-seal★-left-renameⁱ renameρ seal★′)
      (right-narrowing-left-renameⁱ renameρ d′⊒)
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noL noL′ L⊑L′)
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
    where
    modeτ = left-insertion-cast-renamer ins
  left-rename-no•ᵀᵖ-proof {τ = τ} ins renameρ renameγ
      (no•-· noL (no•-⟨⟩ noM))
      (no•-· noL′ (no•-⟨⟩ noM′))
      (quotient-id-down-applicationᵖᵀ
        d⊒ d′⊒ L⊑L′ M⊑M′) =
    quotient-id-down-applicationᵖᵀ
      (left-narrowing-rename-modeⁱ
        (modeRename-id-only τ) renameρ d⊒)
      (right-narrowing-left-renameⁱ renameρ d′⊒)
      (left-rename-no•ᵀᵖ-proof ins renameρ renameγ
        noL noL′ L⊑L′)
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
  left-rename-no•ᵀᵖ-proof ins renameρ renameγ
      (no•-· noL (no•-⟨⟩ noM))
      (no•-· noL′ (no•-⟨⟩ noM′))
      (quotient-down-applicationᵖᵀ
        mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′) =
    quotient-down-applicationᵖᵀ
      (CastModeRenamer.target-mode modeτ mode)
      (left-seal★-renameⁱ modeτ renameρ mode seal★)
      (left-narrowing-renameⁱ modeτ mode renameρ d⊒)
      mode′
      (right-seal★-left-renameⁱ renameρ seal★′)
      (right-narrowing-left-renameⁱ renameρ d′⊒)
      (left-rename-no•ᵀᵖ-proof ins renameρ renameγ
        noL noL′ L⊑L′)
      (left-rename-no•ᵀ-proof ins renameρ renameγ
        noM noM′ M⊑M′)
    where
    modeτ = left-insertion-cast-renamer ins

left-rename-no-bullet : LeftRenameNoBullet
left-rename-no-bullet =
  record
    { left-rename-no•ᵀ = left-rename-no•ᵀ-proof
    ; left-rename-no•ᵀᵖ = left-rename-no•ᵀᵖ-proof
    }
