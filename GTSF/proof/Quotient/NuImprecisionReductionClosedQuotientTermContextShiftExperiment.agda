module
  proof.Quotient.NuImprecisionReductionClosedQuotientTermContextShiftExperiment
  where

-- File Charter:
--   * Proves mutual no-bullet term-context insertion for the independent
--     smaller ordinary and one-boundary quotient-imprecision relations.
--   * Keeps a fresh variable at the correct depth beneath ordinary lambdas
--     and transports insertion beneath paired and source-only type binders.
--   * Recontextualizes the closed target-instantiation residuals directly.
--   * Imports neither the live term-imprecision relation nor any conversion
--     from it.
--   * Contains no postulate, hole, permissive option, termination bypass, or
--     catch-all clause.

open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import Imprecision using
  (ImpCtx; _ˣ⊑★; _ˣ⊑ˣ_; ⇑ᴸᵢ; ⇑ᵢ)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftCtxⁱ
  ; ctx-imp
  ; leftCtxⁱ
  ; lift-ctx-∷
  ; lift-left-ctx-∷
  ; rightCtxⁱ
  )
open import NuTerms using
  ( No•
  ; Renameˣ
  ; Term
  ; extʳ
  ; no•-$
  ; no•-ƛ
  ; no•-Λ
  ; no•-·
  ; no•-ν
  ; no•-⊕
  ; no•-`
  ; no•-⟨⟩
  ; no•-blame
  ; renameˣᵐ
  )
open import TermTyping using (forget)
open import Types using
  (Ty; TyCtx; S; Z; _∋_⦂_; ⇑ᵗ)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (shape-lift∀ᵢ; shape-source-liftνᵢ)
open import proof.Core.Properties.NuTermProperties using
  ( RenameWf
  ; rename-closedᵐ
  ; renameˣᵐ-preserves-Value
  ; typing-closedᵐ
  )
open import proof.Core.Properties.TypePreservation using
  (typing-renameˣ)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (⊑-lift∀ᵢ; ⊑-source-liftνᵢ)
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using
  ( embedded-creation-source-typingᴱ
  ; embedded-creation-target-typingᴱ
  )


private
  data TermCtxInsertᴿ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      (C C′ : Ty) (q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ) :
      CtxImp Φ Δᴸ Δᴿ →
      CtxImp Φ Δᴸ Δᴿ → Renameˣ → Set₁ where
    insert-hereᴿ : ∀ {γ} →
      TermCtxInsertᴿ C C′ q γ (ctx-imp C C′ q ∷ γ) suc

    insert-underᴿ : ∀ {γ δ η A B p} →
      TermCtxInsertᴿ C C′ q γ δ η →
      TermCtxInsertᴿ C C′ q
        (ctx-imp A B p ∷ γ) (ctx-imp A B p ∷ δ) (extʳ η)


  term-ctx-insert-lookupᴿ :
    ∀ {Φ Δᴸ Δᴿ C C′ q γ δ η x A B p} →
    TermCtxInsertᴿ {Φ} {Δᴸ} {Δᴿ} C C′ q γ δ η →
    γ ∋ x ⦂ ctx-imp A B p →
    δ ∋ η x ⦂ ctx-imp A B p
  term-ctx-insert-lookupᴿ insert-hereᴿ x∈ = S x∈
  term-ctx-insert-lookupᴿ (insert-underᴿ insert) Z = Z
  term-ctx-insert-lookupᴿ (insert-underᴿ insert) (S x∈) =
    S (term-ctx-insert-lookupᴿ insert x∈)


  term-ctx-insert-left-wfᴿ :
    ∀ {Φ Δᴸ Δᴿ C C′ q γ δ η} →
    TermCtxInsertᴿ {Φ} {Δᴸ} {Δᴿ} C C′ q γ δ η →
    RenameWf (leftCtxⁱ γ) (leftCtxⁱ δ) η
  term-ctx-insert-left-wfᴿ insert-hereᴿ x∈ = S x∈
  term-ctx-insert-left-wfᴿ (insert-underᴿ insert) Z = Z
  term-ctx-insert-left-wfᴿ (insert-underᴿ insert) (S x∈) =
    S (term-ctx-insert-left-wfᴿ insert x∈)


  term-ctx-insert-right-wfᴿ :
    ∀ {Φ Δᴸ Δᴿ C C′ q γ δ η} →
    TermCtxInsertᴿ {Φ} {Δᴸ} {Δᴿ} C C′ q γ δ η →
    RenameWf (rightCtxⁱ γ) (rightCtxⁱ δ) η
  term-ctx-insert-right-wfᴿ insert-hereᴿ x∈ = S x∈
  term-ctx-insert-right-wfᴿ (insert-underᴿ insert) Z = Z
  term-ctx-insert-right-wfᴿ (insert-underᴿ insert) (S x∈) =
    S (term-ctx-insert-right-wfᴿ insert x∈)


  term-ctx-insert-paired-liftᴿ :
    ∀ {Φ Δᴸ Δᴿ C C′ q γ δ η γ↑} →
    (insert : TermCtxInsertᴿ {Φ} {Δᴸ} {Δᴿ}
      C C′ q γ δ η) →
    LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ↑ →
    ∃[ δ↑ ]
      LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) δ δ↑ ×
      TermCtxInsertᴿ (⇑ᵗ C) (⇑ᵗ C′) (⊑-lift∀ᵢ q)
        γ↑ δ↑ η
  term-ctx-insert-paired-liftᴿ {q = q} insert-hereᴿ liftγ =
    _ ,
    lift-ctx-∷ {p′ = ⊑-lift∀ᵢ q}
      (shape-lift∀ᵢ q) liftγ ,
    insert-hereᴿ
  term-ctx-insert-paired-liftᴿ
      (insert-underᴿ insert)
      (lift-ctx-∷ {p′ = p↑} shape-eq liftγ)
      with term-ctx-insert-paired-liftᴿ insert liftγ
  term-ctx-insert-paired-liftᴿ
      (insert-underᴿ insert)
      (lift-ctx-∷ {p′ = p↑} shape-eq liftγ)
      | δ↑ , liftδ , insert↑ =
    _ , lift-ctx-∷ {p′ = p↑} shape-eq liftδ ,
    insert-underᴿ insert↑


  term-ctx-insert-left-liftᴿ :
    ∀ {Φ Δᴸ Δᴿ C C′ q γ δ η γ↑} →
    (insert : TermCtxInsertᴿ {Φ} {Δᴸ} {Δᴿ}
      C C′ q γ δ η) →
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ↑ →
    ∃[ δ↑ ]
      LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) δ δ↑ ×
      TermCtxInsertᴿ (⇑ᵗ C) C′ (⊑-source-liftνᵢ q)
        γ↑ δ↑ η
  term-ctx-insert-left-liftᴿ {q = q} insert-hereᴿ liftγ =
    _ ,
    lift-left-ctx-∷ {p′ = ⊑-source-liftνᵢ q}
      (shape-source-liftνᵢ q) liftγ ,
    insert-hereᴿ
  term-ctx-insert-left-liftᴿ
      (insert-underᴿ insert)
      (lift-left-ctx-∷ {p′ = p↑} shape-eq liftγ)
      with term-ctx-insert-left-liftᴿ insert liftγ
  term-ctx-insert-left-liftᴿ
      (insert-underᴿ insert)
      (lift-left-ctx-∷ {p′ = p↑} shape-eq liftγ)
      | δ↑ , liftδ , insert↑ =
    _ , lift-left-ctx-∷ {p′ = p↑} shape-eq liftδ ,
    insert-underᴿ insert↑


  mutual
    term-ctx-insertᴿ :
      ∀ {Φ Δᴸ Δᴿ ρ γ δ η C C′ q M M′ A B p} →
      (insert : TermCtxInsertᴿ {Φ} {Δᴸ} {Δᴿ}
        C C′ q γ δ η) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p →
      No• M → No• M′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
        ⊢ᴿ renameˣᵐ η M ⊑ renameˣᵐ η M′
        ⦂ A ⊑ B ∶ p

    quotient-term-ctx-insertᴿ :
      ∀ {Φ Δᴸ Δᴿ ρ γ δ η C C′ q M M′ D D′ pD} →
      (insert : TermCtxInsertᴿ {Φ} {Δᴸ} {Δᴿ}
        C C′ q γ δ η) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ pD →
      No• M → No• M′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
        ⊢ᴿᵖ renameˣᵐ η M ⊑ renameˣᵐ η M′
        ⦂ D ⊑ᵖ D′ ∶ pD

    term-ctx-insertᴿ insert (blame⊑ᴿ M′⊢)
        no•-blame noM′ =
      blame⊑ᴿ
        (typing-renameˣ (term-ctx-insert-right-wfᴿ insert) M′⊢)
    term-ctx-insertᴿ insert (x⊑xᴿ x∈) no•-` no•-` =
      x⊑xᴿ (term-ctx-insert-lookupᴿ insert x∈)
    term-ctx-insertᴿ insert (ƛ⊑ƛᴿ hA hA′ body)
        (no•-ƛ noN) (no•-ƛ noN′) =
      ƛ⊑ƛᴿ hA hA′
        (term-ctx-insertᴿ
          (insert-underᴿ insert) body noN noN′)
    term-ctx-insertᴿ insert (fun ·ᴿ arg)
        (no•-· noL noM) (no•-· noL′ noM′) =
      term-ctx-insertᴿ insert fun noL noL′
      ·ᴿ
      term-ctx-insertᴿ insert arg noM noM′
    term-ctx-insertᴿ insert
        (Λ⊑Λᴿ liftρ liftγ vV vV′ body)
        (no•-Λ noV) (no•-Λ noV′)
        with term-ctx-insert-paired-liftᴿ insert liftγ
    term-ctx-insertᴿ insert
        (Λ⊑Λᴿ liftρ liftγ vV vV′ body)
        (no•-Λ noV) (no•-Λ noV′)
        | δ↑ , liftδ , insert↑ =
      Λ⊑Λᴿ liftρ liftδ
        (renameˣᵐ-preserves-Value _ vV)
        (renameˣᵐ-preserves-Value _ vV′)
        (term-ctx-insertᴿ insert↑ body noV noV′)
    term-ctx-insertᴿ insert
        (Λ⊑ᴿ occ liftρ liftγ vV body)
        (no•-Λ noV) noN′
        with term-ctx-insert-left-liftᴿ insert liftγ
    term-ctx-insertᴿ insert
        (Λ⊑ᴿ occ liftρ liftγ vV body)
        (no•-Λ noV) noN′
        | δ↑ , liftδ , insert↑ =
      Λ⊑ᴿ occ liftρ liftδ
        (renameˣᵐ-preserves-Value _ vV)
        (term-ctx-insertᴿ insert↑ body noV noN′)
    term-ctx-insertᴿ insert
        (α⊑αᴿ vL noL vL′ noL′ p liftρ liftγ
          body L⊢ L′⊢) () noM′
    term-ctx-insertᴿ insert
        (α⊑ᴿ vL noL hA liftρ liftγ body L⊢ N′⊢)
        () noN′
    term-ctx-insertᴿ insert
        (allocation-prefixᴿ prefix body M⊢ M′⊢) noM noM′ =
      allocation-prefixᴿ prefix
        (term-ctx-insertᴿ insert body noM noM′)
        (typing-renameˣ (term-ctx-insert-left-wfᴿ insert) M⊢)
        (typing-renameˣ (term-ctx-insert-right-wfᴿ insert) M′⊢)
    term-ctx-insertᴿ insert
        (ν⊑νᴿ hA hA′ s↑ s′↑ A⊑A′ A↑⊑A′↑
          liftρ liftγ body replace)
        (no•-ν noN) (no•-ν noN′)
        with term-ctx-insert-paired-liftᴿ insert liftγ
    term-ctx-insertᴿ insert
        (ν⊑νᴿ hA hA′ s↑ s′↑ A⊑A′ A↑⊑A′↑
          liftρ liftγ body replace)
        (no•-ν noN) (no•-ν noN′)
        | δ↑ , liftδ , insert↑ =
      ν⊑νᴿ hA hA′ s↑ s′↑ A⊑A′ A↑⊑A′↑ liftρ liftδ
        (term-ctx-insertᴿ insert body noN noN′) replace
    term-ctx-insertᴿ insert
        (ν⊑ᴿ hA hA↑ s↑ liftρ liftγ body replace)
        (no•-ν noN) noN′
        with term-ctx-insert-left-liftᴿ insert liftγ
    term-ctx-insertᴿ insert
        (ν⊑ᴿ hA hA↑ s↑ liftρ liftγ body replace)
        (no•-ν noN) noN′
        | δ↑ , liftδ , insert↑ =
      ν⊑ᴿ hA hA↑ s↑ liftρ liftδ
        (term-ctx-insertᴿ insert body noN noN′) replace
    term-ctx-insertᴿ insert κ⊑κᴿ no•-$ no•-$ =
      κ⊑κᴿ
    term-ctx-insertᴿ insert (left ⊕ᴿ[ op ] right)
        (no•-⊕ noL noM) (no•-⊕ noL′ noM′) =
      term-ctx-insertᴿ insert left noL noL′
      ⊕ᴿ[ op ]
      term-ctx-insertᴿ insert right noM noM′
    term-ctx-insertᴿ insert
        (gen⊑groundᴿ
          mode seal c⊒ ground vV vW W⊢ body q)
        (no•-⟨⟩ noV) noW =
      gen⊑groundᴿ mode seal c⊒ ground
        (renameˣᵐ-preserves-Value _ vV)
        (renameˣᵐ-preserves-Value _ vW)
        (typing-renameˣ
          (term-ctx-insert-right-wfᴿ insert) W⊢)
        (term-ctx-insertᴿ
          insert body noV (no•-⟨⟩ noW)) q
    term-ctx-insertᴿ insert
        (cast⊒⊑ᴿ mode seal c⊒ body q shape comp)
        (no•-⟨⟩ noM) noM′ =
      cast⊒⊑ᴿ mode seal c⊒
        (term-ctx-insertᴿ insert body noM noM′)
        q shape comp
    term-ctx-insertᴿ insert
        (cast⊑⊑ᴿ mode seal c⊑ body q shape comp)
        (no•-⟨⟩ noM) noM′ =
      cast⊑⊑ᴿ mode seal c⊑
        (term-ctx-insertᴿ insert body noM noM′)
        q shape comp
    term-ctx-insertᴿ insert
        (⊑cast⊒ᴿ mode seal c⊒ body q shape comp)
        noM (no•-⟨⟩ noM′) =
      ⊑cast⊒ᴿ mode seal c⊒
        (term-ctx-insertᴿ insert body noM noM′)
        q shape comp
    term-ctx-insertᴿ insert
        (⊑cast⊑ᴿ mode seal c⊑ body q shape comp)
        noM (no•-⟨⟩ noM′) =
      ⊑cast⊑ᴿ mode seal c⊑
        (term-ctx-insertᴿ insert body noM noM′)
        q shape comp
    term-ctx-insertᴿ insert
        (conv↑⊑ᴿ conv body q replace)
        (no•-⟨⟩ noM) noM′ =
      conv↑⊑ᴿ conv
        (term-ctx-insertᴿ insert body noM noM′) q replace
    term-ctx-insertᴿ insert
        (conv↓⊑ᴿ conv body q replace)
        (no•-⟨⟩ noM) noM′ =
      conv↓⊑ᴿ conv
        (term-ctx-insertᴿ insert body noM noM′) q replace
    term-ctx-insertᴿ insert
        (⊑conv↑ᴿ conv body q replace)
        noM (no•-⟨⟩ noM′) =
      ⊑conv↑ᴿ conv
        (term-ctx-insertᴿ insert body noM noM′) q replace
    term-ctx-insertᴿ insert
        (⊑conv↓ᴿ conv body q replace)
        noM (no•-⟨⟩ noM′) =
      ⊑conv↓ᴿ conv
        (term-ctx-insertᴿ insert body noM noM′) q replace
    term-ctx-insertᴿ insert
        (paired-revealᴿ corresponds source target replace body)
        (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
      paired-revealᴿ corresponds source target replace
        (term-ctx-insertᴿ insert body noM noM′)
    term-ctx-insertᴿ insert
        (paired-concealᴿ corresponds source target replace body)
        (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
      paired-concealᴿ corresponds source target replace
        (term-ctx-insertᴿ insert body noM noM′)
    term-ctx-insertᴿ {η = η} insert
        (target-instantiationᴿ embedded) noM noM′
        rewrite
          rename-closedᵐ
            (typing-closedᵐ
              (forget (embedded-creation-source-typingᴱ embedded))) η
        | rename-closedᵐ
            (typing-closedᵐ
              (forget (embedded-creation-target-typingᴱ embedded))) η =
      target-instantiationᴿ embedded
    term-ctx-insertᴿ insert
        (closeᴿ body widening
          source-shape target-shape square compatible)
        (no•-⟨⟩ noN) (no•-⟨⟩ noN′) =
      closeᴿ
        (quotient-term-ctx-insertᴿ insert body noN noN′)
        widening source-shape target-shape square compatible
    term-ctx-insertᴿ insert
        (paired-wideningᴿ
          mode seal source source-shape
          mode′ seal′ target target-shape
          left-square right-square compatible body)
        (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
      paired-wideningᴿ
        mode seal source source-shape
        mode′ seal′ target target-shape
        left-square right-square compatible
        (term-ctx-insertᴿ insert body noM noM′)

    quotient-term-ctx-insertᴿ insert
        (paired-downᴿ
          body source-mode source source-shape
          target-mode target target-shape square)
        (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
      paired-downᴿ
        (term-ctx-insertᴿ insert body noM noM′)
        source-mode source source-shape
        target-mode target target-shape square


smaller-term-context-shiftᴿ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A B C C′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ} →
  No• M → No• M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ ctx-imp C C′ q ∷ γ
    ⊢ᴿ renameˣᵐ suc M ⊑ renameˣᵐ suc M′
    ⦂ A ⊑ B ∶ p
smaller-term-context-shiftᴿ noM noM′ M⊑M′ =
  term-ctx-insertᴿ insert-hereᴿ M⊑M′ noM noM′
