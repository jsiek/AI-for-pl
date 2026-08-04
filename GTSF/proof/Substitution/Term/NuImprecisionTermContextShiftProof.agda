module proof.Substitution.Term.NuImprecisionTermContextShiftProof where

-- File Charter:
--   * Proves no-bullet quotiented term-context shift.
--   * Uses one private insertion judgment to keep the fresh variable at the
--     correct depth beneath ordinary lambdas and to lift that insertion
--     coherently beneath paired, left-only, and right-only type binders.
--   * Traverses ordinary and quotient relations mutually and exhaustively.
--   * Contains no postulate, hole, catch-all, or permissive option.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_; _ˣ⊑★; _ˣ⊑ˣ_; ⇑ᴸᵢ; ⇑ᴿᵢ; ⇑ᵢ)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftCtxⁱ
  ; LiftRightCtxⁱ
  ; ctx-imp
  ; leftCtxⁱ
  ; lift-ctx-∷
  ; lift-left-ctx-∷
  ; lift-right-ctx-∷
  ; rightCtxⁱ
  )
open import NuTerms using
  ( No•
  ; Renameˣ
  ; Term
  ; extʳ
  ; no•-$
  ; no•-blame
  ; no•-Λ
  ; no•-ν
  ; no•-·
  ; no•-`
  ; no•-ƛ
  ; no•-⊕
  ; no•-⟨⟩
  ; renameˣᵐ
  )
open import QuotientedTermImprecision
open import TermTyping using (forget)
open import Types using
  ( S
  ; Ty
  ; TyCtx
  ; Z
  ; _∋_⦂_
  ; ⇑ᵗ
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  (⊑-lift∀ᵢ; ⊑-source-liftνᵢ; ⊑-target-lift-rightᵢ)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( shape-lift∀ᵢ
  ; shape-source-liftνᵢ
  ; shape-target-lift-rightᵢ
  )
open import proof.Substitution.Term.NuImprecisionTermContextShiftDef using
  (QuotientedTermContextShiftᵀ)
open import proof.Core.Properties.NuTermProperties using
  ( closed-refined-typing-recontextualize
  ; RenameWf
  ; rename-closedᵐ
  ; renameˣᵐ-preserves-No•
  ; renameˣᵐ-preserves-Value
  ; typing-closedᵐ
  )
open import proof.Core.Properties.TypePreservation using (typing-renameˣ)
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using
  ( embedded-creation-source-typingᴱ
  ; embedded-creation-target-typingᴱ
  )


private
  data TermCtxInsertⁱ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      (C C′ : Ty) (q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ) :
      CtxImp Φ Δᴸ Δᴿ → CtxImp Φ Δᴸ Δᴿ → Renameˣ → Set₁ where
    insert-hereⁱ : ∀ {γ} →
      TermCtxInsertⁱ C C′ q γ (ctx-imp C C′ q ∷ γ) suc

    insert-underⁱ : ∀ {γ δ η A B p} →
      TermCtxInsertⁱ C C′ q γ δ η →
      TermCtxInsertⁱ C C′ q
        (ctx-imp A B p ∷ γ) (ctx-imp A B p ∷ δ) (extʳ η)


  term-ctx-insert-lookupⁱ :
    ∀ {Φ Δᴸ Δᴿ C C′ q γ δ η x A B p} →
    TermCtxInsertⁱ {Φ} {Δᴸ} {Δᴿ} C C′ q γ δ η →
    γ ∋ x ⦂ ctx-imp A B p →
    δ ∋ η x ⦂ ctx-imp A B p
  term-ctx-insert-lookupⁱ insert-hereⁱ x∈ = S x∈
  term-ctx-insert-lookupⁱ (insert-underⁱ insert) Z = Z
  term-ctx-insert-lookupⁱ (insert-underⁱ insert) (S x∈) =
    S (term-ctx-insert-lookupⁱ insert x∈)


  term-ctx-insert-left-wfⁱ :
    ∀ {Φ Δᴸ Δᴿ C C′ q γ δ η} →
    TermCtxInsertⁱ {Φ} {Δᴸ} {Δᴿ} C C′ q γ δ η →
    RenameWf (leftCtxⁱ γ) (leftCtxⁱ δ) η
  term-ctx-insert-left-wfⁱ insert-hereⁱ x∈ = S x∈
  term-ctx-insert-left-wfⁱ (insert-underⁱ insert) Z = Z
  term-ctx-insert-left-wfⁱ (insert-underⁱ insert) (S x∈) =
    S (term-ctx-insert-left-wfⁱ insert x∈)


  term-ctx-insert-right-wfⁱ :
    ∀ {Φ Δᴸ Δᴿ C C′ q γ δ η} →
    TermCtxInsertⁱ {Φ} {Δᴸ} {Δᴿ} C C′ q γ δ η →
    RenameWf (rightCtxⁱ γ) (rightCtxⁱ δ) η
  term-ctx-insert-right-wfⁱ insert-hereⁱ x∈ = S x∈
  term-ctx-insert-right-wfⁱ (insert-underⁱ insert) Z = Z
  term-ctx-insert-right-wfⁱ (insert-underⁱ insert) (S x∈) =
    S (term-ctx-insert-right-wfⁱ insert x∈)


  term-ctx-insert-lift∀ⁱ :
    ∀ {Φ Δᴸ Δᴿ C C′ q γ δ η γ↑} →
    (insert : TermCtxInsertⁱ {Φ} {Δᴸ} {Δᴿ}
      C C′ q γ δ η) →
    LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ↑ →
    ∃[ δ↑ ]
      LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) δ δ↑ ×
      TermCtxInsertⁱ (⇑ᵗ C) (⇑ᵗ C′) (⊑-lift∀ᵢ q)
        γ↑ δ↑ η
  term-ctx-insert-lift∀ⁱ {q = q} insert-hereⁱ liftγ =
    _ ,
    lift-ctx-∷ {p′ = ⊑-lift∀ᵢ q}
      (shape-lift∀ᵢ q) liftγ ,
    insert-hereⁱ
  term-ctx-insert-lift∀ⁱ
      (insert-underⁱ insert)
      (lift-ctx-∷ {p′ = p↑} shape-eq liftγ)
      with term-ctx-insert-lift∀ⁱ insert liftγ
  term-ctx-insert-lift∀ⁱ
      (insert-underⁱ insert)
      (lift-ctx-∷ {p′ = p↑} shape-eq liftγ)
      | δ↑ , liftδ , insert↑ =
    _ , lift-ctx-∷ {p′ = p↑} shape-eq liftδ ,
    insert-underⁱ insert↑


  term-ctx-insert-lift-leftⁱ :
    ∀ {Φ Δᴸ Δᴿ C C′ q γ δ η γ↑} →
    (insert : TermCtxInsertⁱ {Φ} {Δᴸ} {Δᴿ}
      C C′ q γ δ η) →
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ↑ →
    ∃[ δ↑ ]
      LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) δ δ↑ ×
      TermCtxInsertⁱ (⇑ᵗ C) C′ (⊑-source-liftνᵢ q)
        γ↑ δ↑ η
  term-ctx-insert-lift-leftⁱ {q = q} insert-hereⁱ liftγ =
    _ ,
    lift-left-ctx-∷ {p′ = ⊑-source-liftνᵢ q}
      (shape-source-liftνᵢ q) liftγ ,
    insert-hereⁱ
  term-ctx-insert-lift-leftⁱ
      (insert-underⁱ insert)
      (lift-left-ctx-∷ {p′ = p↑} shape-eq liftγ)
      with term-ctx-insert-lift-leftⁱ insert liftγ
  term-ctx-insert-lift-leftⁱ
      (insert-underⁱ insert)
      (lift-left-ctx-∷ {p′ = p↑} shape-eq liftγ)
      | δ↑ , liftδ , insert↑ =
    _ , lift-left-ctx-∷ {p′ = p↑} shape-eq liftδ ,
    insert-underⁱ insert↑


  term-ctx-insert-lift-rightⁱ :
    ∀ {Φ Δᴸ Δᴿ C C′ q γ δ η γ↑} →
    (insert : TermCtxInsertⁱ {Φ} {Δᴸ} {Δᴿ}
      C C′ q γ δ η) →
    LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γ↑ →
    ∃[ δ↑ ]
      LiftRightCtxⁱ (⇑ᴿᵢ Φ) δ δ↑ ×
      TermCtxInsertⁱ C (⇑ᵗ C′) (⊑-target-lift-rightᵢ q)
        γ↑ δ↑ η
  term-ctx-insert-lift-rightⁱ {q = q} insert-hereⁱ liftγ =
    _ ,
    lift-right-ctx-∷ {p′ = ⊑-target-lift-rightᵢ q}
      (shape-target-lift-rightᵢ q) liftγ ,
    insert-hereⁱ
  term-ctx-insert-lift-rightⁱ
      (insert-underⁱ insert)
      (lift-right-ctx-∷ {p′ = p↑} shape-eq liftγ)
      with term-ctx-insert-lift-rightⁱ insert liftγ
  term-ctx-insert-lift-rightⁱ
      (insert-underⁱ insert)
      (lift-right-ctx-∷ {p′ = p↑} shape-eq liftγ)
      | δ↑ , liftδ , insert↑ =
    _ , lift-right-ctx-∷ {p′ = p↑} shape-eq liftδ ,
    insert-underⁱ insert↑


  mutual
    term-ctx-insert-no•ᵀ :
      ∀ {Φ Δᴸ Δᴿ ρ γ δ η C C′ q M M′ A B p} →
      (insert : TermCtxInsertⁱ {Φ} {Δᴸ} {Δᴿ}
        C C′ q γ δ η) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
      No• M → No• M′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
        ⊢ᴺ renameˣᵐ η M ⊑ renameˣᵐ η M′
        ⦂ A ⊑ B ∶ p

    term-ctx-insert-no•ᵀᵖ :
      ∀ {Φ Δᴸ Δᴿ ρ γ δ η C C′ q M M′ D D′ pD} →
      (insert : TermCtxInsertⁱ {Φ} {Δᴸ} {Δᴿ}
        C C′ q γ δ η) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ pD →
      No• M → No• M′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
        ⊢ᴺᵖ renameˣᵐ η M ⊑ renameˣᵐ η M′
        ⦂ D ⊑ᵖ D′ ∶ pD

    term-ctx-insert-no•ᵀ insert (blame⊑ᵀ M′⊢)
        no•-blame noM′ =
      blame⊑ᵀ (typing-renameˣ
        (term-ctx-insert-right-wfⁱ insert) M′⊢)
    term-ctx-insert-no•ᵀ insert (x⊑xᵀ x∈) no•-` no•-` =
      x⊑xᵀ (term-ctx-insert-lookupⁱ insert x∈)
    term-ctx-insert-no•ᵀ insert (ƛ⊑ƛᵀ hA hA′ N⊑N′)
        (no•-ƛ noN) (no•-ƛ noN′) =
      ƛ⊑ƛᵀ hA hA′
        (term-ctx-insert-no•ᵀ
          (insert-underⁱ insert) N⊑N′ noN noN′)
    term-ctx-insert-no•ᵀ insert (·⊑·ᵀ L⊑L′ M⊑M′)
        (no•-· noL noM) (no•-· noL′ noM′) =
      ·⊑·ᵀ
        (term-ctx-insert-no•ᵀ insert L⊑L′ noL noL′)
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)
    term-ctx-insert-no•ᵀ insert
        (closeᵀ N⊑N′ widening pA
          u-shape u′-shape square compatible)
        (no•-⟨⟩ noN) (no•-⟨⟩ noN′) =
      closeᵀ
        (term-ctx-insert-no•ᵀᵖ insert N⊑N′ noN noN′)
        widening pA u-shape u′-shape square compatible
    term-ctx-insert-no•ᵀ insert
        (Λ⊑Λᵀ liftρ liftγ vV vV′ V⊑V′)
        (no•-Λ noV) (no•-Λ noV′)
        with term-ctx-insert-lift∀ⁱ insert liftγ
    term-ctx-insert-no•ᵀ insert
        (Λ⊑Λᵀ liftρ liftγ vV vV′ V⊑V′)
        (no•-Λ noV) (no•-Λ noV′)
        | δ↑ , liftδ , insert↑ =
      Λ⊑Λᵀ liftρ liftδ
        (renameˣᵐ-preserves-Value _ vV)
        (renameˣᵐ-preserves-Value _ vV′)
        (term-ctx-insert-no•ᵀ insert↑ V⊑V′ noV noV′)
    term-ctx-insert-no•ᵀ insert
        (Λ⊑ᵀ occ liftρ liftγ vV V⊑N′)
        (no•-Λ noV) noN′
        with term-ctx-insert-lift-leftⁱ insert liftγ
    term-ctx-insert-no•ᵀ insert
        (Λ⊑ᵀ occ liftρ liftγ vV V⊑N′)
        (no•-Λ noV) noN′
        | δ↑ , liftδ , insert↑ =
      Λ⊑ᵀ occ liftρ liftδ
        (renameˣᵐ-preserves-Value _ vV)
        (term-ctx-insert-no•ᵀ insert↑ V⊑N′ noV noN′)
    term-ctx-insert-no•ᵀ {η = ζ} insert
        (target-instantiationᵀ embedded)
        noM₀ noM′₀
        rewrite rename-closedᵐ
                  (typing-closedᵐ
                    (forget
                      (embedded-creation-source-typingᴱ embedded)))
                  ζ
              | rename-closedᵐ
                  (typing-closedᵐ
                    (forget
                      (embedded-creation-target-typingᴱ embedded)))
                  ζ =
      target-instantiationᵀ embedded
    term-ctx-insert-no•ᵀ insert
        (α⊑αᵀ vL noL vL′ noL′ pA liftρ liftγ
          L⊑L′ prefix L⊢ L′⊢)
        () noM′
    term-ctx-insert-no•ᵀ insert
        (α⊑ᵀ vL noL hA liftρ liftγ L⊑N′ prefix L⊢ N′⊢)
        () noN′
    term-ctx-insert-no•ᵀ insert
        (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A↑⊑A′↑
          liftρ liftγ N⊑N′ replace)
        (no•-ν noN) (no•-ν noN′)
        with term-ctx-insert-lift∀ⁱ insert liftγ
    term-ctx-insert-no•ᵀ insert
        (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A↑⊑A′↑
          liftρ liftγ N⊑N′ replace)
        (no•-ν noN) (no•-ν noN′)
        | δ↑ , liftδ , insert↑ =
      ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A↑⊑A′↑ liftρ liftδ
        (term-ctx-insert-no•ᵀ insert N⊑N′ noN noN′)
        replace
    term-ctx-insert-no•ᵀ insert
        (ν⊑ᵀ hA hA↑ s↑ liftρ liftγ N⊑N′ replace)
        (no•-ν noN) noN′
        with term-ctx-insert-lift-leftⁱ insert liftγ
    term-ctx-insert-no•ᵀ insert
        (ν⊑ᵀ hA hA↑ s↑ liftρ liftγ N⊑N′ replace)
        (no•-ν noN) noN′
        | δ↑ , liftδ , insert↑ =
      ν⊑ᵀ hA hA↑ s↑ liftρ liftδ
        (term-ctx-insert-no•ᵀ insert N⊑N′ noN noN′)
        replace
    term-ctx-insert-no•ᵀ insert κ⊑κᵀ no•-$ no•-$ =
      κ⊑κᵀ
    term-ctx-insert-no•ᵀ insert (⊕⊑⊕ᵀ L⊑L′ M⊑M′)
        (no•-⊕ noL noM) (no•-⊕ noL′ noM′) =
      ⊕⊑⊕ᵀ
        (term-ctx-insert-no•ᵀ insert L⊑L′ noL noL′)
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)
    term-ctx-insert-no•ᵀ insert
        (gen⊑groundᵀ mode seal c⊒ gH vV vW W⊢ V⊑Wtag q)
        (no•-⟨⟩ noV) noW =
      gen⊑groundᵀ mode seal c⊒ gH
        (renameˣᵐ-preserves-Value _ vV)
        (renameˣᵐ-preserves-Value _ vW)
        (typing-renameˣ (term-ctx-insert-right-wfⁱ insert) W⊢)
        (term-ctx-insert-no•ᵀ
          insert V⊑Wtag noV (no•-⟨⟩ noW)) q
    term-ctx-insert-no•ᵀ insert
        (cast⊒⊑ᵀ mode seal c⊒ M⊑M′ q c-shape comp)
        (no•-⟨⟩ noM) noM′ =
      cast⊒⊑ᵀ mode seal c⊒
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)
        q c-shape comp
    term-ctx-insert-no•ᵀ insert
        (cast⊑⊑ᵀ mode seal c⊑ M⊑M′ q c-shape comp)
        (no•-⟨⟩ noM) noM′ =
      cast⊑⊑ᵀ mode seal c⊑
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)
        q c-shape comp
    term-ctx-insert-no•ᵀ insert
        (⊑cast⊒ᵀ mode seal c⊒ M⊑M′ q c-shape comp)
        noM (no•-⟨⟩ noM′) =
      ⊑cast⊒ᵀ mode seal c⊒
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)
        q c-shape comp
    term-ctx-insert-no•ᵀ insert
        (⊑cast⊑ᵀ mode seal c⊑ M⊑M′ q c-shape comp)
        noM (no•-⟨⟩ noM′) =
      ⊑cast⊑ᵀ mode seal c⊑
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)
        q c-shape comp
    term-ctx-insert-no•ᵀ insert
        (paired-revealᵀ corresponds source target replace M⊑M′)
        (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
      paired-revealᵀ corresponds source target replace
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)
    term-ctx-insert-no•ᵀ insert
        (paired-concealᵀ corresponds source target replace M⊑M′)
        (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
      paired-concealᵀ corresponds source target replace
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)
    term-ctx-insert-no•ᵀ insert
        (paired-wideningᵀ
          mode seal★ source source-shape
          mode′ seal★′ target target-shape
          left-square right-square compatible M⊑M′)
        (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
      paired-wideningᵀ
        mode seal★ source source-shape
        mode′ seal★′ target target-shape
        left-square right-square compatible
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)
    term-ctx-insert-no•ᵀ insert
        (conv↑⊑ᵀ conv M⊑M′ q replace)
        (no•-⟨⟩ noM) noM′ =
      conv↑⊑ᵀ conv
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)
        q replace
    term-ctx-insert-no•ᵀ insert
        (conv↓⊑ᵀ conv M⊑M′ q replace)
        (no•-⟨⟩ noM) noM′ =
      conv↓⊑ᵀ conv
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)
        q replace
    term-ctx-insert-no•ᵀ insert
        (⊑conv↑ᵀ conv M⊑M′ q replace)
        noM (no•-⟨⟩ noM′) =
      ⊑conv↑ᵀ conv
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)
        q replace
    term-ctx-insert-no•ᵀ insert
        (⊑conv↓ᵀ conv M⊑M′ q replace)
        noM (no•-⟨⟩ noM′) =
      ⊑conv↓ᵀ conv
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)
        q replace

    term-ctx-insert-no•ᵀᵖ insert
        (paired-downᵀ
          M⊑M′ mode d⊒ d-shape mode′ d′⊒ d′-shape square elimination)
        (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
      paired-downᵀ
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)
        mode d⊒ d-shape mode′ d′⊒ d′-shape square elimination


quotiented-term-context-shift-proofᵀ : QuotientedTermContextShiftᵀ
quotiented-term-context-shift-proofᵀ noM noM′ M⊑M′ =
  term-ctx-insert-no•ᵀ insert-hereⁱ M⊑M′ noM noM′
