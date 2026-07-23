module proof.NuImprecisionTermContextShiftProof where

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
open import NuTermImprecision using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftCtxⁱ
  ; LiftRightCtxⁱ
  ; StoreImp
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
open import Types using
  ( S
  ; Ty
  ; TyCtx
  ; Z
  ; _∋_⦂_
  ; ⇑ᵗ
  )
open import proof.MaximalLowerBoundsWf using
  (⊑-lift∀ᵢ; ⊑-source-liftνᵢ; ⊑-target-lift-rightᵢ)
open import proof.NuImprecisionTermContextShiftDef using
  (QuotientedTermContextShiftᵀ)
open import proof.NuTermProperties using
  (RenameWf; renameˣᵐ-preserves-No•; renameˣᵐ-preserves-Value)
open import proof.TypePreservation using (typing-renameˣ)


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
    _ , lift-ctx-∷ {p′ = ⊑-lift∀ᵢ q} liftγ , insert-hereⁱ
  term-ctx-insert-lift∀ⁱ
      (insert-underⁱ insert) (lift-ctx-∷ {p′ = p↑} liftγ)
      with term-ctx-insert-lift∀ⁱ insert liftγ
  term-ctx-insert-lift∀ⁱ
      (insert-underⁱ insert) (lift-ctx-∷ {p′ = p↑} liftγ)
      | δ↑ , liftδ , insert↑ =
    _ , lift-ctx-∷ {p′ = p↑} liftδ , insert-underⁱ insert↑


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
    _ , lift-left-ctx-∷ {p′ = ⊑-source-liftνᵢ q} liftγ ,
      insert-hereⁱ
  term-ctx-insert-lift-leftⁱ
      (insert-underⁱ insert) (lift-left-ctx-∷ {p′ = p↑} liftγ)
      with term-ctx-insert-lift-leftⁱ insert liftγ
  term-ctx-insert-lift-leftⁱ
      (insert-underⁱ insert) (lift-left-ctx-∷ {p′ = p↑} liftγ)
      | δ↑ , liftδ , insert↑ =
    _ , lift-left-ctx-∷ {p′ = p↑} liftδ , insert-underⁱ insert↑


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
    _ , lift-right-ctx-∷ {p′ = ⊑-target-lift-rightᵢ q} liftγ ,
      insert-hereⁱ
  term-ctx-insert-lift-rightⁱ
      (insert-underⁱ insert) (lift-right-ctx-∷ {p′ = p↑} liftγ)
      with term-ctx-insert-lift-rightⁱ insert liftγ
  term-ctx-insert-lift-rightⁱ
      (insert-underⁱ insert) (lift-right-ctx-∷ {p′ = p↑} liftγ)
      | δ↑ , liftδ , insert↑ =
    _ , lift-right-ctx-∷ {p′ = p↑} liftδ , insert-underⁱ insert↑


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
    term-ctx-insert-no•ᵀ insert (up⊑upᵀ N⊑N′ widening pA)
        (no•-⟨⟩ noN) (no•-⟨⟩ noN′) =
      up⊑upᵀ
        (term-ctx-insert-no•ᵀᵖ insert N⊑N′ noN noN′)
        widening pA
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
    term-ctx-insert-no•ᵀ insert
        (α⊑αᵀ vL noL vL′ noL′ pA liftρ liftγ
          L⊑L′ L⊢ L′⊢)
        () noM′
    term-ctx-insert-no•ᵀ insert
        (α⊑ᵀ vL noL hA liftρ liftγ L⊑N′ L⊢ N′⊢)
        () noN′
    term-ctx-insert-no•ᵀ insert
        (⊑αᵀ vL′ noL′ hA liftρ liftγ N⊑L′ r N⊢ L′⊢)
        noN ()
    term-ctx-insert-no•ᵀ insert
        (allocation-prefixᵀ prefix M⊑M′ M⊢ M′⊢) noM noM′ =
      allocation-prefixᵀ prefix
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)
        (typing-renameˣ (term-ctx-insert-left-wfⁱ insert) M⊢)
        (typing-renameˣ (term-ctx-insert-right-wfⁱ insert) M′⊢)
    term-ctx-insert-no•ᵀ insert
        (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A↑⊑A′↑
          liftρ liftγ N⊑N′)
        (no•-ν noN) (no•-ν noN′)
        with term-ctx-insert-lift∀ⁱ insert liftγ
    term-ctx-insert-no•ᵀ insert
        (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A↑⊑A′↑
          liftρ liftγ N⊑N′)
        (no•-ν noN) (no•-ν noN′)
        | δ↑ , liftδ , insert↑ =
      ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A↑⊑A′↑ liftρ liftδ
        (term-ctx-insert-no•ᵀ insert N⊑N′ noN noN′)
    term-ctx-insert-no•ᵀ insert
        (ν⊑ᵀ hA hA↑ s↑ liftρ liftγ N⊑N′)
        (no•-ν noN) noN′
        with term-ctx-insert-lift-leftⁱ insert liftγ
    term-ctx-insert-no•ᵀ insert
        (ν⊑ᵀ hA hA↑ s↑ liftρ liftγ N⊑N′)
        (no•-ν noN) noN′
        | δ↑ , liftδ , insert↑ =
      ν⊑ᵀ hA hA↑ s↑ liftρ liftδ
        (term-ctx-insert-no•ᵀ insert N⊑N′ noN noN′)
    term-ctx-insert-no•ᵀ insert
        (⊑νᵀ hA hA↑ s↑ liftρ liftγ r N⊑N′)
        noN (no•-ν noN′)
        with term-ctx-insert-lift-rightⁱ insert liftγ
    term-ctx-insert-no•ᵀ insert
        (⊑νᵀ hA hA↑ s↑ liftρ liftγ r N⊑N′)
        noN (no•-ν noN′)
        | δ↑ , liftδ , insert↑ =
      ⊑νᵀ hA hA↑ s↑ liftρ liftδ r
        (term-ctx-insert-no•ᵀ insert N⊑N′ noN noN′)
    term-ctx-insert-no•ᵀ insert
        (νcast⊑νcastᵀ mode seal mode′ seal′ s⊑ s′⊑ compat
          liftρ liftγ N⊑N′)
        (no•-ν noN) (no•-ν noN′)
        with term-ctx-insert-lift∀ⁱ insert liftγ
    term-ctx-insert-no•ᵀ insert
        (νcast⊑νcastᵀ mode seal mode′ seal′ s⊑ s′⊑ compat
          liftρ liftγ N⊑N′)
        (no•-ν noN) (no•-ν noN′)
        | δ↑ , liftδ , insert↑ =
      νcast⊑νcastᵀ mode seal mode′ seal′ s⊑ s′⊑ compat
        liftρ liftδ
        (term-ctx-insert-no•ᵀ insert N⊑N′ noN noN′)
    term-ctx-insert-no•ᵀ insert
        (νcast⊑ᵀ mode seal s⊑ liftρ liftγ N⊑N′)
        (no•-ν noN) noN′
        with term-ctx-insert-lift-leftⁱ insert liftγ
    term-ctx-insert-no•ᵀ insert
        (νcast⊑ᵀ mode seal s⊑ liftρ liftγ N⊑N′)
        (no•-ν noN) noN′
        | δ↑ , liftδ , insert↑ =
      νcast⊑ᵀ mode seal s⊑ liftρ liftδ
        (term-ctx-insert-no•ᵀ insert N⊑N′ noN noN′)
    term-ctx-insert-no•ᵀ insert
        (⊑νcastᵀ mode seal s⊑ liftρ liftγ r N⊑N′)
        noN (no•-ν noN′)
        with term-ctx-insert-lift-rightⁱ insert liftγ
    term-ctx-insert-no•ᵀ insert
        (⊑νcastᵀ mode seal s⊑ liftρ liftγ r N⊑N′)
        noN (no•-ν noN′)
        | δ↑ , liftδ , insert↑ =
      ⊑νcastᵀ mode seal s⊑ liftρ liftδ r
        (term-ctx-insert-no•ᵀ insert N⊑N′ noN noN′)
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
        (cast⊒⊑ᵀ mode seal c⊒ M⊑M′ q)
        (no•-⟨⟩ noM) noM′ =
      cast⊒⊑ᵀ mode seal c⊒
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′) q
    term-ctx-insert-no•ᵀ insert
        (cast⊑⊑ᵀ mode seal c⊑ M⊑M′ q)
        (no•-⟨⟩ noM) noM′ =
      cast⊑⊑ᵀ mode seal c⊑
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′) q
    term-ctx-insert-no•ᵀ insert
        (⊑cast⊒ᵀ mode seal c⊒ M⊑M′ q)
        noM (no•-⟨⟩ noM′) =
      ⊑cast⊒ᵀ mode seal c⊒
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′) q
    term-ctx-insert-no•ᵀ insert
        (⊑cast⊑ᵀ mode seal c⊑ M⊑M′ q)
        noM (no•-⟨⟩ noM′) =
      ⊑cast⊑ᵀ mode seal c⊑
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′) q
    term-ctx-insert-no•ᵀ insert
        (⊑cast⊑idᵀ seal c⊑ M⊑M′ q)
        noM (no•-⟨⟩ noM′) =
      ⊑cast⊑idᵀ seal c⊑
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′) q
    term-ctx-insert-no•ᵀ insert (conv⊑convᵀ cast M⊑M′)
        (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
      conv⊑convᵀ cast
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)
    term-ctx-insert-no•ᵀ insert (conv↑⊑ᵀ conv M⊑M′ q)
        (no•-⟨⟩ noM) noM′ =
      conv↑⊑ᵀ conv
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′) q
    term-ctx-insert-no•ᵀ insert (conv↓⊑ᵀ conv M⊑M′ q)
        (no•-⟨⟩ noM) noM′ =
      conv↓⊑ᵀ conv
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′) q
    term-ctx-insert-no•ᵀ insert (⊑conv↑ᵀ conv M⊑M′ q)
        noM (no•-⟨⟩ noM′) =
      ⊑conv↑ᵀ conv
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′) q
    term-ctx-insert-no•ᵀ insert (⊑conv↓ᵀ conv M⊑M′ q)
        noM (no•-⟨⟩ noM′) =
      ⊑conv↓ᵀ conv
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′) q

    term-ctx-insert-no•ᵀᵖ insert
        (down⊑downᵀ d⊒ d′⊒ M⊑M′ q)
        (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
      down⊑downᵀ d⊒ d′⊒
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′) q
    term-ctx-insert-no•ᵀᵖ insert
        (gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ q)
        (no•-⟨⟩ noM) (no•-⟨⟩ noM′) =
      gen-down⊑gen-downᵀ d⊒ d′⊒
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′) q
    term-ctx-insert-no•ᵀᵖ insert
        (ordinary-down-applicationᵖᵀ
          mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′)
        (no•-· noL (no•-⟨⟩ noM))
        (no•-· noL′ (no•-⟨⟩ noM′)) =
      ordinary-down-applicationᵖᵀ
        mode seal★ d⊒ mode′ seal★′ d′⊒
        (term-ctx-insert-no•ᵀ insert L⊑L′ noL noL′)
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)
    term-ctx-insert-no•ᵀᵖ insert
        (quotient-id-down-applicationᵖᵀ d⊒ d′⊒ L⊑L′ M⊑M′)
        (no•-· noL (no•-⟨⟩ noM))
        (no•-· noL′ (no•-⟨⟩ noM′)) =
      quotient-id-down-applicationᵖᵀ d⊒ d′⊒
        (term-ctx-insert-no•ᵀᵖ insert L⊑L′ noL noL′)
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)
    term-ctx-insert-no•ᵀᵖ insert
        (quotient-down-applicationᵖᵀ
          mode seal★ d⊒ mode′ seal★′ d′⊒ L⊑L′ M⊑M′)
        (no•-· noL (no•-⟨⟩ noM))
        (no•-· noL′ (no•-⟨⟩ noM′)) =
      quotient-down-applicationᵖᵀ
        mode seal★ d⊒ mode′ seal★′ d′⊒
        (term-ctx-insert-no•ᵀᵖ insert L⊑L′ noL noL′)
        (term-ctx-insert-no•ᵀ insert M⊑M′ noM noM′)


quotiented-term-context-shift-proofᵀ : QuotientedTermContextShiftᵀ
quotiented-term-context-shift-proofᵀ noM noM′ M⊑M′ =
  term-ctx-insert-no•ᵀ insert-hereⁱ M⊑M′ noM noM′
