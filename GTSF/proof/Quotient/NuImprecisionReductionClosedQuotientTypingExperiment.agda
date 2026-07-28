module
  proof.Quotient.NuImprecisionReductionClosedQuotientTypingExperiment
  where

-- File Charter:
--   * Proves source and target typing projections for the independent smaller
--     ordinary term-imprecision relation.
--   * Proves the projections mutually with the one-boundary quotient
--     judgment, including both narrowing and quotient-closing casts.
--   * Uses the exact typing evidence retained by the composable embedded
--     target-instantiation creation residual.
--   * Contains no legacy term-imprecision judgment, postulate, hole,
--     permissive option, termination bypass, or catch-all clause.

open import Relation.Binary.PropositionalEquality using (subst)

open import Coercions using (id-only≤tag-or-idᵈ)
open import Conversion using
  (conceal-conversion-typing; reveal-conversion-typing)
open import Data.List using ([])
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; ⊑-src-wf)
open import NarrowWiden using
  (narrow-mode-relax; widen-mode-relax)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; leftStoreⁱ-lift
  ; leftStoreⁱ-lift-left
  ; rightStoreⁱ
  ; rightStoreⁱ-lift
  ; rightStoreⁱ-lift-left
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  ; leftCtxⁱ
  ; leftCtxⁱ-lift
  ; leftCtxⁱ-lift-left
  ; leftCtxⁱ-∋
  ; rightCtxⁱ
  ; rightCtxⁱ-lift
  ; rightCtxⁱ-lift-left
  ; rightCtxⁱ-∋
  )
open import proof.Core.Properties.SealModeProperties using
  (seal★-tag-or-id)
open import NuTerms using (Term)
open import TermTyping using
  ( cast-tag-or-id
  ; ⊢blame
  ; ⊢`
  ; ⊢ƛ
  ; ⊢·
  ; ⊢Λ
  ; ⊢ν↑
  ; ⊢$
  ; ⊢⊕
  ; ⊢⟨⟩↑
  ; ⊢⟨⟩↓
  ; ⊢⟨⟩⊒
  ; ⊢⟨⟩⊑
  ; forget
  ; _∣_∣_⊢_⦂_
  )
open import Types using (Ty; TyCtx)
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using
  ( embedded-creation-source-typingᴱ
  ; embedded-creation-target-typingᴱ
  )
open import QuotientImprecisionCompatibility
  using (SpineCastMode; id-only↓; gradual↓)
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
  using
  ( QuotientWideningPairᴿ
  ; blame⊑ᴿ
  ; x⊑xᴿ
  ; ƛ⊑ƛᴿ
  ; _·ᴿ_
  ; Λ⊑Λᴿ
  ; Λ⊑ᴿ
  ; α⊑αᴿ
  ; α⊑ᴿ
  ; allocation-prefixᴿ
  ; ν⊑νᴿ
  ; ν⊑ᴿ
  ; κ⊑κᴿ
  ; _⊕ᴿ[_]_
  ; gen⊑groundᴿ
  ; cast⊒⊑ᴿ
  ; cast⊑⊑ᴿ
  ; ⊑cast⊒ᴿ
  ; ⊑cast⊑ᴿ
  ; conv↑⊑ᴿ
  ; conv↓⊑ᴿ
  ; ⊑conv↑ᴿ
  ; ⊑conv↓ᴿ
  ; paired-revealᴿ
  ; paired-concealᴿ
  ; target-instantiationᴿ
  ; closeᴿ
  ; paired-wideningᴿ
  ; paired-downᴿ
  ; quotient-id-wideningᴿ
  ; quotient-cast-wideningᴿ
  ; _∣_∣_∣_∣_⊢ᴿ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴿᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
open import proof.Core.Properties.NuTermProperties using
  (closed-refined-typing-recontextualize; typing-closedᵐ)


private
  spine-source-cast-typing :
    ∀ {Δ Σ Γ M A B d μ} →
    SpineCastMode Σ μ →
    μ NarrowWiden.∣ Δ ∣ Σ ⊢ d ∶ A ⊒ B →
    Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
    Δ ∣ Σ ∣ Γ ⊢ NuTerms._⟨_⟩ M d ⦂ B
  spine-source-cast-typing id-only↓ d⊒ M⊢ =
    ⊢⟨⟩⊒ cast-tag-or-id seal★-tag-or-id
      (narrow-mode-relax id-only≤tag-or-idᵈ d⊒) M⊢
  spine-source-cast-typing (gradual↓ mode seal★) d⊒ M⊢ =
    ⊢⟨⟩⊒ mode seal★ d⊒ M⊢

  quotient-widening-source-typing :
    ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
      {Γ N D D′ A A′ u u′} →
    QuotientWideningPairᴿ Δᴸ Δᴿ ρ u u′ D D′ A A′ →
    Δᴸ ∣ leftStoreⁱ ρ ∣ Γ ⊢ N ⦂ D →
    Δᴸ ∣ leftStoreⁱ ρ ∣ Γ ⊢ NuTerms._⟨_⟩ N u ⦂ A
  quotient-widening-source-typing
      (quotient-id-wideningᴿ u⊑ u′⊑) N⊢ =
    ⊢⟨⟩⊑ cast-tag-or-id seal★-tag-or-id
      (widen-mode-relax id-only≤tag-or-idᵈ u⊑) N⊢
  quotient-widening-source-typing
      (quotient-cast-wideningᴿ
        mode seal★ u⊑ mode′ seal★′ u′⊑) N⊢ =
    ⊢⟨⟩⊑ mode seal★ u⊑ N⊢

  quotient-widening-target-typing :
    ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
      {Γ N′ D D′ A A′ u u′} →
    QuotientWideningPairᴿ Δᴸ Δᴿ ρ u u′ D D′ A A′ →
    Δᴿ ∣ rightStoreⁱ ρ ∣ Γ ⊢ N′ ⦂ D′ →
    Δᴿ ∣ rightStoreⁱ ρ ∣ Γ ⊢ NuTerms._⟨_⟩ N′ u′ ⦂ A′
  quotient-widening-target-typing
      (quotient-id-wideningᴿ u⊑ u′⊑) N′⊢ =
    ⊢⟨⟩⊑ cast-tag-or-id seal★-tag-or-id
      (widen-mode-relax id-only≤tag-or-idᵈ u′⊑) N′⊢
  quotient-widening-target-typing
      (quotient-cast-wideningᴿ
        mode seal★ u⊑ mode′ seal★′ u′⊑) N′⊢ =
    ⊢⟨⟩⊑ mode′ seal★′ u′⊑ N′⊢


mutual
  smaller-imprecision-source-typingᴿ :
    ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Δᴸ ∣ leftStoreⁱ ρ ∣ leftCtxⁱ γ ⊢ M ⦂ A

  smaller-imprecision-target-typingᴿ :
    ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M′ ⦂ B

  smaller-quotient-source-typingᴿ :
    ∀ {Φ Δᴸ Δᴿ ρ γ M M′ D D′}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴿᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
    Δᴸ ∣ leftStoreⁱ ρ ∣ leftCtxⁱ γ ⊢ M ⦂ D

  smaller-quotient-target-typingᴿ :
    ∀ {Φ Δᴸ Δᴿ ρ γ M M′ D D′}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴿᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
    Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M′ ⦂ D′

  smaller-imprecision-source-typingᴿ (blame⊑ᴿ {p = p} M′⊢) =
    ⊢blame (⊑-src-wf p)
  smaller-imprecision-source-typingᴿ (x⊑xᴿ x∈) =
    ⊢` (leftCtxⁱ-∋ x∈)
  smaller-imprecision-source-typingᴿ (ƛ⊑ƛᴿ hA hA′ N⊑N′) =
    ⊢ƛ hA (smaller-imprecision-source-typingᴿ N⊑N′)
  smaller-imprecision-source-typingᴿ (L⊑L′ ·ᴿ M⊑M′) =
    ⊢· (smaller-imprecision-source-typingᴿ L⊑L′)
       (smaller-imprecision-source-typingᴿ M⊑M′)
  smaller-imprecision-source-typingᴿ
      (Λ⊑Λᴿ {ρ = ρ} {γ = γ} liftρ liftγ vV vV′ V⊑V′) =
    ⊢Λ vV
      (subst
        (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
        (leftCtxⁱ-lift liftγ)
        (subst
          (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
          (leftStoreⁱ-lift liftρ)
          (smaller-imprecision-source-typingᴿ V⊑V′)))
  smaller-imprecision-source-typingᴿ
      (Λ⊑ᴿ occ liftρ liftγ vV V⊑N′) =
    ⊢Λ vV
      (subst
        (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
        (leftCtxⁱ-lift-left liftγ)
        (subst
          (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
          (leftStoreⁱ-lift-left liftρ)
          (smaller-imprecision-source-typingᴿ V⊑N′)))
  smaller-imprecision-source-typingᴿ
      (α⊑αᴿ vL noL vL′ noL′ A⇑⊑B⇑ liftρ liftγ
        L⊑L′ L•⊢ L′•⊢) =
    L•⊢
  smaller-imprecision-source-typingᴿ
      (α⊑ᴿ vL noL h⇑A liftρ liftγ L⊑N′ L•⊢ N′⊢) =
    L•⊢
  smaller-imprecision-source-typingᴿ
      (allocation-prefixᴿ prefix M⊑M′ M⊢ M′⊢) =
    M⊢
  smaller-imprecision-source-typingᴿ
      (ν⊑νᴿ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑ liftρ liftγ
        N⊑N′ replace) =
    ⊢ν↑ hA (smaller-imprecision-source-typingᴿ N⊑N′)
      (reveal-conversion-typing s↑)
  smaller-imprecision-source-typingᴿ
      (ν⊑ᴿ hA h⇑A s↑ liftρ liftγ N⊑N′ replace) =
    ⊢ν↑ hA (smaller-imprecision-source-typingᴿ N⊑N′)
      (reveal-conversion-typing s↑)
  smaller-imprecision-source-typingᴿ κ⊑κᴿ =
    ⊢$ _
  smaller-imprecision-source-typingᴿ
      (L⊑L′ ⊕ᴿ[ op ] M⊑M′) =
    ⊢⊕ (smaller-imprecision-source-typingᴿ L⊑L′) op
      (smaller-imprecision-source-typingᴿ M⊑M′)
  smaller-imprecision-source-typingᴿ
      (gen⊑groundᴿ mode seal★ c⊒ ground vV vW W⊢ V⊑Wtag q) =
    ⊢⟨⟩⊒ mode seal★ c⊒
      (smaller-imprecision-source-typingᴿ V⊑Wtag)
  smaller-imprecision-source-typingᴿ
      (cast⊒⊑ᴿ mode seal★ c⊒ M⊑M′ q shape comp) =
    ⊢⟨⟩⊒ mode seal★ c⊒
      (smaller-imprecision-source-typingᴿ M⊑M′)
  smaller-imprecision-source-typingᴿ
      (cast⊑⊑ᴿ mode seal★ c⊑ M⊑M′ q shape comp) =
    ⊢⟨⟩⊑ mode seal★ c⊑
      (smaller-imprecision-source-typingᴿ M⊑M′)
  smaller-imprecision-source-typingᴿ
      (⊑cast⊒ᴿ mode′ seal★′ c′⊒ M⊑M′ q shape comp) =
    smaller-imprecision-source-typingᴿ M⊑M′
  smaller-imprecision-source-typingᴿ
      (⊑cast⊑ᴿ mode′ seal★′ c′⊑ M⊑M′ q shape comp) =
    smaller-imprecision-source-typingᴿ M⊑M′
  smaller-imprecision-source-typingᴿ
      (conv↑⊑ᴿ c↑ M⊑M′ q replace) =
    ⊢⟨⟩↑ (reveal-conversion-typing c↑)
      (smaller-imprecision-source-typingᴿ M⊑M′)
  smaller-imprecision-source-typingᴿ
      (conv↓⊑ᴿ c↓ M⊑M′ q replace) =
    ⊢⟨⟩↓ (conceal-conversion-typing c↓)
      (smaller-imprecision-source-typingᴿ M⊑M′)
  smaller-imprecision-source-typingᴿ
      (⊑conv↑ᴿ c′↑ M⊑M′ q replace) =
    smaller-imprecision-source-typingᴿ M⊑M′
  smaller-imprecision-source-typingᴿ
      (⊑conv↓ᴿ c′↓ M⊑M′ q replace) =
    smaller-imprecision-source-typingᴿ M⊑M′
  smaller-imprecision-source-typingᴿ
      (paired-revealᴿ corresponds c↑ c′↑ replace M⊑M′) =
    ⊢⟨⟩↑ (reveal-conversion-typing c↑)
      (smaller-imprecision-source-typingᴿ M⊑M′)
  smaller-imprecision-source-typingᴿ
      (paired-concealᴿ corresponds c↓ c′↓ replace M⊑M′) =
    ⊢⟨⟩↓ (conceal-conversion-typing c↓)
      (smaller-imprecision-source-typingᴿ M⊑M′)
  smaller-imprecision-source-typingᴿ
      (target-instantiationᴿ embedded) =
    closed-refined-typing-recontextualize
      (typing-closedᵐ
        (forget (embedded-creation-source-typingᴱ embedded)))
      (embedded-creation-source-typingᴱ embedded)
  smaller-imprecision-source-typingᴿ
      (closeᴿ M⊑M′ widening-pair
        u-shape u′-shape square compatible) =
    quotient-widening-source-typing widening-pair
      (smaller-quotient-source-typingᴿ M⊑M′)
  smaller-imprecision-source-typingᴿ
      (paired-wideningᴿ
        mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
        left-square right-square compatible M⊑M′) =
    ⊢⟨⟩⊑ mode seal★ c⊑
      (smaller-imprecision-source-typingᴿ M⊑M′)

  smaller-imprecision-target-typingᴿ (blame⊑ᴿ M′⊢) =
    M′⊢
  smaller-imprecision-target-typingᴿ (x⊑xᴿ x∈) =
    ⊢` (rightCtxⁱ-∋ x∈)
  smaller-imprecision-target-typingᴿ (ƛ⊑ƛᴿ hA hA′ N⊑N′) =
    ⊢ƛ hA′ (smaller-imprecision-target-typingᴿ N⊑N′)
  smaller-imprecision-target-typingᴿ (L⊑L′ ·ᴿ M⊑M′) =
    ⊢· (smaller-imprecision-target-typingᴿ L⊑L′)
       (smaller-imprecision-target-typingᴿ M⊑M′)
  smaller-imprecision-target-typingᴿ
      (Λ⊑Λᴿ {ρ = ρ} {γ = γ} liftρ liftγ vV vV′ V⊑V′) =
    ⊢Λ vV′
      (subst
        (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
        (rightCtxⁱ-lift liftγ)
        (subst
          (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
          (rightStoreⁱ-lift liftρ)
          (smaller-imprecision-target-typingᴿ V⊑V′)))
  smaller-imprecision-target-typingᴿ
      (Λ⊑ᴿ occ liftρ liftγ vV V⊑N′) =
    subst
      (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
      (rightCtxⁱ-lift-left liftγ)
      (subst
        (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
        (rightStoreⁱ-lift-left liftρ)
        (smaller-imprecision-target-typingᴿ V⊑N′))
  smaller-imprecision-target-typingᴿ
      (α⊑αᴿ vL noL vL′ noL′ A⇑⊑B⇑ liftρ liftγ
        L⊑L′ L•⊢ L′•⊢) =
    L′•⊢
  smaller-imprecision-target-typingᴿ
      (α⊑ᴿ vL noL h⇑A liftρ liftγ L⊑N′ L•⊢ N′⊢) =
    N′⊢
  smaller-imprecision-target-typingᴿ
      (allocation-prefixᴿ prefix M⊑M′ M⊢ M′⊢) =
    M′⊢
  smaller-imprecision-target-typingᴿ
      (ν⊑νᴿ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑ liftρ liftγ
        N⊑N′ replace) =
    ⊢ν↑ hA′ (smaller-imprecision-target-typingᴿ N⊑N′)
      (reveal-conversion-typing s′↑)
  smaller-imprecision-target-typingᴿ
      (ν⊑ᴿ hA h⇑A s↑ liftρ liftγ N⊑N′ replace) =
    smaller-imprecision-target-typingᴿ N⊑N′
  smaller-imprecision-target-typingᴿ κ⊑κᴿ =
    ⊢$ _
  smaller-imprecision-target-typingᴿ
      (L⊑L′ ⊕ᴿ[ op ] M⊑M′) =
    ⊢⊕ (smaller-imprecision-target-typingᴿ L⊑L′) op
      (smaller-imprecision-target-typingᴿ M⊑M′)
  smaller-imprecision-target-typingᴿ
      (gen⊑groundᴿ mode seal★ c⊒ ground vV vW W⊢ V⊑Wtag q) =
    W⊢
  smaller-imprecision-target-typingᴿ
      (cast⊒⊑ᴿ mode seal★ c⊒ M⊑M′ q shape comp) =
    smaller-imprecision-target-typingᴿ M⊑M′
  smaller-imprecision-target-typingᴿ
      (cast⊑⊑ᴿ mode seal★ c⊑ M⊑M′ q shape comp) =
    smaller-imprecision-target-typingᴿ M⊑M′
  smaller-imprecision-target-typingᴿ
      (⊑cast⊒ᴿ mode′ seal★′ c′⊒ M⊑M′ q shape comp) =
    ⊢⟨⟩⊒ mode′ seal★′ c′⊒
      (smaller-imprecision-target-typingᴿ M⊑M′)
  smaller-imprecision-target-typingᴿ
      (⊑cast⊑ᴿ mode′ seal★′ c′⊑ M⊑M′ q shape comp) =
    ⊢⟨⟩⊑ mode′ seal★′ c′⊑
      (smaller-imprecision-target-typingᴿ M⊑M′)
  smaller-imprecision-target-typingᴿ
      (conv↑⊑ᴿ c↑ M⊑M′ q replace) =
    smaller-imprecision-target-typingᴿ M⊑M′
  smaller-imprecision-target-typingᴿ
      (conv↓⊑ᴿ c↓ M⊑M′ q replace) =
    smaller-imprecision-target-typingᴿ M⊑M′
  smaller-imprecision-target-typingᴿ
      (⊑conv↑ᴿ c′↑ M⊑M′ q replace) =
    ⊢⟨⟩↑ (reveal-conversion-typing c′↑)
      (smaller-imprecision-target-typingᴿ M⊑M′)
  smaller-imprecision-target-typingᴿ
      (⊑conv↓ᴿ c′↓ M⊑M′ q replace) =
    ⊢⟨⟩↓ (conceal-conversion-typing c′↓)
      (smaller-imprecision-target-typingᴿ M⊑M′)
  smaller-imprecision-target-typingᴿ
      (paired-revealᴿ corresponds c↑ c′↑ replace M⊑M′) =
    ⊢⟨⟩↑ (reveal-conversion-typing c′↑)
      (smaller-imprecision-target-typingᴿ M⊑M′)
  smaller-imprecision-target-typingᴿ
      (paired-concealᴿ corresponds c↓ c′↓ replace M⊑M′) =
    ⊢⟨⟩↓ (conceal-conversion-typing c′↓)
      (smaller-imprecision-target-typingᴿ M⊑M′)
  smaller-imprecision-target-typingᴿ
      (target-instantiationᴿ embedded) =
    closed-refined-typing-recontextualize
      (typing-closedᵐ
        (forget (embedded-creation-target-typingᴱ embedded)))
      (embedded-creation-target-typingᴱ embedded)
  smaller-imprecision-target-typingᴿ
      (closeᴿ M⊑M′ widening-pair
        u-shape u′-shape square compatible) =
    quotient-widening-target-typing widening-pair
      (smaller-quotient-target-typingᴿ M⊑M′)
  smaller-imprecision-target-typingᴿ
      (paired-wideningᴿ
        mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
        left-square right-square compatible M⊑M′) =
    ⊢⟨⟩⊑ mode′ seal★′ c′⊑
      (smaller-imprecision-target-typingᴿ M⊑M′)

  smaller-quotient-source-typingᴿ
      (paired-downᴿ
        M⊑M′ mode d⊒ d-shape mode′ d′⊒ d′-shape square) =
    spine-source-cast-typing mode d⊒
      (smaller-imprecision-source-typingᴿ M⊑M′)

  smaller-quotient-target-typingᴿ
      (paired-downᴿ
        M⊑M′ mode d⊒ d-shape mode′ d′⊒ d′-shape square) =
    spine-source-cast-typing mode′ d′⊒
      (smaller-imprecision-target-typingᴿ M⊑M′)
