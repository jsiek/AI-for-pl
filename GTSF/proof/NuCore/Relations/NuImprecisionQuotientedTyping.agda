module
  proof.NuCore.Relations.NuImprecisionQuotientedTyping
  where

-- File Charter:
--   * Proves source and target typing for the live ordinary and quotiented
--     term-imprecision judgments.
--   * Keeps proof-only typing recursion out of the high-fanout grammar
--     module.
--   * Contains no term-imprecision constructor, compatibility alias,
--     postulate, hole, or broad simulation import.

open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (subst)

open import Coercions using
  (id-only≤tag-or-idᵈ)
open import Conversion using
  (conceal-conversion-typing; reveal-conversion-typing)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf
open import NarrowWiden using
  ( narrow-mode-relax
  ; widen-mode-relax
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
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
  ( leftCtxⁱ
  ; leftCtxⁱ-∋
  ; leftCtxⁱ-lift
  ; leftCtxⁱ-lift-left
  ; rightCtxⁱ
  ; rightCtxⁱ-∋
  ; rightCtxⁱ-lift
  ; rightCtxⁱ-lift-left
  )
open import proof.Core.Properties.CastImprecision using
  ( seal★-tag-or-id
  )
open import NuTerms using (_⟨_⟩)
open import Primitives
open import QuotientImprecisionCompatibility using
  (SpineCastMode; id-only↓; gradual↓)
open import QuotientedTermImprecision
open import TermTyping using
  ( cast-tag-or-id
  ; forget
  ; _∣_∣_⊢_⦂_
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
  ; ⊢blame
  )
open import Types
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using
  ( embedded-creation-source-typingᴱ
  ; embedded-creation-target-typingᴱ
  )
open import proof.Core.Properties.NuTermProperties using
  (closed-refined-typing-recontextualize; typing-closedᵐ)


private
  spine-source-cast-typing :
    ∀ {Δ Σ Γ M A B d μ} →
    SpineCastMode Σ μ →
    μ ∣ Δ ∣ Σ ⊢ d ∶ A ⊒ B →
    Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
    Δ ∣ Σ ∣ Γ ⊢ M ⟨ d ⟩ ⦂ B
  spine-source-cast-typing id-only↓ d⊒ M⊢ =
    ⊢⟨⟩⊒ cast-tag-or-id seal★-tag-or-id
      (narrow-mode-relax id-only≤tag-or-idᵈ d⊒) M⊢
  spine-source-cast-typing (gradual↓ mode seal★) d⊒ M⊢ =
    ⊢⟨⟩⊒ mode seal★ d⊒ M⊢

  quotient-widening-source-typing :
    ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
      {Γ N D D′ A A′ u u′} →
    QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
    Δᴸ ∣ leftStoreⁱ ρ ∣ Γ ⊢ N ⦂ D →
    Δᴸ ∣ leftStoreⁱ ρ ∣ Γ ⊢ N ⟨ u ⟩ ⦂ A
  quotient-widening-source-typing
      (quotient-id-widening u⊑ u′⊑) N⊢ =
    ⊢⟨⟩⊑ cast-tag-or-id seal★-tag-or-id
      (widen-mode-relax id-only≤tag-or-idᵈ u⊑) N⊢
  quotient-widening-source-typing
      (quotient-cast-widening
        mode seal★ u⊑ mode′ seal★′ u′⊑) N⊢ =
    ⊢⟨⟩⊑ mode seal★ u⊑ N⊢

  quotient-widening-target-typing :
    ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
      {Γ N′ D D′ A A′ u u′} →
    QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
    Δᴿ ∣ rightStoreⁱ ρ ∣ Γ ⊢ N′ ⦂ D′ →
    Δᴿ ∣ rightStoreⁱ ρ ∣ Γ ⊢ N′ ⟨ u′ ⟩ ⦂ A′
  quotient-widening-target-typing
      (quotient-id-widening u⊑ u′⊑) N′⊢ =
    ⊢⟨⟩⊑ cast-tag-or-id seal★-tag-or-id
      (widen-mode-relax id-only≤tag-or-idᵈ u′⊑) N′⊢
  quotient-widening-target-typing
      (quotient-cast-widening
        mode seal★ u⊑ mode′ seal★′ u′⊑) N′⊢ =
    ⊢⟨⟩⊑ mode′ seal★′ u′⊑ N′⊢


mutual
  nu-term-imprecision-source-typing :
    ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Δᴸ ∣ leftStoreⁱ ρ ∣ leftCtxⁱ γ ⊢ M ⦂ A

  nu-term-imprecision-target-typing :
    ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M′ ⦂ B

  quotiented-nu-term-imprecision-source-typing :
    ∀ {Φ Δᴸ Δᴿ ρ γ M M′ D D′}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
    Δᴸ ∣ leftStoreⁱ ρ ∣ leftCtxⁱ γ ⊢ M ⦂ D

  quotiented-nu-term-imprecision-target-typing :
    ∀ {Φ Δᴸ Δᴿ ρ γ M M′ D D′}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
    Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M′ ⦂ D′

  nu-term-imprecision-source-typing (blame⊑ᵀ {p = p} M′⊢) =
    ⊢blame (⊑-src-wf p)
  nu-term-imprecision-source-typing (x⊑xᵀ x∈) =
    ⊢` (leftCtxⁱ-∋ x∈)
  nu-term-imprecision-source-typing (ƛ⊑ƛᵀ hA hA′ N⊑N′) =
    ⊢ƛ hA (nu-term-imprecision-source-typing N⊑N′)
  nu-term-imprecision-source-typing (·⊑·ᵀ L⊑L′ M⊑M′) =
    ⊢·
      (nu-term-imprecision-source-typing L⊑L′)
      (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (closeᵀ M⊑M′ widening-pair
        p u-shape u′-shape square compatible) =
    quotient-widening-source-typing widening-pair
      (quotiented-nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (Λ⊑Λᵀ {ρ = ρ} {γ = γ} liftρ liftγ vV vV′ V⊑V′) =
    ⊢Λ vV
      (subst
        (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
        (leftCtxⁱ-lift liftγ)
        (subst
          (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
          (leftStoreⁱ-lift liftρ)
          (nu-term-imprecision-source-typing V⊑V′)))
  nu-term-imprecision-source-typing
      (Λ⊑ᵀ occ liftρ liftγ vV V⊑N′) =
    ⊢Λ vV
      (subst
        (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
        (leftCtxⁱ-lift-left liftγ)
        (subst
          (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
          (leftStoreⁱ-lift-left liftρ)
          (nu-term-imprecision-source-typing V⊑N′)))
  nu-term-imprecision-source-typing
      (target-instantiationᵀ embedded) =
    closed-refined-typing-recontextualize
      (typing-closedᵐ
        (forget (embedded-creation-source-typingᴱ embedded)))
      (embedded-creation-source-typingᴱ embedded)
  nu-term-imprecision-source-typing
      (α⊑αᵀ vL noL vL′ noL′ A⇑⊑B⇑ liftρ liftγ L⊑L′
        L•⊢ L′•⊢) =
    L•⊢
  nu-term-imprecision-source-typing
      (α⊑ᵀ vL noL h⇑A liftρ liftγ L⊑N′ L•⊢ N′⊢) =
    L•⊢
  nu-term-imprecision-source-typing
      (allocation-prefixᵀ prefix M⊑M′ M⊢ M′⊢) =
    M⊢
  nu-term-imprecision-source-typing
      (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
        liftρ liftγ N⊑N′ replace) =
    ⊢ν↑ hA (nu-term-imprecision-source-typing N⊑N′)
      (reveal-conversion-typing s↑)
  nu-term-imprecision-source-typing
      (ν⊑ᵀ hA h⇑A s↑ liftρ liftγ N⊑N′ replace) =
    ⊢ν↑ hA (nu-term-imprecision-source-typing N⊑N′)
      (reveal-conversion-typing s↑)
  nu-term-imprecision-source-typing κ⊑κᵀ =
    ⊢$ (κℕ _)
  nu-term-imprecision-source-typing (⊕⊑⊕ᵀ L⊑L′ M⊑M′) =
    ⊢⊕
      (nu-term-imprecision-source-typing L⊑L′)
      addℕ
      (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (gen⊑groundᵀ mode seal★ c⊒ gH vV vW W⊢ V⊑Wtag q) =
    ⊢⟨⟩⊒ mode seal★ c⊒
      (nu-term-imprecision-source-typing V⊑Wtag)
  nu-term-imprecision-source-typing
      (cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ q c-shape comp) =
    ⊢⟨⟩⊒ mode seal★ c⊒ (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q c-shape comp) =
    ⊢⟨⟩⊑ mode seal★ c⊑ (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (⊑cast⊒ᵀ mode′ seal★′ c′⊒ M⊑M′ q c-shape comp) =
    nu-term-imprecision-source-typing M⊑M′
  nu-term-imprecision-source-typing
      (⊑cast⊑ᵀ mode′ seal★′ c′⊑ M⊑M′ q c-shape comp) =
    nu-term-imprecision-source-typing M⊑M′
  nu-term-imprecision-source-typing
      (paired-revealᵀ x∈ c↑ c′↑ replace M⊑M′) =
    ⊢⟨⟩↑ (reveal-conversion-typing c↑)
      (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (paired-concealᵀ x∈ c↓ c′↓ replace M⊑M′) =
    ⊢⟨⟩↓ (conceal-conversion-typing c↓)
      (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (paired-wideningᵀ
        mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
        left right compat M⊑M′) =
    ⊢⟨⟩⊑ mode seal★ c⊑
      (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (conv↑⊑ᵀ c↑ M⊑M′ q replace) =
    ⊢⟨⟩↑ (reveal-conversion-typing c↑)
      (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (conv↓⊑ᵀ c↓ M⊑M′ q replace) =
    ⊢⟨⟩↓ (conceal-conversion-typing c↓)
      (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (⊑conv↑ᵀ c′↑ M⊑M′ q replace) =
    nu-term-imprecision-source-typing M⊑M′
  nu-term-imprecision-source-typing
      (⊑conv↓ᵀ c′↓ M⊑M′ q replace) =
    nu-term-imprecision-source-typing M⊑M′

  nu-term-imprecision-target-typing (blame⊑ᵀ M′⊢) =
    M′⊢
  nu-term-imprecision-target-typing (x⊑xᵀ x∈) =
    ⊢` (rightCtxⁱ-∋ x∈)
  nu-term-imprecision-target-typing (ƛ⊑ƛᵀ hA hA′ N⊑N′) =
    ⊢ƛ hA′ (nu-term-imprecision-target-typing N⊑N′)
  nu-term-imprecision-target-typing (·⊑·ᵀ L⊑L′ M⊑M′) =
    ⊢·
      (nu-term-imprecision-target-typing L⊑L′)
      (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (closeᵀ M⊑M′ widening-pair
        p u-shape u′-shape square compatible) =
    quotient-widening-target-typing widening-pair
      (quotiented-nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (Λ⊑Λᵀ {ρ = ρ} {γ = γ} liftρ liftγ vV vV′ V⊑V′) =
    ⊢Λ vV′
      (subst
        (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
        (rightCtxⁱ-lift liftγ)
        (subst
          (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
          (rightStoreⁱ-lift liftρ)
          (nu-term-imprecision-target-typing V⊑V′)))
  nu-term-imprecision-target-typing
      (Λ⊑ᵀ occ liftρ liftγ vV V⊑N′) =
    subst
      (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
      (rightCtxⁱ-lift-left liftγ)
      (subst
        (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
        (rightStoreⁱ-lift-left liftρ)
        (nu-term-imprecision-target-typing V⊑N′))
  nu-term-imprecision-target-typing
      (target-instantiationᵀ embedded) =
    closed-refined-typing-recontextualize
      (typing-closedᵐ
        (forget (embedded-creation-target-typingᴱ embedded)))
      (embedded-creation-target-typingᴱ embedded)
  nu-term-imprecision-target-typing
      (α⊑αᵀ vL noL vL′ noL′ A⇑⊑B⇑ liftρ liftγ L⊑L′
        L•⊢ L′•⊢) =
    L′•⊢
  nu-term-imprecision-target-typing
      (α⊑ᵀ vL noL h⇑A liftρ liftγ L⊑N′ L•⊢ N′⊢) =
    N′⊢
  nu-term-imprecision-target-typing
      (allocation-prefixᵀ prefix M⊑M′ M⊢ M′⊢) =
    M′⊢
  nu-term-imprecision-target-typing
      (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
        liftρ liftγ N⊑N′ replace) =
    ⊢ν↑ hA′ (nu-term-imprecision-target-typing N⊑N′)
      (reveal-conversion-typing s′↑)
  nu-term-imprecision-target-typing
      (ν⊑ᵀ hA h⇑A s↑ liftρ liftγ N⊑N′ replace) =
    nu-term-imprecision-target-typing N⊑N′
  nu-term-imprecision-target-typing κ⊑κᵀ =
    ⊢$ (κℕ _)
  nu-term-imprecision-target-typing (⊕⊑⊕ᵀ L⊑L′ M⊑M′) =
    ⊢⊕
      (nu-term-imprecision-target-typing L⊑L′)
      addℕ
      (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (gen⊑groundᵀ mode seal★ c⊒ gH vV vW W⊢ V⊑Wtag q) =
    W⊢
  nu-term-imprecision-target-typing
      (cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ q c-shape comp) =
    nu-term-imprecision-target-typing M⊑M′
  nu-term-imprecision-target-typing
      (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q c-shape comp) =
    nu-term-imprecision-target-typing M⊑M′
  nu-term-imprecision-target-typing
      (⊑cast⊒ᵀ mode′ seal★′ c′⊒ M⊑M′ q c-shape comp) =
    ⊢⟨⟩⊒ mode′ seal★′ c′⊒
      (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (⊑cast⊑ᵀ mode′ seal★′ c′⊑ M⊑M′ q c-shape comp) =
    ⊢⟨⟩⊑ mode′ seal★′ c′⊑
      (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (paired-revealᵀ x∈ c↑ c′↑ replace M⊑M′) =
    ⊢⟨⟩↑ (reveal-conversion-typing c′↑)
      (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (paired-concealᵀ x∈ c↓ c′↓ replace M⊑M′) =
    ⊢⟨⟩↓ (conceal-conversion-typing c′↓)
      (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (paired-wideningᵀ
        mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
        left right compat M⊑M′) =
    ⊢⟨⟩⊑ mode′ seal★′ c′⊑
      (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (conv↑⊑ᵀ c↑ M⊑M′ q replace) =
    nu-term-imprecision-target-typing M⊑M′
  nu-term-imprecision-target-typing
      (conv↓⊑ᵀ c↓ M⊑M′ q replace) =
    nu-term-imprecision-target-typing M⊑M′
  nu-term-imprecision-target-typing
      (⊑conv↑ᵀ c′↑ M⊑M′ q replace) =
    ⊢⟨⟩↑ (reveal-conversion-typing c′↑)
      (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (⊑conv↓ᵀ c′↓ M⊑M′ q replace) =
    ⊢⟨⟩↓ (conceal-conversion-typing c′↓)
      (nu-term-imprecision-target-typing M⊑M′)

  quotiented-nu-term-imprecision-source-typing
      (paired-downᵀ
        M⊑M′ mode d⊒ d-shape mode′ d′⊒ d′-shape square) =
    spine-source-cast-typing mode d⊒
      (nu-term-imprecision-source-typing M⊑M′)

  quotiented-nu-term-imprecision-target-typing
      (paired-downᵀ
        M⊑M′ mode d⊒ d-shape mode′ d′⊒ d′-shape square) =
    spine-source-cast-typing mode′ d′⊒
      (nu-term-imprecision-target-typing M⊑M′)


nu-term-imprecision-typing :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  (Δᴸ ∣ leftStoreⁱ ρ ∣ leftCtxⁱ γ ⊢ M ⦂ A) ×
  (Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M′ ⦂ B)
nu-term-imprecision-typing M⊑M′ =
  nu-term-imprecision-source-typing M⊑M′ ,
  nu-term-imprecision-target-typing M⊑M′
