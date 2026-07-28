module proof.Store.Prefix.NuImprecisionTermStorePrefixProof where

-- File Charter:
--   * Proves admissible relational-store prefix weakening mutually for the
--     live ordinary and quotient term-imprecision judgments.
--   * Rebuilds syntax-directed constructors after weakening store-indexed
--     coercions, conversions, correspondence, and binder lifts.
--   * Composes prefix lineage inside runtime-bullet and target-instantiation
--     residuals instead of adding an administrative term constructor.
--   * Contains no postulate, hole, catch-all, or permissive option.

open import Data.List using (_∷_; [])
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (refl; subst; sym)

open import Coercions using
  ( cast-tag
  ; tag-or-idᵈ
  )
open import Conversion using
  ( weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  ; ⊑-tgt-wf
  )
open import NarrowWiden using
  ( narrow-weaken
  ; widen-weaken
  )
import NarrowWiden
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
  ; rightCtxⁱ
  ; rightCtxⁱ-lift
  ; rightCtxⁱ-lift-left
  )
open import
  proof.NuCore.Relations.NuImprecisionQuotientedTyping
  using
  ( nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; quotiented-nu-term-imprecision-source-typing
  ; quotiented-nu-term-imprecision-target-typing
  )
open import NuTerms using (Term; _⟨_⟩; ν)
open import QuotientImprecisionCompatibility using
  ( SpineCastMode
  ; gradual↓
  ; id-only↓
  )
open import QuotientedTermImprecision
open import Store using (StoreIncl-cons)
open import TermTyping using
  ( cast-tag-or-id
  ; forget
  ; _∣_∣_⊢_⦂_
  ; ⊢ƛ
  ; ⊢·
  ; ⊢Λ
  ; ⊢ν↑
  ; ⊢ν⊑
  ; ⊢⊕
  ; ⊢⟨⟩↑
  ; ⊢⟨⟩↓
  ; ⊢⟨⟩⊒
  ; ⊢⟨⟩⊑
  )
open import proof.Core.Properties.NuTermProperties using
  (closed-refined-typing-recontextualize; typing-closedᵐ)
open import proof.Core.Properties.SealModeProperties using
  (seal★-tag-or-id)
open import proof.Core.Properties.StoreProperties using (renameStoreᵗ-incl)
open import proof.Core.Properties.TypePreservation using
  ( conversion↑-weaken
  ; conversion↓-weaken
  ; seal★-weaken
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  ; store-imp-prefix-transⁱ
  )
open import proof.Store.Prefix.NuImprecisionStorePrefixEvidenceDef using
  ( QuotientWideningPairPrefixᵀ
  ; StoreCorrespondsPrefixᵀ
  )
open import proof.Store.Prefix.NuImprecisionStorePrefixLiftDef using
  ( LeftStorePrefixLiftᵀ
  ; PairedStorePrefixLiftᵀ
  )
open import proof.Store.Prefix.NuImprecisionTermStorePrefixDef using
  ( QuotientTermImprecisionStorePrefixᵀ
  ; TermImprecisionStorePrefixᵀ
  )
open import
  proof.NuCore.Misc.NuImprecisionRuntimeBulletStoreStability
  using
  ( term-typing-prefix-left-align
  ; term-typing-prefix-right-align
  )
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using
  ( StoreImpPrefixᴿ
  ; prefix-creationᴱ
  ; prefix-reflᴿ
  ; prefix-∷ᴿ
  )
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using
  ( embedded-creation-source-typingᴱ
  ; embedded-creation-target-typingᴱ
  )
open import Types using (Ctx; Ty; TyCtx)


private
  to-creation-prefix :
    ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺} →
    StoreImpPrefix {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ⁺ →
    StoreImpPrefixᴿ ρ₀ ρ⁺
  to-creation-prefix prefix-reflⁱ = prefix-reflᴿ
  to-creation-prefix (prefix-∷ⁱ prefix) =
    prefix-∷ᴿ (to-creation-prefix prefix)

  spine-cast-mode-prefix :
    ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ μ} →
    StoreImpPrefix {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ⁺ →
    SpineCastMode (leftStoreⁱ ρ₀) μ →
    SpineCastMode (leftStoreⁱ ρ⁺) μ
  spine-cast-mode-prefix prefix id-only↓ = id-only↓
  spine-cast-mode-prefix prefix (gradual↓ mode seal★) =
    gradual↓ mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)

  target-spine-cast-mode-prefix :
    ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ μ} →
    StoreImpPrefix {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ⁺ →
    SpineCastMode (rightStoreⁱ ρ₀) μ →
    SpineCastMode (rightStoreⁱ ρ⁺) μ
  target-spine-cast-mode-prefix prefix id-only↓ = id-only↓
  target-spine-cast-mode-prefix prefix (gradual↓ mode seal★) =
    gradual↓ mode
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)

  right-cast-typing-prefix :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {Γ Γ⁺ : Ctx} {M : Term} {A⁺ B : Ty} {c} →
    StoreImpPrefix ρ₀ ρ⁺ →
    Δᴿ ∣ rightStoreⁱ ρ₀ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B →
    Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ Γ⁺ ⊢ M ⦂ A⁺ →
    Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B
  right-cast-typing-prefix prefix (⊢⟨⟩↑ c↑ M⊢) M⊢⁺ =
    ⊢⟨⟩↑
      (conversion↑-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c↑)
      (term-typing-prefix-right-align prefix M⊢ M⊢⁺)
  right-cast-typing-prefix prefix (⊢⟨⟩↓ c↓ M⊢) M⊢⁺ =
    ⊢⟨⟩↓
      (conversion↓-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c↓)
      (term-typing-prefix-right-align prefix M⊢ M⊢⁺)
  right-cast-typing-prefix prefix
      (⊢⟨⟩⊒ mode seal★ c⊒ M⊢) M⊢⁺ =
    ⊢⟨⟩⊒ mode
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c⊒)
      (term-typing-prefix-right-align prefix M⊢ M⊢⁺)
  right-cast-typing-prefix prefix
      (⊢⟨⟩⊑ mode seal★ c⊑ M⊢) M⊢⁺ =
    ⊢⟨⟩⊑ mode
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c⊑)
      (term-typing-prefix-right-align prefix M⊢ M⊢⁺)

  cast-body-typing :
    ∀ {Δ Σ Γ M B c} →
    Δ ∣ Σ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B →
    ∃[ A ] Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
  cast-body-typing (⊢⟨⟩↑ c↑ M⊢) = _ , M⊢
  cast-body-typing (⊢⟨⟩↓ c↓ M⊢) = _ , M⊢
  cast-body-typing (⊢⟨⟩⊒ mode seal★ c⊒ M⊢) = _ , M⊢
  cast-body-typing (⊢⟨⟩⊑ mode seal★ c⊑ M⊢) = _ , M⊢

  nu-body-typing :
    ∀ {Δ Σ Γ A L B c} →
    Δ ∣ Σ ∣ Γ ⊢ ν A L c ⦂ B →
    ∃[ C ] Δ ∣ Σ ∣ Γ ⊢ L ⦂ C
  nu-body-typing (⊢ν↑ hA L⊢ c↑) = _ , L⊢
  nu-body-typing (⊢ν⊑ mode seal★ L⊢ c⊑) = _ , L⊢


module _
    (store-corresponds-prefix : StoreCorrespondsPrefixᵀ)
    (quotient-widening-pair-prefix : QuotientWideningPairPrefixᵀ)
    (paired-store-prefix-lift : PairedStorePrefixLiftᵀ)
    (left-store-prefix-lift : LeftStorePrefixLiftᵀ)
  where

  align-sourceᵀ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {M M′ : Term} {A B A⁺ : Ty} {Γ⁺ : Ctx}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ Γ⁺ ⊢ M ⦂ A⁺ →
    Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ leftCtxⁱ γ ⊢ M ⦂ A
  align-sourceᵀ prefix M⊑M′ M⊢ =
    term-typing-prefix-left-align prefix
      (nu-term-imprecision-source-typing M⊑M′) M⊢

  align-targetᵀ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {M M′ : Term} {A B B⁺ : Ty} {Γ⁺ : Ctx}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ Γ⁺ ⊢ M′ ⦂ B⁺ →
    Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ rightCtxⁱ γ ⊢ M′ ⦂ B
  align-targetᵀ prefix M⊑M′ M′⊢ =
    term-typing-prefix-right-align prefix
      (nu-term-imprecision-target-typing M⊑M′) M′⊢

  align-quotient-sourceᵀ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {M M′ : Term} {D D′ D⁺ : Ty} {Γ⁺ : Ctx}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
      ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
    Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ Γ⁺ ⊢ M ⦂ D⁺ →
    Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ leftCtxⁱ γ ⊢ M ⦂ D
  align-quotient-sourceᵀ prefix M⊑M′ M⊢ =
    term-typing-prefix-left-align prefix
      (quotiented-nu-term-imprecision-source-typing M⊑M′) M⊢

  align-quotient-targetᵀ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {M M′ : Term} {D D′ D′⁺ : Ty} {Γ⁺ : Ctx}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
      ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
    Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ Γ⁺ ⊢ M′ ⦂ D′⁺ →
    Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ rightCtxⁱ γ ⊢ M′ ⦂ D′
  align-quotient-targetᵀ prefix M⊑M′ M′⊢ =
    term-typing-prefix-right-align prefix
      (quotiented-nu-term-imprecision-target-typing M⊑M′) M′⊢

  mutual
    term-imprecision-store-prefix-proofᵀ :
      TermImprecisionStorePrefixᵀ

    quotient-term-imprecision-store-prefix-proofᵀ :
      QuotientTermImprecisionStorePrefixᵀ

    term-imprecision-store-prefix-alignᵀ :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {γ : CtxImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {A B A⁺ B⁺ : Ty} {Γᴸ⁺ Γᴿ⁺ : Ctx}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
      Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ Γᴸ⁺ ⊢ M ⦂ A⁺ →
      Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ Γᴿ⁺ ⊢ M′ ⦂ B⁺ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ γ
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p

    quotient-term-imprecision-store-prefix-alignᵀ :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {γ : CtxImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {D D′ D⁺ D′⁺ : Ty} {Γᴸ⁺ Γᴿ⁺ : Ctx}
        {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
        ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
      Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ Γᴸ⁺ ⊢ M ⦂ D⁺ →
      Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ Γᴿ⁺ ⊢ M′ ⦂ D′⁺ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ γ
        ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q

    term-imprecision-store-prefix-goᵀ :
      TermImprecisionStorePrefixᵀ

    quotient-term-imprecision-store-prefix-goᵀ :
      QuotientTermImprecisionStorePrefixᵀ

    term-imprecision-store-prefix-proofᵀ prefix M⊑M′ M⊢ M′⊢ =
      term-imprecision-store-prefix-alignᵀ prefix M⊑M′ M⊢ M′⊢

    quotient-term-imprecision-store-prefix-proofᵀ prefix M⊑M′ M⊢ M′⊢ =
      quotient-term-imprecision-store-prefix-alignᵀ
        prefix M⊑M′ M⊢ M′⊢

    term-imprecision-store-prefix-alignᵀ prefix M⊑M′ M⊢ M′⊢ =
      term-imprecision-store-prefix-goᵀ prefix M⊑M′
        (align-sourceᵀ prefix M⊑M′ M⊢)
        (align-targetᵀ prefix M⊑M′ M′⊢)

    quotient-term-imprecision-store-prefix-alignᵀ
        prefix M⊑M′ M⊢ M′⊢ =
      quotient-term-imprecision-store-prefix-goᵀ prefix M⊑M′
        (align-quotient-sourceᵀ prefix M⊑M′ M⊢)
        (align-quotient-targetᵀ prefix M⊑M′ M′⊢)

    term-imprecision-store-prefix-goᵀ
        prefix (blame⊑ᵀ M′⊢₀) M⊢ M′⊢ =
      blame⊑ᵀ M′⊢

    term-imprecision-store-prefix-goᵀ
        prefix (x⊑xᵀ x∈) M⊢ M′⊢ =
      x⊑xᵀ x∈

    term-imprecision-store-prefix-goᵀ
        prefix (ƛ⊑ƛᵀ hA hA′ N⊑N′)
        (⊢ƛ hA⁺ N⊢) (⊢ƛ hA′⁺ N′⊢) =
      ƛ⊑ƛᵀ hA hA′
        (term-imprecision-store-prefix-alignᵀ
          prefix N⊑N′ N⊢ N′⊢)

    term-imprecision-store-prefix-goᵀ
        prefix (·⊑·ᵀ L⊑L′ M⊑M′)
        (⊢· L⊢ M⊢) (⊢· L′⊢ M′⊢) =
      ·⊑·ᵀ
        (term-imprecision-store-prefix-alignᵀ
          prefix L⊑L′ L⊢ L′⊢)
        (term-imprecision-store-prefix-alignᵀ
          prefix M⊑M′ M⊢ M′⊢)

    term-imprecision-store-prefix-goᵀ
        prefix
        (closeᵀ N⊑N′ widening-pair p
          u-shape u′-shape square compatible)
        M⊢ M′⊢
        with cast-body-typing M⊢ | cast-body-typing M′⊢
    term-imprecision-store-prefix-goᵀ
        prefix
        (closeᵀ N⊑N′ widening-pair p
          u-shape u′-shape square compatible)
        M⊢ M′⊢
        | D⁺ , N⊢ | D′⁺ , N′⊢ =
      closeᵀ
        (quotient-term-imprecision-store-prefix-alignᵀ
          prefix N⊑N′ N⊢ N′⊢)
        (quotient-widening-pair-prefix prefix widening-pair)
        p u-shape u′-shape square compatible

    term-imprecision-store-prefix-goᵀ
        prefix
        (Λ⊑Λᵀ liftρ liftγ vV vV′ V⊑V′)
        (⊢Λ vV⁺ V⊢) (⊢Λ vV′⁺ V′⊢)
        with paired-store-prefix-lift prefix liftρ
    term-imprecision-store-prefix-goᵀ
        prefix
        (Λ⊑Λᵀ liftρ liftγ vV vV′ V⊑V′)
        (⊢Λ vV⁺ V⊢) (⊢Λ vV′⁺ V′⊢)
        | ρ⁺↑ , liftρ⁺ , prefix↑ =
      Λ⊑Λᵀ liftρ⁺ liftγ vV vV′
        (term-imprecision-store-prefix-alignᵀ
          prefix↑ V⊑V′
          (subst
            (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
            (sym (leftStoreⁱ-lift liftρ⁺))
            (subst
              (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
              (sym (leftCtxⁱ-lift liftγ))
              V⊢))
          (subst
            (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
            (sym (rightStoreⁱ-lift liftρ⁺))
            (subst
              (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
              (sym (rightCtxⁱ-lift liftγ))
              V′⊢)))

    term-imprecision-store-prefix-goᵀ
        prefix
        (Λ⊑ᵀ occ liftρ liftγ vV V⊑N′)
        (⊢Λ vV⁺ V⊢) N′⊢
        with left-store-prefix-lift prefix liftρ
    term-imprecision-store-prefix-goᵀ
        prefix
        (Λ⊑ᵀ occ liftρ liftγ vV V⊑N′)
        (⊢Λ vV⁺ V⊢) N′⊢
        | ρ⁺↑ , liftρ⁺ , prefix↑ =
      Λ⊑ᵀ occ liftρ⁺ liftγ vV
        (term-imprecision-store-prefix-alignᵀ
          prefix↑ V⊑N′
          (subst
            (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
            (sym (leftStoreⁱ-lift-left liftρ⁺))
            (subst
              (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
              (sym (leftCtxⁱ-lift-left liftγ))
              V⊢))
          (subst
            (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
            (sym (rightStoreⁱ-lift-left liftρ⁺))
            (subst
              (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
              (sym (rightCtxⁱ-lift-left liftγ))
              N′⊢)))

    term-imprecision-store-prefix-goᵀ
        prefix (target-instantiationᵀ embedded) M⊢ M′⊢ =
      target-instantiationᵀ
        (prefix-creationᴱ embedded (to-creation-prefix prefix)
          (closed-refined-typing-recontextualize
            {Γ′ = []}
            (typing-closedᵐ
              (forget (embedded-creation-source-typingᴱ embedded)))
            M⊢)
          (closed-refined-typing-recontextualize
            {Γ′ = []}
            (typing-closedᵐ
              (forget (embedded-creation-target-typingᴱ embedded)))
            M′⊢))

    term-imprecision-store-prefix-goᵀ
        prefix
        (α⊑αᵀ vL noL vL′ noL′ A⇑⊑B⇑ liftρ liftγ L⊑L′
          allocation-prefix L•⊢ L′•⊢)
        L•⊢⁺ L′•⊢⁺ =
      α⊑αᵀ vL noL vL′ noL′ A⇑⊑B⇑ liftρ liftγ L⊑L′
        (store-imp-prefix-transⁱ allocation-prefix prefix)
        L•⊢⁺ L′•⊢⁺

    term-imprecision-store-prefix-goᵀ
        prefix
        (α⊑ᵀ vL noL h⇑A liftρ liftγ L⊑N′
          allocation-prefix L•⊢ N′⊢)
        L•⊢⁺ N′⊢⁺ =
      α⊑ᵀ vL noL h⇑A liftρ liftγ L⊑N′
        (store-imp-prefix-transⁱ allocation-prefix prefix)
        L•⊢⁺ N′⊢⁺

    term-imprecision-store-prefix-goᵀ
        prefix
        (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
          liftρ liftγ N⊑N′ replace)
        M⊢ M′⊢
        with nu-body-typing M⊢ | nu-body-typing M′⊢
           | paired-store-prefix-lift prefix liftρ
    term-imprecision-store-prefix-goᵀ
        prefix
        (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
          liftρ liftγ N⊑N′ replace)
        M⊢ M′⊢
        | C⁺ , N⊢ | C′⁺ , N′⊢ | ρ⁺↑ , liftρ⁺ , prefix↑ =
      ν⊑νᵀ hA hA′
        (weaken-reveal-conversion
          (StoreIncl-cons
            (renameStoreᵗ-incl suc
              (leftStoreⁱ-prefix-inclusion prefix)))
          s↑)
        (weaken-reveal-conversion
          (StoreIncl-cons
            (renameStoreᵗ-incl suc
              (rightStoreⁱ-prefix-inclusion prefix)))
          s′↑)
        A⊑A′ A⇑⊑A′⇑ liftρ⁺ liftγ
        (term-imprecision-store-prefix-alignᵀ
          prefix N⊑N′ N⊢ N′⊢)
        replace

    term-imprecision-store-prefix-goᵀ
        prefix
        (ν⊑ᵀ hA h⇑A s↑ liftρ liftγ N⊑N′ replace)
        M⊢ N′⊢
        with nu-body-typing M⊢
           | left-store-prefix-lift prefix liftρ
    term-imprecision-store-prefix-goᵀ
        prefix
        (ν⊑ᵀ hA h⇑A s↑ liftρ liftγ N⊑N′ replace)
        M⊢ N′⊢
        | C⁺ , N⊢ | ρ⁺↑ , liftρ⁺ , prefix↑ =
      ν⊑ᵀ hA h⇑A
        (weaken-reveal-conversion
          (StoreIncl-cons
            (renameStoreᵗ-incl suc
              (leftStoreⁱ-prefix-inclusion prefix)))
          s↑)
        liftρ⁺ liftγ
        (term-imprecision-store-prefix-alignᵀ
          prefix N⊑N′ N⊢ N′⊢)
        replace

    term-imprecision-store-prefix-goᵀ
        prefix κ⊑κᵀ M⊢ M′⊢ =
      κ⊑κᵀ

    term-imprecision-store-prefix-goᵀ
        prefix (⊕⊑⊕ᵀ L⊑L′ M⊑M′)
        (⊢⊕ L⊢ op M⊢) (⊢⊕ L′⊢ op′ M′⊢) =
      ⊕⊑⊕ᵀ
        (term-imprecision-store-prefix-alignᵀ
          prefix L⊑L′ L⊢ L′⊢)
        (term-imprecision-store-prefix-alignᵀ
          prefix M⊑M′ M⊢ M′⊢)

    term-imprecision-store-prefix-goᵀ
        prefix
        (gen⊑groundᵀ mode seal★ c⊒ gH vV vW W⊢₀ V⊑Wtag q)
        M⊢ W⊢
        with cast-body-typing M⊢
    term-imprecision-store-prefix-goᵀ
        prefix
        (gen⊑groundᵀ mode seal★ c⊒ gH vV vW W⊢₀ V⊑Wtag q)
        M⊢ W⊢
        | A⁺ , V⊢ =
      gen⊑groundᵀ
        mode
        (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
        (narrow-weaken ≤-refl
          (leftStoreⁱ-prefix-inclusion prefix) c⊒)
        gH vV vW W⊢
        (term-imprecision-store-prefix-alignᵀ
          prefix V⊑Wtag V⊢
          (right-cast-typing-prefix prefix
            (nu-term-imprecision-target-typing V⊑Wtag) W⊢))
        q

    term-imprecision-store-prefix-goᵀ
        prefix
        (cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ q c-shape comp)
        L⊢ M′⊢
        with cast-body-typing L⊢
    term-imprecision-store-prefix-goᵀ
        prefix
        (cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ q c-shape comp)
        L⊢ M′⊢
        | A⁺ , M⊢ =
      cast⊒⊑ᵀ mode
        (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
        (narrow-weaken ≤-refl
          (leftStoreⁱ-prefix-inclusion prefix) c⊒)
        (term-imprecision-store-prefix-alignᵀ
          prefix M⊑M′ M⊢ M′⊢)
        q c-shape comp

    term-imprecision-store-prefix-goᵀ
        prefix
        (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q c-shape comp)
        L⊢ M′⊢
        with cast-body-typing L⊢
    term-imprecision-store-prefix-goᵀ
        prefix
        (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q c-shape comp)
        L⊢ M′⊢
        | A⁺ , M⊢ =
      cast⊑⊑ᵀ mode
        (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
        (widen-weaken ≤-refl
          (leftStoreⁱ-prefix-inclusion prefix) c⊑)
        (term-imprecision-store-prefix-alignᵀ
          prefix M⊑M′ M⊢ M′⊢)
        q c-shape comp

    term-imprecision-store-prefix-goᵀ
        prefix
        (⊑cast⊒ᵀ mode′ seal★′ c′⊒ M⊑M′ q c-shape comp)
        M⊢ L′⊢
        with cast-body-typing L′⊢
    term-imprecision-store-prefix-goᵀ
        prefix
        (⊑cast⊒ᵀ mode′ seal★′ c′⊒ M⊑M′ q c-shape comp)
        M⊢ L′⊢
        | B′⁺ , M′⊢ =
      ⊑cast⊒ᵀ mode′
        (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★′)
        (narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) c′⊒)
        (term-imprecision-store-prefix-alignᵀ
          prefix M⊑M′ M⊢ M′⊢)
        q c-shape comp

    term-imprecision-store-prefix-goᵀ
        prefix
        (⊑cast⊑ᵀ mode′ seal★′ c′⊑ M⊑M′ q c-shape comp)
        M⊢ L′⊢
        with cast-body-typing L′⊢
    term-imprecision-store-prefix-goᵀ
        prefix
        (⊑cast⊑ᵀ mode′ seal★′ c′⊑ M⊑M′ q c-shape comp)
        M⊢ L′⊢
        | B′⁺ , M′⊢ =
      ⊑cast⊑ᵀ mode′
        (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★′)
        (widen-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) c′⊑)
        (term-imprecision-store-prefix-alignᵀ
          prefix M⊑M′ M⊢ M′⊢)
        q c-shape comp

    term-imprecision-store-prefix-goᵀ
        prefix (conv↑⊑ᵀ c↑ M⊑M′ q replace)
        L⊢ M′⊢
        with cast-body-typing L⊢
    term-imprecision-store-prefix-goᵀ
        prefix (conv↑⊑ᵀ c↑ M⊑M′ q replace)
        L⊢ M′⊢
        | A⁺ , M⊢ =
      conv↑⊑ᵀ
        (weaken-reveal-conversion
          (leftStoreⁱ-prefix-inclusion prefix) c↑)
        (term-imprecision-store-prefix-alignᵀ
          prefix M⊑M′ M⊢ M′⊢)
        q replace

    term-imprecision-store-prefix-goᵀ
        prefix (conv↓⊑ᵀ c↓ M⊑M′ q replace)
        L⊢ M′⊢
        with cast-body-typing L⊢
    term-imprecision-store-prefix-goᵀ
        prefix (conv↓⊑ᵀ c↓ M⊑M′ q replace)
        L⊢ M′⊢
        | A⁺ , M⊢ =
      conv↓⊑ᵀ
        (weaken-conceal-conversion
          (leftStoreⁱ-prefix-inclusion prefix) c↓)
        (term-imprecision-store-prefix-alignᵀ
          prefix M⊑M′ M⊢ M′⊢)
        q replace

    term-imprecision-store-prefix-goᵀ
        prefix (⊑conv↑ᵀ c′↑ M⊑M′ q replace)
        M⊢ L′⊢
        with cast-body-typing L′⊢
    term-imprecision-store-prefix-goᵀ
        prefix (⊑conv↑ᵀ c′↑ M⊑M′ q replace)
        M⊢ L′⊢
        | B′⁺ , M′⊢ =
      ⊑conv↑ᵀ
        (weaken-reveal-conversion
          (rightStoreⁱ-prefix-inclusion prefix) c′↑)
        (term-imprecision-store-prefix-alignᵀ
          prefix M⊑M′ M⊢ M′⊢)
        q replace

    term-imprecision-store-prefix-goᵀ
        prefix (⊑conv↓ᵀ c′↓ M⊑M′ q replace)
        M⊢ L′⊢
        with cast-body-typing L′⊢
    term-imprecision-store-prefix-goᵀ
        prefix (⊑conv↓ᵀ c′↓ M⊑M′ q replace)
        M⊢ L′⊢
        | B′⁺ , M′⊢ =
      ⊑conv↓ᵀ
        (weaken-conceal-conversion
          (rightStoreⁱ-prefix-inclusion prefix) c′↓)
        (term-imprecision-store-prefix-alignᵀ
          prefix M⊑M′ M⊢ M′⊢)
        q replace

    term-imprecision-store-prefix-goᵀ
        prefix (paired-revealᵀ corresponds c↑ c′↑ replace M⊑M′)
        L⊢ L′⊢
        with cast-body-typing L⊢ | cast-body-typing L′⊢
    term-imprecision-store-prefix-goᵀ
        prefix (paired-revealᵀ corresponds c↑ c′↑ replace M⊑M′)
        L⊢ L′⊢
        | A⁺ , M⊢ | B′⁺ , M′⊢ =
      paired-revealᵀ
        (store-corresponds-prefix prefix corresponds)
        (weaken-reveal-conversion
          (leftStoreⁱ-prefix-inclusion prefix) c↑)
        (weaken-reveal-conversion
          (rightStoreⁱ-prefix-inclusion prefix) c′↑)
        replace
        (term-imprecision-store-prefix-alignᵀ
          prefix M⊑M′ M⊢ M′⊢)

    term-imprecision-store-prefix-goᵀ
        prefix (paired-concealᵀ corresponds c↓ c′↓ replace M⊑M′)
        L⊢ L′⊢
        with cast-body-typing L⊢ | cast-body-typing L′⊢
    term-imprecision-store-prefix-goᵀ
        prefix (paired-concealᵀ corresponds c↓ c′↓ replace M⊑M′)
        L⊢ L′⊢
        | A⁺ , M⊢ | B′⁺ , M′⊢ =
      paired-concealᵀ
        (store-corresponds-prefix prefix corresponds)
        (weaken-conceal-conversion
          (leftStoreⁱ-prefix-inclusion prefix) c↓)
        (weaken-conceal-conversion
          (rightStoreⁱ-prefix-inclusion prefix) c′↓)
        replace
        (term-imprecision-store-prefix-alignᵀ
          prefix M⊑M′ M⊢ M′⊢)

    term-imprecision-store-prefix-goᵀ
        prefix
        (paired-wideningᵀ
          mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
          left right compatible M⊑M′)
        L⊢ L′⊢
        with cast-body-typing L⊢ | cast-body-typing L′⊢
    term-imprecision-store-prefix-goᵀ
        prefix
        (paired-wideningᵀ
          mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
          left right compatible M⊑M′)
        L⊢ L′⊢
        | A⁺ , M⊢ | B′⁺ , M′⊢ =
      paired-wideningᵀ
        mode
        (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
        (widen-weaken ≤-refl
          (leftStoreⁱ-prefix-inclusion prefix) c⊑)
        c-shape
        mode′
        (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★′)
        (widen-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) c′⊑)
        c′-shape left right compatible
        (term-imprecision-store-prefix-alignᵀ
          prefix M⊑M′ M⊢ M′⊢)

    quotient-term-imprecision-store-prefix-goᵀ
        prefix
        (paired-downᵀ
          M⊑M′ source-mode source source-shape
          target-mode target target-shape square elimination)
        L⊢ L′⊢
        with cast-body-typing L⊢ | cast-body-typing L′⊢
    quotient-term-imprecision-store-prefix-goᵀ
        prefix
        (paired-downᵀ
          M⊑M′ source-mode source source-shape
          target-mode target target-shape square elimination)
        L⊢ L′⊢
        | D⁺ , M⊢ | D′⁺ , M′⊢ =
      paired-downᵀ
        (term-imprecision-store-prefix-alignᵀ
          prefix M⊑M′ M⊢ M′⊢)
        (spine-cast-mode-prefix prefix source-mode)
        (narrow-weaken ≤-refl
          (leftStoreⁱ-prefix-inclusion prefix) source)
        source-shape
        (target-spine-cast-mode-prefix prefix target-mode)
        (narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) target)
        target-shape square elimination
