module
  proof.Quotient.NuImprecisionReductionClosedQuotientStorePrefixExperiment
  where

-- File Charter:
--   * Proves admissible relational-store prefix weakening mutually for the
--     independent ordinary and quotient prototype judgments.
--   * Keeps the prototype syntax-directed while preserving allocation
--     lineage in runtime bullets and target-instantiation residuals.
--   * Reuses the canonical live store-prefix support for projected stores,
--     evidence, and binder lifts, but does not use the live term relation.
--   * Contains no postulate, hole, catch-all, or permissive option.

open import Data.List using (_∷_; [])
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (refl; subst; sym)

open import Coercions using (cast-tag; tag-or-idᵈ)
open import Conversion using
  ( weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
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
open import NuTerms using (Term; _⟨_⟩; ν)
open import QuotientImprecisionCompatibility using
  (SpineCastMode; gradual↓; id-only↓)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  )
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
open import proof.Core.Properties.StoreProperties using
  (renameStoreᵗ-incl)
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
open import proof.Store.Prefix.NuImprecisionStorePrefixEvidenceProof using
  (store-corresponds-prefix-proofᵀ)
open import proof.Store.Prefix.NuImprecisionStorePrefixLiftLemma using
  ( left-store-prefix-liftᵀ
  ; paired-store-prefix-liftᵀ
  )
open import
  proof.NuCore.Misc.NuImprecisionRuntimeBulletStoreStability
  using
  ( term-typing-prefix-left-align
  ; term-typing-prefix-right-align
  )
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientTypingExperiment
  using
  ( smaller-imprecision-source-typingᴿ
  ; smaller-imprecision-target-typingᴿ
  ; smaller-quotient-source-typingᴿ
  ; smaller-quotient-target-typingᴿ
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
  to-live-prefix :
    ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺} →
    StoreImpPrefixᴿ {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ⁺ →
    StoreImpPrefix ρ₀ ρ⁺
  to-live-prefix prefix-reflᴿ = prefix-reflⁱ
  to-live-prefix (prefix-∷ᴿ prefix) =
    prefix-∷ⁱ (to-live-prefix prefix)

  to-prototype-prefix :
    ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺} →
    StoreImpPrefix {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ⁺ →
    StoreImpPrefixᴿ ρ₀ ρ⁺
  to-prototype-prefix prefix-reflⁱ = prefix-reflᴿ
  to-prototype-prefix (prefix-∷ⁱ prefix) =
    prefix-∷ᴿ (to-prototype-prefix prefix)

  store-imp-prefix-transᴿ :
    ∀ {Φ Δᴸ Δᴿ ρ₀ ρ₁ ρ₂} →
    StoreImpPrefixᴿ {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ₁ →
    StoreImpPrefixᴿ ρ₁ ρ₂ →
    StoreImpPrefixᴿ ρ₀ ρ₂
  store-imp-prefix-transᴿ prefix₀ prefix₁ =
    to-prototype-prefix
      (store-imp-prefix-transⁱ
        (to-live-prefix prefix₀)
        (to-live-prefix prefix₁))

  spine-cast-mode-prefixᴿ :
    ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ μ} →
    StoreImpPrefixᴿ {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ⁺ →
    SpineCastMode (leftStoreⁱ ρ₀) μ →
    SpineCastMode (leftStoreⁱ ρ⁺) μ
  spine-cast-mode-prefixᴿ prefix id-only↓ = id-only↓
  spine-cast-mode-prefixᴿ prefix (gradual↓ mode seal★) =
    gradual↓ mode
      (seal★-weaken
        (leftStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        seal★)

  target-spine-cast-mode-prefixᴿ :
    ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ μ} →
    StoreImpPrefixᴿ {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ⁺ →
    SpineCastMode (rightStoreⁱ ρ₀) μ →
    SpineCastMode (rightStoreⁱ ρ⁺) μ
  target-spine-cast-mode-prefixᴿ prefix id-only↓ = id-only↓
  target-spine-cast-mode-prefixᴿ prefix (gradual↓ mode seal★) =
    gradual↓ mode
      (seal★-weaken
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        seal★)

  right-cast-typing-prefixᴿ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {Γ Γ⁺ : Ctx} {M : Term} {A⁺ B : Ty} {c} →
    StoreImpPrefixᴿ ρ₀ ρ⁺ →
    Δᴿ ∣ rightStoreⁱ ρ₀ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B →
    Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ Γ⁺ ⊢ M ⦂ A⁺ →
    Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B
  right-cast-typing-prefixᴿ prefix (⊢⟨⟩↑ c↑ M⊢) M⊢⁺ =
    ⊢⟨⟩↑
      (conversion↑-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix)) c↑)
      (term-typing-prefix-right-align
        (to-live-prefix prefix) M⊢ M⊢⁺)
  right-cast-typing-prefixᴿ prefix (⊢⟨⟩↓ c↓ M⊢) M⊢⁺ =
    ⊢⟨⟩↓
      (conversion↓-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix)) c↓)
      (term-typing-prefix-right-align
        (to-live-prefix prefix) M⊢ M⊢⁺)
  right-cast-typing-prefixᴿ prefix
      (⊢⟨⟩⊒ mode seal★ c⊒ M⊢) M⊢⁺ =
    ⊢⟨⟩⊒ mode
      (seal★-weaken
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        seal★)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        c⊒)
      (term-typing-prefix-right-align
        (to-live-prefix prefix) M⊢ M⊢⁺)
  right-cast-typing-prefixᴿ prefix
      (⊢⟨⟩⊑ mode seal★ c⊑ M⊢) M⊢⁺ =
    ⊢⟨⟩⊑ mode
      (seal★-weaken
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        seal★)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        c⊑)
      (term-typing-prefix-right-align
        (to-live-prefix prefix) M⊢ M⊢⁺)

  cast-body-typingᴿ :
    ∀ {Δ Σ Γ M B c} →
    Δ ∣ Σ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B →
    ∃[ A ] Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
  cast-body-typingᴿ (⊢⟨⟩↑ c↑ M⊢) = _ , M⊢
  cast-body-typingᴿ (⊢⟨⟩↓ c↓ M⊢) = _ , M⊢
  cast-body-typingᴿ (⊢⟨⟩⊒ mode seal★ c⊒ M⊢) = _ , M⊢
  cast-body-typingᴿ (⊢⟨⟩⊑ mode seal★ c⊑ M⊢) = _ , M⊢

  nu-body-typingᴿ :
    ∀ {Δ Σ Γ A L B c} →
    Δ ∣ Σ ∣ Γ ⊢ ν A L c ⦂ B →
    ∃[ C ] Δ ∣ Σ ∣ Γ ⊢ L ⦂ C
  nu-body-typingᴿ (⊢ν↑ hA L⊢ c↑) = _ , L⊢
  nu-body-typingᴿ (⊢ν⊑ mode seal★ L⊢ c⊑) = _ , L⊢


TermImprecisionStorePrefixᴿ : Set₁
TermImprecisionStorePrefixᴿ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefixᴿ ρ₀ ρ⁺ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ leftCtxⁱ γ ⊢ M ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ rightCtxⁱ γ ⊢ M′ ⦂ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ γ
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p


QuotientTermImprecisionStorePrefixᴿ : Set₁
QuotientTermImprecisionStorePrefixᴿ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {D D′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
  StoreImpPrefixᴿ ρ₀ ρ⁺ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
    ⊢ᴿᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ leftCtxⁱ γ ⊢ M ⦂ D →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ rightCtxⁱ γ ⊢ M′ ⦂ D′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ γ
    ⊢ᴿᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q


private
  align-sourceᴿ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {M M′ : Term} {A B A⁺ : Ty} {Γ⁺ : Ctx}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    StoreImpPrefixᴿ ρ₀ ρ⁺ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
      ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ Γ⁺ ⊢ M ⦂ A⁺ →
    Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ leftCtxⁱ γ ⊢ M ⦂ A
  align-sourceᴿ prefix M⊑M′ M⊢ =
    term-typing-prefix-left-align (to-live-prefix prefix)
      (smaller-imprecision-source-typingᴿ M⊑M′) M⊢

  align-targetᴿ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {M M′ : Term} {A B B⁺ : Ty} {Γ⁺ : Ctx}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    StoreImpPrefixᴿ ρ₀ ρ⁺ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
      ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ Γ⁺ ⊢ M′ ⦂ B⁺ →
    Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ rightCtxⁱ γ ⊢ M′ ⦂ B
  align-targetᴿ prefix M⊑M′ M′⊢ =
    term-typing-prefix-right-align (to-live-prefix prefix)
      (smaller-imprecision-target-typingᴿ M⊑M′) M′⊢

  align-quotient-sourceᴿ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {M M′ : Term} {D D′ D⁺ : Ty} {Γ⁺ : Ctx}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
    StoreImpPrefixᴿ ρ₀ ρ⁺ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
      ⊢ᴿᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
    Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ Γ⁺ ⊢ M ⦂ D⁺ →
    Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ leftCtxⁱ γ ⊢ M ⦂ D
  align-quotient-sourceᴿ prefix M⊑M′ M⊢ =
    term-typing-prefix-left-align (to-live-prefix prefix)
      (smaller-quotient-source-typingᴿ M⊑M′) M⊢

  align-quotient-targetᴿ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {M M′ : Term} {D D′ D′⁺ : Ty} {Γ⁺ : Ctx}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
    StoreImpPrefixᴿ ρ₀ ρ⁺ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
      ⊢ᴿᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
    Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ Γ⁺ ⊢ M′ ⦂ D′⁺ →
    Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ rightCtxⁱ γ ⊢ M′ ⦂ D′
  align-quotient-targetᴿ prefix M⊑M′ M′⊢ =
    term-typing-prefix-right-align (to-live-prefix prefix)
      (smaller-quotient-target-typingᴿ M⊑M′) M′⊢

  quotient-widening-pair-prefixᴿ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {u u′} {D D′ A A′ : Ty} →
    StoreImpPrefixᴿ ρ₀ ρ⁺ →
    QuotientWideningPairᴿ Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
    QuotientWideningPairᴿ Δᴸ Δᴿ ρ⁺ u u′ D D′ A A′
  quotient-widening-pair-prefixᴿ prefix
      (quotient-id-wideningᴿ source target) =
    quotient-id-wideningᴿ
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        source)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        target)
  quotient-widening-pair-prefixᴿ prefix
      (quotient-cast-wideningᴿ
        mode seal★ source mode′ seal★′ target) =
    quotient-cast-wideningᴿ
      mode
      (seal★-weaken
        (leftStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        seal★)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        source)
      mode′
      (seal★-weaken
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        seal★′)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        target)


mutual
  term-imprecision-store-prefixᴿ :
    TermImprecisionStorePrefixᴿ

  quotient-term-imprecision-store-prefixᴿ :
    QuotientTermImprecisionStorePrefixᴿ

  term-imprecision-store-prefix-alignᴿ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {M M′ : Term} {A B A⁺ B⁺ : Ty} {Γᴸ⁺ Γᴿ⁺ : Ctx}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    StoreImpPrefixᴿ ρ₀ ρ⁺ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
      ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ Γᴸ⁺ ⊢ M ⦂ A⁺ →
    Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ Γᴿ⁺ ⊢ M′ ⦂ B⁺ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ γ
      ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p

  quotient-term-imprecision-store-prefix-alignᴿ :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {γ : CtxImp Φ Δᴸ Δᴿ}
      {M M′ : Term} {D D′ D⁺ D′⁺ : Ty} {Γᴸ⁺ Γᴿ⁺ : Ctx}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
    StoreImpPrefixᴿ ρ₀ ρ⁺ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
      ⊢ᴿᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
    Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ Γᴸ⁺ ⊢ M ⦂ D⁺ →
    Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ Γᴿ⁺ ⊢ M′ ⦂ D′⁺ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ γ
      ⊢ᴿᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q

  term-imprecision-store-prefix-goᴿ :
    TermImprecisionStorePrefixᴿ

  quotient-term-imprecision-store-prefix-goᴿ :
    QuotientTermImprecisionStorePrefixᴿ

  term-imprecision-store-prefixᴿ prefix M⊑M′ M⊢ M′⊢ =
    term-imprecision-store-prefix-alignᴿ prefix M⊑M′ M⊢ M′⊢

  quotient-term-imprecision-store-prefixᴿ prefix M⊑M′ M⊢ M′⊢ =
    quotient-term-imprecision-store-prefix-alignᴿ
      prefix M⊑M′ M⊢ M′⊢

  term-imprecision-store-prefix-alignᴿ prefix M⊑M′ M⊢ M′⊢ =
    term-imprecision-store-prefix-goᴿ prefix M⊑M′
      (align-sourceᴿ prefix M⊑M′ M⊢)
      (align-targetᴿ prefix M⊑M′ M′⊢)

  quotient-term-imprecision-store-prefix-alignᴿ
      prefix M⊑M′ M⊢ M′⊢ =
    quotient-term-imprecision-store-prefix-goᴿ prefix M⊑M′
      (align-quotient-sourceᴿ prefix M⊑M′ M⊢)
      (align-quotient-targetᴿ prefix M⊑M′ M′⊢)

  term-imprecision-store-prefix-goᴿ
      prefix (blame⊑ᴿ M′⊢₀) M⊢ M′⊢ =
    blame⊑ᴿ M′⊢

  term-imprecision-store-prefix-goᴿ
      prefix (x⊑xᴿ x∈) M⊢ M′⊢ =
    x⊑xᴿ x∈

  term-imprecision-store-prefix-goᴿ
      prefix (ƛ⊑ƛᴿ hA hA′ N⊑N′)
      (⊢ƛ hA⁺ N⊢) (⊢ƛ hA′⁺ N′⊢) =
    ƛ⊑ƛᴿ hA hA′
      (term-imprecision-store-prefix-alignᴿ
        prefix N⊑N′ N⊢ N′⊢)

  term-imprecision-store-prefix-goᴿ
      prefix (L⊑L′ ·ᴿ M⊑M′)
      (⊢· L⊢ M⊢) (⊢· L′⊢ M′⊢) =
    (term-imprecision-store-prefix-alignᴿ
      prefix L⊑L′ L⊢ L′⊢)
    ·ᴿ
    (term-imprecision-store-prefix-alignᴿ
      prefix M⊑M′ M⊢ M′⊢)

  term-imprecision-store-prefix-goᴿ
      prefix
      (Λ⊑Λᴿ liftρ liftγ vV vV′ V⊑V′)
      (⊢Λ vV⁺ V⊢) (⊢Λ vV′⁺ V′⊢)
      with paired-store-prefix-liftᵀ
        (to-live-prefix prefix) liftρ
  term-imprecision-store-prefix-goᴿ
      prefix
      (Λ⊑Λᴿ liftρ liftγ vV vV′ V⊑V′)
      (⊢Λ vV⁺ V⊢) (⊢Λ vV′⁺ V′⊢)
      | ρ⁺↑ , liftρ⁺ , prefix↑ =
    Λ⊑Λᴿ liftρ⁺ liftγ vV vV′
      (term-imprecision-store-prefix-alignᴿ
        (to-prototype-prefix prefix↑) V⊑V′
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

  term-imprecision-store-prefix-goᴿ
      prefix
      (Λ⊑ᴿ occ liftρ liftγ vV V⊑N′)
      (⊢Λ vV⁺ V⊢) N′⊢
      with left-store-prefix-liftᵀ
        (to-live-prefix prefix) liftρ
  term-imprecision-store-prefix-goᴿ
      prefix
      (Λ⊑ᴿ occ liftρ liftγ vV V⊑N′)
      (⊢Λ vV⁺ V⊢) N′⊢
      | ρ⁺↑ , liftρ⁺ , prefix↑ =
    Λ⊑ᴿ occ liftρ⁺ liftγ vV
      (term-imprecision-store-prefix-alignᴿ
        (to-prototype-prefix prefix↑) V⊑N′
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

  term-imprecision-store-prefix-goᴿ
      prefix (target-instantiationᴿ embedded) M⊢ M′⊢ =
    target-instantiationᴿ
      (prefix-creationᴱ embedded prefix
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

  term-imprecision-store-prefix-goᴿ
      prefix
      (α⊑αᴿ vL noL vL′ noL′ A⇑⊑B⇑ liftρ liftγ L⊑L′
        allocation-prefix L•⊢ L′•⊢)
      L•⊢⁺ L′•⊢⁺ =
    α⊑αᴿ vL noL vL′ noL′ A⇑⊑B⇑ liftρ liftγ L⊑L′
      (store-imp-prefix-transᴿ allocation-prefix prefix)
      L•⊢⁺ L′•⊢⁺

  term-imprecision-store-prefix-goᴿ
      prefix
      (α⊑ᴿ vL noL h⇑A liftρ liftγ L⊑N′
        allocation-prefix L•⊢ N′⊢)
      L•⊢⁺ N′⊢⁺ =
    α⊑ᴿ vL noL h⇑A liftρ liftγ L⊑N′
      (store-imp-prefix-transᴿ allocation-prefix prefix)
      L•⊢⁺ N′⊢⁺

  term-imprecision-store-prefix-goᴿ
      prefix
      (ν⊑νᴿ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
        liftρ liftγ N⊑N′ replace)
      M⊢ M′⊢
      with nu-body-typingᴿ M⊢ | nu-body-typingᴿ M′⊢
         | paired-store-prefix-liftᵀ
             (to-live-prefix prefix) liftρ
  term-imprecision-store-prefix-goᴿ
      prefix
      (ν⊑νᴿ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
        liftρ liftγ N⊑N′ replace)
      M⊢ M′⊢
      | C⁺ , N⊢ | C′⁺ , N′⊢ | ρ⁺↑ , liftρ⁺ , prefix↑ =
    ν⊑νᴿ hA hA′
      (weaken-reveal-conversion
        (StoreIncl-cons
          (renameStoreᵗ-incl suc
            (leftStoreⁱ-prefix-inclusion
              (to-live-prefix prefix))))
        s↑)
      (weaken-reveal-conversion
        (StoreIncl-cons
          (renameStoreᵗ-incl suc
            (rightStoreⁱ-prefix-inclusion
              (to-live-prefix prefix))))
        s′↑)
      A⊑A′ A⇑⊑A′⇑ liftρ⁺ liftγ
      (term-imprecision-store-prefix-alignᴿ
        prefix N⊑N′ N⊢ N′⊢)
      replace

  term-imprecision-store-prefix-goᴿ
      prefix
      (ν⊑ᴿ hA h⇑A s↑ liftρ liftγ N⊑N′ replace)
      M⊢ N′⊢
      with nu-body-typingᴿ M⊢
         | left-store-prefix-liftᵀ
             (to-live-prefix prefix) liftρ
  term-imprecision-store-prefix-goᴿ
      prefix
      (ν⊑ᴿ hA h⇑A s↑ liftρ liftγ N⊑N′ replace)
      M⊢ N′⊢
      | C⁺ , N⊢ | ρ⁺↑ , liftρ⁺ , prefix↑ =
    ν⊑ᴿ hA h⇑A
      (weaken-reveal-conversion
        (StoreIncl-cons
          (renameStoreᵗ-incl suc
            (leftStoreⁱ-prefix-inclusion
              (to-live-prefix prefix))))
      s↑)
      liftρ⁺ liftγ
      (term-imprecision-store-prefix-alignᴿ
        prefix N⊑N′ N⊢ N′⊢)
      replace

  term-imprecision-store-prefix-goᴿ
      prefix κ⊑κᴿ M⊢ M′⊢ =
    κ⊑κᴿ

  term-imprecision-store-prefix-goᴿ
      prefix (L⊑L′ ⊕ᴿ[ op ] M⊑M′)
      (⊢⊕ L⊢ op⁺ M⊢) (⊢⊕ L′⊢ op′⁺ M′⊢) =
    (term-imprecision-store-prefix-alignᴿ
      prefix L⊑L′ L⊢ L′⊢)
    ⊕ᴿ[ op ]
    (term-imprecision-store-prefix-alignᴿ
      prefix M⊑M′ M⊢ M′⊢)

  term-imprecision-store-prefix-goᴿ
      prefix
      (gen⊑groundᴿ mode seal★ c⊒ gH vV vW W⊢₀ V⊑Wtag q)
      M⊢ W⊢
      with cast-body-typingᴿ M⊢
  term-imprecision-store-prefix-goᴿ
      prefix
      (gen⊑groundᴿ mode seal★ c⊒ gH vV vW W⊢₀ V⊑Wtag q)
      M⊢ W⊢
      | A⁺ , V⊢ =
    gen⊑groundᴿ
      mode
      (seal★-weaken
        (leftStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        seal★)
      (narrow-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        c⊒)
      gH vV vW W⊢
      (term-imprecision-store-prefix-alignᴿ
        prefix V⊑Wtag V⊢
        (right-cast-typing-prefixᴿ prefix
          (smaller-imprecision-target-typingᴿ V⊑Wtag)
          W⊢))
      q

  term-imprecision-store-prefix-goᴿ
      prefix
      (cast⊒⊑ᴿ mode seal★ c⊒ M⊑M′ q c-shape comp)
      L⊢ M′⊢
      with cast-body-typingᴿ L⊢
  term-imprecision-store-prefix-goᴿ
      prefix
      (cast⊒⊑ᴿ mode seal★ c⊒ M⊑M′ q c-shape comp)
      L⊢ M′⊢
      | A⁺ , M⊢ =
    cast⊒⊑ᴿ mode
      (seal★-weaken
        (leftStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        seal★)
      (narrow-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        c⊒)
      (term-imprecision-store-prefix-alignᴿ
        prefix M⊑M′ M⊢ M′⊢)
      q c-shape comp

  term-imprecision-store-prefix-goᴿ
      prefix
      (cast⊑⊑ᴿ mode seal★ c⊑ M⊑M′ q c-shape comp)
      L⊢ M′⊢
      with cast-body-typingᴿ L⊢
  term-imprecision-store-prefix-goᴿ
      prefix
      (cast⊑⊑ᴿ mode seal★ c⊑ M⊑M′ q c-shape comp)
      L⊢ M′⊢
      | A⁺ , M⊢ =
    cast⊑⊑ᴿ mode
      (seal★-weaken
        (leftStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        seal★)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        c⊑)
      (term-imprecision-store-prefix-alignᴿ
        prefix M⊑M′ M⊢ M′⊢)
      q c-shape comp

  term-imprecision-store-prefix-goᴿ
      prefix
      (⊑cast⊒ᴿ mode′ seal★′ c′⊒ M⊑M′ q c-shape comp)
      M⊢ L′⊢
      with cast-body-typingᴿ L′⊢
  term-imprecision-store-prefix-goᴿ
      prefix
      (⊑cast⊒ᴿ mode′ seal★′ c′⊒ M⊑M′ q c-shape comp)
      M⊢ L′⊢
      | B′⁺ , M′⊢ =
    ⊑cast⊒ᴿ mode′
      (seal★-weaken
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        seal★′)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        c′⊒)
      (term-imprecision-store-prefix-alignᴿ
        prefix M⊑M′ M⊢ M′⊢)
      q c-shape comp

  term-imprecision-store-prefix-goᴿ
      prefix
      (⊑cast⊑ᴿ mode′ seal★′ c′⊑ M⊑M′ q c-shape comp)
      M⊢ L′⊢
      with cast-body-typingᴿ L′⊢
  term-imprecision-store-prefix-goᴿ
      prefix
      (⊑cast⊑ᴿ mode′ seal★′ c′⊑ M⊑M′ q c-shape comp)
      M⊢ L′⊢
      | B′⁺ , M′⊢ =
    ⊑cast⊑ᴿ mode′
      (seal★-weaken
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        seal★′)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        c′⊑)
      (term-imprecision-store-prefix-alignᴿ
        prefix M⊑M′ M⊢ M′⊢)
      q c-shape comp

  term-imprecision-store-prefix-goᴿ
      prefix (conv↑⊑ᴿ c↑ M⊑M′ q replace)
      L⊢ M′⊢
      with cast-body-typingᴿ L⊢
  term-imprecision-store-prefix-goᴿ
      prefix (conv↑⊑ᴿ c↑ M⊑M′ q replace)
      L⊢ M′⊢
      | A⁺ , M⊢ =
    conv↑⊑ᴿ
      (weaken-reveal-conversion
        (leftStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        c↑)
      (term-imprecision-store-prefix-alignᴿ
        prefix M⊑M′ M⊢ M′⊢)
      q replace

  term-imprecision-store-prefix-goᴿ
      prefix (conv↓⊑ᴿ c↓ M⊑M′ q replace)
      L⊢ M′⊢
      with cast-body-typingᴿ L⊢
  term-imprecision-store-prefix-goᴿ
      prefix (conv↓⊑ᴿ c↓ M⊑M′ q replace)
      L⊢ M′⊢
      | A⁺ , M⊢ =
    conv↓⊑ᴿ
      (weaken-conceal-conversion
        (leftStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        c↓)
      (term-imprecision-store-prefix-alignᴿ
        prefix M⊑M′ M⊢ M′⊢)
      q replace

  term-imprecision-store-prefix-goᴿ
      prefix (⊑conv↑ᴿ c′↑ M⊑M′ q replace)
      M⊢ L′⊢
      with cast-body-typingᴿ L′⊢
  term-imprecision-store-prefix-goᴿ
      prefix (⊑conv↑ᴿ c′↑ M⊑M′ q replace)
      M⊢ L′⊢
      | B′⁺ , M′⊢ =
    ⊑conv↑ᴿ
      (weaken-reveal-conversion
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        c′↑)
      (term-imprecision-store-prefix-alignᴿ
        prefix M⊑M′ M⊢ M′⊢)
      q replace

  term-imprecision-store-prefix-goᴿ
      prefix (⊑conv↓ᴿ c′↓ M⊑M′ q replace)
      M⊢ L′⊢
      with cast-body-typingᴿ L′⊢
  term-imprecision-store-prefix-goᴿ
      prefix (⊑conv↓ᴿ c′↓ M⊑M′ q replace)
      M⊢ L′⊢
      | B′⁺ , M′⊢ =
    ⊑conv↓ᴿ
      (weaken-conceal-conversion
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        c′↓)
      (term-imprecision-store-prefix-alignᴿ
        prefix M⊑M′ M⊢ M′⊢)
      q replace

  term-imprecision-store-prefix-goᴿ
      prefix
      (paired-revealᴿ corresponds c↑ c′↑ replace M⊑M′)
      L⊢ L′⊢
      with cast-body-typingᴿ L⊢ | cast-body-typingᴿ L′⊢
  term-imprecision-store-prefix-goᴿ
      prefix
      (paired-revealᴿ corresponds c↑ c′↑ replace M⊑M′)
      L⊢ L′⊢
      | A⁺ , M⊢ | B′⁺ , M′⊢ =
    paired-revealᴿ
      (store-corresponds-prefix-proofᵀ
        (to-live-prefix prefix) corresponds)
      (weaken-reveal-conversion
        (leftStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        c↑)
      (weaken-reveal-conversion
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        c′↑)
      replace
      (term-imprecision-store-prefix-alignᴿ
        prefix M⊑M′ M⊢ M′⊢)

  term-imprecision-store-prefix-goᴿ
      prefix
      (paired-concealᴿ corresponds c↓ c′↓ replace M⊑M′)
      L⊢ L′⊢
      with cast-body-typingᴿ L⊢ | cast-body-typingᴿ L′⊢
  term-imprecision-store-prefix-goᴿ
      prefix
      (paired-concealᴿ corresponds c↓ c′↓ replace M⊑M′)
      L⊢ L′⊢
      | A⁺ , M⊢ | B′⁺ , M′⊢ =
    paired-concealᴿ
      (store-corresponds-prefix-proofᵀ
        (to-live-prefix prefix) corresponds)
      (weaken-conceal-conversion
        (leftStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        c↓)
      (weaken-conceal-conversion
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        c′↓)
      replace
      (term-imprecision-store-prefix-alignᴿ
        prefix M⊑M′ M⊢ M′⊢)

  term-imprecision-store-prefix-goᴿ
      prefix
      (closeᴿ N⊑N′ widening-pair
        u-shape u′-shape square compatible)
      M⊢ M′⊢
      with cast-body-typingᴿ M⊢ | cast-body-typingᴿ M′⊢
  term-imprecision-store-prefix-goᴿ
      prefix
      (closeᴿ N⊑N′ widening-pair
        u-shape u′-shape square compatible)
      M⊢ M′⊢
      | D⁺ , N⊢ | D′⁺ , N′⊢ =
    closeᴿ
      (quotient-term-imprecision-store-prefix-alignᴿ
        prefix N⊑N′ N⊢ N′⊢)
      (quotient-widening-pair-prefixᴿ prefix widening-pair)
      u-shape u′-shape square compatible

  term-imprecision-store-prefix-goᴿ
      prefix
      (paired-wideningᴿ
        mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
        left right compatible M⊑M′)
      L⊢ L′⊢
      with cast-body-typingᴿ L⊢ | cast-body-typingᴿ L′⊢
  term-imprecision-store-prefix-goᴿ
      prefix
      (paired-wideningᴿ
        mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
        left right compatible M⊑M′)
      L⊢ L′⊢
      | A⁺ , M⊢ | B′⁺ , M′⊢ =
    paired-wideningᴿ
      mode
      (seal★-weaken
        (leftStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        seal★)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        c⊑)
      c-shape
      mode′
      (seal★-weaken
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        seal★′)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        c′⊑)
      c′-shape left right compatible
      (term-imprecision-store-prefix-alignᴿ
        prefix M⊑M′ M⊢ M′⊢)

  quotient-term-imprecision-store-prefix-goᴿ
      prefix
      (paired-downᴿ
        M⊑M′ source-mode source source-shape
        target-mode target target-shape square)
      L⊢ L′⊢
      with cast-body-typingᴿ L⊢ | cast-body-typingᴿ L′⊢
  quotient-term-imprecision-store-prefix-goᴿ
      prefix
      (paired-downᴿ
        M⊑M′ source-mode source source-shape
        target-mode target target-shape square)
      L⊢ L′⊢
      | D⁺ , M⊢ | D′⁺ , M′⊢ =
    paired-downᴿ
      (term-imprecision-store-prefix-alignᴿ
        prefix M⊑M′ M⊢ M′⊢)
      (spine-cast-mode-prefixᴿ prefix source-mode)
      (narrow-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        source)
      source-shape
      (target-spine-cast-mode-prefixᴿ prefix target-mode)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion (to-live-prefix prefix))
        target)
      target-shape square
