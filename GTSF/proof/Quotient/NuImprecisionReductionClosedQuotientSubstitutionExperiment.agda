module
  proof.Quotient.NuImprecisionReductionClosedQuotientSubstitutionExperiment
  where

-- File Charter:
--   * Tests parallel and single term substitution for the independent smaller
--     ordinary and one-boundary quotient-imprecision relations.
--   * Defines the genuine binder frame and Kripke substitution-environment
--     family needed by structurally recursive parallel substitution.
--   * Reconstructs every store-indexed premise after arbitrary proof-only
--     allocation prefixes.
--   * Keeps theorem conclusions fully indexed at their use sites.
--   * Imports neither the live term-imprecision relation nor any theorem that
--     converts through it.
--   * Contains no postulate, hole, permissive option, termination bypass, or
--     catch-all clause.

open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (subst; sym)

open import Conversion using
  (weaken-conceal-conversion; weaken-reveal-conversion)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import Imprecision using
  (ImpCtx; _ˣ⊑★; _ˣ⊑ˣ_; ⇑ᴸᵢ; ⇑ᵢ)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using (narrow-weaken; widen-weaken)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreCorresponds
  ; StoreImp
  ; correspondence-linked
  ; correspondence-stored
  ; leftStoreⁱ
  ; lift-left-store-left
  ; lift-left-store-link
  ; lift-left-store-right
  ; lift-left-store-∷
  ; lift-store-left
  ; lift-store-link
  ; lift-store-right
  ; lift-store-∷
  ; rightStoreⁱ
  ; store-left
  ; store-link
  ; store-matched
  ; store-right
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftCtxⁱ
  ; ctx-imp
  ; leftCtxⁱ
  ; lift-ctx-[]
  ; lift-ctx-∷
  ; lift-left-ctx-[]
  ; lift-left-ctx-∷
  ; rightCtxⁱ
  )
open import NuTerms using
  ( Closedᵐ
  ; No•
  ; Substˣ
  ; Term
  ; Value
  ; extˢˣ
  ; no•-$
  ; no•-ƛ
  ; no•-Λ
  ; no•-·
  ; no•-ν
  ; no•-⊕
  ; no•-`
  ; no•-⟨⟩
  ; no•-blame
  ; substˣᵐ
  ; ↑ᵗᵐ
  )
open import Store using (StoreIncl; StoreIncl-cons)
open import TermTyping using (forget)
open import Types using
  (Ty; TyCtx; S; Z; _∋_⦂_; ⇑ᵗ)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (shape-lift∀ᵢ; shape-source-liftνᵢ)
open import proof.Core.Properties.NuTermProperties using
  ( closed-refined-typing-recontextualize
  ; subst-closedᵐ
  ; substˣᵐ-preserves-Value
  ; typing-closedᵐ
  )
open import proof.Core.Properties.StoreProperties using
  (renameStoreᵗ-incl)
open import proof.Core.Properties.TypePreservation using
  ( SubstNo•
  ; SubstWf
  ; seal★-weaken
  ; term-weaken
  ; typing-substˣ
  )
open import proof.Core.Properties.TypeProperties using
  (TyRenameWf-suc; renameᵗ-preserves-WfTy)
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  (⊑-lift∀ᵢ; ⊑-source-liftνᵢ)
open import QuotientImprecisionCompatibility
  using (SpineCastMode; gradual↓; id-only↓)
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
  using
  ( QuotientWideningPairᴿ
  ; blame⊑ᴿ
  ; cast⊑⊑ᴿ
  ; cast⊒⊑ᴿ
  ; closeᴿ
  ; conv↑⊑ᴿ
  ; conv↓⊑ᴿ
  ; gen⊑groundᴿ
  ; paired-concealᴿ
  ; paired-downᴿ
  ; paired-revealᴿ
  ; paired-wideningᴿ
  ; quotient-cast-wideningᴿ
  ; quotient-id-wideningᴿ
  ; target-instantiationᴿ
  ; x⊑xᴿ
  ; ƛ⊑ƛᴿ
  ; Λ⊑Λᴿ
  ; Λ⊑ᴿ
  ; _·ᴿ_
  ; α⊑αᴿ
  ; α⊑ᴿ
  ; κ⊑κᴿ
  ; ν⊑νᴿ
  ; ν⊑ᴿ
  ; ⊑cast⊑ᴿ
  ; ⊑cast⊒ᴿ
  ; ⊑conv↑ᴿ
  ; ⊑conv↓ᴿ
  ; _⊕ᴿ[_]_
  ; _∣_∣_∣_∣_⊢ᴿ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴿᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using
  ( embedded-creation-source-typingᴱ
  ; embedded-creation-target-typingᴱ
  )
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientTypingExperiment
  using
  ( smaller-imprecision-source-typingᴿ
  ; smaller-imprecision-target-typingᴿ
  )
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientStorePrefixExperiment
  using (term-imprecision-store-prefixᴿ)
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using
  ( StoreImpPrefixᴿ
  ; prefix-reflᴿ
  ; prefix-∷ᴿ
  )


------------------------------------------------------------------------
-- Prefix algebra independent of the live term relation
------------------------------------------------------------------------

left-store-prefix-inclusionᴿ :
  ∀ {Φ Δᴸ Δᴿ} {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefixᴿ ρ₀ ρ⁺ →
  StoreIncl (leftStoreⁱ ρ₀) (leftStoreⁱ ρ⁺)
left-store-prefix-inclusionᴿ prefix-reflᴿ x∈ = x∈
left-store-prefix-inclusionᴿ
    (prefix-∷ᴿ {entry = store-matched α A β B p} prefix) x∈ =
  there (left-store-prefix-inclusionᴿ prefix x∈)
left-store-prefix-inclusionᴿ
    (prefix-∷ᴿ {entry = store-left α A hA} prefix) x∈ =
  there (left-store-prefix-inclusionᴿ prefix x∈)
left-store-prefix-inclusionᴿ
    (prefix-∷ᴿ {entry = store-right β B hB} prefix) x∈ =
  left-store-prefix-inclusionᴿ prefix x∈
left-store-prefix-inclusionᴿ
    (prefix-∷ᴿ {entry = store-link α A β B p} prefix) x∈ =
  left-store-prefix-inclusionᴿ prefix x∈


right-store-prefix-inclusionᴿ :
  ∀ {Φ Δᴸ Δᴿ} {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefixᴿ ρ₀ ρ⁺ →
  StoreIncl (rightStoreⁱ ρ₀) (rightStoreⁱ ρ⁺)
right-store-prefix-inclusionᴿ prefix-reflᴿ x∈ = x∈
right-store-prefix-inclusionᴿ
    (prefix-∷ᴿ {entry = store-matched α A β B p} prefix) x∈ =
  there (right-store-prefix-inclusionᴿ prefix x∈)
right-store-prefix-inclusionᴿ
    (prefix-∷ᴿ {entry = store-left α A hA} prefix) x∈ =
  right-store-prefix-inclusionᴿ prefix x∈
right-store-prefix-inclusionᴿ
    (prefix-∷ᴿ {entry = store-right β B hB} prefix) x∈ =
  there (right-store-prefix-inclusionᴿ prefix x∈)
right-store-prefix-inclusionᴿ
    (prefix-∷ᴿ {entry = store-link α A β B p} prefix) x∈ =
  right-store-prefix-inclusionᴿ prefix x∈


store-prefix-transᴿ :
  ∀ {Φ Δᴸ Δᴿ} {ρ₀ ρ₁ ρ₂ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefixᴿ ρ₀ ρ₁ →
  StoreImpPrefixᴿ ρ₁ ρ₂ →
  StoreImpPrefixᴿ ρ₀ ρ₂
store-prefix-transᴿ prefix₀₁ prefix-reflᴿ = prefix₀₁
store-prefix-transᴿ prefix₀₁ (prefix-∷ᴿ prefix₁₂) =
  prefix-∷ᴿ (store-prefix-transᴿ prefix₀₁ prefix₁₂)


paired-store-prefix-liftᴿ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₀↑ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)} →
  StoreImpPrefixᴿ ρ₀ ρ⁺ →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ₀↑ →
  ∃[ ρ⁺↑ ]
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ⁺ ρ⁺↑ ×
    StoreImpPrefixᴿ ρ₀↑ ρ⁺↑
paired-store-prefix-liftᴿ prefix-reflᴿ liftρ =
  _ , liftρ , prefix-reflᴿ
paired-store-prefix-liftᴿ
    (prefix-∷ᴿ {entry = store-matched α A β B p} prefix) liftρ
    with paired-store-prefix-liftᴿ prefix liftρ
paired-store-prefix-liftᴿ
    (prefix-∷ᴿ {entry = store-matched α A β B p} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-matched (suc α) (⇑ᵗ A) (suc β) (⇑ᵗ B)
    (⊑-lift∀ᵢ p) ∷ ρ⁺↑ ,
  lift-store-∷ (shape-lift∀ᵢ p) lift⁺ , prefix-∷ᴿ prefix↑
paired-store-prefix-liftᴿ
    (prefix-∷ᴿ {entry = store-left α A hA} prefix) liftρ
    with paired-store-prefix-liftᴿ prefix liftρ
paired-store-prefix-liftᴿ
    (prefix-∷ᴿ {entry = store-left α A hA} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-left (suc α) (⇑ᵗ A)
    (renameᵗ-preserves-WfTy hA TyRenameWf-suc) ∷ ρ⁺↑ ,
  lift-store-left lift⁺ , prefix-∷ᴿ prefix↑
paired-store-prefix-liftᴿ
    (prefix-∷ᴿ {entry = store-right β B hB} prefix) liftρ
    with paired-store-prefix-liftᴿ prefix liftρ
paired-store-prefix-liftᴿ
    (prefix-∷ᴿ {entry = store-right β B hB} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-right (suc β) (⇑ᵗ B)
    (renameᵗ-preserves-WfTy hB TyRenameWf-suc) ∷ ρ⁺↑ ,
  lift-store-right lift⁺ , prefix-∷ᴿ prefix↑
paired-store-prefix-liftᴿ
    (prefix-∷ᴿ {entry = store-link α A β B p} prefix) liftρ
    with paired-store-prefix-liftᴿ prefix liftρ
paired-store-prefix-liftᴿ
    (prefix-∷ᴿ {entry = store-link α A β B p} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-link (suc α) (⇑ᵗ A) (suc β) (⇑ᵗ B)
    (⊑-lift∀ᵢ p) ∷ ρ⁺↑ ,
  lift-store-link (shape-lift∀ᵢ p) lift⁺ , prefix-∷ᴿ prefix↑


left-store-prefix-liftᴿ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₀↑ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ} →
  StoreImpPrefixᴿ ρ₀ ρ⁺ →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρ₀↑ →
  ∃[ ρ⁺↑ ]
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ⁺ ρ⁺↑ ×
    StoreImpPrefixᴿ ρ₀↑ ρ⁺↑
left-store-prefix-liftᴿ prefix-reflᴿ liftρ =
  _ , liftρ , prefix-reflᴿ
left-store-prefix-liftᴿ
    (prefix-∷ᴿ {entry = store-matched α A β B p} prefix) liftρ
    with left-store-prefix-liftᴿ prefix liftρ
left-store-prefix-liftᴿ
    (prefix-∷ᴿ {entry = store-matched α A β B p} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-matched (suc α) (⇑ᵗ A) β B
    (⊑-source-liftνᵢ p) ∷ ρ⁺↑ ,
  lift-left-store-∷ (shape-source-liftνᵢ p) lift⁺ ,
  prefix-∷ᴿ prefix↑
left-store-prefix-liftᴿ
    (prefix-∷ᴿ {entry = store-left α A hA} prefix) liftρ
    with left-store-prefix-liftᴿ prefix liftρ
left-store-prefix-liftᴿ
    (prefix-∷ᴿ {entry = store-left α A hA} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-left (suc α) (⇑ᵗ A)
    (renameᵗ-preserves-WfTy hA TyRenameWf-suc) ∷ ρ⁺↑ ,
  lift-left-store-left lift⁺ , prefix-∷ᴿ prefix↑
left-store-prefix-liftᴿ
    (prefix-∷ᴿ {entry = store-right β B hB} prefix) liftρ
    with left-store-prefix-liftᴿ prefix liftρ
left-store-prefix-liftᴿ
    (prefix-∷ᴿ {entry = store-right β B hB} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-right β B hB ∷ ρ⁺↑ ,
  lift-left-store-right lift⁺ , prefix-∷ᴿ prefix↑
left-store-prefix-liftᴿ
    (prefix-∷ᴿ {entry = store-link α A β B p} prefix) liftρ
    with left-store-prefix-liftᴿ prefix liftρ
left-store-prefix-liftᴿ
    (prefix-∷ᴿ {entry = store-link α A β B p} prefix) liftρ
    | ρ⁺↑ , lift⁺ , prefix↑ =
  store-link (suc α) (⇑ᵗ A) β B
    (⊑-source-liftνᵢ p) ∷ ρ⁺↑ ,
  lift-left-store-link (shape-source-liftνᵢ p) lift⁺ ,
  prefix-∷ᴿ prefix↑


paired-ctx-lift-resultᴿ :
  ∀ {Φ Δᴸ Δᴿ} (γ : CtxImp Φ Δᴸ Δᴿ) →
  ∃[ γ′ ] LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ′
paired-ctx-lift-resultᴿ [] = [] , lift-ctx-[]
paired-ctx-lift-resultᴿ (ctx-imp A B p ∷ γ)
    with paired-ctx-lift-resultᴿ γ
paired-ctx-lift-resultᴿ (ctx-imp A B p ∷ γ)
    | γ′ , liftγ =
  ctx-imp (⇑ᵗ A) (⇑ᵗ B) (⊑-lift∀ᵢ p) ∷ γ′ ,
  lift-ctx-∷ (shape-lift∀ᵢ p) liftγ


left-ctx-lift-resultᴿ :
  ∀ {Φ Δᴸ Δᴿ} (γ : CtxImp Φ Δᴸ Δᴿ) →
  ∃[ γ′ ]
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ′
left-ctx-lift-resultᴿ [] = [] , lift-left-ctx-[]
left-ctx-lift-resultᴿ (ctx-imp A B p ∷ γ)
    with left-ctx-lift-resultᴿ γ
left-ctx-lift-resultᴿ (ctx-imp A B p ∷ γ)
    | γ′ , liftγ =
  ctx-imp (⇑ᵗ A) B (⊑-source-liftνᵢ p) ∷ γ′ ,
  lift-left-ctx-∷ (shape-source-liftνᵢ p) liftγ


store-corresponds-prefixᴿ :
  ∀ {Φ Δᴸ Δᴿ} {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {α X β X′ p} →
  StoreImpPrefixᴿ ρ₀ ρ⁺ →
  StoreCorresponds ρ₀ α X β X′ p →
  StoreCorresponds ρ⁺ α X β X′ p
store-corresponds-prefixᴿ prefix-reflᴿ corresponds = corresponds
store-corresponds-prefixᴿ (prefix-∷ᴿ prefix) corresponds
    with store-corresponds-prefixᴿ prefix corresponds
store-corresponds-prefixᴿ (prefix-∷ᴿ prefix)
    corresponds | correspondence-stored entry∈ =
  correspondence-stored (there entry∈)
store-corresponds-prefixᴿ (prefix-∷ᴿ prefix)
    corresponds | correspondence-linked entry∈ =
  correspondence-linked (there entry∈)


quotient-widening-prefixᴿ :
  ∀ {Φ Δᴸ Δᴿ} {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {u u′ D D′ A A′} →
  StoreImpPrefixᴿ ρ₀ ρ⁺ →
  QuotientWideningPairᴿ Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
  QuotientWideningPairᴿ Δᴸ Δᴿ ρ⁺ u u′ D D′ A A′
quotient-widening-prefixᴿ prefix
    (quotient-id-wideningᴿ source target) =
  quotient-id-wideningᴿ
    (widen-weaken ≤-refl
      (left-store-prefix-inclusionᴿ prefix) source)
    (widen-weaken ≤-refl
      (right-store-prefix-inclusionᴿ prefix) target)
quotient-widening-prefixᴿ prefix
    (quotient-cast-wideningᴿ
      mode seal★ source mode′ seal★′ target) =
  quotient-cast-wideningᴿ
    mode
    (seal★-weaken (left-store-prefix-inclusionᴿ prefix) seal★)
    (widen-weaken ≤-refl
      (left-store-prefix-inclusionᴿ prefix) source)
    mode′
    (seal★-weaken (right-store-prefix-inclusionᴿ prefix) seal★′)
    (widen-weaken ≤-refl
      (right-store-prefix-inclusionᴿ prefix) target)


spine-mode-prefixᴿ :
  ∀ {Σ Σ′ μ} →
  StoreIncl Σ Σ′ →
  SpineCastMode Σ μ →
  SpineCastMode Σ′ μ
spine-mode-prefixᴿ inclusion id-only↓ = id-only↓
spine-mode-prefixᴿ inclusion (gradual↓ mode seal★) =
  gradual↓ mode (seal★-weaken inclusion seal★)


------------------------------------------------------------------------
-- Genuine binder frames and environment family
------------------------------------------------------------------------

data SmallerSubstitutionFrameᴿ
    {Φ₀ : ImpCtx} {Δ₀ᴸ Δ₀ᴿ : TyCtx}
    (ρ₀ : StoreImp Φ₀ Δ₀ᴸ Δ₀ᴿ)
    (γ₀ δ₀ : CtxImp Φ₀ Δ₀ᴸ Δ₀ᴿ)
    (τ₀ τ₀′ : Substˣ) :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} →
    StoreImp Φ Δᴸ Δᴿ →
    CtxImp Φ Δᴸ Δᴿ →
    CtxImp Φ Δᴸ Δᴿ →
    Substˣ → Substˣ → Set₁ where
  substitution-frame-idᴿ :
    SmallerSubstitutionFrameᴿ ρ₀ γ₀ δ₀ τ₀ τ₀′
      ρ₀ γ₀ δ₀ τ₀ τ₀′

  substitution-frame-ƛᴿ :
    ∀ {Φ Δᴸ Δᴿ ρ γ δ τ τ′ A A′ pA} →
    SmallerSubstitutionFrameᴿ ρ₀ γ₀ δ₀ τ₀ τ₀′
      {Φ} {Δᴸ} {Δᴿ} ρ γ δ τ τ′ →
    SmallerSubstitutionFrameᴿ ρ₀ γ₀ δ₀ τ₀ τ₀′
      ρ
      (ctx-imp A A′ pA ∷ γ)
      (ctx-imp A A′ pA ∷ δ)
      (extˢˣ τ) (extˢˣ τ′)

  substitution-frame-Λᴿ :
    ∀ {Φ Δᴸ Δᴿ ρ ρ↑ γ γ↑ δ δ↑ τ τ′} →
    SmallerSubstitutionFrameᴿ ρ₀ γ₀ δ₀ τ₀ τ₀′
      {Φ} {Δᴸ} {Δᴿ} ρ γ δ τ τ′ →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ↑ →
    LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ↑ →
    LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) δ δ↑ →
    SmallerSubstitutionFrameᴿ ρ₀ γ₀ δ₀ τ₀ τ₀′
      ρ↑ γ↑ δ↑ (↑ᵗᵐ τ) (↑ᵗᵐ τ′)

  substitution-frame-Λ-leftᴿ :
    ∀ {Φ Δᴸ Δᴿ ρ ρ↑ γ γ↑ δ δ↑ τ τ′} →
    SmallerSubstitutionFrameᴿ ρ₀ γ₀ δ₀ τ₀ τ₀′
      {Φ} {Δᴸ} {Δᴿ} ρ γ δ τ τ′ →
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ↑ →
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ↑ →
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) δ δ↑ →
    SmallerSubstitutionFrameᴿ ρ₀ γ₀ δ₀ τ₀ τ₀′
      ρ↑ γ↑ δ↑ (↑ᵗᵐ τ) τ′


SmallerSubstitutionEnvironmentFamilyᴿ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} →
  StoreImp Φ Δᴸ Δᴿ →
  CtxImp Φ Δᴸ Δᴿ →
  CtxImp Φ Δᴸ Δᴿ →
  Substˣ → Substˣ → Set₁
SmallerSubstitutionEnvironmentFamilyᴿ ρ₀ γ₀ δ₀ τ₀ τ₀′ =
  ∀ {Φ Δᴸ Δᴿ ρ γ δ τ τ′} →
  SmallerSubstitutionFrameᴿ ρ₀ γ₀ δ₀ τ₀ τ₀′
    {Φ} {Δᴸ} {Δᴿ} ρ γ δ τ τ′ →
  (∀ {x A B p} →
    γ ∋ x ⦂ ctx-imp A B p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
      ⊢ᴿ τ x ⊑ τ′ x ⦂ A ⊑ B ∶ p) ×
  (∀ x → No• (τ x)) ×
  (∀ x → No• (τ′ x))


smaller-substitution-source-wfᴿ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {γ δ : CtxImp Φ Δᴸ Δᴿ}
    {τ τ′ : Substˣ} →
  (∀ {x A B p} →
    γ ∋ x ⦂ ctx-imp A B p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
      ⊢ᴿ τ x ⊑ τ′ x ⦂ A ⊑ B ∶ p) →
  SubstWf Δᴸ (leftStoreⁱ ρ) (leftCtxⁱ γ) (leftCtxⁱ δ) τ
smaller-substitution-source-wfᴿ {γ = []} related ()
smaller-substitution-source-wfᴿ
    {γ = ctx-imp A B p ∷ γ} related Z =
  smaller-imprecision-source-typingᴿ (related Z)
smaller-substitution-source-wfᴿ
    {γ = ctx-imp A B p ∷ γ} related (S x∈) =
  smaller-substitution-source-wfᴿ
    (λ y∈ → related (S y∈)) x∈


smaller-substitution-target-wfᴿ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {γ δ : CtxImp Φ Δᴸ Δᴿ}
    {τ τ′ : Substˣ} →
  (∀ {x A B p} →
    γ ∋ x ⦂ ctx-imp A B p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
      ⊢ᴿ τ x ⊑ τ′ x ⦂ A ⊑ B ∶ p) →
  SubstWf Δᴿ (rightStoreⁱ ρ)
    (rightCtxⁱ γ) (rightCtxⁱ δ) τ′
smaller-substitution-target-wfᴿ {γ = []} related ()
smaller-substitution-target-wfᴿ
    {γ = ctx-imp A B p ∷ γ} related Z =
  smaller-imprecision-target-typingᴿ (related Z)
smaller-substitution-target-wfᴿ
    {γ = ctx-imp A B p ∷ γ} related (S x∈) =
  smaller-substitution-target-wfᴿ
    (λ y∈ → related (S y∈)) x∈


pointwise-no-bulletᴿ :
  ∀ {γ τ} →
  (∀ x → No• (τ x)) →
  SubstNo• γ τ
pointwise-no-bulletᴿ noτ {x = x} x∈ = noτ x


------------------------------------------------------------------------
-- Prefix-aware parallel substitution
------------------------------------------------------------------------

mutual
  smaller-parallel-term-substitution-framedᴿ :
    ∀ {Φ₀ : ImpCtx} {Δ₀ᴸ Δ₀ᴿ : TyCtx}
      {ρ⁺₀ : StoreImp Φ₀ Δ₀ᴸ Δ₀ᴿ}
      {γ₀ δ₀ : CtxImp Φ₀ Δ₀ᴸ Δ₀ᴿ}
      {τ₀ τ₀′ : Substˣ} →
    (environment : SmallerSubstitutionEnvironmentFamilyᴿ
      ρ⁺₀ γ₀ δ₀ τ₀ τ₀′) →
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {γ δ : CtxImp Φ Δᴸ Δᴿ}
      {τ τ′ : Substˣ} {N N′ : Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    SmallerSubstitutionFrameᴿ ρ⁺₀ γ₀ δ₀ τ₀ τ₀′
      {Φ} {Δᴸ} {Δᴿ} ρ⁺ γ δ τ τ′ →
    StoreImpPrefixᴿ ρ₀ ρ⁺ →
    No• N → No• N′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
      ⊢ᴿ N ⊑ N′ ⦂ A ⊑ B ∶ p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ δ
      ⊢ᴿ substˣᵐ τ N ⊑ substˣᵐ τ′ N′
      ⦂ A ⊑ B ∶ p

  smaller-parallel-quotient-substitution-framedᴿ :
    ∀ {Φ₀ : ImpCtx} {Δ₀ᴸ Δ₀ᴿ : TyCtx}
      {ρ⁺₀ : StoreImp Φ₀ Δ₀ᴸ Δ₀ᴿ}
      {γ₀ δ₀ : CtxImp Φ₀ Δ₀ᴸ Δ₀ᴿ}
      {τ₀ τ₀′ : Substˣ} →
    (environment : SmallerSubstitutionEnvironmentFamilyᴿ
      ρ⁺₀ γ₀ δ₀ τ₀ τ₀′) →
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {γ δ : CtxImp Φ Δᴸ Δᴿ}
      {τ τ′ : Substˣ} {N N′ : Term} {D D′ : Ty}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
    SmallerSubstitutionFrameᴿ ρ⁺₀ γ₀ δ₀ τ₀ τ₀′
      {Φ} {Δᴸ} {Δᴿ} ρ⁺ γ δ τ τ′ →
    StoreImpPrefixᴿ ρ₀ ρ⁺ →
    No• N → No• N′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
      ⊢ᴿᵖ N ⊑ N′ ⦂ D ⊑ᵖ D′ ∶ q →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ δ
      ⊢ᴿᵖ substˣᵐ τ N ⊑ substˣᵐ τ′ N′
      ⦂ D ⊑ᵖ D′ ∶ q

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix no•-blame noN′
      (blame⊑ᴿ N′⊢)
      with environment frame
  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix no•-blame noN′
      (blame⊑ᴿ N′⊢)
      | related , noτ , noτ′ =
    blame⊑ᴿ
      (typing-substˣ
        (smaller-substitution-target-wfᴿ related)
        (pointwise-no-bulletᴿ noτ′)
        noN′
        (term-weaken ≤-refl
          (right-store-prefix-inclusionᴿ prefix) noN′ N′⊢))

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix no•-` no•-` (x⊑xᴿ x∈)
      with environment frame
  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix no•-` no•-` (x⊑xᴿ x∈)
      | related , noτ , noτ′ =
    related x∈

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix (no•-ƛ noN) (no•-ƛ noN′)
      (ƛ⊑ƛᴿ hA hA′ body) =
    ƛ⊑ƛᴿ hA hA′
      (smaller-parallel-term-substitution-framedᴿ
        environment (substitution-frame-ƛᴿ frame)
        prefix noN noN′ body)

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix
      (no•-· noL noM) (no•-· noL′ noM′)
      (fun ·ᴿ arg) =
    smaller-parallel-term-substitution-framedᴿ
      environment frame prefix noL noL′ fun
    ·ᴿ
    smaller-parallel-term-substitution-framedᴿ
      environment frame prefix noM noM′ arg

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix (no•-Λ noV) (no•-Λ noV′)
      (Λ⊑Λᴿ liftρ liftγ vV vV′ body)
      with paired-store-prefix-liftᴿ prefix liftρ
         | paired-ctx-lift-resultᴿ _
  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix (no•-Λ noV) (no•-Λ noV′)
      (Λ⊑Λᴿ liftρ liftγ vV vV′ body)
      | ρ⁺↑ , liftρ⁺ , prefix↑
      | δ↑ , liftδ =
    Λ⊑Λᴿ liftρ⁺ liftδ
      (substˣᵐ-preserves-Value _ vV)
      (substˣᵐ-preserves-Value _ vV′)
      (smaller-parallel-term-substitution-framedᴿ
        environment
        (substitution-frame-Λᴿ frame liftρ⁺ liftγ liftδ)
        prefix↑ noV noV′ body)

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix (no•-Λ noV) noN′
      (Λ⊑ᴿ occ liftρ liftγ vV body)
      with left-store-prefix-liftᴿ prefix liftρ
         | left-ctx-lift-resultᴿ _
  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix (no•-Λ noV) noN′
      (Λ⊑ᴿ occ liftρ liftγ vV body)
      | ρ⁺↑ , liftρ⁺ , prefix↑
      | δ↑ , liftδ =
    Λ⊑ᴿ occ liftρ⁺ liftδ
      (substˣᵐ-preserves-Value _ vV)
      (smaller-parallel-term-substitution-framedᴿ
        environment
        (substitution-frame-Λ-leftᴿ frame liftρ⁺ liftγ liftδ)
        prefix↑ noV noN′ body)

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix () noN′
      (α⊑αᴿ vL noL vL′ noL′ p liftρ liftγ
        body allocation-prefix L⊢ L′⊢)
  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix () noN′
      (α⊑ᴿ vL noL hA liftρ liftγ body
        allocation-prefix L⊢ N′⊢)

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix
      (no•-ν noN) (no•-ν noN′)
      (ν⊑νᴿ hA hA′ s↑ s′↑ A⊑A′ A↑⊑A′↑
        liftρ liftγ body replace)
      with paired-store-prefix-liftᴿ prefix liftρ
         | paired-ctx-lift-resultᴿ _
  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix
      (no•-ν noN) (no•-ν noN′)
      (ν⊑νᴿ hA hA′ s↑ s′↑ A⊑A′ A↑⊑A′↑
        liftρ liftγ body replace)
      | ρ⁺↑ , liftρ⁺ , prefix↑
      | δ↑ , liftδ =
    ν⊑νᴿ hA hA′
      (weaken-reveal-conversion
        (StoreIncl-cons
          (renameStoreᵗ-incl suc
            (left-store-prefix-inclusionᴿ prefix)))
        s↑)
      (weaken-reveal-conversion
        (StoreIncl-cons
          (renameStoreᵗ-incl suc
            (right-store-prefix-inclusionᴿ prefix)))
        s′↑)
      A⊑A′ A↑⊑A′↑ liftρ⁺ liftδ
      (smaller-parallel-term-substitution-framedᴿ
        environment frame prefix noN noN′ body)
      replace

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix (no•-ν noN) noN′
      (ν⊑ᴿ hA hA↑ s↑ liftρ liftγ body replace)
      with left-store-prefix-liftᴿ prefix liftρ
         | left-ctx-lift-resultᴿ _
  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix (no•-ν noN) noN′
      (ν⊑ᴿ hA hA↑ s↑ liftρ liftγ body replace)
      | ρ⁺↑ , liftρ⁺ , prefix↑
      | δ↑ , liftδ =
    ν⊑ᴿ hA hA↑
      (weaken-reveal-conversion
        (StoreIncl-cons
          (renameStoreᵗ-incl suc
            (left-store-prefix-inclusionᴿ prefix)))
        s↑)
      liftρ⁺ liftδ
      (smaller-parallel-term-substitution-framedᴿ
        environment frame prefix noN noN′ body)
      replace

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix no•-$ no•-$ κ⊑κᴿ =
    κ⊑κᴿ

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix
      (no•-⊕ noL noM) (no•-⊕ noL′ noM′)
      (left ⊕ᴿ[ op ] right) =
    smaller-parallel-term-substitution-framedᴿ
      environment frame prefix noL noL′ left
    ⊕ᴿ[ op ]
    smaller-parallel-term-substitution-framedᴿ
      environment frame prefix noM noM′ right

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix (no•-⟨⟩ noV) noW
      (gen⊑groundᴿ
        mode seal★ c⊒ ground vV vW W⊢ body q)
      with environment frame
  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix (no•-⟨⟩ noV) noW
      (gen⊑groundᴿ
        mode seal★ c⊒ ground vV vW W⊢ body q)
      | related , noτ , noτ′ =
    gen⊑groundᴿ mode
      (seal★-weaken (left-store-prefix-inclusionᴿ prefix) seal★)
      (narrow-weaken ≤-refl
        (left-store-prefix-inclusionᴿ prefix) c⊒)
      ground
      (substˣᵐ-preserves-Value _ vV)
      (substˣᵐ-preserves-Value _ vW)
      (typing-substˣ
        (smaller-substitution-target-wfᴿ related)
        (pointwise-no-bulletᴿ noτ′)
        noW
        (term-weaken ≤-refl
          (right-store-prefix-inclusionᴿ prefix)
          noW W⊢))
      (smaller-parallel-term-substitution-framedᴿ
        environment frame prefix noV (no•-⟨⟩ noW) body)
      q

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix (no•-⟨⟩ noM) noM′
      (cast⊒⊑ᴿ mode seal★ c⊒ body q shape comp) =
    cast⊒⊑ᴿ mode
      (seal★-weaken (left-store-prefix-inclusionᴿ prefix) seal★)
      (narrow-weaken ≤-refl
        (left-store-prefix-inclusionᴿ prefix) c⊒)
      (smaller-parallel-term-substitution-framedᴿ
        environment frame prefix noM noM′ body)
      q shape comp

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix (no•-⟨⟩ noM) noM′
      (cast⊑⊑ᴿ mode seal★ c⊑ body q shape comp) =
    cast⊑⊑ᴿ mode
      (seal★-weaken (left-store-prefix-inclusionᴿ prefix) seal★)
      (widen-weaken ≤-refl
        (left-store-prefix-inclusionᴿ prefix) c⊑)
      (smaller-parallel-term-substitution-framedᴿ
        environment frame prefix noM noM′ body)
      q shape comp

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix noM (no•-⟨⟩ noM′)
      (⊑cast⊒ᴿ mode seal★ c⊒ body q shape comp) =
    ⊑cast⊒ᴿ mode
      (seal★-weaken (right-store-prefix-inclusionᴿ prefix) seal★)
      (narrow-weaken ≤-refl
        (right-store-prefix-inclusionᴿ prefix) c⊒)
      (smaller-parallel-term-substitution-framedᴿ
        environment frame prefix noM noM′ body)
      q shape comp

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix noM (no•-⟨⟩ noM′)
      (⊑cast⊑ᴿ mode seal★ c⊑ body q shape comp) =
    ⊑cast⊑ᴿ mode
      (seal★-weaken (right-store-prefix-inclusionᴿ prefix) seal★)
      (widen-weaken ≤-refl
        (right-store-prefix-inclusionᴿ prefix) c⊑)
      (smaller-parallel-term-substitution-framedᴿ
        environment frame prefix noM noM′ body)
      q shape comp

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix (no•-⟨⟩ noM) noM′
      (conv↑⊑ᴿ conversion body q replace) =
    conv↑⊑ᴿ
      (weaken-reveal-conversion
        (left-store-prefix-inclusionᴿ prefix) conversion)
      (smaller-parallel-term-substitution-framedᴿ
        environment frame prefix noM noM′ body)
      q replace

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix (no•-⟨⟩ noM) noM′
      (conv↓⊑ᴿ conversion body q replace) =
    conv↓⊑ᴿ
      (weaken-conceal-conversion
        (left-store-prefix-inclusionᴿ prefix) conversion)
      (smaller-parallel-term-substitution-framedᴿ
        environment frame prefix noM noM′ body)
      q replace

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix noM (no•-⟨⟩ noM′)
      (⊑conv↑ᴿ conversion body q replace) =
    ⊑conv↑ᴿ
      (weaken-reveal-conversion
        (right-store-prefix-inclusionᴿ prefix) conversion)
      (smaller-parallel-term-substitution-framedᴿ
        environment frame prefix noM noM′ body)
      q replace

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix noM (no•-⟨⟩ noM′)
      (⊑conv↓ᴿ conversion body q replace) =
    ⊑conv↓ᴿ
      (weaken-conceal-conversion
        (right-store-prefix-inclusionᴿ prefix) conversion)
      (smaller-parallel-term-substitution-framedᴿ
        environment frame prefix noM noM′ body)
      q replace

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (paired-revealᴿ
        corresponds source target replace body) =
    paired-revealᴿ
      (store-corresponds-prefixᴿ prefix corresponds)
      (weaken-reveal-conversion
        (left-store-prefix-inclusionᴿ prefix) source)
      (weaken-reveal-conversion
        (right-store-prefix-inclusionᴿ prefix) target)
      replace
      (smaller-parallel-term-substitution-framedᴿ
        environment frame prefix noM noM′ body)

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (paired-concealᴿ
        corresponds source target replace body) =
    paired-concealᴿ
      (store-corresponds-prefixᴿ prefix corresponds)
      (weaken-conceal-conversion
        (left-store-prefix-inclusionᴿ prefix) source)
      (weaken-conceal-conversion
        (right-store-prefix-inclusionᴿ prefix) target)
      replace
      (smaller-parallel-term-substitution-framedᴿ
        environment frame prefix noM noM′ body)

  smaller-parallel-term-substitution-framedᴿ
      environment {δ = δ} {τ = ζ} {τ′ = ζ′}
      frame prefix noN noN′
      (target-instantiationᴿ embedded)
      with subst-closedᵐ
        (typing-closedᵐ
          (forget (embedded-creation-source-typingᴱ embedded))) ζ
         | subst-closedᵐ
            (typing-closedᵐ
              (forget
                (embedded-creation-target-typingᴱ embedded))) ζ′
  smaller-parallel-term-substitution-framedᴿ
      environment {δ = δ} {τ = ζ} {τ′ = ζ′}
      frame prefix noN noN′
      (target-instantiationᴿ embedded)
      | eqN | eqN′
      rewrite eqN | eqN′ =
    term-imprecision-store-prefixᴿ prefix
      (target-instantiationᴿ embedded)
      (term-weaken ≤-refl
        (left-store-prefix-inclusionᴿ prefix)
        noN
        (smaller-imprecision-source-typingᴿ
          (target-instantiationᴿ embedded)))
      (term-weaken ≤-refl
        (right-store-prefix-inclusionᴿ prefix)
        noN′
        (smaller-imprecision-target-typingᴿ
          (target-instantiationᴿ embedded)))

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix
      (no•-⟨⟩ noN) (no•-⟨⟩ noN′)
      (closeᴿ body widening
        source-shape target-shape square compatible) =
    closeᴿ
      (smaller-parallel-quotient-substitution-framedᴿ
        environment frame prefix noN noN′ body)
      (quotient-widening-prefixᴿ prefix widening)
      source-shape target-shape square compatible

  smaller-parallel-term-substitution-framedᴿ
      environment frame prefix
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (paired-wideningᴿ
        mode seal★ source source-shape
        mode′ seal★′ target target-shape
        left-square right-square compatible body) =
    paired-wideningᴿ
      mode
      (seal★-weaken (left-store-prefix-inclusionᴿ prefix) seal★)
      (widen-weaken ≤-refl
        (left-store-prefix-inclusionᴿ prefix) source)
      source-shape
      mode′
      (seal★-weaken (right-store-prefix-inclusionᴿ prefix) seal★′)
      (widen-weaken ≤-refl
        (right-store-prefix-inclusionᴿ prefix) target)
      target-shape left-square right-square compatible
      (smaller-parallel-term-substitution-framedᴿ
        environment frame prefix noM noM′ body)

  smaller-parallel-quotient-substitution-framedᴿ
      environment frame prefix
      (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (paired-downᴿ
        body source-mode source source-shape
        target-mode target target-shape square) =
    paired-downᴿ
      (smaller-parallel-term-substitution-framedᴿ
        environment frame prefix noM noM′ body)
      (spine-mode-prefixᴿ
        (left-store-prefix-inclusionᴿ prefix) source-mode)
      (narrow-weaken ≤-refl
        (left-store-prefix-inclusionᴿ prefix) source)
      source-shape
      (spine-mode-prefixᴿ
        (right-store-prefix-inclusionᴿ prefix) target-mode)
      (narrow-weaken ≤-refl
        (right-store-prefix-inclusionᴿ prefix) target)
      target-shape square


smaller-parallel-term-substitutionᴿ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {γ δ : CtxImp Φ Δᴸ Δᴿ}
    {τ τ′ : Substˣ} {N N′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  SmallerSubstitutionEnvironmentFamilyᴿ ρ γ δ τ τ′ →
  No• N → No• N′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ N ⊑ N′ ⦂ A ⊑ B ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
    ⊢ᴿ substˣᵐ τ N ⊑ substˣᵐ τ′ N′
    ⦂ A ⊑ B ∶ p
smaller-parallel-term-substitutionᴿ environment noN noN′ N⊑N′ =
  smaller-parallel-term-substitution-framedᴿ
    environment substitution-frame-idᴿ prefix-reflᴿ
    noN noN′ N⊑N′
