module proof.Right.AllocationRuntime.NuImprecisionRightTargetAllocationSourceBulletTransportProof where

-- File Charter:
--   * Proves flat runtime-source-bullet transport across one target
--     allocation.
--   * Recurses through exactly the target-only QTI wrappers and delegates the
--     unique source-only bullet leaf to its focused transport theorem.
--   * Contains no postulate, hole, permissive option, catch-all clause, or
--     termination bypass.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; Σ; proj₂)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; rename-conceal-conversion
  ; rename-reveal-conversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import ImprecisionWf using
  ( ImpCtx
  ; ⇑ᴿᵢ
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( StoreChanges
  ; applyStores
  ; applyTerms
  ; applyTys
  ; bind
  ; keep
  )
open import NuStore using (StoreIncl-cons)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftRightStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; rightStoreⁱ-lift-right
  ; store-right
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( lift-right-ctx-[]
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-ν
  ; no•-⟨⟩
  ; ν
  ; ⇑ᵗᵐ
  ; _•
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; blame⊑ᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; closeᵀ
  ; gen⊑groundᵀ
  ; κ⊑κᵀ
  ; paired-concealᵀ
  ; paired-revealᵀ
  ; paired-wideningᵀ
  ; x⊑xᵀ
  ; Λ⊑Λᵀ
  ; Λ⊑ᵀ
  ; α⊑αᵀ
  ; α⊑ᵀ
  ; ν⊑νᵀ
  ; ν⊑ᵀ
  ; ·⊑·ᵀ
  ; target-instantiationᵀ
  ; ƛ⊑ƛᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; ⊕⊑⊕ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Store using (StoreIncl-drop)
open import TermTyping using
  (SealModeStore★; weakenCastᵈ; _∣_∣_⊢_⦂_)
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; wf★
  ; ★
  ; `∀
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( nu-term-imprecision-transport-termsᵀ
  ; replace-right-target-lift-rightᵢ
  )
open import proof.Core.Properties.NuNarrowingTransport using
  (apply-narrows-typing)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( cast-shape-applyCoercions
  ; imprecision-composition-shape-transport
  )
open import proof.Core.Properties.NuWideningTransport using
  (apply-widens-typing)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercionUnderTyBinders
  ; applyCoercions
  ; applyTerms-cast
  ; applyTerms-ν
  ; applyTys-★
  )
open import proof.Core.Properties.TypeProperties using
  (TyRenameWf-suc)
open import proof.Core.Properties.TypePreservation using
  (modeRename-suc-weakenCast; seal★-weaken)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (⊑-target-lift-rightᵢ)
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using (embedded-creation-source-valueᴱ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentTypeShapeProof
  using (shape-target-lift-rightᵢ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.Right.AllocationRuntime.NuImprecisionRightTargetAllocationSourceBulletTransportDef
  using (RightTargetAllocationSourceBulletTransportᵀ)
open import
  proof.Right.AllocationRuntime.NuImprecisionRightTargetAllocationSourceOnlyBulletTransportProof
  using
  (right-target-allocation-source-only-bullet-transport-proofᵀ)
open import proof.Store.Core.NuImprecisionStoreLift using
  (lift-right-store-result)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  ( rightStoreⁱ-prefix-inclusion
  ; store-imp-prefix-transⁱ
  )
open import NarrowWiden using
  ( narrow-weaken
  ; widen-weaken
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )


private
  allocation-changes : StoreChanges
  allocation-changes = bind ★ ∷ keep ∷ []


  no•-bullet-absurd :
    ∀ {M} → No• (M •) → ⊥
  no•-bullet-absurd ()


  value-bullet-absurd :
    ∀ {M} → Value (M •) → ⊥
  value-bullet-absurd ()


  target-store-eq :
    ∀ {Φ Δᴸ Δᴿ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
    rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ) ≡
      applyStores allocation-changes (rightStoreⁱ ρ)
  target-store-eq liftρ =
    cong ((zero , ★) ∷_) (rightStoreⁱ-lift-right liftρ)


  applyTerms-ν★ :
    ∀ χs M c →
    applyTerms χs (ν ★ M c) ≡
      ν ★ (applyTerms χs M)
        (applyCoercionUnderTyBinders χs c)
  applyTerms-ν★ χs M c =
    trans (applyTerms-ν χs ★ M c)
      (cong
        (λ A → ν A (applyTerms χs M)
          (applyCoercionUnderTyBinders χs c))
        (applyTys-★ χs))


  source-bullet-transport :
    ∀ {Φ Δᴸ Δᴿ}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
      {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
      {S L M′ : Term} {A B : Ty}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ⁺ ρᴿ⁺ →
    AssumptionMembershipUnique Φ →
    RuntimeOK ((⇑ᵗᵐ L) •) →
    No• M′ →
    Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ []
      ⊢ (⇑ᵗᵐ L) • ⦂ A →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
      ⊢ᴺ S ⊑ M′ ⦂ A ⊑ B ∶ q →
    S ≡ (⇑ᵗᵐ L) • →
    ⇑ᴿᵢ Φ ∣ Δᴸ ∣ suc Δᴿ
      ∣ store-right zero ★ wf★ ∷ ρᴿ⁺ ∣ []
      ⊢ᴺ (⇑ᵗᵐ L) • ⊑ ⇑ᵗᵐ M′
      ⦂ A ⊑ ⇑ᵗ B ∶ ⊑-target-lift-rightᵢ q

  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (allocation-prefixᵀ prefix₀ M⊑M′ M⊢₀ M′⊢) eq =
    source-bullet-transport
      (store-imp-prefix-transⁱ prefix₀ prefix)
      liftρ unique runtime noM′ M⊢ M⊑M′ eq
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (blame⊑ᵀ M′⊢) ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (x⊑xᵀ x∈) ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (ƛ⊑ƛᵀ hA hA′ N⊑N′) ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (·⊑·ᵀ L⊑L′ N⊑N′) ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (closeᵀ N⊑N′ widening p u-shape u′-shape square compatible)
      ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (Λ⊑Λᵀ liftρ∀ liftγ vV vV′ V⊑V′) ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (Λ⊑ᵀ occ liftρ∀ liftγ vV V⊑N′) ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (target-instantiationᵀ embedded)
      eq =
    ⊥-elim
      (value-bullet-absurd
        (subst Value eq (embedded-creation-source-valueᴱ embedded)))
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (α⊑αᵀ vV noV vV′ noV′ p liftρ∀ liftγ
        V⊑V′ V•⊢ V′•⊢)
      eq =
    ⊥-elim (no•-bullet-absurd noM′)
  source-bullet-transport
      {Δᴸ = Δᴸ} {ρ⁺ = ρ⁺} {L = L} {A = A}
      prefix liftρ unique runtime noM′ M⊢
      (α⊑ᵀ {L = V} vV noV hA liftρ∀
        lift-left-ctx-[]
        V⊑M′ V•⊢ M′⊢)
      eq =
    nu-term-imprecision-transport-termsᵀ eq refl
      (right-target-allocation-source-only-bullet-transport-proofᵀ
        prefix liftρ unique noM′ source-typing
        V⊑M′ vV noV liftρ∀ V•⊢)
    where
    source-typing =
      subst
        (λ N → Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ N ⦂ A)
        (sym eq) M⊢
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (ν⊑νᵀ hA hA′ s↑ s′↑ pA pA↑
        liftρ∀ liftγ N⊑N′ replacement)
      ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (ν⊑ᵀ hA hA↑ s↑ liftρ∀ liftγ N⊑N′ replacement)
      ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢ κ⊑κᵀ ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (⊕⊑⊕ᵀ L⊑L′ N⊑N′)
      ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (gen⊑groundᵀ mode seal c⊒ gH vV vW W⊢ V⊑W q)
      ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (cast⊒⊑ᵀ mode seal c⊒ N⊑N′ q c-shape comp)
      ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (cast⊑⊑ᵀ mode seal c⊑ N⊑N′ q c-shape comp)
      ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (paired-revealᵀ x∈ c↑ c′↑ replacement N⊑N′)
      ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (paired-concealᵀ x∈ c↓ c′↓ replacement N⊑N′)
      ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (paired-wideningᵀ mode seal c⊑ c-shape
        mode′ seal′ c′⊑ c′-shape square square′
        compatible N⊑N′)
      ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (conv↑⊑ᵀ c↑ N⊑N′ q replacement)
      ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (conv↓⊑ᵀ c↓ N⊑N′ q replacement)
      ()

  source-bullet-transport
      {Δᴿ = Δᴿ} {ρ⁺ = ρ⁺}
      prefix liftρ unique runtime (no•-⟨⟩ noM′) M⊢
      (⊑cast⊒ᵀ {M′ = N′} {A′ = A′} {B′ = B′} {c′ = c}
        mode seal★ c⊒ M⊑M′ q c-shape comp)
      eq
      with apply-narrows-typing
        {χs = allocation-changes}
        mode
        (seal★-weaken
          (rightStoreⁱ-prefix-inclusion prefix) seal★)
        (narrow-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) c⊒)
  source-bullet-transport
      {Δᴿ = Δᴿ} {ρ⁺ = ρ⁺}
      prefix liftρ unique runtime (no•-⟨⟩ noM′) M⊢
      (⊑cast⊒ᵀ {M′ = N′} {A′ = A′} {B′ = B′} {c′ = c}
        mode seal★ c⊒ M⊑M′ q c-shape comp)
      eq
      | mode′ , mode-ok′ , seal★′ , c′⊒ =
    nu-term-imprecision-transport-termsᵀ refl
      (sym (applyTerms-cast allocation-changes N′ c))
      (⊑cast⊒ᵀ mode-ok′ final-seal final-cast
        inner (⊑-target-lift-rightᵢ q)
        final-c-shape final-comp)
    where
    inner =
      source-bullet-transport
        prefix liftρ unique runtime noM′ M⊢ M⊑M′ eq

    final-seal =
      subst (SealModeStore★ mode′)
        (sym (target-store-eq liftρ)) seal★′

    final-cast =
      subst
        (λ Σ → mode′ ∣ suc Δᴿ ∣ Σ
          ⊢ applyCoercions allocation-changes c
          ∶ applyTys allocation-changes A′
          ⊒ applyTys allocation-changes B′)
        (sym (target-store-eq liftρ)) c′⊒

    final-c-shape =
      cast-shape-applyCoercions allocation-changes c-shape

    final-comp =
      imprecision-composition-shape-transport
        (shape-target-lift-rightᵢ q)
        refl
        (shape-target-lift-rightᵢ _)
        comp

  source-bullet-transport
      {Δᴿ = Δᴿ} {ρ⁺ = ρ⁺}
      prefix liftρ unique runtime (no•-⟨⟩ noM′) M⊢
      (⊑cast⊑ᵀ {M′ = N′} {A′ = A′} {B′ = B′} {c′ = c}
        mode seal★ c⊑ M⊑M′ q c-shape comp)
      eq
      with apply-widens-typing
        {χs = allocation-changes}
        mode
        (seal★-weaken
          (rightStoreⁱ-prefix-inclusion prefix) seal★)
        (widen-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) c⊑)
  source-bullet-transport
      {Δᴿ = Δᴿ} {ρ⁺ = ρ⁺}
      prefix liftρ unique runtime (no•-⟨⟩ noM′) M⊢
      (⊑cast⊑ᵀ {M′ = N′} {A′ = A′} {B′ = B′} {c′ = c}
        mode seal★ c⊑ M⊑M′ q c-shape comp)
      eq
      | mode′ , mode-ok′ , seal★′ , c′⊑ =
    nu-term-imprecision-transport-termsᵀ refl
      (sym (applyTerms-cast allocation-changes N′ c))
      (⊑cast⊑ᵀ mode-ok′ final-seal final-cast
        inner (⊑-target-lift-rightᵢ q)
        final-c-shape final-comp)
    where
    inner =
      source-bullet-transport
        prefix liftρ unique runtime noM′ M⊢ M⊑M′ eq

    final-seal =
      subst (SealModeStore★ mode′)
        (sym (target-store-eq liftρ)) seal★′

    final-cast =
      subst
        (λ Σ → mode′ ∣ suc Δᴿ ∣ Σ
          ⊢ applyCoercions allocation-changes c
          ∶ applyTys allocation-changes A′
          ⊑ applyTys allocation-changes B′)
        (sym (target-store-eq liftρ)) c′⊑

    final-c-shape =
      cast-shape-applyCoercions allocation-changes c-shape

    final-comp =
      imprecision-composition-shape-transport
        (shape-target-lift-rightᵢ _)
        refl
        (shape-target-lift-rightᵢ q)
        comp

  source-bullet-transport
      {Δᴿ = Δᴿ} {ρ⁺ = ρ⁺}
      prefix liftρ unique runtime (no•-⟨⟩ noM′) M⊢
      (⊑conv↑ᵀ {M′ = N′} {A′ = A′} {B′ = B′}
        {c′ = c} {μ′ = mode} {β = β} {X′ = X}
        c↑ M⊑M′ q replacement)
      eq =
    nu-term-imprecision-transport-termsᵀ refl
      (sym (applyTerms-cast allocation-changes N′ c))
      (⊑conv↑ᵀ final-conversion inner
        (⊑-target-lift-rightᵢ q)
        (replace-right-target-lift-rightᵢ replacement))
    where
    inner =
      source-bullet-transport
        prefix liftρ unique runtime noM′ M⊢ M⊑M′ eq

    final-conversion =
      subst
        (λ Σ → RevealConversion (weakenCastᵈ mode) (suc Δᴿ) Σ
          (suc β) (⇑ᵗ X)
          (applyCoercions allocation-changes c)
          (applyTys allocation-changes A′)
          (applyTys allocation-changes B′))
        (sym (target-store-eq liftρ))
        (weaken-reveal-conversion StoreIncl-drop
          (rename-reveal-conversion TyRenameWf-suc
            modeRename-suc-weakenCast
            (weaken-reveal-conversion
              (rightStoreⁱ-prefix-inclusion prefix) c↑)))

  source-bullet-transport
      {Δᴿ = Δᴿ} {ρ⁺ = ρ⁺}
      prefix liftρ unique runtime (no•-⟨⟩ noM′) M⊢
      (⊑conv↓ᵀ {M′ = N′} {A′ = A′} {B′ = B′}
        {c′ = c} {μ′ = mode} {β = β} {X′ = X}
        c↓ M⊑M′ q replacement)
      eq =
    nu-term-imprecision-transport-termsᵀ refl
      (sym (applyTerms-cast allocation-changes N′ c))
      (⊑conv↓ᵀ final-conversion inner
        (⊑-target-lift-rightᵢ q)
        (replace-right-target-lift-rightᵢ replacement))
    where
    inner =
      source-bullet-transport
        prefix liftρ unique runtime noM′ M⊢ M⊑M′ eq

    final-conversion =
      subst
        (λ Σ → ConcealConversion (weakenCastᵈ mode) (suc Δᴿ) Σ
          (suc β) (⇑ᵗ X)
          (applyCoercions allocation-changes c)
          (applyTys allocation-changes A′)
          (applyTys allocation-changes B′))
        (sym (target-store-eq liftρ))
        (weaken-conceal-conversion StoreIncl-drop
          (rename-conceal-conversion TyRenameWf-suc
            modeRename-suc-weakenCast
            (weaken-conceal-conversion
              (rightStoreⁱ-prefix-inclusion prefix) c↓)))

right-target-allocation-source-bullet-transport-proofᵀ :
  RightTargetAllocationSourceBulletTransportᵀ
right-target-allocation-source-bullet-transport-proofᵀ
    prefix liftρ unique runtime noM′ M⊢ M⊑M′ =
  source-bullet-transport
    prefix liftρ unique runtime noM′ M⊢ M⊑M′ refl
