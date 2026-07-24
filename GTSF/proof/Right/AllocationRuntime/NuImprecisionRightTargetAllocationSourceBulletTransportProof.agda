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
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import Coercions using (id-onlyᵈ; instᵈ)
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
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; lift-right-ctx-[]
  ; rightStoreⁱ
  ; rightStoreⁱ-lift-right
  ; store-right
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
  ; conv⊑convᵀ
  ; gen⊑groundᵀ
  ; κ⊑κᵀ
  ; up⊑upᵀ
  ; x⊑xᵀ
  ; Λ⊑Λᵀ
  ; Λ⊑instβᵀ
  ; Λ⊑ᵀ
  ; α⊑αᵀ
  ; α⊑ᵀ
  ; νcast⊑νcastᵀ
  ; νcast⊑ᵀ
  ; ν⊑νᵀ
  ; ν⊑ᵀ
  ; ·⊑·ᵀ
  ; ƛ⊑ƛᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; ⊑αᵀ
  ; ⊑νcastᵀ
  ; ⊑νᵀ
  ; ⊕⊑⊕ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (SealModeStore★; _∣_∣_⊢_⦂_)
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
  ( apply-conceal-conversions
  ; apply-narrows-typing
  ; apply-reveal-conversions
  ; apply-reveal-under-ty-binders
  ; apply-widen-inst-under-ty-binders
  ; nu-term-imprecision-transport-termsᵀ
  ; seal★-id-only
  ; ⊑-target-lift-under-rightᵢ
  )
open import proof.Core.Properties.CoercionProperties using
  (modeRename-id-only)
open import proof.Core.Properties.NuWideningTransport using
  (apply-fixed-widens-typing; apply-widens-typing)
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercionUnderTyBinders
  ; applyCoercions
  ; applyTerms-cast
  ; applyTerms-ν
  ; applyTys-★
  ; applyTys-∀
  ; applyTysUnderTyBinders
  ; wfTy-applyTys
  )
open import proof.Core.Properties.StoreProperties using
  (renameStoreᵗ-incl)
open import proof.Core.Properties.TypeProperties using
  (TyRenameWf-suc; renameᵗ-preserves-WfTy)
open import proof.Core.Properties.TypePreservation using
  (seal★-weaken)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (⊑-target-lift-rightᵢ)
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
      (up⊑upᵀ N⊑N′ widening p) ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (Λ⊑Λᵀ liftρ∀ liftγ vV vV′ V⊑V′) ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (Λ⊑ᵀ occ liftρ∀ liftγ vV V⊑N′) ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (Λ⊑instβᵀ prefix₀ mode seal★ inst⊑
        liftρ∀ liftρᴿ vW noW vW′ noW′ inert W⊑W′ f
        assm hτ hσ store-emb M≡ M′≡ A≡ A′≡ p
        vM noM closedM vM′ noM′₀ closedM′ M⊢₀ M′⊢)
      eq =
    ⊥-elim
      (value-bullet-absurd (subst Value eq vM))
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
        NuTermImprecision.lift-left-ctx-[]
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
      (⊑αᵀ vV′ noV′ hA liftρ∀ liftγ
        M⊑V′ r M⊢₀ V′•⊢)
      eq =
    ⊥-elim (no•-bullet-absurd noM′)
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (ν⊑νᵀ hA hA′ s↑ s′↑ pA pA↑
        liftρ∀ liftγ N⊑N′)
      ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (ν⊑ᵀ hA hA↑ s↑ liftρ∀ liftγ N⊑N′)
      ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (νcast⊑νcastᵀ mode seal mode′ seal′
        s⊑ s′⊑ compat liftρ∀ liftγ N⊑N′)
      ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (νcast⊑ᵀ mode seal s⊑ liftρ∀ liftγ N⊑N′)
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
      (cast⊒⊑ᵀ mode seal c⊒ N⊑N′ q)
      ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (cast⊑⊑ᵀ mode seal c⊑ N⊑N′ q)
      ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (conv⊑convᵀ paired N⊑N′)
      ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (conv↑⊑ᵀ c↑ N⊑N′ q)
      ()
  source-bullet-transport
      prefix liftρ unique runtime noM′ M⊢
      (conv↓⊑ᵀ c↓ N⊑N′ q)
      ()

  source-bullet-transport
      {Δᴿ = Δᴿ} {ρ⁺ = ρ⁺}
      prefix liftρ unique runtime (no•-⟨⟩ noM′) M⊢
      (⊑cast⊒ᵀ {M′ = N′} {A′ = A′} {B′ = B′} {c′ = c}
        mode seal★ c⊒ M⊑M′ q)
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
        mode seal★ c⊒ M⊑M′ q)
      eq
      | mode′ , mode-ok′ , seal★′ , c′⊒ =
    nu-term-imprecision-transport-termsᵀ refl
      (sym (applyTerms-cast allocation-changes N′ c))
      (⊑cast⊒ᵀ mode-ok′ final-seal final-cast
        inner (⊑-target-lift-rightᵢ q))
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

  source-bullet-transport
      {Δᴿ = Δᴿ} {ρ⁺ = ρ⁺}
      prefix liftρ unique runtime (no•-⟨⟩ noM′) M⊢
      (⊑cast⊑ᵀ {M′ = N′} {A′ = A′} {B′ = B′} {c′ = c}
        mode seal★ c⊑ M⊑M′ q)
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
        mode seal★ c⊑ M⊑M′ q)
      eq
      | mode′ , mode-ok′ , seal★′ , c′⊑ =
    nu-term-imprecision-transport-termsᵀ refl
      (sym (applyTerms-cast allocation-changes N′ c))
      (⊑cast⊑ᵀ mode-ok′ final-seal final-cast
        inner (⊑-target-lift-rightᵢ q))
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

  source-bullet-transport
      {Δᴿ = Δᴿ} {ρ⁺ = ρ⁺}
      prefix liftρ unique runtime (no•-⟨⟩ noM′) M⊢
      (⊑cast⊑idᵀ {M′ = N′} {A′ = A′} {B′ = B′} {c′ = c}
        seal★ c⊑ M⊑M′ q)
      eq =
    nu-term-imprecision-transport-termsᵀ refl
      (sym (applyTerms-cast allocation-changes N′ c))
      (⊑cast⊑idᵀ seal★-id-only final-cast
        inner (⊑-target-lift-rightᵢ q))
    where
    inner =
      source-bullet-transport
        prefix liftρ unique runtime noM′ M⊢ M⊑M′ eq

    transported-cast =
      apply-fixed-widens-typing
        {χs = allocation-changes}
        (modeRename-id-only suc)
        (widen-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) c⊑)

    final-cast =
      subst
        (λ Σ → id-onlyᵈ ∣ suc Δᴿ ∣ Σ
          ⊢ applyCoercions allocation-changes c
          ∶ applyTys allocation-changes A′
          ⊑ applyTys allocation-changes B′)
        (sym (target-store-eq liftρ)) transported-cast

  source-bullet-transport
      {Δᴿ = Δᴿ} {ρ⁺ = ρ⁺}
      prefix liftρ unique runtime (no•-⟨⟩ noM′) M⊢
      (⊑conv↑ᵀ {M′ = N′} {A′ = A′} {B′ = B′} {c′ = c}
        c↑ M⊑M′ q)
      eq
      with apply-reveal-conversions
        {χs = allocation-changes}
        (weaken-reveal-conversion
          (rightStoreⁱ-prefix-inclusion prefix) c↑)
  source-bullet-transport
      {Δᴿ = Δᴿ} {ρ⁺ = ρ⁺}
      prefix liftρ unique runtime (no•-⟨⟩ noM′) M⊢
      (⊑conv↑ᵀ {M′ = N′} {A′ = A′} {B′ = B′} {c′ = c}
        c↑ M⊑M′ q)
      eq
      | mode′ , α′ , X′ , c′↑ =
    nu-term-imprecision-transport-termsᵀ refl
      (sym (applyTerms-cast allocation-changes N′ c))
      (⊑conv↑ᵀ final-conversion inner
        (⊑-target-lift-rightᵢ q))
    where
    inner =
      source-bullet-transport
        prefix liftρ unique runtime noM′ M⊢ M⊑M′ eq

    final-conversion =
      subst
        (λ Σ → RevealConversion mode′ (suc Δᴿ) Σ α′ X′
          (applyCoercions allocation-changes c)
          (applyTys allocation-changes A′)
          (applyTys allocation-changes B′))
        (sym (target-store-eq liftρ)) c′↑

  source-bullet-transport
      {Δᴿ = Δᴿ} {ρ⁺ = ρ⁺}
      prefix liftρ unique runtime (no•-⟨⟩ noM′) M⊢
      (⊑conv↓ᵀ {M′ = N′} {A′ = A′} {B′ = B′} {c′ = c}
        c↓ M⊑M′ q)
      eq
      with apply-conceal-conversions
        {χs = allocation-changes}
        (weaken-conceal-conversion
          (rightStoreⁱ-prefix-inclusion prefix) c↓)
  source-bullet-transport
      {Δᴿ = Δᴿ} {ρ⁺ = ρ⁺}
      prefix liftρ unique runtime (no•-⟨⟩ noM′) M⊢
      (⊑conv↓ᵀ {M′ = N′} {A′ = A′} {B′ = B′} {c′ = c}
        c↓ M⊑M′ q)
      eq
      | mode′ , α′ , X′ , c′↓ =
    nu-term-imprecision-transport-termsᵀ refl
      (sym (applyTerms-cast allocation-changes N′ c))
      (⊑conv↓ᵀ final-conversion inner
        (⊑-target-lift-rightᵢ q))
    where
    inner =
      source-bullet-transport
        prefix liftρ unique runtime noM′ M⊢ M⊑M′ eq

    final-conversion =
      subst
        (λ Σ → ConcealConversion mode′ (suc Δᴿ) Σ α′ X′
          (applyCoercions allocation-changes c)
          (applyTys allocation-changes A′)
          (applyTys allocation-changes B′))
        (sym (target-store-eq liftρ)) c′↓

  source-bullet-transport
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ⁺ = ρ⁺} {ρᴿ⁺ = ρᴿ⁺} {L = L}
      prefix liftρ unique runtime (no•-ν noN′) M⊢
      (⊑νᵀ {A = A′} {B = B} {B′ = B′}
        {C′ = C′} {N′ = N′} {q = q₀} {s = s}
        hA h⇑A s↑ liftρ∀ liftγ r N⊑N′)
      eq
      with lift-right-store-result
        (store-right zero ★ wf★ ∷ _)
  source-bullet-transport
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ⁺ = ρ⁺} {ρᴿ⁺ = ρᴿ⁺} {L = L}
      prefix liftρ unique runtime (no•-ν noN′) M⊢
      (⊑νᵀ {A = A′} {B = B} {B′ = B′}
        {C′ = C′} {N′ = N′} {q = q₀} {s = s}
        hA h⇑A s↑ liftρ∀ liftγ r N⊑N′)
      eq
      | ρ′ , liftρ′
      with apply-reveal-under-ty-binders
        {χs = allocation-changes}
        (weaken-reveal-conversion binder-incl s↑)
    where
    binder-incl =
      StoreIncl-cons
        (renameStoreᵗ-incl suc
          (rightStoreⁱ-prefix-inclusion prefix))
  source-bullet-transport
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ⁺ = ρ⁺} {ρᴿ⁺ = ρᴿ⁺} {L = L}
      prefix liftρ unique runtime (no•-ν noN′) M⊢
      (⊑νᵀ {A = A′} {B = B} {B′ = B′}
        {C′ = C′} {N′ = N′} {q = q₀} {s = s}
        hA h⇑A s↑ liftρ∀ liftγ r N⊑N′)
      eq
      | ρ′ , liftρ′
      | mode′ , target↑ =
    nu-term-imprecision-transport-termsᵀ refl
      (sym (applyTerms-ν allocation-changes A′ N′ s))
      (⊑νᵀ final-wf final-shift-wf target-reveal
        liftρ′ lift-right-ctx-[]
        (⊑-target-lift-under-rightᵢ r)
        (proj₂ inner-all))
    where
    inner =
      source-bullet-transport
        prefix liftρ unique runtime noN′ M⊢ N⊑N′ eq

    inner-all =
      subst
        (λ T →
          Σ (⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ T ⊣ suc Δᴿ) (λ p →
            ⇑ᴿᵢ Φ ∣ Δᴸ ∣ suc Δᴿ
              ∣ store-right zero ★ wf★ ∷ ρᴿ⁺ ∣ []
              ⊢ᴺ (⇑ᵗᵐ L) • ⊑ ⇑ᵗᵐ N′
              ⦂ B ⊑ T ∶ p))
        (applyTys-∀ allocation-changes C′)
        (⊑-target-lift-rightᵢ q₀ , inner)

    final-wf = wfTy-applyTys allocation-changes hA

    final-shift-wf =
      renameᵗ-preserves-WfTy final-wf TyRenameWf-suc

    target-reveal =
      subst
        (λ Σ → RevealConversion mode′ (suc (suc Δᴿ))
          ((zero , ⇑ᵗ (applyTys allocation-changes A′)) ∷
            ⟰ᵗ Σ)
          zero (⇑ᵗ (applyTys allocation-changes A′))
          (applyCoercionUnderTyBinders allocation-changes s)
          (applyTysUnderTyBinders allocation-changes C′)
          (⇑ᵗ (applyTys allocation-changes B′)))
        (sym (target-store-eq liftρ)) target↑

  source-bullet-transport
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ⁺ = ρ⁺} {ρᴿ⁺ = ρᴿ⁺} {L = L}
      prefix liftρ unique runtime (no•-ν noN′) M⊢
      (⊑νcastᵀ {B = B} {B′ = B′} {C′ = C′}
        {N′ = N′} {q = q₀} {s = s}
        mode seal★ s⊑ liftρ∀ liftγ r N⊑N′)
      eq
      with lift-right-store-result
        (store-right zero ★ wf★ ∷ _)
  source-bullet-transport
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ⁺ = ρ⁺} {ρᴿ⁺ = ρᴿ⁺} {L = L}
      prefix liftρ unique runtime (no•-ν noN′) M⊢
      (⊑νcastᵀ {B = B} {B′ = B′} {C′ = C′}
        {N′ = N′} {q = q₀} {s = s}
        mode seal★ s⊑ liftρ∀ liftγ r N⊑N′)
      eq
      | ρ′ , liftρ′
      with apply-widen-inst-under-ty-binders
        {χs = allocation-changes}
        mode
        (seal★-weaken binder-incl seal★)
        (widen-weaken ≤-refl binder-incl s⊑)
    where
    binder-incl =
      StoreIncl-cons
        (renameStoreᵗ-incl suc
          (rightStoreⁱ-prefix-inclusion prefix))
  source-bullet-transport
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ⁺ = ρ⁺} {ρᴿ⁺ = ρᴿ⁺} {L = L}
      prefix liftρ unique runtime (no•-ν noN′) M⊢
      (⊑νcastᵀ {B = B} {B′ = B′} {C′ = C′}
        {N′ = N′} {q = q₀} {s = s}
        mode seal★ s⊑ liftρ∀ liftγ r N⊑N′)
      eq
      | ρ′ , liftρ′
      | mode′ , mode-ok′ , seal★′ , target⊑ =
    nu-term-imprecision-transport-termsᵀ refl
      (sym (applyTerms-ν★ allocation-changes _ _))
      (⊑νcastᵀ mode-ok′ target-seal target-widen
        liftρ′ lift-right-ctx-[]
        (⊑-target-lift-under-rightᵢ r)
        (proj₂ inner-all))
    where
    inner =
      source-bullet-transport
        prefix liftρ unique runtime noN′ M⊢ N⊑N′ eq

    inner-all =
      subst
        (λ T →
          Σ (⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ T ⊣ suc Δᴿ) (λ p →
            ⇑ᴿᵢ Φ ∣ Δᴸ ∣ suc Δᴿ
              ∣ store-right zero ★ wf★ ∷ ρᴿ⁺ ∣ []
              ⊢ᴺ (⇑ᵗᵐ L) • ⊑ ⇑ᵗᵐ N′
              ⦂ B ⊑ T ∶ p))
        (applyTys-∀ allocation-changes C′)
        (⊑-target-lift-rightᵢ q₀ , inner)

    target-seal =
      subst
        (λ Σ → SealModeStore★ (instᵈ mode′)
          ((zero , ★) ∷ ⟰ᵗ Σ))
        (sym (target-store-eq liftρ)) seal★′

    target-widen =
      subst
        (λ Σ → instᵈ mode′ ∣ suc (suc Δᴿ)
          ∣ (zero , ★) ∷ ⟰ᵗ Σ
          ⊢ applyCoercionUnderTyBinders allocation-changes s
          ∶ applyTysUnderTyBinders allocation-changes C′
          ⊑ ⇑ᵗ (applyTys allocation-changes B′))
        (sym (target-store-eq liftρ)) target⊑


right-target-allocation-source-bullet-transport-proofᵀ :
  RightTargetAllocationSourceBulletTransportᵀ
right-target-allocation-source-bullet-transport-proofᵀ
    prefix liftρ unique runtime noM′ M⊢ M⊑M′ =
  source-bullet-transport
    prefix liftρ unique runtime noM′ M⊢ M⊑M′ refl
