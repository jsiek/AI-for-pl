module proof.Right.AllocationRuntime.NuImprecisionRightTargetAllocationSourceOnlyBulletTransportProof where

-- File Charter:
--   * Proves the source-only runtime-bullet base case across a target
--     allocation.
--   * Factors administrative store prefixes before commuting the source and
--     target allocation lifts at the unique `α⊑ᵀ` leaf.
--   * Uses assumption-membership uniqueness to align the proof-relevant raw
--     target-lift index after transporting the crossed world.
--   * Contains no postulate, hole, permissive option, catch-all clause, or
--     termination bypass.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-irrelevant; ≤-refl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; ⇑ᴿᵢ
  ; _∣_⊢_⊑_⊣_
  )
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; leftStoreⁱ-lift-right
  ; lift-right-store-left
  ; rightStoreⁱ
  ; store-left
  ; store-right
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; renameᵗᵐ
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
  ; nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  ; up⊑upᵀ
  ; x⊑xᵀ
  ; Λ⊑Λᵀ
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
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; wfBase
  ; wfVar
  ; wf⇒
  ; wf∀
  ; wf★
  ; ★
  ; ⇑ᵗ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulation using
  (right-lift-prefix-bodyᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( left-right-store-factorⁱ
  ; nu-term-imprecision-transport-termsᵀ
  ; right-target-square-α⊑ᵀ
  ; right-under-left-ctx-eq
  ; ⊑-target-lift-right-ν-shapeᵢ
  )
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-No•)
open import proof.Core.Properties.TypePreservation using
  (term-weaken)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (⊑-target-lift-rightᵢ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using
  ( AssumptionMembershipUnique
  ; PrecisionIndexUnique
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessLemma
  using (assumption-membership-unique→precision-index-unique)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof
  using (assumption-membership-unique-⇑ᴿᵢ)
open import
  proof.Right.AllocationRuntime.NuImprecisionRightTargetAllocationSourceOnlyBulletTransportDef
  using (RightTargetAllocationSourceOnlyBulletTransportᵀ)
open import
  proof.Right.StorePrefix.NuImprecisionRightStorePrefixFactorLemma
  using (right-store-prefix-factorᵀ)
open import
  proof.Source.Core.NuImprecisionSourceOnlyContextDrop
  using (assumption-membership-unique-drop-source-only)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  ( rightStoreⁱ-prefix-inclusion
  ; store-imp-prefix-transⁱ
  )


private
  wfTy-unique :
    ∀ {Δ A} (h h′ : WfTy Δ A) → h ≡ h′
  wfTy-unique (wfVar X<Δ) (wfVar X<Δ′) =
    cong wfVar (≤-irrelevant X<Δ X<Δ′)
  wfTy-unique wfBase wfBase = refl
  wfTy-unique wf★ wf★ = refl
  wfTy-unique (wf⇒ hA hB) (wf⇒ hA′ hB′) =
    cong₂ wf⇒ (wfTy-unique hA hA′) (wfTy-unique hB hB′)
  wfTy-unique (wf∀ hA) (wf∀ hA′) =
    cong wf∀ (wfTy-unique hA hA′)


  transport-lift-right-store-forward :
    ∀ {Φ Ψ Ω : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      (eq : Ψ ≡ Ω)
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρΨ : StoreImp Ψ Δᴸ (suc Δᴿ)} →
    LiftRightStoreⁱ Ψ ρ ρΨ →
    LiftRightStoreⁱ Ω ρ
      (subst (λ Θ → StoreImp Θ Δᴸ (suc Δᴿ)) eq ρΨ)
  transport-lift-right-store-forward refl liftρ = liftρ


  transport-qti-world-back :
    ∀ {Ψ Ω : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      (eq : Ψ ≡ Ω)
      {ρΩ : StoreImp Ω Δᴸ Δᴿ}
      {M M′ : Term} {A B : Ty}
      {pΩ : Ω ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    Ω ∣ Δᴸ ∣ Δᴿ ∣ ρΩ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ pΩ →
    Ψ ∣ Δᴸ ∣ Δᴿ
      ∣ subst (λ Θ → StoreImp Θ Δᴸ Δᴿ) (sym eq) ρΩ
      ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B
      ∶ subst (λ Θ → Θ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ)
          (sym eq) pΩ
  transport-qti-world-back refl M⊑M′ = M⊑M′


  crossed-left-store-roundtrip :
    ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      (eq : Φ ≡ Ψ)
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {α A} {hA : WfTy Δᴸ A} →
    subst (λ Θ → StoreImp Θ Δᴸ Δᴿ) (sym eq)
      (store-left α A hA ∷
        subst (λ Θ → StoreImp Θ Δᴸ Δᴿ) eq ρ)
      ≡ store-left α A hA ∷ ρ
  crossed-left-store-roundtrip refl = refl


  qti-reindex :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {M M′ : Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    PrecisionIndexUnique Φ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    (q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ q
  qti-reindex {p = p} unique M⊑M′ q with unique p q
  qti-reindex {p = p} unique M⊑M′ q | refl = M⊑M′


right-target-allocation-source-only-bullet-transport-proofᵀ :
  RightTargetAllocationSourceOnlyBulletTransportᵀ
right-target-allocation-source-only-bullet-transport-proofᵀ
      {Φ₀ = Φ₀} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ₀ = ρ₀} {ρᴸ = ρᴸ} {ρᴿ⁺ = ρᴿ⁺}
      {L = L} {M′ = M′} {A = A} {B′ = B′} {C = C}
      {h⇑A = h⇑A} {p = p} {{safe}} {occ}
      prefix liftρ unique noM′ L•⊢⁺ L⊑M′
      vL noL liftᴸρ L•⊢
      with right-store-prefix-factorᵀ prefix liftρ
right-target-allocation-source-only-bullet-transport-proofᵀ
      {Φ₀ = Φ₀} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ₀ = ρ₀} {ρᴸ = ρᴸ} {ρᴿ⁺ = ρᴿ⁺}
      {L = L} {M′ = M′} {A = A} {B′ = B′} {C = C}
      {h⇑A = h⇑A} {p = p} {{safe}} {occ}
      prefix liftρ unique noM′ L•⊢⁺ L⊑M′
      vL noL liftᴸρ L•⊢
      | ρ₀ᴿ ,
        lift-right-store-left {hA′ = h⇑A′} liftᴿρᴸ ,
        prefixᴿ
      with left-right-store-factorⁱ liftᴸρ natural-lift
    where
    eq = right-under-left-ctx-eq Φ₀

    natural-lift =
      transport-lift-right-store-forward eq liftᴿρᴸ
right-target-allocation-source-only-bullet-transport-proofᵀ
      {Φ₀ = Φ₀} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ₀ = ρ₀} {ρᴸ = ρᴸ} {ρᴿ⁺ = ρᴿ⁺}
      {L = L} {M′ = M′} {A = A} {B′ = B′} {C = C}
      {h⇑A = h⇑A} {p = p} {{safe}} {occ}
      prefix liftρ unique noM′ L•⊢⁺ L⊑M′
      vL noL liftᴸρ L•⊢
      | ρ₀ᴿ ,
        lift-right-store-left {hA′ = h⇑A′} liftᴿρᴸ ,
        prefixᴿ
      | ρᴿ , rightᴸρ , leftᴿρ
      with ⊑-target-lift-right-ν-shapeᵢ occ
right-target-allocation-source-only-bullet-transport-proofᵀ
      {Φ₀ = Φ₀} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {ρ₀ = ρ₀} {ρᴸ = ρᴸ} {ρᴿ⁺ = ρᴿ⁺}
      {L = L} {M′ = M′} {A = A} {B′ = B′} {C = C}
      {h⇑A = h⇑A} {p = p} {{safe}} {occ}
      prefix liftρ unique noM′ L•⊢⁺ L⊑M′
      vL noL liftᴸρ L•⊢
      | ρ₀ᴿ ,
        lift-right-store-left {hA′ = h⇑A′} liftᴿρᴸ ,
        prefixᴿ
      | ρᴿ , rightᴸρ , leftᴿρ
      | occ′ , index-eq =
    allocation-prefixᵀ (prefix-∷ⁱ prefixᴿ) aligned
      source-typing target-typing
    where
    eq = right-under-left-ctx-eq Φ₀

    natural-lift =
      transport-lift-right-store-forward eq liftᴿρᴸ

    lifted-body =
      right-lift-prefix-bodyᵀ rightᴸρ prefix-reflⁱ
        noL noM′ L⊑M′

    body =
      subst
        (λ r → ⇑ᴿᵢ Φ₀ ∣ Δᴸ ∣ suc Δᴿ ∣ ρᴿ ∣ []
          ⊢ᴺ L ⊑ ⇑ᵗᵐ M′ ⦂ Types.`∀ C ⊑ ⇑ᵗ B′ ∶ r)
        index-eq lifted-body

    natural =
      right-target-square-α⊑ᵀ
        vL noL h⇑A natural-lift leftᴿρ body L•⊢

    transported =
      transport-qti-world-back eq natural

    store-eq =
      trans
        (crossed-left-store-roundtrip eq)
        (cong
          (λ h → store-left zero (⇑ᵗ A) h ∷ _)
          (wfTy-unique h⇑A h⇑A′))

    store-aligned =
      subst
        (λ ρ → _ ∣ _ ∣ _ ∣ ρ ∣ []
          ⊢ᴺ (⇑ᵗᵐ L) • ⊑ ⇑ᵗᵐ M′
          ⦂ C ⊑ ⇑ᵗ B′ ∶ _)
        store-eq transported

    precision =
      assumption-membership-unique→precision-index-unique
        (assumption-membership-unique-⇑ᴿᵢ unique)

    aligned =
      qti-reindex precision store-aligned
        (⊑-target-lift-rightᵢ p)

    source-typing =
      subst
        (λ Σ → suc Δᴸ ∣ Σ ∣ []
          ⊢ (⇑ᵗᵐ L) • ⦂ C)
        (sym (leftStoreⁱ-lift-right liftρ)) L•⊢⁺

    target-typing =
      term-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion
          (prefix-∷ⁱ
            {entry = store-right zero ★ wf★} prefixᴿ))
        (renameᵗᵐ-preserves-No• suc noM′)
        (nu-term-imprecision-target-typing aligned)
