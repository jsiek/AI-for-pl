module proof.OneStep.NuImprecisionAtomicSourceReindex where

-- File Charter:
--   * Reindexes ordinary quotiented-term imprecision at atomic source types
--     when the source term is a value.
--   * Reconstructs proof-relevant type-imprecision indices structurally;
--     it does not assume proof irrelevance.
--   * Supplies strict support for source identity conversions.

open import Agda.Builtin.Equality using (_≡_; refl)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using
  ( ⌊_⌋
  ; _；⌊_⌋≋ᵖ_；_
  ; quotient-boundary-square
  )
open import ImprecisionWf using
  ( _∣_⊢_⊑_⊣_
  ; idι
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  (StoreImp)
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  (CtxImp)
open import NuTerms using (Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; blame⊑ᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; closeᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; gen⊑groundᵀ
  ; paired-concealᵀ
  ; paired-revealᵀ
  ; paired-wideningᵀ
  ; target-instantiationᵀ
  ; x⊑xᵀ
  ; Λ⊑Λᵀ
  ; Λ⊑ᵀ
  ; α⊑αᵀ
  ; α⊑ᵀ
  ; κ⊑κᵀ
  ; ν⊑νᵀ
  ; ν⊑ᵀ
  ; ·⊑·ᵀ
  ; ƛ⊑ƛᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; ⊕⊑⊕ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Relation.Binary.PropositionalEquality using (sym)
open import Types using (Atom)
open import
  proof.Core.Properties.ConversionIndexCompatibilityProperties
  using
  ( replace-left-source-shape
  ; replace-left-target-shape
  ; replace-paired-source-shape
  ; replace-paired-target-shape
  ; replace-right-source-shape
  ; replace-right-target-shape
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( imprecision-composition-shape-transport
  ; source-atom-shape-unique
  )
open import QuotientImprecisionCompatibility using
  ( reduction-closed-paired-compatible-shape-transport
  ; reduction-closed-quotient-compatible-result-shape-transport
  )


private
  quotient-boundary-ordinary-reindex :
    ∀ {Φ Δᴸ Δᴿ A A′ B B′}
      {p q : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {r : Φ ∣ Δᴸ ⊢ B ⊑ᵖ B′ ⊣ Δᴿ}
      {s s′} →
    ⌊ p ⌋ ≡ ⌊ q ⌋ →
    s ；⌊ p ⌋≋ᵖ r ； s′ →
    s ；⌊ q ⌋≋ᵖ r ； s′
  quotient-boundary-ordinary-reindex eq
      (quotient-boundary-square
        source-shape left-composition target-shape right-composition) =
    quotient-boundary-square
      source-shape
      (imprecision-composition-shape-transport
        refl (sym eq) refl left-composition)
      target-shape
      right-composition


atomic-source-value-reindexᵀ :
  ∀ {Φ Δᴸ Δᴿ V M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Atom A →
  Value V →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ q
atomic-source-value-reindexᵀ atom () (blame⊑ᵀ M′⊢) q
atomic-source-value-reindexᵀ atom () (x⊑xᵀ x∈) q
atomic-source-value-reindexᵀ () vV
    (ƛ⊑ƛᵀ hA hA′ N⊑N′) q
atomic-source-value-reindexᵀ atom ()
    (·⊑·ᵀ L⊑L′ M⊑M′) q
atomic-source-value-reindexᵀ {p = p} atom vV
    (closeᵀ N⊑N′ widening p
      source-shape target-shape square compatible) q =
  closeᵀ N⊑N′ widening q source-shape target-shape
    (quotient-boundary-ordinary-reindex
      (source-atom-shape-unique atom p q) square)
    (reduction-closed-quotient-compatible-result-shape-transport
      (sym (source-atom-shape-unique atom p q)) compatible)
atomic-source-value-reindexᵀ () vV
    (Λ⊑Λᵀ liftρ liftγ vW vW′ W⊑W′) q
atomic-source-value-reindexᵀ () vV
    (Λ⊑ᵀ occ liftρ liftγ vW W⊑M′) q
atomic-source-value-reindexᵀ () vV
    (target-instantiationᵀ embedded) q
atomic-source-value-reindexᵀ atom ()
    (α⊑αᵀ vL noL vL′ noL′ p↑ liftρ liftγ
      L⊑L′ L•⊢ L′•⊢) q
atomic-source-value-reindexᵀ atom ()
    (α⊑ᵀ vL noL hA liftρ liftγ
      L⊑M′ L•⊢ M′⊢) q
atomic-source-value-reindexᵀ atom vV
    (allocation-prefixᵀ prefix V⊑M′ V⊢ M′⊢) q =
  allocation-prefixᵀ prefix
    (atomic-source-value-reindexᵀ atom vV V⊑M′ q)
    V⊢ M′⊢
atomic-source-value-reindexᵀ atom ()
    (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ p↑ liftρ liftγ
      N⊑N′ replacement) q
atomic-source-value-reindexᵀ atom ()
    (ν⊑ᵀ hA hA↑ s↑ liftρ liftγ N⊑N′ replacement) q
atomic-source-value-reindexᵀ atom vV κ⊑κᵀ idι =
  κ⊑κᵀ
atomic-source-value-reindexᵀ atom ()
    (⊕⊑⊕ᵀ L⊑L′ M⊑M′) q
atomic-source-value-reindexᵀ () vV
    (gen⊑groundᵀ mode seal★ c⊒ gH vW vW′ W′⊢
      W⊑W′tag p) q
atomic-source-value-reindexᵀ atom vV
    (cast⊒⊑ᵀ mode seal★ c⊒ V⊑M′ p c-shape comp) q =
  cast⊒⊑ᵀ mode seal★ c⊒ V⊑M′ q c-shape
    (imprecision-composition-shape-transport
      refl refl
      (sym (source-atom-shape-unique atom p q))
      comp)
atomic-source-value-reindexᵀ atom vV
    (cast⊑⊑ᵀ mode seal★ c⊑ V⊑M′ p c-shape comp) q =
  cast⊑⊑ᵀ mode seal★ c⊑ V⊑M′ q c-shape
    (imprecision-composition-shape-transport
      refl
      (sym (source-atom-shape-unique atom p q))
      refl comp)
atomic-source-value-reindexᵀ atom vV
    (⊑cast⊒ᵀ mode seal★ c⊒ V⊑M′ p c-shape comp) q =
  ⊑cast⊒ᵀ mode seal★ c⊒ V⊑M′ q c-shape
    (imprecision-composition-shape-transport
      (sym (source-atom-shape-unique atom p q))
      refl refl comp)
atomic-source-value-reindexᵀ atom vV
    (⊑cast⊑ᵀ mode seal★ c⊑ V⊑M′ p c-shape comp) q =
  ⊑cast⊑ᵀ mode seal★ c⊑ V⊑M′ q c-shape
    (imprecision-composition-shape-transport
      refl refl
      (sym (source-atom-shape-unique atom p q))
      comp)
atomic-source-value-reindexᵀ atom vV
    (conv↑⊑ᵀ c↑ V⊑M′ p replacement) q =
  conv↑⊑ᵀ c↑ V⊑M′ q
    (replace-left-target-shape
      (sym (source-atom-shape-unique atom p q))
      replacement)
atomic-source-value-reindexᵀ atom vV
    (conv↓⊑ᵀ c↓ V⊑M′ p replacement) q =
  conv↓⊑ᵀ c↓ V⊑M′ q
    (replace-left-source-shape
      (sym (source-atom-shape-unique atom p q))
      replacement)
atomic-source-value-reindexᵀ atom vV
    (⊑conv↑ᵀ c↑ V⊑M′ p replacement) q =
  ⊑conv↑ᵀ c↑ V⊑M′ q
    (replace-right-target-shape
      (sym (source-atom-shape-unique atom p q))
      replacement)
atomic-source-value-reindexᵀ atom vV
    (⊑conv↓ᵀ c↓ V⊑M′ p replacement) q =
  ⊑conv↓ᵀ c↓ V⊑M′ q
    (replace-right-source-shape
      (sym (source-atom-shape-unique atom p q))
      replacement)
atomic-source-value-reindexᵀ {p = p} atom vV
    (paired-revealᵀ corr c↑ c′↑ replacement V⊑M′) q =
  paired-revealᵀ corr c↑ c′↑
    (replace-paired-target-shape
      (sym (source-atom-shape-unique atom p q))
      replacement)
    V⊑M′
atomic-source-value-reindexᵀ {p = p} atom vV
    (paired-concealᵀ corr c↓ c′↓ replacement V⊑M′) q =
  paired-concealᵀ corr c↓ c′↓
    (replace-paired-source-shape
      (sym (source-atom-shape-unique atom p q))
      replacement)
    V⊑M′
atomic-source-value-reindexᵀ {p = p} atom vV
    (paired-wideningᵀ
      mode seal★ c⊑ c-shape
      mode′ seal★′ c′⊑ c′-shape
      left-square right-square compatible V⊑M′) q =
  paired-wideningᵀ
    mode seal★ c⊑ c-shape
    mode′ seal★′ c′⊑ c′-shape
    (imprecision-composition-shape-transport
      refl
      (sym (source-atom-shape-unique atom p q))
      refl left-square)
    right-square
    (reduction-closed-paired-compatible-shape-transport
      refl
      (sym (source-atom-shape-unique atom p q))
      compatible)
    V⊑M′
