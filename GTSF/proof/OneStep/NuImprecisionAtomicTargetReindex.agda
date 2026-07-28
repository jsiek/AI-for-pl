module proof.OneStep.NuImprecisionAtomicTargetReindex where

-- File Charter:
--   * Reindexes ordinary quotiented-term imprecision at atomic target types
--     when the target term is a value.
--   * Reconstructs proof-relevant type-imprecision indices structurally;
--     it does not assume proof irrelevance.
--   * Supplies the strict support theorem for target identity conversions.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using
  ( ⌊_⌋
  ; _；⌊_⌋≋ᵖ_；_
  ; quotient-boundary-square
  )
open import ImprecisionWf using
  ( _∣_⊢_⊑_⊣_
  ; idι
  ; ν
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  )
open import NuTerms using (Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( blame⊑ᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; closeᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; gen⊑groundᵀ
  ; paired-concealᵀ
  ; paired-revealᵀ
  ; paired-wideningᵀ
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
  ; target-instantiationᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Atom)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import proof.Compilation.GenSafeProperties using
  (genSafeShape-atomic-impossible)
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
  ; shape-source-liftνᵢ
  ; target-atom-shape-unique
  )
open import
  QuotientImprecisionCompatibility
  using
  ( reduction-closed-paired-compatible-shape-transport
  ; reduction-closed-quotient-compatible-result-shape-transport
  )
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using (embedded-creation-target-shapeᴱ)


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


atomic-target-value-reindexᵀ :
  ∀ {Φ Δᴸ Δᴿ M V A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Atom B →
  Value V →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ M ⊑ V ⦂ A ⊑ B ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ M ⊑ V ⦂ A ⊑ B ∶ q
atomic-target-value-reindexᵀ atom vV (blame⊑ᵀ V⊢) q =
  blame⊑ᵀ V⊢
atomic-target-value-reindexᵀ atom () (x⊑xᵀ x∈) q
atomic-target-value-reindexᵀ () vV (ƛ⊑ƛᵀ hA hA′ N⊑N′) q
atomic-target-value-reindexᵀ atom () (·⊑·ᵀ L⊑L′ M⊑M′) q
atomic-target-value-reindexᵀ {p = p} atom vV
    (closeᵀ N⊑N′ widening p
      source-shape target-shape square compatible) q =
  closeᵀ N⊑N′ widening q source-shape target-shape
    (quotient-boundary-ordinary-reindex
      (target-atom-shape-unique atom p q) square)
    (reduction-closed-quotient-compatible-result-shape-transport
      (sym (target-atom-shape-unique atom p q)) compatible)
atomic-target-value-reindexᵀ () vV
    (Λ⊑Λᵀ liftρ liftγ vW vW′ W⊑W′) q
atomic-target-value-reindexᵀ atom vV
    (Λ⊑ᵀ {{safe}} occ liftρ liftγ vW W⊑V)
    (ν safe′ occ′ q) =
  Λ⊑ᵀ {{safe = safe′}} occ′ liftρ liftγ vW
    (atomic-target-value-reindexᵀ atom vV W⊑V q)
atomic-target-value-reindexᵀ atom vV
    (target-instantiationᵀ embedded)
    p′ =
  ⊥-elim
    (genSafeShape-atomic-impossible
      (embedded-creation-target-shapeᴱ embedded) atom)
atomic-target-value-reindexᵀ atom ()
    (α⊑αᵀ vL noL vL′ noL′ p↑ liftρ liftγ
      L⊑L′ allocation-prefix L•⊢ L′•⊢) q
atomic-target-value-reindexᵀ atom vV
    (α⊑ᵀ {occ = occ} {{safe = safe}} vL noL hA liftρ liftγ
      L⊑V allocation-prefix L•⊢ V⊢) q =
  α⊑ᵀ {{safe = safe}} vL noL hA liftρ liftγ
    (atomic-target-value-reindexᵀ atom vV L⊑V
      (ν safe occ q))
    allocation-prefix L•⊢ V⊢
atomic-target-value-reindexᵀ atom ()
    (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ p↑ liftρ liftγ N⊑N′
      replacement) q
atomic-target-value-reindexᵀ {p = p} atom vV
    (ν⊑ᵀ hA hA↑ s↑ liftρ liftγ N⊑V replacement) q =
  ν⊑ᵀ hA hA↑ s↑ liftρ liftγ N⊑V
    (replace-left-target-shape
      (trans
        (shape-source-liftνᵢ q)
        (trans
          (sym (target-atom-shape-unique atom p q))
          (sym (shape-source-liftνᵢ p))))
      replacement)
atomic-target-value-reindexᵀ atom vV κ⊑κᵀ idι =
  κ⊑κᵀ
atomic-target-value-reindexᵀ atom ()
    (⊕⊑⊕ᵀ L⊑L′ M⊑M′) q
atomic-target-value-reindexᵀ atom vV
    (gen⊑groundᵀ mode seal★ c⊒ gH vW vV′ V′⊢
      W⊑V′tag p) q =
  gen⊑groundᵀ mode seal★ c⊒ gH vW vV′ V′⊢
    W⊑V′tag q
atomic-target-value-reindexᵀ atom vV
    (cast⊒⊑ᵀ mode seal★ c⊒ M⊑V p c-shape comp) q =
  cast⊒⊑ᵀ mode seal★ c⊒ M⊑V q c-shape
    (imprecision-composition-shape-transport
      refl refl
      (sym (target-atom-shape-unique atom p q))
      comp)
atomic-target-value-reindexᵀ atom vV
    (cast⊑⊑ᵀ mode seal★ c⊑ M⊑V p c-shape comp) q =
  cast⊑⊑ᵀ mode seal★ c⊑ M⊑V q c-shape
    (imprecision-composition-shape-transport
      refl
      (sym (target-atom-shape-unique atom p q))
      refl comp)
atomic-target-value-reindexᵀ atom vV
    (⊑cast⊒ᵀ mode seal★ c⊒ M⊑V p c-shape comp) q =
  ⊑cast⊒ᵀ mode seal★ c⊒ M⊑V q c-shape
    (imprecision-composition-shape-transport
      (sym (target-atom-shape-unique atom p q))
      refl refl comp)
atomic-target-value-reindexᵀ atom vV
    (⊑cast⊑ᵀ mode seal★ c⊑ M⊑V p c-shape comp) q =
  ⊑cast⊑ᵀ mode seal★ c⊑ M⊑V q c-shape
    (imprecision-composition-shape-transport
      refl refl
      (sym (target-atom-shape-unique atom p q))
      comp)
atomic-target-value-reindexᵀ atom vV
    (conv↑⊑ᵀ c↑ M⊑V p replacement) q =
  conv↑⊑ᵀ c↑ M⊑V q
    (replace-left-target-shape
      (sym (target-atom-shape-unique atom p q))
      replacement)
atomic-target-value-reindexᵀ atom vV
    (conv↓⊑ᵀ c↓ M⊑V p replacement) q =
  conv↓⊑ᵀ c↓ M⊑V q
    (replace-left-source-shape
      (sym (target-atom-shape-unique atom p q))
      replacement)
atomic-target-value-reindexᵀ atom vV
    (⊑conv↑ᵀ c↑ M⊑V p replacement) q =
  ⊑conv↑ᵀ c↑ M⊑V q
    (replace-right-target-shape
      (sym (target-atom-shape-unique atom p q))
      replacement)
atomic-target-value-reindexᵀ atom vV
    (⊑conv↓ᵀ c↓ M⊑V p replacement) q =
  ⊑conv↓ᵀ c↓ M⊑V q
    (replace-right-source-shape
      (sym (target-atom-shape-unique atom p q))
      replacement)
atomic-target-value-reindexᵀ {p = p} atom vV
    (paired-revealᵀ corr c↑ c′↑ replacement M⊑V) q =
  paired-revealᵀ corr c↑ c′↑
    (replace-paired-target-shape
      (sym (target-atom-shape-unique atom p q))
      replacement)
    M⊑V
atomic-target-value-reindexᵀ {p = p} atom vV
    (paired-concealᵀ corr c↓ c′↓ replacement M⊑V) q =
  paired-concealᵀ corr c↓ c′↓
    (replace-paired-source-shape
      (sym (target-atom-shape-unique atom p q))
      replacement)
    M⊑V
atomic-target-value-reindexᵀ {p = p} atom vV
    (paired-wideningᵀ
      mode seal★ c⊑ c-shape
      mode′ seal★′ c′⊑ c′-shape
      left-square right-square compatible M⊑V) q =
  paired-wideningᵀ
    mode seal★ c⊑ c-shape
    mode′ seal★′ c′⊑ c′-shape
    (imprecision-composition-shape-transport
      refl
      (sym (target-atom-shape-unique atom p q))
      refl left-square)
    right-square
    (reduction-closed-paired-compatible-shape-transport
      refl
      (sym (target-atom-shape-unique atom p q))
      compatible)
    M⊑V
