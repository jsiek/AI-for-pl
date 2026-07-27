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
open import NuTermImprecision using
  (CtxImp; StoreImp)
open import NuTerms using (Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( PairedCast
  ; allocation-prefixᵀ
  ; blame⊑ᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; conv⊑convᵀ
  ; down·up⊑down·upᵀ
  ; gen⊑groundᵀ
  ; up⊑upᵀ
  ; x⊑xᵀ
  ; Λ⊑Λᵀ
  ; Λ⊑ᵀ
  ; α⊑αᵀ
  ; α⊑ᵀ
  ; κ⊑κᵀ
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
  ; replace-right-source-shape
  ; replace-right-target-shape
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( imprecision-composition-shape-transport
  ; shape-source-liftνᵢ
  ; target-atom-shape-unique
  )
open import
  proof.NuCore.Relations.NuImprecisionPairedCastResultShape
  using (paired-cast-result-shape-reindexᵀ)
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using (embedded-creation-target-shapeᴱ)


paired-cast-target-reindexᵀ :
  ∀ {Φ Δᴸ Δᴿ c c′ A A′ B B′}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  Atom B′ →
  PairedCast Φ Δᴸ Δᴿ ρ c c′ p q →
  (r : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  PairedCast Φ Δᴸ Δᴿ ρ c c′ p r
paired-cast-target-reindexᵀ
    {q = q} atom paired r =
  paired-cast-result-shape-reindexᵀ
    (target-atom-shape-unique atom q r) paired


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
atomic-target-value-reindexᵀ atom (() ⟨ inert-u′ ⟩)
    (down·up⊑down·upᵀ
      mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
      L⊑L′ M⊑M′ down-square widening
      u-shape u′-shape up-square compatible) q
atomic-target-value-reindexᵀ atom vV
    (up⊑upᵀ N⊑N′ widening p
      source-shape target-shape square) q =
  up⊑upᵀ N⊑N′ widening q source-shape target-shape
    (quotient-boundary-ordinary-reindex
      (target-atom-shape-unique atom p q) square)
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
      L⊑L′ L•⊢ L′•⊢) q
atomic-target-value-reindexᵀ atom vV
    (α⊑ᵀ {occ = occ} {{safe = safe}} vL noL hA liftρ liftγ
      L⊑V L•⊢ V⊢) q =
  α⊑ᵀ {{safe = safe}} vL noL hA liftρ liftγ
    (atomic-target-value-reindexᵀ atom vV L⊑V
      (ν safe occ q))
    L•⊢ V⊢
atomic-target-value-reindexᵀ atom ()
    (⊑αᵀ vL′ noL′ hA liftρ liftγ N⊑L′ r N⊢ L′•⊢) q
atomic-target-value-reindexᵀ atom vV
    (allocation-prefixᵀ prefix M⊑V M⊢ V⊢) q =
  allocation-prefixᵀ prefix
    (atomic-target-value-reindexᵀ atom vV M⊑V q)
    M⊢ V⊢
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
atomic-target-value-reindexᵀ atom ()
    (⊑νᵀ hA hA↑ s↑ liftρ liftγ r N⊑N′ replacement) q
atomic-target-value-reindexᵀ atom ()
    (νcast⊑νcastᵀ mode seal★ mode′ seal★′
      s⊑ s′⊑ _ liftρ liftγ N⊑N′
      s-shape s′-shape left-comp right-comp) q
atomic-target-value-reindexᵀ {p = p} atom vV
    (νcast⊑ᵀ mode seal★ s⊑ liftρ liftγ N⊑V
      s-shape comp) q =
  νcast⊑ᵀ mode seal★ s⊑ liftρ liftγ N⊑V s-shape
    (imprecision-composition-shape-transport
      refl (sym (target-atom-shape-unique atom p q)) refl comp)
atomic-target-value-reindexᵀ atom ()
    (⊑νcastᵀ mode seal★ s⊑ liftρ liftγ r N⊑N′
      s-shape comp) q
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
    (⊑cast⊑idᵀ seal★ c⊑ M⊑V p c-shape comp) q =
  ⊑cast⊑idᵀ seal★ c⊑ M⊑V q c-shape
    (imprecision-composition-shape-transport
      refl refl
      (sym (target-atom-shape-unique atom p q))
      comp)
atomic-target-value-reindexᵀ atom vV
    (conv⊑convᵀ paired M⊑V) q =
  conv⊑convᵀ (paired-cast-target-reindexᵀ atom paired q) M⊑V
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
