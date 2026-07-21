module proof.NuImprecisionAtomicTargetReindex where

-- File Charter:
--   * Reindexes ordinary quotiented-term imprecision at atomic target types
--     when the target term is a value.
--   * Reconstructs proof-relevant type-imprecision indices structurally;
--     it does not assume proof irrelevance.
--   * Supplies the strict support theorem for target identity conversions.

open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; idι; ν)
open import NuTermImprecision using
  (CtxImp; StoreImp)
open import NuTerms using (Value)
open import QuotientedTermImprecision using
  ( PairedCast
  ; allocation-prefixᵀ
  ; blame⊑ᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; conv⊑convᵀ
  ; paired-conceal
  ; paired-conversion
  ; paired-reveal
  ; paired-widening
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
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Atom)


paired-cast-target-reindexᵀ :
  ∀ {Φ Δᴸ Δᴿ c c′ A A′ B B′}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  PairedCast Φ Δᴸ Δᴿ ρ c c′ p q →
  (r : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  PairedCast Φ Δᴸ Δᴿ ρ c c′ p r
paired-cast-target-reindexᵀ
    (paired-conversion (paired-reveal corr c↑ c′↑)) r =
  paired-conversion (paired-reveal corr c↑ c′↑)
paired-cast-target-reindexᵀ
    (paired-conversion (paired-conceal corr c↓ c′↓)) r =
  paired-conversion (paired-conceal corr c↓ c′↓)
paired-cast-target-reindexᵀ
    (paired-widening mode seal★ c⊑ mode′ seal★′ c′⊑ compat) r =
  paired-widening mode seal★ c⊑ mode′ seal★′ c′⊑ compat


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
atomic-target-value-reindexᵀ atom vV
    (up⊑upᵀ N⊑N′ widening p) q =
  up⊑upᵀ N⊑N′ widening q
atomic-target-value-reindexᵀ () vV
    (Λ⊑Λᵀ liftρ liftγ vW vW′ W⊑W′) q
atomic-target-value-reindexᵀ atom vV
    (Λ⊑ᵀ occ liftρ liftγ vW W⊑V) (ν occ′ q) =
  Λ⊑ᵀ occ′ liftρ liftγ vW
    (atomic-target-value-reindexᵀ atom vV W⊑V q)
atomic-target-value-reindexᵀ atom ()
    (α⊑αᵀ vL noL vL′ noL′ p↑ liftρ liftγ
      L⊑L′ L•⊢ L′•⊢) q
atomic-target-value-reindexᵀ atom vV
    (α⊑ᵀ {occ = occ} vL noL hA liftρ liftγ
      L⊑V L•⊢ V⊢) q =
  α⊑ᵀ vL noL hA liftρ liftγ
    (atomic-target-value-reindexᵀ atom vV L⊑V (ν occ q))
    L•⊢ V⊢
atomic-target-value-reindexᵀ atom ()
    (⊑αᵀ vL′ noL′ hA liftρ liftγ N⊑L′ r N⊢ L′•⊢) q
atomic-target-value-reindexᵀ atom vV
    (allocation-prefixᵀ prefix M⊑V M⊢ V⊢) q =
  allocation-prefixᵀ prefix
    (atomic-target-value-reindexᵀ atom vV M⊑V q)
    M⊢ V⊢
atomic-target-value-reindexᵀ atom ()
    (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ p↑ liftρ liftγ N⊑N′) q
atomic-target-value-reindexᵀ atom vV
    (ν⊑ᵀ hA hA↑ s↑ liftρ liftγ N⊑V) q =
  ν⊑ᵀ hA hA↑ s↑ liftρ liftγ N⊑V
atomic-target-value-reindexᵀ atom ()
    (⊑νᵀ hA hA↑ s↑ liftρ liftγ r N⊑N′) q
atomic-target-value-reindexᵀ atom ()
    (νcast⊑νcastᵀ mode seal★ mode′ seal★′
      s⊑ s′⊑ _ liftρ liftγ N⊑N′) q
atomic-target-value-reindexᵀ atom vV
    (νcast⊑ᵀ mode seal★ s⊑ liftρ liftγ N⊑V) q =
  νcast⊑ᵀ mode seal★ s⊑ liftρ liftγ N⊑V
atomic-target-value-reindexᵀ atom ()
    (⊑νcastᵀ mode seal★ s⊑ liftρ liftγ r N⊑N′) q
atomic-target-value-reindexᵀ atom vV κ⊑κᵀ idι =
  κ⊑κᵀ
atomic-target-value-reindexᵀ atom ()
    (⊕⊑⊕ᵀ L⊑L′ M⊑M′) q
atomic-target-value-reindexᵀ atom vV
    (cast⊒⊑ᵀ mode seal★ c⊒ M⊑V p) q =
  cast⊒⊑ᵀ mode seal★ c⊒ M⊑V q
atomic-target-value-reindexᵀ atom vV
    (cast⊑⊑ᵀ mode seal★ c⊑ M⊑V p) q =
  cast⊑⊑ᵀ mode seal★ c⊑ M⊑V q
atomic-target-value-reindexᵀ atom vV
    (⊑cast⊒ᵀ mode seal★ c⊒ M⊑V p) q =
  ⊑cast⊒ᵀ mode seal★ c⊒ M⊑V q
atomic-target-value-reindexᵀ atom vV
    (⊑cast⊑ᵀ mode seal★ c⊑ M⊑V p) q =
  ⊑cast⊑ᵀ mode seal★ c⊑ M⊑V q
atomic-target-value-reindexᵀ atom vV
    (⊑cast⊑idᵀ seal★ c⊑ M⊑V p) q =
  ⊑cast⊑idᵀ seal★ c⊑ M⊑V q
atomic-target-value-reindexᵀ atom vV
    (conv⊑convᵀ paired M⊑V) q =
  conv⊑convᵀ (paired-cast-target-reindexᵀ paired q) M⊑V
atomic-target-value-reindexᵀ atom vV
    (conv↑⊑ᵀ c↑ M⊑V p) q =
  conv↑⊑ᵀ c↑ M⊑V q
atomic-target-value-reindexᵀ atom vV
    (conv↓⊑ᵀ c↓ M⊑V p) q =
  conv↓⊑ᵀ c↓ M⊑V q
atomic-target-value-reindexᵀ atom vV
    (⊑conv↑ᵀ c↑ M⊑V p) q =
  ⊑conv↑ᵀ c↑ M⊑V q
atomic-target-value-reindexᵀ atom vV
    (⊑conv↓ᵀ c↓ M⊑V p) q =
  ⊑conv↓ᵀ c↓ M⊑V q
