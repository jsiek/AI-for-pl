module proof.LeftWideningSealInversion where

-- File Charter:
--   * Inverts factored term narrowing whose left value has a seal coercion.
--   * Uses store uniqueness to identify the sealed source type.
--   * Preserves the shared relocation and right narrowing components.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (zero)
open import Data.Product using (_×_; _,_; proj₂; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)

open import Types
open import TyStore
open import Coercions
open import Terms
open import TypeRelocate
open import NarrowWiden
open import FactoredTypeNarrowing
open import EnvironmentNarrowing
open import ImprecisionTheorems using (dualʷ; _⨟ⁿ_)
open import TermNarrowing
open import proof.TyStore using (unique)
open import proof.ImprecisionComposition using
  ( seal-prefix-composeⁿ-evidence
  ; shifted-variable-target-no-zero
  )

------------------------------------------------------------------------
-- A one-context narrowing from a variable still targets a variable
------------------------------------------------------------------------

variable-narrowing-target : ∀ {μ Δ Σ X A c}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ＇ X ⊒ A
  → Σ[ Y ∈ TyVar ] A ≡ ＇ Y
variable-narrowing-target (idᵃ (＇ X) hX) = X , refl
variable-narrowing-target
    (seal {X = Y} Y<Δ hA Y,A∈Σ allowed) =
  Y , refl
variable-narrowing-target
    (seal-seq {X = Y} p Y<Δ Y,A∈Σ allowed B≢A) =
  Y , refl
variable-narrowing-target
    (gen nonvarA zero∈A hX p X≢★) =
  ⊥-elim (shifted-variable-target-no-zero p zero∈A)

variable-relocation-target : ∀ {Δᴸ Δᴿ X A}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ⊢ ＇ X ≈ A
  → Σ[ Y ∈ TyVar ] A ≡ ＇ Y
variable-relocation-target
    (idᵃ (＇ X) (＇ Y) hX hY (varᵃ X≈Y)) =
  Y , refl

factor-variable-gen-impossible :
    ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ X C A}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}}
  → (r : ρ ⊢ᵀ ＇ X ⊒ C)
  → (d : ⇑ᴿᵉ ρ ⊢ᴿⁿ ⇑ᵗ C ⊒ A)
  → zero ∈ᵗ A
  → ⊥
factor-variable-gen-impossible
    (pᴸ ⨟ᶠ relocation ⨟ᶠ pᴿ) (d , d⊒) zero∈A
    with variable-narrowing-target (proj₂ pᴸ)
factor-variable-gen-impossible
    (pᴸ ⨟ᶠ relocation ⨟ᶠ pᴿ) (d , d⊒) zero∈A
    | y , refl with variable-relocation-target relocation
factor-variable-gen-impossible
    (pᴸ ⨟ᶠ relocation ⨟ᶠ pᴿ) (d , d⊒) zero∈A
    | y , refl | z , refl with variable-narrowing-target (proj₂ pᴿ)
factor-variable-gen-impossible
    (pᴸ ⨟ᶠ relocation ⨟ᶠ pᴿ) (d , d⊒) zero∈A
    | y , refl | z , refl | w , refl =
  shifted-variable-target-no-zero d⊒ zero∈A

------------------------------------------------------------------------
-- Left widening seal inversion
------------------------------------------------------------------------

left-widening-seal-inversion :
    ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ V V′ X A B C C′}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}}
      {u⊑ : ρ ⊢ᴸʷ unseal X ⦂ ＇ X ⊑ A}
      {pᴸ : ρ ⊢ᴸⁿ ＇ X ⊒ C}
      {qᴸ : ρ ⊢ᴸⁿ A ⊒ C}
      {relocation : Φ ⊢ C ≈ C′}
      {pᴿ : ρ ⊢ᴿⁿ C′ ⊒ B}
  → StoreWf Δᴸ Σᴸ
  → Value V
  → Value V′
  → ρ ⊢ᴺ V ⟨ seal X ⟩ ⊒ V′
      ∶ (pᴸ ⨟ᶠ relocation ⨟ᶠ pᴿ)
  → (dualʷ (unseal X , u⊑) ⨟ⁿ pᴸ) ≐ⁿ qᴸ
  → Σ[ pᴸ′ ∈ ρ ⊢ᴸⁿ A ⊒ C ]
      (pᴸ′ ≐ⁿ qᴸ)
    × (ρ ⊢ᴺ V ⊒ V′
        ∶ (pᴸ′ ⨟ᶠ relocation ⨟ᶠ pᴿ))
left-widening-seal-inversion wfΣᴸ vV () (⊒blame M⊢) eq₀
left-widening-seal-inversion
    {u⊑ = unseal X<Δ hA X,A∈Σ allowed} {pᴸ = pᴸ}
    wfΣᴸ vV vV′
    (castⁿ⊒
      {pᴸ = qᴸ}
      {s⦂ = seal X<Δ′ hA′ X,A′∈Σ allowed′}
      V⊒V′ eq) eq₀
    with unique wfΣᴸ X,A′∈Σ X,A∈Σ
left-widening-seal-inversion
    {u⊑ = unseal X<Δ hA X,A∈Σ allowed} {pᴸ = pᴸ}
    wfΣᴸ vV vV′
    (castⁿ⊒
      {pᴸ = qᴸ}
      {s⦂ = seal X<Δ′ hA′ X,A′∈Σ allowed′}
      V⊒V′ eq) eq₀
    | refl =
  qᴸ ,
  trans (sym eq)
    (trans
      (seal-prefix-composeⁿ-evidence
        {s = seal X<Δ′ hA′ X,A′∈Σ allowed′}
        {t = seal X<Δ hA X,A∈Σ allowed}
        {q = pᴸ})
      eq₀) ,
  V⊒V′
left-widening-seal-inversion {ρ = ρ}
    {u⊑ = unseal {X = X} X<Δ hA X,A∈Σ allowed}
    wfΣᴸ vV vV′
    (⊒Λ {r = rᴸ ⨟ᶠ relocation ⨟ᶠ rᴿ}
      {d = d} {z∈A = zero∈A}
      extension vW′ W⊒W′) eq₀ =
  ⊥-elim
    (factor-variable-gen-impossible {ρ = ρ}
      (rᴸ ⨟ᶠ relocation ⨟ᶠ rᴿ) d zero∈A)
left-widening-seal-inversion {ρ = ρ}
    {u⊑ = unseal {X = X} X<Δ hA X,A∈Σ allowed}
    wfΣᴸ vV vV′
    (⊒⟨ν⟩ {r = rᴸ ⨟ᶠ relocation ⨟ᶠ rᴿ}
      {d = d} {z∈A = zero∈A}
      vW′ W′⊢ hC c⊢ W⊒W′) eq₀ =
  ⊥-elim
    (factor-variable-gen-impossible {ρ = ρ}
      (rᴸ ⨟ᶠ relocation ⨟ᶠ rᴿ) d zero∈A)
left-widening-seal-inversion
    {u⊑ = u⊑} {pᴸ = pᴸ} {qᴸ = qᴸ} wfΣᴸ
    vV (vW′ ⟨ i′ ⟩)
    (⊒castⁿ {t⦂ = t⦂} W⊒W′ eq) eq₀
    with left-widening-seal-inversion
      {u⊑ = u⊑} {pᴸ = pᴸ} {qᴸ = qᴸ}
      wfΣᴸ vV vW′ W⊒W′ eq₀
left-widening-seal-inversion wfΣᴸ
    vV (vW′ ⟨ i′ ⟩)
    (⊒castⁿ {t⦂ = t⦂} W⊒W′ eq) eq₀
    | qᴸ , qᴸ≐qᴸ , V⊒W′ =
  qᴸ , qᴸ≐qᴸ , ⊒castⁿ {t⦂ = t⦂} V⊒W′ eq
left-widening-seal-inversion
    {u⊑ = u⊑} {pᴸ = pᴸ} {qᴸ = qᴸ} wfΣᴸ
    vV (vW′ ⟨ i′ ⟩)
    (⊒castʷ {t⦂ = t⦂} W⊒W′ eq) eq₀
    with left-widening-seal-inversion
      {u⊑ = u⊑} {pᴸ = pᴸ} {qᴸ = qᴸ}
      wfΣᴸ vV vW′ W⊒W′ eq₀
left-widening-seal-inversion wfΣᴸ
    vV (vW′ ⟨ i′ ⟩)
    (⊒castʷ {t⦂ = t⦂} W⊒W′ eq) eq₀
    | qᴸ , qᴸ≐qᴸ , V⊒W′ =
  qᴸ , qᴸ≐qᴸ , ⊒castʷ {t⦂ = t⦂} V⊒W′ eq
