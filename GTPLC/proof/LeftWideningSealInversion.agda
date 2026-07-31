module proof.LeftWideningSealInversion where

-- File Charter:
--   * Inverts term narrowing whose left value has a seal coercion.
--   * Uses a supplied seal-prefix composition equation.
--   * Relies on one-sided contexts to preserve the surrounding imprecision.
--   * Supports the unseal case of the Left Widening lemma.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)

open import Types
open import Coercions
open import Terms
open import NarrowWiden
open import EnvironmentNarrowing
open import ImprecisionTheorems using
  ( LeftOneSidedᵢ
  ; _⨟ˡⁿ[_]_
  ; _≐ⁿ_
  )
open import TermNarrowing

special-no-zero-variable : ∀ {Δᴸ Δᴿ X} {Φ : ImpCtx Δᴸ Δᴿ}
  → freshᴿ Φ ⊢ X ≈ˣ zero
  → ⊥
special-no-zero-variable ()

variable-target-no-zero : ∀ {Δᴸ Δᴿ X A c}
    {Φ : ImpCtx Δᴸ Δᴿ}
  → freshᴿ Φ ∣ Δᴸ ⊢ c ⦂ ＇ X ⊒ A ⊣ suc Δᴿ
  → zero ∈ᵗ A
  → ⊥
variable-target-no-zero
    (idᵃ (＇ X) (＇ zero) hA hB X≈zero)
    var-∈ =
  special-no-zero-variable X≈zero
variable-target-no-zero
    (gen nonvarA zero∈A p B≢★) X∈ =
  variable-target-no-zero p zero∈A

no-variable-to-star-narrowing :
    ∀ {Δᴸ Δᴿ X c}
      {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ∣ Δᴸ ⊢ c ⦂ ＇ X ⊒ ★ ⊣ Δᴿ
  → ⊥
no-variable-to-star-narrowing
    (idᵃ (＇ X) ★ hA hB ())

no-function-to-variable-narrowing :
    ∀ {Δᴸ Δᴿ A B Y c}
      {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⇒ B ⊒ ＇ Y ⊣ Δᴿ
  → ⊥
no-function-to-variable-narrowing
    (idᵃ () (＇ Y) hA hB a⊒b)

no-inert-right-narrowing-to-variable :
    ∀ {Δᴸ Δᴿ A X Y c d}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {Ψ : ImpCtx Δᴿ Δᴿ}
  → Inert d
  → Ψ ∣ Δᴿ ⊢ d ⦂ A ⊒ ＇ Y ⊣ Δᴿ
  → Φ ∣ Δᴸ ⊢ c ⦂ ＇ X ⊒ A ⊣ Δᴿ
  → ⊥
no-inert-right-narrowing-to-variable (G !) () p
no-inert-right-narrowing-to-variable (seal Y)
    (seal Y⊑★) p =
  no-variable-to-star-narrowing p
no-inert-right-narrowing-to-variable (c ↦ d) () p
no-inert-right-narrowing-to-variable (`∀ c) () p
no-inert-right-narrowing-to-variable (gen c) () p

no-inert-right-widening-to-variable :
    ∀ {Δᴿ A Y u}
      {Ψ : ImpCtx Δᴿ Δᴿ}
  → Inert u
  → Ψ ∣ Δᴿ ⊢ u ⦂ A ⊑ ＇ Y ⊣ Δᴿ
  → ⊥
no-inert-right-widening-to-variable (G !) ()
no-inert-right-widening-to-variable (seal Y) ()
no-inert-right-widening-to-variable (c ↦ d) ()
no-inert-right-widening-to-variable (`∀ c) ()
no-inert-right-widening-to-variable (gen c) ()

left-widening-seal-inversion :
    ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ V V′ X B}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {Ψ : ImpCtx Δᴸ Δᴸ}
      {σ : Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ}
      {γ : Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ}
      {left : LeftOneSidedᵢ Φ Ψ}
      {s⊒ : Ψ ∣ Δᴸ ⊢ seal X ⦂ ★ ⊒ ＇ X ⊣ Δᴸ}
      {p : Φ ∣ Δᴸ ⊢ ＇ X ⊒ B ⊣ Δᴿ}
      {r : Φ ∣ Δᴸ ⊢ ★ ⊒ B ⊣ Δᴿ}
  → Value V
  → Value V′
  → Φ ∣ Δᴸ ∣ Δᴿ ∣ σ ∣ γ
      ⊢ᴺ V ⟨ seal X ⟩ ⊒ V′ ⦂ ＇ X ⊒ B ∶ p
  → (seal X , s⊒) ⨟ˡⁿ[ left ] p ≐ⁿ r
  → Σ[ r′ ∈ (Φ ∣ Δᴸ ⊢ ★ ⊒ B ⊣ Δᴿ) ]
      (r′ ≐ⁿ r)
    × (Φ ∣ Δᴸ ∣ Δᴿ ∣ σ ∣ γ
        ⊢ᴺ V ⊒ V′ ⦂ ★ ⊒ B ∶ r′)
left-widening-seal-inversion vV ()
    (⊒blame M⊢) eq
left-widening-seal-inversion vV vV′
    (⊒Λ {p = _ , p} {z∈A = zero∈A}
      extension preservation vW′ W⊒W′) eq =
  ⊥-elim (variable-target-no-zero p zero∈A)
left-widening-seal-inversion
    {p = _ , gen nonvarB zero∈B p B≢★}
    vV vV′ V⊒V′ eq =
  ⊥-elim (variable-target-no-zero p zero∈B)
left-widening-seal-inversion
    {s⊒ = seal X⊑★₀}
    {p = _ , idᵃ (＇ X) (＇ Y) hX hY Y⊑X}
    {r = r , r⊒}
    vV vV′
  (castⁿ⊒
      {d⊒ = seal X⊑★}
      {p = r′ , r′⊒}
      left′ seal⊢ V⊒V′ eq′) eq =
  (r′ , r′⊒) ,
  trans (sym eq′) eq ,
  V⊒V′
left-widening-seal-inversion
    {p = _ , idᵃ (＇ X) (＇ Y) hX hY Y⊑X}
    vV (vV′ ⟨ i′ ⟩)
    (⊒castⁿ {d′⊒ = d′⊒} {p = _ , p}
      right′ d′⊢ V⊒V′ eq′) eq =
  ⊥-elim (no-inert-right-narrowing-to-variable i′ d′⊒ p)
left-widening-seal-inversion
    {p = _ , idᵃ (＇ X) (＇ Y) hX hY Y⊑X}
    vV (vV′ ⟨ i′ ⟩)
    (⊒castʷ {u′⊑ = u′⊑}
      right′ u′⊢ V⊒V′ eq′) eq =
  ⊥-elim (no-inert-right-widening-to-variable i′ u′⊑)
