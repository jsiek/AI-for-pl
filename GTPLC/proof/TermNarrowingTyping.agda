module proof.TermNarrowingTyping where

-- File Charter:
--   * Projects source typing from term narrowing.
--   * Projects source lookup from context narrowing lookup.
--   * Supplies typing evidence needed by source-side canonical forms.
--   * Uses the bundled narrowing environment throughout.

open import Types hiding (_∋_⦂_)
open import Ctx
open import Terms
open import TypeNarrow
open import NarrowWiden
open import EnvironmentNarrowing
open import TermNarrowing

lookup-source : ∀ {Δᴸ Δᴿ Γᴸ Γᴿ x A B}
    {Φ : ImpCtx Δᴸ Δᴿ}
    {γ : Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ}
    {p : Φ ⊢ A ⊒ B}
  → γ ∋ x ⦂ p
  → Γᴸ Types.∋ x ⦂ A
lookup-source Zⁿ = Z
lookup-source (Sⁿ x∈) = S (lookup-source x∈)

term-narrowing-source-typing :
    ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ M M′ A B}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}}
      {p : ρ ⊢ᵀ A ⊒ B}
  → ρ ⊢ᴺ M ⊒ M′ ∶ p
  → ρ ⊢ᴸ M ⦂ A
term-narrowing-source-typing (⊒blame M⊢) = M⊢
term-narrowing-source-typing (x⊒x x∈) =
  ⊢` (lookup-source x∈)
term-narrowing-source-typing (ƛ⊒ƛ hA hA′ N⊒N′) =
  ⊢ƛ hA (term-narrowing-source-typing N⊒N′)
term-narrowing-source-typing (·⊒· L⊒L′ M⊒M′) =
  ⊢· (term-narrowing-source-typing L⊒L′)
     (term-narrowing-source-typing M⊒M′)
term-narrowing-source-typing (Λ⊒Λ vV vV′ V⊒V′) =
  ⊢Λ vV (term-narrowing-source-typing V⊒V′)
term-narrowing-source-typing
    (⊒Λ extension vV′ N⊒V′) =
  term-narrowing-source-typing N⊒V′
term-narrowing-source-typing
    (⊒⟨ν⟩ vV′ V′⊢ hC c⊢ N⊒V′) =
  term-narrowing-source-typing N⊒V′
term-narrowing-source-typing
    (ν⊒ν {s⦂ = s⦂} a L⊒L′ square) =
  ⊢ν (TypeNarrow.⊒-src-wf a)
     (term-narrowing-source-typing L⊒L′)
     (narrowing-typing s⦂)
term-narrowing-source-typing
    (⊒ν hA′ N⊒L′ endpoints) =
  term-narrowing-source-typing N⊒L′
term-narrowing-source-typing κ⊒κ = ⊢$ _
term-narrowing-source-typing (⊕⊒⊕ L⊒L′ M⊒M′) =
  ⊢⊕ (term-narrowing-source-typing L⊒L′) _
     (term-narrowing-source-typing M⊒M′)
term-narrowing-source-typing
    (castⁿ⊒ {s⦂ = s⦂} M⊒M′ endpoints) =
  ⊢⟨⟩ (narrowing-typing s⦂)
       (term-narrowing-source-typing M⊒M′)
term-narrowing-source-typing
    (castʷ⊒ {s⦂ = s⦂} M⊒M′ endpoints) =
  ⊢⟨⟩ (widening-typing s⦂)
       (term-narrowing-source-typing M⊒M′)
term-narrowing-source-typing
    (⊒castⁿ M⊒M′ endpoints) =
  term-narrowing-source-typing M⊒M′
term-narrowing-source-typing
    (⊒castʷ M⊒M′ endpoints) =
  term-narrowing-source-typing M⊒M′
