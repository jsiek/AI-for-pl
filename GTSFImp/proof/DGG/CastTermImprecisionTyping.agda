{-# OPTIONS --safe #-}

module proof.DGG.CastTermImprecisionTyping where

-- File Charter:
--   * Projects source and target typing from the canonical cast-term
--     imprecision relation.
--   * Works directly with the complete endpoint contexts that index a world.
--   * Uses no compatibility context, runtime-store transport, or world wrapper.

open import Types
open import CastTerms
open import proof.DGG.World
import proof.DGG.CastTermImprecision as CTI
open CTI using (_⊢²_⊑_∶_)


------------------------------------------------------------------------
-- Endpoint typing
------------------------------------------------------------------------

mutual
  source-typing : ∀ {Γᴸ Γᴿ} {γ : Γᴸ ⊑ᶜ Γᴿ}
      {M M′ A B} {p : A ⊑ᵀ⟨ γ ⟩ B}
    → γ ⊢² M ⊑ M′ ∶ p
    → Γᴸ ⊢ M ⦂ A

  target-typing : ∀ {Γᴸ Γᴿ} {γ : Γᴸ ⊑ᶜ Γᴿ}
      {M M′ A B} {p : A ⊑ᵀ⟨ γ ⟩ B}
    → γ ⊢² M ⊑ M′ ∶ p
    → Γᴿ ⊢ M′ ⦂ B

  source-typing (CTI.x⊑x² x∈ x∈′) = ⊢` x∈
  source-typing (CTI.ƛ⊑ƛ² M⊑M′) = ⊢ƛ (source-typing M⊑M′)
  source-typing (CTI.·⊑·² L⊑L′ M⊑M′) =
    ⊢· (source-typing L⊑L′) (source-typing M⊑M′)
  source-typing (CTI.Λ⊑Λ² vV vV′ V⊑V′ q) =
    ⊢Λ vV (source-typing V⊑V′)
  source-typing (CTI.Λ⊑² Anv zero∈A vV M′⊢ V⊑M′ q) =
    ⊢Λ vV (source-typing V⊑M′)
  source-typing (CTI.•⊑•² p∀ M⊑M′ q r) = ⊢• (source-typing M⊑M′)
  source-typing (CTI.•⊑² p∀ M⊑M′ q r) = ⊢• (source-typing M⊑M′)
  source-typing (CTI.κ⊑κ² κ p) = ⊢$ κ
  source-typing (CTI.cast⊑cast² c c′ M⊑M′ q) =
    ⊢⟨⟩ (source-typing M⊑M′) c
  source-typing (CTI.⊑cast² c′ M⊑M′ q) = source-typing M⊑M′
  source-typing (CTI.⊑reveal-identity c′⊢ pos M⊑M′ q) =
    source-typing M⊑M′
  source-typing (CTI.⊑conceal-identity c′⊢ pos M⊑M′ q) =
    source-typing M⊑M′
  source-typing (CTI.cast⊑² c M⊑M′ q) =
    ⊢⟨⟩ (source-typing M⊑M′) c
  source-typing (CTI.reveal⊑-identity c⊢ pos M⊑M′ q) =
    ⊢reveal c⊢ (source-typing M⊑M′)
  source-typing
      (CTI.reveal⊑-only² c⊢ pos mark disaligned represented M⊑M′ q) =
    ⊢reveal c⊢ (source-typing M⊑M′)
  source-typing (CTI.conceal⊑-identity c⊢ pos M⊑M′ q) =
    ⊢conceal c⊢ (source-typing M⊑M′)
  source-typing
      (CTI.conceal⊑-only² c⊢ pos mark disaligned represented M⊑M′ q) =
    ⊢conceal c⊢ (source-typing M⊑M′)
  source-typing
      (CTI.reveal⊑reveal² c⊢ c′⊢ aligned matched represented M⊑M′ q) =
    ⊢reveal c⊢ (source-typing M⊑M′)
  source-typing
      (CTI.conceal⊑conceal² c⊢ c′⊢ aligned matched represented M⊑M′ q) =
    ⊢conceal c⊢ (source-typing M⊑M′)
  source-typing
      (CTI.⊑reveal-rebase² c′⊢ rebase M⊑M′ q) =
    source-typing M⊑M′
  source-typing
      (CTI.⊑conceal-rebase² c′⊢ rebase M⊑M′ q) =
    source-typing M⊑M′
  source-typing (CTI.blame⊑² M′⊢ p) = ⊢blame
  source-typing (CTI.⊕⊑⊕² op L⊑L′ M⊑M′ r) =
    ⊢⊕ op (source-typing L⊑L′) (source-typing M⊑M′)

  target-typing (CTI.x⊑x² x∈ x∈′) = ⊢` x∈′
  target-typing (CTI.ƛ⊑ƛ² M⊑M′) = ⊢ƛ (target-typing M⊑M′)
  target-typing (CTI.·⊑·² L⊑L′ M⊑M′) =
    ⊢· (target-typing L⊑L′) (target-typing M⊑M′)
  target-typing (CTI.Λ⊑Λ² vV vV′ V⊑V′ q) =
    ⊢Λ vV′ (target-typing V⊑V′)
  target-typing (CTI.Λ⊑² Anv zero∈A vV M′⊢ V⊑M′ q) = M′⊢
  target-typing (CTI.•⊑•² p∀ M⊑M′ q r) = ⊢• (target-typing M⊑M′)
  target-typing (CTI.•⊑² p∀ M⊑M′ q r) = target-typing M⊑M′
  target-typing (CTI.κ⊑κ² κ p) = ⊢$ κ
  target-typing (CTI.cast⊑cast² c c′ M⊑M′ q) =
    ⊢⟨⟩ (target-typing M⊑M′) c′
  target-typing (CTI.⊑cast² c′ M⊑M′ q) =
    ⊢⟨⟩ (target-typing M⊑M′) c′
  target-typing (CTI.⊑reveal-identity c′⊢ pos M⊑M′ q) =
    ⊢reveal c′⊢ (target-typing M⊑M′)
  target-typing (CTI.⊑conceal-identity c′⊢ pos M⊑M′ q) =
    ⊢conceal c′⊢ (target-typing M⊑M′)
  target-typing (CTI.cast⊑² c M⊑M′ q) = target-typing M⊑M′
  target-typing (CTI.reveal⊑-identity c⊢ pos M⊑M′ q) =
    target-typing M⊑M′
  target-typing
      (CTI.reveal⊑-only² c⊢ pos mark disaligned represented M⊑M′ q) =
    target-typing M⊑M′
  target-typing (CTI.conceal⊑-identity c⊢ pos M⊑M′ q) =
    target-typing M⊑M′
  target-typing
      (CTI.conceal⊑-only² c⊢ pos mark disaligned represented M⊑M′ q) =
    target-typing M⊑M′
  target-typing
      (CTI.reveal⊑reveal² c⊢ c′⊢ aligned matched represented M⊑M′ q) =
    ⊢reveal c′⊢ (target-typing M⊑M′)
  target-typing
      (CTI.conceal⊑conceal² c⊢ c′⊢ aligned matched represented M⊑M′ q) =
    ⊢conceal c′⊢ (target-typing M⊑M′)
  target-typing
      (CTI.⊑reveal-rebase² c′⊢ rebase M⊑M′ q) =
    ⊢reveal c′⊢ (target-typing M⊑M′)
  target-typing
      (CTI.⊑conceal-rebase² c′⊢ rebase M⊑M′ q) =
    ⊢conceal c′⊢ (target-typing M⊑M′)
  target-typing (CTI.blame⊑² M′⊢ p) = M′⊢
  target-typing (CTI.⊕⊑⊕² op L⊑L′ M⊑M′ r) =
    ⊢⊕ op (target-typing L⊑L′) (target-typing M⊑M′)
