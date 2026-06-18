module proof.NuEffectProperties where

-- File Charter:
--   * Proof-only metatheory for the prototype Nu effect typing judgment.
--   * Starts with structural lemmas that are independent of the remaining
--     store-split exactness problem: subeffecting and term-variable renaming.
--   * Full preservation belongs here once the type-renaming and substitution
--     lemmas for the effect judgment are complete.

open import Data.List using ([]; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import NuTerms
open import NuEffectTyping
open import proof.CoercionProperties using (renameᶜ-preserves-Inert)
open import proof.NuTermProperties using (renameˣᵐ-preserves-Value)

------------------------------------------------------------------------
-- Subeffecting
------------------------------------------------------------------------

⊆ᵉ-refl :
  ∀ {E} →
  E ⊆ᵉ E
⊆ᵉ-refl α∈E = α∈E

⊆ᵉ-trans :
  ∀ {E F G} →
  E ⊆ᵉ F →
  F ⊆ᵉ G →
  E ⊆ᵉ G
⊆ᵉ-trans E⊆F F⊆G α∈E = F⊆G (E⊆F α∈E)

------------------------------------------------------------------------
-- Term-variable renaming
------------------------------------------------------------------------

RenameEffWf : EffCtx → EffCtx → Renameˣ → Set₁
RenameEffWf Ξ Ξ′ ρ =
  ∀ {x A E} → Ξ ∋ x ⦂ A ▷ E → Ξ′ ∋ ρ x ⦂ A ▷ E

RenameEffWf-ext :
  ∀ {Ξ Ξ′ A E ρ} →
  RenameEffWf Ξ Ξ′ ρ →
  RenameEffWf ((A , E) ∷ Ξ) ((A , E) ∷ Ξ′) (extʳ ρ)
RenameEffWf-ext hρ Zᵉ = Zᵉ
RenameEffWf-ext hρ (Sᵉ h) = Sᵉ (hρ h)

lookup-renameCtxᵉ :
  ∀ τ {Ξ x A E} →
  Ξ ∋ x ⦂ A ▷ E →
  renameCtxᵉ τ Ξ ∋ x ⦂ renameᵉ τ A ▷ renameᴱ τ E
lookup-renameCtxᵉ τ Zᵉ = Zᵉ
lookup-renameCtxᵉ τ (Sᵉ h) = Sᵉ (lookup-renameCtxᵉ τ h)

lookup-emptyᵉ :
  ∀ {x A E} →
  [] ∋ x ⦂ A ▷ E →
  ⊥
lookup-emptyᵉ ()

lookup-renameCtxᵉ-inv :
  ∀ τ Ξ {x A′ E′} →
  renameCtxᵉ τ Ξ ∋ x ⦂ A′ ▷ E′ →
  ∃[ A ] ∃[ E ] (Ξ ∋ x ⦂ A ▷ E ×
    A′ ≡ renameᵉ τ A × E′ ≡ renameᴱ τ E)
lookup-renameCtxᵉ-inv τ [] h = ⊥-elim (lookup-emptyᵉ h)
lookup-renameCtxᵉ-inv τ ((A , E) ∷ Ξ) Zᵉ =
  A , E , Zᵉ , refl , refl
lookup-renameCtxᵉ-inv τ ((B , F) ∷ Ξ) (Sᵉ h)
    with lookup-renameCtxᵉ-inv τ Ξ h
lookup-renameCtxᵉ-inv τ ((B , F) ∷ Ξ) (Sᵉ h)
    | A , E , hΞ , eqA , eqE =
  A , E , Sᵉ hΞ , eqA , eqE

RenameEffWf-renameCtxᵉ :
  ∀ {Ξ Ξ′ ρ} τ →
  RenameEffWf Ξ Ξ′ ρ →
  RenameEffWf (renameCtxᵉ τ Ξ) (renameCtxᵉ τ Ξ′) ρ
RenameEffWf-renameCtxᵉ {Ξ = Ξ} τ hρ h
    with lookup-renameCtxᵉ-inv τ Ξ h
RenameEffWf-renameCtxᵉ {Ξ = Ξ} τ hρ h
    | A , E , hΞ , refl , refl =
  lookup-renameCtxᵉ τ (hρ hΞ)

typing-renameˣ :
  ∀ {Δ Σ Ξ Ξ′ M A E ρ} →
  RenameEffWf Ξ Ξ′ ρ →
  Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ E →
  Δ ∣ Σ ∣ Ξ′ ⊢ renameˣᵐ ρ M ⦂ A ▷ E
typing-renameˣ hρ (eff-var hΞ) = eff-var (hρ hΞ)
typing-renameˣ hρ (eff-lam hA hM) =
  eff-lam hA (typing-renameˣ (RenameEffWf-ext hρ) hM)
typing-renameˣ hρ (eff-app hL hM EM⊆Earg) =
  eff-app (typing-renameˣ hρ hL) (typing-renameˣ hρ hM) EM⊆Earg
typing-renameˣ hρ (eff-tylam vM hM) =
  eff-tylam
    (renameˣᵐ-preserves-Value _ vM)
    (typing-renameˣ (RenameEffWf-renameCtxᵉ suc hρ) hM)
typing-renameˣ hρ (eff-tyapp hL α<Δ α∉E noαB) =
  eff-tyapp (typing-renameˣ hρ hL) α<Δ α∉E noαB
typing-renameˣ hρ (eff-nu hA hN) =
  eff-nu hA (typing-renameˣ (RenameEffWf-renameCtxᵉ suc hρ) hN)
typing-renameˣ hρ (eff-const κ) = eff-const κ
typing-renameˣ hρ (eff-prim hL op hM) =
  eff-prim (typing-renameˣ hρ hL) op (typing-renameˣ hρ hM)
typing-renameˣ hρ (eff-cast d c⊢ exact hM) =
  eff-cast d c⊢ exact (typing-renameˣ hρ hM)
typing-renameˣ hρ (eff-blame hA) = eff-blame hA
typing-renameˣ hρ (eff-sub hM E⊆F) =
  eff-sub (typing-renameˣ hρ hM) E⊆F

typing-renameˣ-shift :
  ∀ {Δ Σ Ξ M A B E F} →
  Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ E →
  Δ ∣ Σ ∣ ((B , F) ∷ Ξ) ⊢ renameˣᵐ suc M ⦂ A ▷ E
typing-renameˣ-shift hM =
  typing-renameˣ (λ h → Sᵉ h) hM

------------------------------------------------------------------------
-- Term substitution environments
------------------------------------------------------------------------

SubstEffWf : TyCtx → Store → EffCtx → EffCtx → Substˣ → Set₁
SubstEffWf Δ Σ Ξ Ξ′ σ =
  ∀ {x A E} → Ξ ∋ x ⦂ A ▷ E → Δ ∣ Σ ∣ Ξ′ ⊢ σ x ⦂ A ▷ E

SubstEffWf-exts :
  ∀ {Δ Σ Ξ Ξ′ A E σ} →
  SubstEffWf Δ Σ Ξ Ξ′ σ →
  SubstEffWf Δ Σ ((A , E) ∷ Ξ) ((A , E) ∷ Ξ′) (extˢˣ σ)
SubstEffWf-exts hσ Zᵉ = eff-var Zᵉ
SubstEffWf-exts hσ (Sᵉ h) = typing-renameˣ-shift (hσ h)

singleSubstEffWf :
  ∀ {Δ Σ Ξ A E V EV} →
  Δ ∣ Σ ∣ Ξ ⊢ V ⦂ A ▷ EV →
  EV ⊆ᵉ E →
  SubstEffWf Δ Σ ((A , E) ∷ Ξ) Ξ (singleEnv V)
singleSubstEffWf hV EV⊆E Zᵉ = eff-sub hV EV⊆E
singleSubstEffWf hV EV⊆E (Sᵉ h) = eff-var h
