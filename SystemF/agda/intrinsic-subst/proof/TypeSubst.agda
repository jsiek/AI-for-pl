module intrinsic-subst.proof.TypeSubst where

-- File Charter:
--   * Private substitution metatheory for System F types, from the kit
--     library (Subst/proof/Kit.agda): this file proves the two laws that
--     need induction on types, fusion of two traversals (`fuseᵗ`) and the
--     identity substitution (`sub-idᵗ`), and the library derives the rest.
--   * The derived lemmas are exported under the module `TL` (e.g.
--     `TL.sub-sub`, `TL.ren-sub`, `TL.sub-[]`, `TL.exts-[]`, `TL.⇑-[]`).
--   * No function extensionality: substitutions are compared pointwise.

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)

open import intrinsic-subst.Types
import Subst.proof.Kit

module TP = Subst.proof.Kit.Traversal tyScope Typ `_ travᵗ (λ _ _ _ → refl)

fuseᵗ : TP.Fuse
fuseᵗ 𝒦₁ 𝒦₂ 𝒦₃ R R-exts R-var = go
  where
  go : ∀ {Γ Δ Θ} {σ₁ : TK.Sub 𝒦₁ Γ Δ} {σ₂ : TK.Sub 𝒦₂ Δ Θ}
    {σ₃ : TK.Sub 𝒦₃ Γ Θ}
    → R σ₁ σ₂ σ₃ → ∀ {s} (A : Typ Γ s)
    → travᵗ 𝒦₂ σ₂ (travᵗ 𝒦₁ σ₁ A) ≡ travᵗ 𝒦₃ σ₃ A
  go r (` α) = R-var r α
  go r `Nat = refl
  go r `Bool = refl
  go r (A ⇒ B) = cong₂ _⇒_ (go r A) (go r B)
  go r (`∀ A) = cong `∀_ (go (R-exts r) A)

sub-idᵗ : TP.SubId
sub-idᵗ h (` α) = h α
sub-idᵗ h `Nat = refl
sub-idᵗ h `Bool = refl
sub-idᵗ h (A ⇒ B) = cong₂ _⇒_ (sub-idᵗ h A) (sub-idᵗ h B)
sub-idᵗ h (`∀ A) = cong `∀_ (sub-idᵗ (TP.sub-id-exts h) A)

module TL = TP.Lemmas fuseᵗ sub-idᵗ
