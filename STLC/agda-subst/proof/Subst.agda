module proof.Subst where

-- File Charter:
--   * Private substitution metatheory for STLC, from the kit library
--     (Subst/proof/Kit.agda): this file proves the two laws that need
--     induction on terms, fusion of two traversals (`fuse`) and the
--     identity substitution (`sub-id`), and the library derives the rest
--     (`Lemmas`: `ren-ren`, `sub-sub`, `exts-[]`, `sub-[]`, ...).
--   * No function extensionality: substitutions are compared pointwise.
--   * Consumed by private proofs, especially termination.

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)
open import Subst.Scope using (ℕScope)
open import STLC
open import Subst.proof.Kit ℕScope Tm `_ using (module Traversal)

open Traversal trav (λ _ _ _ → refl) public
  using (Fuse; SubId; sub-id-exts; Laws; module Lemmas)

------------------------------------------------------------------------
-- Fusion of two traversals, by induction on terms
------------------------------------------------------------------------

fuse : Fuse
fuse 𝒦₁ 𝒦₂ 𝒦₃ R R-exts R-var = go
  where
  go : ∀ {Γ Δ Θ} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ}
    → R σ₁ σ₂ σ₃ → ∀ {A} (M : Tm Γ A)
    → trav 𝒦₂ σ₂ (trav 𝒦₁ σ₁ M) ≡ trav 𝒦₃ σ₃ M
  go r (` i) = R-var r i
  go r (ƛ A ⇒ N) = cong (ƛ A ⇒_) (go (R-exts r) N)
  go r (L · M) = cong₂ _·_ (go r L) (go r M)
  go r `zero = refl
  go r (`suc M) = cong `suc_ (go r M)
  go r (case_[zero⇒_|suc⇒_] L M N)
    rewrite go r L | go r M | go (R-exts r) N = refl

------------------------------------------------------------------------
-- The identity substitution, by induction on terms
------------------------------------------------------------------------

sub-id : SubId
sub-id h (` i) = h i
sub-id h (ƛ A ⇒ N) = cong (ƛ A ⇒_) (sub-id (sub-id-exts h) N)
sub-id h (L · M) = cong₂ _·_ (sub-id h L) (sub-id h M)
sub-id h `zero = refl
sub-id h (`suc M) = cong `suc_ (sub-id h M)
sub-id h (case_[zero⇒_|suc⇒_] L M N)
  rewrite sub-id h L | sub-id h M | sub-id (sub-id-exts h) N = refl

------------------------------------------------------------------------
-- Everything else comes from the library
------------------------------------------------------------------------

open Lemmas fuse sub-id public
