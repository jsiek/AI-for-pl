module strong-rep-nu.proof.Determinism where

-- File Charter:
--   * THE PROOF OF DETERMINISM.  `det` takes the redex's TYPING
--     DERIVATION and concludes `M₁ ≡ M₂ × δ₁ ≡ δ₂`: uniqueness of the
--     contractum AND of the store change.  Name-map uniqueness is read
--     off the typing through `bw-exterior`; the carried readings are
--     identified by `interior-functional`/`conversion-functional`, and
--     the respellings (Wrap's, Merge's two) are computed from them, so
--     Wrap and Merge need no typing at all.  The public statement is
--     strong-rep-nu.TypeSafety.
--   * Commentary: Commentary.md § Reduction.agda / det.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.Boundary
open import strong-rep-nu.TermSubst
open import strong-rep-nu.Reduction


det : ∀ {Δ Γ M M₁ M₂ A δ₁ δ₂}
  → Δ ∣ Γ ⊢ M ⦂ A
  → Δ ⊢ M -→ M₁ ∣ δ₁
  → Δ ⊢ M -→ M₂ ∣ δ₂
  → M₁ ≡ M₂ × δ₁ ≡ δ₂

-- TyBeta
det _ (TyBeta v same) (TyBeta v′ same′)
  with same-rep-unique same same′
det _ (TyBeta v same) (TyBeta v′ same′) | refl = refl , refl
det _ (TyBeta v same) (ξ-ν st) =
  ⊥-elim (value-¬step (V-simple (S-Λ v)) st)
det _ (ξ-ν st) (TyBeta v same) =
  ⊥-elim (value-¬step (V-simple (S-Λ v)) st)

-- Beta
det _ (Beta w)     (Beta w′)    = refl , refl
det _ (Beta w)     (ξ-·₁ st)   = ⊥-elim (value-¬step (V-simple S-ƛ) st)
det _ (Beta w)     (ξ-·₂ v st) = ⊥-elim (value-¬step w st)
det _ (ξ-·₁ st)   (Beta w)     = ⊥-elim (value-¬step (V-simple S-ƛ) st)
det _ (ξ-·₂ v st) (Beta w)     = ⊥-elim (value-¬step w st)

-- Wrap — the three readings are functions of the scope, and the dual's
-- spelling is computed from them.
det _ (Wrap v w rc ri rd) (Wrap v′ w′ rc′ ri′ rd′)
  with conversion-functional rc rc′ | interior-functional ri ri′
det _ (Wrap v w rc ri rd) (Wrap v′ w′ rc′ ri′ rd′)
  | refl | refl with conversion-functional rd rd′
det _ (Wrap v w rc ri rd) (Wrap v′ w′ rc′ ri′ rd′)
  | refl | refl | refl = refl , refl
det _ (Wrap v w rc ri rd) (ξ-·₁ st) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-fun) st)
det _ (Wrap v w rc ri rd) (ξ-·₂ u′ st) =
  ⊥-elim (value-¬step w st)
det _ (ξ-·₁ st) (Wrap v w rc ri rd) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-fun) st)
det _ (ξ-·₂ u′ st) (Wrap v w rc ri rd) =
  ⊥-elim (value-¬step w st)

-- TyWrap (ν over a boundary) — determined by the redex outright.
det _ (TyWrap v same)
    (TyWrap v′ same′)
  with same-rep-unique same same′
det _ (TyWrap v same)
    (TyWrap v′ same′) | refl = refl , refl
det _ (TyWrap v same) (ξ-ν st) =
  ⊥-elim (value-¬step (V-⟪⟫ (S-Λ v) I-all) st)
det _ (ξ-ν st) (TyWrap v same) =
  ⊥-elim (value-¬step (V-⟪⟫ (S-Λ v) I-all) st)

-- Merge — the four readings are functions of the scopes, and the two
-- spellings are computed from them.
det _ (Merge u it ri r₁ r₂ r⋉) (Merge u′ it′ ri′ r₁′ r₂′ r⋉′)
  with interior-functional ri ri′
det _ (Merge u it ri r₁ r₂ r⋉) (Merge u′ it′ ri′ r₁′ r₂′ r⋉′) | refl
  with conversion-functional r₁ r₁′ | conversion-functional r₂ r₂′
     | conversion-functional r⋉ r⋉′
det _ (Merge u it ri r₁ r₂ r⋉) (Merge u′ it′ ri′ r₁′ r₂′ r⋉′)
    | refl | refl | refl | refl = refl , refl
det _ (Merge u it ri r₁ r₂ r⋉) (ξ-⟪⟫ frame st) =
  ⊥-elim (value-¬step (V-⟪⟫ u it) st)
det _ (ξ-⟪⟫ frame st) (Merge u it ri r₁ r₂ r⋉) =
  ⊥-elim (value-¬step (V-⟪⟫ u it) st)

-- Id
det _ (Id u b) (Id u′ b′) = refl , refl
det _ (Id u b) (ξ-⟪⟫ frame st) = ⊥-elim (value-¬step (V-simple u) st)
det _ (ξ-⟪⟫ frame st) (Id u b) = ⊥-elim (value-¬step (V-simple u) st)
det _ (Id () b) (Merge u it ri r₁ r₂ r⋉)
det _ (Merge u it ri r₁ r₂ r⋉) (Id () b)

-- the congruences: the sibling shift is a function of the store change
det (⊢· ⊢L ⊢M) (ξ-·₁ st) (ξ-·₁ st′) with det ⊢L st st′
det (⊢· ⊢L ⊢M) (ξ-·₁ st) (ξ-·₁ st′) | refl , refl = refl , refl
det _ (ξ-·₁ st) (ξ-·₂ v st′) = ⊥-elim (value-¬step v st)
det _ (ξ-·₂ v st) (ξ-·₁ st′) = ⊥-elim (value-¬step v st′)
det (⊢· ⊢L ⊢M) (ξ-·₂ v st) (ξ-·₂ u st′) with det ⊢M st st′
det (⊢· ⊢L ⊢M) (ξ-·₂ v st) (ξ-·₂ u st′) | refl , refl = refl , refl
det (⊢ν wA rA ⊢L mw ⊢c smC same wB) (ξ-ν st) (ξ-ν st′) with det ⊢L st st′
det (⊢ν wA rA ⊢L mw ⊢c smC same wB) (ξ-ν st) (ξ-ν st′) | refl , refl = refl , refl
det (boundary mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  with interior-functional rel rel′
det (boundary mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  | refl with interior-functional rel (bw-interior mwΘ)
det (boundary mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  | refl | refl with det ⊢M st st′
det (boundary mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  | refl | refl | refl , refl = refl , refl

