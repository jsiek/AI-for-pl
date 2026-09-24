module strong-rep-nu.proof.Determinism where

-- File Charter:
--   * THE PROOF OF DETERMINISM.  `det` takes the redex's TYPING
--     DERIVATION and concludes `M₁ ≡ M₂ × δ₁ ≡ δ₂`: uniqueness of the
--     contractum AND of the store change.  Name-map uniqueness is read
--     off the typing through `bw-exterior`; the carried readings are
--     identified by `interior-functional`/`conversion-functional`, the
--     weakenings (Peel's `s′`, Merge's `t₁′` and `c₂′`) by
--     `sameConv-src-unique`.  The public statement is
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

-- Nu-Λ
det _ (Nu-Λ v same) (Nu-Λ v′ same′)
  with same-rep-unique same same′
det _ (Nu-Λ v same) (Nu-Λ v′ same′) | refl = refl , refl
det _ (Nu-Λ v same) (ξ-ν st) =
  ⊥-elim (value-¬step (V-simple (S-Λ v)) st)
det _ (ξ-ν st) (Nu-Λ v same) =
  ⊥-elim (value-¬step (V-simple (S-Λ v)) st)

-- Beta
det _ (Beta w)     (Beta w′)    = refl , refl
det _ (Beta w)     (ξ-·-l st)   = ⊥-elim (value-¬step (V-simple S-ƛ) st)
det _ (Beta w)     (ξ-·-r v st) = ⊥-elim (value-¬step w st)
det _ (ξ-·-l st)   (Beta w)     = ⊥-elim (value-¬step (V-simple S-ƛ) st)
det _ (ξ-·-r v st) (Beta w)     = ⊥-elim (value-¬step w st)

-- Peel
-- the dual's spelling is pinned by `sameConv-src-unique`
det (⊢· (boundary mwΘ _ _ _ _ _) _)
    (Peel v w rc ri rd sc) (Peel v′ w′ rc′ ri′ rd′ sc′)
  with conversion-functional rc rc′ | interior-functional ri ri′
det (⊢· (boundary mwΘ _ _ _ _ _) _)
    (Peel v w rc ri rd sc) (Peel v′ w′ rc′ ri′ rd′ sc′)
  | refl | refl with conversion-functional rd rd′
det (⊢· (boundary mwΘ _ _ _ _ _) _)
    (Peel v w rc ri rd sc) (Peel v′ w′ rc′ ri′ rd′ sc′)
  | refl | refl | refl
  with sameConv-src-unique
         (dual-unique (name-fn (bw-exterior mwΘ)) ri rd) sc sc′
det (⊢· (boundary mwΘ _ _ _ _ _) _)
    (Peel v w rc ri rd sc) (Peel v′ w′ rc′ ri′ rd′ sc′)
  | refl | refl | refl | refl = refl , refl
det _ (Peel v w rc ri rd sc) (ξ-·-l st) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-fun) st)
det _ (Peel v w rc ri rd sc) (ξ-·-r u′ st) =
  ⊥-elim (value-¬step w st)
det _ (ξ-·-l st) (Peel v w rc ri rd sc) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-fun) st)
det _ (ξ-·-r u′ st) (Peel v w rc ri rd sc) =
  ⊥-elim (value-¬step w st)

-- Nu over a boundary — determined by the redex outright.
det _ (Nu-⟪Λ⟫ v rel ⊢s same)
    (Nu-⟪Λ⟫ v′ rel′ ⊢s′ same′)
  with same-rep-unique same same′
det _ (Nu-⟪Λ⟫ v rel ⊢s same)
    (Nu-⟪Λ⟫ v′ rel′ ⊢s′ same′) | refl = refl , refl
det _ (Nu-⟪Λ⟫ v rel ⊢s same) (ξ-ν st) =
  ⊥-elim (value-¬step (V-⟪⟫ (S-Λ v) I-all) st)
det _ (ξ-ν st) (Nu-⟪Λ⟫ v rel ⊢s same) =
  ⊥-elim (value-¬step (V-⟪⟫ (S-Λ v) I-all) st)

-- Merge — the three readings are functions of the scopes, and the two
-- carried spellings are pinned at the merged conversion context.
det (boundary mwΘ₂ _ _ _ _ _)
    (Merge u it ri r₁ r₂ r⋉ sc₁ sc₂)
    (Merge u′ it′ ri′ r₁′ r₂′ r⋉′ sc₁′ sc₂′)
  with interior-functional ri ri′
det (boundary mwΘ₂ _ _ _ _ _)
    (Merge u it ri r₁ r₂ r⋉ sc₁ sc₂)
    (Merge u′ it′ ri′ r₁′ r₂′ r⋉′ sc₁′ sc₂′) | refl
  with conversion-functional r₁ r₁′ | conversion-functional r₂ r₂′
     | conversion-functional r⋉ r⋉′
det (boundary mwΘ₂ _ _ _ _ _)
    (Merge u it ri r₁ r₂ r⋉ sc₁ sc₂)
    (Merge u′ it′ ri′ r₁′ r₂′ r⋉′ sc₁′ sc₂′)
    | refl | refl | refl | refl
  with sameConv-src-unique
         (conversion-unique (name-fn (bw-exterior mwΘ₂)) r⋉) sc₁ sc₁′
     | sameConv-src-unique
         (conversion-unique (name-fn (bw-exterior mwΘ₂)) r⋉) sc₂ sc₂′
det (boundary mwΘ₂ _ _ _ _ _)
    (Merge u it ri r₁ r₂ r⋉ sc₁ sc₂)
    (Merge u′ it′ ri′ r₁′ r₂′ r⋉′ sc₁′ sc₂′)
    | refl | refl | refl | refl | refl | refl = refl , refl
det _ (Merge u it ri r₁ r₂ r⋉ sc₁ sc₂) (ξ-⟪⟫ frame st) =
  ⊥-elim (value-¬step (V-⟪⟫ u it) st)
det _ (ξ-⟪⟫ frame st) (Merge u it ri r₁ r₂ r⋉ sc₁ sc₂) =
  ⊥-elim (value-¬step (V-⟪⟫ u it) st)

-- Drop$
det _ (Drop$ b)    (Drop$ b′)   = refl , refl
det _ (Drop$ b) (ξ-⟪⟫ frame st) = ⊥-elim (value-¬step (V-simple S-$) st)
det _ (ξ-⟪⟫ frame st) (Drop$ b) = ⊥-elim (value-¬step (V-simple S-$) st)

-- Drop-true / Drop-false
det _ Drop-true Drop-true = refl , refl
det _ Drop-true (ξ-⟪⟫ frame st) = ⊥-elim (value-¬step (V-simple S-true) st)
det _ (ξ-⟪⟫ frame st) Drop-true = ⊥-elim (value-¬step (V-simple S-true) st)
det _ Drop-false Drop-false = refl , refl
det _ Drop-false (ξ-⟪⟫ frame st) = ⊥-elim (value-¬step (V-simple S-false) st)
det _ (ξ-⟪⟫ frame st) Drop-false = ⊥-elim (value-¬step (V-simple S-false) st)

-- the congruences: the sibling shift is a function of the store change
det (⊢· ⊢L ⊢M) (ξ-·-l st) (ξ-·-l st′) with det ⊢L st st′
det (⊢· ⊢L ⊢M) (ξ-·-l st) (ξ-·-l st′) | refl , refl = refl , refl
det _ (ξ-·-l st) (ξ-·-r v st′) = ⊥-elim (value-¬step v st)
det _ (ξ-·-r v st) (ξ-·-l st′) = ⊥-elim (value-¬step v st′)
det (⊢· ⊢L ⊢M) (ξ-·-r v st) (ξ-·-r u st′) with det ⊢M st st′
det (⊢· ⊢L ⊢M) (ξ-·-r v st) (ξ-·-r u st′) | refl , refl = refl , refl
det (⊢ν wA rA ⊢L mw ⊢c same wB) (ξ-ν st) (ξ-ν st′) with det ⊢L st st′
det (⊢ν wA rA ⊢L mw ⊢c same wB) (ξ-ν st) (ξ-ν st′) | refl , refl = refl , refl
det (boundary mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  with interior-functional rel rel′
det (boundary mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  | refl with interior-functional rel (bw-interior mwΘ)
det (boundary mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  | refl | refl with det ⊢M st st′
det (boundary mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  | refl | refl | refl , refl = refl , refl

