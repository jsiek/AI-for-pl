module strong-rep-store.proof.Determinism where

-- File Charter:
--   * THE PROOF OF DETERMINISM.  `det` takes the redex's TYPING
--     DERIVATION and concludes `M₁ ≡ M₂ × δ₁ ≡ δ₂`: uniqueness of the
--     contractum AND of the store change.  Name-map uniqueness is read
--     off the typing through `bw-exterior`; the carried readings are
--     identified by `interior-functional`/`conversion-functional`, the
--     re-spellings by `sameConv-src-unique`.  The public statement is
--     strong-rep-store.TypeSafety.
--   * Commentary: Commentary.md § Reduction.agda / det.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong)

open import strong-rep-store.Types
open import strong-rep-store.Ctx
open import strong-rep-store.proof.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Terms
open import strong-rep-store.Boundary
open import strong-rep-store.TermSubst
open import strong-rep-store.Reduction


det : ∀ {Δ Γ M M₁ M₂ A δ₁ δ₂}
  → Δ ∣ Γ ⊢ M ⦂ A
  → Δ ⊢ M -→ M₁ ∣ δ₁
  → Δ ⊢ M -→ M₂ ∣ δ₂
  → M₁ ≡ M₂ × δ₁ ≡ δ₂

-- TyBeta
det _ (TyBeta v same) (TyBeta v′ same′)
  with same-rep-unique same same′
det _ (TyBeta v same) (TyBeta v′ same′) | refl = refl , refl
det _ (TyBeta v same) (ξ-·[] st) =
  ⊥-elim (value-¬step (V-Λ v) st)
det _ (ξ-·[] st) (TyBeta v same) =
  ⊥-elim (value-¬step (V-Λ v) st)

-- Beta
det _ (Beta w)     (Beta w′)    = refl , refl
det _ (Beta w)     (ξ-·-l st)   = ⊥-elim (value-¬step V-ƛ st)
det _ (Beta w)     (ξ-·-r v st) = ⊥-elim (value-¬step w st)
det _ (ξ-·-l st)   (Beta w)     = ⊥-elim (value-¬step V-ƛ st)
det _ (ξ-·-r v st) (Beta w)     = ⊥-elim (value-¬step w st)

-- Peel
-- the dual's spelling is pinned by `sameConv-src-unique`
det (⊢· (env mwΘ _ _ _ _ _) _)
    (Peel v w rc ri rd sc) (Peel v′ w′ rc′ ri′ rd′ sc′)
  with conversion-functional rc rc′ | interior-functional ri ri′
det (⊢· (env mwΘ _ _ _ _ _) _)
    (Peel v w rc ri rd sc) (Peel v′ w′ rc′ ri′ rd′ sc′)
  | refl | refl with conversion-functional rd rd′
det (⊢· (env mwΘ _ _ _ _ _) _)
    (Peel v w rc ri rd sc) (Peel v′ w′ rc′ ri′ rd′ sc′)
  | refl | refl | refl
  with sameConv-src-unique
         (dual-unique (name-fn (bw-exterior mwΘ)) ri rd) sc sc′
det (⊢· (env mwΘ _ _ _ _ _) _)
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

-- TyPeelR — the two clauses' patterns are DISJOINT, and the Λ clause is
-- determined by the redex outright.
det _ (TyPeelR-Λ v rel ⊢s same)
    (TyPeelR-Λ v′ rel′ ⊢s′ same′)
  with same-rep-unique same same′
det _ (TyPeelR-Λ v rel ⊢s same)
    (TyPeelR-Λ v′ rel′ ⊢s′ same′) | refl = refl , refl
det _ (TyPeelR-Λ v rel ⊢s same) (ξ-·[] st) =
  ⊥-elim (value-¬step (V-⟪⟫ (V-Λ v) I-all) st)
det _ (ξ-·[] st) (TyPeelR-Λ v rel ⊢s same) =
  ⊥-elim (value-¬step (V-⟪⟫ (V-Λ v) I-all) st)

-- the wrapper clause: all five carried readings are identified first
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
  with interior-functional ri ri′ | conversion-functional rc rc′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl
  with interior-functional ri (bw-interior mwΘ)
     | conversion-functional rc (bw-conversion mwΘ)
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl
  with conversion-functional r′ r′′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl
  with conv-src-unique
         (unique-underΛ {Γ = Δᶜ} (name-fn (bw-conversion-wf mwΘ))) ⊢s ⊢s′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl | refl
  with sameTy-src-unique
         (unique-underΛ {Γ = Δᵢ} (name-fn (bw-interior-wf mwΘ))) sm sm′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl | refl | refl
  with same-rep-unique same same′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl | refl | refl | refl
  with interior-functional ri⁺ ri⁺′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δ″ᶜ = Δ″ᶜ} v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl | refl | refl | refl | refl
  with conversion-functional r″ r″′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δ″ᶜ = Δ″ᶜ} v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl
  with sameConv-src-unique
         (unique-underΛ {Γ = Δ″ᶜ}
           (conversion-unique
             (interior-unique (unique-shift (name-fn (bw-exterior mwΘ)))
                              ri⁺) r″))
         sc sc′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl
    | refl = refl , refl
det _ (TyPeelR-⟪⟫ v ri rc r′ ri⁺ r″ sc ⊢s sm same) (ξ-·[] st) =
  ⊥-elim (value-¬step (V-⟪⟫ (V-⟪⟫ v I-all) I-all) st)
det _ (ξ-·[] st) (TyPeelR-⟪⟫ v ri rc r′ ri⁺ r″ sc ⊢s sm same) =
  ⊥-elim (value-¬step (V-⟪⟫ (V-⟪⟫ v I-all) I-all) st)

-- CancelR — both looked-up types and the re-spelling are functional
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
  with interior-functional ri ri′ | conversion-functional r₂ r₂′
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
    | refl | refl
  with conversion-functional r₁ r₁′ | conversion-functional r⋉ r⋉′
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
    | refl | refl | refl | refl
  with interior-functional ri (bw-interior mwΘ₂)
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
    | refl | refl | refl | refl | refl
  with conversion-functional r₁ (bw-conversion mwΘ₁)
     | conversion-functional r₂ (bw-conversion mwΘ₂)
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
    | refl | refl | refl | refl | refl | refl | refl
  with ∋:=-det (name-fn (bw-conversion-wf mwΘ₁)) d₁ d₁′
     | ∋:=-det (name-fn (bw-conversion-wf mwΘ₂)) d₂ d₂′
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
    | refl | refl | refl | refl | refl | refl | refl | refl | refl
  with sameTy-src-unique
         (conversion-unique (name-fn (bw-exterior mwΘ₂)) r⋉) sm sm′
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
    | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl =
  refl , refl
det _ (CancelR v ri r₁ d₁ r⋉ sm r₂ d₂) (ξ-⟪⟫ frame st) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-seal) st)
det _ (ξ-⟪⟫ frame st) (CancelR v ri r₁ d₁ r⋉ sm r₂ d₂) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-seal) st)

-- Drop$
det _ (Drop$ b)    (Drop$ b′)   = refl , refl
det _ (Drop$ b) (ξ-⟪⟫ frame st) = ⊥-elim (value-¬step V-$ st)
det _ (ξ-⟪⟫ frame st) (Drop$ b) = ⊥-elim (value-¬step V-$ st)

-- Drop-true / Drop-false
det _ Drop-true Drop-true = refl , refl
det _ Drop-true (ξ-⟪⟫ frame st) = ⊥-elim (value-¬step V-true st)
det _ (ξ-⟪⟫ frame st) Drop-true = ⊥-elim (value-¬step V-true st)
det _ Drop-false Drop-false = refl , refl
det _ Drop-false (ξ-⟪⟫ frame st) = ⊥-elim (value-¬step V-false st)
det _ (ξ-⟪⟫ frame st) Drop-false = ⊥-elim (value-¬step V-false st)

-- IdPush — likewise determined by the lookup.
det (env mwΘ₂ _ _ _ _ _)
    (IdPush {Θ₂ = Θ₂} v ri r₁ r⋉ sm rel d)
    (IdPush v′ ri′ r₁′ r⋉′ sm′ rel′ d′)
  with interior-functional ri ri′ | conversion-functional rel rel′
det (env mwΘ₂ _ _ _ _ _)
    (IdPush {Θ₂ = Θ₂} v ri r₁ r⋉ sm rel d)
    (IdPush v′ ri′ r₁′ r⋉′ sm′ rel′ d′) | refl | refl
  with conversion-functional r₁ r₁′ | conversion-functional r⋉ r⋉′
det (env mwΘ₂ _ _ _ _ _)
    (IdPush {Θ₂ = Θ₂} v ri r₁ r⋉ sm rel d)
    (IdPush v′ ri′ r₁′ r⋉′ sm′ rel′ d′)
    | refl | refl | refl | refl
  with conversion-functional rel (bw-conversion mwΘ₂)
det (env mwΘ₂ _ _ _ _ _)
    (IdPush {Θ₂ = Θ₂} v ri r₁ r⋉ sm rel d)
    (IdPush v′ ri′ r₁′ r⋉′ sm′ rel′ d′)
    | refl | refl | refl | refl | refl
  with sameTy-src-unique
         (conversion-unique (name-fn (bw-exterior mwΘ₂)) r⋉) sm sm′
     | ∋:=-det (name-fn (bw-conversion-wf mwΘ₂)) d d′
det (env mwΘ₂ _ _ _ _ _)
    (IdPush {Θ₂ = Θ₂} v ri r₁ r⋉ sm rel d)
    (IdPush v′ ri′ r₁′ r⋉′ sm′ rel′ d′)
    | refl | refl | refl | refl | refl | refl | refl = refl , refl
det _ (IdPush v ri r₁ r⋉ sm rel d) (ξ-⟪⟫ frame st) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-idv) st)
det _ (ξ-⟪⟫ frame st) (IdPush v ri r₁ r⋉ sm rel d) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-idv) st)

-- the congruences: the sibling shift is a function of the store change
det (⊢· ⊢L ⊢M) (ξ-·-l st) (ξ-·-l st′) with det ⊢L st st′
det (⊢· ⊢L ⊢M) (ξ-·-l st) (ξ-·-l st′) | refl , refl = refl , refl
det _ (ξ-·-l st) (ξ-·-r v st′) = ⊥-elim (value-¬step v st)
det _ (ξ-·-r v st) (ξ-·-l st′) = ⊥-elim (value-¬step v st′)
det (⊢· ⊢L ⊢M) (ξ-·-r v st) (ξ-·-r u st′) with det ⊢M st st′
det (⊢· ⊢L ⊢M) (ξ-·-r v st) (ξ-·-r u st′) | refl , refl = refl , refl
det (⊢·[] ⊢L ⊢A) (ξ-·[] st) (ξ-·[] st′) with det ⊢L st st′
det (⊢·[] ⊢L ⊢A) (ξ-·[] st) (ξ-·[] st′) | refl , refl = refl , refl
det (env mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  with interior-functional rel rel′
det (env mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  | refl with interior-functional rel (bw-interior mwΘ)
det (env mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  | refl | refl with det ⊢M st st′
det (env mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  | refl | refl | refl , refl = refl , refl

