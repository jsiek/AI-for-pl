module CoercionGradualGuarantee where

open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)

open import Types
open import Contexts
open import Coercions

------------------------------------------------------------------------
-- Coercion simulation
------------------------------------------------------------------------

preserve-—↠ᶜᶜ : ∀ {c c′ A B}
  → ⊢ c ⦂ A ⇨ B
  → c —↠ᶜᶜ c′
  → ⊢ c′ ⦂ A ⇨ B
preserve-—↠ᶜᶜ cwt (_ ∎ᶜᶜ) = cwt
preserve-—↠ᶜᶜ cwt (_ —→ᶜᶜ⟨ c→c₁ ⟩ c₁↠c′) =
  preserve-—↠ᶜᶜ (preserve-—→ᶜᶜ cwt c→c₁) c₁↠c′

postulate
  -- TODO: prove principal β-proj-inj-okᶜ simulation case.
  simᶜ-β-proj-inj-ok : ∀ {c G A B}
    → c ⊑ᶜ (G ! ⨟ G `?)
    → ⊢ c ⦂ A ⇨ B
    → ⊢ (G ! ⨟ G `?) ⦂ G ⇨ G
    → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ idᶜ G))

  -- TODO: prove principal β-idLᶜ simulation case.
  simᶜ-β-idL : ∀ {c A B X Y d}
    → c ⊑ᶜ (idᶜ A ⨟ d)
    → ⊢ c ⦂ X ⇨ Y
    → ⊢ d ⦂ A ⇨ B
    → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ d))

  -- TODO: prove principal β-idRᶜ simulation case.
  simᶜ-β-idR : ∀ {c A B X Y d}
    → c ⊑ᶜ (d ⨟ idᶜ B)
    → ⊢ c ⦂ X ⇨ Y
    → ⊢ d ⦂ A ⇨ B
    → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ d))

  -- TODO: prove principal β-assocLᶜ simulation case.
  simᶜ-β-assocL : ∀ {c c₁ c₂ c₃ A B C D X Y}
    → c ⊑ᶜ (c₁ ⨟ (c₂ ⨟ c₃))
    → ⊢ c ⦂ X ⇨ Y
    → ⊢ c₁ ⦂ A ⇨ B
    → ⊢ c₂ ⦂ B ⇨ C
    → ⊢ c₃ ⦂ C ⇨ D
    → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ ((c₁ ⨟ c₂) ⨟ c₃)))

  -- TODO: prove principal β-assocRᶜ simulation case.
  simᶜ-β-assocR : ∀ {c c₁ c₂ c₃ A B C D X Y}
    → c ⊑ᶜ ((c₁ ⨟ c₂) ⨟ c₃)
    → ⊢ c ⦂ X ⇨ Y
    → ⊢ c₁ ⦂ A ⇨ B
    → ⊢ c₂ ⦂ B ⇨ C
    → ⊢ c₃ ⦂ C ⇨ D
    → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ (c₁ ⨟ (c₂ ⨟ c₃))))

  -- TODO: prove principal β-↦ᶜ simulation case.
  simᶜ-β-↦ : ∀ {c c₁ d₁ c₂ d₂ A B C D E F X Y}
    → c ⊑ᶜ ((c₁ ↦ d₁) ⨟ (c₂ ↦ d₂))
    → ⊢ c ⦂ X ⇨ Y
    → ⊢ c₁ ⦂ C ⇨ A
    → ⊢ d₁ ⦂ B ⇨ D
    → ⊢ c₂ ⦂ E ⇨ C
    → ⊢ d₂ ⦂ D ⇨ F
    → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ ((c₂ ⨟ c₁) ↦ (d₁ ⨟ d₂))))

  -- TODO: prove congruence ξ-⨟₁ᶜ simulation case.
  simᶜ-ξ-⨟₁ : ∀ {c c₁ c₁′ d A B C X Y}
    → c ⊑ᶜ (c₁ ⨟ d)
    → ⊢ c ⦂ X ⇨ Y
    → ⊢ c₁ ⦂ A ⇨ B
    → ⊢ d ⦂ B ⇨ C
    → c₁ —→ᶜᶜ c₁′
    → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ (c₁′ ⨟ d)))

  -- TODO: prove congruence ξ-⨟₂ᶜ simulation case.
  simᶜ-ξ-⨟₂ : ∀ {c c₁ d d′ A B C X Y}
    → c ⊑ᶜ (c₁ ⨟ d)
    → ⊢ c ⦂ X ⇨ Y
    → ⊢ c₁ ⦂ A ⇨ B
    → ⊢ d ⦂ B ⇨ C
    → d —→ᶜᶜ d′
    → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ (c₁ ⨟ d′)))

  -- TODO: prove congruence ξ-↦₁ᶜ simulation case.
  simᶜ-ξ-↦₁ : ∀ {c c₁ c₁′ d A B C D X Y}
    → c ⊑ᶜ (c₁ ↦ d)
    → ⊢ c ⦂ X ⇨ Y
    → ⊢ c₁ ⦂ C ⇨ A
    → ⊢ d ⦂ B ⇨ D
    → c₁ —→ᶜᶜ c₁′
    → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ (c₁′ ↦ d)))

  -- TODO: prove congruence ξ-↦₂ᶜ simulation case.
  simᶜ-ξ-↦₂ : ∀ {c c₁ d d′ A B C D X Y}
    → c ⊑ᶜ (c₁ ↦ d)
    → ⊢ c ⦂ X ⇨ Y
    → ⊢ c₁ ⦂ C ⇨ A
    → ⊢ d ⦂ B ⇨ D
    → d —→ᶜᶜ d′
    → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ (c₁ ↦ d′)))

simᶜ : ∀ {c d d′ A B A′ B′}
  → c ⊑ᶜ d
  → ⊢ c ⦂ A′ ⇨ B′
  → ⊢ d ⦂ A ⇨ B
  → d —→ᶜᶜ d′
  → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ d′))
simᶜ c≤d cwt (⊢⨟ (⊢! g) (⊢? h)) β-proj-inj-okᶜ =
  simᶜ-β-proj-inj-ok c≤d cwt (⊢⨟ (⊢! g) (⊢? h))
simᶜ {c = c} c≤d cwt (⊢⨟ (⊢! g) (⊢? h)) (β-proj-inj-badᶜ {G = G} {H = H} G≢H)
  with ⊑ᶜ→⊑ (⊢⨟ (⊢! g) (⊢? h)) cwt c≤d
... | A′⊑G , B′⊑H =
  c , ((c ∎ᶜᶜ) , (⊑⊥ cwt A′⊑G B′⊑H))
simᶜ c≤d cwt (⊢⨟ ⊢idᶜ dwt) β-idLᶜ =
  simᶜ-β-idL c≤d cwt dwt
simᶜ c≤d cwt (⊢⨟ cwt₁ ⊢idᶜ) β-idRᶜ =
  simᶜ-β-idR c≤d cwt cwt₁
simᶜ c≤d cwt (⊢⨟ cwt₁ (⊢⨟ dwt ewt)) β-assocLᶜ =
  simᶜ-β-assocL c≤d cwt cwt₁ dwt ewt
simᶜ c≤d cwt (⊢⨟ (⊢⨟ cwt₁ dwt) ewt) β-assocRᶜ =
  simᶜ-β-assocR c≤d cwt cwt₁ dwt ewt
simᶜ c≤d cwt (⊢⨟ (⊢↦ cwt₁ dwt) (⊢↦ c′wt d′wt)) β-↦ᶜ =
  simᶜ-β-↦ c≤d cwt cwt₁ dwt c′wt d′wt
simᶜ c≤d cwt (⊢⨟ cwt₁ dwt) (ξ-⨟₁ᶜ c→c′) =
  simᶜ-ξ-⨟₁ c≤d cwt cwt₁ dwt c→c′
simᶜ c≤d cwt (⊢⨟ cwt₁ dwt) (ξ-⨟₂ᶜ d→d′) =
  simᶜ-ξ-⨟₂ c≤d cwt cwt₁ dwt d→d′
simᶜ c≤d cwt (⊢↦ cwt₁ dwt) (ξ-↦₁ᶜ c→c′) =
  simᶜ-ξ-↦₁ c≤d cwt cwt₁ dwt c→c′
simᶜ c≤d cwt (⊢↦ cwt₁ dwt) (ξ-↦₂ᶜ d→d′) =
  simᶜ-ξ-↦₂ c≤d cwt cwt₁ dwt d→d′

sim*ᶜ : ∀ {c d d′ A B A′ B′}
  → c ⊑ᶜ d
  → ⊢ c ⦂ A′ ⇨ B′
  → ⊢ d ⦂ A ⇨ B
  → d —↠ᶜᶜ d′
  → ∃[ c′ ] ((c —↠ᶜᶜ c′) × (c′ ⊑ᶜ d′))
sim*ᶜ {c = c} c≤d cwt dwt (d ∎ᶜᶜ) =
  c , ((c ∎ᶜᶜ) , c≤d)
sim*ᶜ c≤d cwt dwt (d —→ᶜᶜ⟨ d→d₁ ⟩ d₁↠d′)
  with simᶜ c≤d cwt dwt d→d₁
... | c₁ , c↠c₁ , c₁≤d₁
  with sim*ᶜ c₁≤d₁ (preserve-—↠ᶜᶜ cwt c↠c₁) (preserve-—→ᶜᶜ dwt d→d₁) d₁↠d′
... | c′ , c₁↠c′ , c′≤d′ =
  c′ , ((multi-transᶜᶜ c↠c₁ c₁↠c′) , c′≤d′)
