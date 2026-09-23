module strong-rep-store.proof.Residual where

-- File Charter:
--   * SOUNDNESS OF THE RESIDUAL LAYER: a residual names a position IN
--     THE CONTRACTUM — `plug D N` is the step's target and `plug C M`
--     its source (`residual-source`, `residual-sound`,
--     `residuals-sound`), via `plug-renCtxᴿ`, `plug-↑` and
--     `plug-substCtx`.  Sanity lemmas for the color-preservation
--     STATEMENT; the theorem is strong-rep-store.proof.ColorPreservation.
-- Commentary: Commentary.md § proof/Residual.agda

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₂)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import strong-rep-store.Types using (Ty; `_; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import strong-rep-store.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Terms
open import strong-rep-store.Boundary
open import strong-rep-store.TermSubst
open import strong-rep-store.proof.TermSubst
open import strong-rep-store.Reduction
open import strong-rep-store.Residual

-- Renaming through a context is renaming the plugged term.  Since the
-- store there is only ONE renaming: the representation-only `renᴹᴿ`.
plug-renCtxᴿ : ∀ (ρ : Renameᵗ) (C : TermCtx) (M : Term)
  → plug (renCtxᴿ ρ C) (renᴹᴿ (holeᴿ ρ C) M) ≡ renᴹᴿ ρ (plug C M)
plug-renCtxᴿ ρ □ M = refl
plug-renCtxᴿ ρ (ƛC A ∙ C) M =
  cong (ƛ A ∙_) (plug-renCtxᴿ ρ C M)
plug-renCtxᴿ ρ (C ·L N) M =
  cong (_· renᴹᴿ ρ N) (plug-renCtxᴿ ρ C M)
plug-renCtxᴿ ρ (L ·R C) M =
  cong (renᴹᴿ ρ L ·_) (plug-renCtxᴿ ρ C M)
plug-renCtxᴿ ρ (ΛC C) M =
  cong Λ_ (plug-renCtxᴿ (extᵗ ρ) C M)
plug-renCtxᴿ ρ (C ·C[ B , A ]) M =
  cong (_·[ B , A ]) (plug-renCtxᴿ ρ C M)
plug-renCtxᴿ ρ (C ⟪C Θ , c ⟫) M =
  cong (_⟪ renᴮᴿ ρ Θ , c ⟫) (plug-renCtxᴿ ρ C M)

-- The SIBLING SHIFT through a context: the three halves of `↑ᴹ[ δ ]`
-- (strong-rep-store.Residual §3) rebuild exactly the shifted term.
plug-↑ : ∀ (δ : Alloc) (C : TermCtx) (M : Term)
  → plug (↑ᶜ[ δ ] C) (↑ᴴ[ δ ] C M) ≡ ↑ᴹ[ δ ] (plug C M)
plug-↑ none    C M = refl
plug-↑ (new R) C M = plug-renCtxᴿ suc C M

-- A pointwise-identity substitution is the identity.
substᵐ-ivar : ∀ (σ : Var → Img) → (∀ x → σ x ≡ ivar x)
  → ∀ (M : Term) → substᵐ σ M ≡ M
substᵐ-ivar σ h (` x) = cong imgTm (h x)
substᵐ-ivar σ h ($ n) = refl
substᵐ-ivar σ h `true = refl
substᵐ-ivar σ h `false = refl
substᵐ-ivar σ h (ƛ A ∙ N) =
  cong (ƛ A ∙_) (substᵐ-ivar (extᴵ σ) ext-ivar N)
  where
    ext-ivar : ∀ x → extᴵ σ x ≡ ivar x
    ext-ivar zero = refl
    ext-ivar (suc x) = cong shiftᴵ (h x)
substᵐ-ivar σ h (L · M) =
  cong₂ _·_ (substᵐ-ivar σ h L) (substᵐ-ivar σ h M)
substᵐ-ivar σ h (Λ N) =
  cong Λ_ (substᵐ-ivar (λ x → ⇑ᴵ (σ x)) lam-ivar N)
  where
    lam-ivar : ∀ x → (λ y → ⇑ᴵ (σ y)) x ≡ ivar x
    lam-ivar x = cong ⇑ᴵ (h x)
substᵐ-ivar σ h (L ·[ B , A ]) =
  cong (λ t → t ·[ B , A ]) (substᵐ-ivar σ h L)
substᵐ-ivar σ h (M ⟪ Θ , c ⟫) = refl

-- Substituting through a context is substituting the plugged term.
plug-substCtx : ∀ (σ : Var → Img) (C : TermCtx) (M : Term)
  → plug (substCtx σ C) (substᵐ (holeEnv σ C) M) ≡ substᵐ σ (plug C M)
plug-substCtx σ □ M = refl
plug-substCtx σ (ƛC A ∙ C) M =
  cong (ƛ A ∙_) (plug-substCtx (extᴵ σ) C M)
plug-substCtx σ (C ·L N) M =
  cong (_· substᵐ σ N) (plug-substCtx σ C M)
plug-substCtx σ (L ·R C) M =
  cong (substᵐ σ L ·_) (plug-substCtx σ C M)
plug-substCtx σ (ΛC C) M =
  cong Λ_ (plug-substCtx (λ x → ⇑ᴵ (σ x)) C M)
plug-substCtx σ (C ·C[ B , A ]) M =
  cong (_·[ B , A ]) (plug-substCtx σ C M)
-- A boundary frame is term-closed: the substitution neither enters the
-- frame nor reaches the hole, so both sides are the original plug.
plug-substCtx σ (C ⟪C Θ , c ⟫) M =
  cong (λ z → plug C z ⟪ Θ , c ⟫) (substᵐ-ivar ivar (λ x → refl) M)

image-sound : ∀ {k I C M ρ D N}
  → ImageResidual k I C M ρ D N → plug D N ≡ imgTm I
image-sound image-here = refl
-- `crossΛᴹ` is written with the paired renaming, whose ordinary half is
-- the identity; `renᴹ²-ord-id` is what identifies it with `renᴹᴿ suc`.
image-sound (image-Λ {A = A} {D = D} {N = N} r) =
  cong (_⟪ (lock 0 0 ∷ []) , mkId (⇑ᵗ A) ⟫)
    (trans (trans (plug-renCtxᴿ suc D N)
                  (cong (renᴹᴿ suc) (image-sound r)))
           (sym (renᴹ²-ord-id (λ X → refl) _)))

copy-sound : ∀ {k σ P C M ρ D N}
  → CopyResidual k σ P C M ρ D N → plug D N ≡ substᵐ σ P
copy-sound (copy-var i)   = image-sound i
copy-sound (copy-ƛ r)     = cong₂ ƛ_∙_ refl (copy-sound r)
copy-sound (copy-·L r)    = cong₂ _·_ (copy-sound r) refl
copy-sound (copy-·R r)    = cong₂ _·_ refl (copy-sound r)
copy-sound (copy-Λ r)     = cong Λ_ (copy-sound r)
copy-sound (copy-·[] r)   = cong (_·[ _ , _ ]) (copy-sound r)

residual-source : ∀ {Δ L L′ δ C M ρ D N} {r : Δ ⊢ L -→ L′ ∣ δ}
  → Residual r C M ρ D N → plug C M ≡ L
residual-source (residual-TyBeta vN pA)          = refl
residual-source (residual-Beta-body vW st)       = refl
residual-source (residual-Beta-arg vW cr)        = refl
residual-source (residual-Peel-fun vV vW rc ri rd sc) = refl
residual-source (residual-Peel-arg vV vW rc ri rd sc) = refl
residual-source (residual-TyPeelR-Λ vN rc ⊢s pA) = refl
residual-source
  (residual-TyPeelR-⟪⟫ vW ri rc rc′ ri⁺ rc″ sc ⊢s sm pA) = refl
residual-source
  (residual-CancelR vV ri rc₁ lX rc⋉ sm)  = refl
residual-source
  (residual-IdPush vV ri rc₁ rc⋉ sm)      = refl
residual-source (residual-ξ-·-l r)      = cong (_· _) (residual-source r)
residual-source (residual-ξ-·-l-sib r)  = refl
residual-source (residual-ξ-·-r v r)    = cong (_ ·_) (residual-source r)
residual-source (residual-ξ-·-r-sib v r) = refl
residual-source (residual-ξ-·[] r) = cong (_·[ _ , _ ]) (residual-source r)
residual-source (residual-ξ-⟪⟫ ri r) = cong (_⟪ _ , _ ⟫) (residual-source r)

residual-sound : ∀ {Δ L L′ δ C M ρ D N} {r : Δ ⊢ L -→ L′ ∣ δ}
  → Residual r C M ρ D N → plug D N ≡ L′
residual-sound (residual-TyBeta vN pA) = refl
residual-sound (residual-Beta-body {W = W} {A = A} {C = C} {M = M} vW st) =
  plug-substCtx (betaEnv W A) C M
residual-sound (residual-Beta-arg vW cr) = copy-sound cr
residual-sound (residual-Peel-fun vV vW rc ri rd sc) = refl
residual-sound (residual-Peel-arg vV vW rc ri rd sc) = refl
residual-sound (residual-TyPeelR-Λ vN rc ⊢s pA) = refl
residual-sound
  (residual-TyPeelR-⟪⟫ {Θ = Θ} {C = C} {M = M} {Θ′ = Θ′} {s″ = s″}
    {s = s} {Bᵢ′ = Bᵢ′} vW ri rc rc′ ri⁺ rc″ sc ⊢s sm pA) =
  cong (λ z → ((z ⟪ (renᴮᴿ suc Θ′ ++ (lock 0 0 ∷ [])) , `∀ s″ ⟫)
                  ·[ renameᵗ (extᵗ suc) Bᵢ′ , ` 0 ])
                ⟪ inst Θ , instReveal 0 s ⟫)
    (plug-renCtxᴿ suc C M)
residual-sound
  (residual-CancelR vV ri rc₁ lX rc⋉ sm) = refl
residual-sound
  (residual-IdPush vV ri rc₁ rc⋉ sm)     = refl
residual-sound (residual-ξ-·-l r)      = cong (_· _) (residual-sound r)
residual-sound (residual-ξ-·-l-sib {δ = δ} {C = C} {M = M} r) =
  cong (_ ·_) (plug-↑ δ C M)
residual-sound (residual-ξ-·-r v r)    = cong (_ ·_) (residual-sound r)
residual-sound (residual-ξ-·-r-sib {δ = δ} {C = C} {M = M} v r) =
  cong (_· _) (plug-↑ δ C M)
residual-sound (residual-ξ-·[] r) = cong (_·[ _ , _ ]) (residual-sound r)
residual-sound (residual-ξ-⟪⟫ ri r) = cong (_⟪ _ , _ ⟫) (residual-sound r)

residuals-sound : ∀ {Δ L L′ C M ρ D N} {rs : Δ ⊢ L -→* L′}
  → Residuals rs C M ρ D N → (plug C M ≡ L) × (plug D N ≡ L′)
residuals-sound residuals-done = refl , refl
residuals-sound (residuals-step r rs) =
  residual-source r , proj₂ (residuals-sound rs)
