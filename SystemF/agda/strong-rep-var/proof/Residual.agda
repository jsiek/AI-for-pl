module strong-rep-var.proof.Residual where

-- SOUNDNESS OF THE RESIDUAL LAYER (strong-rep-var.Residual): a residual
-- names a position IN THE CONTRACTUM — `plug D N` is the step's target
-- and `plug C M` its source.  These are the sanity lemmas for the
-- statement of color preservation; the theorem itself is
-- proof/ColorPreservation, after Jeremy's review of the statement.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₂)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import strong-rep-var.Types using (Ty; `_; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import strong-rep-var.Ctx
open import strong-rep-var.Conversion
open import strong-rep-var.Terms
open import strong-rep-var.Boundary
open import strong-rep-var.TermSubst
open import strong-rep-var.Reduction
open import strong-rep-var.Residual

-- Renaming through a context is renaming the plugged term.
plug-renCtx² : ∀ (ρ : TyRename) (C : TermCtx) (M : Term)
  → plug (renCtx² ρ C) (renᴹ² (holeRen² ρ C) M) ≡ renᴹ² ρ (plug C M)
plug-renCtx² ρ □ M = refl
plug-renCtx² ρ (ƛC A ∙ C) M =
  cong (ƛ renameᵗ (ordinary ρ) A ∙_) (plug-renCtx² ρ C M)
plug-renCtx² ρ (C ·L N) M =
  cong (_· renᴹ² ρ N) (plug-renCtx² ρ C M)
plug-renCtx² ρ (L ·R C) M =
  cong (renᴹ² ρ L ·_) (plug-renCtx² ρ C M)
plug-renCtx² ρ (ΛC C) M =
  cong Λ_ (plug-renCtx² (underΛ-ren ρ) C M)
plug-renCtx² ρ (C ·C[ B , A ]) M =
  cong (_·[ renameᵗ (extᵗ (ordinary ρ)) B , renameᵗ (ordinary ρ) A ])
    (plug-renCtx² ρ C M)
plug-renCtx² ρ (C ⟪C Θ , c ⟫) M =
  cong (_⟪ renᴮ² ρ Θ , renᶜ (ordinary ρ) c ⟫)
    (plug-renCtx² (underReps-ren (numBinds Θ) ρ) C M)

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

image-sound : ∀ {I C M ρ D N}
  → ImageResidual I C M ρ D N → plug D N ≡ imgTm I
image-sound image-here = refl
image-sound (image-Λ {A = A} {D = D} {N = N} r) =
  cong (_⟪ boundary [] (lock 0 0 ∷ []) , mkId (⇑ᵗ A) ⟫)
    (trans (plug-renCtx² (moveᴿ suc) D N)
           (cong (renᴹ² (moveᴿ suc)) (image-sound r)))

copy-sound : ∀ {σ P C M ρ D N}
  → CopyResidual σ P C M ρ D N → plug D N ≡ substᵐ σ P
copy-sound (copy-var i)   = image-sound i
copy-sound (copy-ƛ r)     = cong₂ ƛ_∙_ refl (copy-sound r)
copy-sound (copy-·L r)    = cong₂ _·_ (copy-sound r) refl
copy-sound (copy-·R r)    = cong₂ _·_ refl (copy-sound r)
copy-sound (copy-Λ r)     = cong Λ_ (copy-sound r)
copy-sound (copy-·[] r)   = cong (_·[ _ , _ ]) (copy-sound r)

residual-source : ∀ {Δ L L′ C M ρ D N} {r : Δ ⊢ L -→ L′}
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
  (residual-CancelR vV ri rc₁ lX rc⋉ sm rc₂ lY)  = refl
residual-source
  (residual-IdPush vV ri rc₁ rc⋉ sm rc₂ lY)      = refl
residual-source (residual-ξ-·-l r)      = cong (_· _) (residual-source r)
residual-source (residual-ξ-·-l-sib r)  = refl
residual-source (residual-ξ-·-r v r)    = cong (_ ·_) (residual-source r)
residual-source (residual-ξ-·-r-sib v r) = refl
residual-source (residual-ξ-·[] r) = cong (_·[ _ , _ ]) (residual-source r)
residual-source (residual-ξ-Λ r)        = cong Λ_ (residual-source r)
residual-source (residual-ξ-⟪⟫ ri r) = cong (_⟪ _ , _ ⟫) (residual-source r)

residual-sound : ∀ {Δ L L′ C M ρ D N} {r : Δ ⊢ L -→ L′}
  → Residual r C M ρ D N → plug D N ≡ L′
residual-sound (residual-TyBeta vN pA) = refl
residual-sound (residual-Beta-body {W = W} {A = A} {C = C} {M = M} vW st) =
  plug-substCtx (betaEnv W A) C M
residual-sound (residual-Beta-arg vW cr) = copy-sound cr
residual-sound (residual-Peel-fun vV vW rc ri rd sc) = refl
residual-sound
  (residual-Peel-arg {Θ = Θ} {V = V} {C = C} {M = M} {s′ = s′} {t = t}
    vV vW rc ri rd sc) =
  cong (λ z → (V · (z ⟪ dualBoundary Θ , s′ ⟫)) ⟪ Θ , t ⟫)
    (plug-renCtx² (moveᴿ (wkN (numBinds Θ))) C M)
residual-sound (residual-TyPeelR-Λ vN rc ⊢s pA) = refl
residual-sound
  (residual-TyPeelR-⟪⟫ {Θ = Θ} {C = C} {M = M} {Θ′ = Θ′} {s″ = s″}
    {s = s} {R = R} {Bᵢ′ = Bᵢ′} vW ri rc rc′ ri⁺ rc″ sc ⊢s sm pA) =
  cong (λ z → ((z ⟪ addLock0 (renᴮ² (moveᴿ suc) Θ′) , `∀ s″ ⟫)
                  ·[ renameᵗ (extᵗ suc) Bᵢ′ , ` 0 ])
                ⟪ instantiate R Θ , instReveal 0 s ⟫)
    (plug-renCtx² (moveᴿ (extN (numBinds Θ′) suc)) C M)
residual-sound
  (residual-CancelR vV ri rc₁ lX rc⋉ sm rc₂ lY) = refl
residual-sound
  (residual-IdPush vV ri rc₁ rc⋉ sm rc₂ lY)     = refl
residual-sound (residual-ξ-·-l r)      = cong (_· _) (residual-sound r)
residual-sound (residual-ξ-·-l-sib r)  = refl
residual-sound (residual-ξ-·-r v r)    = cong (_ ·_) (residual-sound r)
residual-sound (residual-ξ-·-r-sib v r) = refl
residual-sound (residual-ξ-·[] r) = cong (_·[ _ , _ ]) (residual-sound r)
residual-sound (residual-ξ-Λ r)        = cong Λ_ (residual-sound r)
residual-sound (residual-ξ-⟪⟫ ri r) = cong (_⟪ _ , _ ⟫) (residual-sound r)

residuals-sound : ∀ {Δ L L′ C M ρ D N} {rs : Δ ⊢ L -→* L′}
  → Residuals rs C M ρ D N → (plug C M ≡ L) × (plug D N ≡ L′)
residuals-sound residuals-done = refl , refl
residuals-sound (residuals-step r rs) =
  residual-source r , proj₂ (residuals-sound rs)
