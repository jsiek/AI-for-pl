module examples.TermImprecisionRegressionExamples where

-- File Charter:
--   * REGRESSION EXAMPLE for design.md D26 (the generalized right-only
--     boundary rule `⊑⟪⟫` with `Opens`, TermImprecision §2): the
--     counterexample K of proof/DGG/notes/RestrictedForallBoundary.agda
--     (§3), Inst on a ∀-boundary value followed by a Merge of the Inst
--     boundary with the value's own boundary.  Before D26 its final
--     pair `VL ⊑ RF` was related by no rule (`final-unrelated` there),
--     which refuted Sim, SimBack and DGG part 1.  Here every
--     synchronization pair of K derives with the real relation:
--       lk⊑rk, lk₁⊑rk₁   the initial pair and the pair after both
--                        source TyBetas (no opening needed)
--       lk₁⊑rk₃          before the right's Merge: `⊑⟪⟫` at Θ₀ with one
--                        opening of VL (premise `Nk ⊑ Nk`, ⟪⟫⊑⟪⟫)
--       lk₁⊑rk₄, VL⊑RF   after the right's Merge: `⊑⟪⟫` at the merged
--                        Θ₂ with one opening at name 0 (Y, β:=★);
--                        premise `Nk ⊑ idX` by ⟪⟫⊑ (the left's inner
--                        `+X^αᴸ` is left-only, its name rejoins the
--                        right's X through the global pair (αᴸ, αᴿ))
--     and the obligations the old relation refuted are met on K:
--     `sim-K` (Sim at the left's Beta), `simBack-K-merge` (SimBack at
--     the right's Merge: both sides stop), `dgg1-K` (DGG part 1).
--   * THE RUNS (pinned to `evalTerms` by `refl`):
--       L:  LK —→ (TyBeta) LK₁ —→ (Beta) VL
--       R:  RK —→ (TyBeta) RK₁ —→ (Inst) RK₂ —→ (TyBeta) RK₃
--             —→ (Merge) RK₄ —→ (Beta) RF
--   * Copied, with the real relation, from the checked local copy
--     proof/DGG/notes/GeneralizedRightBoundary.agda §4 and its sources
--     (RestrictedForallBoundary §3, FixB's `IntK-ro`, FixA's `int-Θ₂`);
--     no notes module is imported.
--   * Orientation: the LEFT term is the more precise one.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Reduction
  using (InstX; inst-Λ; inst-⟪⟫; _⊢_-→_∣_; _⊢_-→*_; done; _then_)
open import Imprecision
open import ImprecisionWorld
open import proof.ImprecisionWorld
  using (namedᴸ-≤1; namedᴿ-≤1; ≤1-[]; ≤1-∷[])
open import ConversionImprecision
open import TermImprecision
open import proof.TypeSafety.PreservationSupport using (alloc-wf)
open import proof.Ctx using (wf-empty)
open import proof.DGG.Evolve
  using (_⟿[_∣_]_; ev-done; ev-R; ev-noneᴸ; ev-noneᴿ; applyˢ; allocs)
open import examples.TypeCheck using (tc; tf)
open import examples.Eval using (evalTerms; step; StepResult)
open import examples.CambridgeExamples using (I; instI)
open import examples.TermImprecisionExamples
  using (idX; revX; Θ₀; ΔL; ΔLᵢ; ∀X⇒X; int₀; conv₀; Wν; Wν-conv)
open import examples.TermImprecisionRebaseExamples
  using (id★↦; ∀id⊑★; ∀id⊑∀id)

------------------------------------------------------------------------
-- 1. The programs and their runs
------------------------------------------------------------------------

--   L  (λf:∀X.X→X. f) (K[ℕ])        K = ΛY.ΛX.λx:X.x
--   R  (λf:★→★.    f) (K[ℕ]⟨inst⟩)

KK : Term
KK = Λ I

cId cK : Conv
cId = ⌞ ⌞ id (` 0) ⌟ ↦ ⌞ id (` 0) ⌟ ⌟
cK  = ⌞ `∀ cId ⌟

-- VL: the left's ∀-boundary value; Nk = inst_Y(VL); Bm: the merged
-- boundary `[+Y^β, +X^αᴿ] λx:Y.x`
VL Nk Rarg₃ Bm RF : Term
VL    = I ⟪ Θ₀ , cK ⟫
Nk    = idX ⟪ bind 1 1 ∷ [] , cId ⟫
Rarg₃ = (Nk ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩
Bm    = idX ⟪ bind 1 1 ∷ bind 0 0 ∷ [] , revX ⟫
RF    = Bm ⟨ [] ∣ id★↦ ⟩

LK LK₁ RK RK₁ RK₂ RK₃ RK₄ : Term
LK  = (ƛ ∀X⇒X ∙ ` 0) · (ν `ℕ · KK ⟨ cK ⟩)
LK₁ = (ƛ ∀X⇒X ∙ ` 0) · VL
RK  = (ƛ (★ ⇒ ★) ∙ ` 0) · ((ν `ℕ · KK ⟨ cK ⟩) ⟨ [] ∣ instI ⟩)
RK₁ = (ƛ (★ ⇒ ★) ∙ ` 0) · (VL ⟨ [] ∣ instI ⟩)
RK₂ = (ƛ (★ ⇒ ★) ∙ ` 0) · ((ν ★ · VL ⟨ revX ⟩) ⟨ [] ∣ id★↦ ⟩)
RK₃ = (ƛ (★ ⇒ ★) ∙ ` 0) · Rarg₃
RK₄ = (ƛ (★ ⇒ ★) ∙ ` 0) · RF

LK-⊢ : empty ∣ [] ⊢ LK ⦂ ∀X⇒X
LK-⊢ = tc

RK-⊢ : empty ∣ [] ⊢ RK ⦂ ★ ⇒ ★
RK-⊢ = tc

LK-states : evalTerms 20 LK-⊢ ≡ LK ∷ LK₁ ∷ VL ∷ []
LK-states = refl

RK-states : evalTerms 20 RK-⊢ ≡ RK ∷ RK₁ ∷ RK₂ ∷ RK₃ ∷ RK₄ ∷ RF ∷ []
RK-states = refl

-- the right's context after its Inst TyBeta (β:=★)
ΔRk : Ctxᵗ
ΔRk = allocate ★ ΔL

vVL : Value VL
vVL = V-⟪⟫ (S-Λ (V-simple S-ƛ)) I-all

vRF : Value RF
vRF = V-simple (S-cast (V-⟪⟫ S-ƛ I-fun) I-↦)

justStep : ∀ {Δ M} {r : StepResult Δ M} → step Δ M ≡ just r
  → Δ ⊢ M -→ proj₁ r ∣ proj₁ (proj₂ r)
justStep {r = r} _ = proj₂ (proj₂ r)

stL₀ : empty ⊢ LK -→ LK₁ ∣ new `ℕ
stL₀ = justStep refl

stL : ΔL ⊢ LK₁ -→ VL ∣ none
stL = justStep refl

st₀ : empty ⊢ RK -→ RK₁ ∣ new `ℕ
st₀ = justStep refl

st₁ : ΔL ⊢ RK₁ -→ RK₂ ∣ none
st₁ = justStep refl

st₂ : ΔL ⊢ RK₂ -→ RK₃ ∣ new ★
st₂ = justStep refl

st₃ : ΔRk ⊢ RK₃ -→ RK₄ ∣ none
st₃ = justStep refl

st₄ : ΔRk ⊢ RK₄ -→ RF ∣ none
st₄ = justStep refl

-- the Merge alone, on the argument
stM : ΔRk ⊢ Rarg₃ -→ RF ∣ none
stM = justStep refl

------------------------------------------------------------------------
-- 2. The initial pairs (no opening)
------------------------------------------------------------------------

cId⊑cId : ∀ {Δ Δ′} {W : World Δ Δ′} → ` 0 ⊑ᵂ⟨ W ⟩ ` 0 → ConvImp W cId cId
cId⊑cId x = conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦ i i))
  where
  i = conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id x))

νK-ty : NuTy empty `ℕ ∀X⇒X cK ∀X⇒X
νK-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = empty} {M = ν `ℕ · KK ⟨ cK ⟩})))

instI₀-ty : CastTy empty [] instI ∀X⇒X (★ ⇒ ★)
instI₀-ty = proj₂ (proj₂ (cast-inv {Γ = []}
  (tc {Δ = empty} {M = (ν `ℕ · KK ⟨ cK ⟩) ⟨ [] ∣ instI ⟩})))

νK-conv : NuConversionImp ∅ʷ νK-ty νK-ty
νK-conv =
  Wν , Wν-conv , conv-tail⊑tail (conv-mid⊑mid (conv-∀⊑∀ (cId⊑cId X⊑X)))

lk⊑rk : ∅ʷ ∣ [] ⊢ LK ⊑ RK ∶ ∀id⊑★ ∅ʷ
lk⊑rk =
  ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ ∅ʷ} tf tf (x⊑x Zʷ))
    (⊑cast
      (ν⊑ν
        (Λ⊑Λ lift-[] (V-simple (S-Λ (V-simple S-ƛ)))
          (V-simple (S-Λ (V-simple S-ƛ)))
          (Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
            (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)))
          (∀⊑∀ (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X))))
        (ι⊑ι base-ℕ) νK-ty νK-ty νK-conv (∀id⊑∀id ∅ʷ))
      instI₀-ty (∀id⊑★ ∅ʷ))

-- after both source TyBetas (α:=ℕ on each side, matched)
Wk1 : World ΔL ΔL
Wk1 = world [] []↪ []↪ ((0 , 0) ∷ []) []

Wk1ᵢ : World ΔLᵢ ΔLᵢ
Wk1ᵢ = world (X⊑X ∷ []) (keep []↪) (keep []↪) ((0 , 0) ∷ []) []

Wk1-wf : WfWorld Wk1
Wk1-wf = wf-world joint[] agree (namedᴸ-≤1 Wk1 ≤1-[]) (namedᴿ-≤1 Wk1 ≤1-[])
  where
  agree : ∀ {α β} → Paired Wk1 α β → Agree Wk1 α β
  agree (inj₁ here⇔)         = rep-rep r-here r-here (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

Wk1ᵢ-wf : WfWorld Wk1ᵢ
Wk1ᵢ-wf = wf-world (both (inj₁ here⇔) joint[]) agree
  (namedᴸ-≤1 Wk1ᵢ ≤1-∷[]) (namedᴿ-≤1 Wk1ᵢ ≤1-∷[])
  where
  agree : ∀ {α β} → Paired Wk1ᵢ α β → Agree Wk1ᵢ α β
  agree (inj₁ here⇔)         = rep-rep r-here r-here (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

Wk1ᵢ-int : Interior Wk1 Θ₀ Θ₀ Wk1ᵢ
Wk1ᵢ-int = record
  { int-left   = int₀
  ; int-right  = int₀
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                   ; here (there ()) _ ; (there ()) _ _ }
  ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

Wk1ᵢ-conv : ConversionInterior Wk1 Θ₀ Θ₀ Wk1ᵢ
Wk1ᵢ-conv = record
  { conv-left       = conv₀
  ; conv-right      = conv₀
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ { _ _ () _ }
  ; conv-join-fresh = λ
      { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there ()) _
      ; (there ()) _ _
      }
  ; conv-mark-left  = λ { _ () _ }
  ; conv-mark-right = λ { _ () _ }
  }

cK⊑cK : ConvImp Wk1ᵢ cK cK
cK⊑cK = conv-tail⊑tail (conv-mid⊑mid (conv-∀⊑∀ (cId⊑cId X⊑X)))

bVL : BdyTy ΔL Θ₀ ΔLᵢ ∀X⇒X cK ∀X⇒X
bVL = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = VL}))))

instI-ty : CastTy ΔL [] instI ∀X⇒X (★ ⇒ ★)
instI-ty =
  proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔL} {M = VL ⟨ [] ∣ instI ⟩})))

lk₁⊑rk₁ : Wk1 ∣ [] ⊢ LK₁ ⊑ RK₁ ∶ ∀id⊑★ Wk1
lk₁⊑rk₁ =
  ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk1} tf tf (x⊑x Zʷ))
    (⊑cast
      (⟪⟫⊑⟪⟫ Wk1ᵢ-int Wk1ᵢ-wf
        (Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
          (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)))
        bVL bVL (Wk1ᵢ , Wk1ᵢ-conv , cK⊑cK) (∀id⊑∀id Wk1))
      instI-ty (∀id⊑★ Wk1))

------------------------------------------------------------------------
-- 3. Before the right's Merge (RK₃): one opening at Θ₀
------------------------------------------------------------------------

-- the world after the right's Inst TyBeta: (αᴸ, αᴿ) global, β unpaired
Wk : World ΔL ΔRk
Wk = world [] []↪ []↪ ((0 , 1) ∷ []) []

Wk-wf : WfWorld Wk
Wk-wf = wf-world joint[] agree (namedᴸ-≤1 Wk ≤1-[]) (namedᴿ-≤1 Wk ≤1-[])
  where
  agree : ∀ {α β} → Paired Wk α β → Agree Wk α β
  agree (inj₁ here⇔)         = rep-rep r-here (r-there r-here) (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

-- the opened world: Y (the opened left binder) lexically paired with β
PwK : World (underΛ ΔL) (reps ΔRk ∣ (0 ∷ []))
PwK = Wk ⊕⁺ X⊑X ^ 0

PwK-wf : WfWorld PwK
PwK-wf = wf-world (both (inj₂ here⇔) joint[]) agree
  (namedᴸ-≤1 PwK ≤1-∷[]) (namedᴿ-≤1 PwK ≤1-∷[])
  where
  agree : ∀ {α β} → Paired PwK α β → Agree PwK α β
  agree (inj₁ here⇔) =
    rep-rep (r-there-abst r-here) (r-there r-here) (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ here⇔) = abst-★ r-here r-here
  agree (inj₂ (there⇔ ()))

Θ₀-int : ∀ {b Ξ} → ((b ∷ Ξ) ∣ []) ⊢ⁱ Θ₀ ⇒ ((b ∷ Ξ) ∣ (0 ∷ []))
Θ₀-int = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

-- the Inst boundary `+Y^β` alone: Y is introduced right-only
IntK-ro : Interior Wk [] Θ₀ (Wk ⊕ʳ X⊑X ^ 0)
IntK-ro = record
  { int-left   = interior changes[]
  ; int-right  = Θ₀-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  ; mark-left  = λ { (_ , ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

-- inside the inner boundary `+X^α` (both sides): Y at 0, X at 1
ΘX : Boundary
ΘX = bind 1 1 ∷ []

ΔLX ΔRX : Ctxᵗ
ΔLX = (abstR ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])
ΔRX = (bindR ★ ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])

bindX-int : ∀ {b₀ b₁ : RepBinding}
  → ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ [])) ⊢ⁱ ΘX ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ 1 ∷ []))
bindX-int = interior (changes∷ changes[]
  (step-bind (_ , there here) (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))

bindX-conv : ∀ {b₀ b₁ : RepBinding}
  → ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ [])) ⊢ᶜ ΘX ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ 1 ∷ []))
bindX-conv = conversion (conv-bind (_ , there here) conv[]
  (fresh∷ (λ ()) fresh[]) (ins-there ins-here))

WX : World ΔLX ΔRX
WX = world (X⊑X ∷ X⊑X ∷ []) (keep (keep []↪)) (keep (keep []↪))
       ((1 , 1) ∷ []) ((0 , 0) ∷ [])

WX-int : Interior PwK ΘX ΘX WX
WX-int = record
  { int-left   = bindX-int
  ; int-right  = bindX-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ
      { (_ , here) (_ , here) refl refl → (λ _ → refl) , (λ _ → refl)
      ; (_ , here) (_ , there here) _ ()
      ; (_ , here) (_ , there (there ())) _ _
      ; (_ , there here) _ () _
      ; (_ , there (there ())) _ _ _
      }
  ; join-fresh = λ
      { here here (inj₁ ()) ; here here (inj₂ ())
      ; here (there here) _ →
          (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
      ; (there here) here _ →
          (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
      ; (there here) (there here) _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there (there ())) _
      ; (there here) (there (there ())) _
      ; (there (there ())) _ _
      }
  ; mark-left  = λ
      { (_ , here) refl here → here
      ; (_ , there here) () _
      ; (_ , there (there ())) _ _
      }
  ; mark-right = λ
      { (_ , here) refl here → here
      ; (_ , there here) () _
      ; (_ , there (there ())) _ _
      }
  }

WX-conv : ConversionInterior PwK ΘX ΘX WX
WX-conv = record
  { conv-left       = bindX-conv
  ; conv-right      = bindX-conv
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ
      { here here here here → (λ _ → refl) , (λ _ → refl)
      ; here here here (there ())
      ; here here (there ()) _
      ; here (there here) _ (there ())
      ; here (there (there ())) _ _
      ; (there here) _ (there ()) _
      ; (there (there ())) _ _ _
      }
  ; conv-join-fresh = λ
      { here here (inj₁ (fresh∷ n _)) → ⊥-elim (n refl)
      ; here here (inj₂ (fresh∷ n _)) → ⊥-elim (n refl)
      ; here (there here) _ →
          (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
      ; (there here) here _ →
          (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
      ; (there here) (there here) _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there (there ())) _
      ; (there here) (there (there ())) _
      ; (there (there ())) _ _
      }
  ; conv-mark-left  = λ
      { here here here → here
      ; here (there ()) _
      ; (there here) (there ()) _
      ; (there (there ())) _ _
      }
  ; conv-mark-right = λ
      { here here here → here
      ; here (there ()) _
      ; (there here) (there ()) _
      ; (there (there ())) _ _
      }
  }

-- WX's lexical and global pairs (the same ϱ as the opened world WoK
-- below)
uniqᴸX : ∀ {α α′ β} → Paired WX α β → Paired WX α′ β → α ≡ α′
uniqᴸX (inj₁ here⇔) (inj₁ here⇔) = refl
uniqᴸX (inj₁ here⇔) (inj₁ (there⇔ ()))
uniqᴸX (inj₁ (there⇔ ())) _
uniqᴸX (inj₂ here⇔) (inj₂ here⇔) = refl
uniqᴸX (inj₂ here⇔) (inj₂ (there⇔ ()))
uniqᴸX (inj₂ (there⇔ ())) _
uniqᴸX (inj₁ here⇔) (inj₂ (there⇔ ()))
uniqᴸX (inj₂ here⇔) (inj₁ (there⇔ ()))

uniqᴿX : ∀ {α β β′} → Paired WX α β → Paired WX α β′ → β ≡ β′
uniqᴿX (inj₁ here⇔) (inj₁ here⇔) = refl
uniqᴿX (inj₁ here⇔) (inj₁ (there⇔ ()))
uniqᴿX (inj₁ (there⇔ ())) _
uniqᴿX (inj₂ here⇔) (inj₂ here⇔) = refl
uniqᴿX (inj₂ here⇔) (inj₂ (there⇔ ()))
uniqᴿX (inj₂ (there⇔ ())) _
uniqᴿX (inj₁ here⇔) (inj₂ (there⇔ ()))
uniqᴿX (inj₂ here⇔) (inj₁ (there⇔ ()))

WX-wf : WfWorld WX
WX-wf = wf-world (both (inj₂ here⇔) (both (inj₁ here⇔) joint[])) agree
  (λ _ _ _ → uniqᴸX) (λ _ _ _ → uniqᴿX)
  where
  agree : ∀ {α β} → Paired WX α β → Agree WX α β
  agree (inj₁ here⇔) =
    rep-rep (r-there-abst r-here) (r-there r-here) (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ here⇔) = abst-★ r-here r-here
  agree (inj₂ (there⇔ ()))

-- inst_Y(VL) is literally the right's interior Nk
instVL : InstX VL Nk
instVL = inst-⟪⟫ (S-Λ (V-simple S-ƛ)) (inst-Λ (V-simple S-ƛ))

VL-⊢ : ΔL ∣ [] ⊢ VL ⦂ ∀X⇒X
VL-⊢ = tc

bNL : BdyTy (underΛ ΔL) ΘX ΔLX (` 0 ⇒ ` 0) cId (` 0 ⇒ ` 0)
bNL = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = underΛ ΔL} {M = Nk}))))

bNR : BdyTy (reps ΔRk ∣ (0 ∷ [])) ΘX ΔRX (` 0 ⇒ ` 0) cId (` 0 ⇒ ` 0)
bNR = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = reps ΔRk ∣ (0 ∷ [])} {M = Nk}))))

bOutK : BdyTy ΔRk Θ₀ (reps ΔRk ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bOutK = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΔRk} {M = Nk ⟪ Θ₀ , revX ⟫}))))

id★↦ᴿk-ty : CastTy ΔRk [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
id★↦ᴿk-ty = cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl

-- one opening of VL (inst-⟪⟫) at the Inst boundary's name 0
openVLₖ : Opens Θ₀ (Wk ⊕ʳ X⊑X ^ 0) VL ∀X⇒X PwK Nk (` 0 ⇒ ` 0)
openVLₖ =
  open-∀ nv-⇒ (∈-⇒ˡ ∈-var) vVL VL-⊢ instVL refl (open-⊕ r-here) open-none

Nk⊑Nk : PwK ∣ [] ⊢ Nk ⊑ Nk ∶ ⇒⊑⇒ X⊑X X⊑X
Nk⊑Nk =
  ⟪⟫⊑⟪⟫ WX-int WX-wf (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bNL bNR
    (WX , WX-conv , cId⊑cId X⊑X) (⇒⊑⇒ X⊑X X⊑X)

VL⊑Rarg₃ : Wk ∣ [] ⊢ VL ⊑ Rarg₃ ∶ ∀id⊑★ Wk
VL⊑Rarg₃ =
  ⊑cast (⊑⟪⟫ IntK-ro openVLₖ PwK-wf Nk⊑Nk bOutK (∀id⊑★ Wk))
    id★↦ᴿk-ty (∀id⊑★ Wk)

lk₁⊑rk₃ : Wk ∣ [] ⊢ LK₁ ⊑ RK₃ ∶ ∀id⊑★ Wk
lk₁⊑rk₃ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑Rarg₃

------------------------------------------------------------------------
-- 4. After the right's Merge (RK₄, RF): one opening at the merged Θ₂
------------------------------------------------------------------------

Θ₂ : Boundary
Θ₂ = bind 1 1 ∷ bind 0 0 ∷ []

int-Θ₂ : ∀ {b₀ b₁ : RepBinding}
  → ((b₀ ∷ b₁ ∷ []) ∣ []) ⊢ⁱ Θ₂ ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ 1 ∷ []))
int-Θ₂ = interior
  (changes∷ (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))
    (step-bind (_ , there here) (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))

bBm : BdyTy ΔRk Θ₂ ΔRX (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bBm = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔRk} {M = Bm}))))

-- inside the merged `+Y^β, +X^αᴿ`: both right names right-only
WiR : World ΔL ΔRX
WiR = world (X⊑X ∷ X⊑X ∷ []) (skip (skip []↪)) (keep (keep []↪))
        ((0 , 1) ∷ []) []

-- the opened world: the left's opened binder joins Y (β:=★)
WoK : World (underΛ ΔL) ΔRX
WoK = world (X⊑X ∷ X⊑X ∷ []) (keep (skip []↪)) (keep (keep []↪))
        ((1 , 1) ∷ []) ((0 , 0) ∷ [])

IntK-Θ₂ : Interior Wk [] Θ₂ WiR
IntK-Θ₂ = record
  { int-left   = interior changes[]
  ; int-right  = int-Θ₂
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  ; mark-left  = λ { (_ , ()) _ _ }
  ; mark-right = λ
      { (_ , here) () _ ; (_ , there here) () _
      ; (_ , there (there ())) _ _ }
  }

openK : Open1 WiR 0 WoK
openK = open1 join-here here r-here

openVL : Opens Θ₂ WiR VL ∀X⇒X WoK Nk (` 0 ⇒ ` 0)
openVL = open-∀ nv-⇒ (∈-⇒ˡ ∈-var) vVL VL-⊢ instVL refl openK open-none

WoK-wf : WfWorld WoK
WoK-wf = wf-world (both (inj₂ here⇔) (right-only joint[])) agree
  (λ _ _ _ → uniqᴸX) (λ _ _ _ → uniqᴿX)
  where
  agree : ∀ {α β} → Paired WoK α β → Agree WoK α β
  agree (inj₁ here⇔) =
    rep-rep (r-there-abst r-here) (r-there r-here) (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ here⇔) = abst-★ r-here r-here
  agree (inj₂ (there⇔ ()))

-- inside the left's inner `+X^αᴸ` (left-only): the interior world WX
IntK-X : Interior WoK ΘX [] WX
IntK-X = record
  { int-left   = bindX-int
  ; int-right  = interior changes[]
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ
      { (_ , here) (_ , here) refl refl → (λ _ → refl) , (λ _ → refl)
      ; (_ , here) (_ , there here) refl refl → (λ ()) , (λ ())
      ; (_ , here) (_ , there (there ())) _ _
      ; (_ , there here) _ () _
      ; (_ , there (there ())) _ _ _
      }
  ; join-fresh = λ
      { here here (inj₁ ()) ; here here (inj₂ ())
      ; here (there here) (inj₁ ()) ; here (there here) (inj₂ ())
      ; (there here) here _ →
          (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
      ; (there here) (there here) _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; _ (there (there ())) _
      ; (there (there ())) _ _
      }
  ; mark-left  = λ
      { (_ , here) refl x → x
      ; (_ , there here) () _
      ; (_ , there (there ())) _ _
      }
  ; mark-right = λ
      { (_ , here) refl x → x
      ; (_ , there here) refl x → x
      ; (_ , there (there ())) _ _
      }
  }

Nk⊑idX : WoK ∣ [] ⊢ Nk ⊑ idX ∶ ⇒⊑⇒ X⊑X X⊑X
Nk⊑idX =
  ⟪⟫⊑ IntK-X WX-wf (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bNL (⇒⊑⇒ X⊑X X⊑X)

-- THE FINAL ARGUMENT PAIR (unrelated before D26)
VL⊑Bm : Wk ∣ [] ⊢ VL ⊑ Bm ∶ ∀id⊑★ Wk
VL⊑Bm = ⊑⟪⟫ IntK-Θ₂ openVL WoK-wf Nk⊑idX bBm (∀id⊑★ Wk)

VL⊑RF : Wk ∣ [] ⊢ VL ⊑ RF ∶ ∀id⊑★ Wk
VL⊑RF = ⊑cast VL⊑Bm id★↦ᴿk-ty (∀id⊑★ Wk)

lk₁⊑rk₄ : Wk ∣ [] ⊢ LK₁ ⊑ RK₄ ∶ ∀id⊑★ Wk
lk₁⊑rk₄ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑RF

------------------------------------------------------------------------
-- 5. The obligations the relation before D26 refuted on K
------------------------------------------------------------------------

-- Sim at (LK₁, RK₁) and the left's Beta: the right runs Inst, TyBeta,
-- Merge, Beta (SimDef's conclusion)
sim-K :
  ∃[ N′ ] Σ[ r′ ∈ ΔL ⊢ RK₁ -→* N′ ]
    Σ[ W′ ∈ World ΔL (applyˢ (allocs r′) ΔL) ]
      (Wk1 ⟿[ none ∷ [] ∣ allocs r′ ] W′) × WfWorld W′
      × Σ[ q ∈ ∀X⇒X ⊑ᵂ⟨ W′ ⟩ (★ ⇒ ★) ] (W′ ∣ [] ⊢ VL ⊑ N′ ∶ q)
sim-K =
  RF , (st₁ then st₂ then st₃ then st₄ then done) , Wk ,
  ev-noneᴸ (ev-noneᴿ (ev-R wfᴿ-★ (ev-noneᴿ (ev-noneᴿ ev-done)))) ,
  Wk-wf , ∀id⊑★ Wk , VL⊑RF

-- SimBack at the right's Merge (VL ⊑ Rarg₃, Rarg₃ —→ RF): both sides
-- stop; the premise changes from ⟪⟫⊑⟪⟫ (Nk ⊑ Nk) to ⟪⟫⊑ (Nk ⊑ idX),
-- the opening stays at name 0
simBack-K-merge :
  Σ[ r ∈ ΔL ⊢ VL -→* VL ] Σ[ r″ ∈ ΔRk ⊢ RF -→* RF ]
    Σ[ W′ ∈ World (applyˢ (allocs r) ΔL)
                  (applyˢ (allocs (stM then r″)) ΔRk) ]
      (Wk ⟿[ allocs r ∣ allocs (stM then r″) ] W′) × WfWorld W′
      × Σ[ q ∈ ∀X⇒X ⊑ᵂ⟨ W′ ⟩ (★ ⇒ ★) ] (W′ ∣ [] ⊢ VL ⊑ RF ∶ q)
simBack-K-merge = done , done , Wk , ev-noneᴿ ev-done , Wk-wf , _ , VL⊑RF

-- DGG part 1 on the initial pair: the right also reaches a value,
-- related to the left's
dgg1-K :
  ∃[ V′ ] Σ[ r′ ∈ empty ⊢ RK -→* V′ ] Value V′
    × Σ[ W′ ∈ World ΔL (applyˢ (allocs r′) empty) ]
        Σ[ q ∈ ∀X⇒X ⊑ᵂ⟨ W′ ⟩ (★ ⇒ ★) ] (W′ ∣ [] ⊢ VL ⊑ V′ ∶ q)
dgg1-K =
  RF , (st₀ then st₁ then st₂ then st₃ then st₄ then done) , vRF ,
  Wk , ∀id⊑★ Wk , VL⊑RF
