module examples.TermImprecisionRegressionExamples where

-- File Charter:
--   * REGRESSION EXAMPLE for design.md D26 and D27: the counterexample
--     K of proof/DGG/notes/RestrictedForallBoundary.agda (§3), Inst on
--     a ∀-boundary value followed by a Merge of the Inst boundary with
--     the value's own boundary.  Before D26 its final pair `VL ⊑ RF`
--     was related by no rule (`final-unrelated` there), which refuted
--     Sim, SimBack and DGG part 1.  Here every synchronization pair of
--     K derives with the real relation (D31: openings are slots of the
--     index, TermImprecision §2):
--       lk⊑rk, lk₁⊑rk₁   the initial pair and the pair after both
--                        source TyBetas (no slot)
--       VL⊑idX           THE COMMON PREMISE, Y opened: ⟪⟫⊑ passes the
--                        slot into VL's ∀-boundary, Λ⊑ joins it
--       lk₁⊑rk₄, VL⊑RF   after the right's Merge: `⊑⟪⟫` at the merged
--                        Θ₂ OPENS Y (type variable 0, β:=★, X⊑X: no
--                        permission, design.md D28)
--       lk₁⊑rk₃          before the right's Merge, right-first: `⊑⟪⟫`
--                        at Θ₀ opens Y, the inner `⊑⟪⟫` at ΘX carries
--                        the slot, then VL⊑idX
--     and the obligations the old relation refuted are met on K:
--     `sim-K` (Sim at the left's Beta), `simBack-K-merge` (SimBack at
--     the right's Merge: both sides stop), `dgg1-K` (DGG part 1).
--     `no-push-K`: without the opening the premise index is empty.
--   * §6 regression facts: the ★-embedding counterexample pair is
--     unrelated (`cx-unrelated`, any world), and under a slot the left
--     term is a value (`slot-value`, design.md D31).
--   * THE RUNS (pinned to `evalTerms` by `refl`):
--       L:  LK —→ (TyBeta) LK₁ —→ (Beta) VL
--       R:  RK —→ (TyBeta) RK₁ —→ (Inst) RK₂ —→ (TyBeta) RK₃
--             —→ (Merge) RK₄ —→ (Beta) RF
--   * Copied, with the real relation, from the checked local copy
--     proof/DGG/notes/PendingOpenings.agda §3, §5 (and, for D26,
--     GeneralizedRightBoundary.agda §4); no notes module is imported.
--     No permission anywhere (design.md D28, D31): the opened Y and the
--     shared X are X⊑X, and every index of K uses only X ⊑ X at them;
--     the `⟪⟫⊑` of `VL⊑idX` passes R1′ with `ok-bind ∷ []`.
--   * Orientation: the LEFT term is the more precise one.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Reduction using (_⊢_-→_∣_; _⊢_-→*_; done; _then_)
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
-- 2. The initial pairs (no slot)
------------------------------------------------------------------------

cId⊑cId : ∀ {Δ Δ′} {W : World Δ Δ′} → marksʷ W ⊢ embᴸ W (` 0) ⊑ embᴿ W (` 0)
  → ConvImp W cId cId
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
Wk1 = world⁰ 0 []↪ []↪ ((0 , 0) ∷ []) []

Wk1ᵢ : World ΔLᵢ ΔLᵢ
Wk1ᵢ = world⁰ 1 (keep []↪) (keep []↪) ((0 , 0) ∷ []) []

Wk1-wf : WfWorld Wk1
Wk1-wf = wf-world joint[] agree (namedᴸ-≤1 Wk1 ≤1-[]) (namedᴿ-≤1 Wk1 ≤1-[])
  []
  where
  agree : ∀ {α β} → Paired Wk1 α β → Agree Wk1 α β
  agree (inj₁ here⇔)         = rep-rep r-here r-here (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

Wk1ᵢ-wf : WfWorld Wk1ᵢ
Wk1ᵢ-wf = wf-world (both (inj₁ here⇔) joint[]) agree
  (namedᴸ-≤1 Wk1ᵢ ≤1-∷[]) (namedᴿ-≤1 Wk1ᵢ ≤1-∷[]) []
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
  ; same-κ     = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                   ; here (there ()) _ ; (there ()) _ _ }
  }

Wk1ᵢ-conv : ConversionInterior Wk1 Θ₀ Θ₀ Wk1ᵢ
Wk1ᵢ-conv = record
  { conv-left       = conv₀
  ; conv-right      = conv₀
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-same-κ     = refl
  ; conv-join-cont  = λ { _ _ () _ }
  ; conv-join-fresh = λ
      { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there ()) _
      ; (there ()) _ _
      }
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
      (⟪⟫⊑⟪⟫₀ Wk1ᵢ-int Wk1ᵢ-wf
        (Λ⊑Λ lift-[] (V-simple S-ƛ) (V-simple S-ƛ)
          (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)))
        bVL bVL (Wk1ᵢ , Wk1ᵢ-conv , cK⊑cK) (∀id⊑∀id Wk1))
      instI-ty (∀id⊑★ Wk1))

------------------------------------------------------------------------
-- 3. The worlds and boundaries after the right's Inst TyBeta
------------------------------------------------------------------------

-- the world after the right's Inst TyBeta: (αᴸ, αᴿ) global, β unpaired
Wk : World ΔL ΔRk
Wk = world⁰ 0 []↪ []↪ ((0 , 1) ∷ []) []

Wk-wf : WfWorld Wk
Wk-wf = wf-world joint[] agree (namedᴸ-≤1 Wk ≤1-[]) (namedᴿ-≤1 Wk ≤1-[]) []
  where
  agree : ∀ {α β} → Paired Wk α β → Agree Wk α β
  agree (inj₁ here⇔)         = rep-rep r-here (r-there r-here) (ι⊑ι base-ℕ)
  agree (inj₁ (there⇔ ()))
  agree (inj₂ ())

Θ₀-int : ∀ {b Ξ} → ((b ∷ Ξ) ∣ []) ⊢ⁱ Θ₀ ⇒ ((b ∷ Ξ) ∣ (0 ∷ []))
Θ₀-int = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

-- the Inst boundary `+Y^β` alone: Y is introduced right-only (X⊑X: β is
-- not permitted, design.md D28); the boundary OPENS the left's ∀ at Y
-- (a slot of the index, design.md D31)
IntK-ro : Interior Wk [] Θ₀ (Wk ⊕ʳ^ 0)
IntK-ro = record
  { int-left   = interior changes[]
  ; int-right  = Θ₀-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; same-κ     = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  }

-- inside the inner boundary `+X^α`: Y at 0, X at 1
ΘX : Boundary
ΘX = bind 1 1 ∷ []

ΔLX ΔRX : Ctxᵗ
ΔLX = (abstR ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])
ΔRX = (bindR ★ ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])

bindX-int : ∀ {b₀ b₁ : RepBinding}
  → ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ [])) ⊢ⁱ ΘX ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ 1 ∷ []))
bindX-int = interior (changes∷ changes[]
  (step-bind (_ , there here) (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))

-- the merged boundary `+Y^β, +X^αᴿ`
Θ₂ : Boundary
Θ₂ = bind 1 1 ∷ bind 0 0 ∷ []

int-Θ₂ : ∀ {b₀ b₁ : RepBinding}
  → ((b₀ ∷ b₁ ∷ []) ∣ []) ⊢ⁱ Θ₂ ⇒ ((b₀ ∷ b₁ ∷ []) ∣ (0 ∷ 1 ∷ []))
int-Θ₂ = interior
  (changes∷ (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))
    (step-bind (_ , there here) (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))

bNR : BdyTy (reps ΔRk ∣ (0 ∷ [])) ΘX ΔRX (` 0 ⇒ ` 0) cId (` 0 ⇒ ` 0)
bNR = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = reps ΔRk ∣ (0 ∷ [])} {M = Nk}))))

bOutK : BdyTy ΔRk Θ₀ (reps ΔRk ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bOutK = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΔRk} {M = Nk ⟪ Θ₀ , revX ⟫}))))

bBm : BdyTy ΔRk Θ₂ ΔRX (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bBm = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔRk} {M = Bm}))))

id★↦ᴿk-ty : CastTy ΔRk [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
id★↦ᴿk-ty = cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl

-- The worlds of the opened type variable Y (design.md D31).  Right type
-- variables inside the merged `+Y^β, +X^αᴿ`: Y at 0 (β:=★, OPENED,
-- X⊑X: the slot `opn 0`), X at 1 (αᴿ:=ℕ).

-- inside Θ₂ (and inside the Inst boundary's inner `+X^αᴿ`): no left
-- type variable, Y opened
WiR★ : World ΔL ΔRX
WiR★ = world⁰ 2 (skip (skip []↪)) (keep (keep []↪))
         ((0 , 1) ∷ []) []

-- inside the left's `+X^αᴸ` as well: X joined through (αᴸ, αᴿ)
Wx★ : World ΔLᵢ ΔRX
Wx★ = world⁰ 2 (skip (keep []↪)) (keep (keep []↪))
        ((0 , 1) ∷ []) []

-- after the join of Y: the left binder Y joins the right's Y, its
-- abstract rep. var paired lexically with β
WX★ : World ΔLX ΔRX
WX★ = world⁰ 2 (keep (keep []↪)) (keep (keep []↪))
        ((1 , 1) ∷ []) ((0 , 0) ∷ [])

openX★ : Join1 Wx★ 0 WX★
openX★ = join1 join-here here r-here

IntΘ₂★ : Interior Wk [] Θ₂ WiR★
IntΘ₂★ = record
  { int-left   = interior changes[]
  ; int-right  = int-Θ₂
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; same-κ     = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  }

Wx-fresh : ∀ {X X′ α β}
  → ΔLᵢ ∋ᵗ X := α → ΔRX ∋ᵗ X′ := β
  → (Joins Wx★ X X′ → Paired WiR★ α β) × (Paired WiR★ α β → Joins Wx★ X X′)
Wx-fresh here here = (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ ()) })
Wx-fresh here (there here) = (λ _ → inj₁ here⇔) , (λ _ → refl)
Wx-fresh here (there (there ()))
Wx-fresh (there ()) _

IntX★ : Interior WiR★ Θ₀ [] Wx★
IntX★ = record
  { int-left   = int₀
  ; int-right  = interior changes[]
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; same-κ     = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ a b _ → Wx-fresh a b
  }

-- the Inst boundary `+Y^β` alone (before the Merge), Y opened
WiY★ : World ΔL (reps ΔRk ∣ (0 ∷ []))
WiY★ = Wk ⊕ʳ^ 0

-- the right's inner `+X^αᴿ` carries Y (toExt ΘX 0 = just 0)
IntXc★ : Interior WiY★ [] ΘX WiR★
IntXc★ = record
  { int-left   = interior changes[]
  ; int-right  = bindX-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; same-κ     = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  }

agreeₖ : ∀ {Δ₀ Δ₀′} {W : World Δ₀ Δ₀′} → Δ₀ ∋rep 0 := `ℕ
  → Δ₀′ ∋rep 1 := `ℕ → ϱᵍʷ W ≡ (0 , 1) ∷ [] → ϱˡʷ W ≡ []
  → ∀ {α β} → Paired W α β → Agree W α β
agreeₖ l r refl refl (inj₁ here⇔) = rep-rep l r (ι⊑ι base-ℕ)
agreeₖ l r refl refl (inj₁ (there⇔ ()))
agreeₖ l r refl refl (inj₂ ())

WiR★-wf : WfWorld WiR★
WiR★-wf = wf-world (right-only (right-only joint[]))
  (agreeₖ r-here (r-there r-here) refl refl)
  (namedᴸ-≤1 WiR★ ≤1-[]) (λ { (_ , ()) _ _ _ _ })
  []

-- Y's opening is well formed (design.md D31), inside Θ₂ (or ΘX) and
-- inside the Inst boundary alone
okR★ : All (SlotOK WiR★) (opn 0 ∷ [])
okR★ = (0 , here , r-here , (λ { (_ , ()) }) , (λ { (_ , ()) })) ∷ []

okY★ : All (SlotOK WiY★) (opn 0 ∷ [])
okY★ = (0 , here , r-here , (λ { (_ , ()) }) , (λ { (_ , ()) })) ∷ []

uniqᴿx : NamedUniqueᴿ Wx★
uniqᴿx _ _ _ (inj₁ here⇔) (inj₁ here⇔) = refl
uniqᴿx _ _ _ (inj₁ here⇔) (inj₁ (there⇔ ()))
uniqᴿx _ _ _ (inj₁ (there⇔ ())) _
uniqᴿx _ _ _ (inj₂ ()) _
uniqᴿx _ _ _ _ (inj₂ ())

Wx★-wf : WfWorld Wx★
Wx★-wf = wf-world (right-only (both (inj₁ here⇔) joint[]))
  (agreeₖ r-here (r-there r-here) refl refl)
  (namedᴸ-≤1 Wx★ ≤1-∷[]) uniqᴿx
  []

WiY★-wf : WfWorld WiY★
WiY★-wf = wf-world (right-only joint[])
  (agreeₖ r-here (r-there r-here) refl refl)
  (namedᴸ-≤1 WiY★ ≤1-[]) (namedᴿ-≤1 WiY★ ≤1-∷[])
  []

------------------------------------------------------------------------
-- 4. The pairs with Y opened: open, pass, join (design.md D31)
------------------------------------------------------------------------

-- THE COMMON PREMISE: inside the right boundary, Y opened.  ⟪⟫⊑ passes
-- the slot into VL's boundary (cK = ∀Y.cId), Λ⊑ joins it, ƛ⊑ƛ at Y ⊑ Y
VL⊑idX : WiR★ ∣ [] ⊢ VL ⊑ idX
  ∶⟨ ∀X⇒X , ` 0 ⇒ ` 0 ⟩[ opn 0 ∷ [] ] ⇒⊑⇒ X⊑X X⊑X
VL⊑idX =
  ⟪⟫⊑ IntX★ (ok-bind ∷ []) (bo-∀ (S-Λ (V-simple S-ƛ)) (fc-∷ fc-[])) []
    Wx★-wf (⇒⊑⇒ X⊑X X⊑X)
    (Λ⊑ (b-join openX★) nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
      (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) (⇒⊑⇒ X⊑X X⊑X))
    bVL (⇒⊑⇒ X⊑X X⊑X)

-- after the right's Merge (RK₄, RF): ⊑⟪⟫ at the merged Θ₂ OPENS Y.
-- THE FINAL ARGUMENT PAIR (unrelated before D26)
VL⊑Bm : Wk ∣ [] ⊢ VL ⊑ Bm ∶ ∀id⊑★ Wk
VL⊑Bm =
  ⊑⟪⟫ IntΘ₂★ (push ca-[] f-end (ns-opn refl ∷ []) (inj₂ vVL)) okR★
    ([] ∷ []) [] WiR★-wf (⇒⊑⇒ X⊑X X⊑X) VL⊑idX bBm (∀id⊑★ Wk)

VL⊑RF : Wk ∣ [] ⊢ VL ⊑ RF ∶ ∀id⊑★ Wk
VL⊑RF = ⊑cast VL⊑Bm id★↦ᴿk-ty (∀id⊑★ Wk)

lk₁⊑rk₄ : Wk ∣ [] ⊢ LK₁ ⊑ RK₄ ∶ ∀id⊑★ Wk
lk₁⊑rk₄ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑RF

-- before the Merge (RK₃), RIGHT-FIRST: ⊑⟪⟫ at Θ₀ opens Y, the inner
-- ⊑⟪⟫ at ΘX CARRIES the slot; the premise is VL⊑idX again
VL⊑Nk : WiY★ ∣ [] ⊢ VL ⊑ Nk
  ∶⟨ ∀X⇒X , ` 0 ⇒ ` 0 ⟩[ opn 0 ∷ [] ] ⇒⊑⇒ X⊑X X⊑X
VL⊑Nk =
  ⊑⟪⟫ IntXc★ (push (ca-opn refl ca-[]) (f-keep f-end) [] (inj₁ refl))
    okR★ ([] ∷ []) [] WiR★-wf (⇒⊑⇒ X⊑X X⊑X) VL⊑idX bNR (⇒⊑⇒ X⊑X X⊑X)

VL⊑Rarg₃ : Wk ∣ [] ⊢ VL ⊑ Rarg₃ ∶ ∀id⊑★ Wk
VL⊑Rarg₃ =
  ⊑cast
    (⊑⟪⟫ IntK-ro (push ca-[] f-end (ns-opn refl ∷ []) (inj₂ vVL)) okY★
      ([] ∷ []) [] WiY★-wf (⇒⊑⇒ X⊑X X⊑X) VL⊑Nk bOutK (∀id⊑★ Wk))
    id★↦ᴿk-ty (∀id⊑★ Wk)

lk₁⊑rk₃ : Wk ∣ [] ⊢ LK₁ ⊑ RK₃ ∶ ∀id⊑★ Wk
lk₁⊑rk₃ = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑Rarg₃

-- K NEEDS its opening: with no slot, the premise index of `VL ⊑ Bm`
-- inside Θ₂ is empty (Y is right-only)
no-push-K : ¬ (∀X⇒X ⊑ᵂ⟨ WiR★ ⟩ (` 0 ⇒ ` 0))
no-push-K (∀⊑ _ _ (⇒⊑⇒ () _))

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
-- stop; the premise `VL⊑idX` does not change (the opening at Θ₀ and the
-- carry at ΘX compose into the opening at the merged Θ₂)
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

------------------------------------------------------------------------
-- 6. Regression facts of design.md D27 and D31 (proof/DGG/notes/
--    PendingOpenings §5): the ★-embedding counterexample pair is
--    unrelated, and under a slot the left term is a value
------------------------------------------------------------------------

-- The ★-embedding counterexample (proof/DGG/notes/StarEmbedding.md):
--   L  (λx:ℕ. x) 5                     —→* 5
--   R  ((ΛY. λx:Y. x⟨Y!⟩)⟨inst Y.(Y?ℓ0 → id(★))⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩  —→* blame
-- CX-R₂ is R after its Inst and TyBeta.  The ★-embedded relation
-- related (CX-L, CX-R₂); D31's relation does not, in any world.
CX-tagY CX-BdY CX-L CX-R CX-R₂ : Term
CX-tagY = ` 0 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩
CX-BdY  = (ƛ (` 0) ∙ CX-tagY) ⟪ Θ₀ , reveal 0 (` 0 ⇒ ★) ⟫
CX-L    = (ƛ `ℕ ∙ ` 0) · $ 5
CX-R    = ((Λ (ƛ (` 0) ∙ CX-tagY) ⟨ [] ∣ instᵖ (((` 0) ？ 0) ↦ᵖ idᵖ ★) ⟩)
            · ($ 5 ⟨ [] ∣ `ℕ ! ⟩)) ⟨ [] ∣ `ℕ ？ 0 ⟩
CX-R₂   = ((CX-BdY ⟨ [] ∣ id★↦ ⟩) · ($ 5 ⟨ [] ∣ `ℕ ! ⟩)) ⟨ [] ∣ `ℕ ？ 0 ⟩

CX-R-⊢ : empty ∣ [] ⊢ CX-R ⦂ `ℕ
CX-R-⊢ = tc

CX-R₂-state : Data.List.head (Data.List.drop 2 (evalTerms 30 CX-R-⊢))
  ≡ just CX-R₂
CX-R₂-state = refl

-- the only way down is ⊑cast, ·⊑·, ⊑cast, ⊑⟪⟫, and then
-- `λx:ℕ.x ⊑ λx:Y.x⟨Y!⟩` at any slots: only ƛ⊑ƛ has a λ on the left (at
-- no slot), and it needs `ℕ ⊑ Y` in a world, which `_⊢_⊑_` lacks
no-ƛℕ⊑ƛX : ∀ {Δ Δ′} {W : World Δ Δ′} {γ N N′ X O A A′}
    {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → ¬ (W ∣ γ ⊢ ƛ `ℕ ∙ N ⊑ ƛ (` X) ∙ N′ ∶[ O ] p)
no-ƛℕ⊑ƛX (ƛ⊑ƛ {pA = ()} _ _ _)

cx-unrelated : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → ¬ (W ∣ γ ⊢ CX-L ⊑ CX-R₂ ∶ p)
cx-unrelated
  (⊑cast (·⊑· (⊑cast (⊑⟪⟫ _ _ _ _ _ _ _ d _ _) _ _) _) _ _) =
  no-ƛℕ⊑ƛX d

-- under a slot the left term is a value (design.md D31)
carried-≢[] : ∀ {Θ′ O O′} → Carried Θ′ O O′ → O ≢ [] → O′ ≢ []
carried-≢[] ca-[]         ne = λ _ → ne refl
carried-≢[] (ca-opn _ _)  ne = λ ()
carried-≢[] (ca-skp _)    ne = λ ()

fill-≢[] : ∀ {O′ N Oᵢ} → Fill O′ N Oᵢ → O′ ≢ [] → Oᵢ ≢ []
fill-≢[] f-end      ne = λ _ → ne refl
fill-≢[] (f-keep _) ne = λ ()
fill-≢[] (f-fill _) ne = λ ()

slot-value : ∀ {Δ Δ′} {W : World Δ Δ′} {γ M M′ O A A′}
    {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → W ∣ γ ⊢ M ⊑ M′ ∶[ O ] p → O ≢ [] → Value M
slot-value (x⊑x _) ne = ⊥-elim (ne refl)
slot-value (κ⊑κ _ _) ne = ⊥-elim (ne refl)
slot-value (ƛ⊑ƛ _ _ _) ne = ⊥-elim (ne refl)
slot-value (·⊑· _ _) ne = ⊥-elim (ne refl)
slot-value (blame⊑ _ _ _) ne = ⊥-elim (ne refl)
slot-value (cast⊑cast _ _ _ _) ne = ⊥-elim (ne refl)
slot-value (cast⊑ co-plain _ _ _) ne = ⊥-elim (ne refl)
slot-value (cast⊑ (co-∀ v _) _ _ _) ne = V-simple (S-cast v I-∀ᵖ)
slot-value (cast⊑ (co-gen v _) _ _ _) ne = V-simple (S-cast v I-gen)
slot-value (⊑cast d _ _) ne = slot-value d ne
slot-value (Λ⊑Λ _ _ _ _ _) ne = ⊥-elim (ne refl)
slot-value (Λ⊑ b-fresh _ _ _ _ _ _) ne = ⊥-elim (ne refl)
slot-value (Λ⊑ (b-rep _ _ _) _ _ _ _ _ _) ne = ⊥-elim (ne refl)
slot-value (Λ⊑ (b-join _) _ _ _ v _ _) ne = V-simple (S-Λ v)
slot-value (ν⊑ν _ _ _ _ _ _) ne = ⊥-elim (ne refl)
slot-value (ν⊑ _ _ _ _) ne = ⊥-elim (ne refl)
slot-value (⟪⟫⊑⟪⟫ _ _ _ _ _ _ _ _ _) ne = ⊥-elim (ne refl)
slot-value (⟪⟫⊑ _ _ bo-plain _ _ _ _ _ _) ne = ⊥-elim (ne refl)
slot-value (⟪⟫⊑ _ _ (bo-∀ s (fc-∷ _)) _ _ _ _ _ _) ne = V-⟪⟫ s I-all
slot-value (⊑⟪⟫ _ (push ca f _ _) _ _ _ _ _ d _ _) ne =
  slot-value d (fill-≢[] f (carried-≢[] ca ne))
