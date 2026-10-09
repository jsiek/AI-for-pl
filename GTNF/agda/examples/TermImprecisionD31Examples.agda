module examples.TermImprecisionD31Examples where

-- File Charter:
--   * REGRESSION EXAMPLES for design.md D31 (openings as slots of the
--     index, permissions chosen at joining boundaries), ported from the
--     checked prototype proof/DGG/notes/D28pD30.agda (§6f, §6g, §7,
--     §8b).  Every pair below was refuted under D27/D28 (the notes
--     ReductionAudit, TwoGen) or had no derivation, and is related here
--     with the real relation (TermImprecision).  No notes module is
--     imported: the programs, worlds and interiors of
--     proof/DGG/notes/ReductionAudit.agda and TwoGen.agda are copied.
--       P4k.init, pre, post,   P4k (ReductionAudit §1.1): the pair after
--       wrap, castfun          both TyBetas is related (the matched
--                              TyBeta boundary permits αᴿ, paying with
--                              X→ℕ ⊑ X→ℕ at X⊑X); the run goes on
--                              related through Wrap and CastFun
--       P4h.init, pre, post,   P4h (ReductionAudit §1.2): related after
--       r1-rejects             both TyBetas through R1′ (`ok-hidden`:
--                              the left's crossΛ hide has exterior type
--                              ℕ→ℕ); R1 alone would reject it
--       TwoGen.*-init,         TwoGen's seven pairs: G0, G2m, HRm,
--       TwoGen.*-final         N2 merged (one gen layer CONSUMES each
--                              opening, `co-gen`), G2, HR, N2 two-cast
--                              (the outer `+Y^β` creates the slots
--                              [skip, Y] and the inner `+X^α` FILLS the
--                              skip with X)
--       DGG1.*                 DGG part 1 for TwoGen's seven pairs, H1
--                              and K: the right's run, its value, a
--                              well-formed top-level world with no
--                              permission, and a derivation at O = []
--       P5.init, p5-mid, fin   P5 (design.md §C7): the left blames on an
--                              escaped tag, the right answers
--       R2c.r2c-pre, r2c-post, R2c (ForallBoundaryRisks §3): a left gen
--       r2c-final              value against the right's Inst boundary,
--                              before and after the right's inner Merge
--   * Every state that is not a source program is pinned to its
--     `evalTerms`/`eval` state by `refl`.  Typing side premises are read
--     off `tc` by TermImprecision's inversions.
--   * Orientation: the LEFT term is the more precise one.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Imprecision
open import ImprecisionWorld
open import ConversionImprecision
open import TermImprecision
open import proof.ImprecisionWorld
  using (namedᴸ-≤1; namedᴿ-≤1; ≤1-[]; ≤1-∷[]; wf+κ)
open import examples.TypeCheck using (tc; tf)
open import examples.Eval
  using (evalTerms; eval; Trace; stop; illtyped; _◅⟨_⟩_; value; blamed;
         no-redex; out-of-fuel; traceEnd; traceCtx)
open import Reduction using (_⊢_-→*_; done; _then_; runCtx)
import examples.TermImprecisionExamples as TIE
import examples.TermImprecisionRebaseExamples as Rbs
import examples.TermImprecisionPermissionExamples as PE
import examples.TermImprecisionH1Examples as H1
import examples.TermImprecisionRegressionExamples as RG

------------------------------------------------------------------------
-- Tools
------------------------------------------------------------------------

nth : List Term → ℕ → Term
nth []       _       = $ 0
nth (x ∷ xs) zero    = x
nth (x ∷ xs) (suc n) = nth xs n

-- a trace that ends in a value, as a run, and its value
EndsV : ∀ {Δ A M} → Trace Δ A M → Set
EndsV (stop (value _))   = ⊤
EndsV (stop (blamed _))  = ⊥
EndsV (stop no-redex)    = ⊥
EndsV (stop out-of-fuel) = ⊥
EndsV (illtyped _)       = ⊥
EndsV (_ ◅⟨ _ ⟩ tr)      = EndsV tr

runOf : ∀ {Δ A M} (tr : Trace Δ A M) → EndsV tr → Δ ⊢ M -→* traceEnd tr
runOf (stop (value v)) e = done
runOf (st ◅⟨ ⊢M′ ⟩ tr) e = st then runOf tr e

vEnd : ∀ {Δ A M} (tr : Trace Δ A M) → EndsV tr → Value (traceEnd tr)
vEnd (stop (value v)) e = v
vEnd (st ◅⟨ ⊢M′ ⟩ tr) e = vEnd tr e

ι : ∀ {μ} → μ ⊢ `ℕ ⊑ `ℕ
ι = ι⊑ι base-ℕ

------------------------------------------------------------------------
-- 1. P4k (ReductionAudit §1.1): P4 with the constant body.  The left
-- argument ΛY.λx:Y.5 against the right (λx:★.5 : ∀X.X→ℕ), whose gen
-- wrapper `X! → id(ℕ)` checks nothing.  Under D28 the pair after both
-- TyBetas was related in no world; under D31 the matched TyBeta
-- boundary `+X ∥ +X` permits αᴿ for its interior and pays with
-- X→ℕ ⊑ X→ℕ at X⊑X.
------------------------------------------------------------------------

module P4k where
  open TIE using (Θ₀; ΔL; ΔLᵢ; Wν; Wν-conv)
  open PE.P4 using (v₀; W₄; W₄²; W₄²¹; W₄²¹-wf; W₄ᴸ-wf; S; S⊑Sκ; tagˣ-ty;
                    p0)
  open Rbs using (Wc-bind²; Wc-bind²-conv; Wc-unbindᴿ; jr₀)

  ∀Xℕ : Ty
  ∀Xℕ = `∀ (` 0 ⇒ `ℕ)

  cK : Conv
  cK = reveal 0 (` 0 ⇒ `ℕ)

  -- the shared function  λf:∀X.X→ℕ. f [ℕ] 5
  F : Term
  F = ƛ ∀Xℕ ∙ ((ν `ℕ · ` 0 ⟨ cK ⟩) · $ 5)

  -- the left argument ΛY. λx:Y. 5; the right (λx:★. 5 : ∀X. X→ℕ)
  genK5 : Coercion
  genK5 = genᵖ (((` 0) !) ↦ᵖ idᵖ `ℕ)

  KL KR LK RK : Term
  KL = Λ (ƛ (` 0) ∙ $ 5)
  KR = (ƛ ★ ∙ $ 5) ⟨ [] ∣ genK5 ⟩
  LK = F · KL
  RK = F · KR

  LK-⊢ : empty ∣ [] ⊢ LK ⦂ `ℕ
  LK-⊢ = tc

  RK-⊢ : empty ∣ [] ⊢ RK ⦂ `ℕ
  RK-⊢ = tc

  q∀ : ∀ {μ} → μ ⊢ ∀Xℕ ⊑ ∀Xℕ
  q∀ = ∀⊑∀ (⇒⊑⇒ X⊑X ι)

  q★ : ∀ {μ} → μ ⊢ ∀Xℕ ⊑ ★ ⇒ `ℕ
  q★ = ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) ι)

  ℕ⇒ℕ : ∀ {μ} → μ ⊢ `ℕ ⇒ `ℕ ⊑ `ℕ ⇒ `ℕ
  ℕ⇒ℕ = ⇒⊑⇒ ι ι

  genK5-ty : CastTy empty [] genK5 (★ ⇒ `ℕ) ∀Xℕ
  genK5-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = empty} {M = KR})))

  νF-ty : NuTy empty `ℕ (` 0 ⇒ `ℕ) cK (`ℕ ⇒ `ℕ)
  νF-ty = proj₂ (proj₂ (ν-inv {Γ = ∀Xℕ ∷ []}
    (tc {Δ = empty} {Γ = ∀Xℕ ∷ []} {M = ν `ℕ · ` 0 ⟨ cK ⟩})))

  cK⊑cK : ∀ {Δ Δ′} {W : World Δ Δ′} → Joins W 0 0 → ConvImp W cK cK
  cK⊑cK j =
    conv-tail⊑tail
      (conv-mid⊑mid
        (conv-↦⊑↦ (conv-tail⊑tail (conv-seal⊑seal j))
                   (conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id ι)))))

  -- the left Λ against the right gen value: the Λ's binder is a fresh
  -- left-only type variable (X⊑★), facing the gen's source ★→ℕ
  KL⊑KR : ∅ʷ ∣ [] ⊢ KL ⊑ KR ∶ q∀
  KL⊑KR =
    ⊑cast
      (Λ⊑ b-fresh nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
        (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (κ⊑κ lit-$ ι)) q★)
      genK5-ty q∀

  -- the initial cast terms are related
  init : ∅ʷ ∣ [] ⊢ LK ⊑ RK ∶ ι
  init =
    ·⊑·
      (ƛ⊑ƛ {pA = q∀} tf tf
        (·⊑· (ν⊑ν (x⊑x Zʷ) ι νF-ty νF-ty (Wν , Wν-conv , cK⊑cK refl) ℕ⇒ℕ)
             (κ⊑κ lit-$ ι)))
      KL⊑KR

  -- state 1 on both sides (after both Betas): the ν pair
  L₁ R₁ : Term
  L₁ = (ν `ℕ · KL ⟨ cK ⟩) · $ 5
  R₁ = (ν `ℕ · KR ⟨ cK ⟩) · $ 5

  L₁-state : nth (evalTerms 10 LK-⊢) 1 ≡ L₁
  L₁-state = refl

  R₁-state : nth (evalTerms 20 RK-⊢) 1 ≡ R₁
  R₁-state = refl

  νL-ty : NuTy empty `ℕ (` 0 ⇒ `ℕ) cK (`ℕ ⇒ `ℕ)
  νL-ty = proj₂ (proj₂ (ν-inv {Γ = []}
    (tc {Δ = empty} {M = ν `ℕ · KL ⟨ cK ⟩})))

  νR-ty : NuTy empty `ℕ (` 0 ⇒ `ℕ) cK (`ℕ ⇒ `ℕ)
  νR-ty = proj₂ (proj₂ (ν-inv {Γ = []}
    (tc {Δ = empty} {M = ν `ℕ · KR ⟨ cK ⟩})))

  -- the ν pair is related: ν⊑ν over KL ⊑ KR
  pre : ∅ʷ ∣ [] ⊢ L₁ ⊑ R₁ ∶ ι
  pre =
    ·⊑· (ν⊑ν KL⊑KR ι νL-ty νR-ty (Wν , Wν-conv , cK⊑cK refl) ℕ⇒ℕ)
        (κ⊑κ lit-$ ι)

  -- state 2 on both sides (after both TyBetas, α:=ℕ on each)
  pF : Coercion
  pF = ((` 0) !) ↦ᵖ idᵖ `ℕ

  cUF : Conv
  cUF = tail (mid (tail (mid (id ★)) ↦ tail (mid (id `ℕ))))

  UF IF LB RB L₂ R₂ : Term
  UF = (ƛ ★ ∙ $ 5) ⟪ unbind 0 0 ∷ [] , cUF ⟫
  IF = UF ⟨ ★∼X ∷ [] ∣ pF ⟩
  LB = (ƛ (` 0) ∙ $ 5) ⟪ Θ₀ , cK ⟫
  RB = IF ⟪ Θ₀ , cK ⟫
  L₂ = LB · $ 5
  R₂ = RB · $ 5

  L₂-state : nth (evalTerms 10 LK-⊢) 2 ≡ L₂
  L₂-state = refl

  R₂-state : nth (evalTerms 20 RK-⊢) 2 ≡ R₂
  R₂-state = refl

  bLB : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ `ℕ) cK (`ℕ ⇒ `ℕ)
  bLB = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = LB}))))

  bRB : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ `ℕ) cK (`ℕ ⇒ `ℕ)
  bRB = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = RB}))))

  pF-ty : CastTy ΔLᵢ (★∼X ∷ []) pF (★ ⇒ `ℕ) (` 0 ⇒ `ℕ)
  pF-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = IF})))

  bUF : BdyTy ΔLᵢ (unbind 0 0 ∷ []) ΔL (★ ⇒ `ℕ) cUF (★ ⇒ `ℕ)
  bUF = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = UF}))))

  -- inside the matched +X, αᴿ permitted: the left's λx:X. 5 against the
  -- right's −X (X left-only), and against the gen wrapper, peeled by a
  -- plain ⊑cast at X→ℕ ⊑ ★→ℕ
  body : W₄²¹ ∣ [] ⊢ ƛ (` 0) ∙ $ 5 ⊑ UF ∶ ⇒⊑⇒ (X⊑★ here) ι
  body =
    ⊑⟪⟫₀ (Wc-unbindᴿ v₀) W₄ᴸ-wf
      (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (κ⊑κ lit-$ ι)) bUF (⇒⊑⇒ (X⊑★ here) ι)

  fun : W₄²¹ ∣ [] ⊢ ƛ (` 0) ∙ $ 5 ⊑ IF ∶ ⇒⊑⇒ X⊑X ι
  fun = ⊑cast {A = ` 0 ⇒ `ℕ} body pF-ty (⇒⊑⇒ X⊑X ι)

  -- THE TyBeta PAIR IS RELATED: the matched +X permits αᴿ (K = [0]),
  -- paying with X→ℕ ⊑ X→ℕ at X⊑X
  post : W₄ ∣ [] ⊢ L₂ ⊑ R₂ ∶ ι
  post =
    ·⊑·
      (⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) (jr₀ ∷ []) W₄²¹-wf (⇒⊑⇒ X⊑X ι) fun
        bLB bRB (W₄² , Wc-bind²-conv v₀ here⇔ , cK⊑cK refl) ℕ⇒ℕ)
      (κ⊑κ lit-$ ι)

  -- the run goes on: the left's Wrap against the right's Wrap (states
  -- 3, 3) and the right's CastFun (states 3, 4; D28's R12 site).  The
  -- Wrap duals are the matched seals `[−X^α] 5 ⟨−X⟩`
  L₃ R₃ R₄ : Term
  L₃ = ((ƛ (` 0) ∙ $ 5) · S) ⟪ Θ₀ , ⌞ id `ℕ ⌟ ⟫
  R₃ = (IF · S) ⟪ Θ₀ , ⌞ id `ℕ ⌟ ⟫
  R₄ = ((UF · (S ⟨ X∼★ ∷ [] ∣ (` 0) ! ⟩)) ⟨ ★∼X ∷ [] ∣ idᵖ `ℕ ⟩)
         ⟪ Θ₀ , ⌞ id `ℕ ⌟ ⟫

  L₃-state : nth (evalTerms 10 LK-⊢) 3 ≡ L₃
  L₃-state = refl

  R₃-state : nth (evalTerms 20 RK-⊢) 3 ≡ R₃
  R₃-state = refl

  R₄-state : nth (evalTerms 20 RK-⊢) 4 ≡ R₄
  R₄-state = refl

  bL₃ : BdyTy ΔL Θ₀ ΔLᵢ `ℕ ⌞ id `ℕ ⌟ `ℕ
  bL₃ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = L₃}))))

  bR₃ : BdyTy ΔL Θ₀ ΔLᵢ `ℕ ⌞ id `ℕ ⌟ `ℕ
  bR₃ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = R₃}))))

  bR₄ : BdyTy ΔL Θ₀ ΔLᵢ `ℕ ⌞ id `ℕ ⌟ `ℕ
  bR₄ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = R₄}))))

  idℕ-ty : CastTy ΔLᵢ (★∼X ∷ []) (idᵖ `ℕ) `ℕ `ℕ
  idℕ-ty = cast-ty (⊢id atom-ℕ wf-ℕ) refl

  idℕ⊑ : ConvImp W₄² ⌞ id `ℕ ⌟ ⌞ id `ℕ ⌟
  idℕ⊑ = conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id ι))

  S⊑S : W₄²¹ ∣ [] ⊢ S ⊑ S ∶ X⊑X
  S⊑S = S⊑Sκ p0

  -- Wrap against Wrap: the matched seals inside the permitting boundary
  wrap : W₄ ∣ [] ⊢ L₃ ⊑ R₃ ∶ ι
  wrap =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) (jr₀ ∷ []) W₄²¹-wf ι (·⊑· {pA = X⊑X} fun S⊑S)
      bL₃ bR₃ (W₄² , Wc-bind²-conv v₀ here⇔ , idℕ⊑) ι

  -- Wrap against CastFun: the right's X! on its dual is peeled at X ⊑ ★
  -- under the boundary's permission
  castfun : W₄ ∣ [] ⊢ L₃ ⊑ R₄ ∶ ι
  castfun =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) (jr₀ ∷ []) W₄²¹-wf ι
      (⊑cast (·⊑· {pA = X⊑★ here} body (⊑cast S⊑S tagˣ-ty (X⊑★ here)))
        idℕ-ty ι)
      bL₃ bR₄ (W₄² , Wc-bind²-conv v₀ here⇔ , idℕ⊑) ι

------------------------------------------------------------------------
-- 2. P4h (ReductionAudit §1.2): P4 whose left Λ captures a free term
-- variable, so the left's Beta puts it under the Λ's crossΛ hide
-- [−Y^β] (λy:ℕ. y) ⟨id(ℕ) → id(ℕ)⟩.  After both TyBetas the matched
-- TyBeta boundary permits αᴿ; the hide, inside the right's −X, is a
-- one-sided ⟪⟫⊑ whose exterior type ℕ→ℕ does not mention α, so R1′
-- admits it (`ok-hidden`) although α is paired with the permitted αᴿ.
------------------------------------------------------------------------

module P4h where
  open TIE using (Θ₀; ΔL; ΔLᵢ; Wν; Wν-conv; revX; revX⊑revX; ∀X⇒X)
  open PE.P4 using (v₀; W₄; W₄²; W₄²¹; W₄²¹-wf; W₄ᴸ-wf; W₄⁰; W₄⁰-wf; p0;
                    bdy-wf; Ξ₄; ϱ₄)
  open Rbs using (Wc-bind²; Wc-bind²-conv; Wc-unbindᴿ; Wcᴸ; c⊑c²; c⊑★²;
                  jr₀)

  -- P4's function  λh:∀X.X→X. h [ℕ] 5
  F4 : Term
  F4 = ƛ ∀X⇒X ∙ ((ν `ℕ · ` 0 ⟨ revX ⟩) · $ 5)

  -- the body  (λy:ℕ. x) (f 1)  under x (0) and f (1)
  bodyH : Term
  bodyH = (ƛ `ℕ ∙ ` 1) · (` 1 · $ 1)

  genI : Coercion
  genI = genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ 0))

  -- left argument  (λf:ℕ→ℕ. ΛX. λx:X. (λy:ℕ. x) (f 1)) (λz:ℕ. z)
  -- right argument (λf:ℕ→ℕ. (λx:★. (λy:ℕ. x) (f 1) : ∀X. X→X)) (λz:ℕ. z)
  HL HR LH RH : Term
  HL = (ƛ (`ℕ ⇒ `ℕ) ∙ Λ (ƛ (` 0) ∙ bodyH)) · (ƛ `ℕ ∙ ` 0)
  HR = (ƛ (`ℕ ⇒ `ℕ) ∙ ((ƛ ★ ∙ bodyH) ⟨ [] ∣ genI ⟩)) · (ƛ `ℕ ∙ ` 0)
  LH = F4 · HL
  RH = F4 · HR

  LH-⊢ : empty ∣ [] ⊢ LH ⦂ `ℕ
  LH-⊢ = tc

  RH-⊢ : empty ∣ [] ⊢ RH ⦂ `ℕ
  RH-⊢ = tc

  q∀ : ∀ {μ} → μ ⊢ ∀X⇒X ⊑ ∀X⇒X
  q∀ = ∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)

  q★ : ∀ {μ} → μ ⊢ ∀X⇒X ⊑ ★ ⇒ ★
  q★ = ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) (X⊑★ here))

  idℕ⇒ℕ id★⇒★ : Conv
  idℕ⇒ℕ = tail (mid (tail (mid (id `ℕ)) ↦ tail (mid (id `ℕ))))
  id★⇒★ = tail (mid (tail (mid (id ★)) ↦ tail (mid (id ★))))

  -- the left's Λ after the argument's Beta: f became the crossΛ hide
  idℕ H₀ bodyL bodyR HLv HRv : Term
  idℕ   = ƛ `ℕ ∙ ` 0
  H₀    = idℕ ⟪ unbind 0 0 ∷ [] , idℕ⇒ℕ ⟫
  bodyL = (ƛ `ℕ ∙ ` 1) · (H₀ · $ 1)
  bodyR = (ƛ `ℕ ∙ ` 1) · (idℕ · $ 1)
  HLv   = Λ (ƛ (` 0) ∙ bodyL)
  HRv   = (ƛ ★ ∙ bodyR) ⟨ [] ∣ genI ⟩

  genI-ty : CastTy empty [] genI (★ ⇒ ★) ∀X⇒X
  genI-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = empty} {M = HRv})))

  -- the initial cast terms are related (the arguments by Λ⊑ under λf,
  -- the functions by reflexivity)
  νb-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  νb-ty = proj₂ (proj₂ (ν-inv {Γ = ∀X⇒X ∷ []}
    (tc {Δ = empty} {Γ = ∀X⇒X ∷ []} {M = ν `ℕ · ` 0 ⟨ revX ⟩})))

  bodyf : ∅ʷ ∣ ctx-imp (`ℕ ⇒ `ℕ) (`ℕ ⇒ `ℕ) (⇒⊑⇒ ι ι) ∷ []
    ⊢ Λ (ƛ (` 0) ∙ bodyH) ⊑ (ƛ ★ ∙ bodyH) ⟨ [] ∣ genI ⟩ ∶ q∀
  bodyf =
    ⊑cast
      (Λ⊑ b-fresh nv-⇒ (∈-⇒ˡ ∈-var) (liftᴸ-∷ {p′ = ⇒⊑⇒ ι ι} liftᴸ-[])
        (V-simple S-ƛ)
        (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★
          (·⊑· {pA = ι}
            (ƛ⊑ƛ {pA = ι} {pB = X⊑★ here} tf tf (x⊑x (Sʷ Zʷ)))
            (·⊑· {pA = ι} (x⊑x (Sʷ Zʷ)) (κ⊑κ lit-$ ι))))
        q★)
      genI-ty q∀

  init : ∅ʷ ∣ [] ⊢ LH ⊑ RH ∶ ι
  init =
    ·⊑·
      (ƛ⊑ƛ {pA = q∀} tf tf
        (·⊑· (ν⊑ν (x⊑x Zʷ) ι νb-ty νb-ty (Wν , Wν-conv , revX⊑revX refl)
                (⇒⊑⇒ ι ι))
             (κ⊑κ lit-$ ι)))
      (·⊑· (ƛ⊑ƛ {pA = ⇒⊑⇒ ι ι} tf tf bodyf)
           (ƛ⊑ƛ {pA = ι} {pB = ι} tf tf (x⊑x Zʷ)))

  -- state 2 on both sides: the ν redexes
  L₂ R₂ : Term
  L₂ = (ν `ℕ · HLv ⟨ revX ⟩) · $ 5
  R₂ = (ν `ℕ · HRv ⟨ revX ⟩) · $ 5

  L₂-state : nth (evalTerms 20 LH-⊢) 2 ≡ L₂
  L₂-state = refl

  R₂-state : nth (evalTerms 30 RH-⊢) 2 ≡ R₂
  R₂-state = refl

  νL-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  νL-ty = proj₂ (proj₂ (ν-inv {Γ = []}
    (tc {Δ = empty} {M = ν `ℕ · HLv ⟨ revX ⟩})))

  νR-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  νR-ty = proj₂ (proj₂ (ν-inv {Γ = []}
    (tc {Δ = empty} {M = ν `ℕ · HRv ⟨ revX ⟩})))

  -- the left's hide under the left-only Λ binder (no pair)
  ΔΛ ΔΛᵢ : Ctxᵗ
  ΔΛ  = underΛ empty
  ΔΛᵢ = (abstR ∷ []) ∣ []

  WΛ : World ΔΛ empty
  WΛ = ∅ʷ ⊕ᴸ

  WΛᵢ : World ΔΛᵢ empty
  WΛᵢ = world 0 []↪ []↪ [] [] []

  bH₀ : BdyTy ΔΛ (unbind 0 0 ∷ []) ΔΛᵢ (`ℕ ⇒ `ℕ) idℕ⇒ℕ (`ℕ ⇒ `ℕ)
  bH₀ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔΛ} {M = H₀}))))

  intH₀ : Interior WΛ (unbind 0 0 ∷ []) [] WΛᵢ
  intH₀ = record
    { int-left   = bw-interior (proj₂ (bdy-wf bH₀))
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  wf-WΛᵢ : WfWorld WΛᵢ
  wf-WΛᵢ = wf-world joint[] (λ { (inj₁ ()) ; (inj₂ ()) })
    (λ { _ _ _ (inj₁ ()) _ ; _ _ _ (inj₂ ()) _ })
    (λ { _ _ _ (inj₁ ()) _ ; _ _ _ (inj₂ ()) _ }) []

  -- the hide against the right's λz:ℕ. z, one-sided: R1 holds, the Λ's
  -- rep. var has no partner
  H₀⊑ : ∀ {γ} → WΛ ∣ γ ⊢ H₀ ⊑ idℕ ∶ ⇒⊑⇒ ι ι
  H₀⊑ = ⟪⟫⊑₀ intH₀ (ok-unbind (λ { (inj₁ ()) ; (inj₂ ()) }) ∷ []) wf-WΛᵢ
    (ƛ⊑ƛ {pA = ι} {pB = ι} tf tf (x⊑x Zʷ)) bH₀ (⇒⊑⇒ ι ι)

  bodyΛ⊑ : WΛ ∣ [] ⊢ ƛ (` 0) ∙ bodyL ⊑ ƛ ★ ∙ bodyR
    ∶ ⇒⊑⇒ (X⊑★ here) (X⊑★ here)
  bodyΛ⊑ =
    ƛ⊑ƛ {pA = X⊑★ here} tf wf-★
      (·⊑· {pA = ι}
        (ƛ⊑ƛ {pA = ι} {pB = X⊑★ here} tf tf (x⊑x (Sʷ Zʷ)))
        (·⊑· {pA = ι} H₀⊑ (κ⊑κ lit-$ ι)))

  HLv⊑HRv : ∅ʷ ∣ [] ⊢ HLv ⊑ HRv ∶ q∀
  HLv⊑HRv =
    ⊑cast (Λ⊑ b-fresh nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ) bodyΛ⊑ q★)
      genI-ty q∀

  -- the ν pair is related
  pre : ∅ʷ ∣ [] ⊢ L₂ ⊑ R₂ ∶ ι
  pre =
    ·⊑· (ν⊑ν HLv⊑HRv ι νL-ty νR-ty (Wν , Wν-conv , revX⊑revX refl)
           (⇒⊑⇒ ι ι))
        (κ⊑κ lit-$ ι)

  -- state 3 on both sides: after both TyBetas
  pI : Coercion
  pI = ((` 0) !) ↦ᵖ ((` 0) ？ 0)

  UF IF LB RB L₃ R₃ : Term
  UF = (ƛ ★ ∙ bodyR) ⟪ unbind 0 0 ∷ [] , id★⇒★ ⟫
  IF = UF ⟨ ★∼X ∷ [] ∣ pI ⟩
  LB = (ƛ (` 0) ∙ bodyL) ⟪ Θ₀ , revX ⟫
  RB = IF ⟪ Θ₀ , revX ⟫
  L₃ = LB · $ 5
  R₃ = RB · $ 5

  L₃-state : nth (evalTerms 20 LH-⊢) 3 ≡ L₃
  L₃-state = refl

  R₃-state : nth (evalTerms 30 RH-⊢) 3 ≡ R₃
  R₃-state = refl

  bLB : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  bLB = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = LB}))))

  bRB : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  bRB = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = RB}))))

  pI-ty : CastTy ΔLᵢ (★∼X ∷ []) pI (★ ⇒ ★) (` 0 ⇒ ` 0)
  pI-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = IF})))

  bUF : BdyTy ΔLᵢ (unbind 0 0 ∷ []) ΔL (★ ⇒ ★) id★⇒★ (★ ⇒ ★)
  bUF = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = UF}))))

  bH : BdyTy ΔLᵢ (unbind 0 0 ∷ []) ΔL (`ℕ ⇒ `ℕ) idℕ⇒ℕ (`ℕ ⇒ `ℕ)
  bH = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = H₀}))))

  -- the left's crossΛ hide alone, inside the right's −X: the left X
  -- goes away
  intH : Interior (Wcᴸ {Ξ₄} {ϱ₄} (0 ∷ [])) (unbind 0 0 ∷ []) []
    (W₄⁰ (0 ∷ []))
  intH = record
    { int-left   = bw-interior (proj₂ (bdy-wf bH))
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  -- R1′: the hide's exterior type ℕ→ℕ mentions no type variable
  H⊑ : ∀ {γ} → Wcᴸ {Ξ₄} {ϱ₄} (0 ∷ []) ∣ γ ⊢ H₀ ⊑ idℕ ∶ ⇒⊑⇒ ι ι
  H⊑ = ⟪⟫⊑₀ intH (ok-hidden (λ _ → refl) ∷ []) (W₄⁰-wf p0)
    (ƛ⊑ƛ {pA = ι} {pB = ι} tf tf (x⊑x Zʷ)) bH (⇒⊑⇒ ι ι)

  -- R1 alone (`ok-unbind`) fails at this very step: αᴸ = 0 has the
  -- permitted partner αᴿ = 0
  r1-rejects : ¬ Unpermitted (Wcᴸ {Ξ₄} {ϱ₄} (0 ∷ [])) 0
  r1-rejects u with u (inj₁ here⇔)
  ... | ()

  body⊑ : Wcᴸ {Ξ₄} {ϱ₄} (0 ∷ []) ∣ []
    ⊢ ƛ (` 0) ∙ bodyL ⊑ ƛ ★ ∙ bodyR ∶ ⇒⊑⇒ (X⊑★ here) (X⊑★ here)
  body⊑ =
    ƛ⊑ƛ {pA = X⊑★ here} tf wf-★
      (·⊑· {pA = ι}
        (ƛ⊑ƛ {pA = ι} {pB = X⊑★ here} tf tf (x⊑x (Sʷ Zʷ)))
        (·⊑· {pA = ι} H⊑ (κ⊑κ lit-$ ι)))

  -- THE TyBeta PAIR IS RELATED (R1′ and the boundary's permission)
  post : W₄ ∣ [] ⊢ L₃ ⊑ R₃ ∶ ι
  post =
    ·⊑·
      (⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) (jr₀ ∷ []) W₄²¹-wf (c⊑c² Ξ₄ ϱ₄ [] 0)
        (⊑cast {A = ` 0 ⇒ ` 0}
          (⊑⟪⟫₀ (Wc-unbindᴿ v₀) W₄ᴸ-wf body⊑ bUF
            (c⊑★² Ξ₄ ϱ₄ (0 ∷ []) 0 refl))
          pI-ty (c⊑c² Ξ₄ ϱ₄ (0 ∷ []) 0))
        bLB bRB (W₄² , Wc-bind²-conv v₀ here⇔ , revX⊑revX refl)
        (⇒⊑⇒ ι ι))
      (κ⊑κ lit-$ ι)

------------------------------------------------------------------------
-- 3. TwoGen's seven pairs (proof/DGG/notes/TwoGen.md §1).  A left
-- ∀-value built by a gen cast against a right that instantiates it at
-- ★, from related sources.  A left gen layer CONSUMES its opening in
-- cast⊑ (no world change), after the right's cast over the
-- instantiated gen body has been peeled by ⊑cast at the OPENED type
-- variable, which the ⊑⟪⟫ that opened it permits (paying with the
-- opened interior index at X⊑X).  G2, HR, N2.TwoCast use the skip slot:
-- the outer `+Y^β` creates [skip, Y] and the inner `+X^α` FILLS it.
------------------------------------------------------------------------

module TwoGen where
  open import examples.CambridgeExamples using (K★; genK; instK)
  open import examples.Examples using (ℓ)
  open H1 using (K2; KY; instX∀; instY; ci; cf; cX; cY; ΘX; ΘY; ΔT2; ΔXY;
                 ΔY; q-top; q-src1; instX∀-ty; instY-ty₀; cf-ty; ci-ty; bX;
                 bY)
  open TIE using (W₃; int-ro₃; ok₃; ΔR; ΔRᵢ)
  open Rbs using (IntN; W₃-wf; push₀; ne₀; jo₀; wf¹; p0; p10)

  ----------------------------------------------------------------------
  -- the programs

  -- two gen layers:  (λx:★.λy:★.x : ∀X.∀Y.X→Y→X)
  GL GR GRm : Term
  GL  = K★ ⟨ [] ∣ genK ⟩
  GR  = (GL ⟨ [] ∣ instX∀ ⟩) ⟨ [] ∣ instY ⟩
  GRm = GL ⟨ [] ∣ instK ⟩

  GL-⊢ : empty ∣ [] ⊢ GL ⦂ K2
  GL-⊢ = tc

  GR-⊢ : empty ∣ [] ⊢ GR ⦂ ★ ⇒ (★ ⇒ ★)
  GR-⊢ = tc

  GRm-⊢ : empty ∣ [] ⊢ GRm ⦂ ★ ⇒ (★ ⇒ ★)
  GRm-⊢ = tc

  -- gen over Λ: (ΛX.λx:X.λy:★.x : ∀X.∀Y.X→Y→X)
  NΛ KΛ : Term
  NΛ = ƛ (` 0) ∙ (ƛ ★ ∙ ` 1)
  KΛ = Λ NΛ

  pH ∀gen : Coercion
  pH   = idᵖ (` 1) ↦ᵖ (((` 0) !) ↦ᵖ idᵖ (` 1))
  ∀gen = ∀ᵖ (genᵖ pH)

  HL HR HRm : Term
  HL  = KΛ ⟨ [] ∣ ∀gen ⟩
  HR  = (HL ⟨ [] ∣ instX∀ ⟩) ⟨ [] ∣ instY ⟩
  HRm = HL ⟨ [] ∣ instK ⟩

  HL-⊢ : empty ∣ [] ⊢ HL ⦂ K2
  HL-⊢ = tc

  HR-⊢ : empty ∣ [] ⊢ HR ⦂ ★ ⇒ (★ ⇒ ★)
  HR-⊢ = tc

  HRm-⊢ : empty ∣ [] ⊢ HRm ⦂ ★ ⇒ (★ ⇒ ★)
  HRm-⊢ = tc

  -- one gen, no covariant check of its type variable:
  -- (λx:★. 5 : ∀X. X→ℕ)
  I5 : Term
  I5 = ƛ ★ ∙ $ 5

  genX5 instX5 : Coercion
  genX5  = genᵖ (((` 0) !) ↦ᵖ idᵖ `ℕ)
  instX5 = instᵖ (((` 0) ？ 0) ↦ᵖ idᵖ `ℕ)

  FL FR : Term
  FL = I5 ⟨ [] ∣ genX5 ⟩
  FR = FL ⟨ [] ∣ instX5 ⟩

  FL-⊢ : empty ∣ [] ⊢ FL ⦂ `∀ (` 0 ⇒ `ℕ)
  FL-⊢ = tc

  FR-⊢ : empty ∣ [] ⊢ FR ⦂ ★ ⇒ `ℕ
  FR-⊢ = tc

  -- nested gens: ((λx:★.λy:★.x : ∀Y.★→Y→★) : ∀X.∀Y.X→Y→X)
  genY genX∀ : Coercion
  genY  = genᵖ (idᵖ ★ ↦ᵖ (((` 0) !) ↦ᵖ idᵖ ★))
  genX∀ = genᵖ (∀ᵖ (((` 1) !) ↦ᵖ (idᵖ (` 0) ↦ᵖ ((` 1) ？ 0))))

  NL NR NRm : Term
  NL  = (K★ ⟨ [] ∣ genY ⟩) ⟨ [] ∣ genX∀ ⟩
  NR  = (NL ⟨ [] ∣ instX∀ ⟩) ⟨ [] ∣ instY ⟩
  NRm = NL ⟨ [] ∣ instK ⟩

  NL-⊢ : empty ∣ [] ⊢ NL ⦂ K2
  NL-⊢ = tc

  NR-⊢ : empty ∣ [] ⊢ NR ⦂ ★ ⇒ (★ ⇒ ★)
  NR-⊢ = tc

  NRm-⊢ : empty ∣ [] ⊢ NRm ⦂ ★ ⇒ (★ ⇒ ★)
  NRm-⊢ = tc

  ----------------------------------------------------------------------
  -- the right's final values

  -- G0
  pF : Coercion
  pF = ((` 0) !) ↦ᵖ idᵖ `ℕ

  cU0 cB0 : Conv
  cU0 = tail (mid (tail (mid (id ★)) ↦ tail (mid (id `ℕ))))
  cB0 = tail (mid (tail (seal 0) ↦ tail (mid (id `ℕ))))

  UF IF BF FR₁ FR₂ : Term
  UF  = I5 ⟪ unbind 0 0 ∷ [] , cU0 ⟫
  IF  = UF ⟨ ★∼X ∷ [] ∣ pF ⟩
  BF  = IF ⟪ bind 0 0 ∷ [] , cB0 ⟫
  FR₁ = (ν ★ · FL ⟨ cB0 ⟩) ⟨ [] ∣ idᵖ ★ ↦ᵖ idᵖ `ℕ ⟩
  FR₂ = BF ⟨ [] ∣ idᵖ ★ ↦ᵖ idᵖ `ℕ ⟩

  FR-states : evalTerms 20 FR-⊢ ≡ FR ∷ FR₁ ∷ FR₂ ∷ []
  FR-states = refl

  -- the gen bodies after the right's two TyBetas
  cU cXY cUH : Conv
  cU  = tail (mid (tail (mid (id ★))
          ↦ tail (mid (tail (mid (id ★)) ↦ tail (mid (id ★))))))
  cXY = tail (mid (tail (seal 1) ↦ tail (mid (tail (seal 0) ↦ unseal 1))))
  cUH = tail (mid (tail (mid (id (` 1)))
          ↦ tail (mid (tail (mid (id ★)) ↦ tail (mid (id (` 1)))))))

  pK : Coercion
  pK = ((` 1) !) ↦ᵖ (((` 0) !) ↦ᵖ ((` 1) ？ ℓ))

  U2 ΘXY : Boundary
  U2  = unbind 0 1 ∷ unbind 0 0 ∷ []
  ΘXY = bind 1 1 ∷ bind 0 0 ∷ []

  UK CK UH CH : Term
  UK = K★ ⟪ U2 , cU ⟫
  CK = UK ⟨ ★∼X ∷ ★∼X ∷ [] ∣ pK ⟩
  UH = NΛ ⟪ unbind 0 0 ∷ [] , cUH ⟫
  CH = UH ⟨ ★∼X ∷ X∼X ∷ [] ∣ pH ⟩

  -- G2m, G2, HRm, HR
  GmF GF HmF HF : Term
  GmF = (CK ⟪ ΘXY , cXY ⟫) ⟨ [] ∣ cf ⟩
  GF  = ((((CK ⟪ ΘX , cX ⟫) ⟨ X∼X ∷ [] ∣ ci ⟩) ⟪ ΘY , cY ⟫)) ⟨ [] ∣ cf ⟩
  HmF = (CH ⟪ ΘXY , cXY ⟫) ⟨ [] ∣ cf ⟩
  HF  = ((((CH ⟪ ΘX , cX ⟫) ⟨ X∼X ∷ [] ∣ ci ⟩) ⟪ ΘY , cY ⟫)) ⟨ [] ∣ cf ⟩

  GmF-end : traceEnd (eval 40 GRm GRm-⊢) ≡ GmF
  GmF-end = refl

  GmF-ctx : traceCtx (eval 40 GRm GRm-⊢) ≡ ΔT2
  GmF-ctx = refl

  GF-end : traceEnd (eval 40 GR GR-⊢) ≡ GF
  GF-end = refl

  HmF-end : traceEnd (eval 40 HRm HRm-⊢) ≡ HmF
  HmF-end = refl

  HF-end : traceEnd (eval 40 HR HR-⊢) ≡ HF
  HF-end = refl

  -- N2
  pY pX : Coercion
  pY = idᵖ ★ ↦ᵖ (((` 0) !) ↦ᵖ idᵖ ★)
  pX = ((` 1) !) ↦ᵖ (idᵖ (` 0) ↦ᵖ ((` 1) ？ 0))

  cUX : Conv
  cUX = tail (mid (tail (mid (id ★))
          ↦ tail (mid (tail (mid (id (` 0))) ↦ tail (mid (id ★))))))

  NL₁ NUY NCY NUX NCX NF NmF : Term
  NL₁ = K★ ⟨ [] ∣ genY ⟩
  NUY = K★ ⟪ unbind 0 0 ∷ [] , cU ⟫
  NCY = NUY ⟨ ★∼X ∷ [] ∣ pY ⟩
  NUX = NCY ⟪ unbind 1 1 ∷ [] , cUX ⟫
  NCX = NUX ⟨ X∼X ∷ ★∼X ∷ [] ∣ pX ⟩
  NF  = (((NCX ⟪ ΘX , cX ⟫) ⟨ X∼X ∷ [] ∣ ci ⟩) ⟪ ΘY , cY ⟫) ⟨ [] ∣ cf ⟩
  NmF = (NCX ⟪ ΘXY , cXY ⟫) ⟨ [] ∣ cf ⟩

  NF-end : traceEnd (eval 40 NR NR-⊢) ≡ NF
  NF-end = refl

  NmF-end : traceEnd (eval 40 NRm NRm-⊢) ≡ NmF
  NmF-end = refl

  ----------------------------------------------------------------------
  -- values and typing side premises

  vK★ : Value K★
  vK★ = V-simple S-ƛ

  vNΛ : Value NΛ
  vNΛ = V-simple S-ƛ

  vKΛ : Value KΛ
  vKΛ = V-simple (S-Λ vNΛ)

  vGL : Value GL
  vGL = V-simple (S-cast vK★ I-gen)

  vHL : Value HL
  vHL = V-simple (S-cast vKΛ I-∀ᵖ)

  vFL : Value FL
  vFL = V-simple (S-cast (V-simple S-ƛ) I-gen)

  vNL₁ : Value NL₁
  vNL₁ = V-simple (S-cast vK★ I-gen)

  vNL : Value NL
  vNL = V-simple (S-cast vNL₁ I-gen)

  gcvGL : GenCastValue GL
  gcvGL = gcv vK★ gl-gen

  gcvHL : GenCastValue HL
  gcvHL = gcv vKΛ (gl-∀ gl-gen)

  gcvNL : GenCastValue NL
  gcvNL = gcv vNL₁ gl-gen

  genK-ty : CastTy empty [] genK (★ ⇒ (★ ⇒ ★)) K2
  genK-ty = proj₂ (proj₂ (cast-inv {Γ = []} GL-⊢))

  ∀gen-ty : CastTy empty [] ∀gen (`∀ (` 0 ⇒ (★ ⇒ ` 0))) K2
  ∀gen-ty = proj₂ (proj₂ (cast-inv {Γ = []} HL-⊢))

  instK-ty : CastTy empty [] instK K2 (★ ⇒ (★ ⇒ ★))
  instK-ty = proj₂ (proj₂ (cast-inv {Γ = []} GRm-⊢))

  genX5-ty : CastTy empty [] genX5 (★ ⇒ `ℕ) (`∀ (` 0 ⇒ `ℕ))
  genX5-ty = proj₂ (proj₂ (cast-inv {Γ = []} FL-⊢))

  instX5-ty : CastTy empty [] instX5 (`∀ (` 0 ⇒ `ℕ)) (★ ⇒ `ℕ)
  instX5-ty = proj₂ (proj₂ (cast-inv {Γ = []} FR-⊢))

  genY-ty : CastTy empty [] genY (★ ⇒ (★ ⇒ ★)) KY
  genY-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = empty} {M = NL₁})))

  genX∀-ty : CastTy empty [] genX∀ KY K2
  genX∀-ty = proj₂ (proj₂ (cast-inv {Γ = []} NL-⊢))

  pF-ty : CastTy ΔRᵢ (★∼X ∷ []) pF (★ ⇒ `ℕ) (` 0 ⇒ `ℕ)
  pF-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = IF})))

  UF-ty : BdyTy ΔRᵢ (unbind 0 0 ∷ []) ΔR (★ ⇒ `ℕ) cU0 (★ ⇒ `ℕ)
  UF-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = UF}))))

  BF-ty : BdyTy ΔR (bind 0 0 ∷ []) ΔRᵢ (` 0 ⇒ `ℕ) cB0 (★ ⇒ `ℕ)
  BF-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = BF}))))

  cF-ty : CastTy ΔR [] (idᵖ ★ ↦ᵖ idᵖ `ℕ) (★ ⇒ `ℕ) (★ ⇒ `ℕ)
  cF-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔR} {M = FR₂})))

  pK-ty : CastTy ΔXY (★∼X ∷ ★∼X ∷ []) pK (★ ⇒ (★ ⇒ ★)) (` 1 ⇒ (` 0 ⇒ ` 1))
  pK-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔXY} {M = CK})))

  UK-ty : BdyTy ΔXY U2 ΔT2 (★ ⇒ (★ ⇒ ★)) cU (★ ⇒ (★ ⇒ ★))
  UK-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔXY} {M = UK}))))

  BXY-ty : BdyTy ΔT2 ΘXY ΔXY (` 1 ⇒ (` 0 ⇒ ` 1)) cXY (★ ⇒ (★ ⇒ ★))
  BXY-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔT2} {M = CK ⟪ ΘXY , cXY ⟫}))))

  pH-ty : CastTy ΔXY (★∼X ∷ X∼X ∷ []) pH (` 1 ⇒ (★ ⇒ ` 1))
    (` 1 ⇒ (` 0 ⇒ ` 1))
  pH-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔXY} {M = CH})))

  ΔX1 : Ctxᵗ
  ΔX1 = (bindR ★ ∷ bindR ★ ∷ []) ∣ (1 ∷ [])

  UH-ty : BdyTy ΔXY (unbind 0 0 ∷ []) ΔX1 (` 0 ⇒ (★ ⇒ ` 0)) cUH
    (` 1 ⇒ (★ ⇒ ` 1))
  UH-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔXY} {M = UH}))))

  BXYh-ty : BdyTy ΔT2 ΘXY ΔXY (` 1 ⇒ (` 0 ⇒ ` 1)) cXY (★ ⇒ (★ ⇒ ★))
  BXYh-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔT2} {M = CH ⟪ ΘXY , cXY ⟫}))))

  pY-ty : CastTy ΔY (★∼X ∷ []) pY (★ ⇒ (★ ⇒ ★)) (★ ⇒ (` 0 ⇒ ★))
  pY-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔY} {M = NCY})))

  pX-ty : CastTy ΔXY (X∼X ∷ ★∼X ∷ []) pX (★ ⇒ (` 0 ⇒ ★))
    (` 1 ⇒ (` 0 ⇒ ` 1))
  pX-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔXY} {M = NCX})))

  UY-ty : BdyTy ΔY (unbind 0 0 ∷ []) ΔT2 (★ ⇒ (★ ⇒ ★)) cU (★ ⇒ (★ ⇒ ★))
  UY-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔY} {M = NUY}))))

  UX-ty : BdyTy ΔXY (unbind 1 1 ∷ []) ΔY (★ ⇒ (` 0 ⇒ ★)) cUX
    (★ ⇒ (` 0 ⇒ ★))
  UX-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔXY} {M = NUX}))))

  BXYn-ty : BdyTy ΔT2 ΘXY ΔXY (` 1 ⇒ (` 0 ⇒ ` 1)) cXY (★ ⇒ (★ ⇒ ★))
  BXYn-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔT2} {M = NCX ⟪ ΘXY , cXY ⟫}))))

  ----------------------------------------------------------------------
  -- the initial pairs (related at ∅ʷ)

  idK2 : ∀ {μ} → μ ⊢ K2 ⊑ K2
  idK2 = ∀⊑∀ (∀⊑∀ (⇒⊑⇒ X⊑X (⇒⊑⇒ X⊑X X⊑X)))

  idKY : ∀ {μ} → μ ⊢ KY ⊑ KY
  idKY = ∀⊑∀ (⇒⊑⇒ ★⊑★ (⇒⊑⇒ X⊑X ★⊑★))

  q0 : ∀ {μ} → μ ⊢ `∀ (` 0 ⇒ `ℕ) ⊑ (★ ⇒ `ℕ)
  q0 = ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) ι)

  K★⊑K★ : ∀ {Δ Δ′} {W : World Δ Δ′} {γ}
    → W ∣ γ ⊢ K★ ⊑ K★ ∶ ⇒⊑⇒ ★⊑★ (⇒⊑⇒ ★⊑★ ★⊑★)
  K★⊑K★ = ƛ⊑ƛ tf tf (ƛ⊑ƛ {pA = ★⊑★} {pB = ★⊑★} tf tf (x⊑x (Sʷ Zʷ)))

  KΛ⊑KΛ : ∅ʷ ∣ [] ⊢ KΛ ⊑ KΛ ∶ ∀⊑∀ (⇒⊑⇒ X⊑X (⇒⊑⇒ ★⊑★ X⊑X))
  KΛ⊑KΛ =
    Λ⊑Λ lift-[] vNΛ vNΛ
      (ƛ⊑ƛ {pA = X⊑X} tf tf (ƛ⊑ƛ {pA = ★⊑★} {pB = X⊑X} tf tf (x⊑x (Sʷ Zʷ))))
      (∀⊑∀ (⇒⊑⇒ X⊑X (⇒⊑⇒ ★⊑★ X⊑X)))

  GL⊑GL : ∅ʷ ∣ [] ⊢ GL ⊑ GL ∶ idK2
  GL⊑GL = cast⊑cast K★⊑K★ genK-ty genK-ty idK2

  HL⊑HL : ∅ʷ ∣ [] ⊢ HL ⊑ HL ∶ idK2
  HL⊑HL = cast⊑cast KΛ⊑KΛ ∀gen-ty ∀gen-ty idK2

  NL⊑NL : ∅ʷ ∣ [] ⊢ NL ⊑ NL ∶ idK2
  NL⊑NL = cast⊑cast (cast⊑cast K★⊑K★ genY-ty genY-ty idKY)
            genX∀-ty genX∀-ty idK2

  g0-init : ∅ʷ ∣ [] ⊢ FL ⊑ FR ∶ q0
  g0-init =
    ⊑cast
      (cast⊑cast (ƛ⊑ƛ {pA = ★⊑★} tf tf (κ⊑κ lit-$ ι))
        genX5-ty genX5-ty (∀⊑∀ (⇒⊑⇒ X⊑X ι)))
      instX5-ty q0

  g2m-init : ∅ʷ ∣ [] ⊢ GL ⊑ GRm ∶ q-top
  g2m-init = ⊑cast GL⊑GL instK-ty q-top

  g2-init : ∅ʷ ∣ [] ⊢ GL ⊑ GR ∶ q-top
  g2-init = ⊑cast (⊑cast GL⊑GL instX∀-ty q-src1) instY-ty₀ q-top

  hrm-init : ∅ʷ ∣ [] ⊢ HL ⊑ HRm ∶ q-top
  hrm-init = ⊑cast HL⊑HL instK-ty q-top

  hr-init : ∅ʷ ∣ [] ⊢ HL ⊑ HR ∶ q-top
  hr-init = ⊑cast (⊑cast HL⊑HL instX∀-ty q-src1) instY-ty₀ q-top

  nr-init : ∅ʷ ∣ [] ⊢ NL ⊑ NR ∶ q-top
  nr-init = ⊑cast (⊑cast NL⊑NL instX∀-ty q-src1) instY-ty₀ q-top

  nrm-init : ∅ʷ ∣ [] ⊢ NL ⊑ NRm ∶ q-top
  nrm-init = ⊑cast NL⊑NL instK-ty q-top

  ----------------------------------------------------------------------
  -- the worlds, at any permissions κ

  -- outside: ΔT2, no type variable (H1's W₄ at κ = [])
  W4 : List RVar → World empty ΔT2
  W4 κ = world 0 []↪ []↪ [] [] κ

  W4-wf : ∀ {κ} → All (reps ΔT2 ∋ʳ_) κ → WfWorld (W4 κ)
  W4-wf ps = wf-world joint[] (λ { (inj₁ ()) ; (inj₂ ()) })
    (λ { (_ , ()) _ _ _ _ }) (λ { _ (_ , ()) _ _ _ }) ps

  -- inside +Y^β, +X^α: X (type variable 1), Y (type variable 0), both
  -- right-only
  Wm : List RVar → World empty ΔXY
  Wm κ = world 2 (skip (skip []↪)) (keep (keep []↪)) [] [] κ

  wfm : ∀ {κ} → All (reps ΔXY ∋ʳ_) κ → WfWorld (Wm κ)
  wfm ps = wf-world (right-only (right-only joint[]))
    (λ { (inj₁ ()) ; (inj₂ ()) })
    (λ { (_ , ()) _ _ _ _ }) (λ { _ _ _ (inj₁ ()) _ ; _ _ _ (inj₂ ()) _ })
    ps

  -- inside +Y^β alone: Y right-only
  WYg : List RVar → World empty ΔY
  WYg κ = world 1 (skip []↪) (keep []↪) [] [] κ

  wfYg : ∀ {κ} → All (reps ΔY ∋ʳ_) κ → WfWorld (WYg κ)
  wfYg ps = wf-world (right-only joint[]) (λ { (inj₁ ()) ; (inj₂ ()) })
    (λ { (_ , ()) _ _ _ _ }) (λ { _ _ _ (inj₁ ()) _ ; _ _ _ (inj₂ ()) _ })
    ps

  -- gen over Λ: after the Λ joins X (lexical pair (0, X's rep. var 1))
  W1h : List RVar → World (underΛ empty) ΔXY
  W1h κ = world 2 (skip (keep []↪)) (keep (keep []↪)) [] ((0 , 1) ∷ []) κ

  Wq : List RVar → World (underΛ empty) ΔX1
  Wq κ = world 1 (keep []↪) (keep []↪) [] ((0 , 1) ∷ []) κ

  wfq : ∀ {κ} → All (reps ΔX1 ∋ʳ_) κ → WfWorld (Wq κ)
  wfq {κ} ps = wf-world (both (inj₂ here⇔) joint[])
    (λ { (inj₁ ()) ; (inj₂ here⇔) → abst-★ r-here (r-there r-here)
       ; (inj₂ (there⇔ ())) })
    (namedᴸ-≤1 (Wq κ) ≤1-∷[]) (namedᴿ-≤1 (Wq κ) ≤1-∷[]) ps

  join1h : ∀ {κ} → Join1 (Wm κ) 1 (W1h κ)
  join1h = join1 (join-there join-here) (there here) (r-there r-here)

  -- the boundaries
  intXYW : ∀ {κ} → Interior (W4 κ) [] ΘXY (Wm κ)
  intXYW = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷
        (changes∷ changes[] (step-bind (bindR ★ , here) fresh[] ins-here))
        (step-bind (bindR ★ , there here) (fresh∷ (λ ()) fresh[])
          (ins-there ins-here)))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  intU2 : ∀ {κ} → Interior (Wm κ) [] U2 (W4 κ)
  intU2 = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷
        (changes∷ changes[]
          (step-unbind (bindR ★ , here) del-here (fresh∷ (λ ()) fresh[])))
        (step-unbind (bindR ★ , there here) del-here fresh[]))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  intUH : ∀ {κ} → Interior (W1h κ) [] (unbind 0 0 ∷ []) (Wq κ)
  intUH = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
        (step-unbind (bindR ★ , here) del-here (fresh∷ (λ ()) fresh[])))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , here) (_ , here) refl refl →
                         (λ _ → refl) , (λ _ → refl)
                     ; (_ , there ()) _ _ _
                     ; (_ , here) (_ , there ()) _ _ }
    ; join-fresh = λ { here here (inj₁ ()) ; here here (inj₂ ())
                     ; (there ()) _ _ ; here (there ()) _ }
    }

  intYg : ∀ {κ} → Interior (W4 κ) [] ΘY (WYg κ)
  intYg = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-bind (_ , here) fresh[] ins-here))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  -- the inner Inst boundary +X^α: Y carried, X new
  intXg : ∀ {κ} → Interior (WYg κ) [] ΘX (Wm κ)
  intXg = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-bind (_ , there here)
                        (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  -- N2: the right's −X^α (Y continues) and −Y^β
  intUX : ∀ {κ} → Interior (Wm κ) [] (unbind 1 1 ∷ []) (WYg κ)
  intUX = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
        (step-unbind (bindR ★ , there here) (del-there del-here)
          (fresh∷ (λ ()) fresh[])))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  intUY : ∀ {κ} → Interior (WYg κ) [] (unbind 0 0 ∷ []) (W4 κ)
  intUY = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
        (step-unbind (bindR ★ , here) del-here fresh[]))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  -- the openings: X (rep. var 1) then Y (rep. var 0), right-only, ★
  okm : ∀ {κ} → All (SlotOK (Wm κ)) (opn 1 ∷ opn 0 ∷ [])
  okm = (1 , there here , r-there r-here , (λ { (_ , ()) }) ,
          (λ { (_ , ()) }))
      ∷ (0 , here , r-here , (λ { (_ , ()) }) , (λ { (_ , ()) })) ∷ []

  nem : AllPairs SlotNe (opn 1 ∷ opn 0 ∷ [])
  nem = ((λ ()) ∷ []) ∷ [] ∷ []

  okY : ∀ {κ} → All (SlotOK (WYg κ)) (skp ∷ opn 0 ∷ [])
  okY = tt ∷ (0 , here , r-here , (λ { (_ , ()) }) , (λ { (_ , ()) })) ∷ []

  neY : AllPairs SlotNe (skp ∷ opn 0 ∷ [])
  neY = (tt ∷ []) ∷ [] ∷ []

  okUX : ∀ {κ} → All (SlotOK (WYg κ)) (opn 0 ∷ [])
  okUX = (0 , here , r-here , (λ { (_ , ()) }) , (λ { (_ , ()) })) ∷ []

  -- the merged boundary opens X then Y: it may permit both
  jrXY : ∀ {κ Θ′} → All (JoinRep (Wm κ) [] Θ′ (opn 1 ∷ opn 0 ∷ []))
    (1 ∷ 0 ∷ [])
  jrXY = jr-open oh (there here) ∷ jr-open (ot oh) here ∷ []

  κ10 : List RVar
  κ10 = 1 ∷ 0 ∷ []

  -- the indices
  qm : ∀ κ → K2 ⊑ᵂ⟨ Wm κ ⟩[ opn 1 ∷ opn 0 ∷ [] ] (` 1 ⇒ (` 0 ⇒ ` 1))
  qm _ = ⇒⊑⇒ X⊑X (⇒⊑⇒ X⊑X X⊑X)

  q★ : K2 ⊑ᵂ⟨ Wm κ10 ⟩[ opn 1 ∷ opn 0 ∷ [] ] (★ ⇒ (★ ⇒ ★))
  q★ = ⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ (X⊑★ here) (X⊑★ (there here)))

  qH : ∀ κ → `∀ (` 0 ⇒ (★ ⇒ ` 0)) ⊑ᵂ⟨ Wm κ ⟩[ opn 1 ∷ [] ]
    (` 1 ⇒ (★ ⇒ ` 1))
  qH _ = ⇒⊑⇒ X⊑X (⇒⊑⇒ ★⊑★ X⊑X)

  qH★ : K2 ⊑ᵂ⟨ Wm κ10 ⟩[ opn 1 ∷ opn 0 ∷ [] ] (` 1 ⇒ (★ ⇒ ` 1))
  qH★ = ⇒⊑⇒ X⊑X (⇒⊑⇒ (X⊑★ here) X⊑X)

  -- THE SKIP: at the outer +Y^β, K2's outer ∀ waits left-only and its
  -- inner ∀ opens at Y
  qY : ∀ κ → K2 ⊑ᵂ⟨ WYg κ ⟩[ skp ∷ opn 0 ∷ [] ] (★ ⇒ (` 0 ⇒ ★))
  qY _ = nv-∀ , ∈-∀ (∈-⇒ˡ ∈-var) , ⇒⊑⇒ (X⊑★ here) (⇒⊑⇒ X⊑X (X⊑★ here))

  ----------------------------------------------------------------------
  -- G0: one opening, permitted; the gen consumes it

  g0-final : W₃ ∣ [] ⊢ FL ⊑ FR₂ ∶ q0
  g0-final =
    ⊑cast
      (⊑⟪⟫ int-ro₃ (push₀ vFL) ok₃ ne₀ (jo₀ ∷ []) wf¹ (⇒⊑⇒ X⊑X ι)
        (⊑cast {A = `∀ (` 0 ⇒ `ℕ)}
          (cast⊑ (co-gen (V-simple S-ƛ) co-plain)
            (⊑⟪⟫₀ IntN (W₃-wf p0)
              (ƛ⊑ƛ {pA = ★⊑★} tf tf (κ⊑κ lit-$ ι)) UF-ty (⇒⊑⇒ ★⊑★ ι))
            genX5-ty (⇒⊑⇒ (X⊑★ here) ι))
          pF-ty (⇒⊑⇒ X⊑X ι))
        BF-ty q0)
      cF-ty q0

  ----------------------------------------------------------------------
  -- G2m, HRm, N2 merged: the merged boundary opens X then Y and permits
  -- both (K = [1, 0])

  merged : ∀ {M M′ c′ A′ᵢ} {r : K2 ⊑ᵂ⟨ Wm κ10 ⟩[ opn 1 ∷ opn 0 ∷ [] ] A′ᵢ}
    → Value M → K2 ⊑ᵂ⟨ Wm [] ⟩[ opn 1 ∷ opn 0 ∷ [] ] A′ᵢ
    → Wm κ10 ∣ [] ⊢ M ⊑ M′ ∶[ opn 1 ∷ opn 0 ∷ [] ] r
    → BdyTy ΔT2 ΘXY ΔXY A′ᵢ c′ (★ ⇒ (★ ⇒ ★))
    → W4 [] ∣ [] ⊢ M ⊑ M′ ⟪ ΘXY , c′ ⟫ ∶⟨ K2 , ★ ⇒ (★ ⇒ ★) ⟩ q-top
  merged v pay d b =
    ⊑⟪⟫ intXYW (push ca-[] f-end (ns-opn refl ∷ ns-opn refl ∷ []) (inj₂ v))
      okm nem jrXY (wfm p10) pay d b q-top

  -- G2m's (and G2's) gen body: ⊑cast `X! → Y! → X?` at the permitted
  -- X, Y; then BOTH gen layers consume their openings; then the right's
  -- `−Y^β, −X^α`
  bodyK : Wm κ10 ∣ [] ⊢ GL ⊑ CK ∶[ opn 1 ∷ opn 0 ∷ [] ] qm κ10
  bodyK =
    ⊑cast
      (cast⊑ (co-gen vK★ (co-gen vK★ co-plain))
        (⊑⟪⟫₀ intU2 (W4-wf p10) K★⊑K★ UK-ty (⇒⊑⇒ ★⊑★ (⇒⊑⇒ ★⊑★ ★⊑★)))
        genK-ty q★)
      pK-ty (qm κ10)

  g2m-final : W4 [] ∣ [] ⊢ GL ⊑ GmF ∶ q-top
  g2m-final = ⊑cast (merged vGL (qm []) bodyK BXY-ty) cf-ty q-top

  -- HRm's (and HR's) body: ⊑cast `id(X) → Y! → id(X)` at the permitted
  -- Y; the ∀ layer passes X to the Λ, the gen layer consumes Y; the Λ
  -- JOINS X (b-join); then the right's `−Y^β`
  NΛ⊑NΛ : Wq κ10 ∣ [] ⊢ NΛ ⊑ NΛ ∶ ⇒⊑⇒ X⊑X (⇒⊑⇒ ★⊑★ X⊑X)
  NΛ⊑NΛ = ƛ⊑ƛ {pA = X⊑X} tf tf
    (ƛ⊑ƛ {pA = ★⊑★} {pB = X⊑X} tf tf (x⊑x (Sʷ Zʷ)))

  bodyH : Wm κ10 ∣ [] ⊢ HL ⊑ CH ∶[ opn 1 ∷ opn 0 ∷ [] ] qm κ10
  bodyH =
    ⊑cast
      (cast⊑ (co-∀ vKΛ (co-gen vKΛ co-plain))
        (Λ⊑ (b-join join1h) nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] vNΛ
          (⊑⟪⟫₀ intUH (wfq p10) NΛ⊑NΛ UH-ty (⇒⊑⇒ X⊑X (⇒⊑⇒ ★⊑★ X⊑X)))
          (qH κ10))
        ∀gen-ty qH★)
      pH-ty (qm κ10)

  hrm-final : W4 [] ∣ [] ⊢ HL ⊑ HmF ∶ q-top
  hrm-final = ⊑cast (merged vHL (qm []) bodyH BXYh-ty) cf-ty q-top

  -- N2: the outer cast `gen X. ∀Y. …` consumes X and passes Y; the
  -- right's −X^α carries Y; the inner `gen Y. …` consumes Y
  qXY : ∀ κ → KY ⊑ᵂ⟨ WYg κ ⟩[ opn 0 ∷ [] ] (★ ⇒ (` 0 ⇒ ★))
  qXY _ = ⇒⊑⇒ ★⊑★ (⇒⊑⇒ X⊑X ★⊑★)

  qXYm : KY ⊑ᵂ⟨ Wm κ10 ⟩[ opn 0 ∷ [] ] (★ ⇒ (` 0 ⇒ ★))
  qXYm = ⇒⊑⇒ ★⊑★ (⇒⊑⇒ X⊑X ★⊑★)

  qY★ : KY ⊑ᵂ⟨ WYg κ10 ⟩[ opn 0 ∷ [] ] (★ ⇒ (★ ⇒ ★))
  qY★ = ⇒⊑⇒ ★⊑★ (⇒⊑⇒ (X⊑★ here) ★⊑★)

  qX★ : K2 ⊑ᵂ⟨ Wm κ10 ⟩[ opn 1 ∷ opn 0 ∷ [] ] (★ ⇒ (` 0 ⇒ ★))
  qX★ = ⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ X⊑X (X⊑★ (there here)))

  inner : WYg κ10 ∣ [] ⊢ NL₁ ⊑ NCY ∶[ opn 0 ∷ [] ] qXY κ10
  inner =
    ⊑cast
      (cast⊑ (co-gen vK★ co-plain)
        (⊑⟪⟫₀ intUY (W4-wf p10) K★⊑K★ UY-ty (⇒⊑⇒ ★⊑★ (⇒⊑⇒ ★⊑★ ★⊑★)))
        genY-ty qY★)
      pY-ty (qXY κ10)

  bodyN : Wm κ10 ∣ [] ⊢ NL ⊑ NCX ∶[ opn 1 ∷ opn 0 ∷ [] ] qm κ10
  bodyN =
    ⊑cast
      (cast⊑ (co-gen vNL₁ (co-∀ vNL₁ co-plain))
        (⊑⟪⟫ intUX (push (ca-opn refl ca-[]) (f-keep f-end) [] (inj₁ refl))
          okUX ([] ∷ []) [] (wfYg p10) (qXY κ10) inner UX-ty qXYm)
        genX∀-ty qX★)
      pX-ty (qm κ10)

  nrm-final : W4 [] ∣ [] ⊢ NL ⊑ NmF ∶ q-top
  nrm-final = ⊑cast (merged vNL (qm []) bodyN BXYn-ty) cf-ty q-top

  ----------------------------------------------------------------------
  -- G2, HR, N2 two-cast: +Y^β creates [skip, Y] and permits β; +X^α
  -- FILLS the skip with X and permits α; then the merged case's body

  twoCast : ∀ {M M′} → Value M → GenCastValue M
    → Wm κ10 ∣ [] ⊢ M ⊑ M′ ∶[ opn 1 ∷ opn 0 ∷ [] ] qm κ10
    → W4 [] ∣ [] ⊢ M ⊑ ((M′ ⟪ ΘX , cX ⟫) ⟨ X∼X ∷ [] ∣ ci ⟩) ⟪ ΘY , cY ⟫
        ∶⟨ K2 , ★ ⇒ (★ ⇒ ★) ⟩ q-top
  twoCast v g d =
    ⊑⟪⟫ intYg (push ca-[] f-end (ns-skp g ∷ ns-opn refl ∷ []) (inj₂ v))
      okY neY (jr-open (ot oh) here ∷ []) (wfYg p0) (qY [])
      (⊑cast
        (⊑⟪⟫ intXg
          (push (ca-skp (ca-opn refl ca-[])) (f-fill (f-keep f-end))
            (ns-opn refl ∷ []) (inj₂ v))
          okm nem (jr-open oh (there here) ∷ []) (wfm p10) (qm (0 ∷ [])) d bX
          (qY (0 ∷ [])))
        ci-ty (qY (0 ∷ [])))
      bY q-top

  g2-final : W4 [] ∣ [] ⊢ GL ⊑ GF ∶ q-top
  g2-final = ⊑cast (twoCast vGL gcvGL bodyK) cf-ty q-top

  hr-final : W4 [] ∣ [] ⊢ HL ⊑ HF ∶ q-top
  hr-final = ⊑cast (twoCast vHL gcvHL bodyH) cf-ty q-top

  nr-final : W4 [] ∣ [] ⊢ NL ⊑ NF ∶ q-top
  nr-final = ⊑cast (twoCast vNL gcvNL bodyN) cf-ty q-top

------------------------------------------------------------------------
-- 4. DGG PART 1 for TwoGen's seven pairs, H1 and K: the left is a
-- value; the right's run (pinned by `eval`) reaches its value; the
-- relation relates them at a well-formed top-level world with no
-- permission, at O = []
------------------------------------------------------------------------

module DGG1 where
  open TwoGen
  open H1 using (K2; q-top)

  Part1 : Term → Term → Ty → Ty → Set
  Part1 M M′ A A′ =
    ∃[ V′ ] Σ[ r′ ∈ empty ⊢ M′ -→* V′ ] Value V′
      × Σ[ W ∈ World empty (runCtx r′) ] WfWorld W × κʷ W ≡ []
        × Σ[ q ∈ A ⊑ᵂ⟨ W ⟩ A′ ] (W ∣ [] ⊢ M ⊑ V′ ∶ q)

  g0 : Part1 FL FR (`∀ (` 0 ⇒ `ℕ)) (★ ⇒ `ℕ)
  g0 = _ , runOf (eval 40 FR FR-⊢) tt , vEnd (eval 40 FR FR-⊢) tt ,
       TIE.W₃ , Rbs.W₃-wf [] , refl , q0 , g0-final

  g2m : Part1 GL GRm K2 (★ ⇒ (★ ⇒ ★))
  g2m = _ , runOf (eval 40 GRm GRm-⊢) tt , vEnd (eval 40 GRm GRm-⊢) tt ,
        W4 [] , W4-wf [] , refl , q-top , g2m-final

  g2 : Part1 GL GR K2 (★ ⇒ (★ ⇒ ★))
  g2 = _ , runOf (eval 40 GR GR-⊢) tt , vEnd (eval 40 GR GR-⊢) tt ,
       W4 [] , W4-wf [] , refl , q-top , g2-final

  hrm : Part1 HL HRm K2 (★ ⇒ (★ ⇒ ★))
  hrm = _ , runOf (eval 40 HRm HRm-⊢) tt , vEnd (eval 40 HRm HRm-⊢) tt ,
        W4 [] , W4-wf [] , refl , q-top , hrm-final

  hr : Part1 HL HR K2 (★ ⇒ (★ ⇒ ★))
  hr = _ , runOf (eval 40 HR HR-⊢) tt , vEnd (eval 40 HR HR-⊢) tt ,
       W4 [] , W4-wf [] , refl , q-top , hr-final

  nrm : Part1 NL NRm K2 (★ ⇒ (★ ⇒ ★))
  nrm = _ , runOf (eval 40 NRm NRm-⊢) tt , vEnd (eval 40 NRm NRm-⊢) tt ,
        W4 [] , W4-wf [] , refl , q-top , nrm-final

  nr : Part1 NL NR K2 (★ ⇒ (★ ⇒ ★))
  nr = _ , runOf (eval 40 NR NR-⊢) tt , vEnd (eval 40 NR NR-⊢) tt ,
       W4 [] , W4-wf [] , refl , q-top , nr-final

  -- H1 (design.md D29): claim-rep, an opening, a carried slot, a join
  h1 : Part1 H1.L₀ H1.R₀ K2 (★ ⇒ (★ ⇒ ★))
  h1 = H1.R₄ , (H1.st₀ then H1.st₁ then H1.st₂ then H1.st₃ then done) ,
       H1.vR₄ , H1.W₄ , H1.W₄-wf , refl , q-top , H1.final

  -- K (D26's counterexample): the real witness
  k = RG.dgg1-K

------------------------------------------------------------------------
-- 5. P5 (design.md §C7; no derivation existed before D31): the left
-- blames on an escaped tag, the right answers.  The initial pair; the
-- pair before the left's TagUntagBad-⟪⟫ (the left's seal is a payload
-- view under its own `+X`, X left-only: R1′ reads the seal's exterior
-- type X, and α has no partner); the blame.
------------------------------------------------------------------------

module P5 where
  open import examples.ImprecisionExamples using (L5; R5; L5-⊢; R5-⊢)
  open import examples.Examples using (ℓ; μX)
  import examples.Examples
  open PE.P4 using (S; bS)
  open TIE using (ΔL; ΔLᵢ; W₂; Wᵢ₂; Wᵢ₂-int; Wᵢ₂-wf; ℕ⊑★)

  ℕ?-ty : ∀ {Ξ} → CastTy (Ξ ∣ []) [] (`ℕ ？ ℓ) ★ `ℕ
  ℕ?-ty = cast-ty (⊢check g-ℕ) refl

  idℕ⊑ : ∀ {Δ Δ′} {W : World Δ Δ′} {γ}
    → W ∣ γ ⊢ ƛ `ℕ ∙ ` 0 ⊑ ƛ `ℕ ∙ ` 0 ∶ ⇒⊑⇒ ι ι
  idℕ⊑ = ƛ⊑ƛ {pA = ι} {pB = ι} wf-ℕ wf-ℕ (x⊑x Zʷ)

  five : ∀ {Δ Ξ′} {W : World Δ (Ξ′ ∣ [])} {γ}
    → W ∣ γ ⊢ $ 5 ⊑ TIE.5⟨ℕ!⟩ ∶ ℕ⊑★
  five = ⊑cast (κ⊑κ lit-$ ι) (cast-ty (⊢tag g-ℕ) refl) ℕ⊑★

  inner-ty : NuTy empty `ℕ (` 0 ⇒ ★) (reveal 0 (` 0 ⇒ ★)) (`ℕ ⇒ ★)
  inner-ty = proj₂ (proj₂ (ν-inv {Γ = []}
    (tc {Δ = empty} {M = examples.Examples.ex4-inner})))

  tagY-ty : CastTy (underΛ empty) μX ((` 0) !) (` 0) ★
  tagY-ty = cast-ty (⊢tag-var (_ , here) here tag-cross) refl

  -- the initial pair: ν⊑ over Λ⊑ (Y left-only); the left's tag x⟨Y!⟩
  -- against the right's x by cast⊑
  init : ∅ʷ ∣ [] ⊢ L5 ⊑ R5 ∶ ι
  init =
    ·⊑· idℕ⊑
      (cast⊑cast
        (·⊑· {pA = ℕ⊑★} {pB = ★⊑★}
          (ν⊑
            (Λ⊑ b-fresh nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
              (ƛ⊑ƛ {pA = X⊑★ here} {pB = ★⊑★} tf wf-★
                (·⊑· {pA = ★⊑★} {pB = ★⊑★}
                  (ƛ⊑ƛ {pA = ★⊑★} {pB = ★⊑★} wf-★ wf-★ (x⊑x Zʷ))
                  (cast⊑ co-plain (x⊑x Zʷ) tagY-ty ★⊑★)))
              (∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) ★⊑★)))
            ℕ⊑★ inner-ty (⇒⊑⇒ ℕ⊑★ ★⊑★))
          five)
        ℕ?-ty ℕ?-ty ι)

  -- the left's state 4 against the right's state 2
  T L₄ R₂ : Term
  T  = (S ⟨ μX ∣ (` 0) ! ⟩) ⟪ TIE.Θ₀ , ⌞ id ★ ⌟ ⟫
  L₄ = (ƛ `ℕ ∙ ` 0) · (T ⟨ [] ∣ `ℕ ？ ℓ ⟩)
  R₂ = (ƛ `ℕ ∙ ` 0) · (TIE.5⟨ℕ!⟩ ⟨ [] ∣ `ℕ ？ ℓ ⟩)

  L₄-state : nth (evalTerms 20 L5-⊢) 4 ≡ L₄
  L₄-state = refl

  R₂-state : nth (evalTerms 20 R5-⊢) 2 ≡ R₂
  R₂-state = refl

  bT : BdyTy ΔL TIE.Θ₀ ΔLᵢ ★ ⌞ id ★ ⌟ ★
  bT = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = T}))))

  tagX-ty : CastTy ΔLᵢ μX ((` 0) !) (` 0) ★
  tagX-ty = cast-ty (⊢tag-var (_ , here) here tag-cross) refl

  -- the left's seal alone: X goes away
  intS : Interior Wᵢ₂ (unbind 0 0 ∷ []) [] W₂
  intS = record
    { int-left   = Rbs.unbind₀-int
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  wf₂ : WfWorld W₂
  wf₂ = wf-world joint[] (λ { (inj₁ ()) ; (inj₂ ()) })
    (λ { _ _ _ (inj₁ ()) _ ; _ _ _ (inj₂ ()) _ })
    (λ { _ _ _ (inj₁ ()) _ ; _ _ _ (inj₂ ()) _ }) []

  p5-mid : W₂ ∣ [] ⊢ L₄ ⊑ R₂ ∶ ι
  p5-mid =
    ·⊑· idℕ⊑
      (cast⊑cast
        (⟪⟫⊑₀ Wᵢ₂-int (ok-bind ∷ []) Wᵢ₂-wf
          (cast⊑ co-plain
            (⟪⟫⊑₀ intS (ok-unbind (λ { (inj₁ ()) ; (inj₂ ()) }) ∷ [])
              wf₂ five bS (X⊑★ here))
            tagX-ty ★⊑★)
          bT ★⊑★)
        ℕ?-ty ℕ?-ty ι)

  -- the left blames; blame ⊑ anything
  fin : W₂ ∣ [] ⊢ (ƛ `ℕ ∙ ` 0) · blame ℓ ⊑ (ƛ `ℕ ∙ ` 0) · $ 5 ∶ ι
  fin = ·⊑· idℕ⊑ (blame⊑ wf-ℕ ⊢$ ι)

------------------------------------------------------------------------
-- 6. R2c (ForallBoundaryRisks §3): a left gen-cast value over a
-- boundary value against the right's Inst boundary, before and after
-- the right's Merge INSIDE it.
--   L  (λh:∀X.X→X. h) ((λg:∀X.X→X. g) ((ΛX.λx:X.x)[★]))
--   R  (λh:★→★. h)    ((λg:∀X.X→X. g) ((ΛX.λx:X.x)[★]))
-- The Inst boundary +Y^β OPENS the left's ∀ at Y and permits β; the
-- right's gen wrapper is peeled at Y⊑★; the left's gen CONSUMES the
-- opening; then the matched +X ∥ +X (before the Merge: under the
-- right's −Y; after it: one merged −Y, +X boundary).
------------------------------------------------------------------------

module R2c where
  open import examples.CambridgeExamples using (I; genI; instI)
  open TIE using (idX; revX; ∀X⇒X; Θ₀; ΔR; revX⊑revX)
  open Rbs using (id★↦; id★→; tagX↦; ∀id⊑★)

  I[★] Gc L2c R2c : Term
  I[★] = ν ★ · I ⟨ revX ⟩
  Gc   = (ƛ ∀X⇒X ∙ ` 0) · (I[★] ⟨ [] ∣ genI ⟩)
  L2c  = (ƛ ∀X⇒X ∙ ` 0) · Gc
  R2c  = (ƛ (★ ⇒ ★) ∙ ` 0) · (Gc ⟨ [] ∣ instI ⟩)

  L2c-⊢ : empty ∣ [] ⊢ L2c ⦂ ∀X⇒X
  L2c-⊢ = tc

  R2c-⊢ : empty ∣ [] ⊢ R2c ⦂ (★ ⇒ ★)
  R2c-⊢ = tc

  Θ₁ Θm : Boundary
  Θ₁ = bind 0 1 ∷ []
  Θm = bind 0 1 ∷ unbind 0 0 ∷ []

  Bα V2 L2c₂ Bin Nu N N₀ R2c₄ R2c₅ R2c₆ : Term
  Bα   = idX ⟪ Θ₀ , revX ⟫
  V2   = Bα ⟨ [] ∣ genI ⟩
  L2c₂ = (ƛ ∀X⇒X ∙ ` 0) · V2
  Bin  = idX ⟪ Θ₁ , revX ⟫
  Nu   = Bin ⟪ unbind 0 0 ∷ [] , id★→ ⟫
  N    = Nu ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩
  N₀   = (idX ⟪ Θm , revX ⟫) ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩
  R2c₄ = (ƛ (★ ⇒ ★) ∙ ` 0) · ((N ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩)
  R2c₅ = (ƛ (★ ⇒ ★) ∙ ` 0) · ((N₀ ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩)
  R2c₆ = (N₀ ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩

  L2c₂-state : nth (evalTerms 20 L2c-⊢) 2 ≡ L2c₂
  L2c₂-state = refl

  V2-state : nth (evalTerms 20 L2c-⊢) 3 ≡ V2
  V2-state = refl

  R2c₄-state : nth (evalTerms 20 R2c-⊢) 4 ≡ R2c₄
  R2c₄-state = refl

  R2c₅-state : nth (evalTerms 20 R2c-⊢) 5 ≡ R2c₅
  R2c₅-state = refl

  R2c₆-state : nth (evalTerms 20 R2c-⊢) 6 ≡ R2c₆
  R2c₆-state = refl

  vBα : Value Bα
  vBα = V-⟪⟫ S-ƛ I-fun

  vV2 : Value V2
  vV2 = V-simple (S-cast vBα I-gen)

  -- contexts: left αᴸ:=★ (rep. var 0); right β:=★ (0, the Inst's),
  -- αᴿ:=★ (1)
  ΞR : RepCtx
  ΞR = bindR ★ ∷ bindR ★ ∷ []

  ΔR2 ΔRY ΔRX ΔLX : Ctxᵗ
  ΔR2 = ΞR ∣ []
  ΔRY = ΞR ∣ (0 ∷ [])
  ΔRX = ΞR ∣ (1 ∷ [])
  ΔLX = (bindR ★ ∷ []) ∣ (0 ∷ [])

  ϱ : RepRel
  ϱ = (0 , 1) ∷ []

  -- the worlds (κ = the permission of β where it holds)
  W4 W4¹ : World ΔR ΔR2
  W4  = world 0 []↪ []↪ ϱ [] []
  W4¹ = world 0 []↪ []↪ ϱ [] (0 ∷ [])

  Wy : World ΔR ΔRY
  Wy = world 1 (skip []↪) (keep []↪) ϱ [] []

  Wb : World ΔLX ΔRX
  Wb = world 1 (keep []↪) (keep []↪) ϱ [] (0 ∷ [])

  agreeR : ∀ {n nsL nsR κ} {η : nsL ↪ n} {η′ : nsR ↪ n} {α β}
    → let W = world {(bindR ★ ∷ []) ∣ nsL} {ΞR ∣ nsR} n η η′ ϱ [] κ in
      Paired W α β → Agree W α β
  agreeR (inj₁ here⇔) = rep-rep r-here (r-there r-here) ★⊑★
  agreeR (inj₁ (there⇔ ()))
  agreeR (inj₂ ())

  -- +Y^β alone: Y right-only, opened
  intY : Interior W4 [] Θ₀ Wy
  intY = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-bind (_ , here) fresh[] ins-here))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  okY : All (SlotOK Wy) (opn 0 ∷ [])
  okY = (0 , here , r-here , (λ { (_ , ()) }) , (λ { (_ , ()) })) ∷ []

  wfY¹ : WfWorld (Wy +κ (0 ∷ []))
  wfY¹ = wf-world (right-only joint[]) agreeR (namedᴸ-≤1 W ≤1-[])
    (namedᴿ-≤1 W ≤1-∷[]) ((_ , here) ∷ [])
    where W = Wy +κ (0 ∷ [])

  wf4¹ : WfWorld W4¹
  wf4¹ = wf-world joint[] agreeR (namedᴸ-≤1 W4¹ ≤1-[])
    (namedᴿ-≤1 W4¹ ≤1-[]) ((_ , here) ∷ [])

  wfb : WfWorld Wb
  wfb = wf-world (both (inj₁ here⇔) joint[]) agreeR (namedᴸ-≤1 Wb ≤1-∷[])
    (namedᴿ-≤1 Wb ≤1-∷[]) ((_ , here) ∷ [])

  -- the right's −Y alone, under β's permission
  intU : Interior (Wy +κ (0 ∷ [])) [] (unbind 0 0 ∷ []) W4¹
  intU = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-unbind (_ , here) del-here fresh[]))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  bindL : ΔR ⊢ⁱ Θ₀ ⇒ ΔLX
  bindL = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

  bindLc : ΔR ⊢ᶜ Θ₀ ⇒ ΔLX
  bindLc = conversion (conv-bind (_ , here) conv[] fresh[] ins-here)

  -- the matched +X ∥ +X (αᴸ, αᴿ paired in ϱᵍ: X joins)
  intB : Interior W4¹ Θ₀ Θ₁ Wb
  intB = record
    { int-left   = bindL
    ; int-right  = interior (changes∷ changes[]
                     (step-bind (_ , there here) fresh[] ins-here))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    }

  intBc : ConversionInterior W4¹ Θ₀ Θ₁ Wb
  intBc = record
    { conv-left       = bindLc
    ; conv-right      = conversion (conv-bind (_ , there here) conv[] fresh[]
                          ins-here)
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

  -- typing side premises, read off `tc`
  genI-ty : CastTy ΔR [] genI (★ ⇒ ★) ∀X⇒X
  genI-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔR} {M = V2})))

  tag-ty : CastTy ΔRY (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  tag-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔRY} {M = N})))

  tag₀-ty : CastTy ΔRY (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  tag₀-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔRY} {M = N₀})))

  bBα : BdyTy ΔR Θ₀ ΔLX (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bBα = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = Bα}))))

  bBin : BdyTy ΔR2 Θ₁ ΔRX (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bBin = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR2} {M = Bin}))))

  bNu : BdyTy ΔRY (unbind 0 0 ∷ []) ΔR2 (★ ⇒ ★) id★→ (★ ⇒ ★)
  bNu = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔRY} {M = Nu}))))

  bM : BdyTy ΔRY Θm ΔRX (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bM = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔRY} {M = idX ⟪ Θm , revX ⟫}))))

  bOut₄ : BdyTy ΔR2 Θ₀ ΔRY (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bOut₄ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔR2} {M = N ⟪ Θ₀ , revX ⟫}))))

  bOut₅ : BdyTy ΔR2 Θ₀ ΔRY (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bOut₅ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔR2} {M = N₀ ⟪ Θ₀ , revX ⟫}))))

  id★↦-ty : CastTy ΔR2 [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
  id★↦-ty = cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl

  idX⊑ : Wb ∣ [] ⊢ idX ⊑ idX ∶ ⇒⊑⇒ X⊑X X⊑X
  idX⊑ = ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)

  Bα⊑Bin : W4¹ ∣ [] ⊢ Bα ⊑ Bin ∶ ⇒⊑⇒ ★⊑★ ★⊑★
  Bα⊑Bin = ⟪⟫⊑⟪⟫₀ intB wfb idX⊑ bBα bBin (Wb , intBc , revX⊑revX refl)
    (⇒⊑⇒ ★⊑★ ★⊑★)

  -- the Inst boundary: open Y, permit β (pay: ∀X.X→X ⊑^[Y] Y→Y)
  instB : ∀ {M′} {r : ∀X⇒X ⊑ᵂ⟨ Wy +κ (0 ∷ []) ⟩[ opn 0 ∷ [] ] (` 0 ⇒ ` 0)}
    → Wy +κ (0 ∷ []) ∣ [] ⊢ V2 ⊑ M′ ∶[ opn 0 ∷ [] ] r
    → BdyTy ΔR2 Θ₀ ΔRY (` 0 ⇒ ` 0) revX (★ ⇒ ★)
    → W4 ∣ [] ⊢ V2 ⊑ (M′ ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩ ∶ ∀id⊑★ W4
  instB d b =
    ⊑cast
      (⊑⟪⟫ intY (push ca-[] f-end (ns-opn refl ∷ []) (inj₂ vV2)) okY
        ([] ∷ []) (jr-open oh here ∷ []) wfY¹ (⇒⊑⇒ X⊑X X⊑X) d b
        (∀id⊑★ W4))
      id★↦-ty (∀id⊑★ W4)

  outer : ∀ {M′} {r : ∀X⇒X ⊑ᵂ⟨ Wy +κ (0 ∷ []) ⟩[ opn 0 ∷ [] ] (` 0 ⇒ ` 0)}
    → Wy +κ (0 ∷ []) ∣ [] ⊢ V2 ⊑ M′ ∶[ opn 0 ∷ [] ] r
    → BdyTy ΔR2 Θ₀ ΔRY (` 0 ⇒ ` 0) revX (★ ⇒ ★)
    → W4 ∣ [] ⊢ L2c₂ ⊑ (ƛ (★ ⇒ ★) ∙ ` 0) · ((M′ ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩)
        ∶ ∀id⊑★ W4
  outer d b = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ W4} tf tf (x⊑x Zʷ)) (instB d b)

  -- before the right's Merge: the gen consumes the opening; under the
  -- right's −Y, the matched +X ∥ +X
  r2c-pre : W4 ∣ [] ⊢ L2c₂ ⊑ R2c₄ ∶ ∀id⊑★ W4
  r2c-pre = outer
    (⊑cast {A = ∀X⇒X}
      (cast⊑ (co-gen vBα co-plain)
        (⊑⟪⟫₀ intU wf4¹ Bα⊑Bin bNu (⇒⊑⇒ ★⊑★ ★⊑★))
        genI-ty (⇒⊑⇒ (X⊑★ here) (X⊑★ here)))
      tag-ty (⇒⊑⇒ X⊑X X⊑X))
    bOut₄

  -- after it: the merged −Y, +X on the right; the conversion contexts
  -- keep Y (center 1, right-only)
  Wcm : World ΔLX (ΞR ∣ (1 ∷ 0 ∷ []))
  Wcm = world 2 (keep (skip []↪)) (keep (keep []↪)) ϱ [] (0 ∷ [])

  intM : Interior (Wy +κ (0 ∷ [])) Θ₀ Θm Wb
  intM = record
    { int-left   = bindL
    ; int-right  = interior (changes∷
        (changes∷ changes[] (step-unbind (_ , here) del-here fresh[]))
        (step-bind (_ , there here) fresh[] ins-here))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    }

  intMc : ConversionInterior (Wy +κ (0 ∷ [])) Θ₀ Θm Wcm
  intMc = record
    { conv-left       = bindLc
    ; conv-right      = conversion (conv-bind (_ , there here)
        (conv-unbind (_ , here) conv[]) (fresh∷ (λ ()) fresh[]) ins-here)
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-same-κ     = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; here (there here) _ →
            (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ ()) })
        ; here (there (there ())) _
        ; (there ()) _ _
        }
    }

  merged-body : Wy +κ (0 ∷ []) ∣ [] ⊢ V2 ⊑ N₀
    ∶⟨ ∀X⇒X , ` 0 ⇒ ` 0 ⟩[ opn 0 ∷ [] ] ⇒⊑⇒ X⊑X X⊑X
  merged-body =
    ⊑cast {A = ∀X⇒X}
      (cast⊑ (co-gen vBα co-plain)
        (⟪⟫⊑⟪⟫₀ intM wfb idX⊑ bBα bM (Wcm , intMc , revX⊑revX refl)
          (⇒⊑⇒ ★⊑★ ★⊑★))
        genI-ty (⇒⊑⇒ (X⊑★ here) (X⊑★ here)))
      tag₀-ty (⇒⊑⇒ X⊑X X⊑X)

  r2c-post : W4 ∣ [] ⊢ L2c₂ ⊑ R2c₅ ∶ ∀id⊑★ W4
  r2c-post = outer merged-body bOut₅

  -- the final pair (left state 3, right state 6): DGG part 1's witness
  r2c-final : W4 ∣ [] ⊢ V2 ⊑ R2c₆ ∶ ∀id⊑★ W4
  r2c-final = instB merged-body bOut₅
