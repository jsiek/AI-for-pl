module Examples where

-- File Charter:
--   * THE EXAMPLES OF GTNF/design.md §8, hand-compiled per §7 into the
--     cast calculus, each with its typing derivation (`tc`, from
--     TypeCheck) and ONE `Reaches k n ⊢M V` proved by `refl`: with fuel
--     k the evaluator reaches the answer V (a value or blame) in exactly
--     n steps, and every state along the run type-checks (Eval §10).
--   * COMPILATION CHOICES.  Identity casts `⟨id(A)⟩` that compilation
--     puts on arguments whose types already agree are DROPPED, as the
--     traces of design.md §8 drop them.  Every cast carries the
--     environment compilation writes: every name in scope at `★∼X∼★`
--     (`[]` at top level, `μX` under one Λ, `μXY` under two).
--   * THE RUNS (k = fuel, n = steps; rules as `evalRules` reports them):
--       ex1  11  5⟨ℕ!⟩      Inst TyBeta Beta CastFun CastId Wrap Beta
--                           Merge IdDyn Id CastId          (= design.md)
--       ex2   8  5          Beta TyBeta Wrap CastFun Beta TagUntag
--                           Merge Id                       (= design.md)
--       ex3   9  blame ℓ′   … TagUntagBad Blame Blame Blame (= design.md)
--       ex4   6  blame ℓ    TyBeta Wrap Beta Beta TagUntagBad-⟪⟫ Blame
--       ex5  21  5          the full program; the k a call goes Wrap
--                           Merge IdDyn(-var) as in design.md
--       ex6   8  7⟨ℕ!⟩      Beta TyBeta Wrap CastFun CastId Beta IdDyn
--                           Id                             (= design.md)
--       d8   11  blame ℓ    D8's alias: … TagUntagBad-⟪⟫ Blame Blame
--     and four coverage runs: cov1 (CastSeq, TagUntag), cov2
--     (BlameBotIntro, Blame-ν), cov3 (TagUntagBad, Blame-·₁), cov4
--     (TyBeta's boundary case `inst-⟪⟫`, νF's old TyWrap).
--   * Labels: ℓ = 0, ℓ′ = 1.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import TermSubst
open import Reduction
open import TypeCheck using (tc; infer; check⊢)
open import Eval

ℓ ℓ′ : Label
ℓ = 0
ℓ′ = 1

ex1 : Term
ex1 = (ƛ (★ ⇒ ★) ∙ (` 0 · ($ 5 ⟨ [] ∣ `ℕ ! ⟩)))
    · (Λ (ƛ (` 0) ∙ ` 0) ⟨ [] ∣ instᵖ (((` 0) ？ ℓ) ↦ᵖ ((` 0) !)) ⟩)

ex1-⊢ : empty ∣ [] ⊢ ex1 ⦂ ★
ex1-⊢ = tc

μX : ModeEnv
μX = ★∼X∼★ ∷ []

ex2 : Term
ex2 = (ƛ (`∀ (` 0 ⇒ ` 0)) ∙ ((ν `ℕ · ` 0 ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · $ 5))
    · ((ƛ ★ ∙ ` 0) ⟨ [] ∣ genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ ℓ)) ⟩)

ex2-⊢ : empty ∣ [] ⊢ ex2 ⦂ `ℕ
ex2-⊢ = tc

ex3 : Term
ex3 = (ƛ (`∀ (` 0 ⇒ ` 0)) ∙ ((ν `ℕ · ` 0 ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · $ 5))
    · ((ƛ ★ ∙ ((ƛ `ℕ ∙ ` 1) · (` 0 ⟨ [] ∣ `ℕ ？ ℓ′ ⟩)))
         ⟨ [] ∣ genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ ℓ)) ⟩)

ex3-⊢ : empty ∣ [] ⊢ ex3 ⦂ `ℕ
ex3-⊢ = tc

ex4-inner : Term
ex4-inner =
  ν `ℕ · Λ (ƛ (` 0) ∙ ((ƛ ★ ∙ ` 0) · (` 0 ⟨ μX ∣ (` 0) ! ⟩)))
    ⟨ reveal 0 (` 0 ⇒ ★) ⟩

ex4 : Term
ex4 = (ƛ `ℕ ∙ ` 0) · ((ex4-inner · $ 5) ⟨ [] ∣ `ℕ ？ ℓ ⟩)

ex4-⊢ : empty ∣ [] ⊢ ex4 ⦂ `ℕ
ex4-⊢ = tc

F5 C5 : _
C5 = ` 0 ⇒ ((★ ⇒ ((★ ⇒ ` 0) ⇒ ` 0)) ⇒ ` 0)
F5 = Λ (ƛ (` 0) ∙ ƛ (★ ⇒ ((★ ⇒ ` 0) ⇒ ` 0)) ∙
       ((` 0 · ((ƛ ★ ∙ ` 0) · (` 1 ⟨ μX ∣ (` 0) ! ⟩)))
        · (ƛ ★ ∙ ((ƛ (` 0) ∙ ` 0) · (` 0 ⟨ μX ∣ (` 0) ？ ℓ ⟩)))))

ex5 : Term
ex5 = ((ν `ℕ · F5 ⟨ reveal 0 C5 ⟩) · $ 5)
    · (ƛ ★ ∙ ƛ (★ ⇒ `ℕ) ∙ (` 0 · ` 1))

ex5-⊢ : empty ∣ [] ⊢ ex5 ⦂ `ℕ
ex5-⊢ = tc

ex6 : Term
ex6 = (ƛ (`∀ (` 0 ⇒ ★)) ∙ ((ν `𝔹 · ` 0 ⟨ reveal 0 (` 0 ⇒ ★) ⟩) · `true))
    · (Λ (ƛ (` 0) ∙ $ 7) ⟨ [] ∣ ∀ᵖ (idᵖ (` 0) ↦ᵖ (`ℕ !)) ⟩)

ex6-⊢ : empty ∣ [] ⊢ ex6 ⦂ ★
ex6-⊢ = tc

-- f sits under the outer Λ, so its cast's environment has two names
μXY : ModeEnv
μXY = ★∼X∼★ ∷ ★∼X∼★ ∷ []

f8 : Term
f8 = Λ (ƛ (` 0) ∙ ((ƛ ★ ∙ ` 0) · (` 0 ⟨ μXY ∣ (` 0) ! ⟩)))

d8 : Term
d8 = (ν `ℕ · Λ (ƛ (` 0) ∙ ((ƛ (` 0) ∙ ` 0)
        · (((ν (` 0) · f8 ⟨ reveal 0 (` 0 ⇒ ★) ⟩) · ` 0)
             ⟨ μX ∣ (` 0) ？ ℓ ⟩)))
       ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · $ 5

d8-⊢ : empty ∣ [] ⊢ d8 ⦂ `ℕ
d8-⊢ = tc


cov1 cov2 cov3 cov4 : Term
cov1 = ($ 5 ⟨ [] ∣ `ℕ ! ︔ `ℕ ？ ℓ ⟩)
cov2 = ν `ℕ · (Λ ($ 5 ⟨ μX ∣ `ℕ ! ⟩) ⟨ [] ∣ bot-intro ℓ ⟩) ⟨ reveal 0 (` 0) ⟩
cov3 = ($ 5 ⟨ [] ∣ `ℕ ! ⟩ ⟨ [] ∣ (★ ⇒ ★) ？ ℓ ⟩) · ($ 1 ⟨ [] ∣ `ℕ ! ⟩)
cov4 = (ν `𝔹 · (ν `ℕ · Λ (Λ (ƛ (` 0) ∙ ` 0))
          ⟨ reveal 0 (`∀ (` 0 ⇒ ` 0)) ⟩) ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩)
       · `true
cov1-⊢ : empty ∣ [] ⊢ cov1 ⦂ `ℕ
cov1-⊢ = tc
cov2-⊢ : empty ∣ [] ⊢ cov2 ⦂ `ℕ
cov2-⊢ = tc
cov3-⊢ : empty ∣ [] ⊢ cov3 ⦂ ★
cov3-⊢ = tc
cov4-⊢ : empty ∣ [] ⊢ cov4 ⦂ `𝔹
cov4-⊢ = tc

------------------------------------------------------------------------
-- The runs
------------------------------------------------------------------------

ex1-run : Reaches 16 11 ex1-⊢ ($ 5 ⟨ [] ∣ `ℕ ! ⟩)
ex1-run = reaches refl (ans-value (V-simple (S-cast (V-simple S-$) I-tag)))

ex2-run : Reaches 13 8 ex2-⊢ ($ 5)
ex2-run = reaches refl (ans-value (V-simple S-$))

ex3-run : Reaches 14 9 ex3-⊢ (blame ℓ′)
ex3-run = reaches refl (ans-blame)

ex4-run : Reaches 11 6 ex4-⊢ (blame ℓ)
ex4-run = reaches refl (ans-blame)

ex5-run : Reaches 26 21 ex5-⊢ ($ 5)
ex5-run = reaches refl (ans-value (V-simple S-$))

ex6-run : Reaches 13 8 ex6-⊢ ($ 7 ⟨ [] ∣ `ℕ ! ⟩)
ex6-run = reaches refl (ans-value (V-simple (S-cast (V-simple S-$) I-tag)))

d8-run : Reaches 16 11 d8-⊢ (blame ℓ)
d8-run = reaches refl (ans-blame)

cov1-run : Reaches 7 2 cov1-⊢ ($ 5)
cov1-run = reaches refl (ans-value (V-simple S-$))

cov2-run : Reaches 7 2 cov2-⊢ (blame ℓ)
cov2-run = reaches refl (ans-blame)

cov3-run : Reaches 7 2 cov3-⊢ (blame ℓ)
cov3-run = reaches refl (ans-blame)

cov4-run : Reaches 12 7 cov4-⊢ `true
cov4-run = reaches refl (ans-value (V-simple S-true))
