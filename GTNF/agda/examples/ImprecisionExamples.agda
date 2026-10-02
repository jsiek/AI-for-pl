module examples.ImprecisionExamples where

-- File Charter:
--   * PAIRS OF PROGRAMS FOR DESIGNING A CAST-TERM IMPRECISION (design.md
--     §9.6–§9.7).  In each pair `Lᵢ` is the MORE precise program and
--     `Rᵢ` the LESS precise one; their sources are related by GTSFImp's
--     source term imprecision.  Each is hand-compiled as Examples.agda
--     does (identity casts dropped; a cast at top level carries `[]`,
--     under one Λ `μX`), typed by `tc`, and run by one
--     `Reaches k n ⊢M V` proved by `refl`.  Programs that are design.md
--     examples are Examples' `ex1`, `ex2`, `ex4`, `ex6`, not copies.
--   * THE PAIRS (source; L ⊑ R):
--       P1 aligned instantiation, reps ℕ ⊑ ★
--          L (ΛX.λx:X.x)[ℕ] 5          R (ΛX.λx:X.x)[★] 5
--       P2 left-only Λ and instantiation
--          L as P1                     R (λx:★.x) 5
--       P3 right-only implicit instantiation
--          L (λf:∀X.X→X. f[ℕ] 5)(ΛX.λx:X.x)   R design Example 1
--       P4 right-only implicit generalization
--          L as P3                     R design Example 2
--       P5 the left blames on an escaped tag
--          L design Example 4          R (λn:ℕ.n)((λx:★.(λz:★.z) x) 5)
--       P6 a ∀-cast on the right, conversions of different shape
--          L (λg:∀X.X→ℕ. g[𝔹] true)(ΛX.λx:X.7)   R design Example 6
--   * THE RUNS (k = fuel, n = steps; rules as `evalRules` reports them):
--       L1   10  5  5          TyBeta Wrap Beta Merge Id
--       R1   11  6  5⟨ℕ!⟩      TyBeta Wrap Beta Merge IdDyn Id
--       L2 = L1
--       R2    6  1  5⟨ℕ!⟩      Beta
--       L3   11  6  5          Beta TyBeta Wrap Beta Merge Id
--       R3 = ex1  16 11  5⟨ℕ!⟩ Inst TyBeta Beta CastFun CastId Wrap Beta
--                              Merge IdDyn Id CastId
--       L4 = L3
--       R4 = ex2  17 12  5     Beta TyBeta Wrap CastFun Wrap Beta Merge
--                              IdDyn Merge TagUntag Merge Id
--       L5 = ex4  11  6  blame ℓ   TyBeta Wrap Beta Beta TagUntagBad-⟪⟫
--                              Blame
--       R5    9  4  5          Beta Beta TagUntag Beta
--       L6   10  5  7          Beta TyBeta Wrap Beta Id
--       R6 = ex6  13  8  7⟨ℕ!⟩ Beta TyBeta Wrap CastFun CastId Beta IdDyn
--                              Id
--     The `-rules` equations pin the rule sequences of the six new runs.
--   * Rendered traces: scripts/render_gtnf.sh 'showRun 10 L1-⊢'
--     'open import ImprecisionExamples'.
--   * Labels: ℓ = 0 (from Examples).

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import Ctx
open import Conversion
open import Coercion
open import Terms
open import examples.TypeCheck using (tc)
open import examples.Eval
open import examples.Examples
  using (ℓ; ex1; ex1-⊢; ex1-run; ex2; ex2-⊢; ex2-run; ex4; ex4-⊢; ex4-run;
         ex6; ex6-⊢; ex6-run)

------------------------------------------------------------------------
-- The programs
------------------------------------------------------------------------

-- P1
L1 R1 : Term
L1 = (ν `ℕ · Λ (ƛ (` 0) ∙ ` 0) ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · $ 5
R1 = (ν ★ · Λ (ƛ (` 0) ∙ ` 0) ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩)
   · ($ 5 ⟨ [] ∣ `ℕ ! ⟩)

L1-⊢ : empty ∣ [] ⊢ L1 ⦂ `ℕ
L1-⊢ = tc

R1-⊢ : empty ∣ [] ⊢ R1 ⦂ ★
R1-⊢ = tc

-- P2
L2 R2 : Term
L2 = L1
R2 = (ƛ ★ ∙ ` 0) · ($ 5 ⟨ [] ∣ `ℕ ! ⟩)

L2-⊢ : empty ∣ [] ⊢ L2 ⦂ `ℕ
L2-⊢ = L1-⊢

R2-⊢ : empty ∣ [] ⊢ R2 ⦂ ★
R2-⊢ = tc

-- P3
L3 R3 : Term
L3 = (ƛ (`∀ (` 0 ⇒ ` 0)) ∙ ((ν `ℕ · ` 0 ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · $ 5))
   · Λ (ƛ (` 0) ∙ ` 0)
R3 = ex1

L3-⊢ : empty ∣ [] ⊢ L3 ⦂ `ℕ
L3-⊢ = tc

R3-⊢ : empty ∣ [] ⊢ R3 ⦂ ★
R3-⊢ = ex1-⊢

-- P4
L4 R4 : Term
L4 = L3
R4 = ex2

L4-⊢ : empty ∣ [] ⊢ L4 ⦂ `ℕ
L4-⊢ = L3-⊢

R4-⊢ : empty ∣ [] ⊢ R4 ⦂ `ℕ
R4-⊢ = ex2-⊢

-- P5
L5 R5 : Term
L5 = ex4
R5 = (ƛ `ℕ ∙ ` 0)
   · (((ƛ ★ ∙ ((ƛ ★ ∙ ` 0) · ` 0)) · ($ 5 ⟨ [] ∣ `ℕ ! ⟩)) ⟨ [] ∣ `ℕ ？ ℓ ⟩)

L5-⊢ : empty ∣ [] ⊢ L5 ⦂ `ℕ
L5-⊢ = ex4-⊢

R5-⊢ : empty ∣ [] ⊢ R5 ⦂ `ℕ
R5-⊢ = tc

-- P6
L6 R6 : Term
L6 = (ƛ (`∀ (` 0 ⇒ `ℕ)) ∙ ((ν `𝔹 · ` 0 ⟨ reveal 0 (` 0 ⇒ `ℕ) ⟩) · `true))
   · (Λ (ƛ (` 0) ∙ $ 7))
R6 = ex6

L6-⊢ : empty ∣ [] ⊢ L6 ⦂ `ℕ
L6-⊢ = tc

R6-⊢ : empty ∣ [] ⊢ R6 ⦂ ★
R6-⊢ = ex6-⊢

------------------------------------------------------------------------
-- The runs
------------------------------------------------------------------------

L1-run : Reaches 10 5 L1-⊢ ($ 5)
L1-run = reaches refl (ans-value (V-simple S-$))

R1-run : Reaches 11 6 R1-⊢ ($ 5 ⟨ [] ∣ `ℕ ! ⟩)
R1-run = reaches refl (ans-value (V-simple (S-cast (V-simple S-$) I-tag)))

L2-run : Reaches 10 5 L2-⊢ ($ 5)
L2-run = L1-run

R2-run : Reaches 6 1 R2-⊢ ($ 5 ⟨ [] ∣ `ℕ ! ⟩)
R2-run = reaches refl (ans-value (V-simple (S-cast (V-simple S-$) I-tag)))

L3-run : Reaches 11 6 L3-⊢ ($ 5)
L3-run = reaches refl (ans-value (V-simple S-$))

R3-run : Reaches 16 11 R3-⊢ ($ 5 ⟨ [] ∣ `ℕ ! ⟩)
R3-run = ex1-run

L4-run : Reaches 11 6 L4-⊢ ($ 5)
L4-run = L3-run

R4-run : Reaches 17 12 R4-⊢ ($ 5)
R4-run = ex2-run

L5-run : Reaches 11 6 L5-⊢ (blame ℓ)
L5-run = ex4-run

R5-run : Reaches 9 4 R5-⊢ ($ 5)
R5-run = reaches refl (ans-value (V-simple S-$))

L6-run : Reaches 10 5 L6-⊢ ($ 7)
L6-run = reaches refl (ans-value (V-simple S-$))

R6-run : Reaches 13 8 R6-⊢ ($ 7 ⟨ [] ∣ `ℕ ! ⟩)
R6-run = ex6-run

------------------------------------------------------------------------
-- The rule sequences of the new runs
------------------------------------------------------------------------

L1-rules : evalRules 10 L1-⊢ ≡ "TyBeta" ∷ "Wrap" ∷ "Beta" ∷ "Merge" ∷ "Id" ∷ []
L1-rules = refl

R1-rules : evalRules 11 R1-⊢
  ≡ "TyBeta" ∷ "Wrap" ∷ "Beta" ∷ "Merge" ∷ "IdDyn" ∷ "Id" ∷ []
R1-rules = refl

R2-rules : evalRules 6 R2-⊢ ≡ "Beta" ∷ []
R2-rules = refl

L3-rules : evalRules 11 L3-⊢
  ≡ "Beta" ∷ "TyBeta" ∷ "Wrap" ∷ "Beta" ∷ "Merge" ∷ "Id" ∷ []
L3-rules = refl

R5-rules : evalRules 9 R5-⊢ ≡ "Beta" ∷ "Beta" ∷ "TagUntag" ∷ "Beta" ∷ []
R5-rules = refl

L6-rules : evalRules 10 L6-⊢
  ≡ "Beta" ∷ "TyBeta" ∷ "Wrap" ∷ "Beta" ∷ "Id" ∷ []
L6-rules = refl
