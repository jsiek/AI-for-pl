module CambridgeExamples where

-- File Charter:
--   * THE TERM-IMPRECISION EXAMPLES OF papers/cambridge26.lagda.md
--     (Siek, Thiemann, Wadler; "EXAMPLES", lines ~1218-2450, and the
--     pairs among the notes before it), translated to GTNF.  Each pair
--     is `Cx-L` (MORE precise) and `Cx-R` (LESS precise): the notes'
--     `M ⊒ M′` is `Cx-R ⊒ Cx-L`.  Each program is closed, typed by
--     `tc`, and run by one `Reaches k n ⊢M V` proved by `refl`.
--   * TRANSLATION.  ι = ℕ, κ = 5 (or 42, 69), c★ = n⟨ℕ!⟩^[]; ι′ = 𝔹.
--     να.α!→α? is `genI`; ν̅α.α♯→α♭ is `instI` = inst X.(X?ℓ→X!): the
--     seals of the notes' ν̅ body become Inst's `reveal` conversion,
--     and the coercion keeps the tags (closed at ★ by Inst).  A bare
--     function value is applied (`I`, `I★⟨gen⟩` at [ℕ] 5; a ★→★ to 5★),
--     so every pair is a pair of runs.  Every cast is at top level, `[]`.
--   * THE PAIRS (notes' name, line; what it tests), and the runs
--     (n steps; rules as `evalRules` reports them):
--     Cf   (f) 1246, Ex 7 1457, Ex 15 2049: gen on the right only
--          L  5     5   TyBeta Wrap Beta Merge Id          (= L1)
--          R  5    11   TyBeta Wrap CastFun Wrap Beta Merge IdDyn
--                       Merge TagUntag Merge Id
--     Cg   (g) 1250, Ex 1 1274, Ex 20 2308, the note at line 1; R is (d):
--          gen then inst on the right only
--          L  5     5   (= L1)
--          R  5★   16   Inst TyBeta CastFun CastId Wrap CastFun Wrap
--                       Beta Merge IdDyn Merge TagUntag Merge IdDyn Id
--                       CastId
--     Ch   (h) 1259, Ex 4 1348, Ex 11 1623, F_G pair 1047: inst on the
--          right only
--          L  5     5   (= L1)
--          R  5★   10   Inst TyBeta CastFun CastId Wrap Beta Merge
--                       IdDyn Id CastId
--     Ce   (e) 1242, Ex 3 1337, Ex 9 1552: I★ ⊒ I (= P2)
--          L  5     5;  R  5★  1   Beta
--     C2   Ex 2 1311, Ex 21 2345: gen on both, inst on the right
--          L = Cf-R  5  11;  R = Cg-R  5★  16
--     C5   Ex 5 1380: the more precise side's ι? fails on a 𝔹
--          L  blame 4   CastFun TagUntagBad Blame Blame
--          R  true★ 1   Beta
--     C6   Ex 6 1400: as C5, under a ν
--          L  blame 5   TyBeta CastFun TagUntagBad Blame Blame
--          R  true★ 1   (= C5-R)
--     C8   Ex 8 1489: I[★] c★ ⊒ I[ι] c (= P1)
--          L  5     5;  R  5★  6
--     C10  Ex 10 1596: inst on the more precise side only
--          L  5★   10   (= Ch-R);  R  5★  1  (= R2)
--     C12  Ex 12 1658: inst;gen on the right
--          L  5     5   (= L1)
--          R  5    19   Inst TyBeta TyBeta Wrap CastFun Wrap CastFun
--                       CastId Wrap Merge Beta Merge CastId Merge IdDyn
--                       Merge TagUntag Merge Id
--     C13  Ex 13 1831: inst;gen;inst on the right
--          L  5     5;  R  5★  24  Inst TyBeta Inst TyBeta CastFun
--                       CastId Wrap CastFun Wrap CastFun CastId Wrap
--                       Merge Beta Merge CastId Merge IdDyn Merge
--                       TagUntag Merge IdDyn Id CastId
--     C14  Ex 14 1935: inst;gen;inst;gen on the right
--          L  5     5;  R  5   33  Inst TyBeta Inst TyBeta TyBeta Wrap
--                       CastFun Wrap CastFun CastId Wrap Merge CastFun
--                       Wrap CastFun CastId Wrap Merge Beta Merge CastId
--                       Merge IdDyn Merge TagUntag Merge CastId Merge
--                       IdDyn Merge TagUntag Merge Id
--     C16  Ex 16 2074: gen on the more precise side only
--          L  5    11   (= Cf-R);  R  5★  1  (= R2)
--     C16b Ex 16b 2102: gen;inst on the more precise side only
--          L  5★   16   (= Cg-R);  R  5★  1  (= R2)
--     C17  Ex 17 2121: K★ 42★ 69★ ⊒ K ι ι 42 69, two allocations
--          L  42    9   TyBeta TyBeta Merge Wrap Beta Wrap Beta Merge
--                       Id
--          R  42★   2   Beta Beta
--     C18  Ex 18 2179: K ⟨inst X. inst Y. (X?→Y?→X!)⟩ on the right
--          L  42    9   (= C17-L)
--          R  42★  17   Inst TyBeta Inst TyBeta Merge CastFun CastId
--                       Wrap Beta CastFun CastId Wrap Beta Merge IdDyn
--                       Id CastId
--     C18b Ex 18b 2223: K★ ⟨gen X. gen Y. (X!→Y!→X?)⟩ [ℕ][ℕ] on the
--          right (the notes write the sides the other way round)
--          L  42    9   (= C17-L)
--          R  42   18   TyBeta TyBeta Merge Merge Wrap CastFun Wrap Beta
--                       Wrap CastFun Wrap Beta Merge IdDyn Merge TagUntag
--                       Merge Id
--     C19  Ex 19 2231: rebinding, ν Y:=X inside a Λ on the left
--          L  5    10   TyBeta Wrap Beta TyBeta Wrap Merge Beta Merge
--                       Merge Id
--          R  5★    2   Beta Beta
--     C22  Ex 22 2391: reflexivity, L = R = L1;  5  5
--     C23a Ex 23 2414 (constructed; the upcast along its first
--          imprecision): K ⟨inst X. ∀Y. (X?→id(Y)→X!)⟩
--          L  42    9   (= C17-L)
--          R  42★  22   Inst TyBeta TyBeta Wrap IdDyn Id CastFun CastId
--                       Wrap Beta Wrap CastFun CastId Wrap Merge Beta
--                       Merge IdDyn Id CastId IdDyn Id
--     C23b Ex 23 2415 (constructed; the upcast along its second):
--          K ⟨∀X. inst Y. (id(X)→Y?→id(X))⟩
--          L  42    9   (= C17-L)
--          R  42   20   TyBeta Inst TyBeta Wrap CastFun CastId Wrap Merge
--                       Beta Wrap IdDyn Id CastFun CastId Wrap Beta Merge
--                       CastId Merge Id
--     CJ   the DGG counterexample at lines 72/81, fixed form (the check
--          (★→★)? before the gen; the unfixed gen X.((★→★)?; …) is
--          ill typed in GTNF: GenSafe, and gen's A ≠ ★)
--          L  blame 4   CastSeq TagUntagBad Blame Blame
--          R  blame 2   TagUntagBad Blame
--   * NOT TRANSLATED: (a)–(d) are single programs (they are the sides
--     of Ex 15, Cg and C16b); Ex 23 has no programs (C23a/b are
--     constructed); the notes' other counterexamples are single terms
--     with seals inside coercions.
--   * Rendered traces: scripts/render_gtnf.sh 'showRun 16 Cf-R-⊢'
--     'open import CambridgeExamples'.
--   * Labels: ℓ = 0 (from Examples).

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import Ctx
open import Conversion
open import Coercion
open import Terms
open import TypeCheck using (tc)
open import Eval
open import Examples using (ℓ; ex1; ex1-⊢; ex1-run)
open import ImprecisionExamples
  using (L1; L1-⊢; L1-run; R1; R1-⊢; R1-run; R2; R2-⊢; R2-run)

------------------------------------------------------------------------
-- Building blocks
------------------------------------------------------------------------

-- I★ = λx:★.x,  I = ΛX.λx:X.x,  K★ = λx:★.λy:★.x,  K = ΛX.ΛY.λx:X.λy:Y.x
I★ I K★ K : Term
I★ = ƛ ★ ∙ ` 0
I  = Λ (ƛ (` 0) ∙ ` 0)
K★ = ƛ ★ ∙ (ƛ ★ ∙ ` 1)
K  = Λ (Λ (ƛ (` 1) ∙ (ƛ (` 0) ∙ ` 1)))

-- να.α!→α?  and  ν̅α.α♯→α♭  (GTNF: gen X.(X!→X?ℓ), inst X.(X?ℓ→X!))
genI instI : Coercion
genI  = genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ ℓ))
instI = instᵖ (((` 0) ？ ℓ) ↦ᵖ ((` 0) !))

-- the injected constants  n★ = n⟨ℕ!⟩^[]  and  true★ = true⟨𝔹!⟩^[]
dyn : ℕ → Term
dyn n = $ n ⟨ [] ∣ `ℕ ! ⟩

true★ : Term
true★ = `true ⟨ [] ∣ `𝔹 ! ⟩

-- M [ℕ] 5, for M : ∀X.X→X
at-ℕ-5 : Term → Term
at-ℕ-5 M = (ν `ℕ · M ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · $ 5

-- M [ℕ] [ℕ] 42 69, for M : ∀X.∀Y.X→Y→X
KC : Ty
KC = `∀ (` 1 ⇒ (` 0 ⇒ ` 1))

at-ℕℕ-42-69 : Term → Term
at-ℕℕ-42-69 M =
  ((ν `ℕ · (ν `ℕ · M ⟨ reveal 0 KC ⟩) ⟨ reveal 0 (`ℕ ⇒ (` 0 ⇒ `ℕ)) ⟩)
    · $ 42) · $ 69

------------------------------------------------------------------------
-- The pairs (L = more precise, R = less precise)
------------------------------------------------------------------------

-- Cf: (f), Example 7, Example 15
Cf-L Cf-R : Term
Cf-L = L1
Cf-R = at-ℕ-5 (I★ ⟨ [] ∣ genI ⟩)

Cf-L-⊢ : empty ∣ [] ⊢ Cf-L ⦂ `ℕ
Cf-L-⊢ = L1-⊢
Cf-R-⊢ : empty ∣ [] ⊢ Cf-R ⦂ `ℕ
Cf-R-⊢ = tc

-- Cg: (g), Example 1, Example 20, the opening note; R is (d)
Cg-L Cg-R : Term
Cg-L = L1
Cg-R = (I★ ⟨ [] ∣ genI ⟩ ⟨ [] ∣ instI ⟩) · (dyn 5)

Cg-L-⊢ : empty ∣ [] ⊢ Cg-L ⦂ `ℕ
Cg-L-⊢ = L1-⊢
Cg-R-⊢ : empty ∣ [] ⊢ Cg-R ⦂ ★
Cg-R-⊢ = tc

-- Ch: (h), Example 4, Example 11, the F_G pair
Ch-L Ch-R : Term
Ch-L = L1
Ch-R = (I ⟨ [] ∣ instI ⟩) · (dyn 5)

Ch-L-⊢ : empty ∣ [] ⊢ Ch-L ⦂ `ℕ
Ch-L-⊢ = L1-⊢
Ch-R-⊢ : empty ∣ [] ⊢ Ch-R ⦂ ★
Ch-R-⊢ = tc

-- C2: Example 2, Example 21
C2-L C2-R : Term
C2-L = Cf-R
C2-R = Cg-R

C2-L-⊢ : empty ∣ [] ⊢ C2-L ⦂ `ℕ
C2-L-⊢ = Cf-R-⊢
C2-R-⊢ : empty ∣ [] ⊢ C2-R ⦂ ★
C2-R-⊢ = Cg-R-⊢

-- C5: Example 5
C5-L C5-R : Term
C5-L = ((ƛ `ℕ ∙ ` 0) ⟨ [] ∣ (`ℕ ？ ℓ) ↦ᵖ (`ℕ !) ⟩) · true★
C5-R = I★ · true★

C5-L-⊢ : empty ∣ [] ⊢ C5-L ⦂ ★
C5-L-⊢ = tc
C5-R-⊢ : empty ∣ [] ⊢ C5-R ⦂ ★
C5-R-⊢ = tc

-- C6: Example 6
C6-L C6-R : Term
C6-L = ((ν `ℕ · I ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) ⟨ [] ∣ (`ℕ ？ ℓ) ↦ᵖ (`ℕ !) ⟩)
     · true★
C6-R = C5-R

C6-L-⊢ : empty ∣ [] ⊢ C6-L ⦂ ★
C6-L-⊢ = tc
C6-R-⊢ : empty ∣ [] ⊢ C6-R ⦂ ★
C6-R-⊢ = C5-R-⊢

-- C10: Example 10
C10-L C10-R : Term
C10-L = Ch-R
C10-R = R2

C10-L-⊢ : empty ∣ [] ⊢ C10-L ⦂ ★
C10-L-⊢ = Ch-R-⊢
C10-R-⊢ : empty ∣ [] ⊢ C10-R ⦂ ★
C10-R-⊢ = R2-⊢

-- C12: Example 12
C12-L C12-R : Term
C12-L = L1
C12-R = at-ℕ-5 (I ⟨ [] ∣ instI ⟩ ⟨ [] ∣ genI ⟩)

C12-L-⊢ : empty ∣ [] ⊢ C12-L ⦂ `ℕ
C12-L-⊢ = L1-⊢
C12-R-⊢ : empty ∣ [] ⊢ C12-R ⦂ `ℕ
C12-R-⊢ = tc

-- C13: Example 13
C13-L C13-R : Term
C13-L = L1
C13-R = (I ⟨ [] ∣ instI ⟩ ⟨ [] ∣ genI ⟩ ⟨ [] ∣ instI ⟩) · (dyn 5)

C13-L-⊢ : empty ∣ [] ⊢ C13-L ⦂ `ℕ
C13-L-⊢ = L1-⊢
C13-R-⊢ : empty ∣ [] ⊢ C13-R ⦂ ★
C13-R-⊢ = tc

-- C14: Example 14
C14-L C14-R : Term
C14-L = L1
C14-R = at-ℕ-5
  (I ⟨ [] ∣ instI ⟩ ⟨ [] ∣ genI ⟩ ⟨ [] ∣ instI ⟩ ⟨ [] ∣ genI ⟩)

C14-L-⊢ : empty ∣ [] ⊢ C14-L ⦂ `ℕ
C14-L-⊢ = L1-⊢
C14-R-⊢ : empty ∣ [] ⊢ C14-R ⦂ `ℕ
C14-R-⊢ = tc

-- C16: Example 16
C16-L C16-R : Term
C16-L = Cf-R
C16-R = R2

C16-L-⊢ : empty ∣ [] ⊢ C16-L ⦂ `ℕ
C16-L-⊢ = Cf-R-⊢
C16-R-⊢ : empty ∣ [] ⊢ C16-R ⦂ ★
C16-R-⊢ = R2-⊢

-- C16b: Example 16b
C16b-L C16b-R : Term
C16b-L = Cg-R
C16b-R = R2

C16b-L-⊢ : empty ∣ [] ⊢ C16b-L ⦂ ★
C16b-L-⊢ = Cg-R-⊢
C16b-R-⊢ : empty ∣ [] ⊢ C16b-R ⦂ ★
C16b-R-⊢ = R2-⊢

-- C17: Example 17
C17-L C17-R : Term
C17-L = at-ℕℕ-42-69 K
C17-R = (K★ · (dyn 42)) · (dyn 69)

C17-L-⊢ : empty ∣ [] ⊢ C17-L ⦂ `ℕ
C17-L-⊢ = tc
C17-R-⊢ : empty ∣ [] ⊢ C17-R ⦂ ★
C17-R-⊢ = tc

-- C18: Example 18
instK : Coercion
instK = instᵖ (instᵖ (((` 1) ？ ℓ) ↦ᵖ (((` 0) ？ ℓ) ↦ᵖ ((` 1) !))))

C18-L C18-R : Term
C18-L = C17-L
C18-R = ((K ⟨ [] ∣ instK ⟩) · (dyn 42)) · (dyn 69)

C18-L-⊢ : empty ∣ [] ⊢ C18-L ⦂ `ℕ
C18-L-⊢ = C17-L-⊢
C18-R-⊢ : empty ∣ [] ⊢ C18-R ⦂ ★
C18-R-⊢ = tc

-- C18b: Example 18b
genK : Coercion
genK = genᵖ (genᵖ (((` 1) !) ↦ᵖ (((` 0) !) ↦ᵖ ((` 1) ？ ℓ))))

C18b-L C18b-R : Term
C18b-L = C17-L
C18b-R = at-ℕℕ-42-69 (K★ ⟨ [] ∣ genK ⟩)

C18b-L-⊢ : empty ∣ [] ⊢ C18b-L ⦂ `ℕ
C18b-L-⊢ = C17-L-⊢
C18b-R-⊢ : empty ∣ [] ⊢ C18b-R ⦂ `ℕ
C18b-R-⊢ = tc

-- C19: Example 19
C19-L C19-R : Term
C19-L = at-ℕ-5
  (Λ (ƛ (` 0) ∙ ((ν (` 0) · I ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · ` 0)))
C19-R = (ƛ ★ ∙ (I★ · ` 0)) · (dyn 5)

C19-L-⊢ : empty ∣ [] ⊢ C19-L ⦂ `ℕ
C19-L-⊢ = tc
C19-R-⊢ : empty ∣ [] ⊢ C19-R ⦂ ★
C19-R-⊢ = tc

-- C23a, C23b: Example 23's two type imprecisions, as casts on K
inst∀K ∀instK : Coercion
inst∀K = instᵖ (∀ᵖ (((` 1) ？ ℓ) ↦ᵖ (idᵖ (` 0) ↦ᵖ ((` 1) !))))
∀instK = ∀ᵖ (instᵖ (idᵖ (` 1) ↦ᵖ (((` 0) ？ ℓ) ↦ᵖ idᵖ (` 1))))

C23a-L C23a-R C23b-L C23b-R : Term
C23a-L = C17-L
C23a-R = ((ν `ℕ · K ⟨ [] ∣ inst∀K ⟩ ⟨ reveal 0 (★ ⇒ (` 0 ⇒ ★)) ⟩)
           · (dyn 42)) · $ 69
C23b-L = C17-L
C23b-R = ((ν `ℕ · K ⟨ [] ∣ ∀instK ⟩ ⟨ reveal 0 (` 0 ⇒ (★ ⇒ ` 0)) ⟩)
           · $ 42) · (dyn 69)

C23a-L-⊢ : empty ∣ [] ⊢ C23a-L ⦂ `ℕ
C23a-L-⊢ = C17-L-⊢
C23a-R-⊢ : empty ∣ [] ⊢ C23a-R ⦂ ★
C23a-R-⊢ = tc
C23b-L-⊢ : empty ∣ [] ⊢ C23b-L ⦂ `ℕ
C23b-L-⊢ = C17-L-⊢
C23b-R-⊢ : empty ∣ [] ⊢ C23b-R ⦂ `ℕ
C23b-R-⊢ = tc

-- CJ: the counterexample to the DGG at the top of the notes, with the
-- projection outside the ν (the version GTNF can type)
CJ-L CJ-R : Term
CJ-L = (ƛ (`∀ (` 0 ⇒ ` 0)) ∙ ` 0)
     · ((dyn 0) ⟨ [] ∣ ((★ ⇒ ★) ？ ℓ) ︔ genI ⟩)
CJ-R = (ƛ (★ ⇒ ★) ∙ ` 0) · ((dyn 0) ⟨ [] ∣ (★ ⇒ ★) ？ ℓ ⟩)

CJ-L-⊢ : empty ∣ [] ⊢ CJ-L ⦂ `∀ (` 0 ⇒ ` 0)
CJ-L-⊢ = tc
CJ-R-⊢ : empty ∣ [] ⊢ CJ-R ⦂ (★ ⇒ ★)
CJ-R-⊢ = tc

-- Ce: (e), Example 3, Example 9  (= ImprecisionExamples P2)
-- C8: Example 8                  (= ImprecisionExamples P1)
-- C22: Example 22, reflexivity   (L = R)
Ce-L Ce-R C8-L C8-R C22-L C22-R : Term
Ce-L = L1
Ce-R = R2
C8-L = L1
C8-R = R1
C22-L = L1
C22-R = L1

Ce-L-⊢ : empty ∣ [] ⊢ Ce-L ⦂ `ℕ
Ce-L-⊢ = L1-⊢
Ce-R-⊢ : empty ∣ [] ⊢ Ce-R ⦂ ★
Ce-R-⊢ = R2-⊢
C8-L-⊢ : empty ∣ [] ⊢ C8-L ⦂ `ℕ
C8-L-⊢ = L1-⊢
C8-R-⊢ : empty ∣ [] ⊢ C8-R ⦂ ★
C8-R-⊢ = R1-⊢
C22-L-⊢ : empty ∣ [] ⊢ C22-L ⦂ `ℕ
C22-L-⊢ = L1-⊢
C22-R-⊢ : empty ∣ [] ⊢ C22-R ⦂ `ℕ
C22-R-⊢ = L1-⊢

------------------------------------------------------------------------
-- The runs
------------------------------------------------------------------------

Cf-R-run : Reaches 16 11 Cf-R-⊢ ($ 5)
Cf-R-run = reaches refl (ans-value (V-simple S-$))

Cg-R-run : Reaches 21 16 Cg-R-⊢ ($ 5 ⟨ [] ∣ `ℕ ! ⟩)
Cg-R-run = reaches refl (ans-value (V-simple (S-cast (V-simple S-$) I-tag)))

Ch-R-run : Reaches 15 10 Ch-R-⊢ ($ 5 ⟨ [] ∣ `ℕ ! ⟩)
Ch-R-run = reaches refl (ans-value (V-simple (S-cast (V-simple S-$) I-tag)))

C5-L-run : Reaches 9 4 C5-L-⊢ (blame ℓ)
C5-L-run = reaches refl (ans-blame)

C5-R-run : Reaches 6 1 C5-R-⊢ (`true ⟨ [] ∣ `𝔹 ! ⟩)
C5-R-run = reaches refl (ans-value (V-simple (S-cast (V-simple S-true) I-tag)))

C6-L-run : Reaches 10 5 C6-L-⊢ (blame ℓ)
C6-L-run = reaches refl (ans-blame)

C12-R-run : Reaches 24 19 C12-R-⊢ ($ 5)
C12-R-run = reaches refl (ans-value (V-simple S-$))

C13-R-run : Reaches 29 24 C13-R-⊢ ($ 5 ⟨ [] ∣ `ℕ ! ⟩)
C13-R-run = reaches refl (ans-value (V-simple (S-cast (V-simple S-$) I-tag)))

C14-R-run : Reaches 38 33 C14-R-⊢ ($ 5)
C14-R-run = reaches refl (ans-value (V-simple S-$))

C17-L-run : Reaches 14 9 C17-L-⊢ ($ 42)
C17-L-run = reaches refl (ans-value (V-simple S-$))

C17-R-run : Reaches 7 2 C17-R-⊢ ($ 42 ⟨ [] ∣ `ℕ ! ⟩)
C17-R-run = reaches refl (ans-value (V-simple (S-cast (V-simple S-$) I-tag)))

C18-R-run : Reaches 22 17 C18-R-⊢ ($ 42 ⟨ [] ∣ `ℕ ! ⟩)
C18-R-run = reaches refl (ans-value (V-simple (S-cast (V-simple S-$) I-tag)))

C18b-R-run : Reaches 23 18 C18b-R-⊢ ($ 42)
C18b-R-run = reaches refl (ans-value (V-simple S-$))

C19-L-run : Reaches 15 10 C19-L-⊢ ($ 5)
C19-L-run = reaches refl (ans-value (V-simple S-$))

C19-R-run : Reaches 7 2 C19-R-⊢ ($ 5 ⟨ [] ∣ `ℕ ! ⟩)
C19-R-run = reaches refl (ans-value (V-simple (S-cast (V-simple S-$) I-tag)))

C23a-R-run : Reaches 27 22 C23a-R-⊢ ($ 42 ⟨ [] ∣ `ℕ ! ⟩)
C23a-R-run = reaches refl (ans-value (V-simple (S-cast (V-simple S-$) I-tag)))

C23b-R-run : Reaches 25 20 C23b-R-⊢ ($ 42)
C23b-R-run = reaches refl (ans-value (V-simple S-$))

CJ-L-run : Reaches 9 4 CJ-L-⊢ (blame ℓ)
CJ-L-run = reaches refl (ans-blame)

CJ-R-run : Reaches 7 2 CJ-R-⊢ (blame ℓ)
CJ-R-run = reaches refl (ans-blame)

-- runs shared with another pair
Cf-L-run : Reaches 10 5 Cf-L-⊢ ($ 5)
Cf-L-run = L1-run

Cg-L-run : Reaches 10 5 Cg-L-⊢ ($ 5)
Cg-L-run = L1-run

Ch-L-run : Reaches 10 5 Ch-L-⊢ ($ 5)
Ch-L-run = L1-run

C2-L-run : Reaches 16 11 C2-L-⊢ ($ 5)
C2-L-run = Cf-R-run

C2-R-run : Reaches 21 16 C2-R-⊢ ($ 5 ⟨ [] ∣ `ℕ ! ⟩)
C2-R-run = Cg-R-run

C6-R-run : Reaches 6 1 C6-R-⊢ (`true ⟨ [] ∣ `𝔹 ! ⟩)
C6-R-run = C5-R-run

C10-L-run : Reaches 15 10 C10-L-⊢ ($ 5 ⟨ [] ∣ `ℕ ! ⟩)
C10-L-run = Ch-R-run

C10-R-run : Reaches 6 1 C10-R-⊢ ($ 5 ⟨ [] ∣ `ℕ ! ⟩)
C10-R-run = R2-run

C12-L-run : Reaches 10 5 C12-L-⊢ ($ 5)
C12-L-run = L1-run

C13-L-run : Reaches 10 5 C13-L-⊢ ($ 5)
C13-L-run = L1-run

C14-L-run : Reaches 10 5 C14-L-⊢ ($ 5)
C14-L-run = L1-run

C16-L-run : Reaches 16 11 C16-L-⊢ ($ 5)
C16-L-run = Cf-R-run

C16-R-run : Reaches 6 1 C16-R-⊢ ($ 5 ⟨ [] ∣ `ℕ ! ⟩)
C16-R-run = R2-run

C16b-L-run : Reaches 21 16 C16b-L-⊢ ($ 5 ⟨ [] ∣ `ℕ ! ⟩)
C16b-L-run = Cg-R-run

C16b-R-run : Reaches 6 1 C16b-R-⊢ ($ 5 ⟨ [] ∣ `ℕ ! ⟩)
C16b-R-run = R2-run

C18-L-run : Reaches 14 9 C18-L-⊢ ($ 42)
C18-L-run = C17-L-run

C18b-L-run : Reaches 14 9 C18b-L-⊢ ($ 42)
C18b-L-run = C17-L-run

C23a-L-run : Reaches 14 9 C23a-L-⊢ ($ 42)
C23a-L-run = C17-L-run

C23b-L-run : Reaches 14 9 C23b-L-⊢ ($ 42)
C23b-L-run = C17-L-run

Ce-L-run : Reaches 10 5 Ce-L-⊢ ($ 5)
Ce-L-run = L1-run

Ce-R-run : Reaches 6 1 Ce-R-⊢ ($ 5 ⟨ [] ∣ `ℕ ! ⟩)
Ce-R-run = R2-run

C8-L-run : Reaches 10 5 C8-L-⊢ ($ 5)
C8-L-run = L1-run

C8-R-run : Reaches 11 6 C8-R-⊢ ($ 5 ⟨ [] ∣ `ℕ ! ⟩)
C8-R-run = R1-run

C22-L-run : Reaches 10 5 C22-L-⊢ ($ 5)
C22-L-run = L1-run

C22-R-run : Reaches 10 5 C22-R-⊢ ($ 5)
C22-R-run = L1-run
