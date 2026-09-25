module strong-rep-nu.notes.ErasureProbe where

-- File Charter:
--   * CHECKS OF THE ERASURE THEOREMS ON RUNS, by `refl`.  The erasure is
--     strong-rep-nu.Erasure, the statements strong-rep-nu.ErasureTheorems
--     (proofs under proof/Erasure*); the design is notes/ErasureSketch.md.
--   * §7a equality deciders; §7b per-step rows (predicted by `isStutter`,
--     observed on the erasures); §7c rendering; §7d the required runs;
--     §7e all twenty compiled programs; §7f runs beyond the corpus, the
--     store followed, the naive erasure, and `Mbad` (why the simulation
--     needs its typing premise).

open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Product using (_,_; proj₁)
open import Data.String using (String)
import Data.Nat.Show
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.Boundary using (unbind)
open import strong-rep-nu.Terms
  using (Term; `_; $_; `true; `false; ƛ_∙_; _·_; Λ_; ν_·_⟨_⟩; _⟪_,_⟫)
open import strong-rep-nu.Reduction
open import strong-rep-nu.Eval using (step)
open import strong-rep-nu.Show using (ruleName; tyBinder; tmBinder; nthS)
open import strong-rep-nu.Source
  using (STerm; `_; $_; `true; `false; ƛ_∙_; _·_; Λ_; _[_]; inferˢ)
open import strong-rep-nu.Conversion using (⌞_⌟; id)
open import strong-rep-nu.SourceReduction
open import strong-rep-nu.Erasure
import strong-rep-nu.Examples as E
import strong-rep-nu.SourceExamples as SE

------------------------------------------------------------------------
-- 7. The example checks
------------------------------------------------------------------------

-- 7a. Deciding what a checker needs: equality of types and terms.
_==ᵗ_ : Ty → Ty → Bool
(` X)   ==ᵗ (` Y)     = X ≡ᵇ Y
`ℕ      ==ᵗ `ℕ        = true
`𝔹      ==ᵗ `𝔹        = true
(A ⇒ B) ==ᵗ (A′ ⇒ B′) = (A ==ᵗ A′) ∧ (B ==ᵗ B′)
(`∀ A)  ==ᵗ (`∀ A′)   = A ==ᵗ A′
_       ==ᵗ _         = false

_==ˢ_ : STerm → STerm → Bool
(` x)     ==ˢ (` y)       = x ≡ᵇ y
($ k)     ==ˢ ($ j)       = k ≡ᵇ j
`true     ==ˢ `true       = true
`false    ==ˢ `false      = true
(ƛ A ∙ N) ==ˢ (ƛ A′ ∙ N′) = (A ==ᵗ A′) ∧ (N ==ˢ N′)
(L · M)   ==ˢ (L′ · M′)   = (L ==ˢ L′) ∧ (M ==ˢ M′)
(Λ N)     ==ˢ (Λ N′)      = N ==ˢ N′
(L [ A ]) ==ˢ (L′ [ A′ ]) = (L ==ˢ L′) ∧ (A ==ᵗ A′)
_         ==ˢ _           = false

-- The per-step checks below compare a PREDICTED relation with the
-- OBSERVED one; the prediction is read off `isStutter`, the same function
-- the statements use.
data Link : Set where
  same : Link     -- the two erasures are equal
  src  : Link     -- the second is the source step of the first
  bad  : Link     -- neither (only produced by the checker below)

ruleKind : ∀ {Δ M M′ δ} → Δ ⊢ M -→ M′ ∣ δ → Link
ruleKind r = if isStutter r then same else src

-- how two consecutive erasures are related, as observed
link : STerm → STerm → Link
link M N with M ==ˢ N
link M N | true = same
link M N | false with stepToˢ M
link M N | false | nothing = bad
link M N | false | just M′ = if M′ ==ˢ N then src else bad

-- 7b. A run-time run, step by step: the rule, what `ruleKind` PREDICTS
-- (`isStutter`: `ErasureStutter` / `ErasureStep`), and what the erasures
-- SHOW.
record Row : Set where
  constructor row
  field
    rule      : String
    predicted : Link
    observed  : Link

rows : ℕ → Ctxᵗ → Term → List Row
rows zero    Δ M = []
rows (suc k) Δ M with step Δ M
rows (suc k) Δ M | nothing = []
rows (suc k) Δ M | just (M′ , δ , r) =
  row (ruleName r) (ruleKind r) (link (erase Δ M) (erase (apply δ Δ) M′))
    ∷ rows k (apply δ Δ) M′

-- the erased states of a run-time run
erasedRun : ℕ → Ctxᵗ → Term → List STerm
erasedRun zero    Δ M = erase Δ M ∷ []
erasedRun (suc k) Δ M with step Δ M
erasedRun (suc k) Δ M | nothing = erase Δ M ∷ []
erasedRun (suc k) Δ M | just (M′ , δ , r) =
  erase Δ M ∷ erasedRun k (apply δ Δ) M′

-- drop the stutters
collapse : List STerm → List STerm
collapse []       = []
collapse (M ∷ Ms) = M ∷ go M Ms
  where
  go : STerm → List STerm → List STerm
  go P []       = []
  go P (N ∷ Ns) = if P ==ˢ N then go P Ns else N ∷ go N Ns

linkEq : Link → Link → Bool
linkEq same same = true
linkEq src  src  = true
linkEq bad  bad  = true
linkEq _    _    = false

-- every step is related as its rule predicts, and none is `bad`
allAgree : List Row → Bool
allAgree []                  = true
allAgree (row n p bad ∷ rs)  = false
allAgree (row n p o ∷ rs)    = linkEq p o ∧ allAgree rs

-- every erased state is a closed source term of type A (ErasureTyping
-- at the empty ambient, where eraseTy is the identity on closed types)
typeOfˢ : STerm → Maybe Ty
typeOfˢ M = Maybe.map proj₁ (inferˢ 0 [] M)

allTyped : Ty → List STerm → Bool
allTyped A []       = true
allTyped A (M ∷ Ms) with typeOfˢ M
allTyped A (M ∷ Ms) | nothing = false
allTyped A (M ∷ Ms) | just B  = (A ==ᵗ B) ∧ allTyped A Ms

-- THE CHECK OF ONE RUN: (i) the rules agree with ErasureStutter / ErasureStep,
-- (ii) the erased run with its stutters dropped IS the source
-- evaluator's run from the source program, (iii) every erased state has
-- the program's type.
record RunChecks (k : ℕ) (M : Term) (S : STerm) (A : Ty) : Set where
  field
    agree    : allAgree (rows k empty M) ≡ true
    collapsed : collapse (erasedRun k empty M) ≡ runˢ k S
    typed    : allTyped A (erasedRun k empty M) ≡ true

-- 7c. Rendering a source term with names (for ErasureSketch.md, via
-- scripts/render_term.sh)
showTyˢ : List String → Ty → String
showTyˢ ns (` X)   = nthS ns X
showTyˢ ns `ℕ      = "ℕ"
showTyˢ ns `𝔹      = "𝔹"
showTyˢ ns (A ⇒ B) =
  Data.String._++_ "(" (Data.String._++_ (showTyˢ ns A)
    (Data.String._++_ "⇒" (Data.String._++_ (showTyˢ ns B) ")")))
showTyˢ ns (`∀ A)  =
  Data.String._++_ "(∀" (Data.String._++_ (tyBinder (Data.List.length ns))
    (Data.String._++_ ". "
      (Data.String._++_ (showTyˢ (tyBinder (Data.List.length ns) ∷ ns) A)
        ")")))

private
  infixr 5 _+++_
  _+++_ : String → String → String
  _+++_ = Data.String._++_

showS : List String → List String → STerm → String
showS ts xs (` x)     = nthS xs x
showS ts xs ($ k)     = Data.Nat.Show.show k
showS ts xs `true     = "true"
showS ts xs `false    = "false"
showS ts xs (ƛ A ∙ N) =
  "(λ" +++ tmBinder (Data.List.length xs) +++ ":" +++ showTyˢ ts A
    +++ ". " +++ showS ts (tmBinder (Data.List.length xs) ∷ xs) N +++ ")"
showS ts xs (L · M)   =
  "(" +++ showS ts xs L +++ " · " +++ showS ts xs M +++ ")"
showS ts xs (Λ N)     =
  "(Λ" +++ tyBinder (Data.List.length ts) +++ ". "
    +++ showS (tyBinder (Data.List.length ts) ∷ ts) xs N +++ ")"
showS ts xs (L [ A ]) = showS ts xs L +++ " [" +++ showTyˢ ts A +++ "]"

showRows : List Row → String
showRows [] = ""
showRows (row n p o ∷ rs) =
  n +++ ":" +++ showLink o +++ " " +++ showRows rs
  where
  showLink : Link → String
  showLink same = "="
  showLink src  = "→ˢ"
  showLink bad  = "BAD"

showErased : List STerm → String
showErased []       = ""
showErased (M ∷ []) = showS [] [] M
showErased (M ∷ Ms@(_ ∷ _)) = showS [] [] M +++ "\n  ~~>\n" +++ showErased Ms

-- 7d. THE REQUIRED RUNS AND AN ALIAS RUN, row by row.  A row is
-- `row rule predicted observed`: `predicted` is `ruleKind` of the step
-- `step` took, `observed` is `link` on the two erasures.  Every row
-- agrees: Wrap, Merge and Id stutter; TyBeta, TyWrap and Beta take
-- exactly one source step.

-- Examples §1a `P₀` = (ΛX. λx:X. x) [ℕ] · 7
P-rows : rows 25 empty E.P₀ ≡
    row "TyBeta" src src ∷ row "Wrap" same same ∷ row "Beta" src src
  ∷ row "Merge" same same ∷ row "Id" same same ∷ []
P-rows = refl

-- Examples §5a `E₀ᴮ`, the tower
Eᴮ-rows : rows 25 empty E.E₀ᴮ ≡
    row "TyBeta" src src ∷ row "Wrap" same same ∷ row "Beta" src src
  ∷ row "TyWrap" src src ∷ row "Merge" same same ∷ row "Wrap" same same
  ∷ row "Id" same same ∷ row "Beta" src src ∷ row "Merge" same same
  ∷ row "TyWrap" src src ∷ row "Merge" same same ∷ row "Merge" same same
  ∷ row "Wrap" same same ∷ row "Beta" src src ∷ row "Merge" same same
  ∷ row "Id" same same ∷ []
Eᴮ-rows = refl

-- Examples §7a `A₀` = (ΛX. λx:X. x) [ℕ⇒ℕ] · (λn:ℕ. n) · 7
A-rows : rows 25 empty E.A₀ ≡
    row "TyBeta" src src ∷ row "Wrap" same same ∷ row "Beta" src src
  ∷ row "Merge" same same ∷ row "Wrap" same same ∷ row "Id" same same
  ∷ row "Beta" src src ∷ row "Id" same same ∷ []
A-rows = refl

-- Examples §8 `S₀`: the alias cell β := γ, and the chained seals
S-rows : rows 25 empty E.S₀ ≡
    row "TyBeta" src src ∷ row "Wrap" same same ∷ row "Beta" src src
  ∷ row "TyBeta" src src ∷ row "Wrap" same same ∷ row "Beta" src src
  ∷ row "TyWrap" src src ∷ row "Merge" same same ∷ row "Wrap" same same
  ∷ row "Beta" src src ∷ row "Merge" same same ∷ row "Merge" same same
  ∷ row "Merge" same same ∷ row "Merge" same same ∷ row "Id" same same
  ∷ []
S-rows = refl

-- Examples §2c `R₀`: a cell whose payload is another cell's variable
R-rows : rows 25 empty E.R₀ ≡
    row "TyBeta" src src ∷ row "Wrap" same same ∷ row "Beta" src src
  ∷ row "TyBeta" src src ∷ row "Wrap" same same ∷ row "Merge" same same
  ∷ row "Beta" src src ∷ row "TyBeta" src src ∷ row "Wrap" same same
  ∷ row "Id" same same ∷ row "Beta" src src ∷ row "Merge" same same
  ∷ row "Merge" same same ∷ row "Merge" same same ∷ row "Merge" same same
  ∷ row "Id" same same ∷ []
R-rows = refl

-- 7e. ALL TWENTY COMPILED PROGRAMS (strong-rep-nu.SourceExamples): the
-- rows agree, the collapsed erased run IS the source run of the source
-- program, and every erased state has the program's type.
checks : ∀ {k M S A} → allAgree (rows k empty M) ≡ true
  → collapse (erasedRun k empty M) ≡ runˢ k S
  → allTyped A (erasedRun k empty M) ≡ true
  → RunChecks k M S A
checks a c t = record { agree = a ; collapsed = c ; typed = t }

P-checks : RunChecks 25 E.P₀ SE.P₀ `ℕ
P-checks = checks refl refl refl

K-checks : RunChecks 25 E.K₀ SE.K₀ `𝔹
K-checks = checks refl refl refl

J-checks : RunChecks 25 E.J₀ SE.J₀ `ℕ
J-checks = checks refl refl refl

F-checks : RunChecks 25 E.F₀ SE.F₀ `𝔹
F-checks = checks refl refl refl

U-checks : RunChecks 25 E.U₀ SE.U₀ `ℕ
U-checks = checks refl refl refl

Q-checks : RunChecks 25 E.Q₀ SE.Q₀ `ℕ
Q-checks = checks refl refl refl

D-checks : RunChecks 25 E.D₀ SE.D₀ `ℕ
D-checks = checks refl refl refl

L-checks : RunChecks 25 E.L₀ SE.L₀ `ℕ
L-checks = checks refl refl refl

R-checks : RunChecks 25 E.R₀ SE.R₀ `ℕ
R-checks = checks refl refl refl

G-checks : RunChecks 25 E.G₀ SE.G₀ `ℕ
G-checks = checks refl refl refl

H-checks : RunChecks 25 E.H₀ SE.H₀ `ℕ
H-checks = checks refl refl refl

E-checks : RunChecks 25 E.E₀ SE.E₀ (`∀ (`ℕ ⇒ (` 0 ⇒ ` 0)))
E-checks = checks refl refl refl

Eᴮ-checks : RunChecks 25 E.E₀ᴮ SE.E₀ᴮ `𝔹
Eᴮ-checks = checks refl refl refl

V-checks : RunChecks 25 E.V₀ SE.V₀ `𝔹
V-checks = checks refl refl refl

I-checks : RunChecks 25 E.I₀ SE.I₀ `𝔹
I-checks = checks refl refl refl

N-checks : RunChecks 25 E.N₀ SE.N₀ `ℕ
N-checks = checks refl refl refl

A-checks : RunChecks 25 E.A₀ SE.A₀ `ℕ
A-checks = checks refl refl refl

B-checks : RunChecks 25 E.B₀ SE.B₀ `ℕ
B-checks = checks refl refl refl

C-checks : RunChecks 25 E.C₀ SE.C₀ `ℕ
C-checks = checks refl refl refl

S-checks : RunChecks 25 E.S₀ SE.S₀ `ℕ
S-checks = checks refl refl refl

-- 7f. BEYOND THE COMPILED CORPUS.

-- Examples §10 `Bg`: Beta substitutes 7 UNDER a Λ, so the image crosses
-- in a wrapper `7 ⟪ ↓Z , id ℕ ⟫`; the erasure of the wrapper is the
-- source substitution's type-shifted image (here 7 itself).
Bgˢ : STerm
Bgˢ = ((ƛ `ℕ ∙ (Λ (ƛ `ℕ ∙ ` 1))) · $ 7) [ `ℕ ] · $ 0

Bg-rows : rows 25 empty E.Bg ≡
    row "Beta" src src ∷ row "TyBeta" src src ∷ row "Wrap" same same
  ∷ row "Id" same same ∷ row "Beta" src src ∷ row "Id" same same
  ∷ row "Id" same same ∷ []
Bg-rows = refl

Bg-checks : RunChecks 25 E.Bg Bgˢ `ℕ
Bg-checks = checks refl refl refl

-- Examples §9, at the NON-EMPTY ambient Δ₆ = (α := ℕ) ∣ (X ↦ α): the
-- hand-written seal/unseal layers all stutter, and the ambient name X
-- erases to ℕ.
Tcancel-rows : rows 25 E.Δ₆ E.Tcancel ≡
  row "Merge" same same ∷ row "Id" same same ∷ []
Tcancel-rows = refl

Tid₂-rows : rows 25 E.Δ₆ E.Tid₂ ≡
    row "Merge" same same ∷ row "Merge" same same ∷ row "Merge" same same
  ∷ row "Id" same same ∷ []
Tid₂-rows = refl

Δ₆-X : eraseTy E.Δ₆ (` 0 ⇒ `∀ (` 0 ⇒ ` 1)) ≡ (`ℕ ⇒ `∀ (` 0 ⇒ `ℕ))
Δ₆-X = refl

-- THE STORE, followed: an ALIAS cell denotes what its payload's cell
-- denotes (Examples §8's store [α := ℕ , β := γ , γ := ℕ], newest
-- first) ...
alias-concrete :
  env (bindR `ℕ ∷ bindR (` 0) ∷ bindR `ℕ ∷ []) 1 ≡ `ℕ
alias-concrete = refl

-- ... including an alias of an ABSTRACT cell, which denotes a source
-- variable, numbered by the abstract cells newer than it
alias-abstract :
  env (bindR (` 0) ∷ abstR ∷ bindR `ℕ ∷ abstR ∷ []) 0 ≡ ` 0
alias-abstract = refl

abstract-numbering :
  env (abstR ∷ bindR (` 0) ∷ abstR ∷ []) 1 ≡ ` 1
abstract-numbering = refl

-- WHY THE BODY IS ERASED AT `inside Δ Θ`.  Erasing a boundary's body
-- at the EXTERIOR context instead reads its ordinary names through the
-- wrong name map.  After §1a's TyBeta the state is
-- (λx:X. x) ⟪ ↥X , … ⟫ · 7 at the store (α := ℕ) with no ambient
-- names: the right erasure reads X as ℕ, the naive one leaves it
-- dangling.
eraseNaive : Ctxᵗ → Term → STerm
eraseNaive Δ (` x)           = ` x
eraseNaive Δ ($ n)           = $ n
eraseNaive Δ `true           = `true
eraseNaive Δ `false          = `false
eraseNaive Δ (ƛ A ∙ N)       = ƛ eraseTy Δ A ∙ eraseNaive Δ N
eraseNaive Δ (L · M)         = eraseNaive Δ L · eraseNaive Δ M
eraseNaive Δ (Λ N)           = Λ (eraseNaive (underΛ Δ) N)
eraseNaive Δ (ν A · L ⟨ c ⟩) = eraseNaive Δ L [ eraseTy Δ A ]
eraseNaive Δ (M ⟪ Θ , c ⟫)   = eraseNaive Δ M

P-state₁ : Maybe Term
P-state₁ = Maybe.map proj₁ (step empty E.P₀)

P-state₁-erase :
  Maybe.map (erase (allocate `ℕ empty)) P-state₁
    ≡ just ((ƛ `ℕ ∙ ` 0) · $ 7)
P-state₁-erase = refl

P-state₁-naive :
  Maybe.map (eraseNaive (allocate `ℕ empty)) P-state₁
    ≡ just ((ƛ ` 0 ∙ ` 0) · $ 7)
P-state₁-naive = refl

-- THE TYPING PREMISE IS NEEDED.  `Id` checks only `Simple U` and
-- `Base A`, so on an ILL-TYPED term it can drop an identity boundary
-- whose body is a λ.  At Δ₆ = (α := ℕ) ∣ (X ↦ α), the body of
-- (λx:X. x) ⟪ ↓X , id ℕ ⟫ is erased where X is NOT named (its
-- annotation dangles), while the contractum λx:X. x reads X as ℕ: the
-- two erasures are neither equal nor a source step.
Mbad : Term
Mbad = (ƛ (` 0) ∙ (` 0)) ⟪ unbind 0 0 ∷ [] , ⌞ id `ℕ ⌟ ⟫

Mbad-rows : rows 5 E.Δ₆ Mbad ≡ row "Id" same bad ∷ []
Mbad-rows = refl

-- NON-VACUITY of the checker: `link` does say `bad`
link-bad : link ($ 1) ($ 2) ≡ bad
link-bad = refl

link-bad-step : link ((ƛ `ℕ ∙ ` 0) · $ 1) ($ 2) ≡ bad
link-bad-step = refl

