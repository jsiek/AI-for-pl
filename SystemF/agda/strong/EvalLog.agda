module strong.EvalLog where

-- THE EVENT ANNOTATOR — a rendered trace with, between the states, a
-- line saying WHAT THE BOUNDARY BOOKKEEPING DID at that step.
--
--   event    : ∀ {Δ M M′} → Δ ⊢ M -→ M′ → String
--   traceLog : ℕ → TCtx → Term → String
--
-- `event` pattern-matches THE DERIVATION (strong.Eval's stepΣ hands
-- one back next to every contractum), recursing through the ξ-frames
-- and reporting the base rule.  So the annotation cannot drift from the
-- rule that actually fired: there is no second transcription of the
-- rule table here, only a reading of the one derivation.
--
-- WHAT EACH RULE REPORTS
--
--   TyBeta / TyWrap / TyPeel   the reveal they MINT — ↑X:=rep — with a
--       CLASSIFIER of the rep against the ambient Δ (`repClass`):
--       resolved-ground / names-Λ-bound / names-KNOWLEDGE-carrying-slot
--       (a CHAINED spelling) / names-x-slot.  This is the survey's key
--       column: DECISIONS.md's Decision 8(A) is precisely a proposal to
--       outlaw two of these four classes at birth.
--   Peel                       the AMBIENT DUAL it mints, entry by
--       entry, marking each `entᴳ` outcome: copied-raw / copied-unfolded
--       (the second-chance retry at the rep unfolded in its own tail) /
--       re-revealed-from-conceal / rvl⋆-at-abst (harmless) / DEMOTED —
--       an rvl⋆ emitted at a slot whose Δ-entry is NOT abst, i.e. the
--       one knowledge-DESTROYING step in the whole system.  Each such
--       line SCREAMS:  !! DEMOTION: Z:=Y lost.
--   Merge                      the composite: which pairs cancelled, and
--       whether Θ₁ ⊕ Θ₂ is empty.
--   Beta / Drop$               one line each.
--
-- NAMING.  The annotator mirrors strong.Show exactly: it carries the
-- same binder depth `d` and type-variable Supply that `showTm` carries
-- at the same point in the term, so a name in an event line is the name
-- the surrounding states print.  ξ-Λ extends the supply with a fresh
-- binder; ξ-⟪⟫ switches to the boundary's INTERIOR supply (reveal names,
-- then the exterior past the dropped block), as `intSup` does.
--
-- USE.  Non-interactively, via scripts/render_term.sh (see the header of
-- strong/Show.agda), piping through  sed 's/\\n/\n/g' :
--
--   scripts/render_term.sh 'traceLog 20 [] cxP₀' \
--     'open import strong.EvalLog' \
--     'open import strong.notes.InstallGauntlet'

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<ᵇ_; _<?_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_)
open import Data.Nat.Show using (show)
open import Data.String using (String) renaming (_++_ to _⧺_)
open import Relation.Nullary using (Dec; yes; no)
open import strong.Types
open import strong.Context
  using (TCtx; TyEntry; abst; rvld; xrvld; _↓_; entAt)
open import strong.Boundary
open import strong.BReduction
open import strong.Eval using (Step; stepΣ)
open import strong.Show
  using (Supply; tyBinder; extS; showTy; revNames; nth; intSup;
         showTmIn)

------------------------------------------------------------------------
-- small string plumbing
------------------------------------------------------------------------

nl : String
nl = "
"

-- one event line, indented under its state
evLine : String → String
evLine s = nl ⧺ "      ⟨" ⧺ s ⧺ "⟩"

-- one sub-line of an event (a dual's slot, a cancelled pair)
subLine : String → String
subLine s = nl ⧺ "         · " ⧺ s

------------------------------------------------------------------------
-- FREE VARIABLES of a type, as indices of the ambient
------------------------------------------------------------------------

fvsAt : ℕ → Ty → List ℕ
fvsAt d (` X)   = if X <ᵇ d then [] else (X ∸ d) ∷ []
fvsAt d `ℕ      = []
fvsAt d `𝔹      = []
fvsAt d (A ⇒ B) = fvsAt d A ++ fvsAt d B
fvsAt d (`∀ A)  = fvsAt (suc d) A

------------------------------------------------------------------------
-- THE REP CLASSIFIER.  What kind of ambient slot does a reveal's rep
-- name?  Four answers, and the design cares about all four:
--
--   kΛ    a Λ-bound (abst) slot — the class Peel's dual DEMOTES;
--   kK    a KNOWLEDGE (rvld) slot — a CHAINED spelling, the class
--         Decision 8(A) would resolve away at birth;
--   kX    an exterior-read (xrvld) slot;
--   kOut  no such slot (only reachable on an ill-scoped rep).
--
-- A rep with NO free variables is `resolved-ground`.
------------------------------------------------------------------------

data Kind : Set where
  kΛ kX kK kOut : Kind

kindAt : TCtx → ℕ → Kind
kindAt []            i       = kOut
kindAt (abst    ∷ Δ) zero    = kΛ
kindAt (rvld A  ∷ Δ) zero    = kK
kindAt (xrvld A ∷ Δ) zero    = kX
kindAt (E       ∷ Δ) (suc i) = kindAt Δ i

kindStr : Kind → String
kindStr kΛ   = "Λ-bound"
kindStr kX   = "x-slot"
kindStr kK   = "KNOWLEDGE"
kindStr kOut = "OUT-OF-SCOPE"

headStr : Kind → String
headStr kΛ   = "names-Λ-bound"
headStr kX   = "names-x-slot"
headStr kK   = "names-KNOWLEDGE-carrying-slot (chained)"
headStr kOut = "names-OUT-OF-SCOPE-slot"

rankK : Kind → ℕ
rankK kΛ   = 0
rankK kX   = 1
rankK kK   = 2
rankK kOut = 3

maxK : Kind → Kind → Kind
maxK a b = if rankK a <ᵇ rankK b then b else a

worstOf : TCtx → List ℕ → Kind
worstOf Δ []       = kΛ
worstOf Δ (X ∷ Xs) = maxK (kindAt Δ X) (worstOf Δ Xs)

perVar : Supply → TCtx → List ℕ → String
perVar sup Δ []           = ""
perVar sup Δ (X ∷ [])     = sup X ⧺ ":" ⧺ kindStr (kindAt Δ X)
perVar sup Δ (X ∷ Y ∷ Xs) =
  sup X ⧺ ":" ⧺ kindStr (kindAt Δ X) ⧺ "," ⧺ perVar sup Δ (Y ∷ Xs)

repClassS : ℕ → Supply → TCtx → Ty → String
repClassS d sup Δ A with fvsAt 0 A
repClassS d sup Δ A | []       = "resolved-ground"
repClassS d sup Δ A | (X ∷ Xs) =
  headStr (worstOf Δ (X ∷ Xs)) ⧺ " {" ⧺ perVar sup Δ (X ∷ Xs) ⧺ "}"

-- the plain form: names the ambient's slots X, Y, Z, … , exactly as
-- strong.Show's default supply does
repClass : TCtx → Ty → String
repClass Δ A = repClassS (length Δ) tyBinder Δ A

------------------------------------------------------------------------
-- PEEL'S DUAL, SLOT BY SLOT.  `entᴳ Δ Θ i k` is mirrored branch for
-- branch — the outcome names are the only thing added.  k, the number
-- of DEEPER dual reveals, is  cmax Θ ∸ suc i , which is what
-- `rvlsᴳ (cmax Θ) 0` feeds it.
------------------------------------------------------------------------

-- the rep of Δ's own entry at slot i lives over Δ ↓ i
tailSup : ℕ → Supply → Supply
tailSup i sup k = sup (suc (i + k))

entOutcome : ℕ → Supply → TCtx → BCtx → ℕ → ℕ → String
entOutcome d sup Δ Θ i k with isConc i Θ
entOutcome d sup Δ Θ i k | true =
  "re-revealed-from-conceal  ↑" ⧺ sup i ⧺ ":="
    ⧺ showTy d sup (repOf i Θ)
entOutcome d sup Δ Θ i k | false with entAt Δ i
entOutcome d sup Δ Θ i k | false | abst =
  "rvl⋆-at-abst (harmless)   ↑" ⧺ sup i ⧺ ":⋆"
entOutcome d sup Δ Θ i k | false | xrvld B =
  "!! DEMOTION: " ⧺ sup i ⧺ ":=ˣ"
    ⧺ showTy d (tailSup i sup) B ⧺ " lost  (→ ↑" ⧺ sup i ⧺ ":⋆)"
entOutcome d sup Δ Θ i k | false | rvld B with dfree 0 k B
entOutcome d sup Δ Θ i k | false | rvld B | true =
  "copied-raw                ↑" ⧺ sup i ⧺ ":="
    ⧺ showTy d (tailSup i sup) B
entOutcome d sup Δ Θ i k | false | rvld B | false
  with dfree 0 k (unfEnt Δ i B)
entOutcome d sup Δ Θ i k | false | rvld B | false | true =
  "copied-unfolded (2nd chance)  ↑" ⧺ sup i ⧺ ":="
    ⧺ showTy d (tailSup i sup) (unfEnt Δ i B)
    ⧺ "  [raw was " ⧺ showTy d (tailSup i sup) B ⧺ "]"
entOutcome d sup Δ Θ i k | false | rvld B | false | false =
  "!! DEMOTION: " ⧺ sup i ⧺ ":="
    ⧺ showTy d (tailSup i sup) B ⧺ " lost  (→ ↑" ⧺ sup i ⧺ ":⋆)"

-- the same branch tree, as a Bool, so a corpus entry can assert the
-- demotion count by refl.  Split at the ENTRY so the two structural
-- facts — a demotion is never at an `abst` slot, and never at a
-- CONCEALED one — are provable without inspecting a with-tree
-- (SurveyCorpus §C.2/§C.3).
demoteE : TyEntry → TCtx → ℕ → ℕ → Bool
demoteE abst      Δ i k = false
demoteE (xrvld B) Δ i k = true
demoteE (rvld B)  Δ i k with dfree 0 k B
demoteE (rvld B)  Δ i k | true  = false
demoteE (rvld B)  Δ i k | false with dfree 0 k (unfEnt Δ i B)
demoteE (rvld B)  Δ i k | false | true  = false
demoteE (rvld B)  Δ i k | false | false = true

isDemote : TCtx → BCtx → ℕ → ℕ → Bool
isDemote Δ Θ i k =
  if isConc i Θ then false else demoteE (entAt Δ i) Δ i k

-- n slots remaining, current slot s, k = n ∸ 1 deeper dual reveals
demoteFrom : TCtx → BCtx → ℕ → ℕ → ℕ
demoteFrom Δ Θ zero    s = 0
demoteFrom Δ Θ (suc k) s =
  (if isDemote Δ Θ s k then 1 else 0) + demoteFrom Δ Θ k (suc s)

demoteCount : TCtx → BCtx → ℕ
demoteCount Δ Θ = demoteFrom Δ Θ (cmax Θ) 0

dualSlots : ℕ → Supply → TCtx → BCtx → ℕ → ℕ → String
dualSlots d sup Δ Θ zero    s = ""
dualSlots d sup Δ Θ (suc k) s =
  subLine (entOutcome d sup Δ Θ s k) ⧺ dualSlots d sup Δ Θ k (suc s)

-- the dual's CONCEAL block: every reveal of Θ becomes a conceal
dualCncs : ℕ → Supply → ℕ → List String → BCtx → String
dualCncs d sup j rn []            = ""
dualCncs d sup j rn (rvl A ∷ Θ)   =
  subLine ("conceal-of-reveal        ↓" ⧺ nth rn j ⧺ ":="
            ⧺ showTy d sup A)
    ⧺ dualCncs d sup (suc j) rn Θ
dualCncs d sup j rn (rvl⋆ ∷ Θ)    =
  subLine ("conceal-of-⋆-reveal      ↓" ⧺ nth rn j ⧺ ":⋆")
    ⧺ dualCncs d sup (suc j) rn Θ
dualCncs d sup j rn (cnc X A ∷ Θ) = dualCncs d sup j rn Θ
dualCncs d sup j rn (cnc⋆ X ∷ Θ)  = dualCncs d sup j rn Θ

dualReport : ℕ → Supply → TCtx → BCtx → String
dualReport d sup Δ Θ =
  "Peel: crossing inward through dualᴳ Δ Θ  (drops "
    ⧺ show (cmax Θ) ⧺ " slot(s), keeps " ⧺ show (revs Θ)
    ⧺ " reveal(s); demotions=" ⧺ show (demoteCount Δ Θ) ⧺ ")"
  ⧺ dualSlots d sup Δ Θ (cmax Θ) 0
  ⧺ dualCncs d sup 0 (revNames d Θ) Θ

------------------------------------------------------------------------
-- MERGE.  Which pairs cancelled, and whether the composite empties.
-- The cancel clause is on the INDEX: Θ₁'s conceal of a Ψ₂-slot that Θ₂
-- REVEALS deletes both entries.
------------------------------------------------------------------------

cancelLines : ℕ → Supply → List String → BCtx → BCtx → String
cancelLines d sup rn Θ₂ []            = ""
cancelLines d sup rn Θ₂ (rvl A ∷ Θ)   = cancelLines d sup rn Θ₂ Θ
cancelLines d sup rn Θ₂ (rvl⋆ ∷ Θ)    = cancelLines d sup rn Θ₂ Θ
cancelLines d sup rn Θ₂ (cnc X A ∷ Θ) with X <? revs Θ₂
cancelLines d sup rn Θ₂ (cnc X A ∷ Θ) | yes _ =
  subLine ("CANCEL  ↓" ⧺ nth rn X ⧺ ":=" ⧺ showTy d sup A
            ⧺ "  against Θ₂'s ↑" ⧺ nth rn X)
    ⧺ cancelLines d sup rn Θ₂ Θ
cancelLines d sup rn Θ₂ (cnc X A ∷ Θ) | no _ =
  cancelLines d sup rn Θ₂ Θ
cancelLines d sup rn Θ₂ (cnc⋆ X ∷ Θ)  with X <? revs Θ₂
cancelLines d sup rn Θ₂ (cnc⋆ X ∷ Θ)  | yes _ =
  subLine ("CANCEL  ↓" ⧺ nth rn X ⧺ ":⋆  against Θ₂'s ↑" ⧺ nth rn X)
    ⧺ cancelLines d sup rn Θ₂ Θ
cancelLines d sup rn Θ₂ (cnc⋆ X ∷ Θ)  | no _ =
  cancelLines d sup rn Θ₂ Θ

cancelCount : BCtx → BCtx → ℕ
cancelCount Θ₂ []            = 0
cancelCount Θ₂ (rvl A ∷ Θ)   = cancelCount Θ₂ Θ
cancelCount Θ₂ (rvl⋆ ∷ Θ)    = cancelCount Θ₂ Θ
cancelCount Θ₂ (cnc X A ∷ Θ) with X <? revs Θ₂
cancelCount Θ₂ (cnc X A ∷ Θ) | yes _ = suc (cancelCount Θ₂ Θ)
cancelCount Θ₂ (cnc X A ∷ Θ) | no  _ = cancelCount Θ₂ Θ
cancelCount Θ₂ (cnc⋆ X ∷ Θ)  with X <? revs Θ₂
cancelCount Θ₂ (cnc⋆ X ∷ Θ)  | yes _ = suc (cancelCount Θ₂ Θ)
cancelCount Θ₂ (cnc⋆ X ∷ Θ)  | no  _ = cancelCount Θ₂ Θ

emptyStr : BCtx → String
emptyStr []      = "⊕ ≡ [] — the boundary VANISHES"
emptyStr (_ ∷ _) = "⊕ ≢ []"

mergeReport : ℕ → Supply → BCtx → BCtx → String
mergeReport d sup Θ₁ Θ₂ =
  "Merge: composite Θ₁⊕Θ₂ has " ⧺ show (length (Θ₁ ⊕ Θ₂))
    ⧺ " entry(s); " ⧺ show (cancelCount Θ₂ Θ₁) ⧺ " pair(s) cancelled; "
    ⧺ emptyStr (Θ₁ ⊕ Θ₂)
  ⧺ cancelLines d (intSup Θ₂ (revNames d Θ₂) sup) (revNames d Θ₂) Θ₂ Θ₁

------------------------------------------------------------------------
-- THE ANNOTATOR.  `d` and `sup` track strong.Show's own naming state,
-- so every name printed here is the name the states print.
------------------------------------------------------------------------

eventAt : ∀ {Δ M M′} → ℕ → Supply → Δ ⊢ M -→ M′ → String

eventAt {Δ} d sup (TyBeta {A = A} v) =
  "TyBeta: mints ↑" ⧺ tyBinder d ⧺ ":=" ⧺ showTy d sup A
    ⧺ "   rep " ⧺ repClassS d sup Δ A

eventAt d sup (Beta w) = "Beta: β-substitution (no boundary action)"

eventAt {Δ} d sup (TyWrap {Θ = Θ} {A = A} v) =
  "TyWrap: mints ↑" ⧺ tyBinder d ⧺ ":=" ⧺ showTy d sup A
    ⧺ " onto a " ⧺ show (length Θ) ⧺ "-entry boundary"
    ⧺ "   rep " ⧺ repClassS d sup Δ A

eventAt {Δ} d sup (TyPeel {Θ = Θ} {A = A} v i) =
  "TyPeel: mints ↑" ⧺ tyBinder d ⧺ ":=" ⧺ showTy d sup A
    ⧺ " onto a " ⧺ show (length Θ)
    ⧺ "-entry boundary; body weakened by ⇑ᵀ"
    ⧺ "   rep " ⧺ repClassS d sup Δ A

eventAt {Δ} d sup (Peel {Θ = Θ} v w) = dualReport d sup Δ Θ

eventAt d sup (Merge {Θ₁ = Θ₁} {Θ₂ = Θ₂} v i a mok) =
  mergeReport d sup Θ₁ Θ₂

eventAt d sup Drop$ =
  "Drop$: base face ℕ — the boundary is dropped from the numeral"

eventAt d sup (ξ-·-l st)   = "ξ·l ▸ " ⧺ eventAt d sup st
eventAt d sup (ξ-·-r v st) = "ξ·r ▸ " ⧺ eventAt d sup st
eventAt d sup (ξ-·[] st)   = "ξ[] ▸ " ⧺ eventAt d sup st
eventAt d sup (ξ-Λ st)     =
  "ξΛ ▸ " ⧺ eventAt (suc d) (extS sup (tyBinder d)) st
eventAt d sup (ξ-⟪⟫ {Θ = Θ} st) =
  "ξ⟪⟫ ▸ "
    ⧺ eventAt (d + revs Θ) (intSup Θ (revNames d Θ) sup) st

-- the plain form: the ambient's own length is the binder depth, exactly
-- as strong.Show's showTmIn takes it
event : ∀ {Δ M M′} → Δ ⊢ M -→ M′ → String
event {Δ} st = eventAt (length Δ) tyBinder st

------------------------------------------------------------------------
-- THE ANNOTATED TRACE.  States as strong.Show renders them, with the
-- event of each step between the state it leaves and the state it
-- reaches.
------------------------------------------------------------------------

logFrom : ℕ → ℕ → (Δ : TCtx) (M : Term) → String
logFrom zero    n Δ M = showTmIn n M ⧺ nl ⧺ "      [fuel exhausted]"
logFrom (suc k) n Δ M with stepΣ Δ M
logFrom (suc k) n Δ M | nothing        = showTmIn n M
logFrom (suc k) n Δ M | just (M′ , st) =
  showTmIn n M ⧺ evLine (event st) ⧺ nl ⧺ "  —→  "
    ⧺ logFrom k n Δ M′

traceLog : ℕ → TCtx → Term → String
traceLog k Δ M = logFrom k (length Δ) Δ M
