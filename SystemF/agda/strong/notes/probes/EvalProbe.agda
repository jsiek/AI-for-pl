module strong.notes.probes.EvalProbe where

-- VALIDATION OF strong.Eval — the lightweight step function — against
-- the hand-built runs of the gauntlet and the probes.
--
-- Everything here is run on the LIVE `step` (strong.Eval) and the LIVE
-- terms of strong.notes.InstallGauntlet / strong.notes.probes
-- .DualIntProbe: no local copies.  Every claim is a refl-checked
-- computation, so this file IS the test suite.
--
-- CONTENTS
--   §1  THE §9f PROGRAM.  `step` reproduces cx-step₁ … cx-step₁₀ on the
--       nose, one assertion per mechanized step, and `trace` runs the
--       closed source cxP₀ to the bare numeral 3 in 14 steps.  The one
--       place the MERGE GUARD has to fire on this run is cxP₅ → cxP₅′
--       (cx-step₆a's lineage cancel), and it does: mergeOK? discharges
--       all five components there.
--   §2  §9i's rvQ₀ — the REVEAL-VARIABLE face, where the only move is a
--       Merge.  The run reaches the bare 7 in 11 steps, and passes
--       through rv-merge, rv-finish and the three Drop$ tail steps.
--   §3  §9m's STUCK TERM.  `step` returns `nothing` there, exactly, and
--       for the right reason: MergeOK's EXTERNAL-FACE component fails
--       (¬ext-q), so mergeOK? refuses and no other rule applies.  This
--       is the machine confirming ¬progress by computation.
--   §4  THE PRESERVATION COUNTEREXAMPLE (DualIntProbe §5).  `step` is
--       TYPE-BLIND, so it steps THROUGH the fatal Peel into the
--       ill-typed contractum and keeps going.  Typability is lost at
--       the FIRST step: ⊢Redex types state 0 at ℕ and ¬⊢contractum
--       refutes state 1.  Nothing after that is typed at all.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.String using (String)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import strong.Types
open import strong.Context
open import strong.Boundary
open import strong.BReduction
open import strong.EvalDec
open import strong.Eval
open import strong.notes.InstallGauntlet
import strong.notes.probes.DualIntProbe as DI

------------------------------------------------------------------------
-- §1  THE §9f PROGRAM, STEP BY STEP.
--
--   P = ((ΛX. λx:X. λf:X⇒ℕ. f·x) ·[X⇒(X⇒ℕ)⇒ℕ, ℕ] · 5)
--         · ((ΛW. λy:W. 3) ·[W⇒ℕ, ℕ])
--
-- a CLOSED plain System F source (⊢cxP₀ : [] ∣ [] ⊢ cxP₀ ⦂ ℕ).
------------------------------------------------------------------------

cx₁ : step [] cxP₀ ≡ just cxP₁                     -- cx-step₁  TyBeta
cx₁ = refl

cx₂a : step [] cxP₁ ≡ just cxP₁½                   -- cx-step₂a Peel
cx₂a = refl

cx₂b : step [] cxP₁½ ≡ just cxP₂                   -- cx-step₂b Beta
cx₂b = refl

cx₃ : step [] cxP₂ ≡ just cxP₃                     -- cx-step₃  TyBeta
cx₃ = refl

cx₄a : step [] cxP₃ ≡ just cxP₃½                   -- cx-step₄a Peel
cx₄a = refl

cx₄b : step [] cxP₃½ ≡ just cxP₄                   -- cx-step₄b Beta
cx₄b = refl

cx₅ : step [] cxP₄ ≡ just cxP₅                     -- cx-step₅  Peel
cx₅ = refl

-- *** THE MERGE GUARD FIRES HERE ***  cxP₅'s argument is the lineage
-- tower (5 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=ℕ , X ⟫, whose outer face is ACTIVE;
-- mergeOK? discharges all five components and the pair cancels.
cx₆a : step [] cxP₅ ≡ just cxP₅′                   -- cx-step₆a Merge
cx₆a = refl

cx₆b : step [] cxP₅′ ≡ just cxP₅″                  -- cx-step₆b Drop$
cx₆b = refl

cx₆ : step [] cxP₅″ ≡ just cxP₆                    -- cx-step₆  Peel
cx₆ = refl

cx₇ : step [] cxP₆ ≡ just cxP₇                     -- cx-step₇  Beta
cx₇ = refl

cxP₈ cxP₉ : Term
cxP₈ = (($ 3) ⟪ Θcx2 , `ℕ ⟫) ⟪ Θcx1 , `ℕ ⟫
cxP₉ = ($ 3) ⟪ Θcx1 , `ℕ ⟫

cx₈ : step [] cxP₇ ≡ just cxP₈                     -- cx-step₈  Drop$
cx₈ = refl

cx₉ : step [] cxP₈ ≡ just cxP₉                     -- cx-step₉  Drop$
cx₉ = refl

cx₁₀ : step [] cxP₉ ≡ just ($ 3)                   -- cx-step₁₀ Drop$
cx₁₀ = refl

cx-halts : step [] ($ 3) ≡ nothing
cx-halts = refl

-- THE WHOLE RUN, as one computation: 15 states, 14 steps, ending at the
-- §9f answer.
cx-run : trace 20 [] cxP₀
       ≡ cxP₀ ∷ cxP₁ ∷ cxP₁½ ∷ cxP₂ ∷ cxP₃ ∷ cxP₃½ ∷ cxP₄ ∷ cxP₅
           ∷ cxP₅′ ∷ cxP₅″ ∷ cxP₆ ∷ cxP₇ ∷ cxP₈ ∷ cxP₉ ∷ ($ 3) ∷ []
cx-run = refl

cxRun : String                     -- render with scripts/render_term.sh
cxRun = showTrace 20 0 cxP₀

-- THE ACTIVE/INERT DISCIPLINE, as `step` sees it.  §9d(i)'s ⇒-faced
-- nesting is a VALUE (val-redex-cx) — both faces INERT — so `step`
-- idles on it; §9i's tower has an ACTIVE outer face (¬val-rv) and is
-- not a value, so it steps.  This is Decision 6 in two computations.
cx-value-idles : step Δcx ((Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫)
                            ⟪ Θcx2 , ` 0 ⇒ `ℕ ⟫)
               ≡ nothing
cx-value-idles = refl

------------------------------------------------------------------------
-- §2  §9i's rvQ₀ — the run that NEEDS Merge.
--
--   Q = ((ΛX. λf:(ℕ⇒X). f · 3) ·[ (ℕ⇒X)⇒X , ℕ⇒ℕ ] · g) · 5
--       g = λn:ℕ. λm:ℕ. 7
--
-- rvQ₅'s tower has a REVEAL-VARIABLE face: rv-only-merge says every
-- step from it is a Merge, so deleting the rule strands this program.
------------------------------------------------------------------------

rvQ₆ rvQ₇ rvQ₈ rvQ₉ : Term
rvQ₆ = ((ƛ `ℕ ∙ ($ 7)) ⟪ [] , `ℕ ⇒ `ℕ ⟫) · ($ 5)
rvQ₇ = ((ƛ `ℕ ∙ ($ 7)) · (($ 5) ⟪ [] , `ℕ ⟫)) ⟪ [] , `ℕ ⟫
rvQ₈ = ((ƛ `ℕ ∙ ($ 7)) · ($ 5)) ⟪ [] , `ℕ ⟫
rvQ₉ = ($ 7) ⟪ [] , `ℕ ⟫

rv₁ : step [] rvQ₀ ≡ just rvQ₁                     -- rv-step₁  TyBeta
rv₁ = refl

rv₂ : step [] rvQ₁ ≡ just rvQ₂                     -- rv-step₂  Peel
rv₂ = refl

rv₃ : step [] rvQ₂ ≡ just rvQ₃                     -- rv-step₃  Beta
rv₃ = refl

rv₄ : step [] rvQ₃ ≡ just rvQ₄                     -- rv-step₄  Peel
rv₄ = refl

rv₄a : step [] rvQ₄ ≡ just rvQ₄′                   -- rv-step₄a Drop$
rv₄a = refl

rv₅ : step [] rvQ₄′ ≡ just rvQ₅                    -- rv-step₅  Beta
rv₅ = refl

-- *** THE MERGE GUARD FIRES HERE ***  rv-merge: the lineage pair
-- cancels to the EMPTY composite (rv-⊕-∅) and X's rep resolves to ℕ⇒ℕ
-- (rv-mrgB), so the collapsed face is a genuine function type again.
rv₆ : step [] rvQ₅ ≡ just rvQ₆                     -- rv-merge
rv₆ = refl

rv₇ : step [] rvQ₆ ≡ just rvQ₇                     -- rv-finish Peel
rv₇ = refl

rv₈ : step [] rvQ₇ ≡ just rvQ₈                     -- rv-fin₂   Drop$
rv₈ = refl

rv₉ : step [] rvQ₈ ≡ just rvQ₉                     -- rv-fin₃   Beta
rv₉ = refl

rv₁₀ : step [] rvQ₉ ≡ just ($ 7)                   -- rv-fin₄   Drop$
rv₁₀ = refl

-- the run reaches the BARE answer: no wrapper is left around the 7
rv-run : trace 20 [] rvQ₀
       ≡ rvQ₀ ∷ rvQ₁ ∷ rvQ₂ ∷ rvQ₃ ∷ rvQ₄ ∷ rvQ₄′ ∷ rvQ₅
           ∷ rvQ₆ ∷ rvQ₇ ∷ rvQ₈ ∷ rvQ₉ ∷ ($ 7) ∷ []
rv-run = refl

rvRun : String                     -- render with scripts/render_term.sh
rvRun = showTrace 20 0 rvQ₀

------------------------------------------------------------------------
-- §3  §9m's STUCK TERM — the machine's own confirmation of ¬progress.
--
--   Δq = X:=ℕ ;  Θq2 = ↑X:=ℕ ;  Θq1 = ↓X:=(` 0)
--   ((5 ⟪ ↓·:=ℕ , · ⟫) ⟪ Θq1 , · ⟫) ⟪ Θq2 , · ⟫  :  ℕ        (⊢q)
--
-- ⊢q types it, ¬val-q says it is not a value, stuck-q says it takes no
-- step — and `step` AGREES BY COMPUTATION.  The refusal is MergeOK's
-- component (5): the composite's external face is ` 0 while the redex's
-- own type is ℕ (¬ext-q), and mergeOK?'s `_≟ᵗ_` on that pair says no.
------------------------------------------------------------------------

qTm : Term
qTm = (Vq ⟪ Θq1 , ` 0 ⟫) ⟪ Θq2 , ` 0 ⟫

q-stuck : step Δq qTm ≡ nothing
q-stuck = refl

-- … and the trace stops there, with the single state
q-run : trace 20 Δq qTm ≡ qTm ∷ []
q-run = refl

-- FOR CONTRAST: §9m's own repair — the LINEAGE rep ℕ in place of the
-- coincident variable — merges, exactly as merge-q′ says
q′-steps : step Δq ((($ 5) ⟪ Θq1′ , ` 0 ⟫) ⟪ Θq2 , ` 0 ⟫)
         ≡ just (($ 5) ⟪ Θq1′ ⊕ Θq2 , mrgB Θq1′ Θq2 (` 0) ⟫)
q′-steps = refl

------------------------------------------------------------------------
-- §4  THE PRESERVATION COUNTEREXAMPLE, RUN.
--
-- strong.notes.probes.DualIntProbe §3.3/§5:
--
--   Δd = W:=X , X Λ-bound , V:=ℕ
--   Θ2 = ↑?:=W , ↓V:=ℕ
--   redex = (λf:(W⇒W). 5) ⟪ Θ2 , (W⇒W)⇒ℕ ⟫ · ((λx:W. x) ⟪ ↓W:=W , W⇒W ⟫)
--
-- ⊢Redex types the redex at ℕ and peel-step fires — but the dual
-- dualᴳ Δd Θ2 DEMOTES slot 0 to rvl⋆, so the crossing argument does not
-- retype in the rebuild (¬⊢W-rebuild) and the contractum has no typing
-- at all (¬⊢contractum).  PRESERVATION IS FALSE HERE.
--
-- `step` is TYPE-BLIND: it takes the Peel anyway, and keeps evaluating.
-- TYPABILITY IS LOST AT STEP 1 — state 0 is ⊢Redex, state 1 is
-- ¬⊢contractum's term — and no later state is typed either.
------------------------------------------------------------------------

diRedex diPeeled : Term
diRedex = (DI.Vtm ⟪ DI.Θ2 , (` 0 ⇒ ` 0) ⇒ `ℕ ⟫) · DI.Wtm
diPeeled =
  (DI.Vtm · (DI.Wtm ⟪ dualᴳ DI.Δd DI.Θ2
                    , renameᵗ (swapᵇ DI.Θ2) (` 0 ⇒ ` 0) ⟫))
  ⟪ DI.Θ2 , `ℕ ⟫

-- state 0 → state 1 : THE FATAL PEEL (DualIntProbe's peel-step)
di₁ : step DI.Δd diRedex ≡ just diPeeled
di₁ = refl

-- *** WHERE TYPABILITY IS LOST *** — state 1 has no typing at ℕ
di-untyped : ¬ (DI.Δd ∣ [] ⊢ diPeeled ⦂ `ℕ)
di-untyped = DI.¬⊢contractum

-- and the evaluator carries on regardless: the ill-typed contractum
-- β-reduces under the boundary, and the residual ℕ-faced wrapper drops
diP₂ diP₃ : Term
diP₂ = ($ 5) ⟪ DI.Θ2 , `ℕ ⟫
diP₃ = $ 5

di₂ : step DI.Δd diPeeled ≡ just diP₂              -- ξ-⟪⟫ (Beta …)
di₂ = refl

di₃ : step DI.Δd diP₂ ≡ just diP₃                  -- Drop$
di₃ = refl

di-run : trace 20 DI.Δd diRedex
       ≡ diRedex ∷ diPeeled ∷ diP₂ ∷ diP₃ ∷ []
di-run = refl

-- the ambient here CARRIES KNOWLEDGE (W:=X, V:=ℕ), which Peel's dual
-- copies, so the render uses the REAL context, not prepAbst
diRun : String                     -- render with scripts/render_term.sh
diRun = showTraceIn 20 DI.Δd diRedex
