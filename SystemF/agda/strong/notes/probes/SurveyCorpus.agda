module strong.notes.probes.SurveyCorpus where

-- THE BOUNDARY SURVEY CORPUS.  One place collecting every critical
-- example of the development, each with (a) the rendered, EVENT-ANNOTATED
-- trace (strong.EvalLog's traceLog), (b) the OBLIGATION table of every
-- state (strong.Oblig's obligLog), and (c) machine-checked landmarks —
-- demotion counts, dual shapes, rebuilds — next to the gauntlet/probe
-- lemma names that already carry the typability verdicts.
--
-- Nothing here is a local copy: the EXISTING programs are imported from
-- strong.notes.InstallGauntlet and strong.notes.probes.DualIntProbe, and
-- the NEW ones (§B) are built and typed here.
--
-- NOT in strong/All.agda: this is evidence, not development.  Every
-- claim below is a refl-checked computation or a ⊢-derivation.
--
-- THE RENDERS are Strings; produce them with scripts/render_term.sh and
-- pipe through  sed 's/\\n/\n/g' :
--
--   scripts/render_term.sh 'c6Run' \
--     'open import strong.notes.probes.SurveyCorpus'
--
-- CONTENTS
--   §A  the EXISTING corpus
--       c1  E★′ end to end                       (gauntlet §1)
--       c2  E★ end to end                        (gauntlet §2)
--       c3  Pc's chained-copy site               (gauntlet §5)
--       c4  the cancel pair                      (gauntlet §9a)
--       c5  the Example-3-shaped tower           (gauntlet §9c)
--       c6  the §9d(i)-reachable program         (gauntlet §9f)
--       c7  the DOUBLE COINCIDENCE run           (gauntlet §9g)
--       c8  the reveal-variable face             (gauntlet §9i)
--       c9  the STUCK term + its lineage contrast(gauntlet §9m)
--       c10 the PRESERVATION BREAK, from source  (gauntlet §9n)
--       c11 the break's redex on its own         (DualIntProbe §3.3/§5)
--   §B  the NEW closed/typed configurations
--       n1a depth-2 chain, chain target KNOWN    (second chance SAVES)
--       n1b depth-2 chain, chain target Λ-BOUND  (DEMOTED — the break,
--                                                 MINIMIZED)
--       n2  the DOUBLE CROSSING (closed source)
--       n3  the RETURNED boundary, used again (closed source)
--       n4  an x-ENTRY consulted after one more dual — A SECOND BREAK
--       n5  a Λ-bound-rep reveal crossed TWICE (the exact round trip)

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.String using (String)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import strong.Types
open import strong.Context
open import strong.Boundary
open import strong.BReduction
open import strong.Unfold using (_≈Δ̄⟨_⟩_; ≈unf; ≡→≈; ≈-refl)
open import strong.Eval
open import strong.EvalLog
open import strong.Oblig
open import strong.notes.InstallGauntlet
import strong.notes.probes.DualIntProbe as DI

------------------------------------------------------------------------
-- §A.1  E★′ END TO END (gauntlet §1).  Source ⊢T0′; the TyWrap at T2′→T3′
-- mints ↑Z:=Y at a Λ-BOUND rep, and the Peel at T3′ builds the dual
-- dualᵛ = ↑Y:⋆ , ↑X:=ℕ , ↓Z:=Y whose ⋆ is HARMLESS (Y really is
-- abstract).  Landmarks: ⊢T0′ … ⊢T4full′, rebuild-E★′, DualInt-E★′.
------------------------------------------------------------------------

c1Run c1Ob : String
c1Run = traceLog 30 [] T0′
c1Ob  = obligLog 30 [] (`∀ (` 0 ⇒ `ℕ)) T0′

-- the crossing at T3′ demotes NOTHING: the ⋆ it emits sits at Γ★'s own
-- Λ-bound slot
c1-nodemote : demoteCount Γ★ Θ★ ≡ 0
c1-nodemote = refl

c1-dual : dualᴳ Γ★ Θ★ ≡ dualᵛ
c1-dual = refl

c1-rebuild : intOf (intOf Γ★ Θ★) dualᵛ ≡ Γ★
c1-rebuild = rebuild-E★′

------------------------------------------------------------------------
-- §A.2  E★ (gauntlet §2).  Same shape with a Z-free ∀-body: the run ends
-- at (Λ 5)⟪↑X:=ℕ, ∀ℕ⟫ (⊢T4full′′′, val-T4full′′′).
------------------------------------------------------------------------

c2Run c2Ob : String
c2Run = traceLog 30 [] T4full
c2Ob  = obligLog 30 [] (`∀ `ℕ) T4full

------------------------------------------------------------------------
-- §A.3  Pc's CHAINED-COPY SITE (gauntlet §5).  Γq = W:=Y , Y:=ℕ , X:=ℕ ;
-- Θq = ↓X:=ℕ drops all three.  W's rep is the CHAIN "W is Y" and the raw
-- guard refuses it — the SECOND-CHANCE copy takes it at the unfolded ℕ,
-- so all three slots come back with knowledge (DualInt-Γq).
--
-- A CROSSING AT THAT SITE.  The interior of Θq is EMPTY and baseS marks
-- slots W and Y `blk`, so a boundary type may name only X; the crossing
-- value is therefore an X-sealed numeral.  (A W-typed value — argW —
-- CANNOT cross this boundary at all: no boundary type can name W.  That
-- is why §5 exercises argW through the REBUILD, ⊢argW-rebuilt, not
-- through a Peel.)
------------------------------------------------------------------------

c3Fn c3Arg c3Redex : Term
c3Fn    = (ƛ `ℕ ∙ ($ 1)) ⟪ Θq , ` 2 ⇒ `ℕ ⟫
c3Arg   = ($ 3) ⟪ Θq , ` 2 ⟫
c3Redex = c3Fn · c3Arg

⊢c3Fn : Γq ∣ [] ⊢ c3Fn ⦂ (` 2 ⇒ `ℕ)
⊢c3Fn = env (bwf↓ (skip-rvld (skip-rvld here)) (≡→≈ refl) wf-ℕ bwf[])
            (sc-⇒ (sc-var (thereᵒ (thereᵒ hereᵒ))) sc-ℕ)
            (⊢ƛ wf-ℕ ⊢$)

⊢c3Arg : Γq ∣ [] ⊢ c3Arg ⦂ ` 2
⊢c3Arg = env (bwf↓ (skip-rvld (skip-rvld here)) (≡→≈ refl) wf-ℕ bwf[])
             (sc-var (thereᵒ (thereᵒ hereᵒ))) ⊢$

⊢c3Redex : Γq ∣ [] ⊢ c3Redex ⦂ `ℕ
⊢c3Redex = ⊢· ⊢c3Fn ⊢c3Arg

c3Run c3Ob : String
c3Run = traceLog 30 Γq c3Redex
c3Ob  = obligLog 30 Γq `ℕ c3Redex

-- the site's headline: three dropped slots, ZERO demotions — the second
-- chance is what buys the third one
c3-nodemote : demoteCount Γq Θq ≡ 0
c3-nodemote = refl

c3-dual : dualᴳ Γq Θq ≡ rvl `ℕ ∷ rvl `ℕ ∷ rvl `ℕ ∷ []
c3-dual = refl

-- … and WITHOUT the second chance the first slot would be lost: the raw
-- guard really does refuse the chained rep
c3-raw-refused : dfree 0 2 (` 0) ≡ false
c3-raw-refused = refl

c3-unfolded : unfEnt Γq 0 (` 0) ≡ `ℕ
c3-unfolded = refl

------------------------------------------------------------------------
-- §A.4  THE CANCEL PAIR (gauntlet §9a).  Merge then Drop$ to the bare 7;
-- landmarks types-c / types-c′ / types-c″, merge-c-uniq.
------------------------------------------------------------------------

c4Tm : Term
c4Tm = (($ 7) ⟪ Θ1c , ` 0 ⟫) ⟪ Θ2c , ` 0 ⟫

c4Run c4Ob : String
c4Run = traceLog 30 [] c4Tm
c4Ob  = obligLog 30 [] `ℕ c4Tm

c4-cancels : Θ1c ⊕ Θ2c ≡ []
c4-cancels = refl

------------------------------------------------------------------------
-- §A.5  THE EXAMPLE-3-SHAPED TOWER (gauntlet §9c).  Every face is ⇒, so
-- the tower is a VALUE (tower-value) and takes no step (tower-stuck) —
-- the trace is one state long.  Kept because its ⊕ arithmetic is the
-- record of what a merge WOULD compute (tower-ok₁ / tower-ok₂).
------------------------------------------------------------------------

c5Tm : Term
c5Tm = ((Vtw ⟪ Θtw1 , ` 0 ⇒ ` 0 ⟫) ⟪ Θtw2 , ` 0 ⇒ ` 0 ⟫)
         ⟪ Θtw3 , ` 0 ⇒ ` 0 ⟫

c5Run c5Ob : String
c5Run = traceLog 30 Δtw c5Tm
c5Ob  = obligLog 30 Δtw (` 0 ⇒ ` 0) c5Tm

c5-idles : step Δtw c5Tm ≡ nothing
c5-idles = refl

------------------------------------------------------------------------
-- §A.6  THE §9f PROGRAM (gauntlet §9f; EvalProbe §1).  A CLOSED plain
-- System F source (⊢cxP₀), 14 steps to the bare 3.  The one Merge on the
-- run is the LINEAGE cancel at cxP₅.
------------------------------------------------------------------------

c6Run c6Ob : String
c6Run = traceLog 30 [] cxP₀
c6Ob  = obligLog 30 [] `ℕ cxP₀

c6P₈ c6P₉ : Term
c6P₈ = (($ 3) ⟪ Θcx2 , `ℕ ⟫) ⟪ Θcx1 , `ℕ ⟫
c6P₉ = ($ 3) ⟪ Θcx1 , `ℕ ⟫

c6-run : trace 20 [] cxP₀
       ≡ cxP₀ ∷ cxP₁ ∷ cxP₁½ ∷ cxP₂ ∷ cxP₃ ∷ cxP₃½ ∷ cxP₄ ∷ cxP₅
           ∷ cxP₅′ ∷ cxP₅″ ∷ cxP₆ ∷ cxP₇ ∷ c6P₈ ∷ c6P₉ ∷ ($ 3) ∷ []
c6-run = refl

------------------------------------------------------------------------
-- §A.7  THE DOUBLE-COINCIDENCE RUN (gauntlet §9g).  The shape on which
-- FLATTENING IS IMPOSSIBLE (¬ext-d, ¬ext-dX, ¬ext-dZ, ¬γ-dXZ, ¬γ-dWZ) is
-- an ordinary Peel redex, and it runs: the dual of the DOUBLE conceal is
-- the DOUBLE reveal (dual-d), two lineage pairs, and the coincidence is
-- never consulted.  Landmarks ⊢redex-d, ⊢Wd, run-d₁ … run-d₃.
------------------------------------------------------------------------

c7Tm : Term
c7Tm = ((Vd ⟪ Θd1 , Bd1 ⟫) ⟪ Θd2 , Bd2 ⟫) · Wd

c7Run c7Ob : String
c7Run = traceLog 30 Δd c7Tm
c7Ob  = obligLog 30 Δd (` 1) c7Tm

c7-nodemote : demoteCount Δd Θd2 ≡ 0
c7-nodemote = refl

------------------------------------------------------------------------
-- §A.8  THE REVEAL-VARIABLE FACE (gauntlet §9i; EvalProbe §2).  Another
-- closed source (⊢rvQ₀); the only move at rvQ₅ is a Merge
-- (rv-only-merge), and the composite EMPTIES.
------------------------------------------------------------------------

c8Run c8Ob : String
c8Run = traceLog 30 [] rvQ₀
c8Ob  = obligLog 30 [] `ℕ rvQ₀

------------------------------------------------------------------------
-- §A.9  THE STUCK TERM (gauntlet §9m).  ⊢q types it, ¬val-q says it is
-- no value, stuck-q says it takes no step — MergeOK's EXTERNAL-face
-- component fails (¬ext-q).  The LINEAGE contrast (rep ℕ instead of the
-- coincident variable) steps: merge-q′.
------------------------------------------------------------------------

c9Tm c9Tm′ : Term
c9Tm  = (Vq ⟪ Θq1 , ` 0 ⟫) ⟪ Θq2 , ` 0 ⟫
c9Tm′ = (($ 5) ⟪ Θq1′ , ` 0 ⟫) ⟪ Θq2 , ` 0 ⟫

c9Run c9Ob c9Run′ c9Ob′ : String
c9Run  = traceLog 30 Δq c9Tm
c9Ob   = obligLog 30 Δq `ℕ c9Tm
c9Run′ = traceLog 30 Δq c9Tm′
c9Ob′  = obligLog 30 Δq `ℕ c9Tm′

c9-stuck : step Δq c9Tm ≡ nothing
c9-stuck = refl

------------------------------------------------------------------------
-- §A.10  THE PRESERVATION BREAK, FROM A CLOSED SOURCE (gauntlet §9n).
-- ⊢qP₀ types the source at ∀Y.ℕ; ⊢qP₇ types the state before the fatal
-- Peel; ¬⊢qP₈ refutes the state after it (qPreservationFails).
------------------------------------------------------------------------

c10Run c10Ob : String
c10Run = traceLog 30 [] qP₀
c10Ob  = obligLog 30 [] (`∀ `ℕ) qP₀

-- the fatal step's own ambient and boundary, reached by computation
c10-ambient : intOf qΓ2 qΘx ≡ DI.Δd
c10-ambient = qΔ-is-Δd

c10-demote : demoteCount DI.Δd DI.Θ2 ≡ 1
c10-demote = refl

------------------------------------------------------------------------
-- §A.11  THE BREAK'S REDEX ON ITS OWN (DualIntProbe §3.3, §5).
-- DI.⊢Redex types it at ℕ; DI.peel-step fires; DI.¬⊢contractum refutes
-- the contractum.  `step` is type-blind and runs straight through.
------------------------------------------------------------------------

c11Tm : Term
c11Tm = (DI.Vtm ⟪ DI.Θ2 , (` 0 ⇒ ` 0) ⇒ `ℕ ⟫) · DI.Wtm

c11Run c11Ob : String
c11Run = traceLog 30 DI.Δd c11Tm
c11Ob  = obligLog 30 DI.Δd `ℕ c11Tm

c11-dual : dualᴳ DI.Δd DI.Θ2 ≡ rvl⋆ ∷ rvl⋆ ∷ rvl `ℕ ∷ cnc 0 (` 0) ∷ []
c11-dual = refl

c11-rebuild : intOf (intOf DI.Δd DI.Θ2) (dualᴳ DI.Δd DI.Θ2) ≡ DI.Rd
c11-rebuild = DI.rebuild-2

------------------------------------------------------------------------
-- §B.1  N1 — DEPTH-2 CHAINED KNOWLEDGE, THE TWO VARIANTS.
--
-- Both ambients spell slot 0 as a CHAIN "X is Y"; they differ only in
-- what Y is.  The boundary drops BOTH slots, so the raw copy guard
-- refuses the chain in both cases and everything turns on the
-- SECOND-CHANCE retry at the rep unfolded in its own tail.
--
--   n1a  Y:=ℕ   — the tail HAS knowledge, the chain collapses to ℕ, the
--                 copy succeeds: NO demotion.
--   n1b  Y Λ-bound — the tail has NOTHING to unfold, the retry returns
--                 the same variable, and the slot is DEMOTED.
--
-- n1b is the preservation break MINIMIZED: two ambient entries, a
-- REP-LESS conceal, and no third slot.  Everything DualIntProbe §3.3
-- needs survives the minimization.
------------------------------------------------------------------------

Δ1a Δ1b : TCtx
Δ1a = rvld (` 0) ∷ rvld `ℕ ∷ []       -- X:=Y , Y:=ℕ
Δ1b = rvld (` 0) ∷ abst ∷ []          -- X:=Y , Y Λ-bound

Θ1a : BCtx
Θ1a = cnc 1 `ℕ ∷ []                   -- ↓Y:=ℕ   (drops X and Y)

Θ1b : BCtx
Θ1b = rvl (` 0) ∷ cnc⋆ 1 ∷ []         -- ↑?:=X , ↓Y:⋆  (drops X and Y)

-- ---- n1a : the second chance SAVES the chained slot ----

n1a-second-chance : entᴳ Δ1a Θ1a 0 1 ≡ rvl `ℕ
n1a-second-chance = refl

n1a-nodemote : demoteCount Δ1a Θ1a ≡ 0
n1a-nodemote = refl

n1a-dual : dualᴳ Δ1a Θ1a ≡ rvl `ℕ ∷ rvl `ℕ ∷ []
n1a-dual = refl

-- the rebuild recovers knowledge at BOTH slots (one unfolding away from
-- the original, which is exactly what _≼≈_ absorbs)
n1a-rebuild : intOf (intOf Δ1a Θ1a) (dualᴳ Δ1a Θ1a)
            ≡ rvld `ℕ ∷ rvld `ℕ ∷ []
n1a-rebuild = refl

n1a-≼≈ : Δ1a ≼≈ intOf (intOf Δ1a Θ1a) (dualᴳ Δ1a Θ1a)
n1a-≼≈ = ≼≈rvld (≼≈rvld ≼≈[] ≈-refl) (≈unf refl)

n1aFn n1aArg n1aRedex : Term
n1aFn    = (ƛ `ℕ ∙ ($ 8)) ⟪ Θ1a , ` 1 ⇒ `ℕ ⟫
n1aArg   = ($ 3) ⟪ Θ1a , ` 1 ⟫
n1aRedex = n1aFn · n1aArg

⊢n1aFn : Δ1a ∣ [] ⊢ n1aFn ⦂ (` 1 ⇒ `ℕ)
⊢n1aFn = env (bwf↓ (skip-rvld here) (≡→≈ refl) wf-ℕ bwf[])
             (sc-⇒ (sc-var (thereᵒ hereᵒ)) sc-ℕ)
             (⊢ƛ wf-ℕ ⊢$)

⊢n1aArg : Δ1a ∣ [] ⊢ n1aArg ⦂ ` 1
⊢n1aArg = env (bwf↓ (skip-rvld here) (≡→≈ refl) wf-ℕ bwf[])
              (sc-var (thereᵒ hereᵒ)) ⊢$

⊢n1aRedex : Δ1a ∣ [] ⊢ n1aRedex ⦂ `ℕ
⊢n1aRedex = ⊢· ⊢n1aFn ⊢n1aArg

n1aRun n1aOb : String
n1aRun = traceLog 30 Δ1a n1aRedex
n1aOb  = obligLog 30 Δ1a `ℕ n1aRedex

-- ---- n1b : the same chain over a Λ-BOUND tail — DEMOTED ----

n1b-interior : intOf Δ1b Θ1b ≡ xrvld (` 0) ∷ []
n1b-interior = refl

n1b-demoted : entᴳ Δ1b Θ1b 0 1 ≡ rvl⋆
n1b-demoted = refl

n1b-demote-count : demoteCount Δ1b Θ1b ≡ 1
n1b-demote-count = refl

n1b-dual : dualᴳ Δ1b Θ1b ≡ rvl⋆ ∷ rvl⋆ ∷ cnc 0 (` 0) ∷ []
n1b-dual = refl

-- THE REBUILD LOSES BOTH SLOTS: what was X:=Y , Y Λ-bound comes back as
-- two ABSTRACT slots
n1b-rebuild : intOf (intOf Δ1b Θ1b) (dualᴳ Δ1b Θ1b) ≡ abst ∷ abst ∷ []
n1b-rebuild = refl

n1b-¬≼≈ : ¬ (Δ1b ≼≈ intOf (intOf Δ1b Θ1b) (dualᴳ Δ1b Θ1b))
n1b-¬≼≈ ()

-- the crossing value: sealed by ORDINARY knowledge of the demoted slot
Θ1bw : BCtx
Θ1bw = cnc 0 (` 0) ∷ []

n1bW : Term
n1bW = (ƛ (` 0) ∙ (` 0)) ⟪ Θ1bw , ` 0 ⇒ ` 0 ⟫

n1b-w-interior : intOf Δ1b Θ1bw ≡ abst ∷ []
n1b-w-interior = refl

⊢n1bW : Δ1b ∣ [] ⊢ n1bW ⦂ (` 0 ⇒ ` 0)
⊢n1bW = env (bwf↓ here (≡→≈ refl) (wf-var here-abst) bwf[])
            (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
            (⊢ƛ (wf-var here-abst) (⊢` here))

n1bV n1bFn n1bRedex : Term
n1bV     = ƛ (` 0 ⇒ ` 0) ∙ ($ 5)
n1bFn    = n1bV ⟪ Θ1b , (` 0 ⇒ ` 0) ⇒ `ℕ ⟫
n1bRedex = n1bFn · n1bW

⊢n1bFn : Δ1b ∣ [] ⊢ n1bFn ⦂ ((` 0 ⇒ ` 0) ⇒ `ℕ)
⊢n1bFn =
  env (bwf↑ (wf-var here-rvld) (bwf⋆↓ (skip-rvld here-abst) bwf[]))
      (sc-⇒ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)) sc-ℕ)
      (⊢ƛ (wf-⇒ (wf-var here-xrvld) (wf-var here-xrvld)) ⊢$)

-- *** THE MINIMIZED REDEX IS WELL TYPED ***
⊢n1bRedex : Δ1b ∣ [] ⊢ n1bRedex ⦂ `ℕ
⊢n1bRedex = ⊢· ⊢n1bFn ⊢n1bW

n1b-step : Δ1b ⊢ n1bRedex
         -→ (n1bV · (n1bW ⟪ dualᴳ Δ1b Θ1b
                          , renameᵗ (swapᵇ Θ1b) (` 0 ⇒ ` 0) ⟫))
            ⟪ Θ1b , `ℕ ⟫
n1b-step = Peel (V-G G-ƛ) (V-⟪⟫ (V-G G-ƛ) I-⇒)

-- *** AND THE CROSSING VALUE DOES NOT RETYPE IN THE REBUILD *** — both
-- conceal licences ask the rebuild about slot 0, and it is `abst` there
n1b-¬W-rebuild : ¬ ((abst ∷ abst ∷ []) ∣ [] ⊢ n1bW ⦂ (` 0 ⇒ ` 0))
n1b-¬W-rebuild (env (bwf↓  ()  _ _ _)   _ _)
n1b-¬W-rebuild (env (bwf↓x ()  _ _ _ _) _ _)

-- *** SO THE CONTRACTUM HAS NO TYPING AT ALL: the break, minimized ***
n1b-¬contractum : ¬ (Δ1b ∣ []
  ⊢ (n1bV · (n1bW ⟪ dualᴳ Δ1b Θ1b
                  , renameᵗ (swapᵇ Θ1b) (` 0 ⇒ ` 0) ⟫))
      ⟪ Θ1b , `ℕ ⟫ ⦂ `ℕ)
n1b-¬contractum (env _ _ (⊢· (⊢ƛ _ _) (env _ _ ⊢W))) =
  n1b-¬W-rebuild ⊢W

n1bRun n1bOb : String
n1bRun = traceLog 30 Δ1b n1bRedex
n1bOb  = obligLog 30 Δ1b `ℕ n1bRedex

------------------------------------------------------------------------
-- §B.2  N2 — THE DOUBLE CROSSING, from a CLOSED source.  One sealed
-- value crosses two DIFFERENT reveals in sequence:
--
--   N2 = ((ΛX. λx:X. ((ΛY. λy:Y. 1) [X]) · x) ·[ X⇒ℕ , ℕ ]) · 5
--
-- TyBeta(X) mints ↑X:=ℕ; the Peel seals 5 as ↓X:=ℕ; INSIDE that
-- boundary TyBeta(Y) mints ↑Y:=X — a rep naming a KNOWLEDGE slot — and
-- the second Peel crosses the ALREADY-SEALED 5 through that reveal's
-- dual.  Dual-of-dual in the flesh.
------------------------------------------------------------------------

n2Src : Term
n2Src =
  ((Λ (ƛ (` 0) ∙ (((Λ (ƛ (` 0) ∙ ($ 1))) ·[ ` 0 ⇒ `ℕ , ` 0 ]) · (` 0))))
     ·[ ` 0 ⇒ `ℕ , `ℕ ]) · ($ 5)

⊢n2Src : [] ∣ [] ⊢ n2Src ⦂ `ℕ
⊢n2Src =
  ⊢· (⊢·[] (⊢Λ (⊢ƛ (wf-var here-abst)
                   (⊢· (⊢·[] (⊢Λ (⊢ƛ (wf-var here-abst) ⊢$))
                             (wf-var here-abst))
                       (⊢` here))))
           wf-ℕ)
     ⊢$

n2Run n2Ob : String
n2Run = traceLog 30 [] n2Src
n2Ob  = obligLog 30 [] `ℕ n2Src

------------------------------------------------------------------------
-- §B.3  N3 — A RETURNED BOUNDARY, USED AGAIN.  The package's ∀-body
-- returns a FUNCTION over the abstract variable, so the residue of the
-- first crossing is a wrapper at an ⇒ face which is then APPLIED:
--
--   N3 = ((ΛX. λh:(ℕ⇒X). λz:X. 9) ·[ (ℕ⇒X)⇒(X⇒ℕ) , ℕ ] · (λn:ℕ. n)) · 4
--
-- The boundary comes back OUT on the codomain side and is peeled a
-- SECOND time — the outbound bookkeeping, on a closed source.
------------------------------------------------------------------------

n3Src : Term
n3Src =
  (((Λ (ƛ (`ℕ ⇒ ` 0) ∙ (ƛ (` 0) ∙ ($ 9))))
      ·[ (`ℕ ⇒ ` 0) ⇒ (` 0 ⇒ `ℕ) , `ℕ ])
    · (ƛ `ℕ ∙ (` 0))) · ($ 4)

⊢n3Src : [] ∣ [] ⊢ n3Src ⦂ `ℕ
⊢n3Src =
  ⊢· (⊢· (⊢·[] (⊢Λ (⊢ƛ (wf-⇒ wf-ℕ (wf-var here-abst))
                       (⊢ƛ (wf-var here-abst) ⊢$)))
               wf-ℕ)
         (⊢ƛ wf-ℕ (⊢` here)))
     ⊢$

n3Run n3Ob : String
n3Run = traceLog 30 [] n3Src
n3Ob  = obligLog 30 [] `ℕ n3Src

------------------------------------------------------------------------
-- §B.4  N4 — AN x-ENTRY CONSULTED AFTER ONE MORE DUAL.  *** A SECOND,
-- INDEPENDENT PRESERVATION BREAK. ***
--
-- Γz = Z:=ˣY is E★′'s own sealed interior (gauntlet §1.3, xlic-E★′), so
-- the configuration is plantable.  The value `Val` (strong.Boundary's
-- ⊢3s-alias example) is licensed there by (bwf-↓x) — the ONE clause that
-- consults an x-entry.  Put it through a Peel whose boundary drops the
-- x-slot: entᴳ's xrvld branch emits rvl⋆ UNCONDITIONALLY, the rebuild has
-- `abst` at that slot, and the x-licence dies exactly as the ordinary one
-- does in n1b / DualIntProbe §3.3.
------------------------------------------------------------------------

Θ4 : BCtx
Θ4 = rvl (` 0) ∷ cnc⋆ 0 ∷ []           -- ↑?:=Z , ↓Z:⋆

n4-interior : intOf Γz Θ4 ≡ xrvld (` 0) ∷ []
n4-interior = refl

n4-demoted : entᴳ Γz Θ4 0 0 ≡ rvl⋆
n4-demoted = refl

n4-demote-count : demoteCount Γz Θ4 ≡ 1
n4-demote-count = refl

n4-dual : dualᴳ Γz Θ4 ≡ rvl⋆ ∷ cnc 0 (` 0) ∷ []
n4-dual = refl

n4-rebuild : intOf (intOf Γz Θ4) (dualᴳ Γz Θ4) ≡ abst ∷ []
n4-rebuild = refl

-- the crossing value is strong.Boundary's own x-licensed alias
n4W : Term
n4W = (ƛ ` 0 ∙ ($ 5)) ⟪ Ξalias , ` 1 ⇒ `ℕ ⟫

⊢n4W : Γz ∣ [] ⊢ n4W ⦂ (` 0 ⇒ `ℕ)
⊢n4W = env (bwf⋆ (bwf↓x herex refl sk-var (wf-var here-abst) bwf[]))
           (sc-⇒ (sc-var (thereᵒ hereᵒ)) sc-ℕ)
           (⊢ƛ (wf-var here-abst) ⊢$)

n4V n4Fn n4Redex : Term
n4V     = ƛ (` 0 ⇒ `ℕ) ∙ ($ 6)
n4Fn    = n4V ⟪ Θ4 , (` 0 ⇒ `ℕ) ⇒ `ℕ ⟫
n4Redex = n4Fn · n4W

⊢n4Fn : Γz ∣ [] ⊢ n4Fn ⦂ ((` 0 ⇒ `ℕ) ⇒ `ℕ)
⊢n4Fn = env (bwf↑ (wf-var here-xrvld) (bwf⋆↓ here-xrvld bwf[]))
            (sc-⇒ (sc-⇒ (sc-var hereᵒ) sc-ℕ) sc-ℕ)
            (⊢ƛ (wf-⇒ (wf-var here-xrvld) wf-ℕ) ⊢$)

-- *** WELL TYPED ***
⊢n4Redex : Γz ∣ [] ⊢ n4Redex ⦂ `ℕ
⊢n4Redex = ⊢· ⊢n4Fn ⊢n4W

n4-step : Γz ⊢ n4Redex
        -→ (n4V · (n4W ⟪ dualᴳ Γz Θ4
                       , renameᵗ (swapᵇ Θ4) (` 0 ⇒ `ℕ) ⟫))
           ⟪ Θ4 , `ℕ ⟫
n4-step = Peel (V-G G-ƛ) (V-⟪⟫ (V-G G-ƛ) I-⇒)

-- *** AND THE x-LICENCE DIES IN THE REBUILD ***  (bwf-↓x) needs an
-- x-entry at slot 0 and the rebuild has `abst`; (bwf-↓) needs ordinary
-- knowledge, which was never there.
n4-¬W-rebuild : ¬ ((abst ∷ []) ∣ [] ⊢ n4W ⦂ (` 0 ⇒ `ℕ))
n4-¬W-rebuild (env (bwf⋆ (bwf↓  ()  _ _ _))   _ _)
n4-¬W-rebuild (env (bwf⋆ (bwf↓x ()  _ _ _ _)) _ _)

n4-¬contractum : ¬ (Γz ∣ []
  ⊢ (n4V · (n4W ⟪ dualᴳ Γz Θ4 , renameᵗ (swapᵇ Θ4) (` 0 ⇒ `ℕ) ⟫))
      ⟪ Θ4 , `ℕ ⟫ ⦂ `ℕ)
n4-¬contractum (env _ _ (⊢· (⊢ƛ _ _) (env _ _ ⊢W))) = n4-¬W-rebuild ⊢W

n4Run n4Ob : String
n4Run = traceLog 30 Γz n4Redex
n4Ob  = obligLog 30 Γz `ℕ n4Redex

------------------------------------------------------------------------
-- §B.5  N5 — A Λ-BOUND-REP REVEAL CROSSED TWICE.  E★′'s own boundary
-- Θ★ = ↑Z:=Y , ↓X:=ℕ at Γ★ = Y Λ-bound , X:=ℕ.  Its dual emits ↑Y:⋆ at
-- the Λ-bound slot — a rvl⋆ that is NOT a demotion, because Y really was
-- abstract — and the SECOND crossing (the dual of the dual) restores it
-- with cnc⋆.  The round trip is EXACT: intOf Γ★ dd ≡ Γz (gauntlet §4).
------------------------------------------------------------------------

n5-cross₁ : demoteCount Γ★ Θ★ ≡ 0
n5-cross₁ = refl

n5-cross₂ : demoteCount Γz dualᵛ ≡ 0
n5-cross₂ = refl

n5-dual-of-dual : dualᴳ Γz dualᵛ ≡ dd
n5-dual-of-dual = refl

n5-roundtrip : intOf Γ★ dd ≡ Γz
n5-roundtrip = refl

-- and the twice-crossed value still types (§1.3's ⊢W′ inside §4's ⊢dd)
n5Tm : Term
n5Tm = W′ ⟪ dd , ` 0 ⇒ `ℕ ⟫

n5Run n5Ob : String
n5Run = traceLog 30 Γ★ n5Tm
n5Ob  = obligLog 30 Γ★ (` 0 ⇒ `ℕ) n5Tm

------------------------------------------------------------------------
-- §C  CROSS-CORPUS FACTS, machine-checked.
------------------------------------------------------------------------

-- §C.1  THE MINT CLASSIFIER, on the two decisive mints.  E★′'s TyWrap
-- mints a rep naming a Λ-BOUND slot and its crossing is SAFE; §9n's
-- TyWrap mints a rep naming a KNOWLEDGE slot — a CHAINED spelling — and
-- its crossing is the preservation break.
class-E★′ : repClass Γ★ (` 0) ≡ "names-Λ-bound {X:Λ-bound}"
class-E★′ = refl

class-break : repClass DI.Δd (` 0)
            ≡ "names-KNOWLEDGE-carrying-slot (chained) {X:KNOWLEDGE}"
class-break = refl

-- and the chain's own target is the Λ-bound slot: the break needs BOTH
-- levels — a chained rep whose target is abstract
class-break-tail : repClass (abst ∷ rvld `ℕ ∷ []) (` 0)
                 ≡ "names-Λ-bound {X:Λ-bound}"
class-break-tail = refl

-- §C.2  A DEMOTION IS NEVER AT AN ABSTRACT SLOT.  `entᴳ`'s rvl⋆ fallback
-- is reached from three entry shapes, and only two of them lose
-- anything; at `abst` there was nothing to lose.  (This is the general
-- statement behind every "rvl⋆-at-abst (harmless)" line of the survey.)
demote-not-abst : ∀ (Δ₁ : TCtx) (i k : ℕ) → demoteE abst Δ₁ i k ≡ false
demote-not-abst Δ₁ i k = refl

-- … and at the OTHER two entry shapes it can happen: an x-entry loses
-- UNCONDITIONALLY, a knowledge entry loses when both copy guards refuse
demote-x-always : ∀ (Δ₁ : TCtx) (B : Ty) (i k : ℕ)
                → demoteE (xrvld B) Δ₁ i k ≡ true
demote-x-always Δ₁ B i k = refl

-- §C.3  A CONCEALED SLOT IS NEVER DEMOTED EITHER: the dual re-reveals it
-- at the boundary's own conceal rep.
demote-not-conc : ∀ (Δ₁ : TCtx) (Θ₁ : BCtx) (i k : ℕ)
                → isConc i Θ₁ ≡ true → isDemote Δ₁ Θ₁ i k ≡ false
demote-not-conc Δ₁ Θ₁ i k eq =
  cong (λ b → if b then false else demoteE (entAt Δ₁ i) Δ₁ i k) eq

-- §C.4  … SO EVERY DEMOTION IS AT A KNOWLEDGE-CARRYING SLOT THE
-- BOUNDARY DROPS WITHOUT CONCEALING — `rvld` or `xrvld`.  That is the
-- whole of the knowledge-destroying step, and the corpus's three
-- typability losses (c10/c11, n1b, n4) are exactly its three instances.
demote-count-safe : demoteCount Γ★ Θ★ ≡ 0
demote-count-safe = refl

demote-count-c3 : demoteCount Γq Θq ≡ 0
demote-count-c3 = refl

demote-count-c7 : demoteCount Δd Θd2 ≡ 0
demote-count-c7 = refl

demote-count-rv : demoteCount Ψr Θrᵈ ≡ 0
demote-count-rv = refl

demote-count-n1a : demoteCount Δ1a Θ1a ≡ 0
demote-count-n1a = refl

demote-count-n1b : demoteCount Δ1b Θ1b ≡ 1
demote-count-n1b = refl

demote-count-n4 : demoteCount Γz Θ4 ≡ 1
demote-count-n4 = refl

demote-count-break : demoteCount DI.Δd DI.Θ2 ≡ 1
demote-count-break = refl

-- §C.5  *** THE JOINT SIGNATURE OF A DEMOTING CROSSING. ***  All four
-- boundaries below have the SAME interior shape — one reveal whose rep
-- names a BLOCKED slot, so the fallback chain lands on `xrvld` — and
-- they are told apart by ONE thing: what the AMBIENT holds at the named
-- slot.  E★′'s is `abst`, and the ⋆ the dual emits there is harmless;
-- the other three hold knowledge, and it is destroyed.
sig-E★′-int : intOf Γ★ Θ★ ≡ xrvld (` 0) ∷ []
sig-E★′-int = refl

sig-E★′-target : entAt Γ★ 0 ≡ abst                 -- SAFE
sig-E★′-target = refl

sig-break-int : intOf DI.Δd DI.Θ2 ≡ xrvld (` 0) ∷ []
sig-break-int = refl

sig-break-target : entAt DI.Δd 0 ≡ rvld (` 0)      -- BROKEN
sig-break-target = refl

sig-n1b-int : intOf Δ1b Θ1b ≡ xrvld (` 0) ∷ []
sig-n1b-int = refl

sig-n1b-target : entAt Δ1b 0 ≡ rvld (` 0)          -- BROKEN
sig-n1b-target = refl

sig-n4-int : intOf Γz Θ4 ≡ xrvld (` 0) ∷ []
sig-n4-int = refl

sig-n4-target : entAt Γz 0 ≡ xrvld (` 0)           -- BROKEN
sig-n4-target = refl

-- §C.6  EVERY MERGE THAT FIRES IN THE CORPUS EMPTIES THE BOUNDARY.
-- Not one of them produces a composite with entries left.
mrg-∅-c4 : Θ1c ⊕ Θ2c ≡ []
mrg-∅-c4 = refl

mrg-∅-c6 : Θcx2 ⊕ Θcx1 ≡ []
mrg-∅-c6 = refl

mrg-∅-c7 : Θd2 ⊕ dualᴳ Δd Θd2 ≡ []
mrg-∅-c7 = run-d-∅

mrg-∅-c8 : Θrᵈ ⊕ Θr ≡ []
mrg-∅-c8 = refl

mrg-∅-c9′ : Θq1′ ⊕ Θq2 ≡ []
mrg-∅-c9′ = refl
