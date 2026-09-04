# The preservation endgame: closing the three DualDef residues
# (plan written 2026-09-05, at Jeremy's "speed up the push to finish
# preservation"; three probe/proof agents launched in parallel)

Preservation (`BPreservation.Impl`) is proven in every rule case and is
parameterized by exactly three statements about the ambient dual
`Θᵈ = dualᴳ Δ Θ` that Peel mints at a crossing (strong/DualDef.agda):
`DualRep≈`, `DualCnc≈`, `DualInt≈`.  `bwf-dual` proves these three are
the WHOLE residue.  This file is the plan for closing them.

## Truth-status analysis (why each track is probe-first)

None of the three should be assumed true as stated; each has a known
suspect corner, and a refutation with a repaired statement is a better
deliverable than a stalled grind.

### DualRep≈ (the copied-rep well-formedness) — suspected FALSE without ⊢ᶜ Δ

Nothing in the hypothesis `Δ ∣ intOf Δ Θ ⊢ᵇ Θ` constrains Δ's OWN
entries: a Δ whose `rvld B` stores garbage B refutes the conclusion.
The repair is the classic store-typing pattern: a context
well-formedness judgment `⊢ᶜ Δ` (each entry's type wf in its own tail),
threaded through preservation as a new premise.  The real work is the
threading lemmas — `⊢ᶜ (abst ∷ Δ)`, and crucially
`⊢ᶜ Δ → bwf → ⊢ᶜ (intOf Δ Θ)` (the interior's ⟦_⟧ᴴ-minted entries are
wf), so every ξ case carries the invariant.  NOTE: this changes the
top-level preservation STATEMENT (`⊢ᶜ Δ → Δ ∣ [] ⊢ M ⦂ A → …`) — a
Jeremy check-in item when the agent reports (standing rule: major
statements shown before install).  Grounded-invariants reading: ⊢ᶜ is
minted by compile ([] trivially) and preserved by reduction — a legal
invariant-in-the-relation, not a companion predicate (it indexes the
theorem, not the syntax).

### DualInt≈ (the rebuild law) — suspected FALSE at two slot kinds

`_≼≈_` has no clause admitting LEFT xrvld / RIGHT abst nor LEFT rvld /
RIGHT abst, and the dual re-reveals exactly those slots rep-lessly when
(i) Δ's entry is exterior-read (entᴳ-x), or (ii) both copy guards refuse
(entᴳ-B⋆) — the rebuild then has `abst` where Δ has knowledge.  Two
repair routes, the probe decides:
  (i) weaken ≼≈ (right-abst absorbs anything) IFF ⊢retag≈/≼≈-⊢ can
      tolerate it — they cannot in general (a crossing term whose typing
      consumed the lost knowledge), so this route needs the analysis
      "no well-typed crossing uses the lost slots";
  (ii) hypothesize the bad slots away and track where the hypothesis
      comes from (reachability invariant, or a Peel-premise in the
      MergeOK style).

### DualCnc≈ (the conceal license) — the sharp one; PLAN below

`CncLic Ψ Θᵈ k (ρᵇ Θ k)`: ordinary disjunct (∋:= + Reversal≈) or
x-disjunct (∋:=x + starOnly + SkelEq).  Proven around it: the x-lookup
exists whenever the raw reading is blocked (revE-lo:=x), SkelEq is free
at birth (xrep-stored / dual-cnc-skel), rep-wf free given DualInt≈
(dual-rep-ok), the ⋆ half free (cnc⋆-licensed).  THE RESIDUE is
starOnly — "the conceal's rep claims nothing" — and it is caught in a
design TENSION built into dualᴳ itself:

    Pc needs the SECOND-CHANCE COPY: the dual re-reveals a chained slot
    REP-CARRYINGLY so the rebuild keeps the knowledge the crossing term
    retypes against (the Γp/Γp′ one-unfolding-away pattern).
    Pn needs the OPPOSITE: the conceal's rep names that re-revealed
    slot, and the license demands it be REP-LESS (starOnly).

  The copy that saved Pc is exactly what kills Pn's license.

THE CRUX QUESTION (probe Q2): can the two demands ever target the SAME
slot of one boundary?  If NOT — if the slots some conceal rep names and
the slots whose copied knowledge a crossing can consume are provably
disjoint — then the repair is PER-SLOT COPY SUPPRESSION (Q3):

    dualᴳ′ = dualᴳ, but emit rvl⋆ at exactly the slots named by some
    conceal rep of the emitted block (decidable, birth-time, grounded).

  Pn's license then holds via the x-disjunct; Pc's slot is untouched.
  Cost to check: DualInt≈'s case at a suppressed slot.
If the demands CAN collide, the fallback is Q4: weaken starOnly to
"claims nothing NEW" (a variable may name a rep-carrying reveal whose
stored rep agrees with the transported knowledge) — but ANY such
comparison must be renaming-stable (the D1 lesson: SkelEq-form, never a
raw ≈ against a movable home), and must re-refute the ⊢3n-adv adversary
family that starOnly exists to block.  If neither works, the remaining
move is a typing strengthening minting the license at the boundary's
birth (grounded-invariants law), with TyBeta/Peel as the minting sites.

## Sequencing

1. (running) MergeOK repair → progress unconditional.  Independent.
2. (running) DualRep≈ agent → expected: ⊢ᶜ Δ + threading lemmas +
   repaired statement.  Jeremy confirms the preservation-statement
   change.
3. (running) DualInt≈ agent → expected: refutations at the two corners +
   the strongest true version + the ⊢retag≈ analysis.
4. (running) DualCnc≈ probe → the Q1–Q4 verdicts feed the design ruling
   (suppression vs starOnly′ vs birth-time minting) — Jeremy rules with
   the probe's examples on the table.
5. Assembly landing: repaired statements installed, `bwf-dual`
   re-assembled, `BPreservation.Impl` instantiated, top-level
   `preservation` (and `TypeSafety.agda`, PLAN §9 step 3) stated with
   whatever context invariant (⊢ᶜ Δ) the repairs require.
