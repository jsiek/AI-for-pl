# Design memo: the pedigree index of Rep★PartnerOK (rounds 14-17)

## Where the migration stands

One sub-head remains between the tightening and M3 completion: in
`emit-tagged-transfer`'s target-only-peel branch, the source-seal
sub-head must re-emit a paired star seal, and the partner witness it
holds has target pedigree Yᵖ (the inner rebase's pairing) while the
demanded package index is Y (the outer peel's pairing). Consecutive
same-pivot rebases legitimately have different targets, so no
uniqueness theorem can identify them.

Everything else is done and green: premise-world partner predicates,
partner-flow inversion, var-tag-value-sealed, the see-through
round-trip clause with X₂ ≢ X orthogonalization, the transport
principle (witness induction, total), the tagged-transfer surface,
all probes/examples/catalog gates, and the support lemmas
(aligned-functional, decay-rep★-round-trip). The two worker
postulates fall to already-validated emptiness proofs the moment the
sub-head closes.

## Three candidates, three verdicts (all scratch-checked)

1. PROPAGATED pedigree (current live): the round-trip clause passes
   the outer pedigree into its recursive premise. Sound, but the
   round-16 site cannot discharge: Yᵖ ≠ Y.
2. FREED pedigree (pre-flight 6): recursive premise pedigree
   existential. UNSOUND, three ways: the round-15 emptiness
   counterexample reopens, wrong-pedigree laundering succeeds, the
   worker emptiness payoffs break.
3. ANCHORED-INNER pedigree (pre-flight 7): recursive premise pedigree
   must be X's actual alignment in the witness's world. Closes the
   nothing-pedigree attacks and discharges the round-16 sub-head
   locally, but the clause's OUTER index is then unconstrained, so
   arbitrary-pedigree packages still form (round-15 reopens) and the
   anchored-just transport is not definable.

## The crisp question (yours to call, Jeremy)

What does the Xᴿ? index of Rep★PartnerOK MEAN?

(A) A conclusion-world pairing pin: "this partner story is about the
    seal that pairs X with Y", where Y is pinned EXTERNALLY by the
    consuming rule's RebaseAt — mixing a conclusion-world name into a
    premise-world predicate. Under this reading the predicate should
    arguably not constrain the index internally at all; the round-15
    "emptiness at arbitrary Y₂" stops being the right sanity
    criterion (the rule, not the predicate, rejects bad pairings),
    and the emptiness payoffs must be re-derived from the
    nothing-pedigree and clause-content sides only (pre-flight 7
    shows those survive anchoring). Repair: freed-or-anchored clause
    PLUS restated emptiness criteria; requires re-validating the
    worker-clause payoffs under the new criteria.

(B) Premise-world protection content: the pedigree is part of what
    the discipline protects, and the predicate must constrain it in
    every clause. Then the round-16 demand itself is wrong — the
    re-emission is asking for the partner in world W₂ at a pairing
    that only exists in W₀ — and the fix is not in the predicate but
    in the re-emission's world plumbing: the paired rule's premise
    world for the new (X,Y) pairing should be one where the partner's
    pedigree statement is coherent (e.g. package the partner at the
    PRE-rebase pairing Yᵖ and let the rule's RebaseAt carry it to Y,
    the way q already rides the rebase).

My read: (B) is more conservative and matches the premise-world
principle that has won every previous round; concretely it means the
paired-conceal rule's MatchedConcealPartnerOK index should be the
rule's PREMISE-world pairing (Yᵖ = X's pre-rebase partner), with the
conclusion-world Y appearing only in RebaseAt/q. That is a one-index
change to the rule surface, not to the protection clauses, and every
site we have examined holds the pre-rebase alignment natively.
But it is your relation and the index semantics are a design
commitment the DGG simulation will live with through M7/M8.

## Cost of each path

(A): clause change + emptiness re-derivation + re-run of the full
     laundering battery + worker payoff re-validation. One pre-flight
     plus a live round.
(B): rule-surface index change (MatchedConcealPartnerOK pedigree =
     premise-world pairing) + mechanical updates at paired-seal
     emission sites (probes already hold pre-rebase alignments) +
     the round-16 sub-head then discharges with the witness AS HELD.
     One pre-flight plus a live round.

Both paths keep: the tightened discipline, see-through, transport,
tagged transfer, and all landed green work.
