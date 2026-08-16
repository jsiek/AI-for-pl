LG-3 paired target-cast inversion: post-source endpoint gap

Status: open as of 2026-08-16.

The target-only exposed cells in
`Catchup/TargetCastStepInversionProof.agda` now check for identity, ground
split, expansion split, and the generated-projection replacement aliases.
The paired identity cell also checks:

`cast⊑cast² c id prem q` followed by `β-id` replays as `cast⊑² c prem q`.

The generic paired non-identity rows still resist.  The core obstruction is
not the target cast classification; it is the missing endpoint witness after
the source cast.

For a target ground split, the paired CTI head has the shape

`cast⊑cast² c c′ prem q`

with premises corresponding to

`c  : C ∼ A`
`c′ : B ∼ G`
`prem : C ⊑ B`
`q : A ⊑ ★`

and the target step is

$$
M' \langle c' ! \rangle
\longrightarrow
M' \langle c' \rangle \langle G ! \rangle .
$$

To rebuild the reduct with the paired source cast first, the direct
constructor path needs

`A ⊑ G`

so it can form

`cast⊑cast² c c′ prem (A⊑G)`

and then reapply the target tag.  The checked target-only lemma
`ground-cast-target⊑` recovers `C ⊑ G` from `C ⊑ B` and `C ⊑ ★`, but the
paired constructor supplies `A ⊑ ★`, not `C ⊑ ★`, and it does not relate the
source cast endpoint `A` to the target ground `G`.

For a matched projection, the paired head has

`c′ : ★ ∼ G`, `prem : C ⊑ ★`, and `q : A ⊑ G`.

After the projection step, right-injection inversion can remove a visible
target tag only from a relation to `N ⟨ G ! ⟩`.  Replaying the source-only
cast at that tag layer needs

`A ⊑ ★`,

while the paired head supplies only the pre-source-cast `C ⊑ ★` and the final
`A ⊑ G`.

The legacy source-strip code has positive paired handling only under much
more specific source-spine/inert-variable-tag hypotheses, and several of
those branches are legacy `NON_COVERING` debt.  A total wrapper-aware theorem
therefore needs either:

- a new checked endpoint-transport lemma that recovers the post-source witness
  from the value/inert source shape plus the paired CTI head; or
- a narrowed paired-cell statement that carries the exact source-spine
  hypotheses required by the legacy strip/target-chain machinery.

No CTI relation change has been made.
