# Design dossier: rigid type variables meeting ★ (source consistency)

Status: FOR DISCUSSION — no implementation. Branch
agent/gtsf-source-consistency. Companion: SRCCONSIST-INVENTORY.md
(full classified site table), SrcConsistBlocked.agda (the checked
negative witness: the gate failure for (ΛX. λx:X. (λy:★. y) · x)).

## 1. The problem

The ground judgments `_⊢_∼★` / `_⊢★∼_` admit variables only via
`X∼★ᵍ : μ X ≡ X∼★` and `★∼Xᵍ : μ X ≡ ★∼X`. Rigid mode X∼X has no
path to ★ from either side, so `？`/`！` casts at rigid variables are
unformable, and the canonical tag-minting programs — dynamic code
inside polymorphic code — are untypable. The blocked witness fails
exactly at `idᶜ Fin.zero ≡ ★∼X` instance search.

## 2. Intended semantics

At rigid mode, a variable meeting ★ is name-tag minting: the runtime
witness is the EXISTING tag/untag forms (X! / X?), whose semantics
already implement name protection (tag-untag at the same name
succeeds; different names blame; ground equality, not gate mode,
decides — Reduction.agda:196-212, Eval.agda:240-259). No new runtime
form is needed. Canonical forms at ＇X are unaffected (variable tags
classify values at ★, not at ＇X).

## 3. What the inventory says about risk

GOOD: the entire DGG stack — tightened partner discipline
(Rep★PartnerOK and friends), var-tag-value-sealed, seal-transfer,
the M3 inversion stack, catch-up lemmas — is class (a)/(c): gate
evidence is opaque; arguments key on alignment and term shape, never
on mode equalities. Rigid-gated tags flow through unchanged.

THE REAL (b) CLUSTER, four bases:
 1. Substitution (Consistency.agda:549-654, 778-800, 896-927):
    SubstEnv∼ has exact-mode obligations (to-★ / from-★). A rigid
    gate under substitution X ↦ C turns X! into a C ∼ ★ cast for
    ARBITRARY C — the machinery needs a rigid obligation, which is
    satisfiable iff `C ∼ ★` is total. NOTE: with rigid gates added,
    every-type-∼-★ plausibly BECOMES derivable (today it fails
    precisely at rigid variables) — the fix may close its own
    substitution story. Needs a totality lemma (to-★ : ∀ C → μ ⊢ C ∼ ★)
    as part of the design validation.
 2. Occurrence lemmas (proof/Consistency2.agda:217-373): "variable
    occurs in a ground meeting ★ ⇒ its mode is dynamic on that side"
    — false under rigid gates. Consumers (occurrence safety,
    dynamic-side conclusions) need per-site repair or weakened
    statements.
 3. Lower-bound theory (proof/ImprecisionConsistency.agda:355-489,
    610-744, 1506-1578): variable tag/projection cases consume exact
    modes; `ground-self-occurs⊥` IS the exclusivity and dies with the
    fix; its consumers need repair. VarLower already allows X∼X to be
    both-to-star (32-43) — the likely repair route for common-lower
    at rigid tags.
 4. Progress (proof/TypeSafety/Progress.agda:231-265):
    `consistency-to-fresh : extᵐ μ ⊢ A ∼ ＇0 → A ≡ ＇0` gains an
    A ≡ ★ case; no-bot-value needs a corresponding repair.

Compile is additive: ⊢ᴳ· compiles via symᶜ of the witness; ⊢ᴳ·★
takes it directly; both accept rigid-gated witnesses once formable
(Compile.agda:82-90). compile-preserves-imprecision² and the catalog
gain cases/examples, not repairs.

## 4. Sibling calibration (a design question, not just a fact)

- GTSF (the sibling): ALSO rejects rigid-var-to-★ — its ordinary ∀
  consistency rule adds only `0 ~ᶜ 0`; the dynamic-side assumptions
  `X ~ᶜ★`/`★~ᶜ X` enter only at forall-vs-nonforall. If GTSFImp's
  intended design admits the minters, GTSF likely has the same latent
  gap.
- PolyG: unmoded surface consistency, `A ∼ Dyn` always.
- PolyBlameI: `Ground` excludes rigid variables; tagging to ★ is
  ground-only.
- λB / GSF lineage (external): casts between X and ★ are the sealing
  mechanism itself — rigid-var-to-★ is admitted. The fix aligns
  GTSFImp with that lineage and diverges from the in-repo siblings.

## 5. Options

(A) RIGID GATES (recommended): add `X∼★ʳ : μ X ≡ X∼X → μ ⊢ ＇X ∼★`
    and mirror `★∼Xʳ`, plus instances. Symmetry is free
    (flipVar∼ X∼X = X∼X). Runtime = existing tag/untag. Cost: the
    four (b)-cluster repairs above; everything else extends
    mechanically per the inventory.
(B) GTSF-STYLE mode switching at binders (type ∀-bodies with a
    dynamic-side mode when they contain dynamic code): rejected on
    inspection — the needed witness sits at an ordinary application
    under an ordinary ∀; there is no principled local trigger to
    switch modes, and it changes what ∀-types mean.
(C) A FOURTH Var∼ value ("rigid-dynamic"): complicates the mode
    lattice and every flipᵐ/extᵐ lemma for no expressiveness gain
    over (A).
(D) A DEDICATED name-tag cast form (leave ？/！ and the ground
    judgments untouched; add a parallel constructor with its own
    typing/reduction): isolates the exclusivity lemmas (they stay
    true for ？/！), converting the (b)-cluster into additive new
    cases. Cost: duplicates tag/untag runtime forms and doubles the
    cast surface in every proof over casts; the DGG stack's opaque
    treatment means (A) already flows through it — (D) would NOT
    (new constructor = new cases everywhere in the DGG stack too).

## 6. Recommendation and validation plan

Recommend (A). The runtime semantics is already present; the DGG
stack is provably indifferent; the (b)-cluster is finite, named, and
each repair has a visible route (rigid SubstEnv∼ obligation via a
to-★ totality lemma; occurrence lemmas weakened per consumer;
lower-bound via the both-to-star VarLower route; consistency-to-fresh
disjunction). Divergence from GTSF should be a conscious decision —
possibly with a follow-up TODO for GTSF.

Validation plan (before any live edit, per house discipline):
 P1. Scratch-model the rigid gates + the to-★ totality lemma.
 P2. Scratch-repair the four (b) clusters against the model
     (statement-first; the exact sites are in the inventory table).
 P3. Type the minter programs end-to-end in scratch (source typing,
     compile, a reduction trace minting a rigid tag) — including the
     PPRIME/ROUNDTRIP examples that motivated the TODO.
 P4. Re-run the DGG gate battery unmodified (expected: green, per the
     inventory's opacity findings).
Then the live migration in the usual pre-flight → live loop.

## 7. Open questions for discussion

 Q1. Should ∼ become total-to-★ (every type consistent with ★) as a
     THEOREM after the fix, and do we WANT that (it is the λB/GSF
     norm)? The substitution story appears to require it.
 Q2. One gate or two: admit rigid variables in BOTH ∼★ and ★∼ (full
     symmetry, recommended) or only the minting direction?
 Q3. Fix GTSF the same way (follow-up TODO), or is GTSFImp
     deliberately more permissive than the sibling?
 Q4. Mode of the rigid tag under the NEW contravariant _↦_: rigid
     gates are flipᵐ-fixed points, so domain positions are
     unaffected — confirm no interaction wanted here.
