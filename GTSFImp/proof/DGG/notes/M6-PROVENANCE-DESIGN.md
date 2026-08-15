# M6 Driver Provenance Design

Date: 2026-08-11. Status: option (A), driver, and fuel knot live; the closed
theorem awaits only the M5 instantiation factory.

Update, 2026-08-13: the pre-flight described below has landed in
`Catchup/ValueCatchupRightDef.agda`.  `CatchupCast⁻`, `CatchupColumn⁻`,
`CatchupColumn`, `ValueCatchupRightProv²`, the fuel-indexed `...At`
interfaces, and `FuelKnot` are now the live M6 surface.  The decrease,
column-size, world-extension, context-composition, reduction-composition,
column-lifting, and `catchup⁻-embed` support is proved in
`Catchup/ColumnSupportProof.agda`.  The fuel-aware extra-cast worker, column
driver, and `Acc _<_` knot are live in `Catchup/ExtraCastRightAtProof.agda`,
`Catchup/ValueCatchupRightProof.agda`, and `Catchup/FuelKnotProof.agda`.
This memo remains the rationale for that surface, not a pending choice among
(A), (B), and (C).

## The gap (checked)

The M6 design scratch's driver surface

    ValueCatchupRight² : ... → (κ : CastColumn B B′) → (q : A ⊑ᵂ⟨W⟩ B′) → ...

takes an arbitrary cast column with NO provenance premise. It is FALSE:
instantiated at the singleton column `Y?` with the QHUNT
projection-mismatch package, the target blames and never reaches a value.
Machine-checked in
`GTSFImp/proof/DGG/notes/ValueCatchupProvenanceGapScratch.agda`
(commit b886024), against the current post-#128 relation — the package's
`⊢²` derivation was re-validated after the see-through tightening
(`rep★-nonvar-tag` admits the `ℕ!` top tag).

So the `CatchupCast` premise on `ExtraCastRight²` cannot be dropped one
level up; the driver must carry a column-level provenance.

## The structural fact the design leans on

`CatchupCast p M′ c′ q` inspects its TERM argument `M′` only in the
projection constructors (`catchup-projection` →
`generated-project-same` / `generated-project-expand`, which demand
matching injection ancestry on the visible value). The other
constructors — `catchup-inert`, `catchup-id`, `catchup-ground-other`,
`catchup-inst`, `catchup-bot-elim/intro` — constrain only the cast and
the world obligations (`ground-other` carries `r : A ⊑ᵂ⟨W⟩ G` and its
recursion, but never the term's shape).

This matters because the driver consumes the column left to right: by
the time cast `cᵢ₊₁` fires, the term is the (existentially produced)
value `Nᵢ` of the previous catch-up, so any provenance stated upfront
about `cᵢ₊₁` cannot mention the term — unless it is term-independent.

## Candidate interfaces

(A) **Head-full, tail-term-independent** (SELECTED AND LIVE). Define the
    term-independent fragment `CatchupCast⁻`
    (constructors above minus the projection family; `ground-other`
    recursion also lands in the fragment). Column provenance:

        CatchupColumn p M′ κ q :=
          chain of intermediate obligations q₀ = p, ..., qₙ = q with
          * head link: full CatchupCast p M′ c₁ q₁ (may be a
            projection — the head faces the REAL current value);
          * tail links: CatchupCast⁻ qᵢ cᵢ₊₁ qᵢ₊₁.

    Driver recursion: run the head worker; embed the first tail link
    `CatchupCast⁻ ↪ CatchupCast` at the new value `N₁` (sound BECAUSE
    the fragment never inspects the term); transport its world
    obligations along `WorldExtendᴿ`; recurse.

    Support lemmas this needs (all expected mechanical):
    * `catchup⁻-embed : CatchupCast⁻ q c q′ → CatchupCast q N c q′`
      (any term N);
    * `catchup⁻-transport : CatchupCast⁻ stable under transport⊑ᵂ`
      (transport the `ground-other` obligations pointwise);
    * `catchup⁻-map : CatchupCast⁻ stable under applyConsistencies`
      (store changes are weakenings; Inert/Ground/Atom/inst-index
      shapes are preserved by renaming).

    Coverage check against known call shapes:
    * the M5 β-inst residual `↑ᶜ (c [ ★/0 ]ᶜ)` — needs a provenance
      minted by the M5 continuation; term-independent constructors
      suffice iff the residual is never a bare projection (to be
      established as part of the M5 relational continuations — this is
      the same knot obligation as before, now made explicit);
    * the catalog column (inst ▻ function cast) — both links
      term-independent;
    * the refutation package — excluded at the head (CatchupCast on it
      is empty, checked) and in tails (fragment has no projections).

(B) **Outcome-indexed provenance** (continuation function: for every
    possible (N′, ext) outcome, produce the next CatchupCast). Maximally
    general, but the driver's callers would have to run the driver to
    discharge it — rejected unless (A) proves too weak.

(C) **Derivation-harvested provenance with a strengthened conclusion**:
    if M7 turns out to need projections in TAILS (a `⊢²` node exposing
    `V′⟨c⟩⟨？G⟩` with the projection separated from its ancestry by a
    reducible cast), the driver's conclusion must additionally expose
    the reduct's top-tag discipline (e.g. a `TagTransport`-style fact
    relating N′'s visible tag to the q₁-world alignment), so the
    next projection link can be re-established semi-statically. Not
    needed by any call shape known today; sketch kept as the fallback.
    Cross-reference: QHUNT-REPORT.md "Candidate Invariant Interface".

## Current sequencing

1. DONE: select and pre-flight option (A); make the provenance-carrying
   surfaces live in `ValueCatchupRightDef.agda`.
2. IN PROGRESS: finish M5's `InstInversionPackage`.  The shared finalizer now
   consumes `InstSpineDescentPackage` and transports residual provenance
   before smaller-fuel catch-up.  The plan-indexed Λ top-post obligation is
   live, as is the hereditary prefix worker; package assembly remains.  Each
   non-Λ view must still mint the residual `CatchupCast⁻`; the Λ support
   already constructs the non-star residual provenance.
3. DONE (2026-08-13): `catchup-column⁻-transport` proves
   `CatchupColumn⁻Transportᵀ`, transporting every tail link through the store
   changes returned by a head catch-up.
4. DONE (2026-08-13): `extra-cast-right-at` adapts M4 to the fuel-indexed
   surface.  Its ground-other and project-expand cases call `smaller-extra`;
   instantiation consumes the supplied same-fuel `InstCatchupRightAt`.
5. DONE (2026-08-13): `value-catchup-right-prov-at` runs the head through
   the current-fuel M4 worker, transports the tail, embeds its first
   term-independent link at the resulting value, and recurses through
   `smaller-value` on the strictly smaller mapped tail column.
6. DONE modulo M5 (2026-08-13): `build-fuel-knot-acc` ties
   `ExtraCastRightAt`, `InstCatchupRightAt`, and
   `ValueCatchupRightProvAt` by `Acc _<_`.  The unindexed
   `value-catchup-right-prov²` is live with one explicit argument:
   `∀ fuel → FuelStepSurface fuel → InstCatchupRightAt fuel`.  Completing
   M5 supplies that factory without changing M6.

`FuelStepSurface.next-knot` was removed on 2026-08-13.  It was unused by M5
or M6, and it pointed in the wrong well-founded direction: constructing the
surface at `fuel` demanded a complete knot at `suc fuel`, so even the
zero-fuel case generated an infinite upward obligation.  The live surface now
contains only the three strictly smaller workers.  The knot is assembled by
`Acc _<_ fuel`: recursive calls provide knots at `m < fuel`; their three
fields populate `smaller-extra`, `smaller-inst`, and `smaller-value`; the
current M5, M4, and column workers then populate `FuelKnot fuel`.

The provenance-free surface remains only as a refuted design reference.  Do
not revive it or admit projection casts in `CatchupCast⁻` without a new
machine-checked call shape requiring option (C).
