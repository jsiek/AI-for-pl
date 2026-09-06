# Design points — glossary for `notes/DesignSpace.md`

One entry per node of the map, same ids and same order.  Each says what
the design point **was**, why it was tried, and what happened to it, with
a pointer.  Labels keep their historical names (`ambient dual`,
`x-licenses`, `MergeOK`, `Peel`, `TyWrapCncl`, …); the prose around them
uses today's vocabulary — a boundary's **interior**, its **exterior**
(the plain `Δ`), its **conversion context** `convCtx Θ Δ`, its
**conversion** `c` with a **source** and a **target** type, a variable's
**binder** (the `bind` entry that carries its representation), and the
context-morphism entries **bind / lock / unlock**.

Where a section title is quoted it is a heading of `notes/DECISIONS.md`
unless stated otherwise.  "Gauntlet §9x" refers to the numbered sections
of the v1 install gauntlet, quoted throughout `DECISIONS.md`.

---

## A. Per-variable wrappers (2026-09-01/02)

**D01 — conceal-b: delete the binding.**  The conceal rule before the
first commit typed a sealed body by *removing* `X := A` from the context
outright, with the side condition `X ∉ Γ₂`.  It is refuted by
Example 6 (`(ΛX. λw:ℕ. (ΛY. w)[X⇒X])[ℕ]·5`): revealing `Y := X⇒X` puts
`X` back into `Γ₂`, the side condition fails, and the context is left
dangling — i.e. "revealing a variable preserves typing" (L2) is false
under it.  Kept as a cautionary record in `notes/old/notes-v1.md`, "Why
the earlier conceal-b design failed".

**D02 — per-variable `↑X:=A` / `↓X:=A` wrappers.**  The first design
(commit `a3847769`): one wrapper per revealed or concealed variable, each
carrying its own copy of the representation, with a context entry `↓X`
(the *conceal marker*) blocking the concealed variable, and the rule set
`Beta`, `TyBeta`, `WrapReveal`, `WrapConceal`, `TyWrapRevl`,
`TyWrapCncl`, `Cancel`, `Drop`, `Commute`, `RevealCnst` plus congruences.
Refuted as a whole by the pre-boundary counterexample (see `D05`);
recorded in `notes/old/notes-v1.md`, "Old per-variable design", and
summarised in `Design.md` §1.

**D03 — `ConcealCtx`, a companion predicate for representation
well-formedness.**  `(conceal)` recovers `A` by lookup and needs
`Γ ⊢ A`, which lookup alone did not give (a marker between the use and a
revealed variable whose representation names a *concealed* variable), so
an inductive predicate `ConcealCtx Δ X` was carried alongside the term
and re-established at every context change.  It was deleted at commit
`600cc2da` once the marker was tightened, and is the first instance of
the standing **grounded-invariants** law — no external companion
predicate — that later killed `1b` (`D09`) and `W1` (`D14`).

**D04 — the tightened conceal marker.**  Lookup was changed so that `↓X`
blocks `X` *and every variable revealed after it* — in de Bruijn
`skip-cncl : n < X` in place of `n ≢ X` (commit `600cc2da`).  This makes
`∋:=-⊢` immediate (deleting `ConcealCtx`), makes the dangerous shape
unstateable, and statically rejects the `Commute` redex, so `Commute` and
its two lemmas were removed at `92956022`.  It died with the rest of the
per-variable design.

**D05 — `TyWrapCncl`: push the type argument into the sealed body.**  The
∀-elimination for a *concealed* value,
`F ↓[X:=A]@∀Y.B [C] → F [C[X:=A]] ↓[X:=A]@B`, substituting the type
argument into the sealed body.  **This is the design point the whole
development turns on**: on the closed program
`(ΛX. λf:(∀Z.Z→Z). ΛY. f [Y])[ℕ] · (ΛZ. λz:Z. z)` the conceal drifts
under the later `ΛY`, its interior `Γ ↓ X = (Y , X:=ℕ) ↓ X = ∅`, and the
pushed `[Y]` forces `∅ ⊢ Y` — the term is typeable at no type
(`Design.md` §1, "The pre-boundary counterexample"; machine-checked in
the era's `Scratch7/8/9.agda`; `notes/old/notes-v1.md`, "Example 8,
historical").  The two lessons drawn were *mask, do not drop* and *never
push a type argument inward*; v1 took only the second.

**D06 — the marker-free "prefix" design.**  Proposed in `notes.md` at
commit `92956022` (`git show 92956022:SystemF/agda/strong/notes.md`):
delete the conceal marker from contexts entirely and type a conceal's
body in the context prefix `Γ ↓ X`, "the tightened marker compiled away —
the same variables in scope, but nothing to block, shift or subtract".
It removes the marker's skip conditions and the lemmas `L-mark` and
`L-exch′`, but it still **drops**, so `D05`'s counterexample survives it
unchanged; superseded by the combined boundary.

---

## B. v1 — the combined boundary `M ⟪Θ, B₀⟫` (2026-09-03/04)

**D07 — one combined boundary with an entry list.**  Commit `f219963e`:
replace per-variable wrappers by a single wrapper `M ⟪ Θ , B₀ ⟫` whose
`Θ` is a list of reveals `↑X:=A` and conceals `↓Y:=A`, with one boundary
type `B₀` read two ways (internal face `B₀[γΘ]`, external face
`B₀[ρΘ]`), a whole-`Γ` tight interior `intOf Δ Θ` restricted once at the
deepest conceal, and a **scope premise** `Scoped (baseS Θ Δ) B₀` on
`(env)` forbidding `B₀` to name a blocked slot.  Combining is what lets a
conceal's interior still see a reveal's fresh variable — the thing the
per-variable design could not express.  Refuted as a whole on 2026-09-05
(`D29`).

**D08 — `TyWrap` (R1) and `Wrap` (R2): float the elimination inside.**
Proposed in `notes/BoundaryRules.md` §4 and landed at `298e5eeb` and
`9f84b620`: at a `∀` face float the type application inside the boundary
applied to the fresh reveal variable and **record** the type argument as
a new reveal (never push it in — `D05`'s lesson); at a `⇒` face move the
argument inside through the **dual** boundary `dualᵇ Θ`.  Both are total
in the wrapped value; superseded by `TyWrap′`/push-through `Wrap`
(`D12`), then by `Peel` (`D25`).

**D09 — Decision 1, options 1b and 1c.**  The probe found `bad`, a closed
well-typed value no type-preserving rule can eliminate, so a conceal's
representation needs a licence.  `1b` proposed a companion predicate
`Consistent M` ("every `↓Y:=A` under a matching `↑Y:=A′` has `A = A′`"),
preserved by reduction; `1c` proposed accepting the gap and proving
progress only for source images.  Both **withdrawn** on 2026-09-03 —
`1b` against the grounded-invariants law, and Jeremy's own account is
that the old design's `Γ ∋ X:=A` premise was never meant to be dropped
("Decision 1 — resolution").

**D10 — Decision 1a: the interior-reading licence.**  The restored
invariant, in three successive forms: naive syntactic `Γ ∋ X:=A`;
then the transported `A = A₀[γΘ]` with interior knowledge entries
(`GroundedProbe.agda`, commit `677634d6`); then the *interior reading*
`X:⟦A⟧` with a `dfree` guard ("Decision 1 — refinement forced by the
implementation").  The naive form still admits a stuck closed value
`bad₂`, and the entry form is refuted under renaming by `¬hk-int` — an
entry stored "as written in the exterior" is read everywhere else as a
telescope entry.  Superseded by `D11`.

**D11 — `Reversal`: license the conceal by reading back outward.**
`outRead Θ A ≡ upRep X A₀` — the conceal's representation, read back out
through the boundary's reveals, must equal the exterior's knowledge
("Decision 3 — tension with Decision 1 found by the Merge probe";
`ReversalProbe.agda`, commit `7211610a`).  Forced by three independent
facts: `bad₂`, `¬hk-int`, and the merged boundary that must carry
`↓X:=(W⇒W)` which the interior form refuses.  It transports under any
monotone renaming with no scope restriction — and it is exactly the
machinery that becomes *definitional* under binder-syntactic storage
(`D33`, advice Q4).

**D12 — `TyWrap′` and push-through `Wrap`.**  Decision 2 was ruled for
the total float-inside `TyWrap` on 2026-09-03, then **revised** on
2026-09-04: with `Merge` and depth-1 values a wrapper-bodied wrapper is a
`Merge` redex, so the direct-combine form
`((ΛY.V) ⟪Θ, ∀Y.B₀⟫) ·[B,A] → V ⟪ ↑Y:=A , Θ , B₀ ⟫` is total enough — and
it removes `TyWrap`'s `⇑ᵀ`, the one term type-shift in the calculus.
`Wrap` was switched the same day to the symmetric push-through-the-lambda
form ("Decision 2 — REVISED to TyWrap′"; commits `149e161e`, `2315538a`,
`a0a94add`).  Superseded by `Peel` (`D25`).

**D13 — `Merge` `⊕` with `Drop∅`.**  Decision 3, option 3a: collapse
nested boundaries by an entry-wise composition `Θ₁ ⊕ Θ₂` in which a
`Θ₁`-conceal of a `Θ₂`-reveal slot **cancels**, with `Drop∅` shipping
alongside so a fully cancelled tower reduces to the bare value
("Decision 3", its addendum, and "THE MERGE + DROP∅ LANDING"; commits
`7947fe95`, `7b024831`; precedent digested in
`notes/Zdancewic-embeddings.md` §4).  It landed with both preservation
cases proven but carried `MergeOK` as a rule premise, and the flatten-first
design it implied was refuted at §9f/§9g (`D24`).  `Drop∅` was retired by
active/inert in favour of `Drop$`; the whole operator is retired in v2
under the law "towers, not merges" (`Design.md` §8.6).

**D14 — Decision 4, W1 and W2.**  When a boundary drops a slot *without*
concealing it, its dual cannot rebuild the exterior's knowledge there, so
a crossing argument fails to retype (program `P`, `notes/old/notes-v1.md`
Example 9).  `W1` added a `RunOK Γ M` premise to preservation ("at every
boundary the dual rebuilds the exterior") — a companion predicate on
terms, against the grounded-invariants law.  `W2` made it an `(env)`
premise ("every dropped-unconcealed slot is abstract") — refuted because
`TyWrap` itself creates the offending terms by weakening a sealed value
under a new reveal.

**D15 — Decision 4, W3: knowledge-preserving weakening.**  When a
boundary with conceals is weakened by a new revealed variable, conceal
that variable in it too, at the interior reading of its knowledge.  It
repairs `P` and makes blocked slots abstract by construction, but Jeremy
objected that its `⇓` is a **term traversal**, and example `E`
(`notes/old/notes-v1.md` Example 10) makes the traversal depth unbounded
by putting an evaluated `Λ` between the `ΛY` and the sealed value.
Superseded by the ambient dual.

**D16 — Decision 4, W4: stop dropping.**  Give up the tight interior:
`Γ ⇈ Θ = Γ , X₁:⟦A₁⟧ , …`, so concealed variables stay in scope, no slot
is ever blocked, the dual has nothing to rebuild and the scope premise is
vacuous.  It was the agent's recommendation and was **OVERRULED** by
Jeremy on 2026-09-04 — "tightness is wanted for its own sake" — together
with the explicit principle that almost no rule performs a type shift on
a term (commit `8c78d5bc`).  Both laws survive verbatim into v2
(`Design.md` §8.2 and §8.3).

**D17 — the ambient dual `dualᴳ`.**  Index reduction by the ambient type
context (`Γ ⊢ M -→ M′`), extend it at `ξ-⟪⟫` by the boundary's interior
and at `ξ-Λ` by an abstract entry, and let the dual **copy `Γ`'s own
entry** at each dropped slot instead of fabricating one ("Decision 4 —
ambient dual probe verdict and the overnight install";
`AmbientDualProbe.agda`, commit `acebd7f5`).  It repairs `P` with no
insertion and handles `E` with zero traversal, but it is the copy that
every later era-B counterexample attacks, and the survey's demotion is
its failure mode (F1, F3).  Its one surviving trace is the Γ-indexed
reduction judgment itself, which v2 keeps as `Δ ⊢ M -→ M′`.

**D18 — the telescopic reveal block.**  Residue R1 of the ambient-dual
install: a copied entry naming another dropped slot is inexpressible
under the parallel reading, so `(bwf-↑)` was made **telescopic** — each
reveal representation read over the deeper reveals of the same boundary.
Landed overnight (`357c2b27`), flagged as revertible, and **REVERTED**
the next morning by Jeremy's simultaneity ruling: "the representation
type of a reveal entry is well-formed in the external context, without
any interference from the other entries in the boundary" (commit
`329a4962`).  Simultaneity has been a standing law ever since
(`Design.md` §8.4).

**D19 — candidate (a′): unfold at entry birth.**  Store knowledge fully
resolved through the ambient context at the moment the entry is born, so
chained representations never have to be unfolded later ("CANDIDATE (a)
SHARPENED TO (a′)").  Jeremy gave a conditional go-ahead — "if the probe
finds no mismatches" — and `UnfoldProbe.agda` found one, at exactly one
consumer: the dual's conceal-of-a-reveal is forced by simultaneity to
carry the *raw* stored representation, so `¬DualCnc-a′`.  Not installed,
per the ruling (commit `5699979e`).

**D20 — candidate (a″): equality up to unfolding.**  Keep entries raw and
make the *comparisons* up to `≈Δ̄` — Zdancewic's `(eq)` without their
eager retag — with a hybrid interior entry `⟦·⟧ᴴ` retried at the unfolded
representation ("(a″) PROBE VERDICT — SURVIVED", `UpToProbe.agda`, commit
`eb839a44`).  It carried `Pc` and collapsed Merge's retyping-along-
unfolding into `≼≈`, and it is exactly the `≡`-versus-`≈` gap that later
made progress false (§9m).  Retired by advice Q5(b), "no `≈` in the
rules".

**D21 — `cnc⋆`, the rep-less conceal.**  The dual image of the rep-less
reveal `↑Y:⋆` — re-hide a variable claiming nothing, emitted when a
reveal's knowledge is neither expressible nor unfoldable; Jeremy's
observation that the entry syntax must be **closed under dualization**
made it inevitable ("E★ — the vacuity lemma is insufficient").
`StarConcealProbe.agda` found it **sound and required but not
sufficient**: on `E★′` the boundary type *names* the unknowable reveal,
so `cnc⋆` trades a licence failure for a scope failure (commit
`868fc459`).  It stayed in the calculus until the v1 deletion.

**D22 — x-licenses: candidate (b3) plus "claims nothing".**  A fourth
context entry `X:=ˣA` ("revealed; representation readable one level out;
asserts nothing here"), minted by the interior computation and consumed
by a new clause `(bwf-↓x)`, chosen over `(b1)` read-back identity,
`(b2)` faces-as-premise and the structurally-excluded `(b4)`; the naive
version admitted the adversary `⊢3n-adv`, which the load-bearing "claims
nothing" premise refuses (`notes/DualLicenseDesign.md`,
`DualLicenseProbe.agda`, commits `4b3ab446`, `e07e8863`).  Retired by
advice Q5(c) on the survey's F4: an x-licence is consulted at birth and
never survives a crossing (`demote-x-always`).

**D23 — the comparison-free `(bwf-↓x)`, then the `SkelEq` repair.**  As
installed, `(bwf-↓x)` carried *no* representation comparison (deviation
D1), because neither `≡` nor `≈Δ̄` survives `⊢renameᵀ` at that clause.
`D1Probe.agda` then found a genuine **soundness hole** — `starOnly` is
vacuously true of closed representations, so `↓Z:=ℕ` was licensed at an
x-slot (`⊢Tg`, `⊢Tbad`) — repaired by comparing representations by
**skeleton**, which is stable under independent renamings ("D1 PROBE
VERDICT"; commit `39c405f1`).  Retired with the rest of the x-machinery.

**D24 — face-directed `⊕`: keep the abstract witness.**  Decision 5's
first fork: make `Merge` consult the face types, so a `Θ₁`-reveal whose
representation crosses a `Θ₂`-conceal is re-abstracted at that conceal's
*variable* rather than at its resolved representation.  Motivated by
gauntlet §9f, where `cxP₄` is reachable from closed source, well typed
and **stuck** — a live type-safety hole in the flatten-first design — and
**refuted** by §9g's double coincidence: one revealed `W` can coincide
with two conceals at once, and then no flat boundary exists under *any*
`⊕` ("Decision 5 — ⊕ must keep the abstract witness", and its two
addenda).

**D25 — `Peel` and `TyPeel`: crossings go inward.**  Decision 5's second
fork, **RULED** by Jeremy on 2026-09-04: generalize `Wrap` from
ƛ-bodied to any value body and move the *argument* inward through the
dual, so every re-expression is in the `γ` direction — a function —
and the relational outward re-abstraction is never needed
("Decision 5 — RULING … PEEL (fork (b))", commit `d5c5fe48`).  The pairs
it creates are lineage pairs, depth-1 values are superseded (towers stay
values), and the survey later confirmed the choice empirically (F10: 23
of 23 crossings inward).  `Peel` and `TyPeelR` are the current rules.

**D26 — standalone `Cancel`.**  Jeremy: "that example looks like it needs
a `Cancel` reduction, not `Merge`" — an era-A rule revived, restricted to
the face-anchored shape `(V ⟪Θ₁, ` Y⟫) ⟪Θ₂, ` X⟫ -→ V`.  `CancelProbe`
confirmed his identity `Cancel = Merge + Drop∅` as a machine fact and
**derived** the side condition (the load-bearing conjunct is that the
contexts undo, not that the faces agree; the `≈` form is unsound), but
also showed that `Cancel` cannot carry progress: of the three
variable-face families `α`, `β1`, `β2`, only `β1` cancels, and `α` and
`β2` stay stuck ("Decision 6 — CANCEL PROBE VERDICT").  Reinstated in v2
as `CancelR`, where the face match is definitional (`D43`).

**D27 — the active/inert discipline.**  Jeremy pushed Siek–Chen's
parameterized cast calculi (`notes/ParameterizedCastCalculi.md`) and
**RULED** on 2026-09-04: boundaries are casts, classified **inert** at
`⇒` and `∀` faces (value-forming, eliminated at their use) and **active**
at reveal-variable and base faces; `V-⟪⟫` gains the `Inert` premise
("Decision 6 — RULING … ACTIVE/INERT, inert/inert", commit `2f3e1341`).
`det` and `values-don't-step` became theorems the same night, and F11
later found the split perfectly separated on the corpus.  It is the v2
design (`Design.md` §5), classified there by conversion constructor
alone.

**D28 — `MergeOK` component (1) repaired.**  §9l exhibited a well-typed
non-value taking no step because `cmax Θ₁ ≤ revs Θ₂` failed while every
other component and the internal-face equation held — a sufficient side
condition mistaken for a necessary one.  Jeremy ruled the repair on
2026-09-05 (replace it by the internal-face equation itself, demote `⊕-γ`
to its discharge), and `merge-derivable` was proven, closing that
component for good ("Decision 7"; commit `0e31b11e`).  It is the one
era-B result that closed permanently, and it did not save the design.

---

## C. The verdict and the survey (2026-09-05)

**D29 — subject reduction is FALSE.**  `DualIntProbe` §5 exhibits a live
`Peel` whose contractum has no typing (`⊢Redex`, `peel-step`,
`¬⊢contractum`), and gauntlet §9n reaches the same configuration from a
closed plain source in nine steps (`qP₀ … qP₈`, `¬⊢qP₈`); with §9m's
`¬progress` already in, **both halves of type safety are false** for v1
("THE PRESERVATION VERDICT (2026-09-05)"; commits `f8ca0568`,
`e8910f47`).  The same sweep proved `DualRep≈`, `DualCnc≈` and
`DualInt≈` false as stated and mutually inconsistent, so the parameterized
preservation module could never have been instantiated.

**D30 — Decision 8: a representation discipline, `PeelOK`, or rethinking
demotion.**  The ask assembled from that verdict: **(A)** require reveal
representations to be `Scoped` and resolved, killing `Pn` and §9m at
birth; **(B)** give `Peel` a grounded `PeelOK` premise that progress must
then derive; **(C)** rethink the dual's `rvl⋆` fallback, the only
knowledge-destroying step in the system.  No option was installed —
Jeremy superseded the whole track with the survey the same day.

**D31 — the boundary survey, findings F1–F12.**  Jeremy: "I'm worried
that our current boundary bookkeeping is rather broken … time for a fresh
look at all the critical examples", with the amendment to instrument
*what the boundary must provide* independently of the bookkeeping.
Delivered as `EvalLog.agda` (event annotator), `Oblig.agda` (a
requirements extractor that computes no face and reads no context entry),
`SurveyCorpus.agda` (16 programs) and `notes/BoundarySurvey.md` (commit
`831591b3`).  The decisive findings: **F1** every typability loss
coincides with a demotion and vice versa; **F4** an x-entry is demoted
unconditionally, so no x-licence survives a crossing; **F5** every
knowledge demotion is at a chained representation whose target is
Λ-bound; **F8/F9** every `Merge` that fires is a lineage cancel to the
empty composite; **F10** no trace ever reads outward; **F11** the
active/inert split is exactly the observed behaviour; **F12** 61 of 195
obligation rows have no term-determined interior type.

**D32 — the redesign advice, Q1–Q5.**  `notes/RedesignAdvice.md` turns
the findings into design: **Q1** store the representation once and cite
it by name — *yes*, the strongest-supported change, since every failure
is a failed copy; **Q2** simultaneity — *keep*, no finding implicates
sibling entries; **Q3** use `GTSF`'s `Conversion` as the **conversion
half** of a split boundary, with the scope discipline as the other half,
because Conversion does not do scoping (Jeremy's own caveat); **Q4** the
cancel face-match becomes **definitional** under Q1, replacing
`cancel-agree`, `Reversal≈`, `SkelEq`, `xrep-stored` and `MergeOK`'s two
face equations with one algebra lemma; **Q5** `Merge → Cancel`, no `≈` in
the rules, retire the x-machinery, shrink the dual to slot re-pointing,
keep active/inert, inward-only, `det` and tightness.  Soundness gate:
`⊢3n-adv` must stay unmintable.

---

## D. v2 — conversion boundaries (2026-09-05/06)

**D33 — binder-syntactic representation storage.**  Q1's realization,
**RULED** by Jeremy on 2026-09-05: not a global `Σ`-store (realization
(i), GTSF's, with its ready-made transport lemmas) but **(ii)** — "once
type variables are in a global store, it becomes more difficult to talk
about their lexical scope relationships, which we are currently using in
conceal blocking".  The `bind` entry *is* the store entry; every other
mention carries a name and resolves by `Δ ∋ X := A`, which is a lookup,
so knowledge transport is definitional and the cancel equation follows
from `∋:=-det` twice (commit `93d37333`; `Design.md` §1, §3).

**D34 — mask, do not drop.**  A `lock X` **masks** its slot in place and
retains every other entry, and the interior is *computed* from the
ambient context at the boundary's current position.  This is era A's
deferred lesson 1 (`D05`), and it is **forced, not stylistic**: the probe
built the split-constructor dropping variant far enough to fail — a
dropping conceal's dual must reintroduce a telescope of representation
copies, "D1's disease one level out" — and masking additionally lets
mask/unmask be functions (`THE REDESIGN PROBE VERDICT`, obligation 2;
`Design.md` §1 and §3).  With it, demotion is not expressible at all
(`⊑-kn`).

**D35 — the conversion boundary `M ⟪Θ, c⟫`.**  One boundary form carrying
a context morphism `Θ` (entries `bind A` / `lock X` / `unlock X`) and a
representation-free **conversion** `c` (`id` / `seal X` / `unseal X` /
`_↦_` / `` `∀ ``) checked by `Δ ⊢ c ∶ A ⇝ B` in the boundary's own
**conversion context** `convCtx Θ Δ`.  The probe was green on the
make-or-break question — transport passes with nothing beyond the
renaming, `⊢retag` has no residue, the three v1 breaks' contracta type,
`⊢3n-adv` is unmintable by one inversion of `conv-seal`, and §9m cannot
arise (commits `c843cfbd`, `f0141d3e`).  This is the current design
(`Design.md` §2, §4.4).

**D36 — split per-purpose term constructors.**  Jeremy asked whether the
outermost reveal, the conceals and the inner reveals should be *different*
constructors, making binder-ship a syntactic invariant; it was folded into
the probe mandate (commit `e179e23e`).  It was **not** carried into the
restructure: v2 has one boundary form whose `Θ` distinguishes the three
purposes by entry kind (`bind` / `lock` / `unlock`), which is where the
one-representation-per-variable invariant actually lives.

**D37 — the polarity index on conversions.**  GTSF's conversions are
polarized (`↦` flips on domains), so the probe's mini-core carried a
polarity index `p` and "Option A" kept it, with a canonicity invariant to
be proven alongside preservation.  `Examples` §13 then showed the landed
`TyPeelR` contractum `seal 0 ↦ seal 1` types at **neither** polarity, and
Jeremy asked "do we really need polarity at all?" — the per-variable
invariant is already enforced by `env`'s two contexts, and nothing uses
`p` for work.  **RULED dropped** on 2026-09-06, which is what makes
`TyPeelR` provable at every `∀` conversion (commit `adcf48f9`;
`Design.md` §2, "Why there is no polarity index").

**D38 — `IdAbsorb` with the frame operator `⊳`.**  The probe found a
progress hole — an `id (` X)`-faced value cannot be eliminated (`T₆`,
stuck and well typed) — and Jeremy ruled an absorption rule with an
explicit `Active c` premise, merging the two frames with `⊳`.
`IdLayerProbe` refuted the *operator*: `⊳` jams on an id-layer whose
representation names the outer boundary's binder, and the only repair is
substituting representations into representations, i.e. **`⊕` regrown**
(the no-composition test).  Retired; recorded as `Design.md` §8.6.

**D39 — `IdPush` with the binder-lookup premise.**  `IdAbsorb`'s
degenerate form with `⊳` deleted: the two conversions **swap** instead of
the frames merging, so the active conversion moves one layer inward each
step and the process terminates.  **RULED** by Jeremy on 2026-09-05 —
"go ahead with IdPush and the lookup premise and the other repairs" —
together with the principle that every rule minting an identity at a
looked-up representation carries the lookup as a premise, which is how
determinism is bought ("Id-layer RULING"; commit `92ede193`;
`Design.md` §6.7).

**D40 — the v2 restructure.**  Commit `4c4c44c6`: the convention layout
(`Ctx`, `Conversion`, `Terms`, `TermSubst`, `Reduction`, `Examples`,
`Show`, `proof/`), v1 deleted, all five ruled repairs in the rules, and
`det` + `values-don't-step` proven; `1caf9b27` then proved **progress
with zero parameters**.  Jeremy's vocabulary rulings landed on top
("skeleton" → context morphism, "spine" → type context, `own`/`ali`/`cnc`
→ `bind`/`unlock`/`lock`), and `TyBeta`'s `Value N` premise was confirmed
as the fifth determinism repair.

**D41 — v2 preservation FALSE: four rules refuted.**  Commit `5554c6b2`:
`TyBeta`, `Beta`, `Drop$` and all five congruences are proven with no
context well-formedness premise, but `Peel`, `TyPeelR`, `CancelR` and
`IdPush` are each refuted with a diagnosed cause — three read as local
rule bugs (the dual's flip logic, `TyPeelR`'s annotation and double
shift, `CancelR`'s residue) and `IdPush` as a possible design question
("v2 PRESERVATION VERDICT").  Every cause turned out to be a rule
definition, not a proof gap.

**D42 — the dual repaired (half of it).**  `dualScope` had mapped a no-op
`unlock X` to a real `lock` and replayed the morphism in `Θ`-order, so a
same-slot mask/unmask pair failed to cancel; **dropping** the `unlock`
case fixes both defects, and `interior-dual` / `convCtx-dual` are then
proven in general, discharging `PeelCase` (commit `7e9c4109`,
`proof/PeelDual.agda`).  The reading behind the drop — "an `unlock`
claims nothing, so the dual need not restore it" — is what **leaked**
four days later (`D47`), and the current `dual` restores the `unlock`
*and* reverses the list (`D50`).  What survives from `D42` is the
diagnosis: a dual is an inverse, and the two defects it names are real.

**D43 — `TyPeelR` and `CancelR` repaired.**  `notes/RuleRepairs-TyPeelR-
CancelR.md` proposed both, before-and-after, run on the closed programs
that broke them: `TyPeelR` takes plain `Θ` (not `renᴮ suc Θ` — the double
count alone gives `¬⊢G₅`) and a premise-determined **interior** ∀-body,
plus `instReveal` for the new bind's leaves; `CancelR` keeps **both**
frames and neutralizes both conversions to identities instead of dropping
`Θ₁`'s frame (commits `4defe7b5`, `5d69c0d7`).  With polarity dropped,
`TyPeelR` is proven at every `∀` conversion (`adcf48f9`); `CancelR` is
`D26`'s `Cancel` reinstated with the face match definitional.

**D44 — the wall, and four candidate invariants.**  Both repaired
contracta make an inner wrapper present a representation inside `Θ₂`'s
interior, owing `interior Θ₂ Δ ⊢ᵗ A`, and four grounded invariants were
tried and **all machine-refuted**: (1) folding `RepWf` into the lock
clause of `_⊢ᵐ_` — impossible, the unsound witness and the reachable one
have the same `(Δ, Θ)`, and `RepWf` is not `⊑`-stable; (2) exterior-type
`Scoped` on reveal conversions — too weak, `R★`; (3) pointwise `RepWf` at
name-faced boundaries — refuted by a seven-step closed program that mints
`Y := Z` under an id-faced lock of `Z`; (4) chain-scoped — preserved by
`IdPush` and `CancelR` but not `⊑`-stable ("Rule repairs LANDED; the
invariant hunt", commit `e4c9fe88`).  The four record modules were
deleted by ruling once the wall dissolved (`b1ed2b87`).

**D45 — the scope move `Θ₁ ⋉ Θ₂`.**  Jeremy: "I'm contemplating whether
part of `Θ₂` should sometimes be moved to the inner boundary in the
contractum … the `↓X` could be moved to the left of the `unseal Y`."
`IdPush` and `CancelR` now move `Θ₂`'s **whole scope** — locks *and*
unlocks, order kept, indices lifted — into the inner frame and leave a
scope-free outer frame behind, so the representation is presented outside
the locks that hide it; moving only the locks is refuted in tree
(`proof/MoveScope` §4b, `¬frame-locksOnly`).  The wall's premise then
follows from the redex typing, and **preservation is proven
parameter-free** (commit `cdb24a41`).  "The wall was never a missing
invariant — the rule put the representation on the wrong side of the
lock."  The move itself is unchanged today; what changed at `D50` is
*which* scope-free frame stays outside — `dropLocks Θ₂` then,
`rewind Θ₂` now, because only `rewind` keeps its own `_⊢ᵐ_`
(`proof/MwUObstruct` §2/§4).

**D46 — `TypeSafety`, and the naming rulings.**  `strong/TypeSafety.agda`
(commit `5f67634f`) states the six public theorems — `progress`,
`preservation`, `preservation*`, `type-safety`, `det`, `value-¬step` —
with no parameters, no postulates and no holes under `--safe`.  Jeremy
then ruled the vocabulary on 2026-09-06: `intC → interior`,
`fceC → convCtx` (the conversion context — *not* the exterior, since the
conversion names the boundary's own binds and cites locked binders, so it
types in neither the interior nor the exterior), "exterior" meaning the
plain `Δ` and nothing else, **"face" retired** in favour of
conversion / source / target, **"binder" instead of "owner"**, and
`MorphWf Δ Θ` becoming the infix judgment `Δ ⊢ᵐ Θ` (commits `390c5723`,
`a6ed7232`, `505f6ad9`, `9c7c6f9d`; `Design.md` Appendix A).

**D47 — `dual` drops `unlock` entries: the scope leak.**  The design
point is the *reading* behind `D42`: an `unlock X` "claims nothing", so
the dual of a boundary need not restore it.  **Refuted by Jeremy's test**
(`notes/DECISIONS.md`, "Peel's dual is NOT tight for `unlock` entries
(Jeremy's test, 2026-09-06)"; `proof/DualTightness.agda`, commits
`db4e3351` / `a9e12cee`).  Jeremy: "create an example program that takes
a `Peel` step, and the program should have an ill-formed type in the
argument `W`, and after the reduction step, `W` wrapped in the dual
boundary should still be ill-formed."  The witness: exterior
`Δᵤ = ⌷[U := ℕ]`, `Θᵤ = ↥U`, `W = λy:ℕ. (ΛZ. 3)[U]` — `W` names the
masked `U`, so the redex `(V ⟪ ↥U , c ⟫) · W` is **ill typed**, and its
`Peel` contractum was **well typed**, because
`interior (dual Θᵤ) (interior Θᵤ Δᵤ)` was the masked bind prefix over
`unlockedScope Θᵤ Δᵤ`, strictly more nameable than `Δᵤ`.  Scope was
gained through the boundary: design law 2 was false for the *reduction
relation* — though not for typing, and not a preservation failure, since
the redex is not well typed and preservation says nothing about it.
This is the only edge in the whole map driven by an ill-typed program.

**D48 — masked-only `mw-u` + unconditional relock + `bindsOnly`.**  The
three-part repair, proposed as one package: (1) `mw-u` demands the slot
be LOCKED, so a *vacuous* unlock is refused; (2)
`dualScope n (unlock X ∷ Θ)` mints `lock (n + X)`; (3) the scope move's
outer frame becomes `bindsOnly Θ₂`, its scope deleted outright.
**Refuted as a package** (`proof/MwUObstruct.agda`, same commits), *under
the simultaneous `_⊢ᵐ_` of the day*.  Part (3) alone is good — the frame
lemmas become equalities, and `frame-move`'s `⊑` turns out to have been
an artifact of the retained unlocks.  But (2) forces (1), and (1) then
kills two things at once: `⊢retag` along `⊑`, because `le-mu` *unmasks* a
slot that an `unlock` cites and so destroys its claim; and `⊢ᵐ-⋉`,
because `_⋉_` builds lists that both lock and unlock one slot while (1)
makes `mw-l` and `mw-u` exact complements, so no simultaneous derivation
exists.  The structural diagnosis is what the entry is worth keeping for:
**`_⊢ᵐ_` was simultaneous and `scope` is sequential**, and the two cannot
both be right.

**D49 — the Δ-dependent dual (`δ`).**  Leave `_⊢ᵐ_` alone and let the
dual read the exterior: `dual Δ Θ` maps `unlock X ↦ lock X` only when `X`
is actually masked in `Δ`.  Reduction is already `Δ`-indexed, so `Peel`
may inspect `Δ`, and one read on the plain `Δ` respects simultaneity.
Vacuous unlocks then add nothing (so `preserve-Peel` survives),
non-vacuous ones are re-locked (so the leak closes), and (†) should stay
exact with no change to the scope move.  Probed on branch `dual-relock`
(`notes/DECISIONS.md`, "RULING: vacuous unlocks are wrong and
unreachable (Jeremy, 2026-09-06)"; commit `01459ab0`).  **Superseded, not
refuted**: it leaves the vacuous unlock *legal*, which Jeremy had just
ruled wrong — "why do we allow `↥X` over `X := ℕ` visible?  That feels
wrong … and unreachable" — and paying for it would have meant weakening
`mw-l`.  `D50` closes the leak and refuses the vacuous unlock at once.

**D50 — sequential `⊢ᵐ`, the exact dual, `rewind`, reps on
`unlockedScope`.**  The package that landed, from the probe run in
parallel with `D49` on branch `dual-principled` — an audit of every place
information was being dropped, then a repair at each (commits
`79bf9a7d`, `fa554db7`, `439dda14`; merged as PR #193, `b9da77f2`).
Four coupled parts:

* **`Δ ⊢ᵐ Θ` becomes SEQUENTIAL.**  Every premise is read on the frame
  its entry acts on, in the order `scope` applies the list (head-last):
  `mw-l` needs `scope Θ′ Δ ∋tv X`, `mw-u` needs `scope Θ′ Δ ∋lk X`, and
  `mw-b` reads its representation on `unlockedScope Θ′ Δ`.  No vacuous
  unlocks and no double locks, so `Locked` is one mask deep and
  `mask ∘ unmask` is the identity where the dual needs it.  Both of
  `D48`'s refutations dissolve: they were artifacts of reading every
  premise on the plain `Δ`.
* **The dual becomes an exact inverse.**  `unlock X ↦ lock (n + X)` —
  restoring what `Θ` unlocked — *and* the list is **reversed**, because
  `scope` applies it head-last.  Then (†)
  `interior (dual Θ) (interior Θ Δ)
  ≡ map masked (pushBinds (repsOf Θ) []) ++ Δ` is an equality: the
  crossing frame *is* the exterior, and the argument crosses by
  `⊢rename` alone.
* **`rewind Θ₂ = dualScope 0 Θ₂ ++ Θ₂`** as the scope move's outer frame,
  neither `dropLocks Θ₂` (its moved unlock goes vacuous) nor
  `bindsOnly Θ₂` (its own bind rep loses the unlock it was read past) —
  the two refutations that remain in `proof/MwUObstruct`, on
  `Δ₆ = ⌷[U := ℕ]`, `Θ₂ = ↥U`, `Θ₁ = ↑V:=U`, `Θ₁ ⋉ Θ₂ = ↑V:=U , ↥U`.
* **`⊢retag` runs along `_⊑ᵃ_`**, the refinement without `le-mu`: a term
  may travel along a refinement that learns a representation, never along
  one that unmasks a slot its boundaries cite.

Jeremy ratified item 2 of the package and ordered the merge ("RATIFIED:
representations read past the tail's unlocks; PR #193 merged (Jeremy,
2026-09-06)"): "That particular law was not valuable on its own, it was
just a design idea to try."  **Design law 4 is thereby reduced to its
surviving half** — a representation is never blocked by its own frame's
locks, and `pushBinds` lifts it past exactly the binders inside it —
while the "every premise on the plain exterior" half is retired.  The
tests that came out of the episode are `proof/DualTightness` (the
`unlock` half of `Peel`) and `Examples` §15 (every other rule that moves
a subterm into a new frame, with the five frame identities collected in
§15f and tabulated in `Design.md` §7).
