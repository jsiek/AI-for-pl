# CTI Tightening Calibration: S-NARROW

Status: evaluation only.  No live CTI2 or proof files were edited.

## Designed Premises

The scratch `CTITighteningNarrowScratch.agda` models the CTI2 analogue of the
GTSF cast-shape premises as:

- `CastDirection = widening | narrowing`.
- `direction ⊢ᶜ c ⦂ s`, where `s` is a proof-relevant cast shape.  Unlike the
  GTSF model's generic `tagˣˢ`, the CTI2 scratch keeps the ground type in
  `tagˢ G`, so variable tags/projections preserve `G = ＇ X`.
- `SourceCastOK W c p q`: source-side composition against world witnesses.
  Widening composes as `s ; q = p`; narrowing composes as `s ; p = q`.
- `TargetCastOK W c p q`: target-side composition.  Widening composes as
  `p ; s = q`; narrowing composes as `q ; s = p`.
- `PairedCastOK W c c′ p q`: paired-cast composition.  It does not require an
  actual source-first or target-first term-imprecision intermediate, because
  paired upcasts such as `ℕ!`/`ℕ!` would otherwise need the invalid witness
  `★ ⊑ ℕ`.  Instead it records the common composition boundary directly.

The reveal/conceal family does not need the same treatment for this candidate:
`⊑reveal²`, `reveal⊑²`, and `reveal⊑reveal²` already carry pivot-indexed
conversion typing (`⊢↑[ X? ]`/`⊢↓[ X? ]`) plus `RebaseAt`/`RebaseAtᴸ`/
`RebaseAtᴿ` and store-representation premises.  The endpoint-only gap is in
ordinary consistency casts, not in conversion wrappers.

## Matrix

| Cell | S-NARROW verdict | Evidence |
| --- | --- | --- |
| C1 Soundness | **CHECKED-FAIL** | `projection-mismatch-still-derivableᴺ` typechecks.  The bad `X?`/`Y?` paired projection still composes through the common boundary `X ⊑ ★`. |
| C2 Compile monotonicity | **BLOCKED** | Direct compile sites are enumerated below.  The scratch checks representative paired base, source one-sided, and target one-sided sites (`compile-paired-base-site`, `compile-source-one-sided-site`, `compile-target-one-sided-site`), but the live proof would need generic shape/composition lemmas for arbitrary consistency evidence (`A∼C`, `d′`, `c′`). |
| C3 Good executions | **CHECKED-OK, partial** | `matching-projectionᴺ` and `good-generated-catchup` check the matching generated-name projection/catch-up shape.  This confirms the intended positive square survives, but the full reachability catalog was not ported to the mini-relation. |
| C4 Migration inventory | **CHECKED-FAIL for cost** | Premises are often available after destructing a CTI2 derivation, but many rebuild sites need new threading/transport lemmas.  See inventory below. |
| C5 LR cell | **BLOCKED** | The requested LR worktree is outside `/home/runner/AI-for-pl`; the repo instructions say never read files outside the current directory. |

## C2 Compile Sites

`CompilePreservesImprecision2.agda` builds the three ordinary cast rules at
seven direct sites:

- `:506` application argument paired cast:
  `cast⊑cast² (symᶜ A∼C) d′`.
- `:556` dynamic callee target insertion:
  `⊑cast² c′`.
- `:558` dynamic application argument paired cast:
  `cast⊑cast² (symᶜ A∼C) d′`.
- `:595` dynamic-function callee paired cast:
  `cast⊑cast² CPI.dynamic-function-cast c′`.
- `:597` dynamic argument paired cast:
  `cast⊑cast² C∼★ d′`.
- `:749` primitive left argument paired cast:
  `cast⊑cast² A∼arg c′`.
- `:753` primitive right argument paired cast:
  `cast⊑cast² B∼arg d′`.

The type-application clauses do not directly build these three CTI2 cast
rules; inst/gen consistency evidence appears inside application casts and
catch-up machinery.  A migration would need a reusable consistency-shape
extraction and composition theorem, not one-off premises at each compile site.

## C4 Inventory

Available with local threading:

- `CastTermImprecision2Typing`: constructor premises are unused by typing.
- `Examples2`, probes, and counterexample modules: direct witnesses can be
  updated locally, but there are many example constructors.
- `CenterRename`, `TargetExtend`, `TargetBindLift`, `TermImpDecay`: the old
  premises are available by pattern matching, but each file needs transport
  lemmas for `⊢ᶜ`, `SourceCastOK`, `TargetCastOK`, and `PairedCastOK`.

Needs new threading, high risk:

- Inversion stack (`RightInjInversion2Proof`, `SourceStripWorkerProof`,
  `TargetStripProof`, `TargetChainProof`, `TargetWalkSupport`): many branches
  rebuild `cast⊑²`, `⊑cast²`, or `cast⊑cast²` after changing the endpoint
  witness.  The M3 seal-transfer/tag-discipline branches need the new
  composition evidence exactly where they currently re-emit a cast from
  geometric facts.
- NS-4 absorption/equal helpers:
  `StructuralTargetFrameAbsorptionDef` must carry target-cast composition in
  `tfa-cast`; `ExtraCastRightProof` must preserve shape through `χs ▶ᶜ tag`;
  `StructuralValueInstantiationCastProof` and `InstInversionLambdaProof` need
  post-prefix packages extended with source-cast composition.
- `SealTransferCore`: direct `cast⊑²` rebuilds around sealed terms need source
  cast-shape premises threaded from the seal-transfer geometry.
- `CompilePreservesImprecision2`: all seven direct cast-emission sites need
  generic consistency-shape/composition lemmas.

## Assessment

S-NARROW is not a sufficient CTI tightening.  The checked scratch shows the
bad square still has exactly the paired-composition evidence the candidate
would ask for.  The missing invariant is not ordinary cast direction; it is
runtime provenance that distinguishes a generated `Y?` facing its matching
`Y!` from a paired `X?`/`Y?` constructor that manufactures the same boundary
without that value-flow history.

# CTI Tightening Calibration: S-PROV

Status: evaluation only.  No live CTI2 or proof files were edited.  The checked
scratch is `CTITighteningProvScratch.agda`.

## Column Summary

| Candidate | Scope | Verdict | Reason |
| --- | --- | --- | --- |
| S-NARROW | Direction/shape composition only | **Refuted** | C1 still derives the bad square because the bad and good projections have identical cast/world endpoints. |
| S-WORLD | Items 1-3 only: provenance cells and capability-gated `⊑ᵂ`, type-level cast rules | **Refuted** | C1-W still derives the bad square by rerouting through the good square's final target-projection tuple. |
| S-PROV CORE | Items 1-5: provenance cells, decay capability, runtime alignment witnesses, cast-derivation relation, term-shaped projections | **Recommended** | C1 blocks the mismatch and keeps the matching and residual controls.  C2 is compatible when the term-shaped clause is scoped to generated/runtime-aligned projections. |
| S-OCC | Occupancy-gated source-seal see-through partner | **Checked viable** | C1 blocks the bad square at the aligned source-seal/bare-target premise, while pre-alignment see-through, matched post-alignment seals, and existing catch-up/projection machinery remain available. |
| S-PROV item 6 | Remove `CatchupCast`, `CatchupCast⁻`, and `CatchupColumn` | **Defer** | It reworks the M4/M6/NS-4 fuel knot and is not needed for the CORE tightening. |

## CORE Rule Forms

World cells carry provenance in addition to the current imprecision mark:

$$
\mathsf{cell}
  = (\mathsf{birth}, \mathsf{current}, \mathsf{capability},
     \mathsf{occupancy}, \mathsf{allocation}, \mathsf{castAncestry})
$$

The constructors used by the scratch are the statement-level fragment needed
for the calibration:

- `matched-birth` with `matched-use` for `Λ⊑Λ²`/matched bindings.
- `source-only-birth` with `source-star-use` for source-only `Λ⊑²`.
- `matched-occupied`, `source-open`, and `runtime-aligned` occupancy.
- `matched-generated-cast` and `residual-after-cancel` cast ancestry.

Decay changes the current mark, but not use capability:

$$
\mathsf{decay}
  (b, X{\sqsubseteq}X, u, o, a, c)
  = (b, X{\sqsubseteq}\star, u, o, a, c)
$$

Runtime alignment of a source-only cell requires explicit witnesses, not just
the endpoint mark:

$$
\mathsf{RuntimeAlignment}(W, X_L, X_R)
  = \mathsf{cellProv}
    \times \mathsf{StoreRepImp}(W, X_L, X_R)
    \times \mathsf{RebaseAt}(W, W, X_L, X_R)
    \times \mathsf{castAncestry}
$$

The cast rules split ordinary non-projection casts from generated projections:

- `cast⊑cast²` carries related cast derivations and direction/shape data.  A
  paired projection must expose either a matching injected target input or the
  residual-after-cancellation derivation below.
- `⊑cast²` non-projection clauses cover identity and widening insertions.
- `⊑cast²` same-tag generated projection is term-shaped:

$$
\frac{
  \pi : \mathsf{RuntimeAlignment}(W, X_L, X_R)
  \qquad
  D : W \mid \gamma \vdash M \sqsubseteq V\langle G! \rangle : A\sqsubseteq\star
}{
  W \mid \gamma \vdash
  M \sqsubseteq V\langle G! \rangle\langle G? \rangle : A\sqsubseteq G
}
$$

- The expanded/residual clause retains the injection derivation and a recursive
  residual CTI derivation after the matching pair cancels:

$$
\frac{
  D_{\mathsf{inj}} :
    W \mid \gamma \vdash M \sqsubseteq V\langle G! \rangle : A\sqsubseteq\star
  \qquad
  D_{\mathsf{res}} :
    W \mid \gamma \vdash M \sqsubseteq V\langle c \rangle : A\sqsubseteq B
}{
  W \mid \gamma \vdash
  M \sqsubseteq V\langle G! \rangle\langle G?;c \rangle : A\sqsubseteq B
}
$$

There is no projection constructor for
`V⟨H!⟩⟨G?⟩` when the retained CTI derivation only reaches `V⟨H!⟩`.
The source-side projection rule should be symmetric.

## Matrix

| Cell | S-PROV CORE verdict | Evidence |
| --- | --- | --- |
| C1 Soundness | **CHECKED-OK** | `bad-base-target-Y-project-clause-empty`, `bad-target-projection-underivable`, and `bad-paired-projection-underivable` typecheck.  The matching controls `matching-projectionᴾ` and `post-cancellation-residualᴾ` also typecheck. |
| C2 Compile monotonicity | **CHECKED-OK** | For scoped CORE, the site audit below finds no compiler-emitted bare generated-name projection onto a value.  Non-projection representatives check as `compile-paired-base-siteᴾ`, `compile-source-one-sided-siteᴾ`, and `compile-target-one-sided-siteᴾ`.  If the term-shaped clause bans every projection, not just generated/runtime-aligned projections, sites `:556` and `:595` fail. |
| C3 Good executions | **CHECKED-OK** | `good-generated-projection-siteᴾ`, `good-generated-catchupᴾ`, and `residual-after-cancellation-siteᴾ` typecheck.  These match the successful states in `SourceReachabilityResultScratch.agda` (`target-route`, `reached-catchup`) and the cast-heavy examples spot-checked below. |
| C4 Migration inventory | **CHECKED-OK** | The needed premises are identifiable, but live migration has high cost: statement changes and new threading through world evolution, inversion, seal-transfer, Λ, NS-4, decay, rebase/smart-alias, rename/extend, and compile². |
| C5 LR cell | **CHECKED-OK** | The LR reference cast phase needs same-tag projection evidence and residual recursion; CORE supplies both.  `CastComposition.agda` is parameterized by the cast-phase theorem and needs no extra CTI rule. |
| C6 Item-6 cost | **CHECKED-OK** | Audit complete; recommendation is **DEFER**.  Removing catch-up judgments would replace the current term-independent tail embedding used by M4/M6/NS-4.  CORE does not yet provide that replacement. |

## C2 Compile Audit

`Compile.agda` emits casts only in ordinary application, dynamic application,
and primitive arguments:

- `Compile.agda:82-90`: ordinary argument cast and dynamic callee/argument
  casts.
- `Compile.agda:101-106`: primitive argument casts.
- Variables, lambdas, type lambdas, type application, and constants emit no
  ordinary casts directly.

The direct CTI2 cast-emission sites in `CompilePreservesImprecision2.agda` are:

| Site | Constructor | CORE premise |
| --- | --- | --- |
| `:506` | `cast⊑cast² (symᶜ A∼C) d′` | Paired non-projection shape/derivation relation. |
| `:556` | `⊑cast² c′` for dynamic callee insertion | Needs a separate non-generated dynamic projection allowance if `c′ = dynamic-function-cast`; it is not a generated-name value projection. |
| `:558` | `cast⊑cast² (symᶜ A∼C) d′` | Paired non-projection shape/derivation relation. |
| `:595` | `cast⊑cast² dynamic-function-cast c′` | Same caveat as `:556`, now paired.  It cannot satisfy a rule that requires the callee input to be syntactically `V⟨G!⟩`. |
| `:597` | `cast⊑cast² C∼★ d′` | Paired non-projection widening. |
| `:749` | `cast⊑cast² A∼arg c′` | Paired primitive-argument cast. |
| `:753` | `cast⊑cast² B∼arg d′` | Paired primitive-argument cast. |

The compile-image worlds are compatible with the provenance discipline:
`initialWorld` uses identity embeddings and equal source/target stores, so it
mints no runtime-aligned cells.  The proof enters new cells only through the
existing lift/bind machinery; CORE must make those binders mint
`matched-birth`/`matched-use` for matched binds and
`source-only-birth`/`source-star-use` for source-only binds.

Conclusion for C2: compile is monotone for the scoped CORE rule.  A blanket
"every projection must be term-shaped over `V⟨G!⟩`" version is too strong for
compile because dynamic function casts are syntactic elaboration casts in
callee position.

## C3 Good-Execution Checks

The mini-relation keeps the good states that S-NARROW was meant to preserve:

- `matching-inputᴾ`: source sealed term relates to the generated target
  injection `V⟨Y!⟩`.
- `matching-projectionᴾ`: the matching `Y?` projection is derivable because the
  target input is exactly `V⟨Y!⟩` and the CTI derivation to that input is
  retained.
- `post-cancellation-residualᴾ` and `residual-after-cancellation-siteᴾ`: the
  post-cancellation target value remains related by the recursive residual
  derivation.

Spot checks against live notes/examples:

- `SourceReachabilityResultScratch.agda`: `target-route` reduces through the
  target-side unseal/catch-up path, and `reached-catchup` uses
  `generated-project-same target-sealed-value`; this is exactly
  `good-generated-catchupᴾ`.
- `Examples2.agda`: `example12-initial-poly` uses two target-side `⊑cast²`
  witnesses around polymorphic instantiation; these are compile/example casts,
  not the bad generated-name mismatch.
- `ReachabilityScreen.agda`: reachability checkpoints using generated
  projection/catch-up follow the same `V⟨G!⟩`-then-`G?` shape as the scratch.

## C4 Migration Inventory

| Site family | Verdict | Migration note |
| --- | --- | --- |
| M3 inversion stack: `RightInjInversion2Proof`, `SourceStripWorkerProof`, `TargetStripProof`, `TargetChainProof`, `TargetWalkSupport` | Statement change needed | Inversion must expose the projection subderivation, runtime-alignment witness, and residual CTI derivation instead of rebuilding endpoint-only cast constructors. |
| Seal-transfer/tag discipline: `SealTransferCore` and `Rep★PartnerOK` packages | New threading needed | The store/tag facts are already present, but partner packages must also carry birth/use/cast ancestry so generated projections can be justified after transfer. |
| Λ machinery: `Λ⊑Λ²`, `Λ⊑²`, `TargetBindLift`, `InstInversionLambdaProof` | Statement change needed | Binder constructors must mint provenance cells; lift/inst inversion must transport the new fields through type-variable movement. |
| NS-4 equal helpers and absorption chain: `StructuralTargetFrameAbsorptionDef`, `ExtraCastRightProof`, `ExtraCastRightAtProof`, `StructuralValueInstantiationCastProof`, `StructuralNameInstantiationProof` | New threading needed | `tfa-cast` and extra-cast packages must carry target/source cast provenance instead of only a cast term and endpoint witness. |
| Decay: `WorldDecay`, `TermImpDecay` | Premises available with new lemmas | Decay already has `ImpEnvMono`; it needs the stronger lemma that capability and ancestry survive while the current mark weakens. |
| Parked world and `ImpEnv`: `ParkedWorldDef`, `CastTermImprecision2` world/lift constructors | Statement change needed | `World` and parked-world evolution must store birth origin, use capability, occupancy/allocation ancestry, and cast ancestry. |
| Rebase/smart-alias: `RebaseAt`, `RebaseAtᴸ`, `RebaseAtᴿ`, smart comma/alias guards | New threading needed | Alignment must be witnessed by allocation/store/cast ancestry rather than inferred from `X⊑★` marks alone. |
| `CenterRename` | Premises available with transport lemmas | Structural rebuilds can keep the evidence, but rename lemmas are needed for cell provenance and retained projection derivations. |
| `TargetExtend` and `TargetBindLift` | Premises available with transport lemmas | Target extension/lift must transport runtime-alignment witnesses and preserve the injected-input shape. |
| `CompilePreservesImprecision2` | Premises available, with dynamic-projection caveat | Seven direct sites need reusable cast-shape/provenance lemmas.  Sites `:556` and `:595` require the scoped non-generated projection allowance. |

Compared with the S-NARROW C4 inventory, S-PROV has strictly higher world-state
cost: it changes `World`, parked-world evolution, decay, and rebase/smart-alias
statements.  The cast-rebuild cost is shared with S-NARROW, because both
candidates require new premises at every `cast⊑²`/`⊑cast²`/`cast⊑cast²`
consumer.  The difference is that S-NARROW pays most of this cost and still
fails C1, while S-PROV adds provenance threading and actually blocks the bad
projection.

## C5 LR Cell

The read-only LR reference copies in `notes/lr-reference/` need exactly the
information CORE records:

- `Cast.agda` projection/projection cases use dynamic-payload and projection
  step views, then need evidence that the target projection tag matches the
  retained injection tag.
- The residual branches need a recursive CTI derivation after the matching
  injection/projection pair cancels.
- `CastComposition.agda` composes the cast phase around the theorem returned by
  `Cast.agda`; it does not require item 6.

This audits as **CHECKED-OK** for CORE.

## C6 Item-6 Cost

The catch-up removal is separable from the tightening:

- `ValueCatchupRightDef.agda` deliberately splits head `CatchupCast` from
  projection-free tail `CatchupCast⁻`, then packages them as `CatchupColumn`.
- `Catchup⁻Embedᵀ` can re-head a tail at an arbitrary target term.  The fuel
  knot uses that term-independent embedding in `ValueCatchupRightProof` and
  `FuelKnotProof`.
- `InstInversionDef`, `ColumnSupportProof`, and
  `StructuralNameInstantiationProof` thread `CatchupCast⁻` through NS-4
  residual provenance and target-frame absorption.

CTI-internal inversion may eventually replace this family, but CORE by itself
does not supply the key operation: embedding a projection-free residual tail at
an arbitrary new target value while preserving the provenance needed by the
fuel knot.  Bundling item 6 would turn a focused CTI tightening into a larger
M4/M6/NS-4 redesign.

Verdict: **defer item 6**.  Keep the catch-up judgments while landing CORE,
then remove them in a separate arc once CTI-internal inversion has the same
term-independent tail embedding story.

## S-WORLD Column

Status: evaluation only.  No live CTI2 or proof files were edited.  The checked
scratch is `CTITighteningWorldScratch.agda`.

The faithful S-WORLD rendering used for the negative test records
`probe-cell` as
`source-only-birth, mark-X⊑★, source-star-use, runtime-aligned,
matched-generated-cast`.  `SourceStarCapability` gates the `X⊑★` endpoint, and
`RuntimeAlignment` gates the `qXY : ＇X ⊑ᵂ ＇Y` endpoint with explicit
`StoreRepImp`, `RebaseAt`, and cast-ancestry witnesses.  `decay-cell` changes
only the current mark, with `decay-preserves-capability` and
`probe-decay-preserves-capability` checking that capability is preserved.  A
stricter matched-only endpoint gate was also checked: it proves
`strict-runtime-endpoint-blocks-good-square`, so it blocks the genuine runtime
state and is too strong for the positive control.

| Cell | S-WORLD verdict | Evidence |
| --- | --- | --- |
| C1-W Soundness | **CHECKED-FAIL** | Outcome A: `world-only-bad-square-still-derivableᵂ` typechecks.  The derivation first builds the source side through `X!` and `X?` back to `X⊑★W`, then applies `target-project-Y?-OKᵂ`. |
| Positive control | **CHECKED-OK** | `matching-projectionᵂ`, `good-generated-projection-siteᵂ`, `post-cancellation-residualᵂ`, and `good-generated-catchupᵂ` typecheck with the same rule set. |
| C2 Compile representatives | **CHECKED-OK** | `compile-paired-base-siteᵂ`, `compile-source-one-sided-siteᵂ`, and `compile-target-one-sided-siteᵂ` typecheck. |
| Strict variant | **CHECKED-FAIL for viability** | `strict-runtime-endpoint-blocks-good-square` shows the only stricter plausible gate blocks the positive `qXY` endpoint itself. |

Verdict: world-only tightening does not suffice.  The distinguishing power
missing from S-WORLD is term-level memory of the target input to the final
projection.  In the good square and rerouted bad square, the final rule uses
the same world `N.W`, the same premise witness `N.X⊑★W`, the same conclusion
witness `N.qXY`, the same cast `N.Y?`, and the same capability/runtime
alignment witnesses.  The only difference is the target term before the final
projection: the good square has the generated input `V⟨Y!⟩`, while the bad
square has `0⟨ℕ!⟩`.  A type-level target cast rule cannot see that difference;
the term-shaped projection/residual clauses from S-PROV CORE are the needed
extra invariant.

## S-OCC Column

Status: evaluation only.  No live CTI2 or proof files were edited.  The checked
scratch is `CTITighteningOccScratch.agda`.

The faithful S-OCC rendering keeps the ordinary cast premises and target
projection witnesses from S-NARROW/S-WORLD, and changes only the source-seal
partner discipline.  The scratch has two occupancy states:

- `pre-occ = source-only-cell`, a source-only cell with no target occupant.
  In this state `star-rep-targetᴼ` is available and delegates to the existing
  `Rep★PartnerOK`.
- `aligned-occ = target-occupied-cell`, the probe state where target `Y`
  occupies the shared center.  In this state `star-rep-targetᴼ` requires
  `NoTargetOccupant aligned-occ`, which is empty.

Matched target seals are unchanged: `matching-outputᴼ` uses the existing
`matched-seal-star-partner`, and `matching-inputᴼ`/`matching-projectionᴼ` then
use the unchanged `Y!`/`Y?` cast witnesses.  `post-alignment-input-is-taggedᴼ`
aliases the reachability fact that the target input before projection is
`target-sealed ⟨ Y! ⟩`.

| Cell | S-OCC verdict | Evidence |
| --- | --- | --- |
| C1 Soundness | **CHECKED-OK** | `bad-input-underivableᴼ`, `source-tagged-bare-underivableᴼ`, `source-projected-bare-underivableᴼ`, and `bad-square-underivableᴼ` typecheck. |
| C2 Compile monotonicity | **CHECKED-OK** | Base compile representatives check in both regimes: `aligned-baseᴼ`, `aligned-target-one-sided-baseᴼ`, `aligned-source-one-sided-baseᴼ`, `pre-baseᴼ`, `pre-target-one-sided-baseᴼ`, and `pre-source-one-sided-baseᴼ`.  The source-seal see-through representative is checked only in the source-only world as `prealignment-see-throughᴼ`, matching initial/compile-image worlds with no aligned occupant. |
| C3 Good executions + skew window | **CHECKED-OK** | Pre-alignment see-through checks as `prealignment-see-throughᴼ`; post-alignment matched seals and generated projection check as `matching-outputᴼ`, `matching-inputᴼ`, `matching-projectionᴼ`, and `good-generated-catchupᴼ`.  The skew window does **not** exist in the checked reachability run: `post-alignment-input-is-taggedᴼ` fixes the input as sealed-and-`Y!`-tagged, and `target-catchup-routeᴼ` is the existing two-step cancellation route. |
| C5 LR cell | **CHECKED-OK** | The LR reference needs same-tag projection facts and residual recursion.  S-OCC does not make these CTI-internal, but it keeps the existing `CatchupCast`/projection machinery that supplies `generated-project-same` and the residual cast recursion. |

### C1 Reroute Table

| Attempted route | Checked name | Why it dies |
| --- | --- | --- |
| Direct aligned source seal vs bare target at `X ⊑ ★` | `bad-input-underivableᴼ` | The only live bad partner shape is `star-rep-target`; in `aligned-occ` its `NoTargetOccupant` premise is empty.  `plain-target` cannot match a top cast, and `name-protected-target` cannot match the bare non-sealed target. |
| Cast source through `X!`, then project back through `X?` | `source-tagged-bare-underivableᴼ`, `source-projected-bare-underivableᴼ`, `bad-square-underivableᴼ` | The source/paired cast-shape premises refine the intermediate endpoints back to the sealed-source/bare-target premise, which is already empty. |
| Try the `X ⊑ X` variable witness instead of the `X ⊑ ★` witness | `route-X⊑X-variable-witness-closedᴼ` | The target is still the bare `ℕ!` value; the aligned source-seal partner gate closes before the endpoint witness matters. |
| Try the `rep★-round-trip` source package | `route-rep★-round-trip-closedᴼ` | The enclosing `star-rep-targetᴼ` is rejected by occupancy before the round-trip subcase can reopen see-through. |
| Try a variable-tagged sealed source value | `var-tag-value-sealed-bare-target-closedᴼ` | This is the `var-tag-value-sealed` territory: target values carrying the partnered seal/tag are good, but the bare non-`Y` target still needs the aligned star-rep see-through gate, which is empty.  No blames-right/returns-left witness derives. |

### C3 Skew Window

The live reduction rules make the allocation/tag step atomic for the relevant
target generation.  `β-gen` allocates with `bind C` and returns the already
casted contractum `⇑ᵗᵐ V ⟨ c ⟩ ...`; `β-inst` similarly allocates with
`bind ★` and returns the wrapped/casted contractum.  The checked reachability
state agrees: immediately before the generated projection, the target input is

$$
\left((0\langle\mathbb{N}!\rangle)
  \mathbin{\downarrow}\operatorname{seal}Y\,\star\right)
\langle Y!\rangle .
$$

So there is no reachable state in this run where the cell is occupied while
the target copy relevant to the relation is still the unsealed bare
`0⟨ℕ!⟩`.  The only unsealed-target state checked by S-OCC is the
pre-alignment one, `prealignment-see-throughᴼ`, where the cell has no target
occupant and the see-through premise is intentionally available.

## S-OCC vs S-PROV CORE

Both S-OCC and S-PROV CORE pass this calibration, but they move the invariant
to different places.  S-PROV CORE changes the cast/projection clauses so
generated projections must retain the matching injected target input or a
post-cancellation residual derivation; this directly serves M3 inversion and
LR-style projection reasoning, but forces term-shaped cast-premise threading
through `cast⊑²`/`⊑cast²`/`cast⊑cast²` consumers.  S-OCC is narrower: it
changes the seal partner predicate and world evolution so source-seal
see-through is available only before target occupancy.  That is less invasive
for M4/M6/NS-4 and item-6-style cleanup because `CatchupCast`,
`CatchupCast⁻`, `CatchupColumn`, and ordinary target projection rules remain
unchanged.  Its live migration cost is instead concentrated in world occupancy
tracking plus every consumer that transports or rebuilds
`SourceConcealPartnerOK`/`SealPartnerOK` through M3 seal transfer, target
extension/bind lift, center rename, and decay.

Conclusion: S-OCC is a viable lower-surface alternative if the live proof can
maintain the reachability invariant that every bad blames-right/returns-left
projection must pass through aligned source-seal/bare-target see-through.
S-PROV CORE is more explicit and robust at the cast rule itself, but also more
invasive for cast consumers.

## Recommendation

Do not land S-NARROW or S-WORLD.  S-PROV CORE remains the more explicit
cast-rule repair; S-OCC is now a checked viable alternative with a smaller
cast-consumer surface but a stronger burden on world occupancy and source-seal
partner transport.  Defer item 6 under either viable route until after the
chosen tightening is green.
