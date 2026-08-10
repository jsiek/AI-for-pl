# GTSFImp Source-Consistency Inventory

Branch: `agent/gtsf-source-consistency`.

Scope: read-only investigation of gate/inversion sites for
`_⊢_∼★`, `_⊢★∼_`, and `Var∼` mode equalities.  I did not edit
`GTSFImp/`, `PLAN.md`, or `TODO.md`.  The only scratch source added is
`SrcConsistBlocked.agda`.

Class legend:

- a: extends mechanically to a rigid gate; the site carries or renames gate
  evidence, or would add a parallel constructor case.
- b: relies on the current exclusivity "variable-to-star gate implies exact
  mode `X∼★`" or "star-to-variable gate implies exact mode `★∼X`"; a rigid
  gate would weaken or invalidate the stated fact.
- c: rigid variable gates are unreachable by other premises or indices.

## Scratch Check

`SrcConsistBlocked.agda` attempts the source term
`ΛX. λx:X. (λy:★. y) · x`.

Command:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 SrcConsistBlocked.agda
```

Result:

```text
/home/runner/AI-for-pl/SrcConsistBlocked.agda:19,16-17
No instance of type idᶜ Fin.zero Agda.Builtin.Equality.≡ ★∼X was
found in scope.
when checking that (id (＇ Fin.zero)) is a valid argument to a
function of type
{G B : Ty 1} ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : idᶜ ⊢★∼ G ⦄ →
idᶜ ⊢ G ∼ B → ⦃ Bns : NonStar B ⦄ → idᶜ ⊢ ★ ∼ B
```

This is exactly the current gate block for `★ ∼ ＇0` under `idᶜ`, where
`idᶜ Fin.zero = X∼X`.

## Gate Match / Inversion Sites

| Site | What it does | Class | Facts |
| --- | --- | --- | --- |
| `GTSFImp/Consistency.agda:23-31` | Defines `Var∼` and `flipVar∼`. | a | `flipVar∼ X∼X = X∼X`; a rigid gate would flip to a rigid gate on the opposite star judgment. |
| `GTSFImp/Consistency.agda:38-50` | Inverts flipped mode equalities to exact opposite dynamic modes. | b | Proves `flipVar∼ v ≡ X∼★ -> v ≡ ★∼X` and mirror; explicitly rejects `X∼X`. |
| `GTSFImp/Consistency.agda:82-98` | Defines ground-to-star gates. | b | Current variable gates require `μ X ≡ X∼★` or `μ X ≡ ★∼X`; this is the source block. |
| `GTSFImp/Consistency.agda:104-130` | Instance search for ground-to-star gates. | b | Variable instances require exact dynamic-side equalities, so rigid `X∼X` has no instance. |
| `GTSFImp/Consistency.agda:155-169` | Cast consistency constructors `_!` and `？_` store gate evidence. | a | Constructors are parametric in the gate evidence; no mode equality is inspected there. |
| `GTSFImp/Consistency.agda:233-247` | `flip-∼★` and `flip-★∼` invert gate judgments. | a | Variable cases only rebuild the opposite gate with `cong flipVar∼ eq`; a rigid case is parallel. |
| `GTSFImp/Consistency.agda:271-280` | `sym∼` flips `_!`/`？_`. | a | Delegates to `flip-∼★`/`flip-★∼`; no exclusive mode fact is used directly. |
| `GTSFImp/Consistency.agda:362-384` | Renames `_⊢_∼★` and `_⊢★∼_`. | a | Variable cases transport the stored equality along the renaming map; rigid cases are parallel. |
| `GTSFImp/Consistency.agda:407-414` | Renames `_!`/`？_` consistency evidence. | a | Gate evidence is renamed through `rename∼★`/`rename★∼`. |
| `GTSFImp/Consistency.agda:522-533` | `renameᵐᶜ-idᵍ!` proves renamed identity tags remain identity tags. | a | Pattern matches on the ground gate and returns `refl`; rigid variable case would be another `refl`-shaped case if the constructor is definitionally aligned. |
| `GTSFImp/Consistency.agda:549-555` | `SubstEnv∼` records substitution obligations for variable modes. | b | The interface only has `to-★ : μ X ≡ X∼★ -> ... ∼ ★` and `from-★ : μ X ≡ ★∼X -> ★ ∼ ...`; no obligation covers `μ X ≡ X∼X` producing a star cast. |
| `GTSFImp/Consistency.agda:561-654` | Extends/flips substitution environments. | b | `ext-SubstEnv∼` treats fresh exact dynamic modes as impossible; `flip-SubstEnv∼` uses the exact `flipVar∼-to-*` lemmas. A generalized rigid gate would not be covered by these exact-mode fields. |
| `GTSFImp/Consistency.agda:778-800` | `subst-to-star-var` and `subst-from-star-var`. | b | These turn variable ground casts through substitution by consuming exact `μ X ≡ X∼★` or `μ X ≡ ★∼X`. |
| `GTSFImp/Consistency.agda:812-837` | `inst-to-var-occurs-impossible` and `gen-from-var-occurs-impossible`. | c | Their premises are exact dynamic-mode equalities under `instᵐ`/`genᵐ`; rigid self mode is outside the statement. |
| `GTSFImp/Consistency.agda:839-894` | `factor-inst-star` and `factor-gen-star`. | a | Shifted variable-ground cases transport the gate outward. The fresh-zero variable subcases are unreachable for rigid because `instᵐ μ zero = X∼★` and `genᵐ μ zero = ★∼X`. |
| `GTSFImp/Consistency.agda:896-927` | `subst∼` handles variable-ground `_!`/`？_`. | b | Variable cases dispatch to `subst-to-star-var`/`subst-from-star-var`, so they require exact dynamic mode. |
| `GTSFImp/Consistency.agda:989-1035` | `close-inst-to/from-★` and `close-gen-to/from-★`. | a | Fresh inst/gen modes are dynamic by construction; old shifted variables would transport a parallel rigid gate if present. |
| `GTSFImp/Consistency.agda:1054-1069` | `open-to-★` and `open-from-★`. | b | For `extᵐ`, the fresh zero variable is currently impossible for exact dynamic modes. A rigid gate at zero would open to arbitrary `C`, not to a variable ground. |
| `GTSFImp/Conversion.agda:27-150` | Conversion generation and typing. | c | No match or inversion on source-consistency gates or `Var∼` modes. |
| `GTSFImp/CastTerms.agda:85-90,214-218` | Inert casts and cast typing store consistency evidence. | a | `inj` carries `G∼★` opaquely; cast typing accepts any `μ ⊢ A ∼ B`. |
| `GTSFImp/Reduction.agda:178-212` | Runtime `ground`, `expand`, `tag-untag`, `tag-untag-bad`. | a | Reduction rules carry gate evidence but inspect only ground names/types and value shape. |
| `GTSFImp/Eval.agda:32-51,196-280` | `inert?` and `cast-redex?`. | a | Uses `to-ground`/`from-ground` on inner consistency and `H ≟Ty G` for tag/untag; gate evidence is passed through. |
| `GTSFImp/proof/Reduction.agda:38-60` | Renames inert tags through type-store changes. | a | Pattern matches on `G∼★`; variable case shifts `X∼★ᵍ eq`. Rigid variable case would shift analogously. |
| `GTSFImp/proof/TypeInTermSubst.agda:257-272` | Renaming preserves tagged values. | a | Rebuilds `inj` using `rename∼★ᵐ`; gate evidence is opaque. |
| `GTSFImp/proof/TypeSafety/Progress.agda:80-85` | `StarView` recognizes tagged star values. | a | Stores `G∼★` opaquely. |
| `GTSFImp/proof/TypeSafety/Progress.agda:208-223` | `canonical-X`. | c | Closed values of type `＇X` are `↓ seal X R`, not star tags; rigid star tags still have type `★`. |
| `GTSFImp/proof/TypeSafety/Progress.agda:231-265,332-334` | Fresh-variable contradictions and `consistency-to-fresh`, used by `no-bot-value`. | b | Proves `extᵐ μ ⊢ A ∼ ＇0 -> A ≡ ＇0` by rejecting `★∼Xᵍ ()`; a rigid `★ ∼ ＇0` under `extᵐ` would be a new case. |
| `GTSFImp/proof/TypeSafety/Progress.agda:482-545` | Progress for casts over values. | a | `_!`/`？_` progress uses `to-ground`/`from-ground`; tag-untag compares ground types. |
| `GTSFImp/proof/TypeSafety/Preservation.agda:167-174` | Preservation for tag/untag and bad tag/untag. | a | Reconstructs target typing or blame; no gate mode inspection. |
| `GTSFImp/Consistency2.agda:33-43` | Maps consistency modes to left/right imprecision environments. | b | `X∼X` maps to precise on both sides; one-sided dynamic facts come only from `X∼★` or `★∼X`. |
| `GTSFImp/proof/Consistency2.agda:217-240` | `ground-occurs-to-star` / `ground-occurs-from-star`. | b | From a variable occurrence in a ground-to-star gate, concludes exact mode `X∼★` or `★∼X`. |
| `GTSFImp/proof/Consistency2.agda:242-252` | Flipped not-dynamic lemmas. | b | Uses `flipVar∼-to-*`, which excludes `X∼X`. |
| `GTSFImp/proof/Consistency2.agda:254-373` | Occurrence safety and dynamic-side conclusions. | b | Uses `ground-occurs-*` to show variables present in a term consistent with `★` are dynamic on the relevant side. |
| `GTSFImp/proof/ImprecisionConsistency.agda:32-43` | `VarLower` / `LowerEnv`. | b | `X∼X` can be precise-precise or both-to-star, but one-sided star facts are tied to `X∼★`/`★∼X`. |
| `GTSFImp/proof/ImprecisionConsistency.agda:86-102` | `right-star-from-var-lower` / `left-star-from-var-lower`. | b | Reject `X∼X` when asked for a one-sided star relation. |
| `GTSFImp/proof/ImprecisionConsistency.agda:355-396` | Converts variable lower-bound proofs to star lower-bound proofs. | b | Requires exact `μ X ≡ X∼★` or `μ X ≡ ★∼X`. |
| `GTSFImp/proof/ImprecisionConsistency.agda:441-489` | Common-lower proof for variable-ground `_!`/`？_`. | b | Variable tag/projection cases pattern on `X∼★ᵍ eq` / `★∼Xᵍ eq` and use exact-mode lower-bound lemmas. |
| `GTSFImp/proof/ImprecisionConsistency.agda:610-650` | Self-mode cannot occur in ground-to-star gates. | b | `ground-self-occurs⊥` and mirror contradict `X∼X` with `X∼★`/`★∼X`; rigid gates directly weaken this fact. |
| `GTSFImp/proof/ImprecisionConsistency.agda:652-744` | Consistency occurrence preservation for self-mode variables. | b | Uses `ground-self-occurs⊥` and mirror in `_!`/`？_` cases. |
| `GTSFImp/proof/ImprecisionConsistency.agda:754-768` | Inst-shift of gate judgments. | a | Constructor-by-constructor shift; rigid variable gate would be parallel. |
| `GTSFImp/proof/ImprecisionConsistency.agda:1506-1516` | `variable-to-star` / `star-to-variable`. | b | Public constructors from exact dynamic mode equality to variable-star consistency. |
| `GTSFImp/proof/ImprecisionConsistency.agda:1554-1578` | Infers exact consistency mode from one-sided imprecision shape. | b | Concludes `r ≡ X∼★` or `r ≡ ★∼X`, excluding `X∼X` when only one side is dynamic. |
| `GTSFImp/proof/DGG/SealPeelToolkit.agda:62-81` | `right-var-obligation-view`. | c | Inverts imprecision `R ⊑ᵂ ＇Y`; non-variable and `★` left sides are impossible independently of consistency gates. |
| `GTSFImp/proof/DGG/SealPeelToolkit.agda:201-209` | `var-consistency-view`. | a | For `ν ⊢ ＇Z ∼ R`, `id` gives `R = ＇Z`; any `_!` gives `R = ★`. It does not inspect the gate evidence inside `_!`. |
| `GTSFImp/proof/DGG/Inversion/SpineValueDef.agda:145-154` | `var-tag-value-sealed`. | a | Matches only on `Value (N ⟨ _! ... ⟩)` being `vN 《 inj 》`, then uses typing; no gate case split. |
| `GTSFImp/proof/DGG/CastTermImprecision2.agda:388-438` | `Rep★PartnerOK` var-tag, matched-inner-tags, round-trip clauses. | a | Variable tag evidence is stored opaquely; clauses require alignment or nonvar evidence, not mode equality. |
| `GTSFImp/proof/DGG/CastTermImprecision2.agda:509-538` | `TagRebaseAtᴸ` and forgetting. | c | `tag-rebase-onlyᴸ` has `Xᴿ? = nothing`; var-tag/matched-inner partner cases with `just Y` cannot inhabit that index. |
| `GTSFImp/proof/DGG/CenterRename.agda:336-349,360-375` | Renames tag-rebases and `Rep★PartnerOK`. | a | Var-tag/matched-inner clauses only rename alignment facts. |
| `GTSFImp/proof/DGG/TermImpDecay.agda:120-139,360-397` | Decays partner predicates and tag-rebases. | a | Var-tag/matched-inner clauses are structural; `tag-rebase-onlyᴸ` only transports imprecision environment facts. |
| `GTSFImp/proof/DGG/ExtraCastRight2.agda:117-142,166-176` | Generated projection/catchup cases carry tag/projection gates. | a | `G∼★`/`★∼G` are parameters and are not inspected. |
| `GTSFImp/proof/DGG/Catchup/ExtraCastRightProof.agda:305-356,389-432,636-668` | Extra-cast-right reductions for tag/projection. | a | Reduction chains use `tag-untag`/`expand`; ground equality, not gate mode, determines behavior. |
| `GTSFImp/proof/DGG/SealTransferCore.agda:126-174` | Dynamic partner lifting and payload seal partner. | a | `rep★-var-tag` path calls `var-tag-value-sealed`; gate evidence remains opaque. |
| `GTSFImp/proof/DGG/SealTransferCore.agda:194-212` | Transports `Rep★PartnerOK` through variable rebase. | a | `tag-rebase-varᴸ` transports alignment; gate evidence is not inspected. |
| `GTSFImp/proof/DGG/SealTransferCore.agda:293-316` | Transports `Rep★PartnerOK` through tag-only rebase. | c | Under `tag-rebase-onlyᴸ`, var-tag/matched-inner partners are index-unreachable because their partner index is `just Y`, not `nothing`. |
| `GTSFImp/proof/DGG/SealTransferCore.agda:318-340` | Builds protected tag partners from a cast. | a | Splits on cast ground and inner `c`; the `G∼★` gate of the outer `_!` is not inspected. |
| `GTSFImp/proof/DGG/SealTransferCore.agda:418-519` | Source-star package and round-trip decay. | a | Requires inert variable tag shape `G = ＇X`; gate evidence is not inspected. |
| `GTSFImp/proof/DGG/SealTransferCore.agda:715-722` | Seal transfer rejects `R = ★` with `right-var-obligation-view`. | c | Impossibility is from `★ ⊑ᵂ ＇Y`, independent of consistency gates. |
| `GTSFImp/proof/DGG/SealTransferCore.agda:731-748` | Emits matched seal-star partner. | a | Uses already-accepted `Rep★PartnerOK`; no mode inspection. |
| `GTSFImp/proof/DGG/Inversion/SourceStripColumnView.agda:72-95` | Column view on `rep★-var-tag`. | c | Calls `var-consistency-view cVar`; `inj₁` continues, `inj₂` is impossible by the indexed branch. A rigid `_!` would route to `inj₂`. |
| `GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda:881-909` | Source-strip emptiness for base/function/forall source heads. | c | Uses `right-var-obligation-view`; non-variable left types cannot be `⊑ᵂ` a right variable. |
| `GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda:1040-1062` | Source strip over seal-star branch. | c | `var-consistency-view` `inj₂` is impossible by indices; rigid tag would be in that impossible branch. |
| `GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda:1153-1163` | Dispatches `rep★-var-tag` to the seal-star worker. | a | Carries `cVar` to the worker; no mode inspection here. |
| `GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda:1338-1386,1463-1499` | Source-strip seal/cast and seal/source cases. | c | Same `var-consistency-view` shape: identity continues, tag-to-star branch impossible by indices. |
| `GTSFImp/proof/DGG/Inversion/TargetWalkSupport.agda:904-941` | Rejects tagged target under nonvar/nonstar source spine. | c | `right-var-obligation-view` forces a variable, then `var-consistency-view` branches are eliminated by `NonVar`/`NonStar`. |
| `GTSFImp/proof/DGG/Inversion/TargetWalkSupport.agda:956-965` | Rejects gen value at variable source. | c | Both `var-consistency-view` branches are impossible by type indices. |
| `GTSFImp/proof/DGG/Inversion/TargetChainProof.agda:259-302` | Target source-star chain through a variable tag. | a | Uses `var-consistency-view (sym∼ cᴿ)` and `var-tag-value-sealed`; outer tag gate is opaque. |
| `GTSFImp/proof/DGG/Inversion/RightInjInversion2Proof.agda:568-650` | Right-injection inversion through sealed variable tags. | a | Uses `right-var-obligation-view` and `var-consistency-view`; tag branch routes to star-chain cases or nonstar impossibilities, not mode equality. |
| `GTSFImp/proof/DGG/Inversion/TargetStripProof.agda:865-975,1106-1112` | Target-strip descent at target variables. | c | All listed gates are imprecision inversions via `right-var-obligation-view`; no consistency gate mode is inspected. |
| `GTSFImp/proof/DGG/Inversion/TargetStripProof.agda:1197-1211` | Dispatch payoff for nonvar-empty target strip case. | c | Emptiness is a stored `⊥` payoff from tag dispatch, not a mode equality argument. |
| `GTSFImp/proof/DGG/ReachabilityCatalog.agda:87-109` | Catalog examples for inst/gen variable tags/projections. | a | Examples use exact dynamic modes by construction (`instᵐ`/`genᵐ`); not an inversion dependency. |
| `GTSFImp/proof/DGG/notes/*Scratch.agda` | Preflight/probe files for tightened partner variants and traces. | a | The live-like tightened partner clauses inspect alignment/wrapper shape; scratch `tag-untag-bad` traces use ground inequality. These are not the live relation/proof surface. |

## Source Typing and Compile Facts

- Source typing is in `GTSFImp/GradualTerms.agda:81-130`; `Compile.agda:17-37`
  renames this judgment and constructors to `⊢ᴳ`.
- Ordinary application `⊢·` (`GradualTerms.agda:94-99`) requires `A ∼ A′`
  between the function domain and argument type.
- Dynamic-function application `⊢·★` (`GradualTerms.agda:101-106`) requires
  `A′ ∼ ★`.
- The blocked term uses ordinary application, not `⊢·★`: inside the `Λ`,
  `(λy:★. y)` has type `★ ⇒ ★`, and `x` has type `＇0`; the required witness is
  `★ ∼ ＇0` under `idᶜ`.
- `Compile.agda:82-85` compiles `⊢ᴳ·` by casting the argument with
  `symᶜ A∼A′`.  For a rigid-gated source witness `★ ∼ ＇X`, this path would need
  `sym∼` to produce the corresponding rigid-gated `＇X ∼ ★`.
- `Compile.agda:86-90` compiles `⊢ᴳ·★` by casting the function from `★` to
  `★ ⇒ ★` and casting the argument with the given `A′∼★`; a rigid `＇X ∼ ★`
  witness would flow directly through this clause.
- `Compile.agda:101-106` compiles primitive arguments by inserting the provided
  consistency casts; it does not inspect gate modes.
- DGG elaboration mirrors these facts: `proof/DGG/Elab.agda:201-206` recovers
  source typing from `E-·`/`E-·★`, `224-229` casts elaborated arguments, and
  `250-261` shows compile elaborates `⊢ᴳ·`/`⊢ᴳ·★` using the same consistency
  witnesses.
- Gradual term imprecision typing also passes these witnesses through:
  `GradualTermImprecision.agda:231-245` for source typing and `273-286` for
  target typing.

## Tag Discipline Interaction

- `var-tag-value-sealed` (`proof/DGG/Inversion/SpineValueDef.agda:145-154`)
  does not case on the gate. It only observes that a value of tagged form is
  `vN 《 inj 》`, then uses the inner typing of `N`.
- `Rep★PartnerOK` (`proof/DGG/CastTermImprecision2.agda:388-438`) stores
  variable-tag gate evidence opaquely. The var-tag and matched-inner clauses
  inspect only `CenterAligned` and, for matched-inner tags, `X₂ ≢ X`.
- `SealPartnerOK` and `MatchedConcealPartnerOK`
  (`CastTermImprecision2.agda:440-490`) lift those partner predicates; they do
  not inspect `μ X`.
- A rigid-gated variable tag would flow into rep-star seal-partner positions
  whenever the alignment/index premises select the var-tag path. Under
  `tag-rebase-onlyᴸ`, var-tag and matched-inner partners are index-unreachable
  because the target pivot is `nothing`.

## Sibling Comparison

- `GTSF/Consistency.agda:27-30` has assumption-context entries
  `X ~ᶜ★`, `★~ᶜ X`, and `X ~ᶜ Y`; variable-to-star consistency requires the
  explicit star-side assumption at `93-110`.  The ordinary forall case adds
  only `0 ~ᶜ 0` at `79-82`, so rigid variable-to-star is not admitted there.
- `GTSF/Consistency.agda:112-122` admits forall-vs-nonforall consistency by
  extending the context with `0 ~ᶜ★` or `★~ᶜ 0`, i.e. by switching the bound
  variable to a dynamic-side assumption.
- `PolyG/PolyG.agda:38-56` uses a simple surface consistency relation:
  `TDyn ∼ A` and `A ∼ TDyn` are always available, while names are consistent
  only with the same name. There is no `Var∼` mode environment.
- `PolyBlameI` has no separate `Consistency.agda`; casts are `up`/`down`
  imprecision (`PolyBlameI/PolyBlame.agda:41-50`).  Type-variable imprecision is
  identity-only (`PolyBlameI/Imprecision.agda:78-80`), while tagging to `★`
  uses `Ground` (`Imprecision.agda:101-106`), and `Ground` excludes rigid type
  variables (`PolyBlameI/Types.agda:69-72`).

## Reduction Semantics Facts

- `_!` and `？_` over rigid variable grounds would use the existing runtime
  tag/projection forms; no new runtime term form is visible in `Reduction.agda`,
  `Eval.agda`, or `CastTerms.agda`.
- `tag-untag` (`Reduction.agda:196-203`) reduces same-ground tag/projection
  pairs to the payload.  For variable grounds, same name is equality of the
  ground type `＇X`.
- `tag-untag-bad` (`Reduction.agda:205-212`) blames when ground types differ.
  `Eval.agda:240-259` decides this with `H ≟Ty G`, not with gate evidence.
- `Progress.cast-value-progress` (`proof/TypeSafety/Progress.agda:515-539`)
  mirrors the evaluator: after `canonical-★`, same ground gives `tag-untag`,
  different ground gives `tag-untag-bad`.
- Canonical forms at `＇X` are unchanged by variable tags:
  `canonical-X` (`Progress.agda:208-223`) recognizes only sealed values of type
  `＇X`; variable tags classify values at type `★`.
- The only reduction/progress support that pattern matches on ground-to-star
  gate constructors is administrative transport such as
  `proof/Reduction.agda:38-60`, which shifts inert tags and does not inspect
  mode equality for runtime behavior.
