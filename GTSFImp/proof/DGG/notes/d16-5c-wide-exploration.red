# D16 5c wide exploration: marks, representations, and pairing history

Date: 2026-08-19

Status: DESIGN RECONNAISSANCE ONLY.  No live relation, world, store,
reduction, or proof definition is changed.  The checked audit probe is
`proof/DGG/notes/probes/D16WideMarkIndependenceProbe.agda`.

This memo deliberately does not select a direction.  It widens the search
beyond the rejected fixture-mark edit, invariant-(5) refinement, and local
store-mediated judgment.  The rankings in Section 6 report two different
axes--frictions removed and risk--and are not a recommendation.

Files and internal branch material read for this pass include:

- `Imprecision.agda`, `TyStore.agda`, and `Reduction.agda`;
- `proof/DGG/CtxImp.agda`, `WorldInvariants.agda`, `WorldDecay.agda`,
  `CenterRename.agda`, `TargetBindLift.agda`, and `TargetExtend.agda`;
- `proof/DGG/Example12Worlds.agda`, `Examples2.agda`,
  `SmartCommaWitness.agda`, and the live finite world probes;
- `proof/DGG/notes/d16-5b-paired-seal-first-try.red` and
  `d16-smart-alias-invariant-blocked.red`;
- `proof/DGG/notes/t14-partner-premise-redesign.red`;
- `proof/DGG/notes/CTI-TIGHTENING-CALIBRATION.md` and its provenance
  scratches;
- `proof/DGG/notes/probes/T15WorldInvariantsDesignProbe.agda`,
  `T15Invariant5ReconProbe.agda`, and
  `D16PairedSealRecalibrationProbe.agda`;
- the repository-internal D18 policy note and probe at
  `agent/gtsf-dispatcher-residuals:GTSFImp/proof/DGG/notes/`
  `d18-rebase-tightening-design.red` and
  `probes/D18RebaseTighteningProbe.agda`.

## 0. World-display notation

Worlds are displayed in the canonical `worldSnapshot` cell notation from
the repository's world-grid branch:

```text
<center>: <source pivot and direct entry, or ─>
          ⊑[<mark>]
          <target pivot and direct entry, or ─>
```

Cells are ordered by the shared center.  For example,

```text
⟨C: X↦ℕ ⊑[X⊑X] Y↦ℕ⟩
```

means that source `X` and target `Y` are aligned at center `C`, both direct
entries are `ℕ`, and `impEnv C = X⊑X`.  Displays below are rendered by hand
because `WorldSnapshot.agda` is not on this branch.

## 1. Disease diagnosis

### 1.1 The three pieces of per-variable data

The live world stores three logically different facts around a source
variable:

1. **The mark.**  `impEnvʷ W Z : VarImp` is one of:

   ```agda
   data VarImp : Set where
     X⊑X : VarImp
     X⊑★ : VarImp
   ```

   The core type relation consults it only at the widening leaf:

   ```agda
   X⊑X : μ ⊢ ＇ X ⊑ ＇ X

   X⊑★ : μ X ≡ X⊑★
     → μ ⊢ ＇ X ⊑ ★
   ```

2. **The two direct store entries.**  For aligned endpoint variables
   `Xᴸ` and `Xᴿ`, `lookupStore` exposes one source representation and one
   target representation.  It does not follow a variable chain.

3. **Alignment.**  The two embeddings decide whether endpoint variables
   occupy the same shared center:

   ```agda
   CenterAligned W Xᴸ Xᴿ =
     toRenameᵗ (ηᴸʷ W) Xᴸ ≡ toRenameᵗ (ηᴿʷ W) Xᴿ
   ```

The landed companion connects the three through two mark-sensitive fields:

```agda
preciseMarksAligned :
  impEnvʷ W (center Xᴸ) ≡ X⊑X
  → Σ[ Xᴿ ∈ TyVar Δᴿ ] CenterAligned W Xᴸ Xᴿ

dynamicStarSourcesUnoccupied :
  impEnvʷ W (center Xᴸ) ≡ X⊑★
  → lookupStore (sourceStoreʷ W) Xᴸ ≡ ★
  → NoTargetOccupantAtSource W Xᴸ
```

The representation field is deliberately independent of the mark:

```agda
representationsImprecise :
  CenterAligned W Xᴸ Xᴿ
  → impEnvʷ W ⊢ embedᴸ (lookupStore sourceStore Xᴸ)
                  ⊑ embedᴿ (lookupStore targetStore Xᴿ)
```

Thus the current design gives the bit three jobs:

- **type capability:** may this variable occurrence widen to `★`?
- **allocation/occupancy phase:** is a direct source-`★` cell still open, or
  may it have a target occupant?
- **temporal proof state:** did a rule decay/honestify this center, and which
  origin world did a rebase come from?

Those jobs coincide in simple source-only and paired-bind worlds.  They do
not coincide in the YZ chain.

### 1.2 The YZ exception is the collision, not the cause

The complete live checkpoint-3/4 layout is:

```text
⟨X: Xᴸ↦ℕ    ⊑[X⊑★] ─
 │ Y: Yᴸ↦＇Zᴸ  ⊑[X⊑★] Yᴿ↦＇Zᴿ
 │ Z: Zᴸ↦★    ⊑[X⊑★] Zᴿ↦★⟩
```

The constructor data is, in full:

```agda
sourceStore =
  store-bind (store-bind (store-bind store-empty ★)
    (＇ Fin.zero)) (‵ `ℕ)

targetStore =
  store-bind (store-bind store-empty ★) (＇ Fin.zero)

ηᴸ = keep (keep (keep empty))
ηᴿ = skip (keep (keep empty))

μ X = X⊑★
μ Y = X⊑★
μ Z = X⊑★
```

The paired Y reveal follows the two direct variable entries and leaves the
term relation at `＇ Zᴸ ⊑ ＇ Zᴿ`.  The subsequent target-only Z reveal
uses `targetStore[Zᴿ] = ★` and requires:

```text
＇ Zᴸ ⊑ᵂ⟨W⟩ ★.
```

The live `X⊑★` rule obtains that leaf only from the mark at center Z.  It
does not inspect `sourceStore[Zᴸ] = ★`.  This leaf is used twice at
checkpoint 3 and once at checkpoints 8, 9, and 10, as audited in
`d16-5b-paired-seal-first-try.red`.

Invariant (5), however, reads the same local state in the other direction:

```text
mark Z = X⊑★  +  sourceStore[Zᴸ] = ★
  ==> no target occupant at Z.
```

The actual world has target occupant `Zᴿ`.  Changing Z to `X⊑X` satisfies
the occupancy reading but destroys the widening capability.  The rejected
narrow proposals tried to decide which reading wins.  The disease is that
one bit is being used for both readings.

### 1.3 The projection mismatch shows why the bit cannot simply favor YZ

The projection-mismatch calibration has the complete one-cell layout:

```text
⟨C: X↦★ ⊑[X⊑★] Y↦★⟩
```

Its stores are both `store-bind store-empty ★`; both embeddings are
`keep empty`; the environment is the constant `X⊑★` environment.  The bad
whole-term square is:

```text
source sealed/tagged/projected at X   ⊑   target ℕ-tag projected at Y
                  |                                  |
                  | returns                          | blame
                  v                                  v
             source value                          blame
```

This local cell has exactly the same source entry, target entry, alignment,
and live mark as the Z cell above.  The difference is term/cast ancestry and,
in the YZ world, the incoming paired alias chain through Y.  A local
two-entry classifier cannot distinguish them.  A whole-world classifier can
notice the incoming Y chain, but it still cannot reconstruct the static
binder choice in the general case; the next subsection checks that fact.

### 1.4 Checked answer: marks are independent information today

The new probe constructs these two worlds:

```text
precise-world = ⟨C: X↦ℕ ⊑[X⊑X] Y↦ℕ⟩
dynamic-world = ⟨C: X↦ℕ ⊑[X⊑★] Y↦ℕ⟩
```

Both have identity embeddings and the same source and target store
`store-bind store-empty ℕ`.  Both satisfy all four fields of the landed
`WorldInvariants` companion:

```agda
precise-world-invariants : WorldInvariants precise-world
dynamic-world-invariants : WorldInvariants dynamic-world
```

For the dynamic world, invariant (5)'s direct-source-`★` antecedent is
false.  The probe then refutes the strongest reconstruction principle that
identical valid layouts determine pointwise-equal environments:

```agda
valid-layouts-do-not-determine-marks :
  ValidLayoutsDetermineMarks → ⊥
```

This establishes two different conclusions:

- In the **current design**, `impEnv` is genuinely independent data.  It is
  not recoverable even from entries, alignment, and all landed invariants.
- A future design may **choose** a computed classification, but it will be a
  semantic policy change.  It will not be recovering information already
  present in the two stores and embeddings.

## 2. Complete builder and fixture audit

The audit distinguishes “chosen by the builder's history” from “uniquely
forced by the completed layout.”  Only the latter would support eliminating
`impEnv` without a semantic change.

### 2.1 Every live world builder

| Builder | How the output mark is obtained | Determined by output entries + alignment? |
| --- | --- | --- |
| Raw `CtxImp.world` | Takes an arbitrary `ImpEnv` as its third field. | **No by definition.** This is the independent-data surface. |
| `CompilePreservesImprecision2.initialWorld μ Σ`; duplicate `Occupancy.initialWorldᴼ`; `WorldInvariants.initialWorld μ` | Uses caller-supplied `μ`; the first two also accept an arbitrary common store, while the D16 version uses `emptyStore`. | **No.** Identity alignment and equal stores do not select a mark; the checked one-cell pair is the finite counterexample. |
| `Examples2.reflWorld Σ` | Chooses `idᵐ`, hence `X⊑X`, for every center. | **Policy-fixed, not layout-derived.** Replacing `idᵐ` by a dynamic environment on a non-`★` common entry can still satisfy all four invariants. |
| `CtxImp.liftWorldBoth v W` | Inserts caller-supplied `v`; both fresh store entries are structural self variables and the fresh endpoints are aligned. | **No.** `v = X⊑X` and `v = X⊑★` have the same output layout. `WorldInvariants.liftWorldBoth-invariants` accepts both. |
| `CtxImp.liftWorldLeft v W` | Inserts caller-supplied `v`; fresh source is unaligned and has a structural self entry. | **Raw: no. Valid companion: fresh mark forced dynamic.** `WorldInvariants.liftWorldLeft-invariants` requires `v ≡ X⊑★` because invariant (2) rejects a precise unaligned source. Old marks remain inherited, not recomputed. |
| `CtxImp.leftOnlyWorld v W A` | Inserts caller-supplied `v`; fresh source is unaligned and has direct entry `A`. | **Raw: no. Valid companion: fresh mark forced dynamic.** `leftOnlyWorld-invariants` has the same `v ≡ X⊑★` restriction, independently of `A`; old marks are inherited. |
| `CtxImp.rightOnlyWorld W B` | `instᵐ` inserts `X⊑★` at the fresh target-only center and shifts old marks. | **Chosen by the right-only allocation event.** It is not inferred from `B`; `B` may be `★`, an alias, or a generic type on the raw surface. |
| `CtxImp.bothBindWorld v W A B` | Inserts caller-supplied `v` at a fresh aligned pair. | **Raw: no.** The landed live invariant theorem specializes to `v ≡ X⊑X`, but the output layout alone does not make that choice for non-`★` entries. |
| `CenterRename.renameWorld π W` | Copies old marks through `renameEnv`; every center outside `π`'s image is filled with `X⊑★`. | **No.** The answer depends on old/fresh center provenance, not on final entries and alignment. |
| `WorldDecay.blendWorld W′ Wᵈ` | Keeps `W′`'s embeddings and stores, but takes each mark from `W′` unless it is precise, in which case it may take `Wᵈ`'s mark. | **Explicitly no.** A second world changes the marks while the output layout is fixed. |
| `WorldDecay.honestify W` | Preserves marks at target-occupied centers and changes unoccupied centers to `X⊑★`. | **Partly geometry-computed, partly inherited.** Aligned centers retain independent history. |
| `SealPeelToolkit.dynWorld W` | Replaces every mark by `X⊑★` and leaves both stores and embeddings unchanged. | **No.** `dynWorld-invariants` needs an extra no-forbidden-source premise precisely because the layout does not justify this blanket choice. |
| Generic `EnvDecay W Wᵈ` endpoints | `Wᵈ` is caller-supplied with identical embeddings/stores and a monotone environment. | **No.** Decay is the public relation witnessing allowed independent mark change. |
| `TargetBindLift.ΛLiftToBindFreshWorld v W` and `ΛLiftToBindFreshWorldᴸ v W` | Compose `instᵐ`, `extendᵐ v`, and another `instᵐ`; the target store is the `★`-then-`＇ zero` tower. | **No.** The middle `v` is an explicit history parameter; the other fresh marks encode target allocation steps. |
| `TargetBindLift.targetStoreAs W Σᴿ` | Copies embeddings and marks from `W` while replacing the target store. | **No, decisively.** The current target entries can change without changing any mark. Validity therefore needs separate representation/classification premises. |
| `TargetExtend.smartAliasInsertWorld`, `smartFreshInsertWorld`, and `insertRebaseWorld` | Rename marks from `Wᵐ` or `Wᵖ`, while mixing them with target embeddings/stores from another insertion world. | **No.** Their marks follow premise/rebase provenance. The final store pair is assembled from different inputs. |
| `Inversion.TargetStripProof.lowerLiftWorldLeft` | Drops the fresh center and copies the tail of `Wᴸ`'s environment. | **No.** This is inverse history reconstruction, not output-layout classification. |
| `Catchup.InstInversionLambdaProof.ΛPostMidWorld` and `ΛRouteOneMidWorldAt` | The former applies `instᵐ` three times; the latter copies the environment of `liftWorldLeft X⊑★ W₂` while rebuilding embeddings. | **No.** Both encode the selected allocation schedule explicitly. |

Records such as `TargetInsert`, `RebaseAt`, `ParkedWorld`, and
`ParkedEvolve` relate already constructed worlds.  They are not additional
world builders.  Their consumers may constrain marks, but they do not make
marks a function of entries and alignment.

### 2.2 Every live fixture family

This table covers direct named fixture worlds outside `proof/DGG/notes/` and
the three required note-level kill fixtures.  Builder-composed fixtures are
listed in the last row and inherit the builder verdict above.

| Fixture family and names | Mark data and layout fact | Audit verdict |
| --- | --- | --- |
| `Example12Worlds.example12-world-X/Y/Z` | One source `ℕ` cell is moved among target `X↦ℕ`, `Y↦＇Z`, and `Z↦★`; `example12-imp-env` is independently all `X⊑★`. | **Not determined.** The same environment is reused across three different alignments. D16 direct-entry invariants accept X and reject the skewed Y/Z layouts for store reasons, not because the environment was computed. |
| `example12-nat-chain-world-X/Y` | Target is `Y↦＇X, X↦ℕ`; source `ℕ` is aligned first with X, then Y; both marks are independently `X⊑X`. | **Not determined.** The mark environment is held fixed while alignment changes; the Y layout is rejected by the direct-entry invariant. |
| `example12-left-path-world-X/Y/Z` | Source is `X↦ℕ, Y↦＇Z, Z↦★`, target is one `★` cell moved X→Y→Z. X/Y use all dynamic marks; Z changes only center Z to `X⊑X`. | **Mixed policy.** The Z repair is forced by invariant (5), while X/Y retain dynamic capability needed by their direct/chain relations. It is a hand-selected global policy, not a uniform local classifier. |
| `Examples2.reflWorld`, `left-path-world₁/₂`, and `left-path-world₃/₄/₅` | The first three identity-style worlds choose `idᵐ`. The XZ checkpoints use `⟨X: Xᴸ↦ℕ ⊑[X⊑★] Xᴿ↦★ │ Y: Yᴸ↦＇Z ⊑[X⊑★] ─ │ Z: Zᴸ↦★ ⊑[X⊑X] Zᴿ↦★⟩`. | **Policy-fixed, not generally derived.** XZ's Z mark is the invariant-(5) repair; its X mark remains dynamic because `ℕ ⊑ ★`. |
| `Examples2.left-path-world₃-YZ/₄-YZ` | Exact YZ snapshot from Section 1.2; both worlds reuse the same stores and all-dynamic environment. | **Contradictory demands.** Z must be dynamic for the live relation and precise for invariant (5). This is the motivating exception. |
| `ExtraCastRight2Counterexample.pre-world`, `post-world`, and `dyn-premise-world` | The stores are fixed while the source pivot is displaced. `pre/post` reuse a precise mark; `post` is explicitly not `WFWorld`; `dyn-premise-world` changes only the mark to dynamic. | **Not determined.** This family is itself a mark-history counterexample and the reason for `ImpEnvMono`/honestify. |
| `SmartCommaWitness.base-world`, `d1-outer-smart-world`, `a3-d1-alias-world`, and `a3-d1-name-world` | Base is empty. The other worlds use the all-dynamic environment with target `β↦＇α, α↦★`; alias and name worlds place the fresh structural source at β and α respectively. | **Not determined.** The environment is fixed by the route. The alias world's direct entries contradict `representationsImprecise` even though its guard requires the dynamic mark. |
| `CenterCrossingProbe.W/W′/Wᵖ`, `ChainRideProbe.W₁/Wₗ/W₂`, `MovedLinkProbe.probe-W₁/W₄/W₅/W₆`, `TagBoundaryProbe.probe-W₁/W₄/W₅`, `SealPeelProbe.probe-W/W′/W₄/Wᵖ`, `StarRepChainProbe.W`, and `SourceStarProbe.W₀` | Each family declares stores and embeddings separately and then applies one all-`X⊑★` `probe-μ` to every placement. Most stores contain direct `★` or alias-to-`★` cells. | **Not determined.** Marks are held fixed while pivots move. Several positive raw fixtures are intentionally outside invariant (5); they remain relation probes until world validity becomes mandatory. |
| `TerminusRebuildProbe.InstanceA.W` and `InstanceB.W/Wᵖ` | Instance A is `⟨C: X↦∀X.X⇒X ⊑[X⊑★] Y↦★⟩`. Instance B has source `X↦★`, target `Y↦＇Y₂, Y₂↦★`, all dynamic, and moves X from Y to Y₂. | **Not determined.** D16 kills both Instance-B endpoints; D18 uses their two rebases as the checked obstruction to unrestricted functional origins. |
| Required D8a worlds | `W = ⟨F: ─ ⊑[X⊑★] Yf↦ℕ │ O: X↦ℕ ⊑[X⊑X] Yo↦ℕ⟩`; `Wᵖ = ⟨F: X↦ℕ ⊑[X⊑★] Yf↦ℕ │ O: ─ ⊑[X⊑X] Yo↦ℕ⟩`. | **History-selected and invalid.** Both are rejected by unmatched-target invariant (4), independently of marks. |
| Required T10 Probe-1 worlds | Same geometry/marks as D8a with every direct `ℕ` changed to `★`: `W = ⟨F: ─ ⊑[X⊑★] Yf↦★ │ O: X↦★ ⊑[X⊑X] Yo↦★⟩`; `Wᵖ = ⟨F: X↦★ ⊑[X⊑★] Yf↦★ │ O: ─ ⊑[X⊑X] Yo↦★⟩`. | **Mixed.** Invariant (4) accepts both; invariant (5) accepts W and rejects Wᵖ. The fresh/old allocation history, not entries alone, tells why the two centers have different marks. |
| Required projection mismatch | `⟨C: X↦★ ⊑[X⊑★] Y↦★⟩`, with the term square from Section 1.3. | **Invalid under (5), but locally indistinguishable from YZ's Z cell.** Term/cast ancestry is what distinguishes the executions. |
| Builder-composed operational fixtures in `Phase3DeepDives`, `LambdaImpProbe`, parked D4, and instantiation catch-up | Constructed only through `initialWorld`, paired `bothBindWorld X⊑X`, `leftOnlyWorld X⊑★`, right-only allocation, rename, and the Λ tower builders. | **They inherit builder history.** Their marks are not re-derived after construction. |

The audit answer is therefore unambiguous: marks are sometimes *constrained*
by entries and alignment, but they are not *determined* by them.  Invariant
(5) makes aligned direct `★/★` cells precise, while the YZ execution needs
one such cell to retain dynamic widening capability.  The missing discriminator
is history/provenance or a redesigned semantics, not another equation over the
existing two-point bit.

## 3. Full mark-system friction inventory

| ID | Open friction | What the mark is asked to mean | Store/alignment facts already present | Exact collision |
| --- | --- | --- | --- | --- |
| F1 | YZ paired-seal exception | `X⊑★` authorizes `＇Zᴸ ⊑ ★`. | Z is paired and both direct entries are `★`; Y provides an incoming aligned alias chain. | Invariant (5) interprets the same `X⊑★ + source ★` as necessarily unoccupied. |
| F2 | Smart-alias blocker | `SmartAliasMergeGuard.alias-mark-dynamic` and `transport⊑ᵂ` require the fresh source/target-β center to be `X⊑★`. | Fresh source direct entry is its structural self variable; target β directly points to α, and target α is `★`. | Direct `representationsImprecise` forces β = α, contradicting the two target entries. Changing the mark to precise breaks the guard before repairing the entries. |
| F3 | `liftWorldLeft` / `leftOnlyWorld` stage-1 restriction | Generic APIs accept `v`, but a fresh source-only `X⊑X` would claim precision without a target alignment. | Fresh source is visibly unoccupied; `store-lift` gives a self variable and `store-bind` gives A. | `preciseMarksAligned` forces the valid invariant theorems to require `v ≡ X⊑★`; raw APIs remain broader. |
| F4 | Decay and `ImpEnvMono` | A proof may weaken `X⊑X` to `X⊑★` while leaving embeddings and stores fixed. | Runtime layout is unchanged. | Validity is not monotone: decay can create the forbidden `X⊑★ + source ★ + occupied` combination. `WorldInvariants.decay-invariants` therefore needs a no-new-forbidden-cell premise. |
| F5 | `honestify`, `blendWorld`, and `dynWorld` | `honestify` dynamizes only unaligned centers; blend imports marks from a second world; `dynWorld` dynamizes all centers. | Each operation keeps the output runtime layout fixed (blend uses the first world's layout). | Mark transformation is history-sensitive. Honestify is valid, blend/decay need premises, and `dynWorld` needs a premise for every direct source `★`. |
| F6 | Invariant (5) itself | `X⊑★` at a direct source `★` is used as an “open source-only cell” certificate. | Occupancy is already directly decidable from embeddings; both entries are also available. | The condition is stronger than mark honesty: it kills the bad mismatch world, but also all good matched-seal uses inside the same aligned all-dynamic calibration and the live YZ Z cell. |
| F7 | D18 origin-policy mark coherence | Two rule-facing rebases with the same destination and pivots must have exactly the same origin, hence the same origin `impEnv`. Origin-to-destination marks may still decay. | D18's proposed `origin-determined : W ≡ originAt policy W′ X Y` pins the whole origin record. | Exact origin equality derives `origin-marks-unique`; equating origin and destination marks would be too strong. Any mark redesign must preserve this two-level distinction and commute with rename/decay/insertion. |

## 4. Structurally different directions

### Direction A: compute marks from layout and delete independent `impEnv`

Split the raw layout from its computed classification:

```agda
record WorldLayout (Δᴸ Δᴿ Δ : TyCtx) : Set where
  field
    ηᴸ : Δᴸ ↪ᵗ Δ
    ηᴿ : Δᴿ ↪ᵗ Δ
    sourceStore : TyStore Δᴸ
    targetStore : TyStore Δᴿ

classify : WorldLayout Δᴸ Δᴿ Δ → TyVar Δ → VarImp

record World (Δᴸ Δᴿ Δ : TyCtx) : Set where
  field
    layout : WorldLayout Δᴸ Δᴿ Δ

impEnvʷ W = classify (layout W)
```

A purely local `classify` has no satisfactory YZ choice.  Classifying aligned
`★/★` as precise preserves invariant (5) and rejects the mismatch world but
breaks YZ.  Classifying it dynamic restores YZ but admits the mismatch layout.
A whole-layout classifier could add an incoming-paired-alias condition:

```agda
classify L Z = X⊑★
  if source-only L Z
  or incoming-aligned-alias-to L Z
  else X⊑X
```

That distinguishes the concrete YZ and one-cell mismatch layouts.  It still
does not reconstruct the general binder choice: the checked `ℕ/ℕ` worlds and
`liftWorldBoth v` have identical layouts and valid inhabitants at both marks.
Adopting the classifier therefore removes one of those semantics.

Consequences:

- `ImpEnvMono`, `EnvDecay`, blend, honestify, and mark fields on guards become
  equations about `classify` under layout transformations.
- `liftWorld*`, bind worlds, rename, target insertion, and rebase must prove
  classifier stability instead of choosing marks.
- Static source imprecision that is not encoded in stores must either be
  discarded or moved into new provenance--which turns this into Direction D.

Kill checks:

- D8a remains rejected by unmatched non-`★`, non-variable target entries.
- T10 W/Wᵖ depends on the chosen global classifier; a local classifier cannot
  recover the intended fresh-versus-old distinction from the two `★` entries.
- ProjectionMismatch is unsafe if the classifier makes every aligned
  `★/★` cell dynamic.  Incoming-alias classification excludes the concrete
  one-cell probe but needs a new spoofing/laundering battery.

One-line verdict: **removes the independent bit and much transition plumbing,
but the checked independence probe proves this is a semantics choice, and a
layout-only policy has no uniform YZ/mismatch/binder answer.**

### Direction B: enrich the mark lattice

Separate an open dynamic cell from a paired cell whose representation is
dynamic:

```agda
data VarImp : Set where
  X⊑X       : VarImp
  X⊑★-open  : VarImp
  X⊑★-paired : VarImp

data CanWiden : VarImp → Set where
  open-widen   : CanWiden X⊑★-open
  paired-widen : CanWiden X⊑★-paired

X⊑★ : CanWiden (μ X) → μ ⊢ ＇ X ⊑ ★
```

The world conditions become:

```agda
openStarSourcesUnoccupied :
  μ (center Xᴸ) ≡ X⊑★-open
  → lookupStore sourceStore Xᴸ ≡ ★
  → NoTargetOccupantAtSource W Xᴸ

pairedDynamicRepresentations :
  μ (center Xᴸ) ≡ X⊑★-paired
  → Σ[ Xᴿ ∈ TyVar Δᴿ ]
      CenterAligned W Xᴸ Xᴿ
    × lookupStore sourceStore Xᴸ ≡ ★
    × lookupStore targetStore Xᴿ ≡ ★
```

YZ marks Z `X⊑★-paired`; source-only seal windows use `X⊑★-open`;
ordinary paired binders use `X⊑X`.

Consequences:

- All pattern matches on `VarImp`, `extendᵐ`, `instᵐ`, environment rename,
  decay, and mark guards gain a case.
- Decay is no longer a two-point order.  At minimum it needs
  `X⊑X -> X⊑★-open` and `X⊑X -> X⊑★-paired`, selected by world state.
- Smart alias remains blocked: its direct structural-source/alias-target
  mismatch is not repaired by naming the mark more accurately.
- D18 can still pin exact origin marks, but every policy naturality theorem
  must preserve the three-way classification.

Kill checks:

- D8a invariant (4) is unchanged.
- T10 Wᵖ must not acquire `X⊑★-paired` merely from alignment; its target-only
  occupant was not born as the source's partner.
- ProjectionMismatch also has aligned direct `★/★`.  If the new mark can be
  minted from those facts alone, it reopens the bad world.  Either the term
  partner premise must remain the soundness guard or the paired mark needs
  ancestry, converging on Direction D.

One-line verdict: **directly expresses the YZ state and resolves the literal
invariant-(5) contradiction, but it does not explain who may mint the third
point and leaves smart alias, decay selection, and provenance risk open.**

### Direction C: flatten representation chains at allocation time

Make runtime bind store the current terminal representative rather than the
syntax supplied by the reduction:

```agda
bindFlat : TyStore Δ → Ty Δ → TyStore (suc Δ)
bindFlat Σ A = store-bind Σ (resolveRep Σ A)

applyStore keep Σ = Σ
applyStore (bind A) Σ = bindFlat Σ A
```

The canonical resolver would have to move from `CtxImp` into the core store
layer.  Every world builder corresponding to `bind` must use `bindFlat`.

The YZ stores then become:

```text
⟨X: Xᴸ↦ℕ ⊑[X⊑★] ─
 │ Y: Yᴸ↦★ ⊑[X⊑X] Yᴿ↦★
 │ Z: Zᴸ↦★ ⊑[X⊑X] Zᴿ↦★⟩
```

The paired Y reveal reaches `★ ⊑ ★` directly.  There is no later
`＇Zᴸ ⊑ ★` leaf and no Y-to-Z chain.  Both paired direct-`★` centers may
remain precise.

This also makes the smart-alias target shape `β↦＇α, α↦★` unmintable:
β is stored as `★`.  The current smart-alias guard and branch disappear or are
replaced by a flat fresh bind.  That is a semantic simplification, not merely
a proof repair.

Consequences:

- `Reduction.applyStore`, preservation, `Eval`, conversion typing, all
  `store-bind` equality proofs, and all Example-12 chain fixtures change.
- Generated casts still mention the syntactic argument A.  Preservation must
  prove those casts well typed against the flattened store entry or regenerate
  them from `resolveRep Σ A`.
- Representation-chain theorems and the chain-permissive unmatched-target
  invariant become obsolete or collapse to one-step facts.
- Polymorphic generativity may depend on retaining name indirection; flattening
  must be checked against sealing/unsealing semantics, not just DGG proofs.

Kill checks:

- D8a's direct `ℕ` entries are already flat, so invariant (4) still kills it.
- T10 and ProjectionMismatch are already all-`★`/flat; their verdicts are
  unchanged.  Invariant (5) or term partner/provenance remains necessary.

One-line verdict: **removes the concrete YZ chain and the smart-alias store
shape at their source, at the cost of changing the operational representation
discipline and potentially the calculus's generative-name semantics.**

### Direction D: make pair provenance first-class and derive marks from it

Record how each center was born and which older cell an alias descends from:

```agda
data CellBirth (Δ : TyCtx) : Set where
  structural : CellBirth Δ
  paired-bind : CellBirth Δ
  source-bind : CellBirth Δ
  target-bind : CellBirth Δ
  alias-bind : TyVar Δ → CellBirth Δ

record CellHistory (W : World Δᴸ Δᴿ Δ) (Z : TyVar Δ) : Set where
  field
    birth : CellBirth Δ
    sourcePivot : Maybe (TyVar Δᴸ)
    targetPivot : Maybe (TyVar Δᴿ)
    partnerAncestor : Maybe (TyVar Δ)
    castAncestry : CastAncestry W Z
```

The production version should index constructors tightly enough that invalid
combinations are unconstructible; the loose record above only shows the data.
The world stores one history per center, and the current mark becomes a
projection:

```agda
impEnvʷ W Z = capabilityMark (historyʷ W Z)
```

For YZ, Z's history says it is a paired dynamic-representation ancestor of
the paired Y aliases.  It may widen while occupied.  ProjectionMismatch lacks
the incoming allocation/cast ancestry.  Smart alias can be admitted only if
the fresh source and target β share an ancestry path to α; otherwise the branch
is rejected for the real reason instead of a direct-entry accident.

This is the fresh-partner-ancestry direction anticipated by the D8a.4
discussion and the earlier S-PROV calibration.  The calibration's richer
version separates birth origin, use capability, occupancy/allocation
ancestry, and cast ancestry; its term-shaped projection checks block the bad
ProjectionMismatch square.

Consequences:

- Every allocating world builder mints a constructor; rename, target insert,
  rebase, bind lift, and parked evolution transport histories.
- Decay changes a current observation/capability state but cannot erase birth
  or cast ancestry.  Honestify becomes a derived view over history.
- The smart-alias guard is replaced by an ancestry-producing allocation rule,
  or the branch becomes uninhabited explicitly.
- D18's `originAt` can be keyed by the same event/partner ancestry.  Exact
  origin mark coherence follows because both marks are projections of the
  same selected origin history; origin-to-destination decay remains separate.

Kill checks:

- The checked S-PROV CORE calibration blocks ProjectionMismatch while keeping
  matching and residual controls.
- D8a's unmatched `ℕ` target has no legitimate paired ancestry and remains
  rejected; T10 Wᵖ's target-only cell was not born as X's partner and remains
  rejected.
- The risk is underspecifying or forgeably transporting ancestry.  Every
  rebase/shortcut producer needs a laundering check, especially the D18
  proof-local-chain split.

One-line verdict: **has enough information to distinguish all known cells and
can subsume marks, but it moves allocation and cast history through nearly the
entire DGG development.**

### Direction E: redesign `_⊑ᵂ⟨_⟩_` as a store-aware inductive relation

Replace the current abbreviation

```agda
A ⊑ᵂ⟨ W ⟩ B = impEnvʷ W ⊢ embedᴸ W A ⊑ embedᴿ W B
```

with a relation whose every constructor is world-indexed:

```agda
data _⊑ᵂ⟨_⟩_ : Ty Δᴸ → World Δᴸ Δᴿ Δ → Ty Δᴿ → Set where
  ★⊑★ : ★ ⊑ᵂ⟨ W ⟩ ★
  ι⊑ι : ‵ ι ⊑ᵂ⟨ W ⟩ ‵ ι

  var⊑var :
    CenterAligned W Xᴸ Xᴿ
    → ＇ Xᴸ ⊑ᵂ⟨ W ⟩ ＇ Xᴿ

  var⊑★-open :
    NoTargetOccupantAtSource W Xᴸ
    → lookupStore (sourceStoreʷ W) Xᴸ ≡ ★
    → ＇ Xᴸ ⊑ᵂ⟨ W ⟩ ★

  var⊑★-represented :
    DynamicRepresentation W Xᴸ
    → ＇ Xᴸ ⊑ᵂ⟨ W ⟩ ★

  ⇒⊑⇒ : A ⊑ᵂ⟨ W ⟩ A′ → B ⊑ᵂ⟨ W ⟩ B′
    → A ⇒ B ⊑ᵂ⟨ W ⟩ A′ ⇒ B′

  ∀⊑∀ : ...
```

Unlike the rejected narrow store-mediated leaf, this direction migrates the
whole relation: variable equality uses alignment directly, binder rules
choose their lifted world explicitly, and every rename/substitution/decay
theorem is proved by induction over world-aware evidence.

`DynamicRepresentation` may be only a resolved source-`★` fact, or a
stronger paired-chain witness.  The weak choice reconstructs YZ but also
reconstructs the one-cell mismatch type boundary; the existing term partner
discipline must then remain.  The strong choice needs ancestry and approaches
Direction D.

Consequences:

- Every `⊑ᵂ` constructor use, inversion, uniqueness proof, context entry,
  compile theorem, center rename, target extension, bind lift, and term rule
  index changes.
- `proof.Imprecision.occurs-not-star`, `source-path-same`, and `⊑-unique`
  require world/store-aware restatements; uniqueness may need proof
  irrelevance for representation evidence.
- YZ can keep Z precise in `impEnv` because the widening fact is carried by
  the witness.  That resolves the local invariant-(5) collision without
  eliminating all other mark uses.
- Smart alias remains blocked unless `DynamicRepresentation` also validates
  its structural-source/alias-target path and invariant (3) is redesigned.

Kill checks:

- Keeping invariants (3)--(5) leaves the D8a and T10 verdicts unchanged.
- ProjectionMismatch remains excluded only if the term partner premise stays,
  or if `DynamicRepresentation` contains the checked cast ancestry from
  S-PROV.

One-line verdict: **gives the type witness the store facts it actually uses
and restores YZ, but a ground-up migration is large and does not by itself
solve smart alias or term-level projection ancestry.**

### Direction F: compare terminal representations and remove variable marks

Normalize endpoint types through their own stores before comparing them:

```agda
normalizeᴸ : World Δᴸ Δᴿ Δ → Ty Δᴸ → Ty Δ
normalizeᴿ : World Δᴸ Δᴿ Δ → Ty Δᴿ → Ty Δ

A ⊑ʳ⟨ W ⟩ B =
  baseEnv ⊢ normalizeᴸ W A ⊑ normalizeᴿ W B
```

Here `normalize` recursively replaces a variable by `resolveVar` and embeds
the result.  If variable widening is entirely determined after resolution,
`VarImp` and `impEnv` can disappear.

YZ's Z normalizes to `★` on both sides, and its target-only reveal uses
`★ ⊑ ★`.  Smart alias's target β resolves through α to `★`; a dynamic
fresh source can also be interpreted through its runtime role, so the direct
head mismatch no longer blocks it.  Decay/honestify and D18 mark coherence
disappear as named problems.

Consequences:

- This changes what a type variable denotes in imprecision.  Distinct names
  with equal terminal representations become indistinguishable to the type
  relation.
- The current direct-entry invariant was introduced specifically to reject
  chain-depth skew hidden by terminal resolution.  That protection is lost or
  must be reintroduced as separate ancestry evidence.
- Universal binders, structural `store-lift` variables, opening, and
  substitution need a scope-correct normalization relation, not merely a
  function over closed stores.
- The term relation still needs name/tag/cast ancestry.  Terminal equality
  cannot justify a target projection bearing the wrong visible tag.

Kill checks:

- D8a remains rejected only if unmatched-target invariant (4) stays direct.
- Without a replacement occupancy/provenance invariant, T10 Wᵖ becomes hard
  to distinguish from a legitimate paired terminal-`★` world.
- ProjectionMismatch becomes easier to type because both variables resolve
  to `★`; the live partner discipline or Direction-D ancestry is mandatory.

One-line verdict: **removes nearly every mark-specific friction by quotienting
through runtime representation, but also removes distinctions that D16 and
the projection-mismatch discipline were built to protect.**

## 5. Cross-direction kill-check matrix

| Direction | YZ exception | Smart alias | D8a | T10 W / Wᵖ | ProjectionMismatch |
| --- | --- | --- | --- | --- | --- |
| A. Computed mark | Conditional: only a nonlocal classifier notices Y ancestry. | Direct entry contradiction remains. | Invariant (4) still rejects both. | Classifier must reconstruct allocation age; local entries cannot. | Aligned-`★/★` classifier is unsafe; incoming-alias variant needs new laundering checks. |
| B. Three-point lattice | Yes via `X⊑★-paired`. | No. | Unchanged rejection. | W stays; Wᵖ is unsafe if paired mark is forgeable from alignment. | Term partner or ancestry still required. |
| C. Flat allocation | Yes; problematic chain is not minted. | Current alias branch becomes unmintable. | Unchanged rejection. | Unchanged because stores are already flat. | Unchanged because its stores are already flat. |
| D. First-class provenance | Yes via paired ancestor capability. | Either justified by ancestry or explicitly rejected. | Rejected by missing legitimate target ancestry. | W retained; Wᵖ rejected as target-only, not born partner. | Checked S-PROV-style term ancestry blocks it. |
| E. Store-aware `⊑ᵂ` | Yes via represented-variable constructor. | Not without broadening representation invariants. | Unchanged if D16 invariants remain. | Unchanged if D16 invariants remain. | Existing term partner must remain, or witness gains cast ancestry. |
| F. Terminal quotient | Yes by normalization. | Direct mismatch dissolves. | Only direct invariant (4) preserves the kill. | Needs a new occupancy/history discriminator. | High risk: terminal equality erases the visible-name mismatch. |

## 6. Honest rankings

The friction count uses F1--F7 from Section 3.  “Dissolves” means the
friction ceases to be a separate proof obligation in the direction's stated
form; moving the same obligation into a stronger provenance predicate does not
count unless the direction provides that predicate.

### 6.1 Rank by number of mark frictions dissolved

| Rank | Direction | Definite frictions dissolved | Count | Frictions left or conditional |
| ---: | --- | --- | ---: | --- |
| 1= | D. First-class provenance | F1 YZ, F2 smart-alias explanation, F3 lift minting, F4 decay split, F5 honestify/blend, F6 invariant (5), F7 D18 mark source | 7 | Soundness depends on unforgeable ancestry and term-shaped cast provenance. |
| 1= | F. Terminal quotient | F1--F7 disappear as mark-specific obligations. | 7 | Occupancy, visible tag, and chain-skew obligations do not disappear semantically; they need replacement relations. |
| 3 | A. Computed mark | F3, F4, F5, F6, F7 become classifier equations. | 5 | F1 is conditional on a nonlocal policy; F2's direct entry mismatch remains. |
| 4 | C. Flat allocation | F1, F2's current store shape, and the YZ instance of F6. | 3 | Source-only lifts, decay/honestify, general occupancy, and D18 remain. |
| 5= | B. Three-point lattice | F1 and the YZ contradiction in F6. | 2 | F2--F5 and F7 remain, often with another mark case. |
| 5= | E. Store-aware `⊑ᵂ` | F1 and the YZ contradiction in F6. | 2 | Other world-mark mechanics remain unless this direction is combined with A or D. |

### 6.2 Rank by combined soundness and implementation risk

This is a low-to-high risk ordering, with engineering blast shown separately
so a semantically disciplined but large design is not conflated with a small
but unsound shortcut.

| Risk rank | Direction | Soundness risk | Engineering blast | Basis |
| ---: | --- | --- | --- | --- |
| 1 | B. Three-point lattice | **Medium.** Existing relation shape and term partner can remain; the main risk is forgeable paired marks. | **High.** Every mark/decay match gains a case. | Smallest semantic delta, but it names rather than proves provenance. |
| 2 | E. Store-aware `⊑ᵂ` | **Medium.** Keeping term partner and D16 invariants preserves known kills. | **Very high.** The public type-witness relation and all transports change. | The narrow local probe is checked; the full inductive migration is not. |
| 3 | D. First-class provenance | **Medium.** Rich ancestry has the strongest existing ProjectionMismatch checks, but transport can launder it if underspecified. | **Extreme.** World construction, allocation, casts, rebase, decay, and simulation all thread it. | S-PROV CORE provides positive evidence; D18 and every shortcut producer add obligations. |
| 4 | C. Flat allocation | **High.** May change generative sealing/name semantics and cast typing. | **Very high.** Core reduction/store action and all chain fixtures change. | Structural kills survive cheaply, but operational equivalence is unproved. |
| 5 | A. Computed mark | **High.** The checked probe proves layout is insufficient; any classifier discards a currently valid semantic distinction. | **Very high.** Every builder/transport proves classifier equations. | Concrete YZ/mismatch distinction requires an ad hoc global condition or hidden provenance. |
| 6 | F. Terminal quotient | **Very high.** It erases name and chain-depth distinctions used by current soundness checks. | **Extreme.** Core imprecision, binders, stores, invariants, and term proofs change. | Known mismatch types become easier to relate; replacement ancestry is mandatory. |

Neither table implies that the first row is preferable.  Direction D removes
the most frictions while carrying extreme implementation cost; Direction B
has the lowest combined risk while removing only two; Direction F scores high
on deletion precisely because it discards the most semantic structure.

## 7. Validation record

The new probe contains no postulates, holes, or option pragmas.  It was
spot-checked with Agda 2.8 using:

```text
agda --safe -v0 -i . -i proof/DGG/notes -i proof/DGG/notes/probes \
  proof/DGG/notes/probes/D16WideMarkIndependenceProbe.agda
```

The command exited 0.  It checks both complete `WorldInvariants` values and
the refutation of mark reconstruction from identical valid layouts.

Existing cheap kill evidence was reused rather than duplicated:

- `D16PairedSealRecalibrationProbe`: YZ forcing leaf, precise-Z emptiness,
  local store-aware reconstruction, and invariant-(5) checks;
- `T15WorldInvariantsDesignProbe`: D8a invariant-(4) rejections and T10
  invariant-(4) controls;
- `T15Invariant5ReconProbe`: ProjectionMismatch and T10-style occupied
  dynamic-source-`★` rejection;
- `ProjectionMismatchStarRepScratch` and the S-PROV probes cited by
  `CTI-TIGHTENING-CALIBRATION.md`: operational mismatch and ancestry controls;
- the D18 branch probe: exact origin, source-pivot and origin-mark equality,
  plus the Instance-B collision for unrestricted origins.

The final repository gate is recorded in the commit handoff after it exits
zero.
