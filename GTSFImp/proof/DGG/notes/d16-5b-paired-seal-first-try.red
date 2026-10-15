# D16 Stage 2: 5b paired-seal first-try exception and 5c recalibration

Date: 2026-08-19

## Decision status

The live YZ paired-seal derivations require a variable-to-dynamic type
judgment at the matched Z center.  With the live type-imprecision relation,
that judgment is derivable exactly when the Z center is marked `X⊑★`.
Changing only that mark to `X⊑X` therefore breaks four live whole-term
derivations.

There is nevertheless a real recalibration design available: make
variable-to-dynamic imprecision store-mediated.  At this fixture the source Z
cell directly contains `★`, so such a rule derives `＇ Zᴸ ⊑ ★` while the center
remains `X⊑X`; the recalibrated world then satisfies all four landed
`WorldInvariants` fields, including invariant (5).  This is a relation redesign,
not a fixture-only edit.  Its global proof cost and semantic admissibility have
not been established.

A seal-boundary mark-transition exception also reconstructs the local type
step, but its conclusion world restores `X⊑★` at an occupied source-`★` center.
That world is rejected by invariant (5), so this candidate does not solve 5c.
A raw rule allowing every `X⊑X` variable to relate to `★` is too broad and is
rejected below.

No live relation or proof module was changed.  The checked probe is
`proof/DGG/notes/probes/D16PairedSealRecalibrationProbe.agda`.

## Self-contained YZ paired-seal fixture

### Names and indices

The source has three cells and the target has two.  These are the variable
names used below:

| Side | Name | Agda index |
| --- | --- | --- |
| source | `Xᴸ` | `Fin.zero` |
| source | `Yᴸ` | `Fin.suc Fin.zero` |
| source | `Zᴸ` | `Fin.suc (Fin.suc Fin.zero)` |
| target | `Yᴿ` | `Fin.zero` |
| target | `Zᴿ` | `Fin.suc Fin.zero` |

The shared center also has three cells, named X, Y, and Z at `Fin.zero`,
`Fin.suc Fin.zero`, and `Fin.suc (Fin.suc Fin.zero)` respectively.

### Full stores

Here is the complete constructor data.  `Examples2` stores these behind
`store-after`; the four expansion equalities
`examples2-source-store₃-expanded`, `examples2-source-store₄-expanded`,
`examples2-target-store₃-expanded`, and
`examples2-target-store₄-expanded` are all checked by `refl`.

```agda
-- Source cells after lookup in the final three-cell scope:
--   Xᴸ = Fin.zero                         ↦ ‵ `ℕ
--   Yᴸ = Fin.suc Fin.zero               ↦ ＇ Zᴸ
--   Zᴸ = Fin.suc (Fin.suc Fin.zero)     ↦ ★
yz-source-store : TyStore 3
yz-source-store =
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) (‵ `ℕ)

-- Target cells after lookup in the final two-cell scope:
--   Yᴿ = Fin.zero                       ↦ ＇ Zᴿ
--   Zᴿ = Fin.suc Fin.zero               ↦ ★
yz-target-store : TyStore 2
yz-target-store = store-bind (store-bind store-empty ★) (＇ Fin.zero)
```

Thus the direct store data is:

```text
sourceStore[Xᴸ] = ‵ `ℕ       targetStore has no X cell
sourceStore[Yᴸ] = ＇ Zᴸ      targetStore[Yᴿ] = ＇ Zᴿ
sourceStore[Zᴸ] = ★          targetStore[Zᴿ] = ★
```

`left-path-world₃-YZ` uses `Ex.right-store₃` and
`left-path-target-store₃`; `left-path-world₄-YZ` uses the corresponding
stage-4 names.  Both pairs reduce definitionally to the two stores above.
The reduction from checkpoint 3 to checkpoint 4 changes the term, not either
store.

### Full embeddings

The source embedding is identity on the three centers.  The target embedding
skips the unmatched X center:

```agda
yz-source-η : 3 ↪ᵗ 3
yz-source-η = keep (keep (keep empty))

yz-target-η : 2 ↪ᵗ 3
yz-target-η = skip (keep (keep empty))
```

Consequently:

```text
toRenameᵗ yz-source-η Xᴸ = X
toRenameᵗ yz-source-η Yᴸ = Y
toRenameᵗ yz-source-η Zᴸ = Z

toRenameᵗ yz-target-η Yᴿ = Y
toRenameᵗ yz-target-η Zᴿ = Z
```

The live `Examples2` spelling is verbatim:

```agda
left-path-target-ηᴿ-YZ : 2 ↪ᵗ 3
left-path-target-ηᴿ-YZ = skip id↪ᵗ

left-path-world₃-YZ =
  world id↪ᵗ left-path-target-ηᴿ-YZ left-path-imp-env-YZ
    Ex.right-store₃ left-path-target-store₃

left-path-world₄-YZ =
  world id↪ᵗ left-path-target-ηᴿ-YZ left-path-imp-env-YZ
    Ex.right-store₄ left-path-target-store₄
```

### Full imprecision environment

The live environment is:

```agda
left-path-imp-env-YZ : ImpEnv 3
left-path-imp-env-YZ Fin.zero = X⊑★
left-path-imp-env-YZ (Fin.suc Fin.zero) = X⊑★
left-path-imp-env-YZ (Fin.suc (Fin.suc Fin.zero)) = X⊑★
```

The proposed recalibration changes only the last equation:

```agda
yz-precise-Z-env : ImpEnv 3
yz-precise-Z-env Fin.zero = X⊑★
yz-precise-Z-env (Fin.suc Fin.zero) = X⊑★
yz-precise-Z-env (Fin.suc (Fin.suc Fin.zero)) = X⊑X
```

Diagram:

    source store             shared center / mark              target store

    Xᴸ : ‵ `ℕ  ----------->  X : X⊑★

    Yᴸ : ＇ Zᴸ  ----------->  Y : X⊑★  <-----------  Yᴿ : ＇ Zᴿ
          |                                             |
          | direct alias                                | direct alias
          v                                             v
    Zᴸ : ★     ----------->  Z : X⊑★  <-----------  Zᴿ : ★
                                  |
                                  `-- 5c proposal: X⊑X

The Y and Z pairs are center-aligned.  X is source-only.  In particular, Z is
not an unmatched source cell: invariant (5) rejects the live Z data because it
combines source entry `★`, center mark `X⊑★`, and the aligned target occupant
`Zᴿ`.

## The forcing chain

The forcing point occurs once in `left-path-world₃-YZ` and is then reused at
three checkpoint families in `left-path-world₄-YZ`.  `Imprecision.X⊑X` is
unconditional, so the variable-to-variable steps below do not inspect the
center mark.  Only the variable-to-`★` step does.

### Checkpoint 3: paired Y reveal, then target-only Z reveal

The live type-imprecision chain is:

```text
＇ Yᴸ ⊑ᵂ⟨ left-path-world₃-YZ ⟩ ＇ Yᴿ
  left-path-Y-var⊑YZ₃

(＇ Yᴸ ⇒ ＇ Yᴸ)
  ⊑ᵂ⟨ left-path-world₃-YZ ⟩
(＇ Yᴿ ⇒ ＇ Yᴿ)
  left-path-Y⇒Y⊑Y⇒Y-YZ₃

(＇ Zᴸ ⇒ ＇ Zᴸ)
  ⊑ᵂ⟨ left-path-world₃-YZ ⟩
(＇ Zᴿ ⇒ ＇ Zᴿ)
  left-path-Z⇒Z⊑Z⇒Z-YZ₃
```

The second judgment is the lambda relation.  The paired Y reveal changes its
endpoint types from Y to the direct store entries Z, producing the third
judgment.  The target then reveals `Zᴿ`, whose store entry is `★`.  Its two
function components require two copies of:

```text
＇ Zᴸ ⊑ᵂ⟨ left-path-world₃-YZ ⟩ ★
  left-path-Z-var⊑★-YZ₃
```

Those two leaves feed:

```text
(＇ Zᴸ ⇒ ＇ Zᴸ)
  ⊑ᵂ⟨ left-path-world₃-YZ ⟩
(★ ⇒ ★)
  left-path-Z⇒Z⊑★⇒★-YZ₃
```

That final type judgment is the conclusion index supplied to
`CTI2.⊑reveal²` by `left-path-target-Z-revealed₃-YZ`.

### Checkpoint 8: paired Z seal, then target-only Z unseal

The stage-4 shared prelude is:

```text
＇ Yᴸ ⊑ᵂ⟨ left-path-world₄-YZ ⟩ ＇ Yᴿ
  left-path-Y-var⊑YZ₄

＇ Zᴸ ⊑ᵂ⟨ left-path-world₄-YZ ⟩ ＇ Zᴿ
  left-path-Z-var⊑YZ₄

(＇ Zᴸ ⇒ ＇ Zᴸ)
  ⊑ᵂ⟨ left-path-world₄-YZ ⟩
(＇ Zᴿ ⇒ ＇ Zᴿ)
  left-path-Z⇒Z⊑Z⇒Z-YZ₄
```

The paired Z seals in `left-path-argument-Z₈-YZ` retain

```text
＇ Zᴸ ⊑ᵂ⟨ left-path-world₄-YZ ⟩ ＇ Zᴿ.
```

Application with `left-path-Y-revealed₄-YZ` makes
`left-path-application₈-YZ`, also indexed by

```text
＇ Zᴸ ⊑ᵂ⟨ left-path-world₄-YZ ⟩ ＇ Zᴿ.
```

The target-only Z unseal then requires:

```text
＇ Zᴸ ⊑ᵂ⟨ left-path-world₄-YZ ⟩ ★
  left-path-Z-var⊑★-YZ₄
```

That is the conclusion index of `left-path-target-Z-revealed₈-YZ`.

### Checkpoint 9: paired Y seal/unseal, then target-only Z unseal

Starting from `left-path-argument-Z₈-YZ`, paired Y seals produce:

```text
＇ Yᴸ ⊑ᵂ⟨ left-path-world₄-YZ ⟩ ＇ Yᴿ
  left-path-argument-Y₉-YZ
```

Application retains the same judgment:

```text
＇ Yᴸ ⊑ᵂ⟨ left-path-world₄-YZ ⟩ ＇ Yᴿ
  left-path-application₉-YZ
```

The paired Y unseals return to the direct Y-store entries:

```text
＇ Zᴸ ⊑ᵂ⟨ left-path-world₄-YZ ⟩ ＇ Zᴿ
  left-path-Y-unsealed₉-YZ
```

The target-only Z unseal again requires:

```text
＇ Zᴸ ⊑ᵂ⟨ left-path-world₄-YZ ⟩ ★
  left-path-Z-var⊑★-YZ₄
```

That is the conclusion index of `left-path-target-Z-unsealed₉-YZ`.

### Checkpoint 10: value-side paired Y unseal, then target-only Z unseal

The value-side branch reuses the same paired-seal chain:

```text
＇ Zᴸ ⊑ᵂ⟨ left-path-world₄-YZ ⟩ ＇ Zᴿ
  left-path-argument-Z₈-YZ

＇ Yᴸ ⊑ᵂ⟨ left-path-world₄-YZ ⟩ ＇ Yᴿ
  left-path-argument-Y₉-YZ

＇ Zᴸ ⊑ᵂ⟨ left-path-world₄-YZ ⟩ ＇ Zᴿ
  left-path-Y-unsealed₁₀-YZ

＇ Zᴸ ⊑ᵂ⟨ left-path-world₄-YZ ⟩ ★
  left-path-Z-var⊑★-YZ₄
```

The last judgment is the conclusion index of
`left-path-target-Z-unsealed₁₀-YZ`.

### Exact rule and exact failure

Both live leaf proofs are applications of the same rule:

```agda
X⊑★ : ∀ {X}
  → μ X ≡ X⊑★
  → μ ⊢ ＇ X ⊑ ★
```

At Z, its only premise is:

```text
left-path-imp-env-YZ (Fin.suc (Fin.suc Fin.zero)) ≡ X⊑★.
```

Under the proposed edit this normalizes to `X⊑X ≡ X⊑★`.  This is the first
and precise failure.  The earlier `＇ Yᴸ ⊑ ＇ Yᴿ`, `＇ Zᴸ ⊑ ＇ Zᴿ`, paired-seal,
and paired-Y-unseal judgments remain inhabited.

The probe records the failure as checked emptiness, both at the leaf and at
the function judgment:

```agda
yz-Z-to-star-precise-empty :
  (＇ (Fin.suc (Fin.suc Fin.zero)))
    CTX.⊑ᵂ⟨ yz-precise-Z-world ⟩ ★
  → ⊥
yz-Z-to-star-precise-empty (I.X⊑★ ())

yz-Z-function-to-star-precise-empty
    (I.⇒⊑⇒ Z-domain-to-star Z-codomain-to-star) =
  yz-Z-to-star-precise-empty Z-domain-to-star
```

The empty pattern is Agda's checked rejection of the impossible constructor
premise `X⊑X ≡ X⊑★`.  A direct attempted live proof reports the same mismatch
as `X⊑X != X⊑★`.

## Recalibration candidates

### Candidate A: store-mediated `X⊑X` variable-to-`★`

Draft the new world-indexed clause verbatim as:

```agda
X⊑★-store : ∀ {W : CTX.World Δᴸ Δᴿ Δ} {Xᴸ : TyVar Δᴸ}
  → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑X
  → lookupStore (CTX.sourceStoreʷ W) Xᴸ ≡ ★
  → (＇ Xᴸ) ⊑ˢ⟨ W ⟩ ★
```

The probe's `_⊑ˢ⟨_⟩_` is a note-local draft relation.  It also contains the
ordinary live judgments and structural function closure:

```agda
live : A CTX.⊑ᵂ⟨ W ⟩ B → A ⊑ˢ⟨ W ⟩ B

⇒⊑⇒-store :
  A ⊑ˢ⟨ W ⟩ A′
  → B ⊑ˢ⟨ W ⟩ B′
  → (A ⇒ B) ⊑ˢ⟨ W ⟩ (A′ ⇒ B′)
```

At the fixture, both premises of `X⊑★-store` are `refl`: Z's center mark is
`X⊑X` and `sourceStore[Zᴸ] = ★`.  The checked witnesses are
`yz-Z-to-star-store-mediated` and
`yz-Z-function-to-star-store-mediated`.  This reconstructs every missing
type index identified above: checkpoint 3 uses the function closure; checkpoints
8, 9, and 10 use the leaf.

Consequences: implementing this candidate cannot be a new constructor of the
current store-free `Imprecision._⊢_⊑_`, because that relation has no store or
embedding parameters.  Either `_⊑ᵂ⟨_⟩_` must become an inductive enriched
relation or the core relation must acquire explicit representation evidence.
`CastTermImprecision` and all type-indexed term rules would then migrate to the
enriched relation.  Existing inversion arguments that use “an `X⊑X` occurrence
cannot widen to `★`” must be restated with store evidence; the immediate sites
include `proof.Imprecision.occurs-not-star`, `source-path-same`, `⊑-unique`,
and downstream uses of uniqueness in simulation, transport, center rename,
target extension, and target bind lift.  The fixture probe establishes local
sufficiency, not global soundness or preservation.

The D8a/T10 invariant-(4) kill-checks survive unchanged: this candidate does
not alter embeddings, stores, or invariant (4).  Both D8a endpoints are still
rejected for their unmatched non-`★`, non-variable target entries, while both
T10 Probe 1 endpoints still pass invariant (4) because those entries are `★`.

Invariant (5) does cover the recalibrated YZ family.  The probe constructs the
complete value

```text
yz-precise-Z-world-invariants :
  WI.WorldInvariants yz-precise-Z-world
```

The Z case of invariant (5) is vacuous because its mark is `X⊑X`; the X and Y
cases cannot have both a dynamic mark and direct source entry `★`.  Invariants
(2)--(4) also hold: precise Z has aligned target `Zᴿ`, the aligned direct Z
entries are `★ ⊑ ★`, and both target cells are aligned.

Verdict: **fixture-sufficient and compatible with invariant (5), but a global
relation redesign whose metatheory is still open.**

### Candidate B: target-unseal mark-transition exception

The current `ImpEnvMono W Wᵖ` requires every `X⊑★` mark in the conclusion
world `W` to remain `X⊑★` in the premise world `Wᵖ`.  A target-unseal
exception could instead permit the target pivot alone to have been `X⊑X` in
the premise.  The checked draft is verbatim:

```agda
RevealMarkTransition W Wᵖ Xᴿ = ∀ Z
  → CTX.impEnvʷ W Z ≡ X⊑★
  → CTX.impEnvʷ Wᵖ Z ≡ X⊑★
    ⊎ (Z ≡ toRenameᵗ (CTX.ηᴿʷ W) Xᴿ
      × CTX.impEnvʷ Wᵖ Z ≡ X⊑X)
```

The corresponding rule delta would be:

```agda
⊑reveal²-boundary :
  RevealMarkTransition W Wᵖ Xᴿ
  → RebaseAtᴿ W Wᵖ (just Xᴿ)
  → SameCtx γ γᵖ
  → targetStoreʷ W ⊢↑[ just Xᴿ ] c′
  → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → W ∣ γ ⊢² M ⊑ M′ ↑ c′ ∶ q
```

At the fixture, take `Wᵖ = yz-precise-Z-world` and
`W = yz-dynamic-world`.  The X and Y marks pass through unchanged, while Z
uses the exception.  `yz-target-Z-unseal-transition` checks this exact
transition.  The premise has `＇ Zᴸ ⊑ ＇ Zᴿ` under `X⊑X`; the conclusion has
the live `＇ Zᴸ ⊑ ★` under `X⊑★`.

Consequences: this needs either a specialized target-unseal constructor or a
new pivot-indexed alternative to `ImpEnvMono`.  Every proof that transports,
decays, or inverts target reveal steps must handle the exceptional pivot; a
global replacement would touch the target-reveal callers and mark-transport
layers in `CastTermImprecision`, `TermImpDecay`, `TargetExtend`,
`CenterRename`, and the term-imprecision transport proofs.  A specialized
constructor limits the syntactic edit but does not remove the invariant
problem.

The conclusion world is checkably illegal under invariant (5):

```agda
yz-dynamic-world-rejects-invariant5 :
  WI.WorldInvariants yz-dynamic-world → ⊥
```

Its witness selects source `Zᴸ`, target `Zᴿ`, direct entry `★`, dynamic mark
`X⊑★`, and their center equality.  Therefore invariant (5) cannot cover the
whole YZ derivation if this transition is used.  The D8a/T10 invariant-(4)
classifications are textually unchanged, but their force would be undermined
if term rules were allowed to cross through endpoints lacking
`WorldInvariants`; requiring valid endpoints preserves the kill-checks and
simultaneously makes this fixture transition unavailable.

Verdict: **locally inhabited, but not a 5c solution because its needed
conclusion world violates invariant (5).**

### Candidate C: reinterpret every `X⊑X` variable as dynamic

The smallest core-relation edit would be:

```agda
X⊑★-precise : ∀ {X}
  → μ X ≡ X⊑X
  → μ ⊢ ＇ X ⊑ ★
```

The probe models that clause verbatim at world level as:

```agda
X⊑★-raw :
  CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑X
  → (＇ Xᴸ) ⊑ʳ⟨ W ⟩ ★
```

This reconstructs the missing YZ leaf, but it ignores the reason Z can be
viewed dynamically.  `raw-rule-ignores-nondynamic-store` checks a one-cell
identity world whose source entry is `ℕ` and whose mark is `X⊑X`; the raw rule
still derives `＇ zero ⊑ ★`.  The same problem appears at precise polymorphic
binders created by `liftWorldBoth X⊑X`.

Consequences: `proof.Imprecision.occurs-not-star` and `source-path-same` become
false as stated, not merely incomplete by a new constructor case.  Proofs
using `X⊑X` as the certificate that a variable occurrence retains its endpoint
spine lose their premise.  The D8a/T10 structural invariant-(4) verdicts remain
unchanged, and the recalibrated YZ world still satisfies invariant (5), but
that is not a safety argument: invariant (5) is deliberately silent at
`X⊑X`, so it cannot constrain this newly broad rule.

Verdict: **checkably overbroad and rejected.**

## Comparative result

| Candidate | Restores all four missing YZ type indices at Z=`X⊑X`? | Complete recalibrated YZ `WorldInvariants`? | D8a/T10 invariant-(4) kill-check | Result |
| --- | --- | --- | --- | --- |
| A. Store-mediated variable rule | Yes, checked at the leaf and function levels. | Yes, checked. | Unchanged. | Viable design investigation; global proof cost open. |
| B. Target-unseal mark transition | Locally, by using an `X⊑★` conclusion world. | No; that conclusion world is rejected by (5). | Preserved only if all rule endpoints must be valid. | Not a 5c solution. |
| C. Raw `X⊑X`-to-`★` rule | Yes. | The fixture world passes, but (5) is blind to the overbroad rule. | Structurally unchanged. | Rejected. |

## Validation record

The new probe contains no postulates, holes, or option pragmas.  It was
spot-checked with Agda 2.8 using:

```text
agda --safe -v0 -i . -i proof/DGG/notes -i proof/DGG/notes/probes \
  proof/DGG/notes/probes/D16PairedSealRecalibrationProbe.agda
```

The command exited 0.  Its checked facts cover the expanded stores, original
dynamic derivability, `X⊑X` emptiness, candidates A--C, the complete
recalibrated world invariant, and the invariant-(5) rejection of candidate
B's dynamic conclusion world.

The unchanged D8a/T10 invariant-(4) results remain checked in
`T15WorldInvariantsDesignProbe.agda`: `d8a-W-violates-invariant4` and
`d8a-Wᵖ-violates-invariant4` reject D8a; `t10-W`, `t10-Wᵖ`, and
`t10-probe1-worlds-satisfy` retain the T10 representation result.

The required final repository gate was:

```text
PATH=.../scratchpad/agda28/bin:$PATH make check
```

It exited 0.

## Sharpened 5c decision menu

1. **5c-E: keep the checked exception.**  Keep `X⊑★` in the four live YZ
   derivation worlds, leave them outside `WorldInvariants`, keep the XZ worlds
   recalibrated to `X⊑X`, and make no relation change.  Choose this if 5c is a
   world-classification step rather than a demand that every legacy fixture be
   admitted.

2. **5c-S: open a store-mediated relation redesign.**  Adopt candidate A as
   the intended direction, keep Z at `X⊑X`, and require an implementation arc
   to migrate the world-indexed type relation and reprove inversion,
   uniqueness, transport, and simulation before landing it.  This is the only
   checked candidate that both reconstructs the YZ forcing chain and admits
   the fixture under invariant (5).

3. **5c-B: allow boundary-local dynamization.**  Adopt candidate B and accept
   that at least the target-Z-unseal conclusion world lies outside invariant
   (5).  This does not achieve full world-invariant coverage and is therefore
   strictly weaker than 5c-S while adding a new mark-transition case.

4. **5c-R: reinterpret `X⊑X` globally.**  Adopt candidate C.  Do not choose
   this: the checked non-dynamic-store witness shows that it erases the
   semantic distinction carried by `X⊑X`.
