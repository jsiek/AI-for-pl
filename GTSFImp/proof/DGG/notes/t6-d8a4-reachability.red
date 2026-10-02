T6 D8a4 compile reachability probe
===================================

Verdict
-------

**UNDECIDED.**  The existing LG-2 grounding/occupancy invariant does not
exclude the D8a3 configuration.  The standalone checked probe
`notes/probes/T6D8a4CompileReachabilityProbe.agda` proves that the exact
configuration satisfies the available occupancy facts.  No gradual source
pair plus compilation/reduction trace producing the exact configuration was
found, and the repository has no preservation theorem strong enough to rule
it out.

There is therefore no justified D8a5 groundedness premise to state.  Adding a
premise now would name a conjectural value-flow invariant rather than reuse a
theorem minted by `compile-preserves-imprecision²` and preserved by reduction.

The suspect configuration
-------------------------

Let `empty-μ` be the empty imprecision environment and let `store-empty` be
the empty type store.  The root world is built by one matched binder followed
by one target-only runtime allocation:

```agda
W₀       = CPI2.initialWorld empty-μ store-empty
W-paired = CTI2.bothBindWorld X⊑X W₀ ℕ₀ ℕ₀
W        = CTI2.rightOnlyWorld W-paired ℕ₁
```

Its stores and center environment are

```agda
source-store = store-bind store-empty ℕ₀
target-store = store-bind (store-bind store-empty ℕ₀) ℕ₁
μ            = instᵐ (extendᵐ X⊑X empty-μ)
```

Thus center `0` is marked `X⊑★`, center `1` is marked `X⊑X`, and the
root embeddings are

```text
ηᴸ(X)       = 1
ηᴿ(Y-fresh) = 0
ηᴿ(Y-old)   = 1.
```

The wrapper premise world `Wᵖ` has the same stores, target embedding, and
center environment, but rebases the source pivot:

```text
ηᴸᵖ(X)       = 0
ηᴿᵖ(Y-fresh) = 0
ηᴿᵖ(Y-old)   = 1.
```

The checked `forward-rebase : RebaseAt W Wᵖ X Y-fresh` supplies this move.
The target embedding is frozen, as required by `RebaseAt`.

The beta argument values are

```text
source-argument = (($ (κℕ 0) ↓ seal X ℕ) ⟨X!⟩)
target-argument = (($ (κℕ 0) ↓ seal Y-old ℕ) ⟨Y-old!⟩).
```

Both are closed with respect to term variables.  Their checked relation at
the root is

```agda
argument-is-entangled-at-old-pivot :
  W CTI2.∣ [] ⊢²
    source-argument ⊑ target-argument ∶ ★⊑★
```

The witness is entangled with the old pivot.  Its inner paired seals use
`conceal⊑conceal²`, `reversed-rebase : RebaseAt Wᵖ W X Y-old`, and the
root witness `＇ X ⊑ᵂ⟨ W ⟩ ＇ Y-old`.  The outer injection casts then
retarget the pair to `★⊑★`.  At `Wᵖ`, `X` instead shares center `0` with
`Y-fresh`, so the old endpoint witness is empty:

```agda
pivot-old-at-Wᵖ-empty :
  (＇ X) CTI2.⊑ᵂ⟨ Wᵖ ⟩ (＇ Y-old) → ⊥
```

The function body independently uses the beta variable below a source
wrapper.  In named notation its essential shape is

```text
source-body = (λz. x) ↑ (seal X ℕ ↦↑ id↑ ★)
target-body = λz. x.
```

The `reveal⊑²` derivation is stated at `W`, descends through
`forward-rebase` to `Wᵖ`, and reaches the occurrence `x⊑x²` there at
`★⊑★`.  `caller-configuration` checks the complete related application of
these functions to the entangled values.  The source application takes the
ordinary beta step.  Substitution would therefore need the same argument
pair related at the occurrence world `Wᵖ`; D8a3 proves that obligation
implies `⊥`.

What the grounding attempt proves
----------------------------------

`compile-preserves-imprecision²` mints the initial CTI2 relation at
`CPI2.initialWorld`.  `GroundingMint.CompileImageWorld` describes only the
worlds visited by its structural recursion: initial worlds, matched lifts,
and source-only lifts.  The probe checks

```agda
root-is-not-a-compile-recursion-world :
  Mint.CompileImageWorld W → ⊥

premise-is-not-a-compile-recursion-world :
  Mint.CompileImageWorld Wᵖ → ⊥
```

This is not an unreachability result.  `W` contains the target-only allocation
that happens after compilation, and it is a checked `ParkedWorld` via
`parked-right-bind (parked-both-bind parked-initial)`.

The LG-2 reduction facts positively admit the configuration:

- `rightOnly-new-target-occupiedᴼ` makes center `0` occupied by `Y-fresh`.
- `rightOnly-old-occupiedᴼ` preserves center `1`, occupied by `Y-old`.
- `rebase-occupied-forwardᴼ forward-rebase` preserves both occupied centers
  in `Wᵖ`, because rebasing freezes the target embedding.
- `occupied-see-through-empty` makes `NoTargetOccupantAtSource` impossible for
  `X` at both worlds.

The checked declarations `root-every-center-occupied` and
`premise-every-center-occupied` instantiate these facts for every center.
Most importantly,

```agda
occupancy-admits-refuting-configuration :
  (Occupied W (ηᴸ(X)) ×
    (W ∣ [] ⊢² source-argument ⊑ target-argument ∶ ★⊑★)) ×
  (Occupied Wᵖ (ηᴸᵖ(X)) ×
    (W ∣ root-source-ctx ⊢² source-body ⊑ target-body
       ∶ p-root-body))
```

is inhabited.  The argument derivation uses a matched non-star seal partner
and ordinary cast rules; it never asks for the occupancy-gated
`star-rep-target` see-through clause.  The body wrapper likewise does not use
that clause.  Consequently the S-OCC invariant has no contradiction to expose
on this state.

Why neither side is settled
---------------------------

`GroundingPreserve` proves useful local facts: beta-instantiation and
beta-generalization allocations immediately produce a fresh-name reveal
(optionally followed by a cast), and their fresh target center is occupied.
Those facts suggest the missing invariant: a fresh target allocation's
wrapper ancestry must remain coupled to every value that crosses the
generated function boundary until the matching fresh layers cancel.

That is a term-history/value-flow invariant, not the current occupancy
predicate.  The checked `grounding-preservation-knot` is a higher-order record
of conditional occupancy transport and one-step allocation facts.  It is not
an induction showing that all related reduction states preserve fresh-partner
ancestry.  `PLAN.md` records that its instantiation was deferred, and the LG-3
assembly notes still record it as an unassembled residual.

The known generated-name traces support the conjecture but do not prove it.
Example 12 reaches a tagged-sealed argument whose tag and seal both use the
fresh generated name.  The D8a3 counterconfiguration instead carries only the
stale `Y-old` tag/seal while its body descends through the `Y-fresh` rebase.
No checked source pair in the reachability catalog produces that combination.
Conversely, the catalog is a finite evaluator-backed screen, not a complete
inverse characterization of compiler outputs.

A proof of unreachability therefore still needs all of the following:

1. A predicate over related runtime configurations that records fresh target
   allocation ancestry and the values flowing through each generated
   conversion boundary.
2. A minting theorem connecting that predicate to
   `compile-preserves-imprecision²`.
3. Preservation through every related reduction/catch-up case, including
   wrapper distribution, cancellation, and beta closing.
4. An instantiation at `caller-configuration` yielding `⊥`.

Using the unfinished paired-function simulation to obtain item 3 would be
circular: that simulation is precisely waiting for the D8a substitution
closing result under investigation.

A proof of reachability instead needs closed gradual source terms, a source
imprecision derivation, the two ordinary `compile` outputs, and explicit
store-changing reductions whose related checkpoint is the exact stale-old
argument/fresh-body combination.  This probe found no such witness.

D8a5 consequence
-----------------

No groundedness premise is proposed.  The only available checked candidate,
occupancy/no-see-through, is satisfied by the bad configuration.  A
fresh-partner ancestry premise may eventually be appropriate, but its `Set`
declaration should be introduced only together with the minting and
preservation theorems above; otherwise it would be another ungrounded
companion predicate.
