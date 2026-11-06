T6 D8a3 occurrence-harvested feasibility
==========================================

Scope
-----

The checked module
`proof/DGG/notes/probes/T6D8a3OccurrenceFeasibilityProbe.agda` extends
the exact moving-pivot worlds and entangled tagged-sealed beta argument from
the D8a2 caller probe.  It performs calibration only: there is no
substitution induction.

Checked instance
----------------

At the root world `W`, the beta-bound context entry is
`ctx-imp ★ ★ ★⊑★`.  The source body places the free beta variable
below a
pivoted source reveal by first building the inner function pair

```
λz : ＇ X. x  ⊑  λz : ★. x
```

at the premise world `Wᵖ`.  The inner binder uses `p-pivot-star :
＇ X ⊑ᵂ⟨ Wᵖ ⟩ ★`; the free variable use is checked by
`use-relation` at

```
p-use : ★ ⊑ᵂ⟨ Wᵖ ⟩ ★
p-use = ★⊑★.
```

The source reveal is `seal X (‵ ℕ) ↦↑ id↑ ★`.  Thus `body-at-root`
rebuilds the body relation
at `W`, and `application-at-root` applies the resulting function relation to
the same `source-argument` and `target-argument` used by
`T6D8a2CallerSupplyProbe`.  This checks that the occurrence is part of an
actual caller configuration, not merely an independently reachable boundary.

Option 1: occurrence harvesting -- REFUTED
------------------------------------------

The configuration exists.  In particular, `SameCtx` preserves the
`★`/`★` entry into `Wᵖ`, even though the wrapper pivot occurs in the
type of
the enclosing inner function.  Consequently the occurrence-harvested
environment really must provide the entry

```agda
Wᵖ ∣ [] ⊢²
  singleSub source-argument 0 ⊑
  singleSub target-argument 0 ∶ p-use
```

for this derivation.  `harvested-obligation-empty` proves this type implies
`⊥`.  Occurrence harvesting avoids irrelevant reachable nodes, but this node
is relevant: the derivation actually reaches `x⊑x²` there.  Therefore the
redirect is refuted on the checked caller instance.

Option 2: substitute then rewrap -- REFUTED
-------------------------------------------

Substitution does not move the use back to `W`.  The checked definitional
equalities `source-substitution-shape` and `target-substitution-shape` show
that substitution produces `(λz. source-argument) ↑ source-wrapper` on the
left and `λz. target-argument` on the right.  Peeling that source wrapper
still demands the two-sided relation at `Wᵖ`, not at the caller's root world
`W`.  The exact peeled obligation is refuted by
`peeled-substituted-premise-empty`, which reduces it to the same impossible
argument relation at `p-use`.  Thus changing the order of substitution and
wrapper replay does not recover the root-world caller evidence on this
instance.

Calibration verdict
-------------------

Both redirects are `REFUTED` by
`T6D8a3OccurrenceFeasibilityProbe.agda`.  The earlier blanket boundary
environment was stronger than necessary, but its failing `Wᵖ` lookup is also
a genuine variable occurrence in a concrete body.  Any viable repair needs
evidence other than reuse of the root argument relation at this wrapper
premise.
