# Alignment-only source allocation: evolution impact audit

This note records the stage-2 change needed after the role-tagged source-rebase
world is green.  It is an impact audit, not a compatibility design.  The live
term-imprecision relation is unchanged.

## Exact one-step evolution

The trusted target-identity reduction allocates one source store entry and, in
the same simulation checkpoint, aligns that new source pivot with one existing
target pivot.  Against the role API in `World`, the direct constructor is:

```agda
  evolution-bind-left-aligned : ∀
      {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴸ⁺ : TermCtx (suc Δᴸ)} {A : Ty Δᴸ}
      {γ : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {Xᴿ : TyVar Δᴿ}
    → (eqᴸ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
    → (update : PivotUpdateᵗ
        (ηᴸᶜ (γ ▻ᶜ bind-left-changeᶜ A eqᴸ)) Fin.zero
        (toRenameⁱ
          (ηᴿᶜ (γ ▻ᶜ bind-left-changeᶜ A eqᴸ)) Xᴿ))
    → (boundary : AlignmentBoundaryᶜ
        (γ ▻ᶜ bind-left-changeᶜ A eqᴸ)
        Fin.zero Xᴿ update)
    → (represented :
        (＇ Fin.zero) ⊑ᵀ⟨ γ ▻ᶜ bind-left-changeᶜ A eqᴸ ⟩
          lookupStore Σᴿ Xᴿ)
    → WorldEvolution
        {W = γ}
        {W′ =
          (γ ▻ᶜ bind-left-changeᶜ A eqᴸ) ▻ᶜ
            rebase-source-changeᶜ Fin.zero Xᴿ update
              (alignment-onlyᶜ boundary) represented}
        (bind-ctx eqᴸ) keep-ctx
```

The conversion evidence stays inside `AlignmentBoundaryᶜ`; the evolution
constructor should not repeat the reveal/conceal fields.  No list of aligned
rebases is justified.  One source allocation creates one fresh source pivot,
and injection permits it to occupy only one target center.  The trusted
checkpoint-3 reduction uses exactly one such node for alpha.  Beta remains one
open frame in the nested CTI world.  Repeated runtime allocations can use
repeated one-step evolutions.

This result is not derivable from the existing constructors.  The ordinary
left-bind evolution stops at `γ ▻ᶜ bind-left-changeᶜ A eqᴸ`.
`evolution-keep` cannot append the same-endpoint history node because its result
world is definitionally its input world.  Encoding the alignment as a second
multi-evolution step would also invent a `keep` store change not present in the
runtime reduction.

## One-step projections

Add aligned clauses to these sound projections in `WorldEvolution.agda`:

- `evolution-⊑ᵀ`
- `evolution-source-represented`
- `evolution-aligned`
- `evolution-source-mark`
- `evolution-source-disaligned`

They all use that the new update is at source pivot `zero`, whereas every
pre-step source variable is transported to `suc X`.  The common equation is

```agda
off-pivot-fixedᵗ update (Fin.suc X) (λ ())
```

For `evolution-⊑ᵀ`, use `renameᵗ-comp` and `renameᵗ-cong` once to show
that renaming a shifted type through the post-update injection agrees with
renaming it through the ordinary left-bind injection.  The remaining clauses
only need the point equation above and the facts that the target injection and
marks do not change.

Do not add an aligned clause to `evolution-can-rebase-source`.  Its current
statement transports an arbitrary *potential* pivot update.  The fresh zero
may take exactly that potential update's target center, so the post-step
repointing need not be injective.  The theorem has no live callers and should
be deleted from the closed-world API.

## Open frames versus geometric rebase history

An alignment-only node still increments the geometric
`sourceRebaseCountᶜ`.  Consequently these current theorems are false for the
new evolution:

```agda
multi-sourceRebaseCount
multi-no-source-rebase
```

Do not redefine the geometric count: `DirectWorldInvariantsᶜ` deliberately
uses it, and the trusted checkpoint-3 aligned world does not satisfy those
direct invariants.  Instead expose the role-derived open-frame list and prove
the natural evolution law

```agda
openFramesᶜ γ′ ≡
  renameOpenFramesᶜ (applyVars χsᴸ) (applyVars χsᴿ)
    (openFramesᶜ γ)
```

for multi-evolution, with a direct empty-list corollary for simulation.  The
aligned constructor contributes no new frame; its ordinary left allocation
only renames existing frames by `suc` on the source and identity on the target.
All simulation and catchup premises currently using
`sourceRebaseCountᶜ γ ≡ 0` to mean "no open frame" must migrate to this
role-derived fact.  The stronger count premise in `WorldInvariants.agda` must
remain unchanged.

## Exhaustive constructor ripple

### `WorldEvolutionProducer.agda`

Add `evolution-request-left-aligned` with the same semantic fields, then add
its clause to every exhaustive request projection:

- `evolutionSourceStoreValue`
- `evolutionSourceTermCtxValue`
- `evolutionTargetStoreValue`
- `evolutionTargetTermCtxValue`
- `evolutionSourceTerm`
- `evolutionTargetTerm`
- `evolutionWorld`
- `evolutionSourceStore`
- `evolutionTargetStore`
- `evolutionSourceTerm-agrees`
- `evolutionTargetTerm-agrees`
- `evolutionSourceTermCtx`
- `evolutionTargetTermCtx`
- `evolutionSourceChange`
- `evolutionTargetChange`
- `produceWorldEvolution`

All endpoint projections agree with the ordinary left request.  Only
`evolutionWorld` and `produceWorldEvolution` expose the appended alignment-only
node.

### `WorldEvolutionSequence.agda`

`MultiWorldEvolution` itself needs no new constructor.  The existing
`evolutions-step-left` embeds the new one-step evolution with the real
`bind A` store change.  Update:

- replace the false geometric-count preservation facts with the open-frame
  transport and empty-frame corollary described above;
- add the aligned request cases to `request-source-change`,
  `request-target-change`, and `prepend-left-request`.

The generic multi type/alignment/mark/disalignment, store, context, conversion,
and term projections recurse through one-step projections and need no new
outer cases.

### CTI transport

State a sibling `TransportAlignedSourceBindᵀ` in
`TransportTermImprecisionStepDef.agda`.  Its conclusion uses
`evolution-⊑ᵀ (evolution-bind-left-aligned ...)` and the exact aligned result
world above.  Implement it by extending the genuine `SourceBindScope`
induction with a `source-scope-root-aligned` case.  That case supplies clauses
for:

- `source-scope-center`
- `source-scope-left-commutes`
- `source-scope-right-commutes`
- `source-scope-mark`
- `source-scope-context`
- `source-scope-store`

The generic source/target type and CTI transport lemmas then reuse those
equations.  `TransportSourceBindProof.agda` can export both the ordinary and
aligned source-bind proofs from its existing parameterized module; no new
classifier or result wrapper is needed.

Thread the sibling interface through
`TransportTermImprecisionStepProof.agda` and
`TransportTermImprecisionProof.agda`, adding the one exhaustive evolution
case.  Replace their geometric zero premise/propagation with the open-frame
empty fact.  The aligned step preserves emptiness even though it does not
preserve geometric zero.

### Transitional source-rebase stack

`SourceRebaseStackDef.agda` currently treats geometric zero as an empty stack
and has only shape-preserving bind evolutions.  Both assumptions are invalid
for the trusted allocation: alpha becomes alignment-only while the newer beta
remains open, so this is a non-top frame discharge.  Do not add a superficial
`stack-evolution-bind-left-aligned` that merely shifts the old stack.  Migrate
the root/stack facts to the role-derived `openFramesᶜ` view, or isolate the
actual selected-frame removal as its own semantic induction.  The corresponding
consumers are:

- `TransportSourceRebaseStackBindDef.agda`
- `TransportSourceRebaseStackProof.agda`
- `SimSourceRebaseStackProof.agda`

The primary new proof consumer is `SimSourceLambdaApplicationᵀ`, reached from
the one-sided `Λ⊑` branches of `SimPairedAllValuesProof.agda`.

## Safe migration order

1. Finish and strict-check role-tagged `World`, `SourceRebase`, and trusted
   examples.
2. Add the one-step aligned evolution and its five sound projections; remove
   the unused false potential-update projection.
3. Add producer/request support and sequence open-frame transport.
4. Add the aligned source-bind scope root and CTI transport interface/proof.
5. Migrate no-open simulation interfaces from geometric zero to role-derived
   open-frame emptiness, keeping the invariant gate unchanged.
6. Replace the transitional stack's LIFO/non-rebase assumptions before using
   the aligned evolution in `SimSourceLambdaApplicationᵀ`.
7. Pin the resulting evolution and CTI at the target-identity checkpoint-3
   trusted example.
