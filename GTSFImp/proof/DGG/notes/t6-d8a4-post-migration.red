T6 D8a4 post-migration substitution probes
============================================

Scope
-----

This note re-runs the D8a2 caller-supply and D8a3 occurrence-feasibility
probes after the full D15 source-conceal migration.  The original probe files
are retained as historical artifacts.  They no longer check standalone:
`T6D8a2CallerSupplyProbe.agda` has an uncovered
`conceal⊑²-source-ok` case.  The replacements are:

- `notes/probes/T6D8a4PostMigrationCallerSupplyProbe.agda`;
- `notes/probes/T6D8a4PostMigrationOccurrenceProbe.agda`.

Both replacement modules check with Agda 2.8, without postulates, holes, or
pragmas.

D8a2 caller supply: STILL-REFUTED
---------------------------------

The D8a2 probe asks the caller to supply a `TermSubstRelBoundary` at every
structurally reachable boundary node.  Its old source-reveal edge is replaced
by the migrated source-conceal edge

```agda
boundary-source-conceal P.mono-forward
  (CTI2.tag-rebase-varᴸ P.reversed-rebase)
```

from root `W` to premise `Wᵖ`.  The caller argument remains related at `W`:

```agda
argument-at-W :
  P.W CTI2.∣ [] ⊢² source-argument ⊑ target-argument ∶ ★⊑★
```

The boundary lookup still demands the same pair at `Wᵖ`, and the checked
declaration remains:

```agda
argument-at-Wᵖ-empty :
  P.Wᵖ CTI2.∣ [] ⊢² source-argument ⊑ target-argument ∶ ★⊑★
  → ⊥
```

The migrated `conceal⊑²-source-ok` head does not inhabit the relation.  After
peeling the non-star source seal, its recursive premise relates the source
natural-number constant to the stale `Y-old` target tag.  The only possible
target-cast head would require
`(‵ `ℕ) CTI2.⊑ᵂ⟨ W′ ⟩ (＇ P.Y-old)`, which is empty.  The updated inversion is
exhaustive and proves:

```agda
caller-supply-post-migration-verdict :
  CallerSupplyPostMigrationVerdict
```

Thus the blanket caller-supplied boundary environment remains too strong.

D8a3 occurrence feasibility: COUNTEREXAMPLE-DEAD
-------------------------------------------------

The occurrence itself can still be placed at `Wᵖ`.  The replacement builds

```agda
core-at-premise :
  P.Wᵖ CTI2.∣ premise-context ⊢²
    source-core ⊑ target-core ∶
      I.⇒⊑⇒ I.ι⊑★ I.★⊑★
```

and its free beta-variable use is still at `p-use = ★⊑★`.  Consequently the
substituted occurrence obligation is still empty:

```agda
harvested-obligation-still-empty :
  P.Wᵖ CTI2.∣ [] ⊢²
    Caller.source-argument ⊑ Caller.target-argument ∶ p-use
  → ⊥
```

What changed is reachability of that occurrence from the old caller root.
The migrated function-conceal reconstruction uses

```agda
source-ok-wrapper = unseal P.X (‵ `ℕ) ↦↓ id↓ ★
```

and would be classified by `conceal⊑²-source-ok fun-conceal-ok`.  Its premise
type relation exists at `Wᵖ`, but rebuilding at `W` needs

```agda
((＇ P.X) ⇒ ★) CTI2.⊑ᵂ⟨ P.W ⟩ (★ ⇒ ★).
```

That result witness is empty: its domain would require
`(＇ P.X) CTI2.⊑ᵂ⟨ P.W ⟩ ★`, while `W` marks the old `X`/`Y-old` center
precise.  `source-ok-body-at-old-root-empty` checks that no related body of
the reconstructed shape exists.

The `conceal⊑²-seal-star-open` alternative does not recover the old
configuration:

1. Keeping the old target function unwrapped asks for the rule's fixed
   premise `★ CTI2.⊑ᵂ⟨ P.Wᵖ ⟩ (★ ⇒ ★)`, refuted by
   `open-premise-against-function-empty`.
2. Retargeting the premise to `★` makes the type witness `★⊑★`, but the rule
   also asks for `NoTargetOccupantAtSource P.Wᵖ P.X`.  `Y-fresh` occupies
   exactly that center, and `open-gate-at-premise-empty` refutes the gate.
3. Trying the open rule at the old root additionally lacks the result witness
   `(＇ P.X) CTI2.⊑ᵂ⟨ P.W ⟩ ★`, as checked by
   `open-result-at-old-root-empty`.

The old D8a3 counterexample therefore cannot be reconstructed on the migrated
relation.  The argument relation at the proposed occurrence node is still
uninhabited, but the migrated premises prevent the related caller body from
reaching that node.

D8a.5 consequence
------------------

No D8a.5 `⊢²-term-subst` statement is proposed in this artifact.  The task's
condition that the counterexamples be dead is not met: D8a3's concrete
occurrence counterexample is dead, but D8a2 still refutes the caller-supplied
`TermSubstRelBoundary` premise.  A same-`p` substitution statement would need
a separate justification showing that only derivation-reachable migrated
premises matter; these two probes do not provide that theorem.
