# Initial Closed `CastTerm` Pair

Branch: `agent/gtsf-extra-cast-right`

Checked scratch: `GTSFImp/proof/DGG/notes/InitialPairScratch.agda`

Command:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/notes/InitialPairScratch.agda
```

## Pair

`Pᶜ` is `PPrimeTraceScratch.P′ᶜ`.  The scratch also proves:

```agda
Pᶜ-local-gate : Pᶜ ≡ PLocalᶜ
```

`Qᶜ` is the closed direct `CastTerm` partner:

```agda
Qᶜ = QFunᶜ · taggedZeroᶜ
```

where `QFunᶜ` is the `λd` wrapper whose body instantiates the GEN-cast dynamic identity at `★`:

```agda
genDynIdᶜ = dynIdᶜ ⟨ ★⇒★∼∀X⇒X ⟩
QBodyᶜ = ((genDynIdᶜ ⦂∀ X⇒X [ ★ ])
  · ((` 0) ⟨ id {μ = idᶜ {Δ = 0}} ★ ⟩))
QFunᶜ = ƛ QBodyᶜ
```

## Initial Relation

The initial relation is checked directly, not through
`compile-preserves-imprecision²`:

```agda
initial-Pᶜ⊑Qᶜ :
  W₀ ∣ [] ⊢² Pᶜ ⊑ Qᶜ ∶ ★⊑★₀
```

The key subderivation is:

```agda
innerId⊑dynId
innerId⊑genDynId = ⊑cast² ★⇒★∼∀X⇒X innerId⊑dynId ...
innerCallee⊑ = •⊑•² ... innerId⊑genDynId ...
```

So the `⊑` relation between the initial closed pair is derivable with the
intended slack structure.

## Trace Gates

Left trace:

```agda
P-step₀-change = bind ★
P-step₃-change = bind (＇ Fin.zero)
P₇-two-seal-state-gate : P₇ ≡ P-two-seal-result-context
P₇-two-seal-skeleton-gate :
  RC.skeleton P₇ ≡ RC.skeleton P.two-seal-result-context
```

Right trace:

```agda
Q-step₁-change = bind ★
Q₆-generated-tagged-input-gate :
  Q₆ ≡ (Q-generated-tagged-input ⟨ X? ⟩) ↑ Conv.unseal Fin.zero ★
```

with:

```agda
Q-generated-tagged-input =
  (($ (κℕ 0) ⟨ Q-shifted-ℕ! ⟩) ↓ Conv.seal Fin.zero ★)
    ⟨ Q-Y! ⟩
```

## Mid-Simulation Instance

The walk-input relation reuses `StarRepChainProbe`:

```agda
mid-output = Probe.output
mid-input = Probe.input
mid-q : ＇ Fin.zero ⊑ᵂ⟨ Probe.W ⟩ ＇ Fin.zero
```

The trace-produced input shapes are connected to the probe by:

```agda
left-walk-input-skeleton-gate :
  RC.skeleton P-two-seal-arg ≡ RC.skeleton Probe.M

right-walk-input-skeleton-gate :
  RC.skeleton Q-generated-tagged-input ≡ RC.skeleton Probe.N
```

No `GTSFImp/` files were edited.
