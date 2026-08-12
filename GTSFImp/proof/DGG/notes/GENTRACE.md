# GEN Trace Verdict

## Verdict

Yes. A source-reachable target reduction does exhibit the inversion shape

```agda
(U ↓ seal Y S) ⟨Y!⟩
```

It is not minted by source-level rigid-variable/`★` consistency. It is minted
on the GEN path after the runtime fresh name exists.

The checked witness is `GenTraceScratch.agda`.

## Checked Core Facts

`GenTraceScratch.agda` records:

- `gen-fresh-zero-is-projection`: `genᵐ idᶜ 0 ≡ ★∼X`.
- `example12-post-gen-tag-env-zero`: after flipping the post-GEN environment,
  the fresh zero name has injection direction `X∼★`.
- `example12-name-tagged-sealed-value`: the term
  `($ (κℕ 7) ↓ seal 0 ℕ) ⟨id (＇0)!⟩` is a value.
- `example12-right-step₂-change`: Example 12's right step 2 is the β-gen
  allocation at `ℕ`.
- `example12-right-step₄-next`: two ordinary target steps later, the trace is
  `right₅`, whose argument contains the tagged-sealed value.

The scratch type-checks with:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GenTraceScratch.agda
```

## Trace Point

In `GTSFImp/proof/DGG/Examples.agda`, Example 12's right trace has:

- `right-step₂`: β-gen for the `να.α!→α?` cast at the `ℕ` instantiation.
- `right₃`: the β-gen reduct, with the GEN projection still as a function cast.
- `right-step₃`: `β-reveal-⇒`, sealing the argument at the new `ℕ` cell.
- `right-step₄`: `β-⇒`, pushing the GEN-derived argument cast onto that sealed
  argument.
- `right₅`: contains
  `(($ (κℕ 7) ↓ seal 0 (‵ `ℕ)) ⟨ id (＇ 0) ! ⟩)`.

So the concrete source-reachable state is:

```agda
right₅ =
  ...
    · (($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
      ⟨ id {μ = flipᵐ (genᵐ ...)} (＇ 0) ! ⟩)
  ...
```

The same shape persists through `right₁₃`, where the matching projection is
outside it; `right-step₁₃` then cancels it by `tag-untag`.

## Catalog And Catch-Up

Catalog screen facts checked in `GenTraceScratch.agda`:

- `left-only-gen-path` is screen-clean, but its more-precise side has a
  nonempty variable-tag summary and its more-imprecise side has an empty one.
- `gen-inst-return-poly` and `gen-inst-self-nat` are screen-clean and have empty
  more-precise variable-tag summaries.
- Example 12 right has a nonempty variable-tag summary.

The read-only catch-up step catalog in
`GTSFImp/proof/DGG/Catchup/InstCatchupRightDef.agda` and
`InstCatchupRightProof.agda` does not itself introduce a fresh
`(U ↓ seal Y S) ⟨Y!⟩` wrapper. The GEN catch-up reduct is the direct β-gen
shape:

```agda
⇑ᵗᵐ V ⟨ c ⟩ ↑ 〖 zero , ⇑ᵗ C ↑ B 〗
```

The tagged-sealed value arises later when the GEN-derived function cast is
pushed across an already sealed argument.

## Candidate Walk Characterization

For the walk, the reachable tagged-sealed target input should not be
characterized as arbitrary variable injection over arbitrary seal. The checked
reachable form is narrower:

```agda
(U ↓ seal Y S) ⟨Y!⟩
```

where `Y` is the fresh GEN name, the injection environment is the flipped
post-GEN environment with `Y ↦ X∼★`, and the same `Y` is the seal name on the
payload. This is an ordinary source-reachable target state, not only a
mid-catch-up artifact.
