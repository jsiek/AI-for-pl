# Insertion-generalized fundamental motive

Design note for Milestone 1 of `FUNDAMENTAL-PROPERTY-PLAN.md`.

## Problem

A CTI derivation for the body of `Λ⊑Λ²` lives at the syntactic world
`liftWorldBoth X⊑X Wᶜ`, whose new center is *unbound* (`store-lift`). The
LR tests a universal at an arbitrary future `W′ ≽ W` and then allocates the
binder as a *bound* paired center (`bothBindWorld (forgetWorld W′) R R′`).
The future's allocations therefore sit behind the syntactic binder:

```text
syntactic:   liftWorldBoth Wᶜ            centers:  binder, Wᶜ…
semantic:    bothBindWorld fW′ R R′      centers:  binder, (W′ \ W)…, W…
```

A `Future` or an OPE cannot reorder these centers, so an induction
hypothesis stated at semantic worlds realizing the syntactic world exactly
(`forgetWorld W₁ ≡ liftWorldBoth Wᶜ`) is useless: no such `W₁` is a
predecessor of the test world.

## Motive

Generalize over an insertion `ins : Wᶜ ↪ forgetWorld W` consisting of
endpoint OPEs `ρᴾ : Δᴾ ↪ᵗ Δᴾ′`, `ρᴵ : Δᴵ ↪ᵗ Δᴵ′`, a center OPE
`π : Δᶜ ↪ᵗ Δᶜ′`, and coherence fields (the both-sided form of
`TargetExtend.TargetInsert`):

- embedding squares `ηᴾ′ ∘ ρᴾ ≡ π ∘ ηᴾ` and `ηᴵ′ ∘ ρᴵ ≡ π ∘ ηᴵ`;
- `impEnv′ (π Z) ≡ impEnv Z` on the image;
- `StoreRename` of both endpoint stores along `ρᴾ`, `ρᴵ`;
- alignment transport and reflection as needed by the cases.

```agda
InsertedFundamental d =
  ∀ W (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W)) k
  → CompiledTermRelation {W = W} (insert⊑ ins p) k (insertCtx ins Γ)
      (renameᵗᵐ (toRenameᵗ ρᴾ) Mᴾ) (renameᵗᵐ (toRenameᵗ ρᴵ) Mᴵ)
```

The identity insertion yields `FundamentalProperty d`.

## Why it closes the universal cases

Given `ins : Wᶜ ↪ fW` and the test extension chosen by the universal
observation at `W′ ≽ W`, compose `ins` with the future and lift under the
binder:

```text
liftWorldBoth Wᶜ  ↪  bothBindWorld (forgetWorld W′) R R′
```

This is a world-level lemma (one per world former), not a derivation
recursion. The hypothesis for the literal body premise then applies at
`pairedBindWorld W′ R R′ fresh`. Nested universals compose insertions.

What remains is semantic: the body relation observes the type-beta
contractum `V ↑ 〖 zero , ⇑R ↑ B 〗`, so the related bodies at `B` must be
carried through a matched reveal at the fresh center to `B [ R ]ᵗ`. This
lemma is independent of the motive and is shared with Milestone 2.

## Consequences for the compatibility lemmas

The lemmas are applied to renamed terms at the semantic world, where no
derivation exists. Derivation premises must therefore be replaced:

- `application`, `primitive`: premises already unused; drop them.
- `lambda`, casts: used only for endpoint typing; take typing premises,
  obtained by `typing-renameᵗ` from the original derivation's typing.

Renaming commutes definitionally with every term constructor, so the
non-binder cases are wrappers; `ƛ` needs the context-extension case of
`insertCtx`, and the universal cases use the lifting lemmas above.

The rebase constructors (Milestone 2) keep their obligations, now stated
under an insertion; rebase × insertion commutation is needed on any route.
