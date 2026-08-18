T5 NS-4 stage 2 proposal: target-wrapper strict surfaces

Date: 2026-08-17

Status: blocked by the standing major-lemma rule.

The stage-2 strict cells require a target-wrapper strip theorem.  The fixed
field types in `StructuralStrictViewSurfaces` are already the right public
surface; they should not be reshaped.  The missing checked theorems should
inhabit those fields directly:

```agda
structural-lambda-strict-surface :
  StructuralΛStrictSurfaceᵀ

structural-all-cast-strict-surface :
  StructuralAllCastStrictSurfaceᵀ

structural-gen-strict-surface :
  StructuralGenStrictSurfaceᵀ

structural-reveal-strict-surface :
  StructuralRevealStrictSurfaceᵀ

structural-conceal-strict-surface :
  StructuralConcealStrictSurfaceᵀ
```

The four non-lambda cells are the new major part.  For example, the
`∀`-cast cell must turn:

```agda
rel : W ∣ γ ⊢² M ⊑ V ⟨ ∀ᶜ d ⟩ ∶ p
```

into the `StructuralStrictChild` whose recursive relation field is:

```agda
child-relation :
  W ∣ γ ⊢² M ⊑ V ∶ child-endpoint
```

where:

```agda
child-endpoint : Aₛ ⊑ᵂ⟨ W ⟩ `∀ B
```

and whose chain and typed-spine fields cover:

```agda
name-type-app-frame B X refl refl ▻ⁱ
cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ
mapInstantiationSpine keep spine
```

The `gen`, `reveal`, and `conceal` cells have the same proof shape after a
target bind: from a parent relation against the visible target wrapper, produce
the child relation against `⇑ᵗᵐ V`, plus the target-bind child plan,
chain plan, frame-absorption chain, and typed spine required by
`StructuralStrictChild`.

The proof is not a local constructor application.  It must recurse on the
term-imprecision derivation, just as the live
`target-id-step-inversion` theorem does for target identity casts:

```agda
target-id-step-inversion :
  ...
  → W ∣ γ ⊢² M ⊑ M′ ⟨ id a ⟩ ∶ q
  → W ∣ γ ⊢² M ⊑ M′ ∶ q
```

For the strict target wrappers, the analogous derivation-recursive cells must
handle:

```agda
⊑cast² (∀ᶜ d) rel q
⊑cast² ((gen d) A≢★) rel q
⊑reveal² mono rb same c⊢ rel q
⊑conceal² mono rb same c⊢ rel q
```

and (per PR review) the PAIRED-wrapper heads, which can produce the same
target wrappers while the source remains a value carrying its own
wrapper — the paired case of `target-id-step-inversion` is the model:

```agda
cast⊑cast² c (∀ᶜ d) rel q        -- paired ∀ᶜ target
cast⊑cast² c ((gen d) A≢★) rel q -- paired gen target
reveal⊑reveal² mono rb same c⊢ c′⊢ rel q
conceal⊑conceal² partner mono rb same c⊢ c′⊢ rel q
packaged-seal-star² partner mono rb same c⊢ c′⊢ rel pkg-rel q
```

In the paired rows the strip keeps the source wrapper on the child
relation (the source side takes zero steps), so the `StructuralStrictChild`
endpoint is the paired child form rather than the bare source; the
per-row conclusion shapes must be checked against the fixed
`StructuralStrictChild` fields when implementing.

and replay source-side heads such as:

```agda
cast⊑² c rel q
reveal⊑² mono rb same c⊢ rel q
conceal⊑² ok mono rb same c⊢ rel q
Λ⊑² ...
Λ⊑²-smart-comma ...
```

The required square for each strict target wrapper is:

$$
\begin{array}{ccc}
M & \sqsubseteq & \operatorname{wrap}(V) \\
\downarrow^{0} & & \downarrow \\
M & \sqsubseteq & V_{\mathsf{child}}
\end{array}
$$

The lower horizontal edge is exactly the `child-relation` field consumed by
`StructuralNameInstantiationProof.agda`.  The target-only peel modules already
provide the right vertical edge and finalizer:

```agda
structural-target-all-peel
structural-target-gen-peel
structural-target-reveal-peel
structural-target-conceal-peel
```

The live LG-3 repair supplies target-cast step support such as
`target-id-step-inversion`, exposed ground/expand cast cells, and generated
projection replacements.  It does not export the polymorphic wrapper strip
theorems above.  Proving those theorems would be an induction over `⊢²`, so it
falls under the standing rule for new major lemmas.

No live Agda statement, term-imprecision relation, reduction relation, or
Catchup knot file was changed for this proposal.
