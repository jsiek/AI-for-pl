# Graduality through an imprecision-indexed logical relation

## Objective and terminology

The primary goal of `LR-narrow` is a fundamental theorem of **graduality**.
For every live type-imprecision derivation

$$
p : \Phi \mid \Delta_P \vdash A_P \sqsubseteq A_I \dashv \Delta_I,
$$

the semantics assigns a step-indexed Kripke relation between closed
interpreter values at the two endpoints:

$$
\mathcal{V}\llbracket p \rrbracket_I^k(V_I,V_P).
$$

In Agda this judgment is

```agda
ValueNarrowing p I k Vᴵ Vᴾ
```

The syntactic relation records the precise source before the imprecise target.
The semantic and displayed orientation is deliberately the reverse: `Vᴵ` is
the imprecise-left value at `Aᴵ`, and `Vᴾ` is the precise-right value at `Aᴾ`.
The interpretation therefore maps `Δᴵ` to `left-types` and `Δᴾ` to
`right-types`. This is not primarily a parametricity relation. It is the
relational interpretation of
type imprecision used to prove graduality.

This follows the terminology of New and Ahmed's
[Graduality from Embedding-Projection Pairs](https://arxiv.org/abs/1807.02786):
graduality is the local-to-global semantic principle corresponding to type
and term imprecision. For polymorphic gradual typing, New, Jamner, and Ahmed
show that parametricity can follow from a relational interpretation of
graduality in
[Graduality and Parametricity](https://doi.org/10.1145/3371114).

The intended theorem hierarchy is therefore:

1. fundamental graduality for open typed term-imprecision derivations;
2. operational graduality, namely the four direct DGG properties, for closed
   compiled programs; and
3. parametricity as a specialization of graduality at reflexive universal
   type and term imprecision.

## Semantic judgments

### Values

`ValueNarrowing p I k Vᴵ Vᴾ` is indexed by the actual proof `p`, rather than by
a separately defined relational type code. Every clause includes a
`TypedClosedEndpoints` certificate:

$$
\begin{aligned}
  V_I &: \llbracket A_I \rrbracket_{I_L}, \\
  V_P &: \llbracket A_P \rrbracket_{I_R}.
\end{aligned}
$$

The constructor of `p` then determines the semantic observation. Base values
must agree, functions preserve related arguments in every future world, and
universal values preserve every valid paired-seal extension. The active
positive `id★` clause exposes tagged values whose runtime tags agree at an
existential ground imprecision derivation `q`, and whose untagged payloads
satisfy `ValueNarrowing q I k`. The enclosing observation is at `suc k`, so
this is a genuine guarded recursive use. Raw cross-world tag equality is
intentionally not required for variable tags: distinct seals paired by the
Kripke world count as equal. The `tag` and `tag ⇛` clauses remain provisional.

At zero remaining elimination steps, `FunctionsRelated` and
`UniversalsRelated` are unit. Endpoint narrowing is already supplied by
`TypedClosedEndpoints`, and both `applyValue` and paired `instantiateValue`
time out at zero interpreter fuel. Their behavioral obligations begin only at
a positive remaining index.

### Worlds, atoms, and sealing

An atom is a downward-closed relation

$$
R : \mathbb{N} \to \mathit{Value} \to \mathit{Value} \to \mathit{Set}.
$$

The world can associate such a relation with either a pair of seals

$$
\alpha \leftrightarrow \alpha' : R
$$

or a precise-right seal related to the dynamic left side. The world-validity
proof
ensures that every value pair admitted by `R` has the semantic types recorded
for those allocations.

For an assumption `X ˣ⊑ˣ Y`, related nominal values have the shape

$$
\mathsf{sealed}\;\alpha_I\;U_I
\quad\text{and}\quad
\mathsf{sealed}\;\alpha_P\;U_P,
$$

where the first value is imprecise-left and the second is precise-right. The
atom is applied in the same order: `R k Uᴵ Uᴾ`. Thus the seals enforce
the abstraction boundary while the arbitrary atom supplies its relational
meaning.

### Universal types

For `∀ⁱ p`, related values must remain computation-related after every
`PairedBinderExtension`. Such an extension installs a new atom for
`0 ˣ⊑ˣ 0`, associates it with a pair of runtime seals, and interprets the
body contexts of `p` under those seals.

The two seals are required to be genuinely fresh, and
`fresh-paired-binder-extension` constructs an extension for every supplied
downward-closed, type-respecting atom and pair of well-formed represented
types. Once fundamental graduality is available, reflexive imprecision for a closed
`M : ∀ X. A` can be instantiated with an arbitrary atom. Compatibility of
the compiler's reveal conversions then transports the nominal result back to
the chosen concrete type interpretations. That is the expected parametricity
corollary.

The precise-right `ν` clause is not this paired parametricity argument. It
interprets imprecision between a universal precise source and a
non-universal imprecise target and still needs to account explicitly for the
compiler's post-allocation
reveal/generalization conversion.

## Computations and finite observations

The computation relation packages the two directional approximations needed
for graduality. At logical index `k`, it currently contains:

- `forward-return`: if the imprecise-left computation returns at some
  `n ≤ k`, the precise-right computation eventually returns a related value
  or raises blame;
- `backward-return`: if the precise-right computation returns at some
  `n ≤ k`, the imprecise-left computation eventually returns a related
  value; and
- `forward-blame`: if the imprecise-left computation raises blame at some
  `n ≤ k`, the precise-right computation eventually raises blame.

The matching computation may use a different fuel index. This is essential:
the two compiled programs need not perform the same number of interpreter
calls.

At present the relation imposes no condition when either finite observation
is `timed`, or when the precise-right computation raises blame. Errors are
excluded
separately by interpreter type soundness for the well-typed programs to which
graduality is applied.

Consequently the current relation says the following about divergence:

- two computations that time out at every index satisfy all return premises
  vacuously;
- if the precise-right computation times out at every index, the
  imprecise-left computation cannot return, because `forward-return` would
  produce a precise-right return or blame;
- if the precise-right computation times out at every index, the
  imprecise-left computation cannot blame, because `forward-blame` would
  produce precise-right blame; and
- if the imprecise-left computation times out at every index, the
  precise-right computation cannot return, because `backward-return` would
  produce an imprecise-left return. Precise-right blame remains allowed.

`ComputationsRelated` contains the following blame clause:

```agda
forward-blame : ∀ {n Uᴵ}
  → n ≤ k
  → left n ≡ blamed Uᴵ
  → Σ[ m ∈ ℕ ] Σ[ Uᴾ ∈ RuntimeWorld ]
      right m ≡ blamed Uᴾ
```

The actual field carries the same common-future-world evidence as the return
clauses. Precise-right blame remains otherwise unconstrained, because adding
precision is allowed to introduce blame.

## Divergence belongs outside the finite LR

Finite timeout is not divergence. `timed W` only says that the selected fuel
was insufficient. Requiring matching timeouts at the same index would be too
strong, because related programs may have different evaluation costs.

For that reason the LR should contain finite terminal observations but no
global divergence field. Interpreter divergence is already stated positively
and without negated convergence:

```agda
Divergesᴵ M = ∀ n → IsTimeout (run M n)
```

The divergence parts of graduality should be derived in a separate,
reduction-free corollary module from:

1. fundamental graduality at every logical index;
2. `forward-return`, `backward-return`, and `forward-blame`;
3. interpreter type soundness, which excludes `failed`; and
4. outcome classification and terminal fuel stability.

The derivations are constructive and pointwise in fuel.

### Precise-right divergence

If the precise-right run times out at every index, classify the imprecise-left
outcome at an arbitrary index `n`.

- An imprecise-left return contradicts `forward-return`.
- Imprecise-left blame contradicts `forward-blame`.
- An imprecise-left error contradicts type soundness.
- Therefore the imprecise-left outcome is a timeout.

This proves

```agda
Divergesᴵ right → Divergesᴵ left
```

without defining divergence as failure to converge.

### Imprecise-left divergence

If the imprecise-left run times out at every index, classify the precise-right
outcome at each index `n`.

- A precise-right return contradicts `backward-return`.
- A precise-right error contradicts type soundness.
- The remaining cases are timeout and blame.

The constructive conclusion should be the direct pointwise formulation:

```agda
∀ n → IsTimeout (run right n) ⊎ IsBlame (run right n)
```

It should not initially be strengthened to

```agda
Divergesᴵ right ⊎ Blamesᴵ right
```

because turning `∀ n. timeout(n) ⊎ blame(n)` into the global disjunction
requires deciding whether blame ever appears. Constructively, that is an
omniscience principle even though terminal outcomes are stable once reached.
The pointwise statement is exactly the fourth theorem in the direct DGG
interface and avoids this issue.

Small-step divergence adequacy may later transport these interpreter results
to the positive small-step `Diverges` predicate. That transport remains in
`InterpreterAdequacy/` and must not enter the graduality proof dependency
cone.

## Fundamental graduality theorem

The intended open theorem has the following schematic form:

```agda
fundamental-graduality :
  {w : World}
  (I : Interpretation w)
  (Mᴾ⊑Mᴵ : Φ ∣ Δᴾ ∣ Δᴵ ∣ Γ⊑
    ⊢ᴳ Mᴾ ⊑ Mᴵ ⦂ Aᴾ ⊑ Aᴵ ∶ p)
  → RelatedEnvironments I k Γ⊑ γᴵ γᴾ
  → ComputationsRelated (ValueNarrowing p) I k
      (λ n → interpret (left-world w) γᴵ (left-types I) Mᴵ n)
      (λ n → interpret (right-world w) γᴾ (right-types I) Mᴾ n)
```

Its closed specialization provides the finite return and blame observations.
The separate divergence corollaries above provide the remaining two direct
DGG properties. The paired-universal specialization with an arbitrary atom
then provides the route from graduality to parametricity.

## Action items

- [x] Integrate the guarded `id★` clause with related tags and recursively
  related untagged payloads.
- [ ] Complete the `tag` and `tag ⇛` value clauses.
- [x] Prove downward closure and future monotonicity of active `id★`.
- [x] Prove paired-seal functionality, injectivity, and tag-check coherence
  for the active dynamic clause.
- [x] Require generative freshness in `PairedBinderExtension`.
- [x] Construct paired extensions for arbitrary type-respecting atoms.
- [x] Prove the base, function, and paired-variable constructors for
  `DynamicPayloadRelated`.
- [ ] Replace the localized `TERMINATING` pragma with an explicit
  well-founded lexicographic recursion proof.
- [x] Add `forward-blame` to `ComputationsRelated`.
- [x] Prove downward closure and Kripke monotonicity.
- [x] Define related term environments and their lookup theorem.
- [x] Prove the variable context lemma in its own module.
- [x] Prove the natural-constant context lemma in its own module.
- [ ] Prove compatibility of application, instantiation, coercion, and reveal.
- [ ] Prove fundamental graduality.
- [ ] Derive the four direct DGG theorems without small-step imports.
- [ ] Derive sealing-based parametricity as a universal-type corollary.
