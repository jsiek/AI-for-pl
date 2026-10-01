# GTSFImp consistency detours: finite model and search

## Result in one example

For the motivating endpoints

`∀Y. Y→Y ∼ ∀X. X→X`

the checked GTSFImp relation has exactly one derivation in the model:

`∀ᶜ (id[Y] ↦ id[Y])`.

The proposed second route needs the two-step leaf coercion

`X ! ︔ Y ? : X ⟹ ★ ⟹ Y`.

That route is accepted by GTNF because `Coercion.agda` has the sequencing
constructor `_︔_`. It is not evidence for
`GTSFImp.Consistency._⊢_∼_`, which has no sequencing or transitivity
constructor. After `gen` and `inst`, GTSFImp would need a direct derivation of
`X ∼ Y` for distinct variables; none of its constructors provides one.

Thus the GTNF probe is valid, but the background claim that it supplies a
second GTSFImp declarative-consistency derivation is false. This distinction
also changes the answer for

`∀Y. Y→★ ∼ ∀X. X→X`:

GTSFImp rejects the pair entirely; it is not a pair consistent only through a
GTSFImp detour.

## Model

[`model.py`](model.py) implements intrinsically scoped de Bruijn types,
`shift`, occurrence, the four consistency modes and their extensions, and all
constructors of `Consistency._⊢_∼_`. `enumerate_evidence` returns every proof
tree for fixed endpoints. Tags/checks range over the finite `Ground` family.
The Agda side conditions on `inst` and `gen` are tested literally. Those rules
remove an outer universal before recurring; tag/check recursion changes `★` to
a non-star ground type. These facts prevent cycles.

The canonical evidence is the first enumerated tree. Structural rules come
first; at two universal endpoints the order is `∀ᶜ`, `inst`, `gen`, then the
bottom rules, matching `lower?`. Unlike `lower?`, the selector uses the actual
consistency modes for tags/checks, so under `idᶜ` it accepts both `X ∼ ★` and
`★ ∼ X` for a free cross-mode name.

The model also contains:

- a decision procedure for every rule of `Imprecision._⊢_⊑_`;
- a direct Python transcription of `Consistency2.lowerAcc`;
- the local overlap ban and the stronger all-`∀` ban;
- the requested alignment test. It ignores a subtree once a less precise
  endpoint is `★`, treats bottom clauses as `★` cases, and permits an
  `inst`/`gen` mismatch when the relevant imprecision proof contains `∀⊑`.

All displayed search records use named binders. With no display limit, this
command emits every counterexample, ordered first by total size and then by
the four component sizes:

```sh
python3 GTNF/notes/detour/model.py --search --max-size 6
```

`--max-examples K` limits only JSON display, not the search.

## Agda validation

[`Validation.agda`](Validation.agda) asks Agda 2.8.0 to normalize the following
closed `lower?` calls. Every stated equality closes by `refl`; Python returned
the same lower type in all 12 rows.

| # | `A` | `B` | normalized `lower? A B` |
|---:|---|---|---|
| 1 | `ℕ` | `ℕ` | `just ℕ` |
| 2 | `ℕ` | `𝔹` | `nothing` |
| 3 | `ℕ` | `★` | `just ℕ` |
| 4 | `★` | `𝔹` | `just 𝔹` |
| 5 | `ℕ→𝔹` | `★→★` | `just (ℕ→𝔹)` |
| 6 | `∀X. X→X` | `∀X. X→X` | `just (∀X. X→X)` |
| 7 | `∀X. X→X` | `★→★` | `just (∀X. X→X)` |
| 8 | `∀X. X` | `∀X. ★` | `just (∀X. X)` |
| 9 | `∀X. ★` | `∀X. X` | `just (∀X. X)` |
| 10 | `∀X. X` | `★` | `just (∀X. X)` |
| 11 | `∀Y. Y→★` | `∀X. X→X` | `nothing` |
| 12 | `∀X.∀Y. X` | itself | `just (∀X.∀Y. X)` |

The same file checks the direct identity evidence, a genuine all-`∀`
`gen` example, and `idᶜ ⊢ X ∼ ★`. It also confirms the expected limitation
`lower? X ★ = nothing` under its strict `idᵐ` imprecision environment. The
existing `GTNF/agda/notes/LeftOnlyUnbindProbe.agda` type-checks separately,
confirming that the sequenced GTNF coercion is valid.

As a broader internal check, the Python declarative enumerator and its
`lowerAcc` transcription agreed on all 57,121 ordered pairs of closed types of
size at most 5. There were no Agda/Python disagreements in the normalization
table. The only disagreement is the stated scope error between “GTNF typed
coercion” and “GTSFImp consistency evidence.”

## Exhaustive search

Size is Agda's node count: atoms have size 1, `∀A` has `1 + size A`, and
`A→B` has `1 + size A + size B`. Both endpoint types in every pair have size
at most 6. The open run has one free name with consistency mode `★∼X∼★` and
imprecision mark `X⊑X`.

| context | types | consistent ordered pairs | imprecision ordered pairs | Q1 squares | time |
|---|---:|---:|---:|---:|---:|
| closed | 932 | 36,642 | 7,658 | 1,416,992 | 23.40 s |
| one free `X` | 1,702 | 78,780 | 10,040 | 1,841,052 | 59.49 s |

Python was 3.12.3. The combined wall time was 90.49 seconds.

### Q1. Canonical-selector monotonicity

The answer is **no**: 8,901 closed squares and 11,001 one-free-name squares
are not aligned. The command above emits every one in the requested order.
There are no failures through size 3; the smallest closed failure has maximum
type size 4:

| | precise | less precise |
|---|---|---|
| first endpoint | `A = ∀X. X→X` | `A′ = ★→★` |
| second endpoint | `C = ∀X. X→X` | `C′ = ★→★` |
| canonical evidence | `∀ᶜ (id[X] ↦ id[X])` | `id[★] ↦ id[★]` |

Both type-imprecision derivations use `∀⊑`. At the root the evidence
constructors are `∀ᶜ` and arrow. No less precise endpoint is yet `★`, and
there is no one-sided `inst`/`gen`, so this is a counterexample under the
given alignment definition.

The smallest counterexample that actually mentions the free cross-mode name
is the same shape:

`A = C = ∀Y. Y→X`, `A′ = C′ = ★→X`.

The selected evidence changes from `∀ᶜ (id[Y] ↦ id[X])` to
`id[★] ↦ id[X]`. The failures are therefore not evidence of the advertised
identity detour; ordinary `∀⊑` can already erase the constructor selected by
the preferred structural case.

### Q2. Bans and the static gradual guarantee

The local **overlap ban** rejects an `inst`/`gen` at universal endpoints only
if a structural `∀ᶜ` derivation also exists. It removed no consistent pair and
caused no graduality failure at size 6:

| context | SGG candidates | failures | pairs consistent only by a forbidden overlap |
|---|---:|---:|---:|
| closed | 1,416,992 | 0 | 0 |
| one free `X` | 1,841,052 | 0 | 0 |

The stronger **all-`∀` ban** rejects every `inst` whose target is a universal
and every `gen` whose source is a universal. It breaks the guarantee:

| context | SGG candidates | failures | rejected ordered pairs | rejected unordered pairs |
|---|---:|---:|---:|---:|
| closed | 1,338,014 | 3,634 | 2,980 | 1,490 |
| one free `X` | 1,752,186 | 3,982 | 4,144 | 2,072 |

Let `T = ∀X.∀Y. X` and `U = ∀X. ★`. The four smallest closed failures are:

1. `A = C = T`, `A′ = ★`, `C′ = T`.
2. `A = C = T`, `A′ = T`, `C′ = ★`.
3. `A = C = T`, `A′ = U`, `C′ = T`.
4. `A = C = T`, `A′ = T`, `C′ = U`.

For example, `T ∼ T` uses `∀ᶜ (∀ᶜ id[X])`, while full consistency proves
`U ∼ T` by `gen (∀ᶜ (？ id[X]))`. The strong ban removes that latter proof,
so case 3 loses target consistency after `T ⊑ U`.

The smallest unordered pairs consistent only through an all-`∀`
`inst`/`gen` are, in order:

1. `★ ∼ T`.
2. `U ∼ T`.

At size 6 there are 1,490 such closed pairs and 2,072 in the one-name
context; the untruncated command lists all of them.

## Assessment

On the motivating identity example, three candidate responses act as follows:

1. If source casts are produced only by the canonical GTSFImp selector, then
   both identity casts use `∀ᶜ (id ↦ id)` and the GTNF sequence never arises.
2. If arbitrary explicit GTNF coercions remain source constructs but sequences
   such as `X! ︔ Y?` are forbidden below a `gen`/`inst` crossing, then the
   probe's route is rejected directly; this is a restriction on GTNF coercion
   typing, not on GTSFImp consistency.
3. If GTNF coercions are normalized before cast-term imprecision compares
   them, then the proposed route would need a proved normalization from
   `gen (inst ((X! ︔ Y?) ↦ (Y! ︔ X?)))` to the direct identity coercion.

The bounded evidence favors the first response when casts are compiler
generated. The local overlap ban is harmless through size 6 but does not touch
the motivating GTNF sequence, while the stronger all-`∀` ban has concrete
static-graduality counterexamples. Independently, the strict constructor-wise
alignment requested in Q1 is too strong for the existing `∀⊑` rule even when
all casts are canonical.
