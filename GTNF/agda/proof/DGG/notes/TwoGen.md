# Two gen layers: the gen analogue of H1

Status: 2026-10-06.  Agda: `TwoGen.agda` (this directory).  From
`GTNF/agda` it checks with

```
agda --safe -v0 proof/DGG/notes/TwoGen.agda
```

The file has no holes, no postulates and no pragmas.  It imports the
real relation at HEAD 810b540e (D27 pushes, D28 permissions with R1/R2,
D29 claim-rep) and edits nothing outside this directory.  All.agda does
not import it.  LEFT is the more precise side.  Every cast term below is
a `scripts/render_gtnf.sh` render (`showRun 40 …`).

## Verdict

**The order problem comes back for gen binders, and there is a more
basic failure underneath it, already with ONE gen layer.**

- **(O1) A gen pop needs a grant.**  `cc-gen` pops into a premise at
  the gen's SOURCE type, so the right's cast over the instantiated gen
  body must be peeled first, by `⊑cast`, at the popped name `X ⊑ ★`.
  Under D28 that needs a grant.  A gen body with no covariant check of
  its variable grants nothing.  G0, `(λx:★. 5 : ∀X. X→ℕ)` against its
  own instantiation at ★, is a DGG part 1 counterexample with ONE gen
  layer.  Also, `cc-gen` pops exactly one name, so `gen X. gen Y. p`
  cannot consume two.
- **(O2) H1's order problem.**  With two casts, the right's boundaries
  nest `[+Y^β]` OUTSIDE `[+X^α]`.  Inside `+Y^β` the index must open the
  left's INNER ∀ at Y while its outer ∀ waits.  Pending names open outer
  first, and claim-rep cannot help: a gen binder scopes over no left
  term, so there is nothing to peel.

Every pair below has RELATED sources and RELATED initial cast terms at
`∅ʷ`.  Its left is a value.  The right's final value is unrelated to it
in the real relation, so each one proves `¬ DGG`:

| pair | left | right | real relation | Agda |
|---|---|---|---|---|
| G0 | one gen, body `X! → id(ℕ)` | one Inst | **unrelated, `¬ DGG`** (O1) | `G0.g0-unrelated`, `G0.not-dgg` |
| G2m | two gens | one cast, Merge | **unrelated, `¬ DGG`** (O1) | `G2m.g2m-unrelated`, `G2m.not-dgg` |
| G2 | two gens | two casts | **unrelated, `¬ DGG`** (O2) | `G2.g2-unrelated`, `G2.not-dgg` |
| HRm | a gen under a ∀ (over a Λ) | one cast, Merge | **unrelated, `¬ DGG`** (O1) | `HRm.hrm-unrelated`, `HRm.not-dgg` |
| HR | a gen under a ∀ (over a Λ) | two casts | **unrelated, `¬ DGG`** (O2) | `HR.hr-unrelated`, `HR.not-dgg` |
| N2.Merged | nested gen casts | one cast, Merge | **unrelated, `¬ DGG`** | `N2.Merged.nrm-unrelated`, `N2.not-dgg-m` |
| N2.TwoCast | nested gen casts | two casts | **unrelated, `¬ DGG`** (O2) | `N2.TwoCast.nr-unrelated`, `N2.not-dgg` |
| G2, state 2 | | after the first Inst | **unrelated** | `G2st.g2-st2-unrelated` |
| G2, state 4 | | before the Merge | **unrelated** | `G2st.g2-st4-unrelated` |
| Λ over gen | `ΛX. (… : ∀Y. …)` | — | not constructible from a source (below) | `ΛG-⊢` |

The non-derivability results quantify over every world with no
permission (`κʷ W ≡ []`), every index and every term context.  G0, G2,
HR, HRm and N2.TwoCast hold over any right context.  G2m holds over the
final context `ΔT2`.  N2.Merged holds over `ΔT2` at any κ.  None assumes
`WfWorld` of the top world or `πʷ W ≡ []`.  `not-dgg` combines the
initial pair with `final-of`, which shows by determinism that every run
of the right to a value ends at the pinned final value, in the pinned
context.

**The fix** is a local variant `V` of the relation (§3).  `V1` has
(i) a gen pop against a right cast (`cast⊑cast` with a claim) and
(ii) one pop per gen layer, with the claim continuing below.  It fixes
O1: G0, G2m, HRm and N2.Merged.  G2 and HR stay unrelated in V1
(`InV1.G2ns.g2-unrelated`, `InV1.HRns.hr-unrelated`), so O2 needs more.
`V2` adds (iii): for a left GEN-CAST VALUE only, the index may SKIP a
leading left ∀ (left-only, X⊑★) before it opens the next ∀ at a pending
name, and `⊑⟪⟫` may push new names before carried ones.  This is the gen
analogue of claim-rep.  V2 relates all seven final pairs and G2's
states 2 and 4.  It contains the real relation, so the corpus derives,
and C1–C5 and C4g stay dead.

## 1. The examples

Cast insertion is the compilation: an ascription `(M : A)` becomes a
cast from M's type to A, and an ascription at the term's own type
inserts no cast (PushOrder.md, NoPush.md).

### G0: one gen layer, no covariant check

Sources (RELATED: the same term, and `∀X.X→ℕ ⊑ ★→ℕ`, `G0.src`):

```
L:  (λx:★. 5 : ∀X. X→ℕ)
R:  ((λx:★. 5 : ∀X. X→ℕ) : ★→ℕ)
```

Initial cast terms (RELATED at `∅ʷ`, `G0.init`):

```
L₀ = (λx:★. 5)⟨gen X. (X! → id(ℕ))⟩^[]
R₀ = (λx:★. 5)⟨gen X. (X! → id(ℕ))⟩^[]⟨inst Y. (Y?ℓ0 → id(ℕ))⟩^[]
```

The left is a value.  The right's run (`G0.FR-states`):

```
  (λx:★. 5)⟨gen X. (X! → id(ℕ))⟩^[]⟨inst Y. (Y?ℓ0 → id(ℕ))⟩^[]
⟶ (Inst)
  (ν X:=★. ((λx:★. 5)⟨gen Y. (Y! → id(ℕ))⟩^[] X) ⟨−X → id(ℕ)⟩)⟨id(★) → id(ℕ)⟩^[]
⟶ (TyBeta, ⊣ α:=★)
  ([+X^α] ([−X^α] (λx:★. 5) ⟨id(★) → id(ℕ)⟩)⟨X! → id(ℕ)⟩^[X:★∼X] ⟨−X → id(ℕ)⟩)⟨id(★) → id(ℕ)⟩^[]
```

The final pair is **unrelated** (`G0.g0-unrelated`).  The walk:

```
⊑cast (id(★) → id(ℕ); grants nothing)      L₀ ⊑ [+X^α] …                 ∀X.X→ℕ ⊑ ★→ℕ
  ⊑⟪⟫ +X^α, push X                         L₀ ⊑ (…)⟨X! → id(ℕ)⟩          X→ℕ ⊑ X→ℕ   (X⊑X: α not permitted)
    cast⊑ (cc-gen):  premise λx:★.5 at      ★→ℕ ⊑ X→ℕ                      ✗ ★ ⊑ X
    ⊑cast (X! → id(ℕ) checks nothing):      L₀ ⊑ [−X^α] …   X→ℕ ⊑ ★→ℕ       ✗ X ⊑ ★ needs a grant
    cast⊑cast:                              needs πʷ = []                    ✗
```

Without the push, the index `∀X.X→ℕ ⊑ X→ℕ` is empty, and peeling the
left first leaves `★→ℕ` against `X→ℕ`.  G1 (NoPush.md) is the same pair
with the body `X! → X?`, whose covariant check `X?` grants α.  That
grant is the only thing that makes G1 related.

### G2m and G2: two gen layers

Sources (RELATED: `src-m`; `src-1`, `src-2` of H1):

```
L:    (λx:★.λy:★.x : ∀X.∀Y.X→Y→X)
Rm:   ((λx:★.λy:★.x : ∀X.∀Y.X→Y→X) : ★→★→★)
R:    (((λx:★.λy:★.x : ∀X.∀Y.X→Y→X) : ∀Y.★→Y→★) : ★→★→★)
```

The initial cast terms are related at `∅ʷ` (`G2m.init`, `G2.init`).
The left is the value

```
(λx:★. (λy:★. x))⟨gen X. (gen Y. (X! → (Y! → X?ℓ0)))⟩^[]
```

The run of `Rm` (one cast; it Merges twice):

```
  (λx:★. (λy:★. x))⟨gen X. (gen Y. (X! → (Y! → X?ℓ0)))⟩^[]⟨inst Z. (inst X′. (Z?ℓ0 → (X′?ℓ0 → Z!)))⟩^[]
⟶ (Inst)
  (ν X:=★. ((λx:★. (λy:★. x))⟨gen Y. (gen Z. (Y! → (Z! → Y?ℓ0)))⟩^[] X) ⟨∀Y. (−X → (id(Y) → +X))⟩)⟨inst X′. (id(★) → (X′?ℓ0 → id(★)))⟩^[]
⟶ (TyBeta, ⊣ α:=★)
  ([+X^α] ([−X^α] (λx:★. (λy:★. x)) ⟨id(★) → (id(★) → id(★))⟩)⟨gen Y. (X! → (Y! → X?ℓ0))⟩^[X:★∼X] ⟨∀Y. (−X → (id(Y) → +X))⟩)⟨inst Z. (id(★) → (Z?ℓ0 → id(★)))⟩^[]
⟶ (Inst)
  (ν Y:=★. (([+X^α] ([−X^α] (λx:★. (λy:★. x)) ⟨id(★) → (id(★) → id(★))⟩)⟨gen Z. (X! → (Z! → X?ℓ0))⟩^[X:★∼X] ⟨∀Y. (−X → (id(Y) → +X))⟩) Y) ⟨id(★) → (−Y → id(★))⟩)⟨id(★) → (id(★) → id(★))⟩^[]
⟶ (TyBeta, ⊣ β:=★)
  ([+Y^β] ([+X^α] ([−Y^β] ([−X^α] (λx:★. (λy:★. x)) ⟨id(★) → (id(★) → id(★))⟩) ⟨id(★) → (id(★) → id(★))⟩)⟨X! → (Y! → X?ℓ0)⟩^[X:★∼X, Y:★∼X] ⟨−X → (id(Y) → +X)⟩) ⟨id(★) → (−Y → id(★))⟩)⟨id(★) → (id(★) → id(★))⟩^[]
⟶ (Merge)
  ([+Y^β] ([+X^α] ([−Y^β, −X^α] (λx:★. (λy:★. x)) ⟨id(★) → (id(★) → id(★))⟩)⟨X! → (Y! → X?ℓ0)⟩^[X:★∼X, Y:★∼X] ⟨−X → (id(Y) → +X)⟩) ⟨id(★) → (−Y → id(★))⟩)⟨id(★) → (id(★) → id(★))⟩^[]
⟶ (Merge)
  ([+Y^β, +X^α] ([−Y^β, −X^α] (λx:★. (λy:★. x)) ⟨id(★) → (id(★) → id(★))⟩)⟨X! → (Y! → X?ℓ0)⟩^[X:★∼X, Y:★∼X] ⟨−X → (−Y → +X)⟩)⟨id(★) → (id(★) → id(★))⟩^[]
```

The second InstX goes through the first boundary (`inst-⟪⟫`) and its
gen layer (`inst-gen`).  So the second boundary `+Y^β` is born outside
`+X^α`.  With one cast the two Merge; with two casts the `∀`-cast
`⟨id(★) → (id(Y) → id(★))⟩` stays between them.  The run of `R`:

```
  (λx:★. (λy:★. x))⟨gen X. (gen Y. (X! → (Y! → X?ℓ0)))⟩^[]⟨inst Z. (∀X′. (Z?ℓ0 → (id(X′) → Z!)))⟩^[]⟨inst Y′. (id(★) → (Y′?ℓ0 → id(★)))⟩^[]
⟶ (Inst)
  (ν X:=★. ((λx:★. (λy:★. x))⟨gen Y. (gen Z. (Y! → (Z! → Y?ℓ0)))⟩^[] X) ⟨∀Y. (−X → (id(Y) → +X))⟩)⟨∀X′. (id(★) → (id(X′) → id(★)))⟩^[]⟨inst Y′. (id(★) → (Y′?ℓ0 → id(★)))⟩^[]
⟶ (TyBeta, ⊣ α:=★)
  ([+X^α] ([−X^α] (λx:★. (λy:★. x)) ⟨id(★) → (id(★) → id(★))⟩)⟨gen Y. (X! → (Y! → X?ℓ0))⟩^[X:★∼X] ⟨∀Y. (−X → (id(Y) → +X))⟩)⟨∀Z. (id(★) → (id(Z) → id(★)))⟩^[]⟨inst X′. (id(★) → (X′?ℓ0 → id(★)))⟩^[]
⟶ (Inst)
  (ν Y:=★. (([+X^α] ([−X^α] (λx:★. (λy:★. x)) ⟨id(★) → (id(★) → id(★))⟩)⟨gen Z. (X! → (Z! → X?ℓ0))⟩^[X:★∼X] ⟨∀Y. (−X → (id(Y) → +X))⟩)⟨∀X′. (id(★) → (id(X′) → id(★)))⟩^[] Y) ⟨id(★) → (−Y → id(★))⟩)⟨id(★) → (id(★) → id(★))⟩^[]
⟶ (TyBeta, ⊣ β:=★)
  ([+Y^β] ([+X^α] ([−Y^β] ([−X^α] (λx:★. (λy:★. x)) ⟨id(★) → (id(★) → id(★))⟩) ⟨id(★) → (id(★) → id(★))⟩)⟨X! → (Y! → X?ℓ0)⟩^[X:★∼X, Y:★∼X] ⟨−X → (id(Y) → +X)⟩)⟨id(★) → (id(Y) → id(★))⟩^[Y:X∼X] ⟨id(★) → (−Y → id(★))⟩)⟨id(★) → (id(★) → id(★))⟩^[]
⟶ (Merge)
  ([+Y^β] ([+X^α] ([−Y^β, −X^α] (λx:★. (λy:★. x)) ⟨id(★) → (id(★) → id(★))⟩)⟨X! → (Y! → X?ℓ0)⟩^[X:★∼X, Y:★∼X] ⟨−X → (id(Y) → +X)⟩)⟨id(★) → (id(Y) → id(★))⟩^[Y:X∼X] ⟨id(★) → (−Y → id(★))⟩)⟨id(★) → (id(★) → id(★))⟩^[]
```

These are the only orders the right can produce.  The first Inst always
opens the outer binder X.  The second goes through the first boundary,
so `+Y^β` is outside `+X^α` (argued from `InstX`).

**G2m (Merge) is unrelated** (`G2m.g2m-unrelated`).  Inside the merged
boundary the index forces both names to be pending, X then Y.  Then
none of the three rules for the left gen cast applies:

- `cast⊑cast` needs `πʷ = []`;
- `cc-gen` pops exactly one name (`no-cc2`);
- `⊑cast` of `X! → (Y! → X?)` grants only α (its `X?`); its premise
  needs `Y ⊑ ★`, and β is not permitted (`gC.noY`).

**G2 (two casts) is unrelated** (`G2.g2-unrelated`).  The proof stops
at the OUTER boundary `+Y^β`.  Its interior has one right name, Y, and
type `★ → Y → ★`.  The index of the left's `∀X.∀Y.X→Y→X` (`no-K2-★`):

- with nothing pending, it puts the left's bound Y against Y;
- with `[Y]` pending, it opens X at Y, and the left's bound Y meets Y;
- with two names pending (both Y), the left's X meets ★ at a name the
  right sees, which needs a permission.

So the left must open its INNER ∀ at Y and leave the outer one waiting.
Pending names cannot say that.  This is PushOrder §2's diagnosis, now
for gen binders.  The peeled left `λx:★.λy:★.x` fails there too
(`★ ⊑ Y`).

**G2's intermediate states.**  State 2 (after the first Inst and TyBeta)
is unrelated (`G2st.g2-st2-unrelated`).  Inside `+X^α` the left opens X.
The right's `gen Y. (X! → …)` cast grants nothing, and `cc-gen`'s
premise puts `★→★→★` against `∀Y.X→Y→X`.  State 4 is unrelated by the
same walk as the final pair (`G2st.G2W`, generic in the inner term).
States 1 and 3 are ν-terms that no rule relates to a left non-ν, as in
P3, K and H1.

### HRm and HR: a gen under a ∀, over a Λ

Sources (RELATED, as for G2m/G2):

```
L:    (ΛX.λx:X.λy:★.x : ∀X.∀Y.X→Y→X)
Rm:   ((ΛX.λx:X.λy:★.x : ∀X.∀Y.X→Y→X) : ★→★→★)
R:    (((ΛX.λx:X.λy:★.x : ∀X.∀Y.X→Y→X) : ∀Y.★→Y→★) : ★→★→★)
```

The initial cast terms are related (`HRm.init`, `HR.init`).  The left
value is

```
(ΛX. (λx:X. (λy:★. x)))⟨∀Y. (gen Z. (id(Y) → (Z! → id(Y))))⟩^[]
```

The run of `Rm`:

```
  (ΛX. (λx:X. (λy:★. x)))⟨∀Y. (gen Z. (id(Y) → (Z! → id(Y))))⟩^[]⟨inst X′. (inst Y′. (X′?ℓ0 → (Y′?ℓ0 → X′!)))⟩^[]
⟶ (Inst)
  (ν X:=★. ((ΛY. (λx:Y. (λy:★. x)))⟨∀Z. (gen X′. (id(Z) → (X′! → id(Z))))⟩^[] X) ⟨∀Y. (−X → (id(Y) → +X))⟩)⟨inst Y′. (id(★) → (Y′?ℓ0 → id(★)))⟩^[]
⟶ (TyBeta, ⊣ α:=★)
  ([+X^α] (λx:X. (λy:★. x))⟨gen Y. (id(X) → (Y! → id(X)))⟩^[X:X∼X] ⟨∀Y. (−X → (id(Y) → +X))⟩)⟨inst Z. (id(★) → (Z?ℓ0 → id(★)))⟩^[]
⟶ (Inst)
  (ν Y:=★. (([+X^α] (λx:X. (λy:★. x))⟨gen Z. (id(X) → (Z! → id(X)))⟩^[X:X∼X] ⟨∀Y. (−X → (id(Y) → +X))⟩) Y) ⟨id(★) → (−Y → id(★))⟩)⟨id(★) → (id(★) → id(★))⟩^[]
⟶ (TyBeta, ⊣ β:=★)
  ([+Y^β] ([+X^α] ([−Y^β] (λx:X. (λy:★. x)) ⟨id(X) → (id(★) → id(X))⟩)⟨id(X) → (Y! → id(X))⟩^[X:X∼X, Y:★∼X] ⟨−X → (id(Y) → +X)⟩) ⟨id(★) → (−Y → id(★))⟩)⟨id(★) → (id(★) → id(★))⟩^[]
⟶ (Merge)
  ([+Y^β, +X^α] ([−Y^β] (λx:X. (λy:★. x)) ⟨id(X) → (id(★) → id(X))⟩)⟨id(X) → (Y! → id(X))⟩^[X:X∼X, Y:★∼X] ⟨−X → (−Y → +X)⟩)⟨id(★) → (id(★) → id(★))⟩^[]
```

The run of `R` ends at

```
  ([+Y^β] ([+X^α] ([−Y^β] (λx:X. (λy:★. x)) ⟨id(X) → (id(★) → id(X))⟩)⟨id(X) → (Y! → id(X))⟩^[X:X∼X, Y:★∼X] ⟨−X → (id(Y) → +X)⟩)⟨id(★) → (id(Y) → id(★))⟩^[Y:X∼X] ⟨id(★) → (−Y → id(★))⟩)⟨id(★) → (id(★) → id(★))⟩^[]
```

(with Inst, TyBeta, Inst, TyBeta before it; `HR.HF-end`).

**HRm is unrelated** (`HRm.hrm-unrelated`): O1 again.

- `cc-∀` passes X to the Λ and `cc-gen` pops Y.  But its premise faces
  `∀X.X→★→X` against `X→Y→X`.
- The right's `id(X) → (Y! → id(X))` grants nothing, so `⊑cast` needs
  `Y ⊑ ★`.

**HR is unrelated** (`HR.hr-unrelated`): O2 at `+Y^β`, for the left
value, its Λ, and its λ.

### N2: nested gen casts

Sources (RELATED: the same term with the same inner ascription;
`src-m`, `src-1`, `src-2`):

```
L:    ((λx:★.λy:★.x : ∀Y.★→Y→★) : ∀X.∀Y.X→Y→X)
Rm:   (L : ★→★→★)
R:    ((L : ∀Y.★→Y→★) : ★→★→★)
```

The initial cast terms are related (`N2.init-m`, `N2.init`).  The left
value is

```
(λx:★. (λy:★. x))⟨gen X. (id(★) → (X! → id(★)))⟩^[]⟨gen Y. (∀Z. (Y! → (id(Z) → Y?ℓ0)))⟩^[]
```

The run of `Rm` ends at

```
  ([+Y^β, +X^α] ([−X^α] ([−Y^β] (λx:★. (λy:★. x)) ⟨id(★) → (id(★) → id(★))⟩)⟨id(★) → (Y! → id(★))⟩^[Y:★∼X] ⟨id(★) → (id(Y) → id(★))⟩)⟨X! → (id(Y) → X?ℓ0)⟩^[X:★∼X, Y:X∼X] ⟨−X → (−Y → +X)⟩)⟨id(★) → (id(★) → id(★))⟩^[]
```

The run of `R` ends at

```
  ([+Y^β] ([+X^α] ([−X^α] ([−Y^β] (λx:★. (λy:★. x)) ⟨id(★) → (id(★) → id(★))⟩)⟨id(★) → (Y! → id(★))⟩^[Y:★∼X] ⟨id(★) → (id(Y) → id(★))⟩)⟨X! → (id(Y) → X?ℓ0)⟩^[X:★∼X, Y:X∼X] ⟨−X → (id(Y) → +X)⟩)⟨id(★) → (id(Y) → id(★))⟩^[Y:X∼X] ⟨id(★) → (−Y → id(★))⟩)⟨id(★) → (id(★) → id(★))⟩^[]
```

(`N2.NmF-end`, `N2.NF-end`).

**N2.Merged is unrelated, at any κ** (`N2.Merged.nrm-unrelated`).
Both names must be pending inside the merged boundary.  The outer gen
cast cannot claim two (`no-cc2`).  If the right's `X! → (id(Y) → X?)`
is peeled first, even under its grant, both pending names must continue
through the right's `−X^α`.  Its interior has one name, so two distinct
pending names cannot both be right names there (`nU`).

**N2.TwoCast is unrelated** (`N2.TwoCast.nr-unrelated`).  The proof
uses O2 at `+Y^β`.  The once-peeled left `∀Y.★→Y→★` can open Y there,
but inside `+X^α` it puts ★ against X (`no-KY-var`).

### Λ over gen

`ΛX. ((λx:X.λy:★.x) : ∀Y.X→Y→X)` is a cast-calculus value (`ΛG-⊢`):

```
(ΛX. (λx:X. (λy:★. x))⟨gen Y. (id(X) → (Y! → id(X)))⟩^[X:X∼X])
```

No source program compiles to it.  `⊢Λ`'s value restriction needs a
source value under the Λ, and an ascription is not one.  No reduction
rule creates a Λ.  So it is not an example by the standing rules
(argued).  If it were run, its Λ could claim α (D29), and its gen body
would then meet O1 exactly as in HRm.

## 2. Diagnosis

- **O1 is the gen counterpart of the push type premise.**  The real
  `cc-gen` relates the gen VALUE to the right term at the gen's SOURCE
  type, at the base world.  So the right's cast `p′` (what the right's
  TyBeta left of the gen body) must be peeled first, with the popped
  name at `X ⊑ ★`.  D28 permits a name only under a covariant check of
  it (`Grants`).
  - G1's `X! → X?` checks X.
  - G0's `X! → id(ℕ)`, G2m's Y in `X! → (Y! → X?)` and HRm's
    `id(X) → (Y! → id(X))` check nothing, although no value of that
    type ever flows out (the name occurs only contravariantly).
- **O2 is PushOrder §2 for gen binders.**  claim-rep fixed it for a Λ
  by peeling the Λ above the right boundaries.  A gen binder scopes over
  no left term, so the left context cannot grow, and nothing can be
  claimed.  The claim has to live in the INDEX, as "this left ∀ waits,
  left-only".

## 3. The fix (`module V SkipOK`, a local variant of the relation)

The real relation's 15 rules, with three changes.  The index is
`_⊑ˢ⟨_⟩_` (`OpenImpS`).  At a world with no pending name it is the
plain index, definitionally.

```
  CastClaimG M c (πʷ W) πₚ    W, πₚ ∣ γ ⊢ M ⊑ M′ : B ⊑ B′
  c : B ⇒ A    c′ : B′ ⇒ A′    OkIx (M⟨c⟩) q
  ─────────────────────────────────────────────────── (cast⊑cast, (i))
  W ∣ γ ⊢ M⟨c⟩ ⊑ M′⟨c′⟩ : q
```

```
  CastClaimG M c π πₚ                       CastClaimG M c π πₚ
  ─────────────────────────────── (cg-∀)    ──────────────────────────────── (cg-gen, (ii))
  CastClaimG M (∀X.c) (k·π) (k·πₚ)          CastClaimG M (gen X.c) (k·π) πₚ
```

(`cg-plain` relates `[]` to `[]`; M is a value under `cg-∀`, `cg-gen`.)

```
  OpenImpS μ (c·cs) ρ (∀A) B  =  OpenImpS μ cs (c ⊳ ρ) A B
                              ⊎  (A non-var, X ∈ A,
                                  OpenImpS (X⊑★·μ) (map suc (c·cs)) (ext ρ) A (⇑B))   (iii, skip)
```

```
  SkipOK M    Carried Θ′ π π′    new ⊆ Fresh Θ′    M a value
  ─────────────────────────────────────────────────── (pv-new, (iii))
  PushV Θ′ M π (new ++ π′)
```

- **(i)** `cast⊑cast` is stated at any world, with a claim on its LEFT
  coercion.  A left gen layer pops its name against the right's cast,
  whose types carry the index, so no grant is needed.  This is the
  shape of the left's own instantiation: `inst-gen` turns `V⟨gen X.p⟩`
  into `([−X^α] V⟨id⟩)⟨p⟩`, which is exactly the right's term.
- **(ii)** A gen layer pops one name, and the claim continues into the
  layer below, as `cc-∀` already does.  `gen X. gen Y. p` pops X then Y;
  `gen X. ∀Y. p` pops X and passes Y on (nested gen casts).
- **(iii)** For a left GEN-CAST VALUE only (`SkipOK = GenCastValue`):
  the index may skip a leading left ∀, which then stays left-only at
  X⊑★, as type imprecision's `∀⊑`.  And `⊑⟪⟫` may push new names
  BEFORE carried ones.  Every rule whose world may have pending names
  takes `OkIx M q`: its index has no skip, or its left term may skip.
- `V1 = V (λ _ → ⊥)` has (i) and (ii) only.  `V2 = V GenCastValue` has
  all three.

**G2 in V2** (`Pos2.g2-final`):

```
⊑cast (id(★) → (id(★) → id(★)))           L ⊑ R_F                            ∀X.∀Y.X→Y→X ⊑ ★→★→★
  ⊑⟪⟫ +Y^β, push Y                         L ⊑ (…)⟨id(★) → (id(Y) → id(★))⟩
    index qY: SKIP X (left-only), open Y   X′→Y→X′ ⊑ ★→Y→★
    ⊑cast (id(★) → (id(Y) → id(★)))
      ⊑⟪⟫ +X^α, push X BEFORE carried Y    πʷ = [X, Y]                         X→Y→X ⊑ X→Y→X
        cast⊑cast, cg-gen, cg-gen          L ⊑ (…)⟨X! → (Y! → X?ℓ0)⟩
          ⊑⟪⟫ −Y^β, −X^α (no push)         λx:★.λy:★.x ⊑ [−Y^β, −X^α] (λx:★.λy:★.x)⟨…⟩   ★→★→★ ⊑ ★→★→★
            ƛ⊑ƛ, ƛ⊑ƛ, x⊑x
```

G2m (`Pos.g2m-final`) is the inner part: the merged boundary pushes
`[X, Y]` directly, with no skip.  G0 (`Pos.g0-final`) is the push of X,
then `cast⊑cast` with `cg-gen` against `X! → id(ℕ)`, then `−X^α`.

**HRm and HR** (`Pos.hrm-final`, `Pos2.hr-final`):
`cast⊑cast (cg-∀ (cg-gen))` passes X to the Λ and pops Y.  The Λ pops X
by `claim-pop` (`open1h`).  Then come the right's `−Y^β` and the bodies
at `X ⊑ X`.

**N2** (`N2.InV2.nrm-final`, `nr-final`):
- the outer cast pops X and passes Y on: `cg-gen (cg-∀ cg-plain)`;
- the right's `−X^α` carries Y;
- the inner cast pops Y: `cg-gen cg-plain`.

**G2's states** (`G2st.InV2.g2-st2`, `g2-st4`):
- state 2 pops X with `cg-gen cg-plain`.  The left's inner gen layer
  meets the right's `gen Y. …` through the types
  (`∀Y.X→Y→X ⊑ ∀Y.X→Y→X`);
- state 4 is the final derivation with the unmerged `−Y^β`, `−X^α`.

DGG part 1 holds in V2 for all seven pairs (`DGG1.g0`, `g2m`, `g2`,
`hrm`, `hr`; `N2.DGG1ᴺ.nr`, `nrm`).  Each witness is a run to the
right's value, a well-formed world with `πʷ = []` and `κʷ = []`, and a
V2 derivation.

## 4. Checks

| check | V1 | V2 | Agda |
|---|---|---|---|
| G0, G2m, HRm, N2.Merged final pairs | **derive** | **derive** | `Pos.*` (generic in SkipOK), `N2.InV2.nrm-final` |
| G2, HR final pairs | **unrelated** | **derive** | `InV1.G2ns.g2-unrelated`, `InV1.HRns.hr-unrelated`; `Pos2.*` |
| N2.TwoCast final pair | (as G2, argued) | **derives** | `N2.InV2.nr-final` |
| G2 states 2, 4 | — | **derive** | `G2st.InV2.g2-st2`, `g2-st4` |
| real ⊆ variant | yes | yes | `V.fromReal` |
| H1 (`final`, `final-no-push`), K (`VL⊑RF`, `lk₁⊑rk₄`, `lk₁⊑rk₃`), P3, Ch X0, Cg X0, C2 X0, G1, C12 (X0, B1), L3c (pre, post), L3d (before), P4 (B1–B6) | derive | **derive** | `Corpus.*` (V2) |
| C1, C2, C3, C4, C4g (at κʷ ≡ []), C5 | dead | **dead** | `Dead1.*`, `Dead2.*` |

The dead checks are mechanized.  The left terms of C1–C5 and C4g are
gen-free: no `∀ᵖ` or `genᵖ` cast anywhere (`GenFree`, solved by
normalization).  On a gen-free left term, a variant derivation has no
skip, no new-first push and only plain claims.  `V.Back.back` maps it to
a real derivation, and the real non-derivability results apply.

## 5. What is argued, and what is open

- **Argued.**
  - No right order other than "`+Y^β` outside `+X^α`" (or merged) is
    reachable.
  - Λ over gen comes from no source.
  - N2.TwoCast is also unrelated in V1 (same walk as G2).
  - States 1 and 3 are transient ν-terms.
- **Not checked: (i)–(iii) against the metatheory.**
  - Sim and SimBack need the new cases: a left `TyBeta` catching up
    with a cast⊑cast pop, InstX of a skipped index, and a new-first
    push in `PushInstR` and `RightMergePending`.
  - Whether (i) or (iii) revives some gen-valued counterexample beyond
    C1–C5/C4g.  The dead checks cover only the existing (gen-free)
    counterexamples.
- **Smaller alternatives considered (not mechanized).**
  - O1 alone could instead be fixed by VACUOUS grants plus several
    grants per cast.  A name that never flows out (only contravariant
    occurrences) would count as checked, and `X! → (Y! → X?)` would
    grant α and β at once.  HRm would then need nothing else, but G2m
    still needs (ii).  (i) needs no reasoning about which names flow
    out, and it is what the left's own InstX produces.
  - O2 cannot be fixed by push order alone.  At `+Y^β` only Y exists,
    and the index must still open the inner ∀ (PushOrder's `NoFixA`,
    `NoFixB`, `NoFixS` argue the same for Λ).
  - The principled form of (iii) is PushOrder's (c3): pending REP. VARS,
    whose unnamed entries open left-only.  The skip is its
    index-only shadow, restricted to gen-cast values.
- **Push order and claim-rep.**  The new-first push is needed only when
  something is carried AND something is new.  No corpus push does both
  (PushOrder §3), and it is guarded by `SkipOK`.  claim-rep (D29) is
  unchanged and still needed for Λ binders (H1).

## 6. Names

- **Tools.**
  - Types read off a derivation: `ltyT`, `rtyT`, `ty-cast`, `ct-src`,
    `ct-trg`, `ty-ƛ`, `ty-Λ`, `ty-K★`, `ty-NΛ`, `ty-KΛ`.
  - Indices and pending names: `idxπ`, `idx0`, `idx1`, `pend-all`,
    `pend-name`.
  - Runs: `EndsV`, `final-of`, `runOf`, `vEnd`.
- **Index lemmas.** `dom⇒`, `cod⇒`, `no-mid`, `no-∀mid`, `K2-01`,
  `no-K2-★`, `LeftMid`, `no-lm-cast`, `no-KΛ-cast`, `tp-ci`, `tp-pK`,
  `tp-pH`, `no-cc2`, `ng-cf`, `ng-pH`.
- **Programs.**
  - `GL`, `GR`, `GRm`, `HL`, `HR`, `HRm`, `FL`, `FR`, `NL`, `NR`,
    `NRm`, `ΛG`.
  - Their right pieces: `pK`, `pH`, `cU`, `cXY`, `cUH`, `U2`, `ΘXY`,
    `UK`, `CK`, `UH`, `CH`.
- **Real relation.**
  - Pairs: `G0.*`, `G2m.*`, `G2.*`, `HRm.*`, `HR.*`, `G2st.*`,
    `N2.{TwoCast, Merged}.*`.
  - DGG failures: `G0.not-dgg`, `G2m.not-dgg`, `G2.not-dgg`,
    `HRm.not-dgg`, `HR.not-dgg`, `N2.not-dgg`, `N2.not-dgg-m`.
- **The variant.**
  - Definitions: `OpenImpS`, `_⊑ˢ⟨_⟩_`, `SkipFree`, `toOI`, `fromOI`,
    `fromOIʷ`, `toOIʷ`, `CastClaimG` (`cg-plain`, `cg-∀`, `cg-gen`),
    `ccG`, `GenLayer`, `GenCastValue`, `NoGA`, `GenFree`, `gf-no-gcv`.
  - Inside `V`: `OkIx`, `PushV` (`pv-real`, `pv-new`), `_∣_⊢_⊑ᵛ_∶_`,
    `⊑cast₀ᵛ`, `fromReal`, `Back.{sfOf, back}`.
  - Instances: `V1`, `V2`.
  - Results: `Pos`, `Pos2`, `NoSkipWalk` (`InV1`), `DeadAt` (`Dead1`,
    `Dead2`), `Corpus`, `DGG1`.
- **Worlds.** `Wm`, `intXYW`, `wfm`, `intU2`, `W₁h`, `open1h`, `Wq`,
  `intUH`, `wfq`, `WYg`, `intYg`, `wfYg`, `intXg`, `qm`, `qH`, `qY`
  (the skip), `Wu0`, `intU0`, `wfU0`, `intU1`, `q2`, `N2.intUX`,
  `N2.intUY`.
