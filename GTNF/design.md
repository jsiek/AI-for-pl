# GTNF: a gradual νF — design draft

Status: first draft (2026-10-01).

GTNF is a gradually typed polymorphic lambda calculus whose cast
calculus is **System νF** (`SystemF/agda/strong-rep-nu/`, presented in
`SystemF/agda/strong-rep-nu/paper/main.tex`) extended with **coercions**
for the run-time checks that involve the dynamic type `★`.  The source
language is the one in `GTSFImp/GradualTerms.agda`.

The organizing principle is that the two kinds of run-time mediation stay
**separate sorts**:

| sort | metavariables | job | lives in |
|---|---|---|---|
| conversion | `c, d` (tails `t`, middles `g, h`) | type abstraction: `seal`/`unseal` a name `X` against its representation | `ν X:=A.(L X)⟨c⟩` and boundaries `[δ] M ⟨c⟩` (unchanged from νF) |
| coercion | `p, q, r` | gradual typing: tag into `★`, check out of `★`, and the structural and polymorphic casts | the new cast form `M ⟨p⟩` |

A conversion never contains a coercion and a coercion never contains a
conversion.  (GTSF, GTPLC and PolyBlameI merge the two into one coercion
language; GTSFImp keeps them apart as `_⟨_⟩` versus `_↑_`/`_↓_`, and
GTNF follows GTSFImp in that respect.)  The two sorts meet only in the
reduction rules, and in exactly the following places: the instantiation
rules (`Inst`, and `TyBeta` through `inst_X`) and the two rules
for a `★`-value under a boundary (`IdDyn`, which moves the tag out, and
`TagUntagBad-⟪⟫`, which checks a tag that cannot move out).

Notation.  This document writes variables as names, following the νF
paper.  The Agda will use de Bruijn indices with parallel renaming and
substitution, as `strong-rep-nu` does.  Everything marked **(new)** is
an addition to νF; everything else is νF as in the paper, restated so
that this file is self-contained.  A cast is written `M ⟨p⟩`.
It is told apart from a boundary `[δ] M ⟨c⟩` by the boundary's leading
`[δ]`, and from the conversion slot of `ν X:=A. (L X) ⟨c⟩` by the
enclosing `ν`; the metavariables also differ (`p, q, r` for coercions,
`c, d` for conversions).

Contents

1. Types, representation types, type contexts
2. Conversions
3. Coercions (new)
4. Terms and typing
5. Values
6. Reduction
7. Compilation from the source language
8. Examples
9. Metatheory goals
10. Decisions taken in this draft, and open questions
11. Agda plan
12. Cast-term imprecision `⊢²` (sketch)

------------------------------------------------------------------------

## 1. Types, representation types, type contexts

```
Base types          ι      ::= Int | Bool
Type variables      X, Y, Z
Rep. variables      α, β
Types               A,B,C  ::= X | ι | ★ | A → B | ∀X. A                (★ new)
Rep. types          R, S   ::= α | X | ι | ★ | R → S | ∀X. R            (★ new)
Type contexts       Δ      ::= [] | Δ, α | Δ, α:=R | Δ, X:=α
Ground types (new)  G, H   ::= ι | ★ → ★ | ∀X. ★ | X
```

The ground types are those of GTSFImp (`Types.Ground`): `＇ X`, `‵ ι`,
`★⇒★`, `∀★`.  A type variable is its own ground type, so a value of
type `X` is tagged with the *name* `X` when it is injected into `★`.
§6.4 explains why a name, rather than a representation variable, is
enough to make the tag check well defined.

Well-formed types `Δ ⊢ A` are as in νF, plus `Δ ⊢ ★`:

```
  X:=α ∈ Δ                         Δ ⊢ A   Δ ⊢ B      Δ, α, X:=α ⊢ A
  ────────   ─────   ─────(new)   ──────────────     ──────────────── (X, α ∉ Δ)
  Δ ⊢ X      Δ ⊢ ι   Δ ⊢ ★         Δ ⊢ A → B          Δ ⊢ ∀X. A
```

The representation type of a type, `Δ(A)`, is as in νF, plus
`Δ(★) = ★` **(new)**:

```
  Δ(X)      = α             if X:=α ∈ Δ
  Δ(X)      = X             if X is not bound in Δ
  Δ(ι)      = ι
  Δ(★)      = ★                                             (new)
  Δ(A → B)  = Δ(A) → Δ(B)
  Δ(∀X. A)  = ∀X. (−X(Δ))(A)
```

The derived lookup is unchanged: `X:=A ∈ Δ` means that `X:=α ∈ Δ`,
`α:=R ∈ Δ`, and `Δ(A) = R`.  In particular, if a `ν X:=★` has allocated
`α:=★`, then `X:=★ ∈ Δ`, so `seal X : ★ ⇒ X` and `unseal X : X ⇒ ★` are
well typed.  The gradual instantiation rule `Inst` (§6.3) relies on
this.

Scope changes `δ ::= [] | δ, +X^α | δ, −X^α`, the interior `δ(Δ)`, the
inverse `−δ`, removal `−X(Δ)`, coherence `Δ ⊢ δ`, and the conversion
context `δ⁺(Δ)` are exactly as in the νF paper (Figure "Context
Operations and Scope Changes").  Coherence is what makes tags by name
work; it says that, inside `δ⁺(Δ)`, names and representation variables
are in bijection:

```
  Δ ⊢ δ    X:=α ∉ δ(Δ)    ∀ Y:=β ∈ δ⁺(Δ).  X = Y ⇔ α = β
  ─────────────────────────────────────────────────────
  Δ ⊢ δ, +X^α
```

------------------------------------------------------------------------

## 2. Conversions

The grammar, `Id?`, the smart sequencing `⨾ˢ`, `+X(t)`, the typing
judgment `Δ ⊢ c : A ⇒ B` and the composition `Δ ⊢ c ⨟ d` are those of
νF.  Three additions concern only `★`:

```
  ──────────────────────── (new)        Inert  i ::= id(X) | c → d | ∀X.c
  Δ ⊢ id(★) : ★ ⇒ ★                                | −X | t ; −X           (unchanged)

  Id(★) = id(★)                         (new clause of Id(A))
```

The ν-conversions are those of `strong-rep-nu.Conversion` §4, with one
new clause each for `★`:

```
  reveal_X(Y)      = +X     if X = Y          conceal_X(Y)      = −X     if X = Y
                   = id(Y)  otherwise                           = id(Y)  otherwise
  reveal_X(ι)      = id(ι)                    conceal_X(ι)      = id(ι)
  reveal_X(★)      = id(★)        (new)       conceal_X(★)      = id(★)        (new)
  reveal_X(A → B)  = conceal_X(A) → reveal_X(B)
  conceal_X(A → B) = reveal_X(A) → conceal_X(B)
  reveal_X(∀Y. A)  = ∀Y. reveal_X(A)          conceal_X(∀Y. A)  = ∀Y. conceal_X(A)
```

If `X:=A ∈ Δ`, then `Δ ⊢ reveal_X(C) : C ⇒ C[A/X]`.

`id(★)` is not inert.  A boundary `[δ] (V⟨G!⟩) ⟨id(★)⟩` around a
tagged value is discharged by `IdDyn`, which moves the tag outside,
except when the tag `G` is a name that only the boundary binds.  In that
case the boundary is the only thing that keeps the tag in scope, and the
term is a value (§5, §6.4, Example 4).

------------------------------------------------------------------------

## 3. Coercions (new)

### Grammar

```
Labels       ℓ
Coercions    p, q, r ::= id(A)            identity
                       | G!               tag (inject into ★)
                       | G?ℓ              check a tag (project out of ★)
                       | p → q            function
                       | ∀X. p            under a type binder
                       | inst X. p        instantiate a ∀ at ★ (implicit instantiation)
                       | gen X. p         generalize to a ∀ (implicit generalization)
                       | p ; q            sequencing
                       | bot-elim         ∀X. X ⇒ ∀X. ★
                       | bot-intro ℓ      ∀X. ★ ⇒ ∀X. X  (always blames)
Inert coercions  P ::= G! | p → q | ∀X. p | gen X. p
Modes            m ::= X∼X | X∼★ | ★∼X | ★∼X∼★
Mode envs        μ ::= [] | μ, X:m
Gen-safe         GenSafe(p)  iff  p is  q → r,  ∀X. q,  inst X. q,  or  gen X. q with GenSafe(q)
```

The constructor names follow GTSF's `Coercions.agda` (`id`, `_!`, `_？`,
`_↦_`, `` `∀ ``, `inst`, `gen`, `_︔_`) and GTSFImp's consistency
constructors (`id`, `_!`, `？_`, `_↦_`, `∀ᶜ_`, `inst_`, `gen_`,
`bot-elim`, `bot-intro`).  The modes are GTSFImp's `Var∼`, and a mode
environment is its `Env∼`.
`GenSafe` is GTSFImp's `CastTerms.GenSafe`: the coercion suspended under
a `gen` must not hide a check that ought to run before the polymorphic
value exists.  Compilation always produces gen-safe coercions under
`gen`, by GTSFImp's `gen-safe` lemma (`proof/Consistency.agda`).

`src(p)` and `trg(p)` are computed syntactically (`src(id A) = A`,
`src(G!) = G`, `src(G?ℓ) = ★`, `src(p → q) = trg(p) → src(q)`,
`src(∀X.p) = ∀X.src(p)`, `src(inst X.p) = ∀X.src(p)`,
`src(gen X.p) = src(p)`, `src(p ; q) = src(p)`,
`src(bot-elim) = ∀X. X`, `src(bot-intro ℓ) = ∀X. ★`, and dually for
`trg`).

### Typing `Δ ; μ ⊢ p : A ⇒ B`

Coercion typing carries a **mode environment** `μ`, which gives each
type variable in scope a mode, exactly as GTSFImp's consistency
`μ ⊢ A ∼ B` does (`Consistency.agda`).  The mode of `X` says whether a
coercion may tag a value with `X` and whether it may check a `★`
against `X`:

| mode | `X!` allowed | `X?ℓ` allowed | given to a variable bound by |
|---|---|---|---|
| `X∼X` (strict) | no | no | `∀X. p` (GTSFImp `extᵐ`) |
| `X∼★` | yes | no | `inst X. p` (GTSFImp `instᵐ`) |
| `★∼X` | no | yes | `gen X. p` (GTSFImp `genᵐ`) |
| `★∼X∼★` (cross) | yes | yes | the type context of a source term (GTSFImp `idᶜ`) |

The domain of a function coercion is typed under `flip(μ)`, which swaps
`X∼★` and `★∼X` and leaves the other two modes alone (GTSFImp `flipᵐ`).
The side conditions on `inst` and `gen` are GTSFImp's.

```
  Δ ⊢ A                         Δ ⊢ G   G ≠ X                Δ ⊢ G   G ≠ X
  ──────────────────────        ──────────────────           ────────────────────
  Δ ; μ ⊢ id(A) : A ⇒ A         Δ ; μ ⊢ G! : G ⇒ ★           Δ ; μ ⊢ G?ℓ : ★ ⇒ G

  Δ ⊢ X   μ(X) ∈ {X∼★, ★∼X∼★}         Δ ⊢ X   μ(X) ∈ {★∼X, ★∼X∼★}
  ───────────────────────────          ───────────────────────────
  Δ ; μ ⊢ X! : X ⇒ ★                   Δ ; μ ⊢ X?ℓ : ★ ⇒ X

  Δ ; flip(μ) ⊢ p : A′ ⇒ A    Δ ; μ ⊢ q : B ⇒ B′
  ─────────────────────────────────────────────
  Δ ; μ ⊢ p → q : A → B ⇒ A′ → B′

  Δ, α, X:=α ; μ, X:X∼X ⊢ p : A ⇒ B
  ─────────────────────────────────────── (X, α ∉ Δ)
  Δ ; μ ⊢ ∀X. p : ∀X. A ⇒ ∀X. B

  Δ, α, X:=α ; μ, X:X∼★ ⊢ p : A ⇒ B    Δ ⊢ B    A not a variable    X ∈ A    B ≠ ★
  ──────────────────────────────────────────────────────────────────────────────── (X, α ∉ Δ)
  Δ ; μ ⊢ inst X. p : ∀X. A ⇒ B

  Δ, α, X:=α ; μ, X:★∼X ⊢ p : A ⇒ B    Δ ⊢ A    B not a variable    X ∈ B    A ≠ ★
  GenSafe(p)
  ──────────────────────────────────────────────────────────────────────────────── (X, α ∉ Δ)
  Δ ; μ ⊢ gen X. p : A ⇒ ∀X. B

  Δ ; μ ⊢ p : A ⇒ B    Δ ; μ ⊢ q : B ⇒ C
  ──────────────────────────────────────
  Δ ; μ ⊢ p ; q : A ⇒ C

  ─────────────────────────────────          ───────────────────────────────────
  Δ ; μ ⊢ bot-elim : ∀X. X ⇒ ∀X. ★           Δ ; μ ⊢ bot-intro ℓ : ∀X. ★ ⇒ ∀X. X
```

**Why modes are in the cast calculus.**  An earlier draft left modes to
the source language.  Two properties need them in the cast calculus:

- **No value has type `∀X. X`.**  In GTSFImp this is the machine-checked
  lemma `no-bot-value` (`proof/TypeSafety/Progress.agda`).  It goes
  through a `∀` cast because the cast's bound variable is strict
  (`X∼X`), so `consistency-to-fresh` forces the value under the cast to
  have type `∀X. X` as well.  Without modes, `V ⟨∀X. X?ℓ⟩` would be a
  value of type `∀X. X` for any `V : ∀X. ★`.  It is also why
  `bot-elim` and `bot-intro` need their own constructors.  `∀X. X!` and
  `∀X. X?ℓ` are ill typed, because `X` is strict.
- **The dynamic gradual guarantee.**  GTSFImp's DGG closes its
  `bot-elim` and `bot-intro` cells with `no-bot-value`
  (`proof/DGG/Catchup/ExtraCastRightAtProof.agda`;
  `proof/DGG/notes/LG3TargetCastStepInversionCaseTable.md`).  More
  generally, the DGG relates cast terms whose casts obey the same
  modes as source consistency.

**Modes at a cast.**  A cast carries its mode environment as part of
the term, written `M ⟨p⟩^μ` when the environment matters and `M ⟨p⟩`
otherwise.  This follows GTSFImp's `CastTerms`, whose cast constructor
is `_⟨_⟩ : Term Δ → {μ : Env∼ Δ} … (c : μ ⊢ A ∼ B) → Term Δ`: the `μ`
is part of the cast's evidence, so a term determines it.  Compilation
creates every cast at the environment that gives each name in scope
`★∼X∼★`, matching the source's `A ∼ B = idᶜ ⊢ A ∼ B`.  Reduction then
**keeps and extends** each cast's environment, and it never replaces it
by the cross environment:

- When an instantiation rule moves a coercion out from under its binder,
  the freed name keeps the binder's mode.  `TyBeta`'s
  `inst_X(W ⟨gen X.p⟩^μ) = ([−X^α] W ⟨Id(A)⟩) ⟨p⟩^(μ, X:★∼X)` and
  `inst_X(W ⟨∀X.p⟩^μ) = inst_X(W) ⟨p⟩^(μ, X:X∼X)`.  The modes are
  those of GTSFImp's `β-gen`, whose contractum is `⇑ᵗᵐ V ⟨ c ⟩` with
  `c` under `genᵐ μ`, and of the analogous `β-∀`.  GTNF differs from
  GTSFImp in not shifting `V` (§6.2).
- `CastFun` casts the argument at `flip(μ)`, because the domain
  coercion was typed there.  This is GTSFImp's `β-⇒`, whose argument
  cast `c` has type `flipᵐ μ ⊢ A′ ∼ A`.
- `CastSeq` keeps `μ` for both halves, and `Inst` closes `X` at `★`, so
  its result cast is at `μ`.
- `IdDyn` moves a tag cast from a boundary's interior to its exterior.
  The moved cast keeps the interior mode of every exterior name the
  interior can see.  It gives `X∼X` to every exterior name that the
  interior cannot see, because the cast has never seen that name
  (`exit_δ(μ)`, §6.3; Example 7).  This is what GTSFImp does when a
  cast first meets a variable: at an allocation, `ξ-⟨⟩` re-indexes the
  cast's environment by `applyEnv (bind A) μ = extᵐ μ`, which gives the
  new variable `X∼X`.  The filled-in mode never belongs to a name that
  the coercion mentions.  If the tag were that name, then the name
  would be visible in the interior and its mode would be copied.  So
  the choice does not affect typing or reduction; it is bookkeeping for
  the cast-term imprecision (§9.6).

The modes of free names are therefore data that the dynamic semantics
carries along.  The cast-term imprecision relates casts with possibly
different environments on its two sides, as GTSFImp's `cast⊑cast²`
does (`ν ⊢ C ∼ A`, `ν′ ⊢ C′ ∼ A′`).

A coercion's typing does not depend on whether a representation
variable is abstract (`α`) or bound (`α:=R`).  Instantiation rules use
this fact when they move a coercion typed under a `Λ`'s `α` to a
context where `α:=R` has been allocated.

### Closing at ★: `p[★/X]`

`Inst` instantiates at `★` and then closes the coercion at `★`, as in
GTSFImp's `β-inst` (`c [ ★/0 ]ᶜ`; Rationale.md, "Instantiation closes
consistency at star"):

```
  id(A)[★/X]      = id(A[★/X])
  (X!)[★/X]       = id(★)          (G!)[★/X]  = G!    if G ≠ X
  (X?ℓ)[★/X]      = id(★)          (G?ℓ)[★/X] = G?ℓ   if G ≠ X
  (p → q)[★/X]    = p[★/X] → q[★/X]
  (∀Y. p)[★/X]    = ∀Y. p[★/X]          (inst Y. p)[★/X] = inst Y. p[★/X]
  (gen Y. p)[★/X] = gen Y. p[★/X]       (p ; q)[★/X]     = p[★/X] ; q[★/X]
  bot-elim[★/X]   = bot-elim            (bot-intro ℓ)[★/X] = bot-intro ℓ
```

If `Δ, α, X:=α ; μ, X:m ⊢ p : A ⇒ B` for any mode `m`, then
`Δ ; μ ⊢ p[★/X] : A[★/X] ⇒ B[★/X]`.  `Inst` uses the lemma at
`m = X∼★`.  The lemma is stated for every `m` because a function
coercion's domain flips `X∼★` to `★∼X`.

------------------------------------------------------------------------

## 4. Terms and typing

```
Variables    x, y
Constants    k   ::= 0 | 1 | … | true | false
Operators    op  ::= + | ∧ | …
Terms        L, M, N ::= k | op(M⃗) | x | λx:A. N | L M
                       | ΛX. V
                       | ν X:=A. (L X) ⟨c⟩
                       | [δ] M ⟨c⟩
                       | M ⟨p⟩                              (new) cast
                       | blame ℓ                              (new)
Term contexts  Γ ::= [] | Γ, x:A
```

The νF rules are unchanged (constants, operators, variables, `λ`,
application, value-restricted `Λ`, `⊢ν`, boundary):

```
  Δ, α, X:=α ∣ Γ ⊢ V : A
  ──────────────────────────
  Δ ∣ Γ ⊢ ΛX. V : ∀X. A

  Δ ⊢ A    Δ ∣ Γ ⊢ L : ∀X. C    Δ, α:=Δ(A), X:=α ⊢ c : C ⇒ B    Δ ⊢ B
  ──────────────────────────────────────────────────────────────────────
  Δ ∣ Γ ⊢ ν X:=A. (L X) ⟨c⟩ : B

  Δ ⊢ δ    δ(Δ) ∣ [] ⊢ M : A    δ⁺(Δ) ⊢ c : A ⇒ B    Δ ⊢ B
  ─────────────────────────────────────────────────────────
  Δ ∣ Γ ⊢ [δ] M ⟨c⟩ : B
```

New rules:

```
  Δ ∣ Γ ⊢ M : A    Δ ; μ ⊢ p : A ⇒ B            Δ ⊢ A
  ──────────────────────────────── (new)        ───────────────────── (new)
  Δ ∣ Γ ⊢ M ⟨p⟩^μ : B                          Δ ∣ Γ ⊢ blame ℓ : A
```

------------------------------------------------------------------------

## 5. Values

```
Simples   U ::= k | λx:A. N | ΛX. V | V ⟨P⟩            (V⟨P⟩ new)
Values    V, W ::= U | [δ] U ⟨i⟩
                 | [δ] (V ⟨X!⟩) ⟨id(★)⟩      if X ∈ fresh(δ)          (new)

fresh(δ) = { X | the first entry of δ that mentions X is +X^α }
```

**The new value form** is a `★`-value under a boundary whose tag names
a variable introduced by the boundary itself.  `IdDyn` (§6.3) moves the
tag out of every other boundary around a tagged value, so this is the
only boundary that can remain around a `★`-value.

`fresh(δ)` gives a syntactic form of `IdDyn`'s side condition `Δ ⊢ G`.  If
`Δ ⊢ δ` and `δ(Δ) ⊢ X`, then

```
Δ ⊢ X    if and only if    X ∉ fresh(δ)
```

Proof sketch: suppose that `X ∈ fresh(δ)` and that `X:=β ∈ Δ`.  Before
the first `X`-entry the interior still contains `X:=β`.  Coherence of
that first entry `+X^α` (`X = Y ⇔ α = β` on `δ⁺(Δ) ∋ X:=β`) forces
`α = β`, so `X:=α` is already in the interior, contradicting the premise
`X:=α ∉ δ(Δ)` of `+X^α`.  Conversely, suppose that `X ∉ Δ`.  Then `X`
is in `δ(Δ)` only because some entry `+X^α` added it, and the first
`X`-entry cannot be `−X^α`, because that entry requires `X` in the
interior.

Using `fresh(δ)` rather than `Δ ⊢ X` keeps `Value` a predicate on terms
alone, not indexed by the type context, as it is in νF.  This matters
because a congruence step carries values to other contexts.  The
syntactic form makes it immediate that a value stays a value under
allocation and under weakening by fresh names.

The one structural change to νF is that **a value with an inert cast
counts as a simple**.  Every boundary rule of νF is stated for a simple
interior: `Wrap` crosses `[δ] U ⟨c → d⟩`, `TyBeta` crosses
`[δ] U ⟨∀X. c⟩` (νF's `TyWrap`), `Merge` fuses
`[δ₂]([δ₁] U ⟨t₁⟩)⟨c⟩`, and `Id` drops `[δ] U ⟨id(ι)⟩`.  With this change those rules also apply when the
interior is a cast value.  The rules never look inside `U`, so the
change costs nothing in them.  The boundary invariant of νF, "at most
one boundary directly around a simple", is unaffected.  A cast value may
contain boundaries *inside* its `V`, just as `λx:A. N` may contain them
inside `N`.

The modes give GTSFImp's emptiness lemma, which the progress and DGG
proofs use (§3):

```
no-bot-value :  if V is a value, then not (Δ ∣ Γ ⊢ V : ∀X. X)
```

The proof goes by cases on `V`.  A `Λ` would need a body value of type
`X` under an abstract `α`, and there is none.  For `W ⟨∀X. p⟩`, `p` is
strict in `X`, so `p : A ⇒ X` forces `A = X`, and `W` has type `∀X. X`.
`W ⟨gen X. p⟩` has the target type `∀X. B` with `B` not a variable.  For the
boundary `[δ] U ⟨∀X. c⟩`, the conversion `c : A′ ⇒ X` is typed with
`X:=α` for an abstract `α`.  Sealing needs a representation, so `c` can
only be `id(X)`, and then `U` has type `∀X. X`.  These cases need
checking when the Agda exists.

Canonical forms, by type:

| type | values |
|---|---|
| `ι` | `k` |
| `A → B` | `λx:A.N`, `V⟨p → q⟩`, `[δ] U ⟨c → d⟩` |
| `∀X. A` | `ΛX.V`, `V⟨∀X.p⟩`, `V⟨gen X.p⟩`, `[δ] U ⟨∀X. c⟩` |
| `★` | `V⟨G!⟩`, `[δ] (V⟨X!⟩) ⟨id(★)⟩` with `X ∈ fresh(δ)` |
| `X` | `[δ] U ⟨−X⟩`, `[δ] U ⟨t ; −X⟩` (as in νF; `U` may now be a `★`-value when `X:=★`) |

------------------------------------------------------------------------

## 6. Reduction

`Δ ⊢ M ⟶ N ⊣ ξ`, where `ξ ::= ε | α:=R` is the allocation the step made
(as in νF).

### 6.1 Frames

```
F ::= □ M | V □ | op(V⃗, □, M⃗)
    | ν X:=A. (□ X) ⟨c⟩
    | [δ] □ ⟨c⟩
    | □ ⟨p⟩                                   (new)

(□ M)(Δ) = (V □)(Δ) = (op(V⃗,□,M⃗))(Δ) = (ν X:=A.(□ X)⟨c⟩)(Δ) = Δ
([δ] □ ⟨c⟩)(Δ) = δ(Δ)
(□ ⟨p⟩)(Δ) = Δ                                (new)
```

### 6.2 The νF rules

`Delta`, `Beta`, `Wrap`, `Merge`, `Id` and `ξ` are verbatim from νF,
except that `Merge`'s inner boundary may now also be the new value form
`[δ₁] (V⟨X!⟩) ⟨id(★)⟩` (`t₁ = id(★)`).  The merged boundary may no
longer introduce `X`, in which case `IdDyn` fires next (Example 5).
`TyBeta` is generalized from a `Λ` to any ∀-value, through a
meta-operation `inst_X(V)` that instantiates a ∀-value `V` at the name
`X` by reaching through all of its layers:

```
inst_X(ΛX. V)            = V
inst_X(W ⟨gen X. p⟩^μ)   = ([−X^α] W ⟨Id(A)⟩) ⟨p⟩^(μ, X:★∼X)     (W : A)
inst_X(W ⟨∀X. p⟩^μ)      = inst_X(W) ⟨p⟩^(μ, X:X∼X)
inst_X([δ] U ⟨∀X. c⟩)    = [δ] inst_X(U) ⟨c⟩          (X not mentioned by δ)
```

Here `α` is the representation variable that `TyBeta` allocates for
`X`, so `inst_X` is really `inst_X^α`.

**No term moves under a new name.**  In the `gen` case, `W` was typed
outside `X`'s scope, and only `p` mentions `X`.  Placing `W` directly
in the interior `Δ, X:=α` would need a weakening, so `W` is put under
the binder's dual `[−X^α]` instead.  Its interior is
`−X(Δ, X:=α) = Δ`, which is exactly where `W` was typed, and its
conversion `Id(A)` is typed in `(−X^α)⁺(Δ, X:=α) = Δ, X:=α`.  So `W`
keeps its scope ("colour") and needs no weakening, either in the Agda
(no de Bruijn shift) or in a preservation proof with names (Jeremy,
2026-10-01).  This is νF's `crossΛᴹ`, the wrapper Beta puts on a value
that crosses a `Λ`.  It costs extra steps: Example 2 takes 12 steps
rather than 8, because the wrapper is crossed by `Wrap` and later
fused by `Merge`.  In the `Λ` and `∀X.p` cases nothing moves under the
new name: the `Λ` body and `p` were already typed under a binder for
`X`.

These four clauses cover every canonical ∀-value (§5).  The recursion
is on the structure of the value, and each layer of the value becomes
one layer of the result: a cast stays a cast, and a boundary stays a
boundary.  So `inst_X` stacks boundaries, as νF's `TyWrap` does, and
`Merge` fuses them afterwards.  `inst_X` allocates nothing; the one
allocation `α:=Δ(A)` is made by `TyBeta` itself, however many layers
the value has.  (Under the name `inst_X`, the meta-operation is not to
be confused with the coercion `inst X. p` and its rule `Inst`.)

```
Δ ⊢ op(k⃗) ⟶ ⟦op⟧(k⃗) ⊣ ε                                              (Delta)

Δ ⊢ (λx:A. N) V ⟶ N[x:=V] ⊣ ε                                          (Beta)

Δ ⊢ ([δ] U ⟨c → d⟩) W ⟶ [δ] (U ([−δ] W ⟨c⟩)) ⟨d⟩ ⊣ ε                    (Wrap)

Δ ⊢ ν X:=A. (V X) ⟨d⟩ ⟶ [+X^α] inst_X(V) ⟨d⟩ ⊣ α:=Δ(A)                  (TyBeta)
      V a ∀-value; α fresh

Δ ⊢ [δ₂] ([δ₁] U ⟨t₁⟩) ⟨c₁⟩ ⟶ [δ₂ ++ δ₁] U ⟨d⟩ ⊣ ε                      (Merge)
      where [δ₁] U ⟨t₁⟩ is a value and (δ₂ ++ δ₁)⁺(Δ) ⊢ t₁ ⨟ c₁ = d

Δ ⊢ [δ] U ⟨id(ι)⟩ ⟶ U ⊣ ε                                              (Id)

Δ ⊢ F[M] ⟶ F[M′] ⊣ ξ     if  F(Δ) ⊢ M ⟶ M′ ⊣ ξ                        (ξ)
```

νF's two rules are instances of this `TyBeta`.  If `V = ΛX.N`, then it
is νF's `TyBeta`.  If `V = [δ] (ΛX.N) ⟨∀X.c⟩`, then it is νF's
`TyWrap`.  The `gen` case is GTSFImp's `β-gen` with a boundary in place
of `↑ 〖 0 , ⇑ᵗ C ↑ B 〗`.  The `∀X.p` case is GTSFImp's `β-∀`: the
value under the cast is instantiated, with no further allocation, and
then cast.  When the Agda is written, `inst_X` may be a function on
value derivations, or `TyBeta` may be split into one constructor per
outermost layer; this draft states it once.

Preservation of `TyBeta` rests on one lemma, proved by induction on the
∀-value:

```
if  Δ ∣ [] ⊢ V : ∀X. C,  V a ∀-value,  and  α:=R ∈ Δ  with  X, α fresh,
then  Δ, X:=α ∣ [] ⊢ inst_X(V) : C
```

The `Λ` case re-reads the body, typed under an abstract `α`, at the
allocated `α:=R`, as νF's `TyBeta` does.  The `gen X.p` and `∀X.p`
cases use the fact that coercion typing does not depend on whether `α`
is abstract or bound (§3).  The `gen` case types `[−X^α] W ⟨Id(A)⟩`
with the boundary rule, and `W` is used at exactly its own typing
`Δ ∣ [] ⊢ W : A`, so no weakening lemma is needed.  In the boundary case, `δ` stays coherent at
`Δ, X:=α`, because `X` and `α` are fresh.  Its interior is then
`δ(Δ), X:=α`, and `c` is typed in `δ⁺(Δ), X:=α`.

### 6.3 Cast rules (new)

```
Δ ⊢ V ⟨id(A)⟩ ⟶ V ⊣ ε                                                 (CastId)

Δ ⊢ V ⟨p ; q⟩^μ ⟶ V ⟨p⟩^μ ⟨q⟩^μ ⊣ ε                                 (CastSeq)

Δ ⊢ (V ⟨p → q⟩^μ) W ⟶ (V (W ⟨p⟩^flip(μ))) ⟨q⟩^μ ⊣ ε                 (CastFun)

Δ ⊢ V ⟨inst X. p⟩^μ ⟶ (ν X:=★. (V X) ⟨reveal_X(src(p))⟩) ⟨p[★/X]⟩^μ ⊣ ε   (Inst)

Δ ⊢ V ⟨G!⟩ ⟨G?ℓ⟩ ⟶ V ⊣ ε                                              (TagUntag)

Δ ⊢ V ⟨G!⟩ ⟨H?ℓ⟩ ⟶ blame ℓ ⊣ ε        if G ≠ H                         (TagUntagBad)

Δ ⊢ [δ] (V ⟨G!⟩^μ) ⟨id(★)⟩ ⟶ ([δ] V ⟨Id(G)⟩) ⟨G!⟩^exit_δ(μ) ⊣ ε        (IdDyn)
      if G ∉ fresh(δ)            (equivalently, on well-typed terms, Δ ⊢ G)

exit_δ(μ)(Y) = μ(Y)    if Y is visible in the interior δ(Δ)
             = X∼X     otherwise

Δ ⊢ ([δ] (V ⟨X!⟩) ⟨id(★)⟩) ⟨H?ℓ⟩ ⟶ blame ℓ ⊣ ε     if X ∈ fresh(δ)     (TagUntagBad-⟪⟫)

Δ ⊢ V ⟨bot-intro ℓ⟩ ⟶ blame ℓ ⊣ ε                                      (BlameBotIntro)

Δ ⊢ F[blame ℓ] ⟶ blame ℓ ⊣ ε                                            (Blame)
```

These rules correspond to GTSFImp's `β-id`, `β-⇒`, `β-inst`,
`tag-untag`, `tag-untag-bad` and `blame-bot-intro`.  No rule applies
`bot-elim` to a value, because no value has type `∀X. X` (§5); progress
dismisses that case, as GTSFImp's `cast-value-progress` does.  GTSFImp's `ground` and `expand` are
not needed, because a tag through a non-ground type is the sequence
`p ; G!` and `CastSeq` splits it.  GTSFImp's `β-∀` is the
`∀X.p` case of `inst_X` (§6.2), because GTNF instantiates by `ν` and not
by a `⦂∀ B [ C ]` type application.

`Inst` does not allocate by itself.  The `ν X:=★` it creates allocates
`α:=★` on the next step, by `TyBeta`.  Inside the resulting
boundary, `X:=★` holds, so `reveal_X(src(p))` seals and unseals `X`
against `★`.  The coercion has already been closed at `★`: each `X!`
and `X?ℓ` in `p` has become `id(★)`.  As in GTSFImp, the `inst`-bound
variable is therefore implemented entirely by conversions, and no tag
names it.

### 6.4 Why a tag by name keeps its meaning across a boundary

`IdDyn` moves a tag `G` from the interior `δ(Δ)` to the exterior `Δ`
without changing it.  If `G` is a name `X`, then this is sound because
of coherence: `X:=α ∈ δ(Δ) ⊆ δ⁺(Δ)` and `X:=β ∈ Δ ⊆ δ⁺(Δ)`, and
coherence (`X = Y ⇔ α = β` on `δ⁺(Δ)`) forces `α = β`.  So the two
occurrences of `X` denote the same representation variable, even if `δ`
removed `X` (`−X^α`) and later rebound it (`+X^α`).  After the tag is
outside, the ordinary `TagUntag`/`TagUntagBad` compare it with a check
`H` by **syntactic equality**.

If the tag's name is in `fresh(δ)`, then the tag cannot move out, and no
check `H` that is well formed in `Δ` can be equal to it.  So
`TagUntagBad-⟪⟫` blames unconditionally.  This is the "escaping seal"
behaviour of GTSFImp and of λB (Example 4).  The successful check across
a boundary, which an earlier draft had as `TagUntag-⟪⟫`, can no longer
arise: if the tag is visible outside, then `IdDyn` has already moved it.

`IdDyn`'s contractum `[δ] V ⟨Id(G)⟩` keeps the boundary, because `V`
was typed in the interior.  If `G = ι`, then `Id` removes the boundary
on the next step.  If `G = ★ → ★` or `G = ∀X.★`, then the boundary is
an inert `c → d` or `∀X.c` over `V`, and if `V` is itself a boundary
value, then `Merge` fuses the two.  If `G = X`, then the boundary is
`[δ] V ⟨id(X)⟩`, an inert boundary over a value of type `X`.

------------------------------------------------------------------------

## 7. Compilation from the source language

The source is `GTSFImp/GradualTerms.agda`, unchanged:
`x | λx:A. M | L ·[ℓ] M | ΛX. M | M [A] | k | L ⊕[op at ℓ] M`, typed by
`⊢` `⊢ƛ` `⊢·` `⊢·★` `⊢Λ` `⊢•` `⊢$` `⊢⊕`, with GTSFImp's consistency
`A ∼ B = idᶜ ⊢ A ∼ B` (`Consistency.agda`).  `⊢Λ` keeps its value
restriction and its `zero ∈ᵗ A` premise.

As in νF's `Compile.agda`, compilation is defined on typing derivations.
Consistency evidence compiles to a coercion `⟦c⟧ℓ`, where `ℓ` is the
label of the enclosing application or operator:

```
⟦id A⟧ℓ        = id(A)
⟦c ↦ d⟧ℓ       = ⟦c⟧ℓ → ⟦d⟧ℓ
⟦∀ᶜ c⟧ℓ        = ∀X. ⟦c⟧ℓ
⟦(id G) !⟧ℓ    = G!                 ⟦c !⟧ℓ   = ⟦c⟧ℓ ; G!       (c : A ∼ G, otherwise)
⟦？ (id G)⟧ℓ   = G?ℓ                ⟦？ c⟧ℓ  = G?ℓ ; ⟦c⟧ℓ      (c : G ∼ B, otherwise)
⟦inst c⟧ℓ      = inst X. ⟦c⟧ℓ
⟦gen c⟧ℓ       = gen X. ⟦c⟧ℓ
⟦bot-elim⟧ℓ    = bot-elim
⟦bot-intro⟧ℓ   = bot-intro ℓ
```

Terms (following GTSFImp's `Compile.agda`, which casts the argument by
`symᶜ`):

```
⟦x⟧                     = x
⟦λx:A. M⟧               = λx:A. ⟦M⟧
⟦L ·[ℓ] M⟧  (⊢·, c)      = ⟦L⟧ (⟦M⟧ ⟨⟦symᶜ c⟧ℓ⟩)
⟦L ·[ℓ] M⟧  (⊢·★, c)     = (⟦L⟧ ⟨(★→★)?ℓ⟩) (⟦M⟧ ⟨⟦c⟧ℓ⟩)
⟦ΛX. V⟧                 = ΛX. ⟦V⟧
⟦M [A]⟧     (M : ∀X.C)   = ν X:=A. (⟦M⟧ X) ⟨reveal_X(C)⟩
⟦k⟧                     = k
⟦L ⊕[op at ℓ] M⟧        = op(⟦L⟧ ⟨⟦c₁⟧ℓ⟩, ⟦M⟧ ⟨⟦c₂⟧ℓ⟩)
```

The intended theorem is the analogue of νF's `compile-⊢`: if
`Δ ∣ Γ ⊢ M : A` in the source, then `Δ ∣ Γ ⊢ ⟦M⟧ : A`.  Its proof needs
the fact that `⟦c⟧ℓ` is typed at the endpoints and modes of `c`
(if `μ ⊢ c : A ∼ B`, then `Δ ; μ ⊢ ⟦c⟧ℓ : A ⇒ B`, by induction on `c`,
since each coercion rule mirrors a consistency rule).  It also needs
the fact that `⟦·⟧` maps source values
to values, which needs `⟦gen c⟧ℓ` to be gen-safe and so uses GTSFImp's
`gen-safe`.

------------------------------------------------------------------------

## 8. Examples

The traces omit the identity casts `⟨id(A)⟩` that compilation puts
on arguments whose types already agree.  Each such cast would be removed
by one `CastId` step.

### Example 1 — implicit instantiation at ★

Source: `(λf:★→★. f 5) (ΛX. λx:X. x)`.  The argument's type
`∀X. X→X` is consistent with `★→★` by `inst`, with `X∼★` marking the
fresh variable.  The evidence is `inst ((？ id X) ↦ (id X) !)`, so the
argument's coercion is `inst X. (X?ℓ → X!)`, and
`(X?ℓ → X!)[★/X] = id(★) → id(★)`.  The `5` is cast by `ℕ!`.

```
  (λf:★→★. f (5⟨ℕ!⟩)) ((ΛX. λx:X. x) ⟨inst X. (X?ℓ → X!)⟩)
⟶ (Inst; reveal_X(X→X) = −X → +X)
  (λf:★→★. f (5⟨ℕ!⟩)) ((ν X:=★. ((ΛX. λx:X. x) X) ⟨−X → +X⟩) ⟨id(★) → id(★)⟩)
⟶ (TyBeta, ⊣ α:=★)
  (λf:★→★. f (5⟨ℕ!⟩)) (([+X^α] (λx:X. x) ⟨−X → +X⟩) ⟨id(★) → id(★)⟩)
⟶ (Beta)
  (([+X^α] (λx:X. x) ⟨−X → +X⟩) ⟨id(★) → id(★)⟩) (5⟨ℕ!⟩)
⟶ (CastFun)
  (([+X^α] (λx:X. x) ⟨−X → +X⟩) (5⟨ℕ!⟩⟨id(★)⟩)) ⟨id(★)⟩
⟶ (CastId, under ξ)
  (([+X^α] (λx:X. x) ⟨−X → +X⟩) (5⟨ℕ!⟩)) ⟨id(★)⟩
⟶ (Wrap)
  ([+X^α] ((λx:X. x) ([−X^α] (5⟨ℕ!⟩) ⟨−X⟩)) ⟨+X⟩) ⟨id(★)⟩
⟶ (Beta, under ξ)
  ([+X^α] ([−X^α] (5⟨ℕ!⟩) ⟨−X⟩) ⟨+X⟩) ⟨id(★)⟩
⟶ (Merge; −X ⨟ +X = Id(★) = id(★), because X:=★)
  ([+X^α, −X^α] (5⟨ℕ!⟩) ⟨id(★)⟩) ⟨id(★)⟩
⟶ (IdDyn, under ξ; ℕ ∉ fresh(+X^α, −X^α))
  (([+X^α, −X^α] 5 ⟨id(ℕ)⟩) ⟨ℕ!⟩) ⟨id(★)⟩
⟶ (Id, under ξ)
  5⟨ℕ!⟩⟨id(★)⟩
⟶ (CastId)
  5⟨ℕ!⟩                                               -- a value of type ★
```

The `[+X^α, −X^α]` boundary that the tagged `5` acquired by passing
through the instantiated identity is removed by `IdDyn` and `Id`,
because the tag `ℕ` does not depend on it.

### Example 2 — implicit generalization, used parametrically

Source: `(λg:∀X.X→X. g [ℕ] 5) (λx:★. x)`.  The argument's type `★→★` is
consistent with `∀X.X→X` by `gen`, with `★∼X` marking the fresh
variable, so the coercion is `gen X. (X! → X?ℓ)`.  Write
`I = (λx:★. x) ⟨gen X. (X! → X?ℓ)⟩`, which is a value.

```
  (λg:∀X.X→X. (ν X:=ℕ. (g X) ⟨−X → +X⟩) 5) I
⟶ (Beta)
  (ν X:=ℕ. (I X) ⟨−X → +X⟩) 5
⟶ (TyBeta, with inst_X(I) = ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩) ⟨X! → X?ℓ⟩, ⊣ α:=ℕ)
  ([+X^α] (([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩) ⟨X! → X?ℓ⟩) ⟨−X → +X⟩) 5
⟶ (Wrap)
  [+X^α] ((([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩) ⟨X! → X?ℓ⟩) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩
⟶ (CastFun)
  [+X^α] ((([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩) (([−X^α] 5 ⟨−X⟩) ⟨X!⟩)) ⟨X?ℓ⟩) ⟨+X⟩
⟶ (Wrap, under ξ)
  [+X^α] (([−X^α] ((λx:★. x) ([+X^α] (([−X^α] 5 ⟨−X⟩) ⟨X!⟩) ⟨id(★)⟩)) ⟨id(★)⟩) ⟨X?ℓ⟩) ⟨+X⟩
⟶ (Beta, under ξ)
  [+X^α] (([−X^α] ([+X^α] (([−X^α] 5 ⟨−X⟩) ⟨X!⟩) ⟨id(★)⟩) ⟨id(★)⟩) ⟨X?ℓ⟩) ⟨+X⟩
⟶ (Merge, under ξ)
  [+X^α] (([−X^α, +X^α] (([−X^α] 5 ⟨−X⟩) ⟨X!⟩) ⟨id(★)⟩) ⟨X?ℓ⟩) ⟨+X⟩
⟶ (IdDyn, under ξ; X ∉ fresh(−X^α, +X^α))
  [+X^α] ((([−X^α, +X^α] ([−X^α] 5 ⟨−X⟩) ⟨id(X)⟩) ⟨X!⟩) ⟨X?ℓ⟩) ⟨+X⟩
⟶ (Merge, under ξ; −X ⨟ id(X) = −X)
  [+X^α] ((([−X^α, +X^α, −X^α] 5 ⟨−X⟩) ⟨X!⟩) ⟨X?ℓ⟩) ⟨+X⟩
⟶ (TagUntag, under ξ)
  [+X^α] ([−X^α, +X^α, −X^α] 5 ⟨−X⟩) ⟨+X⟩
⟶ (Merge; −X ⨟ +X = Id(ℕ))
  [+X^α, −X^α, +X^α, −X^α] 5 ⟨id(ℕ)⟩
⟶ (Id)
  5
```

The tagged argument enters `W`'s wrapper `[−X^α]`, where `X` is not
visible.  There it is the fresh-tag value
`[+X^α] (… ⟨X!⟩) ⟨id(★)⟩`, and the body `λx:★. x` sees only a `★`
whose tag it cannot name.  When the value comes back out, `Merge` and
`IdDyn` restore the tag `X`.  The Agda run (`ex2-run`) fires exactly
these 12 rules.

### Example 3 — implicit generalization, used non-parametrically

Replace the argument by `λx:★. (λy:ℕ. x) x`, which inspects its
argument at `ℕ`.  The coercion is again `gen X. (X! → X?ℓ)`; the inner
application has label `ℓ′`.  The first six steps are those of
Example 2.  The body then runs inside `W`'s wrapper `[−X^α]`, where `x`
is the fresh-tag value `x′ = [+X^α] (([−X^α] 5 ⟨−X⟩) ⟨X!⟩) ⟨id(★)⟩`.
The check `ℕ?ℓ′` fails, because the tag `X` is not visible there:

```
  [+X^α] (([−X^α] ((λy:ℕ. x′) (x′ ⟨ℕ?ℓ′⟩)) ⟨id(★)⟩) ⟨X?ℓ⟩) ⟨+X⟩
⟶ (TagUntagBad-⟪⟫, under ξ)
  [+X^α] (([−X^α] ((λy:ℕ. x′) (blame ℓ′)) ⟨id(★)⟩) ⟨X?ℓ⟩) ⟨+X⟩
⟶ (Blame, under ξ)
  [+X^α] (([−X^α] (blame ℓ′) ⟨id(★)⟩) ⟨X?ℓ⟩) ⟨+X⟩
⟶ (Blame, under ξ)
  [+X^α] ((blame ℓ′) ⟨X?ℓ⟩) ⟨+X⟩
⟶ (Blame, under ξ)
  [+X^α] (blame ℓ′) ⟨+X⟩
⟶ (Blame)
  blame ℓ′
```

Parametricity is enforced by the tag
`X`, not by the representation `ℕ`.

### Example 4 — a tag whose name has escaped

Source: `(λn:ℕ. n) ((ΛX. λx:X. (λz:★. z) x) [ℕ] 5)`.  The argument
has type `★`, so the outer application casts it by `ℕ?ℓ`.  The `★`-value that leaves
the `[+X^α]` boundary is `[+X^α] (W ⟨X!⟩) ⟨id(★)⟩`, where
`W = [−X^α] 5 ⟨−X⟩` is the sealed `5`.  The check `ℕ?ℓ` meets the tag
`X`.  `IdDyn` does not apply, because `X ∈ fresh(+X^α)`; the boundary
is all that keeps `X` in scope, so the term is a value.

```
  (λn:ℕ. n) (([+X^α] (W ⟨X!⟩) ⟨id(★)⟩) ⟨ℕ?ℓ⟩)
⟶ (TagUntagBad-⟪⟫, under ξ)
  (λn:ℕ. n) (blame ℓ)
⟶ (Blame)
  blame ℓ
```

GTSFImp gives the same answer, because its tag is the store variable
allocated by `β-Λ`, and so does λB.

### Example 5 — an escaped tag comes back into scope

A tagged value that has escaped its boundary can be passed back into the
same instantiation.  `Merge` then puts it under a boundary that no longer
introduces its tag, and `IdDyn` moves the tag out.  Source:

```
F [ℕ] 5 (λa:★. λk:★→ℕ. k a)
  where F = ΛX. λx:X. λh:★→(★→X)→X. h ((λz:★. z) x) (λy:★. (λw:X. w) y)
```

`F` exports `x` as a `★` (tag `X`) together with a function that
projects a `★` back to `X`, and the caller hands one to the other.  The
answer is `5`.  Write `W = [−X^α] 5 ⟨−X⟩` for the sealed `5` and
`K = λy:★. (λw:X. w) (y⟨X?ℓ⟩)`.  The prefix of the trace, which allocates
`α:=ℕ` and passes `h` its two arguments, is omitted.  The prefix reaches
the call `k a`, where both `k` and `a` were created inside the `[+X^α]`
boundary:

```
  ([+X^α] K ⟨id(★) → +X⟩) ([+X^α] (W⟨X!⟩) ⟨id(★)⟩)
⟶ (Wrap)
  [+X^α] (K ([−X^α] ([+X^α] (W⟨X!⟩) ⟨id(★)⟩) ⟨id(★)⟩)) ⟨+X⟩
⟶ (Merge, under ξ)
  [+X^α] (K ([−X^α, +X^α] (W⟨X!⟩) ⟨id(★)⟩)) ⟨+X⟩
⟶ (IdDyn, under ξ; X ∉ fresh(−X^α, +X^α))
  [+X^α] (K (([−X^α, +X^α] W ⟨id(X)⟩) ⟨X!⟩)) ⟨+X⟩
⟶ (Merge, under ξ; W = [−X^α] 5 ⟨−X⟩, and −X ⨟ id(X) = −X)
  [+X^α] (K (([−X^α, +X^α, −X^α] 5 ⟨−X⟩) ⟨X!⟩)) ⟨+X⟩
⟶ (Beta, under ξ)
  [+X^α] ((λw:X. w) (([−X^α, +X^α, −X^α] 5 ⟨−X⟩) ⟨X!⟩ ⟨X?ℓ⟩)) ⟨+X⟩
⟶ (TagUntag, under ξ)
  [+X^α] ((λw:X. w) ([−X^α, +X^α, −X^α] 5 ⟨−X⟩)) ⟨+X⟩
```

The `Merge` after `IdDyn` is needed because `IdDyn` leaves a boundary
directly over the boundary value `W`, which is not a value (§5).  The
machine-checked run (`GTNF/agda/Examples.agda`, `ex5-run`, 21 steps)
continues with `Beta`, then `Merge` and `Id` twice.  The second pair
comes from the two boundary layers around `h`'s call, which the omitted
prefix creates.  The result is `5`.  The `IdDyn` step happens at the interior `Δ, X:=α` of
the outer boundary, where `X` is visible again.  The rule's two forms of
side condition agree there: `X ∉ fresh(−X^α, +X^α)`, and
`Δ, X:=α ⊢ X`.

### Example 6 — instantiating a ∀-cast

Source: `(λg:∀X. X→★. g [𝔹] true) (ΛX. λx:X. 7)`.  The argument's type
`∀X. X→ℕ` is consistent with `∀X. X→★` by `∀ᶜ ((id X) ↦ (id ℕ) !)`, so
the argument's coercion is `∀X. (id(X) → ℕ!)`.  Its bound `X` is strict
(`X∼X`), and the coercion neither tags nor checks `X`.  Write
`W = (ΛX. λx:X. 7) ⟨∀X. (id(X) → ℕ!)⟩`, which is a value.

```
  (ν X:=𝔹. (W X) ⟨−X → id(★)⟩) true
⟶ (TyBeta, with inst_X(W) = (λx:X. 7) ⟨id(X) → ℕ!⟩, ⊣ α:=𝔹)
  ([+X^α] ((λx:X. 7) ⟨id(X) → ℕ!⟩) ⟨−X → id(★)⟩) true
⟶ (Wrap)
  [+X^α] (((λx:X. 7) ⟨id(X) → ℕ!⟩) ([−X^α] true ⟨−X⟩)) ⟨id(★)⟩
⟶ (CastFun)
  [+X^α] (((λx:X. 7) (([−X^α] true ⟨−X⟩) ⟨id(X)⟩)) ⟨ℕ!⟩) ⟨id(★)⟩
⟶ (CastId, under ξ)
  [+X^α] (((λx:X. 7) ([−X^α] true ⟨−X⟩)) ⟨ℕ!⟩) ⟨id(★)⟩
⟶ (Beta, under ξ)
  [+X^α] (7⟨ℕ!⟩) ⟨id(★)⟩
⟶ (IdDyn; ℕ ∉ fresh(+X^α))
  ([+X^α] 7 ⟨id(ℕ)⟩) ⟨ℕ!⟩
⟶ (Id, under ξ)
  7⟨ℕ!⟩
```

`TyBeta` allocates once.  Under the earlier alias design (see D5), the
first step would instead have produced
`[+X^α] ((ν Y:=X. ((ΛX. λx:X. 7) Y) ⟨−Y → id(ℕ)⟩) ⟨id(X) → ℕ!⟩) ⟨−X → id(★)⟩`,
and a second `TyBeta` would have allocated the alias `β:=α`.

### Example 7 — a tag cast enters a scope it has never seen

A polymorphic function receives a `★` that was created outside its
type variable's scope:

```
F = ΛY. λz:★. λy:Y. z                       : ∀Y. ★ → Y → ★

(ν Y:=ℕ. (F Y) ⟨id(★) → (−Y → id(★))⟩) (5⟨ℕ!⟩^[]) 3
```

The cast `5⟨ℕ!⟩^[]` was created at the top level, where there are no
names, so its mode environment is empty.  The run (`ex7-run`, 9 steps)
is:

```
  (ν Y:=ℕ. (F Y) ⟨id(★) → (−Y → id(★))⟩) (5⟨ℕ!⟩^[]) 3
⟶ (TyBeta, ⊣ β:=ℕ)
  ([+Y^β] (λz:★. λy:Y. z) ⟨id(★) → (−Y → id(★))⟩) (5⟨ℕ!⟩^[]) 3
⟶ (Wrap)
  ([+Y^β] ((λz:★. λy:Y. z) ([−Y^β] (5⟨ℕ!⟩^[]) ⟨id(★)⟩)) ⟨−Y → id(★)⟩) 3
⟶ (IdDyn, under ξ; ℕ ∉ fresh(−Y^β))
  ([+Y^β] ((λz:★. λy:Y. z) (([−Y^β] 5 ⟨id(ℕ)⟩) ⟨ℕ!⟩^[Y:X∼X])) ⟨−Y → id(★)⟩) 3
⟶ (Id, under ξ)
  ([+Y^β] ((λz:★. λy:Y. z) (5⟨ℕ!⟩^[Y:X∼X])) ⟨−Y → id(★)⟩) 3
⟶ (Beta, under ξ)
  ([+Y^β] (λy:Y. 5⟨ℕ!⟩^[Y:X∼X]) ⟨−Y → id(★)⟩) 3
⟶ (Wrap)
  [+Y^β] ((λy:Y. 5⟨ℕ!⟩^[Y:X∼X]) ([−Y^β] 3 ⟨−Y⟩)) ⟨id(★)⟩
⟶ (Beta, under ξ)
  [+Y^β] (5⟨ℕ!⟩^[Y:X∼X]) ⟨id(★)⟩
⟶ (IdDyn; ℕ ∉ fresh(+Y^β))
  ([+Y^β] 5 ⟨id(ℕ)⟩) ⟨ℕ!⟩^[]
⟶ (Id)
  5⟨ℕ!⟩^[]
```

At the first `IdDyn`, the boundary `[−Y^β]` sits in `F`'s body, where
`Y` is in scope, but its interior does not see `Y`.  So the moved cast
gets `Y:X∼X` (D10).  At the second `IdDyn`, the tag leaves `F` through
`[+Y^β]`, whose exterior has no `Y`, and the entry is dropped.
`ex7-env` in `Examples.agda` checks the state after the first `IdDyn`.

------------------------------------------------------------------------

## 9. Metatheory goals

GTNF should satisfy the same metatheory as GTSFImp.  Each goal below
names the GTSFImp statement it mirrors.  The νF-specific invariants
(`det`, tightness, `ScopeMapPreservation`/`ColorPreservation`) carry over
from `strong-rep-nu` as well.  Status: only the type imprecision of §9.4 is in Agda.

### 9.1 Type safety of the cast calculus

GTSFImp: `proof/TypeSafety/Progress.agda`, `proof/TypeSafety/Preservation.agda`.
νF: `strong-rep-nu.TypeSafety`.

```
progress :      if  Δ ∣ [] ⊢ M : A,  then  M is a value,  or  M = blame ℓ,
                or  Δ ⊢ M ⟶ N ⊣ ξ  for some N, ξ

preservation :  if  Δ ∣ [] ⊢ M : A  and  Δ ⊢ M ⟶ N ⊣ ξ,  then  ξ(Δ) ∣ [] ⊢ N : A

det :           if  Δ ⊢ M ⟶ N ⊣ ξ  and  Δ ⊢ M ⟶ N′ ⊣ ξ′,  then  N = N′  and  ξ = ξ′
                (up to the choice of fresh α)

no-bot-value :  if  V is a value,  then not  (Δ ∣ Γ ⊢ V : ∀X. X)
```

As in νF, preservation may need a well-formedness premise on `Δ`
(strong-rep-nu's `PreservationWf`/`CtxWf`).  `no-bot-value` is a lemma
for progress (§5).

### 9.2 Compilation

GTSFImp: `Compile.agda` (`compile`, `compile-value`).
νF: `strong-rep-nu.CompileTyping` (`compile-⊢`).

```
compile-⊢ :     if  Δ ∣ Γ ⊢ M : A  (source),  then  Δ ∣ Γ ⊢ ⟦M⟧ : A
compile-value : if  M is a source value,  then  ⟦M⟧ is a value
```

The coercion lemma behind `compile-⊢` is mode for mode:
if `μ ⊢ c : A ∼ B`, then `Δ ; μ ⊢ ⟦c⟧ℓ : A ⇒ B` (§7).

### 9.3 The source type system

GTSFImp: `GradualTypeCheck.agda`, `Consistency2.agda`.

- **A type checker.**  A synthesis function for source terms returns a
  type together with a typing derivation.  It is sound by construction,
  as in GTSFImp, where it is positive-only.
- **Decidable consistency.**  This is GTSFImp's `Consistency2.lower?`.

### 9.4 Type imprecision

GTSFImp: `Imprecision.agda` (`ImpEnv`, modes `X⊑X`/`X⊑★`),
`proof/Imprecision.agda` (`⊑-unique`), `proof/ImprecisionComposition.agda`
(`⊑-trans`), `proof/ImprecisionConsistency.agda` (`refl⊑`, and the
bridges between imprecision and consistency).

```
refl⊑ :     A ⊑ A
⊑-trans :   if  A ⊑ B  and  B ⊑ C,  then  A ⊑ C
⊑-unique :  any two derivations of  A ⊑ B  are equal
```

GTNF's types are GTSFImp's, so the type-level imprecision is ported
unchanged (`GTNF/agda/Imprecision.agda`, §12.1).  The imprecision environment `ImpEnv` is a different lattice
from the consistency modes `Env∼` of §3.  The two must not be conflated:
imprecision relates two programs, and consistency types the casts
within one program.

### 9.5 Static gradual guarantee

```
sgg :  if  Δ ∣ Γ ⊢ M : A  and  M ⊑ M′  (with  Γ ⊑ Γ′),
       then  Δ ∣ Γ′ ⊢ M′ : A′  for some  A′  with  A ⊑ A′
```

GTSFImp's term imprecision `μ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p`
(`GradualTermImprecision.agda`) is typed and carries both typings
(`gradual-term-imprecision-source-typing`/`-target-typing`).  I did not
find a standalone static gradual guarantee in GTSFImp.  For GTNF, the
plan is to state `sgg` against an *untyped* syntactic term imprecision,
and to derive the typed relation from it.  Since the source language is
GTSFImp's, `sgg` is really a theorem about GTSFImp's source; it could be
proved there and reused here.

### 9.6 Compilation preserves imprecision

GTSFImp: `proof/DGG/CompilePreservesImprecision2.agda`
(`compile-preserves-imprecision²`).

```
compile-⊑ :  if  μ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p,
             then  W₀ ∣ γ₀ ⊢² ⟦M⟧ ⊑ ⟦M′⟧ ∶ p₀
```

Here `⊢²` is a *cast-term* imprecision for GTNF that still has to be
designed, and `W₀`, `γ₀`, `p₀` are the initial world, context and type
imprecision.  In GTSFImp the world `W` aligns the two runs' type stores.
In GTNF it must align the two runs' representation variables (`α`) and
their names (`X:=α`), and it must relate boundaries `[δ] M ⟨c⟩` on the
two sides, including one-sided boundaries.  This is the largest new
design item in the metatheory.  §12 sketches it.

**Why GTNF is shaped for this relation.**  In earlier gradually typed
polymorphic calculi (GTSF, GTSFImp, PolyBlameI and others), the hardest
part of the DGG was defining a cast-term imprecision that reduction
preserves.  Within that, the hardest part was discovering the right
invariant relating the type variables of the two programs.  In
GTSFImp, for example, the world `W` and its rebasing (`RebaseAt`) evolve
with the two runs' global type stores.  GTNF was designed to make this
step more straightforward (Jeremy, 2026-10-01).  It is explicit about
type variables: every type variable is a name `X:=α`, bound by a `Λ`, a
coercion binder, or a boundary entry `+X^α`.  It also treats them
locally, in a lexically scoped way: a name is in scope only inside the
boundary that binds it, and coherence makes names and representation
variables correspond one to one within any conversion context.  The
hope is that the invariant between the two programs' type variables can
then be stated boundary by boundary, as a relation between matching
`δ`s and their names, instead of as a global correspondence between two
stores that grow independently.

### 9.7 Dynamic gradual guarantee

GTSFImp: `proof/DGG/DynamicGradualGuaranteeDef.agda` (`GradualDGG`), with
the proof under way in `proof/DGG/`.  For closed source terms with
`[] ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p`, the four parts are:

```
1.  if  ⟦M⟧ ⟶* V  (a value),
    then  ⟦M′⟧ ⟶* V′  (a value)  with  W ∣ [] ⊢² V ⊑ V′ ∶ q  for some world W

2.  if  ⟦M⟧ diverges,  then  ⟦M′⟧ diverges

3.  if  ⟦M′⟧ ⟶* V′  (a value),
    then  ⟦M⟧ ⟶* V  (a value)  with  W ∣ [] ⊢² V ⊑ V′ ∶ q,   or  ⟦M⟧ ⟶* blame ℓ

4.  if  ⟦M′⟧ diverges,  then  ⟦M⟧ diverges or reaches  blame ℓ
```

The runs are νF runs, so each `⟶*` carries the allocations it made
(`runCtx`), and `q` relates the result types at the two final contexts.
The proof strategy follows GTSFImp: a simulation of the more precise
side by the less precise side (`sim-left`/`sim-right`), with catch-up
lemmas for the administrative steps that occur on one side only.  In
GTNF those steps are `Merge`, `Id`, `IdDyn`, `CastId`, `CastSeq`, and the
`Inst`/`TyBeta` pair.  The consistency modes (D6) are what make the
`bot-elim` and `bot-intro` cells vacuous, by `no-bot-value`.

------------------------------------------------------------------------

## 10. Decisions taken in this draft, and open questions

These decisions are complementary: together they make up the draft.
Each one can be revisited on its own.

- **D1 (separation).**  Coercions are their own sort and are applied by
  their own term form `M ⟨p⟩`; νF's conversions, `ν` and boundaries
  are unchanged.  The sorts meet only in `Inst`, `TyBeta` (via
  `inst_X`), `IdDyn` and `TagUntagBad-⟪⟫`.
- **D2 (cast values are simples).**  This lets `Wrap`, `TyBeta`,
  `Merge` and `Id` apply unchanged when the interior is a cast value.
- **D3 (tags by name).**  `X` is a ground type, and tags are compared
  syntactically, which coherence makes sound (§6.4).
- **D4 (inst closes at ★).**  `Inst` instantiates by `ν X:=★` with the
  conversion `reveal_X`, and substitutes `★` for `X` in the coercion,
  as GTSFImp does.
- **D5 (one allocation per instantiation).**  `TyBeta` instantiates a
  ∀-value through all of its layers with the meta-operation `inst_X`,
  which allocates nothing (Jeremy, 2026-10-01).  An earlier draft
  re-instantiated the value under a `∀X.p` cast by an alias `ν Y:=X`,
  which cost a second allocation per `∀`-cast layer (Example 6).  Under
  D8, the alias also gave the inner tags the name `Y`, so a check `X?ℓ`
  in `p` would have blamed where GTSFImp's `β-∀` succeeds.  Since D6,
  such a check is ill typed, because `p`'s `X` is strict.  `inst_X`
  matches GTSFImp's `β-∀`, which instantiates the value itself with a
  single allocation and then casts.  νF's `TyWrap` is now the boundary
  case of `TyBeta`.
- **D6 (modes in the cast calculus).**  Coercion typing carries
  GTSFImp's consistency modes (`X∼X`, `X∼★`, `★∼X`, `★∼X∼★`), and
  `∀X.p`, `inst X.p` and `gen X.p` give their bound variable the modes
  of `extᵐ`, `instᵐ` and `genᵐ` (Jeremy, 2026-10-01; this reverses the
  first draft).  The modes give `no-bot-value` (§5), and the dynamic
  gradual guarantee needs them.  `bot-elim` and `bot-intro ℓ` are
  dedicated coercions.  `bot-intro ℓ` blames eagerly, as GTSFImp's
  `blame-bot-intro` does.
- **D7 (tags move out of boundaries).**  `IdDyn` moves a tag out of a
  boundary whenever the tag is visible outside it.  A `★`-value keeps
  a boundary only when the tag is in `fresh(δ)` (§5).
- **D8 (alias tags are distinct).**  A tag created under an alias name
  does not match the name it aliases, so the check blames (Jeremy,
  2026-10-01).  GTSFImp and λB behave the same way.  Consider

  ```
  ΛX. λx:X. (λw:X. w) (f [X] x)        where  f = ΛY. λy:Y. (λz:★. z) y
  ```

  `f [X]` allocates the alias `β:=α` under the name `Y`, so the `★` that
  `f` returns is tagged `Y`, and `Y ∈ fresh(+Y^β)`.  Writing `x₀` for the
  value of `x` and `ℓ` for the label of the outer application, the end
  of the run is

  ```
    (λw:X. w) (([+Y^β] (([−Y^β] x₀ ⟨−Y⟩) ⟨Y!⟩) ⟨id(★)⟩) ⟨X?ℓ⟩)
  ⟶ (TagUntagBad-⟪⟫, under ξ)
    (λw:X. w) (blame ℓ)
  ⟶ (Blame)
    blame ℓ
  ```

- **D9 (no term moves under a new name).**  No rule weakens a term by
  an ordinary name, even with names.  The `gen` case of `inst_X` puts
  the value under the binder's dual `[−X^α]` rather than in the
  interior that has `X` (§6.2; Jeremy, 2026-10-01).  A weakening lemma
  in the preservation proof would be the sign of a term changing
  colour.

- **D10 (unseen names get X∼X).**  When `IdDyn` moves a tag cast out of
  a boundary, every exterior name that the interior cannot see gets the
  mode `X∼X` in the moved cast's environment (`exit_δ(μ)`, §6.3;
  Example 7; Jeremy, 2026-10-01).  This matches GTSFImp's `extᵐ` at an
  allocation.  The choice may be revisited when `⊢²` is designed.

- **D11 (marks are chosen at the binder).**  In `⊢²`, the mark of a
  name that both sides bind (`X⊑X` or `X⊑★`) is chosen by the rule that
  binds it, and it is fixed for the subterm under the binder.  No rule
  weakens a mark on the way to a premise, unlike GTSFImp's
  `ImpEnvMono` (§12.2, Example P4; Jeremy, 2026-10-01).

- **D12 (names lexical, cells global).**  In `⊢²`'s worlds, the
  relation between the two sides' type variables (`Ω`, `η`, `η′`, `μ`)
  is lexically scoped.  The relation `ϱ` between their representation
  variables is global: it grows at matched allocations and is read
  when a boundary rebinds a cell (§12.2, Example P4; Jeremy,
  2026-10-01).

- **D13 (`ϱ` is many-to-one, toward the left).**  In `⊢²`'s worlds,
  each right (less precise) cell has at most one left partner in `ϱ`,
  and a left cell may have several.  So a right-only `+X^β` always has
  a unique left name to rejoin.  The mirror is not needed, because an
  extra left name can stay left-only at `X⊑★`, while an extra right
  name cannot stay right-only (§12.6, F3; C12–C14; mirror pairs M1,
  M2, M4; Jeremy, 2026-10-02).

The open design questions are those of the `⊢²` sketch (§12.5).

Out of scope for now: space efficiency.  Normal forms for coercions,
and a composition `p ⨟ q` like νF's for conversions, are not a concern
for the time being (Jeremy, 2026-10-01).

------------------------------------------------------------------------

## 11. Agda plan

- `GTNF/agda/`, with its own `Makefile` and `All.agda`, starts as a
  copy of `SystemF/agda/strong-rep-nu`'s definitional layer (`Types`,
  `Ctx`, `Boundary`, `Conversion`, `Lookup`, `Terms`, `TermSubst`,
  `Reduction`).  `★` is added to `Ty`, and `Coercion` is a new module.
- De Bruijn indices are used throughout, with parallel renaming and
  substitution.  `inst X.p`, `gen X.p` and `∀X.p` bind a type variable
  (`underΛ`), and `p[★/X]` is an instance of a coercion substitution
  `substᶜ`.
- The source language and its consistency relation are taken from
  GTSFImp (`GradualTerms`, `Consistency`, `Primitives`).  They are
  ported from GTSFImp's intrinsically scoped `Ty Δ` to νF's extrinsic
  `Ty`, or bridged by an erasure.  This is to be decided once the cast
  calculus is settled.
- Status: the definitional layer, `TypeCheck` (a `Maybe` typing
  derivation), `Eval` (a step function that returns the step
  derivation) and `Examples` (Examples 1–7 and D8 as `refl` runs) exist
  in `GTNF/agda/`, and `make check` passes.  Also in place:
  `Imprecision` (type imprecision, copied from GTSFImp, §12.1),
  `ImprecisionExamples` (the six pairs of §12.4) and `Show` (a named
  renderer, `scripts/render_gtnf.sh`).  Next: settle §12.5's open
  questions, then formalize `⊢²` in Agda; then progress and
  preservation, then `compile-⊢`.

------------------------------------------------------------------------

## 12. Cast-term imprecision `⊢²` (sketch)

Status: sketch (2026-10-01).  §12.1 is in Agda (`Imprecision.agda`).
The relation itself (§12.3) is on paper only.  The examples (§12.4)
are machine-run: each pair of programs is in
`ImprecisionExamples.agda`, and both of its runs come from `Eval`.
The left program is always the **more precise** one.

### 12.1 Type imprecision

GTSFImp's `Imprecision.agda`, copied rule for rule into
`GTNF/agda/Imprecision.agda`.  The marks are `X⊑X` and `X⊑★`, and an
imprecision environment `μ` gives one mark to each name in scope.  As
with `ModeEnv`, it is a list parallel to the names (index 0 at the
head).

```
                                                        μ(X) = X⊑★
  ★ ⊑ ★     ι ⊑ ι     X ⊑ X     ι ⊑ ★     ∀X.★ ⊑ ★       ──────────
                                                         X ⊑ ★

  A ⊑ A′   B ⊑ B′          A ⊑ ★   B ⊑ ★          μ, X:X⊑X ⊢ A ⊑ B
  ─────────────────        ─────────────          ─────────────────
  A → B ⊑ A′ → B′          A → B ⊑ ★              μ ⊢ ∀X.A ⊑ ∀X.B

  μ, X:X⊑★ ⊢ A ⊑ ⇑B    A not a variable    X ∈ A     (∀⊑)
  ───────────────────────────────────────────────
  μ ⊢ ∀X.A ⊑ B

  μ, X:X⊑X ⊢ A ⊑ ★    A ≠ ★
  ──────────────────────────     ∀X.X ⊑ ∀X.★  (bot-elim)     ∀X.X ⊑ ★
  μ ⊢ ∀X.A ⊑ ★
```

The marks belong to the imprecision lattice.  They are not the
consistency modes of §3, which type the casts inside one program
(§9.4).

### 12.2 Worlds

A cast-term imprecision judgment relates a left term typed in `Δ` to a
right term typed in `Δ′`.  The two runs allocate independently, and a
`ν`, a `Λ` or a boundary entry may exist on one side only.  A
**world** says how the two sides' names line up.  It follows GTSFImp's
`World` (`proof/DGG/CtxImp.agda`), minus the stores:

```
W = (Δ, Δ′, Ω, η, η′, μ, ϱ)

  Ω              the center: a list of names
  η  : names(Δ)  ↪ Ω     order-preserving embeddings (GTSFImp ηᴸʷ, ηᴿʷ);
  η′ : names(Δ′) ↪ Ω     every center name is in the image of at least one
  μ  : ImpEnv(Ω)         a name in both images is X⊑X or X⊑★;
                         a name in η's image only (left-only) is X⊑★
  ϱ  ⊆ cells(Δ) × cells(Δ′)    the cell correspondence: each right cell has at
                               most one left partner, and a left cell may have
                               several (D13)

  A ⊑_W A′   iff   μ ⊢ η(A) ⊑ η′(A′)               (GTSFImp _⊑ᵂ⟨_⟩_)
```

Well-formedness has two parts:

- **Names name paired cells.**  If a center name `X` is `X:=α` on the
  left and `X:=β` on the right, then `(α, β) ∈ ϱ`.
- **Paired cells agree.**  If `(α, β) ∈ ϱ`, then either both are
  abstract (bound by a `Λ` on each side), or `α` is abstract and
  `β:=★`, or `α:=R`, `β:=R′`, and `R ⊑ R′` (read through `W`).

**Names are related lexically, cells globally** (D12).  The relation
between type variables (`Ω`, `η`, `η′`, `μ`) is lexically scoped: it
is extended and shrunk with the scope, never by a step.  The relation
between representation variables (`ϱ`) is global, like the stores it
relates.

The point of the design (§9.6) is that **no part of a world is ever
rebased.**  `Ω`, `η`, `η′` and `μ` change only lexically: they are
extended by a binder (`Λ`, a coercion binder, a boundary entry `+X^α`)
and shrunk by an unbind (`−X^α`), for the subterm under it, exactly as
the type context is.  The one non-lexical part is `ϱ`, and it only
grows: a `TyBeta` that the other side matches adds one pair.  An
unmatched allocation only renumbers the allocating side's cells (de
Bruijn).

World operations, used by the rules:

```
W ⊕ X:m          both sides bind X (a new center name in both images, mark m)
W ⊕ᴸ X           the left side binds X alone (center name in η only, X⊑★)
W ⊕ᴿ X           the right side binds X alone (center name in η′ only)
W[δ ∥ δ′]        the interior world of a boundary pair: each side's
                 changes act on that side's names and embedding.
                 −X on one side removes X from that side's image; a center
                 name in neither image is dropped.  +X^α joins the center
                 name of the cell α is paired with by ϱ, if any, and is
                 otherwise a new one-sided center name.  A new
                 both-sided name gets the mark X⊑X or X⊑★; the
                 derivation chooses (Example P4 needs X⊑★; D11).
                 (Write W[δ ∥ ·] and W[· ∥ δ′] for a one-sided boundary.)
```

`W[δ ∥ δ′]` is defined only when it is well formed.  In particular, a
right-only `−X` of a name in both images leaves `X` left-only, so it
needs `μ(X) = X⊑★` (Example P4).

### 12.3 Rules

`W ∣ γ ⊢² M ⊑ M′ : A ⊑ A′` with `γ ::= [] | γ, x : B ⊑ B′`.  Every
rule also assumes the two typings `Δ ∣ γᴸ ⊢ M : A` and
`Δ′ ∣ γᴿ ⊢ M′ : A′` and `A ⊑_W A′`; the premises below list only what
is new.  The rules marked "GTSFImp" are GTSFImp's
`proof/DGG/CastTermImprecision.agda` rules with the same name.

**Congruence** (GTSFImp `x⊑x²`, `κ⊑κ²`, `ƛ⊑ƛ²`, `·⊑·²`, `⊕⊑⊕²`):
the usual rules, one per term former.  Their types are related
componentwise.

**Blame** (GTSFImp `blame⊑²`):

```
  ────────────────────────────── (blame⊑)
  W ∣ γ ⊢² blame ℓ ⊑ M′ : A ⊑ A′
```

**Casts** (GTSFImp `cast⊑cast²`, `cast⊑²`, `⊑cast²`).  Each coercion
is typed on its own side, under the mode environment its cast carries.
The rules do not compare the two coercions, or the two mode
environments, except through the types:

```
  W ∣ γ ⊢² M ⊑ M′ : B ⊑ B′    p : B ⇒ A    p′ : B′ ⇒ A′
  ────────────────────────────────────────────────── (cast⊑cast)
  W ∣ γ ⊢² M ⟨p⟩ ⊑ M′ ⟨p′⟩ : A ⊑ A′

  W ∣ γ ⊢² M ⊑ M′ : B ⊑ A′    p : B ⇒ A
  ────────────────────────────────────── (cast⊑)
  W ∣ γ ⊢² M ⟨p⟩ ⊑ M′ : A ⊑ A′

  W ∣ γ ⊢² M ⊑ M′ : A ⊑ B′    p′ : B′ ⇒ A′
  ────────────────────────────────────── (⊑cast)
  W ∣ γ ⊢² M ⊑ M′ ⟨p′⟩ : A ⊑ A′
```

**Type abstraction** (GTSFImp `Λ⊑Λ²`, `Λ⊑²`), plus one new rule.
`Λ⊑` keeps the right term unweakened: the right side does not bind
`X`, so `η′` simply does not reach the new center name.

```
  W ⊕ X:X⊑X ∣ ⇑γ ⊢² V ⊑ V′ : A ⊑ A′
  ────────────────────────────────── (Λ⊑Λ)
  W ∣ γ ⊢² ΛX.V ⊑ ΛX.V′ : ∀X.A ⊑ ∀X.A′

  W ⊕ᴸ X ∣ ⇑ᴸγ ⊢² V ⊑ M′ : A ⊑ B′    A not a variable    X ∈ A
  ──────────────────────────────────────────────────────── (Λ⊑)
  W ∣ γ ⊢² ΛX.V ⊑ M′ : ∀X.A ⊑ B′

  W ⊕ X:X⊑X ∣ [] ⊢² V ⊑ V′ : A ⊑ A′    β:=★    c′ : A′ ⇒ B′   (new)
  ──────────────────────────────────────────────────── (Λ⊑⟪+⟫)
  W ∣ γ ⊢² ΛX.V ⊑ [+X^β] V′ ⟨c′⟩ : ∀X.A ⊑ B′
```

`Λ⊑⟪+⟫` is for a right side that has already instantiated a value at
`★` through `Inst`, while the left side still holds the `Λ`
(Example P3).  The left `Λ`'s abstract cell is paired with the right
cell `β:=★`.  When the left side later instantiates, its new boundary
`[+X^α]` meets the right's `[+X^β]`, and `ϱ` gains `(α, β)`.

**Instantiation** (GTSFImp `•⊑•²`, `•⊑²`).  The compiled form of
`M [A]` is a `ν`, so the two type applications become:

```
  W ∣ γ ⊢² L ⊑ L′ : ∀X.C ⊑ ∀X.C′    A ⊑_W A′    c : C ⇒ B    c′ : C′ ⇒ B′
  ─────────────────────────────────────────────────────────────── (ν⊑ν)
  W ∣ γ ⊢² ν X:=A.(L X)⟨c⟩ ⊑ ν X:=A′.(L′ X)⟨c′⟩ : B ⊑ B′

  W ∣ γ ⊢² L ⊑ M′ : ∀X.C ⊑ B′    A ⊑_W ★    c : C ⇒ B
  ──────────────────────────────────────────────── (ν⊑)
  W ∣ γ ⊢² ν X:=A.(L X)⟨c⟩ ⊑ M′ : B ⊑ B′
```

There is no `⊑ν`.  The only right-only `ν` is the one that `Inst`
creates, and the right side reduces it by `TyBeta` at once.  So a
catch-up lemma can take `Inst` and `TyBeta` together, and the
relation never has to hold in between.

**Boundaries** (new; these replace GTSFImp's eight `reveal`/`conceal`
rules).  A boundary's interior is term-closed, so the premise has
`γ = []`.  The conversions are typed on their own sides, and, like the
coercions, they are not compared with each other:

```
  W[δ ∥ δ′] ∣ [] ⊢² M ⊑ M′ : Aᵢ ⊑ A′ᵢ    c : Aᵢ ⇒ A    c′ : A′ᵢ ⇒ A′
  ───────────────────────────────────────────────────────────── (⟪⟫⊑⟪⟫)
  W ∣ γ ⊢² [δ] M ⟨c⟩ ⊑ [δ′] M′ ⟨c′⟩ : A ⊑ A′

  W[δ ∥ ·] ∣ [] ⊢² M ⊑ M′ : Aᵢ ⊑ A′    c : Aᵢ ⇒ A
  ───────────────────────────────────────────── (⟪⟫⊑)
  W ∣ γ ⊢² [δ] M ⟨c⟩ ⊑ M′ : A ⊑ A′

  W[· ∥ δ′] ∣ [] ⊢² M ⊑ M′ : A ⊑ A′ᵢ    c′ : A′ᵢ ⇒ A′
  ───────────────────────────────────────────── (⊑⟪⟫)
  W ∣ γ ⊢² M ⊑ [δ′] M′ ⟨c′⟩ : A ⊑ A′
```

In `⟪⟫⊑` and `⊑⟪⟫`, the term without the boundary is in the premise
at `γ = []`, so it must be term-closed as well.  That holds at run
time, because every boundary of a run is a closed subterm.

**Count.**  Five congruence rules, `blame⊑`, three cast rules, three
`Λ` rules, two `ν` rules and three boundary rules: 17 rules.  GTSFImp's
`⊢²` has 22.

### 12.4 Examples

Six pairs, in `ImprecisionExamples.agda`.  Each run is a `Reaches …
refl` proof, and the states below are rendered from `evalTerms` by
`Show.agda` (`scripts/render_gtnf.sh`), not transcribed by hand.  Each
run names its cells by allocation order, so both runs call their first
cell `α`.  They are different cells, and `ϱ` pairs them; write `αᴸ`
and `αᴿ` when the difference matters.

The traces are shown **synchronized**: each block is a pair of states
that the relation must relate, and between blocks one side takes one
step while the other takes zero or more steps (the shape of a
simulation, §9.7).  Under each pair are the rules at the top of its
derivation and the facts the derivation turns on.

| pair | left (more precise) | right | left answer | right answer |
|---|---|---|---|---|
| P1 | `(ΛX.λx:X.x)[ℕ] 5` | `(ΛX.λx:X.x)[★] 5` | `5` (5 steps) | `5⟨ℕ!⟩` (6) |
| P2 | `(ΛX.λx:X.x)[ℕ] 5` | `(λx:★.x) 5` | `5` (5) | `5⟨ℕ!⟩` (1) |
| P3 | `(λf:∀X.X→X. f[ℕ] 5)(ΛX.λx:X.x)` | Example 1 | `5` (6) | `5⟨ℕ!⟩` (11) |
| P4 | as P3 | Example 2 | `5` (6) | `5` (12) |
| P5 | Example 4 | `(λn:ℕ.n)((λx:★.(λz:★.z) x) 5)` | `blame ℓ` (6) | `5` (4) |
| P6 | `(λg:∀X.X→ℕ. g[𝔹] true)(ΛX.λx:X.7)` | Example 6 | `7` (5) | `7⟨ℕ!⟩` (8) |

The answers are related in every case: `5 ⊑ 5⟨ℕ!⟩` by `⊑cast`, and in
P5 the left blames, which `blame⊑` allows.

#### P1 — both sides instantiate, at ℕ and at ★ (aligned boundaries)

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  ((ν X:=★. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5⟨ℕ!⟩^[])
   ·⊑·, ν⊑ν (ℕ ⊑ ★), ⊑cast
                                         L: TyBeta (α:=ℕ)    R: TyBeta (α:=★)
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5⟨ℕ!⟩^[])
   ·⊑·, ⟪⟫⊑⟪⟫: X both-sided, ϱ = {(αᴸ, αᴿ)}, αᴸ:=ℕ ⊑ αᴿ:=★
                                         L: Wrap             R: Wrap
L  ([+X^α] ((λx:X. x) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
R  ([+X^α] ((λx:X. x) ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)) ⟨+X⟩)
   ⟪⟫⊑⟪⟫, ·⊑·, ⟪⟫⊑⟪⟫ (both unbind X), ⊑cast: 5 ⊑ 5⟨ℕ!⟩ at ℕ ⊑ ★
                                         L: Beta             R: Beta
                                         L: Merge            R: Merge
L  ([+X^α, −X^α] 5 ⟨id(ℕ)⟩)
R  ([+X^α, −X^α] 5⟨ℕ!⟩^[] ⟨id(★)⟩)
   ⟪⟫⊑⟪⟫, ⊑cast
                                         L: Id               R: IdDyn, Id
L  5
R  5⟨ℕ!⟩^[]
   ⊑cast
```

The two `−X` conversions are the same syntax, typed at different
representations (`ℕ ⇒ X` and `★ ⇒ X`).  The interior types `ℕ ⊑ ★`
are related because the paired cells are.

#### P2 — the left side alone abstracts and instantiates (one-sided boundaries)

```
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   ·⊑·, ν⊑ (ℕ ⊑ ★), Λ⊑: X left-only, λx:X.x ⊑ λx:★.x at X→X ⊑ ★→★
                                         L: TyBeta (α:=ℕ)    R: —
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   ·⊑·, ⟪⟫⊑: X left-only, interior X→X ⊑ ★→★, exterior ℕ→ℕ ⊑ ★→★
                                         L: Wrap             R: —
L  ([+X^α] ((λx:X. x) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
R  ((λx:★. x) 5⟨ℕ!⟩^[])
   ⟪⟫⊑, ·⊑·, ⟪⟫⊑ (the left unbinds its left-only X; the center drops it)
                                         L: Beta             R: Beta
L  ([+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩)
R  5⟨ℕ!⟩^[]
   ⟪⟫⊑, ⟪⟫⊑, ⊑cast: [−X^α] 5 ⟨−X⟩ ⊑ 5⟨ℕ!⟩ at X ⊑ ★ (X left-only)
                                         L: Merge, Id        R: —
L  5
R  5⟨ℕ!⟩^[]
```

The right term crosses the left-only `Λ` and `[+X^α]` unweakened: only
`η` reaches the new center name.

#### P3 — the right side alone instantiates, by `Inst` (the new rule `Λ⊑⟪+⟫`)

```
L  ((λx:(∀X. X→X). ((ν X:=ℕ. (x X) ⟨−X → +X⟩) 5)) (ΛY. (λx:Y. x)))
R  ((λx:★→★. (x 5⟨ℕ!⟩^[])) (ΛX. (λx:X. x))⟨inst Y. (Y?ℓ0 → Y!)⟩^[])
   ·⊑·, ƛ⊑ƛ (∀X.X→X ⊑ ★→★), ν⊑ in the body; ⊑cast, Λ⊑Λ for the argument
                                         L: Beta             R: Inst, TyBeta (α:=★), Beta
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  (([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
   ·⊑·, ν⊑, ⊑cast, Λ⊑⟪+⟫: the left Λ's abstract cell is paired with αᴿ:=★
                                         L: TyBeta (α:=ℕ)    R: —
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  (([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
   ·⊑·, ⊑cast, ⟪⟫⊑⟪⟫: ϱ gains (αᴸ, αᴿ), αᴸ:=ℕ ⊑ αᴿ:=★
                                         L: Wrap             R: CastFun, CastId, Wrap
L  ([+X^α] ((λx:X. x) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
R  ([+X^α] ((λx:X. x) ([−X^α] 5⟨ℕ!⟩^[] ⟨−X⟩)) ⟨+X⟩)⟨id(★)⟩^[]
   ⊑cast, then as P1
                                         L: Beta             R: Beta
                                         L: Merge            R: Merge
                                         L: Id               R: IdDyn, Id, CastId
L  5
R  5⟨ℕ!⟩^[]
```

The `Inst`/`TyBeta` pair runs before the right's `Beta`, because `inst`
is not inert, so the right holds a boundary while the left still holds
a `Λ`.  That is the only reason for `Λ⊑⟪+⟫`.

#### P4 — the right side alone generalizes (a both-sided name at `X⊑★`)

```
L  ((λx:(∀X. X→X). ((ν X:=ℕ. (x X) ⟨−X → +X⟩) 5)) (ΛY. (λx:Y. x)))
R  ((λx:(∀X. X→X). ((ν X:=ℕ. (x X) ⟨−X → +X⟩) 5)) (λx:★. x)⟨gen Y. (Y! → Y?ℓ0)⟩^[])
   ·⊑·, ƛ⊑ƛ, ν⊑ν; ⊑cast, Λ⊑ (Y left-only) for the argument
                                         L: Beta             R: Beta
                                         L: TyBeta (α:=ℕ)    R: TyBeta (α:=ℕ)
L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
R  (([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X] ⟨−X → +X⟩) 5)
   ·⊑·, ⟪⟫⊑⟪⟫ with X both-sided at X⊑★, ⊑cast, ⊑⟪⟫: the right unbinds X,
   so X is left-only inside, λx:X.x ⊑ λx:★.x at X→X ⊑ ★→★
                                         L: Wrap             R: Wrap, CastFun
L  ([+X^α] ((λx:X. x) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩)
R  ([+X^α] (([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩) ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★])⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
   ⟪⟫⊑⟪⟫, ⊑cast (X?: X ⊑ ★ to X ⊑ X), ·⊑·, ⊑⟪⟫ for the function,
   ⊑cast for the argument: [−X^α] 5 ⟨−X⟩ ⊑ ([−X^α] 5 ⟨−X⟩)⟨X!⟩ at X ⊑ ★
                                         L: Beta             R: Wrap, Beta
L  ([+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩)
R  ([+X^α] ([−X^α] ([+X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:X∼★] ⟨id(★)⟩) ⟨id(★)⟩)⟨X?ℓ0⟩^[X:★∼X] ⟨+X⟩)
   ⟪⟫⊑⟪⟫, ⊑cast, ⊑⟪⟫ (the right unbinds X: X left-only),
   ⊑⟪⟫ (the right rebinds the cell αᴿ, which ϱ pairs with αᴸ: X is
   both-sided again), ⊑cast (X!), ⟪⟫⊑⟪⟫
                                         L: —                R: Merge, IdDyn, Merge, TagUntag
L  ([+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩)
R  ([+X^α] ([−X^α, +X^α, −X^α] 5 ⟨−X⟩) ⟨+X⟩)
   ⟪⟫⊑⟪⟫, ⟪⟫⊑⟪⟫ with δ = (−X), δ′ = (−X, +X, −X): the net effect on
   names is the same on both sides
                                         L: Merge, Id        R: Merge, Id
L  5
R  5
```

This pair needs two things that P1–P3 do not.  First, a both-sided
name at `X⊑★`: inside the `[+X^α]` pair, the left's `λx:X.x` faces the
right's `λx:★.x`, which `gen` has not yet cast to `X → X`.  Second, `ϱ`
must survive a right-only unbind: the right's `[−X^α, +X^α]` hides `X`
and rebinds the same cell, and only `ϱ` says that the rebound name is
the left's `X` again.

#### P5 — the left side blames on an escaped tag; the right side succeeds

```
L  ((λx:ℕ. x) ((ν X:=ℕ. ((ΛY. (λx:Y. ((λy:★. y) x⟨Y!⟩^[Y:★∼X∼★]))) X) ⟨−X → id(★)⟩) 5)⟨ℕ?ℓ0⟩^[])
R  ((λx:ℕ. x) ((λx:★. ((λy:★. y) x)) 5⟨ℕ!⟩^[])⟨ℕ?ℓ0⟩^[])
   ·⊑·, cast⊑cast, ·⊑·, ν⊑, Λ⊑ (Y left-only); cast⊑ for x⟨Y!⟩ ⊑ x
                                         L: TyBeta, Wrap     R: —
                                         L: Beta             R: Beta
                                         L: Beta             R: Beta
L  ((λx:ℕ. x) ([+X^α] ([−X^α] 5 ⟨−X⟩)⟨X!⟩^[X:★∼X∼★] ⟨id(★)⟩)⟨ℕ?ℓ0⟩^[])
R  ((λx:ℕ. x) 5⟨ℕ!⟩^[]⟨ℕ?ℓ0⟩^[])
   ·⊑·, cast⊑cast, ⟪⟫⊑ (X left-only), cast⊑ (the left's X!),
   ⟪⟫⊑ (the left unbinds X), ⊑cast: 5 ⊑ 5⟨ℕ!⟩
                                         L: TagUntagBad-⟪⟫   R: TagUntag
L  ((λx:ℕ. x) blame ℓ0)
R  ((λx:ℕ. x) 5)
   ·⊑·, blame⊑
```

The fresh-tag value `[+X^α] (… ⟨X!⟩) ⟨id(★)⟩` is related to the
`ℕ`-tagged `5`.  This is sound because `X` is left-only, so its mark
is `X⊑★`: the right side sees `★` wherever the left sees `X`, and no
check on the right can be paired with a check of `X` on the left.

#### P6 — a `∀`-cast on the right, and conversions of different shape

```
L  ((λx:(∀X. X→ℕ). ((ν X:=𝔹. (x X) ⟨−X → id(ℕ)⟩) true)) (ΛY. (λx:Y. 7)))
R  ((λx:(∀X. X→★). ((ν X:=𝔹. (x X) ⟨−X → id(★)⟩) true)) (ΛY. (λx:Y. 7))⟨∀Z. (id(Z) → ℕ!)⟩^[])
   ·⊑·, ƛ⊑ƛ, ν⊑ν; ⊑cast, Λ⊑Λ
                                         L: Beta             R: Beta
                                         L: TyBeta (α:=𝔹)    R: TyBeta (α:=𝔹)
L  (([+X^α] (λx:X. 7) ⟨−X → id(ℕ)⟩) true)
R  (([+X^α] (λx:X. 7)⟨id(X) → ℕ!⟩^[X:X∼X] ⟨−X → id(★)⟩) true)
   ·⊑·, ⟪⟫⊑⟪⟫ (the conversions differ: −X → id(ℕ) and −X → id(★)), ⊑cast
                                         L: Wrap             R: Wrap
                                         L: Beta             R: CastFun, CastId, Beta
L  ([+X^α] 7 ⟨id(ℕ)⟩)
R  ([+X^α] 7⟨ℕ!⟩^[X:X∼X] ⟨id(★)⟩)
   ⟪⟫⊑⟪⟫, ⊑cast
                                         L: Id               R: IdDyn, Id
L  7
R  7⟨ℕ!⟩^[]
```

`inst_X` reaches through the right's `∀`-cast, so both `TyBeta`s
allocate one cell each and the boundaries stay aligned.

### 12.5 What the examples say about the sketch

- **The world never rebases.**  In all six pairs, `Ω`, `η`, `η′` and
  `μ` change only at a binder or a boundary entry, for the subterm
  under it.  `ϱ` gains a pair at a matched `TyBeta` (P1, P4, P6) and
  at the left's catch-up `TyBeta` in P3.
- **Rules used.**  Every rule of §12.3 is used except `⊕⊑⊕` (no
  example has an operator).  P2 and P5 need the left-only boundary
  rule `⟪⟫⊑`.  P4 needs
  the right-only rule `⊑⟪⟫`, with both an unbind and a rebind.  P3
  needs `Λ⊑⟪+⟫`.
- **Not exercised.**  A gen cast on both sides; a gen cast on the left
  only (its `[−X^α]` is then a left-only unbind of a both-sided name);
  `bot-elim`/`bot-intro`; an escaped tag that comes back into scope
  (Example 5) on one side only; two-allocation runs (D8).
- **Open questions** (to be settled one at a time):
  1. *Settled (D11).*  A both-sided name gets the mark `X⊑★` at its
     binder (`W ⊕ X:m`, `W[δ ∥ δ′]`), not by GTSFImp's `ImpEnvMono`
     decay at the cast rules.
  2. *Settled (D12).*  `ϱ` stays in the world as a global relation on
     cells; the relation on names stays lexical.  P4's rebind reads `ϱ`.
  3. Whether `W[δ ∥ δ′]` should be restricted (for example, forbid a
     left-only unbind of a both-sided name), or whether such
     restrictions should come from the DGG proof.

     *Finding (probe `notes/LeftOnlyUnbindProbe.agda`; corrected).*
     The probe's left coercion
     `gen X. inst Y. ((X! ; Y?ℓ) → (Y! ; X?ℓ))` is a well-typed GTNF
     coercion, and a §12.3 world relates its run to the direct cast's
     only at the start.  But compilation never produces it.  It is not
     the image `⟦c⟧ℓ` of any consistency evidence: inside it,
     `X ∼ Y` would be needed for two distinct names, and consistency
     is not transitive (`_!` and `？_` only give `A ∼ ★` and
     `★ ∼ B`).  This agrees with the specification "two types are
     consistent if and only if they have a common lower bound"
     (Jeremy, 2026-10-01).  `∀X.X→X`'s only lower bound is itself,
     so `∀Y.Y→★` (which `∀X.X→X ⋢ ∀Y.Y→★` excludes) is not
     consistent with it.  GTSFImp's `lower?` agrees, checked by
     `refl`: it finds a lower bound for `∀Y.Y→Y ∼ ∀X.X→X` and none for
     `∀Y.Y→★ ∼ ∀X.X→X`.  Closed types have only `CrossFree` evidence,
     so `∼→∼ᵘ` (`proof/Consistency2.agda`) rules out declarative
     evidence for the latter as well.  So the probe's pair is outside
     the image of compilation.

     *`gen` does not produce it (argument, and a search).*  At a shared
     `X` (`∀X.B ⊑ ∀X.B′` by `∀⊑∀`), if the more precise evidence
     `c : A ∼ ∀X.B` handles `X`'s binder by `gen`, then so does the
     less precise `c′ : A′ ∼ ∀X.B′` (with `A ⊑ A′`).  Each alternative
     for `c′` fails:

     - `∀ᶜ` identifies a binder of `A′` with `X`.  Then on the left the
       corresponding binder of `A` faces `X`, a distinct name, and
       consistency cannot relate two distinct names.
     - `inst` leaves `X` in the target, so the same argument applies
       one level down.
     - If `A′ = ★`, then `c′ = ？(∀★) ; c″`.  `c″` cannot be `∀ᶜ`,
       because a strict `X` would face a `★` leaf.  It cannot be
       `inst` either, because `X ∉ ★`.  So `c″` is `gen`.
     - `bot-elim` needs `B′ = ★`, which does not contain `X`.

     `notes/detour/left_only_unbind.py`, on the Python model of
     GTSFImp's consistency and imprecision in `notes/detour/model.py`
     (validated against Agda in `notes/detour/REPORT.md`), searches
     every piece of declarative evidence on both sides.  It found no
     counterexample for types of size up to 6: closed (28,697 related
     pairs with a left `gen`) and with one free cross-mode name
     (35,649).  A control in which `X` is left-only (`∀⊑`) gives 343
     hits, so the search can fire.

     *But another producer exists (cambridge26 check, finding F4).*
     `Merge` can fuse two boundaries on one side only, when the other
     side has a cast between its two boundaries.  `Wrap`'s dual of the
     fused boundary then unbinds both names on that side alone.  In
     C23a the left fuses `[+Y^β][+X^α]`, and its `Wrap` dual
     `[−X^α, −Y^β]` faces the right's `[−X^α]`:

     ```
     L  (([+Y^β, +X^α] (λx:Y. ([−X^α, −Y^β] 42 ⟨−X⟩)) ⟨−Y → +X⟩) 69)
     R  (([+Y^β] ([+X^α] (λx:Y. ([−X^α] 42⟨ℕ!⟩^[Y:X∼X] ⟨−X⟩)) ⟨id(Y) → +X⟩)⟨id(Y) → id(★)⟩^[Y:X∼X] ⟨−Y → id(★)⟩) 69)
     ```

     The shared `Y` is then right-only inside, and nothing there
     mentions it, so the block is derivable.  So this row of the table
     does occur.  Restricting `W[δ ∥ δ′]` against it would make C23a
     underivable, so `W[δ ∥ δ′]` stays unrestricted.

### 12.6 The cambridge26 pairs against §12.3

`notes/cambridge-imprecision-check.md` checks the 22 pairs of
`CambridgeExamples.agda` block by block, in the format of §12.4.  19
are derivable as written.  C12, C13 and C14 are not, with any
synchronization (F3).  Findings, smallest first:

- **F1.**  `Λ⊑⟪+⟫` fixes the new name's mark at `X⊑X`.  It should
  read `W ⊕ X:m` with the mark chosen at the binder (D11).  Cg's
  right-led block needs `X⊑★`.
- **F2.**  `Λ⊑⟪+⟫` covers only a left `Λ`.  A left `gen`-cast
  ∀-value facing the right's `[+X^β] V′ ⟨c′⟩` needs the same rule,
  so it should be stated for every ∀-value through `inst_X` at the
  left's abstract cell (C2's right-led block):

  ```
    W ⊕ X:m ∣ [] ⊢² inst_X(V) ⊑ V′ : A ⊑ A′    V a ∀-value    β:=★    c′ : A′ ⇒ B′
    ────────────────────────────────────────────────────────────────── (∀⊑⟪+⟫)
    W ∣ γ ⊢² V ⊑ [+X^β] V′ ⟨c′⟩ : ∀X.A ⊑ B′
  ```

- **F3 (settled, D13).**  `ϱ` cannot be a partial bijection.  In C12
  (`I⟨inst⟩⟨gen⟩` on the right), the left's one cell `α:=ℕ` must be
  paired with two right cells: the right's `β:=ℕ`, from the
  instantiation that both sides make, and the right's `α:=★`, from
  `Inst`.  The block is

  ```
  L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
  R  (([+Y^β] ([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ⟨−Y → +Y⟩) 5)
  ```

  The outer pair needs `(αᴸ, βᴿ)`.  The inner right-only `[+X^αᴿ]`
  must rejoin the same center name, which needs `(αᴸ, αᴿ)`.  Under
  the proposed fix, each right cell has at most one left partner, and
  a left cell may have several.  With it, C12–C14 go through.

  *The mirror needs nothing (checked on the existing runs).*  Put
  `I⟨inst⟩⟨gen⟩` on the left, that is, C12's right program, against
  three less precise partners:

  - **M1:** `Cf-R` (`I★⟨gen⟩`).  The outer boundaries pair
    `(βᴸ:=ℕ, αᴿ:=ℕ)`, and the two `gen` unbinds match.  The left's
    `Inst` boundary `[+X^αᴸ]` (`αᴸ:=★`) is left-only, its name has
    mark `X⊑★`, and then `λx:X.x ⊑ λx:★.x` holds.
  - **M4:** Example 1 (`I⟨inst⟩`, with no `gen` and no `[ℕ]`).  The
    two `Inst`/`TyBeta` pairs match, giving `(αᴸ, αᴿ)`.  The left's
    `[ℕ]` is a left-only `ν`, and its `[+Y^β]` and `gen` unbind
    `[−Y^β]` are left-only too.
  - **M2:** `Cg-R` (`I★⟨gen⟩⟨inst⟩`).  The right's `Inst` cell
    `α:=★` pairs with the left's `[ℕ]` cell (`ℕ ⊑ ★`), the two `gen`
    unbinds match, and the left's `Inst` boundary is left-only.

  In all three, `ϱ` stays one-to-one.  The asymmetry comes from type
  imprecision, which has no rule with a bare variable on the less
  precise side (the same remark is in GTSFImp's
  `proof/DGG/CastTermImprecision.agda`).  So an extra left name can
  stay left-only, with the right seeing `★` (`X⊑★`).  An extra right
  name cannot stay right-only, because no left type is more precise
  than it, so it must rejoin a left name.  That rejoin is what forces
  C12's second pair.  So the fix is needed in one direction only: a
  right cell has at most one left partner, and a left cell may have
  several.
- **F4.**  A one-sided `Merge` also produces a left-only unbind of a
  shared name (§12.5, question 3).
- **D1.**  `W[δ ∥ δ′]` must say which intermediate worlds of a
  multi-entry `δ` have to be well formed, and that a name keeps its
  mark when it goes one-sided and later rejoins.
- **D2.**  `Λ⊑⟪+⟫`'s pair involves the left `Λ`'s abstract cell,
  which is not in `cells(Δ)`.  `ϱ`'s type has to allow it.

