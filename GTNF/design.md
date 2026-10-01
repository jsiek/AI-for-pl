# GTNF: a gradual νF — design draft

Status: first draft (2026-10-01).  No Agda yet.

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
from `strong-rep-nu` as well.  Status: nothing is stated in Agda yet.

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

GTNF's types are GTSFImp's, so the type-level imprecision can be ported
unchanged.  The imprecision environment `ImpEnv` is a different lattice
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
design item in the metatheory.

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

No design questions are open at the moment.  The next design item is
the cast-term imprecision `⊢²` (§9.6).

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
  in `GTNF/agda/`, and `make check` passes.  Next: the cast-term
  imprecision `⊢²` (§9.6), experimented with through `Eval`; then
  progress and preservation, then `compile-⊢`.
