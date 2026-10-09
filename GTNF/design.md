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
| conversion | `c, d` (tails `t`, middles `g, h`) | type abstraction: `seal`/`unseal` a type variable `X` against its representation | `ν X:=A.(L X)⟨c⟩` and boundaries `[δ] M ⟨c⟩` (unchanged from νF) |
| coercion | `p, q, r` | gradual typing: tag into `★`, check out of `★`, and the structural and polymorphic casts | the new cast form `M ⟨p⟩` |

A conversion never contains a coercion and a coercion never contains a
conversion.  (GTSF, GTPLC and PolyBlameI merge the two into one coercion
language; GTSFImp keeps them apart as `_⟨_⟩` versus `_↑_`/`_↓_`, and
GTNF follows GTSFImp in that respect.)  The two sorts meet only in the
reduction rules, and in exactly the following places: the instantiation
rules (`Inst`, and `TyBeta` through `inst_X`) and the two rules
for a `★`-value under a boundary (`IdDyn`, which moves the tag out, and
`TagUntagBad-⟪⟫`, which checks a tag that cannot move out).

Notation.  This document writes every kind of variable (term
variables, type variables and representation variables) with names
rather than de Bruijn indices, following the νF paper.  The Agda will
use de Bruijn indices with parallel renaming and substitution, as
`strong-rep-nu` does.  Everything marked **(new)** is an addition to
νF; everything else is νF as in the paper, restated so that this file
is self-contained.  A cast is written `M ⟨p⟩`.
It is told apart from a boundary `[δ] M ⟨c⟩` by the boundary's leading
`[δ]`, and from the conversion slot of `ν X:=A. (L X) ⟨c⟩` by the
enclosing `ν`; the metavariables also differ (`p, q, r` for coercions,
`c, d` for conversions).

**Review markers (2026-10-09):** text marked 🆕 **D31** is the
PROPOSED D31 (§C12): D28′ and D30 combined, with three adjustments.
It is not adopted; its rule set is checked in the notes
(`agda/proof/DGG/notes/D28pD30.agda`), not in the main Agda.  Text it
replaces is ~~struck through~~.  Part I shows the proposal only as
marked changes to definitions; its explanation is in Part II (§C9.2).

The file has two parts.  **Part I** gives the definitions of the
current adopted design (through D29), tersely.  **Part II** gives the
commentary: rationale, worked examples and ladders, counterexamples,
proposals, metatheory discussion, the Agda plan and the history of
decisions.  A definition links to its commentary as `(…: §Cn.m)`.
The section map at the end translates the section numbers of earlier
versions of this file (cited by the Agda and the notes).

Contents

Part I — Definitions

1. Types, representation types, type contexts
2. Conversions
3. Coercions (new)
4. Terms and typing
5. Values
6. Reduction
7. Compilation from the source language
8. Type imprecision
9. Worlds
10. Cast-term imprecision rules
11. Metatheory statements

Part II — Commentary

- C1. Coercions: provenance and modes
- C2. Values: rationale and proof sketches
- C3. Reduction: rationale
- C4. Compilation: the typing theorem
- C5. Examples of reduction (Examples 1–7)
- C6. Cast-term imprecision: explanations and ladders
- C7. Examples of cast-term imprecision (P1–P6)
- C8. Counterexamples and open defects
- C9. Sketches and proposals (interfaces, D31)
- C10. Metatheory discussion
- C11. Agda plan
- C12. Decisions taken in this draft, and open questions

Section map (old → new)

------------------------------------------------------------------------

# Part I — Definitions

The current adopted design, through D29, with the proposal D31 shown
as marked changes.

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
type `X` is tagged with the *type variable* `X` when it is injected
into `★`.  §C3.7 explains why a type variable, rather than a
representation variable, is enough to make the tag check well defined.

Well-formed types `Δ ⊢ A` are as in νF, plus `Δ ⊢ ★`:

```
  X:=α ∈ Δ                         Δ ⊢ A   Δ ⊢ B      Δ,α,X:=α ⊢ A
  ────────   ─────   ─────(new)   ──────────────     ────────────── (X, α ∉ Δ)
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
Operations and Scope Changes").  Coherence is what makes tags by type
variable work; it says that, inside `δ⁺(Δ)`, type variables and
representation variables are in bijection:

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
except when the tag `G` is a type variable that only the boundary
binds.  In that case the boundary is the only thing that keeps the tag
in scope, and the term is a value (§5, §C3.7, Example 4).

------------------------------------------------------------------------

## 3. Coercions (new)

### Grammar

```
Labels       ℓ
Coercions    p, q, r ::= id(A)            identity, at an atom A ::= X | ι | ★ (D21)
                       | G!               tag (inject into ★)
                       | G?ℓ              check a tag (project out of ★)
                       | p → q            function
                       | ∀X. p            under a type binder
                       | inst X. p        instantiate a ∀ at ★ (implicit instantiation)
                       | gen X. p         generalize to a ∀ (implicit generalization)
                       | p ; G!           tag after a coercion   (evidence-shaped, D20)
                       | G?ℓ ; p          check before a coercion
                       | bot-elim         ∀X. X ⇒ ∀X. ★
                       | bot-intro ℓ      ∀X. ★ ⇒ ∀X. X  (always blames)
Inert coercions  P ::= G! | p → q | ∀X. p | gen X. p
Modes            m ::= X∼X | X∼★ | ★∼X | ★∼X∼★
Mode envs        μ ::= [] | μ, X:m
Gen-safe         GenSafe(p)  iff  p is  q → r,  ∀X. q,  inst X. q,  or  gen X. q with GenSafe(q)
```

(Provenance of the names, and what `GenSafe` is for: §C1.1.)

`src(p)` and `trg(p)` are computed syntactically (`src(id A) = A`,
`src(G!) = G`, `src(G?ℓ) = ★`, `src(p → q) = trg(p) → src(q)`,
`src(∀X.p) = ∀X.src(p)`, `src(inst X.p) = ∀X.src(p)`,
`src(gen X.p) = src(p)`, `src(p ; G!) = src(p)`, `src(G?ℓ ; p) = ★`,
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
  Δ ⊢ A    A an atom            Δ ⊢ G   G ≠ X              Δ ⊢ G   G ≠ X
  ──────────────────────        ──────────────────         ────────────────────
  Δ ; μ ⊢ id(A) : A ⇒ A         Δ ; μ ⊢ G! : G ⇒ ★         Δ ; μ ⊢ G?ℓ : ★ ⇒ G

  Δ ⊢ X   μ(X) ∈ {X∼★, ★∼X∼★}         Δ ⊢ X   μ(X) ∈ {★∼X, ★∼X∼★}
  ───────────────────────────          ───────────────────────────
  Δ ; μ ⊢ X! : X ⇒ ★                   Δ ; μ ⊢ X?ℓ : ★ ⇒ X

  Δ ; flip(μ) ⊢ p : A′ ⇒ A    Δ ; μ ⊢ q : B ⇒ B′
  ─────────────────────────────────────────────
  Δ ; μ ⊢ p → q : A → B ⇒ A′ → B′

  Δ, α, X:=α ; μ, X:X∼X ⊢ p : A ⇒ B
  ─────────────────────────────────────── (X, α ∉ Δ)
  Δ ; μ ⊢ ∀X. p : ∀X. A ⇒ ∀X. B

  Δ,α,X:=α ; μ,X:X∼★ ⊢ p : A ⇒ B  Δ ⊢ B  A not a var.  X ∈ A  B ≠ ★
  ────────────────────────────────────────────────────────────────── (X, α ∉ Δ)
  Δ ; μ ⊢ inst X. p : ∀X. A ⇒ B

  Δ,α,X:=α ; μ,X:★∼X ⊢ p : A ⇒ B
  Δ ⊢ A   B not a var.   X ∈ B   A ≠ ★   GenSafe(p)
  ───────────────────────────────────────────────── (X, α ∉ Δ)
  Δ ; μ ⊢ gen X. p : A ⇒ ∀X. B

  Δ ; μ ⊢ p : A ⇒ G    G! allowed by μ    A ≠ ★
  ─────────────────────────────────────────────   (GTSFImp `_!`)
  Δ ; μ ⊢ p ; G! : A ⇒ ★

  G?ℓ allowed by μ    Δ ; μ ⊢ p : G ⇒ B    B ≠ ★
  ─────────────────────────────────────────────   (GTSFImp `？_`)
  Δ ; μ ⊢ G?ℓ ; p : ★ ⇒ B

  ─────────────────────────────────      ───────────────────────────────────
  Δ ; μ ⊢ bot-elim : ∀X. X ⇒ ∀X. ★      Δ ; μ ⊢ bot-intro ℓ : ∀X. ★ ⇒ ∀X. X
```

A cast carries its mode environment, written `M ⟨p⟩^μ` (§4).  Why
modes are in the cast calculus: §C1.2; how compilation and reduction
set a cast's `μ`: §C1.3.

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
  (∀Y. p)[★/X]    = ∀Y. p[★/X]     (inst Y. p)[★/X] = inst Y. p[★/X]
  (gen Y. p)[★/X] = gen Y. p[★/X]
  (p ; X!)[★/X]   = p[★/X]         (p ; G!)[★/X]   = p[★/X] ; G!    if G ≠ X
  (X?ℓ ; p)[★/X]  = p[★/X]         (G?ℓ ; p)[★/X]  = G?ℓ ; p[★/X]   if G ≠ X
  bot-elim[★/X]   = bot-elim            (bot-intro ℓ)[★/X] = bot-intro ℓ
```

Closing a sequence re-normalizes, as GTSFImp's `subst∼` does
(`subst-to-star-var`, `factor-inst-star`): a tag or check of `X`
itself disappears.  If `Δ, α, X:=α ; μ, X:m ⊢ p : A ⇒ B` for any mode
`m`, then `Δ ; μ ⊢ p[★/X] : A[★/X] ⇒ B[★/X]`.  (Why it needs the
evidence-shaped sequences of D20, and why every `m`: §C1.4.)

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
  ────────────────────────── (TyAbs)
  Δ ∣ Γ ⊢ ΛX. V : ∀X. A

  Δ ⊢ A    Δ ∣ Γ ⊢ L : ∀X. C    Δ, α:=Δ(A), X:=α ⊢ c : C ⇒ B    Δ ⊢ B
  ────────────────────────────────────────────────────────────────────── (Inst)
  Δ ∣ Γ ⊢ ν X:=A. (L X) ⟨c⟩ : B

  Δ ⊢ δ    δ(Δ) ∣ [] ⊢ M : A    δ⁺(Δ) ⊢ c : A ⇒ B    Δ ⊢ B
  ───────────────────────────────────────────────────────── (Boundary)
  Δ ∣ Γ ⊢ [δ] M ⟨c⟩ : B
```

New rules:

```
  Δ ∣ Γ ⊢ M : A    Δ ; μ ⊢ p : A ⇒ B            Δ ⊢ A
  ────────────────────────────────── (Cast)    ─────────────────── (Blame)
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

(Why the new value form is the only boundary left around a `★`-value:
§C2.1; why a value with an inert cast counts as a simple: §C2.3, D2.)

`fresh(δ)` gives a syntactic form of `IdDyn`'s side condition `Δ ⊢ G`.  If
`Δ ⊢ δ` and `δ(Δ) ⊢ X`, then

```
Δ ⊢ X    if and only if    X ∉ fresh(δ)
```

(Proof sketch, and why `fresh(δ)` rather than `Δ ⊢ X`: §C2.2.)

The modes give GTSFImp's emptiness lemma, which the progress and DGG
proofs use (§C1.2):

```
no-bot-value :  if V is a value, then not (Δ ∣ Γ ⊢ V : ∀X. X)
```

(Proof sketch: §C2.4.)

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

### 6.2 The reduction rules from νF

`Delta`, `Beta`, `Wrap`, `Merge`, `Id` and `ξ` are verbatim from νF,
except that `Merge`'s inner boundary may now also be the new value form
`[δ₁] (V⟨X!⟩) ⟨id(★)⟩` (`t₁ = id(★)`).  The merged boundary may no
longer introduce `X`, in which case `IdDyn` fires next (Example 5).
`TyBeta` is generalized from a `Λ` to any ∀-value, through a
meta-operation `inst_X(V)` that instantiates a ∀-value `V` at the type
variable `X` by reaching through all of its layers:

```
inst_X(ΛX. V)            = V
inst_X(W ⟨gen X. p⟩^μ)   = ([−X^α] W ⟨Id(A)⟩) ⟨p⟩^(μ, X:★∼X)     (W : A)
inst_X(W ⟨∀X. p⟩^μ)      = inst_X(W) ⟨p⟩^(μ, X:X∼X)
inst_X([δ] U ⟨∀X. c⟩)    = [δ] inst_X(U) ⟨c⟩          (X not mentioned by δ)
```

Here `α` is the representation variable that `TyBeta` allocates for
`X`, so `inst_X` is really `inst_X^α`.

(No term moves under a new type variable: §C3.1, D9; how `inst_X`
recurses and why it allocates nothing: §C3.2.)

```
Δ ⊢ op(k̅) ⟶ ⟦op⟧(k̅) ⊣ ε                                                (Delta)

Δ ⊢ (λx:A. N) V ⟶ N[x:=V] ⊣ ε                                           (Beta)

Δ ⊢ ([δ] U ⟨c → d⟩) W ⟶ [δ] (U ([−δ] W ⟨c⟩)) ⟨d⟩ ⊣ ε                    (Wrap)

Δ ⊢ ν X:=A. (V X) ⟨d⟩ ⟶ [+X^α] inst_X(V) ⟨d⟩ ⊣ α:=Δ(A)                (TyBeta)
      V a ∀-value; α fresh

Δ ⊢ [δ₂] ([δ₁] U ⟨t₁⟩) ⟨c₁⟩ ⟶ [δ₂ ++ δ₁] U ⟨d⟩ ⊣ ε                    (Merge)
      where [δ₁] U ⟨t₁⟩ is a value and (δ₂ ++ δ₁)⁺(Δ) ⊢ t₁ ⨟ c₁ = d

Δ ⊢ [δ] U ⟨id(ι)⟩ ⟶ U ⊣ ε                                              (Id)

Δ ⊢ F[M] ⟶ F[M′] ⊣ ξ     if  F(Δ) ⊢ M ⟶ M′ ⊣ ξ                        (ξ)
```

(How this `TyBeta` covers νF's `TyBeta` and `TyWrap` and GTSFImp's
`β-gen` and `β-∀`: §C3.3.)

Preservation of `TyBeta` rests on one lemma, proved by induction on the
∀-value:

```
if  Δ ∣ [] ⊢ V : ∀X. C,  V a ∀-value,  and  α:=R ∈ Δ  with  X, α fresh,
then  Δ, X:=α ∣ [] ⊢ inst_X(V) : C
```

(Proof sketch: §C3.4.)

### 6.3 Cast rules (new)

```
Δ ⊢ V ⟨id(A)⟩ ⟶ V ⊣ ε                                                (CastId)

Δ ⊢ V ⟨p ; q⟩^μ ⟶ V ⟨p⟩^μ ⟨q⟩^μ ⊣ ε                                 (CastSeq)

Δ ⊢ (V ⟨p → q⟩^μ) W ⟶ (V (W ⟨p⟩^flip(μ))) ⟨q⟩^μ ⊣ ε                 (CastFun)

Δ ⊢ V ⟨inst X. p⟩^μ ⟶ (ν X:=★. (V X) ⟨reveal_X(src(p))⟩) ⟨p[★/X]⟩^μ ⊣ ε   (Inst)
      where  p : A ⇒ B  under  μ, X:X∼★,  with V : ∀X. A,  X ∉ B,
             A = src(p),  B = trg(p)

Δ ⊢ V ⟨G!⟩ ⟨G?ℓ⟩ ⟶ V ⊣ ε                                            (TagUntag)

Δ ⊢ V ⟨G!⟩ ⟨H?ℓ⟩ ⟶ blame ℓ ⊣ ε        if G ≠ H                   (TagUntagBad)

Δ ⊢ [δ] (V ⟨G!⟩^μ) ⟨id(★)⟩ ⟶ ([δ] V ⟨Id(G)⟩) ⟨G!⟩^exit_δ(μ) ⊣ ε        (IdDyn)
      if G ∉ fresh(δ)            (equivalently, on well-typed terms, Δ ⊢ G)

exit_δ(μ)(Y) = μ(Y)    if Y is visible in the interior δ(Δ)
             = X∼X     otherwise

Δ ⊢ ([δ] (V ⟨X!⟩) ⟨id(★)⟩) ⟨H?ℓ⟩ ⟶ blame ℓ ⊣ ε                (TagUntagBad-⟪⟫)
      if X ∈ fresh(δ)

Δ ⊢ V ⟨bot-intro ℓ⟩ ⟶ blame ℓ ⊣ ε                              (BlameBotIntro)

Δ ⊢ F[blame ℓ] ⟶ blame ℓ ⊣ ε                                           (Blame)
```

(Correspondence with GTSFImp's rules: §C3.5; how `Inst` works through
`ν` and `TyBeta`: §C3.6; why a tag by type variable keeps its meaning
across a boundary: §C3.7, D3.)

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
⟦id A⟧ℓ        = id(A)              (A an atom, as in GTSFImp's `id`)
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

(The theorem is `compile-⊢`, §11.2; what its proof needs: §C4.)

------------------------------------------------------------------------

## 8. Type imprecision

Status (2026-10-06): §8 is `Imprecision.agda`; the worlds (§9)
are `ImprecisionWorld.agda`; the rules (§10) are `TermImprecision.agda`
and `ConversionImprecision.agda`, current through D29.  Known open
defect: the gen-value pairs of `proof/DGG/notes/TwoGen.md` (G0 and six
more, from related sources) are DGG-part-1 counterexamples for these
rules (§C8.1).  🆕 **D31** relates all seven (§C9.2).
The left program is always the **more precise** one.

GTSFImp's `Imprecision.agda`, copied rule for rule into
`GTNF/agda/Imprecision.agda`.  The marks are `X⊑X` and `X⊑★`, and an
imprecision environment `μ` gives one mark to each type variable in
scope (a map from type variables to marks; `μ, X:m` extends it with a
fresh `X`).  In the Agda it is a list parallel to the type variables,
index 0 at the head.

```
                                                        μ(X) = X⊑★
  ★ ⊑ ★     ι ⊑ ι     X ⊑ X     ι ⊑ ★     ∀X.★ ⊑ ★       ──────────
                                                         X ⊑ ★

  A ⊑ A′   B ⊑ B′          A ⊑ ★   B ⊑ ★          μ, X:X⊑X ⊢ A ⊑ B
  ─────────────────        ─────────────          ─────────────────
  A → B ⊑ A′ → B′          A → B ⊑ ★              μ ⊢ ∀X.A ⊑ ∀X.B

  μ, X:X⊑★ ⊢ A ⊑ B    A not a variable    X ∈ A     (∀⊑)
  X not free in B
  ───────────────────────────────────────────────
  μ ⊢ ∀X.A ⊑ B

  μ, X:X⊑X ⊢ A ⊑ ★    A ≠ ★
  ──────────────────────────     ∀X.X ⊑ ∀X.★  (bot-elim)     ∀X.X ⊑ ★
  μ ⊢ ∀X.A ⊑ ★
```

The marks belong to the imprecision lattice.  They are not the
consistency modes of §3, which type the casts inside one program
(§C10.1).

------------------------------------------------------------------------

## 9. Worlds

A cast-term imprecision judgment relates a left term typed in `Δ` to a
right term typed in `Δ′`.  The two runs allocate independently, and a
`ν`, a `Λ` or a boundary entry may exist on one side only.  A
**world** says how the two sides' type variables line up.  It follows
GTSFImp's `World` (`proof/DGG/CtxImp.agda`), minus the stores:

```
W = (Δ, Δ′, Ω, η, η′, ϱ, κ, π)      🆕 D31: no π

  Ω              the center: a finite set of center type variables
  η  : tyvars(Δ)  ↪ Ω    injective maps from each side's type
  η′ : tyvars(Δ′) ↪ Ω    variables in scope to center type variables
                         (GTSFImp ηᴸʷ, ηᴿʷ); every center type
                         variable is in the image of at least one
                         of them
  κ              the permitted right rep. vars (D28); [] at every
                 top-level world; ~~a right check adds one (⊑cast)~~
                 🆕 **D31**: only a boundary rule adds to κ, for
                 its interior: rep. vars of type variables it
                 JOINS (W +κ K, §10.5)
  μ  = marks(W)          DERIVED (D28): a type variable in η's image
                         only (left-only) is X⊑★; a type variable in
                         η′'s image is X⊑★ iff its right rep. var is
                         in κ, else X⊑X
  ϱ  = ϱᵍ ∪ ϱˡ           the rep. var correspondence, in two parts (D16),
                         any relation whose pairs agree (D25):
                         ϱᵍ global, over the two stores' rep. vars;
                         ϱˡ lexical, over rep. vars bound by an enclosing
                         Λ or ν.  (D13's one-partner rule was dropped
                         by D25.)
  ~~π~~          ~~the pending right type variables (D27), next pop
                 first: right type variables that a ⊑⟪⟫ pushed and a
                 left binder will join; [] at every top-level world~~
                 🆕 **D31**: π leaves the world; its type variables
                 become the slots of the index (below)

  A ⊑_W A′   iff   μ ⊢ η(A) ⊑ η′(A′)     when π = []  (GTSFImp _⊑ᵂ⟨_⟩_)
             and in general A, with one outer ∀ opened at the center
             type variable of each pending type variable, against A′
```

🆕 **D31**: **the index with slots** `A ⊑_W^O A′` (Agda `OpenO`,
`_⊑ᴰ⟨_∣_⟩_`).  `O` is a list of slots, next first.  A slot opens the
next left outer `∀` at a right type variable `Y`, or SKIPS it (`_`):
the `∀` stays left-only, `X⊑★`.  (why: §C9.2)

```
  O ::= [] | s·O          s ::= Y | _

  A ⊑_W^[] A′         =  μ ⊢ η(A) ⊑ η′(A′)
  ∀X.A ⊑_W^(Y·O) A′   =  A[X:=Y] ⊑_W^O A′
  ∀X.A ⊑_W^(_·O) A′   =  A ⊑_W^O A′, with X left-only (X⊑★),
                          A not a variable, X ∈ A,
                          X not free in A′             (as ∀⊑)
  B ⊑_W^(s·O) A′      =  false, if B is not a ∀ type
```

In `A[X:=Y]`, `X` is read as `Y`'s center type variable.  `A ⊑_W A′`
is the case `O = []`.  Only `⊑⟪⟫` creates slots; `Λ⊑` and the gen
layers of a left cast consume them (§10.2, §10.3, §10.5).

In Agda (`ImprecisionWorld`) `π` is the field `πʷ` of `World`, `κ`
the field `κʷ`, and `μ` is computed, `marksʷ W = dmarks (ηᴿʷ W)
(κʷ W)`; the index `_⊑ᵂ⟨_⟩_` reads `πʷ` (`OpenImp`) and `marksʷ`.
Everything that is not about pending type variables reads only the
other fields: `Paired`, `Joins`, `Interior`, and the term-context
imprecision `CtxImp`, whose entries hold the plain `μ ⊢ η(A) ⊑ η′(A′)`
and are parameterized by the marks, `η` and `η′`.  So `W` with its
pending type variables replaced (`record W { πʷ = π }`) has the same
`CtxImp`, definitionally; a grant (`record W { κʷ = β ∷ κʷ W }`)
changes the marks, and `⊑cast` moves the entries by `RaiseCtx` (same
types, proofs at the raised marks).  The structural rules are stated
at a world in constructor form with `π = []`, where the index computes
to the plain one; the theorems are stated at `W` with `πʷ W ≡ []` and
`κʷ W ≡ []`, and an evolution keeps `π` and renumbers `κ` with the
right side (an allocation moves no type variable).

🆕 **D31**: no rule reads `πʷ` (the D31 Agda keeps the field, always
`[]`), the theorems keep only `κʷ W ≡ []`, there are no grants (so no
`RaiseCtx`), and `κ` changes only at a boundary's interior world,
`Wᵢ +κ K` (`record Wᵢ { κʷ = K ++ κʷ Wᵢ }`).

Well-formedness has five parts (🆕 **D31**: four; the pending part
becomes a condition on the index):

- **Shared type variables have paired rep. vars.**  If a center type
  variable `X` is `X:=α` on the left and `X:=β` on the right, then
  `(α, β) ∈ ϱ`.
- **Uniqueness among type variables in scope** (D25).  Among the type
  variables in scope on one side, at most one is bound to a rep. var
  paired with the rep. var of a given type variable on the other side.
  A rejoin is therefore unambiguous, although `ϱ` itself may pair a
  rep. var with several partners.
- **Paired rep. vars agree.**  If `(α, β) ∈ ϱ`, then either both are
  abstract (bound by a `Λ` on each side), or `α` is abstract and
  `β:=★`, or `α:=R`, `β:=R′`, and `R ⊑ᴿ_W R′`: the payloads are
  compared in the representation universe, free rep. vars through `ϱ`
  (D23).
- ~~**Pending type variables are pending** (D27).  Each type variable
  of `π` is bound to a `★` rep. var `β`, is right-only, and `β` has no
  left partner bound to a type variable in scope; the type variables of
  `π` are distinct.  (Its mark is derived, D28.)~~
  🆕 **D31**: **well-formed slots.**  Each opened `Y` of an index
  `A ⊑_W^O A′` is right-only and bound to a `★` rep. var that has no
  left partner bound to a type variable in scope, and the opened type
  variables are distinct.  It is checked where a slot is created, at
  `⊑⟪⟫` (Agda `SlotOK`, `SlotNe`; `WfWorldᴰ` is `WfWorld` without
  `wf-pending`, `wf-distinct`).
- **Permissions are right rep. vars** (D28).  Every rep. var in `κ` is
  a rep. var of the right store, whether or not a type variable in
  scope is bound to it (a right `−X` keeps its permission, P4 B4).
  R1/R2 (§10.5, §10.6) are rule premises, not parts of well-formedness.

**Type variables are related lexically; rep. vars lexically and
globally** (D12, D16).  The relation between type variables (`Ω`, `η`,
`η′`, `μ`) is lexically scoped: it is extended and shrunk with the
scope, never by a step.  Rep. vars come from two places, so their
relation has two parts:

- **Lexical, `ϱˡ`.**  A `Λ` binds an abstract rep. var for its body
  (`⊢Λ` types the body at `underΛ Δ`).  A `ν X:=A` binds the rep. var
  for its conversion (`⊢ν` types `c` at `allocate R Δ`).  A rule that
  goes under such binders on both sides pairs their rep. vars for the
  premise only: `Λ⊑Λ` pairs two abstract rep. vars; `Λ⊑`'s pop pairs
  the left binder's abstract rep. var with the `β:=★` of the pending
  type variable it joins (D27; 🆕 **D31**: of the opening it joins),
  and its claim-rep with a `β:=★` to
  which no right type variable is bound yet (D29); `ν⊑ν` pairs the two
  `ν`s' rep. vars.
- **Global, `ϱᵍ`.**  A store rep. var is created by a step (`TyBeta`)
  and is visible everywhere afterwards.  When the two sides' `TyBeta`s
  are matched, the lexical pair of the two `ν`s becomes a global pair.
  When a left `TyBeta` catches up with a right boundary whose type
  variable its binder popped or claimed, the left's lexical abstract
  rep. var is replaced by the new store rep. var, which is paired
  globally with the right's `β` (Evolve's `ev-L⇔`).

(An example, P3's block, and why no part of a world is ever rebased:
§C6.1.)

### 9.1 World operations

Every operation is given by what it does to each component of
`W = (Ω, η, η′, ϱᵍ, ϱˡ, κ, π)` (🆕 **D31**: no `π`); a component not
mentioned is unchanged.
The marks `μ` are never set: they are recomputed from `η′` and `κ`
(D28).  In this account variables have names: "`X ↦ Z`" means that
the type variable `X` is embedded as the center type variable `Z`.  (In
the Agda the same operations also renumber de Bruijn positions; that
renumbering moves no type variable.)

**Notation used in the rules.**  Every way §10 writes a world, with
where it is defined:

| written | meaning | defined |
|---|---|---|
| `W` | a world whose pending list `π` is empty (🆕 **D31**: a world; there is no `π`) | §9 |
| ~~`W.π := π′`~~ | ~~`W` with its pending list set to `π′` (field update)~~ | here |
| ~~`W.π := Y·π′`~~ | ~~the pending list `π′` with `Y` in front (the next pop)~~ | here |
| ~~`W.π := [Y]`~~ | ~~exactly one pending type variable~~ | here |
| 🆕 **D31** `A ⊑_W^O A′` | the index with slots `O` (`Y` opens, `_` skips); `A ⊑_W A′` is `O = []` | §9 |
| `W ⊕ (X:α ∥ X′:α′)` | both sides bind (left `X` with abstract rep. var `α`, right `X′` with `α′`) | binders, below |
| `W ⊕ (X:α ∥ ·)` | the left side alone binds `X` | binders, below |
| `W ⊕ (X:α⇔β ∥ ·)` | as `W ⊕ (X:α ∥ ·)`, claiming the right rep. var `β` | binders, below |
| `W ⊕ (· ∥ X′:α′)` | the right side alone binds `X′` | binders, below |
| `W[δ ∥ δ′]` | the interior world of a boundary pair | interior, below |
| `W[δ ∥ ·]`, `W[· ∥ δ′]` | the interior world of a left-only / right-only boundary | interior, below |
| ~~`W[δ ∥ ·].π := π′`~~ | ~~that interior world, with pending list `π′`~~ | combines the rows above |
| ~~`W[· ∥ δ′].π := π′ ++ new`~~ | ~~that interior world, with the carried type variables `π′` then the pushed type variables `new`~~ | §10.5 (`⊑⟪⟫`) |
| `W[X:α ↦ Y]` | the pop of `Y` by the left binder `X` (abstract rep. var `α`); 🆕 **D31**: the join of the opening `Y` | pops, below |
| ~~`W[X:α ↦ Y].π := π′`~~ | ~~that pop, with the remaining pending list `π′`~~ | combines the rows above |
| ~~`W +κ β`~~ | ~~`W` with `β` added to `κ` (a grant)~~ | grants, below; §10.2 |
| 🆕 **D31** `Wᵢ +κ K` | the interior world `Wᵢ` with the rep. vars `K` added to `κ`; only at a boundary rule, `K` ⊆ the rep. vars of type variables it joins | §10.5 |
| `Wᶜ` | the world over the two conversion contexts | conversion worlds, below |
| `W +ˡ (α, α′)` | `W` with `(α, α′)` added to `ϱˡ` (the conversion world of `ν⊑ν`) | allocation, below |
| `W +ᵍ (α, α′)` | `W` with `(α, α′)` added to `ϱᵍ` (a matched allocation) | allocation, below |

In the Agda, `W.π := π′` is `record W { πʷ = π′ }`, and a grant is
`record W { κʷ = β ∷ κʷ W }`.  🆕 **D31**: neither exists; `π`
becomes the slots `O` of the index, and `Wᵢ +κ K` is `_+κ_`.

The term context `γ` has one operation, `γ, x : B ⊑ B′` (extend, in
`ƛ⊑ƛ`).  With named variables, `γ` is used unchanged under a binder and
under a grant: a binder's type variable and rep. var are fresh, so no
entry mentions them, and a grant only raises marks from `X⊑X` to `X⊑★`,
which keeps every entry's `B ⊑ B′` (the de Bruijn version needs `⇑γ`,
`⇑ᴸγ` and `RaiseCtx` for these).

**Binders on one or both sides** (`Λ⊑Λ`, `Λ⊑`; Agda `_⊕²`, `_⊕ᴸ`,
`_⊕ᴸ⇔_`, `_⊕ᴿ`).  A `Λ` binds a type variable together with a fresh
abstract rep. var (`⊢Λ` types the body at `Δ, X:α`).  The operation
writes both, the type variable and its rep. var: `X:α` on the left,
`X′:α′` on the right.  In every row, `Z` is fresh.

| op | `Ω` | `η` | `η′` | `ϱˡ` |
|---|---|---|---|---|
| `W ⊕ (X:α ∥ X′:α′)` | add `Z` | add `X ↦ Z` | add `X′ ↦ Z` | add `(α, α′)` |
| `W ⊕ (X:α ∥ ·)` | add `Z` | add `X ↦ Z` | — | — |
| `W ⊕ (X:α⇔β ∥ ·)` | add `Z` | add `X ↦ Z` | — | add `(α, β)` |
| `W ⊕ (· ∥ X′:α′)` | add `Z` | — | add `X′ ↦ Z` | — |

- Both sides: `Z` is shared; `α′` is not in `κ`, so `Z` is `X⊑X`.
- Left only: `Z` is left-only, so `X⊑★`; `α` is unpaired.
- Claim-rep (D29): as left only, and `α` is paired with the right rep.
  var `β:=★`, to which no right type variable is bound yet.  A later
  right boundary entry `+Y^β` joins `Y` to `Z` (`W[δ ∥ δ′]` below).
- Right only: `Z` is right-only (no rule of §10 uses it).
- (Agda: `W ⊕²`, `W ⊕ᴸ`, `W ⊕ᴸ⇔ β`, `W ⊕ᴿ`; with de Bruijn indices
  the binder and its rep. var are position 0 and need no name.)

**Rep. var pairs** (allocation, between steps, and the conversion
world of `ν⊑ν`).  A world holds no stores, so a new rep. var changes
no component by itself; the only world change is a new pair:

| op | `ϱᵍ` | `ϱˡ` | used for |
|---|---|---|---|
| `W +ᵍ (α, α′)` | add `(α, α′)` | — | a matched pair of `TyBeta`s allocating `α:=R`, `α′:=R′` |
| `W +ᵍ (α, β)` | add `(α, β)` | — | a left `TyBeta` (`α:=R`) catching up with a right boundary `+Y^β` whose type variable a left binder popped or claimed |
| `W +ˡ (α, α′)` | — | add `(α, α′)` | the conversion world of `ν⊑ν`: the two `ν`s' rep. vars |

An unmatched `TyBeta` (one side only) leaves `W` unchanged; only that
side's context grows.  (Agda: `alloc²`, `allocᴸ⇔`, `underν²`, and
`allocᴸ`, `allocᴿ`, which only renumber de Bruijn indices.)

**The interior world `W[δ ∥ δ′]`** (all boundary rules; Agda `Interior`,
a relation).  `δ` acts on the left type variables, `δ′` on the right
type variables; `ϱᵍ`, `ϱˡ` and `κ` are unchanged.  Each entry, on its
own side:

| entry | effect |
|---|---|
| `−X^α` | `X` leaves that side's embedding; a center type variable in neither embedding is dropped |
| `+X^α`, rejoin | if a type variable `X′` on the other side, in scope inside, is bound to a rep. var paired with `α` in `ϱ`: `X ↦` the center type variable of `X′` |
| `+X^α`, fresh | otherwise: add `Z`, `X ↦ Z`, one-sided, with `Z` fresh |
| a type variable no entry touches | keeps its center type variable; two continuing type variables are joined inside iff they are joined outside |

- ~~`π` (D27): a pending type variable stays pending inside, under the
  same type variable; a pending type variable that `δ′` unbinds must
  have been popped before.~~  🆕 **D31**: the world has no `π`; the
  slots of the index are carried by `⊑⟪⟫` (§10.5).
- Uniqueness among type variables in scope (D25) makes the rejoin
  unambiguous.
- `W[δ ∥ ·]` and `W[· ∥ δ′]` are the one-sided cases.
- Only the final interior world must be well formed, not the worlds
  between the entries of a multi-entry `δ`.
- 🆕 **D31**: the boundary rule may then add `K` to `κ`, the right
  rep. vars of type variables this boundary joins (`Wᵢ +κ K`, §10.5).

The marks follow: a type variable that goes one-sided and later rejoins
gets its derived mark back (D28, superseding D15); a right-only `−X` of
a shared type variable leaves `X` left-only, hence `X⊑★` (Example P4).

**Pops** (D27; Agda `Open1`, `Join↪`).  `W[X:α ↦ Y]`, for the next
pending type variable `Y` (bound to `β:=★`) and a left binder `X` with
abstract rep. var `α`:

| `Ω` | `η` | `η′` | `ϱˡ` | `π` |
|---|---|---|---|---|
| — | add `X ↦ η′(Y)` | — | add `(α, β)` | remove `Y` (🆕 **D31**: no `π`) |

🆕 **D31**: the same operation is the JOIN of the next opening `Y` of
the index (Agda `Join1`, `Open1` without the `π` update); `Λ⊑` takes
`Y` off the index itself (§10.3).

The center type variable of `Y` was right-only and becomes shared.
(Agda `W ⊕⁺^ β` is a push of `+Y^β`'s type variable followed by this
pop.)

**Conversion worlds `Wᶜ`** (`ν⊑ν`, `⟪⟫⊑⟪⟫`, §10.6; Agda
`ConversionInterior`, `underν²`).  A conversion is read in its own
context, which keeps every exterior type variable and adds one type
variable for each rep. var its boundary binds that no exterior type
variable is bound to yet; an unbind removes no type variable.

| for | `Ω`, `η`, `η′` | `ϱᵍ`, `ϱˡ`, `κ` |
|---|---|---|
| `⟪⟫⊑⟪⟫` | as `W`, plus one center type variable per rep. var newly bound to a type variable, shared iff the two rep. vars are paired in `ϱ` | unchanged |
| `ν⊑ν` (`W +ˡ (α, α′)`) | as `W` | the two `ν`s' rep. vars added, paired in `ϱˡ` |

The conversion clauses then go under binders with
`Wᶜ ⊕ (X:α ∥ X′:α′)` (both sides' `∀`) and `Wᶜ ⊕ (X:α ∥ ·)` (a
left-only `∀`).

**Grants** (D28; `⊑cast`, §10.2).  `W +κ β` adds `β` to `κ`; nothing
else changes, so the marks of the type variables bound to `β` become
`X⊑★`.  🆕 **D31**: ~~grants~~ go; the same addition happens only at
a boundary rule, as `Wᵢ +κ K` for its interior (§10.5).

------------------------------------------------------------------------

## 10. Cast-term imprecision rules

### 10.1 The judgment, congruence and blame

`W ∣ γ ⊢ M ⊑ M′ : A ⊑ A′` with `γ ::= [] | γ, x : B ⊑ B′`.  Every
rule also assumes the two typings `Δ ∣ γᴸ ⊢ M : A` and
`Δ′ ∣ γᴿ ⊢ M′ : A′` and `A ⊑_W A′`; the premises below list only what
is new.  🆕 **D31**: the judgment is `W ∣ γ ⊢ M ⊑ M′ : A ⊑_W^O A′`;
writing no `O` means `O = []`.  The congruence rules, `blame⊑`,
`cast⊑cast`, `Λ⊑Λ`, the `ν` rules and `⟪⟫⊑⟪⟫` are stated at `O = []`.
The rules marked "GTSFImp" are GTSFImp's
`proof/DGG/CastTermImprecision.agda` rules with the same name.

**Congruence** (GTSFImp `x⊑x²`, `κ⊑κ²`, `ƛ⊑ƛ²`, `·⊑·²`, `⊕⊑⊕²`):
the usual rules, one per term former.  Their types are related
componentwise.

**Blame** (GTSFImp `blame⊑²`):

```
  ────────────────────────────── (blame⊑)
  W ∣ γ ⊢ blame ℓ ⊑ M′ : A ⊑ A′
```

### 10.2 Casts

🆕 **D31**: ~~grants~~ go: no cast rule changes the world.  The
`Grants` definition below is D28's.

**Grants** (D28).  A right coercion `p′` *grants* a right rep. var
`β` when every value that leaves a cast through `p′` is checked
against the right type variable bound to `β`.  Inductively (Agda
`Grants`):

```
  X the right type variable of β
  ─────────────────────────────── (gr-?)
  X?ℓ grants β

  X the right type variable of β
  ─────────────────────────────── (gr-?;)
  (X?ℓ ; q) grants β

  q₁ first order    q₂ grants β
  ───────────────────────────── (gr-→)
  q₁ → q₂ grants β

  first order:  id(A),  G!,  G?ℓ
```

So P4's gen wrapper `X! → X?` grants `X`'s rep. var (its codomain
checks `X`), and C2's `X! → id(★)` grants nothing.  (Why: §C6.2.)

**Casts** (GTSFImp `cast⊑cast²`, `cast⊑²`, `⊑cast²`).  Each coercion
is typed on its own side, under the mode environment its cast carries.
The rules do not compare the two coercions, or the two mode
environments, except through the types:

```
  W ∣ γ ⊢ M ⊑ M′ : B ⊑ B′
  p : B ⇒ A    p′ : B′ ⇒ A′
  ──────────────────────────────── (cast⊑cast)
  W ∣ γ ⊢ M ⟨p⟩ ⊑ M′ ⟨p′⟩ : A ⊑ A′

  W ∣ γ ⊢ M ⊑ M′ : B ⊑ A′    p : B ⇒ A
  ───────────────────────────────── (cast⊑)
  W ∣ γ ⊢ M ⟨p⟩ ⊑ M′ : A ⊑ A′

  W⁺ ∣ γ ⊢ M ⊑ M′ : A ⊑ B′    p′ : B′ ⇒ A′
  W⁺ = W,  or  W⁺ = W +κ β  if p′ grants β
  ──────────────────────────────── (⊑cast, D28)
  W ∣ γ ⊢ M ⊑ M′ ⟨p′⟩ : A ⊑ A′
```

(What a grant means: §C6.2.)

With pending type variables (D27), `⊑cast` carries them unchanged, and
`cast⊑` has two more forms, for a value `M`:

```
  W.π := Y·π ∣ γ ⊢ M ⊑ M′ : ∀X.B ⊑ A′        ∀X.p : ∀X.B ⇒ ∀X.A
  ─────────────────────────────────────────────────── (cast⊑, pass ∀)
  W.π := Y·π ∣ γ ⊢ M ⟨∀X.p⟩ ⊑ M′ : ∀X.A ⊑ A′

  W ∣ γ ⊢ M ⊑ M′ : B ⊑ A′        gen X.p : B ⇒ ∀X.A
  ─────────────────────────────────────────────────── (cast⊑, pop gen)
  W.π := [Y] ∣ γ ⊢ M ⟨gen X.p⟩ ⊑ M′ : ∀X.A ⊑ A′

  (an index ∀X.… ⊑ A′ at a world with pending type variables is read
   with its outer ∀ opened at the next pending type variable;
   corrected 2026-10-07: the earlier display wrote the bodies B, A for
   the cast's types)
```

The gen pop leaves the base world unchanged: the value under a `gen`
does not see the binder.  One gen pops one pending type variable.

🆕 **D31** replaces D28's `⊑cast` and the three forms of `cast⊑` by
the two rules below.  `⊑cast` is GTSFImp's plain rule and keeps the
slots; `cast⊑` is one rule whose premise slots follow the coercion's
binder layers (`CastOpen`).  `cast⊑cast` is unchanged.  (why: §C9.2)

```
  W ∣ γ ⊢ M ⊑ M′ : A ⊑_W^O B′
  p′ : B′ ⇒ A′
  ──────────────────────────────── (⊑cast, D31)
  W ∣ γ ⊢ M ⊑ M′ ⟨p′⟩ : A ⊑_W^O A′

  W ∣ γ ⊢ M ⊑ M′ : B ⊑_W^Oₚ A′
  p : B ⇒ A
  opens(p, O) = Oₚ
  M a value, unless O = []
  ──────────────────────────────── (cast⊑, D31)
  W ∣ γ ⊢ M ⟨p⟩ ⊑ M′ : A ⊑_W^O A′
```

`opens` (Agda `CastOpen`) is the partial function

```
  opens(p,       [])   = []                 any p
  opens(∀X.p,    s·O)  = s · opens(p, O)    the ∀ layer passes s
  opens(gen X.p, s·O)  = opens(p, O)        the gen layer uses s up
```

undefined otherwise (a coercion with no binder layer, given a slot).
`s` is any slot, an opening or a skip.  (Agda cases: `co-plain`,
`co-∀`, `co-gen`.)

### 10.3 Type abstraction

**Type abstraction** (GTSFImp `Λ⊑Λ²`, `Λ⊑²`), plus one new rule.
`Λ⊑` keeps the right term unweakened: the right side does not bind
`X`, so `η′` simply does not reach the new center type variable.

```
  W ⊕ (X:α ∥ X′:α′) ∣ γ ⊢ V ⊑ V′ : A ⊑ A′
  α, α′ fresh
  ───────────────────────────────────── (Λ⊑Λ)
  W ∣ γ ⊢ ΛX.V ⊑ ΛX′.V′ : ∀X.A ⊑ ∀X′.A′

  W ⊕ (X:α ∥ ·) ∣ γ ⊢ V ⊑ M′ : A ⊑ B′
  α fresh    A not a variable    X ∈ A
  ───────────────────────────────── (Λ⊑, fresh)
  W ∣ γ ⊢ ΛX.V ⊑ M′ : ∀X.A ⊑ B′

  W[X:α ↦ Y].π := π ∣ γ ⊢ V ⊑ M′ : A ⊑ B′
  α fresh    A not a variable    X ∈ A
  ───────────────────────────────── (Λ⊑, pop)
  W.π := Y·π ∣ γ ⊢ ΛX.V ⊑ M′ : ∀X.A ⊑ B′
```

```
  W ⊕ (X:α⇔β ∥ ·) ∣ γ ⊢ V ⊑ M′ : A ⊑ B′
  α fresh    A not a variable    X ∈ A
  β:=★ in Δ′    no right type variable bound to β in scope
  no left partner of β bound to a type variable in scope
  ──────────────────────────────────────────────────────── (Λ⊑, claim-rep, D29)
  W ∣ γ ⊢ ΛX.V ⊑ M′ : ∀X.A ⊑ B′
```

Here `W.π := π` is a world with the pending type variables `π` (D27), and
`W` alone means no pending type variable.  In the pop, `Y` is the next
pending type variable and `W[X:α ↦ Y]` joins the binder `X` to it
(`Open1`).  The left's abstract rep. var is paired lexically with
`Y`'s `β:=★`.  The type `∀X.A ⊑ B′` of a world with pending type
variables is read with one `∀` opened per pending type variable.

🆕 **D31** replaces the three `Λ⊑` forms by one rule whose binder is
fresh, a JOIN, or claim-rep (the function `bind` below; Agda `Bind`).  Fresh and claim-rep are
the forms above, at `O = []`.  The join is the old pop: it consumes
the next opening of the index, and the world changes there, at a term
binder.  It takes no permission (the permission of an opening is
chosen where the opening is created, at `⊑⟪⟫`, §10.5).

```
  bind(b, W, O) = (W₁, O₁)
  W₁ ∣ γ ⊢ V ⊑ M′ : A ⊑_W₁^O₁ B′
  b = X:α or X:α⇔β,  α fresh
  A not a variable
  X ∈ A
  ──────────────────────────────── (Λ⊑, D31)
  W ∣ γ ⊢ ΛX.V ⊑ M′ : ∀X.A ⊑_W^O B′
```

The binder `b` is `X:α` (fresh or join) or `X:α⇔β` (claim-rep), and
`bind` is the partial function

```
  bind(X:α,   W, [])   = (W ⊕ (X:α ∥ ·), [])          fresh
  bind(X:α,   W, Y·O)  = (W[X:α ↦ Y], O)              join
  bind(X:α⇔β, W, [])   = (W ⊕ (X:α⇔β ∥ ·), [])        claim-rep, D29
```

undefined otherwise (a claim with openings, or a skip slot first).
Side conditions: for the join, `Y` is right-only and bound to `β:=★`
(well-formedness of the index); for claim-rep, `β:=★` in `Δ′`, no right
type variable bound to `β` is in scope, and no left partner of `β`
bound to a type variable is in scope.  (Agda: `Bind`, with cases
`b-fresh`, `b-join`, `b-rep`.)

`bind` has no case for a skip slot: a skip is used up only by a gen
layer of `cast⊑` (`opens`, §10.2), or filled by a later `⊑⟪⟫`
(§10.5).

(How the rule for a left ∀-value against a right `Inst` boundary
evolved, and claim-rep on H1 with its ladder: §C6.3, D29.)

### 10.4 Instantiation

**Instantiation** (GTSFImp `•⊑•²`, `•⊑²`).  The compiled form of
`M [A]` is a `ν`, so the two type applications become:

```
  W ∣ γ ⊢ L ⊑ L′ : ∀X.C ⊑ ∀X.C′    A ⊑_W A′    c : C ⇒ B    c′ : C′ ⇒ B′
  ─────────────────────────────────────────────────────────────── (ν⊑ν)
  W ∣ γ ⊢ ν X:=A.(L X)⟨c⟩ ⊑ ν X:=A′.(L′ X)⟨c′⟩ : B ⊑ B′

  W ∣ γ ⊢ L ⊑ M′ : ∀X.C ⊑ B′    A ⊑_W ★    c : C ⇒ B
  ──────────────────────────────────────────────── (ν⊑)
  W ∣ γ ⊢ ν X:=A.(L X)⟨c⟩ ⊑ M′ : B ⊑ B′
```

There is no `⊑ν`.  The only right-only `ν` is the one that `Inst`
creates, and the right side reduces it by `TyBeta` at once.  So a
catch-up lemma can take `Inst` and `TyBeta` together, and the
relation never has to hold in between.

### 10.5 Boundaries

**Boundaries** (new; these replace GTSFImp's eight `reveal`/`conceal`
rules).  A boundary's interior is term-closed, so the premise has
`γ = []`.  The conversions are typed on their own sides, and, like the
coercions, they are not compared with each other:

```
  W[δ ∥ δ′] ∣ [] ⊢ M ⊑ M′ : Aᵢ ⊑ A′ᵢ    c : Aᵢ ⇒ A    c′ : A′ᵢ ⇒ A′
  ───────────────────────────────────────────────────────────── (⟪⟫⊑⟪⟫)
  W ∣ γ ⊢ [δ] M ⟨c⟩ ⊑ [δ′] M′ ⟨c′⟩ : A ⊑ A′

  W[δ ∥ ·].π := π ∣ [] ⊢ M ⊑ M′ : Aᵢ ⊑ A′    c : Aᵢ ⇒ A
  π = [] or (M simple and c has a ∀ per type variable of π)
  every −X^α in δ: no partner of α in ϱ is in κ          (R1, D28)
  ───────────────────────────────────────────── (⟪⟫⊑, D27, D28)
  W.π := π ∣ γ ⊢ [δ] M ⟨c⟩ ⊑ M′ : A ⊑ A′
```

```
  W[· ∥ δ′].π := π′ ++ new ∣ [] ⊢ M ⊑ M′ : A ⊑ A′ᵢ
  c′ : A′ᵢ ⇒ A′
  π′ = π seen inside δ′    new introduced by δ′
  new = [] or M a value
  ───────────────────────────────────────────── (⊑⟪⟫, D27)
  W.π := π ∣ γ ⊢ M ⊑ [δ′] M′ ⟨c′⟩ : A ⊑ A′
```

🆕 **D31** replaces the three boundary rules by the three below.
Each may add a set `K` of right rep. vars to `κ` for its interior,
limited to rep. vars of type variables this boundary JOINS, and
PAYS: its interior index holds at `Wᵢ`, without `K`, so the joined
type variables are read there at `X⊑X`.  `⊑⟪⟫` is the only rule that
creates slots, and the permission of a new opening is chosen there.
`⟪⟫⊑`'s R1 becomes R1′.  Every boundary rule also takes `Wᵢ +κ K`
well formed.  (why: §C9.2)

`joined(δ ∥ δ′)` (Agda `JoinRep`, `jr-join`): the right rep. vars `β`
such that, in `Wᵢ = W[δ ∥ δ′]`, a right type variable bound to `β` is
joined to a left type variable, and one of the two is introduced by
this boundary (a matched fresh pair, or a rejoin through `ϱ`).

```
  Wᵢ = W[δ ∥ δ′]
  K ⊆ joined(δ ∥ δ′)
  Aᵢ ⊑_Wᵢ A′ᵢ                            (the join pays)
  Wᵢ +κ K ∣ [] ⊢ M ⊑ M′ : Aᵢ ⊑ A′ᵢ
  c : Aᵢ ⇒ A
  c′ : A′ᵢ ⇒ A′
  Wᶜ ⊢ c ⊑ c′
  ──────────────────────────────────────── (⟪⟫⊑⟪⟫, D31)
  W ∣ γ ⊢ [δ] M ⟨c⟩ ⊑ [δ′] M′ ⟨c′⟩ : A ⊑ A′

  Wᵢ = W[δ ∥ ·]
  K ⊆ joined(δ ∥ ·)
  Aᵢ ⊑_Wᵢ^O A′                           (the join pays)
  Wᵢ +κ K ∣ [] ⊢ M ⊑ M′ : Aᵢ ⊑^O A′
  c : Aᵢ ⇒ A
  O = [] or (M simple and c has a ∀ per slot of O)
  every −X^α in δ is unbind-OK for A in W     (R1′)
  ──────────────────────────────────────── (⟪⟫⊑, D31)
  W ∣ γ ⊢ [δ] M ⟨c⟩ ⊑ M′ : A ⊑_W^O A′

  Wᵢ = W[· ∥ δ′]
  O seen inside δ′ is O′
  N new slots for δ′ and M
  N = [] or M a value
  Fill O′ N Oᵢ
  Oᵢ well formed at Wᵢ
  K ⊆ joined(· ∥ δ′) ∪ newreps(N)
  A ⊑_Wᵢ^Oᵢ A′ᵢ                          (the join pays)
  Wᵢ +κ K ∣ [] ⊢ M ⊑ M′ : A ⊑^Oᵢ A′ᵢ
  c′ : A′ᵢ ⇒ A′
  ──────────────────────────────────────── (⊑⟪⟫, D31)
  W ∣ γ ⊢ M ⊑ [δ′] M′ ⟨c′⟩ : A ⊑_W^O A′
```

The side relations of `⟪⟫⊑` and `⊑⟪⟫` under D31:

- **R1′** (Agda `UnbindOK′`).  `−X^α` is unbind-OK for `A` in `W` iff
  `X ∉ A` (`ok-hidden`) or no partner of `α` in `ϱ` is in `W`'s `κ`
  (`ok-unbind′`, R1).  So only a left unbind whose type variable
  occurs in the boundary's EXTERIOR type needs an unpermitted partner.
- **The `O` seen inside `δ′`** (Agda `CarriedS`).  An opening `Y`
  continues as its interior type variable (`δ′` must not unbind it); a
  skip continues as a skip.
- **New slots** (Agda `NewSlot`).  Each slot of `N` is an opening of a
  type variable `δ′` introduces (`Y` fresh in `δ′`), or a skip, and a
  skip only when `M` is a gen-cast value (`GenCastValue`).
  `newreps(N)` is the set of rep. vars `β` with `Y:=β`, `Y` an opening
  of `N` (`jr-open`).
- **`Fill`** (Agda `Fill`, `PushD`).  The carried slots keep their
  order; a new opening may fill a carried skip (left to right); the
  remaining new slots go last:

  ```
    ─────────────── (f-end)
    Fill [] N N

    Fill O N Oᵢ
    ───────────────────────── (f-keep)
    Fill (s·O) N (s·Oᵢ)

    Fill O N Oᵢ
    ───────────────────────── (f-fill)
    Fill (_·O) (Y·N) (Y·Oᵢ)
  ```

- **Well-formed slots** (Agda `SlotOK`, `SlotNe`): §9.

`Wᶜ ⊢ c ⊑ c′` is D17/D18's (§10.6) and reads the EXTERIOR `κ`, so R2
is unchanged.

In `⟪⟫⊑` and `⊑⟪⟫`, the term without the boundary is in the premise
at `γ = []`, so it must be term-closed as well.  That holds at run
time, because every boundary of a run is a closed subterm.

(What `⊑⟪⟫`'s push, pass and carry do: §C6.4; R1 and counterexample
C5: §C6.5; the ladders of K's final pair and of P4's block B3: §C6.6,
§C6.7.)

### 10.6 Conversion imprecision

**Conversion imprecision** (D17, D18; `ConversionImprecision.agda`).
`ν⊑ν` and `⟪⟫⊑⟪⟫` also require `Wᶜ ⊢ c ⊑ c′`, where `Wᶜ` is the world
over the two conversion contexts.  For `ν⊑ν`, it adds both
allocations and pairs the two `ν`s' rep. vars in `ϱˡ`.  For a
boundary pair, it is the conversion-context analogue of `W[δ ∥ δ′]`.
The one-sided boundary rules have no conversion premise.  The clauses
follow the conversion grammar (§2): middles `g`, tails `t` and
conversions `c`.  One rule per block; every premise is on its own
line.  "Shared" means `X` and `X′` are embedded as the same center type
variable.

**Middles** `Wᶜ ⊢ g ⊑ g′`:

```
  A ⊑ A′
  ──────────────── (id⊑id)
  id(A) ⊑ id(A′)

  c ⊑ c′
  d ⊑ d′
  ──────────────── (→⊑→)
  c → d ⊑ c′ → d′

  Wᶜ ⊕ (X:α ∥ X′:α′) ⊢ c ⊑ c′
  α, α′ fresh
  ─────────────────────────── (∀⊑∀)
  ∀X.c ⊑ ∀X′.c′

  Wᶜ ⊕ (X:α ∥ ·) ⊢ c ⊑ g′
  α fresh
  ─────────────────────────── (∀⊑)
  ∀X.c ⊑ g′
```

**Tails** `Wᶜ ⊢ t ⊑ t′`:

```
  g ⊑ g′
  ──────────────── (mid⊑mid)
  g ⊑ g′  (as tails)

  X, X′ shared
  ──────────────── (seal⊑seal)
  −X ⊑ −X′

  t ⊑ t′
  X, X′ shared
  ──────────────── (;seal⊑;seal)
  t ; −X ⊑ t′ ; −X′

  μ(X) = X⊑★
  U(X)
  ──────────────── (seal⊑id★)
  −X ⊑ id(★)

  t ⊑ t′
  μ(X) = X⊑★
  U(X)
  ──────────────── (;seal⊑)
  t ; −X ⊑ t′
```

**Conversions** `Wᶜ ⊢ c ⊑ c′`:

```
  t ⊑ t′
  ──────────────── (tail⊑tail)
  t ⊑ t′  (as conversions)

  X, X′ shared
  ──────────────── (unseal⊑unseal)
  +X ⊑ +X′

  X, X′ shared
  c ⊑ c′
  ──────────────── (unseal;⊑unseal;)
  +X ; c ⊑ +X′ ; c′

  μ(X) = X⊑★
  U(X)
  ──────────────── (unseal⊑id★)
  +X ⊑ id(★)

  μ(X) = X⊑★
  U(X)
  c ⊑ c′
  ──────────────── (unseal;⊑)
  +X ; c ⊑ c′
```

where

```
  U(X)  =  no partner in ϱ of X's rep. var
           is in κ                        (R2, D28)
```

(Agda: `conv-id⊑id`, `conv-↦⊑↦`, `conv-∀⊑∀`, `conv-∀⊑`;
`conv-mid⊑mid`, `conv-seal⊑seal`, `conv-⨾seal⊑⨾seal`, `conv-seal⊑id★`,
`conv-⨾seal⊑`; `conv-tail⊑tail`, `conv-unseal⊑unseal`,
`conv-unseal⨾⊑unseal⨾`, `conv-unseal⊑id★`, `conv-unseal⨾⊑`.)

(Why the `★` clauses, R2 and the chain forms: §C6.8, D17, D18.)

### 10.7 Rule count and side relations

**Count.**  In Agda, 15 rules: four congruence rules (`x⊑x`, `κ⊑κ`,
`ƛ⊑ƛ`, `·⊑·`; GTNF has no binary operators, so no `⊕⊑⊕`), `blame⊑`,
three cast rules, `Λ⊑Λ` and `Λ⊑` (one rule whose `Claim` is fresh, pop
or claim-rep, displayed above as three), two `ν` rules and three
boundary rules.  The side relations are `Claim` (3 cases), `CastClaim`
(3), `BdyClaim` (2), `Push` with `Carried` (D27), and `CastGrant`
(D28; 🆕 **D31**: removed).
GTSFImp's `_∣_⊢²_⊑_∶_` has 22.

🆕 **D31**: still 15 rules, one per rule above (`_∣_⊢_⊑ᴰ_∶[_]_` in
`proof/DGG/notes/D28pD30.agda`); `Imprecision.agda` (`_⊢_⊑_`) is
unchanged.  Its side relations, against today's:

| D31 | what it does | replaces |
|---|---|---|
| `Slot`, `OpenO` | the index with slots (opening `opn`, skip `skp`), §9 | `πʷ`, `OpenImp` |
| `CastOpen` (3) | `cast⊑`'s slots along the coercion's layers | `CastClaim` (3) |
| `Bind` (3), `Join1` | `Λ⊑`'s binder: fresh, join, claim-rep | `Claim` (3), `Open1` |
| `BdyOpen` (2), `ForallConvS` | `⟪⟫⊑` passes slots into a `∀` boundary | `BdyClaim` (2), `ForallConv` |
| `PushD`: `CarriedS`, `NewSlot`, `Fill` | `⊑⟪⟫` carries, creates and fills slots | `Push`, `Carried` |
| `SlotOK`, `SlotNe` | well-formed slots, at `⊑⟪⟫` | `PendingOK`, `wf-pending`, `wf-distinct` |
| `JoinRep` | the `K` a boundary may add to `κ` | `CastGrant`, `Grants` |
| `UnbindOK′` (R1′) | `⟪⟫⊑`'s unbind condition | `UnbindOK` (R1) |
| `WfWorldᴰ` | `WfWorld` without its pending parts | `WfWorld` |

------------------------------------------------------------------------

## 11. Metatheory statements

GTNF should satisfy the same metatheory as GTSFImp.  Each goal below
names the GTSFImp statement it mirrors.  The νF-specific invariants
(`det`, tightness, `ScopeMapPreservation`/`ColorPreservation`) carry over
from `strong-rep-nu` as well.  Status: only the type imprecision of §11.4 is in Agda.

### 11.1 Type safety of the cast calculus

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

### 11.2 Compilation

GTSFImp: `Compile.agda` (`compile`, `compile-value`).
νF: `strong-rep-nu.CompileTyping` (`compile-⊢`).

```
compile-⊢ :     if  Δ ∣ Γ ⊢ M : A  (source),  then  Δ ∣ Γ ⊢ ⟦M⟧ : A
compile-value : if  M is a source value,  then  ⟦M⟧ is a value
```

The coercion lemma behind `compile-⊢` is mode for mode:
if `μ ⊢ c : A ∼ B`, then `Δ ; μ ⊢ ⟦c⟧ℓ : A ⇒ B` (§7; §C4).

### 11.3 The source type system

GTSFImp: `GradualTypeCheck.agda`, `Consistency2.agda`.

- **A type checker.**  A synthesis function for source terms returns a
  type together with a typing derivation.  It is sound by construction,
  as in GTSFImp, where it is positive-only.
- **Decidable consistency.**  This is GTSFImp's `Consistency2.lower?`.

### 11.4 Type imprecision

GTSFImp: `Imprecision.agda` (`ImpEnv`, modes `X⊑X`/`X⊑★`),
`proof/Imprecision.agda` (`⊑-unique`), `proof/ImprecisionComposition.agda`
(`⊑-trans`), `proof/ImprecisionConsistency.agda` (`refl⊑`, and the
bridges between imprecision and consistency).

```
refl⊑ :     A ⊑ A
⊑-trans :   if  A ⊑ B  and  B ⊑ C,  then  A ⊑ C
⊑-unique :  any two derivations of  A ⊑ B  are equal
```

(Type imprecision is §8; it must not be conflated with the consistency
modes of §3: §C10.1.)

### 11.5 Static gradual guarantee

```
sgg :  if  Δ ∣ Γ ⊢ M : A  and  M ⊑ M′  (with  Γ ⊑ Γ′),
       then  Δ ∣ Γ′ ⊢ M′ : A′  for some  A′  with  A ⊑ A′
```

(GTSFImp's typed term imprecision, and the plan for `sgg`: §C10.2.)

### 11.6 Compilation preserves imprecision

GTSFImp: `proof/DGG/CompilePreservesImprecision2.agda`
(`compile-preserves-imprecision²`).

```
compile-⊑ :  if  μ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p,
             then  W₀ ∣ γ₀ ⊢ ⟦M⟧ ⊑ ⟦M′⟧ ∶ p₀
```

Here `⊑` is a *cast-term* imprecision for GTNF that still has to be
designed, and `W₀`, `γ₀`, `p₀` are the initial world, context and type
imprecision (§9, §10).  Discussion, and why GTNF is shaped for this
relation: §C10.3.

### 11.7 Dynamic gradual guarantee

GTSFImp: `proof/DGG/DynamicGradualGuaranteeDef.agda` (`GradualDGG`), with
the proof under way in `proof/DGG/`.  For closed source terms with
`[] ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p`, the four parts are:

```
1.  if  ⟦M⟧ ⟶* V  (a value),
    then  ⟦M′⟧ ⟶* V′  (a value)  with  W ∣ [] ⊢ V ⊑ V′ ∶ q  for some world W

2.  if  ⟦M⟧ diverges,  then  ⟦M′⟧ diverges

3.  if  ⟦M′⟧ ⟶* V′  (a value),
    then  ⟦M⟧ ⟶* V  (a value)  with  W ∣ [] ⊢ V ⊑ V′ ∶ q,   or  ⟦M⟧ ⟶* blame ℓ

4.  if  ⟦M′⟧ diverges,  then  ⟦M⟧ diverges or reaches  blame ℓ
```

The runs are νF runs, so each `⟶*` carries the allocations it made
(`runCtx`), and `q` relates the result types at the two final contexts.

(Proof strategy, forward and backward simulation: §C10.4.)

------------------------------------------------------------------------

# Part II — Commentary

Explanations and rationale, worked examples and ladders,
counterexamples and open defects, proposals, metatheory discussion,
the Agda plan, and the history of decisions.  C1–C4 comment on §3,
§5, §6 and §7; C6 comments on §9 and §10.

------------------------------------------------------------------------

## C1. Coercions: provenance and modes

### C1.1 Names and provenance

The constructor names follow GTSF's `Coercions.agda` (`id`, `_!`, `_？`,
`_↦_`, `` `∀ ``, `inst`, `gen`, `_︔_`) and GTSFImp's consistency
constructors (`id`, `_!`, `？_`, `_↦_`, `∀ᶜ_`, `inst_`, `gen_`,
`bot-elim`, `bot-intro`).  The modes are GTSFImp's `Var∼`, and a mode
environment is its `Env∼`.
`GenSafe` is GTSFImp's `CastTerms.GenSafe`: the coercion suspended under
a `gen` must not hide a check that ought to run before the polymorphic
value exists.  Compilation always produces gen-safe coercions under
`gen`, by GTSFImp's `gen-safe` lemma (`proof/Consistency.agda`).

### C1.2 Why modes are in the cast calculus

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

### C1.3 Modes at a cast

**Modes at a cast.**  A cast carries its mode environment as part of the
term, written `M ⟨p⟩^μ` when the environment matters and `M ⟨p⟩`
otherwise.  This follows GTSFImp's `CastTerms`, whose cast constructor
is `_⟨_⟩ : Term Δ → {μ : Env∼ Δ} … (c : μ ⊢ A ∼ B) → Term Δ`: the `μ` is
part of the cast's evidence, so a term determines it.  Compilation
creates every cast at the environment that gives each type variable in
scope `★∼X∼★`, matching the source's `A ∼ B = idᶜ ⊢ A ∼ B`.  Reduction
then **keeps and extends** each cast's environment, and it never
replaces it by the cross environment:

- When an instantiation rule moves a coercion out from under its binder,
  the freed type variable keeps the binder's mode.  `TyBeta`'s
  `inst_X(W ⟨gen X.p⟩^μ) = ([−X^α] W ⟨Id(A)⟩) ⟨p⟩^(μ, X:★∼X)` and
  `inst_X(W ⟨∀X.p⟩^μ) = inst_X(W) ⟨p⟩^(μ, X:X∼X)`.  The modes are those
  of GTSFImp's `β-gen`, whose contractum is `⇑ᵗᵐ V ⟨ c ⟩` with `c` under
  `genᵐ μ`, and of the analogous `β-∀`.  GTNF differs from GTSFImp in
  not shifting `V` (§C3.1).
- `CastFun` casts the argument at `flip(μ)`, because the domain
  coercion was typed there.  This is GTSFImp's `β-⇒`, whose argument
  cast `c` has type `flipᵐ μ ⊢ A′ ∼ A`.
- `CastSeq` keeps `μ` for both halves, and `Inst` closes `X` at `★`, so
  its result cast is at `μ`.
- `IdDyn` moves a tag cast from a boundary's interior to its exterior.
  The moved cast keeps the interior mode of every exterior type
  variable the interior can see.  It gives `X∼X` to every exterior type
  variable that the interior cannot see, because the cast has never
  seen that type variable (`exit_δ(μ)`, §6.3; Example 7).  This is
  what GTSFImp does when a cast first meets a variable: at an
  allocation, `ξ-⟨⟩` re-indexes the cast's environment by
  `applyEnv (bind A) μ = extᵐ μ`, which gives the new variable `X∼X`.
  The filled-in mode never belongs to a type variable that the
  coercion mentions.  If the tag were that type variable, then it
  would be visible in the interior and its mode would be copied.  So
  the choice does not affect typing or reduction; it is bookkeeping for
  the cast-term imprecision (§11.6).

The modes of free type variables are therefore data that the dynamic
semantics carries along.  The cast-term imprecision relates casts with
possibly different environments on its two sides, as GTSFImp's
`cast⊑cast²` does (`ν ⊢ C ∼ A`, `ν′ ⊢ C′ ∼ A′`).

### C1.4 Closing at ★ needs evidence-shaped sequences

The closing lemma of §3 needs the
evidence-shaped sequences of D20: with a general `p ; q`, a nested
`inst Y. q` could reach the target `X` by a detour through `★`, such as
`… ; (★→★)! ; X?ℓ`, and closing would give it the target `★`, which
`inst` forbids (M1's counterexample,
`proof/TypeSafety/notes/InstCloseCounterexample.agda`).  `Inst` uses the lemma at
`m = X∼★`.  The lemma is stated for every `m` because a function
coercion's domain flips `X∼★` to `★∼X`.

------------------------------------------------------------------------

## C2. Values: rationale and proof sketches

### C2.1 The new value form

**The new value form** is a `★`-value under a boundary whose tag is a
type variable introduced by the boundary itself.  `IdDyn` (§6.3) moves
the tag out of every other boundary around a tagged value, so this is
the only boundary that can remain around a `★`-value.

### C2.2 `fresh(δ)`

On the lemma of §5: `Δ ⊢ X` if and only if `X ∉ fresh(δ)`.

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
allocation and under weakening by fresh type variables.

### C2.3 Cast values are simples

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

### C2.4 Proof sketch of `no-bot-value`

The proof goes by cases on `V`.  A `Λ` would need a body value of type
`X` under an abstract `α`, and there is none.  For `W ⟨∀X. p⟩`, `p` is
strict in `X`, so `p : A ⇒ X` forces `A = X`, and `W` has type `∀X. X`.
`W ⟨gen X. p⟩` has the target type `∀X. B` with `B` not a variable.  For the
boundary `[δ] U ⟨∀X. c⟩`, the conversion `c : A′ ⇒ X` is typed with
`X:=α` for an abstract `α`.  Sealing needs a representation, so `c` can
only be `id(X)`, and then `U` has type `∀X. X`.  These cases need
checking when the Agda exists.

------------------------------------------------------------------------

## C3. Reduction: rationale

### C3.1 No term moves under a new type variable

**No term moves under a new type variable.**  In the `gen` case of
`inst_X`, `W` was typed outside `X`'s scope, and only `p` mentions `X`.
Placing `W` directly in the interior `Δ, X:=α` would need a weakening,
so `W` is put under the binder's dual `[−X^α]` instead.  Its interior is
`−X(Δ, X:=α) = Δ`, which is exactly where `W` was typed, and its
conversion `Id(A)` is typed in `(−X^α)⁺(Δ, X:=α) = Δ, X:=α`.  So `W`
keeps its scope ("colour") and needs no weakening, either in the Agda
(no de Bruijn shift) or in a preservation proof with named variables
(Jeremy, 2026-10-01).  This is νF's `crossΛᴹ`, the wrapper Beta puts on
a value that crosses a `Λ`.  It costs extra steps: Example 2 takes 12
steps rather than 8, because the wrapper is crossed by `Wrap` and later
fused by `Merge`.  In the `Λ` and `∀X.p` cases nothing moves under the
new type variable: the `Λ` body and `p` were already typed under a
binder for `X`.

### C3.2 How `inst_X` works

The four `inst_X` clauses of §6.2 cover every canonical ∀-value (§5).  The recursion
is on the structure of the value, and each layer of the value becomes
one layer of the result: a cast stays a cast, and a boundary stays a
boundary.  So `inst_X` stacks boundaries, as νF's `TyWrap` does, and
`Merge` fuses them afterwards.  `inst_X` allocates nothing; the one
allocation `α:=Δ(A)` is made by `TyBeta` itself, however many layers
the value has.  (Under the name `inst_X`, the meta-operation is not to
be confused with the coercion `inst X. p` and its rule `Inst`.)

### C3.3 `TyBeta` covers νF's rules and GTSFImp's

νF's two rules are instances of §6.2's `TyBeta`.  If `V = ΛX.N`, then it
is νF's `TyBeta`.  If `V = [δ] (ΛX.N) ⟨∀X.c⟩`, then it is νF's
`TyWrap`.  The `gen` case is GTSFImp's `β-gen` with a boundary in place
of `↑ 〖 0 , ⇑ᵗ C ↑ B 〗`.  The `∀X.p` case is GTSFImp's `β-∀`: the
value under the cast is instantiated, with no further allocation, and
then cast.  When the Agda is written, `inst_X` may be a function on
value derivations, or `TyBeta` may be split into one constructor per
outermost layer; this draft states it once.

### C3.4 Preservation of `TyBeta`

Proof sketch for the lemma of §6.2.
The `Λ` case re-reads the body, typed under an abstract `α`, at the
allocated `α:=R`, as νF's `TyBeta` does.  The `gen X.p` and `∀X.p`
cases use the fact that coercion typing does not depend on whether `α`
is abstract or bound (§3).  The `gen` case types `[−X^α] W ⟨Id(A)⟩`
with the boundary rule, and `W` is used at exactly its own typing
`Δ ∣ [] ⊢ W : A`, so no weakening lemma is needed.  In the boundary case, `δ` stays coherent at
`Δ, X:=α`, because `X` and `α` are fresh.  Its interior is then
`δ(Δ), X:=α`, and `c` is typed in `δ⁺(Δ), X:=α`.

### C3.5 The cast rules and GTSFImp's

The rules of §6.3 correspond to GTSFImp's `β-id`, `β-⇒`, `β-inst`,
`tag-untag`, `tag-untag-bad` and `blame-bot-intro`.  No rule applies
`bot-elim` to a value, because no value has type `∀X. X` (§5); progress
dismisses that case, as GTSFImp's `cast-value-progress` does.  GTSFImp's `ground` and `expand` are
not needed, because a tag through a non-ground type is the sequence
`p ; G!` and `CastSeq` splits it.  GTSFImp's `β-∀` is the
`∀X.p` case of `inst_X` (§6.2), because GTNF instantiates by `ν` and not
by a `⦂∀ B [ C ]` type application.

### C3.6 `Inst` allocates through `ν`

`Inst` does not allocate by itself.  The `ν X:=★` it creates allocates
`α:=★` on the next step, by `TyBeta`.  Inside the resulting
boundary, `X:=★` holds, so `reveal_X(src(p))` seals and unseals `X`
against `★`.  The coercion has already been closed at `★`: each `X!`
and `X?ℓ` in `p` has become `id(★)`.  As in GTSFImp, the `inst`-bound
variable is therefore implemented entirely by conversions, and no tag
mentions it.

### C3.7 Why a tag by type variable keeps its meaning across a boundary

`IdDyn` moves a tag `G` from the interior `δ(Δ)` to the exterior `Δ`
without changing it.  If `G` is a type variable `X`, then this is sound
because of coherence: `X:=α ∈ δ(Δ) ⊆ δ⁺(Δ)` and `X:=β ∈ Δ ⊆ δ⁺(Δ)`, and
coherence (`X = Y ⇔ α = β` on `δ⁺(Δ)`) forces `α = β`.  So the two
occurrences of `X` denote the same representation variable, even if `δ`
removed `X` (`−X^α`) and later rebound it (`+X^α`).  After the tag is
outside, the ordinary `TagUntag`/`TagUntagBad` compare it with a check
`H` by **syntactic equality**.

If the tag is a type variable in `fresh(δ)`, then the tag cannot move
out, and no check `H` that is well formed in `Δ` can be equal to it.  So
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

## C4. Compilation: the typing theorem

The intended theorem is the analogue of νF's `compile-⊢`: if
`Δ ∣ Γ ⊢ M : A` in the source, then `Δ ∣ Γ ⊢ ⟦M⟧ : A`.  Its proof needs
the fact that `⟦c⟧ℓ` is typed at the endpoints and modes of `c`
(if `μ ⊢ c : A ∼ B`, then `Δ ; μ ⊢ ⟦c⟧ℓ : A ⇒ B`, by induction on `c`,
since each coercion rule mirrors a consistency rule).  It also needs
the fact that `⟦·⟧` maps source values
to values, which needs `⟦gen c⟧ℓ` to be gen-safe and so uses GTSFImp's
`gen-safe`.

------------------------------------------------------------------------

## C5. Examples of reduction

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
visible.  There it is the fresh-tag value `[+X^α] (… ⟨X!⟩) ⟨id(★)⟩`, and
the body `λx:★. x` sees only a `★` whose tag it cannot refer to.  When
the value comes back out, `Merge` and `IdDyn` restore the tag `X`.  The
Agda run (`ex2-run`) fires exactly these 12 rules.

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

### Example 4 — a tag whose type variable has escaped

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
machine-checked run (`GTNF/agda/examples/Examples.agda`, `ex5-run`, 21 steps)
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
type variables, so its mode environment is empty.  The run (`ex7-run`, 9
steps) is:

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

## C6. Cast-term imprecision: explanations and ladders

### C6.1 Worlds: an example, and why nothing is rebased

Example: in P3's block after the left's `Beta`, `⊑⟪⟫` pushes the
right `Inst` boundary's type variable and the left `Λ⊑` pops it, so the
premise relates `λx:X.x` (typed under the left `Λ`'s abstract `α₀`) to
`λx:X.x` (inside the right's `[+X^αᴿ]`, `αᴿ:=★`).  The shared type
variable `X` needs `(α₀, αᴿ) ∈ ϱˡ`.  After the left's `TyBeta`, the
pair is `(αᴸ, αᴿ) ∈ ϱᵍ`, with `αᴸ:=ℕ`.

The point of the design (§11.6, §C10.3) is that **no part of a world is
ever rebased.**  `Ω`, `η`, `η′` and `κ` change only lexically: they are
extended by a binder (`Λ`, a coercion binder, a boundary entry `+X^α`)
and shrunk by an unbind (`−X^α`), for the subterm under it, exactly as
the type context is; ~~`κ` grows at a right check (`⊑cast`) for the
subterm under it~~ 🆕 **D31**: `κ` grows only at a boundary rule that
joins a type variable, for the boundary's interior.  So is `ϱˡ`.  The
one non-lexical part is `ϱᵍ`, and it only grows: a `TyBeta` that the
other side matches adds one pair.  An unmatched allocation only
renumbers the allocating side's rep. vars (de Bruijn).

### C6.2 Grants (D28)

Under the adopted D28, `⊑cast` (§10.2) may grant.  The explanation is
struck through because 🆕 **D31** would remove grants.

~~A right check GRANTS (D28): every value that leaves the right's cast
value through `p′` is checked against the right type variable bound to
`β`, so in the premise an X-tagged right value may face an untagged left
value of that type variable, i.e. the type variable bound to `β` is
`X⊑★`.  P4's gen wrapper `X! → X?` and its later check `X?` grant `αᴿ`;
C2's `X! → id(★)` grants nothing.  Left casts, `cast⊑cast`, right hides
and boundaries grant nothing.  A grant covers the whole premise; `γ⁺`
has the same types at the raised marks (`RaiseCtx`).~~

### C6.3 Claim-rep (D29) and H1

The rule that relates a left ∀-value to a right `Inst` boundary, first
`∀⊑⟪+⟫` (D14, D22), then an opening of `⊑⟪⟫` (D26), is now a push of
`⊑⟪⟫` followed by a pop (D27), or, for a `Λ`, a claim above the
boundary followed by its rejoin (D29).

In the claim-rep case (D29), the binder `X` claims the right rep. var
`β`, to which no type variable is bound yet.  `X` is left-only (`X⊑★`)
until a right boundary `+Y^β` binds the type variable `Y` to `β`.  There
`Interior.join-fresh` joins `Y` to `X`, because their rep. vars are
paired (D25).  From then on the shared type variable's mark is `β`'s
permission: `X⊑X` unless a right check of `Y` above grants `β`.  So C4's
`x ⊑ x⟨X!⟩` still needs a grant.  The claim is what H1 needs.  There the
right's boundaries bind type variables for the instantiations in the
opposite order to the left's binders, and the left's first binder must
be matched before the right binds a type variable to its rep. var.  H1's
final pair, generated by
`scripts/render_gtnf.sh 'impLadder final' 'open import examples.TermImprecisionH1Examples' 'open import examples.ImpLadder'`
(pinned in `examples/ImpLadder.agda`):

```
W0 = the conclusion's world
  ⟨⟩
  ϱᵍ = {}  ϱˡ = {}  Ξᴸ = []  Ξᴿ = [α:=★, β:=★]
W1 = W0 ⊕ᴸ⇔ α
  ⟨X: X^α ⊑[X⊑★] ─⟩
  ϱᵍ = {}  ϱˡ = {α⇔α}  Ξᴸ = [α abst]  Ξᴿ = [α:=★, β:=★]
W2 = Interior W1
  ⟨Y: ─ ⊑[X⊑X] Y^β │ X: X^α ⊑[X⊑★] ─⟩
  ϱᵍ = {}  ϱˡ = {α⇔α}  Ξᴸ = [α abst]  Ξᴿ = [α:=★, β:=★]  πʷ = [Y^β]
W3 = Interior W2
  ⟨Y: ─ ⊑[X⊑X] Y^β │ X: X^α ⊑[X⊑X] X^α⟩
  ϱᵍ = {}  ϱˡ = {α⇔α}  Ξᴸ = [α abst]  Ξᴿ = [α:=★, β:=★]  πʷ = [Y^β]
W4 = Open1 W3: pop Y^β
  ⟨Y: Y^β ⊑[X⊑X] Y^β │ X: X^α ⊑[X⊑X] X^α⟩
  ϱᵍ = {}  ϱˡ = {β⇔β, α⇔α}  Ξᴸ = [α abst, β abst]  Ξᴿ = [α:=★, β:=★]
W   left term      A              ηᴸA            ⊑                            ηᴿA′   A′     right term
──  ─────────────  ─────────────  ─────────────  ───────────────────────────  ─────  ─────  ──────────────────────────────────
W0  ΛX. □          ∀X. ∀Y. X→Y→X  ∀X. ∀Y. X→Y→X  ∀X⊑★. ∀Y⊑★. X⊑★ → Y⊑★ → X⊑★  ★→★→★  ★→★→★  ─ (claim α)
W1  ─              ∀Y. X→Y→X      ∀Y. X→Y→X      ∀Y⊑★. X⊑★ → Y⊑★ → X⊑★        ★→★→★  ★→★→★  □⟨id(★) → (id(★) → id(★))⟩^[]
W1  ─ (push Y^β)   ∀Y. X→Y→X      ∀Y. X→Y→X      ∀Y⊑★. X⊑★ → Y⊑★ → X⊑★        ★→★→★  ★→★→★  [+Y^β] □ ⟨id(★) → (−Y → id(★))⟩
W2  ─              ∀Y. X→Y→X      X→Y→X          X⊑★ → Y⊑Y → X⊑★              ★→Y→★  ★→Y→★  □⟨id(★) → (id(Y) → id(★))⟩^[Y:X∼X]
W2  ─ (carry Y^β)  ∀Y. X→Y→X      X→Y→X          X⊑★ → Y⊑Y → X⊑★              ★→Y→★  ★→Y→★  [+X^α] □ ⟨−X → (id(Y) → +X)⟩
W3  ΛY. □          ∀Y. X→Y→X      X→Y→X          X⊑X → Y⊑Y → X⊑X              X→Y→X  X→Y→X  ─ (pop Y^β)
W4  λx:X. □        X→Y→X          X→Y→X          X⊑X → Y⊑Y → X⊑X              X→Y→X  X→Y→X  λx:X. □
W4  λy:Y. □        Y→X            Y→X            Y⊑Y → X⊑X                    Y→X    Y→X    λy:Y. □
W4  x              X              X              X⊑X                          X      X      x
```

`final-no-push` relates the same pair with two claims, `α` for `ΛX`
and `β` for `ΛY`, and no push at all.

### C6.4 Push, pass and carry (D27)

`⊑⟪⟫` PUSHES type variables that `δ′` introduces.  Each is right-only
and bound to a rep. var `:=★`: the interior world's well-formedness
says so; its mark is derived (D28).  A pending type variable is a right
type variable position, so `⟪⟫⊑` passes it into the left boundary
unchanged; `⊑⟪⟫` carries it through `δ′` to its interior position.  A
type variable that `δ′` unbinds has no interior position, so it must
be popped first.  With no pending type variable these are the plain
one-sided boundary rules.  For the right's `Inst` boundary against a
left ∀-value (Example P3), `⊑⟪⟫` pushes the boundary's type variable
and `Λ⊑` pops it.  The left stays the ∀-value: no `inst_X` appears in
the relation, and under a pending type variable the left term is a
value.

🆕 **D31**: the push creates an opening in the index (`PushD`), the
carry is `CarriedS`, the pass is `BdyOpen` (and `co-∀` at a left
`∀`-cast), and the pop is `Λ⊑`'s join or a gen layer's `co-gen`.  The
world itself changes only at the join.

### C6.5 R1 and counterexample C5

R1 (D28; 🆕 **D31**: R1′, §10.5): the left's own seal `[−X^α] V ⟨−X⟩` relates to an arbitrary
right `★` value (the "payload view", P2), which is right when `X` is
left-only, but not under a right check that permitted `α`'s partner:
counterexample C5 relates `[+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩` to
`[+X^α] 5⟨ℕ!⟩⟨X?ℓ0⟩ ⟨+X⟩`, whose right blames
(`examples/TermImprecisionPermissionExamples.agda`, `C5Dead`; source
programs `(ΛY. λx:Y. x) [ℕ] 5` and `(ΛY. λx:★. (x : Y)) [ℕ] (5 : ★)`).
R1 and R2 are rule premises: no condition on worlds alone separates
C5's hidden variant from P4 B3 (`PermissionsR.md` §1.4).

### C6.6 K: the counterexample of D26, related by push, pass and pop

The counterexample of D26 is `(λf:∀X.X→X. f)(K[ℕ])` against
`(λf:★→★. f)(K[ℕ])`, with `K = ΛY.ΛX.λx:X.x`.  After the right's `Inst`
and `Merge`, its final pair `VL ⊑ RF` is related by a push, a pass and
a pop.  Its ladder, generated by
`scripts/render_gtnf.sh 'impLadder VL⊑RF' …` (`examples/ImpLadder.agda`,
where it is pinned):

```
W0 = the conclusion's world
  ⟨⟩
  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ, β:=★]
W1 = Interior W0
  ⟨Y: ─ ⊑[X⊑X] Y^β │ X: ─ ⊑[X⊑X] X^α⟩
  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ, β:=★]  πʷ = [Y^β]
W2 = Interior W1
  ⟨Y: ─ ⊑[X⊑X] Y^β │ X: X^α ⊑[X⊑X] X^α⟩
  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ, β:=★]  πʷ = [Y^β]
W3 = Open1 W2: pop Y^β
  ⟨Y: Y^β ⊑[X⊑X] Y^β │ X: X^α ⊑[X⊑X] X^α⟩
  ϱᵍ = {α⇔α}  ϱˡ = {β⇔β}  Ξᴸ = [α:=ℕ, β abst]  Ξᴿ = [α:=ℕ, β:=★]
W   left term                       A        ηᴸA      ⊑                ηᴿA′  A′   right term
──  ──────────────────────────────  ───────  ───────  ───────────────  ────  ───  ────────────────────────
W0  ─                               ∀X. X→X  ∀X. X→X  ∀X⊑★. X⊑★ → X⊑★  ★→★   ★→★  □⟨id(★) → id(★)⟩^[]
W0  ─ (push Y^β)                    ∀X. X→X  ∀X. X→X  ∀X⊑★. X⊑★ → X⊑★  ★→★   ★→★  [+Y^β, +X^α] □ ⟨−Y → +Y⟩
W1  [+X^α] □ ⟨∀Y. (id(Y) → id(Y))⟩  ∀X. X→X  Y→Y      Y⊑Y → Y⊑Y        Y→Y   Y→Y  ─ (pass Y^β)
W2  ΛY. □                           ∀Y. Y→Y  Y→Y      Y⊑Y → Y⊑Y        Y→Y   Y→Y  ─ (pop Y^β)
W3  λx:Y. □                         Y→Y      Y→Y      Y⊑Y → Y⊑Y        Y→Y   Y→Y  λx:Y. □
W3  x                               Y        Y        Y⊑Y              Y     Y    x
```

The push is a choice: the rule does not say which introduced type
variables to push, and the index decides (`PendingOpenings.md` §6).  No
permission appears: the pending `Y` is `X⊑X` (D28).  🆕 **D31**: the
same derivation with `K = []` at every boundary (`CorpusA.VL⊑RF`).

### C6.7 A grant: P4's block B3

🆕 **D31**: in the ladder below (generated from the D28 Agda), the
permission for `αᴿ` would come from the outer matched boundary `W0 →
W1`, which joins `X` and pays `X ⊑ X` there (`K = [αᴿ]`), instead of
the grant at `W1 → W2`; the rows below `W2` are unchanged
(`CorpusB.p4-B3` in `notes/D28pD30.agda`).

A grant (D28), P4's block B3 (`p4-B3`, pinned in
`examples/ImpLadder.agda`): the right's check `X?` grants `αᴿ`, so
inside it the shared `X` is `X⊑★` (W2), stays `X⊑★` as a left-only type
variable inside the right's `−X` (W3), and the matched seals `S ⊑ S`
relate at the index `X ⊑ X` under the grant:

```
W0 = the conclusion's world
  ⟨⟩
  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ]
W1 = Interior W0
  ⟨X: X^α ⊑[X⊑X] X^α⟩
  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ]
W2 = W1 grant X^α
  ⟨X: X^α ⊑[X⊑★] X^α⟩
  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ]  κʷ = {α}
W3 = Interior W2
  ⟨X: X^α ⊑[X⊑★] ─⟩
  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ]  κʷ = {α}
W4 = Interior W2
  ⟨⟩
  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ]  κʷ = {α}
W   left term        A    ηᴸA  ⊑          ηᴿA′  A′   right term
──  ───────────────  ───  ───  ─────────  ────  ───  ────────────────────────
W0  [+X^α] □ ⟨+X⟩    ℕ    ℕ    ℕ⊑ℕ        ℕ     ℕ    [+X^α] □ ⟨+X⟩
W1  ─ (grant X^α)    X    X    X⊑X        X     X    □⟨X?ℓ0⟩^[X:★∼X]
W2  □₁ □₂            X    X    X⊑★        ★     ★    □₁ □₂
W2  ├ ─              X→X  X→X  X⊑★ → X⊑★  ★→★   ★→★  [−X^α] □ ⟨id(★) → id(★)⟩
W3  │ λx:X. □        X→X  X→X  X⊑★ → X⊑★  ★→★   ★→★  λx:★. □
W3  │ x              X    X    X⊑★        ★     ★    x
W2  └ ─              X    X    X⊑★        ★     ★    □⟨X!⟩^[X:X∼★]
W2    [−X^α] □ ⟨−X⟩  X    X    X⊑X        X     X    [−X^α] □ ⟨−X⟩
W4    5              ℕ    ℕ    ℕ⊑ℕ        ℕ     ℕ    5
```

### C6.8 The `★` clauses of conversion imprecision

The last row of §10.6 mirrors type imprecision's `X ⊑ ★` and `∀⊑`.  A
seal or unseal of a left type variable at `X⊑★` may be absent on the
right, and a left-only universal is opened at `X⊑★`.  R2 (D28) adds
`U(X)`: with "shared type variables have paired rep. vars", `μ(X) = X⊑★`
and `U(X)` force `X` to be left-only in the conversion world (it closes
the matched variant of C5).  C23a needs the bare forms, and C23b needs
the `∀` form.  The chain forms are needed because a left-only `Merge`
builds chains.

------------------------------------------------------------------------

## C7. Examples of cast-term imprecision (P1–P6)

The examples are machine-run: each pair of programs is
in `examples/`, and both of its runs come from `Eval`.

Six pairs, in `ImprecisionExamples.agda`.  Each run is a `Reaches …
refl` proof, and the states below are rendered from `evalTerms` by
`Show.agda` (`scripts/render_gtnf.sh`), not transcribed by hand.  Each
run names its rep. vars by allocation order, so both runs call their first
rep. var `α`.  They are different rep. vars, and `ϱ` pairs them; write `αᴸ`
and `αᴿ` when the difference matters.

The traces are shown **synchronized**: each block is a pair of states
that the relation must relate, and between blocks one side takes one
step while the other takes zero or more steps (the shape of a
simulation, §C10.4).  Under each pair are the rules at the top of its
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

### P1 — both sides instantiate, at ℕ and at ★ (aligned boundaries)

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
are related because the paired rep. vars are.

### P2 — the left side alone abstracts and instantiates (one-sided boundaries)

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
`η` reaches the new center type variable.

### P3 — the right side alone instantiates, by `Inst` (the new rule `∀⊑⟪+⟫`)

```
L  ((λx:(∀X. X→X). ((ν X:=ℕ. (x X) ⟨−X → +X⟩) 5)) (ΛY. (λx:Y. x)))
R  ((λx:★→★. (x 5⟨ℕ!⟩^[])) (ΛX. (λx:X. x))⟨inst Y. (Y?ℓ0 → Y!)⟩^[])
   ·⊑·, ƛ⊑ƛ (∀X.X→X ⊑ ★→★), ν⊑ in the body; ⊑cast, Λ⊑Λ for the argument
                                         L: Beta             R: Inst, TyBeta (α:=★), Beta
L  ((ν X:=ℕ. ((ΛY. (λx:Y. x)) X) ⟨−X → +X⟩) 5)
R  (([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] 5⟨ℕ!⟩^[])
   ·⊑·, ν⊑, ⊑cast, ∀⊑⟪+⟫: the left Λ's abstract rep. var is paired with αᴿ:=★
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
a `Λ`.  That is the reason for `∀⊑⟪+⟫`.

### P4 — the right side alone generalizes (a both-sided type variable at `X⊑★`)

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
   ⊑⟪⟫ (the right rebinds the rep. var αᴿ, which ϱ pairs with αᴸ: X is
   both-sided again), ⊑cast (X!), ⟪⟫⊑⟪⟫
                                         L: —                R: Merge, IdDyn, Merge, TagUntag
L  ([+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩)
R  ([+X^α] ([−X^α, +X^α, −X^α] 5 ⟨−X⟩) ⟨+X⟩)
   ⟪⟫⊑⟪⟫, ⟪⟫⊑⟪⟫ with δ = (−X), δ′ = (−X, +X, −X): the net effect on
   type variables is the same on both sides
                                         L: Merge, Id        R: Merge, Id
L  5
R  5
```

This pair needs two things that P1–P3 do not.  First, a both-sided
type variable at `X⊑★`: inside the `[+X^α]` pair, the left's `λx:X.x`
faces the right's `λx:★.x`, which `gen` has not yet cast to `X → X`.
Second, `ϱ` must survive a right-only unbind: the right's
`[−X^α, +X^α]` hides `X` and rebinds the same rep. var, and only `ϱ`
says that the rebound type variable is the left's `X` again.

### P5 — the left side blames on an escaped tag; the right side succeeds

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

### P6 — a `∀`-cast on the right, and conversions of different shape

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
allocate one rep. var each and the boundaries stay aligned.

------------------------------------------------------------------------

## C8. Counterexamples and open defects

The counterexamples C1–C5 that motivated D28 are presented
from their source programs in
`agda/proof/DGG/notes/ConditionPlacement.md` §3.

### C8.1 Open: left values built by `gen` (TwoGen)

Status (2026-10-06): a known defect of §10 and a proposed fix, checked
in `proof/DGG/notes/TwoGen.agda` (`.md`); the fix is not adopted.  Each
example below has RELATED source programs and related initial cast
terms, its left is a value, and the right's final value is related to
it by no derivation of §10 in any top-level world.  So each is a
counterexample to DGG part 1 (`*.not-dgg : ¬ DGG`).

🆕 **D31** subsumes the fix below: (i) is not needed (the permission
of an opening sits at `⊑⟪⟫`), (ii) is `CastOpen` (§10.2), and (iii)
is the skip slot of the index (§9, §10.5).  D31 relates all seven
final pairs, with DGG part 1 witnesses (§C9.2).

**G0: one `gen` layer.**  Sources (related: the same term, and
`∀X.X→ℕ ⊑ ★→ℕ`):

```
L   (λx:★. 5 : ∀X. X→ℕ)
R   ((λx:★. 5 : ∀X. X→ℕ) : ★→ℕ)
```

Cast terms (related at the empty world, `G0.init`):

```
L₀  (λx:★. 5)⟨gen X. (X! → id(ℕ))⟩
R₀  (λx:★. 5)⟨gen X. (X! → id(ℕ))⟩⟨inst Y. (Y?ℓ0 → id(ℕ))⟩
```

The left is a value.  The right runs:

```
  R₀
⟶ (Inst)
  (ν X:=★. ((λx:★. 5)⟨gen Y. (Y! → id(ℕ))⟩ X) ⟨−X → id(ℕ)⟩)⟨id(★) → id(ℕ)⟩
⟶ (TyBeta, ⊣ α:=★)
  ([+X^α] ([−X^α] (λx:★. 5) ⟨id(★) → id(ℕ)⟩)⟨X! → id(ℕ)⟩^[X:★∼X] ⟨−X → id(ℕ)⟩)⟨id(★) → id(ℕ)⟩
```

Every attempt at the final pair stops (`G0.g0-unrelated`):

```
⊑cast  ⟨id(★) → id(ℕ)⟩, grants nothing          ∀X.X→ℕ ⊑ ★→ℕ
  ⊑⟪⟫  +X^α, push X                            X→ℕ ⊑ X→ℕ   (X is X⊑X)
    cast⊑ (pop at the left's gen):  premise at the gen's source,  ★→ℕ ⊑ X→ℕ   ✗
    ⊑cast ⟨X! → id(ℕ)⟩:  premise needs X ⊑ ★, and X! → id(ℕ) grants nothing  ✗
    cast⊑cast:  needs no pending type variable  ✗
```

The cause (O1): a pop at a left `gen` relates the value under the gen
at the gen's SOURCE type, so the right's cast over the instantiated
gen body (`⟨X! → id(ℕ)⟩`) must first be peeled by `⊑cast` at
`X ⊑ ★`, and under D28 that needs a grant, i.e. a covariant check of
`X`.  G1's body `X! → X?` checks `X`; G0's `X! → id(ℕ)` does not,
although no `X`-tagged value can flow out of it (`X` occurs only
contravariantly).

**G2: two `gen` layers, two right casts.**  Sources (related):

```
L   (λx:★. λy:★. x : ∀X. ∀Y. X→Y→X)
R   (((λx:★. λy:★. x : ∀X. ∀Y. X→Y→X) : ∀Y. ★→Y→★) : ★→★→★)
```

The right instantiates twice.  The second `Inst` goes through the first
boundary and its gen layer, so its boundary `+Y^β` is born OUTSIDE
`+X^α`, and the `∀`-cast between them blocks the `Merge`.  The right's
final value:

```
([+Y^β] ([+X^α] ([−Y^β, −X^α] (λx:★. (λy:★. x)) ⟨id(★) → (id(★) → id(★))⟩)⟨X! → (Y! → X?ℓ0)⟩^[X:★∼X, Y:★∼X] ⟨−X → (id(Y) → +X)⟩)⟨id(★) → (id(Y) → id(★))⟩^[Y:X∼X] ⟨id(★) → (−Y → id(★))⟩)⟨id(★) → (id(★) → id(★))⟩^[]
```

Inside `+Y^β` the only right type variable is `Y`, with interior type
`★ → Y → ★`.  The left's `∀X.∀Y.X→Y→X` must open its INNER `∀` at `Y`
while its outer `∀` waits; pending type variables open the outer one
first (O2, `G2.g2-unrelated`).  This is H1's problem (D29) for `gen`
binders, and `claim-rep` cannot help: a `gen` binder scopes over no left
term, so the left context cannot grow above the right boundaries.

The other five pairs combine these: two gen layers with one right cast
and a `Merge` (G2m, O1: one pop per gen); a gen under a `∀` over a `Λ`
(HRm, HR); nested gen casts (N2, merged and with two casts).

**Proposed fix** (a local variant `V2` of §10; three changes):

1. **Pop against a right cast.**  `cast⊑cast` may run with pending
   type variables and carry a claim on its LEFT coercion, so a left gen
   layer pops its type variable against the right's cast without a
   grant:

   ```
     W.π := πₚ ∣ γ ⊢ M ⊑ M′ : B ⊑ B′    c claims π ↦ πₚ
     c : B ⇒ A    c′ : B′ ⇒ A′
     ──────────────────────────────────────────────────────────── (cast⊑cast, (i))
     W.π := π ∣ γ ⊢ M ⟨c⟩ ⊑ M′ ⟨c′⟩ : A ⊑ A′
   ```

   This is the shape the left's own instantiation produces: `inst-gen`
   turns `V⟨gen X.p⟩` into `([−X^α] V⟨…⟩)⟨p⟩`, the right's term.
2. **One pop per gen layer.**  The claim continues below a pop:
   `gen X. gen Y. p` pops `X` then `Y`; `gen X. ∀Y. p` pops `X` and
   passes `Y` on.
3. **Skip a waiting `∀`, for gen-cast values only.**  The index may skip
   a leading left `∀`, which stays left-only at `X⊑★` (as type
   imprecision's `∀⊑`), before opening the next `∀` at a pending type
   variable; and `⊑⟪⟫` may push new type variables before carried ones.
   This is the gen analogue of `claim-rep`: the waiting binder lives in
   the index, because there is no left term to claim it.

G2 under the fix (`Pos2.g2-final`):

```
⊑cast  ⟨id(★) → (id(★) → id(★))⟩                         ∀X.∀Y.X→Y→X ⊑ ★→★→★
  ⊑⟪⟫  +Y^β, push Y;  index: SKIP X (left-only), open Y at Y   X′→Y→X′ ⊑ ★→Y→★
    ⊑cast  ⟨id(★) → (id(Y) → id(★))⟩
      ⊑⟪⟫  +X^α, push X BEFORE the carried Y;  pending [X, Y]  X→Y→X ⊑ X→Y→X
        cast⊑cast  ⟨gen X. gen Y. …⟩ ∥ ⟨X! → (Y! → X?ℓ0)⟩: pop X, pop Y
          ⊑⟪⟫  −Y^β, −X^α                                    ★→★→★ ⊑ ★→★→★
            ƛ⊑ƛ, ƛ⊑ƛ, x⊑x
```

G0 under the fix: push `X`, then `cast⊑cast` pops `X` against
`⟨X! → id(ℕ)⟩`, then the right's `−X^α`.

**Checks** (mechanized in TwoGen): changes 1–2 alone relate G0, G2m,
HRm and N2-merged; all three relate all seven final pairs and G2's
intermediate states, and DGG part 1 holds on each.  §10's relation is
contained in the variant, so the corpus derives; C1–C5 and C4g stay
not derivable (their left terms contain no gen or `∀` casts, and a
variant derivation of such a term maps back to a §10 derivation).

**Open.**  Sim and SimBack against the new cases are not checked (a left
`TyBeta` catching up with a `cast⊑cast` pop, instantiating at a skipped
`∀`, a new-first push), nor whether changes 1 or 3 relate some
gen-valued pair that should not be.  An alternative for O1 alone: count
a type variable that never flows out as checked ("vacuous" grants); G2m
would still need change 2.  The principled form of change 3 is pending
rep. vars whose entries with no type variable bound to them open
left-only (PushOrder.md, fix (c3)); the skip is its index-only shadow.

### C8.2 What the examples say about the sketch

- **The world never rebases.**  In all six pairs, `Ω`, `η`, `η′` and
  `μ` change only at a binder or a boundary entry, for the subterm
  under it.  `ϱ` gains a pair at a matched `TyBeta` (P1, P4, P6) and
  at the left's catch-up `TyBeta` in P3.
- **Rules used.**  Every rule of §10 is used except `⊕⊑⊕` (no
  example has an operator).  P2 and P5 need the left-only boundary
  rule `⟪⟫⊑`.  P4 needs
  the right-only rule `⊑⟪⟫`, with both an unbind and a rebind.  P3
  needs `∀⊑⟪+⟫` (at a `Λ`).
- **Not exercised.**  A gen cast on both sides; a gen cast on the left
  only (its `[−X^α]` is then a left-only unbind of a both-sided type
  variable); `bot-elim`/`bot-intro`; an escaped tag that comes back into
  scope (Example 5) on one side only; two-allocation runs (D8).
- **Open questions** (to be settled one at a time):
  1. *Settled (D11).*  A both-sided type variable gets the mark `X⊑★` at
     its binder (`W ⊕ X:m`, `W[δ ∥ δ′]`), not by GTSFImp's `ImpEnvMono`
     decay at the cast rules.
  2. *Settled (D12).*  `ϱ` stays in the world as a global relation on
     rep. vars; the relation on type variables stays lexical.  P4's
     rebind reads `ϱ`.
  3. Whether `W[δ ∥ δ′]` should be restricted (for example, forbid a
     left-only unbind of a both-sided type variable), or whether such
     restrictions should come from the DGG proof.

     *Finding (probe `notes/LeftOnlyUnbindProbe.agda`; corrected).*  The
     probe's left coercion `gen X. inst Y. ((X! ; Y?ℓ) → (Y! ; X?ℓ))` is
     a well-typed GTNF coercion, and a §10 world relates its run to the
     direct cast's only at the start.  But compilation never produces
     it.  It is not the image `⟦c⟧ℓ` of any consistency evidence: inside
     it, `X ∼ Y` would be needed for two distinct type variables, and
     consistency is not transitive (`_!` and `？_` only give `A ∼ ★` and
     `★ ∼ B`).  This agrees with the specification "two types are
     consistent if and only if they have a common lower bound" (Jeremy,
     2026-10-01).  `∀X.X→X`'s only lower bound is itself, so `∀Y.Y→★`
     (which `∀X.X→X ⋢ ∀Y.Y→★` excludes) is not consistent with it.
     GTSFImp's `lower?` agrees, checked by `refl`: it finds a lower
     bound for `∀Y.Y→Y ∼ ∀X.X→X` and none for `∀Y.Y→★ ∼ ∀X.X→X`.  Closed
     types have only `CrossFree` evidence, so `∼→∼ᵘ`
     (`proof/Consistency2.agda`) rules out declarative evidence for the
     latter as well.  So the probe's pair is outside the image of
     compilation.

     *`gen` does not produce it (argument, and a search).*  At a shared
     `X` (`∀X.B ⊑ ∀X.B′` by `∀⊑∀`), if the more precise evidence
     `c : A ∼ ∀X.B` handles `X`'s binder by `gen`, then so does the
     less precise `c′ : A′ ∼ ∀X.B′` (with `A ⊑ A′`).  Each alternative
     for `c′` fails:

     - `∀ᶜ` identifies a binder of `A′` with `X`.  Then on the left the
       corresponding binder of `A` faces `X`, a distinct type variable,
       and consistency cannot relate two distinct type variables.
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
     pairs with a left `gen`) and with one free cross-mode type variable
     (35,649).  A control in which `X` is left-only (`∀⊑`) gives 343
     hits, so the search can fire.

     *But another producer exists (cambridge26 check, finding F4).*
     `Merge` can fuse two boundaries on one side only, when the other
     side has a cast between its two boundaries.  `Wrap`'s dual of the
     fused boundary then unbinds both type variables on that side alone.
     In C23a the left fuses `[+Y^β][+X^α]`, and its `Wrap` dual
     `[−X^α, −Y^β]` faces the right's `[−X^α]`:

     ```
     L  (([+Y^β, +X^α] (λx:Y. ([−X^α, −Y^β] 42 ⟨−X⟩)) ⟨−Y → +X⟩) 69)
     R  (([+Y^β] ([+X^α] (λx:Y. ([−X^α] 42⟨ℕ!⟩^[Y:X∼X] ⟨−X⟩)) ⟨id(Y) → +X⟩)⟨id(Y) → id(★)⟩^[Y:X∼X] ⟨−Y → id(★)⟩) 69)
     ```

     The shared `Y` is then right-only inside, and nothing there
     mentions it, so the block is derivable.  So this row of the table
     does occur.  Restricting `W[δ ∥ δ′]` against it would make C23a
     underivable, so `W[δ ∥ δ′]` stays unrestricted.

### C8.3 The cambridge26 pairs against §10

`notes/cambridge-imprecision-check.md` checks the 22 pairs of
`CambridgeExamples.agda` block by block, in the format of §C7.  19
are derivable as written.  C12, C13 and C14 are not, with any
synchronization (F3).  Findings, smallest first:

- **F1 (settled, D14).**  `Λ⊑⟪+⟫` fixes the new type variable's mark at
  `X⊑X`.  It should read `W ⊕ X:m` with the mark chosen at the binder
  (D11).  Cg's right-led block needs `X⊑★`.
- **F2 (settled, D14).**  `Λ⊑⟪+⟫` covers only a left `Λ`.  The block is forced by
  the simulation shapes of §C10.4.  Take `L = Example 2` and
  `R = (λx:★→★. x 5⟨ℕ!⟩)(I★⟨gen⟩⟨inst⟩)`.  In the forward direction,
  the left's step `Beta` makes the right catch up through `Inst`,
  `TyBeta` and `Beta`.  The right cannot `Beta` earlier, because its
  argument's `inst` cast is not inert.  In the backward direction, the
  right's first step `Inst` needs either a `⊑ν` rule or a further
  `TyBeta`, which leads to the same block.  A left `gen`-cast
  ∀-value facing the right's `[+X^β] V′ ⟨c′⟩` needs the same rule,
  so it should be stated for every ∀-value through `inst_X` at the
  left's abstract rep. var (C2's right-led block):

  ```
    W ⊕ X:m ∣ [] ⊢ inst_X(V) ⊑ V′ : A ⊑ A′    V a ∀-value    β:=★    c′ : A′ ⇒ B′
    ────────────────────────────────────────────────────────────────── (∀⊑⟪+⟫)
    W ∣ γ ⊢ V ⊑ [+X^β] V′ ⟨c′⟩ : ∀X.A ⊑ B′
  ```

- **F3 (settled, D13).**  `ϱ` cannot be a partial bijection.  In C12
  (`I⟨inst⟩⟨gen⟩` on the right), the left's one rep. var `α:=ℕ` must be
  paired with two right rep. vars: the right's `β:=ℕ`, from the
  instantiation that both sides make, and the right's `α:=★`, from
  `Inst`.  The block is

  ```
  L  (([+X^α] (λx:X. x) ⟨−X → +X⟩) 5)
  R  (([+Y^β] ([−Y^β] ([+X^α] (λx:X. x) ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[] ⟨id(★) → id(★)⟩)⟨Y! → Y?ℓ0⟩^[Y:★∼X] ⟨−Y → +Y⟩) 5)
  ```

  The outer pair needs `(αᴸ, βᴿ)`.  The inner right-only `[+X^αᴿ]` must
  rejoin the same center type variable, which needs `(αᴸ, αᴿ)`.  Under
  the proposed fix, each right rep. var has at most one left partner,
  and a left rep. var may have several.  With it, C12–C14 go through.

  *The mirror needs nothing (checked on the existing runs).*  Put
  `I⟨inst⟩⟨gen⟩` on the left, that is, C12's right program, against
  three less precise partners:

  - **M1:** `Cf-R` (`I★⟨gen⟩`).  The outer boundaries pair
    `(βᴸ:=ℕ, αᴿ:=ℕ)`, and the two `gen` unbinds match.  The left's
    `Inst` boundary `[+X^αᴸ]` (`αᴸ:=★`) is left-only, its type variable
    has mark `X⊑★`, and then `λx:X.x ⊑ λx:★.x` holds.
  - **M4:** Example 1 (`I⟨inst⟩`, with no `gen` and no `[ℕ]`), against
    the application form `(λf:∀X.X→X. f[ℕ] 5)(I⟨inst⟩⟨gen⟩)` on the
    left.  The two `Inst`/`TyBeta` pairs match, giving `(αᴸ, αᴿ)`.
    The left's `[ℕ]` is a left-only `ν`, and its `[+Y^β]` and `gen`
    unbind `[−Y^β]` are left-only too.  (`C12-R` itself is the bare
    redex `at-ℕ-5 (I⟨inst⟩⟨gen⟩)`.  Paired directly with Example 1 it
    is not related at the start, because the function parts have
    unrelated types.  The re-check, `notes/cambridge-imprecision-check-v2.md`,
    confirms that the post-`Beta` suffix is derivable with `ϱ`
    one-to-one.)
  - **M2:** `Cg-R` (`I★⟨gen⟩⟨inst⟩`).  The right's `Inst` rep. var
    `α:=★` pairs with the left's `[ℕ]` rep. var (`ℕ ⊑ ★`), the two `gen`
    unbinds match, and the left's `Inst` boundary is left-only.

  In all three, `ϱ` stays one-to-one.  The asymmetry comes from type
  imprecision, which has no rule with a bare variable on the less
  precise side (the same remark is in GTSFImp's
  `proof/DGG/CastTermImprecision.agda`).  So an extra left type variable
  can stay left-only, with the right seeing `★` (`X⊑★`).  An extra right
  type variable cannot stay right-only, because no left type is more
  precise than it, so it must rejoin a left type variable.  That rejoin
  is what forces C12's second pair.  So the fix is needed in one
  direction only: a right rep. var has at most one left partner, and a
  left rep. var may have several.
- **F4.**  A one-sided `Merge` also produces a left-only unbind of a
  shared type variable (§C8.2, question 3).
- **D1 (settled, D15).**  `W[δ ∥ δ′]` must say which intermediate worlds of a
  multi-entry `δ` have to be well formed, and that a type variable keeps
  its mark when it goes one-sided and later rejoins.
- **D2 (settled, D16).**  `∀⊑⟪+⟫`'s pair involves the left value's abstract rep. var,
  which is not in `rv(Δ)`.  `ϱ`'s type has to allow it.

**Re-check under D13–D16** (`notes/cambridge-imprecision-check-v2.md`).
All 22 pairs support both simulations of §C10.4, forward and backward.
C12, C13 and C14 now go through: one left rep. var has two, two and
three right partners, as D13 permits.  Cg's and C2's right-led blocks
go through with `∀⊑⟪+⟫` (D14).  C2's multi-entry boundary goes
through under D15.  The `Λ`-bound pairs are in `ϱˡ` (D16).  C23a
confirms that `W[δ ∥ δ′]` must stay unrestricted.  The mirror pairs
M1 and M2 keep `ϱ` one-to-one, and so does M4's post-`Beta` suffix.

------------------------------------------------------------------------

## C9. Sketches and proposals

### C9.1 Sketch: allocation hands the `ν` invariants to the world

Status: sketch (2026-10-06; Jeremy), not adopted, not checked.  The
problem it addresses: the relation is tight enough on related source
programs, but it drops invariants as the terms reduce, so states that
no related start reaches become related (C1–C5,
`agda/proof/DGG/notes/ConditionPlacement.md` §3).

**What a `ν` pair knows, and what `TyBeta` drops.**  Matched `ν`s are
the one place where both sides' ∀ types, payloads and conversions meet:

```
  W ∣ γ ⊢ L ⊑ L′ : ∀X.C ⊑ ∀X.C′    A ⊑_W A′    c ⊑ c′
  ──────────────────────────────────────────────────── (ν⊑ν)
  W ∣ γ ⊢ ν X:=A.(L X)⟨c⟩ ⊑ ν X:=A′.(L′ X)⟨c′⟩
```

After the two `TyBeta`s the `ν`s are gone:

```
ν X:=A.(L X)⟨c⟩  ⟶ (TyBeta, ⊣ α:=A)  [+X^α] inst_X(L) ⟨c⟩
```

| what `ν⊑ν` checked | after `TyBeta` |
|---|---|
| payloads `A ⊑ A′` | in the stores; paired rep. vars agree (D23) |
| conversions `c ⊑ c′` | kept by the boundaries; re-checked by `⟪⟫⊑⟪⟫` only |
| the ∀ types, `C ⊑ C′` with `X` matched at `X⊑X` (`∀⊑∀`) | **dropped** |

C1's sources are `((ΛX. λx:X. x) : ★→★) 5 : ℕ` against
`((ΛX. λx:X. (x : ★)) : ★→★) 5 : ℕ`.  No `ν` pair relates them, because
`∀X.X→X ⊑ ∀X.X→★` fails.  After both sides' `Inst` and `TyBeta` the
boundaries are

```
[+X^α] (λx:X. x) ⟨−X → +X⟩      against      [+X^α] (λx:X. x⟨X!⟩) ⟨−X → id(★)⟩
```

and `⟪⟫⊑⟪⟫` never asks whether `X→X` and `X→★`, read as functions of
the bound `X`, are related with `X` matched.  That is the dropped
invariant.

**The proposal: each rep. var pair carries an interface.**  A pair
`(αᴸ, αᴿ)` in `ϱ` records the bodies `(C, C′)` of the two ∀ types whose
instantiation allocated it, as representation types (type variables
resolved to rep. vars, so the record survives renaming, `Merge` and
`exitEnv`; compared as in D23).

- **Created at allocation.**  A matched pair of `TyBeta`s (Evolve's
  `ev-2`) creates the pair from the `ν⊑ν` derivation:
  interface `(C, C′)`.  A right `Inst` against a left ∀-value (the
  push and pop of D27, or `claim-rep` of D29) creates the pair from the
  index of the pair before `Inst`.  A left-only `ν⊑` creates a left-only
  rep. var; its interface is `C` against the right type it faced
  (`∀⊑`, `X⊑★`).
- **Well-formedness.**  For every pair, `C ⊑ C′` holds with the bound
  variable at `X⊑X`, i.e. the `∀⊑∀` that the `ν`s needed.
- **Read at every binding rule.**  A boundary rule that binds a type
  variable `X` to a paired rep. var, matched (`⟪⟫⊑⟪⟫`) or one-sided
  (`⟪⟫⊑`, `⊑⟪⟫` including a push), and the joins of a pop or a
  `claim-rep`, require the boundary's interior type, abstracted over
  `X`, to be the side's recorded interface body.  No cast rule reads or
  changes it (the world changes only at binders).

**On the examples.**

- **C1.**  A world that pairs the two `α`s must record `(X→X, X→★)`,
  and `X→X ⊑ X→★` with `X` matched is not derivable.  So no
  well-formed world relates C1's states: the dropped invariant is back.
- **C2–C5** (sources in ConditionPlacement §3): their ∀ types are
  `∀Y.Y→Y` against `∀Y.Y→★` or `∀Y.★→Y`, so their interfaces fail the
  same way; C4's is the push type premise (`PushTypePremise.md`) as one
  case of this rule.
- **K.**  The right's `Inst` of `VL` against the left's `VL`: the pair
  before `Inst` relates them by `Λ⊑Λ`, interface `(Y→Y, Y→Y)`.
- **P4.**  The matched `ν`s relate `x ⊑ x` at `∀X.X→X ⊑ ∀X.X→X`, so
  the interface is `(X→X, X→X)`: it holds.  P4 also needs `X⊑★` inside
  the right's `gen` wrapper; that is a question about marks, below.
- **G0** (§C8.1).  The right instantiates the left's own gen-value:
  interface `(X→ℕ, X→ℕ)`, which holds.

**Marks.**  If the interface is what C1–C5 violate, the marks may not
need to carry that burden.  Hypothesis (unchecked): with interfaces
recorded and checked at every binding rule, a shared type variable may
again take `X⊑★` inside (D11's choice, or a status recorded with the
pair at allocation, e.g. "the left binder faced a right `gen`", as in
P4), and D28's permissions and R1/R2 may become unnecessary.  The reason
to expect it: an `X`-tagged right value causes a blame only when a check
other than `X?` meets it, inside or at the boundary (`TagUntagBad-⟪⟫`);
a mismatch at the boundary is ruled out by the interface (checked at
`X⊑X`), and one inside would put a non-`X` check on the right where the
left has an `X`-typed term, which the types forbid without a matching
left cast.

**Open.**
- Whether the hypothesis holds, against C1–C5, C4g, the TwoGen pairs,
  P4 and the corpus.
- The exact statement of "the interior type, abstracted over `X`" for
  a multi-entry boundary and after a `Merge`.
- The audit (below) may find more dropped invariants.

**Audit result (2026-10-06, `agda/proof/DGG/notes/ReductionAudit.md`).**
Correction to the table above: under D28 the matched `TyBeta` does not
drop the `∀⊑∀` fact, since the derived `X⊑X` re-checks it; it is lost
only under a later grant, after `Wrap`, or after `Merge`.  Recorded
interfaces turn out to be neither needed nor checkable (after `Wrap` or
`Merge` a boundary's interior type is only part of the ∀ body, and C5's
late states fit a trivial interface, `iface-fake`), so the hypothesis
about R1/R2 is refuted.  The audit found two `¬ Sim` counterexamples
from related sources (P4k, P4h) and proposes D28′: permissions chosen at
the binding rule that joins a type variable, with an `X⊑X` check of its
interior types there, no grants at casts, and R1 refined to unbinds
whose rep. var occurs in the exterior type.  (D28′ is now part of the
D31 proposal, §C9.2.)

**Audit (done; was queued).**  For each reduction rule that changes binders or
casts (`TyBeta`, `Inst`, `Wrap`, `Merge`, `IdDyn`, `IdDyn-var`,
`CastFun`, the `inst_X` cases, `TagUntag`, `exitEnv`): the premises
that relate its redex, what the rules for the contractum check, and
what is dropped in between, each on a concrete pair from related source
programs.  Every dropped invariant becomes world data created at the
step and read at a binding rule.

### C9.2 🆕 D31: D28′ + D30 combined

Status: PROPOSED 2026-10-09 (Jeremy approved the write-up); not
adopted.  The rule set is checked in
`agda/proof/DGG/notes/D28pD30.agda` (`.md`), a local variant
`_∣_⊢_⊑ᴰ_∶[_]_` of `TermImprecision`; the main Agda and
`Imprecision.agda` are unchanged.  The changed definitions are marked
🆕 **D31** in §9 and §10 (§10.2, §10.3, §10.5, §10.7).  D31 is the two
earlier proposals D28′ (permissions chosen at joining binders,
2026-10-07) and D30 (openings in the index, 2026-10-08), checked
together, with three adjustments.

**Why.**

- **P4k and P4h** (`ReductionAudit.md` §1), both from related sources,
  refute `Sim` under D28 (`P4k.not-sim`, `P4h.not-sim`).  After the
  left's `TyBeta` and the right's matched `TyBeta`, no world relates
  the pair: inside the right's `X! → …` wrapper the shared `X` must be
  `X⊑★`, and no right check grants it.  D28′'s answer: the boundary
  that JOINS `X` (here the matched `+X ∥ +X`) may permit `X`'s right
  rep. var for its interior, and pays by reading its interior index
  with `X` at `X⊑X`.
- **TwoGen** (§C8.1).  G0, G2m, HRm and N2.Merged fail because a gen
  pop needs a grant (O1); G2, HR and N2.TwoCast because the left's
  inner `∀` must open first (O2).  All seven have related sources.
- **Openings are not world data** (D30).  A pending type variable only
  changes how the index is read (`CtxImp` never read `πʷ`), and two of
  the three binders that consume one, a `gen X.p` and a `∀X.p`
  coercion, have no term in their scope.  So the openings belong to
  the index, and the world changes only at term binders (Jeremy,
  2026-10-06/07/08).
- **C1–C5 and C4g must stay dead.**  The payment is what keeps them
  dead now that `κ` may grow; HEAD's invariant "`κ` stays `[]`" is
  replaced by reading the paying boundary's index.

**Joins, not introduces.**  A permission may be added only by a
boundary that JOINS the type variable (`JoinRep`).  If a boundary that
only introduces it could permit it, C1's right-first route would
revive: the right's `+X` would pay a vacuous `★ ⊑ ★` (the type
variable is right-only, so the left's term there is the whole left
boundary), the left's later `+X` would rejoin inside an already loose
region for free, and `S ⊑ S⟨X!⟩` would follow at `X⊑★`.  A type
variable the boundary only continues, or rejoins inside a region
where it is already permitted, pays nothing (P4 B4's `J`).

**Example: P4k's pair after both `TyBeta`s** (`P4kᴰ.post`):

```
L  (([+X^α] (λx:X. 5) ⟨−X → id(ℕ)⟩) 5)
R  (([+X^α] ([−X^α] (λx:★. 5) ⟨id(★) → id(ℕ)⟩)
       ⟨X! → id(ℕ)⟩^[X:★∼X] ⟨−X → id(ℕ)⟩) 5)
```

```
·⊑·
  ⟪⟫⊑⟪⟫  +X^α ∥ +X^α: X joined (ϱᵍ)
         K = [αᴿ];  pays X→ℕ ⊑ X→ℕ
    ⊑cast ⟨X! → id(ℕ)⟩         X→ℕ ⊑ ★→ℕ  (αᴿ permitted)
      ⊑⟪⟫ −X^α                 X left-only
        ƛ⊑ƛ, κ⊑κ
  κ⊑κ
```

The run goes on related: the left's `Wrap` against the right's `Wrap`
and against the right's `CastFun` (`P4kᴰ.wrap`, `P4kᴰ.castfun`; the
latter is D28's R12 site).

**Example: K's final pair** (§C6.6's ladder), read with D31:

```
⊑cast           ∀X.X→X ⊑ ★→★                      (O = [])
  ⊑⟪⟫  [+Y^β, +X^α], open at Y
                ∀X.X→X ⊑^[Y] Y→Y  =  Y→Y ⊑ Y→Y
    ⟪⟫⊑  [+X^α] … ⟨∀Y. …⟩, pass   ∀Y.Y→Y ⊑^[Y] Y→Y
      Λ⊑  join ΛY to Y      world: Y joined; Y→Y ⊑ Y→Y
        ƛ⊑ƛ, x⊑x
```

The only world change is at `ΛY`, a term binder; the opening lives in
the index from `⊑⟪⟫` down to `Λ⊑`.  Every boundary takes `K = []`.

**Adjustment 1: `cast⊑` follows the coercion's binder layers**, not
D30's `drop k O`.  HRm's left value is

```
(ΛX. (λx:X. (λy:★. x)))
  ⟨∀Y. (gen Z. (id(Y) → (Z! → id(Y))))⟩^[]
```

The right's merged `Inst` boundary opens `∀X.∀Y.X→Y→X` at `[X, Y]`.
The cast's target has two outer `∀`s and its source one, so D30's
count gives `k = 1`, and `drop 1 [X, Y] = [Y]` would open the `Λ`'s
`∀` at `Y`: the `Λ` would face `Y→★→Y` against the right's `X→★→X`.
But the source's `∀` is the cast's `∀Y` layer, which belongs to the
opening `X`.  `CastOpen` passes `X` to the `Λ` (`co-∀`) and uses `Y` up
at the gen layer (`co-gen`), and HRm derives (`TwoGenᴰ.bodyH`).  This
is also TwoGen's (ii), one consumption per gen layer, for free.

**Adjustment 2: the permission of an opening is chosen at `⊑⟪⟫`**,
where the opening is created, not at `Λ⊑`.  The opening is the join
at the level of the index, and `⊑⟪⟫` is a term binder (a boundary
entry), so the world still changes only at term binders.  A left gen
value uses its opening up at a CAST, which binds no term and may not
change the world; with the permission at `Λ⊑`, G0, G2m, HRm and N2
would need TwoGen's (i).  With it at `⊑⟪⟫` they do not.  G0's left gen
value against the right's `Inst` boundary (`TwoGenᴰ.G0ᴰ.g0-final`):

```
⊑cast  ⟨id(★) → id(ℕ)⟩              ∀X.X→ℕ ⊑ ★→ℕ
  ⊑⟪⟫  +X^α: open at X, K = [α]
       pays ∀X.X→ℕ ⊑^[X] X→ℕ  (X ⊑ X)
    ⊑cast  ⟨X! → id(ℕ)⟩             ∀X.X→ℕ ⊑^[X] ★→ℕ
                                     (X⊑★: α permitted)
      cast⊑  gen: uses X up (co-gen)  ★→ℕ ⊑ ★→ℕ
        ⊑⟪⟫  −X^α                    ★→ℕ ⊑ ★→ℕ
          ƛ⊑ƛ, κ⊑κ
```

The payment reads the opened left type against the boundary's
interior type at `X⊑X`: what a payment at `Λ⊑` would read, up to the
`∀` conversions and `∀` casts between the two.  It is not vacuous: C4,
C4g and the hunt's gen-valued C4 fail it.  `Λ⊑`'s join then needs
nothing beyond `Join1`.  G2m, HRm and N2.Merged are G0 with two
openings `[X, Y]` and `K = [α, β]`.

**Adjustment 3: skip slots** (TwoGen's (iii), as a value of the
index).  G2's right nests `[+Y^β]` outside `[+X^α]`, with the cast
`⟨id(★) → (id(Y) → id(★))⟩` between them (TwoGen.md §1).  Write
`K2 = ∀X.∀Y.X→Y→X` (`TwoGenᴰ.twoCast`, `g2-final`):

```
⊑cast  ⟨id(★) → (id(★) → id(★))⟩       K2 ⊑ ★→★→★
  ⊑⟪⟫  +Y^β: new slots [_, Y], K = [β]
       pays K2 ⊑^[_,Y] ★→Y→★
       (X left-only against ★, Y ⊑ Y)
    ⊑cast  ⟨id(★) → (id(Y) → id(★))⟩    K2 ⊑^[_,Y] ★→Y→★
      ⊑⟪⟫  +X^α: carried [_, Y]; X FILLS the skip:
           [X, Y]; K = [α];  pays K2 ⊑^[X,Y] X→Y→X
        G2m's body (as G0, two gen layers)
```

TwoGen's V2 encoded the skip as a nondeterministic reading of the
index (`OpenImpS`) plus a new-first push (`pv-new`), so every rule
whose world might hold pending type variables took an `OkIx` premise.
Under D31 a skip is created only by `⊑⟪⟫` (for a left gen-cast value,
`GenCastValue`), used up by a gen layer (`co-gen` takes any slot) or
filled by `Fill`; no other rule mentions it.  HR and N2.TwoCast are
the same.

**R1′** (`UnbindOK′`) reads the boundary's exterior type.  A seal
`[−X^α] V ⟨−X⟩` always has exterior `X`, so on seals R1′ is R1, and
C5's seal `[−X^α] 5 ⟨−X⟩` is still rejected.  It relaxes only pure
hides (conversion `Id(A)`, `X ∉ A`), which create no left `X`-value.
P4h needs it: its crossΛ hide `[−X^α] (λy:ℕ. y) ⟨id(ℕ) → id(ℕ)⟩`,
whose exterior `ℕ→ℕ` does not mention `X`, sits under the permitted
`αᴿ` (`P4hᴰ.H⊑`; R1 rejects it, `P4hᴰ.r1-rejects`).

**Checked** (all in `notes/D28pD30.agda`; no holes, no postulates):

| check | result | Agda |
|---|---|---|
| corpus: P1–P6, K, H1, Cg, C2 X0, G1, C12–C14 B1, C18b B7, L3c, L3d, R2c, Ch | derives | `CorpusA.*` … `CorpusE.*`, `P5ᴰ.*`, `R2cᴰ.*` |
| P4k, P4h (`¬ Sim` under D28) | the `TyBeta` pair is related (P4k also its `Wrap` and `CastFun` states) | `P4kᴰ.post`, `wrap`, `castfun`; `P4hᴰ.post` |
| TwoGen G0, G2m, G2, HRm, HR, N2 (both) (`¬ DGG` under D28) | final pairs related; DGG part 1 witnesses | `TwoGenᴰ.*`, `DGG1ᴰ.*` |
| C1 (all routes), C2 late, C3 early, C4, C4g | dead at every world with `κʷ ≡ []`, any slots | `C1ᴰ` … `C4gᴰ` |
| C5, its redex, its hidden variant | dead at every world, any κ | `C5ᴰ.*` |
| hunt | no counterexample; a gen-valued C4 is dead | `Hunt.c4gen-unrelated` |
| HEAD's relation without grants | a sub-relation | `toD` |

P5 and R2c had no Agda derivation before; both are derived from their
programs.  Every D28 grant of the corpus is re-derived as a permission
at the enclosing joining boundary (D28pD30.md §3).

**Open obligations** (argued, not checked; D28pD30.md §8):

- **`Wrap` needs κ-weakening.**  `Wrap` puts the argument into the
  dual `[−δ] W ⟨c⟩` INSIDE the function's boundary, whose interior
  carries that boundary's `K`; R1′ and R2 are anti-monotone in `κ`.
  D28's R12 moves from `CastFun` to `Wrap`; it does not disappear.
  When the payload view is at the argument's top, the pair can be
  re-related matched (seal ⊑ seal), as in `P4kᴰ.wrap`.  A general
  lemma is open.
- **`Merge` can lose a rejoin's permission.**  A right hide `[−X^α]`
  merged with an inner rejoin `[+X^α]` makes `X` continuing, and
  `JoinRep` admits only type variables the boundary introduces.  In
  every corpus `Merge` (P4c R7–R10, R2c) the permission comes from an
  outer join, so nothing is lost.  A possible fix: `JoinRep` also
  accepts a type variable that an entry of the boundary rebinds and
  that is joined inside (the merged `[−X, +X]`), paying the same index.
- **Not ported:** G2's intermediate states 2 and 4 (TwoGen
  `G2st.InV2`).
- **Sim/SimBack** for the new cases: `co-gen` with a continuation, the
  `K`/payment premises of the three boundary rules, and a `K` chosen by
  a matched `TyBeta` or by `PushInstR`.

------------------------------------------------------------------------

## C10. Metatheory discussion

### C10.1 Type imprecision is not consistency

GTNF's types are GTSFImp's, so the type-level imprecision is ported
unchanged (`GTNF/agda/Imprecision.agda`, §8).  The imprecision environment `ImpEnv` is a different lattice
from the consistency modes `Env∼` of §3.  The two must not be conflated:
imprecision relates two programs, and consistency types the casts
within one program.

### C10.2 Static gradual guarantee

GTSFImp's term imprecision `μ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p`
(`GradualTermImprecision.agda`) is typed and carries both typings
(`gradual-term-imprecision-source-typing`/`-target-typing`).  I did not
find a standalone static gradual guarantee in GTSFImp.  For GTNF, the
plan is to state `sgg` against an *untyped* syntactic term imprecision,
and to derive the typed relation from it.  Since the source language is
GTSFImp's, `sgg` is really a theorem about GTSFImp's source; it could be
proved there and reused here.

### C10.3 Compilation preserves imprecision

In GTSFImp the world `W` aligns the two runs' type stores.  In GTNF it
must align the two runs' representation variables (`α`) and their type
variables (`X:=α`), and it must relate boundaries `[δ] M ⟨c⟩` on the two
sides, including one-sided boundaries.  This is the largest new design
item in the metatheory.  §9–§10 define it.

**Why GTNF is shaped for this relation.**  In earlier gradually typed
polymorphic calculi (GTSF, GTSFImp, PolyBlameI and others), the hardest
part of the DGG was defining a cast-term imprecision that reduction
preserves.  Within that, the hardest part was discovering the right
invariant relating the type variables of the two programs.  In
GTSFImp, for example, the world `W` and its rebasing (`RebaseAt`) evolve
with the two runs' global type stores.  GTNF was designed to make this
step more straightforward (Jeremy, 2026-10-01).  It is explicit about
type variables: every type variable `X` is bound to a representation
variable (`X:=α`) by a `Λ`, a coercion binder, or a boundary entry
`+X^α`.  It also treats them locally, in a lexically scoped way: a type
variable is in scope only inside the boundary that binds it, and
coherence makes type variables and representation variables correspond
one to one within any conversion context.  The hope is that the
invariant between the two programs' type variables can then be stated
boundary by boundary, as a relation between matching `δ`s and their
type variables, instead of as a global correspondence between two
stores that grow independently.

### C10.4 Dynamic gradual guarantee: proof strategy

The proof strategy follows GTLC's (`GTLC/agda/proof/
DynamicGradualGuaranteeCore.agda` `sim`/`sim*`,
`DynamicGradualGuarantee.agda` `sim-back`/`sim-back*`; GTLC writes the
less precise term on the left), with catch-up lemmas for the
administrative steps that occur on one side only.  In GTNF's
orientation:

- **Forward simulation:** the more precise side takes one step, and
  then the less precise side takes zero or more steps to restore the
  relation.
- **Backward simulation:** the less precise side takes one step, and
  then both sides take zero or more steps to become related.  In
GTNF those steps are `Merge`, `Id`, `IdDyn`, `CastId`, `CastSeq`, and the
`Inst`/`TyBeta` pair.  The consistency modes (D6) are what make the
`bot-elim` and `bot-intro` cells vacuous, by `no-bot-value`.

------------------------------------------------------------------------

## C11. Agda plan

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
  `Imprecision` (type imprecision, copied from GTSFImp, §8),
  `ImprecisionExamples` (the six pairs of §C7) and `Show` (a renderer
  with named variables, `scripts/render_gtnf.sh`).  `⊑` is formalized:
  `ImprecisionWorld` (worlds, `W[δ ∥ δ′]` as the relation `Interior`,
  `CtxImp`, `WfWorld`), `TermImprecision` (the 16 rules of §10, with
  no `⊕⊑⊕`) and `TermImprecisionExamples` (P1 at the start and after
  both `TyBeta`s, P2 after the left's `TyBeta`, P3 at `∀⊑⟪+⟫`).  Next:
  progress and preservation, then `compile-⊢`.

------------------------------------------------------------------------

## C12. Decisions taken in this draft, and open questions

These decisions are complementary: together they make up the draft.
Each one can be revisited on its own.

- **D1 (separation).**  Coercions are their own sort and are applied by
  their own term form `M ⟨p⟩`; νF's conversions, `ν` and boundaries
  are unchanged.  The sorts meet only in `Inst`, `TyBeta` (via
  `inst_X`), `IdDyn` and `TagUntagBad-⟪⟫`.
- **D2 (cast values are simples).**  This lets `Wrap`, `TyBeta`,
  `Merge` and `Id` apply unchanged when the interior is a cast value.
- **D3 (tags by type variable).**  `X` is a ground type, and tags are
  compared syntactically, which coherence makes sound (§C3.7).
- **D4 (inst closes at ★).**  `Inst` instantiates by `ν X:=★` with the
  conversion `reveal_X`, and substitutes `★` for `X` in the coercion,
  as GTSFImp does.
- **D5 (one allocation per instantiation).**  `TyBeta` instantiates a
  ∀-value through all of its layers with the meta-operation `inst_X`,
  which allocates nothing (Jeremy, 2026-10-01).  An earlier draft
  re-instantiated the value under a `∀X.p` cast by an alias `ν Y:=X`,
  which cost a second allocation per `∀`-cast layer (Example 6).  Under
  D8, the alias also gave the inner tags the type variable `Y`, so a
  check `X?ℓ` in `p` would have blamed where GTSFImp's `β-∀` succeeds.
  Since D6, such a check is ill typed, because `p`'s `X` is strict.
  `inst_X` matches GTSFImp's `β-∀`, which instantiates the value itself
  with a single allocation and then casts.  νF's `TyWrap` is now the
  boundary case of `TyBeta`.
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
- **D8 (alias tags are distinct).**  A tag created under an alias type
  variable does not match the type variable it aliases, so the check
  blames (Jeremy, 2026-10-01).  GTSFImp and λB behave the same way.
  Consider

  ```
  ΛX. λx:X. (λw:X. w) (f [X] x)        where  f = ΛY. λy:Y. (λz:★. z) y
  ```

  `f [X]` allocates the alias `β:=α` under the type variable `Y`, so the
  `★` that `f` returns is tagged `Y`, and `Y ∈ fresh(+Y^β)`.  Writing
  `x₀` for the value of `x` and `ℓ` for the label of the outer
  application, the end of the run is

  ```
    (λw:X. w) (([+Y^β] (([−Y^β] x₀ ⟨−Y⟩) ⟨Y!⟩) ⟨id(★)⟩) ⟨X?ℓ⟩)
  ⟶ (TagUntagBad-⟪⟫, under ξ)
    (λw:X. w) (blame ℓ)
  ⟶ (Blame)
    blame ℓ
  ```

- **D9 (no term moves under a new type variable).**  No rule weakens a
  term by an ordinary type variable, even with named variables.  The
  `gen` case of `inst_X` puts the value under the binder's dual `[−X^α]`
  rather than in the interior that has `X` (§6.2; Jeremy, 2026-10-01).
  A weakening lemma in the preservation proof would be the sign of a
  term changing colour.

- **D10 (unseen type variables get X∼X).**  When `IdDyn` moves a tag
  cast out of a boundary, every exterior type variable that the interior
  cannot see gets the mode `X∼X` in the moved cast's environment
  (`exit_δ(μ)`, §6.3; Example 7; Jeremy, 2026-10-01).  This matches
  GTSFImp's `extᵐ` at an allocation.  The choice may be revisited when
  `⊑` is designed.

- **D11 (marks are chosen at the binder).**  In `⊑`, the mark of a type
  variable that both sides bind (`X⊑X` or `X⊑★`) is chosen by the rule
  that binds it, and it is fixed for the subterm under the binder.  No
  rule weakens a mark on the way to a premise, unlike GTSFImp's
  `ImpEnvMono` (§9, Example P4; Jeremy, 2026-10-01).  *Superseded by
  D28* (2026-10-05): no rule chooses a mark; marks are derived from the
  world's permissions.

- **D12 (type variables lexical, rep. vars global).**  In `⊑`'s worlds,
  the relation between the two sides' type variables (`Ω`, `η`, `η′`,
  `μ`) is lexically scoped.  The relation `ϱ` between their
  representation variables is global: it grows at matched allocations
  and is read when a boundary rebinds a rep. var (§9, Example P4;
  Jeremy, 2026-10-01).

- **D13 (`ϱ` is many-to-one, toward the left).**  In `⊑`'s worlds, each
  right (less precise) rep. var has at most one left partner in `ϱ`, and
  a left rep. var may have several.  So a right-only `+X^β` always has a
  unique left type variable to rejoin.  The mirror is not needed,
  because an extra left type variable can stay left-only at `X⊑★`, while
  an extra right type variable cannot stay right-only (§C8.3, F3;
  C12–C14; mirror pairs M1, M2, M4; Jeremy, 2026-10-02).

- **D14 (`∀⊑⟪+⟫`).**  The rule relating a left ∀-value to a right
  boundary `[+X^β] V′ ⟨c′⟩` created by `Inst` applies to every
  ∀-value, not only a `Λ`: its premise is `inst_X(V) ⊑ V′`, at a mark
  chosen at the binder.  It replaces `Λ⊑⟪+⟫`, and it is not
  syntax-directed, because the premise uses the meta-operation
  `inst_X`.  GTLC's forward and backward simulation shapes force it
  (§C10.4; §C8.3, F1, F2; Jeremy, 2026-10-02).

- **D15 (interior worlds).**  For `W[δ ∥ δ′]`, only the final interior
  world has to be well formed.  A type variable that goes one-sided
  inside a multi-entry `δ` and rejoins keeps its earlier mark (§9;
  §C8.3, D1; examples P4, Cf, C2, C12, C18b; Jeremy, 2026-10-02).  *The
  keep-on-rejoin part is superseded by D28* (2026-10-05): a boundary
  keeps `ϱ` and the permissions, so a rejoined type variable's mark is
  derived again; the "only the final interior world" part stands.

- **D16 (rep. vars related lexically and globally).**  `ϱ` has a
  lexical part `ϱˡ`, for the rep. vars that an enclosing `Λ` or `ν`
  binds (paired by `Λ⊑Λ`, `∀⊑⟪+⟫`, `ν⊑ν` for their premises), and a
  global part `ϱᵍ`, for store rep. vars (grown by matched `TyBeta`s).
  A matched `TyBeta` turns the lexical pair of the two `ν`s into a
  global pair (§9; §C8.3, D2; Jeremy, 2026-10-02).  Terminology:
  representation variables are "rep. vars", never "cells" (Jeremy,
  2026-10-02).

- **D17 (conversions are related structurally).**  The two
  conversions of a `ν⊑ν` pair and of a `⟪⟫⊑⟪⟫` pair are related by a
  structural conversion imprecision `c ⊑ c′`, not only through their
  types.  The relation is read in the conversion context, where the
  rep. vars bound by the `ν`s (paired in `ϱˡ`) or by the boundaries
  are in scope.  This is what `ϱˡ`'s `ν` pairs are for (D16).  Its
  clauses are in §10.6, with D18 (Jeremy, 2026-10-02).

- **D18 (the ★ clauses of conversion imprecision).**  Besides the
  structural clauses, a seal or unseal of a left type variable marked
  `X⊑★` may be absent on the right (`−X ⊑ id(★)`, `+X ⊑ id(★)`, and the
  chain forms `t ; −X ⊑ t′`, `+X ; c ⊑ c′`).  A left-only universal is
  opened at `X⊑★` (`∀X.c ⊑ g′`).  These mirror type imprecision's
  `X ⊑ ★` and `∀⊑` (§10.6; C23a, C23b; Jeremy, 2026-10-02).

- **D19 (`TyBeta` fires only on a ∀-value).**  `TyBeta` has the
  premise `Value V`.  Every case of `inst_X` requires a value: `inst-Λ`
  a value body, `inst-gen` and `inst-∀` a value under the cast, and
  `inst-⟪⟫` a *simple* interior.  `Value U` would not be enough there,
  because a boundary over a boundary value is a `Merge` redex.  Without
  these premises, `ν ℕ · ([] ([] Λ7 ⟨∀ id(ℕ)⟩) ⟨∀ id(ℕ)⟩) ⟨id(ℕ)⟩` had
  two steps, `TyBeta` and `Merge`, so `det` failed.  M1 found this
  (`proof/TypeSafety/notes/InstXDeterminismCounterexample.agda`, now a
  regression test; Jeremy, 2026-10-02).

- **D20 (evidence-shaped coercions).**  Coercions have no general
  sequencing.  The only sequences are the two that compilation
  produces, `p ; G!` and `G?ℓ ; p`, typed like GTSFImp's `_!` and `？_`:
  the tag or check is outside, permitted by the modes, and the inner
  coercion's other end is not `★`.  This is GTSFImp's normal form
  (commit c2c020fb added `B ≢ ★` to `inst` and `A ≢ ★` to `gen`, which
  keeps injections and projections outside them).  It makes closing at
  `★` preserve typing: a nested `inst`/`gen` can no longer reach the
  closed variable through `★`.  M1 found the counterexample
  (Jeremy, 2026-10-02).

- **D21 (identities at atoms).**  An identity coercion `id(A)` is
  formed only at an atom, `A ::= X | ι | ★`, as GTSFImp's `id` is
  (`Types.Atom`).  Compound identities are written structurally,
  `id(A) → id(B)` and `∀X. id(A)`.  With D20, GTNF's coercions are
  exactly the images of GTSFImp's consistency evidence, which is the
  correspondence the DGG's cast cases rely on (Jeremy, 2026-10-02).

- **D22 (`∀⊑⟪+⟫`'s body type mentions its type variable).**  `∀⊑⟪+⟫` has
  the side conditions `A not a variable` and `X ∈ A`, the same as `Λ⊑`.
  Without them `SimBack` was false.  A left value
  `(ΛX. true⟨𝔹!⟩)⟨∀Y. ℕ?ℓ⟩ : ∀X.ℕ` could be related to a right `Inst`
  boundary whose interior blames by itself, which the value can never
  match.  `Inst` never creates such a state, because its interior's type
  mentions the bound type variable (checked:
  `proof/DGG/notes/ForallBoundaryRisks.{agda,md}`; Jeremy, 2026-10-03).

- **D23 (payloads compared in the representation universe).**  The
  agreement of two paired rep. vars compares their payloads as
  representation types.  Free rep. vars inside them correspond through
  `ϱ`, and local `∀`-bound variables correspond position by position.
  The relation is `R ⊑ᴿ_W R′` (`ImprecisionWorld.RepImp`), whose rules
  are those of `⊑` (§8) over payloads.  A free left rep. var may also
  face `★`, with no condition, because rep. vars carry no marks (marks
  belong to type variables; confirmed by Jeremy, 2026-10-03).  Clarified
  (Jeremy, 2026-10-05): this is not a ban on mark-like information for
  rep. vars.  Rep. var pairs may carry such information, and the marks
  of the type variables bound to them may be derived from it
  (proof/DGG/notes/ConditionPlacement.md §7).  Strictness is still
  enforced where world pairs are created: `ν⊑ν`'s premise `A ⊑ A′`
  compares the type arguments with the type variables' marks.  Before,
  the payloads were read as ordinary types through the type variables in
  scope.  That broke once interior worlds had to be well formed: inside
  a boundary that hides a type variable, a payload mentioning that type
  variable's rep. var had no reading
  (`proof/DGG/drafts/EvolveImpWfInteriorCounterexample.agda`, now a
  regression test; `proof/DGG/notes/RepImp.md`; Jeremy, 2026-10-03).

- **D24 (unique occurrence proofs).**  `X ∈ᵗ A` has unique proofs, as
  in GTSFImp: the right-of-arrow rule has the premise
  `occurs X A ≡ false`, a Boolean occurrence check, rather than
  GTSFImp's separate `_∉ᵗ_` datatype.  Without it, `∀⊑`'s occurrence
  premise made type-imprecision derivations non-unique, and the DGG's
  `·⊑·` cases need uniqueness (`proof/Imprecision.agda`; Jeremy,
  2026-10-03).

- **D25 (`ϱ` is any agreeing relation; revises D13).**  A rep. var may
  have several partners on either side.  C12 needs a left rep. var with
  several right partners.  L3d needs the converse: the right `Inst`s its
  argument once, a `Beta` duplicates the boundary, and the left
  instantiates both copies (`proof/DGG/notes/ForallBoundaryFixes.md`;
  checked: `no-second-catchup`, `second-paired-¬wf`).  A rejoin (`+X^β`
  on one side) joins the partner whose type variable is in scope.  Its
  uniqueness comes from type variables, which coherence makes injective
  on rep. vars within a context, not from `ϱ` (Jeremy, 2026-10-03).

- **D26 (one rule for right boundaries; replaces `∀⊑⟪+⟫`; `Opens`
  superseded by D27).**  The right-only boundary rule `⊑⟪⟫` takes a
  premise `Opens` that opens the left term zero or more times.  Each
  opening opens a left ∀-value at a right-only type variable, bound to
  `★`, that the right boundary introduces.  `∀⊑⟪+⟫` is removed.  It
  hard-coded the position of the `Inst` entry, and a compiled pair
  refuted `Sim`, `SimBack` and DGG part 1 for the relation with it:
  `(λf:∀X.X→X. f)(K[ℕ])` against `(λf:★→★. f)(K[ℕ])`, with
  `K = ΛY.ΛX.λx:X.x`.  The right's `Inst` lands on a ∀-boundary value
  and its boundary merges, leaving final values that no rule related
  (`proof/DGG/notes/RestrictedForallBoundary.md`).  The generalized rule
  relates them, re-derives every earlier `∀⊑⟪+⟫` block, and does not
  change type imprecision (`GeneralizedRightBoundary.md`; alternatives
  considered: `FixA-MergedBoundary.md`, `FixB-BoundaryAbsorbs.md`;
  Jeremy, 2026-10-03).  D27 replaced `Opens` by pending type variables
  in the world.

- **D27 (pending type variables in the world; supersedes D26's
  `Opens`).**  A world of `⊑` also carries its *pending* right type
  variables `πʷ`, next pop first.  A pending type variable is
  right-only, bound to a `★` rep. var, at `X⊑★`, and introduced by a
  right boundary that the left has not matched yet.  `⊑⟪⟫` pushes such
  type variables (the left term must be a value) and carries the older
  ones through its boundary.  `Λ⊑` pops the next one: its binder joins
  that type variable (`Open1`).  `cast⊑` pops at a `gen` cast and
  passes them on at a `∀` cast, and `⟪⟫⊑` passes them into a `∀`
  boundary.  The type index opens one `∀` of the actual left type per
  pending type variable.  Every other rule requires no pending type
  variable, so top-level worlds have none.  What changed: `InstX` is
  out of the relation (D26's openings related `inst_X V`, which is not
  a value), and under a pending type variable the left term stays a
  value.  Jeremy asked whether the openings could be part of the world;
  they are: `πʷ` is a field of `ImprecisionWorld.World`, so there is
  one world type, one index `_⊑ᵂ⟨_⟩_` (which opens the pending type
  variables, and is the plain `μ ⊢ η(A) ⊑ η′(A′)` when there are none)
  and one `WfWorld` (§9).  A first encoding wrapped the world in a
  separate record with the pending type variables beside it; Jeremy
  rejected it (two world types and coercions between them grow proof
  complexity; 2026-10-05).  The counterexample K and every corpus
  block derive, K by push, pass and pop.  The alternative,
  ★-embedding the right's type variable, was refuted: it relates
  `(λx:ℕ. x) 5` to a right program that blames, a pair this relation
  leaves unrelated (`cx-unrelated`).  Checked first as
  `proof/DGG/notes/PendingOpenings.{agda,md}`; the refuted alternative
  is `StarEmbedding.md` (Jeremy, 2026-10-05).  (D28: a pending type
  variable's mark is derived, X⊑X unless its rep. var is permitted.)

- **D28 (permissions; marks are computed; R1/R2).**  A world carries the
  *permitted* right rep. vars `κ` (`κʷ`), and marks are no longer stored
  or chosen: a center type variable the right does not see is `X⊑★`; a
  center type variable the right sees is `X⊑★` iff its right rep. var is
  in `κ`, else `X⊑X` (`marksʷ W = dmarks (ηᴿʷ W) (κʷ W)`; the center is
  a number).  A right check GRANTS: `⊑cast` may add `β` to its premise
  world's `κ` when its coercion checks every outflow against the right
  type variable bound to `β` (`X?`, `X? ; p`, or `p → q` with `p` first
  order and `q` granting; `CastGrant`, `Grants`).  A boundary passes `κ`
  unchanged; top-level worlds have `κ = []`.  Two RULE premises close
  the remaining route: R1, `⟪⟫⊑` requires every left unbind entry `−X^α`
  of its boundary to have no permitted right partner (`UnbindOK`,
  `Unpermitted`); R2, the four `★` conversion clauses require the same
  of the left type variable (`LeftUnpermitted`).  Why: with marks chosen
  at the binder (D11) and kept on rejoin (D15), C1–C4g
  (`HiddenNames.md`, `ConditionPlacement.md`) relate pairs whose source
  programs are unrelated, refuting `SimBackBlame` (M22); the permissions
  world makes them unrelated (`κʷ ≡ []` invariant), but admits C5, where
  the left's own seal faces a right `5⟨ℕ!⟩` under a grant (refuting M22
  and `CastRedexNoBlame`, M26, also at the previous relation).  R1/R2
  kill C5 and its hidden variant; no condition on worlds alone can,
  because the hidden variant uses exactly P4 B3's worlds
  (`PermissionsR.md` §1.4).  The whole corpus (P1–P4, P6, K, Cg, C2,
  C12–C14, C18b, Ch) derives.  D11 and D15's keep-on-rejoin are
  superseded; `PendingOK` loses its fixed `X⊑★`.  The push type premise
  (`PushTypePremise.md`) is not adopted (redundant under permissions);
  the push ORDER defect H1 (`PushTypePremise.md` §7) is fixed by D29.
  Open obligations: CastFun needs κ-weakening with the R1/R2 side
  condition (`κ-weaken`, `R12`), and TagUntag a drop lemma
  (`PermissionsR.md` §4).  Notes: `proof/DGG/notes/Permissions.md`,
  `PermissionsR.md`, `ConditionPlacement.md`, `HiddenNames.md`,
  `SidedMarks.md`, `ModeCondition.md`, `PushTypePremise.md`; examples
  `examples/TermImprecisionPermissionExamples.agda` (Jeremy,
  2026-10-05).

- **D29 (claim-rep: a left binder claims a right rep. var to which no
  type variable is bound).**  `Λ⊑`'s binder has a third case beside a
  fresh left-only type variable and the pop of a pending type variable.
  With no pending type variable, the binder's abstract rep. var is
  paired LEXICALLY with a right rep. var `β:=★` to which no right type
  variable in scope is bound and which has no left partner bound to a
  type variable in scope (`W ⊕ᴸ⇔ β`, TermImprecision `claim-rep`).  The
  binder is left-only, so `X⊑★`, until a right boundary binds a type
  variable to `β`.  That boundary's fresh type variable REJOINS it by
  `Interior.join-fresh` (D25), and from then on its mark is `β`'s
  permission (D28): `X⊑X` unless a right check grants `β`.  There is no
  new world field and no new `WfWorld` field: the pair `(0, β)` agrees
  by `abst-★`, and uniqueness among type variables in scope ignores `β`
  while no type variable is bound to it.  Why: counterexample H1
  (`PushOrder.md`).  Its sources are related:
  `(ΛX.ΛY.λx:X.λy:Y.x : ∀X.∀Y.X→Y→X)` and
  `((ΛX.ΛY.λx:X.λy:Y.x : ∀Y.★→Y→★) : ★→★→★)`.  The right instantiates
  twice, through two casts.  Its final value nests `[+Y^β]` outside
  `[+X^α]`, with a cast between them, so there is no Merge.  D27 and D28
  relate it to the left value in no world, which refutes DGG part 1, and
  no push order fixes it (`NoD27`, `NoFixA`, `NoFixB`, `NoFixS`).  With
  claim-rep, the left's `ΛX` claims `α` at the top and `+X^α` rejoins
  it.  See `examples/TermImprecisionH1Examples.agda`: `final` (claim,
  push, carry, pop), `final-no-push` (two claims), and `dgg1-H1`.  At
  D27's stored marks, claim-rep revived C4 (`C4Revived`).  Under D28's
  derived marks C4 and C4g stay dead
  (`TermImprecisionPermissionExamples`: `C4.c4-unrelated`,
  `C4g.c4g-unrelated`, with the claim-rep cases), and so do C1, C2, C3
  and C5.  Can pushes now go?  `proof/DGG/notes/NoPush.md` answers:
  every push popped by a `Λ` can be replaced by a claim (P3 = Ch X0, Cg
  X0, C12 X0, L3c, L3d, K, H1).  A left GEN ∀-value against a right
  `Inst` boundary cannot be: C2 X0, R2c, and the DGG part 1 pair G1
  (`(λx:★.x : ∀X.X→X)` against `((λx:★.x : ∀X.X→X) : ★→★)`) are related
  only by a push and a `cc-gen` pop.  Pushes are kept (Jeremy,
  2026-10-06).
- **D28′** **(PROPOSED 2026-10-07, not adopted: permissions chosen
  at binders; R1′).**  *Superseded by the D31 proposal* (2026-10-09),
  which contains it; its marks in §9–§10 are now D31's.  Changes to
  D28: `⊑cast` no
  longer grants, so no cast rule changes the world (Jeremy, 2026-10-06:
  the world changes only at binding rules).  Instead, a boundary rule
  that JOINS a type variable (a matched fresh pair, a rejoin through
  `ϱ`, or a pushed type variable against a left binder) may add that
  type variable's right rep. var to `κ` for its premise, and pays by
  checking its interior index with the joined type variables at `X⊑X` (κ
  without the additions).  R1 becomes R1′: only a left unbind whose rep.
  var occurs in the boundary's EXTERIOR type needs an unpermitted
  partner.  R2 is unchanged.  `Grants`, `CastGrant` and `RaiseCtx` go,
  and so do the `CastFun` side condition (R12) and the `TagUntag` drop
  lemma.  Why: P4k and P4h, both from related sources, refute `Sim`
  under D28 (`proof/DGG/notes/ReductionAudit.md` §1, `P4k.not-sim`,
  `P4h.not-sim`); TwoGen's G0 is the same failure as P4k.  Argued in
  ReductionAudit §4; to check: the corpus, C1–C5 and C4g dead, the
  TwoGen pairs, the `Merge` case of the binder check, and R1′'s safety.
- **D30** **(PROPOSED 2026-10-08, not adopted: openings in the
  index, not the world).**  *Superseded by the D31 proposal*
  (2026-10-09), which contains it with two of its adjustments
  (`cast⊑` by binder layers, not `drop k O`; skip slots); its §10.8
  is now inline D31 marks.  The pending type variables of D27
  only ever changed how the type index is read, and the binders that
  consume them (`gen`, a `∀` coercion) have no term in their scope, so
  they belong to the index.  The list `π` leaves the world (`πʷ`, the
  `PendingOK` part of well-formedness, the `πʷ W ≡ []` hypotheses) and
  becomes part of the index: `A ⊑_W^O A′`, the left type with its outer
  ∀s opened at the right type variables `O`.  `cast⊑` becomes one rule
  whose premise openings follow from its conclusion openings and the
  cast's types (no special forms, no condition on the world).  The world
  changes only at term binders: `Λ⊑` consumes an opening by joining its
  binder (D27's pop), and `⊑⟪⟫` may open its premise index at the type
  variables its `δ′` binds (D27's push).  (Jeremy, 2026-10-07/08: the
  world changes only at binders, and a `gen` binder's scope contains
  no term.)
- 🆕 **D31** **(PROPOSED 2026-10-09, not adopted: D28′ + D30
  combined, with three adjustments).**  The world has no `π` and no
  grants; `κ` changes only at boundary rules.  The index is
  `A ⊑_W^O A′`, `O` a list of slots: a slot opens the next left outer
  `∀` at a right type variable, or skips it (left-only, `X⊑★`).  15
  rules, `_⊢_⊑_` unchanged: `⊑cast` is GTSFImp's plain rule; one
  `cast⊑` whose premise slots follow the coercion's binder layers
  (`CastOpen`: a `∀` layer passes its slot, a gen layer uses it up);
  `Λ⊑` with `Bind` (fresh, join, claim-rep); each boundary rule may add
  `K` to `κ` for its interior, `K` limited to rep. vars of type
  variables it joins (`JoinRep`), and pays with its interior index
  read without `K`; `⊑⟪⟫` is the only rule that creates slots
  (`PushD`, `Fill`); `⟪⟫⊑` with R1′ (`UnbindOK′`); R2 unchanged.  The
  adjustments to D28′ and D30: (1) `cast⊑`'s slots follow the
  coercion's layers, not `drop k O` (HRm's `∀Y. gen Z.`); (2) the
  permission of an opening is chosen at `⊑⟪⟫`, where the opening is
  created, not at `Λ⊑` (a gen value uses its opening up at a cast, so
  TwoGen's (i) is not needed); (3) skip slots, created only for a left
  gen-cast value and fillable by a later `⊑⟪⟫` (TwoGen's (iii); G2,
  HR, N2.TwoCast).  Why: P4k, P4h (`¬ Sim` under D28), TwoGen's seven
  pairs (`¬ DGG`), with C1–C5 and C4g kept dead.  Checked: the corpus
  (P5 and R2c for the first time) derives; P4k, P4h and TwoGen's pairs
  are related, with DGG part 1 witnesses; C1–C5, C4g and the hunt's
  gen-valued C4 are dead.  Open: `Wrap` needs κ-weakening; a `Merge`
  can lose a rejoin's permission (possible fix: `JoinRep` accepts a
  rebound type variable); G2's states 2 and 4 not ported.  Pointers:
  `proof/DGG/notes/D28pD30.{md,agda}`, `ReductionAudit.md` §4,
  `TwoGen.md` §3; §C9.2 (Jeremy, 2026-10-09).

The open design questions are those of the `⊑` sketch (§C8.2).

Out of scope for now: space efficiency.  Normal forms for coercions,
and a composition `p ⨟ q` like νF's for conversions, are not a concern
for the time being (Jeremy, 2026-10-01).

------------------------------------------------------------------------

## Section map (old → new)

Section numbers of earlier versions of this file (up to 2026-10-08),
as cited by the Agda comments and the notes, and where that material
is now.  D-numbers are unchanged.

| old | content | new |
|---|---|---|
| §1 | types, rep. types, contexts | §1 (rationale of tags by type variable: §C3.7) |
| §2 | conversions | §2 |
| §3 | coercions: grammar, typing, closing at ★ | §3; names and provenance §C1.1; why modes §C1.2; modes at a cast §C1.3; closing lemma rationale §C1.4 |
| §4 | terms and typing | §4 |
| §5 | values | §5; rationale and proof sketches §C2 |
| §6 | reduction | §6 (6.1–6.3); rationale §C3 |
| §6.1 | frames | §6.1 |
| §6.2 | the νF rules, `inst_X` | §6.2; no term moves under a new type variable §C3.1; `inst_X` §C3.2; νF and GTSFImp instances §C3.3; preservation sketch §C3.4 |
| §6.3 | cast rules | §6.3; correspondence §C3.5; `Inst` §C3.6 |
| §6.4 | why a tag by type variable keeps its meaning | §C3.7 |
| §7 | compilation | §7; the typing theorem §C4 |
| §8 | Examples 1–7 | §C5 |
| §9 | metatheory goals | §11 (statements) and §C10 (discussion) |
| §9.1 | type safety | §11.1 |
| §9.2 | compilation | §11.2 |
| §9.3 | the source type system | §11.3 |
| §9.4 | type imprecision | §11.4; §C10.1 |
| §9.5 | static gradual guarantee | §11.5; §C10.2 |
| §9.6 | compilation preserves imprecision | §11.6; §C10.3 |
| §9.7 | dynamic gradual guarantee | §11.7 (statement); §C10.4 (simulations) |
| §10 | decisions D1–D31, open questions | §C12 |
| §11 | Agda plan | §C11 |
| §12 | cast-term imprecision | §8–§10 (definitions); §C6–§C9 (commentary) |
| §12 status | status, review markers, C1–C5 pointer | §8 (status); top of file (markers); §C8 (C1–C5) |
| §12.1 | type imprecision | §8 |
| §12.2 | worlds | §9; P3 example and "never rebased" §C6.1 |
| §12.2.1 | sketch: allocation hands the ν invariants to the world | §C9.1 |
| §12.3 | rules | §10 (10.1–10.7); grants §C6.2; claim-rep and H1 §C6.3; push §C6.4; R1 and C5 §C6.5; K ladder §C6.6; P4 B3 ladder §C6.7; ★ conversion clauses §C6.8; D28′ rationale §C9.2 (now D31) |
| §12.3.1 | TwoGen | §C8.1 |
| §12.3.2 | D30 proposal | 🆕 D31 marks in §9, §10.2–§10.7 (changed rules); §C9.2 (rationale) |
| §10.8, §C9.3 (2026-10-08) | D30 proposal | 🆕 D31 marks in §9, §10.2–§10.7; §C9.2 |
| §C9.2 (2026-10-08) | D28′ rationale | §C9.2 (D31) |
| §12.4 | Examples P1–P6 | §C7 |
| §12.5 | what the examples say | §C8.2 |
| §12.6 | the cambridge26 pairs | §C8.3 |
