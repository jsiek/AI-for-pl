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
rules (`Inst`, and `TyBeta`/`TyWrap` through `open`) and the two rules
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
9. Decisions taken in this draft, and open questions
10. Agda plan

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
Inert coercions  P ::= G! | p → q | ∀X. p | gen X. p
Gen-safe         GenSafe(p)  iff  p is  q → r,  ∀X. q,  inst X. q,  or  gen X. q with GenSafe(q)
```

The constructor names follow GTSF's `Coercions.agda` (`id`, `_!`, `_？`,
`_↦_`, `` `∀ ``, `inst`, `gen`, `_︔_`) and GTSFImp's consistency
constructors (`id`, `_!`, `？_`, `_↦_`, `∀ᶜ_`, `inst_`, `gen_`).
`GenSafe` is GTSFImp's `CastTerms.GenSafe`: the coercion suspended under
a `gen` must not hide a check that ought to run before the polymorphic
value exists.  Compilation always produces gen-safe coercions under
`gen`, by GTSFImp's `gen-safe` lemma (`proof/Consistency.agda`).

`src(p)` and `trg(p)` are computed syntactically (`src(id A) = A`,
`src(G!) = G`, `src(G?ℓ) = ★`, `src(p → q) = trg(p) → src(q)`,
`src(∀X.p) = ∀X.src(p)`, `src(inst X.p) = ∀X.src(p)`,
`src(gen X.p) = src(p)`, `src(p ; q) = src(p)`, and dually for `trg`).

### Typing `Δ ⊢ p : A ⇒ B`

```
  Δ ⊢ A                    Δ ⊢ G                  Δ ⊢ G
  ───────────────────      ──────────────         ───────────────
  Δ ⊢ id(A) : A ⇒ A        Δ ⊢ G! : G ⇒ ★         Δ ⊢ G?ℓ : ★ ⇒ G

  Δ ⊢ p : A′ ⇒ A    Δ ⊢ q : B ⇒ B′          Δ, α, X:=α ⊢ p : A ⇒ B
  ────────────────────────────────          ───────────────────────────── (X, α ∉ Δ)
  Δ ⊢ p → q : A → B ⇒ A′ → B′               Δ ⊢ ∀X. p : ∀X. A ⇒ ∀X. B

  Δ, α, X:=α ⊢ p : A ⇒ B    Δ ⊢ B          Δ, α, X:=α ⊢ p : A ⇒ B    Δ ⊢ A    GenSafe(p)
  ─────────────────────────────── (X,α∉Δ)  ──────────────────────────────────────────── (X,α∉Δ)
  Δ ⊢ inst X. p : ∀X. A ⇒ B                Δ ⊢ gen X. p : A ⇒ ∀X. B

  Δ ⊢ p : A ⇒ B    Δ ⊢ q : B ⇒ C
  ──────────────────────────────
  Δ ⊢ p ; q : A ⇒ C
```

Coercion typing carries **no consistency modes**.  GTSFImp's
`Env∼` marks (`X∼X`, `X∼★`, `★∼X`, `★∼X∼★`) restrict which coercions the
*source* may ask for, and they stay in the source language's
consistency relation.  The cast calculus types any coercion whose
endpoints line up, just as νF's `⊢ν` accepts any conversion whose types
line up and not only the `reveal` that the compiler writes.  One
consequence is that GTSFImp's `bot-elim`/`bot-intro` need no special
constructors; they compile to `∀X. X!` and `∀X. X?ℓ` (§7).  A coercion's
typing does not depend on whether a representation variable is abstract
(`α`) or bound (`α:=R`).  Instantiation rules use this fact when they
move a coercion typed under a `Λ`'s `α` to a context where `α:=R` has
been allocated.

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
```

If `Δ, α, X:=α ⊢ p : A ⇒ B`, then `Δ ⊢ p[★/X] : A[★/X] ⇒ B[★/X]`.

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
  Δ ∣ Γ ⊢ M : A    Δ ⊢ p : A ⇒ B                Δ ⊢ A
  ──────────────────────────────── (new)        ───────────────────── (new)
  Δ ∣ Γ ⊢ M ⟨p⟩ : B                            Δ ∣ Γ ⊢ blame ℓ : A
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
interior: `Wrap` crosses `[δ] U ⟨c → d⟩`, `TyWrap` crosses
`[δ] U ⟨∀X. c⟩`, `Merge` fuses `[δ₂]([δ₁] U ⟨t₁⟩)⟨c⟩`, and `Id` drops
`[δ] U ⟨id(ι)⟩`.  With this change those rules also apply when the
interior is a cast value.  The rules never look inside `U`, so the
change costs nothing in them.  The boundary invariant of νF, "at most
one boundary directly around a simple", is unaffected.  A cast value may
contain boundaries *inside* its `V`, just as `λx:A. N` may contain them
inside `N`.

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
`TyBeta` and `TyWrap` are generalized from a `Λ` interior to any
∀-simple, through a meta-operation `open_X(U)` that peels one layer:

```
open_X(ΛX. V)          = V
open_X(W ⟨gen X. p⟩)  = W ⟨p⟩
open_X(W ⟨∀X. p⟩)     = (ν Y:=X. (W Y) ⟨reveal_Y(src(p)[Y/X])⟩) ⟨p⟩      (Y fresh)
```

The third clause instantiates `W` at the *already allocated* name `X`
by an alias `ν` (it allocates `β:=α` where `X:=α`).  This is the
"alias allocation per layer" choice that νF made for nested type
applications (strong-rep-nu NuSketch, answer (3a)).  GTNF has no
non-allocating type application.

```
Δ ⊢ op(k⃗) ⟶ ⟦op⟧(k⃗) ⊣ ε                                              (Delta)

Δ ⊢ (λx:A. N) V ⟶ N[x:=V] ⊣ ε                                          (Beta)

Δ ⊢ ([δ] U ⟨c → d⟩) W ⟶ [δ] (U ([−δ] W ⟨c⟩)) ⟨d⟩ ⊣ ε                    (Wrap)

Δ ⊢ ν X:=A. (U X) ⟨d⟩ ⟶ [+X^α] open_X(U) ⟨d⟩ ⊣ α:=Δ(A)                  (TyBeta)
      U a ∀-simple; α fresh

Δ ⊢ ν X:=A. (([δ] U ⟨∀X. c⟩) X) ⟨d⟩
      ⟶ [+X^α] ([δ] open_X(U) ⟨c⟩) ⟨d⟩ ⊣ α:=Δ(A)                        (TyWrap)

Δ ⊢ [δ₂] ([δ₁] U ⟨t₁⟩) ⟨c₁⟩ ⟶ [δ₂ ++ δ₁] U ⟨d⟩ ⊣ ε                      (Merge)
      where [δ₁] U ⟨t₁⟩ is a value and (δ₂ ++ δ₁)⁺(Δ) ⊢ t₁ ⨟ c₁ = d

Δ ⊢ [δ] U ⟨id(ι)⟩ ⟶ U ⊣ ε                                              (Id)

Δ ⊢ F[M] ⟶ F[M′] ⊣ ξ     if  F(Δ) ⊢ M ⟶ M′ ⊣ ξ                        (ξ)
```

As in νF, if the redex's `U` is `ΛX.V`, then `TyBeta` and `TyWrap` are
the paper's rules.  The `gen` instances are GTSFImp's `β-gen` with a
boundary in place of `↑ 〖 0 , ⇑ᵗ C ↑ B 〗`.  When the Agda is written,
the three instances of `open_X` may become three named constructors
each; this draft states them once.

Preservation of the `∀X.p` instance of `TyBeta`, informally: let
`Δ ∣ [] ⊢ W : ∀X. C`, `Δ, α, X:=α ⊢ p : C ⇒ C′` and
`Δ, α:=Δ(A), X:=α ⊢ d : C′ ⇒ B`.  The interior is `Δ′ = Δ, X:=α`, where
`Δ` now contains `α:=Δ(A)`.  The alias `ν Y:=X` is well typed at `C`,
because `Y:=X ∈ (Δ′, β:=α, Y:=β)` and so
`reveal_Y(C[Y/X]) : C[Y/X] ⇒ C`.  The cast `⟨p⟩` brings the type to
`C′`, and `d` is typed in `(+X^α)⁺(Δ) = Δ, X:=α`.

### 6.3 Cast rules (new)

```
Δ ⊢ V ⟨id(A)⟩ ⟶ V ⊣ ε                                                 (CastId)

Δ ⊢ V ⟨p ; q⟩ ⟶ V ⟨p⟩ ⟨q⟩ ⊣ ε                                       (CastSeq)

Δ ⊢ (V ⟨p → q⟩) W ⟶ (V (W ⟨p⟩)) ⟨q⟩ ⊣ ε                             (CastFun)

Δ ⊢ V ⟨inst X. p⟩ ⟶ (ν X:=★. (V X) ⟨reveal_X(src(p))⟩) ⟨p[★/X]⟩ ⊣ ε   (Inst)

Δ ⊢ V ⟨G!⟩ ⟨G?ℓ⟩ ⟶ V ⊣ ε                                              (TagUntag)

Δ ⊢ V ⟨G!⟩ ⟨H?ℓ⟩ ⟶ blame ℓ ⊣ ε        if G ≠ H                         (TagUntagBad)

Δ ⊢ [δ] (V ⟨G!⟩) ⟨id(★)⟩ ⟶ ([δ] V ⟨Id(G)⟩) ⟨G!⟩ ⊣ ε                     (IdDyn)
      if G ∉ fresh(δ)            (equivalently, on well-typed terms, Δ ⊢ G)

Δ ⊢ ([δ] (V ⟨X!⟩) ⟨id(★)⟩) ⟨H?ℓ⟩ ⟶ blame ℓ ⊣ ε     if X ∈ fresh(δ)     (TagUntagBad-⟪⟫)

Δ ⊢ F[blame ℓ] ⟶ blame ℓ ⊣ ε                                            (Blame)
```

These rules correspond to GTSFImp's `β-id`, `β-⇒`, `β-inst`,
`tag-untag` and `tag-untag-bad`.  GTSFImp's `ground` and `expand` are
not needed, because a tag through a non-ground type is the sequence
`p ; G!` and `CastSeq` splits it.  GTSFImp's `β-∀` is replaced by the
`∀X.p` instance of `open_X`, because GTNF instantiates by `ν` and not by
a `⦂∀ B [ C ]` type application.

`Inst` does not allocate by itself.  The `ν X:=★` it creates allocates
`α:=★` on the next step, by `TyBeta` or `TyWrap`.  Inside the resulting
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
⟦bot-elim⟧ℓ    = ∀X. X!
⟦bot-intro⟧ℓ   = ∀X. X?ℓ
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
the facts that `⟦c⟧ℓ` is typed at the endpoints of `c`, which holds
because coercion typing has no modes, and that `⟦·⟧` maps source values
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
⟶ (TyBeta with open_X(… ⟨gen X. p⟩), ⊣ α:=ℕ)
  ([+X^α] ((λx:★. x) ⟨X! → X?ℓ⟩) ⟨−X → +X⟩) 5
⟶ (Wrap)
  [+X^α] (((λx:★. x) ⟨X! → X?ℓ⟩) ([−X^α] 5 ⟨−X⟩)) ⟨+X⟩
⟶ (CastFun)
  [+X^α] (((λx:★. x) (([−X^α] 5 ⟨−X⟩) ⟨X!⟩)) ⟨X?ℓ⟩) ⟨+X⟩
⟶ (Beta)
  [+X^α] (([−X^α] 5 ⟨−X⟩) ⟨X!⟩ ⟨X?ℓ⟩) ⟨+X⟩
⟶ (TagUntag)
  [+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩
⟶ (Merge; −X ⨟ +X = Id(ℕ))
  [+X^α, −X^α] 5 ⟨id(ℕ)⟩
⟶ (Id)
  5
```

### Example 3 — implicit generalization, used non-parametrically

Replace the argument by `λx:★. (λy:ℕ. x) x`, which inspects its
argument at `ℕ`.  The coercion is again `gen X. (X! → X?ℓ)`; the inner
application has label `ℓ′`.  After the same first five steps, the body
reaches `(λy:ℕ. x′) (x′ ⟨ℕ?ℓ′⟩)`, where `x′ = ([−X^α] 5 ⟨−X⟩) ⟨X!⟩`,
still under the result cast `⟨X?ℓ⟩`.  The check fails because `X ≠ ℕ`:

```
  [+X^α] (((λy:ℕ. x′) (([−X^α] 5 ⟨−X⟩) ⟨X!⟩ ⟨ℕ?ℓ′⟩)) ⟨X?ℓ⟩) ⟨+X⟩
⟶ (TagUntagBad, under ξ)
  [+X^α] (((λy:ℕ. x′) (blame ℓ′)) ⟨X?ℓ⟩) ⟨+X⟩
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
⟶ (Beta, under ξ)
  [+X^α] ((λw:X. w) (([−X^α, +X^α] W ⟨id(X)⟩) ⟨X!⟩ ⟨X?ℓ⟩)) ⟨+X⟩
⟶ (TagUntag, under ξ)
  [+X^α] ((λw:X. w) ([−X^α, +X^α] W ⟨id(X)⟩)) ⟨+X⟩
```

The remaining steps are `Merge` (which fuses `[−X^α, +X^α]` with `W`'s
boundary), `Beta`, `Merge` with the outer `[+X^α]`, and `Id`.  The
result is `5`.  The `IdDyn` step happens at the interior `Δ, X:=α` of
the outer boundary, where `X` is visible again.  The rule's two forms of
side condition agree there: `X ∉ fresh(−X^α, +X^α)`, and
`Δ, X:=α ⊢ X`.

------------------------------------------------------------------------

## 9. Decisions taken in this draft, and open questions

These decisions are complementary: together they make up the draft.
Each one can be revisited on its own.

- **D1 (separation).**  Coercions are their own sort and are applied by
  their own term form `M ⟨p⟩`; νF's conversions, `ν` and boundaries
  are unchanged.  The sorts meet only in `Inst`, `TyBeta`/`TyWrap` (via
  `open_X`), `IdDyn` and `TagUntagBad-⟪⟫`.
- **D2 (cast values are simples).**  This lets `Wrap`, `TyWrap`,
  `Merge` and `Id` apply unchanged when the interior is a cast value.
- **D3 (tags by name).**  `X` is a ground type, and tags are compared
  syntactically, which coherence makes sound (§6.4).
- **D4 (inst closes at ★).**  `Inst` instantiates by `ν X:=★` with the
  conversion `reveal_X`, and substitutes `★` for `X` in the coercion,
  as GTSFImp does.
- **D5 (∀-casts by alias ν).**  `open_X(W⟨∀X.p⟩)` re-instantiates `W`
  at the existing name by an alias `ν`.  This costs a second allocation
  per `∀`-cast layer, consistently with νF's answer (3a).
- **D6 (no modes in the cast calculus).**  Consistency modes remain a
  source-language device.
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

Open questions, in roughly the order I would like them settled:

- **Q1.**  D5 versus a non-allocating instantiation at an existing name.
- **Q2.**  `bot-intro` blames eagerly in GTSFImp (`blame-bot-intro`),
  but `⟦bot-intro⟧ = ∀X. X?ℓ` blames only at instantiation.
- **Q3.**  Space efficiency (normal forms for coercions and a
  composition `p ⨟ q`, like νF's for conversions) is deferred.

------------------------------------------------------------------------

## 10. Agda plan

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
- Order: the definitional layer and `Examples` (Examples 1–5 as `refl`
  runs), then progress and preservation, then `compile-⊢`.
