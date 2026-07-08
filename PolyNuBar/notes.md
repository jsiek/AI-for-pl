# PolyNuBar Notes

These notes describe the full-barrier PolyNuBar calculus as mechanized in
Agda, with references to the Scheme constructors in `interp-nu/`.  The
presentation uses named variables and mathematical notation; the Agda
implementation uses de Bruijn indices for both ordinary type variables and
seal/store names.

The Scheme test harness also contains a no-barrier experiment, but the Agda
development intentionally models only the full barrier calculus.


## Syntax

    Types                 A,B,C ::= X | ι | ★ | A → B | A × B | ∀X.A[X]
    Base types            ι     ::= 𝕀 | 𝔹
    Ground types          G,H   ::= ι | ★ → ★ | ★ × ★ | X

    Terms                 L,M,N ::= x | c | λx:A.M[x] | L M
                                  | let x = L in M[x]
                                  | Λ^p X.M[X] :: A
                                  | M • A
                                  | ν^p α:=A. M
                                  | M : A ⇒^p B
                                  | M : A ⇒^α B
                                  | M : A ⇒^ᾱ B
                                  | M is^p G
                                  | ⟨M,N⟩ | fst M | snd M
                                  | if L then M else N
                                  | prim op M
                                  | blame p

    Constants             c     ::= n | true | false
    Labels                p,q   ::= ℓ | - | p̄
    Barrier binders       P,Q   ::= α | ᾱ

    Type variables        X,Y
    Seal names            α,β
    Term variables        x,y

The dynamic type `★` is the Scheme type `dyn`; `𝕀` and `𝔹` correspond to the
Scheme base types `int` and `bool`.  The pair type `A × B` is represented in
Scheme by `(X A B)`.

The two cast-like term forms have different labels: `M : A ⇒^p B` is an
ordinary cast with blame label `p`, while `M : A ⇒^P B` is a barrier whose label
is a barrier binder `P`.  The binder `ᾱ` is the negation of `α`; similarly
`p̄` is the negation of `p`, and both negations are involutive.

A `ν` binder introduces a seal/store name `α:=A`, not an ordinary type
variable.  Ordinary type variables introduced by a `ν` allocation may be used
only through barriers.  The positive barrier `M : A ⇒^α B` pushes the type
variable associated with seal `α` into scope while checking `M` and `A`.  The
negative barrier `M : A ⇒^ᾱ B` is the matching pop: the type variable is in
scope for the whole barrier and result `B`, but not in scope for `M` or `A`.
The pop is targeted by `α`; it may remove the associated type variable from
below younger ordinary type variables introduced later.  Those younger
variables stay in scope, and stored annotations above the removed variable are
closed by substituting the representation type for that variable.


## Scheme Correspondence

These are the implementation constructors for the non-obvious pretty forms:

    A → B                 (-> A B)
    A × B                 (X A B)
    ∀X.A                  (forall (X) A)
    λx:A.M                (lambda (x : A) M)
    Λ^p X.M :: A          (Lambda (X) p M A)
    M • A                 Agda: M • A
                          Scheme: (inst M A)
    ν^p α:=A. M           (nu X A p M)
    M : A ⇒^p B           (cast M (A => p B))
    M : A ⇒^P B           (barrier M A P B)
    α, ᾱ                 Agda: bind X, unbind X
                          Scheme: (bind X), (bar-bind X)
    p̄                    (bar p)
    M is^p G              (is p M G)
    ⟨M,N⟩                 (pair M N)
    fst M                 (fst M)
    snd M                 (snd M)


## Contexts and Well-Formed Types

The Agda formalization uses one telescope for ordinary type variables,
barrier-pushed type variables, seal/store names, and term variables:

    Contexts              Γ ::= ∅ | Γ, X | Γ, X^α | Γ, α:=A | Γ, x:A

The well-formed type judgment is written `Γ ⊢wf A`.  A `ν` binder adds only the
seal entry `α:=A`; it does not add an ordinary type variable.  The variable
associated with `α` can be used only where a barrier has pushed a marked
ordinary type variable `X^α` onto the telescope.

    X ∈ty Γ
    -------
    Γ ⊢wf X

    --------
    Γ ⊢wf ι

    --------
    Γ ⊢wf ★

    Γ ⊢wf A    Γ ⊢wf B
    --------------------
    Γ ⊢wf A → B

    Γ ⊢wf A    Γ ⊢wf B
    --------------------
    Γ ⊢wf A × B

    Γ, X ⊢wf A[X]
    --------------
    Γ ⊢wf ∀X.A[X]

Type-variable lookup treats both `X` and `X^α` as ordinary de Bruijn type
variables, and crosses seal and term entries unchanged.  Term-variable and seal
lookups cross either kind of type-variable entry by weakening the stored type.
Thus if `α:=A` or `x:A` is found below a pushed type variable, it is observed
above that binder as `α:=A↑` or `x:A↑`.

For deep pops, write `close_k(C,A)` for the type obtained by deleting the type
variable at de Bruijn depth `k` and substituting `C` there.  Variables younger
than depth `k` are preserved, the deleted variable is replaced by `C` weakened
under those younger binders, and older variables shift down by one.

    close_0(C, X0)       = C
    close_0(C, X(n+1))   = Xn
    close_{k+1}(C, X0)   = X0
    close_{k+1}(C, X(n+1)) = close_k(C, Xn)↑

    close_k(C, ι)        = ι
    close_k(C, ★)        = ★
    close_k(C, A → B)    = close_k(C,A) → close_k(C,B)
    close_k(C, A × B)    = close_k(C,A) × close_k(C,B)
    close_k(C, ∀X.A)     = ∀X.close_{k+1}(C,A)


## Ground Types and Consistency

The predicate `ground?` recognizes the runtime tags used for casts to and from
`★`:

    Ground types          G,H ::= ι | ★ → ★ | ★ × ★ | X

The helper `ground(A)` used by the `Ground` reduction rule computes:

    ground(ι)      = ι
    ground(A → B)  = ★ → ★
    ground(A × B)  = ★ × ★
    ground(X)      = X

Type equality is structural, with alpha-equivalence for universal types.

Type consistency is written `A ∼ B`.

    ---------
    ι ∼ ι

    ---------
    ★ ∼ A

    ---------
    A ∼ ★

    X = Y
    -----
    X ∼ Y

    A ∼ A′    B ∼ B′
    ----------------
    A → B ∼ A′ → B′

    A ∼ A′    B ∼ B′
    ----------------
    A × B ∼ A′ × B′

    A[★/X] ∼ B
    ------------
    ∀X.A[X] ∼ B

    A ∼ B[Y/X]    Y fresh
    ---------------------
    A ∼ ∀X.B[X]

The implementation also contains legacy consistency clauses for concrete forms
like `(dyn X)`.  Those forms are not generated by the well-formed type grammar
above.


## Substitution and Seal Variables

Term substitution is capture-avoiding for both term variables and seal
variables.  In particular, when a substitution crosses `ν^p α:=A. M`, every
free seal index in the substitution range is weakened.  Thus substituting a
term that mentions an outer seal `β` under a fresh `ν α` preserves that
reference as `β`, rather than capturing it as `α`.

    (ν^p α:=A. M)[V/x]
      =
    ν^p α:=A. M[V↑seal/x]

This is separate from type-variable weakening under `Λ`.

Substitution also tracks the raw type-variable depth associated with barriers.
When substitution enters the protected term of `M : A ⇒^α B`, substitution
ranges are pushed in a seal-aware way: occurrences of the type variable already
associated with `α` are redirected to the newly pushed top variable.  When
substitution enters the protected term of `M : A ⇒^ᾱ B`, it pops the
corresponding type-variable scope from every substitution range.

The Agda operation is total on raw terms: deleting a type variable that is
actually mentioned maps that variable to itself, so ill-scoped raw inputs still
produce a term.  Well-typed reductions use only the cases where the pop is
meaningful.


## Typing Rules

The Agda typing judgment is written `Γ ⊢ M : A`.  The context `Γ` is the
telescope above; extending it with `X` automatically weakens term-variable and
seal lookup results that live below that type binder.

    x:A ∈ Γ
    -------
    Γ ⊢ x : A

    type-of-const(c) = A
    --------------------
    Γ ⊢ c : A

Constants are integers and booleans.  Their types are `𝕀` and `𝔹`.

    Γ ⊢wf A    Γ,x:A ⊢ M : B
    -------------------------
    Γ ⊢ λx:A.M : A → B

    Γ ⊢ L : A    Γ,x:A ⊢ M : B
    --------------------------------
    Γ ⊢ let x = L in M : B

    Γ,X ⊢wf B    Γ,X ⊢ M : B
    ------------------------
    Γ ⊢ Λ^p X.M :: B : ∀X.B

The reducer treats a type abstraction as a value only when its body is a value.

    Γ ⊢ M : ∀X.A[X]    Γ ⊢wf B
    ---------------------------
    Γ ⊢ M • B : A[B/X]

    Γ ⊢wf A    Γ ⊢wf B    Γ,α:=A ⊢ M : B
    -------------------------------------
    Γ ⊢ ν^p α:=A. M : B

The `ν` rule extends only the seal portion of the telescope.  It does not add a
type-variable entry, so neither `α` nor the representation type `A` can be
mentioned as an ordinary type variable in annotations or casts outside a
barrier.  The result type `B` must be well formed in the outside context `Γ`;
this is the Agda version of the `(New)` side condition that the abstract
variable introduced for the seal must not escape in the type of the body.

Positive barriers push the ordinary type variable associated with seal `α`.
In the simple top-binder case, after checking the protected term, the
representation type `C` stored at `α` is substituted for that top variable.

    lookup(Γ,α) = C
    Γ,X^α ⊢wf A    Γ ⊢wf B
    Γ,X^α ⊢ M : A
    B = A[C/X]
    ----------------------------
    Γ ⊢ (M : A ⇒^α B) : B

Negative barriers are the matching pop.  In the simple top-binder case, the
whole barrier lives under the pushed type variable, but the protected term `M`
and source type `A` are checked after that variable has been removed.

    lookup(Γ,α) = C
    Γ ⊢wf A    Γ,X^α ⊢wf B
    Γ ⊢ M : A
    A = B[C/X]
    -------------------------------
    Γ,X^α ⊢ (M : A ⇒^ᾱ B) : B

The Agda typing relation also includes the corresponding deep-pop telescope
form.  Write `Pop_α(Γᵒ, Γᶜ, C, k)` when `Γᶜ` is obtained from `Γᵒ` by removing
the marked type variable `X^α` at depth `k`, closing each stored type above that
point with `close_k(C,-)`.  The case `k = 0` is the top pop shown above; larger
`k` values preserve younger type binders above the removed variable.

    Pop_α(Γᵒ, Γᶜ, C, k)
    Γᵒ ⊢wf A    Γᶜ ⊢wf B
    Γᵒ ⊢ M : A
    B = close_k(C,A)
    --------------------------------
    Γᶜ ⊢ (M : A ⇒^α B) : B

    Pop_α(Γᵒ, Γᶜ, C, k)
    Γᶜ ⊢wf A    Γᵒ ⊢wf B
    Γᶜ ⊢ M : A
    A = close_k(C,B)
    ----------------------------------
    Γᵒ ⊢ (M : A ⇒^ᾱ B) : B

    Γ ⊢ M : A′    A = A′    Γ ⊢wf A    Γ ⊢wf B    A ∼ B
    ------------------------------------------------------------
    Γ ⊢ (M : A ⇒^p B) : B

    Γ ⊢ M : ★    G ground
    ----------------------
    Γ ⊢ M is^p G : 𝔹

    Γ ⊢ L : A    Γ ⊢ M : B
    ------------------------
    Γ ⊢ ⟨L,M⟩ : A × B

    Γ ⊢ M : A × B
    -------------
    Γ ⊢ fst M : A

    Γ ⊢ M : A × B
    -------------
    Γ ⊢ snd M : B

    Γ ⊢ L : 𝔹    Γ ⊢ M : A    Γ ⊢ N : A
    ------------------------------------------
    Γ ⊢ if L then M else N : A

    type-of-proc(op) = A → B    Γ ⊢ M : A
    --------------------------------------
    Γ ⊢ prim op M : B

    Γ ⊢ L : A → B    Γ ⊢ M : A
    ----------------------------
    Γ ⊢ L M : B

The implemented primitive operators are:

    add1       : 𝕀 → 𝕀
    f          : 𝔹 → 𝕀
    not        : 𝔹 → 𝔹
    one-minus  : 𝕀 → 𝕀
    positive?  : 𝕀 → 𝔹

The runtime term `blame p` is produced by reduction and treated as a terminal
result by the evaluator.  The Agda typing relation assigns it any well-formed
type, which is the usual preservation-friendly runtime convention.


## Values and Evaluation Contexts

The implemented values are:

    Values V,W ::= c
                 | λx:A.M
                 | Λ^p X.V :: A
                 | V : G ⇒^- ★
                 | V : A ⇒^ᾱ Xα
                 | ⟨V,W⟩

The barrier value form records a negative barrier whose target is the abstract
type variable associated with that barrier.  In the top de Bruijn presentation
of the value form, that target is index `0`; negative barriers over older
variables continue to reduce rather than becoming values.

Reduction is call-by-value and is closed under the following strict evaluation
contexts:

    C ::= []
        | C : A ⇒^p B
        | if C then M else N
        | ⟨C,M⟩ | ⟨V,C⟩
        | fst C | snd C
        | let x = C in M
        | Λ^p X.C :: A
        | C • A
        | ν^p α:=A. C
        | C : A ⇒^P B
        | C is^p G
        | prim op C
        | C M | V C


## Reduction Rules

One-step reduction is written `M —→ N`.  The rules below correspond to the
Agda `Reduction` and `Eval` modules and to the active full-barrier rules in
the Scheme reducer.

The Scheme source contains several experimental alternatives guarded by literal
`#f` such as alternate wrapper, pair-barrier, type-barrier, and `NuBarDrop`
clauses.  Those clauses cannot fire and are not included as active rules below.

### System F and Functions

    (Λ^p X.V :: B) • A
      —→
    ν^p α:=A. (V : B ⇒^α B[A/X])

    (λx:A.M) V
      —→
    M[V/x]

    let x = V in M
      —→
    M[V/x]


### Casts

    V : A ⇒^p ∀X.B[X]
      —→
    Λ^p Y. (V : A ⇒^p B[Y/X]) :: B[Y/X]       Y fresh

    V : ∀X.A[X] ⇒^p B
      —→
    (V [ ★ ]) : A[★/X] ⇒^p B

    (λx:C.M) : A1 → B1 ⇒^p A2 → B2
      —→
    λy:A2. ((λx:C.M) (y : A2 ⇒^p̄ A1)) : B1 ⇒^p B2

    V : ι ⇒^p ι
      —→
    V

    V : X ⇒^p X
      —→
    V

    V : A ⇒^p ★
      —→
    (V : A ⇒^p ground(A)) : ground(A) ⇒^- ★
      where p ≠ - and A ≠ ★

    (V : G ⇒^- ★) : ★ ⇒^p A
      —→
    V : G ⇒^p A
      if G ∼ A

    (V : G ⇒^- ★) : ★ ⇒^p A
      —→
    blame p
      if G is ground and not G ∼ A

### Dynamic Type Tests

    (V : H ⇒^- ★) is^p G
      —→
    true
      if H = G and H is 𝕀, 𝔹, or ★ → ★

    (V : X ⇒^p ★) is^q G
      —→
    blame q

Implementation note: the Scheme file contains a second clause named `IsFalse`,
but it has the same guard and result as `IsTrue`.  Thus the current
implementation has no distinct negative ground-tag test rule.


### `ν` Rules

    ν^p α:=A. c
      —→
    c
      if c is an integer or boolean constant

    ν^p α:=A. ⟨V,W⟩
      —→
    ⟨ν^p α:=A. V, ν^p α:=A. W⟩

    ν^p α:=A. λx:B.M
      —→
    λx:B. ν^p α:=A. M

    ν^p α:=A. Λ^q Y.M :: B
      —→
    Λ^q Y. ν^p α:=A↑. M :: B

The `A↑` in the type-abstraction rule is `A` weakened under the newly pushed
ordinary type variable `Y`.

    ν^p α:=A. (V : G ⇒^- ★)
      —→
    (ν^p α:=A. V) : G ⇒^- ★
      if G is ground

    ν^q α:=A. (V : X ⇒^p ★)
      —→
    blame q

    ν^p α:=A. (V : B ⇒^β̄ Y)
      —→
    (ν^p α:=A. V) : B ⇒^β̄ Y
      if V : B ⇒^β̄ Y is a value and β ≠ α

In de Bruijn form this is the single nonzero case
`unbind(suc k) ↦ unbind k`.  There is no zero case: a negative barrier for the
freshly allocated seal `α` cannot be pushed out past the `ν` that introduced
`α`.


### Barrier Rules

    V : ι ⇒^P ι
      —→
    V

    ⟨V,W⟩ : A × B ⇒^P A′ × B′
      —→
    ⟨V : A ⇒^P A′, W : B ⇒^P B′⟩

    (λx:C.M) : A → B ⇒^P A′ → B′
      —→
    λy:A′.
      (let x = y : A′ ⇒^P̄ A in M) : B ⇒^P B′

For a negative function barrier, `P = ᾱ`, so the argument crosses back through
the positive barrier `α` and the result remains protected by `ᾱ`; this is the
same rule with `P̄ = α`.

In de Bruijn form, the occurrence of `M` in the contractum is
`rename (ext suc) M`: the old argument remains de Bruijn index `0` under the
new `let`, and every old free term variable is shifted over both the `let`
binder and the wrapper lambda's argument.

    (Λ^p X.V :: B) : ∀X1.B1[X1] ⇒^P ∀X2.B2[X2]
      —→
    Λ^p X. (V : B ⇒^P B2[X/X2]) :: B2[X/X2]

For `P = ᾱ`, the body barrier is typed by the deep-pop rule at depth 1 under
the freshly introduced `Λ` variable.

    (V : G ⇒^- ★) : ★ ⇒^Q ★
      —→
    V : G ⇒^- ★

    (V : A′ ⇒^ᾱ X) : X ⇒^α A
      —→
    V
      where X is the type variable at de Bruijn depth 0

    V↑ : X+1 ⇒^α X
      —→
    V

    V : X ⇒^ᾱ X+1
      —→
    V↑

Here `V↑` is type-variable weakening through the term.  The executable
evaluator implements the first rule with a partial inverse of weakening; the
relational rule expresses the same partiality by requiring the redex to contain
an already-weakened value.

The source contains a commented-out `BarConflict` rule for barriers over sealed
casts to `★`; it is not part of the active reducer.


### Base Computation

    prim op V
      —→
    op(V)

    if true then M else N
      —→
    M

    if false then M else N
      —→
    N

    fst ⟨V,W⟩
      —→
    V

    snd ⟨V,W⟩
      —→
    W


## No-Barrier Experiment

The Scheme directory contains a no-barrier execution experiment used by older
simulation tests.  It is not part of the Agda language in this directory.  The
Agda evaluator keeps barriers and reports whether evaluation finishes, gets
stuck, or exhausts gas while another step is still available.
