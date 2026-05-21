# PolyConvert Notes

========================================================================
THE DEVELOPMENT
========================================================================

These notes describe the `extrinsic-inst` development using named variables in
the prose. The Agda files use de Bruijn indices for type variables, seal names,
and term variables; read `A[X]`, `M[x]`, and `Σ, α:=A` below as the informal
named presentation of those binders and stores.

## Types

    Types                 A,B,C      ::=  X | α | ι | ★ | A → B
                                        | ∀X.A[X]
    Base types            ι          ::=  ℕ | 𝔹
    Ground types          G,H        ::=  α | ι | ★ → ★

    Type variables        X,Y
    Seal variables        α,β
    Term variables        x,y

    Type contexts         Δ          ::=  ∅ | Δ, X
    Seal contexts         Ψ          ::=  ∅ | Ψ, α
    Stores                Σ          ::=  ∅ | Σ, α:=A
    Term contexts         Γ          ::=  ∅ | Γ, x:A
    Imprecision contexts  Φ          ::=  ∅ | Φ, X⊑X | Φ, X⊑★
    Consistency contexts  Ω          ::=  ∅ | Ω, X~★ | Ω, ★~X
                                        | Ω, X~X | Ω, neither
    Gradual term contexts Π          ::=  ∅ | Π, x:p

The judgment `Δ ; Ψ ⊢ A` says that `A` is well formed with type-variable
context `Δ` and seal context `Ψ`.

    X ∈ Δ
    -----
    Δ ; Ψ ⊢ X

    α ∈ Ψ
    -----
    Δ ; Ψ ⊢ α

    ---------
    Δ ; Ψ ⊢ ι

    ---------
    Δ ; Ψ ⊢ ★

    Δ ; Ψ ⊢ A    Δ ; Ψ ⊢ B
    ----------------------
    Δ ; Ψ ⊢ A → B

    Δ, X ; Ψ ⊢ A[X]
    ----------------
    Δ ; Ψ ⊢ ∀X.A[X]


## Imprecision

Type imprecision evidence is written `p,q`. Its typing judgment is
`Ψ | Φ ⊢ p : A ⊑ B`, where `Φ` records how type variables are allowed
to relate: `X⊑X` means the variable is preserved, and `X⊑★` means the
variable may be abstracted to `★`.

    Imprecision           p,q        ::=  id★ | X! | p! | id_X | id_α
                                        | id_ι | p → q | ∀X.p[X] | νX.p[X]

    Source/target intuition:
      id★        : ★ ⊑ ★
      X!         : X ⊑ ★
      p!         : A ⊑ ★, when p : A ⊑ G and G is ground
      id_X       : X ⊑ X
      id_α       : α ⊑ α
      id_ι       : ι ⊑ ι
      p → q      : A → B ⊑ A′ → B′
      ∀X.p[X]    : ∀X.A[X] ⊑ ∀X.B[X]
      νX.p[X]    : ∀X.A[X] ⊑ B

    -----------------
    Ψ | Φ ⊢ id★ : ★ ⊑ ★

    Φ(X) = X⊑★
    ----------------
    Ψ | Φ ⊢ X! : X ⊑ ★

    G ground    Ψ | Φ ⊢ p : A ⊑ G
    --------------------------------
    Ψ | Φ ⊢ p! : A ⊑ ★

    Φ(X) = X⊑X
    -------------------
    Ψ | Φ ⊢ id_X : X ⊑ X

    α ∈ Ψ
    -------------------
    Ψ | Φ ⊢ id_α : α ⊑ α

    -------------------
    Ψ | Φ ⊢ id_ι : ι ⊑ ι

    Ψ | Φ ⊢ p : A ⊑ A′    Ψ | Φ ⊢ q : B ⊑ B′
    ------------------------------------------------
    Ψ | Φ ⊢ p → q : A → B ⊑ A′ → B′

    Ψ | Φ, X⊑X ⊢ p[X] : A[X] ⊑ B[X]
    ---------------------------------------
    Ψ | Φ ⊢ ∀X.p[X] : ∀X.A[X] ⊑ ∀X.B[X]

    Ψ | Φ, X⊑★ ⊢ p[X] : A[X] ⊑ B
    --------------------------------- B well formed without X
    Ψ | Φ ⊢ νX.p[X] : ∀X.A[X] ⊑ B

The judgment `Ψ | Φ ⊢ p : A ⊒ B` abbreviates `Ψ | Φ ⊢ p : B ⊑ A`.


## Conversion

Conversions are store-indexed seal replacement witnesses. Reveals turn sealed
types back into the type stored for the seal; conceals move in the opposite
direction.

    Reveal conversions    c↑         ::=  unseal α | c↓ → c↑
                                        | ∀X.c↑[X] | id_A
    Conceal conversions   c↓         ::=  seal α | c↑ → c↓
                                        | ∀X.c↓[X] | id_A

    Judgments:
      Δ ; Ψ ; Σ ⊢ c↑ : A ↑ˢ B
      Δ ; Ψ ; Σ ⊢ c↓ : A ↓ˢ B

    α:=A ∈ Σ
    -------------------------------
    Δ ; Ψ ; Σ ⊢ unseal α : α ↑ˢ A

    Δ ; Ψ ; Σ ⊢ c↓ : A′ ↓ˢ A    Δ ; Ψ ; Σ ⊢ c↑ : B ↑ˢ B′
    ------------------------------------------------------
    Δ ; Ψ ; Σ ⊢ c↓ → c↑ : A → B ↑ˢ A′ → B′

    Δ, X ; Ψ ; Σ ⊢ c↑[X] : A[X] ↑ˢ B[X]
    --------------------------------------
    Δ ; Ψ ; Σ ⊢ ∀X.c↑[X] : ∀X.A[X] ↑ˢ ∀X.B[X]

    Δ ; Ψ ⊢ A
    --------------------------
    Δ ; Ψ ; Σ ⊢ id_A : A ↑ˢ A

    α:=A ∈ Σ
    -----------------------------
    Δ ; Ψ ; Σ ⊢ seal α : A ↓ˢ α

    Δ ; Ψ ; Σ ⊢ c↑ : A′ ↑ˢ A    Δ ; Ψ ; Σ ⊢ c↓ : B ↓ˢ B′
    ------------------------------------------------------
    Δ ; Ψ ; Σ ⊢ c↑ → c↓ : A → B ↓ˢ A′ → B′

    Δ, X ; Ψ ; Σ ⊢ c↓[X] : A[X] ↓ˢ B[X]
    --------------------------------------
    Δ ; Ψ ; Σ ⊢ ∀X.c↓[X] : ∀X.A[X] ↓ˢ ∀X.B[X]

    Δ ; Ψ ⊢ A
    --------------------------
    Δ ; Ψ ; Σ ⊢ id_A : A ↓ˢ A

The functions `convert↑ A α` and `convert↓ A α` compute the reveal/conceal
structure induced by replacing the distinguished type variable in `A` with the
fresh seal `α`.


## Consistency

Type consistency is written `Ω ⊢ A ~ B`, where the consistency context
records how variables may relate.

    Consistency modes     m          ::=  X~★ | ★~X | X~X | neither

    ----------------
    Ω ⊢ ★ ~ ★

    Ω(X) = X~X
    ------------
    Ω ⊢ X ~ X

    ------------
    Ω ⊢ ι ~ ι

    Ω ⊢ A ~ A′    Ω ⊢ B ~ B′
    ------------------------
    Ω ⊢ A → B ~ A′ → B′

    Ω, X~X ⊢ A[X] ~ B[X]
    ---------------------
    Ω ⊢ ∀X.A[X] ~ ∀X.B[X]

    G ground    Ω ⊢ A ~ G
    ---------------------
    Ω ⊢ A ~ ★

    H ground    Ω ⊢ H ~ B
    ---------------------
    Ω ⊢ ★ ~ B

    Ω(X) = X~★
    ------------
    Ω ⊢ X ~ ★

    Ω(X) = ★~X
    ------------
    Ω ⊢ ★ ~ X

    Ω, X~★ ⊢ A[X] ~ B
    ------------------- B well formed without X
    Ω ⊢ ∀X.A[X] ~ B

    Ω, ★~X ⊢ A ~ B[X]
    ------------------- A well formed without X
    Ω ⊢ A ~ ∀X.B[X]

The function `coerce` maps a consistency derivation to a pair of
imprecision witnesses. Informally, if `Ω ⊢ A ~ B`, then `coerce`
chooses a common type `C` and produces evidence `C ⊑ A` and `C ⊑ B`.
Compilation uses these two witnesses to mediate implicit gradual
consistency checks.


## Gradual Terms

Gradual source terms are the terms before explicit imprecision and conversion
operations have been inserted.

    Gradual terms         L,M,N      ::=  x
                                        | λx:A.N[x]
                                        | L M
                                        | ΛX.V[X]
                                        | M [ A ]
                                        | κ
                                        | L ⊕ M

    Gradual values        V,W        ::=  λx:A.N[x] | ΛX.V[X] | κ


## Typing Rules for Gradual Terms

The source typing judgment is `Δ ; Γ ⊢ M : A`.

    Γ(x) = A
    -----------
    Δ ; Γ ⊢ x : A

    Δ ⊢ A    Δ ; Γ, x:A ⊢ M[x] : B
    ------------------------------------
    Δ ; Γ ⊢ λx:A.M[x] : A → B

    Δ ; Γ ⊢ L : A → B    Δ ; Γ ⊢ M : A′    Δ ⊢ A ~ A′
    ---------------------------------------------------
    Δ ; Γ ⊢ L M : B

    Δ ; Γ ⊢ L : ★    Δ ; Γ ⊢ M : A′    Δ ⊢ A′ ~ ★
    ------------------------------------------------
    Δ ; Γ ⊢ L M : ★

    Δ, X ; Γ ⊢ V[X] : A[X]
    ------------------------ V is a value
    Δ ; Γ ⊢ ΛX.V[X] : ∀X.A[X]

    Δ ; Γ ⊢ M : ∀X.B[X]    Δ, X ⊢ B[X]    Δ ⊢ A
    ------------------------------------------------
    Δ ; Γ ⊢ M [ A ] : B[A]

    ------------------
    Δ ; Γ ⊢ κ : tp(κ)

    Δ ; Γ ⊢ L : A    Δ ⊢ A ~ ℕ
    Δ ; Γ ⊢ M : B    Δ ⊢ B ~ ℕ
    --------------------------------
    Δ ; Γ ⊢ L ⊕ M : ℕ


## Gradual Term Imprecision

Gradual term imprecision is written `Δ ; Φ ; Π ⊢ᴳ M ⊑ M′ : p`. The
context `Π` maps each term variable to the type-imprecision witness for
its endpoints.

    Π(x) = p
    ------------------------
    Δ ; Φ ; Π ⊢ᴳ x ⊑ x : p

    Φ ⊢ p : A ⊑ A′    Δ ; Φ ; Π, x:p ⊢ᴳ M[x] ⊑ M′[x] : q
    ----------------------------------------------------------------
    Δ ; Φ ; Π ⊢ᴳ λx:A.M[x] ⊑ λx:A′.M′[x] : p → q

    Δ ; Φ ; Π ⊢ᴳ L ⊑ L′ : p → q
    Δ ; Φ ; Π ⊢ᴳ M ⊑ M′ : p′
    ------------------------------------
    Δ ; Φ ; Π ⊢ᴳ L M ⊑ L′ M′ : q

    Δ, X ; Φ, X⊑X ; Π↑ ⊢ᴳ V[X] ⊑ V′[X] : p[X]
    ---------------------------------------------------- V and V′ are values
    Δ ; Φ ; Π ⊢ᴳ ΛX.V[X] ⊑ ΛX.V′[X] : ∀X.p[X]

    Δ, X ; Φ, X⊑★ ; Π↑ ⊢ᴳ V[X] ⊑ M′ : p[X]
    ----------------------------------------------- V is a value
    Δ ; Φ ; Π ⊢ᴳ ΛX.V[X] ⊑ M′ : νX.p[X]

    Δ ; Φ ; Π ⊢ᴳ M ⊑ M′ : ∀X.p[X]    Φ ⊢ q : A ⊑ A′
    ----------------------------------------------------------
    Δ ; Φ ; Π ⊢ᴳ M [ A ] ⊑ M′ [ A′ ] : p[A := q]

    Δ ; Φ ; Π ⊢ᴳ M ⊑ M′ : νX.p[X]    Φ ⊢ q : A ⊑ ★
    ---------------------------------------------------------
    Δ ; Φ ; Π ⊢ᴳ M [ A ] ⊑ M′ : p[A := q]

    --------------------------------
    Δ ; Φ ; Π ⊢ᴳ n ⊑ n : id_ℕ

    Δ ; Φ ; Π ⊢ᴳ L ⊑ L′ : pL
    Δ ; Φ ; Π ⊢ᴳ M ⊑ M′ : pM
    ----------------------------------------
    Δ ; Φ ; Π ⊢ᴳ L ⊕ M ⊑ L′ ⊕ M′ : id_ℕ


## Terms

Target terms make type imprecision and store-driven conversion explicit.

    Terms                 L,M,N      ::=  x | λx:A.N[x] | L M | ΛX.V[X]
                                        | M [ T ] | κ | L ⊕ M | M ⇑ p
                                        | M ⇓ p | M ↑ c↑ | M ↓ c↓
                                        | blame ℓ

    Values                V,W        ::=  λx:A.N[x] | κ | ΛX.V[X]
                                        | V ⇑ p | V ⇓ p | V ↑ c↑
                                        | V ↓ c↓

Value-shaped upcasts include `X!`, `p!`, `p → q`, and `∀X.p[X]`.
Value-shaped downcasts include `p → q`, `∀X.p[X]`, and `νX.p[X]`.
Value-shaped reveals and conceals include the arrow and universal cases,
and conceal also includes `seal α`.


## Typing Rules for Terms

The target typing judgment is `Δ ; Ψ ; Σ ; Γ ⊢ M : A`.

    x:A ∈ Γ
    ---------------------
    Δ ; Ψ ; Σ ; Γ ⊢ x : A

    Δ ; Ψ ⊢ A    Δ ; Ψ ; Σ ; Γ, x:A ⊢ M[x] : B
    ------------------------------------------------
    Δ ; Ψ ; Σ ; Γ ⊢ λx:A.M[x] : A → B

    Δ ; Ψ ; Σ ; Γ ⊢ L : A → B    Δ ; Ψ ; Σ ; Γ ⊢ M : A
    ----------------------------------------------------
    Δ ; Ψ ; Σ ; Γ ⊢ L M : B

    Δ, X ; Ψ ; Σ ; Γ ⊢ V[X] : A[X]
    -------------------------------- V is a value
    Δ ; Ψ ; Σ ; Γ ⊢ ΛX.V[X] : ∀X.A[X]

    Δ ; Ψ ; Σ ; Γ ⊢ M : ∀X.B[X]    Δ, X ; Ψ ⊢ B[X]    Δ ; Ψ ⊢ T
    ----------------------------------------------------------------
    Δ ; Ψ ; Σ ; Γ ⊢ M [ T ] : B[T]

    -----------------------------
    Δ ; Ψ ; Σ ; Γ ⊢ κ : tp(κ)

    Δ ; Ψ ; Σ ; Γ ⊢ L : ℕ    Δ ; Ψ ; Σ ; Γ ⊢ M : ℕ
    ------------------------------------------------
    Δ ; Ψ ; Σ ; Γ ⊢ L ⊕ M : ℕ

    Ψ | id(Δ) ⊢ p : A ⊑ B    Δ ; Ψ ; Σ ; Γ ⊢ M : A
    ------------------------------------------------
    Δ ; Ψ ; Σ ; Γ ⊢ M ⇑ p : B

    Ψ | id(Δ) ⊢ p : A ⊒ B    Δ ; Ψ ; Σ ; Γ ⊢ M : A
    ------------------------------------------------
    Δ ; Ψ ; Σ ; Γ ⊢ M ⇓ p : B

    Δ ; Ψ ; Σ ⊢ c↑ : A ↑ˢ B    Δ ; Ψ ; Σ ; Γ ⊢ M : A
    ---------------------------------------------------
    Δ ; Ψ ; Σ ; Γ ⊢ M ↑ c↑ : B

    Δ ; Ψ ; Σ ⊢ c↓ : A ↓ˢ B    Δ ; Ψ ; Σ ; Γ ⊢ M : A
    ---------------------------------------------------
    Δ ; Ψ ; Σ ; Γ ⊢ M ↓ c↓ : B

    ----------------------------
    Δ ; Ψ ; Σ ; Γ ⊢ blame ℓ : A


## Reduction Rules for Terms

Pure one-step reduction is written `M —→ N`.

    (λx:A.N[x]) V                 —→  N[V/x]
    (V ⇑ ∀X.p[X]) [ A ]           —→  (V [ A ]) ⇑ p[A]
    (V ⇑ (p → q)) W               —→  (V (W ⇓ p)) ⇑ q
    (V ⇓ (p → q)) W               —→  (V (W ⇑ p)) ⇓ q
    (V ↑ (c↓ → c↑)) W             —→  (V (W ↓ c↓)) ↑ c↑
    (V ↓ (c↑ → c↓)) W             —→  (V (W ↑ c↑)) ↓ c↓
    V ⇑ id_A                      —→  V
    V ⇓ id_A                      —→  V
    V ↑ id_A                      —→  V
    V ↓ id_A                      —→  V
    (V ↓ seal α) ↑ unseal α       —→  V
    (V ⇑ p!) ⇓ q!                 —→  (V ⇑ p) ⇓ q,  tgt(p) = tgt(q)
    (V ⇑ p!) ⇓ q!                 —→  blame ℓ,      tgt(p) ≠ tgt(q)
    n ⊕ m                         —→  n + m
    blame ℓ in a strict position  —→  blame ℓ

Store-threaded one-step reduction is written `Σ | M —→ Σ′ | N`.

    M —→ N                    implies  Σ | M —→ Σ | N
    Σ | (ΛX.V[X]) [ A ]       —→  Σ,α:=A | V[α/X] ↑ convert↑(B,α)
    Σ | (V ⇓ ∀X.p[X]) [ A ]   —→  Σ,α:=A | (V [ α ]) ⇓ p[α]
                                          ↑ convert↑(src(p),α)
    Σ | (V ⇓ νX.p[X]) [ A ]   —→  Σ,α:=A | V ⇓ p[α]
                                          ↑ convert↑(src(p),α)
    Σ | V ⇑ νX.p[X]           —→  Σ,α:=★ | (V [ α ]) ⇑ p[α]
    Σ | (V ↑ ∀X.c↑[X]) [ T ]  —→  Σ | (V [ T ]) ↑ c↑[T]
    Σ | (V ↓ ∀X.c↓[X]) [ T ]  —→  Σ | (V [ T ]) ↓ c↓[T]

In the store-extending rules, `α` is fresh for `Σ`.

The store-threaded reduction relation is closed under the strict contexts for
application, type application, upcasts, downcasts, reveals, conceals, and
primitive operations.

Multi-step reduction is written `Σ | M —↠ Σ′ | N`.


## Compile from Gradual Terms to Terms

Compilation is typed: if `Δ ; Γ ⊢ M : A`, then `compile` returns a
target term `N` such that `Δ ; 0 ; ∅ ; Γ ⊢ N : A`.

    compile(x) = x

    compile(λx:A.M[x]) =
      λx:A.compile(M[x])

    compile(L M) =
      compile(L) (compile(M) ⇓ p_right ⇑ p_left)

      where the source typing rule used `A ~ A′`, the function expects `A`,
      the argument has type `A′`, and `coerce(A ~ A′)` supplies the two
      imprecision witnesses inserted around the compiled argument.

    compile(L M) when L has type ★ =
      (compile(L) ⇓ q_right ⇑ q_left) compile(M)

      where `q_left` and `q_right` come from the consistency evidence that
      treats `★` as compatible with a function type.

    compile(ΛX.V[X]) =
      ΛX.compile(V[X])

    compile(M [ T ]) =
      compile(M) [ T ]

    compile(κ) =
      κ

    compile(L ⊕ M) =
      (compile(L) ⇓ pL_right ⇑ pL_left) ⊕
      (compile(M) ⇓ pM_right ⇑ pM_left)

      where the inserted imprecisions come from the consistency checks against
      `ℕ`.

Compilation preserves source values: if `V` is a gradual value and `V` is
well typed, then `compile(V)` is a target value.


## Type Safety

Progress.
If `0 ; Ψ ; Σ ; ∅ ⊢ M : A`, then one of the following holds.

    * `M` is a value.
    * There exist `Σ′` and `N` such that `Σ | M —→ Σ′ | N`.
    * `M = blame ℓ` for some label `ℓ`.

Preservation.
If `StoreWf Δ Ψ Σ`, `Δ ; Ψ ; Σ ; Γ ⊢ M : A`, and
`Σ | M —→ Σ′ | M′`, then there exists a seal context `Ψ′` such that
`StoreWf Δ Ψ′ Σ′` and `Δ ; Ψ′ ; Σ′ ; Γ ⊢ M′ : A`.


## Compile Preserves Imprecision

The broad closed-world statement one might first expect is:

    If 0 ; ∅ ; ∅ ⊢ᴳ M ⊑ M′ : p
    and 0 ; ∅ ⊢ M : A,
    then there exist B and a typing derivation 0 ; ∅ ⊢ M′ : B such that
    compile(M) ⊑ compile(M′) : A ⊑ B.

The current target term-imprecision judgment does not validate this broad
statement. The Agda file `proof/CompilePreservesImprecision.agda` records the
obstruction as a counterexample:

    ΛX.0 ⊑ 0 : νX.id_ℕ

The left source term has type `∀X.ℕ`, but the compiled target terms
`ΛX.0` and `0` are not related by the current target relation at
`∀X.ℕ ⊑ ℕ`. Formally, the development states:

    ClosedCompilePreservation =
      ∀ M M′ A p.
        0 ; ∅ ; ∅ ⊢ᴳ M ⊑ M′ : p →
        0 ; ∅ ⊢ M : A →
        ∃ B. ∃ M′⊢.
          compile(M) ⊑ compile(M′) : A ⊑ B

    closed-compile-preservation-impossible :
      ¬ ClosedCompilePreservation


## Static Gradual Guarantee

The public SGG theorem is:

    If 0 ; ∅ ; ∅ ⊢ᴳ M ⊑ M′ : p
    and 0 ; ∅ ⊢ M : A,
    then there exists B such that
      0 ; ∅ ⊢ M′ : B
    and
      0 | ∅ ⊢ p : A ⊑ B.

The indexed internal version generalizes this statement to nonempty type and
term precision contexts.


## Dynamic Gradual Guarantee

The public DGG theorem is stated over target terms. If `StoreWf 0 Ψ Σ` and
`M ⊑ M′ : A ⊑ B` in the empty term-imprecision context, then all of the
following hold.

    1. If the more precise term evaluates to a value,
       Σ | M —↠ ΣL | V,
       then the less precise term evaluates to a value,
       Σ | M′ —↠ ΣR | V′,
       and the resulting values are related:
       V ⊑ V′ : A ⊑ B
       under well-formed output stores.

    2. If the more precise term diverges, then the less precise term diverges.

    3. If the less precise term evaluates to a value,
       Σ | M′ —↠ ΣR | V′,
       then either the more precise term blames, or the more precise term
       evaluates to a related value:
       Σ | M —↠ ΣL | V
       and
       V ⊑ V′ : A ⊑ B
       under well-formed output stores.

    4. If the less precise term diverges, then the more precise term
       diverges-or-blames: from every reachable state of the more precise term,
       the term is either already blame or can take another step.
