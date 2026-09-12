# Design Criteria

Color Preservation: The set of type variables in scope (the "color")
at every subterm from the source program is invariant under reduction
(not including the runtime terms: conversions and scope boundaries,
and not including runtime created terms).

Progress: Every closed, well-typed term is a value or can take a reduction step.

Presrevation: A reduction step preserves the type of a closed term.

Determinism: Every term has at most one immediate reduct.

# Types

  X,Y,Z ∈ TyVar
  A,B,C ::= X | ℕ | 𝔹 | A → B | ∀X.A

# Representation Types

Representation types mention stable anchors, not source type variables.

  R,S ::= α | ℕ | 𝔹 | R → S | ∀α.R

# Source Terms

  n ∈ ℕ
  b ∈ 𝔹
  x ∈ Var
  k ::= n | b
  ⊕ ::= + | ×
  L,M,N ::= x | k | M ⊕ N | λx:A. N | L · M | Λα,X.N | L •B[A]

# Conversions

  c,d   ::= id(X) | id(ι) | c → d | ∀X.c | +X | -X

  -------------
  | +X(A) = c | (reveal X in A)
  | -X(A) = c | (conceal X in A)
  -------------

  +X(X) = +X                   -X(X) = -X
  +X(Y) = id       (X ≠ Y)     -X(Y) = id       (X ≠ Y)
  +X(ι) = id                   -X(ι) = id
  +X(A → B) = -X(A) → +X(B)    -X(A → B) = +X(A) → -X(B)
  +X(∀Y.A) = ∀Y.+X(A)  (X≠Y)   -X(∀Y.A) = ∀Y.-X(A)  (X ≠ Y)

  --------------
  | +X(c) = c′ | (reveal X in c)
  | -X(c) = c′ | (conceal X in c)
  --------------

  +X(+Y) = +Y                 -X(+Y) = +Y
  +X(-Y) = -Y                 -X(-Y) = -Y
  +X(id(ι)) = id(ι)           -X(id(ι)) = id(ι)
  +X(id(X)) = +X              -X(id(X)) = -X
  +X(id(Y)) = id(Y)           -X(id(Y)) = id(Y)       if X ≠ Y
  +X(c → d) = -X(c) → +X(d)   -X(c → d) = +X(c) → -X(d)
  +X(∀Y.c) = ∀Y.+X(c)         -X(∀Y.c) = ∀Y.-X(c)     if X ≠ Y
  +X(∀X.c) = ∀X.c             -X(∀X.c) = ∀X.c

# Runtime Terms

  χ ::= ∅ | χ,+X:=α | χ,-X:=α       (scope changes)
  Θ ::= ∅ | Θ,α:=R | Θ,α            (representation bindings)
  L,M,N ::= ... | νΘ,χ[M|c]

  We call νΘ,χ[M|c] a boundary

  -----------
  | -χ = χ′ |
  -----------

  -∅                 = ∅
  -(χ,+X:=α)          = (∅,-X:=α) ++ -χ
  -(χ,-X:=α)          = (∅,+X:=α) ++ -χ

# Contexts and variable lookup

  Γ ::= ∅ | Γ,α | Γ,α:=R | Γ,X:=α | Γ,x:A

  ------------
  | Γ ∋ X:=α |
  ------------

  ---------------
  (Γ,X:=α) ∋ X:=α

  Γ ∋ X:=α
  --------------- (X ≠ Y)
  (Γ,Y:=β) ∋ X:=α

  Γ ∋ X:=α
  ---------------
  (Γ,β:=S) ∋ X:=α

  Γ ∋ X:=α
  ------------
  (Γ,β) ∋ X:=α

  Γ ∋ X:=α
  ------------
  (Γ,x:A) ∋ X:=α


  ---------
  | Γ ∋ α |
  ---------

  ---------
  (Γ,α) ∋ α

  ---------------
  (Γ,α:=R) ∋ α

  Γ ∋ α
  --------------- (α ≠ β)
  (Γ,β:=S) ∋ α

  Γ ∋ α
  ---------------
  (Γ,Y:=β) ∋ α

  Γ ∋ α
  ------------ (α ≠ β)
  (Γ,β) ∋ α

  Γ ∋ α
  -----------
  (Γ,x:A) ∋ α

  ------------
  | Γ ∋ α:=R |
  ------------

  ---------------
  (Γ,α:=R) ∋ α:=R

  Γ ∋ α:=R
  --------------- (α ≠ β)
  (Γ,β:=S) ∋ α:=R
  
  Γ ∋ α:=R
  ---------------
  (Γ,Y:=β) ∋ α:=R

  Γ ∋ α:=R
  ------------
  (Γ,β) ∋ α:=R

  Γ ∋ α:=R
  ------------
  (Γ,x:A) ∋ α:=R

# Anchor representation of a source type

Write `⌊A⌋Γ` for the representation of `A` in `Γ`.

  ⌊X⌋Γ       = α                         if Γ ∋ X:=α
  ⌊ι⌋Γ       = ι
  ⌊A → B⌋Γ   = ⌊A⌋Γ → ⌊B⌋Γ
  ⌊∀X.A⌋Γ    = ∀α.⌊A⌋(Γ,α,X:=α)          (α fresh)

The last equation is defined up to renaming its bound anchor.

# Reading a representation type

The judgment `Γ ⊢ R ⇓ A` reads anchors through the source names visible
at one endpoint.

  Γ ∋ X:=α
  ---------
  Γ ⊢ α ⇓ X

  ---------
  Γ ⊢ ι ⇓ ι

  Γ ⊢ R ⇓ A   Γ ⊢ S ⇓ B
  ---------------------
  Γ ⊢ R → S ⇓ A → B

  Γ,α,X:=α ⊢ R ⇓ A
  ------------------ (α and X fresh)
  Γ ⊢ ∀α.R ⇓ ∀X.A

# Apply Scope Change to Context

  -------------
  | χ(Γ) = Γ′ |
  -------------

  ∅(Γ) = Γ
  (χ,+X:=α)(Γ)       = χ(Γ),X:=α
  (χ,-X:=α)(Γ,α)     = χ(Γ,α)
  (χ,-X:=α)(Γ,β)     = (χ,-X:=α)(Γ),β     (β ≠ α)
  (χ,-X:=α)(Γ,α:=R)  = χ(Γ,α:=R)
  (χ,-X:=α)(Γ,β:=R)  = (χ,-X:=α)(Γ),β:=R  (β ≠ α)
  (χ,-X:=α)(Γ,Y:=α)  = (χ,-X:=α)(Γ)
  (χ,-X:=α)(Γ,Y:=β)  = (χ,-X:=α)(Γ),Y:=β  (β ≠ α)
  (χ,-X:=α)(Γ,x:A)   = (χ,-X:=α)(Γ)

# Well-formed Types   Γ ⊢ A

  (wf-ℕ)      Γ ⊢ ℕ

  (wf-𝔹)      Γ ⊢ 𝔹

  (wf-tvar)   Γ ∋ X
              ------
              Γ ⊢ X

  (wf-fun)    Γ ⊢ A    Γ ⊢ B
              --------------
              Γ ⊢ A → B

  (wf-all)    X ∉ Γ  α ∉ Γ  Γ, α, X:=α ⊢ A
              ----------------------------
              Γ ⊢ ∀X.A

# Well-formed Representation Types   Γ ⊢ᴿ R

  (wfᴿ-tvar)  Γ ∋ α
              -----
              Γ ⊢ᴿ α

  (wfᴿ-ι)     Γ ⊢ᴿ ι

  (wfᴿ-fun)   Γ ⊢ᴿ R   Γ ⊢ᴿ S
              ----------------
              Γ ⊢ᴿ R → S

  (wfᴿ-all)   α ∉ Γ   Γ,α ⊢ᴿ R
              -----------------
              Γ ⊢ᴿ ∀α.R

# Well-formed Contexts   Γ ok

  ----
  ∅ ok

  Γ ok   α ∉ Γ
  ------------
  Γ,α ok

  Γ ok  Γ ⊢ᴿ R  α ∉ Γ
  -------------------
  Γ,α:=R ok

  Γ ok   α ∈ Γ   X ∉ Γ   Γ ∌ _:=α
  ---------------------------------
  Γ,X:=α ok

  Γ ok  Γ ⊢ A
  -----------
  Γ,x:A

# Conversion Typing 

  Γₑ ∋ X:=α   Γₑ ∋ α:=R   Γᵢ ⊢ R ⇓ A
  ------------------------------------
  Γᵢ ⊢ -X : A ⇒ X ⊣ Γₑ

  Γᵢ ∋ X:=α   Γᵢ ∋ α:=R   Γₑ ⊢ R ⇓ A
  ------------------------------------
  Γᵢ ⊢ +X : X ⇒ A ⊣ Γₑ

  -----------------------
  Γᵢ ⊢ id(ι) : ι ⇒ ι ⊣ Γₑ

  Γᵢ ∋ X   Γₑ ∋ X
  -----------------------
  Γᵢ ⊢ id(X) : X ⇒ X ⊣ Γₑ
  
  Γₑ ⊢ c : C ⇒ A ⊣ Γᵢ    Γᵢ ⊢ d : B ⇒ D ⊣ Γₑ
  ------------------------------------------
  Γᵢ ⊢ c → d : (A → B) ⇒ (C → D) ⊣ Γₑ

  Γᵢ,α,X:=α ⊢ c : A ⇒ B ⊣ Γₑ,α,X:=α
  ------------------------------------ (α fresh)
  Γᵢ ⊢ ∀X.c : ∀X.A ⇒ ∀X.B ⊣ Γₑ

# Conversion Identity    Id(A)

  Id(X) = id(X)
  Id(ℕ) = id(ℕ)
  Id(𝔹) = id(𝔹)
  Id(A → B) = Id(A) → Id(B)
  Id(∀X.A) = ∀X.Id(A)

# Conversion Composition

  Suppose:
    Γ₁ ⊢ c : A ⇒ B ⊣ Γ₂
    Γ₂ ⊢ d : B ⇒ C ⊣ Γ₃

  Γ ⊢ id(X) ⨟ d = d
  Γ ⊢ c ⨟ id(X) = c
  Γ ⊢ (c₁ → d₁) ⨟ (c₂ → d₂) = (Γ ⊢ c₂ ⨟ c₁) → (Γ ⊢ d₁ ⨟ d₂)
  Γ ⊢ (∀X.c) ⨟ (∀X.d) = ∀X.(Γ,X ⊢ c ⨟ d)
  Γ ⊢ -X ⨟ +X = Id(A)
    if Γ ∋ X:=α and Γ ∋ α:=R and Γ ⊢ R ⇓ A
  Γ ⊢ +X ⨟ -X = id(X)
  
# Well-formed χ   Γ ⊢ χ

  -----
  Γ ⊢ ∅

  Γ ⊢ χ   χ(Γ) ∌ X   χ(Γ) ∋ α   χ(Γ) ∌ _:=α
  ------------------------------------------------
  Γ ⊢ χ,+X:=α

  Γ ⊢ χ   χ(Γ) ∋ X:=α
  -------------------
  Γ ⊢ χ,-X:=α

# Well-formed Θ   Γ ⊢ Θ

  -----
  Γ ⊢ ∅

  Γ ⊢ Θ   Γ++Θ ⊢ᴿ R   α ∉ Γ++Θ
  --------------------------------
  Γ ⊢ Θ,α:=R

  Γ ⊢ Θ   α ∉ Γ++Θ
  -----------------
  Γ ⊢ Θ,α


# Term Typing 

  (ConstNat)  ---------
              Γ ⊢ n : ℕ

  (ConstBool)  ---------
               Γ ⊢ b : 𝔹

  (Arith)   Γ ⊢ L : ℕ   Γ ⊢ M : ℕ
            ---------------------
            Γ ⊢ L ⊕ M : ℕ

  (Var)     x:A ∈ Γ
            ---------
            Γ ⊢ x : A

  (Lam)     Γ, x:A ⊢ N : B   Γ ⊢ A
            -----------------------
            Γ ⊢ λx:A.N : A→B

  (App)     Γ ⊢ L : A→B   Γ ⊢ M : A
            -----------------------
            Γ ⊢ L · M : B

  (TyLam)    Γ, α, X:=α ⊢ N : A
            -------------------- (α fresh)
            Γ ⊢ Λα,X.N : ∀X.A

  (TyApp)    Γ ⊢ L : ∀X.B   Γ ⊢ A
            --------------------
            Γ ⊢ L@B[A] : B[X:=A]
            
  (Bndry)   Γ ⊢ Θ   Γ++Θ ⊢ χ
            χ(Γ++Θ) ⊢ M : A
            χ(Γ++Θ) ⊢ c : A ⇒ B ⊣ Γ
            -----------------------
            Γ ⊢ νΘ,χ[M|c] : B

# Values

  Vˢ,Wˢ ::= k | λx:A.N | Λα,X.V
  V,W ::= Vˢ | νθ,χ[Vˢ|c→d] | νθ,χ[Vˢ|∀X.c] | νθ,χ[Vˢ|-X] | νθ,χ[Vˢ|id(X)]

# Term-variable substitution   N[x := M : A]

  x[x:=V:A]             = V
  y[x:=V:A]             = y                             (y ≠ x)
  k[x:=V:A]             = k
  (M₁ ⊕ M₂)[x:=V : A]   = M₁[x:=V:A] ⊕ M₂[x:=V:A]
  (L · M)[x:=V:A]       = L[x:=V:A] · M[x:=V:A]
  (λx:B. N)[x:=V:A]     = λx:B. N                       (shadow)
  (λy:B. N)[x:=V:A]     = λy:B. N[x:=V:A]               (y ≠ x)
  (Λα,X. N)[x:=V:A]     = Λα,X. N[x:= ν-X:=α[V|Id(A)] ]
  (L @B[C])[x:=V:A]     = L[x:=V:A] @B[C]
  νΘ,χ[M|c] [x:=V]      = νΘ,χ[M|c]                     (skip M)

# Reduction Rules

Reduction is indexed by the ambient context so that type application can
store `⌊A⌋Γ`.  Write `Γ ⊢ M -→ N`, omitting `Γ ⊢` when it is clear.

  (Beta)      Γ ⊢ (λx:A. N) · W  -→ N[x:=W:A]
  (PrimBeta)  Γ ⊢ n₁ ⊕ n₂        -→ n₁ ⟦⊕⟧ n₂
  (TyBeta)    Γ ⊢ (Λα,X.V) •B[A]
              -→ να:=⌊A⌋Γ,+X:=α[ V | +X(B)]
  (Wrap)      Γ ⊢ νΘ,χ[ V |c→d] · W
              -→ νΘ,χ[ V · ν∅,-χ[W|c] |d]
  (TyWrap)    Γ ⊢ νΘ,χ[ Λα,X.V |∀X.c] •B[A]
              -→ ν(Θ,α:=⌊A⌋Γ),(χ,+X:=α)[ V |+X(c)]
  (Merge)     Γ ⊢ νΘ₁,χ₁[ νΘ₂,χ₂[ V |c] |d]
              -→ ν(Θ₁,Θ₂),(χ₁++χ₂)[ V |c⨟d]
              if νΘ₂,χ₂[ V |c] is a value
  (Const)     Γ ⊢ νΘ,χ[ k |id(ι)] -→ k

  (ξ-·-l)   Γ ⊢ L · M -→ L′ · M       if Γ ⊢ L -→ L′
  (ξ-·-r)   Γ ⊢ V · M -→ V · M′       if Γ ⊢ M -→ M′
  (ξ-⊕-l)   Γ ⊢ L ⊕ M -→ L′ ⊕ M       if Γ ⊢ L -→ L′
  (ξ-⊕-r)   Γ ⊢ V ⊕ M -→ V ⊕ M′       if Γ ⊢ M -→ M′
  (ξ-•)     Γ ⊢ L •B[A] -→ L′ •B[A]   if Γ ⊢ L -→ L′
  (ξ-Λ)     Γ ⊢ Λα,X.N -→ Λα,X.N′
              if Γ,α,X:=α ⊢ N -→ N′
  (ξ-ν)     Γ ⊢ νΘ,χ[M|c] -→ νΘ,χ[M′|c]
              if χ(Γ++Θ) ⊢ M -→ M′

# Theorem Statements

## Progress

If `∅ ⊢ M : A`, then either

  Value M

or there exists an `N` such that

  ∅ ⊢ M -→ N.

## Preservation

If

  Γ ok
  Γ ⊢ M : A
  Γ ⊢ M -→ N

then

  Γ ⊢ N : A.

## Determinism

If

  Γ ok
  Γ ⊢ M : A
  Γ ⊢ M -→ N₁
  Γ ⊢ M -→ N₂

then

  N₁ ≡α N₂.

Here `≡α` identifies renamings of bound term variables, type variables,
and anchors.  With a canonical fresh-name operation, replace `≡α` by `=`.

## Color Preservation

Define the color of a context by

  color(Γ) = { X | Γ ∋ X }.

Let `C` and `D` range over one-hole term contexts.  They descend through
every term constructor, not only evaluation positions.  Write `C[M]` for
plugging `M` into the hole of `C`.

The judgment

  Γ ⊢ C ⊣ Γ′

says that the hole of `C` is under context `Γ′` when `C[M]` is under
context `Γ`.  Its important clauses are

  Γ ⊢ □ ⊣ Γ

  Γ,α,X:=α ⊢ C ⊣ Γ′
  -------------------
  Γ ⊢ Λα,X.C ⊣ Γ′

  χ(Γ++Θ) ⊢ C ⊣ Γ′
  ---------------------
  Γ ⊢ νΘ,χ[C | c] ⊣ Γ′

A term abstraction adds its term-variable binding.  Descending through
any other source-term constructor leaves the context unchanged.

For a reduction `r`, write

  Γ ⊢ C[M] ⇝[r] D[N]

if the focused source node `M` has descendant `N`.  Nodes copied by a rule
retain the focus.  Substitution relates each node of the substituted value
to every copy of that node.  Nodes created by a reduction rule, including
new application and type-application nodes, cannot receive the focus.
Consumed nodes have no descendant.  Write `Γ ⊢ C[M] ⇝[rs]* D[N]` for
the reflexive, transitive closure along `rs`.

Some representative clauses follow.  In the first `Beta` clause,
substitution acts on a one-hole context without filling its hole.

  Γ ⊢ ((λx:A. C[M]) · W)
    ⇝[Beta]
  C[x:=W][M[x:=W]]

If `P[x:=W] = D[M]`, where `M` is any one copy descended from the focused
node in `W`, then

  Γ ⊢ ((λx:A. P) · C[M])
    ⇝[Beta]
  D[M]

  Γ ⊢ ((νΘ,χ[C[M] | c₁→c₂]) · W)
    ⇝[Wrap]
  νΘ,χ[C[M] · ν∅,-χ[W | c₁] | c₂]

  Γ ⊢ ((νΘ,χ[V | c₁→c₂]) · C[M])
    ⇝[Wrap]
  νΘ,χ[V · ν∅,-χ[C[M] | c₁] | c₂]

  Γ ⊢ ((Λα,X. C[M]) •B[A])
    ⇝[TyBeta]
  να:=⌊A⌋Γ,+X:=α[C[M] | +X(B)]

  Γ ⊢ ((νΘ,χ[Λα,X. C[M] | ∀X.c]) •B[A])
    ⇝[TyWrap]
  ν(Θ,α:=⌊A⌋Γ),(χ,+X:=α)[C[M] | +X(c)]

  Γ ⊢ νΘ₁,χ₁[νΘ₂,χ₂[C[M] | c] | d]
    ⇝[Merge]
  ν(Θ₁,Θ₂),(χ₁++χ₂)[C[M] | c⨟d]

Residuals lift through an unchanged surrounding context:

  Γ′ ⊢ C[M] ⇝[r] D[N]
  Γ ⊢ E ⊣ Γ′
  -------------------------
  Γ ⊢ E[C[M]] ⇝[r] E[D[N]]

There is no clause focusing the application introduced by `Wrap`, or any
other source-shaped node introduced by reduction.

Color preservation states that if

  C[M] is a source term
  ∅ ⊢ C[M] : A
  ∅ ⊢ C[M] -→* D[N]               by rs
  ∅ ⊢ C[M] ⇝[rs]* D[N]
  ∅ ⊢ C ⊣ Γ₁
  ∅ ⊢ D ⊣ Γ₂

then

  color(Γ₁) = color(Γ₂).

## Scope-change preservation

If `Γ ok`, `Γ ⊢ χ`, and `χ(Γ) = Γ′`, then `Γ′ ok`.

## Representation soundness

If `Γ ok` and `Γ ⊢ A`, then

  Γ ⊢ᴿ ⌊A⌋Γ

and

  Γ ⊢ ⌊A⌋Γ ⇓ A.


# Examples

## `Beta` followed by `TyWrap`

  (λg:∀Y.Y→Y. Λζ,Z. g •(Y→Y)[Z]) · (Λη,Y. λy:Y.y)
  -→⟨ Beta ⟩
  Λζ,Z. (ν∅,-Z:=ζ[Λη,Y. λy:Y.y | Id(∀Y.Y→Y)]) •(Y→Y)[Z]
  -→⟨ TyWrap ⟩
  Λζ,Z. νη:=ζ,(-Z:=ζ,+Y:=η)[ λy:Y.y | -Y → +Y ]

At the `TyWrap` step, the exterior context is

  ΓZ = Γ,ζ,Z:=ζ

Thus

  ⌊Z⌋ΓZ = ζ.

The interior context is

  (-Z:=ζ,+Y:=η)(ΓZ,η:=ζ)
    = (+Y:=η)(Γ,ζ,η:=ζ)
    = Γ,ζ,η:=ζ,Y:=η.
