# Design Criteria

Color Preservation: The set of type variables in scope (the "color")
at every subterm from the source program is invariant under reduction
(not including the runtime terms: conversions and scope boundaries,
runtime-created terms, or constant literals).

Progress: Every closed, well-typed term is a value or can take a reduction step.

Presrevation: A reduction step preserves the type of a closed term.

Determinism: Every term has at most one immediate reduct.

# Types

  X,Y,Z ∈ TyVar
  a,b ::= X | ℕ | 𝔹            (atomic types)
  A,B,C ::= a | A → B | ∀X.A

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

  ĉ,ḓ ::= +X | -X | c → d | ∀X.c
  c,d ::= id(A) | ĉ ∷ c

The builders are indexed by a visible context `Γᵥ` and a concealed context
`Γₕ`.  If an equation reaches a free occurrence of `X`, its represented
type is obtained by

  Γᵥ ∋ X:=α   Γᵥ ∋ α:=R   Γₕ ⊢ R ⇓ S
  ------------------------------------
  Γᵥ ; Γₕ ⊢ repr(X) = S.

No representation is needed if `X` does not occur.  The context indices
and `S` are suppressed in the equations below:

  -------------
  | +X(A) = c | (reveal X in A)
  | -X(A) = c | (conceal X in A)
  -------------

Both operations return a conversion in normal form.

  +X(X) = +X ∷ id(S)              -X(X) = -X ∷ id(X)
  +X(Y) = id(Y)       (X ≠ Y)     -X(Y) = id(Y)       (X ≠ Y)
  +X(ι) = id(ι)                   -X(ι) = id(ι)
  +X(A → B) = (-X(A) → +X(B)) ∷ id((A → B)[X:=S])
  -X(A → B) = (+X(A) → -X(B)) ∷ id(A → B)
  +X(∀Y.A) = (∀Y.+X(A)) ∷ id((∀Y.A)[X:=S])  (X ≠ Y)
  -X(∀Y.A) = (∀Y.-X(A)) ∷ id(∀Y.A)          (X ≠ Y)
  +X(∀X.A) = id(∀X.A)             -X(∀X.A) = id(∀X.A)

  -----------------
  | +X(c) = c′ | (reveal X in c)
  | -X(c) = c′ | (conceal X in c)
  -----------------

These operations require `NF(c)` and return a conversion in normal form.

  +X(id(A)) = +X(A)             -X(id(A)) = -X(A)
  +X(ĉ ∷ c) = +X(ĉ) ⨟ +X(c)
  -X(ĉ ∷ c) = -X(ĉ) ⨟ -X(c)

On heads, the operations are

  +X(+Y) = +Y ∷ id(B)             -X(+Y) = +Y ∷ id(B)
  +X(-Y) = -Y ∷ id(B)             -X(-Y) = -Y ∷ id(B)
  +X(c → d) = (-X(c) → +X(d)) ∷ id(B)
  -X(c → d) = (+X(c) → -X(d)) ∷ id(B)
  +X(∀Y.c) = (∀Y.+X(c)) ∷ id(B)  (X ≠ Y)
  -X(∀Y.c) = (∀Y.-X(c)) ∷ id(B)  (X ≠ Y)
  +X(∀X.c) = (∀X.c) ∷ id(B)
  -X(∀X.c) = (∀X.c) ∷ id(B)

Here `B` is the target supplied by the typing derivation of the transformed
head.  If `X=Y` under `∀Y`, then the head is unchanged and terminated by
its target identity.

# Runtime Terms

  δ ::= +X:=α | -X:=α                    (atomic scope changes)
  χ ::= ∅ | δ | χ ; χ                    (scope changes)
  Θ ::= ∅ | Θ,α:=R | Θ,α                (representation bindings)
  L,M,N ::= ... | νΘ,χ[M|c]

  We call νΘ,χ[M|c] a boundary

  -----------
  | -χ = χ′ |
  -----------

  -∅                 = ∅
  -(+X:=α)            = -X:=α
  -(-X:=α)            = +X:=α
  -(χ₁ ; χ₂)           = -χ₂ ; -χ₁

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

# Rightmost visible source name

The judgment `Γ ▷ X:=α` says that `X:=α` is the rightmost visible
source-name binding in `Γ`.

  -----------------
  (Γ,X:=α) ▷ X:=α

  Γ ▷ X:=α
  ---------------
  (Γ,β) ▷ X:=α

  Γ ▷ X:=α
  -------------------
  (Γ,β:=R) ▷ X:=α

  Γ ▷ X:=α
  -----------------
  (Γ,x:A) ▷ X:=α

There is no rule through `Y:=β`.  For example,

  α,X:=α,β,Y:=β ▷ Y:=β
  α,X:=α,β,Y:=β ⋫ X:=α.


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

# Scope Change Action on a Context

  -------------
  | χ(Γ) = Γ′ |
  -------------

  ∅(Γ)                    = Γ
  (+X:=α)(Γ)              = Γ,X:=α
  (-X:=α)(Γ,α)            = Γ,α
  (-X:=α)(Γ,β)            = (-X:=α)(Γ),β     (β ≠ α)
  (-X:=α)(Γ,α:=R)         = Γ,α:=R
  (-X:=α)(Γ,β:=R)         = (-X:=α)(Γ),β:=R  (β ≠ α)
  (-X:=α)(Γ,X:=α)         = Γ
  (-X:=α)(Γ,x:A)          = (-X:=α)(Γ)
  (χ₁ ; χ₂)(Γ)             = χ₂(χ₁(Γ))

There is no equation that carries `-X:=α` through a source-name binding.
The transition premise `Γ ▷ X:=α` ensures that the rightmost such binding
is already `X:=α`.  For example,

  α,X:=α,β,Y:=β ⋫ X:=α,

so `-X:=α` cannot be applied until `-Y:=β` has removed `Y:=β`.

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

# Conversion-head Typing

  Γₑ ∋ X:=α   Γₑ ∋ α:=R   Γᵢ ⊢ R ⇓ A
  ------------------------------------
  Γᵢ ⊢̂ -X : A ⇒ X ⊣ Γₑ

  Γᵢ ∋ X:=α   Γᵢ ∋ α:=R   Γₑ ⊢ R ⇓ A
  ------------------------------------
  Γᵢ ⊢̂ +X : X ⇒ A ⊣ Γₑ
  
  Γₑ ⊢ c : C ⇒ A ⊣ Γᵢ    Γᵢ ⊢ d : B ⇒ D ⊣ Γₑ
  ------------------------------------------
  Γᵢ ⊢̂ c → d : (A → B) ⇒ (C → D) ⊣ Γₑ

  Γᵢ,α,X:=α ⊢ c : A ⇒ B ⊣ Γₑ,α,X:=α
  ------------------------------------ (α fresh)
  Γᵢ ⊢̂ ∀X.c : ∀X.A ⇒ ∀X.B ⊣ Γₑ

# Conversion Typing

  Γᵢ ⊢ A   Γₑ ⊢ A
  ---------------------
  Γᵢ ⊢ id(A) : A ⇒ A ⊣ Γₑ

  Γ₁ ⊢̂ ĉ : A ⇒ B ⊣ Γ₂   Γ₂ ⊢ c : B ⇒ C ⊣ Γ₃
  ---------------------------------------------
  Γ₁ ⊢ ĉ ∷ c : A ⇒ C ⊣ Γ₃

# Conversion Composition

  Suppose:
    Γ₁ ⊢ c : A ⇒ B ⊣ Γ₂
    Γ₂ ⊢ d : B ⇒ C ⊣ Γ₃
    NF(c)
    NF(d).

## Conversion normal forms

Adjacent heads fuse as follows:

  fuseΓ(-X,+X)             = []
  fuseΓ(+X,-X)             = []
  fuseΓ(c₁→d₁,c₂→d₂)       = [(c₂ ⨟ c₁) → (d₁ ⨟ d₂)]
  fuseΓ(∀X.c,∀X.d)         = [∀X.(c ⨟ d)]
  fuseΓ(ĉ,ḓ)               undefined otherwise.

The cancellation clauses use the conversion-typing derivations at that
position.  In particular, `-X,+X` has equal non-`X` endpoints and
`+X,-X` has equal `X` endpoints.

A conversion is in normal form if every conversion inside a `→` or `∀`
head is normal and `fuseΓ` is undefined on every adjacent pair of heads:

  NF(id(A))

  NF(c)   NF-head(ĉ)   no head ḓ of c makes fuseΓ(ĉ,ḓ) defined
  ------------------------------------------------------------
  NF(ĉ ∷ c).

Here `NF-head(c→d)` means `NF(c)` and `NF(d)`;
`NF-head(∀X.c)` means `NF(c)`; and `NF-head(+X)` and `NF-head(-X)`
always hold.

## `reduce`

Strip and rebuild the list terminator by

  heads(id(A)) = []                 target(id(A)) = A
  heads(ĉ ∷ c) = ĉ :: heads(c)      target(ĉ ∷ c) = target(c)

  attach([],A)      = id(A)
  attach(ĉ::w,A)    = ĉ ∷ attach(w,A).

`contractΓ(w) = scanΓ([],w)`, where the first argument of `scanΓ` is a
reversed, reduced prefix:

  scanΓ(s,[]) = reverse(s)

  scanΓ([],ĉ::w) = scanΓ([ĉ],w)

  scanΓ(ĉ::s,ḓ::w) = scanΓ(ḓ::ĉ::s,w)
    if fuseΓ(ĉ,ḓ) is undefined

  scanΓ(ĉ::s,ḓ::w) = scanΓ(s,w)
    if fuseΓ(ĉ,ḓ) = []

  scanΓ(ĉ::s,ḓ::w) = scanΓ(s,r::w)
    if fuseΓ(ĉ,ḓ) = [r].

Then composition of two normal conversions is

  reduceΓ(c,d)
    = attach(contractΓ(heads(c) ++ heads(d)),target(d))

  Γ ⊢ c ⨟ d = reduceΓ(c,d).

Because `c` and `d` are normal, the first contraction, if any, is at
their seam.  The last clause checks a fused head against its new left
neighbor.  For example,

  contractΓ([+X,+Y,-Y,-X])
    = scanΓ([],[+X,+Y,-Y,-X])
    = scanΓ([+X],[+Y,-Y,-X])
    = scanΓ([+Y,+X],[-Y,-X])
    = scanΓ([+X],[-X])
    = scanΓ([],[])
    = [].

The recursive calls inside `fuseΓ` are on proper structural children;
every successful fusion shortens the unprocessed conversion path.

## Normal-form builders

The conversion-building operations have the following contracts:

  if +X(A) = c, then NF(c)
  if -X(A) = c, then NF(c)
  NF(id(A))
  if NF(c) and +X(c) = d, then NF(d)
  if NF(c) and -X(c) = d, then NF(d)
  if NF(c), NF(d), and c ⨟ d = e, then NF(e).

The conversion-directed builders use `⨟` at each list seam, so
cancellation is restored immediately.

## Associativity

The head-list seam lemma is

  contractΓ(contractΓ(w₁ ++ w₂) ++ w₃)
    = contractΓ(w₁ ++ contractΓ(w₂ ++ w₃)).

Therefore both associations of `⨟` normalize the same word:

  Γ ⊢ (c ⨟ d) ⨟ e = c ⨟ (d ⨟ e).

For example,

  (-Y ∷ id(Y)) ⨟ (+Y ∷ -X ∷ id(X))
    = -X ∷ id(X).

Thus associativity is computation, not an additional term equivalence.

## Conversion views

For normal, well-typed conversions at function and universal types:

  arr(id(A → B)) = (id(A),id(B))
  arr((c → d) ∷ id(C → D)) = (c,d)

  all(id(∀X.A)) = id(A)
  all((∀X.c) ∷ id(∀X.B)) = c.

Typing and normality ensure that these are the only cases.  Thus `arr` and
`all` are total on their respective typed inputs.

## Composition totality

If

  Γ₁ ⊢ c : A ⇒ B ⊣ Γ₂
  Γ₂ ⊢ d : B ⇒ C ⊣ Γ₃
  NF(c)
  NF(d)

then there is a unique `e` such that

  Γ₁ ⊢ c ⨟ d = e
  NF(e)
  Γ₁ ⊢ e : A ⇒ C ⊣ Γ₃.

# Scope-change transition   Γ ⊢ χ ⇒ Γ′

  ---------
  Γ ⊢ ∅ ⇒ Γ

  Γ ∌ X   Γ ∋ α   Γ ∌ _:=α
  -----------------------------------
  Γ ⊢ +X:=α ⇒ Γ,X:=α

  Γ ▷ X:=α
  -----------------------------------
  Γ ⊢ -X:=α ⇒ (-X:=α)(Γ)

  Γ ⊢ χ₁ ⇒ Γ₁   Γ₁ ⊢ χ₂ ⇒ Γ₂
  ------------------------------
  Γ ⊢ χ₁ ; χ₂ ⇒ Γ₂

Thus unmatched reveals are allowed, but every conceal removes the latest
visible source name:

  α ⊢ +X:=α ⇒ α,X:=α

  α,X:=α,β,Y:=β
    ⊢ (-Y:=β) ; (-X:=α) ⇒ α,β.

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
            
  (Bndry)   Γ ⊢ Θ   Γ++Θ ⊢ χ ⇒ Γᵢ   NF(c)
            Γᵢ ⊢ M : A
            Γᵢ ⊢ c : A ⇒ B ⊣ Γ
            ----------------------
            Γ ⊢ νΘ,χ[M|c] : B

# Values

  Vˢ,Wˢ ::= k | λx:A.N | Λα,X.V
  V,W ::= Vˢ | νθ,χ[Vˢ|c]
    where NF(c) and arr(c), all(c), or a type-variable target applies

# Term-variable substitution   N[x := M : A]

  x[x:=V:A]             = V
  y[x:=V:A]             = y                             (y ≠ x)
  k[x:=V:A]             = k
  (M₁ ⊕ M₂)[x:=V : A]   = M₁[x:=V:A] ⊕ M₂[x:=V:A]
  (L · M)[x:=V:A]       = L[x:=V:A] · M[x:=V:A]
  (λx:B. N)[x:=V:A]     = λx:B. N                       (shadow)
  (λy:B. N)[x:=V:A]     = λy:B. N[x:=V:A]               (y ≠ x)
  (Λα,X. N)[x:=V:A]     = Λα,X. N[x:= ν∅,-X:=α[V|id(A)] ]
  (L @B[C])[x:=V:A]     = L[x:=V:A] @B[C]
  νΘ,χ[M|c] [x:=V]      = νΘ,χ[M|c]                     (skip M)

# Reduction Rules

Reduction is indexed by the ambient context so that type application can
store `⌊A⌋Γ`.  Write `Γ ⊢ M -→ N`, omitting `Γ ⊢` when it is clear.

  (Beta)      Γ ⊢ (λx:A. N) · W  -→ N[x:=W:A]
  (PrimBeta)  Γ ⊢ n₁ ⊕ n₂        -→ n₁ ⟦⊕⟧ n₂
  (TyBeta)    Γ ⊢ (Λα,X.V) •B[A]
              -→ να:=⌊A⌋Γ,+X:=α[ V | +X(B)]
  (Wrap)      Γ ⊢ νΘ,χ[ V |c] · W
              -→ νΘ,χ[ V · ν∅,-χ[W|c₁] |c₂]
              if arr(c) = (c₁,c₂)
  (TyWrap)    Γ ⊢ νΘ,χ[ Λα,X.V |c] •B[A]
              -→ ν(Θ,α:=⌊A⌋Γ),(χ ; (+X:=α))[ V |+X(d)]
              if all(c) = d
  (Merge)     Γ ⊢ νΘ₁,χ₁[ νΘ₂,χ₂[ V |c] |d]
              -→ ν(Θ₁++Θ₂),(χ₁;χ₂)[ V |c⨟d]
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
Constant literals cannot receive the focus.  Consumed nodes have no
descendant.  Write `Γ ⊢ C[M] ⇝[rs]* D[N]` for the reflexive, transitive
closure along `rs`.

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

  Γ ⊢ ((νΘ,χ[C[M] | c]) · W)
    ⇝[Wrap]
  νΘ,χ[C[M] · ν∅,-χ[W | c₁] | c₂]
    if arr(c) = (c₁,c₂)

  Γ ⊢ ((νΘ,χ[V | c]) · C[M])
    ⇝[Wrap]
  νΘ,χ[V · ν∅,-χ[C[M] | c₁] | c₂]
    if arr(c) = (c₁,c₂)

  Γ ⊢ ((Λα,X. C[M]) •B[A])
    ⇝[TyBeta]
  να:=⌊A⌋Γ,+X:=α[C[M] | +X(B)]

  Γ ⊢ ((νΘ,χ[Λα,X. C[M] | c]) •B[A])
    ⇝[TyWrap]
  ν(Θ,α:=⌊A⌋Γ),(χ ; (+X:=α))[C[M] | +X(d)]
    if all(c) = d

  Γ ⊢ νΘ₁,χ₁[νΘ₂,χ₂[C[M] | c] | d]
    ⇝[Merge]
  ν(Θ₁++Θ₂),(χ₁ ; χ₂)[C[M] | c⨟d]

Residuals lift through an unchanged surrounding context:

  Γ′ ⊢ C[M] ⇝[r] D[N]
  Γ ⊢ E ⊣ Γ′
  -------------------------
  Γ ⊢ E[C[M]] ⇝[r] E[D[N]]

There is no clause focusing the application introduced by `Wrap`, or any
other source-shaped node introduced by reduction.

Color preservation states that if

  M is a non-literal source node
  ∅ ⊢ C[M] : A
  ∅ ⊢ C[M] -→* D[N]               by rs
  ∅ ⊢ C[M] ⇝[rs]* D[N]
  ∅ ⊢ C ⊣ Γ₁
  ∅ ⊢ D ⊣ Γ₂

then

  color(Γ₁) = color(Γ₂).

## Scope-change preservation

If `Γ ok` and `Γ ⊢ χ ⇒ Γ′`, then `Γ′ ok`.

## Representation soundness

If `Γ ok` and `Γ ⊢ A`, then

  Γ ⊢ᴿ ⌊A⌋Γ

and

  Γ ⊢ ⌊A⌋Γ ⇓ A.


# Examples

## `Examples.agda` §6: polymorphic identity

  ((Λα,X. λx:X.x) •(X→X)[ℕ]) · 7
  -→⟨ ξ-·-l TyBeta ⟩
  (να:=ℕ,+X:=α[
     λx:X.x
   | ((-X ∷ id(X)) → (+X ∷ id(ℕ))) ∷ id(ℕ→ℕ)]) · 7
  -→⟨ Wrap ⟩
  να:=ℕ,+X:=α[
    (λx:X.x) · ν∅,-X:=α[7 | -X ∷ id(X)]
  | +X ∷ id(ℕ)]
  -→⟨ ξ-ν Beta ⟩
  να:=ℕ,+X:=α[
    ν∅,-X:=α[7 | -X ∷ id(X)]
  | +X ∷ id(ℕ)]
  -→⟨ Merge; (-X ∷ id(X)) ⨟ (+X ∷ id(ℕ)) = id(ℕ) ⟩
  να:=ℕ,((+X:=α) ; (-X:=α))[7 | id(ℕ)]
  -→⟨ Const ⟩
  7.

The merged scope change is admitted by

  α:=ℕ ⊢ +X:=α ⇒ α:=ℕ,X:=α
  α:=ℕ,X:=α ⊢ -X:=α ⇒ α:=ℕ

and hence

  α:=ℕ ⊢ (+X:=α) ; (-X:=α) ⇒ α:=ℕ.

Preservation:

  step       redex type   reduct type
  -----------------------------------
  TyBeta     ℕ             ℕ
  Wrap       ℕ             ℕ
  Beta       ℕ             ℕ
  Merge      ℕ             ℕ
  Const      ℕ             ℕ

Color preservation for non-literal source nodes:

  step       descendants
  --------------------------------------------------
  TyBeta     application: ∅→∅;  λ and x: {X}→{X}
  Wrap       λ and x: {X}→{X};  application consumed
  Beta       λ and x consumed
  Merge      none
  Const      none

The application introduced by `Wrap` and the literal `7` are untracked.
The literal's colors are

  ∅ → ∅ → ∅ → ∅ → ∅ → ∅.

Thus the example also preserves its literal's color, though this is not
required.

## `Examples.agda` §14: polymorphic argument under `Λ`

  ((Λα,X.
      λf:∀Z.Z→Z. Λβ,Y. f •(Z→Z)[Y])
    •((∀Z.Z→Z)→(∀Y.Y→Y))[ℕ])
  · (Λγ,Z. λz:Z.z)
  -→⟨ ξ-·-l TyBeta ⟩
  (να:=ℕ,+X:=α[
     λf:∀Z.Z→Z. Λβ,Y. f •(Z→Z)[Y]
   | id((∀Z.Z→Z) → (∀Y.Y→Y))])
  · (Λγ,Z. λz:Z.z)
  -→⟨ Wrap ⟩
  να:=ℕ,+X:=α[
    (λf:∀Z.Z→Z. Λβ,Y. f •(Z→Z)[Y])
      · ν∅,-X:=α[Λγ,Z. λz:Z.z | id(∀Z.Z→Z)]
  | id(∀Y.Y→Y)]
  -→⟨ ξ-ν Beta ⟩
  να:=ℕ,+X:=α[
    Λβ,Y.
      (ν∅,-Y:=β[
         ν∅,-X:=α[Λγ,Z. λz:Z.z | id(∀Z.Z→Z)]
       | id(∀Z.Z→Z)]) •(Z→Z)[Y]
  | id(∀Y.Y→Y)]
  -→⟨ ξ-ν (ξ-Λ (ξ-• Merge)) ⟩
  να:=ℕ,+X:=α[
    Λβ,Y.
      (ν∅,((-Y:=β) ; (-X:=α))[
         Λγ,Z. λz:Z.z | id(∀Z.Z→Z)]) •(Z→Z)[Y]
  | id(∀Y.Y→Y)]
  -→⟨ ξ-ν (ξ-Λ TyWrap) ⟩
  να:=ℕ,+X:=α[
    Λβ,Y.
      νγ:=β,(((-Y:=β) ; (-X:=α)) ; (+Z:=γ))[
        λz:Z.z
      | ((-Z ∷ id(Z)) → (+Z ∷ id(Y))) ∷ id(Y→Y)]
  | id(∀Y.Y→Y)].

Before `Merge`, the crossed argument follows

  α:=ℕ,X:=α,β,Y:=β ⊢ -Y:=β ⇒ α:=ℕ,X:=α,β
  α:=ℕ,X:=α,β ⊢ -X:=α ⇒ α:=ℕ,β.

Hence the composed boundary is admitted:

  α:=ℕ,X:=α,β,Y:=β
    ⊢ (-Y:=β) ; (-X:=α) ⇒ α:=ℕ,β.

At `TyWrap`,

  ⌊Y⌋(α:=ℕ,X:=α,β,Y:=β) = β.

Its scope transition is

  α:=ℕ,X:=α,β,Y:=β,γ:=β
    ⊢ ((-Y:=β) ; (-X:=α)) ; (+Z:=γ)
    ⇒ α:=ℕ,β,γ:=β,Z:=γ.

Checks:

  step       redex type   reduct type
  ---------------------------------------
  TyBeta     ∀Y.Y→Y        ∀Y.Y→Y
  Wrap       ∀Y.Y→Y        ∀Y.Y→Y
  Beta       ∀Y.Y→Y        ∀Y.Y→Y
  Merge      ∀Y.Y→Y        ∀Y.Y→Y
  TyWrap     ∀Y.Y→Y        ∀Y.Y→Y

Tracked colors:

  step       descendants
  ---------------------------------------------------------------------
  TyBeta     λf and ΛY: {X}→{X}; f and its type application: {X,Y}→{X,Y}
  Wrap       λf: {X}→{X}; ΛZ: ∅→∅; λz and z: {Z}→{Z}
  Beta       ΛY: {X}→{X}; f's type application: {X,Y}→{X,Y};
             ΛZ: ∅→∅; λz and z: {Z}→{Z}
  Merge      ΛZ: ∅→∅; λz and z: {Z}→{Z}
  TyWrap     λz and z: {Z}→{Z}; ΛZ and its type application consumed.

Thus every step preserves the type and all tracked colors.

## Cross-name composition and cancellation

Write

  χ  = (-Y:=α) ; (+X:=β)
  χ̄  = (-X:=β) ; (+Y:=α) = -χ
  p  = +X ∷ -Y ∷ id(Y)
  q  = +Y ∷ -X ∷ id(X)
  p⇒ = (p → id(ℕ)) ∷ id(X→ℕ)
  q⇒ = (q → id(ℕ)) ∷ id(Y→ℕ)
  m  = (p⇒ → q⇒) ∷ id((Y→ℕ)→(Y→ℕ))
  r  = ((-Y ∷ id(Y)) → id(ℕ)) ∷ id(ℕ→ℕ)
  s  = (
         (((+X ∷ id(ℕ)) → id(ℕ)) ∷ id(X→ℕ))
         →
         (((-X ∷ id(X)) → id(ℕ)) ∷ id(ℕ→ℕ))
       ) ∷ id((ℕ→ℕ)→(ℕ→ℕ))
  t  = (
         (((-Y ∷ id(Y)) → id(ℕ)) ∷ id(ℕ→ℕ))
         →
         (((+Y ∷ id(ℕ)) → id(ℕ)) ∷ id(Y→ℕ))
       ) ∷ id((Y→ℕ)→(Y→ℕ))
  o  = (t → r) ∷ id(((ℕ→ℕ)→(ℕ→ℕ))→(ℕ→ℕ)).

The source term is closed and has type `ℕ`:

  (
    ((Λα,Y.
        λk:((Y→ℕ)→(Y→ℕ)).
          k · (λy:Y. 0))
      •(((Y→ℕ)→(Y→ℕ))→(Y→ℕ))[ℕ])
    ·
    ((Λβ,X.
        λf:X→ℕ. λx:X. f · x)
      •((X→ℕ)→(X→ℕ))[ℕ])
  )
  · 5
  -→⟨ ξ-·-l (ξ-·-l TyBeta) ⟩
  (
    (να:=ℕ,+Y:=α[
       λk:((Y→ℕ)→(Y→ℕ)). k · (λy:Y. 0)
     | o])
    ·
    ((Λβ,X. λf:X→ℕ. λx:X. f · x)
      •((X→ℕ)→(X→ℕ))[ℕ])
  )
  · 5
  -→⟨ ξ-·-l (ξ-·-r TyBeta) ⟩
  (
    (να:=ℕ,+Y:=α[
       λk:((Y→ℕ)→(Y→ℕ)). k · (λy:Y. 0)
     | o])
    ·
    νβ:=ℕ,+X:=β[
      λf:X→ℕ. λx:X. f · x
    | s]
  )
  · 5
  -→⟨ ξ-·-l Wrap ⟩
  να:=ℕ,+Y:=α[
    (λk:((Y→ℕ)→(Y→ℕ)). k · (λy:Y. 0))
    ·
    ν∅,-Y:=α[
      νβ:=ℕ,+X:=β[
        λf:X→ℕ. λx:X. f · x
      | s]
    | t]
  | r]
  · 5
  -→⟨ ξ-·-l (ξ-ν (ξ-·-r Merge)) ⟩
  να:=ℕ,+Y:=α[
    (λk:((Y→ℕ)→(Y→ℕ)). k · (λy:Y. 0))
    ·
    νβ:=ℕ,χ[
      λf:X→ℕ. λx:X. f · x
    | m]
  | r]
  · 5
  -→⟨ ξ-·-l (ξ-ν Beta) ⟩
  να:=ℕ,+Y:=α[
    νβ:=ℕ,χ[
      λf:X→ℕ. λx:X. f · x
    | m]
    · (λy:Y. 0)
  | r]
  · 5
  -→⟨ ξ-·-l (ξ-ν Wrap) ⟩
  να:=ℕ,+Y:=α[
    νβ:=ℕ,χ[
      (λf:X→ℕ. λx:X. f · x)
      · ν∅,χ̄[λy:Y. 0 | p⇒]
    | q⇒]
  | r]
  · 5
  -→⟨ ξ-·-l (ξ-ν (ξ-ν Beta)) ⟩
  να:=ℕ,+Y:=α[
    νβ:=ℕ,χ[
      λx:X. (ν∅,χ̄[λy:Y. 0 | p⇒]) · x
    | q⇒]
  | r]
  · 5
  -→⟨ Wrap ⟩
  να:=ℕ,+Y:=α[
    νβ:=ℕ,χ[
      λx:X. (ν∅,χ̄[λy:Y. 0 | p⇒]) · x
    | q⇒]
    · ν∅,-Y:=α[5 | -Y ∷ id(Y)]
  | id(ℕ)]
  -→⟨ ξ-ν Wrap ⟩
  να:=ℕ,+Y:=α[
    νβ:=ℕ,χ[
      (λx:X. (ν∅,χ̄[λy:Y. 0 | p⇒]) · x)
      · ν∅,χ̄[ν∅,-Y:=α[5 | -Y ∷ id(Y)] | q]
    | id(ℕ)]
  | id(ℕ)]
  -→⟨ ξ-ν (ξ-ν (ξ-·-r Merge)) ⟩
  να:=ℕ,+Y:=α[
    νβ:=ℕ,χ[
      (λx:X. (ν∅,χ̄[λy:Y. 0 | p⇒]) · x)
      · ν∅,(χ̄ ; (-Y:=α))[5 | -X ∷ id(X)]
    | id(ℕ)]
  | id(ℕ)]
  -→⟨ ξ-ν (ξ-ν Beta) ⟩
  να:=ℕ,+Y:=α[
    νβ:=ℕ,χ[
      (ν∅,χ̄[λy:Y. 0 | p⇒])
      · ν∅,(χ̄ ; (-Y:=α))[5 | -X ∷ id(X)]
    | id(ℕ)]
  | id(ℕ)]
  -→⟨ ξ-ν (ξ-ν Wrap) ⟩
  να:=ℕ,+Y:=α[
    νβ:=ℕ,χ[
      ν∅,χ̄[
        (λy:Y. 0)
        · ν∅,χ[ν∅,(χ̄ ; (-Y:=α))[5 | -X ∷ id(X)] | p]
      | id(ℕ)]
    | id(ℕ)]
  | id(ℕ)]
  -→⟨ ξ-ν (ξ-ν (ξ-ν (ξ-·-r Merge))) ⟩
  να:=ℕ,+Y:=α[
    νβ:=ℕ,χ[
      ν∅,χ̄[
        (λy:Y. 0)
        · ν∅,(χ ; χ̄ ; (-Y:=α))[5 | -Y ∷ id(Y)]
      | id(ℕ)]
    | id(ℕ)]
  | id(ℕ)]
  -→⟨ ξ-ν (ξ-ν (ξ-ν Beta)) ⟩
  να:=ℕ,+Y:=α[
    νβ:=ℕ,χ[
      ν∅,χ̄[0 | id(ℕ)]
    | id(ℕ)]
  | id(ℕ)]
  -→⟨ ξ-ν (ξ-ν Const) ⟩
  να:=ℕ,+Y:=α[
    νβ:=ℕ,χ[0 | id(ℕ)]
  | id(ℕ)]
  -→⟨ ξ-ν Const ⟩
  να:=ℕ,+Y:=α[0 | id(ℕ)]
  -→⟨ Const ⟩
  0.

The two later merges normalize by associativity and cancellation:

  (-Y ∷ id(Y)) ⨟ q = -X ∷ id(X)
  (-X ∷ id(X)) ⨟ p = -Y ∷ id(Y).

Preservation and color preservation:

  nodes          color while retained       consumed by
  -------------------------------------------------------
  λk, k·(λy.0)   {Y}                        Beta, Wrap
  λf, λx, f·x    {X}                        Beta, Beta, Wrap
  λy             {Y}                        Beta

Every term in the trace has type `ℕ`.  Constant colors are untracked.
