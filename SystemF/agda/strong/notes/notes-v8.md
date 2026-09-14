# Changes from v7 (DRAFT)

Version 8 makes the conversion the single source of truth for scope
crossings.

1. The boundary loses its scope-change component: `νΘ,χ[M|c]` becomes
   `νΘ[M|c]`.  The crossings that `χ` performed become conversion
   ELEMENTS: `id{+X:=α}` and `id{-X:=α}` cross a reveal or a conceal
   without changing the type, alongside the renaming elements, which now
   also carry their anchor: `+X:=α` (unseal) and `-X:=α` (seal).
2. Conversion typing is EXACT.  `id(A)` is strictly reflexive (one
   context, one type).  Each element connects two contexts that differ in
   exactly the crossing it performs; `→` and `∀` elements delegate their
   crossing to their component conversions.  Consequently a conversion's
   interior context is a function of its syntax and its exterior context
   (`⟨c⟩(Γ)` below), which is what replaces `χ` in the `(Bndry)` and
   `(ξ-ν)` rules.
3. Contexts merge each anchor's data into ONE entry that is either
   concealed (`α:=R`, `α`) or revealed with a source name (`X:α:=R`,
   `X:α`).  A reveal or conceal flips an entry in place; it never adds or
   removes one.  Anchor freshness and name uniqueness become structural.
4. The dual operation `-χ`, the scope-change action `χ(Γ)`, the
   transition `Γ ⊢ χ ⇒ Γ′`, and the rightmost-visible judgment `Γ ▷ X:=α`
   are deleted.  With `▷` goes v7's bracketing discipline (a conceal
   removes the latest visible name): crossings under `∀`-descents always
   violated it, and it is no longer enforced by typing.  If bracketing is
   wanted, it returns as a THEOREM about the conversions the builders and
   the reduction rules produce, not as a typing restriction.
5. The reduction rules stop doing scope bookkeeping: `Merge` appends
   conversions and nothing else; `Wrap` needs no dual scope, because the
   contravariant `arr` component carries the dual crossings; `TyBeta` and
   `TyWrap` need no separate scope component, because `+X(·)` emits the
   crossing.
6. `fuse` gains cancellation rows for the crossing elements, and the view
   functions `arr`/`all` gain clauses that carry an identity crossing
   element into the components.

Motivation: under v7's rules the crossing information lived in two
places, and the typed coherence between them could not survive the
operations that rearrange conversion syntax.  Machine-checked failures:
`notes/old/probes-pre-merge/V7MergeScopeClashProbe.agda` (`Merge` strands
the crossings a bridging `id` performed) and
`notes/probes/V7CancelDriftProbe.agda` (cancelling a `seal/unseal` pair
strands the visibility drift its flanks absorbed).  Both configurations
become regression tests for v8.

# Design Criteria

Color Preservation: The set of type variables in scope (the "color")
at every subterm from the source program is invariant under reduction
(not including the runtime terms: conversions and scope boundaries,
runtime-created terms, or constant literals).

Progress: Every closed, well-typed term is a value or can take a reduction step.

Preservation: A reduction step preserves the type of a closed term.

Determinism: Every term has at most one immediate reduct.

Single source of crossings: every change of visibility between a
boundary's interior and exterior is performed by exactly one conversion
element, so the operations that rearrange conversions (`⨟`, `fuse`, the
reduction rules) preserve the crossing structure by construction.

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

# Contexts and variable lookup

Each anchor owns ONE context entry, concealed or revealed:

  Γ ::= ∅ | Γ,α | Γ,α:=R | Γ,X:α | Γ,X:α:=R | Γ,x:A

`α:=R` is a concealed represented anchor and `α` a concealed abstract
one; `X:α:=R` and `X:α` are the same entries revealed, carrying the
source name `X`.  A reveal or conceal FLIPS an entry in place.  The
spine of a context is the entry list with visibility and names erased;
every judgment below relates contexts only through equal spines.

Write `ty(Γ)` for the type-only projection (drop the `x:A` entries).

  ------------
  | Γ ∋ X:=α |
  ------------

Only a revealed entry has a name.

  -------------------          -----------------
  (Γ,X:α:=R) ∋ X:=α            (Γ,X:α) ∋ X:=α

  Γ ∋ X:=α                     Γ ∋ X:=α
  ------------------- (X ≠ Y)  ----------------- (X ≠ Y)
  (Γ,Y:β:=S) ∋ X:=α            (Γ,Y:β) ∋ X:=α

  Γ ∋ X:=α                     Γ ∋ X:=α         Γ ∋ X:=α
  ---------------              ------------     ------------
  (Γ,β:=S) ∋ X:=α              (Γ,β) ∋ X:=α     (Γ,x:A) ∋ X:=α

  ---------
  | Γ ∋ α |
  ---------

Every entry form containing `α` (concealed or revealed) matches; all
other entries are skipped.  Similarly `Γ ∋ α:=R` looks up the
representation regardless of visibility.

# Anchor representation of a source type

Write `⌊A⌋Γ` for the representation of `A` in `Γ`.

  ⌊X⌋Γ       = α                         if Γ ∋ X:=α
  ⌊ι⌋Γ       = ι
  ⌊A → B⌋Γ   = ⌊A⌋Γ → ⌊B⌋Γ
  ⌊∀X.A⌋Γ    = ∀α.⌊A⌋(Γ,X:α)             (α fresh)

The last equation is defined up to renaming its bound anchor.

# Reading a representation type

The judgment `Γ ⊢ R ⇓ A` reads anchors through the source names visible
in `Γ`.

  Γ ∋ X:=α
  ---------
  Γ ⊢ α ⇓ X

  ---------
  Γ ⊢ ι ⇓ ι

  Γ ⊢ R ⇓ A   Γ ⊢ S ⇓ B
  ---------------------
  Γ ⊢ R → S ⇓ A → B

  Γ,X:α ⊢ R ⇓ A
  ------------------ (α and X fresh)
  Γ ⊢ ∀α.R ⇓ ∀X.A

# Well-formed Types   Γ ⊢ A

  (wf-ℕ)      Γ ⊢ ℕ

  (wf-𝔹)      Γ ⊢ 𝔹

  (wf-tvar)   Γ ∋ X:=α
              --------
              Γ ⊢ X

  (wf-fun)    Γ ⊢ A    Γ ⊢ B
              --------------
              Γ ⊢ A → B

  (wf-all)    X ∉ Γ  α ∉ Γ  Γ,X:α ⊢ A
              -----------------------
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

Merged entries make name uniqueness structural: an anchor carries at
most one name because a name is part of its entry.

  ----
  ∅ ok

  Γ ok   α ∉ Γ                Γ ok  Γ ⊢ᴿ R  α ∉ Γ
  ------------                -------------------
  Γ,α ok                      Γ,α:=R ok

  Γ ok   α ∉ Γ   X ∉ Γ        Γ ok  Γ ⊢ᴿ R  α ∉ Γ  X ∉ Γ
  --------------------        --------------------------
  Γ,X:α ok                    Γ,X:α:=R ok

  Γ ok  Γ ⊢ A
  -----------
  Γ,x:A ok

# Conversions

  ĉ,ḓ ::= +X:=α | -X:=α | id{+X:=α} | id{-X:=α} | c → d | ∀X.c
  c,d ::= id(A) | ĉ ∷ c

The four atomic elements all cross the visibility of one anchor; they
differ in whether the crossing renames the type:

  -X:=α      : SEAL: crosses α's reveal outward, `A ⇒ X`, reading α's
               representation on the concealed side.
  +X:=α      : UNSEAL: crosses α's conceal outward, `X ⇒ A`.
  id{-X:=α}  : identity conceal crossing: the same crossing as `-X:=α`
               with the type unchanged.  As a boundary element it
               conceals `X` inward — v7's scope change `-X:=α`,
               relocated into the conversion.
  id{+X:=α}  : identity reveal crossing: the same crossing as `+X:=α`
               with the type unchanged (the type must not mention `X`).

The ANCHOR is the operative datum of every atomic element, and the
syntax carries it: `fuse` decides cancellation by anchor equality (in
the `+X:=α ∷ -Y:=β` order the seam context is the concealed side, where
names do not exist, and equal names at the two outer contexts need not
mean equal anchors), the interior walk `⟨c⟩` identifies the entry to
flip by its anchor, and anchors are the coordinate that weakening
shifts uniformly.  In the mechanization the constructors carry ONLY the
anchor (`seal α`, `unseal α`, `hide α`, `show α`); the de Bruijn name is
recomputed as a reveal-count wherever a rule needs it.

# Conversion-element Typing

Each rule's two contexts share a spine and differ in EXACTLY the entry
the element crosses.  Below, `Γ[α]` and `Γ[X:α]` display α's entry
concealed and revealed; the rest of the context is unchanged between the
two sides of a rule.

  Γₑ[X:α] ∋ α:=R   Γᵢ[α] ⊢ R ⇓ A
  ------------------------------------
  Γᵢ[α] ⊢̂ -X:=α : A ⇒ X ⊣ Γₑ[X:α]

  Γᵢ[X:α] ∋ α:=R   Γₑ[α] ⊢ R ⇓ A
  ------------------------------------
  Γᵢ[X:α] ⊢̂ +X:=α : X ⇒ A ⊣ Γₑ[α]

  Γᵢ[α] ⊢ A   (X fresh for Γᵢ[α])
  ------------------------------------
  Γᵢ[α] ⊢̂ id{-X:=α} : A ⇒ A ⊣ Γₑ[X:α]

  Γₑ[α] ⊢ A
  ------------------------------------
  Γᵢ[X:α] ⊢̂ id{+X:=α} : A ⇒ A ⊣ Γₑ[α]

Well-formedness of `A` on the concealed side is what enforces `X ∉ A`
for the identity crossings.

The structural elements delegate their crossing to their components:

  Γₑ ⊢ c : C ⇒ A ⊣ Γᵢ    Γᵢ ⊢ d : B ⇒ D ⊣ Γₑ
  ------------------------------------------
  Γᵢ ⊢̂ c → d : (A → B) ⇒ (C → D) ⊣ Γₑ

  Γᵢ,X:α ⊢ c : A ⇒ B ⊣ Γₑ,X:α
  ------------------------------------ (α fresh)
  Γᵢ ⊢̂ ∀X.c : ∀X.A ⇒ ∀X.B ⊣ Γₑ

# Conversion Typing

The terminator is strictly reflexive; all context movement is in the
elements.

  Γ ⊢ A
  ---------------------
  Γ ⊢ id(A) : A ⇒ A ⊣ Γ

  Γ₁ ⊢̂ ĉ : A ⇒ B ⊣ Γ₂   Γ₂ ⊢ c : B ⇒ C ⊣ Γ₃
  ---------------------------------------------
  Γ₁ ⊢ ĉ ∷ c : A ⇒ C ⊣ Γ₃

# Crossings of a conversion

`⟨c⟩(Γ)` computes a conversion's interior context from its exterior
context, replacing the deleted `χ(Γ)`.  It walks the elements from the
terminator inward, undoing each element's crossing:

  ⟨id(A)⟩(Γ)     = Γ
  ⟨ĉ ∷ c⟩(Γ)     = ⟨ĉ⟩̂(⟨c⟩(Γ))

  ⟨-X:=α⟩̂(Γ[X:α]) = Γ[α]         ⟨id{-X:=α}⟩̂(Γ[X:α]) = Γ[α]
  ⟨+X:=α⟩̂(Γ[α])   = Γ[X:α]       ⟨id{+X:=α}⟩̂(Γ[α])   = Γ[X:α]
  ⟨c → d⟩̂(Γ)     = ⟨d⟩(Γ)
  ⟨∀X.c⟩̂(Γ)      = Γ′             if ⟨c⟩(Γ,X:α) = Γ′,X:α

The `+` clauses restore the name the element carries, so the walk is
fully syntax-directed; on well-typed conversions `⟨c⟩` and the typing
agree:

  if Γᵢ ⊢ c : A ⇒ B ⊣ Γₑ then ⟨c⟩(Γₑ) = Γᵢ.

# Conversion builders   +X(A), -X(A)

The builders are indexed by the two endpoint contexts.  If an equation
reaches a free occurrence of `X`, its represented type is obtained by

  Γᵥ ∋ X:=α   Γᵥ ∋ α:=R   Γₕ ⊢ R ⇓ S
  ------------------------------------
  Γᵥ ; Γₕ ⊢ repr(X) = S.

Every equation's result crosses α's visibility exactly once at the top
level: a hit crosses with the renaming element, a miss crosses with the
identity crossing element, and a split delegates the crossing to its
components.  The context indices and `S` are suppressed:

  +X(A) = id{+X:=α} ∷ id(A)                        (X ∉ A)
  +X(X) = +X:=α ∷ id(S)
  +X(A → B) = (-X(A) → +X(B)) ∷ id((A → B)[X:=S])  (X ∈ A → B)
  +X(∀Y.A) = (∀Y.+X(A)) ∷ id((∀Y.A)[X:=S])         (X ∈ ∀Y.A, X ≠ Y)

  -X(A) = id{-X:=α} ∷ id(A)                        (X ∉ A)
  -X(X) = -X:=α ∷ id(X)
  -X(A → B) = (+X(A) → -X(B)) ∷ id(A → B)          (X ∈ A → B)
  -X(∀Y.A) = (∀Y.-X(A)) ∷ id(∀Y.A)                 (X ∈ ∀Y.A, X ≠ Y)

The v7 miss equations (`+X(Y)`, `+X(ι)`, `+X(∀X.A)` and duals) are the
instances of the first equation.  Contracts:

  Γᵢ[X:α] ⊢ +X(A) : A ⇒ A[X:=S] ⊣ Γₑ[α]
  Γᵢ[α]   ⊢ -X(A) : A[X:=S] ⇒ A ⊣ Γₑ[X:α]

  -----------------
  | +X(c) = c′ | (reveal X in c)
  | -X(c) = c′ | (conceal X in c)
  -----------------

These operations require `NF(c)` and return a conversion in normal form.

  +X(id(A)) = +X(A)             -X(id(A)) = -X(A)
  +X(ĉ ∷ c) = +X(ĉ) ⨟ +X(c)
  -X(ĉ ∷ c) = -X(ĉ) ⨟ -X(c)

On elements, with `B` the target supplied by the typing derivation of the
transformed element:

  +X(+Y:=β) = +Y:=β ∷ id(B)             -X(+Y:=β) = +Y:=β ∷ id(B)
  +X(-Y:=β) = -Y:=β ∷ id(B)             -X(-Y:=β) = -Y:=β ∷ id(B)
  +X(id{±Y:=β}) = id{±Y:=β} ∷ id(B)     -X(id{±Y:=β}) = id{±Y:=β} ∷ id(B)
  +X(c → d) = (-X(c) → +X(d)) ∷ id(B)
  -X(c → d) = (+X(c) → -X(d)) ∷ id(B)
  +X(∀Y.c) = (∀Y.+X(c)) ∷ id(B)  (X ≠ Y)
  -X(∀Y.c) = (∀Y.-X(c)) ∷ id(B)  (X ≠ Y)
  +X(∀X.c) = (∀X.c) ∷ id(B)
  -X(∀X.c) = (∀X.c) ∷ id(B)

# Runtime Terms

  Θ ::= ∅ | Θ,α:=R | Θ,α                (representation bindings)
  L,M,N ::= ... | νΘ[M|c]

We call `νΘ[M|c]` a boundary.  There is no scope component: the
conversion's elements carry the crossings, and the interior context is
`⟨c⟩` of the exterior.

# Conversion Composition

  Suppose:
    Γ₁ ⊢ c : A ⇒ B ⊣ Γ₂
    Γ₂ ⊢ d : B ⇒ C ⊣ Γ₃
    NF(c)
    NF(d).

## Conversion normal forms

Adjacent elements fuse as follows:

  fuse(-X:=α,+X:=α)                 = []
  fuse(+X:=α,-X:=α)                 = []
  fuse(id{-X:=α},id{+X:=α})         = []
  fuse(id{+X:=α},id{-X:=α})         = []
  fuse(c₁→d₁,c₂→d₂)         = [(c₂ ⨟ c₁) → (d₁ ⨟ d₂)]
  fuse(∀X.c,∀X.d)           = [∀X.(c ⨟ d)]
  fuse(ĉ,ḓ)                 undefined otherwise.

Cancellation compares the ANCHORS, which the syntax displays.  A
renaming element against the opposite identity crossing does not fuse:
`+X:=α ∷ id{-X:=α}` performs a net-zero crossing while renaming
`X ⇒ S ⇒ S`, and stays as it is in normal form.  Identity crossings at
different anchors do not fuse either — commuting one past a seal is not
type-preserving, because the seal's read-back can mention the crossed
anchor.

A conversion is in normal form if every conversion inside a `→` or `∀`
element is normal and `fuse` is undefined on every adjacent pair:

  NF(id(A))

  NF(c)   NF-elt(ĉ)   no element ḓ of c makes fuse(ĉ,ḓ) defined
  ------------------------------------------------------------
  NF(ĉ ∷ c).

`NF-elt` holds always for the four atomic elements, and recursively for
`→` and `∀` elements.

## `reduce`

Unchanged from v7 in structure: strip the elements, `contract` adjacent
pairs by `fuse` with rescanning, reattach the target terminator.

  Γ ⊢ c ⨟ d = reduce(c,d)
    = attach(contract(elts(c) ++ elts(d)), target(d)).

Every successful fusion decreases the total weight of the element list, so
`contract` terminates; the crossing elements have weight 1 like the
renaming elements.

## Normal-form builders

  if +X(A) = c, then NF(c)
  if -X(A) = c, then NF(c)
  NF(id(A))
  if NF(c) and +X(c) = d, then NF(d)
  if NF(c) and -X(c) = d, then NF(d)
  if NF(c), NF(d), and c ⨟ d = e, then NF(e).

## Associativity

  contract(contract(w₁ ++ w₂) ++ w₃)
    = contract(w₁ ++ contract(w₂ ++ w₃))

and hence `(c ⨟ d) ⨟ e = c ⨟ (d ⨟ e)`, as computation.

## Conversion views

`arr` takes the INTERIOR domain from the λ annotation at its use site
(the conversion's syntax does not carry it when the conversion is a bare
`id` or begins with crossing elements).  For κ ranging over the identity
crossing elements, with `κ̄` the dual element
(`id{+X:=α}` ↔ `id{-X:=α}`):

  arr(A₀, id(A → B)) = (id(A), id(B))
  arr(A₀, κ₁ ∷ … ∷ κₙ ∷ (c → d) ∷ id(C → D))
    = (c ⧺ (κ̄ₙ ∷ … ∷ κ̄₁ ∷ id(A₀)), κ₁ ∷ … ∷ κₙ ∷ d)     (n ≥ 0)

  all(id(∀X.A)) = id(A)
  all(κ₁ ∷ … ∷ κₙ ∷ (∀X.c) ∷ id(∀X.B)) = κ₁ ∷ … ∷ κₙ ∷ c  (n ≥ 0)

`arr` peels the crossing prefix in one pass: the contravariant component
re-crosses it in reverse with the dual elements and terminates at the
INTERIOR domain `A₀` — the λ's own annotation, in its own coordinates —
so no renaming is involved; the covariant component keeps the prefix.
Here `_⧺_` is terminator-discarding append.

OPEN (to be settled in the mechanization): whether every reachable
normal boundary conversion at a function or universal target has one of
these shapes.  Renaming elements can in principle stand between identity
crossings in a normal form (`-X:=α ∷ id{-Y:=β} ∷ +X:=α ∷ id(S)` is
normal); the claim
to prove is that such conversions do not reach value boundaries, or else
`arr`/`all` and the `Value` clause must treat them.

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

Because every crossing is a element, the appended element list performs
exactly the crossings of the two derivations in sequence; the v7
counterexamples (a deleted bridging `id`, a cancelled pair with drifted
flanks) cannot be stated.

# Well-formed Θ   Γ ⊢ Θ

  -----
  Γ ⊢ ∅

  Γ ⊢ Θ   Γ++Θ ⊢ᴿ R   α ∉ Γ++Θ
  --------------------------------
  Γ ⊢ Θ,α:=R

  Γ ⊢ Θ   α ∉ Γ++Θ
  -----------------
  Γ ⊢ Θ,α

Store entries enter the context concealed.

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

  (TyLam)   Γ, X:α ⊢ N : A
            -------------------- (α fresh)
            Γ ⊢ Λα,X.N : ∀X.A

  (TyApp)   Γ ⊢ L : ∀X.B   Γ ⊢ A
            --------------------
            Γ ⊢ L •B[A] : B[X:=A]

  (Bndry)   ty(Γ) ⊢ Θ   NF(c)
            ⟨c⟩(ty(Γ)++Θ) = Γᵢ
            Γᵢ ⊢ M : A
            Γᵢ ⊢ c : A ⇒ B ⊣ ty(Γ)++Θ
            ----------------------
            Γ ⊢ νΘ[M|c] : B

The interior context is not a component of the term; it is computed from
the conversion, and it is unique because each element's crossing inverts
uniquely.  A boundary body contains no free term variables from its
exterior.

# Values

  Vˢ,Wˢ ::= k | λx:A.N | Λα,X.V
  V,W ::= Vˢ | νΘ[Vˢ|c]
    where NF(c) and arr(A₀,c), all(c), or a type-variable target applies

# Term-variable substitution   N[x := M : A]

  x[x:=V:A]             = V
  y[x:=V:A]             = y                             (y ≠ x)
  k[x:=V:A]             = k
  (M₁ ⊕ M₂)[x:=V : A]   = M₁[x:=V:A] ⊕ M₂[x:=V:A]
  (L · M)[x:=V:A]       = L[x:=V:A] · M[x:=V:A]
  (λx:B. N)[x:=V:A]     = λx:B. N                       (shadow)
  (λy:B. N)[x:=V:A]     = λy:B. N[x:=V:A]               (y ≠ x)
  (Λα,X. N)[x:=V:A]     = Λα,X. N[x:= ν∅[V | id{-X:=α} ∷ id(A)] ]
  (L •B[C])[x:=V:A]     = L[x:=V:A] •B[C]
  νΘ[M|c] [x:=V]        = νΘ[M|c]                       (skip M)

The `Λ` clause is v7's crossing boundary with the scope component
relocated into the conversion: the value crosses `X`'s reveal with the
identity crossing element, and `A` cannot mention `X` because `V` was
typed outside the `Λ`.

# Reduction Rules

Reduction is indexed by the ambient context so that type application can
store `⌊A⌋Γ`.  Write `Γ ⊢ M -→ N`, omitting `Γ ⊢` when it is clear.

  (Beta)      Γ ⊢ (λx:A. N) · W  -→ N[x:=W:A]
  (PrimBeta)  Γ ⊢ n₁ ⊕ n₂        -→ n₁ ⟦⊕⟧ n₂
  (TyBeta)    Γ ⊢ (Λα,X.V) •B[A]
              -→ να:=⌊A⌋Γ[ V | +X(B) ]
  (Wrap)      Γ ⊢ νΘ[ λx:A₀.N |c] · W
              -→ νΘ[ (λx:A₀.N) · ν∅[W|c₁] |c₂]
              if arr(A₀,c) = (c₁,c₂)
  (TyWrap)    Γ ⊢ νΘ[ Λα,X.V |c] •B[A]
              -→ ν(Θ,α:=⌊A⌋Γ)[ V |+X(d)]
              if all(c) = d
  (Merge)     Γ ⊢ νΘ₁[ νΘ₂[ V |c] |d]
              -→ ν(Θ₁++Θ₂)[ V |c⨟d]
              if νΘ₂[ V |c] is a value
  (Const)     Γ ⊢ νΘ[ k |id(ι)] -→ k

Compare v7: `TyBeta` and `TyWrap` lose their scope components
(the crossing is inside `+X(·)`); `Wrap` loses the dual scope `-χ` (the
contravariant component `c₁` carries the dual crossings); `Merge` loses
the scope concatenation.  `Wrap` matches the body as a λ because `arr`
needs the interior domain.

  (ξ-·-l)   Γ ⊢ L · M -→ L′ · M       if Γ ⊢ L -→ L′
  (ξ-·-r)   Γ ⊢ V · M -→ V · M′       if Γ ⊢ M -→ M′
  (ξ-⊕-l)   Γ ⊢ L ⊕ M -→ L′ ⊕ M       if Γ ⊢ L -→ L′
  (ξ-⊕-r)   Γ ⊢ V ⊕ M -→ V ⊕ M′       if Γ ⊢ M -→ M′
  (ξ-•)     Γ ⊢ L •B[A] -→ L′ •B[A]   if Γ ⊢ L -→ L′
  (ξ-Λ)     Γ ⊢ Λα,X.N -→ Λα,X.N′
              if Γ,X:α ⊢ N -→ N′
  (ξ-ν)     Γ ⊢ νΘ[M|c] -→ νΘ[M′|c]
              if ⟨c⟩(ty(Γ)++Θ) ⊢ M -→ M′

# Theorem Statements

## Progress

If `∅ ⊢ M : A`, then either `Value M` or there exists an `N` such that
`∅ ⊢ M -→ N`.

## Preservation

If `Γ ok`, `ty(Γ) = Γ`, `Γ ⊢ M : A`, and `Γ ⊢ M -→ N`, then `Γ ⊢ N : A`.

## Determinism

If `Γ ok`, `Γ ⊢ M : A`, `Γ ⊢ M -→ N₁`, and `Γ ⊢ M -→ N₂`, then
`N₁ ≡α N₂`.

## Interior well-formedness

Replaces v7's scope-change preservation: if `Γ ok`, `NF(c)`, and
`Γᵢ ⊢ c : A ⇒ B ⊣ Γ`, then `Γᵢ ok` and `⟨c⟩(Γ) = Γᵢ`.

## Color Preservation

As in v7, with the boundary clause of the one-hole-context judgment
computed by `⟨c⟩` instead of `χ`:

  ⟨c⟩(ty(Γ)++Θ) ⊢ C ⊣ Γ′
  ----------------------
  Γ ⊢ νΘ[C | c] ⊣ Γ′

The descendant relation and the statement are otherwise unchanged from
v7.

## Representation soundness

If `Γ ok` and `Γ ⊢ A`, then `Γ ⊢ᴿ ⌊A⌋Γ` and `Γ ⊢ ⌊A⌋Γ ⇓ A`.

# Examples

## Polymorphic identity (v7 Examples §6)

  ((Λα,X. λx:X.x) •(X→X)[ℕ]) · 7
  -→⟨ ξ-·-l TyBeta ⟩
  (να:=ℕ[
     λx:X.x
   | ((-X:=α ∷ id(X)) → (+X:=α ∷ id(ℕ))) ∷ id(ℕ→ℕ)]) · 7
  -→⟨ Wrap; arr(X, ·) = (-X:=α ∷ id(X), +X:=α ∷ id(ℕ)) ⟩
  να:=ℕ[
    (λx:X.x) · ν∅[7 | -X:=α ∷ id(X)]
  | +X:=α ∷ id(ℕ)]
  -→⟨ ξ-ν Beta ⟩
  να:=ℕ[
    ν∅[7 | -X:=α ∷ id(X)]
  | +X:=α ∷ id(ℕ)]
  -→⟨ Merge; (-X:=α ∷ id(X)) ⨟ (+X:=α ∷ id(ℕ)) = id(ℕ) ⟩
  να:=ℕ[7 | id(ℕ)]
  -→⟨ Const ⟩
  7.

The trace is v7's with every scope component erased.  `X` occurs in the
instantiated type, so `+X(X→X)` is all renaming elements and no
identity crossing appears.  After the merge, the strict `id(ℕ)`
types the boundary reflexively: interior and exterior are both `α:=ℕ`,
concealed, exactly as the cancelled crossings require.  In v7 the merged
scope `(+X:=α);(-X:=α)` had to be carried and separately admitted.

## Polymorphic argument under `Λ` (v7 Examples §14)

Here `X ∉ (∀Z.Z→Z)→(∀Y.Y→Y)`, so the type-preserving crossings appear.

  ((Λα,X.
      λf:∀Z.Z→Z. Λβ,Y. f •(Z→Z)[Y])
    •((∀Z.Z→Z)→(∀Y.Y→Y))[ℕ])
  · (Λγ,Z. λz:Z.z)
  -→⟨ ξ-·-l TyBeta; X ∉ B so +X(B) = id{+X:=α} ∷ id(B) ⟩
  (να:=ℕ[
     λf:∀Z.Z→Z. Λβ,Y. f •(Z→Z)[Y]
   | id{+X:=α} ∷ id((∀Z.Z→Z) → (∀Y.Y→Y))])
  · (Λγ,Z. λz:Z.z)
  -→⟨ Wrap; arr(∀Z.Z→Z, id{+X:=α} ∷ id(B→C))
          = (id{-X:=α} ∷ id(∀Z.Z→Z), id{+X:=α} ∷ id(∀Y.Y→Y)) ⟩
  να:=ℕ[
    (λf:∀Z.Z→Z. Λβ,Y. f •(Z→Z)[Y])
      · ν∅[Λγ,Z. λz:Z.z | id{-X:=α} ∷ id(∀Z.Z→Z)]
  | id{+X:=α} ∷ id(∀Y.Y→Y)]
  -→⟨ ξ-ν Beta; the substitution wraps f's value for the Λβ,Y crossing ⟩
  να:=ℕ[
    Λβ,Y.
      (ν∅[
         ν∅[Λγ,Z. λz:Z.z | id{-X:=α} ∷ id(∀Z.Z→Z)]
       | id{-Y:=β} ∷ id(∀Z.Z→Z)]) •(Z→Z)[Y]
  | id{+X:=α} ∷ id(∀Y.Y→Y)]
  -→⟨ ξ-ν (ξ-Λ (ξ-• Merge));
      (id{-X:=α} ∷ id(∀Z.Z→Z)) ⨟ (id{-Y:=β} ∷ id(∀Z.Z→Z))
        = id{-X:=α} ∷ id{-Y:=β} ∷ id(∀Z.Z→Z) ⟩
  να:=ℕ[
    Λβ,Y.
      (ν∅[
         Λγ,Z. λz:Z.z | id{-X:=α} ∷ id{-Y:=β} ∷ id(∀Z.Z→Z)]) •(Z→Z)[Y]
  | id{+X:=α} ∷ id(∀Y.Y→Y)]
  -→⟨ ξ-ν (ξ-Λ TyWrap);
      all(id{-X:=α} ∷ id{-Y:=β} ∷ id(∀Z.Z→Z))
        = id{-X:=α} ∷ id{-Y:=β} ∷ id(Z→Z);
      ⌊Y⌋ = β ⟩
  να:=ℕ[
    Λβ,Y.
      νγ:=β[
        λz:Z.z
      | id{-X:=α} ∷ id{-Y:=β}
          ∷ ((-Z:=γ ∷ id(Z)) → (+Z:=γ ∷ id(Y))) ∷ id(Y→Y)]
  | id{+X:=α} ∷ id(∀Y.Y→Y)].

The inner boundary's crossings, read inward from its exterior
`(α:=ℕ, X revealed; β, Y revealed; γ:=β)`: the `→` element reveals `Z:γ`
through its components, `id{-Y:=β}` conceals `Y`, `id{-X:=α}`
conceals `X` —
interior `α:=ℕ, β, Z:γ:=β`, so `λz:Z.z : Z→Z` with color `{Z}`, matching
v7.  What v7 wrote as the accumulated scope
`((-Y:=β) ; (-X:=α)) ; (+Z:=γ)` is now the conversion's own element prefix,
produced by `⨟` and `+Z(·)` with no separate bookkeeping.

## Cross-name composition and cancellation (v7 Examples, third)

The v7 example exercises compositions whose scopes cancel across
different names.  In v8 the same program produces those cancellations
inside `⨟` alone.  The key conversions become (with `α ≔ ℕ` revealed as
`Y`, `β ≔ ℕ` revealed as `X` at their binding sites):

  p  = +X:=β ∷ -Y:=α ∷ id(Y)          (both names occur: renaming only)
  q  = +Y:=α ∷ -X:=β ∷ id(X)
  v7's ℕ-typed component ids gain identity crossings, e.g. v7's
    s = (((+X ∷ id(ℕ)) → id(ℕ)) ∷ id(X→ℕ)) → (((-X ∷ id(X)) → id(ℕ)) ∷ id(ℕ→ℕ)) ...
  becomes
    s = (((+X:=β ∷ id(ℕ)) → (id{-X:=β} ∷ id(ℕ))) ∷ id(X→ℕ))
        → (((-X:=β ∷ id(X)) → (id{+X:=β} ∷ id(ℕ))) ∷ id(ℕ→ℕ)) ...

and the merges that v7 justified through scope transitions

  (-Y:=α ∷ id(Y)) ⨟ q = -X:=β ∷ id(X)
  (-X:=β ∷ id(X)) ⨟ p = -Y:=α ∷ id(Y)

go through unchanged, while the crossings that v7's `χ = (-Y:=α);(+X:=β)`
and `χ̄` tracked ride along as `id{∓Y:=α}`/`id{±X:=β}` elements and
cancel in `⨟` by the new `fuse` rows.  The full v8 trace should be machine-checked in
`Examples.agda` rather than hand-maintained here.

# Mechanization notes (Agda, strong/)

The v8 Agda development keeps the merged-entry de Bruijn contexts
(`Ctx.agda`), where a revealed entry is a visibility bit on the anchor's
entry and source names are read off as reveal-counts.  The v8 changes
land as:

  * `Conversion.agda`: the element type is `ConvElt` (renaming v7's
    `Head`), with new constructors `show`/`hide` (the `id{±X:=α}`
    forms, carrying the crossed anchor), strict `conv-id`, exact
    crossing premises on all four atomic elements, new `fuse` rows and
    weights.
    The tail
    judgment `_⊩_∶_⇝_⊣_` merges into `_⊢_∶_⇝_⊣_`, since a strict `id`
    makes every seam reflexive.
  * `Terms.agda`/`Reduction.agda`: `ν_[_∣_]` without the scope
    component; `⟨c⟩` as the interior computation; the reduction rules
    above.
  * `CtxMorph.agda` shrinks to stores; `ScopeDual.agda` and the
    scope/store commutation obligations disappear.
  * Regression probes: the two v7 failure configurations
    (`V7MergeScopeClashProbe`, `V7CancelDriftProbe`) restated in v8
    syntax must be typable and step-preserving.
