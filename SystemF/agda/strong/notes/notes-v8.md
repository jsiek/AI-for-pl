# Changes from v7 (DRAFT)

Version 8 makes the conversion the single source of truth for scope
crossings, and makes anchor allocation a global effect.

1. The boundary is conversion application, written `M⟨c⟩`.  It has no
   scope component and no store component.  The crossings that v7's `χ`
   performed are conversion ELEMENTS: `id{+X:=α}` and `id{-X:=α}` cross
   a reveal or a conceal without changing the type, alongside the
   renaming elements, which also carry their anchor: `+X:=α` (unseal)
   and `-X:=α` (seal).
2. Conversion typing is EXACT.  `id(A)` is strictly reflexive (one
   context, one type).  Each element connects two contexts that differ
   in exactly the crossing it performs; `→` and `∀` elements delegate
   their crossing to their component conversions.  A conversion's
   interior context is therefore a function `⟨c⟩(Γ)` of its syntax and
   its exterior context, which is what replaces `χ` in the `(Bndry)`
   and `(ξ-⟨⟩)` rules.
3. Representation bindings live in a GLOBAL store Σ, in the style of
   `GTSF/cambridge26.lagda.md`.  The term `να:=R. M` binds a local
   anchor with its representation; when it reaches evaluation position
   it discharges IMMEDIATELY into the store — one step, no per-frame
   hoisting.  Anchors in Σ are permanent and never shift.  The dual
   `-χ`, the action `χ(Γ)`, the transition `Γ ⊢ χ ⇒ Γ′`, and the
   rightmost-visible judgment `Γ ▷ X:=α` are all deleted; bracketing is
   not enforced by typing (crossings under `∀`-descents need
   arbitrary-depth conceals) and can return as a theorem about the
   conversions the builders and reduction rules produce.
4. The source `Λα,X.V` keeps α as a BINDER — a local anchor variable,
   not an allocation — because the substitution wrap under an
   uninstantiated `Λ` must name the anchor its crossing will use.
   `TyBeta` turns the bound α into the `ν` term's α.  The body is
   restricted to a VALUE, so there is no reduction under `Λ` and no
   `ξ-Λ` rule; term variables are NOT values, and Λ-bodies with free
   term variables are written with an inserted λ.
5. The reduction rules do no scope or store bookkeeping: `Merge` is
   `V⟨c⟩⟨d⟩ -→ V⟨c ⨟ d⟩`; `Wrap` needs no dual scope, because the
   contravariant `arr` component carries the dual crossings; `TyBeta`
   and `TyWrap` allocate through `ν` and let `+X(·)` emit the crossing.
6. `fuse` gains cancellation rows for the identity crossing elements;
   the views `arr` and `all` peel a crossing prefix, and a third view
   `base` lets `Const` see a ground terminator through identity
   crossings.

Motivation: under v7's rules the crossing information lived in two
places, and the typed coherence between them could not survive the
operations that rearrange conversion syntax.  Machine-checked failures:
`notes/old/probes-pre-merge/V7MergeScopeClashProbe.agda` (`Merge`
strands the crossings a bridging `id` performed) and
`notes/probes/V7CancelDriftProbe.agda` (cancelling a `seal/unseal` pair
strands the visibility drift its flanks absorbed).  Both configurations
become regression tests for v8.

# Design Criteria

Color Preservation: The set of type variables (X's) in scope (the
"color") at every subterm from the source program is invariant under
reduction (not including the runtime terms: conversions and boundaries,
runtime-created terms, or constant literals).  Color is about type
variables, not anchors: anchors are runtime store addresses.

Progress: Every closed, well-typed configuration is a value or can take
a reduction step.

Preservation: A reduction step preserves the type of a closed term and
extends the store conservatively.

Determinism: Every configuration has at most one immediate reduct, up
to the choice of fresh anchor.

Single source of crossings: every change of visibility between a
boundary's interior and exterior is performed by exactly one conversion
element, so the operations that rearrange conversions (`⨟`, `fuse`, the
reduction rules) preserve the crossing structure by construction.

# Types

  X,Y,Z ∈ TyVar
  a,b ::= X | ℕ | 𝔹            (atomic types)
  A,B,C ::= a | A → B | ∀X.A

Types mention type variables only; anchors never appear in types.

# Representation Types

Representation types mention stable anchors, not source type variables.

  R,S ::= α | ℕ | 𝔹 | R → S | ∀α.R

# Source Terms

  n ∈ ℕ
  b ∈ 𝔹
  x ∈ Var
  k ::= n | b
  ⊕ ::= + | ×
  L,M,N ::= x | k | M ⊕ N | λx:A. N | L · M | Λα,X.V | L •B[A]

The body of a `Λ` is a VALUE (see the value grammar below).  The α in
`Λα,X.V` is a binder for a local anchor variable: the body's
conversions — in particular the substitution wraps that `Beta` inserts
— name their crossing with it before any allocation has happened.
Binding is not allocating; the global store grows only at `ν`
discharge.

# The global store and contexts

  Σ ::= ∅ | Σ,α:=R                       (global representation store)
  Γ ::= ∅ | Γ,α | Γ,α:=R | Γ,X:=α | Γ,x:A

The store Σ is append-only: `ν` discharge adds a binding, and nothing
removes or reorders one, so anchors are permanent addresses.  A context
Γ holds the LOCAL structure: `α` is a Λ- or ∀-bound abstract anchor
variable, `α:=R` a ν-bound one not yet discharged, `X:=α` assigns a
source name to an anchor — "revealed" in v8 means exactly that a name
assignment for the anchor is in scope — and `x:A` is a term variable.
Judgments are indexed by both, written `Σ;Γ ⊢ ⋯`; anchor lookups search
Σ and Γ's anchor entries jointly, and we suppress Σ when it is fixed.

Write `ty(Γ)` for the type-only projection (drop the `x:A` entries).

  ------------
  | Γ ∋ X:=α |
  ------------

  ---------------
  (Γ,X:=α) ∋ X:=α

  Γ ∋ X:=α                    Γ ∋ X:=α        Γ ∋ X:=α
  --------------- (X ≠ Y)     ------------    ---------------
  (Γ,Y:=β) ∋ X:=α             (Γ,β) ∋ X:=α    (Γ,β:=S) ∋ X:=α

  Γ ∋ X:=α
  --------------
  (Γ,x:A) ∋ X:=α

  --------------          -----------
  | Σ;Γ ∋ α:=R |          | Σ;Γ ∋ α |
  --------------          -----------

`Σ;Γ ∋ α:=R` finds α's representation in Σ or among Γ's `α:=R` entries;
`Σ;Γ ∋ α` additionally accepts Γ's abstract `α` entries.  At most one
name assignment per anchor is live (`ok` below), so `Γ ∋ X:=α` and
`Γ ∋ Y:=α` force `X = Y`.

# Anchor representation of a source type

Write `⌊A⌋Γ` for the representation of `A` in `Σ;Γ`.

  ⌊X⌋Γ       = α                         if Γ ∋ X:=α
  ⌊ι⌋Γ       = ι
  ⌊A → B⌋Γ   = ⌊A⌋Γ → ⌊B⌋Γ
  ⌊∀X.A⌋Γ    = ∀α.⌊A⌋(Γ,α,X:=α)          (α fresh)

# Reading a representation type

The judgment `Σ;Γ ⊢ R ⇓ A` reads anchors through the name assignments
in scope.

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

# Well-formed Types   Σ;Γ ⊢ A

  (wf-ℕ)      Γ ⊢ ℕ

  (wf-𝔹)      Γ ⊢ 𝔹

  (wf-tvar)   Γ ∋ X:=α
              --------
              Γ ⊢ X

  (wf-fun)    Γ ⊢ A    Γ ⊢ B
              --------------
              Γ ⊢ A → B

  (wf-all)    X ∉ Γ  α ∉ Σ;Γ  Γ,α,X:=α ⊢ A
              -----------------------------
              Γ ⊢ ∀X.A

# Well-formed Representation Types   Σ;Γ ⊢ᴿ R

  (wfᴿ-tvar)  Σ;Γ ∋ α
              -------
              Γ ⊢ᴿ α

  (wfᴿ-ι)     Γ ⊢ᴿ ι

  (wfᴿ-fun)   Γ ⊢ᴿ R   Γ ⊢ᴿ S
              ----------------
              Γ ⊢ᴿ R → S

  (wfᴿ-all)   α ∉ Σ;Γ   Γ,α ⊢ᴿ R
              -------------------
              Γ ⊢ᴿ ∀α.R

# Well-formed store and contexts

  ----
  ∅ ok

  Σ ok  Σ;∅ ⊢ᴿ R  α ∉ Σ
  ----------------------
  Σ,α:=R ok

  -------
  Σ; ∅ ok

  Σ;Γ ok   α ∉ Σ;Γ           Σ;Γ ok  Σ;Γ ⊢ᴿ R  α ∉ Σ;Γ
  ----------------           -------------------------
  Σ; Γ,α ok                  Σ; Γ,α:=R ok

  Σ;Γ ok   Σ;Γ ∋ α   X ∉ Γ   Γ ∌ _:=α
  ------------------------------------
  Σ; Γ,X:=α ok

  Σ;Γ ok  Σ;Γ ⊢ A
  ---------------
  Σ; Γ,x:A ok

# Conversions

  ĉ,ḓ ::= +X:=α | -X:=α | id{+X:=α} | id{-X:=α} | c → d | ∀X.c
  c,d ::= id(A) | ĉ ∷ c

The four atomic elements all cross the introduction of one name
assignment `X:=α`; they differ in whether the crossing renames the
type:

  -X:=α      : SEAL: crosses the assignment's introduction outward,
               `A ⇒ X`, reading α's representation on the unassigned
               side.
  +X:=α      : UNSEAL: crosses the assignment's removal outward,
               `X ⇒ A`.
  id{-X:=α}  : identity conceal crossing: the same crossing as `-X:=α`
               with the type unchanged.  As a boundary element it
               conceals `X` inward — v7's scope change `-X:=α`,
               relocated into the conversion.
  id{+X:=α}  : identity reveal crossing: the same crossing as `+X:=α`
               with the type unchanged (the type must not mention `X`).

The ANCHOR is the operative datum of every atomic element, and the
syntax carries it: `fuse` decides cancellation by anchor equality (in
the `+X:=α ∷ -Y:=β` order the seam context has neither name in scope,
and equal names at the two outer contexts need not mean equal anchors),
the interior walk `⟨c⟩` identifies the assignment to add or remove by
its anchor, and anchors never shift.  The identity crossings work for
ABSTRACT anchors too — a Λ-bound α has no representation, and the
substitution wrap needs exactly `id{-X:=α}` — while the renaming
elements additionally demand `α:=R` for their read-back.

# Conversion-element Typing

Each rule's two contexts differ in EXACTLY the assignment the element
crosses.  Write `Γ+X:=α` for Γ with the assignment inserted at `X`'s
position (in the mechanization the name is a de Bruijn index, which is
the position).

  Σ;Γₑ ∋ α:=R   Σ;Γᵢ ⊢ R ⇓ A          (Γₑ = Γᵢ+X:=α)
  --------------------------------
  Σ;Γᵢ ⊢̂ -X:=α : A ⇒ X ⊣ Γₑ

  Σ;Γᵢ ∋ α:=R   Σ;Γₑ ⊢ R ⇓ A          (Γᵢ = Γₑ+X:=α)
  --------------------------------
  Σ;Γᵢ ⊢̂ +X:=α : X ⇒ A ⊣ Γₑ

  Σ;Γᵢ ⊢ A   Σ;Γᵢ ∋ α   X ∉ Γᵢ        (Γₑ = Γᵢ+X:=α)
  --------------------------------
  Σ;Γᵢ ⊢̂ id{-X:=α} : A ⇒ A ⊣ Γₑ

  Σ;Γₑ ⊢ A                            (Γᵢ = Γₑ+X:=α)
  --------------------------------
  Σ;Γᵢ ⊢̂ id{+X:=α} : A ⇒ A ⊣ Γₑ

Well-formedness of `A` on the unassigned side is what enforces `X ∉ A`
for the identity crossings.

The structural elements delegate their crossing to their components:

  Γₑ ⊢ c : C ⇒ A ⊣ Γᵢ    Γᵢ ⊢ d : B ⇒ D ⊣ Γₑ
  ------------------------------------------
  Γᵢ ⊢̂ c → d : (A → B) ⇒ (C → D) ⊣ Γₑ

  Γᵢ,α,X:=α ⊢ c : A ⇒ B ⊣ Γₑ,α,X:=α
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
context, replacing v7's `χ(Γ)`.  It walks the elements from the
terminator inward, undoing each element's crossing:

  ⟨id(A)⟩(Γ)     = Γ
  ⟨ĉ ∷ c⟩(Γ)     = ⟨ĉ⟩̂(⟨c⟩(Γ))

  ⟨-X:=α⟩̂(Γ+X:=α) = Γ           ⟨id{-X:=α}⟩̂(Γ+X:=α) = Γ
  ⟨+X:=α⟩̂(Γ)      = Γ+X:=α      ⟨id{+X:=α}⟩̂(Γ)      = Γ+X:=α
  ⟨c → d⟩̂(Γ)      = ⟨d⟩(Γ)
  ⟨∀X.c⟩̂(Γ)       = Γ′          if ⟨c⟩(Γ,α,X:=α) = Γ′,α,X:=α

The walk is fully syntax-directed — each element carries its name and
anchor — and on well-typed conversions it agrees with the typing:

  if Γᵢ ⊢ c : A ⇒ B ⊣ Γₑ then ⟨c⟩(Γₑ) = Γᵢ.

# Conversion builders   +X(A), -X(A)

The builders are indexed by the two endpoint contexts.  If an equation
reaches a free occurrence of `X`, its represented type is obtained by

  Γᵥ ∋ X:=α   Σ;Γᵥ ∋ α:=R   Γₕ ⊢ R ⇓ S
  --------------------------------------
  Γᵥ ; Γₕ ⊢ repr(X) = S.

Every equation's result crosses `X:=α` exactly once at the top level: a
hit crosses with the renaming element, a miss crosses with the identity
crossing element, and a split delegates the crossing to its components.
The context indices and `S` are suppressed:

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

  Γᵢ+X:=α ⊢ +X(A) : A ⇒ A[X:=S] ⊣ Γᵢ
  Γᵢ      ⊢ -X(A) : A[X:=S] ⇒ A ⊣ Γᵢ+X:=α

  -----------------
  | +X(c) = c′ | (reveal X in c)
  | -X(c) = c′ | (conceal X in c)
  -----------------

These operations require `NF(c)` and return a conversion in normal form.

  +X(id(A)) = +X(A)             -X(id(A)) = -X(A)
  +X(ĉ ∷ c) = +X(ĉ) ⨟ +X(c)
  -X(ĉ ∷ c) = -X(ĉ) ⨟ -X(c)

On elements, with `B` the target supplied by the typing derivation of
the transformed element:

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

  L,M,N ::= ... | να:=R. M | M⟨c⟩

`M⟨c⟩` is CONVERSION APPLICATION — the boundary.  It has no store and
no scope: the conversion's elements carry the crossings, and the
interior context is `⟨c⟩` of the exterior.  `να:=R. M` binds a local
anchor with its representation; it is an allocation waiting to
discharge into Σ.

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
  fuse(c₁→d₁,c₂→d₂)                 = [(c₂ ⨟ c₁) → (d₁ ⨟ d₂)]
  fuse(∀X.c,∀X.d)                   = [∀X.(c ⨟ d)]
  fuse(ĉ,ḓ)                         undefined otherwise.

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

Every successful fusion decreases the total weight of the element list,
so `contract` terminates; the crossing elements have weight 1 like the
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

Three views classify a normal boundary conversion by peeling its
crossing prefix; κ ranges over the identity crossing elements, with
`κ̄` the dual element (`id{+X:=α}` ↔ `id{-X:=α}`).

`arr` takes the INTERIOR domain from the λ annotation at its use site
(the conversion's syntax does not carry it when the conversion is a
bare `id` or begins with crossing elements):

  arr(A₀, id(A → B)) = (id(A), id(B))
  arr(A₀, κ₁ ∷ … ∷ κₙ ∷ (c → d) ∷ id(C → D))
    = (c ⧺ (κ̄ₙ ∷ … ∷ κ̄₁ ∷ id(A₀)), κ₁ ∷ … ∷ κₙ ∷ d)     (n ≥ 0)

  all(id(∀X.A)) = id(A)
  all(κ₁ ∷ … ∷ κₙ ∷ (∀X.c) ∷ id(∀X.B)) = κ₁ ∷ … ∷ κₙ ∷ c  (n ≥ 0)

  base(id(ι)) = ι
  base(κ ∷ c) = base(c)

`arr` peels the crossing prefix in one pass: the contravariant
component re-crosses it in reverse with the dual elements and
terminates at the INTERIOR domain `A₀` — the λ's own annotation, in its
own coordinates — so no renaming is involved; the covariant component
keeps the prefix.  Here `_⧺_` is terminator-discarding append.  `base`
is the view `Const` uses: a literal ignores identity crossings.

OPEN (to be settled in the mechanization): whether every reachable
normal boundary conversion at a function, universal, or ground target
has one of these shapes.  Renaming elements can in principle stand
between identity crossings in a normal form
(`-X:=α ∷ id{-Y:=β} ∷ +X:=α ∷ id(S)` is normal); the claim to prove is
that such conversions do not reach value boundaries, or else the views
and the `Value` clause must treat them.

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

Because every crossing is an element, the appended element list
performs exactly the crossings of the two derivations in sequence; the
v7 counterexamples (a deleted bridging `id`, a cancelled pair with
drifted flanks) cannot be stated.

# Term Typing   Σ;Γ ⊢ M : A

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

  (TyLam)   Γ, α, X:=α ⊢ V : A   Value V
            ------------------------------ (α fresh)
            Γ ⊢ Λα,X.V : ∀X.A

  (TyApp)   Γ ⊢ L : ∀X.B   Γ ⊢ A
            --------------------
            Γ ⊢ L •B[A] : B[X:=A]

  (Nu)      Σ;ty(Γ) ⊢ᴿ R   Σ; Γ,α:=R ⊢ M : A
            --------------------------------- (α fresh)
            Σ;Γ ⊢ να:=R. M : A

  (Bndry)   NF(c)   ⟨c⟩(ty(Γ)) = Γᵢ
            Σ;Γᵢ ⊢ M : A
            Σ;Γᵢ ⊢ c : A ⇒ B ⊣ ty(Γ)
            ------------------------
            Σ;Γ ⊢ M⟨c⟩ : B

Anchors never appear in types, so `(Nu)` needs no side condition to
keep α from escaping.  The interior context of a boundary is not a
component of the term; it is computed from the conversion, and it is
unique because each element's crossing inverts uniquely.  A boundary
body contains no free term variables from its exterior.

# Values

  Vˢ,Wˢ ::= k | λx:A.N | Λα,X.V
  V,W ::= Vˢ | Vˢ⟨c⟩
    where NF(c) and arr(A₀,c), all(c), or a type-variable target applies

Term variables are NOT values.  The value restriction on `Λ` bodies is
compatible with free term variables under `Λ` because the value grammar
is not closed under subterms: `λx:A.N` is a value for ARBITRARY `N`, so
a body like `λy:Y. (f •(Z→Z)[Y]) · y` is a value with `f` free.
Values are closed under substitution of values for term variables,
which is what `Beta` needs to preserve the restriction.

A `να:=R.V` is not a value: an allocation in evaluation position always
discharges.  A `k⟨c⟩` with `base(c)` defined is not a value: it steps
by `Const`.

# Term-variable substitution   N[x := M : A]

  x[x:=V:A]             = V
  y[x:=V:A]             = y                             (y ≠ x)
  k[x:=V:A]             = k
  (M₁ ⊕ M₂)[x:=V : A]   = M₁[x:=V:A] ⊕ M₂[x:=V:A]
  (L · M)[x:=V:A]       = L[x:=V:A] · M[x:=V:A]
  (λx:B. N)[x:=V:A]     = λx:B. N                       (shadow)
  (λy:B. N)[x:=V:A]     = λy:B. N[x:=V:A]               (y ≠ x)
  (Λα,X. W)[x:=V:A]     = Λα,X. W[x:= V⟨id{-X:=α} ∷ id(A)⟩ ]
  (L •B[C])[x:=V:A]     = L[x:=V:A] •B[C]
  (να:=R. M)[x:=V:A]    = να:=R. M[x:=V:A]
  M⟨c⟩ [x:=V]           = M⟨c⟩                          (skip M)

The `Λ` clause is the COLOR wrap: the substituend crosses into `X`'s
scope behind an identity conceal, so its nodes' color does not gain
`X`.  The element `id{-X:=α}` names the Λ-BOUND anchor — this is why
`Λ` keeps its binder — and needs no representation, because identity
crossings never read one.  `A` cannot mention `X` because `V` was typed
outside the `Λ`.

# Reduction Rules

Reduction is store-passing and indexed by the ambient context: write
`Σ;Γ ⊢ M —→ N ⊣ Σ′`, where only `Alloc` extends the store; we omit `Σ`
and `Γ` when they are unchanged or clear.

  (Beta)      (λx:A. N) · W  -→  N[x:=W:A]
  (PrimBeta)  n₁ ⊕ n₂        -→  n₁ ⟦⊕⟧ n₂
  (TyBeta)    (Λα,X.V) •B[A]  -→  να:=⌊A⌋Γ. V⟨+X(B)⟩
  (Alloc)     Σ;Γ ⊢ να:=R. M  —→  M ⊣ Σ,α:=R            (α fresh for Σ)
  (Wrap)      (λx:A₀.N)⟨c⟩ · W  -→  ((λx:A₀.N) · W⟨c₁⟩)⟨c₂⟩
              if arr(A₀,c) = (c₁,c₂)
  (TyWrap)    (Λα,X.V)⟨c⟩ •B[A]  -→  να:=⌊A⌋Γ. V⟨+X(d)⟩
              if all(c) = d
  (Merge)     V⟨c⟩⟨d⟩  -→  V⟨c ⨟ d⟩
              if V⟨c⟩ is a value
  (Const)     k⟨c⟩ -→ k       if base(c) = ι

`Alloc` is immediate: the ξ-rules propagate the store extension, so an
allocation discharges in one step from any evaluation position — there
is no per-frame hoisting and `ν` never blocks a redex.  `TyBeta` and
`TyWrap` turn the `Λ`'s bound anchor into the `ν`'s; the body `V` is
untouched, and its wraps' `id{-X:=α}` elements are captured by the same
binder.  Compare v7: `TyBeta` and `TyWrap` lose their scope components
(the crossing is inside `+X(·)`), `Wrap` loses the dual scope `-χ` (the
contravariant component `c₁` carries the dual crossings), and `Merge`
loses the store concatenation and scope composition.  `Wrap` matches
the body as a λ because `arr` needs the interior domain.

  (ξ-·-l)   L · M -→ L′ · M       if L -→ L′
  (ξ-·-r)   V · M -→ V · M′       if M -→ M′
  (ξ-⊕-l)   L ⊕ M -→ L′ ⊕ M       if L -→ L′
  (ξ-⊕-r)   V ⊕ M -→ V ⊕ M′       if M -→ M′
  (ξ-•)     L •B[A] -→ L′ •B[A]   if L -→ L′
  (ξ-⟨⟩)    M⟨c⟩ -→ M′⟨c⟩
              if Σ; ⟨c⟩(ty(Γ)) ⊢ M -→ M′ ⊣ Σ′

There is NO `ξ-Λ`: `Λ` bodies are values and never reduce in place.

# Theorem Statements

## Progress

If `Σ ok` and `Σ;∅ ⊢ M : A`, then either `Value M` or there exist `N`,
`Σ′` such that `Σ;∅ ⊢ M —→ N ⊣ Σ′`.

## Preservation

If `Σ;Γ ok`, `ty(Γ) = Γ`, `Σ;Γ ⊢ M : A`, and `Σ;Γ ⊢ M —→ N ⊣ Σ′`, then
`Σ′ ⊇ Σ` and `Σ′;Γ ⊢ N : A`.

## Determinism

If `Σ;Γ ok`, `Σ;Γ ⊢ M : A`, `Σ;Γ ⊢ M —→ N₁ ⊣ Σ₁`, and
`Σ;Γ ⊢ M —→ N₂ ⊣ Σ₂`, then `N₁ ≡α N₂` and `Σ₁ ≡α Σ₂`, identifying the
choice of fresh anchor.

## Interior well-formedness

If `Σ;Γ ok`, `NF(c)`, and `Σ;Γᵢ ⊢ c : A ⇒ B ⊣ Γ`, then `Σ;Γᵢ ok` and
`⟨c⟩(Γ) = Γᵢ`.

## Color Preservation

Color is over TYPE VARIABLES:

  color(Γ) = { X | Γ ∋ X:=α for some α }.

The one-hole-context judgment descends as in v7, with the `Λ` clause
adding `α, X:=α` and the boundary clause computed by `⟨c⟩`:

  Γ,α,X:=α ⊢ C ⊣ Γ′               ⟨c⟩(ty(Γ)) ⊢ C ⊣ Γ′
  ------------------              --------------------
  Γ ⊢ Λα,X.C ⊣ Γ′                 Γ ⊢ C⟨c⟩ ⊣ Γ′

  Γ,α:=R ⊢ C ⊣ Γ′
  ------------------
  Γ ⊢ να:=R.C ⊣ Γ′

The `ν` clause adds no name assignment, so allocation never changes a
color.  The descendant relation and the statement are otherwise as in
v7; the substitution wrap in the `Λ` clause of substitution is what
keeps a substituted value's color from gaining `X`.

## Representation soundness

If `Σ;Γ ok` and `Σ;Γ ⊢ A`, then `Σ;Γ ⊢ᴿ ⌊A⌋Γ` and `Σ;Γ ⊢ ⌊A⌋Γ ⇓ A`.

# Examples

Store extensions are noted at each `Alloc` step.

## Polymorphic identity (v7 Examples §6)

  ((Λα,X. λx:X.x) •(X→X)[ℕ]) · 7
  -→⟨ ξ-·-l TyBeta ⟩
  (να:=ℕ. (λx:X.x)⟨((-X:=α ∷ id(X)) → (+X:=α ∷ id(ℕ))) ∷ id(ℕ→ℕ)⟩) · 7
  -→⟨ ξ-·-l Alloc;  Σ = α:=ℕ ⟩
  ((λx:X.x)⟨((-X:=α ∷ id(X)) → (+X:=α ∷ id(ℕ))) ∷ id(ℕ→ℕ)⟩) · 7
  -→⟨ Wrap; arr(X, ·) = (-X:=α ∷ id(X), +X:=α ∷ id(ℕ)) ⟩
  ((λx:X.x) · 7⟨-X:=α ∷ id(X)⟩)⟨+X:=α ∷ id(ℕ)⟩
  -→⟨ ξ-⟨⟩ Beta ⟩
  (7⟨-X:=α ∷ id(X)⟩)⟨+X:=α ∷ id(ℕ)⟩
  -→⟨ Merge; (-X:=α ∷ id(X)) ⨟ (+X:=α ∷ id(ℕ)) = id(ℕ) ⟩
  7⟨id(ℕ)⟩
  -→⟨ Const; base(id(ℕ)) = ℕ ⟩
  7.

The λ's body types at the interior `Γ,X:=α`; after the merge the strict
`id(ℕ)` has an empty interior walk, and `Const` reads the ground
terminator directly.  Every piece of v7's scope bookkeeping — the
boundary's `+X:=α` scope component, the dual `-χ` on the argument wrap,
the merged scope and its separate admissibility check — is gone, and
the store records `α:=ℕ` permanently.

## Polymorphic argument under `Λ` (v7 Examples §14, adapted)

The value restriction requires a λ in the inner `Λ` body, so the source
term η-expands `f •(Z→Z)[Y]`:

  ((Λα,X.
      λf:∀Z.Z→Z. Λβ,Y. λy:Y. (f •(Z→Z)[Y]) · y)
    •((∀Z.Z→Z)→(∀Y.Y→Y))[ℕ])
  · (Λγ,Z. λz:Z.z)
  -→⟨ ξ-·-l TyBeta; X ∉ B so +X(B) = id{+X:=α} ∷ id(B) ⟩
  (να:=ℕ.
    (λf:∀Z.Z→Z. Λβ,Y. λy:Y. (f •(Z→Z)[Y]) · y)
      ⟨id{+X:=α} ∷ id((∀Z.Z→Z) → (∀Y.Y→Y))⟩)
  · (Λγ,Z. λz:Z.z)
  -→⟨ ξ-·-l Alloc;  Σ = α:=ℕ ⟩
  ((λf:∀Z.Z→Z. Λβ,Y. λy:Y. (f •(Z→Z)[Y]) · y)
     ⟨id{+X:=α} ∷ id((∀Z.Z→Z) → (∀Y.Y→Y))⟩)
  · (Λγ,Z. λz:Z.z)
  -→⟨ Wrap; arr(∀Z.Z→Z, id{+X:=α} ∷ id(B→C))
          = (id{-X:=α} ∷ id(∀Z.Z→Z), id{+X:=α} ∷ id(∀Y.Y→Y)) ⟩
  ((λf:∀Z.Z→Z. Λβ,Y. λy:Y. (f •(Z→Z)[Y]) · y)
    · (Λγ,Z. λz:Z.z)⟨id{-X:=α} ∷ id(∀Z.Z→Z)⟩)
  ⟨id{+X:=α} ∷ id(∀Y.Y→Y)⟩
  -→⟨ ξ-⟨⟩ Beta; the substitution wraps W for the Λβ,Y crossing,
      W = (Λγ,Z. λz:Z.z)⟨id{-X:=α} ∷ id(∀Z.Z→Z)⟩ ⟩
  (Λβ,Y. λy:Y.
     ((W⟨id{-Y:=β} ∷ id(∀Z.Z→Z)⟩) •(Z→Z)[Y]) · y)
  ⟨id{+X:=α} ∷ id(∀Y.Y→Y)⟩

and this is a VALUE: the `Λβ,Y` body is a λ, the boundary's conversion
is normal, and `all(id{+X:=α} ∷ id(∀Y.Y→Y)) = id{+X:=α} ∷ id(Y→Y)` is
defined.  Under the value restriction the `Merge` and `TyWrap` that v7
performed inside the `Λ` wait for instantiation.  Applying the value,
say `•(Y→Y)[𝔹]` and then `· true`, drives them:

  -→⟨ TyWrap; all as above; ⌊𝔹⌋ = 𝔹 ⟩  -→⟨ Alloc; Σ = α:=ℕ, β:=𝔹 ⟩
  (λy:Y. ((W⟨id{-Y:=β} ∷ id(∀Z.Z→Z)⟩) •(Z→Z)[Y]) · y)
  ⟨id{+X:=α} ∷ ((-Y:=β ∷ id(Y)) → (+Y:=β ∷ id(𝔹))) ∷ id(𝔹→𝔹)⟩
  · true

after which `Wrap` splits the conversion (the crossing prefix peels
into both components), `Beta` substitutes the wrapped `true`, the inner
type application `Merge`s the two wraps on `W` into
`(Λγ,Z. λz:Z.z)⟨id{-X:=α} ∷ id{-Y:=β} ∷ id(∀Z.Z→Z)⟩`, `TyWrap`
allocates `γ:=β` (note `⌊Y⌋ = β`: a stored representation can point at
an earlier anchor), and the remaining `Wrap`/`Beta`/`Merge`/`Const`
steps cancel every crossing and deliver `true` with
`Σ = α:=ℕ, β:=𝔹, γ:=β`.  The full trace belongs in `Examples.agda`.

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
cancel in `⨟` by the new `fuse` rows.  The λ-insertion applies to this
example's `Λ` bodies as well (`λk:…` and `λf:…` are already λs).  The
full v8 trace should be machine-checked in `Examples.agda` rather than
hand-maintained here.

# Mechanization notes (Agda, strong/)

The v8 Agda development realizes the two-sorted contexts with the
merged-entry representation already in `Ctx.agda`: the global store is
an append-only context of anchor entries, a name assignment is a
visibility mark on its anchor's entry (so name order equals anchor
order and `Γ+X:=α`'s insertion position is determined by α), and de
Bruijn names are reveal-counts.  Λ- and ν-bound anchors are ordinary de
Bruijn binders substituted at `TyBeta`/`Alloc`; discharged anchors are
stable levels, so no anchor renaming accompanies any reduction.  The
v8 changes land as:

  * `Conversion.agda`: the element type is `ConvElt` (renaming v7's
    `Head`), with new constructors `show`/`hide` (the `id{±X:=α}`
    forms, carrying the crossed anchor), strict `conv-id`, exact
    crossing premises on all four atomic elements, new `fuse` rows and
    weights, and the `base` view beside `arr`/`allView`.  The tail
    judgment `_⊩_∶_⇝_⊣_` merges into `_⊢_∶_⇝_⊣_`, since a strict `id`
    makes every seam reflexive.
  * `Terms.agda`/`Reduction.agda`: `_⟨_⟩` and `ν_:=_._` replace
    `ν_,_[_∣_]`; `⟨c⟩` as the interior computation; store-passing
    reduction with `Alloc`; the value restriction on `Λ` bodies; no
    `ξ-Λ`.
  * `CtxMorph.agda` and `proof/ScopeDual.agda` disappear (no scopes, no
    stores in terms); `proof/AnchorWeaken.agda` disappears (nothing
    shifts).
  * Regression probes: the two v7 failure configurations
    (`V7MergeScopeClashProbe`, `V7CancelDriftProbe`) restated in v8
    syntax must be typable and step-preserving.
