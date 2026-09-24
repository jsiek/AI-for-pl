# Strong System F with representation variables

This is the mathematical presentation of the calculus in
`SystemF/agda/strong-rep-nu/` at commit `5d98bbe2` (2026-09-24).  The Agda uses de
Bruijn indices; this note uses names.  The named presentation is not a
different calculus: it suppresses index shifts and weakenings, but keeps
the contexts in which types and conversions are read.

## What changed and why

Four experiments have landed since the first draft of this note, and
all four are visible in every section below.

  1. **The value restriction** (2026-09-21).  `⊢Λ` requires its body to
     be a value and there is no `ξ-Λ`: nothing reduces under a type
     binder.
  2. **The store** (2026-09-22).  A boundary no longer carries a block of
     representation bindings.  The representation a ∀-elimination mints is
     allocated on the **ambient** representation context, and a reduction
     step reports the change it made to that context.  A boundary scope is
     now its change list alone, and a boundary changes **names** only.

  3. **`ν` replaces type application** (2026-09-24, strong-rep-nu).  The
     run-time language has no `L [B, A]`.  Its ∀-elimination is
     `νX:=A · L ⟨ c ⟩`, which carries the conversion the old `TyBeta`
     minted at run time.  Plain System F, with the standard `L [A]`, is a
     separate source language that is compiled into it (§ "The source
     language and `compile`" below).  The ∀-elimination rules are `Nu-Λ`
     and `Nu-⟪Λ⟫`, and `Nu-⟪Λ⟫` STACKS the crossed conversion under
     `ν`'s own instead of fusing the two.
  4. **Merging boundaries** (2026-09-24, strong-rep-nu, 5d98bbe2).
     Conversions are normal forms in three sorts, a value carries AT
     MOST ONE boundary, and a boundary directly over a value's boundary
     is a redex of the one rule `Merge`, which merges the two frames and
     COMPOSES the two conversions (`Δ ⊢ c₁ ⨟ c₂`).  `Merge` subsumes
     the retired `CancelR` and `IdPush`, and it fuses `Nu-⟪Λ⟫`'s stacked
     layers one step later.  The third ∀-elimination rule, `Nu-⟪⟫`, is
     deleted: the interior of a `∀`-value's single boundary is a `Λ`, so
     it could not fire, and with it went the one reveal minted at run
     time; every reveal is now written by the compiler.

The design note for the second is `notes/RepStoreSketch.md`, for the
third `notes/NuSketch.md` and for the fourth `notes/MergeSketch.md`; the
dated record for all four is the last entries of `notes/DECISIONS.md`.

The distinction at the center of the development is:

    X, Y, Z       type variables
    α, β, γ       representation variables

A type variable is lexical: `∀X.A`, `ΛX.M`, and types mention `X`.  A
representation variable is runtime storage: a representation context
binds `α` abstractly or to a representation type, while a boundary
only says which type variables may name it.  A live type variable `X` is
associated with that `α`.  The renderer pairs the supplies (`X` to
`α`, `Y` to `β`, and so on), but the two universes remain different.

# Syntax

## Types and representation types

    A, B ::= X | ℕ | 𝔹 | A ⇒ B | ∀X.A

Types contain free type variables.  A representation type has the same
tree grammar, but its free variables are representation variables:

    R, S ::= α | X | ℕ | 𝔹 | R ⇒ S | ∀X.R

An `X` occurrence in a representation type is legal only under its representation-local
`∀X`; every free representation type variable is a representation variable such as
`α`.  This is the named reading of Agda's one datatype `Ty` with its mixed
`_ ⊢ᴿ[ n ]_` formation judgment.

## Conversions

Conversions are NORMAL FORMS in three sorts (Agda `Mid`, `Tail`,
`Conv`):

    g ::= id A | c ↦ d | ∀X.c                 middle      (A a base type or a variable)
    t ::= g | seal X | t ; seal X             tail        (a seal chain, associates LEFT)
    c, d ::= t | unseal X | unseal X ; c      conversion  (an unseal chain, associates RIGHT)

A middle is a tail and a tail is a conversion; Agda writes the
injections `mid g` and `tail t`, and `⌞ g ⌟` for `tail (mid g)`.  The
chains are Agda's `t ⨾seal X` and `unseal X ⨾ c`.  A bare `seal X`
stands for an identity middle followed by `seal X`, and a bare
`unseal X` for `unseal X` followed by an identity middle.

`seal X` and `unseal X` carry a type variable, never a representation:
conversions are REP-FREE, and they find the representation through the
context.  Function conversions are contravariant on the left.

The types force the positions.  `unseal X ; c` has source `X`, so an
unseal can only open a conversion whose source is a variable, and
`t ; seal X` has target `X`, so a seal can only close a conversion
whose target is a variable.

**Identity** is syntactic, and it includes the structural identities:

    IsId(id A)          = true
    IsId(c ↦ d)         = IsId(c) and IsId(d)
    IsId(∀X.c)          = IsId(c)
    IsId(seal X)        = IsId(t ; seal X)  = false
    IsId(unseal X)      = IsId(unseal X ; c) = false

**No cancellation.**  `NoCancel X c` says that `c`'s seal chain does not
begin with a bare `seal X`, so that `unseal X ; c` is not a second
spelling of an identity:

    NoCancel X (seal Y)        = X and Y are distinct
    NoCancel X (t ; seal Y)    = NoCancel X t
    NoCancel X g               = true      (a non-identity middle blocks the cancel)
    NoCancel X (unseal Y)      = true
    NoCancel X (unseal Y ; c)  = true

## Terms

    n ∈ ℕ
    x ∈ Var

    L, M, N ::= x | n | true | false
              | λx:A. N | L · M
              | ΛX. N | νX:=A · L ⟨ c ⟩
              | M ⟪ Θ , c ⟫

`νX:=A · L ⟨ c ⟩` is the run-time ∀-elimination (Agda `ν_·_⟨_⟩`).  It
evaluates `L` to a `∀`-value, allocates a fresh store cell `α` for the
representation of `A`, instantiates `L` at `α`, and converts the result
with `c`.  The name `X` is bound in `c` only: it is the type variable
that names the new cell `α`, and `c` is read with it live.  (Agda writes
`ν A · L ⟨ c ⟩`, and `c`'s ordinary variable 0 is that name; the
renderer prints `(ν X:=A · L ⟨ c ⟩)`.)  There is no type application in
the run-time language.


`M ⟪ Θ , c ⟫` is a runtime boundary.  Its body is term-closed.
The boundary scope `Θ` determines its contexts, and `c` converts the body's
interior type to the boundary's exterior type.

## Boundary Scope

    δ ::= unbind X α | bind X α
    Θ ::= ⟨⟩ | δ ∷ Θ

(written `⟨ δ₁ , δ₂ ⟩` for `δ₁ ∷ δ₂ ∷ ⟨⟩`, in acting order: the head
acts first)

A boundary scope is a change sequence: `Boundary = List Change` in
Agda.  The changes are sequential.  Agda stores them head-last, so there
the tail acts first; this note writes them in acting order.

The displayed boundary notation follows `Show.agda`:

    ↓X         unbind X, recording that it names α
    ↥X         bind the type variable X for α

Thus `M ⟪ ↓Y , ↥Z , c ⟫` displays changes in the order in which they act,
and the conversion last.  The full change syntax remains `unbind Y β` and
`bind Z γ`; the Greek argument is recoverable from the displayed Latin
name.

# The two context universes

A type context is presented as

    Ξ ∣ Γ

where `Ξ` is a representation context and `Γ` maps type variables to representation variables:

    Ξ ::= · | Ξ, α | Ξ, α := R
    Γ ::= · | Γ, X ↦ α

`Ξ` is the **store**: it holds every representation cell the run has
minted, interleaved with the abstract cells the `Λ`s introduced.  The Γ
context contains exactly the live type variables.  An unbound type
variable has no entry in `Γ`, but its representation variable remains in
`Ξ`.  In a well-formed context every representation type is well formed outside its
own binder, every type variable points into `Ξ`, and no representation variable has
two simultaneous type variables.  We use the Barendregt convention, so
type variables and representation variables are chosen fresh.

The main lookups are:

    Ξ ∣ Γ ∋ X ↦ α       X is live and α points to its representation type
    Ξ ∣ Γ ∋ α := R      α's stored representation is R
    Ξ ∣ Γ ∋ X := A      X is live and A is its representation type

The definition of lookup Ξ ∣ Γ ∋ X := A is derived from the other forms.

## Allocation

A ∀-elimination mints a representation cell on the ambient store:

    allocate(α:=R, (Ξ ∣ Γ))  =  (Ξ, α := R) ∣ Γ

This is Agda's `allocate R (Ξ ∣ Δ) = (bindR R ∷ Ξ) ∣ shiftReps Δ`: the
fresh cell takes index `0` and every existing representation index — in
the name map and in every sibling term — moves up by one.  With names
nothing moves; the new `α` is simply fresh, and `Γ` is unchanged.

## Well-formed Types

Write `Δ = Ξ ∣ Γ`.  Extending under an ordinary type binder allocates a
fresh abstract representation variable and a type variable for it:

    under(X,α,Δ) = (Ξ, α) ∣ (Γ, X ↦ α)

The ordinary formation rules are:

    (wf-var)   X ↦ α ∈ Γ
               ---------
               Δ ⊢ᵗ X

    (wf-ℕ)     ---------          (wf-𝔹)     ---------
               Δ ⊢ᵗ ℕ                         Δ ⊢ᵗ 𝔹

    (wf-⇒)     Δ ⊢ᵗ A    Δ ⊢ᵗ B
               -----------------
               Δ ⊢ᵗ A ⇒ B

    (wf-∀)     under(X,α,Δ) ⊢ᵗ A
               ------------------
               Δ ⊢ᵗ ∀X.A

Representation formation has the same structural rules.  Its free-variable
rule asks for `α ∈ Ξ`; under representation type `∀X` it adds only the representation-local
ordinary binder `X`, not a new free representation variable.

## One representation, two ordinary spellings

The Agda relation `Γ ⊢ A ~ R` says that the ordinary type `A`, read
through scope map `Γ`, denotes representation type `R`.  Consequently

    Δ ⊢ A ≈ B ⊣ Δ′

says that `A` in `Δ` and `B` in `Δ′` denote the same representation
type.  `SameConv Δ c Δ′ c′` is the structural analogue for conversions.

With names, the type variable of a representation does not change merely
because another name is unbound or bound.  Therefore a weakening
premise normally becomes:

  * use the same type variable or conversion on both sides; and
  * require every variable in it to be in scope in each context where it is
    read.

This simplification does not identify the interior and conversion contexts.
Which context reads a premise remains genuine semantic content.

# Boundaries and Generating the Interior and Conversion Scopes

A boundary scope does not touch the store: both readings leave `Ξ`
exactly as it was, and differ only in what they do to `Γ`.  (This is
Agda's `interior-reps`/`conversion-reps`: `reps Δᵢ ≡ reps Δ ≡ reps Δᶜ`.)

The **interior scope** generation, written `Δ ⊢ⁱ Θ ⇒ Δᵢ`, performs every change:

    unbind X α   removes X ↦ α
    bind X α     adds X ↦ α, provided α has no live type variable

The **conversion scope** generation, written `Δ ⊢ᶜ Θ ⇒ Δᶜ`, is the union of
the variable live anywhere in the boundary:

    unbind X α   is skipped
    bind X α     adds X ↦ α if α is not live
    bind X α     is a no-op if α already has its unique live name

The last clause is `conv-bind-live`.  For example, a conversion reading
of `↓X` leaves `X` live; the inverse `↥X` in `Θ ++ dual Θ` must therefore
be a no-op, not a failed freshness check.  `strong-rep-store/notes/ReUnlockWall.agda`
machine-checks the old failure and the repaired readings.

Both readings are relations, but each is functional.  A well-formed
boundary witness is:

    BoundaryWf Δ Θ Δᵢ Δᶜ

It carries `WfCtx Δ` and the two readings `Δ ⊢ⁱ Θ ⇒ Δᵢ` and
`Δ ⊢ᶜ Θ ⇒ Δᶜ`, and nothing else.  Well-formedness of the two outputs is
derived.

## Derived Boundary Scopes

Change sequences are written in ACTING order (the head acts first).  The
inverse of a change swaps unbind and bind:

    (unbind X α)⁻¹  = bind X α
    (bind X α)⁻¹    = unbind X α

    dual []          = []
    dual (δ ∷ Θ)     = dual Θ ++ [ δ⁻¹ ]      -- inverses, in reverse order

The other scopes the rules build are written out at their use sites:
`[ bind X α ]` (the outer layer of both `Nu` contracta), `Θ` itself read
under that bind (the middle layer of Nu-⟪Λ⟫), and the merge `Θ₂ ++ Θ₁`,
the outer scope acting first, which is the one Merge builds.  Stacked,
the outer and middle layers act as `bind X α ∷ Θ`, which is the single
scope the pre-`ν` rules wrote, and the next Merge builds exactly that
merge.  The rewind `Θ ++ dual Θ` is still a scope one can write, but
since 2026-09-23 no rule builds one.  Agda's change lists are head-LAST
(the tail acts first), so its spellings are the mirror images:
`dual χ = map dualChange (reverse χ)`, `rewind Θ = dual Θ ++ Θ`, the
merge is `Θ₁ ++ Θ₂`, the outer layer is `inst [] = bind 0 0 ∷ []`
(`TyBetaBoundary`), and the middle layer is `liftᴮ Θ = map shiftChange
Θ`, so that `inst Θ = liftᴮ Θ ++ (bind 0 0 ∷ [])` is the two stacked.  Nothing shifts a representation when two
scopes merge, because both were spelled at the same store; `liftᴮ`
shifts in both universes because it is read one allocation later — with
names that shift is invisible.

## A concrete boundary

Let

    Δ = (α := ℕ, β) ∣ (X ↦ α, Y ↦ β)
    Θ = ⟨ ↓X, ↥Z ⟩

where `Z` names `γ`, a cell the enclosing ∀-elimination just allocated:
the boundary is read at `allocate(γ:=α, Δ)`, so

    Δ₀ = (α := ℕ, β, γ := α) ∣ (X ↦ α, Y ↦ β)

Then

    Δᵢ = (α := ℕ, β, γ := α)
         ∣ (Y ↦ β, Z ↦ γ)

    Δᶜ = (α := ℕ, β, γ := α)
         ∣ (X ↦ α, Y ↦ β, Z ↦ γ)

The interior scope loses `X`; the conversion scope keeps it.  Both keep
`Δ₀`'s store, unchanged.
At `Δᶜ`, `unseal Z` converts `Z` to `X`, because `Z` names `γ`,
`γ` stores the representation type `α`, and `X` is the live type variable of `α`.
Thus a `boundary` instance can type

    Δᵢ ∣ · ⊢ M : Z
    Δᶜ ⊢ unseal Z : Z ⇝ X
    ----------------------------------------
    Δ₀ ∣ Γₜ ⊢ M ⟪ ↓X, ↥Z, unseal Z ⟫ : X

The body type is read in the interior and conversion contexts.  The result
type is read in the conversion and exterior contexts.  Naming removes the
index weakening, not this four-context fact.

# Conversion typing

There is one judgment per sort, all read at a conversion context and
with no polarity index: `Δ ⊢ᵐ g : A ⇝ B` for a middle, `Δ ⊢ᵀ t : A ⇝ B`
for a tail and `Δ ⊢ c : A ⇝ B` for a conversion.

    (conv-id)       Base A
                    -------------------
                    Δ ⊢ᵐ id A : A ⇝ A

    (conv-idv)      X is in scope in Δ
                    -------------------
                    Δ ⊢ᵐ id X : X ⇝ X

    (conv-fun)      Δ ⊢ c : A′ ⇝ A    Δ ⊢ d : B ⇝ B′
                    ----------------------------------
                    Δ ⊢ᵐ c ↦ d : (A ⇒ B) ⇝ (A′ ⇒ B′)

    (conv-all)      under(X,α,Δ) ⊢ c : A ⇝ B
                    ---------------------------
                    Δ ⊢ᵐ ∀X.c : ∀X.A ⇝ ∀X.B

    (conv-mid)      Δ ⊢ᵐ g : A ⇝ B
                    ---------------
                    Δ ⊢ᵀ g : A ⇝ B

    (conv-seal)     Δ ∋ X := A
                    -------------------
                    Δ ⊢ᵀ seal X : A ⇝ X

    (conv-seal-seq) Δ ⊢ᵀ t : A ⇝ R    Δ ∋ X := R    t is not an identity
                    -----------------------------------------------------
                    Δ ⊢ᵀ t ; seal X : A ⇝ X

    (conv-tail)     Δ ⊢ᵀ t : A ⇝ B
                    ---------------
                    Δ ⊢ t : A ⇝ B

    (conv-unseal)   Δ ∋ X := A
                    --------------------
                    Δ ⊢ unseal X : X ⇝ A

    (conv-unseal-seq)
                    Δ ∋ X := R    Δ ⊢ c : R ⇝ B
                    c is not an identity    NoCancel X c
                    -------------------------------------
                    Δ ⊢ unseal X ; c : X ⇝ B

`Base A` has exactly the cases `A = ℕ` and `A = 𝔹`.  `conv-seal` is the
soundness gate: a seal must cite a live, represented binder
(`proof/Adversary.agda`).  The two chain premises keep the forms TIGHT:
a chain never extends an identity (the bare `seal X`/`unseal X` is that
case), and `NoCancel` rules out `unseal X ; seal X`, which is `id X`.
Compound identities are structural.  Define them by:

    mkId X       = id X
    mkId ℕ       = id ℕ
    mkId 𝔹       = id 𝔹
    mkId (A⇒B)   = mkId A ↦ mkId B
    mkId (∀X.A)  = ∀X.mkId A

The conversion born at an instantiation is mutually defined.  The
compiler writes `revealₓ(C)` into every `ν` it emits, and no rule mints
one at run time:

    revealₓ(X)       = unseal X
    revealₓ(Y)       = id Y                 if X and Y are distinct
    revealₓ(A⇒B)    = concealₓ(A) ↦ revealₓ(B)
    revealₓ(∀Y.A)   = ∀Y.revealₓ(A)

    concealₓ(X)      = seal X
    concealₓ(Y)      = id Y                 if X and Y are distinct
    concealₓ(A⇒B)   = revealₓ(A) ↦ concealₓ(B)
    concealₓ(∀Y.A)  = ∀Y.concealₓ(A)

Both operations are identities on base types.  (The pre-`ν` boundary
rules also used `instRevealₓ(c)`, the same mint pushed through an
existing conversion, fusing the crossed conversion with the reveal.  The
`Nu` rules stack the two instead, and `instRevealₓ`/`instConcealₓ` were
deleted on 2026-09-24.)

## Composition

`Δ ⊢ c₁ ⨟ c₂` is `c₁` followed by `c₂`, at one conversion context `Δ`
(Agda `_⊢_⨟_`, `Conversion.agda` §4b).  It is an untyped function with
one operator per sort (`⨟`, `⨟ᵀ` for a tail then a conversion, `⨟ᵀᵀ`
for two tails, `⨟ᵐ` for two middles), and it recurses on the sorts
alone.  It takes the context because of one clause: where `seal X`
meets `unseal Y` it writes the identity at `X`'s representation, and
only `Δ` knows that representation (`repOf Δ X`, which reads the lookup
square through `Lookup.agda`'s `∋:=?`); under `∀X` it composes at
`under(X,α,Δ)`.  In the clauses below `Δ ⊢` is left implicit where it is
only passed on.

    unseal X ⨟ c₂              =  unseal X ;ˢ c₂
    (unseal X ; c₁) ⨟ c₂       =  unseal X ;ˢ (c₁ ⨟ c₂)
    t ⨟ c₂                     =  t ⨟ᵀ c₂

    t ⨟ᵀ t₂                    =  t ⨟ᵀᵀ t₂
    seal X ⨟ᵀ unseal Y         =  mkId A        where Δ ∋ X := A
    seal X ⨟ᵀ (unseal Y ; c)   =  c
    (t ; seal X) ⨟ᵀ unseal Y   =  t
    (t ; seal X) ⨟ᵀ (unseal Y ; c)
                               =  t ⨟ᵀ c
    g ⨟ᵀ unseal Y              =  unseal Y      g's target is a variable, so g = id Y
    g ⨟ᵀ (unseal Y ; c)        =  unseal Y ; c  likewise

    t ⨟ᵀᵀ seal Y               =  t ;ˢ seal Y
    t ⨟ᵀᵀ (t₂ ; seal Y)        =  (t ⨟ᵀᵀ t₂) ;ˢ seal Y
    g ⨟ᵀᵀ g₂                   =  g ⨟ᵐ g₂
    seal X ⨟ᵀᵀ g₂              =  seal X        g₂'s source is a variable, so g₂ = id X
    (t ; seal X) ⨟ᵀᵀ g₂        =  t ; seal X    likewise

    id A ⨟ᵐ g₂                 =  g₂
    (s ↦ c) ⨟ᵐ id B            =  s ↦ c
    (s ↦ c) ⨟ᵐ (s′ ↦ c′)       =  (s′ ⨟ s) ↦ (c ⨟ c′)      the domain flips
    ∀X.s ⨟ᵐ id B               =  ∀X.s
    ∀X.s ⨟ᵐ ∀X.s′              =  ∀X.(s ⨟ s′)              at under(X,α,Δ)

The remaining pairs of middles (an arrow against a `∀`) are ruled out by
typing, and the function returns its first argument there.  Where a
seal meets an unseal the clauses compare no names: typing forces the
two to denote one representation (`cancel-name`, `proof/IdLayer.agda`).
The two smart constructors keep the result tight:

    t ;ˢ seal X        =  seal X            if t is an identity
                       =  t ; seal X        otherwise

    unseal X ;ˢ t      =  unseal X          if t is an identity
                       =  cancelₓ(t)        otherwise
    unseal X ;ˢ c      =  unseal X ; c      if c is an unseal chain

    cancelₓ(g)         =  unseal X ; g
    cancelₓ(seal Y)    =  id X              if X = Y
                       =  unseal X ; seal Y otherwise
    cancelₓ(t ; seal Y) = t′ ;ˢ seal Y      if cancelₓ(t) is a tail t′
                       =  unseal X ; (t ; seal Y)   otherwise

Composition is well typed (`⊢⨟`, `proof/Compose.agda`):

    Unique names in Δ    Δ ⊢ c₁ : A ⇝ B    Δ ⊢ c₂ : B ⇝ C
    ----------------------------------------------------
    Δ ⊢ (Δ ⊢ c₁ ⨟ c₂) : A ⇝ C

The chain premises `IsId` and `NoCancel` of the result are rebuilt by
the proof, never assumed; the uniqueness premise is what makes
`repOf Δ X` the looked-up `A` (`repOf-sound`) and settles the cancelled
seal/unseal pair (`∋:=-det`).

# Term typing

The judgment is `Δ ∣ Γₜ ⊢ M : A`, with type context `Δ` and term
context `Γₜ`.

    (⊢`)       x : A ∈ Γₜ
               -----------
               Δ ∣ Γₜ ⊢ x : A

    (⊢$)       -----------
               Δ ∣ Γₜ ⊢ n : ℕ

    (⊢true)    --------------
               Δ ∣ Γₜ ⊢ true : 𝔹

    (⊢false)   ---------------
               Δ ∣ Γₜ ⊢ false : 𝔹

    (⊢ƛ)       Δ ⊢ᵗ A    Δ ∣ Γₜ, x:A ⊢ N : B
               ----------------------------
               Δ ∣ Γₜ ⊢ λx:A.N : A ⇒ B

    (⊢·)       Δ ∣ Γₜ ⊢ L : A ⇒ B    Δ ∣ Γₜ ⊢ M : A
               -----------------------------------
               Δ ∣ Γₜ ⊢ L · M : B

    (⊢Λ)       Value N    under(X,α,Δ) ∣ ⇑Γₜ ⊢ N : C
               -------------------------------------
               Δ ∣ Γₜ ⊢ ΛX.N : ∀X.C

    (⊢ν)       Δ ⊢ᵗ A    Δ ⊢ᶜ A ~ R    Δ ∣ Γₜ ⊢ L : ∀X.C
               Δ₀ = allocate(α:=R, Δ)
               BoundaryWf Δ₀ [ bind X α ] Δᵢ Δᶜ
               Δᶜ ⊢ c : C ⇝ B
               Δ ⊢ᵗ B
               ---------------------------------------
               Δ ∣ Γₜ ⊢ νX:=A · L ⟨ c ⟩ : B

Here `⇑Γₜ` weakens every type in the term context through the fresh
type binder.

`⊢ν` accepts ANY conversion `c` whose types line up.  Its source is the
operator's body `C`, and it is read at the conversion context of the
scope `[ bind X α ]` over the allocation, which is the context the `Nu`
rules put `c` at (Agda: `TyBetaBoundary` at `allocate R Δ`).  The
compiler always writes `c = revealₓ(C)`, whose target is `C[X:=A]` read
through the cell, so a compiled `νX:=A · L ⟨ revealₓ(C) ⟩` has the
System F type `C[X:=A]` (`compile-ν`, `proof/Compile.agda`).  Until the
merge port the generality was used at run time, by the pushed `ν` of the
retired `Nu-⟪⟫`; no rule builds a `ν` now, so every `ν` in the run of a
compiled program is one the compiler wrote.

Mechanization note.  Agda's `⊢ν` compares the result by representation,
`allocate R Δ ⊢ B ≈ Cₑ ⊣ Δᶜ`, exactly as `boundary` compares its exterior;
with names that is the identification of `c`'s target with `B` written
into the rule above.

`⊢Λ`'s `Value N` premise is **the value restriction**, the first of the two
experiments.  It is what licenses the absence of `ξ-Λ`: a well-typed
`ΛX.N` is already a value, so there is nothing a congruence under the
binder could do.

The boundary rule and `⊢ν` are the non-System-F rules:

    (boundary) BoundaryWf Δ Θ Δᵢ Δᶜ
               Δᵢ ∣ · ⊢ M : Bᵢ
               Δᶜ ⊢ c : Bᵢ ⇝ Bₑ
               Δ ⊢ᵗ Bₑ
               --------------------------------
               Δ ∣ Γₜ ⊢ M ⟪ Θ , c ⟫ : Bₑ

With variables as names no scope premises are needed.  `Bᵢ` is in scope
in `Δᵢ` by its typing premise, and every name live in the interior is
live in the conversion context — an unbind is the only thing that removes a
name and the conversion reading skips unbinds (`int⇒conv-live`,
Boundary.agda §3a) — so it is in scope in `Δᶜ` too.  `Bₑ` is in scope in
`Δ` by `Δ ⊢ᵗ Bₑ`, and the conversion reading never removes an exterior
name (`conversion-live`), so it is in scope in `Δᶜ` too.

The empty term context in the second premise is load-bearing: substitution
does not descend into a boundary.

Mechanization note.  In de Bruijn form the same variable can have
different indices in the three name maps, so Agda's `boundary` carries two
weakening premises, `Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ` and `Δ ⊢ Bₑ ≈ Cₑ ⊣ Δᶜ` —
**the same relation on both sides**, since the exterior and the
conversion context now share one store (the bind-prefix-crossing
`SameTyExt` went with the bind block).  Their job is to pin the
conversion's endpoints `Cᵢ`/`Cₑ` to the spellings of `Bᵢ`/`Bₑ` in `Δᶜ`,
not to put anything in scope; with names they are the identifications
`Cᵢ = Bᵢ`, `Cₑ = Bₑ` already written into the rule above.  A worked
instance with all three maps distinct is notes/TwoSpellings.md.

# Values and conversion classification

Classification is by conversion constructor, subject to conversion typing:

    inert tail  ::= id X | c ↦ d | ∀X.c | seal X | t ; seal X
    active      ::= id ℕ | id 𝔹 | unseal X | unseal X ; c

The two classes are total on typed conversions and disjoint
(`act-or-inert`, `act-not-inert`).  Every inert conversion is a tail
(Agda `Inert (tail t)` from `InertTail t`).

A value carries AT MOST ONE boundary:

    U ::= n | true | false | λx:A.N | ΛX.V          simple values
    V, W ::= U | U ⟪ Θ , t ⟫   if t is an inert tail

(Agda `Simple`, with `S-$`, `S-true`, `S-false`, `S-ƛ`, `S-Λ`, and
`Value`, with `V-simple` and `V-⟪⟫ : Simple U → InertTail t →
Value (U ⟪ Θ , tail t ⟫)`.)  A simple value has a type that is not a
variable, so a value boundary's conversion has a non-variable source: it
has no unseal chain, and it is a tail.  The one active tail is `id` at a
base type, which `Drop` removes.  A second boundary on a value is not
a value but a `Merge` redex, and a boundary with an active conversion is
not a value.

`ΛX.N` is a value only if `N` is a value.  On well-typed terms that is
automatic, because `⊢Λ` demands it; the premise is kept on `S-Λ` so
that `Value` is a relation on untyped terms.

# Frame-exact term substitution

`N[x:=W:A]` is capture-avoiding term substitution, with the argument type
carried explicitly.  It does not enter a boundary, because boundary bodies
are term-closed.  When an occurrence of `x` lies under `ΛX`, the substituted
value crosses that binder in a boundary:

    W  becomes  W ⟪ ↓X , mkId A ⟫

in named notation.  Agda additionally weakens free representation indices
and the displayed type through the new abstract representation binder.
This is `_[_∶_]ᵐ`, not ordinary raw substitution; it is why `Beta` is
frame-exact.

# Reduction

The judgment is

    Δ ⊢ M -→ M′ ∣ δ            δ ::= none | new R

where `δ` is the change the step made to the **store**, the second
experiment.  The contractum is read one context later:

    apply none Δ      = Δ
    apply (new R) Δ   = allocate(α:=R, Δ)

The premises naming interior and conversion contexts are part of the
reduction relation even when the redex's typing can reconstruct them.

## Computational rules

Rules are stated for a well-typed redex, with variables as names,
`U` ranging over simple values and `V`, `W` over values; a `where`
clause defines a context or a type the contractum reads.  Commentary is
in the appendix at the end of this file, keyed by rule.

    (Nu-Λ)      Δ ⊢ νX:=A · (ΛX.V) ⟨ d ⟩
                    -→ V ⟪ [ bind X α ] , d ⟫ ∣ new R
                where Δ ⊢ᶜ A ~ R

    (Beta)      Δ ⊢ (λx:A.N) · W -→ N[x:=W:A] ∣ none

    (Peel)      Δ ⊢ (U ⟪ Θ , c ↦ d ⟫) · W
                    -→ (U · (W ⟪ dual Θ , c ⟫)) ⟪ Θ , d ⟫ ∣ none

    (Nu-⟪Λ⟫)    Δ ⊢ νX:=A · ((ΛX.V) ⟪ Θ , ∀X.c ⟫) ⟨ d ⟩
                    -→ (V ⟪ Θ , c ⟫) ⟪ [ bind X α ] , d ⟫ ∣ new R
                where Δ ⊢ᶜ A ~ R

    (Merge)     t₁ is an inert tail
                --------------------------------------------------
                Δ ⊢ (U ⟪ Θ₁ , t₁ ⟫) ⟪ Θ₂ , c₂ ⟫
                    -→ U ⟪ Θ₂ ++ Θ₁ , Δ⋉ᶜ ⊢ t₁ ⨟ c₂ ⟫ ∣ none
                where Δ ⊢ᶜ Θ₂ ++ Θ₁ ⇒ Δ⋉ᶜ

    (Drop)      U is simple    Base A
                --------------------------------------
                Δ ⊢ U ⟪ Θ , id A ⟫ -→ U ∣ none

There are six computational rules and four congruences, ten in all.  `Merge` fires whatever the outer conversion `c₂` is: at an active
one it does what the retired `CancelR` (`seal X` then `unseal X`) and
`IdPush` (`id X` then `unseal X`) did, and at an inert one it merges a
pair that used to stack.  If the composite is `id` at a base type, a
drop fires next.

## Congruence rules

A congruence passes the store change `δ` up and shifts the redex's
siblings by it (`↑ᴹ[δ]` on a term, `↑ᴮ[δ]` on a scope; the identity
with names).

    (ξ-·-l)     Δ ⊢ L -→ L′ ∣ δ
                ----------------------------------
                Δ ⊢ L · M -→ L′ · ↑ᴹ[δ]M ∣ δ

    (ξ-·-r)     Δ ⊢ M -→ M′ ∣ δ
                ----------------------------------
                Δ ⊢ V · M -→ ↑ᴹ[δ]V · M′ ∣ δ

    (ξ-ν)       Δ ⊢ L -→ L′ ∣ δ
                ------------------------------------------
                Δ ⊢ νX:=A · L ⟨ c ⟩ -→ νX:=A · L′ ⟨ c ⟩ ∣ δ

    (ξ-⟪⟫)      Δ ⊢ⁱ Θ ⇒ Δᵢ    Δᵢ ⊢ M -→ M′ ∣ δ
                --------------------------------------
                Δ ⊢ M ⟪ Θ,c ⟫ -→ M′ ⟪ ↑ᴮ[δ]Θ , c ⟫ ∣ δ

    (done)      ----------------
                Δ ⊢ M -→* M

    (then)      Δ ⊢ L -→ M ∣ δ    apply δ Δ ⊢ M -→* N
                ---------------------------------------
                Δ ⊢ L -→* N

# A Merge run excerpt

`Examples.agda` §8 contains the closed program, compiled from the
source `SourceExamples.S₀`,

    ((ΛX. λx:X.
        ((ΛY. λy:(∀Z.Z⇒Y). y[ℕ] · 7) [X]
          · (ΛZ. λy:Z. x))) [ℕ]) · 7

and proves that it reaches `7` in fifteen steps.  The following excerpt
was generated by `Show.showRun 0 15 S₀-⊢`
(`scripts/render_term.sh 'showRun 0 15 S₀-⊢' 'open import strong-rep-nu.Examples'`),
not transcribed from indices.  The renderer prints the store as
`Ξ = [...]` with the **newest** cell first, so `α` is the most recently
allocated one.  The eleventh state onwards is the whole tail, at the
store

    Ξ = [α := ℕ , β := γ , γ := ℕ]

which the five steps leave alone — none of them allocates.  The states,
as rendered:

    (((((7 ⟪ ↓Z , seal Z ⟫) ⟪ ↓X , id Z ⟫) ⟪ ↥X , ↓Y , seal Y ⟫) ⟪ ↥Y , unseal Y ⟫) ⟪ ↥Z , unseal Z ⟫)
      --[Merge]-->
    ((((7 ⟪ ↓X , ↓Z , seal Z ⟫) ⟪ ↥X , ↓Y , seal Y ⟫) ⟪ ↥Y , unseal Y ⟫) ⟪ ↥Z , unseal Z ⟫)
      --[Merge]-->
    (((7 ⟪ ↥X , ↓Y , ↓X , ↓Z , seal Z ; seal Y ⟫) ⟪ ↥Y , unseal Y ⟫) ⟪ ↥Z , unseal Z ⟫)
      --[Merge]-->
    ((7 ⟪ ↥Y , ↥X , ↓Y , ↓X , ↓Z , seal Z ⟫) ⟪ ↥Z , unseal Z ⟫)
      --[Merge]-->
    (7 ⟪ ↥Z , ↥Y , ↥X , ↓Y , ↓X , ↓Z , id ℕ ⟫)
      --[Drop]-->
    7

Every step merges the innermost pair, and each shows one clause of the
composition:

  1. `seal Z ⨟ id Z = seal Z`: a middle whose source is a variable is an
     identity and is absorbed.  (Before `Merge` this pair stacked, and
     the layer `⟪ ↓X , id Z ⟫` waited for an `IdPush` from outside.)
  2. `seal Z ⨟ seal Y = seal Z ; seal Y`: two seals CHAIN.  The chain
     exists because `β := γ` is an alias cell: `Y` names `β`, whose
     stored representation is the representation VARIABLE `γ`, which
     `Z` names.
  3. `(seal Z ; seal Y) ⨟ unseal Y = seal Z`: the unseal cancels the
     last seal of the chain, what `CancelR` did on the open
     representation `β := γ`.
  4. `seal Z ⨟ unseal Z = mkId ℕ = id ℕ`: the identity at `Z`'s
     representation, which composition reads off the merged conversion
     context (`repOf`).
  5. `Drop` removes the identity at a base type.

The trace makes the two universes visible: the store cell `β := γ` holds
an open representation, while `↥Y` gives `β` a type variable.  Every
boundary is changes-only, and `Merge` keeps both frames, MERGED, so the
scope grows by the outer frame at every step while the tower shrinks by
one boundary.  No VALUE carries two boundaries: each stacked pair in
the trace is a `Merge` redex.  Merging
costs this run one step fewer than the sixteen it took with `CancelR`
and `IdPush`.

# Metatheory

The public surface is in `TypeSafety.agda`, and every statement is read
against the store: a step's contractum lives at `apply δ Δ`, and a run's
final term lives at `runCtx r`.

    Progress
      Δ ∣ · ⊢ M : A
      -----------------------------------------------------
      Value M  or  there exist M′ and δ with Δ ⊢ M -→ M′ ∣ δ

    Preservation
      WfCtx Δ
      Δ ∣ · ⊢ M : A
      Δ ⊢ M -→ M′ ∣ δ
      ------------------------
      apply δ Δ ∣ · ⊢ M′ : A

    PreservationWf
      WfCtx Δ
      Δ ∣ · ⊢ M : A
      Δ ⊢ M -→ M′ ∣ δ
      ----------------
      WfCtx (apply δ Δ)

    Preservation*
      WfCtx Δ
      Δ ∣ · ⊢ M : A
      r : Δ ⊢ M -→* M′
      ------------------------
      runCtx r ∣ · ⊢ M′ : A

    TypeSafety
      WfCtx Δ
      Δ ∣ · ⊢ M : A
      r : Δ ⊢ M -→* N
      ---------------------------------------------------------
      Value N  or  there exist N′ and δ with runCtx r ⊢ N -→ N′ ∣ δ

    Determinism
      Δ ∣ Γₜ ⊢ M : A
      Δ ⊢ M -→ M₁ ∣ δ₁    Δ ⊢ M -→ M₂ ∣ δ₂
      -------------------------------------
      M₁ = M₂  and  δ₁ = δ₂

    Values do not step
      Value V
      ----------------------------------------------
      there are no V′, δ with Δ ⊢ V -→ V′ ∣ δ

Determinism concludes the **pair**: the contractum and the store change
are both functions of the redex.

Progress needs no global `WfCtx` premise: each boundary typing derivation
already contains its `BoundaryWf`.  Determinism does need the redex's typing
derivation, from which it recovers uniqueness of all relevant name maps.

Preservation needs `WfCtx Δ`.  Here is the counterexample to the
premise-free statement.  Take

    Ξ = (α := ℕ)
    Γ = (X ↦ α, Y ↦ α)

and the redex `(λx:ℕ. ΛZ. λy:ℕ. x) · 0`.  It mentions neither `X` nor
`Y`, so it can be typed despite the duplicate naming of `α`.  `Beta`
substitutes the value `0` under the `ΛZ`, so it wraps it in that binder's
dual; the contractum is `ΛZ. λy:ℕ. (0 ⟪ ↓Z , id ℕ ⟫)` (rendered).  That
boundary's `BoundaryWf` contains `WfCtx (under(Z,γ,Ξ ∣ Γ))`, and that is
impossible: one representation variable has two live type variables.  In
the named presentation `WfCtx` therefore reads as distinct-name, no-alias
hygiene; in ordinary mathematical practice it is maintained by
alpha-conversion.

(Until 2026-09-24 the counterexample was a type application
`(ΛZ.0) [ℕ,ℕ]`, whose `TyBeta` contractum minted the ill-formed
`BoundaryWf`.  With `ν` that redex no longer exists in a well-typed
form: `⊢ν` itself carries `BoundaryWf (allocate(α:=R,Δ)) [bind X α] …`,
so a `ν` cannot be typed at a duplicate name map at all.  The `Beta`
counterexample above was checked with the derivation-producing checker
on 2026-09-24: `infer` succeeds on the redex and fails on the contractum
and on `νX:=ℕ · (ΛZ.0) ⟨ id ℕ ⟩`.  That is the checker's verdict, not a
machine-checked refutation.)

The four congruences all rest on one lemma, the **sibling shift**
(`ShiftTyping`, `proof/RepWeaken.agda`): if `Δ ∣ Γₜ ⊢ M : A` and `R` is a
well-formed representation at `Δ`'s store, then
`allocate(α:=R,Δ) ∣ Γₜ ⊢ ↑ᴹ[new R]M : A`.  The type does not change,
because an allocation only renumbers the representation universe.  It is
what replaced the bind-block weakening the old `Peel` consumed.

## Color preservation

`ColorPreservation.agda` states the design law that reduction never
changes which type variables a subterm can see.  A hole's **color** is
the scope map `Γ` at that hole, and `Residuals` follows a position
through a run, recording the representation renaming `ρ` the run
delivered to it.

    ScopeMapPreservation
      WfCtx Δ
      Δ ∣ · ⊢ L : A
      Residuals rs C M ρ D N
      Δ ⊢C C ⊣ Δ₁        runCtx rs ⊢C D ⊣ Δ₂
      ---------------------------------------
      Γ of Δ₂  =  ρ applied to Γ of Δ₁

    ColorPreservation
      same premises
      ------------------------------------
      |Γ of Δ₂|  =  |Γ of Δ₁|

The target position is read at `runCtx rs`, the context the run ends at,
not at `Δ`: allocating a cell renumbers the ambient name map, which is
exactly the `ρ` the equation already reports.  Both statements have
closed forms at the empty ambient, premise-free beyond the typing.

# The source language and `compile`

The run-time language has no type application, so plain System F is a
separate SOURCE language (`Source.agda`):

    M, N ::= x | n | true | false | λx:A. N | M · N | ΛX. N | M [A]

It shares `Ty` and the term context with the run-time language and has
no boundaries, representations or reduction.  Its judgement
`n ∣ Γₜ ⊢ˢ M : A` is over a COUNT `n` of type variables (`n ⊢ˢ A`: the
free variables of `A` are below `n`), and it carries the same value
restriction as the run-time `⊢Λ`:

    (⊢ˢΛ)      SValue N    n+1 ∣ ⇑Γₜ ⊢ˢ N : C
               ------------------------------
               n ∣ Γₜ ⊢ˢ ΛX.N : ∀X.C

    (⊢ˢ[])     n ∣ Γₜ ⊢ˢ L : ∀X.C    n ⊢ˢ A
               ----------------------------
               n ∣ Γₜ ⊢ˢ L [A] : C[X:=A]

The other rules are the System F ones.  `inferˢ` is a checker that
builds these derivations.

`compile` (`Compile.agda`) is defined on typing DERIVATIONS, because the
conversion it writes needs the operator's type.  It is structural except
at type application:

    ⟦ L [A] ⟧  =  νX:=A · ⟦L⟧ ⟨ revealₓ(C) ⟩        where  L : ∀X.C

Source values compile to run-time values (`compile-value`), which is
what `⊢Λ`'s premise needs.  The theorems (`CompileTyping.agda`, proofs
in `proof/Compile.agda`):

    compile-⊢
      WfCtx Δ
      CtxWf Δ Γₜ          every type in Γₜ is well formed at Δ
      |Γ of Δ| = n
      d : n ∣ Γₜ ⊢ˢ M : A
      ----------------------
      Δ ∣ Γₜ ⊢ ⟦d⟧ : A

    compile-closed
      d : 0 ∣ · ⊢ˢ M : A
      ---------------------
      · ∣ · ⊢ ⟦d⟧ : A

    compile-safe
      d : 0 ∣ · ⊢ˢ M : A
      r : · ⊢ ⟦d⟧ -→* N
      ---------------------------------------------------------
      Value N  or  there exist N′ and δ with runCtx r ⊢ N -→ N′ ∣ δ

`CtxWf Δ Γₜ` is needed.  Without it `compile-⊢` is false for open terms:
with `n = 0`, `Δ` empty and `Γₜ = x : ∀Y.Z` for a variable `Z` that is
not in scope, `x [ℕ]` is a source derivation (the source variable rule
does not check its type), but `⊢ν` demands `Δ ⊢ᵗ B` of the result type
`B`, which names `Z`.  (In Agda this is `Γ = [∀ (` 5)]` at `n = 0`.)
The `⊢ν` case is `compile-ν`: its conversion premise is the typing of
`revealₓ(C)` at the conversion context of `[bind X α]` over the
allocation, which is the construction the old `preserve-TyBeta` did at
run time.

`SourceExamples.agda` writes each of the twenty plain-System-F programs
of `Examples.agda` as source and proves, by `refl`, that `compile` of the
derivation `inferˢ` builds for it IS the run-time term `Examples.agda`
runs.

# The six weakening repairs

The named presentation makes the same name remain the same name, but it
does not hide why the Agda carries relational witnesses.  Six repairs
were installed, each after a machine-checked defect.  Since the merge
port (2026-09-24) three premises are live: `conv-bind-live`, `Peel`'s
`s′`, and `Merge`'s pair `t₁′`/`c₂′`, which inherits the lesson of the
`X′` and `A′` rows (the inner conversion is read at Θ₁'s own conversion
context, not at the merged one).  The two `Nu-⟪⟫` rows went with that
rule.

| defect | repair | status | what naming removes | what survives |
|---|---|---|---|---|
| `strong-rep-store/notes/ReUnlockWall.agda` | `conv-bind-live` | live | a repeated insertion position | the conversion reading is a union and differs from the interior |
| `strong-rep-store/notes/ForallPayloadWall.agda`, `TyPeelR-⟪⟫` | carry `Bᵢ′` with `_⊢_≈_⊣_` | retired with `Nu-⟪⟫`, 2026-09-24 | reindexing the interior annotation | it had to be readable in both the interior and conversion contexts |
| `strong-rep-store/notes/ForallPayloadWall.agda`, `IdPush` | carry `X′` with `_⊢_≈_⊣_` | subsumed by `Merge`'s `t₁′`, 2026-09-24 | reindexing the pushed name | the name must be live at the inner and merged conversion contexts |
| `notes/CancelRShiftWall.agda` (deleted 2026-09-24; git history) | carry `A′` from `Θ₁`'s own conversion context | subsumed by `Merge`'s `t₁′`, 2026-09-24 | the bind-prefix shift, which no longer exists | the type is still read at two different NAME MAPS, `Θ₁`'s and the merged one |
| `notes/CrossingAudit.agda` and `notes/PeelPremise.agda` | carry `s′` with `SameConv` | live | reindexing the domain conversion across the dual | the original and dual conversion contexts remain different |
| `strong-rep-store/notes/AddLock0Wall.agda` (against `TyPeelR-⟪⟫`) | carry `s″` with `SameConv` | retired with `Nu-⟪⟫`, 2026-09-24 | reindexing through the new unbind and old binds | both conversion readings and the old context's representation-rebased view were premises |

# Notes ↔ Agda correspondence

The rule names below are the Agda constructor names.

## Contexts, the store, and boundary scopes

| notes | Agda | presentation/mechanization gap |
|---|---|---|
| `Ξ ∣ Γ` | `Ctxᵗ = reps ∣ names` | none |
| `allocate(α:=R,Δ)` | `allocate R Δ` | the fresh cell is index 0 and everything else shifts; with names nothing moves |
| `δ ::= none \| new R` | `Alloc`, `none`/`new` | none |
| `apply δ Δ` | `apply` | none |
| `runCtx r` | `runCtx` | none |
| `↑ᴹ[δ]M`, `↑ᴮ[δ]Θ` | `↑ᴹ[_]`, `↑ᴮ[_]` (`renᴹᴿ suc`, `renᴮᴿ suc`) | the named shift is the identity: ordinary positions never move |
| `Θ = ⟨ δ₁ , δ₂ ⟩` | `Boundary = List Change` | an alias; a scope IS its change list, stored head-last |
| `dual Θ` | `dual` | none |
| `Θ ++ dual Θ` | `rewind Θ = dual Θ ++ Θ` | no rule builds one since 2026-09-23 |
| `Θ₂ ++ Θ₁` (acting order) | `Θ₁ ++ Θ₂` (head-last) | nothing shifts: both scopes are spelled at the same store |
| `[ bind X α ]` | `inst [] = TyBetaBoundary = bind 0 0 ∷ []` | the outer layer of every `Nu` contractum |
| `Θ` under that bind | `liftᴮ Θ = map shiftChange Θ` | one shift in each universe, because it is read one allocation later; `inst Θ = liftᴮ Θ ++ (bind 0 0 ∷ [])` is the two layers stacked |

## Formation, conversion, and term typing

| notes | Agda constructor | presentation/mechanization gap |
|---|---|---|
| `wf-var`, `wf-ℕ`, `wf-𝔹`, `wf-⇒`, `wf-∀` | same names in `Ctx.agda` | named binders replace `underΛ` index shifts |
| representation formation | `wfᴿ-var`, `wfᴿ-ℕ`, `wfᴿ-𝔹`, `wfᴿ-⇒`, `wfᴿ-∀` | free Greek variables and local Latin binders replace the mixed index cutoff |
| `unbind`, `bind` | `step-unbind`, `step-bind` | membership/freshness replaces positional insert/delete evidence |
| interior changes | `changes[]`, `changes∷` | named sequences suppress index shifts only |
| conversion changes | `conv[]`, `conv-unbind`, `conv-bind`, `conv-bind-live` | the no-op re-bind remains semantically visible |
| `BoundaryWf` | `bw` | three fields only — exterior `WfCtx` and the two readings; output well-formedness is derived in both presentations |
| middles, tails, conversions `g`, `t`, `c` | `Mid` (`id`, `_↦_`, `` `∀ ``), `Tail` (`mid`, `seal`, `_⨾seal_`), `Conv` (`tail`, `unseal`, `unseal_⨾_`) | the injections `mid`/`tail` (and `⌞ g ⌟ = tail (mid g)`) are implicit here; `;` is `⨾` |
| `IsId`, `NoCancel X c` | `IsIdᵐ`/`IsIdᵀ`/`IsIdᶜ`, `NoCancelᵀ`/`NoCancel` | none |
| `Δ ⊢ᵐ`, `Δ ⊢ᵀ`, `Δ ⊢` | `_⊢ᵐ_∶_⇝_`, `_⊢ᵀ_∶_⇝_`, `_⊢_∶_⇝_` | none |
| `conv-id`, `conv-idv`, `conv-fun`, `conv-all`, `conv-mid`, `conv-seal`, `conv-seal-seq`, `conv-tail`, `conv-unseal`, `conv-unseal-seq` | same names in `Conversion.agda` | none beyond named lookup and binders; "not an identity" is `¬ IsIdᵀ t` / `¬ IsIdᶜ c` |
| `Δ ⊢ c₁ ⨟ c₂` and its sort operators | `_⊢_⨟_`, `_⊢_⨟ᵀ_`, `_⊢_⨟ᵀᵀ_`, `_⊢_⨟ᵐ_`, with `repOf`, `_⨾sealˢ_`, `unseal_⨾ˢ_`, `cancelᵀ` | the `mkId A` of the seal-then-unseal clause is `mkId (repOf Δ X)`, whose fallback is never reached on typed input |
| `⊢⨟` | `proof/Compose.agda`, `⊢⨟` | the uniqueness premise is `Unique (names Δ)` |
| `mkId`, `revealₓ`, `concealₓ` | `mkId`, `reveal`, `conceal` | the Agda operations carry the slot as an index, not a name |
| `⊢\``, `⊢$`, `⊢true`, `⊢false`, `⊢ƛ`, `⊢·`, `⊢Λ`, `⊢ν` | same constructors in `Terms.agda` | named binders replace term/type indices; `⊢Λ`'s `Value N` is the value restriction; `⊢ν`'s bound `X` is Agda's ordinary variable 0 in `c`, and its result is compared by `≈` as in `boundary` |
| `νX:=A · L ⟨ c ⟩` | `ν A · L ⟨ c ⟩` | the name `X` is implicit (de Bruijn 0 in `c`) |
| source `M [A]`, `⊢ˢ`-rules | `Source.agda`: `_[_]`, `` ⊢ˢ` ``, `⊢ˢ$`, `⊢ˢtrue`, `⊢ˢfalse`, `⊢ˢƛ`, `⊢ˢ·`, `⊢ˢΛ`, `⊢ˢ[]` | a count `n` of type variables replaces a type context |
| `⟦d⟧` | `compile d` | defined on derivations |
| `boundary` | `boundary` | Agda has `Bᵢ/Cᵢ` and `Bₑ/Cₑ`, both related by `_⊢_≈_⊣_`; notes use one named endpoint plus paired scope conditions |
| inert tails | `InertTail`: `I-idv`, `I-fun`, `I-all`, `I-seal`, `I-seal-seq`; `Inert`: `I-tail` | none |
| active conversions | `A-idb`, `A-unseal`, `A-unseal-seq` | none |
| simple values `U` | `Simple`: `S-$`, `S-true`, `S-false`, `S-ƛ`, `S-Λ` | named binders only |
| values `V`, `W` | `Value`: `V-simple`, `V-⟪⟫` | none |

## Reduction

| notes rule | Agda constructor | presentation/mechanization gap |
|---|---|---|
| `Nu-Λ` | `Nu-Λ` | the contractum's scope is `inst []`; the conversion is `ν`'s own `c`, moved verbatim; `Value N` is retained.  Store change `new R` |
| `Beta` | `Beta` | named frame-exact substitution hides the representation-only weakening under `Λ`, not the crossing boundary.  `none` |
| `Peel` | `Peel` | `Simple V` and `Value W` are retained; `s′`/`SameConv` becomes one `c` plus scope in `Δᶜ,Δᵈ`; `W` moves verbatim.  `none` |
| `Nu-⟪Λ⟫` | `Nu-⟪Λ⟫` | the middle scope is `liftᴮ Θ`, whose shift is invisible with names; `s` and `c` move verbatim; the premises `Δ ⊢ᶜ Θ ⇒ Δᶜ` and `underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ` are recoverable from typing.  `new R` |
| `Merge` | `Merge` | `Simple U` and `InertTail t₁` are retained; the carried `t₁′` and `c₂′` with their two `SameConv`s collapse to `t₁` and `c₂` read at the merged conversion context `Δ⋉ᶜ`; the readings `Δ ⊢ⁱ Θ₂ ⇒ Δᵢ`, `Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ` and `Δ ⊢ᶜ Θ₂ ⇒ Δ₂ᶜ` are retained in Agda.  `none` |
| `Drop` | `Drop` | none; the `Simple U` and `Base A` premises are retained (typing makes `U` a literal).  `none` |
| `ξ-·-l` | `ξ-·-l` | the sibling shift `↑ᴹ[δ]` is the named identity |
| `ξ-·-r` | `ξ-·-r` | same; `Value V` is retained |
| `ξ-ν` | `ξ-ν` | none; `A` and `c` are ordinary and never shift |
| `ξ-⟪⟫` | `ξ-⟪⟫` | the scope shift `↑ᴮ[δ]` is the named identity; the explicit interior-reading premise is retained |
| — | (no `ξ-Λ`) | the value restriction removed it |
| — | (no `Nu-⟪⟫`, `CancelR`, `IdPush`) | retired 2026-09-24: `Nu-⟪⟫` is unreachable with one boundary per value, and `Merge` subsumes the other two |
| `done`, `then` | `done`, `_then_` | the tail runs at `apply δ Δ` |

For completeness, the named rules render differently from their Agda
premises only at these sites:

  1. `boundary`: `Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ` becomes one `Bᵢ` readable in
     both contexts; `Δ ⊢ Bₑ ≈ Cₑ ⊣ Δᶜ` becomes one `Bₑ`
     readable in the exterior and conversion contexts.
  2. `Peel`: `SameConv Δᵈ s′ Δᶜ s` becomes one `c` readable in
     both contexts.
  3. `Merge`: `SameConv Δ⋉ᶜ (tail t₁′) Δ₁ᶜ (tail t₁)` becomes one `t₁`
     readable at `Δ₁ᶜ` and `Δ⋉ᶜ`, and `SameConv Δ⋉ᶜ c₂′ Δ₂ᶜ c₂` one `c₂`
     readable at `Δ₂ᶜ` and `Δ⋉ᶜ`; the composite is written at `Δ⋉ᶜ`.
  4. The congruences: `↑ᴹ[ δ ]` and `↑ᴮ[ δ ]` become the identity,
     because with names an allocation renumbers nothing.

Every other premise in the displayed typing and reduction rules is present
with the same mathematical content as in `Terms.agda` or `Reduction.agda`.

# Appendix: commentary on the reduction rules

The prose that used to sit between the rules of the Reduction section,
keyed by the rule it follows.

## The computational rules: conventions

Each rule is stated for a **well-typed redex** with variables as names,
and with the metavariable convention that `U` ranges over SIMPLE values
and `V`, `W` over VALUES (so a rule written with them needs no `Simple`
or `Value` premise; Agda's `Simple U`/`Value V`/`Value W` premises are
that convention spelled out — they fix the evaluation order and are what
determinism rests on).  Everything the contractum reads that is not in
the redex (`R`, `Δ⋉ᶜ`) is determined by the redex, so it appears as a
`where` clause, and every "is in scope in both" condition the Agda rules
carry is a consequence of the readings' inclusions (`Δᵢ ⊆ Δᶜ`,
`Δ ⊆ Δᶜ`, `Δᶜ ≈ Δᵈ`, `Δ₁ᶜ ⊆ Δ⋉ᶜ`, `Δ₂ᶜ ⊆ Δ⋉ᶜ`) and of typing, and is
omitted.  The mechanization notes say which Agda
premises these were.

## Nu-Λ

`X` and `α` are the ordinary and representation binders of the event:
`ν`'s own bound name, the `Λ`'s binder alpha-renamed to it, and the cell
the step allocates.  `R` is the ordinary argument `A` read as a
representation type; the step allocates it at `α` — the allocation is
the step's store change, not part of the boundary.  The conversion `d`
is `ν`'s own, moved verbatim onto the new boundary: before 2026-09-24
this rule was `TyBeta`, whose contractum minted `revealₓ(B)` from the
annotation `B` of `(ΛX.V) [B,A]`.  The contractum is the same term when
`d` is the compiler's `revealₓ(B)`; only the origin of the conversion
changed.  `Examples.agda` §1a, rendered (`showRun 0 5 P₀-⊢`):

    Ξ = []
    ((ν X:=ℕ · (ΛY. (λx:Y. x)) ⟨ (seal X ↦ unseal X) ⟩) · 7)
      --[Nu-Λ]-->
    Ξ = [α := ℕ]
    (((λx:X. x) ⟪ ↥X , (seal X ↦ unseal X) ⟫) · 7)

(The renderer names a `Λ`'s binder and `ν`'s bound name from separate
counters, hence `ΛY` against `ν X`; they are the same variable after
the step.)

Mechanization note.  Agda carries `Value N` and `Δ ⊢ᶜ A ~ R`; the scope
is `inst []`, which is `TyBetaBoundary`.

## Peel

Mechanization note.  Agda's `Peel` carries the readings `Δ ⊢ᶜ Θ ⇒ Δᶜ`,
`Δ ⊢ⁱ Θ ⇒ Δᵢ`, `Δᵢ ⊢ᶜ dual Θ ⇒ Δᵈ` and `SameConv Δᵈ s′ Δᶜ s`: the domain
conversion is weakened from Θ's conversion context to the dual's.
With names `c` is textually unchanged, and that the two contexts name
the same representation variables is `Q`/`Q-inv` (Boundary.agda §3b), so
none of these is a premise here.  The crossed value `U` is simple,
because a value carries one boundary.  `W` **moves verbatim** — a boundary
changes names only, so the crossing argument lands at the very store it
was spelled at.  `notes/CrossingAudit.agda` refutes equality of the de
Bruijn name maps, while `notes/PeelPremise.agda` proves that they name
the same representation variables.

## Nu-⟪Λ⟫: stack, then merge

With one boundary per value, a `∀`-value is a `Λ` or a `Λ` under ONE
`∀`-conversion boundary (`canon-∀`, `proof/Canonical.agda`), so `Nu-Λ`
and `Nu-⟪Λ⟫` are total over canonical `∀`-values.  `Nu-⟪Λ⟫`'s contractum
has two outer layers: `ν`'s own `⟪ [bind X α] , d ⟫` outside, and the
crossed boundary's `⟪ Θ , c ⟫`, read under the new name, in the middle.
The crossed conversion `c` moves VERBATIM and the rule computes no
conversion from `d`.  Before 2026-09-24 this rule was `TyPeelR-Λ`, which
wrote ONE layer `⟪ bind X α ∷ Θ , instRevealₓ(c) ⟫`, fusing the crossed
conversion with the reveal; stacking was chosen over a fused contractum
(`notes/NuSketch.md`, candidates N1/N2).  Read inside out the two
layers' scopes act as `bind X α ∷ Θ`, the old fused scope
(`Nu-⟪Λ⟫-stacks-to-inst`, `proof/ShiftAudit.agda` §3).  Since the merge
port the stacked pair is a `Merge` redex, so the fusion happens on the
next step, by general composition (Jeremy kept the stacked contractum
rather than merging on construction, 2026-09-24).

## Nu-⟪Λ⟫

No term moves in this clause: the `Λ` binder becomes the binder the
allocation introduces, and the outer bind names it.  `Examples.agda`
§1b, the fourth and fifth states (`showRun 0 9 K₀-⊢`):

    Ξ = [α := 𝔹]
    (((ν Y:=X · ((ΛZ. (λx:Z. true)) ⟪ ↓X , (∀Y. (id Y ↦ id 𝔹)) ⟫) ⟨ (seal Y ↦ id 𝔹) ⟩) ⟪ ↥X , (seal X ↦ id 𝔹) ⟫) · false)
      --[Nu-⟪Λ⟫]-->
    Ξ = [α := β , β := 𝔹]
    (((((λx:X. true) ⟪ ↓Y , (id X ↦ id 𝔹) ⟫) ⟪ ↥X , (seal X ↦ id 𝔹) ⟫) ⟪ ↥Y , (seal Y ↦ id 𝔹) ⟫) · false)

The renderer names cells newest first, so after the step the new cell is
`α` (named `X`) and the old one is `β` (named `Y`).  The contractum's
innermost layer is the crossed boundary `⟪ ↓Y , id X ↦ id 𝔹 ⟫`, its
conversion the crossed `∀`'s body moved verbatim; the next is `ν`'s own
`⟪ ↥X , seal X ↦ id 𝔹 ⟫`; the outermost is the layer the first `Nu-Λ`
built.  The new cell's payload is `β`, the cell the first `Nu-Λ`
allocated, because this `ν`'s argument is the name of that cell.  The
next two steps are `Merge`s, which fuse the three layers into one:

    ((λx:X. true) ⟪ ↥Y , ↥X , ↓Y , ((seal Y ; seal X) ↦ id 𝔹) ⟫) · false

(the seventh state of the same run, rendered; its store is unchanged).

Mechanization note.  Agda also carries `Δ ⊢ᶜ Θ ⇒ Δᶜ` and
`underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ`; both are recoverable from the redex typing
(`conv-all-inv`), and the contractum does not mention `Bᵢ`.  The middle
scope is `liftᴮ Θ`, Θ shifted one step in both universes; with names
that shift is invisible and the scope is `Θ`.

## Merge

A boundary over a value's boundary.  The value `U ⟪ Θ₁ , t₁ ⟫` is
simple under ONE inert tail, and the outer conversion `c₂` is anything.
Both frames are kept, MERGED: the merge `Θ₂ ++ Θ₁` presents the outer
boundary's exterior and the inner boundary's interior, so `U` retypes
exactly where it was (`merged-interior`).  Both conversions are read at
the merged conversion context `Δ⋉ᶜ` and composed there, so the rule
writes no conversion of its own: it is `Δ⋉ᶜ ⊢ t₁ ⨟ c₂`, whatever the
two are.  `Examples.agda` §1a, the fourth and fifth states
(`showRun 0 5 P₀-⊢`):

    Ξ = [α := ℕ]
    ((7 ⟪ ↓X , seal X ⟫) ⟪ ↥X , unseal X ⟫)
      --[Merge]-->
    Ξ = [α := ℕ]
    (7 ⟪ ↥X , ↓X , id ℕ ⟫)

Here the composite is `seal X ⨟ unseal X = mkId ℕ`, the identity at
`X`'s representation, and `Drop` fires next.  This is the step the
retired `CancelR` made; the retired `IdPush` (`id X` under `unseal Y`)
is the composite `id X ⨟ unseal Y = unseal Y`.  The pairs neither rule
handled, an inert tail under an inert conversion, used to STACK on a
value; they are `Merge` redexes too (`notes/MergeSketch.md`, the census,
and the K and S runs above).

That `t₁`'s target and `c₂`'s source agree at `Δ⋉ᶜ` is a lemma, not a
premise: both weaken the redex's one middle type at one context whose
names are unique (`same-target-unique`, `proof/MoveScope.agda`).  With
names this is invisible.

Mechanization note.  Agda carries `Simple U`, `InertTail t₁`, the
readings `Δ ⊢ⁱ Θ₂ ⇒ Δᵢ` (the outer interior), `Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ` (the
inner conversion context), `Δ ⊢ᶜ Θ₂ ⇒ Δ₂ᶜ` (the outer conversion
context) and `Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ` — read at the **plain exterior** `Δ`,
since both scopes were spelled at the same store — and the two carried
spellings `t₁′` and `c₂′`, pinned by `SameConv Δ⋉ᶜ (tail t₁′) Δ₁ᶜ
(tail t₁)` and `SameConv Δ⋉ᶜ c₂′ Δ₂ᶜ c₂`.  The contractum is
`U ⟪ Θ₁ ++ Θ₂ , Δ⋉ᶜ ⊢ tail t₁′ ⨟ c₂′ ⟫`.  With names `t₁′` is `t₁` and
`c₂′` is `c₂`, in scope in the merged context because `Δ₁ᶜ ⊆ Δ⋉ᶜ` and
`Δ₂ᶜ ⊆ Δ⋉ᶜ` (`merged-conversion-exists`).  The inner spelling is read
from Θ₁'s OWN conversion context, the lesson of the 2026-09-19
`CancelR` repair.  Preservation is `preserve-Merge`
(`proof/MoveScope.agda`), which weakens both typed conversions by
`weaken-⊢` and composes them by `⊢⨟`.

## Retired rules: Nu-⟪⟫, CancelR, IdPush (2026-09-24)

These three rules were deleted by the merge port.

  * `Nu-⟪⟫` pushed a `ν` at the new name inward when the crossed
    boundary's interior was itself a `∀`-conversion boundary, minting
    that `ν`'s conversion `revealᵧ(Bᵢ[X:=Y])`, the one reveal made at
    run time.  With one boundary per value that interior is a `Λ`, so
    the rule could not fire.  Its carried spellings `Bᵢ′` and `s″`, its
    moved scope `unbind X α ∷ Θ′` and the tower-descent measure
    (`Nu-⟪⟫-height`) went with it, as did `proof/AddUnbind0.agda`.
  * `CancelR` rewrote `(V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫` to
    `V ⟪ Θ₂ ++ Θ₁ , mkId Aᵢ ⟫` (`Aᵢ` the sealed type), and `IdPush` rewrote
    `(V ⟪ Θ₁ , id X ⟫) ⟪ Θ₂ , unseal Y ⟫` to `V ⟪ Θ₂ ++ Θ₁ , unseal X ⟫`.
    Both are `Merge` at the corresponding composites, and their carried
    spellings `A′` and `X′` are `Merge`'s `t₁′`.  The facts that made
    them sound without a name-relating premise (`cancel-name`,
    `idpush-name`, `proof/IdLayer.agda`) now justify composition's
    seal-then-unseal clause.  The record of the `CancelR` weakening
    wall, `notes/CancelRShiftWall.agda`, was deleted with them.

The history of all three rules is in `notes/DECISIONS.md` and in
`Commentary.md` § Reduction.agda / Retired.

## The congruences: the sibling shift

A congruence passes the store change up and applies it to the redex's
**siblings**: after an allocation the whole program lives under one more
representation cell, so every representation occurrence in a sibling moves
up by one.  Agda writes that `↑ᴹ[ δ ]` on a term and `↑ᴮ[ δ ]` on a
boundary scope; with names it is the identity, exactly like the other
index shifts this note suppresses.  Ordinary positions never move, so no
type annotation and no conversion is touched.

## No ξ-Λ, and where reduction goes

There is **no `ξ-Λ`**: reduction does not go under a type abstraction,
because the value restriction leaves nothing there to reduce.  There is
no reduction under a term lambda either.  Reduction is call-by-value,
left-to-right, and it does proceed inside a boundary at that boundary's
interior context.

The reflexive-transitive closure used by preservation and type safety
threads the store change through:

## Runs and runCtx

`runCtx r` is the context a run `r` **ends** at: every step's change
applied in order.
