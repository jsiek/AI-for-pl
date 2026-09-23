# Strong System F with representation variables

This is the mathematical presentation of the calculus in
`SystemF/agda/strong-rep-store/` at commit `463d83be`.  The Agda uses de
Bruijn indices; this note uses names.  The named presentation is not a
different calculus: it suppresses index shifts and re-spellings, but keeps
the contexts in which types and conversions are read.

## What changed and why

Two experiments have landed since the first draft of this note, and both
are visible in every section below.

  1. **The value restriction** (2026-09-21).  `⊢Λ` requires its body to
     be a value and there is no `ξ-Λ`: nothing reduces under a type
     binder.
  2. **The store** (2026-09-22).  A boundary no longer carries a block of
     representation bindings.  The representation a ∀-elimination mints is
     allocated on the **ambient** representation context, and a reduction
     step reports the change it made to that context.  A boundary scope is
     now its change list alone, and a boundary changes **names** only.

The design note for the second is `notes/RepStoreSketch.md`; the dated
record for both is the last two entries of `notes/DECISIONS.md`.

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

    c, d ::= id A | seal X | unseal X | c ↦ d | ∀X.c

`seal X` and `unseal X` carry a type variable.  They find its
representation through the context.  Function conversions are
contravariant on the left.

## Terms

    n ∈ ℕ
    x ∈ Var

    L, M, N ::= x | n | true | false
              | λx:A. N | L · M
              | ΛX. N | L [B, A]
              | M ⟪ Θ , c ⟫

`L [B, A]` applies `L` to type argument `A`; `B` is the body-type
annotation carried by the Agda constructor `_ ·[_,_]`.  The renderer writes
only `L [A]` because `B` is an annotation, not source syntax.

`M ⟪ Θ , c ⟫` is a runtime boundary.  Its body is term-closed.
The boundary scope `Θ` determines its contexts, and `c` converts the body's
interior type to the boundary's exterior type.

## Boundary Scope

    δ ::= lock X α | unlock X α
    Θ ::= ⟨ δ₁, ..., δₘ ⟩

A boundary scope is a change sequence: `Boundary = List Change` in
Agda.  The changes are sequential and stored head-last, so the tail
acts first.

The displayed boundary notation follows `Show.agda`:

    ↓X         lock X, recording that it names α
    ↥X         unlock the type variable X for α

Thus `M ⟪ ↓Y , ↥Z , c ⟫` displays changes in the order in which they act,
and the conversion last.  The full change syntax remains `lock Y β` and
`unlock Z γ`; the Greek argument is recoverable from the displayed Latin
name.

# The two context universes

A type context is presented as

    Ξ ∣ Γ

where `Ξ` is a representation context and `Γ` maps type variables to representation variables:

    Ξ ::= · | Ξ, α abstract | Ξ, α := R
    Γ ::= · | Γ, X ↦ α

`Ξ` is the **store**: it holds every representation cell the run has
minted, interleaved with the abstract cells the `Λ`s introduced.  The Γ
context contains exactly the live type variables.  A locked type
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

    under(X,α,Δ) = (Ξ, α abstract) ∣ (Γ, X ↦ α)

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
because another name is locked or unlocked.  Therefore a re-spelling
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

    lock X α       removes X ↦ α
    unlock X α     adds X ↦ α, provided α has no live type variable

The **conversion scope** generation, written `Δ ⊢ᶜ Θ ⇒ Δᶜ`, is the union of
the variable live anywhere in the boundary:

    lock X α       is skipped
    unlock X α     adds X ↦ α if α is not live
    unlock X α     is a no-op if α already has its unique live name

The last clause is `conv-unlock-live`.  For example, a conversion reading
of `↓X` leaves `X` live; the inverse `↥X` in `Θ ++ dual Θ` must therefore
be a no-op, not a failed freshness check.  `notes/ReUnlockWall.agda`
machine-checks the old failure and the repaired readings.

Both readings are relations, but each is functional.  A well-formed
boundary witness is:

    BoundaryWf Δ Θ Δᵢ Δᶜ

It carries `WfCtx Δ` and the two readings `Δ ⊢ⁱ Θ ⇒ Δᵢ` and
`Δ ⊢ᶜ Θ ⇒ Δᶜ`, and nothing else.  Well-formedness of the two outputs is
derived.

## Derived Boundary Scopes

Change sequences are written in ACTING order (the head acts first).  The
inverse of a change swaps lock and unlock:

    (lock X α)⁻¹    = unlock X α
    (unlock X α)⁻¹  = lock X α

    dual []          = []
    dual (δ ∷ Θ)     = dual Θ ++ [ δ⁻¹ ]      -- inverses, in reverse order

The other scopes the rules build are written out at their use sites:
`Θ ++ dual Θ` (CancelR/IdPush's outer scope), `lock X α ∷ Θ`
(TyPeelR-⟪⟫'s moved scope), `unlock X α ∷ Θ` (the instantiated scope of
TyBeta and both TyPeelR), and the merge `Θ₂ ++ Θ₁`, the outer scope
acting first.  Agda's change lists are head-LAST (the tail acts first),
so its spellings are the mirror images: `dual χ = map dualChange
(reverse χ)`, `rewind Θ = dual Θ ++ Θ`, the merge is `Θ₁ ++ Θ₂`, the
moved scope is the snoc `Θ ++ (lock 0 0 ∷ [])`, and the instantiated
scope is `inst Θ = map shiftChange Θ ++ (unlock 0 0 ∷ [])`.  Nothing
shifts a representation when two scopes merge, because both were spelled
at the same store; `inst` shifts in both universes because it is read
one allocation later — with names that shift is invisible.

## A concrete boundary

Let

    Δ = (α := ℕ, β abstract) ∣ (X ↦ α, Y ↦ β)
    Θ = ⟨ ↓X, ↥Z ⟩

where `Z` names `γ`, a cell the enclosing ∀-elimination just allocated:
the boundary is read at `allocate(γ:=α, Δ)`, so

    Δ₀ = (α := ℕ, β abstract, γ := α) ∣ (X ↦ α, Y ↦ β)

Then

    Δᵢ = (α := ℕ, β abstract, γ := α)
         ∣ (Y ↦ β, Z ↦ γ)

    Δᶜ = (α := ℕ, β abstract, γ := α)
         ∣ (X ↦ α, Y ↦ β, Z ↦ γ)

The interior scope loses `X`; the conversion scope keeps it.  Both keep
`Δ₀`'s store, unchanged.
At `Δᶜ`, `unseal Z` converts `Z` to `X`, because `Z` names `γ`,
`γ` stores the representation type `α`, and `X` is the live type variable of `α`.
Thus an `env` instance can type

    Δᵢ ∣ · ⊢ M : Z
    Δᶜ ⊢ unseal Z : Z ⇝ X
    ----------------------------------------
    Δ₀ ∣ Γₜ ⊢ M ⟪ ↓X, ↥Z, unseal Z ⟫ : X

The body type is read in the interior and conversion contexts.  The result
type is read in the conversion and exterior contexts.  Naming removes the
index re-spelling, not this four-context fact.

# Conversion typing

The judgment is `Δ ⊢ c : A ⇝ B`, read at a conversion context.

    (conv-id)       Base A
                    -----------------
                    Δ ⊢ id A : A ⇝ A

    (conv-idv)      X is in scope in Δ
                    -----------------
                    Δ ⊢ id X : X ⇝ X

    (conv-unseal)   Δ ∋ X := A
                    --------------------
                    Δ ⊢ unseal X : X ⇝ A

    (conv-seal)     Δ ∋ X := A
                    ------------------
                    Δ ⊢ seal X : A ⇝ X

    (conv-fun)      Δ ⊢ c : A′ ⇝ A    Δ ⊢ d : B ⇝ B′
                    ---------------------------------
                    Δ ⊢ c ↦ d : (A ⇒ B) ⇝ (A′ ⇒ B′)

    (conv-all)      under(X,α,Δ) ⊢ c : A ⇝ B
                    --------------------------
                    Δ ⊢ ∀X.c : ∀X.A ⇝ ∀X.B

`Base A` has exactly the cases `A = ℕ` and `A = 𝔹`.  Compound
identities are structural.  Define them by:

    mkId X       = id X
    mkId ℕ       = id ℕ
    mkId 𝔹       = id 𝔹
    mkId (A⇒B)   = mkId A ↦ mkId B
    mkId (∀X.A)  = ∀X.mkId A

The conversion born at an instantiation is mutually defined:

    revealₓ(X)       = unseal X
    revealₓ(Y)       = id Y                 if X and Y are distinct
    revealₓ(A⇒B)    = concealₓ(A) ↦ revealₓ(B)
    revealₓ(∀Y.A)   = ∀Y.revealₓ(A)

    concealₓ(X)      = seal X
    concealₓ(Y)      = id Y                 if X and Y are distinct
    concealₓ(A⇒B)   = revealₓ(A) ↦ concealₓ(B)
    concealₓ(∀Y.A)  = ∀Y.concealₓ(A)

Both operations are identities on base types.  `instRevealₓ(c)` and
`instConcealₓ(c)` recurse over an existing conversion: an `id A` leaf
becomes `revealₓ(A)` or `concealₓ(A)`, existing `seal`/`unseal` leaves
stay fixed, function position flips the operation, and `∀` recurses.

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

    (⊢·[])     Δ ∣ Γₜ ⊢ L : ∀X.B    Δ ⊢ᵗ A
               ----------------------------
               Δ ∣ Γₜ ⊢ L [B,A] : B[X:=A]

Here `⇑Γₜ` weakens every type in the term context through the fresh
type binder.

`⊢Λ`'s `Value N` premise is **the value restriction**, the first of the two
experiments.  It is what licenses the absence of `ξ-Λ`: a well-typed
`ΛX.N` is already a value, so there is nothing a congruence under the
binder could do.

The boundary rule is the only non-System-F rule:

    (boundary) BoundaryWf Δ Θ Δᵢ Δᶜ
               Δᵢ ∣ · ⊢ M : Bᵢ
               Δᶜ ⊢ c : Bᵢ ⇝ Bₑ
               Δ ⊢ᵗ Bₑ
               --------------------------------
               Δ ∣ Γₜ ⊢ M ⟪ Θ , c ⟫ : Bₑ

With variables as names no scope premises are needed.  `Bᵢ` is in scope
in `Δᵢ` by its typing premise, and every name live in the interior is
live in the conversion context — a lock is the only thing that removes a
name and the conversion reading skips locks (`int⇒conv-live`,
Boundary.agda §3a) — so it is in scope in `Δᶜ` too.  `Bₑ` is in scope in
`Δ` by `Δ ⊢ᵗ Bₑ`, and the conversion reading never removes an exterior
name (`conversion-live`), so it is in scope in `Δᶜ` too.

The empty term context in the second premise is load-bearing: substitution
does not descend into a boundary.

Mechanization note.  In de Bruijn form the same variable can have
different indices in the three name maps, so Agda's `env` carries two
re-spelling premises, `Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ` and `Δ ⊢ Bₑ ≈ Cₑ ⊣ Δᶜ` —
**the same relation on both sides**, since the exterior and the
conversion context now share one store (the bind-prefix-crossing
`SameTyExt` went with the bind block).  Their job is to pin the
conversion's endpoints `Cᵢ`/`Cₑ` to the spellings of `Bᵢ`/`Bₑ` in `Δᶜ`,
not to put anything in scope; with names they are the identifications
`Cᵢ = Bᵢ`, `Cₑ = Bₑ` already written into the rule above.  A worked
instance with all three maps distinct is notes/TwoSpellings.md.

# Values and conversion classification

Classification is by conversion constructor, subject to conversion typing:

    inert  ::= id X | seal X | c ↦ d | ∀X.c
    active ::= id ℕ | id 𝔹 | unseal X

The two classes are total on typed conversions and disjoint.

    V, W ::= n | true | false | λx:A.N
            | ΛX.V
            | V ⟪ Θ , c ⟫       if c is inert

`ΛX.N` is a value only if `N` is a value.  On well-typed terms that is
automatic, because `⊢Λ` demands it; the premise is kept on the value
constructor so that `Value` remains the same relation on untyped terms.
A boundary with an active conversion is not a value.

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

Each rule is stated for a **well-typed redex** with variables as names,
and with the metavariable convention that `V` and `W` range over
VALUES (so a rule written with `V`/`W` needs no `Value` premise; Agda's
`Value V`/`Value W` premises are that convention spelled out — they fix
the evaluation order and are what determinism rests on).  Every
type the contractum writes (`R`, `Aᵢ`, `Aₒ`, `A`, `Bᵢ`) is determined by
the redex, so it appears as a `where` clause, and every "is in scope in
both" condition the Agda rules carry is a consequence of the readings'
inclusions (`Δᵢ ⊆ Δᶜ`, `Δ ⊆ Δᶜ`, `Δᶜ ≈ Δᵈ`, `Δ₁ᶜ ⊆ Δ⋉ᶜ`, `Δ′ᶜ ⊆ Δ″ᶜ`) and
of typing, and is omitted.  The mechanization notes say which Agda
premises these were.

    (TyBeta)    Δ ⊢ (ΛX.V) [B,A]
                    -→ V ⟪ [ unlock X α ] , revealₓ(B) ⟫ ∣ new R
                where Δ ⊢ᶜ A ~ R

`X` and `α` are the ordinary and representation binders of the event.
`R` is the ordinary argument `A` read as a representation type; the
step allocates it at `α` — the allocation is the step's store change,
not part of the boundary.

    (Beta)      Δ ⊢ (λx:A.N) · W -→ N[x:=W:A] ∣ none

    (Peel)      Δ ⊢ (V ⟪ Θ , c ↦ d ⟫) · W
                    -→ (V · (W ⟪ dual Θ , c ⟫)) ⟪ Θ , d ⟫ ∣ none

Mechanization note.  Agda's `Peel` carries the readings `Δ ⊢ᶜ Θ ⇒ Δᶜ`,
`Δ ⊢ⁱ Θ ⇒ Δᵢ`, `Δᵢ ⊢ᶜ dual Θ ⇒ Δᵈ` and `SameConv Δᵈ s′ Δᶜ s`: the domain
conversion is re-spelled from Θ's conversion context to the dual's.
With names `c` is textually unchanged, and that the two contexts name
the same representation variables is `Q`/`Q-inv` (Boundary.agda §3b), so
none of these is a premise here.  `W` **moves verbatim** — a boundary
changes names only, so the crossing argument lands at the very store it
was spelled at.  `notes/CrossingAudit.agda` refutes equality of the de
Bruijn name maps, while `notes/PeelPremise.agda` proves that they name
the same representation variables.

    (TyPeelR-Λ) Δ ⊢ ((ΛX.V) ⟪ Θ , ∀X.c ⟫) [B,A]
                    -→ V ⟪ unlock X α ∷ Θ , instRevealₓ(c) ⟫ ∣ new R
                where Δ ⊢ᶜ A ~ R

No term moves in this clause: the `Λ` binder becomes the binder the
allocation introduces, and the prepended unlock names it.

Mechanization note.  Agda also carries `Δ ⊢ᶜ Θ ⇒ Δᶜ` and
`underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ`; both are recoverable from the redex typing
(`conv-all-inv`), and the contractum does not mention `Bᵢ`.

    (TyPeelR-⟪⟫)
                Δ ⊢ ((W ⟪ Θ′ , ∀X.c′ ⟫) ⟪ Θ , ∀X.c ⟫) [B,A]
                    -→ ((W ⟪ lock X α ∷ Θ′ , ∀X.c′ ⟫) [Bᵢ,X])
                         ⟪ unlock X α ∷ Θ , instRevealₓ(c) ⟫ ∣ new R
                where Δ ⊢ᶜ A ~ R
                  and under(X,α,Δᶜ) ⊢ c : Bᵢ ⇝ Bₑ   (Δ ⊢ᶜ Θ ⇒ Δᶜ)

The two displayed universal binders have separate lexical scopes; they
have been alpha-renamed to the same `X` so the named correspondence is
literal.  `Bᵢ`, the source type of the outer conversion, is the one type
this rule WRITES into the term: the pushed-in type application
instantiates the inner package at `X`, and its annotation must be the
inner package's body type, which typing identifies with `Bᵢ`.

Mechanization note.  Agda's rule carries five readings — `Δ ⊢ⁱ Θ ⇒ Δᵢ`,
`Δ ⊢ᶜ Θ ⇒ Δᶜ`, `Δᵢ ⊢ᶜ Θ′ ⇒ Δ′ᶜ`, `allocate R Δ ⊢ⁱ inst Θ ⇒ Δᵢ⁺` (at the
ALLOCATED context: the cell this step mints is ambient) and
`Δᵢ⁺ ⊢ᶜ renᴮᴿ suc Θ′ ++ (lock 0 0 ∷ []) ⇒ Δ″ᶜ` — and two re-spellings:
the annotation is `Bᵢ′` with `underΛ Δᵢ ⊢ Bᵢ′ ≈ Bᵢ ⊣ underΛ Δᶜ` (the
source type spelled in the interior, where the annotation sits), and the
moved conversion is `s″` with `SameConv` at the two conversion readings.
Both the moved value and the moved boundary take the **sibling shift** of
the allocation: `renᴹᴿ suc W` and `renᴮᴿ suc Θ′ ++ (lock 0 0 ∷ [])`,
which is `lock X α ∷ Θ′` after that shift.  With names `c′` is unchanged
(`Δ′ᶜ ⊆ Δ″ᶜ` after the shift, `snoc-lock0-conversion-ren`) and `Bᵢ` is in
scope in the interior because the outer `env` compares the inner
package's type with `∀Bᵢ` across `Δᵢ`/`Δᶜ`.
`notes/ForallPayloadWall.agda` shows why a fixed position for the
annotation is wrong; `notes/AddLock0Wall.agda` shows why the skipped lock
and old unlocks defeat every fixed conversion renaming.

    (CancelR)   Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
                    -→ (V ⟪ Θ₂ ++ Θ₁ , mkId Aᵢ ⟫)
                         ⟪ Θ₂ ++ dual Θ₂ , mkId Aₒ ⟫ ∣ none
                where Δ₁ᶜ ∋ X := Aᵢ   (Δ ⊢ⁱ Θ₂ ⇒ Δᵢ , Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ)
                  and Δᶜ ∋ Y := Aₒ   (Δ ⊢ᶜ Θ₂ ⇒ Δᶜ)

`Aᵢ` is the type the inner seal conceals, looked up in Θ₁'s own
conversion context; `Aₒ` the type the outer unseal reveals.  `X` and `Y`,
and `Aᵢ` and `Aₒ`, remain distinct metavariables: typing a redex forces
the seal and unseal to meet at the same representation, but the untyped
reduction constructor does not carry that equation.

Mechanization note.  Agda spells the merged scope `Θ₁ ++ Θ₂` (its lists
are head-last).  It also carries `Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ` — read at the
**plain exterior** `Δ`, since both scopes were spelled at the same
store — and the re-spelling `Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ`, using `mkId A′`; with
names `Aᵢ` is in scope in the merged context because
`Δ₁ᶜ ⊆ Δ⋉ᶜ` (`merged-conversion-exists`).  `notes/CancelRShiftWall.agda`
records the wall and its dissolution — with the store there is no
representation shift between the two readings at all (`no-shift`);
`notes/CancelRReachabilityWitness.agda` reaches that case from source.

    (Drop$)     Base A
                --------------------------------------
                Δ ⊢ n ⟪ Θ , id A ⟫ -→ n ∣ none

    (Drop-true) --------------------------------------------
                Δ ⊢ true ⟪ Θ , id 𝔹 ⟫ -→ true ∣ none

    (Drop-false)
                ----------------------------------------------
                Δ ⊢ false ⟪ Θ , id 𝔹 ⟫ -→ false ∣ none

    (IdPush)    Δ ⊢ (V ⟪ Θ₁ , id X ⟫) ⟪ Θ₂ , unseal Y ⟫
                    -→ (V ⟪ Θ₂ ++ Θ₁ , unseal X ⟫)
                         ⟪ Θ₂ ++ dual Θ₂ , mkId A ⟫ ∣ none
                where Δᶜ ∋ Y := A   (Δ ⊢ᶜ Θ₂ ⇒ Δᶜ)

Mechanization note.  Agda carries `Δ ⊢ⁱ Θ₂ ⇒ Δᵢ`, `Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ`,
`Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ` and the re-spelling `Δ⋉ᶜ ⊢ X′ ≈ X ⊣ Δ₁ᶜ`, using
`unseal X′`; with names `X` stays live in the merged context for the
same reason as CancelR's `Aᵢ`.  `notes/ForallPayloadWall.agda` exhibits
the reordering that defeats a fixed index calculation.

## Congruence rules

A congruence passes the store change up and applies it to the redex's
**siblings**: after an allocation the whole program lives under one more
representation cell, so every representation occurrence in a sibling moves
up by one.  Agda writes that `↑ᴹ[ δ ]` on a term and `↑ᴮ[ δ ]` on a
boundary scope; with names it is the identity, exactly like the other
index shifts this note suppresses.  Ordinary positions never move, so no
type annotation and no conversion is touched.

    (ξ-·-l)     Δ ⊢ L -→ L′ ∣ δ
                ----------------------------------
                Δ ⊢ L · M -→ L′ · ↑ᴹ[δ]M ∣ δ

    (ξ-·-r)     Δ ⊢ M -→ M′ ∣ δ
                ----------------------------------
                Δ ⊢ V · M -→ ↑ᴹ[δ]V · M′ ∣ δ

    (ξ-·[])     Δ ⊢ L -→ L′ ∣ δ
                ----------------------------------
                Δ ⊢ L [B,A] -→ L′ [B,A] ∣ δ

    (ξ-⟪⟫)      Δ ⊢ⁱ Θ ⇒ Δᵢ    Δᵢ ⊢ M -→ M′ ∣ δ
                --------------------------------------
                Δ ⊢ M ⟪ Θ,c ⟫ -→ M′ ⟪ ↑ᴮ[δ]Θ , c ⟫ ∣ δ

There is **no `ξ-Λ`**: reduction does not go under a type abstraction,
because the value restriction leaves nothing there to reduce.  There is
no reduction under a term lambda either.  Reduction is call-by-value,
left-to-right, and it does proceed inside a boundary at that boundary's
interior context.

The reflexive-transitive closure used by preservation and type safety
threads the store change through:

    (done)      ----------------
                Δ ⊢ M -→* M

    (then)      Δ ⊢ L -→ M ∣ δ    apply δ Δ ⊢ M -→* N
                ---------------------------------------
                Δ ⊢ L -→* N

`runCtx r` is the context a run `r` **ends** at: every step's change
applied in order.

# A CancelR run excerpt

`Examples.agda` §8 contains the closed source program

    ((ΛX. λx:X.
        ((ΛY. λy:(∀Z.Z⇒Y). y[ℕ] · 7) [X]
          · (ΛZ. λy:Z. x))) [ℕ]) · 7

and proves that it reaches `7` in nineteen steps.  The following excerpt
was generated by `Show.showTrace`, not transcribed from indices.  The
renderer prints the store as `Ξ = [...]` with the **newest** cell first,
so `α` is the most recently allocated one.  Let

    V = (7 ⟪ ↓Z , seal Z ⟫) ⟪ ↓X , id Z ⟫

The tenth through thirteenth states are whole terms, at the store

    Ξ = [ α := ℕ , β := γ , γ := ℕ ]

which the four steps leave alone — none of them allocates.  The first
`CancelR` is the open-representation case: the cancelled cell is `β`, and
its stored representation is the representation *variable* `γ`.

    ((V ⟪ ↥X , ↓Y , seal Y ⟫) ⟪ ↥Y , unseal Y ⟫) ⟪ ↥Z , unseal Z ⟫
    -→ CancelR
    ((V ⟪ ↥Y , ↥X , ↓Y , id Z ⟫) ⟪ ↥Y , ↓Y , id Z ⟫) ⟪ ↥Z , unseal Z ⟫
    -→ IdPush
    ((V ⟪ ↥Y , ↥X , ↓Y , id Z ⟫) ⟪ ↥Z , ↥Y , ↓Y , unseal Z ⟫)
      ⟪ ↥Z , ↓Z , id ℕ ⟫
    -→ IdPush
    ((V ⟪ ↥Z , ↥Y , ↓Y , ↥Y , ↥X , ↓Y , unseal Z ⟫)
       ⟪ ↥Z , ↥Y , ↓Y , ↥Y , ↓Y , ↓Z , id ℕ ⟫)
      ⟪ ↥Z , ↓Z , id ℕ ⟫

The trace makes the two universes visible: the store cell `β := γ` holds
an open representation, while `↥Y` gives `β` a type variable.  Every
boundary is changes-only — the representations they used to carry are in
`Ξ`.  `CancelR` keeps both frames and replaces the matched
`seal`/`unseal` conversions by identities; the following `IdPush` steps
move the remaining active conversion inward without merging those frames.

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

and the redex `( ΛZ.0 ) [ℕ,ℕ]`.  It mentions neither `X` nor `Y`, so it
can be typed despite the duplicate naming of `α`.  (Its body is a
numeral, so the value restriction accepts it.)  `TyBeta` must mint a
boundary whose `BoundaryWf` contains `WfCtx (Ξ ∣ Γ)`, and that is impossible:
one representation variable has two live type variables.  In the named
presentation `WfCtx` therefore reads as distinct-name, no-alias hygiene;
in ordinary mathematical practice it is maintained by alpha-conversion.

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

# The six re-spelling repairs

The named presentation makes the same name remain the same name, but it
does not hide why the Agda carries relational witnesses.

| defect | live repair | what naming removes | what survives |
|---|---|---|---|
| `notes/ReUnlockWall.agda` | `conv-unlock-live` | a repeated insertion position | the conversion reading is a union and differs from the interior |
| `notes/ForallPayloadWall.agda`, `TyPeelR-⟪⟫` | carry `Bᵢ′` with `_⊢_≈_⊣_` | reindexing the interior annotation | it must be readable in both the interior and conversion contexts |
| `notes/ForallPayloadWall.agda`, `IdPush` | carry `X′` with `_⊢_≈_⊣_` | reindexing the pushed name | the name must be live at the inner and merged conversion contexts |
| `notes/CancelRShiftWall.agda` (dissolved by the store, kept as a record) | carry `A′` from `Θ₁`'s own conversion context | the bind-prefix shift, which no longer exists (`no-shift`) | the type is still read at two different NAME MAPS, `Θ₁`'s and the merged one |
| `notes/CrossingAudit.agda` and `notes/PeelPremise.agda` | carry `s′` with `SameConv` | reindexing the domain conversion across the dual | the original and dual conversion contexts remain different |
| `notes/AddLock0Wall.agda` | carry `s″` with `SameConv` | reindexing through the new lock and old unlocks | both conversion readings and the old context's representation-rebased view remain premises |

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
| `Θ = ⟨ δ₁,…,δₘ ⟩` | `Boundary = List Change` | an alias; a scope IS its change list |
| `dual Θ` | `dual` | none |
| `Θ ++ dual Θ` | `rewind Θ = dual Θ ++ Θ` | none |
| `Θ₂ ++ Θ₁` (acting order) | `Θ₁ ++ Θ₂` (head-last) | nothing shifts: both scopes are spelled at the same store |
| `lock X α ∷ Θ` | the snoc `Θ ++ (lock 0 0 ∷ [])` | written out at its use sites |
| `unlock X α ∷ Θ` | `inst Θ = map shiftChange Θ ++ (unlock 0 0 ∷ [])` | one shift in each universe, because it is read one allocation later |

## Formation, conversion, and term typing

| notes | Agda constructor | presentation/mechanization gap |
|---|---|---|
| `wf-var`, `wf-ℕ`, `wf-𝔹`, `wf-⇒`, `wf-∀` | same names in `Ctx.agda` | named binders replace `underΛ` index shifts |
| representation formation | `wfᴿ-var`, `wfᴿ-ℕ`, `wfᴿ-𝔹`, `wfᴿ-⇒`, `wfᴿ-∀` | free Greek variables and local Latin binders replace the mixed index cutoff |
| `lock`, `unlock` | `step-lock`, `step-unlock` | membership/freshness replaces positional insert/delete evidence |
| interior changes | `changes[]`, `changes∷` | named sequences suppress index shifts only |
| conversion changes | `conv[]`, `conv-lock`, `conv-unlock`, `conv-unlock-live` | the no-op re-unlock remains semantically visible |
| `BoundaryWf` | `bw` | three fields only — exterior `WfCtx` and the two readings; output well-formedness is derived in both presentations |
| `conv-id`, `conv-idv`, `conv-unseal`, `conv-seal`, `conv-fun`, `conv-all` | same names in `Conversion.agda` | none beyond named lookup and binders |
| `mkId`, `revealₓ`, `concealₓ`, `instRevealₓ`, `instConcealₓ` | `mkId`, `reveal`, `conceal`, `instReveal`, `instConceal` | the Agda operations carry the slot as an index, not a name |
| `⊢\``, `⊢$`, `⊢true`, `⊢false`, `⊢ƛ`, `⊢·`, `⊢Λ`, `⊢·[]` | same constructors in `Terms.agda` | named binders replace term/type indices; `⊢Λ`'s `Value N` is the value restriction |
| `env` | `env` | Agda has `Bᵢ/Cᵢ` and `Bₑ/Cₑ`, both related by `_⊢_≈_⊣_`; notes use one named endpoint plus paired scope conditions |
| inert identities, seals, arrows, universals | `I-idv`, `I-seal`, `I-fun`, `I-all` | none |
| active base identities and unseals | `A-idb`, `A-unseal` | none |
| values | `V-$`, `V-true`, `V-false`, `V-ƛ`, `V-Λ`, `V-⟪⟫` | named binders only |

## Reduction

| notes rule | Agda constructor | presentation/mechanization gap |
|---|---|---|
| `TyBeta` | `TyBeta` | `inst` shifts old representation indices; names stay fixed.  Store change `new R` |
| `Beta` | `Beta` | named frame-exact substitution hides the representation-only weakening under `Λ`, not the crossing boundary.  `none` |
| `Peel` | `Peel` | `s′`/`SameConv` becomes one `c` plus scope in `Δᶜ,Δᵈ`; `W` moves verbatim.  `none` |
| `TyPeelR-Λ` | `TyPeelR-Λ` | `inst` shifts indices; no re-spelling premise is removed.  `new R` |
| `TyPeelR-⟪⟫` | `TyPeelR-⟪⟫` | `Bᵢ′` and `s″` collapse to named `Bᵢ` and `c′` with four scope readings; Agda sibling-shifts `W` and `Θ′` by the allocation and renames the annotation.  `new R` |
| `CancelR` | `CancelR` | `A′` collapses to named `Aᵢ` with scope at `Δ⋉ᶜ,Δ₁ᶜ`; the merged reading is at the plain exterior; distinct raw-rule `X,Y,Aᵢ,Aₒ` are retained.  `none` |
| `Drop$` | `Drop$` | none; the `Base A` premise is retained.  `none` |
| `Drop-true` | `Drop-true` | none.  `none` |
| `Drop-false` | `Drop-false` | none.  `none` |
| `IdPush` | `IdPush` | `X′` collapses to named `X` with scope at `Δ⋉ᶜ,Δ₁ᶜ`; the merged reading is at the plain exterior; distinct raw-rule outer `Y` is retained.  `none` |
| `ξ-·-l` | `ξ-·-l` | the sibling shift `↑ᴹ[δ]` is the named identity |
| `ξ-·-r` | `ξ-·-r` | same; `Value V` is retained |
| `ξ-·[]` | `ξ-·[]` | none; annotations are ordinary and never shift |
| `ξ-⟪⟫` | `ξ-⟪⟫` | the scope shift `↑ᴮ[δ]` is the named identity; the explicit interior-reading premise is retained |
| — | (no `ξ-Λ`) | the value restriction removed it |
| `done`, `then` | `done`, `_then_` | the tail runs at `apply δ Δ` |

For completeness, the named rules render differently from their Agda
premises only at these sites:

  1. `env`: `Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ` becomes one `Bᵢ` readable in
     both contexts; `Δ ⊢ Bₑ ≈ Cₑ ⊣ Δᶜ` becomes one `Bₑ`
     readable in the exterior and conversion contexts.
  2. `Peel`: `SameConv Δᵈ s′ Δᶜ s` becomes one `c` readable in
     both contexts.
  3. `TyPeelR-⟪⟫`: the moved-reading premise uses
     `renᴮᴿ suc Θ′ ++ (lock 0 0 ∷ [])` in Agda and `lock X α ∷ Θ′`
     here; its `SameConv … s″ … s′` becomes one `c′` readable in both
     conversion contexts; and `underΛ Δᵢ ⊢ Bᵢ′ ≈ Bᵢ ⊣ underΛ Δᶜ`
     becomes one `Bᵢ` readable in both contexts.
  4. `CancelR`: `Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ` becomes one `Aᵢ`
     readable in both contexts.  Both lookup premises remain separate.
  5. `IdPush`: the merged-name premise, which relates the variable
     spellings X′ and X at Δ⋉ᶜ and Δ₁ᶜ, becomes one `X`
     live in both contexts.  The outer lookup premise remains separate.
  6. The congruences: `↑ᴹ[ δ ]` and `↑ᴮ[ δ ]` become the identity,
     because with names an allocation renumbers nothing.

Every other premise in the displayed typing and reduction rules is present
with the same mathematical content as in `Terms.agda` or `Reduction.agda`.
