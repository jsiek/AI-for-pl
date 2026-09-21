# Strong System F with representation variables

This is the mathematical presentation of the calculus in
`SystemF/agda/strong-rep-var/` at commit `e6171412`.  The Agda uses de
Bruijn indices; this note uses names.  The named presentation is not a
different calculus: it suppresses index shifts and re-spellings, but keeps
the contexts in which types and conversions are read.

The distinction at the center of the development is:

    X, Y, Z       type variables
    α, β, γ       representation variables

A type variable is lexical: `∀X.A`, `ΛX.M`, and types mention `X`.  A
representation variable is runtime storage: a representation context
binds `α` abstractly or to a representation type, while a boundary
introduces only the represented form.  A live type variable `X` is
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

`seal X` and `unseal X` carry an type variable.  They find its
representation through the context; they never contain a representation
variable directly.  Function conversions are contravariant on the left.

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
    Θ ::= ⟨ α₁ := R₁, ..., αₙ := Rₙ,  δ₁, ..., δₘ ⟩

The representation bindings are parallel: every `Rᵢ` is read in the exterior
representation context.  The changes `δᵢ` are sequential and stored
head-last in Agda, so its tail acts first.
We write `binds(Θ)` for all the representation bindings
and `changes(Δ)` for the list of changes.

The displayed boundary notation follows `Show.agda`:

    ↑α:=R      bind the fresh representation variable α to R
    ↓X         lock X, recording that it names α
    ↥X         unlock the type variable X for α

Thus `M ⟪ ↑α:=R , ↓Y , ↥Z , c ⟫` displays binds first, changes in
the order in which they act, and the conversion last.  The full change
syntax remains `lock Y β` and `unlock Z γ`; the Greek argument is
recoverable from the displayed Latin name.

# The two context universes

A type context is presented as

    Ξ ∣ Γ

where `Ξ` is a representation context and `Γ` maps type variables to representation variables:

    Ξ ::= · | Ξ, α abstract | Ξ, α := R
    Γ ::= · | Γ, X ↦ α

The Γ context contains exactly the live type variales.  A locked type
variable has no entry in `Γ`, but its representation variable remains in
`Ξ`.  In a well-formed context every representation type is well formed outside its
own binder, every type variable points into `Ξ`, and no representation variable has
two simultaneous type variables.  We use the Barendregt convention, so
type variables and representation variables are chosen fresh.

The main lookups are:

    Ξ ∣ Γ ∋ X ↦ α       X is live and α points to its representation type
    Ξ ∣ Γ ∋ α := R      α's stored representation is R
    Ξ ∣ Γ ∋ X := A      X is live and A is its representation type

The definition of lookup Ξ ∣ Γ ∋ X := A is derived form the other forms.

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

The representation bindings first extend `Ξ` with fresh represented
variables.  It does not change any existing type variable.  The two
readings then treat changes differently.

The **interior scope** generation, written `Δ ⊢ⁱ Θ ⇒ Δᵢ`, performs every change:

    lock X α       removes X ↦ α
    unlock X α     adds X ↦ α, provided α has no live type variable

The **conversion scope** generation, written `Δ ⊢ᶜ Θ ⇒ Δᶜ`, is the union of
the variable live anywhere in the boundary:

    lock X α       is skipped
    unlock X α     adds X ↦ α if α is not live
    unlock X α     is a no-op if α already has its unique live name

The last clause is `conv-unlock-live`.  For example, a conversion reading
of `↓X` leaves `X` live; the inverse `↥X` in `rewind Θ` must therefore
be a no-op, not a failed freshness check.  `notes/ReUnlockWall.agda`
machine-checks the old failure and the repaired readings.

Both readings are relations, but each is functional.  A well-formed
boundary witness is:

    BoundaryWf Δ Θ Δᵢ Δᶜ

It carries `WfCtx Δ`, well-formedness of the parallel bind block, and the
two readings `Δ ⊢ⁱ Θ ⇒ Δᵢ` and `Δ ⊢ᶜ Θ ⇒ Δᶜ`.  Well-formedness
of the two outputs is derived.

## Derived Boundary Scopes

In the following equations, change sequences are written in acting order.
Named variables make the definitions clearer wrt. de Bruijn because representation
indices do not have to shift past a bind block.

    dualBoundary Θ
      binds no representations and performs the inverse changes
      in reverse acting order

    rewind Θ
      keeps binds(Θ), performs changes(Θ), then their inverses

    Θ₁ ⋉ Θ₂
      keeps binds(Θ₁), performs changes(Θ₂), then changes(Θ₁)

    addLock(X,α,Θ)
      keeps binds(Θ), performs lock X α first, then changes(Θ)

    instantiate(X,α,R,Θ)
      prepends α := R, unlocks X α first, then performs changes(Θ)

Agda's `_ ⋉ _`, `addLock0`, and `instantiate` additionally shift de
Bruijn representation indices.  Those shifts change no named occurrence.

## A concrete boundary 

Let

    Δ = (α := ℕ, β abstract) ∣ (X ↦ α, Y ↦ β)
    Θ = ⟨ ↑γ:=α, ↓X, ↥Z ⟩

where `Z` names the new `γ`.  Then

    Δᵢ = (α := ℕ, β abstract, γ := α)
         ∣ (Y ↦ β, Z ↦ γ)

    Δᶜ = (α := ℕ, β abstract, γ := α)
         ∣ (X ↦ α, Y ↦ β, Z ↦ γ)

The interior scope loses `X`; the conversion scope keeps it.
At `Δᶜ`, `unseal Z` converts `Z` to `X`, because `Z` names `γ`,
`γ` stores the representation type `α`, and `X` is the live type variable of `α`.
Thus an `env` instance can type

    Δᵢ ∣ · ⊢ M : Z
    Δᶜ ⊢ unseal Z : Z ⇝ X
    ----------------------------------------
    Δ ∣ Γₜ ⊢ M ⟪ ↑γ:=α, ↓X, ↥Z, unseal Z ⟫ : X

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

    (⊢Λ)       under(X,α,Δ) ∣ ⇑Γₜ ⊢ N : C
               ------------------------------
               Δ ∣ Γₜ ⊢ ΛX.N : ∀X.C

    (⊢·[])     Δ ∣ Γₜ ⊢ L : ∀X.B    Δ ⊢ᵗ A
               ----------------------------
               Δ ∣ Γₜ ⊢ L [B,A] : B[X:=A]

Here `⇑Γₜ` weakens every type in the term context through the fresh
type binder.

The boundary rule is the only non-System-F rule:

    (boundary) BoundaryWf Δ Θ Δᵢ Δᶜ
               Δᵢ ∣ · ⊢ M : Bᵢ
               Δᶜ ⊢ c : Bᵢ ⇝ Bₑ
               Bᵢ is in scope in both Δᵢ and Δᶜ
               Bₑ is in scope in both Δ and Δᶜ
               Δ ⊢ᵗ Bₑ
               --------------------------------
               Δ ∣ Γₜ ⊢ M ⟪ Θ , c ⟫ : Bₑ

The empty term context in the second premise is load-bearing: substitution
does not descend into a boundary.

Mechanization note.  Agda allows distinct index spellings `Bᵢ/Cᵢ` and
`Bₑ/Cₑ`.  Its fourth premise is `Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ`; its fifth is
`SameTyExt (numBinds Θ) Δ Bₑ Δᶜ Cₑ`, which also crosses the
boundary scope's representation-bind prefix.  Named variables turn these into
the two paired scope conditions above; the interior/conversion/exterior
contexts do not disappear.

# Values and conversion classification

Classification is by conversion constructor, subject to conversion typing:

    inert  ::= id X | seal X | c ↦ d | ∀X.c
    active ::= id ℕ | id 𝔹 | unseal X

The two classes are total on typed conversions and disjoint.

    V, W ::= n | true | false | λx:A.N
            | ΛX.V
            | V ⟪ Θ , c ⟫       if c is inert

Reduction goes under `Λ`, so `ΛX.N` is a value only if `N` is a value.
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

The judgment is `Δ ⊢ M -→ M′`.  The premises naming interior and
conversion contexts are part of the reduction relation even when the
redex's typing can reconstruct them.

## Computational rules

    (TyBeta)    Value N    Δ ⊢ᶜ A ~ R
                -----------------------------------------------
                Δ ⊢ (ΛX.N) [B,A]
                    -→ N ⟪ instantiate(X,α,R,∅), revealₓ(B) ⟫

`X` and `α` are the ordinary and representation binders of the event.
The second premise is genuine: it translates the ordinary argument `A`
to the representation type stored at `α`.

    (Beta)      Value W
                --------------------------------
                Δ ⊢ (λx:A.N) · W -→ N[x:=W:A]

For `Peel`, suppose the carried readings are

    Δ  ⊢ⁱ Θ             ⇒ Δᵢ
    Δ  ⊢ᶜ Θ             ⇒ Δᶜ
    Δᵢ ⊢ᶜ dualBoundary Θ   ⇒ Δᵈ

Then:

    (Peel)      Value V    Value W
                Δ ⊢ᶜ Θ ⇒ Δᶜ    Δ ⊢ⁱ Θ ⇒ Δᵢ
                Δᵢ ⊢ᶜ dualBoundary Θ ⇒ Δᵈ
                c is in scope in both Δᶜ and Δᵈ
                ------------------------------------------------------
                Δ ⊢ (V ⟪ Θ , c ↦ d ⟫) · W
                    -→ (V · (W ⟪ dualBoundary Θ , c ⟫)) ⟪ Θ , d ⟫

Mechanization note.  Agda names the dual spelling `c′`, requires
`SameConv Δᵈ c′ Δᶜ c`, and shifts `W` past `numBinds Θ`; named variables
leave `c` and `W` textually unchanged.  `notes/CrossingAudit.agda` refutes
equality of the de Bruijn name maps, while `notes/PeelPremise.agda` proves
that they name the same representation variables.

For `TyPeelR-Λ`, let `Δ ⊢ᶜ Θ ⇒ Δᶜ`:

    (TyPeelR-Λ)
                Value N
                Δ ⊢ᶜ Θ ⇒ Δᶜ
                under(X,α,Δᶜ) ⊢ c : Bᵢ ⇝ Bₑ
                Δ ⊢ᶜ A ~ R
                --------------------------------------------------
                Δ ⊢ ((ΛX.N) ⟪ Θ , ∀X.c ⟫) [B,A]
                    -→ N ⟪ instantiate(X,α,R,Θ), instRevealₓ(c) ⟫

No term moves in this clause: the `Λ` binder becomes the represented
binder introduced by `instantiate`.

For `TyPeelR-⟪⟫`, let the readings named in the premises be:

    Δ     ⊢ⁱ Θ                         ⇒ Δᵢ
    Δ     ⊢ᶜ Θ                         ⇒ Δᶜ
    Δᵢ    ⊢ᶜ Θ′                        ⇒ Δ′ᶜ
    Δ     ⊢ⁱ instantiate(X,α,R,Θ)     ⇒ Δᵢ⁺
    Δᵢ⁺   ⊢ᶜ addLock(X,α,Θ′)          ⇒ Δ″ᶜ

The named rule is:

The two displayed universal binders have separate lexical scopes; they
have been alpha-renamed to the same `X` so the named correspondence is
literal.

    (TyPeelR-⟪⟫)
                Value W
                Δ ⊢ⁱ Θ ⇒ Δᵢ    Δ ⊢ᶜ Θ ⇒ Δᶜ    Δᵢ ⊢ᶜ Θ′ ⇒ Δ′ᶜ
                Δ ⊢ⁱ instantiate(X,α,R,Θ) ⇒ Δᵢ⁺
                Δᵢ⁺ ⊢ᶜ addLock(X,α,Θ′) ⇒ Δ″ᶜ
                c′ is in scope under X in both the old view of Δ′ᶜ
                   after adding α, and Δ″ᶜ
                under(X,α,Δᶜ) ⊢ c : Bᵢ ⇝ Bₑ
                Bᵢ is in scope under X in both Δᵢ and Δᶜ
                Δ ⊢ᶜ A ~ R
                ----------------------------------------------------------
                Δ ⊢ ((W ⟪ Θ′ , ∀X.c′ ⟫) ⟪ Θ , ∀X.c ⟫) [B,A]
                    -→ ((W ⟪ addLock(X,α,Θ′), ∀X.c′ ⟫) [Bᵢ,X])
                         ⟪ instantiate(X,α,R,Θ), instRevealₓ(c) ⟫

Mechanization note.  Agda calls the annotation `Bᵢ′`, carries
`underΛ Δᵢ ⊢ Bᵢ′ ≈ Bᵢ ⊣ underΛ Δᶜ`, and renames it past the inserted
representation binder; `notes/ForallPayloadWall.agda` shows why a fixed
position is wrong.  It also calls the moved conversion `c″`, relates it
to `c′` by `SameConv` at the two conversion readings, and representation-
renames `W` and `Θ′`; `notes/AddLock0Wall.agda` shows why the skipped lock
and old unlocks defeat every fixed conversion renaming.

For the scope-move rules, `binds(Θ₂)·Δ` means the exterior context
with `Θ₂`'s parallel representation bind block added.  It does not apply
`Θ₂`'s ordinary-name changes.

    (CancelR)   Value V
                Δ ⊢ⁱ Θ₂ ⇒ Δᵢ
                Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
                Δ₁ᶜ ∋ X := Aᵢ
                binds(Θ₂)·Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
                Aᵢ is in scope in both Δ⋉ᶜ and Δ₁ᶜ
                Δ ⊢ᶜ Θ₂ ⇒ Δᶜ
                Δᶜ ∋ Y := Aₒ
                -------------------------------------------------------
                Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
                    -→ (V ⟪ Θ₁ ⋉ Θ₂ , mkId Aᵢ ⟫)
                         ⟪ rewind Θ₂ , mkId Aₒ ⟫

`X` and `Y`, and `Aᵢ` and `Aₒ`, remain distinct metavariables in the
rule.  Typing a redex forces the seal and unseal to meet at the same
representation, but the untyped reduction constructor does not carry that
equation as a premise.

Mechanization note.  Agda calls the merged spelling `A′`, carries
`Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ`, and uses `mkId A′`; named notation keeps
`Aᵢ` with the paired scope condition.  `notes/CancelRShiftWall.agda`
refutes reading it anywhere but `Θ₁`'s own conversion context, and
`notes/CancelRReachabilityWitness.agda` reaches that case from source.

    (Drop$)     Base A
                ------------------------------
                Δ ⊢ n ⟪ Θ , id A ⟫ -→ n

    (Drop-true) --------------------------------
                Δ ⊢ true ⟪ Θ , id 𝔹 ⟫ -→ true

    (Drop-false)
                ----------------------------------
                Δ ⊢ false ⟪ Θ , id 𝔹 ⟫ -→ false

    (IdPush)    Value V
                Δ ⊢ⁱ Θ₂ ⇒ Δᵢ
                Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
                binds(Θ₂)·Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
                X is in scope in both Δ⋉ᶜ and Δ₁ᶜ
                Δ ⊢ᶜ Θ₂ ⇒ Δᶜ
                Δᶜ ∋ Y := A
                -------------------------------------------------------
                Δ ⊢ (V ⟪ Θ₁ , id X ⟫) ⟪ Θ₂ , unseal Y ⟫
                    -→ (V ⟪ Θ₁ ⋉ Θ₂ , unseal X ⟫)
                         ⟪ rewind Θ₂ , mkId A ⟫

Mechanization note.  Agda names the merged spelling `X′`, carries
`Δ⋉ᶜ ⊢ X′ ≈ X ⊣ Δ₁ᶜ`, and uses `unseal X′`; named notation keeps `X`
live in both contexts.  `notes/ForallPayloadWall.agda` exhibits the
reordering that defeats a fixed index calculation, and the raw rule's
outer `Y` remains distinct.

## Congruence rules

    (ξ-·-l)     Δ ⊢ L -→ L′
                ---------------------
                Δ ⊢ L · M -→ L′ · M

    (ξ-·-r)     Value V    Δ ⊢ M -→ M′
                --------------------------
                Δ ⊢ V · M -→ V · M′

    (ξ-·[])      Δ ⊢ L -→ L′
                --------------------------
                Δ ⊢ L [B,A] -→ L′ [B,A]

    (ξ-Λ)       under(X,α,Δ) ⊢ N -→ N′
                ---------------------------
                Δ ⊢ ΛX.N -→ ΛX.N′

    (ξ-⟪⟫)      Δ ⊢ⁱ Θ ⇒ Δᵢ    Δᵢ ⊢ M -→ M′
                -----------------------------------
                Δ ⊢ M ⟪ Θ,c ⟫ -→ M′ ⟪ Θ,c ⟫

There is no reduction under a term lambda.  Reduction is call-by-value,
left-to-right, but it does proceed under a type abstraction and inside a
boundary at that boundary's interior context.

The reflexive-transitive closure used by preservation and type safety is:

    (done)      ----------------
                Δ ⊢ M -→* M

    (then)      Δ ⊢ L -→ M    Δ ⊢ M -→* N
                ---------------------------
                Δ ⊢ L -→* N

# A CancelR run excerpt

`Examples.agda` §8 contains the closed source program

    ((ΛX. λx:X.
        ((ΛY. λy:(∀Z.Z⇒Y). y[ℕ] · 7) [X]
          · (ΛZ. λy:Z. x))) [ℕ]) · 7

and proves that it reaches `7` in nineteen steps.  The following excerpt
was generated by `Show.showTrace`, not transcribed from indices.  Let

    V = (7 ⟪ ↓X, seal X ⟫) ⟪ ↓Z, id X ⟫

The ninth through twelfth states are whole terms; the first `CancelR` is
the repaired open-representation case (`↑β:=α`):

    ((V ⟪ ↑γ:=ℕ, ↥Z, ↓Y, seal Y ⟫)
         ⟪ ↑β:=α, ↥Y, unseal Y ⟫)
      ⟪ ↑α:=ℕ, ↥X, unseal X ⟫
    -→ CancelR
    ((V ⟪ ↑γ:=ℕ, ↥Y, ↥Z, ↓Y, id X ⟫)
         ⟪ ↑β:=α, ↥Y, ↓Y, id X ⟫)
      ⟪ ↑α:=ℕ, ↥X, unseal X ⟫
    -→ IdPush
    ((V ⟪ ↑γ:=ℕ, ↥Y, ↥Z, ↓Y, id X ⟫)
         ⟪ ↑β:=α, ↥X, ↥Y, ↓Y, unseal X ⟫)
      ⟪ ↑α:=ℕ, ↥X, ↓X, id ℕ ⟫
    -→ IdPush
    ((V ⟪ ↑γ:=ℕ, ↥X, ↥Y, ↓Y, ↥Y, ↥Z, ↓Y, unseal X ⟫)
         ⟪ ↑β:=α, ↥X, ↥Y, ↓Y, ↥Y, ↓Y, ↓X, id ℕ ⟫)
      ⟪ ↑α:=ℕ, ↥X, ↓X, id ℕ ⟫

The trace makes the two universes visible: `↑β:=α` stores an open
representation type, while `↥Y` gives `β` an type variable.  `CancelR`
keeps both frames and replaces the matched `seal`/`unseal` conversions by
identities; the following `IdPush` steps move the remaining active
conversion inward without merging those frames.

# Metatheory

The public surface is in `TypeSafety.agda`.

    Progress
      Δ ∣ · ⊢ M : A
      -----------------------------------------------
      Value M  or  there exists M′ with Δ ⊢ M -→ M′

    Preservation
      WfCtx Δ
      Δ ∣ · ⊢ M : A
      Δ ⊢ M -→ M′
      ----------------
      Δ ∣ · ⊢ M′ : A

    Preservation*
      WfCtx Δ
      Δ ∣ · ⊢ M : A
      Δ ⊢ M -→* M′
      -----------------
      Δ ∣ · ⊢ M′ : A

    TypeSafety
      WfCtx Δ
      Δ ∣ · ⊢ M : A
      Δ ⊢ M -→* N
      -----------------------------------------------
      Value N  or  there exists N′ with Δ ⊢ N -→ N′

    Determinism
      Δ ∣ Γₜ ⊢ M : A
      Δ ⊢ M -→ M₁    Δ ⊢ M -→ M₂
      --------------------------------
      M₁ = M₂

    Values do not step
      Value V
      --------------------------
      there is no V′ with Δ ⊢ V -→ V′

Progress needs no global `WfCtx` premise: each boundary typing derivation
already contains its `BoundaryWf`.  Determinism does need the redex's typing
derivation, from which it recovers uniqueness of all relevant name maps.

Preservation needs `WfCtx Δ`.  Here is the counterexample to the
premise-free statement.  Take

    Ξ = (α := ℕ)
    Γ = (X ↦ α, Y ↦ α)

and the redex `( ΛZ.0 ) [ℕ,ℕ]`.  It mentions neither `X` nor `Y`, so it
can be typed despite the duplicate naming of `α`.  `TyBeta` must mint a
boundary whose `BoundaryWf` contains `WfCtx (Ξ ∣ Γ)`, and that is impossible:
one representation variable has two live type variables.  In the named
presentation `WfCtx` therefore reads as distinct-name, no-alias hygiene;
in ordinary mathematical practice it is maintained by alpha-conversion.

# The six re-spelling repairs

The named presentation makes the same name remain the same name, but it
does not hide why the Agda carries relational witnesses.

| defect | live repair | what naming removes | what survives |
|---|---|---|---|
| `notes/ReUnlockWall.agda` | `conv-unlock-live` | a repeated insertion position | the conversion reading is a union and differs from the interior |
| `notes/ForallPayloadWall.agda`, `TyPeelR-⟪⟫` | carry `Bᵢ′` with `_⊢_≈_⊣_` | reindexing the interior annotation | it must be readable in both the interior and conversion contexts |
| `notes/ForallPayloadWall.agda`, `IdPush` | carry `X′` with `_⊢_≈_⊣_` | reindexing the pushed name | the name must be live at the inner and merged conversion contexts |
| `notes/CancelRShiftWall.agda` | carry `A′` from `Θ₁`'s own conversion context | the bind-prefix shift of the representation | the type is read at `Θ₁`'s context and at the merged context |
| `notes/CrossingAudit.agda` and `notes/PeelPremise.agda` | carry `c′` with `SameConv` | reindexing the domain conversion across the dual | the original and dual conversion contexts remain different |
| `notes/AddLock0Wall.agda` | carry `c″` with `SameConv` | reindexing through the new lock and old unlocks | both conversion readings and the old context's representation-rebased view remain premises |

# Notes ↔ Agda correspondence

The rule names below are the Agda constructor names.

## Formation, conversion, and term typing

| notes | Agda constructor | presentation/mechanization gap |
|---|---|---|
| `wf-var`, `wf-ℕ`, `wf-𝔹`, `wf-⇒`, `wf-∀` | same names in `Ctx.agda` | named binders replace `underΛ` index shifts |
| representation formation | `wfᴿ-var`, `wfᴿ-ℕ`, `wfᴿ-𝔹`, `wfᴿ-⇒`, `wfᴿ-∀` | free Greek variables and local Latin binders replace the mixed index cutoff |
| `lock`, `unlock` | `step-lock`, `step-unlock` | membership/freshness replaces positional insert/delete evidence |
| interior changes | `changes[]`, `changes∷` | named sequences suppress index shifts only |
| conversion changes | `conv[]`, `conv-lock`, `conv-unlock`, `conv-unlock-live` | the no-op re-unlock remains semantically visible |
| `BoundaryWf` | `bw` | output well-formedness is derived in both presentations |
| `conv-id`, `conv-idv`, `conv-unseal`, `conv-seal`, `conv-fun`, `conv-all` | same names in `Conversion.agda` | none beyond named lookup and binders |
| `⊢\``, `⊢$`, `⊢true`, `⊢false`, `⊢ƛ`, `⊢·`, `⊢Λ`, `⊢·[]` | same constructors in `Terms.agda` | named binders replace term/type indices |
| `env` | `env` | Agda has `Bᵢ/Cᵢ` related by `_⊢_≈_⊣_` and `Bₑ/Cₑ` related by `SameTyExt`; notes use one named endpoint plus paired scope conditions |
| inert identities, seals, arrows, universals | `I-idv`, `I-seal`, `I-fun`, `I-all` | none |
| active base identities and unseals | `A-idb`, `A-unseal` | none |
| values | `V-$`, `V-true`, `V-false`, `V-ƛ`, `V-Λ`, `V-⟪⟫` | named binders only |

## Reduction

| notes rule | Agda constructor | presentation/mechanization gap |
|---|---|---|
| `TyBeta` | `TyBeta` | `instantiate` shifts old representation indices; names stay fixed |
| `Beta` | `Beta` | named frame-exact substitution hides the representation-only weakening under `Λ`, not the crossing boundary |
| `Peel` | `Peel` | `c′`/`SameConv` becomes one `c` plus scope in `Δᶜ,Δᵈ`; `W` is representation-weakened in Agda |
| `TyPeelR-Λ` | `TyPeelR-Λ` | `instantiate` shifts indices; no re-spelling premise is removed |
| `TyPeelR-⟪⟫` | `TyPeelR-⟪⟫` | `Bᵢ′` and `c″` collapse to named `Bᵢ` and `c′` with four scope readings; Agda representation-renames `W`, `Θ′`, and the annotation |
| `CancelR` | `CancelR` | `A′` collapses to named `Aᵢ` with scope at `Δ⋉ᶜ,Δ₁ᶜ`; distinct raw-rule `X,Y,Aᵢ,Aₒ` are retained |
| `Drop$` | `Drop$` | none; the `Base A` premise is retained |
| `Drop-true` | `Drop-true` | none |
| `Drop-false` | `Drop-false` | none |
| `IdPush` | `IdPush` | `X′` collapses to named `X` with scope at `Δ⋉ᶜ,Δ₁ᶜ`; distinct raw-rule outer `Y` is retained |
| `ξ-·-l` | `ξ-·-l` | none |
| `ξ-·-r` | `ξ-·-r` | none; `Value V` is retained |
| `ξ-·[]` | `ξ-·[]` | none |
| `ξ-Λ` | `ξ-Λ` | `underΛ` is written as a fresh named `X ↦ α` plus abstract `α` |
| `ξ-⟪⟫` | `ξ-⟪⟫` | none; the explicit interior-reading premise is retained |

For completeness, the named rules render differently from their Agda
premises only at these sites:

  1. `env`: `Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ` becomes one `Bᵢ` readable in
     both contexts; `SameTyExt ... Bₑ ... Cₑ` becomes one `Bₑ`
     readable in the exterior and conversion contexts.
  2. `Peel`: `SameConv Δᵈ c′ Δᶜ c` becomes one `c` readable in
     both contexts.
  3. `TyPeelR-⟪⟫`: the moved-reading premise uses
     `addLock0 (renᴮ² ... Θ′)` in Agda and `addLock(X,α,Θ′)` here;
     its `SameConv ... c″ ... c′` becomes one `c′` readable in both
     conversion contexts; and `underΛ Δᵢ ⊢ Bᵢ′ ≈ Bᵢ ⊣ underΛ Δᶜ`
     becomes one `Bᵢ` readable in both contexts.
  4. `CancelR`: `Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ` becomes one `Aᵢ`
     readable in both contexts.  Both lookup premises remain separate.
  5. `IdPush`: `Δ⋉ᶜ ⊢ X′ ≈ X ⊣ Δ₁ᶜ` becomes one `X`
     live in both contexts.  The outer lookup premise remains separate.

Every other premise in the displayed typing and reduction rules is present
with the same mathematical content as in `Terms.agda` or `Reduction.agda`.
