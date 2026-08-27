# World current-embedding design

Status: the World portion and the reveal/conceal portion of term imprecision
are implemented in place and example checked.

The checked probes are:

- `notes/probes/WorldChangeSequenceProbe.agda`
- `notes/probes/WorldCurrentEmbeddingProbe.agda`

These inspect the live definition directly. The provisional mirror-world,
rebase-edge, and constructor-rewrite probes were removed after the in-place
refactor.

## The distinction

A world currently serves two purposes:

1. it records the allocation history that produced the endpoint contexts;
2. its source embedding says where a source variable is compared now.

Those agree outside a conversion boundary. They do not agree while traversing
the nested target reveals in Example 12.

At checkpoint C1, the target allocation history is fixed:

    X₁′ maps to star
    Z′ maps to X₁′

The source variable `X` occupies three successive current positions:

    outside both reveals: X is not aligned with X₁′ or Z′
    inside the X₁′ reveal: X is aligned with X₁′
    inside the Z′ reveal:  X is aligned with Z′

The `Z′` representation comparison and `Z′` variable alignment occur in
different worlds:

    before the Z′ reveal:
      X is aligned with X₁′
      representation(Z′) = X₁′
      therefore X is imprecise to representation(Z′)

    after the Z′ reveal:
      X is aligned with Z′
      therefore X and Z′ may be compared in the reveal body

Trying to state both facts using one source embedding is the source of the
earlier tension.

## Current definition

The former definition derived every view from the same constructor history:

    data _⊑ᶜ_ : Ctx -> Ctx -> Set where
      emptyᶜ
      skip-centerᶜ
      lift-both-rawᶜ
      lift-left-rawᶜ
      bind-left-rawᶜ
      bind-right-rawᶜ
      bind-both-rawᶜ
      bind-both-star-rawᶜ
      bind-termᶜ

    centerᶜ : Γᴸ ⊑ᶜ Γᴿ -> TyCtx
    ηᴸᶜ     : (γ : Γᴸ ⊑ᶜ Γᴿ) -> Injectionᵗ (Δᵉ Γᴸ) (centerᶜ γ)
    ηᴿᶜ     : (γ : Γᴸ ⊑ᶜ Γᴿ) -> Injectionᵗ (Δᵉ Γᴿ) (centerᶜ γ)
    marksᶜ  : (γ : Γᴸ ⊑ᶜ Γᴿ) -> ImpEnv (centerᶜ γ)

## Separating history from changes

The nine current constructors mix two independent questions:

1. is this the empty history, or is this one more change?
2. what kind of endpoint change occurred?

The live definition now separates them. A world history has only two
constructors:

    data _⊑ᶜ_ : Ctx -> Ctx -> Set where
      emptyᶜ : empty-context ⊑ᶜ empty-context
      _▻ᶜ_ : (γ : Γᴸ ⊑ᶜ Γᴿ)
           -> WorldChange γ Γᴸ′ Γᴿ′
           -> Γᴸ′ ⊑ᶜ Γᴿ′

`WorldChange` classifies one step as a center change, a source type-context
change, a target type-context change, a paired type-context change, or a term
binding change. The representation-specific evidence remains in the relevant
change. For example, a paired type change still distinguishes a structural
lift, a precise bind, and a dynamic bind. This does not erase semantic
distinctions; it removes them from the recursive history datatype.

The probe defines a total `world-sequence` translation over every constructor
of the current live world. Its example checks compute:

    Example 4 matched world                 1 change
    Example 12 X₁′ allocation               1 change
    Example 12 Z′ alias allocation          2 changes
    Example 12 C1 outside-scope world       3 changes
    Example 12 C5 runtime world             3 changes

Thus the live shape uses `emptyᶜ` and one snoc constructor, with the actual
change as its second argument. The updated probe checks this definition
directly rather than translating from the former world.

## Source rebase as a change

The additional change needed for reveal is:

    rebaseSourceᶜ :
        (γ : Γᴸ ⊑ᶜ Γᴿ)
      -> (X : TyVar (Δᵉ Γᴸ))
      -> (Y : TyVar (Δᵉ Γᴿ))
      -> PivotUpdateᵗ
           (ηᴸᶜ γ) X (toRenameⁱ (ηᴿᶜ γ) Y)
      -> (＇ X) ⊑ᵀ⟨ γ ⟩ lookupStore (Σᵉ Γᴿ) Y
      -> Γᴸ ⊑ᶜ Γᴿ

Here `ηᴸᶜ` means the current source injection. `PivotUpdateᵗ` stores the new
source injection, proves that `X` moves to the center position occupied by
`Y`, and proves that every other source image stays fixed. The last premise is
the direct representation comparison in the predecessor world.

An order-preserving source thinning is too restrictive. The checked source
pair in `notes/SourceBindLiftLeftTrustedProbe.agda` reaches a protected-binder
checkpoint where allocation leaves the source images

    X ↦ X, Y ↦ Y

and the next reveal must rebase `X` to the target pivot at center 3 while
preserving the fresh allocation:

    X ↦ X₁, Y ↦ Y

This map is injective but not order preserving. The live reconstruction in
`notes/ArbitraryInjectionWorldProbe.agda` checks both the source-only and
paired-allocation versions of this counterexample. Actual syntax weakening,
allocation changes, and center changes remain order-preserving embeddings;
only the two endpoint-to-center maps are arbitrary injections.

The old extensional premises are now derived theorems:

    rebaseSource-before-apartᵗ
    rebaseSource-alignedᵗ
    rebaseSource-offᵗ

The defining equations are:

    centerᶜ (rebaseSourceᶜ γ X Y ok represented) = centerᶜ γ
    ηᴸᶜ     (rebaseSourceᶜ γ X Y ok represented) =
      rebaseSourceEmbeddingᵗ ok
    ηᴿᶜ     (rebaseSourceᶜ γ X Y ok represented) = ηᴿᶜ γ
    marksᶜ  (rebaseSourceᶜ γ X Y ok represented) = marksᶜ γ

Thus the predecessor `γ` retains the allocation evidence needed at the
boundary, while the constructor result is the world used for the recursive
term-imprecision comparison. Nested rebases retain the entire predecessor
chain.

There is no separate base, pending, active, mode, action, or wrapper family.
Nested reveals are successive source-rebase changes in the same history.

## Reveal and conceal

For a fixed rebase step `s`, define:

    revealWorld γ s = rebase-sourceᶜ γ s
    concealWorld (rebase-sourceᶜ γ s) = γ

The cancellation equations are constructor equations:

    concealWorld (revealWorld γ s) = γ

    revealWorld (concealWorld (rebase-sourceᶜ γ s)) s
      = rebase-sourceᶜ γ s

The first equation is the direction used when an arrow reveal introduces an
argument conceal. The second is available when inversion shows that a conceal
is crossing the same boundary.

The checked live probes establish the following cases:

- Example 4's matched `Nat`/star allocation is already aligned and therefore
  uses paired reveal/conceal without a rebase;
- Example 12's outside-to-`X₁′` edge;
- Example 12's `X₁′`-to-`Z′` edge;
- the same two Example 12 edges after the paired runtime `Nat` allocation;
- target embeddings and marks remain frozen across the two rebases;
- representation comparison holds in the predecessor world while body
  comparison holds in the rebased world.

## Which world checks which fact

Term and type imprecision always use the current embeddings:

    A ⊑ᵀ⟨ γ ⟩ B =
      marksᶜ γ ⊢
        renameᵗ (toRenameⁱ (ηᴸᶜ γ)) A ⊑
        renameᵗ (toRenameⁱ (ηᴿᶜ γ)) B

In particular, `bind-term` must store its argument comparison in the current
world. It must not silently revert to the predecessor allocation embedding.

A reveal boundary uses two worlds:

    γ-before
      checks the conversion representation comparison

    γ-after = revealWorld γ-before s
      checks the recursively related terms and their result types

For Example 12's inner `Z′` reveal:

    γ-before aligns X with X₁′
    γ-after aligns X with Z′

This is why the `Z′` representation comparison succeeds before the rebase and
fails if it is incorrectly repeated after the rebase.

`representationsImprecise` should remain, but its current unrestricted
statement must be narrowed. A rebase-created alignment is not an allocation
pair and does not imply that the two direct store entries are imprecise in the
rebased world. The allocation proof stored in the predecessor world remains
valid; the reveal rule consumes the representation comparison in that
predecessor world.

This avoids inventing representation-chain resolution and preserves the direct
store-entry invariant.

## Allocation history is not replayed

The target alias `Z′ maps to X₁′` was fresh when it was allocated. After
rebasing `X` to `X₁′`, repeating that old freshness check is false. Therefore
a rebase must not rebuild the target bind constructors in a new order.

Appending a source-rebase change preserves the preceding allocation evidence
verbatim. Later allocations append further changes; lifting a rebase through
such an allocation preserves its off-pivot equations.

## Implemented World scope

The live World change contains:

1. the two-constructor world history and its genuine change evidence;
2. the source-rebase change;
3. the four defining equations for center, current source embedding, target
   embedding, and marks;
4. the corrected current-world formulation of `bind-term`;
5. the narrowed direct-representation invariant.

No target rebase should be added without a trusted example that requires it.

The live CTI now uses its world as an index. Target reveal appends one source
rebase change and target conceal removes that exact outer change by inversion.
Example 4 remains in one world through paired reveal/conceal; Example 12 C1
checks the outside-to-`X₁′` and `X₁′`-to-`Z′` target reveals and has a pinned
generated ladder.
