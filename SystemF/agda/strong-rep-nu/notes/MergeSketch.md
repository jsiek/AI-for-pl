# Merging boundaries — design sketch (2026-09-24)

Status: PROPOSAL.  Nothing here is implemented.  Data comes from
`notes/StackCensus.agda`, which renders with
`scripts/render_term.sh 'census' 'open import strong-rep-nu.notes.StackCensus'`.

## The goal

Today a value can carry any number of boundaries: `V-⟪⟫ : Value M → Inert c
→ Value (M ⟪ Θ , c ⟫)`.  The proposal is ONE boundary per value:

    Simple U  ::=  $n | true | false | ƛA.N | Λ N         (not a boundary)
    Value     ::=  U | U ⟪ Θ , c ⟫   where c is inert

A second boundary on a value is then a redex, and a MERGE rule removes it.
`CancelR` and `IdPush` are already merges: both rewrite
`(V ⟪ Θ₁ , c₁ ⟫) ⟪ Θ₂ , c₂ ⟫` to `V ⟪ Θ₁ ++ Θ₂ , c ⟫`, with `c` being
`mkId A′` or `unseal X′` respectively.  They handle an
ACTIVE outer conversion.  What is missing is the case where the outer
conversion is INERT as well.

## What the census shows

The census looks at every state of the 19 compiled `Examples` runs.  In
each state it records every place where a value boundary `V ⟪ Θ₁ , c₁ ⟫`
sits directly under another boundary `⟪ Θ₂ , c₂ ⟫`.  Below, `c₁/c₂` gives
the head constructors, and "occurrences" totals the counts over all states.

| inner `c₁` / outer `c₂` | occurrences | runs | handled today by |
|---|---|---|---|
| `seal` / `idv`   | 214 | 14 | nothing (it stacks) |
| `fun` / `fun`    | 101 | 11 | nothing (Peel crosses both, one per step) |
| `idv` / `seal`   |  92 |  5 | nothing |
| `idv` / `idv`    |  62 | 11 | nothing |
| `idv` / `unseal` |  55 | 13 | `IdPush` |
| `all` / `all`    |  43 |  4 | nothing — this is what `Nu-⟪⟫` exists for |
| `seal` / `unseal`|  31 | 18 | `CancelR` |
| `seal` / `seal`  |  12 |  3 | nothing — an ALIAS cell (J, K, R) |
| `fun` / `seal`   |   2 |  1 | nothing (B) |

The largest number of stacked pairs in one state: V 11, E 7, C 7, D 5,
G 5.  `IdPush` and `CancelR` together account for 22 of V's 49 steps.

## Proposal

**(1) A normal-form grammar for conversions**, in three sorts, read off
the SOURCE and TARGET types.

*Where the idea comes from.*
- GTLC (`GTLC/agda/Coercions.agda`, § Structural Coercion Normal Forms)
  splits its normal forms into three mutually defined sorts:
  `_⇨ⁿ_` (projection head) / `_⇨ᵗ_` (injection tail) / `_⇨ᵐ_` (the
  structural middle, `_↦_` only).
- GTPLC (`GTPLC/NarrowWiden.agda`, `Rationale.md` § canonical
  association) fixes how chains ASSOCIATE — seal chains to the left,
  unseal chains to the right — and enforces it with endpoint premises.
  Its `seal-seq : c ︔ seal X` and `unseal-seq : unseal X ︔ c` are our
  chains.
- GTSF (`GTSF/NarrowWiden.agda`) separates "cross" (structural)
  categories from "strict" (non-identity) ones, so that no identity can
  hide inside a sequence.

- GTSFImp (`GTSFImp/Conversion.agda`) is the closest relative, and it is
  the design that does NOT merge.  Its conversions are INTRINSICALLY
  endpoint-typed and split by polarity: `Conv↑ Δ A B` (reveal —
  `unseal`, with a `Conv↓` domain) and `Conv↓ Δ A B` (conceal — `seal`,
  with a `Conv↑` domain).  Each has at most one PIVOT variable
  (`_⊢↑[_]_`, joined by `PivotJoin`).  Values keep stacks
  (`RevealValue`/`ConcealValue` over any value), and the only merge is
  the cancel `conceal-reveal`.  Neither sort is closed under
  composition: reveal-then-conceal at two different pivots is in
  neither.  That is exactly the gap the chains below fill.  Two things
  carry over: (i) endpoint-indexed syntax, which makes "the middle type
  decides the clause" a matter of the indices; (ii) the pivot, which
  generalises to a pivot SET for question 4.

strong-rep-nu has no `★`, so the only sequencing is by seal and unseal.
The types force their positions:
- `unseal X ; c` has source `` ` X ``, so unseals can only open a
  conversion whose SOURCE is a variable;
- `t ; seal Y` has target `` ` Y ``, so seals can only close a
  conversion whose TARGET is a variable;
- between the two sits one structural middle.

    g  ::=  id A  |  c ↦ c  |  ∀ c                 middle     (A base or a variable)
    t  ::=  g  |  t ; seal X                       tail       (seal chain, associates LEFT)
    c  ::=  t  |  unseal X ; c                     conversion (unseal chain, associates RIGHT)

Typing, one judgement per sort (`Δ ∋ X := R` is today's lookup square):

    Δ ⊢ g ∶ A ⇒ᵐ B
      id-base   Base ι                               ⟹  Δ ⊢ id ι ∶ ι ⇒ᵐ ι
      id-var    Δ ∋tv X                              ⟹  Δ ⊢ id X ∶ X ⇒ᵐ X
      fun       Δ ⊢ s ∶ A′ ⇝ A ,  Δ ⊢ t ∶ B ⇝ B′     ⟹  Δ ⊢ s ↦ t ∶ A⇒B ⇒ᵐ A′⇒B′
      all       underΛ Δ ⊢ s ∶ A ⇝ B                 ⟹  Δ ⊢ ∀ s ∶ ∀A ⇒ᵐ ∀B

    Δ ⊢ t ∶ A ⇒ᵗ B
      mid       Δ ⊢ g ∶ A ⇒ᵐ B                       ⟹  Δ ⊢ g ∶ A ⇒ᵗ B
      seal      Δ ⊢ t ∶ A ⇒ᵗ R ,  Δ ∋ Y := R         ⟹  Δ ⊢ t ; seal Y ∶ A ⇒ᵗ Y

    Δ ⊢ c ∶ A ⇝ B
      tail      Δ ⊢ t ∶ A ⇒ᵗ B                       ⟹  Δ ⊢ t ∶ A ⇝ B
      unseal    Δ ∋ X := R ,  Δ ⊢ c ∶ R ⇝ B ,  NoCancel X c
                                                     ⟹  Δ ⊢ unseal X ; c ∶ X ⇝ B

*Why it is tight.*
- There is NO standalone `seal X` or `unseal X`.  Today's `seal X` is
  the tail `id R ; seal X` (with R written as `mkId` when R is
  compound), and today's `unseal X` is `unseal X ; id R`.  So every
  conversion has exactly one middle.
- `id` stays restricted to base types and variables; a compound
  identity is the structural `mkId`, as today.
- A seal can never be followed by an unseal, because seals only close a
  conversion and unseals only open one.  Hence the redex `seal X ;
  unseal X` is not even expressible.
- The one remaining redundancy is `unseal X ; id R ; seal X`, which
  equals `id X`.  It can only occur when the middle is an identity, and
  `NoCancel` rules it out:

        NoCancel X (unseal Y ; c)  =  ⊤
        NoCancel X t               =  ¬ (middle t is an identity  ×  the first seal of t is X)

  `NoCancel` only ever looks at the innermost unseal: an outer unseal
  could only cancel after the inner one did, and that cancellation is
  already excluded.

*What reaches a value.*  The Simple part `U` of a value has a
non-variable type (ℕ, 𝔹, ⇒ or ∀), so a value boundary's conversion
has a non-variable SOURCE.  It therefore has no unseal chain: it is a
TAIL.  The one active tail is `id ι`, which `Drop$`/`Drop-true`/
`Drop-false` remove.  Every other tail is inert:

    Value  ::=  U  |  U ⟪ Θ , t ⟫      where t ≠ id ι

**Composition** `c₁ ⨟ c₂` (first `c₁`, then `c₂`) at one conversion
context.  It has one operator per sort and recurses on the sorts alone.
It is total on well-typed pairs, because the type in the middle decides
which clause applies.  Where a clause relies on that, the right-hand
comment says why.

    (unseal X ; c₁) ⨟ c₂        =  unseal X ;ˢ (c₁ ⨟ c₂)
    (t ; seal X) ⨟ (unseal X ; c) =  t ⨟ c        the CancelR step (the types force equal names)
    g ⨟ (unseal X ; c)          =  unseal X ; c   g's target is ` X, so g = id X
    t ⨟ t₂                      =  t ⨟ᵗ t₂

    t ⨟ᵗ (t₂ ; seal Y)          =  (t ⨟ᵗ t₂) ; seal Y
    (t ; seal X) ⨟ᵗ g₂          =  t ; seal X     g₂'s source is ` X, so g₂ = id X
    g ⨟ᵗ g₂                     =  g ⨟ᵐ g₂

    id A    ⨟ᵐ g₂               =  g₂
    g       ⨟ᵐ id B             =  g
    (s ↦ t) ⨟ᵐ (s′ ↦ t′)        =  (s′ ⨟ s) ↦ (t ⨟ t′)   the domain flips
    ∀ s     ⨟ᵐ ∀ s′             =  ∀ (s ⨟ s′)

`unseal X ;ˢ c` is the only smart constructor.  If `c` violates
`NoCancel X` — that is, `c` is a tail whose middle is an identity and
whose first seal is `X` — it returns `id X`.  Otherwise it returns
`unseal X ; c`.

**(2) One merge rule**, subsuming `CancelR` and `IdPush`:

    (Merge)  Δ ⊢ (U ⟪ Θ₁ , t₁ ⟫) ⟪ Θ₂ , c₂ ⟫ -→ U ⟪ Θ₁ ++ Θ₂ , t₁′ ⨟ c₂′ ⟫ ∣ none

Here `t₁′` and `c₂′` are `t₁` and `c₂` re-spelled at the MERGED conversion
context of `Θ₁ ++ Θ₂`.  They are carried, pinned by `SameConv`, the same
way `CancelR` carries `A′` and `IdPush` carries `X′`.  If the merged
conversion is active (`id` at a base type), `Drop$`/`Drop-true`/
`Drop-false` fire next.

**(3) `Nu-⟪⟫` goes away.**  The operand of `ν` is a value of `∀` type.
Under the single-boundary invariant, that value is either `Λ N` or
`(Λ N) ⟪ Θ , ∀ s ⟫`: the Simple part of a `∀` value can only be a `Λ`.
So only `Nu-Λ` and `Nu-⟪Λ⟫` remain.  The run-time reveal `Nu-⟪⟫` minted
goes with it, and after that every reveal is written by the compiler.

## On an example: §1b, `K`

The first three steps (`Nu-Λ`, `Peel`, `Beta`) are unchanged.  After
`Nu-⟪Λ⟫` the state is (rendered from today's run):

    Ξ = [α := β , β := 𝔹]
    ((((λx:X. true) ⟪ ↓Y , (id X ↦ id 𝔹) ⟫) ⟪ ↥X , (seal X ↦ id 𝔹) ⟫)
         ⟪ ↥Y , (seal Y ↦ id 𝔹) ⟫) · false

Today two `Peel`s take the argument through the three layers one at a
time, and three `Drop-true`s peel the result.  With `Merge` (HAND-DERIVED;
frame spellings not checked):

    --[Merge]-->   (id X ↦ id 𝔹) ⨟ (seal X ↦ id 𝔹) = seal X ↦ id 𝔹
    ((λx:X. true) ⟪ ↓Y , ↥X , (seal X ↦ id 𝔹) ⟫) ⟪ ↥Y , (seal Y ↦ id 𝔹) ⟫ · false
    --[Merge]-->   the domain composes to the tail id 𝔹 ; seal Y ; seal X
    (λx:X. true) ⟪ ↓Y , ↥X , ↥Y , ((id 𝔹 ; seal Y ; seal X) ↦ id 𝔹) ⟫ · false
    --[Peel]-->
    ((λx:X. true) · (false ⟪ dual Θ , id 𝔹 ; seal Y ; seal X ⟫)) ⟪ Θ , id 𝔹 ⟫
    --[Beta]-->  --[Drop-true]-->
    true

That is 9 steps against today's 11, and no state carries more than one
boundary on a value.

## Questions for Jeremy

1. **The grammar.**  Accept the three-sort grammar (middle / tail /
   conversion) with `NoCancel`?  A seal chain of length two or more
   exists only because of alias cells (decision (a)).  A tail
   `(s ↦ t) ; seal Y` exists regardless (run B).  A further option is to
   make the sorts SYNTACTIC and ENDPOINT-INDEXED — `Mid Δ A B`,
   `Tail Δ A B`, `Conv Δ A B`, as GTLC's `_⇨ᵐ_`/`_⇨ᵗ_`/`_⇨ⁿ_` and
   GTSFImp's `Conv↑`/`Conv↓` do — rather than one untyped `Conv`
   constrained by a typing judgement.  `NoCancel` then reads as a
   condition on indices: in `unseal X ; c`, if `c`'s middle is an
   identity, the first seal of `c` is not `X`.  Equivalently, an
   identity middle sits at the meeting point of the unseal path and
   the seal path through the alias cells, and not above it.
2. **When to merge.**  Take the separate `Merge` step (M1, sketched above,
   which generalises `CancelR`/`IdPush`)?  Or merge ON CONSTRUCTION (M2):
   every rule that would build a stack — `Peel`'s argument, `Beta`'s
   crossed-`Λ` wrapper, `Nu-⟪Λ⟫` — builds the merged boundary directly?
   M2 never builds a stack, but every such rule then carries the merge's
   re-spelling premises.
3. **`Nu-⟪Λ⟫` under M1.**  Its stacked contractum is merged one step
   later.  That is exactly the fused shape (N2) you declined, now reached
   in two steps and with general composition in place of `instReveal`.
   Is that acceptable?
4. **Canonicity.**  The single-binder family `CanonC` cannot contain a
   `seal Y ; seal X` chain, which cites two binders.  Should the
   invariant be generalised — to a pivot SET, in the spirit of
   GTSFImp's `PivotJoin` — or retired?

## Decisions (Jeremy, 2026-09-24)

- A separate `Merge` step (M1), not merge-on-construction.
- The three-sort grammar with `NoCancel`, as ENDPOINT-INDEXED datatypes.
- `Nu-⟪Λ⟫` keeps its stacked (N1) contractum, and `Merge` fires next.
- `proof/Canonicity.agda` is retired when `Merge` lands: the single-binder
  invariant is exactly what merging gives up.
- The work continues on branch `strong-rep-nu` (PR #209).

## Proposed statements (for review before implementing)

**Syntax** (`Conversion.agda`).  The sorts are indexed by their endpoints.
A seal or unseal carries the representation spelling `R` in its
indices, as GTSFImp's `seal X R` does.  The context enters only through
the validity judgement below.

    data Atomic : Ty → Set where           -- where a bare `id` may sit
      at-base : Base A → Atomic A
      at-var  : Atomic (` X)

    mutual
      data Mid : Ty → Ty → Set where
        id    : Atomic A → Mid A A
        _↦_   : Conv A′ A → Conv B B′ → Mid (A ⇒ B) (A′ ⇒ B′)
        `∀    : Conv A B → Mid (`∀ A) (`∀ B)

      data Tail : Ty → Ty → Set where
        mid     : Mid A B → Tail A B
        _⨾seal_ : Tail A R → (X : ℕ) → Tail A (` X)

      data Conv : Ty → Ty → Set where
        tail      : Tail A B → Conv A B
        unseal_⨾_ : (X : ℕ) (c : Conv R B) → NoCancel X c → Conv (` X) B

`NoCancel X c` is a computed `Set`: `⊥` if `c` is a tail whose middle
is an identity and whose first seal is `X`, and `⊤` otherwise.  Being
computed, its proofs are unique, so it does not break equality of
conversions.

**Validity** replaces `Δ ⊢ c ∶ A ⇝ B`.  Each seal and unseal must agree
with the lookup square, and each identity variable must be in scope:

    Δ ⊢ᶜᵛ c      for c : Conv A B      (and ⊢ᵗᵛ, ⊢ᵐᵛ for the other sorts)
      unseal : Δ ∋ X := R → Δ ⊢ᶜᵛ c → Δ ⊢ᶜᵛ unseal X ⨾ c    (c : Conv R B)
      seal   : Δ ⊢ᵗᵛ t → Δ ∋ X := R → Δ ⊢ᵗᵛ t ⨾seal X     (t : Tail A R)
      id-var : Δ ∋tv X → Δ ⊢ᵐᵛ id at-var
      id-base: Δ ⊢ᵐᵛ id (at-base b)
      fun    : Δ ⊢ᶜᵛ s → Δ ⊢ᶜᵛ t → Δ ⊢ᵐᵛ s ↦ t
      all    : underΛ Δ ⊢ᶜᵛ s → Δ ⊢ᵐᵛ `∀ s
      mid    : Δ ⊢ᵐᵛ g → Δ ⊢ᵗᵛ mid g
      tail   : Δ ⊢ᵗᵛ t → Δ ⊢ᶜᵛ tail t

`reveal`/`conceal` gain the representation spelling:
`reveal : (X : ℕ) (A B : Ty) → Conv B (B [ X := A ]ᵗ)`.  The compiler
writes `reveal 0 (⇑ A) C`.

**Composition** — its typing is by construction:

    _⨟_  : Conv A B → Conv B C → Conv A C
    ⊢⨟   : Δ ⊢ᶜᵛ c₁ → Δ ⊢ᶜᵛ c₂ → Δ ⊢ᶜᵛ (c₁ ⨟ c₂)

**Terms and values** (`Terms.agda`):

    _⟪_,_⟫ : Term → Boundary → Conv A B → Term        (A and B implicit)

    data Simple : Term → Set      -- $n, true, false, ƛ, Λ
    data Value  : Term → Set where
      V-simple : Simple U → Value U
      V-⟪⟫     : Simple U → InertTail t → Value (U ⟪ Θ , tail t ⟫)

`InertTail t` holds unless `t = mid (id (at-base b))`.

**Merge** (`Reduction.agda`) replaces `CancelR` and `IdPush`:

    Merge : Simple U → InertTail t₁
      → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ   → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
      → Δ ⊢ᶜ Θ₂ ⇒ Δ₂ᶜ  → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
      → SameConv Δ⋉ᶜ (tail t₁′) Δ₁ᶜ (tail t₁)       -- t₁′ : Tail A′ M
      → SameConv Δ⋉ᶜ c₂′ Δ₂ᶜ c₂                     -- c₂′ : Conv M C′
      → Δ ⊢ (U ⟪ Θ₁ , tail t₁ ⟫) ⟪ Θ₂ , c₂ ⟫
          -→ U ⟪ Θ₁ ++ Θ₂ , tail t₁′ ⨟ c₂′ ⟫ ∣ none

The two re-spellings SHARE the middle index `M`, so `_⨟_` applies
without a cast.  That both `M`s agree is a lemma: they re-spell one
representation at one context, and the names there are unique.

**The rules that change shape**: `Peel` matches `tail (mid (s ↦ t))`,
`Nu-⟪Λ⟫` matches `tail (mid (∀ s))`, and the drops match
`tail (mid (id (at-base b)))`.  `Nu-⟪⟫`, `CancelR` and `IdPush` are
deleted.  The theorem statements are unchanged: `Progress`,
`Preservation`, `det`, `TypeSafety`, `compile-⊢`.
