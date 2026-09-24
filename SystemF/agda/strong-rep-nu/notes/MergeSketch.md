# Merging boundaries — design sketch (2026-09-24)

Status: IMPLEMENTED at 5d98bbe2 (definitional layer 0e662d1b, ports
and proofs 5d98bbe2), on the "Proposed statements (revised 2026-09-24)" section
below with the corrections marked there.  The sections before
"Decisions" are the proposal as written: where they say "today" they
mean the calculus BEFORE `Merge` (with `CancelR`, `IdPush` and
`Nu-⟪⟫`), and where they disagree with the revised statements, the
revised statements and the Agda win.  Data comes from
`notes/StackCensus.agda`, which renders with
`scripts/render_term.sh 'census' 'open import strong-rep-nu.notes.StackCensus'`
(since `Merge`, every pair that census finds is a `Merge` redex).

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

### Re-rendered after `Merge` (2026-09-24, 5d98bbe2)

The same census, taken over the implemented runs.  Tags are
`inner-value·c₁/c₂` over the new sorts (`t;seal`, `unseal;c`).  The
occurrences are totals over all states.

| stacked pair | occurrences | runs |
|---|---|---|
| `$·seal/idv`           | 56 | D, G, H, L, N, Q, S |
| `Λ·all/all`            | 23 | C, E, N, V |
| `ƛ·fun/fun`            | 17 | C, E, G, H, I, J, K, N, S, V |
| `$·seal/unseal`        | 11 | D, G, H, J, L, N, P, Q, R, S, U |
| `$·t;seal/idv`         |  6 | R |
| `$·seal/seal`          |  3 | J, R, S |
| `ƛ·seal/unseal`        |  3 | A, B |
| `b·seal/unseal`        |  2 | F, I |
| `$·t;seal/unseal`      |  2 | R, S |
| `b·t;seal/unseal;c`    |  2 | E, V |
| `Λ·seal/unseal`        |  2 | I, N |
| `ƛ·fun/seal`           |  1 | B |
| `ƛ·t;seal/unseal;c`    |  1 | C |

Rules fired over the 19 runs: `Merge` 66, `Beta` 46, `Peel` 45, `Nu-Λ` 29,
`Drop$` 26, `Nu-⟪Λ⟫` 14, `Drop-true` 4, `Drop-false` 1.  No state holds
more than TWO stacked pairs (before `Merge` the maximum was 11, in V).

A stack in EVALUATION position is merged on the very next step.  The
stacks that persist sit under a binder.  In G, for example,
`((7 ⟪ ↓Z , seal Z ⟫) ⟪ ↓Y , id Z ⟫) ⟪ ↓X , id Z ⟫` stays inside a
`λx:ℕ.` body across steps 3–8: these are the frame-exact wrappers that
`Beta` puts on a value crossing a `Λ` (`crossΛᴹ`).  They are merged, one
per step, once the application reaches them (steps 9–12).

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
  generalises to a pivot SET for question 4.  (Neither carried over in
  the end: endpoint indexing was withdrawn to keep representation
  variables, and question 4 was answered by retiring Canonicity; see
  "Decisions".)

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
`Nu-⟪Λ⟫` the state is:

    Ξ = [α := β , β := 𝔹]
    ((((λx:X. true) ⟪ ↓Y , (id X ↦ id 𝔹) ⟫) ⟪ ↥X , (seal X ↦ id 𝔹) ⟫)
         ⟪ ↥Y , (seal Y ↦ id 𝔹) ⟫) · false

Before `Merge`, two `Peel`s took the argument through the three layers
one at a time, and three `Drop-true`s peeled the result.  With `Merge`
the rest of the run is (RENDERED at 5d98bbe2 by
`scripts/render_term.sh 'showRun 0 9 K₀-⊢' 'open import strong-rep-nu.Examples'`,
continuing from the state above; each line is one state, the store
`Ξ = [α := β , β := 𝔹]` throughout):

    ((((λx:X. true) ⟪ ↓Y , (id X ↦ id 𝔹) ⟫) ⟪ ↥X , (seal X ↦ id 𝔹) ⟫) ⟪ ↥Y , (seal Y ↦ id 𝔹) ⟫) · false
      --[Merge]-->
    (((λx:X. true) ⟪ ↥X , ↓Y , (seal X ↦ id 𝔹) ⟫) ⟪ ↥Y , (seal Y ↦ id 𝔹) ⟫) · false
      --[Merge]-->
    ((λx:X. true) ⟪ ↥Y , ↥X , ↓Y , ((seal Y ; seal X) ↦ id 𝔹) ⟫) · false
      --[Peel]-->
    ((λx:X. true) · (false ⟪ ↥Y , ↓X , ↓Y , seal Y ; seal X ⟫)) ⟪ ↥Y , ↥X , ↓Y , id 𝔹 ⟫
      --[Beta]-->
    true ⟪ ↥Y , ↥X , ↓Y , id 𝔹 ⟫
      --[Drop-true]-->
    true

That is 9 steps against the 11 before `Merge`, and no state carries
more than one boundary on a value.  The first `Merge` composes
`(id X ↦ id 𝔹) ⨟ (seal X ↦ id 𝔹)` to `seal X ↦ id 𝔹`; the second
composes the domains `seal Y ⨟ seal X` (contravariantly) to the seal
chain `seal Y ; seal X`, whose identity middle is implicit.  (The
proposal's hand derivation wrote that chain as `id 𝔹 ; seal Y ; seal X`
and the argument's scope as `dual Θ`; the rendered run shows the
implemented, tighter spellings above.)

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
- The three-sort grammar with `NoCancel`, as three syntactic datatypes.
  ("Endpoint-indexed" was withdrawn once representation variables were
  kept; see below.)
- `Nu-⟪Λ⟫` keeps its stacked (N1) contractum, and `Merge` fires next.
- Composition takes the conversion context (option (c)), written
  `Δ ⊢ c₁ ⨟ c₂` with the context first: `seal X` meeting `unseal X`
  writes `mkId` of `X`'s representation, which only the context knows
  (`repOf Δ X`, through `Lookup.agda`'s `∋:=?`), and composition under
  `∀` reads at `underΛ Δ`.
- `proof/Canonicity.agda` is retired when `Merge` lands: the single-binder
  invariant is exactly what merging gives up.
- The work continues on branch `strong-rep-nu` (PR #209).

## Proposed statements (revised 2026-09-24: representation variables kept)

Jeremy: keep the current design, where a seal or unseal carries only the
ordinary NAME `X` and its representation is read through the lookup
square `Δ ∋ X := R` (CONVERSIONS ARE REP-FREE).  Two consequences:

- **The sorts are syntactic but not endpoint-indexed.**  `seal X`'s
  source is `X`'s representation spelled in `Δ`, so no syntax index can
  state it.  The endpoints come from a per-sort typing judgement, as
  today.
- **Standalone `seal X` and `unseal X` return.**  `unseal X ; id R` would
  have to spell `R`, which may be compound (run B has `ℕ⇒ℕ`).  So a bare
  `seal X` or `unseal X` stands for an identity middle, and a chain
  extends only a NON-identity — GTPLC's `A ≢ B` premise.

**Syntax** (`Conversion.agda`):

    mutual
      data Mid : Set where
        id   : Ty → Mid                 -- typing restricts A to a base type or a variable
        _↦_  : Conv → Conv → Mid
        `∀   : Conv → Mid

      data Tail : Set where
        mid     : Mid → Tail
        seal    : ℕ → Tail              -- the identity middle, then seal X
        _⨾seal_ : Tail → ℕ → Tail       -- t ; seal X

      data Conv : Set where
        tail      : Tail → Conv
        unseal    : ℕ → Conv            -- unseal X, then the identity middle
        unseal_⨾_ : ℕ → Conv → Conv     -- unseal X ; c

**Identity** is syntactic.  It includes the structural identities, so
that `(id ℕ ↦ id ℕ) ; seal Y` is not a second spelling of `seal Y`:

    IsIdᵐ (id A)   = ⊤
    IsIdᵐ (s ↦ t)  = IsIdᶜ s × IsIdᶜ t
    IsIdᵐ (`∀ s)   = IsIdᶜ s
    IsIdᶜ (tail (mid g)) = IsIdᵐ g
    IsIdᶜ c              = ⊥          for every other shape of c

**Typing** (per sort, with the endpoints read off `Δ`):

    Δ ⊢ g ∶ A ⇒ᵐ B
      id-base   Base ι                              ⟹  Δ ⊢ id ι ∶ ι ⇒ᵐ ι
      id-var    Δ ∋tv X                             ⟹  Δ ⊢ id (` X) ∶ X ⇒ᵐ X
      fun       Δ ⊢ s ∶ A′ ⇝ A ,  Δ ⊢ t ∶ B ⇝ B′    ⟹  Δ ⊢ s ↦ t ∶ A⇒B ⇒ᵐ A′⇒B′
      all       underΛ Δ ⊢ s ∶ A ⇝ B                ⟹  Δ ⊢ ∀ s ∶ ∀A ⇒ᵐ ∀B

    Δ ⊢ t ∶ A ⇒ᵗ B
      mid       Δ ⊢ g ∶ A ⇒ᵐ B                      ⟹  Δ ⊢ mid g ∶ A ⇒ᵗ B
      seal      Δ ∋ X := R                          ⟹  Δ ⊢ seal X ∶ R ⇒ᵗ X
      seal-seq  Δ ⊢ t ∶ A ⇒ᵗ R ,  Δ ∋ X := R ,  ¬ IsIdᵗ t
                                                    ⟹  Δ ⊢ t ⨾seal X ∶ A ⇒ᵗ X

    Δ ⊢ c ∶ A ⇝ B
      tail        Δ ⊢ t ∶ A ⇒ᵗ B                    ⟹  Δ ⊢ tail t ∶ A ⇝ B
      unseal      Δ ∋ X := R                        ⟹  Δ ⊢ unseal X ∶ X ⇝ R
      unseal-seq  Δ ∋ X := R ,  Δ ⊢ c ∶ R ⇝ B ,  ¬ IsIdᶜ c ,  NoCancel X c
                                                    ⟹  Δ ⊢ unseal X ⨾ c ∶ X ⇝ B

(`IsIdᵗ (mid g) = IsIdᵐ g`, and `IsIdᵗ t = ⊥` for the two seal forms.)

As implemented the three judgements are `_⊢ᵐ_∶_⇝_`, `_⊢ᵀ_∶_⇝_` and
`_⊢_∶_⇝_`, with constructors `conv-id`, `conv-idv`, `conv-fun`,
`conv-all`; `conv-mid`, `conv-seal`, `conv-seal-seq`; `conv-tail`,
`conv-unseal`, `conv-unseal-seq`.  The tail-sort identity is spelled
`IsIdᵀ`.

`NoCancel X c` says that `c` does not start by resealing `X`.  With the
identity middle now implicit, that means `c`'s seal chain does not begin
with a bare `seal X`:

    NoCancel X (tail (seal Y))       = X ≢ Y
    NoCancel X (tail (t ⨾seal Y))    = NoCancelᵗ X t
    NoCancelᵗ X (seal Y)             = X ≢ Y
    NoCancelᵗ X (t ⨾seal Y)          = NoCancelᵗ X t
    NoCancelᵗ X (mid g)              = ⊤        (a non-identity middle blocks the cancel)
    NoCancel X (tail (mid g))        = ⊤
    NoCancel X (unseal Y)            = ⊤
    NoCancel X (unseal Y ⨾ c)        = ⊤

**Composition** is an untyped function on the syntax.  Its correctness
is a lemma.  As IMPLEMENTED (`Conversion.agda` §4b, `proof/Compose.agda`)
the function takes the context first and the lemma needs unique names:

    _⊢_⨟_ : Ctxᵗ → Conv → Conv → Conv
    ⊢⨟    : Unique (names Δ)
          → Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C → Δ ⊢ (Δ ⊢ c₁ ⨟ c₂) ∶ A ⇝ C

(The proposal wrote `_⨟_ : Conv → Conv → Conv` and `⊢⨟` without the
`Unique` premise.  The context is needed where `seal X` meets
`unseal X`, whose result is `mkId (repOf Δ X)`; `Unique` is what
`∋:=-det` needs at that pair and at `repOf`.)

Each clause is justified by typing.  Pairs that typing rules out, such
as `seal X` followed by `unseal Y` with `X ≢ Y`, get an arbitrary result
in the function; the lemma never looks at them.  The smart constructors
`_⨾sealˢ_` and `unseal_⨾ˢ_` drop an identity middle (turning `mid g`
with `IsIdᵐ g` into a bare `seal X`/`unseal X`) and apply the
`NoCancel` cancellation (`unseal X` then `seal X` is `mid (id (` X))`).

**Terms and values** (`Terms.agda`): `_⟪_,_⟫ : Term → Boundary → Conv →
Term` is unchanged.

    data Simple : Term → Set      -- $n, true, false, ƛ, Λ
    data Value  : Term → Set where
      V-simple : Simple U → Value U
      V-⟪⟫     : Simple U → InertTail t → Value (U ⟪ Θ , tail t ⟫)

`InertTail t` has the constructors `I-idv` (`mid (id (` X))`), `I-fun`,
`I-all`, `I-seal` and `I-seal-seq`: every typed tail except `mid (id A)`
with `A` a base type.

**Merge** (`Reduction.agda`) replaces `CancelR` and `IdPush`:

    Merge : Simple U → InertTail t₁
      → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ   → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
      → Δ ⊢ᶜ Θ₂ ⇒ Δ₂ᶜ  → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
      → SameConv Δ⋉ᶜ (tail t₁′) Δ₁ᶜ (tail t₁)
      → SameConv Δ⋉ᶜ c₂′ Δ₂ᶜ c₂
      → Δ ⊢ (U ⟪ Θ₁ , tail t₁ ⟫) ⟪ Θ₂ , c₂ ⟫
          -→ U ⟪ Θ₁ ++ Θ₂ , Δ⋉ᶜ ⊢ tail t₁′ ⨟ c₂′ ⟫ ∣ none

(As implemented; the composition is taken at the merged conversion
context `Δ⋉ᶜ`.)

That `t₁′`'s target and `c₂′`'s source agree at `Δ⋉ᶜ` is a lemma: they
re-spell one representation at one context, and the names there are
unique.  `SameConv` extends to the new sorts leaf by leaf, as today.

**The rules that change shape**: `Peel` matches `tail (mid (s ↦ t))`,
`Nu-⟪Λ⟫` matches `tail (mid (∀ s))`, and the drops match
`tail (mid (id A))` with `A` a base type.  `Nu-⟪⟫`, `CancelR` and
`IdPush` are deleted.  `reveal`/`conceal` keep their signatures and
emit bare `unseal X`/`seal X`, so the compiler is unchanged.  The
theorem statements are unchanged: `Progress`, `Preservation`, `det`,
`TypeSafety`, `compile-⊢`.
