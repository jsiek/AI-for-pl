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
`(V ⟪ Θ₁ , c₁ ⟫) ⟪ Θ₂ , c₂ ⟫` to `V ⟪ Θ₁ ++ Θ₂ , … ⟫`.  They handle an
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

**(1) Composition `c₁ ⨟ c₂`** (first `c₁`, then `c₂`), defined on two
conversions spelled at ONE conversion context:

    id X      ⨟ c          = c
    c         ⨟ id X       = c
    seal X    ⨟ unseal X   = mkId A      (Δ ∋ X := A — what CancelR does)
    (s₁↦t₁)   ⨟ (s₂↦t₂)    = (s₂ ⨟ s₁) ↦ (t₁ ⨟ t₂)    (the domain flips)
    ∀ s₁      ⨟ ∀ s₂       = ∀ (s₁ ⨟ s₂)
    c         ⨟ seal X     = c ; seal X          ← NEW grammar
    unseal X  ⨟ c          = unseal X ; c        ← NEW grammar (only inside a domain)

The census forces the two new forms.  `fun/seal` (run B) seals a
converted function.  `seal/seal` (runs J, K, R) seals twice: this arises
exactly when the second cell is an ALIAS, `α := β`, from decision (a).  In
K the argument crosses `seal Y` and then `seal X`, where X's cell holds Y.
No single `Conv` of today's grammar denotes either composite.  So a
conversion becomes a NORMAL FORM, as in space-efficient coercions:

    c  ::=  unseal X ; … ; g ; … ; seal Y       (possibly empty chains)
    g  ::=  id A | s ↦ t | ∀ s

(Adjacent `seal X ; unseal X` cancel, so a normal form never contains
that pair.)

**(2) One merge rule**, subsuming `CancelR` and `IdPush`:

    (Merge)  Δ ⊢ (U ⟪ Θ₁ , c₁ ⟫) ⟪ Θ₂ , c₂ ⟫ -→ U ⟪ Θ₁ ++ Θ₂ , c₁′ ⨟ c₂′ ⟫ ∣ none

Here `c₁′` and `c₂′` are `c₁` and `c₂` re-spelled at the MERGED conversion
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
    --[Merge]-->   the domain composes to seal Y ; seal X   (X's cell holds Y)
    (λx:X. true) ⟪ ↓Y , ↥X , ↥Y , ((seal Y ; seal X) ↦ id 𝔹) ⟫ · false
    --[Peel]-->
    ((λx:X. true) · (false ⟪ … , seal Y ; seal X ⟫)) ⟪ … , id 𝔹 ⟫
    --[Beta]-->  --[Drop-true]-->
    true

That is 9 steps against today's 11, and no state carries more than one
boundary on a value.

## Questions for Jeremy

1. **Chains.**  Accept the normal-form grammar, with `; seal Y` and
   `unseal X ;` chains?  The `seal ; seal` chain exists only because of
   alias cells (decision (a)).  The `fun ; seal` chain exists regardless.
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
   invariant be generalised, or retired?
