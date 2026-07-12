# `enumMLB` Soundness Plan

File Charter:

- Purpose: top-down plan for proving the soundness target for
  `EndpointCanonicalMLBSimple.enumMLB`.
- Scope: theorem shape, proof decomposition, hard supporting lemmas, and the
  order in which to attack them.
- Main dependencies: `EndpointCanonicalMLBSimple.agda`, `ImprecisionWf.agda`,
  `ImprecisionProperties.agda`, and the list membership API.

## Goal

The core theorem should say that every type enumerated by `enumMLB` is a common
lower bound of the two endpoint types under the two imprecision contexts used
by the search.

Use a membership-based statement for the raw enumerator:

```agda
enumMLB-sound :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
  WfImpCtx² Δᶜ Δᴸ Φᴸ →
  WfImpCtx² Δᶜ Δᴿ Φᴿ →
  C ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B →
  Φᴸ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ ×
  Φᴿ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ
```

This should be the first proof target.  Top-level endpoint soundness can then
be a corollary:

```agda
allEndpointMlbsAt-sound :
  C ∈ allEndpointMlbsAt Δ A B →
  idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ ×
  idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ

MLB-sound :
  MLB Δ A B ≡ just C →
  idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ ×
  idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ
```

Do not start with `MLB-sound`.  Its proof depends mostly on
list plumbing, while the important semantic argument is in `enumMLB-sound`.

## Top-Down Proof Structure

### Layer 1. Public Endpoint Soundness

Prove these last.

1. `MLB-sound`
2. `allEndpointMlbsAt-sound`
3. optionally `simpleEndpointMlb-sound`, with `endpointCtx A B`

These proofs should use:

- `first-sound`: if `first xs ≡ just C`, then `C ∈ xs`.
- `pruneStrictlyBelow-sound`: membership after pruning implies membership
  before pruning.
- `dedupe-sound`: membership after deduplication implies membership before
  deduplication.
- `enumMLB-sound` instantiated with `Φᴸ = idᵢ Δ` and `Φᴿ = idᵢ Δ`.
- `WfImpCtx-to² (idᵢ-wf Δ)` for both endpoint sides.

Hardness: low, once the list lemmas exist.

### Layer 2. Raw Enumerator Soundness

This is the central theorem:

```agda
enumMLB-sound
```

Induct on `fuel`, and case split on the two endpoint types exactly as
`enumMLB` does.  The zero-fuel case is impossible by membership in `[]`.

For each recursive case, invert membership through the list constructor used by
that branch, apply the induction hypothesis, then wrap the two recursive
certificates with the corresponding `ImprecisionWf` constructors.

Hardness: medium, except for the three support lemmas listed in Layer 3.

### Layer 3. Hard Supporting Lemmas

These are the pieces to prove first.

#### 1. Boolean context lookup soundness

`enumMLB` uses boolean lookup functions:

```agda
hasVar  : ℕ → ℕ → ImpCtx → Bool
hasStar : ℕ → ImpCtx → Bool
```

For soundness, booleans must be converted into membership evidence:

```agda
hasVar-sound :
  hasVar W X Φ ≡ true →
  (W ˣ⊑ˣ X) ∈ Φ

hasStar-sound :
  hasStar W Φ ≡ true →
  (W ˣ⊑★) ∈ Φ
```

These should be proved by induction on `Φ`.

Also prove a small equality bridge for `_==ᵇ_`:

```agda
==ᵇ-true :
  X ==ᵇ Y ≡ true →
  X ≡ Y
```

Use this in the `hasVar` and `hasStar` cases where the boolean comparison
succeeds.

Why this is hard: without these lemmas, the variable cases cannot construct the
`idˣ` and `tagˣ` constructors of `ImprecisionWf`.

#### 2. Variable enumeration soundness

The variable clauses call:

```agda
varCandidatesUpTo Φᴸ Φᴿ A B Δᶜ
```

The proof needs one lemma for all three supported variable/star shapes:

```agda
varCandidatesUpTo-sound :
  WfImpCtx² Δᶜ Δᴸ Φᴸ →
  WfImpCtx² Δᶜ Δᴿ Φᴿ →
  C ∈ varCandidatesUpTo Φᴸ Φᴿ A B Δᶜ →
  Φᴸ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ ×
  Φᴿ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ
```

This lemma must recover:

- `C = ＇ W`,
- `W < Δᶜ`,
- the appropriate assumptions from `Φᴸ` and `Φᴿ`.

The better proof route is to recover `W < Δᶜ` from the contexts, not from the
enumeration limit.  Once boolean lookup soundness gives a membership proof such
as `(W ˣ⊑ˣ X) ∈ Φᴸ` or `(W ˣ⊑★) ∈ Φᴸ`, the hypothesis
`WfImpCtx² Δᶜ Δᴸ Φᴸ` directly gives the source-side bound needed by `idˣ` or
`tagˣ`.

First prove a stronger limit-polymorphic auxiliary theorem:

```agda
varCandidatesUpTo-sound-at :
  ∀ {limit Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
  WfImpCtx² Δᶜ Δᴸ Φᴸ →
  WfImpCtx² Δᶜ Δᴿ Φᴿ →
  C ∈ varCandidatesUpTo Φᴸ Φᴿ A B limit →
  Φᴸ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ ×
  Φᴿ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ
```

Then `varCandidatesUpTo-sound` is the specialization with
`limit = Δᶜ`.

The induction is on `limit`.  In the `suc n` case, inspect the boolean
candidate test:

```agda
varCandidatesUpTo Φᴸ Φᴿ A B (suc n)
  = varCandidatesUpTo Φᴸ Φᴿ A B n ++ (＇ n ∷ [])
```

If `varCandidate? Φᴸ Φᴿ A B n = false`, recurse on the old list.  If it is
`true`, split membership through the append.  Old-list membership uses the
induction hypothesis; singleton membership gives `C = ＇ n`, and the focused
semantic helper handles the new candidate:

```agda
varCandidate?-sound :
  WfImpCtx² Δᶜ Δᴸ Φᴸ →
  WfImpCtx² Δᶜ Δᴿ Φᴿ →
  varCandidate? Φᴸ Φᴿ A B W ≡ true →
  Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ A ⊣ Δᴸ ×
  Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ B ⊣ Δᴿ
```

`varCandidate?` has three successful shapes:

- `＇ X` / `＇ Y`: require `hasVar W X Φᴸ` and `hasVar W Y Φᴿ`.
- `＇ X` / `★`: require `hasVar W X Φᴸ` and `hasStar W Φᴿ`.
- `★` / `＇ Y`: require `hasStar W Φᴸ` and `hasVar W Y Φᴿ`.

All other type-shape pairs compute to `false`.

Expected helper lemmas:

```agda
andᵇ-true :
  a andᵇ b ≡ true →
  a ≡ true × b ≡ true

hasVar-sound :
  hasVar W X Φ ≡ true →
  (W ˣ⊑ˣ X) ∈ Φ

hasStar-sound :
  hasStar W Φ ≡ true →
  (W ˣ⊑★) ∈ Φ

∈-++-split :
  x ∈ xs ++ ys →
  x ∈ xs ⊎ x ∈ ys
```

Why this is hard: this is the only place where the algorithm turns boolean
context queries into the real `idˣ` and `tagˣ` constructors of
`ImprecisionWf`.

#### 3. Branch membership inversion

Most recursive clauses are list expressions, not constructors.  Prove
specialized inversion lemmas before proving `enumMLB-sound`:

```agda
dedupe-sound :
  C ∈ dedupe xs →
  C ∈ xs

wrapAll-sound :
  C ∈ wrapAll xs →
  ∃[ A ] C ≡ `∀ A × A ∈ xs

wrapAllIfOccurs-sound :
  C ∈ wrapAllIfOccurs xs →
  ∃[ A ] C ≡ `∀ A × occurs zero A ≡ true × A ∈ xs

arrowProducts-sound :
  C ∈ arrowProducts xs ys →
  ∃[ A ] ∃[ B ] C ≡ A ⇒ B × A ∈ xs × B ∈ ys
```

The `wrapAllIfOccurs-sound` lemma is especially important for the `ν` branches,
because its `occurs zero A ≡ true` output becomes the occurrence premise of
`ν`.

Why this is hard: these lemmas are tedious, but they keep the main induction
readable and prevent proof scripts from becoming list-manipulation noise.

## Main `enumMLB-sound` Cases

### `∀`/`∀`

The computed list is:

```agda
dedupe (both ++ leftOnly ++ rightOnly)
```

Use `dedupe-sound`, then split membership through the two appends.

#### `both`

Membership in `wrapAll (...)` gives:

```agda
C = `∀ C₀
C₀ ∈ enumMLB fuel (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B
```

Apply the induction hypothesis under the extended contexts:

```agda
∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ C₀ ⊑ A ⊣ suc Δᴸ
∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ C₀ ⊑ B ⊣ suc Δᴿ
```

Then return:

```agda
∀ⁱ leftProof , ∀ⁱ rightProof
```

Needed context well-formedness lemmas:

```agda
∀ᵢ-wf² :
  WfImpCtx² Δᶜ Δᴸ Φ →
  WfImpCtx² (suc Δᶜ) (suc Δᴸ) (∀ᵢᶜ Φ)
```

This already exists in `proof.ImprecisionProperties` as `∀ᵢ-wf²`, but it is
currently for `((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)`, which is definitionally `∀ᵢᶜ Φ`.

#### `leftOnly`

Membership in `wrapAllIfOccurs (...)` gives:

```agda
C = `∀ C₀
occurs zero C₀ ≡ true
C₀ ∈ enumMLB fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ A (`∀ B)
```

Apply the induction hypothesis:

```agda
∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ C₀ ⊑ A ⊣ suc Δᴸ
νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ C₀ ⊑ `∀ B ⊣ Δᴿ
```

Then return:

```agda
∀ⁱ leftProof , ν occursProof rightProof
```

This case is one of the important ones.  It confirms that the algorithm’s
recursive call against the unchanged right endpoint is exactly the premise
needed by `ν`.

Needed context well-formedness lemma:

```agda
νᵢ-wf²-left :
  WfImpCtx² Δᶜ Δᴿ Φ →
  WfImpCtx² (suc Δᶜ) Δᴿ (νᵢᶜ Φ)
```

There is a close existing lemma, `⇑ᴸᵢ-wf²`, and `νᵢᶜ Φ` is
`(zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ`.  If no exact lemma exists, add it near the simple proof
infrastructure.

#### `rightOnly`

Symmetric to `leftOnly`:

```agda
ν occursProof leftProof , ∀ⁱ rightProof
```

### One-Sided `∀`

For:

```agda
enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B
```

the only branch is `wrapAllIfOccurs` over:

```agda
enumMLB fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
  (suc Δᶜ) (suc Δᴸ) Δᴿ A B
```

Use:

```agda
∀ⁱ leftProof , ν occursProof rightProof
```

The right-sided one-sided `∀` case is symmetric.

### First-Order Base/Star Cases

These are direct:

```agda
★ / ★              -> id★ , id★
base / same base   -> idι , idι
base / ★           -> idι , tag ι
★ / base           -> tag ι , idι
```

The mismatched base case has impossible membership in `[]`.

Hardness: low.

### Arrow Cases

For:

```agda
arrowProducts leftCandidates rightCandidates
```

use `arrowProducts-sound`, then induction on the domain and codomain
memberships.

Return:

```agda
(domainLeft ↦ codomainLeft) , (domainRight ↦ codomainRight)
```

For arrow/star:

```agda
(domainLeft ↦ codomainLeft) ,
tag domainRight ⇛ codomainRight
```

For star/arrow:

```agda
tag domainLeft ⇛ codomainLeft ,
(domainRight ↦ codomainRight)
```

Hardness: low to medium, depending on how clean `arrowProducts-sound` is.

### Variable Cases

Delegate entirely to `varCandidatesUpTo-sound`.

Hardness: high.  Do not inline this proof into `enumMLB-sound`.

### Empty Shape-Mismatch Cases

Every branch returning `[]` closes by impossible membership.

Hardness: low, but avoid catch-all clauses.  Split explicitly according to the
function clauses in `enumMLB`.

## List/Selection Corollaries

After `enumMLB-sound`, prove:

```agda
rawEndpointMlbsAt-sound :
  C ∈ rawEndpointMlbsAt Δ A B →
  idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ ×
  idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ
```

Then:

```agda
allEndpointMlbsAt-sound :
  C ∈ allEndpointMlbsAt Δ A B →
  idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ ×
  idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ
```

This only needs:

```agda
pruneStrictlyBelow-sound :
  C ∈ pruneStrictlyBelow Δ xs →
  C ∈ xs
```

Finally:

```agda
MLB-sound :
  MLB Δ A B ≡ just C →
  idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ ×
  idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ
```

This only needs:

```agda
first-sound :
  first xs ≡ just C →
  C ∈ xs
```

## Recommended Work Order

1. Add a new module `proof.EndpointCanonicalMLBSimpleSoundness`.
2. Prove list plumbing:
   `∈-++-split`, `dedupe-sound`, `wrapAll-sound`,
   `wrapAllIfOccurs-sound`, `arrowProducts-sound`,
   `pruneStrictlyBelow-sound`, `first-sound`.
3. Prove boolean lookup plumbing:
   `==ᵇ-true`, `hasVar-sound`, `hasStar-sound`.
4. Prove context extension well-formedness for `νᵢᶜ` if the exact lemma is
   missing.
5. Prove `varCandidatesUpTo-sound`.
6. Prove `enumMLB-sound`.
7. Prove the raw/pruned/selected endpoint corollaries.
8. Add one or two `EndpointCanonicalMLBSimpleTest` proof witnesses using the
   final selected soundness theorem directly.

## What Not To Prove Yet

Do not try to prove maximality, failure completeness, or coherence in this
phase.

Also do not try to prove that `endpointCtx A B` is the least well-formed
context for `A` and `B`.  Soundness for `simpleEndpointMlb` can initially be
stated with an explicit `Δ` via `MLB`.  The endpoint-only
`simpleEndpointMlb` corollary can be delayed until there are `typeCtxBound`
well-formedness lemmas.

## Main Risks

- **Variable candidates:** this is the hardest local proof because it must
  recover both context-membership assumptions and the finite bound `W < Δᶜ`.
- **`νᵢᶜ` context well-formedness:** the existing library has closely related
  lifting lemmas, but the exact indexed shape may need a small wrapper.
- **List inversion noise:** without specialized list lemmas, the main proof will
  become unreadable.  Keep list reasoning out of `enumMLB-sound`.
- **Fuel:** soundness does not require proving the fuel is sufficient.  The
  zero-fuel branch returns `[]`, so it is trivially sound.  Do not spend effort
  on fuel completeness during this proof.
