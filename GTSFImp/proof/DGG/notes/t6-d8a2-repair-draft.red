T6 D8a2 repair draft
=====================

Context
-------

The checked probe
`proof/DGG/notes/probes/T6D8a2ClosedValueRebaseTransportProbe.agda`
uses a T10-style moving-source-pivot world:

* `W` aligns source pivot `X` with old target pivot `Y-old`.
* `Wᵖ` rebases source pivot `X` to fresh target pivot `Y-fresh`.
* The source and target store representations are concrete `ℕ`
  representations, so the entangled pair can use sealed constant values.

Verdict
-------

| form | rebase-unrelated constants at `ℕ` | rebase-entangled sealed values at the old pivot |
| --- | --- | --- |
| `RebaseAtᴸ W Wᵖ (just X)` | PROVEN by `unrelated-RebaseAtᴸ-verdict` | REFUTED at the exact boundary endpoint by `entangled-RebaseAtᴸ-transport-refuted` |
| `RebaseAtᴿ W Wᵖ (just Y-fresh)` | PROVEN by `unrelated-RebaseAtᴿ-verdict` | REFUTED at the exact boundary endpoint by `entangled-RebaseAtᴿ-transport-refuted` |
| `TagRebaseAtᴸ W Wᵖ (just X) (just Y-fresh)` | PROVEN by `unrelated-TagRebaseAtᴸ-verdict` | REFUTED at the exact boundary endpoint by `entangled-TagRebaseAtᴸ-transport-refuted` |

The refuted endpoint is:

```agda
Σ[ p′ ∈ (＇ X) CTI2.⊑ᵂ⟨ Wᵖ ⟩ (＇ Y-old) ]
  EntangledAtWᵖExact p′
```

and the checked emptiness is driven by:

```agda
pivot-old-at-Wᵖ-empty : (＇ X) CTI2.⊑ᵂ⟨ Wᵖ ⟩ (＇ Y-old) → ⊥
pivot-old-at-Wᵖ-empty ()
```

So the pure "reuse the image relation at the rebased premise world" plan is
not sound for values whose relation witness is tied to the rebased pivot's
old boundary endpoint.  The repair should not try to synthesize every image
relation by rebase transport.  Instead, the substitution hypothesis must carry
supplied image evidence at each boundary-stack-reachable premise world.

Before
------

The direct D8a surface supplies image relations only at the initial world and
image context:

```agda
record TermSubstRelDirect {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ)
    (γ δ : CtxImp W)
    (σᴸ : Subst Δᴸ)
    (σᴿ : Subst Δᴿ) : Set where
  field
    lookup : ∀ {x A B} {p : A ⊑ᵂ⟨ W ⟩ B}
      → γ ∋ʷ x ⦂ ctx-imp A B p
      → W ∣ δ ⊢² σᴸ x ⊑ σᴿ x ∶ p


⊢²-term-subst-directᵀ : Set
⊢²-term-subst-directᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {γ δ : CtxImp W}
    {σᴸ : Subst Δᴸ} {σᴿ : Subst Δᴿ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → TermSubstRelDirect W γ δ σᴸ σᴿ
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W ∣ δ ⊢² subst σᴸ M ⊑ subst σᴿ M′ ∶ p
```

After
-----

The repair surface makes the substitution relation boundary-indexed.  It is
supplied-hereditary: for every boundary-stack-reachable world and matching
source/image contexts, the hypothesis directly supplies the image relation at
that node's own witness `p`.

```agda
record BoundaryNode {Δᴸ Δᴿ Δ} : Set₁ where
  constructor boundary-node
  field
    world : World Δᴸ Δᴿ Δ
    source-ctx : CtxImp world
    image-ctx : CtxImp world

open BoundaryNode public


data BoundaryStackReachable {Δᴸ Δᴿ Δ}
    (root : BoundaryNode {Δᴸ} {Δᴿ} {Δ}) :
    BoundaryNode {Δᴸ} {Δᴿ} {Δ} → Set₁ where
  reachable-root :
      ---------------------------------
      BoundaryStackReachable root root

  reachable-boundary : ∀ {node node′ kind Xᴸ? Xᴿ?}
    → BoundaryStackReachable root node
    → CatchupBoundary kind Xᴸ? Xᴿ?
        (world node) (world node′)
    → SameCtx (source-ctx node) (source-ctx node′)
    → SameCtx (image-ctx node) (image-ctx node′)
      ---------------------------------------------
    → BoundaryStackReachable root node′


record TermSubstRelBoundary {Δᴸ Δᴿ Δ}
    (root : BoundaryNode {Δᴸ} {Δᴿ} {Δ})
    (σᴸ : Subst Δᴸ)
    (σᴿ : Subst Δᴿ) : Set₁ where
  field
    lookup :
      ∀ {node : BoundaryNode {Δᴸ} {Δᴿ} {Δ}}
      → BoundaryStackReachable root node
      → ∀ {x A B} {p : A ⊑ᵂ⟨ world node ⟩ B}
      → source-ctx node ∋ʷ x ⦂ ctx-imp A B p
      → world node ∣ image-ctx node ⊢² σᴸ x ⊑ σᴿ x ∶ p


⊢²-term-subst-boundaryᵀ : Set₁
⊢²-term-subst-boundaryᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {γ δ : CtxImp W}
    {σᴸ : Subst Δᴸ} {σᴿ : Subst Δᴿ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → TermSubstRelBoundary (boundary-node W γ δ) σᴸ σᴿ
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W ∣ δ ⊢² subst σᴸ M ⊑ subst σᴿ M′ ∶ p
```

Implementation consequence
--------------------------

Wrapper cases should extend the active boundary stack and call the induction
hypothesis with the same `TermSubstRelBoundary`, not with a transported direct
lookup relation.  Variable cases obtain exactly the image relation for the
current boundary node from `TermSubstRelBoundary.lookup`.
