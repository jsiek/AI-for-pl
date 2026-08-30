# The fused design: reveal *is* the region

**Proposal (2026-08-30).** Fuse ν into reveal. The reveal binds the type
variable *and* stores the representation type; anchors, the anchor context
Θ, and ν itself are deleted. Conceal names the bound variable of its
binding reveal and remains an anti-binder. This is the v1 architecture
(rep at the crossing) made viable by three later inventions: open
birth-scope term contexts (U50), public-on-exit escape (U44), and the
immobile/SCWRAP treatment of boundaries (U46/U50).

## Syntax

```agda
Term : TyCtx → Set                       -- one index; Θ is gone

M ↑[⦂= R ] c      -- reveal: binds ZERO (innermost; interior at suc Δ),
                  --         stores R : Ty Δ, conversion c : Reveal
M ↓[ X ] c        -- conceal: anti-binds live X : TyVar (suc Δ), ARBITRARY
                  --          position; node at suc Δ, pocket at Δ
```

No other term changes. The binder is the region's identity: a conceal can
only reference an X that is in scope, hence sits inside the unique reveal
that binds it — tight scoping does the work anchors were invented for.

**Asymmetric positions (2026-08-30).** Reveals always bind zero: regions
OPEN innermost (β-Λ converts the Λ-binder, which is zero, in place), so
begins are plain cons — no insertᵛ, and the begin side of ScopeRoute is
canonical. Conceals stay positional: regions provably CLOSE out of order
(the U57 interleaving trace ends Y under live X), so the end-side
punchOut is forced by a checked reachable trace. The one candidate payer
for nonzero reveals is an eager SCTYWRAP (crossing past a Λ), whose
contractum with zero-only binding needs a 0↔1 exchange rename of the
interior; the prototype's leading audit decides whether that rule family
is needed at all (the lazy β-reveal-∀ consumer may cover it), and if it
is, pays the rename rather than reintroducing positional begins.

## Telescope

```agda
data TyEnv : TyCtx → Set where
  ∅        : TyEnv 0
  _,typ    : TyEnv Δ → TyEnv (suc Δ)                        -- Λ-bound
  _,begin[⦂=_]  : TyEnv Δ → Ty Δ → TyEnv (suc Δ)   -- always binds zero
  _,end[_] : TyEnv (suc Δ) → (X : TyVar (suc Δ)) → TyEnv Δ
```

- σ, `∉ᵛ` freshness, `∈acc`/`∈seg`, and the evidence field are all GONE:
  each begin binds a fresh variable by construction, and "naming a hidden
  region" is unrepresentable — the pocket's Δ-index cannot mention X.
- `rep Ψ X` is a TOTAL lookup for live region variables (weaken the stored
  R along the entries above its begin). No Maybe, no fuel, no scanRep?/
  repoint?: *live ⇒ rep exists* is structural. Anchor-directed transport
  and its dead-crossing resolution are deleted, not reproved.
- Term contexts stay exactly U50-structural: `TermCtx : TyEnv Δ → Set`,
  entries at birth scope, `⊢`` weakens along the path, conceal premises
  truncate with `Γ ↾end[X]`.

## Typing (the two changed rules; all others as in U50)

```agda
⊢reveal :
    ⊢↑[ zero ⦂ wkᵗ zero R ] c ⦂ A ↝ wkᵗ zero B
  → Ψ ,begin[⦂= R ] ∣ Γ ⊢ M ⦂ A
  → Ψ ∣ Γ ⊢ M ↑[⦂= R ] c ⦂ B
  -- old premises rep? Ψ α ≡ just C and α ∉ᵛ σ: deleted (R is right here;
  -- freshness is binding)

⊢conceal :
    rep Ψ X ≡ R                          -- total lookup at the binder
  → ⊢↓[ X ⦂ wkᵗ X R ] c ⦂ wkᵗ X A ↝ B
  → Ψ ,end[ X ] ∣ Γ ↾end[ X ] ⊢ M ⦂ A
  → Ψ ∣ Γ ⊢ M ↓[ X ] c ⦂ B
```

`⊢ν` is deleted.

## Reduction (key rules, instantiated)

```agda
-- Instantiation opens the region IN PLACE: the Λ-binder becomes the
-- region binder. No ν, no anchor shift (shiftᶿ is gone).
β-Λ :  Value V
  →  (Λ V) ⦂∀ B [ C ]  —→  V ↑[⦂= C ] 〖 zero ↑ B 〗
  -- the Λ-binder (zero) becomes the region binder in place

-- Reveal-polarity SCWRAP, verbatim from U50 minus the anchor:
SCWRAP :  outsideDomain? … ≡ just A′
  →  (ƛ A ˙ N) ↑[⦂= R ] (c ↦↑ d)
       —→  ƛ A′ ˙ ((N [ x := (` x) ↓[ zero ] c ]) ↑[⦂= R ] d)

-- Matched cancellation happens AT the binding reveal — the sandwich
-- problem has no home (there is no ν between conceal and reveal):
cancel :  Value V
  →  (V ↓[ zero ] id↓) ↑[⦂= R ] id↑  —→  V

-- Escape stays public-on-exit, with R read off the node:
escape :  Result V
  →  (V ⟨ ＇zero ! ⟩) ↑[⦂= R ] id↑
       —→  (V ↑[⦂= R ] unseal) ⟨ inj★ R ⟩

-- Design-I commutes (inject-conceal unconditional; inject-reveal
-- strengthen-guarded + resolve variant using the node's R), the
-- ★-projection family, blame propagation, the lazy NonLambda
-- fun-boundary consumers, and stratified inj★: all carried over with
-- `≔ α` deleted from the node data.
```

The ν-dissolution family (`const-ν`, `blame-ν`, `tag-out`,
`inert-cast-out`, `NUWRAP`, `NUTYWRAP`) is deleted whole: reveals are
immobile w.r.t. eliminations, and the SCWRAP family plus cancellation do
all the moving that dissolution did.

## Problems that die by unrepresentability

- **The gc sandwich** `ν β [E] (W ↓[X≔α] c)` — no ν exists. ν-gc,
  ν-push-conceal, CUν, unshiftᶿ?: deleted.
- **U49 pocket-strengthens counterexample** — a pocket crossing at the
  young region needs its variable, which the pocket's Δ-index lacks.
  pocket-strengthens IS the indexing.
- **U55/U56 accessibility** — ∈acc, ∈seg, markAccessible, the begin
  evidence field: never exist. The reachable interleaving trace
  (RegionInterleavingReachable) stays representable and boring: the
  Y-conceal under X's reveal anti-binds a non-innermost variable
  (punchOut), which the conceal already does.
- **Anchor reopening, dead-crossing resolution, fuel** — unstatable.

## Acceptance tests for the prototype

1. Re-run the interleaving trace end-to-end (fused β-Λ, SCWRAP, NUWRAP's
   role absorbed — the trace shortens).
2. Re-run the U44 escape trace (`7 ⟨ℕ!⟩` public exit, `？ℕ` projection).
3. Checked unrepresentability notes for the U49 and sandwich shapes.
4. Ladder items 1 (loose cancel) and 7 (resolving float) re-verified.
5. preserve/progress skeletons with holes per the no-scaffolding policy.

## Open questions (flagged, not hidden)

1. **Region-outlives-crossing states**: the fused design cannot express a
   region without its reveal. The only known such state was typed-only
   (the stranded sandwich). If some reachable state needs one, fusion is
   refuted — the prototype should hunt adversarially (U57 discipline).
2. **Truncation under interleaving** (`Γ ↾end[Y]` dropping live-X-era
   entries) and the refuted-as-stated `⊢reenter`: inherited from U50
   unchanged, neither created nor solved by fusion.
3. **Generativity**: each β-Λ redex mints its own reveal, so distinct
   instantiations of one Λ remain distinct regions — preserved, but the
   inversion-theorem statement must be recast with the binder, not the
   anchor, as the region's identity.
