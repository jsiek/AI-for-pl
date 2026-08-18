Source-only ∀ β-closing blocker proposal
========================================

Blocked interface:

`SimSourceAllClosingᵀ`

Reason:

`SimSourceAllClosingᵀ` is the top-down source-only type-application square.  The
target side is an arbitrary term, not a matching target type application.  The
existing M5 source-Λ replay lemmas rebuild source-only `Λ⊑²` relations after a
target normalization trace, and the instantiation packages handle target
instantiation spines, but no current surface consumes a source `β-Λ`/`β-∀`/
`β-gen`/`β-reveal-∀`/`β-conceal-∀` redex and returns the instantiated source
body relation in the exact `SimSourceAllClosingᵀ` output shape.

That missing adapter is a new DGG top-level proof shape over source-only
opening/name-instantiation, so the t6 standing rule says to record the statement
instead of implementing it here.

Before context
--------------

`SimProof.agda` calls the interface at source-only type-application root steps:

```
sim parked (•⊑² p∀ M⊑M′ q r) (β-Λ vM) =
  sim-source-all-closing parked M⊑M′ q r (Λ vM) (β-Λ vM)
```

and similarly for `β-∀`, `β-gen`, `β-reveal-∀`, and `β-conceal-∀`.

The fixed interface starts with:

```
world ∣ [] ⊢² V ⊑ M′ ∶ p∀
Value V
V ⦂∀ C [ A ] —→[ χᴸ ] N
```

and must return target steps from `M′` itself, not from `M′ ⦂∀ ...`:

```
M′ —↠[ χsᴿ ] N′
```

Existing relevant pieces:

* `ValueCatchupRightAt fuel` can normalize `M′` to a target value after a
  `TargetCastBound fuel M⊑M′` proof.
* `structural-Λ-replay` and `structural-smart-Λ-replay` replay `Λ⊑²` and
  `Λ⊑²-smart-comma` after target-only world extension.
* `InstInversionLambdaProof.agda` contains source-only prefix/rewrap machinery
  used by M5 target-instantiation proofs, but it is oriented around generated
  target instantiation casts and does not expose the source-only Sim square.

Proposed statements
-------------------

First reuse the shared M6 closure proposed in
`t6-fun-substitution-proposal.red`:

```
⊢²-target-cast-bound :
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
  → Σ[ fuel ∈ ℕ ] TargetCastBound fuel rel

value-catchup-right² :
  ValueCatchupRight²
```

Then add the source-only value-redex core.  This is the proof after target
catchup has exposed the target value endpoint:

```
SourceAllValueRedexClosingᵀ : Set₁
SourceAllValueRedexClosingᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴸ′} {world : World Δᴸ Δᴿ Δ}
    {χᴸ : StoreChange Δᴸ Δᴸ′}
    {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term Δᴸ′}
    {C : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p∀ : `∀ C ⊑ᵂ⟨ world ⟩ B}
  → ParkedWorld world
  → world ∣ [] ⊢² V ⊑ V′ ∶ p∀
  → (q : A ⊑ᵂ⟨ world ⟩ ★)
  → (r : C [ A ]ᵗ ⊑ᵂ⟨ world ⟩ B)
  → Value V
  → Value V′
  → V ⦂∀ C [ A ] —→[ χᴸ ] N
  → Σ[ Δ′ ∈ TyCtx ] Σ[ world′ ∈ World Δᴸ′ Δᴿ Δ′ ]
    Σ[ s ∈ applyTy χᴸ (C [ A ]ᵗ) ⊑ᵂ⟨ world′ ⟩ B ]
      ParkedEvolve (χᴸ ∷ˢ []ˢ) []ˢ world world′ ×
      (world′ ∣ [] ⊢² N ⊑ V′ ∶ s)
```

Finally assemble the fixed interface by prepending target value catchup:

```
sim-source-all-closing-from-value-redex :
  value-catchup-right²
  → SourceAllValueRedexClosingᵀ
  → SimSourceAllClosingᵀ
```

The source-only value-redex core is expected to dispatch over the source step
and the source-side CTI2 relation shape:

* direct `Λ⊑²` and `Λ⊑²-smart-comma` rows perform source-left opening from the
  premise world to the source-bind world and use `r` as the opened type
  imprecision endpoint;
* source cast/reveal/conceal rows thread the wrapper step and reuse the existing
  replay/rewrap machinery;
* the `Λ⊑Λ²` row is handled through the existing source-only prefix machinery
  when the target universal endpoint is already a target value.

After context
-------------

Once these surfaces exist, `SimSourceAllClosingProof.agda` should be a thin
adapter:

```
sim-source-all-closing parked rel q r vV step =
  -- choose fuel and catch up M′ to a target value V′
  -- call SourceAllValueRedexClosingᵀ on V′
  -- prepend the target catchup trace and compose ParkedEvolve
```

This keeps the fixed `SimSourceAllClosingᵀ` statement unchanged while isolating
the source-only opening proof that is missing from the current M5/M6 frontier.
