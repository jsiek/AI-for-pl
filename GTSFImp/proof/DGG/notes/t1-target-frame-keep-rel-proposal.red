T1 target-frame keep relation proposal

Status: proposal only.  Do not implement without approval.

The D1 ruling has been applied to the structural target reveal/conceal row
surfaces: keep outcomes now receive the checked wrapper relation at the
post-child world before delegating to the caller.

The structural value dispatcher still cannot be total for the plain
`⊑reveal²` and `⊑conceal²` branches.  Those CTI constructors carry a child
relation for the wrapped target term, but not the reduct relation needed after
an administrative target keep step.  The instantiation-spine route has this as
`TargetFrameAbsorptionChain.keep-rel`; the standalone value worker has no
corresponding surface.

Proposed relation-level statements:

```agda
target-reveal-keep-rel : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N N₁ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↑ Δᴿ B B′}
  → Value N
  → W ∣ γ ⊢² M ⊑ N ↑ c′ ∶ q
  → (N ↑ c′) —→[ keep ] N₁
  → Value N₁
  → W ∣ γ ⊢² M ⊑ N₁ ∶ q

target-conceal-keep-rel : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N N₁ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↓ Δᴿ B B′}
  → Value N
  → W ∣ γ ⊢² M ⊑ N ↓ c′ ∶ q
  → (N ↓ c′) —→[ keep ] N₁
  → Value N₁
  → W ∣ γ ⊢² M ⊑ N₁ ∶ q
```

These are major lemmas: they require inversion or induction over `⊢²`, because
the reveal `conceal-reveal` reduct must recover the relation to the concealed
payload from the relation to the sealed target value.  They should either be
approved directly, or replaced by an approved continuation-stack surface for
the value dispatcher that carries the same `keep-rel` information hereditarily.
