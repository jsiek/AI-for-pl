# T2 D2a proposal: source cast layer target-wrapper cases

Date: 2026-08-17

Status: proposal required by D2a stop condition.

`proof.DGG.SimCastLayerInversion` now exports the routine CTI2 head analysis
that D2a permits.  The two ordinary source-cast heads are direct:

```agda
source-cast-layer-head-analysis (CTI2.cast⊑cast² c c′ rel q) =
  paired-source-cast-layer _ rel
source-cast-layer-head-analysis (CTI2.cast⊑² c rel q) =
  source-cast-layer _ rel
```

The same head split exposes three target-wrapper heads:

```agda
source-cast-layer-head-analysis (CTI2.⊑cast² c′ rel q) =
  target-cast-layer-blocked _ rel
source-cast-layer-head-analysis (CTI2.⊑reveal² mono rb sc c′⊢ rel q) =
  target-reveal-layer-blocked mono rb sc c′⊢ _ rel
source-cast-layer-head-analysis (CTI2.⊑conceal² mono rb sc c′⊢ rel q) =
  target-conceal-layer-blocked mono rb sc c′⊢ _ rel
```

These are not impossible by CTI2 head analysis: an arbitrary target value
returned by catchup may itself be a target cast, reveal, or conceal value.  To
turn these views into the source tag-untag peel, a proof must descend through
the target wrapper and then rebuild it around the peeled source core.

For the target cast case the required square is:

$$
\begin{array}{ccc}
V \langle c \rangle & \sqsubseteq & V' \\
\downarrow^{0} & & \downarrow^{0} \\
V \langle c \rangle & \sqsubseteq & V'
\end{array}
\qquad
\text{under } \sqsubseteq\text{ lifted by } \_\langle c' \rangle
$$

The recursive premise has type `B ⊑ᵂ⟨ W ⟩ C′`, but the peeled source core needs
an intermediate witness `A ⊑ᵂ⟨ W ⟩ C′` before `⊑cast² c′` can rebuild the
original target endpoint at `A ⊑ᵂ⟨ W ⟩ C`.  That intermediate witness is a
target-cast inversion/replay obligation, not a one-step source-cast head
inversion.

The reveal and conceal cases are analogous, except the rebuild also threads
`ImpEnvMono`, `RebaseAtᴿ`, `SameCtx`, and the target conversion typing
evidence.  Closing them would require a value-indexed source-cast peel through
target wrappers, or an existing target-wrapper transport surface with exactly
these intermediate witnesses.

Per RULING D2a, this piece should not be completed by silently adding a full
`⊢²` induction.  Proposed next sanctioned statement:

```agda
SourceValueCastLayerPeelᵀ : Set₁
SourceValueCastLayerPeelᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V : Term Δᴸ} {V′ : Term Δᴿ}
    {A B : Ty Δᴸ} {C : Ty Δᴿ}
    {ν : Env∼ Δᴸ} {c : ν ⊢ A ∼ B}
    {q : B ⊑ᵂ⟨ W ⟩ C}
  → Value V′
  → W ∣ γ ⊢² V ⟨ c ⟩ ⊑ V′ ∶ q
  → Σ[ p ∈ A ⊑ᵂ⟨ W ⟩ C ] W ∣ γ ⊢² V ⊑ V′ ∶ p
```

This is intentionally marked as a proposal because it is no longer routine
constructor-head analysis: the target-wrapper rows need additional
intermediate-witness machinery.
