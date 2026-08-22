T1 direct target-frame certificate proposal
===========================================

Status: proposal only.  Do not implement without approval.

The T12 approved `RestatedDispatcherKeepOutcomesᵀ` family has been added to
`proof/DGG/Catchup/StructuralCatchupRightDef.agda`.  Its fields cover the
evidence-forced synchronized rows:

- paired source/target `conceal-reveal`;
- source `conceal-reveal` when the target was already opened by a supplied
  target `conceal-reveal` step;
- paired source/target `id-conceal`;
- source `id-conceal` when the target endpoint is already open.

That replacement is enough for callers that have destructed a matching source
wrapper or matched package.  It is not enough for the plain target-only CTI
constructors in the value dispatcher:

```agda
CTI2.⊑reveal²  mono rb sc c′⊢ rel q
CTI2.⊑conceal² mono rb sc c′⊢ rel q
```

After the child catch-up, `StructuralFrameOutcome` can expose target
administrative keep steps:

```agda
(N′ ↑ c′) —→[ keep ] N₁
(N′ ↓ c′) —→[ keep ] N₁
```

The checked row transformers already pass the post-child frame relation to the
caller-supplied keep continuation:

```agda
Wᵒ ∣ mapCtxᴿ plan γ ⊢² M ⊑ N′ ↑ applyReveals χs c′ ∶ qᵒ
Wᵒ ∣ mapCtxᴿ plan γ ⊢² M ⊑ N′ ↓ applyConceals χs c′ ∶ qᵒ
```

However, the T12 fields do not apply to a plain source value `M`.  For example,
the target reveal `conceal-reveal` case has this square:

$$
\begin{array}{ccc}
M & \sqsubseteq & (V' \downarrow \mathsf{seal}\ X'\ R')
                    \uparrow \mathsf{unseal}\ X'\ R' \\
\downarrow^{0} & & \downarrow^{1} \\
M & \sqsubseteq & V'
\end{array}
$$

The approved paired peel requires the left side of the top row to be the
matching wrapper:

```agda
((V ↓ seal X R) ↑ unseal X R)
```

The approved source-only peel also requires that same source wrapper, plus
supplied evidence that the target endpoint was already opened.  Neither field
has a premise whose source term is the plain value `M`.

The target conceal `id-conceal` case has the analogous plain target-only square:

$$
\begin{array}{ccc}
M & \sqsubseteq & V' \downarrow \mathsf{id} \\
\downarrow^{0} & & \downarrow^{1} \\
M & \sqsubseteq & V'
\end{array}
$$

Again, the approved fields require either a paired source `id-conceal` wrapper
or a source-opened `id-conceal` wrapper.  They do not supply the relation for a
plain source value.

Proposed evidence-supplied surface
----------------------------------

Do not reintroduce a derived broad keep-rel lemma.  Instead, add a small
certificate that is supplied by whatever caller has enough local evidence to
know the plain target-only keep is valid:

```agda
record DirectTargetRevealKeepCertificateᵀ : Set₁ where
  field
    reveal-certificate :
      ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {M N N₁ : Term Δᴿ}
        {P : Term Δᴸ}
        {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
        {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↑ Δᴿ B B′}
      → Value P
      → Value N
      → W ∣ γ ⊢² P ⊑ N ↑ c′ ∶ q
      → (N ↑ c′) —→[ keep ] N₁
      → Value N₁
      → W ∣ γ ⊢² P ⊑ N₁ ∶ q
```

and similarly for direct target conceal:

```agda
record DirectTargetConcealKeepCertificateᵀ : Set₁ where
  field
    conceal-certificate :
      ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {M N N₁ : Term Δᴿ}
        {P : Term Δᴸ}
        {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
        {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↓ Δᴿ B B′}
      → Value P
      → Value N
      → W ∣ γ ⊢² P ⊑ N ↓ c′ ∶ q
      → (N ↓ c′) —→[ keep ] N₁
      → Value N₁
      → W ∣ γ ⊢² P ⊑ N₁ ∶ q
```

These statements are still major surfaces because they generalize beyond the
T12 synchronized wrapper rulings.  They should be approved explicitly, or
replaced by a narrower CTI inversion theorem proving that the plain target-only
keep cases are unreachable or always reduce to one of the approved T12
synchronized cases.

Until one of those approved surfaces exists, the total
`StructuralValueCatchupRightAt` dispatcher cannot be assembled without a hole,
postulate, pragma, or a resurrection of the refuted broad keep-rel lemma.
