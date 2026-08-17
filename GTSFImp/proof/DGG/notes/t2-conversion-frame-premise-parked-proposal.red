# T2 proposal: parked premise worlds for continuation-shaped conversion frames

Date: 2026-08-17

Status: proposed; no live proof surface changed.

The D1 continuation-shaped `SimConversionFramesᵀ` ruling requires `SimProof`
to perform the child recursive simulation call before invoking the frame field.
At every reveal/conceal wrapper constructor, the child relation lives at the
constructor premise world, not at the outer world whose `ParkedWorld` proof is
available to `Simᵀ`.

Focused diagnostic
------------------

A temporary compile experiment in the target-reveal branch tried to call:

```agda
sim parked M⊑M′ M→N
```

under:

```agda
rel@(⊑reveal² mono rebase same c′⊢ M⊑M′ q)
```

Agda reported:

```text
W′ != W of type (World Δᴸ Δᴿ Δ)
when checking that the expression M⊑M′ has type
W ∣ List.[] ⊢² _M_2332 ⊑ _M′_2333 ∶ _p_2337
```

The same premise-world mismatch appears in the source reveal/conceal and
target conceal frame cases.  Passing `parked` to the child call is therefore
ill-typed, and the current parked toolkit exports no lemma that turns
`ParkedWorld W` into `ParkedWorld Wᵖ` through these rebase witnesses.

Required new statement
----------------------

One way to make the D1 shape implementable is to add an explicit parked-premise
capability for wrapper premise worlds:

```agda
ParkedConversionPremisesᵀ : Set₁
ParkedConversionPremisesᵀ =
  (∀ {Δᴸ Δᴿ Δ} {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ?}
    → ParkedWorld W
    → CTI2.RebaseAtᴸ W Wᵖ Xᴸ?
    → ParkedWorld Wᵖ)
  ×
  (∀ {Δᴸ Δᴿ Δ} {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴿ?}
    → ParkedWorld W
    → CTI2.RebaseAtᴿ W Wᵖ Xᴿ?
    → ParkedWorld Wᵖ)
  ×
  (∀ {Δᴸ Δᴿ Δ} {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
    → ParkedWorld W
    → CTI2.TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?
    → ParkedWorld Wᵖ)
  ×
  (∀ {Δᴸ Δᴿ Δ} {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
    → ParkedWorld W
    → CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
    → ParkedWorld Wᵖ)
```

With such a capability, `SimProof` could call the structural child simulation
at the premise world and then pass the resulting Sigma package to the
continuation-shaped frame fields.

This is a new major proof surface: it changes how parkedness is propagated
through wrapper rebasing, and the current `ParkedWorld` constructors do not make
the statement derivable directly.  Per the T2 standing rule, I did not add this
surface or reshape the live frame interface past the approved design point.
