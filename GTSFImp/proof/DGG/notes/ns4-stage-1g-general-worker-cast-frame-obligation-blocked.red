NS-4 stage 1g blocker: general value-spine worker lacks target-frame
intermediate obligations

Date: 2026-08-14

Surface:

  The requested general worker is value-anchored:

    rel : W ∣ γ ⊢² M ⊑ V ∶ p₀
    p₀  : A ⊑ᵂ⟨ W ⟩ C₀
    spine : InstantiationSpine C₀ E
    q : A ⊑ᵂ⟨ W ⟩ E

  This is the right negative control against the refuted statement: the
  premise is not

    W ∣ γ ⊢² M ⊑ applyInstantiationSpine V spine ∶ q

  and the relation remains anchored at the target value `V`.

Blocked branch:

  The standalone general worker must cover an arbitrary cast frame:

    spine = cast-frame c ▻ⁱ tail
    c : μ ⊢ C₀ ∼ C₁
    tail : InstantiationSpine C₁ E

  The caller supplies only

    rel : W ∣ γ ⊢² M ⊑ V ∶ p₀
    p₀  : A ⊑ᵂ⟨ W ⟩ C₀
    q   : A ⊑ᵂ⟨ W ⟩ E

  To consume the `cast-frame`, both advertised paths require an intermediate
  target-frame imprecision witness:

  1. inert/absorbed value path:

       child value: V ⟨ c ⟩
       child spine: tail

     The recursive child relation would need

       W ∣ γ ⊢² M ⊑ V ⟨ c ⟩ ∶ p₁
       p₁ : A ⊑ᵂ⟨ W ⟩ C₁

     Rebuilding that relation with `CTI2.⊑cast² c rel p₁` also requires
     exactly the same `p₁`.

  2. safe-inst / gen path:

       child value/spine: the proven strict child produced by the
       target beta step and the primary mass descent

     The recursive child still lands at the post-frame target type and needs
     the same intermediate endpoint before the tail can be processed.

  Neither `StructuralNamePostPlan W A E q` nor the final witness
  `q : A ⊑ᵂ⟨ W ⟩ E` determines such a `p₁ : A ⊑ᵂ⟨ W ⟩ C₁`.
  This is the same shape as the resolved source-wrapper problem, but on the
  target frame side: the hereditary plan gives premise obligations for source
  wrappers, not target-frame intermediate obligations.

Why the proved ingredients do not close this branch:

  * `cast-frame-rank-decreases` proves the secondary measure descent for the
    inert value child.  It does not produce the relation
    `W ∣ γ ⊢² M ⊑ V ⟨ c ⟩ ∶ p₁`.

  * `inst-primary-decreases` and `gen-primary-decreases` prove the primary
    cast-mass descent for safe-inst/gen children.  They do not produce the
    child endpoint imprecision witness.

  * `StructuralFrameOutcome` classifies target reveal/conceal administration
    as value-or-one-step.  It is a target reduction/value result, not an
    imprecision endpoint generator.

  * `value-type-app-source-view` cannot be applied to the value-anchored
    premise.  Its premise is already a relation to a raw target type
    application.  Using it as the general worker premise would recreate the
    refuted raw-spine shape.

Concrete square:

  The missing cast-frame step is:

    M        ⊑        V        : A ⊑ C₀
    |                 |
    | 0 steps         | cast frame c : C₀ ∼ C₁
    v                 v
    M        ⊑        V⟨c⟩    : A ⊑ C₁   (missing)

  The overall target trace then continues through `tail`:

    V⟨c⟩  --tail*-->  final

  The final endpoint `A ⊑ E` is too late to type the recursive call at
  `V⟨c⟩`; the worker needs the post-frame endpoint `A ⊑ C₁`.

Consequence:

  The requested general structural-spine worker statement is still too weak
  for arbitrary target frames, even while keeping the relation correctly
  anchored at the value.  A live implementation would need an additional
  target-frame post-plan/provenance layer that supplies the intermediate
  obligations for `cast-frame`, `reveal-frame`, `conceal-frame`, and any
  generated frames introduced by the strict peels.

Live code status:

  No frozen files were edited.  No postulates, holes, catch-alls, or weakened
  statements were added.  The stage 1g statement scratch and generalized
  skeleton chunks remain the only committed code changes before this blocker.


RESOLVED postscript, 2026-08-14:

  The missing target-frame intermediate endpoint is now supplied by
  `TargetFrameAbsorptionChain` in
  `GTSFImp/proof/DGG/Catchup/StructuralTargetFrameAbsorptionDef.agda`.
  In particular, `tfa-cast` stores the post-cast endpoint and
  `target-frame-cast-absorption` turns a value-anchored relation into the
  relation needed for the cast-frame child.

  The reveal/conceal analogues were subsequently strengthened in stage 1m
  with supplied premise-relation transport fields, matching the rebased
  premises required by `⊑reveal²` and `⊑conceal²`.
