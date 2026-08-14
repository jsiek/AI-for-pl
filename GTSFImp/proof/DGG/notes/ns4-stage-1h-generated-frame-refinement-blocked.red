NS-4 stage 1h generated-frame refinement blocker
================================================

Status
------

Stage 1h landed the target-frame absorption chain surface:

- `GTSFImp/proof/DGG/notes/NS4Stage1hTargetFrameAbsorptionScratch.agda`
  checks the constructor-shape calibration cells C1-C4.
- `GTSFImp/proof/DGG/Catchup/StructuralTargetFrameAbsorptionDef.agda`
  is wired into `All.agda`.

This closes the stage-1g negative control for an existing target cast frame:
the final tail witness `q : A ⊑ᵂ⟨ W ⟩ E` is not enough, and the chain entry
supplies the missing intermediate witness
`qC : A ⊑ᵂ⟨ W ⟩ C`, which feeds `⊑cast²`.

The strict generated-frame refinements are not yet derivable from the current
live peel outputs.  Do not add the generated-frame witnesses as another worker
input; the missing object is a reusable generated-target-frame geometry record.


Missing witness: `allv-∀`
------------------------

After peeling

`(V ⟨ ∀ᶜ d ⟩) ⦂∀ B [ ＇ X ]`

the child spine contains

`name-type-app-frame A X refl refl ▻ⁱ cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ ...`

The generated cast-frame chain entry needs the opened post-cast endpoint

`qCast : Aₛ ⊑ᵂ⟨ W ⟩ C [ ＇ X ]ᵗ`

for `d : extᵐ μ ⊢ B ∼ C`.

The current target peel returns the smaller target package but no relation
inversion witness that turns the parent target-cast endpoint into this opened
endpoint for arbitrary source value `M`.


Missing witnesses: `allv-reveal` and `allv-conceal`
---------------------------------------------------

After peeling `allv-reveal`, the child spine contains

`name-type-app-frame (applyBody (bind (＇ X)) C) zero refl refl`

then

`type-transport-frame (applyBody-open-zero C)`

then the two generated target conversion frames

`reveal-frame c`

and

`reveal-frame (〖 zero , ⇑ᵗ (＇ X) ↑ B 〗)`.

For the first generated frame, the chain entry requires the full target
absorption premise package in the inserted world `W₁`:

`ImpEnvMono W₁ Wᵖ₁`

`RebaseAtᴿ W₁ Wᵖ₁ X₁?`

`SameCtx γ₁ γᵖ₁`

`targetStoreʷ W₁ ⊢↑[ X₁? ] c`

`q₁ : Aₛ ⊑ᵂ⟨ W₁ ⟩ B`

For `allv-conceal`, the first frame is `conceal-frame c`, so the analogous
premises are

`RebaseAtᴿ Wᵖ₁ W₁ X₁?`

`targetStoreʷ W₁ ⊢↓[ X₁? ] c`

with the same `ImpEnvMono`, `SameCtx`, and

`q₁ : Aₛ ⊑ᵂ⟨ W₁ ⟩ B`.

For the second generated reveal frame, both `allv-reveal` and `allv-conceal`
need

`ImpEnvMono W₁ Wᵖ₂`

`RebaseAtᴿ W₁ Wᵖ₂ X₂?`

`SameCtx γ₁ γᵖ₂`

`targetStoreʷ W₁ ⊢↑[ X₂? ] 〖 zero , ⇑ᵗ (＇ X) ↑ B 〗`

`q₂ : Aₛ ⊑ᵂ⟨ W₁ ⟩ replaceTy zero (⇑ᵗ (＇ X)) B`

The following transport frame then carries this endpoint across

`replace-zero-open B (＇ X)`.


Why the current peel output is insufficient
-------------------------------------------

`StructuralTargetRevealPeelProof`, `StructuralTargetConcealPeelProof`, and
`StructuralTargetAllPeelProof` return target-reduction geometry:

`Δ₁, π, W₁, ins, follows, child-target`

This is enough to rebuild the target package, but it does not expose the
relation-side geometry listed above.  In particular it does not provide:

- the rebased premise worlds `Wᵖ₁` and `Wᵖ₂`;
- the `ImpEnvMono` facts for those worlds;
- the `SameCtx` facts for the recursively transported contexts;
- indexed typing of `c` in `targetStoreʷ W₁`;
- indexed typing of the generated reveal
  `〖 zero , ⇑ᵗ (＇ X) ↑ B 〗` in `targetStoreʷ W₁`;
- the generated endpoint witnesses `qCast`, `q₁`, and `q₂`.

The old specialized proof had these witnesses in `ΛPostWindowGeometry`:

- `midFreshMono`
- `innerRebaseᴿ`
- `midFreshSame`
- `outMidMono`
- `outerRebaseᴿ`
- `outMidSame`
- `innerReveal⊢`
- `outerReveal⊢`
- `innerBody⊑ᵂ`
- `finalBody⊑ᵂ`

Stage 1h needs the analogous generic geometry for the strict peels before the
general worker can refine the parent chain into the child chain without adding
new inputs.


Required next step
------------------

Extract a reusable generated-target-frame geometry record for the strict peel
children.  It should be built from the parent relation inversion plus the
target insert/follows data, and it should provide exactly the witnesses listed
above.  Once that record exists, the live constructor helpers in
`StructuralTargetFrameAbsorptionDef.agda` can be strengthened from explicit
witness inputs to derived refinement lemmas.


RESOLVED postscript, 2026-08-14:

  The reusable generated-frame geometry surface now lives in
  `GTSFImp/proof/DGG/Catchup/StructuralGeneratedFrameGeometryDef.agda`.
  It provides the `allv-∀`, reveal, and conceal generated-frame witnesses
  consumed by the chain-refinement helpers in
  `StructuralTargetFrameAbsorptionDef.agda`.

  Stage 1m strengthened the reveal/conceal generated geometry with
  `transport₁` and `transport₂`, so generated frame chains now carry the
  rebased premise-relation transport demanded by the live relation rules.
