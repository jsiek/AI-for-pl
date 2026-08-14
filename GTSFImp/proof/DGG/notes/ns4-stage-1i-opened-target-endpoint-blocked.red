NS-4 stage 1i opened-target-endpoint blocker
=============================================

Status
------

Stage 1i now has the reusable generated-frame record surface:

- `StructuralAllGeneratedFrameGeometry`
- `StructuralRevealGeneratedFrameGeometry`
- `StructuralConcealGeneratedFrameGeometry`

and `StructuralTargetFrameAbsorptionDef` consumes these records in the
all-∀, all-reveal, and all-conceal child-chain helpers.  This closes the
stage-1h calibration shape where the helper was taking the generated witnesses
as ten independent arguments.

The concrete strict-head instances are still blocked at the opened endpoint
layer, not at target insert/rebase bookkeeping.


Derivable from the current target-insert layer
----------------------------------------------

For the first inherited reveal/conceal frame after a strict peel, the peel
provides

`Δ₁, π, W₁, ins, follows, child-target`.

Given the parent right-side relation constructor, `TargetExtend` can derive the
rebased premise side:

- `insertRebaseAtᴿ ins rb` for `⊑reveal²`;
- `reverseRebaseAtᴿ ins rb` for `⊑conceal²`;
- `impEnvMono-insert ins insᵖ mono`;
- `mapCtxᵀ-same ins insᵖ sc`;
- `reveal-renameˣ (targetStore-rename ins) c⊢`;
- `conceal-renameˣ (targetStore-rename ins) c⊢`.

For the generated reveal

`〖 zero , ⇑ᵗ (＇ X) ↑ B 〗`

the target store typing is also structurally available from `follows` plus the
generic generated-reveal typing lemmas in `InstInversionProof`.  The pivot may
be selected by the occurrence decision for `zero ∈ᵗ B`.


Missing opened endpoints
------------------------

The live tree still lacks a generic lemma that opens a target-side universal
endpoint through the strict peel's fresh bind.

For `allv-∀`, after peeling

`(V ⟨ ∀ᶜ d ⟩) ⦂∀ C [ ＇ X ]`

the generated cast frame needs

`qCast : Aₛ ⊑ᵂ⟨ W ⟩ C [ ＇ X ]ᵗ`

for `d : extᵐ μ ⊢ B ∼ C`.

For `allv-reveal` and `allv-conceal`, after peeling into `W₁`, the generated
conversion frames need

`q₁ : Aₛ ⊑ᵂ⟨ W₁ ⟩ B`

and

`q₂ : Aₛ ⊑ᵂ⟨ W₁ ⟩ replaceTy zero (⇑ᵗ (＇ X)) B`.

These are the strict-head analogues of the Λ-side fields
`innerBody⊑ᵂ` and `finalBody⊑ᵂ` in `ΛPostWindowGeometry`, but the existing
checked lemmas are specialized to the Λ source body premise

`A : Ty (suc Δᴸ)`

and to a `liftWorldBoth` premise.  The strict generated-frame instances need a
statement over an arbitrary source endpoint

`Aₛ : Ty Δᴸ`

against a target universal endpoint, so the Λ lemmas cannot be imported as-is
without changing their logical shape.


Required proof surface
----------------------

Add a shared, non-Λ-specific opened-target-endpoint lemma family, likely in the
base inst-inversion support rather than in `InstInversionLambdaProof`.

The needed statements should be statement-first and should expose the exact
strict-peel endpoints above.  Once those endpoints are available, the rest of
each concrete geometry record is obtained from the existing target-insert
machinery listed above, and the general worker can consume the record-based
C2/C3 helpers without any new worker inputs.

No live relation was changed, and no postulate, hole, catch-all, or weakened
statement was added.
