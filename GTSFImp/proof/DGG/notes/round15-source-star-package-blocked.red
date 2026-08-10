Round 15 blocked case: the exact source-star package theorem is too strong.

Checked command:

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/\
abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home \
  agda -i GTSFImp -v0 SourceStarPackageCounterScratch.agda

The scratch file type-checks and instantiates the proposed theorem shape from
`round14-target-chain-source-star-package.red` with all premises inhabited, but
the requested output package empty.

Concrete instance, from `proof.DGG.TerminusRebuildProbe.InstanceB`:

  W  = InstanceB.W
  γ  = []
  X  = InstanceB.X
  Yᵒ = InstanceB.Y
  Y  = InstanceB.Y₂

  V = InstanceB.source

  U =
    ((InstanceB.U₀ ↓ seal InstanceB.Y₂ ★)
      ↓ seal InstanceB.Y (＇ InstanceB.Y₂))
      ⟨ id {μ = InstanceB.target-env} (＇ InstanceB.Y) ! ⟩

  c = id {μ = InstanceB.source-env} (＇ InstanceB.X) !
  q = InstanceB.X⊑★-W
  D = InstanceB.tagged-input

The exact theorem would require:

  STC.TaggedTransferOutput W [] (V ⟨ c ⟩) U X Y₂

Equivalently, its partner field must contain:

  CTI2.MatchedConcealPartnerOK W
    (V ⟨ c ⟩) (seal X ★) Y₂ U

Since the seal is `seal X ★`, this can only be the star-seal constructor,
so it requires:

  CTI2.Rep★PartnerOK W X (V ⟨ c ⟩) (just Y₂) U

But `SourceStarPackageCounterScratch.no-output-partner` proves this partner
empty.  The target top tag in `U` is at `Yᵒ`, while the package requests
`just Y₂`.  The direct `rep★-var-tag` route would require the target tag to
be `Y₂`; the `rep★-matched-inner-tags` route would have to use the same
source pivot `X` as an inner tag and is rejected by its `X₂ ≢ X` premise; and
the recursive round-trip branch reduces to the same mismatch on the inner
source payload.

The exact missing branch is therefore:

  source-star-cast-package
    source-spine
    source-inert
    target-tag-value
    InstanceB.X∈
    InstanceB.tagged-input

with result:

  STC.TaggedTransferOutput W [] (V ⟨ c ⟩) U X Y₂

The available validated tools cover the same-name case (`Y = Yᵒ`) and the
non-pivot matched-inner-tag case.  They do not provide a way to retarget a
top-level variable tag from `Yᵒ` to arbitrary `Y₂`, and doing so would be
unsound for the current `Rep★PartnerOK` surface.
