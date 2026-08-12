M5 instantiation inversion blocker: source-strip post obligation is missing

Date: 2026-08-12

Context:

  The approved post-prefix-only surface from
  `m5-inst-inversion-source-strip-post-only-surface-blocked.red` was
  stated in `GTSFImp/proof/DGG/notes/M5InstInversionDesignScratch.agda` as
  `ΛPostPrefixOnlySourceStripSurface`.  The live proof module now has
  checked support for the parts that do not depend on source-strip
  wrappers:

    `ΛPostPrefixPackageAt`
    `Λ-post-prefix→package-at`
    `Λ⊑Λ²-base-prefix-at`
    `Λ⊑²-smart-recursive-prefix-at`
    `mapCtxᴿ-sameCtx`
    `rightOnlyImpEnvMono`
    `post-source-conceal-partner-ok`

  These show that a post-prefix relation can be converted back into the
  existing full `InstPostCatalogPackageAt`, with the residual
  `CatchupCast⁻` rebuilt from the caller's outer residual `q`.

New resister:

  The source-strip cases still need an outer post obligation for the
  wrapper source type.  In the `cast⊑²` case:

    `c : ν ⊢ A ∼ A′`
    `prem : W ∣ γ ⊢² M ⊑ Λ V′ ∶ p`
    `q∀ : A′ ⊑ᵂ⟨ W ⟩ `∀ B`

  the recursive prefix on `prem` gives:

    `A ⊑ᵂ⟨ W₂ ⟩ ΛResidualSource₂ B`
    `W₂ ∣ mapCtxᴿ ext₂ γ ⊢² M ⊑ Λ⊑Λ²PostTerm V′ B ∶ ...`

  To rebuild `cast⊑²`, the outer branch must supply:

    `A′ ⊑ᵂ⟨ W₂ ⟩ ΛResidualSource₂ B`

  The obvious attempt, transporting `q∀` through the two target binds,
  produces the wrong target type:

    `ECR.transport⊑ᵂ ext₂ q∀
       : A′ ⊑ᵂ⟨ W₂ ⟩ applyTys χs₂ (`∀ B)`

  Agda reports the mismatch as:

    `applyTys χs₂ (`∀ B)`
      != `substᵗ Λ⊑Λ²TargetSplit₂ B`

  and `substᵗ Λ⊑Λ²TargetSplit₂ B` is the post-instantiation body type
  used by `Λ⊑Λ²PostTerm V′ B` (transported to `ΛResidualSource₂ B` by
  `residual-source₂-eq`).

Why this is a real surface gap:

  The target post-prefix is not an ordinary right-world transport of the
  original target type `∀ B`; it is the result of reducing the target
  instantiation cast through `β-inst` and `β-Λ`.  Therefore

    `A′ ⊑ᵂ⟨ W ⟩ `∀ B`

  does not by itself provide

    `A′ ⊑ᵂ⟨ W₂ ⟩ ΛResidualSource₂ B`.

  The same missing outer post obligation is required by `reveal⊑²` and
  `conceal⊑²` after their premise prefix has been obtained.  Their rebase,
  mono, same-context, and source-conceal-partner side conditions lift
  mechanically through the two right binds; the unsupplied piece is the
  post type obligation for the wrapper's source type.

Consequence:

  The four-field post-prefix surface is correctly shaped as a package, but
  the live source-strip recursion needs one more theorem or field:

    if a source-only wrapper has an outer `∀` obligation against the
    pre-instantiation target, then it must also provide, or derive, the
    corresponding obligation against the fixed two-allocation post body.

  Without that obligation, `InstInversionPackage.Λ-package` cannot rebuild
  the `cast⊑²` / `reveal⊑²` / `conceal⊑²` source-strip cases.

Checked commands after backing out the non-checking worker:

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
    GTSFImp/proof/DGG/Catchup/InstInversionProof.agda

No live relation was changed, and no postulate, hole, or catch-all was
added.
