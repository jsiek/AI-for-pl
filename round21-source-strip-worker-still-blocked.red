Blocked goal: `GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda`

Command:

  AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda

Current result:

  Unsolved interaction metas at:
    GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda:497,57-61
    GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda:500,64-68

The two goals are still the worker inhabitants:

  source-column-strip-worker : SourceColumnStrip
  source-spine-strip-worker  : SourceSpineStrip

Agda reports the goal shapes as:

  ?0
    : Σ[ Core ∈ Term Δᴸ ]
      Σ[ CoreTy ∈ Ty Δᴸ ]
      Σ[ Xᵒ ∈ TyVar Δᴸ ]
      Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
      Σ[ γᵒ ∈ CtxImp Wᵒ ]
      Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
        (SpineValue Core
         × SourceColumnStripBranch W γ V U Xᴸ Y S cY q
             Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)

  ?1
    : Σ[ Core ∈ Term Δᴸ ]
      Σ[ CoreTy ∈ Ty Δᴸ ]
      Σ[ Xᵒ ∈ TyVar Δᴸ ]
      Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
      Σ[ γᵒ ∈ CtxImp Wᵒ ]
      Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
        (SpineValue Core
         × SourceSpineStripBranch W γ V R U Xᴸ Y S cY q
             Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)

Exploration that checked before being reverted to the original two metas:

  * The `SourceSpineStrip` right-target-cast case checks by returning
    `spine-sealed` and rebuilding with `plain-target CTI2.not-↓`.

  * The non-variable/all/gen source cast cases and source reveal/conceal
    function/all cases check by `tagged-target-nonvar-nonstar-spine-⊥`.

  * The variable-injection `cast⊑cast²` case checks by returning
    `spine-sealed` and using `star-rep-cast-final`.

After those clauses, the only `SourceSpineStrip` pattern families left are:

  source-spine-strip-worker ... (CTI2.cast⊑² c prem p)
  source-spine-strip-worker ... (CTI2.conceal⊑² ok mono rb sc c⊢ prem p)

The blocker is the source-seal/tagged-target conversion:

  * For `conceal⊑²`, the source term is already a seal, so the outer
    `SourceSpineStrip` store premise can point at the inner sealed variable.
    To wrap the outer source seal with `plain-target CTI2.not-↓`, the proof
    needs an inner stripped premise

      W′ ∣ γ′ ⊢² V ↓ seal X R ⊑ U ↓ seal Y S ∶ (＇ X) ⊑ᵂ⟨ W′ ⟩ (＇ Y)

    but the live premise only gives the tagged target

      W′ ∣ γ′ ⊢² V ↓ seal X R ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ (＇ X) ⊑ᵂ⟨ W′ ⟩ ★

    and the required `＇ X ⊑ᵂ⟨ W′ ⟩ ＇ Y` obligation is not exposed by
    the outer `SourceSpineStrip` inputs.

  * For `cast⊑²`, the analogous problem appears one source cast higher:
    stripping the tagged target from the pre-cast premise is needed before
    `star-rep-cast-final` can re-emit the paired source-star seal.

The `TargetChainProof.agda` `S = ★` pattern gives the right package shape
when the target seal has already been peeled to its payload:

  STC.emit-tagged-transfer
    ... (STC.tagged-transfer-output
      ... (STC.premise-partner-just aligned)
      (CTI2.matched-seal-star-partner
        (CTI2.rep★-var-tag aligned)))
    ...

At the worker sites the available premise is still the tagged target
`(U ↓ seal Y S) ⟨ cY ⟩`, not the payload `U`, so I could not instantiate
the same package without either:

  1. deriving the missing inner `＇ X ⊑ᵂ⟨ W′ ⟩ ＇ Y` / target-payload
     premise from the source-seal branch, or
  2. adding a new relation rule, which is forbidden without explicit
     permission and should not be done here.

No changes were made to `GTSF/QuotientedTermImprecision.agda`, and no new
postulates or holes were added.
