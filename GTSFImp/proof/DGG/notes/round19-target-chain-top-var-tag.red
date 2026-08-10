Round 19 stop: TargetChainProof top target variable-tag branch.

Focused command:

AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/\
abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home \
  agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetChainProof.agda

Current error:

  GTSFImp/proof/DGG/Inversion/TargetChainProof.agda:89,1-245,45

  Incomplete pattern matching for
  proof.DGG.Inversion.TargetChainProof.with-256. Missing cases:

    target-source-star-at {V = V ↓ x} {Y = _} {★} {c = c} {q}
      sv inert vU X∈ Y∈ D
      | fst , fst₁ , fst₂ , fst₃ , fst₄ , fst₅ ,
        _∣_⊢²_⊑_∶_.⊑cast² .(_ !) snd .fst₅

Meaning:

After `STC.seal-transfer sv vU X∈ D`, the peeled premise can still be
a top-level target variable injection:

  D₂ : W₂ ∣ γ₂ ⊢² V ⊑ U ⟨ Y₂ ! ⟩ ∶ q₂
  q₂ : (＇ X) ⊑ᵂ⟨ W₂ ⟩ ★

The non-variable target injection cases are handled by `rep★-nonvar-tag`,
and the source-conceal star/name-protected cases are handled by the new
package helpers.  This remaining variable-injection case needs either:

  1. a `TaggedTransferOutput W₂ γ₂ (V ⟨ c ⟩) (U ⟨ Y₂ ! ⟩) X (just Y₂)`
     plus the source-side premise

       W₂ ∣ γ₂ ⊢² (V ⟨ c ⟩) ↓ seal X ★ ⊑ U ⟨ Y₂ ! ⟩ ∶ q₂

     which requires a premise-world `RebaseAt W₂ W₂ X Y₂`/`StoreRepImp`
     not exposed by the `⊑cast²` branch; or

  2. a direct paired re-emission at the outer target `Y`, which would
     require identifying the target tag variable `Y₂` with that outer
     target and giving `CenterAligned W₂ X Y`.  The transfer link only
     aligns the outer target in the outer world, not in `W₂`.

Adding a permissive partner/package for this branch would contradict the
checked `SourceStarPackageCounterScratch.agda` discipline: the bad
InstanceB output package is still refutable precisely because arbitrary
variable-tag output packages cannot be fabricated.
