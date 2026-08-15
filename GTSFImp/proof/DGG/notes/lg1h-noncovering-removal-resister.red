LG-1h resister: the three new `NON_COVERING` pragmas hide real surface
mismatches.

Command that exposes the target-strip cases:

  cd GTSFImp
  AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home \
    agda -i . -v0 proof/DGG/Inversion/TargetStripProof.agda

Agda reports the two missing target-strip branches:

  seal-descent-current-star ... |
    STC.seal-transfer-paired x x₁ x₂ x₃ x₄ x₅ x₆

  seal-descent-at-var ... | Xᴸ , refl , aligned | refl |
    STC.seal-transfer-paired x x₁ x₂ x₃ x₄ x₅ x₆

In both cases the result type is still the old stripped terminal record:

  TargetSealTerminusData W γ V A U X Y S

Its only constructor requires:

  W★ ∣ γ★ ⊢² V ⊑ U★ ∶ q★

with `q★ : A ⊑ᵂ⟨ W★ ⟩ ★`.  In the star-seal paired branch,
`SealTransferResult` instead provides:

  V = P ↓ seal X ★
  MatchedConcealPartnerOK Wᵖ P (seal X ★) (just Y) U
  Wᵖ ∣ γᵖ ⊢² P ⊑ U ∶ ★⊑★

It does not provide, and cannot soundly synthesize, the stripped premise:

  Wᵖ ∣ γᵖ ⊢² P ↓ seal X ★ ⊑ U ∶ (＇ X) ⊑ᵂ⟨ Wᵖ ⟩ ★

That missing premise is exactly the occupied-center source-seal/bare-target
shape that LG-1 split out of `seal-transfer`.

The source worker has the same obstruction at `wrap-star-cast-final`.  After
removing its pragma, the unchecked branches are the residual, paired, and
payload alternatives returned by `target-source-star-at` and
`target-source-star-chain`.

The immediate star case would have to turn a carried residual square

  W′ ∣ γ′ ⊢² P ↓ seal X ★ ⊑ U ↓ seal Y ★ ∶ (＇ X) ⊑ᵂ⟨ W′ ⟩ ＇ Y

into the old final conclusion

  W ∣ γ ⊢² ((P ↓ seal X ★) ⟨ c ⟩) ↓ seal X ★
    ⊑ U ↓ seal Y ★ ∶ (＇ X) ⊑ᵂ⟨ W ⟩ ＇ Y

The only direct route through the live constructors first casts the source side
to `★`, which would require a type-imprecision witness:

  ★ ⊑ᵂ⟨ _ ⟩ ＇ Y

No such constructor exists, by design.  The paired and payload cases only make
this more explicit: the branch-sensitive result carries the matched pair or
payload provenance so a later site with the matching target cast can consume
the residual square, as `RightInjInversion2Proof` does with
`cast⊑cast²`.  `wrap-star-cast-final` has no matching target cast in its
input.

Conclusion: the pragmas were hiding a real statement mismatch.  Closing these
cases requires reshaping the target/source strip result surfaces to carry a
paired/residual alternative through to the existing higher-level consumer,
or strengthening the helper inputs so they only accept an already-final
`TargetSourceStarAtResult`/`TargetSourceStarChainResult`.  The current old
final-record statements cannot consume the new LG-1 paired alternatives
without reintroducing the rejected source-seal/bare-target premise.

Postscript 2026-08-15: the target-strip half of this diagnosis is resolved in
`TargetStripDef`/`TargetStripProof` by carrying paired terminus/strip
alternatives through the target strip surfaces and consuming them at the
matching target-cast branch with `cast⊑cast²`.

The source-worker half remains open.  `SourceStripWorkerProof` still exposes
the old final-only `wrap-star-cast-final` obstruction when checked through
`SourceStripProof`: `target-source-star-at` and `target-source-star-chain`
can return residual/paired/payload alternatives, and the helper has no matching
target cast in its input.  Moving those alternatives to the existing legacy
worker pragmas or reintroducing the removed pragma would hide the mismatch
rather than close it.  A real close needs a source-strip surface that carries
the cast-restored residual to a consumer with the target cast, without changing
the protected top-level theorem surface.
