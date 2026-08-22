Round 12 stop note: TargetChainProof route A needs one more package

Command:

agda -i GTSFImp -v0 \
  GTSFImp/proof/DGG/Inversion/TargetChainProof.agda

Live red remains:

GTSFImp/proof/DGG/Inversion/TargetChainProof.agda:88,3-90,29

The requested support lemmas split as follows:

1. `decay-rep★-round-trip` is derivable and now public in
   `SealTransferCore`.

2. `aligned-functional` and the RebaseAt-level target-pedigree uniqueness
   lemmas are derivable in `TargetWalkSupport`.  The usable statement is:

   aligned-functional :
     CTI2.CenterAligned W X Y →
     CTI2.CenterAligned W X Y′ →
     Y ≡ Y′

   and therefore two `RebaseAt _ W X _` witnesses with the same conclusion
   world identify their target pivots.

3. The route-A rebuild is still missing a bridge.  The failing package is:

   decayed-source-star-bridge : ∀ {Δᴸ Δᴿ Δ}
       {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
       {γ : CTI2.CtxImp W} {γᵖ : CTI2.CtxImp Wᵖ}
       {P : Term Δᴸ} {U : Term Δᴿ}
       {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
       {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X) ∼ ★}
     → Inert c
     → Value U
     → CTI2.ImpEnvMono W Wᵖ
     → CTI2.RebaseAt Wᵖ W X Y
     → CTI2.SameCtx γ γᵖ
     → CTI2.sourceStoreʷ W ∋ X ⦂ ★
     → CTI2.targetStoreʷ W ∋ Y ⦂ ★
     → CTI2.Rep★PartnerOK Wᵖ X P (just Y) U
     → Wᵖ ∣ γᵖ ⊢² P ⊑ U ∶ ★⊑★
     → Σ[ γᵈ ∈ CTI2.CtxImp (SPT.dynWorld Wᵖ) ]
         ( CTI2.ImpEnvMono W (SPT.dynWorld Wᵖ)
         × CTI2.RebaseAt (SPT.dynWorld Wᵖ) W X Y
         × CTI2.SameCtx γ γᵈ
         × (SPT.dynWorld Wᵖ) ∣ γᵈ ⊢²
             (P ↓ seal X ★) ⟨ c ⟩ ⊑ U ∶ ★⊑★
         × CTI2.MatchedConcealPartnerOK (SPT.dynWorld Wᵖ)
             ((P ↓ seal X ★) ⟨ c ⟩) (seal X ★) Y U )

Obstruction:

The final paired constructor requires the premise derivation and the
`MatchedConcealPartnerOK` witness in the same world.

The partner side can live in `SPT.dynWorld Wᵖ`:

  STC.decay-rep★-round-trip inert partner :
    CTI2.Rep★PartnerOK (SPT.dynWorld Wᵖ) X
      ((P ↓ seal X ★) ⟨ c ⟩) (just Y) U

But the source-seal reconstruction produced by `seal-transfer` for the paired
branch lives at the post-rebase conclusion world:

  CTI2.conceal⊑²
    (CTI2.seal-partner-ok
      (dynPayloadSealPartnerOK ... partner))
    ...
    (CTI2.tag-rebase-varᴸ
      (TD.decayRebaseAt (SPT.dynWorld-decay Wᵖ)
        (SPT.dynWorld-decay W) rbᵖ))
    ...

That builds:

  (SPT.dynWorld W) ∣ _ ⊢² P ↓ seal X ★ ⊑ U ∶ _

and then:

  (SPT.dynWorld W) ∣ _ ⊢² (P ↓ seal X ★) ⟨ c ⟩ ⊑ U ∶ ★⊑★

If we choose the outer premise world as `SPT.dynWorld W`, the premise is
available but the round-trip partner must be transported from `Wᵖ` across the
source rebase.  That transport is not valid in general for
`rep★-matched-inner-tags`, because its alignment is a premise-world fact about
the inner source/target tags.

If we choose the outer premise world as `SPT.dynWorld Wᵖ`, the round-trip
partner is available, but constructing

  (SPT.dynWorld Wᵖ) ∣ _ ⊢² P ↓ seal X ★ ⊑ U ∶ _

would require a same-world source tag rebase

  CTI2.TagRebaseAtᴸ (SPT.dynWorld Wᵖ) (SPT.dynWorld Wᵖ)
    (just X) (just Y)

for the carried `Rep★PartnerOK ... (just Y) ...`.  The available rebase is
instead:

  CTI2.RebaseAt Wᵖ W X Y

which decays to a rebase from `SPT.dynWorld Wᵖ` to `SPT.dynWorld W`, not a
same-world rebase in `SPT.dynWorld Wᵖ`.

`target-pedigree-unique` cannot close this gap: it identifies two target
pivots only when both alignments/rebases are in the same conclusion world.
Here the available outer pivot alignment is in `W`, while the partner evidence
that route A wants to keep is indexed by `Wᵖ`.

Thus the three requested support lemmas are not enough to discharge
`TargetChainProof.agda:88`.  A further package is needed, such as a proven
transport of the source-star premise from `SPT.dynWorld W` back to
`SPT.dynWorld Wᵖ`, or a strengthened transfer/terminal surface that returns the
rebuilt premise and the round-trip partner in one common world.
