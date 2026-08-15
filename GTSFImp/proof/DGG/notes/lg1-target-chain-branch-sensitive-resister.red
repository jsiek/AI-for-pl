LG-1 TargetChainProof resister after branch-sensitive seal-transfer.

Command:

  agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetChainProof.agda

Current first error:

  GTSFImp/proof/DGG/Inversion/TargetChainProof.agda:170

The failing branch is the old stripped source-star continuation after
`STC.seal-transfer`:

`D₂ = conceal⊑²
  (seal-partner-ok (star-rep-target no-target partner))
  monoᵖ rbᵖ scᵖ source⊢ prem q₂`

The live `star-rep-target` gate gives
`no-target : NoTargetOccupantAtSource Wᵖ X`, where `Wᵖ` is the premise world
of that source-only conceal.  The helper needed by the old continuation must
emit a fresh `star-rep-target` at the post-transfer world `W₂`, so it needs:

`NoTargetOccupantAtSource W₂ X`.

There is no sound transport from the available fact to the needed fact.  The
rebase

`rbᵖ : TagRebaseAtᴸ Wᵖ W₂ (just X) Xᴿ?`

may be a variable rebase, and variable rebasing is allowed to move the source
pivot.  In that case `W₂` may occupy the new source center with the target
partner, exactly the condition LG-1 uses to reject the stripped source-seal /
bare-target shape.

The new paired `seal-transfer-paired` branch has the analogous public statement
tension.  `TargetSourceStarAt` must return:

`W ∣ γ ⊢² (V ⟨ c ⟩) ↓ seal X ★ ⊑ U ↓ seal Y ★ ∶ q`

with `c : (＇ X) ∼ ★`.  The paired branch supplies the sound square:

`Wᵖ ∣ γᵖ ⊢² P ↓ seal X ★ ⊑ U ↓ seal Y ★ ∶ q`.

Trying to continue with the old shape would require either:

- a stripped premise `P ↓ seal X ★ ⊑ U`, which is exactly the refuted
  occupied-center intermediate, or
- a source cast step from `＇ X ⊑ ＇ Y` to `★ ⊑ ＇ Y`, for which the live type
  imprecision relation has no constructor.

So `TargetSourceStarAt` cannot absorb the paired case while keeping its current
public meaning.  Weakening the M3 statement to return a paired alternative
would be a public statement change, and the task explicitly says
`right-inj-inversion²` and the M3 stack statements must keep their meaning.
