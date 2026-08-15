LG-1 blocked surface: SealTransferCore.dynPayloadSealPartnerOK

`SealTransferCore.dynPayloadSealPartnerOK` currently rebuilds
`SealPartnerOK (SPT.dynWorld Wᵖ) Z V ★ Xᴿ? U` from an arbitrary
`Rep★PartnerOK Wᵖ Z V Xᴿ? U`.

The untagged branch reroutes to `plain-target`, and the generated-name branch
reroutes to `name-protected-target` when `var-tag-value-sealed` exposes the
partnered target seal.  The remaining top-tag branches still require
`star-rep-target`:

- `rep★-nonvar-tag`
- `rep★-matched-inner-tags`
- `rep★-round-trip` when its recursive tail is top-tagged

In the matched seal-transfer branch, `Wᵖ` is the premise world of
`conceal⊑conceal²` and `RebaseAt W₁ Wᵖ Z Y` aligns the source pivot `Z` with
target pivot `Y`.  `SPT.dynWorld Wᵖ` preserves embeddings, so target `Y`
occupies the source center.  The attempted rebuilt square is:

$$
\begin{array}{ccc}
V\downarrow \operatorname{seal} Z\,\star
  & \sqsubseteq & U \\
\downarrow^{0} & & \downarrow^{0} \\
V\downarrow \operatorname{seal} Z\,\star
  & \sqsubseteq & U
\end{array}
$$

with horizontal imprecision at
`Z`'s center while target `Y` is an occupant of that same center.  LG-1 says
this shape must not be admitted by a bare see-through rebuild.  This consumer
needs a statement-level reroute at the partnered shape, or a proof that the
top-tag residual branches cannot arise at the matched seal-transfer call site.

No live CTI2 cast-imprecision rule was changed for this surface.

2026-08-15 OPEN postscript after supervisor reroute attempt:

The matched call site can supply the target-seal evidence:

`SealTransferCore.agda:735-750`

destructs

`CTI2.conceal⊑conceal²
  (CTI2.matched-seal-star-partner partner)
  monoᵖ rbᵖ scᵖ source-seal target-seal prem .p`

so `target-seal : targetStoreʷ W₁ ⊢↓[ just Y ] seal Y ★` is in
scope.  This is enough to rebuild the paired square through the matched
family:

$$
\begin{array}{ccc}
P \downarrow \operatorname{seal} Z\,\star
  & \sqsubseteq & U \downarrow \operatorname{seal} Y\,\star \\
\downarrow^{0} & & \downarrow^{0} \\
P \downarrow \operatorname{seal} Z\,\star
  & \sqsubseteq & U \downarrow \operatorname{seal} Y\,\star
\end{array}
$$

It is not enough to inhabit the old stripped `seal-transfer` result:

$$
\begin{array}{ccc}
P \downarrow \operatorname{seal} Z\,\star
  & \sqsubseteq & U \\
\downarrow^{0} & & \downarrow^{0} \\
P \downarrow \operatorname{seal} Z\,\star
  & \sqsubseteq & U
\end{array}
$$

For `partner = rep★-nonvar-tag ...`, that stripped conclusion would require
a `SourceConcealPartnerOK ... (seal Z ★) ... U` whose only possible top-tag
route is the gated `star-rep-target`.  The checked LG-1 negative witnesses
`ChainRideProbe.probe-direct-premise-partner-empty` and
`TerminusRebuildProbe.InstanceB.inner-source-partner-empty` refute exactly
that source-seal/bare-top-tag shape at an occupied center.

Therefore a restated `dynPayloadSealPartnerOK` cannot still return
`SealPartnerOK (SPT.dynWorld Wᵖ) Z P ★ (just Y) U` for the non-variable
top-tag branches.  The sound branch is a paired/matched result; finishing
LG-1 needs a branch-sensitive `seal-transfer` output, or a further ruling
that the public `seal-transfer` surface may be weakened so these top-tag
branches return the paired target-seal square instead of the stripped
payload square.

2026-08-15 RESOLVED postscript after supervisor ruling:

`SealTransferCore.seal-transfer` now returns the branch-sensitive
`SealTransferResult` family.

- `seal-transfer-stripped` preserves the old payload result:
  `W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂`.
- `seal-transfer-paired` exposes the matched paired-seal data:
  `MatchedConcealPartnerOK Wᵖ P (seal Z ★) (just Y) U` and
  `Wᵖ ∣ γᵖ ⊢² P ⊑ U ∶ p★`, with the source and target seal typings needed to
  reconstruct
  `W₁ ∣ γ₁ ⊢² P ↓ seal Z ★ ⊑ U ↓ seal Y ★ ∶ p`.

The matched `conceal⊑conceal²` call site now classifies its payload target:
plain targets and generated-name protected targets still route to the stripped
constructor; non-variable top tags, matched-inner tags, and round-trip tails
that remain top-tagged route to the paired constructor.  No CTI2 rule, cast
rule, or occupancy gate was changed.
