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
