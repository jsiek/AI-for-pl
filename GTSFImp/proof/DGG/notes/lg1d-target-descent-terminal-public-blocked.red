LG-1d protected public surface blocker: `TargetSealTerminal.premiseᵒ`

Mandatory `RightInjInversion2Def` check passed: the public
`RightInjInversion²` statement is a function surface ending in
`W ∣ γ ⊢² M ⊑ N ∶ q`; it exposes no record field and embeds no stripped
source-seal/bare-target square.

The stop is instead the protected `TargetDescentDef` surface.  In
`TargetDescentDef.agda`, `TargetSealDescent` fixes the terminal payload as
`P = V ⟨ c ⟩`:

`TargetSealDescentResult {W₀ = W} {γ₀ = γ} {P = V ⟨ c ⟩}
  {U = U} Xᴸ Y q S`

For `S = ★`, `target-seal★` requires `TargetSealTerminal`, whose field

`premiseᵒ : Wᵒ ∣ γᵒ ⊢² P ⊑ U ∶ ★⊑★`

therefore becomes:

`Wᵒ ∣ γᵒ ⊢² V ⟨ c ⟩ ⊑ U ∶ ★⊑★`

When the input descent has `V = P₀ ↓ seal X ★` and the live gate classifies the
top-tag matched branch as `seal-transfer-paired`, the available sound square is
the paired matched-seal square:

$$
\begin{array}{ccc}
P₀ \downarrow \operatorname{seal} X\,\star
  & \sqsubseteq & U \downarrow \operatorname{seal} Y\,\star \\
\downarrow^{0} & & \downarrow^{0} \\
P₀ \downarrow \operatorname{seal} X\,\star
  & \sqsubseteq & U \downarrow \operatorname{seal} Y\,\star
\end{array}
$$

plus the branch-local partner evidence
`MatchedConcealPartnerOK Wᵖ P₀ (seal X ★) (just Y) U` and the premise
`Wᵖ ∣ γᵖ ⊢² P₀ ⊑ U ∶ ★⊑★`.

The protected terminal field asks instead for the stripped source-seal /
bare-target payload after applying the source star cast:

$$
\begin{array}{ccc}
(P₀ \downarrow \operatorname{seal} X\,\star)\langle c\rangle
  & \sqsubseteq & U \\
\downarrow^{0} & & \downarrow^{0} \\
(P₀ \downarrow \operatorname{seal} X\,\star)\langle c\rangle
  & \sqsubseteq & U
\end{array}
$$

or, before the cast wrapper, the same rejected source-seal/bare-target shape:

$$
\begin{array}{ccc}
P₀ \downarrow \operatorname{seal} X\,\star
  & \sqsubseteq & U \\
\downarrow^{0} & & \downarrow^{0} \\
P₀ \downarrow \operatorname{seal} X\,\star
  & \sqsubseteq & U
\end{array}
$$

At an occupied center this is exactly the LG-1 gated shape.  The paired
`SealTransferResult` branch carries more information, but it does not produce
the bare-target premise required by `TargetSealTerminal.premiseᵒ`.

`TargetDescentProof.target-seal★-descent` currently shows the same obstruction:
the old tuple pattern at the `seal-transfer` call no longer matches the
branch-sensitive result, and the old construction at lines 153-159 used
`CTI2.cast⊑² c D₂ ★⊑★` precisely as the `premiseᵒ` field.  In the paired
constructor there is no corresponding `D₂ : V ⊑ U`.

Because `TargetDescentDef` is listed as protected by the supervisor ruling,
reshaping this terminal result would be a public-statement change, not merely
an internal M3 walk migration.
