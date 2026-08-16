LG-3 endpoint transport resister: paired function source cast / target expand

Status: open as of 2026-08-16.

This blocks supervisor option (a) at the stated generality.  The failing cell
is the paired target expansion row:

`cast⊑cast² c (？ d) prem q`

where the source cast is inert by the `fun` value constructor and the target
cast takes an `expand` step.

The checked witness is
`proof/DGG/notes/LG3EndpointTransportCounterexampleScratch.agda`.

The cell is instantiated in a one-variable world whose shared center marks the
variable precise:

`X : X⊑X`

Use the endpoints:

`C = ★ ⇒ ℕ`

`A = X ⇒ ℕ`

`G = ★ ⇒ ★`

`B = X ⇒ ℕ`

The paired witnesses are inhabited:

`p★ : C ⊑ ★`

`qB : A ⊑ B`

The source cast is an inert function cast:

`source-cast : C ∼ A`

Its domain component uses a consistency environment where, after `flipᵐ`, the
variable can be widened to `★`.

The target residual cast is:

`target-residual : G ∼ B`

and the reducing target cast is:

`target-expand-cast = ？ target-residual : ★ ∼ B`

The target step is the ordinary expansion step:

`target-star-value ⟨ target-expand-cast ⟩`

reduces to

`target-star-value ⟨ ？ (idᵍ ★⇒★) ⟩ ⟨ target-residual ⟩`.

The endpoint-transport lemma needed by the rebuild would have to produce:

`A ⊑ G`

that is:

`X ⇒ ℕ ⊑ ★ ⇒ ★`.

This is impossible in the precise center.  Inverting a candidate proof leaves
the domain obligation `X ⊑ ★`, whose only possible constructor would require
`X⊑X ≡ X⊑★`.

The CTI premise is not empty.  The scratch checks all of the following:

- `source-casted-value : Value (source-core ⟨ source-cast ⟩)`
- `target-star-value-value : Value target-star-value`
- `source-to-target-star-value : W ∣ [] ⊢² source-core ⊑ target-star-value ∶ p★`
- `paired-expand-cell-nonempty :
  W ∣ [] ⊢² source-core ⟨ source-cast ⟩
    ⊑ target-star-value ⟨ target-expand-cast ⟩ ∶ qB`
- `target-expand-step`

So both closure routes fail for this cell:

- the requested post-source midpoint witness is not derivable;
- the relevant paired CTI premise is inhabited.

No CTI relation change has been made.
