LG-3 blocked surface: `ValueCatchupRightAt` / M6 fuel knot

The CatchupColumn-family premises have been removed from the live statements.
The new value-catch-up surface consumes:

`W ∣ γ ⊢² M ⊑ applyColumn M′ κ ∶ q`, `Value M`, `Value M′`, and the syntactic
`CastColumn`.

The old recursion cannot be mechanically replayed because `CatchupColumn` and
`CatchupColumn⁻` supplied, for every layer, the exact intermediate
imprecision obligation and the residual-cast admissibility proof.  The
inversion-based recursion needs a live column peel theorem:

for `κ = c ▻ᶜ κ′`, invert
`W ∣ γ ⊢² M ⊑ applyColumn (M′ ⟨ c ⟩) κ′ ∶ q`
to obtain the head premise required by `ExtraCastRightAt` for `c`, then after
the head target reduction transport the remaining syntactic column `κ′` and
continue recursively.

The M5/NS-4 consumers no longer depend on the deleted column propositions;
they build residual cast CTI premises directly with `⊑cast²`.  The executable
M6 knot remains parked until the column peel theorem and the extra-cast proof
above are available.
