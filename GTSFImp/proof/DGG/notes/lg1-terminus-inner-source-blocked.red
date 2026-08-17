LG-1 blocked surface: TerminusRebuildProbe.InstanceB.inner-source-seal²

The old InstanceB inner witness constructed:

  Wᵖ ∣ [] ⊢² V₀ ↓ seal X ★ ⊑ dyn-id ∶ ＇ X ⊑ ★

using:

  seal-partner-ok
    (star-rep-target (rep★-nonvar-tag nonvar-fun))

In `Wᵖ`, source `X` and target `Y₂` both occupy center `1`, so the
new `NoTargetOccupantAtSource Wᵖ X` premise is false.

Diagram:

  V₀ ↓ seal X ★     ⊑     (ƛ (` 0)) ⟨ fun! ⟩
       │                          │
       │ same world Wᵖ            │ target Y₂ occupies center 1
       ▼                          ▼
  source center 1       =        target center 1

The direct same-world partner is now recorded in
`inner-source-partner-empty`.  The outer tagged InstanceB input remains
constructive by routing through `name-protected-target` at the partnered
outer seal, so this note stops only the old inner source-seal/bare-target
see-through surface.
