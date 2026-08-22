LG-1 blocked surface: ChainRideProbe.probe-premise

The old live probe constructed:

  W₂ ∣ [] ⊢² V₀ ↓ seal Z₃ ★ ⊑ U ∶ ＇ Z₃ ⊑ ★

with `U = ($ 0) ⟨ ℕ! ⟩` by the same-world source-seal
see-through clause:

  seal-partner-ok
    (star-rep-target (rep★-nonvar-tag nonvar-base))

In `W₂`, source `Z₃` and target `Y` both occupy center `c`.
The new `star-rep-target` premise is therefore false:

Diagram:

  V₀ ↓ seal Z₃ ★     ⊑     ($ 0) ⟨ ℕ! ⟩
       │                         │
       │ same world W₂           │ target Y occupies center c
       ▼                         ▼
  source center c       =       target center c

The direct same-world partner is now recorded in
`probe-direct-premise-partner-empty`.  A stronger theorem saying the
whole live relation is empty is false at this surface: `conceal⊑²`
can still transport a source-only premise across a source rebase whose
conclusion is occupied.  That is the V2-table "do not transport the
dead clause; rederive at the partnered shape" case, not an LG-1 rule
change.
