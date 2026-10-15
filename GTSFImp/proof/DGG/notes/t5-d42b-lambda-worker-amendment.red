# D4.2b: the approved Λ one-bind worker statement is uninhabitable at
# vacuous B — amendment needed

Status: ask. No implementation; nothing else on this branch yet.

The approved D4.2 statement (`Λ-strict-one-bind-child`, telescope in
t5-lambda-strict-one-bind-proposal.red, merged via #160) concludes in a
`StructuralStrictChild` that demands

    Value (V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗)

When the ∀-body `B` does not mention its bound variable (vacuous/base
`B`), the conversion `〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗` degenerates to an
identity reveal, and `RevealValue` has only function and universal
constructors — so the conclusion is uninhabitable at base `B`. The
`child-target : StructuralTargetInstantiationPackage …` premise
guarantees only that its eventual `final` is a value, not the revealed
term itself. Additionally the route1 geometry needs a one-bind
`TargetWindowInsert` witness absent from the approved telescope.

## Amendment options

(1) GUARD-AND-SPLIT (recommended): add premises

    NonVar B  →  Fin.zero ∈ᵗ B  →  (window : TargetWindowInsert …)

to the worker — the same NonVar/∈ᵗ discipline the stage-1 design and
the D14 lifted-body obligations already use (the smart-comma/plain
split). The vacuous-B case then gets its own degenerate route in the
strict cell (no reveal wrapper is created); that routing is part of
the approval.

(2) REFACTOR THE CONCLUSION around `child-target.final` (which IS
guaranteed a value) — a different result shape for the strict child's
instantiation; cleaner in the vacuous case but a larger departure from
the approved telescope and from what the stage-1 worker consumes.

Question (D4.2b): guard-and-split (1), or conclusion-refactor (2)?
