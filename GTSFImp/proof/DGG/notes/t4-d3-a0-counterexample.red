# T4 D3 `A₀ = ★` counterexample

The `SourceBindTransport²ᵀ` statement should not be specialized to
`A₀ := ★`.

The checked left-only producer set is not limited to `β-inst`.

`β-inst` does allocate `★`:

```agda
β-inst :
  ...
  → V ⟨ (inst c) B≢★ ⟩ —→[ bind ★ ]
      ⇑ᵗᵐ V ⦂∀ (bind ★ ▷ᵇ A) [ ＇ 0 ] ↑ 〖 0 , ★ ↑ A 〗
```

But source-only universal closing is also wired for the source-side
type-application roots in `proof/DGG/SimProof.agda`:

```agda
sim parked
    (•⊑² p∀ M⊑M′ q r) (β-Λ vM) =
  sim-source-all-closing parked M⊑M′ q r (Λ vM) (β-Λ vM)

sim parked
    (•⊑² p∀ M⊑M′ q r) (β-gen vM A≠★ safe) =
  sim-source-all-closing parked M⊑M′ q r
    (vM 《 genᵥ A≠★ safe 》) (β-gen vM A≠★ safe)

sim parked
    (•⊑² p∀ M⊑M′ q r) (β-reveal-∀ vM) =
  sim-source-all-closing parked M⊑M′ q r
    (vM ↑ all) (β-reveal-∀ vM)

sim parked
    (•⊑² p∀ M⊑M′ q r) (β-conceal-∀ vM) =
  sim-source-all-closing parked M⊑M′ q r
    (vM ↓ all) (β-conceal-∀ vM)
```

Those roots come from `Reduction.agda` and their store changes are not
restricted to `★`:

```agda
β-Λ :
  ...
  → (Λ V) ⦂∀ B [ A ] —→[ bind A ]
      V ↑ 〖 0 , ⇑ᵗ A ↑ B 〗

β-gen :
  ...
  → (V ⟨ (gen c) A≢★ ⟩) ⦂∀ B [ C ] —→[ bind C ]
      ...

β-reveal-∀ :
  ...
  → (V ↑ `∀↑ c) ⦂∀ B [ A ] —→[ bind A ]
      ...

β-conceal-∀ :
  ...
  → (V ↓ `∀↓ c) ⦂∀ B [ A ] —→[ bind A ]
      ...
```

There is also a concrete existing left-only world witness in
`proof/DGG/LambdaImpProbe.agda`:

```agda
probe-world₁ = CTI2.leftOnlyWorld X⊑★ probe-world₀ Ex.ℕᵗ
```

The surrounding note states that this is the source `β-Λ` step allocating
`Xᴸ ↦ ℕ`.  This is a genuine non-`★` left-only bind.

Conclusion: Statement 2 must remain polymorphic in `A₀`, or the live
left-only `β-Λ`/universal-closing path is not covered.  Per the D3
instruction, `SourceBindTransport²ᵀ` is left unimplemented in this run.
