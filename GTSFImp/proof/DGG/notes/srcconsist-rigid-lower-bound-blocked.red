Rigid source-consistency lower-bound blocker

Command:

  AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/\
abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home \
    agda -i GTSFImp -v0 GTSFImp/proof/ImprecisionConsistency.agda

Failure after adding the approved rigid gates:

  GTSFImp/proof/ImprecisionConsistency.agda:428,1-520,37
  Incomplete pattern matching for consistent-common-lowerᵐ. Missing:

    consistent-common-lowerᵐ h
      (_! {G = ＇ X} {G∼★ = X∼★ʳ eq} c)

This is not a mechanical missing case.  The old statement is:

  LowerEnv μ φ ψ
  -> μ ⊢ A ∼ B
  -> ∃[ D ] φ ⊢ D ⊑ A × ψ ⊢ D ⊑ B

For the rigid branch, take:

  μ X = X∼X
  h X = var-refl
  c = id (＇ X)

Then the new rigid tag gives:

  μ ⊢ ＇ X ∼ ★

The old theorem would require a `D` such that:

  φ ⊢ D ⊑ ＇ X
  ψ ⊢ D ⊑ ★

The direct variable lower forces `D = ＇ X`, and the star-side proof then
needs `ψ X ≡ X⊑★`.  But `h X = var-refl` gives `ψ X = X⊑X`.

The repair route named in the preflight, `both-to-star`, works only if the
statement selects or requires that lower-env branch for rigid variables.  The
current theorem quantifies over arbitrary `LowerEnv`, so it also admits
`var-refl`; under that premise the rigid branch is false.

The same issue appears under `∀ᶜ`: a rigid gate for the bound variable can be
used inside the body, while `∀⊑∀` lowers bodies under `I.extᵐ`, whose fresh
variable is precise rather than dynamic.  That requires a larger statement
change to the lower-bound characterization or a change to the type-imprecision
relation, neither of which is specified by the live migration preflight.
