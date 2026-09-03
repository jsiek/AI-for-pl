# Open design decisions (2026-09-03) — alternatives as definitions

Notation as in notes.md.  Each decision lists the alternatives as definitions
and the one consequence that matters.  Status: awaiting Jeremy's choice.

## Decision 1 — what licenses a conceal's representation?

Today:

    Γ ⇈ Θ    =  (Γ ↓ Y★) , X₁ , … , X_r            reveal variables enter as ABSTRACT
    (bwf-↓)  Γ ∋ Y      Ψ ⊢ A      Γ ∣ Ψ ⊢ Θ   ⟹  Γ ∣ Ψ ⊢ ↓Y:=A , Θ

Consequence — a closed well-typed value that no type-preserving rule can
eliminate (machine-checked, notes/BoundaryRulesProbe.agda §5a):

    bad  =  (7 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=∀Z.Z→Z , X ⟫   :  ∀Z.Z→Z
    bad @(Z→Z)[ℕ]  :  ℕ→ℕ          stuck: B₀ is the variable X, not a ∀

Option 1a — record the knowledge in the interior context:

    Γ ⇈ Θ    =  (Γ ↓ Y★) , X₁:=A₁ , … , X_r:=A_r
    (bwf-↓)  Γ ∋ Y:=A      Γ ∣ Ψ ⊢ Θ            ⟹  Γ ∣ Ψ ⊢ ↓Y:=A , Θ

  No typing rule converts through X:=A, so abstraction is unchanged.  `bad`
  is ill-typed (↓X:=ℕ against X:=∀Z.Z→Z).  This is the in-the-relation form
  of Zdancewic's global δ-consistency and is what Merge (Decision 3) needs.
  Cost: A₁ is read in the exterior Γ but the entry sits in the interior,
  whose tail may lack variables A₁ names (Example 8: ↑Z:=Y , ↓X:=ℕ over
  Y, X has interior ∅ , Z:=Y with Y blocked).  So the entry is a knowledge
  entry read in Γ, not a telescope entry; in Agda ⊢renameᵀ renames it by
  the exterior renaming.
  Second cost (found while landing Wrap): today typing reads Γ only through
  ∋ and ⊢, so it transports along any context of the same LENGTH
  (BReduction.⊢retag), and Wrap's preservation uses that to retype the
  argument in the dual's interior (Γ ↓ Y★ rebuilt with abstract entries),
  which equals Γ only when Γ's dropped prefix is all abstract.  Under 1a the
  entries X:=A become typing-relevant, ⊢retag fails, and the dual's interior
  must equal Γ exactly — which fails at BLOCKED slots (their dual reveal has
  a dummy rep, Γ's entry may carry knowledge).  1a therefore needs either a
  Wrap restricted to boundaries whose exterior is all-abstract-below-Y★
  (true at run time: only Λ and reveals create entries — a probe should
  confirm), or a dual that copies Γ's knowledge for blocked slots.

Option 1b — keep (env); progress for reachable terms via a predicate

    Consistent M  ⟺  every ↓Y:=A in M whose enclosing boundary has ↑Y:=A′
                     satisfies A = A′

  preserved by reduction, true of source programs.  A companion predicate
  (against the grounded-invariants design law).

Option 1c — accept the gap: progress for source images only; no Merge/Cancel.

## Decision 2 — a boundary meets a type application

Both well typed on every step of Example 8 (notes/Example8Trace.agda).

    (TyWrap)   (V ⟪ Θ , ∀Z.B₀ ⟫) @B[A]        -→  (V @(B₀[γΘ])[Z]) ⟪ ↑Z:=A , Θ , B₀ ⟫
    (TyWrap′)  ((ΛZ.V) ⟪ Θ , ∀Z.B₀ ⟫) @B[A]   -→  V ⟪ ↑Z:=A , Θ , B₀ ⟫

  TyWrap: total in V (Zdancewic §4.1's sketch); leaves a nested boundary per
  use.  TyWrap′: one boundary, but stuck when the body is a boundary (which
  Wrap produces) — needs Merge.  TyWrap is what the Agda has (constructor TyWrap).

## Decision 3 — nested boundaries: merge, or let them pile up?

Option 3a — depth-1 values (Zdancewic rule (8), p. 203):

    (Merge)   (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫   -→  V ⟪ Θ₁ ⊕ Θ₂ , B₂ ⟫
    values:   c | λx:A.N | ΛX.V | V ⟪ Θ , B₀ ⟫   with V not itself a boundary

  Θ₁ ⊕ Θ₂ keeps all entries of both, except a conceal ↓X:=A in Θ₁ of a
  variable revealed ↑X:=A by Θ₂ cancels against it — sound only under 1a.
  Obligations: contexts compose, internal face composes (their (trans)),
  external face unchanged (notes/Zdancewic-embeddings.md §4).

Option 3b — towers as values, no Merge (current).  Canonical form at a
  variable type = a chain of boundaries ending in a conceal; Examples
  1,2,5,6,7 end at towers; progress still needs Decision 1.

## Recommendation

1a → Wrap → Merge (3a); keep TyWrap, TyWrap′ as a later optimisation.
