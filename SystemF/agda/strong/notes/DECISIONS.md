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

### Decision 1 — resolution (2026-09-03, after Jeremy's clarification and the probe)

Jeremy: the old design's (conceal) rule had the premise `Γ ∋ X:=A` and the
invariant "a conceal's representation is the one the matching reveal
recorded" was never meant to be dropped.  Decision 1 is therefore settled
on restoring it (Option 1a); 1b/1c are withdrawn.  The probe
notes/GroundedProbe.agda (agda --safe clean) fixes the exact form:

    Γ ⇈ Θ    =  (Γ ↓ Y★) , X₁:=A₁ , … , X_r:=A_r       knowledge entries (Aᵢ read in Γ)
    (bwf-↓)  Γ ∋ Y:=A₀      A = A₀[γΘ]      Γ ∣ Ψ ⊢ Θ   ⟹  Γ ∣ Ψ ⊢ ↓Y:=A , Θ

  i.e. the conceal's rep A is the INTERIOR reading of the knowledge Γ holds
  about Y.  The transport A = A₀[γΘ] is NOT optional: comparing A₀ and A
  syntactically (the naive 1a) still admits a stuck closed value `bad₂`
  (probe §5), because ` 0 read in Γ↓Y (= P) and ` 0 read in the interior
  (= the fresh reveal Z) are different variables.  In de Bruijn A₀ is first
  shifted past the r reveals and Y (`liftRep`), then γΘ is applied.
  Since the premise mentions γΘ of the WHOLE boundary, boundary
  well-formedness takes Θ as a parameter instead of recursing on the list.

  Checked in the probe: `bad` and `bad₂` are untypable; Example 8 T0…T5 all
  type and every step is a real -→ (TyWrap/Wrap included); Merge's cancel
  clause is sound by inversion (`cancel-agree`: a ↓X:=A inside a boundary
  whose reveal is ↑X:=A′ has A = A′) — the payoff.

  Consequences for Wrap (also machine-checked):
  * typing no longer transports along equal-length contexts (`¬⊢retag-len`);
    it transports along `Δ ≼ Δ′` (entrywise: abstract ≼ anything, X:=A ≼
    X:=A) — `⊢retag′`.
  * the dual rebuilds Γ's entry exactly at CONCEALED slots (the conceal rep
    is Γ's knowledge), but at BLOCKED slots it yields a dummy `↑Y:=ℕ`, i.e.
    interior entry Y:=ℕ, which can differ from Γ's entry for Y.  Wrap's
    argument retypes only if blocked slots are ABSTRACT in Γ (`BlkAbst`),
    and that property is not preserved unless the dual marks blocked slots
    specially.  Hence one more syntax change:

    Θ  ::=  …  |  ↑Y:⋆ , Θ      blocked reveal: interior entry abstract, no
                                 knowledge; external face a dummy (never named,
                                 by the scope premise); produced only by the
                                 dual at dropped-but-unconcealed slots

  Open (small): whether `BlkAbst` then holds for every run-time boundary (only
  Λ, reveals and ↑Y:⋆ create context entries) or must be a premise of (env).

## Decision 2 — a boundary meets a type application

Both well typed on every step of Example 8 (notes/Example8Trace.agda).

    (TyWrap)   (V ⟪ Θ , ∀Z.B₀ ⟫) @B[A]        -→  (V @(B₀[γΘ])[Z]) ⟪ ↑Z:=A , Θ , B₀ ⟫
    (TyWrap′)  ((ΛZ.V) ⟪ Θ , ∀Z.B₀ ⟫) @B[A]   -→  V ⟪ ↑Z:=A , Θ , B₀ ⟫

  TyWrap: total in V (Zdancewic §4.1's sketch); leaves a nested boundary per
  use.  TyWrap′: one boundary, but stuck when the body is a boundary (which
  Wrap produces) — needs Merge.  TyWrap is what the Agda has (constructor TyWrap).

### Decision 2 — resolution (2026-09-03)

Jeremy: TyWrap.  "It would yield a more consistent calculus … because that
mirrors the way Wrap works for function typed values" — both rules float the
elimination inside the boundary and are total in the wrapped value.  TyWrap′
is at most a later optimisation (and would need Merge).  No change to the Agda.

## Decision 3 — nested boundaries: merge, or let them pile up?

Option 3a — depth-1 values (Zdancewic rule (8), p. 203):

    (Merge)   (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫   -→  V ⟪ Θ₁ ⊕ Θ₂ , B₂ ⟫
    values:   c | λx:A.N | ΛX.V | V ⟪ Θ , B₀ ⟫   with V not itself a boundary

  Θ₁ ⊕ Θ₂ keeps all entries of both, except a conceal ↓X:=A in Θ₁ of a
  variable revealed ↑X:=A by Θ₂ cancels against it — sound only under 1a.
  Obligations: contexts compose, internal face composes (their (trans)),
  external face unchanged (notes/Zdancewic-embeddings.md §4).

### Decision 3 — resolution (2026-09-03)

Jeremy leans to 3a (Merge, depth-1 values).  Plan: after the Decision-1
rework lands, (i) define Θ₁ ⊕ Θ₂ and probe the three obligations (contexts
compose; internal face composes given the middle type; external face
unchanged — notes/Zdancewic-embeddings.md §4); (ii) add `Merge` with its
example and preservation case (cancel clause discharged by `cancel-agree`);
(iii) restrict `Value` so a wrapper's body is not itself a wrapper, and
adjust `Wrap`/`TyWrap`'s progress cases and canonical forms accordingly.

Option 3b — towers as values, no Merge (current, to be replaced).  Canonical form at a
  variable type = a chain of boundaries ending in a conceal; Examples
  1,2,5,6,7 end at towers; progress still needs Decision 1.

## Recommendation

All three decisions settled: restore the invariant (transported form above);
TyWrap; Merge with depth-1 values.  Order: Boundary.agda rework and re-run of every
preservation case → ⊕ probe → Merge → depth-1 values → progress.
