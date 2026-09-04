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

### Decision 1 — refinement forced by the implementation (2026-09-04)

The rework (worktree, not merged; 2 labelled holes) machine-checked that the
form above is not yet right: storing a reveal's rep "as written, read in the
exterior" as the interior entry X:=A is inconsistent with renaming, because
every other use of an entry (∋ X:=A, the shift liftRep, ⊢renameᵀ) reads it as
a TELESCOPE entry, over the entries below it.  Witness (`¬hk-int`):

    Γ = X:=ℕ , W        Θ = ↑Z:=W , ↓X:=ℕ        weaken by a new abstract V
    Γ ⇈ Θ = ∅ , Z:=W    but after weakening the entry reads Z:=(the slot W moved to)
    while the interior renaming (identity here) demands the entry be unchanged.

Fix (worked out, to implement): the interior entry is the INTERIOR READING of
the reveal's rep — concealed variables replaced by their reps, kept variables
re-indexed — and a reveal whose rep names a BLOCKED variable contributes an
abstract entry (no knowledge):

    Γ ⇈ Θ    =  (Γ ↓ Y★) , X₁:⟦A₁⟧ , … , X_r:⟦A_r⟧
       ⟦A⟧    =  A[γΘ]  if A names no blocked variable,   X:⟦A⟧ = X abstract otherwise
    (bwf-↓)  Γ ∋ Y:=A₀     ⟦A₀⟧ scoped (names no blocked var)     A = ⟦A₀⟧
             Ψ ⊢ A     Γ ∣ Ψ ⊢ Θ                             ⟹  Γ ∣ Ψ ⊢ ↓Y:=A , Θ

  Under the grounded premise a conceal rep never names a reveal variable (it
  is the reading of exterior knowledge, which bottoms out in kept variables),
  so ⟦A⟧ is a legitimate telescope entry.  `bad`/`bad₂` stay refuted.

### Decision 4 — Wrap and a blocked slot that carries knowledge (needs a ruling)

The example.  Exterior Γ = Y:=𝔹 , X:=ℕ (both revealed; Y shallower).  A sealed
identity on X, and an argument of type X that USES Y's knowledge:

    h  =  (λx:ℕ. x) ⟪ ↓X:=ℕ , X→X ⟫              : X→X      Γ ⇈ (↓X:=ℕ) = ∅ ; Y is BLOCKED
    W  =  (3 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↓Y:=𝔹 , X ⟫         : X        the outer conceal reads Γ ∋ Y:=𝔹
    R  =  h · W                                   : X        well typed, a Wrap redex

    (Wrap)  R  -→  ((λx:ℕ. x) · (W ⟪ Θᵈ , X ⟫)) ⟪ ↓X:=ℕ , X ⟫

Θᵈ, the dual of ↓X:=ℕ over Γ, has exterior ∅ and must rebuild Γ as its
interior.  It can rebuild X (concealed: its rep ℕ is Γ's knowledge), but for
the BLOCKED slot Y it has nothing to copy — the dual is syntactic and cannot
see Γ — so it emits a blocked reveal ↑Y:⋆, whose interior entry is Y abstract:

    Γ ⇈ (↓X:=ℕ) ⇈ Θᵈ  =  Y , X:=ℕ        ≠   Y:=𝔹 , X:=ℕ  =  Γ

W must now be retyped there, and its outer conceal ↓Y:=𝔹 needs Y:=𝔹 — FAILS.
The contractum is ill typed: preservation breaks on R.  (Nothing here is
exotic: Γ is the interior of two reveals; h is a sealed value weakened by a
later reveal Y — exactly what TyWrap does to the boundaries inside V; W's
conceal of Y is what the dual of a boundary revealing Y produces.)

A closed System F program that reaches this configuration (two blocked
knowledge slots instead of one):

    P  =  (ΛX. λf:(X→X). ΛY. λw:X. f w) [ℕ] (λn:ℕ. n) [𝔹] 3      : ℕ

    TyBeta   (λf. ΛY. λw. f w) ⟪ ↑X:=ℕ , (X→X)→∀Y.X→X ⟫ · (λn.n) [𝔹] 3
    Wrap     ((λf. ΛY. λw. f w) · f′) ⟪ ↑X:=ℕ , ∀Y.X→X ⟫ [𝔹] 3        f′ = (λn:ℕ.n) ⟪ ↓X:=ℕ , X→X ⟫
    Beta     (ΛY. λw:X. f′ w) ⟪ ↑X:=ℕ , ∀Y.X→X ⟫ [𝔹] 3
    TyWrap   ((ΛY. λw. f′ w) [Y′]) ⟪ ↑Y′:=𝔹 , ↑X:=ℕ , X→X ⟫ 3          interior Y′:=𝔹 , X:=ℕ
    TyBeta   ((λw:X. f′ w) ⟪ ↑Y:=Y′ , X→X ⟫) ⟪ ↑Y′:=𝔹 , ↑X:=ℕ , X→X ⟫ 3
    Wrap     (((λw. f′ w) ⟪ ↑Y:=Y′ , X→X ⟫) · W₁) ⟪ … , X ⟫              W₁ = 3 ⟪ ↓Y′:=𝔹 , ↓X:=ℕ , X ⟫
    Wrap     ((λw. f′ w) · W₂) ⟪ ↑Y:=Y′ , X ⟫ ⟪ … ⟫                     W₂ = W₁ ⟪ ↓Y:=Y′ , X ⟫
    Beta     (f′ · W₂) ⟪ ↑Y:=Y′ , X ⟫ ⟪ ↑Y′:=𝔹 , ↑X:=ℕ , X ⟫

  The last line is a Wrap redex at exterior Γ = Y:=Y′ , Y′:=𝔹 , X:=ℕ; f′'s
  boundary ↓X:=ℕ blocks Y and Y′ (both revealed), W₂ conceals both; the dual
  of ↓X:=ℕ is ↑Y:⋆ , ↑Y′:⋆ , ↑X:=ℕ with interior Y , Y′ , X:=ℕ ≠ Γ, and W₂'s
  two conceals fail to retype.  Note that BOTH TyWrap and TyBeta introduce a
  revealed variable above f′ (TyBeta turns the Λ-bound Y into Y:=Y′ without
  renaming), so W3 has to act in both rules.

The alternatives, on this example:

  (W1)  Add a premise to preservation, RunOK Γ M: "at every boundary in M the
        dual rebuilds the exterior" (here: false, so R is simply excluded).
        Works (the rework closed Wrap with it) but it is a companion predicate
        on terms — against the grounded-invariants law.

  (W2)  Make it an (env) premise: "every slot the boundary drops without
        concealing is ABSTRACT".  h is then ill typed (Y:=𝔹 is dropped and not
        concealed).  Grounded — but TyWrap creates h-like terms by weakening a
        sealed value under a new reveal, so TyWrap would fail preservation.

  (W3)  Never let a revealed slot be blocked: when a boundary with conceals is
        weakened by a NEW REVEALED variable, conceal that variable in it too,
        with the interior reading of its knowledge.  In the example h becomes

            h′ = (λx:ℕ. x) ⟪ ↓Y:=𝔹 , ↓X:=ℕ , X→X ⟫         Y concealed, not blocked

        the body is unchanged (interior still ∅, X→X[γ] = ℕ→ℕ), and the dual
        is ↑Y:=𝔹 , ↑X:=ℕ with interior Y:=𝔹 , X:=ℕ = Γ, so W retypes and
        Wrap preserves types.  Blocked slots are then always ABSTRACT
        (Λ-bound), (W2)'s condition holds by construction, and no premise is
        needed anywhere.  Cost: type-variable weakening through a boundary
        becomes knowledge-aware.  Only TyWrap introduces a revealed variable
        above existing boundaries, so the cleanest place is TyWrap's
        contractum: instead of a plain ⇑ᵀ V, weaken V by "↑Z:=A, concealing Z
        in every boundary of V that has a conceal" (named notation: nothing
        moves, the conceal ↓Z:=⟦A⟧ is inserted).

  (W4)  Stop dropping: Γ ⇈ Θ = Γ , X₁:⟦A₁⟧ , … , X_r:⟦A_r⟧ — concealed variables
        stay in scope (γ still resolves them to their reps) and no slot is ever
        blocked.  Then the dual has nothing to rebuild (its interior is a
        weakening of Γ by the reveal slots, which ⊢renameᵀ supplies), the
        scope premise of (env) becomes vacuous, Merge's context law is trivial,
        and the counterexample below (a reveal rep naming a blocked slot)
        cannot arise.  Cost: it gives up the TIGHT interior of §2 — the
        property that a sealed value's context contains only variables that
        existed when the seal was made.  Terms cannot mention later variables
        anyway (they predate them), so tightness restricts derivations, not
        terms; but it is the design intent behind "strong", so this is
        Jeremy's call, not a technicality.  (Under W4 the old design's Example
        8 reduct would even be well typed: the type argument Y is in scope.)

  Recommendation was W4; OVERRULED (Jeremy, 2026-09-04): tightness is wanted
  for its own sake — W4 withdrawn.  Design principle made explicit: almost no
  rule performs a type shift on a TERM, and that is the point — a shift
  forgets which type variables a term is not allowed to mention.  The only
  exception is TyWrap's ⇑ᵀ V, which Jeremy would also like to eliminate
  (open; candidate: introduce the new reveal at the DEEP end of the interior
  instead of the shallow end, so existing term indices are untouched and the
  shift lands on the boundary type B₀ instead of on V — to be probed).
  So Decision 4 is resolved by W3 (knowledge-preserving weakening), with the
  reveal-rep-names-a-blocked-variable case (¬⊢dualΘnʳ, e.g. TyWrap's own
  ↑Z:=Y with Y Λ-bound and blocked) still open under tightness.

### Decision 3 — tension with Decision 1 found by the Merge probe (needs a ruling)

notes/MergeProbe.agda (agda --safe clean) defines Θ₁ ⊕ Θ₂ and proves the
face laws in general, but exhibits a Merge redex with NO well-typed
contractum under the grounded premise as stated:

    Γ  =  X:=ℕ→ℕ
    inner  (λw:W. w) ⟪ ↑W:=ℕ , W→W ⟫            : ℕ→ℕ    in the interior of the outer boundary
    outer  ( … ) ⟪ ↓X:=ℕ→ℕ , X ⟫                : X       internal face of X is ℕ→ℕ  ✓

A merged single boundary must have external face X and internal face W→W:

    (λw:W. w) ⟪ ↑W:=ℕ , ↓X:=(W→W) , X ⟫

i.e. the conceal of X must carry the rep W→W — "X is W→W", true because W is
ℕ — but the grounded premise as written pins X's rep to the interior
READING of Γ's knowledge, ℕ→ℕ, syntactically.  So Decisions 1 and 3a
conflict: the premise compares knowledge without UNFOLDING the boundary's
own reveals, which is exactly what Zdancewic's Δ̄ (transitive closure) and
their (trans) rule allow.

Candidate fix — compare in the EXTERIOR instead of the interior (the
"reversal" form):

    (bwf-↓)  Γ ∋ Y:=A₀     A[ρΘ] = A₀     Ψ ⊢ A     Γ ∣ Ψ ⊢ Θ   ⟹  Γ ∣ Ψ ⊢ ↓Y:=A , Θ

  the conceal's rep A, read back out through the boundary (reveal variables
  ↦ their reps), must equal the exterior's knowledge.  On the examples:
  merged boundary above: (W→W)[W↦ℕ] = ℕ→ℕ = Γ's knowledge  ✓ accepted;
  bad: ℕ ≠ ∀Z.Z→Z  ✓ rejected;  bad₂: ` 0[Z↦ℕ] = ℕ ≠ P  ✓ rejected;
  dual conceal of a reveal Z:=A: A read back = A = the entry  ✓.
  Bonus: the external face commutes with renaming WITHOUT a scope restriction
  (BReduction.ρᵇ-comm / C-ext), unlike γ, so this premise should transport
  under ⊢renameᵀ more easily than the interior form.  Interior knowledge
  entries stay as in the Decision-1 refinement (X:⟦A⟧).
  Still open even with the fix: Merge's contractum interior differs from the
  nested one by UNFOLDING (probe: nested W:=Z vs merged W:=ℕ when Z:=ℕ), so
  Merge's preservation needs "retyping along unfolding", Zdancewic's Δ̄.

  Probe verdict (notes/ReversalProbe.agda, agda --safe clean, 2026-09-04):
  ADOPT.  Verbatim premise (over Δ; A₀ lifted from Δ ↓ X):

      Reversal Θ X A A₀ = outRead Θ A ≡ upRep X A₀
      bwf↓ʳ : Δ ∋ X := A₀ → Reversal Θ X A A₀ → Ψ ⊢ A → … → ⊢ᵇʳ (cnc X A ∷ Ξ)

  ✓ bad, bad₂ refuted;  ✓ the no-merge redex AND its merged boundary type;
  ✓ MergeProbe's ¬⊕-bwf pair now composes;  ✓ Example 8 T0…T5 with all steps;
  ✓ Wrap's dual conceals satisfy the premise (dual-read-back, general, for
  reps naming no blocked slot);  ✓ transports under ANY monotone renaming
  with no scope restriction (Reversal-ren) — the interior form's failure
  point;  ✓ W3's h′ types, its dual interior is Γ on the nose, W retypes.

  NEW COUNTEREXAMPLE (¬⊢dualΘnʳ): a reveal whose rep names a BLOCKED slot —
  Example 8's own run-time boundary ↑Z:=Y , ↓X:=ℕ over Y , X (Y blocked) —
  gets an abstract interior entry for Z under the Decision-1 refinement, so
  the dual's conceal ↓Z:=Y has no knowledge to match: Wrap is stuck on the
  T5 boundary.  W3 does not help (Y is Λ-bound, so nothing conceals it); W4
  removes the problem (Y is not dropped, Z:=Y is a legal entry).  Otherwise:
  forbid reveal reps that name blocked slots in (bwf-↑), which would reject
  T4/T5.
  Still open: Merge's contractum interior differs from the nested one by one
  UNFOLDING (probe: ⊕ pushes Θ₂'s conceal rep in as ℕ→ℕ, Merge needs W→W);
  preservation of Merge needs retyping along unfolding (Zdancewic's Δ̄).

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

Settled: TyWrap; Merge (3a).  Decision 1: restore the invariant in the REVERSAL
form (probe-verified).  Awaiting Jeremy: W3 vs W4 (Decision 4).  Then: Boundary.agda
rework (reversal premise + W3/W4) and re-run of every preservation case → Merge with
retyping-along-unfolding → depth-1 values → progress.
