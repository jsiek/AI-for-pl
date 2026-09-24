# Open design decisions (2026-09-03) — alternatives as definitions

Notation as in notes.md.  Each decision lists the alternatives as definitions
and the one consequence that matters.  Status: awaiting Jeremy's choice.

## Decision 1 — what licenses a conceal's representation?

Today:

    Γ ⇈ Θ    =  (Γ ↓ Y★) , X₁ , … , X_r            reveal variables enter as ABSTRACT
    (bwf-↓)  Γ ∋ Y      Ψ ⊢ A      Γ ∣ Ψ ⊢ Θ   ⟹  Γ ∣ Ψ ⊢ ↓Y:=A , Θ

Consequence — a closed well-typed value that no type-preserving rule can
eliminate (machine-checked, notes/old/BoundaryRulesProbe.agda §5a):

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
notes/old/GroundedProbe.agda (agda --safe clean) fixes the exact form:

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

  P  =  (ΛX. λf:(X→X). ΛY. λw:X. f w) [ℕ] (λn:ℕ. n) [𝔹] 3      : ℕ

  → TyBeta   (λf. ΛY. λw. f w) ⟪ ↑X:=ℕ , (X→X)→∀Y.X→X ⟫ · (λn.n) [𝔹] 3
  → Wrap     ((λf. ΛY. λw. f w) · f′) ⟪ ↑X:=ℕ , ∀Y.X→X ⟫ [𝔹] 3          f′ = (λn:ℕ.n) ⟪ ↓X:=ℕ , X→X ⟫
  → Beta     (ΛY. λw:X. f′ w) ⟪ ↑X:=ℕ , ∀Y.X→X ⟫ [𝔹] 3
  → TyWrap   ((ΛY. λw. f′ w) [Y′]) ⟪ ↑Y′:=𝔹 , ↑X:=ℕ , X→X ⟫ 3            interior Y′:=𝔹 , X:=ℕ
  → TyBeta   ((λw:X. f′ w) ⟪ ↑Y:=Y′ , X→X ⟫) ⟪ ↑Y′:=𝔹 , ↑X:=ℕ , X→X ⟫ 3
  → Wrap     (((λw. f′ w) ⟪ ↑Y:=Y′ , X→X ⟫) · W₁) ⟪ … , X ⟫                W₁ = 3 ⟪ ↓Y′:=𝔹 , ↓X:=ℕ , X ⟫
  → Wrap     ((λw. f′ w) · W₂) ⟪ ↑Y:=Y′ , X ⟫ ⟪ … ⟫                       W₂ = W₁ ⟪ ↓Y:=Y′ , X ⟫
  → Beta     ((λn:ℕ.n) ⟪ ↓X:=ℕ , X→X ⟫ · W₂) ⟪ ↑Y:=Y′ , X ⟫ ⟪ ↑Y′:=𝔹 , ↑X:=ℕ , X ⟫
  → Wrap     ((λn:ℕ.n) · (W₂ ⟪ ↑Y:⋆,↑Y′:⋆, ↑X:=ℕ , X ⟫)) 
                 ⟪ ↓X:=ℕ , X ⟫ ⟪ ↑Y:=Y′ , X ⟫ ⟪ ↑Y′:=𝔹 , ↑X:=ℕ , X ⟫

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

  Would Merge help instead? (Jeremy's question, 2026-09-04.)  No — checked on
  P: after the second TyBeta the two nested reveal boundaries DO merge
  (Θ₁ = ↑Y:=Y′ against Θ₂ = ↑Y′:=𝔹,↑X:=ℕ; nothing cancels; Y's rep unfolds
  to 𝔹), and the trace gets nicer — the argument then carries ONE dual
  boundary ↓Y:=𝔹,↓Y′:=𝔹,↓X:=ℕ with fully unfolded reps instead of the nested
  W₂ — but the failing step is unchanged: f′ = (λn:ℕ.n) ⟪ ↓X:=ℕ , X→X ⟫ sits
  UNDER the λ in λw:X. f′ w, so no wrapper-on-wrapper Merge ever reaches it,
  and its dual still rebuilds Y, Y′ as ⋆ where Γ has knowledge.  The blocked-
  knowledge configuration is created by TyBeta/TyWrap weakening boundaries
  INSIDE the body; only those rules are positioned to fix it, which is W3 —
  indeed W3's inserted ↓Z:=⟦A⟧ is exactly the entry a merge with the new
  reveal's dual would deliver if the λ were not in the way.

### Decision 4, continued — W3's traversal, the forcing example E, and the ambient dual (2026-09-04)

Jeremy: W3's ⇓ ("pass Y:=A down into V") is a term traversal — wants a
localized/incremental mechanism.  Forcing example (closed source; the gadget
is a TYPE abstraction between ΛY and the sealed value, evaluated under the Λ
by ξ-Λ before Y's TyWrap can fire):

    E  =  (ΛX. λf:(X→X). ΛY. (ΛZ. λz:X. f z) [ℕ]) [ℕ] · (λn:ℕ. n) · [𝔹] · 3

    TyBeta(X); Wrap; ξ TyBeta(Z)  [TyBeta needs W3 too: ↓X blocks Z ⇒ insert ↓Z:=ℕ]
      ⇒ ((ΛY. ((λz:X. ((λn:ℕ.n) ⟪ ↓Z:=ℕ , ↓X:=ℕ ⟫) z) ⟪ ↑Z:=ℕ ⟫)) ⟪ ↑X:=ℕ ⟫) [𝔹] · 3
    TyWrap(Y)+W3: the Λ-body is the REVEAL-ONLY wrapper ⟪↑Z:=ℕ⟫, which does not
    block Y ⇒ ⇓ must CROSS it (and λz, and an application) to insert ↓Y:=𝔹 at
    the sealed boundary.  Merge cannot pre-flatten (the ΛY sits between the two
    boundaries); iterating the (ΛZ.…)[ℕ] gadget makes the crossing depth
    unbounded; P already made the binder depth unbounded.

Where the knowledge is CONSUMED: only when the sealed boundary's own
Wrap/TyWrap builds its dual — and that redex sits under the ξ-⟪⟫ frames of
the boundaries that revealed Y, whose interiors are exactly the redex's
typing context.  Hence the incremental candidate:

  (A) AMBIENT DUAL / knowledge-indexed reduction:  Γ ⊢ M -→ M′  (mirroring
      the Δ-indexed typing);  ξ-⟪⟫ extends Γ with the boundary's interior,
      ξ-Λ with an abstract entry;  Wrap's dual is  dualᵇ Γ Θ  — for each slot
      Θ drops without concealing, copy Γ's OWN entry (knowledge if revealed,
      abstract if Λ-bound).  No ⇓, no insertion, no ⋆-with-lost-knowledge;
      every step local; grounded (it is the reduction judgment itself).
      By typing, Γ always suffices.

Star nuance: W3/(A) eliminate the HARMFUL stars (knowledge existed and was
lost).  A genuinely Λ-bound blocked slot still gets an abstract
re-introduction under either scheme — exact, since Γ's entry is abstract too;
write it as a rep-less reveal ↑Y rather than ↑Y:⋆.

Status: probe launched (contextual dual on E and P, compatibility with the
reversal-form premise).  W3-as-traversal kept as the fallback.

### Decision 4 — ambient dual probe verdict and the overnight install (2026-09-04, Jeremy asleep)

notes/old/AmbientDualProbe.agda (agda --safe clean).  Verdict: POSITIVE on the
candidate itself —
  ✓ P repaired with NO insertion anywhere (dualᴳ copies Y:=𝔹; rebuild = Γ on
    the nose; dualᵇ version refuted);
  ✓ E handled with ZERO traversal (both blocked knowledge entries copied at
    the moment of use; the sealed boundary stays the plain ↓X:=ℕ for its
    whole life);
  ✓ Λ-bound blocked slot: rep-less abstract reveal, exact rebuild (dualᵇ
    rebuilt bogus knowledge Y:=ℕ there — an exactness leak now fixed);
  ✓ reversal-premise compatibility reproduced in general.

Two residues, and the overnight scoping calls made under the mandate ("if
the probe comes back positive, install"):

  (R1) CHAINED KNOWLEDGE (probe §6b, reachable): Γ = Y:=Y′ , Y′:=𝔹 , X:=ℕ,
    Θ = ↓X:=ℕ — the copied entry for Y names Y′, which Θ also blocks, so the
    dual's reveal rep ` 0 is ill-formed under the PARALLEL reading of a
    boundary's reveal block.  Probe: it is exactly the right TELESCOPIC
    entry.  CALL: adopt the telescopic reading of the reveal block
    ((bwf-↑) reads each reveal rep over Γ extended by the DEEPER reveals of
    the same boundary; ρ becomes the corresponding fold) — this matches the
    repo's existing telescope convention for revealed entries
    (Context.agda: "the rep stored in rvld A is a type over its tail").
    Flagged for Jeremy's review; revertible.  [REVERTED 2026-09-04, see RULING below — landed on the branch.]

  (R2) A REVEAL REP NAMING A SLOT ITS OWN BOUNDARY BLOCKS (¬⊢dualᴳΘn;
    Θn = ↑Z:=Y , ↓X:=ℕ with Y Λ-bound and blocked — minted by TyWrap itself
    whenever a sealed polymorphic value is instantiated at an abstract
    variable, e.g. Example 8's f [Y]).  "Z is Y" is not expressible in an
    interior that dropped Y: Z's knowledge entry is abstract, so the dual's
    conceal of Z is unlicensed and Wrap's contractum does not type.  NOT
    resolved by the ambient dual (nor by W3).  CALL: do not invent a fix
    overnight; the Wrap preservation case for such boundaries is isolated
    as a `...Def` statement parameter with the obligation stated precisely,
    and the candidate resolutions recorded: (a) Γ-aware knowledge closure in
    ⟦·⟧ (resolve blocked variables of a reveal rep through Γ's knowledge
    when it exists — helps the revealed case, not the Λ-bound one);
    (b) a conceal premise licensed by the boundary's own reveal rep rather
    than the interior entry; (c) Merge-first normalization.  Jeremy rules.

Install scope (Track L/M): knowledge interiors ⟦A⟧ + reversal-form (bwf-↓)
+ rep-less abstract reveal entry + telescopic reveal block + Γ-indexed
reduction with dualᴳ; preservation and progress updated; Merge still NOT
landed (unfolding-transport open); ProgressDef keeps its parameters.

### Decision 3 — tension with Decision 1 found by the Merge probe (needs a ruling)

notes/old/MergeProbe.agda (agda --safe clean) defines Θ₁ ⊕ Θ₂ and proves the
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

  Probe verdict (notes/old/ReversalProbe.agda, agda --safe clean, 2026-09-04):
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

## MORNING AGENDA (2026-09-04, after the overnight install — commit acebd7f5)

The ambient dual is INSTALLED and `make check` is green.  Preservation lives
in `BPreservation.Impl (dual-rep) (dual-cnc) (dual-int)`; progress in
`Progress.Impl (rv-app) (rv-tapp) (nt-app) (nt-tapp)` (statements in
DualDef.agda / ProgressDef.agda).  Rulings wanted, in rough priority:

1. R2 (`DualCnc`): a reveal whose rep names a slot its own boundary blocks
   (Example 8's ↑Z:=Y , ↓X:=ℕ with Y Λ-bound).  Candidates: (a) Γ-aware
   knowledge closure in ⟦·⟧; (b) license the dual's conceal by the reveal's
   own rep; (c) Merge-first normalisation (may subsume R2 — see 6).
2. `DualRep` vs a `⊢ Δ` premise on preservation: the copied-knowledge rep's
   well-formedness is provable if preservation carries well-formedness of
   the ambient context (needs an intOf-closure lemma).  Accept parameter or
   add the premise?
3. Confirm/revert the telescopic reveal block (R1 call, provisional).
4. Confirm the `dfree` guard on ⟦·⟧ (a reveal whose interior reading is not
   a legal telescope entry contributes an abstract entry — some knowledge
   silently dropped; without the guard ⊢renameᵀ is false).
5. TyWrap's rep lift `renameᵗ (revs Θ +_) A` (type shift only) — forced by
   the telescope; confirm the rule as landed.
6. Next big piece order: Merge (discharges the four ProgressDef parameters;
   needs retyping-along-unfolding) vs resolving R2 first — note candidate
   (c) would make Merge subsume R2.
7. Cheap win, if wanted: revive Cancel — its old side condition ("conceal
   rep equals the enclosing reveal's rep") is now exactly what Reversal
   guarantees.

## RULING (Jeremy, 2026-09-04 morning) — telescopic (bwf-↑) REVERTED

"The representation type of a reveal entry is well-formed in the EXTERNAL
context, without any interference from the other entries in the boundary.
This is an important part of the simultaneous nature of the boundaries."

The R1 overnight call (telescopic reveal block) is therefore a mistake and
is reverted: (bwf-↑) reads each reveal rep over the plain exterior Γ, in
parallel; ρ returns to the parallel form (rep substituted as-is, not folded
through the other reveals).  Recorded as a design principle alongside
tightness and no-term-shifts: SIMULTANEITY = (i) a conceal's rep may mention
the boundary's reveal variables (the original Example-8 fix), and (ii) a
reveal's rep is read in the plain exterior, independent of its siblings.

Consequences (worked out before reverting):
  * TyWrap's rep lift `renameᵗ (revs Θ +_) A` was forced ONLY by the
    telescope — it disappears; the rule returns to
    `((Λ V) ⟪ Θ , ∀·B₀ ⟫)·[B,A] -→ V ⟪ ↑?:=A , shiftReps Θ , B₀ ⟫` with A
    unlifted.  Agenda items 3 and 5 are hereby closed.
  * ρᵇ-comm / C-ext revert to their simpler pre-fold proofs; the Reversal
    premise's read-back returns to the ReversalProbe-verified parallel form.
  * The one thing the telescope was buying — AmbientDualProbe §6b (chained
    knowledge: the dual's copied rep for Y is Y′, itself blocked) — is no
    longer expressible as a raw copy.  Under the parallel reading the dual's
    copied rep must be UNFOLDED through Γ's knowledge until it mentions only
    surviving variables (well-founded: Γ's entries are a telescope), which is
    the SAME knowledge-closure operator as candidate (a) for R2.  Until (a)
    is ruled on, §6b's obligation simply lives inside the DualRep parameter.
    One operator would then serve both: interior entries ⟦·⟧ and the dual's
    copied reps.

## CANDIDATE (a) SHARPENED TO (a′) — unfold AT ENTRY BIRTH (2026-09-04)

Worked example Pc (colored trace: the "Scope Trace of Pc" artifact) — the
smallest closed program minting CHAINED knowledge above a seal:

    Pc = (ΛX. λg:(X→X). ΛY. λx:X. ((ΛW. λu:X. g u) [Y]) x) [ℕ] · (λn:ℕ. n) · [𝔹] · 3

  By T5 the ambient context is  W:=Y , Y:=𝔹 , X:=ℕ  and the seal ↓X:=ℕ (in
  application position — Merge can never reach it) must eventually dualise,
  copying knowledge for W.  Raw copy of W:=Y is inexpressible under the
  parallel reveal reading (Y is itself dropped) → ↑W:⋆ → the argument's
  ↓W conceal is unlicensed → ✗.

  Fix, sharpened by the trace: unfold WHEN THE ENTRY IS BORN — ⟦·⟧ stores
  knowledge fully resolved through the ambient context (Zdancewic's Δ̄), so
  T5's entry is W:=𝔹, T6's dual conceal is minted as ↓W:=𝔹, and T7's copy
  is a plain closed type.  Unfolding lazily in the DUAL instead is wrong:
  the rebuilt entry (W:=𝔹) would mismatch conceals minted at the raw
  knowledge (↓W:=Y), forcing "retyping along unfolding" — Merge's open
  obligation — into Wrap.  At-birth unfolding keeps every conceal and copy
  in agreement by construction.

  (a′) preserves the rulings: simultaneity — the boundary SYNTAX ↑W:=Y is
  untouched, reps still read in the plain exterior; tightness — nothing new
  enters an interior, entries only become more resolved.  It is the same
  operator that fixes R2's Pn (there the BLOCKED Y unfolds; here the
  CHAINED Y does), so one mechanism closes both Pn and Pc, with the
  Λ-bound case abstract-as-today plus the no-abstract-value vacuity lemma.

  RULING (Jeremy, 2026-09-04): conditional go-ahead — "If the probe finds no
  mismatches, go ahead with (a′)."

  PROBE VERDICT (notes/UnfoldProbe.agda, agda --safe clean): MISMATCH FOUND
  — (a′) NOT INSTALLED, per the ruling.  Jeremy's worry is real, structural,
  and lands at exactly one consumer: THE DUAL'S CONCEAL-OF-A-REVEAL.

  The witness (¬DualCnc-a′), on Pc's own next step, exterior Y:=ℕ , X:=ℕ,
  boundary ΘW = ↑W:=Y:

      (a′) entry for W:  W:=ℕ  (unfolded)
      the dual's conceal is FORCED to carry the raw stored rep:  ↓W:=Y
        (simultaneity: cncOfRevs reads the reveal's stored rep, which stays
         raw — the same ruling that reverted the telescope)
      read-back Y  ≠  knowledge ℕ   →  the Wrap contractum does not type.

  All three placements of eager unfolding fail, each refl-checked:
    entry only          → ¬DualCnc-a′   (above)
    + dual's conceal    → ¬face-unfolded, ¬argY-retype (internal face and
                          the argument's retype break)
    + the stored rep    → ¬TyBeta-unfold-rep (TyBeta breaks; also rewrites
                          the TERM, against the no-term-shift spirit)
  and each is repaired by the same missing ingredient: EQUALITY UP TO
  UNFOLDING.  So (a′) does not eliminate retyping-along-unfolding — it
  relocates it from Merge into Wrap — and it additionally needs a
  strengthened ⊢renameᵀ hypothesis (¬UnfRen-hk).

  Provably impossible under uniform (a′) (the sites that are SAFE):
  route divergence (routes-agree — and note ¬cnc-W-raw: in the RAW regime
  chained knowledge can never be concealed at all), Merge's middle-type
  mismatch (⊕-int-a′ on the nose), ≼-retag (⊕-retag-a′ via idempotence),
  faces/scope/blocked slots bit-identical (barrier-* — the abstraction
  barrier is untouched by either regime).  Bonus: under normal-form
  knowledge the dfree guard is vacuous (rd-dfree).

  RECOMMENDATION → (a″): keep RAW entries (no information erased anywhere),
  and make the KNOWLEDGE COMPARISONS up-to-unfolding: bwf↓'s licensing
  compares Δ̄(read-back) with Δ̄(knowledge); the dual's copy is the one-step
  unfold of Γ's entry (differing from it by exactly unf-eq-entries); ≼ and
  the Merge middle type compare up to Δ̄.  This is Zdancewic's (eq) rule
  (compare at Δ̄) WITHOUT their eager retag (7).  On the probe's witnesses
  (a″) needs nothing at site 3 (DualCnc-raw is refl today), dissolves the
  ⊢renameᵀ strengthening, and repairs site 1 by unfolding only the copy.
  Cost: the licensing premise becomes 'up to Δ̄' — one congruence threaded
  through bwf↓/dual/retag — instead of syntactic equality.  Awaiting ruling.

## Would Merge solve Pc instead of (a′)?  (Jeremy's question, 2026-09-04)

No — checked on Pc's T6 argument (3 ⟪ ↓Y:=𝔹 , ↓X:=ℕ ⟫) ⟪ ↓W:=Y ⟫, which IS a
Merge redex.  ⊕ pushes the outer conceal's rep through the inner γ, so the
merge UNFOLDS correctly: 3 ⟪ ↓W:=𝔹 , ↓Y:=𝔹 , ↓X:=ℕ ⟫.  But:
  (1) the merge step itself is ill typed in the raw-knowledge world — the
      merged ↓W:=𝔹 is licensed against the ambient entry, which is still the
      raw W:=Y from T5 (read-back 𝔹 ≠ Y) — MergeProbe's retyping-along-
      unfolding gap, live on this trace;
  (2) even granting it, T7 still fails: the seal's dual copies the AMBIENT
      entry (raw W:=Y → ↑W:⋆), which no restructuring of the argument can
      reach.
Under (a′) both vanish: entries are born unfolded (W:=𝔹 from T5′), the
argument's conceal is minted unfolded, Merge's output agrees with the
context and becomes type-preserving.  Conclusion: MERGE PRESUPPOSES (a′),
not the reverse — Zdancewic's structure exactly (their merge (8) is sound
only over Δ̄-resolved annotations, maintained eagerly by retag (7); (a′) is
our rule (7)).  Order of work: (a′) → Merge.

## (a″) PROBE VERDICT — SURVIVED (notes/UpToProbe.agda, 2026-09-04)

All seven sites SAFE, with one requirement and one residual:
  ✓ the (a′) killer reversed (DualCnc≈-Pc: raw conceal licenses by refl);
  ✓ Pc end-to-end (the chained copy unfolds, the argument retypes: ≼≈);
  ✓ Pn/R2 — pure (a″) is NOT enough (¬DualCnc≈-Pn-raw: bwf↓'s ∋:= lookup
    is a lookup, no congruence relaxes it); the HYBRID entry ⟦·⟧ᴴ is
    REQUIRED and fixes it (raw entry where expressible, retried at
    unfoldᵉ Γ A where not, abstract only when both fail).  Bonus finding:
    with the hybrid, the dual's read-back at Pn resolves through the dual's
    own copied reveal and the licensing premise holds SYNTACTICALLY;
  ✓ bad/bad₂ stay refuted under ≈; near-bad-by-a-different-route rightly
    admitted; genuinely different knowledge rejected;
  ✓ renaming: better than (a′) — the entrywise strengthening dissolves
    (UnfRen≈-abst is refl).  RESIDUAL: the hybrid entry commutes with
    renaming only up to ≼≈ (¬⟦⟧ᴴ-ren / ⟦⟧ᴴ-ren≼≈) — one ⊢retag≈ inside
    ⊢renameᵀ's (env) case;
  ✓ Merge's retyping-along-unfolding collapses into ≼≈ (both directions);
  ✓ the raw/unfolded mixture is coherent (mix-≼≈, idempotence, two-routes,
    abstraction barrier bit-identical).
  Λ-bound blocked case still stuck as expected → the no-abstract-value
  vacuity lemma is still the closing piece (bases proven, chain step a
  commented conjecture).

Design summary (before/after, home relations) presented to Jeremy for
sign-off; install pending his approval.
## E★ — the vacuity lemma is insufficient; the rep-less conceal ↓·:⋆ (2026-09-04)

    E★ = (ΛX. λf:(∀Z. ℕ→ℕ). ΛY. (f [Y]) 5) [ℕ] · (ΛZ. λn:ℕ. n)   : ∀Y. ℕ

    TyBeta(X); Wrap  ⇒  (ΛY. (((ΛZ. λn:ℕ. n) ⟪ ↓X:=ℕ ⟫) [Y]) 5) ⟪ ↑X:=ℕ ⟫
    ξ TyWrap(Z)      ⇒  (ΛY. ((λn:ℕ. n) ⟪ ↑Z:=Y , ↓X:=ℕ ⟫) 5) ⟪ ↑X:=ℕ ⟫
      Y is Λ-bound AND blocked: Z's entry is abstract under raw, hybrid, and
      unfolding alike — nothing to unfold.
    ξ Wrap on (…) · 5  ⇒  STUCK: the dual must conceal Z, no knowledge exists,
      and the argument is 5 : ℕ — so no-abstract-value says NOTHING here
      (the boundary's type ℕ→ℕ never mentions Z).

  Fix proposed to Jeremy (trace artifact "Scope Trace of E★"): the REP-LESS
  CONCEAL ↓Z:⋆, mirror of ↑Y:⋆ — re-hide the variable claiming nothing,
  licensed by nothing, slot blocked in baseS so no boundary type may depend
  on it; the dual emits it exactly when a reveal's knowledge is
  inexpressible and un-unfoldable.  Completed case split for the dual's
  conceal-of-a-reveal:
    knowledge expressible raw        → as today
    expressible after unfolding      → the (a″) copy
    inexpressible, named by the type → vacuous (no-abstract-value: no redex)
    inexpressible, not named         → ↓·:⋆
  Probe in flight (notes/StarConcealProbe.agda): E★ end-to-end before/after,
  bad-via-⋆ refutation, whether no-abstract-value stays load-bearing, dual-of-
  dual/renaming/retag behaviour of cnc⋆.

  RULING (Jeremy, 2026-09-04): conditional — "if the probe passes, install
  a″ with the star conceal."  His observation, recorded as the design's
  symmetry principle: "I suppose we should have expected to need a rep-less
  conceal because we already have a rep-less reveal."  Formal version: the
  entry syntax must be CLOSED UNDER DUALIZATION — the dual maps reveals to
  conceals and back, ↑Y:⋆ was forced by the dual re-introducing Λ-bound
  slots, so its dual image ↓Y:⋆ was inevitable; E★ is merely the program
  that makes the missing image observable.

## STAR-CONCEAL PROBE VERDICT — sound and required, NOT sufficient (2026-09-04)

notes/StarConcealProbe.agda (agda --safe clean, 1531 lines).  Per the
conditional mandate, (a″)+↓·:⋆ is NOT installed: a new counterexample.

What PASSED:
  ✓ E★ verified end-to-end (two index corrections: the dual's conceal is
    cnc 1 under the ΛY, and the dual's entry order is ↑Y:⋆ , ↑X:=ℕ , ↓Z);
    the fix types E★'s contractum, exact rebuild, final value at ∀Y.ℕ;
  ✓ cnc⋆ soundness clean: bad-via-⋆ refuted (the scope premise forbids a
    boundary type naming a ⋆-slot), no new route to variable-typed values,
    faces unchanged, renaming/retag trivial;
  ✓ closure under dualization confirmed (dual-of-dual round-trips; a
    cnc⋆-dropped slot duals to rvl⋆ when abstract, to the exterior's own
    knowledge when revealed);
  ✓ cnc⋆ is REQUIRED regardless of E★: today's dual of a boundary containing
    rvl⋆ mints cnc j ℕ, which is ALREADY unlicensable (¬DualCnc-rvl⋆) and
    reachable — E★'s own dual contains a rvl⋆;
  ✓ the DualCnc case split: raw and unfoldable knowledge are the standing
    (a″) obligations; the inexpressible-and-unneeded case is now a THEOREM
    (cnc⋆-licensed); no-abstract-value is no longer needed for DualCnc.

What FAILED — the new counterexample E★′ (both regimes), full trace:

    E★′ = (ΛX. λf:(∀Z.(Z→ℕ)→(Z→ℕ)). ΛY. (f [Y]) (λy:Y. 5)) [ℕ]
            · (ΛZ. λg:(Z→ℕ). λz:Z. g z)      : ∀Y. Y→ℕ

    TyBeta(X)  ((λf:(∀Z.(Z→ℕ)→(Z→ℕ)). ΛY. (f [Y]) (λy:Y. 5)) ⟪ ↑X:=ℕ ⟫)
                 · (ΛZ. λg:(Z→ℕ). λz:Z. g z)
    Wrap       (ΛY. (((ΛZ. λg:(Z→ℕ). λz:Z. g z) ⟪ ↓X:=ℕ ⟫) [Y]) (λy:Y. 5))
                 ⟪ ↑X:=ℕ ⟫
    ξ TyWrap(Z)  (ΛY. ((λg:(Z→ℕ). λz:Z. g z) ⟪ ↑Z:=Y , ↓X:=ℕ ⟫) (λy:Y. 5))
                 ⟪ ↑X:=ℕ ⟫
       — Y Λ-bound AND blocked: Z's entry abstract, nothing to unfold; the
         boundary's type (Z→ℕ)→(Z→ℕ) NAMES Z.
    ξ Wrap     STUCK.  The argument λy:Y.5 is a VALUE at the arrow type Y→ℕ
       (the external face of the domain Z→ℕ), so no-abstract-value is silent.
       Attempt 1, rep-keeping dual  ↓Z:=Y , ↑Y:⋆ , ↑X:=ℕ : both faces are
       exactly right (face-int-E★′, face-ext-E★′, sc-live-E★′) — only
       bwf↓'s knowledge lookup fails (¬⊢T4′).
       Attempt 2, star dual  ↓Z:⋆ , ↑Y:⋆ , ↑X:=ℕ : licensed by nothing, but
       the re-hidden slot is blk and the dual cannot express its own
       boundary type Z→ℕ (¬Scoped-⋆-E★′, ¬⊢T4′⋆).

  Same shape as E★, but B₁ = Z→ℕ NAMES Z, and the argument λy:Y.5 is a
  VALUE at the arrow type Y→ℕ — reachable, and vacuity is silent.  At the
  Wrap: if the dual conceals with the rep kept (↓Z:=Y), then both faces are
  already EXACTLY right (face-int-E★′, face-ext-E★′, sc-live-E★′) and the
  ONLY defect is bwf↓'s knowledge lookup (Z's entry is abstract); if the
  dual conceals with ↓Z:⋆ instead, then the re-hidden slot is blk and the
  dual cannot express its own boundary type Z→ℕ (¬Scoped-⋆-E★′).  So cnc⋆
  trades a boundary failure for a scope failure exactly when the type
  mentions the unknowable reveal.

Probe's recommendation: candidate (b) for rep-carrying reveals — a
DUAL-ONLY conceal that KEEPS the rep and is licensed by the reveal it
cancels (Zdancewic Lemma A.2, Reversal) rather than by interior knowledge —
with cnc⋆ retained for duals of rvl⋆.

RULING (Jeremy, 2026-09-04): probe the candidate premises for (b); a full
design description of (b) to follow the probe.

(b)-PROBE VERDICT (notes/DualLicenseProbe.agda, agda --safe clean):
(b3)-SOUND WINS; (b1) and (b2) refuted; the NAIVE (b3) was itself unsound
(an adversary reuses a planted x-entry in a non-dual boundary, ⊢3n-adv) and
is repaired by the load-bearing "claims nothing" premise.  Full design
description with example, before/after rules and homes, the soundness
story, the uncovered obligations, and the one open renaming lemma:
notes/DualLicenseDesign.md.  Awaiting Jeremy's sign-off on that design
(and on §5's choice (i) vs (ii)) before the combined install.  In flight
(notes/DualLicenseProbe.agda), three candidates against the E★′/E★/Pn/bad/
bad₂/near-bad gauntlet:
  (b1) read-back identity (concealing-then-revealing is the identity on the
       slot's face) — expected to produce garbage past rep-less reveals;
  (b2) the face laws themselves as the bwf↓ premise — expected to be
       whole-boundary, not per-entry, and possibly circular;
  (b3) an exterior-read knowledge entry `xrvld A` in the interior (minted by
       ⟦·⟧ when a rep-carrying reveal's knowledge is neither expressible nor
       unfoldable; consumed ONLY by a new bwf↓ clause with syntactic rep
       equality — the homes align: the x-entry's rep and a dual conceal's
       rep both live over the same context).  Also probed: whether (b3)
       subsumes the (a″) hybrid at Pn, and the structural argument ruling
       out (b4) (a co-boundary-parameterized judgment: the contractum must
       be typed by plain env).
## D1 PROBE VERDICT — root cause pinned; A SOUNDNESS HOLE in the landed license; the SkelEq repair (2026-09-04)

notes/D1Probe.agda (agda --safe clean).  Answers to Jeremy's two questions:

ROOT CAUSE — CONFIRMED, one line: x-entry reps rename by the EXTERIOR ρ
(entRen₂), conceal reps by the induced INTERIOR renaming (renᴮ).  The
divergence class is exactly "ρ differs from the induced interior renaming
on the rep's support" — and it contains EVERY weakening, because an x-entry
forces a conceal, and a conceal absorbs suc outright.  A renaming inserting
deeper than cmax leaves the comparison intact, so the class is proper.
CORRECTION: DualLicenseDesign §2's "the homes align" was false — the two
reps are identified only through the rebuild.  The rebuild-relative
comparison (Jeremy's re-alignment instinct) HOLDS AT BIRTH — xrep-stored is
the x-analogue of cancel-agree, the two reps are syntactically equal at
every dual's birth — but is NOT renaming-stable, fatally: after an absorbed
weakening the rebuild has fewer slots than the ambient context (¬rebuild-ren
— ≼≈ is FALSE, not unproven).

PROPAGATION — WORSE THAN FEARED.  CORRECTION to this file's earlier claim
"the comparison never was the load-bearing part": REFUTED.  starOnly is
vacuously true of CLOSED types (starOnly Θ d ℕ = true), so the landed
(bwf-↓x) licenses  ↓Z:=ℕ  at an x-slot — asserting "Z is ℕ" with no
justification.  Machine-checked: ⊢Tg exports 7 at the Λ-bound Y through
E★′'s own x-slot; ⊢Tbad is bad's configuration one indirection away,
reached via the ⊢retag≈ transport TyBeta performs.  The dropped comparison
is exactly what refuses it (would-refute-≡/-≈).  The same hole was in the
original absOnly form.  Once depth-1 values land, ⊢Tg's term becomes a
stuck Merge redex — a progress failure.

THE REPAIR — SkelEq (found by the probe): compare the conceal's rep with
the recorded one by SKELETON (constructor tree with variable positions
identified) — stable under arbitrary independent renamings with NO
hypotheses (skel-ren), so it survives exactly the drift that killed ≡ and
≈Δ̄, while still refusing ↓Z:=ℕ against a recorded variable (closing the
hole) and the ⊢3n-adv adversary, and admitting the whole gauntlet.

    (bwf-↓x)   Γ ∋ X:=ˣA′     starOnly Θ 0 A ≡ true     SkelEq A A′
               Ψ ⊢ A
               ──────────────────────────────────────────────────
               Γ ∣ Ψ ⊢ ↓X:=A , Θ

Cost: ⊢renameᵀ's hx hypothesis strengthens to SkelX (weaker than the
rejected XRen; both live call sites already satisfy it — SkelX-suc,
SkelX-mv).  Bonus: SkelEq + xrep-stored discharge MERGE'S cancel-agree for
x-pairs, so the deleting cancel keeps its justification.

MERGE VERDICTS: the TOPLAS three-agent adversary CLEARS our deleting cancel
(their term is conceal-of-conceal — our cancel never fires; the appended
merge types, the middle authority discharging Reversal through ≈Δ̄; the
variant where cancel DOES fire survives via the agreed rep).  APPEND-ONLY
IS REFUTED FOR US (¬bwf-append: exterior-relative conceal indices make the
appended boundary inadmissible — theirs works only over a global
namespace); the faces-agree strip is unsound except at Θ = ∅ (= Drop∅).
Towers collapse via DELETING merge + strip at a closed B₀ — which needs
cancel-agree anyway.  So the ranked recommendation is unambiguous:

  (i) REPAIR (bwf-↓x) WITH SkelEq — RULED BY JEREMY AND LANDED (commit
      "the SkelEq repair").  ⊢Tg/⊢Tbad are now permanent refutations in
      Boundary.agda; ¬⊢adv reconfirmed; CncLic's x-disjunct carries the
      SkelEq conjunct at zero residual cost (dual-cnc-skel discharges it
      at every dual's birth via xrep-stored); D1 is CLOSED — the landed
      license now reads: x-lookup + starOnly + SkelEq + Ψ ⊢ A.
  (ii)/(iii) accepting D1, with either cancel flavor: refuted or dominated.

## DESIGN LAW, restated by Jeremy via the trace coloring (2026-09-04)

"Another way to think about the tightness property that I'm going for is
that THE COLOR OF A NON-BOUNDARY TERM SHOULD NEVER CHANGE DURING REDUCTION."

I.e. reduction never changes which type variables a non-boundary subterm
can see — scope regions are preserved; only boundary syntax moves.  Two
instances already in the calculus: TyWrap consumes a Λ but its body keeps
its color (the binder's slot becomes the boundary's reveal slot — same
scope, new binder site); Wrap moves an argument inside a dual whose
interior REBUILDS exactly the context the argument was colored by — the
argument keeps its color, which is the DualInt law stated visually.  A
candidate rule that recolors a non-boundary term is thereby suspect on
sight.  Recorded next to tightness / no-term-shifts / simultaneity /
closure-under-dualization.

## THE X-LICENSE INSTALL — LANDED (e07e8863), WITH THREE DEVIATIONS (2026-09-04 night)

Gates green (cold make check + notes/InstallGauntlet.agda, worktree and main
tree).  E★′ closed through (bwf-↓x); E★ needs no cnc⋆ under the x-license;
bad/bad₂/far-bad refuted, near-bad admitted, dual-of-dual exact.  Honest
scorecard: preservation did NOT become unconditional — three parameters
remain, materially smaller (DualRep≈ wants ⊢ Δ; DualCnc≈ is a per-reveal
disjunction whose residue is exactly the Pn shape; DualInt≈ the rebuild law).

Deviations from the ruled design, all machine-checked, FOR JEREMY'S REVIEW:

  (D1) (bwf-↓x) carries NO rep comparison — neither ≡ nor ≈.  Ruling (ii)
       does not survive ⊢renameᵀ at this clause: under a weakening the
       x-entry's rep moves by the exterior renaming while renᴮ freezes the
       conceal's stored rep, and the two end a genuinely-abstract slot
       apart even up to unfolding (¬x-rep-match-ren≈, InstallGauntlet §7b).
       The license is: the x-LOOKUP (the slot is x-marked) + the
       claims-nothing premise + Ψ ⊢ A.  The whole soundness gauntlet turns
       on claims-nothing (the ⊢3n-adv rep MATCHES on both sides — the
       comparison never was the load-bearing part, confirming (ii)'s
       orthogonality expectation from the wrong direction).
  (D2) Claims-nothing is the BOUNDARY-relative `starOnly Θ` ("the rep names
       only rep-less reveal slots of Θ"), not the interior-relative absOnly:
       the interior form is anti-monotone in knowledge and dies at the
       abst↦rvld retag TyBeta/TyWrap perform.  Same verdicts on the whole
       gauntlet.
  (D3) The ambient unfold retry in ⟦·⟧ is NOT installed: an ambient-
       dependent interior breaks both required transports (renaming:
       ¬UnfRen-hk; knowledge-monotonicity: a further-resolved rep may name
       a blocked slot).  Price: Pn's dual conceal is unlicensed again and
       is now EXACTLY the DualCnc≈ residue.  The congruence ≈Δ̄ itself,
       Reversal≈, ≼≈, and the dual's second-chance unfolded copy ARE
       installed and carry Pc.

Open questions this leaves (beyond the roadmap): whether to accept (D1)'s
comparison-free license as final (the rep is still constrained by starOnly
+ Ψ ⊢ A, and the faces use it; but "the conceal repeats the recorded rep"
is now unchecked — is that acceptable, or should the x-entry itself be
REDEFINED to be renaming-stable so a comparison can return?), and whether
Pn's residue is acceptable pending Merge (Merge-first unfolds Pn's chain in
the cases that reach eliminations — to check at the Merge landing).

## THE TOPLAS FOLLOW-ON (notes/SyntacticTypeAbstraction.md, 2026-09-04)

Jeremy pushed p1037-grossman.pdf ("Syntactic Type Abstraction", the journal
version, WITH a System F treatment).  Digest highlights, as they bear on our
open items:

  * OUR E★′-CLASS CONFIGURATIONS ARE UNREACHABLE FOR THEM — dissolved
    upstream by a global type-variable namespace plus eager retag, not
    solved.  Reconstructing E★′ inside their own encoding yields exactly an
    ordinary δ-entry `Z=Y` with Y Λ-bound and in nobody's domain — i.e. our
    `Z:=ˣY` — compatible precisely because Y is nobody's key.  Independent
    support for (bwf-↓x) + the "claims nothing" premise; ruling (ii) intact
    (the paper has no transport hypotheses anywhere — substitution is a
    judgment-level lemma).
  * (a″) VALIDATED WITH A WARNING: they keep eager retag [7] AND (eq)-at-Δ̄;
    p. 1049 notes relaxing eagerness needs "additional proof-normalization
    arguments" — our ≈Δ̄ congruence is exactly that normalization.
  * MERGE: their [8] APPENDS AND NEVER DELETES; a three-agent counterexample
    (p. 1048–49: δ_i(t)=int, δ_j(s)=t, δ_k=⊥) shows dropping authority
    breaks abstraction.  Our ⊕ deletes matched ↑X/↓X pairs (cancel).  Before
    Merge lands: build the cancel adversary on their example; if cancel
    fails, fall back to append-only merge + Drop∅ (which we adopted anyway).
  * B₂′ ANSWERED: keep the OUTER boundary type; the ⊕ obligation is "the
    middle type is abstract to the middle boundary" ([trans] + Idempotence
    is their entire preservation case for merge).
  * PRESERVATION STRENGTHENING to adopt: the outgoing context REFINES the
    incoming one (their Def. 5.4 / Lemma 5.5) — a grounded invariant our
    statement does not yet carry.
  * Depth-1 values + canon-var-conceal are literally their Lemma 3.2 third
    clause; under polymorphism their VALUE-HOOD IS DYNAMIC (p. 1074) —
    expect our Value to become Δ-indexed at the depth-1 step.

## AGENDA ITEM 1 IN DETAIL — R2 / DualCnc, by example (2026-09-04)

The program (ordinary System F; the essential move is instantiating an
imported polymorphic value AT AN ABSTRACT VARIABLE, f [Y] — Example 8's core):

    Pn = (ΛX. λf:(∀Z.Z→Z). ΛY. λy:Y. f [Y] y) [ℕ] · (ΛZ. λz:Z. z) · [𝔹] · true   : 𝔹

    TyBeta(X)  ((λf:(∀Z.Z→Z). ΛY. λy:Y. f [Y] y) ⟪ ↑X:=ℕ ⟫) · (ΛZ. λz:Z. z)  [𝔹] · true
    Wrap       ((ΛY. λy:Y. (((ΛZ. λz:Z. z) ⟪ ↓X:=ℕ ⟫) [Y]) y) ⟪ ↑X:=ℕ ⟫)  [𝔹] · true
    TyWrap(Y)  ((λy:Y. (((ΛZ. λz:Z. z) ⟪ ↓X:=ℕ ⟫) [Y]) y) ⟪ ↑Y:=𝔹 , ↑X:=ℕ ⟫) · true
    Wrap       ((((ΛZ. λz:Z. z) ⟪ ↓X:=ℕ ⟫) [Y]) · (true ⟪ ↓Y:=𝔹 , ↓X:=ℕ ⟫)) ⟪ ↑Y:=𝔹 , ↑X:=ℕ ⟫
    ξ TyWrap   (((λz:Z. z) ⟪ ↑Z:=Y , ↓X:=ℕ ⟫) · (true ⟪ ↓Y:=𝔹 , ↓X:=ℕ ⟫)) ⟪ ↑Y:=𝔹 , ↑X:=ℕ ⟫

  All well typed so far.  The inner TyWrap minted, at exterior Γn = Y:=𝔹 , X:=ℕ:

    Θn = ↑Z:=Y , ↓X:=ℕ          interior:  Z ABSTRACT

  Z's entry should be the knowledge "Z is Y", but ⟦·⟧ reads Θn ALONE, and in
  Θn's interior Y is BLOCKED (↓X drops everything up to X, including the
  shallower Y): no interior reading exists, so the entry falls back to
  abstract.  "Z is Y" — and via Γn, "Z is 𝔹" — is known ambiently, recorded
  nowhere in Θn.

  The failing step: the last Wrap's dual must CONCEAL Z (duals turn reveals
  into conceals), and a conceal ↓Z:=A₀ is licensed only by interior knowledge
  Ψn ∋ Z := A₀ — which does not exist.  Contractum untypable.  That is
  DualCnc's counterexample; the dual's REVEAL block is fine (↑Y:=𝔹 copied
  from Γn, ↑X:=ℕ from the conceal) — only the conceal-of-a-reveal side is
  stuck.

  Candidates, on Pn:

  (a) KNOWLEDGE CLOSURE IN ⟦·⟧ — compute the entry with the ambient Γ: when
      a reveal's rep names a blocked variable, resolve it through Γ's
      knowledge first.  At the ξ TyWrap step, ⟦Y⟧ under Γn unfolds Y:=𝔹, so
      Z's entry is Z:=𝔹; the dual's ↓Z:=𝔹 is licensed and the rebuild is
      exact.  FIXES Pn.  The residual case — same shape with Y still
      Λ-bound — is conjectured VACUOUS: the failing Wrap needs a VALUE of
      type Y, and no value inhabits an abstract variable's type (a value at
      variable type is a wrapper chain that can only terminate in a conceal,
      and a conceal of an abstract variable is unlicensed by the restored
      invariant).  New lemma to prove: no-abstract-value.  If it holds, (a)
      closes DualCnc completely.  Cost: intOf consults Γ's entries (it
      already takes Γ; renaming transport rides ⊢renameᵀ's ∋:= hypothesis).
      bad/bad₂ unaffected (their failure is the conceal check).

  (b) SELF-JUSTIFYING DUAL CONCEALS — a marked entry ↓Z:≈A minted only by
      dualᴳ, licensed by the read-back law against the reveal it cancels
      (A = the reveal's own rep; Zdancewic's Reversal lemma made syntactic).
      On Pn: ↓Z:≈Y, Y in scope in the dual's interior (= Γn).  Spot-checks:
      read-back alone still refutes bad (ℕ ≠ ∀Z.Z→Z) and bad₂.  Cost: a
      fourth entry form whose typing reaches across to ANOTHER boundary —
      the kind of non-local premise the design has avoided.  Probe first.

  (c) MERGE-FIRST — REFUTED AS A COMPLETE SOLUTION BY Pn.  Merge fuses only
      adjacent wrappers.  In the E8-shape (sealed value = the Λ-body) TyWrap
      creates the adjacency and Merge dissolves Θn (the cancel unfolds
      ↑Z:=Y against ↑Y:=𝔹 into ↑Z:=𝔹).  In Pn the sealed value sits in
      APPLICATION position inside the boundary — never wrapper-on-wrapper —
      and Merge cannot reach it before the failing Wrap.  Shape-dependent;
      not an R2 fix on its own.

  RECOMMENDATION: (a) + the no-abstract-value lemma, probed before install.
  (b) is the fallback if the vacuity lemma fails; (c) stays desirable for
  Decision 3 but does not resolve R2.

## Decision 2 — a boundary meets a type application

Both well typed on every step of Example 8 (notes/old/Example8Trace.agda).

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

### Decision 2 — REVISED to TyWrap′ (Jeremy, 2026-09-04)

The 2026-09-03 objection to TyWrap′ (partial: the body must be syntactically
Λ) dissolves under Decision 3: with depth-1 values a wrapper-bodied wrapper is
a Merge redex, and after merging, a value wrapped at a ∀-shaped B₀ has a Λ
body by canonical forms.  And TyWrap′ has NO ⇑ᵀ on the term — the shift in
TyWrap existed only because it declined to consume the Λ (the Λ-binder's slot
IS the new reveal slot) — so the switch also discharges the no-term-shift
principle's one exception.  Ruling: switch to TyWrap′; the notes.md rule name
stays TyWrap (its definition changes to the direct-combine shape):

    (TyWrap)  ((ΛY.V) ⟪ Θ , ∀Y.B₀ ⟫) @B[A]   -→   V ⟪ ↑Y:=A , Θ , B₀ ⟫

  (conceal reps still shift — types, not terms).  Progress at a ∀-faced
  wrapper: Λ body → TyWrap; wrapper body → Merge (a ProgressDef parameter
  until Merge lands).  W3 is still needed and now acts in TyBeta and TyWrap
  (both upgrade a Λ-bound slot above inner boundaries to revealed).
  Follow-up ruling (Jeremy, 2026-09-04, same day): switch Wrap too, from the
  lazy/float form to PUSH-THROUGH-THE-LAMBDA, symmetric to TyWrap′ — consume
  the ƛ and β-substitute the dual-wrapped argument in one step:

    (Wrap)  ((λx:B₁′. N) ⟪ Θ , B₁→B₂ ⟫) · W  -→  N[x := W ⟪ Θᵈ , B₁ ⟫] ⟪ Θ , B₂ ⟫

  (this is PLAN §4's original sketch, before the memo generalised it to the
  total float form).  The dual Θᵈ and its face laws are unchanged, so
  Decision 4 / W3 is unaffected.  Totality: a wrapper-bodied wrapper at a
  ⇒ face waits for Merge, exactly as at a ∀ face — progress carries two
  further ProgressDef parameters (NestedApp, NestedTApp) until Merge lands.
  No term shift anywhere: _[_]ᵐ substitutes term variables only.

### Decision 3, addendum (Jeremy, 2026-09-04): Drop∅ ships WITH Merge

    (Drop∅)   V ⟪ ∅ , B₀ ⟫   -→   V          both faces are B₀; long proven safe

Merge's cancel clause empties matched boundaries (e.g. the cancel pair
(7 ⟪ ↓X:=ℕ ⟫) ⟪ ↑X:=ℕ ⟫ merges to 7 ⟪ ∅ ⟫), so without Drop∅ towers
collapse to a vacuous wrapper rather than the bare value.  Adopt both in
one landing: rule + example + preservation + progress cases each, per the
§1 Method.  Note Drop∅ finally becomes REACHABLE at that point (today no
rule mints an empty boundary).

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

Settled: TyWrap′ and push-through Wrap (both revised 2026-09-04); Merge (3a).  Decision 1: restore the invariant in the REVERSAL
form (probe-verified).  Awaiting Jeremy: W3 vs W4 (Decision 4).  Then: Boundary.agda
rework (reversal premise + W3/W4) and re-run of every preservation case → Merge with
retyping-along-unfolding → depth-1 values → progress.

## THE MERGE + DROP∅ LANDING — LANDED, ONE OPEN RULING (2026-09-04 night)

Gates green cold (`make -C strong check` + InstallGauntlet `--safe`). The rules as landed
(`BReduction.agda`):

```agda
Merge : Value V
      → MergeOK Δ Θ₁ Θ₂ B₁ B₂
      → Δ ⊢ (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫ -→ V ⟪ Θ₁ ⊕ Θ₂ , mrgB Θ₁ Θ₂ B₁ ⟫

Drop∅ : Value V
      → Δ ⊢ V ⟪ [] , B₀ ⟫ -→ V
```

`Θ₁ ⊕ Θ₂ = mapL Θ₂ Θ₁ ++ mapR Θ₁ 0 Θ₂`: Θ₁'s reveals stay, reps pushed out through Θ₂;
a Θ₁-conceal (or `cnc⋆`) of a Θ₂-reveal slot CANCELS both (the clause is on the index, not
the flavour — sound because only a `rvl`/`cnc` pair transports a rep, and that pair is
`cancel-agree`); surviving conceals re-index. Both preservation cases are FULLY PROVEN, no
new parameters: `⊕-γ` (the internal face composes on the nose), `cancel-agree` re-derived
as a theorem on the live core (ordinary pairs; x-pairs are `xrep-stored`/`dual-cnc-skel`),
body transport = `⊢retag≈` along `≼≈` — so "retyping-along-unfolding = ≼≈" is now USED,
not just probed. Worked examples in gauntlet §9: the cancel pair
`(7 ⟪ ↓X:=ℕ ⟫) ⟪ ↑X:=ℕ ⟫ → 7 ⟪ ∅ ⟫ → 7`, E★′'s continuation tower (the reachable x-pair
cancel — exact, `⊢merged-★`), Example 3's tower merged twice, and the TOPLAS three-agent
shape (`⊢merged-ag` — types with both authorities kept, NO abstraction breach).

DEVIATION (grounded, not a parameter): `Merge` carries `MergeOK` as a rule premise —
`cmax Θ₁ ≤ revs Θ₂`, bwf + Scoped + `≼≈` for the composite, and the external-face
equation `substᵗ (ρᵇ (Θ₁ ⊕ Θ₂)) (mrgB Θ₁ Θ₂ B₁) ≡ substᵗ (ρᵇ Θ₂) B₂`. A `MergeDef`
parameter was NOT used because the residues are FALSE as universal statements (below).

PROGRESS SCORECARD: `RevealVarApp`/`RevealVarTApp` DIED — theorems inside
`Progress.Impl`, no new hypothesis: at a reveal-variable face `γᵇ Θ X = \` X` (`γᵇ-lo`),
so the wrapper's body is a value of variable type, hence itself a wrapper by `canon-var` —
the redex was a wrapper-bodied wrapper all along, and `ξ-·-l (Merge v ok)` steps it.
`NestedApp`/`NestedTApp` remain, reduced to exactly "supply `MergeOK`".

### Decision 5 — ⊕ must keep the abstract witness (NEEDS A RULING)

Why progress did not close: `MergeOK` is falsifiable. The example (gauntlet §9d(i),
`⊢redex-cx`/`¬ext-cx`/`¬⊢merged-cx`):

```
Δ = X:=ℕ  ⊢  ((ƛ y:W. 3) ⟪ ↑W:=ℕ , W⇒ℕ ⟫) ⟪ ↓X:=ℕ , X⇒ℕ ⟫  :  X⇒ℕ
```

(No cancel fires here — W's reveal and X's conceal sit at different slots; the cancel
variant of the same failure is §9d(ii).)  If Merge fires with the current ⊕, then the
result is (`Θcx1 ⊕ Θcx2 ≡ rvl ℕ ∷ cnc 0 ℕ` and `mrgB Θcx1 Θcx2 (W⇒ℕ) ≡ W⇒ℕ`, both
by `refl` in the gauntlet):

```
(ƛ y:W. 3) ⟪ ↑W:=ℕ , ↓X:=ℕ , W⇒ℕ ⟫

  internal face:  (γᵇ) W⇒ℕ = ℕ⇒ℕ   ✓ matches the body
  external face:  (ρᵇ) W⇒ℕ = ℕ⇒ℕ   ✗ the redex has X⇒ℕ   (¬ext-cx)
```

The flattening lost the outer boundary's re-abstraction step: in the nested redex the
inner wrapper exports ℕ⇒ℕ into the middle region and the outer conceal re-abstracts
that to X⇒ℕ; in the composite, ρᵇ reads ↑W's rep — kept as the RESOLVED ℕ by mapL's
push-out — directly in the exterior, so the wrapper exports ℕ⇒ℕ and X's abstraction
is dropped (exactly TOPLAS's authority warning, reachable at an ⇒ face; `¬⊢merged-cx`
— the merged wrapper is not typable at X⇒ℕ).  This bad term is never actually
produced: MergeOK's external-face premise refuses it, so Merge does not fire — which
is precisely why `NestedApp` is unprovable and progress stalls on this redex.  But a
CORRECT merged boundary exists and types (`⊢repair-cx`):

```
(ƛ y:W. 3) ⟪ ↑W:=X , ↓X:=ℕ , X⇒ℕ ⟫        -- re-abstract W AT X, not at ℕ
```

— the reveal is kept, re-abstracted at the OUTER conceal's variable (the abstract
witness) instead of its resolved rep; both faces are then exact and the interior is
identical. Same story for the alias/x-pair shape (§9d(ii), `⊢repair-al`: keep Θ₂'s reveal
rather than the alias's ⋆-slot). And B₂′ is NOT a mrg₁-vs-mrg₂ coin flip — both are
machine-refuted in opposite directions (`¬γ-mrg₂-tower`: TOPLAS's keep-the-outer fails on
Example 3's tower; `¬ρ-mrgB-ag`: the landed pushed-out form fails on the three-agent
shape). The pattern in all four verdicts: the transport is wrong exactly when it
RESOLVES a cancelled reveal's rep through an enclosing conceal instead of naming that
conceal's variable.

THE PROPOSAL: change `mapL` so a Θ₁-reveal whose rep crosses a Θ₂-conceal is re-abstracted
at that conceal's variable (⊕ consults Θ₂'s conceals, not only its reveal count). If this
holds up, both `MergeOK` faces plausibly become theorems, `MergeOK` shrinks or vanishes,
and `NestedApp`/`NestedTApp` — the last two progress parameters — close.

Also flagged for later: `cmax Θ₁ ≤ revs Θ₂` (⊕-γ's side condition) is sufficient, not
necessary — it over-refuses conceal-of-conceal, the very TOPLAS-adversary shape whose
merge IS sound (`⊢merged-ag`); Merge simply doesn't fire there (no stuckness: such
towers are values pending depth-1).

### Decision 5, addendum (Jeremy's question, 2026-09-04 night): why ↑W:=ℕ
### and not ↑W:=X — the redex is REACHABLE, and the machine is STUCK there

Jeremy asked why the counterexample's inner boundary carries `↑W:=ℕ` rather
than the witness form `↑W:=X`.  The answer upgraded Decision 5's severity,
so it is recorded in full (machine-checked: gauntlet §9f).

WHERE A REVEAL'S REP COMES FROM.  A rep is minted by `TyBeta` as the
LITERAL type argument at the application site:

```agda
TyBeta : Value V → Δ ⊢ (Λ V) ·[ B , A ] -→ V ⟪ rvl A ∷ [] , B ⟫
```

So the question "ℕ or X?" is "what did the source program write at
`·[_]`?" — and that depends on whether X is NAMEABLE at that site.  Inside
`↑X:=ℕ`'s interior it is (`rvld` slot), and there the source writes `·[X]`
and the landed ⊕ is exact.  But in the PLAIN EXTERIOR — after the `ΛX` was
eliminated — X does not exist, and `ℕ` is the only spelling of that type;
inside `↓X:=ℕ` likewise (`intOf` DROPS the concealed slot: tightness).
The counterexample's form is therefore not exotic; it is what any client
that instantiates its own `ΛW` OUTSIDE the package produces.

THE WHOLE TRACE (gauntlet §9f: `cxP₀ … cxP₄`, `cx-step₁ … cx-step₄`,
`⊢cxP₀`, `⊢cxP₄`, all live inhabitants).  A closed plain System F source:

```
P = ((ΛX. λx:X. λf:X⇒ℕ. f·x) ·[X⇒(X⇒ℕ)⇒ℕ, ℕ] · 5) · ((ΛW. λy:W. 3) ·[W⇒ℕ, ℕ])

T1 TyBeta(X):  the package opens
    → ((λx:X. λf:X⇒ℕ. f·x) ⟪ ↑X:=ℕ , X⇒(X⇒ℕ)⇒ℕ ⟫ · 5) · ((ΛW. λy:W. 3) ·[W⇒ℕ, ℕ])
T2 Wrap(5):    5 crosses in as the abstract x; dualᴳ mints ↓X:=ℕ
    → (λf:X⇒ℕ. f · (5 ⟪ ↓X:=ℕ , X ⟫)) ⟪ ↑X:=ℕ , (X⇒ℕ)⇒ℕ ⟫
        · ((ΛW. λy:W. 3) ·[W⇒ℕ, ℕ])
T3 TyBeta(W):  the client's Λ opens IN THE EXTERIOR — ↑W:=ℕ is FORCED,
               X is not a name here
    → (λf:X⇒ℕ. f · (5 ⟪ ↓X:=ℕ , X ⟫)) ⟪ ↑X:=ℕ , (X⇒ℕ)⇒ℕ ⟫
        · ((λy:W. 3) ⟪ ↑W:=ℕ , W⇒ℕ ⟫)
T4 Wrap:       the client's function crosses in — the §9d(i) nesting
    → ( ((λy:W. 3) ⟪ ↑W:=ℕ , W⇒ℕ ⟫ ⟪ ↓X:=ℕ , X⇒ℕ ⟫)
          · (5 ⟪ ↓X:=ℕ , X ⟫) ) ⟪ ↑X:=ℕ , ℕ ⟫
```

STUCK — MACHINE-CHECKED (`stuck-cx`, `stuck-cxP₄`): the post-T4 term is
well-typed at ℕ (`⊢cxP₄`), is not a value, and NO rule fires on it: the
only candidate on the active redex is `Merge` via ξ-·-l, and `MergeOK`'s
external-face component is exactly `¬ext-cx`.  So this is no longer just
"NestedApp is unprovable": `cxP₄` is a reachable counterexample to TYPE
SAFETY of the calculus as it stands.  Decision 5 (or a change to `Value`)
is REQUIRED, not optional.

THE CROSSING IS THE GAP.  T4's dual re-expresses the crossing term's
boundary TYPE from interior to exterior coordinates (X⇒ℕ), but the reps of
boundaries ALREADY INSIDE the crossing term keep their exterior spelling
(↑W:=ℕ).  The re-abstraction ℕ↦X is exactly what Decision 5 asks ⊕ to
perform at merge time — and it is the INVERSE of the conceal's interior
reading γᵇ, which is relational in general (which ℕs become X?  In
`⊢repair-cx` the whole rep; for a rep like ℕ⇒ℕ under ↓X:=ℕ the candidates
X⇒ℕ / ℕ⇒X / X⇒X differ).  The external-face equation (B₂'s positional
alignment) is what selects the right one — so the repaired ⊕ must consult
Θ₂'s conceals AND B₂, or equivalently Zdancewic's Δ̄ backward reading.

CONTRAST, machine-checked (`run-repair-cx`): with the repaired boundary
`Θcx′ = ↑W:=X , ↓X:=ℕ` in place of the un-mergeable nesting, `Wrap` fires
and the program runs on to 3.

AND THE REPAIRED RUN FINISHES (`run-repair-tail`, fully-discharged
`MergeOK`): `(3 ⟪ ↑W:=X , ↓X:=ℕ , ℕ ⟫) ⟪ ↑X:=ℕ , ℕ ⟫` merges — the ↓X/↑X
pair CANCELS and W's rep resolves to ℕ legitimately, the outward crossing
passing the reveal that publishes X:=ℕ.  Final value: `3 ⟪ ↑W:=ℕ , ℕ ⟫`.
The resolved spelling ℕ is CORRECT in the plain exterior; it was wrong
only across ↓X:=ℕ — Decision 5 in one example.

### Decision 5, REFRAMED by Jeremy at the §9f review (2026-09-04 night):
### the linkage lives in the FACE TYPES — and Merge cannot be the whole story

Jeremy, reading the §9f trace: "W and X are not really tied to each other,
they just both happen to have the same rep type, and that means a revealed
W can line up with a concealed X" — and then: "the merge operator needs to
know the face types, because it's the face types that cause W and X to be
linked."  Both confirmed, machine-checked (gauntlet §9g); the second has a
machine-checked LIMIT.

(i) CONFIRMED: the W/X alignment is a COINCIDENCE OF REPS stipulated
positionally by B₂ — not a lineage.  (The x-pair cancels ARE lineage:
`xrep-stored` ties the dual's conceal to the reveal it was born from.
The §9f pair has no common birth.)  Consequence: a correct ⊕ cannot be
face-blind.  The landed `⊕ : BCtx → BCtx → BCtx` never consults B₁/B₂ —
which is exactly why the external-face equation had to be carried as a
MergeOK premise.  Any repaired merge is at least `⊕ Θ₁ Θ₂ B₁ B₂`.

(ii) THE LIMIT (gauntlet §9g): if the linkage is coincidence, one revealed
W can coincide with TWO different conceals at once.  The double package —
the §9f construction with two abstractions, client's Λ still opened
outside:

```
(ΛX. ΛZ. λx:X. λg:X⇒Z. g·x) ·[ℕ] ·[ℕ] · 5 · ((ΛW. λy:W. y) ·[ℕ])
```

The client `(λy:W. y) ⟪ ↑W:=ℕ , W⇒W ⟫` crosses the double reveal; the
dual mints `↓X:=ℕ , ↓Z:=ℕ` at boundary type `X⇒Z`.  The nesting types
(`⊢redex-d`).  But the external face needs W ↦ X at the domain and W ↦ Z
at the codomain, and:
- a single rep cannot carry both (`¬ext-dX`, `¬ext-dZ` — the two
  face-directed candidates each fix one position and break the other);
- rewriting B₀ to spell X⇒Z breaks the INTERNAL face against the body's
  type W⇒W (`¬γ-dXZ`, `¬γ-dWZ`) — terms are never rewritten, so the body
  stays typed at W⇒W;
- splitting the reveal in two (↑W₁:=X, ↑W₂:=Z with B₀ = W₁⇒W₂) is barred
  by the same internal-face pinning.

So on this shape FLATTENING IS IMPOSSIBLE — not underdetermined,
impossible, under ANY ⊕.  If this nesting is reachable (the construction
is the §9f trace with one more TyBeta; full mechanization of the trace is
queued), then `NestedApp` cannot be discharged by Merge at all, and the
abstract-witness ⊕ repair — even face-directed — is NOT sufficient for
progress/safety.

THE FORK THIS LEAVES (for Jeremy):
(a) FACE-DIRECTED ⊕ (`⊕ Θ₁ Θ₂ B₁ B₂`, keep the abstract witness where B₂
    stipulates one).  Fixes §9f's single-coincidence; machine-refuted on
    §9g's double coincidence — Merge stays partial, so progress
    additionally needs un-mergeable nestings to be handled some other way
    (values? a peel rule?).
(b) PEEL instead of flatten — generalize Wrap (and TyWrap) from ƛ-bodied
    (Λ-bodied) wrappers to VALUE-bodied wrappers:
      (V ⟪ Θ , B₁ ⇒ B₂ ⟫) · W -→
        (V · (W ⟪ dualᴳ Δ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫)) ⟪ Θ , B₂ ⟫
    (today's Wrap = peel + Beta when V is a ƛ; a TyWrap analog would have
    the inner type application instantiate at the new reveal's own
    abstract variable).  The application unwinds ONE boundary per step —
    all readings are INWARD (γ-direction, functional); the outward
    (relational, Δ̄) re-abstraction is never needed.  On §9f's stuck term:
    peel crosses the argument through ↓X:=ℕ (its dual re-reveals X:=ℕ),
    the inner Wrap then fires — runs, no merge.  On §9g's double
    coincidence: same, runs.  Merge + Drop∅ remain as MergeOK-guarded
    GARBAGE COLLECTION (they are sound as landed — preservation is
    proven), no longer load-bearing for progress; depth-1 values would be
    dropped (towers stay values).  Needs its own probe: preservation of
    peel = the Wrap case minus the β-substitution, plus the ∀-face analog.

Status: NO RULING YET.  §9g evidence is in; the fork is Jeremy's call.

### Decision 5 — RULING (Jeremy, 2026-09-04 night): PEEL (fork (b))

"Let's go with the Peel design."  Install in flight.  The finding that
led here, in full, since it reshapes the calculus:

THE CHAIN.  (1) The Merge landing left `MergeOK`'s external-face equation
as a rule premise, and §9f showed a reachable well-typed term stuck on it
(`cxP₄`) — the flatten-first design had a type-safety hole.  (2) Jeremy,
reading the §9f trace: W and X are NOT tied to each other — they merely
happen to share a rep type; the linkage that lets a revealed W line up
with a concealed X lives in the FACE TYPES, stipulated positionally by
B₂, not in the entries.  So any correct flattening ⊕ must consult the
faces.  (3) The limit (§9g, machine-checked): because the linkage is
coincidence rather than lineage, one revealed W can coincide with TWO
equal-rep conceals at once (`⊢redex-d`, face X⇒Z over ↑W:=ℕ against
↓X:=ℕ,↓Z:=ℕ), and then NO flat boundary exists under ANY ⊕ — the
external face needs W↦X and W↦Z simultaneously (`¬ext-dX`, `¬ext-dZ`),
rewriting B₀ breaks the internal face against the body's type
(`¬γ-dXZ`, `¬γ-dWZ`), and splitting the reveal is barred the same way.
Flattening is not underdetermined but IMPOSSIBLE.  (4) The root cause,
stated once: flattening must move an inner boundary OUTWARD across a
conceal, and the outward re-expression is the inverse of the conceal's
interior reading — relational (Zdancewic's Δ̄), with no syntactic home.

THE DESIGN.  Peel moves the ARGUMENT INWARD instead — the inward
re-expression is dualᴳ, a function, already live:

    Peel : Value V → Value W
         → Δ ⊢ (V ⟪ Θ , B₁ ⇒ B₂ ⟫) · W
           -→ (V · (W ⟪ dualᴳ Δ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫)) ⟪ Θ , B₂ ⟫

(generalizing Wrap from ƛ-bodied to any value body; old Wrap = Peel
followed by Beta; a TyPeel analog replaces/extends TyWrap at ∀ faces —
form to be fixed by probe at install, flagged for review).  The pairs
Peel creates are LINEAGE pairs — `dualᴳ Δcx Θcx2 ≡ Θcx1` by refl (§9h
`dual-cx`): the minted reveal comes from the very conceal it faces — and
those are exactly the cancels `cancel-agree`/`xrep-stored` justify.  On
§9f's stuck term: Peel, then the LANDED Merge cancels the argument's
↓X/↑X pair with a fully discharged MergeOK (`peel-cancel`), Drop∅, the
ordinary ƛ-crossing — a value.  §9g's double coincidence runs the same
way.  Each boundary is consumed by its own crossing, in its own
coordinates; the coincidence linkage is never needed.

CONSEQUENCES:
- Merge + Drop∅ STAY AS LANDED (preservation proven), demoted from
  load-bearing to lineage-pair GARBAGE COLLECTION behind MergeOK.
- Decision 3's depth-1 value grammar (option (iii)) is SUPERSEDED:
  towers remain values; no Value change needed.
- Progress: at a ⇒/∀ face Peel/TyPeel fires on ANY value body —
  NestedApp/NestedTApp become theorems; with the rv-* discharges kept,
  `progress` should become a top-level unconditional theorem at this
  install.
- §9f's stuck-cx/stuck-cxP₄ change meaning: cxP₄ now steps; the gauntlet
  keeps ¬ext-cx/§9g as the permanent record of why flattening was
  abandoned, and replaces the stuckness lemmas with the live Peel run.

### Decision 5 — refinement rulings (Jeremy, 2026-09-04 night)

(1) EITHER TOWERS OR MERGE/DROP∅, NOT BOTH.  Since Peel forces towers
(§9g killed collapse-by-flattening, so depth-1 + Merge was never
available), Merge/Drop∅ must be DELETED unless some progress case has no
Merge-free route — the known hinge is the RevealVarApp/RevealVarTApp
discharges (a variable-faced wrapper whose external rep is an arrow does
not match Peel's syntactic ⇒ face).  The install agent is determining
the dependency on the machine; if a case genuinely needs Merge, it stops
and reports rather than keeping Merge silently.  On deletion, the
flatten-first record (⊕, MergeOK, the §9 refutations) freezes into
notes/old per repo convention.

(2) DESIGN LAW — DETERMINISM: "I do indeed want determinism for this
language."  This independently evicts Merge/Drop∅: they are the only
rules whose LHS is a VALUE, so with them a tower in argument position
steps by ξ-·-r + Merge or is consumed by Peel — two different reducts.
Deliverables at the install: values-don't-step
(`Value V → ¬ (Δ ⊢ V -→ M′)`) and the determinism statement

    det : Δ ⊢ M -→ M₁ → Δ ⊢ M -→ M₂ → M₁ ≡ M₂

(proof included if it doesn't balloon the install, else queued NEXT —
never postulated).  Rule-pair disjointness to preserve: Peel vs Beta
(wrapper vs ƛ function), TyPeel vs TyBeta (wrapper vs bare Λ), ξ frames
directed left-to-right with Value premises.

## Decision 6 — PROGRESS NEEDS MERGE; THE DETERMINISM LAW FORBIDS IT
## (2026-09-04 night, at the Peel install — NEEDS A RULING)

The Peel install landed green (Peel replaces Wrap; TyPeel added for
wrapper-bodied ∀ faces, form (β) — TyWrap kept for Λ bodies;
NestedApp/NestedTApp DISCHARGED and deleted).  But the install surfaced a
genuine conflict between two rulings, both sides machine-checked:

(1) PROGRESS NEEDS MERGE (gauntlet §9i).  At a reveal-variable face the
interior type is `γᵇ Θ X = ` X` — abstract — so Peel/TyPeel, which push
the elimination INWARD, cannot type there; weakening B₀ as the rep
breaks the internal face by §9g's own ¬γ argument.  The nesting must
collapse: Merge is the ONLY rule that fires.  Reachable BY PEEL STEPS
ALONE from a closed plain source (`⊢rvQ₀`, `rv-step₁…₅` live):

    Q = ((ΛX. λf:(ℕ⇒X). f · 3) ·[ (ℕ⇒X)⇒X , ℕ⇒ℕ ] · (λn.λm.7)) · 5
      →TyBeta →Peel →Beta →Peel →Beta
      (((λm.7) ⟪ ↓X:=ℕ⇒ℕ , X ⟫) ⟪ ↑X:=ℕ⇒ℕ , X ⟫) · 5      : ℕ

`rv-only-merge` (coverage-complete): every step from this term is a
Merge; `rv-merge`: the Merge fires with MergeOK FULLY discharged (a
lineage pair, composite ∅); `rv-finish` runs on to 7.  So Merge was NOT
deleted.  RevealVarApp/RevealVarTApp are again Progress.Impl parameters,
now TIGHTENED to exactly this nested variable-face shape (strictly
weaker than before).

(2) DETERMINISM FAILS WITH MERGE (gauntlet §9j).  Merge/Drop∅ are the
only rules whose LHS is a VALUE.  Machine-checked counterexample
`nd-peel`/`nd-merge`/`nd-≢`: at

    (Vcx ⟪ ↑X:=ℕ , X⇒ℕ ⟫) · ((($5) ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=ℕ , X ⟫)

both Peel (consuming the tower argument as a value) and ξ-·-r + Merge
(stepping it) fire, with provably distinct contracta.  So as landed:
values-don't-step is FALSE and `det` is FALSE (both left as a NEXT
comment, not postulated).  No other rule pair overlaps — deleting
Merge/Drop∅ would give determinism immediately, and by (1) lose progress.

### The option space (no ruling taken)

(A) FOLD THE MERGE INTO THE ELIMINATION — front-runner.  Delete
    standalone Merge/Drop∅ (restoring values-don't-step + det) and add
    variable-face ELIMINATION rules whose LHS is the APPLICATION, e.g.

      MergeApp : … ((V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫) · W -→
                   (V ⟪ Θ₁ ⊕ Θ₂ , mrgB Θ₁ Θ₂ (` Y) ⟫) · W   (+ ∀ analog)

    An application never IS a value, so determinism survives; the
    collapse happens exactly where progress needs it.  OPEN QUESTION
    (the crux): the rv parameters demand a step for EVERY well-typed
    variable-face nesting — is the needed MergeOK derivable there in
    general (§9i's instance is a fully-discharged lineage pair), or does
    typing/bwf need a grounded strengthening so that only
    MergeOK-satisfying nestings type?  If some well-typed instance lacks
    MergeOK, this option needs the invariant minted at birth (the
    grounded-invariants law) — or the shape shown unreachable-and-
    untypeable.
(B) KEEP MERGE, SHRINK VALUE: a tower whose adjacent pair cancels is not
    a value (conditional, knowledge-relative value-hood — TOPLAS p.1074
    style).  Restores values-don't-step by construction; costs the
    simple value grammar and reintroduces a Decision-3-flavor depth
    restriction, now semantic.
(C) KEEP MERGE, WEAKEN THE LAW to determinism-up-to-GC (Merge/Drop∅
    confluent with everything).  Conflicts with the law as stated.

### Also flagged at this install (law-touching deviation)

TyPeel WEAKENS THE TERM: its contractum is `⇑ᵀ (V ⟪ Θ₁ , B₁ ⟫) ·[ … ]`
— the one rule that moves a term, against the no-term-shift law.  The
agent's case: it is a pure weakening (⊢renameᵀ at suc, a landed
theorem), not the forbidden push-a-type-inward (that is TyWrapCncl,
refuted by Example 8), and it is confined to the wrapper-bodied case
(TyWrap for Λ bodies stays shift-free — that is why form (β) was
chosen over (α), which also recreates the Ξalias residue and breaks the
E★′ trace).  Jeremy to confirm or overrule.

### Decision 6 — Jeremy's direction (2026-09-04 night): CANCEL, not Merge

"That example looks like it needs a Cancel reduction, not Merge."
Confirmed by §9i's own numbers: the firing Merge computes `Θrᵈ ⊕ Θr ≡ []`
— nothing is re-indexed; it is the CANCEL CLAUSE alone.  Precedent: the
old design's Cancel rule; the standing roadmap note "revive Cancel — its
side condition is exactly what Reversal now guarantees."  The option
space accordingly REPLACES (A)/(B):

  Cancel : Value V → (side condition)
         → Δ ⊢ (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫ -→ V

(A′) FOLDED: CancelApp/CancelTApp with the APPLICATION as LHS, restricted
     to variable-faced outer boundaries (where Peel/TyPeel cannot fire) —
     Value grammar untouched, towers at rest stay values, determinism by
     disjointness.
(B′) STANDALONE Cancel + Value restriction: a cancellable tower is NOT a
     value (decidable side condition required) — towers GC eagerly;
     Peel's Value premise and ξ-·-r become disjoint by construction.

Probe in flight (notes/CancelProbe.agda — now notes/old/CancelProbe.agda, pinned to the pre-Decision-6 relation): the side condition (syntactic
inverse vs Reversal≈ agreement vs lineage/dualᴳ form — the ≈ form is
suspected necessary, since a conceal rep spelled `X` under a reveal rep
spelled `ℕ⇒ℕ` may type via Reversal≈ unfolding while failing the
syntactic check); the (A′)/(B′) determinism tables; THE CRUX — whether
Cancel discharges the tightened rv parameters for EVERY well-typed
variable-face nesting (adversaries: the alias-reveal tower ↑Y:=X over a
conceal bottom; extra-entry Θ₁), or whether typing must mint
cancellability at birth (grounded-invariants law) / an extra rule is
needed; and the deletion inventory (Merge/Drop∅/⊕/MergeOK all die if
Cancel suffices — "either towers or merge/drop" resolved as towers +
Cancel).

Jeremy's refinement (same night): "cancel is a special form of merge +
drop — the special case where the inner value has type X, concealed by
the inner boundary and revealed by the outer boundary."  So Cancel's LHS
is FACE-ANCHORED:

    Cancel : Value V → (side condition)
           → Δ ⊢ (V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫ -→ V

with ` Y a conceal of Θ₁ (V's interior type = the conceal's rep,
concrete) and ` X the matching reveal of Θ₂ — exactly the tightened
RevealVarApp/RevealVarTApp shape, so Cancel targets precisely the
progress residue.  The probe additionally verifies the identity
cancel ≡ merge-then-drop∅ on the shapes where both fire (§9i: Merge
gives V ⟪ ∅ , mrgB ⟫, Drop∅ gives V), and derives the preservation
equation for the face-anchored form (what the OTHER entries of Θ₁/Θ₂
must satisfy — or be absent — for bare V to be typed in Δ at
ρᵇ Θ₂ (` X)).

### Decision 6 — CANCEL PROBE VERDICT (notes/CancelProbe.agda — now notes/old/, 2026-09-04)

Jeremy's identity CONFIRMED as a machine fact, and the side condition is
DERIVED, not chosen — but Cancel cannot carry progress alone.

(1) THE SOUND CANCEL.  Inverting (env) twice forces the side condition:

    CancelOK Δ Θ₁ Θ₂ B₁ B₂ =
        (intOf (intOf Δ Θ₂) Θ₁ ≡ Δ)                 -- contexts undo
      × (substᵗ (γᵇ Θ₁) B₁ ≡ substᵗ (ρᵇ Θ₂) B₂)     -- faces agree, ON THE NOSE

`cancel-pres` proves preservation for -→ V IN GENERAL from just these
two equations (no bwf, no Reversal, no MergeOK); `cancelOK?` decides it.
SURPRISE: the CONTEXT conjunct is the load-bearing one, not the face
pair — `Θe` (an extra reveal beside the conceal) has all four
face-anchored conjuncts yet its interior term can be ill-typed at Δ
(`¬⊢Ve`); a face-only Cancel is UNSOUND.  The ≈ form is also UNSOUND
(`¬a-inner-pres`: contexts undo, faces agree up to ≈Δ̄, contractum has
no type) — this CLOSES the old note "Cancel's side condition is exactly
what Reversal now guarantees": only ≡ works.

(2) CANCEL = MERGE + DROP∅, exactly: `cancel-≡-merge+drop` +
`merge+drop-general` — Cancel is Merge's `Θ₁ ⊕ Θ₂ ≡ []` case with Drop∅
fused; its only gain is 2 equations instead of MergeOK's 5 components.

(3) THE CRUX — Cancel does NOT discharge the rv parameters; progress
FAILS under both placements.  The well-typed variable-face nestings
`(V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫` classify into THREE families (typing
forces ρᵇ Θ₁ (` Y) ≡ ` X):
    α  alias-reveal: Y < revs Θ₁, rep ` X — NO conceal anywhere
       (¬a-CancelFace holds for every Y,X); typed: ⊢Ma.
    β1 the cancel case: Y = revs Θ₁ + X, X concealed — Cancel fires
       iff contexts undo; typed: ⊢rvQ₅ (§9i).
    β2 transparent layer: X kept and unconcealed — Cancel refuted
       (¬p-CancelOK); typed: ⊢Mtp; REACHABLE IN ONE LIVE TyBeta STEP
       from plain source (⊢p-src/p-birth/p-reaches — a ∀-body returning
       an OUTER type variable mints it: (ΛW. e) ·[ ` X-spelling , ℕ ]).
`progress-failsᴬ/ᴮ`: Ma · 5 and Mtp · 5 are closed, well-typed at ℕ, not
values, and take NO step in either Cancel placement (coverage-complete).
Merge fires on ALL THREE families with MergeOK FULLY DISCHARGED
(a-MergeOK, p-MergeOK, e-MergeOK).

(4) PRACTICAL CONCLUSION.  Piecemeal rules for α and β2 re-derive Merge
(β2 = the [] ⊕ Θ₂ case, α = the reveal-over-reveal case).  The design
that works is option (A) FOLDED MERGE: MergeApp/MergeTApp with the
APPLICATION as LHS, restricted to variable-faced outer boundaries
(disjoint from Peel/TyPeel by the face constructor — Progress's own
cf-⇒-B₀/cf-∀-B₀ split); standalone Merge/Drop∅ (the value-LHS rules)
DELETED → values-don't-step and det restored.  Cancel remains a
noteworthy special case (the 2-equation form), not a rule.  The three
fully-discharged MergeOK instances are positive evidence for (A)'s
remaining crux: the general lemma "MergeOK is derivable at every
well-typed variable-face nesting" (needed to discharge rv-app/rv-tapp;
if it resists, the rv parameters carry exactly it).

Placement detail from the probe (§4 disjointness tables): under (A′/A)
the §9j tower simply does not step at rest (nd-arg-stuckᴬ) and Peel is
the unique step at the application (nd-onlyᴬ); the Value grammar stays
untouched.  AWAITING JEREMY'S RULING on installing (A).

### Decision 6 — Jeremy's face-type restriction, checked (gauntlet §9k)

Proposal: "restrict Merge to function and universal face types" (keep it
standalone; the elimination position is maybe not the point).  Verdict:
the face types ARE the right discriminator, but the restriction alone
does not restore determinism — §9k, machine-checked.  §9j's clash does
vanish (that tower's external face is base ℕ).  But §9i's own tower has
EXTERNAL face ℕ⇒ℕ — a function face, so the restricted Merge still fires
on it — and in ARGUMENT position it clashes: `nd-beta` (Beta consumes
the tower as a value) and `nd-mergeArg` (ξ-·-r merges it) are both live
steps with distinct contracta (`nd-fnface-≢`).  A merge-redex that IS a
value clashes somewhere, whatever the face restriction.  The two exits:
  (i) exclude ⇒/∀-faced merge-redexes from Value — but ⊢redex-cx (§9d)
      is a ⇒-faced nesting with MergeOK FALSE: at rest it would be
      neither a value nor able to step, reviving the §9f hole — unless
      value-hood is conditioned on MergeOK itself (knowledge-relative
      values + a MergeOK decidability burden);
  (ii) put the merge at the elimination (MergeApp/MergeTApp) — the LHS
      is an application, never a value, so Value stays untouched and
      determinism is free.  Note the face types remain the point there
      too: at an elimination the merge fires exactly when the outer face
      is a VARIABLE (the complement of Peel/TyPeel's syntactic ⇒/∀)
      whose external reading is the function/universal type — the merge
      exists to EXPOSE the face Peel needs.

### Decision 6 — RULING (Jeremy, 2026-09-04 night): ACTIVE/INERT, inert/inert

Jeremy pushed the Siek–Chen JFP'21 parameterized-cast-calculi paper
(digest: notes/ParameterizedCastCalculi.md): reveals/conceals are casts;
casts classify as ACTIVE (reduce on values; not values themselves) or
INERT (value-forming; eliminated at use sites), with coherence fields
(ActiveOrInert totality, InertCross→, baseNotInert, applyCast totality)
that name exactly our failure modes — §9j/§9k were an active rule
(Merge) on inert-classified values; pre-Peel §9f was an inert shape
with no elimination.  RULED: **inert for function faces, inert for
universal faces** (Peel/TyWrap/TyPeel are the eliminations — active-⇒
would eta-expand and hide the boundary; active-∀ needs a type shift on
the term, barred by the no-term-shift law).  The classification table
(notes/ParameterizedCastCalculi.md): reveal-var faces and base faces
are ACTIVE (collapse via ⊕ / drop), conceal-var and ambient-var faces
INERT (the sealed values; no elimination exists at abstract type).
V-⟪⟫ gains the Inert premise (the Vcast discipline).  Install in
flight: Value restriction, active rules replacing standalone
Merge/Drop∅, canonical forms (canon-ℕ = numerals, canon-var-conceal),
applyCast-totality lemma (discharges rv-app/rv-tapp → progress
unconditional), values-don't-step + det.

### Decision 6 — INSTALLED (2026-09-04 night); Decision 7 opened

The active/inert install is LANDED, gates green cold.  As landed:

- `Inert`/`Active` classifiers (I-⇒ / I-∀ / I-var (revs Θ ≤ X);
  A-var (X < revs Θ) / A-ℕ / A-𝔹), `ActiveOrInert` total,
  `active-not-inert`; `V-⟪⟫ : Value V → Inert Θ B₀ → Value (V ⟪ Θ , B₀ ⟫)`.
- Active rules: `Merge` (kept name; now carries `Inert Θ₁ B₁`,
  `Active Θ₂ B₂`, and MergeOK — its LHS is no longer a value) and
  `Drop$ : Δ ⊢ ($ n) ⟪ Θ , `ℕ ⟫ -→ $ n`.  The base-face action set is a
  THEOREM, not a choice: `inert-ext` (InertCross→ + baseNotInert in one)
  gives the sharpened `canon-ℕ` (a value of type ℕ IS a numeral) and
  `canon-𝔹` (no 𝔹 values exist), so a numeral is the only possible body
  — CancelProbe's context conjunct is free (`⊢$` types anywhere).
  `Drop∅` DELETED (subsumed: at ∅ every var face is inert, every base
  face is Drop$'s redex).
- `TyPeel` gained `Inert Θ₁ B₁` (required for det — otherwise an active
  body stepping under ξ-·[] clashes with TyPeel).
- **DESIGN LAW SATISFIED — DETERMINISM IS PROVEN**:
  `V-¬-→ : Value V → ¬ (Δ ⊢ V -→ M′)` and
  `det : Δ ⊢ M -→ M₁ → Δ ⊢ M -→ M₂ → M₁ ≡ M₂`, both in BReduction.agda,
  no parameters — the whole proof runs off `active-not-inert` + the
  Value premises on the ξ frames.
- Canonical forms sharpened across the board; `canon-var-conceal`
  landed (a value at variable type is an INERT — conceal/ambient-faced
  — wrapper).
- `rv-app`/`rv-tapp` DISSOLVED (the reveal-var branch of the arrow/∀
  canonical-form analysis is refuted by `active-not-inert`).
- CancelProbe.agda retired to notes/old (pinned to the pre-Decision-6
  relation; its verdict lives here and in gauntlet §9a–§9l).

### Decision 7 — MergeOK's component (1) is the LAST obstruction to
### unconditional progress (gauntlet §9l — NEEDS A RULING)

Progress now carries exactly ONE parameter:

    MergeDerivable = ∀ {Δ V Θ₁ Θ₂ X Y}
      → Value V → revs Θ₁ ≤ Y → X < revs Θ₂
      → Δ ∣ [] ⊢ (V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫ ⦂ substᵗ (ρᵇ Θ₂) (` X)
      → MergeOK Δ Θ₁ Θ₂ (` Y) (` X)

and it is FALSE as stated — machine-checked (§9l).  With Δ = W:=𝔹,
Θ₂ = ↑X:=ℕ, Θ₁ = ↓X:=ℕ , ↓W:=𝔹:

    (3 ⟪ ↓X:=ℕ , ↓W:=𝔹 , X ⟫) ⟪ ↑X:=ℕ , X ⟫   :  ℕ     (⊢p)

is well typed, NOT a value (outer face active, ¬val-p), and takes NO
step: MergeOK's component (1) — `cmax Θ₁ ≤ revs Θ₂` — is 2 ≤ 1 (¬mok-p).
The inner boundary conceals an AMBIENT slot (W) the outer does not
reveal.  THE DIAGNOSIS IS SHARP: components (2)–(5) all hold on the nose
(bwf-p, sc-p, int⊕-p, ext-p), the contractum types at the redex's type
(⊢merged-p), and the INTERNAL-FACE EQUATION — the very thing component
(1) exists to buy via ⊕-γ — ALSO holds (int-p = refl).  Component (1)
is ⊕-γ's sufficient side condition, mistaken for a necessary one.

THE INDICATED REPAIR: replace MergeOK's component (1) by the
internal-face equation itself

    substᵗ (γᵇ (Θ₁ ⊕ Θ₂)) (mrgB Θ₁ Θ₂ B₁) ≡ substᵗ (γᵇ Θ₁) B₁

keeping `⊕-γ` as the theorem that discharges it whenever
`cmax Θ₁ ≤ revs Θ₂` (every existing Merge witness still builds).  §9l's
counterexample then steps, and `MergeDerivable` plausibly becomes a
theorem — PROGRESS UNCONDITIONAL.  This edits `MergeOK`, a Decision-3
object in the reduction relation: Jeremy's ruling required.

### Decision 7 — RULING (Jeremy, 2026-09-05): repair MergeOK

"Go ahead with the MergeOK repair."  Install in flight: MergeOK's
component (1) `cmax Θ₁ ≤ revs Θ₂` becomes the internal-face equation
`substᵗ (γᵇ (Θ₁ ⊕ Θ₂)) (mrgB Θ₁ Θ₂ B₁) ≡ substᵗ (γᵇ Θ₁) B₁`, with ⊕-γ
demoted to the theorem discharging it under cmax≤revs (existing
witnesses rebuild); §9l's counterexample steps; the target is
MergeDerivable proven → Progress.Impl instantiated → progress TOP-LEVEL
UNCONDITIONAL, with det/V-¬-→ kept.

## THE PRESERVATION ENDGAME (2026-09-05) — plan + three parallel tracks

Jeremy: "speed up the push to finish preservation; plan DualCnc≈ now,
launch subagents for DualRep≈ and DualInt≈."  Done — the full plan is
notes/PreservationEndgame.md.  Key points: all three residues are
PROBE-FIRST (each has a suspected-false corner: DualRep≈ lacks ⊢ᶜ Δ —
the store-typing pattern, a preservation-STATEMENT change to confirm;
DualInt≈'s ≼≈ has no clause for the rebuild's abst at xrvld /
double-refusal slots; DualCnc≈'s starOnly is caught in the Pc-copy vs
Pn-license tension INSIDE dualᴳ).  The DualCnc crux = whether the
copy-needing and license-needing demands can hit the SAME slot (probe
Q2); if not, the repair is per-slot copy suppression in dualᴳ
(decidable, birth-time, grounded); else starOnly′ "claims nothing new"
(renaming-stable form only — D1 lesson; must re-refute ⊢3n-adv) or a
birth-time minting.  Rulings will be asked with the probes' examples on
the table.

## DECISION 7 LANDED; TWO REFUTATIONS OPEN DECISION 8 (2026-09-05)

The MergeOK repair is in (component (1) = the internal-face equation,
⊕-γ demoted to its discharge; every witness rebuilt; preservation's
Merge case simpler; det/V-¬-→ untouched).  `merge-derivable :
MergeRest → MergeDerivable` is PROVEN — Decision 7 closed component (1)
for good (`mid-var` pins Y ≡ revs Θ₁ + X, `⊕-γ-var` discharges (1) with
no side condition).  Progress's parameter shrank to `MergeRest`
(components (2)–(5)).

BUT two refutations landed the same hour, and they share a root cause.

(1) `¬MergeRest` and `¬progress` (gauntlet §9m).  Δq = X:=ℕ,
Θq2 = ↑X:=ℕ, Θq1 = ↓X:=(` 0) — the conceal's rep is spelled `X`, the
ABSTRACT witness, licensed by bwf↓'s Reversal≈ THROUGH THE UNFOLDING
(rev-q = ≈unf refl; the syntactic form is refuted, ¬rev-q-≡).  The pair
cancels, and MergeOK's external-face component — stated with ≡ because
preservation transports by subst — fails: mrgB = ` 0 vs ℕ (¬ext-q).
The same tower with the lineage rep ℕ steps (merge-q′).  Half is
settled: ⊕-ρ-var-kept proves the external face free in the KEPT branch;
the CANCELLED branch is the refuted half.  So the unconditional
progress statement is FALSE as things stand (¬progress, machine).

(2) `¬DualCnc≈` and — the sharp one — `¬DualCnc≈-soundness :
DualRep≈ → DualInt≈ → ¬ DualCnc≈` (notes/probes/DualCncProbe.agda).
Pn refutes DualCnc≈ with the hypothesis discharged; per-slot copy
suppression is IMPOSSIBLE as a theorem (`no-per-slot-suppression`:
every rep-carryingly-copied slot is non-abst in Δ and ≼≈ has no
knowledge-below-abst clause — the copy the license wants gone is the
copy the rebuild law requires, ALWAYS the same slot); the
claims-nothing-NEW weakening re-admits ⊢3n-adv via the same
constructor, and the machine shows WHY nothing can work at that site:
`Ψn≡Γz` — Pn's dual conceal and the ⊢3n-adv adversary are THE SAME
(bwf-↓x) INSTANCE (same Γ, Ψ, Θ, X, A, A′).  The three preservation
parameters are mutually INCONSISTENT: BPreservation.Impl as
parameterized can never be instantiated.  The residue must not be
attacked at DualCnc≈.

THE SHARED ROOT CAUSE: reps spelled through knowledge CHAINS rather
than resolved.  §9m's conceal rep is the abstract spelling `X` whose
license is ≈-through-unfolding while the merge's faces demand ≡; Pn's
reveal rep is the chained spelling `Y` whose dual re-reveals the
knowledge rep-carryingly.  In both, the ≡/≈ gap between what bwf
licenses (≈Δ̄, Decision 1's (a″)) and what the metatheory transports
(subst over ≡) is the obstruction.

DECISION 8 — the option space (probing before the ask is complete;
DualRep≈/DualInt≈ agents still out, their verdicts fold in):
(α) FACES UP TO ≈: state MergeOK's two face components (and possibly
    the middle-type equation) with ≈Δ̄ instead of ≡, and transport
    preservation's Merge case by a retag≈-style lemma.  Obstacle: ⊢retag≈
    moves CONTEXTS; a type-side ≈ in the typing judgment has no
    transport today — this road may lead to a conversion-style typing
    rule or ≈-stated (env) faces, a deep change to Boundary.agda.
(β) BORN-RESOLVED REPS: normalize reps THROUGH THE AMBIENT AT MINT TIME
    (in the RULES — TyBeta/TyWrap/dualᴳ — not in the entry maps, so the
    transports that killed (a′)-at-entry-birth are untouched).  Kills
    §9m (conceal born ↓X:=ℕ — merge-q′ steps) and Pn (reveal born
    ↑Z:=ℕ — raw-readable, ordinary license) and collapses Pc's chain
    (second-chance copy retired).  KNOWN OBSTACLE, stated honestly: the
    ≡-rigidity relocates — e.g. TyBeta's contractum must be typed at
    B [ A ]ᵗ with the SYNTACTIC A, so normalizing a reveal rep changes
    the external face away from the redex's type unless the face
    equations/typing absorb ≈ somewhere.  Needs a probe (distinct from
    the refuted (a′): UnfoldProbe's ¬DualCnc-a′ was about the ENTRY
    map).
(γ) UPSTREAM DISSOLUTION: make the chained/abstract-rep shapes
    unmintable or non-values (classification/typing strengthening), or
    dissolve Pn-shaped boundaries by an eager collapse before any dual
    is taken.  Shape unclear; the probes' reachability analysis
    matters (is §9m's ↓X:=(` 0) conceal MINTABLE by the current rules?
    — dualᴳ mints conceal reps as the STORED reveal reps, and TyBeta
    mints reveals from literal type arguments; a ↓X:=X-spelled conceal
    may only arise from a source-written abstract-witness spelling —
    check).
NO RULING YET.  The ask will be assembled with the DualRep≈/DualInt≈
verdicts and reachability probes, on concrete examples.

## THE PRESERVATION VERDICT (2026-09-05) — SUBJECT REDUCTION IS FALSE;
## the endgame probes converge on the REP DISCIPLINE (Decision 8, full ask)

All four endgame tracks are in.  The headline, machine-checked
(notes/probes/DualIntProbe.agda §3.3 + §5):

    ⊢Redex     : Δd ∣ [] ⊢ (Vtm ⟪ Θ2 , (` 0 ⇒ ` 0) ⇒ `ℕ ⟫) · Wtm ⦂ `ℕ
    peel-step  : a live Peel step on it
    ¬⊢contractum : the contractum has NO typing at ℕ

with Δd = rvld (` 0) ∷ abst ∷ rvld `ℕ (a chained-knowledge ambient),
Θ2 = ↑?:=(` 0) , ↓·:=ℕ (a reveal whose REP names the chained slot), and
Wtm a value sealed by ORDINARY knowledge of that same slot
(↓0:=(` 0), bwf↓ at Δd ∋ 0 := ` 0).  The Peel's dual DEMOTES slot 0
(both copy guards refuse → rvl⋆ → the rebuild has abst), and Wtm's own
conceal license — which consults slot 0 — dies inside the dual
(¬⊢W-rebuild).  So the loss is not in the proofs: the CALCULUS loses
subject reduction at this Peel.  Combined with §9m's ¬progress, both
halves of type safety are false as things stand; the DualDef
parameterization was covering a false theorem (and ¬DualCnc≈-soundness
had already shown the three parameters mutually inconsistent).

WHAT IS CLOSED, in the same sweep:
- DualRep≈: FALSE as stated, REPAIRED AND FULLY PROVEN
  (strong-rep-nu/DualRepProof.agda): BlkRepWf (the index relation
  cmax Θ ≤ suc (i + k) the emitter guarantees) + the EXISTING ⊢_ context
  judgment; threading lemmas ⊢-[], ⊢-abst, ⊢-intOf, ⊢-intOf-dual all
  proven — preservation's statement gains a ⊢ Δ premise (store-typing
  pattern; every ξ case covered).  bwf-dual-wf drops the parameter: the
  residue set shrinks by one.
- DualInt≈: FALSE (two corners, xrvld and double-refusal — both the
  rvl⋆→abst demotion); the ≼≈-weakening repair REFUTED at the live Peel
  above; strongest-true version delivered (strong-rep-nu/DualIntProof.agda):
  dual-int≈ reduces it to DualIntHead, a per-slot residue on the cmax Θ
  dropped slots, and head-⋆-abst shows the residue at an rvl⋆ slot IS
  "Δ was abstract there" — dual-int-nodrop / dual-int-abst are the
  closed sub-cases.
- DualCnc≈: FALSE; unfixable at its own site (no-per-slot-suppression;
  CNN re-admits ⊢3n-adv; Pn's dual IS the adversary's (bwf-↓x) instance).
- Decision 7's component (1): closed for good (merge-derivable).
- det / values-don't-step: STAND (they are about the rules, not the
  typing).

THE CONVERGENT DIAGNOSIS.  Every counterexample of the sweep — Pn
(DualCnc), §9m (progress), the two DualInt corners, and the live
preservation break — threads through the same gap: THE SCOPE DISCIPLINE
POLICES B₀ BUT NOT THE REPS.  `Scoped (baseS Θ Δ) B₀` forbids the
boundary type from naming a blocked slot, but bwf↑ licenses a reveal
rep to be ANY Δ-type — chained spellings (` Y with Y:=ℕ), abstract
witnesses (` X licensed only ≈-through-unfolding), and demotable slots
included — and bwf↓/bwf↓x's licenses are NOT stable under the demotion
the dual performs (≼≈ has no knowledge-below-abst clause, correctly:
¬⊢W-rebuild is exactly a license dying under demotion).  The ≡/≈ gap
(§9m) is the same phenomenon one level up.

DECISION 8 — the ask (rulings on direction, then probes before install):
(A) A REP DISCIPLINE in bwf: reps must be Scoped like B₀ (no blocked
    slots) AND resolved (no spelling through rvld-chained slots — the
    resolved spelling exists and is what the license compares against
    anyway).  Kills Pn and §9m at birth (their boundaries become
    unmintable as written; TyBeta/source can still write ·[Y] — the
    RULE would mint the resolved rep, which is where the known
    obstacle lives: TyBeta's contractum must still be typed at
    B [ A ]ᵗ with the syntactic A — needs a probe).  ASSESSMENT, not
    machine-checked: this alone does NOT close the live preservation
    break — §3.3's resolved rep lands on an abst (Λ-bound) slot and
    the demotion problem remains.
(B) DEMOTION-COMPATIBLE CROSSINGS: Peel (the only rule reading Δ)
    gains a grounded premise in the MergeOK style — the crossing value
    W must be typeable against the dual's rebuild ("PeelOK"), with
    progress then obligated to derive it at well-typed redexes or the
    redex classified a value/stuck-by-design.  §3.3's redex would fail
    PeelOK; the question becomes whether every SOURCE-reachable
    crossing satisfies it (reachability probe) — if yes, this is the
    grounded-invariants answer; if no, the calculus needs (C).
(C) RETHINK THE DEMOTION: the dual's rvl⋆ fallback is the only
    knowledge-destroying step in the system; alternatives (keep an
    x-marked copy instead of rvl⋆ so licenses survive demotion as
    x-licenses; or forbid boundaries whose reps/licences depend on
    demotable slots — a transitive rep discipline) need design work
    with the five counterexamples (Pn, §9m, DualInt ×2, §3.3-peel,
    plus ⊢3n-adv as the soundness gate) as the fixed test suite.
Recommendation: (A)+(B) probed together first — (A) shrinks the shapes
to Λ-bound-only demotions, (B) polices exactly those; (C) only if the
reachability probe under (B) finds a source-reachable failing crossing.

## REDESIGN SURVEY ORDERED (Jeremy, 2026-09-05)

"I'm worried that our current boundary bookkeeping is rather broken...
time for a fresh look at all the critical examples and perhaps more, now
that trace generation is easy, and use the data to inform a redesign."
This SUPERSEDES Decision 8's install track: no repair is installed until
the survey data is in.  In flight: EvalLog.agda (an event annotator over
stepΣ's derivations — boundary mints with rep classification, crossings
with per-slot dual outcomes incl. DEMOTION markers, merges/cancels),
notes/probes/SurveyCorpus.agda (the critical examples + new families:
depth-2 chains, double crossings, returned sealed values, x-entries
under a second dual, Λ-bound reps crossed twice), and
notes/BoundarySurvey.md (the master table + machine-backed findings).
The corpus doubles as the regression suite / kill criterion for any
redesign candidate.

Survey amendment (Jeremy, same day): additionally instrument WHAT THE
BOUNDARY MUST PROVIDE, ignoring the current bookkeeping — per boundary
occurrence per trace state: the internal face (synthesized bottom-up
from the interior TERM alone — interiors are term-closed and annotated,
so no γᵇ/ρᵇ/intOf is consulted), the external face (the top-down DEMAND
from the use site), and the type variables in scope/mentioned on each
side.  Oblig.agda + obligLog; a REQUIREMENTS section in
BoundarySurvey.md.  Because synthesis needs no typability, the
instrument keeps reporting through the ill-typed states after the §9n
break — the obligation rows there ARE the requirements spec the redesign
must meet.


## Jeremy's Questions

The next step is to turn this data into advice regarding the design of
the boundaries. 

* For example, we're having a lot of trouble propagating the
  representation types. Should we instead only store the
  representation type with the outermost reveal and perform lookup to
  access it from the inner boundaries associated with the same type
  variable?

* What about the simultaneous aspect of the design? Is that holding up
  or should be go back to a sequential/telescopic treatment?
  Something that we have not yet explored is using the notion of
  Conversion (see GTSF/Conversion.agda) for relating the interior face
  to the exterior face of a boundary. It seems Conversion by itself
  cannot explain the scoping of type variables in the terms, but
  perhaps it would still be useful.

* As we think about all of this, the load bearing thing is that when
  we cancel a matching conceal and reveal (or in Conversion terms, a
  seal and unseal), we need to know that the interior and exterior
  face types match, otherwise we have a preservation problem.

In addition to those design questions, are there other aspects of the
design that we should think about changing?

## REDESIGN ADVICE (2026-09-05) — notes/RedesignAdvice.md

Jeremy's four questions answered from the survey data (full memo in
RedesignAdvice.md): Q1 central rep storage YES (the strongest-supported
change; every failure is a failed rep copy; ownership makes the pointer
stable where the copy was not; GTSF's Σ-store realization comes with
proven transport lemmas); Q2 simultaneity KEEP (no finding implicates
siblings; the failures are all cross-boundary); Q3 Conversion YES as the
FACE half of a split boundary — scope skeleton (strong-rep-nu/, rep-free) +
conversion witness (GTSF), closing R3's 61 undetermined rows; Q4 the
cancel face-match becomes DEFINITIONAL under ownership (one algebra
lemma replaces cancel-agree/Reversal≈/SkelEq/MergeOK-faces).  Q5 extras:
Merge→Cancel (⊕ retired, F8/F9), no ≈ in rules (§9m disease), retire the
x-machinery (F4), the dual shrinks to slot re-pointing (demotion concept
deleted), keep active/inert + inward-only + det + tightness-for-scope;
FLAGGED for ruling: owner lookup vs the tightness law.  Soundness gate:
⊢3n-adv must be unmintable.  Next: ConversionBoundaryProbe (transport
risk probed FIRST), corpus as kill criteria.

### Redesign — Q1 realization RULED (Jeremy, 2026-09-05): OWNER-SYNTACTIC (ii)

"Once type variables are in a global store, it becomes more difficult to
talk about their lexical scope relationships, which we are currently
using in conceal blocking.  So I'd lean towards realization (ii) for
now."  Recorded: the outermost reveal wrapper IS the store entry; inner
boundaries carry names only; faces/licenses resolve by lookup along the
ENCLOSING SPINE.  Note the coherence this buys: conceal blocking and
ownership are both lexical-enclosure notions — the owner outlives every
reference because the variable's scope is inside its wrapper (the
owner-liveness invariant, to be machine-checked).  The known risk stays:
faces become spine-dependent, so the ⊢renameᵀ/⊢retag transport analogs
must be probed FIRST (mitigation: lookup is by slot identity along the
spine, which renamings move coherently — the inverse of D1's refuted
spelled-copies).  ConversionBoundaryProbe launched with this mandate.

### Redesign — split term constructors (Jeremy, 2026-09-05)

"Should we create a different term constructor for the outermost reveal,
that stores the rep type, then another for conceals, and another for
inner reveals?"  Adopted into the probe mandate.  Assessment: this makes
OWNERSHIP A SYNTACTIC INVARIANT (the rep field exists only on the owner
constructor — R1's one-spelling-per-variable enforced by the grammar);
the constructors pair one-to-one with the Conversion forms (owner ↔
unseal-at-owner, conceal ↔ seal, alias ↔ id) so the face witness may be
derivable from the constructor itself; the entry-list machinery
(revs/cmax/shiftReps/swapᵇ) should disappear into ordinary de Bruijn
binder discipline; Cancel becomes an adjacent-pair syntactic rule with
no composite/⊕ notion at all; duals mint only rep-free constructors.
Simultaneity note: nesting single-purpose constructors is sequential,
but the keep-simultaneity ruling concerned SIBLING REP interference in
one multi-entry boundary — with at most one rep per constructor there
are no siblings; the probe reports if any interference reappears.

## THE REDESIGN PROBE VERDICT (notes/probes/ConvBoundary{Core,Terms,Probe}.agda,
## 2026-09-05) — GREEN; one ruling ask (POLARITY); the redesign branch is cut

TRANSPORT (the make-or-break): PASSES.  `conv-ren` needs NOTHING beyond
the spine renaming (knowledge transport is DEFINITIONAL: `Δ ∋ X := A` is
an entry lookup, so the rep comes back out of the renamed spine already
renamed — the inverse of D1); `⊢rename` needs one structural hypothesis
`Inj ρ` (positional masking, not reps; stable under all binder
extensions); `⊢retag` has NO residue (the ⊑ ordering has no clause that
loses an owner — the demotion is not expressible).  Jeremy's mask-not-
drop prediction confirmed: one frame per spine is what makes it go.

THE MINI-CORE (verbatim in the probe): spine entries abst / own A /
blk E (mask retains the entry); conversions c-b/c-v/c-u(unseal at
owner)/c-s(seal at owner)/c-f(⇛, contravariant)/c-a(∀ᶜ), polarity-
indexed; one boundary form M ⟪ Θ , c ⟫ with own/ali/cnc entries and
(env) checking the conversion between the faces over a face spine;
rules TyBeta/Beta/Peel/TyPeel/Cancel/Drop$/ξ; dual Θ = maskOwns ++
name-flips (cnc↔ali) — NAMES ONLY; Inert = {cv, csl, ⇛, ∀ᶜ}, Active =
{cb, cus} — constructor totality, no arithmetic.

VERDICTS: the three breaks (c10/c11, n1b; n4 structurally) TYPE, CROSS,
and their contracta are TYPED (⊢contractumd directly contradicts
DI.¬⊢contractum; mask-retains + ali-recovers prove no operation can
take an owner away); ⊢3n-adv UNMINTABLE by one inversion
(seal-cites-owner); bad/bad₂ dead (a seal's interior face IS the
owner's rep); §9m CANNOT ARISE (cancel-faces-agree = ∋:=-det twice —
one lemma replacing cancel-agree/Reversal≈/SkelEq/xrep-stored/MergeOK's
faces); the cancel pair runs (Cancel + Drop$); shape-IV obligations all
typeable, Rows B/C now SURVIVE their crossings.

DELETED (no analog): ⊕/mrgB/MergeOK, the x-machinery, ≈/Unfold/
Reversal≈, entᴳ/copy guards/second chance/rvl⋆/demotion, cmax/dropN/
Δ↓X/swapᵇ/shiftReps, baseS/Scoped as a separate stack (the mask IS the
entry), DualDef's three parameters, ≼≈.  SURVIVES: simultaneity (own
reps read in the plain exterior), active/inert + values, inward-only,
nrev as the only index arithmetic (ordinary binder offsets).

FOUR NEW OBLIGATIONS the advice memo missed:
1. **POLARITY — NEEDS JEREMY'S RULING.**  Conversions are polarized
   (⇛ flips on domains), so one boundary unseals OR seals at positive
   face positions; a boundary revealing X and concealing Y with BOTH
   positive in the face is inexpressible.  The corpus never needs it —
   every corpus conceal is PURE SCOPE (absent from the face).  Ruling:
   accept single-polarity boundaries (+ prove source-reachable
   boundaries are single-polarity), or add a mixed conversion form.
2. Mask-not-drop is FORCED, not stylistic: the split-constructor +
   dropping variant was built far enough to fail — a dropping conceal's
   dual must reintroduce a telescope of rep COPIES (D1's disease one
   level out).  Masking also lets mask/unmask be FUNCTIONS (the
   split form needed relations, blocking inversion).
3. A context-wellformedness premise (⊢ Δ, the store-typing pattern
   DualRepProof already built) is needed for "a conversion's faces are
   well-formed" — preservation will carry it.
4. Inj ρ (structural, positional-masking-only).

HONEST LIMITS: the two general Peel context identities are refl on
every corpus instance but the general induction (nrev index bookkeeping)
is NOT done; ⊢subst not done (sources not run end-to-end); n4/E★′
checked structurally.  These are the first work items of the build-out,
not design risks.

## Redesign — the id-layer rule (Jeremy, 2026-09-05): IdAbsorb, ACTIVE-guarded

Jeremy's question "can a value wrapped at an id (` X) face be eliminated?"
exposed the mini-core's first progress hole (ConvBoundaryProbe §6: T₆ is
stuck-well-typed — the β2/transparent-layer family landing in the
redesign; Cancel covers only β1).  RULED: a new reduction rule of the
absorption shape, WITH THE ACTIVE/INERT METHODOLOGY EXPLICIT — the outer
conversion must be ACTIVE:

    IdAbsorb : Value V → Active c
      → Δ ⊢ (V ⟪ Θ₁ , id A ⟫) ⟪ Θ₂ , c ⟫ -→ V ⟪ Θ₁ ⊳ Θ₂ , c⁺ ⟫

The Active premise is load-bearing: with c inert the LHS is a VALUE
(V-⟪⟫), so the premise is exactly what preserves values-don't-step and
det.  `id` is composition's unit, so no conversion is composed — ⊳ must
be owners+names-only (the no-⊕ test).  Probe in flight: T₆ runs to 7;
stacked id-layers; the mask-jam analysis for ⊳; whether R1 (vacuous
instantiation) earns a place as companion; the door-closing on naked
id-drop (the context conjunct).

## THE ID-LAYER PROBE VERDICT (notes/probes/IdLayerProbe.agda, 2026-09-05)

IdAbsorb's SHAPE (Active c premise) is right; its operator ⊳ is not.
Machine-checked: T₆ runs to 7 under IdAbsorb, and the id-base branch of
Active is vacuous (outer-id-base-untypeable — unseal is the only active
face the rule meets; the inner face must be spelled id (` X)).  BUT ⊳
has two failure modes: Jam #2 (Tᵣ, typed and stuck) — an id-layer whose
skeleton carries a rep naming Θ₂'s owner: the merge equations fail and
the only repair is substituting reps into reps — REP ARITHMETIC, i.e.
⊕ REGROWN.  Fails the no-⊕ test.  Jam #1 (Tₘ) — ⊳ computes both spines
correctly yet Bwf refuses: Bwf is not compositional (entries checked
against the plain exterior, not the spine the earlier entries build).

THE RECOMMENDED ALTERNATIVE — IdPush, IdAbsorb's degenerate form with
⊳ deleted (same LHS, same methodology, both frames untouched):

    IdPush : Value V → Δ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫
                     -→ (V ⟪ Θ₁ , unseal X ⟫) ⟪ Θ₂ , idc A ⟫

No merge equations ever arise; idpush-name proves typing FORCES
X ≡ nrev Θ₁ + Y (the pushed name is already written in the id face); it
runs T₆ AND both of ⊳'s adversaries (run-Tᵣ-push, push-Tₘ); each step
moves the active face one layer inward toward the seal, so it
terminates.  R1 (vacuous TyBeta) = optional hygiene only (TyPeel mints
the same layers regardless); R2 (deep Cancel) dead; naked drop sound
only at Θ ≡ [] (drop-empty-frame).  AWAITING JEREMY: IdPush vs
pay-for-⊳ (compositional Bwf + an owners-exterior-readable discipline).

THREE MINI-CORE BUGS the probing surfaced (repairs for the restructure):
1. Cancel's residue maskOwns (nrev Θ₂) masks exterior slots that need
   not exist (¬Bwf-cancelTm-residue); CancelR (drop maskOwns) types on
   every instance.  Also Cancel's single name X presumes nrev Θ₁ ≡ 0.
2. TyPeel does not shift its type annotation: repair
   ·[ renameᵗ (extᵗ suc) B , ` 0 ] (TyPeelR).
3. V-Λ lacks the Value premise (v1's G-Λ had it): Λ N is a value for
   EVERY N while ξ-Λ reduces under Λ — value-that-steps and
   det-already-broken are machine-checked.  REPAIR (restores Jeremy's
   determinism law): V-Λ : Value N → Value (Λ N).  With that fix and
   either new rule, no new overlaps (IdAbsorb≢Cancel etc.).

### Id-layer RULING (Jeremy, 2026-09-05): IdPush + the lookup premise + all repairs

"Go ahead with IdPush and the lookup premise and the other repairs."
The rule as ruled:

    IdPush : Value V → fceC Θ₂ Δ ∋ Y := A
      → Δ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫
          -→ (V ⟪ Θ₁ , unseal X ⟫) ⟪ Θ₂ , idc A ⟫

with the principle made explicit: EVERY rule minting an identity face at
a looked-up rep carries the owner-lookup premise (Cancel's idc B too) —
determinism via ∋:=-determinacy; the premise is the rule-level twin of
conv-unseal's typing premise.  The repair set for the restructure:
V-Λ gains the Value premise (restores det/values-don't-step), CancelR
(residue fixed, lookup premise, single-name presumption generalized),
TyPeelR (shifted annotation), lookup-determined idc faces.  R1 (vacuous
TyBeta) deferred as optional hygiene.  ⊳/IdAbsorb retired (fails the
no-⊕ test — IdLayerProbe Tᵣ).

### v2 vocabulary + repair (5) CONFIRMED (Jeremy, 2026-09-05)

Names ruled and landed: "boundary skeleton" → "boundary CONTEXT
BOUNDARY SCOPE"; BCtx → Boundary, BEnt → MorphEnt; own → bind (both the
boundary scope entry and the type-context entry it creates), ali → bind,
cnc → unbind; derived: bw-b/bw-l/bw-u, bindNames, lockBinds, reps→bind,
nrev → nbind, vis-o → vis-b.  Prose: "spine" → "type context"
(standard terminology), "slot lookup" → "entry lookup".

REPAIR (5) CONFIRMED: TyBeta carries `Value N` — the fifth determinism
repair (TyBeta vs ξ-·[]⨟ξ-Λ was a genuine overlap; mirrors Beta;
positive witness run-Ωt).  With it, det and values-don't-step are
theorems of the landed v2 rule set.

## v2 PRESERVATION VERDICT (2026-09-05) — FALSE as the rules stand; four rules to repair

Committed 5554c6b2 (Preservation.agda + proof/Preserve.agda +
proof/PreserveObstruct.agda).  det, values-don't-step, and PROGRESS are
parameter-free theorems.  Preservation:
- preservation-fails : ¬ Preservation PROVEN; the positive theorem lives
  in `Conditional` over four refuted rule obligations.
- PROVEN outright: TyBeta (⊢unsealAt/⊢sealAt; abst→bind retag; intC
  (bind A ∷ []) Δ definitional), Beta, Drop$, all five ξ.  NO ⊢ᶜ Δ
  premise needed — ⊢ᵗ-of recovers face wf from the derivation.
- REFUTED, each with a diagnosed cause (a RULE bug, not a proof gap):
  * Peel — `dual` is wrong: dualS maps a no-op `bind X` to a real
    `unbind`, and it replays Θ's ops in Θ-order so a same-slot mask/unmask
    pair fails to cancel; intC-dual is FALSE (¬intC-dual).  fceC-dual is
    fine (refl).
  * TyPeelR — the pushed `·[ B , ` 0 ]` must carry the INTERIOR ∀-body,
    not the exterior B; and `renᴮ suc Θ` double-counts the new binder.
  * CancelR — residue `reps→bind (reps Θ₂)` discards Θ₁'s whole frame
    (and any `bind` in Θ₂).
  * IdPush — swapping the faces demands the owner's rep well-formed in
    Θ₂'s interior, which an `unbind` there has blocked: the c10/c11
    chained-rep shape, resurfacing at the rule level.

READ: three of the four are LOCAL rule-definition bugs (dual's flip
logic + non-reversal; TyPeelR's annotation + shift; CancelR's residue) —
fixable in the rules with the frames already computed by the proven
cases.  IdPush is the one that may be a genuine DESIGN question (its
swapped-face typing obligation is the old chained-rep shape) — probe
whether the c10/c11 configuration is even reachable under v2's rules, or
whether IdPush needs a scoping premise / a different contractum.  NEXT:
repair the three local bugs, then settle IdPush by reachability probe;
each repair is validated by instantiating `Conditional`.

### IdPush reachability probe (proof/IdPushReach.agda, 2026-09-05)

VERDICT: the refuting configuration (an unbind in Θ₂ blocking the slot the
id-face's owner-rep names) is reachable ONLY through the Peel/dual bug
(dualS's `bind X ↦ unbind (n+X)` defect); under the repaired dual the
only unbinds a Peel ever mints are lockBinds of the crossed boundary's OWN
new binders, and by SIMULTANEITY (an owner's rep is a type over the
plain exterior, lifted past the owners bound inside it) those never
block a face's rep.  The exact fact the swapped-face contractum needs
and the redex does not provide: `intC Θ₂ Δ ⊢ᵗ A` (scoped-fails on the
witness; owner-holds still true).  Machine-checked: adding that premise
to IdPush makes its preservation case PROVABLE (idPush⁺ : IdPushCase⁺;
idPushCase-scoped shows the companion owner-lookup follows from the
redex typing via MaskOnly — the one interface lemma left un-rederived).

SUPERVISOR'S CAUTION (the v1 lesson): the premise route trades the
preservation break for a PROGRESS hole unless typing excludes the bad
configuration — the ¬IdPushCase witness is WELL-TYPED (Bwf's bw-l asks
only that the unbound slot exist), so with the premise IdPush would not
fire on it and progress would lose a well-typed non-value.  Grounded
resolution options: (α) Bwf strengthening so an unbind may not block a
slot that a visible owner's rep names (makes the witness ill-formed;
non-local — needs a formulation), or (β) Jeremy's hunch — a
CONTRACTUM that never presents A inside Θ₂'s unbinds (the swapped face
forces the inner wrapper to EXPORT the rep into a region that cannot
name it).  The trace Jeremy asked for was NOT built (the agent judged it
redundant post-repair); to be built if wanted.  Open for ruling after
the three-bug fix lands.

### Peel FIXED and PROVEN; CancelR/TyPeelR/IdPush share ONE wall (2026-09-05)

Peel/dual repair landed: `dualS` drops the `bind` case (a no-op bind
must dualize to nothing — fixes both the no-op→unbind defect and the
same-slot cancellation), `intC-dual : intC (dual Θ) (intC Θ Δ) ≡
map blk (prep (reps Θ) []) ++ fscp Θ Δ` and `fceC-dual` PROVEN in general
(proof/PeelDual.agda); `PeelCase` discharged; Conditional now over
(typeel, cancel, idpush).  det/value-¬step/examples unchanged.

THE FINDING: CancelR and TyPeelR are NOT local bugs — they hit the SAME
wall as IdPush.  CancelR's honest contractum (keep both frames,
neutralize the faces: `(V ⟪ Θ₁ , idc (liftN (nbind Θ₁) A) ⟫) ⟪ Θ₂ , idc
A ⟫`) fixes the frame-drop but demands `intC Θ₂ Δ ⊢ᵗ A` — failing
exactly when Θ₂ unbinds a slot A names while Θ₁ re-exposes it (the IdPush
§4 witness with seal for id).  TyPeelR's annotation must be the
INTERIOR ∀-body, i.e. the SOURCE of the face `s`, which is not
syntactically recoverable for `↓ˢ` conceal faces (a seal's source is a
rep, absent from the rep-free conversion) — closable for `↑ˢ` reveal
faces via a `srcOf : Conv → Ty` reconstruction, not in full generality.
Common denominator: a contractum's inner wrapper must PRESENT A REP
inside Θ₂'s interior; rep-free conversions + masks make that either
non-syntactic (TyPeelR) or ill-scoped (CancelR/IdPush).  DESIGN
QUESTION for Jeremy, informed by the re-probe: is the wall REACHABLE
post-repair (simultaneity says no for IdPush); if not, a grounded
Bwf/typing invariant makes the offending configurations ill-formed and
the `intC Θ₂ Δ ⊢ᵗ A` facts derivable; if yes, contracta must be
reformulated so no inner wrapper presents a rep under an unbind.

### First closed-source IdPush traces + the wall's reachability (2026-09-05)

Examples §11: Q = ((ΛY. λx:Y. ((ΛZ. x)·[Y,ℕ]))·[Y⇒Y,ℕ])·7 — the FIRST
IdPush ever reached from plain System F (8 live steps to 7; TyBeta,
Peel, Beta, TyBeta minting id (` 1), IDPUSH, CancelR, Drop$, Drop$; all
states typed; IdPush's contractum TYPES).  Variants: D (IdPush twice —
stacked vacuous Λs; both contracta type), R (chained face rep, three
IdPush firings; types — the exported rep lands where it is nameable).
Variant (i) nontrivial Θ₁ REQUIRES TyPeelR (nbind arithmetic:
TyBeta≡1, dual≡0, CancelR preserves, TyPeelR≡suc) and G₀ =
((ΛX. λx:X. ((ΛY. ΛZ. x)·[ℕ])·[ℕ])·[ℕ])·7 gives ¬⊢G₅ — THE FIRST
CLOSED-SOURCE REFUTATION OF TyPeelR, from the `renᴮ suc Θ` double-shift
alone (the face is an identity, so the annotation defect is not what
fires); K shows the multi-bind frame types once the shift is fixed.

Examples §12 + proof/WallReach.agda — THE WALL: reachable? SPLIT.  L₀
(instantiate the vacuous ΛZ at Y instead of ℕ) reaches the c10/c11
blocked-context shape from closed source — but only at a Θ₁ (inert
seal-faced) position; every Θ₂ on the run is unbind-free and IdPush's
contractum types.  INVARIANT RepWf Ξ ("no unbind blocks a slot a NAMEABLE
owner's rep names"): closure under abst/bind/blk/prep proven
(RepWf-prep = simultaneity: prep stores reps lifted past inner owners);
the wall itself is a theorem (mask-breaks-RepWf); THE ANSWER RepWf-dual:
a Peel's unbinds can never block a rep, no side condition on Θ (one line
off intC-dual); PAYOFF: unseal-scoped gives `intC Θ Δ ⊢ᵗ A` at every
unseal-faced wrapper from RepWf + MaskOnly, idPush-RepWf DISCHARGES
IdPush's case over the invariant (no rule premise), cancelR-scoped the
same for CancelR's honest contractum.  LIMIT: the global term invariant
WallFree is REFUTED on reachable L (¬wall-step) — the carried invariant
must be "RepWf at every Θ₂"; its mint obligations (TyBeta/Peel/CancelR/
binds-only frames) are all discharged; REMAINING = the term-level
induction's ⊑/renaming/substitution transports for the Θ₂-only predicate
(stated, not faked).

READ: IdPush is RIGHT as formulated — it needs only the grounded fact
RepWf supplies.  Remaining design items for Jeremy: (1) TyPeelR — fix
the double-shift (mechanical) and rule on the annotation: srcOf closes
↑ˢ faces; ↓ˢ ∀-faces (a polymorphic ARGUMENT crossing) need either a
stored source type or a different elimination; (2) CancelR's honest
contractum (keep both frames, faces idc) is a rule change to approve;
(3) finish the Θ₂-RepWf induction → IdPush + CancelR discharge with
zero rule premises.

### Rule repairs LANDED; the invariant hunt; polarity is the TyPeelR blocker (2026-09-06)

Jeremy ordered (2026-09-05): "land both repairs and proceed to finish
the preservation proof".  LANDED (Reduction.agda):

    CancelR : Value V → fceC Θ₂ Δ ∋ Y := A
      → (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
        -→ (V ⟪ Θ₁ , idc (liftN (nbind Θ₁) A) ⟫) ⟪ Θ₂ , idc A ⟫
    TyPeelR : Value V → (abst ∷ fceC Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ ∙ p
      → (V ⟪ Θ , `∀ s ⟫) ·[ B , A ]
        -→ (wkᴹ 1 V ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ]) ⟪ bind A ∷ Θ , unsealAtᶜ 0 s ⟫

The RuleRepairs note MISSED one defect: the pushed face `s` still names
the bound variable in its target while env demands liftN (n+1) (Bₑ[A]);
the new bind slot needs the instantiation leaves — `unsealAtᶜ`, the Conv
analogue of TyBeta's unsealAt (unsealAtᶜ X (idc B) ≡ unsealAt X B).
det/value-¬step re-proven (conv-faces-unique: faces are a function of
conversion + context).  CancelRCase DISCHARGED (proof/CancelFaces) over
one interface, ScopedAtUnseal (proof/ScopedAtUnsealDef): "at a
well-typed (V ⟪Θ₁,c₁⟫) ⟪Θ₂, unseal Y⟫ with Y := A, intC Θ₂ Δ ⊢ᵗ A".
TyPeelRCase↑ (↑ˢ face) PROVEN (Preservation.preservation-TyPeelR-↑);
Examples §13b H runs it.  MaskOnly is a theorem (MaskFacts.mask-only).
Conditional = (typeel : TyPeelRCase) (scoped : ScopedAtUnseal) (idpush).

POLARITY VERDICT (Examples §13, machine-checked): closed source
  (((ΛX. λx:X. λy:(∀Y. Y⇒X). y[X]·x)[ℕ]·7) · (ΛX. λx:X. 3))
reaches the TyPeelR redex ((ΛY. λx:Y. 3) ⟪ ↓X , ∀Y. (id Y ↦ seal X) ⟫)[X]
— a ↓ˢ ∀-face (a polymorphic ARGUMENT that crossed a Peel).  Keeping `s`
is untypeable (¬⊢J-plain); unsealAtᶜ 0 s = seal 0 ↦ seal 1, whose
leaves each type alone but whose tree types at NEITHER polarity
(¬seal↦seal: the inserted domain seal needs flip p = ↓ˢ, the covariant
seal needs p = ↓ˢ).  So ¬TyPeelRCase is now a fact about the POLARITY
DISCIPLINE, not the rule.  notes/polarity-relaxation.patch (NOT applied)
frees conv-seal/conv-unseal from their fixed polarity: with it the full
TyPeelRCase discharges; collateral = Canonicity §5 (typed→canon,
canon-pol, pol-unique) becomes FALSE, i.e. `p` is vacuous and the honest
form is to DROP Pol; nothing else breaks.  RULING NEEDED (Jeremy).

THE INVARIANT HUNT (IdPush/CancelR need intC Θ₂ Δ ⊢ᵗ A), all refuted
by machine, proof/WallGrounding + proof/ScopedFace (phase-one worktree,
to land next):
 (1) RepWf folded into Bwf's unbind clause — IMPOSSIBLE: the unsound
     IdPush witness Ri and the reachable L₄ have the SAME (Δ, Θ); and
     RepWf of the interior is not ⊑-stable at le-ao (TyBeta refines
     abst→bind under existing unbinds): BwfWall → ¬TyBetaCase.
 (2) Scoped = exterior type wf in scp Θ Δ, on reveal faces — ⊑-stable,
     refuses Ri, admits L₄, and the ↓ˢ-Peel crossing is dischargeable
     (peel-crossing-scoped) — but TOO WEAK: IdPush's swapped inner face
     owes X's REP (R★: ¬ScopedAt ↑ˢ Ξ★ Θ★₁ (` 2) while the redex passes).
 (3) pointwise RepWf at name-faced boundaries — hand-refuted by
     (ΛX′. λx′:X′. ((ΛZ. λx:X′. (ΛY. x)[Z])[ℕ] · x′))[ℕ] · 7 (TyBeta
     mints Y := Z under the unbind Z of an id-faced wrapper); kill test in
     flight.
 Candidate under probe: CHAIN-scoped — at faces naming X, every rep
 reachable from X by owner lookup is wf in the interior.
 UPDATE (same day): (3) CONFIRMED by machine (proof/ChainScoped
 ¬NameFacedRepWf: the program above runs 7 steps; the TyBeta at Z mints
 Y := Z around the id-faced unbind-Z wrapper, both states type, RepWf
 fails after).  CHAIN-scoped (Reach/ChainScoped, VERBATIM in the file):
 refuses Ri and R★, admits L₄ and the kill test, is PRESERVED by IdPush
 (both frames and names kept, only faces swap) and by CancelR's residue
 (chain-mono: the idc leaves' chains are Y's), needs NO lifting — but is
 NOT ⊑-stable (¬ChainFaced): a chain STOPS at a Λ-bound abst slot and
 TyBeta gives that slot a rep, so the chain runs on into whatever the
 instantiating type names (hand-built typed redex CR; le-ao a third
 time).  My reachability reading of CR: NOT reachable — a crossing
 wrapper's face variable is visible at the exterior of the boundary it
 is dual to, so its owner (and its whole chain, reps being read at the
 owner's exterior) is OLDER than every unbind the wrapper carries, and a
 chain never enters a younger Λ.  That suggests the STABLE form is an
 ORDER condition: every variable on the chain of the face's name is
 older than every unbind in Θ (the face's own name may be the unbound one
 — the seal-crossing case).  It refuses R★ (X younger than the unbind) and
 CR (chain hits the abst at slot 1, unbind at 2) and admits L₄/Q/kill
 test; ⊑-stability: a refinement of a chain slot Y reads its rep at Y's
 exterior, hence older than Y, hence older than the unbinds.  OPEN RISK:
 TyPeelR's mint `bind A ∷ Θ` where A names a slot Θ unbinds (Examples §13:
 bind X ∷ unbind X) puts an unbound slot on the new bind's chain — either
 the order condition refuses a reachable state, or that state is the
 wall itself and TyPeelR must be restricted/reformulated.  NOT probed;
 Jeremy to rule on direction before more invariant hunting.

### RULING: polarity dropped from the conversion judgment (Jeremy, 2026-09-06)

Trace artifact "Two Polarities, One Rule" (Examples §13, every state
machine-rendered; renderer now gives globally unique type-binder names,
cc97298c).  J₆ (b), the landed TyPeelR contractum
  ((ΛZ. λx:Z. 3) [Y]) ⟪ ↑Y:=X , ↓X , (seal Y ↦ seal X) ⟫
is untypeable ONLY because the two seals demand opposite values of the
single index p (domain seal Y wants flip p = ↓ˢ, codomain seal X wants
p = ↓ˢ).  Jeremy: "I'm wondering if the invariant is really one polarity
per type variable, not one polarity for all type variables.  However, do
we really need polarity at all?"  Analysis: per variable the face IS
consistent — each variable's name sits on the side where it is a name
(Y: bind, interior side; X: unbind, exterior side) — and that per-variable
fact is already enforced by env's frames (an unbound X is masked in intC,
a bound X is not in the image of liftN), so `p` is a redundant summary
that is uniform only for single-kind boundary scopes and breaks the first time
a mint mixes kinds (TyPeelR's `bind A ∷ Θ`).  Nothing uses p for work
(det/progress/canonical forms go by face shape; the relaxation experiment
showed only Canonicity §5 dies, whose content was p).  Considered and
recorded (Examples §13c): Jeremy's candidate ⟪ ↑Y:=X , ↓X , id X ↦ seal X ⟫
is untypeable as written (id X vs interior domain Y; instantiating at X
is masked) but types with the unbind lifted/removed (Cu/Cr); the
resolve-through-unbinds variant (Cb/CbH) also types.  None needed once p
is gone.  RULED: "go ahead and drop polarity, then finish TyPeelR".
Consequence: TyPeelR as landed is THE rule; Conditional shrinks to
(scoped : ScopedAtUnseal) (idpush : IdPushCase) — the two are one fact.
Regularity (typed terms have well-formed types) is the lemma that makes
the per-variable invariant a theorem; to be stated if wanted.

### PRESERVATION PROVEN, PARAMETER-FREE — Jeremy's unbind-moving contractum (2026-09-06)

Jeremy: "Regarding IdPush, I'm contemplating whether part of Θ₂ should
sometimes be moved to the inner boundary in the contractum.  For example,
in R₁, the ↓X could be moved to the left of the unseal Y, into the inner
boundary."  Machine-checked first on the wall witness (R₁′ types: the
value's frame is unchanged, the rep is presented OUTSIDE the unbind), then
generalised (proof/MoveScope.agda, artifact "The Wall"):

    moveS n Θ      -- Θ's unbinds AND binds (binds dropped), indices lifted by n
    bound Θ     -- Θ with its unbinds removed (binds and binds stay)
    Θ₁ ◃ Θ₂ = Θ₁ ++ moveS (nbind Θ₂) Θ₂

    IdPush  : (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫
              -→ (V ⟪ Θ₁ ◃ Θ₂ , unseal X ⟫) ⟪ bound Θ₂ , idc A ⟫
    CancelR : (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
              -→ (V ⟪ Θ₁ ◃ Θ₂ , idc (liftN (nbind Θ₁) A) ⟫) ⟪ bound Θ₂ , idc A ⟫

The whole scope (unbinds and binds, order kept) moves; the binds are
also retained in Θ₂′.  Moving ONLY the unbinds is REFUTED in-tree (MoveScope
§4b: Θ✗ = bind 0 ∷ unbind 0, Bwf-legal; scp applies head-last, so an unbind
moved past a same-slot bind flips the mask).  Frame lemmas, all
unconditional: intC-bound (intC (bound Θ) Δ ≡ fceC Θ Δ — the outer
frame IS the face frame), scp-moveS, frame-move / face-move (REFINEMENTS
⊑, not equalities — the retained unmasks apply twice; ⊢retag carries
them), move-∋, Bwf-◃, nbind-◃.  The premise the wall asked for,
intC Θ₂ Δ ⊢ᵗ A, becomes intC (bound Θ₂) Δ ⊢ᵗ A = fceC Θ₂ Δ ⊢ᵗ A, which
follows from the redex typing (A ≡ liftN (nbind Θ₂) C, Δ ⊢ᵗ C,
wf-liftN-prep).  Both cases typed on the first attempt.

RESULT: strong-rep-nu.Preservation has top-level `preservation : Preservation`
and `preservation* : Preservation*` — no Conditional module, no
ScopedAtUnseal, no RepWf, no MaskOnly.  det re-proven, value-¬step and
Progress unchanged.  Deleted: proof/CancelFaces, proof/ScopedAtUnsealDef,
preservation-fails/¬preservation, ¬IdPushCase (PreserveObstruct §4 now
records the POSITIVE fact: the old wall witness steps to a typed term and
on to a value, Examples §12b R₀ → R₁′ → R₂).  Example ripple: one pinned
trace (§4 Tₘ, Θ₂ = bind 0) changed shape; Q/D/R/L/K/J unchanged (binds-
only Θ₂: Θ₁ ◃ Θ₂ ≡ Θ₁ computes).  KEPT AS RECORDS (compiling, banners):
proof/WallReach, WallGrounding, ChainScoped, IdPushReach — the invariant
hunt for a premise that no longer exists; recommended for deletion
(Jeremy's call; closed-world repo).  The design lesson: the wall was
never a missing invariant — the rule put the rep on the wrong side of
the unbind.  NEXT: TypeSafety.agda (progress + preservation, top-level
wrappers), README/Design, PR #190 body.

### RULING: helper names (Jeremy, 2026-09-06)

The v2 helpers were over-abbreviated ("scp (secure copy?), fscp, intC,
fceC") and "face" is retired in favour of a boundary's INTERIOR and
EXTERIOR (Jeremy's slides already use interior(Θ,Δ)/exterior(Θ,Δ)).
Final map, applied as one mechanical pass (lemma names follow):

    intC → interior        fceC → exterior
    scp → scope            fscp → unlockedScope
    prep → pushBinds       reps → repsOf          nbind → numBinds
    liftN → shiftBy        liftᵇ → shiftBodyBy    upd → updateAt
    blk → masked           unblk → unmaskEnt      Vis → Nameable
    Bwf → BoundaryWf (bw[]/bw-b/bw-l/bw-u → bw[]/mw-b/mw-l/mw-u)
    idc → mkId
    unsealAt/sealAt → reveal/conceal        (amended from revealAt/concealAt)
    unsealAtᶜ/sealAtᶜ → instReveal/instConceal
    dual KEPT              dualS → dualScope      lockBinds → hideBinds
    moveS → scopeOf        bound → dropLocks   _◃_ → _⋉_
    kept: Θ, bind/unbind/bind, abst, mask/unmask, Inj.

Reading: `exterior Θ Δ` is not the plain Δ the whole term is typed in
but Δ as seen from the boundary (binds pushed, binds applied); the
identity `interior (dropLocks Θ) Δ ≡ exterior Θ Δ` is the one that
retired the wall.  Earlier entries of this log use the old names.

### Naming correction: `exterior` → `convCtx` (Jeremy, 2026-09-06)

The helper fceC had been renamed `exterior` after Jeremy's slides, but it
is NOT the type context at the boundary's exterior (that is the plain Δ):
fceC Θ Δ = pushBinds (repsOf Θ) (unlockedScope Θ Δ) — Δ with the
boundary's binds pushed and its unbinds lifted.  Jeremy: "fce is not the
same as the context at the exterior of the boundary … 'conversion
context' is a phrase you use.  Then we can use 'exterior' to mean 'plain
exterior'."  RULED: the function is `convCtx Θ Δ` (conversion context);
"exterior" means the plain Δ everywhere.  Why a separate context: the
conversion names the boundary's own binds (absent from Δ) and cites
owners by lookup, including unbound ones (masked in the interior), so it
types in neither; convCtx = interior (dropLocks Θ) Δ is the smallest
context where both resolve (Design.md §3).

### RULING: "face" retired from the development (Jeremy, 2026-09-06)

The word "face" (for a boundary's conversion and its two types) is
retired from identifiers, comments and notes of strong-rep-nu/ (v1 memos,
notes/old and this log keep their vocabulary).  Speak of the boundary's
CONVERSION `c`, its SOURCE type (the interior type) and TARGET type (the
exterior type shifted by numBinds), the boundary's INTERIOR and EXTERIOR,
and the CONVERSION CONTEXT `convCtx Θ Δ`.  Consistency rule: "exterior"
means the plain Δ and nothing else.  Identifier map: conv-faces-unique →
conv-types-unique, unseal-face-is-the-owners-rep → unseal-target-is-rep,
seal-face-is-the-owners-rep → seal-source-is-rep, inert-*-face →
inert-*-conv, J-face-ctx/t-face-ctx → J-convCtx/t-convCtx, ⊢Hface/⊢Gface/
⊢Pk-face → ⊢Hconv/⊢Gconv/⊢Pk-conv, face-move → convCtx-move,
∀-face-premise → ∀-conv-premise, ¬ChainFaced → ¬ChainConv.
 ADDENDUM (Jeremy, same day): `BoundaryWf Δ Θ` becomes the infix judgment
 `Δ ⊢ᵐ Θ` (the boundary scope Θ is well formed over Δ), in the family
 of `Δ ⊢ᵗ A` and `Δ ⊢ c ∶ A ⇝ B`; constructors bw[]/mw-b/mw-l/mw-u stay;
 lemma names follow (⊢ᵐ-⊑, ⊢ᵐ-⋉, …).

### RULING: "binder" instead of "owner" (Jeremy, 2026-09-06)

The bind entry ↑X:=A of a boundary is X's BINDER (it binds X and carries
its representation A); "owner"/"ownership"/"owner lookup" are retired
from Design.md, README, comments and identifiers (abstN-owner →
abstN-binder, unseal-owner → unseal-binder, owner-holds → binder-holds,
abst-not-owner → abst-not-binder, ¬canonC-two-owners →
¬canonC-two-binders, seal-cites-owner → seal-cites-binder).  `Δ ∋ X := A`
is the binder lookup.  Where "binder" would be ambiguous with Λ/∀/λ
binders, prose says "the `bind` entry for X" / "Λ-bound X".  Historical
memos and this log keep the old word.

### RULINGS before PR #190 leaves draft (Jeremy, 2026-09-06)

(1) DELETE the four invariant-hunt record files proof/WallReach,
WallGrounding, ChainScoped, IdPushReach — the refutations they carried
are recorded in this log (2026-09-06 entries "the invariant hunt" and
its UPDATE) and in the artifacts "The Wall" and "Two Polarities, One
Rule"; nothing in the development depends on them.  (2) MOVE PLAN.md
(the superseded PR #189 handoff for v1) to notes/old/PLAN-v1.md.  (3)
The `_⊑ᵉ_` constructors lose their owner/blocked initials: le-ao → le-ab
(abst ⊑ bind), le-oo → le-bb (bind ⊑ bind), and the masked pair le-bb →
le-mm, le-bu → le-mu; le-aa stays.  Then the PR is marked ready for
review.

### Peel's dual is NOT tight for `bind` entries (Jeremy's test, 2026-09-06)

Jeremy: "I don't fully understand the definition of dual and not sure I
trust it … create an example program that takes a Peel step, and the
program should have an ill-formed type in the argument W, and after the
reduction step, W wrapped in the dual boundary should still be
ill-formed."  RESULT (proof/DualTightness.agda): bind entries are tight
(wkᴹ shifts W's indices past them) but `dualScope` DROPS binds, so with
exterior ⌷[X := ℕ], Θ = ↥X, W = λx:ℕ. (ΛY. 3)[X] (names the masked X;
ill-typed), the redex `(V ⟪ ↥X , c ⟫) · W` is ill-typed and its Peel
contractum is WELL-TYPED (W's frame inside is bind ℕ: X visible).  Scope
is gained through the boundary — design law 2 fails for the RELATION
(not a preservation failure: the redex is ill-typed).

PROBED FIX, REFUTED (proof/MwUObstruct.agda): (1) mw-u requires a masked
slot, (2) dualScope maps bind ↦ unbind, (3) the scope move's outer frame
becomes bindsOnly.  (3) alone is GOOD: interior-⋉-bindsOnly and
convCtx-⋉-bindsOnly are EQUALITIES (frame-move's ⊑ was an artifact of the
retained binds).  But (2) forces (1) (a vacuous bind, legal today,
makes preserve-Peel false under dual′), and (1) kills ⊢ᵐ-⊑ hence ⊢retag
(le-mu: Cancel's own refinement unmasks a slot a bind cites) and kills
⊢ᵐ-⋉ (⋉ builds lists that unbind AND bind one slot; under (1) mw-l and
mw-u are exact complements so no SIMULTANEOUS ⊢ᵐ can hold — §3/§4 mirror
witnesses).  Structural reason: `_⊢ᵐ_` is simultaneous (law 4), `scope`
is sequential.  Sequential ⊢ᵐ (§5/§6) would force dualScope to reverse
and mw-b's rep to be read sequentially — colliding with simultaneity.
NEXT CANDIDATE (δ), to probe: leave ⊢ᵐ alone and make the dual read the
EXTERIOR: `dual Δ Θ` maps `bind X ↦ unbind X` only when X is masked in Δ
(reduction is Δ-indexed, so Peel may inspect Δ; simultaneity respected —
one read on the plain Δ).  Then vacuous binds add nothing (preserve-Peel
survives), non-vacuous ones are re-unbound (the leak closes), and
`interior (dual Δ Θ) (interior Θ Δ) ≡ masked binds ++ Δ` should be exact
with no change to the scope move.

### RULING: vacuous binds are wrong and unreachable (Jeremy, 2026-09-06)

Jeremy: "why do we allow ↥X over X := ℕ visible?  That feels wrong … and
unreachable."  RULED: the judgment must refuse them (mw-u's slot must be
masked).  Hint for the probe: "my feeling is you're missing a few
premises … look for places where information is dropped."  Two probes
run in parallel, both non-landing: (δ) branch dual-relock — a Δ-dependent
dual that re-unbinds only non-vacuous binds, leaving `_⊢ᵐ_` alone; and
the PRINCIPLED package, branch dual-principled — audit of dropped
information (mw-u's maskedness, dualScope dropping binds, the scope
move's dropped entries, `_⊢ᵐ_` reading scope premises on the plain Δ and
so dropping order, le-mu forgetting maskedness, Peel's crossing retype,
mw-b's rep independence from the same boundary scope's binds), then:
masked-only mw-u with SEQUENTIAL scope premises (reps stay on the plain
Δ — simultaneity), dualScope restoring bind ↦ unbind, ⊢retag over the
non-unmasking refinement only, scope move with bindsOnly outer frame
(frame lemmas as equalities).  Expected sticking point: Θ₁'s bind reps
under the move (MwUObstruct §6) — the missing premise, if any, is there.

### RATIFIED: representations read past the tail's binds; PR #193 merged (Jeremy, 2026-09-06)

Jeremy ratified item 2 of the tight-boundary package (mw-b reads a
bind's representation on `unlockedScope Θ′ Δ`, the frame the conversion
is read on; names in unbind/bind entries are read on `scope Θ′ Δ`) and
ordered PR #193 merged: "That particular law was not valuable on its own,
it was just a design idea to try."  Design law 4 ("Simultaneity") is
thereby reduced to its surviving half — a representation is never blocked
by its own frame's unbinds, and `pushBinds` lifts it past exactly the
binders inside it — and the "every premise on the plain exterior" half is
retired.  Landed with it: sequential `Δ ⊢ᵐ Θ` (no vacuous binds, no
double unbinds), the exact dual (†), `rewind Θ₂` as the scope move's outer
frame, `⊢retag` over `⊑ᵃ`.  Branch dual-relock (Δ-dependent dual) is the
superseded alternative; PR #192 is contained in #193.

### The boundary scope becomes a PAIR (Jeremy, 2026-09-06)

Jeremy, reading `dual`: binds are treated specially (hideBinds, all at the
front) while unbind/bind are sequential — "is that essential … perhaps
the main difference between the current design and the very first design
with single reveal/conceal … should we keep the list of binds separately
from the list of unbind/bind?"  Analysis: the special treatment IS
essential (binds are PARALLEL — reps read outside all of the boundary scope's
own binders, the surviving half of simultaneity; unbind/bind are
SEQUENTIAL — the sequential ⊢ᵐ, the reversed dual and rewind depend on
it; the very first design was the fully sequential composition and died
on the drifted ↓X), but the INTERLEAVING was not: interior/convCtx/dual/
rewind/⋉ never used bind-vs-change order; only mw-b's rep frame did
(tail's binds).  RULED: refactor into a record `boundary binds changes`
(field name `changes`, Jeremy's choice; entry type `Change` with
unbind/bind), `Δ ⊢ᵐ Θ` = `unlockedScope Θ Δ ⊢ʳ binds Θ` × `Δ ⊢ˢ
changes Θ`.  ONE semantic change: a rep is read past ALL of the
boundary scope's binds (not just those listed after it) — strictly more
permissive, no theorem weakened, no example affected (every reachable
boundary scope has all binds before all changes); the one lemma that pays is
⊢ᵐ-rewind (rewind's inverse half adds unmasks).  Lemma deltas: 8 repsOf
lemmas deleted, 3 numBinds lemmas became refl, ⊢ᵐ-++ vanished (⊢ˢ-++ is
rep-free), 26 change-list inductions lost their bind case.  Rendering
unchanged.  Branch morph-pair, PR to follow.

### Entries are a binding plus at most one unbind (Jeremy, 2026-09-08)

Jeremy: "Split it into two types so that masked is no longer recursive.
I don't want to allow more than one masked."  LANDED (branch ent-binding):
`data Binding = abst | bind A` and `data Ent = unmasked Binding | masked
Binding`.  One-mask-deep is now BY CONSTRUCTION: `Unbound (masked b)` has
no Nameable premise, `_⊑ᵉ_`/`_⊑ᵃᵉ_` are lifts of one `_⊑ᵇ_` on bindings
(la-aa/la-ab/la-bb subsumed), `unmaskEnt-nameable` and MaskFacts' `core`
family vanished, a dozen recursive entry lemmas became two-clause lifts.
The one honest cost: `maskEnt` is idempotent, so `unmask X (mask X Δ) ≡ Δ`
needs `Δ ∋tv X` (witness: Δ = masked abst ∷ [], X = 0) — the premise `sw-l`
always has; threaded into applyUnlocks-dualScope and convCtx-dual.  The
two mask inverses are now symmetric (`mask-unmask : Δ ∋lk X → …`,
`unmask-mask : Δ ∋tv X → …`).  Rendering unchanged.

### Frame-exact Beta: substitution wraps values crossing a Λ (probe, 2026-09-08)

Jeremy, reading the slide trace of `(ΛX. λf:(∀Z.Z→Z). ΛY. f [Y]) [ℕ] ·
(ΛZ. λz:Z. z)`: "On the fourth step, is there a missing −Y in the
boundary around the ΛZ?"  Yes: Beta's substitution moved the crossing
wrapper under ΛY and its interior became `Y Λ-bound , ⌷[X := ℕ]` — the
value's frame GAINED Y (harmless via indices, but not frame-exact; every
other rule is exact).  PROBED and LANDED on branch exact-beta:
substitution carries the value's type and wraps every value image that
crosses a Λ in the binder's dual with an identity conversion,
`crossΛ W A = ⇑ᴹ W ⟪ boundary [] (unbind 0 ∷ []) , mkId (⇑ᵗ A) ⟫`; Beta is
`(ƛ A ∙ N) · W -→ N [ W ∶ A ]ᵐ`.  Images are a two-constructor type
(variable / closed value with its type), since env types a boundary's
interior at Γ = [].  The boundary-interior half of the gap is VACUOUS:
substitution never descends into a wrapper (term-closed), and Peel's
crossing is already exact by (†).  Frame identity `interior (boundary []
(unbind 0 ∷ [])) (unmasked abst ∷ Δ) ≡ masked abst ∷ Δ` by refl; Examples
§15 gains the under-Λ Beta case (still refused) and §14 shows the ↓Y
Jeremy expected at E₃/E₄.  Value/progress/det/canonical forms unchanged;
at a base type the minted `id ℕ` is active, so a numeral crossing a Λ
costs one extra Drop$.  Step-count deltas: Q 9→11, D 12→16, R 18→21,
L 9→11, E 5→6; P₀, G, J, H, Ri unchanged.  Alternatives costed in
notes/PR-exact-beta.md (extend an existing wrapper's changes; one
composed dual per substitution path).  Awaiting Jeremy's ruling.

### RULING: TyPeelR split into TyPeelR-Λ / TyPeelR-⟪⟫ (Jeremy, 2026-09-08)

THE PROBLEM (shift audit after #199, PR #201).  The live TyPeelR shifted
its value `V` by `wkᴹ 1` under the new bind slot `X := A`, which is
UNMASKED in V's frame although V was authored where it did not exist.
The §15b index test cannot see this — the shift makes the slot
unreachable from V — but the frame does not tell the truth: the live
frame and the tight frame differ by exactly one `le-mu`, the
re-exposure step `⊑ᵃ` refuses (ShiftAudit `TyPeelR-leak-⊑`).  Jeremy
first read the "V" as another subterm and called it not a tightness
problem, then confirmed: "I see the problem now".  Every other shift
site (Peel, TyBeta, Beta with crossΛ, CancelR/IdPush, Drop$, ξ) is
frame-exact by a machine-checked identity.

THE CANDIDATES, on the §15b example, machine-checked in
proof/ShiftAudit.agda:
  (a) wrap V in the binder's dual `⟪ ↓X , ∀ id ⟫` — REFUTED: the only
      identity at a ∀ type is `∀ (mkId …)`, inert, so the wrapper is a
      TyPeelR redex again; `fixA-loop-step` proves the regress, a closed
      run adds one boundary per step and TyBeta never fires.
  (b) split on the canonical form of V.  For `Λ N` the contractum is
      `N ⟪ boundary (A ∷ binds Θ) (changes Θ) , instReveal 0 s ⟫`: NO
      shift, the Λ's abst slot becomes the boundary's bind slot
      (TyBeta's own refinement).
  (b′) for a nested `W ⟪ Θ′ , ∀ s′ ⟫`: the moved inner boundary gets
      `unbind 0` appended at the TAIL of its own shifted change list
      (`addUnbind0`), no wrapper minted; contractum = the live one with
      `addUnbind0ᵛ` on the moved value (`TyPeelR-⟪⟫-wkᴹ`, refl).  Inner
      interior ≡ birth frame with the new slot inserted MASKED.
      Terminates: tower height drops by one per step, height 0 is a Λ.
  (c) resolve A inside the interior — exact for V but writes the
      exterior's representation into the interior: a KNOWLEDGE leak.
      Rejected.

RULING.  Install (b)+(b′), replacing TyPeelR by the pair (canon-∀ makes
the pair total, so progress's single TyPeelR case becomes a two-way
split).  Jeremy asked "do we have Progress?" — answered: the probe
proved only the `·[]` case; the full theorems are re-checked by the
install gate.
INSTALLED on branch typeelr-split (PR "TyPeelR split").  Side effect
measured in Examples: the Λ clause performs the instantiation itself,
so one type instantiation mints ONE binder where TyPeelR ⨟ TyBeta minted
two — J₀ 14 → 11 steps, E₀ 6 → 5 (ends in a value), T₉'s birth story
2 → 1 step; P₀ Q₀ R₀ L₀ Ri G unchanged.

## THE RE-BIND CLAUSE (2026-09-17, representation-variable branch)
## — finishing the fourth reduction example broke `rewind` and `_⋉_`

CONTEXT.  notes/PLAN.md item 1 asked for the fourth example,

    ( ΛX. λf:(∀Z. Z⇒Z). ΛY. f [Y] ) [ℕ] · (ΛZ. λz:Z. z) , then [𝔹] · true

run to a first-order value with an explicit typing derivation at every
state.  The first five steps were already checked; the continuation is
where the two-universe design is actually under load, because the value
that must reach `true` has crossed THREE boundaries and carries three
seals, and unwinding them is what drives `CancelR` and `IdPush`.

THE DEFECT.  The eleventh step is `CancelR`, whose contractum is

    (V ⟪ Θ₁ ⋉ Θ₂ , mkId A ⟫) ⟪ rewind Θ₂ , mkId A ⟫ .

Here Θ₂ is `instantiate (` 0) ΘE-moved`, which UNBINDS: it is `TyPeelR-Λ`'s
frame over a boundary that had already crossed two `Λ`s, so its change
list is `unbind 1 3 ∷ unbind 1 1 ∷ bind 0 0 ∷ []`.  Both of the contractum's
frames append the DUAL of that list — `rewind Θ = dual (changes Θ) ++
changes Θ`, and `Θ₁` is the argument's `dualBoundary Θ₂` from the `Peel` that
sent it across.  The conversion context SKIPS an `unbind` (that is the whole
point: the conversion must still be able to name the concealed variable),
so when the dual's matching `bind` arrives, the name is still live and
the `Fresh α Δ₂` premise of `conv-bind` fails.

So `rewind Θc` and `dualBoundary Θc ⋉ Θc` have NO conversion context, `env`
cannot type the contractum, and preservation fails at `CancelR` — and at
`IdPush`, which has the same two frames.  Machine-checked:
`no-old-rewind-conv` (strong-rep-store/notes/ReUnlockWall.agda, against a local copy of the
two-clause judgement as it stood).  Every state up to
and including the redex is well typed, so this is a defect in the rule
set, not in the example.

Note this could not show up in examples 1–3: their `CancelR`s all have a
unbind-free Θ₂ (`TyBetaBoundary`, or a `⋉` of it), and for an unbind-free Θ the
dual is all unbinds, which the conversion context skips.

THE RULING.  The conversion context is the UNION of the names live
anywhere along the boundary scope — that is what "skips `unbind`s" means.  Read
that way the old judgement was simply not total: a `bind` of a name
that is already live is a NO-OP, and the missing clause is

    conv-bind-live : ValidRVar Ξ α → Ξ ∣ Δ₁ ⊢χᶜ χ ⇒ Δ₂ → Δ₂ ∋ˡ Y := α
      → Ξ ∣ Δ₁ ⊢χᶜ bind X α ∷ χ ⇒ Δ₂ .

The position X is dropped, exactly as `conv-unbind` already drops its own:
skipping the unbind left α where it was, so the paired bind must leave it
there too.  The two bind clauses are mutually exclusive
(`fresh-not-lookup`), so the conversion context stays a FUNCTION of the
change list — which is what determinism for `CancelR`, `IdPush` and
`TyPeelR-⟪⟫` consumes.  With the clause, `rewind Θ`'s conversion context
is Θ's own conversion context, which is where `CancelR`'s minted `mkId A`
is read; that is the invariant the rule always presumed.

ALTERNATIVE CONSIDERED AND REJECTED.  Redefine `rewind` to invert only
the binds (`dual (binds χ) ++ binds χ`).  That repairs `rewind` —
its interior run becomes literally Θ's conversion run, followed by its
inverse — but leaves `Θ₁ ⋉ Θ₂` broken, and `Θ₁` is the argument's dual,
which is not ours to rewrite.  One clause fixes both frames; two rule
rewrites fix one.

INSTALLED in strong-rep-nu.Boundary §3.  The whole development still checks, and
examples 1–3 are unchanged (no unbind-carrying `CancelR` occurs in them).

THE RESULT.  The fourth example now runs `E₀ᴮ -→* true` in 25 steps with a
typing derivation at every state.  The shape of the tail is worth
recording: with a tower of n seals against n unseals, `CancelR` at the
innermost live pair leaves two identity layers, each of which `IdPush`
walks outward one layer at a time before the next `CancelR` can fire, so
the run is quadratic in n — for n = 3, four `Peel`/`Beta` steps, two
`CancelR`s inside, five `IdPush`es, a last `CancelR`, and six `Drop-true`s.

THE TOOLING THIS FORCED (strong-rep-nu.TypeCheck).  Because `_⋉_` and `rewind`
CONCATENATE change lists, those frames grow with the tower: the last ones
in this run carry tens of changes each.  A hand-written
`Ξ ∣ Δ ⊢χ χ ⇒ Δ′` is one line per change and contains nothing the change
list does not already determine.  So the development now carries an
executable, DERIVATION-PRODUCING type checker: every judgement it decides
— the two induced contexts, `WfCtx`, the lookup square, conversion
typing, type formation, and the term judgement itself — is returned as a
`Maybe` of the ordinary derivation, built from the ordinary constructors.
The caller states the answer and the checker is forced at it, so a
failure or a different answer is a type error, not a silently accepted
witness.  Nothing is postulated.

Consequence for the example module: a state's typing derivation is now

    E₁₄-⊢ : empty ∣ [] ⊢ E₁₄ ⦂ `𝔹
    E₁₄-⊢ = tc

and the module lost about 1400 lines of `SameTy` readings, `WfCtx`
obligations and change-by-change frame derivations, all of which the
terms already fixed.  What each state's derivation documents — its TYPE —
survives; the reduction steps are untouched, because the rule and the
value premises at each edge are the content of the test.

One design point is worth recording.  The checker must INFER, not merely
check: `⊢·` and `⊢·[]` need the head's type and a head can be a boundary.
Inferring a boundary's exterior type means inverting `shiftRep`, because
`env` reads that type across the boundary scope's representation-bind prefix
(`Δᶜ ⊢ᶜ Cₑ ~ shiftRep n R`).  That inverse is `strAt`, strengthening at a
binder depth, and it is the only place in the checker that produces an
equation rather than a derivation.

A second one, found by trying to be too clever: the lookup premise of
`CancelR`/`IdPush` canNOT be discharged by a goal-directed checker.  Both
contracta mention the looked-up type only under `mkId`, which the unifier
cannot invert, so `A` is fixed by that premise and by nothing else and the
INFERRING form has to be used there.

## A REPRESENTATION PAYLOAD WITH A `∀` BREAKS TWO RULES (2026-09-18)
## — found by the first example that instantiates at a polymorphic type

CONTEXT.  The example suite had been extended until all fifteen reduction
rules fire, and the remaining gap was a kind of VALUE rather than a rule:
nothing anywhere instantiated a type variable at a polymorphic type, so no
boundary scope ever bound a representation payload containing a `∀`, and
`wfᴿ-∀` and `local-ref` fired nowhere.  System F is impredicative, so that
is an ordinary program, not an exotic one.

Two were written:

    H₀ = (ΛX. λx:X. x) [∀Z. Z⇒Z] · (ΛZ. λz:Z. z) , at [𝔹] · true
    N₀ = (ΛX. λx:X. ((ΛY. λy:Y. y) [∀Z. Z⇒X]) · (ΛZ. λz:Z. x)) [ℕ] · 7 ,
         at [𝔹] · true

H₀'s payload is a closed `∀`; N₀'s is `∀Z. Z⇒X`, whose body mentions a
live type variable, so the payload carries a payload-LOCAL reference and a
FREE representation variable under the same binder — the mixed reading
`_⊢ref[_]_` exists for.

BOTH WERE WELL TYPED AND NEITHER RAN.  H₀ takes ten steps and loses its
type at the eleventh; N₀ takes eight and loses it at the ninth.  These are
not stuck states: the evaluator finds a redex each time, and the
CONTRACTUM fails to typecheck.  Machine-checked at the time in
strong-rep-store/notes/ForallPayloadWall.agda, which pinned the failing premise in each
case.  REPAIRED, below; both programs now run, as §8 and §9 of
notes/RepresentationReductionExamples.agda — seventeen and twenty-three
steps, every state type-checked.

THE TWO FAILURES ARE THE SAME DEFECT.  Each rule takes a SPELLING — an
ordinary de Bruijn index — that is valid in one conversion context and
reuses it in a different one, without re-basing.  The two contexts agree
whenever the unbinds and binds between them leave the relevant name where
it was, which is why nothing else in the suite notices.

`TyPeelR-⟪⟫` (N₀, step 9).  The contractum pushes the type application in
one layer carrying `renameᵗ (extᵗ suc) Bᵢ`, where Bᵢ is the source of the
crossed boundary's conversion — read at `underΛ Δᶜ` by the rule's own
premise.  `⊢·[]` reads that annotation in the INTERIOR context instead.
Here Δᶜ is `… ∣ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])` and the interior is `… ∣ (0 ∷ 3 ∷ [])`,
because the conversion context keeps the two names the interior's unbinds
removed; the same representation therefore sits at ordinary index 3 in one
and 1 in the other.  The head's type is `∀ (` 0 ⇒ ` 2)` and the pushed
annotation is `` ` 0 ⇒ ` 4 ``.

`IdPush` (H₀, step 11).  The rule turns the inner `id (` X)` into
`unseal X` and merges the two frames.  `X` was read in the INNER frame's
conversion context; the merged frame `Θ₁ ⋉ Θ₂` has a different one.  Here
the value under the merged frame has type `` ` 0 `` at
`… ∣ (1 ∷ [])`, whose representation is `𝔹, and the merged conversion
context is `… ∣ (0 ∷ 1 ∷ 2 ∷ [])`, in which `𝔹 is named 1 and the `∀`
payload is named 2.  The rule minted `unseal 2`; `unseal 1` is what
matches.

WHAT THIS SAYS ABOUT THE RE-BIND CLAUSE (2026-09-17).  That repair
turned on the same question and was decided the same way: the conversion
context keeps an unbound name WHERE IT WAS, so positions in it are the
interior's positions with the unbound names left in place.  The ruling
recorded that dropping the position was safe because a dual restores what
its unbind removed.  These two rules show the wider consequence the ruling
did not draw: as soon as a spelling CROSSES between the two readings it
must be re-based, and neither rule does.  The repair is not wrong — both
of its own checks still hold — but it is not sufficient, and the invariant
it leaned on ("the two contexts agree on the names that matter") is false
in general.

THE RULING (2026-09-18), INSTALLED: CARRY THE INTERIOR SPELLING AS A
PREMISE.

The two candidates were: re-base the spelling at the crossing, or name the
interior spelling in a premise and relate the two.  They are the same
CONTENT — the question is only whether the rule computes it or asserts it
— and four things decide it for the premise.

(1) The translation is not arithmetic.  The two name maps can REORDER
relative to each other: the interior's `bind` inserts at a position in
ITS list, and the conversion context, having skipped the matching `unbind`,
is looking at a different one.  `Θ↔ = boundary [] (bind 1 0 ∷ unbind 0 0 ∷ [])`
over names `0 ∷ 1 ∷ []` gives interior `1 ∷ 0 ∷ []` and conversion
`0 ∷ 1 ∷ []` (machine-checked, notes/ForallPayloadWall §3).  So the two
maps are not even subsequences of one another and the only translation
there is goes through the REPRESENTATION a name denotes.

(2) That translation is a LOOKUP, and it is partial: Δᶜ holds names the
interior does not, so re-basing can fail.  A total version needs a junk
case; a faithful one needs a premise saying it succeeded — which is the
other candidate.

(3) A premise is free on both of the things a new premise usually costs.
Determinism: the premise is a `SameTy`, whose target is unique on a name
map with `Unique` names by `same-target-unique` (strong-rep-nu.Ctx) — already
proved, and both rules already carry the `Unique` premise.  Progress: it
comes by inverting the redex's own `env`, at exactly the point where
`TyPeelR` already inverts to recover its annotation premise.

(4) It is what this design already does everywhere else, and the reason it
does.  `CancelR` and `IdPush` carry a binder-lookup premise rather than
computing `mkId` from stored knowledge; `TyPeelR` carries the annotation
premise rather than computing the interior body; `IdPush` REPLACED
`IdAbsorb` precisely to keep context arithmetic (`⊕`, `⊳`) out of the
contracta.  Computing the re-basing would put a partial, lookup-based
defined function back inside a contractum — and a defined function in a
reduction index is what trips Agda's unifier (AGENTS.md, constructor-form
indices).

AS INSTALLED.  `TyPeelR-⟪⟫` gains `Δ ⊢ⁱ Θ ⇒ Δᵢ`,
`Unique (names (underΛ Δᵢ))` and `SameTy (underΛ Δᵢ) Bᵢ′ (underΛ Δᶜ) Bᵢ`,
and pushes `renameᵗ (extᵗ suc) Bᵢ′`.  `IdPush` gains `Δ ⊢ⁱ Θ₂ ⇒ Δᵢ`,
`Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ`, `extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ`,
`Unique (names Δ⋉ᶜ)` and `SameTy Δ⋉ᶜ (` X′) Δ₁ᶜ (` X)`, and mints
`unseal X′`.

THE PRICE, HONESTLY.  Three premises and five, not the one apiece the
recommendation estimated.  The crossing needs BOTH contexts named to be
stated at all, and the interior name map's `Unique` is what makes the
re-based spelling a function — so each rule pays for the contexts it
relates, not just for the relation.  The determinism cases grew to match;
they are still nothing but `interior-functional`, `conversion-functional`,
`conv-src-unique`, `sameTy-src-unique` and `∋:=-det`, all of which already
existed.  Nothing new had to be proved.

WHAT IT DID NOT DISTURB.  The seven runs that predated the repair are
unchanged, step for step: wherever the two contexts agree on a name, the
re-based spelling IS the old one, so their contracta are identical.  That
is also why the defect stayed hidden — the suite had no program in which a
unbind and a bind moved a name far enough for the readings to part.

`CancelR`, REPAIRED THE SAME WAY, PREVENTIVELY.  Its contractum minted
`mkId A` on BOTH layers from a single `A` read at the outer conversion
context, while the inner layer is checked at the merged frame's — the same
crossing.  It now carries
`extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ`, `Unique (names Δ⋉ᶜ)` and
`SameTy Δ⋉ᶜ A′ Δᶜ A`, and mints `mkId A′` inside.  Three premises, not
five: the source spelling is the looked-up `A`, which the rule already
had at Δᶜ, so unlike `IdPush` it needs neither the interior context nor
the inner frame's conversion context.

BE CLEAR ABOUT THE EVIDENCE.  No example distinguishes `A′` from `A`, so
this one is not justified by a failing program the way the other two
were.  It is justified by uniformity and by the fact that the two
contexts PROVABLY can disagree (the reorder witness,
notes/ForallPayloadWall §1) — the previous two defects were both found
only after a program happened to reach the disagreement, and waiting for
a third is not a strategy.  The nine runs are unchanged by it, and the
new premise is built at every `CancelR` in the suite, so the machinery is
exercised even where the value coincides.

THE STRUCTURAL OPTION, NOT TAKEN NOW.  Both this defect and the
2026-09-17 one come from the same place: the interior and the conversion
context are two DIFFERENT LISTS, and every spelling that crosses between
them is a hazard.  A representation in which they share one list — the
interior's map with the unbound entries marked rather than deleted — would
make the positions coincide and retire the whole class.  That is a
redesign of `Ctxᵗ` touching everything, and it is close to the masking
discipline this development already retired once (proof/MaskFacts, the
SCOPE MOVE of 2026-09-06), so it should not be reached for on two data
points.  If a third defect of this kind appears, it is the thing to
reconsider — and the reasons masking was dropped should be re-read first,
because they may not apply to marking the CONVERSION context.

## 2026-09-18 — `BoundaryWf` stops storing what it can prove

`BoundaryWf` carried its OUTPUT well-formedness as two explicit obligations,
`bw-interior-wf : WfCtx Γᵢ` and `bw-conversion-wf : WfCtx Γᶜ`, with a
standing note that they should become derived lemmas. They are now
derived, and the fields are gone.

WHAT IT TOOK.  `WfCtx` has three fields and each transports separately
(`strong-rep-nu.Boundary` §3a):

* `name-fn` — an unbind deletes and a bind inserts a name its own premise
  says is fresh, so both readings preserve `Unique` (`int-unique`,
  `conv-unique`), and `shiftRVars` is injective past the bind block.
* `wf-names` — every name a reading leaves live is one the exterior
  already had, shifted past the bind block, or one a `bind` brought in,
  and a `bind` carries its own `ValidRVar` (`int-valid`, `conv-valid`).
* `wf-reps` — neither reading touches the representation context, so all
  that is needed is that the bind block is well formed where it lands:
  each payload weakened past the block's own tail. That is `wfᴿ-push`, on
  a general renaming lemma `wfᴿ-rename` for `_⊢ᴿ[_]_`, which is the only
  genuinely new proof here.

WHY THIS SHAPE.  The two former fields keep their names, as functions of
a `BoundaryWf`, so every USE site is unchanged and only the two construction
sites shrink. `boundaryWf?` no longer re-runs `wfCtx?` on both derived
contexts at every boundary; that re-check was measured at about 0.3s of
the 7.4s example suite, so the gain is the obligation, not the clock.

The `Unique` half of this is what `notes/PeelPremise.agda` §8 consumes: a
repaired `Peel` would get `Unique` from the boundary scope witness the redex's
own typing already stores, rather than carrying it as a premise the way
`TyPeelR-⟪⟫`, `IdPush` and `CancelR` do.

## 2026-09-18 — the `Peel` repair, installed

`Peel` moves the domain half `s` of its boundary's conversion onto the
crossed frame's DUAL. `s` was read at Θ's conversion context and is used
at the dual's, which is taken at the interior. Those are different name
maps, and not merely renumberings of each other: the invariant that would
have made them agree is false (`notes/CrossingAudit.agda` §5).

THE RULE now names the dual's spelling `s′` and carries
`SameConv Δᵈ s′ Δᶜ s`, alongside the boundary scope's two readings, the dual's
conversion context and `Unique (names Δᵈ)`. That is the fourth and last
crossing to be repaired this way, and the only one whose carried object is
a CONVERSION rather than a type, so it needed a new judgement: `_⊩_~_`
and `SameConv` in `strong-rep-nu.Conversion` §2b, which is `_⊢_~_` one universe
up, structural except at the three leaves a conversion spells a name at.

WHY IT IS SAFE TO CARRY, which is the part that took the work
(`notes/PeelPremise.agda`): the two contexts NAME THE SAME representation
variables — (Q), proved for every boundary scope with no restriction on the
change list — a well-typed conversion always has a representation-universe
reading to transport, and the dual's conversion context, which typing the
redex does not supply, always exists. So the premise never blocks a
reduction. All twelve runs pass unchanged, same step counts and endpoints.

BE CLEAR ABOUT ONE THING. The rule still CARRIES `Unique (names Δᵈ)`.
`det` has no typing derivation to read it from, exactly as for the other
three. What the argument shows is that a well-typed redex always supplies
it, not that the premise can be dropped.

MEASUREMENT. The example suite is ~7.5s cold, against ~7.4s before, so the
extra premises cost roughly nothing at this size. Two readings of ~32s
were taken during the install and did not reproduce across five later
runs; they were artifacts, not a regression.

## 2026-09-18 — uniqueness comes from typing, not reduction

The concrete `IdPush` redex

    (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫

used to carry both `Unique (names Δ⋉ᶜ)` for the merged frame and
`Unique (names Δᶜ)` for Θ₂'s conversion context. The contractum mentions
neither witness; it depends on the retained `SameTy`, lookup and context
readings. The same duplication occurred at every boundary rule whose
determinism case compared a weakened type or conversion.

THE RULING, INSTALLED. Reduction carries no `Unique` premises. All eight
were removed: one each from `Peel` and `TyPeelR-Λ`, and two each from
`TyPeelR-⟪⟫`, `CancelR` and `IdPush`. The `SameTy`/`SameConv` and context
reading premises stay because they pin the spellings that occur in the
contracta.

Determinism now states

    det : ∀ {Δ Γ M M₁ M₂ A} → Δ ∣ Γ ⊢ M ⦂ A
      → Δ ⊢ M -→ M₁ → Δ ⊢ M -→ M₂ → M₁ ≡ M₂

and obtains name-map functionality from that typing derivation. In a
boundary case it inverts to `env`, reads `name-fn` from the stored
`BoundaryWf`, and uses `bw-interior-wf`/`bw-conversion-wf`; `unique-underΛ`
handles the type-binder cases. The merged contexts of `CancelR` and
`IdPush` transport the exterior's uniqueness through their explicit
conversion readings. `Peel` uses `dual-unique`, moved from
`notes/PeelPremise.agda` to `strong-rep-nu.Boundary` §3a, where it is stated from
the lifted `interior-unique` and `conversion-unique` lemmas. Congruence
cases invert typing and pass the appropriate subterm derivation when they
recurse.

THE EXECUTABLE CONSEQUENCE. `Eval.agda` no longer imports or runs
`unique?`: its gatherers decide only evidence the rules still carry. The
twelve example runs keep the same step counts and endpoints.

## 2026-09-18 — rewind's two context invariants are relational theorems

THE NECESSARY HYPOTHESIS, on a concrete boundary scope. Let

    Δ₀ = (bindR `ℕ ∷ []) ∣ []
    Θ₀ = boundary [] (unbind 0 0 ∷ []) .

The raw conversion relation admits `Δ₀ ⊢ᶜ Θ₀ ⇒ Δ₀`: `conv-unbind`
skips the unbind even though representation variable 0 has no ordinary name.
But `rewind Θ₀` has changes
`bind 0 0 ∷ unbind 0 0 ∷ []`. Its conversion reading skips the tail unbind
and then inserts name 0, so its result is

    (bindR `ℕ ∷ []) ∣ (0 ∷ []) ,

not `Δ₀`. Thus a theorem from the conversion reading alone is false for
the relational interface. There is no interior reading of `Θ₀` at `Δ₀`,
because its unbind has nothing to delete.

THE RULING, INSTALLED in `strong-rep-nu.Boundary` §3a:

    rewind-interior : ∀ {Θ : Boundary}
      → Γ ⊢ⁱ Θ ⇒ Γᵢ
      → Γ ⊢ⁱ rewind Θ ⇒ extendReps (binds Θ) Γ

    rewind-conversion : ∀ {Θ : Boundary}
      → Γ ⊢ⁱ Θ ⇒ Γᵢ
      → Γ ⊢ᶜ Θ ⇒ Γᶜ
      → Γ ⊢ᶜ rewind Θ ⇒ Γᶜ

The first proof runs the original changes and their exact inverse. The
second uses the original interior reading to show that every name a dual
bind restores is already live in the original conversion context; that
step is discharged by `conv-bind-live`. A dual unbind is skipped. No
`WfCtx`, bind-well-formedness or `BoundaryWf` hypothesis is needed: the pair
of relational readings is the weaker interface, and every `BoundaryWf`
already supplies both.

WHY THESE TWO FORMS. The outer identity layer minted by both `CancelR` and
`IdPush` uses `rewind Θ₂`, so these lemmas construct exactly the
interior and conversion readings its `env` needs. The inner layer uses
`Θ₁ ⋉ Θ₂`; both reduction rules already carry that composite's
conversion reading explicitly, so item 3 needs no additional composite
theorem.

## 2026-09-18 — stage-1 preservation is relational and parameterized

THE EXAMPLE THAT CHANGED THE PUBLIC STATEMENT. Let

    Δdup = (abstR ∷ []) ∣ (0 ∷ 0 ∷ [])

and consider

    (Λ ($ 0)) ·[ `ℕ , `ℕ ] .

The source is typed at `Δdup`: neither `$ 0` nor either `ℕ` annotation
uses an ordinary type variable. TyBeta also steps because `$ 0` is a value
and `Δdup ⊢ᶨ `ℕ ~ `ℕ`. Its contractum is

    ($ 0) ⟪ instantiate `ℕ (boundary [] []) , reveal 0 `ℕ ⟫ .

Typing that boundary requires a `BoundaryWf` whose exterior field is
`WfCtx Δdup`, but the duplicate name map is not `Unique`. Keeping the old
premise-free preservation statement would therefore assert a false result
on this example; trying to recover `WfCtx Δ` from the source typing also
fails on this same derivation. THE RULING: the stage-1 `Preservation` and
every local rule case take `WfCtx Δ`. On the example this premise rejects
`Δdup` at the theorem boundary, exactly where the minted `BoundaryWf` needs it.

THE RETIRED INTERFACE WAS DELETED, NOT SHIMMED. The old `Nameable` and
masked/unmasked-entry arguments do not occur in `proof/Preserve.agda`.
Section 1 now phrases lookup preservation directly on `Ctx.agda`:

    WfRen Δ Δ′ ρ = ∀ {X} → Δ ∋tv X → Δ′ ∋tv ρ X

    SubWf Δ Δ′ σ = ∀ {X} → Δ ∋tv X → Δ′ ⊢ᵗ σ X

`wf-ren`, `wf-substᵗ`, and `wf-[]ᵗ` follow those live ordinary-name
lookups. `CtxWf` still records well-formed term-context entries, and
`⊢ᵗ-of` is its typing induction. The former retagging step became
`RepRefines`: it changes an `abstR` binding to `bindR R` while leaving the
ordinary name map fixed, and `⊢refine` transports the term typing through
that representation refinement.

THE MINTED CONVERSIONS FOLLOW THE NEW RULES. TyBeta uses `reveal 0 B` and
the new relational readings of `instantiate R (boundary [] [])`. Both TyPeelR
clauses use the rule-carried representation spelling and mint
`instReveal 0 s`; `instantiate-interior` and `instantiate-conversion`
transport the two induced contexts. The wrapper clause consumes its carried
`SameTy` premise instead of reconstructing the interior spelling. No term,
typing, conversion, or reduction rule changed in this port.

THE STAGE-1 MODULE IS HONESTLY PARAMETERIZED. `Peel`, `CancelR`, and
`IdPush` remain the downstream cases they were designed to be. Two further
representation-only typing transports have no new-design theorem yet. On
the Beta example `( ƛ A ∙ N) · W`, `CrossΛTyping` is what types an image
`crossΛᴹ W A` when substitution passes a `Λ`. On the nested TyPeelR
example, `AddUnbind0Typing` types the moved inner boundary after paired
ordinary/representation renaming and `addUnbind0`.

**NEW MAJOR STATEMENTS FOR REVIEW; NOT PROVED IN STAGE 1:**

    CrossΛTyping : Set
    CrossΛTyping = ∀ {Δ W A}
      → WfCtx Δ
      → Δ ⊢ᵗ A
      → Δ ∣ [] ⊢ W ⦂ A
      → underΛ Δ ∣ [] ⊢ crossΛᴹ W A ⦂ ⇑ᵗ A

    AddUnbind0Typing : Set
    AddUnbind0Typing = ∀ {Δ W Θ s A P}
      → WfCtx ((bindR P ∷ reps Δ) ∣
                   (zero ∷ shiftReps (names Δ)))
      → Δ ∣ [] ⊢ W ⟪ Θ , `∀ s ⟫ ⦂ `∀ A
      → ((bindR P ∷ reps Δ) ∣ (zero ∷ shiftReps (names Δ)))
          ∣ [] ⊢
            (renᴹ² (ren² (λ X → X) (extN (numBinds Θ) suc)) W
              ⟪ addUnbind0 (renᴮ² (ren² (λ X → X) suc) Θ)
              , `∀ (renᶨ (extᵗ suc) s) ⟫)
            ⦂ `∀ (renameᵗ (extᵗ suc) A)

The top-level `Preservation.agda` no longer repeats the main branch's false
claim of an unconditional theorem. It exports the statement with `WfCtx`
and a `Stage1` module parameterized by these two transports plus the three
crossing cases. The next stage must review and prove the two transport
statements, then port `PeelDual.agda` and `MoveScope.agda`, before restoring
an unparameterized public theorem.

## 2026-09-19 — canonical base values include Boolean literals

THE CONCRETE COUNTEREXAMPLE to the inherited statement is

    V = `true
    V-true : Value V
    ⊢true  : empty ∣ [] ⊢ V ⦂ `𝔹
    base-𝔹 : Base `𝔹 .

The old `canon-base` conclusion required `Σ[ n ∈ ℕ ] (V ≡ $ n)`, so these
premises demanded that `true` equal a numeral. Boolean terms, typings, values,
and `Drop-true`/`Drop-false` were added when the representation-variable
experiment began, but `proof/Canonical.agda` had not yet been ported and still
described the earlier language in which no Boolean literal existed.

THE RULING. `canon-base` keeps its name and base-type premise, but its result
now enumerates all three base literals:

    (Σ[ n ∈ ℕ ] (V ≡ $ n)) ⊎ (V ≡ `true) ⊎ (V ≡ `false) .

On the example it returns the `true` branch. `canon-ℕ` keeps its old,
numeral-only statement, so clients that specifically know the exterior type is
`ℕ` lose no precision. Progress must split the three branches against `Drop$`,
`Drop-true`, and `Drop-false` when it is ported.

THE RELATIONAL PORT itself adds no new major theorem. For a boundary
`W ⟪ Θ , c ⟫`, `SameTyExt` factors the exterior and conversion-target
spellings through a common representation type. Local inversions show that
`shiftRep (numBinds Θ)` preserves that type's base, variable, arrow, or `∀`
head; the existing inert-conversion inversions then recover the same wrapper
shapes as before.

## 2026-09-19 — stage-1 progress is relational and premise-free

THE CONCRETE CASE THAT EXPOSES THE REMAINING OBLIGATION is the repaired
`IdPush` state from the polymorphic-payload run. The inner identity is read at

    names Δ₁ᶜ = 1 ∷ []
    id (` 0)                       -- ordinary name 0 denotes representation 1

while the merged frame's conversion context is

    names Δ⋉ᶜ = 0 ∷ 1 ∷ 2 ∷ [] .

After the push, the conversion must therefore be `unseal 1`, not `unseal 0`:

    (V ⟪ Θ₁ , id (` 0) ⟫) ⟪ Θ₂ , unseal Y ⟫
      -→ (V ⟪ Θ₁ ⋉ Θ₂ , unseal 1 ⟫)
           ⟪ rewind Θ₂ , mkId A ⟫ .

The typing derivation supplies `BoundaryWf` for Θ₂ and Θ₁, but it does not
supply a conversion reading for `Θ₁ ⋉ Θ₂`. The rule carries that reading and
the `SameTy` weakening explicitly, so Progress must construct both before it
can exhibit this step.

THE TWO IMPLEMENTATION CHOICES on this example were:

1. Prove immediately that the merged reading always exists and contains both
   source name sets. On the example this theorem constructs a context
   containing representation 1 and weakens name 0 as name 1.
2. State that invariant exactly, use it as a stage-1 module parameter, and
   defer its proof for review. On the same example the parameter supplies the
   identical merged reading and the identical name-1 witness, while making the
   new general claim visible at the public proof boundary.

THE RULING FOR STAGE 1 is option 2. This is a genuinely new major statement,
not a transcription of a computed-context theorem and not one of the facts
already proved in `notes/PeelPremise.agda`:

    MergedReading : Set
    MergedReading = ∀ {Δ Δᵢ Δᶜ Δ₁ᵢ Δ₁ᶜ Θ₁ Θ₂}
      → BoundaryWf Δ Θ₂ Δᵢ Δᶜ
      → BoundaryWf Δᵢ Θ₁ Δ₁ᵢ Δ₁ᶜ
      → Σ[ Δ⋉ᶜ ∈ Ctxᵗ ]
          ((extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ)
            × Keeps (names Δᶜ) (names Δ⋉ᶜ)
            × Keeps (names Δ₁ᶜ) (names Δ⋉ᶜ))

The first `Keeps` supplies CancelR's weakening of the lookup type from
Θ₂'s conversion context. The second supplies IdPush's weakening of the
inner identity variable from Θ₁'s conversion context. `weaken-ty` turns each
name-retention fact into the exact `SameTy` carried by the reduction rule.

THE PUBLIC LOGICAL STATEMENT DOES NOT CHANGE and takes no `WfCtx` premise:

    Progress : Set
    Progress = ∀ {Δ : Ctxᵗ} {M : Term} {A : Ty}
      → Δ ∣ [] ⊢ M ⦂ A
      → Value M ⊎ (Σ[ M′ ∈ Term ] (Δ ⊢ M -→ M′))

For the preservation counterexample at the duplicate-name context,
TyBeta's contractum had to mint a new `BoundaryWf`, so preservation needed
`WfCtx Δ`. Progress only mints a step derivation. TyBeta gets its
representation reading from the type-formation premise, and if Progress is
under a boundary then that boundary's `env` node already carries the needed
`BoundaryWf`. Thus the typing derivation alone suffices.

THE PROVED PEEL PACKAGE MOVED FROM NOTES TO CORE. The name-set invariant (Q),
its list machinery, and `dual-conversion-exists` now live in
`Boundary.agda` §3b/§3c. Type/conversion weakening, readability,
`premise-exists`, `peel-premises`, and `peel-premises-env` now live in
`Conversion.agda` §2c. `notes/PeelPremise.agda` retains the mixed-frame
counterexample and machine-checks the moved `Q` and `premise-exists` on it.
The duplicate `Keeps`, `keeps-underΛ`, and `weaken-ty` definitions in
`proof/Preserve.agda` were removed so preservation reuses the core facts too.

All other Progress obligations are direct inversions of the typing
derivation. `canon-base`'s three branches construct `Drop$`, `Drop-true`, and
`Drop-false`; the two TyPeelR clauses reuse the outer `BoundaryWf` readings and
the `SameTy` body inversion; Peel uses `peel-premises-env`; CancelR and
IdPush reuse the outer lookup and the deferred merged package. No term,
typing, conversion, or reduction rule changed.

## 2026-09-19 — stage-2 crossings: IdPush and Peel land, CancelR is refuted

THE CONCRETE COUNTEREXAMPLE, and it is small. Let

    Ξ* = bindR (` 0) ∷ bindR `ℕ ∷ []
    Δ* = Ξ* ∣ (0 ∷ 1 ∷ [])
    Θ₂* = boundary [] []            Θ₁* = boundary (`ℕ ∷ []) []

so that ordinary name 0 denotes representation 0, whose payload is the
representation VARIABLE 1 — the shape a type application at a type
variable produces. `Δ* ∋ 0 := ` 1` and the redex

    (($ 7) ⟪ boundary [] [] , seal 1 ⟫ ⟪ Θ₁* , seal 0 ⟫) ⟪ Θ₂* , unseal 0 ⟫

is well typed at `` ` 1 ``. Every premise of `CancelR` holds — the merged
frame's conversion reading is `Δ₁* = (bindR `ℕ ∷ Ξ*) ∣ (1 ∷ 2 ∷ [])`, and
`SameTy Δ₁* (` 0) Δ* (` 1)` has the witness `` ` 1 `` — so the rule fires.
Its contractum

    (V ⟪ Θ₁* ⋉ Θ₂* , mkId (` 0) ⟫) ⟪ rewind Θ₂* , mkId (` 1) ⟫

has NO typing derivation. The outer `mkId (` 1)` pins the inner boundary's
exterior type to representation 1; the inner `env`'s `SameTyExt 1` then
asks its conversion's type to denote `shiftBy 1 (` 1) ≡ ` 2`, while the
inner `mkId (` 0)` denotes representation 1. A representation reading is
unique (`same-rep-unique`), and `1 ≢ 2`.

THE DIAGNOSIS. `CancelR`'s weakening premise reads the inner layer's
identity type in the OUTER conversion context:

    SameTy Δ⋉ᶜ A′ Δᶜ A ,

so it asserts that `A′` denotes the SAME representation as `A`. But the
inner boundary sits `numBinds Θ₁` representation binders inside its own
exterior, and `env` compares an exterior type with a conversion type
across exactly that block. The premise therefore drops the shift. The
other three crossings do not: `TyPeelR-⟪⟫` and `IdPush` weaken against
the INNER boundary's own conversion context `Δ₁ᶜ`, where the shifted
reading already lives, and `Peel` weakens a conversion between two
contexts that share a representation context. `CancelR` was the one
repaired PREVENTIVELY (2026-09-18), against no failing program, and it was
repaired against the wrong context.

WHY NO EXAMPLE SAW IT. A bare `seal X` conversion is minted by exactly one
rule — `Peel`, on the crossing argument — and `Peel`'s frame is
`dualBoundary Θ`, whose `binds` is `[]`. So every `CancelR` the twelve runs
reach has `numBinds Θ₁ ≡ 0`, and `shiftBy 0` is the identity. The
identities the unwinding tower mints are moreover at first-order types,
where the representation is closed and the shift is invisible a second
time.

IS THE CONFIGURATION REACHABLE? NOT SETTLED, and that is the second
repair path. The redex above is well typed and the rule fires on it, which
is everything `CancelRCase` quantifies over; but no closed program is
exhibited that reduces to it, and the `Peel` observation above suggests a
REACHABLE `CancelR` redex may always have `numBinds Θ₁ ≡ 0`. If so the
rule is sound where it fires and only the statement is wrong. The two
repairs are therefore: carry the shifted premise, or prove and carry the
invariant `numBinds Θ₁ ≡ 0`. Both are rule-level decisions.

THE RULING: NOTHING IS CHANGED. A rule repair is Jeremy's call. The wall
is machine-checked in `notes/CancelRShiftWall.agda`, which also carries
the reduction step and `cancelR-case-false : ¬ CancelRCase`;
`strong-rep-nu.proof.Preserve` keeps `CancelRCase` as the parameter of
`Impl` it always was, and `strong-rep-nu.Preservation` and `strong-rep-nu.TypeSafety`
keep it in `Stage1`. The public preservation and type-safety theorems are
therefore conditional on a hypothesis now known to be false — which is the
finding, not a gap. For the record, the shape the other crossings suggest
is `SameTy Δ⋉ᶜ A′ Δ₁ᶜ Aᵢ`, with `Aᵢ` the cancelled `seal X`'s source and
`Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ` a new premise; the retired `preserve-CancelR` minted
`mkId (shiftBy (numBinds Θ₁) A)`, so the old design had the shift and the
port lost it.

IDPUSH NEEDS NOTHING NEW, AND IN PARTICULAR NOT `MergedReading`. Four
facts do it, and three are relational readings:

  * `rewind-interior` / `rewind-conversion` give the outer frame's two
    contexts (2026-09-18);
  * `merged-interior` — NEW, `Boundary.agda` §3a — gives the merged
    frame's interior, and it is the inner frame's OWN interior on the
    nose. The lifted copy of Θ₂'s changes re-creates Θ₂'s interior one
    bind block in, which is exactly where Θ₁'s reading starts. This is
    the relational form of the retired `interior-⋉-rewind` equality;
  * `conversion-live` weakens the exterior type C into the merged
    conversion context, because a conversion reading only ADDS names, so
    every name of the merged frame's own exterior survives into it. That
    is the half of `MergedReading` preservation actually needs, and it was
    already a theorem;
  * `∋ʳ-push` — NEW, §3a — says a payload looked up THROUGH a bind block
    is the payload shifted past it. This is why `IdPush` escapes
    `CancelR`'s defect: its minted `unseal X′` takes its type from a
    LOOKUP, which shifts itself, where `mkId A′` takes its type from the
    premise.

Typing also forces `X′`'s representation to be `numBinds Θ₁ + αY` — the
old `idpush-name` equation, one universe up — and that is what lets the
lookup be taken at all.

PEEL LANDS ON ONE NEW TRANSPORT. `dual-interior` — NEW, §3a, beside
`rewind-interior` — says the dual's interior is the exterior under the
original bind block, so the crossing argument gains no ordinary scope.
`weaken-⊢` — NEW, `proof/PeelDual.agda` §1 — turns the rule's `SameConv`
premise into the dual boundary's conversion TYPING: the two conversion
contexts share a representation context, so a `seal`/`unseal` cites the
same binder and only its ordinary spelling changes, and an identity's
payload goes through `weaken-ty` against (Q). Source and target come back
paired with the `SameTy`s the crossing boundary's `env` consumes.

**REVIEW REQUIRED — NEW MAJOR STATEMENT, NOT PROVED.** The argument must
be retyped one bind block in, and that is the third representation-only
typing transport this port has needed:

    RepWeakenTyping : Set
    RepWeakenTyping = ∀ {Δ W A} (Rs : List Ty)
      → Δ ∣ [] ⊢ W ⦂ A
      → extendReps Rs Δ ∣ []
          ⊢ renᴹ² (ren² (λ X → X) (wkN (length Rs))) W ⦂ A

It stands beside `CrossΛTyping` and `AddUnbind0Typing` in
`proof/Preserve.agda` §4, and `preserve-Peel` takes it as a module
parameter rather than assuming it silently.

WHAT WAS DELETED, NOT SHIMMED. `proof/MoveScope.agda` lost its whole
masked-entry development: the `applyUnlocks`/`applyChanges` lookup
transports, the `shiftScope`/`rewind`/`_⋉_` list algebra, the
`scope`/`interior` context identities, the frame lemmas as EQUALITIES with
the unbind-only refutation, and `_⊢ᵐ_` for the two new frames.
`proof/PeelDual.agda` lost `applyChanges-dualScope`, `⊢ˢ-dualScope`,
`applyUnlocks-dualScope`, `interior-dual`, `applyUnlocks-hideBinds`, the
`Ren`/`wkN` crossing machinery `⊢ᵐ-dual`/`Ren-wkN`/`crossing`, and
`convCtx-dual` — which WAS (P), and (P) is refuted on this branch. None of
it has a two-universe counterpart: there is no computed context to state
an equality between, and the relational readings replace all of it.

WHAT MOVED INTO CORE. `Boundary.agda` §3a gained `dual-interior`,
`merged-interior`, `∋ʳ-push`, `interior-reps`/`conversion-reps`, and the
private `shiftRVars`-lifting of a change run that `merged-interior` needs.
`proof/Preserve.agda` §1 gained `same-wf` (the converse of `wf-same`),
`wf-mono`/`TvMono` with `tvMono-extendReps` (type formation depends on
ordinary POSITIONS only), `shiftRVars-∋` and `shiftRep-var`.

THE INTERFACE SHRANK. `strong-rep-nu.Preservation.Stage1` now takes `crossΛ`,
`addUnbind0`, `repWeaken` and `cancel`; `peel` and `idpush` are discharged
and gone. `strong-rep-nu.TypeSafety.Stage1` and `proof/TypeSafety.agda` follow.
`All.agda`'s first failure is unchanged: `proof/Adversary.agda:38`, on the
retired `applyChanges`.

## 2026-09-19 — the module sweep: four deletions, four ports

THE FRONTIER MOVED to `Examples.agda`. `All.agda` stopped at
`proof/Adversary.agda:38`, on the retired `applyChanges`; every proof
script between there and the regression corpus has now been classified
and acted on, by the branch's closed-world rule — port a fact about the
LIVE rules, delete a module whose subject IS the retired design, and say
which in one line.

WHAT WAS DELETED, AND WHY EACH.

* `proof/MaskFacts.agda` — its whole subject is masking: `mask`/`unmask`
  at a retained entry, `Nameable`, `∋lk`, `updateAt`, and `mask-only`, the
  statement that `interior Θ Δ` and `convCtx Θ Δ` "differ ONLY by
  masking". There is no lock BIT here: an unbind DELETES an ordinary name and
  a bind INSERTS one, so there is no core to compare and no computed
  context to write the equation between. What replaces `mask-only` is
  `conv-unbind` itself (`strong-rep-nu.Boundary` §3), which skips an unbind outright,
  and `conversion-live`, which says a conversion reading only ADDS names.

* `proof/PreserveObstruct.agda` — four concrete redexes, each written in
  `unmasked (bind …)` contexts with `bw`/`sw-l`/`sw-u` witnesses, exhibited
  to refute an OLD rule shape and then repaired. Three of the four rules
  have since changed shape again on this branch, and `CancelR` is refuted
  outright (notes/CancelRShiftWall.agda). The positive content is now
  theorems — `preserve-TyPeelR-Λ`, `preserve-IdPush` — and the twelve
  closed runs in `notes/RepresentationReductionExamples.agda` (now merged
  into `strong-rep-nu.Examples`), which exercise them from plain source rather
  than from hand-built derivations.

* `proof/DualTightness.agda` — Jeremy's 2026-09-06 tightness test, stated
  as `interior (dual Θ) (interior Θ Δ) ≡ map maskEnt (bind prefix) ++ Δ`
  with a vacuous-bind refutation beside it. Both halves are properties of
  the masked-entry `_⊢ᵐ_`. Tightness is now `dual-interior` (§3a): the
  dual's interior is the EXTERIOR under the original bind block, so a
  crossing argument gains no ordinary name at all — a stronger statement,
  proved for every boundary scope, with no well-formedness hypothesis. The
  vacuous bind is refused by `step-bind`'s own `Fresh α Δ` premise.

* `proof/MwUObstruct.agda` — the record of WHY the outer frame of
  CancelR/IdPush is `rewind Θ₂` rather than `dropLocks Θ₂` or
  `bindsOnly Θ₂`. Every one of its three refutations is an appeal to
  `sw-u`'s "the slot must be UNBOUND" premise or to reading a bind payload
  on `applyUnlocks`. Neither survives: a bind payload is now checked in the
  representation universe against the exterior (`_⊢ᴮ_`), where the ordinary
  change list cannot reach it, so the question the module answered is not
  askable. The choice itself is settled by `rewind-interior` /
  `rewind-conversion` (2026-09-18).

WHAT WAS PORTED.

* `proof/Adversary.agda`. The gate is unchanged — `seal-cites-binder` is
  still the one-line inversion of `conv-seal`. What the two universes add
  is that the gate now refuses a conceal for TWO independent reasons, and
  the module states both: the cited ordinary name may be absent from the
  map (§2b, the reading that replaces `∋lk`), or the representation
  variable it names may be `abstR` (§2, the old ⊢3n-adv, at
  `Δadv = (abstR ∷ []) ∣ (0 ∷ [])`). Neither can be repaired by a change
  list, because no change rewrites a representation binding. §3's "two
  spellings of one fact" survives as stated — `seal 0` at a binder whose
  payload is `∀Z.Z⇒Z` forces the source type, and the boundary at a
  mismatched interior type is untypeable. §4's `cancel-types-agree` gains
  the `Unique (names Δ)` premise that `∋:=-det` now carries. DELETED from
  it: `bind-claims-a-unbind` and `bind-mentions-no-rep`, which asserted
  things about the unbind layer of a retained entry.

* `proof/IdLayer.agda`. §1 was an EQUATION between ordinary de Bruijn
  indices, `X ≡ numBinds Θ₁ + Y`. That equation is FALSE here and not
  wanted: the two conversions are read on different name maps which may
  reorder relative to each other. The fact is one universe up, and it is
  what `preserve-IdPush` already consumes — `push-rep` says the inner
  conversion's name denotes `numBinds Θ₁ + α` exactly when the outer's
  denotes α, and `idpush-name`/`cancel-name` package it with the three
  context readings the derivation supplies. §2's
  `outer-id-base-untypeable` is proved through the representation universe
  instead of through `shiftBy`: the outer `id A` forces the inner
  boundary's exterior type to be BASE, `SameTyExt` carries base to base
  across the bind block, and the inner conversion's target is a VARIABLE.
  §3 keeps the naked-drop trap and `drop-empty-frame`, the latter now
  reading both induced contexts off `extendReps [] Δ ≡ Δ`. DELETED:
  `convCtx-unbind`.

* `proof/Canonicity.agda`, with ONE NEW SECTION. The family and its mint,
  decompose and rename facts port unchanged. `Peel` is what forces the new
  work: it no longer carries its crossing argument's conversion `s` onto
  the dual, it carries the dual's own spelling `s′` with a `SameConv`
  (2026-09-18). So canonicity must WEAKEN, and §5 does it by stating the
  family a SECOND time on representation variables (`CanonAtᴿ`) and
  transporting through `_⊩_~_` in both directions. Two things fell out.
  First, the way back needs the target name map to be a FUNCTION, so
  `canon-step` takes `Unique (names Δ)` — obtained for the dual by
  `dual-unique` from the readings `Peel` already carries, and propagated
  through `ξ-Λ`/`ξ-⟪⟫` by `unique-underΛ`/`interior-unique`. This is the
  same ruling as for `det`: uniqueness is a property of the context, not a
  premise of a rule. Second, a conversion whose leaves are ALL identities
  names no binder, so it is canonical everywhere and its weakening has
  no name to inherit; both transports therefore return a sum over a new
  `AllId` predicate, of which `mkId` is the leading instance. The old §10,
  which validated the invariant on `strong-rep-nu.Examples`, is dropped while that
  module is unported; its ground-level mint checks are kept.
  `CanonTyPeelR` is still REFUTED, for the unchanged two-binder reason.

* `proof/ShiftAudit.agda`. The criterion survives verbatim; what changes is
  that a frame identity is no longer an EQUATION BETWEEN COMPUTED
  CONTEXTS. §2 and §6 therefore CITE `dual-interior`, `rewind-interior`,
  `rewind-conversion` and `merged-interior` rather than restating them, and
  the masked-entry material — the `⊑ᵃ` refinement, the `Nameable`/`Unbound`
  slot arithmetic, the old single `TyPeelR`'s leak witness and the fix-(a)
  prototype relation — goes with the design that stated it. The audit's NEW
  headline is the second half: a moved subterm is renamed in the two
  universes SEPARATELY, and at every site but TyBeta's the ORDINARY
  component is the identity, because the unbind the crossing appends deletes
  the ordinary name it introduced. That is recorded per site in §2, §3 and
  §5. KEPT IN FULL: the tower measure. `towerHeight`,
  `towerHeight-renᴹ²`, `TyPeelR-⟪⟫-height` (the measure strictly
  decreases), `fixA-height-stalls` (the rejected repair's does not),
  `canon-∀-height` and `progress-Λ-at-0` (where the descent stops) are
  live facts about the live wrapper clause, and `strong-rep-nu.Reduction`'s own
  comment cites them.

WHAT THE SWEEP DID NOT TOUCH. No rule, term, typing, conversion or
boundary scope definition changed; `notes/RepresentationReductionExamples.agda`
runs the same twelve programs to the same endpoints in the same step
counts. `CancelR`'s refuted preservation case is untouched, and the three
representation-only typing transports — `CrossΛTyping`, `AddUnbind0Typing`,
`RepWeakenTyping` — and `MergedReading` remain module parameters awaiting
review.

ONE LOOSE END FOR THE NEXT PORT. `Examples.agda` imports
`strong-rep-nu.proof.PreserveObstruct` twice (§§ around its IdPush and TyPeelR
witnesses). That module is gone, so those two sections must be rebuilt
against the live rules or dropped when the corpus is ported. Several
comments in `strong-rep-nu.Reduction` still name the four deleted modules; they
are left as they stand because that file is not to be edited in this
sweep.

## 2026-09-19 — the regression corpus and the renderer: the frontier closes

`All.agda` now passes end to end, and so does `make check`. The two
modules that stood between it and the gate were `Examples.agda` (3763
lines) and `Show.agda`; both are ported, and nothing in the development
is postulated, holed or unported.

THE RULE THE PORT FOLLOWED, section by section, is the branch's
closed-world rule again: a section whose PROGRAM still makes sense is
rebuilt as a run stated through `TypeCheck.agda`/`Eval.agda`; a section
whose subject IS the retired design is dropped, with one line saying
where its verdict lives; a section the twelve-run suite already covers is
CITED rather than duplicated.

WHAT WAS REBUILT AS A RUN. Each is one `Reaches k n ⊢M V`, so each run is
evaluated once and every intermediate state is type-checked by `eval` at
the type the run started with.

* old §11 `Q` — `((ΛY. λx:Y. ((ΛZ. x) [ℕ])) [ℕ]) · 7`, the smallest
  closed program that reaches `IdPush`, since a VACUOUS `Λ` is what makes
  `TyBeta` mint an identity-at-a-variable layer. 11 steps to `7`, the
  same length as in the old design.
* old §11a `D` — two vacuous `Λ`s, so `IdPush` fires twice: 16 steps.
* old §12 `L` — `Q` with the vacuous `Λ` instantiated at the OUTER
  ordinary variable, which is the "wall" configuration: the chained
  representation with a `Peel`-minted unbind on the very name it was read
  through. 11 steps, every state typed. The reading is unchanged by the
  port: the wall CONTEXT is reachable, the wall CONFIGURATION is not,
  because the blocked name is always in a `Θ₁` (inert) position.
* old §11b `R` — the chained-representation variant, 21 steps.
* old §11c `G` — the only closed source that reaches `TyPeelR` over a
  frame that already has a bind, hence the only route to a two-bind
  frame. In the old design its run stopped after 5 steps at a non-value;
  here it runs to `7` in 14. Its `numBinds` table is kept and restated on
  the live frames (`instantiate`, `dualBoundary`, `addUnbind0 ∘ renᴮ²`, `_⋉_`,
  `rewind`), because it is what explains why no example ever saw the
  `CancelR` defect: `Peel`'s dual binds nothing.
* old §13b `H` — the REVEAL mirror, where the `∀` crosses OUTWARD as a
  result. Applied to an argument so that it ends at a numeral: 11 steps.
* old §7's `Bg` — the base-typed crossing wrapper, 2 steps to `Λ 7`.

WHAT WAS REBUILT AS A HAND-BUILT RUN AT A NON-EMPTY AMBIENT. Every run
above starts at `empty`; old §§1–3 did not, and that coverage was worth
keeping. At `Δ₆ = (bindR ℕ ∣ names 0)` the corpus now carries the cancel
pair (3 steps), one transparent id-layer (5) and two (7) — the stack
resolving one layer per step, outermost first, exactly as the old §3
observed. These three are the ONLY places a state-by-state transcript is
still written out; two of them are pinned with `evalTerms`, which is the
old file's second, independent transcription kept where it costs nothing.

WHAT WAS CITED, NOT DUPLICATED. Old §13a `J` is the twelve-run suite's
§3 and old §14 `E` — the program that killed the per-variable design,
v1's historical Example 8 — is its §4. Both run there; repeating them
would only pay for the evaluation twice.

WHAT WAS DROPPED, AND WHY EACH.

* old §4 (`Tᵣ`/`Tₘ`, the adversaries the retired `⊳` could not clear) —
  `⊳` does not exist. The gate is `proof/Adversary.agda`, which on this
  branch refuses a conceal for two independent reasons.
* old §5 (the three preservation BREAKS of the PREVIOUS design and the
  shape-IV survivor) — hand-built redexes in `unmasked (bind …)`
  contexts refuting rule shapes that are gone. The live verdicts are
  `proof/Preserve.agda`, `proof/MoveScope.agda`, `proof/PeelDual.agda`,
  and the one refutation that survives, `notes/CancelRShiftWall.agda`.
* old §6 — `P₀`, which is the suite's §1; its hand-composed chain and
  pinned `evalTerms` line are what the suite replaced.
* old §8, §9 (progress and preservation along a run) — both theorems sit
  inside parameterized modules today and one parameter is known FALSE,
  so applying them to a run would state a conditional. The run-level
  subject reduction in the corpus is the one `eval` CHECKS, state by
  state, and `reaches-⦂` hands the endpoint's typing back.
* old §12b, and the witnesses old §13a/§13b imported — they came from
  `strong-rep-nu.proof.PreserveObstruct`, deleted in the module sweep.
* old §15 (TIGHTNESS, RULE BY RULE) — its seven frame identities were
  EQUATIONS BETWEEN COMPUTED CONTEXTS, and there are no computed
  contexts here. They are now the relational transports `dual-interior`,
  `rewind-interior`, `rewind-conversion` and `merged-interior`
  (`strong-rep-nu.Boundary` §3a), and `proof/ShiftAudit.agda` is what consumes
  them.

WHAT WAS ADDED. A refutation section, because the port is only worth
having if its checks bite: a boundary over an ACTIVE conversion is not a
value; `infer` refuses `(ΛZ. z) [Z]`, an unbound ordinary type argument;
and a wrong endpoint, a wrong step count and too little fuel are each
rejected by `Reaches`.

THE RENDERER NOW SHOWS THE TWO UNIVERSES DIFFERENTLY, which is the whole
point of porting it rather than deleting it. A representation variable
prints as α, β, γ (then α′, …) and the ORDINARY variable that names it
prints as the Latin letter at the same counter — X names α, Y names β.
So a boundary reads `⟪ ↑α:=ℕ , ↥X , (seal X ↦ unseal X) ⟫`, and a change
whose letter does not match the representation it carries is visibly
wrong, which is the defect class the 2026-09-18 repairs were about.
Three further things the port had to get right, each a consequence of the
two-universe design rather than a display choice:

* the rendering environment IS the context: a representation context of
  named entries plus the ordinary name map `names Γ`, so an ordinary
  variable's name is a TWO-STEP lookup, an `unbind` DELETES an entry of the
  map and a `bind` INSERTS one;
* a boundary's body is rendered on the INTERIOR reading and its
  conversion on the CONVERSION reading — unbinds skipped, a re-bind of a
  live name a no-op — because those two name maps genuinely differ;
* the changes print IN THE ORDER THEY ACT, which is the list read
  head-LAST, and a bind payload prints in the representation universe
  over the EXTERIOR representation context, because the bind block is
  parallel.

`showRun` renders a whole `strong-rep-nu.Eval` trace with the name of the rule
that fired at each step (`ruleName` reports the rule INSIDE a
congruence), which is what `scripts/render_term.sh` was always being
used for by hand. That script needed no change.

## 2026-09-19 — the `CancelR` configuration is REACHABLE, and path (b) dies

THE QUESTION, Jeremy's, verbatim: "For the CancelR problem and repair, do
you have an example source program that reduces to the problematic
configuration?"  YES.  The program is

    Src = ((ΛP. λp:P. ((ΛX. λf:(∀Z. Z⇒X). f [ℕ] · 7) [P])
                         · (ΛZ. λz:Z. p)) [ℕ]) · 7  :  ℕ

closed, plain System F: not a boundary, boundary scope or conversion anywhere in
the source.  Nine steps — TyBeta, Peel, Beta, TyBeta, Peel, Beta,
TyPeelR-Λ, Peel, Beta — reach

    (((($ 7 ⟪ ↓X , seal X ⟫) ⟪ ↓Z , id X ⟫)
        ⟪ ↑γ:=ℕ , ↥Z , ↓Y , seal Y ⟫)      -- Θ₁, numBinds ≡ 1
       ⟪ ↑β:=α , ↥Y , unseal Y ⟫)          -- Θ₂, payload the rep VARIABLE α
      ⟪ ↑α:=ℕ , ↥X , unseal X ⟫

and the tenth step is the `CancelR`.  `eval` records it as `broke`, and
`no-contractum` refutes the contractum outright — an explicit `¬`, not the
checker's refusal.  BOTH conjuncts of the defect hold at once, which is
what no earlier example achieved.  The conversion context the run builds
for `Θ₂` is `notes/CancelRShiftWall.agda`'s hand-built `Δ*` ON THE NOSE:
`(bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])`, with `Δ* ∋ 0 := ` 1` and
`` ` 1 `` denoting representation `` ` 1 ``.  The wall was not a synthetic
configuration after all.

WHERE THE UNREACHABILITY ARGUMENT WENT WRONG.  The wall module said a bare
`seal X` conversion "is minted by exactly one rule — `Peel`, on the
crossing argument — whose frame is `dualBoundary Θ`".  `Peel` mints TWO
boundaries:

    Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
      -→ (V · (… ⟪ dualBoundary Θ , s′ ⟫)) ⟪ Θ , t ⟫

Only the ARGUMENT's carries the dual.  The RESULT keeps `Θ` and takes the
CODOMAIN `t`, so a bare `seal` sits on `Θ` whenever `t` is one — and `Θ`
binds when that boundary came from `TyPeelR`, whose mint is
`instReveal 0 s` on `instantiate R Θ₀` and whose `instReveal X (seal Y) ≡
seal Y` carries a `seal` leaf across untouched.  What was still needed was
a `↦` with a bare `seal` CODOMAIN, i.e. a `conceal` at the abstracted
variable to the RIGHT of an `⇒` and UNDER a `∀`:

    conceal 0 (∀Z. Z ⇒ X) ≡ `∀ (id (` 0) ↦ seal 1)

which is `TyBeta`'s mint at an argument of type `∀Z. Z ⇒ X`.  No program
in the twelve-run suite or in `Examples.agda` ever passed an argument
whose polymorphic type RETURNS the abstracted variable — example 9 has
`∀Z. Z ⇒ X`, but as the PAYLOAD of a type application, so its seal leaf
never meets a `TyPeelR`.  That was the gap.  The open representation is
then the same trick `Examples.agda` §1c uses for `IdPush`: instantiate at
an enclosing `Λ`'s variable, `[P]` and not `[ℕ]`.

EACH CONJUNCT ALONE IS STILL HARMLESS, and now that is a regression rather
than a remark.  Two controls, §7 of the witness module: the same program
instantiated at `ℕ` (so `numBinds Θ₁ ≡ 1` but the payload is closed) runs
to `5` in nine steps; the same program with a FIRST-ORDER crossing
argument `ℕ ⇒ X` (so the payload is still α but the seal stays on the
`Peel` dual, `numBinds Θ₁ ≡ 0`) runs to `7` in seventeen.

THE CONSEQUENCE FOR THE REPAIR.  Path (b) — prove and carry the invariant
`numBinds Θ₁ ≡ 0` — is CLOSED: the invariant is FALSE at a reachable
redex.  Path (a) is what is left, and it is confirmed on this example:
with the premise read against the inner boundary's own conversion context,
`Δ₁ᶜ = conv Θ₁ (int Θ₂ Δ₉) = (bindR `ℕ ∷ bindR (` 0) ∷ bindR `ℕ ∷ []) ∣
(0 ∷ 1 ∷ 2 ∷ [])`, the cancelled `seal 1`'s source is `Δ₁ᶜ ∋ 1 := ` 2`, so
the repaired premise delivers `A′ ≡ ` 2` where the rule as stated delivers
`A′ ≡ ` 1` — and the contractum built with `mkId (` 2)` IS well typed
(`repaired-⊢`).  What is NOT answered here is whether that premise is
always satisfiable, the analogue of `peel-premises` for `CancelR`.

THE RULING: STILL NOTHING IS CHANGED.  `strong-rep-nu.Reduction` is untouched,
`strong-rep-nu.proof.Preserve` keeps `CancelRCase` as the open parameter it was,
and the public preservation and type-safety theorems stay conditional on a
hypothesis now known false FOR A REACHABLE REDEX rather than only for a
hand-built one.  The evidence is `strong-rep-store/notes/CancelRReachabilityWitness.agda`
(in `All.agda`, which stays green) with the hunt log in
`notes/CancelRReachability.md`.

## 2026-09-19 — repair (a) for `CancelR`, approved and installed; the
## preservation case lands

THE APPROVAL, and it is the first rule change on this branch that Jeremy
ruled on directly.  The two earlier entries of today left `CancelR` with a
refuted preservation case and only one repair path open: path (b), the
invariant `numBinds Θ₁ ≡ 0`, died when the configuration turned out to be
reachable from a closed, plain source program.  Repair (a) — read the
weakening premise at the INNER boundary's conversion context — is
approved and installed.  `strong-rep-nu.Reduction` is no longer untouched.

THE RULE, BEFORE:

    CancelR : ∀ {Δ Δ⋉ᶜ Δᶜ V Θ₁ Θ₂ X Y A A′} → Value V
      → extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
      → SameTy Δ⋉ᶜ A′ Δᶜ A
      → Δ ⊢ᶜ Θ₂ ⇒ Δᶜ → Δᶜ ∋ Y := A
      → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
          -→ (V ⟪ Θ₁ ⋉ Θ₂ , mkId A′ ⟫) ⟪ rewind Θ₂ , mkId A ⟫

AND AFTER:

    CancelR : ∀ {Δ Δᵢ Δ₁ᶜ Δ⋉ᶜ Δᶜ V Θ₁ Θ₂ X Y A A′ Aᵢ} → Value V
      → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ
      → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
      → Δ₁ᶜ ∋ X := Aᵢ
      → extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
      → SameTy Δ⋉ᶜ A′ Δ₁ᶜ Aᵢ
      → Δ ⊢ᶜ Θ₂ ⇒ Δᶜ → Δᶜ ∋ Y := A
      → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
          -→ (V ⟪ Θ₁ ⋉ Θ₂ , mkId A′ ⟫) ⟪ rewind Θ₂ , mkId A ⟫

Three premises are added and one is re-pointed.  The contractum is
UNCHANGED as a term shape; what changed is which type `A′` is forced to
be.  The block is now premise-isomorphic to `IdPush`'s: the same interior
reading of Θ₂, the same conversion reading of Θ₁, the same lookup at
`Δ₁ᶜ`, the same weakening target `Δ⋉ᶜ`.  `IdPush` looks up a VARIABLE
and mints `unseal X′`; `CancelR` looks up the cancelled seal's SOURCE and
mints `mkId A′`.

WHY THE SPELLING MUST BE READ AT `Δ₁ᶜ`, in one paragraph.  The inner
boundary of the contractum carries the merged frame `Θ₁ ⋉ Θ₂`, and
`numBinds (Θ₁ ⋉ Θ₂) ≡ numBinds Θ₁`.  So its `env` compares its exterior
type against its conversion's type across `n = numBinds Θ₁`
representation binders: `SameTyExt n`, which asks the conversion's type to
denote `shiftBy n` of what the exterior denotes.  The outer layer's
`mkId A` pins that exterior to the representation `A` denotes in `Δᶜ`.
Reading `A′` FROM `Δᶜ` therefore asserts exactly the wrong thing — that
`A′` denotes the UNSHIFTED representation — and a representation reading
is unique (`same-rep-unique`), so the two are compatible only when `n ≡ 0`
or the representation is closed.  `Δ₁ᶜ` is `n` binders in, which is where
the shifted reading already lives; and the cancelled `seal X`'s own source
is read there, by `conv-seal`, in the redex's own typing derivation.  This
is not a coincidence of `CancelR`: it is why `TyPeelR-⟪⟫` and `IdPush`
weaken against `Δ₁ᶜ` too.  `CancelR` was the one crossing repaired
PREVENTIVELY (2026-09-18), against no failing program — and it was
repaired against the wrong context.

THE MEASURED RUN.  `strong-rep-store/notes/CancelRReachabilityWitness.agda`'s `Src` —
closed, plain System F, no boundary in the source — is unchanged.  Its
first nine steps are unchanged.  Step 10 now mints `mkId (` 2)` on the
inner layer where it minted `mkId (` 1)`, pinned by

    contractum-is-state-10 : traceEnd (eval 10 Src Src-⊢) ≡ Contractum

and the run COMPLETES:

    Src-eval : Reaches 19 19 Src-⊢ ($ 7)

nineteen steps, every state type checked at `ℕ`.  The tail past the
repaired `CancelR` is three `IdPush`es, a second `CancelR`, and the
`Drop$` tower.  `strong-rep-store/notes/RawRunProbe.agda` checks the same thing without the
type checker in the loop: `rawLen 100 Src ≡ 19` ending at `$ 7`, where the
pre-repair raw machine stuck after SIXTEEN steps at a non-value identity
tower — an `id ℕ` boundary over a wrapper claiming type X.  The raw and
the checked machines now agree exactly.

NO REGRESSION.  The twelve-run suite
(`notes/RepresentationReductionExamples.agda`) is BYTE-IDENTICAL and
green — every `CancelR` it reaches has `numBinds Θ₁ ≡ 0`, where the old
and the new premise deliver the same spelling.  `Examples.agda` is
likewise untouched and green, same step counts, for the same reason.  The
two controls of the witness module keep their counts, 9 and 17.  `make
check` is green: `All.agda` passes and `postulate-check` is clean.

THE FATE OF `CancelRCase`.  It is PROVED —
`strong-rep-nu.proof.MoveScope.preserve-CancelR`, beside `preserve-IdPush` and by
the same argument.  The outer layer is literally `IdPush`'s: the same
`rewind Θ₂` frame from `rewind-interior`/`rewind-conversion`, the same
`mkId A` at the outer binder's payload, the redex's own `se₂`/`wE` reused.
The inner layer is where the two diverge, because `mkId A′` has the SAME
type as source and target, so one type must satisfy both premises of the
inner `env`.  They meet because the lookup still shifts itself, one level
up: the cancelled binder's representation variable is `numBinds Θ₁ + αY`
(`eqX`, the old `cancel-name` equation one universe up), and `∋ʳ-push`
reads Y's payload through Θ₁'s bind block as `shiftBy (numBinds Θ₁)` of it
(`eqRB`).  So the representation the seal's source names at `Δ₁ᶜ` IS the
shifted one, and the repaired premise transports exactly that to `Δ⋉ᶜ`.
Read against `Δᶜ` it was the unshifted one, and nothing could have fixed
it.  One new one-line inversion was needed, `bindR-inj`.

CONSEQUENTLY THE INTERFACE SHRANK AGAIN.  `strong-rep-nu.Preservation.Stage1`
takes `crossΛ`, `addUnbind0` and `repWeaken` — `cancel` is gone, as `peel`
and `idpush` went before it.  `strong-rep-nu.TypeSafety.Stage1` and
`proof/TypeSafety.agda` follow.  No parameter of this development is known
false any more: the four that remain (`CrossΛTyping`, `AddUnbind0Typing`,
`RepWeakenTyping` for preservation, `MergedReading` for progress) are
open, plausible obligations pending review.

WHAT THE HISTORY MODULES BECAME, and the choice made for each.
`notes/CancelRShiftWall.agda` KEEPS its refutation machine-checked, by
stating the old preservation case LOCALLY as `CancelRCase°` — the device
`strong-rep-store/notes/ReUnlockWall.agda` already uses for the pre-`conv-bind-live`
conversion judgement.  So `cancelR-case°-false : ¬ CancelRCase°` still
runs, the `Δ*` configuration and the redex typing are untouched, and a new
§6 closes the module: the repaired rule fires on the same configuration
and its contractum is retyped by `preserve-CancelR` itself.  Only the old
rule's `step*` had to go, since its constructor no longer exists.  The
wall module now sits BELOW the proof scripts in `All.agda` for that
reason.  `strong-rep-store/notes/CancelRReachabilityWitness.agda` becomes the before/after
record: the before half is prose (its equations were about a constructor
that is gone), the after half is `Src-eval` plus the pinned state-9 redex,
the pinned state-10 contractum, the six contexts the run builds, both
conjuncts, and the repaired premises assembled into an actual `CancelR`
step.  `strong-rep-store/notes/RawRunProbe.agda` is KEPT as a separate module rather than
folded in, because it checks something the witness cannot: `eval` refuses
to continue past an ill-typed state, so its count is partly a statement
about the checker, while the raw step function carries no typing at all.
Agreement between the two is an independent check.

WHAT WAS NOT DONE, deliberately.  `MergedReading`'s statement could now
SHRINK — with both id-layer rules reading at `Δ₁ᶜ`, `proof/Progress.agda`
no longer consumes its outer `Keeps (names Δᶜ) (names Δ⋉ᶜ)` component.
The statement is under review and shrinking it is a separate decision, so
it stands unchanged with a note at the definition.

## 2026-09-20 — representation-only renaming is its own traversal

THE CONCRETE `Peel` TERM.  The reduction rule still produces

    (V · (renᴹ² (ren² idᵗ (wkN (numBinds Θ))) W
              ⟪ dualBoundary Θ , s′ ⟫)) ⟪ Θ , t ⟫ .

Its ordinary component is pointwise the identity: annotations, conversions
and ordinary unbind/bind names do not move.  Jeremy's instruction was:
"Regarding RepWeakenTyping, one of those renamings is with the identity. We
should have a separate lemma about that. Then simplify the statement of
RepWeakenTyping with the identity lemma."  The rule itself is unchanged.

THE NEW OPERATION.  `renᴹᴿ : Renameᵗ → Term → Term` is a genuine
representation-only traversal.  It leaves ordinary annotations, type
arguments, conversions and ordinary change names untouched; it renames bind
payloads, representation change names and recursively occurring
representation material.  Its boundary scope and change actions are `renᴮᴿ` and
`renᶠᴿ`.

THE IDENTITY LEMMA AND THE REVIEW STATEMENT.  The bridge is

    renᴹ²-ord-id : ∀ {ρᵗ ρʳ} → (∀ X → ρᵗ X ≡ X) → ∀ M
      → renᴹ² (ren² ρᵗ ρʳ) M ≡ renᴹᴿ ρʳ M

and the simplified obligation is

    RepWeakenTyping : Set
    RepWeakenTyping = ∀ {Δ W A} (Rs : List Ty)
      → Δ ∣ [] ⊢ W ⦂ A
      → extendReps Rs Δ ∣ [] ⊢ renᴹᴿ (wkN (length Rs)) W ⦂ A .

`preserve-Peel` applies this obligation and transports the resulting inner
boundary with `sym (renᴹ²-ord-id (λ X → refl) W)`, so its conclusion still
matches the reduction rule verbatim.  No proof of `RepWeakenTyping` is added;
only its form changes under Jeremy's instruction.

## 2026-09-20 — `RepWeakenTyping` is PROVED, at a CUT, with one premise
## added

Jeremy's instruction was "first prove RepWeakenTyping".  It is proved,
`strong-rep-nu.proof.RepWeaken.rep-weaken-⊢`, and `PeelCase` is therefore
UNCONDITIONAL: `strong-rep-nu.Preservation.Stage1` now takes only `crossΛ` and
`addUnbind0`, and the two `TypeSafety` stages follow.

THE STATEMENT NEEDED A PREMISE, and the simplified form landed that
morning is FALSE without it.  `extendReps Rs Δ` pushes the payloads `Rs`
onto the representation context WITHOUT checking them, but a boundary
inside the crossing argument has to be RETYPED at the weakened context,
and `env` stores a `BoundaryWf` whose `bw-exterior` is a `WfCtx` of that
context — which demands `WfRepCtx`, that is, that every stored payload be
well formed where it is written.  The counterexample is as small as the
development allows: `β-seven` at the EMPTY context, weakened by the single
payload `` ` 0 ``.  The renamed term is `β-seven` itself — `renᴮᴿ (wkN 1)
TyBetaBoundary` IS `TyBetaBoundary`, since the boundary scope's one change sits
inside its own one-wide bind block and `extᵗ (wkN 1) 0 ≡ 0` — so the conclusion
asks for the same term at a context whose only representation binding is
`bindR (` 0)`, and `[] ⊢ᴿ ` 0` has no derivation.  Machine-checked:
`no-rep-weaken : ¬ RepWeakenTyping₀`, `notes/RepWeakenBindsWall.agda`.

The repair is one premise, and it costs nothing:

    RepWeakenTyping : Set
    RepWeakenTyping = ∀ {Δ W A} (Rs : List Ty)
      → reps Δ ⊢ᴮ Rs
      → Δ ∣ [] ⊢ W ⦂ A
      → extendReps Rs Δ ∣ [] ⊢ renᴹᴿ (wkN (length Rs)) W ⦂ A

At the one call site — `Peel`'s crossing argument,
`strong-rep-nu.proof.PeelDual` §3 — the premise is `bw-binds mwΘ` of the very
boundary being crossed, already stored in the redex's own typing
derivation.  Nothing else about `preserve-Peel` changed, and the reduction
rule is untouched.

THE WORKHORSE IS THE CUT.  The induction goes under `Λ`, which pushes one
`abstR`, and under a boundary, which pushes a whole bind block; so the
inserted block stops being at the HEAD of the representation context and
the name map stops being the exterior's.  Rather than carry an
insertion-at-depth-k operation with its own arithmetic, the insertion is
ABSTRACTED into an arbitrary representation renaming ρ together with the
four facts it must supply, and the name map is renamed POINTWISE:

    record RepWk (ρ : Renameᵗ) (Ξ Ξ′ : RepCtx) : Set where
      field
        wk-inj  : Injᵗ ρ
        wk-look : ∀ {α b} → Ξ ∋ˡ α := b → ∃[ b′ ] (Ξ′ ∋ˡ ρ α := b′)
        wk-bind : ∀ {α b} → Ξ ∋ʳ α := b
                → Ξ′ ∋ʳ ρ α := renRepBinding ρ b
        wk-reps : WfRepCtx Ξ → WfRepCtx Ξ′

    ⊢renᴿ : ∀ {Ξ Ξ′ η ρ Γ M A}
      → RepWk ρ Ξ Ξ′
      → (Ξ ∣ η) ∣ Γ ⊢ M ⦂ A
      → (Ξ′ ∣ map ρ η) ∣ Γ ⊢ renᴹᴿ ρ M ⦂ A

Three fields are the three `WfCtx` obligations one universe down.  The
fourth, INJECTIVITY, is the one that is easy to miss: an `unbind` records
that the name it deleted is now FRESH, and freshness is not preserved by a
renaming that identifies two representation variables.

The cut is then entirely in the closure lemmas, `strong-rep-nu.Boundary` §3d:
`repwk-abst` takes `RepWk ρ` to `RepWk (extᵗ ρ)` across one `abstR`, and
`repwk-push` takes it to `RepWk (extN (length Rs) ρ)` across a whole
parallel bind block — which is exactly how `renᴹᴿ` recurses (`extᵗ ρ`
under `Λ`, `extN (numBinds Θ) ρ` under a boundary).  The head insertion is
one instance, `repwk-wkN Rs bs : RepWk (wkN (length Rs)) Ξ
(pushRepBinds Rs Ξ)`, and the theorem is `⊢renᴿ` run at it, modulo
`map (wkN n) η ≡ shiftRVars n η`.

TWO DIRECTIONS OF GENERALISATION, as expected.  The term context Γ is
arbitrary and passes through UNCHANGED — the variable rule does not read
the type context at all, and no ordinary type spelling moves under a
representation renaming — so the `⊢ƛ` case needs nothing.  The depth is
the cut, above.

THE HARD CASE IS `env`, and every one of its six premises transports by a
per-relation lemma, in the style §3a already used:

  * `bw-exterior` by `wfctx-ren` (the three `WfCtx` fields: `wk-reps`,
    `validNames-ren`, `unique-ren`);
  * `bw-binds` by `binds-ren`, which is `wfᴿ-rename` at the ref-level
    transport `wk-ref` — a reference at local depth m is either local,
    and then untouched, or free, and then renamed, which is precisely
    what `extN m ρ` does;
  * the two readings by `interior-ren` and `conversion-ren`, which are
    `changes-ren`/`conv-changes-ren` over `del-ren`, `ins-ren`,
    `fresh-ren` and `∋ˡ-ren`.  NOTHING here is arithmetic on ordinary
    positions: an unbind deletes at the SAME position and a bind inserts
    at the same position, which is why the ordinary spelling survives;
  * the conversion's TYPING by `conv-ren` (strong-rep-nu.Conversion §2d).  A
    conversion is REP-FREE, so the conversion and both of its types come
    through UNCHANGED; what moves is the context it is read on, and the
    lookup square it cites now reads a renamed representation variable
    with a renamed payload (`∋:=-ren`);
  * the two alignment premises by `same-ren` — `SameTy` at
    `extN (numBinds Θ) ρ` on both sides, and `SameTyExt` at ρ on the
    exterior side and `extN (numBinds Θ) ρ` on the conversion side, the
    two related by `renameᵗ (extN n ρ) (shiftRep n R) ≡
    shiftRep n (renameᵗ ρ R)`;
  * `Δ ⊢ᵗ Bₑ` by `wf-ren-rep`, which is pure position-monotonicity.

`TyBeta`-minted boundaries inside the argument, `instantiate` boundary scopes
and unbind/bind change lists are NOT special-cased anywhere: they are
`env`s and change runs like any other, and the generic transports cover
them.

THREE SMALL RELOCATIONS, in the closed-world spirit.  `extN` moved from
`TermSubst.agda` to `strong-rep-nu.Ctx` §8, and `renᶠᴿ`/`renᴮᴿ` from
`TermSubst.agda` to `strong-rep-nu.Boundary` §2/§3, because the renaming
metatheory has to be stated below `Conversion.agda` (which `TermSubst`
imports) and over exactly those operations.  No definition changed; the
one `using (extN)` import, in `TypeCheck.agda`, was dropped since
`strong-rep-nu.Ctx` is already opened there.  `strong-rep-nu.Ctx` §8 also gains the
`renameᵗ` toolkit the transport needs — congruence, fusion, and
`renameᵗ (extᵗ ρ) ∘ ⇑ᵗ ≡ ⇑ᵗ ∘ renameᵗ ρ` — which `Types.agda` did not
have and which, by the branch's standing rule, does not go there.

WHAT IS LEFT.  The review queue is now `CrossΛTyping`, `AddUnbind0Typing`
(preservation) and `MergedReading` (progress).  The first two are the same
shape as this one — `crossΛᴹ`'s `renᴹ² (ren² idᵗ suc) W` is
`renᴹᴿ suc W` by `renᴹ²-ord-id`, and `AddUnbind0Typing`'s mover is
`renᴹᴿ (extN (numBinds Θ) suc) W` — so `⊢renᴿ` is very likely most of
both; what they add is a BINDER (`underΛ`, `addUnbind0`) on top of the
renaming, which this lemma does not.  That is a separate landing.

## 2026-09-20 — `CrossΛTyping` is PROVED by one unbound `env`

THE CONCRETE CROSSING TERM is `Examples.agda` §5's image

    Wsub = ($ 7) ⟪ boundary [] [] , seal 0 ⟫

at type `` ` 0 ``.  Crossing it through `Λ` produces

    (($ 7) ⟪ boundary [] [] , seal 0 ⟫)
      ⟪ boundary [] (unbind 0 0 ∷ []) , id (` 1) ⟫ .

The `seal 0` is an ORDINARY name and stays `seal 0`.  The new outer unbind
deletes ordinary name zero for the inner term, while its conversion reading
skips that unbind and retains the name needed by `id (` 1)`.  This is the
exact term `cross-Λ-⊢` now types.

THE STATEMENT HOLDS AS WRITTEN.  No premise and no conclusion changed:

    CrossΛTyping = ∀ {Δ W A}
      → WfCtx Δ
      → Δ ⊢ᵗ A
      → Δ ∣ [] ⊢ W ⦂ A
      → underΛ Δ ∣ [] ⊢ crossΛᴹ W A ⦂ ⇑ᵗ A .

The proof is `strong-rep-nu.proof.RepWeaken.cross-Λ-⊢`, beside
`rep-weaken-⊢`, because both use the same general typing transport
`⊢renᴿ`.  First `renᴹ²-ord-id (λ X → refl) W` exposes the mover as
`renᴹᴿ suc W`.  The new base instance

    repwk-abst₀ : RepWk suc Ξ (abstR ∷ Ξ)

then types that moved term at

    (abstR ∷ reps Δ) ∣ shiftReps (names Δ) .

One zero-bind boundary supplies the ordinary side of the crossing.  Its
exterior and conversion context are

    underΛ Δ
      = (abstR ∷ reps Δ) ∣ (0 ∷ shiftReps (names Δ)) ,

and its interior is the moved term's context above.  `mkId (⇑ᵗ A)` is
well formed at the exterior by the ordinary `WfRen-wk` transport.  If `A`
reads as `R` at `Δ` then the inner `A` reads as `⇑ᵗ R` by
`same-ren suc`, while the conversion's `⇑ᵗ A` reads as the same `⇑ᵗ R`
by `same-weaken`.  The exterior alignment is reflexive because the frame
has zero representation binds.

THE INTERFACE SHRANK.  `strong-rep-nu.Preservation.Stage1` now takes ONLY
`addUnbind0`; it plugs `cross-Λ-⊢` into `proof/Preserve.Impl`, whose
downstream-parameter shape stays unchanged just as it does for `Peel`,
`CancelR` and `IdPush`.  `strong-rep-nu.TypeSafety.Stage1` and
`strong-rep-nu.proof.TypeSafety.Stage1` now take `merged-reading` plus
`addUnbind0`.  The review queue is exactly `AddUnbind0Typing` and
`MergedReading`.

## 2026-09-20 — `AddUnbind0Typing` is REFUTED, and with it PRESERVATION:
## `TyPeelR-⟪⟫` weakens its moved conversion in the wrong name map

Jeremy's instruction was "now prove AddUnbind0Typing, same approach, though
consider decomposing into simpler and more general lemmas".  The
decomposition is right and two of its three parts hold; the third does
not, and it is the RULE that is wrong, not the statement's premises.  The
wall is `strong-rep-store/notes/AddLock0Wall.agda`, and it is reached from a CLOSED, PLAIN
System F program.

THE DECOMPOSITION, AS PLANNED.  The move has three orthogonal parts.

  (1) THE TERM'S MOVE IS REPRESENTATION-ONLY.
      `renᴹ² (ren² idᵗ (extN (numBinds Θ) suc)) W` is
      `renᴹᴿ (extN (numBinds Θ) suc) W` by `renᴹ²-ord-id`, and
      `renᴮ² (ren² idᵗ suc) Θ` is `renᴮᴿ suc Θ` by `renᴮ²-ord-id` — the
      boundary clause of the former already contains the latter, so no
      new identity lemma was needed.  The new exterior inserts `bindR P`
      at the HEAD of the representation context, which is
      `repwk-cons₀` (below) pushed through `repwk-push` to the depth
      `numBinds Θ` where the moved term lives.  `⊢renᴿ`
      (`proof/RepWeaken.agda`) then types the moved term, exactly as it
      does for `Peel` and for `crossΛ`.  THIS PART IS SOUND.

  (2) THE CONVERSION AND THE TYPE MOVE IN THE ORDINARY UNIVERSE.
      `` `∀ (renᶜ (extᵗ suc) s) `` is `renᶜ suc` of the whole
      conversion and `` `∀ (renameᵗ (extᵗ suc) A) `` is `renameᵗ suc` of
      the whole type: both say the new ordinary name is inserted at
      POSITION ZERO of the map they are read on.  THIS IS WHERE IT
      BREAKS — see below.

  (3) THE BOUNDARY SCOPE READINGS.  The INTERIOR reading of
      `addUnbind0 (renᴮᴿ suc Θ)` at the new exterior is the renamed
      interior reading of Θ: `addUnbind0` APPENDS `unbind 0 (numBinds Θ)`,
      a change list acts head-LAST, so that unbind runs FIRST and deletes
      the new ordinary name before any of Θ's changes run.  The unbind's
      two premises are free — `ValidRVar` of the new head binding and
      freshness of name zero in a shifted map.  THIS HALF IS SOUND.  The
      CONVERSION reading is not: `conv-unbind` SKIPS unbinds.

WHY THE CONVERSION READING IS DIFFERENT.  A conversion context is the
UNION of the names live anywhere along the boundary scope — that is what the
2026-09-17 re-bind clause settled — so the appended unbind does NOT
remove the new ordinary name there.  It stays in the map while Θ's own
changes run, and every `bind X α` of Θ inserts at position X of a map
that already carries it.  The new name is therefore DISPLACED, by one
place per bind that inserts in front of it, and `renᶜ suc` — correct
only if it landed at position zero — is then wrong at every position
below it.

ONE `TyBeta` IS ENOUGH.  `instantiate R Θ` appends `bind 0 0`, so the
smallest boundary the language mints already has the offending shape.  In
the wall's run the moved boundary's conversion context goes

    (bindR `ℕ ∷ abstR ∷ [])             ∣ (0 ∷ [])       -- before
    (bindR `ℕ ∷ bindR `𝔹 ∷ abstR ∷ [])  ∣ (0 ∷ 1 ∷ [])   -- after

(`conv-before`, `conv-after`, both machine-checked).  The new name is at
position ONE; position zero still names the `TyBeta` binder.  `renᶜ suc`
pushes the conversion's occurrences of position 0 onto position 1 — onto
the NEW binder, whose payload is the type argument's representation.  So
`seal 1 ↦ unseal 1`, which converted `` ` 1 ⇒ ` 1 `` to `` `ℕ ⇒ `ℕ ``,
becomes `seal 2 ↦ unseal 2`, which converts `` ` 2 ⇒ ` 2 `` to
`` `𝔹 ⇒ `𝔹 ``, and `env`'s exterior alignment `SameTyExt` has to relate
`` `∀ (`ℕ ⇒ `ℕ) `` to `` `∀ (`𝔹 ⇒ `𝔹) ``.  It cannot.

THE PROGRAM.  No boundary is written by hand:

    Src = (λf : ∀X. ℕ⇒ℕ. ΛX. f [𝔹]) · ((ΛY. ΛZ. λx:Y. x) [ℕ])

typed at `` `∀ (`ℕ ⇒ `ℕ) `` by `TypeCheck.agda`'s `tc`.  Its run is
`TyBeta` (which packages `ΛZ. λx:Y. x` behind
`` `∀ (seal 1 ↦ unseal 1) ``, a conversion that MENTIONS the binder
being instantiated), then `Beta` (whose `crossΛᴹ` carries that value
under the new `Λ` inside a SECOND `` `∀ `` boundary), then
`TyPeelR-⟪⟫` on the resulting two-layer value.  The third contractum has
NO typing derivation — the wall proves that, rather than relying on
`check⊢`'s refusal, by `conversion-functional` (the conversion context is
a function of the boundary scope and its exterior), `conv-types-unique` (the
moved conversion's types are then forced) and the `SameTyExt` clash
above.  Hence

    no-addUnbind0 : ¬ AddUnbind0Typing
    no-preservation : ¬ Preservation
    no-preservation*: ¬ Preservation*

WHY NO PREMISE REPAIRS IT, and what does.  The offending spelling is in
the CONTRACTUM, so no hypothesis on the redex can change it; and there is
no renaming to substitute, because where the new name lands depends on
Θ's own binds.  This is the SAME defect the crossing audit found for
`Peel` on 2026-09-18 — "not merely a renumbering of the same one" — and
it wants the same repair: `TyPeelR-⟪⟫` should NAME the moved conversion
and carry a `SameConv` relating it to the original across the two
conversion contexts, with `weaken`/`Q` (`Conversion.agda` §2b,
`Boundary.agda` §3b) supplying the witness and `proof/Progress.agda`
deriving the premise as it already does for `Peel`.  That is a rule
change, so it is Jeremy's call; `Reduction.agda` and `Terms.agda` are
untouched.

THE ONE LEMMA THAT LANDED.  `repwk-cons₀` (`Boundary.agda` §3d)
generalises `repwk-abst₀` from an abstract head binding to ANY head
binding:

    repwk-cons₀ : ∀ {Ξ : RepCtx} (b₀ : RepBinding)
      → (WfRepCtx Ξ → WfRepCtx (b₀ ∷ Ξ))
      → RepWk suc Ξ (b₀ ∷ Ξ)

Three of `RepWk`'s four fields do not look at the binding at all — a name
lookup only moves one place further in, and injectivity is `suc`'s — so
the only input is the WEAKEST form of the insertion's own
well-formedness, the step `WfRepCtx Ξ → WfRepCtx (b₀ ∷ Ξ)`, which is
`wf-abstR` for `abstR` and `wf-bindR w` for `bindR R`.  `repwk-abst₀` is
now its `abstR` instance, so nothing downstream changed.  The `bindR`
instance is what part (1) above needs, and it is ready for the repaired
rule.  The interior half of part (3) was NOT written: it has no consumer
until the rule is repaired, and this branch does not keep dead code.

WHAT THE PUBLIC SURFACE SAYS NOW.  `strong-rep-nu.Preservation.Stage1` and
`strong-rep-nu.TypeSafety.Stage1` keep their `addUnbind0` parameter, but that
parameter is KNOWN FALSE: they are conditional theorems with a refuted
hypothesis, kept so that the assembled preservation proof survives the
rule repair.  `MergedReading` is unaffected and remains an open,
plausible obligation pending review.

## 2026-09-20 — the `TyPeelR-⟪⟫` repair is APPROVED and INSTALLED: the moved
## conversion is NAMED, pinned by `SameConv`, against the OLD context viewed
## through the representation renaming

Jeremy approved the repair the wall of the previous entry forces, on the
condition that it be installed on a POSITIVE experiment.  It was, and it
is installed.

THE RULE, AS IT NOW READS (`Reduction.agda`):

    TyPeelR-⟪⟫ : ∀ {Δ Δᵢ Δᵢ⁺ Δᶜ Δ′ᶜ Δ″ᶜ W Θ′ s′ s″ Θ s B A R
                      Bᵢ Bᵢ′ Bₑ} → Value W
      → Δ ⊢ⁱ Θ ⇒ Δᵢ
      → Δ ⊢ᶜ Θ ⇒ Δᶜ
      → Δᵢ ⊢ᶜ Θ′ ⇒ Δ′ᶜ
      → Δ ⊢ⁱ instantiate R Θ ⇒ Δᵢ⁺
      → Δᵢ⁺ ⊢ᶜ addUnbind0 (renᴮ² (ren² idᵗ suc) Θ′) ⇒ Δ″ᶜ
      → SameConv (underΛ Δ″ᶜ) s″
          (underΛ
            (renNameCtx (extN (numBinds Θ′) suc) Δ″ᶜ Δ′ᶜ)) s′
      → underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ
      → SameTy (underΛ Δᵢ) Bᵢ′ (underΛ Δᶜ) Bᵢ
      → Δ ⊢ᶜ A ~ R
      → Δ ⊢ ((W ⟪ Θ′ , `∀ s′ ⟫) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
          -→ ((renᴹ² (ren² idᵗ (extN (numBinds Θ′) suc)) W
                 ⟪ addUnbind0 (renᴮ² (ren² idᵗ suc) Θ′)
                 , `∀ s″ ⟫)
                ·[ renameᵗ (extᵗ suc) Bᵢ′ , ` 0 ])
               ⟪ instantiate R Θ , instReveal 0 s ⟫

Three premises are new and one spelling changed: the contractum's
`` `∀ (renᶜ (extᵗ suc) s′) `` became `` `∀ s″ ``.  Everything else — the
`addUnbind0` frame, the outer frame, the minted `instReveal 0 s`, the
pushed-in annotation and the type argument `` ` 0 `` — is untouched.  This
is exactly the shape `Peel` got on 2026-09-18.

THE ONE DESIGN POINT THAT IS NOT `Peel`'s: `renNameCtx`.  The old
conversion context `Δ′ᶜ` is read through

    renNameCtx ρ target source = reps target ∣ map ρ (names source)

at `ρ = extN (numBinds Θ′) suc` — the representation renaming the inserted
binder makes.  The ordinary POSITIONS of `Δ′ᶜ` are kept; what each denotes
moves, because Θ′'s own bind block stays at representation indices
`0 … numBinds Θ′ - 1` and everything below it is pushed past the new
binder.  Taking `reps` from the TARGET is what makes
`proof/PeelDual.weaken-⊢` applicable later: its premise is
`reps Γ′ ≡ reps Γ`.

The view is NOT optional.  Replacing `renNameCtx … Δ″ᶜ Δ′ᶜ` by plain `Δ′ᶜ`
was measured: run 9 of `notes/RepresentationReductionExamples.agda` — the
one whose payload `∀Z. Z ⇒ X` carries a FREE representation variable —
then loses its type at step 8 (`traceLen ≡ 8`, `repKept ≡ false`), because
a free representation index is compared against the newly inserted binder.

THE MEASUREMENT.  The wall's own program,

    Src = (λf : ∀X. ℕ⇒ℕ. ΛX. f [𝔹]) · ((ΛY. ΛZ. λx:Y. x) [ℕ])

now runs `TyBeta`, `Beta`, `TyPeelR-⟪⟫`, `TyPeelR-Λ` to a VALUE with every
state type-checked:

    Src-eval : Reaches 4 4 Src-⊢ Dst

Its third state is the state the wall refutes with ONE conversion leaf
changed — `seal 1 ↦ unseal 1` where the old rule wrote
`seal 2 ↦ unseal 2`; the frames are identical.  Here the correct
weakening is the IDENTITY, which is precisely what no fixed renaming
delivers.  `strong-rep-store/notes/AddLock0Wall.agda` checks all of that
(`repaired-state`, `good≢bad`), keeps the retired statement as a LOCAL
`AddUnbind0Typing°` and still refutes THAT, and states no refutation of
anything live.

THE SUITE IS BYTE-IDENTICAL.  `notes/RepresentationReductionExamples.agda`
and `Examples.agda` are unchanged and green, at the same endpoints and the
same step counts.  `TyPeelR-⟪⟫` fires in several of those runs; the
carried premise is invisible there because `Eval.agda`'s
`bdyPremises?` builds it by the same `weaken?` search the checker already
ran for `Peel`.

PROGRESS TOOK NO NEW PARAMETER — the point at which the experiment and the
install diverge.  The experiment left the moved boundary's reading as a
second stage-1 parameter; it is PROVED here, as
`proof/Progress.addUnbind0-reading`, from three pieces:

  * `conv-weaken` and `conv-snoc-unbind` (`Boundary.agda` §3, new): a
    conversion reading is monotone in its starting name set, and an
    APPENDED unbind — which runs FIRST — is skipped by a conversion reading.
  * `addUnbind0-conversion-ren` (`Boundary.agda` §3d, new): those two after
    `conv-changes-ren`, giving
    `map (extN (numBinds Θ) suc) (names Γᶜ) ⊆ᵃ names Γ′ᶜ`.  The RENAMED
    inclusion is the true one; the unrenamed one is false exactly when the
    old context names a representation below the insertion.
  * `instantiate-boundarywf` (`proof/Preserve.agda`, hoisted out of the two
    `mwᵢ` blocks that already built it): the instantiated frame is again a
    `BoundaryWf`, which supplies the `RepWk suc` witness
    `repwk-cons₀ (bindR (shiftBy (numBinds Θ) R)) …`.

THE ORDER OF THE TWO TRANSPORTS IS THE WHOLE KNOT.  `readable` reads the
old conversion at `underΛ Δ′ᶜ`.  The rule wants it at
`underΛ (renNameCtx ρ Δ″ᶜ Δ′ᶜ)`, whose name map is `map ρ (names Δ′ᶜ)`.
So the reading is REPRESENTATION-SHIFTED FIRST — `sameᶜ-ren (extᵗ ρ)`,
carried past the `Λ` by `names-underΛ-ren` — and only THEN weakened into
the moved boundary's own context through `⊆ᵃ-underΛ keep`.  Weakening
first, which is what the experiment did, leaves the reading in the
UNRENAMED map and the goal unprovable; that was the one open hole the
experiment reported.  `strong-rep-nu.Progress.Stage1` therefore still takes
exactly one parameter, `MergedReading`.

AND THE RESHAPED PARAMETER IS PROVED — PRESERVATION IS UNCONDITIONAL.
`AddUnbind0Typing` (`proof/Preserve.agda`) was RESHAPED with the rule — it
now receives `Δ ⊢ᶜ Θ ⇒ Δᶜ`, the moved reading and the `SameConv`, and names
the moved spelling — and `proof/AddUnbind0.agda` proves it, the same day.  It
is the `env`-to-`env` transport across one inserted representation binder
and one fresh ordinary name, and each of the six `env` premises moves by a
lemma that already existed or by one small new one:

  * `bw-exterior` is the statement's own `WfCtx` premise;
  * `bw-binds` by `binds-ren` at `repwk-cons₀ (bindR P) …`;
  * `bw-interior` by `addUnbind0-interior-ren` (`Boundary.agda` §3d, NEW —
    the interior half of `addUnbind0-conversion-ren`).  It is the SHORT half:
    an interior reading PERFORMS the appended unbind, which runs first and
    deletes the fresh ordinary name, so what is left is exactly
    `interior-ren` with no ordinary position moved.  The conversion half is
    the long one precisely because it SKIPS that unbind;
  * `bw-conversion` is the rule's own premise;
  * the interior TERM by `proof/RepWeaken.⊢renᴿ` at
    `repwk-push (repwk-cons₀ (bindR P) …) (binds Θ)` — purely
    representation, which is what `renᴹᴿ` was for;
  * the CONVERSION by `conv-ren` (`Conversion.agda` §2d), which moves the
    representation context, then `proof/PeelDual.weaken-⊢`, which moves
    the name map.  `weaken-⊢` demands `reps Γ′ ≡ reps Γ`, and THAT is what
    `renNameCtx` was shaped to satisfy: it keeps the old ordinary positions
    and takes the representation context from the moved side.  Its
    retention argument is the `keep` of `addUnbind0-conversion-ren`, pushed
    onto the rule's own `Δ⁺ᶜ` by `conversion-functional`;
  * the two `SameTy` premises come back FROM `weaken-⊢`, paired with the
    old readings; `same-ren` supplies the moved side and `same-rep-unique`
    identifies the two representations;
  * the exterior `SameTyExt` by `same-weaken` for the fresh ordinary name
    and `renameᵗ-shiftBy` for the bind-block shift — the one place the
    proof has to know that `shiftRep k` COMMUTES with the representation
    renaming.

One inversion was added, `same-∀⁻` (`proof/AddUnbind0.agda` §1): `SameTyExt`
compares against `shiftRep n R`, stuck on a variable `n`, so a `` `∀ ``'s
exterior reading cannot be matched directly.  It is `conv-all-inv`'s
counterpart one universe up.  One definition was hoisted rather than
written twice: `instantiate-boundarywf` (`proof/Preserve.agda`), which was
already built inline in both `preserve-TyPeelR` clauses.

CONSEQUENTLY `strong-rep-nu.Preservation.Stage1` IS GONE.  `preservation` and
`preservation*` are stated outright, unconditionally.  `strong-rep-nu.TypeSafety`
exports them unconditionally too, and its `Stage1` — like
`strong-rep-nu.Progress.Stage1` and `strong-rep-nu.proof.TypeSafety.Stage1` — now takes
exactly ONE parameter, `MergedReading`, which remains the single open,
plausible obligation pending review.  Nothing is postulated anywhere.

## 2026-09-20 — the context layer is split by SUBJECT: definitions, their
## lemmas, and the boundary scope layer above them

Three of Jeremy's cleanup items are one refactor: nothing is proved or
restated, every declaration is byte-identical to the one it replaces, and
only its ADDRESS changes.  The rule applied is SUBJECT, not size: a
declaration whose statement mentions only `RepCtx`, `TyCtx` or `Ctxᵗ` is
context material; one that mentions `Change` or `Boundary` is boundary scope
material and stays where it was.  A declaration that mixes the two stays
in `Boundary.agda`.

The resulting module map, bottom up:

  * `Types.agda` — `Ty`, `Renameᵗ`/`Substᵗ`, `renameᵗ`, `substᵗ`, the
    single-substitution operations.  Definitions only.
  * `proof/Types.agda` (NEW) — `substᵗ-cong`, `extsᵗ-renᵗ`,
    `substᵗ-renᵗ`.  Imports `strong-rep-nu.Types` and the standard library, and
    nothing else: it is the lowest proof module in the development.
  * `Ctx.agda` — the two de Bruijn universes and every RELATION on them:
    lookup (`_∋ˡ_:=_`, `_∋ʳ_:=_`, `_∋_:=_`, and the name-map queries
    `_∋ʳ_`, `_∋ᵅ_`, `_⊆ᵃ_`), ordinary type formation, representation
    payloads, the two readings of `Ty`, well-formedness, `extN`/`Injᵗ`,
    and — new here, from `Boundary` §1/§2/§3d — the representation-binder
    blocks (`shiftBy`, `pushRepBinds`, `shiftRVars`, `extendReps`,
    `_⊢ᴮ_`, `shiftByᵇ`) as §9, the insert/delete relations
    (`_⊢+_at_⇒_`, `_⊢-_at_⇒_`) as §10, and `RepWk` as §11.
  * `proof/Ctx.agda` (NEW) — every lemma about the above, in two halves:
    the ones that used to sit in `Ctx.agda` (§1–§2: `∋ˡ-det`,
    `same-target-unique`, `sameTy-src-unique`, the `renameᵗ` algebra, the
    `map ρ` transport of the name map, …) and the context-only ones that
    used to sit in `Boundary.agda` (§3: `insert-functional`, the `∋ᵅ`
    monotonicity family, `pigeon`, `live?`, `wfᴿ-rename`,
    `wfRepCtx-push`, `validNames-push`, the `repwk-*` closure lemmas,
    `wfctx-ren`, `∋:=-ren`, …).
  * `Boundary.agda` — `Change`, the change judgements, `Boundary`, the
    two induced readings, `dualBoundary`/`rewind`/`_⋉_`/`addUnbind0`/
    `instantiate`, `Q`, `dual-conv-exists`, `BoundaryWf`, and the renaming
    of a boundary scope.  Its own lemmas stay with it; only the context layer
    beneath them left.

The layering stays acyclic and is now three-deep instead of two:
`Types → proof/Types → Ctx → proof/Ctx → Boundary`.  `Ctx.agda` does not
import `Boundary`, and `proof/Ctx.agda` imports only `Types`,
`proof/Types` and `Ctx` — which is what lets a proof module sit that low
at all.  Downstream, twelve files gained `open import strong-rep-nu.proof.Ctx`;
the rest never used a lemma from either moved group, and the set of names
in scope in every file is exactly what it was before.

Two things did NOT move, and both are deliberate.  The `private` helper
blocks of `Boundary` §3a/§3b (`shiftReps-lookup`, `insert-shift`,
`delete-shift`, `shiftRVars-suc`, `del-shiftRVars`, `ins-shiftRVars`) are
context-only but are proof script for `instantiate`/`step-lift`; moving
them would have made them public, so they stay private where they are
used.  `ΛXCtx` is `Ctxᵗ`-only but exists solely as the domain of `crossΛ`
and `uncrossΛ`, so it stays with them in §4.

`make check` is green, the thirteen-run suite and `Examples.agda` keep
every step count and endpoint (they are typed equalities, so the check
IS the verification), and no `postulate` or hole was introduced.

## 2026-09-21 — `MergedReading` is SHRUNK AND PROVED; the theorem surface
## is unconditional

THE CONCRETE CONSUMERS FIRST. In `progress-unseal`, repaired `CancelR`
reads the cancelled seal's source at the inner conversion context `Δ₁ᶜ`,
and `IdPush` reads its identity variable there too. Both branches use only

    names Δ₁ᶜ ⊆ᵃ names Δ⋉ᶜ

to weaken that source in the merged conversion context. Neither branch
uses the former outer component

    names Δᶜ ⊆ᵃ names Δ⋉ᶜ .

Jeremy's instruction was "now prove MergedReading, shrinking it first since
the outer half is unconsumed". The grep audit found exactly one consumer of
`MergedReading`, those two branches of `progress-unseal`, and confirmed that
their bound outer witness was never read. The statement was therefore
shrunk before proof to

    MergedReading : Set
    MergedReading = ∀ {Δ Δᵢ Δᶜ Δ₁ᵢ Δ₁ᶜ Θ₁ Θ₂}
      → BoundaryWf Δ Θ₂ Δᵢ Δᶜ
      → BoundaryWf Δᵢ Θ₁ Δ₁ᵢ Δ₁ᶜ
      → Σ[ Δ⋉ᶜ ∈ Ctxᵗ ]
          ((extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ)
            × (names Δ₁ᶜ) ⊆ᵃ (names Δ⋉ᶜ))

THE INNER INCLUSION IS NOT RENAMED. This is unlike
`addUnbind0-reading`: no new representation binder is inserted between
`Δ₁ᶜ` and the merged output. Both already live under Θ₂'s bind block
followed by Θ₁'s, so the consumer's direct `names Δ₁ᶜ` inclusion is the
true statement and is what the proof delivers.

THE PROOF IS THE CHANGE-LIST CONCATENATION. The merged changes are

    changes Θ₁ ++ map (underRepBinds (numBinds Θ₁)) (changes Θ₂) .

Because change lists act tail first, the scope-moved Θ₂ conversion runs
first. `conv-changes-lift` transports that reading under Θ₁'s bind block;
`⊆ᵃ-shiftRVars` transports the fact that Θ₂'s conversion reading contains
its interior output. `conv-weaken` then runs Θ₁'s existing conversion
reading from this larger name map and retains its old output. Its fresh
bind branch uses `pigeon`, `ins-le` and `ins-cover` to prove that the
recorded insertion position is still in range; the other branches transport
freshness or reuse an already-live name. `conv-changes-++` concatenates the
two runs. The packaged theorem is
`strong-rep-nu.Boundary.merged-conversion-exists`; no premise was added.

THE MILESTONE. `strong-rep-nu.proof.Progress.Impl` now consumes the proved
`merged-reading`, and `strong-rep-nu.Progress.progress` is stated outright.
`Stage1` is deleted from `strong-rep-nu.Progress`, `strong-rep-nu.proof.TypeSafety` and
`strong-rep-nu.TypeSafety`; `type-safety` is stated outright. Preservation,
progress, type safety, determinism and the no-step property for values are
therefore all unconditional under `--safe`, with no postulates. The review
queue is empty: the two-universe experiment's complete theorem surface is
now proved.

## 2026-09-21 — the reduction suite is MERGED into `Examples.agda`; the
## corpus is one file and its runs are the acceptance test

`notes/RepresentationReductionExamples.agda` (thirteen closed runs) is
merged into `Examples.agda` and DELETED. The two files had grown into one
corpus that cited itself across a module boundary: `Examples.agda` did not
repeat the suite's `J` and `E` but pointed at them, and the suite's
coverage note counted rules fired in both. One file, one map, one gate.

EVERY RUN CARRIES OVER UNCHANGED — same program, same fuel, same step
count, same endpoint. That table is the acceptance test and is now the
head comment of `Examples.agda`. `make check` is green and cold-checking
`Examples.agda` alone is about 4s.

THREE COLLISION RENAMES, all on the incoming side (`Examples.agda` keeps
its names), staying in the suite's own one-letter style:

| suite | was | now | why |
|---|---|---|---|
| run 6, argument still reducing | `R₀` | `U₀` | `R` is the chained representation, §2c |
| run 7, two later binders | `G₀`/`GBod`/`Gbody`/`Gfun` | `V₀`/`VBod`/`Vbody`/`Vfun` | `G` is the two-bind frame, §3 |
| run 8, impredicative identity | `H₀` | `I₀` | `H` is the reveal mirror, §4 |

with `-⊢`, `-eval` and `-run` following each.

THE SECTIONS WERE RENUMBERED so the file reads from the plainest run to
the hardest and ends with the equations and the refutations. Old pointers
resolve through this map:

| old | new |
|---|---|
| suite 1, 2, 3, 5, 6 | §1a `P`, §1b `K`, §1c `J`, §1d `F`, §1e `U` |
| suite 4, 7 | §5a `E`, §5b `V` |
| suite 8, 9 | §6a `I`, §6b `N` |
| suite 10, 11, 12 | §7a `A`, §7b `B`, §7c `C` |
| suite 13 | §8 `S` |
| `Examples` §1, §1a, §1b, §1c | §2, §2a, §2b, §2c |
| `Examples` §2, §3 | §3, §4 |
| `Examples` §4, §4a–c | §9, §9a–c |
| `Examples` §5, §6 | §10, §11 |

Comments elsewhere that cited the suite by module name or run number were
retargeted: `Reduction.agda`, `Boundary.agda`, `proof/Progress.agda`,
`proof/Preserve.agda`, `strong-rep-store/notes/AddLock0Wall.agda`,
`strong-rep-store/notes/ForallPayloadWall.agda`, `strong-rep-store/notes/ReUnlockWall.agda`,
`notes/CrossingAudit.agda`, `strong-rep-store/notes/CancelRReachabilityWitness.agda`,
`notes/PLAN.md`, `notes/CancelRReachability.md`. Dated entries above keep
the old names: they describe the past. `notes/All.agda` lost the import;
`strong-rep-nu.All` already reached `strong-rep-nu.Examples`, so the checked set loses
exactly the deleted module and gains nothing.

## 2026-09-21 — `CtxMorph` is RENAMED `Boundary`: the first component of a
## boundary term is its BOUNDARY SCOPE, not a "context morphism"

Jeremy's handoff (notes/TODO.md): rename context morphism to boundary
scope, `CtxMorph` to `Boundary`, `MorphWf` to `BoundaryWf`, and retarget
every use of the old word.  The Agda names now read

| old | new |
|---|---|
| module `strong-rep-nu.CtxMorph`, file `CtxMorph.agda` | `strong-rep-nu.Boundary`, `Boundary.agda` |
| `CtxMorph`, constructor `morph binds changes` | `Boundary`, `boundary binds changes` |
| `MorphWf`, constructor `mw`, fields `mw-exterior`/`mw-binds`/`mw-interior`/`mw-conversion` | `BoundaryWf`, `bw`, `bw-…` |
| `mw-interior-wf`, `mw-conversion-wf`, `TyBeta-mw` | `bw-interior-wf`, `bw-conversion-wf`, `TyBeta-bw` |
| `dualMorph`, `TyBetaMorph`, `TyBetaMorph-ren-*` | `dualBoundary`, `TyBetaBoundary`, `TyBetaBoundary-ren-*` |
| `morphWf`, `MorphWfResult`, `instantiate-morphwf`, `apply-morph` (TypeCheck) | `boundaryWf`, `BoundaryWfResult`, `instantiate-boundarywf`, `apply-boundary` |

In prose, "context morphism" and "morphism" are "boundary scope"
throughout — the Agda files, `Design.md`, `README.md`, `notes.md` and the
gated notes probes, and the dated entries above (they now speak the new
word even where they describe the past; the git history keeps the old).
Unchanged: the branch name recorded in `notes/PR-morph-pair.md` and
`notes/old/`.  The constructor `boundary` mirrors the type name the way
`morph` mirrored `CtxMorph`; a boundary TERM is still `M ⟪ Θ , c ⟫`, and
the word "boundary" alone still means that term in prose, so the
two-word "boundary scope" is used wherever `Θ` is meant.  `make check`
passes unchanged in content: the rename is exact, no proof moved.

## 2026-09-21 — COLOR PRESERVATION is RESTATED for the two universes:
## the scope map at a residual position is the old one under the move's
## representation renaming

The v7 theorem (strong-v3-design, 31fa0918; retired by the v8 sweep) said
`scopeᵗ Δ₁ ≡ scopeᵗ Δ₂` for the contexts at a hole and at its residual,
and proved it by a push/pop BALANCE on one-hole contexts.  Neither side
of that equation exists here — there is no `scopeᵗ`, and a move can
rename the representation universe.  The restatement
(`ColorPreservation.agda`, layer in `Residual.agda`):

    ColorPreservation = ∀ {Δ L L′ A} {rs : Δ ⊢ L -→* L′} {C M ρ D N}
      → Δ ∣ [] ⊢ L ⦂ A
      → Residuals rs C M ρ D N
      → ∀ {Δ₁ Δ₂} → Δ ⊢C C ⊣ Δ₁ → Δ ⊢C D ⊣ Δ₂
      → names Δ₂ ≡ map ρ (names Δ₁)

A hole's COLOR is its scope map `names Δ₁` — which ordinary names are
live, and which representation variable each denotes.  `Residual r C M ρ
D N` carries the representation renaming ρ the move delivers to the hole
(`holeRen²`); every move but TyBeta's `abstR → bindR R` refinement is
representation-only (proof/ShiftAudit §3), so ρ replaces v7's balance
counting: ordinary POSITIONS never move, only the representation indices
they denote are transported.  Redex nodes are consumed, the `Drop` rules
consume their literal, and `Beta` splits into a `Stable` body residual
and one `CopyResidual` per occurrence that receives the argument — each
`Λ` crossed inside `crossΛᴹ`'s dual adds one boundary frame and one
`suc` to ρ.

Checked today: the layer and statement type-check; the statement holds by
`refl` on a three-step run (TyBeta, Peel, Beta under a Λ) with its full
`Residuals` and `⊢C` derivations — `notes/ColorPreservationProbe.agda`;
and the layer is SOUND — `plug C M` is the step's source and `plug D N`
its contractum (`proof/Residual.agda`, via `plug-renCtx²`,
`plug-substCtx` and `substᵐ-ivar`).  Per the standing protocol the proof
waits on Jeremy's review of the statement; the five decisions embedded in
it are listed in `notes/TODO.md` and on PR #207.

## 2026-09-21 — COLOR PRESERVATION is PROVED; the copy depth index is
## RESTORED; the theorem carries `WfCtx Δ`

Jeremy approved the statement and the constructor name `boundary`
(PR #207); the proof landed the same day.  Two deltas, both flagged on
the PR:

**The depth index (a repair to the reviewed layer).**  Writing
`copy-frame` exposed that `CopyResidual`/`ImageResidual` without v7's
ℕ index admit a WRONG-POSITION derivation: `⇑ᴵ (ival V A)` is again an
`ival`, so when the β-redex's argument is itself a `crossΛᴹ`-shaped
wrapper (reachable: `crossΛᴹ W (` X)` is a value), a depth-1 occurrence
can match `image-here` and claim the UNWRAPPED source position at the
ambient one `Λ` in — take `C₀ = □ ⟪C boundary [] (unbind 0 0 ∷ []) ,
mkId (⇑ᵗ A) ⟫`: the source reading of `C₀` at Δ deletes Δ's name 0,
the target reading at `underΛ Δ` deletes the new binder, and
`names Δ₂ ≡ map idᵗ (names Δ₁)` is FALSE.  The index pins `image-here`
to depth zero, and the copy walk keeps it in sync (`copy-Λ` recurses at
`suc k`); soundness (`proof/Residual.agda`) was index-blind and did not
change.

**`WfCtx Δ` (a premise added to the statement).**  `residuals-color`
re-types each intermediate term by `preservation`, which is conditional
on `WfCtx Δ` — the price of decision 5 (any Δ, since ξ-Λ reduces under
Λ).  `ColorPreservationClosed` at `empty` is the v7-faithful form,
premise-free beyond the typing.  Decision 4 is resolved the other way
too: the typing premise IS needed, at exactly two sites — Peel's
argument (the crossed bind block's `⊢ᴮ`, from the redex's own `env` via
`bw-binds`, feeding `repwk-wkN`) and TyPeelR-⟪⟫ (the refined store's
well-formedness via `instantiate-boundarywf`).

**The proof's shape** (proof/ColorPreservation.agda): per step,
`residual-frame` CONSTRUCTS the target position's frame derivation
together with `names Δ₂ ≡ map ρ (names Δ₁)` — frame-for-frame at every
rule except the three movers; the minted boundary frames' readings are
exactly the §3a interior lemmas (`instantiate-interior` for
TyBeta/TyPeelR-Λ, `dual-interior` for Peel, `rewind-interior` +
`merged-interior` for CancelR/IdPush — for these two the inner
derivation is reused VERBATIM, ShiftAudit's "exact" made literal), plus
the new `crossΛ-interior` for the dual `crossΛᴹ` mints.  The movers go
through the new `⊢C-ren`: transport of `Γ ⊢C C ⊣ Δ₁` along a
`TyRename` with pointwise-id ordinary component, producing
`renCtx² ρ² C`'s derivation with the scope map moved by exactly
`represent (holeRen² ρ² C)` — the boundary case is `interior-ren` over
`RepWk` (§3d), closed under frames by `repwk-abst`/`repwk-push`.  The
slot refinement `abstR → bindR R` at TyBeta/TyPeelR-Λ is `⊢C-len`: the
frame judgment reads the representation store only through `∋ʳ`, i.e.
its length.  `Beta`'s body is `⊢C-substCtx` (boundary frames are
term-closed, so the substitution never moves a frame); its argument is
`copy-frame`/`image-frame` over the depth index, one `crossΛ-interior`
frame and one `moveᴿ suc` transport per `Λ`, composing to the
residual's `holeᴿ suc D ∘ ρ`.  `residuals-color` chains the equations
by `map-∘`.  The probe now also checks the run's equation THROUGH the
theorem (`color-preserved-thm`).

## 2026-09-21 — RULED (Jeremy): the COLOR THEOREM concludes with the
## SIZE of the scope map; the pointwise form is kept, stronger, as
## `ScopeMapPreservation`

"Color is just about type variables and not representation variables" —
so the color theorem proper says a residual position's lexical
type-variable scope keeps its size,

    ColorPreservation      … → length (names Δ₂) ≡ length (names Δ₁)

a corollary (`residuals-color-length`, by `map-length`) of the proved

    ScopeMapPreservation   … → names Δ₂ ≡ map ρ (names Δ₁)

which additionally pins WHICH representation variable each surviving
name denotes, transported along the run's renaming ρ.  Jeremy: "don't
get rid of the current theorem, it's valuable and stronger."  Both have
closed forms at `empty`; the probe checks its run through both.  The
NAME `ColorPreservation` moved to the corollary — flagged on PR #207
for veto.

## 2026-09-21 — strong-rep-nu FORKED from strong-rep-var: the VALUE
## RESTRICTION on `⊢Λ`, and no `ξ-Λ`

Jeremy: "we are going to build a variant of SystemF/agda/strong-rep-var,
in a new directory SystemF/agda/strong-rep-nu.  The first change to
the design I want to experiment with is changing the ⊢Λ typing rule to
require the term N to be a Value and removing the ξ-Λ reduction rule.
Everything else should stay the same for now."

    ⊢Λ : Value N → underΛ Δ ∣ ⤊ Γ ⊢ N ⦂ C → Δ ∣ Γ ⊢ Λ N ⦂ `∀ C
    (ξ-Λ deleted)

WHAT IT TOUCHED.  `Value` moved above the typing judgement in Terms.
`TermSubst` gained `inert-renᶜ` (from `proof/ShiftAudit`), `value-renᴹ²`
(same), `value-renᴹᴿ`, `value-renⁿ`, `value-substᵐ`: every
typing-transport lemma (`⊢renⁿ`, `⊢renᴿ`, `⊢refine`, `⊢substᴹ`) has to
rebuild the `Value N` premise for the term it produces.  `value?` and
`inert?` moved from `Eval` to `TypeCheck` so that `infer` can decide the
premise.  `progress (⊢Λ vN ⊢N) = inj₁ (V-Λ vN)`.  The `ξ-Λ` cases of
`value-¬step`, `det`, `preserve`, `canon-step`, `Drop$-only-numerals`,
`ruleName`, `step`, and the residual `residual-ξ-Λ` with its
`residual-source`/`residual-sound`/`residual-frame` cases, are gone.
`V-Λ` KEEPS `Value N` — redundant on well-typed terms, kept so that
`Value` and the untyped relation stay strong-rep-var's verbatim.

WHAT IT COST IN THE CORPUS.  A closed program is rejected whenever some
`Λ` body is a variable or an application.  Of the 21 closed programs in
Examples, 11 were untouched (P K J F U H I N A B S — identical runs and
step counts, since none of them ever stepped under a `Λ`) and 10 were
rejected (Q D L R G E E-B V C Bg), as were the ColorPreservation probe's
run (a Peel UNDER a Λ) and the AddUnbind0 wall program.  Jeremy's
repair recipe: "insert a lambda to turn the body of the Λ's into a
value, and then also insert extra applications to eliminate those
lambdas" — `ΛZ. x` becomes `ΛZ. λy:ℕ. x` and `(ΛZ. x)[ℕ]` becomes
`((ΛZ. λy:ℕ. x)[ℕ]) · 0`.  The wall program's run grows from 4 steps to
8 and reaches the same `TyPeelR-⟪⟫` state at the top level, inside the
outer `TyBeta` boundary, instead of under the `Λ`; the probe runs its
body at the ambient `underΛ empty` instead of under an outer `Λ`.

## 2026-09-22 — experiment 2 LANDED: the store

Jeremy: "removing the binds field from Boundary and instead make that a
global representation type store … use zero for the fresh address and
push all the existing addresses up by one … have reduction return the
change to the environment instead of the new environment."  The design
note is `notes/RepStoreSketch.md` (fourth revision, rulings R4/R5/R6);
this entry records what LANDED.

WHAT THE STORE IS.  `Boundary = boundary (changes : List Change)` and
nothing else.  The representation a ∀-elimination mints is ALLOCATED on
the AMBIENT representation context at address 0,

    allocate : Ty → Ctxᵗ → Ctxᵗ
    allocate R (Ξ ∣ Δ) = (bindR R ∷ Ξ) ∣ shiftReps Δ

and a step returns the CHANGE it made, `δ : Alloc = none | new R`, so
the contractum lives at `apply δ Δ` and every congruence shifts the
redex's SIBLINGS by `↑ᴹ[ δ ]` (`renᴹᴿ suc`, or the identity).  A
boundary changes NAMES only: `reps Δᵢ ≡ reps Δ ≡ reps Δᶜ`.

THE STATEMENTS AS LANDED (all machine-checked, `make check` green).

    Preservation   = ∀ {Δ M M′ A δ} → WfCtx Δ → Δ ∣ [] ⊢ M ⦂ A
                   → Δ ⊢ M -→ M′ ∣ δ → apply δ Δ ∣ [] ⊢ M′ ⦂ A

    PreservationWf = ∀ {Δ M M′ A δ} → WfCtx Δ → Δ ∣ [] ⊢ M ⦂ A
                   → Δ ⊢ M -→ M′ ∣ δ → WfCtx (apply δ Δ)

    Preservation*  = ∀ {Δ M M′ A} → WfCtx Δ → Δ ∣ [] ⊢ M ⦂ A
                   → (r : Δ ⊢ M -→* M′) → runCtx r ∣ [] ⊢ M′ ⦂ A

    Progress       = ∀ {Δ M A} → Δ ∣ [] ⊢ M ⦂ A
                   → Value M ⊎ (Σ[ M′ ∈ Term ] Σ[ δ ∈ Alloc ]
                                 (Δ ⊢ M -→ M′ ∣ δ))

    ScopeMapPreservation = ∀ {Δ L L′ A} {rs : Δ ⊢ L -→* L′} {C M ρ D N}
      → WfCtx Δ → Δ ∣ [] ⊢ L ⦂ A → Residuals rs C M ρ D N
      → ∀ {Δ₁ Δ₂} → Δ ⊢C C ⊣ Δ₁ → runCtx rs ⊢C D ⊣ Δ₂
      → names Δ₂ ≡ map ρ (names Δ₁)

`ColorPreservation`, its `length` corollary, and both closed forms at
`empty` keep their 2026-09-21 shape.  The one delta in the color layer's
STATEMENT is that the target position is read at `runCtx rs`, the
context the run ends at, rather than at Δ — which is exactly the
renumbering `map ρ` reports.

WHAT THE STORE RETIRED.  `binds`/`numBinds`/`extendReps`/
`pushRepBinds`/`shiftRVars`/`_⊢ᴮ_`/`shiftByᵇ` (Ctx), `underRepBinds`
(Boundary), `renᴮ`/`TyBetaBoundary-ren-Λ` (TermSubst),
`SameTyExt`/`shiftRep` (Ctx — `env`'s exterior premise is now plain
`_⊢_≈_⊣_`), the bind-block lemma family in `proof/Ctx.agda`
(`wfᴿ-push`, `wfRepCtx-push`, `∋ʳ-push`, `∋ʳ-pushᵇ`, `shiftByᵇ-*`,
`∋ˡ-push`, `∋ˡ-shiftRVars`, `⊆ᵃ-shiftRVars`, `validNames-push`,
`fresh-shiftRVars`, `unique-shiftRVars`, `shiftRVars-0`,
`shiftRVars-ren`, `names-ren-push`, `repwk-push`, `repwk-bind`,
`binds-ren`, and their now-dead helpers `extN-+`, `inj-extN`, `wfᴿ-⇑`,
`length-map`, `renameᵗ-shiftBy`), `RepWeakenTyping` (the bind-block
weakening `Peel` consumed — `dual-interior` lands the crossing argument
at the exterior itself, so `Peel` moves it VERBATIM), and
`renCtx²`/`holeRen²`/`moveᴿ`'s bind offset in the residual layer.

WHAT REPLACED IT, in one lemma: the SIBLING SHIFT, today's
representation weakening at `ρ = suc`,

    shift-⊢ : ShiftTyping            -- proof/RepWeaken §2
    shift-⊢ wR ⊢M = ⊢renᴿ (repwk-alloc wR) ⊢M

applied in the four congruences, plus `step-alloc`, which reads off a
step what it did to the store.

WHAT THE WALLS SAY NOW.  `notes/CancelRShiftWall.agda` is DISSOLVED and
kept as a record: the inner layer's conversion context no longer lies
`numBinds Θ₁` representation binders inside its exterior — it lies ZERO
binders inside it (`no-shift`, one line) — so the shift the old premise
dropped does not exist and the old premise and the repaired one have the
same witness on the very configuration that raised the wall.  The
repaired premise stays, for the reason `_⊢_≈_⊣_` has always existed: two
different NAME MAPS, which `strong-rep-store/notes/CancelRReachabilityWitness.agda` still
exhibits at a reachable redex (19 steps, unchanged).
`strong-rep-store/notes/AddLock0Wall.agda` is UNTOUCHED in substance — its defect was
always in the CONVERSION reading, a name-map fact — and its run is still
`Reaches 8 8`.  `notes/RepWeakenBindsWall.agda` keeps its refutation with
LOCAL copies of the retired bind-block machinery.

## EXPERIMENT 3 — THE ONE-LAYER `CancelR` / `IdPush` CONTRACTUM (2026-09-23, approved by Jeremy)

**The question Jeremy asked.**  "Can `IdPush` be simplified by removing
the second boundary, the one with `mkId`, and somehow compensating for
that in the first boundary?"

**The answer: yes, and nothing needs compensating.**  Both rules built

```
  (V ⟪ Θ₁ , c ⟫) ⟪ Θ₂ , unseal Y ⟫
    -→ (V ⟪ Θ₁ ++ Θ₂ , c′ ⟫) ⟪ rewind Θ₂ , mkId A ⟫ ∣ none
```

and the outer layer was a no-op on both counts a boundary has:
`rewind-interior` says its frame's interior IS the exterior it sits at,
and `mkId A : A ⇝ A` converts nothing.  Its only effect was to weaken
the exterior type — and the surviving layer could already be given that
type.  `proof/MoveScope.agda` said so before the change: both
`preserve-IdPush` and `preserve-CancelR` built a local

```
  inner : Δ ∣ [] ⊢ V ⟪ Θ₁ ++ Θ₂ , c′ ⟫ ⦂ C          -- C = THE REDEX'S TYPE
```

and then wrapped it.  Deleting the wrapper leaves each preservation case
as that `inner` and nothing else.

**The rules now.**

```
  CancelR : Value V
    → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ  → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ  → Δ₁ᶜ ∋ X := Aᵢ
    → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ  → Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ
    → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
        -→ V ⟪ Θ₁ ++ Θ₂ , mkId A′ ⟫ ∣ none

  IdPush  : Value V
    → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ  → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
    → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ  → Δ⋉ᶜ ⊢ ` X′ ≈ ` X ⊣ Δ₁ᶜ
    → Δ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫
        -→ V ⟪ Θ₁ ++ Θ₂ , unseal X′ ⟫ ∣ none
```

**The premises that went with the layer.**  `Δ ⊢ᶜ Θ₂ ⇒ Δᶜ` and
`Δᶜ ∋ Y := A` existed only to mint the discarded `mkId A`, so both rules
drop them; `Δᶜ` and `A` leave both telescopes.  `Y` now occurs only in
the redex.  RULED BY JEREMY: "we can assume the redex is well-typed, so
`Y` is effectively constrained" — typing forces `X` and `Y` to name ONE
representation variable (`idpush-name` / `cancel-name`,
`proof/IdLayer.agda`), which is the only thing the metatheory ever used
those premises for.  `CancelR` keeps its OTHER lookup, `Δ₁ᶜ ∋ X := Aᵢ`:
that one determines the identity it still mints.

**What the change touched.**

* `proof/MoveScope.agda` — both cases are the former `inner`, renamed
  `contractum`; `mwR`, `outerᵢ`, `rewind-interior` and
  `rewind-conversion` are gone, and the outer lookup is inverted out of
  the redex's own `conv-unseal` where the proofs still need it.
* `proof/Determinism.agda` — `IdPush` is determined by its weakening
  `X′` alone (`sameTy-src-unique`); `CancelR` by `Δ₁ᶜ ∋ X := Aᵢ` and the
  weakening.  The outer `∋:=-det` step is gone from both.
* `Eval.agda` — `bdyRedex` no longer calls `cancelPremises?` in either
  branch.
* `proof/ShiftAudit.agda` §6 — `Move-outer-frame` and
  `Move-outer-conversion` DELETED: they audited a layer no rule builds.
* `Residual.agda`, `proof/ColorPreservation.agda`,
  `proof/Canonicity.agda`, `proof/Progress.agda`, `Show.agda` — one
  layer fewer, mechanically.
* NO RULE BUILDS A `rewind` any more.  `rewind`, `rewind-interior` and
  `rewind-conversion` stay in `Boundary.agda` §3/§3a as constructions.

**What the corpus says.**  Every run that reaches a `CancelR` or an
`IdPush` got shorter, and no endpoint moved:

| run | before | after | | run | before | after |
|---|---|---|---|---|---|---|
| §1a `P`   | 6  | 5  | | §5b `V`   | 40 | 24 |
| §1c `J`   | 11 | 10 | | §6a `I`   | 17 | 9  |
| §1d `F`   | 6  | 5  | | §6b `N`   | 23 | 16 |
| §1e `U`   | 7  | 6  | | §7a `A`   | 11 | 8  |
| §2  `Q`   | 14 | 11 | | §7b `B`   | 21 | 15 |
| §2a `D`   | 22 | 17 | | §7c `C`   | 41 | 22 |
| §2b `L`   | 14 | 11 | | §8  `S`   | 19 | 14 |
| §2c `R`   | 24 | 16 | | §9a `T`   | 3  | 2  |
| §3  `G`   | 17 | 13 | | §9b `Tid` | 5  | 3  |
| §4  `H`   | 11 | 9  | | §9c `Tid₂`| 7  | 4  |
| §5a `E`   | 28 | 19 | | | | |

(`§1b K` at 9 and `§10 Bg` at 7 are unchanged — neither reaches one of
the two rules.)  `strong-rep-store/notes/CancelRReachabilityWitness.agda` runs in 14 with
controls at 8 and 13, and `strong-rep-store/notes/RawRunProbe.agda` agrees at 14.

The shape of the change is clearest in `Examples.agda` §9c, a stack of
two transparent layers over a cancel pair:

```
  (((7 ⟪ seal X ⟫) ⟪ id X ⟫) ⟪ id X ⟫) ⟪ unseal X ⟫
    --[IdPush]-->  ((7 ⟪ seal X ⟫) ⟪ id X ⟫) ⟪ unseal X ⟫
    --[IdPush]-->  (7 ⟪ seal X ⟫) ⟪ unseal X ⟫
    --[CancelR]--> 7 ⟪ id ℕ ⟫
    --[Drop$]-->   7
```

`IdPush` now consumes one identity layer per step instead of relocating
it, so the tower strictly shrinks.

**Gate.**  `make check` green (whole development plus `notes/All.agda`),
`postulate-check: OK`.

## RENAME — `Change`'s constructors are `unbind` / `bind` (2026-09-23, Jeremy's TODO)

`lock X α` DELETES the ordinary name `X` for the representation variable
`α`, and `unlock X α` INSERTS it.  The old names said "hidden" where the
judgements say "not named", so they are gone:

```
  lock    ⟶  unbind        the name X for α is removed
  unlock  ⟶  bind          the name X for α is added
```

The rename is uniform across the Agda and the notes, and carries the
derived vocabulary with it.  The identifiers that moved:

```
  lock / unlock                 unbind / bind
  step-lock / step-unlock       step-unbind / step-bind
  conv-lock / conv-unlock       conv-unbind / conv-bind
  conv-unlock-live              conv-bind-live       ("the re-bind clause")
  conv-unlocks                  conv-binds
  InLocks / InUnlocks           InUnbinds / InBinds
  il-here/-there, iu-here/-there  iu-here/-there, ib-here/-there
  inLocks?                      inUnbinds?
  int-locked / int-unlocked     int-unbound / int-bound
  in-unlocks-++ˡ/-++ʳ/-++-inv   in-binds-++ˡ/-++ʳ/-++-inv
  locks→dual / dual→locks       unbinds→dual / dual→unbinds
  locks-only-ok / unlocks-only-ok   unbinds-only-ok / binds-only-ok
  conv-snoc-lock                conv-snoc-unbind
  snoc-lock0-interior-ren       snoc-unbind0-interior-ren
  snoc-lock0-conversion-ren     snoc-unbind0-conversion-ren
  addLock0-⊢ / addLock0-reading addUnbind0-⊢ / addUnbind0-reading
  AddLock0Typing                AddUnbind0Typing
  proof/AddLock0.agda           proof/AddUnbind0.agda
```

In prose, "locked" is now "unbound", "unlocked" is "bound", and "Θ's
locks" are "Θ's unbinds".  The displayed notation of `notes/notes.md` and
`Show.agda` is unchanged: `↓X` is still an unbind and `↥X` a bind.

WHAT KEPT ITS OLD NAME, and why.  Two note modules are date-stamped
records of walls and are cited by name throughout this log, so their
FILENAMES stand: `strong-rep-store/notes/AddLock0Wall.agda` and `strong-rep-store/notes/ReUnlockWall.agda`.
Each now opens with a comment saying so.  The retired masked-entry
design's "lock bit" (`unmasked b` / `masked b`, `SystemF/agda/strong/`)
also keeps its name: it is a bit on a slot, not a `Change`.  And
`Design.md`'s retired identifiers — `applyUnlocks`, `unlockedScope`,
`¬frame-locksOnly`, the `dual-relock` branch — name machinery that no
longer exists, so renaming them would point at nothing.

ONE COLLISION TO KNOW ABOUT.  "bind" now means two things in the older
prose: the `Change` constructor, and the retired BIND BLOCK a boundary
used to carry (`binds Θ`, `numBinds`, `pushBinds`, and `bindR` in
`Ctx.agda`, which is the representation binding and is unaffected).  The
bind block has not existed since experiment 2 (2026-09-22), so every
live use of "bind" is the change; where the historical notes mean the
block they say "bind block".

**Gate.**  `make check` green, cold; `postulate-check: OK`.

## 2026-09-24 — strong-rep-nu FORKED from strong-rep-store: `ν A · L ⟨ c ⟩` replaces type application (RULED by Jeremy)

strong-rep-nu is a verbatim copy of strong-rep-store at `main` 694fe461
(after PR #208).  The experiment borrows GTPLC's `ν A · L •⟨ c ⟩`
(`GTPLC/Terms.agda`, `⊢ν`), with a Conversion in place of the coercion:
evaluate `L` to a `∀`-value, allocate a fresh cell for `A`'s
representation, instantiate `L` there, and convert with `c`.  The
proposal, its two examples and the alternatives are
`notes/NuSketch.md`.  Jeremy answered its four questions:

1. **Elaboration.**  The compiler writes `c = reveal 0 C` for an
   operator `L : ∀ C`, but `⊢ν` accepts ANY `c` whose types line up, as
   GTPLC's `⊢ν` does.  `c` is read at the conversion context of
   `TyBetaBoundary` over `allocate R Δ`, which is where the `Nu` rules
   put it, and its target is compared to the result type by `≈`, as in
   `env`.  The generality is used: `Nu-⟪⟫` pushes a `ν` whose conversion
   is a run-time reveal of the inner body.
2. **Rule 2: N1, stack, don't fuse.**  `Nu-⟪Λ⟫` moves the crossed
   conversion `s` verbatim into a middle layer over `liftᴮ Θ` and puts
   `ν`'s own `c` outside it on `inst []`:
   ```
     ν A · ((Λ N) ⟪ Θ , ∀ s ⟫) ⟨ c ⟩  -→  (N ⟪ liftᴮ Θ , s ⟫) ⟪ inst [] , c ⟫ ∣ new R
   ```
   N2 (a run-time composition `s ⨟ c`) was rejected: it would put back
   the run-time work the compile-time reveal removed.
3. **Nested case: (a), re-allocate an alias cell per layer.**  `Nu-⟪⟫`
   pushes `ν (` 0) · (↑W ⟪ ↑Θ′ ++ [unbind 0 0] , ∀ s″ ⟫) ⟨ reveal 0 (⇑Bᵢ′) ⟩`
   inward under the same two stacked layers.  When it fires it
   allocates a cell whose payload is the outer `ν`'s cell.  (b), one
   allocation per `ν` with a non-allocating instantiation form, was
   rejected: it needs a non-injective representation renaming that
   `RepWk`/`⊢renᴿ` do not cover.
4. **`·[_,_]` leaves the run-time language.**  A SEPARATE source
   language, plain System F with the standard `L [ A ]`
   (`Source.agda`), is compiled into it (`Compile.agda`).

As implemented, the rule renaming is:

```
  TyBeta       ⟶  Nu-Λ       contractum N ⟪ inst [] , c ⟫ (c is ν's own)
  TyPeelR-Λ    ⟶  Nu-⟪Λ⟫     stacked, as in (2)
  TyPeelR-⟪⟫   ⟶  Nu-⟪⟫      pushes a ν, as in (3)
  ξ-·[]        ⟶  ξ-ν
```

`Boundary.agda` gains `liftᴮ Θ = map shiftChange Θ`, and
`inst Θ = liftᴮ Θ ++ (bind 0 0 ∷ [])`, so read inside out the stacked
scopes are the old fused one (`Nu-⟪Λ⟫-stacks-to-inst`,
`proof/ShiftAudit.agda` §3).  No rule mints `instReveal` any more, so
`canon-step`/`canon-steps` (`proof/Canonicity.agda`) lost their
`CanonTyPeelR` hypothesis; `¬CanonTyPeelR` is kept as the record of the
wall.  The one reveal still minted at run time is `Nu-⟪⟫`'s; the old
`TyPeelR-⟪⟫` pushed in `·[⇑Bᵢ′, 0]`, which the next `TyBeta` turned into
the same `reveal 0 (⇑Bᵢ′)`.

**`compile-⊢` carries `CtxWf Δ Γ`** (Jeremy approved the extra
premise, 2026-09-24).  The statement is

```
  compile-⊢ : WfCtx Δ → CtxWf Δ Γ → length (names Δ) ≡ n
            → (d : n ∣ Γ ⊢ˢ M ⦂ A) → Δ ∣ Γ ⊢ compile d ⦂ A
```

and it is FALSE without `CtxWf Δ Γ` (every type in the term context is
well formed at `Δ`) for open terms.  The source variable rule does not
check the variable's type, so at `n = 0`, `Γ = [∀ (` 5)]` the term
`x [ℕ]` has a source derivation, but its compiled `ν` needs
`Δ ⊢ᵗ B` of a result type that names a variable `Δ` does not have.
`compile-closed` discharges it by `CtxWf-[]`, and `compile-safe` is
`type-safety` after `compile-closed`.  `SourceExamples.agda` checks
`compile … ≡ E.X₀` by `refl` for the twenty plain-System-F programs of
`Examples.agda`.

**What it cost.**  The stacked layer is one more boundary per crossing:
K 9→11, J 10→12, G 13→16, H 9→11, E 19→30, V 24→49, I 9→12, N 16→20,
C 22→33, S 14→16 steps.  Three wall records whose checked content is
exact states of runs through the retired rules left `notes/All.agda`:
`CancelRReachabilityWitness`, `RawRunProbe` and `AddLock0Wall`.  The
files were kept unported at first and then DELETED the same day (Jeremy);
strong-rep-store holds their checked versions,
and the CancelR witness program still runs green as `Examples.agda` §8
`S`.

**The premise-free preservation counterexample moved.**  The 2026-09-18
counterexample was the `TyBeta` redex `(Λ ($ 0)) ·[ ℕ , ℕ ]` at a
duplicate name map.  Its `ν` counterpart is not typeable there at all,
because `⊢ν` carries `BoundaryWf (allocate R Δ) TyBetaBoundary …`.  The
premise is still needed: `Beta` on `(λx:ℕ. ΛZ. λy:ℕ. x) · 0` mints the
dual boundary `0 ⟪ ↓Z , id ℕ ⟫` under the `Λ`, whose `BoundaryWf`
demands the well-formedness the duplicate map lacks.  Checked with the
derivation-producing checker (`infer` succeeds on the redex and fails on
the contractum), not machine-checked as a refutation.

**Gate.**  `make check` green at 4bf42f26.

**Deleted, 2026-09-24 (Jeremy).**  The unused `⊢instReveal`/
`⊢instConceal` (old `proof/Preserve.agda` §2b, with its `underΛN`/
`Avoid`/`abstract-*` helpers), then `instReveal`/`instConceal`/
`instReveal-mkId` (`Conversion.agda` §4) and the refuted record
`CanonTyPeelR`/`¬CanonTyPeelR` (`proof/Canonicity.agda` §8).
`¬canonC-two-binders` (§10) now carries the two-binder refutation
directly.

## 2026-09-24 — merging boundaries: one boundary per value, and `Merge` (RULED by Jeremy; IMPLEMENTED 0e662d1b, 5d98bbe2)

Proposal, census and the ruled statements: `notes/MergeSketch.md`
(status IMPLEMENTED).  The census (`notes/StackCensus.agda`) found every
place a value boundary sits directly under another boundary, over every
state of the 19 compiled runs; `CancelR` and `IdPush` handled only the
pairs whose outer conversion is an unseal, and every other pair
stacked.

**Decisions (Jeremy, 2026-09-24).**

* A SEPARATE `Merge` step (M1), not merging on construction (M2), so
  that `Peel`, `Beta` and `Nu-⟪Λ⟫` carry no merge premises.
* Conversions are normal forms in THREE SYNTACTIC SORTS with
  `NoCancel`, NOT endpoint-indexed.  Endpoint indexing was withdrawn
  once representation variables were kept: `seal X`'s source is `X`'s
  representation spelled in `Δ`, which no syntax index can state while
  seals and unseals carry only the ordinary NAME (rep-free, read through
  the lookup square).  Consequently the bare `seal X` / `unseal X`
  stay, standing for an identity middle, and a chain extends only a
  non-identity.
* Composition TAKES THE CONTEXT (option (c)), written `Δ ⊢ c₁ ⨟ c₂`
  with the context first: `seal X` meeting `unseal X` writes
  `mkId (repOf Δ X)`, and under `∀` the bodies compose at `underΛ Δ`.
* `Nu-⟪Λ⟫` keeps its STACKED contractum; `Merge` fuses it on the next
  step.
* `proof/Canonicity.agda` is RETIRED: its single-binder invariant is
  exactly what merging gives up (a chain `seal Y ⨾seal X` names two
  binders); the pivot-set generalisation was declined.
* The work stays on branch `strong-rep-nu` (PR #209).

**The definitions.**

```
  Mid   g ::= id A | s ↦ c | `∀ s
  Tail  t ::= mid g | seal X | t ⨾seal X        seal chain, associates LEFT
  Conv  c ::= tail t | unseal X | unseal X ⨾ c  unseal chain, associates RIGHT

  _⊢ᵐ_∶_⇝_   conv-id  conv-idv  conv-fun  conv-all
  _⊢ᵀ_∶_⇝_   conv-mid  conv-seal  conv-seal-seq  (¬ IsIdᵀ t)
  _⊢_∶_⇝_    conv-tail  conv-unseal  conv-unseal-seq  (¬ IsIdᶜ c, NoCancel X c)

  _⊢_⨟_ : Ctxᵗ → Conv → Conv → Conv                  Conversion.agda §4b
  ⊢⨟    : Unique (names Δ) → Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C
        → Δ ⊢ (Δ ⊢ c₁ ⨟ c₂) ∶ A ⇝ C                   proof/Compose.agda

  Simple   S-$  S-true  S-false  S-ƛ  S-Λ
  Value    V-simple : Simple U → Value U
           V-⟪⟫     : Simple U → InertTail t → Value (U ⟪ Θ , tail t ⟫)

  Merge : Simple U → InertTail t₁
    → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ → Δ ⊢ᶜ Θ₂ ⇒ Δ₂ᶜ
    → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
    → SameConv Δ⋉ᶜ (tail t₁′) Δ₁ᶜ (tail t₁)
    → SameConv Δ⋉ᶜ c₂′ Δ₂ᶜ c₂
    → Δ ⊢ (U ⟪ Θ₁ , tail t₁ ⟫) ⟪ Θ₂ , c₂ ⟫
        -→ U ⟪ Θ₁ ++ Θ₂ , Δ⋉ᶜ ⊢ tail t₁′ ⨟ c₂′ ⟫ ∣ none
```

The lookup functions moved to a new `Lookup.agda`, below
`Conversion.agda`, because composition reads `∋:=?`; `TypeCheck.agda`
re-exports them.

**Rule changes.**  The rule set is twelve: `Nu-Λ`, `Beta`, `Peel`,
`Nu-⟪Λ⟫`, `Merge`, `Drop$`, `Drop-true`, `Drop-false`, `ξ-·-l`,
`ξ-·-r`, `ξ-ν`, `ξ-⟪⟫`.

* `Merge` is NEW and SUBSUMES `CancelR` (`seal X` then `unseal X`) and
  `IdPush` (`id X` then `unseal X`), both DELETED.  Its carried
  spellings `t₁′`/`c₂′` replace `A′`/`X′`, and the inner one is read
  from Θ₁'s own conversion context, the lesson of the 2026-09-19
  `CancelR` repair.
* `Nu-⟪⟫` is DELETED as unreachable: the interior of a `∀`-value's
  single boundary is a `Λ` (`canon-∀`), so only `Nu-⟪Λ⟫` fires.  With
  it went the one reveal minted at run time; every reveal is now
  written by the compiler.  Its carried `Bᵢ′` and `s″` and the tower
  descent (`Nu-⟪⟫-height`) went too.
* `Peel` requires `Simple V` (the crossed value's one boundary is the
  one it peels) and matches `⌞ s ↦ t ⌟`; `Nu-⟪Λ⟫` matches `⌞ `∀ s ⌟`;
  the drops match `⌞ id A ⌟`.

**Proofs.**  `preserve-Merge : MergeCase` (`proof/MoveScope.agda`)
weakens both typed conversions onto `Δ⋉ᶜ` by `weaken-⊢` and composes
them by `⊢⨟`; the middle type agrees by `same-target-unique`.
`merge-redex` (`proof/Progress.agda`) builds the premises from
`merged-conversion-exists`.  `det` handles `Merge` by
`sameConv-src-unique`; `weaken-⊢` gained `Unique (names Γ)` for
`NoCancel`.  `Merge-height` (`proof/ShiftAudit.agda` §4): `Merge`
lowers the tower measure, which is at most one on a value.  The
top-level theorem statements are unchanged.

**Deleted files.**  `proof/Canonicity.agda` (retired, above),
`proof/AddUnbind0.agda` (used only by `Nu-⟪⟫`),
`notes/CancelRShiftWall.agda` (the record of the `CancelR` weakening
wall; dropped from `notes/All.agda`).  New files: `Lookup.agda`,
`proof/Compose.agda`, `notes/MergeSketch.md`, `notes/StackCensus.agda`
(gated by `notes/All.agda`).

**Counts.**  K 11→9, G 16→14, H 11→10, E 30→16, V 49→19, I 12→10,
N 20→15, B 15→13, C 33→19, S 16→15; the others are unchanged.
Against the pre-`ν` counts, E (19), V (24), N (16) and C (22) are now
shorter, K (9) is equal, and J, G, H, I and S remain longer.

**Inspiration**, recorded in `notes/MergeSketch.md`: GTLC's three
normal-form sorts, GTPLC's chain association, GTSF's strict/cross
categories, and GTSFImp's `Conv↑`/`Conv↓`, the closest relative, which
does not merge.

**Gate.**  `make check` green at 5d98bbe2.
