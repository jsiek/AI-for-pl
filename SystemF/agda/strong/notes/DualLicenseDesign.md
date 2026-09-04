# The dual-conceal license (design (b3), probed) — 2026-09-04

Design description for Jeremy, per his request.  Everything asserted is
machine-checked in notes/DualLicenseProbe.agda (agda --safe clean); witness
names cited.  This design closes E★′, the last known counterexample to the
dual construction; it sits ON TOP of the already-probed (a″) pieces (raw
entries, comparisons up to unfolding, hybrid ⟦·⟧, cnc⋆), which it does NOT
subsume.

## 1. The example (E★′, fixed)

    E★′ = (ΛX. λf:(∀Z.(Z→ℕ)→(Z→ℕ)). ΛY. (f [Y]) (λy:Y. 5)) [ℕ]
            · (ΛZ. λg:(Z→ℕ). λz:Z. g z)      : ∀Y. Y→ℕ

At the ξ TyWrap(Z) step the boundary  ↑Z:=Y , ↓X:=ℕ  is minted at exterior
Y (Λ-bound) , X:=ℕ.  The knowledge "Z is Y" is inexpressible in the interior
(Y is blocked) and un-unfoldable (Y is Λ-bound).  TODAY Z's interior entry
falls back to ABSTRACT and the later Wrap is stuck (¬⊢T4′ / ¬⊢T4′⋆).

Under this design the entry instead records the rep, marked exterior-read:

    interior of ↑Z:=Y , ↓X:=ℕ   =   Z :=ˣ Y        "revealed; rep Y readable
                                                    one level OUT; asserts
                                                    nothing HERE"

and the Wrap's dual conceals Z with that very rep:

    dual  =  ↓Z:=Y , ↑Y:⋆ , ↑X:=ℕ        licensed by the new clause (bwf-↓x)
    contractum types end-to-end (⊢3s-T4′); both faces were already exactly
    right (face-int-E★′, face-ext-E★′) — only the license was missing.

E★ is fixed the same way with no cnc⋆ needed (⊢3s-T4); cnc⋆ remains for
duals of rep-less reveals (rvl⋆), where there is no rep to record.

## 2. Before/after — the rules that change, and their homes

New CONTEXT entry form (TyEntry, strong/Context.agda):

    entries   E ::= abstract | X:=A | X:=ˣA          (new: exterior-read)

  X:=ˣA is minted ONLY by the interior computation ⟦·⟧ and consumed ONLY by
  the new boundary clause below.  It is NOT a telescope entry: its rep A is
  a type over THIS context's exterior.  No typing rule converts through it;
  ordinary knowledge lookup (∋:=) does not see it — that is what dodges the
  ¬hk-int renaming trap (checked: no-know-Z).

The interior computation  Γ ⇈ Θ  (strong/Boundary.agda; used by (env) in the
typing relation  Δ ∣ Γ ⊢ M : A — the (env) rule itself is unchanged):

    before   reveal ↑Z:=A ⇒ entry Z:=⟦A⟧ when expressible;
             retried at the unfolding (hybrid);  ABSTRACT otherwise
    after    same, except the final fallback for a REP-CARRYING reveal is
             Z:=ˣA instead of abstract  (rvl⋆ still gives abstract)

Boundary well-formedness  Γ ∣ Ψ ⊢ Θ  (strong/Boundary.agda) — one new
clause; (bwf-↓), (bwf-↑), (bwf-⋆) unchanged:

    (bwf-↓x)   Γ ∋ X:=ˣA      A names only abstract variables of Ψ
               Ψ ⊢ A
               ────────────────────────────────────────────────
               Γ ∣ Ψ ⊢ ↓X:=A , Θ

  Read: a conceal is licensed by exterior-read knowledge when its rep is
  SYNTACTICALLY the recorded one (the homes align: the x-entry's rep and a
  conceal's rep both live over Ψ) AND the rep asserts nothing the interior
  could use ("claims nothing": every variable it names is abstract in Ψ).
  The second premise (absOnly) is LOAD-BEARING, not hygiene — see §3.

The dual construction (entᴳ/cncOfRevs in strong/BReduction.agda, feeding the
Wrap rule of  Δ ⊢ M -→ M′ — the Wrap rule TEXT is unchanged):

    before   conceal block consults the interior entry; rvl⋆ duals mint an
             unlicensable knowledge-claiming conceal (¬DualCnc-rvl⋆)
    after    entry-independent: rep-carrying reveal ↦ conceal with that rep
             (licensed by (bwf-↓) / (bwf-↓x) as available);
             rvl⋆ ↦ cnc⋆ (licensed by nothing, claims nothing)

## 3. Why the naive form was unsound, and the repair

Naive (b3) — license by the x-lookup alone — admits an adversary
(⊢3n-adv): inside E★′'s own sealed interior (so the x-entry Z:=ˣY is
genuinely plantable), a NON-dual boundary  ↑W:=ℕ , ↓Z:=W  types the term
7 : ℕ at the abstract Z — the conceal's rep W smuggles interior content in
through a slot whose knowledge was supposed to be unusable.  The repair —
"A names only abstract variables of Ψ" — forbids exactly that: the rep may
give the FACES their shape but may not carry interior information.  With it
the adversary is refuted (¬⊢3s-adv, mutation-tested), and the admitted
residue is abstract-to-abstract aliasing (⊢3s-alias), which cnc⋆ already
grants and which claims nothing.  bad, bad₂, far-bad all stay refuted
(¬⊢3s-bad, ¬Rev³-bad₂, ¬Rev³-far); the near-bad by a different route stays
admitted (⊢3s-near-bad).  Dual-of-dual round-trips exactly (bwf3-dd).

## 4. What (b3) does NOT cover (unchanged obligations from (a″))

  * Pn still needs the hybrid unfold retry — b3 does not subsume it
    (xlic-Pnⁿ vs ¬abs-Pnⁿ): an x-entry licenses only reps that claim
    nothing, and Pn's conceal needs the UNFOLDED knowledge.
  * Pc's chained COPY site lives in the dual's reveal block (entᴳ), not in
    any conceal clause — the (a″) unfolded copy and ≼≈ carry it.
  * An x-slot that a deeper boundary drops without concealing loses its
    knowledge to rvl⋆, as abstract slots always did.

## 5. The one open lemma for the install

The x-rep lives in the exterior, so under type-variable renaming it moves
by the exterior ρ, while renᴮ freezes a conceal's stored rep — so the
syntactic equality in (bwf-↓x) is not ⊢renameᵀ-stable as stated
(¬xlic-ren, ¬dual-ren-comm).  Two candidate repairs; RULING (Jeremy, 2026-09-04): (ii), for duality —
"It would be strange to use the congruence only for conceal and never for
reveal."  With (ii) the design is ≈-symmetric on both axes: syntactic rep
well-formedness (reveal in the exterior / conceal in the interior), and
knowledge coherence up to ≈Δ̄ (conceals CONSUMING knowledge via bwf-↓ and
bwf-↓x / the dual's reveal block REBUILDING knowledge via ≼≈, DualInt≈).
  (i) an XRen transport hypothesis on ⊢renameᵀ — REJECTED (grows the
      renaming interface; asymmetric);
  (ii) state (bwf-↓x)'s equality up to ≈Δ̄, renaming-stable the way
      Reversal≈ already is — CHOSEN.  Install-gauntlet addition: re-run the
      ⊢3n-adv adversary under the congruence (expected refuted — the
      load-bearing premise is "claims nothing", orthogonal to how the rep
      equality is compared — but it is a check, not an assumption).

## 6. Verdict table (from the probe)

    candidate                     E★′   E★   Pn   bad/bad₂   near/far  ren
    (b1) read-back identity        ✗    ✓*   ✓      ✓          ✓        ✓
    (b2) faces as premise          ✓†   ✓*   ✓      ✗ADMITS    ✗        ✓
    (b3) x-entry, naive            ✓    ✓    ✓      ✗ADMITS    —        ✗
    (b3) x-entry + claims-nothing  ✓    ✓    ✓      ✓          ✓        ✗(§5)
        * only via cnc⋆    † vacuously (the premise is definitional)

  (b1) additionally re-opens conceals of plain abstract variables
  (bwf1-garbage), undoing what the restored invariant bought.  (b4) — a
  co-boundary-parameterized judgment — is ruled out structurally: (env)'s
  premise has no co-boundary slot, and preservation must produce a plain
  derivation.
