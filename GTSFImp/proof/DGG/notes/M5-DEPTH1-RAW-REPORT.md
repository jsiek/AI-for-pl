# M5 depth-1 obstruction — raw report

Audience: Jeremy, for the design decision. Everything below is stated in
terms of the imprecision relation, the reduction rules, and concrete term
shapes. No package records, no transport-lemma names. Machine-checked
artifacts backing each claim are cited at the end.

## 1. The lemma we are proving

`InstCatchupRight²` (proof/DGG/ExtraCastRight2.agda:228), fully unfolded:

Given
    W ∣ γ ⊢² M ⊑ M′ ∶ p          -- term imprecision, version 2
    Value M,  Value M′
    p : A ⊑ᵂ⟨ W ⟩ `∀ B
    c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′      -- the inst consistency
    NonVar B,  0 ∈ᵗ B,  B′ ≢ ★
    q : A ⊑ᵂ⟨ W ⟩ B′
conclude there are store changes χs, a right-extended world W′, and a
target value N′ with
    M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs ] N′
    W′ ∣ γ′ ⊢² M ⊑ N′ ∶ q′        -- q transported to W′; γ likewise.

The source M never steps. Only the target reduces.

## 2. The input shape that breaks (depth 1)

Source and target values:

    M  = Λ (Λ V)        -- two type abstractions
    M′ = Λ V′            -- one

Input derivation (its only possible shape, by the relation's rules):

    Λ⊑²   : source's OUTER Λ is one-sided — the target has no partner.
            Premise lives in liftWorldLeft X⊑★ W: a fresh center is
            pushed at the FRONT of the center context for the outer
            source binder, marked X⊑★, target side untouched.
      Λ⊑Λ² : source's INNER Λ matches the target's Λ.
            Premise lives in liftWorldBoth X⊑X (liftWorldLeft X⊑★ W):
            one more fresh center at the front, SHARED by both binders,
            marked X⊑X.
        bodyRel : … ⊢² V ⊑ V′ ∶ body-p

Type side: A = `∀ (`∀ A₀), against `∀ B — the outer source ∀ relates
one-sidedly (the ∀⊑ rule), the inner matches B's ∀.

This shape is reachable from compiled gradual sources: the screen
(M5-DEPTH-SCREEN.md) checks a ⊑ᴳ-derivable pair whose argument relation
stacks Λ⊑ᴳ/Λ⊑ᴳ/Λ⊑Λᴳ with a generated inst cast on the compiled right
operand (screening-grade: source shape and inst site checked; the target
⊢² stack inferred from compile-preservation, not per-step).

## 3. What the target does (two steps, source frozen)

    Λ V′ ⟨ (inst c′) B′≢★ ⟩
      —→[ bind ★ ]                                        (β-inst)
    (⇑ᵗᵐ (Λ V′) ⦂∀ (bind ★ ▷ᵇ B) [ ＇0 ] ↑ 〖 0 , ★ ↑ B 〗)
      ⟨ ↑ᶜ (c′ [ ★/0 ]ᶜ) ⟩
      —→[ bind (＇0) ]  (inside the cast frame)            (β-Λ)
    ((⇑ᵗᵐ V′) ↑ 〖 0 , ⇑ᵗ(＇0) ↑ (bind ★ ▷ᵇ B) 〗 ↑ …)
      ⟨ residual ⟩

Two target-store allocations:
  slot α : the fresh runtime name, representation ★   (from β-inst)
  slot β : the type-application binding, type ＇α      (from β-Λ)

## 4. The relation we must now derive, and why we cannot

After the two steps (set aside the residual cast — it is handled by
recursion and is NOT the problem), we must derive, in the world W₂ = W
extended by target slots α then β:

    W₂ ∣ γ₂ ⊢² Λ (Λ V) ⊑ post ∶ p₂

where post is the reveal-wrapped applied body above. The source still has
BOTH its Λ's; the target has none. So the derivation must open with TWO
nested Λ⊑² (both source binders are now one-sided). Each Λ⊑² pushes its
lift center at the FRONT of the premise world's center context. Inside
both, the center context is, front to back:

    [ ℓ_in , ℓ_out , c_β , c_α , …old centers… ]
       0       1      2     3

    ℓ_in  = inner source binder's lift center (pushed last, so at 0)
    ℓ_out = outer source binder's lift center
    c_β, c_α = the two fresh target centers (allocated before the
               Λ⊑² wraps are applied, so behind the lifts)

Inside, we must relate V to the applied body of V′ wrapped in the
generated reveals 〖0, ⇑ᵗ(＇0) ↑ …〗 and 〖0, ★ ↑ B〗. The reveal rules of
⊢² demand world evidence connecting the revealed runtime name to the
source: the inner source binder — whose target partner was consumed by
β-Λ and replaced by the name α — must be ALIGNED with α's center.
Alignment lives in the world's two store embeddings

    ηᴸ : source store ↪ᵗ centers      ηᴿ : target store ↪ᵗ centers

both of which are ORDER-PRESERVING by the World representation.

Route A (move the pivot — how depth 0 closed). The reveal's rebase
evidence re-points the inner source binder's center onto c_α. The
required source embedding is then

    inner source binder  ↦  center 3   (c_α)
    outer source binder  ↦  center 2-or-stays at 1

i.e. the newer source binder must land BEHIND the older one. No
order-preserving embedding does this. Machine-checked:
`no-ope-0↦3-1↦2` (M5UnderLiftRevealScratch.agda). At depth 0 there is no
ℓ_out in between — the move crosses only target centers, which is legal —
and that case is fully proven.

Route B (do not move the pivot). Take the reveal evidence with the pivot
in place (`sameWorldRebaseAt`, alignment "source var is imprecise at ★").
The reveal rule ACCEPTS this evidence (checked:
`depth1-inner-sameWorld-rebaseᴿ`). But then the post TYPE obligation must
hold in the unmoved world. Concrete instance, with inner body type
＇0 ⇒ ★ (the identity-ish shape):

    (＇0 ⇒ ★)  ⊑ᵂ  replaceTy 0 (⇑ᵗ(＇0)) (applyBody (bind ★) (＇0 ⇒ ★))

whose domain reduces to the bare variable judgment  ＇1 ⊑ ＇3 : the
source's inner binder (as a variable, one lift under) against the target
alias variable. The imprecision relation has NO rule for two variables at
different, unaligned centers. Machine-checked empty:
`depth1-inner-sameWorld-q-empty` via `no-var1⊑var3`.

Summary picture (reduction vertical, precision horizontal; the source
column never moves):

    Λ (Λ V)   ⊑   Λ V′ ⟨ inst c′ ⟩          ∶ p        -- OK (input)
       |                 |  β-inst, bind ★ (slot α)
       |                 v
    Λ (Λ V)   ⊑   (⇑(Λ V′) ⦂∀ … [＇0] ↑ 〖0,★↑B〗)⟨…⟩    -- still OK
       |                 |  β-Λ, bind ＇0 (slot β)
       |                 v
    Λ (Λ V)   ⊑   ((⇑V′) ↑ 〖0,⇑ᵗ(＇0)↑…〗 ↑ …)⟨resid⟩   -- NOT DERIVABLE
                                                        (routes A and B
                                                         both refuted)

## 4b. Interleaving `Λ⊑²` and right-only reveal peels

Follow-up check: `M5-INTERLEAVE-CHECK.md` enumerates the six legal top-down
orders preserving `Lₒ < Lᵢ` and `Rₒ < Rᵢ`. All six still fail under the current
rules. The checked blockers are either immediate absence of a source pivot for
`RebaseAtᴿ ... (just α)`, an order-preserving-embedding impossibility, or the
same unequal-variable type leaf (`＇0 ⊑ ＇3`) at the concrete body
`＇0 ⇒ ★`.

The same scratch also checks the candidate fix's representation shape:
`[ c_β , c_α , ℓ_out , old… ]`, with `inner ↦ c_β`,
`outer ↦ ℓ_out`, `β ↦ c_β`, and `α ↦ c_α`, is a valid `World` shape and
satisfies `WFWorld` in the concrete no-old-center instance. This does not add a
relation rule; it only confirms that "Λ⊑² premise lift enters at an existing
target center" is representable.

## 5. Answer to the invariant question

It is genuinely a third thing, but of your two readings it is much closer
to "what we thought was an invariant is not really an invariant" — with
the caveat that the failed invariant was never written down; it was baked
into the World representation:

- Nothing about EXECUTION broke. Reduction preserves every stated world
  invariant; no preservation lemma was refuted. The invariants we
  explicitly maintain (order-preserving ηᴸ/ηᴿ, frozen target centers,
  source re-parks never crossing source binders) all still hold on every
  reachable world.

- What failed is an IMPLICIT invariant of the relation's representation:
  "a one-sided source binder never needs to be aligned past another
  source binder." The single total center order, with Λ⊑² forcing lift
  centers to the front in derivation-nesting order, encodes exactly that
  assumption. Right-instantiation under an outer one-sided binder
  falsifies it: the inner binder's alignment target (the fresh name's
  center) necessarily sits behind the outer binder's lift center, and
  order-preservation of ηᴸ forbids the alignment. So the state the
  simulation reaches is semantically fine — the programs run, and the
  gradual guarantee should hold for them — but it has NO representative
  in the current relation. The relation is INCOMPLETE for catch-up at
  depth ≥ 1, not unsound.

- Consequently this is NOT a "tighten the invariants" situation. Every
  tightening keeps the same representable states and would only shrink
  them. The fix has to RELAX or refactor the representation so the
  missing states become expressible — e.g. letting a lift's center enter
  at a non-front position (so the Λ⊑² premise can interleave the lift
  behind existing store centers), or divorcing one-sided lift centers
  from the shared total order altogether — OR restrict the STATEMENT so
  the missing states are never demanded (viable only if M7's driver
  never invokes inst catch-up in this configuration; the program-level
  screen says the program shapes exist, but the invocation-site question
  is open).

## 6. Machine-checked artifacts

- `M5UnderLiftRevealScratch.agda` (repo root): both refutations
  (`no-ope-0↦3-1↦2`, `depth1-inner-sameWorld-q-empty`) and the checked
  acceptance of the non-moving reveal evidence.
- `notes/M5-DEPTH-SCREEN.md` + `notes/M5DepthScreenScratch.agda`: the
  reachability screen (verdict REACHED, with its screening-grade caveat).
- `notes/m5-inst-inversion-*.red`: the full resister chain, each with
  its RESOLVED or blocking status; the depth-0 closure is live in
  `Catchup/InstInversionProof.agda` (`Λ⊑Λ²-post-body-transport`).
- The Λ⊑²/Λ⊑Λ² rules quoted in §2: CastTermImprecision2.agda:668-693.
- β-inst / β-Λ quoted in §3: Reduction.agda:311-326.
