# Nu-imprecision DGG progress

This ledger tracks the checked path from `QuotientedTermImprecision` to the
dynamic gradual guarantee. In the detailed plan, **completed** means that the
linked declaration has been accepted by Agda without holes, **partial** means
that a checked interface or some checked cases exist but required cases remain,
and **not yet started** means that the terminal theorem or support lemma has no
Agda declaration yet. Historical log entries use **checked** as a synonym for
**completed**.

## Current objective

Complete the arbitrary-type source catch-up and the target-step dispatcher,
then plug them into the now-completed backward-blame trace assembly and build
the analogous backward-value assembly. In parallel, the forward terminal
clause still requires a source-oriented one-step simulation and a target
catch-up theorem for the case where the source is already a value. Those three
terminal clauses feed the already checked reduction to `ClosedNuDGG` and then
to the public `GradualDGG`.

## Coverage ledger

| Obligation | Status | Evidence or next issue |
|---|---|---|
| Matched ordinary `ν` allocation | checked | `matched-ν↑-allocation` |
| Left-only ordinary `ν` allocation | checked | `left-ν↑-allocation` |
| Right-only ordinary `ν` allocation | checked locally | `right-ν↑-allocation`; uses explicit intermediate index |
| Matched `ν ★` allocation | checked | `matched-νcast-allocation` |
| Left-only `ν ★` allocation | checked | `left-νcast-allocation` |
| Right-only `ν ★` allocation | checked locally | `right-νcast-allocation`; uses explicit intermediate index |
| Post-allocation `β-Λ•` reduction | checked for matched and left-only `ν` | `matched-ν↑-β-Λ•` and `left-ν↑-β-Λ•` |
| Paired reveal `β-∀•` | checked through allocation | `matched-post-allocation-β-∀-conversionᵀ` |
| Paired conceal `β-∀•` | checked through allocation | Same theorem handles both paired conversion forms |
| One-sided reveal/conceal `β-∀•` | checked | Left/right reveal and conceal lemmas |
| Generic narrowing/widening `β-∀•` | checked one-step boundary | Both constructor orders and all four combinations return `WeakOneStepResult` |
| Source-only canonical-`∀` catchup | partial | Ten explicit holes remain in `NuImprecisionCatchupScratch`; the upstream quotient-value pattern and inference regression is repaired and strictly checked |
| `β-gen•` | partial | Matched reconstruction and one-sided administrative clause checked; source-allocation naturality remains |
| `β-inst` followed by `ν ★` allocation | checked locally | Matched, left-only, and right-only two-step lemmas |
| Polymorphic value-shape inversion | checked locally | `Λ`, `∀` cast, or `gen`; each forces one administrative step |
| Quotiented `∀`-index inversion | checked locally | Representatives remain `∀`; ordinary witness is paired `∀` or source-only `ν` |
| Atomic-target desired-index reindexing | completed | `atomic-target-value-reindexᵀ` reconstructs the term relation structurally at the requested proof-relevant index |
| World/store-name coherence contract | partial | `WorldCoherent` is frozen; empty, entry extension, all three canonical lifts, and matched/left/right single-name allocation are strict; crossed allocation and simulation-result propagation remain |
| Swapped two-allocation context/store | checked locally | Crossed name assumptions and independent-order store links |
| Swapped two-allocation relation boundary | checked locally | `allocation-crossedᵀ`; projections equal the two-`bind` traces |
| Reduction under `ν` and `ν ★` | checked | Matched, source-only, and target-only outer frame lemmas |
| `blame-ν` | checked outcome | Exceptional outcomes carry a source catchup to blame; source frames lift it with `ν-blame-tail` |
| Administrative simulation-up-to | partial | The result, transport, coherence, source-`keep` composition, and all six `ν`-frame outcome maps are checked; the unfinished integration is confined to the dispatcher scratch |
| One-step Nu-imprecision simulation | partial | The dispatcher skeleton covers blame and the matched/source-only/target-only `ν` and `ν ★` families; ten explicit helper holes remain, and the non-`ν` constructor/reduction patterns are not yet enumerated |
| Terminal target-trace alignment | checked | Determinism makes every administrative `targetTail` a prefix of an observed trace to a value or blame |
| Forward source-value terminal clause | partial | Its exact named statement is checked in `NuDGGTerminalForward`; the proof still needs a source-oriented dispatcher and target-side value catch-up |
| Backward target-value-or-source-blame clause | partial dependencies | Its `Def` contract, generic `Proof`, and canonical `Lemma` assembly are hole-free; arbitrary-value catch-up and the target dispatcher supplied by the lemma remain partial |
| Backward target-blame clause | partial | Its exact named statement is checked in `NuDGGTerminalBackwardBlame`; target-trace alignment and the higher-order trace induction are checked, while zero-step blame catch-up and the live target dispatcher remain partial |
| Residual target-trace measure | completed | `aligned-residual-shorter` proves that the aligned residual after a distinguished target step is strictly shorter |
| Multi-step store well-formedness | completed | `multi-store-preservation` packages the store invariant across a complete Nu trace |
| Named terminal components compose to `GradualDGG` | completed interface check | `dynamic-gradual-guarantee-skeleton` supplies the three named boundaries to the checked strict wrapper |
| Three terminal clauses imply `ClosedNuDGG` | checked | `closed-nu-terminal-simulation⇒closed-nu-dgg` is hole-free |
| Closed `GradualDGG` | checked reduction | `closed-nu-dgg⇒gradual-dgg` reduces it to `ClosedNuDGG`, which now follows from exactly three terminal simulation clauses |

## Top-down proof plan from `QuotientedTermImprecision`

### Checked outer spine

The public input relation is compiled to the closed runtime relation by
[`compiled-term-imprecision`](NuDGGSpine.agda#L77). The runtime theorem to be
proved is [`ClosedNuDGG`](NuDGGSpine.agda#L235). Its four observable clauses
are forward termination, forward divergence, backward termination-or-blame,
and backward divergence-or-blame.

The checked theorem
[`closed-nu-terminal-simulation⇒closed-nu-dgg`](NuDGGSpine.agda#L330) proves
that it is enough to supply only the following three terminal facts:

1. if the source reaches a value, the target reaches a related value;
2. if the target reaches a value, the source reaches a related value or blame;
3. if the target reaches blame, the source reaches blame.

It derives both divergence clauses by finite-prefix arguments. The checked
theorem [`closed-nu-dgg⇒gradual-dgg`](NuDGGSpine.agda#L400) then discharges the
public [`GradualDGG`](../DynamicGradualGuarantee.agda#L91).

Status of this outer spine:

| Step | Status | Checked declaration or remaining work |
|---|---|---|
| Compile public imprecision to closed Nu imprecision | completed | [`compiled-term-imprecision`](NuDGGSpine.agda#L77) |
| Reduce the four observations in `ClosedNuDGG` to three terminal facts | completed | [`closed-nu-terminal-simulation⇒closed-nu-dgg`](NuDGGSpine.agda#L330) |
| Reduce `GradualDGG` to `ClosedNuDGG` | completed | [`closed-nu-dgg⇒gradual-dgg`](NuDGGSpine.agda#L400) |
| Supply the three terminal facts | partial | All three exact statements and arbitrary-world recursive forms are named in the terminal modules; their general proof bodies remain open |

### Common hypotheses and final related-value package

All three terminal facts are quantified over closed terms and begin with

\[
  \operatorname{RuntimeOK}(N),\qquad
  \operatorname{RuntimeOK}(N'),\qquad
  []\mid 0\mid 0\mid []\mid []
    \vdash^{N} N\sqsubseteq N'
    \mathrel{\vcentcolon} A\sqsubseteq B\mathbin{\mathop{\vcentcolon}}p,
\]

where

\[
  p : []\mid 0\vdash A\sqsubseteq B\dashv 0.
\]

Whenever a value branch succeeds, it must return all of the transported world,
store, and type-index evidence explicitly. For source changes \(\chi_s\) and
target changes \(\chi_t\), this package is

\[
\begin{aligned}
  \exists\,\Phi,\rho,q.\quad
  &\rho : \operatorname{StoreImp}
      \bigl(\Phi,\operatorname{applyTyCtxs}(\chi_s,0),
                   \operatorname{applyTyCtxs}(\chi_t,0)\bigr),\\
  &q : \Phi\mid\operatorname{applyTyCtxs}(\chi_s,0)
      \vdash \operatorname{applyTys}(\chi_s,A)
        \sqsubseteq \operatorname{applyTys}(\chi_t,B)
      \dashv \operatorname{applyTyCtxs}(\chi_t,0),\\
  &\operatorname{leftStore}^{i}(\rho)
      = \operatorname{applyStores}(\chi_s,[]),\\
  &\operatorname{rightStore}^{i}(\rho)
      = \operatorname{applyStores}(\chi_t,[]),\\
  &\Phi\mid\operatorname{applyTyCtxs}(\chi_s,0)
       \mid\operatorname{applyTyCtxs}(\chi_t,0)\mid\rho\mid[]
       \vdash^{N} V\sqsubseteq V'
       \mathrel{\vcentcolon}
       \operatorname{applyTys}(\chi_s,A)
       \sqsubseteq\operatorname{applyTys}(\chi_t,B)
       \mathbin{\mathop{\vcentcolon}}q.
\end{aligned}
\]

This is deliberately written out rather than hidden behind a new alias: the
final store projections and transported type index are invariants that every
trace-level proof must preserve.

The CamelCase names below remain expository labels.  Their exact Agda
counterparts are [`forward-source-valueᵀ`](NuDGGTerminalForward.agda#L67),
[`backward-target-value-or-source-blameᵀ`](NuDGGTerminalBackwardValueLemma.agda),
and [`backward-target-blameᵀ`](NuDGGTerminalBackwardBlame.agda#L44).

## Terminal fact 1: `ForwardSourceValue`

### Statement

This is the first premise of
[`closed-nu-terminal-simulation⇒closed-nu-dgg`](NuDGGSpine.agda#L330), now
named [`forward-source-valueᵀ`](NuDGGTerminalForward.agda#L67). Under the
common hypotheses, it states

\[
\begin{aligned}
  &N\xRightarrow{\chi_s}V\ \land\ \operatorname{Value}(V)\\
  &\quad\Longrightarrow
  \exists\,V',\chi_t,\Phi,\rho,q.\quad
    N'\xRightarrow{\chi_t}V'\ \land\ \operatorname{Value}(V')
    \ \land\ \text{the full related-value package above}.
\end{aligned}
\]

### Proof plan and status

| Step | Status | Proof obligation and available evidence |
|---|---|---|
| F1. State a source-oriented one-step simulation | not yet started | If related terms satisfy \(M\xrightarrow{\chi}L\), produce a target multi-step \(M'\xRightarrow{\chi_t}L'\) and a transported relation \(L\sqsubseteq L'\), with exact world/store/type actions. This is the polarity-reversed analogue of the current target-step dispatcher, but no declaration exists yet. |
| F2. Prove the source-oriented one-step cases | not yet started | Split on the source reduction and term-imprecision derivation. Reuse the checked matched, left-only, and right-only allocation/cast/frame lemmas where their polarity fits. The definition-sensitive `ν`, `ν ★`, `Λ`, `gen`, `inst`, and `•` cases should be proved before the ordinary congruence cases. |
| F3. Prove target catch-up from a related source value | not yet started | From \(\operatorname{Value}(V)\) and \(V\sqsubseteq M'\), show that \(M'\) reduces to a value \(V'\) related to \(V\). This needs structural recursion over the relation and target administrative reductions, including target-only allocation and quotient-cast cases. |
| F4. Rule out a source-blame alternative when the source is a value | completed | [`source-value-indexed-outcome-relatedᵀ`](NuImprecisionSimulationCore.agda#L1231) proves the required local outcome fact: an indexed weak outcome from a source value must be related, with zero source changes and the same source value. It constrains one target step; it does **not** by itself prove target termination. |
| F5. Lift source one-step simulation over a source trace | partial | [`forward-source-value-generalᵀ`](NuDGGTerminalForward.agda#L36) freezes the required arbitrary-world conclusion and its closed specialization is checked. The trace induction body remains a hole. |
| F6. Normalize composed changes and final store projections | partial | The weak result transport, type coherence, frame maps, and store-change composition infrastructure are checked. The forward trace-level composition theorem that packages the exact equalities required by the terminal statement is unwritten. |
| F7. Package the terminal theorem | partial | The exact full package is frozen in [`forward-source-value-generalᵀ`](NuDGGTerminalForward.agda#L36), and the closed theorem is a checked specialization. Constructing its witnesses in the general proof remains. |

The essential missing fact is not another use of the target-oriented dispatcher.
That dispatcher allows target administrative work while the source takes zero
steps. It therefore cannot, by itself, prove that a target eventually becomes a
value merely because the source has become one. F1 advances along the known
source trace; F3 closes the remaining target administrative tail.

## Terminal fact 2: `BackwardTargetValueOrSourceBlame`

### Statement

This is the second premise of
[`closed-nu-terminal-simulation⇒closed-nu-dgg`](NuDGGSpine.agda#L330), now
named
[`backward-target-value-or-source-blameᵀ`](NuDGGTerminalBackwardValueLemma.agda).
Under the common hypotheses, it states

\[
\begin{aligned}
  &N'\xRightarrow{\chi_t}V'\ \land\ \operatorname{Value}(V')\\
  &\quad\Longrightarrow\\
  &\qquad\left(
    \exists\,V,\chi_s,\Phi,\rho,q.\quad
      N\xRightarrow{\chi_s}V\ \land\ \operatorname{Value}(V)
      \ \land\ \text{the full related-value package above}
    \right)\\
  &\qquad\quad\lor\quad
    \left(\exists\,\chi_s.\ N\xRightarrow{\chi_s}\operatorname{blame}\right).
\end{aligned}
\]

### Proof plan and status

| Step | Status | Proof obligation and available evidence |
|---|---|---|
| B1. Catch up a source related to an already terminal target value | partial | [`left-catchup-indexed-prefixᵀ`](NuImprecisionCatchupScratch.agda#L1083) has the required arbitrary-type interface: given `RuntimeOK N`, `Value V′`, `No• V′`, and \(N\sqsubseteq V'\), it returns an indexed source catch-up. Ten explicit holes remain in this proof. |
| B2. Finish quotient-cast value classification | completed | The first GPT 5.5 ginger pilot supplied all four missing down/gen-down clauses for an untag-then-seal source sequence, then made the type and precision implicits explicit through the quotient helper chain. The exact wrapper command and a local strict focused check pass for [`NuImprecisionQuotientValue.agda`](NuImprecisionQuotientValue.agda). |
| B3. Discharge the two quotient-`inst` residuals in B1 | partial | The residual alternative from B2 must be threaded through the outer down/up and gen-down/up catch-up functions. These are the holes at [`left-catchup-indexed-prefix-down-upᵀ`](NuImprecisionCatchupScratch.agda#L961) and [`left-catchup-indexed-prefix-gen-down-upᵀ`](NuImprecisionCatchupScratch.agda#L1021). |
| B4. Discharge the remaining source allocation/cast leaves in B1 | partial | Eight holes remain in [`left-catchup-indexed-prefixᵀ`](NuImprecisionCatchupScratch.agda#L1083): the `α⊑ᵀ` residual, source-only `ν`, source-only `ν ★`, narrowing cast, widening cast, paired conversion, reveal, and conceal leaves. The strict pre-allocation terminal frames for the two source allocation cases are now isolated in [`NuImprecisionCatchupSourceAllocationTerminal.agda`](NuImprecisionCatchupSourceAllocationTerminal.agda), and the four arbitrary-type source cast terminal frames are complete; recursive assembly around those leaves remains. |
| B5. Complete the target-oriented one-step dispatcher | partial | [`weak-one-step-indexed-simulationᵀ`](NuImprecisionCatchupScratch.agda#L1381) now connects explicit impossible/value cases, primitive frames, target cast/conversion frames, and all five target root handlers in addition to the allocation and source cast/conversion families. Atomic target identity and all three target-cast β-id roots are complete. One target reveal/seal root and eight target-cast roots remain explicit holes; the scratch module still permits incomplete matches. |
| B6. Forget the indexed wrapper when aligning an outcome | completed | [`forget-weak-indexed-outcome`](NuImprecisionSimulationCore.agda#L1264) converts the indexed outcome to the unindexed outcome consumed by the trace-alignment layer. |
| B7. Align administrative target tails with the observed value trace | completed | [`weak-outcome-target-value-alignedᵀ`](NuDGGTraceAlignment.agda#L53), using [`target-tail-prefix-value`](NuReductionDeterminism.agda#L199), returns either an immediate source-blame trace or a residual target trace from the related result, together with \(\psi=\operatorname{targetTailChanges}(R)\mathbin{++}\theta\). |
| B8. Maintain runtime, typing, and store well-formedness | completed | One-step [`store-preservation`](NuPreservation.agda#L802), [`multi-preservation`](NuPreservation.agda#L882), [`multi-runtime-preservation`](NuPreservation.agda#L897), and [`multi-store-preservation`](NuDGGPreservation.agda#L27) are completed. The four result-level projections are checked in [`NuDGGWeakResultPreservation.agda`](NuDGGWeakResultPreservation.agda). |
| B9. Prove the target-trace terminal induction | completed proof | [`backward-target-value-or-source-blame-proofᵀ`](NuDGGTerminalBackwardValueProof.agda) is a hole-free fuel induction over the observed target trace. It consumes only [`WeakOneStepIndexedSimulationᵀ`](NuImprecisionOneStepDef.agda) and [`LeftValueCatchupᵀ`](NuImprecisionValueCatchupDef.agda), aligns administrative target tails, and recurses only on the strictly shorter residual trace. |
| B9a. Check the strengthened world-coherent induction | completed proof | [`world-coherent-backward-target-value-or-source-blame-proofᵀ`](NuDGGTerminalBackwardValueWorldCoherentProof.agda) repeats the fuel induction against the strengthened one-step and catch-up contracts. It threads successor `WorldCoherent` evidence only through continuing branches and imports no live implementation. |
| B10. Compose source traces and transported worlds | completed | [`prepend-weak-related-valueᵀ`](NuDGGTerminalBackwardValueProof.agda) composes the source trace and source changes while transporting the value relation, worlds, stores, and endpoint equations. The proof packages the final related-value witnesses or propagates source blame. |
| B11. Package the terminal theorem | completed assembly; dependencies partial | [`BackwardTargetValueOrSourceBlameᵀ`](NuDGGTerminalBackwardValueDef.agda) freezes the exact alternatives. [`backward-target-value-or-source-blame-generalᵀ`](NuDGGTerminalBackwardValueLemma.agda) is the hole-free canonical application of the generic proof to the live dispatcher and catch-up declarations. The lemma stays outside the strict spine until those supplied implementations are hole-free. |

The induction should be on target-trace length, not directly on the syntactic
multi-step proof. A weak outcome can consume the distinguished target step and
then take an administrative `targetTail`. B7 proves that this tail is a prefix
of the observed trace and exposes the strictly smaller residual trace on which
the induction hypothesis applies.

## Terminal fact 3: `BackwardTargetBlame`

### Statement

This is the third premise of
[`closed-nu-terminal-simulation⇒closed-nu-dgg`](NuDGGSpine.agda#L330), now
named [`backward-target-blameᵀ`](NuDGGTerminalBackwardBlame.agda#L44). Under
the common hypotheses, it states

\[
  N'\xRightarrow{\chi_t}\operatorname{blame}
  \quad\Longrightarrow\quad
  \exists\,\chi_s.\ N\xRightarrow{\chi_s}\operatorname{blame}.
\]

### Proof plan and status

| Step | Status | Proof obligation and available evidence |
|---|---|---|
| C1. Prove zero-step catch-up against target blame | completed | [`left-catchup-target-blame-generalᵀ`](NuImprecisionTargetBlameCatchup.agda#L92) is a hole-free structural recursion over quotiented term precision. It handles direct blame, rules out impossible value/bullet cases, recurses under source `ν`/`ν ★`, and lifts all four source cast/conversion frames; [`left-catchup-target-blameᵀ`](NuImprecisionTargetBlameCatchup.agda#L162) is its frozen specialization. |
| C2. Complete the target-oriented one-step dispatcher | partial | Reuse B5. Its exceptional outcome already carries the required source trace to blame. |
| C3. Align administrative target tails with the observed blame trace | completed | [`weak-outcome-target-blame-alignedᵀ`](NuDGGTraceAlignment.agda#L75), using [`target-tail-prefix-blame`](NuReductionDeterminism.agda#L220), returns either source blame immediately or a residual target trace ending in blame with the exact change-list equation. |
| C4. Prove the target-blame trace induction | completed assembly and live fit check | [`backward-target-blame-general-from-componentsᵀ`](NuDGGTerminalBackwardBlameAssembly.agda#L103) proves the higher-order trace theorem from the dispatcher and blame catch-up. It uses fuel, target-tail alignment, [`aligned-residual-shorter`](NuDGGTraceMeasure.agda#L26), the four checked weak-result preservation facts, and source-trace composition. [`backward-target-blame-general-integratedᵀ`](NuDGGTerminalBackwardBlameIntegration.agda#L32) checks that the live partial implementations have exactly those argument types. That consumer check exposed and repaired an accidental use of the superseded term-imprecision judgment in C1. |
| C5. Compose accumulated source traces | completed | The assembly prepends each `sourceCatchup` with `↠-trans` and concatenates its `sourceChanges` with the recursive blame trace. |
| C6. Package the terminal theorem | partial | The exact existential trace is frozen in [`backward-target-blame-generalᵀ`](NuDGGTerminalBackwardBlame.agda#L28), and the closed theorem is a checked specialization. The assembly, C1, and the live interface fit are complete; only the exhaustive dispatcher C2 remains before this theorem can be defined by the checked assembly application. |

C1 may be implemented as its own structural theorem or as the blame branch of a
single generalized left catch-up theorem whose target is terminal (value or
blame). The latter is attractive only if it shortens the proof without hiding
the explicit source trace required by the terminal statement.

## Recommended implementation order

The shortest current path to visible terminal progress is:

1. **Completed:** repair and strictly check the quotient-value patterns and
   inference in
   [`NuImprecisionQuotientValue.agda`](NuImprecisionQuotientValue.agda).
2. **Partial:** close the two quotient-`inst` residuals in
   [`NuImprecisionCatchupScratch.agda`](NuImprecisionCatchupScratch.agda#L961).
3. **Partial:** close the remaining eight leaves of
   [`left-catchup-indexed-prefixᵀ`](NuImprecisionCatchupScratch.agda#L1083).
4. **Partial:** enumerate and prove every non-`ν` case of
   [`weak-one-step-indexed-simulationᵀ`](NuImprecisionCatchupScratch.agda#L1343),
   then remove incomplete-pattern acceptance.
5. **Partial:** fill the checked `backward-target-value-or-source-blameᵀ`
   statement by proving the terminal induction B9 and packaging B11.
6. **Partial:** finish zero-step target-blame catch-up C1 and the dispatcher C2,
   then package `backward-target-blameᵀ` with the completed C4 assembly and
   its checked live adapter.
7. **Not yet started:** introduce the source-oriented one-step theorem F1–F2
   and the target-side value catch-up F3.
8. **Partial:** fill the checked `forward-source-valueᵀ` statement by lifting
   those results across the source trace and packaging F5–F7.
9. **Completed interface check:**
   [`terminal-components⇒gradual-dgg`](NuDGGTerminal.agda#L38) accepts the
   three proofs separately, and
   [`dynamic-gradual-guarantee-skeleton`](NuDGGTerminalSkeleton.agda#L17)
   checks their end-to-end fit.  The imported terminal bodies remain partial.

The backward value theorem is the best first trace-level target because its two
largest prerequisites already exist as partial checked declarations. The
forward theorem is structurally separate work: completing the target-oriented
dispatcher does not remove the need for its source-oriented mirror and its
value catch-up base.

## Interface freeze and ginger execution plan

### Two-layer skeleton

The skeleton is split into an interface layer and an implementation layer.
The interface layer is developed and reviewed with GPT 5.6 before proof cases
are delegated:

| File | Status | Role |
|---|---|---|
| [`NuDGGTerminal.agda`](NuDGGTerminal.agda) | completed | Strict wrapper with the three full terminal statements as separate arguments; produces `GradualDGG` |
| [`NuDGGTerminalForward.agda`](NuDGGTerminalForward.agda) | partial | Owns the exact `forward-source-valueᵀ` statement and its eventual proof |
| [`NuDGGTerminalBackwardValueDef.agda`](NuDGGTerminalBackwardValueDef.agda) | completed | Small statement module defining `BackwardTargetValueOrSourceBlameᵀ` |
| [`NuDGGTerminalBackwardValueProof.agda`](NuDGGTerminalBackwardValueProof.agda) | completed | Hole-free higher-order fuel induction and source-trace composition from the two dependency contracts |
| [`NuDGGTerminalBackwardValueLemma.agda`](NuDGGTerminalBackwardValueLemma.agda) | completed assembly; dependencies partial | Canonical application to the live dispatcher and value catch-up; excluded from the strict spine until both supplied lemmas are strict |
| [`NuDGGTerminalBackwardBlame.agda`](NuDGGTerminalBackwardBlame.agda) | partial | Owns the exact `backward-target-blameᵀ` statement and its eventual proof |
| [`NuDGGTerminalSkeleton.agda`](NuDGGTerminalSkeleton.agda) | completed interface check | Supplies the three named boundaries to the strict wrapper and therefore checks the path to `GradualDGG` |
| [`NuDGGTraceMeasure.agda`](NuDGGTraceMeasure.agda) | completed | Supplies the decreasing measure for target-terminal induction |
| [`NuDGGPreservation.agda`](NuDGGPreservation.agda) | completed | Supplies multi-step store well-formedness |
| [`NuDGGWeakResultPreservation.agda`](NuDGGWeakResultPreservation.agda) | completed | Four result-level runtime/store preservation lemmas, completed by the second GPT 5.5 ginger slice and rechecked locally against the shared multi-step store theorem |
| [`NuDGGTerminalBackwardBlameAssembly.agda`](NuDGGTerminalBackwardBlameAssembly.agda) | completed | Hole-free fuel induction proving that the frozen target-step and blame-catch-up interfaces suffice for the arbitrary-world backward-blame terminal theorem |
| [`NuDGGTerminalBackwardBlameIntegration.agda`](NuDGGTerminalBackwardBlameIntegration.agda) | completed live interface check | Instantiates the strict assembly with the live dispatcher and target-blame catch-up declarations; the focused consumer check passes, although those imported leaf bodies remain partial |
| [`NuImprecisionSimulationResultDef.agda`](NuImprecisionSimulationResultDef.agda) | completed | Strict 506-line home of the weak-result, indexed-outcome, transport/coherence, and left-catch-up result algebra; imported directly by contracts without the simulation core |
| [`NuImprecisionOneStepRelated.agda`](NuImprecisionOneStepRelated.agda) | completed | Strict canonical keep-step result and indexed-outcome builders extracted from the simulation core so terminal and identity roots do not import the 15,000-line implementation |
| [`NuImprecisionStoreLift.agda`](NuImprecisionStoreLift.agda) | completed | Sole strict definition site for canonical left/right store-lift results; coherent allocation proofs can import it without depending on the simulation core |
| [`NuImprecisionStorePrefix.agda`](NuImprecisionStorePrefix.agda) | completed | Sole strict definition site for source/target prefix-store inclusion and prefix transitivity; catch-up modules import it directly instead of inheriting these lemmas from the simulation core |
| [`NuImprecisionCatchupPrefixSupport.agda`](NuImprecisionCatchupPrefixSupport.agda) | completed | Strict home of nine silent-composition, target-prefix-frame, and terminal value/blame helpers extracted from the permissive scratch dispatcher; the focused strict check passes |
| [`NuImprecisionCatchupQuotientSupport.agda`](NuImprecisionCatchupQuotientSupport.agda) | completed | Strict home of the broader paired/down-up framing, narrowing, and final assembly helpers; quotient widening-pair transport has moved to a focused module with no compatibility re-export |
| [`NuWideningTransport.agda`](NuWideningTransport.agda) | completed extraction | Seventy-line low-level home of generic and fixed-mode widening transport through store changes; imports no term-imprecision result or simulation core |
| [`NuImprecisionQuotientWideningTransport.agda`](NuImprecisionQuotientWideningTransport.agda) | completed extraction | Focused transport of one id-only/general quotient widening pair; the paired-widening leaf now avoids both the 14,449-line simulation core and broad quotient support |
| [`NuImprecisionWorldCoherentCatchupComposition.agda`](NuImprecisionWorldCoherentCatchupComposition.agda) | completed | Strict coherent wrapper for silent-result resumption, preserving both final `WorldCoherent` and final left `StoreWf`; the focused strict check passes |
| [`NuImprecisionWorldCoherentCatchupPrefixFrames.agda`](NuImprecisionWorldCoherentCatchupPrefixFrames.agda) | completed | Five strict wrappers for target narrowing, widening, identity widening, reveal, and conceal frames; dependent pattern matching makes preservation of the final world and left store definitionally visible |
| [`NuImprecisionAtomicTargetReindex.agda`](NuImprecisionAtomicTargetReindex.agda) | completed | Strict exhaustive reconstruction of atomic-target value relations at an explicit desired type-imprecision index; closes target conversion identity roots without proof irrelevance |
| [`NuImprecisionOneStepTargetCastIdentityRoots.agda`](NuImprecisionOneStepTargetCastIdentityRoots.agda) | completed | Three strict β-id root outcomes for narrowing, general widening, and id-only widening target casts; the partial target-cast dispatcher now has eight holes instead of eleven |
| [`NuImprecisionTargetCastSequenceMidpointDef.agda`](NuImprecisionTargetCastSequenceMidpointDef.agda) | completed statement | Strict indexed family for the local midpoint evidence retained by one quotiented target-cast node; avoids an unsound global right-context-compatibility requirement |
| [`NuImprecisionOneStepTargetCastSequenceRoots.agda`](NuImprecisionOneStepTargetCastSequenceRoots.agda) | completed leaves | Strict narrowing and widening β-sequence root helpers consume an explicit midpoint witness and reconstruct the nested target relation; this proves the proposed local evidence is sufficient |
| Id-only target-cast β-sequence root | partial dependency | `right-id-only-compatible` supplies context composition, but the existing `widening⇒⊑ᵢ` route requires dense `Store.StoreWf`; the dispatcher has sparse `NuStore.StoreWf`. Ground tags mean the branch is not generally impossible, so it also needs retained midpoint evidence or a new sparse-store embedding theorem |
| General target-cast β-sequence midpoint integration | not yet started | The narrowing and general widening nodes must retain a local `TargetCastSequenceMidpointᵀ` witness and pass it to their root helpers; existing constructors retain only final `q` |
| [`NuImprecisionWorldCoherenceDef.agda`](NuImprecisionWorldCoherenceDef.agda) | completed statement | Freezes `WorldCoherent`, the exact store-correspondence invariant required before target seal cancellation can be a sound leaf |
| [`NuImprecisionWorldCoherenceProof.agda`](NuImprecisionWorldCoherenceProof.agda) | completed | Strict structural proof layer: empty world, exact entry-extension obligations, correspondence weakening, and matched/left/right canonical lift preservation |
| [`NuImprecisionWorldCoherenceLemma.agda`](NuImprecisionWorldCoherenceLemma.agda) | partial boundary | Strict assembly for matched, source-only, and target-only single-name lift-plus-allocation; crossed two-name allocation remains separate |
| [`NuImprecisionWorldCoherenceCrossedLemma.agda`](NuImprecisionWorldCoherenceCrossedLemma.agda) | completed | Separate strict crossed two-name allocation proof over `swapRight∀∀ᵢ`, using the exact two canonical lift witnesses and six-entry `crossedStoreⁱ` layout |
| [`NuImprecisionWorldCoherentResultDef.agda`](NuImprecisionWorldCoherentResultDef.agda) | completed statement | Continuing one-step and catch-up results expose final `WorldCoherent` and `SourceNameExclusive`; catch-up additionally exposes final left `StoreWf` |
| [`NuImprecisionWorldCoherentOneStepDef.agda`](NuImprecisionWorldCoherentOneStepDef.agda) | completed statement | Strengthened one-step contract consumes coherence, source-name exclusivity, and both source/target `StoreWf`, and returns both semantic invariants on every related successor branch |
| [`NuImprecisionWorldCoherentValueCatchupDef.agda`](NuImprecisionWorldCoherentValueCatchupDef.agda) | completed statement | Strengthened value-catch-up consumes initial coherence, source-name exclusivity, and left `StoreWf`, and exposes all three at the final catch-up world |
| [`NuImprecisionWorldCoherentValueCatchupPrefixDef.agda`](NuImprecisionWorldCoherentValueCatchupPrefixDef.agda) | completed statement | Ambient-prefix induction contract: the relation may use a smaller prefix world, while coherence, source-name exclusivity, and left `StoreWf` belong to the ambient evaluation world |
| [`NuImprecisionWorldCoherentValueCatchupProof.agda`](NuImprecisionWorldCoherentValueCatchupProof.agda) | completed adapter proof | Strictly derives the public coherent value-catch-up contract from the prefix worker by applying it to `prefix-reflⁱ` |
| [`NuImprecisionWorldCoherentSourceRuntimeCatchupDef.agda`](NuImprecisionWorldCoherentSourceRuntimeCatchupDef.agda) | completed statement | Strict eight-field assembly record; bullet, ordinary `ν`, runtime `ν ★`, narrowing, and widening fields now refer to their own whole contracts |
| [`NuImprecisionWorldCoherentSourceBulletCatchupDef.agda`](NuImprecisionWorldCoherentSourceBulletCatchupDef.agda) | completed statement | Exact former runtime-field telescope for source-only post-allocation bullet catch-up |
| [`NuImprecisionWorldCoherentSourceBulletCatchupProof.agda`](NuImprecisionWorldCoherentSourceBulletCatchupProof.agda) | completed higher-order proof | Strictly reconstructs the allocated `α⊑ᵀ` relation and delegates to the whole value-prefix catch-up contract; canonical assembly remains in the mutual SCC |
| [`NuImprecisionWorldCoherentSourceNuCatchupDef.agda`](NuImprecisionWorldCoherentSourceNuCatchupDef.agda) | completed statement | Exact ordinary source-`ν` handler contract; its inhabitant is downstream of source-bullet and source-reveal, not in the minimal SCC |
| [`NuImprecisionWorldCoherentSourceNuCastCatchupDef.agda`](NuImprecisionWorldCoherentSourceNuCastCatchupDef.agda) | completed statement | Exact runtime `ν ★` handler boundary participating in the widening-`inst` mutual SCC |
| [`NuImprecisionWorldCoherentSourceNarrowCatchupDef.agda`](NuImprecisionWorldCoherentSourceNarrowCatchupDef.agda) | completed statement | Whole accumulated-world source-narrowing handler contract |
| [`NuImprecisionWorldCoherentFinalSourceNarrowCatchupDef.agda`](NuImprecisionWorldCoherentFinalSourceNarrowCatchupDef.agda) | completed statement | Exact-final terminal source-narrowing semantics, separated from accumulated-change framing |
| [`NuImprecisionWorldCoherentSourceWidenCatchupDef.agda`](NuImprecisionWorldCoherentSourceWidenCatchupDef.agda) | completed statement | Whole accumulated-world source-widening handler contract and the precise dependency used by terminal paired widening |
| [`NuImprecisionWorldCoherentFinalSourceWidenCatchupDef.agda`](NuImprecisionWorldCoherentFinalSourceWidenCatchupDef.agda) | completed statement | Exact-final terminal source-widening semantics; active `inst` remains the explicit allocation-sensitive case |
| [`NuImprecisionWorldCoherentSourceConcealCatchup.agda`](NuImprecisionWorldCoherentSourceConcealCatchup.agda) | completed leaf | GPT 5.5 proved all conceal-conversion cases on ginger; the adapted proof preserves final coherence and left `StoreWf` and passes a local focused strict check |
| [`NuImprecisionContextExclusivityDef.agda`](NuImprecisionContextExclusivityDef.agda) | completed statement | Separate source-name role invariant: a source-only row and matched row cannot share the same source name; this remains distinct from store-world coherence |
| [`NuImprecisionContextExclusivityProof.agda`](NuImprecisionContextExclusivityProof.agda) | completed proof | Strict exhaustive preservation under empty, matched, source-only, target-only, and crossed context transformations; the focused no-unsolved-metas check passes |
| [`NuImprecisionSourceSealCancellationDef.agda`](NuImprecisionSourceSealCancellationDef.agda) | completed repaired statement | Exact-world cancellation now requires `SourceNameExclusive Φ`; the strict contract check passes |
| [`NuImprecisionSourceSealCancellationCounterexample.agda`](NuImprecisionSourceSealCancellationCounterexample.agda) | completed counterexample | Strictly packages the valid old premise and impossible conclusion in a context containing both `0 ˣ⊑★` and `0 ˣ⊑ˣ 0`; the focused no-unsolved-metas check passes |
| [`NuImprecisionSourceSealCancellationProof.agda`](NuImprecisionSourceSealCancellationProof.agda) | completed proof | Exhaustive prefix-recursive inversion; `SourceNameExclusive` eliminates exactly the two target tag-widening overlap cases, and the focused strict check passes |
| [`NuImprecisionSourceSealCancellationLemma.agda`](NuImprecisionSourceSealCancellationLemma.agda) | completed lemma | Canonical strict inhabitant of the repaired source-seal cancellation contract |
| [`NuImprecisionWorldCoherentSourceUnsealCatchupDef.agda`](NuImprecisionWorldCoherentSourceUnsealCatchupDef.agda) | completed statement | Strict assembly contract; final source-name exclusivity is obtained from the coherent inner catch-up result |
| [`NuImprecisionWorldCoherentSourceUnsealCatchupProof.agda`](NuImprecisionWorldCoherentSourceUnsealCatchupProof.agda) | completed higher-order proof | Strictly derives active source-unseal catch-up from repaired seal cancellation; a structural `AppliedUnseal` equality view keeps transformed indices in constructor form, and the focused check passes |
| [`NuImprecisionWorldCoherentSourceUnsealCatchupLemma.agda`](NuImprecisionWorldCoherentSourceUnsealCatchupLemma.agda) | completed lemma | Canonical strict assembly supplies source-seal cancellation to the higher-order unseal proof |
| [`NuImprecisionWorldCoherentSourceRevealCatchupDef.agda`](NuImprecisionWorldCoherentSourceRevealCatchupDef.agda) | completed statement | Full source reveal-conversion handler contract, with active unseal isolated behind the completed higher-order dependency |
| [`NuImprecisionWorldCoherentSourceRevealCatchupProof.agda`](NuImprecisionWorldCoherentSourceRevealCatchupProof.agda) | completed higher-order proof | GPT 5.5 supplied the exhaustive strict dispatch for all six reveal forms; identity and inert forms use source-cast framing, while active unseal calls the whole supplied unseal contract |
| [`NuImprecisionWorldCoherentSourceRevealCatchupLemma.agda`](NuImprecisionWorldCoherentSourceRevealCatchupLemma.agda) | completed lemma | Canonical strict assembly supplies the completed source-unseal lemma |
| [`NuImprecisionSourceTagCancellationDef.agda`](NuImprecisionSourceTagCancellationDef.agda) | completed sound statement | Pure same-ground source-tag cancellation; its ground/value hypotheses admit restricted quotient elimination in the surviving quotient-up case |
| [`NuImprecisionGroundValueQuotientEliminationDef.agda`](NuImprecisionGroundValueQuotientEliminationDef.agda) | completed statement | Restricted elimination from a ground-related quotient relation between values to an existential ordinary relation; does not imply global dequotienting |
| [`NuImprecisionGroundValueQuotientEliminationProof.agda`](NuImprecisionGroundValueQuotientEliminationProof.agda) | completed proof | Variable/base cases contradict inert value narrowing; the function-ground case reclassifies inert down coercions as paired widening |
| [`NuImprecisionGroundValueQuotientEliminationLemma.agda`](NuImprecisionGroundValueQuotientEliminationLemma.agda) | completed lemma | Canonical strict inhabitant of the restricted elimination theorem |
| [`NuImprecisionSourceTagQuotientUpProof.agda`](NuImprecisionSourceTagQuotientUpProof.agda) | completed higher-order adapter | Eliminates the ground-value quotient inner relation and rebuilds either id-only or general target widening without a physical-endpoint alignment theorem |
| [`NuImprecisionSourceTagCancellationProof.agda`](NuImprecisionSourceTagCancellationProof.agda) | completed higher-order proof | Exhaustive structural proof takes only `GroundValueQuotientEliminationᵀ`; quotient-up, target cast/conversion, paired widening, and allocation-prefix cases are explicit |
| [`NuImprecisionSourceTagCancellationLemma.agda`](NuImprecisionSourceTagCancellationLemma.agda) | completed lemma | Canonical strict assembly supplies ground-value quotient elimination |
| [`NuImprecisionSourceCastSequenceMidpointCounterexample.agda`](NuImprecisionSourceCastSequenceMidpointCounterexample.agda) | completed corrected obstruction | Strictly packages coherent, exclusive, well-typed two-seal endpoints with no midpoint, but also proves that the example violates `SealModeStore★`; `seal-enabled-store-entry-star` explains why the raw obstruction cannot refute the full source-runtime boundary |
| [`NuImprecisionSourceCastSequenceMidpointDef.agda`](NuImprecisionSourceCastSequenceMidpointDef.agda) | completed statement | Exact narrowing and widening midpoint capability over the ambient prefix, coherence, exclusivity, final sparse `StoreWf`, cast mode, and `SealModeStore★` package |
| [`NuImprecisionSourceCastSequenceMidpointProof.agda`](NuImprecisionSourceCastSequenceMidpointProof.agda) | completed proof | Strict-cross tag/untag shapes yield the only ground midpoint; final-store uniqueness plus prefix inclusion eliminates seal/unseal sequence shapes |
| [`NuImprecisionSourceCastSequenceMidpointLemma.agda`](NuImprecisionSourceCastSequenceMidpointLemma.agda) | completed lemma | Canonical strict inhabitant of both midpoint fields |
| [`NuImprecisionLeftSilentPairedCastTransportDef.agda`](NuImprecisionLeftSilentPairedCastTransportDef.agda) | completed statement; hard proof | Exact accumulated-change transport contract for `PairedCast`; arbitrary source changes must rebuild final `StoreCorresponds` or carry an explicit world embedding |
| [`NuImprecisionLeftSilentPairedWideningTransportDef.agda`](NuImprecisionLeftSilentPairedWideningTransportDef.agda) | completed statement | Store-neutral constructor-family transport independent of final world coherence |
| [`NuImprecisionLeftSilentPairedWideningTransportProof.agda`](NuImprecisionLeftSilentPairedWideningTransportProof.agda) | completed proof | GPT 5.5 adapter transports a quotient widening pair, its compatibility witness, and both cast-widening and id-widening results |
| [`NuImprecisionLeftSilentPairedWideningTransportLemma.agda`](NuImprecisionLeftSilentPairedWideningTransportLemma.agda) | completed lemma | Canonical strict inhabitant of the widening constructor-family transport contract |
| [`NuImprecisionLeftSilentPairedConversionTransportDef.agda`](NuImprecisionLeftSilentPairedConversionTransportDef.agda) | completed statement; hard proof | Sole remaining accumulated-transport boundary that reconstructs final paired `StoreCorresponds` evidence |
| [`NuImprecisionLeftSilentStoreCorrespondsTransportDef.agda`](NuImprecisionLeftSilentStoreCorrespondsTransportDef.agda) | completed statement; hard proof | Minimal relational-world embedding capability preserving both stored and linked correspondences through accumulated changes; projected store equalities cannot recover linked entries |
| [`NuImprecisionRelStoreEmbeddingDef.agda`](NuImprecisionRelStoreEmbeddingDef.agda) | completed extraction | Small stable definition of relational-store embedding, moved out of the simulation core with no compatibility re-export |
| [`NuImprecisionRelStoreEmbeddingProof.agda`](NuImprecisionRelStoreEmbeddingProof.agda) | completed proof | Transports both stored and linked `StoreCorresponds` evidence through one relational-store embedding; membership helpers remain private |
| [`NuImprecisionWeakOneStepStoreLineageDef.agda`](NuImprecisionWeakOneStepStoreLineageDef.agda) | completed statement | Packages the smallest sufficient lineage invariant: an embedding under accumulated source/target renamings followed by a prefix into the result store |
| [`NuImprecisionLeftSilentStoreCorrespondsTransportProof.agda`](NuImprecisionLeftSilentStoreCorrespondsTransportProof.agda) | completed lineage-aware proof | Uses ambient-prefix weakening, relational-store embedding, endpoint reindexing, and result-prefix weakening to preserve stored or linked correspondence |
| Coherent catch-up store-lineage construction | partial; hard plumbing | The lineage statement and its correspondence consumer are strict; identity/frame/composition/allocation constructors still need to construct and propagate lineage before the accumulated paired-conversion contract can receive it |
| [`NuImprecisionLeftSilentPairedConversionTransportProof.agda`](NuImprecisionLeftSilentPairedConversionTransportProof.agda) | completed higher-order proof | Exhaustively transports paired reveal/conceal endpoints and reduces their correspondence evidence to `LeftSilentStoreCorrespondsTransportᵀ` |
| [`NuImprecisionLeftSilentPairedCastTransportProof.agda`](NuImprecisionLeftSilentPairedCastTransportProof.agda) | completed higher-order proof | Exhaustively derives full paired-cast transport from the widening and conversion constructor-family capabilities |
| [`NuImprecisionWorldCoherentFinalPairedCastCatchupDef.agda`](NuImprecisionWorldCoherentFinalPairedCastCatchupDef.agda) | completed statement | Exact-final-world terminal paired-cast contract retaining target inertness, final coherence, source-name exclusivity, and left `StoreWf` |
| [`NuImprecisionWorldCoherentFinalPairedConversionCatchupDef.agda`](NuImprecisionWorldCoherentFinalPairedConversionCatchupDef.agda) | completed statement | Constructor-level terminal paired-conversion capability retaining all final-world invariants |
| [`NuImprecisionWorldCoherentFinalPairedConversionCatchupProof.agda`](NuImprecisionWorldCoherentFinalPairedConversionCatchupProof.agda) | completed proof | Exhaustive strict proof: source blame and identities take administrative steps, inert reveal/conceal forms are terminal frames, and source unseal is impossible against target inertness |
| [`PairedWideningCompatibility.agda`](../PairedWideningCompatibility.agda) | completed definition | `PairedWideningCompatible` records either source inertness or the exact bridge obtained from target inertness; `PairedCast.paired-widening` and `νcast⊑νcastᵀ` carry it explicitly |
| [`NuImprecisionSimulationCore.agda`](NuImprecisionSimulationCore.agda) paired-widening migration | completed integration | Two-sided, left-only, under-binder, allocation-frame, transport, and coherence paths preserve the compatibility witness; the focused strict core check passes |
| [`NuImprecisionAllocationSimulation.agda`](NuImprecisionAllocationSimulation.agda) paired-widening migration | completed integration | Matched `ν ★` allocation, value/source-blame catch-up, transport, coherence, and indexed outcomes thread the compatibility witness; the focused strict check passes |
| [`NuImprecisionCatchupScratch.agda`](NuImprecisionCatchupScratch.agda) paired-widening migration | partial legacy debt | Four `νcast⊑νcastᵀ` branches still use the old constructor shape and the local allocation helper lacks compatibility; repair or retire this permissive scratch file before strict-spine inclusion |
| [`NuImprecisionWorldCoherentFinalPairedWideningCatchupDef.agda`](NuImprecisionWorldCoherentFinalPairedWideningCatchupDef.agda) | completed repaired statement | Exact-final terminal widening now requires `PairedWideningCompatible Φ Δᴸ Δᴿ c c′ B A′` |
| [`NuImprecisionWorldCoherentFinalPairedWideningCatchupProof.agda`](NuImprecisionWorldCoherentFinalPairedWideningCatchupProof.agda) | completed higher-order proof | Source-inert pairs are terminal; source-active/target-inert pairs use the compatibility bridge, the supplied whole `WorldCoherentSourceWidenCatchupᵀ`, and a target-cast frame; source blame is propagated |
| `NuImprecisionWorldCoherentFinalPairedWideningCatchupLemma.agda` | not yet started; mutual assembly | No permissive canonical assembly is created: the strict proof exposes only the genuine source-widen dependency, whose canonical inhabitant belongs to the mutual SCC |
| [`NuImprecisionWorldCoherentFinalPairedWideningCatchupCounterexample.agda`](NuImprecisionWorldCoherentFinalPairedWideningCatchupCounterexample.agda) | completed regression | The former active-source-unseal/inert-target-tag pair cannot inhabit `PairedWideningCompatible`; this keeps the original obstruction as a strict guard on the repaired relation |
| [`NuImprecisionWorldCoherentFinalPairedCastCatchupProof.agda`](NuImprecisionWorldCoherentFinalPairedCastCatchupProof.agda) | completed higher-order proof | Exhaustively derives the exact-final-world contract from strict paired-conversion and repaired paired-widening capabilities |
| [`NuImprecisionWorldCoherentSourcePairedCastCatchupDef.agda`](NuImprecisionWorldCoherentSourcePairedCastCatchupDef.agda) | completed statement | Top accumulated-world paired-cast handler, matching the strengthened source-runtime field |
| [`NuImprecisionWorldCoherentSourcePairedCastCatchupProof.agda`](NuImprecisionWorldCoherentSourcePairedCastCatchupProof.agda) | completed higher-order proof; partial assembly | Strictly composes accumulated paired-cast transport with exact-final-world catch-up; canonical assembly still waits for store-lineage propagation and the mutual source-runtime/paired-widening join |
| `NuImprecisionWorldCoherentSourceRuntimeCatchupProof.agda` | partial | Conceal/reveal and terminal paired-widening layers are complete; source-bullet has a strict higher-order proof; the minimal canonical SCC is value-prefix catch-up, bullet, `ν ★`, widening-`inst`, paired cast, and final paired widening. Ordinary `ν` is downstream. Exact-final narrowing/widening and paired-conversion lineage remain active work |
| [`NuImprecisionWorldCoherentQuotientInstCatchupDef.agda`](NuImprecisionWorldCoherentQuotientInstCatchupDef.agda) | completed narrowed statement | Strict mode-polymorphic final-state contract shared by ordinary-down and gen-down quotient-`inst` residuals; it requires the actual ready inner value `V ⟨ d ⟩` and no-bullet evidence |
| [`NuImprecisionWorldCoherentQuotientRepresentativeInstCatchupDef.agda`](NuImprecisionWorldCoherentQuotientRepresentativeInstCatchupDef.agda) | completed statement; hard proof | Exposes `quotientᵖ D≈C C⊑C′ C′≈D′` and asks for direct coherent catch-up without inventing an ordinary relation between physical endpoints |
| [`NuImprecisionWorldCoherentQuotientRepresentativeInstPathCatchupDef.agda`](NuImprecisionWorldCoherentQuotientRepresentativeInstPathCatchupDef.agda) | completed statement | Replaces arbitrary permutation derivations by explicit finite paths of oriented contextual adjacent swaps while retaining the original quotient evidence in the term relation |
| [`NuImprecisionWorldCoherentQuotientRepresentativeInstPathCatchupProof.agda`](NuImprecisionWorldCoherentQuotientRepresentativeInstPathCatchupProof.agda) | completed higher-order proof | Normalizes `refl`, `sym`, `trans`, arrow/`∀` congruence, and swap into paths and reduces representative catch-up to the path-aware capability |
| Quotient representative-`inst` path semantics | not yet started; hard boundary | Prove the identity path and prepend-one-oriented-contextual-swap cases, including whole-source reduction, crossed store/world construction, and continuation on the residual path; no canonical `Lemma` exists yet |
| [`NuImprecisionWorldCoherentQuotientInstCatchupProof.agda`](NuImprecisionWorldCoherentQuotientInstCatchupProof.agda) | completed higher-order proof | Strict dependent elimination of `qD` reduces the existing quotient-`inst` contract to the direct representative capability |
| `NuImprecisionWorldCoherentQuotientInstCatchupLemma.agda` | not yet started | Canonical assembly waits for a strict representative-level inhabitant; no permissive lemma is created |
| [`NuImprecisionQuotientToOrdinaryCounterexample.agda`](NuImprecisionQuotientToOrdinaryCounterexample.agda) | completed obstruction | An empty-context adjacent-`∀` swap is quotient-related but has no ordinary relation; strict proof rules out generic dequotienting, so quotient-`inst` needs direct permutation-aware catch-up |
| [`NuImprecisionWorldCoherentQuotientClassificationDef.agda`](NuImprecisionWorldCoherentQuotientClassificationDef.agda) | completed narrowed statement | Strict structural classifier returning either a coherent terminal quotient result or the unique outer-`inst` residual with `Value (V ⟨ d ⟩)`, `No• (V ⟨ d ⟩)`, and reduction evidence |
| [`NuImprecisionWorldCoherentQuotientClassificationProof.agda`](NuImprecisionWorldCoherentQuotientClassificationProof.agda) | completed proof | GPT 5.5 supplied the exhaustive classifier on Ginger; local integration strengthened it to retain final source-name exclusivity and the ready `V ⟨ d ⟩` residual, and the focused strict check passes |
| [`NuImprecisionWorldCoherentQuotientFinalCatchupDef.agda`](NuImprecisionWorldCoherentQuotientFinalCatchupDef.agda) | completed statement | Complete terminal down/up quotient-node contract; unlike the narrower `Inst` leaf, it returns a coherent, left-well-formed catch-up result for every final source value/blame classification |
| [`NuImprecisionWorldCoherentQuotientFinalCatchupProof.agda`](NuImprecisionWorldCoherentQuotientFinalCatchupProof.agda) | completed higher-order proof | Strict two-way assembly from coherent quotient classification and the quotient-`inst` contract; the source-runtime record is not needed at this join |
| [`NuImprecisionWorldCoherentValueCatchupPrefixProof.agda`](NuImprecisionWorldCoherentValueCatchupPrefixProof.agda) | completed higher-order proof | Exhaustive recursive dispatcher from exactly `WorldCoherentSourceRuntimeCatchupᵀ` and `WorldCoherentQuotientFinalCatchupᵀ`; contains no holes/options/postulates, imports no scratch dispatcher, and passes a focused strict check |
| `NuImprecisionWorldCoherentValueCatchupLemma.agda` | not yet started | Canonical assembly waits for the strict prefix proof and its strict allocation/quotient leaves |
| [`NuDGGTerminalBackwardValueWorldCoherentDef.agda`](NuDGGTerminalBackwardValueWorldCoherentDef.agda) | completed statement | Arbitrary-world backward-value terminal contract with initial world coherence and source-name exclusivity; the closed public conclusion is unchanged |
| [`NuDGGTerminalBackwardValueWorldCoherentProof.agda`](NuDGGTerminalBackwardValueWorldCoherentProof.agda) | completed proof | Hole-free higher-order fuel induction threads both invariants from one-step outcomes into recursive value catch-up; the focused strict check passes |
| [`NuDGGClosedWorld.agda`](NuDGGClosedWorld.agda) | completed | Supplies both `empty-store-wf` and the vacuous `empty-world-coherent` witness needed when the strengthened arbitrary-world theorem is specialized back to closed DGG |
| [`NuImprecisionTargetSealCancellationDef.agda`](NuImprecisionTargetSealCancellationDef.agda) | completed statement | Exact terminal target-seal cancellation contract with world coherence, target-store well-formedness, physical membership, value/no-bullet facts, and explicit old/new indices |
| [`NuImprecisionTargetSealCancellationProof.agda`](NuImprecisionTargetSealCancellationProof.agda) | completed proof | Hard quotient/value inversion with ambient-prefix recursion; source seals recurse via exact correspondence, target-only seals strip, paired conceal becomes source-only conceal, allocation prefixes rebuild, and all incompatible cast/value forms are eliminated exhaustively |
| [`NuImprecisionTargetSealCancellationLemma.agda`](NuImprecisionTargetSealCancellationLemma.agda) | completed lemma | Canonical inhabitant of `TargetSealCancellationᵀ`; its focused assembly check passes without importing the dispatcher or catch-up implementation |
| [`NuImprecisionWorldCoherentTargetRevealRootDef.agda`](NuImprecisionWorldCoherentTargetRevealRootDef.agda) | completed statement | Full coherent target reveal-unseal root contract, including initial coherence, target store typing and membership, runtime/value premises, and the desired unsealed index |
| [`NuImprecisionWorldCoherentTargetRevealRootProof.agda`](NuImprecisionWorldCoherentTargetRevealRootProof.agda) | completed proof | Strict higher-order proof from coherent value catch-up and target-seal cancellation; transports store evidence into the catch-up world, cancels the seal, and retargets the result without losing transport, type, trace, or coherence evidence |
| `NuImprecisionWorldCoherentTargetRevealRootLemma.agda` | not yet started | Canonical assembly waits for a strict inhabitant of `WorldCoherentLeftValueCatchupᵀ`; no permissive assembly file is created in the meantime |
| [`NuImprecisionTargetBlameCatchup.agda`](NuImprecisionTargetBlameCatchup.agda) | completed | Hole-free structural target-blame catch-up, including source allocation and all four source cast/conversion tails |
| [`NuImprecisionCatchupSourceCastTerminal.agda`](NuImprecisionCatchupSourceCastTerminal.agda) | completed | Two arbitrary-type terminal frame lemmas for source cast-to-blame and source inert-cast outcomes |
| [`NuImprecisionQuotientInstView.agda`](NuImprecisionQuotientInstView.agda) | completed | Exhaustive quotient-instantiation spine view exposing only sound structural witnesses |
| [`NuImprecisionOneStepSourceCastFrames.agda`](NuImprecisionOneStepSourceCastFrames.agda) | completed | Two strict outcome wrappers that lift recursive source narrowing/widening cast results or source blame |
| [`NuImprecisionOneStepSourceConversionFrames.agda`](NuImprecisionOneStepSourceConversionFrames.agda) | completed | Two strict reveal/conceal outcome wrappers; transported conversion provenance supplies the related branch and `cast-blame-tailᵀ` supplies the exceptional branch |
| [`NuImprecisionCatchupSourceAllocationTerminal.agda`](NuImprecisionCatchupSourceAllocationTerminal.agda) | completed | Two strict pre-allocation `ν`/`ν ★` terminal-value frames, including prefix-lifted reveal/seal/widening evidence and preservation of silent, transport, and coherence invariants |
| [`NuDGGStrictSpine.agda`](NuDGGStrictSpine.agda) | completed check target; milestone run pending | Strict aggregate that deliberately excludes all partial proof modules; its first clean-room rebuild was stopped after the checking-cost policy changed |

The three terminal modules now also state their arbitrary-world recursive
theorems.  Each theorem quantifies over the initial imprecision world, both
store typings, both runtime invariants, and the transported type index; its
conclusion exposes final store projections relative to the initial stores.
The closed terminal theorem in each file is already a checked specialization
of that general statement.

The backward-blame member of the next interface layer is complete: its strict,
higher-order trace assembly takes the major leaf simulations as arguments and
proves the terminal trace induction without postulates.  The same pattern
should next be applied to backward target-value-or-source-blame.  This checks
that leaf interfaces carry enough world, store, runtime, and type-action
evidence before the leaf cases are completed.

The implementation layer will eventually have the following stable module
boundaries:

| Planned module | Major proof boundary | Model assignment |
|---|---|---|
| `NuImprecisionValueCatchup.agda` | Promote `left-catchup-indexed-prefixᵀ` after its ten holes close | GPT 5.6 for quotient/allocation/cast leaves |
| `NuImprecisionTargetStep.agda` | Promote the exhaustive target-oriented dispatcher | GPT 5.6 integration; GPT 5.5 for frozen simple case helpers |
| [`NuImprecisionTargetBlameCatchup.agda`](NuImprecisionTargetBlameCatchup.agda) | Promoted hole-free structural target-blame catch-up | Completed by GPT 5.5 from a GPT 5.6-frozen interface; integrated and focused checked here |
| `NuImprecisionSourceStep.agda` | Source-oriented one-step simulation | GPT 5.6 |
| `NuImprecisionRightValueCatchup.agda` | Target catch-up from an already valuable source | GPT 5.6 design; GPT 5.5 for frozen simple cases |

The live declarations remain in `NuImprecisionCatchupScratch` until they are
hole-free.  Promotion moves the canonical declaration and deletes the obsolete
scratch copy; it does not introduce a compatibility alias.

### Tiered checking lanes

Use the smallest check that can detect the expected class of error:

1. **Per edit and per worker:** check only the owned module with
   `agda --no-allow-unsolved-metas -v0 proof/<OwnedModule>.agda`.  New
   statement-only scaffolding belongs in a strict `Def` module, and unfinished
   proof dependencies belong in the telescope of a strict higher-order
   `Proof`.  Only pre-existing legacy scratch modules may remain deliberately
   permissive while they are being decomposed.
2. **Per integration batch:** check the nearest focused consumer, such as one
   terminal theorem module, `NuDGGTerminalBackwardBlameIntegration`, or
   `NuDGGTerminalSkeleton`.  Batch several independent worker results before
   paying this cost.  Treat a consumer as high-cost if a clean dependency
   rebuild dominates its nominally small source file.
3. **At interface freezes and proof milestones only:** check
   `NuDGGStrictSpine`, followed by `All.agda` when broad compatibility is
   warranted.  These are not per-commit or per-worker commands.

`NuDGGStrictSpine` imports only hole-free modules.  `NuDGGTerminalSkeleton` is
the exploratory end-to-end fit check and imports the three explicitly partial
terminal modules.  `All.agda` remains the broad compatibility check, but is
not by itself a strict completion certificate while it imports active scratch
modules.

A completed worker slice may not contain holes, postulates, incomplete
matches, or new foundational definitions.  Its default validation stops after
the targeted owned-module check; the GPT 5.6 integrator owns the focused and
full checks.

### Agda modularity and checking-cost policy

Parameterized modules are useful for organizing a family of results that all
assume the same proof capabilities, but they are not a separate interface
compilation mechanism.  Agda abstracts module parameters over every exported
definition; applying the module creates definitions that apply those
parameters.  Thus, for the single backward-blame theorem, the explicit
`one-step` and `target-blame-catchup` arguments of
[`backward-target-blame-general-from-componentsᵀ`](NuDGGTerminalBackwardBlameAssembly.agda#L103)
already provide essentially the same elaborated boundary.  Convert an assembly
to a parameterized module only when several definitions share the capability
telescope and the namespace improves readability.

The important compilation boundary is the source file.  Agda stores checked
case trees and resolved implicits in `.agdai` interface files and loads an
external module through that interface.  Major architectural joins therefore
use the naming and dependency policy in [`proof/README.md`](README.md):

1. Put each complete major theorem contract in a small strict `<Stem>Def`
   module.
2. Put its higher-order implementation in a strict `<Stem>Proof` module that
   imports dependency `Def` modules rather than dependency proofs.
3. Use a small `<Stem>Lemma` module only to supply completed canonical
   dependencies.  Keep it outside the strict spine until those dependencies
   are themselves strict.
4. Keep each changing leaf proof in its own implementation module; do not make
   unrelated workers import the large dispatcher scratch file.
5. Represent every unfinished architectural dependency as a higher-order
   contract parameter, not an Agda hole.  Avoiding `--allow-unsolved-metas` is
   an explicit objective of the split, in addition to checking-time isolation.
   If the canonical dependency graph is mutual, leave the `Lemma` assembly
   absent until the strongly connected proof is ready; a strict `Def` and
   higher-order `Proof` still count as completed architectural work.
6. Once a large proof is complete, consider putting its definition in an
   `opaque` block if no client relies on its definitional reduction.  Agda 2.7
   documents opacity specifically as a way to control unfolding for
   performance.  Apply this selectively and recheck the nearest consumer,
   because an equality proof that closes by reduction may need an explicit
   `unfolding` clause instead.

The completed backward-blame assembly already has the first four parts of this
shape.  The cold live consumer took several minutes because it had to rebuild
the changing scratch dependency; after interfaces were cached, repairing the
wrong relation import and rechecking the same consumer took about five seconds.
This is evidence that module application is not the current bottleneck.

Before changing proof architecture for performance, collect one cold profile
at the relevant milestone:

    agda --profile=modules -v0 proof/<FocusedConsumer>.agda

If one owned module dominates, profile its definitions separately:

    agda --profile=definitions -v0 proof/<OwnedModule>.agda

Do not profile `All.agda` by default.  Preserve the resulting module and
definition timings in this log, then optimize the measured boundary.  Keep
Agda's default interface caching and default projection-like optimization
enabled; do not use the interface-ignoring debug flags in ordinary work.

`Def`, `Proof`, and completed `Lemma` modules must not enable unsolved metas or
incomplete matches.  A command-line `--no-allow-unsolved-metas` does not
reliably override a source module's local permissive option, so strict
promotion requires removing that option and checking again.

Primary Agda references: the
[2.7 module-system description](https://agda.readthedocs.io/en/v2.7.0/language/module-system.html),
[interface-file description](https://agda.readthedocs.io/en/stable/tools/interface-files.html),
[2.7 opaque-definition description](https://agda.readthedocs.io/en/v2.7.0/language/opaque-definitions.html),
and [2.7.0.1 profiling options](https://agda.readthedocs.io/en/v2.7.0.1/tools/command-line-options.html#profiling-and-debugging-options).

On ginger, replace the bare `agda` above with the repository wrapper:

    scripts/agda-ginger --no-allow-unsolved-metas -v0 proof/<OwnedModule>.agda

The canonical operational instructions, paths, checking tiers, and
troubleshooting guide are in
[`scripts/GINGER_AGDA.md`](../../scripts/GINGER_AGDA.md).  Keep that guide in
sync if either installed path or the worker workflow changes.

The wrapper changes to `GTSF/` itself, pins
`/home/jsiek/.local/opt/Agda-v2.7.0.1`, and sets `Agda_datadir` to that
installation's `data` directory.  It also sets `AGDA_DIR` to the checked-in
`scripts/agda-ginger-config`, whose local library descriptor points at the
adjacent stdlib source.  Agda therefore stores any refreshed stdlib interfaces
inside the worktree rather than the read-only installation.  This avoids the
executable's stale compiled-in Cabal data path, dependence on per-user library
registration, and per-worker copies of the standard-library source.  The
executable prefix can be overridden with `GINGER_AGDA_PREFIX`; update the
small local library descriptor if the stdlib installation moves.

### Ginger work-package contract

The remote repository is `/home/jsiek/src/AI-for-pl` on
`ginger.luddy.indiana.edu`.  Each GPT 5.5 worker receives a separate worktree and a
branch based on one frozen interface commit.  Each work package records:

1. the exact theorem statement and base commit;
2. one owned file or a nonoverlapping helper module;
3. allowed imports and explicit forbidden API/definition changes;
4. the cheap owned-module validation command; focused and full aggregate
   checks are assigned to the GPT 5.6 integrator, not every worker;
5. the rule that any required interface change is reported rather than made;
6. a final summary of remaining holes, which must be zero for integration.

Begin with two workers.  The first tasks should be short, mechanical case
families whose helper signatures have already been checked by the GPT 5.6
trace skeleton.  Scale the worker count only after both pilot branches
integrate without interface repair.  Quotient recursion, allocation-world
permutations, dependent transports, termination architecture, and dispatcher
integration stay with GPT 5.6 here.

Bootstrap status on 2026-07-20: the corrected host is reachable, the tracked
checkout is clean on `main`, Agda 2.7.0.1 and standard library 2.1.1 are under
`/home/jsiek/.local/opt`, Codex CLI 0.144.6 is installed, and the model catalog
exposes the exact slug `gpt-5.5`.  The first worker ran in an isolated worktree
on branch `codex/ginger-dgg-quotient-seal-cases` and repaired the four missing
quotient pattern clauses plus their ambiguous inference boundary.  Its first
validation attempt exposed the stale compiled-in Agda data path and a sandbox
attempt to refresh installed stdlib interfaces; `scripts/agda-ginger` now makes
the runtime path explicit and redirects Agda's application/library cache into
the worktree for every future worker.  Do not change GitHub authentication as
part of this bootstrap.

## Definition audit

The right-only `ν` constructors use the target-only context transformation

\[
  \Uparrow_R(X\sqsubseteq\star)=X\sqsubseteq\star,
  \qquad
  \Uparrow_R(X\sqsubseteq Y)=X\sqsubseteq(Y+1).
\]

This correctly avoids inventing a source seal. It does not by itself provide
the relation needed immediately after the target allocates:

\[
  N \sqsubseteq (\uparrow N')\,\bullet.
\]

The term relation now has a dual `⊑αᵀ` state with an explicit, well-typed
post-allocation imprecision index. The right-only `ν` and `ν ★` constructors
carry this index as an invariant, so allocation cannot manufacture a relation
between the unchanged source type and the opened target body.

The first relational `β-Λ•` proof exposed a second store boundary. A `Λ` body
is related under the shifted old store, while allocation adds a fresh entry.
The `allocation-matchedᵀ` and `allocation-leftᵀ` rules cross exactly this
extension. They require a `LiftStoreⁱ` or `LiftLeftStoreⁱ` witness for the tail
and explicit refined typings under the extended stores; they do not permit
arbitrary store replacement.

## Work sequence

1. Add and validate the right-only post-allocation bullet state. — checked
2. Prove right-only ordinary `ν` and `ν ★` allocation. — checked locally
3. Prove relational post-allocation `β-Λ•` lemmas. — matched and left-only checked
4. Prove one-sided and generic-cast `β-∀•` lemmas. — checked locally
5. Prove relational `β-gen•` transport. — matched body checked locally
6. Connect `β-inst` to `ν ★` and its allocation step. — checked locally
7. Prove `ξ-ν`, `blame-ν`, and store-change composition. — checked
8. Package administrative reductions into a sound simulation-up-to closure.
   — partial; the stable result, transport, coherence, frame, and prefix
   composition layers are checked.
9. Prove one-step simulation and lift it to `GradualDGG`.
   — partial; the recursive dispatcher is stated, but its current skeleton
   covers only blame and the `ν`/`ν ★` families.  The ten explicit helper
   holes and the still-unwritten dispatcher patterns are listed in the latest
   snapshot below.

## Log

### 2026-07-14

- Created this ledger.
- Began the right-only allocation audit.
- Confirmed that `⇑ᴿᵢ` and `⊑-target-lift-rightᵢ` cover the final result index,
  but a separate relation is needed for the bare target bullet before its
  reveal or widening conversion is applied.
- Added `⊑αᵀ` and strengthened the right-only `ν` and `ν ★` states with the
  intermediate post-allocation type-imprecision index.
- Proved `right-ν↑-allocation` and `right-νcast-allocation`.
- Added fresh allocation-store extension rules constrained by the existing
  store-lift witnesses.
- Proved matched and left-only allocation followed by `β-Λ•`, ending in a
  related pair after the reveal conversion.
- Lifted paired and one-sided reveal/conceal `β-∀•` facts to complete
  term-relation simulation lemmas.
- Consolidated the binder-opening mode renaming as
  `single-mode-rename-lower` in `proof.CoercionProperties`.
- Proved `open-narrowing`, `open-widening`, `open-all-narrowing`, and
  `open-all-widening`. In nominal form, the latter two establish

  \[
    c : \forall X.A \mathrel{\trianglerighteq} \forall X.B
    \Longrightarrow
    c[\alpha] : A[\alpha/X]
      \mathrel{\trianglerighteq} B[\alpha/X],
  \]

  and its widening dual.
- Proved the four generic one-sided term simulations
  `left-β-∀-narrowingᵀ`, `left-β-∀-wideningᵀ`,
  `right-β-∀-narrowingᵀ`, and `right-β-∀-wideningᵀ`.
- Proved `post-allocation-β-gen•-bare` and its cast-context lifting. The
  reduction uses

  \[
    ((\uparrow V)\langle
       \mathsf{gen}\;(\uparrow A)\;(\uparrow c)\rangle)\,\bullet
    \longrightarrow
    (\uparrow V)\langle c\rangle,
  \]

  where opening the shifted coercion cancels back to `c`.
- Proved `allocate-gen-narrowing`, which transports the original `gen` body
  narrowing under the exact fresh store extension.
- Proved `matched-gen-left-incompatible` and
  `matched-gen-right-incompatible`. A one-sided `gen` body rule would require
  `0 ˣ⊑★`, but matched allocation provides only `0 ˣ⊑ˣ 0`.
- Added the paired `gen-down⊑gen-downᵀ` repair to the quotiented down-cast
  judgment and proved `matched-post-allocation-β-genᵀ`. The final body casts
  remain paired and quotiented, so no false one-sided star assumption is
  introduced.
- Proved `matched-β-inst-νcast-allocation`,
  `left-β-inst-νcast-allocation`, and
  `right-β-inst-νcast-allocation`. These package the complete administrative
  boundary

  \[
    V\langle\mathsf{inst}\;B\;s\rangle
      \longrightarrow \nu\star.V\;s
      \longrightarrow
      ((\uparrow V)\,\bullet)\langle s\rangle,
  \]

  including the `keep` then `bind ★` store-change trace and the appropriate
  matched, left-only, or right-only post-allocation relation.
- Added store-extension monotonicity for `RevealConversion` and
  `ConcealConversion`. This preserves the exact single-seal provenance while
  permitting allocation to add a fresh store entry.
- Proved `post-allocation-polymorphic-value-step` and the matched/one-sided
  relational corollaries. If a closed value has type `∀X.A`, then it has
  exactly one of the shapes

  \[
    \Lambda X.V,
    \qquad V\langle\forall X.c\rangle,
    \qquad V\langle\mathsf{gen}\;A\;c\rangle,
  \]

  and its post-allocation runtime bullet takes the corresponding `β-Λ•`,
  `β-∀•`, or `β-gen•` step. The latter two use shift/open cancellation, so
  the reduct contains the original body coercion `c`.
- Proved `open-allocated-paired-all-conversion`. A paired reveal or conceal
  between outer `∀` coercions opens after allocation to a paired conversion
  between their bodies. Its matched seal entry is transported to the shifted
  store tail, while the newly allocated entry remains independent.
- Proved `matched-post-allocation-β-∀-conversionᵀ`. In nominal form, from a
  bare relation `V ⊑ V′` and a paired outer conversion, it reconstructs

  \[
    (\uparrow(V\langle\forall X.c\rangle))\,\bullet
      \longrightarrow ((\uparrow V)\,\bullet)\langle c\rangle
      \mathrel{\sqsubseteq}
      ((\uparrow V')\,\bullet)\langle c'\rangle
      \longleftarrow
    (\uparrow(V'\langle\forall X.c'\rangle))\,\bullet.
  \]

  This single theorem covers both paired reveal and paired conceal.
- Completed the generic one-sided cast compatibility audit. In addition to
  `matched-gen-left-incompatible` and `matched-gen-right-incompatible`, proved
  `matched-inst-left-incompatible` and `matched-inst-right-incompatible`.
  Hence none of the four generic one-sided reconstruction rules can cross a
  matched fresh-seal boundary:

  \[
    X\sqsubseteq X
      \not\Longrightarrow X\sqsubseteq\star.
  \]

  Narrowing under a freshly opened `∀` uses `genᵈ`; widening uses `instᵈ`.
  Both modes permit a star-changing cast at the fresh name, so their generic
  compatibility predicates demand the unavailable `X ˣ⊑★` assumption.
  This rules out a mutual structural lifting theorem for the current term
  relation: at least the generic cast branches cannot be reconstructed with
  their original one-sided constructors.
- Proved outer-`∀` shape preservation and reflection for permutation
  equivalence in `proof.ForallPermutationProperties`:

  \[
    \forall X.A \approx_{\forall} B
      \Longrightarrow
      \exists C.\;B=\forall X.C,
    \qquad
    A \approx_{\forall} \forall X.B
      \Longrightarrow
      \exists C.\;A=\forall X.C.
  \]

  Symmetry and transitivity are handled mutually; the adjacent-binder swap
  case preserves the outer binder explicitly.
- Proved `⊑ᵖ-all-representatives` and `⊑ᵖ-all-view`. Thus an index

  \[
    \forall X.A \sqsubseteq^{p} \forall X.B
  \]

  exposes polymorphic representatives `∀X.C` and `∀X.D`, an ordinary
  imprecision derivation between them, and the surrounding permutation
  equivalences. The ordinary derivation has exactly two possible shapes:

  \[
    \frac{C\sqsubseteq D}
         {\forall X.C\sqsubseteq\forall X.D}
    \qquad\text{or}\qquad
    \frac{C\sqsubseteq\forall X.D}
         {\forall X.C\sqsubseteq\forall X.D}\;\nu.
  \]

  The mechanized `AllImprecisionView` records this paired-versus-source-only
  split without assuming that quotienting makes every outer binder matched.
- Audited the adjacent-binder swap operationally. Opening only the first
  binder does not preserve `≈∀`, because the two representatives instantiate
  different logical binders first. The sound simulation unit for a direct
  swap is therefore two allocations. If the newest names are `α₀` and `β₀`
  and the preceding names are `α₁` and `β₁`, the required context is

  \[
    \alpha_0\sqsubseteq\beta_1,
    \qquad
    \alpha_1\sqsubseteq\beta_0,
  \]

  followed by the old assumptions shifted twice.
- Added `swapRight∀∀ᵢ` and proved `⊑-swapRight01∀∀ᵢ`. The latter
  transports an ordinary two-binder imprecision derivation by swapping only
  the target's two fresh names:

  \[
    A\sqsubseteq B
      \Longrightarrow
    A\sqsubseteq \mathsf{swap}_{01}(B)
  \]

  under the crossed context above.
- The existing `StoreImp` list could not represent this crossing: even when a
  `store-matched` entry mentioned different names, both physical-store
  projections inherited the same list order. Added correspondence-only
  `store-link` entries and the `StoreCorresponds` judgment. Physical left and
  right entries can now be ordered independently, while links record the
  crossed name relation used by paired reveal/conceal conversions.
- Added `crossedStoreⁱ`. Its checked projection equations are

  \[
  \begin{aligned}
    \mathsf{leftStore}(\rho_{\times})
      &= (\alpha_0,A_0),(\alpha_1,A_1),\mathsf{leftStore}(\rho),\\
    \mathsf{rightStore}(\rho_{\times})
      &= (\beta_0,B_0),(\beta_1,B_1),\mathsf{rightStore}(\rho).
  \end{aligned}
  \]

  Meanwhile `crossedStoreⁱ-new-old` and `crossedStoreⁱ-old-new` expose the
  crossed correspondences. Store links lift through matched, left-only, and
  right-only allocation, and paired conversions now consume
  `StoreCorresponds` rather than requiring a physically paired entry.
- Moved `swapRight∀∀ᵢ` to the shared type-imprecision context API and
  added `allocation-crossedᵀ` to the quotiented term relation. This rule is
  deliberately not arbitrary store weakening: it requires two successive
  `LiftStoreⁱ` witnesses for the old tail, adds exactly two physical entries
  to each side, and installs only the crossed links

  \[
    \alpha_{\mathsf{new}}\sqsubseteq\beta_{\mathsf{old}},
    \qquad
    \alpha_{\mathsf{old}}\sqsubseteq\beta_{\mathsf{new}}.
  \]

  Its source- and target-typing projections are checked.
- Proved `leftStoreⁱ-crossed-two-binds` and
  `rightStoreⁱ-crossed-two-binds`. If the source allocates `Aold` then
  `Anew`, while the target allocates `Bold` then `Bnew`, the final stores are

  \[
  \begin{aligned}
    \mathsf{leftStore}(\rho_\times)
      &= \mathsf{applyStores}
           [\mathsf{bind}\;Aold,\mathsf{bind}\;Anew]
           (\mathsf{leftStore}(\rho)),\\
    \mathsf{rightStore}(\rho_\times)
      &= \mathsf{applyStores}
           [\mathsf{bind}\;Bold,\mathsf{bind}\;Bnew]
           (\mathsf{rightStore}(\rho)).
  \end{aligned}
  \]

  Thus the crossed state supplies the store equalities required by the
  public DGG, rather than merely having the right list shape.
- Proved the two direct-swap administrative traces. In nominal notation, the
  left route reduces in the order

  \[
    \beta_{\mathsf{inst}};
    \mathsf{alloc}\;\alpha_1;
    \beta_{\forall\bullet};
    \beta_{\Lambda\bullet};
    \mathsf{alloc}\;\alpha_0;
    \beta_{\forall\bullet};
    \beta_{\mathsf{gen}\bullet},
  \]

  while the right route reduces in the opposite allocation order

  \[
    \mathsf{alloc}\;\beta_1;
    \beta_{\forall\bullet};
    \beta_{\mathsf{gen}\bullet};
    \beta_{\mathsf{inst}};
    \mathsf{alloc}\;\beta_0;
    \beta_{\forall\bullet};
    \beta_{\Lambda\bullet}.
  \]

  Both are seven checked small steps. Their exposed bodies are

  \[
    \uparrow W
    \qquad\text{and}\qquad
    \operatorname{rename}(\operatorname{ext}\,\uparrow)W'.
  \]
- Added the exact quotient boundary `swapRight-bodyᵀ` and proved
  `crossed-bodyᵀ`. From a body relation `W \sqsubseteq W'` below the first
  `∀`, the latter derives

  \[
    \uparrow W
      \sqsubseteq
    \operatorname{rename}(\operatorname{ext}\,\uparrow)W'
  \]

  under `swapRight∀∀ᵢ`. This is deliberately narrower than a general lifting
  theorem: it requires both store-lift witnesses and explicit typing of the
  renamed endpoints.
- Proved the two type derivations consumed by the crossed allocation:

  \[
  \begin{aligned}
    \uparrow^2 A_{\mathsf{obs}}
      &\sqsubseteq \uparrow^2 B_{\mathsf{obs}},\\
    \star &\sqsubseteq \star.
  \end{aligned}
  \]

  The first is `⊑-crossed-double-lift∀∀ᵢ`; the second is `id★`.
  `⊑-crossed-body-lift∀∀ᵢ` supplies the adjacent-binder-permuted body index.
- Proved `paired-swap-gen-inst-allocationᵀ`. It combines the two traces,
  feeds the crossed body and the two instantiation-type relations to
  `allocation-crossedᵀ`, then rebuilds the exposed paired `gen` narrowing,
  paired `inst` widening, and final paired reveal conversion over the crossed
  store.
- Proved `left-swap-reveal-conversion` and
  `right-swap-reveal-conversion`. They derive the final reveal premises from
  the original outer `ν` premises. On the left,

  \[
    s \longmapsto
    \operatorname{rename}(\operatorname{ext}\,\uparrow)s
  \]

  and the inner `★` entry is inserted second. On the right,

  \[
    s' \longmapsto \uparrow s'
  \]

  and the inner `★` entry is inserted first. The resulting conversions reveal
  `α₀` and `β₁`, respectively, so `crossedStoreⁱ-new-old` supplies their
  paired correspondence.
- Strengthened `paired-swap-gen-inst-allocationᵀ` to accept the original
  outer reveal conversions at the one-binder stores. It now performs both
  conversion transports internally before applying `conv⊑convᵀ`.
- Proved direct inversion lemmas for the paired administrative coercions:

  \[
  \begin{array}{rcl}
    \forall X.\mathsf{gen}\;A\;d
      &: & \forall X.A \;\Rrightarrow\;
           \forall X.\forall Y.D,\\
    \mathsf{gen}\;(\forall X.B)\;(\forall Y.d')
      &: & \forall X.B \;\Rrightarrow\;
           \forall Y.\forall X.D',\\
    \mathsf{inst}\;(\forall X.E)\;(\forall Y.u)
      &: & \forall Y.\forall X.D \;\Rrightarrow\;
           \forall X.E,\\
    \forall Y.(\mathsf{inst}\;E'\;u')
      &: & \forall Y.\forall X.D' \;\Rrightarrow\;
           \forall Y.E'.
  \end{array}
  \]

  Inverting their `cast-all`, `cast-gen`, and `cast-inst` premises derives

  \[
  \begin{aligned}
    d  &: \uparrow A \Rrightarrow D,
      &d' &: \operatorname{rename}(\operatorname{ext}\,\uparrow)B
              \Rrightarrow D',\\
    u  &: D \Rrightarrow
             \operatorname{rename}(\operatorname{ext}\,\uparrow)E,
      &u' &: D' \Rrightarrow \uparrow E'.
  \end{aligned}
  \]

  The derivations are then transported through the two store lifts. The left
  widening body has mode
  `extᵈ (instᵈ tag-or-idᵈ)` and uses the star at name `1`; the right
  body has mode `instᵈ (extᵈ tag-or-idᵈ)` and uses the star at name
  `0`.
- Added `crossed-up⊑upᵀ`, the ordinary term-imprecision boundary for that
  exact pair of widening modes. Its typing projections use
  `cast-ext (cast-inst cast-tag-or-id)` on the left and
  `cast-inst (cast-ext cast-tag-or-id)` on the right. This retains the seal
  permission produced by each `inst` instead of imposing the old,
  uninhabited `id-onlyᵈ` requirement on the exposed bodies.
- Strengthened `paired-swap-gen-inst-allocationᵀ` again: its four coercion
  arguments are now the original paired `∀gen`/`gen∀` narrowing and
  `inst∀`/`∀inst` widening derivations. It derives the final typings of
  `d`, `d'`, `u`, and `u'` internally before rebuilding the crossed body
  relation.
- Proved the symmetric crossed type transport
  `⊑-crossed-left-body-lift∀∀ᵢ`. If

  \[
    E \sqsubseteq E'
  \]

  below one paired binder, it derives

  \[
    \operatorname{rename}(\operatorname{ext}\,\uparrow)E
      \sqsubseteq \uparrow E'
  \]

  in `swapRight∀∀ᵢ Φ`. This is the left-renaming counterpart of
  `⊑-crossed-body-lift∀∀ᵢ`, which shifts the left endpoint and renames
  the right endpoint.
- Proved `crossed-lift-store`. From the first store lift supplied by the
  `Λ⊑Λᵀ` inversion, it constructs an existential second store and a
  `LiftStoreⁱ (swapRight∀∀ᵢ Φ)` witness. Each stored or linked
  imprecision proof is transported with
  `⊑-crossed-double-lift∀∀ᵢ`; left-only and right-only entries carry
  their twice-shifted well-formedness evidence.
- Proved `direct-swap-gen-inst-caseᵀ`. This is the integrated direct-adjacent
  simulation case. It consumes the evidence exposed by the pre-reduction
  constructor inversions:

  \[
  \begin{aligned}
    W &\sqsubseteq W',\\
    D &\sqsubseteq D' &&\text{below two paired binders},\\
    E &\sqsubseteq E' &&\text{below one paired binder},\\
    F &\sqsubseteq F',
  \end{aligned}
  \]

  together with the observer relation, four full administrative coercion
  typings, and two outer reveal conversions. It constructs `ρ₂`, the crossed
  quotient index, the crossed `E` and `F` indices, the source's seven-step
  trace, and the final Nu-term relation. Thus a caller no longer supplies the
  hand-built `ρ₂`, `qD×`, `pE×`, or `pF×` setup.
- Proved `right-swap-allocation-step-tail` and changed the two direct-swap
  wrappers to expose the target trace in the form needed by forward
  simulation. In nominal notation the target side is now factored as

  \[
    M' \longrightarrow_{\operatorname{bind} B_{\mathit{obs}}} N'
       \longrightarrow^{6} P'.
  \]

  The first arrow is exactly the target step being simulated. The six-step
  suffix is administrative closure through `β-∀•`, `β-gen•`, `β-inst`, the
  inner `ν` allocation, the second `β-∀•`, and `β-Λ•`. The final crossed
  relation is only required at `P'`, not at the transient state `N'`.
- Added `nested-Λ-no•` and `nested-Λ-runtime-no•`, then moved
  `direct-swap-gen-inst-caseᵀ` to the actual one-step premises. It now
  consumes source `RuntimeOK` for the whole `ν` term and target `No•` for the
  value allocated by the target `ν` step. It derives `No• W` and `No• W'`
  internally before building the two administrative traces.
- Audited constructor inversion for the direct quotient case. Exact term shape
  does not determine the term-imprecision constructor: generic left- and
  right-cast constructors overlap the paired `up⊑upᵀ` shape. Consequently,
  the direct quotient witness must be dispatched while recursing on the
  imprecision derivation; a standalone inversion function on only the two term
  indices would be false.
- Defined `WeakOneStepResult`, the general result of simulating one target
  store-changing step. Given an observed target change `χ`, it records source
  changes `χ̄`, target administrative changes `ψ̄`, final terms `N` and
  `N'`, and a final store-imprecision witness `ρ'` such that

  \[
  \begin{aligned}
    M &\longrightarrow^{\bar\chi} N,\\
    M'_1 &\longrightarrow^{\bar\psi} N',\\
    \operatorname{leftStore}(\rho')
      &= \operatorname{applyStores}(\bar\chi,
           \operatorname{leftStore}(\rho)),\\
    \operatorname{rightStore}(\rho')
      &= \operatorname{applyStores}(\bar\psi,
           \operatorname{applyStore}(\chi,
             \operatorname{rightStore}(\rho))),\\
    N &\sqsubseteq N'.
  \end{aligned}
  \]

  The final endpoint types carry equations to
  `applyTys χ̄ A` and `applyTys ψ̄ (applyTy χ B)`. This admits the
  nominal crossed endpoint
  `renameᵗ (extᵗ suc) (⇑ᵗ F)` while recording that it equals the
  two-step store-change action on `F`.
- Proved `weak-one-step-direct-quotientᵀ`, the direct quotient clause for
  derivation recursion. It packages `direct-swap-gen-inst-caseᵀ` as a
  `WeakOneStepResult`, including both store projection equations from
  `leftStoreⁱ-crossed-two-binds` and `rightStoreⁱ-crossed-two-binds`. Its
  quotient premise includes an equality to the literal direct constructor

  \[
    q_D = \mathsf{quotient}^{p}
      \;\mathsf{refl}
      \;(\forall^{i}(\forall^{i}p_D))
      \;\mathsf{swap},
  \]

  so this clause does not accidentally cover a transitive quotient witness.
- Added the four generic `β-∀•` base and finishing clauses for weak
  one-step simulation. The right clauses consume the observed target step
  and return zero source steps; the left clauses consume the resulting body
  relation and add the source catch-up step. All store projections are
  definitional because every step has change `keep`.
- Proved all four compositions with the left generic cast outermost:

  \[
    \begin{array}{c|cc}
      & \text{target narrowing} & \text{target widening} \\
      \hline
      \text{source narrowing} & \checkmark & \checkmark \\
      \text{source widening} & \checkmark & \checkmark
    \end{array}
  \]

  These are
  `weak-one-step-generic-β-∀-left-outer-narrowing-narrowingᵀ`,
  `weak-one-step-generic-β-∀-left-outer-narrowing-wideningᵀ`,
  `weak-one-step-generic-β-∀-left-outer-widening-narrowingᵀ`, and
  `weak-one-step-generic-β-∀-left-outer-widening-wideningᵀ`.
- Proved the symmetric four compositions with the right generic cast
  outermost. The helper `weak-one-step-keep-source-catchupᵀ` packages the
  already-derived source `keep` step after the right constructor reconstructs
  the final relation. Thus exact term shape no longer leaves an uncovered
  generic narrowing/widening order at this `β-∀•` boundary.
- Generalized `WeakOneStepResult` so its final left and right type contexts
  are explicit, with equations to the corresponding `applyTyCtxs` actions.
  This matches the existing treatment of endpoint types and avoids dependent
  transport through `StoreImp` when traces are concatenated.
- Proved `weak-one-step-composeᵀ`. Given consecutive weak results separated
  by the next observed target step, it produces one weak result whose traces
  are

  \[
    \bar\chi_1 \mathbin{+\!+} \bar\chi_2
    \qquad\text{and}\qquad
    \bar\psi_1 \mathbin{+\!+}
      (\chi_2 :: \bar\psi_2).
  \]

  Its context, endpoint-type, and store projection equations follow from
  `applyTyCtxs-++`, `applyTys-++`, and `applyStores-++`. Its source and target
  traces use `↠-trans`. No postulate or heterogeneous transport is needed.
- Proved `weak-one-step-relatedᵀ`, the neutral result with zero source and
  target-tail steps when the post-step terms are already related.
- Added the symmetric crossed-widening constructor
  `crossed-left-up⊑upᵀ`. It admits the mode pair forced by the reverse
  adjacent swap:

  \[
    \mathsf{inst}(\mathsf{ext}(\mathsf{tag\text{-}or\text{-}id)) )
    \quad\text{and}\quad
    \mathsf{ext}(\mathsf{inst}(\mathsf{tag\text{-}or\text{-}id)) ).
  \]

  Its source and target typing projections use the corresponding nested cast
  modes. This is a genuine relation clause: the existing crossed widening
  admits only the opposite mode order.
- Proved the reverse crossed body and administrative transports:
  `crossed-left-bodyᵀ`, the four mirrored `gen`/`inst` coercion-body lemmas,
  and the two mirrored reveal-conversion lemmas. The final body and reveal
  shapes are

  \[
    \operatorname{rename}(\operatorname{ext}\,\uparrow)W
      \sqsubseteq \uparrow W',
    \qquad
    \uparrow s
      \quad\text{and}\quad
    \operatorname{rename}(\operatorname{ext}\,\uparrow)s'.
  \]
- Proved `paired-reverse-swap-gen-inst-allocationᵀ`. It derives the opposite
  allocation traces directly from the paired administrative forms:

  \[
    \begin{aligned}
      \text{source:}&\quad A_{\mathit{obs}}\ ;\ \star,\\
      \text{target:}&\quad \star\ ;\ B_{\mathit{obs}}.
    \end{aligned}
  \]

  The target's first observed step is `keep`, exposing the inner `ν ★`; its
  tail then performs the two allocations. The observer conversion uses the
  old--new crossed-store correspondence, while the fresh `★` cells use the
  new--old identity correspondence.
- Proved `direct-reverse-swap-gen-inst-caseᵀ` for the literal quotient
  witness

  \[
    q_D = \mathsf{quotient}^{p}
      \;(\mathsf{sym}\;\mathsf{swap})
      \;(\forall^{i}(\forall^{i}p_D))
      \;\mathsf{refl}.
  \]

  It derives the crossed inner quotient by swapping the source index and
  derives both outer crossed endpoints from the original nominal
  imprecision premises.
- Proved `weak-one-step-reverse-direct-quotientᵀ`. Its final endpoint is

  \[
    \uparrow\uparrow F
      \sqsubseteq
    \operatorname{rename}(\operatorname{ext}\,\uparrow)(\uparrow F'),
  \]

  and the right endpoint equation is exactly
  `renameᵗ-ext-suc-comm suc F′`. Both store projections are discharged by
  the existing two-bind crossed-store lemmas instantiated in the reverse
  order.
- Proved `direct-swap-residualᵖ` and `reverse-swap-residualᵖ`. These remove
  the former assumption that the permutation remaining after the adjacent
  swap is reflexive. In the direct orientation, if

  \[
    D \sqsubseteq E
    \qquad\text{and}\qquad
    \mathsf{swap}_{01}(E) \approx_{\forall} T,
  \]

  then the crossed context contains

  \[
    D \sqsubseteq^{p} T.
  \]

  The reverse lemma starts from
  `S ≈∀ renameᵗ swap01ᵗ D` and derives `S ⊑ᵖ E`. Thus the local
  operational swap preserves, rather than discards, the residual quotient
  proof.
- Added `direct-swap-residual-outerᵖ` and
  `reverse-swap-residual-outerᵖ`. They construct the exact outer quotient
  indices produced by the route-permutation proof:

  \[
    \mathsf{trans}\;\mathsf{swap}
      \;(\forall(\forall\,r))
    \qquad\text{or its symmetric orientation}.
  \]

  These lemmas make explicit that `≈∀-trans` here is proof structure for one
  adjacent operational swap followed by a residual congruence; it is not an
  additional runtime step.
- Generalized `direct-swap-gen-inst-caseᵀ`,
  `direct-reverse-swap-gen-inst-caseᵀ`, and both weak one-step wrappers to
  consume these residual equivalences. The resulting inner
  `gen-down⊑gen-downᵀ` derivation retains an arbitrary quotiented relation,
  so later simulation recursion can expose the next local permutation only
  when another reduction reaches it.
- Packaged the synchronized reveal-allocation lemma as
  `weak-one-step-matched-ν↑ᵀ`. For an observed target allocation
  `bind A′`, it records the source allocation `bind A`, the matched fresh
  store entry, the lifted endpoint relation

  \[
    \uparrow B \sqsubseteq \uparrow B',
  \]

  and both store projections as consequences of the supplied store lift.
- Packaged the right-only reveal allocation as
  `weak-one-step-right-ν↑ᵀ`. It uses zero source steps and returns the repaired
  right-lifted context `⇑ᴿᵢ Φ`, a right-only fresh-store entry, and
  `⊑-target-lift-rightᵢ pB`.
- Added the analogous `ν ★` clauses
  `weak-one-step-matched-νcastᵀ` and
  `weak-one-step-right-νcastᵀ`. These are the allocation-facing recursion
  interfaces reached after `β-inst`; they preserve the instantiation
  widening evidence already reconstructed by `matched-νcast-allocation` and
  `right-νcast-allocation`.
- Strengthened `WeakOneStepResult` with two world-action laws. For every
  observer relation (C \sqsubseteq D), `transportType` returns

  \[
    \operatorname{applyTys}(\bar\chi,C)
      \sqsubseteq
    \operatorname{applyTys}
      (\bar\psi,\operatorname{applyTy}(\chi,D)).
  \]

  For every body relation under a nominal type binder,
  `transportAllBody` returns

  \[
    \operatorname{applyTysUnder}(\bar\chi,C)
      \sqsubseteq
    \operatorname{applyTysUnder}
      (\bar\psi,\operatorname{applyTyUnder}(\chi,D)).
  \]

  The latter is not derivable merely by inverting the former: a relation
  whose two endpoints are syntactic `∀` types may be headed by the
  source-only `ν` rule rather than by `∀ⁱ`.
- Proved the matched, right-only, crossed-double-allocation, neutral, and
  compositional instances of both transport laws. The crossed body theorem
  preserves the static binder at index zero while shifting the two runtime
  allocations beneath it. The composition proof uses the new general lemma
  `applyTysUnderTyBinders-++`.
- Proved `lift-store-result`: every final store-imprecision witness can be
  lifted under a fresh paired nominal binder. Each stored relation is mapped
  by `⊑-lift∀ᵢ`; left-only and right-only entries use ordinary
  well-formed type renaming.
- Defined `WeakOneStepAllResult`, the recursive result interface for an input
  relation headed by `∀ⁱ`. Besides the general weak result, it records the
  canonical final body relation

  \[
    \operatorname{sourceResult}
      \sqsubseteq
    \operatorname{targetResult}
      :
    \forall\operatorname{applyTysUnder}(\bar\chi,C)
      \sqsubseteq
    \forall\operatorname{applyTysUnder}
      (\bar\psi,\operatorname{applyTyUnder}(\chi,C'))
  \]

  with proof index
  `∀ⁱ (transportAllBody weakResult q)`. The neutral constructor
  `weak-one-step-all-relatedᵀ` is checked.
- Proved `weak-one-step-matched-ν-frameᵀ`. Given a recursive
  `WeakOneStepAllResult`, it lifts both traces through the whole outer term,
  transports the paired single-seal reveal conversions across all source and
  target-tail store changes, constructs the final lifted store, and rebuilds
  the outer `ν⊑νᵀ` derivation.
- Proved `apply-widen-inst-under-ty-binders` and
  `weak-one-step-matched-νcast-frameᵀ`. The former iterates the existing
  one-change `inst` widening preservation theorem, retaining the changing
  cast mode and seal-store invariant. The latter uses it on both sides and
  rebuilds the outer `νcast⊑νcastᵀ` derivation. Thus both matched outer
  frame forms now use the same canonical `∀ⁱ` recursive interface.
- Validated the focused modules and the aggregate development with
  `agda --no-allow-unsolved-metas -v0 All.agda`.

### 2026-07-15

- Proved `weak-result-source-all`. A general recursive result whose source
  endpoint initially has type `∀X.C` can be normalized to the explicit final
  source type

  \[
    \forall X.\operatorname{applyUnder}(\bar\chi,C).
  \]

  This does not invert its term-imprecision derivation or assume that its
  target endpoint is polymorphic.
- Proved `lift-left-store-result` and the source-only outer frame lemmas
  `weak-one-step-source-ν-frameᵀ` and
  `weak-one-step-source-νcast-frameᵀ`. In nominal form, the ordinary frame
  transports

  \[
    s : C \mathrel{\uparrow}
      (\uparrow B)
  \]

  through every source allocation, lifts only the source store and context,
  and reconstructs `ν⊑ᵀ`. The `ν ★` frame transports the corresponding
  instantiation widening while preserving `CastMode` and `SealModeStore★`,
  then reconstructs `νcast⊑ᵀ`.
- Added `applyTy-∀`, which states

  \[
    \operatorname{applyTy}(\chi,\forall X.C)
      = \forall X.\operatorname{applyUnder}(\chi,C),
  \]

  and used it to prove `weak-result-target-all`, the dual endpoint
  normalization for a recursive result whose target is polymorphic.
- Strengthened `WeakOneStepResult` with `transportRightBody`. Besides the
  closed endpoint and paired-binder actions, every result now transports the
  target-only crossed premise

  \[
    \Uparrow_R\Phi \mid \Delta_L
      \vdash B \sqsubseteq C' \dashv \Delta_R,X
  \]

  to

  \[
    \Uparrow_R\Phi_f \mid \Delta_{L,f}
      \vdash
      \operatorname{applyTys}(\bar\chi,B)
      \sqsubseteq
      \operatorname{applyUnder}
        (\bar\psi,\operatorname{applyUnder}(\chi,C'))
      \dashv \Delta_{R,f},X.
  \]

  This premise is not derivable from the closed endpoint relation: it is the
  separate invariant already required by `⊑νᵀ` and `⊑νcastᵀ`.
- Proved `lift-right-store-result` and both target-only frame lemmas
  `weak-one-step-target-ν-frameᵀ` and
  `weak-one-step-target-νcast-frameᵀ`. They transport only the target reveal
  or instantiation-widening evidence, lift only the target store and context,
  and use `transportRightBody` to reconstruct the outer relation.
- Proved the three allocation actions on the target-only crossed premise:
  `⊑-lift-under-rightᵢ`, `⊑-target-lift-under-rightᵢ`, and
  `⊑-crossed-double-lift-under-rightᵢ`. They respectively transport it
  through a matched allocation, a target-only allocation, and the two
  allocations whose target order is crossed. In every case the nominal
  binder remains at index zero, so the target body is renamed by
  `extᵗ suc`, not by `suc`.
- Installed `transportRightBody` in every existing `WeakOneStepResult`
  constructor. Neutral clauses use identity; outer frames forward the
  recursive action; matched, right-only, and crossed allocations use the
  three laws above. `weak-one-step-compose-right-body` proves that the action
  is closed under simulation-up-to composition. The temporary
  `WeakOneStepRightAllResult` wrapper was deleted after this generalization.
- Defined `WeakOneStepOutcome`. A target step produces either a related
  `WeakOneStepResult` together with its `WeakOneStepTransport`, or evidence
  that the more-precise source reduces to `blame`. A target reduction to
  blame is not by itself a simulation outcome.
- Proved `ν-blame-tail` and the three outcome maps
  `weak-outcome-map-source`, `weak-outcome-map-target-ν`, and
  `weak-all-outcome-map-target-ν`. Their six concrete corollaries cover
  ordinary and `★` frames in matched, source-only, and target-only
  orientations. Matched and source-only frames lift source blame through the
  whole source `ν` term; target-only frames preserve source-blame evidence
  unchanged.
- Added `WeakOneStepAllOutcome`, which retains the canonical `∀ⁱ` result in
  the related branch and shares the source-blame branch with the general
  outcome.
- Strictly validated the focused simulation module and the aggregate
  development with no unsolved metas.
- Audited the hypotheses needed by the total derivation-recursive dispatcher.
  An arbitrary `StoreImp` does not imply store uniqueness, so the eventual
  theorem should take well-formedness of the two projected stores as explicit
  hypotheses. More importantly, the current matched `ν ★` allocation lemma is
  not yet a usable leaf: it assumes

  \[
    \mathsf{RightCastCtxCompatible}
      (\mathsf{inst}^{d}\,\mu')
      (\mathsf{suc}\,\Delta_R)
      ((0\mathbin{\smash{\sqsubseteq}}0)::\Uparrow\Phi),
  \]

  while `matched-inst-right-incompatible` proves that exact proposition
  impossible. The analogous right-only `ν ★` leaf also asks for a global
  compatibility premise that is not carried by `⊑νcastᵀ`. Consequently the
  total dispatcher cannot obtain either premise by inversion of its input
  derivation. No term- or type-imprecision definition was changed during this
  audit.
- Audited the smaller alternative of loosening the existing one-layer cast
  rules instead of adding allocation constructors whose conclusions mention
  both runtime bullet and cast nodes. For the quotiented relation,
  `⊑cast⊑ᵀ` already takes its final type-imprecision derivation explicitly;
  its `StoreDetWf` and `RightCastCtxCompatible` premises are therefore not
  used by either typing projection. Removing those two premises repairs the
  right-only `ν ★` state. The matched state cannot be obtained by merely
  nesting the two one-sided rules: after applying either widening first, the
  required intermediate type relation need not exist. It can instead use the
  existing one-layer `conv⊑convᵀ` rule if that rule is broadened from paired
  reveal/conceal evidence to the disjoint alternative of two well-typed
  widening coercions. This proposal changes no type-imprecision rule and
  subsumes the two previously proposed multi-node administrative
  constructors. It was subsequently approved and implemented below.

### 2026-07-16

- Defined the proof-relevant invariant `PairedCast`. It has two cases:
  `paired-conversion` embeds the existing exact paired reveal/conceal
  judgment, while `paired-widening` records two `CastMode` witnesses, their
  seal-store invariants, and the two widening typings. The existing
  `conv⊑convᵀ` term rule now consumes `PairedCast`. Thus both alternatives
  still introduce exactly one cast node on each side and share one simulation
  case at the term-relation level.
- Loosened the quotiented `⊑cast⊑ᵀ` rule. Before the change it required
  `StoreDetWf` and `RightCastCtxCompatible` in addition to the target
  widening and an explicit final type-imprecision derivation. After the
  change it retains `CastMode`, `SealModeStore★`, the target widening typing,
  the inner term relation, and the explicit final type relation, but removes
  the two premises used only by the alternative route that derives that final
  type relation. The non-quotiented rule in `NuTermImprecision` is unchanged.
- Reproved `matched-νcast-allocation` using one `paired-widening` above the
  existing bare-bullet `α⊑αᵀ` relation. There is no intermediate one-sided
  type relation and no appeal to the impossible matched-inst compatibility
  predicate.
- Reproved `right-νcast-allocation` by applying the loosened `⊑cast⊑ᵀ`
  directly to `⊑αᵀ` and its already-recorded crossed body relation. Removed
  the false/unavailable compatibility and determinacy hypotheses from both
  weak one-step allocation interfaces and from the matched and right-only
  `β-inst` administrative traces.
- Strictly validated `QuotientedTermImprecision.agda`,
  `proof/NuImprecisionSimulation.agda`, and the aggregate `All.agda` with no
  unsolved metas.
- Factored source catchup into two proof-level invariants, without adding a
  term-imprecision rule. For a weak result (R), `LeftSilentInvariant R`
  states

  \[
    \overline\psi = \epsilon
    \qquad\text{and}\qquad
    \operatorname{target}(R) = V'.
  \]

  `LeftCatchupInvariant R` adds the exhaustive final-source classification

  \[
    (\operatorname{Value}(W) \land \operatorname{No\bullet}(W))
      \;\lor\; W = \mathsf{blame}.
  \]

  The `No•` component is essential: a caught-up value can be supplied
  directly to the operational `ν-step` rule. `LeftCatchupAllResult` combines
  the same invariant with `WeakOneStepAllResult`, retaining the canonical
  body relation for a nominal universal type
  `∀X.C ⊑ ∀X.C'`.
- Proved `weak-one-step-prepend-left-silentᵀ`. If a source-only prefix leaves
  the target unchanged and a second weak result simulates the observed target
  step, then their composition observes the second target change, concatenates
  only the source histories, and retains only the second target tail. This is
  the correct algebra for source catchup before a target step; ordinary weak
  composition would incorrectly keep the prefix's observed `keep`.
- Proved result-indexed transport for both allocation interfaces:
  `weak-result-source-reveal` and `weak-result-target-reveal` transport the
  two single-seal reveal conversions to the caught-up world, while
  `weak-result-source-widen-inst` and `weak-result-target-widen-inst` transport
  the corresponding `inst` widenings together with `CastMode` and
  `SealModeStore★`.
- Proved that matched ordinary and `★` frames preserve the silent-prefix
  invariant. Then proved the value branches
  `weak-one-step-matched-ν↑-value-catchupᵀ` and
  `weak-one-step-matched-νcast-value-catchupᵀ`. In nominal form, both have the
  same proof shape:

  \[
    N \longrightarrow^{\!*}_{L} W
      \quad W \sqsubseteq V'
      \quad \operatorname{Value}(W),\operatorname{No\bullet}(W)
  \]

  is first lifted through the whole `ν` frame, then followed by the existing
  synchronized allocation leaf. The two lemmas differ only in whether the
  transported boundary evidence is a pair of reveals or a pair of
  instantiation widenings.
- Proved `weak-one-step-source-blame-right-allocationᵀ`. It handles the
  common crossed outcome after catchup:

  \[
    \nu X.\mathsf{blame}
      \longrightarrow \mathsf{blame}
    \qquad
    \nu Y.V'
      \longrightarrow
      ((\uparrow V')\,\bullet)\langle s'\rangle.
  \]

  The proof uses target preservation for the observed allocation and then
  applies `blame⊑ᵀ` at the right-lifted type relation. Consequently it is
  independent of the target boundary coercion's reveal/widening shape. The
  only additional theorem-level premise is the right projected store's
  `StoreWf`, already identified as necessary for the total dispatcher.
- Proved both blame branches after canonical-`∀` catchup and packaged the
  exhaustive splits as `weak-one-step-matched-ν↑-catchupᵀ` and
  `weak-one-step-matched-νcast-catchupᵀ`. Each dispatcher inspects only the
  shared final-source invariant:

  \[
    (\operatorname{Value}(W)\land\operatorname{No\bullet}(W))
      \lor W=\mathsf{blame}.
  \]

  Thus matched allocation now contributes one recursive clause per existing
  outer term-imprecision constructor, not separate value and blame clauses.
- Strictly validated the focused simulation module and the aggregate
  `All.agda` development with `--no-allow-unsolved-metas` after adding the
  catchup algebra and all four matched allocation outcome proofs.
- Proved the constructor-independent terminal clauses
  `left-catchup-all-valueᵀ` and `left-catchup-all-blameᵀ`. Thus a source
  term already at a value or blame closes without inspecting how its
  imprecision derivation was built. The value clause derives `No•` from
  `RuntimeOK`, so the terminal invariant is not duplicated across term
  constructors.
- Proved `left-catchup-all-keep-stepᵀ` and the recursive algebra
  `left-catchup-all-prepend-keepᵀ`. In nominal form, if

  \[
    M \longrightarrow_{\mathsf{keep}} N,
    \qquad
    N \sqsubseteq V',
    \qquad
    N \longrightarrow_L^{\!*} W \sqsubseteq V',
  \]

  then the combined catchup is

  \[
    M \longrightarrow_{\mathsf{keep}}
      N \longrightarrow_L^{\!*} W \sqsubseteq V'.
  \]

  The target remains unchanged, and only the source trace is extended.
  This one lemma is the shared recursion step for `β-Λ•`, `β-∀•`, and
  `β-gen•`; no term-imprecision constructor is added.
- Proved the direct `β-Λ•` terminal leaf and the stronger
  `left-catchup-all-α-Λᵀ` clause. The latter handles the fact that the
  allocation witness carried by the outer `α⊑ᵀ` state and the lift witness
  carried by the inner `Λ⊑ᵀ` state may produce different proof-relevant
  `StoreImp` lists. No equality between those lists is required. Both lifts
  have the same left and right runtime-store projections, so the weak result
  chooses the inner lift for the final body relation and discharges the store
  equations by

  \[
    \operatorname{leftStore}(\rho_b)
      = \uparrow\operatorname{leftStore}(\rho)
      = \operatorname{leftStore}(\rho_a),
    \qquad
    \operatorname{rightStore}(\rho_b)
      = \operatorname{rightStore}(\rho)
      = \operatorname{rightStore}(\rho_a).
  \]

  This is the minimal coherence invariant needed at the direct
  `α/Λ` boundary; strengthening the term relation with equality of lift
  witnesses would be unnecessary.
- Audited two attempted direct coverage splits for the active-bullet case.
  Agda expands the hidden indexed cases for more than a minute even when the
  source is fixed to `(\uparrow L)\,\bullet`. The probes were removed. The
  checked proof instead uses explicit clauses for the three canonical
  polymorphic value shapes and composes them with the shared `keep` algebra.
- Factored `left-allocated-bulletᵀ`. From a source-only universal relation

  \[
    V \sqsubseteq V' : \forall X.A \sqsubseteq B'
  \]

  and the chosen left-allocation lift, it reconstructs

  \[
    (\uparrow V)\,\bullet \sqsubseteq V' : A \sqsubseteq B'
  \]

  together with the two endpoint typings under the allocated store. Both
  one-layer `∀`-cast catchup clauses reuse this fact rather than rebuilding
  the `α⊑ᵀ` state independently.
- Proved `open-allocated-left-all-reveal` and
  `open-allocated-left-all-conceal`. They open exactly one outer universal
  conversion after source-only allocation, transport the shifted old store
  through `LiftLeftStoreⁱ`, and weaken it with the fresh stored type. These
  are the single-sided counterparts of the earlier paired conversion lemma;
  they preserve the exact reveal/conceal shape.
- Proved the recursive reveal and conceal clauses
  `left-catchup-all-α-∀-revealᵀ` and
  `left-catchup-all-α-∀-concealᵀ`. Both have the same nominal diagram:

      (\uparrow(V⟨∀X.c⟩)) •     ⊑     V'
                 |
                 | one source `keep` step
                 v
        ((\uparrow V) •)⟨c⟩       ⊑     V'
                 |
                 | recursive catchup
                 v
                 W                  ⊑     V'

  The first horizontal relation is rebuilt by `left-allocated-bulletᵀ`
  followed by the existing one-sided conversion rule. The second vertical
  segment is composed by `left-catchup-all-prepend-keepᵀ`. Thus the two
  term-relation constructors contribute two expected simulation clauses, but
  no additional term-relation rule.
- Proved `allocate-all-narrowing` and `allocate-all-widening`. They expose the
  body of a generic outer `∀` cast under one fresh source allocation while
  preserving the extended cast mode. Proved `allocated-left-seal★` once for
  the corresponding seal-store invariant.
- Proved `left-catchup-all-α-∀-wideningᵀ`. It reconstructs the bare bullet
  with `left-allocated-bulletᵀ`, applies the existing `cast⊑⊑ᵀ` rule to the
  allocated body widening, and uses the shared `keep`-prepend algebra. Thus
  generic widening needs no new term relation and no store determinacy.
- Proved the focused impossibility fact
  `fresh-shifted-var-store-not-det`:

  \[
    \neg\operatorname{StoreDetWf}
      \bigl(2,[(0,\alpha_1)]\bigr).
  \]

  Here `α₁` is the shifted form of the open type variable `α₀`. The
  `wfOlder` field would require `α₁` to be well formed at type context
  length zero. Consequently `StoreDetWf` cannot in general be transported
  through ordinary source-only allocation, even though the allocated store
  is valid for term typing.

### Approved minimal definition change

The generic narrowing catchup clause reaches the same post-step shape as the
checked widening clause, but the current quotiented `cast⊒⊑ᵀ` constructor
requires `StoreDetWf` and `LeftCastCtxCompatible` in order to derive its final
type-imprecision index internally. The impossibility lemma above rules out
obtaining the determinacy premise from the allocation invariant in general.

The smallest proposed repair is to make the quotiented narrowing constructor
parallel to the already-loosened widening constructor. Before:

\[
\begin{aligned}
  &\operatorname{CastMode}(\mu),\quad
    \operatorname{StoreDetWf}(\Sigma_L),\quad
    \operatorname{SealModeStore}_\star(\mu,\Sigma_L),\\
  &\operatorname{LeftCastCtxCompatible}(\mu,\Phi),\quad
    c : A \mathrel{\trianglerighteq} B,\quad
    M \sqsubseteq M' : A \sqsubseteq B'\\
  &\hspace{2em}\Longrightarrow
    M\langle c\rangle \sqsubseteq M'
      : B \sqsubseteq B'
      \quad\text{at the internally derived index.}
\end{aligned}
\]

After:

\[
\begin{aligned}
  &\operatorname{CastMode}(\mu),\quad
    \operatorname{SealModeStore}_\star(\mu,\Sigma_L),\quad
    c : A \mathrel{\trianglerighteq} B,\\
  &M \sqsubseteq M' : A \sqsubseteq B',\quad
    q : B \sqsubseteq B'\\
  &\hspace{2em}\Longrightarrow
    M\langle c\rangle \sqsubseteq M' : B \sqsubseteq B'
      \quad\text{at }q.
\end{aligned}
\]

The quotiented `cast⊒⊑idᵀ` constructor is therefore redundant and has been
removed, reducing rather than increasing the simulation cases. The
non-quotiented `NuTermImprecision` definition remains unchanged. The user
approved this smaller route, and the change above is now implemented.

- Audited the remaining canonical `gen` value shape

  \[
    (\uparrow(V\langle\mathsf{gen}\;A\;c\rangle))\,\bullet
      \longrightarrow_{\mathsf{keep}}
    (\uparrow V)\langle c\rangle.
  \]

  In the ordinary one-sided term judgment, a single outer `gen` cast can only
  be introduced by the generic source-narrowing constructor (the quotiented
  `gen-down⊑gen-downᵀ` rule applies to paired downcasts underneath an
  additional upcast). Therefore this case reaches exactly the same
  `StoreDetWf` obstruction as generic outer-`∀` narrowing; it is not a
  separate reason to add a term rule. Once the pending narrowing constructor
  is loosened, the `gen` clause can use `allocate-gen-narrowing` and finish at
  the already-value-shaped reduct.
- Audited the proof-only allocation wrappers before beginning the total
  dispatcher. `allocation-matchedᵀ`, `allocation-leftᵀ`, and the crossed
  wrappers are currently constructed only by the simulation lemmas, not by
  compilation of initial terms. A later target step may nevertheless receive
  one of these derivations, so the total theorem still needs naturality of a
  weak result under the corresponding stored world extension. This is a
  separate recursive-world obligation; it does not repair or weaken the
  generic narrowing premise and does not justify another term constructor.

### Next boundary

Both orientations of the adjacent-swap quotient branch and both orders of
generic `β-∀•` casts now return the same `WeakOneStepResult`. The generic
overlap has eight checked cases:

\[
  2\ \text{constructor orders}
    \times 2\ \text{source directions}
    \times 2\ \text{target directions} = 8.
\]

The result algebra for consecutive operational segments is checked, and the
difficult primitive permutation and its inverse both have residual-preserving
operational clauses. The earlier plan to interpret `≈∀-trans` itself by
`weak-one-step-composeᵀ` was too eager. For the compiler-generated route
proof, the transitive node packages one adjacent swap followed by a residual
`≈∀-∀` congruence. The adjacent-swap clause now performs the runtime work and
stores that congruence in the inner quotient index. Composition is needed
only after a later target reduction actually exposes another local segment.

The allocation leaves needed by a derivation-recursive one-step theorem have
the common `WeakOneStepResult` interface. The ordinary matched and right-only
`ν` leaves, the repaired matched and right-only `ν ★` leaves, and both crossed
adjacent-swap orientations are usable directly. None of the instantiation
allocation leaves now assumes a cast-compatibility proposition absent from
its input term-imprecision derivation. Agda requires the eventual recursive
function to be total, so it cannot be introduced as a one-clause partial
definition.

All six outer `ξ-ν` frame forms are now checked: ordinary and `★`, each in
matched, source-only, and target-only orientation. The matched forms consume
`WeakOneStepAllResult`; target-only forms use the general
`transportRightBody` action; source-only forms need only explicit source
endpoint normalization. Their outcome-level corollaries also propagate an
inner source catchup to blame.

The canonical-`∀` catchup base cases, shared `keep` recursion algebra,
direct `α/Λ` leaf, single-sided reveal/conceal clauses, and both generic cast
directions are now checked. The narrowing proof is
`left-catchup-all-α-∀-narrowingᵀ`; it uses the loosened one-layer
`cast⊒⊑ᵀ` rule with the explicit final witness `∀ⁱ q`. Thus the first
remaining canonical value shape is complete:

\[
  (\uparrow(V\langle\forall X.c\rangle))\,\bullet.
\]

The administrative half of the `gen` shape is also checked by
`left-catchup-all-α-gen-narrowingᵀ`:

\[
  (\uparrow(V\langle\mathsf{gen}\;A\;c\rangle))\,\bullet
    \longrightarrow_{\mathsf{keep}}
  (\uparrow V)\langle c\rangle.
\]

It uses `allocate-gen-narrowing`, the shared `keep`-prepend algebra, and the
same loosened one-layer narrowing rule. Its only non-administrative premise
is the transported inner relation

\[
  \nu\Phi;\Delta_L+1,\Delta_R;\rho^+
    \vdash \uparrow V\sqsubseteq V'
    :\uparrow A\sqsubseteq \forall X.C'.
\]

This isolates the next invariant: term imprecision must be natural under a
one-sided source allocation. Proving that reusable transport is preferable
to adding an `α/gen` rule, because it also addresses later recursion through
proof-only allocation worlds. The β-gen clause itself needs no additional
term-imprecision constructor.

- Refactored all four β-`∀` overlap theorems containing source narrowing.
  They now take the needed intermediate or final type-imprecision witness
  explicitly. None retains `StoreDetWf`, `LeftCastCtxCompatible`, or an
  internally derived source-cast index.
- Proved the first reusable source-allocation naturality components:
  `lifted-left-weakenCast-seal★`, `lifted-left-narrowing`, and
  `lifted-left-widening` transport the cast evidence through the source type
  shift. The constructor actions
  `left-source-lift-cast-narrowingᵀ` and
  `left-source-lift-cast-wideningᵀ` then rebuild exactly one shifted cast
  node. `allocated-left-relationᵀ` adds the fresh runtime-store entry without
  changing the term relation.
- Strengthened `left-catchup-all-α-gen-narrowingᵀ` to consume its recursive
  inner relation in the shifted store world `ρ′`; it uses
  `allocated-left-relationᵀ` internally. Thus the remaining premise is now
  precisely the output of the desired structural theorem:

  \[
  \begin{aligned}
    &\Phi;\Delta_L,\Delta_R;\rho;\Gamma
      \vdash M\sqsubseteq M' : A\sqsubseteq B\\
    &\quad\Longrightarrow
      \nu\Phi;\Delta_L+1,\Delta_R;\uparrow_L\rho;\uparrow_L\Gamma
      \vdash \uparrow M\sqsubseteq M' : \uparrow A\sqsubseteq B.
  \end{aligned}
  \]

  The difficult recursive clause is `Λ`: a source-only `ν` extension must
  commute past a matched `∀` extension. The required type-index action is
  already `⊑-∀ν-to-ν∀ᵢ`. The next proof should establish the corresponding
  term/store/context naturality square and reuse it in the `Λ` clause. This
  is a structural theorem, not a new term-imprecision constructor.
- Proved the store half as `left-forall-store-square`. It constructs both
  allocation orders

  \[
    \rho\xrightarrow{\nu_L}\rho_\nu
      \xrightarrow{\forall}\rho_{\nu\forall},
    \qquad
    \rho\xrightarrow{\forall}\rho_\forall
      \xrightarrow{\nu_L}\rho_{\forall\nu},
  \]

  without identifying their proof-relevant `StoreImp` witnesses, and proves

  \[
    \operatorname{left}(\rho_{\nu\forall})
      =\operatorname{left}(\rho_{\forall\nu}),
    \qquad
    \operatorname{right}(\rho_{\nu\forall})
      =\operatorname{right}(\rho_{\forall\nu}).
  \]

  Thus the remaining `Λ` obligation is the term-relation reindexing between
  `∀(νΦ)` and `ν(∀Φ)`; no equality of world witnesses is needed.
- Proved the inverse type-index transport `⊑-ν∀-to-∀νᵢ`:

  \[
    \nu(\forall\Phi)\vdash A\sqsubseteq B
      \quad\Longrightarrow\quad
    \forall(\nu\Phi)\vdash
      \operatorname{swap}_{01}(A)\sqsubseteq B.
  \]

  Together with the earlier forward direction, this supplies both
  orientations needed when source allocation and a matched universal binder
  occur in opposite orders.
- Proved the term-context analogue `left-forall-ctx-square`. It constructs
  both lifting orders and identifies their erased left and right term
  contexts. As for stores, the two `CtxImp` witnesses remain distinct.
- Proved `left-source-lift-Λᵀ`. Once the body relation has been transported
  into the `∀(νΦ)` corner, the existing `Λ⊑Λᵀ` constructor directly rebuilds
  the shifted outer abstractions:

  \[
    \forall(\nu\Phi)\vdash
      \operatorname{rename}(\operatorname{ext}(\mathsf{suc}),V)
        \sqsubseteq V'
    \quad\Longrightarrow\quad
    \nu\Phi\vdash
      \uparrow(\Lambda V)\sqsubseteq\Lambda V'.
  \]

  Therefore no new term-imprecision rule is missing at the outer `Λ`
  boundary; only body naturality remains.
- Added the general one-sided world-renaming infrastructure
  `⊑-rename-leftᵢ`, `rename-left-storeⁱ`, and `rename-left-ctxⁱ`, with endpoint
  equations, term-context lookup transport, and `StoreCorresponds` transport.
  This captures the repeated non-binder cases once, rather than adding a
  constructor for each administrative term shape.
- Audited the attempted commutation of that map through `LiftStoreⁱ` and
  `LiftCtxⁱ`. The type equation

  \[
    \operatorname{rename}(\operatorname{ext}(\tau),\uparrow A)
      = \uparrow\operatorname{rename}(\tau,A)
  \]

  is propositional, while store and context entries retain their
  type-imprecision proofs. Consequently erased endpoint equality cannot
  transport the variable case, and a deterministic raw renaming map cannot
  be definitionally identified with the normalized lifted world. The next
  proof object must relate proof-relevant world entries while carrying these
  endpoint equalities. This is the minimal binder-naturality invariant; it
  does not require changing the term-imprecision definition.
- Replaced the first proof-flexible `LeftStoreRenameⁱ` and
  `LeftCtxRenameⁱ` attempt with a coherent version. Every matched, linked,
  or term-context entry now contains exactly the canonical
  `⊑-rename-leftᵢ` image of its input type-imprecision witness, transported
  only along its recorded source-endpoint equality. Thus repeated uses of one
  input witness have definitionally the same image.
- Made `⊑-rename-leftᵢ` structural on type-imprecision derivations. In
  particular,

  \[
    \mathsf{ren}_L(p_A\mapsto p_B)
      = \mathsf{ren}_L(p_A)\mapsto\mathsf{ren}_L(p_B),
    \qquad
    \mathsf{ren}_L(\forall^i p)
      = \forall^i\mathsf{ren}_L(p).
  \]

  This is the proof-level coherence needed by application and `Λ`; it is not
  a new term-imprecision rule.
- Proved coordinated binder actions `left-store-rename-∀`,
  `left-ctx-rename-∀`, `left-store-rename-ν`, and `left-ctx-rename-ν`.
  Each action constructs the target lifted world and its coherent body-world
  relation together. The source endpoint equation at either binder is the
  single naturality law

  \[
    \uparrow\mathsf{rename}(\tau,A)
      = \mathsf{rename}(\mathsf{ext}(\tau),\uparrow A).
  \]

  No intermediate `ν(∀Φ)` world or adjacent-binder swap is needed when
  crossing `Λ`; the direct body route is

  \[
    \forall\Phi \longrightarrow \forall(\nu\Phi)
  \]

  under `ext suc`.
- Proved the canonical source-allocation bridges
  `rename-left-store-source-liftⁱ`,
  `rename-left-ctx-source-liftⁱ`, and `left-source-rename-worldsⁱ`.
  These identify the desired outer source allocation with the coherent
  renaming `suc` without adding an administrative term constructor.
- Proved coherent erased-world equations for both stores and term contexts.
  The left erasures are exactly renamed by `τ`, while the right erasures are
  unchanged. These equations are the boundary needed to transport existing
  typing and cast premises through the same invariant.
- Reproved the focused variable and `Λ` actions against the coherent worlds,
  and added the application action `left-rename-·ᵀ`. Application is rebuilt
  directly with the existing `·⊑·ᵀ` constructor: the function and argument
  recursive results now share the exact canonical image of `p_A`. This checks
  the central reason for discarding the proof-flexible precursor.
- Proved the erased typing transports `left-typing-renameⁱ` and
  `right-typing-left-renameⁱ`, then checked the focused `blame` and `ƛ`
  actions. Source typing uses the existing `CastModeRenamer`; target typing is
  unchanged after transport across the right-erasure equations.
- Proved general source-side seal-mode, narrowing, and widening transport as
  `left-seal★-renameⁱ`, `left-narrowing-renameⁱ`, and
  `left-widening-renameⁱ`. The focused `cast⊒⊑ᵀ` and `cast⊑⊑ᵀ`
  actions now rebuild the two source-cast constructors under an arbitrary
  coherent renaming. For source allocation the renamer is
  `castModeRenamer-suc`; crossing `Λ` uses `castModeRenamer-ext`.
- Added the small `LeftInsertion` invariant for the renamings that actually
  occur in source allocation: `suc`, closed under `ext`. It supplies a mode
  renaming for every mode environment, including those in reveal/conceal
  conversions that do not carry a `CastMode` proof, and separately recovers
  the existing `CastModeRenamer` for ordinary cast rules.
- Proved coherent matched/link membership and `StoreCorresponds` transport.
  Using it, proved source and target reveal/conceal transport,
  `left-paired-conversion-renameⁱ`, `left-paired-cast-renameⁱ`, and the
  focused `conv⊑convᵀ` action. Propositionally shifted seal names and source
  types are eliminated at this boundary; no conversion-specific term rule is
  added.
- The remaining source-allocation theorem is derivation-recursive. The next
  difficult clauses are the runtime-bullet allocation forms and the
  quotiented narrowing layer. This is additional structure on the single
  naturality theorem, not an expansion of term imprecision.
- Audited closure of the three quotiented widening constructors under the
  first source allocation. `up⊑upᵀ` is closed because `id-onlyᵈ` is stable,
  but the two crossed rules are not. The checked lemmas
  `no-crossed-up-mode-rename-id`,
  `no-crossed-up-mode-rename-same`, and
  `no-crossed-up-mode-rename-opposite` show that

  \[
    \mathsf{ext}(\mathsf{inst}(\mathsf{tag}))
  \]

  cannot be renamed by `suc` into any existing left mode. Conversely,
  `crossed-left-mode-rename-opposite` shows that the other source orientation
  can rename to the opposite left mode, but its unchanged right mode then
  makes the pair match neither crossed rule.
- The minimal repair under consideration is to generalize only the *left*
  mode premises of `crossed-up⊑upᵀ` and `crossed-left-up⊑upᵀ` from their
  hard-coded modes to an arbitrary `CastMode μ`, retaining the existing
  `SealModeStore★ μ` and widening-typing premises. The right mode remains
  fixed and therefore continues to record the quotient orientation. This
  changes no AST shape and adds no constructor, but it is a term-imprecision
  definition change.
- The user approved that repair. Both constructors now quantify over a left
  mode `μ` and require

  \[
    \mathsf{CastMode}(\mu),\qquad
    \mathsf{SealModeStore}_{\star}(\mu,\Sigma_L),\qquad
    \mu;\Delta_L;\Sigma_L\vdash u:D\sqsubseteq A.
  \]

  Their right modes are unchanged. The typing projections and the two existing
  direct-swap constructions have been updated and checked.
- Proved quotient-type naturality `⊑ᵖ-rename-leftᵢ`. Its only nonstructural
  point is that adjacent-universal equivalence commutes with type renaming:

  \[
    A\approx_{\forall} C
    \quad\Longrightarrow\quad
    \operatorname{rename}(\tau,A)
      \approx_{\forall}
    \operatorname{rename}(\tau,C).
  \]

  The swap case uses `renameᵗ-swap01-ext²-commute`; the two outer binders
  force `ext (ext τ)` to fix the swapped names `0` and `1`.
- Proved the five quotient-layer constructor actions
  `left-rename-up⊑upᵀ`, `left-rename-crossed-up⊑upᵀ`,
  `left-rename-crossed-left-up⊑upᵀ`, `left-rename-down⊑downᵀ`, and
  `left-rename-gen-down⊑gen-downᵀ`. The crossed actions use the approved
  arbitrary left mode; the fixed `id-onlyᵈ` and `genᵈ tag-or-idᵈ` modes are
  stable under every source renaming. Thus the quotient layer needs no new
  term shape.
- Refined the source-allocation theorem to the exact fragment needed by
  `β-gen`: it assumes `No• M`. A source runtime bullet cannot satisfy this
  premise, so the `α⊑αᵀ` and `α⊑ᵀ` branches are impossible. This is
  essential: `⊢•` anchors its active seal at store name `0`, so unrestricted
  source allocation is not a valid typing transformation for an arbitrary
  bullet term. The right-only `⊑αᵀ` branch remains in scope because its
  source term contains no bullet.
- The next administrative boundary is repeated left allocation. If an existing
  `allocation-leftᵀ` derivation adds `(0,A)` and another source allocation is
  performed outside it, the transported entry is `(1,↑A)`. The current
  constructor originally added only name `0`. The user approved replacing that
  fixed name by an arbitrary source seal name `α`, while retaining its explicit
  well-formedness and both final typing premises. This is implemented and
  checked. It remains one proof-only store-extension constructor, not a new
  term-imprecision shape.
- Proved the proof-relevant allocation squares
  `left-right-store-commuteⁱ` and `left-right-ctx-commuteⁱ`. Given source-only
  and target-only allocations from the same world, they construct a single
  crossed world reached in either order:

  \[
  \begin{array}{ccc}
    (\rho,\Gamma) & \xrightarrow{\nu_L} &
      (\rho_L,\Gamma_L) \\
    \mathllap{\nu_R}\downarrow && \downarrow\mathrlap{\nu_R} \\
    (\rho_R,\Gamma_R) & \xrightarrow{\nu_L} &
      (\rho_\times,\Gamma_\times).
  \end{array}
  \]

  The common target retains the transported type-imprecision witnesses, so
  this is stronger than equality of erased stores and contexts.
- Proved `⊑-source-under-rightᵢ`, which transports a body relation already
  beneath a target-only allocation through a subsequent source allocation:

  \[
    \mathord{\uparrow_R\Phi};\Delta_L,\Delta_R+1
      \vdash A\sqsubseteq B
    \quad\Longrightarrow\quad
    \mathord{\uparrow_R(\nu_L\Phi)};\Delta_L+1,\Delta_R+1
      \vdash \uparrow A\sqsubseteq B.
  \]

  Using the allocation square and this type action,
  `left-source-lift-⊑αᵀ` rebuilds the right-only runtime-bullet case after a
  source allocation. This discharges the only bullet constructor compatible
  with the theorem's `No•` source premise, without adding a term-imprecision
  rule.
- Proved `left-rename-Λ⊑ᵀ`, the coherent source-renaming action for the
  one-sided polymorphic value relation

  \[
    \Lambda X.\,V \sqsubseteq N'.
  \]

  It transports the occurrence side condition by
  `occurs-zero-rename-ext`, constructs the two `ν` body worlds with
  `left-store-rename-ν` and `left-ctx-rename-ν`, and rebuilds the existing
  `Λ⊑ᵀ` constructor directly. The matched and one-sided `Λ` boundaries are
  therefore both closed under coherent source renaming.
- Closed the three target-cast wrappers under coherent source renaming with
  `left-rename-⊑cast⊒ᵀ`, `left-rename-⊑cast⊑ᵀ`, and
  `left-rename-⊑cast⊑idᵀ`. Their right coercions are unchanged because the
  right projected store is propositionally preserved. The `id-only` branch
  uses `right-store-det-left-renameⁱ` to transport its `StoreDetWf` premise
  across that same equation.
- Closed all four one-sided reveal/conceal wrappers with
  `left-rename-conv↑⊑ᵀ`, `left-rename-conv↓⊑ᵀ`,
  `left-rename-⊑conv↑ᵀ`, and `left-rename-⊑conv↓ᵀ`. Source conversions use the
  single `LeftInsertion` invariant; target conversions again transport across
  the unchanged right store. These proofs rebuild existing constructors and
  introduce no new imprecision cases.
- The remaining ordinary nullary and congruence forms are direct. The next
  binder-sensitive cluster is `ν⊑νᵀ`, `ν⊑ᵀ`, `⊑νᵀ`, and their three
  `ν ★` analogues. Their term bodies use the structural recursive result, but
  their source boundary conversion must also commute with the freshly
  allocated concrete store. This conversion/store naturality is the next
  proof boundary independent of the still-unapproved repeated-allocation
  repair.
- Proved the allocated ordinary-reveal transports
  `left-reveal-ν-renameⁱ` and `right-reveal-ν-left-renameⁱ`. The source lemma
  normalizes

  \[
    \operatorname{rename}(\operatorname{ext}\tau,
      (0,\uparrow A)::\uparrow\Sigma_L)
    =
    (0,\uparrow\operatorname{rename}(\tau,A))::
      \uparrow\operatorname{rename}(\tau,\Sigma_L),
  \]

  while the target lemma transports across the unchanged right projection.
  Using these lemmas, `left-rename-νᵀ` and `left-rename-ν⊑ᵀ` close the matched
  and left-only ordinary `ν` constructors.
- Proved `rename-assm²-⇑ᴿᵢ` and the proof-relevant commuting actions
  `left-store-rename-⇑ᴿ` and `left-ctx-rename-⇑ᴿ`. For an arbitrary coherent
  source insertion, they construct a shared world obtained by applying that
  insertion and a target-only allocation in either order. Unlike the earlier
  erased square, the resulting matched, linked, and context entries contain
  the exact structural images of their original type-imprecision witnesses.
  `left-rename-⊑νᵀ` uses this square to close the right-only ordinary `ν`
  constructor, including its body relation under `⇑ᴿᵢ`.
- Proved the `ν ★` concrete-store normalization

  \[
    \operatorname{rename}(\operatorname{ext}\tau,
      (0,\star)::\uparrow\Sigma_L)
    =
    (0,\star)::\uparrow\operatorname{rename}(\tau,\Sigma_L),
  \]

  together with source and target transports for both `SealModeStore★` and
  the widening boundary coercion. The checked actions
  `left-rename-νcastᵀ`, `left-rename-νcast⊑ᵀ`, and
  `left-rename-⊑νcastᵀ` consequently close all three existing `ν ★`
  constructors. Thus all six `ν`/`ν ★` term constructors are now structurally
  closed without modifying imprecision.
- The next step is to assemble these actions into the mutual derivation
  recursion for the `No•` source fragment. Runtime source-bullet constructors
  remain impossible, and the right-only bullet uses the already-checked
  allocation square. The proof-only allocation wrappers are the remaining
  administrative cases.
- Proved the inverse proof-relevant allocation actions
  `left-store-rename-⇑ᴿ-inv` and `left-ctx-rename-⇑ᴿ-inv`. If a coherent
  source renaming is given *after* a target-only allocation, these lemmas
  reconstruct a renamed pre-allocation world and a target-allocation witness
  reaching the supplied final world. This is the direction needed by
  derivation recursion through an already allocated state; it is not merely
  an inverse equality on erased stores.
- Proved `left-rename-⊑αᵀ` for arbitrary `LeftInsertion τ`. It uses the inverse
  square to recursively transport the pre-allocation relation, then rebuilds
  the existing right-only runtime-bullet constructor at

  \[
    \mathord{\uparrow_R\Psi};\Delta_L',\Delta_R+1
      \vdash
      \operatorname{rename}(\tau,N)
      \sqsubseteq
      (\uparrow L')\,\bullet.
  \]

  The final source and target typings are transported from the reconstructed
  base world and the given allocated world, respectively. Hence all runtime
  bullets are now covered by the `No•` recursion: `α⊑αᵀ` and `α⊑ᵀ` are
  impossible on the source, while `⊑αᵀ` has a checked generic action.
- The remaining recursive cases are the matched and crossed/swap proof-only
  allocation wrappers. The ordinary syntax, quotient, `Λ`, conversion, cast,
  all `ν` families, and `allocation-leftᵀ` now have constructor actions. The
  next proof step is therefore the matched-allocation square followed by the
  mutual recursion.
- The user approved the minimal `allocation-leftᵀ` generalization. The rule
  now quantifies an arbitrary seal name `α`; its three former occurrences of
  `store-left zero A hA` are `store-left α A hA`. Its world, lifting premise,
  inner relation, typings, and term endpoints are unchanged. Existing uses
  continue to infer `α = zero`.
- Proved `left-store-rename-ν-inv` and `left-ctx-rename-ν-inv`. These are the
  inverse naturality squares for a fixed fresh binder: a coherent
  `ext τ`-renaming of an already lifted world reconstructs the coherently
  renamed base world and its left-lift witness.
- Proved `left-store-rename-suc-liftⁱ`. At the opposite-order boundary, a
  coherent `suc`-renaming from a world to its fresh left extension is itself a
  `LiftLeftStoreⁱ` witness. This is deliberately separate from the `ext τ`
  square because the outer allocation shifts the previously fresh name:

  \[
    0 \longmapsto 1,
    \qquad
    \mathsf{suc}(\alpha) \longmapsto
      \mathsf{suc}(\mathsf{suc}(\alpha)).
  \]

- Proved `left-source-lift-allocation-leftᵀ`, the repeated-left-allocation
  constructor action. It recursively accepts the renamed inner relation,
  converts the tail renaming to the required lift, transports both final
  typings, and rebuilds the existing wrapper with

  \[
    \mathsf{storeLeft}(\alpha,A)
      \longmapsto
    \mathsf{storeLeft}(\mathsf{suc}(\alpha),\uparrow A).
  \]

  This is the first checked use of the approved arbitrary seal name. No new
  term-imprecision constructor or term shape was added.
- Rechecked both strict targets after this change:
  `proof/NuImprecisionSimulation.agda` and `All.agda` pass with
  `--no-allow-unsolved-metas`.

The target-`∀` inversion was also rechecked. It guarantees that the source
type is universal, but the bodies of matched `Λ` values may still have any
type and any term shape. Thus restricting naturality to universal-typed
bodies would be unsound as a proof strategy.

These pieces feed the total derivation-recursive one-step theorem with
codomain `WeakOneStepOutcome`. Its ordinary operational leaves return
`WeakOneStepResult` and a proof that the result transports every bullet-free
relation in the original world. A target-blame leaf must first establish a
source reduction to blame and then use `outcome-source-blame`. When the input
type relation is headed by `∀ⁱ`, recursion returns `WeakOneStepAllOutcome`,
retaining both the canonical body derivation and the transport witness. The
later audit of one-sided `β-gen•` shapes remains separate.

The generic lifting obstruction remains useful: `crossed-bodyᵀ` closes only
the paired direct-swap quotient boundary and does not reintroduce the false
unrestricted structural lifting theorem. The one-sided `β-gen•` shapes still
require their separate audit afterward.

### Blame outcome polarity repair

- Replaced the unsound target-blame alternatives in `WeakOneStepOutcome` and
  `WeakOneStepAllOutcome` with source-blame alternatives. For a more-precise
  source `M` and less-precise target `N'`, the exceptional outcome now requires

  \[
    \exists\,\bar\chi.\; M \longrightarrow^{\bar\chi *} \mathsf{blame}.
  \]

  A target reduction to `blame` alone cannot discharge the simulation.
- Replaced `weak-one-step-target-blameᵀ` with
  `weak-one-step-source-blameᵀ`, which takes the source reduction as an
  explicit premise.
- Strengthened source-framing outcome maps with a source-blame preservation
  premise. The matched and source-only `ν`/`ν ★` corollaries discharge it
  using `ν-blame-tail`; target-only frames preserve the source reduction
  unchanged.
- No term- or type-imprecision clause changed. Both strict checks pass:
  `proof/NuImprecisionSimulation.agda` and `All.agda` with
  `--no-allow-unsolved-metas`.

### Top-down DGG proof spine

- Aligned the public runtime observations with `compileᵀ`, the compilation
  interface used by `compile-preserves-term-imprecision`. Proved
  `compile-term-agrees`, so this changes no compiled term:

  \[
    \pi_1(\mathsf{compile}\;M)
      = \pi_1(\mathsf{compile}^{T}\;M).
  \]

  The agreement proof also transfers `No•` and `RuntimeOK` to `compileᵀ`.
- Added `proof/NuDGGSpine.agda`. The theorem
  `compiled-term-imprecision` checks the exact initial boundary

  \[
    \varnothing;0;0;\varnothing;\varnothing
      \vdash N \sqsubseteq N' : A \sqsubseteq B,
  \]

  where `N` and `N'` are the two public compiled observations.
- Stated the genuine closed operational theorem `ClosedNuDGG` and proved
  `closed-nu-dgg⇒gradual-dgg`. Thus the public theorem now has one explicit
  predecessor rather than an informal gap from compiler monotonicity to the
  final four observations.
- Proved `multi-runtime-preservation` and exposed it through `NuMetaTheory`.
  Together with multi-step typing preservation and progress, it discharges
  the progress component needed at every reachable source state.
- Proved that the two divergence clauses are consequences of terminal
  simulation facts:

  1. target convergence implies source convergence if target values catch up
     to a source value or source blame, and target blame catches up to source
     blame;
  2. source divergence therefore implies target divergence;
  3. forward simulation of source values plus progress implies that target
     divergence gives source divergence-or-blame.

  The full operational theorem therefore has three substantive terminal
  obligations: forward source-value simulation, backward target-value
  simulation, and backward target-blame simulation. The last obligation is
  exactly where `outcome-source-blame` is required.
- Proved `closed-nu-terminal-simulation⇒closed-nu-dgg`. It constructs all four
  clauses of `ClosedNuDGG` from exactly those three terminal clauses. The two
  divergence clauses are therefore connected to the public proof spine by
  checked Agda terms rather than only justified in this ledger.
- This top-down link exposed and repaired two latent interface problems:

  1. the dynamic-application branch of `compile-term-agrees` left the type
     context of its two cast plans implicit; both plans now carry the explicit
     ambient context;
  2. `QuotientedTermImprecision` projects the refined `TermTyping` judgment,
     whereas the existing progress theorem consumes the older `NuTerms`
     judgment. The checked bridge `closed-nu-source-typing` now applies the
     proved `TermTyping.forget` embedding and explicitly normalizes the empty
     source store and context.
- Added `proof/NuReductionDeterminism.agda`. It proves value and blame
  irreducibility, determinism of pure and store-changing one-step reduction,
  and the two terminal-prefix properties

  \[
    M \longrightarrow^{\!*}_{\bar\chi} N,
    \quad
    M \longrightarrow^{\!*}_{\bar\psi} V,
    \quad V\ \mathsf{value}
    \quad\Longrightarrow\quad
    \exists\bar\theta.\;
      N \longrightarrow^{\!*}_{\bar\theta} V
      \land
      \bar\psi = \bar\chi\mathbin{+\!+}\bar\theta,
  \]

  with the analogous statement for `blame`.
- Added `proof/NuDGGTraceAlignment.agda`. It applies those prefix properties
  directly to `WeakOneStepResult.targetTail`, and lifts them across
  `WeakOneStepOutcome`. The lifted result has exactly the sound alternatives
  needed by the backward DGG clauses: either the related result continues
  along the remaining target trace, or the source already reduces to blame.
- The next integration boundary is therefore no longer trace alignment. It is
  the recursive one-step dispatcher itself: from an arbitrary quotiented term
  relation and target head step, produce `WeakOneStepOutcome`, then recurse on
  the aligned remainder while threading the result store, contexts, endpoint
  types, and related-result derivation.
- No term- or type-imprecision definition changed. The focused spine and the
  aggregate development pass with `--no-allow-unsolved-metas`.

### First structural dispatcher boundary

- Proved the application-left frame `weak-one-step-·₁-frameᵀ`. Suppose

  \[
    L \sqsubseteq L',
    \qquad
    L' \longrightarrow^{\chi} L_1',
  \]

  and recursive simulation of the function step produces source changes
  \(\bar\chi_L\), target-tail changes \(\bar\chi_R\), and related
  endpoints \(W_L \sqsubseteq W_R\). If the recursive result retains the
  canonical arrow relation

  \[
    W_L \sqsubseteq W_R :
      \operatorname{apply}(\bar\chi_L,A) \to
      \operatorname{apply}(\bar\chi_L,B)
      \;\sqsubseteq\;
      \operatorname{apply}(\bar\chi_R,\chi A') \to
      \operatorname{apply}(\bar\chi_R,\chi B')
  \]

  and the untouched arguments are transported to

  \[
    \operatorname{apply}(\bar\chi_L,M)
      \sqsubseteq
    \operatorname{apply}(\bar\chi_R,\chi M'),
  \]

  then the whole applications are related after the same changes. The source
  and target traces are the function traces lifted through their application
  frames.
- Proved `weak-one-step-·₁-frame-outcomeᵀ`, which lifts both sound
  outcomes.
  The related branch uses the frame theorem above. In the source-blame branch,
  `·₁-blame-tail` gives the whole-term trace

  \[
    L\,M
      \longrightarrow^{\bar\chi_L *}
    \mathsf{blame}\,
      \operatorname{apply}(\bar\chi_L,M)
      \longrightarrow
    \mathsf{blame}.
  \]

  Thus framing does not reintroduce the rejected alternative in which target
  blame alone is sufficient.
- This boundary identifies the next exact dispatcher obligation: construct
  the two transported relations above from the recursive result and the
  original `L ⊑ L'` and `M ⊑ M'` derivations. This is the term-naturality
  recursion already motivated by allocations; it must preserve canonical
  arrow shape, not merely return an unstructured `WeakOneStepResult`.
- No term-imprecision or type-imprecision rule changed.

### No-bullet term transport through weak results

- The application frame exposed information not present in
  `WeakOneStepResult`. Its `transportType` field transports
  \(A \sqsubseteq A'\), but that alone cannot produce

  \[
    \operatorname{apply}(\bar\chi_L,M)
      \sqsubseteq
    \operatorname{apply}(\bar\chi_R,\chi M').
  \]

  In particular, equality of the erased source and target stores does not
  reconstruct the proof-relevant matched, left, right, and linked entries
  needed by the term judgment.
- Defined the proof-only invariant `WeakOneStepTransport result`. For every
  original derivation

  \[
    M \sqsubseteq M' : A \sqsubseteq A'
  \]

  whose two terms contain no runtime bullet, it transports the whole
  derivation through exactly the source changes, observed target change, and
  target administrative tail recorded by `result`. Its conclusion is

  \[
    \operatorname{apply}(\bar\chi_L,M)
      \sqsubseteq
    \operatorname{apply}(\bar\chi_R,\chi M')
      :
    \operatorname{apply}(\bar\chi_L,A)
      \sqsubseteq
    \operatorname{apply}(\bar\chi_R,\chi A').
  \]

- Proved `weak-one-step-related-transportᵀ`: the reflexive weak result
  preserves every no-bullet term derivation unchanged.
- Proved `weak-one-step-·₁-frame-transportᵀ`. Given the canonical
  transported arrow relation for the recursively simulated function, the
  frame obtains its argument premise by applying `WeakOneStepTransport` to
  the original derivation \(M \sqsubseteq M'\).
- Proved `weak-one-step-·₁-frame-preserves-transportᵀ`. Framing changes
  neither allocation sequence nor world transformation, so the inner
  transport invariant is also the transport invariant of the whole
  application result.
- Proved the corresponding sound outcome theorem
  `weak-one-step-·₁-frame-transport-outcomeᵀ`. Its exceptional branch still
  requires a source trace to blame.
- The next leaf obligation is to construct `WeakOneStepTransport` for the
  allocation-producing results. Matched, left-only, right-only, and crossed
  allocations must use their proof-relevant store/context actions; erased
  store equalities are deliberately insufficient.
- No term-imprecision or type-imprecision definition changed.

### Allocation transport exposes store-representation sensitivity

- Attempted the structural recursion needed to construct
  `WeakOneStepTransport` for allocation-producing leaves. Every ordinary
  term constructor, both quotiented cast constructors, all six `ν` forms,
  `Λ`, conversions, and casts admits the expected no-bullet action using the
  existing lemmas. The remaining cases are exactly the proof-only
  `allocation-matchedᵀ`, `allocation-leftᵀ`, `allocation-crossedᵀ`, and
  swap wrappers.
- The obstruction is the exact representation of `StoreImp`, rather than a
  missing type action. For example, suppose an existing matched wrapper has
  added

  \[
    \mathsf{storeMatched}(\alpha,A,\beta,B)
  \]

  and a later source-only allocation transports it. Its image is

  \[
    \mathsf{storeMatched}
      (\alpha+1,\uparrow A,\beta,B).
  \]

  The resulting world has assumptions

  \[
    0\sqsubseteq\star,
    \qquad
    1\sqsubseteq 0,
  \]

  so it is neither a fresh matched extension nor a fresh left-only extension.
  The current specialized wrappers cannot rebuild the relation in that exact
  store, even though all erased source and target stores have the expected
  shapes. Repeating this per allocation order would create the open-ended
  family of special cases that the proof strategy is intended to avoid.
- The minimal definition-level repair to evaluate next is consolidation, not
  expansion: replace the three specialized proof-only store-extension
  wrappers by one prefix-extension wrapper. Its premise should contain an
  explicit proof that the old `StoreImp` is a suffix of the new one, the inner
  term relation at the old store, and both endpoint typings at the extended
  store. This retains the current wrappers' essential restriction against
  arbitrary store replacement, reduces the number of simulation cases, and
  makes nested matched, one-sided, and crossed allocations instances of one
  invariant.
- This consolidation was approved and is implemented below.

### Allocation prefixes replace the specialized wrappers

- Defined the constructor-form judgment

  \[
    \mathsf{StoreImpPrefix}(\rho_0,\rho^+),
  \]

  whose reflexive case says that a store is its own suffix and whose step
  case adds one `StoreImpEntry` to the front of the extended store. Thus the
  judgment records exactly that

  \[
    \rho^+ = e_1 :: \cdots :: e_n :: \rho_0
  \]

  without putting a list function in an indexed datatype.
- Replaced `allocation-matchedᵀ`, `allocation-leftᵀ`, and
  `allocation-crossedᵀ` by the single rule `allocation-prefixᵀ`. If

  \[
    \mathsf{StoreImpPrefix}(\rho_0,\rho^+),
    \qquad
    \Phi;\Delta_L;\Delta_R;\rho_0;\Gamma
      \vdash M \sqsubseteq M' : A \sqsubseteq B,
  \]

  and both endpoints have their final typings in the projected stores of
  \(\rho^+\), then

  \[
    \Phi;\Delta_L;\Delta_R;\rho^+;\Gamma
      \vdash M \sqsubseteq M' : A \sqsubseteq B.
  \]

  The rule therefore changes only the proof-relevant store prefix; it does
  not relate new term or type shapes.
- Migrated every construction site. A matched or one-sided allocation uses a
  one-entry prefix. The opposite-order two-allocation traces use the exact
  six-entry prefix consisting of two left entries, two right entries, and
  the two crossed links. The three obsolete constructors were deleted, and
  the source- and target-typing projections now have one prefix case.
- Proved `left-store-rename-prefix-invⁱ`. If a left store renaming maps an
  extended store, this lemma exposes a renamed old suffix and the
  corresponding renamed prefix proof. Proved the direct structural clause
  `left-rename-allocation-prefixᵀ`, which recursively transports the inner
  derivation at that suffix and rebuilds the single prefix rule using the
  final transported typings.
- The next transport boundary is now sharply isolated. The general
  no-runtime-bullet naturality recursion can use this one prefix clause for
  every allocation prefix. Its only remaining non-structural term-shape
  cases are `swapRight-bodyᵀ` and `swapLeft-bodyᵀ`; those wrappers are
  intentionally not folded into prefix extension because they permute terms
  and types rather than merely extending a store.
- `QuotientedTermImprecision.agda` and
  `proof/NuImprecisionSimulation.agda` pass with
  `--no-allow-unsolved-metas` after the consolidation.

### Dependency-preserving permutation boundary

- Added the reusable endpoint notion

  \[
    \pi : \Delta \mathrel{\rightsquigarrow} \Theta.
  \]

  A witness contains renamings \(\pi\) and \(\pi^{-1}\), boundedness proofs
  in both directions, and both inverse laws. Identity, symmetry, extension
  under a fresh binder, and the adjacent transposition are proved instances.
  Thus a permutation is not merely an arbitrary function on de Bruijn
  indices.
- Added proof-relevant actions on related stores and term contexts. Given
  endpoint permutations \(\pi_L\) and \(\pi_R\), the assumption action is

  \[
    X \sqsubseteq Y
      \longmapsto
    \pi_L(X) \sqsubseteq \pi_R(Y),
    \qquad
    X \sqsubseteq \star
      \longmapsto
    \pi_L(X) \sqsubseteq \star.
  \]

  `RelStoreRenameⁱ` and `RelCtxRenameⁱ` then require the target related
  store and context explicitly. This is the mechanized dependency check:
  a proposed permutation is usable only when the renamed entries, endpoint
  types, and imprecision assumptions inhabit the proposed target world.
- Packaged these components as `RelWorldPermutationⁱ`. Besides the two
  endpoint bijections, it carries the two coercion-mode actions. The latter
  is essential: permuting names in coercions must also permute the mode
  environment that controls whether a name may be sealed or tagged.
- Proved the projection equations

  \[
  \begin{aligned}
    \mathsf{leftStore}(\varpi\rho)
      &= \pi_L\,\mathsf{leftStore}(\rho), \\
    \mathsf{rightStore}(\varpi\rho)
      &= \pi_R\,\mathsf{rightStore}(\rho), \\
    \mathsf{leftCtx}(\varpi\Gamma)
      &= \pi_L\,\mathsf{leftCtx}(\Gamma), \\
    \mathsf{rightCtx}(\varpi\Gamma)
      &= \pi_R\,\mathsf{rightCtx}(\Gamma).
  \end{aligned}
  \]

  Consequently, for terms with no runtime bullet, endpoint typing already
  transports through a related-world permutation:

  \[
    \Delta_L;\Sigma_L;\Gamma_L \vdash M : A
    \quad\Longrightarrow\quad
    \Theta_L;\pi_L\Sigma_L;\pi_L\Gamma_L
      \vdash \pi_L M : \pi_L A,
  \]

  and symmetrically on the right.
- The adjacent-allocation shapes now have the explicit factor equations

  \[
    \mathsf{swap}_{01}(\uparrow M)
      = \mathsf{lift}_0(\uparrow)M,
    \qquad
    \mathsf{swap}_{01}(\mathsf{lift}_0(\uparrow)M)
      = \uparrow M.
  \]

  Therefore each old crossed-body wrapper factors into a paired fresh
  extension followed by a genuine adjacent permutation on one endpoint.
- Runtime bullet remains deliberately outside the general theorem. Its
  canonical typing fixes the active fresh name at index zero. The proved
  pointed equation is

  \[
    \operatorname{rename}_{\operatorname{ext}(\pi)}
      ((\uparrow L)\mathbin{\bullet})
    =
      (\uparrow\operatorname{rename}_{\pi}L)\mathbin{\bullet}.
  \]

  Hence a permutation may cross a bullet only in extended form
  \(\operatorname{ext}(\pi)\), which fixes zero. An unpointed adjacent swap
  moves zero and does not preserve the canonical bullet state.
- The next obligation is the actual admissibility recursion. If

  \[
    \Phi;\rho;\Gamma \vdash M \sqsubseteq M' : A \sqsubseteq B,
    \qquad
    \varpi : (\Phi;\rho;\Gamma)
      \mathrel{\rightsquigarrow}
      (\Psi;\delta;\Xi),
  \]

  and neither endpoint contains runtime bullet, prove

  \[
    \Psi;\delta;\Xi \vdash
      \pi_L M \sqsubseteq \pi_R M'
      : \pi_L A \sqsubseteq \pi_R B.
  \]

  The ordinary and quotiented judgments must be proved mutually. Once this
  is available, the two specialized swap-body constructors can be derived
  and deleted rather than adding a primitive permutation case to simulation.
- Started that mutual boundary with its structurally direct quotiented case.
  Quotiented type imprecision is natural under independent endpoint
  permutations:

  \[
    A \sqsubseteq^{p} B
      \quad\Longrightarrow\quad
    \pi_L A \sqsubseteq^{p} \pi_R B.
  \]

  The two outer \(\forall\)-permutation equivalences are renamed on their
  respective endpoints, while the ordinary middle derivation uses the
  two-sided indexed type-renaming theorem.
- Proved `rel-world-down-permuteᵀ`, the `down/down` clause that the eventual
  mutual recursion will call. If the recursively permuted bodies are
  related, both `id-only` narrowing coercions rename in the projected target
  stores and `down⊑downᵀ` rebuilds the quotiented relation. This case works
  for every endpoint permutation because the `id-only` mode environment is
  invariant under arbitrary renaming.
- Proved `rel-world-gen-down-permuteᵀ`, the direct
  `gen-down/gen-down` clause. Its mode is `genᵈ tag-or-idᵈ`, which is
  pointwise `tag-or-id` and is therefore invariant under arbitrary
  renaming. The binder-order issue arises instead in nested body modes such
  as `instᵈ (extᵈ μ)` and `extᵈ (instᵈ μ)`.

### Adjacent permutation acts on coercion modes

- Defined the action of the adjacent transposition on a `CastMode` stack. In
  nominal form, if the first two entries are

  \[
    (m_0,m_1,\mu),
  \]

  then the target mode is

  \[
    (m_1,m_0,\mu).
  \]

  The construction covers all five `CastMode` forms. The two constructors
  that introduce an `id-only` entry, `cast-ext` and `cast-weaken`, have the
  same pointwise mode action and therefore share the same target shape.
- Proved `swap-mode-target-agrees`:

  \[
    \mathsf{swapMode}(\mu)(X)
      = \mu(\mathsf{swap}_{01}(X)).
  \]

  Together with involutivity of `swap₀₁`, this gives both required
  semantic properties:

  \[
    \mathsf{ModeRename}(\mathsf{swap}_{01},\mu,
      \mathsf{swapMode}(\mu))
  \]

  and, whenever the target permits sealing at \(\alpha\), the source permits
  sealing at \(\mathsf{swap}_{01}(\alpha)\).
- Packaged the result as
  `castModeRenamer-swap01 : CastModeRenamer swap01ᵗ`. Also proved the
  identity renamer needed for the unchanged endpoint of a one-sided world
  permutation.
- Defined the canonical action of an arbitrary endpoint permutation on an
  arbitrary mode environment:

  \[
    (\pi\mu)(X) = \mu(\pi^{-1}(X)).
  \]

  Proved both `ModeRename` and seal-preimage evidence for this action. This
  is the form needed by reveal and conceal conversions, whose modes need not
  come with a `CastMode` derivation.
- The target computation exposes the crossed modes definitionally:

  \[
  \begin{aligned}
    \mathsf{swapMode}(\mathsf{inst}(\mathsf{ext}(\mu)))
      &= \mathsf{ext}(\mathsf{inst}(\mu)), \\
    \mathsf{swapMode}(\mathsf{ext}(\mathsf{inst}(\mu)))
      &= \mathsf{inst}(\mathsf{ext}(\mu)), \\
    \mathsf{swapMode}(\mathsf{gen}(\mathsf{ext}(\mu)))
      &= \mathsf{ext}(\mathsf{gen}(\mu)), \\
    \mathsf{swapMode}(\mathsf{ext}(\mathsf{gen}(\mu)))
      &= \mathsf{gen}(\mathsf{ext}(\mu)).
  \end{aligned}
  \]

  These are the exact order changes produced by the crossed
  `\forall`/`gen` and `\forall`/`inst` administrative traces. No new term
  imprecision rule is required for the mode change.

### Permutation under a fresh matched binder

- Proved `rel-store-rename-lift∀ⁱ` and `rel-ctx-rename-lift∀ⁱ`.
  Given a related-world permutation and a source lift under a fresh matched
  pair of names, they construct the target lifted store and context and the
  extended permutation between the two body worlds. In nominal form, the
  endpoint action extends as

  \[
    \pi^+(X) = X,
    \qquad
    \pi^+(\alpha) = \pi(\alpha)
    \quad\text{for old names }\alpha,
  \]

  while the fresh assumption remains `X \sqsubseteq X` and every old
  assumption is shifted under it.
- Packaged the construction as `rel-world-permutation-lift∀ⁱ`. Its two
  coercion-mode actions are obtained by extending the original mode
  permutations, so the fresh name stays fixed and the old names retain their
  permuted permissions.
- Proved `rel-world-Λ-permuteᵀ`, the direct `Λ/Λ` binder boundary. It
  returns the constructed target body world and an assembler with the exact
  recursive premise

  \[
    \forall X.\Psi;\pi_L^+\rho_L;\pi_R^+\rho_R
      \vdash \pi_L^+ V \sqsubseteq \pi_R^+ V'
      : \pi_L^+ A \sqsubseteq \pi_R^+ B.
  \]

  Supplying that recursive body relation yields

  \[
    \Psi;\pi_L\rho_L;\pi_R\rho_R
      \vdash \pi_L(\Lambda X.V) \sqsubseteq
        \pi_R(\Lambda X.V')
      : \pi_L(\forall X.A) \sqsubseteq
        \pi_R(\forall X.B).
  \]

  Thus the matched polymorphic value case is now connected to the eventual
  mutual admissibility recursion without a new term-imprecision rule.

### Permutation through `ν`, `ν ★`, and one-sided binders

- Proved the source-only and target-only analogues of the matched lifting
  square:

  - `rel-world-permutation-lift-leftⁱ` extends only \(\pi_L\) and preserves
    the fresh assumption `X \sqsubseteq \star`;
  - `rel-world-permutation-lift-rightⁱ` extends only \(\pi_R\) and shifts
    the target name of every old matched assumption.

  Both constructions produce the target store, target term context, lift
  witnesses, and the related-world permutation needed by a recursive call.
  The generic assumption action for the target-only case is recorded by
  `rename-assm²-⇑ᴿ²ᵢ`.
- Proved `rel-world-Λ⊑-permuteᵀ`. In nominal form, a source-only
  polymorphic value relation

  \[
    X \sqsubseteq \star;Φ
      \vdash V \sqsubseteq N'
      : A \sqsubseteq B
  \]

  is transported in the constructed one-sided body world and reassembled as

  \[
    Ψ \vdash
      \pi_L(\Lambda X.V) \sqsubseteq \pi_R N'
      : \pi_L(\forall X.A) \sqsubseteq \pi_R B.
  \]

  The occurrence premise for the `ν` type-imprecision index is preserved by
  `occurs-zero-rename-ext`.
- Proved `left-reveal-ν-rel-permute` and
  `right-reveal-ν-rel-permute`. They rename a reveal conversion through the
  entire fresh-name store

  \[
    (X,\uparrow A) :: \uparrow\Sigma,
  \]

  normalize both shifted endpoint types, and use the canonical permutation
  action on the reveal mode.
- Using those conversion lemmas and the three lifting squares, proved all
  three reveal-based `ν` clauses:

  - `rel-world-ν⊑ν-permuteᵀ`;
  - `rel-world-ν⊑-permuteᵀ`;
  - `rel-world-⊑ν-permuteᵀ`.

  The matched clause transports the hidden relation
  \(\uparrow A \sqsubseteq \uparrow A'\) at the extended permutations. The
  one-sided clauses instead construct exactly the `X \sqsubseteq \star` or
  target-lifted world required by their original constructors.
- Proved `left-ν★-widening-rel-permute` and
  `right-ν★-widening-rel-permute`. Each transports, as one coherent
  package, the base `CastMode`, the `inst`-extended seal permission, and the
  widening coercion in

  \[
    (X,\star) :: \uparrow\Sigma.
  \]

  Keeping these three premises together prevents the reconstructed relation
  from accidentally combining a target mode with seal or coercion evidence
  produced by a different permutation action.
- Using those packages, proved all three `ν ★` clauses:

  - `rel-world-νcast⊑νcast-permuteᵀ`;
  - `rel-world-νcast⊑-permuteᵀ`;
  - `rel-world-⊑νcast-permuteᵀ`.

  Consequently every ordinary Nu-term-imprecision constructor involving
  `Λ`, `ν`, or `ν ★` now has a direct arbitrary-permutation boundary,
  except the runtime-bullet constructors, which remain intentionally outside
  the no-bullet theorem.

### 2026-07-17

- Strengthened `RelStoreRenameⁱ` and `RelCtxRenameⁱ` so every matched target
  entry contains the canonical renamed imprecision derivation. In nominal
  notation, a source entry

  \[
    A \sqsubseteq_p B
  \]

  is related only to the target entry

  \[
    \pi_L A
      \sqsubseteq_{\pi p}
    \pi_R B,
  \]

  modulo the endpoint equalities already carried by the world relation.
  Previously the target entry could contain an unrelated derivation
  `p′`. That weaker definition preserved endpoint typing but was
  insufficient for the indexed variable rule: two derivations of the same
  type-imprecision proposition need not be definitionally equal.
- Reproved all three binder-lifting squares with this stronger invariant.
  Matched `∀`, source-only `ν`, and target-only `ν` lifting now preserve the
  exact renamed witness in every stored and term-context entry. This changes
  only proof-side world-permutation evidence; neither term imprecision nor
  type imprecision gained a rule.
- Proved `rel-ctx-rename-lookupⁱ`. If

  \[
    \Gamma(x)=A\sqsubseteq_p B,
  \]

  then the permuted context contains at the same term-variable position the
  entry

  \[
    (\pi\Gamma)(x)
      = \pi_L A\sqsubseteq_{\pi p}\pi_R B.
  \]

  Hence `rel-world-x-permuteᵀ` supplies the first complete constructor clause
  of the general admissibility recursion.
- Added the exact context-extension square and the direct clauses for
  `blame`, abstraction, and application. In particular, the abstraction
  clause recurses under

  \[
    x : \pi_L A\sqsubseteq_{\pi p_A}\pi_R A'
  \]

  and reconstructs

  \[
    \lambda x.N \sqsubseteq \lambda x.N'
      : \pi_L(A\to B)\sqsubseteq
        \pi_R(A'\to B').
  \]

- Proved arbitrary-permutation transport for widening coercions on both
  endpoints and for the associated seal-store invariant. Together with the
  existing narrowing transport, this gives one coherent target package

  \[
    \mathsf{CastMode}(\mu),\quad
    \mathsf{SealStore}(\mu,\Sigma),\quad
    \mu;\Sigma\vdash c:A\mathrel{\trianglelefteq}B
  \]

  at each endpoint. The target mode is selected by the same
  `CastModeRenamer` that maps the coercion and seal evidence.
- Used those packages to prove the four generic one-sided cast clauses:
  `rel-world-cast⊒⊑-permuteᵀ`, `rel-world-cast⊑⊑-permuteᵀ`,
  `rel-world-⊑cast⊒-permuteᵀ`, and
  `rel-world-⊑cast⊑-permuteᵀ`. These clauses introduce no new imprecision
  shapes; they rebuild the existing one-node cast constructors around the
  recursively permuted term relation.
- The next boundary is paired reveal/conceal and paired widening in
  `conv⊑convᵀ`, followed by the four one-sided reveal/conceal clauses. Their
  main extra obligation is permutation of `StoreCorresponds`, since the
  conversion must continue to reveal exactly the two renamed seal names.
- Proved `rel-store-rename-correspondenceⁱ` for both ways that stores record a
  logical pair:

  \[
    \operatorname{store\text{-}matched}
      (\alpha,A,\beta,B,p)
    \qquad\text{and}\qquad
    \operatorname{store\text{-}link}
      (\alpha,A,\beta,B,p).
  \]

  The result preserves the exact renamed witness
  \(\pi p\), not merely the four renamed endpoints. Thus crossed stores,
  whose physical entries are independent and whose logical pairing is a
  link, are closed under the same world permutation as ordinary matched
  stores.
- Proved the four general conversion transports
  `left-reveal-rel-permute`, `right-reveal-rel-permute`,
  `left-conceal-rel-permute`, and `right-conceal-rel-permute`. Each uses the
  canonical action

  \[
    (\pi\mu)(X)=\mu(\pi^{-1}X)
  \]

  on the conversion mode and normalizes the renamed physical store to the
  corresponding projection of the target related world.
- Proved `rel-world-paired-conversion-permute` and
  `rel-world-paired-cast-permute`. The latter handles both exact paired
  reveal/conceal and the paired-widening alternative, keeping the mode,
  seal-store evidence, and widening typing synchronized on both endpoints.
  Consequently `rel-world-conv⊑conv-permuteᵀ` closes the paired-cast
  constructor in the eventual recursion.
- Proved all four one-sided conversion clauses and the ordinary
  quotient-to-term clause `rel-world-up⊑up-permuteᵀ`. The remaining
  coercion boundary is the two crossed quotient-to-term constructors. Their
  fixed modes are the two adjacent orders

  \[
    \mathsf{inst}(\mathsf{ext}(\mu))
    \qquad\text{and}\qquad
    \mathsf{ext}(\mathsf{inst}(\mu)).
  \]

  An arbitrary permutation need not leave either fixed order unchanged.
  The next audit should determine the smallest single premise invariant that
  subsumes `up⊑upᵀ`, `crossed-up⊑upᵀ`, and
  `crossed-left-up⊑upᵀ` without adding another syntax-shaped relation rule.
- Replaced that three-constructor family with one `up⊑upᵀ` rule and the
  genuine reusable premise `QuotientWideningPair`. It has two cases:

  \[
    \begin{array}{ll}
    \text{identity pair:}&
      \mathsf{id};\Sigma_L\vdash u:D\sqsubseteq A,
      \quad
      \mathsf{id};\Sigma_R\vdash u':D'\sqsubseteq A',\\[2mm]
    \text{cast-mode pair:}&
      \mathsf{CastMode}(\mu),
      \ \mathsf{SealStore}(\mu,\Sigma_L),
      \ \mu;\Sigma_L\vdash u:D\sqsubseteq A,\\
    & \mathsf{CastMode}(\mu'),
      \ \mathsf{SealStore}(\mu',\Sigma_R),
      \ \mu';\Sigma_R\vdash u':D'\sqsubseteq A'.
    \end{array}
  \]

  The first case retains the ordinary compiled-cast route. The second
  subsumes both adjacent `inst`/`ext` orders and is closed under arbitrary
  independent endpoint permutations. This removes two term-imprecision
  constructors instead of adding another permutation-specific constructor.
- Updated the two crossed administrative derivations to use
  `quotient-cast-widening`, and updated compilation and the quotient
  regression example to use `quotient-id-widening`. The source and target
  typing projections now analyze the widening-pair premise while retaining a
  single outer `up⊑upᵀ` case.
- Proved `rel-world-quotient-widening-pair-permute`; therefore
  `rel-world-up⊑up-permuteᵀ` now covers identity, direct crossed, reverse
  crossed, and all subsequent permutations through one derivation clause.
- Removed the `StoreDetWf` premise from `⊑cast⊑idᵀ`. The conclusion
  already carries the final type-imprecision derivation explicitly, and the
  source- and target-typing projections never used store determinacy. More
  importantly, arbitrary dependency-preserving permutations need not preserve
  the age ordering built into `StoreDetWf`, so retaining it would have imposed
  an unrelated obstruction on permutation admissibility.
- Proved the target identity-cast clause
  `rel-world-⊑cast⊑id-permuteᵀ`. In nominal form, if

  \[
    \mu_{\mathsf{id}};\Sigma_R
      \vdash c' : A' \mathrel{\trianglelefteq} B'
  \]

  and the bodies are related after applying \(\pi_L\) and \(\pi_R\), then

  \[
    \pi_L M
      \sqsubseteq
    (\pi_R M')\langle \pi_R c'\rangle
      : \pi_L A \sqsubseteq \pi_R B'.
  \]

  The seal-store premise at the target is reconstructed directly: the
  identity-only mode permits no seal name, so
  `SealModeStore★ id-onlyᵈ Σ` holds for every store \(\Sigma\).
- Added the direct constant and arithmetic clauses
  `rel-world-κ-permuteᵀ` and `rel-world-⊕-permuteᵀ`. Base types,
  numeric constants, and the addition operator contain no type names, so the
  permutation action is definitionally inert and only the operand relations
  recurse.
- Proved `rel-store-rename-prefix-invⁱ`. If

  \[
    \rho_0 \preccurlyeq \rho^+,
    \qquad
    \varpi : \rho^+ \rightsquigarrow \delta^+,
  \]

  then there is a suffix \(\delta_0\) such that

  \[
    \varpi_0 : \rho_0 \rightsquigarrow \delta_0,
    \qquad
    \delta_0 \preccurlyeq \delta^+.
  \]

  The proof follows the prefix and the proof-relevant store renaming in
  lockstep; therefore matched, left-only, right-only, and linked entries all
  preserve exactly the same prefix depth.
- Used that inversion to prove
  `rel-world-allocation-prefix-permuteᵀ`. The recursive body is transported
  at the exposed suffix world, endpoint typing is transported at the full
  world, and the single existing prefix rule reattaches the target prefix.
  Hence every allocation-producing trace remains covered by one structural
  invariant rather than separate matched, one-sided, and crossed rules.
- The ordinary structural helper layer is now complete. The mutual no-bullet
  recursion has direct clauses for variables, `blame`, abstraction,
  application, constants, arithmetic, casts, conversions, `Λ`, `ν`, `ν ★`,
  quotient boundaries, and allocation prefixes. Its remaining definition
  boundary is confined to `swapRight-bodyᵀ` and `swapLeft-bodyᵀ`: an
  arbitrary outer permutation destroys their fixed two-lift presentation.
  The next step is to express their already-proved
  fresh-extension-then-adjacent-swap factorization in a form closed under
  composition with the outer permutation, and then assemble the mutual
  recursion without adding another syntax-specific imprecision rule.

### Crossed bodies as semantic world embeddings

- The fixed two-lift presentation is not itself closed under arbitrary
  permutation. This is now a checked obstruction, not merely a failed proof
  attempt. Every target of `LiftStoreⁱ` excludes a projected store entry at
  index zero on both endpoints:

  \[
    (0,A) \notin \mathsf{leftStore}(\rho^+),
    \qquad
    (0,B) \notin \mathsf{rightStore}(\rho^+).
  \]

  The lemmas `swap01-lift-left-obstruction` and
  `swap01-lift-right-obstruction` then show that an adjacent permutation can
  move an older entry to zero, making it impossible to reconstruct another
  `LiftStoreⁱ` witness. Consequently the crossed-body proof must preserve the
  semantic related-store shape needed by the term relation, rather than
  demand a new syntactic lift decomposition.
- Introduced `StoreProjectionEmbeddingⁱ`. For endpoint renamings
  \(\tau_L\) and \(\tau_R\), it records exactly

  \[
  \begin{aligned}
    \tau_L\,\mathsf{leftStore}(\rho)
      &\subseteq \mathsf{leftStore}(\delta),\\
    \tau_R\,\mathsf{rightStore}(\rho)
      &\subseteq \mathsf{rightStore}(\delta).
  \end{aligned}
  \]

  This projection-only notion was sufficient for endpoint typing but not for
  the term relation: allocation-prefix inversion and paired reveal/conceal
  also need the related-store entry shape. The checked world invariant is
  therefore the stronger `RelStoreEmbeddingⁱ`. It preserves whether each
  entry is matched, source-only, target-only, or linked, and requires the four
  endpoint names and types to be the appropriate renamings. Crucially, a
  target matched/link entry may contain a different proof of its
  type-imprecision proposition. Thus the invariant retains exactly the
  structural information used by term imprecision without reviving the
  proof-relevance obstruction in `LiftStoreⁱ`.
- `RelWorldEmbeddingⁱ` combines this structural store embedding with
  well-scoped endpoint renamings, left inverses, coercion-mode renamers, the
  assumption action, and the renamed term context. The structural invariant
  implies the exact projection equations

  \[
  \begin{aligned}
    \mathsf{leftStore}(\delta)
      &= \tau_L\,\mathsf{leftStore}(\rho),\\
    \mathsf{rightStore}(\delta)
      &= \tau_R\,\mathsf{rightStore}(\rho).
  \end{aligned}
  \]

  Hence `rel-world-source-typing-embed` and
  `rel-world-target-typing-embed` transport endpoint typing directly. An
  exact `RelWorldPermutationⁱ` induces a world embedding by forgetting only
  the identity of the stored type-imprecision proofs.
- Proved that coercion-mode renamers compose. If

  \[
    \mathsf{ModeRename}(\tau,\mu,\nu),
    \qquad
    \mathsf{ModeRename}(\upsilon,\nu,\xi),
  \]

  then

  \[
    \mathsf{ModeRename}(\upsilon\circ\tau,\mu,\xi).
  \]

  The composed `CastModeRenamer` also composes seal preimages: a target seal
  name is pulled back first through \(\upsilon\), then through \(\tau\).
- Proved composition for assumption transport, well-formed renamings, left
  inverses, and structural store embeddings. Also proved
  `rel-store-embedding-prefix-invⁱ`, so an allocation prefix can be exposed
  after embedding just as it can after an exact permutation. These components
  yield
  `rel-world-embedding-[]-composeⁱ`, the empty-term-context composition
  theorem required by the crossed wrappers. The restriction to the empty
  context is exact here: both crossed-body constructors are closed terms.
- Constructed both primitive crossed embeddings:

  \[
  \begin{array}{c|cc}
    & \text{left endpoint} & \text{right endpoint} \\
    \hline
    \text{right-crossed}
      & \mathsf{suc}
      & \mathsf{ext}(\mathsf{suc}) \\
    \text{left-crossed}
      & \mathsf{ext}(\mathsf{suc})
      & \mathsf{suc}.
  \end{array}
  \]

  The opposite endpoint order is expressed only by these two renamings; no
  new term-imprecision constructor or coercion-specific rule is introduced.
- Finally proved `crossed-right-then-permutation-embeddingⁱ` and
  `crossed-left-then-permutation-embeddingⁱ`. For example, composing the
  right-crossed embedding with arbitrary outer permutations
  \(\pi_L,\pi_R\) produces the endpoint actions

  \[
    \alpha \mapsto \pi_L(\mathsf{suc}\,\alpha),
    \qquad
    \beta \mapsto
      \pi_R(\mathsf{ext}(\mathsf{suc})\,\beta),
  \]

  together with the composed structural store embedding, assumption action,
  mode action, and inverse maps. Thus the crossed factorization is now stable
  under every dependency-preserving outer permutation despite the failure of
  fixed lift reconstruction.
- Completed the remaining paired-conversion prerequisite. The lemmas
  `rel-store-embedding-matched∈ⁱ` and
  `rel-store-embedding-link∈ⁱ` transport the two representations of a
  logical seal pair through the structural embedding. Their conclusion first
  exposes all five target witnesses

  \[
    \alpha', A', \beta', B', p'
  \]

  and only then states the four endpoint equalities and target membership.
  This witness-first order matters operationally to Agda: the equivalent
  interleaved existential statement made dependent constraint solving
  diverge. The wrapper `rel-store-embedding-correspondenceⁱ` now proves

  \[
    \mathsf{Corresponds}_{\rho}(\alpha,A,\beta,B,p)
    \Longrightarrow
    \exists \alpha',A',\beta',B',p'.
      \begin{cases}
        \alpha' = \tau_L\alpha,\\
        A' = \tau_L A,\\
        \beta' = \tau_R\beta,\\
        B' = \tau_R B,\\
        \mathsf{Corresponds}_{\delta}
          (\alpha',A',\beta',B',p').
      \end{cases}
  \]

  The target proof \(p'\) is intentionally existential rather than the
  canonical renamed source proof.
- The next boundary is to state the mutual no-runtime-bullet naturality
  recursion over `RelWorldEmbeddingⁱ`.
  Ordinary permutation clauses enter through the canonical
  permutation-to-embedding map; the two crossed clauses enter through the
  composed embeddings above. Completing that recursion will derive and then
  delete the two specialized crossed-body constructors.
- Began that recursion boundary with the embedding-native structural layer:
  `rel-world-x-embedᵀ`, `rel-world-embedding-ctx-∷ⁱ`,
  `rel-world-ƛ-embedᵀ`, and `rel-world-blame-embedᵀ`. The variable clause
  uses the proof-relevant renamed context, abstraction extends that context
  by the canonically renamed argument relation, and blame uses the general
  target-typing transport.
- Proved `rel-world-allocation-prefix-embedᵀ`. Structural store-embedding
  inversion exposes a target suffix and prefix; the recursive body is related
  at that suffix, while the full-world endpoint typings are transported and
  the one existing `allocation-prefixᵀ` rule reattaches the prefix. Thus the
  allocation case remains one clause even after replacing exact permutations
  by the more general crossed embedding.
- The next constructor family is coercions and conversions. Narrowing,
  widening, seal-store evidence, and paired reveal/conceal must be restated
  against the structural projection equations. After those shared transports,
  the ordinary and quotiented cast clauses can be inserted into the mutual
  recursion without changing either term-imprecision judgment.
- Completed the coercion-mode action for a general embedding. If

  \[
    \psi(\tau\alpha)=\alpha,
  \]

  define the target mode by pullback,

  \[
    (\tau_*\mu)(\beta)=\mu(\psi\beta).
  \]

  Then

  \[
    \mathsf{ModeRename}(\tau,\mu,\tau_*\mu).
  \]

  This is enough for reveal and conceal conversions: their distinguished seal
  name becomes \(\tau\alpha\), their stored type becomes \(\tau A\), and the
  conversion endpoints and coercion are renamed uniformly. General
  narrowing, widening, and `SealModeStore★` instead use the embedding's
  `CastModeRenamer`, which additionally supplies preimages for every target
  seal permission.
- Proved embedding transport for paired reveal and conceal. From

  \[
    \mathsf{Corresponds}_{\rho}(\alpha,A,\beta,B,p)
  \]

  the structural embedding produces some \(p'\) such that

  \[
    \mathsf{Corresponds}_{\delta}
      (\tau_L\alpha,\tau_L A,\tau_R\beta,\tau_R B,p').
  \]

  Thus the conversion modes on the two endpoints remain independent, while
  the logical seal pair remains synchronized by the related store. No paired
  type-instantiation rule is needed.
- Lifted every ordinary cast and conversion clause to
  `RelWorldEmbeddingⁱ`: paired casts, one-sided reveal/conceal, source and
  target narrowing or widening, the target identity-only cast, and quotient
  widening. In nominal notation, the paired cast clause now has the form

  \[
  \begin{aligned}
    &\gamma\vdash M\sqsubseteq M' : A\sqsubseteq A',\\
    &(c,c') : (A,A')\Longrightarrow(B,B')
    \\
    &\qquad\Longrightarrow
    \delta\vdash
      \tau_L(M\langle c\rangle)
      \sqsubseteq
      \tau_R(M'\langle c'\rangle)
      : \tau_L B\sqsubseteq\tau_R B'.
  \end{aligned}
  \]

  These are derived transports only; the term-imprecision definition is
  unchanged.
- Proved that a structural world embedding lifts under a matched fresh
  universal binder. The store theorem constructs \(\delta^{\forall}\) and
  establishes

  \[
    \mathsf{RelStoreEmbedding}
      (\operatorname{ext}\tau_L,
       \operatorname{ext}\tau_R,
       \rho^{\forall},
       \delta^{\forall}),
  \]

  while preserving the target `LiftStoreⁱ` witness. Together with context
  lifting, extended inverse maps, and extended mode renamers, this yields
  `rel-world-embedding-lift∀ⁱ` and the embedding-native `Λ` clause. Hence the
  matched polymorphic introduction case is now ready for the mutual
  no-runtime-bullet recursion.
- The next sub-boundary is the corresponding one-sided binder lifting used by
  `Λ` on only the less-precise side and by one-sided `ν` cases. After the left
  and right variants are available, the mutual recursion can cover all
  binder-shaped constructors and invoke the already-composed crossed
  embeddings at the two administrative swap leaves.
- Completed both one-sided binder lifts. A source-only binder extends only the
  source embedding and its inverse,

  \[
    (\tau_L,\tau_R)
      \longmapsto
    (\operatorname{ext}\tau_L,\tau_R),
  \]

  whereas a target-only binder extends only the target side,

  \[
    (\tau_L,\tau_R)
      \longmapsto
    (\tau_L,\operatorname{ext}\tau_R).
  \]

  The associated store and context lemmas preserve `LiftLeftStoreⁱ` and
  `LiftRightStoreⁱ` witnesses and construct structural embeddings at the
  lifted worlds. The source-only `Λ` clause is now also proved over the
  general embedding.
- Thus all three recursive world transitions needed by polymorphic terms are
  available:

  \[
  \begin{array}{c|c}
    \text{binder relation} & \text{recursive endpoint action} \\
    \hline
    \forall/\forall
      & (\operatorname{ext}\tau_L,
         \operatorname{ext}\tau_R) \\
    \forall/\star
      & (\operatorname{ext}\tau_L,\tau_R) \\
    \star/\forall
      & (\tau_L,\operatorname{ext}\tau_R).
  \end{array}
  \]

  The remaining binder work is local to the `ν` constructors: their reveal or
  widening coercion lives under the freshly extended store and must be
  normalized against these three world transitions. Once those transports
  are restated for embeddings, the mutual no-runtime-bullet recursion can be
  written exhaustively.

### 2026-07-17

- Completed the ordinary `ν` transport under an arbitrary structural world
  embedding. If the endpoint renamings are `τₗ` and `τᵣ`, the fresh
  reveal conversions are transported under `ext τₗ` and `ext τᵣ`, and
  the three term orientations are reconstructed:

  \[
    \nu X.M \sqsubseteq \nu Y.M',
    \qquad
    \nu X.M \sqsubseteq M',
    \qquad
    M \sqsubseteq \nu Y.M'.
  \]

  The endpoint normalization uses

  \[
    (\operatorname{ext}\tau)(\uparrow A)
      = \uparrow(\tau A).
  \]

- Completed the analogous `ν\star` family. Here the seal permission and
  widening derivation move together:

  \[
    (\mu,\mathsf{seal},s:C\sqsubseteq\uparrow B)
      \longmapsto
    (\tau_*\mu,\mathsf{seal}',
       \tau s:\tau C\sqsubseteq\uparrow(\tau B)).
  \]

  This supplies matched, source-only, and target-only `ν\star` clauses
  without coupling conversion to type instantiation.

- Proved the mutually recursive embedding admissibility theorems
  `rel-world-embed-no•ᵀ` and `rel-world-embed-no•ᵀᵖ`. In nominal form, the
  ordinary theorem states that if

  \[
    E:(\Phi,\Gamma,\rho)
      \hookrightarrow_{\tau_L,\tau_R}
      (\Psi,\Gamma',\rho'),
    \qquad
    \Phi;\Gamma;\rho\vdash M\sqsubseteq M':A\sqsubseteq B,
  \]

  and neither endpoint contains a runtime bullet, then

  \[
    \Psi;\Gamma';\rho'\vdash
      \tau_L M\sqsubseteq\tau_R M'
      :\tau_L A\sqsubseteq\tau_R B.
  \]

  The recursion is exhaustive. It covers variables, abstraction,
  application, `Λ`, all six ordinary and `★`-allocating `ν` orientations,
  allocation prefixes, paired and one-sided conversions, narrowing and
  widening casts, constants, arithmetic, and both quotient constructors.
  The three runtime-bullet constructors are impossible by `No•`.

- Derived permutation admissibility as the immediate corollaries
  `rel-world-permute-no•ᵀ` and `rel-world-permute-no•ᵀᵖ`, using the canonical
  map from a related-world permutation to a structural embedding. Thus an
  arbitrary well-formed permutation of both worlds now acts uniformly on
  terms, endpoint types, coercions, stores, contexts, and the proof-relevant
  imprecision index.

- Removed `swapRight-bodyᵀ` and `swapLeft-bodyᵀ` from
  `QuotientedTermImprecision`. They were syntax-specific proof rules whose
  role is now admissible. The crossed lemmas are one-line applications of
  the general theorem to the two primitive embeddings:

  \[
  \begin{aligned}
    (\mathsf{suc},\operatorname{ext}\mathsf{suc}) &:
      M\sqsubseteq M'
      \Longrightarrow
      \uparrow M\sqsubseteq
        \operatorname{ext}(\mathsf{suc})M',\\
    (\operatorname{ext}\mathsf{suc},\mathsf{suc}) &:
      M\sqsubseteq M'
      \Longrightarrow
      \operatorname{ext}(\mathsf{suc})M
        \sqsubseteq\uparrow M'.
  \end{aligned}
  \]

  The four bespoke crossed endpoint-typing helpers became dead code and were
  deleted as well. The next boundary is to use permutation admissibility as
  the general `transportNo•Terms` implementation inside weak one-step
  results, then expose the remaining one-step derivation recursion between
  these checked leaves and the terminal DGG theorem.

- Factored the opposite-order allocation transports through one structural
  invariant. Two successive store lifts induce the world embedding

  \[
    (\tau_L,\tau_R)
      = (\mathsf{suc}\circ\mathsf{suc},
         \mathsf{suc}\circ\mathsf{suc}),
  \]

  from the original world to the crossed world. Hence, for terms with no
  runtime bullet,

  \[
    M\sqsubseteq M' : A\sqsubseteq B
    \quad\Longrightarrow\quad
    \uparrow\uparrow M\sqsubseteq\uparrow\uparrow M'
      : \uparrow\uparrow A\sqsubseteq\uparrow\uparrow B.
  \]

  This is `crossed-double-bodyᵀ`; it is an immediate application of general
  embedding admissibility, not a new term-imprecision rule.

- Proved that a related-store prefix induces ordinary inclusions of both
  endpoint stores. Combining those inclusions with weakening gives
  `crossed-double-prefix-bodyᵀ`: the double-shifted relation remains valid
  after arbitrary administrative store entries are prefixed to the crossed
  store.

- Constructed `WeakOneStepTransport` for both opposite-order direct quotient
  leaves. In each case the recorded store-change traces compute
  definitionally to two shifts, and the six-entry crossed store is handled by
  the prefix theorem. No equality transport, new syntax-specific precision
  rule, or coupling between conversion and instantiation is required. The
  next sub-boundary is to propagate this transport invariant through the
  matched and one-sided `ν` frames, then make it an explicit component of
  the general weak one-step derivation recursion.

- Proved transport preservation for all six outer `ν` frames: matched,
  source-only, and target-only, each for ordinary reveal allocation and
  `ν\star` widening allocation. These frames retain the inner change lists,
  endpoint action, and result store, so their universal term transport is
  inherited exactly from the recursive result after the frame-specific
  reveal or widening evidence is reconstructed.

- Strengthened both weak outcome types. Their related alternatives now carry
  the result and its transport proof together:

  \[
    \mathsf{related}(R,T)
      : \mathsf{WeakOneStepOutcome}(M,N').
  \]

  The application and all six `ν` outcome maps now preserve this pair.
  Consequently the forthcoming dispatcher cannot silently return a result
  whose change trace lacks the permutation action needed by a later frame.
  Target-trace alignment was updated to retain the stronger input while using
  only its operational result. The focused module and `All.agda` both pass
  with no unsolved metas. The active boundary is now the total weak one-step
  recursion itself.

- Factored the three primitive one-allocation actions through structural world
  embeddings. For any bullet-free relation

  \[
    M \sqsubseteq M' : A \sqsubseteq B,
  \]

  the matched, source-only, and target-only lifts give, respectively,

  \[
  \begin{aligned}
    \uparrow M &\sqsubseteq \uparrow M'
      : \uparrow A \sqsubseteq \uparrow B,\\
    \uparrow M &\sqsubseteq M'
      : \uparrow A \sqsubseteq B,\\
    M &\sqsubseteq \uparrow M'
      : A \sqsubseteq \uparrow B.
  \end{aligned}
  \]

  Each conclusion remains valid under an arbitrary later related-store prefix.
  The identity-renaming equations for terms and coercions discharge the
  unchanged endpoint in the one-sided cases.

- Used these prefix-stable actions to construct exact
  `WeakOneStepTransport` witnesses for matched and target-only allocation,
  both for ordinary reveal allocation and `ν\star` widening allocation. The
  source-blame/target-allocation leaf now has the same target-only witness.

- Proved that weak-result transport is closed under sequential composition.
  If `R₁` transports the initial relation and `R₂` transports every relation
  in the world produced by `R₁`, then the composed weak result transports by

  \[
    T_{R_2 \circ R_1}(P)
      = T_{R_2}(T_{R_1}(P)).
  \]

  The theorem normalizes concatenated source and target change lists using
  the corresponding `applyTerms` and `applyTys` fusion equations. A dedicated
  silent-prefix corollary handles the common shape where the source catches up
  while the target is unchanged, followed by the target's distinguished step.

- Connected this composition theorem to the paired polymorphic catch-up
  proofs. Both ordinary reveal and `inst` widening now preserve transport
  through their complete value/blame split:

  \[
    \mathsf{catchup}(N,N')
      \Longrightarrow
    \mathsf{transport}
      \bigl(\mathsf{alloc}(\mathsf{catchup}(N),N')\bigr).
  \]

  Consequently the total dispatcher may call either paired allocation
  catch-up theorem without losing the recursive transport invariant. The next
  boundary is to define the structurally direct clauses of that dispatcher and
  then connect these checked polymorphic clauses at the canonical allocation
  cases.

- Audited the first application clause of the total dispatcher. A generic
  `WeakOneStepOutcome` retains the final relation, but it does not retain the
  fact that this relation has the canonical transported arrow index. That fact
  is required to relate the untouched arguments. In nominal form, recursive
  simulation of the function must return

  \[
  \begin{aligned}
    W &\sqsubseteq W' :
      T_L(A) \to T_L(B)
      \sqsubseteq
      T_R(A') \to T_R(B'),\\
    &\hspace{2.4cm}
      T(p_A) \mathbin{\mapsto} T(p_B),
  \end{aligned}
  \]

  rather than only an existentially indexed relation between equal endpoint
  types. This is proof-relevant: duplicate context assumptions mean that one
  cannot repair the lost index using an unrestricted proof-irrelevance
  argument.

- Added `WeakOneStepArrowResult` and `WeakOneStepArrowOutcome`, parallel to
  the existing universal-shaped result and outcome. The arrow result retains
  both the ordinary weak result and the canonical relation displayed above;
  its exceptional alternative still requires an actual source trace to
  `blame`.

- Proved the direct arrow-shaped related result and its transport-bearing
  outcome. Then proved the callback-free application-left outcome map. Given

  \[
    M \sqsubseteq M' : A \sqsubseteq A'
  \]

  with bullet-free arguments, it applies the recursive transport witness to
  obtain `T_L(M) \sqsubseteq T_R(M')` and combines that derivation directly
  with the retained canonical arrow result. Thus the application clause no
  longer assumes an external function capable of reconstructing information
  that the recursive outcome had forgotten.

- The next dispatcher sub-boundary is to propagate this arrow-shaped
  invariant through the weak-result constructors that can themselves produce
  arrow-typed results. After that closure theorem, the application-left clause
  can be placed directly in the mutual ordinary/arrow/universal recursion.

- Added the canonical projections
  `forget-weak-arrow-outcome` and `forget-weak-all-outcome`. The mutual
  dispatcher may therefore recurse at an elimination-specific shape, use its
  retained evidence in the enclosing frame, and then return the ordinary
  outcome expected by the terminal trace-alignment theorem.

- Proved `weak-one-step-reindexᵀ`. Given a weak result and a new derivation
  relating the same final terms at definitionally transported endpoint types,
  it replaces only the exposed result types, result precision witness, and
  related-term derivation. It preserves source and target traces, the result
  world, all three type-transport actions, and both store equations.
  `weak-one-step-reindex-preserves-transportᵀ` shows that its universal
  term-transport witness is unchanged.

- Used that operation to prove `weak-one-step-arrow-reindexᵀ` and its
  transport theorem. The endpoint equations are the normalized actions

  \[
  \begin{aligned}
    T_L(A \to B) &= T_L(A) \to T_L(B),\\
    T_R(A' \to B') &= T_R(A') \to T_R(B').
  \end{aligned}
  \]

  Thus later arrow-producing frame lemmas need only reconstruct the canonical
  final term relation; they can reuse the operational and world components of
  the ordinary weak result.

- The closure audit must still account for nested result shapes. For example,
  if an application returns another function, retaining only the outer
  function's domain/codomain split is insufficient unless the transported
  codomain precision is itself exposed canonically. The next step is therefore
  to formulate the minimal recursive type-transport coherence invariant shared
  by arrow and universal outcomes before multiplying shape-specific frame
  rules.

### Type-action coherence boundary

- Defined the normalized actions `transportArrowType` and
  `transportAllType`. They expose the endpoint equalities hidden by a weak
  result's lists of store changes. In nominal notation, if the result induces
  the type action (T_R), these definitions have the shapes

  \[
  \begin{aligned}
    \mathsf{transportArrowType}(R,p_A,p_B)
      &: T_R(A) \to T_R(B)
         \sqsubseteq T_R(A') \to T_R(B'),\\
    \mathsf{transportAllType}(R,q)
      &: \forall X.\,T_R^X(C)
         \sqsubseteq \forall X.\,T_R^X(C').
  \end{aligned}
  \]

- Defined `WeakOneStepTypeCoherence R`. It records the two equations

  \[
  \begin{aligned}
    \mathsf{transportArrowType}(R,p_A,p_B)
      &= T_R(p_A) \mathbin{\mapsto} T_R(p_B),\\
    \mathsf{transportAllType}(R,q)
      &= \forall T_R^X(q).
  \end{aligned}
  \]

  This is the minimal recursive invariant needed by application and
  polymorphic elimination. It retains the actual precision derivations, so it
  does not assume proof irrelevance; that would be invalid in contexts with
  duplicate imprecision assumptions.

- Proved coherence for an unchanged related state, reindexing, sequential
  weak-result composition, a silent source prefix, application-left framing,
  and all six matched/source-only/target-only `ν` and `ν★` frames. Hence a
  nested arrow or universal result keeps its canonical precision structure
  through every structural operation already used by the dispatcher.

- Strengthened `WeakOneStepOutcome`, `WeakOneStepArrowOutcome`, and
  `WeakOneStepAllOutcome`. Their related alternatives now carry all three
  components

  \[
    \mathsf{related}(R,
      \mathsf{WeakOneStepTransport}(R),
      \mathsf{WeakOneStepTypeCoherence}(R)).
  \]

  All outcome maps and forgetful projections preserve the new component.

- Proved primitive coherence for matched reveal allocation, matched `ν★`
  allocation, right-only reveal allocation, right-only `ν★` allocation, and
  the source-blame/right-allocation leaf. Each proof reduces to the canonical
  matched or right-lifting action recorded in the corresponding weak result.

- Proved primitive coherence for both opposite-order direct quotient leaves.
  Their two-allocation traces normalize to the same crossed double-lifting
  action on arrows and under `∀`. Thus type-action coherence does not impose an
  allocation order and does not need a new term-imprecision rule.

- Propagated coherence through the complete paired catch-up constructions for
  both ordinary reveal allocation and `ν★` allocation. Each construction is
  exhaustive over the source-value/source-blame split. The value branch
  composes frame coherence with matched-allocation coherence; the blame branch
  composes frame coherence with source-blame/right-allocation coherence.

- The active boundary is now the mutually recursive ordinary, arrow-shaped,
  and universal-shaped weak one-step dispatcher. Its recursive hypotheses can
  return outcomes that retain term transport and type-action coherence, so the
  first direct clauses can be added without another strengthening of the
  result interface. The first clauses should be the unchanged related leaves,
  application-left via `WeakOneStepArrowOutcome`, and the matched reveal and
  `ν★` canonical-allocation cases via the checked catch-up theorems.

### Precision-indexed dispatcher interface

- The application-right audit found the general form of the canonical-index
  requirement. If the recursive argument relation begins at

  \[
    M \sqsubseteq M' : A \sqsubseteq A' \;[p_A],
  \]

  the enclosing application needs the final relation specifically at
  (T_R(p_A)), not at an existential derivation relating the same endpoint
  types. This is the same requirement previously encountered only for arrows
  and universals.

- Defined `WeakOneStepIndexedResult p`. It contains a weak result (R) and
  the canonical final relation

  \[
    \operatorname{source}(R)
      \sqsubseteq
    \operatorname{target}(R)
      : T_R(A) \sqsubseteq T_R(A')
      \;[T_R(p)].
  \]

  `WeakOneStepIndexedOutcome p` pairs this result with term transport and
  type-action coherence, or supplies an actual source trace to `blame`.
  `weak-one-step-index-resultᵀ` is the checked bridge from a weak result whose
  recorded final index is propositionally the transported original index.

- Proved `nu-term-imprecision-transport-typesᵀ`, which simultaneously
  transports both endpoint types and the dependent precision index of a term
  relation. This isolates the dependent equality needed when a type action is
  normalized through `→` or `∀`.

- Proved that an indexed result at (p_A \mapsto p_B) yields the previous
  arrow-shaped result, and that an indexed result at `∀ⁱ q` yields the previous
  universal-shaped result. The conversions use exactly the two equations in
  `WeakOneStepTypeCoherence`; no proof-irrelevance principle is used.
  Consequently the dispatcher no longer needs three mutually maintained
  recursions. One recursion returning `WeakOneStepIndexedOutcome p` can derive
  the arrow or universal view only at an elimination site.

- Added the unchanged indexed related outcome. It has empty source and target
  tails and retains the input precision derivation definitionally.

- Proved indexed application-left framing. Recursive simulation of the
  function is viewed as an arrow result, the untouched arguments are
  transported, and the enclosing application returns an indexed result at the
  original codomain derivation (p_B).

- Proved indexed application-right framing. Given related bullet-free values
  (V \sqsubseteq V'), recursive simulation of the arguments produces

  \[
    T_R(V)\;T_R(M)
      \sqsubseteq
    T_R(V')\;T_R(M') : T_R(B) \sqsubseteq T_R(B')
      \;[T_R(p_B)].
  \]

  `weak-result-transport-arrow-termsᵀ` normalizes the transported function
  relation using arrow coherence. The exceptional branch lifts a genuine
  argument trace to `blame` through the value application frame and then uses
  application blame.

- Proved indexed contextual framing for all six `ν` families: matched,
  source-only, and target-only, each for ordinary reveal and `ν★`. Matched
  framing derives the universal view of the recursive body; one-sided framing
  uses the indexed body result directly. Source blame is lifted through source
  frames and remains unchanged for target-only frames.

- The active proof boundary is now a single derivation-recursive theorem with
  codomain `WeakOneStepIndexedOutcome p`. Its structural clauses for
  application and all `ξ-ν` reductions are represented by checked maps. The
  next step is to state the total dispatcher with its two projected `StoreWf`
  and runtime hypotheses, add the impossible value-head cases and these direct
  structural clauses, then connect canonical matched/right-only allocation.
  The remaining allocation-specific gap is not the result interface: it is to
  package the existing universal source-catchup construction with indexed
  transport and coherence so the allocation clauses can call it recursively.

### Indexed universal catch-up and paired lift worlds

- Defined `LeftCatchupIndexedAllResult q`. Besides the universal caught-up
  weak result, it records the source-value-or-blame invariant, term transport,
  and type-action coherence. Value, blame, one silent `keep` step, silent
  prefix composition, and the post-allocation `β-Λ•` step now construct this
  package directly.

- Lifted the universal administrative catch-up steps for reveal, conceal,
  narrowing, widening, and `gen` narrowing to the indexed package. These
  theorems only prepend a source `keep` step, so their precision index remains
  the index supplied by the recursive catch-up result.

- The `α/Λ` leaf exposes two `LiftLeftStoreⁱ` derivations from the same store:
  one belongs to the enclosing allocation, while the other belongs to the
  body relation obtained by inverting `Λ`. Their stores have identical names
  and types but may contain different proof-relevant precision witnesses.
  Therefore equality of the two stores is neither available nor required.

- Proved `paired-left-lift-rel-embeddingⁱ` and its world and fresh-prefix
  forms. They give an identity embedding between any two left lifts of the
  same base store. The construction is structural in the two lift
  derivations and ignores only the precision witnesses stored in entries;
  it does not identify precision derivations.

- Defined the identity permutation action `⊑-rename-idᵢ`. It need not equal
  its input proof object. What the dispatcher needs are the checked shape
  equations

  \[
  \begin{aligned}
    I(p_A \mapsto p_B) &= I(p_A) \mapsto I(p_B),\\
    I(\forall q) &= \forall I^X(q).
  \end{aligned}
  \]

  The first equation is `⊑-rename-id-arrowᵢ`; the second is
  `⊑-rename-id-allᵢ`. Equality-proof uniqueness is used only to reconcile two
  proofs of the same type-renaming equality under `∀`; no irrelevance
  principle is assumed for precision derivations or context membership.

- Proved `left-catchup-indexed-all-α-Λᵀ`. It moves the final body relation
  across the paired lift embedding and records the identity permutation
  action as its transport. The theorem assumes `No• V'`, exactly the runtime
  fact needed by the general no-bullet world-embedding theorem; matched
  allocation callers already possess this fact for the target value.

- Connected indexed universal catch-up to both matched allocation families:
  `weak-one-step-matched-ν↑-indexed-catchup-outcomeᵀ` and
  `weak-one-step-matched-νcast-indexed-catchup-outcomeᵀ` now return the general
  `WeakOneStepIndexedOutcome`. They reuse the existing exhaustive
  source-value/source-blame constructions and their transport/coherence
  proofs.

- The next boundary is the total derivation recursion itself. Its matched
  allocation clauses can now invoke indexed source catch-up without losing
  the canonical precision index. The immediate task is to state the
  dispatcher over a term-imprecision derivation, add unchanged and structural
  clauses, and use these two indexed matched-allocation outcomes at the first
  canonical `ν` and `ν★` leaves.

### Right extension across a pending source allocation

- The application-left runtime audit isolates one exceptional state. The
  source function is already a bullet-free value, while its argument may
  contain the unique pending runtime bullet. If the target function allocates
  a fresh name, ordinary `No•` transport cannot move that argument relation
  into the target-extended world.

- Proved that the two context actions commute:

  \[
    \mathord{\Uparrow}_{L}
      (\mathord{\Uparrow}_{R}\Phi)
    =
    \mathord{\Uparrow}_{R}
      (\mathord{\Uparrow}_{L}\Phi).
  \]

  The constructor-facing store and term-context commutation lemmas use the
  left-allocation name as the outermost related-context entry. This is the
  shape expected directly by `α⊑ᵀ`.

- Proved the converse factorization lemmas. If a world first performs a
  source-only allocation and the resulting world is then extended on the
  target, the square factors through a target extension of the original
  world:

  \[
  \begin{array}{ccc}
    (\rho,\gamma)
      & \xrightarrow{\;R\;} &
    (\rho_R,\gamma_R) \\
    {\scriptstyle L}\downarrow
      && \downarrow{\scriptstyle L} \\
    (\rho_L,\gamma_L)
      & \xrightarrow{\;R\;} &
    (\rho_{LR},\gamma_{LR}).
  \end{array}
  \]

  These are `left-right-store-factorⁱ` and
  `left-right-ctx-factorⁱ`. They preserve the concrete final store and
  context rather than replacing proof-relevant precision witnesses by
  equality.

- Proved `right-store-prefix-factorⁱ`. A right lift of a store carrying an
  administrative prefix factors into a right lift of the relational suffix
  and a corresponding prefix over the lifted suffix. This is the exact
  decomposition needed for an argument relation already wrapped by
  `allocation-prefixᵀ`; importantly, the lift applies only to the suffix and
  therefore preserves store length.

- Proved the direct pending-bullet transport
  `right-target-lift-α⊑ᵀ`. In nominal notation, its central premise and
  conclusion have the following form. Suppose

  \[
    L \sqsubseteq \uparrow_R N'
      : \forall X.\,C \sqsubseteq \uparrow_R B'
  \]

  in the target-extended base world, and suppose the source-only allocation
  makes `(\uparrow_L L)\,\bullet` well typed. Then the commuting allocation
  square derives

  \[
    (\uparrow_L L)\,\bullet
      \sqsubseteq \uparrow_R N'
      : C \sqsubseteq \uparrow_R B'
  \]

  in the combined world. The statement now gives the pre-extension precision
  derivation and the occurrence witness explicit types. This prevents Agda
  from leaving the base related context as an escaped metavariable.

- Proved the canonical index equation
  `⊑-target-lift-right-ν-shapeᵢ`. For

  \[
    p : C \sqsubseteq B
  \]

  in the source-allocation premise world, target lifting a source-only
  universal derivation has constructor shape

  \[
    T_R(\nu\,p) = \nu\,(T_R^L(p)).
  \]

  The occurrence witness on the right is existential because its particular
  equality proof is irrelevant to constructor selection. The proof uses the
  general source-transport equation `transport-ν-⊑ᵢ` plus equality-proof
  uniqueness only for the two proofs that identity renaming preserves the
  outer universal type. This lets the canonical right-lift index feed the
  direct `α⊑ᵀ` leaf without postulating precision-proof irrelevance.

- This establishes the difficult leaf but not yet the whole exceptional
  application argument. The next proof is a structural right-extension
  theorem for a source term satisfying `RuntimeOK` and a target term
  satisfying `No•`. Its `ok-no` branch reuses
  `right-lift-prefix-bodyᵀ`; its unique-bullet leaf uses
  `right-target-lift-α⊑ᵀ`; application, `ν`, primitive operation, and cast
  cases merely lift the recursive result through their existing relation
  constructors. The application-left dispatcher can then replace its
  residual exceptional alternative by that theorem when the recursive
  function step is a target-only allocation.

- Proved that structural theorem as the mutually recursive pair
  `right-target-lift-runtimeᵀ` and `right-target-lift-runtimeᵀᵖ`.  In
  nominal notation, let

  \[
    \Omega = (\alpha \sqsubseteq \star) :: \uparrow_L\Phi,
    \qquad
    \Omega_{LR}
      = (\alpha \sqsubseteq \star) ::
        \uparrow_L(\uparrow_R\Phi).
  \]

  If

  \[
    \Omega;\rho \vdash M \sqsubseteq M' : A \sqsubseteq B\;[p],
    \qquad
    \mathsf{RuntimeOK}(M),
    \qquad
    \mathsf{NoBullet}(M'),
  \]

  and `ρ` right-extends to `ρ_R` in `Ω_{LR}`, then

  \[
    \Omega_{LR};\rho_R \vdash
      M \sqsubseteq \uparrow_R M'
      : A \sqsubseteq \uparrow_R B\;[\uparrow_R^L p].
  \]

  The quotiented theorem has the identical shape with
  `A \sqsubseteq^p B`.  No term-imprecision constructor was added.  The proof
  factors `allocation-prefixᵀ`, uses the canonical `α⊑ᵀ` square at the
  unique runtime-bullet leaf, and otherwise follows the existing relation
  constructors.  It covers applications, primitive operations, ordinary
  `ν`, `ν★`, paired and one-sided casts, reveal/conceal conversions, and
  both quotient constructors.

- Added direct ordinary and quotiented normalization bridges between the raw
  structural embedding action and `↑_R^L`.  Added specialized wrappers for
  all six ordinary and `ν★` orientations.  Thus seal-mode renaming and
  reveal/widening transport remain inside the existing generic world-embedding
  lemmas rather than being repeated in the runtime recursion.

- Proved `weak-one-step-·₁-value-frameᵀ`.  If recursive simulation of the
  function has

  \[
    \chi_s = [], \qquad L_s = L,
  \]

  then the enclosing source application also takes zero steps.  Consequently
  its argument may satisfy `RuntimeOK`; only the target argument must satisfy
  `No•` so that the target tail can be lifted through the application frame.
  Transport and type-action coherence are inherited unchanged from the
  function result.

- The remaining application-left allocation boundary is now an action
  alignment, not a term-relation gap.  The existing right-only allocation
  leaf records the generic action `⊑-target-lift-rightᵢ` in the context
  `⇑ᴿᵢ Ω`, whereas the crossed structural theorem records the normalized
  action `⊑-target-under-leftᵢ` in `Ω_{LR}`.  The contexts are identified by

  \[
    \uparrow_L(\uparrow_R\Phi)
      = \uparrow_R(\uparrow_L\Phi),
  \]

  but the dependent precision derivations are not definitionally equal.  A
  direct equality attempt exposes proof-relevant renaming evidence and would
  require a separate derivation-recursive coherence proof.

  The smaller next obligation is instead to rebuild the right-only allocation
  leaf with `⊑-target-under-leftᵢ` as its transport action.  This does not need
  equality of precision derivations: the final reveal or widening constructor
  is allowed to choose the normalized conclusion index directly, while the
  inner target-bullet relation is transported only along the context
  commutation equality.  The new zero-source-step frame can then consume
  `right-target-lift-runtimeᵀ` directly for both right-only `ν` and `ν★`
  allocation leaves.

### 2026-07-18: indexed allocation and mode-permutation boundary

- Replaced the last crossed-action detour by direct assumption-renaming
  lemmas.  The two one-sided actions now act on a related assumption as

  \[
  (\mathsf{suc},\operatorname{ext}\mathsf{suc})
  \qquad\text{and}\qquad
  (\operatorname{ext}\mathsf{suc},\mathsf{suc}),
  \]

  and map it directly into the crossed related context.  Their proofs use
  composition and pointwise congruence of assumption renaming.  Consequently
  the mode action remains the one supplied by the same structural world
  embedding; there is no separate mode-specific term-imprecision rule.

- Made the general type-action coherence layer fully explicit.  In
  particular, transport through arrows and through `∀` now states the source
  and target substitution equations and the raw relation being transported.
  The composition theorem therefore records, without inferred holes, that

  \[
  T_{\chi_2}(T_{\chi_1}(p))
    \cong T_{\chi_2\circ\chi_1}(p)
  \]

  and that this action commutes with both arrow formation and the body of a
  universal type.  The equality is heterogeneous because the two sides can
  expose definitionally different context and endpoint indices.

- Closed the indexed matched ordinary-`ν` and matched-`ν★` catch-up
  leaves.  Each proof now makes the operational split required by the DGG:

  \[
  \begin{array}{ll}
  \text{source reaches a value}
    &\Longrightarrow \text{frame the recursive catch-up and use the matched
       allocation leaf},\\
  \text{source reaches blame}
    &\Longrightarrow \text{frame the blame trace and use the right-only
       allocation leaf}.
  \end{array}
  \]

  Thus the less-precise program is not allowed to choose blame merely because
  the simulation is weak; every blame outcome carries an actual source trace
  to `blame`.

- Closed the paired-lift `α/Λ` boundary.  Suppose two lifted stores
  `ρᵃ` and `ρᵇ` arise from the same base store.  The body relation is
  first extended by the fresh allocation in `ρᵇ`, then transported by the
  paired identity embedding to the corresponding extension of `ρᵃ`:

  \[
  (\alpha,\uparrow A)::\rho^b
    \vdash W\sqsubseteq V'
  \quad\Longrightarrow\quad
  (\alpha,\uparrow A)::\rho^a
    \vdash W\sqsubseteq V'.
  \]

  The induced term and type actions are identity renamings, but the two
  proof-relevant store witnesses are not equated.  The indexed theorem
  `left-catchup-indexed-all-α-Λᵀ` records the corresponding transport and
  arrow/`∀` coherence evidence.

- Completed the indexed administrative wrappers for universal narrowing,
  universal widening, and `gen` narrowing.  Their body coercions are now
  named explicitly and transported through the allocated store; no coercion
  is coupled to the bullet/type-instantiation rule.

- Strengthened the terminal trace-alignment consumer to retain the third
  component of `outcome-related`, namely type-action coherence.  Alignment
  still projects only the operational weak result, but it no longer discards
  the stronger invariant by matching an obsolete constructor shape.

- Validation completed for
  `proof/NuImprecisionSimulation.agda`, including
  `--no-allow-unsolved-metas`, and for
  `proof/NuDGGTraceAlignment.agda`.

- The next boundary is the total derivation recursion

  \[
  \Phi;\rho\vdash M\sqsubseteq M' : A\sqsubseteq_p B,
  \qquad M'\longrightarrow_{\chi}N'
  \quad\Longrightarrow\quad
  \mathsf{WeakOneStepIndexedOutcome}(p).
  \]

  Its unchanged, application-frame, and six `ν`-frame maps are already
  checked.  The next implementation step is to add the direct clauses for
  the canonical matched, one-sided, and crossed allocation-producing leaves,
  invoking the indexed catch-up theorems above, and then expose this recursion
  to the terminal DGG proof.

### 2026-07-18: direct indexed allocation leaves

- Packaged the three remaining one-sided allocation results at their original
  precision indices:


  \[
  \begin{array}{rcl}
  \nu X.\mathsf{blame} &\sqsubseteq& \nu X'.V',\\
  N &\sqsubseteq& \nu X'.V',\\
  N &\sqsubseteq& \nu \star.V'.
  \end{array}
  \]

  The corresponding theorems are
  `weak-one-step-source-blame-right-allocation-indexed-outcomeᵀ`,
  `weak-one-step-right-ν↑-indexed-outcomeᵀ`, and
  `weak-one-step-right-νcast-indexed-outcomeᵀ`.  Each theorem combines
  its existing weak result, term transport, and arrow/`∀` type-action
  coherence.  The first alternative still contains an actual source trace to
  `blame`; no unrestricted less-precise blame alternative was reintroduced.

- Packaged both crossed adjacent-allocation traces as indexed outcomes:

  \[
  \begin{array}{c@{\qquad}c}
  \mathsf{gen}_{\forall};\mathsf{inst}_{\forall}
    & \mathsf{gen};\forall\mathsf{inst},\\
  \mathsf{gen};\forall\mathsf{inst}
    & \mathsf{gen}_{\forall};\mathsf{inst}_{\forall}.
  \end{array}
  \]

  Operationally, the two sides allocate the same two names in opposite
  orders.  Relationally, both conclusions use the existing crossed action

  \[
    T_{\times\forall\forall}(p)
      = \mathsf{crossedLift}_{\forall\forall}(p).
  \]

  The new theorems
  `weak-one-step-direct-quotient-indexed-outcomeᵀ` and
  `weak-one-step-reverse-direct-quotient-indexed-outcomeᵀ` expose this
  action directly at the original body relation
  `p : F \sqsubseteq F'`.  No permutation or term-imprecision constructor was
  added.

- Added the general equality lemma `subst-cancel-sym`.  The crossed body
  witnesses had previously been transported backward along

  \[
    \operatorname{rename}(\operatorname{ext}\,\mathsf{suc},
      \uparrow F)
      = \uparrow\uparrow F
  \]

  so that their endpoints matched the concrete opposite-order traces.  The
  indexed wrapper transports the same endpoint forward.  The new lemma proves

  \[
    \operatorname{subst}_P(e)
      (\operatorname{subst}_P(e^{-1})(x)) = x,
  \]

  once on the source endpoint and once on the target endpoint.  This is the
  complete extra equality needed at the crossed quotient boundary.

- Validated `proof/NuImprecisionSimulation.agda` both normally and with
  `--no-allow-unsolved-metas`, then rechecked
  `proof/NuDGGTraceAlignment.agda` and the aggregate `All.agda` module.

- The leaf-level allocation interface is now complete: canonical matched,
  right-only, source-blame/right-only, and both crossed quotient orientations
  all return `WeakOneStepIndexedOutcome` at the transported original index.
  The remaining prerequisite for the total weak one-step dispatcher is not
  another allocation rule.  It is the total universal source-catch-up
  recursion

  \[
  \begin{aligned}
    &\Phi;\rho \vdash N \sqsubseteq V'
       : \forall X.C \sqsubseteq \forall X.C'\;[\forall q],\\
    &\mathsf{RuntimeOK}(N),\quad
      \mathsf{Value}(V'),\quad \mathsf{NoBullet}(V')\\
    &\hspace{2em}\Longrightarrow
      \mathsf{LeftCatchupIndexedAllResult}(q).
  \end{aligned}
  \]

  Its terminal value and blame cases, silent-step composition, `β-Λ•`,
  one-layer reveal/conceal, universal narrowing/widening, and `gen` narrowing
  clauses are already checked.  The next implementation boundary is to join
  those clauses into one exhaustive recursion over the quotiented term
  relation, including transport through `allocation-prefixᵀ`.  Once that
  theorem is total, the matched ordinary-`ν` and matched-`ν★` dispatcher
  clauses can call the indexed catch-up outcomes directly.

### 2026-07-18: pending-prefix universal catch-up boundary

- Generalized the universal catch-up infrastructure around a pending store
  prefix.  The invariant is now stated before recursion: if

  \[
    \rho_0 \preccurlyeq \rho^+
    \quad\text{and}\quad
    \Phi;\rho_0 \vdash N \sqsubseteq V'
      : \forall X.C \sqsubseteq \forall X.C'\;[\forall q],
  \]

  then the catch-up result is constructed directly in the outer world
  `\rho^+`.  This is stronger than lifting a completed result afterward.
  A source catch-up may allocate new names, and those new names must precede
  the already-pending prefix entries in the operational store.

- Proved transitivity of `StoreImpPrefix` and the two prefix-aware catch-up
  combinators:

  \[
  \begin{aligned}
    &\mathsf{terminal}_{\rho_0\preccurlyeq\rho^+},\\
    &\mathsf{prependKeep}_{\rho_0\preccurlyeq\rho^+}.
  \end{aligned}
  \]

  The first weakens a terminal value-or-`blame` relation into `\rho^+`.
  The second prepends one source `keep` step while retaining the relation at
  `\rho_0` and the catch-up result at `\rho^+`.  Their Agda names are
  `left-catchup-indexed-all-prefix-relatedᵀ` and
  `left-catchup-indexed-all-prefix-prepend-keepᵀ`.

- Proved the corresponding prefix-aware `β-Λ•` theorem
  `left-catchup-indexed-all-prefix-post-allocation-β-Λ•ᵀ`.
  In nominal notation its operational component is

  \[
    (\Lambda X.\,W)[\alpha]
      \longrightarrow W,
  \]

  while the final value relation is weakened from `\rho_0` to `\rho^+`.

- Factored the identity action on arbitrary relation worlds.  The new
  `identity-store-rel-embeddingⁱ` and `identity-world-embeddingⁱ` do not
  identify proof-relevant store witnesses; they embed a world into itself.
  Consequently `identity-bodyᵀ` proves

  \[
    \Phi;\rho\vdash L\sqsubseteq L' : A\sqsubseteq B\;[p]
    \quad\Longrightarrow\quad
    \Phi;\rho\vdash L\sqsubseteq L' : A\sqsubseteq B\;[I(p)]
  \]

  for bullet-free terms, where `I = ⊑-rename-idᵢ`.  This is the transport
  needed when the pending prefix produces an arbitrary outer store.

- Closed the direct prefixed `α/Λ` leaf.  Given two left lifts `\rho^a`
  and `\rho^b` of the same base world and a pending extension

  \[
    (\alpha,\uparrow A)::\rho^a \preccurlyeq \rho^+,
  \]

  `left-catchup-indexed-all-prefix-α-Λᵀ` constructs the one-step trace

  \[
    (\Lambda X.\,W)[\alpha] \longrightarrow W
  \]

  and the final relation in `\rho^+`.  The relation first moves from
  `\rho^b` to `\rho^a` by the paired-lift identity embedding and is then
  weakened through the pending prefix.  Its transport action is uniformly
  `I`, independent of the shape of `\rho^+`.

- Audited the total recursion by temporarily exposing its terminal,
  prefix-composition, and direct `α/Λ` clauses to Agda's exhaustiveness
  checker.  After these clauses, the remaining top-level constructors are

  \[
  \begin{gathered}
    \mathsf{up},\quad \nu_L,\quad \nu_L^\star,\\
    \mathsf{cast}_L^{\mathord\sqsupseteq},\quad
    \mathsf{cast}_L^{\mathord\sqsubseteq},\quad
    \mathsf{cast}_R^{\mathord\sqsupseteq},\quad
    \mathsf{cast}_R^{\mathord\sqsubseteq},\\
    \mathsf{conv}_{LR},\quad
    \mathsf{reveal}_L,\quad \mathsf{conceal}_L,\quad
    \mathsf{reveal}_R,\quad \mathsf{conceal}_R.
  \end{gathered}
  \]

  In the `α` branch, canonical-form inversion reduces the residual cases to
  target-cast or prefix wrappers around `Λ`, plus the universal-cast and
  `gen` value forms.  Thus the next proof obligation is a single general
  cast-framing operation for indexed left catch-up.  It should transport an
  already-computed catch-up through one existing source or target cast
  constructor, rather than add another term-imprecision rule.  Once this
  operation is checked, the remaining `α` cases and the top-level cast cases
  share the same recursion principle.

### 2026-07-18: arbitrary-index universal cast framing

- Added structural source and target cast frames for weak one-step results.
  The source frame has the following nominal proof shape:

  \[
  \begin{array}{c@{\qquad}c}
    M & V' \\
    \mathrel{\Downarrow^{\chi_s}} & \mathrel{\Downarrow^0} \\
    W & V' \\
    \hline
    M\langle c\rangle & V' \\
    \mathrel{\Downarrow^{\chi_s}} & \mathrel{\Downarrow^0} \\
    W\langle \chi_s(c)\rangle & V'.
  \end{array}
  \]

  The frame preserves both `WeakOneStepTransport` and
  `WeakOneStepTypeCoherence`.  It does not add a term-imprecision
  constructor; the final cast relation is rebuilt from the transported
  original evidence.

- Factored the terminal argument shared by inert source casts.  If the inner
  catch-up ends in a value `W`, inertness gives

  \[
    \mathsf{Value}(W\langle c\rangle).
  \]

  If it ends in `blame`, the frame appends the existing reduction

  \[
    \mathsf{blame}\langle c\rangle \longrightarrow \mathsf{blame}.
  \]

  Thus the blame branch still contains a concrete source trace; it is not an
  unrestricted permission for the less-precise term to blame.

- Proved the exact universal coercion classifications

  \[
  \begin{aligned}
    c : \forall X.A \mathrel{\sqsupseteq} \forall X.B
      &\Longrightarrow \mathsf{Inert}(c),\\
    c : \forall X.A \mathrel{\sqsubseteq} \forall X.B
      &\Longrightarrow
        \mathsf{Inert}(c)
        \;\lor\;
        \exists s.\;c=\mathsf{inst}(\forall X.B,s).
  \end{aligned}
  \]

  Reveal and conceal conversions between two universal types are also inert.
  These classifications deliberately require both endpoints to be universal:
  a coercion whose target alone is universal may be an `unseal` from a stored
  universal type.

- Added iterated preservation for narrowing and widening evidence through an
  arbitrary sequence of emitted `keep` and `bind` changes.  Added the analogous
  transport for the single-name reveal and conceal predicates.  The latter
  transports the distinguished seal name and its associated type as names are
  allocated.

- Closed the source narrowing, inert source widening, source reveal, and
  source conceal catch-up clauses.  Each has a prefix-aware form.  If

  \[
    \rho_0 \preccurlyeq \rho^+,
  \]

  the original coercion evidence and seal permission are weakened along the
  induced inclusion of left stores before framing the recursive result in
  `\rho^+`.

- Corrected an interface error discovered by the cast clauses.  Even when the
  endpoints of the inner relation are both universal, its proof index need not
  have the form `\forall q`; it may have the source-only form `\nu q`.  In
  particular, a source cast rule may hide

  \[
    \Phi;\rho \vdash M \sqsubseteq V'
      : \forall X.A \sqsubseteq \forall X.A'\;[p]
  \]

  for an arbitrary admissible index `p`.  Added the genuinely general package
  `LeftCatchupIndexedResult p`, together with arbitrary-index terminal and
  `keep`-prefix composition.  The source cast clauses now consume this general
  package and return the requested outer `\forall`-indexed result.  The older
  `LeftCatchupIndexedAllResult q` remains only where a theorem specifically
  needs the canonical outer index `\forall q`.

- The remaining source-widening boundary is now isolated exactly as

  \[
    c=\mathsf{inst}(\forall X.B,s).
  \]

  Its value branch performs `\beta\text{-inst}` and creates a `\nu\,\star`
  state; its blame branch is already covered by the generic cast-on-blame
  composition.  The administrative transition and its return to catch-up are
  now checked in the next boundary.

### 2026-07-18: `\beta`-inst-to-`\nu\,\star` handoff and cached proof layers

- Proved the exceptional source-widening value trace.  If the recursive
  catch-up produces a value `W`, then the source has the nominal reduction
  shape

  \[
  \begin{aligned}
    M\langle \mathsf{inst}(\forall X.B,s)\rangle
      &\mathrel{\Downarrow^{\chi_s}}
        W\langle
          \mathsf{inst}(\forall X.\chi_s(B),\chi_s(s))
        \rangle \\
      &\longrightarrow
        \nu\,\star\,W\,\chi_s(s).
  \end{aligned}
  \]

  The last arrow is the actual `\beta\text{-inst}` reduction.  The final
  relation is obtained from the existing source `\nu\,\star` frame, so this is
  a simulation-up-to administrative step rather than a new term-imprecision
  rule.

- Strengthened `LeftSilentIndexedResult p`.  A silent continuation now carries
  all four invariants needed by recursion:

  \[
  \begin{gathered}
    \text{a canonical indexed result at the transported }p,\\
    \mathsf{RuntimeOK}(W),\qquad
    \mathsf{WeakOneStepTransport},\qquad
    \mathsf{WeakOneStepTypeCoherence}.
  \end{gathered}
  \]

  Storing `RuntimeOK` in the package is essential: the trace may be hidden
  behind a transported coercion derivation, so the consumer should not depend
  on reducing the proof term definitionally to rediscover that the result is
  `\nu\,\star\,W\,s`.

- Added the exhaustive source-widening progress boundary.  For
  `c : \forall X.A \sqsubseteq \forall X.B`, exactly one of the following
  checked outcomes is returned:

  \[
  \begin{array}{c|c}
    \mathsf{Inert}(c),\ W\text{ a value}
      & \text{terminal catch-up} \\
    c=\mathsf{inst}(\forall X.B,s),\ W\text{ a value}
      & \text{silent }\beta\text{-inst-to-}\nu\,\star\text{ continuation} \\
    W=\mathsf{blame}
      & \text{terminal catch-up with an explicit blame trace.}
  \end{array}
  \]

- Proved `left-catchup-indexed-resume-silentᵀ`.  If a silent prefix transports
  `p` to `p_1`, and recursive catch-up closes the resulting relation at `p_1`,
  then their source traces compose and produce catch-up at the original `p`.
  The proof first canonicalizes the prefix endpoint types, then uses
  heterogeneous equality only at the composition boundary.  It does not use
  proof irrelevance.

- Repaired two latent framing interfaces exposed by this composition:

  - a source-only cast changes the left endpoint but leaves the right endpoint
    fixed, so the indexed frame concludes `B \sqsubseteq A'`, not an unrelated
    `B \sqsubseteq B'`;
  - cast frames are normalized through their stored canonical indexed
    relation before their raw `resultType` is composed.

  The universal narrowing and widening classifications are now exhaustive for
  `id`, sequence, `\forall`, `gen`, and `inst` coercion shapes.

- Split the former 24,000-line simulation module into cacheable layers:

  - `NuImprecisionSimulationCore` contains 15,003 lines of stable weak-step,
    transport, world-embedding, and permutation infrastructure;
  - `NuImprecisionSimulation` contains 7,205 lines of active universal
    catch-up and generic `\beta\text{-}\forall` reasoning;
  - `NuImprecisionAllocationSimulation` contains 3,157 lines of completed
    synchronized and one-sided allocation cases;
  - `NuImprecisionCatchupScratch` is a 126-line active proof file containing
    the resume lemma.

  With the core cache warm, the scratch lemma checks in about four seconds.
  The next proof boundary is to invoke its done/continue interface from the
  total indexed universal catch-up recursion.

### 2026-07-18: arbitrary-index source-`∀` catch-up boundary

- Refined the recursive catch-up interface after asking Agda for the exact
  constructor coverage.  The structurally useful worker must preserve
  an arbitrary derivation

  \[
    p : \Phi;\Delta_L \vdash \forall X.A \sqsubseteq B;\Delta_R,
  \]

  rather than assume both endpoints and the index already have the paired
  shape `\forall q`.  A source cast can hide either a paired `\forall` index
  or a source-only `\nu` index, and a target cast can hide a non-universal
  target type.  The public canonical-`\forall` theorem will be the
  specialization obtained after this general worker returns.

- Added `specialize-left-indexed-all-catchup`, the checked projection

  \[
    \mathsf{LeftCatchupIndexedResult}(\forall q)
      \Longrightarrow
    \mathsf{LeftCatchupIndexedAllResult}(q).
  \]

  Added the prefix-aware terminal value lemma
  `left-catchup-indexed-source-all-prefix-valueᵀ`.  It weakens only after the
  source is known to be a bullet-free value, so a pending allocation prefix
  is never incorrectly pushed through an active runtime bullet.

- Proved the first fully general value-shaped allocation leaf,
  `left-catchup-indexed-prefix-α-Λᵀ`.  In nominal notation its operational
  component is

  \[
    (\Lambda X.W)[\alpha] \longrightarrow W.
  \]

  If two lifted worlds `\rho^a` and `\rho^b` arise from the same base world,
  and

  \[
    (\alpha,\uparrow A)::\rho^a \preccurlyeq \rho^+,
    \qquad
    \rho^b \vdash W \sqsubseteq V' : C \sqsubseteq_p B,
  \]

  the lemma returns `LeftCatchupIndexedResult p` in `\rho^+`.  It transports
  `p` by the existing identity permutation action; it does not require
  `p = \forall q` or require `B` to be universal.

- Kept the unfinished dispatcher out of the checked modules.  Its temporary
  coverage audit confirmed that, after terminal `blame`, both `Λ` value
  forms, prefix composition, and the direct `α/Λ` leaf, the remaining
  boundary consists of quotiented widening, the residual value-shaped
  `α` forms, source-only `ν` and `ν★`, and source/target cast or conversion
  wrappers.  These should be discharged by supporting framing lemmas, with
  the recursive hypothesis computed before it is passed to each helper.

- Moved the stable terminal/projection lemmas to
  `NuImprecisionSimulationCore` and the stable general `α/Λ` lemma to
  `NuImprecisionSimulation`.  `NuImprecisionCatchupScratch` is again a
  149-line checked file containing only the active silent-resumption lemma.
  All three modules check with `--no-allow-unsolved-metas`.

### 2026-07-18: target frames and the visible one-step dispatcher

- Added a generic target-frame composition lemma and five prefix-aware target
  wrappers.  They handle target narrowing, target widening in arbitrary and
  identity-only modes, reveal, and conceal.  In nominal notation, each has
  the common shape

  \[
    \frac{
      \rho_0 \preccurlyeq \rho^+
      \qquad
      \rho^+ \vdash N \sqsubseteq V' : A \sqsubseteq_p A'
    }{
      \rho^+ \vdash
        N \sqsubseteq V'\langle c'\rangle
        : A \sqsubseteq_q B'}.
  \]

  The coercion or single-name conversion evidence is first weakened from
  `\rho_0` to `\rho^+`, then transported through the recursive catch-up
  result.  No term-imprecision constructor was added.

- Exposed `left-catchup-indexed-source-all-prefixᵀ` as the active recursive
  worker, together with its unprefixed and canonical paired-`∀` corollaries.
  The implemented recursion obtains its induction hypothesis before passing
  it to each target-frame helper.  Agda's coverage report isolates the
  remaining work into nine explicit hole families:

  1. paired quotiented widening;
  2. residual post-allocation `α` forms;
  3. source-only `ν` and `ν\,\star` catch-up;
  4. source narrowing and source widening frames;
  5. paired, reveal-only, and conceal-only source conversions.

  These holes are intentionally confined to
  `NuImprecisionCatchupScratch`; the stable core, allocation, and universal
  support modules remain hole-free.

- Added the visible recursive statement
  `weak-one-step-indexed-simulationᵀ`:

  \[
    \begin{gathered}
      \Phi;\rho \vdash M \sqsubseteq M' : A \sqsubseteq_p B,
      \qquad
      M' \longrightarrow^{\chi} N' \\
      \Longrightarrow
      \mathsf{WeakOneStepIndexedOutcome}(p).
    \end{gathered}
  \]

  Its checked clauses now include immediate source `blame`, matched ordinary
  `ν`, matched `ν\,\star`, source-only `ν` and `ν\,\star` frames, and
  target-only `ν` and `ν\,\star` allocation and frame cases.  For every
  `ξ-ν` clause, recursion is on the body relation and the resulting induction
  hypothesis is supplied to the corresponding indexed frame theorem.
  Target `blame-ν` is closed whenever inversion exposes an inner
  `blame \sqsubseteq blame` leaf.

- The `ν\,\star` frame boundary exposed one harmless syntactic transport:

  \[
    \mathsf{applyTy}(\chi,\star)=\star.
  \]

  Both matched and target-only `ξ-ν` clauses rewrite by `applyTy-★` before
  invoking their frame helper.

- The scratch module checks normally with its explicit construction options.
  It is not claimed to check with `--no-allow-unsolved-metas`: the nine
  catch-up families and the rest of the general dispatcher are deliberately
  still open.  The next focused boundary is paired quotiented widening,
  because it is the only remaining worker family whose outer source shape is
  a casted quotiented term rather than an allocation or a single source
  frame.

### 2026-07-18: arbitrary-type catch-up and quotient recursion

- Generalized the active value-catch-up recursion from a universal source
  endpoint to an arbitrary source endpoint:

  \[
    \begin{gathered}
      \rho_0 \preccurlyeq \rho^+,
      \qquad
      \rho_0 \vdash M \sqsubseteq V' : A \sqsubseteq_p B,
      \\
      \operatorname{RuntimeOK}(M),
      \qquad
      \operatorname{Value}(V'),
      \qquad
      \operatorname{NoBullet}(V')
      \\
      \Longrightarrow
      \mathsf{LeftCatchupIndexedResult}_{\rho^+}
        (M,V',A,B,p).
    \end{gathered}
  \]

  The previous source-`\forall` worker is now a direct specialization of this
  theorem.  This is a proof-interface change only; no term-imprecision rule
  was added or loosened.

- Proved the general terminal clauses for `blame`, functions, type
  abstractions, and constants.  Also discharged by inversion every relation
  constructor whose target syntax cannot be a value: variables,
  applications, paired runtime bullets, target-only runtime bullets, matched
  allocations, target-only allocations, and primitive applications.

- Added the direct recursive quotient clauses.  In nominal notation, for the
  ordinary body premise

  \[
    M \sqsubseteq M' : C \sqsubseteq_{p_C} C',
  \]

  the dispatcher first obtains the induction hypothesis

  \[
    \mathsf{catchup}(M,M',p_C),
  \]

  and then supplies it to the appropriate cast-spine helper:

  \[
    \frac{
      \mathsf{catchup}(M,M',p_C)
      \qquad
      M\langle d\rangle
        \sqsubseteq^p M'\langle d'\rangle
      \qquad
      (u,u') : (D,D') \leadsto (A,A')
    }{
      M\langle d\rangle\langle u\rangle
        \mathrel{\mathsf{catchup}}
      M'\langle d'\rangle\langle u'\rangle
    }.
  \]

  There are separate helpers for the two existing quotient constructors,
  `down\sqsubseteq down` and `gen\text{-}down\sqsubseteq gen\text{-}down`.
  These are proof helpers, not new syntax-directed relation clauses.

- The target-value inversion is now expressed directly in the dispatcher:

  \[
    \operatorname{Value}
      (M'\langle d'\rangle\langle u'\rangle)
    \Longrightarrow
    \operatorname{Value}(M')
      \land \operatorname{Inert}(d')
      \land \operatorname{Inert}(u').
  \]

  The source runtime premise is stripped through both casts before the
  recursive call.  Thus the quotient boundary no longer assumes that its
  hidden ordinary source type is itself universal.

- Proved and moved to `NuImprecisionSimulationCore` the missing quotient-index
  transport theorem.  Store changes act on types by renaming, and renaming
  preserves adjacent-`\forall` permutation equivalence:

  \[
    C \approx_\forall E
    \Longrightarrow
    \mathsf{applyTys}(\bar\chi,C)
      \approx_\forall
    \mathsf{applyTys}(\bar\chi,E).
  \]

  Therefore, if a weak result transports the ordinary middle witness in

  \[
    C \approx_\forall E
      \sqsubseteq F
      \approx_\forall D,
  \]

  then `weak-one-step-transport-quotientᵀ` reconstructs the corresponding
  transported quotient witness.  The weak-result record itself does not need
  another field.

- The generalized recursion and the source-`\forall` corollaries check in
  the scratch module.  Ten explicit holes remain: two quotient cast-spine
  helpers, residual source runtime-bullet catch-up, source-only ordinary and
  `\star` allocation, source narrowing/widening, and three source-side
  conversion families.

### Next boundary

Analyze each quotient cast-spine helper by the final state returned from its
body induction hypothesis:

\[
  M \longrightarrow^* \mathsf{blame}
  \qquad\text{or}\qquad
  M \longrightarrow^* V.
\]

The blame branch should append two cast-blame steps.  The value branch should
use the narrowing and widening typing premises to classify each source cast
as inert or administrative, resuming catch-up after every administrative
step.  This isolates all operational work inside the two helpers and keeps
the derivation recursion fixed.

### 2026-07-18: transported quotient spines and the shared value boundary

- Proved fixed-mode transport for narrowing and widening coercions.  If
  renaming by one type-variable step preserves the mode environment, then

  \[
    \mu;\Delta;\Sigma \vdash c : A \mathrel{\trianglerighteq} B
    \Longrightarrow
    \mu;\mathsf{applyCtxs}(\bar\chi,\Delta);
      \mathsf{applyStores}(\bar\chi,\Sigma)
      \vdash
      \mathsf{applyCoercions}(\bar\chi,c)
      : \mathsf{applyTys}(\bar\chi,A)
        \mathrel{\trianglerighteq}
        \mathsf{applyTys}(\bar\chi,B),
  \]

  and likewise for widening.  The two modes needed by quotient narrowing,
  `id-only` and `gen(tag-or-id)`, satisfy this invariant.  These lemmas are
  stable and now live in `NuImprecisionSimulationCore`.

- Proved transport of both quotient narrowing constructors through a body
  catch-up result.  In nominal notation, the ordinary case reconstructs

  \[
    N\langle \bar\chi d\rangle
      \sqsubseteq^p
    N'\langle d'\rangle
    : \bar\chi D \sqsubseteq^p D',
  \]

  while the generalized case has the same conclusion with its narrowing
  derivations checked in `gen(tag-or-id)` mode.  Source coercion evidence is
  transported through `\bar\chi`; target evidence only requires prefix
  weakening because the target catch-up tail is empty.

- Proved transport of `QuotientWideningPair` for both of its existing
  constructors.  The identity-only constructor uses fixed-mode widening
  transport.  The arbitrary-cast constructor transports its cast mode,
  seal-store invariant, and widening derivation together.  Consequently the
  final quotient relation is rebuilt directly as

  \[
    \frac{
      N\langle \bar\chi d\rangle
        \sqsubseteq^p N'\langle d'\rangle
      \qquad
      (\bar\chi u,u') :
        (\bar\chi D,D') \leadsto (\bar\chi A,A')
    }{
      N\langle \bar\chi d\rangle\langle \bar\chi u\rangle
        \sqsubseteq
      N'\langle d'\rangle\langle u'\rangle
      : \bar\chi A \sqsubseteq A'}.
  \]

  A single double-cast frame lifts the body reduction trace to this relation.
  The construction preserves the weak-result transport and type-coherence
  interfaces, so both quotient dispatcher clauses now call the same
  structural helper.  No term-imprecision rule was added.

- Closed the body-blame operational branch.  Once body catch-up yields
  `blame`, the source has the trace

  \[
    \mathsf{blame}\langle d\rangle\langle u\rangle
      \longrightarrow
    \mathsf{blame}\langle u\rangle
      \longrightarrow
    \mathsf{blame}.
  \]

  The target takes zero steps, and its typing derivation constructs the
  existing left-blame relation at the final index.  This branch therefore
  does not permit new source blame; it merely propagates blame already
  returned by the recursive body catch-up.

- Factored the remaining quotient work into one shared hole,
  `left-catchup-indexed-final-double-castᵀ`, rather than one hole per
  quotient constructor.  Its open clause assumes that body catch-up returned
  a value.  The two former quotient helper holes are closed, and the scratch
  module now has nine explicit holes in total: this shared value clause plus
  the eight previously isolated allocation, cast, and conversion families.

### Next boundary

Classify the transported source narrowing and widening coercions when the
body result is a value:

\[
  \operatorname{Value}(V),
  \qquad
  V\langle d\rangle\langle u\rangle
    \sqsubseteq
  V'\langle d'\rangle\langle u'\rangle,
  \qquad
  \operatorname{Inert}(d'),
  \operatorname{Inert}(u').
\]

The desired inversion should distinguish inert source casts from the few
administrative `gen`/`inst` shapes that allocate or expose a type
instantiation.  Each inert/inert outcome closes immediately as a value;
each administrative outcome should resume catch-up after its explicit
reduction trace and reuse the completed allocation-crossed lemmas.  This is
the only remaining quotient-specific operational boundary.

### 2026-07-18: active quotient spines reduce by one silent step

- Moved the quotient body-value boundary out of
  `NuImprecisionCatchupScratch` into the small, independently checked module
  `NuImprecisionQuotientValue`.  The large catch-up dispatcher now
  imports only the final quotient theorem.  Stable coercion-shape decision is
  supplied by `inert-dec` in `CoercionProperties`, so changing the active
  proof does not force Agda to recheck the general coercion metatheory.

- Closed the inert/inert source case directly.  In nominal notation, if

  \[
    V\langle d\rangle\langle u\rangle
      \sqsubseteq
    V'\langle d'\rangle\langle u'\rangle
  \]

  is the rebuilt quotient relation and both `d` and `u` are inert, then the
  source already is a value and catch-up takes zero steps.

- Proved the general active-cast progress lemma.  If `V` is a closed
  bullet-free value, `c : C \Rightarrow D` is a well-typed coercion, and `c`
  is not inert, then

  \[
    V\langle c\rangle \longrightarrow_{\mathsf{keep}} L
  \]

  for some `L`.  The proof uses typed progress and value irreducibility.  A
  separate inversion proves that every step out of a cast around a value has
  store change `keep`; hence this fact does not hide an allocation.

- Lifted that result to the complete source quotient spine.  If

  \[
    \neg\bigl(\operatorname{Inert}(d) \land
               \operatorname{Inert}(u)\bigr),
  \]

  then, for some `L`,

  \[
    V\langle d\rangle\langle u\rangle
      \longrightarrow_{\mathsf{keep}} L.
  \]

  When `d` is active, its step is lifted through the outer cast.  When `d` is
  inert, the whole inner cast is a value and typed progress supplies the step
  of `u`.

- Expanded the active quotient dispatcher over the two narrowing premises
  (`down/down` and generalized `gen-down/gen-down`) and the two widening-pair
  premises (identity-mode and arbitrary cast-mode).  Every one of these four
  clauses obtains the source step first and feeds it to the same supporting
  theorem.  Thus the relation recursion gained no constructor and the
  semantic work did not multiply into four holes.

- The shared supporting theorem now has exactly two explicit unfinished
  clauses:

  \[
    \begin{array}{ll}
    \text{outer step:} &
      V\langle d\rangle\langle u\rangle
        \longrightarrow L, \\
    \text{inner step:} &
      V\langle d\rangle \longrightarrow K,
      \quad
      V\langle d\rangle\langle u\rangle
        \longrightarrow K\langle u\rangle.
    \end{array}
  \]

  This is the next proof boundary.  The outer clause contains the important
  `inst` case, whose first step exposes `ν ★`; the inner clause contains the
  administrative narrowing cases.  They should be handled by reduction-shape
  helpers and then resumed through the existing allocation simulation, rather
  than by extending term imprecision.

### 2026-07-18: quotient reduction is split into reachable root shapes

- Replaced the two opaque source-step holes by separate outer- and inner-cast
  dispatchers.  For a bullet-free value `V`, the operational candidates are
  now visible as the formula-shaped cases

  \[
    V\langle d\rangle\langle u\rangle \longrightarrow L
  \]

  and

  \[
    V\langle d\rangle \longrightarrow K,
    \qquad
    V\langle d\rangle\langle u\rangle
      \longrightarrow K\langle u\rangle.
  \]

  Each dispatcher explicitly analyzes identity, sequence, instantiation,
  tag/untag, and seal/unseal roots.  A step below the inner cast is impossible
  because `V` is a value.

- Proved two coercion-shape inversions from the quotient narrowing premise.
  If

  \[
    V\langle d\rangle \sqsubseteq^{p}
      V'\langle d'\rangle,
  \]

  then `d` cannot be a tag and cannot be an unseal.  Consequently, an outer
  tag/untag redex and an inner seal/unseal redex are unreachable.  This is a
  typing fact, not an added case of term imprecision.

- Closed the reachable failed-tag case.  When the tag occurs inside `V` and
  the quotient narrowing is an untag, the whole source trace is

  \[
    W\langle G\mathbin{!}\rangle
      \langle H\mathbin{?}\rangle\langle u\rangle
      \longrightarrow
    \mathsf{blame}\langle u\rangle
      \longrightarrow
    \mathsf{blame},
    \qquad G \ne H.
  \]

  The final relation is obtained from the existing source-blame rule; the
  target remains unchanged.

- Proved the two instantiation/allocation traces needed by the remaining hard
  cases.  Instantiation at the outer widening gives

  \[
    V\langle d\rangle\langle \mathsf{inst}\ B\ s\rangle
      \longrightarrow
    \nu\,\star\;V\langle d\rangle\;s
      \longrightarrow_{\mathsf{bind}\ \star}
    \bigl((\uparrow V\langle d\rangle)\,\bullet\bigr)
      \langle s\rangle.
  \]

  Instantiation at the inner narrowing, lifted through the outer cast, gives

  \[
    V\langle \mathsf{inst}\ B\ s\rangle\langle u\rangle
      \longrightarrow
    (\nu\,\star\;V\;s)\langle u\rangle
      \longrightarrow_{\mathsf{bind}\ \star}
    \bigl((\uparrow V)\,\bullet\bigr)
      \langle s\rangle\langle \uparrow u\rangle.
  \]

  These checked traces are already bound in the two unfinished instantiation
  clauses.  The next relational step is therefore specifically to transport
  the quotient narrowing/widening evidence across the fresh `\star` entry and
  connect it to the crossed-allocation lemmas.

- Eight reachable quotient clauses remain: outer identity, sequence,
  instantiation, and seal/unseal; and inner identity, sequence,
  instantiation, and matching tag/untag.  The dispatcher skeleton is
  intentionally incomplete while these supporting lemmas are developed.

- Proved the ground-endpoint quotient-collapse lemma
  `⊑ᵖ-ground-left`.  In nominal notation, if `G` is ground, then

  \[
    \Gamma \vdash G \sqsubseteq^{p} B
    \quad\Longrightarrow\quad
    \Gamma \vdash G \sqsubseteq B.
  \]

  The proof first shows that variables, base types, `\star`, and the ground
  function type `\star \to \star` are fixed points of adjacent-`\forall`
  permutation.  It then inverts ordinary imprecision from a ground source;
  every possible target is itself fixed by the permutation equivalence.

  Two checked narrowing inversions feed this lemma into the active quotient
  clauses.  A seal narrowing has hidden source endpoint `\alpha`, and an
  untag narrowing has hidden source endpoint `G`.  Hence the remaining
  seal/unseal and matching tag/untag holes now contain an ordinary hidden
  index, rather than only the quotiented one.  Their next obligation is term
  inversion: remove the cancelled source conversion while rebuilding the two
  inert target casts.

### 2026-07-18: inert-target inversion eliminates the conversion leaves

- Audited the matching tag/untag state against the loosened
  `paired-widening` premise.  An unrestricted paired widening can indeed
  forget an intermediate index, so stripping the source tag in isolation is
  not a valid general lemma.  The complete quotient state carries a stronger
  invariant, however: its target narrowing and widening are both inert
  because the target is already a value.

- Proved the coercion inversion used by that invariant.  In nominal form, if
  `G` is ground, `G \sqsubseteq D`, the mode `\mu` permits no seals, and

  \[
    c : \star \mathrel{\trianglerighteq}_{\mu} D,
    \qquad \operatorname{Inert}(c),
  \]

  then this state is impossible.  The only nontrivial inert coercion out of
  `\star` is a `gen` coercion, whose target is universal; ordinary
  imprecision cannot relate a ground source to that universal target.  The
  two quotient narrowing modes satisfy the no-seal premise:

  \[
    \mathsf{id\!\text{-}\!only}^{d},
    \qquad
    \mathsf{gen}^{d}(\mathsf{tag\!\text{-}\!or\!\text{-}\!id}^{d}).
  \]

- Proved that ordinary imprecision with source `\star` has target `\star`.
  Applying this to the body of

  \[
    W\langle G!\rangle\langle G?\rangle
      \sqsubseteq
    V'\langle d'\rangle
  \]

  transports the target narrowing to one whose source is `\star`.  Ground
  quotient collapse supplies `G \sqsubseteq D'`, and the inert-target
  coercion inversion gives a contradiction.  Thus the matching tag/untag
  dispatcher clause is unreachable; no source-tag stripping rule and no new
  term-imprecision constructor is needed.

- Strengthened the analogous seal observation.  A quotient narrowing cannot
  be a seal at all, because neither quotient narrowing mode permits seals.
  Therefore the outer seal/unseal dispatcher clause is also unreachable.
  This replaces the earlier weaker fact that only recovered its ground
  endpoint.

- The active quotient dispatcher now has six holes: outer identity,
  sequence, and instantiation; and inner identity, sequence, and
  instantiation.  All tag/untag and seal/unseal roots are closed.  The next
  boundary is administrative identity/sequence normalization while retaining
  the original quotient-spine evidence; the crossed `inst` allocation traces
  remain the subsequent polymorphic boundary.

### 2026-07-18: sequence normalization preserves the quotient spine

- Split both sequence grammars at their canonical endpoints.  A widening
  sequence has one of the forms

  \[
    s;G!
    \qquad\text{or}\qquad
    \mathsf{unseal}\ \alpha;s,
  \]

  while a quotient narrowing sequence has one of the forms

  \[
    G?;g
    \qquad\text{or}\qquad
    n;\mathsf{seal}\ \alpha.
  \]

  The unseal-headed outer alternatives are impossible because they would
  make the inert quotient narrowing end at a type name in a mode that permits
  no seals.  The seal-tailed inner alternatives are impossible directly:
  neither quotient narrowing mode permits their final seal.

- Proved the strict-cross ground-endpoint inversion.  If `s` is a typed
  strict-cross widening ending at a ground type `G`, or `g` is a typed
  strict-cross narrowing beginning at `G`, then

  \[
    G = \star \to \star.
  \]

  Consequently ordinary imprecision supplies

  \[
    G \sqsubseteq \star.
  \]

  The proof is exhaustive: strict-cross function coercions force an arrow
  endpoint, strict-cross universal coercions force a universal endpoint, and
  only the ground arrow `\star \to \star` survives.

- Closed both outer sequence clauses.  The source trace is

  \[
    V\langle d\rangle\langle s;G!\rangle
      \longrightarrow
    V\langle d\rangle\langle s\rangle\langle G!\rangle.
  \]

  At the residual state, `up⊑upᵀ` retains the original quotient narrowing,
  uses `s` as its source widening, and keeps the original target widening.
  The ordinary source-cast rule then adds `G!`.  This works for both the
  identity-mode pair and the arbitrary cast-mode pair, and the residual is a
  value.  No term-imprecision constructor was added.

- Proved `inner-sequence-residualᵀ`.  For either quotient narrowing mode, if

  \[
    V\langle G?;g\rangle\langle u\rangle
      \sqsubseteq
    V'\langle d'\rangle\langle u'\rangle,
  \]

  then the result of the administrative sequence step has the checked
  relation

  \[
    V\langle G?\rangle\langle g\rangle\langle u\rangle
      \sqsubseteq
    V'\langle d'\rangle\langle u'\rangle.
  \]

  The leading untag is reconstructed by the ordinary source-narrowing rule at
  `G \sqsubseteq \star`; the strict-cross suffix `g`, target narrowing `d'`,
  and outer widenings remain in the quotient constructors.

- Six implementation holes remain, but only five semantic families: outer
  identity and instantiation; inner identity, sequence, and instantiation.
  The two inner sequence holes now already bind their residual relation.  The
  next boundary is to pass the recursive ordinary catch-up result into the
  quotient helper and prepend the checked `keep` step.  This is the required
  induction hypothesis handoff; duplicating ordinary tag/untag catch-up inside
  the quotient helper would be the wrong proof structure.

- Moved the stable source-`keep` composition layer out of
  `NuImprecisionSimulation` into `NuImprecisionCatchupComposition`.  It proves
  that a source step

  \[
    M \longrightarrow_{\mathsf{keep}} N
  \]

  can be prepended to an indexed catch-up result for `N`, while preserving
  `WeakOneStepTransport` and `WeakOneStepTypeCoherence`.  The large simulation
  module now imports these cached lemmas instead of defining them locally.

- Wired both inner sequence clauses through that composition theorem.  Their
  only remaining local hole is now the catch-up result for the already-checked
  residual relation; the outer result, trace concatenation, transport, and
  coherence are all derived.  Thus the open goal is no longer “simulate
  `β-seq`.”  It is exactly “supply the recursive ordinary catch-up result for
  the residual source-narrowing relation.”

### 2026-07-18: identity spines and inner instantiation are impossible

- Proved the three atomic target inversions needed for a literal identity
  coercion.  If an inert narrowing ends at a base type or at `\star`, then the
  state is impossible.  If it ends at a type name, the same conclusion holds
  whenever the mode permits no seals.  Both quotient narrowing modes satisfy
  that restriction.

- Proved that quotiented imprecision with source `\star` has target `\star`:

  \[
    \Phi;\Delta_L \vdash
      \star \sqsubseteq^{p} B
    \quad\Longrightarrow\quad
    B = \star.
  \]

  Together with ground quotient collapse, this gives the complete target-side
  inversion for identity coercions.  A source name can only relate to a target
  name or `\star`; a source base type can only relate to the same base type or
  `\star`; and a source `\star` can only relate to `\star`.

- Closed both identity dispatcher leaves.  In nominal notation, a widening
  coercion that is literally `\mathsf{id}_A` can only have one of the forms

  \[
    \mathsf{id}_{\alpha},
    \qquad
    \mathsf{id}_{\iota},
    \qquad
    \mathsf{id}_{\star}.
  \]

  In the outer leaf, the source quotient narrowing is already an inert value
  ending at that atomic type, which is impossible.  In the inner leaf, the
  target quotient narrowing is inert and ends at the corresponding name, base
  type, or `\star`, which is likewise impossible.  No quotient elimination and
  no new term-imprecision rule are required.

- Closed the inner `\mathsf{inst}` leaf by coercion-grammar inversion.  The
  inner coercion belongs to the quotient narrowing half, while
  `\mathsf{inst}` is a widening form.  The only superficially possible
  narrowing case is a crossed coercion, whose grammar cannot produce an
  `\mathsf{inst}` node.

- Refined the reachable outer `\mathsf{inst}` skeleton into its two existing
  widening-pair cases.  Both clauses now expose directly the premises

  \[
    \mathsf{occurs}(\alpha,A),
    \qquad
    \mathsf{inst}(\mu);\Delta,\alpha{:}\star
      \vdash s : A \mathrel{\sqsubseteq} \uparrow B,
  \]

  obtained from the original `cast-inst` typing and widening derivation.  The
  already-checked trace allocates the fresh `\star` name.  The remaining
  obligation is therefore exactly to relate the allocated bullet body and its
  residual cast `s` to the inert target quotient spine.

- Generalized `AllImprecisionView` from universal targets to arbitrary target
  types, without changing the underlying imprecision relation.  The new
  `\sqsubseteq^{p}` source-universal view states that

  \[
    \Phi;\Delta_L \vdash \forall\alpha.A
      \sqsubseteq^{p} B
  \]

  selects a universal source representative `\forall\beta.C`, an ordinary
  imprecision derivation from that representative, and a final permutation
  equivalence to `B`.  The ordinary derivation has exactly the existing two
  forms: paired `\forall` imprecision or source-only `\nu` imprecision.  Both
  outer instantiation holes now bind this view, so the remaining allocation
  proof can branch on this semantic invariant rather than on term syntax.

- Four holes remain in `NuImprecisionQuotientValue`: two outer
  instantiation clauses (identity mode and general cast mode), and the two
  ordinary catch-up results for normalized inner sequences.  They represent
  two semantic boundaries, not four unrelated cases.

### Next boundary

Thread the ordinary catch-up induction hypothesis through the two normalized
inner-sequence clauses.  Then use the resulting recursion interface at the
outer instantiation boundary, where the source-only `\star` allocation must be
combined with the existing permutation/crossed-allocation infrastructure.

### 2026-07-20: promoted quotient value module is hole-free

- Closed both normalized inner-sequence leaves by contradiction.  A strict
  crossed narrowing after a source untag has an arrow target, whereas the
  underlying source term has type `\star`.  Quotiented imprecision therefore
  forces the target narrowing to start at `\star`; no inert narrowing from
  `\star` can end at that arrow (or at `\star` in the alternative quotient
  shape).  Thus these leaves do not require a recursive catch-up hypothesis.

- Removed the temporary split on the two quotient-narrowing constructors.  It
  was useful diagnostically, but it duplicated the same allocation boundary
  and did not expose any additional invariant connecting the quotient
  representatives to the cast spines.

- Replaced the two outer-instantiation holes with an explicit residual
  alternative.  In nominal notation, when the source widening is

  \[
    u = \mathsf{inst}\ B\ s,
  \]

  `NuImprecisionQuotientValue` now returns the checked trace

  \[
    V\langle d\rangle\langle u\rangle
      \longrightarrow
    \nu\,\star\,(V\langle d\rangle)\,s
      \longrightarrow
    (\uparrow V\langle d\rangle)\,\bullet\langle s\rangle.
  \]

  All other branches still return `LeftCatchupIndexedResult` directly.  The
  result is stated inline as a sum, rather than introducing an alias for part
  of the theorem statement.

- Propagated that residual into the ordinary-down and gen-down clauses of the
  recursive catch-up dispatcher.  The stable
  `NuImprecisionQuotientValue` module contains no holes.  The dispatcher has
  two explicit residual holes whose contexts carry the transported quotient
  narrowing/widening evidence, the source allocation trace, and the
  already-obtained catch-up induction hypothesis for the underlying terms.

- Audited the current Agda proof after promoting and splitting the stable
  modules.  `NuImprecisionSimulationCore`,
  `NuImprecisionAllocationSimulation`, `NuImprecisionCatchupComposition`, and
  `NuImprecisionQuotientValue` all check with unsolved metas disabled.  On the
  active Nu-imprecision simulation path, exactly ten explicit holes remain,
  all in `NuImprecisionCatchupScratch`:

  - two quotient-`inst` residual clauses, in the ordinary-down and gen-down
    helpers;
  - three source-allocation dispatcher leaves, for `α⊑ᵀ`, `ν⊑ᵀ`, and
    `νcast⊑ᵀ`;
  - five source cast/conversion dispatcher leaves, for `cast⊒⊑ᵀ`,
    `cast⊑⊑ᵀ`, `conv⊑convᵀ`, `conv↑⊑ᵀ`, and `conv↓⊑ᵀ`.

- Removed the inherited scratch options from
  `NuImprecisionQuotientValue`.  The promoted module checks with Agda's
  default rejection of both unsolved metas and incomplete pattern matches, so
  its hole-free status no longer depends on permissive module flags.

- Those ten holes are not the complete remainder of one-step simulation.
  `weak-one-step-indexed-simulationᵀ` is still an unfinished dispatcher
  skeleton accepted under `--allow-incomplete-matches`.  Its written clauses
  cover `blame⊑ᵀ` and the matched, source-only, and target-only ordinary `ν`
  and `ν ★` families, including their allocation, inner-step, and blame
  boundaries where applicable.  The non-`ν` term-imprecision constructors and
  their target-reduction cases have not yet been enumerated.  They are
  unwritten obligations, not Agda holes, and must be audited after the focused
  catch-up boundary is closed.

- This refactoring avoids a circular proof.  The quotient endpoint witness
  alone does not derive the ordinary post-allocation body relation required by
  `left-β-inst-νcast-allocation`; the representative equivalences are not tied
  to the narrowing/widening ASTs.  The next proof must use the dispatcher
  induction hypothesis together with the existing one-sided/crossed allocation
  and mode-permutation lemmas, or strengthen the quotient-spine invariant.  It
  must not assume an ordinary body relation inside the value helper.

### Next boundary

Complete the two explicit quotient-instantiation residual clauses in
`NuImprecisionCatchupScratch`.  First invert the transported narrowing and
widening spines into the one-sided and adjacent-swap allocation shapes.  Then
feed the already-bound underlying catch-up result into the corresponding
allocation/permutation helper and prepend the checked `keep, bind \star`
trace.  After those focused clauses, enumerate the missing non-`ν` patterns of
`weak-one-step-indexed-simulationᵀ` and connect each written helper to the main
dispatcher before claiming total one-step coverage.

### 2026-07-20: terminal interfaces and low-cost checking lanes

- Added separate partial modules for the three named terminal facts:
  `forward-source-valueᵀ`,
  `backward-target-value-or-source-blameᵀ`, and
  `backward-target-blameᵀ`.  Their full statements type-check and the
  hole-free `NuDGGTerminal` wrapper accepts them as separate arguments before
  invoking the checked `ClosedNuDGG` and public `GradualDGG` spine.

- Added arbitrary-world versions of all three statements.  This records the
  invariant exposed by the first top-down audit: recursive terminal simulation
  cannot remain at the closed theorem type after a target or source step,
  because the imprecision world, both stores, both type contexts, and the type
  index have changed.  Each closed terminal theorem is now a checked
  specialization of its arbitrary-world statement; only the general proof
  body remains open.

- Added the checked base statement
  `left-catchup-target-blameᵀ`.  It requires `RuntimeOK` and an arbitrary-world
  relation to target `blame`, and returns an explicit source trace to blame.
  Its structural proof remains open.

- Added two hole-free terminal-trace support modules:
  `aligned-residual-shorter` proves the residual trace from deterministic
  target-tail alignment is strictly shorter than the original stepped trace,
  and `multi-store-preservation` propagates `StoreWf` through a full Nu trace.

- Added `NuDGGStrictSpine`, which excludes all partial terminal and catch-up
  modules.  Checking is now explicitly tiered: owned modules after each edit,
  focused terminal consumers after integration batches, and the strict spine
  plus `All.agda` only at interface freezes or major proof milestones.  A
  multi-minute strict aggregate rebuild was stopped once this policy was
  adopted; it is not part of the per-slice loop.

- Bootstrapped the remote machine at `ginger.luddy.indiana.edu`.  The clean
  tracked checkout is `/home/jsiek/src/AI-for-pl` on `main`; Agda 2.7.0.1,
  standard library 2.1.1, Codex CLI 0.144.6, and the exact model slug
  `gpt-5.5` are verified.  The executable's compiled-in Cabal data directory
  is stale, so added `scripts/agda-ginger` to pin both the working Agda data
  directory and a repository-owned Agda application directory.  The latter
  points at the adjacent stdlib source while keeping refreshed interfaces in
  the worktree.  Future ginger work packages use that wrapper and never invoke
  the bare executable, mutate the installed stdlib, or copy its source tree.

- Ran the first isolated GPT 5.5 pilot on
  `codex/ginger-dgg-quotient-seal-cases`.  It supplied the four exhaustive
  down/gen-down clauses missing from the source untag-then-seal quotient
  cases, then repaired the ambiguous type and precision implicits exposed by a
  fresh build.  Both the exact ginger wrapper command and the local strict
  owned-module check pass.

- Completed the second isolated GPT 5.5 slice on
  `codex/ginger-dgg-weak-preservation`.  It proved the four frozen weak-result
  runtime/store facts by preserving across `sourceCatchup`, and across the
  distinguished target step followed by `targetTail`.  The integrated local
  version reuses `NuDGGPreservation.multi-store-preservation` instead of
  duplicating it, and its focused strict check passes.

- Completed the GPT 5.6 higher-order backward-blame assembly in
  `NuDGGTerminalBackwardBlameAssembly`.  The proof is independent of the live
  partial leaf implementations: it accepts their frozen interfaces, performs
  fuel induction over the observed target trace, restores all recursive
  invariants through `NuDGGWeakResultPreservation`, and composes the source
  traces.  This integration pass also caught a missing `[]` import in
  `NuDGGTraceMeasure`; the focused measure and assembly checks pass after that
  repair.

- Checked the live backward-blame consumer in
  `NuDGGTerminalBackwardBlameIntegration`.  Its first run found that
  `left-catchup-target-blameᵀ` had accidentally imported the old
  `NuTermImprecision` judgment.  The statement now uses
  `QuotientedTermImprecision`, and both the focused catch-up statement check
  and the live assembly application pass.  This consumer is classified as an
  integration-milestone check because a clean dependency rebuild is costly.

### Next boundary

Complete the arbitrary-source target-blame catch-up and the exhaustive
target-step dispatcher at the exact interfaces accepted by
`NuDGGTerminalBackwardBlameIntegration`.  In parallel at the architecture
level, establish the analogous higher-order assembly for backward
target-value-or-source-blame before delegating its easy leaf cases to ginger.

### 2026-07-20: terminal assemblies and concurrent Ginger leaves

- Completed the strict higher-order backward-value assembly, now in
  `NuDGGTerminalBackwardValueProof`.  Its fuel induction consumes the
  frozen one-step dispatcher and indexed value catch-up interfaces, aligns
  each administrative target tail with the observed value trace, recurses on
  the strictly shorter residual, and composes the source traces and transported
  world/store/type evidence.  `NuDGGTerminalBackwardValueLemma` supplies the
  live partial declarations without any interface strengthening.

- Completed and integrated the structural target-blame catch-up.  Its proof
  recurses directly over quotiented term precision, lifts source `ν`/`ν ★`
  and cast/conversion frames, and rules out value/bullet alternatives that
  cannot target blame.  Consequently backward target blame now depends only
  on completion of the exhaustive one-step dispatcher.

- Ran three further isolated GPT 5.5 leaf packages on Ginger from frozen GPT
  5.6 interfaces.  All three final owned modules are strict and hole-free:

  1. source narrow/widen cast outcome frames;
  2. source reveal/conceal conversion outcome frames; and
  3. source `ν`/`ν ★` pre-allocation terminal-value frames.

  The first source-cast check took about 258 seconds from a cold worker cache.
  The conversion worker's first cold check took about 265 seconds and exposed
  only a wrong module import for `applyCoercions`; the corrected warm strict
  check passed.  This reinforces the policy that each worker runs its owned
  module once, while the integrator batches the nearest consumer checks.

- Connected the four source cast/conversion outcome wrappers to
  `weak-one-step-indexed-simulationᵀ`.  Each dispatcher clause performs the
  structurally smaller recursive call itself, then passes the computed outcome
  to a nonrecursive leaf helper.  This preserves Agda's visibility of
  termination and avoids a dependency cycle through the scratch module.

- Audited the top-level dispatcher against all 29 constructors of the ordinary
  quotiented term-imprecision judgment.  Eleven constructor families are now
  written.  Eighteen remain: four impossible target values (`x⊑xᵀ`, `ƛ⊑ƛᵀ`,
  `Λ⊑Λᵀ`, and `κ⊑κᵀ`) and fourteen real families.  The next low-risk frozen
  leaves are primitive evaluation-context frames, target cast `ξ-⟨⟩` frames,
  and target reveal/conceal `ξ-⟨⟩` frames.  Application redexes, primitive
  `δ`, quotient widening, bullet/allocation-prefix cases, and cast roots remain
  GPT 5.6 work.

- Strengthened the canonical `left-catchup-indexed-prepend-keepᵀ` interface by
  removing its unused intermediate-relation premise.  This is the composition
  boundary needed after an `α⊑ᵀ` residual exposes a source `β-∀•` or `β-gen•`
  `keep` step: the recursive call supplies the residual catch-up directly, so
  no relation needs to be manufactured in the final prefix-extended world.
  The temporary duplicate helper module was discarded in favor of the single
  closed-world API.

- Documented the permanent Ginger setup in
  [`scripts/GINGER_AGDA.md`](../../scripts/GINGER_AGDA.md), with pointers from
  both repository READMEs.  The guide records the repository-local Agda
  wrapper and library registry, the exact worktree workflow, focused-check
  tiers, and the absolute `/home/jsiek/.local/bin/codex` path required by
  non-login SSH worker shells.

### Next boundary

Finish the focused consumer checks for the stronger `keep` composer and the
two source-conversion dispatcher clauses.  Then freeze the primitive
evaluation-context outcome frames as the next independent Ginger slice while
GPT 5.6 continues the `α⊑ᵀ`, quotient-instantiation, and allocation-prefix
catch-up architecture.

### 2026-07-20: `Def`/`Proof`/`Lemma` pilot and root skeletons

- Converted the backward target-value boundary to the canonical three-file
  organization documented in [`proof/README.md`](README.md):
  [`NuDGGTerminalBackwardValueDef`](NuDGGTerminalBackwardValueDef.agda)
  owns the complete contract,
  [`NuDGGTerminalBackwardValueProof`](NuDGGTerminalBackwardValueProof.agda)
  proves it from the one-step and value-catch-up contracts, and
  [`NuDGGTerminalBackwardValueLemma`](NuDGGTerminalBackwardValueLemma.agda)
  supplies the live implementations.  The superseded `Assembly`,
  `Integration`, and partial theorem files were removed rather than retained
  as compatibility shims.  All three new modules contain no holes and do not
  enable unsolved metas; the `Lemma` remains outside `NuDGGStrictSpine` while
  its two supplied implementations are partial.

- Measured the representative conversion with focused `agda -v0` checks.
  The old generic assembly took 5.89 seconds with warm dependencies and the
  new `Proof` took 5.08 seconds.  With the live scratch dependency stale, the
  old integration check took 275.02 seconds and the new `Lemma` took 264.21
  seconds; with dependencies warm, the new `Lemma` took 5.55 seconds.  The
  stale-run difference is small enough to treat as noise.  The demonstrated
  benefit is invalidation isolation and discoverability, not faster checking
  of an implementation dependency that must actually rebuild.

- The split also shrinks the permissive proof surface.  An unfinished live
  dependency is confined to its implementation and the canonical `Lemma`
  assembly; the theorem `Def` and higher-order `Proof` stay independently
  checkable without `--allow-unsolved-metas`.  Avoiding permissive options in
  completed architectural modules is an explicit goal of this organization,
  alongside checking-time isolation.

- The pilot exposed the next measured modularity boundary.  Even the small
  one-step and value-catch-up `Def` files import the large
  `NuImprecisionSimulationCore` interface merely to name
  `WeakOneStepIndexedOutcome` and `LeftCatchupIndexedResult`.  Extracting those
  result records and their prerequisite definitions into a stable definition
  module is the next checking-time experiment.

- Completed a fourth GPT 5.5 Ginger package at remote commit `817e421a`: two
  primitive runtime views, Nat-value inversion, and the two non-crossed
  primitive blame outcomes.  The worker's module-local
  `--allow-unsolved-metas` initially masked several implicit metas despite the
  command-line strict flag.  The local integration removed that option,
  supplied the contexts and result endpoints explicitly, and rechecked
  [`NuImprecisionOneStepPrimitiveLeaves`](NuImprecisionOneStepPrimitiveLeaves.agda)
  with no holes or metas.  The Ginger guide now records this strictness trap.

- Expanded the target conversion and target cast root files into exhaustive
  operational skeletons.  Target blame and grammar-impossible roots are
  complete.  At this point target conversion had two explicit support holes:
  atomic-target desired-index catch-up and quotient-aware target-seal
  cancellation.  The former is completed below; target seal cancellation
  remains.  Target casts have eleven feasible root holes covering identity
  reindexing, sequence factorization, instantiation allocation, and tag/seal
  collapse.  All five root handlers are now connected to
  `weak-one-step-indexed-simulationᵀ`; the focused scratch consumer check
  passed in 195.25 seconds.  After the full integration batch, the nearest
  end-to-end consumer [`NuDGGTerminalSkeleton`](NuDGGTerminalSkeleton.agda)
  passed in 382.85 seconds.  This was a milestone check; neither
  `NuDGGStrictSpine` nor `All.agda` was run.

- Rejected and removed the proposed unrestricted terminal-result reindexing
  lemma.  Duplicate type-imprecision assumptions give distinct same-endpoint
  witnesses, and a related lambda/variable value at one arrow index need not
  be related at the other.  Target identity roots must instead use a
  structurally restricted result such as atomic-target catch-up; reveal
  unsealing requires its separate quotient-aware cancellation theorem.

- At pushed commit `45cc0c68`, an isolated Ginger worktree passed focused
  `--no-allow-unsolved-metas` checks for
  [`NuDGGTerminalBackwardValueProof`](NuDGGTerminalBackwardValueProof.agda),
  [`NuImprecisionOneStepPrimitiveLeaves`](NuImprecisionOneStepPrimitiveLeaves.agda),
  [`NuImprecisionOneStepApplicationRoots`](NuImprecisionOneStepApplicationRoots.agda),
  and
  [`NuImprecisionOneStepTargetBlameRoots`](NuImprecisionOneStepTargetBlameRoots.agda).
  The cold `Proof` check also checked its imported `Def` contracts without
  importing the live partial dispatcher or value catch-up implementation.

### 2026-07-20: stable weak-result definition boundary

- Moved the complete weak-result algebra from the 15,000-line
  [`NuImprecisionSimulationCore`](NuImprecisionSimulationCore.agda) into the
  strict 506-line
  [`NuImprecisionSimulationResultDef`](NuImprecisionSimulationResultDef.agda).
  This includes base, indexed, arrow, universal, silent, and catch-up result
  records plus the two transport normalizers named by type coherence.  The
  move is closed-world: all consumers import moved names directly, and the
  core neither aliases nor publicly re-exports them.

- Inlined the matched-binder assumption context in the result declarations
  instead of importing the 20,000-line `MaximalLowerBoundsWf` module merely
  for its local `∀ᵢᶜ` abbreviation.  The result module contains no holes,
  permissive options, simulation implementation, or recursive dispatcher.

- Focused checks demonstrate the new boundary.  The result module passed in
  3.57 seconds; `NuImprecisionOneStepDef` and
  `NuImprecisionValueCatchupDef` passed in 3.16 and 3.39 seconds; and the
  higher-order backward-value `Proof` passed in 3.92 seconds.  After a source
  change deliberately invalidated `NuImprecisionSimulationCore`, the same
  `Proof` still passed in 3.23 seconds without rebuilding the core.

- The relocated core passed in 47.24 seconds, a mixed primitive-frame
  consumer passed in 46.19 seconds, the broad batched scratch dispatcher
  passed in 288.55 seconds, and the backward-blame assembly passed in 2.87
  seconds.  These were focused migration checks; `NuDGGStrictSpine`,
  `NuDGGTerminalSkeleton`, and `All.agda` were not rerun.

- At pushed commit `336d17ca`, a fresh isolated Ginger worktree passed
  focused `--no-allow-unsolved-metas` checks for
  `NuImprecisionSimulationResultDef`, `NuImprecisionWorldCoherenceDef`,
  `NuImprecisionAtomicTargetReindex`, and
  `NuDGGTerminalBackwardValueProof`.  The last check transitively checked the
  decoupled one-step and value-catch-up `Def` contracts without importing the
  live scratch implementations.

- Completed strict
  [`atomic-target-value-reindexᵀ`](NuImprecisionAtomicTargetReindex.agda),
  which recursively rebuilds the quotiented term relation at the desired
  index and uses atomicity plus target value shape to eliminate the unsound
  general cases.  It does not prove the old and new indices equal: duplicate
  type assumptions make that false.  The target conversion identity roots
  now consume this theorem, leaving only reveal-unseal in that root module.

- The target reveal/seal hole is not yet a safe Ginger leaf.  Exact-world
  cancellation needs an explicit world/store-name coherence invariant; the
  current weak-result type can otherwise hide the missing invariant by
  choosing an enriched result imprecision context.  The strict
  [`NuImprecisionWorldCoherenceDef`](NuImprecisionWorldCoherenceDef.agda) now
  freezes the minimal `WorldCoherent` contract: every live `idˣ` assumption
  whose endpoints are physically stored returns an exact `StoreCorresponds`
  witness.

### 2026-07-20: strict world-coherence boundary

- Completed strict
  [`NuImprecisionWorldCoherenceProof`](NuImprecisionWorldCoherenceProof.agda).
  It proves the empty world, exact obligations for each store-entry extension,
  correspondence weakening, and coherence preservation through the matched,
  left-only, and right-only canonical store lifts.  The lift theorems are
  deliberately specialized to the reflected allocation contexts: arbitrary
  lift target contexts can introduce a new live `idˣ` assumption between two
  previously unrelated one-sided physical entries, so unrestricted lift
  preservation is false.

- Completed strict single-name allocation assembly in
  [`NuImprecisionWorldCoherenceLemma`](NuImprecisionWorldCoherenceLemma.agda).
  Matched allocation uses absence of physical name `0` from both shifted
  stores; source-only and target-only allocation use absence of a corresponding
  `idˣ` assumption at the freshly allocated endpoint.  Crossed two-name
  allocation remains the outstanding structural case.

- Added a separate acyclic statement layer above the generic weak-result
  algebra:
  [`NuImprecisionWorldCoherentResultDef`](NuImprecisionWorldCoherentResultDef.agda),
  [`NuImprecisionWorldCoherentOneStepDef`](NuImprecisionWorldCoherentOneStepDef.agda),
  and
  [`NuImprecisionWorldCoherentValueCatchupDef`](NuImprecisionWorldCoherentValueCatchupDef.agda).
  Related one-step branches carry coherence of their successor store; source
  blame branches do not need a successor invariant.  Catch-up results expose
  final coherence so existing compositional frames need not split on their
  terminal alternative.

- Froze the full strengthened arbitrary-world terminal statement as
  [`WorldCoherentBackwardTargetValueOrSourceBlameᵀ`](NuDGGTerminalBackwardValueWorldCoherentDef.agda).
  Its only new public-support premise is `WorldCoherent ρ`; its terminal
  alternatives and the eventual closed `ClosedNuDGG` conclusion are unchanged.
  A higher-order proof instantiating the new one-step and catch-up contracts is
  the next top-level fit check.

- All seven new or extended world-coherence modules were checked with focused
  `--no-allow-unsolved-metas` commands.  No aggregate module was checked.

### 2026-07-20: strict target-seal and β-id boundaries

- Integrated Ginger commit `d220d73` as strict
  [`NuImprecisionOneStepTargetCastIdentityRoots`](NuImprecisionOneStepTargetCastIdentityRoots.agda).
  Its three theorems invert an identity narrowing/widening derivation to an
  atomic target and reuse `atomic-target-value-reindexᵀ`.  The target-cast
  dispatcher now has eight explicit roots instead of eleven, and its focused
  permissive check passes.  No aggregate check was run.

- Froze
  [`TargetSealCancellationᵀ`](NuImprecisionTargetSealCancellationDef.agda)
  as a separate strict proposition.  The statement exposes every assumption
  needed at the terminal exact world: `WorldCoherent`, target `StoreWf`, the
  target seal's physical store membership, source and target value facts, the
  source `No•` fact, and both proof-relevant type-imprecision indices.  The
  `Def` module passes `--no-allow-unsolved-metas` independently of the hard
  proof.

- Established the three-file boundary
  `NuImprecisionTargetSealCancellationDef`,
  `NuImprecisionTargetSealCancellationProof`, and
  `NuImprecisionTargetSealCancellationLemma`.  The implemented core of the
  `Proof` uses ambient-prefix recursion: source seals obtain exact
  correspondence from `WorldCoherent`, target-only seals use atomic
  reindexing, paired conceal retains only its source conceal, and allocation
  prefixes rebuild after target typing inversion.  The first local consumer
  check exposed missing impossible value/cast clauses and two unresolved mode
  metas; an exhaustive follow-up eliminated the incompatible target widening,
  paired reveal/widening, and inert-source cases and fixed the modes explicitly.
  The exact `Lemma` consumer and strict checks now pass.  The split keeps the
  live target-conversion dispatcher out of both `Def` and `Proof`, so the hard
  theorem is checked without inheriting that file's
  `--allow-unsolved-metas`.

- Made the no-unsolved-metas benefit an explicit organization criterion.
  Missing major proofs are represented by whole theorem contracts passed to
  strict higher-order `Proof` modules.  Holes are therefore confined to the
  remaining legacy scratch dispatchers while those files are decomposed; new
  skeleton, boundary, and worker modules are expected to be strict from their
  first checked version.

- Completed strict
  [`world-coherent-backward-target-value-or-source-blame-proofᵀ`](NuDGGTerminalBackwardValueWorldCoherentProof.agda).
  The higher-order theorem consumes only the strengthened one-step and value
  catch-up contracts, threads `WorldCoherent` through related successor worlds,
  and preserves the existing fuel decrease, target-tail alignment, and source
  trace composition.  It therefore checks the strengthened invariant against
  the complete top-level terminal induction before any live dispatcher is
  promoted.

- Extracted the canonical keep-step result construction into strict
  [`NuImprecisionOneStepRelated`](NuImprecisionOneStepRelated.agda).  Target
  identity roots now import this small result builder rather than
  `NuImprecisionSimulationCore`.  The immediate cold focused check still pays
  for the quotient relation and atomic reindexer, but future edits to the
  15,000-line simulation implementation no longer invalidate these leaves.

- Integrated Ginger commit `94857b15` as strict
  [`world-coherent-crossed-allocation`](NuImprecisionWorldCoherenceCrossedLemma.agda).
  It reflects tail assumptions and physical store members through the two
  canonical lifts, proves the two fresh head assumptions cannot apply to the
  pre-allocation tail, and assembles all six entries of `crossedStoreⁱ` using
  the two exported crossed correspondences.  The focused Ginger check,
  diff check, and line-length audit pass.

- Completed the strict coherent reveal-unseal root boundary in
  [`NuImprecisionWorldCoherentTargetRevealRootDef`](NuImprecisionWorldCoherentTargetRevealRootDef.agda)
  and
  [`NuImprecisionWorldCoherentTargetRevealRootProof`](NuImprecisionWorldCoherentTargetRevealRootProof.agda).
  The higher-order proof consumes only the coherent value-catch-up and exact
  seal-cancellation contracts.  Its value branch transports target store
  typing and membership into the final catch-up world, cancels at the
  transported desired index, and rebuilds the result with unchanged transport,
  type-coherence, trace, and final-world evidence; its other branch returns
  source blame.  Both focused strict checks pass.  The canonical `Lemma` is
  deliberately not created until coherent catch-up has a strict inhabitant.

- Froze the value-catch-up induction invariant as strict
  [`WorldCoherentLeftValueCatchupPrefixᵀ`](NuImprecisionWorldCoherentValueCatchupPrefixDef.agda).
  It carries coherence for ambient `ρ⁺` while allowing the current quotient
  relation to live in a smaller prefix world `ρ₀`.  This distinction is
  necessary because an arbitrary prefix can contribute correspondences that
  are absent from its tail, so coherence cannot soundly be recovered by a
  post-hoc wrapper around an ordinary catch-up result.  The strict
  [`world-coherent-left-value-catchup-proofᵀ`](NuImprecisionWorldCoherentValueCatchupProof.agda)
  specializes that prefix capability at `prefix-reflⁱ`, checking the path from
  the recursive invariant to the public catch-up contract without importing
  the partial scratch implementation.

- Extracted `lift-left-store-result` and `lift-right-store-result` from the
  simulation core into strict
  [`NuImprecisionStoreLift`](NuImprecisionStoreLift.agda).  The core imports
  the new module non-publicly, and `NuImprecisionSimulation` imports the right
  lift directly; there is no compatibility re-export.  Focused checks passed
  for the new module, the modified core, and the direct simulation consumer.
  The cold new-module check took about 86 seconds because its existing lift
  lemmas still pull in a large dependency cone; that is a future profiling
  target, but edits to the 15,000-line core no longer invalidate the canonical
  store-lift constructors.  No aggregate check was run.

- Extracted `leftStoreⁱ-prefix-inclusion`,
  `rightStoreⁱ-prefix-inclusion`, and `store-imp-prefix-transⁱ` into strict
  [`NuImprecisionStorePrefix`](NuImprecisionStorePrefix.agda).  Core,
  simulation, catch-up scratch, and the source-allocation terminal helper now
  import it directly; the core does not re-export the moved names.  Focused
  checks passed for the new module, Core, Simulation, and the terminal helper.
  The partial scratch consumer produced no diagnostics but was stopped around
  85 seconds under the checking-cost policy.  No aggregate check was run.

- Reduced the ten visible coherent catch-up holes to two semantic higher-order
  capabilities.  `WorldCoherentSourceRuntimeCatchupᵀ` keeps source bullet,
  source allocation, and the five source cast/conversion handlers in one record
  because source `inst` catch-up and `ν ★` allocation form a real proof SCC.
  `WorldCoherentQuotientInstCatchupᵀ` is one mode-polymorphic final-state
  contract shared by the ordinary-down and gen-down quotient residuals.  The
  future strict prefix proof will take exactly those two dependencies; target
  frames and terminal cases preserve an already-established final coherence.

- Froze both capabilities as strict statement modules.  The eight-field
  [`WorldCoherentSourceRuntimeCatchupᵀ`](NuImprecisionWorldCoherentSourceRuntimeCatchupDef.agda)
  mirrors the live `α⊑ᵀ`, source allocation, cast, and conversion branch
  telescopes; in particular, the bullet field retains the full allocated-world
  lifts and coherence premise instead of hiding them behind a simplified term
  shape.  The single
  [`WorldCoherentQuotientInstCatchupᵀ`](NuImprecisionWorldCoherentQuotientInstCatchupDef.agda)
  contract uses the actual quotiented relation and `QuotientWideningPair`, so
  ordinary-down and gen-down share one final-state obligation without an extra
  mode or implementation premise.  Both focused no-unsolved-metas checks pass.

- Stopped the first Ginger β-sequence worker after it made no worktree changes
  during an overlong search.  Its useful diagnostic is that the nested target
  relation needs a midpoint imprecision witness, while the current dispatcher
  root receives only the final index `q`.  This is now an interface/factorization
  question for local GPT 5.6 analysis, not another blind leaf assignment.

- Refined that interface question locally and with a narrow Ginger attempt.
  `right-id-only-compatible` supplies the context-composition half of the
  id-only widening midpoint, but the existing `widening⇒⊑ᵢ` route requires
  dense `Store.StoreWf`; the dispatcher intentionally carries sparse
  `NuStore.StoreWf`.  The branch is not generally impossible because ground
  base/function tags remain available in id-only mode.  Thus all three general
  sequence handlers still need local midpoint evidence, unless a separate
  sparse-store cast-embedding theorem is proved.  For general narrowing and
  widening, a global `RightCastCtxCompatible`
  premise is not sound for this purpose because matched `gen` and `inst` worlds
  are intentionally incompatible.  The strict indexed family
  [`TargetCastSequenceMidpointᵀ`](NuImprecisionTargetCastSequenceMidpointDef.agda)
  instead records local split evidence on one quotiented target-cast node.  The
  future constructor change should retain that witness beside `p` and `q`, and
  the β-sequence root should consume it explicitly.

- Proved that the proposed midpoint is sufficient in strict
  [`NuImprecisionOneStepTargetCastSequenceRoots`](NuImprecisionOneStepTargetCastSequenceRoots.agda).
  Its narrowing and widening helpers take the two typed component casts, the
  explicit midpoint `r`, and final `q`, then rebuild the target reduct using two
  nested quotient cast constructors and the canonical unchanged-source result
  wrapper.  The module imports neither store well-formedness nor the scratch
  dispatcher or simulation core, and its focused no-unsolved-metas check passes.

- Extracted the first nine hole-free catch-up implementation helpers into
  strict
  [`NuImprecisionCatchupPrefixSupport`](NuImprecisionCatchupPrefixSupport.agda).
  The module now owns silent-result resumption, the generic target frame, all
  five target narrow/widen/reveal/conceal prefix frames, and the terminal
  source value and blame builders.  The old definitions were deleted from
  `NuImprecisionCatchupScratch`, which imports the canonical module directly;
  there is no compatibility re-export.  The focused Ginger check passed with
  `--no-allow-unsolved-metas` after the dependency cache warmed.  The partial
  Scratch consumer reached the 90-second bound without diagnostics, and no
  aggregate module was checked.

- Audited the remaining strict prefix dispatcher clause by clause.  Once the
  eight hole-free quotient/down-up transport helpers are extracted into
  `NuImprecisionCatchupQuotientSupport`, the higher-order prefix proof can be
  written without importing the permissive Scratch module.  Its only semantic
  parameters remain `WorldCoherentSourceRuntimeCatchupᵀ` and
  `WorldCoherentQuotientInstCatchupᵀ`.  The quotient residual needs a local
  control-flow split retaining the final source `Value`/`No•` evidence and a
  dependent rewrite by the discovered `inst` shape; neither issue requires a
  broader contract.

- Audited the eight source-runtime fields against the existing strict leaves.
  Only `source-conceal` is presently a direct frame/administrative-step proof.
  `source-bullet`, `source-ν`, `source-νcast`, and widening `inst` form the
  genuine allocation SCC.  Active reveal needs source-side exact seal
  cancellation; active narrowing/widening need tag/untag
  cancellation/classification; paired casts need `PairedCast` transport across
  the ambient prefix and accumulated source changes.  This dependency graph is
  now part of the proof plan so a strict-looking implementation cannot close
  those fields by circularly assuming the whole source-runtime record.

- Extracted the second strict implementation island into
  [`NuImprecisionCatchupQuotientSupport`](NuImprecisionCatchupQuotientSupport.agda).
  Its eight definitions cover paired double-cast framing, final runtime
  recovery, source/target narrowing transport, ordinary and generated down
  transport, quotient-widening transport, and final silent down-up framing.
  The old definitions were deleted from Scratch, while the two drivers with
  real quotient-`inst` holes remain there.  Source audits and `git diff
  --check` are clean; the focused strict check produced no diagnostics before
  its 90-second bound.  No aggregate check was run.

- Added strict
  [`world-coherent-left-catchup-indexed-resume-silentᵀ`](NuImprecisionWorldCoherentCatchupComposition.agda).
  The wrapper composes the existing silent result with a coherent resumed
  catch-up and reuses the resumed result's final-world witness, matching the
  composed result store definitionally.  Source audits are clean.  Two local
  focused attempts were stopped after 60 seconds without diagnostics under the
  checking-cost policy; completion of a warmed focused check remains a
  verification task rather than a reason to run a larger aggregate.

### 2026-07-20: strict coherent catch-up skeleton and first Ginger leaf

- Strengthened
  [`WorldCoherentLeftCatchupIndexedResult`](NuImprecisionWorldCoherentResultDef.agda)
  with final left `StoreWf`.  Initial left well-formedness is now visible in
  both coherent value-catch-up contracts, and both left/right well-formedness
  premises are visible in the coherent one-step contract.  The change was
  threaded through backward-value assembly and the target reveal root.  This
  is not redundant bookkeeping: active source unseal needs uniqueness in the
  final left store.

- Added strict
  [`NuImprecisionWorldCoherentCatchupPrefixFrames.agda`](NuImprecisionWorldCoherentCatchupPrefixFrames.agda).
  Its five target-only frame wrappers preserve the final world and left store
  by dependent pattern matching, making those invariants definitionally
  visible to the recursive dispatcher.

- Froze
  [`WorldCoherentQuotientFinalCatchupᵀ`](NuImprecisionWorldCoherentQuotientFinalCatchupDef.agda)
  as a major semantic join.  An attempted skeleton using only the narrower
  quotient-`inst` contract failed exactly where it tried to attach coherence
  to a generic classifier result.  The final-node contract instead returns a
  coherent, left-well-formed result for the complete terminal quotient node.

- Audited that final quotient join exhaustively and froze
  [`WorldCoherentQuotientClassificationᵀ`](NuImprecisionWorldCoherentQuotientClassificationDef.agda).
  It retains coherence and left `StoreWf` in every ordinary store-neutral
  outcome and packages source value/no-bullet evidence with the sole
  outer-`inst` residual.  The strict
  [`world-coherent-quotient-final-catchup-proofᵀ`](NuImprecisionWorldCoherentQuotientFinalCatchupProof.agda)
  now proves the final contract from exactly that classifier and
  `WorldCoherentQuotientInstCatchupᵀ`; it does not depend on source-runtime
  catch-up.

- Completed the exhaustive higher-order
  [`world-coherent-left-value-catchup-prefix-proofᵀ`](NuImprecisionWorldCoherentValueCatchupPrefixProof.agda).
  It takes only `WorldCoherentSourceRuntimeCatchupᵀ` and
  `WorldCoherentQuotientFinalCatchupᵀ`, imports no permissive scratch
  dispatcher, and passes
  `agda --no-allow-unsolved-metas -v0` on its own module.  All ordinary target
  frames, terminal values/blame, allocation-prefix reassociation, and
  quotient down/up recursion are therefore checked before the semantic leaf
  implementations exist.

- The first exact source-seal contract in
  [`NuImprecisionSourceSealCancellationDef.agda`](NuImprecisionSourceSealCancellationDef.agda)
  did not survive strict proof audit.  The hole-free
  [`source-seal-cancellation-needs-exclusivity`](NuImprecisionSourceSealCancellationCounterexample.agda)
  packages a valid old premise with an impossible conclusion: a context may
  contain both a source-only
  row `0 ˣ⊑★` and a matched row `0 ˣ⊑ˣ 0`, leaving the target seal
  protected by a tag after the proposed source cancellation.  The replacement
  boundary must carry source-only-versus-matched name exclusivity.  This is a
  separate imprecision-context invariant, not a strengthening of
  `WorldCoherent`, whose empty-store constructor is intentionally valid for
  arbitrary contexts.

- Repaired
  [`SourceSealCancellationᵀ`](NuImprecisionSourceSealCancellationDef.agda) by
  making `SourceNameExclusive Φ` an explicit premise.  The counterexample now
  lives in a separately named strict module, leaving the canonical `Proof`
  filename available for the real exclusivity-aware inversion proof.

- Completed
  [`source-seal-cancellation-proofᵀ`](NuImprecisionSourceSealCancellationProof.agda)
  and its canonical
  [`Lemma`](NuImprecisionSourceSealCancellationLemma.agda).  The proof is an
  exhaustive ambient-prefix inversion.  `SourceNameExclusive` is used in
  exactly the two target tag-widening cases where outer `tagˣ` and inner
  `idˣ` would assign the same source name incompatible roles; all other cases
  use store uniqueness, coherent correspondence, cast/conversion inversion,
  atomic-target reindexing, or prefix recursion.

- Completed strict higher-order
  [`world-coherent-source-unseal-catchup-proofᵀ`](NuImprecisionWorldCoherentSourceUnsealCatchupProof.agda).
  It consumes the repaired cancellation contract, extracts final coherence,
  exclusivity, and left-store well-formedness from the inner catch-up, performs
  the source seal-unseal keep step, and preserves all three invariants.  A
  structural `AppliedUnseal` view exposes equalities for the transformed
  coercion and types, avoiding a non-constructor `applyCoercions` pattern.
  Its canonical
  [`Lemma`](NuImprecisionWorldCoherentSourceUnsealCatchupLemma.agda) strictly
  supplies the completed source-seal cancellation dependency.

- Added strict
  [`SourceNameExclusive`](NuImprecisionContextExclusivityDef.agda) and its
  [`structural preservation proofs`](NuImprecisionContextExclusivityProof.agda).
  The invariant is preserved by empty, matched, source-only, target-only, and
  crossed context construction.  Both modules check independently with
  `--no-allow-unsolved-metas` and import no simulation implementation.

- Threaded source-name exclusivity through the strict top-level skeleton.
  Related one-step outcomes and catch-up results now carry the final invariant;
  the one-step, value-catch-up, prefix, quotient, source-runtime, target-reveal,
  and arbitrary-world backward-value contracts consume it explicitly.  The
  structural prefix proof, silent composition, five target frames,
  source-conceal leaf, quotient classifier, target reveal root, and
  backward-value fuel induction all pass focused strict checks after the
  change.  No aggregate module was checked.

- Audited the quotient-`inst` residual against the actual `β-inst` branch.
  [`WorldCoherentQuotientInstCatchupᵀ`](NuImprecisionWorldCoherentQuotientInstCatchupDef.agda)
  and
  [`WorldCoherentQuotientClassificationᵀ`](NuImprecisionWorldCoherentQuotientClassificationDef.agda)
  now retain `Value (V ⟨ d ⟩)` and `No• (V ⟨ d ⟩)`, rather than the
  weaker facts about `V`.  The remaining `Inst` proof is an independent hard
  leaf: source-runtime handlers require an ordinary relation, but the quotient
  view does not supply the representative-to-coercion alignment needed to
  construct it.

- Integrated the GPT 5.5 Ginger
  [`world-coherent-quotient-classification-proofᵀ`](NuImprecisionWorldCoherentQuotientClassificationProof.agda).
  Its exhaustive active/inert analysis packages every store-neutral result
  with final world coherence, source-name exclusivity, and left `StoreWf`.
  The outer-`inst` branch returns the actual ready inner down-cast value and
  no-bullet proof.  The adapted local module passes its focused strict check.

- Rejected generic quotient-to-ordinary alignment with strict
  [`NuImprecisionQuotientToOrdinaryCounterexample.agda`](NuImprecisionQuotientToOrdinaryCounterexample.agda).
  In the empty, hence source-exclusive, context, an adjacent two-`∀` swap is
  quotient-related while exhaustive inversion rules out an ordinary relation
  between the endpoints.  Quotient-`inst` must therefore recurse directly over
  permutation evidence instead of feeding a fabricated ordinary relation to
  source-runtime catch-up.

- Froze pure
  [`SourceTagCancellationᵀ`](NuImprecisionSourceTagCancellationDef.agda) as a
  GPT 5.5 leaf.  A separate audit strengthened `source-paired-cast` with the
  caller's existing `Inert c′` witness and identified final
  `StoreCorresponds` reconstruction across accumulated source changes as its
  hard transport boundary.

- Integrated the first GPT 5.5 Ginger semantic leaf,
  [`world-coherent-source-conceal-catchupᵀ`](NuImprecisionWorldCoherentSourceConcealCatchup.agda).
  Identity conceal performs one administrative `β-id` step; seal, arrow, and
  universal conceal are inert frames; source blame is propagated.  After
  adapting the worker result to retain final left `StoreWf`, the local focused
  strict check passes.

- Added [`scripts/codex-ginger`](../../scripts/codex-ginger) and documented it
  in [`scripts/GINGER_AGDA.md`](../../scripts/GINGER_AGDA.md).  The wrapper
  gives a Codex worker write access only to the installed standard-library
  `_build` interface cache.  This fixes the previously recurring
  `removeLink: permission denied` failure without broadening access to the
  standard-library source or the rest of the remote home directory.

- Recorded the separate Ginger Git handoff.  A worktree's real Git directory
  is outside the Codex `workspace-write` sandbox, so workers now stop after
  their owned-file strict check.  The coordinator reviews, stages, commits,
  and pushes the exact owned paths through the ordinary SSH session.  This
  avoids recurring `index.lock` and sandboxed-network failures without
  granting the proof worker broad access to the shared repository metadata.

- Made strictness an architectural acceptance condition for the three-file
  split.  A missing canonical leaf is represented by an uninstantiated theorem
  parameter in a strict `Proof` module, never by a hole or file-level
  `--allow-unsolved-metas`.  This both checks integration fit early and keeps
  partial implementations out of the dependency cone of already-completed
  theorem skeletons.  The rejected source-seal contract and narrowed
  quotient-`inst` residual are concrete contract errors found by this policy.

- Strictly checked the corrected source cast-sequence obstruction in
  [`NuImprecisionSourceCastSequenceMidpointCounterexample.agda`](NuImprecisionSourceCastSequenceMidpointCounterexample.agda).
  The example has coherent, source-exclusive, typed two-seal endpoints but no
  midpoint.  It necessarily violates `SealModeStore★`; the reusable
  `seal-enabled-store-entry-star` lemma shows that store uniqueness forces any
  seal-enabled entry to carry `★`.  Therefore the full source-runtime contract
  is not refuted, and the remaining hard task is a positive restricted
  midpoint decomposition using its real mode/store hypotheses.

- Integrated the strict GPT 5.5 source-reveal proof and added its canonical
  `Lemma`.  The higher-order `Proof` covers all six `RevealConversion` forms;
  active unseal is the only semantic dependency and is supplied as the whole
  completed `WorldCoherentSourceUnsealCatchupᵀ` contract.  Both focused local
  checks pass with unsolved metas disabled.

- Split source paired-cast catch-up into exact accumulated transport, exact
  final-world semantics, and top handler contracts.  The top higher-order
  proof is complete and strict.  This confines the remaining work to final
  `StoreCorresponds` transport and exact-world paired-cast behavior instead of
  leaving an opaque hole in the source-runtime record.

- Added the direct representative-level quotient-`inst` contract and a strict
  higher-order proof reducing the existing final-state contract to it.  The
  representative statement exposes `quotientᵖ D≈C C⊑C′ C′≈D′`; the remaining
  proof must interpret arbitrary `≈∀` constructors compositionally, while the
  canonical `Lemma` stays absent.

- Completed the positive strict
  [`SourceCastSequenceMidpointᵀ`](NuImprecisionSourceCastSequenceMidpointDef.agda)
  `Def`/`Proof`/`Lemma` triple.  The exact source-runtime hypotheses are
  sufficient: tag/untag strict-cross shapes expose the ground midpoint, while
  prefix inclusion, `SealModeStore★`, and final sparse-store uniqueness make
  the problematic seal/unseal sequence shapes impossible.

- Split accumulated paired-cast transport by constructor family.  The full
  higher-order proof now takes a paired-conversion capability and a
  paired-widening capability explicitly.  The widening contract requires no
  final-world coherence and is a frozen GPT 5.5 leaf; all paired
  `StoreCorresponds` reconstruction is confined to the hard conversion
  contract.

- Split exact-final-world paired-cast semantics by constructor family and
  completed the strict higher-order assembly.  The paired-conversion contract
  isolates target-seal/source-identity cancellation, while paired widening
  isolates its active source-`inst` allocation case.  The assembly imports no
  recursive source-runtime or value-catch-up dispatcher.

- Completed exact-final paired-conversion catch-up without an additional
  cancellation assumption.  Source identity conversions take `β-id`, inert
  conversions remain terminal frames, source blame propagates, and source
  unseal is ruled out by exhaustive inversion against target inertness.

- Reduced accumulated paired-conversion transport to the genuine relational
  world-embedding boundary
  [`LeftSilentStoreCorrespondsTransportᵀ`](NuImprecisionLeftSilentStoreCorrespondsTransportDef.agda).
  The higher-order endpoint proof is complete; only preservation of stored and
  linked correspondence evidence remains.  In particular, final
  `WorldCoherent` cannot recover `store-link` entries absent from both projected
  stores.

- Audited the missing correspondence theorem against all result constructors.
  The smallest sufficient invariant is relational-store renaming/embedding
  followed by an allocation prefix.  It should be added only to
  `WorldCoherentLeftCatchupIndexedResult`, then preserved by the coherent
  composition/frame proofs and supplied by allocation witnesses.  This plan
  carries linked entries without bloating generic `WeakOneStepResult` or using
  unsolved metas.

- Completed the GPT 5.5 paired-widening transport leaf on Ginger and added its
  canonical `Lemma`.  The helper can return either `quotient-cast-widening` or
  `quotient-id-widening`; the proof covers both explicitly, relaxing id-only
  evidence to `tag-or-idᵈ` in the latter case.  The first cold focused check
  spent several minutes rebuilding its broad quotient-support dependency;
  the warmed coordinator recheck took under ten seconds, identifying helper
  extraction as a future invalidation optimization.

- The Ginger source-tag audit exposed a surviving `up⊑upᵀ` branch whose inner
  relation is quotiented.  A GPT 5.6 follow-up proved the strictly smaller
  [`GroundValueQuotientEliminationᵀ`](NuImprecisionGroundValueQuotientEliminationDef.agda)
  theorem from the contract's existing ground/value hypotheses and completed
  the quotient-up adapter.  Thus the original source-tag statement remains
  sound, while unrestricted quotient-to-ordinary alignment remains false.

- Completed the source-tag `Proof`/`Lemma` pair.  The proof is higher-order over
  exactly `GroundValueQuotientEliminationᵀ`, recurses structurally through
  target casts/conversions and allocation prefixes, and handles both quotient
  widening constructors explicitly.  Its focused strict recheck takes about
  four seconds on the current cache.

- Performed the closed-world checking-time extraction prompted by the cold
  Ginger leaf.  `apply-widens-typing` and `apply-fixed-widens-typing` moved to
  `NuWideningTransport`, quotient widening-pair transport moved to
  `NuImprecisionQuotientWideningTransport`, and `modeRename-id-only` moved to
  `CoercionProperties`; original definitions were deleted and every consumer
  retargeted.  The paired-widening proof now checks in about three seconds and
  its source cone contains no simulation-core or broad quotient-support import.

- Normalized arbitrary representative permutations before attempting
  quotient-`inst` semantics.  The new path `Def` exposes a finite sequence of
  oriented contextual adjacent swaps; the strict higher-order `Proof`
  eliminates `sym`, `trans`, and congruence from the remaining semantic
  recursion.  What remains is the honest identity/prepend-one-swap capability,
  rather than an unstructured proof over arbitrary permutation derivations.

- Froze the exact weak-result store-lineage statement and completed its first
  consumer.  Lineage consists of `RelStoreEmbeddingⁱ` under accumulated
  source/target renamings followed by `StoreImpPrefix` into the result store;
  this is sufficient to preserve both stored and linked correspondence.
  Construction and propagation through coherent catch-up remain partial.

- Extracted relational-store embedding and correspondence transport from the
  14k-line simulation core into focused `Def` and `Proof` modules, deleting the
  original definitions and retargeting all consumers.  The four new focused
  checks take roughly 2.6--3.1 seconds.  One deliberate strict core migration
  check passed in about 38 seconds; no aggregate check was run.

- Refuted the unrestricted exact-final paired-widening contract with a strict
  counterexample.  In a coherent matched `★` store, `PairedCast` permits active
  source `unseal 0 ★` to be paired with inert target `(＇ 0) !`, while choosing
  endpoint witnesses `＇ 0 ⊑ ＇ 0` and `★ ⊑ ★` independently.  The source
  cancels its seal, the target remains inert, and any claimed final relation
  would imply the constructorless judgment `Nat ⊑ ＇ 0`.  This is not a missing
  proof lemma: either paired widening must carry compatibility tying its
  endpoint witnesses to both casts, or the relevant relation constructor must
  exclude the cross-mode pair.  No permissive `Proof` or canonical `Lemma` was
  created for the false contract.

- Audited the counterexample against the closed proof boundary.  It does not
  currently refute `ClosedNuDGG` or public DGG: synchronized `ν ★` allocation
  constructs both fresh casts under `cast-inst` modes, where the fresh zero is
  `seal-or-id`, so the bad target variable tag cannot be produced.  Old casts
  shift away from the fresh zero, and ordinary matched allocation constructs a
  paired conversion instead.  The defect is that the arbitrary-world helper
  forgot this allocation provenance and therefore quantified over more paired
  widenings than the closed simulation generates.

- Mechanized the smallest reusable repair.  Every paired widening now carries

  \[
    \operatorname{Inert}(c)
    \;\lor\;
    (\operatorname{Inert}(c') \to B \sqsubseteq A').
  \]

  The source-inert arm retains valid identical tags and inert function casts.
  If the terminal target is inert and the source is active, the second arm
  supplies exactly the bridge needed to catch the source up to the target
  operand before framing `c′`.  No equality tying final proof index `q` to a
  composed derivation is needed: `⊑cast⊑ᵀ` accepts the exact `q` explicitly.
  The compatibility contract is a genuine reusable concept in
  [`PairedWideningCompatibility.agda`](../PairedWideningCompatibility.agda),
  and both `PairedCast.paired-widening` and `νcast⊑νcastᵀ` carry it.

- Migrated the compatibility witness through the strict proof surface.
  GPT 5.5 Ginger workers repaired ground quotient elimination, atomic target
  reindexing, source/target cancellation consumers, and left-silent paired
  widening transport from frozen interfaces.  GPT 5.6 integration repaired
  the simulation core and allocation SCC, including two-sided and left-only
  renaming, binder lifting, weak frames, source-blame allocation, result
  transport, type coherence, and indexed outcomes.  Focused strict checks pass
  for every changed consumer; no aggregate `All.agda` or strict-spine check was
  run for this batch.  A read-only audit found no blocker in the strict modules
  and isolated the remaining stale constructor patterns to the explicitly
  permissive [`NuImprecisionCatchupScratch.agda`](NuImprecisionCatchupScratch.agda).

- Repaired and proved exact-final paired-widening catch-up.  The strict
  [`Def`](NuImprecisionWorldCoherentFinalPairedWideningCatchupDef.agda) requires
  compatibility.  The strict higher-order
  [`Proof`](NuImprecisionWorldCoherentFinalPairedWideningCatchupProof.agda)
  handles source blame, source-inert terminal values, and the
  source-active/target-inert bridge.  The last case calls the supplied whole
  `WorldCoherentSourceWidenCatchupᵀ` contract and then frames the target cast.
  This exposes the smallest honest mutual dependency instead of a hole: the
  canonical `Lemma` is not created until mutual source-widen assembly can
  supply it.

- Converted the old counterexample into a strict regression.  Its active
  source unseal and inert target variable tag cannot satisfy either
  `PairedWideningCompatible` constructor.  Thus the repaired theorem excludes
  exactly the bad pair while preserving the diagnostic as an independently
  checked module.

- Confirmed the strictness benefit of the three-file organization in this
  repair.  The theorem statement and its higher-order proof both pass
  `--no-allow-unsolved-metas` even though canonical mutual assembly is not yet
  available.  Missing work is visible as a whole theorem parameter and an
  absent `Lemma`, rather than an unsolved meta or a permissive module option.

### Next boundary

Use completed source tag cancellation and midpoint recovery in the non-`inst`
narrowing/widening handlers, while constructing store lineage through the
coherent catch-up result families needed by paired conversion.  For
representative quotient-`inst`, prove identity and prepend-one-oriented-swap
path semantics; normalization and the adapter to the original contract are
already complete.  For paired widening, assemble the now-strict terminal proof
inside the genuine source-widen/paired-cast mutual SCC; do not manufacture a
standalone canonical `Lemma` before that join exists.  Once the quotient bridge
is complete, assemble it with the completed classifier, quotient-final proof,
and structural prefix proof.  Continue assigning only frozen, nonoverlapping
leaf modules to Ginger; keep allocation SCCs, arbitrary quotient-permutation
interpretation, mutual assembly, and dependent transport joins under GPT 5.6
coordination.  Use focused strict checks throughout and reserve
`NuDGGStrictSpine.agda` and `All.agda` for milestones.

### 2026-07-21: source-handler contracts and SCC audit

- Split the large source-runtime statement at genuine semantic boundaries.
  Source bullet, ordinary source `ν`, runtime source `ν ★`, source narrowing,
  and source widening now each have a strict whole-contract `Def` module.  The
  eight-field runtime record refers to those contracts rather than repeating
  their telescopes.  This is a naming and checking boundary; it does not claim
  that the cyclic canonical inhabitants can be assembled independently.

- Added exact-final source-narrowing and source-widening contracts.  They
  separate terminal cast semantics from the generic adapter that transports a
  cast through the operand catch-up's accumulated source changes.  In
  particular, active widening `inst` is now visible as the allocation-sensitive
  exact-final case instead of being represented by a hole in a broad handler.

- Completed the strict higher-order source-bullet proof.  It reconstructs the
  allocated `α⊑ᵀ` relation from the former runtime-field premises and invokes
  `WorldCoherentLeftValueCatchupPrefixᵀ`.  The `Def`, `Proof`, refactored
  runtime record, and recursive prefix consumer all pass focused
  `--no-allow-unsolved-metas` checks.

- Audited the implementation graph.  The true inhabitant SCC is value-prefix
  catch-up together with source bullet, runtime `ν ★`, active widening `inst`,
  source paired cast, final paired cast, and final paired widening.  Ordinary
  source `ν` is acyclic once source bullet and source reveal exist.  Therefore
  the higher-order files are useful strict interface checks, but the canonical
  `Lemma` assembly for the SCC must be one structurally decreasing mutual
  proof (or use an explicit administrative-redex measure).

- This split is also an explicit defense against permissive checking.  Missing
  leaves are represented by whole theorem parameters and absent `Lemma`
  assemblies, so new skeleton and adapter modules can remain strict without
  `--allow-unsolved-metas`.  No aggregate module was checked for this batch.
