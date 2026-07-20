# Nu-imprecision DGG progress

This ledger tracks the checked path from `QuotientedTermImprecision` to the
dynamic gradual guarantee. A checked item has been accepted by Agda without
unsolved metas; a statement-only item has its intended interface written down
but is not counted as proved.

## Current objective

Prove simulation coverage for reductions involving `ν`, `Λ`, `gen`, `inst`,
and runtime type application `•`, beginning with the definition-sensitive
cases.

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
| Source-only canonical-`∀` catchup | partial | Now a specialization of arbitrary-type value catchup; ten explicit holes remain, all in `NuImprecisionCatchupScratch`: two quotient-`inst` residuals, three source-allocation leaves, and five source cast/conversion leaves |
| `β-gen•` | partial | Matched reconstruction and one-sided administrative clause checked; source-allocation naturality remains |
| `β-inst` followed by `ν ★` allocation | checked locally | Matched, left-only, and right-only two-step lemmas |
| Polymorphic value-shape inversion | checked locally | `Λ`, `∀` cast, or `gen`; each forces one administrative step |
| Quotiented `∀`-index inversion | checked locally | Representatives remain `∀`; ordinary witness is paired `∀` or source-only `ν` |
| Swapped two-allocation context/store | checked locally | Crossed name assumptions and independent-order store links |
| Swapped two-allocation relation boundary | checked locally | `allocation-crossedᵀ`; projections equal the two-`bind` traces |
| Reduction under `ν` and `ν ★` | checked | Matched, source-only, and target-only outer frame lemmas |
| `blame-ν` | checked outcome | Exceptional outcomes carry a source catchup to blame; source frames lift it with `ν-blame-tail` |
| Administrative simulation-up-to | partial | The result, transport, coherence, source-`keep` composition, and all six `ν`-frame outcome maps are checked; the unfinished integration is confined to the dispatcher scratch |
| One-step Nu-imprecision simulation | partial | The dispatcher skeleton covers blame and the matched/source-only/target-only `ν` and `ν ★` families; ten explicit helper holes remain, and the non-`ν` constructor/reduction patterns are not yet enumerated |
| Terminal target-trace alignment | checked | Determinism makes every administrative `targetTail` a prefix of an observed trace to a value or blame |
| Closed `GradualDGG` | checked reduction | `closed-nu-dgg⇒gradual-dgg` reduces it to `ClosedNuDGG`, which now follows from exactly three terminal simulation clauses |

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
