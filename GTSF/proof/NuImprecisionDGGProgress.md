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
| Source-only canonical-`∀` catchup | checked | Terminal, `α/Λ`, reveal, conceal, generic narrowing, and generic widening clauses |
| `β-gen•` | partial | Matched reconstruction and one-sided administrative clause checked; source-allocation naturality remains |
| `β-inst` followed by `ν ★` allocation | checked locally | Matched, left-only, and right-only two-step lemmas |
| Polymorphic value-shape inversion | checked locally | `Λ`, `∀` cast, or `gen`; each forces one administrative step |
| Quotiented `∀`-index inversion | checked locally | Representatives remain `∀`; ordinary witness is paired `∀` or source-only `ν` |
| Swapped two-allocation context/store | checked locally | Crossed name assumptions and independent-order store links |
| Swapped two-allocation relation boundary | checked locally | `allocation-crossedᵀ`; projections equal the two-`bind` traces |
| Reduction under `ν` and `ν ★` | checked | Matched, source-only, and target-only outer frame lemmas |
| `blame-ν` | checked outcome | Exceptional outcomes carry a source catchup to blame; source frames lift it with `ν-blame-tail` |
| Administrative simulation-up-to | partial | Composition and all six `ν`-frame outcome maps are checked |
| One-step Nu-imprecision simulation | partial | Direct quotient and generic `β-∀•` clauses are checked |
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
9. Prove one-step simulation and lift it to `GradualDGG`.

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
    \mathsf{inst}(\mathsf{ext}(\mathsf{tag\mbox{-}or\mbox{-}id)) )
    \quad\text{and}\quad
    \mathsf{ext}(\mathsf{inst}(\mathsf{tag\mbox{-}or\mbox{-}id)) ).
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
  `WeakOneStepResult` or evidence that the more-precise source reduces to
  `blame`. A target reduction to blame is not by itself a simulation outcome.
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
`WeakOneStepResult` and can be injected with `outcome-related`. A target-blame
leaf must first establish a source reduction to blame and then use
`outcome-source-blame`. When the input type relation is headed by `∀ⁱ`,
recursion returns `WeakOneStepAllOutcome`, retaining the canonical body
derivation. The later audit of one-sided `β-gen•` shapes remains separate.

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
