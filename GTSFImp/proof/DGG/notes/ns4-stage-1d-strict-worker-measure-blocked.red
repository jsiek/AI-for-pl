NS-4 stage 1d strict worker blocker: same-mass strict target heads

Date: 2026-08-14

Surface:

  Strict clauses for `StructuralNameInstantiationProof` after the target
  peels landed.

What landed before this blocker:

  The generic spine inversion family and the five strict target peels all
  type-check and are wired into `All.agda`.

  In particular, the bind-head peels for `allv-Λ`, `allv-gen`,
  `allv-reveal`, and `allv-conceal` expose:

    `Δ₁`, `π`, `W₁`,
    `ins : TargetInsert wk↪ᵗ π W W₁`,
    `follows : targetStoreʷ W₁ ≡
       applyStores (bind (＇ X) ∷ []) (targetStoreʷ W)`,
    and the caller-tail child `StructuralTargetInstantiationPackage W₁ ...`.

  This arbitrary-insert shape is enough for package inversion and for the
  generic `structural-descent-bind-step`; it intentionally does not assume
  the canonical `rightOnlyWorld W (＇ X)`.

Resisted sub-surface:

  `StructuralNameInstantiationAccᵀ` is accessible only on
  `pendingCastMass vV (name-type-app-frame B X refl refl ▻ⁱ spine)`.
  Restarting the worker after a strict peel is allowed only when there is a
  proved strict mass decrease.

  The landed mass lemmas give strict decreases for the cast-bearing target
  heads:

    `allv-∀` via `all-primary-decreases`
    `allv-gen` via `gen-primary-decreases`

  But the first strict steps for `allv-Λ`, `allv-reveal`, and `allv-conceal`
  preserve this primary mass:

    `valueCastMass (Λ vV) = valueCastMass vV`
    `valueCastMass (vV ↑ all) = valueCastMass vV`
    `valueCastMass (vV ↓ all) = valueCastMass vV`

  and the new child spines add only name/type transport and conversion frames,
  whose `spineCastMass` contribution is zero.  Therefore these clauses cannot
  legally restart the current accessibility argument.

  The `allv-∀` clause has an additional child-view obligation: after peeling
  `V ⟨ ∀ᶜ d ⟩`, the recursive call needs `AllValueView V`.  This is derivable
  from `Progress.canonical-∀` and `CTI2T.target-typing²`, but that still only
  solves the view, not the same-mass heads above.

Likely next proof surface:

  Add a secondary well-founded component for the same-mass strict heads, or
  add non-recursive continuation lemmas that consume the `Λ`/conversion peel
  children without calling the worker at the same `pendingCastMass`.

  The conversion cases are the intended place to use
  `StructuralFrameOutcome`: once the strict β-reveal/β-conceal peel exposes
  the conversion frames, a one-keep-step conversion outcome can discharge the
  administrative frame before any recursive call that requires a mass decrease.

Status:

  No worker clauses were added in this chunk.  The checked peels remain
  available as separate lemmas; the worker is not assembled.


RESOLVED postscript, 2026-08-14:

  The same-mass strict-head blocker was closed by the secondary
  `pendingRank` measure in
  `GTSFImp/proof/DGG/Catchup/StructuralValueInstantiationRankDef.agda` and
  the checked descent lemmas in
  `GTSFImp/proof/DGG/Catchup/StructuralValueInstantiationRankProof.agda`:

  - `lambda-rank-decreases`
  - `reveal-rank-decreases`
  - `conceal-rank-decreases`

  Primary cast-mass remains the outer measure; `pendingRank` handles the
  fixed-mass `Λ`, reveal, and conceal strict heads.
