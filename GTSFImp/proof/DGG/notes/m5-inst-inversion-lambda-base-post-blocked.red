M5 instantiation inversion blocker: Λ⊑Λ² post-catalog body transport

Date: 2026-08-11

Blocked target:

  the `Λ⊑Λ²` base case of the derivation-recursive
  `InstInversionPackage.Λ-package` implementation.

The extension-indexed package obstruction is resolved: the live
`InstPostCatalogPackageAt` is now indexed by the caller-supplied
`χs₂`, `W₂`, and `ext₂`, and `inst-post-at-finish` composes its
fixed prefix-to-residual trace with the smaller extra-cast worker.

The next failing shape is the two-sided core relation:

  rel =
    CTI2.Λ⊑Λ² liftγ vV vV′ bodyRel p

with target branch `M′ = Λ V′`.  The available body premise is:

  bodyRel :
    liftWorldBoth X⊑X W ∣ γᴮ
      ⊢² V ⊑ V′ ∶ body-p

After `β-inst` and the catalogued `β-Λ` step, the indexed package
must produce the post-catalog relation at the two-allocation right
extension:

  W₁ = rightOnlyWorld W ★
  W₂ = rightOnlyWorld W₁ (＇ zero)
  ext₂ : WorldExtendᴿ (bind ★ ∷ bind (＇ zero) ∷ []) W W₂

schematically:

  liftWorldLeft X⊑★ W₂ ∣ γ₂ᴸ
    ⊢² V ⊑ postΛ V′ ∶ body-p₂

where `postΛ V′` is the target body exposed by the `β-Λ` step and then
wrapped by the generated target reveal from `β-inst` transported through
the second `bind`:

  (⇑ᵗᵐ V′ ↑ 〖 zero , ⇑ᵗ (＇ zero)
       ↑ applyBody (bind ★) B 〗)
    ↑ rename↑ (λ X → bind (＇ zero) ▷ᵛ X)
        (〖 zero , ★ ↑ B 〗)

The already-proved `right-bind-under-left-lift` and
`Λ⊑²AtRewrapᵀ` cover the one-sided recursive case once a body relation is
already in `liftWorldLeft X⊑★ W₂`.  They do not convert a
`liftWorldBoth X⊑X W` body premise into the left-lifted post-catalog
world, and they do not wrap the target with the generated reveal sequence.

Smallest unblocking statement:

  add a checked post-catalog body transport lemma for the `Λ⊑Λ²` core,
  indexed by the same `χs₂`, `W₂`, and `ext₂`, which consumes the
  `liftWorldBoth X⊑X W` body premise and returns the required
  `liftWorldLeft X⊑★ W₂` relation against `postΛ V′`, including the
  target typing of `postΛ V′` and the aligned `body-p₂`.

Equivalently, the Λ base package can carry this as a premise-world
predicate, but it must be stated at the caller's post-catalog world; an
existential package would recreate the CPS blocker.

REFINED (2026-08-11): the caller-indexed transport surface now checks as
`Λ⊑Λ²PostBodyTransportᵀ`, and the scratch validates that it rewraps the
base case through `Λ⊑²`.  The remaining implementation blocker is the
derivation-level target-extension leg needed before the reveal rebuild;
see `m5-inst-inversion-lambda-target-extension-blocked.red`.

RESOLVED (2026-08-12):

  The live surface is specialized to the concrete two-bind post tower, and
  `Λ⊑Λ²-post-body-transport` now proves the body relation, target typing,
  post value, body obligation, and top `∀` obligation needed by the
  `Λ⊑Λ²` base package.  The checked composition order is:

    target-insert `bind ★`
    → decay `X⊑X` to `X⊑★` under `liftWorldBoth`
    → center extension
    → fresh lift-to-bind move at the `★` mark
    → generated reveal rebuilds by `RebaseAtᴿ`
    → target typing by `target-typing²`

  `Λ⊑Λ²-base-package-at` now checks against the specialized tower.
