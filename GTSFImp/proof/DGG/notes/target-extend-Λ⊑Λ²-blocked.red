Target extension blocker: `Λ⊑Λ²` needs static right insertion under
the target type binder

Date: 2026-08-11

Blocked constructor:

  `Λ⊑Λ²` in `proof/DGG/CastTermImprecision2.agda`.

The statement-first single root right-bind surface checks:

  from

    W ∣ γ ⊢² M ⊑ M′ ∶ p

  to

    rightOnlyWorld W B′ ∣ mapCtxᴿ ext γ
      ⊢² M ⊑ renameᵗᵐ wk↪ᵗ M′ ∶ transport⊑ᵂ ext p

For the `Λ⊑Λ²` constructor, the recursive premise has the target term
under a target type binder:

  bodyRel :
    liftWorldBoth X⊑X W ∣ γᴮ ⊢² V ⊑ V′ ∶ body-p

Rebuilding `Λ⊑Λ²` after the outer right bind requires the body premise
in:

  liftWorldBoth X⊑X (rightOnlyWorld W B′) ∣ γᴮ⁺
    ⊢² V ⊑ renameᵗᵐ (keep wk↪ᵗ) V′ ∶ body-p⁺

Diagram:

  Λ V                    ⊑                  Λ V′
   | β/context                               | target right bind
   v                                         v
  Λ V                    ⊑
  Λ (renameᵗᵐ (keep wk↪ᵗ) V′)

and for the body:

  V                      ⊑                  V′
   | 0 steps                                | static target weakening
   v                                       v
  V                      ⊑                  renameᵗᵐ (keep wk↪ᵗ) V′

The available root extension theorem shape would recursively target

  rightOnlyWorld (liftWorldBoth X⊑X W) (⇑ᵗ B′)

with target term `renameᵗᵐ wk↪ᵗ V′`.  That world is not the one
required by the constructor:

  rightOnlyWorld (liftWorldBoth X⊑X W) (⇑ᵗ B′)
    has target store `store-bind (store-lift Σ) (⇑ᵗ B′)`
    and puts the fresh right variable before the target binder.

  liftWorldBoth X⊑X (rightOnlyWorld W B′)
    has target store `store-lift (store-bind Σ B′)`
    and keeps the target binder before the fresh right variable.

Equivalently, the root recursive call gives `renameᵗᵐ wk↪ᵗ V′`, while
the constructor needs `renameᵗᵐ (keep wk↪ᵗ) V′`.

This is not expressible by `ExtraCastRight2.WorldExtendᴿ`: no
`StoreChanges` sequence turns `store-lift Σ` into
`store-lift (store-bind Σ B′)`, because `StoreChanges` only append root
runtime changes, while this is a static insertion underneath a type
binder.

The fix is not to weaken the public theorem, but to add an internal
static target-extension family stable under `liftWorldBoth` (and the
already-needed `liftWorldLeft`) and use the root right-bind theorem as
its base case.  The helper must transport the same evidence families
already started in `proof/DGG/TargetExtend.agda`: indexed conversion
typing, `RebaseAt`/`RebaseAtᴸ`/`RebaseAtᴿ`/`TagRebaseAtᴸ`, and the
partner predicates.

RESOLVED, 2026-08-11.

The reusable OPE theorem is `⊢²-target-insert : TargetExtendOPEᵀ`.
The depth-0 surface is `⊢²-target-extend-bind : TargetExtendBindᵀ`,
and the under-binder target insertion instance is
`keepRightBindTargetInsert`, which transports target terms with
`renameᵗᵐ (keep wk↪ᵗ)`.
