M6 foundation blocker: `columnSize-map`

Date: 2026-08-11

Blocked statement:

  columnSize-map : ∀ {Δ Δ′} {A B : Ty Δ}
      (χs : StoreChanges Δ Δ′) (κ : CastColumn A B)
    → columnSize (mapColumn χs κ) ≡ columnSize κ

The proof reduces to the one-change obligation:

  castSize (applyConsistency χ c) ≡ castSize c

The `keep` case is definitional.  The `bind` case unfolds through:

  applyConsistency (bind A) c
    = renameEnvᶜ Fin.suc (λ X → refl) c

For `inst`/`gen` consistency constructors, the exported `renameEnvᶜ`
wrapper normalizes to the private worker `rename∼`, which wraps the
recursive result with the private transports `subst-right-∼` and
`subst-left-∼` over `renameᵗ-shift`.  From outside `Consistency.agda`,
the size proof gets stuck at goals of this shape:

  suc
    (castSize
      (Consistency.subst-right-∼ equality
        (Consistency.rename∼ (extᵗ ρ)
          (Consistency.instᵐ-rename ρ eq)
          c)))
    ≡ suc (castSize c)

The relevant transport and recursive worker names are private, and this
task forbids editing `GTSFImp/Consistency.agda`.  The statement is still
expected to be mathematically true for store-change renaming; completing it
needs an exported size-preservation lemma for `renameEnvᶜ`/`renameᵐᶜ` or
for the private `subst-left-∼`/`subst-right-∼` transports.

RESOLVED (2026-08-11): `castSize` now lives in `Consistency.agda` with
`castSize-renameEnvᶜ`, proved by induction on the private `rename∼`
worker and transport-size helpers.  `columnSize-map` uses that exported
renaming equality for the `bind` store-change case.
