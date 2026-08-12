M5 instantiation inversion blocker: source-strip needs a post-only surface

Date: 2026-08-12

Completed before this blocker:

  The direct A3 smart-comma route for the k=1 `Λ⊑²` recursive case is now
  checked in `Catchup/InstInversionProof.agda`; the old exchange route is not
  used.  The new checked support is:

    `Λ⊑²-smart-fresh-guard`
    `Λ⊑²-smart-fresh-untransport`
    `Λ⊑²-smart-fresh-top`
    `Λ⊑²-smart-fresh-catchup⁻`
    `mapCtxᴿ-smart-fresh-liftᴸ`
    `mapCtxᴿ-smart-fresh-target-ctx`
    `Λ⊑²-smart-fresh-at-rewrap`
    `Λ⊑²-smart-recursive-package-at`

  The recursive package-at combinator consumes the body package at the born
  smart world:

    `rightOnlyWorld (rightOnlyWorld (liftWorldLeft X⊑★ W) ★) (＇ zero)`

  and rewraps it at the outer two-allocation world:

    `rightOnlyWorld (rightOnlyWorld W ★) (＇ zero)`

  using `Λ⊑²-smart-comma`.  The inverse finite transport
  `[β, α, fresh, old…] -> [fresh, β, α, old…]` is valid because all three
  window marks are dynamic, so it constructs the top `∀` obligation directly.

Checked commands:

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
    GTSFImp/proof/DGG/Catchup/InstInversionProof.agda

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
    GTSFImp/All.agda

New resister:

  The next M-4 step is the source-strip layer for source-only wrappers:

    `cast⊑²`
    `reveal⊑²`
    `conceal⊑²`

  Using the existing `InstPostCatalogPackageAt` as the recursive surface under
  those wrappers is too strong.  In the `cast⊑²` case, the live constructor
  has the shape:

    `c : ν ⊢ A ∼ A′`
    `prem : W ∣ γ ⊢² M ⊑ Λ V′ ∶ p`
    `q∀ : A′ ⊑ᵂ⟨ W ⟩ `∀ B`

  and the Λ continuation receives the residual obligation:

    `q : A′ ⊑ᵂ⟨ W ⟩ B′`

  A recursive call to the current full catalog package on `prem` would require:

    `A ⊑ᵂ⟨ W ⟩ B′`

  That obligation is not supplied by the constructor, and it is not derivable
  from `c : A ∼ A′` and `q : A′ ⊑ᵂ⟨ W ⟩ B′` in general.  The same mismatch
  appears for `reveal⊑²` and `conceal⊑²`: their recursive premise lives at the
  pre-wrapper source type/world, while the continuation's residual obligation
  is for the post-wrapper source type/world.

Why this is not a smart-comma failure:

  The smart recursive Λ case itself checks.  The needed guard transports,
  target context equality, top obligation, residual `CatchupCast⁻` lift, and
  record-level package-at rewrap are all live.  The blocker is the shape of the
  source-strip recursion surface after that case: source wrappers need to
  recurse only far enough to obtain the post-prefix target relation, then
  rebuild the wrapper and construct residual provenance at the outer source
  type.

Required next surface:

  Add a post-prefix-only source-strip helper for the Λ target branch, or an
  equivalent package that returns:

    1. the fixed two-allocation target post term/type,
    2. the premise post relation at the pre-wrapper source type,
    3. the rebuilt outer post relation for the wrapper source type,
    4. the outer residual `CatchupCast⁻` provenance built from the wrapper's
       own post obligation and the continuation's `q`.

  This is narrower than the old exchange saga and does not require changing
  `Λ⊑²-smart-comma`.  It is a statement-surface issue for the source-strip
  layer of `InstInversionPackage.Λ-package`.

No live relation was changed, and no postulate, hole, or catch-all was added.
