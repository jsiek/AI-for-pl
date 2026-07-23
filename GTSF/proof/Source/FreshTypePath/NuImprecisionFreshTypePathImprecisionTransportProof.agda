module proof.Source.FreshTypePath.NuImprecisionFreshTypePathImprecisionTransportProof where

-- File Charter:
--   * Transports proof-relevant variable paths through well-formed type
--     imprecision while preserving their arrow route.
--   * Excludes a source-only variable from a target path on the same arrow
--     route, including a path into the body of a universal target.
--   * Contains no conversion, store, term-imprecision, simulation, postulate,
--     hole, permissive option, or handler import.

open import Agda.Builtin.Equality using (refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import ImprecisionWf using
  ( _∣_⊢_⊑_⊣_; id★; idˣ; idι; _↦_; ∀ⁱ_
  ; tag_; tag_⇛_; tagˣ; ν
  )
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleFactor using
  ( StarTrack; VarTrack; star-track-∀; star-track-ν
  ; var-track-∀; var-track-ν
  )
open StarTrack using (track-no-var)
open VarTrack using (track-star; track-var)
open import proof.Source.FreshTypePath.NuImprecisionFreshTypePath using
  ( TypePath; VarAtPath; at-body; at-codomain; at-domain; at-here
  ; body; codomain; domain; here
  )
open import proof.Source.FreshTypePath.NuImprecisionFreshTypePathArrowRouteDef using
  ( SameArrowRoute; same-codomain; same-domain; same-here
  ; skip-left-body; skip-right-body; strip-left-body; strip-right-body
  )
open import proof.Source.FreshTypePath.NuImprecisionFreshTypePathImprecisionTransportDef using
  ( FreshTypePathImprecisionTransport
  ; MatchedSourcePathForwardᵀ
  ; SourceOnlySameRouteImpossibleᵀ
  ; SourceOnlyToUniversalBodyImpossibleᵀ
  )


matched-source-path-forward-proofᵀ : MatchedSourcePathForwardᵀ
matched-source-path-forward-proofᵀ track id★ ()
matched-source-path-forward-proofᵀ track (idˣ x∈ X<Δ Y<Δ) at-here
    with track-var track x∈
matched-source-path-forward-proofᵀ track (idˣ x∈ X<Δ Y<Δ) at-here
    | refl =
  here , same-here , at-here
matched-source-path-forward-proofᵀ track idι ()
matched-source-path-forward-proofᵀ track (r ↦ s) (at-domain x-at)
    with matched-source-path-forward-proofᵀ track r x-at
matched-source-path-forward-proofᵀ track (r ↦ s) (at-domain x-at)
    | q , route , y-at =
  domain q , same-domain route , at-domain y-at
matched-source-path-forward-proofᵀ track (r ↦ s) (at-codomain x-at)
    with matched-source-path-forward-proofᵀ track s x-at
matched-source-path-forward-proofᵀ track (r ↦ s) (at-codomain x-at)
    | q , route , y-at =
  codomain q , same-codomain route , at-codomain y-at
matched-source-path-forward-proofᵀ track (∀ⁱ r) (at-body x-at)
    with matched-source-path-forward-proofᵀ (var-track-∀ track) r x-at
matched-source-path-forward-proofᵀ track (∀ⁱ r) (at-body x-at)
    | q , route , y-at =
  body q , skip-left-body (skip-right-body route) , at-body y-at
matched-source-path-forward-proofᵀ track (tag ι) ()
matched-source-path-forward-proofᵀ track (tag r ⇛ s) (at-domain x-at)
    with matched-source-path-forward-proofᵀ track r x-at
matched-source-path-forward-proofᵀ track (tag r ⇛ s) (at-domain x-at)
    | q , route , ()
matched-source-path-forward-proofᵀ track (tag r ⇛ s) (at-codomain x-at)
    with matched-source-path-forward-proofᵀ track s x-at
matched-source-path-forward-proofᵀ track (tag r ⇛ s) (at-codomain x-at)
    | q , route , ()
matched-source-path-forward-proofᵀ track (tagˣ x∈ X<Δ) at-here =
  ⊥-elim (track-star track x∈)
matched-source-path-forward-proofᵀ track (ν _ occ r) (at-body x-at)
    with matched-source-path-forward-proofᵀ (var-track-ν track) r x-at
matched-source-path-forward-proofᵀ track (ν _ occ r) (at-body x-at)
    | q , route , y-at =
  q , skip-left-body route , y-at


source-only-same-route-impossible-proofᵀ :
  SourceOnlySameRouteImpossibleᵀ
source-only-same-route-impossible-proofᵀ track id★ () y-at route
source-only-same-route-impossible-proofᵀ track (idˣ x∈ X<Δ Y<Δ)
    at-here at-here same-here =
  track-no-var track x∈
source-only-same-route-impossible-proofᵀ track idι () y-at route
source-only-same-route-impossible-proofᵀ track (r ↦ s)
    (at-domain x-at) (at-domain y-at) (same-domain route) =
  source-only-same-route-impossible-proofᵀ track r x-at y-at route
source-only-same-route-impossible-proofᵀ track (r ↦ s)
    (at-codomain x-at) (at-codomain y-at) (same-codomain route) =
  source-only-same-route-impossible-proofᵀ track s x-at y-at route
source-only-same-route-impossible-proofᵀ track (∀ⁱ r)
    (at-body x-at) (at-body y-at) route =
  source-only-same-route-impossible-proofᵀ
    (star-track-∀ track) r x-at y-at
    (strip-right-body (strip-left-body route))
source-only-same-route-impossible-proofᵀ track (tag ι) () y-at route
source-only-same-route-impossible-proofᵀ
    track (tag r ⇛ s) x-at () route
source-only-same-route-impossible-proofᵀ
    track (tagˣ x∈ X<Δ) at-here () route
source-only-same-route-impossible-proofᵀ track (ν _ occ r)
    (at-body x-at) y-at route =
  source-only-same-route-impossible-proofᵀ
    (star-track-ν track) r x-at y-at
    (strip-left-body route)


source-only-to-universal-body-impossible-proofᵀ :
  SourceOnlyToUniversalBodyImpossibleᵀ
source-only-to-universal-body-impossible-proofᵀ track (∀ⁱ r)
    (at-body x-at) y-at route =
  source-only-same-route-impossible-proofᵀ
    (star-track-∀ track) r x-at y-at
    (strip-left-body route)
source-only-to-universal-body-impossible-proofᵀ track (ν _ occ r)
    (at-body x-at) y-at route =
  source-only-to-universal-body-impossible-proofᵀ
    (star-track-ν track) r x-at y-at
    (strip-left-body route)


fresh-type-path-imprecision-transport-proof :
  FreshTypePathImprecisionTransport
fresh-type-path-imprecision-transport-proof = record
  { matched-source-path-forward =
      matched-source-path-forward-proofᵀ
  ; source-only-same-route-impossible =
      source-only-same-route-impossible-proofᵀ
  ; source-only-to-universal-body-impossible =
      source-only-to-universal-body-impossible-proofᵀ
  }
