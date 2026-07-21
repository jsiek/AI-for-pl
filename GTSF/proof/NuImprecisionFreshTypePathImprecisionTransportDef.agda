module proof.NuImprecisionFreshTypePathImprecisionTransportDef where

-- File Charter:
--   * Defines proof-relevant variable-path transport through well-formed type
--     imprecision modulo universal-body edges.
--   * Defines the two source-only impossibility claims used by crossed-binder
--     fresh-path arguments.
--   * Contains no implementation, conversion, store, term-imprecision,
--     simulation, postulate, hole, permissive option, or handler import.

open import Data.Empty using (⊥)
open import Data.Product using (_×_; ∃-syntax)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import proof.EndpointCanonicalMLBSimpleFactor using
  ( StarTrack
  ; VarTrack
  )
open import proof.NuImprecisionFreshTypePath using
  ( TypePath
  ; VarAtPath
  )
open import proof.NuImprecisionFreshTypePathArrowRouteDef using
  (SameArrowRoute)
open import Types using (Ty; TyCtx; TyVar; `∀)


MatchedSourcePathForwardᵀ : Set
MatchedSourcePathForwardᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {A B : Ty} {X Y : TyVar} {p : TypePath} →
  VarTrack Φ X Y →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  VarAtPath X p A →
  ∃[ q ] SameArrowRoute p q × VarAtPath Y q B


SourceOnlySameRouteImpossibleᵀ : Set
SourceOnlySameRouteImpossibleᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {A B : Ty} {X Y : TyVar} {p q : TypePath} →
  StarTrack Φ X →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  VarAtPath X p A →
  VarAtPath Y q B →
  SameArrowRoute p q →
  ⊥


SourceOnlyToUniversalBodyImpossibleᵀ : Set
SourceOnlyToUniversalBodyImpossibleᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {A B : Ty} {X Y : TyVar} {p q : TypePath} →
  StarTrack Φ X →
  Φ ∣ Δᴸ ⊢ A ⊑ `∀ B ⊣ Δᴿ →
  VarAtPath X p A →
  VarAtPath Y q B →
  SameArrowRoute p q →
  ⊥


record FreshTypePathImprecisionTransport : Set where
  field
    matched-source-path-forward : MatchedSourcePathForwardᵀ
    source-only-same-route-impossible :
      SourceOnlySameRouteImpossibleᵀ
    source-only-to-universal-body-impossible :
      SourceOnlyToUniversalBodyImpossibleᵀ

open FreshTypePathImprecisionTransport public
