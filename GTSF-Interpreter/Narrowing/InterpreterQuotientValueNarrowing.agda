module Narrowing.InterpreterQuotientValueNarrowing where

-- File Charter:
--   * Records one compiler-produced quotient down/up frame on runtime values.
--   * Also records its down representatives after an active observer removes
--     the final inert wrapper.
--   * Keeps all four inert coercions and their exact aligned static evidence.
--   * Indexes the frame by its world relation and type-environment
--     realization, with weakening and sealed-head invariants.
--   * Does not retain a source AST: runtime arguments can acquire the same
--     quotient frame through component casts.
--   * The base values are related separately by the operational value
--     relation, so the frame applies equally to closed syntax and values
--     returned by an arbitrary subcomputation.
--   * Does not add a runtime value form or invoke evaluation or reduction.

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
import Coercions as C
open import Coercions using
  ( Coercion
  ; Inert
  ; ModeEnv
  ; genᵈ
  ; id-onlyᵈ
  ; tag-or-idᵈ
  )
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Runtime.InterpreterClosedValueFrame
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
import Runtime.InterpreterRuntimeFrame as Frame
open import Narrowing.InterpreterWorldNarrowing
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
import NarrowWiden as NW
import NuTermImprecision as NTI
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; quotient-id-widening
  ; quotient-cast-widening
  )
open import Types
open import proof.EndpointCanonicalMLBSimpleQuotient using
  (EndpointRepresentativeAlignment)

module QuotientWorlds =
  WorldNarrowing InterpreterTypeNarrowing

open QuotientWorlds

data QuotientDownMode : ModeEnv → Set where
  id-down-mode :
    QuotientDownMode id-onlyᵈ

  generalized-down-mode :
    QuotientDownMode (genᵈ tag-or-idᵈ)

instance
  id-down-mode-instance :
    QuotientDownMode id-onlyᵈ
  id-down-mode-instance =
    id-down-mode

  generalized-down-mode-instance :
    QuotientDownMode (genᵈ tag-or-idᵈ)
  generalized-down-mode-instance =
    generalized-down-mode

generalized-down-excludes-seal :
  ∀ X →
  C.sealModeAllowed (genᵈ tag-or-idᵈ X) ≡ true →
  ⊥
generalized-down-excludes-seal zero ()
generalized-down-excludes-seal (suc X) ()

data InterpreterQuotientValueFrame
    {W W′ : World}
    (R : WorldRelation W W′) :
    Value → Value → Value → Value → Set₁ where
  quotient-value-frame :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {C C′ D E D′ X Y A A′ : Ty}
      {d d′ u u′ : Coercion}
      {μ μ′ : ModeEnv}
      {θ θ′ : TypeEnvironment}
      {V V′ L L′ U U′ : Value}
      {id : Inert d} {id′ : Inert d′}
      {iu : Inert u} {iu′ : Inert u′} →
    {{down-mode : QuotientDownMode μ}} →
    μ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ
      ⊢ d ∶ C ⊒ D →
    μ′ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ
      ⊢ d′ ∶ C′ ⊒ D′ →
    (D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ) →
    (alignment :
      EndpointRepresentativeAlignment Δᴿ X Y E D′) →
    QuotientWideningPair
      Δᴸ Δᴿ ρ u u′ D D′ A A′ →
    (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    ClosedValueFrame θ V id L →
    ClosedValueFrame θ′ V′ id′ L′ →
    ClosedValueFrame θ L iu U →
    ClosedValueFrame θ′ L′ iu′ U′ →
    InterpreterQuotientValueFrame R V V′ U U′

  quotient-down-value-frame :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {C C′ D E D′ X Y : Ty}
      {d d′ : Coercion}
      {μ μ′ : ModeEnv}
      {θ θ′ : TypeEnvironment}
      {V V′ U U′ : Value}
      {id : Inert d} {id′ : Inert d′} →
    {{down-mode : QuotientDownMode μ}} →
    μ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ
      ⊢ d ∶ C ⊒ D →
    μ′ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ
      ⊢ d′ ∶ C′ ⊒ D′ →
    (D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ) →
    (alignment :
      EndpointRepresentativeAlignment Δᴿ X Y E D′) →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    ClosedValueFrame θ V id U →
    ClosedValueFrame θ′ V′ id′ U′ →
    InterpreterQuotientValueFrame R V V′ U U′

quotient-value-frame-weaken :
  ∀ {W W′ U U′ V V′ L L′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  WorldExtension R S →
  InterpreterQuotientValueFrame R V V′ L L′ →
  InterpreterQuotientValueFrame S V V′ L L′
quotient-value-frame-weaken R≤S
    (quotient-value-frame
      source-down target-down D⊑E alignment widening pA runtime
      left-down right-down left-up right-up) =
  quotient-value-frame
    source-down target-down D⊑E alignment widening pA
    (Frame.runtime-frame-weaken R≤S runtime)
    left-down right-down left-up right-up
quotient-value-frame-weaken R≤S
    (quotient-down-value-frame
      source-down target-down D⊑E alignment runtime
      left-final right-final) =
  quotient-down-value-frame
    source-down target-down D⊑E alignment
    (Frame.runtime-frame-weaken R≤S runtime)
    left-final right-final

quotient-value-frame-seal-link :
  ∀ {W W′ V V′ α α′ U U′}
    {R : WorldRelation W W′} →
  InterpreterQuotientValueFrame R V V′
    (sealed α U) (sealed α′ U′) →
  SealLink R α α′
quotient-value-frame-seal-link
    (quotient-value-frame
      source-down target-down D⊑E alignment
      (quotient-id-widening (_ , NW.cross ()) right-up)
      pA runtime left-down right-down
      (closed-seal-frame lookup) right-up-frame)

quotient-value-frame-seal-link
    (quotient-down-value-frame
      {{id-down-mode}}
      (C.cast-seal hA α∈Σ () , NW.sealⁿ A α)
      target-down D⊑E alignment runtime
      (closed-seal-frame lookup) right-final)
quotient-value-frame-seal-link
    (quotient-down-value-frame
      {{generalized-down-mode}}
      (C.cast-seal {α = X} hA α∈Σ allowed , NW.sealⁿ A X)
      target-down D⊑E alignment runtime
      (closed-seal-frame lookup) right-final) =
  ⊥-elim (generalized-down-excludes-seal X allowed)
quotient-value-frame-seal-link
    (quotient-value-frame
      source-down target-down D⊑E alignment
      (quotient-cast-widening
        mode seal (_ , NW.cross ()) mode′ seal′ right-up)
      pA runtime left-down right-down
      (closed-seal-frame lookup) right-up-frame)

quotient-value-frame-source-not-sealed :
  ∀ {W W′ V V′ α U U′}
    {R : WorldRelation W W′} →
  InterpreterQuotientValueFrame R V V′
    (sealed α U) U′ →
  ⊥
quotient-value-frame-source-not-sealed
    (quotient-value-frame
      source-down target-down D⊑E alignment
      (quotient-id-widening (_ , NW.cross ()) right-up)
      pA runtime left-down right-down
      (closed-seal-frame lookup) right-up-frame)
quotient-value-frame-source-not-sealed
    (quotient-down-value-frame
      {{id-down-mode}}
      (C.cast-seal hA α∈Σ () , NW.sealⁿ A X)
      target-down D⊑E alignment runtime
      (closed-seal-frame lookup) right-final)
quotient-value-frame-source-not-sealed
    (quotient-down-value-frame
      {{generalized-down-mode}}
      (C.cast-seal {α = X} hA α∈Σ allowed , NW.sealⁿ A X)
      target-down D⊑E alignment runtime
      (closed-seal-frame lookup) right-final) =
  generalized-down-excludes-seal X allowed
quotient-value-frame-source-not-sealed
    (quotient-value-frame
      source-down target-down D⊑E alignment
      (quotient-cast-widening
        mode seal (_ , NW.cross ()) mode′ seal′ right-up)
      pA runtime left-down right-down
      (closed-seal-frame lookup) right-up-frame)
