module proof.InterpreterQuotientValueEliminationProof where

-- File Charter:
--   * Eliminates observable outer wrappers from quotient value frames.
--   * Preserves the hidden quotient down plan as a down-representative frame.
--   * Recovers ground-tag and captured-environment narrowing without
--     evaluation or reduction.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; Σ-syntax)

import Coercions as C
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Runtime.InterpreterClosedValueFrame
open import Narrowing.InterpreterCoercionNarrowing
open import Narrowing.InterpreterQuotientValueNarrowing
import Runtime.InterpreterRuntimeFrame as Frame
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTagNarrowing using (tagOf-narrowing)
open import Narrowing.InterpreterTagNarrowingCore using (TagNarrowing)
open import Runtime.InterpreterTypeEnvironmentRealization using
  (environments-narrow)
open import Narrowing.InterpreterValueNarrowing using (ValueScoped)
import NarrowWiden as NW
import NuTermImprecision as NTI
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; quotient-cast-widening
  ; quotient-id-widening
  )
open import Types
open import proof.ForallPermutationProperties using
  (⊑ᵖ-ground-left)
open import proof.EndpointCanonicalMLBSimpleQuotient using
  (endpoint-representatives-quotient)

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

quotient-tag-types-narrow :
  ∀ {Φ Δᴸ Δᴿ} {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {G H D D′ A A′ : Ty} →
  (gG : Ground G) →
  Ground H →
  (qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ) →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (C._! G) (C._! H) D D′ A A′ →
  Φ ∣ Δᴸ ⊢ G ⊑ H ⊣ Δᴿ
quotient-tag-types-narrow gG gH qD
    (quotient-id-widening
      (C.cast-tag hG gG⊢ ok , NW.tag gG′)
      (C.cast-tag hH gH⊢ ok′ , NW.tag gH′)) =
  ⊑ᵖ-ground-left gG qD
quotient-tag-types-narrow gG gH qD
    (quotient-cast-widening
      mode seal
      (C.cast-tag hG gG⊢ ok , NW.tag gG′)
      mode′ seal′
      (C.cast-tag hH gH⊢ ok′ , NW.tag gH′)) =
  ⊑ᵖ-ground-left gG qD

quotient-related-tagged-payloads :
  ∀ {W W′ V V′ U U′ G H θ θ′}
    {R : WorldRelation W W′}
    {gG : Ground G} {gH : Ground H} →
  InterpreterQuotientValueFrame R V V′
    (tagged gG θ U) (tagged gH θ′ U′) →
  ValueScoped W U →
  ValueScoped W′ U′ →
  ValueNarrowing R V V′ →
  InterpreterGroundNarrowing gG gH ×
  TypeEnvironmentNarrowing R θ θ′ ×
  ValueNarrowing R U U′
quotient-related-tagged-payloads
    {G = G} {H = H} {gG = gG} {gH = gH}
    (quotient-value-frame
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {D = D} {D′ = D′} {A = A} {A′ = A′}
      source-down target-down D⊑E alignment widening pA runtime
      left-down right-down
      closed-tag-frame closed-tag-frame)
    U-ok U′-ok V~V′ =
  ground-narrowing
    (type-narrowing {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      (quotient-tag-types-narrow
        {G = G} {H = H} {D = D} {D′ = D′}
        {A = A} {A′ = A′}
        gG gH
        (endpoint-representatives-quotient D⊑E alignment)
        widening)) ,
  environments-narrow (Frame.type-environments-realized runtime) ,
  quotient-value-frame⊑
    (quotient-down-value-frame
      source-down target-down D⊑E alignment runtime
      left-down right-down)
    U-ok U′-ok V~V′
quotient-related-tagged-payloads
    (quotient-down-value-frame
      (source-cast , NW.cross ()) target-down
      D⊑E alignment runtime closed-tag-frame right-final)
    U-ok U′-ok V~V′

quotient-related-tag-observation :
  ∀ {W W′ V V′ U U′ G H θ θ′}
    {R : WorldRelation W W′}
    {gG : Ground G} {gH : Ground H} →
  InterpreterQuotientValueFrame R V V′
    (tagged gG θ U) (tagged gH θ′ U′) →
  ValueScoped W U →
  ValueScoped W′ U′ →
  ValueNarrowing R V V′ →
  Σ[ tag ∈ Tag ]
  Σ[ tag′ ∈ Tag ]
    tagOf θ gG ≡ just tag ×
    tagOf θ′ gH ≡ just tag′ ×
    TagNarrowing R tag tag′ ×
    ValueNarrowing R U U′
quotient-related-tag-observation
    {G = G} {H = H} {gG = gG} {gH = gH}
    (quotient-value-frame
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {D = D} {D′ = D′} {A = A} {A′ = A′}
      source-down target-down D⊑E alignment widening pA runtime
      left-down right-down
      closed-tag-frame closed-tag-frame)
    U-ok U′-ok V~V′
    with tagOf-narrowing gG gH
      (Frame.type-environments-realized runtime)
      (quotient-tag-types-narrow
        {G = G} {H = H} {D = D} {D′ = D′}
        {A = A} {A′ = A′}
        gG gH
        (endpoint-representatives-quotient D⊑E alignment)
        widening)
quotient-related-tag-observation
    {G = G} {H = H} {gG = gG} {gH = gH}
    (quotient-value-frame
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {D = D} {D′ = D′} {A = A} {A′ = A′}
      source-down target-down D⊑E alignment widening pA runtime
      left-down right-down
      closed-tag-frame closed-tag-frame)
    U-ok U′-ok V~V′
    | tag , tag′ , tag-eq , tag′-eq , tag~tag′ =
  tag , tag′ , tag-eq , tag′-eq , tag~tag′ ,
  quotient-value-frame⊑
    (quotient-down-value-frame
      source-down target-down D⊑E alignment runtime
      left-down right-down)
    U-ok U′-ok V~V′
quotient-related-tag-observation
    (quotient-down-value-frame
      (source-cast , NW.cross ()) target-down
      D⊑E alignment runtime closed-tag-frame right-final)
    U-ok U′-ok V~V′

quotient-related-function-payloads :
  ∀ {W W′ V V′ U U′ p p′ q q′ θ θ′}
    {R : WorldRelation W W′} →
  InterpreterQuotientValueFrame R V V′
    (function-proxy p q θ U)
    (function-proxy p′ q′ θ′ U′) →
  ValueScoped W U →
  ValueScoped W′ U′ →
  ValueNarrowing R V V′ →
  TypeEnvironmentNarrowing R θ θ′ ×
  ValueNarrowing R U U′
quotient-related-function-payloads
    (quotient-value-frame
      source-down target-down D⊑E alignment widening pA runtime
      left-down right-down
      closed-function-frame closed-function-frame)
    U-ok U′-ok V~V′ =
  environments-narrow (Frame.type-environments-realized runtime) ,
  quotient-value-frame⊑
    (quotient-down-value-frame
      source-down target-down D⊑E alignment runtime
      left-down right-down)
    U-ok U′-ok V~V′
quotient-related-function-payloads
    (quotient-down-value-frame
      source-down target-down D⊑E alignment runtime
      closed-function-frame closed-function-frame)
    U-ok U′-ok V~V′ =
  environments-narrow (Frame.type-environments-realized runtime) , V~V′

quotient-related-forall-payloads :
  ∀ {W W′ V V′ U U′ c c′ θ θ′}
    {R : WorldRelation W W′} →
  InterpreterQuotientValueFrame R V V′
    (forall-proxy c θ U) (forall-proxy c′ θ′ U′) →
  ValueScoped W U →
  ValueScoped W′ U′ →
  ValueNarrowing R V V′ →
  TypeEnvironmentNarrowing R θ θ′ ×
  ValueNarrowing R U U′
quotient-related-forall-payloads
    (quotient-value-frame
      source-down target-down D⊑E alignment widening pA runtime
      left-down right-down
      closed-forall-frame closed-forall-frame)
    U-ok U′-ok V~V′ =
  environments-narrow (Frame.type-environments-realized runtime) ,
  quotient-value-frame⊑
    (quotient-down-value-frame
      source-down target-down D⊑E alignment runtime
      left-down right-down)
    U-ok U′-ok V~V′
quotient-related-forall-payloads
    (quotient-down-value-frame
      source-down target-down D⊑E alignment runtime
      closed-forall-frame closed-forall-frame)
    U-ok U′-ok V~V′ =
  environments-narrow (Frame.type-environments-realized runtime) , V~V′

quotient-related-generalized-payloads :
  ∀ {W W′ V V′ U U′ A A′ c c′ θ θ′}
    {R : WorldRelation W W′} →
  InterpreterQuotientValueFrame R V V′
    (generalized A c θ U) (generalized A′ c′ θ′ U′) →
  ValueScoped W U →
  ValueScoped W′ U′ →
  ValueNarrowing R V V′ →
  TypeEnvironmentNarrowing R θ θ′ ×
  ValueNarrowing R U U′
quotient-related-generalized-payloads
    (quotient-value-frame
      source-down target-down D⊑E alignment widening pA runtime
      left-down right-down
      closed-generalized-frame closed-generalized-frame)
    U-ok U′-ok V~V′ =
  environments-narrow (Frame.type-environments-realized runtime) ,
  quotient-value-frame⊑
    (quotient-down-value-frame
      source-down target-down D⊑E alignment runtime
      left-down right-down)
    U-ok U′-ok V~V′
quotient-related-generalized-payloads
    (quotient-down-value-frame
      source-down target-down D⊑E alignment runtime
      closed-generalized-frame closed-generalized-frame)
    U-ok U′-ok V~V′ =
  environments-narrow (Frame.type-environments-realized runtime) , V~V′
