module proof.InterpreterRuntimeFramePrefix where

-- File Charter:
--   * Restricts persistent runtime frames along relational-store prefixes.
--   * Drops only administrative static-store entries; worlds, environments,
--     and executable values remain unchanged.
--   * Contains no interpreter call or reduction semantics.

open import Data.List using (_∷_)

import Runtime.InterpreterRuntimeFrame as Frame
open import Typing.InterpreterSemanticTypingCore using
  ( RuntimeContext
  ; StoreTyping
  ; runtime-context
  ; store-cons
  )
open import Runtime.InterpreterStoreCorrespondenceRealization using
  ( StoreCorrespondenceRealization
  ; realizes-store-correspondence
  ; store-correspondence-realization
  )
import NuTermImprecision as NTI
open import QuotientedTermImprecision using
  (StoreImpPrefix; prefix-reflⁱ; prefix-∷ⁱ)
open import proof.InterpreterCoercionNarrowingProof using
  (store-corresponds-prefix)

left-store-typing-prefix :
  ∀ {W Φ Δᴸ Δᴿ θ ρ₀ ρ} →
  StoreImpPrefix {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ →
  StoreTyping W θ (NTI.leftStoreⁱ ρ) →
  StoreTyping W θ (NTI.leftStoreⁱ ρ₀)
left-store-typing-prefix prefix-reflⁱ store =
  store
left-store-typing-prefix
    (prefix-∷ⁱ {entry = NTI.store-matched α A β B p} prefix)
    (store-cons lookup representation store) =
  left-store-typing-prefix prefix store
left-store-typing-prefix
    (prefix-∷ⁱ {entry = NTI.store-left α A hA} prefix)
    (store-cons lookup representation store) =
  left-store-typing-prefix prefix store
left-store-typing-prefix
    (prefix-∷ⁱ {entry = NTI.store-right β B hB} prefix)
    store =
  left-store-typing-prefix prefix store
left-store-typing-prefix
    (prefix-∷ⁱ {entry = NTI.store-link α A β B p} prefix)
    store =
  left-store-typing-prefix prefix store

right-store-typing-prefix :
  ∀ {W Φ Δᴸ Δᴿ θ ρ₀ ρ} →
  StoreImpPrefix {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ →
  StoreTyping W θ (NTI.rightStoreⁱ ρ) →
  StoreTyping W θ (NTI.rightStoreⁱ ρ₀)
right-store-typing-prefix prefix-reflⁱ store =
  store
right-store-typing-prefix
    (prefix-∷ⁱ {entry = NTI.store-matched α A β B p} prefix)
    (store-cons lookup representation store) =
  right-store-typing-prefix prefix store
right-store-typing-prefix
    (prefix-∷ⁱ {entry = NTI.store-left α A hA} prefix)
    store =
  right-store-typing-prefix prefix store
right-store-typing-prefix
    (prefix-∷ⁱ {entry = NTI.store-right β B hB} prefix)
    (store-cons lookup representation store) =
  right-store-typing-prefix prefix store
right-store-typing-prefix
    (prefix-∷ⁱ {entry = NTI.store-link α A β B p} prefix)
    store =
  right-store-typing-prefix prefix store

runtime-frame-prefix :
  ∀ {W W′ Φ Δᴸ Δᴿ θ θ′ ρ₀ ρ}
    {R : Frame.RelatedWorlds.WorldRelation W W′} →
  StoreImpPrefix ρ₀ ρ →
  Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ₀ θ θ′
runtime-frame-prefix prefix runtime =
  Frame.runtime-frame-narrowing
    (runtime-context left-length left-scope
      (left-store-typing-prefix prefix left-store))
    (runtime-context right-length right-scope
      (right-store-typing-prefix prefix right-store))
    (store-correspondence-realization
      (λ correspondence →
        realizes-store-correspondence
          (Frame.store-correspondences-realized runtime)
          (store-corresponds-prefix prefix correspondence)))
    (Frame.type-environments-realized runtime)
    (Frame.abstract-supply runtime)
  where
  open RuntimeContext
    (Frame.left-runtime-context runtime)
    renaming
      ( type-length to left-length
      ; type-scope to left-scope
      ; store-typing to left-store
      )

  open RuntimeContext
    (Frame.right-runtime-context runtime)
    renaming
      ( type-length to right-length
      ; type-scope to right-scope
      ; store-typing to right-store
      )
