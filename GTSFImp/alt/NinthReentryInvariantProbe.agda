module alt.NinthReentryInvariantProbe where

-- File Charter:
--   * Records U22's checked ninth obstruction to unconditional re-entry.
--   * The live-set index follows an end marker's recorded anchor, while
--     `∋typ.skip-end` can preserve a different surviving slot.  Consequently
--     a constructible telescope can derive `Ψ ∋typ X ≔ α` while α's bit is
--     false.  A representation ref to α resolves before re-entry but reads
--     through X after re-entry, so the public lookup payload changes.

open import Data.Bool using (false; true)
open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.Nat using () renaming (zero to zeroⁿ; suc to sucⁿ)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Types
open import alt.ThetaTyping
open import alt.ThetaTermSubst

-- The original crossing is α = 1.  The lexical slot at zero is then ended
-- with α recorded on the marker, although the surviving crossing is slot
-- zero.  The index follows the marker and therefore marks α dead.
ninth-Ψ : TyEnv (sucⁿ (sucⁿ zeroⁿ)) (sucⁿ zeroⁿ)
    (false Vec.∷ false Vec.∷ Vec.[])
ninth-Ψ =
  ((((∅ ,:= ‵ `ℕ)
    ,begin[ zero ≔ zero ]⟨ refl ⟩) ,typ)
    ,:= ＇ zero)
    ,end[ zero ≔ suc zero ]

ninth-slot : ninth-Ψ ∋typ zero ≔ suc zero
ninth-slot =
  skip-end (skip-nu-binding (skip-typ found-begin))

ninth-slot-bit-dead :
    Vec.lookup (false Vec.∷ false Vec.∷ Vec.[]) (suc zero)
      ≡ false
ninth-slot-bit-dead = refl

-- The newer anchor's representation names the lexical slot that the marker
-- ends.  Its raw payload therefore becomes `ref α`.
ninth-new-raw : ninth-Ψ ∋rep⁺ zero ≔ ref (suc zero)
ninth-new-raw = skip-end Z

ninth-old-rep : ninth-Ψ ∋rep suc zero ≔ ‵ `ℕ
ninth-old-rep =
  ∋rep-of (skip-end (S (skip-typ (skip-begin Z)))) ⇓-base

-- Before re-entry α is dead according to the index, so the ref resolves.
ninth-source : ninth-Ψ ∋rep zero ≔ ‵ `ℕ
ninth-source =
  ∋rep-of ninth-new-raw (⇓-ref-dead refl ninth-old-rep)

ninth-target : TyEnv (sucⁿ (sucⁿ zeroⁿ)) (sucⁿ zeroⁿ)
    (false Vec.∷ true Vec.∷ Vec.[])
ninth-target =
  (ninth-Ψ ,end[ zero ≔ suc zero ])
    ,begin[ zero ≔ suc zero ]⟨ refl ⟩

-- Re-entry makes α live at slot zero, so the same raw ref now reads
-- abstractly through that slot.
ninth-target-abstract : ninth-target ∋rep zero ≔ ＇ zero
ninth-target-abstract =
  ∋rep-of (skip-begin (skip-end ninth-new-raw))
    (⇓-ref-live refl)

-- This is the exact failed obligation of unconditional `∋rep-reenter`.
ninth-target-not-source : ¬ (ninth-target ∋rep zero ≔ ‵ `ℕ)
ninth-target-not-source source-payload
    with ∋rep-unique ninth-target-abstract source-payload
ninth-target-not-source source-payload | ()
