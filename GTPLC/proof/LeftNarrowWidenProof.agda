module proof.LeftNarrowWidenProof where

-- File Charter:
--   * Begins the proofs of the GTPLC Left Narrowing and Left Widening lemmas.
--   * Splits Left Narrowing on its narrowing derivation.
--   * Splits Left Widening on its widening derivation.
--   * Leaves the individual constructor cases as interaction holes.

open import NarrowWiden
open import proof.LeftNarrowWiden

------------------------------------------------------------------------
-- Left Narrowing
------------------------------------------------------------------------

left-narrowing : LeftNarrowing
left-narrowing {d⊒ = idᵃ a b hA hB a⊒b} = {!!}
left-narrowing {d⊒ = c ↦ d} = {!!}
left-narrowing {d⊒ = ∀ⁿ c} = {!!}
left-narrowing {d⊒ = untag ι} = {!!}
left-narrowing {d⊒ = untag★⇒★} = {!!}
left-narrowing {d⊒ = untag★⇒★︔ c [ ★⇒★≢B ]} = {!!}
left-narrowing {d⊒ = seal X∈ X<Δᴿ} = {!!}
left-narrowing {d⊒ = gen nonvarA zero∈A c B≢★} = {!!}

------------------------------------------------------------------------
-- Left Widening
------------------------------------------------------------------------

left-widening : LeftWidening
left-widening {u⊑ = idᵃ a b hA hB a⊑b} = {!!}
left-widening {u⊑ = c ↦ d} = {!!}
left-widening {u⊑ = ∀ʷ c} = {!!}
left-widening {u⊑ = tag ι} = {!!}
left-widening {u⊑ = tag★⇒★} = {!!}
left-widening {u⊑ = c ︔tag★⇒★[ A≢★⇒★ ]} = {!!}
left-widening {u⊑ = unseal X∈ X<Δᴸ} = {!!}
left-widening {u⊑ = inst nonvarA zero∈A c B≢★} = {!!}
