module proof.NuCore.Relations.NuImprecisionContextExclusivityProof where

-- File Charter:
--   * Proves source-name exclusivity for the empty context and preserves it
--     through all runtime allocation context transformations.
--   * Covers matched, source-only, and crossed two-allocation contexts.
--   * Contains no postulates, holes, permissive options, or simulation import.

open import Agda.Builtin.Equality using (refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc)

open import Imprecision using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; ⇑ᴿᵢ
  ; swapRight∀∀ᵢ
  )
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)


private
  un⇑ᵢ-★∈ :
    ∀ {Φ α} →
    (suc α ˣ⊑★) ∈ ⇑ᵢ Φ →
    (α ˣ⊑★) ∈ Φ
  un⇑ᵢ-★∈ {Φ = []} ()
  un⇑ᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
  un⇑ᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there star∈) =
    there (un⇑ᵢ-★∈ star∈)
  un⇑ᵢ-★∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there star∈) =
    there (un⇑ᵢ-★∈ star∈)

  un⇑ᵢ-ˣ∈ :
    ∀ {Φ α β} →
    (suc α ˣ⊑ˣ suc β) ∈ ⇑ᵢ Φ →
    (α ˣ⊑ˣ β) ∈ Φ
  un⇑ᵢ-ˣ∈ {Φ = []} ()
  un⇑ᵢ-ˣ∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there match∈) =
    there (un⇑ᵢ-ˣ∈ match∈)
  un⇑ᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
  un⇑ᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there match∈) =
    there (un⇑ᵢ-ˣ∈ match∈)

  no-⇑ᵢ-zero-star :
    ∀ {Φ} →
    (zero ˣ⊑★) ∈ ⇑ᵢ Φ →
    ⊥
  no-⇑ᵢ-zero-star {Φ = []} ()
  no-⇑ᵢ-zero-star {Φ = (_ ˣ⊑★) ∷ Φ} (there star∈) =
    no-⇑ᵢ-zero-star star∈
  no-⇑ᵢ-zero-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there star∈) =
    no-⇑ᵢ-zero-star star∈

  no-⇑ᵢ-zero-left :
    ∀ {Φ β} →
    (zero ˣ⊑ˣ β) ∈ ⇑ᵢ Φ →
    ⊥
  no-⇑ᵢ-zero-left {Φ = []} ()
  no-⇑ᵢ-zero-left {Φ = (_ ˣ⊑★) ∷ Φ} (there match∈) =
    no-⇑ᵢ-zero-left match∈
  no-⇑ᵢ-zero-left {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there match∈) =
    no-⇑ᵢ-zero-left match∈

  no-⇑ᵢ-zero-right :
    ∀ {Φ α} →
    (α ˣ⊑ˣ zero) ∈ ⇑ᵢ Φ →
    ⊥
  no-⇑ᵢ-zero-right {Φ = []} ()
  no-⇑ᵢ-zero-right {Φ = (_ ˣ⊑★) ∷ Φ} (there match∈) =
    no-⇑ᵢ-zero-right match∈
  no-⇑ᵢ-zero-right {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there match∈) =
    no-⇑ᵢ-zero-right match∈

  un⇑ᴸᵢ-★∈ :
    ∀ {Φ α} →
    (suc α ˣ⊑★) ∈ ⇑ᴸᵢ Φ →
    (α ˣ⊑★) ∈ Φ
  un⇑ᴸᵢ-★∈ {Φ = []} ()
  un⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
  un⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there star∈) =
    there (un⇑ᴸᵢ-★∈ star∈)
  un⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there star∈) =
    there (un⇑ᴸᵢ-★∈ star∈)

  un⇑ᴸᵢ-ˣ∈ :
    ∀ {Φ α β} →
    (suc α ˣ⊑ˣ β) ∈ ⇑ᴸᵢ Φ →
    (α ˣ⊑ˣ β) ∈ Φ
  un⇑ᴸᵢ-ˣ∈ {Φ = []} ()
  un⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there match∈) =
    there (un⇑ᴸᵢ-ˣ∈ match∈)
  un⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
  un⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there match∈) =
    there (un⇑ᴸᵢ-ˣ∈ match∈)

  no-⇑ᴸᵢ-zero-left :
    ∀ {Φ β} →
    (zero ˣ⊑ˣ β) ∈ ⇑ᴸᵢ Φ →
    ⊥
  no-⇑ᴸᵢ-zero-left {Φ = []} ()
  no-⇑ᴸᵢ-zero-left {Φ = (_ ˣ⊑★) ∷ Φ} (there match∈) =
    no-⇑ᴸᵢ-zero-left match∈
  no-⇑ᴸᵢ-zero-left {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there match∈) =
    no-⇑ᴸᵢ-zero-left match∈

  un⇑ᴿᵢ-★∈ :
    ∀ {Φ α} →
    (α ˣ⊑★) ∈ ⇑ᴿᵢ Φ →
    (α ˣ⊑★) ∈ Φ
  un⇑ᴿᵢ-★∈ {Φ = []} ()
  un⇑ᴿᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
  un⇑ᴿᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there star∈) =
    there (un⇑ᴿᵢ-★∈ star∈)
  un⇑ᴿᵢ-★∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there star∈) =
    there (un⇑ᴿᵢ-★∈ star∈)

  un⇑ᴿᵢ-ˣ∈ :
    ∀ {Φ α β} →
    (α ˣ⊑ˣ suc β) ∈ ⇑ᴿᵢ Φ →
    (α ˣ⊑ˣ β) ∈ Φ
  un⇑ᴿᵢ-ˣ∈ {Φ = []} ()
  un⇑ᴿᵢ-ˣ∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there match∈) =
    there (un⇑ᴿᵢ-ˣ∈ match∈)
  un⇑ᴿᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
  un⇑ᴿᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there match∈) =
    there (un⇑ᴿᵢ-ˣ∈ match∈)

  no-⇑ᴿᵢ-zero-right :
    ∀ {Φ α} →
    (α ˣ⊑ˣ zero) ∈ ⇑ᴿᵢ Φ →
    ⊥
  no-⇑ᴿᵢ-zero-right {Φ = []} ()
  no-⇑ᴿᵢ-zero-right {Φ = (_ ˣ⊑★) ∷ Φ} (there match∈) =
    no-⇑ᴿᵢ-zero-right match∈
  no-⇑ᴿᵢ-zero-right {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there match∈) =
    no-⇑ᴿᵢ-zero-right match∈


source-name-exclusive-empty : SourceNameExclusive []
source-name-exclusive-empty () match∈


source-name-exclusive-⇑ᵢ :
  ∀ {Φ : ImpCtx} →
  SourceNameExclusive Φ →
  SourceNameExclusive (⇑ᵢ Φ)
source-name-exclusive-⇑ᵢ exclusive {α = zero} star∈ match∈ =
  no-⇑ᵢ-zero-star star∈
source-name-exclusive-⇑ᵢ exclusive {α = suc α} {β = zero}
    star∈ match∈ =
  no-⇑ᵢ-zero-right match∈
source-name-exclusive-⇑ᵢ exclusive {α = suc α} {β = suc β}
    star∈ match∈ =
  exclusive (un⇑ᵢ-★∈ star∈) (un⇑ᵢ-ˣ∈ match∈)


source-name-exclusive-⇑ᴸᵢ :
  ∀ {Φ : ImpCtx} →
  SourceNameExclusive Φ →
  SourceNameExclusive (⇑ᴸᵢ Φ)
source-name-exclusive-⇑ᴸᵢ exclusive {α = zero} star∈ match∈ =
  no-⇑ᴸᵢ-zero-left match∈
source-name-exclusive-⇑ᴸᵢ exclusive {α = suc α}
    star∈ match∈ =
  exclusive (un⇑ᴸᵢ-★∈ star∈) (un⇑ᴸᵢ-ˣ∈ match∈)


source-name-exclusive-⇑ᴿᵢ :
  ∀ {Φ : ImpCtx} →
  SourceNameExclusive Φ →
  SourceNameExclusive (⇑ᴿᵢ Φ)
source-name-exclusive-⇑ᴿᵢ exclusive {β = zero} star∈ match∈ =
  no-⇑ᴿᵢ-zero-right match∈
source-name-exclusive-⇑ᴿᵢ exclusive {β = suc β} star∈ match∈ =
  exclusive (un⇑ᴿᵢ-★∈ star∈) (un⇑ᴿᵢ-ˣ∈ match∈)


source-name-exclusive-matched-head :
  ∀ {Φ : ImpCtx} →
  SourceNameExclusive Φ →
  SourceNameExclusive ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
source-name-exclusive-matched-head exclusive (here ()) match∈
source-name-exclusive-matched-head exclusive (there star∈) (here refl) =
  no-⇑ᵢ-zero-star star∈
source-name-exclusive-matched-head exclusive
    (there star∈) (there match∈) =
  source-name-exclusive-⇑ᵢ exclusive star∈ match∈


source-name-exclusive-source-only-head :
  ∀ {Φ : ImpCtx} →
  SourceNameExclusive Φ →
  SourceNameExclusive ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
source-name-exclusive-source-only-head exclusive
    (here refl) (here ())
source-name-exclusive-source-only-head exclusive
    (here refl) (there match∈) =
  no-⇑ᴸᵢ-zero-left match∈
source-name-exclusive-source-only-head exclusive
    (there star∈) (here ())
source-name-exclusive-source-only-head exclusive
    (there star∈) (there match∈) =
  source-name-exclusive-⇑ᴸᵢ exclusive star∈ match∈


source-name-exclusive-source-only-matched-shift-head :
  ∀ {Φ : ImpCtx} →
  SourceNameExclusive Φ →
  SourceNameExclusive ((zero ˣ⊑★) ∷ ⇑ᵢ Φ)
source-name-exclusive-source-only-matched-shift-head exclusive
    (here refl) (here ())
source-name-exclusive-source-only-matched-shift-head exclusive
    (here refl) (there match∈) =
  no-⇑ᵢ-zero-left match∈
source-name-exclusive-source-only-matched-shift-head exclusive
    (there star∈) (here ())
source-name-exclusive-source-only-matched-shift-head exclusive
    (there star∈) (there match∈) =
  source-name-exclusive-⇑ᵢ exclusive star∈ match∈


source-name-exclusive-swap-right-∀∀ :
  ∀ {Φ : ImpCtx} →
  SourceNameExclusive Φ →
  SourceNameExclusive (swapRight∀∀ᵢ Φ)
source-name-exclusive-swap-right-∀∀ exclusive (here ()) match∈
source-name-exclusive-swap-right-∀∀ exclusive
    (there (here ())) match∈
source-name-exclusive-swap-right-∀∀ exclusive
    (there (there star∈)) (here refl) =
  no-⇑ᵢ-zero-star star∈
source-name-exclusive-swap-right-∀∀ exclusive
    (there (there star∈)) (there (here refl)) =
  no-⇑ᵢ-zero-star (un⇑ᵢ-★∈ star∈)
source-name-exclusive-swap-right-∀∀ exclusive
    (there (there star∈)) (there (there match∈)) =
  source-name-exclusive-⇑ᵢ
    (source-name-exclusive-⇑ᵢ exclusive) star∈ match∈
