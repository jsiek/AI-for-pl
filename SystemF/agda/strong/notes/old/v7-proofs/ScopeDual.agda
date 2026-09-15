module strong.proof.ScopeDual where

-- Strong System F v7 — the dual of a scope change is an EXACT inverse.
--
-- `Wrap` sends the argument back out through `-χ`:
--
--   νΘ,χ[V|c] · W  -→  νΘ,χ[ V · ν∅,-χ[W|c₁] | c₂ ]
--
-- and for the inner boundary to type, `-χ` must lead from the interior
-- back to `ty(Γ)++Θ` — that is where `c₁` and the weakened argument live.
-- With merged entries a change FLIPS A BIT and adds no entry, so undoing
-- it is undoing a flip: the round trip returns the SAME context, not one
-- up to reordering.
--
-- The split representation could not do this.  There a conceal removed a
-- name IN PLACE, under whatever anchors sat above it, while the dual
-- reveal put it back ON TOP; the two contexts agreed on everything
-- observable and differed as lists.

open import Data.Nat using (zero)
open import Data.List using (List; []; _∷_; _++_; map; reverse)
open import Data.List.Properties using (unfold-reverse; map-++)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

open import strong.Ctx
open import strong.CtxMorph

private
  variable
    Δ Δ′ Δ₁ Δ₂ Δ₃ : Ctxᵗ
    δ : Change
    χ χ₁ χ₂ : Scope

scope-++ : Δ₁ ⊢χ χ₁ ⇒ Δ₂ → Δ₂ ⊢χ χ₂ ⇒ Δ₃ → Δ₁ ⊢χ χ₁ ++ χ₂ ⇒ Δ₃
scope-++ scope[] t = t
scope-++ (scope∷ d s) t = scope∷ d (scope-++ s t)

-- Undoing a flip is a flip.
δ-invert : Δ ⊢δ δ ⇒ Δ′ → Δ′ ⊢δ dualChange δ ⇒ Δ
δ-invert rev-here = con-here
δ-invert (rev-under d) = con-under (δ-invert d)
δ-invert con-here = rev-here
δ-invert (con-under d) = rev-under (δ-invert d)

dual-∷ : ∀ δ χ → dual (δ ∷ χ) ≡ dual χ ++ (dualChange δ ∷ [])
dual-∷ δ χ =
  trans (cong (map dualChange) (unfold-reverse δ χ))
        (map-++ dualChange (reverse χ) (δ ∷ []))

χ-invert : Δ ⊢χ χ ⇒ Δ′ → Δ′ ⊢χ dual χ ⇒ Δ
χ-invert scope[] = scope[]
χ-invert {Δ = Δ} {Δ′ = Δ′} (scope∷ {δ = δ} {χ = χ} d s) =
  subst (λ ξ → Δ′ ⊢χ ξ ⇒ Δ) (sym (dual-∷ δ χ))
    (scope-++ (χ-invert s) (scope∷ (δ-invert d) scope[]))

------------------------------------------------------------------------
-- The type-variable order IS the anchor order
------------------------------------------------------------------------

-- A reveal makes its anchor the NEWEST type variable, and a conceal
-- removes the newest — because a change passes only through entries that
-- are already concealed.  So an older anchor cannot be revealed while a
-- newer one is, and the out-of-order state is unrepresentable.
reveal-newest : ∀ {α} → Δ ⊢δ reveal α ⇒ Δ′ → Δ′ ∋n zero := α
reveal-newest rev-here = n-here
reveal-newest (rev-under d) = n-concealed (reveal-newest d)

conceal-newest : ∀ {α} → Δ ⊢δ conceal α ⇒ Δ′ → Δ ∋n zero := α
conceal-newest con-here = n-here
conceal-newest (con-under d) = n-concealed (conceal-newest d)
