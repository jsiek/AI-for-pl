module strong.Progress where

-- Progress for the tight dual boundary (B₀) design (PLAN.md §5).
--
-- Generalised over the TYPE context Δ, exactly as preservation is: ξ-⟪⟫
-- reduces the INTERIOR of a boundary, which is typed at intOf Δ Θ, i.e. at a
-- different Δ.  The TERM context is always [] (runtime), so ⊢` is impossible.
--
-- The value cases of the two eliminations are factored into app-steps and
-- tapp-steps.  Neither goes through strong.Canonical: inverting the Value
-- proof already pins the head constructor of the term, and inv-⟪⟫ recovers the
-- wrapper's external-face equation without pattern-matching (env) against a
-- non-constructor type index.  What remains is the shape of the BOUNDARY type
-- B₀ — that is what selects the rule — which is cf-⇒-B₀ / cf-∀-B₀, ported
-- from notes/BoundaryRulesProbe §6.

open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)
open import strong.Types
open import strong.Context using (TCtx; Ctx)
open import strong.Boundary
open import strong.BReduction

------------------------------------------------------------------------
-- 0.  Boundary-type shape analysis
--
-- Ported from notes/BoundaryRulesProbe.agda §6 (proved there); `split` and
-- ρᵇ-hi (the exterior face is the identity on the Γ-part of the boundary
-- frame) are already live in strong.BReduction.
------------------------------------------------------------------------

-- A wrapper whose EXTERNAL face is a ∀ either has a ∀ boundary type — and
-- then R1 fires — or a REVEAL variable as its boundary type (memo §4).  A
-- ` X with X ≥ revs Θ is impossible: by ρᵇ-hi the external face would then be
-- a variable, and no elimination types a variable.
cf-∀-B₀ : ∀ Θ B₀ {B} → substᵗ (ρᵇ Θ) B₀ ≡ `∀ B
  → (Σ Ty λ B₀′ → B₀ ≡ `∀ B₀′)
  ⊎ (Σ ℕ λ X → (B₀ ≡ ` X) × (X < revs Θ))
cf-∀-B₀ Θ (` X) eq with split (revs Θ) X
cf-∀-B₀ Θ (` X) eq | inj₁ X<r        = inj₂ (X , refl , X<r)
cf-∀-B₀ Θ (` X) eq | inj₂ (i , refl) =
  ⊥-elim (var≢∀ (trans (sym (ρᵇ-hi Θ i)) eq))
  where
    var≢∀ : ∀ {j T} → (` j) ≡ `∀ T → ⊥
    var≢∀ ()
cf-∀-B₀ Θ `ℕ      ()
cf-∀-B₀ Θ `𝔹      ()
cf-∀-B₀ Θ (A ⇒ B) ()
cf-∀-B₀ Θ (`∀ T)  eq = inj₁ (T , refl)

cf-⇒-B₀ : ∀ Θ B₀ {A B} → substᵗ (ρᵇ Θ) B₀ ≡ (A ⇒ B)
  → (Σ Ty λ B₁ → Σ Ty λ B₂ → B₀ ≡ (B₁ ⇒ B₂))
  ⊎ (Σ ℕ λ X → (B₀ ≡ ` X) × (X < revs Θ))
cf-⇒-B₀ Θ (` X) eq with split (revs Θ) X
cf-⇒-B₀ Θ (` X) eq | inj₁ X<r        = inj₂ (X , refl , X<r)
cf-⇒-B₀ Θ (` X) eq | inj₂ (i , refl) =
  ⊥-elim (var≢⇒ (trans (sym (ρᵇ-hi Θ i)) eq))
  where
    var≢⇒ : ∀ {j S T} → (` j) ≡ (S ⇒ T) → ⊥
    var≢⇒ ()
cf-⇒-B₀ Θ `ℕ        ()
cf-⇒-B₀ Θ `𝔹        ()
cf-⇒-B₀ Θ (B₁ ⇒ B₂) eq = inj₁ (B₁ , B₂ , refl)
cf-⇒-B₀ Θ (`∀ T)    ()

------------------------------------------------------------------------
-- 1.  Wrapper inversion
--
-- (env) is the only rule whose subject is a wrapper, so the type of a
-- wrapper is FORCED to be its external face.  Stated with a free result
-- index T so the unifier never has to match a constructor type against the
-- neutral substᵗ (ρᵇ Θ) B₀ — which is why progress never pattern-matches
-- (env) at an ⇒ / ∀ type.
------------------------------------------------------------------------

inv-⟪⟫ : ∀ {Δ Γₜ V Θ B₀ T} → Δ ∣ Γₜ ⊢ V ⟪ Θ , B₀ ⟫ ⦂ T
       → T ≡ substᵗ (ρᵇ Θ) B₀
inv-⟪⟫ (env bwf sc ⊢V) = refl

------------------------------------------------------------------------
-- 2.  The two eliminations applied to a value
------------------------------------------------------------------------

-- L · M with both sides values.  L : A ⇒ B, so L is a ƛ (Beta) or a wrapper.
app-steps : ∀ {Δ L M A B} → Value L → Value M → Δ ∣ [] ⊢ L ⦂ (A ⇒ B)
          → Σ Term λ M′ → (L · M) -→ M′
app-steps V-$           w ()
app-steps (V-G G-ƛ)     w ⊢L = _ , Beta w
app-steps (V-G (G-Λ v)) w ()
app-steps (V-⟪⟫ {Θ = Θ} {B₀ = B₀} v) w ⊢L
  with cf-⇒-B₀ Θ B₀ (sym (inv-⟪⟫ ⊢L))
app-steps (V-⟪⟫ v) w ⊢L | inj₁ (B₁ , B₂ , refl) =
  _ , Wrap v w
app-steps (V-⟪⟫ v) w ⊢L | inj₂ (X , refl , X<r) =
  {!!}   -- reveal-variable boundary type: needs the grounded rep invariant
         -- (memo §4, decision pending)

-- L ·[ B , A ] with L a value.  L : `∀ B, so L is a Λ (TyBeta) or a wrapper.
-- The Λ case reads the body's value proof straight off G-Λ, so neither a
-- canonical-form equation nor a subst on the term is needed.
tapp-steps : ∀ {Δ L B A} → Value L → Δ ∣ [] ⊢ L ⦂ `∀ B
           → Σ Term λ M′ → (L ·[ B , A ]) -→ M′
tapp-steps V-$           ()
tapp-steps (V-G G-ƛ)     ()
tapp-steps (V-G (G-Λ v)) ⊢L = _ , TyBeta v
tapp-steps (V-⟪⟫ {Θ = Θ} {B₀ = B₀} v) ⊢L
  with cf-∀-B₀ Θ B₀ (sym (inv-⟪⟫ ⊢L))
tapp-steps (V-⟪⟫ v) ⊢L | inj₁ (B₀′ , refl) =
  _ , TyWrap v
tapp-steps (V-⟪⟫ v) ⊢L | inj₂ (X , refl , X<r) =
  {!!}   -- reveal-variable boundary type: needs the grounded rep invariant
         -- (memo §4, decision pending)

------------------------------------------------------------------------
-- 3.  Progress
------------------------------------------------------------------------

progress : ∀ {Δ M A} → Δ ∣ [] ⊢ M ⦂ A
         → Value M ⊎ (Σ Term λ M′ → M -→ M′)

-- no term variable is in scope at the runtime term context
progress (⊢` ())

progress ⊢$          = inj₁ V-$
progress (⊢ƛ wfA ⊢N) = inj₁ (V-G G-ƛ)

-- Λ N is a value only when N is (G-Λ), so the body must be reduced in place;
-- it is typed at (abst ∷ Δ) ∣ ⤊ [], and ⤊ [] = [] definitionally
progress (⊢Λ ⊢N) with progress ⊢N
progress (⊢Λ ⊢N) | inj₁ v           = inj₁ (V-G (G-Λ v))
progress (⊢Λ ⊢N) | inj₂ (N′ , N→N′) = inj₂ (Λ N′ , ξ-Λ N→N′)

-- likewise the INTERIOR of a boundary, typed at intOf Δ Θ ∣ []
progress (env bwf sc ⊢M) with progress ⊢M
progress (env bwf sc ⊢M) | inj₁ v = inj₁ (V-⟪⟫ v)
progress (env {Θ = Θ} {B₀ = B₀} bwf sc ⊢M) | inj₂ (M′ , M→M′) =
  inj₂ (M′ ⟪ Θ , B₀ ⟫ , ξ-⟪⟫ M→M′)

progress (⊢· ⊢L ⊢M) with progress ⊢L
progress (⊢· {M = M} ⊢L ⊢M) | inj₂ (L′ , L→L′) =
  inj₂ (L′ · M , ξ-·-l L→L′)
progress (⊢· ⊢L ⊢M) | inj₁ vL with progress ⊢M
progress (⊢· {L = L} ⊢L ⊢M) | inj₁ vL | inj₂ (M′ , M→M′) =
  inj₂ (L · M′ , ξ-·-r vL M→M′)
progress (⊢· ⊢L ⊢M) | inj₁ vL | inj₁ vM = inj₂ (app-steps vL vM ⊢L)

progress (⊢·[] ⊢L wfA) with progress ⊢L
progress (⊢·[] {B = B} {A = A} ⊢L wfA) | inj₂ (L′ , L→L′) =
  inj₂ (L′ ·[ B , A ] , ξ-·[] L→L′)
progress (⊢·[] ⊢L wfA) | inj₁ vL = inj₂ (tapp-steps vL ⊢L)
