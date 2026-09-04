module strong.Progress where

-- Progress for the tight dual boundary (B₀) design (PLAN.md §5).
--
-- Generalised over the TYPE context Δ, exactly as preservation is: ξ-⟪⟫
-- reduces the INTERIOR of a boundary, which is typed at intOf Δ Θ, i.e. at a
-- different Δ.  The TERM context is always [] (runtime), so ⊢` is impossible.
--
-- The value cases of the two eliminations are factored into app-steps and
-- tapp-steps.  Neither goes through strong.Canonical: inverting the Value
-- proof already pins the head constructor of the term, and inv-⟪⟫ / inv-body
-- recover the wrapper's external-face equation and its body's typing without
-- pattern-matching (env) against a non-constructor type index.  What remains
-- is the shape of the BOUNDARY type B₀ — that is what selects the rule —
-- which is cf-⇒-B₀ / cf-∀-B₀, ported from notes/BoundaryRulesProbe §6, and
-- then, since Wrap/TyWrap consume the ƛ/Λ they are applied to, the shape of
-- the wrapper's BODY (app-⇒ / tapp-∀).

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
open import strong.ProgressDef

-- Parameterised over the four open cases (strong.ProgressDef): the two
-- reveal-variable ones (Decision 1) and the two nested-wrapper ones (Merge,
-- Decision 3).  Order: application before type application within each
-- family, reveal-variable family first.  Instantiate `Impl` once they are
-- proven.
module Impl (rv-app : RevealVarApp) (rv-tapp : RevealVarTApp)
            (nt-app : NestedApp)    (nt-tapp : NestedTApp) where

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

  -- the (env) premise that types the BODY, at the wrapper's interior and
  -- interior face.  Free result index T, for the same reason as inv-⟪⟫.
  inv-body : ∀ {Δ Γₜ V Θ B₀ T} → Δ ∣ Γₜ ⊢ V ⟪ Θ , B₀ ⟫ ⦂ T
           → intOf Δ Θ ∣ [] ⊢ V ⦂ substᵗ (γᵇ Θ) B₀
  inv-body (env bwf sc ⊢V) = ⊢V

  ------------------------------------------------------------------------
  -- 2.  The two eliminations applied to a value
  --
  -- Wrap and TyWrap are PARTIAL in the wrapped value: each consumes a binder
  -- (a ƛ / a Λ), so a wrapper at an ⇒ / ∀ boundary type must have its BODY
  -- analysed too.  The body's own typing — at the interior face, which is
  -- ⇒ / ∀-shaped by construction — refutes the numeral and the mismatched
  -- binder; what is left is the binder (the rule fires) or a nested wrapper
  -- (Merge's job, a ProgressDef parameter until Merge lands).
  ------------------------------------------------------------------------

  -- a wrapper whose boundary type is ⇒-shaped, applied to a value
  app-⇒ : ∀ {Δ V W Θ B₁ B₂ A B} → Value V → Value W
        → intOf Δ Θ ∣ [] ⊢ V ⦂ substᵗ (γᵇ Θ) (B₁ ⇒ B₂)
        → Δ ∣ [] ⊢ V ⟪ Θ , B₁ ⇒ B₂ ⟫ ⦂ (A ⇒ B)
        → Σ Term λ M′ → ((V ⟪ Θ , B₁ ⇒ B₂ ⟫) · W) -→ M′
  app-⇒ V-$           w () ⊢L
  app-⇒ (V-G G-ƛ)     w ⊢V ⊢L = _ , Wrap w
  app-⇒ (V-G (G-Λ v)) w () ⊢L
  app-⇒ (V-⟪⟫ v)      w ⊢V ⊢L = nt-app v w ⊢L   -- nested wrapper (Merge)

  -- a wrapper whose boundary type is ∀-shaped, type-applied
  tapp-∀ : ∀ {Δ V Θ B₀ B A} → Value V
         → intOf Δ Θ ∣ [] ⊢ V ⦂ substᵗ (γᵇ Θ) (`∀ B₀)
         → Δ ∣ [] ⊢ V ⟪ Θ , `∀ B₀ ⟫ ⦂ `∀ B
         → Σ Term λ M′ → ((V ⟪ Θ , `∀ B₀ ⟫) ·[ B , A ]) -→ M′
  tapp-∀ V-$           () ⊢L
  tapp-∀ (V-G G-ƛ)     () ⊢L
  tapp-∀ (V-G (G-Λ v)) ⊢V ⊢L = _ , TyWrap v
  tapp-∀ (V-⟪⟫ v)      ⊢V ⊢L = nt-tapp v ⊢L     -- nested wrapper (Merge)

  -- L · M with both sides values.  L : A ⇒ B, so L is a ƛ (Beta) or a wrapper.
  app-steps : ∀ {Δ L M A B} → Value L → Value M → Δ ∣ [] ⊢ L ⦂ (A ⇒ B)
            → Σ Term λ M′ → (L · M) -→ M′
  app-steps V-$           w ()
  app-steps (V-G G-ƛ)     w ⊢L = _ , Beta w
  app-steps (V-G (G-Λ v)) w ()
  app-steps (V-⟪⟫ {Θ = Θ} {B₀ = B₀} v) w ⊢L
    with cf-⇒-B₀ Θ B₀ (sym (inv-⟪⟫ ⊢L))
  app-steps (V-⟪⟫ v) w ⊢L | inj₁ (B₁ , B₂ , refl) =
    app-⇒ v w (inv-body ⊢L) ⊢L
  app-steps (V-⟪⟫ v) w ⊢L | inj₂ (X , refl , X<r) =
    rv-app v w ⊢L X<r      -- reveal-variable boundary type (ProgressDef)

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
    tapp-∀ v (inv-body ⊢L) ⊢L
  tapp-steps (V-⟪⟫ v) ⊢L | inj₂ (X , refl , X<r) =
    rv-tapp v ⊢L X<r       -- reveal-variable boundary type (ProgressDef)

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
