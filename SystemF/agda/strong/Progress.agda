module strong.Progress where

-- Progress for the tight dual boundary (B₀) design (PLAN.md §5), under the
-- Decision-6 ACTIVE/INERT discipline (Siek & Chen, JFP 31(e30) 2021;
-- notes/ParameterizedCastCalculi.md).
--
-- Generalised over the TYPE context Δ, exactly as preservation is: ξ-⟪⟫
-- reduces the INTERIOR of a boundary, which is typed at intOf Δ Θ, i.e. at a
-- different Δ.  The TERM context is always [] (runtime), so ⊢` is impossible.
--
-- THE SHAPE OF THE PROOF AFTER THE INSTALL.  The paper's Theorem 14 splits a
-- well-typed term into a value, a step, or a wrapper whose cast is ACTIVE and
-- therefore steps by applyCast.  Ours does the same, in three places:
--
--   * the ELIMINATIONS (app-steps / tapp-steps) see only INERT wrappers,
--     because an active one is not a value.  By inert-ext an inert face keeps
--     its head constructor when read outward, so an arrow-typed wrapper value
--     has the SYNTACTIC ⇒ face Peel needs (`InertCross→`) and a ∀-typed one
--     has the syntactic ∀ face — cf-⇒-B₀ / cf-∀-B₀'s reveal-variable branch
--     is REFUTED by inertness, which is precisely how rv-app / rv-tapp
--     dissolved.  Neither elimination case assumes anything.
--   * the WRAPPER case of progress classifies the face (ActiveOrInert): inert
--     ⇒ the wrapper is a value; active ⇒ apply-active steps it.
--   * apply-active IS applyCast: canon-ℕ / canon-𝔹 / canon-var-conceal pin
--     the body's shape at each active face, leaving Merge's MergeOK premise
--     at a reveal-variable face as the one residue (strong.ProgressDef).

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)
open import strong.Types
open import strong.Context using (TCtx; Ctx)
open import strong.Boundary
open import strong.BReduction
open import strong.Canonical using (canon-ℕ; canon-𝔹; canon-var-conceal)
open import strong.ProgressDef

-- Parameterised over the ONE open fact: applyCast totality at a
-- reveal-variable face, i.e. MergeOK's derivability there
-- (strong.ProgressDef, and notes/DECISIONS.md's Decision-6 crux).
-- Everything else below is proven.
module Impl (mrg-ok : MergeDerivable) where

  ------------------------------------------------------------------------
  -- 0.  Boundary-type shape analysis
  --
  -- Ported from notes/old/BoundaryRulesProbe.agda §6; `split` and
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
  -- 2.  APPLYCAST: every well-typed ACTIVE wrapper around a value steps.
  --
  -- This is the paper's `applyCast` totality field, and it is where the
  -- sharpened canonical forms do their work.  At each active face the
  -- body's INTERIOR type is forced, and the canonical form for that type
  -- names the one shape that can occur:
  --
  --   ℕ face   internal face substᵗ (γᵇ Θ) `ℕ = `ℕ, so canon-ℕ makes the
  --            body a NUMERAL — Drop$.  (A wrapper body is impossible: it
  --            would have to be a value of type ℕ, and baseNotInert-ℕ
  --            forbids an ℕ-exporting inert face.  This is what collapses
  --            the base-face action set to ONE rule.)
  --   𝔹 face   canon-𝔹: there is no value of type 𝔹 — vacuous.
  --   ` X face internal face γᵇ Θ X = ` X (γᵇ-lo), so canon-var-conceal
  --            makes the body a SEALED value V′ ⟪ Θ₁ , ` Y ⟫ with
  --            revs Θ₁ ≤ Y — Merge, with MergeOK from the parameter.
  ------------------------------------------------------------------------

  apply-active : ∀ {Δ V Θ B₀} → Value V → Active Θ B₀
    → Δ ∣ [] ⊢ V ⟪ Θ , B₀ ⟫ ⦂ substᵗ (ρᵇ Θ) B₀
    → Σ Term λ M′ → Δ ⊢ V ⟪ Θ , B₀ ⟫ -→ M′

  apply-active v A-ℕ ⊢W with canon-ℕ v (inv-body ⊢W)
  apply-active v A-ℕ ⊢W | (n , refl) = _ , Drop$

  apply-active v A-𝔹 ⊢W = ⊥-elim (canon-𝔹 v (inv-body ⊢W))

  apply-active {Δ} {V} {Θ} {` X} v (A-var X<r) ⊢W
    with canon-var-conceal v
           (subst (λ T → intOf Δ Θ ∣ [] ⊢ V ⦂ T) (γᵇ-lo Θ X X<r)
                  (inv-body ⊢W))
  apply-active v (A-var X<r) ⊢W | (V′ , Θ₁ , Y , refl , ge , v′) =
    _ , Merge v′ (I-var ge) (A-var X<r) (mrg-ok v′ ge X<r ⊢W)

  ------------------------------------------------------------------------
  -- 3.  The two eliminations applied to a value
  --
  -- PEEL IS TOTAL AT AN ⇒ FACE: it does not consume the ƛ, so the wrapped
  -- value's shape is irrelevant.  At a ∀ face one further split is needed,
  -- on the wrapper's BODY (a Λ ⇒ TyWrap, a wrapper ⇒ TyPeel).  The
  -- reveal-variable branch of cf-⇒-B₀ / cf-∀-B₀ is REFUTED: the wrapper is a
  -- value, so its face is inert, and no face is both.
  ------------------------------------------------------------------------

  -- a wrapper whose boundary type is ∀-shaped, type-applied
  tapp-∀ : ∀ {Δ V Θ B₀ B A} → Value V
         → intOf Δ Θ ∣ [] ⊢ V ⦂ substᵗ (γᵇ Θ) (`∀ B₀)
         → Σ Term λ M′ → Δ ⊢ ((V ⟪ Θ , `∀ B₀ ⟫) ·[ B , A ]) -→ M′
  tapp-∀ V-$           ()
  tapp-∀ (V-G G-ƛ)     ()
  tapp-∀ (V-G (G-Λ v)) ⊢V = _ , TyWrap v
  tapp-∀ (V-⟪⟫ v i)    ⊢V = _ , TyPeel v i   -- wrapper body: peel

  -- L · M with both sides values.  L : A ⇒ B, so L is a ƛ (Beta) or a
  -- wrapper — and an INERT one, so its face is syntactically an arrow.
  app-steps : ∀ {Δ L M A B} → Value L → Value M → Δ ∣ [] ⊢ L ⦂ (A ⇒ B)
            → Σ Term λ M′ → Δ ⊢ (L · M) -→ M′
  app-steps V-$           w ()
  app-steps (V-G G-ƛ)     w ⊢L = _ , Beta w
  app-steps (V-G (G-Λ v)) w ()
  app-steps (V-⟪⟫ {Θ = Θ} {B₀ = B₀} v i) w ⊢L
    with cf-⇒-B₀ Θ B₀ (sym (inv-⟪⟫ ⊢L))
  app-steps (V-⟪⟫ v i) w ⊢L | inj₁ (B₁ , B₂ , refl) = _ , Peel v w
  -- a reveal-variable face is ACTIVE, so this wrapper is not a value
  app-steps (V-⟪⟫ v i) w ⊢L | inj₂ (X , refl , X<r) =
    ⊥-elim (active-not-inert (A-var X<r) i)

  -- L ·[ B , A ] with L a value.  L : `∀ B, so L is a Λ (TyBeta) or an
  -- INERT wrapper, whose face is then syntactically a ∀.
  tapp-steps : ∀ {Δ L B A} → Value L → Δ ∣ [] ⊢ L ⦂ `∀ B
             → Σ Term λ M′ → Δ ⊢ (L ·[ B , A ]) -→ M′
  tapp-steps V-$           ()
  tapp-steps (V-G G-ƛ)     ()
  tapp-steps (V-G (G-Λ v)) ⊢L = _ , TyBeta v
  tapp-steps (V-⟪⟫ {Θ = Θ} {B₀ = B₀} v i) ⊢L
    with cf-∀-B₀ Θ B₀ (sym (inv-⟪⟫ ⊢L))
  tapp-steps (V-⟪⟫ v i) ⊢L | inj₁ (B₀′ , refl) = tapp-∀ v (inv-body ⊢L)
  tapp-steps (V-⟪⟫ v i) ⊢L | inj₂ (X , refl , X<r) =
    ⊥-elim (active-not-inert (A-var X<r) i)

  ------------------------------------------------------------------------
  -- 4.  Progress
  ------------------------------------------------------------------------

  progress : ∀ {Δ M A} → Δ ∣ [] ⊢ M ⦂ A
           → Value M ⊎ (Σ Term λ M′ → Δ ⊢ M -→ M′)

  -- no term variable is in scope at the runtime term context
  progress (⊢` ())

  progress ⊢$          = inj₁ V-$
  progress (⊢ƛ wfA ⊢N) = inj₁ (V-G G-ƛ)

  -- Λ N is a value only when N is (G-Λ), so the body must be reduced in place;
  -- it is typed at (abst ∷ Δ) ∣ ⤊ [], and ⤊ [] = [] definitionally
  progress (⊢Λ ⊢N) with progress ⊢N
  progress (⊢Λ ⊢N) | inj₁ v           = inj₁ (V-G (G-Λ v))
  progress (⊢Λ ⊢N) | inj₂ (N′ , N→N′) = inj₂ (Λ N′ , ξ-Λ N→N′)

  -- likewise the INTERIOR of a boundary, typed at intOf Δ Θ ∣ [] — and then
  -- the FACE decides: inert ⇒ a value, active ⇒ applyCast
  progress (env bwf sc ⊢M) with progress ⊢M
  progress (env {Θ = Θ} {B₀ = B₀} bwf sc ⊢M) | inj₂ (M′ , M→M′) =
    inj₂ (M′ ⟪ Θ , B₀ ⟫ , ξ-⟪⟫ M→M′)
  progress (env {Θ = Θ} {B₀ = B₀} bwf sc ⊢M) | inj₁ v
    with ActiveOrInert Θ B₀
  progress (env bwf sc ⊢M) | inj₁ v | inj₂ i = inj₁ (V-⟪⟫ v i)
  progress (env bwf sc ⊢M) | inj₁ v | inj₁ a =
    inj₂ (apply-active v a (env bwf sc ⊢M))

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
