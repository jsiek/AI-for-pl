-- Strong System F v8 — PROGRESS.
--
-- Every case is discharged here except one, which the module takes as a
-- parameter: at a boundary over a SIMPLE value, the conversion is
-- INERT (so the boundary is a value) or ACTIVE — the body is a literal
-- the `base` view sees through, and `Const` fires.  That is the
-- canonicity obligation notes-v8.md flags under "Conversion views".  It
-- is NOT provable for arbitrary typed normal conversions — see
-- notes/probes/V8CanonicityProbe.agda for a typed normal conversion
-- with a renaming element at a ground source and an arrow target — so
-- it needs an invariant on the conversions reduction can REACH.
module strong.proof.Progress where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.Reduction
open import strong.proof.Interior using (conv-interior)
open import strong.proof.Canonical

------------------------------------------------------------------------
-- Representation totality: every well-formed type has a representation
------------------------------------------------------------------------

quote-total : ∀ {Δ A} (Sg : Store) → Δ ⊢ᵗ A → Σ[ R ∈ RepTy ] (Sg ∣ Δ ⊢⌊ A ⌋ R)
quote-total Sg (wf-var n) = _ , quote-var n
quote-total Sg wf-ℕ = _ , quote-ℕ
quote-total Sg wf-𝔹 = _ , quote-𝔹
quote-total Sg (wf-⇒ a b) with quote-total Sg a | quote-total Sg b
quote-total Sg (wf-⇒ a b) | _ , qa | _ , qb = _ , quote-⇒ qa qb
quote-total Sg (wf-∀ a) with quote-total Sg a
quote-total Sg (wf-∀ a) | _ , qa = _ , quote-∀ qa

------------------------------------------------------------------------
-- A value at a ground type is a literal
------------------------------------------------------------------------

value-ℕ : ∀ {Sg Δ V} → Value V → Sg ∣ Δ ∣ [] ⊢ V ⦂ `ℕ
  → Σ[ n ∈ ℕ ] (V ≡ $ n)
value-ℕ (Vs simple) ⊢V = simple-ℕ simple ⊢V
value-ℕ (V⟨⟩ simple nf app) (⊢⟨⟩ nf′ ⊢M conv) =
  ⊥-elim (inert-ground app
           (subst GroundShape (sym (conv-target conv)) ground-ℕ))

------------------------------------------------------------------------
-- The canonicity obligation
------------------------------------------------------------------------

Canonicity : Set
Canonicity = ∀ {Sg Δᵢ Δ V c A B}
  → Simple V
  → Sg ∣ Δᵢ ∣ [] ⊢ V ⦂ A
  → Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ
  → NF c
  → Inert c ⊎ (Σ[ ι ∈ Ty ] (Literal V × (base c ≡ just ι)))

module Proof (canon : Canonicity) where

  Progresses : Store → Ctxᵗ → Term → Set
  Progresses Sg Δ M =
    Value M ⊎ (Σ[ N ∈ Term ] Σ[ Sg′ ∈ Store ] (Sg ∣ Δ ⊢ M —→ N ⊣ Sg′))

  progress : ∀ {Sg Δ M A} → Sg ∣ Δ ∣ [] ⊢ M ⦂ A → Progresses Sg Δ M
  progress (⊢` ())
  progress ⊢$ = inj₁ (Vs S$)
  progress ⊢# = inj₁ (Vs S#)

  progress (⊢⊕ ⊢L ⊢M) with progress ⊢L
  progress (⊢⊕ ⊢L ⊢M) | inj₂ (_ , _ , st) = inj₂ (_ , _ , ξ-⊕-l st)
  progress (⊢⊕ ⊢L ⊢M) | inj₁ vL with value-ℕ vL ⊢L
  progress (⊢⊕ ⊢L ⊢M) | inj₁ vL | _ , refl with progress ⊢M
  progress (⊢⊕ ⊢L ⊢M) | inj₁ vL | _ , refl | inj₂ (_ , _ , st) =
    inj₂ (_ , _ , ξ-⊕-r vL st)
  progress (⊢⊕ ⊢L ⊢M) | inj₁ vL | _ , refl | inj₁ vM with value-ℕ vM ⊢M
  progress (⊢⊕ ⊢L ⊢M) | inj₁ vL | _ , refl | inj₁ vM | _ , refl =
    inj₂ (_ , _ , PrimBeta)

  progress (⊢ƛ wf body) = inj₁ (Vs Sƛ)
  progress (⊢Λ v body) = inj₁ (Vs (SΛ v))
  progress (⊢ν wfR ⊢M) = inj₂ (_ , _ , Alloc)

  progress (⊢· ⊢L ⊢M) with progress ⊢L
  progress (⊢· ⊢L ⊢M) | inj₂ (_ , _ , st) = inj₂ (_ , _ , ξ-·-l st)
  progress (⊢· ⊢L ⊢M) | inj₁ vL with canonical-⇒ vL ⊢L | progress ⊢M
  progress (⊢· ⊢L ⊢M) | inj₁ vL | _ | inj₂ (_ , _ , st) =
    inj₂ (_ , _ , ξ-·-r vL st)
  progress (⊢· ⊢L ⊢M) | inj₁ vL | inj₁ (_ , _ , refl) | inj₁ vM =
    inj₂ (_ , _ , Beta vM)
  progress (⊢· ⊢L ⊢M) | inj₁ vL
    | inj₂ (_ , _ , _ , _ , _ , refl , arr-eq) | inj₁ vM =
    inj₂ (_ , _ , Wrap vL vM arr-eq)

  progress (⊢•[] ⊢L wfA) with progress ⊢L
  progress (⊢•[] ⊢L wfA) | inj₂ (_ , _ , st) = inj₂ (_ , _ , ξ-•[] st)
  progress {Sg = Sg} (⊢•[] ⊢L wfA) | inj₁ vL
    with canonical-∀ vL ⊢L | quote-total Sg wfA
  progress {Sg = Sg} (⊢•[] ⊢L wfA) | inj₁ vL
    | inj₁ (_ , v , refl) | _ , q = inj₂ (_ , _ , TyBeta v q)
  progress {Sg = Sg} (⊢•[] ⊢L wfA) | inj₁ vL
    | inj₂ (_ , _ , _ , refl , all-eq) | _ , q =
    inj₂ (_ , _ , TyWrap vL all-eq q)

  progress (⊢⟨⟩ nf ⊢M conv) with progress ⊢M
  progress (⊢⟨⟩ nf ⊢M conv) | inj₂ (_ , _ , st) =
    inj₂ (_ , _ , ξ-⟨⟩ (conv-interior conv) st)
  progress (⊢⟨⟩ nf ⊢M conv) | inj₁ (V⟨⟩ simple nf″ app) =
    inj₂ (_ , _ , Merge (V⟨⟩ simple nf″ app))
  progress (⊢⟨⟩ nf ⊢M conv) | inj₁ (Vs simple)
    with canon simple ⊢M conv nf
  progress (⊢⟨⟩ nf ⊢M conv) | inj₁ (Vs simple) | inj₁ app =
    inj₁ (V⟨⟩ simple nf app)
  progress (⊢⟨⟩ nf ⊢M conv) | inj₁ (Vs simple)
    | inj₂ (_ , lit , base-eq) = inj₂ (_ , _ , Const lit base-eq)
