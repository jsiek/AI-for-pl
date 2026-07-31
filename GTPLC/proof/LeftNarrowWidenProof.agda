module proof.LeftNarrowWidenProof where

-- File Charter:
--   * Proves the administrative and inert Left Narrowing/Widening cases.
--   * Uses one-context cast evidence directly.
--   * Uses endpoint matching instead of coercion duality or equations.
--   * Leaves the active tag, seal, and instantiation cases open.

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)

open import Coercions
open import Terms
open import Reduction
open import NarrowWiden
open import EnvironmentNarrowing using ([]ᵍ)
open import TermNarrowing
open import proof.LeftNarrowWiden

------------------------------------------------------------------------
-- Left Narrowing
------------------------------------------------------------------------

left-narrowing : LeftNarrowing
left-narrowing {V = V} {σ = σ} {r = r}
    {d⊒ = idᵃ a hA} vV vV′ V⊒V′ eq =
  (keep ∷ []) , V ,
  ↠-step (pure-step (β-id vV)) ↠-refl ,
  vV , σ , r , V⊒V′
left-narrowing {V = V} {d = c ↦ d} {σ = σ} {p = p}
    {d⊒ = c⊑ ↦ d⊒} vV vV′ V⊒V′ eq =
  [] , V ⟨ c ↦ d ⟩ , ↠-refl , (vV ⟨ c ↦ d ⟩) ,
  σ , p ,
  castⁿ⊒ {s⦂ = c⊑ ↦ d⊒} V⊒V′ eq
left-narrowing {V = V} {d = `∀ c} {σ = σ} {p = p}
    {d⊒ = ∀ⁿ c⊒} vV vV′ V⊒V′ eq =
  [] , V ⟨ `∀ c ⟩ , ↠-refl , (vV ⟨ `∀ c ⟩) ,
  σ , p ,
  castⁿ⊒ {s⦂ = ∀ⁿ c⊒} V⊒V′ eq
left-narrowing
    {d⊒ = untag G hG allowed G꞉B}
    vV vV′ V⊒V′ eq =
  {!!}
left-narrowing
    {d⊒ = untag-seq G hG allowed G꞉A c⊒ A≢B}
    vV vV′ V⊒V′ eq =
  {!!}
left-narrowing {V = V} {d = seal X} {σ = σ} {p = p}
    {d⊒ = seal X<Δ hA X,A∈Σ allowed}
    vV vV′ V⊒V′ eq =
  [] , V ⟨ seal X ⟩ , ↠-refl , (vV ⟨ seal X ⟩) ,
  σ , p ,
  castⁿ⊒ {s⦂ = seal X<Δ hA X,A∈Σ allowed} V⊒V′ eq
left-narrowing
    {d⊒ = seal-seq c⊒ X<Δ X,B∈Σ allowed A≢B}
    vV vV′ V⊒V′ eq =
  {!!}
left-narrowing {V = V} {d = gen c} {σ = σ} {p = p}
    {d⊒ = gen nonvarA zero∈A hB c⊒ B≢★}
    vV vV′ V⊒V′ eq =
  [] , V ⟨ gen c ⟩ , ↠-refl , (vV ⟨ gen c ⟩) ,
  σ , p ,
  castⁿ⊒
    {s⦂ = gen nonvarA zero∈A hB c⊒ B≢★}
    V⊒V′ eq

------------------------------------------------------------------------
-- Left Widening
------------------------------------------------------------------------

left-widening : LeftWidening
left-widening {V = V} {σ = σ} {p = p}
    {u⊑ = idᵃ a hA} vV vV′ V⊒V′ eq =
  (keep ∷ []) , V ,
  ↠-step (pure-step (β-id vV)) ↠-refl ,
  vV , σ , p , V⊒V′
left-widening {V = V} {u = c ↦ d} {σ = σ} {r = r}
    {u⊑ = c⊒ ↦ d⊑} vV vV′ V⊒V′ eq =
  [] , V ⟨ c ↦ d ⟩ , ↠-refl , (vV ⟨ c ↦ d ⟩) ,
  σ , r ,
  castʷ⊒ {s⦂ = c⊒ ↦ d⊑} V⊒V′ eq
left-widening {V = V} {u = `∀ c} {σ = σ} {r = r}
    {u⊑ = ∀ʷ c⊑} vV vV′ V⊒V′ eq =
  [] , V ⟨ `∀ c ⟩ , ↠-refl , (vV ⟨ `∀ c ⟩) ,
  σ , r ,
  castʷ⊒ {s⦂ = ∀ʷ c⊑} V⊒V′ eq
left-widening {V = V} {u = G !} {σ = σ} {r = r}
    {u⊑ = tag G hG allowed G꞉A} vV vV′ V⊒V′ eq =
  [] , V ⟨ G ! ⟩ , ↠-refl , (vV ⟨ G ! ⟩) ,
  σ , r ,
  castʷ⊒ {s⦂ = tag G hG allowed G꞉A} V⊒V′ eq
left-widening
    {u⊑ = tag-seq G c⊑ hG allowed G꞉B A≢B}
    vV vV′ V⊒V′ eq =
  {!!}
left-widening
    {u⊑ = unseal X<Δ hA X,A∈Σ allowed}
    vV vV′ V⊒V′ eq =
  {!!}
left-widening
    {u⊑ = unseal-seq X<Δ X,A∈Σ allowed c⊑ A≢B}
    vV vV′ V⊒V′ eq =
  {!!}
left-widening
    {u⊑ = inst nonvarA zero∈A hB c⊑ B≢★}
    vV vV′ V⊒V′ eq =
  {!!}
