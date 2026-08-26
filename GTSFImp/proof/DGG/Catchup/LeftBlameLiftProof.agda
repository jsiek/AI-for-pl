module proof.DGG.Catchup.LeftBlameLiftProof where

-- File Charter:
--   * Proves the source blame-lift workers used by left catch-up packages.
--   * Lifts source-blame traces through source cast, reveal, and conceal
--     wrappers and appends the corresponding pure blame step.
--   * Mirrors the boundary-stack blame propagation pattern without changing
--     CTI2 or the public catch-up surfaces.

open import Data.Product using (_,_)

open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (Conv↑; Conv↓)
open import CastTerms using (Term; blame; _⟨_⟩; _↑_; _↓_)
import Reduction as R
open import Reduction using
  ( StoreChanges
  ; keep
  ; _∷_
  ; _—↠[_]_
  ; _—↠[_]⟨_⟩_
  ; _—→[_]⟨_⟩_
  ; _∎[]
  ; pure-step
  ; blame-⟨⟩
  ; blame-reveal
  ; blame-conceal
  )
open import Types using (Ty)
open import proof.DGG.Catchup.LeftSourceOperationsDef
  using (LeftBlameCastLiftAt; LeftBlameConcealLiftAt; LeftBlameRevealLiftAt)
open import proof.DGG.Parked.ParkedEvolveCompositionProof
  using (compose-parked-evolve)
open import proof.DGG.Parked.ParkedWorldDef
  using (evolve-keepᴸ; evolve-refl)
open import proof.Reduction
  using
    ( _++χ_
    ; applyConceals
    ; applyReveals
    ; cast-↠
    ; composeReduction
    ; conceal-↠
    ; reveal-↠
    )


left-blame-cast-lift-at : LeftBlameCastLiftAt
left-blame-cast-lift-at {M = M} {χsᴸ = χsᴸ} c M↠blame evol =
  _ , χsᴸ ++χ (keep ∷ R.[]) , _ , _ ,
  composeReduction
    (M ⟨ c ⟩
      —↠[ χsᴸ ]⟨ cast-↠ c M↠blame ⟩
     blame ⟨ R.applyConsistencies χsᴸ c ⟩ ∎[])
    (blame ⟨ R.applyConsistencies χsᴸ c ⟩
      —→[ keep ]⟨ pure-step blame-⟨⟩ ⟩
     blame ∎[]) ,
  compose-parked-evolve evol (evolve-keepᴸ evolve-refl)


left-blame-reveal-lift-at : LeftBlameRevealLiftAt
left-blame-reveal-lift-at {M = M} {χsᴸ = χsᴸ} c M↠blame evol =
  _ , χsᴸ ++χ (keep ∷ R.[]) , _ , _ ,
  composeReduction
    (M ↑ c
      —↠[ χsᴸ ]⟨ reveal-↠ c M↠blame ⟩
     blame ↑ applyReveals χsᴸ c ∎[])
    (blame ↑ applyReveals χsᴸ c
      —→[ keep ]⟨ pure-step blame-reveal ⟩
     blame ∎[]) ,
  compose-parked-evolve evol (evolve-keepᴸ evolve-refl)


left-blame-conceal-lift-at : LeftBlameConcealLiftAt
left-blame-conceal-lift-at {M = M} {χsᴸ = χsᴸ} c M↠blame evol =
  _ , χsᴸ ++χ (keep ∷ R.[]) , _ , _ ,
  composeReduction
    (M ↓ c
      —↠[ χsᴸ ]⟨ conceal-↠ c M↠blame ⟩
     blame ↓ applyConceals χsᴸ c ∎[])
    (blame ↓ applyConceals χsᴸ c
      —→[ keep ]⟨ pure-step blame-conceal ⟩
     blame ∎[]) ,
  compose-parked-evolve evol (evolve-keepᴸ evolve-refl)
