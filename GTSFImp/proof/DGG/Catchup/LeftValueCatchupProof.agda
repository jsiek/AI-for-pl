module proof.DGG.Catchup.LeftValueCatchupProof where

-- File Charter:
--   * Develops the direct left value catch-up proof by induction on CTI.
--   * Is parameterized only by the separate source-cast induction.
--   * Keeps unfinished semantic cases as explicit interaction goals.
--   * Is listed in Makefile's IN_PROGRESS_PROOFS until every goal closes.

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
import CastTerms as CT
open import CastTerms using (Value; _《_》; _↑_; _↓_)
open import Reduction using ([]; _∷_; keep; ↠-refl)
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.Catchup.LeftSourceCastCatchupDef using
  (LeftSourceCastCatchupAt)
open import proof.DGG.Catchup.LeftSourceTypeAppCatchupDef using
  (LeftSourceTypeAppCatchupAt)
open import proof.DGG.Catchup.LeftValueCatchupDef using
  (LeftValueCatchupAt)
open import proof.DGG.WorldEvolutionSequence using
  ( append-left-keep
  ; evolutions-refl
  ; multi-⊑ᵀ
  )
open import proof.Reduction using
  ( _++χ_
  ; conceal-blame-↠
  ; reveal-blame-↠
  )


module _
    (source-cast-catchup : ∀ {fuel} → LeftSourceCastCatchupAt fuel)
    (source-type-app-catchup : ∀ {fuel}
      → LeftSourceTypeAppCatchupAt fuel)
  where

  left-value-catchup : ∀ {fuel} → LeftValueCatchupAt fuel
  left-value-catchup no-rebase (CTI.x⊑x² _ _) () bound

  left-value-catchup {γ = γ} {M = M} {p = p} no-rebase
      rel@(CTI.ƛ⊑ƛ² prem) vV′ bound =
    inj₁ (_ , _ , [] , M , γ , p , ↠-refl , CT.ƛ _ ,
      evolutions-refl , rel)

  left-value-catchup no-rebase (CTI.·⊑·² prem₁ prem₂) () bound

  left-value-catchup {γ = γ} {M = M} {p = p} no-rebase
      rel@(CTI.Λ⊑Λ² vV vV′ prem q) target-value bound =
    inj₁ (_ , _ , [] , M , γ , p , ↠-refl , CT.Λ vV ,
      evolutions-refl , rel)

  left-value-catchup {γ = γ} {M = M} {p = p} no-rebase
      rel@(CTI.Λ⊑² Anv zero∈A vV target⊢ prem q) vV′ bound =
    inj₁ (_ , _ , [] , M , γ , p , ↠-refl , CT.Λ vV ,
      evolutions-refl , rel)

  left-value-catchup no-rebase (CTI.•⊑•² p∀ prem q r) () bound

  left-value-catchup no-rebase (CTI.•⊑² p∀ prem q r) vV′ bound =
    source-type-app-catchup no-rebase prem vV′ bound

  left-value-catchup {γ = γ} {M = M} {p = p} no-rebase
      rel@(CTI.κ⊑κ² κ q) vV′ bound =
    inj₁ (_ , _ , [] , M , γ , p , ↠-refl , CT.$ κ ,
      evolutions-refl , rel)

  left-value-catchup no-rebase
      rel@(CTI.cast⊑cast² c c′ prem q) vV′ bound =
    source-cast-catchup no-rebase rel vV′ bound

  left-value-catchup no-rebase
      (CTI.⊑cast² c′ prem q) (vV′ 《 inert 》) bound
      with left-value-catchup no-rebase prem vV′ bound
  left-value-catchup no-rebase
      (CTI.⊑cast² c′ prem q) (vV′ 《 inert 》) bound
    | inj₂ blame-result = inj₂ blame-result
  left-value-catchup no-rebase
      (CTI.⊑cast² c′ prem q) (vV′ 《 inert 》) bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , V , γ′ , q′ , M↠V , vV , evol ,
         V⊑V′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , V , γ′ , multi-⊑ᵀ evol q ,
         M↠V , vV , evol ,
         CTI.⊑cast² c′ V⊑V′ (multi-⊑ᵀ evol q))

  left-value-catchup no-rebase
      (CTI.⊑reveal-identity c′⊢ absent prem q) (vV′ ↑ reveal) bound
      with left-value-catchup no-rebase prem vV′ bound
  left-value-catchup no-rebase
      (CTI.⊑reveal-identity c′⊢ absent prem q) (vV′ ↑ reveal) bound
    | inj₂ blame-result = inj₂ blame-result
  left-value-catchup no-rebase
      (CTI.⊑reveal-identity c′⊢ absent prem q) (vV′ ↑ reveal) bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , V , γ′ , q′ , M↠V , vV , evol ,
         V⊑V′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , V , γ′ , multi-⊑ᵀ evol q ,
         M↠V , vV , evol ,
         CTI.⊑reveal-identity c′⊢ absent V⊑V′ (multi-⊑ᵀ evol q))

  left-value-catchup no-rebase
      (CTI.⊑conceal-identity c′⊢ absent prem q) (vV′ ↓ conceal) bound
      with left-value-catchup no-rebase prem vV′ bound
  left-value-catchup no-rebase
      (CTI.⊑conceal-identity c′⊢ absent prem q) (vV′ ↓ conceal) bound
    | inj₂ blame-result = inj₂ blame-result
  left-value-catchup no-rebase
      (CTI.⊑conceal-identity c′⊢ absent prem q) (vV′ ↓ conceal) bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , V , γ′ , q′ , M↠V , vV , evol ,
         V⊑V′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , V , γ′ , multi-⊑ᵀ evol q ,
         M↠V , vV , evol ,
         CTI.⊑conceal-identity c′⊢ absent V⊑V′
           (multi-⊑ᵀ evol q))

  left-value-catchup no-rebase rel@(CTI.cast⊑² c prem q) vV′ bound =
    source-cast-catchup no-rebase rel vV′ bound

  left-value-catchup no-rebase
      (CTI.reveal⊑-identity {c = c} c⊢ absent prem q) vV′ bound
      with left-value-catchup no-rebase prem vV′ bound
  left-value-catchup no-rebase
      (CTI.reveal⊑-identity {c = c} c⊢ absent prem q) vV′ bound
    | inj₂ (Δᴸ′ , Σᴸ′ , χsᴸ , γ′ , M↠blame , evol) =
      inj₂
        (Δᴸ′ , Σᴸ′ , χsᴸ ++χ (keep ∷ []) , γ′ ,
         reveal-blame-↠ c M↠blame , append-left-keep evol)
  left-value-catchup no-rebase
      (CTI.reveal⊑-identity {c = c} c⊢ absent prem q) vV′ bound
    | inj₁ success = {! !}

  left-value-catchup no-rebase
      (CTI.reveal⊑-only² {c = c}
        c⊢ present mark free represented prem q)
      vV′ bound
      with left-value-catchup no-rebase prem vV′ bound
  left-value-catchup no-rebase
      (CTI.reveal⊑-only² {c = c}
        c⊢ present mark free represented prem q)
      vV′ bound
    | inj₂ (Δᴸ′ , Σᴸ′ , χsᴸ , γ′ , M↠blame , evol) =
      inj₂
        (Δᴸ′ , Σᴸ′ , χsᴸ ++χ (keep ∷ []) , γ′ ,
         reveal-blame-↠ c M↠blame , append-left-keep evol)
  left-value-catchup no-rebase
      (CTI.reveal⊑-only² {c = c}
        c⊢ present mark free represented prem q)
      vV′ bound
    | inj₁ success = {! !}

  left-value-catchup no-rebase
      (CTI.conceal⊑-identity {c = c} c⊢ absent prem q) vV′ bound
      with left-value-catchup no-rebase prem vV′ bound
  left-value-catchup no-rebase
      (CTI.conceal⊑-identity {c = c} c⊢ absent prem q) vV′ bound
    | inj₂ (Δᴸ′ , Σᴸ′ , χsᴸ , γ′ , M↠blame , evol) =
      inj₂
        (Δᴸ′ , Σᴸ′ , χsᴸ ++χ (keep ∷ []) , γ′ ,
         conceal-blame-↠ c M↠blame , append-left-keep evol)
  left-value-catchup no-rebase
      (CTI.conceal⊑-identity {c = c} c⊢ absent prem q) vV′ bound
    | inj₁ success = {! !}

  left-value-catchup no-rebase
      (CTI.conceal⊑-only² {c = c}
        c⊢ present mark free represented prem q)
      vV′ bound
      with left-value-catchup no-rebase prem vV′ bound
  left-value-catchup no-rebase
      (CTI.conceal⊑-only² {c = c}
        c⊢ present mark free represented prem q)
      vV′ bound
    | inj₂ (Δᴸ′ , Σᴸ′ , χsᴸ , γ′ , M↠blame , evol) =
      inj₂
        (Δᴸ′ , Σᴸ′ , χsᴸ ++χ (keep ∷ []) , γ′ ,
         conceal-blame-↠ c M↠blame , append-left-keep evol)
  left-value-catchup no-rebase
      (CTI.conceal⊑-only² {c = c}
        c⊢ present mark free represented prem q)
      vV′ bound
    | inj₁ success = {! !}

  left-value-catchup no-rebase
      (CTI.reveal⊑reveal² {c = c}
        c⊢ c′⊢ positions aligned represented prem q)
      (vV′ ↑ reveal) bound
      with left-value-catchup no-rebase prem vV′ bound
  left-value-catchup no-rebase
      (CTI.reveal⊑reveal² {c = c}
        c⊢ c′⊢ positions aligned represented prem q)
      (vV′ ↑ reveal) bound
    | inj₂ (Δᴸ′ , Σᴸ′ , χsᴸ , γ′ , M↠blame , evol) =
      inj₂
        (Δᴸ′ , Σᴸ′ , χsᴸ ++χ (keep ∷ []) , γ′ ,
         reveal-blame-↠ c M↠blame , append-left-keep evol)
  left-value-catchup no-rebase
      (CTI.reveal⊑reveal² {c = c}
        c⊢ c′⊢ positions aligned represented prem q)
      (vV′ ↑ reveal) bound
    | inj₁ success = {! !}

  left-value-catchup no-rebase
      (CTI.conceal⊑conceal² {c = c}
        c⊢ c′⊢ positions aligned represented prem q)
      (vV′ ↓ conceal) bound
      with left-value-catchup no-rebase prem vV′ bound
  left-value-catchup no-rebase
      (CTI.conceal⊑conceal² {c = c}
        c⊢ c′⊢ positions aligned represented prem q)
      (vV′ ↓ conceal) bound
    | inj₂ (Δᴸ′ , Σᴸ′ , χsᴸ , γ′ , M↠blame , evol) =
      inj₂
        (Δᴸ′ , Σᴸ′ , χsᴸ ++χ (keep ∷ []) , γ′ ,
         conceal-blame-↠ c M↠blame , append-left-keep evol)
  left-value-catchup no-rebase
      (CTI.conceal⊑conceal² {c = c}
        c⊢ c′⊢ positions aligned represented prem q)
      (vV′ ↓ conceal) bound
    | inj₁ success = {! !}

  -- The recursive premise is after one source rebase, so the public
  -- no-rebase induction hypothesis is not available.  This is a genuine
  -- pre-induction obligation, not a post-IH reconstruction case.
  left-value-catchup no-rebase
      (CTI.⊑reveal-rebase² c′⊢ present ok represented prem q)
      (vV′ ↑ reveal) bound = {! !}

  left-value-catchup ()
      (CTI.⊑conceal-rebase² c′⊢ present ok represented prem q)
      vV′ bound

  left-value-catchup {γ = γ} {M = M} no-rebase
      (CTI.blame⊑² target⊢ p) vV′ bound =
    inj₂ (_ , _ , [] , γ , ↠-refl , evolutions-refl)

  left-value-catchup no-rebase
      (CTI.⊕⊑⊕² op prem₁ prem₂ r) () bound
