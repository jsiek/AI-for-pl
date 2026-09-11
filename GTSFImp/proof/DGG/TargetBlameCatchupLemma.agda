{-# OPTIONS --safe #-}

module proof.DGG.TargetBlameCatchupLemma where

-- File Charter:
--   * Proves source catch-up when the less precise target is blame.
--   * Proceeds directly by induction on canonical cast-term imprecision.
--   * Exports the closed proof `target-blame-catchup`.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Product using (_,_)

open import Types using (Ty; TyCtx)
open import CastTerms
open import Reduction using ([]; _∷_; keep; _∎[])
open import proof.DGG.CastTermImprecision
open import proof.DGG.TargetBlameCatchupDef
open import proof.DGG.World
open import proof.Reduction using
  (_++χ_; cast-blame-↠; conceal-blame-↠; reveal-blame-↠;
   typeApp-blame-↠)


TargetValueBlameExclusionᵀ : Set
TargetValueBlameExclusionᵀ = ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {V : Term (Δᵉ Γᴸ)} {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
    {p : A ⊑ᵀ⟨ γ ⟩ B}
  → Value V
  → γ ⊢² V ⊑ blame ∶ p
  → ⊥

target-value-blame-exclusion : TargetValueBlameExclusionᵀ
target-value-blame-exclusion (ƛ N) ()
target-value-blame-exclusion (Λ source-value)
    (Λ⊑² nonvar occurs source-value′ target⊢ related type-rel) =
  target-value-blame-exclusion source-value related
target-value-blame-exclusion ($ constant) ()
target-value-blame-exclusion (source-value 《 inert 》)
    (cast⊑² source-cast related type-rel) =
  target-value-blame-exclusion source-value related
target-value-blame-exclusion (source-value ↑ reveal-value)
    (reveal⊑-identity conversion position related type-rel) =
  target-value-blame-exclusion source-value related
target-value-blame-exclusion (source-value ↑ reveal-value)
    (reveal⊑-only² conversion position mark free represented
      related type-rel) =
  target-value-blame-exclusion source-value related
target-value-blame-exclusion (source-value ↓ conceal-value)
    (conceal⊑-identity conversion position related type-rel) =
  target-value-blame-exclusion source-value related
target-value-blame-exclusion (source-value ↓ conceal-value)
    (conceal⊑-only² conversion position mark free represented
      related type-rel) =
  target-value-blame-exclusion source-value related


target-blame-catchup : TargetBlameCatchupᵀ
target-blame-catchup
    (Λ⊑² nonvar occurs source-value target⊢ related type-rel) =
  ⊥-elim (target-value-blame-exclusion source-value related)
target-blame-catchup
    (•⊑² all-rel related type-rel result-rel)
    with target-blame-catchup related
target-blame-catchup
    (•⊑² all-rel related type-rel result-rel)
  | Δᴸ′ , χsᴸ , source-blame =
    Δᴸ′ , χsᴸ ++χ (keep ∷ []) , typeApp-blame-↠ source-blame
target-blame-catchup (cast⊑² source-cast related type-rel)
    with target-blame-catchup related
target-blame-catchup (cast⊑² source-cast related type-rel)
  | Δᴸ′ , χsᴸ , source-blame =
    Δᴸ′ , χsᴸ ++χ (keep ∷ []) ,
      cast-blame-↠ source-cast source-blame
target-blame-catchup
    (reveal⊑-identity {c = c} conversion position related type-rel)
    with target-blame-catchup related
target-blame-catchup
    (reveal⊑-identity {c = c} conversion position related type-rel)
  | Δᴸ′ , χsᴸ , source-blame =
    Δᴸ′ , χsᴸ ++χ (keep ∷ []) , reveal-blame-↠ c source-blame
target-blame-catchup
    (reveal⊑-only² {c = c} conversion position mark free represented
      related type-rel)
    with target-blame-catchup related
target-blame-catchup
    (reveal⊑-only² {c = c} conversion position mark free represented
      related type-rel)
  | Δᴸ′ , χsᴸ , source-blame =
    Δᴸ′ , χsᴸ ++χ (keep ∷ []) , reveal-blame-↠ c source-blame
target-blame-catchup
    (conceal⊑-identity {c = c} conversion position related type-rel)
    with target-blame-catchup related
target-blame-catchup
    (conceal⊑-identity {c = c} conversion position related type-rel)
  | Δᴸ′ , χsᴸ , source-blame =
    Δᴸ′ , χsᴸ ++χ (keep ∷ []) , conceal-blame-↠ c source-blame
target-blame-catchup
    (conceal⊑-only² {c = c} conversion position mark free represented
      related type-rel)
    with target-blame-catchup related
target-blame-catchup
    (conceal⊑-only² {c = c} conversion position mark free represented
      related type-rel)
  | Δᴸ′ , χsᴸ , source-blame =
    Δᴸ′ , χsᴸ ++χ (keep ∷ []) , conceal-blame-↠ c source-blame
target-blame-catchup (blame⊑² target⊢ type-rel) =
  _ , [] , (blame ∎[])
