module proof.DGG.WorldSnapshot where

-- File Charter:
--   * Renders DGG worlds as canonical one-line snapshots for proof notes.
--   * Shows each center variable's endpoint pivots, direct store entries, and
--     imprecision mark in center order.
--   * Pins the format on representative Example12Worlds and Examples2 worlds.

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (TyStore; store-empty; store-lift; store-bind)
open import Imprecision using (VarImp; X⊑X; X⊑★)
open import Consistency using (_↪ᵗ_; empty; keep; skip)
import proof.DGG.CtxImp as CTX
import proof.DGG.Example12Worlds as Ex12
import proof.DGG.Examples2 as Ex2

------------------------------------------------------------------------
-- Types and direct store entries
------------------------------------------------------------------------

private

  extendName : ∀ {Δ}
    → (TyVar Δ → String)
    → String
    → TyVar (suc Δ)
    → String
  extendName name binder Fin.zero = binder
  extendName name binder (Fin.suc X) = name X

  showTyAt : ∀ {Δ} → ℕ → (TyVar Δ → String) → Ty Δ → String
  showTyAt depth name (＇ X) = "＇" ++ name X
  showTyAt depth name (‵ `ℕ) = "ℕ"
  showTyAt depth name (‵ `𝔹) = "𝔹"
  showTyAt depth name ★ = "★"
  showTyAt depth name (A ⇒ B) =
    "(" ++ showTyAt depth name A ++ " ⇒ " ++ showTyAt depth name B ++ ")"
  showTyAt depth name (`∀ A) =
    "∀ " ++ showTyAt (suc depth) (extendName name ("b" ++ show depth)) A

showTy : ∀ {Δ} → (TyVar Δ → String) → Ty Δ → String
showTy = showTyAt zero

lookupStore : ∀ {Δ} → TyStore Δ → TyVar Δ → Ty Δ
lookupStore store-empty ()
lookupStore (store-lift Σ) Fin.zero = ＇ Fin.zero
lookupStore (store-lift Σ) (Fin.suc X) = ⇑ᵗ (lookupStore Σ X)
lookupStore (store-bind Σ A) Fin.zero = ⇑ᵗ A
lookupStore (store-bind Σ A) (Fin.suc X) = ⇑ᵗ (lookupStore Σ X)

------------------------------------------------------------------------
-- Center-indexed snapshots
------------------------------------------------------------------------

pivotAt : ∀ {Δᵉ Δ}
  → Δᵉ ↪ᵗ Δ
  → TyVar Δ
  → Maybe (TyVar Δᵉ)
pivotAt empty X = nothing
pivotAt (keep ρ) Fin.zero = just Fin.zero
pivotAt (keep ρ) (Fin.suc X) with pivotAt ρ X
pivotAt (keep ρ) (Fin.suc X) | just Y = just (Fin.suc Y)
pivotAt (keep ρ) (Fin.suc X) | nothing = nothing
pivotAt (skip ρ) Fin.zero = nothing
pivotAt (skip ρ) (Fin.suc X) = pivotAt ρ X

centerVars : (Δ : TyCtx) → List (TyVar Δ)
centerVars zero = []
centerVars (suc Δ) = Fin.zero ∷ map Fin.suc (centerVars Δ)

showMark : VarImp → String
showMark X⊑X = "X⊑X"
showMark X⊑★ = "X⊑★"

showEntry : ∀ {Δ}
  → (TyVar Δ → String)
  → TyStore Δ
  → Maybe (TyVar Δ)
  → String
showEntry name Σ nothing = "─"
showEntry name Σ (just X) =
  name X ++ "↦" ++ showTy name (lookupStore Σ X)

worldCell : ∀ {Δᴸ Δᴿ Δ}
  → (TyVar Δᴸ → String)
  → (TyVar Δᴿ → String)
  → (TyVar Δ → String)
  → CTX.World Δᴸ Δᴿ Δ
  → TyVar Δ
  → String
worldCell nameᴸ nameᴿ nameᶜ W X =
  nameᶜ X ++ ": " ++
  showEntry nameᴸ (CTX.sourceStoreʷ W) (pivotAt (CTX.ηᴸʷ W) X) ++
  " ⊑[" ++ showMark (CTX.impEnvʷ W X) ++ "] " ++
  showEntry nameᴿ (CTX.targetStoreʷ W) (pivotAt (CTX.ηᴿʷ W) X)

joinCells : List String → String
joinCells [] = ""
joinCells (cell ∷ []) = cell
joinCells (cell ∷ next ∷ cells) =
  cell ++ " │ " ++ joinCells (next ∷ cells)

worldSnapshot : ∀ {Δᴸ Δᴿ Δ}
  → (nameᴸ : TyVar Δᴸ → String)
  → (nameᴿ : TyVar Δᴿ → String)
  → (nameᶜ : TyVar Δ → String)
  → CTX.World Δᴸ Δᴿ Δ
  → String
worldSnapshot {Δ = Δ} nameᴸ nameᴿ nameᶜ W =
  "⟨" ++
  joinCells (map (worldCell nameᴸ nameᴿ nameᶜ W) (centerVars Δ)) ++
  "⟩"

defaultName : ∀ {Δ} → TyVar Δ → String
defaultName X = "x" ++ show (Fin.toℕ X)

worldSnapshotDefault : ∀ {Δᴸ Δᴿ Δ}
  → CTX.World Δᴸ Δᴿ Δ
  → String
worldSnapshotDefault = worldSnapshot defaultName defaultName defaultName

------------------------------------------------------------------------
-- Pinned fixture snapshots
------------------------------------------------------------------------

example12-world-X-snapshot :
  worldSnapshotDefault Ex12.example12-world-X ≡
    "⟨x0: x0↦ℕ ⊑[X⊑★] x0↦ℕ │ " ++
    "x1: ─ ⊑[X⊑★] x1↦＇x2 │ " ++
    "x2: ─ ⊑[X⊑★] x2↦★⟩"
example12-world-X-snapshot = refl

examples2-left-path-world₃-snapshot :
  worldSnapshotDefault Ex2.left-path-world₃ ≡
    "⟨x0: x0↦ℕ ⊑[X⊑★] x0↦＇x1 │ " ++
    "x1: x1↦＇x2 ⊑[X⊑X] ─ │ " ++
    "x2: x2↦★ ⊑[X⊑★] x1↦★⟩"
examples2-left-path-world₃-snapshot = refl

nested-∀-store-entry-snapshot :
  showEntry defaultName
    (store-bind store-empty
      (`∀ (`∀ (＇ Fin.zero ⇒ ＇ (Fin.suc Fin.zero)))))
    (just Fin.zero) ≡
      "x0↦∀ ∀ (＇b1 ⇒ ＇b0)"
nested-∀-store-entry-snapshot = refl
