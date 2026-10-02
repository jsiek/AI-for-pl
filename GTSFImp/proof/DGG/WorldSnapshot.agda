module proof.DGG.WorldSnapshot where

-- File Charter:
--   * Renders DGG worlds as canonical one-line snapshots for proof notes.
--   * Shows each center variable's endpoint pivots, direct store entries, and
--     imprecision mark in center order.
--   * Renders a nonempty derived open-frame stack as a separate optional line
--     using the same endpoint name supplies.
--   * Exports `defaultName` for unprimed source/center type variables and
--     `defaultNameᵗ` for primed target type variables.
--   * Names generated type binders with the first canonical `X`, `Y`, `Z`,
--     `X₁`, ... name after the variables already in scope.
--   * Renders the canonical complete-context World relation directly; there
--     is no compatibility-world rendering path.

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_; fromList; toList)
import Data.Fin as Fin
import Data.Fin.Properties as FinP
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore using (TyStore; store-empty; store-lift; store-bind)
open import Imprecision using (VarImp; X⊑X; X⊑★)
open import CastTerms using (Ctx; Δᵉ; Σᵉ)
open import proof.DGG.World

------------------------------------------------------------------------
-- Canonical names
------------------------------------------------------------------------

private

  subscriptDigit : Char → Char
  subscriptDigit '0' = '₀'
  subscriptDigit '1' = '₁'
  subscriptDigit '2' = '₂'
  subscriptDigit '3' = '₃'
  subscriptDigit '4' = '₄'
  subscriptDigit '5' = '₅'
  subscriptDigit '6' = '₆'
  subscriptDigit '7' = '₇'
  subscriptDigit '8' = '₈'
  subscriptDigit '9' = '₉'
  subscriptDigit c = c

subscript : ℕ → String
subscript n = fromList (map subscriptDigit (toList (show n)))

private

  defaultNameAt : ℕ → ℕ → String
  defaultNameAt zero zero = "X"
  defaultNameAt (suc group) zero = "X" ++ subscript (suc group)
  defaultNameAt zero (suc zero) = "Y"
  defaultNameAt (suc group) (suc zero) = "Y" ++ subscript (suc group)
  defaultNameAt zero (suc (suc zero)) = "Z"
  defaultNameAt (suc group) (suc (suc zero)) =
    "Z" ++ subscript (suc group)
  defaultNameAt group (suc (suc (suc index))) =
    defaultNameAt (suc group) index

canonicalTyName : ℕ → String
canonicalTyName = defaultNameAt zero

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
    "∀ " ++ showTyAt (suc depth)
      (extendName name (canonicalTyName depth)) A

showTy : ∀ {Δ} → (TyVar Δ → String) → Ty Δ → String
showTy {Δ} = showTyAt Δ

lookupStore : ∀ {Δ} → TyStore Δ → TyVar Δ → Ty Δ
lookupStore store-empty ()
lookupStore (store-lift Σ) Fin.zero = ＇ Fin.zero
lookupStore (store-lift Σ) (Fin.suc X) = ⇑ᵗ (lookupStore Σ X)
lookupStore (store-bind Σ A) Fin.zero = ⇑ᵗ A
lookupStore (store-bind Σ A) (Fin.suc X) = ⇑ᵗ (lookupStore Σ X)

------------------------------------------------------------------------
-- Center-indexed snapshots
------------------------------------------------------------------------

centerVars : (Δ : TyCtx) → List (TyVar Δ)
centerVars zero = []
centerVars (suc Δ) = Fin.zero ∷ map Fin.suc (centerVars Δ)

pivotAtFrom : ∀ {Δᵉ Δ}
  → List (TyVar Δᵉ)
  → Injectionᵗ Δᵉ Δ
  → TyVar Δ
  → Maybe (TyVar Δᵉ)
pivotAtFrom [] η X = nothing
pivotAtFrom (Y ∷ Ys) η X with FinP._≟_ (toRenameⁱ η Y) X
pivotAtFrom (Y ∷ Ys) η X | yes eq = just Y
pivotAtFrom (Y ∷ Ys) η X | no neq = pivotAtFrom Ys η X

pivotAt : ∀ {Δᵉ Δ}
  → Injectionᵗ Δᵉ Δ
  → TyVar Δ
  → Maybe (TyVar Δᵉ)
pivotAt {Δᵉ} η X = pivotAtFrom (centerVars Δᵉ) η X

showMark : VarImp → String
showMark X⊑X = "X⊑X"
showMark X⊑★ = "X⊑★"

showEntryAt : ∀ {Δ}
  → ℕ
  → (TyVar Δ → String)
  → TyStore Δ
  → Maybe (TyVar Δ)
  → String
showEntryAt depth name Σ nothing = "─"
showEntryAt depth name Σ (just X) =
  name X ++ "↦" ++ showTyAt depth name (lookupStore Σ X)

showEntry : ∀ {Δ}
  → (TyVar Δ → String)
  → TyStore Δ
  → Maybe (TyVar Δ)
  → String
showEntry {Δ} = showEntryAt Δ

worldCell : ∀ {Γᴸ Γᴿ : Ctx}
  → (TyVar (Δᵉ Γᴸ) → String)
  → (TyVar (Δᵉ Γᴿ) → String)
  → (W : Γᴸ ⊑ᶜ Γᴿ)
  → (TyVar (centerᶜ W) → String)
  → TyVar (centerᶜ W)
  → String
worldCell {Γᴸ} {Γᴿ} nameᴸ nameᴿ W nameᶜ X =
  nameᶜ X ++ ": " ++
  showEntryAt (centerᶜ W) nameᴸ (Σᵉ Γᴸ) (pivotAt (ηᴸᶜ W) X) ++
  " ⊑[" ++ showMark (marksᶜ W X) ++ "] " ++
  showEntryAt (centerᶜ W) nameᴿ (Σᵉ Γᴿ) (pivotAt (ηᴿᶜ W) X)

joinCells : List String → String
joinCells [] = ""
joinCells (cell ∷ []) = cell
joinCells (cell ∷ next ∷ cells) =
  cell ++ " │ " ++ joinCells (next ∷ cells)

worldSnapshot : ∀ {Γᴸ Γᴿ : Ctx}
  → (nameᴸ : TyVar (Δᵉ Γᴸ) → String)
  → (nameᴿ : TyVar (Δᵉ Γᴿ) → String)
  → (W : Γᴸ ⊑ᶜ Γᴿ)
  → (nameᶜ : TyVar (centerᶜ W) → String)
  → String
worldSnapshot nameᴸ nameᴿ W nameᶜ =
  "⟨" ++
  joinCells
    (map (worldCell nameᴸ nameᴿ W nameᶜ)
      (centerVars (centerᶜ W))) ++
  "⟩"

showOpenFrame : ∀ {Δᴸ Δᴿ}
  → (TyVar Δᴸ → String)
  → (TyVar Δᴿ → String)
  → RebaseFrameᶜ Δᴸ Δᴿ
  → String
showOpenFrame nameᴸ nameᴿ (Xᴸ ↔ᶜ Xᴿ) =
  nameᴸ Xᴸ ++ " ↔ " ++ nameᴿ Xᴿ

showOpenFrames : ∀ {Δᴸ Δᴿ}
  → (TyVar Δᴸ → String)
  → (TyVar Δᴿ → String)
  → OpenFramesᶜ Δᴸ Δᴿ
  → String
showOpenFrames nameᴸ nameᴿ [] = ""
showOpenFrames nameᴸ nameᴿ (frame ∷ []) =
  showOpenFrame nameᴸ nameᴿ frame
showOpenFrames nameᴸ nameᴿ (frame ∷ next ∷ frames) =
  showOpenFrame nameᴸ nameᴿ frame ++ ", " ++
    showOpenFrames nameᴸ nameᴿ (next ∷ frames)

openFramesLine : ∀ {Δᴸ Δᴿ}
  → (TyVar Δᴸ → String)
  → (TyVar Δᴿ → String)
  → OpenFramesᶜ Δᴸ Δᴿ
  → String
openFramesLine nameᴸ nameᴿ [] = ""
openFramesLine nameᴸ nameᴿ (frame ∷ frames) =
  "\nopenFramesᶜ γ = [" ++
    showOpenFrames nameᴸ nameᴿ (frame ∷ frames) ++ "]"

defaultName : ∀ {Δ} → TyVar Δ → String
defaultName X = canonicalTyName (Fin.toℕ X)

defaultNameᵗ : ∀ {Δ} → TyVar Δ → String
defaultNameᵗ X = defaultName X ++ "′"

worldSnapshotDefault : ∀ {Γᴸ Γᴿ : Ctx}
  → Γᴸ ⊑ᶜ Γᴿ
  → String
worldSnapshotDefault W =
  worldSnapshot defaultName defaultNameᵗ W defaultName

------------------------------------------------------------------------
-- Pinned fixture snapshots
------------------------------------------------------------------------

default-name-groups-pinned :
  defaultName (Fin.fromℕ 3) ++ " " ++
  defaultName (Fin.fromℕ 4) ++ " " ++
  defaultName (Fin.fromℕ 5) ++ " " ++
  defaultName (Fin.fromℕ 6) ++ " " ++
  defaultNameᵗ (Fin.fromℕ 30) ≡ "X₁ Y₁ Z₁ X₂ X₁₀′"
default-name-groups-pinned = refl

empty-world-snapshot : worldSnapshotDefault emptyᶜ ≡ "⟨⟩"
empty-world-snapshot = refl

nested-∀-store-entry-snapshot :
  showEntry defaultName
    (store-bind store-empty
      (`∀ (`∀ (＇ Fin.zero ⇒ ＇ (Fin.suc Fin.zero)))))
    (just Fin.zero) ≡
      "X↦∀ ∀ (＇Z ⇒ ＇Y)"
nested-∀-store-entry-snapshot = refl

outer-custom-name-fresh-binder-snapshot :
  showTy {Δ = suc zero} (λ _ → "b0")
    (`∀ (＇ Fin.zero ⇒ ＇ (Fin.suc Fin.zero))) ≡
      "∀ (＇Y ⇒ ＇b0)"
outer-custom-name-fresh-binder-snapshot = refl
