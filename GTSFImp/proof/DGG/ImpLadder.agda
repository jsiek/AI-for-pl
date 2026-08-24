module proof.DGG.ImpLadder where

-- File Charter:
--   * Renders a typed cast-term-imprecision derivation as an outside-in,
--     seven-column ladder, preceded by its world snapshot.
--   * Shows only the syntax contributed by each derivation node; `□` marks a
--     child and `─` marks a silent side of a one-sided rule.
--   * Reserves `♯`-prefixed names for generated term binders, parallel to the
--     `♭`-prefixed type-binder namespace used by WorldSnapshot; supplied name
--     functions must never produce names in either reserved namespace.
--   * Derives recursive type-name suppliers from the endpoint and center
--     embeddings that change their scope sizes.
--   * Uses WorldSnapshot's unprimed default type names for source/center
--     supplies and its primed default type names for the target supply.
--   * Pads columns by character count; the table's built-in alphabet has no
--     two-column glyphs.  The unpadded WorldSnapshot line retains its own type
--     syntax.
--   * Provides a display-only obstruction row whose cost cell marks missing
--     rule evidence with `?`; it is not a partial CTI judgment or action.
--   * Traverses the current complete-context CTI directly and keeps no
--     compatibility-world or archived-constructor rendering path.

open import Data.Bool using (false; true)
open import Data.List using (List; []; _∷_; map)
import Data.List as List
open import Data.Nat using (ℕ; zero; suc; _∸_; _⊔_)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_; length)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; trans)

open import Types
open import Consistency using (Env∼; _⊢_∼_; toRenameᵗ)
open import Conversion using
  (Conv↑; Conv↓; unseal; _↦↑_; `∀↑_; id↑; seal; _↦↓_;
   `∀↓_; id↓)
import Imprecision as I
open import Primitives using
  (Const; Prim; κℕ; κ𝔹; addℕ; and𝔹)
open import CastTerms using
  (Ctx; Δᵉ; Term; Var; `_ ; ƛ_; _·_; Λ_; _⦂∀_[_]; $; _⊕[_]_; _⟨_⟩;
   _↑_; _↓_; blame)
import proof.DGG.CastTermImprecision as CTI2
open CTI2 using (_⊢²_⊑_∶_)
open import proof.DGG.World
import proof.DGG.WorldSnapshot as Snapshot

------------------------------------------------------------------------
-- Names and syntax fragments
------------------------------------------------------------------------

TyNameSupply : Set
TyNameSupply = ∀ {Δ} → TyVar Δ → String

private

  extendTyName : ∀ {Δ}
    → (TyVar Δ → String)
    → String
    → TyVar (suc Δ)
    → String
  extendTyName name binder Fin.zero = binder
  extendTyName name binder (Fin.suc X) = name X

  showTyAt : ∀ {Δ} → ℕ → (TyVar Δ → String) → Ty Δ → String
  showTyAt depth name (＇ X) = name X
  showTyAt depth name (‵ `ℕ) = "ℕ"
  showTyAt depth name (‵ `𝔹) = "𝔹"
  showTyAt depth name ★ = "★"
  showTyAt depth name (A ⇒ B) =
    "(" ++ showTyAt depth name A ++ " ⇒ " ++ showTyAt depth name B ++ ")"
  showTyAt depth name (`∀ A) =
    "∀ " ++ showTyAt (suc depth)
      (extendTyName name ("♭" ++ show depth)) A

  showTy : ∀ {Δ} → ℕ → (TyVar Δ → String) → Ty Δ → String
  showTy = showTyAt

defaultTermName : Var → String
defaultTermName x = "x" ++ show x

extendTermName : (Var → String) → String → Var → String
extendTermName name binder zero = binder
extendTermName name binder (suc x) = name x

showBase : Base → String
showBase `ℕ = "ℕ"
showBase `𝔹 = "𝔹"

showConst : Const → String
showConst (κℕ n) = show n
showConst (κ𝔹 false) = "false"
showConst (κ𝔹 true) = "true"

showPrim : Prim → String
showPrim addℕ = "+"
showPrim and𝔹 = "∧"

castLayer : ∀ {Δ μ A B}
  → ℕ
  → (TyVar Δ → String)
  → μ ⊢ A ∼ B
  → String
castLayer {A = A} {B = B} depth name c =
  "⟨ " ++ showTy depth name A ++ "↦" ++ showTy depth name B ++ " ⟩"

revealLayer : ∀ {Δ A B}
  → (TyVar Δ → String)
  → Conv↑ Δ A B
  → String
revealLayer name (unseal X R) = "↑ unseal " ++ name X
revealLayer name (seal X R ↦↑ unseal Y S) =
  "↑ unseal " ++ name Y ++ " ⇒-rev"
revealLayer name (c ↦↑ d) = "↑ ⇒-rev"
revealLayer name (`∀↑ c) = "↑ ∀-rev"
revealLayer name (id↑ A) = "↑ id"

concealLayer : ∀ {Δ A B}
  → (TyVar Δ → String)
  → Conv↓ Δ A B
  → String
concealLayer name (seal X R) = "↓ seal " ++ name X
concealLayer name (c ↦↓ seal X R) = "↓ seal " ++ name X
concealLayer name (c ↦↓ d) = "↓ ⇒-con"
concealLayer name (`∀↓ c) = "↓ ∀-con"
concealLayer name (id↓ A) = "↓ id"

showTerm : ∀ {Δ}
  → ℕ
  → ℕ
  → (TyVar Δ → String)
  → (Var → String)
  → Term Δ
  → String
showTerm termDepth tyDepth tyName xName (` x) = xName x
showTerm termDepth tyDepth tyName xName (ƛ M) =
  let binder = "♯" ++ show termDepth in
  "λ" ++ binder ++ ". " ++
  showTerm (suc termDepth) tyDepth tyName
    (extendTermName xName binder) M
showTerm termDepth tyDepth tyName xName (L · M) =
  "(" ++ showTerm termDepth tyDepth tyName xName L ++ " · " ++
  showTerm termDepth tyDepth tyName xName M ++ ")"
showTerm termDepth tyDepth tyName xName (Λ M) =
  let binder = "♭" ++ show tyDepth in
  "Λ" ++ showTerm termDepth (suc tyDepth)
    (extendTyName tyName binder) xName M
showTerm termDepth tyDepth tyName xName (M ⦂∀ C [ A ]) =
  showTerm termDepth tyDepth tyName xName M ++ " [ " ++
  showTy tyDepth tyName A ++ " ]"
showTerm termDepth tyDepth tyName xName ($ κ) = showConst κ
showTerm termDepth tyDepth tyName xName (L ⊕[ op ] M) =
  "(" ++ showTerm termDepth tyDepth tyName xName L ++ " " ++
  showPrim op ++ " " ++
  showTerm termDepth tyDepth tyName xName M ++ ")"
showTerm termDepth tyDepth tyName xName (M ⟨ c ⟩) =
  showTerm termDepth tyDepth tyName xName M ++ " " ++
  castLayer tyDepth tyName c
showTerm termDepth tyDepth tyName xName (M ↑ c) =
  showTerm termDepth tyDepth tyName xName M ++ " " ++ revealLayer tyName c
showTerm termDepth tyDepth tyName xName (M ↓ c) =
  showTerm termDepth tyDepth tyName xName M ++ " " ++ concealLayer tyName c
showTerm termDepth tyDepth tyName xName blame = "blame"

------------------------------------------------------------------------
-- Center-comparison costs
------------------------------------------------------------------------

private

  showCostAt : ∀ {Δ : TyCtx} {μ : I.ImpEnv Δ} {A B : Ty Δ}
    → ℕ
    → (TyVar Δ → String)
    → μ I.⊢ A ⊑ B
    → String
  showCostAt depth name I.★⊑★ = "★⊑★"
  showCostAt depth name (I.ι⊑ι {ι = ι}) =
    showBase ι ++ "⊑" ++ showBase ι
  showCostAt depth name (I.X⊑X {X = X}) = name X ++ " ≈ " ++ name X
  showCostAt depth name (I.⇒⊑⇒ p q) =
    showCostAt depth name p ++ ", " ++ showCostAt depth name q
  showCostAt depth name (I.∀⊑∀ p) =
    "∀(" ++ showCostAt (suc depth)
      (extendTyName name ("♭" ++ show depth)) p ++ ")"
  showCostAt depth name (I.⇒⊑★ p q) =
    showCostAt depth name p ++ ", " ++ showCostAt depth name q
  showCostAt depth name I.ι⊑★ = "ι⊑★"
  showCostAt depth name (I.X⊑★ {X = X} eq) =
    "mark X⊑★ at " ++ name X
  showCostAt depth name (I.∀⊑ Anv occurs p) =
    "∀⊑(" ++ showCostAt (suc depth)
      (extendTyName name ("♭" ++ show depth)) p ++ ")"
  showCostAt depth name I.∀★⊑★ = "∀★⊑★"
  showCostAt depth name (I.∀⊑★ Ans p) =
    "∀⊑★(" ++ showCostAt (suc depth)
      (extendTyName name ("♭" ++ show depth)) p ++ ")"
  showCostAt depth name I.bot-elim = "⊥-elim"
  showCostAt depth name I.bot⊑★ = "⊥⊑★"

showCost : ∀ {Δ : TyCtx} {μ : I.ImpEnv Δ} {A B : Ty Δ}
  → ℕ
  → (TyVar Δ → String)
  → μ I.⊢ A ⊑ B
  → String
showCost = showCostAt

addCost : String → String → String
addCost cost "" = cost
addCost cost extra = cost ++ " + " ++ extra

------------------------------------------------------------------------
-- Rows and aligned table rendering
------------------------------------------------------------------------

record Row : Set where
  constructor row
  field
    source : String
    sourceTy : String
    sourceCenterTy : String
    costs : String
    targetCenterTy : String
    targetTy : String
    target : String

open Row

header : Row
header = row "source term" "A" "ηᴸA" "⊑ costs" "ηᴿB" "B" "target term"

makeRow : ∀ {Γᴸ Γᴿ : Ctx} {W : Γᴸ ⊑ᶜ Γᴿ}
    {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
  → (TyVar (Δᵉ Γᴸ) → String)
  → (TyVar (Δᵉ Γᴿ) → String)
  → (TyVar (centerᶜ W) → String)
  → ℕ
  → String
  → String
  → String
  → A ⊑ᵀ⟨ W ⟩ B
  → String
  → Row
makeRow {W = W} {A = A} {B = B}
    nameᴸ nameᴿ nameᶜ tyDepth prefix source target p extra =
  row (prefix ++ source)
    (showTy tyDepth nameᴸ A)
    (showTy tyDepth nameᶜ
      (renameᵗ (toRenameᵗ (ηᴸᶜ W)) A))
    (addCost (showCost tyDepth nameᶜ p) extra)
    (showTy tyDepth nameᶜ
      (renameᵗ (toRenameᵗ (ηᴿᶜ W)) B))
    (showTy tyDepth nameᴿ B)
    target

record Widths : Set where
  constructor widths
  field
    sourceWidth : ℕ
    sourceTyWidth : ℕ
    sourceCenterTyWidth : ℕ
    costsWidth : ℕ
    targetCenterTyWidth : ℕ
    targetTyWidth : ℕ
    targetWidth : ℕ

open Widths

zeroWidths : Widths
zeroWidths = widths 0 0 0 0 0 0 0

includeRow : Row → Widths → Widths
includeRow r w =
  widths
    (length (source r) ⊔ sourceWidth w)
    (length (sourceTy r) ⊔ sourceTyWidth w)
    (length (sourceCenterTy r) ⊔ sourceCenterTyWidth w)
    (length (costs r) ⊔ costsWidth w)
    (length (targetCenterTy r) ⊔ targetCenterTyWidth w)
    (length (targetTy r) ⊔ targetTyWidth w)
    (length (target r) ⊔ targetWidth w)

tableWidths : List Row → Widths
tableWidths [] = zeroWidths
tableWidths (r ∷ rs) = includeRow r (tableWidths rs)

spaces : ℕ → String
spaces zero = ""
spaces (suc n) = " " ++ spaces n

dashes : ℕ → String
dashes zero = ""
dashes (suc n) = "─" ++ dashes n

pad : ℕ → String → String
pad width value = value ++ spaces (width ∸ length value)

renderRow : Widths → Row → String
renderRow w r =
  pad (sourceWidth w) (source r) ++ "  " ++
  pad (sourceTyWidth w) (sourceTy r) ++ "  " ++
  pad (sourceCenterTyWidth w) (sourceCenterTy r) ++ "  " ++
  pad (costsWidth w) (costs r) ++ "  " ++
  pad (targetCenterTyWidth w) (targetCenterTy r) ++ "  " ++
  pad (targetTyWidth w) (targetTy r) ++ "  " ++ target r

separator : Widths → String
separator w =
  dashes (sourceWidth w) ++ "  " ++
  dashes (sourceTyWidth w) ++ "  " ++
  dashes (sourceCenterTyWidth w) ++ "  " ++
  dashes (costsWidth w) ++ "  " ++
  dashes (targetCenterTyWidth w) ++ "  " ++
  dashes (targetTyWidth w) ++ "  " ++ dashes (targetWidth w)

joinLines : List String → String
joinLines [] = ""
joinLines (line ∷ []) = line
joinLines (line ∷ next ∷ lines) =
  line ++ "\n" ++ joinLines (next ∷ lines)

renderTableWith : Widths → List Row → String
renderTableWith w rows =
  renderRow w header ++ "\n" ++ separator w ++ "\n" ++
  joinLines (map (renderRow w) rows)

renderTable : List Row → String
renderTable rows = renderTableWith (tableWidths (header ∷ rows)) rows

obstructionRow : String → String → String → String → String → String
  → String → String → Row
obstructionRow source sourceTy sourceCenterTy knownCost obstruction
    targetCenterTy targetTy target =
  row source sourceTy sourceCenterTy
    (knownCost ++ " + ? " ++ obstruction)
    targetCenterTy targetTy target

------------------------------------------------------------------------
-- Outside-in derivation traversal
------------------------------------------------------------------------

ladderRows : ∀ {Γᴸ Γᴿ : Ctx} {W : Γᴸ ⊑ᶜ Γᴿ}
  → (TyVar (Δᵉ Γᴸ) → String)
  → (TyVar (Δᵉ Γᴿ) → String)
  → (TyVar (centerᶜ W) → String)
  → ℕ → ℕ → (Var → String) → String → String
  → ∀ {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
      {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
      {p : A ⊑ᵀ⟨ W ⟩ B}
  → W ⊢² M ⊑ M′ ∶ p
  → List Row
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.x⊑x² {x = x} sourceMember targetMember) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix (xName x) (xName x) p "" ∷ []
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.ƛ⊑ƛ² premise) =
  let binder = "♯" ++ show termDepth in
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix ("λ" ++ binder ++ ". □")
      ("λ" ++ binder ++ ". □") p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ (suc termDepth) tyDepth
      (extendTermName xName binder) childPrefix childPrefix premise
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.·⊑·² function argument) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix
      "□₁ · □₂" "□₁ · □₂" p "" ∷
    (ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
       (childPrefix ++ "├ ") (childPrefix ++ "│ ") function
     List.++
     ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
       (childPrefix ++ "└ ") (childPrefix ++ "  ") argument)
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.Λ⊑Λ² v v′ premise q) =
  let binder = "♭" ++ show tyDepth in
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix "Λ□" "Λ□" p "" ∷
    ladderRows (extendTyName nameᴸ binder)
      (extendTyName nameᴿ binder)
      (extendTyName nameᶜ binder)
      termDepth (suc tyDepth) xName childPrefix childPrefix premise
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.Λ⊑² Anv occurs v targetTyping premise q) =
  let binder = "♭" ++ show tyDepth in
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix "Λ□" "─" p "" ∷
    ladderRows (extendTyName nameᴸ binder) nameᴿ
      (extendTyName nameᶜ binder)
      termDepth (suc tyDepth) xName childPrefix childPrefix premise
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.•⊑•² {A = A} {A′ = A′} p∀ premise q r) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix
      ("□ [ " ++ showTy tyDepth nameᴸ A ++ " ]")
      ("□ [ " ++ showTy tyDepth nameᴿ A′ ++ " ]") p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
      childPrefix childPrefix premise
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.•⊑² {A = A} p∀ premise q r) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix
      ("□ [ " ++ showTy tyDepth nameᴸ A ++ " ]") "─" p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
      childPrefix childPrefix premise
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.κ⊑κ² κ q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix (showConst κ) (showConst κ) p "" ∷ []
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.cast⊑cast² c c′ premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix
      ("□ " ++ castLayer tyDepth nameᴸ c)
      ("□ " ++ castLayer tyDepth nameᴿ c′) p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
      childPrefix childPrefix premise
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.⊑cast² c′ premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix "─"
      ("□ " ++ castLayer tyDepth nameᴿ c′)
      p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
      childPrefix childPrefix premise
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.⊑reveal-identity {c′ = c′}
      typed pos≡absent premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix "─" ("□ " ++ revealLayer nameᴿ c′)
      p "generator absent" ∷
    ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
      childPrefix childPrefix premise
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.⊑conceal-identity {c′ = c′}
      typed pos≡absent premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix "─" ("□ " ++ concealLayer nameᴿ c′)
      p "generator absent" ∷
    ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
      childPrefix childPrefix premise
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.cast⊑² c premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix
      ("□ " ++ castLayer tyDepth nameᴸ c) "─"
      p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
      childPrefix childPrefix premise
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.reveal⊑-identity {c = c} typed pos≡absent premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix ("□ " ++ revealLayer nameᴸ c) "─"
      p "generator absent" ∷
    ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
      childPrefix childPrefix premise
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.reveal⊑-only² {c = c} typed pos≢absent mark disaligned
      represented premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix ("□ " ++ revealLayer nameᴸ c) "─"
      p "target unoccupied" ∷
    ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
      childPrefix childPrefix premise
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.conceal⊑-identity {c = c} typed pos≡absent premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix ("□ " ++ concealLayer nameᴸ c) "─"
      p "generator absent" ∷
    ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
      childPrefix childPrefix premise
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.conceal⊑-only² {c = c} typed pos≢absent mark disaligned
      represented premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix ("□ " ++ concealLayer nameᴸ c) "─"
      p "target unoccupied" ∷
    ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
      childPrefix childPrefix premise
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.reveal⊑reveal² {c = c} {c′ = c′}
      typed typed′ positions aligned represented premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix ("□ " ++ revealLayer nameᴸ c)
      ("□ " ++ revealLayer nameᴿ c′) p "matched reveal partner" ∷
    ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
      childPrefix childPrefix premise
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.conceal⊑conceal² {c = c} {c′ = c′}
      typed typed′ positions aligned represented premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix ("□ " ++ concealLayer nameᴸ c)
      ("□ " ++ concealLayer nameᴿ c′) p "matched conceal partner" ∷
    ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
      childPrefix childPrefix premise
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.⊑reveal-rebase² {c′ = c′}
      typed pos≢absent ok represented premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix "─"
      ("□ " ++ revealLayer nameᴿ c′) p "source rebase" ∷
    ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
      childPrefix childPrefix premise
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.⊑conceal-rebase² {c′ = c′}
      typed pos≢absent ok represented premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix "─"
      ("□ " ++ concealLayer nameᴿ c′) p "source rebase" ∷
    ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
      childPrefix childPrefix premise
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix
    {M′ = M′} {A = outA} {B = outB} {p = p}
    (CTI2.blame⊑² targetTyping q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix "blame"
    (showTerm termDepth tyDepth nameᴿ xName M′) p "" ∷ []
ladderRows {W = W} nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
    prefix childPrefix {A = outA} {B = outB} {p = p}
    (CTI2.⊕⊑⊕² op left right q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ tyDepth prefix
      ("□₁ " ++ showPrim op ++ " □₂")
      ("□₁ " ++ showPrim op ++ " □₂") p "" ∷
    (ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
       (childPrefix ++ "├ ") (childPrefix ++ "│ ") left
     List.++
     ladderRows nameᴸ nameᴿ nameᶜ termDepth tyDepth xName
       (childPrefix ++ "└ ") (childPrefix ++ "  ") right)

------------------------------------------------------------------------
-- Public printers
------------------------------------------------------------------------

impLadder : TyNameSupply → TyNameSupply → TyNameSupply → (Var → String)
  → ∀ {Γᴸ Γᴿ : Ctx} {W : Γᴸ ⊑ᶜ Γᴿ}
      {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
      {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
      {p : A ⊑ᵀ⟨ W ⟩ B}
  → W ⊢² M ⊑ M′ ∶ p
  → String
impLadder nameᴸ nameᴿ nameᶜ xName {W = W} derivation =
  Snapshot.worldSnapshot nameᴸ nameᴿ W nameᶜ ++ "\n" ++
  renderTable
    (ladderRows nameᴸ nameᴿ nameᶜ zero zero xName "" "" derivation)

impLadderDefault : ∀ {Γᴸ Γᴿ : Ctx} {W : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
    {p : A ⊑ᵀ⟨ W ⟩ B}
  → W ⊢² M ⊑ M′ ∶ p
  → String
impLadderDefault =
  impLadder Snapshot.defaultName Snapshot.defaultNameᵗ Snapshot.defaultName
    defaultTermName
