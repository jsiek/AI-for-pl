module proof.DGG.ImpLadder where

-- File Charter:
--   * Renders a typed cast-term-imprecision derivation as an outside-in,
--     seven-column ladder, preceded by its world snapshot.
--   * Shows only the syntax contributed by each derivation node; `□` marks a
--     child and `─` marks a silent side of a one-sided rule.
--   * Reserves `♯`-prefixed names for generated term binders, parallel to the
--     `♭`-prefixed type-binder namespace used by WorldSnapshot; supplied name
--     functions must never produce names in either reserved namespace.
--   * Uses polymorphic type-name suppliers because recursive derivation worlds
--     can change endpoint and center scope sizes.
--   * Pins a small lambda ladder and a live, data-bearing reconstruction of
--     Examples2's archived checkpoint-8 target-Z fragment; also exports the
--     whole-checkpoint printer at its intended judgment type.

open import Data.Bool using (false; true)
open import Data.List using (List; []; _∷_; map)
import Data.List as List
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _∸_; _⊔_)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_; length)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (store-empty)
open import Consistency using (Env∼; _⊢_∼_; toRenameᵗ)
import Consistency as C
open import Conversion using
  (Conv↑; Conv↓; unseal; _↦↑_; `∀↑_; id↑; seal; _↦↓_;
   `∀↓_; id↓)
import Conversion as Conv
import Imprecision as I
open import Primitives using
  (Const; Prim; κℕ; κ𝔹; addℕ; and𝔹)
open import CastTerms using
  (Term; Var; `_ ; ƛ_; _·_; Λ_; _⦂∀_[_]; $; _⊕[_]_; _⟨_⟩;
   _↑_; _↓_; blame)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open CTI2 using (_∣_⊢²_⊑_∶_)
open CTX using (_⊑ᵂ⟨_⟩_)
import proof.DGG.ExampleTerms as Ex
import proof.DGG.Examples2 as Ex2
import proof.DGG.WorldSnapshot as Snapshot

------------------------------------------------------------------------
-- Names and syntax fragments
------------------------------------------------------------------------

TyNameSupply : Set
TyNameSupply = ∀ {Δ} → TyVar Δ → String

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
  → (TyVar Δ → String)
  → μ ⊢ A ∼ B
  → String
castLayer {A = A} {B = B} name c =
  "⟨ " ++ Snapshot.showTy name A ++ "↦" ++
  Snapshot.showTy name B ++ " ⟩"

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
  → TyNameSupply
  → (Var → String)
  → Term Δ
  → String
showTerm depth tyName xName (` x) = "`" ++ xName x
showTerm depth tyName xName (ƛ M) =
  let binder = "♯" ++ show depth in
  "λ" ++ binder ++ ". " ++
  showTerm (suc depth) tyName (extendTermName xName binder) M
showTerm depth tyName xName (L · M) =
  "(" ++ showTerm depth tyName xName L ++ " · " ++
  showTerm depth tyName xName M ++ ")"
showTerm depth tyName xName (Λ M) =
  "Λ" ++ showTerm depth tyName xName M
showTerm depth tyName xName (M ⦂∀ C [ A ]) =
  showTerm depth tyName xName M ++ " [ " ++
  Snapshot.showTy tyName A ++ " ]"
showTerm depth tyName xName ($ κ) = showConst κ
showTerm depth tyName xName (L ⊕[ op ] M) =
  "(" ++ showTerm depth tyName xName L ++ " " ++ showPrim op ++ " " ++
  showTerm depth tyName xName M ++ ")"
showTerm depth tyName xName (M ⟨ c ⟩) =
  showTerm depth tyName xName M ++ " " ++ castLayer tyName c
showTerm depth tyName xName (M ↑ c) =
  showTerm depth tyName xName M ++ " " ++ revealLayer tyName c
showTerm depth tyName xName (M ↓ c) =
  showTerm depth tyName xName M ++ " " ++ concealLayer tyName c
showTerm depth tyName xName blame = "blame"

------------------------------------------------------------------------
-- Center-comparison costs and occupancy premises
------------------------------------------------------------------------

private

  extendTyName : ∀ {Δ}
    → (TyVar Δ → String)
    → String
    → TyVar (suc Δ)
    → String
  extendTyName name binder Fin.zero = binder
  extendTyName name binder (Fin.suc X) = name X

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
  → (TyVar Δ → String)
  → μ I.⊢ A ⊑ B
  → String
showCost = showCostAt zero

sourceConcealCost : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ} {M A A′ c Xᴿ? M′}
  → CTX.SourceConcealOK W M {A} {A′} c Xᴿ? M′
  → String
sourceConcealCost (CTX.seal-nonstar-unmatched-ok Ans no-target) =
  "NoTargetOccupantAtSource"
sourceConcealCost (CTX.seal-nonstar-name-protected-ok Ans aligned) =
  "matched-seal-name-partner"
sourceConcealCost CTX.fun-conceal-ok = ""
sourceConcealCost CTX.all-conceal-ok = ""
sourceConcealCost CTX.id-conceal-ok = ""

matchedConcealCost : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ} {M A A′ c Xᴿ? M′}
  → CTX.MatchedConcealPartnerOK W M {A} {A′} c Xᴿ? M′
  → String
matchedConcealCost (CTX.matched-seal-star-partner ok) =
  "matched-seal-★-partner"
matchedConcealCost (CTX.matched-seal-nonstar Ans) =
  "matched-seal-non★-partner"
matchedConcealCost CTX.matched-fun-conceal-target = ""
matchedConcealCost CTX.matched-all-conceal-target = ""
matchedConcealCost CTX.matched-id-conceal-target = ""

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

makeRow : ∀ {Δᴸ Δᴿ Δ} {W : CTX.World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → TyNameSupply
  → TyNameSupply
  → TyNameSupply
  → String
  → String
  → String
  → A ⊑ᵂ⟨ W ⟩ B
  → String
  → Row
makeRow {W = W} {A = A} {B = B}
    nameᴸ nameᴿ nameᶜ prefix source target p extra =
  row (prefix ++ source)
    (Snapshot.showTy nameᴸ A)
    (Snapshot.showTy nameᶜ (CTX.embedᴸ W A))
    (addCost (showCost nameᶜ p) extra)
    (Snapshot.showTy nameᶜ (CTX.embedᴿ W B))
    (Snapshot.showTy nameᴿ B)
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

------------------------------------------------------------------------
-- Outside-in derivation traversal
------------------------------------------------------------------------

ladderRows : TyNameSupply → TyNameSupply → TyNameSupply
  → ℕ → (Var → String) → String → String
  → ∀ {Δᴸ Δᴿ Δ} {W : CTX.World Δᴸ Δᴿ Δ}
      {γ : CTX.CtxImp W} {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → List Row
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.x⊑x² {x = x} lookup) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix ("`" ++ xName x)
    ("`" ++ xName x) p "" ∷ []
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.ƛ⊑ƛ² premise) =
  let binder = "♯" ++ show depth in
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix ("λ" ++ binder ++ ". □")
      ("λ" ++ binder ++ ". □") p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ (suc depth)
      (extendTermName xName binder) childPrefix childPrefix premise
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.·⊑·² function argument) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix
      "□₁ · □₂" "□₁ · □₂" p "" ∷
    (ladderRows nameᴸ nameᴿ nameᶜ depth xName
       (childPrefix ++ "├ ") (childPrefix ++ "│ ") function
     List.++
     ladderRows nameᴸ nameᴿ nameᶜ depth xName
       (childPrefix ++ "└ ") (childPrefix ++ "  ") argument)
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.Λ⊑Λ² lift v v′ premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix "Λ□" "Λ□" p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ depth xName
      childPrefix childPrefix premise
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.Λ⊑² Anv occurs lift v targetTyping premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix "Λ□" "─" p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ depth xName
      childPrefix childPrefix premise
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.Λ⊑²-smart-comma Anv occurs liftWorld liftCtx v targetTyping
      premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix "Λ□" "─" p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ depth xName
      childPrefix childPrefix premise
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.•⊑•² {A = A} {A′ = A′} p∀ premise q r) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix
      ("□ [ " ++ Snapshot.showTy nameᴸ A ++ " ]")
      ("□ [ " ++ Snapshot.showTy nameᴿ A′ ++ " ]") p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ depth xName
      childPrefix childPrefix premise
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.•⊑² {A = A} p∀ premise q r) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix
      ("□ [ " ++ Snapshot.showTy nameᴸ A ++ " ]") "─" p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ depth xName
      childPrefix childPrefix premise
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.κ⊑κ² κ q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix (showConst κ) (showConst κ) p "" ∷ []
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.cast⊑cast² c c′ premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix ("□ " ++ castLayer nameᴸ c)
      ("□ " ++ castLayer nameᴿ c′) p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ depth xName
      childPrefix childPrefix premise
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.⊑cast² c′ premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix "─" ("□ " ++ castLayer nameᴿ c′)
      p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ depth xName
      childPrefix childPrefix premise
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.⊑reveal² {c′ = c′} mono rebase same typed premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix "─" ("□ " ++ revealLayer nameᴿ c′)
      p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ depth xName
      childPrefix childPrefix premise
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.⊑conceal² {c′ = c′} mono rebase same typed premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix "─" ("□ " ++ concealLayer nameᴿ c′)
      p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ depth xName
      childPrefix childPrefix premise
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.cast⊑² c premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix ("□ " ++ castLayer nameᴸ c) "─"
      p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ depth xName
      childPrefix childPrefix premise
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.reveal⊑² {c = c} mono rebase same typed premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix ("□ " ++ revealLayer nameᴸ c) "─"
      p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ depth xName
      childPrefix childPrefix premise
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.conceal⊑²-seal-star-open {X = X} no-target mono rebase same typed
      premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix
      ("□ " ++ concealLayer nameᴸ (seal X ★)) "─"
      p "NoTargetOccupantAtSource" ∷
    ladderRows nameᴸ nameᴿ nameᶜ depth xName
      childPrefix childPrefix premise
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.conceal⊑²-source-ok {c = c} ok mono rebase same typed premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix ("□ " ++ concealLayer nameᴸ c) "─"
      p (sourceConcealCost ok) ∷
    ladderRows nameᴸ nameᴿ nameᶜ depth xName
      childPrefix childPrefix premise
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.reveal⊑reveal² {c = c} {c′ = c′}
      mono rebase same typed typed′ premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix ("□ " ++ revealLayer nameᴸ c)
      ("□ " ++ revealLayer nameᴿ c′) p "" ∷
    ladderRows nameᴸ nameᴿ nameᶜ depth xName
      childPrefix childPrefix premise
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.conceal⊑conceal² {c = c} {c′ = c′}
      ok mono rebase same typed typed′ premise q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix ("□ " ++ concealLayer nameᴸ c)
      ("□ " ++ concealLayer nameᴿ c′) p (matchedConcealCost ok) ∷
    ladderRows nameᴸ nameᴿ nameᶜ depth xName
      childPrefix childPrefix premise
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.packaged-seal-star² {Xᴸ = Xᴸ} {Xᴿ = Xᴿ}
      ok mono rebase same typed typed′ premise
      sourcePrem q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix
      ("□ " ++ concealLayer nameᴸ (seal Xᴸ ★))
      ("□ " ++ concealLayer nameᴿ (seal Xᴿ ★))
      p (matchedConcealCost ok) ∷
    (ladderRows nameᴸ nameᴿ nameᶜ depth xName
       (childPrefix ++ "├ ") (childPrefix ++ "│ ") premise
     List.++
     ladderRows nameᴸ nameᴿ nameᶜ depth xName
       (childPrefix ++ "└ ") (childPrefix ++ "  ") sourcePrem)
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W}
    {M′ = M′} {A = outA} {B = outB} {p = p}
    (CTI2.blame⊑² targetTyping q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix "blame"
    (showTerm depth nameᴿ xName M′) p "" ∷ []
ladderRows nameᴸ nameᴿ nameᶜ depth xName
    prefix childPrefix {W = W} {A = outA} {B = outB} {p = p}
    (CTI2.⊕⊑⊕² op left right q) =
  makeRow {W = W} {A = outA} {B = outB}
    nameᴸ nameᴿ nameᶜ prefix
      ("□₁ " ++ showPrim op ++ " □₂")
      ("□₁ " ++ showPrim op ++ " □₂") p "" ∷
    (ladderRows nameᴸ nameᴿ nameᶜ depth xName
       (childPrefix ++ "├ ") (childPrefix ++ "│ ") left
     List.++
     ladderRows nameᴸ nameᴿ nameᶜ depth xName
       (childPrefix ++ "└ ") (childPrefix ++ "  ") right)

------------------------------------------------------------------------
-- Public printers and pinned fixtures
------------------------------------------------------------------------

impLadder : TyNameSupply → TyNameSupply → TyNameSupply → (Var → String)
  → ∀ {Δᴸ Δᴿ Δ} {W : CTX.World Δᴸ Δᴿ Δ}
      {γ : CTX.CtxImp W} {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → String
impLadder nameᴸ nameᴿ nameᶜ xName {W = W} derivation =
  Snapshot.worldSnapshot nameᴸ nameᴿ nameᶜ W ++ "\n" ++
  renderTable (ladderRows nameᴸ nameᴿ nameᶜ zero xName "" "" derivation)

impLadderDefault : ∀ {Δᴸ Δᴿ Δ} {W : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → String
impLadderDefault =
  impLadder Snapshot.defaultName Snapshot.defaultName Snapshot.defaultName
    defaultTermName

-- Examples2 comments out the rejected checkpoint-4-through-14 chain.  This
-- fixture retains checkpoint 8's approved YZ subderivation shape: a
-- target-only Z reveal above an application whose argument is a paired
-- `seal Z ★` conceal.  Its valid literal/cast payload replaces the rejected
-- source-X-seal edge while using live Examples2 world and typing evidence.

checkpoint₈-source-ℕ!₃ :
  C.renameEnv∼ (C.skip Ex2.id↪ᵗ)
    (C.renameEnv∼ (C.skip Ex2.id↪ᵗ)
      (C.renameEnv∼ C.wk↪ᵗ (C.idᶜ {Δ = 0})))
    ⊢ (‵ `ℕ) ∼ ★
checkpoint₈-source-ℕ!₃ =
  C.renameᵐᶜ (C.skip Ex2.id↪ᵗ) Ex2.left-path-ℕ!₂

checkpoint₈-YZ-base :
  Ex2.left-path-world₃-YZ ∣ [] ⊢²
    $ (κℕ 7) ⟨ checkpoint₈-source-ℕ!₃ ⟩
    ⊑ $ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩ ∶ I.★⊑★
checkpoint₈-YZ-base =
  CTI2.cast⊑cast² checkpoint₈-source-ℕ!₃ Ex2.left-path-ℕ!₂
    (CTI2.κ⊑κ² (κℕ 7) (Ex2.ℕ⊑ℕ² {W = Ex2.left-path-world₃-YZ}))
    I.★⊑★

checkpoint₈-YZ-conceal :
  Ex2.left-path-world₃-YZ ∣ [] ⊢²
    ($ (κℕ 7) ⟨ checkpoint₈-source-ℕ!₃ ⟩)
      ↓ seal (Fin.suc (Fin.suc Fin.zero)) ★
    ⊑ ($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
        ↓ seal (Fin.suc Fin.zero) ★ ∶ Ex2.left-path-Z-var⊑YZ₃
checkpoint₈-YZ-conceal =
  CTI2.conceal⊑conceal²
    (CTX.matched-seal-star-partner (CTX.rep★-nonvar-tag nonvar-base))
    (λ _ eq → eq) Ex2.left-path-rebase-Z-YZ₃ CTX.same-[]
    (Conv.⊢↓-sealˣ Ex2.left-path-source-Z∋₃)
    (Conv.⊢↓-sealˣ Ex2.left-path-target-Z∋₃)
    checkpoint₈-YZ-base Ex2.left-path-Z-var⊑YZ₃

checkpoint₈-YZ-application :
  Ex2.left-path-world₃-YZ ∣ [] ⊢²
    ((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      · (($ (κℕ 7) ⟨ checkpoint₈-source-ℕ!₃ ⟩)
          ↓ seal (Fin.suc (Fin.suc Fin.zero)) ★)
    ⊑ (Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
      · (($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
          ↓ seal (Fin.suc Fin.zero) ★) ∶
        Ex2.left-path-Z-var⊑YZ₃
checkpoint₈-YZ-application =
  CTI2.·⊑·² Ex2.left-path-Y-revealed₃-YZ checkpoint₈-YZ-conceal

checkpoint₈-YZ-fragment :
  Ex2.left-path-world₃-YZ ∣ [] ⊢²
    ((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      · (($ (κℕ 7) ⟨ checkpoint₈-source-ℕ!₃ ⟩)
          ↓ seal (Fin.suc (Fin.suc Fin.zero)) ★)
    ⊑ ((Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
      · (($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
          ↓ seal (Fin.suc Fin.zero) ★))
      ↑ unseal (Fin.suc Fin.zero) ★ ∶ Ex2.left-path-Z-var⊑★-YZ₃
checkpoint₈-YZ-fragment =
  CTI2.⊑reveal² (λ _ eq → eq)
    (CTX.rebase-varᴿ Ex2.left-path-rebase-Z-YZ₃) CTX.same-[]
    (Conv.⊢↑-unsealˣ Ex2.left-path-target-Z∋₃)
    checkpoint₈-YZ-application Ex2.left-path-Z-var⊑★-YZ₃

small-lambda-derivation :
  CTX.liftWorldBoth I.X⊑X (Ex2.reflWorld store-empty) ∣ [] ⊢²
    ƛ (` 0) ⊑ ƛ (` 0) ∶
      I.⇒⊑⇒ Ex2.polyId-var⊑ Ex2.polyId-var⊑
small-lambda-derivation =
  CTI2.ƛ⊑ƛ²
    {pA = Ex2.polyId-var⊑} {pB = Ex2.polyId-var⊑}
    (CTI2.x⊑x² {p = Ex2.polyId-var⊑} CTX.Zʷ)

small-lambda-ladder : String
small-lambda-ladder = impLadderDefault small-lambda-derivation

checkpoint₈-target-Z-fragment-ladder : String
checkpoint₈-target-Z-fragment-ladder =
  impLadderDefault checkpoint₈-YZ-fragment

checkpoint₈-ladder :
  Ex2.left-path-world₄-YZ ∣ [] ⊢² Ex.right₈
    ⊑ Ex2.left-path-target₅ ∶ Ex2.left-path-ℕ⊑★₄-YZ
  → String
checkpoint₈-ladder = impLadderDefault

-- Filled after the formatter is type-checked; these intentionally use refl so
-- any presentation change must update an explicit expected ladder.
small-lambda-ladder-pinned : small-lambda-ladder ≡
  "⟨x0: x0↦＇x0 ⊑[X⊑X] x0↦＇x0⟩\n" ++
  "source term  A            ηᴸA          ⊑ costs           " ++
    "ηᴿB          B            target term\n" ++
  "───────────  ───────────  " ++
    "───────────  ────────────────  " ++
    "───────────  ───────────  ───────────\n" ++
  "λ♯0. □       (＇x0 ⇒ ＇x0)  (＇x0 ⇒ ＇x0)  " ++
    "x0 ≈ x0, x0 ≈ x0  (＇x0 ⇒ ＇x0)  " ++
    "(＇x0 ⇒ ＇x0)  λ♯0. □\n" ++
  "`♯0          ＇x0          ＇x0          x0 ≈ x0           " ++
    "＇x0          ＇x0          `♯0"
small-lambda-ladder-pinned = refl

checkpoint₈-target-Z-fragment-ladder-pinned :
  checkpoint₈-target-Z-fragment-ladder ≡
    "⟨x0: x0↦ℕ ⊑[X⊑★] ─ │ " ++
      "x1: x1↦＇x2 ⊑[X⊑X] x0↦＇x1 │ " ++
      "x2: x2↦★ ⊑[X⊑★] x1↦★⟩\n" ++
    "source term            A            ηᴸA          " ++
      "⊑ costs                           ηᴿB          B            " ++
      "target term\n" ++
    "─────────────────────  ───────────  " ++
      "───────────  ────────────────────────────────  " ++
      "───────────  ───────────  " ++
      "───────────────────\n" ++
    "─                      ＇x2          ＇x2          " ++
      "mark X⊑★ at x2                    ★            ★            " ++
      "□ ↑ unseal x1\n" ++
    "□₁ · □₂                ＇x2          ＇x2          " ++
      "x2 ≈ x2                           ＇x2          ＇x1          " ++
      "□₁ · □₂\n" ++
    "├ □ ↑ unseal x1 ⇒-rev  (＇x2 ⇒ ＇x2)  (＇x2 ⇒ ＇x2)  " ++
      "x2 ≈ x2, x2 ≈ x2                  (＇x2 ⇒ ＇x2)  " ++
      "(＇x1 ⇒ ＇x1)  □ ↑ unseal x0 ⇒-rev\n" ++
    "│ λ♯0. □               (＇x1 ⇒ ＇x1)  (＇x1 ⇒ ＇x1)  " ++
      "x1 ≈ x1, x1 ≈ x1                  (＇x1 ⇒ ＇x1)  " ++
      "(＇x0 ⇒ ＇x0)  λ♯0. □\n" ++
    "│ `♯0                  ＇x1          ＇x1          " ++
      "x1 ≈ x1                           ＇x1          ＇x0          " ++
      "`♯0\n" ++
    "└ □ ↓ seal x2          ＇x2          ＇x2          " ++
      "x2 ≈ x2 + matched-seal-★-partner  ＇x2          ＇x1          " ++
      "□ ↓ seal x1\n" ++
    "  □ ⟨ ℕ↦★ ⟩            ★            ★            " ++
      "★⊑★                               " ++
      "★            ★            " ++
      "□ ⟨ ℕ↦★ ⟩\n" ++
    "  7                    ℕ            ℕ            " ++
      "ℕ⊑ℕ                               " ++
      "ℕ            ℕ            " ++
      "7"
checkpoint₈-target-Z-fragment-ladder-pinned = refl
