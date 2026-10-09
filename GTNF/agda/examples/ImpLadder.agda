module examples.ImpLadder where

-- File Charter:
--   * (GTNF) PORTED FROM GTSFImp/proof/DGG/ImpLadder.agda and
--     WorldSnapshot.agda: renders a cast-term-imprecision derivation
--     `W ∣ γ ⊢ M ⊑ M′ ∶ p` (TermImprecision) as an OUTSIDE-IN LADDER.
--     §1 world snapshots; §2 type-imprecision evidence; §3 term
--     fragments; §4 the aligned table; §5 the traversal; §6 the entry
--     points; §7 pinned ladders.
--   * DISPLAY ONLY — no theorem, and nothing depends on it.  Names,
--     types, conversions, coercions, scopes and terms are printed by
--     examples.Show, in design.md's notation.
--   * THE OUTPUT has two blocks.
--     - WORLDS: one entry per world the derivation visits, in order:
--       `Wn = <how it arises>`, then the center `⟨C: L^α ⊑[m] R^β │ …⟩`
--       (index 0 first; each center name C with the left and right
--       names it embeds, `─` where a side skips it, and its mark m,
--       read from the derived marks `marksʷ`, design.md D28), the
--       paired rep. vars `ϱᵍ`, `ϱˡ` (left ⇔ right), the two stores
--       `Ξᴸ`, `Ξᴿ` (oldest rep. var first), and, when there are any,
--       the PERMITTED right rep. vars `κʷ = {β, …}` (D28, D31).  A
--       boundary's interior world that permits is announced as
--       `Interior Wn +κ {β}, pays p`, p its payment (the interior index
--       read without the permission, design.md D31).
--     - THE LADDER: one row per derivation node, outside in, with
--       columns: W (the row's world), the left term fragment, A, ηᴸA,
--       the ⊑ evidence, ηᴿA′, A′, the right term fragment.  A fragment
--       shows only the syntax the node contributes: `□` is a child
--       (`□₁ □₂` for ·⊑·, whose children are drawn as a ├/└ tree) and
--       `─` the silent side of a one-sided rule (cast⊑, ⊑cast, Λ⊑, ν⊑,
--       ⟪⟫⊑, ⊑⟪⟫; blame⊑ prints the whole right term instead).
--     - SLOTS (design.md D31) appear in the silent column of the
--       one-sided rule that moves them: `─ (open Y^β)`, `─ (skip)`,
--       `─ (carry Y^β)` and `─ (fill _ with Y^β)` for ⊑⟪⟫,
--       `─ (pass Y^β)` for ⟪⟫⊑ and a ∀ᵖ cast⊑, `─ (consume Y^β)` for a
--       genᵖ cast⊑ (no cast rule changes the world), `─ (join Y^β)` for
--       Λ⊑ (premise world `Join1 Wn: join Y^β`), and `─ (claim β)` for
--       a Λ⊑ that claims the unnamed right rep. var β (claim-rep,
--       design.md D29; premise world `Wn ⊕ᴸ⇔ β`).  The ηᴸA and ⊑
--       columns read the left type OPENED at the slots (one ∀ stripped
--       per opening; a skipped ∀ stays, its evidence `∀X⊑★. p`).
--     - PERMISSIONS (design.md D31) appear where a boundary adds them:
--       `─ (…, permit β)` in the silent column of ⊑⟪⟫ and ⟪⟫⊑, and
--       `(permit β)` after the right fragment of ⟪⟫⊑⟪⟫.
--   * NAMES (unlike GTSFImp's positional supplies).  Each side's names
--     are read off the context the node is typed in (Show.ctxEnv:
--     Greek rep. vars by allocation order, each paired with its Latin
--     ordinary name), so a Λ binder, a ν, a boundary entry and its
--     rep. var always agree on a letter.  A CENTER name is the left
--     name it embeds, else the right one, suffixed `ᴿ` when that right
--     name is also a left center name.  Term variables are x, y, z, …
--     by λ-depth, as in Show.
--   * THE ⊑ EVIDENCE is the `_⊢_⊑_` derivation, shaped like the types:
--     `→` and `∀X.` for ⇒⊑⇒ and ∀⊑∀, and at each leaf the rule as a
--     relation (`X⊑X`, `X⊑★`, `ℕ⊑ℕ`, `ℕ⊑★`, `★⊑★`) on center names, so
--     every mark decision is visible where it is made; the non-structural
--     rules are `∀X⊑★. p` (∀⊑, the left binder opened at X⊑★),
--     `(p → q)⊑★` (⇒⊑★), `(∀X. p)⊑★` (∀⊑★), `(∀X. ★)⊑★`, `bot-elim`,
--     `bot⊑★`.  This replaces GTSFImp's flat `X ≈ X, …` cost lists,
--     which lose the structure, and its occupancy costs, which GTNF's
--     rules do not have.
--   * Columns are padded by character count (every glyph used is one
--     column wide).  Driven by scripts/render_gtnf.sh:
--       scripts/render_gtnf.sh 'impLadder VL⊑RF' \
--         'open import examples.TermImprecisionRegressionExamples' \
--         'open import examples.ImpLadder'
--   * Pins (by `refl`, §7) a small λ ladder, ΛI⊑ΛI (Λ⊑Λ), the
--     counterexample K's `lk₁⊑rk₃` (open, carry, pass, join) and
--     `VL⊑RF` (open, pass, join), the rebasing block `c12-b1` (the
--     matched boundary permits β), P4's block B3 `p4-B3` (the matched
--     boundary permits α), and H1's final pair `final` and
--     `final-no-push` (claim-rep, design.md D29: `─ (claim α)`, then the
--     rejoin at `+X^α`), and TwoGen's G2 `TwoGen.g2-final` (a skip,
--     filled; two gen layers consume, design.md D31).

open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_; map; reverse; foldr)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _∸_; _⊔_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.String using (String; _++_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
  using (Ty; `_; `ℕ; `𝔹; ★; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ)
open import Ctx using (Ctxᵗ; RVar; reps; names; underΛ)
open import Terms using (Term; `_; ƛ_∙_)
open import Imprecision
  using (VarImp; X⊑X; X⊑★; _⊢_⊑_; ★⊑★; ι⊑ι; ⇒⊑⇒; ∀⊑∀; ⇒⊑★; ι⊑★;
         ∀⊑; ∀★⊑★; ∀⊑★; bot-elim; bot⊑★)
open import ImprecisionWorld
open import TermImprecision
open import examples.Show
  using (Env; ctxEnv; onames; repNm; ordOf; showTy; annTy; showConv;
         showCo; showEnv; showScope; applyChsC; underΛE; showTmF;
         showRepEntries; joinC; nthS; memberS; freshTy; tyBinder;
         tmBinder; showLabel)
open import Coercion using (ModeEnv; Coercion)
open import Conversion using (Conv)
open import Boundary using (Boundary)

-- the examples pinned in §7
open import examples.TypeCheck using (tf)
open import examples.TermImprecisionExamples using (ℕ⊑★)
open import examples.TermImprecisionRebaseExamples using (ΛI⊑ΛI; c12-b1)
open import examples.TermImprecisionRegressionExamples
  using (lk₁⊑rk₃; VL⊑RF)
open import examples.TermImprecisionPermissionExamples using (module P4)
open P4 using (p4-B3)
open import examples.TermImprecisionH1Examples using (final; final-no-push)
open import examples.TermImprecisionD31Examples using (module TwoGen)

------------------------------------------------------------------------
-- 1. World snapshots
------------------------------------------------------------------------

-- a side's names, index 0 first: (ordinary name, rep. var name)
sideNames : Ctxᵗ → List (String × String)
sideNames Δ = map (λ α → ordOf e α , repNm e α) (names Δ)
  where e = ctxEnv Δ

-- one center name: what the left and the right embed there, and its mark
record CEntry : Set where
  constructor centry
  field
    cL : Maybe (String × String)
    cm : VarImp
    cR : Maybe (String × String)
open CEntry

private
  hd : List (String × String) → String × String
  hd []      = "?" , "?"
  hd (n ∷ _) = n

  tl : List (String × String) → List (String × String)
  tl []       = []
  tl (_ ∷ ns) = ns

  hdm : List VarImp → VarImp
  hdm []      = X⊑X
  hdm (m ∷ _) = m

  tlm : List VarImp → List VarImp
  tlm []       = []
  tlm (_ ∷ ms) = ms

-- walk the two embeddings of one center together, with the center's
-- marks (derived, `marksʷ`, design.md D28)
centerEntries : ∀ {η η′ n}
  → List (String × String) → List (String × String) → List VarImp
  → η ↪ n → η′ ↪ n → List CEntry
centerEntries ls rs ms []↪ []↪ = []
centerEntries ls rs ms (keep ι) (keep ι′) =
  centry (just (hd ls)) (hdm ms) (just (hd rs))
    ∷ centerEntries (tl ls) (tl rs) (tlm ms) ι ι′
centerEntries ls rs ms (keep ι) (skip ι′) =
  centry (just (hd ls)) (hdm ms) nothing
    ∷ centerEntries (tl ls) rs (tlm ms) ι ι′
centerEntries ls rs ms (skip ι) (keep ι′) =
  centry nothing (hdm ms) (just (hd rs))
    ∷ centerEntries ls (tl rs) (tlm ms) ι ι′
centerEntries ls rs ms (skip ι) (skip ι′) =
  centry nothing (hdm ms) nothing ∷ centerEntries ls rs (tlm ms) ι ι′

worldEntries : ∀ {Δ Δ′} → World Δ Δ′ → List CEntry
worldEntries {Δ} {Δ′} W =
  centerEntries (sideNames Δ) (sideNames Δ′) (marksʷ W) (ηᴸʷ W) (ηᴿʷ W)

leftCenter : CEntry → List String
leftCenter (centry (just (X , α)) m r) = X ∷ []
leftCenter (centry nothing m r)        = []

leftCenters : List CEntry → List String
leftCenters []       = []
leftCenters (c ∷ cs) = leftCenter c Data.List.++ leftCenters cs

centerName : List String → CEntry → String
centerName ls (centry (just (X , α)) m r)        = X
centerName ls (centry nothing m (just (X , β))) =
  if memberS X ls then X ++ "ᴿ" else X
centerName ls (centry nothing m nothing)         = "?"

-- the center's names, index 0 first: the list types at W are read on
centerNames : ∀ {Δ Δ′} → World Δ Δ′ → List String
centerNames W =
  map (centerName (leftCenters (worldEntries W))) (worldEntries W)

showMark : VarImp → String
showMark X⊑X = "X⊑X"
showMark X⊑★ = "X⊑★"

showSideName : Maybe (String × String) → String
showSideName (just (X , α)) = X ++ "^" ++ α
showSideName nothing        = "─"

showCEntry : List String → CEntry → String
showCEntry ls c =
  centerName ls c ++ ": " ++ showSideName (cL c) ++ " ⊑[" ++
  showMark (cm c) ++ "] " ++ showSideName (cR c)

joinBar : List String → String
joinBar []               = ""
joinBar (s ∷ [])         = s
joinBar (s ∷ ss@(_ ∷ _)) = s ++ " │ " ++ joinBar ss

showRepRel : Env → Env → RepRel → String
showRepRel eL eR ϱ =
  "{" ++ joinC (map (λ { (α , β) → repNm eL α ++ "⇔" ++ repNm eR β }) ϱ)
  ++ "}"

-- a store, oldest rep. var first (Show.showStore without its `Ξ =`)
showReps : Ctxᵗ → String
showReps Δ =
  "[" ++ joinC (reverse (showRepEntries zero (Env.eReps (ctxEnv Δ))
                                             (reps Δ))) ++ "]"


-- a right name position k of Δ′ as `Y^β`
sideName : Ctxᵗ → ℕ → String
sideName Δ′ k = nth (sideNames Δ′) k
  where
  nth : List (String × String) → ℕ → String
  nth []             k       = "?"
  nth ((X , β) ∷ ns) zero    = X ++ "^" ++ β
  nth (n ∷ ns)       (suc k) = nth ns k

sideNameList : Ctxᵗ → List ℕ → String
sideNameList Δ′ ks = joinC (map (sideName Δ′) ks)

-- a slot of the index (design.md D31): an opening `Y^β`, or `_` (skip)
showSlot : Ctxᵗ → Slot → String
showSlot Δ′ (opn k) = sideName Δ′ k
showSlot Δ′ skp     = "_"

showSlots : Ctxᵗ → List Slot → String
showSlots Δ′ O = joinC (map (showSlot Δ′) O)

-- right rep. vars, by their Greek letters
showRVars : Ctxᵗ → List RVar → String
showRVars Δ′ κ = joinC (map (repNm (ctxEnv Δ′)) κ)

-- the two lines after `Wn = …`, then `κʷ = {β, …}` (the permitted
-- right rep. vars, design.md D28, D31) when there are any
worldSnapshot : ∀ {Δ Δ′} → World Δ Δ′ → String
worldSnapshot {Δ} {Δ′} W =
  "  ⟨" ++ joinBar (map (showCEntry ls) es) ++ "⟩\n" ++
  "  ϱᵍ = " ++ showRepRel eL eR (ϱᵍʷ W) ++
  "  ϱˡ = " ++ showRepRel eL eR (ϱˡʷ W) ++
  "  Ξᴸ = " ++ showReps Δ ++ "  Ξᴿ = " ++ showReps Δ′ ++
  permitted (κʷ W)
  where
  es = worldEntries W
  ls = leftCenters es
  eL = ctxEnv Δ
  eR = ctxEnv Δ′
  permitted : List RVar → String
  permitted []         = ""
  permitted κ@(_ ∷ _)  = "  κʷ = {" ++ showRVars Δ′ κ ++ "}"

------------------------------------------------------------------------
-- 2. Type-imprecision evidence, on the center's names
------------------------------------------------------------------------

mutual
  showImp : List String → ∀ {μ A B} → μ ⊢ A ⊑ B → String
  showImp ns {A = A} ★⊑★       = "★⊑★"
  showImp ns {A = A} (ι⊑ι _)   = showTy ns A ++ "⊑" ++ showTy ns A
  showImp ns {A = A} X⊑X       = showTy ns A ++ "⊑" ++ showTy ns A
  showImp ns (⇒⊑⇒ p q)         = impP ns p ++ " → " ++ showImp ns q
  showImp ns (∀⊑∀ p)           =
    "∀" ++ freshTy ns ++ ". " ++ showImp (freshTy ns ∷ ns) p
  showImp ns (⇒⊑★ p q)         =
    "(" ++ impP ns p ++ " → " ++ showImp ns q ++ ")⊑★"
  showImp ns {A = A} (ι⊑★ _)   = showTy ns A ++ "⊑★"
  showImp ns {A = A} (X⊑★ _)   = showTy ns A ++ "⊑★"
  showImp ns (∀⊑ _ _ p)        =
    "∀" ++ freshTy ns ++ "⊑★. " ++ showImp (freshTy ns ∷ ns) p
  showImp ns ∀★⊑★              = "(∀" ++ freshTy ns ++ ". ★)⊑★"
  showImp ns (∀⊑★ _ p)         =
    "(∀" ++ freshTy ns ++ ". " ++ showImp (freshTy ns ∷ ns) p ++ ")⊑★"
  showImp ns bot-elim          = "bot-elim"
  showImp ns bot⊑★             = "bot⊑★"

  -- evidence as the left operand of `→`
  impP : List String → ∀ {μ A B} → μ ⊢ A ⊑ B → String
  impP ns p@★⊑★         = showImp ns p
  impP ns p@(ι⊑ι _)     = showImp ns p
  impP ns p@X⊑X         = showImp ns p
  impP ns p@(⇒⊑⇒ _ _)   = "(" ++ showImp ns p ++ ")"
  impP ns p@(∀⊑∀ _)     = "(" ++ showImp ns p ++ ")"
  impP ns p@(⇒⊑★ _ _)   = showImp ns p
  impP ns p@(ι⊑★ _)     = showImp ns p
  impP ns p@(X⊑★ _)     = showImp ns p
  impP ns p@(∀⊑ _ _ _)  = "(" ++ showImp ns p ++ ")"
  impP ns p@∀★⊑★        = showImp ns p
  impP ns p@(∀⊑★ _ _)   = showImp ns p
  impP ns p@bot-elim    = showImp ns p
  impP ns p@bot⊑★       = showImp ns p

-- the opened left type and the evidence of an index
-- `A ⊑ᵂ⟨ W ⟩[ O ] A′` (OpenO, design.md D31): one `∀` stripped per
-- opening; a skipped `∀` stays, its evidence shown as type imprecision's
-- `∀X⊑★. p` (a skip is `∀⊑` at one position)
openTy : (ℕ → ℕ) → List Slot → Renameᵗ → Ty → Ty
openTy e []          ρ A      = renameᵗ ρ A
openTy e (opn k ∷ O) ρ (`∀ A) = openTy e O (e k ⊳ ρ) A
openTy e (skp ∷ O)   ρ (`∀ A) =
  `∀ (openTy (λ k → suc (e k)) O (extᵗ ρ) A)
openTy e (_ ∷ _)     ρ A      = renameᵗ ρ A

openEv : List String → ∀ {μ} e O ρ A {B} → OpenO μ e O ρ A B → String
openEv ns e []          ρ A        p = showImp ns p
openEv ns e (opn k ∷ O) ρ (`∀ A)   p = openEv ns e O (e k ⊳ ρ) A p
openEv ns e (skp ∷ O)   ρ (`∀ A)   (_ , _ , p) =
  "∀" ++ freshTy ns ++ "⊑★. " ++
  openEv (freshTy ns ∷ ns) (λ k → suc (e k)) O (extᵗ ρ) A p
openEv ns e (opn _ ∷ O) ρ (` X)    ()
openEv ns e (opn _ ∷ O) ρ `ℕ       ()
openEv ns e (opn _ ∷ O) ρ `𝔹       ()
openEv ns e (opn _ ∷ O) ρ ★        ()
openEv ns e (opn _ ∷ O) ρ (A ⇒ A′) ()
openEv ns e (skp ∷ O)   ρ (` X)    ()
openEv ns e (skp ∷ O)   ρ `ℕ       ()
openEv ns e (skp ∷ O)   ρ `𝔹       ()
openEv ns e (skp ∷ O)   ρ ★        ()
openEv ns e (skp ∷ O)   ρ (A ⇒ A′) ()

-- the evidence of an index at a world, on that world's center
indexEv : ∀ {Δ Δ′} (W : World Δ Δ′) (O : List Slot) (A A′ : Ty)
  → A ⊑ᵂ⟨ W ⟩[ O ] A′ → String
indexEv W O A A′ p = openEv (centerNames W) (emb (ηᴿʷ W)) O (emb (ηᴸʷ W)) A p

------------------------------------------------------------------------
-- 3. Term fragments (Show's printers, with the child as □)
------------------------------------------------------------------------

-- the type/rep. var counter of a context: its next binder's letter
ctr : Ctxᵗ → ℕ
ctr Δ = Data.List.length (reps Δ)

termIn : Ctxᵗ → List String → ℕ → Term → String
termIn Δ tms x M = proj₁ (showTmF (ctxEnv Δ) tms (ctr Δ) x M)

lamFrag : Ctxᵗ → ℕ → Ty → String
lamFrag Δ x A = "λ" ++ tmBinder x ++ ":" ++ annTy (onames (ctxEnv Δ)) A ++ ". □"

tyLamFrag : Ctxᵗ → String
tyLamFrag Δ = "Λ" ++ tyBinder (ctr Δ) ++ ". □"

castFrag : Ctxᵗ → ModeEnv → Coercion → String
castFrag Δ μ c =
  "□⟨" ++ proj₁ (showCo (onames (ctxEnv Δ)) (ctr Δ) c) ++ "⟩" ++
  showEnv (onames (ctxEnv Δ)) μ

nuFrag : Ctxᵗ → Ty → Conv → String
nuFrag Δ A c =
  "ν " ++ X ++ ":=" ++ showTy (onames (ctxEnv Δ)) A ++ ". (□ " ++ X ++
  ") ⟨" ++ showConv (onames (underΛE (ctr Δ) (ctxEnv Δ))) c ++ "⟩"
  where X = tyBinder (ctr Δ)

bdyFrag : Ctxᵗ → Boundary → Conv → String
bdyFrag Δ Θ c =
  showScope (ctxEnv Δ) Θ ++ " □ ⟨" ++
  showConv (onames (applyChsC Θ (ctxEnv Δ))) c ++ "⟩"

------------------------------------------------------------------------
-- 4. The aligned table
------------------------------------------------------------------------

Row : Set
Row = List String

header : Row
header = "W" ∷ "left term" ∷ "A" ∷ "ηᴸA" ∷ "⊑" ∷ "ηᴿA′" ∷ "A′" ∷
  "right term" ∷ []

maxW : List ℕ → Row → List ℕ
maxW []       []       = []
maxW []       (s ∷ ss) = length s ∷ maxW [] ss
maxW (w ∷ ws) []       = w ∷ maxW ws []
maxW (w ∷ ws) (s ∷ ss) = (w ⊔ length s) ∷ maxW ws ss

spaces : ℕ → String
spaces zero    = ""
spaces (suc n) = " " ++ spaces n

dashes : ℕ → String
dashes zero    = ""
dashes (suc n) = "─" ++ dashes n

-- every column but the last is padded to its width
renderRow : List ℕ → Row → String
renderRow ws       []                = ""
renderRow ws       (s ∷ [])          = s
renderRow []       (s ∷ s′ ∷ ss)     = s ++ "  " ++ renderRow [] (s′ ∷ ss)
renderRow (w ∷ ws) (s ∷ s′ ∷ ss)     =
  s ++ spaces (w ∸ length s) ++ "  " ++ renderRow ws (s′ ∷ ss)

joinLines : List String → String
joinLines []                 = ""
joinLines (l ∷ [])           = l
joinLines (l ∷ ls@(_ ∷ _))   = l ++ "\n" ++ joinLines ls

renderTable : List Row → String
renderTable rows =
  joinLines (renderRow ws header ∷ renderRow ws (map dashes ws)
             ∷ map (renderRow ws) rows)
  where ws = foldr (λ r acc → maxW acc r) [] (header ∷ rows)

------------------------------------------------------------------------
-- 5. The outside-in traversal
------------------------------------------------------------------------

-- rows and world entries, each NEWEST FIRST, and the next world number
record Acc : Set where
  constructor acc
  field
    rowsA   : List Row
    worldsA : List String
    nextW   : ℕ
open Acc

label : ℕ → String
label n = "W" ++ show n

pushRow : Row → Acc → Acc
pushRow r (acc rs ws nw) = acc (r ∷ rs) ws nw

-- a new world: its entry is `Wn = prov` and its snapshot
pushWorld : ∀ {Δ Δ′} → String → World Δ Δ′ → Acc → Acc
pushWorld prov W (acc rs ws nw) =
  acc rs ((label nw ++ " = " ++ prov ++ "\n" ++ worldSnapshot W) ∷ ws)
    (suc nw)

-- the type columns of a node at world W, its left type opened at the
-- slots O (design.md D31)
typeCols : ∀ {Δ Δ′} (W : World Δ Δ′) (O : List Slot) (A A′ : Ty)
  → A ⊑ᵂ⟨ W ⟩[ O ] A′ → List String
typeCols {Δ} {Δ′} W O A A′ p =
  showTy (onames (ctxEnv Δ)) A ∷
  showTy cn (openTy (emb (ηᴿʷ W)) O (emb (ηᴸʷ W)) A) ∷
  indexEv W O A A′ p ∷ showTy cn (embᴿ W A′) ∷
  showTy (onames (ctxEnv Δ′)) A′ ∷ []
  where
  cn = centerNames W

-- the row of a derivation node
nodeRow : ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W} {M M′ O A A′}
    {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → ℕ → String → String → String
  → W ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩[ O ] p → Row
nodeRow {W = W} {O = O} {A = A} {A′ = A′} {p = p} n pre l r d =
  label n ∷ (pre ++ l) ∷ (typeCols W O A A′ p Data.List.++ (r ∷ []))

-- the silent side of a one-sided rule, with what it does to the slots
-- and permissions (design.md D31): `consume Y^β`, `pass Y^β`,
-- `join Y^β`, `claim β`, and at a boundary `carry …`, `open Y^β`,
-- `skip`, `fill _ with Y^β`, `permit β`
notes : List String → String
notes []         = "─"
notes ns@(_ ∷ _) = "─ (" ++ joinC ns ++ ")"

-- `cast⊑`: a ∀ layer passes its slot, a gen layer consumes it
castNotes : ∀ {M c O Oₚ} → Ctxᵗ → CastOpen M c O Oₚ → List String
castNotes Δ′ co-plain               = []
castNotes Δ′ (co-∀ {s = s} _ co)    =
  ("pass " ++ showSlot Δ′ s) ∷ castNotes Δ′ co
castNotes Δ′ (co-gen {s = s} _ co)  =
  ("consume " ++ showSlot Δ′ s) ∷ castNotes Δ′ co

-- `⟪⟫⊑`: the slots pass into a ∀-boundary
bdyNotes : ∀ {M c O} → Ctxᵗ → BdyOpen M c O → List String
bdyNotes Δ′ bo-plain               = []
bdyNotes Δ′ (bo-∀ {s = s} {O} _ _) = ("pass " ++ showSlots Δ′ (s ∷ O)) ∷ []

-- a boundary's permissions K
permitNotes : Ctxᵗ → List RVar → List String
permitNotes Δ′ []         = []
permitNotes Δ′ K@(_ ∷ _)  = ("permit " ++ showRVars Δ′ K) ∷ []

-- `⊑⟪⟫`: the carried slots (exterior positions), then the new slots
-- (interior positions), a new opening filling a carried skip
newNote : Ctxᵗ → Slot → String
newNote Δ′ᵢ (opn k) = "open " ++ sideName Δ′ᵢ k
newNote Δ′ᵢ skp     = "skip"

fillNotes : ∀ {O′ N Oᵢ} → Ctxᵗ → Fill O′ N Oᵢ → List String
fillNotes {N = N} Δ′ᵢ f-end = map (newNote Δ′ᵢ) N
fillNotes Δ′ᵢ (f-keep f)    = fillNotes Δ′ᵢ f
fillNotes Δ′ᵢ (f-fill {k = k} f) =
  ("fill _ with " ++ sideName Δ′ᵢ k) ∷ fillNotes Δ′ᵢ f

pushNotes : ∀ {Θ′ M O N Oᵢ} → Ctxᵗ → Ctxᵗ → Push Θ′ M O N Oᵢ
  → List String
pushNotes {O = O} Δ′ Δ′ᵢ (push _ f _ _) = carry O Data.List.++ fillNotes Δ′ᵢ f
  where
  carry : List Slot → List String
  carry []          = []
  carry O@(_ ∷ _)   = ("carry " ++ showSlots Δ′ O) ∷ []

-- a boundary's interior world: its permissions and its payment (the
-- interior index read without them)
interiorProv : ∀ {Δᵢ Δ′ᵢ} → ℕ → Ctxᵗ → (Wᵢ : World Δᵢ Δ′ᵢ) → List RVar
  → (O : List Slot) (A A′ : Ty) → A ⊑ᵂ⟨ Wᵢ ⟩[ O ] A′ → String
interiorProv n Δ′ Wᵢ []        O A A′ pay = "Interior " ++ label n
interiorProv n Δ′ Wᵢ K@(_ ∷ _) O A A′ pay =
  "Interior " ++ label n ++ " +κ {" ++ showRVars Δ′ K ++ "}, pays " ++
  indexEv Wᵢ O A A′ pay

-- the world of a derivation (a premise's world, for `pushWorld`)
worldOf : ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W} {M M′ O A A′}
    {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → W ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩[ O ] p → World Δ Δ′
worldOf {W = W} _ = W

-- `go a n pre pre′ x tms d`: d's rows, outside in; n is d's world, pre
-- the tree prefix of d's row and pre′ that of its children, x the
-- λ-depth and tms the term variables' names
go : ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W} {M M′ O A A′}
    {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → Acc → ℕ → String → String → ℕ → List String
  → W ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩[ O ] p → Acc
go a n pre pre′ x tms d@(x⊑x {x = y} _) =
  pushRow (nodeRow n pre (nthS tms y) (nthS tms y) d) a
go {Δ} a n pre pre′ x tms d@(κ⊑κ {k = k} _ _) =
  pushRow (nodeRow n pre (termIn Δ tms x k) (termIn Δ tms x k) d) a
go {Δ} {Δ′} a n pre pre′ x tms d@(ƛ⊑ƛ {A = A} {A′ = A′} _ _ N) =
  go (pushRow (nodeRow n pre (lamFrag Δ x A) (lamFrag Δ′ x A′) d) a)
    n pre′ pre′ (suc x) (tmBinder x ∷ tms) N
go a n pre pre′ x tms d@(·⊑· L M) =
  go (go (pushRow (nodeRow n pre "□₁ □₂" "□₁ □₂" d) a)
         n (pre′ ++ "├ ") (pre′ ++ "│ ") x tms L)
    n (pre′ ++ "└ ") (pre′ ++ "  ") x tms M
go {Δ′ = Δ′} a n pre pre′ x tms d@(blame⊑ {ℓ = ℓ} {M′ = M′} _ _ _) =
  pushRow (nodeRow n pre ("blame " ++ showLabel ℓ) (termIn Δ′ tms x M′) d) a
go {Δ} {Δ′} a n pre pre′ x tms
    d@(cast⊑cast {μ = μ} {μ′ = μ′} {c = c} {c′ = c′} M _ _ _) =
  go (pushRow (nodeRow n pre (castFrag Δ μ c) (castFrag Δ′ μ′ c′) d) a)
    n pre′ pre′ x tms M
-- no cast rule changes the world (design.md D31): the slots change
go {Δ} {Δ′} a n pre pre′ x tms d@(cast⊑ {μ = μ} {c = c} co M _ _) =
  go (pushRow (nodeRow n pre (castFrag Δ μ c) (notes (castNotes Δ′ co)) d)
       a)
    n pre′ pre′ x tms M
go {Δ′ = Δ′} a n pre pre′ x tms d@(⊑cast {μ′ = μ′} {c′ = c′} M _ _) =
  go (pushRow (nodeRow n pre "─" (castFrag Δ′ μ′ c′) d) a)
    n pre′ pre′ x tms M
go {Δ} {Δ′} a n pre pre′ x tms d@(Λ⊑Λ _ _ _ V _) =
  go (pushWorld (label n ++ " ⊕²") (worldOf V) a₁)
    (nextW a₁) pre′ pre′ x tms V
  where a₁ = pushRow (nodeRow n pre (tyLamFrag Δ) (tyLamFrag Δ′) d) a
go {Δ} {Δ′} a n pre pre′ x tms d@(Λ⊑ b-fresh _ _ _ _ V _) =
  go (pushWorld (label n ++ " ⊕ᴸ") (worldOf V) a₁) (nextW a₁) pre′ pre′ x tms V
  where a₁ = pushRow (nodeRow n pre (tyLamFrag Δ) "─" d) a
-- claim-rep (design.md D29): the binder claims the unnamed right rep.
-- var β; its premise world is `Wn ⊕ᴸ⇔ β`
go {Δ} {Δ′} a n pre pre′ x tms d@(Λ⊑ (b-rep {β = β} _ _ _) _ _ _ _ V _) =
  go (pushWorld (label n ++ " ⊕ᴸ⇔ " ++ α) (worldOf V) a₁)
    (nextW a₁) pre′ pre′ x tms V
  where
  α = repNm (ctxEnv Δ′) β
  a₁ = pushRow (nodeRow n pre (tyLamFrag Δ) (notes (("claim " ++ α) ∷ []))
                 d) a
-- the join of the next opening (design.md D31): a term binder
go {Δ} {Δ′} a n pre pre′ x tms
    d@(Λ⊑ (b-join (join1 {k = k} _ _ _)) _ _ _ _ V _) =
  go (pushWorld ("Join1 " ++ label n ++ ": join " ++ sideName Δ′ k)
       (worldOf V) a₁)
    (nextW a₁) pre′ pre′ x tms V
  where
  a₁ = pushRow (nodeRow n pre (tyLamFrag Δ)
                 (notes (("join " ++ sideName Δ′ k) ∷ [])) d) a
go {Δ} {Δ′} a n pre pre′ x tms
    d@(ν⊑ν {A = A} {A′ = A′} {c = c} {c′ = c′} L _ _ _ _ _) =
  go (pushRow (nodeRow n pre (nuFrag Δ A c) (nuFrag Δ′ A′ c′) d) a)
    n pre′ pre′ x tms L
go {Δ} a n pre pre′ x tms d@(ν⊑ {A = A} {c = c} L _ _ _) =
  go (pushRow (nodeRow n pre (nuFrag Δ A c) "─" d) a) n pre′ pre′ x tms L
go {Δ} {Δ′} a n pre pre′ x tms
    d@(⟪⟫⊑⟪⟫ {Wᵢ = Wᵢ} {K = K} {Θ = Θ} {Θ′ = Θ′} {c = c} {c′ = c′}
         {Aᵢ = Aᵢ} {A′ᵢ = A′ᵢ} _ _ _ pay M _ _ _ _) =
  go (pushWorld (interiorProv n Δ′ Wᵢ K [] Aᵢ A′ᵢ pay) (worldOf M) a₁)
    (nextW a₁) pre′ pre′ x tms M
  where
  permits : List String → String
  permits []         = ""
  permits ns@(_ ∷ _) = " (" ++ joinC ns ++ ")"
  a₁ = pushRow (nodeRow n pre (bdyFrag Δ Θ c)
                 (bdyFrag Δ′ Θ′ c′ ++ permits (permitNotes Δ′ K)) d) a
go {Δ} {Δ′} a n pre pre′ x tms
    d@(⟪⟫⊑ {Wᵢ = Wᵢ} {K = K} {Θ = Θ} {c = c} {Aᵢ = Aᵢ} {A′ = A′} {O = O}
         _ _ bo _ _ pay M _ _) =
  go (pushWorld (interiorProv n Δ′ Wᵢ K O Aᵢ A′ pay) (worldOf M) a₁)
    (nextW a₁) pre′ pre′ x tms M
  where
  a₁ = pushRow (nodeRow n pre (bdyFrag Δ Θ c)
                 (notes (bdyNotes Δ′ bo Data.List.++ permitNotes Δ′ K)) d) a
go {Δ′ = Δ′} a n pre pre′ x tms
    d@(⊑⟪⟫ {Δ′ᵢ = Δ′ᵢ} {Wᵢ = Wᵢ} {K = K} {Θ′ = Θ′} {c′ = c′} {A = A}
         {A′ᵢ = A′ᵢ} {Oᵢ = Oᵢ} _ pu _ _ _ _ pay M _ _) =
  go (pushWorld (interiorProv n Δ′ Wᵢ K Oᵢ A A′ᵢ pay) (worldOf M) a₁)
    (nextW a₁) pre′ pre′ x tms M
  where
  a₁ = pushRow (nodeRow n pre
                 (notes (pushNotes Δ′ Δ′ᵢ pu Data.List.++ permitNotes Δ′ K))
                 (bdyFrag Δ′ Θ′ c′) d) a

------------------------------------------------------------------------
-- 6. Entry points
------------------------------------------------------------------------

-- the whole ladder: worlds, table
impLadder : ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W} {M M′ O A A′}
    {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → W ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩[ O ] p → String
impLadder {W = W} d =
  joinLines (reverse (worldsA a)) ++ "\n" ++ renderTable (reverse (rowsA a))
  where
  a = go (pushWorld "the conclusion's world" W (acc [] [] zero))
         zero "" "" zero [] d

-- GTSFImp's name for the printer (there it fixed the name supplies;
-- GTNF reads names off the contexts, so the two coincide)
impLadderDefault : ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W}
    {M M′ O A A′} {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → W ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩[ O ] p → String
impLadderDefault = impLadder

------------------------------------------------------------------------
-- 7. Pinned ladders
------------------------------------------------------------------------

-- λx:ℕ. x ⊑ λx:★. x
small-λ : ∅ʷ ∣ [] ⊢ ƛ `ℕ ∙ ` 0 ⊑ ƛ ★ ∙ ` 0 ∶ ⇒⊑⇒ ℕ⊑★ ℕ⊑★
small-λ = ƛ⊑ƛ {pA = ℕ⊑★} tf tf (x⊑x Zʷ)

-- the pins: any presentation change must update these expected ladders

small-λ-ladder-pinned : impLadder small-λ ≡
  "W0 = the conclusion's world\n" ++
  "  ⟨⟩\n" ++
  "  ϱᵍ = {}  ϱˡ = {}  Ξᴸ = []  Ξᴿ = []\n" ++
  "W   left term  A    ηᴸA  ⊑          ηᴿA′  A′   right term\n" ++
  "──  ─────────  ───  ───  ─────────  ────  ───  ──────────\n" ++
  "W0  λx:ℕ. □    ℕ→ℕ  ℕ→ℕ  ℕ⊑★ → ℕ⊑★  ★→★   ★→★  λx:★. □\n" ++
  "W0  x          ℕ    ℕ    ℕ⊑★        ★     ★    x"
small-λ-ladder-pinned = refl

ΛI⊑ΛI-ladder-pinned : impLadder ΛI⊑ΛI ≡
  "W0 = the conclusion's world\n" ++
  "  ⟨⟩\n" ++
  "  ϱᵍ = {}  ϱˡ = {}  Ξᴸ = []  Ξᴿ = []\n" ++
  "W1 = W0 ⊕²\n" ++
  "  ⟨X: X^α ⊑[X⊑X] X^α⟩\n" ++
  "  ϱᵍ = {}  ϱˡ = {α⇔α}  Ξᴸ = [α abst]  Ξᴿ = [α abst]\n" ++
  "W   left term  A        ηᴸA      ⊑              ηᴿA′     A′     " ++
  "  right term\n" ++
  "──  ─────────  ───────  ───────  ─────────────  ───────  ───────" ++
  "  ──────────\n" ++
  "W0  ΛX. □      ∀X. X→X  ∀X. X→X  ∀X. X⊑X → X⊑X  ∀X. X→X  ∀X. X→X" ++
  "  ΛX. □\n" ++
  "W1  λx:X. □    X→X      X→X      X⊑X → X⊑X      X→X      X→X    " ++
  "  λx:X. □\n" ++
  "W1  x          X        X        X⊑X            X        X      " ++
  "  x"
ΛI⊑ΛI-ladder-pinned = refl

-- K before the right's Merge (design.md D31): the outer `+Y^β` OPENS
-- the left's ∀ at Y (`─ (open Y^β)`), the inner `+X^α` CARRIES the
-- slot, the left's boundary passes it, and ΛY JOINS it (W4 = Join1)
lk₁⊑rk₃-ladder-pinned : impLadder lk₁⊑rk₃ ≡
  "W0 = the conclusion's world\n" ++
  "  ⟨⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ, β:=★]\n" ++
  "W1 = Interior W0\n" ++
  "  ⟨Y: ─ ⊑[X⊑X] Y^β⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ, β:=★]\n" ++
  "W2 = Interior W1\n" ++
  "  ⟨Y: ─ ⊑[X⊑X] Y^β │ X: ─ ⊑[X⊑X] X^α⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ, β:=★]\n" ++
  "W3 = Interior W2\n" ++
  "  ⟨Y: ─ ⊑[X⊑X] Y^β │ X: X^α ⊑[X⊑X] X^α⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ, β:=★]\n" ++
  "W4 = Join1 W3: join Y^β\n" ++
  "  ⟨Y: Y^β ⊑[X⊑X] Y^β │ X: X^α ⊑[X⊑X] X^α⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {β⇔β}  Ξᴸ = [α:=ℕ, β abst]  Ξᴿ = [α:=ℕ, β:=★]" ++
  "\n" ++
  "W   left term                         A                  ηᴸA    " ++
  "            ⊑                                    ηᴿA′       A′  " ++
  "       right term\n" ++
  "──  ────────────────────────────────  ─────────────────  ───────" ++
  "──────────  ───────────────────────────────────  ─────────  ────" ++
  "─────  ────────────────────────\n" ++
  "W0  □₁ □₂                             ∀X. X→X            ∀X. X→X" ++
  "            ∀X⊑★. X⊑★ → X⊑★                      ★→★        ★→★ " ++
  "       □₁ □₂\n" ++
  "W0  ├ λx:(∀X. X→X). □                 (∀X. X→X)→∀X. X→X  (∀X. X→" ++
  "X)→∀X. X→X  (∀X⊑★. X⊑★ → X⊑★) → ∀X⊑★. X⊑★ → X⊑★  (★→★)→★→★  (★→★" ++
  ")→★→★  λx:★→★. □\n" ++
  "W0  │ x                               ∀X. X→X            ∀X. X→X" ++
  "            ∀X⊑★. X⊑★ → X⊑★                      ★→★        ★→★ " ++
  "       x\n" ++
  "W0  └ ─                               ∀X. X→X            ∀X. X→X" ++
  "            ∀X⊑★. X⊑★ → X⊑★                      ★→★        ★→★ " ++
  "       □⟨id(★) → id(★)⟩^[]\n" ++
  "W0    ─ (open Y^β)                    ∀X. X→X            ∀X. X→X" ++
  "            ∀X⊑★. X⊑★ → X⊑★                      ★→★        ★→★ " ++
  "       [+Y^β] □ ⟨−Y → +Y⟩\n" ++
  "W1    ─ (carry Y^β)                   ∀X. X→X            Y→Y    " ++
  "            Y⊑Y → Y⊑Y                            Y→Y        Y→Y " ++
  "       [+X^α] □ ⟨id(Y) → id(Y)⟩\n" ++
  "W2    [+X^α] □ ⟨∀Y. (id(Y) → id(Y))⟩  ∀X. X→X            Y→Y    " ++
  "            Y⊑Y → Y⊑Y                            Y→Y        Y→Y " ++
  "       ─ (pass Y^β)\n" ++
  "W3    ΛY. □                           ∀Y. Y→Y            Y→Y    " ++
  "            Y⊑Y → Y⊑Y                            Y→Y        Y→Y " ++
  "       ─ (join Y^β)\n" ++
  "W4    λx:Y. □                         Y→Y                Y→Y    " ++
  "            Y⊑Y → Y⊑Y                            Y→Y        Y→Y " ++
  "       λx:Y. □\n" ++
  "W4    x                               Y                  Y      " ++
  "            Y⊑Y                                  Y          Y   " ++
  "       x"
lk₁⊑rk₃-ladder-pinned = refl

-- K's final pair (design.md D31): the merged `+Y^β, +X^α` opens Y;
-- pass, join
VL⊑RF-ladder-pinned : impLadder VL⊑RF ≡
  "W0 = the conclusion's world\n" ++
  "  ⟨⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ, β:=★]\n" ++
  "W1 = Interior W0\n" ++
  "  ⟨Y: ─ ⊑[X⊑X] Y^β │ X: ─ ⊑[X⊑X] X^α⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ, β:=★]\n" ++
  "W2 = Interior W1\n" ++
  "  ⟨Y: ─ ⊑[X⊑X] Y^β │ X: X^α ⊑[X⊑X] X^α⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ, β:=★]\n" ++
  "W3 = Join1 W2: join Y^β\n" ++
  "  ⟨Y: Y^β ⊑[X⊑X] Y^β │ X: X^α ⊑[X⊑X] X^α⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {β⇔β}  Ξᴸ = [α:=ℕ, β abst]  Ξᴿ = [α:=ℕ, β:=★]" ++
  "\n" ++
  "W   left term                       A        ηᴸA      ⊑         " ++
  "       ηᴿA′  A′   right term\n" ++
  "──  ──────────────────────────────  ───────  ───────  ──────────" ++
  "─────  ────  ───  ────────────────────────\n" ++
  "W0  ─                               ∀X. X→X  ∀X. X→X  ∀X⊑★. X⊑★ " ++
  "→ X⊑★  ★→★   ★→★  □⟨id(★) → id(★)⟩^[]\n" ++
  "W0  ─ (open Y^β)                    ∀X. X→X  ∀X. X→X  ∀X⊑★. X⊑★ " ++
  "→ X⊑★  ★→★   ★→★  [+Y^β, +X^α] □ ⟨−Y → +Y⟩\n" ++
  "W1  [+X^α] □ ⟨∀Y. (id(Y) → id(Y))⟩  ∀X. X→X  Y→Y      Y⊑Y → Y⊑Y " ++
  "       Y→Y   Y→Y  ─ (pass Y^β)\n" ++
  "W2  ΛY. □                           ∀Y. Y→Y  Y→Y      Y⊑Y → Y⊑Y " ++
  "       Y→Y   Y→Y  ─ (join Y^β)\n" ++
  "W3  λx:Y. □                         Y→Y      Y→Y      Y⊑Y → Y⊑Y " ++
  "       Y→Y   Y→Y  λx:Y. □\n" ++
  "W3  x                               Y        Y        Y⊑Y       " ++
  "       Y     Y    x"
VL⊑RF-ladder-pinned = refl

-- C12 B1 (design.md D25, D31): the matched TyBeta boundary joins its
-- fresh pair and PERMITS β for its interior (`(permit β)`, W1 = Interior
-- W0 +κ {β}, paying X→X ⊑ X→X at X⊑X); inside, the gen wrapper
-- `Y! → Y?` is a plain ⊑cast at the permitted X
c12-b1-ladder-pinned : impLadder c12-b1 ≡
  "W0 = the conclusion's world\n" ++
  "  ⟨⟩\n" ++
  "  ϱᵍ = {α⇔β, α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=★, β:=ℕ]\n" ++
  "W1 = Interior W0 +κ {β}, pays X⊑X → X⊑X\n" ++
  "  ⟨X: X^α ⊑[X⊑★] Y^β⟩\n" ++
  "  ϱᵍ = {α⇔β, α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=★, β:=ℕ]  κʷ =" ++
  " {β}\n" ++
  "W2 = Interior W1\n" ++
  "  ⟨X: X^α ⊑[X⊑★] ─⟩\n" ++
  "  ϱᵍ = {α⇔β, α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=★, β:=ℕ]  κʷ =" ++
  " {β}\n" ++
  "W3 = Interior W2\n" ++
  "  ⟨X: X^α ⊑[X⊑X] X^α⟩\n" ++
  "  ϱᵍ = {α⇔β, α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=★, β:=ℕ]  κʷ =" ++
  " {β}\n" ++
  "W   left term             A    ηᴸA  ⊑          ηᴿA′  A′   right " ++
  "term\n" ++
  "──  ────────────────────  ───  ───  ─────────  ────  ───  ──────" ++
  "───────────────────────\n" ++
  "W0  □₁ □₂                 ℕ    ℕ    ℕ⊑ℕ        ℕ     ℕ    □₁ □₂" ++
  "\n" ++
  "W0  ├ [+X^α] □ ⟨−X → +X⟩  ℕ→ℕ  ℕ→ℕ  ℕ⊑ℕ → ℕ⊑ℕ  ℕ→ℕ   ℕ→ℕ  [+Y^β]" ++
  " □ ⟨−Y → +Y⟩ (permit β)\n" ++
  "W1  │ ─                   X→X  X→X  X⊑X → X⊑X  X→X   Y→Y  □⟨Y! →" ++
  " Y?ℓ0⟩^[Y:★∼X]\n" ++
  "W1  │ ─                   X→X  X→X  X⊑★ → X⊑★  ★→★   ★→★  [−Y^β]" ++
  " □ ⟨id(★) → id(★)⟩\n" ++
  "W2  │ ─                   X→X  X→X  X⊑★ → X⊑★  ★→★   ★→★  □⟨id(★" ++
  ") → id(★)⟩^[]\n" ++
  "W2  │ ─                   X→X  X→X  X⊑★ → X⊑★  ★→★   ★→★  [+X^α]" ++
  " □ ⟨−X → +X⟩\n" ++
  "W3  │ λx:X. □             X→X  X→X  X⊑X → X⊑X  X→X   X→X  λx:X. " ++
  "□\n" ++
  "W3  │ x                   X    X    X⊑X        X     X    x\n" ++
  "W0  └ 5                   ℕ    ℕ    ℕ⊑ℕ        ℕ     ℕ    5"
c12-b1-ladder-pinned = refl

-- P4 B3 (design.md D31): the matched TyBeta boundary `+X ∥ +X` PERMITS
-- αᴿ (`(permit α)`, W1 = Interior W0 +κ {α}, paying X ⊑ X); the right
-- check `X?` is a plain ⊑cast, under which the shared X is X⊑★ (W1);
-- the right's `−X` leaves X left-only with αᴿ still permitted (W2)
p4-B3-ladder-pinned : impLadder p4-B3 ≡
  "W0 = the conclusion's world\n" ++
  "  ⟨⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ]\n" ++
  "W1 = Interior W0 +κ {α}, pays X⊑X\n" ++
  "  ⟨X: X^α ⊑[X⊑★] X^α⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ]  κʷ = {α}\n" ++
  "W2 = Interior W1\n" ++
  "  ⟨X: X^α ⊑[X⊑★] ─⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ]  κʷ = {α}\n" ++
  "W3 = Interior W1\n" ++
  "  ⟨⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ]  κʷ = {α}\n" ++
  "W   left term        A    ηᴸA  ⊑          ηᴿA′  A′   right term" ++
  "\n" ++
  "──  ───────────────  ───  ───  ─────────  ────  ───  ───────────" ++
  "─────────────\n" ++
  "W0  [+X^α] □ ⟨+X⟩    ℕ    ℕ    ℕ⊑ℕ        ℕ     ℕ    [+X^α] □ ⟨+" ++
  "X⟩ (permit α)\n" ++
  "W1  ─                X    X    X⊑X        X     X    □⟨X?ℓ0⟩^[X:" ++
  "★∼X]\n" ++
  "W1  □₁ □₂            X    X    X⊑★        ★     ★    □₁ □₂\n" ++
  "W1  ├ ─              X→X  X→X  X⊑★ → X⊑★  ★→★   ★→★  [−X^α] □ ⟨i" ++
  "d(★) → id(★)⟩\n" ++
  "W2  │ λx:X. □        X→X  X→X  X⊑★ → X⊑★  ★→★   ★→★  λx:★. □\n" ++
  "W2  │ x              X    X    X⊑★        ★     ★    x\n" ++
  "W1  └ ─              X    X    X⊑★        ★     ★    □⟨X!⟩^[X:X∼" ++
  "★]\n" ++
  "W1    [−X^α] □ ⟨−X⟩  X    X    X⊑X        X     X    [−X^α] □ ⟨−" ++
  "X⟩\n" ++
  "W3    5              ℕ    ℕ    ℕ⊑ℕ        ℕ     ℕ    5"
p4-B3-ladder-pinned = refl

-- H1's FINAL PAIR (design.md D29, D31): the left's ΛX CLAIMS the
-- unnamed right rep. var α (`─ (claim α)`, W1 = W0 ⊕ᴸ⇔ α: X left-only,
-- X⊑★); +Y^β OPENS the left's next ∀ at Y; inside it +X^α REJOINS X
-- (W3: X^α ⊑[X⊑X] X^α, the mark now α's permission) and carries the
-- slot; ΛY JOINS Y
final-ladder-pinned : impLadder final ≡
  "W0 = the conclusion's world\n" ++
  "  ⟨⟩\n" ++
  "  ϱᵍ = {}  ϱˡ = {}  Ξᴸ = []  Ξᴿ = [α:=★, β:=★]\n" ++
  "W1 = W0 ⊕ᴸ⇔ α\n" ++
  "  ⟨X: X^α ⊑[X⊑★] ─⟩\n" ++
  "  ϱᵍ = {}  ϱˡ = {α⇔α}  Ξᴸ = [α abst]  Ξᴿ = [α:=★, β:=★]\n" ++
  "W2 = Interior W1\n" ++
  "  ⟨Y: ─ ⊑[X⊑X] Y^β │ X: X^α ⊑[X⊑★] ─⟩\n" ++
  "  ϱᵍ = {}  ϱˡ = {α⇔α}  Ξᴸ = [α abst]  Ξᴿ = [α:=★, β:=★]\n" ++
  "W3 = Interior W2\n" ++
  "  ⟨Y: ─ ⊑[X⊑X] Y^β │ X: X^α ⊑[X⊑X] X^α⟩\n" ++
  "  ϱᵍ = {}  ϱˡ = {α⇔α}  Ξᴸ = [α abst]  Ξᴿ = [α:=★, β:=★]\n" ++
  "W4 = Join1 W3: join Y^β\n" ++
  "  ⟨Y: Y^β ⊑[X⊑X] Y^β │ X: X^α ⊑[X⊑X] X^α⟩\n" ++
  "  ϱᵍ = {}  ϱˡ = {β⇔β, α⇔α}  Ξᴸ = [α abst, β abst]  Ξᴿ = [α:=★, β" ++
  ":=★]\n" ++
  "W   left term      A              ηᴸA            ⊑              " ++
  "              ηᴿA′   A′     right term\n" ++
  "──  ─────────────  ─────────────  ─────────────  ───────────────" ++
  "────────────  ─────  ─────  ──────────────────────────────────\n" ++
  "W0  ΛX. □          ∀X. ∀Y. X→Y→X  ∀X. ∀Y. X→Y→X  ∀X⊑★. ∀Y⊑★. X⊑★" ++
  " → Y⊑★ → X⊑★  ★→★→★  ★→★→★  ─ (claim α)\n" ++
  "W1  ─              ∀Y. X→Y→X      ∀Y. X→Y→X      ∀Y⊑★. X⊑★ → Y⊑★" ++
  " → X⊑★        ★→★→★  ★→★→★  □⟨id(★) → (id(★) → id(★))⟩^[]\n" ++
  "W1  ─ (open Y^β)   ∀Y. X→Y→X      ∀Y. X→Y→X      ∀Y⊑★. X⊑★ → Y⊑★" ++
  " → X⊑★        ★→★→★  ★→★→★  [+Y^β] □ ⟨id(★) → (−Y → id(★))⟩\n" ++
  "W2  ─              ∀Y. X→Y→X      X→Y→X          X⊑★ → Y⊑Y → X⊑★" ++
  "              ★→Y→★  ★→Y→★  □⟨id(★) → (id(Y) → id(★))⟩^[Y:X∼X]\n" ++
  "W2  ─ (carry Y^β)  ∀Y. X→Y→X      X→Y→X          X⊑★ → Y⊑Y → X⊑★" ++
  "              ★→Y→★  ★→Y→★  [+X^α] □ ⟨−X → (id(Y) → +X)⟩\n" ++
  "W3  ΛY. □          ∀Y. X→Y→X      X→Y→X          X⊑X → Y⊑Y → X⊑X" ++
  "              X→Y→X  X→Y→X  ─ (join Y^β)\n" ++
  "W4  λx:X. □        X→Y→X          X→Y→X          X⊑X → Y⊑Y → X⊑X" ++
  "              X→Y→X  X→Y→X  λx:X. □\n" ++
  "W4  λy:Y. □        Y→X            Y→X            Y⊑Y → X⊑X      " ++
  "              Y→X    Y→X    λy:Y. □\n" ++
  "W4  x              X              X              X⊑X            " ++
  "              X      X      x"
final-ladder-pinned = refl

-- the same pair with no opening: both left binders claim (W1, W2),
-- both right boundaries rejoin (W3, W4)
final-no-push-ladder-pinned : impLadder final-no-push ≡
  "W0 = the conclusion's world\n" ++
  "  ⟨⟩\n" ++
  "  ϱᵍ = {}  ϱˡ = {}  Ξᴸ = []  Ξᴿ = [α:=★, β:=★]\n" ++
  "W1 = W0 ⊕ᴸ⇔ α\n" ++
  "  ⟨X: X^α ⊑[X⊑★] ─⟩\n" ++
  "  ϱᵍ = {}  ϱˡ = {α⇔α}  Ξᴸ = [α abst]  Ξᴿ = [α:=★, β:=★]\n" ++
  "W2 = W1 ⊕ᴸ⇔ β\n" ++
  "  ⟨Y: Y^β ⊑[X⊑★] ─ │ X: X^α ⊑[X⊑★] ─⟩\n" ++
  "  ϱᵍ = {}  ϱˡ = {β⇔β, α⇔α}  Ξᴸ = [α abst, β abst]  Ξᴿ = [α:=★, β" ++
  ":=★]\n" ++
  "W3 = Interior W2\n" ++
  "  ⟨Y: Y^β ⊑[X⊑X] Y^β │ X: X^α ⊑[X⊑★] ─⟩\n" ++
  "  ϱᵍ = {}  ϱˡ = {β⇔β, α⇔α}  Ξᴸ = [α abst, β abst]  Ξᴿ = [α:=★, β" ++
  ":=★]\n" ++
  "W4 = Interior W3\n" ++
  "  ⟨Y: Y^β ⊑[X⊑X] Y^β │ X: X^α ⊑[X⊑X] X^α⟩\n" ++
  "  ϱᵍ = {}  ϱˡ = {β⇔β, α⇔α}  Ξᴸ = [α abst, β abst]  Ξᴿ = [α:=★, β" ++
  ":=★]\n" ++
  "W   left term  A              ηᴸA            ⊑                  " ++
  "          ηᴿA′   A′     right term\n" ++
  "──  ─────────  ─────────────  ─────────────  ───────────────────" ++
  "────────  ─────  ─────  ──────────────────────────────────\n" ++
  "W0  ΛX. □      ∀X. ∀Y. X→Y→X  ∀X. ∀Y. X→Y→X  ∀X⊑★. ∀Y⊑★. X⊑★ → Y" ++
  "⊑★ → X⊑★  ★→★→★  ★→★→★  ─ (claim α)\n" ++
  "W1  ΛY. □      ∀Y. X→Y→X      ∀Y. X→Y→X      ∀Y⊑★. X⊑★ → Y⊑★ → X" ++
  "⊑★        ★→★→★  ★→★→★  ─ (claim β)\n" ++
  "W2  ─          X→Y→X          X→Y→X          X⊑★ → Y⊑★ → X⊑★    " ++
  "          ★→★→★  ★→★→★  □⟨id(★) → (id(★) → id(★))⟩^[]\n" ++
  "W2  ─          X→Y→X          X→Y→X          X⊑★ → Y⊑★ → X⊑★    " ++
  "          ★→★→★  ★→★→★  [+Y^β] □ ⟨id(★) → (−Y → id(★))⟩\n" ++
  "W3  ─          X→Y→X          X→Y→X          X⊑★ → Y⊑Y → X⊑★    " ++
  "          ★→Y→★  ★→Y→★  □⟨id(★) → (id(Y) → id(★))⟩^[Y:X∼X]\n" ++
  "W3  ─          X→Y→X          X→Y→X          X⊑★ → Y⊑Y → X⊑★    " ++
  "          ★→Y→★  ★→Y→★  [+X^α] □ ⟨−X → (id(Y) → +X)⟩\n" ++
  "W4  λx:X. □    X→Y→X          X→Y→X          X⊑X → Y⊑Y → X⊑X    " ++
  "          X→Y→X  X→Y→X  λx:X. □\n" ++
  "W4  λy:Y. □    Y→X            Y→X            Y⊑Y → X⊑X          " ++
  "          Y→X    Y→X    λy:Y. □\n" ++
  "W4  x          X              X              X⊑X                " ++
  "          X      X      x"
final-no-push-ladder-pinned = refl

-- TwoGen's G2 (design.md D31): the outer `+Y^β` creates the slots
-- [_, Y] (the left's outer ∀ SKIPPED, `∀Z⊑★. …`) and permits β; the
-- inner `+X^α` carries them and FILLS the skip with X, permitting α;
-- the left's two gen layers CONSUME both openings (no world change)
g2-final-ladder-pinned : impLadder TwoGen.g2-final ≡
  "W0 = the conclusion's world\n" ++
  "  ⟨⟩\n" ++
  "  ϱᵍ = {}  ϱˡ = {}  Ξᴸ = []  Ξᴿ = [α:=★, β:=★]\n" ++
  "W1 = Interior W0 +κ {β}, pays ∀Z⊑★. Z⊑★ → Y⊑Y → Z⊑★\n" ++
  "  ⟨Y: ─ ⊑[X⊑★] Y^β⟩\n" ++
  "  ϱᵍ = {}  ϱˡ = {}  Ξᴸ = []  Ξᴿ = [α:=★, β:=★]  κʷ = {β}\n" ++
  "W2 = Interior W1 +κ {α}, pays X⊑X → Y⊑Y → X⊑X\n" ++
  "  ⟨Y: ─ ⊑[X⊑★] Y^β │ X: ─ ⊑[X⊑★] X^α⟩\n" ++
  "  ϱᵍ = {}  ϱˡ = {}  Ξᴸ = []  Ξᴿ = [α:=★, β:=★]  κʷ = {α, β}\n" ++
  "W3 = Interior W2\n" ++
  "  ⟨⟩\n" ++
  "  ϱᵍ = {}  ϱˡ = {}  Ξᴸ = []  Ξᴿ = [α:=★, β:=★]  κʷ = {α, β}\n" ++
  "W   left term                                    A              " ++
  "ηᴸA            ⊑                            ηᴿA′   A′     right " ++
  "term\n" ++
  "──  ───────────────────────────────────────────  ─────────────  " ++
  "─────────────  ───────────────────────────  ─────  ─────  ──────" ++
  "──────────────────────────────────\n" ++
  "W0  ─                                            ∀X. ∀Y. X→Y→X  " ++
  "∀X. ∀Y. X→Y→X  ∀X⊑★. ∀Y⊑★. X⊑★ → Y⊑★ → X⊑★  ★→★→★  ★→★→★  □⟨id(★" ++
  ") → (id(★) → id(★))⟩^[]\n" ++
  "W0  ─ (skip, open Y^β, permit β)                 ∀X. ∀Y. X→Y→X  " ++
  "∀X. ∀Y. X→Y→X  ∀X⊑★. ∀Y⊑★. X⊑★ → Y⊑★ → X⊑★  ★→★→★  ★→★→★  [+Y^β]" ++
  " □ ⟨id(★) → (−Y → id(★))⟩\n" ++
  "W1  ─                                            ∀X. ∀Y. X→Y→X  " ++
  "∀Z. Z→Y→Z      ∀Z⊑★. Z⊑★ → Y⊑Y → Z⊑★        ★→Y→★  ★→Y→★  □⟨id(★" ++
  ") → (id(Y) → id(★))⟩^[Y:X∼X]\n" ++
  "W1  ─ (carry _, Y^β, fill _ with X^α, permit α)  ∀X. ∀Y. X→Y→X  " ++
  "∀Z. Z→Y→Z      ∀Z⊑★. Z⊑★ → Y⊑Y → Z⊑★        ★→Y→★  ★→Y→★  [+X^α]" ++
  " □ ⟨−X → (id(Y) → +X)⟩\n" ++
  "W2  ─                                            ∀X. ∀Y. X→Y→X  " ++
  "X→Y→X          X⊑X → Y⊑Y → X⊑X              X→Y→X  X→Y→X  □⟨X! →" ++
  " (Y! → X?ℓ0)⟩^[X:★∼X, Y:★∼X]\n" ++
  "W2  □⟨gen X. (gen Y. (X! → (Y! → X?ℓ0)))⟩^[]     ∀X. ∀Y. X→Y→X  " ++
  "X→Y→X          X⊑★ → Y⊑★ → X⊑★              ★→★→★  ★→★→★  ─ (con" ++
  "sume X^α, consume Y^β)\n" ++
  "W2  ─                                            ★→★→★          " ++
  "★→★→★          ★⊑★ → ★⊑★ → ★⊑★              ★→★→★  ★→★→★  [−Y^β," ++
  " −X^α] □ ⟨id(★) → (id(★) → id(★))⟩\n" ++
  "W3  λx:★. □                                      ★→★→★          " ++
  "★→★→★          ★⊑★ → ★⊑★ → ★⊑★              ★→★→★  ★→★→★  λx:★. " ++
  "□\n" ++
  "W3  λy:★. □                                      ★→★            " ++
  "★→★            ★⊑★ → ★⊑★                    ★→★    ★→★    λy:★. " ++
  "□\n" ++
  "W3  x                                            ★              " ++
  "★              ★⊑★                          ★      ★      x"
g2-final-ladder-pinned = refl
