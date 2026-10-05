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
--       names it embeds, `─` where a side skips it, and its mark m),
--       the paired rep. vars `ϱᵍ`, `ϱˡ` (left ⇔ right), the two
--       stores `Ξᴸ`, `Ξᴿ` (oldest rep. var first), and, when there are
--       any, the PENDING right names `πʷ = [Y^β, …]` (design.md D27;
--       next pop first).
--     - THE LADDER: one row per derivation node, outside in, with
--       columns: W (the row's world), the left term fragment, A, ηᴸA,
--       the ⊑ evidence, ηᴿA′, A′, the right term fragment.  A fragment
--       shows only the syntax the node contributes: `□` is a child
--       (`□₁ □₂` for ·⊑·, whose children are drawn as a ├/└ tree) and
--       `─` the silent side of a one-sided rule (cast⊑, ⊑cast, Λ⊑, ν⊑,
--       ⟪⟫⊑, ⊑⟪⟫; blame⊑ prints the whole right term instead).
--     - PENDING NAMES (D27) appear in the silent column of the
--       one-sided rule that moves them: `─ (push Y^β)` and
--       `─ (carry Y^β)` for ⊑⟪⟫, `─ (pass Y^β)` for ⟪⟫⊑ and a ∀ᵖ
--       cast⊑, `─ (pop Y^β)` for Λ⊑ and a genᵖ cast⊑.  The ηᴸA and ⊑
--       columns read the left type OPENED at the pending names (one ∀
--       stripped per name, `_⊑ᵂπ⟨_⟩_`).  A pop's premise world is
--       `Open1 Wn: pop Y^β`.
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
--     counterexample K's `lk₁⊑rk₃` (push, carry, pass, pop) and `VL⊑RF`
--     (push, pass, pop), and the rebasing block `c12-b1`.

open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_; map; reverse; foldr)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _∸_; _⊔_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.String using (String; _++_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; `_; `ℕ; `𝔹; ★; _⇒_; `∀; Renameᵗ; renameᵗ)
open import Ctx using (Ctxᵗ; reps; names; underΛ)
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

-- walk the two embeddings of one center together
centerEntries : ∀ {η η′ Ω}
  → List (String × String) → List (String × String)
  → η ↪ Ω → η′ ↪ Ω → List CEntry
centerEntries ls rs []↪ []↪ = []
centerEntries ls rs (keep {m = m} ι) (keep ι′) =
  centry (just (hd ls)) m (just (hd rs)) ∷ centerEntries (tl ls) (tl rs) ι ι′
centerEntries ls rs (keep {m = m} ι) (skip ι′) =
  centry (just (hd ls)) m nothing ∷ centerEntries (tl ls) rs ι ι′
centerEntries ls rs (skip {m = m} ι) (keep ι′) =
  centry nothing m (just (hd rs)) ∷ centerEntries ls (tl rs) ι ι′
centerEntries ls rs (skip {m = m} ι) (skip ι′) =
  centry nothing m nothing ∷ centerEntries ls rs ι ι′

worldEntries : ∀ {Δ Δ′} → World Δ Δ′ → List CEntry
worldEntries {Δ} {Δ′} W =
  centerEntries (sideNames Δ) (sideNames Δ′) (ηᴸʷ W) (ηᴿʷ W)

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

-- the two lines after `Wn = …`
worldSnapshot : ∀ {Δ Δ′} → World Δ Δ′ → String
worldSnapshot {Δ} {Δ′} W =
  "  ⟨" ++ joinBar (map (showCEntry ls) es) ++ "⟩\n" ++
  "  ϱᵍ = " ++ showRepRel eL eR (ϱᵍʷ W) ++
  "  ϱˡ = " ++ showRepRel eL eR (ϱˡʷ W) ++
  "  Ξᴸ = " ++ showReps Δ ++ "  Ξᴿ = " ++ showReps Δ′
  where
  es = worldEntries W
  ls = leftCenters es
  eL = ctxEnv Δ
  eR = ctxEnv Δ′

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

-- a world with pending names (design.md D27): the base world's two
-- lines, and `πʷ = [Y^β, …]` (next pop first) when there is one
worldSnapshotπ : ∀ {Δ Δ′} → Worldπ Δ Δ′ → String
worldSnapshotπ {Δ′ = Δ′} (wπ W [])         = worldSnapshot W
worldSnapshotπ {Δ′ = Δ′} (wπ W ks@(_ ∷ _)) =
  worldSnapshot W ++ "  πʷ = [" ++ sideNameList Δ′ ks ++ "]"

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

-- the opened left type and the evidence of an index `_⊑ᵂπ⟨_⟩_`
-- (OpenImp): one `∀` stripped per pending name
openTy : List ℕ → Renameᵗ → Ty → Ty
openTy []       ρ A      = renameᵗ ρ A
openTy (c ∷ cs) ρ (`∀ A) = openTy cs (c ⊳ ρ) A
openTy (c ∷ cs) ρ A      = renameᵗ ρ A

openEv : List String → ∀ {μ} cs ρ A {B} → OpenImp μ cs ρ A B → String
openEv ns []       ρ A        p = showImp ns p
openEv ns (c ∷ cs) ρ (`∀ A)   p = openEv ns cs (c ⊳ ρ) A p
openEv ns (c ∷ cs) ρ (` X)    ()
openEv ns (c ∷ cs) ρ `ℕ       ()
openEv ns (c ∷ cs) ρ `𝔹       ()
openEv ns (c ∷ cs) ρ ★        ()
openEv ns (c ∷ cs) ρ (A ⇒ A′) ()

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
pushWorld : ∀ {Δ Δ′} → String → Worldπ Δ Δ′ → Acc → Acc
pushWorld prov W (acc rs ws nw) =
  acc rs ((label nw ++ " = " ++ prov ++ "\n" ++ worldSnapshotπ W) ∷ ws)
    (suc nw)

-- the type columns of a node at world W (the left type opened at the
-- pending names, design.md D27)
typeCols : ∀ {Δ Δ′} (W : Worldπ Δ Δ′) (A A′ : Ty)
  → A ⊑ᵂπ⟨ W ⟩ A′ → List String
typeCols {Δ} {Δ′} (wπ W π) A A′ p =
  showTy (onames (ctxEnv Δ)) A ∷ showTy cn (openTy cs (emb (ηᴸʷ W)) A) ∷
  openEv cn cs (emb (ηᴸʷ W)) A p ∷ showTy cn (embᴿ W A′) ∷
  showTy (onames (ctxEnv Δ′)) A′ ∷ []
  where
  cn = centerNames W
  cs = map (emb (ηᴿʷ W)) π

-- the row of a derivation node
nodeRow : ∀ {Δ Δ′} {W : Worldπ Δ Δ′} {γ : CtxImp (wᵇ W)} {M M′ A A′}
    {p : A ⊑ᵂπ⟨ W ⟩ A′}
  → ℕ → String → String → String
  → W ∣ γ ⊢ M ⊑ M′ ∶ p → Row
nodeRow {W = W} {A = A} {A′ = A′} {p = p} n pre l r d =
  label n ∷ (pre ++ l) ∷ (typeCols W A A′ p Data.List.++ (r ∷ []))

-- the silent side of a one-sided rule, with what it does to the
-- pending names (D27): `pop Y^β`, `pass Y^β`, `push Y^β`, `carry Y^β`
silent : String → String → String
silent what ks = "─ (" ++ what ++ " " ++ ks ++ ")"

castNote : ∀ {M c π πₚ} → Ctxᵗ → CastClaim M c π πₚ → String
castNote Δ′ cc-plain                 = "─"
castNote Δ′ (cc-∀ {k = k} _ _)       = silent "pass" (sideName Δ′ k)
castNote Δ′ (cc-gen {k = k} _)       = silent "pop" (sideName Δ′ k)

bdyNote : ∀ {M c π} → Ctxᵗ → BdyClaim M c π → String
bdyNote Δ′ bc-plain              = "─"
bdyNote Δ′ (bc-∀ {k = k} {π} _ _) = silent "pass" (sideNameList Δ′ (k ∷ π))

-- `push`'s carried names (exterior positions) and new names (interior)
pushNote : ∀ {Θ′ M π πᵢ} → Ctxᵗ → Ctxᵗ → Push Θ′ M π πᵢ → String
pushNote {π = π} Δ′ Δ′ᵢ (push {new = new} _ _ _) = note π new
  where
  note : List ℕ → List ℕ → String
  note []          []          = "─"
  note []          ns@(_ ∷ _)  = silent "push" (sideNameList Δ′ᵢ ns)
  note ks@(_ ∷ _)  []          = silent "carry" (sideNameList Δ′ ks)
  note ks@(_ ∷ _)  ns@(_ ∷ _)  =
    "─ (carry " ++ sideNameList Δ′ ks ++ ", push " ++ sideNameList Δ′ᵢ ns
    ++ ")"

-- `go a n pre pre′ x tms d`: d's rows, outside in; n is d's world, pre
-- the tree prefix of d's row and pre′ that of its children, x the
-- λ-depth and tms the term variables' names
go : ∀ {Δ Δ′} {W : Worldπ Δ Δ′} {γ : CtxImp (wᵇ W)} {M M′ A A′}
    {p : A ⊑ᵂπ⟨ W ⟩ A′}
  → Acc → ℕ → String → String → ℕ → List String
  → W ∣ γ ⊢ M ⊑ M′ ∶ p → Acc
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
go {Δ} a n pre pre′ x tms d@(cast⊑ {μ = μ} {c = c} cc-plain M _ _) =
  go (pushRow (nodeRow n pre (castFrag Δ μ c) "─" d) a) n pre′ pre′ x tms M
go {Δ} {Δ′} a n pre pre′ x tms
    d@(cast⊑ {W = W} {πₚ = πₚ} {μ = μ} {c = c} cc@(cc-∀ _ _) M _ _) =
  go (pushWorld (label n ++ " cast " ++ castNote Δ′ cc) (wπ W πₚ) a₁)
    (nextW a₁) pre′ pre′ x tms M
  where
  a₁ = pushRow (nodeRow n pre (castFrag Δ μ c) (castNote Δ′ cc) d) a
go {Δ} {Δ′} a n pre pre′ x tms
    d@(cast⊑ {W = W} {μ = μ} {c = c} cc@(cc-gen _) M _ _) =
  go (pushWorld (label n ++ " cast " ++ castNote Δ′ cc) ⌈ W ⌉ a₁)
    (nextW a₁) pre′ pre′ x tms M
  where
  a₁ = pushRow (nodeRow n pre (castFrag Δ μ c) (castNote Δ′ cc) d) a
go {Δ′ = Δ′} a n pre pre′ x tms d@(⊑cast {μ′ = μ′} {c′ = c′} M _ _) =
  go (pushRow (nodeRow n pre "─" (castFrag Δ′ μ′ c′) d) a)
    n pre′ pre′ x tms M
go {Δ} {Δ′} a n pre pre′ x tms d@(Λ⊑Λ {W = W} _ _ _ V _) =
  go (pushWorld (label n ++ " ⊕ X⊑X") ⌈ W ⊕ X⊑X ⌉ a₁)
    (nextW a₁) pre′ pre′ x tms V
  where a₁ = pushRow (nodeRow n pre (tyLamFrag Δ) (tyLamFrag Δ′) d) a
go {Δ} {Δ′} a n pre pre′ x tms
    d@(Λ⊑ {W₁ = W₁} (claim-fresh {W = W}) _ _ _ _ V _) =
  go (pushWorld (label n ++ " ⊕ᴸ") W₁ a₁) (nextW a₁) pre′ pre′ x tms V
  where a₁ = pushRow (nodeRow n pre (tyLamFrag Δ) "─" d) a
go {Δ} {Δ′} a n pre pre′ x tms
    d@(Λ⊑ {W₁ = W₁} (claim-pop {k = k} _) _ _ _ _ V _) =
  go (pushWorld ("Open1 " ++ label n ++ ": pop " ++ sideName Δ′ k) W₁ a₁)
    (nextW a₁) pre′ pre′ x tms V
  where
  a₁ = pushRow (nodeRow n pre (tyLamFrag Δ) (silent "pop" (sideName Δ′ k))
                 d) a
go {Δ} {Δ′} a n pre pre′ x tms
    d@(ν⊑ν {A = A} {A′ = A′} {c = c} {c′ = c′} L _ _ _ _ _) =
  go (pushRow (nodeRow n pre (nuFrag Δ A c) (nuFrag Δ′ A′ c′) d) a)
    n pre′ pre′ x tms L
go {Δ} a n pre pre′ x tms d@(ν⊑ {A = A} {c = c} L _ _ _) =
  go (pushRow (nodeRow n pre (nuFrag Δ A c) "─" d) a) n pre′ pre′ x tms L
go {Δ} {Δ′} a n pre pre′ x tms
    d@(⟪⟫⊑⟪⟫ {Wᵢ = Wᵢ} {Θ = Θ} {Θ′ = Θ′} {c = c} {c′ = c′}
        _ _ M _ _ _ _) =
  go (pushWorld ("Interior " ++ label n) ⌈ Wᵢ ⌉ a₁) (nextW a₁)
    pre′ pre′ x tms M
  where
  a₁ = pushRow (nodeRow n pre (bdyFrag Δ Θ c) (bdyFrag Δ′ Θ′ c′) d) a
go {Δ} {Δ′} a n pre pre′ x tms
    d@(⟪⟫⊑ {Wᵢ = Wᵢ} {π = π} {Θ = Θ} {c = c} _ bc _ M _ _) =
  go (pushWorld ("Interior " ++ label n) (wπ Wᵢ π) a₁) (nextW a₁)
    pre′ pre′ x tms M
  where a₁ = pushRow (nodeRow n pre (bdyFrag Δ Θ c) (bdyNote Δ′ bc) d) a
go {Δ′ = Δ′} a n pre pre′ x tms
    d@(⊑⟪⟫ {Δ′ᵢ = Δ′ᵢ} {Wᵢ = Wᵢ} {πᵢ = πᵢ} {Θ′ = Θ′} {c′ = c′}
        _ pu _ M _ _) =
  go (pushWorld ("Interior " ++ label n) (wπ Wᵢ πᵢ) a₁) (nextW a₁)
    pre′ pre′ x tms M
  where
  a₁ = pushRow (nodeRow n pre (pushNote Δ′ Δ′ᵢ pu) (bdyFrag Δ′ Θ′ c′) d) a

------------------------------------------------------------------------
-- 6. Entry points
------------------------------------------------------------------------

-- the whole ladder: worlds, table
impLadder : ∀ {Δ Δ′} {W : Worldπ Δ Δ′} {γ : CtxImp (wᵇ W)} {M M′ A A′}
    {p : A ⊑ᵂπ⟨ W ⟩ A′}
  → W ∣ γ ⊢ M ⊑ M′ ∶ p → String
impLadder {W = W} d =
  joinLines (reverse (worldsA a)) ++ "\n" ++ renderTable (reverse (rowsA a))
  where
  a = go (pushWorld "the conclusion's world" W (acc [] [] zero))
         zero "" "" zero [] d

-- GTSFImp's name for the printer (there it fixed the name supplies;
-- GTNF reads names off the contexts, so the two coincide)
impLadderDefault : ∀ {Δ Δ′} {W : Worldπ Δ Δ′} {γ : CtxImp (wᵇ W)}
    {M M′ A A′} {p : A ⊑ᵂπ⟨ W ⟩ A′}
  → W ∣ γ ⊢ M ⊑ M′ ∶ p → String
impLadderDefault = impLadder

------------------------------------------------------------------------
-- 7. Pinned ladders
------------------------------------------------------------------------

-- λx:ℕ. x ⊑ λx:★. x
small-λ : ⌈ ∅ʷ ⌉ ∣ [] ⊢ ƛ `ℕ ∙ ` 0 ⊑ ƛ ★ ∙ ` 0 ∶ ⇒⊑⇒ ℕ⊑★ ℕ⊑★
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
  "W1 = W0 ⊕ X⊑X\n" ++
  "  ⟨X: X^α ⊑[X⊑X] X^α⟩\n" ++
  "  ϱᵍ = {}  ϱˡ = {α⇔α}  Ξᴸ = [α abst]  Ξᴿ = [α abst]\n" ++
  "W   left term  A        ηᴸA      ⊑              ηᴿA′     A′       " ++
  "right term\n" ++
  "──  ─────────  ───────  ───────  ─────────────  ───────  ───────  " ++
  "──────────\n" ++
  "W0  ΛX. □      ∀X. X→X  ∀X. X→X  ∀X. X⊑X → X⊑X  ∀X. X→X  ∀X. X→X  " ++
  "ΛX. □\n" ++
  "W1  λx:X. □    X→X      X→X      X⊑X → X⊑X      X→X      X→X      " ++
  "λx:X. □\n" ++
  "W1  x          X        X        X⊑X            X        X        " ++
  "x"
ΛI⊑ΛI-ladder-pinned = refl

lk₁⊑rk₃-ladder-pinned : impLadder lk₁⊑rk₃ ≡
  "W0 = the conclusion's world\n" ++
  "  ⟨⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ, β:=★]\n" ++
  "W1 = Interior W0\n" ++
  "  ⟨Y: ─ ⊑[X⊑★] Y^β⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ, β:=★]  πʷ = [Y^β" ++
  "]\n" ++
  "W2 = Interior W1\n" ++
  "  ⟨Y: ─ ⊑[X⊑★] Y^β │ X: ─ ⊑[X⊑X] X^α⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ, β:=★]  πʷ = [Y^β" ++
  "]\n" ++
  "W3 = Interior W2\n" ++
  "  ⟨Y: ─ ⊑[X⊑★] Y^β │ X: X^α ⊑[X⊑X] X^α⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ, β:=★]  πʷ = [Y^β" ++
  "]\n" ++
  "W4 = Open1 W3: pop Y^β\n" ++
  "  ⟨Y: Y^β ⊑[X⊑★] Y^β │ X: X^α ⊑[X⊑X] X^α⟩\n" ++
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
  "W0    ─ (push Y^β)                    ∀X. X→X            ∀X. X→X" ++
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
  "       ─ (pop Y^β)\n" ++
  "W4    λx:Y. □                         Y→Y                Y→Y    " ++
  "            Y⊑Y → Y⊑Y                            Y→Y        Y→Y " ++
  "       λx:Y. □\n" ++
  "W4    x                               Y                  Y      " ++
  "            Y⊑Y                                  Y          Y   " ++
  "       x"
lk₁⊑rk₃-ladder-pinned = refl

VL⊑RF-ladder-pinned : impLadder VL⊑RF ≡
  "W0 = the conclusion's world\n" ++
  "  ⟨⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ, β:=★]\n" ++
  "W1 = Interior W0\n" ++
  "  ⟨Y: ─ ⊑[X⊑★] Y^β │ X: ─ ⊑[X⊑X] X^α⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ, β:=★]  πʷ = [Y^β" ++
  "]\n" ++
  "W2 = Interior W1\n" ++
  "  ⟨Y: ─ ⊑[X⊑★] Y^β │ X: X^α ⊑[X⊑X] X^α⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=ℕ, β:=★]  πʷ = [Y^β" ++
  "]\n" ++
  "W3 = Open1 W2: pop Y^β\n" ++
  "  ⟨Y: Y^β ⊑[X⊑★] Y^β │ X: X^α ⊑[X⊑X] X^α⟩\n" ++
  "  ϱᵍ = {α⇔α}  ϱˡ = {β⇔β}  Ξᴸ = [α:=ℕ, β abst]  Ξᴿ = [α:=ℕ, β:=★]" ++
  "\n" ++
  "W   left term                       A        ηᴸA      ⊑         " ++
  "       ηᴿA′  A′   right term\n" ++
  "──  ──────────────────────────────  ───────  ───────  ──────────" ++
  "─────  ────  ───  ────────────────────────\n" ++
  "W0  ─                               ∀X. X→X  ∀X. X→X  ∀X⊑★. X⊑★ " ++
  "→ X⊑★  ★→★   ★→★  □⟨id(★) → id(★)⟩^[]\n" ++
  "W0  ─ (push Y^β)                    ∀X. X→X  ∀X. X→X  ∀X⊑★. X⊑★ " ++
  "→ X⊑★  ★→★   ★→★  [+Y^β, +X^α] □ ⟨−Y → +Y⟩\n" ++
  "W1  [+X^α] □ ⟨∀Y. (id(Y) → id(Y))⟩  ∀X. X→X  Y→Y      Y⊑Y → Y⊑Y " ++
  "       Y→Y   Y→Y  ─ (pass Y^β)\n" ++
  "W2  ΛY. □                           ∀Y. Y→Y  Y→Y      Y⊑Y → Y⊑Y " ++
  "       Y→Y   Y→Y  ─ (pop Y^β)\n" ++
  "W3  λx:Y. □                         Y→Y      Y→Y      Y⊑Y → Y⊑Y " ++
  "       Y→Y   Y→Y  λx:Y. □\n" ++
  "W3  x                               Y        Y        Y⊑Y       " ++
  "       Y     Y    x"
VL⊑RF-ladder-pinned = refl

c12-b1-ladder-pinned : impLadder c12-b1 ≡
  "W0 = the conclusion's world\n" ++
  "  ⟨⟩\n" ++
  "  ϱᵍ = {α⇔β, α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=★, β:=ℕ]\n" ++
  "W1 = Interior W0\n" ++
  "  ⟨X: X^α ⊑[X⊑★] Y^β⟩\n" ++
  "  ϱᵍ = {α⇔β, α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=★, β:=ℕ]\n" ++
  "W2 = Interior W1\n" ++
  "  ⟨X: X^α ⊑[X⊑★] ─⟩\n" ++
  "  ϱᵍ = {α⇔β, α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=★, β:=ℕ]\n" ++
  "W3 = Interior W2\n" ++
  "  ⟨X: X^α ⊑[X⊑★] X^α⟩\n" ++
  "  ϱᵍ = {α⇔β, α⇔α}  ϱˡ = {}  Ξᴸ = [α:=ℕ]  Ξᴿ = [α:=★, β:=ℕ]\n" ++
  "W   left term             A    ηᴸA  ⊑          ηᴿA′  A′   right te" ++
  "rm\n" ++
  "──  ────────────────────  ───  ───  ─────────  ────  ───  ────────" ++
  "────────────────\n" ++
  "W0  □₁ □₂                 ℕ    ℕ    ℕ⊑ℕ        ℕ     ℕ    □₁ □₂\n" ++
  "W0  ├ [+X^α] □ ⟨−X → +X⟩  ℕ→ℕ  ℕ→ℕ  ℕ⊑ℕ → ℕ⊑ℕ  ℕ→ℕ   ℕ→ℕ  [+Y^β] □" ++
  " ⟨−Y → +Y⟩\n" ++
  "W1  │ ─                   X→X  X→X  X⊑X → X⊑X  X→X   Y→Y  □⟨Y! → Y" ++
  "?ℓ0⟩^[Y:★∼X]\n" ++
  "W1  │ ─                   X→X  X→X  X⊑★ → X⊑★  ★→★   ★→★  [−Y^β] □" ++
  " ⟨id(★) → id(★)⟩\n" ++
  "W2  │ ─                   X→X  X→X  X⊑★ → X⊑★  ★→★   ★→★  □⟨id(★) " ++
  "→ id(★)⟩^[]\n" ++
  "W2  │ ─                   X→X  X→X  X⊑★ → X⊑★  ★→★   ★→★  [+X^α] □" ++
  " ⟨−X → +X⟩\n" ++
  "W3  │ λx:X. □             X→X  X→X  X⊑X → X⊑X  X→X   X→X  λx:X. □" ++
  "\n" ++
  "W3  │ x                   X    X    X⊑X        X     X    x\n" ++
  "W0  └ 5                   ℕ    ℕ    ℕ⊑ℕ        ℕ     ℕ    5"
c12-b1-ladder-pinned = refl
