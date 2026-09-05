module strong.Oblig where

-- WHAT EACH BOUNDARY IS ASKED TO PROVIDE — an instrument that IGNORES
-- THE CURRENT BOOKKEEPING ENTIRELY.  Nothing here computes γᵇ, ρᵇ,
-- intOf, ⟦·⟧ᴴ, dualᴳ or any context entry: the only inputs are the TERM
-- (which is annotated) and a TOP-DOWN DEMAND.  So a row of this table is
-- a REQUIREMENT on a boundary, stated in a vocabulary any redesign can
-- read: "at this occurrence a boundary must present a value of TYPE t
-- to its exterior, over a body of TYPE s, and here are the type
-- variables each side mentions".
--
-- THE THREE PIECES
--
--   synthTy : List Ty → Term → Maybe Ty
--       bottom-up synthesis from the term alone.  The List Ty is the
--       stack of enclosing λ annotations.  A WRAPPER is where synthesis
--       stops looking inside: without bookkeeping there is no way to
--       read a boundary's exterior face off the term, so the wrapper's
--       type is whatever the DEMAND says, and `nothing` when there is
--       no demand.  Partial by design — this is an instrument.
--
--   obligs : Ty → Term → List Oblig
--       the top demand plus the term, giving one record per BOUNDARY
--       OCCURRENCE (nested ones included), each with its own local
--       demand.  Demands propagate: a function position demands
--       (synth of the argument) ⇒ goal; an argument position demands
--       the function's synthesized domain; ·[B,A] demands ∀B; a λ under
--       an arrow demand passes the codomain down; Λ under a ∀ demand
--       passes the body down.
--
--   obligLog : ℕ → TCtx → Ty → Term → String
--       the trace of strong.Eval with, under every state, that state's
--       obligation table — and strong.EvalLog's event line between the
--       states.  SYNTHESIS DOES NOT NEED THE STATE TO BE WELL TYPED,
--       which is the whole point: the rows for the states AFTER a
--       preservation break say what the boundary there would have had
--       to provide.
--
-- NAMING.  Rows carry the two supplies strong.Show would use at that
-- occurrence — the exterior one, and the interior one (reveal names,
-- then the exterior past the dropped block) — so `int` and `ext` are
-- legible in their own frames, side by side.  THE FRAMES ARE DIFFERENT
-- AND THE ROW SAYS SO; that correspondence is exactly the thing the
-- bookkeeping exists to establish.

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_)
open import Data.String using (String) renaming (_++_ to _⧺_)
open import strong.Types
open import strong.Context using (TCtx; Ctx; ⤊)
open import strong.Boundary
open import strong.BReduction using (_⊢_-→_)
open import strong.Eval using (Step; stepΣ)
open import strong.EvalLog using (event; fvsAt; nl; evLine)
open import strong.Show
  using (Supply; tyBinder; extS; showTy; showBnd; revNames; intSup;
         showTmIn)

------------------------------------------------------------------------
-- Maybe-Ty plumbing: the four ways a demand travels
------------------------------------------------------------------------

domOf : Maybe Ty → Maybe Ty                  -- the domain of an arrow
domOf (just (A ⇒ B)) = just A
domOf (just (` X))   = nothing
domOf (just `ℕ)      = nothing
domOf (just `𝔹)      = nothing
domOf (just (`∀ A))  = nothing
domOf nothing        = nothing

codOf : Maybe Ty → Maybe Ty                  -- the codomain of an arrow
codOf (just (A ⇒ B)) = just B
codOf (just (` X))   = nothing
codOf (just `ℕ)      = nothing
codOf (just `𝔹)      = nothing
codOf (just (`∀ A))  = nothing
codOf nothing        = nothing

allOf : Maybe Ty → Maybe Ty                  -- the body of a ∀
allOf (just (`∀ A))  = just A
allOf (just (` X))   = nothing
allOf (just `ℕ)      = nothing
allOf (just `𝔹)      = nothing
allOf (just (A ⇒ B)) = nothing
allOf nothing        = nothing

arrowD : Maybe Ty → Maybe Ty → Maybe Ty      -- argument type ⇒ goal
arrowD (just A) (just G) = just (A ⇒ G)
arrowD (just A) nothing  = nothing
arrowD nothing  g        = nothing

orElse : Maybe Ty → Maybe Ty → Maybe Ty
orElse (just A) g = just A
orElse nothing  g = g

lookupTy : List Ty → ℕ → Maybe Ty
lookupTy []      x       = nothing
lookupTy (A ∷ Γ) zero    = just A
lookupTy (A ∷ Γ) (suc x) = lookupTy Γ x

------------------------------------------------------------------------
-- SYNTHESIS.  Bottom-up, preferring what the term provides, falling
-- back on the demand where the term is silent (a wrapper, or a body
-- whose own synthesis failed).
------------------------------------------------------------------------

synthD : List Ty → Maybe Ty → Term → Maybe Ty
synthD Γ g (` x)          = lookupTy Γ x
synthD Γ g ($ n)          = just `ℕ
synthD Γ g (ƛ A ∙ N)      with synthD (A ∷ Γ) (codOf g) N
synthD Γ g (ƛ A ∙ N)      | just B  = just (A ⇒ B)
synthD Γ g (ƛ A ∙ N)      | nothing = g
-- an application: try the function BARE first (a λ or a type
-- application types itself), and only then fall back on the
-- demand-driven route (argument type ⇒ goal), which is all there is
-- when the function position is itself a boundary
synthD Γ g (L · M)        with synthD Γ nothing L
synthD Γ g (L · M)        | just (A ⇒ B) = just B
synthD Γ g (L · M)        | just (` X)   = g
synthD Γ g (L · M)        | just `ℕ      = g
synthD Γ g (L · M)        | just `𝔹      = g
synthD Γ g (L · M)        | just (`∀ A)  = g
synthD Γ g (L · M)        | nothing      =
  orElse (codOf (synthD Γ (arrowD (synthD Γ nothing M) g) L)) g
synthD Γ g (Λ N)          with synthD (⤊ Γ) (allOf g) N
synthD Γ g (Λ N)          | just C  = just (`∀ C)
synthD Γ g (Λ N)          | nothing = g
synthD Γ g (L ·[ B , A ]) = just (B [ A ]ᵗ)
synthD Γ g (M ⟪ Θ , B₀ ⟫) = g          -- STOPS HERE: an obligation site

synthTy : List Ty → Term → Maybe Ty
synthTy Γ M = synthD Γ nothing M

------------------------------------------------------------------------
-- THE VARIABLES A SIDE MENTIONS.  For a type: its free indices.  For
-- the interior TERM: the indices its own annotations, type arguments
-- and boundary entries name — read in the interior's OWN frame (a
-- nested boundary's reveal reps and conceal INDICES live there; its
-- conceal reps and B₀ do not, and are skipped).
------------------------------------------------------------------------

fvsM : Maybe Ty → List ℕ
fvsM (just A) = fvsAt 0 A
fvsM nothing  = []

idxAt : ℕ → ℕ → List ℕ                       -- a frame index, under d
idxAt d X = if X <ᵇ d then [] else (X ∸ d) ∷ []

bndVars : ℕ → BCtx → List ℕ
bndVars d []            = []
bndVars d (rvl A ∷ Θ)   = fvsAt d A ++ bndVars d Θ
bndVars d (rvl⋆ ∷ Θ)    = bndVars d Θ
bndVars d (cnc X A ∷ Θ) = idxAt d X ++ bndVars d Θ
bndVars d (cnc⋆ X ∷ Θ)  = idxAt d X ++ bndVars d Θ

memb : ℕ → List ℕ → Bool
memb x []       = false
memb x (y ∷ ys) = (x ≡ᵇ y) ∨ memb x ys

nub : List ℕ → List ℕ
nub []       = []
nub (x ∷ xs) = if memb x (nub xs) then nub xs else x ∷ nub xs

varList : Supply → List ℕ → String
varList sup []           = "-"
varList sup (X ∷ [])     = sup X
varList sup (X ∷ Y ∷ Xs) = sup X ⧺ "," ⧺ varList sup (Y ∷ Xs)

mshow : ℕ → Supply → Maybe Ty → String
mshow d sup (just A) = showTy d sup A
mshow d sup nothing  = "?"

isWrap : Term → Bool
isWrap (` x)          = false
isWrap ($ n)          = false
isWrap (ƛ A ∙ N)      = false
isWrap (L · M)        = false
isWrap (Λ N)          = false
isWrap (L ·[ B , A ]) = false
isWrap (M ⟪ Θ , B₀ ⟫) = true

tyVarsTm : ℕ → Term → List ℕ
tyVarsTm d (` x)          = []
tyVarsTm d ($ n)          = []
tyVarsTm d (ƛ A ∙ N)      = fvsAt d A ++ tyVarsTm d N
tyVarsTm d (L · M)        = tyVarsTm d L ++ tyVarsTm d M
tyVarsTm d (Λ N)          = tyVarsTm (suc d) N
tyVarsTm d (L ·[ B , A ]) =
  tyVarsTm d L ++ fvsAt (suc d) B ++ fvsAt d A
tyVarsTm d (M ⟪ Θ , B₀ ⟫) = bndVars d Θ

------------------------------------------------------------------------
-- THE RECORD
------------------------------------------------------------------------

record Oblig : Set where
  constructor mkOb
  field
    obDepth : ℕ            -- boundary-nesting depth (0 = outermost)
    obTd    : ℕ            -- Show's binder depth OUTSIDE the boundary
    obExt   : Supply       -- exterior type-variable names
    obInt   : Supply       -- interior type-variable names
    obΘ     : BCtx         -- the boundary as written
    obB₀    : Ty           -- its face as written
    obIntTy : Maybe Ty     -- synthesized from the interior TERM
    obExtTy : Maybe Ty     -- the top-down DEMAND at the occurrence
    obIntVs : List ℕ       -- variables the interior mentions
    obExtVs : List ℕ       -- variables the demand mentions
    obNest  : Bool         -- the interior is ITSELF a boundary
    obNote  : String       -- a PARTIAL demand, where no full one exists

open Oblig public

------------------------------------------------------------------------
-- COLLECTING the occurrences, with their local demands
------------------------------------------------------------------------

-- an EMPTY boundary translates nothing, so its interior faces the same
-- demand its exterior does.  Any other boundary changes the frame, and
-- what the interior is asked for is NOT determined by the term alone —
-- which is exactly what the bookkeeping is there to supply.
intDemand : BCtx → Maybe Ty → Maybe Ty
intDemand []      g = g
intDemand (_ ∷ _) g = nothing

-- `nt` is a PARTIAL demand in words, for the occurrences where the term
-- alone fixes no full type (a boundary in function position whose
-- argument is itself a boundary — the shape that the chain of
-- bookkeeping, and nothing else, ties together).
obsOf : ℕ → ℕ → Supply → List Ty → Maybe Ty → String → Term
      → List Oblig
obsOf k td sup Γ g nt (` x)     = []
obsOf k td sup Γ g nt ($ n)     = []
obsOf k td sup Γ g nt (ƛ A ∙ N) =
  obsOf k td sup (A ∷ Γ) (codOf g) "" N
obsOf k td sup Γ g nt (L · M)   with synthD Γ nothing L
obsOf k td sup Γ g nt (L · M)   | just (A ⇒ B) =
     obsOf k td sup Γ (just (A ⇒ B)) "" L
  ++ obsOf k td sup Γ (just A) "" M
obsOf k td sup Γ g nt (L · M)   | just (` X)  =
     obsOf k td sup Γ (just (` X)) "" L
  ++ obsOf k td sup Γ nothing "" M
obsOf k td sup Γ g nt (L · M)   | just `ℕ     =
     obsOf k td sup Γ (just `ℕ) "" L ++ obsOf k td sup Γ nothing "" M
obsOf k td sup Γ g nt (L · M)   | just `𝔹     =
     obsOf k td sup Γ (just `𝔹) "" L ++ obsOf k td sup Γ nothing "" M
obsOf k td sup Γ g nt (L · M)   | just (`∀ A) =
     obsOf k td sup Γ (just (`∀ A)) "" L
  ++ obsOf k td sup Γ nothing "" M
obsOf k td sup Γ g nt (L · M)   | nothing     =
     obsOf k td sup Γ (arrowD (synthD Γ nothing M) g)
       ("must be _⇒" ⧺ mshow td sup g ⧺ " (argument's type not "
         ⧺ "term-determined)") L
  ++ obsOf k td sup Γ
       (domOf (synthD Γ (arrowD (synthD Γ nothing M) g) L))
       "argument of a boundary-headed application" M
obsOf k td sup Γ g nt (Λ N)     =
  obsOf k (suc td) (extS sup (tyBinder td)) (⤊ Γ) (allOf g) "" N
obsOf k td sup Γ g nt (L ·[ B , A ]) =
  obsOf k td sup Γ (just (`∀ B)) "" L
obsOf k td sup Γ g nt (M ⟪ Θ , B₀ ⟫) =
  mkOb k td sup isup Θ B₀ (synthD [] nothing M) g
       (tyVarsTm 0 M) (fvsM g) (isWrap M) nt
  ∷ obsOf (suc k) (td + revs Θ) isup [] (intDemand Θ g) "" M
  where
  isup : Supply
  isup = intSup Θ (revNames td Θ) sup

obligsAt : ℕ → Ty → Term → List Oblig
obligsAt n A M = obsOf 0 n tyBinder [] (just A) "" M

obligs : Ty → Term → List Oblig
obligs = obligsAt 0

------------------------------------------------------------------------
-- RENDERING a row.  Both sides in their own frame.
------------------------------------------------------------------------

nestNote : Bool → String
nestNote true  = "   (interior is itself a boundary — next row down)"
nestNote false = ""

showOb : Oblig → String
showOb ob =
     nl ⧺ "        b" ⧺ show (obDepth ob) ⧺ " "
        ⧺ showBnd (obTd ob) (obExt ob) (obΘ ob) (obB₀ ob)
  ⧺ nl ⧺ "           int ⊢ "
        ⧺ mshow (obTd ob + revs (obΘ ob)) (obInt ob) (obIntTy ob)
        ⧺ "   mentions {"
        ⧺ varList (obInt ob) (nub (obIntVs ob)) ⧺ "}"
        ⧺ nestNote (obNest ob)
  ⧺ nl ⧺ "           ext ⊨ "
        ⧺ mshow (obTd ob) (obExt ob) (obExtTy ob)
        ⧺ "   mentions {"
        ⧺ varList (obExt ob) (nub (obExtVs ob)) ⧺ "}"
        ⧺ noteOf (obNote ob)
  where
  noteOf : String → String
  noteOf "" = ""
  noteOf s  = "   [" ⧺ s ⧺ "]"

showObs : List Oblig → String
showObs []         = ""
showObs (ob ∷ obs) = showOb ob ⧺ showObs obs

-- the table for ONE term, at a given demand and ambient length
obligTable : ℕ → Ty → Term → String
obligTable n A M with obligsAt n A M
obligTable n A M | []         = nl ⧺ "        (no boundaries)"
obligTable n A M | (ob ∷ obs) = showObs (ob ∷ obs)

------------------------------------------------------------------------
-- THE ANNOTATED, OBLIGATION-CARRYING TRACE
------------------------------------------------------------------------

obFrom : ℕ → ℕ → (Δ : TCtx) → Ty → (M : Term) → String
obFrom zero    n Δ A M =
  showTmIn n M ⧺ obligTable n A M ⧺ nl ⧺ "      [fuel exhausted]"
obFrom (suc k) n Δ A M with stepΣ Δ M
obFrom (suc k) n Δ A M | nothing =
  showTmIn n M ⧺ obligTable n A M
obFrom (suc k) n Δ A M | just (M′ , st) =
  showTmIn n M ⧺ obligTable n A M ⧺ evLine (event st)
    ⧺ nl ⧺ "  —→  " ⧺ obFrom k n Δ A M′

obligLog : ℕ → TCtx → Ty → Term → String
obligLog k Δ A M = obFrom k (length Δ) Δ A M
