module strong.Show where

-- de Bruijn → NAMED rendering for strong System F terms, types, boundary
-- context morphisms, conversions and type contexts — adapted from the name-supply
-- infrastructure of GTSFImp/proof/DGG/ImpLadder.agda (Jeremy's request,
-- 2026-09-05, after a hand-transcription error read an interior ` 0 in the
-- exterior frame), and PORTED to the conversion-boundary design.
--
-- CONVENTIONS (Jeremy's): type variables are X, Y, Z (then X′, Y′, Z′, …);
-- term binders are x, y, z, f, g, h (then primes).  V and W are reserved
-- for metavariables over term VALUES and never generated here.
--
-- THE POINT of the adaptation: a boundary changes the type-variable frame.
-- Rendering M ⟪ Θ , c ⟫ under an exterior supply `ext`:
--   * Θ's BINDS bind fresh interior slots; the interior supply is
--     [fresh names for the binders] then ext SHIFTED past them.  Nothing is
--     dropped any more (conceal masks in place), so there is exactly ONE
--     inner supply — the old `cmax` correction has no analogue, and the
--     interior supply and the CONVERSION-CONTEXT supply coincide
--     (`interior` and `convCtx` differ in blocking, not in slot layout).
--   * a BINDER's rep is shown under `ext` — a rep uses the exterior's
--     slots (the judgement reads it on `unlockedScope Θ′ Δ`, which has the
--     same slot layout as Δ);
--   * a `lock X` / `unlock X` names an EXTERIOR slot, so it is shown under
--     `ext`; neither carries a rep, which is the whole point of the
--     redesign;
--   * the CONVERSION `c` is shown under that same supply, and its
--     `seal`/`unseal` names are read there — by their type context, not by a
--     stored spelling.
--
-- USED AS A TOOL non-interactively via scripts/render_term.sh, which
-- exploits the type-error trick: `oops : e ≡ ""; oops = refl` makes Agda
-- print e's normal form in the mismatch error.

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.String using (String; _++_)
open import Data.Product using (_×_; _,_; proj₁)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx using (Ent; abst; bind; masked; Ctxᵗ)
open import strong.Conversion using (Conv; id; seal; unseal; _↦_; `∀)
open import strong.Terms
  using (Term; `_; $_; ƛ_∙_; _·_; Λ_; _·[_,_]; _⟪_,_⟫;
         CtxMorph; MorphEnt; bind; unlock; lock; numBinds)

Supply : Set
Supply = ℕ → String

------------------------------------------------------------------------
-- binder names
------------------------------------------------------------------------

primes : ℕ → String
primes zero    = ""
primes (suc n) = "′" ++ primes n

cyc3 : ℕ → String → String → String → ℕ → String
cyc3 zero                a b c p = a ++ primes p
cyc3 (suc zero)          a b c p = b ++ primes p
cyc3 (suc (suc zero))    a b c p = c ++ primes p
cyc3 (suc (suc (suc n))) a b c p = cyc3 n a b c (suc p)

tyBinder : ℕ → String
tyBinder n = cyc3 n "X" "Y" "Z" zero

cyc6 : ℕ → ℕ → String
cyc6 zero p = "x" ++ primes p
cyc6 (suc zero) p = "y" ++ primes p
cyc6 (suc (suc zero)) p = "z" ++ primes p
cyc6 (suc (suc (suc zero))) p = "f" ++ primes p
cyc6 (suc (suc (suc (suc zero)))) p = "g" ++ primes p
cyc6 (suc (suc (suc (suc (suc zero))))) p = "h" ++ primes p
cyc6 (suc (suc (suc (suc (suc (suc n)))))) p = cyc6 n (suc p)

tmBinder : ℕ → String
tmBinder n = cyc6 n zero

extS : Supply → String → Supply
extS sup b zero    = b
extS sup b (suc k) = sup k

------------------------------------------------------------------------
-- types
------------------------------------------------------------------------

showTy : ℕ → Supply → Ty → String
showTy d sup (` X)   = sup X
showTy d sup `ℕ      = "ℕ"
showTy d sup `𝔹      = "𝔹"
showTy d sup (A ⇒ B) =
  "(" ++ showTy d sup A ++ "⇒" ++ showTy d sup B ++ ")"
showTy d sup (`∀ A)  =
  "(∀" ++ tyBinder d ++ ". "
      ++ showTy (suc d) (extS sup (tyBinder d)) A ++ ")"

------------------------------------------------------------------------
-- conversions
------------------------------------------------------------------------

showConv : ℕ → Supply → Conv → String
showConv d sup (id A)     = "id " ++ showTy d sup A
showConv d sup (seal X)   = "seal " ++ sup X
showConv d sup (unseal X) = "unseal " ++ sup X
showConv d sup (s ↦ t)    =
  "(" ++ showConv d sup s ++ " ↦ " ++ showConv d sup t ++ ")"
showConv d sup (`∀ s)     =
  "(∀" ++ tyBinder d ++ ". "
      ++ showConv (suc d) (extS sup (tyBinder d)) s ++ ")"

------------------------------------------------------------------------
-- the supply a boundary induces
------------------------------------------------------------------------

-- one fresh name per BINDER, newest first (binder 0 is interior slot 0)
bindNames : ℕ → CtxMorph → List String
bindNames d []               = []
bindNames d (bind A ∷ Θ)     = tyBinder d ∷ bindNames (suc d) Θ
bindNames d (unlock X ∷ Θ)   = bindNames d Θ
bindNames d (lock X ∷ Θ)     = bindNames d Θ

nth : List String → ℕ → String
nth []       k       = "?"
nth (s ∷ ss) zero    = s
nth (s ∷ ss) (suc k) = nth ss k

-- interior (= conversion-context) supply: bind names, then ext shifted
-- past them.  No `cmax` correction: conceal masks in place, so no slot
-- is dropped.
intSup : CtxMorph → List String → Supply → Supply
intSup Θ on ext k =
  if k <ᵇ numBinds Θ then nth on k else ext (k ∸ numBinds Θ)

------------------------------------------------------------------------
-- boundary context morphisms
------------------------------------------------------------------------

sep : CtxMorph → String
sep [] = ""
sep (_ ∷ _) = " , "

tl : List String → List String
tl []       = []
tl (s ∷ ss) = ss

-- `on` is the binder-name list still to be consumed; `ext` names exterior
-- slots.  A binder's rep uses the exterior's slots; `lock`/`unlock` carry
-- a name only.
showEnts : ℕ → List String → Supply → CtxMorph → String
showEnts d on ext [] = ""
showEnts d on ext (bind A ∷ Θ) =
  "↑" ++ nth on 0 ++ ":=" ++ showTy d ext A ++ sep Θ
      ++ showEnts d (tl on) ext Θ
showEnts d on ext (lock X ∷ Θ) =
  "↓" ++ ext X ++ sep Θ ++ showEnts d on ext Θ
showEnts d on ext (unlock X ∷ Θ) =
  "↥" ++ ext X ++ sep Θ ++ showEnts d on ext Θ

showBnd : ℕ → Supply → CtxMorph → Conv → String
showBnd d ext [] c =
  "⟪ " ++ showConv d ext c ++ " ⟫"
showBnd d ext Θ@(_ ∷ _) c =
  "⟪ " ++ showEnts d on ext Θ ++ " , "
       ++ showConv (d + numBinds Θ) (intSup Θ on ext) c ++ " ⟫"
  where on = bindNames d Θ

------------------------------------------------------------------------
-- terms
------------------------------------------------------------------------

-- Binder names are GLOBALLY UNIQUE across one rendered term (Jeremy,
-- 2026-09-06: two sibling Λs must not both print as ΛX).  Two counters
-- are threaded left to right through the term: `tf` for type binders (Λ
-- and boundary binds) is a global counter; `xf` for term binders is the
-- λ-depth (restored after each body: term names are stable across steps
-- and sibling λs may share a name).  Type-level ∀ binders inside type
-- annotations stay depth-named: they are local to their type.
-- The ambient supply names the free slots 0..n-1, so `tf` starts at n.

record St : Set where
  constructor mkSt
  field tf xf : ℕ
open St

-- one fresh name per BINDER (bind), listed newest first (slot 0 first) but
-- NAMED oldest first, so an older bind keeps its name when a newer one is
-- prepended (TyPeelR's `bind A ∷ Θ`): the last bind gets tyBinder f.
bindNamesF : ℕ → CtxMorph → List String
bindNamesF f []             = []
bindNamesF f (bind A ∷ Θ)   = tyBinder (f + numBinds Θ) ∷ bindNamesF f Θ
bindNamesF f (unlock X ∷ Θ) = bindNamesF f Θ
bindNamesF f (lock X ∷ Θ)   = bindNamesF f Θ

showBndF : ℕ → ℕ → Supply → CtxMorph → Conv → String
showBndF d f ext [] c =
  "⟪ " ++ showConv d ext c ++ " ⟫"
showBndF d f ext Θ@(_ ∷ _) c =
  "⟪ " ++ showEnts d on ext Θ ++ " , "
       ++ showConv (d + numBinds Θ) (intSup Θ on ext) c ++ " ⟫"
  where on = bindNamesF f Θ

showTmF : ℕ → Supply → Supply → St → Term → String × St
showTmF td tys tms σ (` x)      = tms x , σ
showTmF td tys tms σ ($ n)      = show n , σ
showTmF td tys tms σ (ƛ A ∙ N)
  with showTmF td tys (extS tms (tmBinder (xf σ))) (mkSt (tf σ) (suc (xf σ))) N
... | body , σ′ =
  "(λ" ++ tmBinder (xf σ) ++ ":" ++ showTy td tys A ++ ". " ++ body ++ ")"
    , mkSt (tf σ′) (xf σ)          -- term binders stay depth-named
showTmF td tys tms σ (L · M) with showTmF td tys tms σ L
... | l , σ₁ with showTmF td tys tms σ₁ M
... | m , σ₂ = "(" ++ l ++ " · " ++ m ++ ")" , σ₂
showTmF td tys tms σ (Λ N) with showTmF (suc td) (extS tys (tyBinder (tf σ))) tms (mkSt (suc (tf σ)) (xf σ)) N
... | body , σ′ = "(Λ" ++ tyBinder (tf σ) ++ ". " ++ body ++ ")" , σ′
showTmF td tys tms σ (L ·[ B , A ]) with showTmF td tys tms σ L
... | l , σ′ = l ++ " [" ++ showTy td tys A ++ "]" , σ′
showTmF td tys tms σ (M ⟪ Θ , c ⟫)
  with showTmF (td + numBinds Θ) (intSup Θ (bindNamesF (tf σ) Θ) tys) tms
               (mkSt (tf σ + numBinds Θ) (xf σ)) M
... | body , σ′ =
  "(" ++ body ++ " " ++ showBndF td (tf σ) tys Θ c ++ ")" , σ′

showTm : ℕ → ℕ → Supply → Supply → Term → String
showTm td xd tys tms M = proj₁ (showTmF td tys tms (mkSt td xd) M)

------------------------------------------------------------------------
-- type contexts (entries named newest-first: slot 0 = X)
------------------------------------------------------------------------

showEntry : ℕ → Supply → String → Ent → String
showEntry d sup nm abst       = nm ++ " Λ-bound"
showEntry d sup nm (bind A)   = nm ++ " := " ++ showTy d sup A
showEntry d sup nm (masked E) = "⌷[" ++ showEntry d sup nm E ++ "]"

showTCtxAt : ℕ → ℕ → Supply → Ctxᵗ → String
showTCtxAt d i sup [] = "·"
showTCtxAt d i sup (E ∷ []) =
  showEntry d (λ k → sup (suc (k + i))) (sup i) E
showTCtxAt d i sup (E ∷ Δ@(_ ∷ _)) =
  showEntry d (λ k → sup (suc (k + i))) (sup i) E
    ++ " , " ++ showTCtxAt d (suc i) sup Δ

------------------------------------------------------------------------
-- conveniences: n = ambient context length; slot 0 is named X
------------------------------------------------------------------------

showTyIn : ℕ → Ty → String
showTyIn n A = showTy n tyBinder A

showTmIn : ℕ → Term → String
showTmIn n M = showTm n zero tyBinder tmBinder M

showConvIn : ℕ → Conv → String
showConvIn n c = showConv n tyBinder c

showBndIn : ℕ → CtxMorph → Conv → String
showBndIn n Θ c = showBnd n tyBinder Θ c

showTCtx : Ctxᵗ → String
showTCtx Δ = showTCtxAt 99 zero tyBinder Δ
