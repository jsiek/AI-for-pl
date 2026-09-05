module strong.Show where

-- de Bruijn → NAMED rendering for strong System F terms, types, boundary
-- skeletons, conversions and type contexts — adapted from the name-supply
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
--   * Θ's OWNERS bind fresh interior slots; the interior supply is
--     [fresh names for the owners] then ext SHIFTED past them.  Nothing is
--     dropped any more (conceal masks in place), so there is exactly ONE
--     inner supply — the old `cmax` correction has no analogue, and the
--     interior supply and the FACE supply coincide (`intC` and `fceC`
--     differ in blocking, not in slot layout).
--   * an OWNER's rep is shown under `ext` — a rep is a type over the PLAIN
--     exterior (simultaneity);
--   * a `cnc X` / `ali X` names an EXTERIOR slot, so it is shown under
--     `ext`; neither carries a rep, which is the whole point of the
--     redesign;
--   * the FACE `c` is shown under the interior/face supply, and its
--     `seal`/`unseal` names are read there — by their spine, not by a
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

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx using (Ent; abst; own; blk; Ctxᵗ)
open import strong.Conversion using (Conv; id; seal; unseal; _↦_; `∀)
open import strong.Terms
  using (Term; `_; $_; ƛ_∙_; _·_; Λ_; _·[_,_]; _⟪_,_⟫;
         BCtx; BEnt; own; ali; cnc; nrev)

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

-- one fresh name per OWNER, newest first (owner 0 is interior slot 0)
ownNames : ℕ → BCtx → List String
ownNames d []            = []
ownNames d (own A ∷ Θ)   = tyBinder d ∷ ownNames (suc d) Θ
ownNames d (ali X ∷ Θ)   = ownNames d Θ
ownNames d (cnc X ∷ Θ)   = ownNames d Θ

nth : List String → ℕ → String
nth []       k       = "?"
nth (s ∷ ss) zero    = s
nth (s ∷ ss) (suc k) = nth ss k

-- interior (= face) supply: owner names, then ext shifted past them.
-- No `cmax` correction: conceal masks in place, so no slot is dropped.
intSup : BCtx → List String → Supply → Supply
intSup Θ on ext k =
  if k <ᵇ nrev Θ then nth on k else ext (k ∸ nrev Θ)

------------------------------------------------------------------------
-- boundary skeletons
------------------------------------------------------------------------

sep : BCtx → String
sep [] = ""
sep (_ ∷ _) = " , "

tl : List String → List String
tl []       = []
tl (s ∷ ss) = ss

-- `on` is the owner-name list still to be consumed; `ext` names exterior
-- slots.  An owner's rep is read in the PLAIN exterior; `cnc`/`ali` carry
-- a name only.
showEnts : ℕ → List String → Supply → BCtx → String
showEnts d on ext [] = ""
showEnts d on ext (own A ∷ Θ) =
  "↑" ++ nth on 0 ++ ":=" ++ showTy d ext A ++ sep Θ
      ++ showEnts d (tl on) ext Θ
showEnts d on ext (cnc X ∷ Θ) =
  "↓" ++ ext X ++ sep Θ ++ showEnts d on ext Θ
showEnts d on ext (ali X ∷ Θ) =
  "↥" ++ ext X ++ sep Θ ++ showEnts d on ext Θ

showBnd : ℕ → Supply → BCtx → Conv → String
showBnd d ext [] c =
  "⟪ " ++ showConv d ext c ++ " ⟫"
showBnd d ext Θ@(_ ∷ _) c =
  "⟪ " ++ showEnts d on ext Θ ++ " , "
       ++ showConv (d + nrev Θ) (intSup Θ on ext) c ++ " ⟫"
  where on = ownNames d Θ

------------------------------------------------------------------------
-- terms
------------------------------------------------------------------------

showTm : ℕ → ℕ → Supply → Supply → Term → String
showTm td xd tys tms (` x)      = tms x
showTm td xd tys tms ($ n)      = show n
showTm td xd tys tms (ƛ A ∙ N)  =
  "(λ" ++ tmBinder xd ++ ":" ++ showTy td tys A ++ ". "
    ++ showTm td (suc xd) tys (extS tms (tmBinder xd)) N ++ ")"
showTm td xd tys tms (L · M)    =
  "(" ++ showTm td xd tys tms L ++ " · "
      ++ showTm td xd tys tms M ++ ")"
showTm td xd tys tms (Λ N)      =
  "(Λ" ++ tyBinder td ++ ". "
    ++ showTm (suc td) xd (extS tys (tyBinder td)) tms N ++ ")"
showTm td xd tys tms (L ·[ B , A ]) =
  showTm td xd tys tms L ++ " [" ++ showTy td tys A ++ "]"
showTm td xd tys tms (M ⟪ Θ , c ⟫) =
  "(" ++ showTm (td + nrev Θ) xd (intSup Θ on tys) tms M
      ++ " " ++ showBnd td tys Θ c ++ ")"
  where on = ownNames td Θ

------------------------------------------------------------------------
-- type contexts (entries named newest-first: slot 0 = X)
------------------------------------------------------------------------

showEntry : ℕ → Supply → String → Ent → String
showEntry d sup nm abst    = nm ++ " Λ-bound"
showEntry d sup nm (own A) = nm ++ " := " ++ showTy d sup A
showEntry d sup nm (blk E) = "⌷[" ++ showEntry d sup nm E ++ "]"

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

showBndIn : ℕ → BCtx → Conv → String
showBndIn n Θ c = showBnd n tyBinder Θ c

showTCtx : Ctxᵗ → String
showTCtx Δ = showTCtxAt 99 zero tyBinder Δ
