module strong.Show where

-- de Bruijn → NAMED rendering for strong System F terms, types, boundary
-- contexts and type contexts — adapted from the name-supply infrastructure
-- of GTSFImp/proof/DGG/ImpLadder.agda (Jeremy's request, 2026-09-05, after
-- a hand-transcription error read an interior ` 0 in the exterior frame).
--
-- CONVENTIONS (Jeremy's): type variables are X, Y, Z (then X′, Y′, Z′, …);
-- term binders are x, y, z, f, g, h (then primes).  V and W are reserved
-- for metavariables over term VALUES and never generated here.
--
-- THE POINT of the adaptation: a boundary changes the type-variable frame.
-- Rendering M ⟪ Θ , B₀ ⟫ under an exterior supply `ext`:
--   * the INTERIOR supply is [fresh names for Θ's reveal block] and then
--     ext shifted past the cmax Θ dropped slots (mirroring intOf);
--   * a REVEAL rep is shown under ext (the parallel reading: bwf-↑'s
--     Γ ⊢ A) — and a rep-less reveal as ↑X:⋆;
--   * a CONCEAL's slot is named by ext and its rep shown under the
--     INTERIOR supply (bwf-↓'s Ψ ⊢ A) — rep-less as ↓X:⋆;
--   * B₀ is shown under the FRAME supply [reveal names][ext verbatim]
--     (the baseS frame Scoped ranges over).
--
-- USED AS A TOOL non-interactively via scripts/render_term.sh, which
-- exploits the type-error trick: `oops : e ≡ ""; oops = refl` makes Agda
-- print e's normal form in the mismatch error.

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.String using (String; _++_)
open import strong.Types
open import strong.Context using (TCtx; TyEntry; abst; rvld; xrvld)
open import strong.Boundary
  using (Term; `_; $_; ƛ_∙_; _·_; Λ_; _·[_,_]; _⟪_,_⟫;
         BCtx; BEntry; rvl; rvl⋆; cnc; cnc⋆; revs; cmax)

Supply : Set
Supply = ℕ → String

------------------------------------------------------------------------
-- binder names
------------------------------------------------------------------------

primes : ℕ → String
primes zero    = ""
primes (suc n) = "′" ++ primes n

cyc3 : ℕ → String → String → String → ℕ → String
cyc3 zero          a b c p = a ++ primes p
cyc3 (suc zero)    a b c p = b ++ primes p
cyc3 (suc (suc zero)) a b c p = c ++ primes p
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
-- the three supplies a boundary induces
------------------------------------------------------------------------

revNames : ℕ → BCtx → List String
revNames d []            = []
revNames d (rvl A ∷ Θ)   = tyBinder d ∷ revNames (suc d) Θ
revNames d (rvl⋆ ∷ Θ)    = tyBinder d ∷ revNames (suc d) Θ
revNames d (cnc X A ∷ Θ) = revNames d Θ
revNames d (cnc⋆ X ∷ Θ)  = revNames d Θ

nth : List String → ℕ → String
nth []       k       = "?"
nth (s ∷ ss) zero    = s
nth (s ∷ ss) (suc k) = nth ss k

-- interior supply: reveal names, then ext past the dropped block
intSup : BCtx → List String → Supply → Supply
intSup Θ rn ext k =
  if k <ᵇ revs Θ then nth rn k else ext ((k ∸ revs Θ) + cmax Θ)

-- frame supply (for B₀): reveal names, then ext verbatim
frameSup : BCtx → List String → Supply → Supply
frameSup Θ rn ext k =
  if k <ᵇ revs Θ then nth rn k else ext (k ∸ revs Θ)

------------------------------------------------------------------------
-- boundaries
------------------------------------------------------------------------

sep : BCtx → String
sep [] = ""
sep (_ ∷ _) = " , "

showEnts : ℕ → List String → Supply → Supply → BCtx → String
showEnts d rn ext int [] = ""
showEnts d rn ext int (rvl A ∷ Θ) =
  "↑" ++ nth rn 0 ++ ":=" ++ showTy d ext A ++ sep Θ
    ++ showEnts d (tl rn) ext int Θ
  where tl : List String → List String
        tl [] = []
        tl (s ∷ ss) = ss
showEnts d rn ext int (rvl⋆ ∷ Θ) =
  "↑" ++ nth rn 0 ++ ":⋆" ++ sep Θ
    ++ showEnts d (tl rn) ext int Θ
  where tl : List String → List String
        tl [] = []
        tl (s ∷ ss) = ss
showEnts d rn ext int (cnc X A ∷ Θ) =
  "↓" ++ ext X ++ ":=" ++ showTy d int A ++ sep Θ
    ++ showEnts d rn ext int Θ
showEnts d rn ext int (cnc⋆ X ∷ Θ) =
  "↓" ++ ext X ++ ":⋆" ++ sep Θ
    ++ showEnts d rn ext int Θ

showBnd : ℕ → Supply → BCtx → Ty → String
showBnd d ext [] B₀ =
  "⟪ " ++ showTy d ext B₀ ++ " ⟫"
showBnd d ext Θ B₀ =
  "⟪ " ++ showEnts d rn ext (intSup Θ rn ext) Θ ++ " , "
       ++ showTy d (frameSup Θ rn ext) B₀ ++ " ⟫"
  where rn = revNames d Θ

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
showTm td xd tys tms (M ⟪ Θ , B₀ ⟫) =
  "(" ++ showTm (td + revs Θ) xd
           (intSup Θ rn tys) tms M
      ++ " " ++ showBnd td tys Θ B₀ ++ ")"
  where rn = revNames td Θ

------------------------------------------------------------------------
-- type contexts (entries named newest-first: slot 0 = X)
------------------------------------------------------------------------

showEntry : ℕ → Supply → String → TyEntry → String
showEntry d sup nm abst      = nm ++ " Λ-bound"
showEntry d sup nm (rvld A)  = nm ++ " := " ++ showTy d sup A
showEntry d sup nm (xrvld A) = nm ++ " :=ˣ " ++ showTy d sup A

showTCtxAt : ℕ → ℕ → Supply → TCtx → String
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

showBndIn : ℕ → BCtx → Ty → String
showBndIn n Θ B₀ = showBnd n tyBinder Θ B₀

showTCtx : TCtx → String
showTCtx Δ = showTCtxAt 99 zero tyBinder Δ
