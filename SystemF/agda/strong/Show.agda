module strong.Show where

-- de Bruijn → NAMED rendering for Strong System F v8 (2026-09-16).
--
-- Ported from the v7 renderer, which still spoke of `M ⟪ Θ , c ⟫`,
-- locks and scopes.  v8's boundary is `M ⟨ c ⟩` and carries no Θ, so
-- the whole scope apparatus is gone; what remains is the one real
-- question, WHICH TYPE-VARIABLE FRAME THE INTERIOR IS IN.
--
-- A conversion's element list runs INTERIOR → EXTERIOR (`conv-cons`
-- types its head at the interior end), and each atomic element moves
-- the frame by one name:
--
--   seal X α, hide X α    the EXTERIOR has the assignment at X
--   unseal X α, show X α  the INTERIOR has it
--
-- so to render the body under an exterior supply we walk the list
-- BACKWARD, undoing each: a `seal`/`hide` deletes the name at X going
-- inward, an `unseal`/`show` inserts a fresh one there.  `↦` and `all`
-- do not move the frame at their own level.
--
-- CONVENTIONS (Jeremy's): type variables X, Y, Z (then primed); term
-- binders x, y, z, f, g, h.  V and W are reserved for metavariables
-- over values and are never generated.  Elements print in the notes'
-- spelling — `seal{-X:=α}`, `unseal{+X:=α}`, `id{-X:=α}` for `hide`,
-- `id{+X:=α}` for `show`.  Addresses print by KIND, which is the point
-- of the v8 split: `@ℓ` a store level, `νj` a base binder (a Λ's or a
-- ν's), `∀i` a stack binder (a ∀'s).
--
-- USED AS A TOOL non-interactively via scripts/render_term.sh, which
-- exploits the type-error trick: `oops : e ≡ ""; oops = refl` makes
-- Agda print e's normal form in the mismatch error.

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; length; reverse)
open import Data.String using (String; _++_)
open import Data.Product using (_×_; _,_)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.RepresentationTypes using
  (Addr; lvl; bnd; bse; RepTy; `ᵃ_; `ℕᴿ; `𝔹ᴿ; _⇒ᴿ_; `∀ᴿ)
open import strong.Conversion using
  (Conv; id; _∷ᶜ_; ConvElt; seal; unseal; hide; show; _↦_; all; elts)
open import strong.Terms using
  (Term; `_; $_; #_; _⊕[_]_; ƛ_∙_; _·_; Λ_; _•_[_]; ν_∙_; _⟨_⟩;
   Prim; p+; p×)

Supply : Set
Supply = ℕ → String

------------------------------------------------------------------------
-- binder names
------------------------------------------------------------------------

primes : ℕ → String
primes zero    = ""
primes (suc n) = "′" ++ primes n

cyc3 : ℕ → ℕ → String
cyc3 zero p = "X" ++ primes p
cyc3 (suc zero) p = "Y" ++ primes p
cyc3 (suc (suc zero)) p = "Z" ++ primes p
cyc3 (suc (suc (suc n))) p = cyc3 n (suc p)

tyBinder : ℕ → String
tyBinder n = cyc3 n zero

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

-- insert a name at slot X; everything from X up shifts one out
insAt : ℕ → String → Supply → Supply
insAt X b sup Y =
  if Y <ᵇ X then sup Y
  else (if Y ≡ᵇ X then b else sup (Y ∸ 1))

-- delete the name at slot X; everything above shifts one in
delAt : ℕ → Supply → Supply
delAt X sup Y = if Y <ᵇ X then sup Y else sup (suc Y)

------------------------------------------------------------------------
-- addresses, by KIND
------------------------------------------------------------------------

showAddr : Addr → String
showAddr (lvl ℓ) = "@" ++ showℕ ℓ
showAddr (bnd i) = "∀" ++ showℕ i
showAddr (bse j) = "ν" ++ showℕ j

------------------------------------------------------------------------
-- types and representation types
------------------------------------------------------------------------

showTy : ℕ → Supply → Ty → String
showTy d sup (` X)   = sup X
showTy d sup `ℕ      = "ℕ"
showTy d sup `𝔹      = "𝔹"
showTy d sup (A ⇒ B) =
  "(" ++ showTy d sup A ++ "→" ++ showTy d sup B ++ ")"
showTy d sup (`∀ A)  =
  "(∀" ++ tyBinder d ++ ". "
      ++ showTy (suc d) (extS sup (tyBinder d)) A ++ ")"

showRep : RepTy → String
showRep (`ᵃ α)   = showAddr α
showRep `ℕᴿ      = "ℕᴿ"
showRep `𝔹ᴿ      = "𝔹ᴿ"
showRep (R ⇒ᴿ S) = "(" ++ showRep R ++ "→" ++ showRep S ++ ")"
showRep (`∀ᴿ R)  = "(∀ᴿ. " ++ showRep R ++ ")"

------------------------------------------------------------------------
-- conversions
------------------------------------------------------------------------
-- An element is rendered in the frame it is READ in: the assignment it
-- moves names the slot X on whichever side HAS it, and that is the
-- side whose supply we are holding as we walk.

-- The list runs INTERIOR → EXTERIOR, so the walk starts at the
-- interior frame and carries it outward.  Which frame an element's
-- name lives in depends on which side HAS the assignment:
--
--   unseal X α, show X α   the INTERIOR has it — X names the frame we
--                          are holding, and the next frame loses it
--   seal X α,  hide X α    the EXTERIOR has it — the next frame GAINS
--                          it, and X names that one
--
-- (rendering the whole conversion at the exterior printed `?` for
-- every `show`/`unseal`, whose slot does not exist there)

mutual
  showConvFrom : (ℕ × Supply) → Conv → String
  showConvFrom (d , sup) (id A) = "id " ++ showTy d sup A
  showConvFrom (d , sup) (seal X α ∷ᶜ c) =
    "seal{-" ++ outS X ++ ":=" ++ showAddr α ++ "} ∷ "
      ++ showConvFrom (suc d , outSup) c
    where
    outSup = insAt X (tyBinder d) sup
    outS = outSup
  showConvFrom (d , sup) (hide X α ∷ᶜ c) =
    "id{-" ++ outS X ++ ":=" ++ showAddr α ++ "} ∷ "
      ++ showConvFrom (suc d , outSup) c
    where
    outSup = insAt X (tyBinder d) sup
    outS = outSup
  showConvFrom (d , sup) (unseal X α ∷ᶜ c) =
    "unseal{+" ++ sup X ++ ":=" ++ showAddr α ++ "} ∷ "
      ++ showConvFrom (d ∸ 1 , delAt X sup) c
  showConvFrom (d , sup) (show X α ∷ᶜ c) =
    "id{+" ++ sup X ++ ":=" ++ showAddr α ++ "} ∷ "
      ++ showConvFrom (d ∸ 1 , delAt X sup) c
  showConvFrom (d , sup) ((s ↦ t) ∷ᶜ c) =
    "(" ++ showConvFrom (d , sup) s ++ " → " ++ showConvFrom (d , sup) t
        ++ ") ∷ " ++ showConvFrom (d , sup) c
  showConvFrom (d , sup) (all s ∷ᶜ c) =
    "(∀" ++ tyBinder d ++ ". "
        ++ showConvFrom (suc d , extS sup (tyBinder d)) s ++ ") ∷ "
        ++ showConvFrom (d , sup) c

------------------------------------------------------------------------
-- the frame a conversion's interior is in
------------------------------------------------------------------------
-- Walk the elements BACKWARD from the exterior, undoing each.

-- going OUTWARD→INWARD: a seal/hide loses the name, an unseal/show
-- gains a fresh one; a `↦` or `all` does not move the frame here
undo : (ℕ × Supply) → ConvElt → (ℕ × Supply)
undo (d , sup) (seal X α) = d ∸ 1 , delAt X sup
undo (d , sup) (hide X α) = d ∸ 1 , delAt X sup
undo (d , sup) (unseal X α) = suc d , insAt X (tyBinder d) sup
undo (d , sup) (show X α) = suc d , insAt X (tyBinder d) sup
undo (d , sup) (s ↦ t) = d , sup
undo (d , sup) (all s) = d , sup

undoAll : (ℕ × Supply) → List ConvElt → (ℕ × Supply)
undoAll st [] = st
undoAll st (ĉ ∷ ĉs) = undoAll (undo st ĉ) ĉs

-- the frame the BODY of `M ⟨ c ⟩` is read in
interiorOf : ℕ → Supply → Conv → (ℕ × Supply)
interiorOf d sup c = undoAll (d , sup) (reverse (elts c))

------------------------------------------------------------------------
-- terms
------------------------------------------------------------------------

showPrim : Prim → String
showPrim p+ = "+"
showPrim p× = "×"

-- `d`/`sup` are the TYPE frame, `e`/`tsup` the TERM frame
showTm : ℕ → Supply → ℕ → Supply → Term → String
showTm d sup e tsup (` x) = tsup x
showTm d sup e tsup ($ n) = showℕ n
showTm d sup e tsup (# false) = "false"
showTm d sup e tsup (# true) = "true"
showTm d sup e tsup (M ⊕[ p ] N) =
  "(" ++ showTm d sup e tsup M ++ " " ++ showPrim p ++ " "
      ++ showTm d sup e tsup N ++ ")"
showTm d sup e tsup (ƛ A ∙ N) =
  "(λ" ++ tmBinder e ++ ":" ++ showTy d sup A ++ ". "
       ++ showTm d sup (suc e) (extS tsup (tmBinder e)) N ++ ")"
showTm d sup e tsup (L · M) =
  "(" ++ showTm d sup e tsup L ++ " " ++ showTm d sup e tsup M ++ ")"
showTm d sup e tsup (Λ V) =
  "(Λ" ++ tyBinder d ++ ". "
       ++ showTm (suc d) (extS sup (tyBinder d)) e tsup V ++ ")"
showTm d sup e tsup (L • B [ A ]) =
  showTm d sup e tsup L ++ " [" ++ showTy d sup A ++ "]"
showTm d sup e tsup (ν R ∙ M) =
  "(ν:=" ++ showRep R ++ ". " ++ showTm d sup e tsup M ++ ")"
showTm d sup e tsup (M ⟨ c ⟩) = showBody (interiorOf d sup c)
  where
  showBody : (ℕ × Supply) → String
  showBody (dᵢ , supᵢ) =
    showTm dᵢ supᵢ e tsup M ++ "⟨ " ++ showConvFrom (dᵢ , supᵢ) c ++ " ⟩"

-- closed, at the empty frame
showTm₀ : Term → String
showTm₀ = showTm zero (λ _ → "?") zero (λ _ → "?")

showConv₀ : Conv → String
showConv₀ c = showConvFrom (interiorOf zero (λ _ → "?") c) c
