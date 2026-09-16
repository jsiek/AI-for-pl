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

-- Type-variable names come from TWO DISJOINT POOLS.
--
--   X Y Z …   an ASSIGNMENT to an address; the letter is keyed to the
--             address, so it is the same in every step of every trace
--   S T U …   a variable BOUND by a `∀` in a type or an `all` in a
--             conversion; it has no address, so it is named by
--             position
tyBinder : ℕ → String
tyBinder n = cyc3 n zero

cyc3b : ℕ → ℕ → String
cyc3b zero p = "S" ++ primes p
cyc3b (suc zero) p = "T" ++ primes p
cyc3b (suc (suc zero)) p = "U" ++ primes p
cyc3b (suc (suc (suc n))) p = cyc3b n (suc p)

boundVar : ℕ → String
boundVar n = cyc3b n zero

cyc3g : ℕ → ℕ → String
cyc3g zero p = "α" ++ primes p
cyc3g (suc zero) p = "β" ++ primes p
cyc3g (suc (suc zero)) p = "γ" ++ primes p
cyc3g (suc (suc (suc n))) p = cyc3g n (suc p)

greek : ℕ → String
greek n = cyc3g n zero

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
showAddr (lvl ℓ) = greek ℓ
showAddr (bnd i) = "∀" ++ greek i
showAddr (bse j) = "ν" ++ greek j

-- THE NAME ASSIGNED TO AN ADDRESS, keyed to the address itself — this
-- is what makes a variable print the same at every step of a trace.
varOfAddr : Addr → String
varOfAddr (lvl ℓ) = tyBinder ℓ
varOfAddr (bnd i) = tyBinder i ++ "″"
varOfAddr (bse j) = tyBinder j ++ "′"

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
  "(∀" ++ boundVar d ++ ". "
      ++ showTy (suc d) (extS sup (boundVar d)) A ++ ")"

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

-- The list runs INTERIOR → EXTERIOR, but the frame we are GIVEN is the
-- exterior one, so the walk goes outside-in: recurse on the tail (which
-- is the more exterior part) to reach the frame just outside the head,
-- then handle the head there.  Which frame an element's NAME lives in
-- depends on which side holds the assignment:
--
--   seal X α, hide X α    the EXTERIOR has it — X names the frame we
--                         are holding, and the interior LOSES it
--   unseal X α, show X α  the INTERIOR has it — the interior GAINS a
--                         fresh name at X, and that is what X names
--
-- The ℕ is a monotone FRESH-NAME COUNTER, not a depth: it is never
-- decremented, so two different type variables can never print as the
-- same letter even when both sit at slot 0 of their own frames.

showConvOut : (ℕ × Supply) → Conv → (ℕ × Supply) × String
showConvOut (n , sup) (id A) = (n , sup) , "id " ++ showTy n sup A
showConvOut ext (seal X α ∷ᶜ c) with showConvOut ext c
... | (n , sup) , str =
  (n , delAt X sup)
  , "seal{-" ++ sup X ++ ":=" ++ showAddr α ++ "} ∷ " ++ str
showConvOut ext (hide X α ∷ᶜ c) with showConvOut ext c
... | (n , sup) , str =
  (n , delAt X sup)
  , "id{-" ++ sup X ++ ":=" ++ showAddr α ++ "} ∷ " ++ str
showConvOut ext (unseal X α ∷ᶜ c) with showConvOut ext c
... | (n , sup) , str =
  (n , insAt X (varOfAddr α) sup)
  , "unseal{+" ++ varOfAddr α ++ ":=" ++ showAddr α ++ "} ∷ " ++ str
showConvOut ext (show X α ∷ᶜ c) with showConvOut ext c
... | (n , sup) , str =
  (n , insAt X (varOfAddr α) sup)
  , "id{+" ++ varOfAddr α ++ ":=" ++ showAddr α ++ "} ∷ " ++ str
showConvOut ext ((s ↦ t) ∷ᶜ c) with showConvOut ext c
... | (n , sup) , str with showConvOut (n , sup) s | showConvOut (n , sup) t
... | _ , ss | _ , ts = (n , sup) , "(" ++ ss ++ " → " ++ ts ++ ") ∷ " ++ str
showConvOut ext (all s ∷ᶜ c) with showConvOut ext c
... | (n , sup) , str with showConvOut (suc n , extS sup (boundVar n)) s
... | _ , ss =
  (n , sup) , "(∀" ++ boundVar n ++ ". " ++ ss ++ ") ∷ " ++ str

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
-- `⊢Λ` always assigns the Λ's name to `bse zero`, so key it there
showTm d sup e tsup (Λ V) =
  "(Λ" ++ varOfAddr (bse zero) ++ ". "
       ++ showTm d (extS sup (varOfAddr (bse zero))) e tsup V ++ ")"
showTm d sup e tsup (L • B [ A ]) =
  showTm d sup e tsup L ++ " [" ++ showTy d sup A ++ "]"
showTm d sup e tsup (ν R ∙ M) =
  "(ν:=" ++ showRep R ++ ". " ++ showTm d sup e tsup M ++ ")"
-- A boundary's body is TERM-CLOSED — `⊢⟨⟩` types it at `[]` — so the
-- term-binder supply restarts inside one.  Without the reset the same
-- closed value prints with different binder names depending on how
-- deep the boundary happens to sit, and a reduction step that only
-- moved it would look like a renaming.
showTm d sup e tsup (M ⟨ c ⟩) = go (showConvOut (d , sup) c)
  where
  go : (ℕ × Supply) × String → String
  go ((dᵢ , supᵢ) , str) =
    showTm dᵢ supᵢ zero (λ _ → "?") M ++ "⟨ " ++ str ++ " ⟩"

-- closed, at the empty frame
showTm₀ : Term → String
showTm₀ = showTm zero (λ _ → "?") zero (λ _ → "?")

showConv₀ : Conv → String
showConv₀ c = go (showConvOut (zero , λ _ → "?") c)
  where
  go : (ℕ × Supply) × String → String
  go (_ , str) = str
