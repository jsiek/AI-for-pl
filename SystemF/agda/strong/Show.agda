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
open import Data.Product using (_×_; _,_; proj₂)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.RepresentationTypes using
  (Addr; lvl; bse; RepTy; `ᵃ_; `ᵛ_; `ℕᴿ; `𝔹ᴿ; _⇒ᴿ_; `∀ᴿ)
open import strong.Conversion using
  (Conv; id; _∷ᶜ_; ConvElt; seal; unseal; hide; show; _↦_; all; elts)
open import strong.Terms using
  (Term; `_; $_; #_; _⊕[_]_; ƛ_∙_; _·_; Λ_; _•_[_]; ν_∙_; _⟨_⟩;
   Prim; p+; p×)

Supply : Set
Supply = ℕ → String

-- A BASE SUPPLY maps a `bse` INDEX to the stable id its binder was
-- allocated.  Both the address's own name and the type-variable name
-- for it are derived from that id, so neither changes when a base push
-- renumbers the index.
BSupply : Set
BSupply = ℕ → ℕ

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

extB : BSupply → ℕ → BSupply
extB bs b zero    = b
extB bs b (suc k) = bs k

-- ONE POOL FOR EVERY ADDRESS.  A level is its own id; a base index is
-- the id its binder was allocated.  `Alloc` sends the ν's `bse 0` to
-- the level `length Σ`, so a ν allocated at `length Σ` KEEPS ITS NAME
-- across the allocation step — which is why `showTmΣ` takes the store's
-- length as the first free id.
idxOf : BSupply → Addr → ℕ
idxOf bs (lvl ℓ) = ℓ
idxOf bs (bse j) = bs j

showAddr : BSupply → Addr → String
showAddr bs α = greek (idxOf bs α)

-- THE NAME ASSIGNED TO AN ADDRESS, keyed to the address itself — this
-- is what makes a variable print the same at every step of a trace.
varOfAddr : BSupply → Addr → String
varOfAddr bs α = tyBinder (idxOf bs α)

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

showRep : BSupply → RepTy → String
showRep bs (`ᵃ α)   = showAddr bs α
showRep bs (`ᵛ i)   = boundVar i
showRep bs `ℕᴿ      = "ℕᴿ"
showRep bs `𝔹ᴿ      = "𝔹ᴿ"
showRep bs (R ⇒ᴿ S) = "(" ++ showRep bs R ++ "→" ++ showRep bs S ++ ")"
showRep bs (`∀ᴿ R)  = "(∀ᴿ. " ++ showRep bs R ++ ")"

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

-- The base supply is CONSTANT along a conversion: no element binds a
-- base address (an `all` binds a type variable).
showConvOut : BSupply → (ℕ × Supply) → Conv → (ℕ × Supply) × String
showConvOut bs (n , sup) (id A) = (n , sup) , "id " ++ showTy n sup A
showConvOut bs ext (seal X α ∷ᶜ c) with showConvOut bs ext c
... | (n , sup) , str =
  (n , delAt X sup)
  , "seal{-" ++ sup X ++ ":=" ++ showAddr bs α ++ "} ∷ " ++ str
showConvOut bs ext (hide X α ∷ᶜ c) with showConvOut bs ext c
... | (n , sup) , str =
  (n , delAt X sup)
  , "id{-" ++ sup X ++ ":=" ++ showAddr bs α ++ "} ∷ " ++ str
showConvOut bs ext (unseal X α ∷ᶜ c) with showConvOut bs ext c
... | (n , sup) , str =
  (n , insAt X (varOfAddr bs α) sup)
  , "unseal{+" ++ varOfAddr bs α ++ ":=" ++ showAddr bs α ++ "} ∷ " ++ str
showConvOut bs ext (show X α ∷ᶜ c) with showConvOut bs ext c
... | (n , sup) , str =
  (n , insAt X (varOfAddr bs α) sup)
  , "id{+" ++ varOfAddr bs α ++ ":=" ++ showAddr bs α ++ "} ∷ " ++ str
-- `conv-fun`'s components carry the element's own crossing:
--   t : Γᵢ ⊢ t ∶ B ⇝ D ⊣ Γₑ   runs interior → exterior, like the element
--   s : Γₑ ⊢ s ∶ C ⇝ A ⊣ Γᵢ   runs BACKWARD
-- so the element's interior frame is the one `t` ends at, and `s` is
-- read from there.  Threading it is what makes a `↦` whose covariant
-- half crosses an assignment print that assignment's name in the body
-- (notes/SourceToTyWrapGap); returning the exterior frame unchanged
-- printed it as `?`.
showConvOut bs ext ((s ↦ t) ∷ᶜ c) with showConvOut bs ext c
... | extₑ , str with showConvOut bs extₑ t
... | extᵢ , ts with showConvOut bs extᵢ s
... | _ , ss = extᵢ , "(" ++ ss ++ " → " ++ ts ++ ") ∷ " ++ str
showConvOut bs ext (all s ∷ᶜ c) with showConvOut bs ext c
... | (n , sup) , str with showConvOut bs (suc n , extS sup (boundVar n)) s
... | _ , ss =
  (n , sup) , "(∀" ++ boundVar n ++ ". " ++ ss ++ ") ∷ " ++ str

------------------------------------------------------------------------
-- terms
------------------------------------------------------------------------

showPrim : Prim → String
showPrim p+ = "+"
showPrim p× = "×"

-- `b`/`bs` are the BASE frame, `d`/`sup` the TYPE frame, `e`/`tsup` the
-- TERM frame.  `b` is a MONOTONE counter threaded through the whole
-- term, so two `Λ`s never share a name however they are nested — the
-- reason the result is a pair.
showTm : ℕ → BSupply → ℕ → Supply → ℕ → Supply → Term → ℕ × String
showTm b bs d sup e tsup (` x)     = b , tsup x
showTm b bs d sup e tsup ($ n)     = b , showℕ n
showTm b bs d sup e tsup (# false) = b , "false"
showTm b bs d sup e tsup (# true)  = b , "true"
showTm b bs d sup e tsup (M ⊕[ p ] N)
  with showTm b bs d sup e tsup M
... | b₁ , ms with showTm b₁ bs d sup e tsup N
... | b₂ , ns = b₂ , "(" ++ ms ++ " " ++ showPrim p ++ " " ++ ns ++ ")"
showTm b bs d sup e tsup (ƛ A ∙ N)
  with showTm b bs d sup (suc e) (extS tsup (tmBinder e)) N
... | b₁ , ns =
  b₁ , "(λ" ++ tmBinder e ++ ":" ++ showTy d sup A ++ ". " ++ ns ++ ")"
showTm b bs d sup e tsup (L · M)
  with showTm b bs d sup e tsup L
... | b₁ , ls with showTm b₁ bs d sup e tsup M
... | b₂ , ms = b₂ , "(" ++ ls ++ " " ++ ms ++ ")"
-- `⊢Λ` binds a BASE address and pushes an assignment naming it, so the
-- Λ takes a fresh id and both frames gain it.
showTm b bs d sup e tsup (Λ V)
  with showTm (suc b) (extB bs b) d (extS sup (tyBinder b)) e tsup V
... | b₁ , vs = b₁ , "(Λ" ++ tyBinder b ++ ". " ++ vs ++ ")"
showTm b bs d sup e tsup (L • B [ A ])
  with showTm b bs d sup e tsup L
... | b₁ , ls = b₁ , ls ++ " [" ++ showTy d sup A ++ "]"
-- `⊢ν` binds a base address and NO name, so only the base frame grows.
-- The representation is read OUTSIDE the binder, hence `bs`, not `bs′`.
showTm b bs d sup e tsup (ν R ∙ M)
  with showTm (suc b) (extB bs b) d sup e tsup M
... | b₁ , ms =
  b₁ , "(ν " ++ greek b ++ ":=" ++ showRep bs R ++ ". " ++ ms ++ ")"
-- A boundary's body is TERM-CLOSED — `⊢⟨⟩` types it at `[]` — so the
-- term-binder supply restarts inside one.  Without the reset the same
-- closed value prints with different binder names depending on how
-- deep the boundary happens to sit, and a reduction step that only
-- moved it would look like a renaming.  The BASE frame does not reset:
-- no crossing binds an address.
showTm b bs d sup e tsup (M ⟨ c ⟩) = go (showConvOut bs (d , sup) c)
  where
  go : (ℕ × Supply) × String → ℕ × String
  go ((dᵢ , supᵢ) , str) with showTm b bs dᵢ supᵢ zero (λ _ → "?") M
  ... | b₁ , ms = b₁ , ms ++ "⟨ " ++ str ++ " ⟩"

-- Closed, at the empty frame.  `n` is the STORE'S LENGTH: base ids
-- start there, so the first `ν` — the one `Alloc` is about to
-- discharge to level `length Σ` — keeps its name across that step.
showTmΣ : ℕ → Term → String
showTmΣ n M =
  proj₂ (showTm n (λ _ → zero) zero (λ _ → "?") zero (λ _ → "?") M)

showTm₀ : Term → String
showTm₀ = showTmΣ zero

showConv₀ : Conv → String
showConv₀ c = go (showConvOut (λ _ → zero) (zero , λ _ → "?") c)
  where
  go : (ℕ × Supply) × String → String
  go (_ , str) = str
