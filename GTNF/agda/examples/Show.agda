module examples.Show where

-- File Charter:
--   * (GTNF) FORKED FROM strong-rep-nu.Show: de Bruijn → NAMED
--     rendering of GTNF types, payloads, conversions, coercions, mode
--     environments, boundary scopes, terms and whole evaluator runs.
--     §1 name supplies; §2 indexed string lists; §3 the rendering
--     `Env`; §4 types, payloads, conversions; §5 coercions and modes;
--     §6 boundary scopes; §7 terms; §8 type contexts and states;
--     §9 runs; §10 the entry points.
--   * DISPLAY ONLY — no theorem, and only display modules depend on it
--     (examples.ImpLadder prints its names, types, conversions,
--     coercions, scopes and terms with these printers).
--   * THE NOTATION IS design.md's.  Types `★→★`, `∀X. A`; conversions
--     `id(A)`, `+X` (unseal), `−X` (seal), `c → d`, `∀X. c`, `t ; −X`,
--     `+X ; c` (design.md §2); coercions `id(A)`, `G!`, `G?ℓ0`,
--     `p → q`, `∀X. p`, `inst X. p`, `gen X. p`, `p ; G!`, `G?ℓ ; p`,
--     `bot-intro ℓ0` (§3; a label prints as ℓ followed by its number);
--     terms `λx:A. N`, `L M`, `ΛX. V`, `ν X:=A. (L X) ⟨c⟩`,
--     `[δ] M ⟨c⟩`, `M⟨p⟩^μ`, `blame ℓ0` (§4).
--   * A SCOPE `[δ]` prints its changes in ACTING order (the list's tail
--     acts first, so it prints first): `bind X α` is `+X^α` and
--     `unbind X α` is `−X^α`, so νF's merged `Θ₁ ++ Θ₂` prints as
--     design.md's `[δ₂, δ₁]`.  The conversion is read on the
--     CONVERSION context, the body on the INTERIOR.
--   * A MODE ENVIRONMENT `μ` is parallel to the cast's ordinary names
--     (head = index 0); it prints OUTERMOST NAME FIRST, as design.md's
--     `μ, X:m`: `^[X:★∼X∼★, Y:X∼X]`, and `^[]` when empty.
--   * THE TWO UNIVERSES PRINT DIFFERENTLY (as in strong-rep-nu): a
--     REPRESENTATION variable is a Greek letter (α, β, γ, α′, …) and the
--     ORDINARY name paired with it is the Latin letter at the same
--     counter (X, Y, Z, X′, …).
--   * REP. VARS ARE NAMED BY ALLOCATION ORDER: in a state whose store has n
--     rep. vars, the rep. var at de Bruijn index i is the (n ∸ suc i)-th
--     allocated, so the first allocated rep. var is α (named X) in EVERY
--     state of a run.  The binders of a state (Λ, ν, ∀/inst/gen) take
--     the counters n, n+1, … left to right, so type-binder names are
--     GLOBALLY UNIQUE within a state; a `ν` is named for the rep. var it is
--     about to allocate, which TyBeta then names with that same letter
--     when it is the next allocation.  Binders inside TYPES and
--     CONVERSIONS are local: the first tyBinder not already in scope.
--   * Driven non-interactively by scripts/render_gtnf.sh.

open import Data.Nat using (ℕ; zero; suc; _∸_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.List using (List; []; _∷_; length; map; reverse)
open import Data.List using () renaming (_++_ to _l++_)
open import Data.String using (String; _++_; _==_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Types using (Ty; `_; `ℕ; `𝔹; ★; _⇒_; `∀)
open import Ctx
  using (Ctxᵗ; RepCtx; abstR; bindR; reps; names; apply; Alloc; none; new)
open import Conversion
  using (Mid; Tail; Conv; id; _↦_; `∀; mid; seal; _⨾seal_; tail; unseal;
         unseal_⨾_)
open import Coercion
  using (Coercion; Label; idᵖ; _!; _？_; _↦ᵖ_; ∀ᵖ_; instᵖ_;
         genᵖ_;
         _︔_!; _？_︔_;
         bot-elim; bot-intro; Mode; X∼X; X∼★; ★∼X; ★∼X∼★; ModeEnv)
open import Terms
  using (Term; `_; $_; `true; `false; ƛ_∙_; _·_; Λ_; ν_·_⟨_⟩; _⟪_,_⟫;
         _⟨_∣_⟩; blame; _∣_⊢_⦂_)
open import Boundary using (Boundary; Change; unbind; bind)
open import examples.Eval
  using (Trace; stop; illtyped; _◅⟨_⟩_; Final; value; blamed; no-redex;
         out-of-fuel; eval; ruleName)

------------------------------------------------------------------------
-- 1. Name supplies
------------------------------------------------------------------------

primes : ℕ → String
primes zero    = ""
primes (suc n) = "′" ++ primes n

cyc3 : ℕ → String → String → String → ℕ → String
cyc3 zero                a b c p = a ++ primes p
cyc3 (suc zero)          a b c p = b ++ primes p
cyc3 (suc (suc zero))    a b c p = c ++ primes p
cyc3 (suc (suc (suc n))) a b c p = cyc3 n a b c (suc p)

-- the ORDINARY type variable allocated at counter n
tyBinder : ℕ → String
tyBinder n = cyc3 n "X" "Y" "Z" zero

-- the REPRESENTATION variable allocated at the same counter: X names α,
-- Y names β, X′ names α′
repBinder : ℕ → String
repBinder n = cyc3 n "α" "β" "γ" zero

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

memberS : String → List String → Bool
memberS s []       = false
memberS s (t ∷ ts) = (s == t) ∨ memberS s ts

-- the first tyBinder j ≥ j₀ not in ns; `length ns` tries suffice
freshFrom : ℕ → ℕ → List String → String
freshFrom zero       j ns = tyBinder j
freshFrom (suc fuel) j ns =
  if memberS (tyBinder j) ns then freshFrom fuel (suc j) ns else tyBinder j

-- a local binder name that shadows nothing in scope
freshTy : List String → String
freshTy ns = freshFrom (length ns) (length ns) ns

------------------------------------------------------------------------
-- 2. de Bruijn indexed string lists
------------------------------------------------------------------------

nthS : List String → ℕ → String
nthS []       k       = "?"
nthS (s ∷ ss) zero    = s
nthS (s ∷ ss) (suc k) = nthS ss k

Pairs : Set
Pairs = List (String × String)

nthP : Pairs → ℕ → String × String
nthP []       k       = "?" , "?"
nthP (p ∷ ps) zero    = p
nthP (p ∷ ps) (suc k) = nthP ps k

dropL : ℕ → Pairs → Pairs
dropL zero    ps       = ps
dropL (suc n) []       = []
dropL (suc n) (p ∷ ps) = dropL n ps

deleteAt : ℕ → List ℕ → List ℕ
deleteAt k       []       = []
deleteAt zero    (α ∷ αs) = αs
deleteAt (suc k) (α ∷ αs) = α ∷ deleteAt k αs

insertAt : ℕ → ℕ → List ℕ → List ℕ
insertAt zero    β αs       = β ∷ αs
insertAt (suc k) β []       = β ∷ []
insertAt (suc k) β (α ∷ αs) = α ∷ insertAt k β αs

memberN : ℕ → List ℕ → Bool
memberN β []       = false
memberN β (α ∷ αs) = (β ≡ᵇ α) ∨ memberN β αs

count : ℕ → ℕ → List ℕ
count i zero    = []
count i (suc n) = i ∷ count (suc i) n

-- n-1, n-2, …, 0: the allocation counters of a store's rep. vars, index 0
-- (the newest rep. var) first
countDown : ℕ → List ℕ
countDown zero    = []
countDown (suc n) = n ∷ countDown n

joinC : List String → String
joinC []               = ""
joinC (s ∷ [])         = s
joinC (s ∷ ss@(_ ∷ _)) = s ++ ", " ++ joinC ss

------------------------------------------------------------------------
-- 3. The rendering environment
------------------------------------------------------------------------

-- `eReps` carries BOTH names allocated for each representation
-- variable; `eNames` is the ordinary name map itself, so rendering an
-- ordinary variable is a TWO-STEP lookup.
record Env : Set where
  constructor mkEnv
  field
    eReps  : Pairs
    eNames : List ℕ
open Env

repNm : Env → ℕ → String
repNm e α = proj₁ (nthP (eReps e) α)

ordOf : Env → ℕ → String
ordOf e α = proj₂ (nthP (eReps e) α)

ordNm : Env → ℕ → String
ordNm e X = go (eNames e) X
  where
  go : List ℕ → ℕ → String
  go []       k       = "?"
  go (α ∷ αs) zero    = ordOf e α
  go (α ∷ αs) (suc k) = go αs k

onames : Env → List String
onames e = map (ordOf e) (eNames e)

rnames : Env → List String
rnames e = map proj₁ (eReps e)

newPair : ℕ → String × String
newPair n = repBinder n , tyBinder n

-- `underΛ`: one abstract representation variable, and ordinary name 0
-- for it
underΛE : ℕ → Env → Env
underΛE f e =
  mkEnv (newPair f ∷ eReps e) (zero ∷ map suc (eNames e))

------------------------------------------------------------------------
-- 4. Ordinary types, representation payloads, conversions
------------------------------------------------------------------------

mutual
  showTy : List String → Ty → String
  showTy ns (` X)   = nthS ns X
  showTy ns `ℕ      = "ℕ"
  showTy ns `𝔹      = "𝔹"
  showTy ns ★       = "★"
  showTy ns (A ⇒ B) = parenTy ns A ++ "→" ++ showTy ns B
  showTy ns (`∀ A)  =
    "∀" ++ freshTy ns ++ ". " ++ showTy (freshTy ns ∷ ns) A

  -- a type as an operand: an arrow or a ∀ is parenthesised
  parenTy : List String → Ty → String
  parenTy ns (` X)   = showTy ns (` X)
  parenTy ns `ℕ      = "ℕ"
  parenTy ns `𝔹      = "𝔹"
  parenTy ns ★       = "★"
  parenTy ns (A ⇒ B) = "(" ++ showTy ns (A ⇒ B) ++ ")"
  parenTy ns (`∀ A)  = "(" ++ showTy ns (`∀ A) ++ ")"

-- a λ annotation: only a ∀ is parenthesised (`λf:★→★.`, `λg:(∀X. X→X).`)
annTy : List String → Ty → String
annTy ns (`∀ A) = "(" ++ showTy ns (`∀ A) ++ ")"
annTy ns (` X)   = showTy ns (` X)
annTy ns `ℕ      = "ℕ"
annTy ns `𝔹      = "𝔹"
annTy ns ★       = "★"
annTy ns (A ⇒ B) = showTy ns (A ⇒ B)

-- A PAYLOAD is read in the representation universe, with a LOCAL prefix:
-- index `i < length ls` is bound by an enclosing payload `∀`, and index
-- `length ls + α` is the free representation variable α.
mutual
  showRep : List String → List String → Ty → String
  showRep ls rs (` i)   =
    if i <ᵇ length ls then nthS ls i else nthS rs (i ∸ length ls)
  showRep ls rs `ℕ      = "ℕ"
  showRep ls rs `𝔹      = "𝔹"
  showRep ls rs ★       = "★"
  showRep ls rs (R ⇒ S) = parenRep ls rs R ++ "→" ++ showRep ls rs S
  showRep ls rs (`∀ R)  =
    "∀" ++ freshTy ls ++ ". " ++ showRep (freshTy ls ∷ ls) rs R

  parenRep : List String → List String → Ty → String
  parenRep ls rs (` i)   = showRep ls rs (` i)
  parenRep ls rs `ℕ      = "ℕ"
  parenRep ls rs `𝔹      = "𝔹"
  parenRep ls rs ★       = "★"
  parenRep ls rs (R ⇒ S) = "(" ++ showRep ls rs (R ⇒ S) ++ ")"
  parenRep ls rs (`∀ R)  = "(" ++ showRep ls rs (`∀ R) ++ ")"

-- design.md §2: `unseal X` is `+X`, `seal X` is `−X`.  A chain prints its
-- links with `;`, in the order they act; a compound operand of `→` and
-- a compound `∀` body are parenthesised.
mutual
  showMid : List String → Mid → String
  showMid ns (id A)  = "id(" ++ showTy ns A ++ ")"
  showMid ns (s ↦ t) = showConvP ns s ++ " → " ++ showConvP ns t
  showMid ns (`∀ s)  =
    "∀" ++ freshTy ns ++ ". " ++ showConvP (freshTy ns ∷ ns) s

  showTail : List String → Tail → String
  showTail ns (mid g)     = showMid ns g
  showTail ns (seal X)    = "−" ++ nthS ns X
  showTail ns (t ⨾seal X) = showTailP ns t ++ " ; −" ++ nthS ns X

  showConv : List String → Conv → String
  showConv ns (tail t)       = showTail ns t
  showConv ns (unseal X)     = "+" ++ nthS ns X
  showConv ns (unseal X ⨾ c) = "+" ++ nthS ns X ++ " ; " ++ showConvP ns c

  -- a middle as the left link of a chain
  showTailP : List String → Tail → String
  showTailP ns (mid (id A))  = showMid ns (id A)
  showTailP ns (mid (s ↦ t)) = "(" ++ showMid ns (s ↦ t) ++ ")"
  showTailP ns (mid (`∀ s))  = "(" ++ showMid ns (`∀ s) ++ ")"
  showTailP ns (seal X)      = showTail ns (seal X)
  showTailP ns (t ⨾seal X)   = showTail ns (t ⨾seal X)

  -- a conversion as an operand
  showConvP : List String → Conv → String
  showConvP ns (tail (mid (id A)))  = showMid ns (id A)
  showConvP ns (tail (mid (s ↦ t))) = "(" ++ showMid ns (s ↦ t) ++ ")"
  showConvP ns (tail (mid (`∀ s)))  = "(" ++ showMid ns (`∀ s) ++ ")"
  showConvP ns (tail (seal X))      = showTail ns (seal X)
  showConvP ns (tail (t ⨾seal X))   = "(" ++ showTail ns (t ⨾seal X) ++ ")"
  showConvP ns (unseal X)           = showConv ns (unseal X)
  showConvP ns (unseal X ⨾ c)       = "(" ++ showConv ns (unseal X ⨾ c) ++ ")"

------------------------------------------------------------------------
-- 5. Coercions and modes
------------------------------------------------------------------------

showLabel : Label → String
showLabel ℓ = "ℓ" ++ show ℓ

-- A coercion binder (`∀X.`, `inst X.`, `gen X.`) takes the next counter
-- of the threaded supply, as a term-level Λ does, so its name is unique
-- in the state.
mutual
  showCo : List String → ℕ → Coercion → String × ℕ
  showCo ns f (idᵖ A)       = "id(" ++ showTy ns A ++ ")" , f
  showCo ns f (G !)         = parenTy ns G ++ "!" , f
  showCo ns f (G ？ ℓ)      = parenTy ns G ++ "?" ++ showLabel ℓ , f
  showCo ns f (p ↦ᵖ q) with showCoP ns f p
  showCo ns f (p ↦ᵖ q) | sp , f₁ with showCoP ns f₁ q
  showCo ns f (p ↦ᵖ q) | sp , f₁ | sq , f₂ = sp ++ " → " ++ sq , f₂
  showCo ns f (∀ᵖ p) with showCoP (tyBinder f ∷ ns) (suc f) p
  showCo ns f (∀ᵖ p) | sp , f′ = "∀" ++ tyBinder f ++ ". " ++ sp , f′
  showCo ns f (instᵖ p) with showCoP (tyBinder f ∷ ns) (suc f) p
  showCo ns f (instᵖ p) | sp , f′ =
    "inst " ++ tyBinder f ++ ". " ++ sp , f′
  showCo ns f (genᵖ p) with showCoP (tyBinder f ∷ ns) (suc f) p
  showCo ns f (genᵖ p) | sp , f′ = "gen " ++ tyBinder f ++ ". " ++ sp , f′
  showCo ns f (p ︔ G !) with showCoP ns f p
  showCo ns f (p ︔ G !) | sp , f′ =
    sp ++ " ; " ++ parenTy ns G ++ "!" , f′
  showCo ns f (G ？ ℓ ︔ p) with showCoP ns f p
  showCo ns f (G ？ ℓ ︔ p) | sp , f′ =
    parenTy ns G ++ "?" ++ showLabel ℓ ++ " ; " ++ sp , f′
  showCo ns f bot-elim      = "bot-elim" , f
  showCo ns f (bot-intro ℓ) = "bot-intro " ++ showLabel ℓ , f

  -- a coercion as an operand or a binder body: compound ones get parens
  showCoP : List String → ℕ → Coercion → String × ℕ
  showCoP ns f (idᵖ A)       = showCo ns f (idᵖ A)
  showCoP ns f (G !)         = showCo ns f (G !)
  showCoP ns f (G ？ ℓ)      = showCo ns f (G ？ ℓ)
  showCoP ns f bot-elim      = showCo ns f bot-elim
  showCoP ns f (bot-intro ℓ) = showCo ns f (bot-intro ℓ)
  showCoP ns f (p ↦ᵖ q)  = parens (showCo ns f (p ↦ᵖ q))
  showCoP ns f (∀ᵖ p)    = parens (showCo ns f (∀ᵖ p))
  showCoP ns f (instᵖ p) = parens (showCo ns f (instᵖ p))
  showCoP ns f (genᵖ p)  = parens (showCo ns f (genᵖ p))
  showCoP ns f (p ︔ G !)   = parens (showCo ns f (p ︔ G !))
  showCoP ns f (G ？ ℓ ︔ p) = parens (showCo ns f (G ？ ℓ ︔ p))

  parens : String × ℕ → String × ℕ
  parens (s , f) = "(" ++ s ++ ")" , f

showMode : Mode → String
showMode X∼X   = "X∼X"
showMode X∼★   = "X∼★"
showMode ★∼X   = "★∼X"
showMode ★∼X∼★ = "★∼X∼★"

-- one `name:mode` per entry, index 0 first; a missing name prints `?`
envEntries : List String → ModeEnv → List String
envEntries ns       []      = []
envEntries []       (m ∷ μ) = ("?:" ++ showMode m) ∷ envEntries [] μ
envEntries (n ∷ ns) (m ∷ μ) = (n ++ ":" ++ showMode m) ∷ envEntries ns μ

showEnv : List String → ModeEnv → String
showEnv ns μ = "^[" ++ joinC (reverse (envEntries ns μ)) ++ "]"

------------------------------------------------------------------------
-- 6. Boundary scopes
------------------------------------------------------------------------

-- the interior reading: every change acts
applyChI : Change → Env → Env
applyChI (unbind X α) e = mkEnv (eReps e) (deleteAt X (eNames e))
applyChI (bind X α)   e = mkEnv (eReps e) (insertAt X α (eNames e))

applyChsI : List Change → Env → Env
applyChsI []      e = e
applyChsI (δ ∷ χ) e = applyChI δ (applyChsI χ e)

-- the conversion reading: an `unbind` is SKIPPED, and a `bind` of a name
-- that is already live is a no-op (`conv-bind-live`, Boundary §3)
applyChC : Change → Env → Env
applyChC (unbind X α) e = e
applyChC (bind X α)   e =
  if memberN α (eNames e) then e
  else mkEnv (eReps e) (insertAt X α (eNames e))

applyChsC : List Change → Env → Env
applyChsC []      e = e
applyChsC (δ ∷ χ) e = applyChC δ (applyChsC χ e)

-- `−X^α` names the ordinary name at position X when the change acts;
-- `+X^α` names the ordinary name paired with α
changePiece : Env → Change → String
changePiece e (unbind X α) = "−" ++ ordNm e X ++ "^" ++ repNm e α
changePiece e (bind X α)   = "+" ++ ordOf e α ++ "^" ++ repNm e α

-- IN ACTING ORDER: the tail acts first, so it prints first.
changePieces : Env → List Change → List String
changePieces e []      = []
changePieces e (δ ∷ χ) =
  changePieces e χ l++ (changePiece (applyChsI χ e) δ ∷ [])

showScope : Env → Boundary → String
showScope e Θ = "[" ++ joinC (changePieces e Θ) ++ "]"

------------------------------------------------------------------------
-- 7. Terms
------------------------------------------------------------------------

-- a cast's subject: `blame ℓ` is parenthesised, every other compound
-- term already is
castee : Term → String → String
castee (blame ℓ) s = "(" ++ s ++ ")"
castee (` k) s = s
castee ($ n) s = s
castee `true s = s
castee `false s = s
castee (ƛ A ∙ N) s = s
castee (L · M) s = s
castee (Λ N) s = s
castee (ν A · L ⟨ c ⟩) s = s
castee (M ⟪ Θ , c ⟫) s = s
castee (M ⟨ μ ∣ p ⟩) s = s

-- The type/representation counter is threaded left to right; the term
-- counter is the λ-depth.
showTmF : Env → List String → ℕ → ℕ → Term → String × ℕ
showTmF e tms f x (` k)   = nthS tms k , f
showTmF e tms f x ($ n)   = show n , f
showTmF e tms f x `true   = "true" , f
showTmF e tms f x `false  = "false" , f
showTmF e tms f x (ƛ A ∙ N)
  with showTmF e (tmBinder x ∷ tms) f (suc x) N
... | body , f′ =
  "(λ" ++ tmBinder x ++ ":" ++ annTy (onames e) A ++ ". " ++ body ++ ")"
    , f′
showTmF e tms f x (L · M) with showTmF e tms f x L
showTmF e tms f x (L · M) | l , f₁ with showTmF e tms f₁ x M
showTmF e tms f x (L · M) | l , f₁ | m , f₂ =
  "(" ++ l ++ " " ++ m ++ ")" , f₂
showTmF e tms f x (Λ N) with showTmF (underΛE f e) tms (suc f) x N
... | body , f′ = "(Λ" ++ tyBinder f ++ ". " ++ body ++ ")" , f′
-- `ν` names the rep. var it will allocate (counter `f`), and `c` is read
-- under that fresh name: the conversion reading of `TyBetaBoundary` at
-- the allocated context is `underΛE`'s shape with a bound rep. var.
showTmF e tms f x (ν A · L ⟨ c ⟩) with showTmF e tms (suc f) x L
... | l , f′ =
  "(ν " ++ tyBinder f ++ ":=" ++ showTy (onames e) A ++ ". (" ++ l ++ " "
    ++ tyBinder f ++ ") ⟨" ++ showConv (onames (underΛE f e)) c ++ "⟩)"
    , f′
showTmF e tms f x (M ⟪ Θ , c ⟫)
  with showTmF (applyChsI Θ e) tms f x M
... | body , f′ =
  "(" ++ showScope e Θ ++ " " ++ body ++ " ⟨"
    ++ showConv (onames (applyChsC Θ e)) c ++ "⟩)" , f′
showTmF e tms f x (M ⟨ μ ∣ p ⟩) with showTmF e tms f x M
showTmF e tms f x (M ⟨ μ ∣ p ⟩) | m , f₁ with showCo (onames e) f₁ p
showTmF e tms f x (M ⟨ μ ∣ p ⟩) | m , f₁ | sp , f₂ =
  castee M m ++ "⟨" ++ sp ++ "⟩" ++ showEnv (onames e) μ , f₂
showTmF e tms f x (blame ℓ) = "blame " ++ showLabel ℓ , f

------------------------------------------------------------------------
-- 8. Type contexts and states
------------------------------------------------------------------------

-- the rep. vars of an store of n rep. vars, index 0 first, named by allocation order
repVars : ℕ → Pairs
repVars n = map newPair (countDown n)

-- A representation payload is stored OUTSIDE its own binder, so the entry
-- at index i is read on the names from i+1 on.
showRepEntries : ℕ → Pairs → RepCtx → List String
showRepEntries i ps []             = []
showRepEntries i ps (abstR ∷ Ξ)    =
  (proj₁ (nthP ps i) ++ " abst") ∷ showRepEntries (suc i) ps Ξ
showRepEntries i ps (bindR R ∷ Ξ)  =
  (proj₁ (nthP ps i) ++ ":="
     ++ showRep [] (map proj₁ (dropL (suc i) ps)) R)
    ∷ showRepEntries (suc i) ps Ξ

-- the renderer for a state: rep. var i named by allocation order, and the
-- ordinary names exactly the state's name map
ctxEnv : Ctxᵗ → Env
ctxEnv Γ = mkEnv (repVars (length (reps Γ))) (names Γ)

-- the store, OLDEST rep. var first
showStore : Ctxᵗ → String
showStore Γ =
  "Ξ = [" ++ joinC (reverse (showRepEntries zero (eReps (ctxEnv Γ))
                                               (reps Γ))) ++ "]"

showState : Ctxᵗ → Term → String
showState Γ M = proj₁ (showTmF (ctxEnv Γ) [] (length (reps Γ)) zero M)

------------------------------------------------------------------------
-- 9. Runs
------------------------------------------------------------------------

-- the allocation a step made, `⊣ α:=R` as design.md writes it; the new
-- rep. var is the next one in allocation order
allocNote : Ctxᵗ → Alloc → String
allocNote Γ none    = ""
allocNote Γ (new R) =
  ", ⊣ " ++ repBinder (length (reps Γ)) ++ ":="
    ++ showRep [] (rnames (ctxEnv Γ)) R

finalNote : ∀ {M} → Final M → String
finalNote (value v)   = ""
finalNote (blamed eq) = ""
finalNote no-redex    = "      -- NO REDEX FOUND"
finalNote out-of-fuel = "      -- OUT OF FUEL"

-- every state, each followed by the rule that produced the next:
--     <state>
--   ⟶ (<Rule>)
--     <state>
showTrace : ∀ {Δ A M} → Trace Δ A M → String
showTrace {Δ = Δ} {M = M} (stop fin) =
  "  " ++ showState Δ M ++ finalNote fin
showTrace {Δ = Δ} {M = M} (illtyped {M′ = M′} {δ = δ} r) =
  "  " ++ showState Δ M ++ "\n⟶ (" ++ ruleName r ++ allocNote Δ δ
    ++ ")\n  " ++ showState (apply δ Δ) M′ ++ "      -- TYPE LOST"
showTrace {Δ = Δ} {M = M} (_◅⟨_⟩_ {δ = δ} r ⊢M′ tr) =
  "  " ++ showState Δ M ++ "\n⟶ (" ++ ruleName r ++ allocNote Δ δ
    ++ ")\n" ++ showTrace tr

-- the whole run, rendered: `showRun 11 ex1-⊢`
showRun : ∀ {Δ A M} → ℕ → Δ ∣ [] ⊢ M ⦂ A → String
showRun k ⊢M = showTrace (eval k _ ⊢M)

------------------------------------------------------------------------
-- 10. Entry points — `n` is the number of store rep. vars, all abstract,
-- with ordinary name i for rep. var i
------------------------------------------------------------------------

ambient : ℕ → Env
ambient n = mkEnv (repVars n) (count zero n)

showTyIn : ℕ → Ty → String
showTyIn n A = showTy (onames (ambient n)) A

showRepIn : ℕ → Ty → String
showRepIn n R = showRep [] (rnames (ambient n)) R

showConvIn : ℕ → Conv → String
showConvIn n c = showConv (onames (ambient n)) c

showCoIn : ℕ → Coercion → String
showCoIn n p = proj₁ (showCo (onames (ambient n)) n p)

showTmIn : ℕ → Term → String
showTmIn n M = proj₁ (showTmF (ambient n) [] n zero M)

-- a closed term in the empty context
showTm : Term → String
showTm M = showTmIn zero M

showTermsIn : ℕ → List Term → String
showTermsIn n []       = ""
showTermsIn n (M ∷ []) = "  " ++ showTmIn n M
showTermsIn n (M ∷ Ms@(_ ∷ _)) =
  "  " ++ showTmIn n M ++ "\n⟶\n" ++ showTermsIn n Ms
