module strong-rep-store.Show where

-- File Charter:
--   * de Bruijn → NAMED rendering for the two-universe Strong System F:
--     terms, types, payloads, conversions, boundary scopes, type
--     contexts and whole evaluator traces.  §1 name supplies;
--     §2 indexed string lists; §3 the rendering `Env`; §4 types,
--     payloads, conversions; §5 boundary scopes; §6 terms;
--     §7 type contexts; §8 runs; §9 the entry points.
--   * DISPLAY ONLY — no theorem, and nothing depends on it.
--   * THE TWO UNIVERSES PRINT DIFFERENTLY: a REPRESENTATION variable
--     is a Greek letter (α, β, γ, α′, …) and the ORDINARY name that
--     denotes it is the Latin letter at the same position (X, Y, Z,
--     X′, …).  An `unbind` prints `↓X`, a `bind` `↥X`, in ACTING
--     order; the conversion is rendered on the CONVERSION context.
--   * Driven non-interactively by scripts/render_term.sh.
-- Commentary: Commentary.md § Show.agda

open import Data.Nat using (ℕ; zero; suc; _∸_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.List using (List; []; _∷_; length; map)
open import Data.List using () renaming (_++_ to _l++_)
open import Data.String using (String; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import strong-rep-store.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong-rep-store.Ctx
  using (Ctxᵗ; RepCtx; abstR; bindR; reps; names; apply)
open import strong-rep-store.Conversion using (Conv; id; seal; unseal; _↦_; `∀)
open import strong-rep-store.Terms
  using (Term; `_; $_; `true; `false; ƛ_∙_; _·_; Λ_; _·[_,_]; _⟪_,_⟫;
         _∣_⊢_⦂_)
open import strong-rep-store.Boundary
  using (Boundary; Change; unbind; bind)
open import strong-rep-store.Reduction using (_⊢_-→_∣_; TyBeta; Beta; Peel;
  TyPeelR-Λ; TyPeelR-⟪⟫; CancelR; IdPush; Drop$; Drop-true; Drop-false;
  ξ-·-l; ξ-·-r; ξ-·[]; ξ-⟪⟫)
open import strong-rep-store.Eval
  using (Trace; stop; illtyped; _◅⟨_⟩_; Final; value; no-redex; out-of-fuel;
         eval)

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

-- the REPRESENTATION variable allocated at the same counter.  The pairing
-- is the whole convention: X names α, Y names β, X′ names α′.
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

------------------------------------------------------------------------
-- 3. The rendering environment
------------------------------------------------------------------------

-- `eReps` carries BOTH names allocated for each representation
-- variable; `eNames` is the ordinary name map itself, so rendering an
-- ordinary variable is a TWO-STEP lookup.
-- Commentary.md § Show.agda / §3
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

-- the two flat supplies the type, payload and conversion printers use
onames : Env → List String
onames e = map (ordOf e) (eNames e)

rnames : Env → List String
rnames e = map proj₁ (eReps e)

newPair : ℕ → String × String
newPair n = repBinder n , tyBinder n

-- `underΛ`: one abstract representation variable, and ordinary name 0 for
-- it.
underΛE : ℕ → Env → Env
underΛE f e =
  mkEnv (newPair f ∷ eReps e) (zero ∷ map suc (eNames e))

------------------------------------------------------------------------
-- 4. Ordinary types, representation payloads, conversions
------------------------------------------------------------------------

showTy : List String → Ty → String
showTy ns (` X)   = nthS ns X
showTy ns `ℕ      = "ℕ"
showTy ns `𝔹      = "𝔹"
showTy ns (A ⇒ B) = "(" ++ showTy ns A ++ "⇒" ++ showTy ns B ++ ")"
showTy ns (`∀ A)  =
  "(∀" ++ tyBinder (length ns) ++ ". "
       ++ showTy (tyBinder (length ns) ∷ ns) A ++ ")"

-- A PAYLOAD is read in the representation universe, with a LOCAL prefix:
-- `Ξ ⊢ref[ n ] i` says index `i < n` is bound by an enclosing payload `∀`
-- and index `n + α` is the free representation variable α.  The locals are
-- ordinary variables, so they print with Latin letters and the free ones
-- with Greek.
showRep : List String → List String → Ty → String
showRep ls rs (` i)   =
  if i <ᵇ length ls then nthS ls i else nthS rs (i ∸ length ls)
showRep ls rs `ℕ      = "ℕ"
showRep ls rs `𝔹      = "𝔹"
showRep ls rs (R ⇒ S) =
  "(" ++ showRep ls rs R ++ "⇒" ++ showRep ls rs S ++ ")"
showRep ls rs (`∀ R)  =
  "(∀" ++ tyBinder (length ls) ++ ". "
       ++ showRep (tyBinder (length ls) ∷ ls) rs R ++ ")"

-- `seal` and `unseal` name ORDINARY variables, read on the conversion
-- context; `` `∀ `` binds one.
showConv : List String → Conv → String
showConv ns (id A)     = "id " ++ showTy ns A
showConv ns (seal X)   = "seal " ++ nthS ns X
showConv ns (unseal X) = "unseal " ++ nthS ns X
showConv ns (s ↦ t)    =
  "(" ++ showConv ns s ++ " ↦ " ++ showConv ns t ++ ")"
showConv ns (`∀ s)     =
  "(∀" ++ tyBinder (length ns) ++ ". "
       ++ showConv (tyBinder (length ns) ∷ ns) s ++ ")"

------------------------------------------------------------------------
-- 5. Boundary scopes
------------------------------------------------------------------------

-- the interior reading: every change acts
applyChI : Change → Env → Env
applyChI (unbind X α)   e = mkEnv (eReps e) (deleteAt X (eNames e))
applyChI (bind X α) e = mkEnv (eReps e) (insertAt X α (eNames e))

applyChsI : List Change → Env → Env
applyChsI []      e = e
applyChsI (δ ∷ χ) e = applyChI δ (applyChsI χ e)

-- the conversion reading: an `unbind` is SKIPPED, and a `bind` of a name
-- that is already live is a no-op (`conv-bind-live`,
-- strong-rep-store.Boundary §3)
applyChC : Change → Env → Env
applyChC (unbind X α)   e = e
applyChC (bind X α) e =
  if memberN α (eNames e) then e
  else mkEnv (eReps e) (insertAt X α (eNames e))

applyChsC : List Change → Env → Env
applyChsC []      e = e
applyChsC (δ ∷ χ) e = applyChC δ (applyChsC χ e)

changePiece : Env → Change → String
changePiece e (unbind X α)   = "↓" ++ ordNm e X
changePiece e (bind X α) = "↥" ++ ordOf e α

-- IN ACTING ORDER: the tail acts first, so it prints first.
changePieces : Env → List Change → List String
changePieces e []      = []
changePieces e (δ ∷ χ) =
  changePieces e χ l++ (changePiece (applyChsI χ e) δ ∷ [])

joinC : List String → String
joinC []               = ""
joinC (s ∷ [])         = s
joinC (s ∷ ss@(_ ∷ _)) = s ++ " , " ++ joinC ss

-- the entry block with its trailing separator — empty for an empty
-- boundary scope, so `⟪ c ⟫` renders with no leading comma
entBlock : List String → String
entBlock []         = ""
entBlock ps@(_ ∷ _) = joinC ps ++ " , "

showBnd : Env → ℕ → Boundary → Conv → String
showBnd e f Θ c =
  "⟪ " ++ entBlock (changePieces e Θ)
       ++ showConv (onames (applyChsC Θ e)) c ++ " ⟫"

------------------------------------------------------------------------
-- 6. Terms
------------------------------------------------------------------------

-- Binder names are GLOBALLY UNIQUE across one rendered term: the
-- type/representation counter is threaded left to right, the term
-- counter is the λ-depth.
-- Commentary.md § Show.agda / §6
showTmF : Env → List String → ℕ → ℕ → Term → String × ℕ
showTmF e tms f x (` k)   = nthS tms k , f
showTmF e tms f x ($ n)   = show n , f
showTmF e tms f x `true   = "true" , f
showTmF e tms f x `false  = "false" , f
showTmF e tms f x (ƛ A ∙ N)
  with showTmF e (tmBinder x ∷ tms) f (suc x) N
... | body , f′ =
  "(λ" ++ tmBinder x ++ ":" ++ showTy (onames e) A ++ ". " ++ body ++ ")"
    , f′
showTmF e tms f x (L · M) with showTmF e tms f x L
showTmF e tms f x (L · M) | l , f₁ with showTmF e tms f₁ x M
showTmF e tms f x (L · M) | l , f₁ | m , f₂ =
  "(" ++ l ++ " · " ++ m ++ ")" , f₂
showTmF e tms f x (Λ N) with showTmF (underΛE f e) tms (suc f) x N
... | body , f′ = "(Λ" ++ tyBinder f ++ ". " ++ body ++ ")" , f′
showTmF e tms f x (L ·[ B , A ]) with showTmF e tms f x L
... | l , f′ = l ++ " [" ++ showTy (onames e) A ++ "]" , f′
showTmF e tms f x (M ⟪ Θ , c ⟫)
  with showTmF (applyChsI Θ e) tms f x M
... | body , f′ = "(" ++ body ++ " " ++ showBnd e f Θ c ++ ")" , f′

------------------------------------------------------------------------
-- 7. Type contexts
------------------------------------------------------------------------

-- A representation payload is stored OUTSIDE its own binder (`∋ʳ` shifts
-- it on lookup), so the entry at index i is read on the names from i+1 on.
showRepEntries : ℕ → Pairs → RepCtx → List String
showRepEntries i ps []             = []
showRepEntries i ps (abstR ∷ Ξ)    =
  (proj₁ (nthP ps i) ++ " abst") ∷ showRepEntries (suc i) ps Ξ
showRepEntries i ps (bindR R ∷ Ξ)  =
  (proj₁ (nthP ps i) ++ " := " ++ showRep [] (map proj₁ (dropL (suc i) ps)) R)
    ∷ showRepEntries (suc i) ps Ξ

showNameEntries : Pairs → List ℕ → List String
showNameEntries ps []       = []
showNameEntries ps (α ∷ αs) =
  (proj₂ (nthP ps α) ++ "↦" ++ proj₁ (nthP ps α)) ∷ showNameEntries ps αs

nonEmpty : List String → String
nonEmpty []         = "·"
nonEmpty ps@(_ ∷ _) = joinC ps

showTCtx : Ctxᵗ → String
showTCtx Γ =
  nonEmpty (showRepEntries zero ps (reps Γ))
    ++ " ∣ " ++ nonEmpty (showNameEntries ps (names Γ))
  where
  ps : Pairs
  ps = map newPair (count zero (length (reps Γ)))

-- Build the renderer from the actual state context.  Cell i is always named
-- by the i-th Greek name, and the ordinary names are exactly the state's
-- name map.
ctxEnv : Ctxᵗ → Env
ctxEnv Γ = mkEnv ps (names Γ)
  where
  ps : Pairs
  ps = map newPair (count zero (length (reps Γ)))

showStore : Ctxᵗ → String
showStore Γ = "Ξ = [" ++ joinC (showRepEntries zero (eReps e) (reps Γ))
                    ++ "]"
  where
  e : Env
  e = ctxEnv Γ

showState : Ctxᵗ → Term → String
showState Γ M =
  showStore Γ ++ "\n" ++ proj₁ (showTmF e [] (length (reps Γ)) zero M)
  where
  e : Env
  e = ctxEnv Γ

------------------------------------------------------------------------
-- 8. Runs
------------------------------------------------------------------------

-- The rule that actually fired: a congruence reports the rule inside it,
-- which is what a reader of a trace wants to see.
ruleName : ∀ {Δ M N δ} → Δ ⊢ M -→ N ∣ δ → String
ruleName (TyBeta v same)             = "TyBeta"
ruleName (Beta v)                    = "Beta"
ruleName (Peel v w rc ri rd sc)      = "Peel"
ruleName (TyPeelR-Λ v rel ⊢s same)   = "TyPeelR-Λ"
ruleName (TyPeelR-⟪⟫ v ri rel r′ ri⁺ r″ sc ⊢s sm same) =
  "TyPeelR-⟪⟫"
ruleName (CancelR v ri r₁ d₁ r⋉ sm) = "CancelR"
ruleName (IdPush v ri r₁ r⋉ sm) = "IdPush"
ruleName (Drop$ b)                   = "Drop$"
ruleName Drop-true                   = "Drop-true"
ruleName Drop-false                  = "Drop-false"
ruleName (ξ-·-l st)                  = ruleName st
ruleName (ξ-·-r v st)                = ruleName st
ruleName (ξ-·[] st)                  = ruleName st
ruleName (ξ-⟪⟫ rel st)               = ruleName st

finalName : ∀ {M} → Final M → String
finalName (value v)  = "VALUE"
finalName no-redex   = "NO REDEX FOUND"
finalName out-of-fuel = "OUT OF FUEL"

------------------------------------------------------------------------
-- 9. Entry points — `n` is the number of ambient ordinary names
------------------------------------------------------------------------

-- The ambient environment: `n` representation variables, ordinary name `i`
-- denoting representation `i`, so ordinary slot 0 prints as X and names α.
-- New names start at `n`, so term binders cannot collide with them.
ambient : ℕ → Env
ambient n = mkEnv (map newPair (count zero n)) (count zero n)

showTyIn : ℕ → Ty → String
showTyIn n A = showTy (onames (ambient n)) A

showRepIn : ℕ → Ty → String
showRepIn n R = showRep [] (rnames (ambient n)) R

showConvIn : ℕ → Conv → String
showConvIn n c = showConv (onames (ambient n)) c

showBndIn : ℕ → Boundary → Conv → String
showBndIn n Θ c = showBnd (ambient n) n Θ c

showTmIn : ℕ → Term → String
showTmIn n M = proj₁ (showTmF (ambient n) [] n zero M)

showTermsIn : ℕ → List Term → String
showTermsIn n []       = ""
showTermsIn n (M ∷ []) = showTmIn n M
showTermsIn n (M ∷ Ms@(_ ∷ _)) =
  showTmIn n M ++ "\n  -->\n" ++ showTermsIn n Ms

showTrace : ∀ {Δ A M} → ℕ → Trace Δ A M → String
showTrace {Δ = Δ} {M = M} n (stop fin) =
  showState Δ M ++ "\n    -- " ++ finalName fin
showTrace {Δ = Δ} {M = M} n (illtyped {M′ = M′} {δ = δ} r) =
  showState Δ M ++ "\n  --[" ++ ruleName r ++ "]-->\n"
    ++ showState (apply δ Δ) M′ ++ "\n    -- TYPE LOST"
showTrace {Δ = Δ} {M = M} n (r ◅⟨ ⊢M′ ⟩ tr) =
  showState Δ M ++ "\n  --[" ++ ruleName r ++ "]-->\n" ++ showTrace n tr

-- the whole run, rendered: `showRun 0 11 Q₀-⊢` for a closed program
showRun : ∀ {Δ A M} → ℕ → ℕ → Δ ∣ [] ⊢ M ⦂ A → String
showRun n k ⊢M = showTrace n (eval k _ ⊢M)
