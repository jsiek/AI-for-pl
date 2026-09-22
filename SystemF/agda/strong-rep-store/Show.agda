module strong-rep-store.Show where

-- de Bruijn → NAMED rendering for the two-universe Strong System F: terms,
-- ordinary types, representation payloads, conversions, boundary scopes,
-- type contexts, and whole evaluator traces.  DISPLAY ONLY — there is no
-- theorem here, and nothing in the development depends on it.
--
-- WHY IT EXISTS (Jeremy, 2026-09-05): a hand-transcription error read an
-- interior `` ` 0 `` in the exterior frame.  Nothing in this development
-- should ever be transcribed by hand; it should be rendered.
--
-- THE TWO UNIVERSES ARE RENDERED DIFFERENTLY, and that is the point of the
-- 2026-09-19 port.
--
--   * a REPRESENTATION variable prints as a Greek letter — α, β, γ, then
--     α′, β′, γ′, …;
--   * the ORDINARY type variable that NAMES it prints as the Latin letter
--     at the same position — X, Y, Z, then X′, Y′, Z′, ….
--
-- So `X` is by construction the ordinary name of `α`, `Y` of `β`, and a
-- boundary that unlocks cell α at ordinary position 0 prints as
-- `⟪ ↥X , … ⟫`.  Reading a change's letter therefore says which
-- representation it is about; if a rendered `↓` shows a letter other than
-- the one its representation was allocated with, the name map and the
-- representation it is supposed to denote have come apart, which is the
-- defect class the 2026-09-18 repairs were about.
--
-- WHAT A BOUNDARY `M ⟪ Θ , c ⟫` RENDERS AS, under an exterior environment:
--
--   * `Θ`'s CHANGES appear IN THE ORDER THEY ACT — that is, the list
--     is walked head-LAST, which is the order `_∣_⊢χ_⇒_` uses.  A `lock`
--     prints as `↓X` naming the ordinary variable it deletes, an `unlock`
--     as `↥X` naming the ordinary variable it inserts.
--   * the CONVERSION comes last and is read on the CONVERSION context —
--     unlocks performed, locks SKIPPED, a re-unlock of a live name a
--     no-op — which is a different name map from the interior's whenever
--     the boundary scope locks.  `showBnd` computes both; the body is rendered
--     on the interior, `c` on the conversion context.
--
-- USED AS A TOOL non-interactively via scripts/render_term.sh, which
-- exploits the type-error trick: `oops : e ≡ ""; oops = refl` makes Agda
-- print e's normal form in the mismatch error.  The entry points it calls
-- are at the bottom: `showTyIn`, `showRepIn`, `showTmIn`, `showConvIn`,
-- `showBndIn`, `showTCtx`, `showTermsIn`, and `showRun`, which renders a
-- whole evaluator run with the store and the rule that fired at each step.

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
  using (Boundary; changes; Change; lock; unlock)
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

-- `eReps` is the representation context, de Bruijn indexed, each entry
-- carrying BOTH names allocated for that representation variable: the
-- Greek one it prints as, and the Latin one any ordinary variable naming
-- it prints as.  `eNames` is the ordinary name map itself — exactly
-- `names Γ`, a list of representation-variable indices — so an ordinary
-- variable's rendered name is a two-step lookup, which is what the design
-- says it is.
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
applyChI (lock X α)   e = mkEnv (eReps e) (deleteAt X (eNames e))
applyChI (unlock X α) e = mkEnv (eReps e) (insertAt X α (eNames e))

applyChsI : List Change → Env → Env
applyChsI []      e = e
applyChsI (δ ∷ χ) e = applyChI δ (applyChsI χ e)

-- the conversion reading: a `lock` is SKIPPED, and an `unlock` of a name
-- that is already live is a no-op (`conv-unlock-live`,
-- strong-rep-store.Boundary §3)
applyChC : Change → Env → Env
applyChC (lock X α)   e = e
applyChC (unlock X α) e =
  if memberN α (eNames e) then e
  else mkEnv (eReps e) (insertAt X α (eNames e))

applyChsC : List Change → Env → Env
applyChsC []      e = e
applyChsC (δ ∷ χ) e = applyChC δ (applyChsC χ e)

changePiece : Env → Change → String
changePiece e (lock X α)   = "↓" ++ ordNm e X
changePiece e (unlock X α) = "↥" ++ ordOf e α

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
  "⟪ " ++ entBlock (changePieces e (changes Θ))
       ++ showConv (onames (applyChsC (changes Θ) e)) c ++ " ⟫"

------------------------------------------------------------------------
-- 6. Terms
------------------------------------------------------------------------

-- Binder names are GLOBALLY UNIQUE across one rendered term (Jeremy,
-- 2026-09-06: two sibling `Λ`s must not both print as ΛX).  The
-- type/representation counter `f` is threaded left to right through the
-- whole term; the term-binder counter is the λ-depth, restored after each
-- body, because term names are stable across steps and sibling λs may
-- share one.
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
... | l , f₁ with showTmF e tms f₁ x M
... | m , f₂ = "(" ++ l ++ " · " ++ m ++ ")" , f₂
showTmF e tms f x (Λ N) with showTmF (underΛE f e) tms (suc f) x N
... | body , f′ = "(Λ" ++ tyBinder f ++ ". " ++ body ++ ")" , f′
showTmF e tms f x (L ·[ B , A ]) with showTmF e tms f x L
... | l , f′ = l ++ " [" ++ showTy (onames e) A ++ "]" , f′
showTmF e tms f x (M ⟪ Θ , c ⟫)
  with showTmF (applyChsI (changes Θ) e) tms f x M
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
ruleName (CancelR v ri r₁ d₁ r⋉ sm rel d) = "CancelR"
ruleName (IdPush v ri r₁ r⋉ sm rel d) = "IdPush"
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
