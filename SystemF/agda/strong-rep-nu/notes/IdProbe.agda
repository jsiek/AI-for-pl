module strong-rep-nu.notes.IdProbe where

-- File Charter:
--   * THE ID PROBE (2026-10-26): in the Θ-entry design a `seal`/`unseal`
--     points at its permission entry, but an `id (` X)` leaf still needs
--     a NAME.  Can it be spelled on one side and moved, and created by a
--     cancellation, using the scope Θ alone (no context read)?  For every
--     `id` leaf of every boundary in every state of a run, with α the
--     leaf's representation variable:
--       (a) α has an interior name i and an exterior name e;
--       (b) `toExt Θ i ≡ just e` — GTNF's interior-to-exterior map
--           (GTNF/agda/Boundary.agda §5), ported here, reads Θ alone;
--       (c) each BIND entry of α, replayed forward through the entries
--           that act after it, lands on i (or α is unbound later); each
--           UNBIND entry of α, replayed backward through the entries that
--           act before it, lands on e.  This is how a cancellation would
--           spell the `id` it creates from the cancelled pair's entries.
--     A leaf with no entry for α is AMBIENT; one with an entry is SCOPED.
--   * RESULT (§4): (a), (b), (c) hold for every `id` leaf of every state
--     of the 21 compiled runs and the nine stress programs.  The corpus
--     and S1–S7 have only AMBIENT `id` leaves, so (c) is exercised only
--     by S8 and S9, whose round trips (a function made in X's scope goes
--     out and comes back) make `cancelᵀ` create `id X` inside a domain.
--     Evidence, not proof: four scoped occurrences in two programs.
-- Read with
-- scripts/render_term.sh 'Corpus.corpus' 'open import strong-rep-nu.notes.IdProbe'

open import Data.Nat using (ℕ; zero; suc; _+_; pred; _≡ᵇ_; _<ᵇ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; _×_)
open import Data.String using (String) renaming (_++_ to _+++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.Boundary
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.Lookup
open import strong-rep-nu.TypeCheck using (interior?; conversion?)
open import strong-rep-nu.Eval using (step)
open import strong-rep-nu.Show using (ruleName)

------------------------------------------------------------------------
-- 1. Θ-only maps.  Scope lists act TAIL FIRST: the head acts last.

_≤ᵇ_ : ℕ → ℕ → Bool
m ≤ᵇ n = (m <ᵇ n) ∨ (m ≡ᵇ n)

-- GTNF's `toExt`: an interior position back to the exterior position of
-- the same representation variable, or nothing if the scope created it
mutual
  toExt : Boundary → ℕ → Maybe ℕ
  toExt []               X = just X
  toExt (bind Y α ∷ Θ)   X =
    if X ≡ᵇ Y then seekUnbind α Θ
    else (if X <ᵇ Y then toExt Θ X else toExt Θ (pred X))
  toExt (unbind Y α ∷ Θ) X =
    if X <ᵇ Y then toExt Θ X else toExt Θ (suc X)

  seekUnbind : RVar → Boundary → Maybe ℕ
  seekUnbind α []               = nothing
  seekUnbind α (bind Y β ∷ Θ)   = seekUnbind α Θ
  seekUnbind α (unbind Y β ∷ Θ) =
    if α ≡ᵇ β then toExt Θ Y else seekUnbind α Θ

-- a position carried forward through one entry acting
fwd1 : Change → ℕ → Maybe ℕ
fwd1 (bind Y β)   p = just (if Y ≤ᵇ p then suc p else p)
fwd1 (unbind Y β) p =
  if Y ≡ᵇ p then nothing else just (if Y <ᵇ p then pred p else p)

-- ... and carried backward through one entry being undone
bwd1 : Change → ℕ → Maybe ℕ
bwd1 (bind Y β)   p =
  if Y ≡ᵇ p then nothing else just (if Y <ᵇ p then pred p else p)
bwd1 (unbind Y β) p = just (if Y ≤ᵇ p then suc p else p)

-- forward through entries that act AFTER (they precede in the list, and
-- the one nearest acts first)
fwd : Boundary → ℕ → Maybe ℕ
fwd []       p = just p
fwd (e ∷ es) p with fwd es p
fwd (e ∷ es) p | just q  = fwd1 e q
fwd (e ∷ es) p | nothing = nothing

-- backward through entries that acted BEFORE (they follow in the list,
-- the one nearest is undone first)
bwd : Boundary → ℕ → Maybe ℕ
bwd []       p = just p
bwd (e ∷ es) p with bwd1 e p
bwd (e ∷ es) p | just q  = bwd es q
bwd (e ∷ es) p | nothing = nothing

------------------------------------------------------------------------
-- 2. The checks on one `id` leaf

record Tally : Set where
  constructor tally
  field
    ambient scoped : ℕ
    odd            : List String

nil : Tally
nil = tally 0 0 []

_⊕_ : Tally → Tally → Tally
tally a s xs ⊕ tally b t ys = tally (a + b) (s + t) (xs ++ ys)

eqM : Maybe ℕ → ℕ → Bool
eqM (just m) n = m ≡ᵇ n
eqM nothing  n = false

showM : Maybe ℕ → String
showM (just m) = showℕ m
showM nothing  = "none"

-- walk the entries; `pre` holds the entries that precede (act after)
entryChecks : RVar → ℕ → ℕ → Boundary → Boundary → List String
entryChecks α i e pre [] = []
entryChecks α i e pre (bind X β ∷ post) with α ≡ᵇ β
entryChecks α i e pre (bind X β ∷ post) | true with fwd pre X
entryChecks α i e pre (bind X β ∷ post) | true | just j =
  (if j ≡ᵇ i then []
   else ("bind entry lands on " +++ showℕ j +++ ", interior name "
         +++ showℕ i) ∷ [])
  ++ entryChecks α i e (pre ++ (bind X β ∷ [])) post
entryChecks α i e pre (bind X β ∷ post) | true | nothing =
  entryChecks α i e (pre ++ (bind X β ∷ [])) post
entryChecks α i e pre (bind X β ∷ post) | false =
  entryChecks α i e (pre ++ (bind X β ∷ [])) post
entryChecks α i e pre (unbind X β ∷ post) with α ≡ᵇ β
entryChecks α i e pre (unbind X β ∷ post) | true =
  (if eqM (bwd post X) e then []
   else ("unbind entry lands on " +++ showM (bwd post X)
         +++ ", exterior name " +++ showℕ e) ∷ [])
  ++ entryChecks α i e (pre ++ (unbind X β ∷ [])) post
entryChecks α i e pre (unbind X β ∷ post) | false =
  entryChecks α i e (pre ++ (unbind X β ∷ [])) post

hasEntry : RVar → Boundary → Bool
hasEntry α []                = false
hasEntry α (bind X β ∷ Θ)   = (α ≡ᵇ β) ∨ hasEntry α Θ
hasEntry α (unbind X β ∷ Θ) = (α ≡ᵇ β) ∨ hasEntry α Θ

record Sides : Set where
  constructor sides
  field
    ext int conv : Ctxᵗ

under : Sides → Sides
under (sides e i c) = sides (underΛ e) (underΛ i) (underΛ c)

idLeaf : Sides → Boundary → ℕ → Tally
idLeaf σ Θ X with lookupˡ? (names (Sides.conv σ)) X
idLeaf σ Θ X | nothing = tally 0 0 (("id X" +++ showℕ X +++ " unbound") ∷ [])
idLeaf σ Θ X | just (α , _)
  with find? (names (Sides.int σ)) α | find? (names (Sides.ext σ)) α
idLeaf σ Θ X | just (α , _) | just (i , _) | just (e , _) =
  let odd = (if eqM (toExt Θ i) e then []
             else ("a" +++ showℕ α +++ " toExt " +++ showℕ i +++ " = "
                   +++ showM (toExt Θ i) +++ ", exterior " +++ showℕ e) ∷ [])
            ++ entryChecks α i e [] Θ
  in if hasEntry α Θ then tally 0 1 odd else tally 1 0 odd
idLeaf σ Θ X | just (α , _) | _ | _ =
  tally 0 0 (("a" +++ showℕ α +++ " not named on both sides") ∷ [])

------------------------------------------------------------------------
-- 3. Walking a conversion, a term, a run

mutual
  convI : Sides → Boundary → Conv → Tally
  convI σ Θ (tail t)       = tailI σ Θ t
  convI σ Θ (unseal X)     = nil
  convI σ Θ (unseal X ⨾ c) = convI σ Θ c

  tailI : Sides → Boundary → Tail → Tally
  tailI σ Θ (mid g)     = midI σ Θ g
  tailI σ Θ (seal X)    = nil
  tailI σ Θ (t ⨾seal X) = tailI σ Θ t

  midI : Sides → Boundary → Mid → Tally
  midI σ Θ (id (` X))   = idLeaf σ Θ X
  midI σ Θ (id `ℕ)      = nil
  midI σ Θ (id `𝔹)      = nil
  midI σ Θ (id (A ⇒ B)) = tally 0 0 ("id at a compound type" ∷ [])
  midI σ Θ (id (`∀ A))  = tally 0 0 ("id at a compound type" ∷ [])
  midI σ Θ (s ↦ c)      = convI σ Θ s ⊕ convI σ Θ c
  midI σ Θ (`∀ s)       = convI (under σ) (liftᴮ Θ) s

termI : Ctxᵗ → Term → Tally
termI Δ (` x)            = nil
termI Δ ($ n)            = nil
termI Δ `true            = nil
termI Δ `false           = nil
termI Δ (ƛ A ∙ N)        = termI Δ N
termI Δ (L · M)          = termI Δ L ⊕ termI Δ M
termI Δ (Λ N)            = termI (underΛ Δ) N
termI Δ (ν A · L ⟨ c ⟩)  = termI Δ L
termI Δ (M ⟪ Θ , c ⟫) with interior? Δ Θ | conversion? Δ Θ
termI Δ (M ⟪ Θ , c ⟫) | just (Δᵢ , _) | just (Δᶜ , _) =
  convI (sides Δ Δᵢ Δᶜ) Θ c ⊕ termI Δᵢ M
termI Δ (M ⟪ Θ , c ⟫) | _ | _ = tally 0 0 ("bad frame" ∷ [])

tag : ℕ → String → List String → List String
tag n r []       = []
tag n r (x ∷ xs) =
  ("[" +++ showℕ n +++ " " +++ r +++ "] " +++ x) ∷ tag n r xs

runI : ℕ → ℕ → String → Ctxᵗ → Term → Tally
runI k n r Δ M with termI Δ M
runI zero n r Δ M | tally a s xs = tally a s (tag n r xs ++ ("(fuel)" ∷ []))
runI (suc k) n r Δ M | tally a s xs with step Δ M
runI (suc k) n r Δ M | tally a s xs | just (M′ , δ , d) =
  tally a s (tag n r xs) ⊕ runI k (suc n) (ruleName d) (apply δ Δ) M′
runI (suc k) n r Δ M | tally a s xs | nothing = tally a s (tag n r xs)

probe : Term → Tally
probe M = runI 80 0 "start" empty M

-- states i … i+k of a run, rendered, for reading the witnesses
open import strong-rep-nu.Show using (showState)

statesFrom : ℕ → ℕ → Ctxᵗ → Term → String
statesFrom zero    zero    Δ M = showState Δ M
statesFrom zero    (suc k) Δ M with step Δ M
statesFrom zero    (suc k) Δ M | just (M′ , δ , d) =
  showState Δ M +++ "\n  --[" +++ ruleName d +++ "]-->\n"
  +++ statesFrom zero k (apply δ Δ) M′
statesFrom zero    (suc k) Δ M | nothing = showState Δ M
statesFrom (suc i) k Δ M with step Δ M
statesFrom (suc i) k Δ M | just (M′ , δ , d) = statesFrom i k (apply δ Δ) M′
statesFrom (suc i) k Δ M | nothing           = "(ended)"

showT : Tally → String
showT (tally a s xs) =
  showℕ a +++ " ambient, " +++ showℕ s +++ " scoped" +++ join xs
  where
  join : List String → String
  join []       = ""
  join (x ∷ xs) = "; " +++ x +++ join xs

------------------------------------------------------------------------
-- 4. The compiled corpus and the stress programs

module Corpus where
  import strong-rep-nu.Examples as E

  lab : String → Term → String
  lab s M = " |" +++ s +++ ": " +++ showT (probe M)

  corpus : String
  corpus =
    lab "P" E.P₀ +++ lab "K" E.K₀ +++ lab "J" E.J₀ +++ lab "F" E.F₀
    +++ lab "U" E.U₀ +++ lab "Q" E.Q₀ +++ lab "D" E.D₀ +++ lab "L" E.L₀
    +++ lab "R" E.R₀ +++ lab "G" E.G₀ +++ lab "H" E.H₀ +++ lab "E" E.E₀
    +++ lab "Eb" E.E₀ᴮ +++ lab "V" E.V₀ +++ lab "I" E.I₀ +++ lab "N" E.N₀
    +++ lab "A" E.A₀ +++ lab "B" E.B₀ +++ lab "C" E.C₀ +++ lab "S" E.S₀
    +++ lab "Bg" E.Bg

  -- no anomaly; every `id` leaf of the corpus is AMBIENT
  _ : corpus ≡
      " |P: 0 ambient, 0 scoped |K: 4 ambient, 0 scoped"
      +++ " |J: 7 ambient, 0 scoped |F: 0 ambient, 0 scoped"
      +++ " |U: 0 ambient, 0 scoped |Q: 10 ambient, 0 scoped"
      +++ " |D: 36 ambient, 0 scoped |L: 10 ambient, 0 scoped"
      +++ " |R: 10 ambient, 0 scoped |G: 24 ambient, 0 scoped"
      +++ " |H: 9 ambient, 0 scoped |E: 14 ambient, 0 scoped"
      +++ " |Eb: 40 ambient, 0 scoped |V: 74 ambient, 0 scoped"
      +++ " |I: 4 ambient, 0 scoped |N: 21 ambient, 0 scoped"
      +++ " |A: 0 ambient, 0 scoped |B: 0 ambient, 0 scoped"
      +++ " |C: 40 ambient, 0 scoped |S: 13 ambient, 0 scoped"
      +++ " |Bg: 0 ambient, 0 scoped"
  _ = refl

module Stress where
  open import strong-rep-nu.notes.EntryStress
    using (compileS; S1; S2; S3; S4; S5; S6; S7; S8; S9)
  open import strong-rep-nu.Source using (STerm)

  lab : String → STerm → String
  lab s M with compileS M
  lab s M | just T  = " |" +++ s +++ ": " +++ showT (probe T)
  lab s M | nothing = " |" +++ s +++ ": ILL-TYPED SOURCE"

  stress : String
  stress = lab "S1" S1 +++ lab "S2" S2 +++ lab "S3" S3 +++ lab "S4" S4
           +++ lab "S5" S5 +++ lab "S6" S6 +++ lab "S7" S7
           +++ lab "S8" S8 +++ lab "S9" S9

  -- the other two probes on the round trips
  open import strong-rep-nu.notes.EntryStress using (both)

  other : String
  other = " |S8: " +++ both (compileS S8) +++ " |S9: " +++ both (compileS S9)

  -- no anomaly; the round trips S8 and S9 create SCOPED `id` leaves
  _ : stress ≡
      " |S1: 0 ambient, 0 scoped |S2: 0 ambient, 0 scoped"
      +++ " |S3: 24 ambient, 0 scoped |S4: 30 ambient, 0 scoped"
      +++ " |S5: 0 ambient, 0 scoped |S6: 24 ambient, 0 scoped"
      +++ " |S7: 74 ambient, 0 scoped |S8: 0 ambient, 2 scoped"
      +++ " |S9: 12 ambient, 2 scoped"
  _ = refl

  _ : other ≡
      " |S8: 24 leaves; [10 Merge] seal+ a0: 2 entries; side ok"
      +++ " |S9: 20 leaves; [12 Merge] seal+ a1: 2 entries; side ok"
  _ = refl

  -- THE CANCELLATION, S8 states 6 and 7 (display names; ↥ is a bind,
  -- ↓ an unbind, listed in the order they act):
  --   ((λx:X. 5) ⟪ ↥X , (seal X ↦ id ℕ) ⟫) ⟪ ↓X , (unseal X ↦ id ℕ) ⟫
  --     --[Merge]-->
  --   (λx:X. 5) ⟪ ↓X , ↥X , (id X ↦ id ℕ) ⟫
  -- The domains compose as `unseal X ⨟ seal X`, which `cancelᵀ` turns
  -- into `id X`; the merged scope has entries for X's α, so the leaf is
  -- SCOPED, and its names are recovered from those entries by Θ alone.
  show8 : ℕ → ℕ → String
  show8 i k with compileS S8
  show8 i k | just T  = statesFrom i k empty T
  show8 i k | nothing = "ILL-TYPED SOURCE"
