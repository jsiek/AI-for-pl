module strong-rep-nu.notes.EntryProbe where

-- File Charter:
--   * THE ENTRY PROBE (2026-10-26): could a `seal`/`unseal` leaf point
--     at its PERMISSION ENTRY in the boundary's scope instead of naming
--     its type variable?  The typing already demands an entry of the
--     right kind (strong-rep-nu.Conversion §2, `SealOK`):
--       `seal` at `⁺` and `unseal` at `⁻` need an UNBIND of α,
--       `seal` at `⁻` and `unseal` at `⁺` need a BIND of α.
--     The pointer is CANONICAL when that entry is UNIQUE.  For every
--     boundary in every state of a run, this module counts each leaf's
--     entries of the required kind (under `∀` the scope is `liftᴮ Θ`).
--   * WHY UNIQUENESS SUFFICES.  A leaf keeps its α when a rule moves it
--     (`SameConv` relates two spellings of ONE representation).  So if
--     the entry is unique before and after, Wrap's `dual` reverses its
--     position and Merge's `Θ₁ ++ Θ₂` shifts the outer part's positions
--     by `length Θ₁` (Agda's scope lists act tail first), and nothing
--     else can happen: the reindexing reads Θ alone.
--   * RESULT.  In the 21 compiled runs (§3) every one of the 443 leaf
--     occurrences has EXACTLY ONE entry.  The stress programs of
--     notes/EntryStress.agda, which instantiate at one type variable
--     repeatedly, break uniqueness: a `seal` at `⁺` reaches 2, 3 and 4
--     unbind entries of one α, each first at a `Merge`.  So a pointer
--     is NOT canonical; it must be CARRIED with its entry, never
--     recomputed from α.  Carrying suffices for every rule that moves
--     a leaf (Wrap reverses positions, Merge shifts them, TyWrap's
--     `liftᴮ` and ξ-⟪⟫'s `↑ᴮ` keep them), and no rule but `ν`'s
--     compilation creates a `seal`/`unseal`: composition only keeps,
--     drops or cancels leaves.
-- Read with
-- scripts/render_term.sh 'Corpus.corpus' 'open import strong-rep-nu.notes.EntryProbe'

open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; length)
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
open import strong-rep-nu.TypeCheck using (conversion?)
open import strong-rep-nu.Eval using (step)
open import strong-rep-nu.Show using (ruleName)

------------------------------------------------------------------------
-- 1. Counting a leaf's entries

data Kind : Set where
  bindK unbindK : Kind

-- the entry a leaf needs, by its sort and polarity
sealKind : Pol → Kind
sealKind ⁺ = unbindK
sealKind ⁻ = bindK

unsealKind : Pol → Kind
unsealKind ⁺ = bindK
unsealKind ⁻ = unbindK

entries : Kind → RVar → Boundary → ℕ
entries k α []                = 0
entries bindK α (bind X β ∷ Θ) =
  (if α ≡ᵇ β then 1 else 0) + entries bindK α Θ
entries bindK α (unbind X β ∷ Θ)   = entries bindK α Θ
entries unbindK α (unbind X β ∷ Θ) =
  (if α ≡ᵇ β then 1 else 0) + entries unbindK α Θ
entries unbindK α (bind X β ∷ Θ)   = entries unbindK α Θ

-- one leaf: a tally (leaves seen) and the anomalies (count ≠ 1)
record Tally : Set where
  constructor tally
  field
    seen : ℕ
    odd  : List String

nil : Tally
nil = tally 0 []

_⊕_ : Tally → Tally → Tally
tally n xs ⊕ tally m ys = tally (n + m) (xs ++ ys)

showPol : Pol → String
showPol ⁺ = "+"
showPol ⁻ = "-"

leaf : String → Kind → Ctxᵗ → Boundary → Pol → ℕ → Tally
leaf s k Γᶜ Θ p X with lookupˡ? (names Γᶜ) X
leaf s k Γᶜ Θ p X | nothing =
  tally 1 ((s +++ " X" +++ showℕ X +++ ": unbound") ∷ [])
leaf s k Γᶜ Θ p X | just (α , _) with entries k α Θ
leaf s k Γᶜ Θ p X | just (α , _) | suc zero = tally 1 []
leaf s k Γᶜ Θ p X | just (α , _) | n =
  tally 1 ((s +++ showPol p +++ " a" +++ showℕ α +++ ": "
            +++ showℕ n +++ " entries") ∷ [])

------------------------------------------------------------------------
-- 2. Walking a conversion, a term, a run

mutual
  convE : Ctxᵗ → Boundary → Pol → Conv → Tally
  convE Γ Θ p (tail t)       = tailE Γ Θ p t
  convE Γ Θ p (unseal X)     = leaf "unseal" (unsealKind p) Γ Θ p X
  convE Γ Θ p (unseal X ⨾ c) =
    leaf "unseal" (unsealKind p) Γ Θ p X ⊕ convE Γ Θ p c

  tailE : Ctxᵗ → Boundary → Pol → Tail → Tally
  tailE Γ Θ p (mid g)     = midE Γ Θ p g
  tailE Γ Θ p (seal X)    = leaf "seal" (sealKind p) Γ Θ p X
  tailE Γ Θ p (t ⨾seal X) =
    tailE Γ Θ p t ⊕ leaf "seal" (sealKind p) Γ Θ p X

  midE : Ctxᵗ → Boundary → Pol → Mid → Tally
  midE Γ Θ p (id A)  = nil
  midE Γ Θ p (s ↦ c) = convE Γ Θ (flipᵖ p) s ⊕ convE Γ Θ p c
  midE Γ Θ p (`∀ s)  = convE (underΛ Γ) (liftᴮ Θ) p s

-- the interior is needed only to walk on into the boundary's term
open import strong-rep-nu.TypeCheck using (interior?)

termE : Ctxᵗ → Term → Tally
termE Δ (` x)            = nil
termE Δ ($ n)            = nil
termE Δ `true            = nil
termE Δ `false           = nil
termE Δ (ƛ A ∙ N)        = termE Δ N
termE Δ (L · M)          = termE Δ L ⊕ termE Δ M
termE Δ (Λ N)            = termE (underΛ Δ) N
termE Δ (ν A · L ⟨ c ⟩)  = termE Δ L
termE Δ (M ⟪ Θ , c ⟫) with interior? Δ Θ | conversion? Δ Θ
termE Δ (M ⟪ Θ , c ⟫) | just (Δᵢ , _) | just (Δᶜ , _) =
  convE Δᶜ Θ ⁺ c ⊕ termE Δᵢ M
termE Δ (M ⟪ Θ , c ⟫) | _ | _ = tally 0 ("bad frame" ∷ [])

-- a whole run: the leaves seen in all states, and each state's
-- anomalies tagged by its index and the rule that produced it
tag : ℕ → String → List String → List String
tag n r []       = []
tag n r (x ∷ xs) =
  ("[" +++ showℕ n +++ " " +++ r +++ "] " +++ x) ∷ tag n r xs

runE : ℕ → ℕ → String → Ctxᵗ → Term → Tally
runE k n r Δ M with termE Δ M
runE zero n r Δ M | tally s xs = tally s (tag n r xs ++ ("(fuel)" ∷ []))
runE (suc k) n r Δ M | tally s xs with step Δ M
runE (suc k) n r Δ M | tally s xs | just (M′ , δ , d) =
  tally s (tag n r xs) ⊕ runE k (suc n) (ruleName d) (apply δ Δ) M′
runE (suc k) n r Δ M | tally s xs | nothing = tally s (tag n r xs)

probe : Term → Tally
probe M = runE 80 0 "start" empty M

showT : Tally → String
showT (tally n xs) = showℕ n +++ " leaves" +++ join xs
  where
  join : List String → String
  join []       = ""
  join (x ∷ xs) = "; " +++ x +++ join xs

------------------------------------------------------------------------
-- 3. The compiled corpus (strong-rep-nu.Examples) and Examples §10

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

  -- every leaf of every state of the 21 runs has EXACTLY ONE entry
  _ : corpus ≡
      " |P: 6 leaves |K: 11 leaves |J: 33 leaves |F: 6 leaves"
      +++ " |U: 8 leaves |Q: 18 leaves |D: 30 leaves |L: 18 leaves"
      +++ " |R: 48 leaves |G: 24 leaves |H: 19 leaves |E: 0 leaves"
      +++ " |Eb: 32 leaves |V: 34 leaves |I: 14 leaves |N: 35 leaves"
      +++ " |A: 6 leaves |B: 22 leaves |C: 32 leaves |S: 47 leaves"
      +++ " |Bg: 0 leaves"
  _ = refl
