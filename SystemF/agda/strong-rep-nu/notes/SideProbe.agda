module strong-rep-nu.notes.SideProbe where

-- File Charter:
--   * THE SIDE PROBE (2026-10-26): could conversions name their type
--     variables PER SIDE (a seal's or unseal's variable on the side
--     where the scope gives it a name, an `id`'s on both) instead of
--     through the conversion context?  For every boundary in every
--     state of a run, each leaf is checked at its polarity:
--       - `seal X` at `⁺` needs its α named on the EXTERIOR; at `⁻`
--         on the INTERIOR;
--       - `unseal X` at `⁺` needs α named on the INTERIOR; at `⁻` on
--         the EXTERIOR;
--       - a leaf's payload must be readable on the OPPOSITE side at the
--         end of its chain that meets the middle, and on its own side at
--         every other link (a link's source is the previous target);
--       - `id (` X)` needs α named on BOTH sides.
--     A row lists the flaws of one state and the rule that produced it.
--   * RESULT (§5): PROBLEM 2 IS REACHABLE from closed plain source, in
--     5 of the 21 compiled runs (K, J, Eb, V, C), each first at a
--     `Merge`.  All five instantiate a polymorphic argument at the
--     enclosing type variable (`f [X]`), so a cell's payload is another
--     cell (`α₀ := ` α₁`).  The merged scope binds α₁ and then unbinds
--     it, and the composed chain `seal α₁ ⨾seal α₀` passes through
--     `` ` α₁ ``, which NEITHER side names.  Before the `Merge` every
--     boundary passes.  No `id` leaf ever fails.
-- Read with
-- scripts/render_term.sh 'report 40 E.P₀' 'open import strong-rep-nu.notes.SideProbe' 'import strong-rep-nu.Examples as E'

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.String using (String) renaming (_++_ to _+++_)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.Boundary
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.Lookup
open import strong-rep-nu.TypeCheck using (interior?; conversion?)
open import strong-rep-nu.Eval using (step)
open import strong-rep-nu.Show using (ruleName)

-- A position's polarity, tracked by this probe as it walks a
-- conversion: `⁻` inside an odd number of function domains.  (Since
-- 2026-10-26d the judgement itself has no polarity index; a domain is
-- checked under the dual scope, which grants what `⁻` grants here.)
data Pol : Set where
  ⁺ ⁻ : Pol

flipᵖ : Pol → Pol
flipᵖ ⁺ = ⁻
flipᵖ ⁻ = ⁺


------------------------------------------------------------------------
-- 1. The three readings of one boundary

record Sides : Set where
  constructor sides
  field
    ext int conv : Ctxᵗ

under : Sides → Sides
under (sides e i c) = sides (underΛ e) (underΛ i) (underΛ c)

-- the side a leaf's variable must be NAMED on, and the opposite side,
-- on which its payload must be READABLE
data Side : Set where
  extS intS : Side

other : Side → Side
other extS = intS
other intS = extS

at : Sides → Side → Ctxᵗ
at (sides e i c) extS = e
at (sides e i c) intS = i

showSide : Side → String
showSide extS = "ext"
showSide intS = "int"

-- `seal` at `⁺` is named outside, `unseal` at `⁺` inside
sealHome : Pol → Side
sealHome ⁺ = extS
sealHome ⁻ = intS

unsealHome : Pol → Side
unsealHome ⁺ = intS
unsealHome ⁻ = extS

------------------------------------------------------------------------
-- 2. The checks on one leaf

noName : Ctxᵗ → RVar → String → List String
noName Γ α msg with find? (names Γ) α
noName Γ α msg | just _  = []
noName Γ α msg | nothing = msg ∷ []

payload : Ctxᵗ → RVar → Maybe Ty
payload Γ α with lookupʳ? (reps Γ) α
payload Γ α | just (bindR R , _) = just R
payload Γ α | just (abstR , _)   = nothing
payload Γ α | nothing            = nothing

unreadable : Ctxᵗ → RVar → Ctxᵗ → String → List String
unreadable Γ α Γ′ msg with payload Γ α
unreadable Γ α Γ′ msg | nothing = (msg +++ "(no payload)") ∷ []
unreadable Γ α Γ′ msg | just R with unread? (names Γ′) R
unreadable Γ α Γ′ msg | just R | just _  = []
unreadable Γ α Γ′ msg | just R | nothing = msg ∷ []

showPol : Pol → String
showPol ⁺ = "+"
showPol ⁻ = "-"

tag : String → Pol → ℕ → RVar → String
tag k p X α =
  k +++ showPol p +++ " X" +++ showℕ X +++ " a" +++ showℕ α +++ ": "

-- a seal or unseal leaf named on side `h` whose payload is read on
-- side `r`: the opposite side at the chain's end that meets the
-- middle, the home side at every other link
leaf : String → Side → Side → Sides → Pol → ℕ → List String
leaf k h r σ p X with lookupˡ? (names (Sides.conv σ)) X
leaf k h r σ p X | nothing = (k +++ " X" +++ showℕ X +++ ": unbound") ∷ []
leaf k h r σ p X | just (α , _) =
  noName (at σ h) α (tag k p X α +++ "no name on " +++ showSide h)
  ++ unreadable (Sides.conv σ) α (at σ r)
       (tag k p X α +++ "payload unreadable on " +++ showSide r)

-- where the payload of a link is read: after another seal, at home
sealRead : Side → Tail → Side
sealRead h (mid g)     = other h
sealRead h (seal Y)    = h
sealRead h (t ⨾seal Y) = h

-- before another unseal, at home
unsealRead : Side → Conv → Side
unsealRead h (tail t)       = other h
unsealRead h (unseal Y)     = h
unsealRead h (unseal Y ⨾ c) = h

idLeaf : Sides → ℕ → List String
idLeaf σ X with lookupˡ? (names (Sides.conv σ)) X
idLeaf σ X | nothing = ("id X" +++ showℕ X +++ ": unbound") ∷ []
idLeaf σ X | just (α , _) =
  noName (Sides.ext σ) α (tag "id" ⁺ X α +++ "no name on ext")
  ++ noName (Sides.int σ) α (tag "id" ⁺ X α +++ "no name on int")

------------------------------------------------------------------------
-- 3. Walking a conversion, a term, a run

mutual
  convF : Sides → Pol → Conv → List String
  convF σ p (tail t)       = tailF σ p t
  convF σ p (unseal X)     =
    leaf "unseal" (unsealHome p) (other (unsealHome p)) σ p X
  convF σ p (unseal X ⨾ c) =
    leaf "unseal" (unsealHome p) (unsealRead (unsealHome p) c) σ p X
    ++ convF σ p c

  tailF : Sides → Pol → Tail → List String
  tailF σ p (mid g)     = midF σ p g
  tailF σ p (seal X)    =
    leaf "seal" (sealHome p) (other (sealHome p)) σ p X
  tailF σ p (t ⨾seal X) =
    tailF σ p t ++ leaf "seal" (sealHome p) (sealRead (sealHome p) t) σ p X

  midF : Sides → Pol → Mid → List String
  midF σ p (id (` X))   = idLeaf σ X
  midF σ p (id `ℕ)      = []
  midF σ p (id `𝔹)      = []
  midF σ p (id (A ⇒ B)) = "id at a compound type" ∷ []
  midF σ p (id (`∀ A))  = "id at a compound type" ∷ []
  midF σ p (s ↦ c)      = convF σ (flipᵖ p) s ++ convF σ p c
  midF σ p (`∀ s)       = convF (under σ) p s

termF : Ctxᵗ → Term → List String
termF Δ (` x)            = []
termF Δ ($ n)            = []
termF Δ `true            = []
termF Δ `false           = []
termF Δ (ƛ A ∙ N)        = termF Δ N
termF Δ (L · M)          = termF Δ L ++ termF Δ M
termF Δ (Λ N)            = termF (underΛ Δ) N
termF Δ (ν A · L ⟨ c ⟩)  = termF Δ L
termF Δ (M ⟪ Θ , c ⟫) with interior? Δ Θ | conversion? Δ Θ
termF Δ (M ⟪ Θ , c ⟫) | just (Δᵢ , _) | just (Δᶜ , _) =
  convF (sides Δ Δᵢ Δᶜ) ⁺ c ++ termF Δᵢ M
termF Δ (M ⟪ Θ , c ⟫) | just _  | nothing = "no conversion reading" ∷ []
termF Δ (M ⟪ Θ , c ⟫) | nothing | _       = "no interior reading" ∷ []

-- one line per state with flaws: its index, the rule that produced it
row : ℕ → String → List String → String
row n r []       = ""
row n r (f ∷ fs) = "[" +++ showℕ n +++ " " +++ r +++ "] " +++ join (f ∷ fs)
  where
  join : List String → String
  join []       = ""
  join (x ∷ xs) = x +++ "; " +++ join xs

run : ℕ → ℕ → String → Ctxᵗ → Term → String
run zero    n r Δ M = row n r (termF Δ M) +++ "(out of fuel)"
run (suc k) n r Δ M with step Δ M
run (suc k) n r Δ M | just (M′ , δ , d) =
  row n r (termF Δ M) +++ run k (suc n) (ruleName d) (apply δ Δ) M′
run (suc k) n r Δ M | nothing = row n r (termF Δ M) +++ "(end " +++ showℕ n +++ ")"

report : ℕ → Term → String
report k M = run k 0 "start" empty M

------------------------------------------------------------------------
-- 3b. Raw dumps of every boundary's readings in one state

rawL : List ℕ → String
rawL []       = ""
rawL (x ∷ xs) = showℕ x +++ "," +++ rawL xs

rawΘ : Boundary → String
rawΘ []                = ""
rawΘ (bind X α ∷ Θ)   = "bind " +++ showℕ X +++ " a" +++ showℕ α +++ "; " +++ rawΘ Θ
rawΘ (unbind X α ∷ Θ) = "unbind " +++ showℕ X +++ " a" +++ showℕ α +++ "; " +++ rawΘ Θ

dumpT : Ctxᵗ → Term → String
dumpT Δ (` x)           = ""
dumpT Δ ($ n)           = ""
dumpT Δ `true           = ""
dumpT Δ `false          = ""
dumpT Δ (ƛ A ∙ N)       = dumpT Δ N
dumpT Δ (L · M)         = dumpT Δ L +++ dumpT Δ M
dumpT Δ (Λ N)           = dumpT (underΛ Δ) N
dumpT Δ (ν A · L ⟨ c ⟩) = dumpT Δ L
dumpT Δ (M ⟪ Θ , c ⟫) with interior? Δ Θ | conversion? Δ Θ
dumpT Δ (M ⟪ Θ , c ⟫) | just (Δᵢ , _) | just (Δᶜ , _) =
  " {ext [" +++ rawL (names Δ) +++ "] scope [" +++ rawΘ Θ
  +++ "] int [" +++ rawL (names Δᵢ) +++ "] conv [" +++ rawL (names Δᶜ)
  +++ "]}" +++ dumpT Δᵢ M
dumpT Δ (M ⟪ Θ , c ⟫) | _ | _ = " {bad}"

dumpAt : ℕ → Ctxᵗ → Term → String
dumpAt zero    Δ M = dumpT Δ M
dumpAt (suc k) Δ M with step Δ M
dumpAt (suc k) Δ M | just (M′ , δ , d) = dumpAt k (apply δ Δ) M′
dumpAt (suc k) Δ M | nothing           = "(ended)"

rawAt : ℕ → Term → String
rawAt k M = dumpAt k empty M

------------------------------------------------------------------------
-- 4. The first flawed state of a run

flawsAt : ℕ → Ctxᵗ → Term → List String
flawsAt zero    Δ M = termF Δ M
flawsAt (suc k) Δ M with step Δ M
flawsAt (suc k) Δ M | just (M′ , δ , d) = flawsAt k (apply δ Δ) M′
flawsAt (suc k) Δ M | nothing           = "(ended)" ∷ []

firstFrom : ℕ → ℕ → String → Ctxᵗ → Term → Maybe (ℕ × String)
firstFrom k n r Δ M with termF Δ M
firstFrom k n r Δ M | f ∷ fs = just (n , r)
firstFrom zero n r Δ M | [] = nothing
firstFrom (suc k) n r Δ M | [] with step Δ M
firstFrom (suc k) n r Δ M | [] | just (M′ , δ , d) =
  firstFrom k (suc n) (ruleName d) (apply δ Δ) M′
firstFrom (suc k) n r Δ M | [] | nothing = nothing

firstFlaw : Term → Maybe (ℕ × String)
firstFlaw M = firstFrom 80 0 "start" empty M

------------------------------------------------------------------------
-- 5. The compiled corpus (strong-rep-nu.Examples) and Examples §10

module Corpus where
  import strong-rep-nu.Examples as E

  lab : String → Term → String
  lab s M = " |" +++ s +++ ": " +++ report 80 M

  corpus : String
  corpus =
    lab "P" E.P₀ +++ lab "K" E.K₀ +++ lab "J" E.J₀ +++ lab "F" E.F₀
    +++ lab "U" E.U₀ +++ lab "Q" E.Q₀ +++ lab "D" E.D₀ +++ lab "L" E.L₀
    +++ lab "R" E.R₀ +++ lab "G" E.G₀ +++ lab "H" E.H₀ +++ lab "E" E.E₀
    +++ lab "Eb" E.E₀ᴮ +++ lab "V" E.V₀ +++ lab "I" E.I₀ +++ lab "N" E.N₀
    +++ lab "A" E.A₀ +++ lab "B" E.B₀ +++ lab "C" E.C₀ +++ lab "S" E.S₀
    +++ lab "Bg" E.Bg

  -- the first flawed state of each run, and the rule that produced it
  firsts : List (Maybe (ℕ × String))
  firsts =
    firstFlaw E.P₀ ∷ firstFlaw E.K₀ ∷ firstFlaw E.J₀ ∷ firstFlaw E.F₀
    ∷ firstFlaw E.U₀ ∷ firstFlaw E.Q₀ ∷ firstFlaw E.D₀ ∷ firstFlaw E.L₀
    ∷ firstFlaw E.R₀ ∷ firstFlaw E.G₀ ∷ firstFlaw E.H₀ ∷ firstFlaw E.E₀
    ∷ firstFlaw E.E₀ᴮ ∷ firstFlaw E.V₀ ∷ firstFlaw E.I₀ ∷ firstFlaw E.N₀
    ∷ firstFlaw E.A₀ ∷ firstFlaw E.B₀ ∷ firstFlaw E.C₀ ∷ firstFlaw E.S₀
    ∷ firstFlaw E.Bg ∷ []

  _ : firsts ≡
      nothing ∷ just (6 , "Merge") ∷ just (9 , "Merge") ∷ nothing
    ∷ nothing ∷ nothing ∷ nothing ∷ nothing
    ∷ nothing ∷ nothing ∷ nothing ∷ nothing
    ∷ just (12 , "Merge") ∷ just (15 , "Merge") ∷ nothing ∷ nothing
    ∷ nothing ∷ nothing ∷ just (12 , "Merge") ∷ nothing
    ∷ nothing ∷ []
  _ = refl

  -- THE WITNESS, Examples §1b:
  --   ((ΛX. λf:(∀Y. Y⇒𝔹). f[X]) [𝔹] · (ΛZ. λz:Z. true)) · false.
  -- Store α₀ := ` α₁, α₁ := 𝔹 (Y := X, X := 𝔹).  State 5 is clean:
  --   (((λx. true) ⟪ unbind α₁, bind α₀ , seal α₀ ↦ id 𝔹 ⟫)
  --                ⟪ bind α₁ , seal α₁ ↦ id 𝔹 ⟫) · false
  -- (the inner scope merged from the crossing's lifted unbind and ν's
  -- bind).  State 6 merges them: scope bind α₁, bind α₀, unbind α₁ (in
  -- the order they act), exterior names nothing, interior names α₀
  -- only, and the domain is the chain `seal α₁ ⨾seal α₀` at `⁻`:
  -- 𝔹 ⇝ ` α₁ ⇝ ` α₀.  ` α₁ is on neither side.
  _ : flawsAt 5 empty E.K₀ ≡ []
  _ = refl

  _ : flawsAt 6 empty E.K₀ ≡
        "seal- X1 a1: no name on int"
      ∷ "seal- X0 a0: payload unreadable on int" ∷ []
  _ = refl

  _ : rawAt 6 E.K₀ ≡
      " {ext [] scope [unbind 1 a1; bind 0 a0; bind 0 a1; ] int [0,] conv [0,1,]}"
  _ = refl
