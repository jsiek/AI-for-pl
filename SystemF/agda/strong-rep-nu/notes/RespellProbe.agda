module strong-rep-nu.notes.RespellProbe where

-- File Charter:
--   * THE RESPELLING PROBE (2026-10-26).  Wrap respells `s` and Merge
--     respells `t₁` and `c₂` (branch `nu-respell`: by `respellᶜ`, which
--     reads the two conversion contexts' names; before it, the rules
--     carried the spellings under `SameConv`, and this probe's results
--     were the same).  Moving a
--     conversion to another boundary changes which variables' scopes
--     overlap at its position, so the indices must be renamed, like
--     shifting under a binder.  Can that renaming be COMPUTED from the
--     scopes alone?
--   * THE COMPUTATION.  The exterior's type variables are OPAQUE slots
--     `ext 0 … ext (n−1)`: only their number n is read from the context.
--     The scope is replayed over the slots, as the interior (an unbind
--     deletes, a bind inserts `rep α`) and as the conversion reading (an
--     unbind is skipped, a bind inserts unless α is already present).  A
--     slot's representation is learnt only when the scope unbinds it.
--     The renaming sends a position to the position of the same slot in
--     the target reading.
--   * THE CHECK.  At every Wrap, `renᶜ ρ s ≡ s′`; at every Merge,
--     `renᶜ ρ₁ (tail t₁) ≡ tail t₁′` and `renᶜ ρ₂ c₂ ≡ c₂′`.  Every
--     state of the 21 compiled runs and of the stress programs
--     (notes/EntryStress.agda) is stepped and each base rule inspected.
--   * RESULT (§5): every carried respelling equals the computed one —
--     318 checks over 30 runs, 55 of them a real renaming.  The
--     computation reads the scopes and the exterior's LENGTH, never a
--     name or a representation in the context.  Evidence, not proof.
-- Read with
-- scripts/render_term.sh 'everything' 'open import strong-rep-nu.notes.RespellProbe'

open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_; _<ᵇ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.List using (List; []; _∷_; _++_; length; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; _×_)
open import Data.String using (String) renaming (_++_ to _+++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.Boundary
open import strong-rep-nu.Conversion
open import strong-rep-nu.Lookup using (respell)
open import strong-rep-nu.Terms
open import strong-rep-nu.Reduction
open import strong-rep-nu.Eval using (step)
open import strong-rep-nu.Show using (ruleName)

------------------------------------------------------------------------
-- 1. Slots and the two readings, replayed symbolically

data Sym : Set where
  ext : ℕ → Sym      -- an exterior slot, its representation unknown
  rep : RVar → Sym   -- a name a bind brought in, for α

-- what the scope's unbinds taught us: exterior slot i holds α
Know : Set
Know = List (ℕ × RVar)

knownAt : Know → ℕ → Maybe RVar
knownAt []             i = nothing
knownAt ((j , α) ∷ ks) i = if i ≡ᵇ j then just α else knownAt ks i

holds : Know → Sym → RVar → Bool
holds k (rep β) α = α ≡ᵇ β
holds k (ext i) α with knownAt k i
holds k (ext i) α | just β  = α ≡ᵇ β
holds k (ext i) α | nothing = false

same : Know → Sym → Sym → Bool
same k (ext i) (ext j) = i ≡ᵇ j
same k (rep α) (rep β) = α ≡ᵇ β
same k (ext i) (rep β) = holds k (ext i) β
same k (rep α) (ext j) = holds k (ext j) α

anyHolds : Know → List Sym → RVar → Bool
anyHolds k []       α = false
anyHolds k (x ∷ xs) α = holds k x α ∨ anyHolds k xs α

insertAt : ℕ → Sym → List Sym → List Sym
insertAt zero    y xs       = y ∷ xs
insertAt (suc n) y []       = y ∷ []
insertAt (suc n) y (x ∷ xs) = x ∷ insertAt n y xs

-- delete at a position, returning what was there
deleteAt : ℕ → List Sym → Maybe Sym × List Sym
deleteAt n       []       = nothing , []
deleteAt zero    (x ∷ xs) = just x , xs
deleteAt (suc n) (x ∷ xs) with deleteAt n xs
deleteAt (suc n) (x ∷ xs) | m , ys = m , (x ∷ ys)

learn : Maybe Sym → RVar → Know → Know
learn (just (ext i)) α k = (i , α) ∷ k
learn (just (rep β)) α k = k
learn nothing        α k = k

-- the interior reading (tail first), and what its unbinds teach
interiorS : Boundary → List Sym × Know → List Sym × Know
interiorS []                st = st
interiorS (unbind Y α ∷ Θ) st with interiorS Θ st
interiorS (unbind Y α ∷ Θ) st | xs , k with deleteAt Y xs
interiorS (unbind Y α ∷ Θ) st | xs , k | m , ys = ys , learn m α k
interiorS (bind Y α ∷ Θ)   st with interiorS Θ st
interiorS (bind Y α ∷ Θ)   st | xs , k = insertAt Y (rep α) xs , k

-- the conversion reading (tail first): unbinds skipped, a live bind is
-- the re-bind clause
unionS : Know → Boundary → List Sym → List Sym
unionS k []                xs = xs
unionS k (unbind Y α ∷ Θ) xs = unionS k Θ xs
unionS k (bind Y α ∷ Θ)   xs with unionS k Θ xs
unionS k (bind Y α ∷ Θ)   xs | ys =
  if anyHolds k ys α then ys else insertAt Y (rep α) ys

slots : ℕ → List Sym
slots n = go 0 n
  where
  go : ℕ → ℕ → List Sym
  go i zero    = []
  go i (suc m) = ext i ∷ go (suc i) m

------------------------------------------------------------------------
-- 2. The renaming between two readings

nth : List Sym → ℕ → Maybe Sym
nth []       n       = nothing
nth (x ∷ xs) zero    = just x
nth (x ∷ xs) (suc n) = nth xs n

indexOf : Know → Sym → List Sym → Maybe ℕ
indexOf k y []       = nothing
indexOf k y (x ∷ xs) with same k y x
indexOf k y (x ∷ xs) | true  = just zero
indexOf k y (x ∷ xs) | false with indexOf k y xs
indexOf k y (x ∷ xs) | false | just n  = just (suc n)
indexOf k y (x ∷ xs) | false | nothing = nothing

-- an unmatched position goes far out of range, so it shows as a mismatch
far : ℕ
far = 1000

renameS : Know → List Sym → List Sym → Renameᵗ
renameS k src tgt X with nth src X
renameS k src tgt X | nothing = far + X
renameS k src tgt X | just y with indexOf k y tgt
renameS k src tgt X | just y | just n  = n
renameS k src tgt X | just y | nothing = far + X

------------------------------------------------------------------------
-- 3. Equality of conversions

_==ᵗ_ : Ty → Ty → Bool
(` X)   ==ᵗ (` Y)     = X ≡ᵇ Y
`ℕ      ==ᵗ `ℕ        = true
`𝔹      ==ᵗ `𝔹        = true
(A ⇒ B) ==ᵗ (A′ ⇒ B′) = (A ==ᵗ A′) ∧ (B ==ᵗ B′)
(`∀ A)  ==ᵗ (`∀ A′)   = A ==ᵗ A′
(` X)   ==ᵗ `ℕ        = false
(` X)   ==ᵗ `𝔹        = false
(` X)   ==ᵗ (_ ⇒ _)   = false
(` X)   ==ᵗ (`∀ _)    = false
`ℕ      ==ᵗ (` _)     = false
`ℕ      ==ᵗ `𝔹        = false
`ℕ      ==ᵗ (_ ⇒ _)   = false
`ℕ      ==ᵗ (`∀ _)    = false
`𝔹      ==ᵗ (` _)     = false
`𝔹      ==ᵗ `ℕ        = false
`𝔹      ==ᵗ (_ ⇒ _)   = false
`𝔹      ==ᵗ (`∀ _)    = false
(A ⇒ B) ==ᵗ (` _)     = false
(A ⇒ B) ==ᵗ `ℕ        = false
(A ⇒ B) ==ᵗ `𝔹        = false
(A ⇒ B) ==ᵗ (`∀ _)    = false
(`∀ A)  ==ᵗ (` _)     = false
(`∀ A)  ==ᵗ `ℕ        = false
(`∀ A)  ==ᵗ `𝔹        = false
(`∀ A)  ==ᵗ (_ ⇒ _)   = false

mutual
  eqC : Conv → Conv → Bool
  eqC (tail t)       (tail t′)        = eqT t t′
  eqC (unseal X)     (unseal Y)       = X ≡ᵇ Y
  eqC (unseal X ⨾ c) (unseal Y ⨾ c′)  = (X ≡ᵇ Y) ∧ eqC c c′
  eqC (tail t)       (unseal Y)       = false
  eqC (tail t)       (unseal Y ⨾ c′)  = false
  eqC (unseal X)     (tail t′)        = false
  eqC (unseal X)     (unseal Y ⨾ c′)  = false
  eqC (unseal X ⨾ c) (tail t′)        = false
  eqC (unseal X ⨾ c) (unseal Y)       = false

  eqT : Tail → Tail → Bool
  eqT (mid g)     (mid g′)      = eqM g g′
  eqT (seal X)    (seal Y)      = X ≡ᵇ Y
  eqT (t ⨾seal X) (t′ ⨾seal Y)  = (X ≡ᵇ Y) ∧ eqT t t′
  eqT (mid g)     (seal Y)      = false
  eqT (mid g)     (t′ ⨾seal Y)  = false
  eqT (seal X)    (mid g′)      = false
  eqT (seal X)    (t′ ⨾seal Y)  = false
  eqT (t ⨾seal X) (mid g′)      = false
  eqT (t ⨾seal X) (seal Y)      = false

  eqM : Mid → Mid → Bool
  eqM (id A)  (id B)    = A ==ᵗ B
  eqM (s ↦ c) (s′ ↦ c′) = eqC s s′ ∧ eqC c c′
  eqM (`∀ s)  (`∀ s′)   = eqC s s′
  eqM (id A)  (_ ↦ _)   = false
  eqM (id A)  (`∀ _)    = false
  eqM (s ↦ c) (id _)    = false
  eqM (s ↦ c) (`∀ _)    = false
  eqM (`∀ s)  (id _)    = false
  eqM (`∀ s)  (_ ↦ _)   = false

------------------------------------------------------------------------
-- 4. The checks at Wrap and Merge

-- a check: was it a real renaming (source ≠ target), and did it hold
record Tally : Set where
  constructor tally
  field
    checks moved : ℕ
    odd          : List String

nil : Tally
nil = tally 0 0 []

_⊕_ : Tally → Tally → Tally
tally a b xs ⊕ tally c d ys = tally (a + c) (b + d) (xs ++ ys)

one : String → Conv → Conv → Conv → Tally
one what src tgt computed =
  tally 1 (if eqC src tgt then 0 else 1)
    (if eqC computed tgt then [] else (what +++ " MISMATCH") ∷ [])

wrapCheck : ℕ → Boundary → Conv → Conv → Tally
wrapCheck n Θ s s′ with interiorS Θ (slots n , [])
wrapCheck n Θ s s′ | I , k =
  one "Wrap" s s′
    (renᶜ (renameS k (unionS k Θ (slots n)) (unionS k (dual Θ) I)) s)

mergeCheck : ℕ → Boundary → Boundary → Tail → Tail → Conv → Conv → Tally
mergeCheck n Θ₁ Θ₂ t₁ t₁′ c₂ c₂′ with interiorS Θ₂ (slots n , [])
mergeCheck n Θ₁ Θ₂ t₁ t₁′ c₂ c₂′ | I₂ , k₂ with interiorS Θ₁ (I₂ , k₂)
mergeCheck n Θ₁ Θ₂ t₁ t₁′ c₂ c₂′ | I₂ , k₂ | I₁ , k =
  one "Merge t1" (tail t₁) (tail t₁′)
    (renᶜ (renameS k (unionS k Θ₁ I₂) merged) (tail t₁))
  ⊕ one "Merge c2" c₂ c₂′
    (renᶜ (renameS k (unionS k Θ₂ (slots n)) merged) c₂)
  where
  merged : List Sym
  merged = unionS k (Θ₁ ++ Θ₂) (slots n)

-- descend the congruences to the base rule; only the context's LENGTH
-- is read
base : ∀ {Δ M N δ} → Δ ⊢ M -→ N ∣ δ → Tally
base (TyBeta v same) = nil
base (Beta v) = nil
base {Δ = Δ} (Wrap {Δᶜ = Δᶜ} {Δᵈ = Δᵈ} {Θ = Θ} {s = s} v w rc ri rd) =
  wrapCheck (length (names Δ)) Θ s (respellᶜ Δᶜ Δᵈ s)
base (TyWrap v same) = nil
base {Δ = Δ} (Merge {Δ₁ᶜ = Δ₁ᶜ} {Δ₂ᶜ = Δ₂ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ} {Θ₁ = Θ₁}
                    {Θ₂ = Θ₂} {t₁ = t₁} {c₂ = c₂} u it ri r₁ r₂ r⋉) =
  mergeCheck (length (names Δ)) Θ₁ Θ₂ t₁
    (renᵀ (respell (names Δ₁ᶜ) (names Δ⋉ᶜ)) t₁) c₂ (respellᶜ Δ₂ᶜ Δ⋉ᶜ c₂)
base (Id u b) = nil
base (ξ-·₁ st) = base st
base (ξ-·₂ v st) = base st
base (ξ-ν st) = base st
base (ξ-⟪⟫ rel st) = base st

tag : ℕ → String → List String → List String
tag n r []       = []
tag n r (x ∷ xs) =
  ("[" +++ showℕ n +++ " " +++ r +++ "] " +++ x) ∷ tag n r xs

runR : ℕ → ℕ → Ctxᵗ → Term → Tally
runR zero    n Δ M = tally 0 0 ("(fuel)" ∷ [])
runR (suc k) n Δ M with step Δ M
runR (suc k) n Δ M | just (M′ , δ , d) with base d
runR (suc k) n Δ M | just (M′ , δ , d) | tally a b xs =
  tally a b (tag (suc n) (ruleName d) xs) ⊕ runR k (suc n) (apply δ Δ) M′
runR (suc k) n Δ M | nothing = nil

probe : Term → Tally
probe M = runR 80 0 empty M

showT : Tally → String
showT (tally a b xs) =
  showℕ a +++ " checks, " +++ showℕ b +++ " moved" +++ join xs
  where
  join : List String → String
  join []       = ""
  join (x ∷ xs) = "; " +++ x +++ join xs

------------------------------------------------------------------------
-- 5. The corpus and the stress programs

module Runs where
  import strong-rep-nu.Examples as E
  open import strong-rep-nu.notes.EntryStress
    using (compileS; S1; S2; S3; S4; S5; S6; S7; S8; S9)
  open import strong-rep-nu.Source using (STerm)

  lab : String → Term → String
  lab s M = " |" +++ s +++ ": " +++ showT (probe M)

  labS : String → STerm → String
  labS s M with compileS M
  labS s M | just T  = lab s T
  labS s M | nothing = " |" +++ s +++ ": ILL-TYPED SOURCE"

  corpus : String
  corpus =
    lab "P" E.P₀ +++ lab "K" E.K₀ +++ lab "J" E.J₀ +++ lab "F" E.F₀
    +++ lab "U" E.U₀ +++ lab "Q" E.Q₀ +++ lab "D" E.D₀ +++ lab "L" E.L₀
    +++ lab "R" E.R₀ +++ lab "G" E.G₀ +++ lab "H" E.H₀ +++ lab "E" E.E₀
    +++ lab "Eb" E.E₀ᴮ +++ lab "V" E.V₀ +++ lab "I" E.I₀ +++ lab "N" E.N₀
    +++ lab "A" E.A₀ +++ lab "B" E.B₀ +++ lab "C" E.C₀ +++ lab "S" E.S₀
    +++ lab "Bg" E.Bg

  stress : String
  stress = labS "S1" S1 +++ labS "S2" S2 +++ labS "S3" S3 +++ labS "S4" S4
           +++ labS "S5" S5 +++ labS "S6" S6 +++ labS "S7" S7
           +++ labS "S8" S8 +++ labS "S9" S9

  everything : String
  everything = corpus +++ " |||" +++ stress

  -- NO MISMATCH: 318 checks, 55 of them a real renaming (source ≠
  -- carried target), every one computed from n and the scopes
  _ : everything ≡
      " |P: 3 checks, 0 moved |K: 6 checks, 1 moved |J: 9 checks, 2 moved"
      +++ " |F: 3 checks, 0 moved |U: 3 checks, 0 moved"
      +++ " |Q: 8 checks, 2 moved |D: 13 checks, 4 moved"
      +++ " |L: 8 checks, 2 moved |R: 13 checks, 4 moved"
      +++ " |G: 12 checks, 4 moved |H: 8 checks, 1 moved"
      +++ " |E: 1 checks, 0 moved |Eb: 13 checks, 1 moved"
      +++ " |V: 17 checks, 1 moved |I: 8 checks, 0 moved"
      +++ " |N: 13 checks, 3 moved |A: 4 checks, 0 moved"
      +++ " |B: 9 checks, 2 moved |C: 14 checks, 1 moved"
      +++ " |S: 13 checks, 4 moved |Bg: 1 checks, 0 moved |||"
      +++ " |S1: 5 checks, 0 moved |S2: 14 checks, 0 moved"
      +++ " |S3: 18 checks, 5 moved |S4: 19 checks, 4 moved"
      +++ " |S5: 10 checks, 0 moved |S6: 22 checks, 2 moved"
      +++ " |S7: 33 checks, 11 moved |S8: 8 checks, 0 moved"
      +++ " |S9: 10 checks, 1 moved"
  _ = refl
