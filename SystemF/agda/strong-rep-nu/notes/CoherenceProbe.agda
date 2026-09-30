module strong-rep-nu.notes.CoherenceProbe where

-- File Charter:
--   * THE COHERENT CONVERSION CONTEXT (2026-09-30).  The paper's
--     Fig. 2 defines δ⁺(Δ) with two `+X^α` clauses (α unnamed: add;
--     α named by some Y: no-op).  The proposal: put a COHERENCE
--     precondition on δ and Δ (every name/representation pair of Δ and
--     δ forms a partial bijection) and define δ⁺(Δ) as the plain union
--     Δ ∪ { X≔α | +X^α ∈ δ }.
--   * §1 PROVED: the Agda conversion reading IS that union, as a set of
--     representations, and each representation appears ONCE
--     (`conv-union`).  Positions are the only thing the union drops.
--   * §2 CENSUS: for every boundary of every state of every Examples
--     run, read at the context it actually sits in, which `bind`s take
--     the re-bind clause `conv-bind-live`, and at which positions.
--     Read with
--     scripts/render_term.sh 'census' \
--       'open import strong-rep-nu.notes.CoherenceProbe'
--   * The named reading is the renderer's: Show.agda names every
--     ordinary variable after its representation cell (`ordOf e α`), so
--     every rendered boundary is coherent by construction.

open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.List using (List; []; _∷_; _++_; foldr; length)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String) renaming (_++_ to _+++_)
open import Relation.Nullary using (yes; no)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.Boundary
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.TypeCheck using (runχᶜ; interior?)
open import strong-rep-nu.Eval
open import strong-rep-nu.Show using (ruleName)
open import strong-rep-nu.Examples

------------------------------------------------------------------------
-- §1  The conversion reading is the union, once per representation
------------------------------------------------------------------------

conv-union : ∀ {Ξ Δ Δᶜ χ} → Unique Δ → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δᶜ
  → Unique Δᶜ
    × (∀ {α} → Δᶜ ∋ᵅ α → Δ ∋ᵅ α ⊎ InBinds α χ)
    × (∀ {α} → Δ ∋ᵅ α ⊎ InBinds α χ → Δᶜ ∋ᵅ α)
conv-union uq cs =
  conv-unique uq cs , conv-inv cs ,
  λ where (inj₁ lv) → conv-mono cs lv
          (inj₂ ib) → conv-binds cs ib

------------------------------------------------------------------------
-- §2  The census
------------------------------------------------------------------------

showCh : Change → String
showCh (unbind X α) = "-" +++ showℕ X +++ "^" +++ showℕ α
showCh (bind X α)   = "+" +++ showℕ X +++ "^" +++ showℕ α

-- in ACTING order (the tail acts first)
showχ : List Change → String
showχ = foldr (λ δ r → r +++ " " +++ showCh δ) ""

-- each re-bind: the bind's interior position X, its representation α,
-- and the position Y where the conversion context already has α
rebinds : ∀ {Ξ Δ Δ′} (χ : List Change) → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′ → List String
rebinds [] conv[] = []
rebinds (unbind X α ∷ χ) (conv-unbind v cs) = rebinds χ cs
rebinds (bind X α ∷ χ) (conv-bind v cs f i) = rebinds χ cs
rebinds (bind X α ∷ χ) (conv-bind-live {Y = Y} v cs d)
  with X ≟ Y
... | yes _ = ("same(X=" +++ showℕ X +++ ",α=" +++ showℕ α +++ ")")
              ∷ rebinds χ cs
... | no _  = ("MOVED(X=" +++ showℕ X +++ ",Y=" +++ showℕ Y
               +++ ",α=" +++ showℕ α +++ ")")
              ∷ rebinds χ cs

atBoundary : Ctxᵗ → List Change → List String
atBoundary Γ Θ with runχᶜ (reps Γ) (names Γ) Θ
atBoundary Γ Θ | nothing = ("NO-CONV[" +++ showχ Θ +++ " ]") ∷ []
atBoundary Γ Θ | just (_ , cs) with rebinds Θ cs
atBoundary Γ Θ | just (_ , cs) | [] = []
atBoundary Γ Θ | just (_ , cs) | hs@(_ ∷ _) =
  ("[" +++ showχ Θ +++ " ] " +++ foldr (λ s r → s +++ " " +++ r) "" hs)
  ∷ []

-- every boundary, read at the context it sits in; also counted
walk : Ctxᵗ → Term → List String × ℕ
walk Γ (` x) = [] , 0
walk Γ ($ n) = [] , 0
walk Γ `true = [] , 0
walk Γ `false = [] , 0
walk Γ (ƛ A ∙ N) = walk Γ N
walk Γ (L · M) with walk Γ L | walk Γ M
... | (l , m) | (l′ , m′) = l ++ l′ , m Data.Nat.+ m′
walk Γ (Λ N) = walk (underΛ Γ) N
-- the ν's own boundary is `TyBetaBoundary` = a single bind of a FRESH
-- cell, which never takes the re-bind clause
walk Γ (ν A · L ⟨ c ⟩) = walk Γ L
walk Γ (M ⟪ Θ , c ⟫) with interior? Γ Θ
walk Γ (M ⟪ Θ , c ⟫) | nothing = ("NO-INT[" +++ showχ Θ +++ " ]") ∷ [] , 1
walk Γ (M ⟪ Θ , c ⟫) | just (Γᵢ , _) with walk Γᵢ M
... | (l , m) = atBoundary Γ Θ ++ l , suc m

join : List String → String
join = foldr (λ s r → s +++ "  " +++ r) ""

line : Ctxᵗ → ℕ → String → Term → String
line Δ n r N with walk Δ N
... | (hs , k) =
  showℕ n +++ " " +++ r +++ " #bnd=" +++ showℕ k +++ " " +++ join hs
    +++ "\n"

row : ∀ {Δ A M} → ℕ → Trace Δ A M → String
row {Δ} {M = M} n (stop _) = line Δ n "end" M
row n (illtyped r) = "LOST\n"
row {Δ} {M = M} n (r ◅⟨ _ ⟩ tr) =
  line Δ n (ruleName r) M +++ row (suc n) tr

run : ∀ {Δ A M} → String → ℕ → Δ ∣ [] ⊢ M ⦂ A → String
run nm k ⊢M = "== " +++ nm +++ "\n" +++ row 0 (eval k _ ⊢M)

census : String
census =
  run "P" 5 P₀-⊢ +++ run "K" 9 K₀-⊢ +++ run "J" 12 J₀-⊢
  +++ run "F" 5 F₀-⊢ +++ run "U" 6 U₀-⊢ +++ run "Q" 11 Q₀-⊢
  +++ run "D" 17 D₀-⊢ +++ run "L" 11 L₀-⊢ +++ run "R" 16 R₀-⊢
  +++ run "G" 14 G₀-⊢ +++ run "H" 10 H₀-⊢ +++ run "E" 16 E₀ᴮ-⊢
  +++ run "V" 19 V₀-⊢ +++ run "I" 10 I₀-⊢ +++ run "N" 15 N₀-⊢
  +++ run "A" 8 A₀-⊢ +++ run "B" 13 B₀-⊢ +++ run "C" 19 C₀-⊢
  +++ run "S" 15 S₀-⊢
