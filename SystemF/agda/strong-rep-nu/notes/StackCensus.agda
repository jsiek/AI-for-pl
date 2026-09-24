module strong-rep-nu.notes.StackCensus where

-- THE STACK CENSUS (2026-09-24, notes/MergeSketch.md): where do
-- boundaries STACK on a value?  For every state of every Examples run,
-- list each subterm `(V ⟪ Θ₁ , c₁ ⟫) ⟪ Θ₂ , c₂ ⟫` whose inner
-- `V ⟪ Θ₁ , c₁ ⟫` is a VALUE, tagged by the head of V and by the SORT and
-- head of c₁ and c₂ (a middle `idv`/`idb`/`fun`/`all`, a seal chain
-- `seal`/`t;seal`, an unseal chain `unseal`/`unseal;c`), plus the rule
-- the state fires.  Since `Merge` every such pair is a `Merge` redex.
-- Read with
-- scripts/render_term.sh 'census' 'open import strong-rep-nu.notes.StackCensus'

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.List using (List; []; _∷_; _++_; foldr)
open import Data.Maybe using (just; nothing)
open import Data.String using (String) renaming (_++_ to _+++_)

open import strong-rep-nu.Types
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.TypeCheck using (value?)
open import strong-rep-nu.Eval
open import strong-rep-nu.Show using (ruleName)
open import strong-rep-nu.Examples

-- tagged by SORT and head: a middle, a seal chain, an unseal chain
tagG : Mid → String
tagG (id (` X)) = "idv"
tagG (id A)     = "idb"
tagG (s ↦ t)    = "fun"
tagG (`∀ s)     = "all"

tagC : Conv → String
tagC (tail (mid g))     = tagG g
tagC (tail (seal X))    = "seal"
tagC (tail (t ⨾seal X)) = "t;seal"
tagC (unseal X)         = "unseal"
tagC (unseal X ⨾ c)     = "unseal;c"

tagM : Term → String
tagM (Λ N)       = "Λ"
tagM (ƛ A ∙ N)   = "ƛ"
tagM ($ n)       = "$"
tagM `true       = "b"
tagM `false      = "b"
tagM (M ⟪ Θ , c ⟫) = "⟪⟫"
tagM _           = "?"

stackedAt : Term → Conv → List String
stackedAt (V ⟪ Θ₁ , c₁ ⟫) c₂ with value? (V ⟪ Θ₁ , c₁ ⟫)
stackedAt (V ⟪ Θ₁ , c₁ ⟫) c₂ | just _  =
  (tagM V +++ "·" +++ tagC c₁ +++ "/" +++ tagC c₂) ∷ []
stackedAt (V ⟪ Θ₁ , c₁ ⟫) c₂ | nothing = []
stackedAt M c₂ = []

stacks : Term → List String
stacks (` x) = []
stacks ($ n) = []
stacks `true = []
stacks `false = []
stacks (ƛ A ∙ N) = stacks N
stacks (L · M) = stacks L ++ stacks M
stacks (Λ N) = stacks N
stacks (ν A · L ⟨ c ⟩) = stacks L
stacks (M ⟪ Θ , c ⟫) = stackedAt M c ++ stacks M

join : List String → String
join = foldr (λ s r → s +++ " " +++ r) ""

row : ∀ {Δ A M} → ℕ → Trace Δ A M → String
row {M = M} n (stop _) = showℕ n +++ " end   " +++ join (stacks M) +++ "\n"
row {M = M} n (illtyped r) = "LOST\n"
row {M = M} n (r ◅⟨ _ ⟩ tr) =
  showℕ n +++ " " +++ ruleName r +++ "  " +++ join (stacks M) +++ "\n"
    +++ row (suc n) tr

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
