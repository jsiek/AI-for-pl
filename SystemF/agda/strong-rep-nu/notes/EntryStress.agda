module strong-rep-nu.notes.EntryStress where

-- File Charter:
--   * STRESS PROGRAMS FOR THE TWO PROBES (2026-10-26): closed System F
--     sources written to send values back and forth across ONE type
--     variable's scope, which is how a merged scope could acquire two
--     entries of one kind for one representation variable
--     (notes/EntryProbe.agda) or a seal chain through a variable no
--     side names (notes/SideProbe.agda).  Each is compiled by
--     strong-rep-nu.Compile and run by strong-rep-nu.Eval.
-- Read with
-- scripts/render_term.sh 'stress' 'open import strong-rep-nu.notes.EntryStress'

open import Data.Nat using (ℕ)
open import Data.List using ([])
open import Data.Product using (proj₂)
open import Data.String using (String) renaming (_++_ to _+++_)

open import strong-rep-nu.Types
open import strong-rep-nu.Source
  using (STerm; `_; $_; `true; `false; ƛ_∙_; _·_; Λ_; _[_]; inferˢ)
open import strong-rep-nu.Compile using (compile)
open import strong-rep-nu.Terms using (Term)
open import strong-rep-nu.notes.EntryProbe using (probe; showT)
open import strong-rep-nu.notes.SideProbe using (firstFlaw)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Nat.Show

compileS : STerm → Maybe Term
compileS M with inferˢ 0 [] M
compileS M | just (A , d) = just (compile d)
compileS M | nothing      = nothing

-- S1  (ΛX. λk:(X⇒X)⇒ℕ. k (λy:X. y)) [ℕ] (λh:ℕ⇒ℕ. h 3)
S1 : STerm
S1 = (Λ (ƛ ((` 0 ⇒ ` 0) ⇒ `ℕ) ∙ (` 0 · (ƛ ` 0 ∙ ` 0)))) [ `ℕ ]
     · (ƛ (`ℕ ⇒ `ℕ) ∙ (` 0 · $ 3))

-- S2  (ΛX. λk:(X⇒X)⇒X⇒X. λx:X. k (λy:X. y) x) [ℕ]
--       (λh:ℕ⇒ℕ. λn:ℕ. h (h n)) 5
S2 : STerm
S2 = (Λ (ƛ ((` 0 ⇒ ` 0) ⇒ (` 0 ⇒ ` 0))
          ∙ (ƛ ` 0 ∙ ((` 1 · (ƛ ` 0 ∙ ` 0)) · ` 0)))) [ `ℕ ]
     · (ƛ (`ℕ ⇒ `ℕ) ∙ (ƛ `ℕ ∙ (` 1 · (` 1 · ` 0)))) · $ 5

-- S3  (ΛX. λf:∀Y.Y⇒Y. λx:X. f[X] (f[X] x)) [ℕ] (ΛZ. λz:Z. z) 7
S3 : STerm
S3 = (Λ (ƛ (`∀ (` 0 ⇒ ` 0))
          ∙ (ƛ ` 0 ∙ ((` 1 [ ` 0 ]) · ((` 1 [ ` 0 ]) · ` 0))))) [ `ℕ ]
     · (Λ (ƛ ` 0 ∙ ` 0)) · $ 7

-- S4  (ΛX. λf:∀Y.Y⇒Y. λx:X.
--        ((ΛW. λg:∀Y.Y⇒Y. λw:W. g[W] w) [X]) f x) [ℕ] (ΛZ. λz:Z. z) 7
S4inner : STerm
S4inner = Λ (ƛ (`∀ (` 0 ⇒ ` 0)) ∙ (ƛ ` 0 ∙ ((` 1 [ ` 0 ]) · ` 0)))

S4 : STerm
S4 = (Λ (ƛ (`∀ (` 0 ⇒ ` 0))
          ∙ (ƛ ` 0 ∙ (((S4inner [ ` 0 ]) · ` 1) · ` 0)))) [ `ℕ ]
     · (Λ (ƛ ` 0 ∙ ` 0)) · $ 7

-- S5  (ΛX. λx:X. λk:X⇒X. k (k x)) [ℕ] 7 (λn:ℕ. n)
S5 : STerm
S5 = (Λ (ƛ ` 0 ∙ (ƛ (` 0 ⇒ ` 0) ∙ (` 0 · (` 0 · ` 1))))) [ `ℕ ]
     · $ 7 · (ƛ `ℕ ∙ ` 0)

-- S6  (ΛX. λf:∀Y.(Y⇒Y)⇒Y⇒Y. λx:X. f[X] (λy:X. y) x) [ℕ]
--       (ΛZ. λh:Z⇒Z. λz:Z. h (h z)) 7
S6 : STerm
S6 = (Λ (ƛ (`∀ ((` 0 ⇒ ` 0) ⇒ (` 0 ⇒ ` 0)))
          ∙ (ƛ ` 0 ∙ (((` 1 [ ` 0 ]) · (ƛ ` 0 ∙ ` 0)) · ` 0)))) [ `ℕ ]
     · (Λ (ƛ (` 0 ⇒ ` 0) ∙ (ƛ ` 0 ∙ (` 1 · (` 1 · ` 0))))) · $ 7

-- S7  S3 with the argument applied at the variable THREE times, through
--     a helper that is itself instantiated at X
S7 : STerm
S7 = (Λ (ƛ (`∀ (` 0 ⇒ ` 0))
          ∙ (ƛ ` 0 ∙ ((` 1 [ ` 0 ])
                      · (((S4inner [ ` 0 ]) · ` 1) · ((` 1 [ ` 0 ]) · ` 0))))))
       [ `ℕ ]
     · (Λ (ƛ ` 0 ∙ ` 0)) · $ 7

showFirst : Maybe (ℕ Data.Product.× String) → String
showFirst nothing        = "side ok"
showFirst (just (n , r)) =
  "side flaw first at " +++ Data.Nat.Show.show n +++ " " +++ r

both : Maybe Term → String
both (just M) = showT (probe M) +++ "; " +++ showFirst (firstFlaw M)
both nothing  = "ILL-TYPED SOURCE"

lab : String → STerm → String
lab s M = " |" +++ s +++ ": " +++ both (compileS M)

stress : String
stress = lab "S1" S1 +++ lab "S2" S2 +++ lab "S3" S3 +++ lab "S4" S4
         +++ lab "S5" S5 +++ lab "S6" S6 +++ lab "S7" S7

-- S1, S2, S5 pass both probes.  S3, S4, S6, S7 (repeated instantiation
-- at X) give a `seal` several entries of one kind, and each also fails
-- the side probe at a seal chain, first at a `Merge`.
_ : stress ≡
    " |S1: 14 leaves; side ok |S2: 102 leaves; side ok"
    +++ " |S3: 66 leaves; [13 Merge] seal+ a2: 2 entries;"
    +++ " [14 Wrap] seal+ a2: 2 entries; [15 Merge] seal+ a2: 2 entries;"
    +++ " [16 Beta] seal+ a2: 2 entries; [17 Merge] seal+ a2: 3 entries;"
    +++ " side flaw first at 11 Merge"
    +++ " |S4: 74 leaves; [18 Merge] seal+ a2: 2 entries;"
    +++ " [18 Merge] seal+ a1: 2 entries; [19 Merge] seal+ a2: 2 entries;"
    +++ " side flaw first at 16 Merge"
    +++ " |S5: 50 leaves; side ok"
    +++ " |S6: 106 leaves; [14 Merge] seal+ a1: 2 entries;"
    +++ " [15 Beta] seal+ a1: 2 entries; [16 Merge] seal+ a1: 2 entries;"
    +++ " [16 Merge] seal+ a0: 2 entries; [17 Wrap] seal+ a1: 2 entries;"
    +++ " [17 Wrap] seal+ a0: 2 entries; [18 Merge] seal+ a1: 3 entries;"
    +++ " [19 Beta] seal+ a1: 3 entries; [20 Merge] seal+ a1: 3 entries;"
    +++ " [20 Merge] seal+ a0: 3 entries; [21 Merge] seal+ a1: 4 entries;"
    +++ " side flaw first at 11 Merge"
    +++ " |S7: 170 leaves; [17 Merge] seal+ a3: 2 entries;"
    +++ " [18 Wrap] seal+ a3: 2 entries; [19 Merge] seal+ a3: 2 entries;"
    +++ " [20 Beta] seal+ a3: 2 entries; [21 TyWrap] seal+ a4: 2 entries;"
    +++ " [22 Merge] seal+ a4: 2 entries; [23 Wrap] seal+ a4: 2 entries;"
    +++ " [24 Merge] seal+ a4: 2 entries; [25 Beta] seal+ a4: 2 entries;"
    +++ " [26 Merge] seal+ a4: 3 entries; [26 Merge] seal+ a2: 2 entries;"
    +++ " [27 Merge] seal+ a4: 3 entries; [28 Wrap] seal+ a4: 3 entries;"
    +++ " [29 Merge] seal+ a4: 3 entries; [30 Beta] seal+ a4: 3 entries;"
    +++ " [31 Merge] seal+ a4: 4 entries; side flaw first at 15 Merge"
_ = refl

-- the side probe's full rows, for classifying the flaws
open import strong-rep-nu.notes.SideProbe using (report)

rows : Maybe Term → String
rows (just M) = report 80 M
rows nothing  = "ILL-TYPED SOURCE"

sideRows : String
sideRows = " |S3: " +++ rows (compileS S3) +++ " |S4: " +++ rows (compileS S4)
           +++ " |S6: " +++ rows (compileS S6) +++ " |S7: " +++ rows (compileS S7)
