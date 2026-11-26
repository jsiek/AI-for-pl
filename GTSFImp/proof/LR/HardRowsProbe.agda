module proof.LR.HardRowsProbe where

-- File Charter:
--   * Concrete probes of the cast lemma's hard rows (notes/logrel-dgg.md,
--     "The cast lemma: the case table"), checked before their proofs.
--   * A. Left `inst` against a right non-`inst` at `∀⊑∀` exists: the
--     right `(inst d₀) !`.  Both allocate at the cast, the right one
--     step later (after its `ground` step); the row reduces to `inst`
--     against `inst` followed by the right's injection.
--   * B (F2). Case 4 (left `inst`, X left-only) in `≻` at source right
--     type `★` against a right projection: the goal fails at stage 3
--     (`goalB`).  Under the old relation the hypothesis held there: its
--     `∀⊑`-into-`★` clause was read one stage down and its body into `★`
--     one more.  Now the clause is read at the same stage
--     (`allOnlyG`), so its body is read at stage 2 and relates the
--     same function applications `goalB` refutes.
--   * C (F1). A left value cast (`∀ᶜ`, or `gen`, case 5) against a right
--     projection, at a source `∀⊑` into `★`: the goal fails in `≺` at
--     stage 1 (`goalC`, `goalG`), since the right's projection blames
--     while the left is a value.  Under the old relation the hypothesis
--     held, the left's instantiation taking its one counted step.  Now
--     the clause says the right is injected at the ground its body
--     predicts, `★ → ★`, and `0!` is not (`noHypC`, `noHypG`).

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; s≤s; z≤n; _≤′_; ≤′-refl; ≤′-step; _≤_;
  ≤′-reflexive)
  renaming (zero to zeroℕ; suc to sucℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ᵛ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans;
  cong; sym)
open import Relation.Nullary using (¬_)

open import Types
open import TyStore using (TyStore; store-empty)
open import Consistency
open import CastTerms
open import Primitives using (κℕ)
open import Reduction
open import Eval using (step?; step-result; eval; evalFrom; EvalOutcome;
  outcomeCtx; finalTerm; returned; EvalResult; term; trace; value; changes)
open import LR.Precision
open import LR.EagerCast
open import LR.Desc
open import LR.World
open import LR.Steps
open import LR.Relation
open import proof.Reduction.Determinism using (det; blame-no-step;
  value-run-stops; det-value-run; det-value-↠)
open import proof.TypeInTermSubst using (toRename-id-eq;
  renameᵗᵐ-preserves-Value)
open import proof.Reduction.ValueIrreducibleProof using (value-no-step)
open import proof.LR.Case6Probe using (w₀)

------------------------------------------------------------------------
-- Shared pieces
------------------------------------------------------------------------

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

-- `X → X` and `X → ★`, X bound (index 0)
XX X★ : Ty 1
XX = ＇ zero ⇒ ＇ zero
X★ = ＇ zero ⇒ ★

-- the injection at `ℕ` and the projection at `★ → ★`
-- (at the identity environment, as run-time casts are)
injℕ : ∀ {Δ} → idᶜ {Δ} ⊢ ℕᵗ ∼ ★
injℕ = (id (‵ `ℕ)) !

proj⇒ : ∀ {Δ} → idᶜ {Δ} ⊢ ★ ∼ ★ ⇒ ★
proj⇒ = ？ (id ★ ↦ id ★)

-- an injected constant
nℕ : ∀ {Δ} → ℕ → Term Δ
nℕ k = $ (κℕ k) ⟨ injℕ ⟩

-- k steps of the executable reduction
stepN : ∀ {Δ} → TyStore Δ → ℕ → Term Δ → Maybe (Σ[ Δ′ ∈ TyCtx ] Term Δ′)
stepN S zeroℕ M = just (_ , M)
stepN S (sucℕ k) M with step? S M
stepN S (sucℕ k) M | nothing = nothing
stepN S (sucℕ k) M | just (step-result χ N _) = stepN (applyStore χ S) k N

-- the store size after k steps
storeAfter : ℕ → Term 0 → Maybe ℕ
storeAfter k M with stepN store-empty k M
storeAfter k M | just (Δ′ , N) = just Δ′
storeAfter k M | nothing = nothing

final : ∀ {M : Term 0} → Maybe (EvalOutcome M)
  → Maybe (Σ[ Δ′ ∈ TyCtx ] Term Δ′)
final (just r) = just (outcomeCtx r , finalTerm r)
final nothing = nothing

-- a run of the blame term reaches no value
blame-stuck : ∀ {Δ Δ′} {χs : StoreChanges Δ Δ′} {N : Term Δ′}
  → blame —↠[ χs ] N → Value N → ⊥
blame-stuck ↠-refl ()
blame-stuck (↠-step s _) _ = blame-no-step s

------------------------------------------------------------------------
-- A. Left `inst` against right `(inst d₀) !`, at `∀⊑∀`
------------------------------------------------------------------------

-- the body cast at X's mode `X∼★`: `？X ↦ X!`
c₀ : instᵐ []ᵛ ⊢ XX ∼ ⇑ᵗ (★ ⇒ ★)
c₀ = (？ (id (＇ zero))) ↦ ((id (＇ zero)) !)

clA : []ᵛ ⊢ `∀ XX ∼ ★ ⇒ ★
clA = (inst_ ⦃ nonvar-fun ⦄ ⦃ ∈-fun-left var-∈ ⦄ c₀) (λ ())

-- the right: the same `inst`, then injected
crA : []ᵛ ⊢ `∀ XX ∼ ★
crA = clA !

clA-eager : Eager clA
clA-eager = e-inst ⦃ nonvar-fun ⦄ ⦃ ∈-fun-left var-∈ ⦄
  (e-↦ (e-？ e-id) (e-! e-id))

crA-eager : Eager crA
crA-eager = e-! clA-eager

-- source `∀X.X→X ⊑ ∀Y.Y→Y` (X paired); target `★→★ ⊑ ★`
pA : [] ⊢ `∀ XX ⊑ `∀ XX
pA = ∀⊑∀ (⇒⊑⇒ (X⊑Y ↔-here) (X⊑Y ↔-here))

rA : [] ⊢ ★ ⇒ ★ ⊑ ★
rA = ⇒⊑★ ★⊑★ ★⊑★

-- the precision `inst` against `inst` needs, at the right's ground
rAG : [] ⊢ ★ ⇒ ★ ⊑ ★ ⇒ ★
rAG = ⇒⊑⇒ ★⊑★ ★⊑★

idΛ : Term 0
idΛ = Λ (ƛ (` 0))

-- the left allocates at its first step
leftAllocA : storeAfter 1 (idΛ ⟨ clA ⟩) ≡ just 1
leftAllocA = refl

-- the right takes its `ground` step first, then allocates
rightGroundA : storeAfter 1 (idΛ ⟨ crA ⟩) ≡ just 0
rightGroundA = refl

rightAllocA : storeAfter 2 (idΛ ⟨ crA ⟩) ≡ just 1
rightAllocA = refl

-- both return the argument, `3` injected at `ℕ` (its cast renamed
-- along the two allocations)
leftRunA : final (eval 30 ((idΛ ⟨ clA ⟩) · nℕ 3))
  ≡ just (2 , $ (κℕ 3) ⟨ _ ⟩)
leftRunA = refl

rightRunA : final (eval 30 (((idΛ ⟨ crA ⟩) ⟨ proj⇒ ⟩) · nℕ 3))
  ≡ just (2 , $ (κℕ 3) ⟨ _ ⟩)
rightRunA = refl

------------------------------------------------------------------------
-- C. A left value cast against a right projection, at `∀⊑` into `★`
------------------------------------------------------------------------

-- the right value: `$ 0` injected at `ℕ`
Vr★ : Term 0
Vr★ = nℕ 0

-- its projection at `★ → ★` blames
right-blames : ∀ {Δ′} {χs : StoreChanges 0 Δ′} {N : Term Δ′}
  → Vr★ ⟨ proj⇒ ⟩ —↠[ χs ] N → Value N → ⊥
right-blames ↠-refl (_ 《 () 》)
right-blames (↠-step s rest) vN
    with det s (pure-step (tag-untag-bad ($ (κℕ 0)) (λ ())))
right-blames (↠-step s rest) vN | refl = blame-stuck rest vN

-- C1: left `∀ᶜ (id ↦ id) : ∀X.X→X ∼ ∀X.X→X`, right `？(★→★)`;
-- source `∀X.X→X ⊑ ★`, target `∀X.X→X ⊑ ★→★`, X left-only
clC : []ᵛ ⊢ `∀ XX ∼ `∀ XX
clC = ∀ᶜ (id (＇ zero) ↦ id (＇ zero))

clC-eager : Eager clC
clC-eager = e-∀ (e-↦ e-id e-id)

proj-eager : Eager (proj⇒ {0})
proj-eager = e-？ (e-↦ e-id e-id)

pC : [] ⊢ `∀ XX ⊑ ★
pC = ∀⊑ nonvar-fun (∈-fun-left var-∈) (⇒⊑★ (X⊑★ only-here) (X⊑★ only-here))

rC : [] ⊢ `∀ XX ⊑ ★ ⇒ ★
rC = ∀⊑ nonvar-fun (∈-fun-left var-∈) (⇒⊑⇒ (X⊑★ only-here) (X⊑★ only-here))

-- the hypothesis fails: the clause predicts an injection at `★ → ★`
noHypC : ¬ 𝒱ᵀ ≺ 1 pC w₀ closedI idΛ Vr★
noHypC (t , () , f)

-- the goal does not: the left is a value, the right blames
goalC : ¬ ℰ ≺ 1 rC w₀ closedI (idΛ ⟨ clC ⟩) (Vr★ ⟨ proj⇒ ⟩)
goalC (inj₁ (_ , _ , _ , more s _)) =
  value-no-step ((Λ (ƛ (` 0))) 《 all 》) s
goalC (inj₂ (inj₁ (_ , _ , _ , s≤s z≤n , ())))
goalC (inj₂ (inj₂ (_ , _ , _ , _ , _ , _ , _ , _ , _ ,
    _ , _ , runR , _ , vr , _))) = right-blames runR vr

-- C2 (case 5): left `gen (∀ᶜ (id Z ↦ ？X))
-- : ∀Z.Z→★ ∼ ∀X.∀Z.Z→X`, right `？(★→★)`; source `∀Z.Z→★ ⊑ ★`,
-- target `∀X.∀Z.Z→X ⊑ ★→★`, X and Z left-only
ZX : Ty 2
ZX = ＇ zero ⇒ ＇ (suc zero)

genBody : genᵐ []ᵛ ⊢ ⇑ᵗ (`∀ X★) ∼ `∀ ZX
genBody = ∀ᶜ (id (＇ zero) ↦ ？ (id (＇ (suc zero))))

z∈ZX : zero ∈ᵗ `∀ ZX
z∈ZX = ∈-all (∈-fun-right (∉-var fin-suc≢zero) var-∈)

clG : []ᵛ ⊢ `∀ X★ ∼ `∀ (`∀ ZX)
clG = (gen_ ⦃ nonvar-all ⦄ ⦃ z∈ZX ⦄ genBody) (λ ())

clG-eager : Eager clG
clG-eager = e-gen ⦃ nonvar-all ⦄ ⦃ z∈ZX ⦄ (e-∀ (e-↦ e-id (e-？ e-id))) tt

pG : [] ⊢ `∀ X★ ⊑ ★
pG = ∀⊑ nonvar-fun (∈-fun-left var-∈) (⇒⊑★ (X⊑★ only-here) ★⊑★)

rG : [] ⊢ `∀ (`∀ ZX) ⊑ ★ ⇒ ★
rG = ∀⊑ nonvar-all z∈ZX
  (∀⊑ nonvar-fun (∈-fun-left var-∈)
    (⇒⊑⇒ (X⊑★ only-here) (X⊑★ (only-only only-here))))

-- `Λ ƛ (0!)`, typed at `∀Z.Z→★`
VlG : Term 0
VlG = Λ (ƛ (nℕ 0))

noHypG : ¬ 𝒱ᵀ ≺ 1 pG w₀ closedI VlG Vr★
noHypG (t , () , f)

goalG : ¬ ℰ ≺ 1 rG w₀ closedI (VlG ⟨ clG ⟩) (Vr★ ⟨ proj⇒ ⟩)
goalG (inj₁ (_ , _ , _ , more s _)) =
  value-no-step
    ((Λ (ƛ (nℕ 0))) 《 genᵥ ⦃ nonvar-all ⦄ ⦃ z∈ZX ⦄ (λ ()) safe-∀ 》) s
goalG (inj₂ (inj₁ (_ , _ , _ , s≤s z≤n , ())))
goalG (inj₂ (inj₂ (_ , _ , _ , _ , _ , _ , _ , _ , _ ,
    _ , _ , runR , _ , vr , _))) = right-blames runR vr

------------------------------------------------------------------------
-- B. Case 4 in `≻` at source right type `★`: the guard is paid twice
------------------------------------------------------------------------

-- Left `inst (？X ↦ X!) : ∀X.X→X ∼ ★→★` (`clA`), right `？(★→★)`;
-- source `∀X.X→X ⊑ ★` (`pC`, X left-only), target `★→★ ⊑ ★→★`
-- (`rAG`).  Left `Λ ƛ x`, right the constant function `ƛ (0!)`
-- injected at `★→★`.  Under the old relation, at stage 3 the
-- hypothesis's clause was read at stage 2, and its body `X→X ⊑ ★` at
-- stage 1, so it only asked the right's applications to run 1 step,
-- which they do.  The goal: the right projects in 1 step, leaving
-- stage 2 for `★→★ ⊑ ★→★`, whose applications at stage 2 must give
-- related results at stage 1: `5!` against `0!`, which are not.

cInj : idᶜ {0} ⊢ ★ ⇒ ★ ∼ ★
cInj = (id ★ ↦ id ★) !

Wr₀ : Term 0
Wr₀ = ƛ (nℕ 0)

VrB : Term 0
VrB = Wr₀ ⟨ cInj ⟩

-- the goal fails at stage 3

data Got {Δ} {M : Term Δ} : Maybe (EvalOutcome M) → Set where
  got : (r : EvalResult M) → Got (just (returned r))

resOf : ∀ {Δ} {M : Term Δ} {o : Maybe (EvalOutcome M)} → Got o
  → EvalResult M
resOf (got r) = r

-- a run, counted
count : ∀ {Δ Δ′} {M : Term Δ} {χs : StoreChanges Δ Δ′} {N : Term Δ′}
  → M —↠[ χs ] N → Σ[ k ∈ ℕ ] (M —→^ k [ χs ] N)
count ↠-refl = _ , none
count (↠-step s ss) with count ss
count (↠-step s ss) | k , r = sucℕ k , more s r

-- a term that reaches a value does not reach blame
val-vs-blame : ∀ {Δ Δ₁ Δ₂ j} {M : Term Δ} {χs₁ : StoreChanges Δ Δ₁}
    {V : Term Δ₁} {χs₂ : StoreChanges Δ Δ₂}
  → M —→^ j [ χs₁ ] V → Value V → M —↠[ χs₂ ] blame → ⊥
val-vs-blame none () ↠-refl
val-vs-blame none v (↠-step s _) = value-no-step v s
val-vs-blame (more s ss) v ↠-refl = blame-no-step s
val-vs-blame (more s ss) v (↠-step s′ rest) with det s s′
val-vs-blame (more s ss) v (↠-step s′ rest) | refl = val-vs-blame ss v rest

no21 : ¬ (2 ≤ 1)
no21 (s≤s ())

no31 : ¬ (3 ≤ 1)
no31 (s≤s ())

-- the right's projection: one step to the function
runR1 : VrB ⟨ proj⇒ ⟩ —→^ 1 [ keep ∷ [] ] Wr₀
runR1 = more (pure-step (tag-untag (ƛ _))) none

-- the left's cast, run to its value W′
resL : EvalResult (idΛ ⟨ clA ⟩)
resL = resOf {o = eval 20 (idΛ ⟨ clA ⟩)} (got _)

W′ : Term 2
W′ = term resL

runL : idΛ ⟨ clA ⟩ —→^ _ [ changes resL ] W′
runL = proj₂ (count (trace resL))

-- the arguments: `5` injected at `ℕ`
a₅ : Term 2
a₅ = nℕ 5

b₅ : Term 0
b₅ = nℕ 5

-- the left's application, run to its value
resA : EvalResult (renameᵗᵐ id↪ᵗ W′ · a₅)
resA = resOf {o = evalFrom (applyStores (changes resL) store-empty) 30
  (renameᵗᵐ id↪ᵗ W′ · a₅)} (got _)

runA : renameᵗᵐ id↪ᵗ W′ · a₅ —→^ _ [ changes resA ] term resA
runA = proj₂ (count (trace resA))

-- the right's application: one step to `0`
runB : renameᵗᵐ id↪ᵗ Wr₀ · b₅ —→^ 1 [ keep ∷ [] ] nℕ 0
runB = more (pure-step (β ($ _ 《 inj 》))) none

-- a world with the same tags, renamed, and its extension
module _ {Δ′} (p′ : Prefix 0 Δ′) (tags : TyVar 2 → Tag 2 Δ′)
    (Σ″ : TyStore 0) where

  w″ w‴ : World
  w″ = mkWorld 2 Δ′ tags 0 p′ Σ″
  w‴ = mkWorld 2 Δ′ (λ Y → renameTag id↪ᵗ id↪ᵗ (tags Y)) 0 p′ Σ″

  e‴ : w‴ ⊒ w″
  e‴ = LR.World.ext id↪ᵗ id↪ᵗ id↪ᵗ (coh-id p′) Grows-id
    (λ X → cong (λ Y → renameTag id↪ᵗ id↪ᵗ (tags Y)) (toRename-id-eq X))
    StoreRen-id

  -- at stage 2, the functions are not related at `★→★ ⊑ ★→★`
  refute2 : ∀ {δ} → funRel ≻ 2 (★⊑★ {Φ = []}) ★⊑★ w″ δ W′ Wr₀ → ⊥
  refute2 f with f e‴ ≤′-refl a₅ b₅ ($ _ 《 inj 》) ($ _ 《 inj 》)
      (refl , refl) (typedᴿ ★ refl (⊢⟨⟩ (⊢$ (κℕ 5)) injℕ))
  refute2 f | inj₁ (_ , _ , _ , r2) =
    no21 (value-run-stops runB ($ _ 《 inj 》) r2)
  refute2 f | inj₂ (inj₁ (_ , _ , bl)) = val-vs-blame runA (value resA) bl
  refute2 f | inj₂ (inj₂ (k , n₂ , le₂ , _ , _ , _ , _ , _ , _ ,
      eq₂ , sl₂ , sr₂ , vl₂ , vr₂ , arr₂))
      with det-value-run runB ($ _ 《 inj 》) sr₂ vr₂
  refute2 f | inj₂ (inj₂ (k , n₂ , le₂ , _ , _ , _ , _ , _ , _ ,
      eq₂ , sl₂ , sr₂ , vl₂ , vr₂ , arr₂)) | refl , refl
      with det-value-↠ runA (value resA) sl₂ vl₂
  refute2 f | inj₂ (inj₂ (k , n₂ , ≤′-step ≤′-refl , _ , _ , _ , _ , _ , _ ,
      refl , sl₂ , sr₂ , vl₂ , vr₂ , (_ , _ , _ , _ , _ , _ , (_ , ()))))
      | refl , refl | refl
  refute2 f | inj₂ (inj₂ (k , n₂ , ≤′-step (≤′-step (≤′-reflexive ())) ,
      _ , _ , _ , _ , _ , _ , refl , sl₂ , sr₂ , vl₂ , vr₂ , arr₂))
      | refl , refl | refl

goalB : ¬ ℰ ≻ 3 rAG w₀ closedI (idΛ ⟨ clA ⟩) (VrB ⟨ proj⇒ ⟩)
goalB (inj₁ (_ , _ , _ , r3)) = no31 (value-run-stops runR1 (ƛ _) r3)
goalB (inj₂ (inj₁ (_ , _ , bl))) = val-vs-blame runL (value resL) bl
goalB (inj₂ (inj₂ (k , n′ , le , _ , _ , _ , _ , _ , _ ,
    eq , sl , sr , vl , vr , arr)))
    with det-value-run runR1 (ƛ _) sr vr
goalB (inj₂ (inj₂ (k , n′ , le , _ , _ , _ , _ , _ , _ ,
    eq , sl , sr , vl , vr , arr))) | refl , refl
    with det-value-↠ runL (value resL) sl vl
goalB (inj₂ (inj₂ (k , n′ , ≤′-step ≤′-refl , _ , _ , _ , _ , _ , _ ,
    refl , sl , sr , vl , vr , (_ , p′ , _ , _ , tags , _ , f))))
    | refl , refl | refl = refute2 p′ tags _ f
goalB (inj₂ (inj₂ (k , n′ , ≤′-step (≤′-step (≤′-reflexive ())) ,
    _ , _ , _ , _ , _ , _ , refl , sl , sr , vl , vr , arr)))
    | refl , refl | refl
goalB (inj₂ (inj₂ (k , n′ ,
    ≤′-step (≤′-step (≤′-step (≤′-reflexive ()))) ,
    _ , _ , _ , _ , _ , _ , refl , sl , sr , vl , vr , arr)))
    | refl , refl | refl
