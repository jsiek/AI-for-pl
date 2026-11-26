module proof.LR.Case7Probe where

-- File Charter:
--   * A probe of the cast lemma's case 7 (left `∀ᶜ`, right `gen`, from
--     `∀⊑` to `∀⊑∀`; notes/logrel-dgg.md, Section 7, "Case 7 probe").
--   * The example: left `∀ᶜ (id X ↦ id X) : ∀X.X→X ∼ ∀X.X→X`, right
--     `gen ((Y!) ↦ (？Y)) : ★→★ ∼ ∀Y.Y→Y`, both eager, at
--     `∀X.X→X ⊑ ★→★` (X left-only) to `∀X.X→X ⊑ ∀Y.Y→Y` (X paired).
--     Values `Λ ƛ x` and `ƛ y`.  Run at `[ℕ] · 3`, both return 3; the
--     right's `gen` allocates α′ := ℕ and passes `($3 ↓ seal α′ ℕ) ⟨α′!⟩`
--     to `ƛ y` (`rightArg`), while the left's function receives
--     `$3 ↓ seal β ℕ` from its own `Λ` (`leftArg`).
--   * Obstruction 1 (`no-body-source`): the induction hypothesis for
--     the body casts asks for one correspondence for the body's source
--     (`X→X ⊑ ★→★`, X left-only) and target (`X→X ⊑ Y→Y`, X paired);
--     none exists, so `CastCase` at the body casts is vacuous.
--   * Obstruction 2, Gap D2 (`noLeaf`, `noExample`): in `≺`, at every
--     positive stage, no leaf of the left-only clause relates a
--     constant to a right value injected at a store variable.  So the
--     hypothesis's clause never applies to the example's argument pair
--     `($3 , ($3 ↓ seal α′ ℕ) ⟨α′!⟩)`.
--   * The proposed change, on the example: two correspondences
--     `Φs ≼ Φt` (`≼gen` for a variable that the right's `gen` binds),
--     the cast lemma stated over them (`≼-refl` gives the current
--     statement), and a right tag wrapper `tagΩ` for the source leaf,
--     which relates the example's pair (`leafS-ex`).

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; _≤′_; ≤′-refl; ≤′-step; _≤?_)
  renaming (zero to zeroℕ; suc to sucℕ)
open import Data.Nat.Properties using (≤⇒≤′)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; lookup) renaming ([] to []ᵛ)
import Data.Vec as Vec
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore using (TyStore; store-empty)
open import Consistency
open import Conversion
open import CastTerms
open import Primitives using (κℕ)
open import Reduction using (applyStore; bind)
open import Eval using (step?; step-result; eval; EvalOutcome; outcomeCtx;
  finalTerm)
open import LR.Precision
open import LR.EagerCast
open import LR.Desc
open import LR.World
open import LR.Steps using (more; none)
open import LR.Relation
open import proof.LR.WorldProps using (⊒-refl)
open import proof.LR.Case6Probe using (app-stuck)

------------------------------------------------------------------------
-- The example
------------------------------------------------------------------------

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

-- `X → X`, the body of both `∀` types (X bound, index 0)
XX : Ty 1
XX = ＇ zero ⇒ ＇ zero

cl : []ᵛ ⊢ `∀ XX ∼ `∀ XX
cl = ∀ᶜ (id (＇ zero) ↦ id (＇ zero))

-- the right body cast, at mode `★∼X` for the bound variable: the
-- argument is tagged `Y!`, the result projected `？Y`
dom : flipᵐ (genᵐ []ᵛ) ⊢ ＇ zero ∼ ★
dom = _! ⦃ ＇ zero ⦄ ⦃ X∼★ᵍ refl ⦄ (id (＇ zero)) ⦃ nonstar-X ⦄

cod : genᵐ []ᵛ ⊢ ★ ∼ ＇ zero
cod = ？_ ⦃ ＇ zero ⦄ ⦃ ★∼Xᵍ refl ⦄ (id (＇ zero)) ⦃ nonstar-X ⦄

body′ : genᵐ []ᵛ ⊢ ★ ⇒ ★ ∼ XX
body′ = dom ↦ cod

cr : []ᵛ ⊢ ★ ⇒ ★ ∼ `∀ XX
cr = (gen_ ⦃ nonvar-fun ⦄ ⦃ ∈-fun-left var-∈ ⦄ body′) (λ ())

cl-eager : Eager cl
cl-eager = e-∀ (e-↦ e-id e-id)

cr-eager : Eager cr
cr-eager = e-gen ⦃ nonvar-fun ⦄ ⦃ ∈-fun-left var-∈ ⦄
  (e-↦ (e-! e-id) (e-？ e-id)) tt

Vl Vr : Term 0
Vl = Λ (ƛ (` 0))
Vr = ƛ (` 0)

leftP rightP : Term 0
leftP = ((Vl ⟨ cl ⟩) ⦂∀ XX [ ℕᵗ ]) · $ (κℕ 3)
rightP = ((Vr ⟨ cr ⟩) ⦂∀ XX [ ℕᵗ ]) · $ (κℕ 3)

-- k steps of the executable reduction
stepN : ∀ {Δ} → TyStore Δ → ℕ → Term Δ → Maybe (Σ[ Δ′ ∈ TyCtx ] Term Δ′)
stepN S zeroℕ M = just (_ , M)
stepN S (sucℕ k) M with step? S M
stepN S (sucℕ k) M | nothing = nothing
stepN S (sucℕ k) M | just (step-result χ N _) = stepN (applyStore χ S) k N

right3 : stepN store-empty 3 rightP
  ≡ just (1 , (((ƛ (` 0)) · (($ (κℕ 3) ↓ seal zero ℕᵗ) ⟨ dom ⟩)) ⟨ cod ⟩
                ↑ unseal zero ℕᵗ))
right3 = refl

-- the argument of the innermost `ƛ` application under casts and
-- conversions
argOf : ∀ {Δ} → Term Δ → Maybe (Term Δ)
argOf (M ⟨ c ⟩) = argOf M
argOf (M ↑ c) = argOf M
argOf ((ƛ N) · W) = just W
argOf M = nothing

argAfter : ℕ → Term 0 → Maybe (Σ[ Δ′ ∈ TyCtx ] Term Δ′)
argAfter k M with stepN store-empty k M
argAfter k M | just (Δ′ , N) with argOf N
argAfter k M | just (Δ′ , N) | just W = just (Δ′ , W)
argAfter k M | just (Δ′ , N) | nothing = nothing
argAfter k M | nothing = nothing

leftArg : argAfter 5 leftP ≡ just (1 , ($ (κℕ 3) ↓ seal zero ℕᵗ))
leftArg = refl

rightArg : argAfter 3 rightP ≡ just (1 , (($ (κℕ 3) ↓ seal zero ℕᵗ) ⟨ dom ⟩))
rightArg = refl

final : ∀ {M : Term 0} → Maybe (EvalOutcome M)
  → Maybe (Σ[ Δ′ ∈ TyCtx ] Term Δ′)
final (just r) = just (outcomeCtx r , finalTerm r)
final nothing = nothing

leftRuns : final (eval 20 leftP) ≡ just (1 , $ (κℕ 3))
leftRuns = refl

rightRuns : final (eval 20 rightP) ≡ just (1 , $ (κℕ 3))
rightRuns = refl

------------------------------------------------------------------------
-- The precisions, and the body's induction hypothesis
------------------------------------------------------------------------

-- the casts' sources: `∀X.X→X ⊑ ★→★`, X left-only
p : [] ⊢ `∀ XX ⊑ ★ ⇒ ★
p = ∀⊑ nonvar-fun (∈-fun-left var-∈) p₁
  where
  p₁ : only [] ⊢ XX ⊑ ★ ⇒ ★
  p₁ = ⇒⊑⇒ (X⊑★ only-here) (X⊑★ only-here)

-- the casts' targets: `∀X.X→X ⊑ ∀Y.Y→Y`, X paired with Y
r : [] ⊢ `∀ XX ⊑ `∀ XX
r = ∀⊑∀ r₁
  where
  r₁ : pair [] ⊢ XX ⊑ XX
  r₁ = ⇒⊑⇒ (X⊑Y ↔-here) (X⊑Y ↔-here)

-- The body casts are `id ↦ id : X→X ∼ X→X` (left, X bound by the left's
-- `∀`) and `body′ : ★→★ ∼ Y→Y` (right, Y bound by `gen`).  An
-- induction hypothesis `CastCase (id ↦ id) body′` asks for one
-- correspondence Ψ : Corr 1 1 with both `Ψ ⊢ X→X ⊑ ★→★` and
-- `Ψ ⊢ X→X ⊑ Y→Y`.  The first needs X left-only, the second X paired:
-- no Ψ derives the source, so the hypothesis is vacuous.
no-body-source : ∀ (Ψ : Corr 1 1) → Ψ ⊢ XX ⊑ ★ ⇒ ★ → ⊥
no-body-source (pair []) (⇒⊑⇒ (X⊑★ ()) q)
no-body-source (only ())
no-body-source (dead ())

------------------------------------------------------------------------
-- Gap D2: no left-only clause reads the pair the right's run creates
------------------------------------------------------------------------

-- a right cast that injects at a store variable
data VarInj {Θ} {μ : Env∼ Θ} {A : Ty Θ} : μ ⊢ A ∼ ★ → Set where
  varInj : ∀ {Y} ⦃ g : μ ⊢ ＇ Y ∼★ ⦄ {c : μ ⊢ A ∼ ＇ Y}
      ⦃ Ans : NonStar A ⦄
    → VarInj (_! ⦃ ＇ Y ⦄ ⦃ g ⦄ c ⦃ Ans ⦄)

-- an instantiation of a constant takes no step and is not a value
stuck≺ : ∀ {n} (w : World) {VR : VRel (sucℕ n) w} {κ}
    {B : Ty (sucℕ (ΔL w))} {T : Ty (ΔL w)} {Mr}
  → ℰᵍ ≺ (sucℕ n) w VR ($ κ ⦂∀ B [ T ]) Mr → ⊥
stuck≺ w (inj₁ (_ , _ , _ , more s _)) = app-stuck s
stuck≺ w (inj₂ (inj₁ (zeroℕ , _ , _ , _ , ())))
stuck≺ w (inj₂ (inj₁ (sucℕ k , _ , _ , _ , more s _))) = app-stuck s
stuck≺ w (inj₂ (inj₂ (zeroℕ , _ , _ , _ , _ , _ , _ , _ , _ ,
    _ , none , _ , () , _ , _)))
stuck≺ w (inj₂ (inj₂ (sucℕ k , _ , _ , _ , _ , _ , _ , _ , _ ,
    _ , more s _ , _ , _ , _ , _))) = app-stuck s

entry-$ : ∀ d n w (e : Entry (ΔL w) (ΔR w)) {κ} {V : Term (storeR w)}
  → entry d n w e ($ κ) V → ⊥
entry-$ d n w (seals X Xs Ys c) ()

-- a left-only descriptor at every world
starD : ∀ {ΘL ΘR} → SDesc ΘL ΘR
starD = sdesc [] [] (desc (★⊑★ {Φ = []}) []ᵛ []ᵛ)

starD-ok : ∀ {ΘL ΘR} → OnlyS (starD {ΘL} {ΘR})
starD-ok = (λ ()) , refl

-- at a positive stage in `≺`, no derivation into `★` relates a constant
-- to a right injection at a store variable
noCore : ∀ m {Δ Δ′} {Φ : Corr Δ Δ′} {A} (q : Φ ⊢ A ⊑ ★) (w : World)
    (env : Vec (Entry (ΔL w) (ΔR w)) Δ) (envR : Vec (Ty (ΔR w)) Δ′)
    {κ} {W : Term (storeR w)} {μ} {A₀} {c : μ ⊢ A₀ ∼ ★}
  → VarInj c → 𝒱 ≺ (sucℕ m) q w (envI env envR) ($ κ) (W ⟨ c ⟩) → ⊥
noCore m ★⊑★ w env envR varInj ()
noCore m ι⊑★ w env envR varInj (() , _)
noCore m (X⊑★ {X = X} x) w env envR varInj h =
  entry-$ ≺ (sucℕ m) w (lookup env X) h
noCore m (⇒⊑★ q₁ q₂) w env envR varInj (() , _)
noCore m (∀⊑ Anv z q₁) w env envR varInj (i , h) =
  stuck≺ w {VR = λ {n₀} le′ w″ e′ → 𝒱≤ ≺ (≤′-trans le′ rf) q₁ w″
      (extOnlyI (leftTyS sD) (sem (onlyLeafS ≺ rf sD))
        (envI env envR ↑ᴵ ⊒-refl w) ↑ᴵ e′)}
    (h (⊒-refl w) rf sD starD-ok)
  where
  rf : sucℕ m ≤′ sucℕ m
  rf = ≤′-refl
  sD : SDesc (ΔL w) (ΔR w)
  sD = starD
noCore m ∀★⊑★ w env envR varInj (() , _)
noCore m (∀⊑★ ns q₁) w env envR varInj (() , _)
noCore m bot⊑★ w env envR varInj ()

𝒱<-at : ∀ d {m n} (lt : sucℕ m ≤′ n) {Δ Δ′} {Φ : Corr Δ Δ′} {A A′}
    (q : Φ ⊢ A ⊑ A′) w δ {V V′}
  → 𝒱< d lt q w δ V V′ → 𝒱 d m q w δ V V′
𝒱<-at d ≤′-refl q w δ h = h
𝒱<-at d (≤′-step lt) q w δ h = 𝒱<-at d lt q w δ h

noBelow : ∀ {n′ N} (le : n′ ≤′ N) {ΘL ΘR} (c : Desc ΘL ΘR) → CoreStar c
  → ∀ m w (τL : ΘL ↪ᵗ ΔL w) (τR : ΘR ↪ᵗ ΔR w)
    {κ} {W : Term (storeR w)} {μ} {A₀} {c′ : μ ⊢ A₀ ∼ ★}
  → VarInj c′ → leafBelow ≺ le c (sucℕ m) w τL τR ($ κ) (W ⟨ c′ ⟩) → ⊥
noBelow {n′} le (desc q env envR) refl m w τL τR vi h
    with sucℕ (sucℕ m) ≤? n′
noBelow {n′} le (desc q env envR) refl m w τL τR vi h | yes lt =
  noCore m q w (renameEntries τL τR env)
    (Vec.map (renameᵗ (toRenameᵗ τR)) envR) vi
    (𝒱<-at ≺ (≤′-trans (≤⇒≤′ lt) le) q w _ h)
noBelow {n′} le (desc q env envR) refl m w τL τR vi () | no _

-- Gap D2, checked: at a positive stage in `≺`, no leaf of the
-- left-only clause relates a constant to a right value injected at a
-- store variable
noLeaf : ∀ {n′ N} (le : n′ ≤′ N) {ΘL ΘR} (c : SDesc ΘL ΘR) → OnlyS c
  → ∀ m w (τL : ΘL ↪ᵗ ΔL w) (τR : ΘR ↪ᵗ ΔR w)
    {κ} {W : Term (storeR w)} {μ} {A₀} {c′ : μ ⊢ A₀ ∼ ★}
  → VarInj c′ → onlyLeafS ≺ le c (sucℕ m) w τL τR ($ κ) (W ⟨ c′ ⟩) → ⊥
noLeaf le (sdesc [] Ys c) (wf , cs) m w τL τR vi h =
  noBelow le c cs m w τL τR vi h
noLeaf le (sdesc (X ∷ Xs) Ys c) ok m w τL τR vi ()

-- the example's pair is of that form: the right's argument
-- `($3 ↓ seal α′ ℕ) ⟨ α′! ⟩` (`rightArg`) is an injection at α′
dom-inj : VarInj dom
dom-inj = varInj

------------------------------------------------------------------------
-- The proposed change, on the example
------------------------------------------------------------------------

-- (1) Two correspondences: the source's, where the variables that the
-- right's `gen`s bind are left-only, and the target's, where they are
-- paired.  `Φs ≼ Φt`, with the embedding of the source's right context
-- into the target's.
data _≼_ : ∀ {Δ Δs Δt} → Corr Δ Δs → Corr Δ Δt → Set where
  ≼[] : [] ≼ []
  ≼pair : ∀ {Δ Δs Δt} {Φs : Corr Δ Δs} {Φt : Corr Δ Δt}
    → Φs ≼ Φt → pair Φs ≼ pair Φt
  ≼only : ∀ {Δ Δs Δt} {Φs : Corr Δ Δs} {Φt : Corr Δ Δt}
    → Φs ≼ Φt → only Φs ≼ only Φt
  ≼dead : ∀ {Δ Δs Δt} {Φs : Corr Δ Δs} {Φt : Corr Δ Δt}
    → Φs ≼ Φt → dead Φs ≼ dead Φt
  -- X bound by the left's `∀ᶜ`, Y by the right's `gen`
  ≼gen : ∀ {Δ Δs Δt} {Φs : Corr Δ Δs} {Φt : Corr Δ Δt}
    → Φs ≼ Φt → only Φs ≼ pair Φt

ρ≼ : ∀ {Δ Δs Δt} {Φs : Corr Δ Δs} {Φt : Corr Δ Δt}
  → Φs ≼ Φt → Δs ↪ᵗ Δt
ρ≼ ≼[] = empty
ρ≼ (≼pair g) = keep (ρ≼ g)
ρ≼ (≼only g) = ρ≼ g
ρ≼ (≼dead g) = ρ≼ g
ρ≼ (≼gen g) = skip (ρ≼ g)

-- the current statement is the case Φs = Φt
≼-refl : ∀ {Δ Δ′} (Φ : Corr Δ Δ′) → Φ ≼ Φ
≼-refl [] = ≼[]
≼-refl (pair Φ) = ≼pair (≼-refl Φ)
≼-refl (only Φ) = ≼only (≼-refl Φ)
≼-refl (dead Φ) = ≼dead (≼-refl Φ)

-- the example's body: the source at `only []`, the target at `pair []`,
-- and the right cast's source `★→★` (in the target's context) is the
-- source derivation's right type moved along ρ≼
bodyG : only [] ≼ pair []
bodyG = ≼gen ≼[]

bodyP : only [] ⊢ XX ⊑ ★ ⇒ ★
bodyP = ⇒⊑⇒ (X⊑★ only-here) (X⊑★ only-here)

bodyR : pair [] ⊢ XX ⊑ XX
bodyR = ⇒⊑⇒ (X⊑Y ↔-here) (X⊑Y ↔-here)

bodySrc : ⇑ᵗ (★ ⇒ ★) ≡ renameᵗ (toRenameᵗ (ρ≼ bodyG)) (★ ⇒ ★ {0})
bodySrc = refl

-- (2) The source interpretation's leaf at a gen-bound variable is the
-- target's leaf under a right tag at the variable's store variable
-- (Gap D2's wrapper, as a relation).
tagΩ : ∀ {ΘL ΘR} → TyVar ΘR → RelΩ ΘL ΘR → RelΩ ΘL ΘR
tagΩ Y R k w τL τR V (W ⟨ c ⟩) =
  IsInjVarᴿ (ιʷ w) (renameVar τR Y) c × R k w τL τR V W
tagΩ Y R k w τL τR V V′ = ⊥

-- the example after the right's allocation: right store [α′ := ℕ]
w₁ : World
w₁ = mkWorld 0 1 (λ ()) 1 pid (applyStore (bind ℕᵗ) store-empty)

-- the goal's descriptor: constants at ℕ, no seals
ιD : Desc 0 1
ιD = desc (ι⊑ι {Φ = []} {ι = `ℕ}) []ᵛ []ᵛ

-- the target's leaf for X (paired with α′): sealed by α′ on the right
leafT : ∀ {n′ N} → n′ ≤′ N → RelΩ 0 1
leafT le = leafBelowS ≺ le (sdesc [] (zero ∷ []) ιD)

𝒱<-in : ∀ d {m n} (lt : sucℕ m ≤′ n) {Δ Δ′} {Φ : Corr Δ Δ′} {A A′}
    (q : Φ ⊢ A ⊑ A′) w δ {V V′}
  → 𝒱 d m q w δ V V′ → 𝒱< d lt q w δ V V′
𝒱<-in d ≤′-refl q w δ h = h
𝒱<-in d (≤′-step lt) q w δ h = 𝒱<-in d lt q w δ h

-- the source's leaf relates the example's argument pair, at every
-- stage below the clause's
leafS-ex : ∀ {n′ N} (le : n′ ≤′ N) m → sucℕ m ≤ n′
  → tagΩ zero (leafT le) m w₁ empty id↪ᵗ
      ($ (κℕ 3)) (($ (κℕ 3) ↓ seal zero ℕᵗ) ⟨ dom ⟩)
leafS-ex {n′} le m lt with sucℕ m ≤? n′
leafS-ex {n′} le m lt | yes lt′ =
  refl , (refl , refl) ,
    𝒱<-in ≺ (≤′-trans (≤⇒≤′ lt′) le) ι⊑ι w₁ _ (κℕ 3 , refl , refl)
leafS-ex {n′} le m lt | no ¬lt = ⊥-elim (¬lt lt)

-- while the hypothesis's clause, at any descriptor, does not relate
-- that pair at any positive stage
noExample : ∀ {n′ N} (le : n′ ≤′ N) (c : SDesc 0 1) → OnlyS c → ∀ m
  → onlyLeafS ≺ le c (sucℕ m) w₁ empty id↪ᵗ
      ($ (κℕ 3)) (($ (κℕ 3) ↓ seal zero ℕᵗ) ⟨ dom ⟩)
  → ⊥
noExample le c ok m = noLeaf le c ok m w₁ empty id↪ᵗ dom-inj
