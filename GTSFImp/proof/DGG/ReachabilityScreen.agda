module proof.DGG.ReachabilityScreen where

-- File Charter:
--   * Provides a fast evaluator-backed reachability screen for closed
--     version-2 DGG example pairs.
--   * Extracts allocation order, store-reference edges, and variable-tag
--     cast boundaries from Eval traces without per-step imprecision proofs.
--   * Calibrates the screen on the three Examples2 pairs plus one closed
--     adversarial allocation-chain program.

open import Data.Bool using (Bool; false; true; _∧_; _∨_)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore using (store-empty)
open import Consistency using
  (Env∼; X∼★; _⊢_∼_; idᶜ; instᵐ; id; _!; _↦_; ∀ᶜ_;
   ？_; inst_; gen_; bot-elim; bot-intro)
open import CastTerms
open import Reduction
open import Eval
open import Imprecision using
  (X⊑X; X⊑★; ★⊑★; ⇒⊑⇒; ∀⊑; ∀⊑∀)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.Examples2 as Ex2

open CTI2 using (_⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Closed program entries
------------------------------------------------------------------------

record Entry : Set where
  constructor entry
  field
    more-precise : Term 0
    more-imprecise : Term 0
    gasᴸ : ℕ
    gasᴿ : ℕ
    typeᴸ : Ty 0
    typeᴿ : Ty 0
    type⊑ : typeᴸ ⊑ᵂ⟨ Ex2.reflWorld store-empty ⟩ typeᴿ
    initial⊑ :
      Ex2.reflWorld store-empty ∣ [] ⊢² more-precise
        ⊑ more-imprecise ∶ type⊑

open Entry

------------------------------------------------------------------------
-- Small list and order helpers
------------------------------------------------------------------------

memberℕ : ℕ → List ℕ → Bool
memberℕ n [] = false
memberℕ n (m ∷ ms) with n Nat.≟ m
memberℕ n (m ∷ ms) | yes refl = true
memberℕ n (m ∷ ms) | no n≢m = memberℕ n ms

_<ᵇ_ : ℕ → ℕ → Bool
m <ᵇ n with m Nat.<? n
m <ᵇ n | yes m<n = true
m <ᵇ n | no m≮n = false

anyBool : ∀ {A : Set} → (A → Bool) → List A → Bool
anyBool p [] = false
anyBool p (x ∷ xs) = p x ∨ anyBool p xs

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

varOrder : ∀ {Δ} → Fin Δ → ℕ
varOrder {zero} ()
varOrder {suc Δ} Fin.zero = Δ
varOrder {suc Δ} (Fin.suc X) = varOrder X

oldVarOrders : ∀ {Δ} → (Fin Δ → Maybe ℕ) → Ty Δ → List ℕ
oldVarOrders ρ (＇ X) with ρ X
oldVarOrders ρ (＇ X) | just n = n ∷ []
oldVarOrders ρ (＇ X) | nothing = []
oldVarOrders ρ (‵ ι) = []
oldVarOrders ρ ★ = []
oldVarOrders ρ (A ⇒ B) = oldVarOrders ρ A ++ oldVarOrders ρ B
oldVarOrders {Δ = Δ} ρ (`∀ A) =
  oldVarOrders extend A
  where
  extend : Fin (suc Δ) → Maybe ℕ
  extend Fin.zero = nothing
  extend (Fin.suc X) = ρ X

tyVarOrders : ∀ {Δ} → Ty Δ → List ℕ
tyVarOrders A = oldVarOrders (λ X → just (varOrder X)) A

------------------------------------------------------------------------
-- Extracted trace facts
------------------------------------------------------------------------

data StoreEntryShape : Set where
  entry-var : StoreEntryShape
  entry-base : StoreEntryShape
  entry-star : StoreEntryShape
  entry-fun : StoreEntryShape
  entry-all : StoreEntryShape

storeEntryShape : ∀ {Δ} → Ty Δ → StoreEntryShape
storeEntryShape (＇ X) = entry-var
storeEntryShape (‵ ι) = entry-base
storeEntryShape ★ = entry-star
storeEntryShape (A ⇒ B) = entry-fun
storeEntryShape (`∀ A) = entry-all

record AllocEvent : Set where
  constructor alloc
  field
    step : ℕ
    order : ℕ
    shape : StoreEntryShape
    refs : List ℕ

open AllocEvent

record ChainEdge : Set where
  constructor edge
  field
    from : ℕ
    to : ℕ

open ChainEdge

allocEventsFrom : ∀ {Δ Δ′}
  → ℕ
  → ℕ
  → StoreChanges Δ Δ′
  → List AllocEvent
allocEventsFrom stepᵢ next [] = []
allocEventsFrom stepᵢ next (keep ∷ χs) =
  allocEventsFrom (suc stepᵢ) next χs
allocEventsFrom stepᵢ next (bind A ∷ χs) =
  alloc stepᵢ next (storeEntryShape A) (tyVarOrders A) ∷
  allocEventsFrom (suc stepᵢ) (suc next) χs

allocEvents : ∀ {Δ Δ′} → StoreChanges Δ Δ′ → List AllocEvent
allocEvents = allocEventsFrom 0 0

edgesForAlloc : AllocEvent → List ChainEdge
edgesForAlloc ev = mapList (edge (order ev)) (refs ev)

chainEdges : List AllocEvent → List ChainEdge
chainEdges [] = []
chainEdges (ev ∷ evs) = edgesForAlloc ev ++ chainEdges evs

tagOrders : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → μ ⊢ A ∼ B
  → List ℕ
tagOrders (id a) = []
tagOrders (c ↦ d) = []
tagOrders (∀ᶜ c) = []
tagOrders (_! {G = ＇ X} c) = varOrder X ∷ []
tagOrders (_! {G = ‵ ι} c) = []
tagOrders (_! {G = ★ ⇒ ★} c) = []
tagOrders (_! {G = `∀ ★} c) = []
tagOrders (？ c) = []
tagOrders ((inst c) A≢★) = []
tagOrders ((gen c) A≢★) = []
tagOrders bot-elim = []
tagOrders bot-intro = []

termTagOrders : ∀ {Δ} → Term Δ → List ℕ
termTagOrders (` x) = []
termTagOrders (ƛ M) = termTagOrders M
termTagOrders (L · M) = termTagOrders L ++ termTagOrders M
termTagOrders (Λ M) = termTagOrders M
termTagOrders (L ⦂∀ B [ A ]) = termTagOrders L
termTagOrders ($ κ) = []
termTagOrders (L ⊕[ op ] M) = termTagOrders L ++ termTagOrders M
termTagOrders (M ⟨ c ⟩) = termTagOrders M ++ tagOrders c
termTagOrders (M ↑ c) = termTagOrders M
termTagOrders (M ↓ c) = termTagOrders M
termTagOrders blame = []

traceTagOrdersFrom : ∀ {Δ Δ′} {M : Term Δ}
    {χs : StoreChanges Δ Δ′} {N : Term Δ′}
  → M —↠[ χs ] N
  → List ℕ
traceTagOrdersFrom {M = M} ↠-refl = termTagOrders M
traceTagOrdersFrom {M = M} (↠-step M→N N↠P) =
  termTagOrders M ++ traceTagOrdersFrom N↠P

data RunStatus : Set where
  returned-value : RunStatus
  returned-blame : RunStatus
  stopped : RunStatus

record SideSummary : Set where
  constructor side
  field
    status : RunStatus
    allocations : List AllocEvent
    edges : List ChainEdge
    tags : List ℕ

open SideSummary

summaryFromOutcome : ∀ {Δ} {M : Term Δ}
  → EvalOutcome M
  → SideSummary
summaryFromOutcome (returned r) =
  side returned-value (allocEvents (changes r))
    (chainEdges (allocEvents (changes r))) (traceTagOrdersFrom (trace r))
summaryFromOutcome (blamed χs M↠blame) =
  side returned-blame (allocEvents χs)
    (chainEdges (allocEvents χs)) (traceTagOrdersFrom M↠blame)

runSummary : ℕ → Term 0 → SideSummary
runSummary gas M with eval gas M
runSummary gas M | just out = summaryFromOutcome out
runSummary gas M | nothing = side stopped [] [] []

------------------------------------------------------------------------
-- The version-0 crossing screen
------------------------------------------------------------------------

edgeTouchesTag : ChainEdge → List ℕ → Bool
edgeTouchesTag e tags =
  (to e <ᵇ from e) ∧
  (memberℕ (from e) tags ∨ memberℕ (to e) tags)

sideHasSuspectEdge : SideSummary → Bool
sideHasSuspectEdge s = anyBool touches (edges s)
  where
  touches : ChainEdge → Bool
  touches e = edgeTouchesTag e (tags s)

data ScreenResult : Set where
  clean : ScreenResult
  suspect : ScreenResult

screenPair : SideSummary → SideSummary → ScreenResult
screenPair left right with sideHasSuspectEdge left ∨ sideHasSuspectEdge right
screenPair left right | false = clean
screenPair left right | true = suspect

crossing-suspect : Entry → ScreenResult
crossing-suspect e =
  screenPair (runSummary (gasᴸ e) (more-precise e))
    (runSummary (gasᴿ e) (more-imprecise e))

------------------------------------------------------------------------
-- A closed adversarial allocation-chain program
------------------------------------------------------------------------

tag-env : Env∼ 1
tag-env Fin.zero = X∼★

tag-var! : tag-env ⊢ ＇ Fin.zero ∼ ★
tag-var! = id (＇ Fin.zero) !

tag-body : Term 1
tag-body = ƛ ((` 0) ⟨ tag-var! ⟩)

tag-poly : Term 0
tag-poly = Λ tag-body

tag-inst-var! : instᵐ (idᶜ {Δ = 0}) ⊢ ＇ Fin.zero ∼ ★
tag-inst-var! = id (＇ Fin.zero) !

tag-inst-body :
  instᵐ (idᶜ {Δ = 0}) ⊢
    (＇ Fin.zero ⇒ ★) ∼ (★ ⇒ ★)
tag-inst-body = tag-inst-var! ↦ id ★

tag-inst-cast : idᶜ {Δ = 0} ⊢ `∀ (＇ Fin.zero ⇒ ★) ∼ (★ ⇒ ★)
tag-inst-cast =
  (inst_ ⦃ z∈A = ∈-fun-left var-∈ ⦄ tag-inst-body) (λ ())

tag-body-value : Value tag-body
tag-body-value = ƛ ((` 0) ⟨ tag-var! ⟩)

tag-var⊑ :
  ＇ Fin.zero ⊑ᵂ⟨
    CTI2.liftWorldBoth X⊑X (Ex2.reflWorld store-empty)
  ⟩ ＇ Fin.zero
tag-var⊑ = X⊑X

tag-lambda⊑ :
  CTI2.liftWorldBoth X⊑X (Ex2.reflWorld store-empty) ∣ []
    ⊢² tag-body ⊑ tag-body ∶ ⇒⊑⇒ tag-var⊑ ★⊑★
tag-lambda⊑ =
  CTI2.ƛ⊑ƛ²
    (CTI2.cast⊑cast² tag-var! tag-var!
      (CTI2.x⊑x² CTI2.Zʷ) ★⊑★)

tag-poly-type⊑ :
  `∀ (＇ Fin.zero ⇒ ★) ⊑ᵂ⟨ Ex2.reflWorld store-empty ⟩
    `∀ (＇ Fin.zero ⇒ ★)
tag-poly-type⊑ = ∀⊑∀ (⇒⊑⇒ X⊑X ★⊑★)

tag-poly⊑ :
  Ex2.reflWorld store-empty ∣ [] ⊢² tag-poly ⊑ tag-poly ∶
    tag-poly-type⊑
tag-poly⊑ =
  CTI2.Λ⊑Λ² CTI2.lift-[] tag-body-value tag-body-value
    tag-lambda⊑ tag-poly-type⊑

tag-chain-program : Term 0
tag-chain-program = tag-poly ⟨ tag-inst-cast ⟩

tag-direct-program : Term 0
tag-direct-program = tag-poly ⦂∀ (＇ Fin.zero ⇒ ★) [ ★ ]

tag-chain-type⊑ :
  (★ ⇒ ★) ⊑ᵂ⟨ Ex2.reflWorld store-empty ⟩ (★ ⇒ ★)
tag-chain-type⊑ = Ex2.★⇒★⊑★⇒★² {W = Ex2.reflWorld store-empty}

tag-poly-to-starfun⊑ :
  `∀ (＇ Fin.zero ⇒ ★) ⊑ᵂ⟨ Ex2.reflWorld store-empty ⟩
    (★ ⇒ ★)
tag-poly-to-starfun⊑ =
  ∀⊑ nonvar-fun (∈-fun-left var-∈) (⇒⊑⇒ (X⊑★ refl) ★⊑★)

tag-poly-to-cast⊑ :
  Ex2.reflWorld store-empty ∣ [] ⊢² tag-poly
    ⊑ tag-chain-program ∶ tag-poly-to-starfun⊑
tag-poly-to-cast⊑ =
  CTI2.⊑cast² tag-inst-cast tag-poly⊑ tag-poly-to-starfun⊑

tag-chain-initial⊑ :
  Ex2.reflWorld store-empty ∣ [] ⊢² tag-direct-program
    ⊑ tag-chain-program ∶ tag-chain-type⊑
tag-chain-initial⊑ =
  CTI2.•⊑² tag-poly-to-starfun⊑ tag-poly-to-cast⊑ ★⊑★
    tag-chain-type⊑

------------------------------------------------------------------------
-- Catalog
------------------------------------------------------------------------

example12-entry : Entry
example12-entry =
  entry Ex2.example12-more-precise Ex2.example12-more-imprecise
    30 30 (‵ `ℕ) (‵ `ℕ) Ex2.example12-ℕ⊑ℕ₀
    Ex2.example12-checkpoint₀

nat-chain-entry : Entry
nat-chain-entry =
  entry Ex2.nat-chain-more-precise Ex2.nat-chain-more-imprecise
    30 30 (‵ `ℕ) (‵ `ℕ) Ex2.nat-chain-ℕ⊑ℕ₀
    Ex2.nat-chain-checkpoint₀

left-path-entry : Entry
left-path-entry =
  entry Ex2.left-path-more-precise Ex2.left-path-more-imprecise
    30 30 (‵ `ℕ) ★ Ex2.left-path-ℕ⊑★₀
    Ex2.left-path-checkpoint₀

adversarial-entry : Entry
adversarial-entry =
  entry tag-direct-program tag-chain-program 10 10
    (★ ⇒ ★) (★ ⇒ ★) tag-chain-type⊑ tag-chain-initial⊑

------------------------------------------------------------------------
-- Refl-run calibration gates
------------------------------------------------------------------------

example12-screens-clean : crossing-suspect example12-entry ≡ clean
example12-screens-clean = refl

nat-chain-screens-clean : crossing-suspect nat-chain-entry ≡ clean
nat-chain-screens-clean = refl

left-path-screens-clean : crossing-suspect left-path-entry ≡ clean
left-path-screens-clean = refl

adversarial-screens-suspect :
  crossing-suspect adversarial-entry ≡ suspect
adversarial-screens-suspect = refl
