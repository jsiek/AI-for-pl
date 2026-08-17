module M5DepthScreenScratch where

-- Root-level scratch for the M5 depth reachability screen.
-- It keeps candidate gradual source pairs outside the live catalog,
-- compiles them with the proof-erased screen compiler, and scans right
-- traces/prefixes for inst-cast sites.

open import Data.Bool using (Bool; false; true; _∨_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (proj₁)
import Data.Fin as Fin
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TermCtx using (Z)
open import TyStore using (TyStore; store-empty)
open import Consistency using
  (Env∼; Var∼; X∼★; ★∼X; idᶜ; genᵐ; flipᵐ; _⊢_∼_;
   _∼_; id; _!; ？_; _↦_; gen_; inst_; ★∼Xᵍ; X∼★ᵍ)
import Imprecision as I
import GradualTerms as G
open import GradualTerms
  using (GTerm)
  renaming (_∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_)
import GradualTermImprecision as GTI
open import CastTerms
  using (Term; `_ ; ƛ_; _·_; Λ_; _⦂∀_[_]; $; _⊕[_]_;
   _⟨_⟩; _↑_; _↓_; blame)
open import Eval using (eval; outcomeTrace; step?; step-result)
open import Reduction using (_—↠[_]_; ↠-refl; ↠-step; applyStore)
open import Compile using (compile)
import proof.DGG.ReachabilityCatalog as RC
import proof.DGG.ReachabilityScreen as RS

------------------------------------------------------------------------
-- Trace scanner: target-side inst-cast sites
------------------------------------------------------------------------

termHasInstCast : ∀ {Δ} → Term Δ → Bool
termHasInstCast (` x) = false
termHasInstCast (ƛ M) = termHasInstCast M
termHasInstCast (L · M) = termHasInstCast L ∨ termHasInstCast M
termHasInstCast (Λ M) = termHasInstCast M
termHasInstCast (M ⦂∀ B [ A ]) = termHasInstCast M
termHasInstCast ($ κ) = false
termHasInstCast (L ⊕[ op ] M) =
  termHasInstCast L ∨ termHasInstCast M
termHasInstCast (M ⟨ inst_ c B≢★ ⟩) = true
termHasInstCast (M ⟨ c ⟩) = termHasInstCast M
termHasInstCast (M ↑ c) = termHasInstCast M
termHasInstCast (M ↓ c) = termHasInstCast M
termHasInstCast blame = false

traceHasInstCast : ∀ {Δ Δ′ χs} {M : Term Δ} {N : Term Δ′}
  → M —↠[ χs ] N
  → Bool
traceHasInstCast {M = M} ↠-refl = termHasInstCast M
traceHasInstCast {M = M} (↠-step step rest) =
  termHasInstCast M ∨ traceHasInstCast rest

rightTraceHasInstCast : RS.Entry → Bool
rightTraceHasInstCast e
    with eval (RS.Entry.gasᴿ e) (RS.Entry.more-imprecise e)
rightTraceHasInstCast e | just out =
  traceHasInstCast (outcomeTrace out)
rightTraceHasInstCast e | nothing =
  termHasInstCast (RS.Entry.more-imprecise e)

prefixHasInstCast : ∀ {Δ} → Nat.ℕ → TyStore Δ → Term Δ → Bool
prefixHasInstCast Nat.zero Σ M = termHasInstCast M
prefixHasInstCast (Nat.suc gas) Σ M with termHasInstCast M
prefixHasInstCast (Nat.suc gas) Σ M | true = true
prefixHasInstCast (Nat.suc gas) Σ M | false with step? Σ M
prefixHasInstCast (Nat.suc gas) Σ M | false
    | just (step-result χ N M→N) =
  prefixHasInstCast gas (applyStore χ Σ) N
prefixHasInstCast (Nat.suc gas) Σ M | false | nothing = false

rightPrefixHasInstCast : Nat.ℕ → RS.Entry → Bool
rightPrefixHasInstCast gas e =
  prefixHasInstCast gas store-empty (RS.Entry.more-imprecise e)

------------------------------------------------------------------------
-- Source derivation scanner: consecutive left-only Λ layers
------------------------------------------------------------------------

hasOneSidedΛPrefix : ∀ {Δ μ γ M M′ A B p}
  → GTI._∣_⊢ᴳ_⊑_⦂_⊑_∶_ {Δ} μ γ M M′ A B p
  → Bool
hasOneSidedΛPrefix (GTI.x⊑xᴳ x∈) = false
hasOneSidedΛPrefix (GTI.ƛ⊑ƛᴳ body) = false
hasOneSidedΛPrefix (GTI.·⊑·ᴳ L⊑L′ M⊑M′ A∼C A′∼C′) = false
hasOneSidedΛPrefix (GTI.·⊑·★ᴳ L⊑L′ M⊑M′ A∼C C′∼★) = false
hasOneSidedΛPrefix (GTI.·★⊑·★ᴳ L⊑L′ M⊑M′ C∼★ C′∼★) =
  false
hasOneSidedΛPrefix
    (GTI.Λ⊑Λᴳ liftγ vV vV′ zero∈A zero∈B body) =
  false
hasOneSidedΛPrefix (GTI.Λ⊑ᴳ Anv zero∈A liftγ vV N′⊢ body) =
  true
hasOneSidedΛPrefix (GTI.[]⊑[]ᴳ M⊑M′ q r) = false
hasOneSidedΛPrefix (GTI.[]⊑ᴳ M⊑M′ q r) = false
hasOneSidedΛPrefix (GTI.κ⊑κᴳ κ) = false
hasOneSidedΛPrefix
    (GTI.⊕⊑⊕ᴳ op L⊑L′ A∼arg A′∼arg M⊑M′ B∼arg B′∼arg) =
  false

hasNestedΛPrefix : ∀ {Δ μ γ M M′ A B p}
  → GTI._∣_⊢ᴳ_⊑_⦂_⊑_∶_ {Δ} μ γ M M′ A B p
  → Bool
hasNestedΛPrefix (GTI.x⊑xᴳ x∈) = false
hasNestedΛPrefix (GTI.ƛ⊑ƛᴳ body) = false
hasNestedΛPrefix (GTI.·⊑·ᴳ L⊑L′ M⊑M′ A∼C A′∼C′) = false
hasNestedΛPrefix (GTI.·⊑·★ᴳ L⊑L′ M⊑M′ A∼C C′∼★) = false
hasNestedΛPrefix (GTI.·★⊑·★ᴳ L⊑L′ M⊑M′ C∼★ C′∼★) =
  false
hasNestedΛPrefix
    (GTI.Λ⊑Λᴳ liftγ vV vV′ zero∈A zero∈B body) =
  false
hasNestedΛPrefix (GTI.Λ⊑ᴳ Anv zero∈A liftγ vV N′⊢ body) =
  hasOneSidedΛPrefix body
hasNestedΛPrefix (GTI.[]⊑[]ᴳ M⊑M′ q r) = false
hasNestedΛPrefix (GTI.[]⊑ᴳ M⊑M′ q r) = false
hasNestedΛPrefix (GTI.κ⊑κᴳ κ) = false
hasNestedΛPrefix
    (GTI.⊕⊑⊕ᴳ op L⊑L′ A∼arg A′∼arg M⊑M′ B∼arg B′∼arg) =
  false

sourceHasNestedΛSite : ∀ {Δ μ γ M M′ A B p}
  → GTI._∣_⊢ᴳ_⊑_⦂_⊑_∶_ {Δ} μ γ M M′ A B p
  → Bool
sourceHasNestedΛSite D with hasNestedΛPrefix D
sourceHasNestedΛSite D | true = true
sourceHasNestedΛSite (GTI.x⊑xᴳ x∈) | false = false
sourceHasNestedΛSite (GTI.ƛ⊑ƛᴳ body) | false =
  sourceHasNestedΛSite body
sourceHasNestedΛSite (GTI.·⊑·ᴳ L⊑L′ M⊑M′ A∼C A′∼C′) | false =
  sourceHasNestedΛSite L⊑L′ ∨ sourceHasNestedΛSite M⊑M′
sourceHasNestedΛSite (GTI.·⊑·★ᴳ L⊑L′ M⊑M′ A∼C C′∼★)
    | false =
  sourceHasNestedΛSite L⊑L′ ∨ sourceHasNestedΛSite M⊑M′
sourceHasNestedΛSite (GTI.·★⊑·★ᴳ L⊑L′ M⊑M′ C∼★ C′∼★)
    | false =
  sourceHasNestedΛSite L⊑L′ ∨ sourceHasNestedΛSite M⊑M′
sourceHasNestedΛSite
    (GTI.Λ⊑Λᴳ liftγ vV vV′ zero∈A zero∈B body) | false =
  sourceHasNestedΛSite body
sourceHasNestedΛSite
    (GTI.Λ⊑ᴳ Anv zero∈A liftγ vV N′⊢ body) | false =
  sourceHasNestedΛSite body
sourceHasNestedΛSite (GTI.[]⊑[]ᴳ M⊑M′ q r) | false =
  sourceHasNestedΛSite M⊑M′
sourceHasNestedΛSite (GTI.[]⊑ᴳ M⊑M′ q r) | false =
  sourceHasNestedΛSite M⊑M′
sourceHasNestedΛSite (GTI.κ⊑κᴳ κ) | false = false
sourceHasNestedΛSite
    (GTI.⊕⊑⊕ᴳ op L⊑L′ A∼arg A′∼arg M⊑M′ B∼arg B′∼arg)
    | false =
  sourceHasNestedΛSite L⊑L′ ∨ sourceHasNestedΛSite M⊑M′

------------------------------------------------------------------------
-- Candidate 1: REACHED shape, two erased binders before one matched ∀
------------------------------------------------------------------------

★³ : ∀ {Δ} → Ty Δ
★³ = ★ ⇒ ★ ⇒ ★ ⇒ ★

target-body : ∀ {Δ} → Ty (Nat.suc Δ)
target-body = ★ ⇒ ★ ⇒ ＇ 0 ⇒ ＇ 0

source-body : ∀ {Δ} → Ty (Nat.suc (Nat.suc (Nat.suc Δ)))
source-body = ＇ 2 ⇒ ＇ 1 ⇒ ＇ 0 ⇒ ＇ 0

source-∀Z : ∀ {Δ} → Ty (Nat.suc (Nat.suc Δ))
source-∀Z = `∀ source-body

source-∀Y∀Z : ∀ {Δ} → Ty (Nat.suc Δ)
source-∀Y∀Z = `∀ source-∀Z

source-∀X∀Y∀Z : ∀ {Δ} → Ty Δ
source-∀X∀Y∀Z = `∀ source-∀Y∀Z

target-∀Z : ∀ {Δ} → Ty Δ
target-∀Z = `∀ target-body

Z∈target-body : ∀ {Δ} → Fin.zero ∈ᵗ target-body {Δ}
Z∈target-body =
  ∈-fun-right ∉-star
    (∈-fun-right ∉-star (∈-fun-left var-∈))

Z∈source-body : ∀ {Δ} → Fin.zero ∈ᵗ source-body {Δ}
Z∈source-body =
  ∈-fun-right (∉-var (≢→≢ᶠ (λ ())))
    (∈-fun-right (∉-var (≢→≢ᶠ (λ ()))) (∈-fun-left var-∈))

Y∈source-body : ∀ {Δ} → Fin.suc Fin.zero ∈ᵗ source-body {Δ}
Y∈source-body =
  ∈-fun-right (∉-var (≢→≢ᶠ (λ ()))) (∈-fun-left var-∈)

X∈source-∀Y∀Z : ∀ {Δ} → Fin.zero ∈ᵗ source-∀Y∀Z {Δ}
X∈source-∀Y∀Z = ∈-all (∈-all (∈-fun-left var-∈))

Y∈source-∀Z : ∀ {Δ} → Fin.zero ∈ᵗ source-∀Z {Δ}
Y∈source-∀Z = ∈-all Y∈source-body

star?var : ∀ {Δ} {μ : Env∼ Δ} {X}
  → μ X ≡ ★∼X
  → μ ⊢ ★ ∼ ＇ X
star?var eq =
  ？_ ⦃ Gᵍ = ＇ _ ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄
    (id (＇ _)) ⦃ Bns = nonstar-X ⦄

var!star : ∀ {Δ} {μ : Env∼ Δ} {X}
  → μ X ≡ X∼★
  → μ ⊢ ＇ X ∼ ★
var!star eq =
  _! ⦃ Gᵍ = ＇ _ ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄
    (id (＇ _)) ⦃ Ans = nonstar-X ⦄

★³∼target-∀Z-body :
  genᵐ (idᶜ {Δ = 0}) ⊢ ★³ ∼ target-body
★³∼target-∀Z-body =
  id ★ ↦ id ★ ↦ var!star refl ↦ star?var refl

★³∼target-∀Z : ★³ ∼ target-∀Z
★³∼target-∀Z =
  gen_ ⦃ Bnv = nonvar-fun ⦄ ⦃ z∈B = Z∈target-body ⦄
    ★³∼target-∀Z-body (λ ())

★³∼source-body :
  genᵐ (genᵐ (genᵐ (idᶜ {Δ = 0}))) ⊢ ★³ ∼ source-body
★³∼source-body =
  var!star refl ↦ var!star refl ↦ var!star refl ↦ star?var refl

★³∼source-∀Z :
  genᵐ (genᵐ (idᶜ {Δ = 0})) ⊢ ★³ ∼ source-∀Z
★³∼source-∀Z =
  gen_ ⦃ Bnv = nonvar-fun ⦄ ⦃ z∈B = Z∈source-body ⦄
    ★³∼source-body (λ ())

★³∼source-∀Y∀Z :
  genᵐ (idᶜ {Δ = 0}) ⊢ ★³ ∼ source-∀Y∀Z
★³∼source-∀Y∀Z =
  gen_ ⦃ Bnv = nonvar-all ⦄ ⦃ z∈B = Y∈source-∀Z ⦄
    ★³∼source-∀Z (λ ())

★³∼source-∀X∀Y∀Z : ★³ ∼ source-∀X∀Y∀Z
★³∼source-∀X∀Y∀Z =
  gen_ ⦃ Bnv = nonvar-all ⦄ ⦃ z∈B = X∈source-∀Y∀Z ⦄
    ★³∼source-∀Y∀Z (λ ())

source-triple : ∀ {Δ} → GTerm Δ
source-triple =
  G.Λ (G.Λ (G.Λ
    (G.ƛ ＇ 2 ⇒ G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 0)))

target-one : ∀ {Δ} → GTerm Δ
target-one =
  G.Λ (G.ƛ ★ ⇒ G.ƛ ★ ⇒ G.ƛ ＇ 0 ⇒ G.` 0)

use-dyn : ∀ {Δ} → GTerm Δ
use-dyn = G.ƛ ★³ ⇒ G.` 0

source-triple⊢ : ∀ {Δ Γ} → Δ ∣ Γ ⊢ᴳ source-triple ⦂ source-∀X∀Y∀Z
source-triple⊢ =
  G.⊢Λ {zero∈A = X∈source-∀Y∀Z}
    (G.Λ (G.Λ
      (G.ƛ ＇ 2 ⇒ G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 0)))
    (G.⊢Λ {zero∈A = Y∈source-∀Z}
      (G.Λ (G.ƛ ＇ 2 ⇒ G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 0))
      (G.⊢Λ {zero∈A = Z∈source-body}
        (G.ƛ ＇ 2 ⇒ G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 0)
        (G.⊢ƛ (G.⊢ƛ (G.⊢ƛ (G.⊢` Z))))))

target-one⊢ : ∀ {Δ Γ} → Δ ∣ Γ ⊢ᴳ target-one ⦂ target-∀Z
target-one⊢ =
  G.⊢Λ {zero∈A = Z∈target-body}
    (G.ƛ ★ ⇒ G.ƛ ★ ⇒ G.ƛ ＇ 0 ⇒ G.` 0)
    (G.⊢ƛ (G.⊢ƛ (G.⊢ƛ (G.⊢` Z))))

use-dyn⊢ : ∀ {Δ Γ} → Δ ∣ Γ ⊢ᴳ use-dyn ⦂ ★³ ⇒ ★³
use-dyn⊢ = G.⊢ƛ (G.⊢` Z)

source-body⊑target-body :
  I.extᵐ (I.instᵐ (I.instᵐ (I.idᵐ {Δ = 0}))) I.⊢
    source-body ⊑ target-body
source-body⊑target-body =
  I.⇒⊑⇒ (I.X⊑★ refl)
    (I.⇒⊑⇒ (I.X⊑★ refl) (I.⇒⊑⇒ I.X⊑X I.X⊑X))

source-∀Z⊑target-∀Z :
  I.instᵐ (I.instᵐ (I.idᵐ {Δ = 0})) I.⊢
    source-∀Z ⊑ target-∀Z
source-∀Z⊑target-∀Z = I.∀⊑∀ source-body⊑target-body

source-∀Y∀Z⊑target-∀Z :
  I.instᵐ (I.idᵐ {Δ = 0}) I.⊢ source-∀Y∀Z ⊑ target-∀Z
source-∀Y∀Z⊑target-∀Z =
  I.∀⊑ nonvar-all Y∈source-∀Z source-∀Z⊑target-∀Z

source-∀X∀Y∀Z⊑target-∀Z :
  I.idᵐ {Δ = 0} I.⊢ source-∀X∀Y∀Z ⊑ target-∀Z
source-∀X∀Y∀Z⊑target-∀Z =
  I.∀⊑ nonvar-all X∈source-∀Y∀Z source-∀Y∀Z⊑target-∀Z

★³⊑★³ : ∀ {Δ} {μ : I.ImpEnv Δ} → μ I.⊢ ★³ ⊑ ★³
★³⊑★³ = I.⇒⊑⇒ I.★⊑★ (I.⇒⊑⇒ I.★⊑★
  (I.⇒⊑⇒ I.★⊑★ I.★⊑★))

★³⊑★³₀ : I.idᵐ {Δ = 0} I.⊢ ★³ ⊑ ★³
★³⊑★³₀ = ★³⊑★³

★³⇒★³⊑★³⇒★³₀ : I.idᵐ {Δ = 0} I.⊢ ★³ ⇒ ★³ ⊑ ★³ ⇒ ★³
★³⇒★³⊑★³⇒★³₀ = I.⇒⊑⇒ ★³⊑★³₀ ★³⊑★³₀

γ★ : ∀ {Δ} {μ : I.ImpEnv Δ} → GTI.CtxImp μ
γ★ = GTI.ctx-imp ★ ★ I.★⊑★ ∷ []

liftγ★ : ∀ {Δ} {μ : I.ImpEnv Δ} {ν : I.ImpEnv (Nat.suc Δ)}
  → GTI.LiftCtxⁱ ν (γ★ {μ = μ}) (γ★ {μ = ν})
liftγ★ = GTI.lift-∷ GTI.lift-[]

source-target-body⊑ :
  I.extᵐ (I.instᵐ (I.instᵐ (I.idᵐ {Δ = 0}))) GTI.∣ []
    ⊢ᴳ
      (G.ƛ ＇ 2 ⇒ G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 0)
    ⊑ (G.ƛ ★ ⇒ G.ƛ ★ ⇒ G.ƛ ＇ 0 ⇒ G.` 0)
    ⦂ source-body ⊑ target-body ∶ source-body⊑target-body
source-target-body⊑ =
  GTI.ƛ⊑ƛᴳ
    (GTI.ƛ⊑ƛᴳ
      (GTI.ƛ⊑ƛᴳ (GTI.x⊑xᴳ GTI.Zⁱ)))

source-target-body⊑γ★ :
  I.extᵐ (I.instᵐ (I.instᵐ (I.idᵐ {Δ = 0}))) GTI.∣ γ★
    ⊢ᴳ
      (G.ƛ ＇ 2 ⇒ G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 0)
    ⊑ (G.ƛ ★ ⇒ G.ƛ ★ ⇒ G.ƛ ＇ 0 ⇒ G.` 0)
    ⦂ source-body ⊑ target-body ∶ source-body⊑target-body
source-target-body⊑γ★ =
  GTI.ƛ⊑ƛᴳ
    (GTI.ƛ⊑ƛᴳ
      (GTI.ƛ⊑ƛᴳ (GTI.x⊑xᴳ GTI.Zⁱ)))

source-target-∀Z⊑ :
  I.instᵐ (I.instᵐ (I.idᵐ {Δ = 0})) GTI.∣ []
    ⊢ᴳ
      (G.Λ (G.ƛ ＇ 2 ⇒ G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 0))
    ⊑ (G.Λ (G.ƛ ★ ⇒ G.ƛ ★ ⇒ G.ƛ ＇ 0 ⇒ G.` 0))
    ⦂ source-∀Z ⊑ target-∀Z ∶ source-∀Z⊑target-∀Z
source-target-∀Z⊑ =
  GTI.Λ⊑Λᴳ GTI.lift-[]
    (G.ƛ ＇ 2 ⇒ G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 0)
    (G.ƛ ★ ⇒ G.ƛ ★ ⇒ G.ƛ ＇ 0 ⇒ G.` 0)
    Z∈source-body Z∈target-body source-target-body⊑

source-target-∀Z⊑γ★ :
  I.instᵐ (I.instᵐ (I.idᵐ {Δ = 0})) GTI.∣ γ★
    ⊢ᴳ
      (G.Λ (G.ƛ ＇ 2 ⇒ G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 0))
    ⊑ (G.Λ (G.ƛ ★ ⇒ G.ƛ ★ ⇒ G.ƛ ＇ 0 ⇒ G.` 0))
    ⦂ source-∀Z ⊑ target-∀Z ∶ source-∀Z⊑target-∀Z
source-target-∀Z⊑γ★ =
  GTI.Λ⊑Λᴳ liftγ★
    (G.ƛ ＇ 2 ⇒ G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 0)
    (G.ƛ ★ ⇒ G.ƛ ★ ⇒ G.ƛ ＇ 0 ⇒ G.` 0)
    Z∈source-body Z∈target-body source-target-body⊑γ★

source-target-after-Y⊑ :
  I.instᵐ (I.idᵐ {Δ = 0}) GTI.∣ []
    ⊢ᴳ
      (G.Λ
        (G.Λ (G.ƛ ＇ 2 ⇒ G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 0)))
    ⊑ G.⇑ᵗᴳ target-one
    ⦂ source-∀Y∀Z ⊑ target-∀Z ∶ source-∀Y∀Z⊑target-∀Z
source-target-after-Y⊑ =
  GTI.Λ⊑ᴳ nonvar-all Y∈source-∀Z GTI.lift-[]
    (G.Λ (G.ƛ ＇ 2 ⇒ G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 0))
    target-one⊢
    source-target-∀Z⊑

source-target-after-Y⊑γ★ :
  I.instᵐ (I.idᵐ {Δ = 0}) GTI.∣ γ★
    ⊢ᴳ
      (G.Λ
        (G.Λ (G.ƛ ＇ 2 ⇒ G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 0)))
    ⊑ G.⇑ᵗᴳ target-one
    ⦂ source-∀Y∀Z ⊑ target-∀Z ∶ source-∀Y∀Z⊑target-∀Z
source-target-after-Y⊑γ★ =
  GTI.Λ⊑ᴳ nonvar-all Y∈source-∀Z liftγ★
    (G.Λ (G.ƛ ＇ 2 ⇒ G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 0))
    target-one⊢
    source-target-∀Z⊑γ★

source-target-argument⊑ :
  I.idᵐ GTI.∣ [] ⊢ᴳ source-triple ⊑ target-one
    ⦂ source-∀X∀Y∀Z ⊑ target-∀Z
    ∶ source-∀X∀Y∀Z⊑target-∀Z
source-target-argument⊑ =
  GTI.Λ⊑ᴳ nonvar-all X∈source-∀Y∀Z GTI.lift-[]
    (G.Λ
      (G.Λ (G.ƛ ＇ 2 ⇒ G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 0)))
    target-one⊢
    source-target-after-Y⊑

source-target-argument⊑γ★ :
  I.idᵐ GTI.∣ γ★ ⊢ᴳ source-triple ⊑ target-one
    ⦂ source-∀X∀Y∀Z ⊑ target-∀Z
    ∶ source-∀X∀Y∀Z⊑target-∀Z
source-target-argument⊑γ★ =
  GTI.Λ⊑ᴳ nonvar-all X∈source-∀Y∀Z liftγ★
    (G.Λ
      (G.Λ (G.ƛ ＇ 2 ⇒ G.ƛ ＇ 1 ⇒ G.ƛ ＇ 0 ⇒ G.` 0)))
    target-one⊢
    source-target-after-Y⊑γ★

use-dyn⊑use-dyn :
  I.idᵐ GTI.∣ [] ⊢ᴳ use-dyn ⊑ use-dyn
    ⦂ ★³ ⇒ ★³ ⊑ ★³ ⇒ ★³ ∶ ★³⇒★³⊑★³⇒★³₀
use-dyn⊑use-dyn = GTI.ƛ⊑ƛᴳ (GTI.x⊑xᴳ GTI.Zⁱ)

reached-left : GTerm 0
reached-left = use-dyn G.·[ 301 ] source-triple

reached-right : GTerm 0
reached-right = use-dyn G.·[ 301 ] target-one

reached-left⊢ : 0 ∣ [] ⊢ᴳ reached-left ⦂ ★³
reached-left⊢ =
  G.⊢· use-dyn⊢ source-triple⊢ ★³∼source-∀X∀Y∀Z

reached-right⊢ : 0 ∣ [] ⊢ᴳ reached-right ⦂ ★³
reached-right⊢ =
  G.⊢· use-dyn⊢ target-one⊢ ★³∼target-∀Z

reached⊑ :
  I.idᵐ GTI.∣ [] ⊢ᴳ reached-left ⊑ reached-right
    ⦂ ★³ ⊑ ★³ ∶ ★³⊑★³₀
reached⊑ =
  GTI.·⊑·ᴳ use-dyn⊑use-dyn source-target-argument⊑
    ★³∼source-∀X∀Y∀Z ★³∼target-∀Z

reached-entry : RS.Entry
reached-entry =
  RS.entry (RC.compile-screen reached-left⊢)
    (RC.compile-screen reached-right⊢) 30 30

reached-left-skeleton-gate :
  RC.skeleton (RS.Entry.more-precise reached-entry) ≡
  RC.skeleton (proj₁ (compile {Σ = store-empty} reached-left⊢))
reached-left-skeleton-gate = refl

reached-right-skeleton-gate :
  RC.skeleton (RS.Entry.more-imprecise reached-entry) ≡
  RC.skeleton (proj₁ (compile {Σ = store-empty} reached-right⊢))
reached-right-skeleton-gate = refl

reached-source-nested-left-Λ :
  sourceHasNestedΛSite reached⊑ ≡ true
reached-source-nested-left-Λ = refl

reached-right-initial-inst-cast :
  rightPrefixHasInstCast 1 reached-entry ≡ true
reached-right-initial-inst-cast = refl

------------------------------------------------------------------------
-- Candidate 2: nested erased Λs under a matched term lambda, not forced
------------------------------------------------------------------------

under-lambda-left : GTerm 0
under-lambda-left = G.ƛ ★ ⇒ source-triple

under-lambda-right : GTerm 0
under-lambda-right = G.ƛ ★ ⇒ target-one

under-lambda-type⊑ :
  I.idᵐ {Δ = 0} I.⊢
    ★ ⇒ source-∀X∀Y∀Z ⊑ ★ ⇒ target-∀Z
under-lambda-type⊑ =
  I.⇒⊑⇒ I.★⊑★ source-∀X∀Y∀Z⊑target-∀Z

under-lambda-left⊢ :
  0 ∣ [] ⊢ᴳ under-lambda-left ⦂ ★ ⇒ source-∀X∀Y∀Z
under-lambda-left⊢ = G.⊢ƛ source-triple⊢

under-lambda-right⊢ :
  0 ∣ [] ⊢ᴳ under-lambda-right ⦂ ★ ⇒ target-∀Z
under-lambda-right⊢ = G.⊢ƛ target-one⊢

under-lambda⊑ :
  I.idᵐ GTI.∣ [] ⊢ᴳ under-lambda-left ⊑ under-lambda-right
    ⦂ ★ ⇒ source-∀X∀Y∀Z ⊑ ★ ⇒ target-∀Z
    ∶ under-lambda-type⊑
under-lambda⊑ = GTI.ƛ⊑ƛᴳ source-target-argument⊑γ★

under-lambda-entry : RS.Entry
under-lambda-entry =
  RS.entry (RC.compile-screen under-lambda-left⊢)
    (RC.compile-screen under-lambda-right⊢) 4 4

under-lambda-source-nested-left-Λ :
  sourceHasNestedΛSite under-lambda⊑ ≡ true
under-lambda-source-nested-left-Λ = refl

under-lambda-right-no-inst-cast :
  rightPrefixHasInstCast 4 under-lambda-entry ≡ false
under-lambda-right-no-inst-cast = refl

------------------------------------------------------------------------
-- Control candidates from the existing source catalog / source-leg note
------------------------------------------------------------------------

left-only-inst-source-no-depth2 :
  sourceHasNestedΛSite
    (RC.SourceEntry.initial⊑ᴳ RC.left-only-inst-path) ≡ false
left-only-inst-source-no-depth2 = refl

left-only-inst-right-no-inst-cast :
  rightTraceHasInstCast (RC.compiled RC.left-only-inst-path) ≡ false
left-only-inst-right-no-inst-cast = refl

left-only-gen-source-no-depth2 :
  sourceHasNestedΛSite
    (RC.SourceEntry.initial⊑ᴳ RC.left-only-gen-path) ≡ false
left-only-gen-source-no-depth2 = refl

left-only-gen-right-no-inst-cast :
  rightTraceHasInstCast (RC.compiled RC.left-only-gen-path) ≡ false
left-only-gen-right-no-inst-cast = refl

example12-right-inst-cast :
  rightTraceHasInstCast RS.example12-entry ≡ true
example12-right-inst-cast = refl
