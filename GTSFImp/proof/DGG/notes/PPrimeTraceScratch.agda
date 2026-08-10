module proof.DGG.notes.PPrimeTraceScratch where

-- Root-only scratch for the P' trace question.
-- It keeps the source term, compile-screen term, and checked evaluator gates
-- outside GTSFImp/.

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TermCtx using (Z)
open import TyStore using (store-empty)
open import Consistency using
  (Env∼; X∼★; ★∼X; X∼X; idᶜ; extᵐ; instᵐ; genᵐ;
   _⊢_∼_; _∼_; id; _!; ？_; _↦_; X∼★ᵍ; ★∼Xᵍ)
import Conversion as Conv
open import Primitives using (κℕ)
open import GradualTerms
  using (GTerm)
  renaming
    ( `_ to `ᴳ_
    ; ƛ_⇒_ to ƛᴳ_⇒_
    ; _·[_]_ to _·ᴳ[_]_
    ; Λ_ to Λᴳ_
    ; _`[_] to _`ᴳ[_]
    ; $ to $ᴳ
    ; Value to Valueᴳ
    ; _∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_
    ; ⊢` to ⊢ᴳ`
    ; ⊢ƛ to ⊢ᴳƛ
    ; ⊢· to ⊢ᴳ·
    ; ⊢Λ to ⊢ᴳΛ
    ; ⊢• to ⊢ᴳ•
    ; ⊢$ to ⊢ᴳ$
    )
open import CastTerms
  using
    (Term; Value; ƛ_; Λ_; $; _·_; _⦂∀_[_]; _⟨_⟩; _↑_;
     _↓_; _《_》; inj; seal; blame)
open import Reduction
open import Eval
open import Compile using (compile)
import proof.DGG.ReachabilityCatalog as RC
import proof.DGG.ReachabilityScreen as RS

------------------------------------------------------------------------
-- The source program
------------------------------------------------------------------------

ℕ₀ : Ty 0
ℕ₀ = ‵ `ℕ

X⇒X : ∀ {Δ} → Ty (suc Δ)
X⇒X = ＇ 0 ⇒ ＇ 0

innerIdᴳ : GTerm 1
innerIdᴳ = Λᴳ (ƛᴳ ＇ 0 ⇒ `ᴳ 0)

innerId⊢ᴳ : 1 ∣ [] ⊢ᴳ innerIdᴳ ⦂ `∀ X⇒X
innerId⊢ᴳ =
  ⊢ᴳΛ {zero∈A = ∈-fun-left var-∈}
    (ƛᴳ ＇ 0 ⇒ `ᴳ 0)
    (⊢ᴳƛ (⊢ᴳ` Z))

innerId⊢ᴳ-d : 1 ∣ (＇ 0 ∷ []) ⊢ᴳ innerIdᴳ ⦂ `∀ X⇒X
innerId⊢ᴳ-d =
  ⊢ᴳΛ {zero∈A = ∈-fun-left var-∈}
    (ƛᴳ ＇ 0 ⇒ `ᴳ 0)
    (⊢ᴳƛ (⊢ᴳ` Z))

bodyᴳ : GTerm 1
bodyᴳ = ƛᴳ ＇ 0 ⇒ ((innerIdᴳ `ᴳ[ ＇ 0 ]) ·ᴳ[ 0 ] `ᴳ 0)

body⊢ᴳ : 1 ∣ [] ⊢ᴳ bodyᴳ ⦂ X⇒X
body⊢ᴳ =
  ⊢ᴳƛ
    (⊢ᴳ· (⊢ᴳ• innerId⊢ᴳ-d) (⊢ᴳ` Z) (id (＇ 0)))

polyᴳ : GTerm 0
polyᴳ = Λᴳ bodyᴳ

poly⊢ᴳ : 0 ∣ [] ⊢ᴳ polyᴳ ⦂ `∀ X⇒X
poly⊢ᴳ =
  ⊢ᴳΛ {zero∈A = ∈-fun-left var-∈}
    (ƛᴳ ＇ 0 ⇒ ((innerIdᴳ `ᴳ[ ＇ 0 ]) ·ᴳ[ 0 ] `ᴳ 0))
    body⊢ᴳ

★∼ℕ : ★ ∼ ℕ₀
★∼ℕ = ？ (id (‵ `ℕ))

P′ᴳ : GTerm 0
P′ᴳ = (polyᴳ `ᴳ[ ★ ]) ·ᴳ[ 0 ] ($ᴳ (κℕ 0))

P′⊢ᴳ : 0 ∣ [] ⊢ᴳ P′ᴳ ⦂ ★
P′⊢ᴳ =
  ⊢ᴳ· (⊢ᴳ• poly⊢ᴳ) (⊢ᴳ$ (κℕ 0)) ★∼ℕ

------------------------------------------------------------------------
-- Compile-screen term and fidelity gate
------------------------------------------------------------------------

P′ᶜ : Term 0
P′ᶜ = RC.compile-screen P′⊢ᴳ

P′-standardᶜ : Term 0
P′-standardᶜ = proj₁ (compile {Σ = store-empty} P′⊢ᴳ)

P′-skeleton-gate : RC.skeleton P′ᶜ ≡ RC.skeleton P′-standardᶜ
P′-skeleton-gate = refl

P′-entry : RS.Entry
P′-entry = RS.entry P′ᶜ P′ᶜ 30 30

P′-screen-clean : RS.crossing-suspect P′-entry ≡ RS.clean
P′-screen-clean = refl

------------------------------------------------------------------------
-- Environment-mode facts for the fresh name
------------------------------------------------------------------------

plain-β-mode : extᵐ (idᶜ {Δ = 0}) Fin.zero ≡ X∼X
plain-β-mode = refl

plain-β-no-X∼★ : extᵐ (idᶜ {Δ = 0}) Fin.zero ≡ X∼★ → ⊥
plain-β-no-X∼★ ()

plain-β-no-★∼X : extᵐ (idᶜ {Δ = 0}) Fin.zero ≡ ★∼X → ⊥
plain-β-no-★∼X ()

inst-mode : instᵐ (idᶜ {Δ = 0}) Fin.zero ≡ X∼★
inst-mode = refl

gen-mode : genᵐ (idᶜ {Δ = 0}) Fin.zero ≡ ★∼X
gen-mode = refl

inst-X∼★ : instᵐ (idᶜ {Δ = 0}) ⊢ ＇ Fin.zero ∼ ★
inst-X∼★ =
  _! ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ G∼★ = X∼★ᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Ans = nonstar-X ⦄

gen-★∼X : genᵐ (idᶜ {Δ = 0}) ⊢ ★ ∼ ＇ Fin.zero
gen-★∼X =
  ？_ ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ ★∼G = ★∼Xᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Bns = nonstar-X ⦄

------------------------------------------------------------------------
-- Refl evaluator gate
------------------------------------------------------------------------

P′-eval-is-value : RS.SideSummary.status (RS.runSummary 30 P′ᶜ)
  ≡ RS.returned-value
P′-eval-is-value = refl

P′-eval-allocations : RS.SideSummary.allocations (RS.runSummary 30 P′ᶜ)
  ≡ RS.alloc 0 0 RS.entry-star [] ∷
     RS.alloc 3 1 RS.entry-var (0 ∷ []) ∷ []
P′-eval-allocations = refl

P′-eval-tags : RS.SideSummary.tags (RS.runSummary 30 P′ᶜ) ≡ []
P′-eval-tags = refl

------------------------------------------------------------------------
-- The decisive local conversion route
------------------------------------------------------------------------

ℕ!ᶜ : ∀ {Δ} (μ : Env∼ Δ) → μ ⊢ ‵ `ℕ ∼ ★
ℕ!ᶜ μ = id (‵ `ℕ) !

tagged-zeroᶜ : ∀ {Δ} → Env∼ Δ → Term Δ
tagged-zeroᶜ μ = ($ (κℕ 0)) ⟨ ℕ!ᶜ μ ⟩

tagged-zero-value : ∀ {Δ} {μ : Env∼ Δ} → Value (tagged-zeroᶜ μ)
tagged-zero-value = ($ (κℕ 0)) 《 inj 》

two-seal-arg : Term 2
two-seal-arg =
  ((tagged-zeroᶜ (idᶜ {Δ = 2}) ↓ Conv.seal 1 ★)
    ↓ Conv.seal 0 (＇ 1))

two-seal-result-context : Term 2
two-seal-result-context =
  (two-seal-arg ↑ Conv.unseal 0 (＇ 1)) ↑ Conv.unseal 1 ★

two-seal-route :
  two-seal-result-context —↠[ keep ∷ keep ∷ [] ]
    tagged-zeroᶜ (idᶜ {Δ = 2})
two-seal-route =
  two-seal-result-context
  —→[ keep ]⟨
    ξ-reveal
      (pure-step (conceal-reveal (tagged-zero-value ↓ seal)))
      refl
  ⟩
  (tagged-zeroᶜ (idᶜ {Δ = 2}) ↓ Conv.seal 1 ★)
    ↑ Conv.unseal 1 ★
  —→[ keep ]⟨ pure-step (conceal-reveal tagged-zero-value) ⟩
  tagged-zeroᶜ (idᶜ {Δ = 2}) ∎[]

bad-variable-projection : Term 1
bad-variable-projection =
  tagged-zeroᶜ (genᵐ (idᶜ {Δ = 0})) ⟨ gen-★∼X ⟩

bad-variable-projection-blames : bad-variable-projection —→ blame
bad-variable-projection-blames =
  tag-untag-bad
    ⦃ Gᵍ = ‵ `ℕ ⦄ ⦃ Hᵍ = ＇ Fin.zero ⦄
    ($ (κℕ 0)) (λ ())
