module SourceReachabilityResultScratch where

-- File Charter:
--   * Connects the target of the closed gradual source pair in
--     SourceLegScratch to the runtime checkpoints in InitialPairScratch.
--   * Checks that the target projection reached by compilation carries the
--     matching generated-name injection required by CTI inversion.
--   * Records the exact target cancellation route and the companion route
--     for InitialPairScratch's simplified precise CTI checkpoint.

open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

open import Types
open import Consistency
open import TermCtx using (Z)
open import TyStore using (store-empty)
import Imprecision as I
import GradualTerms as G
import GradualTermImprecision as GTI
open import GradualTerms
  using ()
  renaming (_∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_)
open GTI using (_∣_⊢ᴳ_⊑_⦂_⊑_∶_)
open import CastTerms
  using (Term; Value; $; _⟨_⟩; _↑_; _↓_; _《_》; inj; seal)
open import Reduction
open import Primitives using (κℕ)
open import Compile using (compile)
import Conversion as Conv
open Conv using (unseal)
import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision as CTIR
open CTIR using (_∣_⊢²_⊑_∶_)
import proof.DGG.StarRepChainProbe as Probe
import proof.DGG.ReachabilityCatalog as RC
import proof.DGG.ReachabilityScreen as RS
import proof.DGG.notes.InitialPairScratch as IP
import SourceLegScratch as Source

------------------------------------------------------------------------
-- Binder matching fixes the fresh world cell
------------------------------------------------------------------------

matched-Λ-center : ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
  → toRenameᵗ (CTI2.ηᴸʷ (CTI2.liftWorldBoth I.X⊑X W)) zero
    ≡ toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldBoth I.X⊑X W)) zero
matched-Λ-center = refl

matched-Λ-mark : ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
  → CTI2.impEnvʷ (CTI2.liftWorldBoth I.X⊑X W)
      (toRenameᵗ (CTI2.ηᴸʷ (CTI2.liftWorldBoth I.X⊑X W)) zero)
    ≡ I.X⊑X
matched-Λ-mark = refl

matched-Λ-use-not-star : ∀ {Δ} {μ : I.ImpEnv Δ}
  → ¬ (I.extendᵐ I.X⊑X μ I.⊢ ＇ zero ⊑ ★)
matched-Λ-use-not-star (I.X⊑★ ())

erased-Λ-mark : ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
  → CTI2.impEnvʷ (CTI2.liftWorldLeft W)
      (toRenameᵗ (CTI2.ηᴸʷ (CTI2.liftWorldLeft W)) zero)
    ≡ I.X⊑★
erased-Λ-mark = refl

erased-Λ-use-star : ∀ {Δ} {μ : I.ImpEnv Δ}
  → I.instᵐ μ I.⊢ ＇ zero ⊑ ★
erased-Λ-use-star = I.X⊑★ refl

erased-Λ-has-no-target : ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
    (Y : TyVar Δᴿ)
  → toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldLeft W)) Y
    ≢ toRenameᵗ (CTI2.ηᴸʷ (CTI2.liftWorldLeft W)) zero
erased-Λ-has-no-target Y ()

------------------------------------------------------------------------
-- The literal closed source pair reaches InitialPairScratch
------------------------------------------------------------------------

source-right-entry : Source.Q₁ ≡ IP.Qᶜ
source-right-entry = refl

source-left-screen-returns :
  RS.SideSummary.status (RS.runSummary 40 Source.Pᶜ)
    ≡ RS.returned-value
source-left-screen-returns = refl

source-right-screen-returns :
  RS.SideSummary.status (RS.runSummary 40 Source.Qᶜ)
    ≡ RS.returned-value
source-right-screen-returns = refl

------------------------------------------------------------------------
-- Exact target provenance and reduction
------------------------------------------------------------------------

target-core : Term 1
target-core = ($ (κℕ 0)) ⟨ IP.Q-shifted-ℕ! ⟩

target-core-value : Value target-core
target-core-value = $ (κℕ 0) 《 inj 》

target-sealed : Term 1
target-sealed = target-core ↓ Conv.seal zero ★

target-sealed-value : Value target-sealed
target-sealed-value = target-core-value ↓ seal

target-input-gate :
  IP.Q-generated-tagged-input ≡ target-sealed ⟨ IP.Q-Y! ⟩
target-input-gate = refl

reached-catchup-live-replacement :
  Probe.W ∣ [] ⊢² Probe.M ⊑ Probe.N ∶ Probe.input-type
reached-catchup-live-replacement = IP.mid-input

target-route :
  IP.Q₆ —↠[ keep ∷ keep ∷ [] ] target-core
target-route =
  IP.Q₆
  —→[ keep ]⟨
    ξ-reveal (pure-step (tag-untag target-sealed-value)) refl
  ⟩
  target-sealed ↑ unseal zero ★
  —→[ keep ]⟨ pure-step (conceal-reveal target-core-value) ⟩
  target-core ∎[]

------------------------------------------------------------------------
-- Companion reduction for the simplified precise CTI checkpoint
------------------------------------------------------------------------

source-core-value : Value IP.P-two-seal-tagged-zero
source-core-value = $ (κℕ 0) 《 inj 》

source-inner-sealed-value :
  Value (IP.P-two-seal-tagged-zero ↓ Conv.seal 1 ★)
source-inner-sealed-value = source-core-value ↓ seal

source-route :
  IP.P₇ —↠[ keep ∷ keep ∷ [] ] IP.P-two-seal-tagged-zero
source-route =
  IP.P₇
  —→[ keep ]⟨
    ξ-reveal
      (pure-step (conceal-reveal source-inner-sealed-value)) refl
  ⟩
  (IP.P-two-seal-tagged-zero ↓ Conv.seal 1 ★) ↑ unseal 1 ★
  —→[ keep ]⟨ pure-step (conceal-reveal source-core-value) ⟩
  IP.P-two-seal-tagged-zero ∎[]

------------------------------------------------------------------------
-- A target that really exposes the bad projection is not source-related
------------------------------------------------------------------------

bad-bodyᴳ : ∀ {Δ} → G.GTerm Δ
bad-bodyᴳ =
  (G.ƛ ★ ⇒ G.` 0) G.·[ 93 ] G.$ (κℕ 0)

★∼ℕ : ∀ {Δ} → Consistency._∼_ {Δ = Δ} ★ (‵ `ℕ)
★∼ℕ = ？ (id (‵ `ℕ))

bad-body⊢ᴳ : ∀ {Δ Γ} → Δ ∣ Γ ⊢ᴳ bad-bodyᴳ ⦂ ★
bad-body⊢ᴳ =
  G.⊢· (G.⊢ƛ (G.⊢` Z)) (G.⊢$ (κℕ 0)) ★∼ℕ

bad-dynᴳ : ∀ {Δ} → G.GTerm Δ
bad-dynᴳ = G.ƛ ★ ⇒ bad-bodyᴳ

bad-dyn⊢ᴳ : ∀ {Δ Γ}
  → Δ ∣ Γ ⊢ᴳ bad-dynᴳ ⦂ Source.★⇒★ᵗ
bad-dyn⊢ᴳ = G.⊢ƛ bad-body⊢ᴳ

bad-targetᴳ : G.GTerm 0
bad-targetᴳ = Source.Q-funᴳ G.·[ Source.ℓ-outer ] bad-dynᴳ

bad-target⊢ᴳ : 0 ∣ [] ⊢ᴳ bad-targetᴳ ⦂ ★
bad-target⊢ᴳ =
  G.⊢· Source.Q-fun⊢ᴳ bad-dyn⊢ᴳ Source.∀X⇒X∼★⇒★

bad-targetᶜ : Term 0
bad-targetᶜ = RC.compile-screen bad-target⊢ᴳ

bad-target-standardᶜ : Term 0
bad-target-standardᶜ = proj₁ (compile {Σ = store-empty} bad-target⊢ᴳ)

bad-target-skeleton-gate :
  RC.skeleton bad-targetᶜ ≡ RC.skeleton bad-target-standardᶜ
bad-target-skeleton-gate = refl

bad-target-blames :
  RS.SideSummary.status (RS.runSummary 40 bad-targetᶜ)
    ≡ RS.returned-blame
bad-target-blames = refl

no-shifted-bad-body : ∀ {A B : Ty 1}
    {p : I.instᵐ I.idᵐ I.⊢ A ⊑ B}
  → ¬ (I.instᵐ I.idᵐ ∣ [] ⊢ᴳ
      (G.ƛ ＇ zero ⇒ G.` 0) ⊑ G.⇑ᵗᴳ bad-dynᴳ
      ⦂ A ⊑ B ∶ p)
no-shifted-bad-body (GTI.ƛ⊑ƛᴳ ())

no-poly-id-imprecision-any : ∀ {A B : Ty 0}
    {p : I.idᵐ I.⊢ A ⊑ B}
  → ¬ (I.idᵐ ∣ [] ⊢ᴳ Source.polyIdᴳ ⊑ bad-dynᴳ
      ⦂ A ⊑ B ∶ p)
no-poly-id-imprecision-any
    (GTI.Λ⊑ᴳ _ _ GTI.lift-[] _ _ body) =
  no-shifted-bad-body body

no-poly-id-imprecision :
  ¬ (I.idᵐ ∣ [] ⊢ᴳ Source.polyIdᴳ ⊑ bad-dynᴳ
      ⦂ Source.∀X⇒X ⊑ Source.★⇒★ᵗ
      ∶ Source.∀X⇒X⊑★⇒★₀)
no-poly-id-imprecision
    relation =
  no-poly-id-imprecision-any relation

no-bad-source-pair :
  ¬ (I.idᵐ ∣ [] ⊢ᴳ Source.Pᴳ ⊑ bad-targetᴳ
      ⦂ ★ ⊑ ★ ∶ I.★⊑★)
no-bad-source-pair (GTI.·⊑·ᴳ _ argument _ _) =
  no-poly-id-imprecision-any argument
