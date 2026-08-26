module proof.DGG.notes.InitialPairScratch where

-- Checked scratch for the initial closed CastTerm pair used by the
-- problematic extra-cast-right inversion.  The file constructs the right
-- GEN-cast partner of PPrimeTraceScratch.P′ᶜ, proves the closed initial
-- version-2 imprecision relation, and records evaluator-backed checkpoints.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (proj₁)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TyStore using (store-empty)
open import TermCtx using (Z)
open import Consistency using
  (Env∼; idᶜ; instᵐ; genᵐ; flipᵐ; renameEnv∼; wk↪ᵗ;
   _⊢_∼_; _∼_; id; _!; ？_; _↦_; gen_; X∼★ᵍ; ★∼Xᵍ)
import Conversion as Conv
import Imprecision as I
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
    (Term; Value; `_ ; ƛ_; Λ_; $; _·_; _⦂∀_[_]; _⟨_⟩; _↑_; _↓_;
     _《_》; inj; ⟨_,_,_⟩; _⊢_⦂_; ⊢`; ⊢ƛ; ⊢·; ⊢•; ⊢⟨⟩)
open import Compile using (compile)
open import Eval using (step?)
open import Reduction using (keep; bind)
import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision as CTIR
open CTI2 using
  (World;
   _⊑ᵂ⟨_⟩_;
   ctx-imp;
   lift-[];
   lift-∷;
   liftᴸ-[];
   liftᴸ-∷)
open CTIR using
  (_∣_⊢²_⊑_∶_;
   x⊑x²;
   ƛ⊑ƛ²;
   ·⊑·²;
   Λ⊑²;
   •⊑•²;
   •⊑²;
   κ⊑κ²;
   cast⊑cast²;
   ⊑cast²)
import proof.DGG.CompilePreservesImprecision2 as CPI2
import proof.DGG.ExampleTerms as Ex
import proof.DGG.OneStep as Step
import proof.DGG.ReachabilityCatalog as RC
import proof.DGG.ReachabilityScreen as RS
import proof.DGG.StarRepChainProbe as Probe
import proof.DGG.notes.PPrimeTraceScratch as P

------------------------------------------------------------------------
-- Shared closed casts and the right GEN partner
------------------------------------------------------------------------

ℕ₀ : Ty 0
ℕ₀ = ‵ `ℕ

X⇒X : ∀ {Δ} → Ty (suc Δ)
X⇒X = ＇ Fin.zero ⇒ ＇ Fin.zero

ℕ! : ∀ {Δ} → idᶜ {Δ = Δ} ⊢ ‵ `ℕ ∼ ★
ℕ! = id (‵ `ℕ) !

X! : ∀ {Δ} {μ : Env∼ Δ}
  → instᵐ μ ⊢ ＇ Fin.zero ∼ ★
X! =
  _! ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ G∼★ = X∼★ᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Ans = nonstar-X ⦄

X? : ∀ {Δ} {μ : Env∼ Δ}
  → genᵐ μ ⊢ ★ ∼ ＇ Fin.zero
X? =
  ？_ ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ ★∼G = ★∼Xᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Bns = nonstar-X ⦄

X!-gen-domain : ∀ {Δ} {μ : Env∼ Δ}
  → flipᵐ (genᵐ μ) ⊢ ＇ Fin.zero ∼ ★
X!-gen-domain =
  _! ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ G∼★ = X∼★ᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Ans = nonstar-X ⦄

★⇒★∼∀X⇒X : ∀ {Δ} → idᶜ {Δ = Δ} ⊢ ★ ⇒ ★ ∼ `∀ X⇒X
★⇒★∼∀X⇒X =
  gen_ ⦃ Bnv = nonvar-fun ⦄ ⦃ z∈B = ∈-fun-left var-∈ ⦄
    (X!-gen-domain ↦ X?) (λ ())

dynIdᶜ : ∀ {Δ} → Term Δ
dynIdᶜ = ƛ (` 0)

genDynIdᶜ : Term 0
genDynIdᶜ = dynIdᶜ ⟨ ★⇒★∼∀X⇒X ⟩

innerIdᶜ : ∀ {Δ} → Term Δ
innerIdᶜ = Λ (ƛ (` 0))

taggedZeroᶜ : ∀ {Δ} → Term Δ
taggedZeroᶜ = ($ (κℕ 0)) ⟨ ℕ! ⟩

PBodyᶜ : Term 1
PBodyᶜ =
  ((innerIdᶜ ⦂∀ X⇒X [ ＇ Fin.zero ])
    · ((` 0) ⟨ id {μ = idᶜ {Δ = 1}} (＇ Fin.zero) ⟩))

PFunᶜ : Term 0
PFunᶜ = Λ (ƛ PBodyᶜ)

PCalleeᶜ : Term 0
PCalleeᶜ = PFunᶜ ⦂∀ X⇒X [ ★ ]

PLocalᶜ : Term 0
PLocalᶜ = PCalleeᶜ · taggedZeroᶜ

Pᶜ : Term 0
Pᶜ = P.P′ᶜ

Pᶜ-local-gate : Pᶜ ≡ PLocalᶜ
Pᶜ-local-gate = refl

QBodyᶜ : Term 0
QBodyᶜ =
  ((genDynIdᶜ ⦂∀ X⇒X [ ★ ])
    · ((` 0) ⟨ id {μ = idᶜ {Δ = 0}} ★ ⟩))

QFunᶜ : Term 0
QFunᶜ = ƛ QBodyᶜ

Qᶜ : Term 0
Qᶜ = QFunᶜ · taggedZeroᶜ

Qᶜ-entry : RS.Entry
Qᶜ-entry = RS.entry Pᶜ Qᶜ 40 40

Qᶜ-eval-is-value : RS.SideSummary.status (RS.runSummary 40 Qᶜ)
  ≡ RS.returned-value
Qᶜ-eval-is-value = refl

Qᶜ-eval-allocations : RS.SideSummary.allocations (RS.runSummary 40 Qᶜ)
  ≡ RS.alloc 1 0 RS.entry-star [] ∷ []
Qᶜ-eval-allocations = refl

Qᶜ-eval-tags-nonempty :
  RS.SideSummary.tags (RS.runSummary 40 Qᶜ) ≢ []
Qᶜ-eval-tags-nonempty ()

------------------------------------------------------------------------
-- Right trace to the generated-name tagged sealed input
------------------------------------------------------------------------

Q-step₀ : Step.OneStep store-empty Qᶜ
Q-step₀ = Step.from-just-step (step? store-empty Qᶜ) refl

Q₁ : Term (Step.Δ′ Q-step₀)
Q₁ = Step.next Q-step₀

Q-store₁ = Step.store-after Q-step₀

Q-step₁ : Step.OneStep Q-store₁ Q₁
Q-step₁ = Step.from-just-step (step? Q-store₁ Q₁) refl

Q₂ : Term (Step.Δ′ Q-step₁)
Q₂ = Step.next Q-step₁

Q-store₂ = Step.store-after Q-step₁

Q-step₂ : Step.OneStep Q-store₂ Q₂
Q-step₂ = Step.from-just-step (step? Q-store₂ Q₂) refl

Q₃ : Term (Step.Δ′ Q-step₂)
Q₃ = Step.next Q-step₂

Q-store₃ = Step.store-after Q-step₂

Q-step₃ : Step.OneStep Q-store₃ Q₃
Q-step₃ = Step.from-just-step (step? Q-store₃ Q₃) refl

Q₄ : Term (Step.Δ′ Q-step₃)
Q₄ = Step.next Q-step₃

Q-store₄ = Step.store-after Q-step₃

Q-step₄ : Step.OneStep Q-store₄ Q₄
Q-step₄ = Step.from-just-step (step? Q-store₄ Q₄) refl

Q₅ : Term (Step.Δ′ Q-step₄)
Q₅ = Step.next Q-step₄

Q-store₅ = Step.store-after Q-step₄

Q-step₅ : Step.OneStep Q-store₅ Q₅
Q-step₅ = Step.from-just-step (step? Q-store₅ Q₅) refl

Q₆ : Term (Step.Δ′ Q-step₅)
Q₆ = Step.next Q-step₅

Q-step₀-change : Step.change Q-step₀ ≡ keep
Q-step₀-change = refl

Q-step₁-change : Step.change Q-step₁ ≡ bind ★
Q-step₁-change = refl

Q-step₂-change : Step.change Q-step₂ ≡ keep
Q-step₂-change = refl

Q-step₃-change : Step.change Q-step₃ ≡ keep
Q-step₃-change = refl

Q-step₄-change : Step.change Q-step₄ ≡ keep
Q-step₄-change = refl

Q-step₅-change : Step.change Q-step₅ ≡ keep
Q-step₅-change = refl

Q-tag-env : Env∼ 1
Q-tag-env = flipᵐ (genᵐ (idᶜ {Δ = 0}))

Q-Y! : Q-tag-env ⊢ ＇ Fin.zero ∼ ★
Q-Y! = id (＇ Fin.zero) !

Q-shifted-env : Env∼ 1
Q-shifted-env = renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})

Q-shifted-ℕ! : Q-shifted-env ⊢ ‵ `ℕ ∼ ★
Q-shifted-ℕ! = id (‵ `ℕ) !

Q-generated-tagged-input : Term 1
Q-generated-tagged-input =
  (($ (κℕ 0) ⟨ Q-shifted-ℕ! ⟩) ↓ Conv.seal Fin.zero ★)
    ⟨ Q-Y! ⟩

Q₆-generated-tagged-input-gate :
  Q₆ ≡ (Q-generated-tagged-input ⟨ X? ⟩) ↑ Conv.unseal Fin.zero ★
Q₆-generated-tagged-input-gate = refl

------------------------------------------------------------------------
-- Left trace to the two-seal state
------------------------------------------------------------------------

P-step₀ : Step.OneStep store-empty Pᶜ
P-step₀ = Step.from-just-step (step? store-empty Pᶜ) refl

P₁ : Term (Step.Δ′ P-step₀)
P₁ = Step.next P-step₀

P-store₁ = Step.store-after P-step₀

P-step₁ : Step.OneStep P-store₁ P₁
P-step₁ = Step.from-just-step (step? P-store₁ P₁) refl

P₂ : Term (Step.Δ′ P-step₁)
P₂ = Step.next P-step₁

P-store₂ = Step.store-after P-step₁

P-step₂ : Step.OneStep P-store₂ P₂
P-step₂ = Step.from-just-step (step? P-store₂ P₂) refl

P₃ : Term (Step.Δ′ P-step₂)
P₃ = Step.next P-step₂

P-store₃ = Step.store-after P-step₂

P-step₃ : Step.OneStep P-store₃ P₃
P-step₃ = Step.from-just-step (step? P-store₃ P₃) refl

P₄ : Term (Step.Δ′ P-step₃)
P₄ = Step.next P-step₃

P-store₄ = Step.store-after P-step₃

P-step₄ : Step.OneStep P-store₄ P₄
P-step₄ = Step.from-just-step (step? P-store₄ P₄) refl

P₅ : Term (Step.Δ′ P-step₄)
P₅ = Step.next P-step₄

P-store₅ = Step.store-after P-step₄

P-step₅ : Step.OneStep P-store₅ P₅
P-step₅ = Step.from-just-step (step? P-store₅ P₅) refl

P₆ : Term (Step.Δ′ P-step₅)
P₆ = Step.next P-step₅

P-store₆ = Step.store-after P-step₅

P-step₆ : Step.OneStep P-store₆ P₆
P-step₆ = Step.from-just-step (step? P-store₆ P₆) refl

P₇ : Term (Step.Δ′ P-step₆)
P₇ = Step.next P-step₆

P-step₀-change : Step.change P-step₀ ≡ bind ★
P-step₀-change = refl

P-step₁-change : Step.change P-step₁ ≡ keep
P-step₁-change = refl

P-step₂-change : Step.change P-step₂ ≡ keep
P-step₂-change = refl

P-step₃-change : Step.change P-step₃ ≡ bind (＇ Fin.zero)
P-step₃-change = refl

P-step₄-change : Step.change P-step₄ ≡ keep
P-step₄-change = refl

P-step₅-change : Step.change P-step₅ ≡ keep
P-step₅-change = refl

P-step₆-change : Step.change P-step₆ ≡ keep
P-step₆-change = refl

P-two-seal-env : Env∼ 2
P-two-seal-env =
  renameEnv∼ wk↪ᵗ (renameEnv∼ wk↪ᵗ (flipᵐ (idᶜ {Δ = 0})))

P-two-seal-ℕ! : P-two-seal-env ⊢ ‵ `ℕ ∼ ★
P-two-seal-ℕ! = id (‵ `ℕ) !

P-two-seal-tagged-zero : Term 2
P-two-seal-tagged-zero = ($ (κℕ 0)) ⟨ P-two-seal-ℕ! ⟩

P-two-seal-arg : Term 2
P-two-seal-arg =
  ((P-two-seal-tagged-zero ↓ Conv.seal 1 ★)
    ↓ Conv.seal 0 (＇ 1))

P-two-seal-result-context : Term 2
P-two-seal-result-context =
  (P-two-seal-arg ↑ Conv.unseal 0 (＇ 1)) ↑ Conv.unseal 1 ★

P₇-two-seal-state-gate : P₇ ≡ P-two-seal-result-context
P₇-two-seal-state-gate = refl

P₇-two-seal-skeleton-gate :
  RC.skeleton P₇ ≡ RC.skeleton P.two-seal-result-context
P₇-two-seal-skeleton-gate = refl

------------------------------------------------------------------------
-- Initial closed relation Pᶜ ⊑ Qᶜ
------------------------------------------------------------------------

W₀ : World 0 0 0
W₀ = CPI2.initialWorld I.idᵐ store-empty

★⊑★² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → ★ ⊑ᵂ⟨ W ⟩ ★
★⊑★² = I.★⊑★

★⇒★⊑★⇒★² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → (★ ⇒ ★) ⊑ᵂ⟨ W ⟩ (★ ⇒ ★)
★⇒★⊑★⇒★² = I.⇒⊑⇒ I.★⊑★ I.★⊑★

ℕ⊑ℕ² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → (‵ `ℕ) ⊑ᵂ⟨ W ⟩ (‵ `ℕ)
ℕ⊑ℕ² = I.ι⊑ι

ℕ⊑★² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → (‵ `ℕ) ⊑ᵂ⟨ W ⟩ ★
ℕ⊑★² = I.ι⊑★

X⊑★² : ∀ {Δᴸ Δᴿ Δ} {W : World (suc Δᴸ) Δᴿ (suc Δ)}
  → ＇ Fin.zero ⊑ᵂ⟨ CTI2.liftWorldLeft I.X⊑★ W ⟩ ★
X⊑★² = I.X⊑★ refl

★⊑★₀ : ★ ⊑ᵂ⟨ W₀ ⟩ ★
★⊑★₀ = I.★⊑★

ℕ⊑ℕ₀ : ℕ₀ ⊑ᵂ⟨ W₀ ⟩ ℕ₀
ℕ⊑ℕ₀ = I.ι⊑ι

ℕ⊑★₀ : ℕ₀ ⊑ᵂ⟨ W₀ ⟩ ★
ℕ⊑★₀ = I.ι⊑★

★⇒★⊑★⇒★₀ : (★ ⇒ ★) ⊑ᵂ⟨ W₀ ⟩ (★ ⇒ ★)
★⇒★⊑★⇒★₀ = I.⇒⊑⇒ I.★⊑★ I.★⊑★

∀X⇒X⊑★⇒★₀ : `∀ X⇒X ⊑ᵂ⟨ W₀ ⟩ (★ ⇒ ★)
∀X⇒X⊑★⇒★₀ =
  I.∀⊑ nonvar-fun (∈-fun-left var-∈)
    (I.⇒⊑⇒ (I.X⊑★ refl) (I.X⊑★ refl))

private
  W₁ : World 1 0 1
  W₁ = CTI2.liftWorldLeft I.X⊑★ W₀

  W₂ : World 2 0 2
  W₂ = CTI2.liftWorldLeft I.X⊑★ W₁

  X⊑★₁ : ＇ Fin.zero ⊑ᵂ⟨ W₁ ⟩ ★
  X⊑★₁ = I.X⊑★ refl

  X⇒X⊑★⇒★₁ : X⇒X ⊑ᵂ⟨ W₁ ⟩ (★ ⇒ ★)
  X⇒X⊑★⇒★₁ = I.⇒⊑⇒ X⊑★₁ X⊑★₁

  ∀X⇒X⊑★⇒★₁ : `∀ X⇒X ⊑ᵂ⟨ W₁ ⟩ (★ ⇒ ★)
  ∀X⇒X⊑★⇒★₁ =
    I.∀⊑ nonvar-fun (∈-fun-left var-∈)
      (I.⇒⊑⇒ (I.X⊑★ refl) (I.X⊑★ refl))

  ∀X⇒X⊑∀X⇒X₁ : `∀ X⇒X ⊑ᵂ⟨ W₁ ⟩ `∀ X⇒X
  ∀X⇒X⊑∀X⇒X₁ =
    I.∀⊑∀ (I.⇒⊑⇒ I.X⊑X I.X⊑X)

  X⊑★₂ : ＇ Fin.zero ⊑ᵂ⟨ W₂ ⟩ ★
  X⊑★₂ = I.X⊑★ refl

  outerCtx⊑₂ : ⇑ᵗ (＇ Fin.zero) ⊑ᵂ⟨ W₂ ⟩ ★
  outerCtx⊑₂ = I.X⊑★ refl

  X⇒X⊑★⇒★₂ : X⇒X ⊑ᵂ⟨ W₂ ⟩ (★ ⇒ ★)
  X⇒X⊑★⇒★₂ = I.⇒⊑⇒ X⊑★₂ X⊑★₂

  innerId-body⊑dynId-body :
    W₂ ∣ ctx-imp (＇ Fin.zero) ★ X⊑★₂ ∷
      ctx-imp (⇑ᵗ (＇ Fin.zero)) ★ outerCtx⊑₂ ∷ [] ⊢²
      ` 0 ⊑ ` 0 ∶ X⊑★₂
  innerId-body⊑dynId-body = x⊑x² CTI2.Zʷ

  innerId-λ⊑dynId-λ :
    W₂ ∣ ctx-imp (⇑ᵗ (＇ Fin.zero)) ★ outerCtx⊑₂ ∷ [] ⊢²
      ƛ (` 0) ⊑ dynIdᶜ ∶ X⇒X⊑★⇒★₂
  innerId-λ⊑dynId-λ = ƛ⊑ƛ² innerId-body⊑dynId-body

  innerId⊑dynId :
    W₁ ∣ ctx-imp (＇ Fin.zero) ★ X⊑★₁ ∷ [] ⊢²
      Λ (ƛ (` 0)) ⊑ dynIdᶜ ∶ ∀X⇒X⊑★⇒★₁
  innerId⊑dynId =
    Λ⊑² nonvar-fun (∈-fun-left var-∈) (liftᴸ-∷ liftᴸ-[])
      (ƛ (` 0)) (⊢ƛ (⊢` Z))
      innerId-λ⊑dynId-λ ∀X⇒X⊑★⇒★₁

  innerId⊑genDynId :
    W₁ ∣ ctx-imp (＇ Fin.zero) ★ X⊑★₁ ∷ [] ⊢²
      Λ (ƛ (` 0)) ⊑ genDynIdᶜ ∶ ∀X⇒X⊑∀X⇒X₁
  innerId⊑genDynId =
    ⊑cast² ★⇒★∼∀X⇒X innerId⊑dynId ∀X⇒X⊑∀X⇒X₁

  innerCallee⊑ :
    W₁ ∣ ctx-imp (＇ Fin.zero) ★ X⊑★₁ ∷ [] ⊢²
      (innerIdᶜ ⦂∀ X⇒X [ ＇ Fin.zero ])
      ⊑ (genDynIdᶜ ⦂∀ X⇒X [ ★ ]) ∶ X⇒X⊑★⇒★₁
  innerCallee⊑ =
    •⊑•² ∀X⇒X⊑∀X⇒X₁ innerId⊑genDynId X⊑★₁
      X⇒X⊑★⇒★₁

  innerArg⊑ :
    W₁ ∣ ctx-imp (＇ Fin.zero) ★ X⊑★₁ ∷ [] ⊢²
      (` 0 ⟨ id {μ = idᶜ {Δ = 1}} (＇ Fin.zero) ⟩)
      ⊑ (` 0 ⟨ id {μ = idᶜ {Δ = 0}} ★ ⟩) ∶ X⊑★₁
  innerArg⊑ =
    cast⊑cast² (id {μ = idᶜ {Δ = 1}} (＇ Fin.zero))
      (id {μ = idᶜ {Δ = 0}} ★) (x⊑x² CTI2.Zʷ) X⊑★₁

  outerBody⊑ :
    W₁ ∣ ctx-imp (＇ Fin.zero) ★ X⊑★₁ ∷ [] ⊢²
      PBodyᶜ ⊑ QBodyᶜ ∶ X⊑★₁
  outerBody⊑ = ·⊑·² innerCallee⊑ innerArg⊑

  outerLamBody⊑ :
    W₁ ∣ [] ⊢²
      ƛ PBodyᶜ ⊑ QFunᶜ ∶ X⇒X⊑★⇒★₁
  outerLamBody⊑ = ƛ⊑ƛ² outerBody⊑

  outerPoly⊑QFun :
    W₀ ∣ [] ⊢²
      PFunᶜ ⊑ QFunᶜ ∶ ∀X⇒X⊑★⇒★₀
  outerPoly⊑QFun =
    Λ⊑² nonvar-fun (∈-fun-left var-∈) liftᴸ-[]
      (ƛ _)
      (⊢ƛ
        (⊢·
          (⊢•
            (⊢⟨⟩ (⊢ƛ (⊢` Z)) ★⇒★∼∀X⇒X))
          (⊢⟨⟩ (⊢` Z) (id {μ = idᶜ {Δ = 0}} ★))))
      outerLamBody⊑ ∀X⇒X⊑★⇒★₀

  outerCallee⊑ :
    W₀ ∣ [] ⊢²
      PCalleeᶜ ⊑ QFunᶜ ∶ ★⇒★⊑★⇒★₀
  outerCallee⊑ =
    •⊑² ∀X⇒X⊑★⇒★₀ outerPoly⊑QFun ★⊑★₀ ★⇒★⊑★⇒★₀

  closedArg⊑ :
    W₀ ∣ [] ⊢²
      taggedZeroᶜ ⊑ taggedZeroᶜ ∶ ★⊑★₀
  closedArg⊑ =
    cast⊑cast² ℕ! ℕ! (κ⊑κ² (κℕ 0) ℕ⊑ℕ₀) ★⊑★₀

initial-PLocalᶜ⊑Qᶜ :
  W₀ ∣ [] ⊢² PLocalᶜ ⊑ Qᶜ ∶ ★⊑★₀
initial-PLocalᶜ⊑Qᶜ = ·⊑·² outerCallee⊑ closedArg⊑

initial-Pᶜ⊑Qᶜ :
  W₀ ∣ [] ⊢² Pᶜ ⊑ Qᶜ ∶ ★⊑★₀
initial-Pᶜ⊑Qᶜ = initial-PLocalᶜ⊑Qᶜ

------------------------------------------------------------------------
-- Mid-simulation instance from the reached states
------------------------------------------------------------------------

mid-output :
  Probe.W ∣ [] ⊢² Probe.M ⊑ Probe.target-sealed ∶ Probe.q
mid-output = Probe.output

mid-input :
  Probe.W ∣ [] ⊢² Probe.M ⊑ Probe.N ∶ Probe.input-type
mid-input = Probe.input

mid-q : ＇ Fin.zero ⊑ᵂ⟨ Probe.W ⟩ ＇ Fin.zero
mid-q = Probe.q

left-walk-input-skeleton-gate :
  RC.skeleton P-two-seal-arg ≡ RC.skeleton Probe.M
left-walk-input-skeleton-gate = refl

right-walk-input-skeleton-gate :
  RC.skeleton Q-generated-tagged-input ≡ RC.skeleton Probe.N
right-walk-input-skeleton-gate = refl
