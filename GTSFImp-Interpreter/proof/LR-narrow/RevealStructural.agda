module proof.LR-narrow.RevealStructural where

-- File Charter:
--   * The structural reveal and conceal compatibility at a paired
--     semantic slot, by strong induction on the step index, for the
--     fragment of center imprecision derivations without one-sided
--     universal wrappers (`RevealSafe`).
--   * The function case decomposes the revealed function's application
--     into the argument conceal, the application, and the result reveal,
--     composed under the argument and reveal frames.
--   * The universal case is handled in the paired-allocation form.

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s; _∸_)
open import Data.Nat.Properties using
  (n≤1+n; ≤-trans; ≤-refl; <-wellFounded; m∸n≤m)
open import Data.Nat.Induction using () renaming (<-wellFounded to wf)
open import Induction.WellFounded using (Acc; acc)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion using
  (Conv↑; Conv↓; unseal; seal; _↦↑_; _↦↓_; `∀↑_; `∀↓_; id↑; id↓;
   rename↑; rename↓; replaceTy; 〖_,_↑_〗; makeConceal)
open import Consistency using (toRenameᵗ)
import Imprecision as I
open import Reduction
import Eval as E
open import Interpreter
open import proof.ImprecisionConsistency using
  (toRenameᵗ-injective; renameᵗ-injective)
open import proof.TypeSafety.Preservation using
  (structural-reveal-typing; structural-conceal-typing)
open import proof.TypeInTermSubst using (toRename-wk-eq; renameᵗ-id)
open import proof.LR-narrow.TypeRenamingComposition using
  (Packed↑; Packed↓; pack↑; pack↓; apply↑; apply↓)
open import proof.LR-narrow.TermRenamingComposition using
  (reveal-pointwise; conceal-pointwise)
open import proof.LR-narrow.TypeRenamingComposition using
  (pack-↦↑; pack-↦↓; pack-∀↑; pack-∀↓)
import Data.Fin as Fin
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure using (value-imprecision-downward-to)
import proof.LR-narrow.Closure as ClosureProof
open import proof.LR-narrow.ImmediateReturn using
  (related-values-return)
open import proof.LR-narrow.StepExpansion using
  (related-pure-step-expand)
open import proof.LR-narrow.CastComposition using
  (computations-related-future-compose)
open import proof.LR-narrow.FramePhases
open import proof.LR-narrow.FrameComposition
open import proof.LR-narrow.RevealFrames
open import proof.LR-narrow.RevealSteps
open import proof.LR-narrow.RevealLifting
open import proof.LR-narrow.ArgumentFrame using
  (related-application-computation)
import proof.LR-narrow.RevealAtomic as RA
import proof.LR-narrow.ConcealAtomic as CA
open RA using
  (AtomicReveal; atomic-★; atomic-ι; atomic-X; atomic-ι★; atomic-X★;
   rename-base-injective; rename-star-injective; rename-variable-inversion)

------------------------------------------------------------------------
-- The fragment
------------------------------------------------------------------------

-- Center imprecision derivations whose reveal wrappers are paired on
-- both endpoints: no universal under a `⊑ ★` form, no one-sided
-- universal.  (See FUNDAMENTAL-PROPERTY-PLAN.md, Finding C.)

data RevealSafe {Δ} {μ : I.ImpEnv Δ} :
    ∀ {A B : Ty Δ} → μ I.⊢ A ⊑ B → Set where
  safe-atomic : ∀ {A B} {p : μ I.⊢ A ⊑ B}
    → AtomicReveal p → RevealSafe p
  safe-⇒⊑⇒ : ∀ {A A′ B B′} {p : μ I.⊢ A ⊑ A′} {q : μ I.⊢ B ⊑ B′}
    → RevealSafe p → RevealSafe q → RevealSafe (I.⇒⊑⇒ p q)
  safe-∀⊑∀ : ∀ {A B} {p : I.extᵐ μ I.⊢ A ⊑ B}
    → RevealSafe p → RevealSafe (I.∀⊑∀ p)
  safe-bot-elim : RevealSafe I.bot-elim
  safe-bot⊑★ : RevealSafe I.bot⊑★

------------------------------------------------------------------------
-- Inversions
------------------------------------------------------------------------

rename-arrow-inversion : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {A : Ty Δ} {A₁ A₂}
  → renameᵗ ρ A ≡ A₁ ⇒ A₂
  → Σ[ B₁ ∈ Ty Δ ] Σ[ B₂ ∈ Ty Δ ]
      (A ≡ B₁ ⇒ B₂) × (renameᵗ ρ B₁ ≡ A₁) × (renameᵗ ρ B₂ ≡ A₂)
rename-arrow-inversion ρ {A = ＇ X} ()
rename-arrow-inversion ρ {A = ‵ ι} ()
rename-arrow-inversion ρ {A = ★} ()
rename-arrow-inversion ρ {A = B₁ ⇒ B₂} refl = B₁ , B₂ , refl , refl , refl
rename-arrow-inversion ρ {A = `∀ A} ()

rename-universal-inversion : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {A : Ty Δ} {A₁}
  → renameᵗ ρ A ≡ `∀ A₁
  → Σ[ B₁ ∈ Ty (suc Δ) ] (A ≡ `∀ B₁) × (renameᵗ (extᵗ ρ) B₁ ≡ A₁)
rename-universal-inversion ρ {A = ＇ X} ()
rename-universal-inversion ρ {A = ‵ ι} ()
rename-universal-inversion ρ {A = ★} ()
rename-universal-inversion ρ {A = A ⇒ B} ()
rename-universal-inversion ρ {A = `∀ B₁} refl = B₁ , refl , refl

data ArrowImprecision {Δ} {μ : I.ImpEnv Δ} {A₁ A₂ B₁ B₂ : Ty Δ} :
    μ I.⊢ A₁ ⇒ A₂ ⊑ B₁ ⇒ B₂ → Set where
  arrow-imprecision : (q₁ : μ I.⊢ A₁ ⊑ B₁) (q₂ : μ I.⊢ A₂ ⊑ B₂)
    → ArrowImprecision (I.⇒⊑⇒ q₁ q₂)

arrow-imprecision-view : ∀ {Δ} {μ : I.ImpEnv Δ} {A₁ A₂ B₁ B₂ : Ty Δ}
  → (q : μ I.⊢ A₁ ⇒ A₂ ⊑ B₁ ⇒ B₂) → ArrowImprecision q
arrow-imprecision-view (I.⇒⊑⇒ q₁ q₂) = arrow-imprecision q₁ q₂

reveal-injective : ∀ {Δ} {M M′ : Term Δ} {A B A′ B′ : Ty Δ}
    {c : Conv↑ Δ A B} {c′ : Conv↑ Δ A′ B′}
  → (M ↑ c) ≡ (M′ ↑ c′)
  → pack↑ c ≡ pack↑ c′
reveal-injective refl = refl

liftPreciseTy-arrow : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (A B : Ty Δᴾ)
  → liftPreciseTy W≼W′ (A ⇒ B)
      ≡ liftPreciseTy W≼W′ A ⇒ liftPreciseTy W≼W′ B
liftPreciseTy-arrow future-refl A B = refl
liftPreciseTy-arrow (future-paired W≼W′ r) A B
    rewrite liftPreciseTy-arrow W≼W′ A B = refl
liftPreciseTy-arrow (future-precise W≼W′ r) A B
    rewrite liftPreciseTy-arrow W≼W′ A B = refl
liftPreciseTy-arrow (future-imprecise W≼W′) A B =
  liftPreciseTy-arrow W≼W′ A B

liftImpreciseTy-arrow : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (A B : Ty Δᴵ)
  → liftImpreciseTy W≼W′ (A ⇒ B)
      ≡ liftImpreciseTy W≼W′ A ⇒ liftImpreciseTy W≼W′ B
liftImpreciseTy-arrow future-refl A B = refl
liftImpreciseTy-arrow (future-paired W≼W′ r) A B
    rewrite liftImpreciseTy-arrow W≼W′ A B = refl
liftImpreciseTy-arrow (future-precise W≼W′ r) A B =
  liftImpreciseTy-arrow W≼W′ A B
liftImpreciseTy-arrow (future-imprecise W≼W′) A B
    rewrite liftImpreciseTy-arrow W≼W′ A B = refl

------------------------------------------------------------------------
-- Transported reveal frames are applied store changes
------------------------------------------------------------------------

open Frame revealFrame using () renaming (transports to transports↑)

ext-id : ∀ {Δ} (X : TyVar (suc Δ)) → extᵗ (λ Y → Y) X ≡ X
ext-id Fin.zero = refl
ext-id (Fin.suc X) = refl

mutual
  rename↑-identity : ∀ {Δ} {A B : Ty Δ} (c : Conv↑ Δ A B)
    → pack↑ (rename↑ (λ X → X) c) ≡ pack↑ c
  rename↑-identity (unseal X R) rewrite renameᵗ-id R = refl
  rename↑-identity (c ↦↑ d) =
    cong₂ pack-↦↑ (rename↓-identity c) (rename↑-identity d)
  rename↑-identity (`∀↑ c) =
    cong pack-∀↑
      (trans (reveal-pointwise (extᵗ (λ X → X)) (λ X → X) ext-id c)
        (rename↑-identity c))
  rename↑-identity (id↑ A) rewrite renameᵗ-id A = refl

  rename↓-identity : ∀ {Δ} {A B : Ty Δ} (c : Conv↓ Δ A B)
    → pack↓ (rename↓ (λ X → X) c) ≡ pack↓ c
  rename↓-identity (seal X R) rewrite renameᵗ-id R = refl
  rename↓-identity (c ↦↓ d) =
    cong₂ pack-↦↓ (rename↑-identity c) (rename↓-identity d)
  rename↓-identity (`∀↓ c) =
    cong pack-∀↓
      (trans (conceal-pointwise (extᵗ (λ X → X)) (λ X → X) ext-id c)
        (rename↓-identity c))
  rename↓-identity (id↓ A) rewrite renameᵗ-id A = refl

apply-change-reveal : ∀ {Δ Δ′} (χ : StoreChange Δ Δ′) (M : Term Δ)
    {A B : Ty Δ} (d : Conv↑ Δ A B)
  → χ ▷ᵀ (M ↑ d) ≡ (χ ▷ᵀ M) ↑ rename↑ (λ X → χ ▷ᵛ X) d
apply-change-reveal keep M d =
  cong (apply↑ M) (sym (rename↑-identity d))
apply-change-reveal (bind A) M d =
  cong (apply↑ (⇑ᵗᵐ M))
    (reveal-pointwise (toRenameᵗ Consistency.wk↪ᵗ) (λ X → Fin.suc X)
      toRename-wk-eq d)

apply-changes-reveal : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′) (M : Term Δ)
    {A B : Ty Δ} (d : Conv↑ Δ A B)
  → χs ▶ᵀ (M ↑ d)
      ≡ Frame.plug revealFrame (transports↑ χs (reveal-frm d)) (χs ▶ᵀ M)
apply-changes-reveal [] M d = refl
apply-changes-reveal (χ ∷ χs) M d
    rewrite apply-change-reveal χ M d =
  apply-changes-reveal χs (χ ▷ᵀ M) (rename↑ (λ X → χ ▷ᵛ X) d)

-- Under the future lifting of terms, a transported structural reveal is
-- the structural reveal at the lifted slot data.

transported-reveal-eq : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′)
    (M : Term Δ) (X : TyVar Δ) (R B : Ty Δ)
    {X′ : TyVar Δ′} {R′ B′ : Ty Δ′}
  → χs ▶ᵀ (M ↑ 〖 X , R ↑ B 〗) ≡ (χs ▶ᵀ M) ↑ 〖 X′ , R′ ↑ B′ 〗
  → ∀ (U : Term Δ′)
  → Frame.plug revealFrame (transports↑ χs (reveal-frm 〖 X , R ↑ B 〗)) U
      ≡ U ↑ 〖 X′ , R′ ↑ B′ 〗
transported-reveal-eq χs M X R B lifted U =
  cong (apply↑ U)
    (reveal-injective
      (trans (sym (apply-changes-reveal χs M 〖 X , R ↑ B 〗)) lifted))

------------------------------------------------------------------------
-- Safety is preserved by center renaming and lifting
------------------------------------------------------------------------

open import proof.ImprecisionConsistency using
  (rename-⊑; rename-star-map-ext; fin-suc-injective; ext-injective)

atomic-rename : ∀ {Δ Δ′} (μ : I.ImpEnv Δ) (μ′ : I.ImpEnv Δ′)
    {A B : Ty Δ} (ρ : Δ ⇒ʳ Δ′) (injective : ∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
    (h : ∀ X → μ X ≡ I.X⊑★ → μ′ (ρ X) ≡ I.X⊑★)
    {p : μ I.⊢ A ⊑ B}
  → AtomicReveal p
  → AtomicReveal (rename-⊑ {μ = μ} {μ′ = μ′} ρ injective h p)
atomic-rename μ μ′ ρ injective h atomic-★ = atomic-★
atomic-rename μ μ′ ρ injective h atomic-ι = atomic-ι
atomic-rename μ μ′ ρ injective h atomic-X = atomic-X
atomic-rename μ μ′ ρ injective h atomic-ι★ = atomic-ι★
atomic-rename μ μ′ ρ injective h (atomic-X★ eq) = atomic-X★ (h _ eq)

safe-rename : ∀ {Δ Δ′} (μ : I.ImpEnv Δ) (μ′ : I.ImpEnv Δ′)
    {A B : Ty Δ} (ρ : Δ ⇒ʳ Δ′) (injective : ∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
    (h : ∀ X → μ X ≡ I.X⊑★ → μ′ (ρ X) ≡ I.X⊑★)
    {p : μ I.⊢ A ⊑ B}
  → RevealSafe p
  → RevealSafe (rename-⊑ {μ = μ} {μ′ = μ′} ρ injective h p)
safe-rename μ μ′ ρ injective h (safe-atomic a) =
  safe-atomic (atomic-rename μ μ′ ρ injective h a)
safe-rename μ μ′ ρ injective h (safe-⇒⊑⇒ sp sq) =
  safe-⇒⊑⇒ (safe-rename μ μ′ ρ injective h sp)
    (safe-rename μ μ′ ρ injective h sq)
safe-rename μ μ′ ρ injective h (safe-∀⊑∀ sp) =
  safe-∀⊑∀ (safe-rename (I.extᵐ μ) (I.extᵐ μ′) (extᵗ ρ)
    (ext-injective injective) (rename-star-map-ext ρ h) sp)
safe-rename μ μ′ ρ injective h safe-bot-elim = safe-bot-elim
safe-rename μ μ′ ρ injective h safe-bot⊑★ = safe-bot⊑★

safe-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {Aᴾ Aᴵ : Ty Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
  → RevealSafe p → RevealSafe (liftCenterImprecision W≼W′ p)
safe-lift future-refl sp = sp
safe-lift (future-paired {W′ = W₁} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} W≼W₁ r) sp =
  safe-rename (impEnv (core W₁))
    (impEnv (core (pairedBindWorld W₁ Aᴾ Aᴵ r)))
    Fin.suc fin-suc-injective (λ X eq → eq) (safe-lift W≼W₁ sp)
safe-lift (future-precise {W′ = W₁} {Aᴾ = Aᴾ} W≼W₁ r) sp =
  safe-rename (impEnv (core W₁))
    (impEnv (core (preciseBindWorld W₁ Aᴾ r)))
    Fin.suc fin-suc-injective (λ X eq → eq) (safe-lift W≼W₁ sp)
safe-lift (future-imprecise {W′ = W₁} {Aᴵ = Aᴵ} W≼W₁) sp =
  safe-rename (impEnv (core W₁))
    (impEnv (core (impreciseBindWorld W₁ Aᴵ)))
    Fin.suc fin-suc-injective (λ X eq → eq) (safe-lift W≼W₁ sp)

------------------------------------------------------------------------
-- Statements
------------------------------------------------------------------------

slotXᴾ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} → PairedSlot W → TyVar Δᴾ
slotXᴾ s = preciseVariable (atom s)

slotXᴵ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} → PairedSlot W → TyVar Δᴵ
slotXᴵ s = impreciseVariable (atom s)

slotRᴾ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} → PairedSlot W → Ty Δᴾ
slotRᴾ s = preciseRep (atom s)

slotRᴵ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} → PairedSlot W → Ty Δᴵ
slotRᴵ s = impreciseRep (atom s)

RevealAt : ℕ → Set₁
RevealAt k = ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
    {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → RevealSafe p
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → ∀ {Cᴾ Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ) ≡ Cᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) ≡ Cᴵ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation q) k
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗)
      (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)

ConcealAt : ℕ → Set₁
ConcealAt k = ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
    {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → RevealSafe p
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → ∀ {Cᴾ Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ) ≡ Cᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) ≡ Cᴵ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W q k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ)
      (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ)

Below : ℕ → Set₁
Below k = ∀ j → j < k → RevealAt j × ConcealAt j

------------------------------------------------------------------------
-- No bottom-typed values
------------------------------------------------------------------------

open import proof.TypeSafety.Progress using (no-bot-value)

no-precise-bottom-value : ∀ {Δᴾ Δᴵ Δᶜ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ (`∀ (＇ Fin.zero)) ⊑ Aᴵ}
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ⊥
no-precise-bottom-value {W = W} related =
  no-bot-value (precise-value endpoints) Vᴾ⊢bot
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

  precise-type-eq : preciseType endpoints ≡ `∀ (＇ Fin.zero)
  precise-type-eq = renameᵗ-injective
    (toRenameᵗ-injective (preciseEmbedding (core W)))
    (preciseEmbedded endpoints)

  Vᴾ⊢bot = subst≡
    (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    precise-type-eq (precise-typed endpoints)

------------------------------------------------------------------------
-- Typed endpoints of revealed and concealed values
------------------------------------------------------------------------

revealed-endpoints : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → ∀ {Cᴾ Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ) ≡ Cᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) ≡ Cᴵ
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → Value (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗)
  → Value (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)
  → TypedEndpoints W q
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗)
      (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)
revealed-endpoints W s {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} p sourceᴾ sourceᴵ q
    targetᴾ targetᴵ related vᴵ vᴾ =
  typed-endpoints _ _ targetᴵ targetᴾ vᴵ vᴾ
    (⊢reveal (structural-reveal-typing Bᴵ (impreciseBound (atom s)))
      Vᴵ⊢Bᴵ)
    (⊢reveal (structural-reveal-typing Bᴾ (preciseBound (atom s)))
      Vᴾ⊢Bᴾ)
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

  Vᴾ⊢Bᴾ = subst≡
    (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    (renameᵗ-injective (toRenameᵗ-injective (preciseEmbedding (core W)))
      (trans (preciseEmbedded endpoints) (sym sourceᴾ)))
    (precise-typed endpoints)

  Vᴵ⊢Bᴵ = subst≡
    (λ A → ⟨ _ , impreciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    (renameᵗ-injective
      (toRenameᵗ-injective (impreciseEmbedding (core W)))
      (trans (impreciseEmbedded endpoints) (sym sourceᴵ)))
    (imprecise-typed endpoints)

concealed-endpoints : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → ∀ {Cᴾ Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ) ≡ Cᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) ≡ Cᴵ
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W q k Vᴵ Vᴾ
  → Value (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ)
  → Value (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ)
  → TypedEndpoints W p
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ)
      (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ)
concealed-endpoints W s {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} p sourceᴾ sourceᴵ q
    targetᴾ targetᴵ related vᴵ vᴾ =
  typed-endpoints _ _ sourceᴵ sourceᴾ vᴵ vᴾ
    (⊢conceal (structural-conceal-typing Bᴵ (impreciseBound (atom s)))
      Vᴵ⊢Cᴵ)
    (⊢conceal (structural-conceal-typing Bᴾ (preciseBound (atom s)))
      Vᴾ⊢Cᴾ)
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

  Vᴾ⊢Cᴾ = subst≡
    (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    (renameᵗ-injective (toRenameᵗ-injective (preciseEmbedding (core W)))
      (trans (preciseEmbedded endpoints) (sym targetᴾ)))
    (precise-typed endpoints)

  Vᴵ⊢Cᴵ = subst≡
    (λ A → ⟨ _ , impreciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    (renameᵗ-injective
      (toRenameᵗ-injective (impreciseEmbedding (core W)))
      (trans (impreciseEmbedded endpoints) (sym targetᴵ)))
    (imprecise-typed endpoints)
