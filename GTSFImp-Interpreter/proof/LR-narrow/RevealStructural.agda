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
open import Relation.Nullary using (yes; no)
open import Data.Fin.Properties using (_≟_)

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

-- Center imprecision derivations built from the atomic forms by
-- function imprecision, plus the two bottom forms (which have no
-- precise values).  Universal imprecision is excluded: see
-- FUNDAMENTAL-PROPERTY-PLAN.md, Finding C.

data RevealSafe {Δ} {μ : I.ImpEnv Δ} :
    ∀ {A B : Ty Δ} → μ I.⊢ A ⊑ B → Set where
  safe-atomic : ∀ {A B} {p : μ I.⊢ A ⊑ B}
    → AtomicReveal p → RevealSafe p
  safe-⇒⊑⇒ : ∀ {A A′ B B′} {p : μ I.⊢ A ⊑ A′} {q : μ I.⊢ B ⊑ B′}
    → RevealSafe p → RevealSafe q → RevealSafe (I.⇒⊑⇒ p q)
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

open Frame concealFrame using () renaming (transports to transports↓)

apply-change-conceal : ∀ {Δ Δ′} (χ : StoreChange Δ Δ′) (M : Term Δ)
    {A B : Ty Δ} (d : Conv↓ Δ A B)
  → χ ▷ᵀ (M ↓ d) ≡ (χ ▷ᵀ M) ↓ rename↓ (λ X → χ ▷ᵛ X) d
apply-change-conceal keep M d =
  cong (apply↓ M) (sym (rename↓-identity d))
apply-change-conceal (bind A) M d =
  cong (apply↓ (⇑ᵗᵐ M))
    (conceal-pointwise (toRenameᵗ Consistency.wk↪ᵗ) (λ X → Fin.suc X)
      toRename-wk-eq d)

apply-changes-conceal : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′) (M : Term Δ)
    {A B : Ty Δ} (d : Conv↓ Δ A B)
  → χs ▶ᵀ (M ↓ d)
      ≡ Frame.plug concealFrame (transports↓ χs (conceal-frm d))
          (χs ▶ᵀ M)
apply-changes-conceal [] M d = refl
apply-changes-conceal (χ ∷ χs) M d
    rewrite apply-change-conceal χ M d =
  apply-changes-conceal χs (χ ▷ᵀ M) (rename↓ (λ X → χ ▷ᵛ X) d)

conceal-injective : ∀ {Δ} {M M′ : Term Δ} {A B A′ B′ : Ty Δ}
    {c : Conv↓ Δ A B} {c′ : Conv↓ Δ A′ B′}
  → (M ↓ c) ≡ (M′ ↓ c′)
  → pack↓ c ≡ pack↓ c′
conceal-injective refl = refl

transported-conceal-eq : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′)
    (M : Term Δ) (X : TyVar Δ) (R B : Ty Δ)
    {X′ : TyVar Δ′} {R′ B′ : Ty Δ′}
  → χs ▶ᵀ (M ↓ makeConceal X R B)
      ≡ (χs ▶ᵀ M) ↓ makeConceal X′ R′ B′
  → ∀ (U : Term Δ′)
  → Frame.plug concealFrame
      (transports↓ χs (conceal-frm (makeConceal X R B))) U
      ≡ U ↓ makeConceal X′ R′ B′
transported-conceal-eq χs M X R B lifted U =
  cong (apply↓ U)
    (conceal-injective
      (trans (sym (apply-changes-conceal χs M (makeConceal X R B)))
        lifted))

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

------------------------------------------------------------------------
-- Revealing and concealing a related computation
------------------------------------------------------------------------

-- The slot data of a lifted slot.

slot-precise-variable-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (s : PairedSlot W) (W≼W′ : Future W W′)
  → slotXᴾ (slot-future s W≼W′)
      ≡ liftPreciseVariable W≼W′ (slotXᴾ s)
slot-precise-variable-lift s W≼W′ =
  lifted-precise-variable (slot-lift s W≼W′)

slot-imprecise-variable-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (s : PairedSlot W) (W≼W′ : Future W W′)
  → slotXᴵ (slot-future s W≼W′)
      ≡ liftImpreciseVariable W≼W′ (slotXᴵ s)
slot-imprecise-variable-lift s W≼W′ =
  lifted-imprecise-variable (slot-lift s W≼W′)

slot-precise-rep-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (s : PairedSlot W) (W≼W′ : Future W W′)
  → slotRᴾ (slot-future s W≼W′) ≡ liftPreciseTy W≼W′ (slotRᴾ s)
slot-precise-rep-lift s W≼W′ = lifted-precise-rep (slot-lift s W≼W′)

slot-imprecise-rep-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (s : PairedSlot W) (W≼W′ : Future W W′)
  → slotRᴵ (slot-future s W≼W′) ≡ liftImpreciseTy W≼W′ (slotRᴵ s)
slot-imprecise-rep-lift s W≼W′ = lifted-imprecise-rep (slot-lift s W≼W′)

-- The replaced type of a lifted slot is the lift of the replaced type.

replace-precise-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (s : PairedSlot W) (W≼W′ : Future W W′) (B : Ty Δᴾ)
  → replaceTy (slotXᴾ (slot-future s W≼W′))
      (slotRᴾ (slot-future s W≼W′)) (liftPreciseTy W≼W′ B)
    ≡ liftPreciseTy W≼W′ (replaceTy (slotXᴾ s) (slotRᴾ s) B)
replace-precise-lift s W≼W′ B =
  trans (cong₂ (λ X R → replaceTy X R (liftPreciseTy W≼W′ B))
    (slot-precise-variable-lift s W≼W′)
    (slot-precise-rep-lift s W≼W′))
    (sym (liftPreciseTy-replace W≼W′ (slotXᴾ s) (slotRᴾ s) B))

replace-imprecise-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (s : PairedSlot W) (W≼W′ : Future W W′) (B : Ty Δᴵ)
  → replaceTy (slotXᴵ (slot-future s W≼W′))
      (slotRᴵ (slot-future s W≼W′)) (liftImpreciseTy W≼W′ B)
    ≡ liftImpreciseTy W≼W′ (replaceTy (slotXᴵ s) (slotRᴵ s) B)
replace-imprecise-lift s W≼W′ B =
  trans (cong₂ (λ X R → replaceTy X R (liftImpreciseTy W≼W′ B))
    (slot-imprecise-variable-lift s W≼W′)
    (slot-imprecise-rep-lift s W≼W′))
    (sym (liftImpreciseTy-replace W≼W′ (slotXᴵ s) (slotRᴵ s) B))

-- The lifted structural reveal is the structural reveal at the lifted
-- slot and type.

lifted-reveal-precise : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (s : PairedSlot W) (W≼W′ : Future W W′) (V : Term Δᴾ) (B : Ty Δᴾ)
  → liftPreciseTerm W≼W′ (V ↑ 〖 slotXᴾ s , slotRᴾ s ↑ B 〗)
      ≡ liftPreciseTerm W≼W′ V
          ↑ 〖 slotXᴾ (slot-future s W≼W′)
              , slotRᴾ (slot-future s W≼W′)
              ↑ liftPreciseTy W≼W′ B 〗
lifted-reveal-precise s W≼W′ V B =
  trans (liftPreciseTerm-reveal W≼W′ V (slotXᴾ s) (slotRᴾ s) B)
    (cong (apply↑ (liftPreciseTerm W≼W′ V))
      (cong₂ (λ X R → pack↑ 〖 X , R ↑ liftPreciseTy W≼W′ B 〗)
        (sym (slot-precise-variable-lift s W≼W′))
        (sym (slot-precise-rep-lift s W≼W′))))

lifted-reveal-imprecise : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (s : PairedSlot W) (W≼W′ : Future W W′) (V : Term Δᴵ) (B : Ty Δᴵ)
  → liftImpreciseTerm W≼W′ (V ↑ 〖 slotXᴵ s , slotRᴵ s ↑ B 〗)
      ≡ liftImpreciseTerm W≼W′ V
          ↑ 〖 slotXᴵ (slot-future s W≼W′)
              , slotRᴵ (slot-future s W≼W′)
              ↑ liftImpreciseTy W≼W′ B 〗
lifted-reveal-imprecise s W≼W′ V B =
  trans (liftImpreciseTerm-reveal W≼W′ V (slotXᴵ s) (slotRᴵ s) B)
    (cong (apply↑ (liftImpreciseTerm W≼W′ V))
      (cong₂ (λ X R → pack↑ 〖 X , R ↑ liftImpreciseTy W≼W′ B 〗)
        (sym (slot-imprecise-variable-lift s W≼W′))
        (sym (slot-imprecise-rep-lift s W≼W′))))

lifted-conceal-precise : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (s : PairedSlot W) (W≼W′ : Future W W′) (V : Term Δᴾ) (B : Ty Δᴾ)
  → liftPreciseTerm W≼W′ (V ↓ makeConceal (slotXᴾ s) (slotRᴾ s) B)
      ≡ liftPreciseTerm W≼W′ V
          ↓ makeConceal (slotXᴾ (slot-future s W≼W′))
              (slotRᴾ (slot-future s W≼W′)) (liftPreciseTy W≼W′ B)
lifted-conceal-precise s W≼W′ V B =
  trans (liftPreciseTerm-conceal W≼W′ V (slotXᴾ s) (slotRᴾ s) B)
    (cong (apply↓ (liftPreciseTerm W≼W′ V))
      (cong₂ (λ X R →
          pack↓ (makeConceal X R (liftPreciseTy W≼W′ B)))
        (sym (slot-precise-variable-lift s W≼W′))
        (sym (slot-precise-rep-lift s W≼W′))))

lifted-conceal-imprecise : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (s : PairedSlot W) (W≼W′ : Future W W′) (V : Term Δᴵ) (B : Ty Δᴵ)
  → liftImpreciseTerm W≼W′ (V ↓ makeConceal (slotXᴵ s) (slotRᴵ s) B)
      ≡ liftImpreciseTerm W≼W′ V
          ↓ makeConceal (slotXᴵ (slot-future s W≼W′))
              (slotRᴵ (slot-future s W≼W′)) (liftImpreciseTy W≼W′ B)
lifted-conceal-imprecise s W≼W′ V B =
  trans (liftImpreciseTerm-conceal W≼W′ V (slotXᴵ s) (slotRᴵ s) B)
    (cong (apply↓ (liftImpreciseTerm W≼W′ V))
      (cong₂ (λ X R →
          pack↓ (makeConceal X R (liftImpreciseTy W≼W′ B)))
        (sym (slot-imprecise-variable-lift s W≼W′))
        (sym (slot-imprecise-rep-lift s W≼W′))))

-- Composition: revealing a related computation, given the value-level
-- reveal at every index up to the current one.

open Composition revealFrame revealFrame using ()
  renaming (frame-computations-related to reveal-computations-related;
            PlugValues to RevealPlugValues)
open Composition concealFrame concealFrame using ()
  renaming (frame-computations-related to conceal-computations-related;
            PlugValues to ConcealPlugValues)

revealed-computations : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → RevealSafe p
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → ∀ {Cᴾ Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ) ≡ Cᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) ≡ Cᴵ
  → ∀ {k : ℕ} (below : ∀ j → j ≤ k → RevealAt j)
      {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
  → ComputationsRelated W (FutureValueRelation p) k Mᴵ Mᴾ
  → ComputationsRelated W (FutureValueRelation q) k
      (Mᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗)
      (Mᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)
revealed-computations W s {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    p safe sourceᴾ sourceᴵ {Cᴾ = Cᴾ} {Cᴵ = Cᴵ} q targetᴾ targetᴵ
    {k = k} below {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} related =
  reveal-computations-related
    {R = FutureValueRelation p} {S = FutureValueRelation q}
    (reveal-frm 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)
    (reveal-frm 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗)
    k Mᴵ Mᴾ plug-values related
  where
  plug-values : RevealPlugValues W (FutureValueRelation p)
      (FutureValueRelation q) k
      (reveal-frm 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗)
      (reveal-frm 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗)
  plug-values {W′ = W′} W≼W′ {χsᴾ = χsᴾ} {χsᴵ = χsᴵ}
      storeᴵ storeᴾ termsᴵ termsᴾ {j = j} j≤k {Vᴵ = Uᴵ} {Vᴾ = Uᴾ}
      value-related =
    computations-related-future-compose W≼W′ q
      (ClosureProof.computations-related-reindex
        (liftCenterImprecision W≼W′ q) (liftCenterImprecision W≼W′ q)
        refl refl
        (sym (transported-reveal-eq χsᴵ Mᴵ (slotXᴵ s) (slotRᴵ s) Bᴵ
          (trans (termsᴵ (Mᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗))
            (trans (lifted-reveal-imprecise s W≼W′ Mᴵ Bᴵ)
              (cong (λ M → M ↑ _) (sym (termsᴵ Mᴵ))))) Uᴵ))
        (sym (transported-reveal-eq χsᴾ Mᴾ (slotXᴾ s) (slotRᴾ s) Bᴾ
          (trans (termsᴾ (Mᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Bᴾ 〗))
            (trans (lifted-reveal-precise s W≼W′ Mᴾ Bᴾ)
              (cong (λ M → M ↑ _) (sym (termsᴾ Mᴾ))))) Uᴾ))
        (below j j≤k W′ (slot-future s W≼W′)
          (liftCenterImprecision W≼W′ p) (safe-lift W≼W′ safe)
          (trans (embedPrecise-lift W≼W′ Bᴾ)
            (cong (liftCenterTy W≼W′) sourceᴾ))
          (trans (embedImprecise-lift W≼W′ Bᴵ)
            (cong (liftCenterTy W≼W′) sourceᴵ))
          (liftCenterImprecision W≼W′ q)
          (trans (cong (embedPrecise (core W′))
            (replace-precise-lift s W≼W′ Bᴾ))
            (trans (embedPrecise-lift W≼W′ _)
              (cong (liftCenterTy W≼W′) targetᴾ)))
          (trans (cong (embedImprecise (core W′))
            (replace-imprecise-lift s W≼W′ Bᴵ))
            (trans (embedImprecise-lift W≼W′ _)
              (cong (liftCenterTy W≼W′) targetᴵ)))
          value-related))

concealed-computations : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → RevealSafe p
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → ∀ {Cᴾ Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ) ≡ Cᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) ≡ Cᴵ
  → ∀ {k : ℕ} (below : ∀ j → j ≤ k → ConcealAt j)
      {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
  → ComputationsRelated W (FutureValueRelation q) k Mᴵ Mᴾ
  → ComputationsRelated W (FutureValueRelation p) k
      (Mᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ)
      (Mᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ)
concealed-computations W s {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    p safe sourceᴾ sourceᴵ {Cᴾ = Cᴾ} {Cᴵ = Cᴵ} q targetᴾ targetᴵ
    {k = k} below {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} related =
  conceal-computations-related
    {R = FutureValueRelation q} {S = FutureValueRelation p}
    (conceal-frm (makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ))
    (conceal-frm (makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ))
    k Mᴵ Mᴾ plug-values related
  where
  plug-values : ConcealPlugValues W (FutureValueRelation q)
      (FutureValueRelation p) k
      (conceal-frm (makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ))
      (conceal-frm (makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ))
  plug-values {W′ = W′} W≼W′ {χsᴾ = χsᴾ} {χsᴵ = χsᴵ}
      storeᴵ storeᴾ termsᴵ termsᴾ {j = j} j≤k {Vᴵ = Uᴵ} {Vᴾ = Uᴾ}
      value-related =
    computations-related-future-compose W≼W′ p
      (ClosureProof.computations-related-reindex
        (liftCenterImprecision W≼W′ p) (liftCenterImprecision W≼W′ p)
        refl refl
        (sym (transported-conceal-eq χsᴵ Mᴵ (slotXᴵ s) (slotRᴵ s) Bᴵ
          (trans (termsᴵ (Mᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ))
            (trans (lifted-conceal-imprecise s W≼W′ Mᴵ Bᴵ)
              (cong (λ M → M ↓ _) (sym (termsᴵ Mᴵ))))) Uᴵ))
        (sym (transported-conceal-eq χsᴾ Mᴾ (slotXᴾ s) (slotRᴾ s) Bᴾ
          (trans (termsᴾ (Mᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) Bᴾ))
            (trans (lifted-conceal-precise s W≼W′ Mᴾ Bᴾ)
              (cong (λ M → M ↓ _) (sym (termsᴾ Mᴾ))))) Uᴾ))
        (below j j≤k W′ (slot-future s W≼W′)
          (liftCenterImprecision W≼W′ p) (safe-lift W≼W′ safe)
          (trans (embedPrecise-lift W≼W′ Bᴾ)
            (cong (liftCenterTy W≼W′) sourceᴾ))
          (trans (embedImprecise-lift W≼W′ Bᴵ)
            (cong (liftCenterTy W≼W′) sourceᴵ))
          (liftCenterImprecision W≼W′ q)
          (trans (cong (embedPrecise (core W′))
            (replace-precise-lift s W≼W′ Bᴾ))
            (trans (embedPrecise-lift W≼W′ _)
              (cong (liftCenterTy W≼W′) targetᴾ)))
          (trans (cong (embedImprecise (core W′))
            (replace-imprecise-lift s W≼W′ Bᴵ))
            (trans (embedImprecise-lift W≼W′ _)
              (cong (liftCenterTy W≼W′) targetᴵ)))
          value-related))

------------------------------------------------------------------------
-- The function case
------------------------------------------------------------------------

-- One head of `FunctionsRelated` for a revealed function value: the
-- revealed application redistributes into a concealed argument, the
-- application, and a revealed result.

reveal-function-head : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Aᴾ₀ Bᴾ₀ : Ty Δᴾ} {Aᴵ₀ Bᴵ₀ : Ty Δᴵ}
    {Pᴾ Pᴵ Qᴾ Qᴵ : Ty Δᶜ}
    (p₁ : impEnv (core W) I.⊢ Pᴾ ⊑ Pᴵ)
    (p₂ : impEnv (core W) I.⊢ Qᴾ ⊑ Qᴵ)
  → RevealSafe p₁ → RevealSafe p₂
  → (sourceᴾ₁ : embedPrecise (core W) Aᴾ₀ ≡ Pᴾ)
  → (sourceᴵ₁ : embedImprecise (core W) Aᴵ₀ ≡ Pᴵ)
  → (sourceᴾ₂ : embedPrecise (core W) Bᴾ₀ ≡ Qᴾ)
  → (sourceᴵ₂ : embedImprecise (core W) Bᴵ₀ ≡ Qᴵ)
  → ∀ {Cᴾ Cᴵ Dᴾ Dᴵ : Ty Δᶜ}
      (q₁ : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
      (q₂ : impEnv (core W) I.⊢ Dᴾ ⊑ Dᴵ)
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Aᴾ₀) ≡ Cᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Aᴵ₀) ≡ Cᴵ
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ₀) ≡ Dᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ₀) ≡ Dᴵ
  → ∀ {k : ℕ}
      (revealBelow : ∀ j → j ≤ k → RevealAt j)
      (concealAt : ConcealAt k)
      {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.⇒⊑⇒ p₁ p₂) (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
  → ValueImprecision W′ (liftCenterImprecision W≼W′ q₁) (suc k) Uᴵ Uᴾ
  → ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc k)
      (liftImpreciseTerm W≼W′
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Aᴵ₀ ⇒ Bᴵ₀ 〗) · Uᴵ)
      (liftPreciseTerm W≼W′
        (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Aᴾ₀ ⇒ Bᴾ₀ 〗) · Uᴾ)
reveal-function-head W s {Aᴾ₀ = Aᴾ₀} {Bᴾ₀ = Bᴾ₀}
    {Aᴵ₀ = Aᴵ₀} {Bᴵ₀ = Bᴵ₀} {Pᴾ = Pᴾ} {Pᴵ = Pᴵ} {Qᴾ = Qᴾ} {Qᴵ = Qᴵ}
    p₁ p₂ safe₁ safe₂ sourceᴾ₁ sourceᴵ₁ sourceᴾ₂ sourceᴵ₂
    {Cᴾ = Cᴾ} {Cᴵ = Cᴵ} {Dᴾ = Dᴾ} {Dᴵ = Dᴵ} q₁ q₂
    targetᴾ₁ targetᴵ₁ targetᴾ₂ targetᴵ₂
    {k = k} revealBelow concealAt {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} function-related
    W′ W≼W′ {Uᴵ = Uᴵ} {Uᴾ = Uᴾ} argument-related =
  ClosureProof.computations-related-reindex
    (liftCenterImprecision W≼W′ q₂) (liftCenterImprecision W≼W′ q₂)
    refl refl (sym imprecise-redex-eq) (sym precise-redex-eq)
    expanded
  where
  s′ = slot-future s W≼W′
  Xᴾ′ = slotXᴾ s′
  Xᴵ′ = slotXᴵ s′
  Rᴾ′ = slotRᴾ s′
  Rᴵ′ = slotRᴵ s′

  Aᴾ′ = liftPreciseTy W≼W′ Aᴾ₀
  Bᴾ′ = liftPreciseTy W≼W′ Bᴾ₀
  Aᴵ′ = liftImpreciseTy W≼W′ Aᴵ₀
  Bᴵ′ = liftImpreciseTy W≼W′ Bᴵ₀

  cᴾ = makeConceal Xᴾ′ Rᴾ′ Aᴾ′
  dᴾ = 〖 Xᴾ′ , Rᴾ′ ↑ Bᴾ′ 〗
  cᴵ = makeConceal Xᴵ′ Rᴵ′ Aᴵ′
  dᴵ = 〖 Xᴵ′ , Rᴵ′ ↑ Bᴵ′ 〗

  Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
  Vᴵ′ = liftImpreciseTerm W≼W′ Vᴵ

  -- The lifted revealed value is the revealed lifted value.

  precise-redex-eq :
      liftPreciseTerm W≼W′ (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Aᴾ₀ ⇒ Bᴾ₀ 〗)
        · Uᴾ
      ≡ (Vᴾ′ ↑ (cᴾ ↦↑ dᴾ)) · Uᴾ
  precise-redex-eq
      rewrite lifted-reveal-precise s W≼W′ Vᴾ (Aᴾ₀ ⇒ Bᴾ₀)
            | liftPreciseTy-arrow W≼W′ Aᴾ₀ Bᴾ₀ = refl

  imprecise-redex-eq :
      liftImpreciseTerm W≼W′
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Aᴵ₀ ⇒ Bᴵ₀ 〗) · Uᴵ
      ≡ (Vᴵ′ ↑ (cᴵ ↦↑ dᴵ)) · Uᴵ
  imprecise-redex-eq
      rewrite lifted-reveal-imprecise s W≼W′ Vᴵ (Aᴵ₀ ⇒ Bᴵ₀)
            | liftImpreciseTy-arrow W≼W′ Aᴵ₀ Bᴵ₀ = refl

  source-endpoints =
    ClosureProof.value-imprecision-endpoints
      {W = W} {p = I.⇒⊑⇒ p₁ p₂} {k = suc k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
      function-related
  argument-endpoints =
    ClosureProof.value-imprecision-endpoints argument-related

  -- The lifted source function relation, with an explicit arrow.

  lifted-function : ValueImprecision W′
      (I.⇒⊑⇒ (liftCenterImprecision W≼W′ p₁)
        (liftCenterImprecision W≼W′ p₂)) k Vᴵ′ Vᴾ′
  lifted-function = ClosureProof.value-imprecision-reindex
    (I.⇒⊑⇒ (liftCenterImprecision W≼W′ p₁)
      (liftCenterImprecision W≼W′ p₂))
    (liftCenterImprecision W≼W′ (I.⇒⊑⇒ p₁ p₂))
    (sym (liftCenterTy-arrow W≼W′ Pᴾ Qᴾ))
    (sym (liftCenterTy-arrow W≼W′ Pᴵ Qᴵ))
    (ClosureProof.value-imprecision-future W≼W′
      (value-imprecision-downward-to (n≤1+n k) function-related))

  -- The concealed argument.

  concealed : ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ p₁)) k
      (Uᴵ ↓ cᴵ) (Uᴾ ↓ cᴾ)
  concealed = concealAt W′ s′
    (liftCenterImprecision W≼W′ p₁) (safe-lift W≼W′ safe₁)
    (trans (embedPrecise-lift W≼W′ Aᴾ₀)
      (cong (liftCenterTy W≼W′) sourceᴾ₁))
    (trans (embedImprecise-lift W≼W′ Aᴵ₀)
      (cong (liftCenterTy W≼W′) sourceᴵ₁))
    (liftCenterImprecision W≼W′ q₁)
    (trans (cong (embedPrecise (core W′))
      (replace-precise-lift s W≼W′ Aᴾ₀))
      (trans (embedPrecise-lift W≼W′ _)
        (cong (liftCenterTy W≼W′) targetᴾ₁)))
    (trans (cong (embedImprecise (core W′))
      (replace-imprecise-lift s W≼W′ Aᴵ₀))
      (trans (embedImprecise-lift W≼W′ _)
        (cong (liftCenterTy W≼W′) targetᴵ₁)))
    (value-imprecision-downward-to (n≤1+n k) argument-related)

  applied : ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ p₂)) k
      (Vᴵ′ · (Uᴵ ↓ cᴵ)) (Vᴾ′ · (Uᴾ ↓ cᴾ))
  applied = related-application-computation lifted-function concealed

  contracted : ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) k
      ((Vᴵ′ · (Uᴵ ↓ cᴵ)) ↑ dᴵ) ((Vᴾ′ · (Uᴾ ↓ cᴾ)) ↑ dᴾ)
  contracted = revealed-computations W′ s′
    (liftCenterImprecision W≼W′ p₂) (safe-lift W≼W′ safe₂)
    (trans (embedPrecise-lift W≼W′ Bᴾ₀)
      (cong (liftCenterTy W≼W′) sourceᴾ₂))
    (trans (embedImprecise-lift W≼W′ Bᴵ₀)
      (cong (liftCenterTy W≼W′) sourceᴵ₂))
    (liftCenterImprecision W≼W′ q₂)
    (trans (cong (embedPrecise (core W′))
      (replace-precise-lift s W≼W′ Bᴾ₀))
      (trans (embedPrecise-lift W≼W′ _)
        (cong (liftCenterTy W≼W′) targetᴾ₂)))
    (trans (cong (embedImprecise (core W′))
      (replace-imprecise-lift s W≼W′ Bᴵ₀))
      (trans (embedImprecise-lift W≼W′ _)
        (cong (liftCenterTy W≼W′) targetᴵ₂)))
    revealBelow applied

  expanded : ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc k)
      ((Vᴵ′ ↑ (cᴵ ↦↑ dᴵ)) · Uᴵ) ((Vᴾ′ ↑ (cᴾ ↦↑ dᴾ)) · Uᴾ)
  expanded
      with reveal-fun-app-step-question
             {Σ = impreciseStore (core W′)} cᴵ dᴵ
             (imprecise-value source-endpoints-lifted)
             (imprecise-value argument-endpoints)
         | reveal-fun-app-step-question
             {Σ = preciseStore (core W′)} cᴾ dᴾ
             (precise-value source-endpoints-lifted)
             (precise-value argument-endpoints)
    where
    source-endpoints-lifted =
      ClosureProof.value-imprecision-endpoints lifted-function
  expanded | vVᴵ , vUᴵ , step-eqᴵ | vVᴾ , vUᴾ , step-eqᴾ =
    related-pure-step-expand (λ ()) (λ ())
      (reveal-fun-app-value-none cᴵ dᴵ)
      (reveal-fun-app-value-none cᴾ dᴾ)
      (β-reveal-⇒ vVᴵ vUᴵ) (β-reveal-⇒ vVᴾ vUᴾ)
      step-eqᴵ step-eqᴾ contracted

reveal-function : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Aᴾ₀ Bᴾ₀ : Ty Δᴾ} {Aᴵ₀ Bᴵ₀ : Ty Δᴵ}
    {Pᴾ Pᴵ Qᴾ Qᴵ : Ty Δᶜ}
    (p₁ : impEnv (core W) I.⊢ Pᴾ ⊑ Pᴵ)
    (p₂ : impEnv (core W) I.⊢ Qᴾ ⊑ Qᴵ)
  → RevealSafe p₁ → RevealSafe p₂
  → (sourceᴾ₁ : embedPrecise (core W) Aᴾ₀ ≡ Pᴾ)
  → (sourceᴵ₁ : embedImprecise (core W) Aᴵ₀ ≡ Pᴵ)
  → (sourceᴾ₂ : embedPrecise (core W) Bᴾ₀ ≡ Qᴾ)
  → (sourceᴵ₂ : embedImprecise (core W) Bᴵ₀ ≡ Qᴵ)
  → ∀ {Cᴾ Cᴵ Dᴾ Dᴵ : Ty Δᶜ}
      (q₁ : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
      (q₂ : impEnv (core W) I.⊢ Dᴾ ⊑ Dᴵ)
  → (targetᴾ₁ :
      embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Aᴾ₀) ≡ Cᴾ)
  → (targetᴵ₁ :
      embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Aᴵ₀) ≡ Cᴵ)
  → (targetᴾ₂ :
      embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ₀) ≡ Dᴾ)
  → (targetᴵ₂ :
      embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ₀) ≡ Dᴵ)
  → ∀ {k : ℕ} (below : Below k) {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.⇒⊑⇒ p₁ p₂) k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation (I.⇒⊑⇒ q₁ q₂)) k
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Aᴵ₀ ⇒ Bᴵ₀ 〗)
      (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Aᴾ₀ ⇒ Bᴾ₀ 〗)
reveal-function W s {Aᴾ₀ = Aᴾ₀} {Bᴾ₀ = Bᴾ₀} {Aᴵ₀ = Aᴵ₀} {Bᴵ₀ = Bᴵ₀}
    p₁ p₂ safe₁ safe₂ sourceᴾ₁ sourceᴵ₁ sourceᴾ₂ sourceᴵ₂
    q₁ q₂ targetᴾ₁ targetᴵ₁ targetᴾ₂ targetᴵ₂
    {k = k} below {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related =
  related-values-return
    (imprecise-value endpoints ↑ fun) (precise-value endpoints ↑ fun)
    at-every-index
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

  reveal-endpoints : ∀ (j : ℕ)
    → TypedEndpoints W (I.⇒⊑⇒ q₁ q₂)
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Aᴵ₀ ⇒ Bᴵ₀ 〗)
        (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Aᴾ₀ ⇒ Bᴾ₀ 〗)
  reveal-endpoints j = revealed-endpoints W s (I.⇒⊑⇒ p₁ p₂)
    (cong₂ _⇒_ sourceᴾ₁ sourceᴾ₂) (cong₂ _⇒_ sourceᴵ₁ sourceᴵ₂)
    (I.⇒⊑⇒ q₁ q₂) (cong₂ _⇒_ targetᴾ₁ targetᴾ₂)
    (cong₂ _⇒_ targetᴵ₁ targetᴵ₂) related
    (imprecise-value endpoints ↑ fun) (precise-value endpoints ↑ fun)

  head-at : ∀ (j : ℕ) → suc j ≤ k
    → ValueImprecision W (I.⇒⊑⇒ p₁ p₂) (suc j) Vᴵ Vᴾ
    → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
        (W≼W′ : Future W W′) {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
    → ValueImprecision W′ (liftCenterImprecision W≼W′ q₁) (suc j) Uᴵ Uᴾ
    → ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc j)
        (liftImpreciseTerm W≼W′
          (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Aᴵ₀ ⇒ Bᴵ₀ 〗) · Uᴵ)
        (liftPreciseTerm W≼W′
          (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Aᴾ₀ ⇒ Bᴾ₀ 〗) · Uᴾ)
  head-at j sj≤k source-at = reveal-function-head W s p₁ p₂ safe₁ safe₂
    sourceᴾ₁ sourceᴵ₁ sourceᴾ₂ sourceᴵ₂ q₁ q₂
    targetᴾ₁ targetᴵ₁ targetᴾ₂ targetᴵ₂
    (λ i i≤j → proj₁ (below i (≤-trans (s≤s i≤j) sj≤k)))
    (proj₂ (below j sj≤k)) source-at

  functions-related : ∀ (j : ℕ) → suc j ≤ k
    → ValueImprecision W (I.⇒⊑⇒ p₁ p₂) (suc j) Vᴵ Vᴾ
    → FunctionsRelated W q₁ q₂ (suc j)
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Aᴵ₀ ⇒ Bᴵ₀ 〗)
        (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Aᴾ₀ ⇒ Bᴾ₀ 〗)
  functions-related zero sj≤k source-at =
    head-at zero sj≤k source-at , tt
  functions-related (suc j) sj≤k source-at =
    head-at (suc j) sj≤k source-at ,
    functions-related j (≤-trans (n≤1+n (suc j)) sj≤k)
      (value-imprecision-downward-to
        {W = W} {p = I.⇒⊑⇒ p₁ p₂} {j = suc j} {k = suc (suc j)}
        {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (n≤1+n (suc j)) source-at)

  at-every-index : ∀ (j : ℕ) → j ≤ k
    → FutureValueRelation (I.⇒⊑⇒ q₁ q₂) W future-refl j
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Aᴵ₀ ⇒ Bᴵ₀ 〗)
        (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ Aᴾ₀ ⇒ Bᴾ₀ 〗)
  at-every-index zero j≤k = reveal-endpoints zero
  at-every-index (suc j) sj≤k =
    reveal-endpoints (suc j) ,
    functions-related j sj≤k
      (value-imprecision-downward-to
        {W = W} {p = I.⇒⊑⇒ p₁ p₂} {j = suc j} {k = k}
        {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} sj≤k related)

------------------------------------------------------------------------
-- The conceal function case
------------------------------------------------------------------------

conceal-function-head : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Aᴾ₀ Bᴾ₀ : Ty Δᴾ} {Aᴵ₀ Bᴵ₀ : Ty Δᴵ}
    {Pᴾ Pᴵ Qᴾ Qᴵ : Ty Δᶜ}
    (p₁ : impEnv (core W) I.⊢ Pᴾ ⊑ Pᴵ)
    (p₂ : impEnv (core W) I.⊢ Qᴾ ⊑ Qᴵ)
  → RevealSafe p₁ → RevealSafe p₂
  → (sourceᴾ₁ : embedPrecise (core W) Aᴾ₀ ≡ Pᴾ)
  → (sourceᴵ₁ : embedImprecise (core W) Aᴵ₀ ≡ Pᴵ)
  → (sourceᴾ₂ : embedPrecise (core W) Bᴾ₀ ≡ Qᴾ)
  → (sourceᴵ₂ : embedImprecise (core W) Bᴵ₀ ≡ Qᴵ)
  → ∀ {Cᴾ Cᴵ Dᴾ Dᴵ : Ty Δᶜ}
      (q₁ : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
      (q₂ : impEnv (core W) I.⊢ Dᴾ ⊑ Dᴵ)
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Aᴾ₀) ≡ Cᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Aᴵ₀) ≡ Cᴵ
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ₀) ≡ Dᴾ
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ₀) ≡ Dᴵ
  → ∀ {k : ℕ}
      (revealAt : RevealAt k)
      (concealBelow : ∀ j → j ≤ k → ConcealAt j)
      {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.⇒⊑⇒ q₁ q₂) (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
  → ValueImprecision W′ (liftCenterImprecision W≼W′ p₁) (suc k) Uᴵ Uᴾ
  → ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ p₂)) (suc k)
      (liftImpreciseTerm W≼W′
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (Aᴵ₀ ⇒ Bᴵ₀)) · Uᴵ)
      (liftPreciseTerm W≼W′
        (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (Aᴾ₀ ⇒ Bᴾ₀)) · Uᴾ)
conceal-function-head W s {Aᴾ₀ = Aᴾ₀} {Bᴾ₀ = Bᴾ₀}
    {Aᴵ₀ = Aᴵ₀} {Bᴵ₀ = Bᴵ₀} {Pᴾ = Pᴾ} {Pᴵ = Pᴵ} {Qᴾ = Qᴾ} {Qᴵ = Qᴵ}
    p₁ p₂ safe₁ safe₂ sourceᴾ₁ sourceᴵ₁ sourceᴾ₂ sourceᴵ₂
    {Cᴾ = Cᴾ} {Cᴵ = Cᴵ} {Dᴾ = Dᴾ} {Dᴵ = Dᴵ} q₁ q₂
    targetᴾ₁ targetᴵ₁ targetᴾ₂ targetᴵ₂
    {k = k} revealAt concealBelow {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} function-related
    W′ W≼W′ {Uᴵ = Uᴵ} {Uᴾ = Uᴾ} argument-related =
  ClosureProof.computations-related-reindex
    (liftCenterImprecision W≼W′ p₂) (liftCenterImprecision W≼W′ p₂)
    refl refl (sym imprecise-redex-eq) (sym precise-redex-eq)
    expanded
  where
  s′ = slot-future s W≼W′
  Xᴾ′ = slotXᴾ s′
  Xᴵ′ = slotXᴵ s′
  Rᴾ′ = slotRᴾ s′
  Rᴵ′ = slotRᴵ s′

  Aᴾ′ = liftPreciseTy W≼W′ Aᴾ₀
  Bᴾ′ = liftPreciseTy W≼W′ Bᴾ₀
  Aᴵ′ = liftImpreciseTy W≼W′ Aᴵ₀
  Bᴵ′ = liftImpreciseTy W≼W′ Bᴵ₀

  cᴾ = 〖 Xᴾ′ , Rᴾ′ ↑ Aᴾ′ 〗
  dᴾ = makeConceal Xᴾ′ Rᴾ′ Bᴾ′
  cᴵ = 〖 Xᴵ′ , Rᴵ′ ↑ Aᴵ′ 〗
  dᴵ = makeConceal Xᴵ′ Rᴵ′ Bᴵ′

  Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
  Vᴵ′ = liftImpreciseTerm W≼W′ Vᴵ

  precise-redex-eq :
      liftPreciseTerm W≼W′
        (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (Aᴾ₀ ⇒ Bᴾ₀)) · Uᴾ
      ≡ (Vᴾ′ ↓ (cᴾ ↦↓ dᴾ)) · Uᴾ
  precise-redex-eq
      rewrite lifted-conceal-precise s W≼W′ Vᴾ (Aᴾ₀ ⇒ Bᴾ₀)
            | liftPreciseTy-arrow W≼W′ Aᴾ₀ Bᴾ₀ = refl

  imprecise-redex-eq :
      liftImpreciseTerm W≼W′
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (Aᴵ₀ ⇒ Bᴵ₀)) · Uᴵ
      ≡ (Vᴵ′ ↓ (cᴵ ↦↓ dᴵ)) · Uᴵ
  imprecise-redex-eq
      rewrite lifted-conceal-imprecise s W≼W′ Vᴵ (Aᴵ₀ ⇒ Bᴵ₀)
            | liftImpreciseTy-arrow W≼W′ Aᴵ₀ Bᴵ₀ = refl

  argument-endpoints =
    ClosureProof.value-imprecision-endpoints argument-related

  lifted-function : ValueImprecision W′
      (I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
        (liftCenterImprecision W≼W′ q₂)) k Vᴵ′ Vᴾ′
  lifted-function = ClosureProof.value-imprecision-reindex
    (I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
      (liftCenterImprecision W≼W′ q₂))
    (liftCenterImprecision W≼W′ (I.⇒⊑⇒ q₁ q₂))
    (sym (liftCenterTy-arrow W≼W′ Cᴾ Dᴾ))
    (sym (liftCenterTy-arrow W≼W′ Cᴵ Dᴵ))
    (ClosureProof.value-imprecision-future W≼W′
      (value-imprecision-downward-to
        {W = W} {p = I.⇒⊑⇒ q₁ q₂} {j = k} {k = suc k}
        {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (n≤1+n k) function-related))

  revealed : ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ q₁)) k
      (Uᴵ ↑ cᴵ) (Uᴾ ↑ cᴾ)
  revealed = revealAt W′ s′
    (liftCenterImprecision W≼W′ p₁) (safe-lift W≼W′ safe₁)
    (trans (embedPrecise-lift W≼W′ Aᴾ₀)
      (cong (liftCenterTy W≼W′) sourceᴾ₁))
    (trans (embedImprecise-lift W≼W′ Aᴵ₀)
      (cong (liftCenterTy W≼W′) sourceᴵ₁))
    (liftCenterImprecision W≼W′ q₁)
    (trans (cong (embedPrecise (core W′))
      (replace-precise-lift s W≼W′ Aᴾ₀))
      (trans (embedPrecise-lift W≼W′ _)
        (cong (liftCenterTy W≼W′) targetᴾ₁)))
    (trans (cong (embedImprecise (core W′))
      (replace-imprecise-lift s W≼W′ Aᴵ₀))
      (trans (embedImprecise-lift W≼W′ _)
        (cong (liftCenterTy W≼W′) targetᴵ₁)))
    (value-imprecision-downward-to
      {W = W′} {p = liftCenterImprecision W≼W′ p₁}
      {j = k} {k = suc k} {Vᴵ = Uᴵ} {Vᴾ = Uᴾ}
      (n≤1+n k) argument-related)

  applied : ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) k
      (Vᴵ′ · (Uᴵ ↑ cᴵ)) (Vᴾ′ · (Uᴾ ↑ cᴾ))
  applied = related-application-computation lifted-function revealed

  contracted : ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ p₂)) k
      ((Vᴵ′ · (Uᴵ ↑ cᴵ)) ↓ dᴵ) ((Vᴾ′ · (Uᴾ ↑ cᴾ)) ↓ dᴾ)
  contracted = concealed-computations W′ s′
    (liftCenterImprecision W≼W′ p₂) (safe-lift W≼W′ safe₂)
    (trans (embedPrecise-lift W≼W′ Bᴾ₀)
      (cong (liftCenterTy W≼W′) sourceᴾ₂))
    (trans (embedImprecise-lift W≼W′ Bᴵ₀)
      (cong (liftCenterTy W≼W′) sourceᴵ₂))
    (liftCenterImprecision W≼W′ q₂)
    (trans (cong (embedPrecise (core W′))
      (replace-precise-lift s W≼W′ Bᴾ₀))
      (trans (embedPrecise-lift W≼W′ _)
        (cong (liftCenterTy W≼W′) targetᴾ₂)))
    (trans (cong (embedImprecise (core W′))
      (replace-imprecise-lift s W≼W′ Bᴵ₀))
      (trans (embedImprecise-lift W≼W′ _)
        (cong (liftCenterTy W≼W′) targetᴵ₂)))
    concealBelow applied

  expanded : ComputationsRelated W′
      (FutureValueRelation (liftCenterImprecision W≼W′ p₂)) (suc k)
      ((Vᴵ′ ↓ (cᴵ ↦↓ dᴵ)) · Uᴵ) ((Vᴾ′ ↓ (cᴾ ↦↓ dᴾ)) · Uᴾ)
  expanded
      with conceal-fun-app-step-question
             {Σ = impreciseStore (core W′)} cᴵ dᴵ
             (imprecise-value function-endpoints)
             (imprecise-value argument-endpoints)
         | conceal-fun-app-step-question
             {Σ = preciseStore (core W′)} cᴾ dᴾ
             (precise-value function-endpoints)
             (precise-value argument-endpoints)
    where
    function-endpoints =
      ClosureProof.value-imprecision-endpoints lifted-function
  expanded | vVᴵ , vUᴵ , step-eqᴵ | vVᴾ , vUᴾ , step-eqᴾ =
    related-pure-step-expand (λ ()) (λ ())
      (conceal-fun-app-value-none cᴵ dᴵ)
      (conceal-fun-app-value-none cᴾ dᴾ)
      (β-conceal-⇒ vVᴵ vUᴵ) (β-conceal-⇒ vVᴾ vUᴾ)
      step-eqᴵ step-eqᴾ contracted

conceal-function : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Aᴾ₀ Bᴾ₀ : Ty Δᴾ} {Aᴵ₀ Bᴵ₀ : Ty Δᴵ}
    {Pᴾ Pᴵ Qᴾ Qᴵ : Ty Δᶜ}
    (p₁ : impEnv (core W) I.⊢ Pᴾ ⊑ Pᴵ)
    (p₂ : impEnv (core W) I.⊢ Qᴾ ⊑ Qᴵ)
  → RevealSafe p₁ → RevealSafe p₂
  → (sourceᴾ₁ : embedPrecise (core W) Aᴾ₀ ≡ Pᴾ)
  → (sourceᴵ₁ : embedImprecise (core W) Aᴵ₀ ≡ Pᴵ)
  → (sourceᴾ₂ : embedPrecise (core W) Bᴾ₀ ≡ Qᴾ)
  → (sourceᴵ₂ : embedImprecise (core W) Bᴵ₀ ≡ Qᴵ)
  → ∀ {Cᴾ Cᴵ Dᴾ Dᴵ : Ty Δᶜ}
      (q₁ : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
      (q₂ : impEnv (core W) I.⊢ Dᴾ ⊑ Dᴵ)
  → (targetᴾ₁ :
      embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Aᴾ₀) ≡ Cᴾ)
  → (targetᴵ₁ :
      embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Aᴵ₀) ≡ Cᴵ)
  → (targetᴾ₂ :
      embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ₀) ≡ Dᴾ)
  → (targetᴵ₂ :
      embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ₀) ≡ Dᴵ)
  → ∀ {k : ℕ} (below : Below k) {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.⇒⊑⇒ q₁ q₂) k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation (I.⇒⊑⇒ p₁ p₂)) k
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (Aᴵ₀ ⇒ Bᴵ₀))
      (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (Aᴾ₀ ⇒ Bᴾ₀))
conceal-function W s {Aᴾ₀ = Aᴾ₀} {Bᴾ₀ = Bᴾ₀} {Aᴵ₀ = Aᴵ₀} {Bᴵ₀ = Bᴵ₀}
    p₁ p₂ safe₁ safe₂ sourceᴾ₁ sourceᴵ₁ sourceᴾ₂ sourceᴵ₂
    q₁ q₂ targetᴾ₁ targetᴵ₁ targetᴾ₂ targetᴵ₂
    {k = k} below {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related =
  related-values-return
    (imprecise-value endpoints ↓ fun) (precise-value endpoints ↓ fun)
    at-every-index
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

  conceal-endpoints : ∀ (j : ℕ)
    → TypedEndpoints W (I.⇒⊑⇒ p₁ p₂)
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (Aᴵ₀ ⇒ Bᴵ₀))
        (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (Aᴾ₀ ⇒ Bᴾ₀))
  conceal-endpoints j = concealed-endpoints W s (I.⇒⊑⇒ p₁ p₂)
    (cong₂ _⇒_ sourceᴾ₁ sourceᴾ₂) (cong₂ _⇒_ sourceᴵ₁ sourceᴵ₂)
    (I.⇒⊑⇒ q₁ q₂) (cong₂ _⇒_ targetᴾ₁ targetᴾ₂)
    (cong₂ _⇒_ targetᴵ₁ targetᴵ₂) related
    (imprecise-value endpoints ↓ fun) (precise-value endpoints ↓ fun)

  head-at : ∀ (j : ℕ) → suc j ≤ k
    → ValueImprecision W (I.⇒⊑⇒ q₁ q₂) (suc j) Vᴵ Vᴾ
    → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
        (W≼W′ : Future W W′) {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
    → ValueImprecision W′ (liftCenterImprecision W≼W′ p₁) (suc j) Uᴵ Uᴾ
    → ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ p₂)) (suc j)
        (liftImpreciseTerm W≼W′
          (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (Aᴵ₀ ⇒ Bᴵ₀)) · Uᴵ)
        (liftPreciseTerm W≼W′
          (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (Aᴾ₀ ⇒ Bᴾ₀)) · Uᴾ)
  head-at j sj≤k source-at =
    conceal-function-head W s p₁ p₂ safe₁ safe₂
      sourceᴾ₁ sourceᴵ₁ sourceᴾ₂ sourceᴵ₂ q₁ q₂
      targetᴾ₁ targetᴵ₁ targetᴾ₂ targetᴵ₂
      (proj₁ (below j sj≤k))
      (λ i i≤j → proj₂ (below i (≤-trans (s≤s i≤j) sj≤k)))
      source-at

  functions-related : ∀ (j : ℕ) → suc j ≤ k
    → ValueImprecision W (I.⇒⊑⇒ q₁ q₂) (suc j) Vᴵ Vᴾ
    → FunctionsRelated W p₁ p₂ (suc j)
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (Aᴵ₀ ⇒ Bᴵ₀))
        (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (Aᴾ₀ ⇒ Bᴾ₀))
  functions-related zero sj≤k source-at =
    head-at zero sj≤k source-at , tt
  functions-related (suc j) sj≤k source-at =
    head-at (suc j) sj≤k source-at ,
    functions-related j (≤-trans (n≤1+n (suc j)) sj≤k)
      (value-imprecision-downward-to
        {W = W} {p = I.⇒⊑⇒ q₁ q₂} {j = suc j} {k = suc (suc j)}
        {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (n≤1+n (suc j)) source-at)

  at-every-index : ∀ (j : ℕ) → j ≤ k
    → FutureValueRelation (I.⇒⊑⇒ p₁ p₂) W future-refl j
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (Aᴵ₀ ⇒ Bᴵ₀))
        (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (Aᴾ₀ ⇒ Bᴾ₀))
  at-every-index zero j≤k = conceal-endpoints zero
  at-every-index (suc j) sj≤k =
    conceal-endpoints (suc j) ,
    functions-related j sj≤k
      (value-imprecision-downward-to
        {W = W} {p = I.⇒⊑⇒ q₁ q₂} {j = suc j} {k = k}
        {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} sj≤k related)

------------------------------------------------------------------------
-- Concealing to a bottom type is impossible
------------------------------------------------------------------------

-- The concealed precise value would be a value of the empty universal
-- type.

bottom-conceal-impossible : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W) {Bᴾ : Ty Δᴾ}
  → embedPrecise (core W) Bᴾ ≡ `∀ (＇ Fin.zero)
  → ∀ {Cᴾ Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
  → embedPrecise (core W) (replaceTy (slotXᴾ s) (slotRᴾ s) Bᴾ) ≡ Cᴾ
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W q k Vᴵ Vᴾ
  → ⊥
bottom-conceal-impossible W s {Bᴾ = Bᴾ} sourceᴾ q targetᴾ related
    with rename-universal-inversion _ sourceᴾ
bottom-conceal-impossible W s sourceᴾ q targetᴾ related
    | Bᴾ₀ , refl , bodyᴾ
    with rename-variable-inversion _ bodyᴾ
bottom-conceal-impossible W s sourceᴾ q targetᴾ related
    | .(＇ Fin.zero) , refl , bodyᴾ | Fin.zero , refl , centerᴾ =
  no-bot-value (precise-value endpoints ↓ all)
    (⊢conceal
      (structural-conceal-typing (`∀ (＇ Fin.zero))
        (preciseBound (atom s)))
      Vᴾ⊢Cᴾ)
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

  Vᴾ⊢Cᴾ = subst≡
    (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    (renameᵗ-injective (toRenameᵗ-injective (preciseEmbedding (core W)))
      (trans (preciseEmbedded endpoints) (sym targetᴾ)))
    (precise-typed endpoints)
bottom-conceal-impossible W s sourceᴾ q targetᴾ related
    | .(＇ (Fin.suc _)) , refl , bodyᴾ | Fin.suc Y , refl , centerᴾ
    with centerᴾ
bottom-conceal-impossible W s sourceᴾ q targetᴾ related
    | .(＇ (Fin.suc _)) , refl , bodyᴾ | Fin.suc Y , refl , centerᴾ | ()

------------------------------------------------------------------------
-- The induction
------------------------------------------------------------------------

reveal-conceal-step : ∀ (k : ℕ) → Below k → RevealAt k × ConcealAt k
reveal-conceal-step k below = reveal-at , conceal-at
  where
  reveal-at : RevealAt k
  reveal-at W s p (safe-atomic atomic) sourceᴾ sourceᴵ q
      targetᴾ targetᴵ related =
    RA.AtSlot.reveal-atomic W (atom s) (entry-eq s) (mode-eq s)
      p atomic sourceᴾ sourceᴵ q targetᴾ targetᴵ related
  reveal-at W s (I.⇒⊑⇒ p₁ p₂) (safe-⇒⊑⇒ safe₁ safe₂)
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related
      with rename-arrow-inversion _ sourceᴾ
         | rename-arrow-inversion _ sourceᴵ
  reveal-at W s (I.⇒⊑⇒ p₁ p₂) (safe-⇒⊑⇒ safe₁ safe₂)
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related
      | Aᴾ₀ , Bᴾ₀ , refl , sourceᴾ₁ , sourceᴾ₂
      | Aᴵ₀ , Bᴵ₀ , refl , sourceᴵ₁ , sourceᴵ₂
      with targetᴾ | targetᴵ
  reveal-at W s (I.⇒⊑⇒ p₁ p₂) (safe-⇒⊑⇒ safe₁ safe₂)
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related
      | Aᴾ₀ , Bᴾ₀ , refl , sourceᴾ₁ , sourceᴾ₂
      | Aᴵ₀ , Bᴵ₀ , refl , sourceᴵ₁ , sourceᴵ₂
      | refl | refl
      with arrow-imprecision-view q
  reveal-at W s (I.⇒⊑⇒ p₁ p₂) (safe-⇒⊑⇒ safe₁ safe₂)
      sourceᴾ sourceᴵ .(I.⇒⊑⇒ q₁ q₂) targetᴾ targetᴵ related
      | Aᴾ₀ , Bᴾ₀ , refl , sourceᴾ₁ , sourceᴾ₂
      | Aᴵ₀ , Bᴵ₀ , refl , sourceᴵ₁ , sourceᴵ₂
      | refl | refl
      | arrow-imprecision q₁ q₂ =
    reveal-function W s p₁ p₂ safe₁ safe₂
      sourceᴾ₁ sourceᴵ₁ sourceᴾ₂ sourceᴵ₂ q₁ q₂
      refl refl refl refl below related
  reveal-at W s I.bot-elim safe-bot-elim sourceᴾ sourceᴵ q
      targetᴾ targetᴵ related =
    ⊥-elim (no-precise-bottom-value related)
  reveal-at W s I.bot⊑★ safe-bot⊑★ sourceᴾ sourceᴵ q
      targetᴾ targetᴵ related =
    ⊥-elim (no-precise-bottom-value related)

  conceal-at : ConcealAt k
  conceal-at W s p (safe-atomic atomic) sourceᴾ sourceᴵ q
      targetᴾ targetᴵ related =
    CA.AtSlot.conceal-atomic W (atom s) (entry-eq s) (mode-eq s)
      p atomic sourceᴾ sourceᴵ q targetᴾ targetᴵ related
  conceal-at W s (I.⇒⊑⇒ p₁ p₂) (safe-⇒⊑⇒ safe₁ safe₂)
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related
      with rename-arrow-inversion _ sourceᴾ
         | rename-arrow-inversion _ sourceᴵ
  conceal-at W s (I.⇒⊑⇒ p₁ p₂) (safe-⇒⊑⇒ safe₁ safe₂)
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related
      | Aᴾ₀ , Bᴾ₀ , refl , sourceᴾ₁ , sourceᴾ₂
      | Aᴵ₀ , Bᴵ₀ , refl , sourceᴵ₁ , sourceᴵ₂
      with targetᴾ | targetᴵ
  conceal-at W s (I.⇒⊑⇒ p₁ p₂) (safe-⇒⊑⇒ safe₁ safe₂)
      sourceᴾ sourceᴵ q targetᴾ targetᴵ related
      | Aᴾ₀ , Bᴾ₀ , refl , sourceᴾ₁ , sourceᴾ₂
      | Aᴵ₀ , Bᴵ₀ , refl , sourceᴵ₁ , sourceᴵ₂
      | refl | refl
      with arrow-imprecision-view q
  conceal-at W s (I.⇒⊑⇒ p₁ p₂) (safe-⇒⊑⇒ safe₁ safe₂)
      sourceᴾ sourceᴵ .(I.⇒⊑⇒ q₁ q₂) targetᴾ targetᴵ related
      | Aᴾ₀ , Bᴾ₀ , refl , sourceᴾ₁ , sourceᴵ₂′
      | Aᴵ₀ , Bᴵ₀ , refl , sourceᴵ₁ , sourceᴵ₂
      | refl | refl
      | arrow-imprecision q₁ q₂ =
    conceal-function W s p₁ p₂ safe₁ safe₂
      sourceᴾ₁ sourceᴵ₁ sourceᴵ₂′ sourceᴵ₂ q₁ q₂
      refl refl refl refl below related
  conceal-at W s I.bot-elim safe-bot-elim sourceᴾ sourceᴵ q
      targetᴾ targetᴵ related =
    ⊥-elim (bottom-conceal-impossible W s sourceᴾ q targetᴾ related)
  conceal-at W s I.bot⊑★ safe-bot⊑★ sourceᴾ sourceᴵ q
      targetᴾ targetᴵ related =
    ⊥-elim (bottom-conceal-impossible W s sourceᴾ q targetᴾ related)

-- Strong induction on the step index.

reveal-conceal-acc : ∀ (k : ℕ) → Acc _<_ k → RevealAt k × ConcealAt k
reveal-conceal-acc k (acc smaller) =
  reveal-conceal-step k
    (λ j j<k → reveal-conceal-acc j (smaller j<k))

reveal-conceal-all : ∀ (k : ℕ) → RevealAt k × ConcealAt k
reveal-conceal-all k = reveal-conceal-acc k (wf k)

------------------------------------------------------------------------
-- The structural reveal and conceal
------------------------------------------------------------------------

reveal-structural : ∀ {k} → RevealAt k
reveal-structural {k = k} = proj₁ (reveal-conceal-all k)

conceal-structural : ∀ {k} → ConcealAt k
conceal-structural {k = k} = proj₂ (reveal-conceal-all k)
