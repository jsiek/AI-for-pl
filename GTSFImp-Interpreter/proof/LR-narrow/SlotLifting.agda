module proof.LR-narrow.SlotLifting where

-- File Charter:
--   * Shape inversions for renamed types, the slot accessors, and the
--     laws relating a transported reveal or conceal frame to the future
--     lifting of the structural conversion at the lifted slot.
--   * Shared by the paired structural reveal
--     (proof.LR-narrow.RevealStructural) and the one-sided reveal
--     (proof.LR-narrow.PreciseReveal).

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

