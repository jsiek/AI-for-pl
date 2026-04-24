module LogicalRelation where

-- File Charter:
--   * Defines the step-indexed logical relation for `PolyUpDown`.
--   * Introduces direction/index/world/precision indices and `𝒱`/`ℰ` clauses.

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
  using (ℕ; zero; suc; z<s; _<_; _<′_; <′-base; ≤′-reflexive;
         ≤′-step)
open import Data.Nat.Induction using (<′-rec; <′-wellFounded)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; 0ℓ; lift) renaming (suc to lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Axiom.Extensionality.Propositional
  using (Extensionality; implicit-extensionality)
open import Induction.WellFounded as WF
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import Types
open import Store using (_⊆ˢ_; ⊆ˢ-refl; StoreWf)
open import Imprecision
open import TypeProperties
  using (liftSubstˢ; substᵗ-ν-src; substᵗ-⇑ˢ; substᵗ-id; renameᵗ-substᵗ;
         substᵗ-ground; renameᵗ-preserves-WfTy; renameˢ-preserves-WfTy;
         TyRenameWf-suc; SealRenameWf-suc)
open import UpDown
open import Terms hiding (_[_]ᵀ)
open import TermPrecision using (Prec; PCtx)
open import TermProperties using (Substˣ; substˣ-term; _[_]; _[_]ᵀ)
open import ReductionFresh using (Value; _∣_—→_∣_; _∣_—↠_∣_)
open import ProgressFresh using (canonical-★; sv-up-tag; canonical-｀; sv-down-seal)

------------------------------------------------------------------------
-- Direction, world, and precision index
------------------------------------------------------------------------

data Dir : Set where
  ≼ : Dir
  ≽ : Dir

Rel : Set₁
Rel = ℕ → Dir → Term → Term → Set

DownClosed : Rel → Set
DownClosed R = ∀ {k dir V W} → R (suc k) dir V W → R k dir V W

record SealRel : Set₁ where
  constructor ηentry
  field
    αˡ : Seal
    αʳ : Seal
    Rη : Rel
    downη : DownClosed Rη
open SealRel public

infix 4 _∋η_↔_∶_

data _∋η_↔_∶_ : List SealRel → Seal → Seal → Rel → Set₁ where
  hereη :
    ∀ {η αˡ αʳ R} {dR : DownClosed R} →
    (ηentry αˡ αʳ R dR ∷ η) ∋η αˡ ↔ αʳ ∶ R

  thereη :
    ∀ {η αˡ αʳ R βˡ βʳ R′} {dR′ : DownClosed R′} →
    η ∋η αˡ ↔ αʳ ∶ R →
    (ηentry βˡ βʳ R′ dR′ ∷ η) ∋η αˡ ↔ αʳ ∶ R

infix 4 _⊆η_

data _⊆η_ : List SealRel → List SealRel → Set₁ where
  η-done : ∀ {η} → [] ⊆η η
  η-keep : ∀ {η η′ e} → η ⊆η η′ → (e ∷ η) ⊆η (e ∷ η′)
  η-drop : ∀ {η η′ e} → η ⊆η η′ → η ⊆η (e ∷ η′)

⊆η-refl : ∀ {η} → η ⊆η η
⊆η-refl {η = []} = η-done
⊆η-refl {η = e ∷ η} = η-keep ⊆η-refl

record World : Set₁ where
  constructor mkWorld
  field
    Δ : TyCtx
    Ψ : SealCtx
    Σˡ : Store
    Σʳ : Store
    wfΣˡ : StoreWf Δ Ψ Σˡ
    wfΣʳ : StoreWf Δ Ψ Σʳ
    η : List SealRel
open World public

record _⪰_ (w′ w : World) : Set₁ where
  field
    growΔ : Δ w′ ≡ Δ w
    growΨ : Ψ w′ ≡ Ψ w
    growˡ : Σˡ w ⊆ˢ Σˡ w′
    growʳ : Σʳ w ⊆ˢ Σʳ w′
    growη : η w ⊆η η w′

extendWorld : World → (R : Rel) → DownClosed R → World
extendWorld w R downR =
  mkWorld (Δ w) (Ψ w) (Σˡ w) (Σʳ w) (wfΣˡ w) (wfΣʳ w)
    (ηentry (length (Σˡ w)) (length (Σʳ w)) R downR ∷ η w)

mkWorldˡ :
  (w : World) →
  (Σˡ′ : Store) →
  StoreWf (Δ w) (Ψ w) Σˡ′ →
  World
mkWorldˡ w Σˡ′ wfΣˡ′ =
  mkWorld (Δ w) (Ψ w) Σˡ′ (Σʳ w) wfΣˡ′ (wfΣʳ w) (η w)

mkWorldʳ :
  (w : World) →
  (Σʳ′ : Store) →
  StoreWf (Δ w) (Ψ w) Σʳ′ →
  World
mkWorldʳ w Σʳ′ wfΣʳ′ =
  mkWorld (Δ w) (Ψ w) (Σˡ w) Σʳ′ (wfΣˡ w) wfΣʳ′ (η w)

extendWorld-⪰ : ∀ {w} (R : Rel) (downR : DownClosed R) → extendWorld w R downR ⪰ w
extendWorld-⪰ {w} R downR ._⪰_.growΔ = refl
extendWorld-⪰ {w} R downR ._⪰_.growΨ = refl
extendWorld-⪰ {w} R downR ._⪰_.growˡ = ⊆ˢ-refl
extendWorld-⪰ {w} R downR ._⪰_.growʳ = ⊆ˢ-refl
extendWorld-⪰ {w} R downR ._⪰_.growη = η-drop ⊆η-refl

η∋-downClosed : ∀ {η αˡ αʳ R} → η ∋η αˡ ↔ αʳ ∶ R → DownClosed R
η∋-downClosed {η = ηentry _ _ _ dR ∷ η} hereη {k} {dir} {V} {W} =
  dR {k} {dir} {V} {W}
η∋-downClosed (thereη η∋) {k} {dir} {V} {W} =
  η∋-downClosed η∋ {k} {dir} {V} {W}

--------------------------------------------------------------------------------
-- Logical relation core
--------------------------------------------------------------------------------

VRelFor :
  (∀ {A B} → A ⊑ B → Dir → World → Term → Term → Set₁) →
  ∀ {A B} → A ⊑ B → Dir → World → Term → Term → Set₁
VRelFor payload {A = A} {B = B} p dir w V W =
  Value V × Value W ×
  ((Δ w ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ V ⦂ A) ×
   (Δ w ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ W ⦂ B)) ×
  payload p dir w V W

ERelFor :
  (∀ {A B} → A ⊑ B → Dir → World → Term → Term → Set₁) →
  ∀ {A B} → A ⊑ B → Dir → World → Term → Term → Set₁
ERelFor body {A = A} {B = B} p dir w Mˡ Mʳ =
  ((Δ w ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ A) ×
   (Δ w ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ B)) ×
  body p dir w Mˡ Mʳ

mutual
  record StepRel (n : ℕ) : Set₂ where
    inductive
    field
      payloadᵣ : ∀ {A B} → A ⊑ B → Dir → World → Term → Term → Set₁
      bodyᵣ : ∀ {A B} → A ⊑ B → Dir → World → Term → Term → Set₁
      lowerᵣ : ∀ {j} → j <′ n → StepRel j

  𝒱⟨_⟩ : ∀ {n A B} → StepRel n → A ⊑ B → Dir → World → Term → Term → Set₁
  𝒱⟨ r ⟩ = VRelFor (StepRel.payloadᵣ r)

  ℰ⟨_⟩ : ∀ {n A B} → StepRel n → A ⊑ B → Dir → World → Term → Term → Set₁
  ℰ⟨ r ⟩ = ERelFor (StepRel.bodyᵣ r)

open StepRel public

postulate
  fun-ext : ∀ {a b} → Extensionality a b

lower-ext :
  ∀ {n} {ih ih′ : ∀ {j} → j <′ n → StepRel j} →
  (∀ {j} (j<n : j <′ n) → ih j<n ≡ ih′ j<n) →
  (λ {j} → ih {j}) ≡ (λ {j} → ih′ {j})
lower-ext ih≈ =
  implicit-extensionality fun-ext λ {j} →
    fun-ext λ j<n → ih≈ j<n

ℕ-payload : Term → Term → Set₁
ℕ-payload ($ (κℕ m)) ($ (κℕ m′)) = Lift (lsuc 0ℓ) (m ≡ m′)
ℕ-payload V W = Lift (lsuc 0ℓ) ⊥

stepRel : (n : ℕ) → (∀ {j} → j <′ n → StepRel j) → StepRel n
stepRel zero ih = record
  { payloadᵣ = payload
  ; bodyᵣ = body
  ; lowerᵣ = λ { (≤′-reflexive ()) }
  }
  where
  body : ∀ {A B} → A ⊑ B → Dir → World → Term → Term → Set₁
  body p dir w Mˡ Mʳ = Lift (lsuc 0ℓ) ⊤

  E : ∀ {A B} → A ⊑ B → Dir → World → Term → Term → Set₁
  E {A = A} {B = B} p dir w Mˡ Mʳ =
    ((Δ w ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ A) ×
     (Δ w ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ B)) ×
    body p dir w Mˡ Mʳ

  payload : ∀ {A B} → A ⊑ B → Dir → World → Term → Term → Set₁
  payload {A = ‵ `ℕ} {B = ‵ `ℕ} (⊑-‵ `ℕ) dir w V W = ℕ-payload V W
  payload {A = ‵ `𝔹} {B = ‵ `𝔹} (⊑-‵ `𝔹) dir w V W = Lift (lsuc 0ℓ) ⊥

  payload {A = Aˡ ⇒ Bˡ} {B = Aʳ ⇒ Bʳ}
      (⊑-⇒ Aˡ Aʳ Bˡ Bʳ pA pB) dir w V W =
    (j : ℕ) → (j<n : j <′ zero) → ∀ {V′ W′} →
      𝒱⟨ ih j<n ⟩ pA dir w V′ W′ →
      ℰ⟨ ih j<n ⟩ pB dir w (V · V′) (W · W′)

  payload (⊑-∀ Aˡ Aʳ p) dir w V W =
    ∀ {w′} → w′ ⪰ w → (R : Rel) → (downR : DownClosed R) → (T U : Ty) →
      E p dir (extendWorld w′ R downR) (V ⦂∀ Aˡ [ T ]) (W ⦂∀ Aʳ [ U ])

  payload (⊑-ν A′ B′ p) dir w V W =
    ∀ {w′} → w′ ⪰ w → (R : Rel) → (downR : DownClosed R) →
      E p dir (extendWorld w′ R downR) (V ⦂∀ A′ [ ｀ length (Σˡ w′) ]) W

  payload ⊑-★★ dir w V W = Lift (lsuc 0ℓ) ⊤

  payload (⊑-★ _ G g p) ≼ w V W = Lift (lsuc 0ℓ) ⊤

  payload {A = A} {B = ★} (⊑-★ _ G g p) ≽ w V W = Lift (lsuc 0ℓ) ⊤

  payload {A = ｀ α} {B = ｀ α} (⊑-｀ α) dir w V W = seal-rel V W
    where
    seal-rel : Term → Term → Set₁
    seal-rel (V down seal βˡ) (W down seal βʳ) =
      Σ[ eqˡ ∈ α ≡ βˡ ] Σ[ eqʳ ∈ α ≡ βʳ ] Σ[ R ∈ Rel ]
        (η w ∋η α ↔ α ∶ R) × R zero dir V W
    seal-rel V W = Lift (lsuc 0ℓ) ⊥

  payload {A = ＇ X} {B = ＇ X} (⊑-＇ X) dir w V W = Lift (lsuc 0ℓ) ⊥

stepRel (suc k) ih = record
  { payloadᵣ = payload
  ; bodyᵣ = body
  ; lowerᵣ = lower
  }
  where
  lower : ∀ {j} → j <′ suc k → StepRel j
  lower {j} j<suc = ih {j} j<suc

  smaller : StepRel k
  smaller = lower <′-base

  body : ∀ {A B} → A ⊑ B → Dir → World → Term → Term → Set₁
  body {A = A} {B = B} p ≼ w Mˡ Mʳ =
    (Σ[ Σˡ′ ∈ Store ] Σ[ wfΣˡ′ ∈ StoreWf (Δ w) (Ψ w) Σˡ′ ] Σ[ Mˡ′ ∈ Term ]
      (Σˡ w ∣ Mˡ —→ Σˡ′ ∣ Mˡ′) ×
      ℰ⟨ smaller ⟩ p ≼ (mkWorldˡ w Σˡ′ wfΣˡ′) Mˡ′ Mʳ)
    ⊎
    (Σ[ Σʳ′ ∈ Store ] Σ[ wfΣʳ′ ∈ StoreWf (Δ w) (Ψ w) Σʳ′ ] Σ[ ℓ ∈ Label ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ))
    ⊎
    (Value Mˡ × Σ[ Σʳ′ ∈ Store ] Σ[ wfΣʳ′ ∈ StoreWf (Δ w) (Ψ w) Σʳ′ ]
      Σ[ Wʳ ∈ Term ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ Wʳ) ×
      𝒱⟨ smaller ⟩ p ≼ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Wʳ)

  body {A = A} {B = B} p ≽ w Mˡ Mʳ =
    (Σ[ Σʳ′ ∈ Store ] Σ[ wfΣʳ′ ∈ StoreWf (Δ w) (Ψ w) Σʳ′ ] Σ[ Mʳ′ ∈ Term ]
      (Σʳ w ∣ Mʳ —→ Σʳ′ ∣ Mʳ′) ×
      ℰ⟨ smaller ⟩ p ≽ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Mʳ′)
    ⊎
    (Σ[ Σʳ′ ∈ Store ] Σ[ wfΣʳ′ ∈ StoreWf (Δ w) (Ψ w) Σʳ′ ] Σ[ ℓ ∈ Label ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ))
    ⊎
    (Value Mʳ × Σ[ Σˡ′ ∈ Store ] Σ[ wfΣˡ′ ∈ StoreWf (Δ w) (Ψ w) Σˡ′ ]
      Σ[ Wˡ ∈ Term ]
      (Σˡ w ∣ Mˡ —↠ Σˡ′ ∣ Wˡ) ×
      𝒱⟨ smaller ⟩ p ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) Wˡ Mʳ)

  E : ∀ {A B} → A ⊑ B → Dir → World → Term → Term → Set₁
  E {A = A} {B = B} p dir w Mˡ Mʳ =
    ((Δ w ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ A) ×
     (Δ w ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ B)) ×
    body p dir w Mˡ Mʳ

  payload : ∀ {A B} → A ⊑ B → Dir → World → Term → Term → Set₁
  payload {A = ‵ `ℕ} {B = ‵ `ℕ} (⊑-‵ `ℕ) dir w V W = ℕ-payload V W
  payload {A = ‵ `𝔹} {B = ‵ `𝔹} (⊑-‵ `𝔹) dir w V W = Lift (lsuc 0ℓ) ⊥

  payload {A = Aˡ ⇒ Bˡ} {B = Aʳ ⇒ Bʳ}
      (⊑-⇒ Aˡ Aʳ Bˡ Bʳ pA pB) dir w V W =
    (j : ℕ) → (j<n : j <′ suc k) → ∀ {V′ W′} →
      𝒱⟨ lower j<n ⟩ pA dir w V′ W′ →
      ℰ⟨ lower j<n ⟩ pB dir w (V · V′) (W · W′)

  payload (⊑-∀ Aˡ Aʳ p) dir w V W =
    ∀ {w′} → w′ ⪰ w → (R : Rel) → (downR : DownClosed R) → (T U : Ty) →
      E p dir (extendWorld w′ R downR) (V ⦂∀ Aˡ [ T ]) (W ⦂∀ Aʳ [ U ])

  payload (⊑-ν A′ B′ p) dir w V W =
    ∀ {w′} → w′ ⪰ w → (R : Rel) → (downR : DownClosed R) →
      E p dir (extendWorld w′ R downR) (V ⦂∀ A′ [ ｀ length (Σˡ w′) ]) W

  payload ⊑-★★ dir w V W = star-rel V W
    where
    star-rel : Term → Term → Set₁
    star-rel (V up tag G) (W up tag H) =
      Lift (lsuc 0ℓ) (G ≡ H) × 𝒱⟨ smaller ⟩ (⊑-refl {A = G}) dir w V W
    star-rel (V down seal αˡ) (W down seal αʳ) =
      Σ[ R ∈ Rel ] (η w ∋η αˡ ↔ αʳ ∶ R) × R k dir V W
    star-rel V W = Lift (lsuc 0ℓ) ⊥

  payload (⊑-★ _ G g p) ≼ w V W = star-right-rel W
    where
    star-right-rel : Term → Set₁
    star-right-rel (W up tag H) =
      Lift (lsuc 0ℓ) (G ≡ H) × 𝒱⟨ smaller ⟩ p ≼ w V W
    star-right-rel W = Lift (lsuc 0ℓ) ⊥

  payload {A = A} {B = ★} (⊑-★ _ G g p) ≽ w V W = star-right-rel W
    where
    star-right-rel : Term → Set₁
    star-right-rel (W up tag H) =
      Lift (lsuc 0ℓ) (G ≡ H) × 𝒱⟨ smaller ⟩ p ≽ w V W
    star-right-rel W = Lift (lsuc 0ℓ) ⊥

  payload {A = ｀ α} {B = ｀ α} (⊑-｀ α) dir w V W = seal-rel V W
    where
    seal-rel : Term → Term → Set₁
    seal-rel (V down seal βˡ) (W down seal βʳ) =
      Σ[ eqˡ ∈ α ≡ βˡ ] Σ[ eqʳ ∈ α ≡ βʳ ] Σ[ R ∈ Rel ]
        (η w ∋η α ↔ α ∶ R) × R (suc k) dir V W
    seal-rel V W = Lift (lsuc 0ℓ) ⊥

  payload {A = ＇ X} {B = ＇ X} (⊑-＇ X) dir w V W = Lift (lsuc 0ℓ) ⊥

stepRel-ext :
  (n : ℕ) {ih ih′ : ∀ {j} → j <′ n → StepRel j} →
  (∀ {j} (j<n : j <′ n) → ih j<n ≡ ih′ j<n) →
  stepRel n ih ≡ stepRel n ih′
stepRel-ext n ih≈ rewrite lower-ext ih≈ = refl

sem : (n : ℕ) → StepRel n
sem = <′-rec StepRel stepRel

module StepRelFix = WF.FixPoint <′-wellFounded StepRel stepRel stepRel-ext

lowerᵣ-coh :
  ∀ {n j} (j<n : j <′ n) →
  lowerᵣ (sem n) j<n ≡ sem j
lowerᵣ-coh {n = zero} (≤′-reflexive ())
lowerᵣ-coh {n = suc n} j<n = StepRelFix.wfRecBuilder-wfRec j<n

𝒱-step-subst :
  ∀ {n A B} {r s : StepRel n} {p : A ⊑ B} {dir w V W} →
  r ≡ s →
  𝒱⟨ r ⟩ p dir w V W →
  𝒱⟨ s ⟩ p dir w V W
𝒱-step-subst refl rel = rel

ℰ-step-subst :
  ∀ {n A B} {r s : StepRel n} {p : A ⊑ B} {dir w Mˡ Mʳ} →
  r ≡ s →
  ℰ⟨ r ⟩ p dir w Mˡ Mʳ →
  ℰ⟨ s ⟩ p dir w Mˡ Mʳ
ℰ-step-subst refl rel = rel

𝒱-lower→sem :
  ∀ {n j A B} (j<n : j <′ n) {p : A ⊑ B} {dir w V W} →
  𝒱⟨ lowerᵣ (sem n) j<n ⟩ p dir w V W →
  𝒱⟨ sem j ⟩ p dir w V W
𝒱-lower→sem j<n = 𝒱-step-subst (lowerᵣ-coh j<n)

𝒱-sem→lower :
  ∀ {n j A B} (j<n : j <′ n) {p : A ⊑ B} {dir w V W} →
  𝒱⟨ sem j ⟩ p dir w V W →
  𝒱⟨ lowerᵣ (sem n) j<n ⟩ p dir w V W
𝒱-sem→lower j<n = 𝒱-step-subst (sym (lowerᵣ-coh j<n))

ℰ-lower→sem :
  ∀ {n j A B} (j<n : j <′ n) {p : A ⊑ B} {dir w Mˡ Mʳ} →
  ℰ⟨ lowerᵣ (sem n) j<n ⟩ p dir w Mˡ Mʳ →
  ℰ⟨ sem j ⟩ p dir w Mˡ Mʳ
ℰ-lower→sem j<n = ℰ-step-subst (lowerᵣ-coh j<n)

ℰ-sem→lower :
  ∀ {n j A B} (j<n : j <′ n) {p : A ⊑ B} {dir w Mˡ Mʳ} →
  ℰ⟨ sem j ⟩ p dir w Mˡ Mʳ →
  ℰ⟨ lowerᵣ (sem n) j<n ⟩ p dir w Mˡ Mʳ
ℰ-sem→lower j<n = ℰ-step-subst (sym (lowerᵣ-coh j<n))

𝒱payload : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
𝒱payload p n dir w V W = payloadᵣ (sem n) p dir w V W

𝒱 : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
𝒱 p n dir w V W = 𝒱⟨ sem n ⟩ p dir w V W

ℰ : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
ℰ p n dir w Mˡ Mʳ = ℰ⟨ sem n ⟩ p dir w Mˡ Mʳ

𝒱-left-value :
  ∀ {A B} {p : A ⊑ B} {k : ℕ} {dir : Dir}
    {w : World} {V W : Term} →
  𝒱 p k dir w V W →
  Value V
𝒱-left-value {k = zero} Vrel = proj₁ Vrel
𝒱-left-value {k = suc n} Vrel = proj₁ Vrel

𝒱-right-value :
  ∀ {A B} {p : A ⊑ B} {k : ℕ} {dir : Dir}
    {w : World} {V W : Term} →
  𝒱 p k dir w V W →
  Value W
𝒱-right-value {k = zero} Vrel = proj₁ (proj₂ Vrel)
𝒱-right-value {k = suc n} Vrel = proj₁ (proj₂ Vrel)

lift⊤ : Lift (lsuc 0ℓ) ⊤
lift⊤ = lift tt

------------------------------------------------------------------------
-- Environment interpretation for open terms
------------------------------------------------------------------------

WfTyClosedᵗ : TyCtx → Ty → Set
WfTyClosedᵗ Δ A = Σ[ Ψ ∈ SealCtx ] WfTy Δ Ψ A

record RelSub (Δ : TyCtx) : Set₁ where
  field
    leftᵗ : Substᵗ
    rightᵗ : Substᵗ
    left-closed : (X : TyVar) → WfTyClosedᵗ Δ (leftᵗ X)
    right-closed : (X : TyVar) → WfTyClosedᵗ Δ (rightᵗ X)
    precᵗ : (X : TyVar) → leftᵗ X ⊑ rightᵗ X
open RelSub public

∅ρ : RelSub 0
(∅ρ .leftᵗ) = λ _ → ‵ `ℕ
(∅ρ .rightᵗ) = λ _ → ‵ `ℕ
(∅ρ .left-closed) = λ _ → 0 , wfBase
(∅ρ .right-closed) = λ _ → 0 , wfBase
(∅ρ .precᵗ) = λ _ → ⊑-‵ `ℕ

shift-substᵗ : (A : Ty) → substᵗ (λ X → ＇ suc X) A ≡ renameᵗ suc A
shift-substᵗ A = trans (sym (renameᵗ-substᵗ suc (λ X → ＇ X) A))
                        (cong (renameᵗ suc) (substᵗ-id A))

⇑ᵗρ : ∀ {Δ} → RelSub Δ → RelSub (suc Δ)
(⇑ᵗρ ρ .leftᵗ) = extsᵗ (leftᵗ ρ)
(⇑ᵗρ ρ .rightᵗ) = extsᵗ (rightᵗ ρ)
(⇑ᵗρ ρ .left-closed) zero = 0 , wfVar z<s
(⇑ᵗρ ρ .left-closed) (suc X) =
  let Ψ , wfA = left-closed ρ X in Ψ , renameᵗ-preserves-WfTy wfA TyRenameWf-suc
(⇑ᵗρ ρ .right-closed) zero = 0 , wfVar z<s
(⇑ᵗρ ρ .right-closed) (suc X) =
  let Ψ , wfA = right-closed ρ X in Ψ , renameᵗ-preserves-WfTy wfA TyRenameWf-suc
(⇑ᵗρ ρ .precᵗ) zero = ⊑-＇ zero
(⇑ᵗρ ρ .precᵗ) (suc X) =
  cast-⊑ (shift-substᵗ (leftᵗ ρ X))
          (shift-substᵗ (rightᵗ ρ X))
          (Imprecision.substᵗ-⊑ (λ Y → ＇ suc Y) (precᵗ ρ X))

⇑ˢρ : ∀ {Δ} → RelSub Δ → RelSub Δ
(⇑ˢρ ρ .leftᵗ) = liftSubstˢ (leftᵗ ρ)
(⇑ˢρ ρ .rightᵗ) = liftSubstˢ (rightᵗ ρ)
(⇑ˢρ ρ .left-closed) X =
  let Ψ , wfA = left-closed ρ X in suc Ψ , renameˢ-preserves-WfTy wfA SealRenameWf-suc
(⇑ˢρ ρ .right-closed) X =
  let Ψ , wfA = right-closed ρ X in suc Ψ , renameˢ-preserves-WfTy wfA SealRenameWf-suc
(⇑ˢρ ρ .precᵗ) X = renameˢ-⊑ suc (precᵗ ρ X)

substᴿ-⊑ : ∀ {Δ} → (ρ : RelSub Δ) → ∀ {A B} → A ⊑ B → substᵗ (leftᵗ ρ) A ⊑ substᵗ (rightᵗ ρ) B
substᴿ-⊑ ρ ⊑-★★ = ⊑-★★
substᴿ-⊑ ρ (⊑-★ A G g p) =
  ⊑-★
    (substᵗ (leftᵗ ρ) A)
    (substᵗ (rightᵗ ρ) G)
    (substᵗ-ground (rightᵗ ρ) g)
    (substᴿ-⊑ ρ p)
substᴿ-⊑ ρ (⊑-＇ X) = precᵗ ρ X
substᴿ-⊑ ρ (⊑-｀ α) = ⊑-｀ α
substᴿ-⊑ ρ (⊑-‵ ι) = ⊑-‵ ι
substᴿ-⊑ ρ (⊑-⇒ A A′ B B′ p q) =
  ⊑-⇒
    (substᵗ (leftᵗ ρ) A)
    (substᵗ (rightᵗ ρ) A′)
    (substᵗ (leftᵗ ρ) B)
    (substᵗ (rightᵗ ρ) B′)
    (substᴿ-⊑ ρ p)
    (substᴿ-⊑ ρ q)
substᴿ-⊑ ρ (⊑-∀ A B p) =
  ⊑-∀
    (substᵗ (extsᵗ (leftᵗ ρ)) A)
    (substᵗ (extsᵗ (rightᵗ ρ)) B)
    (substᴿ-⊑ (⇑ᵗρ ρ) p)
substᴿ-⊑ ρ (⊑-ν A B p) =
  ⊑-ν
    (substᵗ (extsᵗ (leftᵗ ρ)) A)
    (substᵗ (rightᵗ ρ) B)
    (cast-⊑ (substᵗ-ν-src (leftᵗ ρ) A)
             (substᵗ-⇑ˢ (rightᵗ ρ) B)
             (substᴿ-⊑ (⇑ˢρ ρ) p))

record RelEnv : Set where
  field
    leftˣ : Substˣ
    rightˣ : Substˣ
open RelEnv public

∅γ : RelEnv
(∅γ .leftˣ) x = ` x
(∅γ .rightˣ) x = ` x

⇓γ : RelEnv → RelEnv
(⇓γ γ .leftˣ) x = leftˣ γ (suc x)
(⇓γ γ .rightˣ) x = rightˣ γ (suc x)

𝒢 : PCtx → ℕ → Dir → World → RelSub 0 → RelEnv → Set₁
𝒢 [] n dir w ρ γ = Lift (lsuc 0ℓ) ⊤
𝒢 ((A , B , p) ∷ Γ) n dir w ρ γ =
  Value (leftˣ γ zero) ×
  Value (rightˣ γ zero) ×
  𝒱 (substᴿ-⊑ ρ p) n dir w (leftˣ γ zero) (rightˣ γ zero) ×
  𝒢 Γ n dir w ρ (⇓γ γ)

_∣_⊨_⊑_⦂_ : PCtx → Dir → Term → Term → ∀ {A B} → A ⊑ B → Set₁
Γ ∣ dir ⊨ M ⊑ M′ ⦂ p =
  ∀ (n : ℕ) (w : World) (ρ : RelSub 0) (γ : RelEnv) →
  𝒢 Γ n dir w ρ γ →
  ℰ (substᴿ-⊑ ρ p) n dir w
    (substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M))
    (substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′))

_⊨_⊑_⦂_ : PCtx → Term → Term → ∀ {A B} → A ⊑ B → Set₁
Γ ⊨ M ⊑ M′ ⦂ p = (Γ ∣ ≼ ⊨ M ⊑ M′ ⦂ p) × (Γ ∣ ≽ ⊨ M ⊑ M′ ⦂ p)

proj⊨ :
  ∀ {Γ M M′ A B} {p : A ⊑ B} →
  (dir : Dir) →
  Γ ⊨ M ⊑ M′ ⦂ p →
  Γ ∣ dir ⊨ M ⊑ M′ ⦂ p
proj⊨ ≼ rel = proj₁ rel
proj⊨ ≽ rel = proj₂ rel

mutual
  𝒱-monotone : ∀ A B (p : A ⊑ B) k dir w V W
    → 𝒱 p (suc k) dir w V W
    → 𝒱 p k dir w V W
  𝒱-monotone .(‵ `ℕ) .(‵ `ℕ) (⊑-‵ `ℕ) zero dir w V W
    (vV , (vW , ((V⊢ , W⊢) , nat-rel))) =
    vV , (vW , ((V⊢ , W⊢) , nat-rel))
  𝒱-monotone .(‵ `ℕ) .(‵ `ℕ) (⊑-‵ `ℕ) (suc k) dir w V W
    (vV , (vW , ((V⊢ , W⊢) , nat-rel))) =
    vV , (vW , ((V⊢ , W⊢) , nat-rel))
  𝒱-monotone .(‵ `𝔹) .(‵ `𝔹) (⊑-‵ `𝔹) zero dir w V W
    (vV , (vW , ((V⊢ , W⊢) , lift ())))
  𝒱-monotone .(‵ `𝔹) .(‵ `𝔹) (⊑-‵ `𝔹) (suc k) dir w V W
    (vV , (vW , ((V⊢ , W⊢) , lift ())))
  𝒱-monotone .(＇ _) .(＇ _) (⊑-＇ X) zero dir w V W
    (vV , (vW , ((V⊢ , W⊢) , lift ())))
  𝒱-monotone .(＇ _) .(＇ _) (⊑-＇ X) (suc k) dir w V W
    (vV , (vW , ((V⊢ , W⊢) , lift ())))
  𝒱-monotone .(★) .(★) ⊑-★★ zero dir w V W
    (vV , (vW , ((V⊢ , W⊢) , rel))) =
    vV , (vW , ((V⊢ , W⊢) , lift⊤))
  𝒱-monotone .(★) .(★) ⊑-★★ (suc k) dir w V W
    (vV , (vW , ((V⊢ , W⊢) , rel)))
    with canonical-★ vV V⊢ | canonical-★ vW W⊢
  𝒱-monotone .(★) .(★) ⊑-★★ (suc k) dir w V W
    (vV , (vW , ((V⊢ , W⊢) , rel)))
    | sv-up-tag {W = U} {G = G} vU eqV
    | sv-up-tag {W = U′} {G = H} vU′ eqW
    rewrite eqV | eqW with rel
  𝒱-monotone .(★) .(★) ⊑-★★ (suc k) dir w V W
    (vV , (vW , ((V⊢ , W⊢) , rel)))
    | sv-up-tag {W = U} {G = G} vU eqV
    | sv-up-tag {W = U′} {G = H} vU′ eqW
    | eqG , inner =
    vV , vW , (V⊢ , W⊢) ,
      eqG ,
      𝒱-sem→lower {n = suc k} <′-base {p = ⊑-refl {A = G}} {dir = dir}
        {w = w} {V = U} {W = U′}
        (𝒱-monotone G G (⊑-refl {A = G}) k dir w U U′
          (𝒱-lower→sem {n = suc (suc k)} <′-base {p = ⊑-refl {A = G}}
            {dir = dir} {w = w} {V = U} {W = U′} inner))
  𝒱-monotone A .(★) (⊑-★ _ G g p) zero ≼ w V W
    (vV , (vW , ((V⊢ , W⊢) , star-rel))) =
    vV , vW , (V⊢ , W⊢) , lift⊤
  𝒱-monotone A .(★) (⊑-★ _ G g p) zero ≽ w V W
    (vV , (vW , ((V⊢ , W⊢) , star-rel))) =
    vV , vW , (V⊢ , W⊢) , lift⊤
  𝒱-monotone A B (⊑-★ _ G g p) (suc k) ≼ w V W
    (vV , (vW , ((V⊢ , W⊢) , star-rel)))
    with canonical-★ vW W⊢
  𝒱-monotone A B (⊑-★ _ G g p) (suc k) ≼ w V W
    (vV , (vW , ((V⊢ , W⊢) , star-rel)))
    | sv-up-tag {W = W′} {G = H} vW′ eqW
    rewrite eqW with star-rel
  𝒱-monotone A B (⊑-★ _ G g p) (suc k) ≼ w V W
    (vV , (vW , ((V⊢ , W⊢) , star-rel)))
    | sv-up-tag {W = W′} {G = H} vW′ eqW
    | eqG , inner =
    vV , vW , (V⊢ , W⊢) ,
      eqG ,
      𝒱-sem→lower {n = suc k} <′-base {p = p} {dir = ≼}
        {w = w} {V = V} {W = W′}
        (𝒱-monotone A G p k ≼ w V W′
          (𝒱-lower→sem {n = suc (suc k)} <′-base {p = p} {dir = ≼}
            {w = w} {V = V} {W = W′} inner))
  𝒱-monotone A B (⊑-★ _ G g p) (suc k) ≽ w V W
    (vV , (vW , ((V⊢ , W⊢) , star-rel)))
    with canonical-★ vW W⊢
  𝒱-monotone A B (⊑-★ _ G g p) (suc k) ≽ w V W
    (vV , (vW , ((V⊢ , W⊢) , star-rel)))
    | sv-up-tag {W = W′} {G = H} vW′ eqW
    rewrite eqW with star-rel
  𝒱-monotone A B (⊑-★ _ G g p) (suc k) ≽ w V W
    (vV , (vW , ((V⊢ , W⊢) , star-rel)))
    | sv-up-tag {W = W′} {G = H} vW′ eqW
    | eqG , inner =
    vV , vW , (V⊢ , W⊢) ,
      eqG ,
      𝒱-sem→lower {n = suc k} <′-base {p = p} {dir = ≽}
        {w = w} {V = V} {W = W′}
        (𝒱-monotone A G p k ≽ w V W′
          (𝒱-lower→sem {n = suc (suc k)} <′-base {p = p} {dir = ≽}
            {w = w} {V = V} {W = W′} inner))
  𝒱-monotone A B (⊑-｀ α) zero dir w V W
    (vV , (vW , ((V⊢ , W⊢) , rel)))
    with canonical-｀ vV V⊢ | canonical-｀ vW W⊢
  𝒱-monotone A B (⊑-｀ α) zero dir w V W
    (vV , (vW , ((V⊢ , W⊢) , rel)))
    | sv-down-seal {W = V′} vV′ eqV
    | sv-down-seal {W = W′} vW′ eqW
    rewrite eqV | eqW with rel
  𝒱-monotone A B (⊑-｀ α) zero dir w V W
    (vV , (vW , ((V⊢ , W⊢) , rel)))
    | sv-down-seal {W = V′} vV′ eqV
    | sv-down-seal {W = W′} vW′ eqW
    | eqˡ , eqʳ , R , η∋ , Rrel =
    vV , vW , (V⊢ , W⊢) ,
      eqˡ , eqʳ , R , η∋ , η∋-downClosed η∋ Rrel
  𝒱-monotone A B (⊑-｀ α) (suc k) dir w V W
    (vV , (vW , ((V⊢ , W⊢) , rel)))
    with canonical-｀ vV V⊢ | canonical-｀ vW W⊢
  𝒱-monotone A B (⊑-｀ α) (suc k) dir w V W
    (vV , (vW , ((V⊢ , W⊢) , rel)))
    | sv-down-seal {W = V′} vV′ eqV
    | sv-down-seal {W = W′} vW′ eqW
    rewrite eqV | eqW with rel
  𝒱-monotone A B (⊑-｀ α) (suc k) dir w V W
    (vV , (vW , ((V⊢ , W⊢) , rel)))
    | sv-down-seal {W = V′} vV′ eqV
    | sv-down-seal {W = W′} vW′ eqW
    | eqˡ , eqʳ , R , η∋ , Rrel =
    vV , vW , (V⊢ , W⊢) ,
      eqˡ , eqʳ , R , η∋ , η∋-downClosed η∋ Rrel
  𝒱-monotone A B (⊑-⇒ Aˡ Aʳ Bˡ Bʳ pA pB)
    zero dir w V W (vV , (vW , ((V⊢ , W⊢) , fun-rel))) =
    vV , vW , (V⊢ , W⊢) , λ j → λ { (≤′-reflexive ()) }
  𝒱-monotone A B (⊑-⇒ Aˡ Aʳ Bˡ Bʳ pA pB)
    (suc k) dir w V W (vV , (vW , ((V⊢ , W⊢) , fun-rel))) =
    vV , vW , (V⊢ , W⊢) , λ j j<k {V′} {W′} arg →
      ℰ-sem→lower {n = suc k} j<k
        (ℰ-lower→sem {n = suc (suc k)} (≤′-step j<k)
          (fun-rel j (≤′-step j<k)
            (𝒱-sem→lower {n = suc (suc k)} (≤′-step j<k)
              (𝒱-lower→sem {n = suc k} j<k arg))))
  𝒱-monotone A B (⊑-∀ Aˡ Aʳ p) zero dir w V W
    (vV , (vW , ((V⊢ , W⊢) , all-rel))) =
    vV , vW , (V⊢ , W⊢) ,
      λ {w′} w⪰ (R : Rel) (downR : DownClosed R) T U →
        ℰ-monotone _ _ p zero dir (extendWorld w′ R downR)
          (V ⦂∀ Aˡ [ T ]) (W ⦂∀ Aʳ [ U ])
          (all-rel w⪰ R downR T U)
  𝒱-monotone A B (⊑-∀ Aˡ Aʳ p) (suc k) dir w V W
    (vV , (vW , ((V⊢ , W⊢) , all-rel))) =
    vV , vW , (V⊢ , W⊢) ,
      λ {w′} w⪰ (R : Rel) (downR : DownClosed R) T U →
        ℰ-monotone _ _ p (suc k) dir (extendWorld w′ R downR)
          (V ⦂∀ Aˡ [ T ]) (W ⦂∀ Aʳ [ U ])
          (all-rel w⪰ R downR T U)
  𝒱-monotone .(`∀ _) B (⊑-ν Aˡ Bʳ p) zero dir w V W
    (vV , (vW , ((V⊢ , W⊢) , nu-rel))) =
    vV , vW , (V⊢ , W⊢) ,
      λ {w′} w⪰ (R : Rel) (downR : DownClosed R) →
        ℰ-monotone _ _ p zero dir (extendWorld w′ R downR)
          (V ⦂∀ Aˡ [ ｀ length (Σˡ w′) ]) W
          (nu-rel w⪰ R downR)
  𝒱-monotone .(`∀ _) B (⊑-ν Aˡ Bʳ p) (suc k) dir w V W
    (vV , (vW , ((V⊢ , W⊢) , nu-rel))) =
    vV , vW , (V⊢ , W⊢) ,
      λ {w′} w⪰ (R : Rel) (downR : DownClosed R) →
        ℰ-monotone _ _ p (suc k) dir (extendWorld w′ R downR)
          (V ⦂∀ Aˡ [ ｀ length (Σˡ w′) ]) W
          (nu-rel w⪰ R downR)

  ℰ-monotone : ∀ A B (p : A ⊑ B) k dir w Mˡ Mʳ
    → ℰ p (suc k) dir w Mˡ Mʳ
    → ℰ p k dir w Mˡ Mʳ
  ℰ-monotone A B p zero ≼ w Mˡ Mʳ ((Mˡ⊢ , Mʳ⊢) , rel) =
    (Mˡ⊢ , Mʳ⊢) , lift⊤
  ℰ-monotone A B p zero ≽ w Mˡ Mʳ ((Mˡ⊢ , Mʳ⊢) , rel) =
    (Mˡ⊢ , Mʳ⊢) , lift⊤
  ℰ-monotone A B p (suc k) ≼ w Mˡ Mʳ
    ((Mˡ⊢ , Mʳ⊢) , inj₁ (Σˡ′ , wfΣˡ′ , Mˡ′ , step , rel′)) =
    (Mˡ⊢ , Mʳ⊢) ,
      inj₁ (Σˡ′ , wfΣˡ′ , Mˡ′ , step ,
        ℰ-sem→lower {n = suc k} <′-base {p = p} {dir = ≼}
          {w = mkWorldˡ w Σˡ′ wfΣˡ′} {Mˡ = Mˡ′} {Mʳ = Mʳ}
          (ℰ-monotone A B p k ≼ (mkWorldˡ w Σˡ′ wfΣˡ′) Mˡ′ Mʳ
            (ℰ-lower→sem {n = suc (suc k)} <′-base {p = p} {dir = ≼}
              {w = mkWorldˡ w Σˡ′ wfΣˡ′} {Mˡ = Mˡ′} {Mʳ = Mʳ} rel′)))
  ℰ-monotone A B p (suc k) ≼ w Mˡ Mʳ
    ((Mˡ⊢ , Mʳ⊢) , inj₂ (inj₁ (Σʳ′ , wfΣʳ′ , ℓ , blame↠))) =
    (Mˡ⊢ , Mʳ⊢) , inj₂ (inj₁ (Σʳ′ , wfΣʳ′ , ℓ , blame↠))
  ℰ-monotone A B p (suc k) ≼ w Mˡ Mʳ
    ((Mˡ⊢ , Mʳ⊢) ,
      inj₂ (inj₂ (vMˡ , Σʳ′ , wfΣʳ′ , Wʳ , steps , Vrel))) =
    (Mˡ⊢ , Mʳ⊢) ,
      inj₂ (inj₂ (vMˡ , Σʳ′ , wfΣʳ′ , Wʳ , steps ,
        𝒱-sem→lower {n = suc k} <′-base {p = p} {dir = ≼}
          {w = mkWorldʳ w Σʳ′ wfΣʳ′} {V = Mˡ} {W = Wʳ}
          (𝒱-monotone A B p k ≼ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Wʳ
            (𝒱-lower→sem {n = suc (suc k)} <′-base {p = p} {dir = ≼}
              {w = mkWorldʳ w Σʳ′ wfΣʳ′} {V = Mˡ} {W = Wʳ} Vrel))))
  ℰ-monotone A B p (suc k) ≽ w Mˡ Mʳ
    ((Mˡ⊢ , Mʳ⊢) , inj₁ (Σʳ′ , wfΣʳ′ , Mʳ′ , step , rel′)) =
    (Mˡ⊢ , Mʳ⊢) ,
      inj₁ (Σʳ′ , wfΣʳ′ , Mʳ′ , step ,
        ℰ-sem→lower {n = suc k} <′-base {p = p} {dir = ≽}
          {w = mkWorldʳ w Σʳ′ wfΣʳ′} {Mˡ = Mˡ} {Mʳ = Mʳ′}
          (ℰ-monotone A B p k ≽ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Mʳ′
            (ℰ-lower→sem {n = suc (suc k)} <′-base {p = p} {dir = ≽}
              {w = mkWorldʳ w Σʳ′ wfΣʳ′} {Mˡ = Mˡ} {Mʳ = Mʳ′} rel′)))
  ℰ-monotone A B p (suc k) ≽ w Mˡ Mʳ
    ((Mˡ⊢ , Mʳ⊢) , inj₂ (inj₁ (Σʳ′ , wfΣʳ′ , ℓ , blame↠))) =
    (Mˡ⊢ , Mʳ⊢) , inj₂ (inj₁ (Σʳ′ , wfΣʳ′ , ℓ , blame↠))
  ℰ-monotone A B p (suc k) ≽ w Mˡ Mʳ
    ((Mˡ⊢ , Mʳ⊢) ,
      inj₂ (inj₂ (vMʳ , Σˡ′ , wfΣˡ′ , Wˡ , steps , Vrel))) =
    (Mˡ⊢ , Mʳ⊢) ,
      inj₂ (inj₂ (vMʳ , Σˡ′ , wfΣˡ′ , Wˡ , steps ,
        𝒱-sem→lower {n = suc k} <′-base {p = p} {dir = ≽}
          {w = mkWorldˡ w Σˡ′ wfΣˡ′} {V = Wˡ} {W = Mʳ}
          (𝒱-monotone A B p k ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) Wˡ Mʳ
            (𝒱-lower→sem {n = suc (suc k)} <′-base {p = p} {dir = ≽}
              {w = mkWorldˡ w Σˡ′ wfΣˡ′} {V = Wˡ} {W = Mʳ} Vrel))))
