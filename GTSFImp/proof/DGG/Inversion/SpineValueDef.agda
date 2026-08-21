module proof.DGG.Inversion.SpineValueDef where

-- File Charter:
--   * Defines the stable value-spine surface shared by DGG inversion proofs
--     and diagnostics.
--   * Provides target polymorphic value views for inst catch-up statements.
--   * Provides canonical target-variable/tag-boundary views used by the
--     right-injection inversion and seal transfer.
--   * Depends only on core cast-term imprecision typing projections and
--     world-decay context transport.

open import Data.Empty using (⊥-elim)
open import Data.Nat using (suc)
import Data.Fin as Fin
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)

open import Types
open import TyStore using (TyStore; _∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_; _⊢_∼★; _↪ᵗ_; _!;
  ∀ᶜ_; gen_; toRenameᵗ)
import Consistency as C
open import Conversion using (Conv↑; Conv↓; _↦↑_; _↦↓_;
  `∀↑_; `∀↓_; ⊢↓-seal)
open import Imprecision
open import Primitives using (Const; κℕ; κ𝔹)
open import CastTerms
import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision as CTIR
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.WorldDecay as WD
open CTI2 using
  (World;
   ηᴸʷ;
   ηᴿʷ;
   sourceStoreʷ;
   targetStoreʷ;
   CtxImp;
   _⊑ᵂ⟨_⟩_)
open CTIR using (_∣_⊢²_⊑_∶_)
open import proof.ImprecisionConsistency using (toRenameᵗ-injective)

------------------------------------------------------------------------
-- Target polymorphic value views
------------------------------------------------------------------------

data AllValueView {Δ : TyCtx} (V : Term Δ) : Set where
  allv-Λ : ∀ {W}
    → Value W
    → V ≡ Λ W
    → AllValueView V

  allv-∀ : ∀ {μ : Env∼ Δ} {W} {A B : Ty (suc Δ)}
      {c : C.extᵐ μ ⊢ A ∼ B}
    → Value W
    → V ≡ W ⟨ ∀ᶜ c ⟩
    → AllValueView V

  allv-gen : ∀ {μ : Env∼ Δ} {W} {A : Ty Δ} {B : Ty (suc Δ)}
      {c : C.genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : Fin.zero ∈ᵗ B ⦄
    → Value W
    → (A≢★ : A ≢ ★)
    → GenSafe c
    → V ≡ W ⟨ (gen c) A≢★ ⟩
    → AllValueView V

  allv-reveal : ∀ {W} {A B : Ty (suc Δ)} {c : Conv↑ (suc Δ) A B}
    → Value W
    → V ≡ W ↑ `∀↑ c
    → AllValueView V

  allv-conceal : ∀ {W} {A B : Ty (suc Δ)} {c : Conv↓ (suc Δ) A B}
    → Value W
    → V ≡ W ↓ `∀↓ c
    → AllValueView V

------------------------------------------------------------------------
-- Source value spines
------------------------------------------------------------------------

data SpineValue {Δ : TyCtx} : Term Δ → Set where
  sv-ƛ : (N : Term Δ) → SpineValue (ƛ N)

  sv-Λ : ∀ {V} → SpineValue V → SpineValue (Λ V)

  sv-$ : (κ : Const) → SpineValue ($ κ)

  sv-cast : ∀ {V} {μ : Env∼ Δ} {A B : Ty Δ} {c : μ ⊢ A ∼ B}
    → SpineValue V → Inert c → SpineValue (V ⟨ c ⟩)

  sv-seal : ∀ {V X R} → SpineValue V
    → SpineValue (V ↓ Conversion.seal X R)

  sv-reveal-fun : ∀ {V} {A A′ B B′ : Ty Δ}
      {c : Conv↓ Δ A′ A} {d : Conv↑ Δ B B′}
    → SpineValue V → SpineValue (V ↑ (c ↦↑ d))

  sv-conceal-fun : ∀ {V} {A A′ B B′ : Ty Δ}
      {c : Conv↑ Δ A′ A} {d : Conv↓ Δ B B′}
    → SpineValue V → SpineValue (V ↓ (c ↦↓ d))

  sv-reveal-all : ∀ {V} {A B : Ty (suc Δ)} {c : Conv↑ (suc Δ) A B}
    → SpineValue V → SpineValue (V ↑ `∀↑ c)

  sv-conceal-all : ∀ {V} {A B : Ty (suc Δ)} {c : Conv↓ (suc Δ) A B}
    → SpineValue V → SpineValue (V ↓ `∀↓ c)

------------------------------------------------------------------------
-- Canonical target values at an abstract variable
------------------------------------------------------------------------

data VarValueView {Δ : TyCtx} (Σ : TyStore Δ) (V : Term Δ)
    (X : TyVar Δ) : Set where
  varv-seal : ∀ {W R}
    → Value W
    → Σ ∋ X ⦂ R
    → V ≡ W ↓ Conversion.seal X R
    → VarValueView Σ V X

var-value-view : ∀ {Δ} {Σ : TyStore Δ} {Γ} {V : Term Δ} {X}
  → Value V
  → ⟨ Δ , Σ , Γ ⟩ ⊢ V ⦂ ＇ X
  → VarValueView Σ V X
var-value-view (ƛ N) ()
var-value-view (Λ vV) ()
var-value-view ($ (κℕ n)) ()
var-value-view ($ (κ𝔹 b)) ()
var-value-view (vV 《 inj 》) ()
var-value-view (vV 《 fun 》) ()
var-value-view (vV 《 all 》) ()
var-value-view (vV 《 genᵥ A≢★ safe 》) ()
var-value-view (vV ↑ fun) ()
var-value-view (vV ↑ all) ()
var-value-view (vV ↓ seal) (⊢conceal (⊢↓-seal X∈) V⊢) =
  varv-seal vV X∈ refl
var-value-view (vV ↓ fun) ()
var-value-view (vV ↓ all) ()

tag-inner-typing : ∀ {Δ} {Σ : TyStore Δ} {Γ} {N : Term Δ}
    {H : Ty Δ} {ν : Env∼ Δ}
    {gH : Ground H} {H∼★ : ν ⊢ H ∼★} {Hns : NonStar H}
    {cH : ν ⊢ H ∼ H}
  → ⟨ Δ , Σ , Γ ⟩ ⊢
      N ⟨ _! ⦃ gH ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ⦂ ★
  → ⟨ Δ , Σ , Γ ⟩ ⊢ N ⦂ H
tag-inner-typing (⊢⟨⟩ N⊢ cH!) = N⊢

var-tag-value-sealed : ∀ {Δ} {Σ : TyStore Δ} {Γ}
    {N : Term Δ} {A : Ty Δ} {Y : TyVar Δ} {ν : Env∼ Δ}
    {Y∼★ : ν ⊢ (＇ Y) ∼★}
    {cY : ν ⊢ A ∼ ＇ Y} {Ans : NonStar A}
  → Value (N ⟨ _! ⦃ ＇ Y ⦄ ⦃ Y∼★ ⦄ cY ⦃ Ans ⦄ ⟩)
  → ⟨ Δ , Σ , Γ ⟩ ⊢
      N ⟨ _! ⦃ ＇ Y ⦄ ⦃ Y∼★ ⦄ cY ⦃ Ans ⦄ ⟩ ⦂ ★
  → VarValueView Σ N Y
var-tag-value-sealed (vN 《 inj 》) N!⊢ =
  var-value-view vN (tag-inner-typing N!⊢)

right-tag-variable-view : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {Y : TyVar Δᴿ} {ν : Env∼ Δᴿ}
    {H∼★ : ν ⊢ (＇ Y) ∼★} {Hns : NonStar (＇ Y)}
    {cH : ν ⊢ (＇ Y) ∼ (＇ Y)} {p : A ⊑ᵂ⟨ W ⟩ ★}
  → Value N
  → W ∣ γ ⊢² M
      ⊑ N ⟨ _! ⦃ ＇ Y ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ∶ p
  → VarValueView (targetStoreʷ W) N Y
right-tag-variable-view vN M⊑N! =
  var-value-view vN (tag-inner-typing (CTI2T.target-typing² M⊑N!))

variable-imprecision-aligns : ∀ {Δ} {μ : ImpEnv Δ} {X Y : TyVar Δ}
  → μ ⊢ ＇ X ⊑ ＇ Y
  → X ≡ Y
variable-imprecision-aligns X⊑X = refl

variable-obligation-aligns : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → ＇ X ⊑ᵂ⟨ W ⟩ ＇ Y
  → toRenameᵗ (ηᴸʷ W) X ≡ toRenameᵗ (ηᴿʷ W) Y
variable-obligation-aligns q = variable-imprecision-aligns q

seal-rebase-target : ∀ {Δᴸ Δᴿ Δ} {Wᵖ W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → CTI2.RebaseAtᴸ Wᵖ W (just X)
  → ＇ X ⊑ᵂ⟨ W ⟩ ＇ Y
  → CTI2.RebaseAt Wᵖ W X Y
seal-rebase-target {W = W} {X = X} {Y = Y}
    (CTI2.rebase-varᴸ {Xᴿ = Xᴿ} rb) q
    with toRenameᵗ-injective (ηᴿʷ W)
      (trans (sym (CTI2.RebaseAt.pivotAligned rb))
        (variable-obligation-aligns {W = W} {X = X} {Y = Y} q))
seal-rebase-target (CTI2.rebase-varᴸ rb) q | refl = rb
seal-rebase-target
    {W = W} {X = X} {Y = Y}
    (CTI2.rebase-onlyᴸ member to-star disaligned represented) q =
  ⊥-elim
    (disaligned Y
      (sym (variable-obligation-aligns {W = W} {X = X} {Y = Y} q)))

seal-tag-boundary-view² : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ} {R : Ty Δᴸ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ} {ν : Env∼ Δᴿ}
    {H∼★ : ν ⊢ (＇ Y) ∼★} {Hns : NonStar (＇ Y)}
    {cH : ν ⊢ (＇ Y) ∼ (＇ Y)} {p : ＇ X ⊑ᵂ⟨ W ⟩ ★}
  → CTI2.RebaseAtᴸ Wᵖ W (just X)
  → Value N
  → W ∣ γ ⊢² M ↓ Conversion.seal X R
      ⊑ N ⟨ _! ⦃ ＇ Y ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ∶ p
  → (q : ＇ X ⊑ᵂ⟨ W ⟩ ＇ Y)
  → Σ[ U ∈ Term Δᴿ ] Σ[ S ∈ Ty Δᴿ ]
      (Value U
        × (targetStoreʷ W ∋ Y ⦂ S)
        × (N ≡ U ↓ Conversion.seal Y S)
        × CTI2.RebaseAt Wᵖ W X Y)
seal-tag-boundary-view² rb vN M↓X⊑N! q
    with right-tag-variable-view vN M↓X⊑N!
seal-tag-boundary-view² rb vN M↓X⊑N! q
    | varv-seal {W = U} {R = S} vU Y∈ refl =
  U , S , vU , Y∈ , refl , seal-rebase-target rb q

------------------------------------------------------------------------
-- Shared context transport
------------------------------------------------------------------------

decaySameCtxʳ : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ W″ : World Δᴸ Δᴿ Δ′}
    {γ : CtxImp W} {γ′ : CTI2.CtxImp W′}
  → (dec : WD.EnvDecay W′ W″)
  → CTI2.SameCtx γ γ′
  → CTI2.SameCtx γ (WD.decayCtx dec γ′)
decaySameCtxʳ dec CTI2.same-[] = CTI2.same-[]
decaySameCtxʳ dec (CTI2.same-∷ sc) =
  CTI2.same-∷ (decaySameCtxʳ dec sc)
