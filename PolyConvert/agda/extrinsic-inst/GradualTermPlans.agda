module GradualTermPlans where

-- File Charter:
--   * Experimental source-typed gradual-term precision relation.
--   * Defines a type-shaped plan that records whether each source forall is
--     preserved or dropped, plus a separate relation connecting ordinary
--     imprecision evidence to a plan.
--   * This file is a side design; the canonical gradual terms remain in
--     `GradualTerms`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (_<_; zero; suc; z<s; s<s)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import Imprecision
  using
    ( Imp
    ; VarPrec
    ; VarPrecCtx
    ; X⊑X
    ; X⊑★
    ; extend-X⊑X
    ; _∣_⊢_⦂_⊑_
    )
  renaming
    ( _∋_∶_ to _∋ⁱ_∶_
    ; here to hereⁱ
    ; there to thereⁱ
    ; ∋→< to ∋ⁱ→<
    )
open import Primitives using (constTy; κℕ)
open import proof.TypeProperties using (rename-raise-ext)
open import GradualTerms
  using
    ( GTerm
    ; `_
    ; ƛ_⇒_
    ; _·_
    ; Λ_
    ; _`[_]
    ; _⊕[_]_
    ; $
    )

------------------------------------------------------------------------
-- Type edit
------------------------------------------------------------------------

data StarEdit (Γ : VarPrecCtx) : Ty → Set where
  star-★ : StarEdit Γ ★
  star-X : ∀ {X} → Γ ∋ⁱ X ∶ X⊑★ → StarEdit Γ (＇ X)
  star-｀ : ∀ {α} → StarEdit Γ (｀ α)
  star-‵ : ∀ {ι} → StarEdit Γ (‵ ι)
  star-⇒ : ∀ {A B} → StarEdit Γ A → StarEdit Γ B → StarEdit Γ (A ⇒ B)

data TyEdit (Γ : VarPrecCtx) : Ty → Set where
  ty-star : ∀ {A} → StarEdit Γ A → TyEdit Γ A
  ty-X : ∀ {X} → Γ ∋ⁱ X ∶ X⊑X → TyEdit Γ (＇ X)
  ty-｀ : ∀ {α} → TyEdit Γ (｀ α)
  ty-‵ : ∀ {ι} → TyEdit Γ (‵ ι)
  ty-★ : TyEdit Γ ★
  ty-⇒ : ∀ {A B} → TyEdit Γ A → TyEdit Γ B → TyEdit Γ (A ⇒ B)
  ty-∀keep : ∀ {A} → TyEdit (X⊑X ∷ Γ) A → TyEdit Γ (`∀ A)
  ty-∀drop : ∀ {A} → TyEdit (X⊑★ ∷ Γ) A → TyEdit Γ (`∀ A)

-- TargetOk records the invariant that a target type mentions only variables
-- whose precision mode is X⊑X.  Variables introduced by dropped source foralls
-- have mode X⊑★, so they may guide an edit but must not escape into the
-- resulting target type.  The edit interpreters return TargetOk evidence with
-- each computed type, and the drop operations use that evidence to remove an
-- X⊑★ binder while preserving the invariant.
data TargetOk (Γ : VarPrecCtx) : Ty → Set where
  ok-X : ∀ {X} → Γ ∋ⁱ X ∶ X⊑X → TargetOk Γ (＇ X)
  ok-｀ : ∀ {α} → TargetOk Γ (｀ α)
  ok-‵ : ∀ {ι} → TargetOk Γ (‵ ι)
  ok-★ : TargetOk Γ ★
  ok-⇒ : ∀ {A B} → TargetOk Γ A → TargetOk Γ B → TargetOk Γ (A ⇒ B)
  ok-∀ : ∀ {A} → TargetOk (X⊑X ∷ Γ) A → TargetOk Γ (`∀ A)

dropTargetVar :
  ∀ n {Γ X} →
  extend-X⊑X n (X⊑★ ∷ Γ) ∋ⁱ X ∶ X⊑X →
  TyVar
dropTargetVar zero (thereⁱ {X = X} x∈) = X
dropTargetVar (suc n) hereⁱ = zero
dropTargetVar (suc n) (thereⁱ x∈) =
  suc (dropTargetVar n x∈)

dropTargetVar∈ :
  ∀ n {Γ X}
    (x∈ : extend-X⊑X n (X⊑★ ∷ Γ) ∋ⁱ X ∶ X⊑X) →
  extend-X⊑X n Γ ∋ⁱ dropTargetVar n x∈ ∶ X⊑X
dropTargetVar∈ zero (thereⁱ x∈) = x∈
dropTargetVar∈ (suc n) hereⁱ = hereⁱ
dropTargetVar∈ (suc n) (thereⁱ x∈) =
  thereⁱ (dropTargetVar∈ n x∈)

dropTargetVar-eq :
  ∀ n {Γ X}
    (x∈ : extend-X⊑X n (X⊑★ ∷ Γ) ∋ⁱ X ∶ X⊑X) →
  X ≡ raiseVarFrom n (dropTargetVar n x∈)
dropTargetVar-eq zero (thereⁱ x∈) = refl
dropTargetVar-eq (suc n) hereⁱ = refl
dropTargetVar-eq (suc n) (thereⁱ x∈) =
  cong suc (dropTargetVar-eq n x∈)

dropTargetFrom :
  ∀ n {Γ A} →
  TargetOk (extend-X⊑X n (X⊑★ ∷ Γ)) A →
  Ty
dropTargetFrom n (ok-X x∈) = ＇ (dropTargetVar n x∈)
dropTargetFrom n (ok-｀ {α = α}) = ｀ α
dropTargetFrom n (ok-‵ {ι = ι}) = ‵ ι
dropTargetFrom n ok-★ = ★
dropTargetFrom n (ok-⇒ okA okB) =
  dropTargetFrom n okA ⇒ dropTargetFrom n okB
dropTargetFrom n (ok-∀ okA) = `∀ (dropTargetFrom (suc n) okA)

dropTargetFrom-ok :
  ∀ n {Γ A}
    (ok : TargetOk (extend-X⊑X n (X⊑★ ∷ Γ)) A) →
  TargetOk (extend-X⊑X n Γ) (dropTargetFrom n ok)
dropTargetFrom-ok n (ok-X x∈) = ok-X (dropTargetVar∈ n x∈)
dropTargetFrom-ok n ok-｀ = ok-｀
dropTargetFrom-ok n ok-‵ = ok-‵
dropTargetFrom-ok n ok-★ = ok-★
dropTargetFrom-ok n (ok-⇒ okA okB) =
  ok-⇒ (dropTargetFrom-ok n okA) (dropTargetFrom-ok n okB)
dropTargetFrom-ok n (ok-∀ okA) = ok-∀ (dropTargetFrom-ok (suc n) okA)

dropTargetFrom-WfTy :
  ∀ n {Γ Ψ A} →
  WfTy (length (extend-X⊑X n (X⊑★ ∷ Γ))) Ψ A →
  (ok : TargetOk (extend-X⊑X n (X⊑★ ∷ Γ)) A) →
  WfTy (length (extend-X⊑X n Γ)) Ψ (dropTargetFrom n ok)
dropTargetFrom-WfTy n wfA (ok-X x∈) =
  wfVar (∋ⁱ→< (dropTargetVar∈ n x∈))
dropTargetFrom-WfTy n (wfSeal α<Ψ) (ok-｀ {α = α}) = wfSeal α<Ψ
dropTargetFrom-WfTy n wfBase (ok-‵ {ι = ι}) = wfBase
dropTargetFrom-WfTy n wf★ ok-★ = wf★
dropTargetFrom-WfTy n (wf⇒ wfA wfB) (ok-⇒ okA okB) =
  wf⇒ (dropTargetFrom-WfTy n wfA okA)
      (dropTargetFrom-WfTy n wfB okB)
dropTargetFrom-WfTy n (wf∀ wfA) (ok-∀ okA) =
  wf∀ (dropTargetFrom-WfTy (suc n) wfA okA)

dropTargetFrom-eq :
  ∀ n {Γ A}
    (ok : TargetOk (extend-X⊑X n (X⊑★ ∷ Γ)) A) →
  A ≡ renameᵗ (raiseVarFrom n) (dropTargetFrom n ok)
dropTargetFrom-eq n (ok-X x∈) =
  cong (λ X → ＇ X) (dropTargetVar-eq n x∈)
dropTargetFrom-eq n (ok-｀ {α = α}) = refl
dropTargetFrom-eq n (ok-‵ {ι = ι}) = refl
dropTargetFrom-eq n ok-★ = refl
dropTargetFrom-eq n (ok-⇒ okA okB) =
  cong₂ _⇒_ (dropTargetFrom-eq n okA) (dropTargetFrom-eq n okB)
dropTargetFrom-eq n (ok-∀ okA) =
  cong `∀ (trans (dropTargetFrom-eq (suc n) okA)
    (sym (rename-raise-ext n (dropTargetFrom (suc n) okA))))

insertMode : TyVar → VarPrec → VarPrecCtx → VarPrecCtx
insertMode zero m Γ = m ∷ Γ
insertMode (suc k) m [] = m ∷ []
insertMode (suc k) m (m′ ∷ Γ) = m′ ∷ insertMode k m Γ

insert∋ⁱ :
  ∀ k m {Γ X p} →
  Γ ∋ⁱ X ∶ p →
  insertMode k m Γ ∋ⁱ raiseVarFrom k X ∶ p
insert∋ⁱ zero m x∈ = thereⁱ x∈
insert∋ⁱ (suc k) m hereⁱ = hereⁱ
insert∋ⁱ (suc k) m (thereⁱ x∈) = thereⁱ (insert∋ⁱ k m x∈)

targetOk-insertAt :
  ∀ k m {Γ A} →
  TargetOk Γ A →
  TargetOk (insertMode k m Γ) (renameᵗ (raiseVarFrom k) A)
targetOk-insertAt k m (ok-X x∈) = ok-X (insert∋ⁱ k m x∈)
targetOk-insertAt k m ok-｀ = ok-｀
targetOk-insertAt k m ok-‵ = ok-‵
targetOk-insertAt k m ok-★ = ok-★
targetOk-insertAt k m (ok-⇒ okA okB) =
  ok-⇒ (targetOk-insertAt k m okA) (targetOk-insertAt k m okB)
targetOk-insertAt k m {A = `∀ A} (ok-∀ okA)
    rewrite rename-raise-ext k A =
  ok-∀ (targetOk-insertAt (suc k) m okA)

targetOk-lift :
  ∀ m {Γ A} →
  TargetOk Γ A →
  TargetOk (m ∷ Γ) (⇑ᵗ A)
targetOk-lift m = targetOk-insertAt zero m

TargetSubstOk : VarPrecCtx → VarPrecCtx → Substᵗ → Set
TargetSubstOk Γ Γ′ σ =
  ∀ {X} → Γ ∋ⁱ X ∶ X⊑X → TargetOk Γ′ (σ X)

targetSubstOk-ext :
  ∀ {Γ Γ′ σ} →
  TargetSubstOk Γ Γ′ σ →
  TargetSubstOk (X⊑X ∷ Γ) (X⊑X ∷ Γ′) (extsᵗ σ)
targetSubstOk-ext h hereⁱ = ok-X hereⁱ
targetSubstOk-ext h (thereⁱ x∈) = targetOk-lift X⊑X (h x∈)

targetOk-subst :
  ∀ {Γ Γ′ σ A} →
  TargetSubstOk Γ Γ′ σ →
  TargetOk Γ A →
  TargetOk Γ′ (substᵗ σ A)
targetOk-subst h (ok-X x∈) = h x∈
targetOk-subst h ok-｀ = ok-｀
targetOk-subst h ok-‵ = ok-‵
targetOk-subst h ok-★ = ok-★
targetOk-subst h (ok-⇒ okA okB) =
  ok-⇒ (targetOk-subst h okA) (targetOk-subst h okB)
targetOk-subst h (ok-∀ okA) = ok-∀ (targetOk-subst (targetSubstOk-ext h) okA)

singleTargetSubstOk :
  ∀ {Γ T} →
  TargetOk Γ T →
  TargetSubstOk (X⊑X ∷ Γ) Γ (singleTyEnv T)
singleTargetSubstOk okT hereⁱ = okT
singleTargetSubstOk okT (thereⁱ x∈) = ok-X x∈

targetOk-subst-zero :
  ∀ {Γ B T} →
  TargetOk (X⊑X ∷ Γ) B →
  TargetOk Γ T →
  TargetOk Γ (B [ T ]ᵗ)
targetOk-subst-zero okB okT =
  targetOk-subst (singleTargetSubstOk okT) okB

applyTyEdit :
  ∀ {Γ A} →
  TyEdit Γ A →
  Σ[ A′ ∈ Ty ] TargetOk Γ A′
applyTyEdit (ty-star s) = ★ , ok-★
applyTyEdit {A = ＇ X} (ty-X x∈) = ＇ X , ok-X x∈
applyTyEdit {A = ｀ α} ty-｀ = ｀ α , ok-｀
applyTyEdit {A = ‵ ι} ty-‵ = ‵ ι , ok-‵
applyTyEdit ty-★ = ★ , ok-★
applyTyEdit (ty-⇒ eA eB) with applyTyEdit eA | applyTyEdit eB
applyTyEdit (ty-⇒ eA eB) | A′ , okA′ | B′ , okB′ =
  A′ ⇒ B′ , ok-⇒ okA′ okB′
applyTyEdit (ty-∀keep eA) with applyTyEdit eA
applyTyEdit (ty-∀keep eA) | A′ , okA′ = `∀ A′ , ok-∀ okA′
applyTyEdit (ty-∀drop eA) with applyTyEdit eA
applyTyEdit (ty-∀drop eA) | A′ , okA′ =
  dropTargetFrom zero okA′ , dropTargetFrom-ok zero okA′

applyTyEdit-type :
  ∀ {Γ A} →
  TyEdit Γ A →
  Ty
applyTyEdit-type e = proj₁ (applyTyEdit e)

tyEdit-ok :
  ∀ {Γ A} →
  (e : TyEdit Γ A) →
  TargetOk Γ (applyTyEdit-type e)
tyEdit-ok e = proj₂ (applyTyEdit e)

drop-raise< :
  ∀ k {X Δ} →
  k < suc Δ →
  raiseVarFrom k X < suc Δ →
  X < Δ
drop-raise< zero k<Δ (s<s X<Δ) = X<Δ
drop-raise< (suc k) {zero} {suc Δ} (s<s k<Δ) z<s = z<s
drop-raise< (suc k) {suc X} {suc Δ} (s<s k<Δ) (s<s X<Δ) =
  s<s (drop-raise< k k<Δ X<Δ)

drop-raise-WfTy :
  ∀ k {Δ Ψ A} →
  k < suc Δ →
  WfTy (suc Δ) Ψ (renameᵗ (raiseVarFrom k) A) →
  WfTy Δ Ψ A
drop-raise-WfTy k {A = ＇ X} k<Δ (wfVar X<Δ) =
  wfVar (drop-raise< k k<Δ X<Δ)
drop-raise-WfTy k {A = ｀ α} k<Δ (wfSeal α<Ψ) = wfSeal α<Ψ
drop-raise-WfTy k {A = ‵ ι} k<Δ wfBase = wfBase
drop-raise-WfTy k {A = ★} k<Δ wf★ = wf★
drop-raise-WfTy k {A = A ⇒ B} k<Δ (wf⇒ wfA wfB) =
  wf⇒ (drop-raise-WfTy k k<Δ wfA) (drop-raise-WfTy k k<Δ wfB)
drop-raise-WfTy k {A = `∀ A} k<Δ (wf∀ wfA) =
  wf∀ (drop-raise-WfTy (suc k) (s<s k<Δ)
    (subst (λ B → WfTy _ _ B) (rename-raise-ext k A) wfA))

drop-⇑ᵗ-WfTy :
  ∀ {Δ Ψ A} →
  WfTy (suc Δ) Ψ (⇑ᵗ A) →
  WfTy Δ Ψ A
drop-⇑ᵗ-WfTy = drop-raise-WfTy zero z<s

starEdit-wf :
  ∀ {Ψ Γ A} →
  WfTy (length Γ) Ψ A →
  StarEdit Γ A →
  WfTy (length Γ) Ψ ★
starEdit-wf wfA s = wf★

tyEdit-wf :
  ∀ {Ψ Γ A} →
  WfTy (length Γ) Ψ A →
  (e : TyEdit Γ A) →
  WfTy (length Γ) Ψ (applyTyEdit-type e)
tyEdit-wf wfA (ty-star s) = starEdit-wf wfA s
tyEdit-wf (wfVar X<Γ) (ty-X x∈) = wfVar X<Γ
tyEdit-wf (wfSeal α<Ψ) ty-｀ = wfSeal α<Ψ
tyEdit-wf wfBase ty-‵ = wfBase
tyEdit-wf wf★ ty-★ = wf★
tyEdit-wf (wf⇒ wfA wfB) (ty-⇒ eA eB) =
  wf⇒ (tyEdit-wf wfA eA) (tyEdit-wf wfB eB)
tyEdit-wf (wf∀ wfA) (ty-∀keep eA) = wf∀ (tyEdit-wf wfA eA)
tyEdit-wf (wf∀ wfA) (ty-∀drop eA) =
  dropTargetFrom-WfTy zero (tyEdit-wf wfA eA) (tyEdit-ok eA)

starEdit-⊑ :
  ∀ {Ψ Γ A} →
  WfTy (length Γ) Ψ A →
  (s : StarEdit Γ A) →
  Σ[ p ∈ Imp ] Ψ ∣ Γ ⊢ p ⦂ A ⊑ ★
starEdit-⊑ wf★ star-★ =
  Imprecision.id★ , Imprecision.⊢★-⊑-★
starEdit-⊑ (wfVar X<Γ) (star-X x∈) =
  Imprecision.‵ _ ! , Imprecision.⊢X-⊑-★ x∈
starEdit-⊑ wfα@(wfSeal α<Ψ) star-｀ =
  (Imprecision.idₛ _) Imprecision.! ,
  Imprecision.⊢A-⊑-★ (｀ _) (Imprecision.⊢α-⊑-α wfα)
starEdit-⊑ wfBase star-‵ =
  (Imprecision.idι _) Imprecision.! ,
  Imprecision.⊢A-⊑-★ (‵ _) Imprecision.⊢ι-⊑-ι
starEdit-⊑ (wf⇒ wfA wfB) (star-⇒ sA sB)
    with starEdit-⊑ wfA sA | starEdit-⊑ wfB sB
starEdit-⊑ (wf⇒ wfA wfB) (star-⇒ sA sB)
    | pA , pA⊢ | pB , pB⊢ =
  (pA Imprecision.↦ pB) Imprecision.! ,
  Imprecision.⊢A-⊑-★ ★⇒★
    (Imprecision.⊢A⇒B-⊑-A′⇒B′ pA⊢ pB⊢)

tyEdit-⊑ :
  ∀ {Ψ Γ A} →
  WfTy (length Γ) Ψ A →
  (e : TyEdit Γ A) →
  Σ[ p ∈ Imp ] Ψ ∣ Γ ⊢ p ⦂ A ⊑ applyTyEdit-type e
tyEdit-⊑ wfA (ty-star s) = starEdit-⊑ wfA s
tyEdit-⊑ (wfVar X<Γ) (ty-X x∈) =
  Imprecision.idₓ _ , Imprecision.⊢X-⊑-X x∈
tyEdit-⊑ wfα@(wfSeal α<Ψ) ty-｀ =
  Imprecision.idₛ _ , Imprecision.⊢α-⊑-α wfα
tyEdit-⊑ wfBase ty-‵ =
  Imprecision.idι _ , Imprecision.⊢ι-⊑-ι
tyEdit-⊑ wf★ ty-★ =
  Imprecision.id★ , Imprecision.⊢★-⊑-★
tyEdit-⊑ (wf⇒ wfA wfB) (ty-⇒ eA eB)
    with tyEdit-⊑ wfA eA | tyEdit-⊑ wfB eB
tyEdit-⊑ (wf⇒ wfA wfB) (ty-⇒ eA eB)
    | pA , pA⊢ | pB , pB⊢ =
  pA Imprecision.↦ pB ,
  Imprecision.⊢A⇒B-⊑-A′⇒B′ pA⊢ pB⊢
tyEdit-⊑ (wf∀ wfA) (ty-∀keep eA)
    with tyEdit-⊑ wfA eA
tyEdit-⊑ (wf∀ wfA) (ty-∀keep eA) | pA , pA⊢ =
  Imprecision.‵∀ pA , Imprecision.⊢∀A-⊑-∀B pA⊢
tyEdit-⊑ (wf∀ wfA) (ty-∀drop eA)
    with tyEdit-⊑ wfA eA | tyEdit-ok eA
tyEdit-⊑ {Γ = Γ} (wf∀ wfA) (ty-∀drop eA) | pA , pA⊢ | okA =
  Imprecision.ν pA ,
  Imprecision.⊢∀A-⊑-B
    (dropTargetFrom-WfTy zero (tyEdit-wf wfA eA) okA)
    (subst (λ C → _ ∣ _ ⊢ pA ⦂ _ ⊑ C)
      (dropTargetFrom-eq zero okA) pA⊢)

mutual
  insertStarEditAt :
    ∀ k m {Γ A} →
    StarEdit Γ A →
    StarEdit (insertMode k m Γ) (renameᵗ (raiseVarFrom k) A)
  insertStarEditAt k m star-★ = star-★
  insertStarEditAt k m (star-X x∈) = star-X (insert∋ⁱ k m x∈)
  insertStarEditAt k m star-｀ = star-｀
  insertStarEditAt k m star-‵ = star-‵
  insertStarEditAt k m (star-⇒ sA sB) =
    star-⇒ (insertStarEditAt k m sA) (insertStarEditAt k m sB)

  insertTyEditAt :
    ∀ k m {Γ A} →
    TyEdit Γ A →
    TyEdit (insertMode k m Γ) (renameᵗ (raiseVarFrom k) A)
  insertTyEditAt k m (ty-star s) = ty-star (insertStarEditAt k m s)
  insertTyEditAt k m (ty-X x∈) = ty-X (insert∋ⁱ k m x∈)
  insertTyEditAt k m ty-｀ = ty-｀
  insertTyEditAt k m ty-‵ = ty-‵
  insertTyEditAt k m ty-★ = ty-★
  insertTyEditAt k m (ty-⇒ eA eB) =
    ty-⇒ (insertTyEditAt k m eA) (insertTyEditAt k m eB)
  insertTyEditAt k m {A = `∀ A} (ty-∀keep eA)
      rewrite rename-raise-ext k A =
    ty-∀keep (insertTyEditAt (suc k) m eA)
  insertTyEditAt k m {A = `∀ A} (ty-∀drop eA)
      rewrite rename-raise-ext k A =
    ty-∀drop (insertTyEditAt (suc k) m eA)

liftTyEdit : ∀ m {Γ A} → TyEdit Γ A → TyEdit (m ∷ Γ) (⇑ᵗ A)
liftTyEdit m = insertTyEditAt zero m

TyEditPack : VarPrecCtx → Set
TyEditPack Γ = Σ[ A ∈ Ty ] TyEdit Γ A

TyEditCtx : VarPrecCtx → Set
TyEditCtx Γ = List (TyEditPack Γ)

sourceCtx : ∀ {Φ} → TyEditCtx Φ → Ctx
sourceCtx [] = []
sourceCtx ((A , e) ∷ Γπ) = A ∷ sourceCtx Γπ

targetCtx : ∀ {Φ} → TyEditCtx Φ → Ctx
targetCtx [] = []
targetCtx ((A , e) ∷ Γπ) = applyTyEdit-type e ∷ targetCtx Γπ

liftTyEditCtx : ∀ m {Φ} → TyEditCtx Φ → TyEditCtx (m ∷ Φ)
liftTyEditCtx m [] = []
liftTyEditCtx m ((A , e) ∷ Γπ) =
  (⇑ᵗ A , liftTyEdit m e) ∷ liftTyEditCtx m Γπ

infix 4 _∋ᴿ_⦂_
data _∋ᴿ_⦂_ {Φ : VarPrecCtx} : TyEditCtx Φ → Var → TyEditPack Φ → Set where

  Zᴿ : ∀ {Γ π} →
    (π ∷ Γ) ∋ᴿ zero ⦂ π

  Sᴿ : ∀ {Γ x π π′} →
    Γ ∋ᴿ x ⦂ π →
    (π′ ∷ Γ) ∋ᴿ suc x ⦂ π

lookupSourceCtx :
  ∀ {Φ Γπ x A} {e : TyEdit Φ A} →
  Γπ ∋ᴿ x ⦂ (A , e) →
  sourceCtx Γπ ∋ x ⦂ A
lookupSourceCtx Zᴿ = Z
lookupSourceCtx (Sᴿ x∈) = S (lookupSourceCtx x∈)

lookupTargetCtx :
  ∀ {Φ Γπ x A} {e : TyEdit Φ A} →
  Γπ ∋ᴿ x ⦂ (A , e) →
  targetCtx Γπ ∋ x ⦂ applyTyEdit-type e
lookupTargetCtx Zᴿ = Z
lookupTargetCtx (Sᴿ x∈) = S (lookupTargetCtx x∈)

data TargetTermOk (Γ : VarPrecCtx) : GTerm → Set where
  tt-var : ∀ {x} → TargetTermOk Γ (` x)
  tt-lam :
    ∀ {A M} →
    TargetOk Γ A →
    TargetTermOk Γ M →
    TargetTermOk Γ (ƛ A ⇒ M)
  tt-app :
    ∀ {L M} →
    TargetTermOk Γ L →
    TargetTermOk Γ M →
    TargetTermOk Γ (L · M)
  tt-Lam :
    ∀ {M} →
    TargetTermOk (X⊑X ∷ Γ) M →
    TargetTermOk Γ (Λ M)
  tt-tyapp :
    ∀ {M T} →
    TargetTermOk Γ M →
    TargetOk Γ T →
    TargetTermOk Γ (M `[ T ])
  tt-const : ∀ {κ} → TargetTermOk Γ ($ κ)
  tt-prim :
    ∀ {L M op} →
    TargetTermOk Γ L →
    TargetTermOk Γ M →
    TargetTermOk Γ (L ⊕[ op ] M)

dropTargetTermFrom :
  ∀ n {Γ M} →
  TargetTermOk (extend-X⊑X n (X⊑★ ∷ Γ)) M →
  GTerm
dropTargetTermFrom n {M = ` x} tt-var = ` x
dropTargetTermFrom n (tt-lam okA okM) =
  ƛ dropTargetFrom n okA ⇒ dropTargetTermFrom n okM
dropTargetTermFrom n (tt-app okL okM) =
  dropTargetTermFrom n okL · dropTargetTermFrom n okM
dropTargetTermFrom n (tt-Lam okM) = Λ (dropTargetTermFrom (suc n) okM)
dropTargetTermFrom n (tt-tyapp okM okT) =
  dropTargetTermFrom n okM `[ dropTargetFrom n okT ]
dropTargetTermFrom n {M = $ κ} tt-const = $ κ
dropTargetTermFrom n (tt-prim {op = op} okL okM) =
  dropTargetTermFrom n okL ⊕[ op ] dropTargetTermFrom n okM

dropTargetTermFrom-ok :
  ∀ n {Γ M}
    (okM : TargetTermOk (extend-X⊑X n (X⊑★ ∷ Γ)) M) →
  TargetTermOk (extend-X⊑X n Γ) (dropTargetTermFrom n okM)
dropTargetTermFrom-ok n tt-var = tt-var
dropTargetTermFrom-ok n (tt-lam okA okM) =
  tt-lam (dropTargetFrom-ok n okA) (dropTargetTermFrom-ok n okM)
dropTargetTermFrom-ok n (tt-app okL okM) =
  tt-app (dropTargetTermFrom-ok n okL) (dropTargetTermFrom-ok n okM)
dropTargetTermFrom-ok n (tt-Lam okM) =
  tt-Lam (dropTargetTermFrom-ok (suc n) okM)
dropTargetTermFrom-ok n (tt-tyapp okM okT) =
  tt-tyapp (dropTargetTermFrom-ok n okM) (dropTargetFrom-ok n okT)
dropTargetTermFrom-ok n tt-const = tt-const
dropTargetTermFrom-ok n (tt-prim okL okM) =
  tt-prim (dropTargetTermFrom-ok n okL) (dropTargetTermFrom-ok n okM)

plannedAppType : Ty → Ty
plannedAppType (A ⇒ B) = B
plannedAppType ★ = ★
plannedAppType A = ★

plannedAppTerm :
  ∀ {Φ} →
  (L′ M′ : GTerm) →
  TargetTermOk Φ L′ →
  TargetTermOk Φ M′ →
  (B′ : Ty) →
  TargetOk Φ B′ →
  Σ[ M′ ∈ GTerm ] Σ[ A′ ∈ Ty ] (TargetTermOk Φ M′ × TargetOk Φ A′)
plannedAppTerm L′ M′ okL okM (A ⇒ B) (ok-⇒ okA okB) =
  L′ · M′ , B , tt-app okL okM , okB
plannedAppTerm L′ M′ okL okM ★ ok-★ =
  L′ · M′ , ★ , tt-app okL okM , ok-★
plannedAppTerm L′ M′ okL okM (＇ X) (ok-X x∈) =
  L′ · M′ , ★ , tt-app okL okM , ok-★
plannedAppTerm L′ M′ okL okM (｀ α) ok-｀ =
  L′ · M′ , ★ , tt-app okL okM , ok-★
plannedAppTerm L′ M′ okL okM (‵ ι) ok-‵ =
  L′ · M′ , ★ , tt-app okL okM , ok-★
plannedAppTerm L′ M′ okL okM (`∀ B) (ok-∀ okB) =
  L′ · M′ , ★ , tt-app okL okM , ok-★

plannedTyAppKeepTerm :
  ∀ {Φ : VarPrecCtx} {T : Ty} →
  (M′ : GTerm) →
  TargetTermOk Φ M′ →
  (A′ : Ty) →
  TargetOk Φ A′ →
  TyEdit Φ T →
  Σ[ M′ ∈ GTerm ] Σ[ A′ ∈ Ty ] (TargetTermOk Φ M′ × TargetOk Φ A′)
plannedTyAppKeepTerm {T = T} M′ okM (`∀ B′) (ok-∀ okB′) πT =
  M′ `[ applyTyEdit-type πT ] ,
  B′ [ applyTyEdit-type πT ]ᵗ ,
  tt-tyapp okM (tyEdit-ok πT) ,
  targetOk-subst-zero okB′ (tyEdit-ok πT)
plannedTyAppKeepTerm {T = T} M′ okM A′ okA πT =
  M′ `[ applyTyEdit-type πT ] , A′ , tt-tyapp okM (tyEdit-ok πT) , okA

plannedTyAppDropTerm :
  ∀ {Φ : VarPrecCtx} {T : Ty} →
  (M′ : GTerm) →
  TargetTermOk Φ M′ →
  (A′ : Ty) →
  TargetOk Φ A′ →
  TyEdit Φ T →
  Σ[ M′ ∈ GTerm ] Σ[ A′ ∈ Ty ] (TargetTermOk Φ M′ × TargetOk Φ A′)
plannedTyAppDropTerm M′ okM A′ okA πT =
  M′ , A′ , okM , okA

data TermEdit (Φ : VarPrecCtx) (Γπ : TyEditCtx Φ) :
    GTerm → Ty → Set where
  term-var : ∀ {x P} →
    Γπ ∋ᴿ x ⦂ P →
    TermEdit Φ Γπ (` x) (proj₁ P)

  term-lam : ∀ {A M} →
    (πA : TyEdit Φ A) →
    ∀ {B} →
    TermEdit Φ ((A , πA) ∷ Γπ) M B →
    TermEdit Φ Γπ (ƛ A ⇒ M) (A ⇒ B)

  term-app : ∀ {L M A B A′} →
    TermEdit Φ Γπ L (A ⇒ B) →
    TermEdit Φ Γπ M A′ →
    TermEdit Φ Γπ (L · M) B

  term-app★ : ∀ {L M A′} →
    TermEdit Φ Γπ L ★ →
    TermEdit Φ Γπ M A′ →
    TermEdit Φ Γπ (L · M) ★

  term-LamKeep : ∀ {M A} →
    TermEdit (X⊑X ∷ Φ) (liftTyEditCtx X⊑X Γπ) M A →
    TermEdit Φ Γπ (Λ M) (`∀ A)

  term-LamDrop : ∀ {M A} →
    TermEdit (X⊑★ ∷ Φ) (liftTyEditCtx X⊑★ Γπ) M A →
    TermEdit Φ Γπ (Λ M) (`∀ A)

  term-tyappKeep : ∀ {M T B} →
    TermEdit Φ Γπ M (`∀ B) →
    TyEdit Φ T →
    TermEdit Φ Γπ (M `[ T ]) (B [ T ]ᵗ)

  term-tyappDrop : ∀ {M T B} →
    TermEdit Φ Γπ M (`∀ B) →
    TyEdit Φ T →
    TermEdit Φ Γπ (M `[ T ]) (B [ T ]ᵗ)

  term-const : ∀ {κ} →
    TermEdit Φ Γπ ($ κ) (constTy κ)

  term-prim : ∀ {L M op} →
    ∀ {A B} →
    TermEdit Φ Γπ L A →
    TermEdit Φ Γπ M B →
    TermEdit Φ Γπ (L ⊕[ op ] M) (‵ `ℕ)

applyTermEdit :
  ∀ {Φ A} →
  (Γπ : TyEditCtx Φ) →
  (M : GTerm) →
  TermEdit Φ Γπ M A →
  Σ[ M′ ∈ GTerm ] Σ[ A′ ∈ Ty ] (TargetTermOk Φ M′ × TargetOk Φ A′)
applyTermEdit Γπ (` x) (term-var {P = A , e} x∈) =
  ` x , applyTyEdit-type e , tt-var , tyEdit-ok e
applyTermEdit Γπ (ƛ A ⇒ M) (term-lam πA ρM)
    with applyTermEdit ((A , πA) ∷ Γπ) M ρM
applyTermEdit Γπ (ƛ A ⇒ M) (term-lam πA ρM)
    | M′ , B′ , okM′ , okB′ =
  (ƛ applyTyEdit-type πA ⇒ M′) ,
  (applyTyEdit-type πA ⇒ B′) ,
  tt-lam (tyEdit-ok πA) okM′ ,
  ok-⇒ (tyEdit-ok πA) okB′
applyTermEdit Γπ (L · M) (term-app ρL ρM)
    with applyTermEdit Γπ L ρL | applyTermEdit Γπ M ρM
applyTermEdit Γπ (L · M) (term-app ρL ρM)
    | L′ , A′⇒B′ , okL′ , okA′⇒B′ | M′ , C′ , okM′ , okC′ =
  plannedAppTerm L′ M′ okL′ okM′ A′⇒B′ okA′⇒B′
applyTermEdit Γπ (L · M) (term-app★ ρL ρM)
    with applyTermEdit Γπ L ρL | applyTermEdit Γπ M ρM
applyTermEdit Γπ (L · M) (term-app★ ρL ρM)
    | L′ , A′ , okL′ , okA′ | M′ , C′ , okM′ , okC′ =
  L′ · M′ , ★ , tt-app okL′ okM′ , ok-★
applyTermEdit Γπ (Λ M) (term-LamKeep ρM)
    with applyTermEdit (liftTyEditCtx X⊑X Γπ) M ρM
applyTermEdit Γπ (Λ M) (term-LamKeep ρM)
    | M′ , A′ , okM′ , okA′ =
  Λ M′ , `∀ A′ , tt-Lam okM′ , ok-∀ okA′
applyTermEdit Γπ (Λ M) (term-LamDrop ρM)
    with applyTermEdit (liftTyEditCtx X⊑★ Γπ) M ρM
applyTermEdit Γπ (Λ M) (term-LamDrop ρM)
    | M′ , A′ , okM′ , okA′ =
  dropTargetTermFrom zero okM′ ,
  dropTargetFrom zero okA′ ,
  dropTargetTermFrom-ok zero okM′ ,
  dropTargetFrom-ok zero okA′
applyTermEdit Γπ (M `[ T ]) (term-tyappKeep ρM πT)
    with applyTermEdit Γπ M ρM
applyTermEdit Γπ (M `[ T ]) (term-tyappKeep ρM πT)
    | M′ , A′ , okM′ , okA′ =
  plannedTyAppKeepTerm M′ okM′ A′ okA′ πT
applyTermEdit Γπ (M `[ T ]) (term-tyappDrop ρM πT)
    with applyTermEdit Γπ M ρM
applyTermEdit Γπ (M `[ T ]) (term-tyappDrop ρM πT)
    | M′ , A′ , okM′ , okA′ =
  plannedTyAppDropTerm M′ okM′ A′ okA′ πT
applyTermEdit Γπ ($ (κℕ n)) term-const =
  $ (κℕ n) , ‵ `ℕ , tt-const , ok-‵
applyTermEdit Γπ (L ⊕[ op ] M) (term-prim ρL ρM)
    with applyTermEdit Γπ L ρL | applyTermEdit Γπ M ρM
applyTermEdit Γπ (L ⊕[ op ] M) (term-prim ρL ρM)
    | L′ , A′ , okL′ , okA′ | M′ , B′ , okM′ , okB′ =
  (L′ ⊕[ op ] M′) , ‵ `ℕ , tt-prim okL′ okM′ , ok-‵
