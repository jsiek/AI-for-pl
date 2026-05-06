module proof.PreservationBetaUpNu where

-- File Charter:
--   * Standalone preservation proof slice for the store-allocating β-up-ν
--     redex in PolyConvert.
--   * Proves the required fresh-ν imprecision opening lemma used by
--     `proof.Preservation`.
--   * Depends on seal/store weakening for terms, but not on the
--     store-threaded preservation induction hypothesis.

open import Data.Bool using (false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)
open import Data.Nat.Properties using (<-≤-trans; n≤1+n; n<1+n; _≟_)
open import Data.Product using (Σ; _,_; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; subst; sym; trans)

open import Types
open import proof.TypeProperties using
  ( TySubstWf
  ; WfTy-weakenˢ
  ; renameᵗ-ground
  ; substᵗ-ground
  ; substᵗ-preserves-WfTy
  )
open import Store
open import Imprecision
open import Terms
open import proof.PreservationWkTerm using (wk-term)

------------------------------------------------------------------------
-- Local fresh-opening dependency
------------------------------------------------------------------------

len<suc-StoreWf :
  ∀ {Δ Ψ}{Σ : Store} →
  StoreWf Δ Ψ Σ →
  length Σ < suc Ψ
len<suc-StoreWf {Ψ = Ψ} wfΣ rewrite storeWf-length wfΣ = n<1+n Ψ

length-plains[] :
  ∀ Δ →
  length (plains Δ []) ≡ Δ
length-plains[] zero = refl
length-plains[] (suc Δ) = cong suc (length-plains[] Δ)

cong-⊢⊑ :
  ∀ {Ψ Γ p A A′ B B′} →
  A ≡ A′ →
  B ≡ B′ →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  Ψ ∣ Γ ⊢ p ⦂ A′ ⊑ B′
cong-⊢⊑ refl refl p⊢ = p⊢

cong-⊢⊑-raw :
  ∀ {Ψ Γ p p′ A A′ B B′} →
  p ≡ p′ →
  A ≡ A′ →
  B ≡ B′ →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  Ψ ∣ Γ ⊢ p′ ⦂ A′ ⊑ B′
cong-⊢⊑-raw refl refl refl p⊢ = p⊢

------------------------------------------------------------------------
-- Opening a ν-bound imprecision variable with a fresh seal
------------------------------------------------------------------------

raiseVarFrom : TyVar → TyVar → TyVar
raiseVarFrom zero X = suc X
raiseVarFrom (suc k) zero = zero
raiseVarFrom (suc k) (suc X) = suc (raiseVarFrom k X)

raiseVarFrom-≢ :
  ∀ k X →
  raiseVarFrom k X ≡ k →
  ⊥
raiseVarFrom-≢ zero X ()
raiseVarFrom-≢ (suc k) zero ()
raiseVarFrom-≢ (suc k) (suc X) eq =
  raiseVarFrom-≢ k X (suc-injective eq)

raise-ext :
  ∀ k X →
  extᵗ (raiseVarFrom k) X ≡ raiseVarFrom (suc k) X
raise-ext k zero = refl
raise-ext k (suc X) = refl

rename-raise-ext :
  ∀ k A →
  renameᵗ (extᵗ (raiseVarFrom k)) A ≡
  renameᵗ (raiseVarFrom (suc k)) A
rename-raise-ext k A = rename-cong (raise-ext k) A

rename-raise-⇑ᵗ :
  ∀ k A →
  renameᵗ (raiseVarFrom (suc k)) (⇑ᵗ A) ≡
  ⇑ᵗ (renameᵗ (raiseVarFrom k) A)
rename-raise-⇑ᵗ k A =
  trans
    (rename-cong (λ X → sym (raise-ext k X)) (⇑ᵗ A))
    (sym (renameᵗ-suc-comm (raiseVarFrom k) A))

occurs-raise :
  ∀ k X A →
  occurs (raiseVarFrom k X) (renameᵗ (raiseVarFrom k) A) ≡
  occurs X A
occurs-raise k X (＇ Y) with X ≟ Y | raiseVarFrom k X ≟ raiseVarFrom k Y
occurs-raise k X (＇ .X) | yes refl | yes refl = refl
occurs-raise k X (＇ .X) | yes refl | no neq = ⊥-elim (neq refl)
occurs-raise k X (＇ Y) | no neq | yes eq =
  ⊥-elim (neq (raiseVarFrom-injective k eq))
  where
    raiseVarFrom-injective :
      ∀ k {X Y} →
      raiseVarFrom k X ≡ raiseVarFrom k Y →
      X ≡ Y
    raiseVarFrom-injective zero eq = suc-injective eq
    raiseVarFrom-injective (suc k) {zero} {zero} eq = refl
    raiseVarFrom-injective (suc k) {zero} {suc Y} ()
    raiseVarFrom-injective (suc k) {suc X} {zero} ()
    raiseVarFrom-injective (suc k) {suc X} {suc Y} eq =
      cong suc (raiseVarFrom-injective k (suc-injective eq))
occurs-raise k X (＇ Y) | no neq | no neq′ = refl
occurs-raise k X (｀ α) = refl
occurs-raise k X (‵ ι) = refl
occurs-raise k X ★ = refl
occurs-raise k X (A ⇒ B)
  rewrite occurs-raise k X A
        | occurs-raise k X B = refl
occurs-raise k X (`∀ A)
  rewrite rename-raise-ext k A =
  occurs-raise (suc k) (suc X) A

occurs-raise-fresh :
  ∀ k A →
  occurs k (renameᵗ (raiseVarFrom k) A) ≡ false
occurs-raise-fresh k (＇ X) with k ≟ raiseVarFrom k X
occurs-raise-fresh k (＇ X) | yes eq =
  ⊥-elim (raiseVarFrom-≢ k X (sym eq))
occurs-raise-fresh k (＇ X) | no neq = refl
occurs-raise-fresh k (｀ α) = refl
occurs-raise-fresh k (‵ ι) = refl
occurs-raise-fresh k ★ = refl
occurs-raise-fresh k (A ⇒ B)
  rewrite occurs-raise-fresh k A
        | occurs-raise-fresh k B = refl
occurs-raise-fresh k (`∀ A)
  rewrite rename-raise-ext k A =
  occurs-raise-fresh (suc k) A

occurs-substVarFrom-var-< :
  ∀ k X Y T →
  X < k →
  occurs X (plainSubstVarFrom k T Y) ≡ occurs X (＇ Y)
occurs-substVarFrom-var-< zero X Y T ()
occurs-substVarFrom-var-< (suc k) zero zero T z<s = refl
occurs-substVarFrom-var-< (suc k) zero (suc Y) T z<s
  rewrite occurs-raise-fresh zero (plainSubstVarFrom k T Y) = refl
occurs-substVarFrom-var-< (suc k) (suc X) zero T (s<s X<k) = refl
occurs-substVarFrom-var-< (suc k) (suc X) (suc Y) T (s<s X<k)
  rewrite occurs-raise zero X (plainSubstVarFrom k T Y)
        | occurs-substVarFrom-var-< k X Y T X<k
        | occurs-raise zero X (＇ Y) = refl

occurs-substVarFrom-<-ty :
  ∀ A k X T →
  X < k →
  occurs X (substᵗ (plainSubstVarFrom k T) A) ≡ occurs X A
occurs-substVarFrom-<-ty (＇ Y) k X T X<k =
  occurs-substVarFrom-var-< k X Y T X<k
occurs-substVarFrom-<-ty (｀ α) k X T X<k = refl
occurs-substVarFrom-<-ty (‵ ι) k X T X<k = refl
occurs-substVarFrom-<-ty ★ k X T X<k = refl
occurs-substVarFrom-<-ty (A ⇒ B) k X T X<k
  rewrite occurs-substVarFrom-<-ty A k X T X<k
        | occurs-substVarFrom-<-ty B k X T X<k = refl
occurs-substVarFrom-<-ty (`∀ A) k X T X<k =
  occurs-substVarFrom-<-ty A (suc k) (suc X) T (s<s X<k)

occurs-substVarFrom-< :
  ∀ k X T A →
  X < k →
  occurs X (substᵗ (plainSubstVarFrom k T) A) ≡ occurs X A
occurs-substVarFrom-< k X T A =
  occurs-substVarFrom-<-ty A k X T

VarSubst : SealCtx → ICtx → Ty → VarMode → Set
VarSubst Ψ Γ A plain = Ψ ∣ Γ ⊢ reflImp A ⦂ A ⊑ A
VarSubst Ψ Γ A ν-bound = Ψ ∣ Γ ⊢ starImp A ⦂ A ⊑ ★

renameImp-refl :
  ∀ ρ A →
  renameImp ρ (reflImp A) ≡ reflImp (renameᵗ ρ A)
renameImp-refl ρ (＇ X) = refl
renameImp-refl ρ (｀ α) = refl
renameImp-refl ρ (‵ ι) = refl
renameImp-refl ρ ★ = refl
renameImp-refl ρ (A ⇒ B) =
  cong₂ A⇒B⊑A′⇒B′ (renameImp-refl ρ A) (renameImp-refl ρ B)
renameImp-refl ρ (`∀ A) = cong `∀A⊑∀B (renameImp-refl (extᵗ ρ) A)

renameImp-star :
  ∀ ρ A →
  renameImp ρ (starImp A) ≡ starImp (renameᵗ ρ A)
renameImp-star ρ (＇ X) = refl
renameImp-star ρ (｀ α) = refl
renameImp-star ρ (‵ ι) = refl
renameImp-star ρ ★ = refl
renameImp-star ρ (A ⇒ B) =
  cong A⊑★
    (cong₂ A⇒B⊑A′⇒B′ (renameImp-star ρ A) (renameImp-star ρ B))
renameImp-star ρ (`∀ A) = cong (`∀A⊑B ★) (renameImp-star (extᵗ ρ) A)

renameImp-cong :
  ∀ {ρ ρ′} →
  (∀ X → ρ X ≡ ρ′ X) →
  (p : Imp) →
  renameImp ρ p ≡ renameImp ρ′ p
renameImp-cong h ★⊑★ = refl
renameImp-cong h (X⊑★ X) = cong X⊑★ (h X)
renameImp-cong h (A⊑★ p) = cong A⊑★ (renameImp-cong h p)
renameImp-cong h (X⊑X X) = cong X⊑X (h X)
renameImp-cong h (α⊑α α) = refl
renameImp-cong h (ι⊑ι ι) = refl
renameImp-cong h (A⇒B⊑A′⇒B′ p q) =
  cong₂ A⇒B⊑A′⇒B′ (renameImp-cong h p) (renameImp-cong h q)
renameImp-cong {ρ = ρ} {ρ′ = ρ′} h (`∀A⊑∀B p) =
  cong `∀A⊑∀B (renameImp-cong h′ p)
  where
    h′ : ∀ X → extᵗ ρ X ≡ extᵗ ρ′ X
    h′ zero = refl
    h′ (suc X) = cong suc (h X)
renameImp-cong {ρ = ρ} {ρ′ = ρ′} h (`∀A⊑B B p) =
  cong₂ `∀A⊑B (rename-cong h B) (renameImp-cong h′ p)
  where
    h′ : ∀ X → extᵗ ρ X ≡ extᵗ ρ′ X
    h′ zero = refl
    h′ (suc X) = cong suc (h X)

rename∋-insert :
  ∀ {Φ Γ X m m′} →
  (Φ ++ Γ) ∋ X ∶ m →
  (Φ ++ m′ ∷ Γ) ∋ raiseVarFrom (length Φ) X ∶ m
rename∋-insert {Φ = []} x∈ = there x∈
rename∋-insert {Φ = m₀ ∷ Φ} here = here
rename∋-insert {Φ = m₀ ∷ Φ} (there x∈) =
  there (rename∋-insert {Φ = Φ} x∈)

lookup-mode :
  ∀ Γ {X} →
  X < length Γ →
  Σ VarMode (λ m → Γ ∋ X ∶ m)
lookup-mode [] ()
lookup-mode (m ∷ Γ) {zero} z<s = m , here
lookup-mode (m ∷ Γ) {suc X} (s<s X<Γ) with lookup-mode Γ X<Γ
lookup-mode (m ∷ Γ) {suc X} (s<s X<Γ) | m′ , x∈ = m′ , there x∈

raiseWf :
  ∀ {Φ Γ m′} →
  TyRenameWf (length (Φ ++ Γ)) (length (Φ ++ m′ ∷ Γ))
    (raiseVarFrom (length Φ))
raiseWf {Φ = Φ} X<len =
  ∋→< (rename∋-insert {Φ = Φ} (proj₂ (lookup-mode _ X<len)))

wkImpAt :
  ∀ {Ψ Φ Γ p A B m′} →
  Ψ ∣ (Φ ++ Γ) ⊢ p ⦂ A ⊑ B →
  Ψ ∣ (Φ ++ m′ ∷ Γ) ⊢
    renameImp (raiseVarFrom (length Φ)) p ⦂
    renameᵗ (raiseVarFrom (length Φ)) A ⊑
    renameᵗ (raiseVarFrom (length Φ)) B
wkImpAt {Φ = Φ} ⊑-★★ = ⊑-★★
wkImpAt {Φ = Φ} (⊑-★ν xν) = ⊑-★ν (rename∋-insert {Φ = Φ} xν)
wkImpAt {Φ = Φ} (⊑-★ g p⊢) =
  ⊑-★ (renameᵗ-ground _ g) (wkImpAt {Φ = Φ} p⊢)
wkImpAt {Φ = Φ} (⊑-＇ x∈) =
  ⊑-＇ (rename∋-insert {Φ = Φ} x∈)
wkImpAt {Φ = Φ} (⊑-｀ (wfSeal α<Ψ)) = ⊑-｀ (wfSeal α<Ψ)
wkImpAt {Φ = Φ} ⊑-‵ = ⊑-‵
wkImpAt {Φ = Φ} (⊑-⇒ p⊢ q⊢) =
  ⊑-⇒ (wkImpAt {Φ = Φ} p⊢) (wkImpAt {Φ = Φ} q⊢)
wkImpAt {Φ = Φ} (⊑-∀ p⊢) =
  ⊑-∀
    (cong-⊢⊑-raw
      (sym (renameImp-cong (raise-ext (length Φ)) _))
      (sym (rename-raise-ext (length Φ) _))
      (sym (rename-raise-ext (length Φ) _))
      (wkImpAt {Φ = plain ∷ Φ} p⊢))
wkImpAt {Φ = Φ} (⊑-ν {A = A} {B = B} wfB p⊢) =
  ⊑-ν
    (renameᵗ-preserves-WfTy wfB (raiseWf {Φ = Φ}))
    (cong-⊢⊑-raw
      (sym (renameImp-cong (raise-ext (length Φ)) _))
      (sym (rename-raise-ext (length Φ) A))
      (rename-raise-⇑ᵗ (length Φ) B)
      (wkImpAt {Φ = ν-bound ∷ Φ} p⊢))

wk-VarSubst :
  ∀ {Ψ Γ A m m′} →
  VarSubst Ψ Γ A m →
  VarSubst Ψ (m′ ∷ Γ) (⇑ᵗ A) m
wk-VarSubst {m = plain} h =
  cong-⊢⊑-raw (renameImp-refl suc _) refl refl
    (wkImpAt {Φ = []} h)
wk-VarSubst {m = ν-bound} h =
  cong-⊢⊑-raw (renameImp-star suc _) refl refl
    (wkImpAt {Φ = []} h)

plain-var-subst :
  ∀ {Δ Ψ X m} →
  plains Δ [] ∋ X ∶ m →
  VarSubst Ψ (plains Δ []) (＇ X) m
plain-var-subst {Δ = zero} ()
plain-var-subst {Δ = suc Δ} here = ⊑-＇ here
plain-var-subst {Δ = suc Δ} {Ψ = Ψ} (there x∈) =
  wk-VarSubst {m′ = plain} (plain-var-subst {Ψ = Ψ} x∈)

subst-var-prefix :
  ∀ {Δ Ψ}{Σ : Store}{Φ X m} →
  StoreWf Δ Ψ Σ →
  (Φ ++ ν-bound ∷ plains Δ []) ∋ X ∶ m →
  VarSubst (suc Ψ) (Φ ++ plains Δ [])
    (plainSubstVarFrom (length Φ) (｀ (length Σ)) X) m
subst-var-prefix {Φ = []} wfΣ here =
  ⊑-★ (｀ _) (⊑-｀ (wfSeal (len<suc-StoreWf wfΣ)))
subst-var-prefix {Ψ = Ψ} {Φ = []} wfΣ (there x∈) =
  plain-var-subst {Ψ = suc Ψ} x∈
subst-var-prefix {Φ = plain ∷ Φ} wfΣ here = ⊑-＇ here
subst-var-prefix {Φ = plain ∷ Φ} wfΣ (there x∈) =
  wk-VarSubst (subst-var-prefix {Φ = Φ} wfΣ x∈)
subst-var-prefix {Φ = ν-bound ∷ Φ} wfΣ here = ⊑-★ν here
subst-var-prefix {Φ = ν-bound ∷ Φ} wfΣ (there x∈) =
  wk-VarSubst (subst-var-prefix {Φ = Φ} wfΣ x∈)

varSubst-wf :
  ∀ {Ψ Γ A m} →
  VarSubst Ψ Γ A m →
  WfTy (length Γ) Ψ A
varSubst-wf {m = plain} h = ⊑-src-wf h
varSubst-wf {m = ν-bound} h = ⊑-src-wf h

substWf-prefix :
  ∀ {Δ Ψ}{Σ : Store}{Φ} →
  StoreWf Δ Ψ Σ →
  TySubstWf
    (length (Φ ++ ν-bound ∷ plains Δ []))
    (length (Φ ++ plains Δ []))
    (suc Ψ)
    (plainSubstVarFrom (length Φ) (｀ (length Σ)))
substWf-prefix {Φ = Φ} wfΣ X<len =
  varSubst-wf (subst-var-prefix {Φ = Φ} wfΣ (proj₂ (lookup-mode _ X<len)))

open-fresh-ν⊑-prefix :
  ∀ {Δ Ψ}{Σ : Store}{Φ : ICtx}{A B : Ty}{p : Imp} →
  StoreWf Δ Ψ Σ →
  Ψ ∣ (Φ ++ ν-bound ∷ plains Δ []) ⊢ p ⦂ A ⊑ B →
  suc Ψ ∣ (Φ ++ plains Δ []) ⊢
    substPlainAtImp (length Φ) (｀ (length Σ)) p ⦂
    substᵗ (plainSubstVarFrom (length Φ) (｀ (length Σ))) A ⊑
    substᵗ (plainSubstVarFrom (length Φ) (｀ (length Σ))) B
open-fresh-ν⊑-prefix wfΣ ⊑-★★ = ⊑-★★
open-fresh-ν⊑-prefix wfΣ (⊑-★ν xν) = subst-var-prefix wfΣ xν
open-fresh-ν⊑-prefix wfΣ (⊑-★ g p⊢) =
  ⊑-★ (substᵗ-ground _ g) (open-fresh-ν⊑-prefix wfΣ p⊢)
open-fresh-ν⊑-prefix {Φ = Φ} wfΣ (⊑-＇ x∈) =
  subst-var-prefix {Φ = Φ} wfΣ x∈
open-fresh-ν⊑-prefix wfΣ (⊑-｀ (wfSeal α<Ψ)) =
  ⊑-｀ (wfSeal (<-≤-trans α<Ψ (n≤1+n _)))
open-fresh-ν⊑-prefix wfΣ ⊑-‵ = ⊑-‵
open-fresh-ν⊑-prefix wfΣ (⊑-⇒ p⊢ q⊢) =
  ⊑-⇒ (open-fresh-ν⊑-prefix wfΣ p⊢)
       (open-fresh-ν⊑-prefix wfΣ q⊢)
open-fresh-ν⊑-prefix {Φ = Φ} wfΣ (⊑-∀ p⊢) =
  ⊑-∀ (open-fresh-ν⊑-prefix {Φ = plain ∷ Φ} wfΣ p⊢)
open-fresh-ν⊑-prefix {Φ = Φ} wfΣ (⊑-ν {A = A} {B = B} wfB p⊢) =
  ⊑-ν
    (substᵗ-preserves-WfTy
      (WfTy-weakenˢ wfB (n≤1+n _))
      (substWf-prefix {Φ = Φ} wfΣ))
    (cong-⊢⊑
      refl
      (substᵗ-suc-renameᵗ-suc
        (plainSubstVarFrom (length Φ) (｀ _))
        B)
      (open-fresh-ν⊑-prefix {Φ = ν-bound ∷ Φ} wfΣ p⊢))

open-fresh-ν⊑ :
  ∀ {Δ Ψ}{Σ : Store}{A B : Ty}{p : Imp} →
  StoreWf Δ Ψ Σ →
  Ψ ∣ (ν-bound ∷ plains Δ []) ⊢ p ⦂ A ⊑ ⇑ᵗ B →
  suc Ψ ∣ plains Δ [] ⊢ p [ ｀ (length Σ) ]⊑ ⦂
    (A [ ｀ (length Σ) ]ᵗ) ⊑ B
open-fresh-ν⊑ {Σ = Σ} {B = B} wfΣ p⊢ =
  cong-⊢⊑ refl (open-renᵗ-suc B (｀ (length Σ)))
    (open-fresh-ν⊑-prefix {Φ = []} wfΣ p⊢)

------------------------------------------------------------------------
-- β-up-ν preservation
------------------------------------------------------------------------

preserve-β-up-ν :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{A B : Ty}{p : Imp} →
  StoreWf Δ Ψ Σ →
  Value V →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ V ⇑ (`∀A⊑B B p) ⦂ A →
  Δ ∣ suc Ψ ∣ ((length Σ , ★) ∷ Σ) ∣ Γ ⊢
    ((V ⦂∀ (src⊑ p) [ ｀ (length Σ) ]) ⇑
      (p [ ｀ (length Σ) ]⊑)) ⦂ A
preserve-β-up-ν {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {V = V} {p = p} wfΣ vV
  (⊢up (⊑-ν {A = Aν} wfB p⊢) V⊢) =
  ⊢up
    (cong-⊢⊑
      (cong (λ A → A [ ｀ (length Σ) ]ᵗ) (sym (src⊑-correct p⊢)))
      refl
      (open-fresh-ν⊑ wfΣ p⊢))
    (⊢• V⊢′
      (WfTy-weakenˢ wf-src (n≤1+n Ψ))
      (wfSeal (len<suc-StoreWf wfΣ)))
  where
    wf-src : WfTy (suc Δ) Ψ (src⊑ p)
    wf-src =
      subst
        (λ A → WfTy (suc Δ) Ψ A)
        (sym (src⊑-correct p⊢))
        (subst
          (λ n → WfTy n Ψ Aν)
          (cong suc (length-plains[] Δ))
          (⊑-src-wf p⊢))

    V⊢↑ :
      _ ∣ suc Ψ ∣ ((length Σ , ★) ∷ Σ) ∣ _ ⊢ V ⦂ `∀ _
    V⊢↑ = wk-term (n≤1+n Ψ) (drop ⊆ˢ-refl) V⊢

    V⊢′ :
      _ ∣ suc Ψ ∣ ((length Σ , ★) ∷ Σ) ∣ _ ⊢
      V ⦂ `∀ (src⊑ p)
    V⊢′ =
      cong-⊢⦂ refl refl refl
        (cong `∀ (sym (src⊑-correct p⊢)))
        V⊢↑
