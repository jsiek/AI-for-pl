module proof.ImprecisionProperties where

-- File Charter:
--   * Properties of type imprecision.
--   * Includes seal-context weakening and small structural facts about
--     imprecision contexts.
--   * Includes insertion/opening helpers for imprecision evidence.
--   * Includes structural transitivity for type imprecision.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Nat using (_<_; _≤_; zero; suc; z<s; s<s)
open import Data.Nat.Properties using (<-≤-trans; n≤1+n)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import Types
open import Imprecision
open import Store
open import proof.TypeProperties
open import proof.StoreProperties using (len<suc-StoreWf)

wk-⊑ :
  ∀ {Ψ Ψ′ Γᵢ p A B} →
  Ψ ≤ Ψ′ →
  Ψ ∣ Γᵢ ⊢ p ⦂ A ⊑ B →
  Ψ′ ∣ Γᵢ ⊢ p ⦂ A ⊑ B
wk-⊑ Ψ≤Ψ′ ⊢★-⊑-★ = ⊢★-⊑-★
wk-⊑ Ψ≤Ψ′ (⊢X-⊑-★ xν) = ⊢X-⊑-★ xν
wk-⊑ Ψ≤Ψ′ (⊢A-⊑-★ g p⊢) = ⊢A-⊑-★ g (wk-⊑ Ψ≤Ψ′ p⊢)
wk-⊑ Ψ≤Ψ′ (⊢X-⊑-X x∈) = ⊢X-⊑-X x∈
wk-⊑ Ψ≤Ψ′ (⊢α-⊑-α wfα) = ⊢α-⊑-α (WfTy-weakenˢ wfα Ψ≤Ψ′)
wk-⊑ Ψ≤Ψ′ ⊢ι-⊑-ι = ⊢ι-⊑-ι
wk-⊑ Ψ≤Ψ′ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  ⊢A⇒B-⊑-A′⇒B′ (wk-⊑ Ψ≤Ψ′ p⊢) (wk-⊑ Ψ≤Ψ′ q⊢)
wk-⊑ Ψ≤Ψ′ (⊢∀A-⊑-∀B p⊢) = ⊢∀A-⊑-∀B (wk-⊑ Ψ≤Ψ′ p⊢)
wk-⊑ Ψ≤Ψ′ (⊢∀A-⊑-B wfB p⊢) =
  ⊢∀A-⊑-B (WfTy-weakenˢ wfB Ψ≤Ψ′) (wk-⊑ Ψ≤Ψ′ p⊢)

wk-⊒ :
  ∀ {Ψ Ψ′ Γᵢ p A B} →
  Ψ ≤ Ψ′ →
  Ψ ∣ Γᵢ ⊢ p ⦂ A ⊒ B →
  Ψ′ ∣ Γᵢ ⊢ p ⦂ A ⊒ B
wk-⊒ = wk-⊑

length-plains[] :
  ∀ Δ →
  length (plains Δ []) ≡ Δ
length-plains[] zero = refl
length-plains[] (suc Δ) = cong suc (length-plains[] Δ)

⊑-src-wf-plains :
  ∀ {Δ p A B} →
  0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B →
  WfTy Δ 0 A
⊑-src-wf-plains {Δ = Δ} p⊢ =
  subst (λ n → WfTy n 0 _) (length-plains[] Δ) (⊑-src-wf p⊢)

⊑-tgt-wf-plains :
  ∀ {Δ p A B} →
  0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B →
  WfTy Δ 0 B
⊑-tgt-wf-plains {Δ = Δ} p⊢ =
  subst (λ n → WfTy n 0 _) (length-plains[] Δ) (⊑-tgt-wf p⊢)

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

VarSubst : SealCtx → VarPrecCtx → Ty → VarPrec → Set
VarSubst Ψ Γ A X⊑X = Ψ ∣ Γ ⊢ reflImp A ⦂ A ⊑ A
VarSubst Ψ Γ A X⊑★ = Ψ ∣ Γ ⊢ starImp A ⦂ A ⊑ ★

renameImp-refl :
  ∀ ρ A →
  renameImp ρ (reflImp A) ≡ reflImp (renameᵗ ρ A)
renameImp-refl ρ (＇ X) = refl
renameImp-refl ρ (｀ α) = refl
renameImp-refl ρ (‵ ι) = refl
renameImp-refl ρ ★ = refl
renameImp-refl ρ (A ⇒ B) =
  cong₂ A⇒B-⊑-A′⇒B′ (renameImp-refl ρ A) (renameImp-refl ρ B)
renameImp-refl ρ (`∀ A) = cong ∀A-⊑-∀B (renameImp-refl (extᵗ ρ) A)

renameImp-star :
  ∀ ρ A →
  renameImp ρ (starImp A) ≡ starImp (renameᵗ ρ A)
renameImp-star ρ (＇ X) = refl
renameImp-star ρ (｀ α) = refl
renameImp-star ρ (‵ ι) = refl
renameImp-star ρ ★ = refl
renameImp-star ρ (A ⇒ B) =
  cong A-⊑-★
    (cong₂ A⇒B-⊑-A′⇒B′ (renameImp-star ρ A) (renameImp-star ρ B))
renameImp-star ρ (`∀ A) = cong (∀A-⊑-B ★) (renameImp-star (extᵗ ρ) A)

renameImp-cong :
  ∀ {ρ ρ′} →
  (∀ X → ρ X ≡ ρ′ X) →
  (p : Imp) →
  renameImp ρ p ≡ renameImp ρ′ p
renameImp-cong h ★-⊑-★ = refl
renameImp-cong h (X-⊑-★ X) = cong X-⊑-★ (h X)
renameImp-cong h (A-⊑-★ p) = cong A-⊑-★ (renameImp-cong h p)
renameImp-cong h (X-⊑-X X) = cong X-⊑-X (h X)
renameImp-cong h (α-⊑-α α) = refl
renameImp-cong h (ι-⊑-ι ι) = refl
renameImp-cong h (A⇒B-⊑-A′⇒B′ p q) =
  cong₂ A⇒B-⊑-A′⇒B′ (renameImp-cong h p) (renameImp-cong h q)
renameImp-cong {ρ = ρ} {ρ′ = ρ′} h (∀A-⊑-∀B p) =
  cong ∀A-⊑-∀B (renameImp-cong h′ p)
  where
    h′ : ∀ X → extᵗ ρ X ≡ extᵗ ρ′ X
    h′ zero = refl
    h′ (suc X) = cong suc (h X)
renameImp-cong {ρ = ρ} {ρ′ = ρ′} h (∀A-⊑-B B p) =
  cong₂ ∀A-⊑-B (rename-cong h B) (renameImp-cong h′ p)
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
  Σ VarPrec (λ m → Γ ∋ X ∶ m)
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
wkImpAt {Φ = Φ} ⊢★-⊑-★ = ⊢★-⊑-★
wkImpAt {Φ = Φ} (⊢X-⊑-★ xν) = ⊢X-⊑-★ (rename∋-insert {Φ = Φ} xν)
wkImpAt {Φ = Φ} (⊢A-⊑-★ g p⊢) =
  ⊢A-⊑-★ (renameᵗ-ground _ g) (wkImpAt {Φ = Φ} p⊢)
wkImpAt {Φ = Φ} (⊢X-⊑-X x∈) =
  ⊢X-⊑-X (rename∋-insert {Φ = Φ} x∈)
wkImpAt {Φ = Φ} (⊢α-⊑-α (wfSeal α<Ψ)) = ⊢α-⊑-α (wfSeal α<Ψ)
wkImpAt {Φ = Φ} ⊢ι-⊑-ι = ⊢ι-⊑-ι
wkImpAt {Φ = Φ} (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  ⊢A⇒B-⊑-A′⇒B′ (wkImpAt {Φ = Φ} p⊢) (wkImpAt {Φ = Φ} q⊢)
wkImpAt {Φ = Φ} (⊢∀A-⊑-∀B p⊢) =
  ⊢∀A-⊑-∀B
    (cong-⊢⊑-raw
      (sym (renameImp-cong (raise-ext (length Φ)) _))
      (sym (rename-raise-ext (length Φ) _))
      (sym (rename-raise-ext (length Φ) _))
      (wkImpAt {Φ = X⊑X ∷ Φ} p⊢))
wkImpAt {Φ = Φ} (⊢∀A-⊑-B {A = A} {B = B} wfB p⊢) =
  ⊢∀A-⊑-B
    (renameᵗ-preserves-WfTy wfB (raiseWf {Φ = Φ}))
    (cong-⊢⊑-raw
      (sym (renameImp-cong (raise-ext (length Φ)) _))
      (sym (rename-raise-ext (length Φ) A))
      (rename-raise-⇑ᵗ (length Φ) B)
      (wkImpAt {Φ = X⊑★ ∷ Φ} p⊢))

wk-VarSubst :
  ∀ {Ψ Γ A m m′} →
  VarSubst Ψ Γ A m →
  VarSubst Ψ (m′ ∷ Γ) (⇑ᵗ A) m
wk-VarSubst {m = X⊑X} h =
  cong-⊢⊑-raw (renameImp-refl suc _) refl refl
    (wkImpAt {Φ = []} h)
wk-VarSubst {m = X⊑★} h =
  cong-⊢⊑-raw (renameImp-star suc _) refl refl
    (wkImpAt {Φ = []} h)

plain-var-subst :
  ∀ {Δ Ψ X m} →
  plains Δ [] ∋ X ∶ m →
  VarSubst Ψ (plains Δ []) (＇ X) m
plain-var-subst {Δ = zero} ()
plain-var-subst {Δ = suc Δ} here = ⊢X-⊑-X here
plain-var-subst {Δ = suc Δ} {Ψ = Ψ} (there x∈) =
  wk-VarSubst {m′ = X⊑X} (plain-var-subst {Ψ = Ψ} x∈)

subst-var-prefix :
  ∀ {Δ Ψ}{Σ : Store}{Φ X m} →
  StoreWf Δ Ψ Σ →
  (Φ ++ X⊑★ ∷ plains Δ []) ∋ X ∶ m →
  VarSubst (suc Ψ) (Φ ++ plains Δ [])
    (substVarFrom (length Φ) (｀ (length Σ)) X) m
subst-var-prefix {Φ = []} wfΣ here =
  ⊢A-⊑-★ (｀ _) (⊢α-⊑-α (wfSeal (len<suc-StoreWf wfΣ)))
subst-var-prefix {Ψ = Ψ} {Φ = []} wfΣ (there x∈) =
  plain-var-subst {Ψ = suc Ψ} x∈
subst-var-prefix {Φ = X⊑X ∷ Φ} wfΣ here = ⊢X-⊑-X here
subst-var-prefix {Φ = X⊑X ∷ Φ} wfΣ (there x∈) =
  wk-VarSubst (subst-var-prefix {Φ = Φ} wfΣ x∈)
subst-var-prefix {Φ = X⊑★ ∷ Φ} wfΣ here = ⊢X-⊑-★ here
subst-var-prefix {Φ = X⊑★ ∷ Φ} wfΣ (there x∈) =
  wk-VarSubst (subst-var-prefix {Φ = Φ} wfΣ x∈)

varSubst-wf :
  ∀ {Ψ Γ A m} →
  VarSubst Ψ Γ A m →
  WfTy (length Γ) Ψ A
varSubst-wf {m = X⊑X} h = ⊑-src-wf h
varSubst-wf {m = X⊑★} h = ⊑-src-wf h

substWf-prefix :
  ∀ {Δ Ψ}{Σ : Store}{Φ} →
  StoreWf Δ Ψ Σ →
  TySubstWf
    (length (Φ ++ X⊑★ ∷ plains Δ []))
    (length (Φ ++ plains Δ []))
    (suc Ψ)
    (substVarFrom (length Φ) (｀ (length Σ)))
substWf-prefix {Φ = Φ} wfΣ X<len =
  varSubst-wf (subst-var-prefix {Φ = Φ} wfΣ (proj₂ (lookup-mode _ X<len)))

open-fresh-ν⊑-prefix :
  ∀ {Δ Ψ}{Σ : Store}{Φ : VarPrecCtx}{A B : Ty}{p : Imp} →
  StoreWf Δ Ψ Σ →
  Ψ ∣ (Φ ++ X⊑★ ∷ plains Δ []) ⊢ p ⦂ A ⊑ B →
  suc Ψ ∣ (Φ ++ plains Δ []) ⊢
    substPlainAtImp (length Φ) (｀ (length Σ)) p ⦂
    substᵗ (substVarFrom (length Φ) (｀ (length Σ))) A ⊑
    substᵗ (substVarFrom (length Φ) (｀ (length Σ))) B
open-fresh-ν⊑-prefix wfΣ ⊢★-⊑-★ = ⊢★-⊑-★
open-fresh-ν⊑-prefix wfΣ (⊢X-⊑-★ xν) = subst-var-prefix wfΣ xν
open-fresh-ν⊑-prefix wfΣ (⊢A-⊑-★ g p⊢) =
  ⊢A-⊑-★ (substᵗ-ground _ g) (open-fresh-ν⊑-prefix wfΣ p⊢)
open-fresh-ν⊑-prefix {Φ = Φ} wfΣ (⊢X-⊑-X x∈) =
  subst-var-prefix {Φ = Φ} wfΣ x∈
open-fresh-ν⊑-prefix wfΣ (⊢α-⊑-α (wfSeal α<Ψ)) =
  ⊢α-⊑-α (wfSeal (<-≤-trans α<Ψ (n≤1+n _)))
open-fresh-ν⊑-prefix wfΣ ⊢ι-⊑-ι = ⊢ι-⊑-ι
open-fresh-ν⊑-prefix wfΣ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  ⊢A⇒B-⊑-A′⇒B′ (open-fresh-ν⊑-prefix wfΣ p⊢)
       (open-fresh-ν⊑-prefix wfΣ q⊢)
open-fresh-ν⊑-prefix {Φ = Φ} wfΣ (⊢∀A-⊑-∀B p⊢) =
  ⊢∀A-⊑-∀B (open-fresh-ν⊑-prefix {Φ = X⊑X ∷ Φ} wfΣ p⊢)
open-fresh-ν⊑-prefix {Φ = Φ} wfΣ (⊢∀A-⊑-B {A = A} {B = B} wfB p⊢) =
  ⊢∀A-⊑-B
    (substᵗ-preserves-WfTy
      (WfTy-weakenˢ wfB (n≤1+n _))
      (substWf-prefix {Φ = Φ} wfΣ))
    (cong-⊢⊑
      refl
      (substᵗ-suc-renameᵗ-suc
        (substVarFrom (length Φ) (｀ _))
        B)
      (open-fresh-ν⊑-prefix {Φ = X⊑★ ∷ Φ} wfΣ p⊢))

open-fresh-ν⊑ :
  ∀ {Δ Ψ}{Σ : Store}{A B : Ty}{p : Imp} →
  StoreWf Δ Ψ Σ →
  Ψ ∣ (X⊑★ ∷ plains Δ []) ⊢ p ⦂ A ⊑ ⇑ᵗ B →
  suc Ψ ∣ plains Δ [] ⊢ p [ ｀ (length Σ) ]⊑ ⦂
    (A [ ｀ (length Σ) ]ᵗ) ⊑ B
open-fresh-ν⊑ {Σ = Σ} {B = B} wfΣ p⊢ =
  cong-⊢⊑ refl (open-renᵗ-suc B (｀ (length Σ)))
    (open-fresh-ν⊑-prefix {Φ = []} wfΣ p⊢)

subst-var-plain-prefix :
  ∀ {Δ Ψ}{Σ : Store}{Φ X m} →
  StoreWf Δ Ψ Σ →
  (Φ ++ X⊑X ∷ plains Δ []) ∋ X ∶ m →
  VarSubst (suc Ψ) (Φ ++ plains Δ [])
    (substVarFrom (length Φ) (｀ (length Σ)) X) m
subst-var-plain-prefix {Φ = []} wfΣ here =
  ⊢α-⊑-α (wfSeal (len<suc-StoreWf wfΣ))
subst-var-plain-prefix {Ψ = Ψ} {Φ = []} wfΣ (there x∈) =
  plain-var-subst {Ψ = suc Ψ} x∈
subst-var-plain-prefix {Φ = X⊑X ∷ Φ} wfΣ here = ⊢X-⊑-X here
subst-var-plain-prefix {Φ = X⊑X ∷ Φ} wfΣ (there x∈) =
  wk-VarSubst (subst-var-plain-prefix {Φ = Φ} wfΣ x∈)
subst-var-plain-prefix {Φ = X⊑★ ∷ Φ} wfΣ here = ⊢X-⊑-★ here
subst-var-plain-prefix {Φ = X⊑★ ∷ Φ} wfΣ (there x∈) =
  wk-VarSubst (subst-var-plain-prefix {Φ = Φ} wfΣ x∈)

substWf-plain-prefix :
  ∀ {Δ Ψ}{Σ : Store}{Φ} →
  StoreWf Δ Ψ Σ →
  TySubstWf
    (length (Φ ++ X⊑X ∷ plains Δ []))
    (length (Φ ++ plains Δ []))
    (suc Ψ)
    (substVarFrom (length Φ) (｀ (length Σ)))
substWf-plain-prefix {Φ = Φ} wfΣ X<len =
  varSubst-wf
    (subst-var-plain-prefix {Φ = Φ} wfΣ (proj₂ (lookup-mode _ X<len)))

open-fresh-∀⊑-prefix :
  ∀ {Δ Ψ}{Σ : Store}{Φ : VarPrecCtx}{A B : Ty}{p : Imp} →
  StoreWf Δ Ψ Σ →
  Ψ ∣ (Φ ++ X⊑X ∷ plains Δ []) ⊢ p ⦂ A ⊑ B →
  suc Ψ ∣ (Φ ++ plains Δ []) ⊢
    substPlainAtImp (length Φ) (｀ (length Σ)) p ⦂
    substᵗ (substVarFrom (length Φ) (｀ (length Σ))) A ⊑
    substᵗ (substVarFrom (length Φ) (｀ (length Σ))) B
open-fresh-∀⊑-prefix wfΣ ⊢★-⊑-★ = ⊢★-⊑-★
open-fresh-∀⊑-prefix wfΣ (⊢X-⊑-★ xν) =
  subst-var-plain-prefix wfΣ xν
open-fresh-∀⊑-prefix wfΣ (⊢A-⊑-★ g p⊢) =
  ⊢A-⊑-★ (substᵗ-ground _ g) (open-fresh-∀⊑-prefix wfΣ p⊢)
open-fresh-∀⊑-prefix {Φ = Φ} wfΣ (⊢X-⊑-X x∈) =
  subst-var-plain-prefix {Φ = Φ} wfΣ x∈
open-fresh-∀⊑-prefix wfΣ (⊢α-⊑-α (wfSeal α<Ψ)) =
  ⊢α-⊑-α (wfSeal (<-≤-trans α<Ψ (n≤1+n _)))
open-fresh-∀⊑-prefix wfΣ ⊢ι-⊑-ι = ⊢ι-⊑-ι
open-fresh-∀⊑-prefix wfΣ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  ⊢A⇒B-⊑-A′⇒B′ (open-fresh-∀⊑-prefix wfΣ p⊢)
       (open-fresh-∀⊑-prefix wfΣ q⊢)
open-fresh-∀⊑-prefix {Φ = Φ} wfΣ (⊢∀A-⊑-∀B p⊢) =
  ⊢∀A-⊑-∀B (open-fresh-∀⊑-prefix {Φ = X⊑X ∷ Φ} wfΣ p⊢)
open-fresh-∀⊑-prefix {Φ = Φ} wfΣ (⊢∀A-⊑-B {A = A} {B = B} wfB p⊢) =
  ⊢∀A-⊑-B
    (substᵗ-preserves-WfTy
      (WfTy-weakenˢ wfB (n≤1+n _))
      (substWf-plain-prefix {Φ = Φ} wfΣ))
    (cong-⊢⊑
      refl
      (substᵗ-suc-renameᵗ-suc
        (substVarFrom (length Φ) (｀ _))
        B)
      (open-fresh-∀⊑-prefix {Φ = X⊑★ ∷ Φ} wfΣ p⊢))

open-fresh-∀⊑ :
  ∀ {Δ Ψ}{Σ : Store}{A B : Ty}{p : Imp} →
  StoreWf Δ Ψ Σ →
  Ψ ∣ (X⊑X ∷ plains Δ []) ⊢ p ⦂ A ⊑ B →
  suc Ψ ∣ plains Δ [] ⊢ p [ ｀ (length Σ) ]⊑ ⦂
    A [ ｀ (length Σ) ]ᵗ ⊑ B [ ｀ (length Σ) ]ᵗ
open-fresh-∀⊑ wfΣ p⊢ =
  open-fresh-∀⊑-prefix {Φ = []} wfΣ p⊢

------------------------------------------------------------------------
-- Context imprecision for transitivity
------------------------------------------------------------------------

data ModeLe : VarPrec → VarPrec → Set where
  X⊑X≤X⊑X : ModeLe X⊑X X⊑X
  X⊑X≤ν : ModeLe X⊑X X⊑★
  ν≤ν : ModeLe X⊑★ X⊑★

infix 4 _≤ᵢ_
data _≤ᵢ_ : VarPrecCtx → VarPrecCtx → Set where
  []≤ᵢ : [] ≤ᵢ []
  _∷≤ᵢ_ : ∀ {m m′ Γ Γ′} →
    ModeLe m m′ →
    Γ ≤ᵢ Γ′ →
    (m ∷ Γ) ≤ᵢ (m′ ∷ Γ′)

≤ᵢ-refl : ∀ {Γ} → Γ ≤ᵢ Γ
≤ᵢ-refl {Γ = []} = []≤ᵢ
≤ᵢ-refl {Γ = X⊑X ∷ Γ} = X⊑X≤X⊑X ∷≤ᵢ ≤ᵢ-refl
≤ᵢ-refl {Γ = X⊑★ ∷ Γ} = ν≤ν ∷≤ᵢ ≤ᵢ-refl

≤ᵢ-length :
  ∀ {Γ Γ′} →
  Γ ≤ᵢ Γ′ →
  length Γ ≡ length Γ′
≤ᵢ-length []≤ᵢ = refl
≤ᵢ-length (m≤m′ ∷≤ᵢ Γ≤Γ′) = cong suc (≤ᵢ-length Γ≤Γ′)

≤ᵢ-ν-lookup :
  ∀ {Γ Γ′ X} →
  Γ ≤ᵢ Γ′ →
  Γ ∋ X ∶ X⊑★ →
  Γ′ ∋ X ∶ X⊑★
≤ᵢ-ν-lookup (ν≤ν ∷≤ᵢ Γ≤Γ′) here = here
≤ᵢ-ν-lookup (m≤m′ ∷≤ᵢ Γ≤Γ′) (there xν) =
  there (≤ᵢ-ν-lookup Γ≤Γ′ xν)

wf-length-cast :
  ∀ {Ψ Γ Γ′ A} →
  Γ ≤ᵢ Γ′ →
  WfTy (length Γ) Ψ A →
  WfTy (length Γ′) Ψ A
wf-length-cast Γ≤Γ′ wfA =
  subst (λ Δ → WfTy Δ _ _) (≤ᵢ-length Γ≤Γ′) wfA

------------------------------------------------------------------------
-- Occurrence inversion for X⊑X variables
------------------------------------------------------------------------

false≢true : false ≡ true → ⊥
false≢true ()

occurs-⇑ᵗ-suc :
  ∀ X A →
  occurs (suc X) (⇑ᵗ A) ≡ occurs X A
occurs-⇑ᵗ-suc X A = occurs-raise zero X A

plain-target-occurs-source :
  ∀ {Ψ Γ X A B p} →
  Γ ∋ X ∶ X⊑X →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  occurs X B ≡ true →
  occurs X A ≡ true
plain-target-occurs-source x∈ ⊢★-⊑-★ ()
plain-target-occurs-source x∈ (⊢X-⊑-★ xν) ()
plain-target-occurs-source x∈ (⊢A-⊑-★ g p⊢) ()
plain-target-occurs-source x∈ (⊢X-⊑-X wfY) occ = occ
plain-target-occurs-source x∈ (⊢α-⊑-α wfα) ()
plain-target-occurs-source x∈ ⊢ι-⊑-ι ()
plain-target-occurs-source {X = X} x∈
    (⊢A⇒B-⊑-A′⇒B′ {A = A} {A′ = A′} {B = B} {B′ = B′} p⊢ q⊢) occ
    with occurs X A′ in occA′ | occurs X A in occA
plain-target-occurs-source {X = X} x∈
    (⊢A⇒B-⊑-A′⇒B′ {A = A} {A′ = A′} {B = B} {B′ = B′} p⊢ q⊢) occ
    | true | true = refl
plain-target-occurs-source {X = X} x∈
    (⊢A⇒B-⊑-A′⇒B′ {A = A} {A′ = A′} {B = B} {B′ = B′} p⊢ q⊢) occ
    | true | false =
  ⊥-elim (false≢true
    (trans (sym occA) (plain-target-occurs-source x∈ p⊢ occA′)))
plain-target-occurs-source {X = X} x∈
    (⊢A⇒B-⊑-A′⇒B′ {A = A} {A′ = A′} {B = B} {B′ = B′} p⊢ q⊢) occ
    | false | true = refl
plain-target-occurs-source {X = X} x∈
    (⊢A⇒B-⊑-A′⇒B′ {A = A} {A′ = A′} {B = B} {B′ = B′} p⊢ q⊢) occ
    | false | false =
  plain-target-occurs-source x∈ q⊢ occ
plain-target-occurs-source x∈ (⊢∀A-⊑-∀B p⊢) occ =
  plain-target-occurs-source (there x∈) p⊢ occ
plain-target-occurs-source {X = X} x∈ (⊢∀A-⊑-B {B = B} wfB p⊢) occB =
  plain-target-occurs-source (there x∈) p⊢
    (trans (occurs-⇑ᵗ-suc X B) occB)

------------------------------------------------------------------------
-- Transport across plain-to-ν context changes
------------------------------------------------------------------------

mutual
  transport-to-star-⊑ :
    ∀ {Ψ Γ Γ′ A p} →
    Γ ≤ᵢ Γ′ →
    Ψ ∣ Γ ⊢ p ⦂ A ⊑ ★ →
    Σ[ r ∈ Imp ] Ψ ∣ Γ′ ⊢ r ⦂ A ⊑ ★
  transport-to-star-⊑ Γ≤Γ′ ⊢★-⊑-★ = ★-⊑-★ , ⊢★-⊑-★
  transport-to-star-⊑ Γ≤Γ′ (⊢X-⊑-★ xν) =
    _ , ⊢X-⊑-★ (≤ᵢ-ν-lookup Γ≤Γ′ xν)
  transport-to-star-⊑ Γ≤Γ′ (⊢A-⊑-★ g p⊢)
      with transport-to-ground-⊑ Γ≤Γ′ g p⊢
  transport-to-star-⊑ Γ≤Γ′ (⊢A-⊑-★ g p⊢) | r , r⊢ =
    A-⊑-★ r , ⊢A-⊑-★ g r⊢
  transport-to-star-⊑ Γ≤Γ′ (⊢∀A-⊑-B {B = ★} wf★ p⊢)
      with transport-to-star-⊑ (ν≤ν ∷≤ᵢ Γ≤Γ′) p⊢
  transport-to-star-⊑ Γ≤Γ′ (⊢∀A-⊑-B {B = ★} wf★ p⊢)
      | r , r⊢ =
    ∀A-⊑-B ★ r , ⊢∀A-⊑-B (wf-length-cast Γ≤Γ′ wf★) r⊢

  transport-to-ground-⊑ :
    ∀ {Ψ Γ Γ′ A G p} →
    Γ ≤ᵢ Γ′ →
    Ground G →
    Ψ ∣ Γ ⊢ p ⦂ A ⊑ G →
    Σ[ r ∈ Imp ] Ψ ∣ Γ′ ⊢ r ⦂ A ⊑ G
  transport-to-ground-⊑ Γ≤Γ′ (｀ α) (⊢α-⊑-α wfα) =
    α-⊑-α α , ⊢α-⊑-α (wf-length-cast Γ≤Γ′ wfα)
  transport-to-ground-⊑ Γ≤Γ′ (‵ ι) ⊢ι-⊑-ι =
    ι-⊑-ι ι , ⊢ι-⊑-ι
  transport-to-ground-⊑ Γ≤Γ′ ★⇒★ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢)
      with transport-to-star-⊑ Γ≤Γ′ p⊢
         | transport-to-star-⊑ Γ≤Γ′ q⊢
  transport-to-ground-⊑ Γ≤Γ′ ★⇒★ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢)
      | p′ , p′⊢ | q′ , q′⊢ =
    A⇒B-⊑-A′⇒B′ p′ q′ , ⊢A⇒B-⊑-A′⇒B′ p′⊢ q′⊢
  transport-to-ground-⊑ Γ≤Γ′ g (⊢∀A-⊑-B {B = B} wfB p⊢)
      with transport-to-ground-⊑ (ν≤ν ∷≤ᵢ Γ≤Γ′) (renameᵗ-ground suc g) p⊢
  transport-to-ground-⊑ Γ≤Γ′ g (⊢∀A-⊑-B {B = B} wfB p⊢)
      | r , r⊢ =
    ∀A-⊑-B B r , ⊢∀A-⊑-B (wf-length-cast Γ≤Γ′ wfB) r⊢

------------------------------------------------------------------------
-- Full transitivity
------------------------------------------------------------------------

trans-ctx-⊑ :
  ∀ {Ψ Γ Γ′ A B C p q} →
  Γ ≤ᵢ Γ′ →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  Ψ ∣ Γ′ ⊢ q ⦂ B ⊑ C →
  Σ[ r ∈ Imp ] Ψ ∣ Γ′ ⊢ r ⦂ A ⊑ C
trans-ctx-⊑ Γ≤Γ′ (⊢∀A-⊑-B {B = B} wfB p⊢) q⊢
    with trans-ctx-⊑ (ν≤ν ∷≤ᵢ Γ≤Γ′) p⊢ (wkImpAt {Φ = []} q⊢)
trans-ctx-⊑ Γ≤Γ′ (⊢∀A-⊑-B {B = B} wfB p⊢) q⊢
    | r , r⊢ =
  ∀A-⊑-B _ r , ⊢∀A-⊑-B (⊑-tgt-wf q⊢) r⊢
trans-ctx-⊑ Γ≤Γ′ p⊢ ⊢★-⊑-★ = transport-to-star-⊑ Γ≤Γ′ p⊢
trans-ctx-⊑ Γ≤Γ′ p⊢ (⊢X-⊑-★ xν) =
  trans-to-starν Γ≤Γ′ p⊢ xν
  where
    trans-to-starν :
      ∀ {Ψ Γ Γ′ A X p} →
      Γ ≤ᵢ Γ′ →
      Ψ ∣ Γ ⊢ p ⦂ A ⊑ ＇ X →
      Γ′ ∋ X ∶ X⊑★ →
      Σ[ r ∈ Imp ] Ψ ∣ Γ′ ⊢ r ⦂ A ⊑ ★
    trans-to-starν Γ≤Γ′ (⊢X-⊑-X wfX) xν = X-⊑-★ _ , ⊢X-⊑-★ xν
    trans-to-starν Γ≤Γ′ (⊢∀A-⊑-B {B = ＇ X} wfB p⊢) xν
        with trans-ctx-⊑ (ν≤ν ∷≤ᵢ Γ≤Γ′) p⊢ (wkImpAt {Φ = []} (⊢X-⊑-★ xν))
    trans-to-starν Γ≤Γ′ (⊢∀A-⊑-B {B = ＇ X} wfB p⊢) xν
        | r , r⊢ =
      ∀A-⊑-B ★ r , ⊢∀A-⊑-B wf★ r⊢
trans-ctx-⊑ Γ≤Γ′ p⊢ (⊢A-⊑-★ g q⊢)
    with trans-ctx-⊑ Γ≤Γ′ p⊢ q⊢
trans-ctx-⊑ Γ≤Γ′ p⊢ (⊢A-⊑-★ g q⊢) | r , r⊢ =
  A-⊑-★ r , ⊢A-⊑-★ g r⊢
trans-ctx-⊑ Γ≤Γ′ (⊢X-⊑-X wfX) (⊢X-⊑-X wfX′) =
  _ , ⊢X-⊑-X wfX′
trans-ctx-⊑ Γ≤Γ′ p⊢ (⊢α-⊑-α wfα) =
  transport-to-ground-⊑ Γ≤Γ′ (｀ _) p⊢
trans-ctx-⊑ Γ≤Γ′ p⊢ ⊢ι-⊑-ι =
  transport-to-ground-⊑ Γ≤Γ′ (‵ _) p⊢
trans-ctx-⊑ Γ≤Γ′ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) (⊢A⇒B-⊑-A′⇒B′ p⊢′ q⊢′)
    with trans-ctx-⊑ Γ≤Γ′ p⊢ p⊢′
       | trans-ctx-⊑ Γ≤Γ′ q⊢ q⊢′
trans-ctx-⊑ Γ≤Γ′ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) (⊢A⇒B-⊑-A′⇒B′ p⊢′ q⊢′)
    | r₁ , r₁⊢ | r₂ , r₂⊢ =
  A⇒B-⊑-A′⇒B′ r₁ r₂ , ⊢A⇒B-⊑-A′⇒B′ r₁⊢ r₂⊢
trans-ctx-⊑ Γ≤Γ′ (⊢∀A-⊑-∀B p⊢) (⊢∀A-⊑-∀B q⊢)
    with trans-ctx-⊑ (X⊑X≤X⊑X ∷≤ᵢ Γ≤Γ′) p⊢ q⊢
trans-ctx-⊑ Γ≤Γ′ (⊢∀A-⊑-∀B p⊢) (⊢∀A-⊑-∀B q⊢) | r , r⊢ =
  ∀A-⊑-∀B r , ⊢∀A-⊑-∀B r⊢
trans-ctx-⊑ Γ≤Γ′ (⊢∀A-⊑-∀B p⊢) (⊢∀A-⊑-B {B = B} wfB q⊢)
    with trans-ctx-⊑ (X⊑X≤ν ∷≤ᵢ Γ≤Γ′) p⊢ q⊢
trans-ctx-⊑ Γ≤Γ′ (⊢∀A-⊑-∀B p⊢) (⊢∀A-⊑-B {B = B} wfB q⊢)
    | r , r⊢ =
  ∀A-⊑-B B r , ⊢∀A-⊑-B wfB r⊢

⊑-trans :
  ∀ {Ψ Γ A B C p q} →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  Ψ ∣ Γ ⊢ q ⦂ B ⊑ C →
  Σ[ r ∈ Imp ] Ψ ∣ Γ ⊢ r ⦂ A ⊑ C
⊑-trans = trans-ctx-⊑ ≤ᵢ-refl

trans-⊑-plains :
  ∀ {Δ A B C p q} →
  0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B →
  0 ∣ plains Δ [] ⊢ q ⦂ B ⊑ C →
  Σ[ r ∈ Imp ] 0 ∣ plains Δ [] ⊢ r ⦂ A ⊑ C
trans-⊑-plains = ⊑-trans
