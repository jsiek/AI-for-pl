module TypeSubst where

open import Data.List using (List; []; _∷_; map; _++_; length)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality as Eq using (cong; cong₂; sym; trans; subst)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat.Base using (_<_; z<s; s<s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)

open import PolyTypes

infixr 50 _⨟ᵗ_
_⨟ᵗ_ : Substᵗ → Substᵗ → Substᵗ
_⨟ᵗ_ sigma1 sigma2 i = substᵗ sigma2 (sigma1 i)

cons-sub : Ty → Substᵗ → Substᵗ
cons-sub v sigma zero = v
cons-sub v sigma (suc j) = sigma j

subst-one-at-one : Ty → Ty → Ty
subst-one-at-one a b = substᵗ (extsᵗ (singleTyEnv b)) a

single-subst-def : (a b : Ty) →
  a [ b ]ᵗ ≡ substᵗ (singleTyEnv b) a
single-subst-def a b = refl

subst-one-at-one-def : (a b : Ty) →
  subst-one-at-one a b ≡ substᵗ (extsᵗ (singleTyEnv b)) a
subst-one-at-one-def a b = refl

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

rename-cong : ∀ {rho rho' : Renameᵗ} → ((i : ℕ) → rho i ≡ rho' i) → (a : Ty) →
  renameᵗ rho a ≡ renameᵗ rho' a
rename-cong {rho} {rho'} h (` i) = cong `_ (h i)
rename-cong {rho} {rho'} h `ℕ = refl
rename-cong {rho} {rho'} h `Bool = refl
rename-cong {rho} {rho'} h `Str = refl
rename-cong {rho} {rho'} h `★ = refl
rename-cong {rho} {rho'} h (`U u) = refl
rename-cong {rho} {rho'} h (a ⇒ b) = cong₂ _⇒_ (rename-cong h a) (rename-cong h b)
rename-cong {rho} {rho'} h (`∀ a) = cong `∀ (rename-cong h-ext a)
  where
    h-ext : (i : ℕ) → extᵗ rho i ≡ extᵗ rho' i
    h-ext zero = refl
    h-ext (suc i) = cong suc (h i)

subst-cong : ∀ {sigma tau : Substᵗ} → ((i : ℕ) → sigma i ≡ tau i) → (a : Ty) →
  substᵗ sigma a ≡ substᵗ tau a
subst-cong {sigma} {tau} h (` i) = h i
subst-cong {sigma} {tau} h `ℕ = refl
subst-cong {sigma} {tau} h `Bool = refl
subst-cong {sigma} {tau} h `Str = refl
subst-cong {sigma} {tau} h `★ = refl
subst-cong {sigma} {tau} h (`U u) = refl
subst-cong {sigma} {tau} h (a ⇒ b) = cong₂ _⇒_ (subst-cong h a) (subst-cong h b)
subst-cong {sigma} {tau} h (`∀ a) = cong `∀ (subst-cong h-ext a)
  where
    h-ext : (i : ℕ) → extsᵗ sigma i ≡ extsᵗ tau i
    h-ext zero = refl
    h-ext (suc i) = cong (renameᵗ suc) (h i)

------------------------------------------------------------------------
-- Converted substitution theorems
------------------------------------------------------------------------

ext-comp : (rho1 rho2 : Renameᵗ) →
  ((i : ℕ) → extᵗ rho2 (extᵗ rho1 i) ≡ extᵗ (λ i' → rho2 (rho1 i')) i)
ext-comp rho1 rho2 zero = refl
ext-comp rho1 rho2 (suc i) = refl

rename-rename-commute : (rho1 rho2 : Renameᵗ) → (a : Ty) →
  renameᵗ rho2 (renameᵗ rho1 a) ≡ renameᵗ (λ i → rho2 (rho1 i)) a
rename-rename-commute rho1 rho2 (` i) = refl
rename-rename-commute rho1 rho2 `ℕ = refl
rename-rename-commute rho1 rho2 `Bool = refl
rename-rename-commute rho1 rho2 `Str = refl
rename-rename-commute rho1 rho2 `★ = refl
rename-rename-commute rho1 rho2 (`U u) = refl
rename-rename-commute rho1 rho2 (a ⇒ b) =
  cong₂ _⇒_ (rename-rename-commute rho1 rho2 a) (rename-rename-commute rho1 rho2 b)
rename-rename-commute rho1 rho2 (`∀ a) =
  trans
    (cong `∀ (rename-rename-commute (extᵗ rho1) (extᵗ rho2) a))
    (cong `∀ (rename-cong (ext-comp rho1 rho2) a))

exts-ext-comp : (rho : Renameᵗ) → (tau : Substᵗ) →
  ((i : ℕ) → extsᵗ tau (extᵗ rho i) ≡ extsᵗ (λ j → tau (rho j)) i)
exts-ext-comp rho tau zero = refl
exts-ext-comp rho tau (suc i) = refl

extnᵗ : ℕ → Renameᵗ → Renameᵗ
extnᵗ zero rho = rho
extnᵗ (suc d) rho = extᵗ (extnᵗ d rho)

rename-subst-commute : (rho : Renameᵗ) → (tau : Substᵗ) → (a : Ty) →
  substᵗ tau (renameᵗ rho a) ≡ substᵗ (λ i → tau (rho i)) a
rename-subst-commute rho tau (` i) = refl
rename-subst-commute rho tau `ℕ = refl
rename-subst-commute rho tau `Bool = refl
rename-subst-commute rho tau `Str = refl
rename-subst-commute rho tau `★ = refl
rename-subst-commute rho tau (`U u) = refl
rename-subst-commute rho tau (a ⇒ b) =
  cong₂ _⇒_ (rename-subst-commute rho tau a) (rename-subst-commute rho tau b)
rename-subst-commute rho tau (`∀ a) =
  trans
    (cong `∀ (rename-subst-commute (extᵗ rho) (extsᵗ tau) a))
    (cong `∀ (subst-cong (exts-ext-comp rho tau) a))

ext-exts-comp : (rho : Renameᵗ) → (tau : Substᵗ) →
  ((i : ℕ) → renameᵗ (extᵗ rho) (extsᵗ tau i) ≡ extsᵗ (λ j → renameᵗ rho (tau j)) i)
ext-exts-comp rho tau zero = refl
ext-exts-comp rho tau (suc j) =
  trans
    (rename-rename-commute suc (extᵗ rho) (tau j))
    (trans
      (rename-cong (λ i → refl) (tau j))
      (sym (rename-rename-commute rho suc (tau j))))

rename-subst : (rho : Renameᵗ) → (tau : Substᵗ) → (a : Ty) →
  renameᵗ rho (substᵗ tau a) ≡ substᵗ (λ i → renameᵗ rho (tau i)) a
rename-subst rho tau (` i) = refl
rename-subst rho tau `ℕ = refl
rename-subst rho tau `Bool = refl
rename-subst rho tau `Str = refl
rename-subst rho tau `★ = refl
rename-subst rho tau (`U u) = refl
rename-subst rho tau (a ⇒ b) =
  cong₂ _⇒_ (rename-subst rho tau a) (rename-subst rho tau b)
rename-subst rho tau (`∀ a) =
  trans
    (cong `∀ (rename-subst (extᵗ rho) (extsᵗ tau) a))
    (cong `∀ (subst-cong (ext-exts-comp rho tau) a))

exts-seq : (sigma tau : Substᵗ) →
  ((i : ℕ) → ((extsᵗ sigma) ⨟ᵗ (extsᵗ tau)) i ≡ extsᵗ (sigma ⨟ᵗ tau) i)
exts-seq sigma tau zero = refl
exts-seq sigma tau (suc j) =
  trans
    (rename-subst-commute suc (extsᵗ tau) (sigma j))
    (sym (rename-subst suc tau (sigma j)))

sub-sub : (sigma tau : Substᵗ) → (a : Ty) →
  substᵗ tau (substᵗ sigma a) ≡ substᵗ (sigma ⨟ᵗ tau) a
sub-sub sigma tau (` i) = refl
sub-sub sigma tau `ℕ = refl
sub-sub sigma tau `Bool = refl
sub-sub sigma tau `Str = refl
sub-sub sigma tau `★ = refl
sub-sub sigma tau (`U u) = refl
sub-sub sigma tau (a ⇒ b) =
  cong₂ _⇒_ (sub-sub sigma tau a) (sub-sub sigma tau b)
sub-sub sigma tau (`∀ a) =
  trans
    (cong `∀ (sub-sub (extsᵗ sigma) (extsᵗ tau) a))
    (cong `∀ (subst-cong (exts-seq sigma tau) a))

rename-id : (A : Ty) → renameᵗ (λ x → x) A ≡ A
rename-id (` i) = refl
rename-id `ℕ = refl
rename-id `Bool = refl
rename-id `Str = refl
rename-id `★ = refl
rename-id (`U u) = refl
rename-id (a ⇒ b) = cong₂ _⇒_ (rename-id a) (rename-id b)
rename-id (`∀ a) = trans (cong `∀ (rename-cong ext-id a)) (cong `∀ (rename-id a))
  where
    ext-id : (i : ℕ) → extᵗ (λ x → x) i ≡ i
    ext-id zero = refl
    ext-id (suc i) = refl

lt-weaken :
  {i Δ d : ℕ} →
  i < Δ →
  Δ ≤ d →
  i < d
lt-weaken {i = zero} {Δ = suc Δ} {d = suc d} z<s (s≤s Δ≤d) = z<s
lt-weaken {i = suc i} {Δ = suc Δ} {d = suc d} (s<s i<Δ) (s≤s Δ≤d) =
  s<s (lt-weaken {i = i} {Δ = Δ} {d = d} i<Δ Δ≤d)


subst-id : (a : Ty) → substᵗ `_ a ≡ a
subst-id (` i) = refl
subst-id `ℕ = refl
subst-id `Bool = refl
subst-id `Str = refl
subst-id `★ = refl
subst-id (`U u) = refl
subst-id (a ⇒ b) = cong₂ _⇒_ (subst-id a) (subst-id b)
subst-id (`∀ a) = trans (cong `∀ (subst-cong exts-var a)) (cong `∀ (subst-id a))
  where
    exts-var : (i : ℕ) → extsᵗ `_ i ≡ ` i
    exts-var zero = refl
    exts-var (suc i) = refl

substitution : {a b c : Ty} →
  (a [ b ]ᵗ) [ c ]ᵗ ≡
  (subst-one-at-one a c) [ (b [ c ]ᵗ) ]ᵗ
substitution {a} {b} {c} =
  trans
    (trans
      (cong (λ t → t [ c ]ᵗ) (single-subst-def a b))
      (trans
        (single-subst-def (substᵗ sigma a) c)
        (sub-sub sigma tau a)))
    (trans
      (subst-cong env-eq a)
      (trans
        (sym (sub-sub (extsᵗ tau) phi a))
        (sym
          (trans
            (cong (λ t → t [ (b [ c ]ᵗ) ]ᵗ) (subst-one-at-one-def a c))
            (trans
              (cong (λ t → (substᵗ (extsᵗ tau) a) [ t ]ᵗ) (single-subst-def b c))
              (single-subst-def (substᵗ (extsᵗ tau) a) (substᵗ tau b)))))))
  where
    sigma : Substᵗ
    sigma = singleTyEnv b

    tau : Substᵗ
    tau = singleTyEnv c

    phi : Substᵗ
    phi = singleTyEnv (substᵗ tau b)

    env-eq : (i : ℕ) → (sigma ⨟ᵗ tau) i ≡ ((extsᵗ tau) ⨟ᵗ phi) i
    env-eq zero = refl
    env-eq (suc zero) =
      trans
        (sym (subst-id c))
        (trans
          (subst-cong (λ i → refl) c)
          (sym (rename-subst-commute suc phi c)))
    env-eq (suc (suc k)) = refl

exts-sub-cons : {sigma : Substᵗ} {a v : Ty} →
  (substᵗ (extsᵗ sigma) a) [ v ]ᵗ ≡
  substᵗ (cons-sub v sigma) a
exts-sub-cons {sigma} {a} {v} =
  trans
    (single-subst-def (substᵗ (extsᵗ sigma) a) v)
    (trans
      (sub-sub (extsᵗ sigma) phi a)
      (subst-cong env-eq a))
  where
    phi : Substᵗ
    phi = singleTyEnv v

    psi : Substᵗ
    psi = cons-sub v sigma

    env-eq : (i : ℕ) → ((extsᵗ sigma) ⨟ᵗ phi) i ≡ psi i
    env-eq zero = refl
    env-eq (suc j) =
      trans
        (rename-subst-commute suc phi (sigma j))
        (trans
          (subst-cong (λ i → refl) (sigma j))
          (subst-id (sigma j)))

rename-[]ᵗ-commute : (ρ : Renameᵗ) (A B : Ty) →
  renameᵗ ρ (A [ B ]ᵗ) ≡ (renameᵗ (extᵗ ρ) A) [ renameᵗ ρ B ]ᵗ
rename-[]ᵗ-commute ρ A B =
  trans
    (trans
      (cong (renameᵗ ρ) (single-subst-def A B))
      (rename-subst ρ (singleTyEnv B) A))
    (trans
      (subst-cong env-eq A)
      (sym (rename-subst-commute (extᵗ ρ) (singleTyEnv (renameᵗ ρ B)) A)))
  where
    env-eq : (i : ℕ) →
      (λ j → renameᵗ ρ (singleTyEnv B j)) i ≡
      (λ j → singleTyEnv (renameᵗ ρ B) (extᵗ ρ j)) i
    env-eq zero = refl
    env-eq (suc i) = refl

subst-[]ᵗ-commute : (σ : Substᵗ) (A B : Ty) →
  substᵗ σ (A [ B ]ᵗ) ≡ (substᵗ (extsᵗ σ) A) [ substᵗ σ B ]ᵗ
subst-[]ᵗ-commute σ A B =
  trans
    (cong (λ T → substᵗ σ T) (single-subst-def A B))
    (trans
      (sub-sub (singleTyEnv B) σ A)
      (trans
        (subst-cong env-eq A)
        (sym (exts-sub-cons {sigma = σ} {a = A} {v = substᵗ σ B}))))
  where
    env-eq : (i : ℕ) → ((singleTyEnv B) ⨟ᵗ σ) i ≡ cons-sub (substᵗ σ B) σ i
    env-eq zero = refl
    env-eq (suc i) = refl


------------------------------------------------------------------------
-- Context lookup under list maps
------------------------------------------------------------------------

lookup-map-renameᵗ :
  {Γ : Ctx} {x : Var} {A : Ty} {ρ : Renameᵗ} →
  Γ ∋ x ⦂ A →
  map (renameᵗ ρ) Γ ∋ x ⦂ renameᵗ ρ A
lookup-map-renameᵗ Z = Z
lookup-map-renameᵗ (S h) = S (lookup-map-renameᵗ h)

lookup-map-substᵗ :
  {Γ : Ctx} {x : Var} {A : Ty} {σ : Substᵗ} →
  Γ ∋ x ⦂ A →
  map (substᵗ σ) Γ ∋ x ⦂ substᵗ σ A
lookup-map-substᵗ Z = Z
lookup-map-substᵗ (S h) = S (lookup-map-substᵗ h)

lookup-map-inv :
  {Γ : Ctx} {x : Var} {B : Ty} {f : Ty → Ty} →
  map f Γ ∋ x ⦂ B →
  Σ Ty (λ A → (Γ ∋ x ⦂ A) × (B ≡ f A))
lookup-map-inv {Γ = A ∷ Γ} {x = zero} Z = A , (Z , refl)
lookup-map-inv {Γ = A ∷ Γ} {x = suc x} (S h)
  with lookup-map-inv h
... | A' , (hA' , eq) = A' , (S hA' , eq)

lookupᵁ-map-renameᵗ :
  {Σ : Store} {U : Name} {A : Ty} {ρ : Renameᵗ} →
  Σ ∋ᵁ U ⦂ A →
  renameΣ ρ Σ ∋ᵁ U ⦂ renameᵗ ρ A
lookupᵁ-map-renameᵗ Zᵁ = Zᵁ
lookupᵁ-map-renameᵗ (Sᵁ h) = Sᵁ (lookupᵁ-map-renameᵗ h)

lookupᵁ-map-inv :
  {stores : Store} {U : Name} {B : Ty} {f : Ty → Ty} →
  map f stores ∋ᵁ U ⦂ B →
  Σ Ty (λ A → (stores ∋ᵁ U ⦂ A) × (B ≡ f A))
lookupᵁ-map-inv {stores = A ∷ stores} {U = zero} Zᵁ = A , (Zᵁ , refl)
lookupᵁ-map-inv {stores = A ∷ stores} {U = suc U} (Sᵁ h)
  with lookupᵁ-map-inv h
... | A' , (hA' , eq) = A' , (Sᵁ hA' , eq)

map-renameΣ-suc : (ρ : Renameᵗ) (Σ : Store) →
  renameΣ (extᵗ ρ) (renameΣ suc Σ) ≡ renameΣ suc (renameΣ ρ Σ)
map-renameΣ-suc ρ [] = refl
map-renameΣ-suc ρ (A ∷ Σ) =
  cong₂ _∷_
    (trans
      (rename-rename-commute suc (extᵗ ρ) A)
      (trans
        (rename-cong (λ i → refl) A)
        (sym (rename-rename-commute ρ suc A))))
    (map-renameΣ-suc ρ Σ)

------------------------------------------------------------------------
-- Well-formed renamings/substitutions on types, replacing X variables
------------------------------------------------------------------------

TyRenameWf : TyCtx → TyCtx → Renameᵗ → Set
TyRenameWf Δ Δ' ρ = ∀ {X} → X < Δ → ρ X < Δ'

TySubstWf : TyCtx → TyCtx → Store → Substᵗ → Set
TySubstWf Δ Δ' Σ σ = ∀ {X} → X < Δ → WfTy Δ' Σ (σ X)

TySubstIsVar : Substᵗ → Set
TySubstIsVar σ = ∀ {X} → IsVar (σ X)

TyRenameWf-ext :
  {Δ Δ' : TyCtx} {ρ : Renameᵗ} →
  TyRenameWf Δ Δ' ρ →
  TyRenameWf (suc Δ) (suc Δ') (extᵗ ρ)
TyRenameWf-ext hρ {zero} z<s = z<s
TyRenameWf-ext hρ {suc X} (s<s x<Δ) = s<s (hρ {X} x<Δ)

TyRenameWf-zero :
  {ρ : Renameᵗ} →
  TyRenameWf zero zero ρ
TyRenameWf-zero ()

renameᵗ-preserves-WfTy :
  {Δ Δ' : TyCtx} {Σ : Store} {A : Ty} {ρ : Renameᵗ} →
  WfTy Δ Σ A →
  TyRenameWf Δ Δ' ρ →
  WfTy Δ' (renameΣ ρ Σ) (renameᵗ ρ A)
renameᵗ-preserves-WfTy (wfVar x<Δ) hρ = wfVar (hρ x<Δ)
renameᵗ-preserves-WfTy wfℕ hρ = wfℕ
renameᵗ-preserves-WfTy wfBool hρ = wfBool
renameᵗ-preserves-WfTy wfStr hρ = wfStr
renameᵗ-preserves-WfTy wf★ hρ = wf★
renameᵗ-preserves-WfTy (wfU hU) hρ = wfU (lookupᵁ-map-renameᵗ hU)
renameᵗ-preserves-WfTy (wf⇒ hA hB) hρ =
  wf⇒ (renameᵗ-preserves-WfTy hA hρ) (renameᵗ-preserves-WfTy hB hρ)
renameᵗ-preserves-WfTy {Δ' = Δ'} {Σ = Σ} {ρ = ρ} (wf∀ {A = A} hA) hρ =
  let IH = renameᵗ-preserves-WfTy {ρ = extᵗ ρ} hA (TyRenameWf-ext hρ) in
  wf∀
    (subst
      (λ S → WfTy (suc Δ') S (renameᵗ (extᵗ ρ) A))
      (map-renameΣ-suc ρ Σ)
      IH)

TySubstWf-exts :
  {Δ Δ' : TyCtx} {Σ : Store} {σ : Substᵗ} →
  TySubstWf Δ Δ' Σ σ →
  TySubstWf (suc Δ) (suc Δ') (renameΣ suc Σ) (extsᵗ σ)
TySubstWf-exts hσ {zero} z<s = wfVar (Data.Nat.s≤s Data.Nat.z≤n)
TySubstWf-exts {Δ' = Δ'} {Σ = Σ} {σ = σ} hσ {suc X} (s<s x<Δ) =
  renameᵗ-preserves-WfTy (hσ {X} x<Δ) (λ {X = X₁} → Data.Nat.s≤s)

substᵗ-preserves-WfTy :
  {Δ Δ' : TyCtx} {Σ : Store} {A : Ty} {σ : Substᵗ} →
  WfTy Δ Σ A →
  TySubstWf Δ Δ' Σ σ →
  WfTy Δ' Σ (substᵗ σ A)
substᵗ-preserves-WfTy (wfVar x<Δ) hσ = hσ x<Δ
substᵗ-preserves-WfTy wfℕ hσ = wfℕ
substᵗ-preserves-WfTy wfBool hσ = wfBool
substᵗ-preserves-WfTy wfStr hσ = wfStr
substᵗ-preserves-WfTy wf★ hσ = wf★
substᵗ-preserves-WfTy (wfU hU) hσ = wfU hU
substᵗ-preserves-WfTy (wf⇒ hA hB) hσ =
  wf⇒ (substᵗ-preserves-WfTy hA hσ) (substᵗ-preserves-WfTy hB hσ)
substᵗ-preserves-WfTy {Δ' = Δ'} {Σ = Σ} {σ = σ} (wf∀ {A = A} hA) hσ =
  wf∀ (substᵗ-preserves-WfTy hA (TySubstWf-exts hσ))

singleTySubstWf : {Δ : TyCtx} {Σ : Store} {B : Ty} →
  WfTy Δ Σ B →
  TySubstWf (suc Δ) Δ Σ (singleTyEnv B)
singleTySubstWf {Δ = Δ} {Σ = Σ} {B = B} hB {zero} X<sΔ = hB
singleTySubstWf {Δ = Δ} {Σ = Σ} {B = B} hB {suc X} (Data.Nat.s≤s X<sΔ) = wfVar X<sΔ

renameᵗ-preserves-Ground :
  {G : Ty} {ρ : Renameᵗ} →
  Ground G →
  Ground (renameᵗ ρ G)
renameᵗ-preserves-Ground G-ℕ = G-ℕ
renameᵗ-preserves-Ground G-Bool = G-Bool
renameᵗ-preserves-Ground G-Str = G-Str
renameᵗ-preserves-Ground G-⇒★ = G-⇒★
renameᵗ-preserves-Ground G-∀★ = G-∀★
renameᵗ-preserves-Ground G-var = G-var
renameᵗ-preserves-Ground G-U = G-U

renameᵗ-preserves-IsVar :
  {A : Ty} {ρ : Renameᵗ} →
  IsVar A →
  IsVar (renameᵗ ρ A)
renameᵗ-preserves-IsVar X-var = X-var
renameᵗ-preserves-IsVar U-var = U-var

TySubstIsVar-exts :
  {σ : Substᵗ} →
  TySubstIsVar σ →
  TySubstIsVar (extsᵗ σ)
TySubstIsVar-exts hσ {zero} = X-var
TySubstIsVar-exts hσ {suc X} =
  renameᵗ-preserves-IsVar (hσ {X})

substᵗ-preserves-IsVar :
  {A : Ty} {σ : Substᵗ} →
  IsVar A →
  TySubstIsVar σ →
  IsVar (substᵗ σ A)
substᵗ-preserves-IsVar {σ = σ} (X-var {X}) hσ = hσ {X}
substᵗ-preserves-IsVar U-var hσ = U-var

substᵗ-preserves-Ground :
  {G : Ty} {σ : Substᵗ} →
  Ground G →
  TySubstIsVar σ →
  Ground (substᵗ σ G)
substᵗ-preserves-Ground G-ℕ hσ = G-ℕ
substᵗ-preserves-Ground G-Bool hσ = G-Bool
substᵗ-preserves-Ground G-Str hσ = G-Str
substᵗ-preserves-Ground G-⇒★ hσ = G-⇒★
substᵗ-preserves-Ground G-∀★ hσ = G-∀★
substᵗ-preserves-Ground {σ = σ} (G-var {X}) hσ =
  IsVar→Ground (hσ {X})
substᵗ-preserves-Ground G-U hσ = G-U

lookup-wfty :
  {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {x : Var} {A : Ty} →
  WfCtx Δ Σ Γ →
  Γ ∋ x ⦂ A →
  WfTy Δ Σ A
lookup-wfty (wfΓ∷ hΓ hA) Z = hA
lookup-wfty (wfΓ∷ hΓ hA) (S h) = lookup-wfty hΓ h

wfty-weaken :
  {Δ Δ' : TyCtx} {Σ : Store} {A : Ty} →
  WfTy Δ Σ A →
  Δ ≤ Δ' →
  WfTy Δ' Σ A
wfty-weaken (wfVar x<Δ) Δ≤Δ' = wfVar (lt-weaken x<Δ Δ≤Δ')
wfty-weaken wfℕ Δ≤Δ' = wfℕ
wfty-weaken wfBool Δ≤Δ' = wfBool
wfty-weaken wfStr Δ≤Δ' = wfStr
wfty-weaken wf★ Δ≤Δ' = wf★
wfty-weaken (wfU hU) Δ≤Δ' = wfU hU
wfty-weaken (wf⇒ hA hB) Δ≤Δ' =
  wf⇒ (wfty-weaken hA Δ≤Δ') (wfty-weaken hB Δ≤Δ')
wfty-weaken (wf∀ hA) Δ≤Δ' =
  wf∀ (wfty-weaken hA (s≤s Δ≤Δ'))

StoreWfAt : TyCtx → Store → Set
StoreWfAt Δ Σ = ∀ {U A} → Σ ∋ᵁ U ⦂ A → WfTy Δ Σ A

storeWfAt-shift :
  {Δ : TyCtx} {Σ : Store} →
  StoreWfAt Δ Σ →
  StoreWfAt (suc Δ) (renameΣ suc Σ)
storeWfAt-shift {Δ = Δ} {Σ = Σ} hΣ {U} {A'} hU'
  with lookupᵁ-map-inv hU'
... | A , (hU , eq) =
  Eq.subst
    (λ T → WfTy (suc Δ) (renameΣ suc Σ) T)
    (sym eq)
    (renameᵗ-preserves-WfTy (hΣ hU) (λ {i} i<Δ → s<s i<Δ))

wfty-store-shift :
  {Δ : TyCtx} {Σ : Store} {A : Ty} →
  WfTy Δ Σ A →
  WfTy Δ (renameΣ suc Σ) A
wfty-store-shift (wfVar x<Δ) = wfVar x<Δ
wfty-store-shift wfℕ = wfℕ
wfty-store-shift wfBool = wfBool
wfty-store-shift wfStr = wfStr
wfty-store-shift wf★ = wf★
wfty-store-shift (wfU hU) = wfU (lookupᵁ-map-renameᵗ hU)
wfty-store-shift (wf⇒ hA hB) =
  wf⇒ (wfty-store-shift hA) (wfty-store-shift hB)
wfty-store-shift (wf∀ hA) =
  wf∀ (wfty-store-shift hA)

wfty-store-unshift :
  {Δ : TyCtx} {Σ : Store} {A : Ty} →
  WfTy Δ (renameΣ suc Σ) A →
  WfTy Δ Σ A
wfty-store-unshift (wfVar x<Δ) = wfVar x<Δ
wfty-store-unshift wfℕ = wfℕ
wfty-store-unshift wfBool = wfBool
wfty-store-unshift wfStr = wfStr
wfty-store-unshift wf★ = wf★
wfty-store-unshift (wfU hU)
  with lookupᵁ-map-inv hU
... | A′ , (hA′ , eq) = wfU hA′
wfty-store-unshift (wf⇒ hA hB) =
  wf⇒ (wfty-store-unshift hA) (wfty-store-unshift hB)
wfty-store-unshift (wf∀ hA) =
  wf∀ (wfty-store-unshift hA)

rename-suc-WfStore-top :
  {Σ : Store} →
  WfStore Σ →
  WfStore (renameΣ suc Σ)
rename-suc-WfStore-top wfΣ∅ = wfΣ∅
rename-suc-WfStore-top {Σ = A ∷ Σ} (wfΣ∷ wfΣ wfA) =
  wfΣ∷
    (rename-suc-WfStore-top wfΣ)
    (renameᵗ-preserves-WfTy wfA (TyRenameWf-zero {ρ = suc}))

wfctx-shift :
  {Δ : TyCtx} {Σ : Store} {Γ : Ctx} →
  WfCtx Δ Σ Γ →
  WfCtx (suc Δ) (renameΣ suc Σ) (⤊ Γ)
wfctx-shift wfΓ∅ = wfΓ∅
wfctx-shift (wfΓ∷ hΓ hA) =
  wfΓ∷
    (wfctx-shift hΓ)
    (renameᵗ-preserves-WfTy hA (λ {i} i<Δ → s<s i<Δ))


map-renameᵗ-⤊ : (ρ : Renameᵗ) (Γ : Ctx) →
  map (renameᵗ (extᵗ ρ)) (⤊ Γ) ≡ ⤊ (map (renameᵗ ρ) Γ)
map-renameᵗ-⤊ ρ [] = refl
map-renameᵗ-⤊ ρ (A ∷ Γ) =
  cong₂ _∷_
    (trans
      (rename-rename-commute suc (extᵗ ρ) A)
      (trans
        (rename-cong (λ i → refl) A)
        (sym (rename-rename-commute ρ suc A))))
    (map-renameᵗ-⤊ ρ Γ)

renameᵗ-preserves-WfStore : {Σ : Store} {ρ : Renameᵗ} →
  WfStore Σ →
  WfStore (renameΣ ρ Σ)
renameᵗ-preserves-WfStore wfΣ∅ = wfΣ∅
renameᵗ-preserves-WfStore {ρ = ρ} (wfΣ∷ wfΣ wfA) =
  wfΣ∷
    (renameᵗ-preserves-WfStore wfΣ)
    (renameᵗ-preserves-WfTy wfA (TyRenameWf-zero {ρ = ρ}))

renameᵗ-preserves-WfCtx :
  {Δ Δ' : TyCtx} {Σ : Store} {Γ : Ctx} {ρ : Renameᵗ} →
  WfCtx Δ Σ Γ →
  TyRenameWf Δ Δ' ρ →
  WfCtx Δ' (renameΣ ρ Σ) (map (renameᵗ ρ) Γ)
renameᵗ-preserves-WfCtx wfΓ∅ hρ = wfΓ∅
renameᵗ-preserves-WfCtx (wfΓ∷ hΓ hA) hρ =
  wfΓ∷
    (renameᵗ-preserves-WfCtx hΓ hρ)
    (renameᵗ-preserves-WfTy hA hρ)

substᵗ-suc-renameᵗ-suc :
  (σ : Substᵗ) →
  (A : Ty) →
  substᵗ (extsᵗ σ) (renameᵗ suc A) ≡
  renameᵗ suc (substᵗ σ A)
substᵗ-suc-renameᵗ-suc σ A =
  trans
    (rename-subst-commute suc (extsᵗ σ) A)
    (sym (rename-subst suc σ A))

map-substᵗ-⤊ :
  (σ : Substᵗ) →
  (Γ : Ctx) →
  map (substᵗ (extsᵗ σ)) (⤊ Γ) ≡ ⤊ (map (substᵗ σ) Γ)
map-substᵗ-⤊ σ [] = refl
map-substᵗ-⤊ σ (A ∷ Γ) =
  cong₂ _∷_
    (substᵗ-suc-renameᵗ-suc σ A)
    (map-substᵗ-⤊ σ Γ)

substᵗ-preserves-WfCtx :
  {Δ Δ' : TyCtx} {Σ : Store} {Γ : Ctx} {σ : Substᵗ} →
  WfCtx Δ Σ Γ →
  TySubstWf Δ Δ' Σ σ →
  WfCtx Δ' Σ (map (substᵗ σ) Γ)
substᵗ-preserves-WfCtx wfΓ∅ hσ = wfΓ∅
substᵗ-preserves-WfCtx (wfΓ∷ hΓ hA) hσ =
  wfΓ∷
    (substᵗ-preserves-WfCtx hΓ hσ)
    (substᵗ-preserves-WfTy hA hσ)

substᵗ-id-on-wf :
  {Δ : TyCtx} {Σ : Store} {A : Ty} {σ : Substᵗ} →
  (∀ {X} → X < Δ → σ X ≡ ` X) →
  WfTy Δ Σ A →
  substᵗ σ A ≡ A
substᵗ-id-on-wf hσ (wfVar x<Δ) = hσ x<Δ
substᵗ-id-on-wf hσ wfℕ = refl
substᵗ-id-on-wf hσ wfBool = refl
substᵗ-id-on-wf hσ wfStr = refl
substᵗ-id-on-wf hσ wf★ = refl
substᵗ-id-on-wf hσ (wfU hU) = refl
substᵗ-id-on-wf hσ (wf⇒ hA hB) =
  cong₂ _⇒_ (substᵗ-id-on-wf hσ hA) (substᵗ-id-on-wf hσ hB)
substᵗ-id-on-wf {Δ = Δ} {σ = σ} hσ (wf∀ hA) =
  cong `∀ (substᵗ-id-on-wf hσ-ext hA)
  where
    hσ-ext : ∀ {X} → X < suc Δ → extsᵗ σ X ≡ ` X
    hσ-ext {zero} z<s = refl
    hσ-ext {suc X} (s<s x<Δ) =
      cong (renameᵗ suc) (hσ x<Δ)

substᵗ-id-closed :
  {Σ : Store} {A : Ty} {σ : Substᵗ} →
  WfTy zero Σ A →
  substᵗ σ A ≡ A
substᵗ-id-closed hA = substᵗ-id-on-wf (λ ()) hA

data WfAt0 (A : Ty) : Set where
  wfAt0 : ∀ {stores : Store} → WfTy 0 stores A → WfAt0 A

lookupᵁ-wfty0 :
  {stores : Store} {U : Name} {A : Ty} →
  WfStore stores →
  stores ∋ᵁ U ⦂ A →
  WfAt0 A
lookupᵁ-wfty0 wfΣ∅ ()
lookupᵁ-wfty0 {stores = A ∷ stores} (wfΣ∷ wfΣ wfA) Zᵁ = wfAt0 wfA
lookupᵁ-wfty0 {stores = B ∷ stores} (wfΣ∷ wfΣ wfB) (Sᵁ hU) =
  lookupᵁ-wfty0 wfΣ hU

rename-suc-WfStore :
  {stores : Store} →
  WfStore stores →
  WfStore (renameΣ suc stores)
rename-suc-WfStore wfΣ∅ = wfΣ∅
rename-suc-WfStore {stores = A ∷ stores} (wfΣ∷ wfΣ wfA) =
  wfΣ∷
    (rename-suc-WfStore wfΣ)
    (renameᵗ-preserves-WfTy wfA (TyRenameWf-zero {ρ = suc}))

subst-cong-wf :
  {Δ : TyCtx} {Σ : Store} {A : Ty} {σ τ : Substᵗ} →
  (∀ {X} → X < Δ → σ X ≡ τ X) →
  WfTy Δ Σ A →
  substᵗ σ A ≡ substᵗ τ A
subst-cong-wf hσ (wfVar x<Δ) = hσ x<Δ
subst-cong-wf hσ wfℕ = refl
subst-cong-wf hσ wfBool = refl
subst-cong-wf hσ wfStr = refl
subst-cong-wf hσ wf★ = refl
subst-cong-wf hσ (wfU hU) = refl
subst-cong-wf hσ (wf⇒ hA hB) =
  cong₂ _⇒_ (subst-cong-wf hσ hA) (subst-cong-wf hσ hB)
subst-cong-wf {Δ = Δ} {σ = σ} {τ = τ} hσ (wf∀ hA) =
  cong `∀ (subst-cong-wf hσ-ext hA)
  where
    hσ-ext : ∀ {X} → X < suc Δ → extsᵗ σ X ≡ extsᵗ τ X
    hσ-ext {zero} z<s = refl
    hσ-ext {suc X} (s<s x<Δ) = cong (renameᵗ suc) (hσ x<Δ)

extendStore : Store → Ty → Store
extendStore Σ B = Σ ++ (B ∷ [])

lookupᵁ-extend :
  {Σ : Store} {U : Name} {A B : Ty} →
  Σ ∋ᵁ U ⦂ A →
  extendStore Σ B ∋ᵁ U ⦂ A
lookupᵁ-extend Zᵁ = Zᵁ
lookupᵁ-extend (Sᵁ hU) = Sᵁ (lookupᵁ-extend hU)

fresh : Store → Name
fresh Σ = length Σ

lookupᵁ-fresh-extend :
  {Σ : Store} {B : Ty} →
  extendStore Σ B ∋ᵁ fresh Σ ⦂ B
lookupᵁ-fresh-extend {Σ = []} {B = B} = Zᵁ
lookupᵁ-fresh-extend {Σ = A ∷ Σ} {B = B} =
  Sᵁ (lookupᵁ-fresh-extend {Σ = Σ} {B = B})

renameᵗ-id-on-wf :
  {Δ : TyCtx} {Σ : Store} {A : Ty} {ρ : Renameᵗ} →
  (∀ {X} → X < Δ → ρ X ≡ X) →
  WfTy Δ Σ A →
  renameᵗ ρ A ≡ A
renameᵗ-id-on-wf hρ (wfVar x<Δ) = cong `_ (hρ x<Δ)
renameᵗ-id-on-wf hρ wfℕ = refl
renameᵗ-id-on-wf hρ wfBool = refl
renameᵗ-id-on-wf hρ wfStr = refl
renameᵗ-id-on-wf hρ wf★ = refl
renameᵗ-id-on-wf hρ (wfU hU) = refl
renameᵗ-id-on-wf hρ (wf⇒ hA hB) =
  cong₂ _⇒_ (renameᵗ-id-on-wf hρ hA) (renameᵗ-id-on-wf hρ hB)
renameᵗ-id-on-wf {Δ = Δ} {ρ = ρ} hρ (wf∀ hA) =
  cong `∀ (renameᵗ-id-on-wf hρ-ext hA)
  where
    hρ-ext : ∀ {X} → X < suc Δ → extᵗ ρ X ≡ X
    hρ-ext {zero} z<s = refl
    hρ-ext {suc X} (s<s x<Δ) = cong suc (hρ x<Δ)

renameᵗ-suc-id-closed :
  {Σ : Store} {A : Ty} →
  WfTy 0 Σ A →
  renameᵗ suc A ≡ A
renameᵗ-suc-id-closed hA = renameᵗ-id-on-wf (λ ()) hA
