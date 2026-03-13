module Preservation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (cong; cong₂; sym; trans)
open import Data.List using (_∷_; []; map)
open import Data.Nat using (zero; suc)
open import Data.Nat.Base using (_<_; z<s; s<s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import PolyCoercions
open import PolyCastCalculus
open import Progress using (canonical-base)
open import TypeSubst

------------------------------------------------------------------------
-- Typing implies type well-formedness
------------------------------------------------------------------------

postulate
  typing-wfty : ∀ {Σ Δ Γ M A}
    → Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A
    → WfTy Δ Σ A

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

lookupᵁ-map-substᵗ :
  {Σ : Store} {U : Name} {A : Ty} {σ : Substᵗ} →
  Σ ∋ᵁ U ⦂ A →
  substΣ σ Σ ∋ᵁ U ⦂ substᵗ σ A
lookupᵁ-map-substᵗ Zᵁ = Zᵁ
lookupᵁ-map-substᵗ (Sᵁ h) = Sᵁ (lookupᵁ-map-substᵗ h)

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

map-substΣ-suc : (σ : Substᵗ) (Σ : Store) →
  substΣ (extsᵗ σ) (renameΣ suc Σ) ≡ renameΣ suc (substΣ σ Σ)
map-substΣ-suc σ [] = refl
map-substΣ-suc σ (A ∷ Σ) =
  cong₂ _∷_
    (trans
      (rename-subst-commute suc (extsᵗ σ) A)
      (sym (rename-subst suc σ A)))
    (map-substΣ-suc σ Σ)

------------------------------------------------------------------------
-- Well-formed renamings/substitutions on type variables
------------------------------------------------------------------------

TyRenameWf : TyCtx → TyCtx → Renameᵗ → Set
TyRenameWf Δ Δ' ρ = ∀ {X} → X < Δ → ρ X < Δ'

data NoU : Ty → Set where
  nuVar  : ∀ {X} → NoU (` X)
  nuℕ    : NoU `ℕ
  nuBool : NoU `Bool
  nuStr  : NoU `Str
  nu★    : NoU `★
  nu⇒    : ∀ {A B} → NoU A → NoU B → NoU (A ⇒ B)
  nu∀    : ∀ {A} → NoU A → NoU (`∀ A)

TySubstWf : TyCtx → TyCtx → Store → Substᵗ → Set
TySubstWf Δ Δ' Σ σ =
  ∀ {X} → X < Δ →
    (WfTy Δ' (substΣ σ Σ) (σ X)) ×
    ((NonDyn (σ X)) × (NoU (σ X)))

data U★Var : Ty → Set where
  u★v-var : ∀ {X} → U★Var (` X)
  u★v-★   : U★Var `★
  u★v-U   : ∀ {U} → U★Var (`U U)

data U★VarView (A : Ty) : Set where
  u★v-isVar : (X : Var) → A ≡ ` X → U★VarView A
  u★v-is★   : A ≡ `★ → U★VarView A
  u★v-isU   : (U : Name) → A ≡ `U U → U★VarView A

u★Var-view : ∀ {A} → U★Var A → U★VarView A
u★Var-view u★v-var = u★v-isVar _ refl
u★Var-view u★v-★ = u★v-is★ refl
u★Var-view u★v-U = u★v-isU _ refl

cast-WfTy :
  ∀ {Δ : TyCtx} {Σ : Store} {A B : Ty} →
  A ≡ B →
  WfTy Δ Σ A →
  WfTy Δ Σ B
cast-WfTy eq h = Eq.subst (λ T → WfTy _ _ T) eq h

cast-injᶜ-typing :
  ∀ {Σ : Store} {Δ : TyCtx} {A B : Ty} →
  A ≡ B →
  Σ ∣ Δ ⊢ injᶜ B ⦂ B ⇨ `★ →
  Σ ∣ Δ ⊢ injᶜ A ⦂ A ⇨ `★
cast-injᶜ-typing eq h =
  Eq.subst (λ T → _ ∣ _ ⊢ injᶜ T ⦂ T ⇨ `★) (sym eq) h

cast-projᶜ-typing :
  ∀ {Σ : Store} {Δ : TyCtx} {A B : Ty} {p : Label} →
  A ≡ B →
  Σ ∣ Δ ⊢ projᶜ B p ⦂ `★ ⇨ B →
  Σ ∣ Δ ⊢ projᶜ A p ⦂ `★ ⇨ A
cast-projᶜ-typing {p = p} eq h =
  Eq.subst (λ T → _ ∣ _ ⊢ projᶜ T p ⦂ `★ ⇨ T) (sym eq) h

TySubstWfᶜ : TyCtx → TyCtx → Store → Substᵗ → Set
TySubstWfᶜ Δ Δ' Σ σ =
  TySubstWf Δ Δ' Σ σ × (∀ {X} → X < Δ → U★Var (σ X))

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
    (Eq.subst
      (λ S → WfTy (suc Δ') S (renameᵗ (extᵗ ρ) A))
      (map-renameΣ-suc ρ Σ)
      IH)

renameᵗ-preserves-NonDyn :
  {A : Ty} {ρ : Renameᵗ} →
  NonDyn A →
  NonDyn (renameᵗ ρ A)
renameᵗ-preserves-NonDyn ndVar = ndVar
renameᵗ-preserves-NonDyn ndℕ = ndℕ
renameᵗ-preserves-NonDyn ndBool = ndBool
renameᵗ-preserves-NonDyn ndStr = ndStr
renameᵗ-preserves-NonDyn ndU = ndU
renameᵗ-preserves-NonDyn nd⇒ = nd⇒
renameᵗ-preserves-NonDyn nd∀ = nd∀

renameᵗ-preserves-NoU :
  {A : Ty} {ρ : Renameᵗ} →
  NoU A →
  NoU (renameᵗ ρ A)
renameᵗ-preserves-NoU nuVar = nuVar
renameᵗ-preserves-NoU nuℕ = nuℕ
renameᵗ-preserves-NoU nuBool = nuBool
renameᵗ-preserves-NoU nuStr = nuStr
renameᵗ-preserves-NoU nu★ = nu★
renameᵗ-preserves-NoU (nu⇒ nuA nuB) =
  nu⇒ (renameᵗ-preserves-NoU nuA) (renameᵗ-preserves-NoU nuB)
renameᵗ-preserves-NoU (nu∀ nuA) =
  nu∀ (renameᵗ-preserves-NoU nuA)

WfTy-store-irrelevant-NoU :
  {Δ : TyCtx} {Σ Σ' : Store} {A : Ty} →
  NoU A →
  WfTy Δ Σ A →
  WfTy Δ Σ' A
WfTy-store-irrelevant-NoU nuVar (wfVar x<Δ) = wfVar x<Δ
WfTy-store-irrelevant-NoU nuℕ wfℕ = wfℕ
WfTy-store-irrelevant-NoU nuBool wfBool = wfBool
WfTy-store-irrelevant-NoU nuStr wfStr = wfStr
WfTy-store-irrelevant-NoU nu★ wf★ = wf★
WfTy-store-irrelevant-NoU (nu⇒ nuA nuB) (wf⇒ hA hB) =
  wf⇒ (WfTy-store-irrelevant-NoU nuA hA) (WfTy-store-irrelevant-NoU nuB hB)
WfTy-store-irrelevant-NoU {Σ = Σ} {Σ' = Σ'} (nu∀ nuA) (wf∀ hA) =
  wf∀ (WfTy-store-irrelevant-NoU {Σ = renameΣ suc Σ} {Σ' = renameΣ suc Σ'} nuA hA)

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

renameᵗ-suc-preserves-U★Var :
  {A : Ty} →
  U★Var A →
  U★Var (renameᵗ suc A)
renameᵗ-suc-preserves-U★Var u★v-var = u★v-var
renameᵗ-suc-preserves-U★Var u★v-★ = u★v-★
renameᵗ-suc-preserves-U★Var u★v-U = u★v-U

TySubstWf-exts :
  {Δ Δ' : TyCtx} {Σ : Store} {σ : Substᵗ} →
  TySubstWf Δ Δ' Σ σ →
  TySubstWf (suc Δ) (suc Δ') (renameΣ suc Σ) (extsᵗ σ)
TySubstWf-exts hσ {zero} z<s = wfVar z<s , (ndVar , nuVar)
TySubstWf-exts {Δ' = Δ'} {Σ = Σ} {σ = σ} hσ {suc X} (s<s x<Δ) =
  let hσX = hσ {X} x<Δ in
  Eq.subst
    (λ S → WfTy (suc Δ') S (renameᵗ suc (σ X)))
    (sym (map-substΣ-suc σ Σ))
    (renameᵗ-preserves-WfTy (proj₁ hσX) (λ {i} i<Δ' → s<s i<Δ'))
  ,
  (renameᵗ-preserves-NonDyn (proj₁ (proj₂ hσX)) ,
   renameᵗ-preserves-NoU (proj₂ (proj₂ hσX)))

TySubstWf-zero :
  {Σ : Store} {σ : Substᵗ} →
  TySubstWf zero zero Σ σ
TySubstWf-zero ()

TySubstWfᶜ-exts :
  {Δ Δ' : TyCtx} {Σ : Store} {σ : Substᵗ} →
  TySubstWfᶜ Δ Δ' Σ σ →
  TySubstWfᶜ (suc Δ) (suc Δ') (renameΣ suc Σ) (extsᵗ σ)
TySubstWfᶜ-exts {Δ = Δ} {σ = σ} hσ =
  TySubstWf-exts (proj₁ hσ)
  ,
  hσu
  where
    hσu : ∀ {X} → X < suc Δ → U★Var (extsᵗ σ X)
    hσu {zero} z<s = u★v-var
    hσu {suc X} (s<s x<Δ) =
      renameᵗ-suc-preserves-U★Var (proj₂ hσ x<Δ)

substᵗ-preserves-WfTy :
  {Δ Δ' : TyCtx} {Σ : Store} {A : Ty} {σ : Substᵗ} →
  WfTy Δ Σ A →
  TySubstWf Δ Δ' Σ σ →
  WfTy Δ' (substΣ σ Σ) (substᵗ σ A)
substᵗ-preserves-WfTy (wfVar x<Δ) hσ = proj₁ (hσ x<Δ)
substᵗ-preserves-WfTy wfℕ hσ = wfℕ
substᵗ-preserves-WfTy wfBool hσ = wfBool
substᵗ-preserves-WfTy wfStr hσ = wfStr
substᵗ-preserves-WfTy wf★ hσ = wf★
substᵗ-preserves-WfTy (wfU hU) hσ = wfU (lookupᵁ-map-substᵗ hU)
substᵗ-preserves-WfTy (wf⇒ hA hB) hσ =
  wf⇒ (substᵗ-preserves-WfTy hA hσ) (substᵗ-preserves-WfTy hB hσ)
substᵗ-preserves-WfTy {Δ' = Δ'} {Σ = Σ} {σ = σ} (wf∀ {A = A} hA) hσ =
  wf∀
    (Eq.subst
      (λ S → WfTy (suc Δ') S (substᵗ (extsᵗ σ) A))
      (map-substΣ-suc σ Σ)
      (substᵗ-preserves-WfTy hA (TySubstWf-exts hσ)))

------------------------------------------------------------------------
-- Renaming type variables in typing derivations
------------------------------------------------------------------------

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
renameᵗ-preserves-WfStore {ρ = ρ} (wfΣ∷ wfΣ ndA wfA) =
  wfΣ∷
    (renameᵗ-preserves-WfStore wfΣ)
    (renameᵗ-preserves-NonDyn ndA)
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

renameᵗ-typeof-const : {ρ : Renameᵗ} {p : Prim} →
  renameᵗ ρ (typeof p) ≡ typeof p
renameᵗ-typeof-base : {ρ : Renameᵗ} (b : Base) →
  renameᵗ ρ (typeof-base b) ≡ typeof-base b
renameᵗ-typeof-base B-Nat = refl
renameᵗ-typeof-base B-Bool = refl

renameᵗ-typeof-const {p = base B-Nat} = refl
renameᵗ-typeof-const {p = base B-Bool} = refl
renameᵗ-typeof-const {p = B ⇒ p} =
  cong₂ _⇒_ (renameᵗ-typeof-base B) (renameᵗ-typeof-const{p = p})

substᵗ-typeof-const : {σ : Substᵗ} {p : Prim} →
  substᵗ σ (typeof p) ≡ typeof p
substᵗ-typeof-base : {σ : Substᵗ} (b : Base) →
  substᵗ σ (typeof-base b) ≡ typeof-base b
substᵗ-typeof-base B-Nat = refl
substᵗ-typeof-base B-Bool = refl

substᵗ-typeof-const {p = base B-Nat} = refl
substᵗ-typeof-const {p = base B-Bool} = refl
substᵗ-typeof-const {p = B ⇒ p} =
  cong₂ _⇒_ (substᵗ-typeof-base B) (substᵗ-typeof-const{p = p})

renameᶜᵗ-preserves-typing :
  {Σ : Store} {Δ Δ' : TyCtx} {c : Coercion} {A B : Ty} {ρ : Renameᵗ} →
  TyRenameWf Δ Δ' ρ →
  Σ ∣ Δ ⊢ c ⦂ A ⇨ B →
  renameΣ ρ Σ ∣ Δ' ⊢ renameᶜᵗ ρ c ⦂ renameᵗ ρ A ⇨ renameᵗ ρ B
renameᶜᵗ-preserves-typing hρ (⊢idᶜ hΣ hA) =
  ⊢idᶜ
    (renameᵗ-preserves-WfStore hΣ)
    (renameᵗ-preserves-WfTy hA hρ)
renameᶜᵗ-preserves-typing hρ (⊢! hΣ hG gG) =
  ⊢!
    (renameᵗ-preserves-WfStore hΣ)
    (renameᵗ-preserves-WfTy hG hρ)
    (renameᵗ-preserves-Ground gG)
renameᶜᵗ-preserves-typing hρ (⊢? hΣ hG gG) =
  ⊢?
    (renameᵗ-preserves-WfStore hΣ)
    (renameᵗ-preserves-WfTy hG hρ)
    (renameᵗ-preserves-Ground gG)
renameᶜᵗ-preserves-typing hρ (⊢↦ cwt dwt) =
  ⊢↦
    (renameᶜᵗ-preserves-typing hρ cwt)
    (renameᶜᵗ-preserves-typing hρ dwt)
renameᶜᵗ-preserves-typing hρ (⊢⨟ cwt dwt) =
  ⊢⨟
    (renameᶜᵗ-preserves-typing hρ cwt)
    (renameᶜᵗ-preserves-typing hρ dwt)
renameᶜᵗ-preserves-typing hρ (⊢conceal hΣ hU) =
  ⊢conceal
    (renameᵗ-preserves-WfStore hΣ)
    (lookupᵁ-map-renameᵗ hU)
renameᶜᵗ-preserves-typing hρ (⊢reveal hΣ hU) =
  ⊢reveal
    (renameᵗ-preserves-WfStore hΣ)
    (lookupᵁ-map-renameᵗ hU)
renameᶜᵗ-preserves-typing {Σ = Σ} {Δ' = Δ'} {ρ = ρ} hρ (⊢∀ᶜ {A = A} {B = B} {c = c} cwt) =
  ⊢∀ᶜ
    (Eq.subst
      (λ S → S ∣ suc Δ' ⊢ renameᶜᵗ (extᵗ ρ) c ⦂ renameᵗ (extᵗ ρ) A ⇨ renameᵗ (extᵗ ρ) B)
      (map-renameΣ-suc ρ Σ)
      (renameᶜᵗ-preserves-typing
        {Σ = renameΣ suc Σ}
        {ρ = extᵗ ρ}
        (TyRenameWf-ext hρ)
        cwt))
renameᶜᵗ-preserves-typing hρ (⊢⊥ hΣ hA hB) =
  ⊢⊥
    (renameᵗ-preserves-WfStore hΣ)
    (renameᵗ-preserves-WfTy hA hρ)
    (renameᵗ-preserves-WfTy hB hρ)

typing-renameᵀ :
  {Σ : Store} {Δ Δ' : TyCtx} {Γ : Ctx} {M : Term} {A : Ty} {ρ : Renameᵗ} →
  TyRenameWf Δ Δ' ρ →
  Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
  renameΣ ρ Σ ∣ Δ' ⊢ map (renameᵗ ρ) Γ ⊢ renameᵀ ρ M ⦂ renameᵗ ρ A
typing-renameᵀ {Σ = Σ} {Δ' = Δ'} {Γ = Γ} {ρ = ρ} hρ (⊢const {p = p} {A = A} {k = k} hΣ hΓ eqA) =
  ⊢const
    (renameᵗ-preserves-WfStore hΣ)
    (renameᵗ-preserves-WfCtx hΓ hρ)
    (trans (cong (renameᵗ ρ) eqA) (renameᵗ-typeof-const {ρ = ρ} {p = p}))
typing-renameᵀ hρ (⊢# h) =
  ⊢# (lookup-map-renameᵗ h)
typing-renameᵀ hρ (⊢ƛ hA hN) =
  ⊢ƛ
    (renameᵗ-preserves-WfTy hA hρ)
    (typing-renameᵀ hρ hN)
typing-renameᵀ hρ (⊢· hL hM) =
  ⊢· (typing-renameᵀ hρ hL) (typing-renameᵀ hρ hM)
typing-renameᵀ {Σ = Σ} {Δ' = Δ'} {ρ = ρ} hρ (⊢Λ {Γ = Γ} {M = N} {A = A} hN) =
  ⊢Λ
    (Eq.subst
      (λ S → S ∣ suc Δ' ⊢ ⤊ (map (renameᵗ ρ) Γ) ⊢
        renameᵀ (extᵗ ρ) N ⦂ renameᵗ (extᵗ ρ) A)
      (map-renameΣ-suc ρ Σ)
      (Eq.subst
        (λ Ψ → renameΣ (extᵗ ρ) (renameΣ suc Σ) ∣ suc Δ' ⊢ Ψ ⊢
          renameᵀ (extᵗ ρ) N ⦂ renameᵗ (extᵗ ρ) A)
        (map-renameᵗ-⤊ ρ Γ)
        (typing-renameᵀ
          {Σ = renameΣ suc Σ}
          {Γ = ⤊ Γ}
          {ρ = extᵗ ρ}
          (TyRenameWf-ext hρ)
          hN)))
typing-renameᵀ {Σ = Σ} {Δ' = Δ'} {Γ = Γ} {ρ = ρ} hρ (⊢·[] {M = M} {A = A} {B = B} hM hB) =
  Eq.subst
    (λ T → renameΣ ρ Σ ∣ Δ' ⊢ map (renameᵗ ρ) Γ ⊢ (renameᵀ ρ M ·[ renameᵗ ρ B ]) ⦂ T)
    (sym (rename-[]ᵗ-commute ρ A B))
    (⊢·[]
      (typing-renameᵀ hρ hM)
      (renameᵗ-preserves-WfTy hB hρ))
typing-renameᵀ hρ (⊢⟨⟩ hM cwt) =
  ⊢⟨⟩
    (typing-renameᵀ hρ hM)
    (renameᶜᵗ-preserves-typing hρ cwt)
typing-renameᵀ hρ (⊢blame hA) =
  ⊢blame (renameᵗ-preserves-WfTy hA hρ)

------------------------------------------------------------------------
-- Substituting type variables in typing derivations
------------------------------------------------------------------------

map-substᵗ-⤊ : (σ : Substᵗ) (Γ : Ctx) →
  map (substᵗ (extsᵗ σ)) (⤊ Γ) ≡ ⤊ (map (substᵗ σ) Γ)
map-substᵗ-⤊ σ [] = refl
map-substᵗ-⤊ σ (A ∷ Γ) =
  cong₂ _∷_
    (trans
      (rename-subst-commute suc (extsᵗ σ) A)
      (sym (rename-subst suc σ A)))
    (map-substᵗ-⤊ σ Γ)

substᵗ-preserves-WfCtx :
  {Δ Δ' : TyCtx} {Σ : Store} {Γ : Ctx} {σ : Substᵗ} →
  WfCtx Δ Σ Γ →
  TySubstWf Δ Δ' Σ σ →
  WfCtx Δ' (substΣ σ Σ) (map (substᵗ σ) Γ)
substᵗ-preserves-WfCtx wfΓ∅ hσ = wfΓ∅
substᵗ-preserves-WfCtx (wfΓ∷ hΓ hA) hσ =
  wfΓ∷
    (substᵗ-preserves-WfCtx hΓ hσ)
    (substᵗ-preserves-WfTy hA hσ)

substᵗ-preserves-NonDyn :
  {Δ Δ' : TyCtx} {Σ : Store} {A : Ty} {σ : Substᵗ} →
  WfTy Δ Σ A →
  NonDyn A →
  TySubstWf Δ Δ' Σ σ →
  NonDyn (substᵗ σ A)
substᵗ-preserves-NonDyn (wfVar x<Δ) ndVar hσ = proj₁ (proj₂ (hσ x<Δ))
substᵗ-preserves-NonDyn wfℕ ndℕ hσ = ndℕ
substᵗ-preserves-NonDyn wfBool ndBool hσ = ndBool
substᵗ-preserves-NonDyn wfStr ndStr hσ = ndStr
substᵗ-preserves-NonDyn (wfU hU) ndU hσ = ndU
substᵗ-preserves-NonDyn (wf⇒ hA hB) nd⇒ hσ = nd⇒
substᵗ-preserves-NonDyn (wf∀ hA) nd∀ hσ = nd∀

TySubstWf-tail :
  {Δ Δ' : TyCtx} {Σ : Store} {A : Ty} {σ : Substᵗ} →
  TySubstWf Δ Δ' (A ∷ Σ) σ →
  TySubstWf Δ Δ' Σ σ
TySubstWf-tail {Σ = Σ} {A = A} {σ = σ} hσ {X} x<Δ =
  let hσX = hσ {X} x<Δ in
  (WfTy-store-irrelevant-NoU
    {Σ = substΣ σ (A ∷ Σ)}
    {Σ' = substΣ σ Σ}
    (proj₂ (proj₂ hσX))
    (proj₁ hσX))
  ,
  (proj₁ (proj₂ hσX) , proj₂ (proj₂ hσX))

substᵗ-preserves-WfStore :
  {Σ : Store} {σ : Substᵗ} →
  WfStore Σ →
  WfStore (substΣ σ Σ)
substᵗ-preserves-WfStore wfΣ∅ = wfΣ∅
substᵗ-preserves-WfStore {Σ = A ∷ Σ} {σ = σ} (wfΣ∷ {A = A} wfΣ ndA wfA) =
  wfΣ∷
    (substᵗ-preserves-WfStore wfΣ)
    (substᵗ-preserves-NonDyn wfA ndA TySubstWf-zero)
    (substᵗ-preserves-WfTy wfA TySubstWf-zero)

substᵗ-preserves-⊢! :
  {Σ : Store} {Δ Δ' : TyCtx} {G : Ty} {σ : Substᵗ} →
  TySubstWfᶜ Δ Δ' Σ σ →
  WfStore Σ →
  WfTy Δ Σ G →
  Ground G →
  substΣ σ Σ ∣ Δ' ⊢ injᶜ (substᵗ σ G) ⦂ substᵗ σ G ⇨ `★
substᵗ-preserves-⊢! {G = ` X} hσ hΣ (wfVar {X = X} x<Δ) G-var
  with u★Var-view (proj₂ hσ {X = X} x<Δ)
... | u★v-isVar Y eq
  = cast-injᶜ-typing eq
      (⊢!
        (substᵗ-preserves-WfStore hΣ)
        (cast-WfTy eq (proj₁ (proj₁ hσ {X = X} x<Δ)))
        G-var)
... | u★v-is★ eq
  = cast-injᶜ-typing eq
      (⊢idᶜ
        (substᵗ-preserves-WfStore hΣ)
        (cast-WfTy eq (proj₁ (proj₁ hσ {X = X} x<Δ))))
... | u★v-isU U eq
  = cast-injᶜ-typing eq
      (⊢!
        (substᵗ-preserves-WfStore hΣ)
        (cast-WfTy eq (proj₁ (proj₁ hσ {X = X} x<Δ)))
        G-U)
substᵗ-preserves-⊢! hσ hΣ hG G-ℕ =
  ⊢!
    (substᵗ-preserves-WfStore hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-ℕ
substᵗ-preserves-⊢! hσ hΣ hG G-Bool =
  ⊢!
    (substᵗ-preserves-WfStore hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-Bool
substᵗ-preserves-⊢! hσ hΣ hG G-Str =
  ⊢!
    (substᵗ-preserves-WfStore hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-Str
substᵗ-preserves-⊢! hσ hΣ hG G-⇒★ =
  ⊢!
    (substᵗ-preserves-WfStore hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-⇒★
substᵗ-preserves-⊢! hσ hΣ hG G-∀★ =
  ⊢!
    (substᵗ-preserves-WfStore hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-∀★
substᵗ-preserves-⊢! hσ hΣ hG G-U =
  ⊢!
    (substᵗ-preserves-WfStore hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-U

substᵗ-preserves-⊢? :
  {Σ : Store} {Δ Δ' : TyCtx} {G : Ty} {p : Label} {σ : Substᵗ} →
  TySubstWfᶜ Δ Δ' Σ σ →
  WfStore Σ →
  WfTy Δ Σ G →
  Ground G →
  substΣ σ Σ ∣ Δ' ⊢ projᶜ (substᵗ σ G) p ⦂ `★ ⇨ substᵗ σ G
substᵗ-preserves-⊢? {G = ` X} {p = p} hσ hΣ (wfVar {X = X} x<Δ) G-var
  with u★Var-view (proj₂ hσ {X = X} x<Δ)
... | u★v-isVar Y eq
  = cast-projᶜ-typing eq
      (⊢?
        (substᵗ-preserves-WfStore hΣ)
        (cast-WfTy eq (proj₁ (proj₁ hσ {X = X} x<Δ)))
        G-var)
... | u★v-is★ eq
  = cast-projᶜ-typing eq
      (⊢idᶜ
        (substᵗ-preserves-WfStore hΣ)
        (cast-WfTy eq (proj₁ (proj₁ hσ {X = X} x<Δ))))
... | u★v-isU U eq
  = cast-projᶜ-typing eq
      (⊢?
        (substᵗ-preserves-WfStore hΣ)
        (cast-WfTy eq (proj₁ (proj₁ hσ {X = X} x<Δ)))
        G-U)
substᵗ-preserves-⊢? hσ hΣ hG G-ℕ =
  ⊢?
    (substᵗ-preserves-WfStore hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-ℕ
substᵗ-preserves-⊢? hσ hΣ hG G-Bool =
  ⊢?
    (substᵗ-preserves-WfStore hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-Bool
substᵗ-preserves-⊢? hσ hΣ hG G-Str =
  ⊢?
    (substᵗ-preserves-WfStore hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-Str
substᵗ-preserves-⊢? hσ hΣ hG G-⇒★ =
  ⊢?
    (substᵗ-preserves-WfStore hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-⇒★
substᵗ-preserves-⊢? hσ hΣ hG G-∀★ =
  ⊢?
    (substᵗ-preserves-WfStore hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-∀★
substᵗ-preserves-⊢? hσ hΣ hG G-U =
  ⊢?
    (substᵗ-preserves-WfStore hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-U

substᶜᵗ-preserves-typing :
  {Σ : Store} {Δ Δ' : TyCtx} {c : Coercion} {A B : Ty} {σ : Substᵗ} →
  TySubstWfᶜ Δ Δ' Σ σ →
  Σ ∣ Δ ⊢ c ⦂ A ⇨ B →
  substΣ σ Σ ∣ Δ' ⊢ substᶜᵗ σ c ⦂ substᵗ σ A ⇨ substᵗ σ B
substᶜᵗ-preserves-typing hσ (⊢idᶜ hΣ hA) =
  ⊢idᶜ
    (substᵗ-preserves-WfStore hΣ)
    (substᵗ-preserves-WfTy hA (proj₁ hσ))
substᶜᵗ-preserves-typing hσ (⊢! hΣ hG gG) =
  substᵗ-preserves-⊢! hσ hΣ hG gG
substᶜᵗ-preserves-typing hσ (⊢? hΣ hG gG) =
  substᵗ-preserves-⊢? hσ hΣ hG gG
substᶜᵗ-preserves-typing hσ (⊢↦ cwt dwt) =
  ⊢↦
    (substᶜᵗ-preserves-typing hσ cwt)
    (substᶜᵗ-preserves-typing hσ dwt)
substᶜᵗ-preserves-typing hσ (⊢⨟ cwt dwt) =
  ⊢⨟
    (substᶜᵗ-preserves-typing hσ cwt)
    (substᶜᵗ-preserves-typing hσ dwt)
substᶜᵗ-preserves-typing hσ (⊢conceal hΣ hU) =
  ⊢conceal
    (substᵗ-preserves-WfStore hΣ)
    (lookupᵁ-map-substᵗ hU)
substᶜᵗ-preserves-typing hσ (⊢reveal hΣ hU) =
  ⊢reveal
    (substᵗ-preserves-WfStore hΣ)
    (lookupᵁ-map-substᵗ hU)
substᶜᵗ-preserves-typing {Σ = Σ} {Δ' = Δ'} {σ = σ} hσ (⊢∀ᶜ {A = A} {B = B} {c = c} cwt) =
  ⊢∀ᶜ
    (Eq.subst
      (λ S → S ∣ suc Δ' ⊢ substᶜᵗ (extsᵗ σ) c ⦂ substᵗ (extsᵗ σ) A ⇨ substᵗ (extsᵗ σ) B)
      (map-substΣ-suc σ Σ)
      (substᶜᵗ-preserves-typing
        {Σ = renameΣ suc Σ}
        {σ = extsᵗ σ}
        (TySubstWfᶜ-exts hσ)
        cwt))
substᶜᵗ-preserves-typing hσ (⊢⊥ hΣ hA hB) =
  ⊢⊥
    (substᵗ-preserves-WfStore hΣ)
    (substᵗ-preserves-WfTy hA (proj₁ hσ))
    (substᵗ-preserves-WfTy hB (proj₁ hσ))

typing-substᵀ :
  {Σ : Store} {Δ Δ' : TyCtx} {Γ : Ctx} {M : Term} {A : Ty} {σ : Substᵗ} →
  TySubstWfᶜ Δ Δ' Σ σ →
  Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
  substΣ σ Σ ∣ Δ' ⊢ map (substᵗ σ) Γ ⊢ substᵀ σ M ⦂ substᵗ σ A
typing-substᵀ {Σ = Σ} {Δ' = Δ'} {Γ = Γ} {σ = σ} hσ (⊢const {p = p} {A = A} {k = k} hΣ hΓ eqA) =
  ⊢const
    (substᵗ-preserves-WfStore hΣ)
    (substᵗ-preserves-WfCtx hΓ (proj₁ hσ))
    (trans (cong (substᵗ σ) eqA) (substᵗ-typeof-const {σ = σ} {p = p}))
typing-substᵀ hσ (⊢# h) =
  ⊢# (lookup-map-substᵗ h)
typing-substᵀ hσ (⊢ƛ hA hN) =
  ⊢ƛ
    (substᵗ-preserves-WfTy hA (proj₁ hσ))
    (typing-substᵀ hσ hN)
typing-substᵀ hσ (⊢· hL hM) =
  ⊢· (typing-substᵀ hσ hL) (typing-substᵀ hσ hM)
typing-substᵀ {Σ = Σ} {Δ' = Δ'} {σ = σ} hσ (⊢Λ {Γ = Γ} {M = N} {A = A} hN) =
  ⊢Λ
    (Eq.subst
      (λ S → S ∣ suc Δ' ⊢ ⤊ (map (substᵗ σ) Γ) ⊢
        substᵀ (extsᵗ σ) N ⦂ substᵗ (extsᵗ σ) A)
      (map-substΣ-suc σ Σ)
      (Eq.subst
        (λ Ψ → substΣ (extsᵗ σ) (renameΣ suc Σ) ∣ suc Δ' ⊢ Ψ ⊢
          substᵀ (extsᵗ σ) N ⦂ substᵗ (extsᵗ σ) A)
        (map-substᵗ-⤊ σ Γ)
        (typing-substᵀ
          {Σ = renameΣ suc Σ}
          {Γ = ⤊ Γ}
          {σ = extsᵗ σ}
          (TySubstWfᶜ-exts hσ)
          hN)))
typing-substᵀ {Σ = Σ} {Δ' = Δ'} {Γ = Γ} {σ = σ} hσ (⊢·[] {M = M} {A = A} {B = B} hM hB) =
  Eq.subst
    (λ T → substΣ σ Σ ∣ Δ' ⊢ map (substᵗ σ) Γ ⊢ (substᵀ σ M ·[ substᵗ σ B ]) ⦂ T)
    (sym (subst-[]ᵗ-commute σ A B))
    (⊢·[]
      (typing-substᵀ hσ hM)
      (substᵗ-preserves-WfTy hB (proj₁ hσ)))
typing-substᵀ hσ (⊢⟨⟩ hM cwt) =
  ⊢⟨⟩
    (typing-substᵀ hσ hM)
    (substᶜᵗ-preserves-typing hσ cwt)
typing-substᵀ hσ (⊢blame hA) =
  ⊢blame (substᵗ-preserves-WfTy hA (proj₁ hσ))

singleTySubstWf : {Δ : TyCtx} {Σ : Store} {B : Ty} →
  WfTy Δ (substΣ (singleTyEnv B) Σ) B →
  NonDyn B →
  NoU B →
  U★Var B →
  TySubstWfᶜ (suc Δ) Δ Σ (singleTyEnv B)
singleTySubstWf {Δ = Δ} {Σ = Σ} {B = B} hB ndB nuB u★B =
  hTy
  ,
  hU★
  where
    hTy : TySubstWf (suc Δ) Δ Σ (singleTyEnv B)
    hTy {zero} z<s = hB , (ndB , nuB)
    hTy {suc X} (s<s x<Δ) = wfVar x<Δ , (ndVar , nuVar)

    hU★ : ∀ {X} → X < suc Δ → U★Var (singleTyEnv B X)
    hU★ {zero} z<s = u★B
    hU★ {suc X} (s<s x<Δ) = u★v-var

substᵗ-renameᵗ-cancel : (C B : Ty) →
  substᵗ (singleTyEnv B) (renameᵗ suc C) ≡ C
substᵗ-renameᵗ-cancel C B =
  trans
    (rename-subst-commute suc (singleTyEnv B) C)
    (subst-id C)

singleTySubst-⤊-cancel : (Γ : Ctx) (B : Ty) →
  map (substᵗ (singleTyEnv B)) (⤊ Γ) ≡ Γ
singleTySubst-⤊-cancel [] B = refl
singleTySubst-⤊-cancel (C ∷ Γ) B =
  cong₂ _∷_
    (substᵗ-renameᵗ-cancel C B)
    (singleTySubst-⤊-cancel Γ B)

typing-single-substᵀ : {Σ : Store} {Δ : TyCtx} {Γ : Ctx} {M : Term} {A B : Ty} →
  Σ ∣ (suc Δ) ⊢ (⤊ Γ) ⊢ M ⦂ A →
  WfTy Δ (substΣ (singleTyEnv B) Σ) B →
  NonDyn B →
  NoU B →
  U★Var B →
  substΣ (singleTyEnv B) Σ ∣ Δ ⊢ Γ ⊢ M [ B ]ᵀ ⦂ A [ B ]ᵗ
typing-single-substᵀ {Σ} {Δ} {Γ} {M} {A} {B} hM hB ndB nuB u★B =
  Eq.subst
    (λ Ψ → substΣ (singleTyEnv B) Σ ∣ Δ ⊢ Ψ ⊢ M [ B ]ᵀ ⦂ A [ B ]ᵗ)
    (singleTySubst-⤊-cancel Γ B)
    (typing-substᵀ (singleTySubstWf hB ndB nuB u★B) hM)

------------------------------------------------------------------------
-- Substituting term variables in typing derivations
------------------------------------------------------------------------

RenameWf : Ctx → Ctx → Rename → Set
RenameWf Γ Γ' ρ = ∀ {x A} → Γ ∋ x ⦂ A → Γ' ∋ ρ x ⦂ A

SubstWf : Store → TyCtx → Ctx → Ctx → Subst → Set
SubstWf Σ Δ Γ Γ' σ = ∀ {x A} → Γ ∋ x ⦂ A → Σ ∣ Δ ⊢ Γ' ⊢ σ x ⦂ A

RenameWf-ext : {Γ Γ' : Ctx} {B : Ty} {ρ : Rename} →
  RenameWf Γ Γ' ρ →
  RenameWf (B ∷ Γ) (B ∷ Γ') (ext ρ)
RenameWf-ext hρ Z = Z
RenameWf-ext hρ (S h) = S (hρ h)

typing-rename : {Σ : Store} {Δ : TyCtx} {Γ Γ' : Ctx} {M : Term} {A : Ty} {ρ : Rename} →
  WfCtx Δ Σ Γ' →
  RenameWf Γ Γ' ρ →
  Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
  Σ ∣ Δ ⊢ Γ' ⊢ rename ρ M ⦂ A
typing-rename hΓ' hρ (⊢const hΣ hΓ eqA) = ⊢const hΣ hΓ' eqA
typing-rename hΓ' hρ (⊢# h) = ⊢# (hρ h)
typing-rename hΓ' hρ (⊢ƛ hA hN) =
  ⊢ƛ hA (typing-rename (wfΓ∷ hΓ' hA) (RenameWf-ext hρ) hN)
typing-rename hΓ' hρ (⊢· hL hM) =
  ⊢· (typing-rename hΓ' hρ hL) (typing-rename hΓ' hρ hM)
typing-rename {Σ = Σ} {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {ρ = ρ} hΓ' hρ (⊢Λ hN) =
  ⊢Λ (typing-rename hΓ'↑ hρ' hN)
  where
    hΓ'↑ : WfCtx (suc Δ) (renameΣ suc Σ) (⤊ Γ')
    hΓ'↑ = renameᵗ-preserves-WfCtx hΓ' (λ {i} i<Δ → s<s i<Δ)

    hρ' : RenameWf (⤊ Γ) (⤊ Γ') ρ
    hρ' h with lookup-map-inv h
    ... | A , (hA , eq)
      rewrite eq = lookup-map-renameᵗ (hρ hA)
typing-rename hΓ' hρ (⊢·[] hM hB) =
  ⊢·[] (typing-rename hΓ' hρ hM) hB
typing-rename hΓ' hρ (⊢⟨⟩ hM cwt) =
  ⊢⟨⟩ (typing-rename hΓ' hρ hM) cwt
typing-rename hΓ' hρ (⊢blame hA) =
  ⊢blame hA

rename-shift : {Σ : Store} {Δ : TyCtx} {Γ : Ctx} {M : Term} {A B : Ty} →
  WfTy Δ Σ B →
  WfCtx Δ Σ Γ →
  Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
  Σ ∣ Δ ⊢ (B ∷ Γ) ⊢ rename suc M ⦂ A
rename-shift hB hΓ hM =
  typing-rename (wfΓ∷ hΓ hB) (λ {x} {A} h → S h) hM

SubstWf-exts : {Σ : Store} {Δ : TyCtx} {Γ Γ' : Ctx} {B : Ty} {σ : Subst} →
  WfTy Δ Σ B →
  WfCtx Δ Σ Γ' →
  SubstWf Σ Δ Γ Γ' σ →
  SubstWf Σ Δ (B ∷ Γ) (B ∷ Γ') (exts σ)
SubstWf-exts hB hΓ' hσ Z = ⊢# Z
SubstWf-exts hB hΓ' hσ (S h) = rename-shift hB hΓ' (hσ h)

SubstWf-⇑ : {Σ : Store} {Δ : TyCtx} {Γ Γ' : Ctx} {σ : Subst} →
  SubstWf Σ Δ Γ Γ' σ →
  SubstWf (renameΣ suc Σ) (suc Δ) (⤊ Γ) (⤊ Γ') (⇑ σ)
SubstWf-⇑ hσ h with lookup-map-inv h
... | A , (hA , eq)
  rewrite eq = typing-renameᵀ (λ {i} i<Δ → s<s i<Δ) (hσ hA)

typing-subst : {Σ : Store} {Δ : TyCtx} {Γ Γ' : Ctx} {M : Term} {A : Ty} {σ : Subst} →
  WfCtx Δ Σ Γ' →
  SubstWf Σ Δ Γ Γ' σ →
  Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
  Σ ∣ Δ ⊢ Γ' ⊢ subst σ M ⦂ A
typing-subst hΓ' hσ (⊢const hΣ hΓ eqA) = ⊢const hΣ hΓ' eqA
typing-subst hΓ' hσ (⊢# h) = hσ h
typing-subst hΓ' hσ (⊢ƛ hA hN) =
  ⊢ƛ hA (typing-subst (wfΓ∷ hΓ' hA) (SubstWf-exts hA hΓ' hσ) hN)
typing-subst hΓ' hσ (⊢· hL hM) =
  ⊢· (typing-subst hΓ' hσ hL) (typing-subst hΓ' hσ hM)
typing-subst {Σ = Σ} {Δ = Δ} {Γ' = Γ'} hΓ' hσ (⊢Λ hN) =
  ⊢Λ
    (typing-subst hΓ'↑ (SubstWf-⇑ hσ) hN)
  where
    hΓ'↑ : WfCtx (suc Δ) (renameΣ suc Σ) (⤊ Γ')
    hΓ'↑ = renameᵗ-preserves-WfCtx hΓ' (λ {i} i<Δ → s<s i<Δ)
typing-subst hΓ' hσ (⊢·[] hM hB) =
  ⊢·[] (typing-subst hΓ' hσ hM) hB
typing-subst hΓ' hσ (⊢⟨⟩ hM cwt) =
  ⊢⟨⟩ (typing-subst hΓ' hσ hM) cwt
typing-subst hΓ' hσ (⊢blame hA) =
  ⊢blame hA

singleSubstWf : {Σ : Store} {Δ : TyCtx} {Γ : Ctx} {A : Ty} {V : Term} →
  Σ ∣ Δ ⊢ Γ ⊢ V ⦂ A →
  SubstWf Σ Δ (A ∷ Γ) Γ (singleEnv V)
singleSubstWf hV Z = hV
singleSubstWf hV (S h) = ⊢# h

typing-single-subst : {Σ : Store} {Δ : TyCtx} {Γ : Ctx} {N V : Term} {A B : Ty} →
  WfCtx Δ Σ Γ →
  Σ ∣ Δ ⊢ (A ∷ Γ) ⊢ N ⦂ B →
  Σ ∣ Δ ⊢ Γ ⊢ V ⦂ A →
  Σ ∣ Δ ⊢ Γ ⊢ N [ V ]ᴹ ⦂ B
typing-single-subst hΓ hN hV =
  typing-subst hΓ (singleSubstWf hV) hN

------------------------------------------------------------------------
-- Term substitution preserves typing (closed-world variant)
------------------------------------------------------------------------

postulate
  preserve-β-ty★-plain : ∀ {Σ M A A₀}
    → Σ ∣ zero ⊢ [] ⊢ ((Λ M ⦂ A₀) ·[ `★ ]) ⦂ A
    → Σ ∣ zero ⊢ [] ⊢ (M [ `★ ]ᵀ) ⦂ A

  preserve-β-ty-wrap★ : ∀ {Σ V c A}
    → Value V
    → Σ ∣ zero ⊢ [] ⊢ ((V ⟨ ∀ᶜ c ⟩) ·[ `★ ]) ⦂ A
    → Σ ∣ zero ⊢ [] ⊢ ((V ·[ `★ ]) ⟨ substᶜᵗ (singleTyEnv `★) c ⟩) ⦂ A

  preserve-β-ty-plain : ∀ {Σ M A A₀ B}
    → NonDyn B
    → Σ ∣ zero ⊢ [] ⊢ ((Λ M ⦂ A₀) ·[ B ]) ⦂ A
    → extendStore Σ B ∣ zero ⊢ [] ⊢
        ((M [ `U (fresh Σ) ]ᵀ) ⟨ coerce⁺ (fresh Σ) (A₀ [ `U (fresh Σ) ]ᵗ) ⟩) ⦂ A

  preserve-β-ty-wrap : ∀ {Σ V A A₀ Aₙ c B}
    → NonDyn B
    → Value V
    → Σ ∣ zero ⊢ ∀ᶜ c ⦂ `∀ A₀ ⇨ `∀ Aₙ
    → Σ ∣ zero ⊢ [] ⊢ ((V ⟨ ∀ᶜ c ⟩) ·[ B ]) ⦂ A
    → extendStore Σ B ∣ zero ⊢ [] ⊢
        (((V ·[ `U (fresh Σ) ]) ⟨ substᶜᵗ (singleTyEnv (`U (fresh Σ))) c ⟩)
          ⟨ coerce⁺ (fresh Σ) (Aₙ [ `U (fresh Σ) ]ᵗ) ⟩) ⦂ A

------------------------------------------------------------------------
-- Transporting typing along store extensions
------------------------------------------------------------------------

record StoreRel (Σ Σ′ : Store) : Set where
  field
    wf-target : WfStore Σ′
    preserve-lookup : ∀ {U A} → Σ ∋ᵁ U ⦂ A → Σ′ ∋ᵁ U ⦂ A

StoreExt : Store → Store → Set
StoreExt = StoreRel

rename-store-rel :
  {Σ Σ′ : Store} {ρ : Renameᵗ} →
  StoreRel Σ Σ′ →
  StoreRel (renameΣ ρ Σ) (renameΣ ρ Σ′)
rename-store-rel rel .StoreRel.wf-target =
  renameᵗ-preserves-WfStore (StoreRel.wf-target rel)
rename-store-rel rel .StoreRel.preserve-lookup {U} {B} h
  with lookupᵁ-map-inv h
... | A , (hA , eq) =
  Eq.subst
    (λ T → renameΣ _ _ ∋ᵁ U ⦂ T)
    (sym eq)
    (lookupᵁ-map-renameᵗ (StoreRel.preserve-lookup rel hA))

mutual
  store-rel-preserves-WfTy :
    {Δ : TyCtx} {Σ Σ′ : Store} {A : Ty} →
    StoreRel Σ Σ′ →
    WfTy Δ Σ A →
    WfTy Δ Σ′ A
  store-rel-preserves-WfTy rel (wfVar x<Δ) = wfVar x<Δ
  store-rel-preserves-WfTy rel wfℕ = wfℕ
  store-rel-preserves-WfTy rel wfBool = wfBool
  store-rel-preserves-WfTy rel wfStr = wfStr
  store-rel-preserves-WfTy rel wf★ = wf★
  store-rel-preserves-WfTy rel (wfU hU) =
    wfU (StoreRel.preserve-lookup rel hU)
  store-rel-preserves-WfTy rel (wf⇒ hA hB) =
    wf⇒
      (store-rel-preserves-WfTy rel hA)
      (store-rel-preserves-WfTy rel hB)
  store-rel-preserves-WfTy {Δ = Δ} rel (wf∀ hA) =
    wf∀
      (store-rel-preserves-WfTy
        (rename-store-rel rel)
        hA)

  store-rel-preserves-WfCtx :
    {Δ : TyCtx} {Σ Σ′ : Store} {Γ : Ctx} →
    StoreRel Σ Σ′ →
    WfCtx Δ Σ Γ →
    WfCtx Δ Σ′ Γ
  store-rel-preserves-WfCtx rel wfΓ∅ = wfΓ∅
  store-rel-preserves-WfCtx rel (wfΓ∷ hΓ hA) =
    wfΓ∷
      (store-rel-preserves-WfCtx rel hΓ)
      (store-rel-preserves-WfTy rel hA)

  store-rel-preserves-coercion :
    {Δ : TyCtx} {Σ Σ′ : Store} {c : Coercion} {A B : Ty} →
    StoreRel Σ Σ′ →
    Σ ∣ Δ ⊢ c ⦂ A ⇨ B →
    Σ′ ∣ Δ ⊢ c ⦂ A ⇨ B
  store-rel-preserves-coercion rel (⊢idᶜ hΣ hA) =
    ⊢idᶜ
      (StoreRel.wf-target rel)
      (store-rel-preserves-WfTy rel hA)
  store-rel-preserves-coercion rel (⊢! hΣ hG gG) =
    ⊢!
      (StoreRel.wf-target rel)
      (store-rel-preserves-WfTy rel hG)
      gG
  store-rel-preserves-coercion rel (⊢? hΣ hG gG) =
    ⊢?
      (StoreRel.wf-target rel)
      (store-rel-preserves-WfTy rel hG)
      gG
  store-rel-preserves-coercion rel (⊢↦ cwt dwt) =
    ⊢↦
      (store-rel-preserves-coercion rel cwt)
      (store-rel-preserves-coercion rel dwt)
  store-rel-preserves-coercion rel (⊢⨟ cwt dwt) =
    ⊢⨟
      (store-rel-preserves-coercion rel cwt)
      (store-rel-preserves-coercion rel dwt)
  store-rel-preserves-coercion rel (⊢conceal hΣ hU) =
    ⊢conceal
      (StoreRel.wf-target rel)
      (StoreRel.preserve-lookup rel hU)
  store-rel-preserves-coercion rel (⊢reveal hΣ hU) =
    ⊢reveal
      (StoreRel.wf-target rel)
      (StoreRel.preserve-lookup rel hU)
  store-rel-preserves-coercion {Δ = Δ} rel (⊢∀ᶜ cwt) =
    ⊢∀ᶜ
      (store-rel-preserves-coercion
        (rename-store-rel rel)
        cwt)
  store-rel-preserves-coercion rel (⊢⊥ hΣ hA hB) =
    ⊢⊥
      (StoreRel.wf-target rel)
      (store-rel-preserves-WfTy rel hA)
      (store-rel-preserves-WfTy rel hB)

  store-rel-preserves-typing :
    {Δ : TyCtx} {Σ Σ′ : Store} {Γ : Ctx} {M : Term} {A : Ty} →
    StoreRel Σ Σ′ →
    Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
    Σ′ ∣ Δ ⊢ Γ ⊢ M ⦂ A
  store-rel-preserves-typing rel (⊢const hΣ hΓ eqA) =
    ⊢const
      (StoreRel.wf-target rel)
      (store-rel-preserves-WfCtx rel hΓ)
      eqA
  store-rel-preserves-typing rel (⊢# h) =
    ⊢# h
  store-rel-preserves-typing rel (⊢ƛ hA hM) =
    ⊢ƛ
      (store-rel-preserves-WfTy rel hA)
      (store-rel-preserves-typing rel hM)
  store-rel-preserves-typing rel (⊢· hL hM) =
    ⊢·
      (store-rel-preserves-typing rel hL)
      (store-rel-preserves-typing rel hM)
  store-rel-preserves-typing {Δ = Δ} rel (⊢Λ hM) =
    ⊢Λ
      (store-rel-preserves-typing
        (rename-store-rel rel)
        hM)
  store-rel-preserves-typing rel (⊢·[] hM hB) =
    ⊢·[]
      (store-rel-preserves-typing rel hM)
      (store-rel-preserves-WfTy rel hB)
  store-rel-preserves-typing rel (⊢⟨⟩ hM cwt) =
    ⊢⟨⟩
      (store-rel-preserves-typing rel hM)
      (store-rel-preserves-coercion rel cwt)
  store-rel-preserves-typing rel (⊢blame hA) =
    ⊢blame (store-rel-preserves-WfTy rel hA)

------------------------------------------------------------------------
-- Blame under frames
------------------------------------------------------------------------

frame-blame : ∀ {Σ F p A}
  → Σ ∣ zero ⊢ [] ⊢ plug F (blame p) ⦂ A
  → Σ ∣ zero ⊢ [] ⊢ blame p ⦂ A
frame-blame h = ⊢blame (typing-wfty h)

∋ᵁ-unique : ∀ {Σ U A B}
  → Σ ∋ᵁ U ⦂ A
  → Σ ∋ᵁ U ⦂ B
  → A ≡ B
∋ᵁ-unique Zᵁ Zᵁ = refl
∋ᵁ-unique (Sᵁ hA) (Sᵁ hB) = ∋ᵁ-unique hA hB

------------------------------------------------------------------------
-- Preservation
------------------------------------------------------------------------

mutual
  preservation : ∀ {Σ Σ′ M N A}
    → StoreExt Σ Σ′
    → Σ ∣ zero ⊢ [] ⊢ M ⦂ A
    → (Σ ⊲ M) —→ (Σ′ ⊲ N)
    → Σ′ ∣ zero ⊢ [] ⊢ N ⦂ A
  preservation hΣ′ M⦂ (ξξ {F = F} refl refl M→N) =
    frame-preservation {F = F} hΣ′ M⦂ M→N
  preservation hΣ′ (⊢· (⊢const x x₁ refl) (⊢const x₂ x₃ refl)) δ =
    ⊢const (hΣ′ .StoreRel.wf-target) wfΓ∅ refl
  preservation hΣ′ (⊢· {A = A} (⊢ƛ {A = A} hA hN) hV) (β-ƛ vV) =
    typing-single-subst wfΓ∅ hN hV
  preservation hΣ′ (⊢⟨⟩ hV (⊢idᶜ _ _)) (β-id vV) = hV
  preservation hΣ′ (⊢· (⊢⟨⟩ hV (⊢↦ cwt dwt)) hW) (β-↦ vV vW) =
    ⊢⟨⟩ (⊢· hV (⊢⟨⟩ hW cwt)) dwt
  preservation hΣ′ (⊢⟨⟩ (⊢⟨⟩ hV (⊢! _ _ _)) (⊢? _ _ _)) (β-proj-inj-ok vV) = hV
  preservation hΣ′ (⊢⟨⟩ (⊢⟨⟩ hV (⊢! _ _ _)) (⊢? _ hG _)) (β-proj-inj-bad vV G≢H) =
    ⊢blame hG
  preservation hΣ′ (⊢⟨⟩ (⊢⟨⟩ hV (⊢conceal _ hU₁)) (⊢reveal _ hU₂)) (β-remove vV)
    with ∋ᵁ-unique hU₁ hU₂
  ... | refl = hV
  preservation hΣ′ (⊢⟨⟩ hV (⊢⨟ cwt dwt)) (β-seq vV) =
    ⊢⟨⟩ (⊢⟨⟩ hV cwt) dwt
  preservation hΣ′ (⊢⟨⟩ hV (⊢⊥ _ _ hB)) (β-fail vV) =
    ⊢blame hB
  preservation hΣ′ M⦂ β-ty★-plain = preserve-β-ty★-plain M⦂
  preservation hΣ′ M⦂ (β-ty-wrap★ vV) = preserve-β-ty-wrap★ vV M⦂
  preservation hΣ′ M⦂ (β-ty-plain ndB) = preserve-β-ty-plain ndB M⦂
  preservation hΣ′ M⦂ (β-ty-wrap ndB vV cwt) = preserve-β-ty-wrap ndB vV cwt M⦂
  preservation hΣ′ M⦂ (ξξ-blame {F = F} refl) = frame-blame {F = F} M⦂

  frame-preservation : ∀ {F Σ Σ′ M N A}
    → StoreExt Σ Σ′
    → Σ ∣ zero ⊢ [] ⊢ plug F M ⦂ A
    → (Σ ⊲ M) —→ (Σ′ ⊲ N)
    → Σ′ ∣ zero ⊢ [] ⊢ plug F N ⦂ A
  frame-preservation {F = □· L} hΣ′ (⊢· hM hL) M→N =
    ⊢·
      (preservation hΣ′ hM M→N)
      (store-rel-preserves-typing hΣ′ hL)
  frame-preservation {F = V ·□ vV} hΣ′ (⊢· hV hM) M→N =
    ⊢·
      (store-rel-preserves-typing hΣ′ hV)
      (preservation hΣ′ hM M→N)
  frame-preservation {F = □·[ B ]} hΣ′ (⊢·[] hM hB) M→N =
    ⊢·[]
      (preservation hΣ′ hM M→N)
      (store-rel-preserves-WfTy hΣ′ hB)
  frame-preservation {F = □⟨ c ⟩} hΣ′ (⊢⟨⟩ hM cwt) M→N =
    ⊢⟨⟩
      (preservation hΣ′ hM M→N)
      (store-rel-preserves-coercion hΣ′ cwt)
