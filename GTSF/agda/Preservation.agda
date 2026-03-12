module Preservation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (cong; cong₂; sym; trans)
open import Data.List using (_∷_; []; map)
open import Data.Nat using (zero; suc)
open import Data.Nat.Base using (_<_; z<s; s<s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import PolyCoercions
open import PolyCastCalculus
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

renameᵗ-preserves-WfStore : {Δ Δ' : TyCtx} {Σ : Store} {ρ : Renameᵗ} →
  TyRenameWf Δ Δ' ρ →
  WfStore Δ Σ →
  WfStore Δ' (renameΣ ρ Σ)
renameᵗ-preserves-WfStore wfρ wfΣ∅ = wfΣ∅
renameᵗ-preserves-WfStore wfρ (wfΣ∷ wfΣ ndA wfA) =
  let xx = renameᵗ-preserves-WfTy wfA wfρ in 
  wfΣ∷ (renameᵗ-preserves-WfStore wfρ wfΣ) (renameᵗ-preserves-NonDyn ndA) xx

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

renameᵗ-ty-const : {ρ : Renameᵗ} {k : Const} →
  renameᵗ ρ (ty k) ≡ ty k
renameᵗ-ty-const {k = nat n} = refl
renameᵗ-ty-const {k = bool b} = refl

substᵗ-ty-const : {σ : Substᵗ} {k : Const} →
  substᵗ σ (ty k) ≡ ty k
substᵗ-ty-const {k = nat n} = refl
substᵗ-ty-const {k = bool b} = refl

renameᶜᵗ-preserves-typing :
  {Σ : Store} {Δ Δ' : TyCtx} {c : Coercion} {A B : Ty} {ρ : Renameᵗ} →
  TyRenameWf Δ Δ' ρ →
  Σ ∣ Δ ⊢ c ⦂ A ⇨ B →
  renameΣ ρ Σ ∣ Δ' ⊢ renameᶜᵗ ρ c ⦂ renameᵗ ρ A ⇨ renameᵗ ρ B
renameᶜᵗ-preserves-typing hρ (⊢idᶜ hΣ hA) =
  ⊢idᶜ
    (renameᵗ-preserves-WfStore hρ hΣ)
    (renameᵗ-preserves-WfTy hA hρ)
renameᶜᵗ-preserves-typing hρ (⊢! hΣ hG gG) =
  ⊢!
    (renameᵗ-preserves-WfStore hρ hΣ)
    (renameᵗ-preserves-WfTy hG hρ)
    (renameᵗ-preserves-Ground gG)
renameᶜᵗ-preserves-typing hρ (⊢? hΣ hG gG) =
  ⊢?
    (renameᵗ-preserves-WfStore hρ hΣ)
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
    (renameᵗ-preserves-WfStore hρ hΣ)
    (lookupᵁ-map-renameᵗ hU)
renameᶜᵗ-preserves-typing hρ (⊢reveal hΣ hU) =
  ⊢reveal
    (renameᵗ-preserves-WfStore hρ hΣ)
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
    (renameᵗ-preserves-WfStore hρ hΣ)
    (renameᵗ-preserves-WfTy hA hρ)
    (renameᵗ-preserves-WfTy hB hρ)

typing-renameᵀ :
  {Σ : Store} {Δ Δ' : TyCtx} {Γ : Ctx} {M : Term} {A : Ty} {ρ : Renameᵗ} →
  TyRenameWf Δ Δ' ρ →
  Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
  renameΣ ρ Σ ∣ Δ' ⊢ map (renameᵗ ρ) Γ ⊢ renameᵀ ρ M ⦂ renameᵗ ρ A
typing-renameᵀ {Σ = Σ} {Δ' = Δ'} {Γ = Γ} {ρ = ρ} hρ (⊢const {k = k} hΣ hΓ) =
  Eq.subst
    (λ T → renameΣ ρ Σ ∣ Δ' ⊢ map (renameᵗ ρ) Γ ⊢ $k k ⦂ T)
    (sym (renameᵗ-ty-const {ρ = ρ} {k = k}))
    (⊢const
      (renameᵗ-preserves-WfStore hρ hΣ)
      (renameᵗ-preserves-WfCtx hΓ hρ))
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
  {Δ Δ' : TyCtx} {Σ : Store} {σ : Substᵗ} →
  TySubstWf Δ Δ' Σ σ →
  WfStore Δ Σ →
  WfStore Δ' (substΣ σ Σ)
substᵗ-preserves-WfStore hσ wfΣ∅ = wfΣ∅
substᵗ-preserves-WfStore {Σ = A ∷ Σ} hσ (wfΣ∷ {A = A} wfΣ ndA wfA) =
  let hσ' = TySubstWf-tail {A = A} hσ in
  wfΣ∷
    (substᵗ-preserves-WfStore hσ' wfΣ)
    (substᵗ-preserves-NonDyn wfA ndA hσ')
    (substᵗ-preserves-WfTy wfA hσ')

substᵗ-preserves-⊢! :
  {Σ : Store} {Δ Δ' : TyCtx} {G : Ty} {σ : Substᵗ} →
  TySubstWfᶜ Δ Δ' Σ σ →
  WfStore Δ Σ →
  WfTy Δ Σ G →
  Ground G →
  substΣ σ Σ ∣ Δ' ⊢ injᶜ (substᵗ σ G) ⦂ substᵗ σ G ⇨ `★
substᵗ-preserves-⊢! {G = ` X} hσ hΣ (wfVar {X = X} x<Δ) G-var
  with u★Var-view (proj₂ hσ {X = X} x<Δ)
... | u★v-isVar Y eq
  = cast-injᶜ-typing eq
      (⊢!
        (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
        (cast-WfTy eq (proj₁ (proj₁ hσ {X = X} x<Δ)))
        G-var)
... | u★v-is★ eq
  = cast-injᶜ-typing eq
      (⊢idᶜ
        (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
        (cast-WfTy eq (proj₁ (proj₁ hσ {X = X} x<Δ))))
... | u★v-isU U eq
  = cast-injᶜ-typing eq
      (⊢!
        (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
        (cast-WfTy eq (proj₁ (proj₁ hσ {X = X} x<Δ)))
        G-U)
substᵗ-preserves-⊢! hσ hΣ hG G-ℕ =
  ⊢!
    (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-ℕ
substᵗ-preserves-⊢! hσ hΣ hG G-Bool =
  ⊢!
    (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-Bool
substᵗ-preserves-⊢! hσ hΣ hG G-Str =
  ⊢!
    (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-Str
substᵗ-preserves-⊢! hσ hΣ hG G-⇒★ =
  ⊢!
    (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-⇒★
substᵗ-preserves-⊢! hσ hΣ hG G-∀★ =
  ⊢!
    (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-∀★
substᵗ-preserves-⊢! hσ hΣ hG G-U =
  ⊢!
    (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-U

substᵗ-preserves-⊢? :
  {Σ : Store} {Δ Δ' : TyCtx} {G : Ty} {p : Label} {σ : Substᵗ} →
  TySubstWfᶜ Δ Δ' Σ σ →
  WfStore Δ Σ →
  WfTy Δ Σ G →
  Ground G →
  substΣ σ Σ ∣ Δ' ⊢ projᶜ (substᵗ σ G) p ⦂ `★ ⇨ substᵗ σ G
substᵗ-preserves-⊢? {G = ` X} {p = p} hσ hΣ (wfVar {X = X} x<Δ) G-var
  with u★Var-view (proj₂ hσ {X = X} x<Δ)
... | u★v-isVar Y eq
  = cast-projᶜ-typing eq
      (⊢?
        (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
        (cast-WfTy eq (proj₁ (proj₁ hσ {X = X} x<Δ)))
        G-var)
... | u★v-is★ eq
  = cast-projᶜ-typing eq
      (⊢idᶜ
        (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
        (cast-WfTy eq (proj₁ (proj₁ hσ {X = X} x<Δ))))
... | u★v-isU U eq
  = cast-projᶜ-typing eq
      (⊢?
        (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
        (cast-WfTy eq (proj₁ (proj₁ hσ {X = X} x<Δ)))
        G-U)
substᵗ-preserves-⊢? hσ hΣ hG G-ℕ =
  ⊢?
    (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-ℕ
substᵗ-preserves-⊢? hσ hΣ hG G-Bool =
  ⊢?
    (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-Bool
substᵗ-preserves-⊢? hσ hΣ hG G-Str =
  ⊢?
    (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-Str
substᵗ-preserves-⊢? hσ hΣ hG G-⇒★ =
  ⊢?
    (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-⇒★
substᵗ-preserves-⊢? hσ hΣ hG G-∀★ =
  ⊢?
    (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-∀★
substᵗ-preserves-⊢? hσ hΣ hG G-U =
  ⊢?
    (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
    (substᵗ-preserves-WfTy hG (proj₁ hσ))
    G-U

substᶜᵗ-preserves-typing :
  {Σ : Store} {Δ Δ' : TyCtx} {c : Coercion} {A B : Ty} {σ : Substᵗ} →
  TySubstWfᶜ Δ Δ' Σ σ →
  Σ ∣ Δ ⊢ c ⦂ A ⇨ B →
  substΣ σ Σ ∣ Δ' ⊢ substᶜᵗ σ c ⦂ substᵗ σ A ⇨ substᵗ σ B
substᶜᵗ-preserves-typing hσ (⊢idᶜ hΣ hA) =
  ⊢idᶜ
    (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
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
    (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
    (lookupᵁ-map-substᵗ hU)
substᶜᵗ-preserves-typing hσ (⊢reveal hΣ hU) =
  ⊢reveal
    (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
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
    (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
    (substᵗ-preserves-WfTy hA (proj₁ hσ))
    (substᵗ-preserves-WfTy hB (proj₁ hσ))

typing-substᵀ :
  {Σ : Store} {Δ Δ' : TyCtx} {Γ : Ctx} {M : Term} {A : Ty} {σ : Substᵗ} →
  TySubstWfᶜ Δ Δ' Σ σ →
  Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
  substΣ σ Σ ∣ Δ' ⊢ map (substᵗ σ) Γ ⊢ substᵀ σ M ⦂ substᵗ σ A
typing-substᵀ {Σ = Σ} {Δ' = Δ'} {Γ = Γ} {σ = σ} hσ (⊢const {k = k} hΣ hΓ) =
  Eq.subst
    (λ T → substΣ σ Σ ∣ Δ' ⊢ map (substᵗ σ) Γ ⊢ $k k ⦂ T)
    (sym (substᵗ-ty-const {σ = σ} {k = k}))
    (⊢const
      (substᵗ-preserves-WfStore (proj₁ hσ) hΣ)
      (substᵗ-preserves-WfCtx hΓ (proj₁ hσ)))
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

postulate
  typing-rename : {Σ : Store} {Δ : TyCtx} {Γ Γ' : Ctx} {M : Term} {A : Ty} {ρ : Rename} →
    RenameWf Γ Γ' ρ →
    Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
    Σ ∣ Δ ⊢ Γ' ⊢ rename ρ M ⦂ A

rename-shift : {Σ : Store} {Δ : TyCtx} {Γ : Ctx} {M : Term} {A B : Ty} →
  Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
  Σ ∣ Δ ⊢ (B ∷ Γ) ⊢ rename suc M ⦂ A
rename-shift hM =
  typing-rename (λ {x} {A} h → S h) hM

SubstWf-exts : {Σ : Store} {Δ : TyCtx} {Γ Γ' : Ctx} {B : Ty} {σ : Subst} →
  SubstWf Σ Δ Γ Γ' σ →
  SubstWf Σ Δ (B ∷ Γ) (B ∷ Γ') (exts σ)
SubstWf-exts hσ Z = ⊢# Z
SubstWf-exts hσ (S h) = rename-shift (hσ h)

⇑ : Subst → Subst
⇑ σ i = renameᵀ suc (σ i)

SubstWf-⇑ : {Σ : Store} {Δ : TyCtx} {Γ Γ' : Ctx} {σ : Subst} →
  SubstWf Σ Δ Γ Γ' σ →
  SubstWf (renameΣ suc Σ) (suc Δ) (⤊ Γ) (⤊ Γ') (⇑ σ)
SubstWf-⇑ hσ h with lookup-map-inv h
... | A , (hA , eq)
  rewrite eq = typing-renameᵀ (λ {i} i<Δ → s<s i<Δ) (hσ hA)

postulate
  typing-subst : {Σ : Store} {Δ : TyCtx} {Γ Γ' : Ctx} {M : Term} {A : Ty} {σ : Subst} →
    SubstWf Σ Δ Γ Γ' σ →
    Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A →
    Σ ∣ Δ ⊢ Γ' ⊢ subst σ M ⦂ A

singleSubstWf : {Σ : Store} {Δ : TyCtx} {Γ : Ctx} {A : Ty} {V : Term} →
  Σ ∣ Δ ⊢ Γ ⊢ V ⦂ A →
  SubstWf Σ Δ (A ∷ Γ) Γ (singleEnv V)
singleSubstWf hV Z = hV
singleSubstWf hV (S h) = ⊢# h

typing-single-subst : {Σ : Store} {Δ : TyCtx} {Γ : Ctx} {N V : Term} {A B : Ty} →
  Σ ∣ Δ ⊢ (A ∷ Γ) ⊢ N ⦂ B →
  Σ ∣ Δ ⊢ Γ ⊢ V ⦂ A →
  Σ ∣ Δ ⊢ Γ ⊢ N [ V ]ᴹ ⦂ B
typing-single-subst hN hV =
  typing-subst (singleSubstWf hV) hN

------------------------------------------------------------------------
-- Term substitution preserves typing (closed-world variant)
------------------------------------------------------------------------

postulate
  impossible-βδ : ∀ {Σ A k₁ k₂}
    → Σ ∣ zero ⊢ [] ⊢ ($k k₁ · $k k₂) ⦂ A
    → ⊥

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
    → Σ ∣ zero ⊢ [] ⊢ M ⦂ A
    → (Σ ⊲ M) —→ (Σ′ ⊲ N)
    → Σ′ ∣ zero ⊢ [] ⊢ N ⦂ A
  preservation M⦂ (ξξ {F = F} refl refl M→N) =
    frame-preservation {F = F} M⦂ M→N
  preservation M⦂ β-δ with impossible-βδ M⦂
  ... | ()
  preservation (⊢· {A = A} (⊢ƛ {A = A} hA hN) hV) (β-ƛ vV) =
    typing-single-subst hN hV
  preservation (⊢⟨⟩ hV (⊢idᶜ _ _)) (β-id vV) = hV
  preservation (⊢· (⊢⟨⟩ hV (⊢↦ cwt dwt)) hW) (β-↦ vV vW) =
    ⊢⟨⟩ (⊢· hV (⊢⟨⟩ hW cwt)) dwt
  preservation (⊢⟨⟩ (⊢⟨⟩ hV (⊢! _ _ _)) (⊢? _ _ _)) (β-proj-inj-ok vV) = hV
  preservation (⊢⟨⟩ (⊢⟨⟩ hV (⊢! _ _ _)) (⊢? _ hG _)) (β-proj-inj-bad vV G≢H) =
    ⊢blame hG
  preservation (⊢⟨⟩ (⊢⟨⟩ hV (⊢conceal _ hU₁)) (⊢reveal _ hU₂)) (β-remove vV)
    with ∋ᵁ-unique hU₁ hU₂
  ... | refl = hV
  preservation (⊢⟨⟩ hV (⊢⨟ cwt dwt)) (β-seq vV) =
    ⊢⟨⟩ (⊢⟨⟩ hV cwt) dwt
  preservation (⊢⟨⟩ hV (⊢⊥ _ _ hB)) (β-fail vV) =
    ⊢blame hB
  preservation M⦂ β-ty★-plain = preserve-β-ty★-plain M⦂
  preservation M⦂ (β-ty-wrap★ vV) = preserve-β-ty-wrap★ vV M⦂
  preservation (⊢·[] (⊢⟨⟩ (⊢Λ hM) (⊢∀ᶜ cwt)) hB) β-ty★ = {!!}
  preservation M⦂ (β-ty-plain ndB) = preserve-β-ty-plain ndB M⦂
  preservation M⦂ (β-ty-wrap ndB vV cwt) = preserve-β-ty-wrap ndB vV cwt M⦂
  preservation (⊢·[] (⊢⟨⟩ (⊢Λ hM) (⊢∀ᶜ cwt)) hB) (β-ty ndB cwt0) = {!!}
  preservation M⦂ (ξξ-blame {F = F} refl) =
    frame-blame {F = F} M⦂

  frame-preservation : ∀ {F Σ Σ′ M N A}
    → Σ ∣ zero ⊢ [] ⊢ plug F M ⦂ A
    → (Σ ⊲ M) —→ (Σ′ ⊲ N)
    → Σ′ ∣ zero ⊢ [] ⊢ plug F N ⦂ A
  frame-preservation M⦂ M→N = {!!}
