module proof.PreservationTermSubst where

-- File Charter:
--   * Ordinary term-variable substitution preservation for PolyConvert terms.
--   * Exports a parallel substitution theorem over `substˣᵐ` and the single
--     substitution corollary for the existing `N [ V ]` notation.
--   * Depends on existing type-substitution preservation for conversions and on
--     the imprecision insertion helper used when crossing type binders.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; length; map; _++_; _∷_)
open import Data.Nat using (_+_; suc; zero; z<s; s<s)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import proof.TypeProperties
  using
    ( TySubstWf )
open import Ctx using (⤊ᵗ; map-renameᵗ-⤊ᵗ)
open import Imprecision
open import Conversion
open import Store using (substStoreᵗ; renameStoreᵗ-ext-⟰ᵗ)
open import Primitives
open import Terms
open import proof.ConversionProperties
  using (cong-⊢↑; cong-⊢↓; subst↑-wt; subst↓-wt)
open import proof.ImprecisionProperties
  using
    ( cong-⊢⊑-raw
    ; renameImp-cong
    ; wkImpAt
    )
open import proof.TypeProperties
  using
    ( raise-ext
    ; rename-raise-ext
    )

cong₃ : ∀ {A B C D : Set}
  (f : A → B → C → D)
  {x x′ : A}{y y′ : B}{z z′ : C} →
  x ≡ x′ →
  y ≡ y′ →
  z ≡ z′ →
  f x y z ≡ f x′ y′ z′
cong₃ f refl refl refl = refl

------------------------------------------------------------------------
-- Term-variable renaming environments
------------------------------------------------------------------------

Renameˣ-wt : (Γ Γ′ : Ctx) (ρ : Renameˣ) → Set
Renameˣ-wt Γ Γ′ ρ =
  ∀ {A : Ty}{x : Var} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A

extʳ-wt : ∀ {Γ Γ′ : Ctx}{A : Ty} (ρ : Renameˣ) →
  Renameˣ-wt Γ Γ′ ρ →
  Renameˣ-wt (A ∷ Γ) (A ∷ Γ′) (extʳ ρ)
extʳ-wt ρ hρ Z = Z
extʳ-wt ρ hρ (S h) = S (hρ h)

wkʳ-wt : ∀ {Γ : Ctx}{A B : Ty}{x : Var} →
  Γ ∋ x ⦂ A →
  (B ∷ Γ) ∋ suc x ⦂ A
wkʳ-wt h = S h

map∋ : ∀ {Γ : Ctx}{x : Var}{A : Ty} (f : Ty → Ty) →
  Γ ∋ x ⦂ A →
  map f Γ ∋ x ⦂ f A
map∋ f Z = Z
map∋ f (S h) = S (map∋ f h)

unmap∋-⤊ᵗ : ∀ {Γ : Ctx}{x : Var}{A : Ty} →
  ⤊ᵗ Γ ∋ x ⦂ A →
  Σ[ B ∈ Ty ] (A ≡ renameᵗ suc B) × (Γ ∋ x ⦂ B)
unmap∋-⤊ᵗ {Γ = B ∷ Γ} Z = B , refl , Z
unmap∋-⤊ᵗ {Γ = B ∷ Γ} (S h) with unmap∋-⤊ᵗ {Γ = Γ} h
... | C , eq , h′ = C , eq , S h′

liftᵗʳ-wt : ∀ {Γ Γ′ : Ctx} (ρ : Renameˣ) →
  Renameˣ-wt Γ Γ′ ρ →
  Renameˣ-wt (⤊ᵗ Γ) (⤊ᵗ Γ′) ρ
liftᵗʳ-wt {Γ′ = Γ′} ρ hρ {x = x} h with unmap∋-⤊ᵗ h
... | B , eq , h₀ =
  subst
    (λ T → ⤊ᵗ Γ′ ∋ ρ x ⦂ T)
    (sym eq)
    (map∋ (renameᵗ suc) (hρ h₀))

------------------------------------------------------------------------
-- Values are stable under the renamings/substitutions used here
------------------------------------------------------------------------

renameˣᵐ-value : ∀ {V} (ρ : Renameˣ) →
  Value V →
  Value (renameˣᵐ ρ V)
renameˣᵐ-value ρ (ƛ A ⇒ N) = ƛ A ⇒ renameˣᵐ (extʳ ρ) N
renameˣᵐ-value ρ ($ κ) = $ κ
renameˣᵐ-value ρ (Λ N) = Λ renameˣᵐ ρ N
renameˣᵐ-value ρ (vV ⇑ p) = renameˣᵐ-value ρ vV ⇑ p
renameˣᵐ-value ρ (vV ⇓ p) = renameˣᵐ-value ρ vV ⇓ p
renameˣᵐ-value ρ (vV ↑ c) = renameˣᵐ-value ρ vV ↑ c
renameˣᵐ-value ρ (vV ↓ c) = renameˣᵐ-value ρ vV ↓ c

renameImp-up-value : ∀ ρ {p} →
  UpValue p →
  UpValue (renameImp ρ p)
renameImp-up-value ρ tagν = tagν
renameImp-up-value ρ tag = tag
renameImp-up-value ρ (_↦_) = _↦_
renameImp-up-value ρ `∀ = `∀

renameImp-down-value : ∀ ρ {p} →
  DownValue p →
  DownValue (renameImp ρ p)
renameImp-down-value ρ (_↦_) = _↦_
renameImp-down-value ρ `∀ = `∀
renameImp-down-value ρ (ν_) = ν_

subst↑-ren-reveal-value : (ρ : Renameᵗ) {c : Conv↑} →
  RevealValue c →
  RevealValue (subst↑ (λ X → ＇ ρ X) c)
subst↑-ren-reveal-value ρ (_↦_) = _↦_
subst↑-ren-reveal-value ρ `∀ = `∀

subst↓-ren-conceal-value : (ρ : Renameᵗ) {c : Conv↓} →
  ConcealValue c →
  ConcealValue (subst↓ (λ X → ＇ ρ X) c)
subst↓-ren-conceal-value ρ seal = seal
subst↓-ren-conceal-value ρ (_↦_) = _↦_
subst↓-ren-conceal-value ρ `∀ = `∀

renameᵗᵐ-value : ∀ {V} ρ →
  Value V →
  Value (renameᵗᵐ ρ V)
renameᵗᵐ-value ρ (ƛ A ⇒ N) = ƛ renameᵗ ρ A ⇒ renameᵗᵐ ρ N
renameᵗᵐ-value ρ ($ κ) = $ κ
renameᵗᵐ-value ρ (Λ N) = Λ renameᵗᵐ (extᵗ ρ) N
renameᵗᵐ-value ρ (vV ⇑ p) =
  renameᵗᵐ-value ρ vV ⇑ renameImp-up-value ρ p
renameᵗᵐ-value ρ (vV ⇓ p) =
  renameᵗᵐ-value ρ vV ⇓ renameImp-down-value ρ p
renameᵗᵐ-value ρ (vV ↑ c) =
  renameᵗᵐ-value ρ vV ↑ subst↑-ren-reveal-value ρ c
renameᵗᵐ-value ρ (vV ↓ c) =
  renameᵗᵐ-value ρ vV ↓ subst↓-ren-conceal-value ρ c

substˣᵐ-value : ∀ {V} (σ : Substˣ) →
  Value V →
  Value (substˣᵐ σ V)
substˣᵐ-value σ (ƛ A ⇒ N) = ƛ A ⇒ substˣᵐ (extˢˣ σ) N
substˣᵐ-value σ ($ κ) = $ κ
substˣᵐ-value σ (Λ N) = Λ substˣᵐ (↑ᵗᵐ σ) N
substˣᵐ-value σ (vV ⇑ p) = substˣᵐ-value σ vV ⇑ p
substˣᵐ-value σ (vV ⇓ p) = substˣᵐ-value σ vV ⇓ p
substˣᵐ-value σ (vV ↑ c) = substˣᵐ-value σ vV ↑ c
substˣᵐ-value σ (vV ↓ c) = substˣᵐ-value σ vV ↓ c

------------------------------------------------------------------------
-- Congruence for type-variable actions used by insertion transports
------------------------------------------------------------------------

mutual
  subst↑-cong : ∀ {σ τ : Substᵗ} →
    ((X : TyVar) → σ X ≡ τ X) →
    (c : Conv↑) →
    subst↑ σ c ≡ subst↑ τ c
  subst↑-cong h (↑-unseal α) = refl
  subst↑-cong h (↑-⇒ p q) =
    cong₂ ↑-⇒ (subst↓-cong h p) (subst↑-cong h q)
  subst↑-cong h (↑-∀ c) = cong ↑-∀ (subst↑-cong h-ext c)
    where
      h-ext : (X : TyVar) → extsᵗ _ X ≡ extsᵗ _ X
      h-ext zero = refl
      h-ext (suc X) = cong (renameᵗ suc) (h X)
  subst↑-cong h (↑-id A) = cong ↑-id (substᵗ-cong h A)

  subst↓-cong : ∀ {σ τ : Substᵗ} →
    ((X : TyVar) → σ X ≡ τ X) →
    (c : Conv↓) →
    subst↓ σ c ≡ subst↓ τ c
  subst↓-cong h (↓-seal α) = refl
  subst↓-cong h (↓-⇒ p q) =
    cong₂ ↓-⇒ (subst↑-cong h p) (subst↓-cong h q)
  subst↓-cong h (↓-∀ c) = cong ↓-∀ (subst↓-cong h-ext c)
    where
      h-ext : (X : TyVar) → extsᵗ _ X ≡ extsᵗ _ X
      h-ext zero = refl
      h-ext (suc X) = cong (renameᵗ suc) (h X)
  subst↓-cong h (↓-id A) = cong ↓-id (substᵗ-cong h A)

renameᵗᵐ-cong : ∀ {ρ ρ′ : Renameᵗ} →
  ((X : TyVar) → ρ X ≡ ρ′ X) →
  (M : Term) →
  renameᵗᵐ ρ M ≡ renameᵗᵐ ρ′ M
renameᵗᵐ-cong h (` x) = refl
renameᵗᵐ-cong h (ƛ A ⇒ M) =
  cong₂ ƛ_⇒_ (rename-cong h A) (renameᵗᵐ-cong h M)
renameᵗᵐ-cong h (L · M) =
  cong₂ _·_ (renameᵗᵐ-cong h L) (renameᵗᵐ-cong h M)
renameᵗᵐ-cong h (Λ M) = cong Λ_ (renameᵗᵐ-cong h-ext M)
  where
    h-ext : (X : TyVar) → extᵗ _ X ≡ extᵗ _ X
    h-ext zero = refl
    h-ext (suc X) = cong suc (h X)
renameᵗᵐ-cong h (M ⦂∀ B [ T ]) =
  cong₃ _⦂∀_[_]
    (renameᵗᵐ-cong h M)
    (rename-cong h-ext B)
    (rename-cong h T)
  where
    h-ext : (X : TyVar) → extᵗ _ X ≡ extᵗ _ X
    h-ext zero = refl
    h-ext (suc X) = cong suc (h X)
renameᵗᵐ-cong h ($ κ) = refl
renameᵗᵐ-cong h (L ⊕[ op ] M) =
  cong₃ _⊕[_]_ (renameᵗᵐ-cong h L) refl (renameᵗᵐ-cong h M)
renameᵗᵐ-cong h (M ⇑ p) =
  cong₂ _⇑_ (renameᵗᵐ-cong h M) (renameImp-cong h p)
renameᵗᵐ-cong h (M ⇓ p) =
  cong₂ _⇓_ (renameᵗᵐ-cong h M) (renameImp-cong h p)
renameᵗᵐ-cong h (M ↑ c) =
  cong₂ _↑_ (renameᵗᵐ-cong h M) (subst↑-cong (λ X → cong ＇_ (h X)) c)
renameᵗᵐ-cong h (M ↓ c) =
  cong₂ _↓_ (renameᵗᵐ-cong h M) (subst↓-cong (λ X → cong ＇_ (h X)) c)
renameᵗᵐ-cong h (blame ℓ) = refl

renameStoreᵗ-cong : ∀ {ρ ρ′ : Renameᵗ} →
  ((X : TyVar) → ρ X ≡ ρ′ X) →
  (Σ : Store) →
  renameStoreᵗ ρ Σ ≡ renameStoreᵗ ρ′ Σ
renameStoreᵗ-cong h [] = refl
renameStoreᵗ-cong h ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (rename-cong h A))
    (renameStoreᵗ-cong h Σ)

map-renameᵗ-cong : ∀ {ρ ρ′ : Renameᵗ} →
  ((X : TyVar) → ρ X ≡ ρ′ X) →
  (Γ : Ctx) →
  map (renameᵗ ρ) Γ ≡ map (renameᵗ ρ′) Γ
map-renameᵗ-cong h [] = refl
map-renameᵗ-cong h (A ∷ Γ) =
  cong₂ _∷_ (rename-cong h A) (map-renameᵗ-cong h Γ)

------------------------------------------------------------------------
-- Type-variable weakening of terms
------------------------------------------------------------------------

raiseWfPlus : ∀ k {Δ} →
  TyRenameWf (k + Δ) (suc (k + Δ)) (raiseVarFrom k)
raiseWfPlus zero X<Δ = TyRenameWf-suc X<Δ
raiseWfPlus (suc k) {Δ} {zero} z<s = z<s
raiseWfPlus (suc k) {Δ} {suc X} (s<s X<Δ) =
  s<s (raiseWfPlus k X<Δ)

renSubst-raise-wf : ∀ k {Δ Ψ} →
  TySubstWf (k + Δ) (suc (k + Δ)) Ψ
    (λ X → ＇ raiseVarFrom k X)
renSubst-raise-wf k {Δ = Δ} X<Δ =
  wfVar (raiseWfPlus k {Δ = Δ} X<Δ)

plains-++ : ∀ k Δ →
  plains (k + Δ) [] ≡ plains k [] ++ plains Δ []
plains-++ zero Δ = refl
plains-++ (suc k) Δ = cong (X⊑X ∷_) (plains-++ k Δ)

length-plains : ∀ k →
  length (plains k []) ≡ k
length-plains zero = refl
length-plains (suc k) = cong suc (length-plains k)

plains-insert : ∀ k Δ →
  plains k [] ++ X⊑X ∷ plains Δ [] ≡ plains (suc (k + Δ)) []
plains-insert zero Δ = refl
plains-insert (suc k) Δ = cong (X⊑X ∷_) (plains-insert k Δ)

wkImp-plains :
  ∀ k {Δ Ψ p A B} →
  Ψ ∣ plains (k + Δ) [] ⊢ p ⦂ A ⊑ B →
  Ψ ∣ plains (suc (k + Δ)) [] ⊢ renameImp (raiseVarFrom k) p ⦂
    renameᵗ (raiseVarFrom k) A ⊑ renameᵗ (raiseVarFrom k) B
wkImp-plains k {Δ} {Ψ} {p} {A} {B} p⊢ =
  subst
    (λ Γᵢ →
      Ψ ∣ Γᵢ ⊢ renameImp (raiseVarFrom k) p ⦂
        renameᵗ (raiseVarFrom k) A ⊑ renameᵗ (raiseVarFrom k) B)
    (plains-insert k Δ)
    (cong-⊢⊑-raw
      (renameImp-cong len-eq p)
      (rename-cong len-eq A)
      (rename-cong len-eq B)
      (wkImpAt {Φ = plains k []} {Γ = plains Δ []}
        (subst (λ Γᵢ → Ψ ∣ Γᵢ ⊢ p ⦂ A ⊑ B) (plains-++ k Δ) p⊢)))
  where
    len-eq : (X : TyVar) →
      raiseVarFrom (length (plains k [])) X ≡ raiseVarFrom k X
    len-eq X = cong (λ n → raiseVarFrom n X) (length-plains k)

renameStoreᵗ-raise-⟰ᵗ : ∀ k (Σ : Store) →
  renameStoreᵗ (raiseVarFrom (suc k)) (⟰ᵗ Σ) ≡
  ⟰ᵗ (renameStoreᵗ (raiseVarFrom k) Σ)
renameStoreᵗ-raise-⟰ᵗ k Σ =
  trans
    (renameStoreᵗ-cong (λ X → sym (raise-ext k X)) (⟰ᵗ Σ))
    (renameStoreᵗ-ext-⟰ᵗ (raiseVarFrom k) Σ)

map-renameᵗ-raise-⤊ᵗ : ∀ k (Γ : Ctx) →
  map (renameᵗ (raiseVarFrom (suc k))) (⤊ᵗ Γ) ≡
  ⤊ᵗ (map (renameᵗ (raiseVarFrom k)) Γ)
map-renameᵗ-raise-⤊ᵗ k Γ =
  trans
    (map-renameᵗ-cong (λ X → sym (raise-ext k X)) (⤊ᵗ Γ))
    (map-renameᵗ-⤊ᵗ (raiseVarFrom k) Γ)

renameᵗ-[]ᵗ :
  (ρ : Renameᵗ) (A T : Ty) →
  renameᵗ ρ (A [ T ]ᵗ) ≡
  (renameᵗ (extᵗ ρ) A) [ renameᵗ ρ T ]ᵗ
renameᵗ-[]ᵗ ρ A T =
  trans
    (renameᵗ-substᵗ ρ (singleTyEnv T) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-renameᵗ (extᵗ ρ) (singleTyEnv (renameᵗ ρ T)) A)))
  where
    env :
      (X : TyVar) →
      renameᵗ ρ (singleTyEnv T X) ≡
      singleTyEnv (renameᵗ ρ T) (extᵗ ρ X)
    env zero = refl
    env (suc X) = refl

substᵗ-ren : (ρ : Renameᵗ) (A : Ty) →
  substᵗ (λ X → ＇ ρ X) A ≡ renameᵗ ρ A
substᵗ-ren ρ (＇ X) = refl
substᵗ-ren ρ (｀ α) = refl
substᵗ-ren ρ (‵ ι) = refl
substᵗ-ren ρ ★ = refl
substᵗ-ren ρ (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-ren ρ A) (substᵗ-ren ρ B)
substᵗ-ren ρ (`∀ A) =
  cong `∀
    (trans
      (substᵗ-cong env A)
      (substᵗ-ren (extᵗ ρ) A))
  where
    env : (X : TyVar) →
      extsᵗ (λ Y → ＇ ρ Y) X ≡ ＇ extᵗ ρ X
    env zero = refl
    env (suc X) = refl

substStoreᵗ-ren : (ρ : Renameᵗ) (Σ : Store) →
  substStoreᵗ (λ X → ＇ ρ X) Σ ≡ renameStoreᵗ ρ Σ
substStoreᵗ-ren ρ [] = refl
substStoreᵗ-ren ρ ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (substᵗ-ren ρ A))
    (substStoreᵗ-ren ρ Σ)

renameᵗᵐ-raise-wt :
  ∀ k {Δ Ψ}{Σ : Store}{Γ : Ctx}{M : Term}{A : Ty} →
  (k + Δ) ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  suc (k + Δ) ∣ Ψ ∣ renameStoreᵗ (raiseVarFrom k) Σ ∣
    map (renameᵗ (raiseVarFrom k)) Γ ⊢
    renameᵗᵐ (raiseVarFrom k) M ⦂ renameᵗ (raiseVarFrom k) A
renameᵗᵐ-raise-wt k (⊢` h) = ⊢` (map∋ (renameᵗ (raiseVarFrom k)) h)
renameᵗᵐ-raise-wt k {Δ = Δ} (⊢ƛ wfA M⊢) =
  ⊢ƛ
    (renameᵗ-preserves-WfTy wfA (raiseWfPlus k {Δ = Δ}))
    (renameᵗᵐ-raise-wt k M⊢)
renameᵗᵐ-raise-wt k (⊢· L⊢ M⊢) =
  ⊢· (renameᵗᵐ-raise-wt k L⊢) (renameᵗᵐ-raise-wt k M⊢)
renameᵗᵐ-raise-wt k {Σ = Σ} {Γ = Γ}
  (⊢Λ {M = M} {A = A} vM M⊢) =
  ⊢Λ (renameᵗᵐ-value (extᵗ (raiseVarFrom k)) vM)
    (cong-⊢⦂
      (renameStoreᵗ-raise-⟰ᵗ k Σ)
      (map-renameᵗ-raise-⤊ᵗ k Γ)
      (renameᵗᵐ-cong (λ X → sym (raise-ext k X)) M)
      (sym (rename-raise-ext k A))
      (renameᵗᵐ-raise-wt (suc k) M⊢))
renameᵗᵐ-raise-wt k {Δ = Δ} (⊢• {B = B} {T = T} M⊢ wfB wfT) =
  cong-⊢⦂
    refl
    refl
    refl
    (sym (renameᵗ-[]ᵗ (raiseVarFrom k) B T))
    (⊢•
      (renameᵗᵐ-raise-wt k M⊢)
      (subst
        (WfTy _ _)
        (sym (rename-raise-ext k B))
        (renameᵗ-preserves-WfTy wfB (raiseWfPlus (suc k) {Δ = Δ})))
      (renameᵗ-preserves-WfTy wfT (raiseWfPlus k {Δ = Δ})))
renameᵗᵐ-raise-wt k (⊢$ (κℕ n)) = ⊢$ (κℕ n)
renameᵗᵐ-raise-wt k (⊢⊕ L⊢ op M⊢) =
  ⊢⊕ (renameᵗᵐ-raise-wt k L⊢) op (renameᵗᵐ-raise-wt k M⊢)
renameᵗᵐ-raise-wt k (⊢up p⊢ M⊢) =
  ⊢up (wkImp-plains k p⊢) (renameᵗᵐ-raise-wt k M⊢)
renameᵗᵐ-raise-wt k (⊢down p⊢ M⊢) =
  ⊢down (wkImp-plains k p⊢) (renameᵗᵐ-raise-wt k M⊢)
renameᵗᵐ-raise-wt k {Σ = Σ} (⊢reveal {A = A} {B = B} c⊢ M⊢) =
  ⊢reveal
    (cong-⊢↑
      (substStoreᵗ-ren (raiseVarFrom k) Σ)
      refl
      (substᵗ-ren (raiseVarFrom k) A)
      (substᵗ-ren (raiseVarFrom k) B)
      (subst↑-wt {σ = λ X → ＇ raiseVarFrom k X}
        (renSubst-raise-wf k)
        c⊢))
    (renameᵗᵐ-raise-wt k M⊢)
renameᵗᵐ-raise-wt k {Σ = Σ} (⊢conceal {A = A} {B = B} c⊢ M⊢) =
  ⊢conceal
    (cong-⊢↓
      (substStoreᵗ-ren (raiseVarFrom k) Σ)
      refl
      (substᵗ-ren (raiseVarFrom k) A)
      (substᵗ-ren (raiseVarFrom k) B)
      (subst↓-wt {σ = λ X → ＇ raiseVarFrom k X}
        (renSubst-raise-wf k)
        c⊢))
    (renameᵗᵐ-raise-wt k M⊢)
renameᵗᵐ-raise-wt k (⊢blame ℓ) = ⊢blame ℓ

renameᵗᵐ-suc-wt :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{M : Term}{A : Ty} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  suc Δ ∣ Ψ ∣ ⟰ᵗ Σ ∣ ⤊ᵗ Γ ⊢ renameᵗᵐ suc M ⦂ renameᵗ suc A
renameᵗᵐ-suc-wt = renameᵗᵐ-raise-wt zero

------------------------------------------------------------------------
-- Term-variable renaming and substitution preserve typing
------------------------------------------------------------------------

renameˣᵐ-wt :
  ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx}{M : Term}{A : Ty} →
  (ρ : Renameˣ) →
  Renameˣ-wt Γ Γ′ ρ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Ψ ∣ Σ ∣ Γ′ ⊢ renameˣᵐ ρ M ⦂ A
renameˣᵐ-wt ρ hρ (⊢` h) = ⊢` (hρ h)
renameˣᵐ-wt ρ hρ (⊢ƛ wfA M⊢) =
  ⊢ƛ wfA (renameˣᵐ-wt (extʳ ρ) (extʳ-wt ρ hρ) M⊢)
renameˣᵐ-wt ρ hρ (⊢· L⊢ M⊢) =
  ⊢· (renameˣᵐ-wt ρ hρ L⊢) (renameˣᵐ-wt ρ hρ M⊢)
renameˣᵐ-wt ρ hρ (⊢Λ vM M⊢) =
  ⊢Λ (renameˣᵐ-value ρ vM) (renameˣᵐ-wt ρ (liftᵗʳ-wt ρ hρ) M⊢)
renameˣᵐ-wt ρ hρ (⊢• M⊢ wfB wfT) =
  ⊢• (renameˣᵐ-wt ρ hρ M⊢) wfB wfT
renameˣᵐ-wt ρ hρ (⊢$ κ) = ⊢$ κ
renameˣᵐ-wt ρ hρ (⊢⊕ L⊢ op M⊢) =
  ⊢⊕ (renameˣᵐ-wt ρ hρ L⊢) op (renameˣᵐ-wt ρ hρ M⊢)
renameˣᵐ-wt ρ hρ (⊢up p⊢ M⊢) =
  ⊢up p⊢ (renameˣᵐ-wt ρ hρ M⊢)
renameˣᵐ-wt ρ hρ (⊢down p⊢ M⊢) =
  ⊢down p⊢ (renameˣᵐ-wt ρ hρ M⊢)
renameˣᵐ-wt ρ hρ (⊢reveal c⊢ M⊢) =
  ⊢reveal c⊢ (renameˣᵐ-wt ρ hρ M⊢)
renameˣᵐ-wt ρ hρ (⊢conceal c⊢ M⊢) =
  ⊢conceal c⊢ (renameˣᵐ-wt ρ hρ M⊢)
renameˣᵐ-wt ρ hρ (⊢blame ℓ) = ⊢blame ℓ

Substˣ-wt :
  ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx} →
  (σ : Substˣ) →
  Set
Substˣ-wt {Δ} {Ψ} {Σ} {Γ} {Γ′} σ =
  ∀ {A : Ty}{x : Var} →
  Γ ∋ x ⦂ A →
  Δ ∣ Ψ ∣ Σ ∣ Γ′ ⊢ σ x ⦂ A

extˢˣ-wt :
  ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx}{A : Ty} (σ : Substˣ) →
  Substˣ-wt {Δ} {Ψ} {Σ} {Γ} {Γ′} σ →
  Substˣ-wt {Δ} {Ψ} {Σ} {A ∷ Γ} {A ∷ Γ′} (extˢˣ σ)
extˢˣ-wt σ hσ Z = ⊢` Z
extˢˣ-wt σ hσ (S h) = renameˣᵐ-wt suc wkʳ-wt (hσ h)

↑ᵗᵐ-wt :
  ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx} (σ : Substˣ) →
  Substˣ-wt {Δ} {Ψ} {Σ} {Γ} {Γ′} σ →
  Substˣ-wt {suc Δ} {Ψ} {⟰ᵗ Σ} {⤊ᵗ Γ} {⤊ᵗ Γ′} (↑ᵗᵐ σ)
↑ᵗᵐ-wt σ hσ {x = x} h with unmap∋-⤊ᵗ h
... | B , eq , h₀ =
  cong-⊢⦂
    refl
    refl
    refl
    (sym eq)
    (renameᵗᵐ-suc-wt (hσ {x = x} h₀))

substˣ-wt :
  ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx}{M : Term}{A : Ty} →
  (σ : Substˣ) →
  Substˣ-wt {Δ} {Ψ} {Σ} {Γ} {Γ′} σ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Ψ ∣ Σ ∣ Γ′ ⊢ substˣᵐ σ M ⦂ A
substˣ-wt σ hσ (⊢` h) = hσ h
substˣ-wt σ hσ (⊢ƛ wfA M⊢) =
  ⊢ƛ wfA (substˣ-wt (extˢˣ σ) (extˢˣ-wt σ hσ) M⊢)
substˣ-wt σ hσ (⊢· L⊢ M⊢) =
  ⊢· (substˣ-wt σ hσ L⊢) (substˣ-wt σ hσ M⊢)
substˣ-wt σ hσ (⊢Λ vM M⊢) =
  ⊢Λ
    (substˣᵐ-value (↑ᵗᵐ σ) vM)
    (substˣ-wt (↑ᵗᵐ σ) (↑ᵗᵐ-wt σ hσ) M⊢)
substˣ-wt σ hσ (⊢• M⊢ wfB wfT) =
  ⊢• (substˣ-wt σ hσ M⊢) wfB wfT
substˣ-wt σ hσ (⊢$ κ) = ⊢$ κ
substˣ-wt σ hσ (⊢⊕ L⊢ op M⊢) =
  ⊢⊕ (substˣ-wt σ hσ L⊢) op (substˣ-wt σ hσ M⊢)
substˣ-wt σ hσ (⊢up p⊢ M⊢) =
  ⊢up p⊢ (substˣ-wt σ hσ M⊢)
substˣ-wt σ hσ (⊢down p⊢ M⊢) =
  ⊢down p⊢ (substˣ-wt σ hσ M⊢)
substˣ-wt σ hσ (⊢reveal c⊢ M⊢) =
  ⊢reveal c⊢ (substˣ-wt σ hσ M⊢)
substˣ-wt σ hσ (⊢conceal c⊢ M⊢) =
  ⊢conceal c⊢ (substˣ-wt σ hσ M⊢)
substˣ-wt σ hσ (⊢blame ℓ) = ⊢blame ℓ

------------------------------------------------------------------------
-- Single-variable substitution
------------------------------------------------------------------------

singleEnv-wt :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{A : Ty} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ V ⦂ A →
  Substˣ-wt {Δ} {Ψ} {Σ} {A ∷ Γ} {Γ} (singleEnv V)
singleEnv-wt V⊢ Z = V⊢
singleEnv-wt V⊢ (S h) = ⊢` h

[]-wt :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{N V : Term}{A B : Ty} →
  Δ ∣ Ψ ∣ Σ ∣ (A ∷ Γ) ⊢ N ⦂ B →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ V ⦂ A →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ N [ V ] ⦂ B
[]-wt N⊢ V⊢ = substˣ-wt (singleEnv _) (singleEnv-wt V⊢) N⊢
