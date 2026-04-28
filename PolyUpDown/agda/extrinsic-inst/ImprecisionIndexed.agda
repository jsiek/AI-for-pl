module ImprecisionIndexed where

-- File Charter:
--   * Context-indexed imprecision for PolyUpDown.
--   * Keeps ν-bound type variables explicit in the recursive premise of
--   * ν-imprecision, instead of substituting them away.
--   * Provides structural mode changes, transitivity, and bridges to/from Cast.

open import Types
open import Cast
open import UpDown
  using
    ( CastPerm; cast-seal; cast-tag
    ; _∈cast_; _∈tag_
    ; here-cast-only; there-cast
    ; here-tag-only; there-tag
    ; wfTySome
    )
open import Store using (renameLookupᵗ)
open import TypeCheckDec using
  (close-openνSrc-id; closeνSrc; openνSrc-zero; raiseVarFrom)
open import TypeProperties using
  (open-renᵗ-suc; renameᵗ-⇑ˢ; renameᵗ-suc-comm;
   substᵗ-suc-renameᵗ-suc)

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _<_; _≤_; z<s; s<s)
open import Data.Nat.Properties
  using (<-≤-trans; n<1+n; n≤1+n; m≤m⊔n; m≤n⊔m; ≤-refl)
open import Data.Product using (_,_; _×_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; subst; sym; trans)
open import Imprecision
  using
    (pred-★-bound; left-rec-⇒-bound; right-rec-⇒-bound;
     ν-rec-bound; ∀ν-rec-bound)

------------------------------------------------------------------------
-- Context-indexed imprecision
------------------------------------------------------------------------

data VarMode : Set where
  plain ν-bound : VarMode

ICtx : Set
ICtx = List VarMode

infix 4 _∋_∶_
data _∋_∶_ : ICtx → TyVar → VarMode → Set where
  here : ∀ {Γ m} → (m ∷ Γ) ∋ zero ∶ m
  there : ∀ {Γ X m m′} → Γ ∋ X ∶ m → (m′ ∷ Γ) ∋ suc X ∶ m

interpSeal : ICtx → Seal → Seal
interpSeal [] α = α
interpSeal (plain ∷ Γ) α = interpSeal Γ α
interpSeal (ν-bound ∷ Γ) α = suc (interpSeal Γ α)

interpVar : ICtx → TyVar → Ty
interpVar [] X = ＇ X
interpVar (plain ∷ Γ) zero = ＇ zero
interpVar (plain ∷ Γ) (suc X) = ⇑ᵗ (interpVar Γ X)
interpVar (ν-bound ∷ Γ) zero = ｀ zero
interpVar (ν-bound ∷ Γ) (suc X) = ⇑ˢ (interpVar Γ X)

interp : ICtx → Ty → Ty
interp Γ (＇ X) = interpVar Γ X
interp Γ (｀ α) = ｀ (interpSeal Γ α)
interp Γ (‵ ι) = ‵ ι
interp Γ ★ = ★
interp Γ (A ⇒ B) = interp Γ A ⇒ interp Γ B
interp Γ (`∀ A) = `∀ (interp (plain ∷ Γ) A)

data Groundᵢ (Γ : ICtx) : Ty → Set where
  ground-ν : ∀ {X} → Γ ∋ X ∶ ν-bound → Groundᵢ Γ (＇ X)
  ground-seal : ∀ α → Groundᵢ Γ (｀ α)
  ground-base : ∀ ι → Groundᵢ Γ (‵ ι)
  ground-fun : Groundᵢ Γ (★ ⇒ ★)

infix 4 _⊢_⊑ᵢ_ _⊢_⊒ᵢ_

data _⊢_⊑ᵢ_ (Γ : ICtx) : Ty → Ty → Set where
  ⊑ᵢ-★★ : Γ ⊢ ★ ⊑ᵢ ★
  ⊑ᵢ-★ : (A G : Ty) → Groundᵢ Γ G → Γ ⊢ A ⊑ᵢ G → Γ ⊢ A ⊑ᵢ ★
  ⊑ᵢ-＇ : (X : TyVar) → Γ ⊢ ＇ X ⊑ᵢ ＇ X
  ⊑ᵢ-｀ : (α : Seal) → Γ ⊢ ｀ α ⊑ᵢ ｀ α
  ⊑ᵢ-‵ : (ι : Base) → Γ ⊢ ‵ ι ⊑ᵢ ‵ ι
  ⊑ᵢ-⇒ : (A A′ B B′ : Ty) →
    Γ ⊢ A ⊑ᵢ A′ →
    Γ ⊢ B ⊑ᵢ B′ →
    Γ ⊢ (A ⇒ B) ⊑ᵢ (A′ ⇒ B′)
  ⊑ᵢ-∀ : (A B : Ty) →
    (plain ∷ Γ) ⊢ A ⊑ᵢ B →
    Γ ⊢ (`∀ A) ⊑ᵢ (`∀ B)
  ⊑ᵢ-ν : (A B : Ty) →
    (ν-bound ∷ Γ) ⊢ A ⊑ᵢ ⇑ᵗ B →
    Γ ⊢ (`∀ A) ⊑ᵢ B

_⊢_⊒ᵢ_ : ICtx → Ty → Ty → Set
Γ ⊢ B ⊒ᵢ A = Γ ⊢ A ⊑ᵢ B

⊑ᵢ-refl : ∀ {Γ A} → Γ ⊢ A ⊑ᵢ A
⊑ᵢ-refl {A = ＇ X} = ⊑ᵢ-＇ X
⊑ᵢ-refl {A = ｀ α} = ⊑ᵢ-｀ α
⊑ᵢ-refl {A = ‵ ι} = ⊑ᵢ-‵ ι
⊑ᵢ-refl {A = ★} = ⊑ᵢ-★★
⊑ᵢ-refl {A = A ⇒ B} = ⊑ᵢ-⇒ A A B B ⊑ᵢ-refl ⊑ᵢ-refl
⊑ᵢ-refl {A = `∀ A} = ⊑ᵢ-∀ A A ⊑ᵢ-refl

postulate
  ν-close-inst⊑ᵢ :
    ∀ {Γ Ψ A B T} →
    WfTy 0 Ψ T →
    (ν-bound ∷ Γ) ⊢ A ⊑ᵢ ⇑ᵗ B →
    Γ ⊢ A [ T ]ᵗ ⊑ᵢ B

record νClosedInstᵢ {Γ A B T}
    (pν : (ν-bound ∷ Γ) ⊢ A ⊑ᵢ ⇑ᵗ B)
    (pT : Γ ⊢ A [ T ]ᵗ ⊑ᵢ B) : Set where
  constructor ν-closed-instᵢ
  field
    ν-inst-Ψᵢ : SealCtx
    ν-inst-wfTᵢ : WfTy 0 ν-inst-Ψᵢ T
    ν-inst-eqᵢ : pT ≡ ν-close-inst⊑ᵢ ν-inst-wfTᵢ pν
open νClosedInstᵢ public

ν-close-inst-evidenceᵢ :
  ∀ {Γ Ψ A B T}
    (hT : WfTy 0 Ψ T)
    (pν : (ν-bound ∷ Γ) ⊢ A ⊑ᵢ ⇑ᵗ B) →
  νClosedInstᵢ pν (ν-close-inst⊑ᵢ hT pν)
ν-close-inst-evidenceᵢ hT pν = ν-closed-instᵢ _ hT refl

νs : ℕ → ICtx → ICtx
νs zero Γ = Γ
νs (suc n) Γ = ν-bound ∷ νs n Γ

νs-lookup :
  ∀ {Γ Δ X} →
  X < Δ →
  νs Δ Γ ∋ X ∶ ν-bound
νs-lookup {Δ = suc Δ} {X = zero} z<s = here
νs-lookup {Δ = suc Δ} {X = suc X} (s<s X<) = there (νs-lookup X<)

wf-νs-⊑★ :
  ∀ {Γ Δ Ψ A} →
  WfTy Δ Ψ A →
  νs Δ Γ ⊢ A ⊑ᵢ ★
wf-νs-⊑★ {A = ＇ X} (wfVar X<) =
  ⊑ᵢ-★ (＇ X) (＇ X) (ground-ν (νs-lookup X<)) (⊑ᵢ-＇ X)
wf-νs-⊑★ {A = ｀ α} (wfSeal α<Ψ) =
  ⊑ᵢ-★ (｀ α) (｀ α) (ground-seal α) (⊑ᵢ-｀ α)
wf-νs-⊑★ {A = ‵ ι} wfBase =
  ⊑ᵢ-★ (‵ ι) (‵ ι) (ground-base ι) (⊑ᵢ-‵ ι)
wf-νs-⊑★ wf★ = ⊑ᵢ-★★
wf-νs-⊑★ {A = A ⇒ B} (wf⇒ wfA wfB) =
  ⊑ᵢ-★ (A ⇒ B) (★ ⇒ ★) ground-fun
    (⊑ᵢ-⇒ A ★ B ★ (wf-νs-⊑★ wfA) (wf-νs-⊑★ wfB))
wf-νs-⊑★ {A = `∀ A} (wf∀ wfA) =
  ⊑ᵢ-ν A ★ (wf-νs-⊑★ wfA)

closed-⊑★ :
  ∀ {Γ Ψ T} →
  WfTy 0 Ψ T →
  Γ ⊢ T ⊑ᵢ ★
closed-⊑★ hT = wf-νs-⊑★ hT

⊑ᵢ-cast :
  ∀ {Γ A A′ B B′} →
  A ≡ A′ →
  B ≡ B′ →
  Γ ⊢ A ⊑ᵢ B →
  Γ ⊢ A′ ⊑ᵢ B′
⊑ᵢ-cast refl refl p = p

size⊑ᵢ : ∀ {Γ A B} → Γ ⊢ A ⊑ᵢ B → ℕ
size⊑ᵢ ⊑ᵢ-★★ = zero
size⊑ᵢ (⊑ᵢ-★ A G g p) = suc (size⊑ᵢ p)
size⊑ᵢ (⊑ᵢ-＇ X) = zero
size⊑ᵢ (⊑ᵢ-｀ α) = zero
size⊑ᵢ (⊑ᵢ-‵ ι) = zero
size⊑ᵢ (⊑ᵢ-⇒ A A′ B B′ p q) = suc (size⊑ᵢ p + size⊑ᵢ q)
size⊑ᵢ (⊑ᵢ-∀ A B p) = suc (size⊑ᵢ p)
size⊑ᵢ (⊑ᵢ-ν A B p) = suc (size⊑ᵢ p)

size-⊑ᵢ-cast :
  ∀ {Γ A A′ B B′} →
  (eqA : A ≡ A′) →
  (eqB : B ≡ B′) →
  (p : Γ ⊢ A ⊑ᵢ B) →
  size⊑ᵢ (⊑ᵢ-cast eqA eqB p) ≡ size⊑ᵢ p
size-⊑ᵢ-cast refl refl p = refl

------------------------------------------------------------------------
-- Interpreting ν-bound variables as fresh seals
------------------------------------------------------------------------

ν-lookup-seal :
  ∀ {Γ X} →
  Γ ∋ X ∶ ν-bound →
  ∃[ α ] interpVar Γ X ≡ ｀ α
ν-lookup-seal here = zero , refl
ν-lookup-seal (there {m′ = plain} x∈) with ν-lookup-seal x∈
... | α , eq = α , cong ⇑ᵗ eq
ν-lookup-seal (there {m′ = ν-bound} x∈) with ν-lookup-seal x∈
... | α , eq = suc α , cong ⇑ˢ eq

groundᵢ-interp :
  ∀ {Γ G} →
  Groundᵢ Γ G →
  Ground (interp Γ G)
groundᵢ-interp (ground-ν x∈) with ν-lookup-seal x∈
... | α , eq = subst Ground (sym eq) (｀ α)
groundᵢ-interp (ground-seal α) = ｀ _
groundᵢ-interp (ground-base ι) = ‵ ι
groundᵢ-interp ground-fun = ★⇒★

maxGroundᵢ : ∀ {Γ G} → Groundᵢ Γ G → ℕ
maxGroundᵢ (ground-ν x∈) with ν-lookup-seal x∈
... | α , eq = α
maxGroundᵢ {Γ = Γ} (ground-seal α) = interpSeal Γ α
maxGroundᵢ (ground-base ι) = zero
maxGroundᵢ ground-fun = zero

plains : ℕ → ICtx → ICtx
plains zero Γ = Γ
plains (suc n) Γ = plain ∷ plains n Γ

openνEnv : ℕ → Substᵗ
openνEnv zero = singleTyEnv α₀
openνEnv (suc n) = extsᵗ (openνEnv n)

renameᵗ-cong :
  ∀ {ρ ϱ} →
  (∀ X → ρ X ≡ ϱ X) →
  ∀ A → renameᵗ ρ A ≡ renameᵗ ϱ A
renameᵗ-cong h (＇ X) = cong ＇_ (h X)
renameᵗ-cong h (｀ α) = refl
renameᵗ-cong h (‵ ι) = refl
renameᵗ-cong h ★ = refl
renameᵗ-cong h (A ⇒ B) = cong₂ _⇒_ (renameᵗ-cong h A) (renameᵗ-cong h B)
renameᵗ-cong h (`∀ A) = cong `∀ (renameᵗ-cong h-ext A)
  where
    h-ext : ∀ X → extᵗ _ X ≡ extᵗ _ X
    h-ext zero = refl
    h-ext (suc X) = cong suc (h X)

raise-ext : ∀ n X → extᵗ (raiseVarFrom n) X ≡ raiseVarFrom (suc n) X
raise-ext n zero = refl
raise-ext n (suc X) = refl

ν-at : ∀ n → plains n (ν-bound ∷ []) ∋ n ∶ ν-bound
ν-at zero = here
ν-at (suc n) = there (ν-at n)

insertνAt : ℕ → ICtx → ICtx
insertνAt zero Γ = ν-bound ∷ Γ
insertνAt (suc k) [] = plain ∷ insertνAt k []
insertνAt (suc k) (m ∷ Γ) = m ∷ insertνAt k Γ

insertPlainAt : ℕ → ICtx → ICtx
insertPlainAt zero Γ = plain ∷ Γ
insertPlainAt (suc k) [] = plain ∷ insertPlainAt k []
insertPlainAt (suc k) (m ∷ Γ) = m ∷ insertPlainAt k Γ

insert-lookup :
  ∀ {Γ X m} k →
  Γ ∋ X ∶ m →
  insertνAt k Γ ∋ raiseVarFrom k X ∶ m
insert-lookup zero x∈ = there x∈
insert-lookup (suc k) here = here
insert-lookup (suc k) (there x∈) = there (insert-lookup k x∈)

insertPlain-lookup :
  ∀ {Γ X m} k →
  Γ ∋ X ∶ m →
  insertPlainAt k Γ ∋ raiseVarFrom k X ∶ m
insertPlain-lookup zero x∈ = there x∈
insertPlain-lookup (suc k) here = here
insertPlain-lookup (suc k) (there x∈) =
  there (insertPlain-lookup k x∈)

inserted-ν :
  ∀ k Γ →
  insertνAt k Γ ∋ k ∶ ν-bound
inserted-ν zero Γ = here
inserted-ν (suc k) [] = there (inserted-ν k [])
inserted-ν (suc k) (m ∷ Γ) = there (inserted-ν k Γ)

rename-raise-⇑ᵗ :
  ∀ k A →
  renameᵗ (raiseVarFrom (suc k)) (⇑ᵗ A) ≡
  ⇑ᵗ (renameᵗ (raiseVarFrom k) A)
rename-raise-⇑ᵗ k A =
  trans
    (renameᵗ-cong (λ X → sym (raise-ext k X)) (⇑ᵗ A))
    (sym (renameᵗ-suc-comm (raiseVarFrom k) A))

ν-weakenAt-ground :
  ∀ k {Γ G} →
  Groundᵢ Γ G →
  Groundᵢ (insertνAt k Γ) (renameᵗ (raiseVarFrom k) G)
ν-weakenAt-ground k (ground-ν x∈) = ground-ν (insert-lookup k x∈)
ν-weakenAt-ground k (ground-seal α) = ground-seal α
ν-weakenAt-ground k (ground-base ι) = ground-base ι
ν-weakenAt-ground k ground-fun = ground-fun

plain-weakenAt-ground :
  ∀ k {Γ G} →
  Groundᵢ Γ G →
  Groundᵢ (insertPlainAt k Γ) (renameᵗ (raiseVarFrom k) G)
plain-weakenAt-ground k (ground-ν x∈) =
  ground-ν (insertPlain-lookup k x∈)
plain-weakenAt-ground k (ground-seal α) = ground-seal α
plain-weakenAt-ground k (ground-base ι) = ground-base ι
plain-weakenAt-ground k ground-fun = ground-fun

plain-weakenAt⊑ᵢ :
  ∀ k {Γ A B} →
  Γ ⊢ A ⊑ᵢ B →
  insertPlainAt k Γ ⊢
    renameᵗ (raiseVarFrom k) A ⊑ᵢ renameᵗ (raiseVarFrom k) B
plain-weakenAt⊑ᵢ k ⊑ᵢ-★★ = ⊑ᵢ-★★
plain-weakenAt⊑ᵢ k (⊑ᵢ-★ A G g p) =
  ⊑ᵢ-★
    (renameᵗ (raiseVarFrom k) A)
    (renameᵗ (raiseVarFrom k) G)
    (plain-weakenAt-ground k g)
    (plain-weakenAt⊑ᵢ k p)
plain-weakenAt⊑ᵢ k (⊑ᵢ-＇ X) = ⊑ᵢ-＇ (raiseVarFrom k X)
plain-weakenAt⊑ᵢ k (⊑ᵢ-｀ α) = ⊑ᵢ-｀ α
plain-weakenAt⊑ᵢ k (⊑ᵢ-‵ ι) = ⊑ᵢ-‵ ι
plain-weakenAt⊑ᵢ k (⊑ᵢ-⇒ A A′ B B′ p q) =
  ⊑ᵢ-⇒
    (renameᵗ (raiseVarFrom k) A)
    (renameᵗ (raiseVarFrom k) A′)
    (renameᵗ (raiseVarFrom k) B)
    (renameᵗ (raiseVarFrom k) B′)
    (plain-weakenAt⊑ᵢ k p)
    (plain-weakenAt⊑ᵢ k q)
plain-weakenAt⊑ᵢ k (⊑ᵢ-∀ A B p) =
  ⊑ᵢ-∀
    (renameᵗ (extᵗ (raiseVarFrom k)) A)
    (renameᵗ (extᵗ (raiseVarFrom k)) B)
    (⊑ᵢ-cast
      (renameᵗ-cong (λ X → sym (raise-ext k X)) A)
      (renameᵗ-cong (λ X → sym (raise-ext k X)) B)
      (plain-weakenAt⊑ᵢ (suc k) p))
plain-weakenAt⊑ᵢ k (⊑ᵢ-ν A B p) =
  ⊑ᵢ-ν
    (renameᵗ (extᵗ (raiseVarFrom k)) A)
    (renameᵗ (raiseVarFrom k) B)
    (⊑ᵢ-cast
      (renameᵗ-cong (λ X → sym (raise-ext k X)) A)
      (rename-raise-⇑ᵗ k B)
      (plain-weakenAt⊑ᵢ (suc k) p))

plain-weaken⊑ᵢ :
  ∀ {Γ A B} →
  Γ ⊢ A ⊑ᵢ B →
  (plain ∷ Γ) ⊢ ⇑ᵗ A ⊑ᵢ ⇑ᵗ B
plain-weaken⊑ᵢ = plain-weakenAt⊑ᵢ zero

substVarFrom : TyVar → Ty → Substᵗ
substVarFrom zero T = singleTyEnv T
substVarFrom (suc k) T = extsᵗ (substVarFrom k T)

substVarFrom-⇑ᵗ :
  ∀ k T A →
  substᵗ (substVarFrom (suc k) T) (⇑ᵗ A) ≡
  ⇑ᵗ (substᵗ (substVarFrom k T) A)
substVarFrom-⇑ᵗ k T A =
  substᵗ-suc-renameᵗ-suc (substVarFrom k T) A

substPlain-lookup :
  ∀ k {Γ X T} →
  insertPlainAt k Γ ∋ X ∶ ν-bound →
  ∃[ Y ] (Γ ∋ Y ∶ ν-bound × substVarFrom k T X ≡ ＇ Y)
substPlain-lookup zero {Γ = Γ} (there x∈) = _ , x∈ , refl
substPlain-lookup (suc k) {Γ = []} {T = T} (there x∈)
  with substPlain-lookup k {Γ = []} {T = T} x∈
... | _ , () , _
substPlain-lookup (suc k) {Γ = ν-bound ∷ Γ} here = zero , here , refl
substPlain-lookup (suc k) {Γ = m ∷ Γ} (there x∈)
  with substPlain-lookup k x∈
... | Y , y∈ , eq = suc Y , there y∈ , cong ⇑ᵗ eq

substPlainAt-ground :
  ∀ k T {Γ G} →
  Groundᵢ (insertPlainAt k Γ) G →
  Groundᵢ Γ (substᵗ (substVarFrom k T) G)
substPlainAt-ground k T (ground-ν x∈) with substPlain-lookup k x∈
... | Y , y∈ , eq = subst (Groundᵢ _) (sym eq) (ground-ν y∈)
substPlainAt-ground k T (ground-seal α) = ground-seal α
substPlainAt-ground k T (ground-base ι) = ground-base ι
substPlainAt-ground k T ground-fun = ground-fun

substPlainAt⊑ᵢ :
  ∀ k T {Γ A B} →
  insertPlainAt k Γ ⊢ A ⊑ᵢ B →
  Γ ⊢ substᵗ (substVarFrom k T) A ⊑ᵢ substᵗ (substVarFrom k T) B
substPlainAt⊑ᵢ k T ⊑ᵢ-★★ = ⊑ᵢ-★★
substPlainAt⊑ᵢ k T (⊑ᵢ-★ A G g p) =
  ⊑ᵢ-★
    (substᵗ (substVarFrom k T) A)
    (substᵗ (substVarFrom k T) G)
    (substPlainAt-ground k T g)
    (substPlainAt⊑ᵢ k T p)
substPlainAt⊑ᵢ k T (⊑ᵢ-＇ X) = ⊑ᵢ-refl
substPlainAt⊑ᵢ k T (⊑ᵢ-｀ α) = ⊑ᵢ-｀ α
substPlainAt⊑ᵢ k T (⊑ᵢ-‵ ι) = ⊑ᵢ-‵ ι
substPlainAt⊑ᵢ k T (⊑ᵢ-⇒ A A′ B B′ p q) =
  ⊑ᵢ-⇒
    (substᵗ (substVarFrom k T) A)
    (substᵗ (substVarFrom k T) A′)
    (substᵗ (substVarFrom k T) B)
    (substᵗ (substVarFrom k T) B′)
    (substPlainAt⊑ᵢ k T p)
    (substPlainAt⊑ᵢ k T q)
substPlainAt⊑ᵢ k T (⊑ᵢ-∀ A B p) =
  ⊑ᵢ-∀
    (substᵗ (substVarFrom (suc k) T) A)
    (substᵗ (substVarFrom (suc k) T) B)
    (substPlainAt⊑ᵢ (suc k) T p)
substPlainAt⊑ᵢ k T (⊑ᵢ-ν A B p) =
  ⊑ᵢ-ν
    (substᵗ (substVarFrom (suc k) T) A)
    (substᵗ (substVarFrom k T) B)
    (⊑ᵢ-cast
      refl
      (substVarFrom-⇑ᵗ k T B)
      (substPlainAt⊑ᵢ (suc k) T p))

substPlain⊑ᵢ :
  ∀ T {Γ A B} →
  (plain ∷ Γ) ⊢ A ⊑ᵢ B →
  Γ ⊢ A [ T ]ᵗ ⊑ᵢ B [ T ]ᵗ
substPlain⊑ᵢ = substPlainAt⊑ᵢ zero

ν-weakenAt⊑ᵢ :
  ∀ k {Γ A B} →
  Γ ⊢ A ⊑ᵢ B →
  insertνAt k Γ ⊢
    renameᵗ (raiseVarFrom k) A ⊑ᵢ renameᵗ (raiseVarFrom k) B
ν-weakenAt⊑ᵢ k ⊑ᵢ-★★ = ⊑ᵢ-★★
ν-weakenAt⊑ᵢ k (⊑ᵢ-★ A G g p) =
  ⊑ᵢ-★
    (renameᵗ (raiseVarFrom k) A)
    (renameᵗ (raiseVarFrom k) G)
    (ν-weakenAt-ground k g)
    (ν-weakenAt⊑ᵢ k p)
ν-weakenAt⊑ᵢ k (⊑ᵢ-＇ X) = ⊑ᵢ-＇ (raiseVarFrom k X)
ν-weakenAt⊑ᵢ k (⊑ᵢ-｀ α) = ⊑ᵢ-｀ α
ν-weakenAt⊑ᵢ k (⊑ᵢ-‵ ι) = ⊑ᵢ-‵ ι
ν-weakenAt⊑ᵢ k (⊑ᵢ-⇒ A A′ B B′ p q) =
  ⊑ᵢ-⇒
    (renameᵗ (raiseVarFrom k) A)
    (renameᵗ (raiseVarFrom k) A′)
    (renameᵗ (raiseVarFrom k) B)
    (renameᵗ (raiseVarFrom k) B′)
    (ν-weakenAt⊑ᵢ k p)
    (ν-weakenAt⊑ᵢ k q)
ν-weakenAt⊑ᵢ k (⊑ᵢ-∀ A B p) =
  ⊑ᵢ-∀
    (renameᵗ (extᵗ (raiseVarFrom k)) A)
    (renameᵗ (extᵗ (raiseVarFrom k)) B)
    (⊑ᵢ-cast
      (renameᵗ-cong (λ X → sym (raise-ext k X)) A)
      (renameᵗ-cong (λ X → sym (raise-ext k X)) B)
      (ν-weakenAt⊑ᵢ (suc k) p))
ν-weakenAt⊑ᵢ k (⊑ᵢ-ν A B p) =
  ⊑ᵢ-ν
    (renameᵗ (extᵗ (raiseVarFrom k)) A)
    (renameᵗ (raiseVarFrom k) B)
    (⊑ᵢ-cast
      (renameᵗ-cong (λ X → sym (raise-ext k X)) A)
      (rename-raise-⇑ᵗ k B)
      (ν-weakenAt⊑ᵢ (suc k) p))

size-ν-weakenAt⊑ᵢ :
  ∀ k {Γ A B} →
  (p : Γ ⊢ A ⊑ᵢ B) →
  size⊑ᵢ (ν-weakenAt⊑ᵢ k p) ≡ size⊑ᵢ p
size-ν-weakenAt⊑ᵢ k ⊑ᵢ-★★ = refl
size-ν-weakenAt⊑ᵢ k (⊑ᵢ-★ A G g p) =
  cong suc (size-ν-weakenAt⊑ᵢ k p)
size-ν-weakenAt⊑ᵢ k (⊑ᵢ-＇ X) = refl
size-ν-weakenAt⊑ᵢ k (⊑ᵢ-｀ α) = refl
size-ν-weakenAt⊑ᵢ k (⊑ᵢ-‵ ι) = refl
size-ν-weakenAt⊑ᵢ k (⊑ᵢ-⇒ A A′ B B′ p q) =
  cong suc
    (cong₂ _+_ (size-ν-weakenAt⊑ᵢ k p) (size-ν-weakenAt⊑ᵢ k q))
size-ν-weakenAt⊑ᵢ k (⊑ᵢ-∀ A B p) =
  trans
    (cong suc
      (size-⊑ᵢ-cast
        (renameᵗ-cong (λ X → sym (raise-ext k X)) A)
        (renameᵗ-cong (λ X → sym (raise-ext k X)) B)
        (ν-weakenAt⊑ᵢ (suc k) p)))
    (cong suc (size-ν-weakenAt⊑ᵢ (suc k) p))
size-ν-weakenAt⊑ᵢ k (⊑ᵢ-ν A B p) =
  trans
    (cong suc
      (size-⊑ᵢ-cast
        (renameᵗ-cong (λ X → sym (raise-ext k X)) A)
        (rename-raise-⇑ᵗ k B)
        (ν-weakenAt⊑ᵢ (suc k) p)))
    (cong suc (size-ν-weakenAt⊑ᵢ (suc k) p))

ν-weaken⊑ᵢ :
  ∀ {Γ A B} →
  Γ ⊢ A ⊑ᵢ B →
  (ν-bound ∷ Γ) ⊢ ⇑ᵗ A ⊑ᵢ ⇑ᵗ B
ν-weaken⊑ᵢ = ν-weakenAt⊑ᵢ zero

size-ν-weaken⊑ᵢ :
  ∀ {Γ A B} →
  (p : Γ ⊢ A ⊑ᵢ B) →
  size⊑ᵢ (ν-weaken⊑ᵢ p) ≡ size⊑ᵢ p
size-ν-weaken⊑ᵢ = size-ν-weakenAt⊑ᵢ zero

replacePlainAt : ℕ → ICtx → ICtx
replacePlainAt zero [] = []
replacePlainAt zero (plain ∷ Γ) = ν-bound ∷ Γ
replacePlainAt zero (ν-bound ∷ Γ) = ν-bound ∷ Γ
replacePlainAt (suc k) [] = []
replacePlainAt (suc k) (m ∷ Γ) = m ∷ replacePlainAt k Γ

replacePlainAt-lookup :
  ∀ k {Γ X} →
  Γ ∋ X ∶ ν-bound →
  replacePlainAt k Γ ∋ X ∶ ν-bound
replacePlainAt-lookup zero {Γ = plain ∷ Γ} (there x∈) = there x∈
replacePlainAt-lookup zero {Γ = ν-bound ∷ Γ} here = here
replacePlainAt-lookup zero {Γ = ν-bound ∷ Γ} (there x∈) = there x∈
replacePlainAt-lookup (suc k) {Γ = m ∷ Γ} here = here
replacePlainAt-lookup (suc k) {Γ = m ∷ Γ} (there x∈) =
  there (replacePlainAt-lookup k x∈)

replacePlainAt-ground :
  ∀ k {Γ G} →
  Groundᵢ Γ G →
  Groundᵢ (replacePlainAt k Γ) G
replacePlainAt-ground k (ground-ν x∈) =
  ground-ν (replacePlainAt-lookup k x∈)
replacePlainAt-ground k (ground-seal α) = ground-seal α
replacePlainAt-ground k (ground-base ι) = ground-base ι
replacePlainAt-ground k ground-fun = ground-fun

replacePlainAt⊑ᵢ :
  ∀ k {Γ A B} →
  Γ ⊢ A ⊑ᵢ B →
  replacePlainAt k Γ ⊢ A ⊑ᵢ B
replacePlainAt⊑ᵢ k ⊑ᵢ-★★ = ⊑ᵢ-★★
replacePlainAt⊑ᵢ k (⊑ᵢ-★ A G g p) =
  ⊑ᵢ-★ A G (replacePlainAt-ground k g) (replacePlainAt⊑ᵢ k p)
replacePlainAt⊑ᵢ k (⊑ᵢ-＇ X) = ⊑ᵢ-＇ X
replacePlainAt⊑ᵢ k (⊑ᵢ-｀ α) = ⊑ᵢ-｀ α
replacePlainAt⊑ᵢ k (⊑ᵢ-‵ ι) = ⊑ᵢ-‵ ι
replacePlainAt⊑ᵢ k (⊑ᵢ-⇒ A A′ B B′ p q) =
  ⊑ᵢ-⇒ A A′ B B′ (replacePlainAt⊑ᵢ k p) (replacePlainAt⊑ᵢ k q)
replacePlainAt⊑ᵢ k (⊑ᵢ-∀ A B p) =
  ⊑ᵢ-∀ A B (replacePlainAt⊑ᵢ (suc k) p)
replacePlainAt⊑ᵢ k (⊑ᵢ-ν A B p) =
  ⊑ᵢ-ν A B (replacePlainAt⊑ᵢ (suc k) p)

size-replacePlainAt⊑ᵢ :
  ∀ k {Γ A B} →
  (p : Γ ⊢ A ⊑ᵢ B) →
  size⊑ᵢ (replacePlainAt⊑ᵢ k p) ≡ size⊑ᵢ p
size-replacePlainAt⊑ᵢ k ⊑ᵢ-★★ = refl
size-replacePlainAt⊑ᵢ k (⊑ᵢ-★ A G g p) =
  cong suc (size-replacePlainAt⊑ᵢ k p)
size-replacePlainAt⊑ᵢ k (⊑ᵢ-＇ X) = refl
size-replacePlainAt⊑ᵢ k (⊑ᵢ-｀ α) = refl
size-replacePlainAt⊑ᵢ k (⊑ᵢ-‵ ι) = refl
size-replacePlainAt⊑ᵢ k (⊑ᵢ-⇒ A A′ B B′ p q) =
  cong suc
    (cong₂ _+_
      (size-replacePlainAt⊑ᵢ k p)
      (size-replacePlainAt⊑ᵢ k q))
size-replacePlainAt⊑ᵢ k (⊑ᵢ-∀ A B p) =
  cong suc (size-replacePlainAt⊑ᵢ (suc k) p)
size-replacePlainAt⊑ᵢ k (⊑ᵢ-ν A B p) =
  cong suc (size-replacePlainAt⊑ᵢ (suc k) p)

plain-to-ν⊑ᵢ :
  ∀ {Γ A B} →
  (plain ∷ Γ) ⊢ A ⊑ᵢ B →
  (ν-bound ∷ Γ) ⊢ A ⊑ᵢ B
plain-to-ν⊑ᵢ = replacePlainAt⊑ᵢ zero

size-plain-to-ν⊑ᵢ :
  ∀ {Γ A B} →
  (p : (plain ∷ Γ) ⊢ A ⊑ᵢ B) →
  size⊑ᵢ (plain-to-ν⊑ᵢ p) ≡ size⊑ᵢ p
size-plain-to-ν⊑ᵢ = size-replacePlainAt⊑ᵢ zero

closeν-ground :
  ∀ k {Γ G} →
  Groundᵢ Γ G →
  Groundᵢ (insertνAt k Γ) (closeνSrc k G)
closeν-ground k (ground-ν x∈) = ground-ν (insert-lookup k x∈)
closeν-ground k (ground-seal zero) = ground-ν (inserted-ν k _)
closeν-ground k (ground-seal (suc α)) = ground-seal α
closeν-ground k (ground-base ι) = ground-base ι
closeν-ground k ground-fun = ground-fun

raiseVarFrom-+ :
  ∀ d k →
  raiseVarFrom d (d + k) ≡ d + suc k
raiseVarFrom-+ zero k = refl
raiseVarFrom-+ (suc d) k = cong suc (raiseVarFrom-+ d k)

raiseVarFrom-close-comm :
  ∀ d k X →
  raiseVarFrom (d + suc k) (raiseVarFrom d X) ≡
  raiseVarFrom d (raiseVarFrom (d + k) X)
raiseVarFrom-close-comm zero k X = refl
raiseVarFrom-close-comm (suc d) k zero = refl
raiseVarFrom-close-comm (suc d) k (suc X) =
  cong suc (raiseVarFrom-close-comm d k X)

closeνSrc-raiseAt :
  ∀ d k A →
  closeνSrc (d + suc k) (renameᵗ (raiseVarFrom d) A) ≡
  renameᵗ (raiseVarFrom d) (closeνSrc (d + k) A)
closeνSrc-raiseAt d k (＇ X) =
  cong ＇_ (raiseVarFrom-close-comm d k X)
closeνSrc-raiseAt d k (｀ zero) = cong ＇_ (sym (raiseVarFrom-+ d k))
closeνSrc-raiseAt d k (｀ (suc α)) = refl
closeνSrc-raiseAt d k (‵ ι) = refl
closeνSrc-raiseAt d k ★ = refl
closeνSrc-raiseAt d k (A ⇒ B) =
  cong₂ _⇒_ (closeνSrc-raiseAt d k A) (closeνSrc-raiseAt d k B)
closeνSrc-raiseAt d k (`∀ A) =
  cong `∀
    (trans
      (cong
        (closeνSrc (suc (d + suc k)))
        (renameᵗ-cong (raise-ext d) A))
      (trans
        (closeνSrc-raiseAt (suc d) k A)
        (renameᵗ-cong
          (λ X → sym (raise-ext d X))
          (closeνSrc (suc (d + k)) A))))

closeνSrc-⇑ᵗ :
  ∀ k A →
  closeνSrc (suc k) (⇑ᵗ A) ≡ ⇑ᵗ (closeνSrc k A)
closeνSrc-⇑ᵗ k A = closeνSrc-raiseAt zero k A

closeνSrc-⇑ˢ :
  ∀ k A →
  closeνSrc k (⇑ˢ A) ≡ renameᵗ (raiseVarFrom k) A
closeνSrc-⇑ˢ k (＇ X) = refl
closeνSrc-⇑ˢ k (｀ α) = refl
closeνSrc-⇑ˢ k (‵ ι) = refl
closeνSrc-⇑ˢ k ★ = refl
closeνSrc-⇑ˢ k (A ⇒ B) =
  cong₂ _⇒_ (closeνSrc-⇑ˢ k A) (closeνSrc-⇑ˢ k B)
closeνSrc-⇑ˢ k (`∀ A) =
  cong `∀
    (trans
      (closeνSrc-⇑ˢ (suc k) A)
      (renameᵗ-cong (λ X → sym (raise-ext k X)) A))

close-openν-zero :
  ∀ A →
  closeνSrc zero ((⇑ˢ A) [ α₀ ]ᵗ) ≡ A
close-openν-zero A =
  trans
    (cong (closeνSrc zero) (sym (openνSrc-zero A)))
    (close-openνSrc-id zero A)

ground-closeν :
  ∀ n {G} →
  Groundᵢ [] G →
  Groundᵢ (plains n (ν-bound ∷ [])) (closeνSrc n G)
ground-closeν n (ground-seal α) with α
... | zero = ground-ν (ν-at n)
... | suc β = ground-seal β
ground-closeν n (ground-base ι) = ground-base ι
ground-closeν n ground-fun = ground-fun

closeν-⊑ᵢ :
  ∀ k {Γ A B} →
  Γ ⊢ A ⊑ᵢ B →
  insertνAt k Γ ⊢ closeνSrc k A ⊑ᵢ closeνSrc k B
closeν-⊑ᵢ k ⊑ᵢ-★★ = ⊑ᵢ-★★
closeν-⊑ᵢ k (⊑ᵢ-★ A G g p) =
  ⊑ᵢ-★
    (closeνSrc k A)
    (closeνSrc k G)
    (closeν-ground k g)
    (closeν-⊑ᵢ k p)
closeν-⊑ᵢ k (⊑ᵢ-＇ X) = ⊑ᵢ-＇ (raiseVarFrom k X)
closeν-⊑ᵢ k (⊑ᵢ-｀ zero) = ⊑ᵢ-＇ k
closeν-⊑ᵢ k (⊑ᵢ-｀ (suc α)) = ⊑ᵢ-｀ α
closeν-⊑ᵢ k (⊑ᵢ-‵ ι) = ⊑ᵢ-‵ ι
closeν-⊑ᵢ k (⊑ᵢ-⇒ A A′ B B′ p q) =
  ⊑ᵢ-⇒
    (closeνSrc k A)
    (closeνSrc k A′)
    (closeνSrc k B)
    (closeνSrc k B′)
    (closeν-⊑ᵢ k p)
    (closeν-⊑ᵢ k q)
closeν-⊑ᵢ k (⊑ᵢ-∀ A B p) =
  ⊑ᵢ-∀
    (closeνSrc (suc k) A)
    (closeνSrc (suc k) B)
    (closeν-⊑ᵢ (suc k) p)
closeν-⊑ᵢ k (⊑ᵢ-ν A B p) =
  ⊑ᵢ-ν
    (closeνSrc (suc k) A)
    (closeνSrc k B)
    (⊑ᵢ-cast
      refl
      (closeνSrc-⇑ᵗ k B)
      (closeν-⊑ᵢ (suc k) p))

⊑ᵢ-trans-fuel :
  ∀ {n Γ A B C} →
  (p : Γ ⊢ A ⊑ᵢ B) →
  (q : Γ ⊢ B ⊑ᵢ C) →
  size⊑ᵢ p + size⊑ᵢ q ≤ n →
  Γ ⊢ A ⊑ᵢ C
⊑ᵢ-trans-fuel {n = zero} p ⊑ᵢ-★★ h = p
⊑ᵢ-trans-fuel {n = zero} ⊑ᵢ-★★ (⊑ᵢ-★ A G g q) ()
⊑ᵢ-trans-fuel {n = zero} (⊑ᵢ-★ A G g p) (⊑ᵢ-★ A′ G′ g′ q) ()
⊑ᵢ-trans-fuel {n = zero} (⊑ᵢ-＇ X) (⊑ᵢ-★ A G g q) ()
⊑ᵢ-trans-fuel {n = zero} (⊑ᵢ-｀ α) (⊑ᵢ-★ A G g q) ()
⊑ᵢ-trans-fuel {n = zero} (⊑ᵢ-‵ ι) (⊑ᵢ-★ A G g q) ()
⊑ᵢ-trans-fuel {n = zero} (⊑ᵢ-⇒ A A′ B B′ p₁ p₂) (⊑ᵢ-★ A₁ G g q) ()
⊑ᵢ-trans-fuel {n = zero} (⊑ᵢ-∀ A B p) (⊑ᵢ-★ A₁ G g q) ()
⊑ᵢ-trans-fuel {n = zero} (⊑ᵢ-ν A B p) (⊑ᵢ-★ A₁ G g q) ()
⊑ᵢ-trans-fuel {n = zero} p (⊑ᵢ-＇ X) h = p
⊑ᵢ-trans-fuel {n = zero} (⊑ᵢ-ν A B p) (⊑ᵢ-｀ α′) ()
⊑ᵢ-trans-fuel {n = zero} (⊑ᵢ-｀ α) (⊑ᵢ-｀ .α) h =
  ⊑ᵢ-｀ α
⊑ᵢ-trans-fuel {n = zero} p (⊑ᵢ-‵ ι) h = p
⊑ᵢ-trans-fuel {n = zero} (⊑ᵢ-⇒ A A′ B B′ p₁ p₂) (⊑ᵢ-⇒ A₁ A″ B₁ B″ q₁ q₂) ()
⊑ᵢ-trans-fuel {n = zero} (⊑ᵢ-∀ A B p) (⊑ᵢ-∀ A₁ B₁ q) ()
⊑ᵢ-trans-fuel {n = zero} (⊑ᵢ-∀ A B p) (⊑ᵢ-ν A₁ B₁ q) ()
⊑ᵢ-trans-fuel {n = zero} (⊑ᵢ-ν A B p) q ()
⊑ᵢ-trans-fuel {n = suc n} p ⊑ᵢ-★★ h = p
⊑ᵢ-trans-fuel {n = suc n} p (⊑ᵢ-★ B G g q) h =
  ⊑ᵢ-★ _ G g (⊑ᵢ-trans-fuel p q (pred-★-bound h))
⊑ᵢ-trans-fuel {n = suc n} p (⊑ᵢ-＇ X) h = p
⊑ᵢ-trans-fuel {n = suc n} (⊑ᵢ-ν A B p) q h =
  ⊑ᵢ-ν A _
    (⊑ᵢ-trans-fuel
      p
      (ν-weaken⊑ᵢ q)
      (subst
        (λ x → size⊑ᵢ p + x ≤ n)
        (sym (size-ν-weaken⊑ᵢ q))
        (ν-rec-bound {a = size⊑ᵢ p} {b = size⊑ᵢ q} h)))
⊑ᵢ-trans-fuel {n = suc n} (⊑ᵢ-｀ α) (⊑ᵢ-｀ .α) h =
  ⊑ᵢ-｀ α
⊑ᵢ-trans-fuel {n = suc n} p (⊑ᵢ-‵ ι) h = p
⊑ᵢ-trans-fuel {n = suc n} (⊑ᵢ-⇒ A A′ B B′ p₁ p₂)
    (⊑ᵢ-⇒ A₁ A″ B₁ B″ q₁ q₂) h =
  ⊑ᵢ-⇒ A A″ B B″
    (⊑ᵢ-trans-fuel
      p₁
      q₁
      (left-rec-⇒-bound
        {a = size⊑ᵢ p₁} {b = size⊑ᵢ p₂}
        {c = size⊑ᵢ q₁} {d = size⊑ᵢ q₂}
        h))
    (⊑ᵢ-trans-fuel
      p₂
      q₂
      (right-rec-⇒-bound
        {a = size⊑ᵢ p₁} {b = size⊑ᵢ p₂}
        {c = size⊑ᵢ q₁} {d = size⊑ᵢ q₂}
        h))
⊑ᵢ-trans-fuel {n = suc n} (⊑ᵢ-∀ A B p) (⊑ᵢ-∀ B₁ C q) h =
  ⊑ᵢ-∀ A C
    (⊑ᵢ-trans-fuel
      p
      q
      (∀ν-rec-bound {a = size⊑ᵢ p} {b = size⊑ᵢ q} h))
⊑ᵢ-trans-fuel {n = suc n} (⊑ᵢ-∀ A B p) (⊑ᵢ-ν B₁ C q) h =
  ⊑ᵢ-ν A C
    (⊑ᵢ-trans-fuel
      (plain-to-ν⊑ᵢ p)
      q
      (subst
        (λ x → x + size⊑ᵢ q ≤ n)
        (sym (size-plain-to-ν⊑ᵢ p))
        (∀ν-rec-bound {a = size⊑ᵢ p} {b = size⊑ᵢ q} h)))

⊑ᵢ-trans :
  ∀ {Γ A B C} →
  Γ ⊢ A ⊑ᵢ B →
  Γ ⊢ B ⊑ᵢ C →
  Γ ⊢ A ⊑ᵢ C
⊑ᵢ-trans p q = ⊑ᵢ-trans-fuel p q ≤-refl

⊒ᵢ-trans :
  ∀ {Γ A B C} →
  Γ ⊢ A ⊒ᵢ B →
  Γ ⊢ B ⊒ᵢ C →
  Γ ⊢ A ⊒ᵢ C
⊒ᵢ-trans p q = ⊑ᵢ-trans q p

interpSeal-plains-empty : ∀ n α → interpSeal (plains n []) α ≡ α
interpSeal-plains-empty zero α = refl
interpSeal-plains-empty (suc n) α = interpSeal-plains-empty n α

interpSeal-plains-ν :
  ∀ n Γ α →
  interpSeal (plains n (ν-bound ∷ Γ)) α ≡
  suc (interpSeal (plains n Γ) α)
interpSeal-plains-ν zero Γ α = refl
interpSeal-plains-ν (suc n) Γ α = interpSeal-plains-ν n Γ α

interp-plains-empty : ∀ n A → interp (plains n []) A ≡ A
interp-plains-empty zero (＇ X) = refl
interp-plains-empty (suc n) (＇ zero) = refl
interp-plains-empty (suc n) (＇ (suc X)) =
  cong ⇑ᵗ (interp-plains-empty n (＇ X))
interp-plains-empty n (｀ α) = cong ｀_ (interpSeal-plains-empty n α)
interp-plains-empty n (‵ ι) = refl
interp-plains-empty n ★ = refl
interp-plains-empty n (A ⇒ B) =
  cong₂ _⇒_ (interp-plains-empty n A) (interp-plains-empty n B)
interp-plains-empty n (`∀ A) = cong `∀ (interp-plains-empty (suc n) A)

interp-empty : ∀ A → interp [] A ≡ A
interp-empty A = interp-plains-empty zero A

interp-ν-left-at :
  ∀ n Γ A →
  interp (plains n (ν-bound ∷ Γ)) A ≡
  substᵗ (openνEnv n) (⇑ˢ (interp (plains (suc n) Γ) A))
interp-ν-left-at zero Γ (＇ zero) = refl
interp-ν-left-at zero Γ (＇ (suc X)) =
  sym
    (trans
      (cong
        (substᵗ (singleTyEnv α₀))
        (sym (renameᵗ-⇑ˢ suc (interpVar Γ X))))
      (open-renᵗ-suc (⇑ˢ (interpVar Γ X)) α₀))
interp-ν-left-at (suc n) Γ (＇ zero) = refl
interp-ν-left-at (suc n) Γ (＇ (suc X)) =
  trans
    (cong ⇑ᵗ (interp-ν-left-at n Γ (＇ X)))
    (trans
      (sym
        (substᵗ-suc-renameᵗ-suc
          (openνEnv n)
          (⇑ˢ (interpVar (plains (suc n) Γ) X))))
      (cong
        (substᵗ (extsᵗ (openνEnv n)))
        (renameᵗ-⇑ˢ suc (interpVar (plains (suc n) Γ) X))))
interp-ν-left-at n Γ (｀ α) = cong ｀_ (interpSeal-plains-ν n Γ α)
interp-ν-left-at n Γ (‵ ι) = refl
interp-ν-left-at n Γ ★ = refl
interp-ν-left-at n Γ (A ⇒ B) =
  cong₂ _⇒_ (interp-ν-left-at n Γ A) (interp-ν-left-at n Γ B)
interp-ν-left-at n Γ (`∀ A) =
  cong `∀ (interp-ν-left-at (suc n) Γ A)

interp-ν-left :
  ∀ Γ A →
  interp (ν-bound ∷ Γ) A ≡
  (⇑ˢ (interp (plain ∷ Γ) A)) [ α₀ ]ᵗ
interp-ν-left Γ A = interp-ν-left-at zero Γ A

interp-ν-right-at :
  ∀ n Γ B →
  interp (plains n (ν-bound ∷ Γ)) (renameᵗ (raiseVarFrom n) B) ≡
  ⇑ˢ (interp (plains n Γ) B)
interp-ν-right-at zero Γ (＇ X) = refl
interp-ν-right-at (suc n) Γ (＇ zero) = refl
interp-ν-right-at (suc n) Γ (＇ (suc X)) =
  trans
    (cong ⇑ᵗ (interp-ν-right-at n Γ (＇ X)))
    (renameᵗ-⇑ˢ suc (interpVar (plains n Γ) X))
interp-ν-right-at n Γ (｀ α) = cong ｀_ (interpSeal-plains-ν n Γ α)
interp-ν-right-at n Γ (‵ ι) = refl
interp-ν-right-at n Γ ★ = refl
interp-ν-right-at n Γ (A ⇒ B) =
  cong₂ _⇒_ (interp-ν-right-at n Γ A) (interp-ν-right-at n Γ B)
interp-ν-right-at n Γ (`∀ A) =
  cong `∀
    (trans
      (cong
        (interp (plains (suc n) (ν-bound ∷ Γ)))
        (renameᵗ-cong (raise-ext n) A))
      (interp-ν-right-at (suc n) Γ A))

interp-ν-right :
  ∀ Γ B →
  interp (ν-bound ∷ Γ) (⇑ᵗ B) ≡ ⇑ˢ (interp Γ B)
interp-ν-right Γ B = interp-ν-right-at zero Γ B

cast⊑-cong :
  ∀ {Σ Φ A A′ B B′} →
  A ≡ A′ →
  B ≡ B′ →
  Σ ∣ Φ ⊢ A ⊑ᶜ B →
  Σ ∣ Φ ⊢ A′ ⊑ᶜ B′
cast⊑-cong refl refl p = p

cast⊒-cong :
  ∀ {Σ Φ A A′ B B′} →
  A ≡ A′ →
  B ≡ B′ →
  Σ ∣ Φ ⊢ A ⊒ᶜ B →
  Σ ∣ Φ ⊢ A′ ⊒ᶜ B′
cast⊒-cong refl refl p = p

------------------------------------------------------------------------
-- Permission resources for seals below a bound
------------------------------------------------------------------------

Resource : Store → List CastPerm → ℕ → Set
Resource Σ Φ n =
  ∀ {α} →
  α < n →
  (Σ ∋ˢ α ⦂ ★ × α ∈cast Φ) ⊎ α ∈tag Φ

resource-restrict :
  ∀ {Σ Φ m n} →
  m ≤ n →
  Resource Σ Φ n →
  Resource Σ Φ m
resource-restrict m≤n r α<m = r (<-≤-trans α<m m≤n)

liftLookup★ :
  ∀ {Σ α} →
  Σ ∋ˢ α ⦂ ★ →
  ⟰ˢ Σ ∋ˢ suc α ⦂ ★
liftLookup★ (Z∋ˢ α≡β A≡B) =
  Z∋ˢ (cong suc α≡β) (cong (renameˢ suc) A≡B)
liftLookup★ (S∋ˢ h) = S∋ˢ (liftLookup★ h)

resource-renameᵗ :
  ∀ {Σ Φ n} →
  Resource Σ Φ n →
  Resource (⟰ᵗ Σ) Φ n
resource-renameᵗ r α<n with r α<n
... | inj₁ (h , c) = inj₁ (renameLookupᵗ suc h , c)
... | inj₂ t = inj₂ t

resource-upν :
  ∀ {Σ Φ n} →
  Resource Σ Φ n →
  Resource ((zero , ★) ∷ ⟰ˢ Σ) (cast-seal ∷ Φ) (suc n)
resource-upν r {zero} z<s = inj₁ (Z∋ˢ refl refl , here-cast-only)
resource-upν r {suc α} (s<s α<n) with r α<n
... | inj₁ (h , c) = inj₁ (S∋ˢ (liftLookup★ h) , there-cast c)
... | inj₂ t = inj₂ (there-tag t)

resource-downν :
  ∀ {Σ Φ n} →
  Resource Σ Φ n →
  Resource ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) (cast-tag ∷ Φ) (suc n)
resource-downν r {zero} z<s = inj₂ here-tag-only
resource-downν r {suc α} (s<s α<n) with r α<n
... | inj₁ (h , c) = inj₁ (S∋ˢ (liftLookup★ h) , there-cast c)
... | inj₂ t = inj₂ (there-tag t)

ground⊑⇒cast⊑★ :
  ∀ {Σ Φ n Γ G} →
  Resource Σ Φ n →
  (g : Groundᵢ Γ G) →
  maxGroundᵢ g < n →
  Σ ∣ Φ ⊢ interp Γ G ⊑ᶜ ★
ground⊑⇒cast⊑★ r (ground-ν x∈) α<n with ν-lookup-seal x∈
... | α , eq with r α<n
...   | inj₁ (h , α∈cast) =
        cast⊑-cong (sym eq) refl (⊑ᶜ-unseal★ h α∈cast)
...   | inj₂ α∈tag =
        cast⊑-cong (sym eq) refl (⊑ᶜ-tag (｀ α) α∈tag)
ground⊑⇒cast⊑★ {Γ = Γ} r (ground-seal α) α<n
  with r {interpSeal Γ α} α<n
... | inj₁ (h , α∈cast) = ⊑ᶜ-unseal★ h α∈cast
... | inj₂ α∈tag = ⊑ᶜ-tag (｀ (interpSeal Γ α)) α∈tag
ground⊑⇒cast⊑★ r (ground-base ι) α<n = ⊑ᶜ-tag (‵ ι) tt
ground⊑⇒cast⊑★ r ground-fun α<n = ⊑ᶜ-tag ★⇒★ tt

ground⊒⇒cast⊒★ :
  ∀ {Σ Φ n Γ G} →
  Resource Σ Φ n →
  (g : Groundᵢ Γ G) →
  maxGroundᵢ g < n →
  Σ ∣ Φ ⊢ ★ ⊒ᶜ interp Γ G
ground⊒⇒cast⊒★ r (ground-ν x∈) α<n with ν-lookup-seal x∈
... | α , eq with r α<n
...   | inj₁ (h , α∈cast) =
        cast⊒-cong refl (sym eq) (⊒ᶜ-seal★ h α∈cast)
...   | inj₂ α∈tag =
        cast⊒-cong refl (sym eq) (⊒ᶜ-untag (｀ α) α∈tag zero)
ground⊒⇒cast⊒★ {Γ = Γ} r (ground-seal α) α<n
  with r {interpSeal Γ α} α<n
... | inj₁ (h , α∈cast) = ⊒ᶜ-seal★ h α∈cast
... | inj₂ α∈tag = ⊒ᶜ-untag (｀ (interpSeal Γ α)) α∈tag zero
ground⊒⇒cast⊒★ r (ground-base ι) α<n = ⊒ᶜ-untag (‵ ι) tt zero
ground⊒⇒cast⊒★ r ground-fun α<n = ⊒ᶜ-untag ★⇒★ tt zero

------------------------------------------------------------------------
-- Soundness bridge to same-seal Cast
------------------------------------------------------------------------

mutual
  seal⊑-cast :
    ∀ {Σ Φ α} →
    Resource Σ Φ zero →
    Σ ∣ Φ ⊢ ｀ α ⊑ᶜ ｀ α
  seal⊑-cast {α = α} r = ⊑ᶜ-seal α

  seal⊒-cast :
    ∀ {Σ Φ α} →
    Resource Σ Φ zero →
    Σ ∣ Φ ⊢ ｀ α ⊒ᶜ ｀ α
  seal⊒-cast {α = α} r = ⊒ᶜ-seal α

  build⊑ :
    ∀ {Γ A B} →
    Γ ⊢ A ⊑ᵢ B →
    ∃[ n ] (∀ {Σ Φ} →
      Resource Σ Φ n →
      Σ ∣ Φ ⊢ interp Γ A ⊑ᶜ interp Γ B)
  build⊑ ⊑ᵢ-★★ = zero , (λ r → ⊑ᶜ-id (wfTySome ★))
  build⊑ (⊑ᵢ-★ A G g p) with build⊑ p
  build⊑ (⊑ᵢ-★ A G g p) | n , f =
    (suc (maxGroundᵢ g) ⊔ n) ,
    (λ r →
      f (resource-restrict (m≤n⊔m (suc (maxGroundᵢ g)) n) r) ；⊑ᶜ
      ground⊑⇒cast⊑★
        r
        g
        (<-≤-trans (n<1+n (maxGroundᵢ g))
          (m≤m⊔n (suc (maxGroundᵢ g)) n)))
  build⊑ {Γ = Γ} (⊑ᵢ-＇ X) =
    zero , (λ r → ⊑ᶜ-id (wfTySome (interpVar Γ X)))
  build⊑ (⊑ᵢ-｀ α) = zero , (λ r → seal⊑-cast r)
  build⊑ (⊑ᵢ-‵ ι) = zero , (λ r → ⊑ᶜ-id (wfTySome (‵ ι)))
  build⊑ (⊑ᵢ-⇒ A A′ B B′ p q) with build⊒ p | build⊑ q
  build⊑ (⊑ᵢ-⇒ A A′ B B′ p q) | n₁ , f₁ | n₂ , f₂ =
    (n₁ ⊔ n₂) ,
    (λ r →
      ⊑ᶜ-⇒
        (f₁ (resource-restrict (m≤m⊔n n₁ n₂) r))
        (f₂ (resource-restrict (m≤n⊔m n₁ n₂) r)))
  build⊑ (⊑ᵢ-∀ A B p) with build⊑ p
  build⊑ (⊑ᵢ-∀ A B p) | n , f =
    n , (λ r → ⊑ᶜ-∀ (f (resource-renameᵗ r)))
  build⊑ {Γ = Γ} (⊑ᵢ-ν A B p) with build⊑ p
  build⊑ {Γ = Γ} (⊑ᵢ-ν A B p) | n , f =
    n ,
    (λ r →
      ⊑ᶜ-ν
        (cast⊑-cong
          (interp-ν-left Γ A)
          (interp-ν-right Γ B)
          (f (resource-restrict (n≤1+n n) (resource-upν r)))))

  build⊒ :
    ∀ {Γ A B} →
    Γ ⊢ A ⊒ᵢ B →
    ∃[ n ] (∀ {Σ Φ} →
      Resource Σ Φ n →
      Σ ∣ Φ ⊢ interp Γ A ⊒ᶜ interp Γ B)
  build⊒ ⊑ᵢ-★★ = zero , (λ r → ⊒ᶜ-id (wfTySome ★))
  build⊒ (⊑ᵢ-★ A G g p) with build⊒ p
  build⊒ (⊑ᵢ-★ A G g p) | n , f =
    (suc (maxGroundᵢ g) ⊔ n) ,
    (λ r →
      ground⊒⇒cast⊒★
        r
        g
        (<-≤-trans (n<1+n (maxGroundᵢ g))
          (m≤m⊔n (suc (maxGroundᵢ g)) n)) ；⊒ᶜ
      f (resource-restrict (m≤n⊔m (suc (maxGroundᵢ g)) n) r))
  build⊒ {Γ = Γ} (⊑ᵢ-＇ X) =
    zero , (λ r → ⊒ᶜ-id (wfTySome (interpVar Γ X)))
  build⊒ (⊑ᵢ-｀ α) = zero , (λ r → seal⊒-cast r)
  build⊒ (⊑ᵢ-‵ ι) = zero , (λ r → ⊒ᶜ-id (wfTySome (‵ ι)))
  build⊒ (⊑ᵢ-⇒ A A′ B B′ p q) with build⊑ p | build⊒ q
  build⊒ (⊑ᵢ-⇒ A A′ B B′ p q) | n₁ , f₁ | n₂ , f₂ =
    (n₁ ⊔ n₂) ,
    (λ r →
      ⊒ᶜ-⇒
        (f₁ (resource-restrict (m≤m⊔n n₁ n₂) r))
        (f₂ (resource-restrict (m≤n⊔m n₁ n₂) r)))
  build⊒ (⊑ᵢ-∀ A B p) with build⊒ p
  build⊒ (⊑ᵢ-∀ A B p) | n , f =
    n , (λ r → ⊒ᶜ-∀ (f (resource-renameᵗ r)))
  build⊒ {Γ = Γ} (⊑ᵢ-ν A B p) with build⊒ p
  build⊒ {Γ = Γ} (⊑ᵢ-ν A B p) | n , f =
    n ,
    (λ r →
      ⊒ᶜ-ν
        (cast⊒-cong
          (interp-ν-right Γ B)
          (interp-ν-left Γ A)
          (f (resource-restrict (n≤1+n n) (resource-downν r)))))

tagPerms : ℕ → List CastPerm
tagPerms zero = []
tagPerms (suc n) = cast-tag ∷ tagPerms n

tagPerms-member :
  ∀ {n α} →
  α < n →
  α ∈tag tagPerms n
tagPerms-member {zero} ()
tagPerms-member {suc n} {zero} z<s = here-tag-only
tagPerms-member {suc n} {suc α} (s<s α<n) = there-tag (tagPerms-member α<n)

resource-tagPerms :
  ∀ n →
  Resource ∅ˢ (tagPerms n) n
resource-tagPerms n α<n = inj₂ (tagPerms-member α<n)

imprecision⊑⇒cast⊑ :
  ∀ {A B} →
  [] ⊢ A ⊑ᵢ B →
  ∃[ Φ ] (∅ˢ ∣ Φ ⊢ A ⊑ᶜ B)
imprecision⊑⇒cast⊑ p with build⊑ p
... | n , f =
  tagPerms n ,
  cast⊑-cong (interp-empty _) (interp-empty _) (f (resource-tagPerms n))

imprecision⊒⇒cast⊒ :
  ∀ {A B} →
  [] ⊢ A ⊒ᵢ B →
  ∃[ Φ ] (∅ˢ ∣ Φ ⊢ A ⊒ᶜ B)
imprecision⊒⇒cast⊒ p with build⊒ p
... | n , f =
  tagPerms n ,
  cast⊒-cong (interp-empty _) (interp-empty _) (f (resource-tagPerms n))

------------------------------------------------------------------------
-- Completeness experiment
------------------------------------------------------------------------

ground-castᵢ-plain : ∀ n {G} → Ground G → Groundᵢ (plains n []) G
ground-castᵢ-plain n (｀ α) = ground-seal α
ground-castᵢ-plain n (‵ ι) = ground-base ι
ground-castᵢ-plain n ★⇒★ = ground-fun

mutual
  ν-close⊑-plain :
    ∀ n {Σ Φ A B} →
    ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢
      (⇑ˢ A) [ α₀ ]ᵗ ⊑ᶜ ⇑ˢ B →
    (ν-bound ∷ plains n []) ⊢ A ⊑ᵢ ⇑ᵗ B
  ν-close⊑-plain n {A = A} {B = B} p =
    ⊑ᵢ-cast
      (close-openν-zero A)
      (closeνSrc-⇑ˢ zero B)
      (closeν-⊑ᵢ zero (cast⊑⇒imprecision⊑-plain n p))

  ν-close⊒-plain :
    ∀ n {Σ Φ A B} →
    ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢
      ⇑ˢ B ⊒ᶜ (⇑ˢ A) [ α₀ ]ᵗ →
    (ν-bound ∷ plains n []) ⊢ ⇑ᵗ B ⊒ᵢ A
  ν-close⊒-plain n {A = A} {B = B} p =
    ⊑ᵢ-cast
      (close-openν-zero A)
      (closeνSrc-⇑ˢ zero B)
      (closeν-⊑ᵢ zero (cast⊒⇒imprecision⊒-plain n p))

  cast⊑⇒imprecision⊑-plain :
    ∀ n {Σ Φ A B} →
    Σ ∣ Φ ⊢ A ⊑ᶜ B →
    plains n [] ⊢ A ⊑ᵢ B
  cast⊑⇒imprecision⊑-plain n (⊑ᶜ-tag g ok) =
    ⊑ᵢ-★ _ _ (ground-castᵢ-plain n g) ⊑ᵢ-refl
  cast⊑⇒imprecision⊑-plain n (⊑ᶜ-unseal★ {α} h α∈Φ) =
    ⊑ᵢ-★ _ _ (ground-seal α) (⊑ᵢ-｀ α)
  cast⊑⇒imprecision⊑-plain n (⊑ᶜ-seal α) = ⊑ᵢ-｀ α
  cast⊑⇒imprecision⊑-plain n (⊑ᶜ-⇒ p q) =
    ⊑ᵢ-⇒ _ _ _ _
      (cast⊒⇒imprecision⊒-plain n p)
      (cast⊑⇒imprecision⊑-plain n q)
  cast⊑⇒imprecision⊑-plain n (⊑ᶜ-∀ p) =
    ⊑ᵢ-∀ _ _ (cast⊑⇒imprecision⊑-plain (suc n) p)
  cast⊑⇒imprecision⊑-plain n (⊑ᶜ-ν p) =
    ⊑ᵢ-ν _ _ (ν-close⊑-plain n p)
  cast⊑⇒imprecision⊑-plain n (⊑ᶜ-id wfA) = ⊑ᵢ-refl
  cast⊑⇒imprecision⊑-plain n (p ；⊑ᶜ q) =
    ⊑ᵢ-trans
      (cast⊑⇒imprecision⊑-plain n p)
      (cast⊑⇒imprecision⊑-plain n q)

  cast⊒⇒imprecision⊒-plain :
    ∀ n {Σ Φ A B} →
    Σ ∣ Φ ⊢ A ⊒ᶜ B →
    plains n [] ⊢ A ⊒ᵢ B
  cast⊒⇒imprecision⊒-plain n (⊒ᶜ-untag g ok ℓ) =
    ⊑ᵢ-★ _ _ (ground-castᵢ-plain n g) ⊑ᵢ-refl
  cast⊒⇒imprecision⊒-plain n (⊒ᶜ-seal★ {α} h α∈Φ) =
    ⊑ᵢ-★ _ _ (ground-seal α) (⊑ᵢ-｀ α)
  cast⊒⇒imprecision⊒-plain n (⊒ᶜ-seal α) = ⊑ᵢ-｀ α
  cast⊒⇒imprecision⊒-plain n (⊒ᶜ-⇒ p q) =
    ⊑ᵢ-⇒ _ _ _ _
      (cast⊑⇒imprecision⊑-plain n p)
      (cast⊒⇒imprecision⊒-plain n q)
  cast⊒⇒imprecision⊒-plain n (⊒ᶜ-∀ p) =
    ⊑ᵢ-∀ _ _ (cast⊒⇒imprecision⊒-plain (suc n) p)
  cast⊒⇒imprecision⊒-plain n (⊒ᶜ-ν p) =
    ⊑ᵢ-ν _ _ (ν-close⊒-plain n p)
  cast⊒⇒imprecision⊒-plain n (⊒ᶜ-id wfA) = ⊑ᵢ-refl
  cast⊒⇒imprecision⊒-plain n (p ；⊒ᶜ q) =
    ⊒ᵢ-trans
      (cast⊒⇒imprecision⊒-plain n p)
      (cast⊒⇒imprecision⊒-plain n q)

cast⊑⇒imprecision⊑ :
  ∀ {Σ Φ A B} →
  Σ ∣ Φ ⊢ A ⊑ᶜ B →
  [] ⊢ A ⊑ᵢ B
cast⊑⇒imprecision⊑ = cast⊑⇒imprecision⊑-plain zero

cast⊒⇒imprecision⊒ :
  ∀ {Σ Φ A B} →
  Σ ∣ Φ ⊢ A ⊒ᶜ B →
  [] ⊢ A ⊒ᵢ B
cast⊒⇒imprecision⊒ = cast⊒⇒imprecision⊒-plain zero
