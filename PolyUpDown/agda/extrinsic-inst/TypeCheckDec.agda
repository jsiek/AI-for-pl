module TypeCheckDec where

-- File Charter:
--   * Decidable type check of raw terms.

open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (zero; suc; _≟_)
open import Data.Nat.Properties using (_<?_)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (subst; sym; refl; cong; cong₂; trans)

open import Types
open import Ctx using (⤊ᵗ; CtxWf; ctxWf-[]; ctxWf-∷)
open import UpDown
open import Terms
open import Store
open import TypeProperties

------------------------------------------------------------------------
-- Local propositions
------------------------------------------------------------------------

HasSomeType : TyCtx → SealCtx → Store → Ctx → Term → Set
HasSomeType Δ Ψ Σ Γ M = Σ[ A ∈ Ty ] Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A

WellTyped : Term → Set
WellTyped M = HasSomeType 0 0 ∅ˢ [] M

data BlameFree : Term → Set where
  bf-` : ∀ {x} → BlameFree (` x)
  bf-ƛ : ∀ {A M} → BlameFree M → BlameFree (ƛ A ⇒ M)
  bf-· : ∀ {L M} → BlameFree L → BlameFree M → BlameFree (L · M)
  bf-Λ : ∀ {M} → BlameFree M → BlameFree (Λ M)
  bf-⦂∀ : ∀ {M B T} → BlameFree M → BlameFree (M ⦂∀ B [ T ])
  bf-$ : ∀ {κ} → BlameFree ($ κ)
  bf-⊕ : ∀ {L op M} → BlameFree L → BlameFree M → BlameFree (L ⊕[ op ] M)
  bf-up : ∀ {M p} → BlameFree M → BlameFree (M up p)
  bf-down : ∀ {M p} → BlameFree M → BlameFree (M down p)

HasSomeTypeBF : TyCtx → SealCtx → Store → Ctx → Term → Set
HasSomeTypeBF Δ Ψ Σ Γ M = HasSomeType Δ Ψ Σ Γ M × BlameFree M

WellTypedBF : Term → Set
WellTypedBF M = HasSomeTypeBF 0 0 ∅ˢ [] M

LookupAny : Ctx → Var → Set
LookupAny Γ x = Σ[ A ∈ Ty ] Γ ∋ x ⦂ A

StoreWf : TyCtx → SealCtx → Store → Set
StoreWf Δ Ψ Σ = Uniqueˢ Σ × (∀ {α A} → Σ ∋ˢ α ⦂ A → WfTy Δ Ψ A)

data NonArrow : Ty → Set where
  na-var : ∀ X → NonArrow (＇ X)
  na-seal : ∀ α → NonArrow (｀ α)
  na-base : ∀ ι → NonArrow (‵ ι)
  na-star : NonArrow ★
  na-all : ∀ A → NonArrow (`∀ A)

storeWf-∅ : StoreWf 0 0 ∅ˢ
storeWf-∅ = uniq[] , (λ ())

storeWf-tail :
  ∀ {Δ Ψ α A Σ} →
  StoreWf Δ Ψ ((α , A) ∷ Σ) →
  StoreWf Δ Ψ Σ
storeWf-tail (uniq∷_ α∉Σ uΣ , wfΣ) = uΣ , (λ h → wfΣ (S∋ˢ h))

ctxWf-⤊ᵗ :
  ∀ {Δ Ψ Γ} →
  CtxWf Δ Ψ Γ →
  CtxWf (suc Δ) Ψ (⤊ᵗ Γ)
ctxWf-⤊ᵗ {Γ = []} wfΓ ()
ctxWf-⤊ᵗ {Γ = B ∷ Γ} wfΓ Z =
  renameᵗ-preserves-WfTy (wfΓ Z) TyRenameWf-suc
ctxWf-⤊ᵗ {Γ = B ∷ Γ} wfΓ (S h) =
  ctxWf-⤊ᵗ
    (λ {x A} h′ → wfΓ (S h′))
    h

storeWf-⟰ᵗ :
  ∀ {Δ Ψ Σ} →
  StoreWf Δ Ψ Σ →
  StoreWf (suc Δ) Ψ (⟰ᵗ Σ)
storeWf-⟰ᵗ {Δ = Δ} {Ψ = Ψ} {Σ = []} wfΣ =
  uniq[] , (λ ())
storeWf-⟰ᵗ {Δ = Δ} {Ψ = Ψ} {Σ = (α , B) ∷ Σ} wfΣ =
  unique-⟰ᵗ (proj₁ wfΣ) , wf
  where
    wf : ∀ {β A′} → ⟰ᵗ ((α , B) ∷ Σ) ∋ˢ β ⦂ A′ → WfTy (suc Δ) Ψ A′
    wf (Z∋ˢ α≡β A≡B) =
      subst
        (WfTy (suc Δ) Ψ)
        (sym A≡B)
        (renameᵗ-preserves-WfTy ((proj₂ wfΣ) (Z∋ˢ refl refl)) TyRenameWf-suc)
    wf (S∋ˢ h) = proj₂ (storeWf-⟰ᵗ (storeWf-tail wfΣ)) h

storeWf-⟰ˢ :
  ∀ {Δ Ψ Σ} →
  StoreWf Δ Ψ Σ →
  StoreWf Δ (suc Ψ) (⟰ˢ Σ)
storeWf-⟰ˢ {Δ = Δ} {Ψ = Ψ} {Σ = []} wfΣ =
  uniq[] , (λ ())
storeWf-⟰ˢ {Δ = Δ} {Ψ = Ψ} {Σ = (α , B) ∷ Σ} wfΣ =
  unique-⟰ˢ (proj₁ wfΣ) , wf
  where
    wf : ∀ {β A} → ⟰ˢ ((α , B) ∷ Σ) ∋ˢ β ⦂ A → WfTy Δ (suc Ψ) A
    wf (Z∋ˢ α≡β A≡B) =
      subst
        (WfTy Δ (suc Ψ))
        (sym A≡B)
        (renameˢ-preserves-WfTy ((proj₂ wfΣ) (Z∋ˢ refl refl)) SealRenameWf-suc)
    wf (S∋ˢ h) = proj₂ (storeWf-⟰ˢ (storeWf-tail wfΣ)) h

ctxWf-⤊ˢ :
  ∀ {Δ Ψ Γ} →
  CtxWf Δ Ψ Γ →
  CtxWf Δ (suc Ψ) (⤊ˢ Γ)
ctxWf-⤊ˢ {Γ = []} wfΓ ()
ctxWf-⤊ˢ {Γ = B ∷ Γ} wfΓ Z =
  renameˢ-preserves-WfTy (wfΓ Z) SealRenameWf-suc
ctxWf-⤊ˢ {Γ = B ∷ Γ} wfΓ (S h) =
  ctxWf-⤊ˢ
    (λ {x A} h′ → wfΓ (S h′))
    h

storeWf-ν-ext :
  ∀ {Δ Ψ Σ A} →
  WfTy Δ Ψ A →
  StoreWf Δ Ψ Σ →
  StoreWf Δ (suc Ψ) ((zero , ⇑ˢ A) ∷ ⟰ˢ Σ)
storeWf-ν-ext {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {A = A} wfA wfΣ =
  unique-ν A (proj₁ wfΣ) , wf
  where
    wf : ∀ {α B} → ((zero , ⇑ˢ A) ∷ ⟰ˢ Σ) ∋ˢ α ⦂ B → WfTy Δ (suc Ψ) B
    wf (Z∋ˢ α≡β A≡B) =
      subst
        (WfTy Δ (suc Ψ))
        (sym A≡B)
        (renameˢ-preserves-WfTy wfA SealRenameWf-suc)
    wf (S∋ˢ h) = proj₂ (storeWf-⟰ˢ wfΣ) h

------------------------------------------------------------------------
-- Blame-free uniqueness helpers
------------------------------------------------------------------------

lookup-unique-ctx :
  ∀ {Γ : Ctx} {x : Var} {A B : Ty} →
  Γ ∋ x ⦂ A →
  Γ ∋ x ⦂ B →
  A ≡ B
lookup-unique-ctx Z Z = refl
lookup-unique-ctx {x = suc x} (S hA) (S hB) = lookup-unique-ctx hA hB

codTy : Ty → Ty
codTy (A ⇒ B) = B
codTy (＇ X) = ＇ X
codTy (｀ α) = ｀ α
codTy (‵ ι) = ‵ ι
codTy ★ = ★
codTy (`∀ A) = `∀ A

forallBodyTy : Ty → Ty
forallBodyTy (`∀ A) = A
forallBodyTy (A ⇒ B) = A ⇒ B
forallBodyTy (＇ X) = ＇ X
forallBodyTy (｀ α) = ｀ α
forallBodyTy (‵ ι) = ‵ ι
forallBodyTy ★ = ★


⇑ˢ-injective :
  ∀ {A B : Ty} →
  ⇑ˢ A ≡ ⇑ˢ B →
  A ≡ B
⇑ˢ-injective {A = A} {B = B} A≡B =
  trans
    (sym (renameˢ-single-⇑ˢ-id zero A))
    (trans
      (cong (renameˢ (singleSealEnv zero)) A≡B)
      (renameˢ-single-⇑ˢ-id zero B))

------------------------------------------------------------------------
-- `ν`-source inversion helpers
------------------------------------------------------------------------

lowerVarFrom : TyVar → TyVar → TyVar
lowerVarFrom zero zero = zero
lowerVarFrom zero (suc X) = X
lowerVarFrom (suc k) zero = zero
lowerVarFrom (suc k) (suc X) = suc (lowerVarFrom k X)

markSubst : TyVar → Substᵗ
markSubst k X with X ≟ k
... | yes _ = ｀ zero
... | no _ = ＇ (lowerVarFrom k X)

raiseVarFrom : TyVar → TyVar → TyVar
raiseVarFrom zero X = suc X
raiseVarFrom (suc k) zero = zero
raiseVarFrom (suc k) (suc X) = suc (raiseVarFrom k X)

raise-lower-neq :
  ∀ (k X : TyVar) →
  (X ≡ k → ⊥) →
  raiseVarFrom k (lowerVarFrom k X) ≡ X
raise-lower-neq zero zero X≢0 = ⊥-elim (X≢0 refl)
raise-lower-neq zero (suc X) X≢0 = refl
raise-lower-neq (suc k) zero X≢suc = refl
raise-lower-neq (suc k) (suc X) X≢suc =
  cong suc
    (raise-lower-neq
      k
      X
      (λ X≡k → X≢suc (cong suc X≡k)))

suc-injectiveᵛ :
  ∀ {m n : TyVar} →
  suc m ≡ suc n →
  m ≡ n
suc-injectiveᵛ refl = refl

closeνSrc : TyVar → Ty → Ty
closeνSrc k (＇ X) = ＇ (raiseVarFrom k X)
closeνSrc k (｀ zero) = ＇ k
closeνSrc k (｀ (suc α)) = ｀ α
closeνSrc k (‵ ι) = ‵ ι
closeνSrc k ★ = ★
closeνSrc k (A ⇒ B) = closeνSrc k A ⇒ closeνSrc k B
closeνSrc k (`∀ A) = `∀ (closeνSrc (suc k) A)

markSubst-self :
  ∀ (k : TyVar) →
  markSubst k k ≡ ｀ zero
markSubst-self k with k ≟ k
... | yes _ = refl
... | no k≢k = ⊥-elim (k≢k refl)

markSubst-neq :
  ∀ (k X : TyVar) →
  (X ≡ k → ⊥) →
  markSubst k X ≡ ＇ (lowerVarFrom k X)
markSubst-neq k X X≢k with X ≟ k
... | yes X≡k = ⊥-elim (X≢k X≡k)
... | no _ = refl

markSubst-exts :
  ∀ {k X} →
  extsᵗ (markSubst k) X ≡ markSubst (suc k) X
markSubst-exts {k = k} {zero} = refl
markSubst-exts {k = k} {suc X} with X ≟ k
... | yes X≡k rewrite X≡k | markSubst-self k | markSubst-self (suc k) = refl
... | no X≢k rewrite markSubst-neq k X X≢k =
  sym
    (markSubst-neq
      (suc k)
      (suc X)
      (λ sucX≡sucK → X≢k (suc-injectiveᵛ sucX≡sucK)))

close-markSubst-id :
  ∀ (k : TyVar) (X : TyVar) →
  closeνSrc k (markSubst k X) ≡ ＇ X
close-markSubst-id k X with X ≟ k
... | yes X≡k = cong ＇_ (sym X≡k)
... | no X≢k = cong ＇_ (raise-lower-neq k X X≢k)

close-openνSrc-id :
  ∀ (k : TyVar) (A : Ty) →
  closeνSrc k (substᵗ (markSubst k) (⇑ˢ A)) ≡ A
close-openνSrc-id k (＇ X) = close-markSubst-id k X
close-openνSrc-id k (｀ α) = refl
close-openνSrc-id k (‵ ι) = refl
close-openνSrc-id k ★ = refl
close-openνSrc-id k (A ⇒ B) =
  cong₂ _⇒_
    (close-openνSrc-id k A)
    (close-openνSrc-id k B)
close-openνSrc-id k (`∀ A) =
  cong `∀
    (trans
      (cong
        (closeνSrc (suc k))
        (substᵗ-cong (λ X → markSubst-exts {k = k} {X = X}) (⇑ˢ A)))
      (close-openνSrc-id (suc k) A))

markSubst-zero :
  ∀ (X : TyVar) →
  markSubst zero X ≡ singleTyEnv (｀ zero) X
markSubst-zero zero = refl
markSubst-zero (suc X) = refl

openνSrc-zero :
  ∀ (A : Ty) →
  substᵗ (markSubst zero) (⇑ˢ A) ≡ (⇑ˢ A) [ ｀ zero ]ᵗ
openνSrc-zero A = substᵗ-cong markSubst-zero (⇑ˢ A)

ν-src-injective :
  ∀ {A B : Ty} →
  ((⇑ˢ A) [ ｀ zero ]ᵗ) ≡ ((⇑ˢ B) [ ｀ zero ]ᵗ) →
  A ≡ B
ν-src-injective {A = A} {B = B} eq =
  trans
    (sym (close-openνSrc-id zero A))
    (trans
      (cong (closeνSrc zero)
        (trans
          (openνSrc-zero A)
          (trans eq (sym (openνSrc-zero B)))))
      (close-openνSrc-id zero B))

raiseVarFrom-≢ :
  ∀ (k X : TyVar) →
  raiseVarFrom k X ≡ k →
  ⊥
raiseVarFrom-≢ zero X ()
raiseVarFrom-≢ (suc k) zero ()
raiseVarFrom-≢ (suc k) (suc X) eq =
  raiseVarFrom-≢ k X (suc-injectiveᵛ eq)

lower-raiseVarFrom-id :
  ∀ (k X : TyVar) →
  lowerVarFrom k (raiseVarFrom k X) ≡ X
lower-raiseVarFrom-id zero X = refl
lower-raiseVarFrom-id (suc k) zero = refl
lower-raiseVarFrom-id (suc k) (suc X) =
  cong suc (lower-raiseVarFrom-id k X)

markSubst-raiseVarFrom :
  ∀ (k X : TyVar) →
  markSubst k (raiseVarFrom k X) ≡ ＇ X
markSubst-raiseVarFrom k X with raiseVarFrom k X ≟ k
... | yes eq = ⊥-elim (raiseVarFrom-≢ k X eq)
... | no neq rewrite markSubst-neq k (raiseVarFrom k X) neq =
  cong ＇_ (lower-raiseVarFrom-id k X)

open-closeνSrc-k :
  ∀ (k : TyVar) (C : Ty) →
  substᵗ (markSubst k) (⇑ˢ (closeνSrc k C)) ≡ C
open-closeνSrc-k k (＇ X) = markSubst-raiseVarFrom k X
open-closeνSrc-k k (｀ zero) = markSubst-self k
open-closeνSrc-k k (｀ (suc α)) = refl
open-closeνSrc-k k (‵ ι) = refl
open-closeνSrc-k k ★ = refl
open-closeνSrc-k k (A ⇒ B) =
  cong₂ _⇒_
    (open-closeνSrc-k k A)
    (open-closeνSrc-k k B)
open-closeνSrc-k k (`∀ A) =
  cong `∀
    (trans
      (substᵗ-cong (λ X → markSubst-exts {k = k} {X = X}) (⇑ˢ (closeνSrc (suc k) A)))
      (open-closeνSrc-k (suc k) A))

open-closeνSrc-id :
  (C : Ty) →
  ((⇑ˢ (closeνSrc zero C)) [ ｀ zero ]ᵗ ≡ C)
open-closeνSrc-id C =
  trans
    (sym (substᵗ-cong markSubst-zero (⇑ˢ (closeνSrc zero C))))
    (open-closeνSrc-k zero C)

------------------------------------------------------------------------
-- Well-typed cast uniqueness
------------------------------------------------------------------------

mutual
  wt⊑-unique :
    ∀ {Σ Φ Φ′ A A′ B B′} {p : Up} →
    Uniqueˢ Σ →
    Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    Σ ∣ Φ′ ⊢ p ⦂ A′ ⊑ B′ →
    (A ≡ A′) × (B ≡ B′)
  wt⊑-unique uΣ (wt-tag g gokΞ) (wt-tag g′ gokΞ′) = refl , refl
  wt⊑-unique uΣ (wt-unseal h α∈Φ) (wt-unseal h′ α∈Φ′) =
    refl , lookup-unique uΣ h h′
  wt⊑-unique uΣ (wt-↦ {A = A} {A′ = A′} {B = B} {B′ = B′} p q)
                 (wt-↦ {A = A₁} {A′ = A₁′} {B = B₁} {B′ = B₁′} p′ q′) =
    (cong₂ _⇒_ eqA eqB) , (cong₂ _⇒_ eqA′ eqB′)
    where
      pEq : (A′ ≡ A₁′) × (A ≡ A₁)
      pEq = wt⊒-unique uΣ p p′

      qEq : (B ≡ B₁) × (B′ ≡ B₁′)
      qEq = wt⊑-unique uΣ q q′

      eqA′ : A′ ≡ A₁′
      eqA′ = proj₁ pEq

      eqA : A ≡ A₁
      eqA = proj₂ pEq

      eqB : B ≡ B₁
      eqB = proj₁ qEq

      eqB′ : B′ ≡ B₁′
      eqB′ = proj₂ qEq
  wt⊑-unique uΣ
             (wt-∀ {A = A} {B = B} p)
             (wt-∀ {A = A′} {B = B′} p′) =
    cong `∀ eqA , cong `∀ eqB
    where
      innerEq : (A ≡ A′) × (B ≡ B′)
      innerEq = wt⊑-unique (unique-⟰ᵗ uΣ) p p′

      eqA : A ≡ A′
      eqA = proj₁ innerEq

      eqB : B ≡ B′
      eqB = proj₂ innerEq
  wt⊑-unique uΣ
             (wt-ν {A = A} {B = B} p)
             (wt-ν {A = A′} {B = B′} p′) =
    cong `∀ (ν-src-injective eqSrc) , ⇑ˢ-injective eqTgt
    where
      innerEq :
        ( ((⇑ˢ A) [ ｀ zero ]ᵗ) ≡ ((⇑ˢ A′) [ ｀ zero ]ᵗ) ) ×
        ( ⇑ˢ B ≡ ⇑ˢ B′ )
      innerEq = wt⊑-unique (unique-ν ★ uΣ) p p′

      eqSrc : ((⇑ˢ A) [ ｀ zero ]ᵗ) ≡ ((⇑ˢ A′) [ ｀ zero ]ᵗ)
      eqSrc = proj₁ innerEq

      eqTgt : ⇑ˢ B ≡ ⇑ˢ B′
      eqTgt = proj₂ innerEq
  wt⊑-unique uΣ (wt-id wfA) (wt-id wfA′) = refl , refl
  wt⊑-unique uΣ
             (wt-； {A = A} {B = B} {C = C} p q)
             (wt-； {A = A′} {B = B′} {C = C′} p′ q′) =
    eqA , eqC
    where
      pEq : (A ≡ A′) × (B ≡ B′)
      pEq = wt⊑-unique uΣ p p′

      qEq : (B ≡ B′) × (C ≡ C′)
      qEq = wt⊑-unique uΣ q q′

      eqA : A ≡ A′
      eqA = proj₁ pEq

      eqC : C ≡ C′
      eqC = proj₂ qEq

  wt⊒-unique :
    ∀ {Σ Φ Φ′ A A′ B B′} {p : Down} →
    Uniqueˢ Σ →
    Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    Σ ∣ Φ′ ⊢ p ⦂ A′ ⊒ B′ →
    (A ≡ A′) × (B ≡ B′)
  wt⊒-unique uΣ (wt-untag g gokΞ ℓ) (wt-untag g′ gokΞ′ ℓ′) = refl , refl
  wt⊒-unique uΣ (wt-seal h α∈Φ) (wt-seal h′ α∈Φ′) =
    lookup-unique uΣ h h′ , refl
  wt⊒-unique uΣ (wt-↦ {A = A} {A′ = A′} {B = B} {B′ = B′} p q)
                 (wt-↦ {A = A₁} {A′ = A₁′} {B = B₁} {B′ = B₁′} p′ q′) =
    (cong₂ _⇒_ eqA eqB) , (cong₂ _⇒_ eqA′ eqB′)
    where
      pEq : (A′ ≡ A₁′) × (A ≡ A₁)
      pEq = wt⊑-unique uΣ p p′

      qEq : (B ≡ B₁) × (B′ ≡ B₁′)
      qEq = wt⊒-unique uΣ q q′

      eqA′ : A′ ≡ A₁′
      eqA′ = proj₁ pEq

      eqA : A ≡ A₁
      eqA = proj₂ pEq

      eqB : B ≡ B₁
      eqB = proj₁ qEq

      eqB′ : B′ ≡ B₁′
      eqB′ = proj₂ qEq
  wt⊒-unique uΣ
             (wt-∀ {A = A} {B = B} p)
             (wt-∀ {A = A′} {B = B′} p′) =
    cong `∀ eqA , cong `∀ eqB
    where
      innerEq : (A ≡ A′) × (B ≡ B′)
      innerEq = wt⊒-unique (unique-⟰ᵗ uΣ) p p′

      eqA : A ≡ A′
      eqA = proj₁ innerEq

      eqB : B ≡ B′
      eqB = proj₂ innerEq
  wt⊒-unique uΣ
             (wt-ν {A = A} {B = B} p)
             (wt-ν {A = A′} {B = B′} p′) =
    ⇑ˢ-injective eqSrc , cong `∀ (ν-src-injective eqTgt)
    where
      innerEq :
        ( ⇑ˢ B ≡ ⇑ˢ B′ ) ×
        ( ((⇑ˢ A) [ ｀ zero ]ᵗ) ≡ ((⇑ˢ A′) [ ｀ zero ]ᵗ) )
      innerEq = wt⊒-unique (unique-ν ★ uΣ) p p′

      eqSrc : ⇑ˢ B ≡ ⇑ˢ B′
      eqSrc = proj₁ innerEq

      eqTgt : ((⇑ˢ A) [ ｀ zero ]ᵗ) ≡ ((⇑ˢ A′) [ ｀ zero ]ᵗ)
      eqTgt = proj₂ innerEq
  wt⊒-unique uΣ (wt-id wfA) (wt-id wfA′) = refl , refl
  wt⊒-unique uΣ
             (wt-； {A = A} {B = B} {C = C} p q)
             (wt-； {A = A′} {B = B′} {C = C′} p′ q′) =
    eqA , eqC
    where
      pEq : (A ≡ A′) × (B ≡ B′)
      pEq = wt⊒-unique uΣ p p′

      qEq : (B ≡ B′) × (C ≡ C′)
      qEq = wt⊒-unique uΣ q q′

      eqA : A ≡ A′
      eqA = proj₁ pEq

      eqC : C ≡ C′
      eqC = proj₂ qEq

type-unique-blamefree :
  ∀ {Δ Ψ Σ Γ M A B} →
  Uniqueˢ Σ →
  BlameFree M →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ B →
  A ≡ B
type-unique-blamefree uΣ bf-` (⊢` x:A) (⊢` x:B) =
  lookup-unique-ctx x:A x:B
type-unique-blamefree uΣ (bf-ƛ {A = A} bfM) (⊢ƛ wfA M:A) (⊢ƛ wfA′ M:B) =
  cong (A ⇒_) (type-unique-blamefree uΣ bfM M:A M:B)
type-unique-blamefree uΣ (bf-· bfL bfM) (⊢· {A = A} {B = B} L:AB M:A) (⊢· {A = A′} {B = B′} L:A′B′ M:A′) =
  cong codTy (type-unique-blamefree uΣ bfL L:AB L:A′B′)
type-unique-blamefree uΣ (bf-Λ bfM) (⊢Λ M:A) (⊢Λ M:B) =
  cong `∀ (type-unique-blamefree (unique-⟰ᵗ uΣ) bfM M:A M:B)
type-unique-blamefree uΣ (bf-⦂∀ bfM)
  (⊢• {B = B} {T = T} M:∀B wfT)
  (⊢• {B = B′} {T = T′} M:∀B′ wfT′) = refl
type-unique-blamefree uΣ bf-$ (⊢$ κ) (⊢$ κ′) = refl
type-unique-blamefree uΣ (bf-⊕ bfL bfM) (⊢⊕ L:ℕ op M:ℕ) (⊢⊕ L:ℕ′ op′ M:ℕ′) = refl
type-unique-blamefree uΣ (bf-up bfM) (⊢up Φ M:A hp) (⊢up Φ′ M:A′ hp′) =
  proj₂ (wt⊑-unique uΣ hp hp′)
type-unique-blamefree uΣ (bf-down bfM) (⊢down Φ M:A hp) (⊢down Φ′ M:A′ hp′) =
  proj₂ (wt⊒-unique uΣ hp hp′)

storeWf-unique :
  ∀ {Δ Ψ Σ} →
  StoreWf Δ Ψ Σ →
  Uniqueˢ Σ
storeWf-unique = proj₁

------------------------------------------------------------------------
-- Decidable cast typing
------------------------------------------------------------------------

LookupStoreAny : Store → Seal → Set
LookupStoreAny Σ α = Σ[ A ∈ Ty ] Σ ∋ˢ α ⦂ A

lookupStoreAnyDec : (Σ : Store) → (α : Seal) → Dec (LookupStoreAny Σ α)
lookupStoreAnyDec [] α = no (λ { (A , ()) })
lookupStoreAnyDec ((β , B) ∷ Σ) α with seal-≟ α β
... | yes α≡β = yes (B , Z∋ˢ α≡β refl)
... | no α≢β with lookupStoreAnyDec Σ α
...   | yes (A , h) = yes (A , S∋ˢ h)
...   | no ¬lookup =
      no
        (λ
          { (A , Z∋ˢ α≡β A≡B) → α≢β α≡β
          ; (A , S∋ˢ h) → ¬lookup (A , h)
          })

permMemberDec : (α : Seal) → (P : List Bool) → Dec (α ∈ P)
permMemberDec α [] = no (λ ())
permMemberDec zero (true ∷ P) = yes here
permMemberDec zero (false ∷ P) = no (λ ())
permMemberDec (suc α) (b ∷ P) with permMemberDec α P
... | yes h = yes (there h)
... | no ¬h = no (λ { (there h) → ¬h h })

groundTyDec : (G : Ty) → Dec (Ground G)
groundTyDec (＇ X) = no (λ ())
groundTyDec (｀ α) = yes (｀ α)
groundTyDec (‵ ι) = yes (‵ ι)
groundTyDec ★ = no (λ ())
groundTyDec (`∀ A) = no (λ ())
groundTyDec (A ⇒ B) with A
groundTyDec (A ⇒ B) | ＇ X = no (λ ())
groundTyDec (A ⇒ B) | ｀ α = no (λ ())
groundTyDec (A ⇒ B) | ‵ ι = no (λ ())
groundTyDec (A ⇒ B) | ★ with B
groundTyDec (A ⇒ B) | ★ | ＇ X = no (λ ())
groundTyDec (A ⇒ B) | ★ | ｀ α = no (λ ())
groundTyDec (A ⇒ B) | ★ | ‵ ι = no (λ ())
groundTyDec (A ⇒ B) | ★ | ★ = yes ★⇒★
groundTyDec (A ⇒ B) | ★ | B₁ ⇒ B₂ = no (λ ())
groundTyDec (A ⇒ B) | ★ | `∀ B′ = no (λ ())
groundTyDec (A ⇒ B) | A₁ ⇒ A₂ = no (λ ())
groundTyDec (A ⇒ B) | `∀ A′ = no (λ ())

groundOkDec :
  ∀ {G : Ty} →
  (g : Ground G) →
  (Φ : List Bool) →
  Dec (⊢ g ok Φ)
groundOkDec (｀ α) Φ with permMemberDec α Φ
... | yes α∈Φ = no (λ α∉Φ → α∉Φ α∈Φ)
... | no α∉Φ = yes α∉Φ
groundOkDec (‵ ι) Φ = yes tt
groundOkDec ★⇒★ Φ = yes tt

ground-ok-cong :
  ∀ {G : Ty} {Φ : List Bool} {g g′ : Ground G} →
  ⊢ g ok Φ →
  ⊢ g′ ok Φ
ground-ok-cong {g = ｀ α} {g′ = ｀ .α} gok = gok
ground-ok-cong {g = ‵ ι} {g′ = ‵ .ι} gok = gok
ground-ok-cong {g = ★⇒★} {g′ = ★⇒★} gok = gok

unshiftSealTyDec :
  (C : Ty) →
  Dec (Σ[ B ∈ Ty ] C ≡ ⇑ˢ B)
unshiftSealTyDec (＇ X) = yes (＇ X , refl)
unshiftSealTyDec (｀ zero) =
  no
    (λ
      { (＇ X , ())
      ; (｀ α , ())
      ; (‵ ι , ())
      ; (★ , ())
      ; (A ⇒ B , ())
      ; (`∀ A , ())
      })
unshiftSealTyDec (｀ (suc α)) = yes (｀ α , refl)
unshiftSealTyDec (‵ ι) = yes (‵ ι , refl)
unshiftSealTyDec ★ = yes (★ , refl)
unshiftSealTyDec (A ⇒ B) with unshiftSealTyDec A | unshiftSealTyDec B
... | yes (A′ , A≡⇑A′) | yes (B′ , B≡⇑B′) =
  yes (A′ ⇒ B′ , cong₂ _⇒_ A≡⇑A′ B≡⇑B′)
... | no ¬A | yes (B′ , B≡⇑B′) =
  no
    (λ
      { (＇ X , ())
      ; (｀ α , ())
      ; (‵ ι , ())
      ; (★ , ())
      ; (A′ ⇒ B″ , refl) → ¬A (A′ , refl)
      ; (`∀ A′ , ())
      })
... | yes (A′ , A≡⇑A′) | no ¬B =
  no
    (λ
      { (＇ X , ())
      ; (｀ α , ())
      ; (‵ ι , ())
      ; (★ , ())
      ; (A″ ⇒ B′ , refl) → ¬B (B′ , refl)
      ; (`∀ A′ , ())
      })
... | no ¬A | no ¬B =
  no
    (λ
      { (＇ X , ())
      ; (｀ α , ())
      ; (‵ ι , ())
      ; (★ , ())
      ; (A′ ⇒ B′ , refl) → ¬A (A′ , refl)
      ; (`∀ A′ , ())
      })
unshiftSealTyDec (`∀ A) with unshiftSealTyDec A
... | yes (A′ , A≡⇑A′) =
  yes (`∀ A′ , cong `∀ A≡⇑A′)
... | no ¬A =
  no
    (λ
      { (＇ X , ())
      ; (｀ α , ())
      ; (‵ ι , ())
      ; (★ , ())
      ; (A′ ⇒ B′ , ())
      ; (`∀ B , refl) → ¬A (B , refl)
      })

infix 4 _≟Ty_
_≟Ty_ : (A B : Ty) → Dec (A ≡ B)
(＇ X) ≟Ty (＇ Y) with X ≟ Y
... | yes eq = yes (cong ＇_ eq)
... | no neq = no (λ { refl → neq refl })
(＇ X) ≟Ty (｀ α) = no (λ ())
(＇ X) ≟Ty (‵ ι) = no (λ ())
(＇ X) ≟Ty ★ = no (λ ())
(＇ X) ≟Ty (B ⇒ C) = no (λ ())
(＇ X) ≟Ty (`∀ B) = no (λ ())

(｀ α) ≟Ty (＇ Y) = no (λ ())
(｀ α) ≟Ty (｀ β) with seal-≟ α β
... | yes eq = yes (cong ｀_ eq)
... | no neq = no (λ { refl → neq refl })
(｀ α) ≟Ty (‵ ι) = no (λ ())
(｀ α) ≟Ty ★ = no (λ ())
(｀ α) ≟Ty (B ⇒ C) = no (λ ())
(｀ α) ≟Ty (`∀ B) = no (λ ())

(‵ ι) ≟Ty (＇ Y) = no (λ ())
(‵ ι) ≟Ty (｀ β) = no (λ ())
(‵ ι) ≟Ty (‵ ι′) with ι ≟Base ι′
... | yes eq = yes (cong ‵_ eq)
... | no neq = no (λ { refl → neq refl })
(‵ ι) ≟Ty ★ = no (λ ())
(‵ ι) ≟Ty (B ⇒ C) = no (λ ())
(‵ ι) ≟Ty (`∀ B) = no (λ ())

★ ≟Ty (＇ Y) = no (λ ())
★ ≟Ty (｀ β) = no (λ ())
★ ≟Ty (‵ ι) = no (λ ())
★ ≟Ty ★ = yes refl
★ ≟Ty (B ⇒ C) = no (λ ())
★ ≟Ty (`∀ B) = no (λ ())

(A ⇒ B) ≟Ty (＇ Y) = no (λ ())
(A ⇒ B) ≟Ty (｀ β) = no (λ ())
(A ⇒ B) ≟Ty (‵ ι) = no (λ ())
(A ⇒ B) ≟Ty ★ = no (λ ())
(A ⇒ B) ≟Ty (C ⇒ D) with A ≟Ty C | B ≟Ty D
... | yes refl | yes refl = yes refl
... | no A≢C | _ = no (λ { refl → A≢C refl })
... | _ | no B≢D = no (λ { refl → B≢D refl })
(A ⇒ B) ≟Ty (`∀ C) = no (λ ())

(`∀ A) ≟Ty (＇ Y) = no (λ ())
(`∀ A) ≟Ty (｀ β) = no (λ ())
(`∀ A) ≟Ty (‵ ι) = no (λ ())
(`∀ A) ≟Ty ★ = no (λ ())
(`∀ A) ≟Ty (C ⇒ D) = no (λ ())
(`∀ A) ≟Ty (`∀ B) with A ≟Ty B
... | yes refl = yes refl
... | no A≢B = no (λ { refl → A≢B refl })

mutual
  up-cast-check′ :
    (Σ : Store) →
    Uniqueˢ Σ →
    (Φ : List Bool) →
    (p : Up) →
    Dec (Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Σ ∣ Φ ⊢ p ⦂ A ⊑ B)
  up-cast-check′ Σ uΣ Φ (tag G) with groundTyDec G
  ... | no ¬g =
      no
        (λ
          { (A , (B , wt-tag g gokΦ)) → ¬g g
          })
  ... | yes g with groundOkDec g Φ
  ...   | no ¬gok =
        no
          (λ
            { (A , (B , wt-tag g′ gokΦ)) →
                ¬gok (ground-ok-cong {g = g′} {g′ = g} gokΦ)
            })
  ...   | yes gokΦ = yes (G , (★ , wt-tag g gokΦ))

  up-cast-check′ Σ uΣ Φ (unseal α) with permMemberDec α Φ | lookupStoreAnyDec Σ α
  ... | no α∉Φ | _ =
      no
        (λ
          { (A , (B , wt-unseal h α∈Φ)) → α∉Φ α∈Φ
          })
  ... | yes α∈Φ | no ¬lookup =
      no
        (λ
          { (A , (B , wt-unseal h α∈Φ′)) → ¬lookup (B , h)
          })
  ... | yes α∈Φ | yes (A , h) =
      yes (｀ α , (A , wt-unseal h α∈Φ))

  up-cast-check′ Σ uΣ Φ (p ↦ q)
      with down-cast-check′ Σ uΣ Φ p | up-cast-check′ Σ uΣ Φ q
  ... | no ¬p | _ =
      no
        (λ
          { (A , (B , wt-↦ hp hq)) → ¬p (_ , (_ , hp))
          })
  ... | yes (A′ , (A , hp)) | no ¬q =
      no
        (λ
          { (A₀ , (B₀ , wt-↦ hp′ hq′)) → ¬q (_ , (_ , hq′))
          })
  ... | yes (A′ , (A , hp)) | yes (B , (B′ , hq)) =
      yes ((A ⇒ B) , ((A′ ⇒ B′) , wt-↦ hp hq))

  up-cast-check′ Σ uΣ Φ (∀ᵖ p) with up-cast-check′ (⟰ᵗ Σ) (unique-⟰ᵗ uΣ) Φ p
  ... | no ¬p =
      no
        (λ
          { (A , (B , wt-∀ hp)) → ¬p (_ , (_ , hp))
          })
  ... | yes (A , (B , hp)) =
      yes (`∀ A , (`∀ B , wt-∀ hp))

  up-cast-check′ Σ uΣ Φ (ν p)
      with up-cast-check′ ((zero , ★) ∷ ⟰ˢ Σ) (unique-ν ★ uΣ) (true ∷ Φ) p
  ... | no ¬p =
      no
        (λ
          { (A , (B , wt-ν hp)) → ¬p (_ , (_ , hp))
          })
  ... | yes (C , (D , hp)) with unshiftSealTyDec D
  ...   | yes (B , D≡⇑B) =
        yes
          (`∀ (closeνSrc zero C) ,
            ( B
            , wt-ν
                (castWt⊑-raw
                  (sym (open-closeνSrc-id C))
                  D≡⇑B
                  hp)
            ))
  ...   | no ¬unshift =
        no
          (λ
            { (A′ , (B′ , wt-ν hp′)) →
                ¬unshift (B′ , proj₂ (wt⊑-unique (unique-ν ★ uΣ) hp hp′))
            })

  up-cast-check′ Σ uΣ Φ (id A) = yes (A , (A , wt-id (wfTySome A)))

  up-cast-check′ Σ uΣ Φ (p ； q)
      with up-cast-check′ Σ uΣ Φ p | up-cast-check′ Σ uΣ Φ q
  ... | no ¬p | _ =
      no
        (λ
          { (A , (B , wt-； hp hq)) → ¬p (_ , (_ , hp))
          })
  ... | yes (A , (B , hp)) | no ¬q =
      no
        (λ
          { (A′ , (C′ , wt-； hp′ hq′)) → ¬q (_ , (_ , hq′))
          })
  ... | yes (A , (B , hp)) | yes (B′ , (C , hq)) with B ≟Ty B′
  ...   | yes refl = yes (A , (C , wt-； hp hq))
  ...   | no B≢B′ =
        no
          (λ
            { (A′ , (C′ , wt-； {B = B₀} hp′ hq′)) →
                let
                  eqB : B ≡ B₀
                  eqB = proj₂ (wt⊑-unique uΣ hp hp′)

                  eqB′ : B′ ≡ B₀
                  eqB′ = proj₁ (wt⊑-unique uΣ hq hq′)
                in
                B≢B′ (trans eqB (sym eqB′))
            })

  down-cast-check′ :
    (Σ : Store) →
    Uniqueˢ Σ →
    (Φ : List Bool) →
    (p : Down) →
    Dec (Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Σ ∣ Φ ⊢ p ⦂ A ⊒ B)
  down-cast-check′ Σ uΣ Φ (untag G ℓ) with groundTyDec G
  ... | no ¬g =
      no
        (λ
          { (A , (B , wt-untag g gokΦ ℓ′)) → ¬g g
          })
  ... | yes g with groundOkDec g Φ
  ...   | no ¬gok =
        no
          (λ
            { (A , (B , wt-untag g′ gokΦ ℓ′)) →
                ¬gok (ground-ok-cong {g = g′} {g′ = g} gokΦ)
            })
  ...   | yes gokΦ = yes (★ , (G , wt-untag g gokΦ ℓ))

  down-cast-check′ Σ uΣ Φ (seal α) with permMemberDec α Φ | lookupStoreAnyDec Σ α
  ... | no α∉Φ | _ =
      no
        (λ
          { (A , (B , wt-seal h α∈Φ)) → α∉Φ α∈Φ
          })
  ... | yes α∈Φ | no ¬lookup =
      no
        (λ
          { (A , (B , wt-seal h α∈Φ′)) → ¬lookup (A , h)
          })
  ... | yes α∈Φ | yes (A , h) =
      yes (A , (｀ α , wt-seal h α∈Φ))

  down-cast-check′ Σ uΣ Φ (p ↦ q)
      with up-cast-check′ Σ uΣ Φ p | down-cast-check′ Σ uΣ Φ q
  ... | no ¬p | _ =
      no
        (λ
          { (A , (B , wt-↦ hp hq)) → ¬p (_ , (_ , hp))
          })
  ... | yes (A′ , (A , hp)) | no ¬q =
      no
        (λ
          { (A₀ , (B₀ , wt-↦ hp′ hq′)) → ¬q (_ , (_ , hq′))
          })
  ... | yes (A′ , (A , hp)) | yes (B , (B′ , hq)) =
      yes ((A ⇒ B) , ((A′ ⇒ B′) , wt-↦ hp hq))

  down-cast-check′ Σ uΣ Φ (∀ᵖ p) with down-cast-check′ (⟰ᵗ Σ) (unique-⟰ᵗ uΣ) Φ p
  ... | no ¬p =
      no
        (λ
          { (A , (B , wt-∀ hp)) → ¬p (_ , (_ , hp))
          })
  ... | yes (A , (B , hp)) =
      yes (`∀ A , (`∀ B , wt-∀ hp))

  down-cast-check′ Σ uΣ Φ (ν p)
      with down-cast-check′ ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) (unique-ν ★ uΣ) (false ∷ Φ) p
  ... | no ¬p =
      no
        (λ
          { (A , (B , wt-ν hp)) → ¬p (_ , (_ , hp))
          })
  ... | yes (C , (D , hp)) with unshiftSealTyDec C
  ...   | yes (B , C≡⇑B) =
        yes
          ( B
          , ( `∀ (closeνSrc zero D)
            , wt-ν
                (castWt⊒-raw
                  C≡⇑B
                  (sym (open-closeνSrc-id D))
                  hp)
            ))
  ...   | no ¬unshift =
        no
          (λ
            { (B′ , (A′ , wt-ν hp′)) →
                ¬unshift (B′ , proj₁ (wt⊒-unique (unique-ν ★ uΣ) hp hp′))
            })

  down-cast-check′ Σ uΣ Φ (id A) = yes (A , (A , wt-id (wfTySome A)))

  down-cast-check′ Σ uΣ Φ (p ； q)
      with down-cast-check′ Σ uΣ Φ p | down-cast-check′ Σ uΣ Φ q
  ... | no ¬p | _ =
      no
        (λ
          { (A , (B , wt-； hp hq)) → ¬p (_ , (_ , hp))
          })
  ... | yes (A , (B , hp)) | no ¬q =
      no
        (λ
          { (A′ , (C′ , wt-； hp′ hq′)) → ¬q (_ , (_ , hq′))
          })
  ... | yes (A , (B , hp)) | yes (B′ , (C , hq)) with B ≟Ty B′
  ...   | yes refl = yes (A , (C , wt-； hp hq))
  ...   | no B≢B′ =
        no
          (λ
            { (A′ , (C′ , wt-； {B = B₀} hp′ hq′)) →
                let
                  eqB : B ≡ B₀
                  eqB = proj₂ (wt⊒-unique uΣ hp hp′)

                  eqB′ : B′ ≡ B₀
                  eqB′ = proj₁ (wt⊒-unique uΣ hq hq′)
                in
                B≢B′ (trans eqB (sym eqB′))
            })

up-cast-check :
  (Σ : Store) →
  (Ψ : SealCtx) →
  Uniqueˢ Σ →
  (p : Up) →
  Dec (Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Σ ∣ every Ψ ⊢ p ⦂ A ⊑ B)
up-cast-check Σ Ψ uΣ p =
  up-cast-check′ Σ uΣ (every Ψ) p

down-cast-check :
  (Σ : Store) →
  (Ψ : SealCtx) →
  Uniqueˢ Σ →
  (p : Down) →
  Dec (Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Σ ∣ every Ψ ⊢ p ⦂ A ⊒ B)
down-cast-check Σ Ψ uΣ p =
  down-cast-check′ Σ uΣ (every Ψ) p

postulate
  cast-to-every-⊑ :
    ∀ {Ψ}{Σ : Store}{Φ : List Bool}{p : Up}{A B : Ty} →
    Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    Σ ∣ every Ψ ⊢ p ⦂ A ⊑ B

  cast-to-every-⊒ :
    ∀ {Ψ}{Σ : Store}{Φ : List Bool}{p : Down}{A B : Ty} →
    Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    Σ ∣ every Ψ ⊢ p ⦂ A ⊒ B

------------------------------------------------------------------------
-- Small inversion helpers
------------------------------------------------------------------------

domTy : Ty → Ty
domTy (A ⇒ B) = A
domTy (＇ X) = ＇ X
domTy (｀ α) = ｀ α
domTy (‵ ι) = ‵ ι
domTy ★ = ★
domTy (`∀ A) = `∀ A

nonArrow-≠⇒ :
  ∀ {A B C : Ty} →
  NonArrow A →
  A ≡ (B ⇒ C) →
  ⊥
nonArrow-≠⇒ (na-var X) ()
nonArrow-≠⇒ (na-seal α) ()
nonArrow-≠⇒ (na-base ι) ()
nonArrow-≠⇒ na-star ()
nonArrow-≠⇒ (na-all A) ()

data NonForall : Ty → Set where
  nf-var : ∀ X → NonForall (＇ X)
  nf-seal : ∀ α → NonForall (｀ α)
  nf-base : ∀ ι → NonForall (‵ ι)
  nf-star : NonForall ★
  nf-⇒ : ∀ A B → NonForall (A ⇒ B)

nonForall-≠∀ :
  ∀ {A B : Ty} →
  NonForall A →
  A ≡ `∀ B →
  ⊥
nonForall-≠∀ (nf-var X) ()
nonForall-≠∀ (nf-seal α) ()
nonForall-≠∀ (nf-base ι) ()
nonForall-≠∀ nf-star ()
nonForall-≠∀ (nf-⇒ A B) ()

------------------------------------------------------------------------
-- Decidable helpers used by decidable typing
------------------------------------------------------------------------

lookupAnyDec : (Γ : Ctx) → (x : Var) → Dec (LookupAny Γ x)
lookupAnyDec [] x = no (λ { (A , ()) })
lookupAnyDec (A ∷ Γ) zero = yes (A , Z)
lookupAnyDec (A ∷ Γ) (suc x) with lookupAnyDec Γ x
... | yes (B , h) = yes (B , S h)
... | no ¬lookup = no (λ { (B , S h) → ¬lookup (B , h) })

wfTyDec : (Δ : TyCtx) → (Ψ : SealCtx) → (A : Ty) → Dec (WfTy Δ Ψ A)
wfTyDec Δ Ψ (＇ X) with X <? Δ
... | yes X<Δ = yes (wfVar X<Δ)
... | no X≮Δ = no (λ { (wfVar X<Δ) → X≮Δ X<Δ })
wfTyDec Δ Ψ (｀ α) with α <? Ψ
... | yes α<Ψ = yes (wfSeal α<Ψ)
... | no α≮Ψ = no (λ { (wfSeal α<Ψ) → α≮Ψ α<Ψ })
wfTyDec Δ Ψ (‵ ι) = yes wfBase
wfTyDec Δ Ψ ★ = yes wf★
wfTyDec Δ Ψ (A ⇒ B) with wfTyDec Δ Ψ A | wfTyDec Δ Ψ B
... | yes hA | yes hB = yes (wf⇒ hA hB)
... | no ¬hA | _ = no (λ { (wf⇒ hA hB) → ¬hA hA })
... | _ | no ¬hB = no (λ { (wf⇒ hA hB) → ¬hB hB })
wfTyDec Δ Ψ (`∀ A) with wfTyDec (suc Δ) Ψ A
... | yes hA = yes (wf∀ hA)
... | no ¬hA = no (λ { (wf∀ hA) → ¬hA hA })

------------------------------------------------------------------------
-- Decidable type checking
------------------------------------------------------------------------

type-check-app-from :
  ∀ {Δ Ψ Σ Γ L M} →
  (wfΣ : StoreWf Δ Ψ Σ) →
  (A : Ty) →
  (L:A : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L ⦂ A) →
  (bfL : BlameFree L) →
  (B : Ty) →
  (M:B : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ B) →
  (bfM : BlameFree M) →
  Dec (HasSomeTypeBF Δ Ψ Σ Γ (L · M))
type-check-app-from wfΣ (＇ X) L:X bfL B M:B bfM =
  no
    (λ
      { ((C , ⊢· {A = A′} L:fun M:A′) , bf-· bfL′ bfM′) →
          let eq : ＇ X ≡ (A′ ⇒ C)
              eq = type-unique-blamefree (storeWf-unique wfΣ) bfL L:X L:fun
          in nonArrow-≠⇒ (na-var X) eq
      })
type-check-app-from wfΣ (｀ α) L:α bfL B M:B bfM =
  no
    (λ
      { ((C , ⊢· {A = A′} L:fun M:A′) , bf-· bfL′ bfM′) →
          let eq : ｀ α ≡ (A′ ⇒ C)
              eq = type-unique-blamefree (storeWf-unique wfΣ) bfL L:α L:fun
          in nonArrow-≠⇒ (na-seal α) eq
      })
type-check-app-from wfΣ (‵ ι) L:ι bfL B M:B bfM =
  no
    (λ
      { ((C , ⊢· {A = A′} L:fun M:A′) , bf-· bfL′ bfM′) →
          let eq : ‵ ι ≡ (A′ ⇒ C)
              eq = type-unique-blamefree (storeWf-unique wfΣ) bfL L:ι L:fun
          in nonArrow-≠⇒ (na-base ι) eq
      })
type-check-app-from wfΣ ★ L:★ bfL B M:B bfM =
  no
    (λ
      { ((C , ⊢· {A = A′} L:fun M:A′) , bf-· bfL′ bfM′) →
          let eq : ★ ≡ (A′ ⇒ C)
              eq = type-unique-blamefree (storeWf-unique wfΣ) bfL L:★ L:fun
          in nonArrow-≠⇒ na-star eq
      })
type-check-app-from wfΣ (A₁ ⇒ B₁) L:AB bfL B M:B bfM with A₁ ≟Ty B
... | yes refl = yes ((B₁ , ⊢· L:AB M:B) , bf-· bfL bfM)
... | no A₁≢B =
  no
    (λ
      { ((C , ⊢· {A = A′} L:AC M:A′) , bf-· bfL′ bfM′) →
          let eqFun : (A₁ ⇒ B₁) ≡ (A′ ⇒ C)
              eqFun =
                type-unique-blamefree
                  (storeWf-unique wfΣ)
                  bfL
                  L:AB
                  L:AC
          in
          let eqArgL : A₁ ≡ A′
              eqArgL = cong domTy eqFun
          in
          let eqArgM : A′ ≡ B
              eqArgM =
                type-unique-blamefree
                  (storeWf-unique wfΣ)
                  bfM
                  M:A′
                  M:B
          in
          A₁≢B (trans eqArgL eqArgM)
      })
type-check-app-from wfΣ (`∀ A′) L:∀ bfL B M:B bfM =
  no
    (λ
      { ((C , ⊢· {A = A″} L:fun M:A″) , bf-· bfL′ bfM′) →
          let eq : `∀ A′ ≡ (A″ ⇒ C)
              eq = type-unique-blamefree (storeWf-unique wfΣ) bfL L:∀ L:fun
          in nonArrow-≠⇒ (na-all A′) eq
      })

type-check :
  (Δ : TyCtx) →
  (Ψ : SealCtx) →
  (Σ : Store) →
  (Γ : Ctx) →
  (wfΓ : CtxWf Δ Ψ Γ) →
  (wfΣ : StoreWf Δ Ψ Σ) →
  (M : Term) →
  Dec (HasSomeTypeBF Δ Ψ Σ Γ M)

type-check Δ Ψ Σ Γ wfΓ wfΣ (` x) with lookupAnyDec Γ x
... | yes (A , x:A) = yes ((A , ⊢` x:A) , bf-`)
... | no ¬x = no (λ { ((A , ⊢` x:A) , bf-`) → ¬x (A , x:A) })

type-check Δ Ψ Σ Γ wfΓ wfΣ (ƛ A ⇒ N) with wfTyDec Δ Ψ A
... | no ¬wfA =
  no
    (λ
      { ((B , ⊢ƛ wfA N:B) , bf-ƛ bfN) → ¬wfA wfA
      })
... | yes wfA
    with type-check Δ Ψ Σ (A ∷ Γ) (ctxWf-∷ wfA wfΓ) wfΣ N
... | yes ((B , N:B) , bfN) =
  yes ((A ⇒ B , ⊢ƛ wfA N:B) , bf-ƛ bfN)
... | no ¬N =
  no
    (λ
      { ((A ⇒ C , ⊢ƛ wfA′ N:C) , bf-ƛ bfN′) → ¬N ((C , N:C) , bfN′)
      })

type-check Δ Ψ Σ Γ wfΓ wfΣ (L · M)
    with type-check Δ Ψ Σ Γ wfΓ wfΣ L | type-check Δ Ψ Σ Γ wfΓ wfΣ M
... | yes ((A , L:A) , bfL) | yes ((B , M:B) , bfM) =
  type-check-app-from wfΣ A L:A bfL B M:B bfM
type-check Δ Ψ Σ Γ wfΓ wfΣ (L · M) | no ¬L | _ =
  no
    (λ
      { ((C , ⊢· {A = A′} L:AC M:A′) , bf-· bfL bfM) →
          ¬L ((A′ ⇒ C , L:AC) , bfL)
      })
type-check Δ Ψ Σ Γ wfΓ wfΣ (L · M) | yes ((A , L:A) , bfL) | no ¬M =
  no
    (λ
      { ((C , ⊢· {A = A′} L:AC M:A′) , bf-· bfL′ bfM) → ¬M ((A′ , M:A′) , bfM)
      })

type-check Δ Ψ Σ Γ wfΓ wfΣ (Λ M)
    with type-check (suc Δ) Ψ (⟰ᵗ Σ) (⤊ᵗ Γ) (ctxWf-⤊ᵗ wfΓ) (storeWf-⟰ᵗ wfΣ) M
... | yes ((A , M:A) , bfM) = yes ((`∀ A , ⊢Λ M:A) , bf-Λ bfM)
... | no ¬M =
  no
    (λ
      { ((`∀ B , ⊢Λ M:B) , bf-Λ bfM) → ¬M ((B , M:B) , bfM)
      })

type-check Δ Ψ Σ Γ wfΓ wfΣ (M ⦂∀ B [ T ]) with type-check Δ Ψ Σ Γ wfΓ wfΣ M
... | no ¬M =
  no
    (λ
      { ((C , ⊢• M:∀ wfT) , bf-⦂∀ bfM) → ¬M ((`∀ _ , M:∀) , bfM)
      })
... | yes ((＇ X , M:X) , bfM) =
  no
    (λ
      { ((C , ⊢• M:∀ wfT) , bf-⦂∀ bfM′) →
          let eq : ＇ X ≡ `∀ _
              eq = type-unique-blamefree (storeWf-unique wfΣ) bfM M:X M:∀
          in nonForall-≠∀ (nf-var X) eq
      })
... | yes ((｀ α , M:α) , bfM) =
  no
    (λ
      { ((C , ⊢• M:∀ wfT) , bf-⦂∀ bfM′) →
          let eq : ｀ α ≡ `∀ _
              eq = type-unique-blamefree (storeWf-unique wfΣ) bfM M:α M:∀
          in nonForall-≠∀ (nf-seal α) eq
      })
... | yes ((‵ ι , M:ι) , bfM) =
  no
    (λ
      { ((C , ⊢• M:∀ wfT) , bf-⦂∀ bfM′) →
          let eq : ‵ ι ≡ `∀ _
              eq = type-unique-blamefree (storeWf-unique wfΣ) bfM M:ι M:∀
          in nonForall-≠∀ (nf-base ι) eq
      })
... | yes ((★ , M:★) , bfM) =
  no
    (λ
      { ((C , ⊢• M:∀ wfT) , bf-⦂∀ bfM′) →
          let eq : ★ ≡ `∀ _
              eq = type-unique-blamefree (storeWf-unique wfΣ) bfM M:★ M:∀
          in nonForall-≠∀ nf-star eq
      })
... | yes ((A ⇒ B′ , M:AB) , bfM) =
  no
    (λ
      { ((C , ⊢• M:∀ wfT) , bf-⦂∀ bfM′) →
          let eq : (A ⇒ B′) ≡ `∀ _
              eq = type-unique-blamefree (storeWf-unique wfΣ) bfM M:AB M:∀
          in nonForall-≠∀ (nf-⇒ A B′) eq
      })
... | yes ((`∀ B′ , M:∀B′) , bfM) with B′ ≟Ty B | wfTyDec Δ Ψ T
...   | no B′≢B | _ =
      no
        (λ
          { ((C , ⊢• M:∀B wfT) , bf-⦂∀ bfM′) →
              let eqAll : `∀ B′ ≡ `∀ B
                  eqAll = type-unique-blamefree (storeWf-unique wfΣ) bfM M:∀B′ M:∀B
              in
              B′≢B (cong forallBodyTy eqAll)
          })
...   | yes refl | no ¬wfT =
      no
        (λ
          { ((C , ⊢• M:∀B wfT) , bf-⦂∀ bfM′) → ¬wfT wfT
          })
...   | yes refl | yes wfT =
      yes ((B [ T ]ᵗ , ⊢• M:∀B′ wfT) , bf-⦂∀ bfM)

type-check Δ Ψ Σ Γ wfΓ wfΣ ($ κ) = yes ((constTy κ , ⊢$ κ) , bf-$)

type-check Δ Ψ Σ Γ wfΓ wfΣ (L ⊕[ op ] M)
    with type-check Δ Ψ Σ Γ wfΓ wfΣ L | type-check Δ Ψ Σ Γ wfΓ wfΣ M
... | yes ((A , L:A) , bfL) | yes ((B , M:B) , bfM) with A ≟Ty (‵ `ℕ) | B ≟Ty (‵ `ℕ)
...   | yes refl | yes refl = yes (((‵ `ℕ) , ⊢⊕ L:A op M:B) , bf-⊕ bfL bfM)
...   | no A≢ℕ | _ =
      no
        (λ
          { ((C , ⊢⊕ L:ℕ op′ M:ℕ) , bf-⊕ bfL′ bfM′) →
              let eqA : A ≡ ‵ `ℕ
                  eqA =
                    type-unique-blamefree
                      (storeWf-unique wfΣ)
                      bfL
                      L:A
                      L:ℕ
              in
              A≢ℕ eqA
          })
...   | _ | no B≢ℕ =
      no
        (λ
          { ((C , ⊢⊕ L:ℕ op′ M:ℕ) , bf-⊕ bfL′ bfM′) →
              let eqB : B ≡ ‵ `ℕ
                  eqB =
                    type-unique-blamefree
                      (storeWf-unique wfΣ)
                      bfM
                      M:B
                      M:ℕ
              in
              B≢ℕ eqB
          })
type-check Δ Ψ Σ Γ wfΓ wfΣ (L ⊕[ op ] M) | no ¬L | _ =
  no
    (λ
      { ((C , ⊢⊕ L:ℕ op′ M:ℕ) , bf-⊕ bfL bfM) → ¬L (((‵ `ℕ) , L:ℕ) , bfL)
      })
type-check Δ Ψ Σ Γ wfΓ wfΣ (L ⊕[ op ] M) | yes ((A , L:A) , bfL) | no ¬M =
  no
    (λ
      { ((C , ⊢⊕ L:ℕ op′ M:ℕ) , bf-⊕ bfL′ bfM) → ¬M (((‵ `ℕ) , M:ℕ) , bfM)
      })

type-check Δ Ψ Σ Γ wfΓ wfΣ (M up p) with type-check Δ Ψ Σ Γ wfΓ wfΣ M
... | no ¬M =
  no
    (λ
      { ((B , ⊢up {A = A′} Φ M:A′ hp) , bf-up bfM) → ¬M ((A′ , M:A′) , bfM)
      })
... | yes ((A , M:A) , bfM) with up-cast-check Σ Ψ (storeWf-unique wfΣ) p
...   | no ¬p =
      no
        (λ
          { ((B , ⊢up {A = A′} Φ M:A′ hp) , bf-up bfM′) →
              ¬p (A′ , (B , cast-to-every-⊑ {Ψ = Ψ} hp))
          })
...   | yes (A′ , (B , hp)) with A′ ≟Ty A
...     | yes refl = yes ((B , ⊢up (every Ψ) M:A hp) , bf-up bfM)
...     | no A′≢A =
        no
          (λ
            { ((C , ⊢up {A = A″} Φ M:A″ hp′) , bf-up bfM′) →
                let eqCastA : A′ ≡ A″
                    eqCastA = proj₁ (wt⊑-unique (storeWf-unique wfΣ) hp hp′)
                in
                let eqTermA : A″ ≡ A
                    eqTermA =
                      type-unique-blamefree
                        (storeWf-unique wfΣ)
                        bfM
                        M:A″
                        M:A
                in
                A′≢A (trans eqCastA eqTermA)
            })

type-check Δ Ψ Σ Γ wfΓ wfΣ (M down p) with type-check Δ Ψ Σ Γ wfΓ wfΣ M
... | no ¬M =
  no
    (λ
      { ((B , ⊢down {A = A′} Φ M:A′ hp) , bf-down bfM) → ¬M ((A′ , M:A′) , bfM)
      })
... | yes ((A , M:A) , bfM) with down-cast-check Σ Ψ (storeWf-unique wfΣ) p
...   | no ¬p =
      no
        (λ
          { ((B , ⊢down {A = A′} Φ M:A′ hp) , bf-down bfM′) →
              ¬p (A′ , (B , cast-to-every-⊒ {Ψ = Ψ} hp))
          })
...   | yes (A′ , (B , hp)) with A′ ≟Ty A
...     | yes refl = yes ((B , ⊢down (every Ψ) M:A hp) , bf-down bfM)
...     | no A′≢A =
        no
          (λ
            { ((C , ⊢down {A = A″} Φ M:A″ hp′) , bf-down bfM′) →
                let eqCastA : A′ ≡ A″
                    eqCastA = proj₁ (wt⊒-unique (storeWf-unique wfΣ) hp hp′)
                in
                let eqTermA : A″ ≡ A
                    eqTermA =
                      type-unique-blamefree
                        (storeWf-unique wfΣ)
                        bfM
                        M:A″
                        M:A
                in
                A′≢A (trans eqCastA eqTermA)
            })

type-check Δ Ψ Σ Γ wfΓ wfΣ (blame ℓ) =
  no (λ { ((A , M:A) , ()) })

------------------------------------------------------------------------
-- Type check against an expected type
------------------------------------------------------------------------

type-check-expect :
  (Δ : TyCtx) →
  (Ψ : SealCtx) →
  (Σ : Store) →
  (Γ : Ctx) →
  (wfΓ : CtxWf Δ Ψ Γ) →
  (wfΣ : StoreWf Δ Ψ Σ) →
  (M : Term) →
  (A : Ty) →
  Dec ((Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A) × BlameFree M)
type-check-expect Δ Ψ Σ Γ wfΓ wfΣ M A with type-check Δ Ψ Σ Γ wfΓ wfΣ M
... | no ¬M =
  no
    (λ
      { (M:A , bfM) →
          ¬M ((A , M:A) , bfM)
      })
... | yes ((B , M:B) , bfM) with B ≟Ty A
...   | yes refl = yes (M:B , bfM)
...   | no B≢A =
      no
        (λ
          { (M:A , bfM′) →
              let eq : B ≡ A
                  eq =
                    type-unique-blamefree
                      (storeWf-unique wfΣ)
                      bfM
                      M:B
                      M:A
              in
              B≢A eq
          })
