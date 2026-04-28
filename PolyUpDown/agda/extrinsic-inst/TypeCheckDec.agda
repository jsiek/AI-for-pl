module TypeCheckDec where

-- File Charter:
--   * Decidable type check of raw terms.

open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; z<s; s<s; _≟_; _⊔_)
open import Data.Nat.Properties
  using (_<?_; <-≤-trans; ≤-<-trans; m≤m⊔n; m≤n⊔m; n≤1+n)
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

upValue? : (p : Up) → Dec (UpValue p)
upValue? (tag G) = yes tag
upValue? (unseal α) = no (λ ())
upValue? (p ↦ q) = yes _↦_
upValue? (∀ᵖ p) = yes ∀ᵖ
upValue? (ν p) = no (λ ())
upValue? (id A) = no (λ ())
upValue? (p ； q) = no (λ ())

downValue? : (p : Down) → Dec (DownValue p)
downValue? (untag G ℓ) = no (λ ())
downValue? (seal α) = yes seal
downValue? (p ↦ q) = yes _↦_
downValue? (∀ᵖ p) = yes ∀ᵖ
downValue? (ν p) = yes ν_
downValue? (id A) = no (λ ())
downValue? (p ； q) = no (λ ())

value? : (M : Term) → Dec (Value M)
value? (` x) = no (λ ())
value? (ƛ A ⇒ M) = yes (ƛ A ⇒ M)
value? (L · M) = no (λ ())
value? (Λ M) = yes (Λ M)
value? (M ⦂∀ B [ T ]) = no (λ ())
value? ($ κ) = yes ($ κ)
value? (L ⊕[ op ] M) = no (λ ())
value? (M up p) with value? M | upValue? p
... | yes vM | yes vp = yes (vM up vp)
... | no ¬vM | _ = no (λ { (vM up vp) → ¬vM vM })
... | yes vM | no ¬vp = no (λ { (vM up vp) → ¬vp vp })
value? (M down p) with value? M | downValue? p
... | yes vM | yes vp = yes (vM down vp)
... | no ¬vM | _ = no (λ { (vM down vp) → ¬vM vM })
... | yes vM | no ¬vp = no (λ { (vM down vp) → ¬vp vp })
value? (blame ℓ) = no (λ ())

LookupAny : Ctx → Var → Set
LookupAny Γ x = Σ[ A ∈ Ty ] Γ ∋ x ⦂ A

data NonArrow : Ty → Set where
  na-var : ∀ X → NonArrow (＇ X)
  na-seal : ∀ α → NonArrow (｀ α)
  na-base : ∀ ι → NonArrow (‵ ι)
  na-star : NonArrow ★
  na-all : ∀ A → NonArrow (`∀ A)

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
    ∀ {Δ Ψ Σ Φ Φ′ A A′ B B′} {p : Up} →
    Uniqueˢ Σ →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    Δ ∣ Ψ ∣ Σ ∣ Φ′ ⊢ p ⦂ A′ ⊑ B′ →
    (A ≡ A′) × (B ≡ B′)
  wt⊑-unique uΣ (wt-tag g gokΞ) (wt-tag g′ gokΞ′) = refl , refl
  wt⊑-unique uΣ (wt-unseal h α∈Φ) (wt-unseal h′ α∈Φ′) =
    refl , lookup-unique uΣ h h′
  wt⊑-unique uΣ (wt-unseal h α∈Φ) (wt-unseal★ h′ α∈Φ′) =
    refl , lookup-unique uΣ h h′
  wt⊑-unique uΣ (wt-unseal★ h α∈Φ) (wt-unseal h′ α∈Φ′) =
    refl , lookup-unique uΣ h h′
  wt⊑-unique uΣ (wt-unseal★ h α∈Φ) (wt-unseal★ h′ α∈Φ′) = refl , refl
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
    ∀ {Δ Ψ Σ Φ Φ′ A A′ B B′} {p : Down} →
    Uniqueˢ Σ →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    Δ ∣ Ψ ∣ Σ ∣ Φ′ ⊢ p ⦂ A′ ⊒ B′ →
    (A ≡ A′) × (B ≡ B′)
  wt⊒-unique uΣ (wt-untag g gokΞ ℓ) (wt-untag g′ gokΞ′ ℓ′) = refl , refl
  wt⊒-unique uΣ (wt-seal h α∈Φ) (wt-seal h′ α∈Φ′) =
    lookup-unique uΣ h h′ , refl
  wt⊒-unique uΣ (wt-seal h α∈Φ) (wt-seal★ h′ α∈Φ′) =
    lookup-unique uΣ h h′ , refl
  wt⊒-unique uΣ (wt-seal★ h α∈Φ) (wt-seal h′ α∈Φ′) =
    lookup-unique uΣ h h′ , refl
  wt⊒-unique uΣ (wt-seal★ h α∈Φ) (wt-seal★ h′ α∈Φ′) = refl , refl
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
type-unique-blamefree uΣ (bf-Λ bfM) (⊢Λ vM M:A) (⊢Λ vM′ M:B) =
  cong `∀ (type-unique-blamefree (unique-⟰ᵗ uΣ) bfM M:A M:B)
type-unique-blamefree uΣ (bf-⦂∀ bfM)
  (⊢• {B = B} {T = T} M:∀B wfB wfT)
  (⊢• {B = B′} {T = T′} M:∀B′ wfB′ wfT′) = refl
type-unique-blamefree uΣ bf-$ (⊢$ κ) (⊢$ κ′) = refl
type-unique-blamefree uΣ (bf-⊕ bfL bfM) (⊢⊕ L:ℕ op M:ℕ) (⊢⊕ L:ℕ′ op′ M:ℕ′) = refl
type-unique-blamefree uΣ (bf-up bfM) (⊢up Φ lenΦ M:A hp) (⊢up Φ′ lenΦ′ M:A′ hp′) =
  proj₂ (wt⊑-unique uΣ hp hp′)
type-unique-blamefree uΣ (bf-down bfM) (⊢down Φ lenΦ M:A hp) (⊢down Φ′ lenΦ′ M:A′ hp′) =
  proj₂ (wt⊒-unique uΣ hp hp′)

------------------------------------------------------------------------
-- Decidable cast typing
------------------------------------------------------------------------

permMemberDec : (α : Seal) → (P : List CastPerm) → Dec (α ∈ P)
permMemberDec α [] = no (λ ())
permMemberDec zero (conv ∷ P) = yes here-conv
permMemberDec zero (cast-seal ∷ P) = yes here-seal
permMemberDec zero (cast-tag ∷ P) = no (λ ())
permMemberDec (suc α) (b ∷ P) with permMemberDec α P
... | yes h = yes (there h)
... | no ¬h = no (λ { (there h) → ¬h h })

permConvMemberDec : (α : Seal) → (P : List CastPerm) → Dec (α ∈conv P)
permConvMemberDec α [] = no (λ ())
permConvMemberDec zero (conv ∷ P) = yes here-conv-only
permConvMemberDec zero (cast-seal ∷ P) = no (λ ())
permConvMemberDec zero (cast-tag ∷ P) = no (λ ())
permConvMemberDec (suc α) (b ∷ P) with permConvMemberDec α P
... | yes h = yes (there-conv h)
... | no ¬h = no (λ { (there-conv h) → ¬h h })

permCastMemberDec : (α : Seal) → (P : List CastPerm) → Dec (α ∈cast P)
permCastMemberDec α [] = no (λ ())
permCastMemberDec zero (conv ∷ P) = no (λ ())
permCastMemberDec zero (cast-seal ∷ P) = yes here-cast-only
permCastMemberDec zero (cast-tag ∷ P) = no (λ ())
permCastMemberDec (suc α) (b ∷ P) with permCastMemberDec α P
... | yes h = yes (there-cast h)
... | no ¬h = no (λ { (there-cast h) → ¬h h })

permTagMemberDec : (α : Seal) → (P : List CastPerm) → Dec (α ∈tag P)
permTagMemberDec α [] = no (λ ())
permTagMemberDec zero (conv ∷ P) = no (λ ())
permTagMemberDec zero (cast-seal ∷ P) = no (λ ())
permTagMemberDec zero (cast-tag ∷ P) = yes here-tag-only
permTagMemberDec (suc α) (b ∷ P) with permTagMemberDec α P
... | yes h = yes (there-tag h)
... | no ¬h = no (λ { (there-tag h) → ¬h h })

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
  (Φ : List CastPerm) →
  Dec (⊢ g ok Φ)
groundOkDec (｀ α) Φ with permTagMemberDec α Φ
... | yes α∈Φ = yes α∈Φ
... | no α∉Φ = no (λ α∈tag → α∉Φ α∈tag)
groundOkDec (‵ ι) Φ = yes tt
groundOkDec ★⇒★ Φ = yes tt

ground-ok-cong :
  ∀ {G : Ty} {Φ : List CastPerm} {g g′ : Ground G} →
  ⊢ g ok Φ →
  ⊢ g′ ok Φ
ground-ok-cong {g = ｀ α} {g′ = ｀ .α} gok = gok
ground-ok-cong {g = ‵ ι} {g′ = ‵ .ι} gok = gok
ground-ok-cong {g = ★⇒★} {g′ = ★⇒★} gok = gok

lookup-★-contra :
  ∀ {Σ : Store}{α : Seal}{A : Ty} →
  Uniqueˢ Σ →
  Σ ∋ˢ α ⦂ A →
  Σ ∋ˢ α ⦂ ★ →
  A ≡ ★
lookup-★-contra uΣ hA h★ =
  trans (sym (lookupTyˢ-lookup uΣ hA)) (lookupTyˢ-lookup uΣ h★)

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

mutual
  up-cast-check′ :
    (Δ : TyCtx) →
    (Ψ : SealCtx) →
    (Σ : Store) →
    StoreWf Δ Ψ Σ →
    (Φ : List CastPerm) →
    (p : Up) →
    Dec
      (Σ[ A ∈ Ty ] Σ[ B ∈ Ty ]
        Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B)
  up-cast-check′ Δ Ψ Σ wfΣ Φ (tag G) with groundTyDec G
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

  up-cast-check′ Δ Ψ Σ wfΣ Φ (unseal α) with lookupStoreAnyDec Σ α
  ... | no ¬lookup =
      no
        (λ
          { (A , (B , wt-unseal h α∈Φ′)) → ¬lookup (B , h)
          ; (A , (B , wt-unseal★ h α∈Φ′)) → ¬lookup (★ , h)
          })
  ... | yes (A , h) with A ≟Ty ★ | permConvMemberDec α Φ | permCastMemberDec α Φ
  ...   | yes refl | yes α∈conv | _ = yes (｀ α , (★ , wt-unseal h α∈conv))
  ...   | yes refl | no α∉conv | yes α∈cast = yes (｀ α , (★ , wt-unseal★ h α∈cast))
  ...   | yes refl | no α∉conv | no α∉cast =
        no
          (λ
            { (A′ , (B′ , wt-unseal h′ α∈conv)) → α∉conv α∈conv
            ; (A′ , (B′ , wt-unseal★ h′ α∈cast)) → α∉cast α∈cast
            })
  ...   | no A≢★ | yes α∈conv | _ = yes (｀ α , (A , wt-unseal h α∈conv))
  ...   | no A≢★ | no α∉conv | yes α∈cast =
        no
          (λ
            { (A′ , (B′ , wt-unseal h′ α∈conv)) → α∉conv α∈conv
            ; (A′ , (★ , wt-unseal★ h′ α∈cast′)) →
                A≢★ (lookup-★-contra (storeWf-unique wfΣ) h h′)
            })
  ...   | no A≢★ | no α∉conv | no α∉cast =
        no
          (λ
            { (A′ , (B′ , wt-unseal h′ α∈conv)) → α∉conv α∈conv
            ; (A′ , (★ , wt-unseal★ h′ α∈cast′)) →
                A≢★ (lookup-★-contra (storeWf-unique wfΣ) h h′)
            })

  up-cast-check′ Δ Ψ Σ wfΣ Φ (p ↦ q)
      with down-cast-check′ Δ Ψ Σ wfΣ Φ p |
           up-cast-check′ Δ Ψ Σ wfΣ Φ q
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

  up-cast-check′ Δ Ψ Σ wfΣ Φ (∀ᵖ p)
      with up-cast-check′ (suc Δ) Ψ (⟰ᵗ Σ) (storeWf-⟰ᵗ wfΣ) Φ p
  ... | no ¬p =
      no
        (λ
          { (A , (B , wt-∀ hp)) → ¬p (_ , (_ , hp))
          })
  ... | yes (A , (B , hp)) =
      yes (`∀ A , (`∀ B , wt-∀ hp))

  up-cast-check′ Δ Ψ Σ wfΣ Φ (ν p)
      with up-cast-check′ Δ (suc Ψ) ((zero , ★) ∷ ⟰ˢ Σ)
             (storeWf-ν-ext wf★ wfΣ) (cast-seal ∷ Φ) p
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
                ¬unshift
                  (B′ ,
                   proj₂
                     (wt⊑-unique
                       (storeWf-unique (storeWf-ν-ext wf★ wfΣ))
                       hp hp′))
            })

  up-cast-check′ Δ Ψ Σ wfΣ Φ (id A) with wfTyDec Δ Ψ A
  ... | yes wfA = yes (A , (A , wt-id wfA))
  ... | no ¬wfA =
      no
        (λ
          { (.A , (.A , wt-id wfA)) → ¬wfA wfA
          })

  up-cast-check′ Δ Ψ Σ wfΣ Φ (p ； q)
      with up-cast-check′ Δ Ψ Σ wfΣ Φ p |
           up-cast-check′ Δ Ψ Σ wfΣ Φ q
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
                  eqB = proj₂ (wt⊑-unique (storeWf-unique wfΣ) hp hp′)

                  eqB′ : B′ ≡ B₀
                  eqB′ = proj₁ (wt⊑-unique (storeWf-unique wfΣ) hq hq′)
                in
                B≢B′ (trans eqB (sym eqB′))
            })

  down-cast-check′ :
    (Δ : TyCtx) →
    (Ψ : SealCtx) →
    (Σ : Store) →
    StoreWf Δ Ψ Σ →
    (Φ : List CastPerm) →
    (p : Down) →
    Dec
      (Σ[ A ∈ Ty ] Σ[ B ∈ Ty ]
        Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B)
  down-cast-check′ Δ Ψ Σ wfΣ Φ (untag G ℓ) with groundTyDec G
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

  down-cast-check′ Δ Ψ Σ wfΣ Φ (seal α) with lookupStoreAnyDec Σ α
  ... | no ¬lookup =
      no
        (λ
          { (A , (B , wt-seal h α∈Φ′)) → ¬lookup (A , h)
          ; (A , (B , wt-seal★ h α∈Φ′)) → ¬lookup (★ , h)
          })
  ... | yes (A , h) with A ≟Ty ★ | permConvMemberDec α Φ | permCastMemberDec α Φ
  ...   | yes refl | yes α∈conv | _ = yes (★ , (｀ α , wt-seal h α∈conv))
  ...   | yes refl | no α∉conv | yes α∈cast = yes (★ , (｀ α , wt-seal★ h α∈cast))
  ...   | yes refl | no α∉conv | no α∉cast =
        no
          (λ
            { (A′ , (B′ , wt-seal h′ α∈conv)) → α∉conv α∈conv
            ; (A′ , (B′ , wt-seal★ h′ α∈cast)) → α∉cast α∈cast
            })
  ...   | no A≢★ | yes α∈conv | _ = yes (A , (｀ α , wt-seal h α∈conv))
  ...   | no A≢★ | no α∉conv | yes α∈cast =
        no
          (λ
            { (A′ , (B′ , wt-seal h′ α∈conv)) → α∉conv α∈conv
            ; (A′ , (｀ α , wt-seal★ h′ α∈cast′)) →
                A≢★ (lookup-★-contra (storeWf-unique wfΣ) h h′)
            })
  ...   | no A≢★ | no α∉conv | no α∉cast =
        no
          (λ
            { (A′ , (B′ , wt-seal h′ α∈conv)) → α∉conv α∈conv
            ; (A′ , (｀ α , wt-seal★ h′ α∈cast′)) →
                A≢★ (lookup-★-contra (storeWf-unique wfΣ) h h′)
            })

  down-cast-check′ Δ Ψ Σ wfΣ Φ (p ↦ q)
      with up-cast-check′ Δ Ψ Σ wfΣ Φ p |
           down-cast-check′ Δ Ψ Σ wfΣ Φ q
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

  down-cast-check′ Δ Ψ Σ wfΣ Φ (∀ᵖ p)
      with down-cast-check′ (suc Δ) Ψ (⟰ᵗ Σ) (storeWf-⟰ᵗ wfΣ) Φ p
  ... | no ¬p =
      no
        (λ
          { (A , (B , wt-∀ hp)) → ¬p (_ , (_ , hp))
          })
  ... | yes (A , (B , hp)) =
      yes (`∀ A , (`∀ B , wt-∀ hp))

  down-cast-check′ Δ Ψ Σ wfΣ Φ (ν p)
      with down-cast-check′ Δ (suc Ψ) ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ)
             (storeWf-ν-ext wf★ wfΣ) (cast-tag ∷ Φ) p
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
                ¬unshift
                  (B′ ,
                   proj₁
                     (wt⊒-unique
                       (storeWf-unique (storeWf-ν-ext wf★ wfΣ))
                       hp hp′))
            })

  down-cast-check′ Δ Ψ Σ wfΣ Φ (id A) with wfTyDec Δ Ψ A
  ... | yes wfA = yes (A , (A , wt-id wfA))
  ... | no ¬wfA =
      no
        (λ
          { (.A , (.A , wt-id wfA)) → ¬wfA wfA
          })

  down-cast-check′ Δ Ψ Σ wfΣ Φ (p ； q)
      with down-cast-check′ Δ Ψ Σ wfΣ Φ p |
           down-cast-check′ Δ Ψ Σ wfΣ Φ q
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
                  eqB = proj₂ (wt⊒-unique (storeWf-unique wfΣ) hp hp′)

                  eqB′ : B′ ≡ B₀
                  eqB′ = proj₁ (wt⊒-unique (storeWf-unique wfΣ) hq hq′)
                in
                B≢B′ (trans eqB (sym eqB′))
            })

up-cast-check :
  (Δ : TyCtx) →
  (Ψ : SealCtx) →
  (Σ : Store) →
  StoreWf Δ Ψ Σ →
  (p : Up) →
  Dec
    (Σ[ A ∈ Ty ] Σ[ B ∈ Ty ]
      Δ ∣ Ψ ∣ Σ ∣ (every Ψ) ⊢ p ⦂ A ⊑ B)
up-cast-check Δ Ψ Σ wfΣ p =
  up-cast-check′ Δ Ψ Σ wfΣ (every Ψ) p

down-cast-check :
  (Δ : TyCtx) →
  (Ψ : SealCtx) →
  (Σ : Store) →
  StoreWf Δ Ψ Σ →
  (p : Down) →
  Dec
    (Σ[ A ∈ Ty ] Σ[ B ∈ Ty ]
      Δ ∣ Ψ ∣ Σ ∣ (every Ψ) ⊢ p ⦂ A ⊒ B)
down-cast-check Δ Ψ Σ wfΣ p =
  down-cast-check′ Δ Ψ Σ wfΣ (every Ψ) p

------------------------------------------------------------------------
-- Finite permission-candidate solver (towards `*-cast-check-any`)
------------------------------------------------------------------------

maxSealTy : Ty → Seal
maxSealTy (＇ X) = zero
maxSealTy (｀ α) = α
maxSealTy (‵ ι) = zero
maxSealTy ★ = zero
maxSealTy (A ⇒ B) = maxSealTy A ⊔ maxSealTy B
maxSealTy (`∀ A) = maxSealTy A

mutual
  maxSealUp : Up → Seal
  maxSealUp (tag G) = maxSealTy G
  maxSealUp (unseal α) = α
  maxSealUp (p ↦ q) = maxSealDown p ⊔ maxSealUp q
  maxSealUp (∀ᵖ p) = maxSealUp p
  maxSealUp (ν p) = maxSealUp p
  maxSealUp (id A) = maxSealTy A
  maxSealUp (p ； q) = maxSealUp p ⊔ maxSealUp q

  maxSealDown : Down → Seal
  maxSealDown (untag G ℓ) = maxSealTy G
  maxSealDown (seal α) = α
  maxSealDown (p ↦ q) = maxSealUp p ⊔ maxSealDown q
  maxSealDown (∀ᵖ p) = maxSealDown p
  maxSealDown (ν p) = maxSealDown p
  maxSealDown (id A) = maxSealTy A
  maxSealDown (p ； q) = maxSealDown p ⊔ maxSealDown q

boolLists : ℕ → List (List CastPerm)
boolLists zero = [] ∷ []
boolLists (suc n) =
  map (λ P → conv ∷ P) (boolLists n) ++
  map (λ P → cast-seal ∷ P) (boolLists n) ++
  map (λ P → cast-tag ∷ P) (boolLists n)

permCandidatesUp : Up → List (List CastPerm)
permCandidatesUp p = boolLists (suc (maxSealUp p))

permCandidatesDown : Down → List (List CastPerm)
permCandidatesDown p = boolLists (suc (maxSealDown p))

infix 4 _∈perm_

data _∈perm_ : List CastPerm → List (List CastPerm) → Set where
  here-perm : ∀ {Φ Φs} → Φ ∈perm (Φ ∷ Φs)
  there-perm : ∀ {Φ Φ′ Φs} → Φ ∈perm Φs → Φ ∈perm (Φ′ ∷ Φs)

clip : ℕ → List CastPerm → List CastPerm
clip zero Φ = []
clip (suc n) [] = cast-tag ∷ clip n []
clip (suc n) (b ∷ Φ) = b ∷ clip n Φ

clip-empty-∉ :
  ∀ {n α} →
  α ∈ clip n [] →
  ⊥
clip-empty-∉ {zero} ()
clip-empty-∉ {suc n} {zero} ()
clip-empty-∉ {suc n} {suc α} (there p) = clip-empty-∉ p

clip-preserve-∈ :
  ∀ {n α Φ} →
  α < n →
  α ∈ Φ →
  α ∈ clip n Φ
clip-preserve-∈ {zero} ()
clip-preserve-∈ {suc n} {zero} {Φ = conv ∷ Φ} α<n here-conv = here-conv
clip-preserve-∈ {suc n} {zero} {Φ = cast-seal ∷ Φ} α<n here-seal = here-seal
clip-preserve-∈ {suc n} {suc α} (s<s α<n) (there p) =
  there (clip-preserve-∈ α<n p)

clip-preserve-∈conv :
  ∀ {n α Φ} →
  α < n →
  α ∈conv Φ →
  α ∈conv clip n Φ
clip-preserve-∈conv {zero} ()
clip-preserve-∈conv {suc n} {zero} {Φ = conv ∷ Φ} α<n here-conv-only = here-conv-only
clip-preserve-∈conv {suc n} {suc α} (s<s α<n) (there-conv p) =
  there-conv (clip-preserve-∈conv α<n p)

clip-preserve-∈cast :
  ∀ {n α Φ} →
  α < n →
  α ∈cast Φ →
  α ∈cast clip n Φ
clip-preserve-∈cast {zero} ()
clip-preserve-∈cast {suc n} {zero} {Φ = cast-seal ∷ Φ} α<n here-cast-only = here-cast-only
clip-preserve-∈cast {suc n} {suc α} (s<s α<n) (there-cast p) =
  there-cast (clip-preserve-∈cast α<n p)

clip-preserve-∈tag :
  ∀ {n α Φ} →
  α < n →
  α ∈tag Φ →
  α ∈tag clip n Φ
clip-preserve-∈tag {zero} ()
clip-preserve-∈tag {suc n} {zero} {Φ = cast-tag ∷ Φ} α<n here-tag-only = here-tag-only
clip-preserve-∈tag {suc n} {suc α} (s<s α<n) (there-tag p) =
  there-tag (clip-preserve-∈tag α<n p)

clip-reflect-∈ :
  ∀ {n α Φ} →
  α < n →
  α ∈ clip n Φ →
  α ∈ Φ
clip-reflect-∈ {zero} ()
clip-reflect-∈ {suc n} {zero} {Φ = []} α<n ()
clip-reflect-∈ {suc n} {zero} {Φ = conv ∷ Φ} α<n here-conv = here-conv
clip-reflect-∈ {suc n} {zero} {Φ = cast-seal ∷ Φ} α<n here-seal = here-seal
clip-reflect-∈ {suc n} {zero} {Φ = cast-tag ∷ Φ} α<n ()
clip-reflect-∈ {suc n} {suc α} {Φ = []} (s<s α<n) (there p) =
  ⊥-elim (clip-empty-∉ p)
clip-reflect-∈ {suc n} {suc α} {Φ = b ∷ Φ} (s<s α<n) (there p) =
  there (clip-reflect-∈ α<n p)

clip-preserve-∉ :
  ∀ {n α Φ} →
  α < n →
  α ∉ Φ →
  α ∉ clip n Φ
clip-preserve-∉ α<n α∉Φ α∈clip = α∉Φ (clip-reflect-∈ α<n α∈clip)

lt-suc-self : (n : ℕ) → n < suc n
lt-suc-self zero = z<s
lt-suc-self (suc n) = s<s (lt-suc-self n)

lt-weaken-suc :
  ∀ {a n} →
  a < n →
  a < suc n
lt-weaken-suc {a} {n} a<n = <-≤-trans a<n (n≤1+n n)

⊔-left< :
  ∀ {a b n} →
  a ⊔ b < n →
  a < n
⊔-left< {a} {b} {n} h = ≤-<-trans (m≤m⊔n a b) h

⊔-right< :
  ∀ {a b n} →
  a ⊔ b < n →
  b < n
⊔-right< {a} {b} {n} h = ≤-<-trans (m≤n⊔m a b) h

∈perm-left :
  ∀ {Φ Φs Ψs} →
  Φ ∈perm Φs →
  Φ ∈perm (Φs ++ Ψs)
∈perm-left here-perm = here-perm
∈perm-left (there-perm h) = there-perm (∈perm-left h)

∈perm-right :
  ∀ {Φ Φs Ψs} →
  Φ ∈perm Ψs →
  Φ ∈perm (Φs ++ Ψs)
∈perm-right {Φs = []} h = h
∈perm-right {Φs = Φ′ ∷ Φs} h = there-perm (∈perm-right {Φs = Φs} h)

∈perm-map-true :
  ∀ {Φ Φs} →
  Φ ∈perm Φs →
  (conv ∷ Φ) ∈perm map (λ P → conv ∷ P) Φs
∈perm-map-true here-perm = here-perm
∈perm-map-true (there-perm h) = there-perm (∈perm-map-true h)

∈perm-map-false :
  ∀ {Φ Φs} →
  Φ ∈perm Φs →
  (cast-tag ∷ Φ) ∈perm map (λ P → cast-tag ∷ P) Φs
∈perm-map-false here-perm = here-perm
∈perm-map-false (there-perm h) = there-perm (∈perm-map-false h)

∈perm-map-seal :
  ∀ {Φ Φs} →
  Φ ∈perm Φs →
  (cast-seal ∷ Φ) ∈perm map (λ P → cast-seal ∷ P) Φs
∈perm-map-seal here-perm = here-perm
∈perm-map-seal (there-perm h) = there-perm (∈perm-map-seal h)

clip∈boolLists :
  (n : ℕ) →
  (Φ : List CastPerm) →
  clip n Φ ∈perm boolLists n
clip∈boolLists zero Φ = here-perm
clip∈boolLists (suc n) [] =
  ∈perm-right
    {Φs = map (λ P → conv ∷ P) (boolLists n)}
    (∈perm-right
      {Φs = map (λ P → cast-seal ∷ P) (boolLists n)}
      (∈perm-map-false (clip∈boolLists n [])))
clip∈boolLists (suc n) (conv ∷ Φ) =
  ∈perm-left
    {Ψs = map (λ P → cast-seal ∷ P) (boolLists n) ++ map (λ P → cast-tag ∷ P) (boolLists n)}
    (∈perm-map-true (clip∈boolLists n Φ))
clip∈boolLists (suc n) (cast-seal ∷ Φ) =
  ∈perm-right
    {Φs = map (λ P → conv ∷ P) (boolLists n)}
    (∈perm-left
      {Ψs = map (λ P → cast-tag ∷ P) (boolLists n)}
      (∈perm-map-seal (clip∈boolLists n Φ)))
clip∈boolLists (suc n) (cast-tag ∷ Φ) =
  ∈perm-right
    {Φs = map (λ P → conv ∷ P) (boolLists n)}
    (∈perm-right
      {Φs = map (λ P → cast-seal ∷ P) (boolLists n)}
      (∈perm-map-false (clip∈boolLists n Φ)))

boolLists-complete-length :
  (Φ : List CastPerm) →
  Φ ∈perm boolLists (length Φ)
boolLists-complete-length [] = here-perm
boolLists-complete-length (conv ∷ Φ) =
  ∈perm-left
    {Ψs = map (λ P → cast-seal ∷ P) (boolLists (length Φ)) ++
          map (λ P → cast-tag ∷ P) (boolLists (length Φ))}
    (∈perm-map-true (boolLists-complete-length Φ))
boolLists-complete-length (cast-seal ∷ Φ) =
  ∈perm-right
    {Φs = map (λ P → conv ∷ P) (boolLists (length Φ))}
    (∈perm-left
      {Ψs = map (λ P → cast-tag ∷ P) (boolLists (length Φ))}
      (∈perm-map-seal (boolLists-complete-length Φ)))
boolLists-complete-length (cast-tag ∷ Φ) =
  ∈perm-right
    {Φs = map (λ P → conv ∷ P) (boolLists (length Φ))}
    (∈perm-right
      {Φs = map (λ P → cast-seal ∷ P) (boolLists (length Φ))}
      (∈perm-map-false (boolLists-complete-length Φ)))

ground-ok-clip :
  ∀ {G : Ty}{g : Ground G}{Φ : List CastPerm} →
  (n : ℕ) →
  maxSealTy G < n →
  ⊢ g ok Φ →
  ⊢ g ok clip n Φ
ground-ok-clip {g = ｀ α} n h gok = clip-preserve-∈tag h gok
ground-ok-clip {g = ‵ ι} n h gok = tt
ground-ok-clip {g = ★⇒★} n h gok = tt

mutual
  normalize-up :
    ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Up} →
    (n : ℕ) →
    maxSealUp p < n →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    Δ ∣ Ψ ∣ Σ ∣ (clip n Φ) ⊢ p ⦂ A ⊑ B
  normalize-up n hmax (wt-tag g gok) =
    wt-tag g (ground-ok-clip n hmax gok)
  normalize-up n hmax (wt-unseal h α∈Φ) =
    wt-unseal h (clip-preserve-∈conv hmax α∈Φ)
  normalize-up n hmax (wt-unseal★ h α∈Φ) =
    wt-unseal★ h (clip-preserve-∈cast hmax α∈Φ)
  normalize-up n hmax (wt-↦ p q) =
    wt-↦ (normalize-down n (⊔-left< hmax) p) (normalize-up n (⊔-right< hmax) q)
  normalize-up n hmax (wt-∀ p) = wt-∀ (normalize-up n hmax p)
  normalize-up n hmax (wt-ν p) =
    wt-ν (normalize-up (suc n) (lt-weaken-suc hmax) p)
  normalize-up n hmax (wt-id wfA) = wt-id wfA
  normalize-up n hmax (wt-； p q) =
    wt-； (normalize-up n (⊔-left< hmax) p) (normalize-up n (⊔-right< hmax) q)

  normalize-down :
    ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Down} →
    (n : ℕ) →
    maxSealDown p < n →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    Δ ∣ Ψ ∣ Σ ∣ (clip n Φ) ⊢ p ⦂ A ⊒ B
  normalize-down n hmax (wt-untag g gok ℓ) =
    wt-untag g (ground-ok-clip n hmax gok) ℓ
  normalize-down n hmax (wt-seal h α∈Φ) =
    wt-seal h (clip-preserve-∈conv hmax α∈Φ)
  normalize-down n hmax (wt-seal★ h α∈Φ) =
    wt-seal★ h (clip-preserve-∈cast hmax α∈Φ)
  normalize-down n hmax (wt-↦ p q) =
    wt-↦ (normalize-up n (⊔-left< hmax) p) (normalize-down n (⊔-right< hmax) q)
  normalize-down n hmax (wt-∀ p) = wt-∀ (normalize-down n hmax p)
  normalize-down n hmax (wt-ν p) =
    wt-ν (normalize-down (suc n) (lt-weaken-suc hmax) p)
  normalize-down n hmax (wt-id wfA) = wt-id wfA
  normalize-down n hmax (wt-； p q) =
    wt-； (normalize-down n (⊔-left< hmax) p) (normalize-down n (⊔-right< hmax) q)

search-up-casts :
  (Δ : TyCtx) →
  (Ψ : SealCtx) →
  (Σ : Store) →
  StoreWf Δ Ψ Σ →
  (p : Up) →
  (Φs : List (List CastPerm)) →
  Dec
    (Σ[ Φ ∈ List CastPerm ]
      (Φ ∈perm Φs) ×
      Σ[ A ∈ Ty ] Σ[ B ∈ Ty ]
        Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B)
search-up-casts Δ Ψ Σ wfΣ p [] =
  no
    (λ
      { (Φ , (() , (A , (B , hp)))) })
search-up-casts Δ Ψ Σ wfΣ p (Φ ∷ Φs)
  with up-cast-check′ Δ Ψ Σ wfΣ Φ p
search-up-casts Δ Ψ Σ wfΣ p (Φ ∷ Φs) | yes (A , (B , hp)) =
  yes (Φ , (here-perm , (A , (B , hp))))
search-up-casts Δ Ψ Σ wfΣ p (Φ ∷ Φs) | no ¬head
  with search-up-casts Δ Ψ Σ wfΣ p Φs
search-up-casts Δ Ψ Σ wfΣ p (Φ ∷ Φs) | no ¬head
  | yes (Φ′ , (Φ′∈ , (A , (B , hp)))) =
  yes (Φ′ , (there-perm Φ′∈ , (A , (B , hp))))
search-up-casts Δ Ψ Σ wfΣ p (Φ ∷ Φs) | no ¬head | no ¬tail =
  no
    (λ
      { (.Φ , (here-perm , (A , (B , hp)))) → ¬head (A , (B , hp))
      ; (Φ′ , (there-perm Φ′∈ , (A , (B , hp)))) →
          ¬tail (Φ′ , (Φ′∈ , (A , (B , hp))))
      })

search-up-casts-length :
  (Δ : TyCtx) →
  (Σ : Store) →
  (Ψ : SealCtx) →
  StoreWf Δ Ψ Σ →
  (p : Up) →
  (Φs : List (List CastPerm)) →
  Dec
    (Σ[ Φ ∈ List CastPerm ]
      (Φ ∈perm Φs) ×
      (length Φ ≡ Ψ) ×
      Σ[ A ∈ Ty ] Σ[ B ∈ Ty ]
        Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B)
search-up-casts-length Δ Σ Ψ wfΣ p [] =
  no
    (λ
      { (Φ , (() , (lenΦ , (A , (B , hp))))) })
search-up-casts-length Δ Σ Ψ wfΣ p (Φ ∷ Φs) with length Φ ≟ Ψ
search-up-casts-length Δ Σ Ψ wfΣ p (Φ ∷ Φs) | yes lenΦ
  with up-cast-check′ Δ Ψ Σ wfΣ Φ p
search-up-casts-length Δ Σ Ψ wfΣ p (Φ ∷ Φs) | yes lenΦ
  | yes (A , (B , hp)) =
  yes (Φ , (here-perm , (lenΦ , (A , (B , hp)))))
search-up-casts-length Δ Σ Ψ wfΣ p (Φ ∷ Φs) | yes lenΦ | no ¬head
  with search-up-casts-length Δ Σ Ψ wfΣ p Φs
search-up-casts-length Δ Σ Ψ wfΣ p (Φ ∷ Φs) | yes lenΦ | no ¬head
  | yes (Φ′ , (Φ′∈ , (lenΦ′ , (A , (B , hp))))) =
      yes (Φ′ , (there-perm Φ′∈ , (lenΦ′ , (A , (B , hp)))))
search-up-casts-length Δ Σ Ψ wfΣ p (Φ ∷ Φs) | yes lenΦ | no ¬head
  | no ¬tail =
      no
        (λ
          { (.Φ , (here-perm , (lenΦ′ , (A , (B , hp))))) → ¬head (A , (B , hp))
          ; (Φ′ , (there-perm Φ′∈ , (lenΦ′ , (A , (B , hp))))) →
              ¬tail (Φ′ , (Φ′∈ , (lenΦ′ , (A , (B , hp)))))
          })
search-up-casts-length Δ Σ Ψ wfΣ p (Φ ∷ Φs) | no ¬len
  with search-up-casts-length Δ Σ Ψ wfΣ p Φs
search-up-casts-length Δ Σ Ψ wfΣ p (Φ ∷ Φs) | no ¬len
  | yes (Φ′ , (Φ′∈ , (lenΦ′ , (A , (B , hp))))) =
      yes (Φ′ , (there-perm Φ′∈ , (lenΦ′ , (A , (B , hp)))))
search-up-casts-length Δ Σ Ψ wfΣ p (Φ ∷ Φs) | no ¬len | no ¬tail =
  no
    (λ
      { (.Φ , (here-perm , (lenΦ′ , (A , (B , hp))))) → ¬len lenΦ′
      ; (Φ′ , (there-perm Φ′∈ , (lenΦ′ , (A , (B , hp))))) →
          ¬tail (Φ′ , (Φ′∈ , (lenΦ′ , (A , (B , hp)))))
      })

search-down-casts :
  (Δ : TyCtx) →
  (Ψ : SealCtx) →
  (Σ : Store) →
  StoreWf Δ Ψ Σ →
  (p : Down) →
  (Φs : List (List CastPerm)) →
  Dec
    (Σ[ Φ ∈ List CastPerm ]
      (Φ ∈perm Φs) ×
      Σ[ A ∈ Ty ] Σ[ B ∈ Ty ]
        Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B)
search-down-casts Δ Ψ Σ wfΣ p [] =
  no
    (λ
      { (Φ , (() , (A , (B , hp)))) })
search-down-casts Δ Ψ Σ wfΣ p (Φ ∷ Φs)
  with down-cast-check′ Δ Ψ Σ wfΣ Φ p
search-down-casts Δ Ψ Σ wfΣ p (Φ ∷ Φs) | yes (A , (B , hp)) =
  yes (Φ , (here-perm , (A , (B , hp))))
search-down-casts Δ Ψ Σ wfΣ p (Φ ∷ Φs) | no ¬head
  with search-down-casts Δ Ψ Σ wfΣ p Φs
search-down-casts Δ Ψ Σ wfΣ p (Φ ∷ Φs) | no ¬head
  | yes (Φ′ , (Φ′∈ , (A , (B , hp)))) =
  yes (Φ′ , (there-perm Φ′∈ , (A , (B , hp))))
search-down-casts Δ Ψ Σ wfΣ p (Φ ∷ Φs) | no ¬head | no ¬tail =
  no
    (λ
      { (.Φ , (here-perm , (A , (B , hp)))) → ¬head (A , (B , hp))
      ; (Φ′ , (there-perm Φ′∈ , (A , (B , hp)))) →
          ¬tail (Φ′ , (Φ′∈ , (A , (B , hp))))
      })

search-down-casts-length :
  (Δ : TyCtx) →
  (Σ : Store) →
  (Ψ : SealCtx) →
  StoreWf Δ Ψ Σ →
  (p : Down) →
  (Φs : List (List CastPerm)) →
  Dec
    (Σ[ Φ ∈ List CastPerm ]
      (Φ ∈perm Φs) ×
      (length Φ ≡ Ψ) ×
      Σ[ A ∈ Ty ] Σ[ B ∈ Ty ]
        Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B)
search-down-casts-length Δ Σ Ψ wfΣ p [] =
  no
    (λ
      { (Φ , (() , (lenΦ , (A , (B , hp))))) })
search-down-casts-length Δ Σ Ψ wfΣ p (Φ ∷ Φs) with length Φ ≟ Ψ
search-down-casts-length Δ Σ Ψ wfΣ p (Φ ∷ Φs) | yes lenΦ
  with down-cast-check′ Δ Ψ Σ wfΣ Φ p
search-down-casts-length Δ Σ Ψ wfΣ p (Φ ∷ Φs) | yes lenΦ
  | yes (A , (B , hp)) =
      yes (Φ , (here-perm , (lenΦ , (A , (B , hp)))))
search-down-casts-length Δ Σ Ψ wfΣ p (Φ ∷ Φs) | yes lenΦ | no ¬head
  with search-down-casts-length Δ Σ Ψ wfΣ p Φs
search-down-casts-length Δ Σ Ψ wfΣ p (Φ ∷ Φs) | yes lenΦ | no ¬head
  | yes (Φ′ , (Φ′∈ , (lenΦ′ , (A , (B , hp))))) =
      yes (Φ′ , (there-perm Φ′∈ , (lenΦ′ , (A , (B , hp)))))
search-down-casts-length Δ Σ Ψ wfΣ p (Φ ∷ Φs) | yes lenΦ | no ¬head
  | no ¬tail =
      no
        (λ
          { (.Φ , (here-perm , (lenΦ′ , (A , (B , hp))))) → ¬head (A , (B , hp))
          ; (Φ′ , (there-perm Φ′∈ , (lenΦ′ , (A , (B , hp))))) →
              ¬tail (Φ′ , (Φ′∈ , (lenΦ′ , (A , (B , hp)))))
          })
search-down-casts-length Δ Σ Ψ wfΣ p (Φ ∷ Φs) | no ¬len
  with search-down-casts-length Δ Σ Ψ wfΣ p Φs
search-down-casts-length Δ Σ Ψ wfΣ p (Φ ∷ Φs) | no ¬len
  | yes (Φ′ , (Φ′∈ , (lenΦ′ , (A , (B , hp))))) =
      yes (Φ′ , (there-perm Φ′∈ , (lenΦ′ , (A , (B , hp)))))
search-down-casts-length Δ Σ Ψ wfΣ p (Φ ∷ Φs) | no ¬len | no ¬tail =
  no
    (λ
      { (.Φ , (here-perm , (lenΦ′ , (A , (B , hp))))) → ¬len lenΦ′
      ; (Φ′ , (there-perm Φ′∈ , (lenΦ′ , (A , (B , hp))))) →
          ¬tail (Φ′ , (Φ′∈ , (lenΦ′ , (A , (B , hp)))))
      })

up-cast-candidates-complete :
  ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{p : Up}{A B : Ty} →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
  Σ[ Φ′ ∈ List CastPerm ]
    (Φ′ ∈perm permCandidatesUp p) ×
    Δ ∣ Ψ ∣ Σ ∣ Φ′ ⊢ p ⦂ A ⊑ B
up-cast-candidates-complete {Φ = Φ} {p = p} hp =
  clip (suc (maxSealUp p)) Φ ,
  ( clip∈boolLists (suc (maxSealUp p)) Φ
  , normalize-up (suc (maxSealUp p)) (lt-suc-self (maxSealUp p)) hp
  )

down-cast-candidates-complete :
  ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{p : Down}{A B : Ty} →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
  Σ[ Φ′ ∈ List CastPerm ]
    (Φ′ ∈perm permCandidatesDown p) ×
    Δ ∣ Ψ ∣ Σ ∣ Φ′ ⊢ p ⦂ A ⊒ B
down-cast-candidates-complete {Φ = Φ} {p = p} hp =
  clip (suc (maxSealDown p)) Φ ,
  ( clip∈boolLists (suc (maxSealDown p)) Φ
  , normalize-down (suc (maxSealDown p)) (lt-suc-self (maxSealDown p)) hp
  )

up-cast-check-any :
  (Δ : TyCtx) →
  (Ψ : SealCtx) →
  (Σ : Store) →
  StoreWf Δ Ψ Σ →
  (p : Up) →
  Dec
    (Σ[ Φ ∈ List CastPerm ] Σ[ A ∈ Ty ] Σ[ B ∈ Ty ]
      Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B)
up-cast-check-any Δ Ψ Σ wfΣ p
  with search-up-casts Δ Ψ Σ wfΣ p (permCandidatesUp p)
up-cast-check-any Δ Ψ Σ wfΣ p | yes (Φ , (Φ∈ , (A , (B , hp)))) =
  yes (Φ , (A , (B , hp)))
up-cast-check-any Δ Ψ Σ wfΣ p | no ¬search =
  no
    (λ
      { (Φ , (A , (B , hp))) →
          let
            Φ′ : List CastPerm
            Φ′ = proj₁ (up-cast-candidates-complete hp)

            Φ′∈ : Φ′ ∈perm permCandidatesUp p
            Φ′∈ = proj₁ (proj₂ (up-cast-candidates-complete hp))

            hp′ : Δ ∣ Ψ ∣ Σ ∣ Φ′ ⊢ p ⦂ A ⊑ B
            hp′ = proj₂ (proj₂ (up-cast-candidates-complete hp))
          in
          ¬search (Φ′ , (Φ′∈ , (A , (B , hp′))))
      })

down-cast-check-any :
  (Δ : TyCtx) →
  (Ψ : SealCtx) →
  (Σ : Store) →
  StoreWf Δ Ψ Σ →
  (p : Down) →
  Dec
    (Σ[ Φ ∈ List CastPerm ] Σ[ A ∈ Ty ] Σ[ B ∈ Ty ]
      Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B)
down-cast-check-any Δ Ψ Σ wfΣ p
  with search-down-casts Δ Ψ Σ wfΣ p (permCandidatesDown p)
down-cast-check-any Δ Ψ Σ wfΣ p | yes (Φ , (Φ∈ , (A , (B , hp)))) =
  yes (Φ , (A , (B , hp)))
down-cast-check-any Δ Ψ Σ wfΣ p | no ¬search =
  no
    (λ
      { (Φ , (A , (B , hp))) →
          let
            Φ′ : List CastPerm
            Φ′ = proj₁ (down-cast-candidates-complete hp)

            Φ′∈ : Φ′ ∈perm permCandidatesDown p
            Φ′∈ = proj₁ (proj₂ (down-cast-candidates-complete hp))

            hp′ : Δ ∣ Ψ ∣ Σ ∣ Φ′ ⊢ p ⦂ A ⊒ B
            hp′ = proj₂ (proj₂ (down-cast-candidates-complete hp))
          in
          ¬search (Φ′ , (Φ′∈ , (A , (B , hp′))))
      })

up-cast-check-length :
  (Δ : TyCtx) →
  (Σ : Store) →
  (Ψ : SealCtx) →
  StoreWf Δ Ψ Σ →
  (p : Up) →
  Dec
    (Σ[ Φ ∈ List CastPerm ]
      (length Φ ≡ Ψ) ×
      Σ[ A ∈ Ty ] Σ[ B ∈ Ty ]
        Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B)
up-cast-check-length Δ Σ Ψ wfΣ p
  with search-up-casts-length Δ Σ Ψ wfΣ p (boolLists Ψ)
up-cast-check-length Δ Σ Ψ wfΣ p
  | yes (Φ , (Φ∈ , (lenΦ , (A , (B , hp))))) =
      yes (Φ , (lenΦ , (A , (B , hp))))
up-cast-check-length Δ Σ Ψ wfΣ p | no ¬search =
  no
    (λ
      { (Φ , (lenΦ , (A , (B , hp)))) →
          let
            Φ∈length : Φ ∈perm boolLists (length Φ)
            Φ∈length = boolLists-complete-length Φ

            Φ∈ : Φ ∈perm boolLists Ψ
            Φ∈ = subst (λ n → Φ ∈perm boolLists n) lenΦ Φ∈length
          in
          ¬search (Φ , (Φ∈ , (lenΦ , (A , (B , hp)))))
      })

down-cast-check-length :
  (Δ : TyCtx) →
  (Σ : Store) →
  (Ψ : SealCtx) →
  StoreWf Δ Ψ Σ →
  (p : Down) →
  Dec
    (Σ[ Φ ∈ List CastPerm ]
      (length Φ ≡ Ψ) ×
      Σ[ A ∈ Ty ] Σ[ B ∈ Ty ]
        Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B)
down-cast-check-length Δ Σ Ψ wfΣ p
  with search-down-casts-length Δ Σ Ψ wfΣ p (boolLists Ψ)
down-cast-check-length Δ Σ Ψ wfΣ p
  | yes (Φ , (Φ∈ , (lenΦ , (A , (B , hp))))) =
      yes (Φ , (lenΦ , (A , (B , hp))))
down-cast-check-length Δ Σ Ψ wfΣ p | no ¬search =
  no
    (λ
      { (Φ , (lenΦ , (A , (B , hp)))) →
          let
            Φ∈length : Φ ∈perm boolLists (length Φ)
            Φ∈length = boolLists-complete-length Φ

            Φ∈ : Φ ∈perm boolLists Ψ
            Φ∈ = subst (λ n → Φ ∈perm boolLists n) lenΦ Φ∈length
          in
          ¬search (Φ , (Φ∈ , (lenΦ , (A , (B , hp)))))
      })

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
       | value? M
... | yes ((A , M:A) , bfM) | yes vM =
  yes ((`∀ A , ⊢Λ vM M:A) , bf-Λ bfM)
... | yes ((A , M:A) , bfM) | no ¬vM =
  no
    (λ
      { ((`∀ B , ⊢Λ vM M:B) , bf-Λ bfM′) → ¬vM vM
      })
... | no ¬M | _ =
  no
    (λ
      { ((`∀ B , ⊢Λ vM M:B) , bf-Λ bfM) → ¬M ((B , M:B) , bfM)
      })

type-check Δ Ψ Σ Γ wfΓ wfΣ (M ⦂∀ B [ T ]) with type-check Δ Ψ Σ Γ wfΓ wfΣ M
... | no ¬M =
  no
    (λ
      { ((C , ⊢• M:∀ wfB wfT) , bf-⦂∀ bfM) → ¬M ((`∀ _ , M:∀) , bfM)
      })
... | yes ((＇ X , M:X) , bfM) =
  no
    (λ
      { ((C , ⊢• M:∀ wfB wfT) , bf-⦂∀ bfM′) →
          let eq : ＇ X ≡ `∀ _
              eq = type-unique-blamefree (storeWf-unique wfΣ) bfM M:X M:∀
          in nonForall-≠∀ (nf-var X) eq
      })
... | yes ((｀ α , M:α) , bfM) =
  no
    (λ
      { ((C , ⊢• M:∀ wfB wfT) , bf-⦂∀ bfM′) →
          let eq : ｀ α ≡ `∀ _
              eq = type-unique-blamefree (storeWf-unique wfΣ) bfM M:α M:∀
          in nonForall-≠∀ (nf-seal α) eq
      })
... | yes ((‵ ι , M:ι) , bfM) =
  no
    (λ
      { ((C , ⊢• M:∀ wfB wfT) , bf-⦂∀ bfM′) →
          let eq : ‵ ι ≡ `∀ _
              eq = type-unique-blamefree (storeWf-unique wfΣ) bfM M:ι M:∀
          in nonForall-≠∀ (nf-base ι) eq
      })
... | yes ((★ , M:★) , bfM) =
  no
    (λ
      { ((C , ⊢• M:∀ wfB wfT) , bf-⦂∀ bfM′) →
          let eq : ★ ≡ `∀ _
              eq = type-unique-blamefree (storeWf-unique wfΣ) bfM M:★ M:∀
          in nonForall-≠∀ nf-star eq
      })
... | yes ((A ⇒ B′ , M:AB) , bfM) =
  no
    (λ
      { ((C , ⊢• M:∀ wfB wfT) , bf-⦂∀ bfM′) →
          let eq : (A ⇒ B′) ≡ `∀ _
              eq = type-unique-blamefree (storeWf-unique wfΣ) bfM M:AB M:∀
          in nonForall-≠∀ (nf-⇒ A B′) eq
      })
... | yes ((`∀ B′ , M:∀B′) , bfM)
  with B′ ≟Ty B | wfTyDec (suc Δ) Ψ B | wfTyDec Δ Ψ T
...   | no B′≢B | _ | _ =
      no
        (λ
          { ((C , ⊢• M:∀B wfB wfT) , bf-⦂∀ bfM′) →
              let eqAll : `∀ B′ ≡ `∀ B
                  eqAll = type-unique-blamefree (storeWf-unique wfΣ) bfM M:∀B′ M:∀B
              in
              B′≢B (cong forallBodyTy eqAll)
          })
...   | yes refl | no ¬wfB | _ =
      no
        (λ
          { ((C , ⊢• M:∀B wfB wfT) , bf-⦂∀ bfM′) → ¬wfB wfB
          })
...   | yes refl | yes wfB | no ¬wfT =
      no
        (λ
          { ((C , ⊢• M:∀B wfB′ wfT) , bf-⦂∀ bfM′) → ¬wfT wfT
          })
...   | yes refl | yes wfB | yes wfT =
      yes ((B [ T ]ᵗ , ⊢• M:∀B′ wfB wfT) , bf-⦂∀ bfM)

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
      { ((B , ⊢up {A = A′} Φ lenΦ M:A′ hp) , bf-up bfM) →
          ¬M ((A′ , M:A′) , bfM)
      })
... | yes ((A , M:A) , bfM) with up-cast-check-length Δ Σ Ψ wfΣ p
...   | no ¬p =
      no
        (λ
          { ((B , ⊢up {A = A′} Φ lenΦ M:A′ hp) , bf-up bfM′) →
              ¬p (Φ , (lenΦ , (A′ , (B , hp))))
          })
...   | yes (Φ′ , (lenΦ′ , (A′ , (B , hp)))) with A′ ≟Ty A
...     | yes refl = yes ((B , ⊢up Φ′ lenΦ′ M:A hp) , bf-up bfM)
...     | no A′≢A =
        no
          (λ
            { ((C , ⊢up {A = A″} Φ lenΦ M:A″ hp′) , bf-up bfM′) →
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
      { ((B , ⊢down {A = A′} Φ lenΦ M:A′ hp) , bf-down bfM) →
          ¬M ((A′ , M:A′) , bfM)
      })
... | yes ((A , M:A) , bfM) with down-cast-check-length Δ Σ Ψ wfΣ p
...   | no ¬p =
      no
        (λ
          { ((B , ⊢down {A = A′} Φ lenΦ M:A′ hp) , bf-down bfM′) →
              ¬p (Φ , (lenΦ , (A′ , (B , hp))))
          })
...   | yes (Φ′ , (lenΦ′ , (A′ , (B , hp)))) with A′ ≟Ty A
...     | yes refl = yes ((B , ⊢down Φ′ lenΦ′ M:A hp) , bf-down bfM)
...     | no A′≢A =
        no
          (λ
            { ((C , ⊢down {A = A″} Φ lenΦ M:A″ hp′) , bf-down bfM′) →
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
