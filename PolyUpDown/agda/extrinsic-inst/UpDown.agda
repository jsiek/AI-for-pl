module UpDown where

-- File Charter:
--   * Raw widening/narrowing syntax and a separate well-typed judgment in extrinsic style.
--   * Theorems whose main subject is `Up`, `Down`, and their well-typed interpretation.
--   * No generic `Ty` substitution algebra (put that in `TypeProperties`) and no
--   * store-structural transport lemmas (put those in `Store`).
-- Note to self:
--   * Keep `Up`/`Down` free of store/permission indices; encode invariants only in
--     the well-typed layer.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; s≤s)
open import Data.Nat.Properties
  using (≤-refl; <-≤-trans; m≤m⊔n; m≤n⊔m; n≤1+n)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Unit using (⊤)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import TypeProperties
open import Store

Label : Set
Label = ℕ

------------------------------------------------------------------------
-- Permissions as explicit seal membership in bool lists
------------------------------------------------------------------------

infix 4 _∈_ _∉_

data _∈_ : Seal → List Bool → Set where
  here  : ∀ {P} → zero ∈ (true ∷ P)
  there : ∀ {α b P} → α ∈ P → suc α ∈ (b ∷ P)

_∉_ : Seal → List Bool → Set
α ∉ P = α ∈ P → ⊥

⊢_ok_ : ∀ {G : Ty} → Ground G → List Bool → Set
⊢ (｀ α) ok Φ = α ∉ Φ
⊢ (‵ ι) ok Φ = ⊤
⊢ ★⇒★ ok Φ = ⊤

------------------------------------------------------------------------
-- Raw widening/narrowing (no indices)
------------------------------------------------------------------------

infixr 7 _↦_
infixl 6 _；_

mutual
  data Up : Set where
    tag : Ty → Up

    unseal : Seal → Up

    _↦_ : Down → Up → Up

    ∀ᵖ : Up → Up

    ν_ : Up → Up

    id : Ty → Up

    _；_ : Up → Up → Up

  data Down : Set where
    untag : Ty → Label → Down

    seal : Seal → Down

    _↦_ : Up → Down → Down

    ∀ᵖ : Down → Down

    ν_ : Down → Down

    id : Ty → Down

    _；_ : Down → Down → Down

------------------------------------------------------------------------
-- Raw cast endpoints
------------------------------------------------------------------------

lookupTyˢ : Store → Seal → Ty
lookupTyˢ [] α = ｀ α
lookupTyˢ ((β , B) ∷ Σ) α with seal-≟ α β
lookupTyˢ ((β , B) ∷ Σ) α | yes _ = B
lookupTyˢ ((β , B) ∷ Σ) α | no _ = lookupTyˢ Σ α

closeVarAt : TyVar → TyVar → TyVar
closeVarAt zero X = suc X
closeVarAt (suc d) zero = zero
closeVarAt (suc d) (suc X) = suc (closeVarAt d X)

data OpenVar : Set where
  openVar : TyVar → OpenVar
  openSeal0 : OpenVar

openVarTy : OpenVar → Ty
openVarTy (openVar X) = ＇ X
openVarTy openSeal0 = ｀ zero

openVarAt : TyVar → TyVar → OpenVar
openVarAt zero zero = openSeal0
openVarAt zero (suc X) = openVar X
openVarAt (suc d) zero = openVar zero
openVarAt (suc d) (suc X) with openVarAt d X
openVarAt (suc d) (suc X) | openVar Y = openVar (suc Y)
openVarAt (suc d) (suc X) | openSeal0 = openSeal0

openTyEnv : TyVar → Substᵗ
openTyEnv d X = openVarTy (openVarAt d X)

closeOpenVarAt : TyVar → OpenVar → TyVar
closeOpenVarAt d (openVar X) = closeVarAt d X
closeOpenVarAt d openSeal0 = d

-- `closeνAt d` closes the ν-introduced seal at depth `d`.
closeνAt : TyVar → Ty → Ty
closeνAt d (＇ X) = ＇ (closeVarAt d X)
closeνAt d (｀ zero) = ＇ d
closeνAt d (｀ suc α) = ｀ α
closeνAt d (‵ ι) = ‵ ι
closeνAt d ★ = ★
closeνAt d (A ⇒ B) = closeνAt d A ⇒ closeνAt d B
closeνAt d (`∀ A) = `∀ (closeνAt (suc d) A)

-- Public close helper used by endpoint definitions.
closeν : Ty → Ty
closeν = closeνAt zero

mutual
  up-src : Store → Up → Ty
  up-src Σ (tag G) = G
  up-src Σ (unseal α) = ｀ α
  up-src Σ (p ↦ q) = down-tgt Σ p ⇒ up-src Σ q
  up-src Σ (∀ᵖ p) = `∀ (up-src (⟰ᵗ Σ) p)
  up-src Σ (ν p) =
    `∀ (closeν (up-src ((zero , ★) ∷ ⟰ˢ Σ) p))
  up-src Σ (id A) = A
  up-src Σ (p ； q) = up-src Σ p

  up-tgt : Store → Up → Ty
  up-tgt Σ (tag G) = ★
  up-tgt Σ (unseal α) = lookupTyˢ Σ α
  up-tgt Σ (p ↦ q) = down-src Σ p ⇒ up-tgt Σ q
  up-tgt Σ (∀ᵖ p) = `∀ (up-tgt (⟰ᵗ Σ) p)
  up-tgt Σ (ν p) =
    renameˢ (singleSealEnv zero) (up-tgt ((zero , ★) ∷ ⟰ˢ Σ) p)
  up-tgt Σ (id A) = A
  up-tgt Σ (p ； q) = up-tgt Σ q

  down-src : Store → Down → Ty
  down-src Σ (untag G ℓ) = ★
  down-src Σ (seal α) = lookupTyˢ Σ α
  down-src Σ (p ↦ q) = up-tgt Σ p ⇒ down-src Σ q
  down-src Σ (∀ᵖ p) = `∀ (down-src (⟰ᵗ Σ) p)
  down-src Σ (ν p) =
    renameˢ (singleSealEnv zero) (down-src ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) p)
  down-src Σ (id A) = A
  down-src Σ (p ； q) = down-src Σ p

  down-tgt : Store → Down → Ty
  down-tgt Σ (untag G ℓ) = G
  down-tgt Σ (seal α) = ｀ α
  down-tgt Σ (p ↦ q) = up-src Σ p ⇒ down-tgt Σ q
  down-tgt Σ (∀ᵖ p) = `∀ (down-tgt (⟰ᵗ Σ) p)
  down-tgt Σ (ν p) =
    `∀ (closeν (down-tgt ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) p))
  down-tgt Σ (id A) = A
  down-tgt Σ (p ； q) = down-tgt Σ q

------------------------------------------------------------------------
-- Well-typed widening/narrowing (recaptures intrinsic invariants)
------------------------------------------------------------------------

infix 3 _∣_⊢_⦂_⊑_ _∣_⊢_⦂_⊒_

WfTySome : Ty → Set
WfTySome A = Σ[ Δ ∈ TyCtx ] Σ[ Ψ ∈ SealCtx ] WfTy Δ Ψ A

WfTy-weakenᵗ :
  ∀ {Δ Δ′ Ψ A} →
  WfTy Δ Ψ A →
  Δ ≤ Δ′ →
  WfTy Δ′ Ψ A
WfTy-weakenᵗ (wfVar X<Δ) Δ≤Δ′ = wfVar (<-≤-trans X<Δ Δ≤Δ′)
WfTy-weakenᵗ (wfSeal α<Ψ) Δ≤Δ′ = wfSeal α<Ψ
WfTy-weakenᵗ wfBase Δ≤Δ′ = wfBase
WfTy-weakenᵗ wf★ Δ≤Δ′ = wf★
WfTy-weakenᵗ (wf⇒ hA hB) Δ≤Δ′ =
  wf⇒ (WfTy-weakenᵗ hA Δ≤Δ′) (WfTy-weakenᵗ hB Δ≤Δ′)
WfTy-weakenᵗ (wf∀ hA) Δ≤Δ′ =
  wf∀ (WfTy-weakenᵗ hA (s≤s Δ≤Δ′))

WfTy-weakenˢ :
  ∀ {Δ Ψ Ψ′ A} →
  WfTy Δ Ψ A →
  Ψ ≤ Ψ′ →
  WfTy Δ Ψ′ A
WfTy-weakenˢ (wfVar X<Δ) Ψ≤Ψ′ = wfVar X<Δ
WfTy-weakenˢ (wfSeal α<Ψ) Ψ≤Ψ′ = wfSeal (<-≤-trans α<Ψ Ψ≤Ψ′)
WfTy-weakenˢ wfBase Ψ≤Ψ′ = wfBase
WfTy-weakenˢ wf★ Ψ≤Ψ′ = wf★
WfTy-weakenˢ (wf⇒ hA hB) Ψ≤Ψ′ =
  wf⇒ (WfTy-weakenˢ hA Ψ≤Ψ′) (WfTy-weakenˢ hB Ψ≤Ψ′)
WfTy-weakenˢ (wf∀ hA) Ψ≤Ψ′ =
  wf∀ (WfTy-weakenˢ hA Ψ≤Ψ′)

wfTySome : (A : Ty) → WfTySome A
wfTySome (＇ X) = suc X , zero , wfVar ≤-refl
wfTySome (｀ α) = zero , suc α , wfSeal ≤-refl
wfTySome (‵ ι) = zero , zero , wfBase
wfTySome ★ = zero , zero , wf★
wfTySome (A ⇒ B)
  with wfTySome A | wfTySome B
... | ΔA , ΨA , wfA | ΔB , ΨB , wfB =
  (ΔA ⊔ ΔB) ,
  (ΨA ⊔ ΨB) ,
  wf⇒
    (WfTy-weakenˢ (WfTy-weakenᵗ wfA (m≤m⊔n ΔA ΔB)) (m≤m⊔n ΨA ΨB))
    (WfTy-weakenˢ (WfTy-weakenᵗ wfB (m≤n⊔m ΔA ΔB)) (m≤n⊔m ΨA ΨB))
wfTySome (`∀ A) with wfTySome A
... | ΔA , ΨA , wfA =
  ΔA ,
  ΨA ,
  wf∀ (WfTy-weakenᵗ wfA (n≤1+n ΔA))

mutual
  data _∣_⊢_⦂_⊑_ (Σ : Store) (Φ : List Bool) : Up → Ty → Ty → Set where
    wt-tag : ∀ {G}
      → (g : Ground G)
      → ⊢ g ok Φ
      → Σ ∣ Φ ⊢ tag G ⦂ G ⊑ ★

    wt-unseal : ∀ {α A}
      → Σ ∋ˢ α ⦂ A
      → α ∈ Φ
      → Σ ∣ Φ ⊢ unseal α ⦂ ｀ α ⊑ A

    wt-↦ : ∀ {A A′ B B′}{p : Down}{q : Up}
      → Σ ∣ Φ ⊢ p ⦂ A′ ⊒ A
      → Σ ∣ Φ ⊢ q ⦂ B ⊑ B′
      → Σ ∣ Φ ⊢ (p ↦ q) ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′)

    wt-∀ : ∀ {A B}{p : Up}
      → ⟰ᵗ Σ ∣ Φ ⊢ p ⦂ A ⊑ B
      → Σ ∣ Φ ⊢ (∀ᵖ p) ⦂ `∀ A ⊑ `∀ B

    wt-ν : ∀ {A B}{p : Up}
      → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (true ∷ Φ) ⊢ p ⦂ (⇑ˢ A) [ ｀ zero ]ᵗ ⊑ ⇑ˢ B
      → Σ ∣ Φ ⊢ (ν p) ⦂ (`∀ A) ⊑ B

    wt-id : ∀ {A}
      → WfTySome A
      → Σ ∣ Φ ⊢ id A ⦂ A ⊑ A

    wt-； : ∀ {A B C}{p q : Up}
      → Σ ∣ Φ ⊢ p ⦂ A ⊑ B
      → Σ ∣ Φ ⊢ q ⦂ B ⊑ C
      → Σ ∣ Φ ⊢ (p ； q) ⦂ A ⊑ C

  data _∣_⊢_⦂_⊒_ (Σ : Store) (Φ : List Bool) : Down → Ty → Ty → Set where
    wt-untag : ∀ {G}
      → (g : Ground G)
      → ⊢ g ok Φ
      → (ℓ : Label)
      → Σ ∣ Φ ⊢ (untag G ℓ) ⦂ ★ ⊒ G

    wt-seal : ∀ {α A}
      → Σ ∋ˢ α ⦂ A
      → α ∈ Φ
      → Σ ∣ Φ ⊢ seal α ⦂ A ⊒ ｀ α

    wt-↦ : ∀ {A A′ B B′}{p : Up}{q : Down}
      → Σ ∣ Φ ⊢ p ⦂ A′ ⊑ A
      → Σ ∣ Φ ⊢ q ⦂ B ⊒ B′
      → Σ ∣ Φ ⊢ (p ↦ q) ⦂ (A ⇒ B) ⊒ (A′ ⇒ B′)

    wt-∀ : ∀ {A B}{p : Down}
      → ⟰ᵗ Σ ∣ Φ ⊢ p ⦂ A ⊒ B
      → Σ ∣ Φ ⊢ (∀ᵖ p) ⦂ `∀ A ⊒ `∀ B

    wt-ν : ∀ {A B}{p : Down}
      → ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (false ∷ Φ) ⊢ p ⦂ ⇑ˢ B ⊒ (⇑ˢ A) [ ｀ zero ]ᵗ
      → Σ ∣ Φ ⊢ (ν p) ⦂ B ⊒ `∀ A

    wt-id : ∀ {A}
      → WfTySome A
      → Σ ∣ Φ ⊢ id A ⦂ A ⊒ A

    wt-； : ∀ {A B C}{p q : Down}
      → Σ ∣ Φ ⊢ p ⦂ A ⊒ B
      → Σ ∣ Φ ⊢ q ⦂ B ⊒ C
      → Σ ∣ Φ ⊢ (p ； q) ⦂ A ⊒ C

------------------------------------------------------------------------
-- Endpoint alignment helpers
------------------------------------------------------------------------

close-openVarAt :
  ∀ (d X : TyVar) →
  closeOpenVarAt d (openVarAt d X) ≡ X
close-openVarAt zero zero = refl
close-openVarAt zero (suc X) = refl
close-openVarAt (suc d) zero = refl
close-openVarAt (suc d) (suc X)
  with openVarAt d X in ov
close-openVarAt (suc d) (suc X)
  | openVar Y =
    cong suc
      (subst
        (λ ov′ → closeOpenVarAt d ov′ ≡ X)
        ov
        (close-openVarAt d X))
close-openVarAt (suc d) (suc X)
  | openSeal0 =
    cong suc
      (subst
        (λ ov′ → closeOpenVarAt d ov′ ≡ X)
        ov
        (close-openVarAt d X))

closeν-openVarTy :
  ∀ (d : TyVar) (ov : OpenVar) →
  closeνAt d (openVarTy ov) ≡ ＇ (closeOpenVarAt d ov)
closeν-openVarTy d (openVar X) = refl
closeν-openVarTy d openSeal0 = refl

closeν-openTyEnv :
  ∀ (d X : TyVar) →
  closeνAt d (openTyEnv d X) ≡ ＇ X
closeν-openTyEnv d X =
  trans
    (closeν-openVarTy d (openVarAt d X))
    (cong ＇_ (close-openVarAt d X))

openTyEnv-ext :
  ∀ (d X : TyVar) →
  extsᵗ (openTyEnv d) X ≡ openTyEnv (suc d) X
openTyEnv-ext d zero = refl
openTyEnv-ext d (suc X) with openVarAt d X
openTyEnv-ext d (suc X) | openVar Y = refl
openTyEnv-ext d (suc X) | openSeal0 = refl

closeν-open-at :
  ∀ (d : TyVar) (A : Ty) →
  closeνAt d (substᵗ (openTyEnv d) (⇑ˢ A)) ≡ A
closeν-open-at d (＇ X) = closeν-openTyEnv d X
closeν-open-at d (｀ α) = refl
closeν-open-at d (‵ ι) = refl
closeν-open-at d ★ = refl
closeν-open-at d (A ⇒ B) =
  cong₂ _⇒_ (closeν-open-at d A) (closeν-open-at d B)
closeν-open-at d (`∀ A) =
  cong `∀
    (trans
      (cong (closeνAt (suc d))
            (substᵗ-cong (openTyEnv-ext d) (⇑ˢ A)))
      (closeν-open-at (suc d) A))

openTyEnv-zero :
  (X : TyVar) →
  openTyEnv zero X ≡ singleTyEnv (｀ zero) X
openTyEnv-zero zero = refl
openTyEnv-zero (suc X) = refl

closeν-open :
  (A : Ty) →
  closeν ((⇑ˢ A) [ ｀ zero ]ᵗ) ≡ A
closeν-open A =
  trans
    (cong closeν (sym (substᵗ-cong openTyEnv-zero (⇑ˢ A))))
    (closeν-open-at zero A)

lookupTyˢ-lookup :
  ∀ {Σ : Store}{α : Seal}{A : Ty} →
  Uniqueˢ Σ →
  Σ ∋ˢ α ⦂ A →
  lookupTyˢ Σ α ≡ A
lookupTyˢ-lookup uniq[] ()
lookupTyˢ-lookup
  {α = α}
  (uniq∷_ {Σ = Σ} {α = β} β∉Σ uΣ)
  (Z∋ˢ {A = A} {B = B} α≡β A≡B)
  with seal-≟ α β
lookupTyˢ-lookup
  {α = α}
  (uniq∷_ {Σ = Σ} {α = β} β∉Σ uΣ)
  (Z∋ˢ {A = A} {B = B} α≡β A≡B)
  | yes _ = sym A≡B
lookupTyˢ-lookup
  {α = α}
  (uniq∷_ {Σ = Σ} {α = β} β∉Σ uΣ)
  (Z∋ˢ {A = A} {B = B} α≡β A≡B)
  | no α≢β = ⊥-elim (α≢β α≡β)
lookupTyˢ-lookup
  {α = α}
  (uniq∷_ {Σ = Σ} {α = β} β∉Σ uΣ)
  (S∋ˢ {A = A} h)
  with seal-≟ α β
lookupTyˢ-lookup
  {α = α}
  (uniq∷_ {Σ = Σ} {α = β} β∉Σ uΣ)
  (S∋ˢ {A = A} h)
  | yes α≡β = ⊥-elim (β∉Σ (subst (λ γ → Σ ∋ˢ γ ⦂ A) α≡β h))
lookupTyˢ-lookup
  {α = α}
  (uniq∷_ {Σ = Σ} {α = β} β∉Σ uΣ)
  (S∋ˢ {A = A} h)
  | no α≢β = lookupTyˢ-lookup uΣ h

stripLookup-⟰ᵗ :
  ∀ {Σ : Store}{α : Seal}{A : Ty} →
  ⟰ᵗ Σ ∋ˢ α ⦂ A →
  Σ[ B ∈ Ty ] Σ ∋ˢ α ⦂ B
stripLookup-⟰ᵗ {Σ = []} ()
stripLookup-⟰ᵗ {Σ = (β , B) ∷ Σ} (Z∋ˢ α≡β A≡B′) =
  B , Z∋ˢ α≡β refl
stripLookup-⟰ᵗ {Σ = (β , B) ∷ Σ} (S∋ˢ h)
  with stripLookup-⟰ᵗ h
stripLookup-⟰ᵗ {Σ = (β , B) ∷ Σ} (S∋ˢ h)
  | C , h′ = C , S∋ˢ h′

∉domˢ-⟰ᵗ :
  ∀ {Σ : Store}{α : Seal} →
  α ∉domˢ Σ →
  α ∉domˢ ⟰ᵗ Σ
∉domˢ-⟰ᵗ α∉Σ h with stripLookup-⟰ᵗ h
∉domˢ-⟰ᵗ α∉Σ h | B , h′ = α∉Σ h′

unique-⟰ᵗ :
  ∀ {Σ : Store} →
  Uniqueˢ Σ →
  Uniqueˢ (⟰ᵗ Σ)
unique-⟰ᵗ uniq[] = uniq[]
unique-⟰ᵗ (uniq∷_ α∉Σ uΣ) =
  uniq∷_ (∉domˢ-⟰ᵗ α∉Σ) (unique-⟰ᵗ uΣ)

mutual
  up-src-irrel :
    ∀ {Σ Σ′ : Store} →
    (p : Up) →
    up-src Σ p ≡ up-src Σ′ p
  up-src-irrel {Σ = Σ} {Σ′ = Σ′} (tag G) = refl
  up-src-irrel {Σ = Σ} {Σ′ = Σ′} (unseal α) = refl
  up-src-irrel {Σ = Σ} {Σ′ = Σ′} (p ↦ q) =
    cong₂ _⇒_
      (down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} p)
      (up-src-irrel {Σ = Σ} {Σ′ = Σ′} q)
  up-src-irrel {Σ = Σ} {Σ′ = Σ′} (∀ᵖ p) =
    cong `∀ (up-src-irrel {Σ = ⟰ᵗ Σ} {Σ′ = ⟰ᵗ Σ′} p)
  up-src-irrel {Σ = Σ} {Σ′ = Σ′} (ν p) =
    cong `∀
      (cong closeν
        (up-src-irrel
          {Σ = (zero , ★) ∷ ⟰ˢ Σ}
          {Σ′ = (zero , ★) ∷ ⟰ˢ Σ′}
          p))
  up-src-irrel {Σ = Σ} {Σ′ = Σ′} (id A) = refl
  up-src-irrel {Σ = Σ} {Σ′ = Σ′} (p ； q) =
    up-src-irrel {Σ = Σ} {Σ′ = Σ′} p

  down-tgt-irrel :
    ∀ {Σ Σ′ : Store} →
    (p : Down) →
    down-tgt Σ p ≡ down-tgt Σ′ p
  down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} (untag G ℓ) = refl
  down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} (seal α) = refl
  down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} (p ↦ q) =
    cong₂ _⇒_
      (up-src-irrel {Σ = Σ} {Σ′ = Σ′} p)
      (down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} q)
  down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} (∀ᵖ p) =
    cong `∀ (down-tgt-irrel {Σ = ⟰ᵗ Σ} {Σ′ = ⟰ᵗ Σ′} p)
  down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} (ν p) =
    cong `∀
      (cong closeν
        (down-tgt-irrel
          {Σ = (zero , ⇑ˢ ★) ∷ ⟰ˢ Σ}
          {Σ′ = (zero , ⇑ˢ ★) ∷ ⟰ˢ Σ′}
          p))
  down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} (id A) = refl
  down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} (p ； q) =
    down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} q

mutual
  up-src-align :
    ∀ {Σ : Store}{Φ : List Bool}{A B : Ty}{p : Up} →
    Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    up-src Σ p ≡ A
  up-src-align (wt-tag g gok) = refl
  up-src-align (wt-unseal h α∈Φ) = refl
  up-src-align (wt-↦ p q) =
    cong₂ _⇒_ (down-tgt-align p) (up-src-align q)
  up-src-align (wt-∀ p) = cong `∀ (up-src-align p)
  up-src-align (wt-ν {A = A} p) =
    cong `∀
      (trans
        (cong closeν (up-src-align p))
        (closeν-open A))
  up-src-align (wt-id wfA) = refl
  up-src-align (wt-； p q) = up-src-align p

  up-tgt-align :
    ∀ {Σ : Store}{Φ : List Bool}{A B : Ty}{p : Up} →
    Uniqueˢ Σ →
    Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    up-tgt Σ p ≡ B
  up-tgt-align uΣ (wt-tag g gok) = refl
  up-tgt-align uΣ (wt-unseal h α∈Φ) = lookupTyˢ-lookup uΣ h
  up-tgt-align uΣ (wt-↦ p q) =
    cong₂ _⇒_ (down-src-align uΣ p) (up-tgt-align uΣ q)
  up-tgt-align uΣ (wt-∀ p) = cong `∀ (up-tgt-align (unique-⟰ᵗ uΣ) p)
  up-tgt-align uΣ (wt-ν {B = B} p) =
    trans
      (cong (renameˢ (singleSealEnv zero)) (up-tgt-align (unique-ν ★ uΣ) p))
      (renameˢ-single-⇑ˢ-id zero B)
  up-tgt-align uΣ (wt-id wfA) = refl
  up-tgt-align uΣ (wt-； p q) = up-tgt-align uΣ q

  down-src-align :
    ∀ {Σ : Store}{Φ : List Bool}{A B : Ty}{p : Down} →
    Uniqueˢ Σ →
    Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    down-src Σ p ≡ A
  down-src-align uΣ (wt-untag g gok ℓ) = refl
  down-src-align uΣ (wt-seal h α∈Φ) = lookupTyˢ-lookup uΣ h
  down-src-align uΣ (wt-↦ p q) =
    cong₂ _⇒_ (up-tgt-align uΣ p) (down-src-align uΣ q)
  down-src-align uΣ (wt-∀ p) = cong `∀ (down-src-align (unique-⟰ᵗ uΣ) p)
  down-src-align uΣ (wt-ν {B = B} p) =
    trans
      (cong (renameˢ (singleSealEnv zero)) (down-src-align (unique-ν (⇑ˢ ★) uΣ) p))
      (renameˢ-single-⇑ˢ-id zero B)
  down-src-align uΣ (wt-id wfA) = refl
  down-src-align uΣ (wt-； p q) = down-src-align uΣ p

  down-tgt-align :
    ∀ {Σ : Store}{Φ : List Bool}{A B : Ty}{p : Down} →
    Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    down-tgt Σ p ≡ B
  down-tgt-align (wt-untag g gok ℓ) = refl
  down-tgt-align (wt-seal h α∈Φ) = refl
  down-tgt-align (wt-↦ p q) =
    cong₂ _⇒_ (up-src-align p) (down-tgt-align q)
  down-tgt-align (wt-∀ p) = cong `∀ (down-tgt-align p)
  down-tgt-align (wt-ν {A = A} p) =
    cong `∀
      (trans
        (cong closeν (down-tgt-align p))
        (closeν-open A))
  down-tgt-align (wt-id wfA) = refl
  down-tgt-align (wt-； p q) = down-tgt-align q

------------------------------------------------------------------------
-- Transport helpers
------------------------------------------------------------------------

RenOk : Renameˢ → List Bool → List Bool → Set
RenOk ρ P P′ = ∀ {α} → α ∈ P → ρ α ∈ P′

RenNotIn : Renameˢ → List Bool → List Bool → Set
RenNotIn ρ P P′ = ∀ {α} → α ∉ P → ρ α ∉ P′

RenOk-id : ∀ {P : List Bool} → RenOk (λ α → α) P P
RenOk-id p = p

RenNotIn-id : ∀ {P : List Bool} → RenNotIn (λ α → α) P P
RenNotIn-id p = p

RenOk-ext-true :
  ∀ {ρ : Renameˢ} {P P′ : List Bool} →
  RenOk ρ P P′ →
  RenOk (extˢ ρ) (true ∷ P) (true ∷ P′)
RenOk-ext-true ok {zero} here = here
RenOk-ext-true ok {suc α} (there p) = there (ok p)

RenOk-ext-false :
  ∀ {ρ : Renameˢ} {P P′ : List Bool} →
  RenOk ρ P P′ →
  RenOk (extˢ ρ) (false ∷ P) (false ∷ P′)
RenOk-ext-false ok {zero} ()
RenOk-ext-false ok {suc α} (there p) = there (ok p)

RenNotIn-ext-true :
  ∀ {ρ : Renameˢ} {P P′ : List Bool} →
  RenNotIn ρ P P′ →
  RenNotIn (extˢ ρ) (true ∷ P) (true ∷ P′)
RenNotIn-ext-true ok {zero} α∉true _ = α∉true here
RenNotIn-ext-true ok {suc α} α∉true (there p) =
  ok (λ α∈ → α∉true (there α∈)) p

RenNotIn-ext-false :
  ∀ {ρ : Renameˢ} {P P′ : List Bool} →
  RenNotIn ρ P P′ →
  RenNotIn (extˢ ρ) (false ∷ P) (false ∷ P′)
RenNotIn-ext-false ok {zero} α∉false ()
RenNotIn-ext-false ok {suc α} α∉false (there p) =
  ok (λ α∈ → α∉false (there α∈)) p

RenOk-singleSealEnv-true :
  ∀ {P : List Bool} {α : Seal} →
  α ∈ P →
  RenOk (singleSealEnv α) (true ∷ P) P
RenOk-singleSealEnv-true α∈P here = α∈P
RenOk-singleSealEnv-true α∈P (there p) = p

RenOk-singleSealEnv-false :
  ∀ {P : List Bool} {α : Seal} →
  RenOk (singleSealEnv α) (false ∷ P) P
RenOk-singleSealEnv-false {P = P} {α = α} {zero} ()
RenOk-singleSealEnv-false {P = P} {α = α} {suc β} (there p) = p

renameᵗ-ground-ok :
  ∀ {G : Ty}
  (ρ : Renameᵗ) (g : Ground G) {Φ : List Bool} →
  ⊢ g ok Φ →
  ⊢ renameᵗ-ground ρ g ok Φ
renameᵗ-ground-ok ρ (｀ α) gok = gok
renameᵗ-ground-ok ρ (‵ ι) gok = gok
renameᵗ-ground-ok ρ ★⇒★ gok = gok

substᵗ-ground-ok :
  ∀ {G : Ty}
  (σ : Substᵗ) (g : Ground G) {Φ : List Bool} →
  ⊢ g ok Φ →
  ⊢ substᵗ-ground σ g ok Φ
substᵗ-ground-ok σ (｀ α) gok = gok
substᵗ-ground-ok σ (‵ ι) gok = gok
substᵗ-ground-ok σ ★⇒★ gok = gok

renameˢ-ground-ok :
  ∀ {G : Ty}
  (ρ : Renameˢ) {Φ Φ′ : List Bool} →
  RenNotIn ρ Φ Φ′ →
  (g : Ground G) →
  ⊢ g ok Φ →
  ⊢ renameˢ-ground ρ g ok Φ′
renameˢ-ground-ok ρ ok (｀ α) gok = ok gok
renameˢ-ground-ok ρ ok (‵ ι) gok = gok
renameˢ-ground-ok ρ ok ★⇒★ gok = gok

------------------------------------------------------------------------
-- Raw coercion transport
------------------------------------------------------------------------

mutual
  rename⊑ᵗ : (ρ : Renameᵗ) → Up → Up
  rename⊑ᵗ ρ (tag G) = tag (renameᵗ ρ G)
  rename⊑ᵗ ρ (unseal α) = unseal α
  rename⊑ᵗ ρ (p ↦ q) = rename⊒ᵗ ρ p ↦ rename⊑ᵗ ρ q
  rename⊑ᵗ ρ (∀ᵖ p) = ∀ᵖ (rename⊑ᵗ (extᵗ ρ) p)
  rename⊑ᵗ ρ (ν p) = ν (rename⊑ᵗ ρ p)
  rename⊑ᵗ ρ (id A) = id (renameᵗ ρ A)
  rename⊑ᵗ ρ (p ； q) = rename⊑ᵗ ρ p ； rename⊑ᵗ ρ q

  rename⊒ᵗ : (ρ : Renameᵗ) → Down → Down
  rename⊒ᵗ ρ (untag G ℓ) = untag (renameᵗ ρ G) ℓ
  rename⊒ᵗ ρ (seal α) = seal α
  rename⊒ᵗ ρ (p ↦ q) = rename⊑ᵗ ρ p ↦ rename⊒ᵗ ρ q
  rename⊒ᵗ ρ (∀ᵖ p) = ∀ᵖ (rename⊒ᵗ (extᵗ ρ) p)
  rename⊒ᵗ ρ (ν p) = ν (rename⊒ᵗ ρ p)
  rename⊒ᵗ ρ (id A) = id (renameᵗ ρ A)
  rename⊒ᵗ ρ (p ； q) = rename⊒ᵗ ρ p ； rename⊒ᵗ ρ q

mutual
  rename⊑ˢ : (ρ : Renameˢ) → Up → Up
  rename⊑ˢ ρ (tag G) = tag (renameˢ ρ G)
  rename⊑ˢ ρ (unseal α) = unseal (ρ α)
  rename⊑ˢ ρ (p ↦ q) = rename⊒ˢ ρ p ↦ rename⊑ˢ ρ q
  rename⊑ˢ ρ (∀ᵖ p) = ∀ᵖ (rename⊑ˢ ρ p)
  rename⊑ˢ ρ (ν p) = ν (rename⊑ˢ (extˢ ρ) p)
  rename⊑ˢ ρ (id A) = id (renameˢ ρ A)
  rename⊑ˢ ρ (p ； q) = rename⊑ˢ ρ p ； rename⊑ˢ ρ q

  rename⊒ˢ : (ρ : Renameˢ) → Down → Down
  rename⊒ˢ ρ (untag G ℓ) = untag (renameˢ ρ G) ℓ
  rename⊒ˢ ρ (seal α) = seal (ρ α)
  rename⊒ˢ ρ (p ↦ q) = rename⊑ˢ ρ p ↦ rename⊒ˢ ρ q
  rename⊒ˢ ρ (∀ᵖ p) = ∀ᵖ (rename⊒ˢ ρ p)
  rename⊒ˢ ρ (ν p) = ν (rename⊒ˢ (extˢ ρ) p)
  rename⊒ˢ ρ (id A) = id (renameˢ ρ A)
  rename⊒ˢ ρ (p ； q) = rename⊒ˢ ρ p ； rename⊒ˢ ρ q

mutual
  subst⊑ᵗ : (σ : Substᵗ) → Up → Up
  subst⊑ᵗ σ (tag G) = tag (substᵗ σ G)
  subst⊑ᵗ σ (unseal α) = unseal α
  subst⊑ᵗ σ (p ↦ q) = subst⊒ᵗ σ p ↦ subst⊑ᵗ σ q
  subst⊑ᵗ σ (∀ᵖ p) = ∀ᵖ (subst⊑ᵗ (extsᵗ σ) p)
  subst⊑ᵗ σ (ν p) = ν (subst⊑ᵗ (liftSubstˢ σ) p)
  subst⊑ᵗ σ (id A) = id (substᵗ σ A)
  subst⊑ᵗ σ (p ； q) = subst⊑ᵗ σ p ； subst⊑ᵗ σ q

  subst⊒ᵗ : (σ : Substᵗ) → Down → Down
  subst⊒ᵗ σ (untag G ℓ) = untag (substᵗ σ G) ℓ
  subst⊒ᵗ σ (seal α) = seal α
  subst⊒ᵗ σ (p ↦ q) = subst⊑ᵗ σ p ↦ subst⊒ᵗ σ q
  subst⊒ᵗ σ (∀ᵖ p) = ∀ᵖ (subst⊒ᵗ (extsᵗ σ) p)
  subst⊒ᵗ σ (ν p) = ν (subst⊒ᵗ (liftSubstˢ σ) p)
  subst⊒ᵗ σ (id A) = id (substᵗ σ A)
  subst⊒ᵗ σ (p ； q) = subst⊒ᵗ σ p ； subst⊒ᵗ σ q

infixl 8 _[_]↓ˢ
_[_]↓ˢ : Down → Seal → Down
p [ α ]↓ˢ = rename⊒ˢ (singleSealEnv α) p

------------------------------------------------------------------------
-- Typed-judgment transport helpers
------------------------------------------------------------------------

castWt⊑ :
  ∀ {Σ Σ′ : Store}{Φ Φ′ : List Bool}{A B : Ty}{p : Up} →
  Σ ≡ Σ′ →
  Φ ≡ Φ′ →
  Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
  Σ′ ∣ Φ′ ⊢ p ⦂ A ⊑ B
castWt⊑ refl refl h = h

castWt⊒ :
  ∀ {Σ Σ′ : Store}{Φ Φ′ : List Bool}{A B : Ty}{p : Down} →
  Σ ≡ Σ′ →
  Φ ≡ Φ′ →
  Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
  Σ′ ∣ Φ′ ⊢ p ⦂ A ⊒ B
castWt⊒ refl refl h = h

castWt⊑-raw :
  ∀ {Σ : Store}{Φ : List Bool}{A A′ B B′ : Ty}{p : Up} →
  (A≡A′ : A ≡ A′) →
  (B≡B′ : B ≡ B′) →
  Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
  Σ ∣ Φ ⊢ p ⦂ A′ ⊑ B′
castWt⊑-raw refl refl h = h

castWt⊒-raw :
  ∀ {Σ : Store}{Φ : List Bool}{A A′ B B′ : Ty}{p : Down} →
  (A≡A′ : A ≡ A′) →
  (B≡B′ : B ≡ B′) →
  Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
  Σ ∣ Φ ⊢ p ⦂ A′ ⊒ B′
castWt⊒-raw refl refl h = h

------------------------------------------------------------------------
-- Type-variable renaming for well-typed widening and narrowing
------------------------------------------------------------------------

mutual
  ⊑-renameᵗ-wt :
    ∀ {Σ : Store}{Φ : List Bool}{A B : Ty}
    {p : Up} →
    (ρ : Renameᵗ) →
    Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    renameStoreᵗ ρ Σ ∣ Φ ⊢ rename⊑ᵗ ρ p ⦂ renameᵗ ρ A ⊑ renameᵗ ρ B
  ⊑-renameᵗ-wt ρ (wt-tag g gokΦ) =
    wt-tag (renameᵗ-ground ρ g) (renameᵗ-ground-ok ρ g gokΦ)
  ⊑-renameᵗ-wt ρ (wt-unseal h α∈Φ) = wt-unseal (renameLookupᵗ ρ h) α∈Φ
  ⊑-renameᵗ-wt ρ (wt-↦ p q) = wt-↦ (⊒-renameᵗ-wt ρ p) (⊑-renameᵗ-wt ρ q)
  ⊑-renameᵗ-wt {Σ = Σ} ρ (wt-∀ p) =
    wt-∀
      (castWt⊑
        (renameStoreᵗ-ext-⟰ᵗ ρ Σ)
        refl
        (⊑-renameᵗ-wt (extᵗ ρ) p))
  ⊑-renameᵗ-wt {Σ = Σ} ρ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊑
        (renameStoreᵗ-ν ρ Σ)
        refl
        (castWt⊑-raw
          (renameᵗ-ν-src ρ A)
          (renameᵗ-⇑ˢ ρ B)
          (⊑-renameᵗ-wt ρ p)))
  ⊑-renameᵗ-wt ρ (wt-id {A = A} wfA) = wt-id (wfTySome (renameᵗ ρ A))
  ⊑-renameᵗ-wt ρ (wt-； p q) = wt-； (⊑-renameᵗ-wt ρ p) (⊑-renameᵗ-wt ρ q)

  ⊒-renameᵗ-wt :
    ∀ {Σ : Store}{Φ : List Bool}{A B : Ty}
    {p : Down} →
    (ρ : Renameᵗ) →
    Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    renameStoreᵗ ρ Σ ∣ Φ ⊢ rename⊒ᵗ ρ p ⦂ renameᵗ ρ A ⊒ renameᵗ ρ B
  ⊒-renameᵗ-wt ρ (wt-untag g gokΦ ℓ) =
    wt-untag (renameᵗ-ground ρ g) (renameᵗ-ground-ok ρ g gokΦ) ℓ
  ⊒-renameᵗ-wt ρ (wt-seal h α∈Φ) = wt-seal (renameLookupᵗ ρ h) α∈Φ
  ⊒-renameᵗ-wt ρ (wt-↦ p q) = wt-↦ (⊑-renameᵗ-wt ρ p) (⊒-renameᵗ-wt ρ q)
  ⊒-renameᵗ-wt {Σ = Σ} ρ (wt-∀ p) =
    wt-∀
      (castWt⊒
        (renameStoreᵗ-ext-⟰ᵗ ρ Σ)
        refl
        (⊒-renameᵗ-wt (extᵗ ρ) p))
  ⊒-renameᵗ-wt {Σ = Σ} ρ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊒
        (renameStoreᵗ-ν ρ Σ)
        refl
        (castWt⊒-raw
          (renameᵗ-⇑ˢ ρ B)
          (renameᵗ-ν-src ρ A)
          (⊒-renameᵗ-wt ρ p)))
  ⊒-renameᵗ-wt ρ (wt-id {A = A} wfA) = wt-id (wfTySome (renameᵗ ρ A))
  ⊒-renameᵗ-wt ρ (wt-； p q) = wt-； (⊒-renameᵗ-wt ρ p) (⊒-renameᵗ-wt ρ q)

------------------------------------------------------------------------
-- Seal renaming for well-typed widening and narrowing
------------------------------------------------------------------------

mutual
  ⊑-renameˢ-wt :
    ∀ {Σ : Store}
      {Φ : List Bool}{Φ′ : List Bool}{A B : Ty}
      {p : Up} →
    (ρ : Renameˢ) →
    RenOk ρ Φ Φ′ →
    RenNotIn ρ Φ Φ′ →
    Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    renameStoreˢ ρ Σ ∣ Φ′ ⊢ rename⊑ˢ ρ p ⦂ renameˢ ρ A ⊑ renameˢ ρ B
  ⊑-renameˢ-wt ρ okΦ ok¬Φ (wt-tag g gokΦ) =
    wt-tag (renameˢ-ground ρ g) (renameˢ-ground-ok ρ ok¬Φ g gokΦ)
  ⊑-renameˢ-wt ρ okΦ ok¬Φ (wt-unseal h α∈Φ) =
    wt-unseal (renameLookupˢ ρ h) (okΦ α∈Φ)
  ⊑-renameˢ-wt ρ okΦ ok¬Φ (wt-↦ p q) =
    wt-↦ (⊒-renameˢ-wt ρ okΦ ok¬Φ p) (⊑-renameˢ-wt ρ okΦ ok¬Φ q)
  ⊑-renameˢ-wt {Σ = Σ} ρ okΦ ok¬Φ (wt-∀ p) =
    wt-∀
      (castWt⊑
        (renameStoreˢ-ext-⟰ᵗ ρ Σ)
        refl
        (⊑-renameˢ-wt ρ okΦ ok¬Φ p))
  ⊑-renameˢ-wt {Σ = Σ} ρ okΦ ok¬Φ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊑
        (renameStoreˢ-ν ρ Σ)
        refl
        (castWt⊑-raw
          (renameˢ-ν-src ρ A)
          (renameˢ-ext-⇑ˢ ρ B)
          (⊑-renameˢ-wt
            (extˢ ρ)
            (RenOk-ext-true okΦ)
            (RenNotIn-ext-true ok¬Φ)
            p)))
  ⊑-renameˢ-wt ρ okΦ ok¬Φ (wt-id {A = A} wfA) = wt-id (wfTySome (renameˢ ρ A))
  ⊑-renameˢ-wt ρ okΦ ok¬Φ (wt-； p q) =
    wt-； (⊑-renameˢ-wt ρ okΦ ok¬Φ p) (⊑-renameˢ-wt ρ okΦ ok¬Φ q)

  ⊒-renameˢ-wt :
    ∀ {Σ : Store}
      {Φ : List Bool}{Φ′ : List Bool}{A B : Ty}
      {p : Down} →
    (ρ : Renameˢ) →
    RenOk ρ Φ Φ′ →
    RenNotIn ρ Φ Φ′ →
    Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    renameStoreˢ ρ Σ ∣ Φ′ ⊢ rename⊒ˢ ρ p ⦂ renameˢ ρ A ⊒ renameˢ ρ B
  ⊒-renameˢ-wt ρ okΦ ok¬Φ (wt-untag g gokΦ ℓ) =
    wt-untag (renameˢ-ground ρ g) (renameˢ-ground-ok ρ ok¬Φ g gokΦ) ℓ
  ⊒-renameˢ-wt ρ okΦ ok¬Φ (wt-seal h α∈Φ) =
    wt-seal (renameLookupˢ ρ h) (okΦ α∈Φ)
  ⊒-renameˢ-wt ρ okΦ ok¬Φ (wt-↦ p q) =
    wt-↦ (⊑-renameˢ-wt ρ okΦ ok¬Φ p) (⊒-renameˢ-wt ρ okΦ ok¬Φ q)
  ⊒-renameˢ-wt {Σ = Σ} ρ okΦ ok¬Φ (wt-∀ p) =
    wt-∀
      (castWt⊒
        (renameStoreˢ-ext-⟰ᵗ ρ Σ)
        refl
        (⊒-renameˢ-wt ρ okΦ ok¬Φ p))
  ⊒-renameˢ-wt {Σ = Σ} ρ okΦ ok¬Φ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊒
        (renameStoreˢ-ν ρ Σ)
        refl
        (castWt⊒-raw
          (renameˢ-ext-⇑ˢ ρ B)
          (renameˢ-ν-src ρ A)
          (⊒-renameˢ-wt
            (extˢ ρ)
            (RenOk-ext-false okΦ)
            (RenNotIn-ext-false ok¬Φ)
            p)))
  ⊒-renameˢ-wt ρ okΦ ok¬Φ (wt-id {A = A} wfA) = wt-id (wfTySome (renameˢ ρ A))
  ⊒-renameˢ-wt ρ okΦ ok¬Φ (wt-； p q) =
    wt-； (⊒-renameˢ-wt ρ okΦ ok¬Φ p) (⊒-renameˢ-wt ρ okΦ ok¬Φ q)

------------------------------------------------------------------------
-- Type-variable substitution for well-typed widening and narrowing
------------------------------------------------------------------------

mutual
  ⊑-substᵗ-wt :
    ∀ {Σ : Store}{Φ : List Bool}{A B : Ty}
      {p : Up} →
    (σ : Substᵗ) →
    Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    substStoreᵗ σ Σ ∣ Φ ⊢ subst⊑ᵗ σ p ⦂ substᵗ σ A ⊑ substᵗ σ B
  ⊑-substᵗ-wt σ (wt-tag g gokΦ) =
    wt-tag (substᵗ-ground σ g) (substᵗ-ground-ok σ g gokΦ)
  ⊑-substᵗ-wt σ (wt-unseal h α∈Φ) = wt-unseal (substLookupᵗ σ h) α∈Φ
  ⊑-substᵗ-wt σ (wt-↦ p q) = wt-↦ (⊒-substᵗ-wt σ p) (⊑-substᵗ-wt σ q)
  ⊑-substᵗ-wt {Σ = Σ} σ (wt-∀ p) =
    wt-∀
      (castWt⊑
        (substStoreᵗ-ext-⟰ᵗ σ Σ)
        refl
        (⊑-substᵗ-wt (extsᵗ σ) p))
  ⊑-substᵗ-wt {Σ = Σ} σ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊑
        (substStoreᵗ-ν σ Σ)
        refl
        (castWt⊑-raw
          (substᵗ-ν-src σ A)
          (substᵗ-⇑ˢ σ B)
          (⊑-substᵗ-wt (liftSubstˢ σ) p)))
  ⊑-substᵗ-wt σ (wt-id {A = A} wfA) = wt-id (wfTySome (substᵗ σ A))
  ⊑-substᵗ-wt σ (wt-； p q) = wt-； (⊑-substᵗ-wt σ p) (⊑-substᵗ-wt σ q)

  ⊒-substᵗ-wt :
    ∀ {Σ : Store}{Φ : List Bool}{A B : Ty}
      {p : Down} →
    (σ : Substᵗ) →
    Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    substStoreᵗ σ Σ ∣ Φ ⊢ subst⊒ᵗ σ p ⦂ substᵗ σ A ⊒ substᵗ σ B
  ⊒-substᵗ-wt σ (wt-untag g gokΦ ℓ) =
    wt-untag (substᵗ-ground σ g) (substᵗ-ground-ok σ g gokΦ) ℓ
  ⊒-substᵗ-wt σ (wt-seal h α∈Φ) = wt-seal (substLookupᵗ σ h) α∈Φ
  ⊒-substᵗ-wt σ (wt-↦ p q) = wt-↦ (⊑-substᵗ-wt σ p) (⊒-substᵗ-wt σ q)
  ⊒-substᵗ-wt {Σ = Σ} σ (wt-∀ p) =
    wt-∀
      (castWt⊒
        (substStoreᵗ-ext-⟰ᵗ σ Σ)
        refl
        (⊒-substᵗ-wt (extsᵗ σ) p))
  ⊒-substᵗ-wt {Σ = Σ} σ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊒
        (substStoreᵗ-ν σ Σ)
        refl
        (castWt⊒-raw
          (substᵗ-⇑ˢ σ B)
          (substᵗ-ν-src σ A)
          (⊒-substᵗ-wt (liftSubstˢ σ) p)))
  ⊒-substᵗ-wt σ (wt-id {A = A} wfA) = wt-id (wfTySome (substᵗ σ A))
  ⊒-substᵗ-wt σ (wt-； p q) = wt-； (⊒-substᵗ-wt σ p) (⊒-substᵗ-wt σ q)

infixl 8 _[_]↑
_[_]↑ :
  Up → Ty → Up
p [ T ]↑ = subst⊑ᵗ (singleTyEnv T) p

[]⊑ᵗ-wt :
  ∀ {Σ : Store}{Φ : List Bool}{A B : Ty}
    {p : Up}
  → Σ ∣ Φ ⊢ p ⦂ A ⊑ B
  → (T : Ty)
  → substStoreᵗ (singleTyEnv T) Σ ∣ Φ ⊢ p [ T ]↑ ⦂ (A [ T ]ᵗ) ⊑ (B [ T ]ᵗ)
[]⊑ᵗ-wt h T = ⊑-substᵗ-wt (singleTyEnv T) h

infixl 8 _[_]↓
_[_]↓ :
  Down → Ty → Down
p [ T ]↓ = subst⊒ᵗ (singleTyEnv T) p

[]⊒ᵗ-wt :
  ∀ {Σ : Store}{Φ : List Bool}{A B : Ty}
    {p : Down}
  → Σ ∣ Φ ⊢ p ⦂ A ⊒ B
  → (T : Ty)
  → substStoreᵗ (singleTyEnv T) Σ ∣ Φ ⊢ p [ T ]↓ ⦂ A [ T ]ᵗ ⊒ B [ T ]ᵗ
[]⊒ᵗ-wt h T = ⊒-substᵗ-wt (singleTyEnv T) h

⊑-[]ᵗ-seal :
  ∀ {Σ : Store}{Φ : List Bool}{A B : Ty}{α : Seal}
    {p : Up}
  → α ∈ Φ
  → Σ ∣ Φ ⊢ p ⦂ A ⊑ B
  → substStoreᵗ (singleTyEnv (｀ α)) Σ ∣ Φ ⊢ p [ ｀ α ]↑ ⦂ A [ ｀ α ]ᵗ ⊑ B [ ｀ α ]ᵗ
⊑-[]ᵗ-seal {α = α} α∈Φ h = []⊑ᵗ-wt h (｀ α)

⊒-[]ᵗ-seal :
  ∀ {Σ : Store}{Φ : List Bool}{A B : Ty}{α : Seal}
    {p : Down}
  → α ∈ Φ
  → Σ ∣ Φ ⊢ p ⦂ A ⊒ B
  → substStoreᵗ (singleTyEnv (｀ α)) Σ ∣ Φ ⊢ p [ ｀ α ]↓ ⦂ A [ ｀ α ]ᵗ ⊒ B [ ｀ α ]ᵗ
⊒-[]ᵗ-seal {α = α} α∈Φ h = []⊒ᵗ-wt h (｀ α)
