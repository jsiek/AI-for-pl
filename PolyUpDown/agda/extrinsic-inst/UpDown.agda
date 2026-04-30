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
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _⊔_; z<s; s<s; s≤s)
open import Data.Nat.Properties
  using (≤-refl; <-≤-trans; m≤m⊔n; m≤n⊔m; n≤1+n)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
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
-- Permissions as explicit per-seal cast flags
------------------------------------------------------------------------

infix 4 _∈_ _∈conv_ _∈cast_ _∈tag_ _∉_

data CastPerm : Set where
  cast-tag : CastPerm
  cast-seal : CastPerm
  conv : CastPerm

every : SealCtx → List CastPerm
every zero = []
every (suc Ψ) = conv ∷ every Ψ

length-every : (Ψ : SealCtx) → length (every Ψ) ≡ Ψ
length-every zero = refl
length-every (suc Ψ) = cong suc (length-every Ψ)

none : SealCtx → List CastPerm
none zero = []
none (suc Ψ) = cast-tag ∷ none Ψ

data _∈_ : Seal → List CastPerm → Set where
  here-conv : ∀ {P} → zero ∈ (conv ∷ P)
  here-seal : ∀ {P} → zero ∈ (cast-seal ∷ P)
  there : ∀ {α b P} → α ∈ P → suc α ∈ (b ∷ P)

data _∈conv_ : Seal → List CastPerm → Set where
  here-conv-only : ∀ {P} → zero ∈conv (conv ∷ P)
  there-conv : ∀ {α b P} → α ∈conv P → suc α ∈conv (b ∷ P)

data _∈cast_ : Seal → List CastPerm → Set where
  here-cast-only : ∀ {P} → zero ∈cast (cast-seal ∷ P)
  there-cast : ∀ {α b P} → α ∈cast P → suc α ∈cast (b ∷ P)

data _∈tag_ : Seal → List CastPerm → Set where
  here-tag-only : ∀ {P} → zero ∈tag (cast-tag ∷ P)
  there-tag : ∀ {α b P} → α ∈tag P → suc α ∈tag (b ∷ P)

_∉_ : Seal → List CastPerm → Set
α ∉ P = α ∈ P → ⊥

∈conv⇒∈ : ∀ {α P} → α ∈conv P → α ∈ P
∈conv⇒∈ here-conv-only = here-conv
∈conv⇒∈ (there-conv p) = there (∈conv⇒∈ p)

∈cast⇒∈ : ∀ {α P} → α ∈cast P → α ∈ P
∈cast⇒∈ here-cast-only = here-seal
∈cast⇒∈ (there-cast p) = there (∈cast⇒∈ p)

every-member : ∀ {Ψ} (α : Seal) → α < Ψ → α ∈ every Ψ
every-member {zero} α ()
every-member {suc Ψ} zero z<s = here-conv
every-member {suc Ψ} (suc α) (s<s α<Ψ) = there (every-member α α<Ψ)

every-member-conv : ∀ {Ψ} (α : Seal) → α < Ψ → α ∈conv every Ψ
every-member-conv {zero} α ()
every-member-conv {suc Ψ} zero z<s = here-conv-only
every-member-conv {suc Ψ} (suc α) (s<s α<Ψ) =
  there-conv (every-member-conv α α<Ψ)

every-index : ∀ {Ψ} {α : Seal} → α ∈ every Ψ → α < Ψ
every-index {suc Ψ} {zero} here-conv = z<s
every-index {suc Ψ} {suc α} (there p) = s<s (every-index p)

every-index-conv : ∀ {Ψ} {α : Seal} → α ∈conv every Ψ → α < Ψ
every-index-conv {suc Ψ} {zero} here-conv-only = z<s
every-index-conv {suc Ψ} {suc α} (there-conv p) = s<s (every-index-conv p)

every-excluded-cast : ∀ {Ψ} (α : Seal) → α ∈cast every Ψ → ⊥
every-excluded-cast {zero} α ()
every-excluded-cast {suc Ψ} zero ()
every-excluded-cast {suc Ψ} (suc α) (there-cast p) = every-excluded-cast α p

every-excluded-tag : ∀ {Ψ} (α : Seal) → α ∈tag every Ψ → ⊥
every-excluded-tag {zero} α ()
every-excluded-tag {suc Ψ} zero ()
every-excluded-tag {suc Ψ} (suc α) (there-tag p) = every-excluded-tag α p

none-excluded : ∀ {Ψ} (α : Seal) → α ∉ none Ψ
none-excluded {zero} α ()
none-excluded {suc Ψ} zero ()
none-excluded {suc Ψ} (suc α) (there p) = none-excluded α p

⊢_ok_ : ∀ {G : Ty} → Ground G → List CastPerm → Set
⊢ (｀ α) ok Φ = α ∈tag Φ
⊢ (‵ ι) ok Φ = ⊤
⊢ ★⇒★ ok Φ = ⊤

------------------------------------------------------------------------
-- Widening/narrowing
------------------------------------------------------------------------

infixr 7 _↦_
infixl 6 _；_

mutual
  data Up : Set where
    tag : Up → Ty → Up
    unseal : Seal → Up → Up
    _↦_ : Down → Up → Up
    ∀ᵖ : Up → Up
    ν_ : Up → Up
    id : Ty → Up

  data Down : Set where
    untag : Ty → Label → Down → Down
    seal : Down → Seal → Down
    _↦_ : Up → Down → Down
    ∀ᵖ : Down → Down
    ν_ : Down → Down
    id : Ty → Down

mutual
  data Conv : Set where
    reveal : Seal → Conv
    _↦_ : Conv → Conv → Conv
    `∀ : Conv → Conv
    id : Ty → Conv
    _；_ : Conv → Conv → Conv

mutual
  data Cast : Set where
    tag : Ty → Cast
    reveal : Seal → Cast
    _↦_ : Cast → Cast → Cast
    `∀ : Cast → Cast
    ν_ : Cast → Cast
    id : Ty → Cast
    _；_ : Cast → Cast → Cast

------------------------------------------------------------------------
-- Raw cast endpoints
------------------------------------------------------------------------

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

-- `closeInlineAt d` closes the ν-introduced seal at depth `d`
-- via explicit `renameᵗ` + `substˢᵗ`.
closeInlineAt : TyVar → Ty → Ty
closeInlineAt d A = substˢᵗ (singleSealTyEnv (＇ d)) (renameᵗ (closeVarAt d) A)

mutual
  up-src : Store → Up → Ty
  up-src Σ (tag p G) = up-src Σ p
  up-src Σ (unseal α p) = ｀ α
  up-src Σ (p ↦ q) = down-tgt Σ p ⇒ up-src Σ q
  up-src Σ (∀ᵖ p) = `∀ (up-src (⟰ᵗ Σ) p)
  up-src Σ (ν p) =
    `∀ ((⇑ᵗ (up-src ((zero , ★) ∷ ⟰ˢ Σ) p)) [ ＇ zero ]ˢᵗ)
  up-src Σ (id A) = A

  up-tgt : Store → Up → Ty
  up-tgt Σ (tag p G) = ★
  up-tgt Σ (unseal α p) = up-tgt Σ p
  up-tgt Σ (p ↦ q) = down-src Σ p ⇒ up-tgt Σ q
  up-tgt Σ (∀ᵖ p) = `∀ (up-tgt (⟰ᵗ Σ) p)
  up-tgt Σ (ν p) =
    renameˢ (singleSealEnv zero) (up-tgt ((zero , ★) ∷ ⟰ˢ Σ) p)
  up-tgt Σ (id A) = A

  down-src : Store → Down → Ty
  down-src Σ (untag G ℓ p) = ★
  down-src Σ (seal p α) = down-src Σ p
  down-src Σ (p ↦ q) = up-tgt Σ p ⇒ down-src Σ q
  down-src Σ (∀ᵖ p) = `∀ (down-src (⟰ᵗ Σ) p)
  down-src Σ (ν p) =
    renameˢ (singleSealEnv zero) (down-src ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) p)
  down-src Σ (id A) = A

  down-tgt : Store → Down → Ty
  down-tgt Σ (untag G ℓ p) = down-tgt Σ p
  down-tgt Σ (seal p α) = ｀ α
  down-tgt Σ (p ↦ q) = up-src Σ p ⇒ down-tgt Σ q
  down-tgt Σ (∀ᵖ p) = `∀ (down-tgt (⟰ᵗ Σ) p)
  down-tgt Σ (ν p) =
    `∀ ((⇑ᵗ (down-tgt ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) p)) [ ＇ zero ]ˢᵗ)
  down-tgt Σ (id A) = A

------------------------------------------------------------------------
-- Well-typed widening/narrowing (recaptures intrinsic invariants)
------------------------------------------------------------------------

infix 3 _∣_∣_∣_⊢_⦂_⊑_ _∣_∣_∣_⊢_⦂_⊒_

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
  data _∣_∣_∣_⊢_⦂_⊑_ (Δ : TyCtx) (Ψ : SealCtx)
      (Σ : Store) (Φ : List CastPerm) : Up → Ty → Ty → Set where
    wt-tag : ∀ {A G}{p : Up}
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ G
      → (g : Ground G)
      → ⊢ g ok Φ
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ tag p G ⦂ A ⊑ ★

    wt-unseal : ∀ {α A B}{p : Up}
      → Σ ∋ˢ α ⦂ A
      → α ∈conv Φ
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ unseal α p ⦂ ｀ α ⊑ B

    wt-unseal★ : ∀ {α B}{p : Up}
      → Σ ∋ˢ α ⦂ ★
      → α ∈cast Φ
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ ★ ⊑ B
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ unseal α p ⦂ ｀ α ⊑ B

    wt-↦ : ∀ {A A′ B B′}{p : Down}{q : Up}
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A′ ⊒ A
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ q ⦂ B ⊑ B′
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ (p ↦ q) ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′)

    {-
      ⤊ Σ ∣ Φ ⊢  p[X]  : A[X] ⊑ B[X]
      -------------------------------------
      ⤊ Σ ∣ Φ ⊢  ∀X.p[X]  : ∀X.A[X] ⊑ ∀X.B[X]
    -}
    wt-∀ : ∀ {A B}{p : Up}
      → suc Δ ∣ Ψ ∣ (⟰ᵗ Σ) ∣ Φ ⊢ p ⦂ A ⊑ B
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ (∀ᵖ p) ⦂ `∀ A ⊑ `∀ B

    {-
      Σ, α:=★ ∣ Φ, cs ⊢  p[α]  : A[α] ⊑ B
      -----------------------------------
      Σ ∣ Φ ⊢  να.p[α]  : ∀X.A[X] ⊑ B
    -}
    wt-ν : ∀ {A B}{p : Up}
      → Δ ∣ suc Ψ ∣ ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ p
          ⦂ ((⇑ˢ A) [ ｀ zero ]ᵗ) ⊑ (⇑ˢ B)
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ (ν p) ⦂ (`∀ A) ⊑ B

    wt-id : ∀ {A}
      → WfTy Δ Ψ A
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ id A ⦂ A ⊑ A

  data _∣_∣_∣_⊢_⦂_⊒_ (Δ : TyCtx) (Ψ : SealCtx)
      (Σ : Store) (Φ : List CastPerm) : Down → Ty → Ty → Set where
    wt-untag : ∀ {G B}{p : Down}
      → (g : Ground G)
      → ⊢ g ok Φ
      → (ℓ : Label)
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ G ⊒ B
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ untag G ℓ p ⦂ ★ ⊒ B

    wt-seal : ∀ {α A B}{p : Down}
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B
      → Σ ∋ˢ α ⦂ B
      → α ∈conv Φ
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ seal p α ⦂ A ⊒ ｀ α

    wt-seal★ : ∀ {α A}{p : Down}
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ ★
      → Σ ∋ˢ α ⦂ ★
      → α ∈cast Φ
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ seal p α ⦂ A ⊒ ｀ α

    wt-↦ : ∀ {A A′ B B′}{p : Up}{q : Down}
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A′ ⊑ A
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ q ⦂ B ⊒ B′
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ (p ↦ q) ⦂ (A ⇒ B) ⊒ (A′ ⇒ B′)

    wt-∀ : ∀ {A B}{p : Down}
      → suc Δ ∣ Ψ ∣ (⟰ᵗ Σ) ∣ Φ ⊢ p ⦂ A ⊒ B
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ (∀ᵖ p) ⦂ `∀ A ⊒ `∀ B

    wt-ν : ∀ {A B}{p : Down}
      → Δ ∣ suc Ψ ∣ ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ p
          ⦂ (⇑ˢ B) ⊒ ((⇑ˢ A) [ ｀ zero ]ᵗ)
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ (ν p) ⦂ B ⊒ `∀ A

    wt-id : ∀ {A}
      → WfTy Δ Ψ A
      → Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ id A ⦂ A ⊒ A

Wt⊑ : TyCtx → SealCtx → Store → List CastPerm → Ty → Ty → Set
Wt⊑ Δ Ψ Σ Φ A B =
  Σ[ p ∈ Up ] (Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B)

Wt⊒ : TyCtx → SealCtx → Store → List CastPerm → Ty → Ty → Set
Wt⊒ Δ Ψ Σ Φ A B =
  Σ[ p ∈ Down ] (Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B)

------------------------------------------------------------------------
-- Endpoint well-formedness
------------------------------------------------------------------------

member-bound :
  ∀ {α Ψ}{Φ : List CastPerm} →
  length Φ ≡ Ψ →
  α ∈ Φ →
  α < Ψ
member-bound {Φ = []} len ()
member-bound {zero} {Ψ} {Φ = conv ∷ Φ} len here-conv =
  subst (λ n → zero < n) len z<s
member-bound {zero} {Ψ} {Φ = cast-seal ∷ Φ} len here-seal =
  subst (λ n → zero < n) len z<s
member-bound {suc α} {Ψ} {Φ = b ∷ Φ} len (there p) =
  subst (λ n → suc α < n) len (s<s (member-bound refl p))

tag-bound :
  ∀ {α Ψ}{Φ : List CastPerm} →
  length Φ ≡ Ψ →
  α ∈tag Φ →
  α < Ψ
tag-bound {Φ = []} len ()
tag-bound {zero} {Ψ} {Φ = cast-tag ∷ Φ} len here-tag-only =
  subst (λ n → zero < n) len z<s
tag-bound {suc α} {Ψ} {Φ = b ∷ Φ} len (there-tag p) =
  subst (λ n → suc α < n) len (s<s (tag-bound refl p))

ground-wf :
  ∀ {Δ Ψ Φ G} →
  length Φ ≡ Ψ →
  (g : Ground G) →
  ⊢ g ok Φ →
  WfTy Δ Ψ G
ground-wf len (｀ α) ok = wfSeal (tag-bound len ok)
ground-wf len (‵ ι) ok = wfBase
ground-wf len ★⇒★ ok = wf⇒ wf★ wf★

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

closeInline-openVarTy :
  ∀ (d : TyVar) (ov : OpenVar) →
  closeInlineAt d (openVarTy ov) ≡ ＇ (closeOpenVarAt d ov)
closeInline-openVarTy d (openVar X) = refl
closeInline-openVarTy d openSeal0 = refl

closeInline-openTyEnv :
  ∀ (d X : TyVar) →
  closeInlineAt d (openTyEnv d X) ≡ ＇ X
closeInline-openTyEnv d X =
  trans
    (closeInline-openVarTy d (openVarAt d X))
    (cong ＇_ (close-openVarAt d X))

openTyEnv-ext :
  ∀ (d X : TyVar) →
  extsᵗ (openTyEnv d) X ≡ openTyEnv (suc d) X
openTyEnv-ext d zero = refl
openTyEnv-ext d (suc X) with openVarAt d X
openTyEnv-ext d (suc X) | openVar Y = refl
openTyEnv-ext d (suc X) | openSeal0 = refl

singleSealTyEnv-ext :
  ∀ (d α : Seal) →
  extsˢᵗ (singleSealTyEnv (＇ d)) α ≡ singleSealTyEnv (＇ (suc d)) α
singleSealTyEnv-ext d zero = refl
singleSealTyEnv-ext d (suc α) = refl

closeVarAt-ext :
  ∀ (d X : TyVar) →
  closeVarAt (suc d) X ≡ extᵗ (closeVarAt d) X
closeVarAt-ext d zero = refl
closeVarAt-ext d (suc X) = refl

renameᵗ-closeVarAt-suc :
  ∀ (d : TyVar) (A : Ty) →
  renameᵗ (closeVarAt (suc d)) A ≡ renameᵗ (extᵗ (closeVarAt d)) A
renameᵗ-closeVarAt-suc d A = rename-cong (closeVarAt-ext d) A

closeInlineAt-suc :
  ∀ (d : TyVar) (A : Ty) →
  closeInlineAt (suc d) A ≡
  substˢᵗ (extsˢᵗ (singleSealTyEnv (＇ d))) (renameᵗ (extᵗ (closeVarAt d)) A)
closeInlineAt-suc d A =
  trans
    (cong (substˢᵗ (singleSealTyEnv (＇ (suc d)))) (renameᵗ-closeVarAt-suc d A))
    (sym (substˢᵗ-cong (singleSealTyEnv-ext d) (renameᵗ (extᵗ (closeVarAt d)) A)))

closeInline-open-at :
  ∀ (d : TyVar) (A : Ty) →
  closeInlineAt d (substᵗ (openTyEnv d) (⇑ˢ A)) ≡ A
closeInline-open-at d (＇ X) = closeInline-openTyEnv d X
closeInline-open-at d (｀ α) = refl
closeInline-open-at d (‵ ι) = refl
closeInline-open-at d ★ = refl
closeInline-open-at d (A ⇒ B) =
  cong₂ _⇒_ (closeInline-open-at d A) (closeInline-open-at d B)
closeInline-open-at d (`∀ A) =
  cong `∀
    (trans
      (cong
        (λ T →
          substˢᵗ
            (extsˢᵗ (singleSealTyEnv (＇ d)))
            (renameᵗ (extᵗ (closeVarAt d)) T))
        (substᵗ-cong (openTyEnv-ext d) (⇑ˢ A)))
      (trans
        (sym (closeInlineAt-suc d (substᵗ (openTyEnv (suc d)) (⇑ˢ A))))
        (closeInline-open-at (suc d) A)))

openTyEnv-zero :
  (X : TyVar) →
  openTyEnv zero X ≡ singleTyEnv (｀ zero) X
openTyEnv-zero zero = refl
openTyEnv-zero (suc X) = refl

closeInlineAt-zero-open :
  (A : Ty) →
  closeInlineAt zero ((⇑ˢ A) [ ｀ zero ]ᵗ) ≡ A
closeInlineAt-zero-open A =
  trans
    (cong (closeInlineAt zero) (sym (substᵗ-cong openTyEnv-zero (⇑ˢ A))))
    (closeInline-open-at zero A)

SealSubstTyWf : TyCtx → SealCtx → SealCtx → Substˢᵗ → Set
SealSubstTyWf Δ Ψ Ψ′ τ = ∀ {α} → α < Ψ → WfTy Δ Ψ′ (τ α)

SealSubstTyWf-extsᵗ :
  ∀ {Δ Ψ Ψ′ τ} →
  SealSubstTyWf Δ Ψ Ψ′ τ →
  SealSubstTyWf (suc Δ) Ψ Ψ′ (extsˢᵗ τ)
SealSubstTyWf-extsᵗ hτ α<Ψ =
  renameᵗ-preserves-WfTy (hτ α<Ψ) TyRenameWf-suc

substˢᵗ-preserves-WfTy :
  ∀ {Δ Ψ Ψ′ τ A} →
  WfTy Δ Ψ A →
  SealSubstTyWf Δ Ψ Ψ′ τ →
  WfTy Δ Ψ′ (substˢᵗ τ A)
substˢᵗ-preserves-WfTy (wfVar X<Δ) hτ = wfVar X<Δ
substˢᵗ-preserves-WfTy (wfSeal α<Ψ) hτ = hτ α<Ψ
substˢᵗ-preserves-WfTy wfBase hτ = wfBase
substˢᵗ-preserves-WfTy wf★ hτ = wf★
substˢᵗ-preserves-WfTy (wf⇒ hA hB) hτ =
  wf⇒ (substˢᵗ-preserves-WfTy hA hτ)
      (substˢᵗ-preserves-WfTy hB hτ)
substˢᵗ-preserves-WfTy (wf∀ hA) hτ =
  wf∀ (substˢᵗ-preserves-WfTy hA (SealSubstTyWf-extsᵗ hτ))

singleSealTyEnv-Wf :
  ∀ {Δ Ψ} d →
  d < Δ →
  SealSubstTyWf Δ (suc Ψ) Ψ (singleSealTyEnv (＇ d))
singleSealTyEnv-Wf d d<Δ {zero} z<s = wfVar d<Δ
singleSealTyEnv-Wf d d<Δ {suc α} (s<s α<Ψ) = wfSeal α<Ψ

closeVarAt-wf :
  ∀ {Δ X} d →
  d < suc Δ →
  X < Δ →
  closeVarAt d X < suc Δ
closeVarAt-wf zero d<sΔ X<Δ = s<s X<Δ
closeVarAt-wf (suc d) d<sΔ z<s = z<s
closeVarAt-wf {Δ = suc Δ} {X = suc X} (suc d) (s<s d<Δ) (s<s X<Δ) =
  s<s (closeVarAt-wf {Δ = Δ} {X = X} d d<Δ X<Δ)

closeVarAt-TyRenameWf :
  ∀ {Δ} d →
  d < suc Δ →
  TyRenameWf Δ (suc Δ) (closeVarAt d)
closeVarAt-TyRenameWf d d<sΔ X<Δ = closeVarAt-wf d d<sΔ X<Δ

closeInlineAt-preserves-WfTy :
  ∀ {Δ Ψ A} d →
  d < suc Δ →
  WfTy Δ (suc Ψ) A →
  WfTy (suc Δ) Ψ (closeInlineAt d A)
closeInlineAt-preserves-WfTy d d<sΔ hA =
  substˢᵗ-preserves-WfTy
    (renameᵗ-preserves-WfTy hA (closeVarAt-TyRenameWf d d<sΔ))
    (singleSealTyEnv-Wf d d<sΔ)

WfTy-ν-open-inv :
  ∀ {Δ Ψ A} →
  WfTy Δ (suc Ψ) ((⇑ˢ A) [ ｀ zero ]ᵗ) →
  WfTy (suc Δ) Ψ A
WfTy-ν-open-inv {A = A} hA =
  subst (WfTy _ _) (closeInlineAt-zero-open A)
    (closeInlineAt-preserves-WfTy zero z<s hA)

WfTy-⇑ˢ-inv :
  ∀ {Δ Ψ A} →
  WfTy Δ (suc Ψ) (⇑ˢ A) →
  WfTy Δ Ψ A
WfTy-⇑ˢ-inv {A = ＇ X} (wfVar X<Δ) = wfVar X<Δ
WfTy-⇑ˢ-inv {A = ｀ α} (wfSeal (s<s α<Ψ)) = wfSeal α<Ψ
WfTy-⇑ˢ-inv {A = ‵ ι} wfBase = wfBase
WfTy-⇑ˢ-inv {A = ★} wf★ = wf★
WfTy-⇑ˢ-inv {A = A ⇒ B} (wf⇒ hA hB) =
  wf⇒ (WfTy-⇑ˢ-inv hA) (WfTy-⇑ˢ-inv hB)
WfTy-⇑ˢ-inv {A = `∀ A} (wf∀ hA) = wf∀ (WfTy-⇑ˢ-inv hA)

mutual
  ⊑-src-wf :
    ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Up} →
    StoreWf Δ Ψ Σ →
    length Φ ≡ Ψ →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    WfTy Δ Ψ A
  ⊑-src-wf wfΣ lenΦ (wt-tag p g ok) = ⊑-src-wf wfΣ lenΦ p
  ⊑-src-wf wfΣ lenΦ (wt-unseal {α = α} h α∈Φ p) =
    wfSeal (member-bound lenΦ (∈conv⇒∈ α∈Φ))
  ⊑-src-wf wfΣ lenΦ (wt-unseal★ {α = α} h α∈Φ p) =
    wfSeal (member-bound lenΦ (∈cast⇒∈ α∈Φ))
  ⊑-src-wf wfΣ lenΦ (wt-↦ p q) =
    wf⇒ (⊒-tgt-wf wfΣ lenΦ p) (⊑-src-wf wfΣ lenΦ q)
  ⊑-src-wf wfΣ lenΦ (wt-∀ p) =
    wf∀ (⊑-src-wf (storeWf-⟰ᵗ wfΣ) lenΦ p)
  ⊑-src-wf wfΣ lenΦ (wt-ν p) =
    wf∀
      (WfTy-ν-open-inv
        (⊑-src-wf (storeWf-ν-ext wf★ wfΣ) (cong suc lenΦ) p))
  ⊑-src-wf wfΣ lenΦ (wt-id wfA) = wfA

  ⊑-tgt-wf :
    ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Up} →
    StoreWf Δ Ψ Σ →
    length Φ ≡ Ψ →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    WfTy Δ Ψ B
  ⊑-tgt-wf wfΣ lenΦ (wt-tag p g ok) = wf★
  ⊑-tgt-wf wfΣ lenΦ (wt-unseal h α∈Φ p) = ⊑-tgt-wf wfΣ lenΦ p
  ⊑-tgt-wf wfΣ lenΦ (wt-unseal★ h α∈Φ p) = ⊑-tgt-wf wfΣ lenΦ p
  ⊑-tgt-wf wfΣ lenΦ (wt-↦ p q) =
    wf⇒ (⊒-src-wf wfΣ lenΦ p) (⊑-tgt-wf wfΣ lenΦ q)
  ⊑-tgt-wf wfΣ lenΦ (wt-∀ p) =
    wf∀ (⊑-tgt-wf (storeWf-⟰ᵗ wfΣ) lenΦ p)
  ⊑-tgt-wf wfΣ lenΦ (wt-ν p) =
    WfTy-⇑ˢ-inv
      (⊑-tgt-wf (storeWf-ν-ext wf★ wfΣ) (cong suc lenΦ) p)
  ⊑-tgt-wf wfΣ lenΦ (wt-id wfA) = wfA

  ⊒-src-wf :
    ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Down} →
    StoreWf Δ Ψ Σ →
    length Φ ≡ Ψ →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    WfTy Δ Ψ A
  ⊒-src-wf wfΣ lenΦ (wt-untag g ok ℓ p) = wf★
  ⊒-src-wf wfΣ lenΦ (wt-seal p h α∈Φ) = ⊒-src-wf wfΣ lenΦ p
  ⊒-src-wf wfΣ lenΦ (wt-seal★ p h α∈Φ) = ⊒-src-wf wfΣ lenΦ p
  ⊒-src-wf wfΣ lenΦ (wt-↦ p q) =
    wf⇒ (⊑-tgt-wf wfΣ lenΦ p) (⊒-src-wf wfΣ lenΦ q)
  ⊒-src-wf wfΣ lenΦ (wt-∀ p) =
    wf∀ (⊒-src-wf (storeWf-⟰ᵗ wfΣ) lenΦ p)
  ⊒-src-wf wfΣ lenΦ (wt-ν p) =
    WfTy-⇑ˢ-inv
      (⊒-src-wf (storeWf-ν-ext wf★ wfΣ) (cong suc lenΦ) p)
  ⊒-src-wf wfΣ lenΦ (wt-id wfA) = wfA

  ⊒-tgt-wf :
    ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Down} →
    StoreWf Δ Ψ Σ →
    length Φ ≡ Ψ →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    WfTy Δ Ψ B
  ⊒-tgt-wf wfΣ lenΦ (wt-untag g ok ℓ p) = ⊒-tgt-wf wfΣ lenΦ p
  ⊒-tgt-wf wfΣ lenΦ (wt-seal {α = α} p h α∈Φ) =
    wfSeal (member-bound lenΦ (∈conv⇒∈ α∈Φ))
  ⊒-tgt-wf wfΣ lenΦ (wt-seal★ {α = α} p h α∈Φ) =
    wfSeal (member-bound lenΦ (∈cast⇒∈ α∈Φ))
  ⊒-tgt-wf wfΣ lenΦ (wt-↦ p q) =
    wf⇒ (⊑-src-wf wfΣ lenΦ p) (⊒-tgt-wf wfΣ lenΦ q)
  ⊒-tgt-wf wfΣ lenΦ (wt-∀ p) =
    wf∀ (⊒-tgt-wf (storeWf-⟰ᵗ wfΣ) lenΦ p)
  ⊒-tgt-wf wfΣ lenΦ (wt-ν p) =
    wf∀
      (WfTy-ν-open-inv
        (⊒-tgt-wf (storeWf-ν-ext wf★ wfΣ) (cong suc lenΦ) p))
  ⊒-tgt-wf wfΣ lenΦ (wt-id wfA) = wfA

------------------------------------------------------------------------
-- Endpoint alignment helpers
------------------------------------------------------------------------

closeν-inline :
  (A : Ty) →
  closeInlineAt zero A ≡ (⇑ᵗ A) [ ＇ zero ]ˢᵗ
closeν-inline A =
  cong (substˢᵗ (singleSealTyEnv (＇ zero))) (rename-cong (λ X → refl) A)

closeν-inline-open :
  (A : Ty) →
  (⇑ᵗ ((⇑ˢ A) [ ｀ zero ]ᵗ)) [ ＇ zero ]ˢᵗ ≡ A
closeν-inline-open A =
  trans
    (sym (closeν-inline ((⇑ˢ A) [ ｀ zero ]ᵗ)))
    (closeInlineAt-zero-open A)

mutual
  up-src-irrel :
    ∀ {Σ Σ′ : Store} →
    (p : Up) →
    up-src Σ p ≡ up-src Σ′ p
  up-src-irrel {Σ = Σ} {Σ′ = Σ′} (tag p G) =
    up-src-irrel {Σ = Σ} {Σ′ = Σ′} p
  up-src-irrel {Σ = Σ} {Σ′ = Σ′} (unseal α p) = refl
  up-src-irrel {Σ = Σ} {Σ′ = Σ′} (p ↦ q) =
    cong₂ _⇒_
      (down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} p)
      (up-src-irrel {Σ = Σ} {Σ′ = Σ′} q)
  up-src-irrel {Σ = Σ} {Σ′ = Σ′} (∀ᵖ p) =
    cong `∀ (up-src-irrel {Σ = ⟰ᵗ Σ} {Σ′ = ⟰ᵗ Σ′} p)
  up-src-irrel {Σ = Σ} {Σ′ = Σ′} (ν p) =
    cong `∀
      (cong (λ A → (⇑ᵗ A) [ ＇ zero ]ˢᵗ)
        (up-src-irrel
          {Σ = (zero , ★) ∷ ⟰ˢ Σ}
          {Σ′ = (zero , ★) ∷ ⟰ˢ Σ′}
          p))
  up-src-irrel {Σ = Σ} {Σ′ = Σ′} (id A) = refl

  down-tgt-irrel :
    ∀ {Σ Σ′ : Store} →
    (p : Down) →
    down-tgt Σ p ≡ down-tgt Σ′ p
  down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} (untag G ℓ p) =
    down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} p
  down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} (seal p α) = refl
  down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} (p ↦ q) =
    cong₂ _⇒_
      (up-src-irrel {Σ = Σ} {Σ′ = Σ′} p)
      (down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} q)
  down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} (∀ᵖ p) =
    cong `∀ (down-tgt-irrel {Σ = ⟰ᵗ Σ} {Σ′ = ⟰ᵗ Σ′} p)
  down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} (ν p) =
    cong `∀
      (cong (λ A → (⇑ᵗ A) [ ＇ zero ]ˢᵗ)
        (down-tgt-irrel
          {Σ = (zero , ⇑ˢ ★) ∷ ⟰ˢ Σ}
          {Σ′ = (zero , ⇑ˢ ★) ∷ ⟰ˢ Σ′}
          p))
  down-tgt-irrel {Σ = Σ} {Σ′ = Σ′} (id A) = refl

mutual
  up-src-align :
    ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Up} →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    up-src Σ p ≡ A
  up-src-align (wt-tag p g gok) = up-src-align p
  up-src-align (wt-unseal h α∈Φ p) = refl
  up-src-align (wt-unseal★ h α∈Φ p) = refl
  up-src-align (wt-↦ p q) =
    cong₂ _⇒_ (down-tgt-align p) (up-src-align q)
  up-src-align (wt-∀ p) = cong `∀ (up-src-align p)
  up-src-align (wt-ν {A = A} p) =
    cong `∀
      (trans
        (cong (λ B → (⇑ᵗ B) [ ＇ zero ]ˢᵗ) (up-src-align p))
        (closeν-inline-open A))
  up-src-align (wt-id wfA) = refl

  up-tgt-align :
    ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Up} →
    Uniqueˢ Σ →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    up-tgt Σ p ≡ B
  up-tgt-align uΣ (wt-tag p g gok) = refl
  up-tgt-align uΣ (wt-unseal h α∈Φ p) = up-tgt-align uΣ p
  up-tgt-align uΣ (wt-unseal★ h α∈Φ p) = up-tgt-align uΣ p
  up-tgt-align uΣ (wt-↦ p q) =
    cong₂ _⇒_ (down-src-align uΣ p) (up-tgt-align uΣ q)
  up-tgt-align uΣ (wt-∀ p) = cong `∀ (up-tgt-align (unique-⟰ᵗ uΣ) p)
  up-tgt-align uΣ (wt-ν {B = B} p) =
    trans
      (cong (renameˢ (singleSealEnv zero)) (up-tgt-align (unique-ν ★ uΣ) p))
      (renameˢ-single-⇑ˢ-id zero B)
  up-tgt-align uΣ (wt-id wfA) = refl

  down-src-align :
    ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Down} →
    Uniqueˢ Σ →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    down-src Σ p ≡ A
  down-src-align uΣ (wt-untag g gok ℓ p) = refl
  down-src-align uΣ (wt-seal p h α∈Φ) = down-src-align uΣ p
  down-src-align uΣ (wt-seal★ p h α∈Φ) = down-src-align uΣ p
  down-src-align uΣ (wt-↦ p q) =
    cong₂ _⇒_ (up-tgt-align uΣ p) (down-src-align uΣ q)
  down-src-align uΣ (wt-∀ p) = cong `∀ (down-src-align (unique-⟰ᵗ uΣ) p)
  down-src-align uΣ (wt-ν {B = B} p) =
    trans
      (cong (renameˢ (singleSealEnv zero)) (down-src-align (unique-ν (⇑ˢ ★) uΣ) p))
      (renameˢ-single-⇑ˢ-id zero B)
  down-src-align uΣ (wt-id wfA) = refl

  down-tgt-align :
    ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Down} →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    down-tgt Σ p ≡ B
  down-tgt-align (wt-untag g gok ℓ p) = down-tgt-align p
  down-tgt-align (wt-seal p h α∈Φ) = refl
  down-tgt-align (wt-seal★ p h α∈Φ) = refl
  down-tgt-align (wt-↦ p q) =
    cong₂ _⇒_ (up-src-align p) (down-tgt-align q)
  down-tgt-align (wt-∀ p) = cong `∀ (down-tgt-align p)
  down-tgt-align (wt-ν {A = A} p) =
    cong `∀
      (trans
        (cong (λ B → (⇑ᵗ B) [ ＇ zero ]ˢᵗ) (down-tgt-align p))
        (closeν-inline-open A))
  down-tgt-align (wt-id wfA) = refl

------------------------------------------------------------------------
-- Transport helpers
------------------------------------------------------------------------

RenOk : Renameˢ → List CastPerm → List CastPerm → Set
RenOk ρ P P′ = ∀ {α} → α ∈ P → ρ α ∈ P′

RenOkConv : Renameˢ → List CastPerm → List CastPerm → Set
RenOkConv ρ P P′ = ∀ {α} → α ∈conv P → ρ α ∈conv P′

RenOkCast : Renameˢ → List CastPerm → List CastPerm → Set
RenOkCast ρ P P′ = ∀ {α} → α ∈cast P → ρ α ∈cast P′

RenOkTag : Renameˢ → List CastPerm → List CastPerm → Set
RenOkTag ρ P P′ = ∀ {α} → α ∈tag P → ρ α ∈tag P′

RenNotIn : Renameˢ → List CastPerm → List CastPerm → Set
RenNotIn ρ P P′ = ∀ {α} → α ∉ P → ρ α ∉ P′

RenOk-id : ∀ {P : List CastPerm} → RenOk (λ α → α) P P
RenOk-id p = p

RenOkConv-id : ∀ {P : List CastPerm} → RenOkConv (λ α → α) P P
RenOkConv-id p = p

RenOkCast-id : ∀ {P : List CastPerm} → RenOkCast (λ α → α) P P
RenOkCast-id p = p

RenOkTag-id : ∀ {P : List CastPerm} → RenOkTag (λ α → α) P P
RenOkTag-id p = p

RenNotIn-id : ∀ {P : List CastPerm} → RenNotIn (λ α → α) P P
RenNotIn-id p = p

RenOk-every :
  ∀ {Ψ Ψ′} {ρ : Renameˢ} →
  SealRenameWf Ψ Ψ′ ρ →
  RenOk ρ (every Ψ) (every Ψ′)
RenOk-every hρ p = every-member _ (hρ (every-index p))

RenOkConv-every :
  ∀ {Ψ Ψ′} {ρ : Renameˢ} →
  SealRenameWf Ψ Ψ′ ρ →
  RenOkConv ρ (every Ψ) (every Ψ′)
RenOkConv-every hρ p = every-member-conv _ (hρ (every-index-conv p))

RenOkCast-every :
  ∀ {Ψ Ψ′} {ρ : Renameˢ} →
  SealRenameWf Ψ Ψ′ ρ →
  RenOkCast ρ (every Ψ) (every Ψ′)
RenOkCast-every hρ {α} p = ⊥-elim (every-excluded-cast α p)

RenOkTag-every :
  ∀ {Ψ Ψ′} {ρ : Renameˢ} →
  SealRenameWf Ψ Ψ′ ρ →
  RenOkTag ρ (every Ψ) (every Ψ′)
RenOkTag-every hρ {α} p = ⊥-elim (every-excluded-tag α p)

mapΦ-suc : List CastPerm → List CastPerm
mapΦ-suc Φ = cast-tag ∷ Φ

RenOk-suc : ∀ {Φ : List CastPerm} → RenOk suc Φ (mapΦ-suc Φ)
RenOk-suc p = there p

RenOkConv-suc : ∀ {Φ : List CastPerm} → RenOkConv suc Φ (mapΦ-suc Φ)
RenOkConv-suc p = there-conv p

RenOkCast-suc : ∀ {Φ : List CastPerm} → RenOkCast suc Φ (mapΦ-suc Φ)
RenOkCast-suc p = there-cast p

RenOkTag-suc : ∀ {Φ : List CastPerm} → RenOkTag suc Φ (mapΦ-suc Φ)
RenOkTag-suc p = there-tag p

RenNotIn-suc : ∀ {Φ : List CastPerm} → RenNotIn suc Φ (mapΦ-suc Φ)
RenNotIn-suc α∉ (there p) = α∉ p

RenOk-none : ∀ {Ψ Ψ′} → (ρ : Renameˢ) → RenOk ρ (none Ψ) (none Ψ′)
RenOk-none ρ {α} p = ⊥-elim (none-excluded α p)

RenOk-any-every :
  ∀ {Ψ′} {P : List CastPerm} →
  (ρ : Renameˢ) →
  RenOk ρ P (every Ψ′) →
  RenOk ρ P (every Ψ′)
RenOk-any-every ρ ok = ok

RenOk-ext-conv :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOk ρ P P′ →
  RenOk (extˢ ρ) (conv ∷ P) (conv ∷ P′)
RenOk-ext-conv ok {zero} here-conv = here-conv
RenOk-ext-conv ok {suc α} (there p) = there (ok p)

RenOk-ext-cast-seal :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOk ρ P P′ →
  RenOk (extˢ ρ) (cast-seal ∷ P) (cast-seal ∷ P′)
RenOk-ext-cast-seal ok {zero} here-seal = here-seal
RenOk-ext-cast-seal ok {suc α} (there p) = there (ok p)

RenOk-ext-cast-tag :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOk ρ P P′ →
  RenOk (extˢ ρ) (cast-tag ∷ P) (cast-tag ∷ P′)
RenOk-ext-cast-tag ok {zero} ()
RenOk-ext-cast-tag ok {suc α} (there p) = there (ok p)

RenOkConv-ext-conv :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOkConv ρ P P′ →
  RenOkConv (extˢ ρ) (conv ∷ P) (conv ∷ P′)
RenOkConv-ext-conv ok {zero} here-conv-only = here-conv-only
RenOkConv-ext-conv ok {suc α} (there-conv p) = there-conv (ok p)

RenOkConv-ext-cast-seal :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOkConv ρ P P′ →
  RenOkConv (extˢ ρ) (cast-seal ∷ P) (cast-seal ∷ P′)
RenOkConv-ext-cast-seal ok {zero} ()
RenOkConv-ext-cast-seal ok {suc α} (there-conv p) = there-conv (ok p)

RenOkConv-ext-cast-tag :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOkConv ρ P P′ →
  RenOkConv (extˢ ρ) (cast-tag ∷ P) (cast-tag ∷ P′)
RenOkConv-ext-cast-tag ok {zero} ()
RenOkConv-ext-cast-tag ok {suc α} (there-conv p) = there-conv (ok p)

RenOkCast-ext-conv :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOkCast ρ P P′ →
  RenOkCast (extˢ ρ) (conv ∷ P) (conv ∷ P′)
RenOkCast-ext-conv ok {zero} ()
RenOkCast-ext-conv ok {suc α} (there-cast p) = there-cast (ok p)

RenOkCast-ext-cast-seal :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOkCast ρ P P′ →
  RenOkCast (extˢ ρ) (cast-seal ∷ P) (cast-seal ∷ P′)
RenOkCast-ext-cast-seal ok {zero} here-cast-only = here-cast-only
RenOkCast-ext-cast-seal ok {suc α} (there-cast p) = there-cast (ok p)

RenOkCast-ext-cast-tag :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOkCast ρ P P′ →
  RenOkCast (extˢ ρ) (cast-tag ∷ P) (cast-tag ∷ P′)
RenOkCast-ext-cast-tag ok {zero} ()
RenOkCast-ext-cast-tag ok {suc α} (there-cast p) = there-cast (ok p)

RenOkTag-ext-conv :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOkTag ρ P P′ →
  RenOkTag (extˢ ρ) (conv ∷ P) (conv ∷ P′)
RenOkTag-ext-conv ok {zero} ()
RenOkTag-ext-conv ok {suc α} (there-tag p) = there-tag (ok p)

RenOkTag-ext-cast-seal :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOkTag ρ P P′ →
  RenOkTag (extˢ ρ) (cast-seal ∷ P) (cast-seal ∷ P′)
RenOkTag-ext-cast-seal ok {zero} ()
RenOkTag-ext-cast-seal ok {suc α} (there-tag p) = there-tag (ok p)

RenOkTag-ext-cast-tag :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOkTag ρ P P′ →
  RenOkTag (extˢ ρ) (cast-tag ∷ P) (cast-tag ∷ P′)
RenOkTag-ext-cast-tag ok {zero} here-tag-only = here-tag-only
RenOkTag-ext-cast-tag ok {suc α} (there-tag p) = there-tag (ok p)

RenNotIn-ext-conv :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenNotIn ρ P P′ →
  RenNotIn (extˢ ρ) (conv ∷ P) (conv ∷ P′)
RenNotIn-ext-conv ok {zero} α∉conv _ = α∉conv here-conv
RenNotIn-ext-conv ok {suc α} α∉conv (there p) =
  ok (λ α∈ → α∉conv (there α∈)) p

RenNotIn-ext-cast-seal :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenNotIn ρ P P′ →
  RenNotIn (extˢ ρ) (cast-seal ∷ P) (cast-seal ∷ P′)
RenNotIn-ext-cast-seal ok {zero} α∉seal _ = α∉seal here-seal
RenNotIn-ext-cast-seal ok {suc α} α∉seal (there p) =
  ok (λ α∈ → α∉seal (there α∈)) p

RenNotIn-ext-cast-tag :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenNotIn ρ P P′ →
  RenNotIn (extˢ ρ) (cast-tag ∷ P) (cast-tag ∷ P′)
RenNotIn-ext-cast-tag ok {zero} α∉tag ()
RenNotIn-ext-cast-tag ok {suc α} α∉tag (there p) =
  ok (λ α∈ → α∉tag (there α∈)) p

RenOk-singleSealEnv-conv :
  ∀ {P : List CastPerm} {α : Seal} →
  α ∈ P →
  RenOk (singleSealEnv α) (conv ∷ P) P
RenOk-singleSealEnv-conv α∈P here-conv = α∈P
RenOk-singleSealEnv-conv α∈P (there p) = p

RenOk-singleSealEnv-cast-seal :
  ∀ {P : List CastPerm} {α : Seal} →
  α ∈ P →
  RenOk (singleSealEnv α) (cast-seal ∷ P) P
RenOk-singleSealEnv-cast-seal α∈P here-seal = α∈P
RenOk-singleSealEnv-cast-seal α∈P (there p) = p

RenOk-singleSealEnv-cast-tag :
  ∀ {P : List CastPerm} {α : Seal} →
  RenOk (singleSealEnv α) (cast-tag ∷ P) P
RenOk-singleSealEnv-cast-tag {P = P} {α = α} {zero} ()
RenOk-singleSealEnv-cast-tag {P = P} {α = α} {suc β} (there p) = p

RenOkConv-singleSealEnv-conv :
  ∀ {P : List CastPerm} {α : Seal} →
  α ∈conv P →
  RenOkConv (singleSealEnv α) (conv ∷ P) P
RenOkConv-singleSealEnv-conv α∈P here-conv-only = α∈P
RenOkConv-singleSealEnv-conv α∈P (there-conv p) = p

RenOkCast-singleSealEnv-cast-seal :
  ∀ {P : List CastPerm} {α : Seal} →
  α ∈cast P →
  RenOkCast (singleSealEnv α) (cast-seal ∷ P) P
RenOkCast-singleSealEnv-cast-seal α∈P here-cast-only = α∈P
RenOkCast-singleSealEnv-cast-seal α∈P (there-cast p) = p

renameᵗ-ground-ok :
  ∀ {G : Ty}
  (ρ : Renameᵗ) (g : Ground G) {Φ : List CastPerm} →
  ⊢ g ok Φ →
  ⊢ renameᵗ-ground ρ g ok Φ
renameᵗ-ground-ok ρ (｀ α) gok = gok
renameᵗ-ground-ok ρ (‵ ι) gok = gok
renameᵗ-ground-ok ρ ★⇒★ gok = gok

substᵗ-ground-ok :
  ∀ {G : Ty}
  (σ : Substᵗ) (g : Ground G) {Φ : List CastPerm} →
  ⊢ g ok Φ →
  ⊢ substᵗ-ground σ g ok Φ
substᵗ-ground-ok σ (｀ α) gok = gok
substᵗ-ground-ok σ (‵ ι) gok = gok
substᵗ-ground-ok σ ★⇒★ gok = gok

renameˢ-ground-ok :
  ∀ {G : Ty}
  (ρ : Renameˢ) {Φ Φ′ : List CastPerm} →
  RenOkTag ρ Φ Φ′ →
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
  rename⊑ᵗ ρ (tag p G) = tag (rename⊑ᵗ ρ p) (renameᵗ ρ G)
  rename⊑ᵗ ρ (unseal α p) = unseal α (rename⊑ᵗ ρ p)
  rename⊑ᵗ ρ (p ↦ q) = rename⊒ᵗ ρ p ↦ rename⊑ᵗ ρ q
  rename⊑ᵗ ρ (∀ᵖ p) = ∀ᵖ (rename⊑ᵗ (extᵗ ρ) p)
  rename⊑ᵗ ρ (ν p) = ν (rename⊑ᵗ ρ p)
  rename⊑ᵗ ρ (id A) = id (renameᵗ ρ A)

  rename⊒ᵗ : (ρ : Renameᵗ) → Down → Down
  rename⊒ᵗ ρ (untag G ℓ p) = untag (renameᵗ ρ G) ℓ (rename⊒ᵗ ρ p)
  rename⊒ᵗ ρ (seal p α) = seal (rename⊒ᵗ ρ p) α
  rename⊒ᵗ ρ (p ↦ q) = rename⊑ᵗ ρ p ↦ rename⊒ᵗ ρ q
  rename⊒ᵗ ρ (∀ᵖ p) = ∀ᵖ (rename⊒ᵗ (extᵗ ρ) p)
  rename⊒ᵗ ρ (ν p) = ν (rename⊒ᵗ ρ p)
  rename⊒ᵗ ρ (id A) = id (renameᵗ ρ A)

mutual
  rename⊑ˢ : (ρ : Renameˢ) → Up → Up
  rename⊑ˢ ρ (tag p G) = tag (rename⊑ˢ ρ p) (renameˢ ρ G)
  rename⊑ˢ ρ (unseal α p) = unseal (ρ α) (rename⊑ˢ ρ p)
  rename⊑ˢ ρ (p ↦ q) = rename⊒ˢ ρ p ↦ rename⊑ˢ ρ q
  rename⊑ˢ ρ (∀ᵖ p) = ∀ᵖ (rename⊑ˢ ρ p)
  rename⊑ˢ ρ (ν p) = ν (rename⊑ˢ (extˢ ρ) p)
  rename⊑ˢ ρ (id A) = id (renameˢ ρ A)

  rename⊒ˢ : (ρ : Renameˢ) → Down → Down
  rename⊒ˢ ρ (untag G ℓ p) = untag (renameˢ ρ G) ℓ (rename⊒ˢ ρ p)
  rename⊒ˢ ρ (seal p α) = seal (rename⊒ˢ ρ p) (ρ α)
  rename⊒ˢ ρ (p ↦ q) = rename⊑ˢ ρ p ↦ rename⊒ˢ ρ q
  rename⊒ˢ ρ (∀ᵖ p) = ∀ᵖ (rename⊒ˢ ρ p)
  rename⊒ˢ ρ (ν p) = ν (rename⊒ˢ (extˢ ρ) p)
  rename⊒ˢ ρ (id A) = id (renameˢ ρ A)

mutual
  subst⊑ᵗ : (σ : Substᵗ) → Up → Up
  subst⊑ᵗ σ (tag p G) = tag (subst⊑ᵗ σ p) (substᵗ σ G)
  subst⊑ᵗ σ (unseal α p) = unseal α (subst⊑ᵗ σ p)
  subst⊑ᵗ σ (p ↦ q) = subst⊒ᵗ σ p ↦ subst⊑ᵗ σ q
  subst⊑ᵗ σ (∀ᵖ p) = ∀ᵖ (subst⊑ᵗ (extsᵗ σ) p)
  subst⊑ᵗ σ (ν p) = ν (subst⊑ᵗ (liftSubstˢ σ) p)
  subst⊑ᵗ σ (id A) = id (substᵗ σ A)

  subst⊒ᵗ : (σ : Substᵗ) → Down → Down
  subst⊒ᵗ σ (untag G ℓ p) = untag (substᵗ σ G) ℓ (subst⊒ᵗ σ p)
  subst⊒ᵗ σ (seal p α) = seal (subst⊒ᵗ σ p) α
  subst⊒ᵗ σ (p ↦ q) = subst⊑ᵗ σ p ↦ subst⊒ᵗ σ q
  subst⊒ᵗ σ (∀ᵖ p) = ∀ᵖ (subst⊒ᵗ (extsᵗ σ) p)
  subst⊒ᵗ σ (ν p) = ν (subst⊒ᵗ (liftSubstˢ σ) p)
  subst⊒ᵗ σ (id A) = id (substᵗ σ A)

------------------------------------------------------------------------
-- Raw coercion substitution algebra
------------------------------------------------------------------------

mutual
  rename⊑ᵗ-cong :
    ∀ {ρ ρ′ : Renameᵗ} →
    ((X : TyVar) → ρ X ≡ ρ′ X) →
    (p : Up) →
    rename⊑ᵗ ρ p ≡ rename⊑ᵗ ρ′ p
  rename⊑ᵗ-cong h (tag p G) = cong₂ tag (rename⊑ᵗ-cong h p) (rename-cong h G)
  rename⊑ᵗ-cong h (unseal α p) = cong (unseal α) (rename⊑ᵗ-cong h p)
  rename⊑ᵗ-cong h (p ↦ q) =
    cong₂ _↦_ (rename⊒ᵗ-cong h p) (rename⊑ᵗ-cong h q)
  rename⊑ᵗ-cong h (∀ᵖ p) = cong ∀ᵖ (rename⊑ᵗ-cong h-ext p)
    where
    h-ext : (X : TyVar) → extᵗ _ X ≡ extᵗ _ X
    h-ext zero = refl
    h-ext (suc X) = cong suc (h X)
  rename⊑ᵗ-cong h (ν p) = cong ν_ (rename⊑ᵗ-cong h p)
  rename⊑ᵗ-cong h (id A) = cong id (rename-cong h A)

  rename⊒ᵗ-cong :
    ∀ {ρ ρ′ : Renameᵗ} →
    ((X : TyVar) → ρ X ≡ ρ′ X) →
    (p : Down) →
    rename⊒ᵗ ρ p ≡ rename⊒ᵗ ρ′ p
  rename⊒ᵗ-cong h (untag G ℓ p) =
    cong₂ (λ T q → untag T ℓ q) (rename-cong h G) (rename⊒ᵗ-cong h p)
  rename⊒ᵗ-cong h (seal p α) = cong (λ q → seal q α) (rename⊒ᵗ-cong h p)
  rename⊒ᵗ-cong h (p ↦ q) =
    cong₂ _↦_ (rename⊑ᵗ-cong h p) (rename⊒ᵗ-cong h q)
  rename⊒ᵗ-cong h (∀ᵖ p) = cong ∀ᵖ (rename⊒ᵗ-cong h-ext p)
    where
    h-ext : (X : TyVar) → extᵗ _ X ≡ extᵗ _ X
    h-ext zero = refl
    h-ext (suc X) = cong suc (h X)
  rename⊒ᵗ-cong h (ν p) = cong ν_ (rename⊒ᵗ-cong h p)
  rename⊒ᵗ-cong h (id A) = cong id (rename-cong h A)

mutual
  subst⊑ᵗ-cong :
    ∀ {σ τ : Substᵗ} →
    ((X : TyVar) → σ X ≡ τ X) →
    (p : Up) →
    subst⊑ᵗ σ p ≡ subst⊑ᵗ τ p
  subst⊑ᵗ-cong h (tag p G) = cong₂ tag (subst⊑ᵗ-cong h p) (substᵗ-cong h G)
  subst⊑ᵗ-cong h (unseal α p) = cong (unseal α) (subst⊑ᵗ-cong h p)
  subst⊑ᵗ-cong h (p ↦ q) =
    cong₂ _↦_ (subst⊒ᵗ-cong h p) (subst⊑ᵗ-cong h q)
  subst⊑ᵗ-cong {σ = σ} {τ = τ} h (∀ᵖ p) =
    cong ∀ᵖ (subst⊑ᵗ-cong h-ext p)
    where
    h-ext : (X : TyVar) → extsᵗ σ X ≡ extsᵗ τ X
    h-ext zero = refl
    h-ext (suc X) = cong (renameᵗ suc) (h X)
  subst⊑ᵗ-cong {σ = σ} {τ = τ} h (ν p) =
    cong ν_ (subst⊑ᵗ-cong h-lift p)
    where
    h-lift : (X : TyVar) → liftSubstˢ σ X ≡ liftSubstˢ τ X
    h-lift X = cong ⇑ˢ (h X)
  subst⊑ᵗ-cong h (id A) = cong id (substᵗ-cong h A)

  subst⊒ᵗ-cong :
    ∀ {σ τ : Substᵗ} →
    ((X : TyVar) → σ X ≡ τ X) →
    (p : Down) →
    subst⊒ᵗ σ p ≡ subst⊒ᵗ τ p
  subst⊒ᵗ-cong h (untag G ℓ p) =
    cong₂ (λ T q → untag T ℓ q) (substᵗ-cong h G) (subst⊒ᵗ-cong h p)
  subst⊒ᵗ-cong h (seal p α) = cong (λ q → seal q α) (subst⊒ᵗ-cong h p)
  subst⊒ᵗ-cong h (p ↦ q) =
    cong₂ _↦_ (subst⊑ᵗ-cong h p) (subst⊒ᵗ-cong h q)
  subst⊒ᵗ-cong {σ = σ} {τ = τ} h (∀ᵖ p) =
    cong ∀ᵖ (subst⊒ᵗ-cong h-ext p)
    where
    h-ext : (X : TyVar) → extsᵗ σ X ≡ extsᵗ τ X
    h-ext zero = refl
    h-ext (suc X) = cong (renameᵗ suc) (h X)
  subst⊒ᵗ-cong {σ = σ} {τ = τ} h (ν p) =
    cong ν_ (subst⊒ᵗ-cong h-lift p)
    where
    h-lift : (X : TyVar) → liftSubstˢ σ X ≡ liftSubstˢ τ X
    h-lift X = cong ⇑ˢ (h X)
  subst⊒ᵗ-cong h (id A) = cong id (substᵗ-cong h A)

mutual
  rename⊑ᵗ-rename⊑ᵗ :
    (ρ₁ ρ₂ : Renameᵗ) (p : Up) →
    rename⊑ᵗ ρ₂ (rename⊑ᵗ ρ₁ p) ≡
    rename⊑ᵗ (λ X → ρ₂ (ρ₁ X)) p
  rename⊑ᵗ-rename⊑ᵗ ρ₁ ρ₂ (tag p G) =
    cong₂ tag
      (rename⊑ᵗ-rename⊑ᵗ ρ₁ ρ₂ p)
      (renameᵗ-compose ρ₁ ρ₂ G)
  rename⊑ᵗ-rename⊑ᵗ ρ₁ ρ₂ (unseal α p) =
    cong (unseal α) (rename⊑ᵗ-rename⊑ᵗ ρ₁ ρ₂ p)
  rename⊑ᵗ-rename⊑ᵗ ρ₁ ρ₂ (p ↦ q) =
    cong₂ _↦_
      (rename⊒ᵗ-rename⊒ᵗ ρ₁ ρ₂ p)
      (rename⊑ᵗ-rename⊑ᵗ ρ₁ ρ₂ q)
  rename⊑ᵗ-rename⊑ᵗ ρ₁ ρ₂ (∀ᵖ p) =
    cong ∀ᵖ
      (trans
        (rename⊑ᵗ-rename⊑ᵗ (extᵗ ρ₁) (extᵗ ρ₂) p)
        (rename⊑ᵗ-cong env p))
    where
    env : (X : TyVar) →
      extᵗ ρ₂ (extᵗ ρ₁ X) ≡ extᵗ (λ Y → ρ₂ (ρ₁ Y)) X
    env zero = refl
    env (suc X) = refl
  rename⊑ᵗ-rename⊑ᵗ ρ₁ ρ₂ (ν p) =
    cong ν_ (rename⊑ᵗ-rename⊑ᵗ ρ₁ ρ₂ p)
  rename⊑ᵗ-rename⊑ᵗ ρ₁ ρ₂ (id A) =
    cong id (renameᵗ-compose ρ₁ ρ₂ A)

  rename⊒ᵗ-rename⊒ᵗ :
    (ρ₁ ρ₂ : Renameᵗ) (p : Down) →
    rename⊒ᵗ ρ₂ (rename⊒ᵗ ρ₁ p) ≡
    rename⊒ᵗ (λ X → ρ₂ (ρ₁ X)) p
  rename⊒ᵗ-rename⊒ᵗ ρ₁ ρ₂ (untag G ℓ p) =
    cong₂ (λ T q → untag T ℓ q)
      (renameᵗ-compose ρ₁ ρ₂ G)
      (rename⊒ᵗ-rename⊒ᵗ ρ₁ ρ₂ p)
  rename⊒ᵗ-rename⊒ᵗ ρ₁ ρ₂ (seal p α) =
    cong (λ q → seal q α) (rename⊒ᵗ-rename⊒ᵗ ρ₁ ρ₂ p)
  rename⊒ᵗ-rename⊒ᵗ ρ₁ ρ₂ (p ↦ q) =
    cong₂ _↦_
      (rename⊑ᵗ-rename⊑ᵗ ρ₁ ρ₂ p)
      (rename⊒ᵗ-rename⊒ᵗ ρ₁ ρ₂ q)
  rename⊒ᵗ-rename⊒ᵗ ρ₁ ρ₂ (∀ᵖ p) =
    cong ∀ᵖ
      (trans
        (rename⊒ᵗ-rename⊒ᵗ (extᵗ ρ₁) (extᵗ ρ₂) p)
        (rename⊒ᵗ-cong env p))
    where
    env : (X : TyVar) →
      extᵗ ρ₂ (extᵗ ρ₁ X) ≡ extᵗ (λ Y → ρ₂ (ρ₁ Y)) X
    env zero = refl
    env (suc X) = refl
  rename⊒ᵗ-rename⊒ᵗ ρ₁ ρ₂ (ν p) =
    cong ν_ (rename⊒ᵗ-rename⊒ᵗ ρ₁ ρ₂ p)
  rename⊒ᵗ-rename⊒ᵗ ρ₁ ρ₂ (id A) =
    cong id (renameᵗ-compose ρ₁ ρ₂ A)

mutual
  subst⊑ᵗ-rename⊑ᵗ :
    (ρ : Renameᵗ) (σ : Substᵗ) (p : Up) →
    subst⊑ᵗ σ (rename⊑ᵗ ρ p) ≡
    subst⊑ᵗ (λ X → σ (ρ X)) p
  subst⊑ᵗ-rename⊑ᵗ ρ σ (tag p G) =
    cong₂ tag
      (subst⊑ᵗ-rename⊑ᵗ ρ σ p)
      (substᵗ-renameᵗ ρ σ G)
  subst⊑ᵗ-rename⊑ᵗ ρ σ (unseal α p) =
    cong (unseal α) (subst⊑ᵗ-rename⊑ᵗ ρ σ p)
  subst⊑ᵗ-rename⊑ᵗ ρ σ (p ↦ q) =
    cong₂ _↦_
      (subst⊒ᵗ-rename⊒ᵗ ρ σ p)
      (subst⊑ᵗ-rename⊑ᵗ ρ σ q)
  subst⊑ᵗ-rename⊑ᵗ ρ σ (∀ᵖ p) =
    cong ∀ᵖ
      (trans
        (subst⊑ᵗ-rename⊑ᵗ (extᵗ ρ) (extsᵗ σ) p)
        (subst⊑ᵗ-cong env p))
    where
    env : (X : TyVar) →
      extsᵗ σ (extᵗ ρ X) ≡ extsᵗ (λ Y → σ (ρ Y)) X
    env zero = refl
    env (suc X) = refl
  subst⊑ᵗ-rename⊑ᵗ ρ σ (ν p) =
    cong ν_ (subst⊑ᵗ-rename⊑ᵗ ρ (liftSubstˢ σ) p)
  subst⊑ᵗ-rename⊑ᵗ ρ σ (id A) =
    cong id (substᵗ-renameᵗ ρ σ A)

  subst⊒ᵗ-rename⊒ᵗ :
    (ρ : Renameᵗ) (σ : Substᵗ) (p : Down) →
    subst⊒ᵗ σ (rename⊒ᵗ ρ p) ≡
    subst⊒ᵗ (λ X → σ (ρ X)) p
  subst⊒ᵗ-rename⊒ᵗ ρ σ (untag G ℓ p) =
    cong₂ (λ T q → untag T ℓ q)
      (substᵗ-renameᵗ ρ σ G)
      (subst⊒ᵗ-rename⊒ᵗ ρ σ p)
  subst⊒ᵗ-rename⊒ᵗ ρ σ (seal p α) =
    cong (λ q → seal q α) (subst⊒ᵗ-rename⊒ᵗ ρ σ p)
  subst⊒ᵗ-rename⊒ᵗ ρ σ (p ↦ q) =
    cong₂ _↦_
      (subst⊑ᵗ-rename⊑ᵗ ρ σ p)
      (subst⊒ᵗ-rename⊒ᵗ ρ σ q)
  subst⊒ᵗ-rename⊒ᵗ ρ σ (∀ᵖ p) =
    cong ∀ᵖ
      (trans
        (subst⊒ᵗ-rename⊒ᵗ (extᵗ ρ) (extsᵗ σ) p)
        (subst⊒ᵗ-cong env p))
    where
    env : (X : TyVar) →
      extsᵗ σ (extᵗ ρ X) ≡ extsᵗ (λ Y → σ (ρ Y)) X
    env zero = refl
    env (suc X) = refl
  subst⊒ᵗ-rename⊒ᵗ ρ σ (ν p) =
    cong ν_ (subst⊒ᵗ-rename⊒ᵗ ρ (liftSubstˢ σ) p)
  subst⊒ᵗ-rename⊒ᵗ ρ σ (id A) =
    cong id (substᵗ-renameᵗ ρ σ A)

mutual
  rename⊑ᵗ-subst⊑ᵗ :
    (ρ : Renameᵗ) (σ : Substᵗ) (p : Up) →
    rename⊑ᵗ ρ (subst⊑ᵗ σ p) ≡
    subst⊑ᵗ (λ X → renameᵗ ρ (σ X)) p
  rename⊑ᵗ-subst⊑ᵗ ρ σ (tag p G) =
    cong₂ tag
      (rename⊑ᵗ-subst⊑ᵗ ρ σ p)
      (renameᵗ-substᵗ ρ σ G)
  rename⊑ᵗ-subst⊑ᵗ ρ σ (unseal α p) =
    cong (unseal α) (rename⊑ᵗ-subst⊑ᵗ ρ σ p)
  rename⊑ᵗ-subst⊑ᵗ ρ σ (p ↦ q) =
    cong₂ _↦_
      (rename⊒ᵗ-subst⊒ᵗ ρ σ p)
      (rename⊑ᵗ-subst⊑ᵗ ρ σ q)
  rename⊑ᵗ-subst⊑ᵗ ρ σ (∀ᵖ p) =
    cong ∀ᵖ
      (trans
        (rename⊑ᵗ-subst⊑ᵗ (extᵗ ρ) (extsᵗ σ) p)
        (subst⊑ᵗ-cong env p))
    where
    env : (X : TyVar) →
      renameᵗ (extᵗ ρ) (extsᵗ σ X) ≡
      extsᵗ (λ Y → renameᵗ ρ (σ Y)) X
    env zero = refl
    env (suc X) = sym (renameᵗ-suc-comm ρ (σ X))
  rename⊑ᵗ-subst⊑ᵗ ρ σ (ν p) =
    cong ν_
      (trans
        (rename⊑ᵗ-subst⊑ᵗ ρ (liftSubstˢ σ) p)
        (subst⊑ᵗ-cong env p))
    where
    env : (X : TyVar) →
      renameᵗ ρ (liftSubstˢ σ X) ≡
      liftSubstˢ (λ Y → renameᵗ ρ (σ Y)) X
    env X = renameᵗ-⇑ˢ ρ (σ X)
  rename⊑ᵗ-subst⊑ᵗ ρ σ (id A) =
    cong id (renameᵗ-substᵗ ρ σ A)

  rename⊒ᵗ-subst⊒ᵗ :
    (ρ : Renameᵗ) (σ : Substᵗ) (p : Down) →
    rename⊒ᵗ ρ (subst⊒ᵗ σ p) ≡
    subst⊒ᵗ (λ X → renameᵗ ρ (σ X)) p
  rename⊒ᵗ-subst⊒ᵗ ρ σ (untag G ℓ p) =
    cong₂ (λ T q → untag T ℓ q)
      (renameᵗ-substᵗ ρ σ G)
      (rename⊒ᵗ-subst⊒ᵗ ρ σ p)
  rename⊒ᵗ-subst⊒ᵗ ρ σ (seal p α) =
    cong (λ q → seal q α) (rename⊒ᵗ-subst⊒ᵗ ρ σ p)
  rename⊒ᵗ-subst⊒ᵗ ρ σ (p ↦ q) =
    cong₂ _↦_
      (rename⊑ᵗ-subst⊑ᵗ ρ σ p)
      (rename⊒ᵗ-subst⊒ᵗ ρ σ q)
  rename⊒ᵗ-subst⊒ᵗ ρ σ (∀ᵖ p) =
    cong ∀ᵖ
      (trans
        (rename⊒ᵗ-subst⊒ᵗ (extᵗ ρ) (extsᵗ σ) p)
        (subst⊒ᵗ-cong env p))
    where
    env : (X : TyVar) →
      renameᵗ (extᵗ ρ) (extsᵗ σ X) ≡
      extsᵗ (λ Y → renameᵗ ρ (σ Y)) X
    env zero = refl
    env (suc X) = sym (renameᵗ-suc-comm ρ (σ X))
  rename⊒ᵗ-subst⊒ᵗ ρ σ (ν p) =
    cong ν_
      (trans
        (rename⊒ᵗ-subst⊒ᵗ ρ (liftSubstˢ σ) p)
        (subst⊒ᵗ-cong env p))
    where
    env : (X : TyVar) →
      renameᵗ ρ (liftSubstˢ σ X) ≡
      liftSubstˢ (λ Y → renameᵗ ρ (σ Y)) X
    env X = renameᵗ-⇑ˢ ρ (σ X)
  rename⊒ᵗ-subst⊒ᵗ ρ σ (id A) =
    cong id (renameᵗ-substᵗ ρ σ A)

subst⊑ᵗ-suc-rename⊑ᵗ-suc :
  (σ : Substᵗ) (p : Up) →
  subst⊑ᵗ (extsᵗ σ) (rename⊑ᵗ suc p) ≡
  rename⊑ᵗ suc (subst⊑ᵗ σ p)
subst⊑ᵗ-suc-rename⊑ᵗ-suc σ p =
  trans
    (subst⊑ᵗ-rename⊑ᵗ suc (extsᵗ σ) p)
    (sym (rename⊑ᵗ-subst⊑ᵗ suc σ p))

subst⊒ᵗ-suc-rename⊒ᵗ-suc :
  (σ : Substᵗ) (p : Down) →
  subst⊒ᵗ (extsᵗ σ) (rename⊒ᵗ suc p) ≡
  rename⊒ᵗ suc (subst⊒ᵗ σ p)
subst⊒ᵗ-suc-rename⊒ᵗ-suc σ p =
  trans
    (subst⊒ᵗ-rename⊒ᵗ suc (extsᵗ σ) p)
    (sym (rename⊒ᵗ-subst⊒ᵗ suc σ p))

mutual
  subst⊑ᵗ-subst⊑ᵗ :
    (τ σ : Substᵗ) (p : Up) →
    subst⊑ᵗ τ (subst⊑ᵗ σ p) ≡
    subst⊑ᵗ (λ X → substᵗ τ (σ X)) p
  subst⊑ᵗ-subst⊑ᵗ τ σ (tag p G) =
    cong₂ tag
      (subst⊑ᵗ-subst⊑ᵗ τ σ p)
      (substᵗ-substᵗ τ σ G)
  subst⊑ᵗ-subst⊑ᵗ τ σ (unseal α p) =
    cong (unseal α) (subst⊑ᵗ-subst⊑ᵗ τ σ p)
  subst⊑ᵗ-subst⊑ᵗ τ σ (p ↦ q) =
    cong₂ _↦_
      (subst⊒ᵗ-subst⊒ᵗ τ σ p)
      (subst⊑ᵗ-subst⊑ᵗ τ σ q)
  subst⊑ᵗ-subst⊑ᵗ τ σ (∀ᵖ p) =
    cong ∀ᵖ
      (trans
        (subst⊑ᵗ-subst⊑ᵗ (extsᵗ τ) (extsᵗ σ) p)
        (subst⊑ᵗ-cong env p))
    where
    env : (X : TyVar) →
      substᵗ (extsᵗ τ) (extsᵗ σ X) ≡
      extsᵗ (λ Y → substᵗ τ (σ Y)) X
    env zero = refl
    env (suc X) = substᵗ-suc-renameᵗ-suc τ (σ X)
  subst⊑ᵗ-subst⊑ᵗ τ σ (ν p) =
    cong ν_
      (trans
        (subst⊑ᵗ-subst⊑ᵗ (liftSubstˢ τ) (liftSubstˢ σ) p)
        (subst⊑ᵗ-cong env p))
    where
    env : (X : TyVar) →
      substᵗ (liftSubstˢ τ) (liftSubstˢ σ X) ≡
      liftSubstˢ (λ Y → substᵗ τ (σ Y)) X
    env X = substᵗ-⇑ˢ τ (σ X)
  subst⊑ᵗ-subst⊑ᵗ τ σ (id A) =
    cong id (substᵗ-substᵗ τ σ A)

  subst⊒ᵗ-subst⊒ᵗ :
    (τ σ : Substᵗ) (p : Down) →
    subst⊒ᵗ τ (subst⊒ᵗ σ p) ≡
    subst⊒ᵗ (λ X → substᵗ τ (σ X)) p
  subst⊒ᵗ-subst⊒ᵗ τ σ (untag G ℓ p) =
    cong₂ (λ T q → untag T ℓ q)
      (substᵗ-substᵗ τ σ G)
      (subst⊒ᵗ-subst⊒ᵗ τ σ p)
  subst⊒ᵗ-subst⊒ᵗ τ σ (seal p α) =
    cong (λ q → seal q α) (subst⊒ᵗ-subst⊒ᵗ τ σ p)
  subst⊒ᵗ-subst⊒ᵗ τ σ (p ↦ q) =
    cong₂ _↦_
      (subst⊑ᵗ-subst⊑ᵗ τ σ p)
      (subst⊒ᵗ-subst⊒ᵗ τ σ q)
  subst⊒ᵗ-subst⊒ᵗ τ σ (∀ᵖ p) =
    cong ∀ᵖ
      (trans
        (subst⊒ᵗ-subst⊒ᵗ (extsᵗ τ) (extsᵗ σ) p)
        (subst⊒ᵗ-cong env p))
    where
    env : (X : TyVar) →
      substᵗ (extsᵗ τ) (extsᵗ σ X) ≡
      extsᵗ (λ Y → substᵗ τ (σ Y)) X
    env zero = refl
    env (suc X) = substᵗ-suc-renameᵗ-suc τ (σ X)
  subst⊒ᵗ-subst⊒ᵗ τ σ (ν p) =
    cong ν_
      (trans
        (subst⊒ᵗ-subst⊒ᵗ (liftSubstˢ τ) (liftSubstˢ σ) p)
        (subst⊒ᵗ-cong env p))
    where
    env : (X : TyVar) →
      substᵗ (liftSubstˢ τ) (liftSubstˢ σ X) ≡
      liftSubstˢ (λ Y → substᵗ τ (σ Y)) X
    env X = substᵗ-⇑ˢ τ (σ X)
  subst⊒ᵗ-subst⊒ᵗ τ σ (id A) =
    cong id (substᵗ-substᵗ τ σ A)

infixl 8 _[_]⊑
_[_]⊑ : Up → Seal → Up
p [ α ]⊑ = rename⊑ˢ (singleSealEnv α) p

infixl 8 _[_]⊒
_[_]⊒ : Down → Seal → Down
p [ α ]⊒ = rename⊒ˢ (singleSealEnv α) p


------------------------------------------------------------------------
-- Typed-judgment transport helpers
------------------------------------------------------------------------

castWt⊑ :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{Φ Φ′ : List CastPerm}{A B : Ty}{p : Up} →
  Σ ≡ Σ′ →
  Φ ≡ Φ′ →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
  Δ ∣ Ψ ∣ Σ′ ∣ Φ′ ⊢ p ⦂ A ⊑ B
castWt⊑ refl refl h = h

castWt⊒ :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{Φ Φ′ : List CastPerm}{A B : Ty}{p : Down} →
  Σ ≡ Σ′ →
  Φ ≡ Φ′ →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
  Δ ∣ Ψ ∣ Σ′ ∣ Φ′ ⊢ p ⦂ A ⊒ B
castWt⊒ refl refl h = h

castWt⊑-raw :
  ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A A′ B B′ : Ty}{p : Up} →
  (A≡A′ : A ≡ A′) →
  (B≡B′ : B ≡ B′) →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A′ ⊑ B′
castWt⊑-raw refl refl h = h

castWt⊒-raw :
  ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A A′ B B′ : Ty}{p : Down} →
  (A≡A′ : A ≡ A′) →
  (B≡B′ : B ≡ B′) →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A′ ⊒ B′
castWt⊒-raw refl refl h = h

------------------------------------------------------------------------
-- Type-variable renaming for well-typed widening and narrowing
------------------------------------------------------------------------

mutual
  ⊑-renameᵗ-wt :
    ∀ {Δ Δ′ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}
    {p : Up} →
    (ρ : Renameᵗ) →
    TyRenameWf Δ Δ′ ρ →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    Δ′ ∣ Ψ ∣ (renameStoreᵗ ρ Σ) ∣ Φ ⊢ (rename⊑ᵗ ρ p)
      ⦂ (renameᵗ ρ A) ⊑ (renameᵗ ρ B)
  ⊑-renameᵗ-wt ρ hρ (wt-tag p g gokΦ) =
    wt-tag (⊑-renameᵗ-wt ρ hρ p) (renameᵗ-ground ρ g) (renameᵗ-ground-ok ρ g gokΦ)
  ⊑-renameᵗ-wt ρ hρ (wt-unseal h α∈Φ p) =
    wt-unseal (renameLookupᵗ ρ h) α∈Φ (⊑-renameᵗ-wt ρ hρ p)
  ⊑-renameᵗ-wt ρ hρ (wt-unseal★ h α∈Φ p) =
    wt-unseal★ (renameLookupᵗ ρ h) α∈Φ (⊑-renameᵗ-wt ρ hρ p)
  ⊑-renameᵗ-wt ρ hρ (wt-↦ p q) =
    wt-↦ (⊒-renameᵗ-wt ρ hρ p) (⊑-renameᵗ-wt ρ hρ q)
  ⊑-renameᵗ-wt {Σ = Σ} ρ hρ (wt-∀ p) =
    wt-∀
      (castWt⊑
        (renameStoreᵗ-ext-⟰ᵗ ρ Σ)
        refl
        (⊑-renameᵗ-wt (extᵗ ρ) (TyRenameWf-ext hρ) p))
  ⊑-renameᵗ-wt {Σ = Σ} ρ hρ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊑
        (renameStoreᵗ-ν ρ Σ)
        refl
        (castWt⊑-raw
          (renameᵗ-ν-src ρ A)
          (renameᵗ-⇑ˢ ρ B)
          (⊑-renameᵗ-wt ρ hρ p)))
  ⊑-renameᵗ-wt ρ hρ (wt-id wfA) =
    wt-id (renameᵗ-preserves-WfTy wfA hρ)

  ⊒-renameᵗ-wt :
    ∀ {Δ Δ′ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}
    {p : Down} →
    (ρ : Renameᵗ) →
    TyRenameWf Δ Δ′ ρ →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    Δ′ ∣ Ψ ∣ (renameStoreᵗ ρ Σ) ∣ Φ ⊢ (rename⊒ᵗ ρ p)
      ⦂ (renameᵗ ρ A) ⊒ (renameᵗ ρ B)
  ⊒-renameᵗ-wt ρ hρ (wt-untag g gokΦ ℓ p) =
    wt-untag (renameᵗ-ground ρ g) (renameᵗ-ground-ok ρ g gokΦ) ℓ (⊒-renameᵗ-wt ρ hρ p)
  ⊒-renameᵗ-wt ρ hρ (wt-seal p h α∈Φ) =
    wt-seal (⊒-renameᵗ-wt ρ hρ p) (renameLookupᵗ ρ h) α∈Φ
  ⊒-renameᵗ-wt ρ hρ (wt-seal★ p h α∈Φ) =
    wt-seal★ (⊒-renameᵗ-wt ρ hρ p) (renameLookupᵗ ρ h) α∈Φ
  ⊒-renameᵗ-wt ρ hρ (wt-↦ p q) =
    wt-↦ (⊑-renameᵗ-wt ρ hρ p) (⊒-renameᵗ-wt ρ hρ q)
  ⊒-renameᵗ-wt {Σ = Σ} ρ hρ (wt-∀ p) =
    wt-∀
      (castWt⊒
        (renameStoreᵗ-ext-⟰ᵗ ρ Σ)
        refl
        (⊒-renameᵗ-wt (extᵗ ρ) (TyRenameWf-ext hρ) p))
  ⊒-renameᵗ-wt {Σ = Σ} ρ hρ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊒
        (renameStoreᵗ-ν ρ Σ)
        refl
        (castWt⊒-raw
          (renameᵗ-⇑ˢ ρ B)
          (renameᵗ-ν-src ρ A)
          (⊒-renameᵗ-wt ρ hρ p)))
  ⊒-renameᵗ-wt ρ hρ (wt-id wfA) =
    wt-id (renameᵗ-preserves-WfTy wfA hρ)

------------------------------------------------------------------------
-- Seal renaming for well-typed widening and narrowing
------------------------------------------------------------------------

mutual
  ⊑-renameˢ-wt :
    ∀ {Δ Ψ Ψ′}{Σ : Store}
      {Φ : List CastPerm}{Φ′ : List CastPerm}{A B : Ty}
      {p : Up} →
    (ρ : Renameˢ) →
    SealRenameWf Ψ Ψ′ ρ →
    RenOkConv ρ Φ Φ′ →
    RenOkCast ρ Φ Φ′ →
    RenOkTag ρ Φ Φ′ →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    Δ ∣ Ψ′ ∣ (renameStoreˢ ρ Σ) ∣ Φ′ ⊢ (rename⊑ˢ ρ p)
      ⦂ (renameˢ ρ A) ⊑ (renameˢ ρ B)
  ⊑-renameˢ-wt ρ hρ okConv okCast okTag (wt-tag p g gokΦ) =
    wt-tag
      (⊑-renameˢ-wt ρ hρ okConv okCast okTag p)
      (renameˢ-ground ρ g)
      (renameˢ-ground-ok ρ okTag g gokΦ)
  ⊑-renameˢ-wt ρ hρ okConv okCast okTag (wt-unseal h α∈Φ p) =
    wt-unseal (renameLookupˢ ρ h) (okConv α∈Φ)
      (⊑-renameˢ-wt ρ hρ okConv okCast okTag p)
  ⊑-renameˢ-wt ρ hρ okConv okCast okTag (wt-unseal★ h α∈Φ p) =
    wt-unseal★ (renameLookupˢ ρ h) (okCast α∈Φ)
      (⊑-renameˢ-wt ρ hρ okConv okCast okTag p)
  ⊑-renameˢ-wt ρ hρ okConv okCast okTag (wt-↦ p q) =
    wt-↦
      (⊒-renameˢ-wt ρ hρ okConv okCast okTag p)
      (⊑-renameˢ-wt ρ hρ okConv okCast okTag q)
  ⊑-renameˢ-wt {Σ = Σ} ρ hρ okConv okCast okTag (wt-∀ p) =
    wt-∀
      (castWt⊑
        (renameStoreˢ-ext-⟰ᵗ ρ Σ)
        refl
        (⊑-renameˢ-wt ρ hρ okConv okCast okTag p))
  ⊑-renameˢ-wt {Σ = Σ} ρ hρ okConv okCast okTag
    (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊑
        (renameStoreˢ-ν ρ Σ)
        refl
        (castWt⊑-raw
          (renameˢ-ν-src ρ A)
          (renameˢ-ext-⇑ˢ ρ B)
          (⊑-renameˢ-wt
            (extˢ ρ)
            (SealRenameWf-ext hρ)
            (RenOkConv-ext-cast-seal okConv)
            (RenOkCast-ext-cast-seal okCast)
            (RenOkTag-ext-cast-seal okTag)
            p)))
  ⊑-renameˢ-wt ρ hρ okConv okCast okTag (wt-id wfA) =
    wt-id (renameˢ-preserves-WfTy wfA hρ)

  ⊒-renameˢ-wt :
    ∀ {Δ Ψ Ψ′}{Σ : Store}
      {Φ : List CastPerm}{Φ′ : List CastPerm}{A B : Ty}
      {p : Down} →
    (ρ : Renameˢ) →
    SealRenameWf Ψ Ψ′ ρ →
    RenOkConv ρ Φ Φ′ →
    RenOkCast ρ Φ Φ′ →
    RenOkTag ρ Φ Φ′ →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    Δ ∣ Ψ′ ∣ (renameStoreˢ ρ Σ) ∣ Φ′ ⊢ (rename⊒ˢ ρ p)
      ⦂ (renameˢ ρ A) ⊒ (renameˢ ρ B)
  ⊒-renameˢ-wt ρ hρ okConv okCast okTag (wt-untag g gokΦ ℓ p) =
    wt-untag
      (renameˢ-ground ρ g)
      (renameˢ-ground-ok ρ okTag g gokΦ)
      ℓ
      (⊒-renameˢ-wt ρ hρ okConv okCast okTag p)
  ⊒-renameˢ-wt ρ hρ okConv okCast okTag (wt-seal p h α∈Φ) =
    wt-seal
      (⊒-renameˢ-wt ρ hρ okConv okCast okTag p)
      (renameLookupˢ ρ h)
      (okConv α∈Φ)
  ⊒-renameˢ-wt ρ hρ okConv okCast okTag (wt-seal★ p h α∈Φ) =
    wt-seal★
      (⊒-renameˢ-wt ρ hρ okConv okCast okTag p)
      (renameLookupˢ ρ h)
      (okCast α∈Φ)
  ⊒-renameˢ-wt ρ hρ okConv okCast okTag (wt-↦ p q) =
    wt-↦
      (⊑-renameˢ-wt ρ hρ okConv okCast okTag p)
      (⊒-renameˢ-wt ρ hρ okConv okCast okTag q)
  ⊒-renameˢ-wt {Σ = Σ} ρ hρ okConv okCast okTag (wt-∀ p) =
    wt-∀
      (castWt⊒
        (renameStoreˢ-ext-⟰ᵗ ρ Σ)
        refl
        (⊒-renameˢ-wt ρ hρ okConv okCast okTag p))
  ⊒-renameˢ-wt {Σ = Σ} ρ hρ okConv okCast okTag
    (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊒
        (renameStoreˢ-ν ρ Σ)
        refl
        (castWt⊒-raw
          (renameˢ-ext-⇑ˢ ρ B)
          (renameˢ-ν-src ρ A)
          (⊒-renameˢ-wt
            (extˢ ρ)
            (SealRenameWf-ext hρ)
            (RenOkConv-ext-cast-tag okConv)
            (RenOkCast-ext-cast-tag okCast)
            (RenOkTag-ext-cast-tag okTag)
            p)))
  ⊒-renameˢ-wt ρ hρ okConv okCast okTag (wt-id wfA) =
    wt-id (renameˢ-preserves-WfTy wfA hρ)

------------------------------------------------------------------------
-- Type-variable substitution for well-typed widening and narrowing
------------------------------------------------------------------------

mutual
  ⊑-substᵗ-wt :
    ∀ {Δ Δ′ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}
      {p : Up} →
    (σ : Substᵗ) →
    TySubstWf Δ Δ′ Ψ σ →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    Δ′ ∣ Ψ ∣ (substStoreᵗ σ Σ) ∣ Φ ⊢ (subst⊑ᵗ σ p)
      ⦂ (substᵗ σ A) ⊑ (substᵗ σ B)
  ⊑-substᵗ-wt σ hσ (wt-tag p g gokΦ) =
    wt-tag (⊑-substᵗ-wt σ hσ p) (substᵗ-ground σ g) (substᵗ-ground-ok σ g gokΦ)
  ⊑-substᵗ-wt σ hσ (wt-unseal h α∈Φ p) =
    wt-unseal (substLookupᵗ σ h) α∈Φ (⊑-substᵗ-wt σ hσ p)
  ⊑-substᵗ-wt σ hσ (wt-unseal★ h α∈Φ p) =
    wt-unseal★ (substLookupᵗ σ h) α∈Φ (⊑-substᵗ-wt σ hσ p)
  ⊑-substᵗ-wt σ hσ (wt-↦ p q) =
    wt-↦ (⊒-substᵗ-wt σ hσ p) (⊑-substᵗ-wt σ hσ q)
  ⊑-substᵗ-wt {Σ = Σ} σ hσ (wt-∀ p) =
    wt-∀
      (castWt⊑
        (substStoreᵗ-ext-⟰ᵗ σ Σ)
        refl
        (⊑-substᵗ-wt (extsᵗ σ) (TySubstWf-exts hσ) p))
  ⊑-substᵗ-wt {Σ = Σ} σ hσ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊑
        (substStoreᵗ-ν σ Σ)
        refl
        (castWt⊑-raw
          (substᵗ-ν-src σ A)
          (substᵗ-⇑ˢ σ B)
          (⊑-substᵗ-wt (liftSubstˢ σ) (TySubstWf-liftˢ hσ) p)))
  ⊑-substᵗ-wt σ hσ (wt-id wfA) =
    wt-id (substᵗ-preserves-WfTy wfA hσ)

  ⊒-substᵗ-wt :
    ∀ {Δ Δ′ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}
      {p : Down} →
    (σ : Substᵗ) →
    TySubstWf Δ Δ′ Ψ σ →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    Δ′ ∣ Ψ ∣ (substStoreᵗ σ Σ) ∣ Φ ⊢ (subst⊒ᵗ σ p)
      ⦂ (substᵗ σ A) ⊒ (substᵗ σ B)
  ⊒-substᵗ-wt σ hσ (wt-untag g gokΦ ℓ p) =
    wt-untag (substᵗ-ground σ g) (substᵗ-ground-ok σ g gokΦ) ℓ (⊒-substᵗ-wt σ hσ p)
  ⊒-substᵗ-wt σ hσ (wt-seal p h α∈Φ) =
    wt-seal (⊒-substᵗ-wt σ hσ p) (substLookupᵗ σ h) α∈Φ
  ⊒-substᵗ-wt σ hσ (wt-seal★ p h α∈Φ) =
    wt-seal★ (⊒-substᵗ-wt σ hσ p) (substLookupᵗ σ h) α∈Φ
  ⊒-substᵗ-wt σ hσ (wt-↦ p q) =
    wt-↦ (⊑-substᵗ-wt σ hσ p) (⊒-substᵗ-wt σ hσ q)
  ⊒-substᵗ-wt {Σ = Σ} σ hσ (wt-∀ p) =
    wt-∀
      (castWt⊒
        (substStoreᵗ-ext-⟰ᵗ σ Σ)
        refl
        (⊒-substᵗ-wt (extsᵗ σ) (TySubstWf-exts hσ) p))
  ⊒-substᵗ-wt {Σ = Σ} σ hσ (wt-ν {A = A} {B = B} p) =
    wt-ν
      (castWt⊒
        (substStoreᵗ-ν σ Σ)
        refl
        (castWt⊒-raw
          (substᵗ-⇑ˢ σ B)
          (substᵗ-ν-src σ A)
          (⊒-substᵗ-wt (liftSubstˢ σ) (TySubstWf-liftˢ hσ) p)))
  ⊒-substᵗ-wt σ hσ (wt-id wfA) =
    wt-id (substᵗ-preserves-WfTy wfA hσ)

infixl 8 _[_]↑
_[_]↑ :
  Up → Ty → Up
p [ T ]↑ = subst⊑ᵗ (singleTyEnv T) p

[]⊑ᵗ-wt :
  ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}
    {p : Up}
  → suc Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B
  → (T : Ty)
  → WfTy Δ Ψ T
  → Δ ∣ Ψ ∣ (substStoreᵗ (singleTyEnv T) Σ) ∣ Φ ⊢ (p [ T ]↑)
      ⦂ (A [ T ]ᵗ) ⊑ (B [ T ]ᵗ)
[]⊑ᵗ-wt h T wfT = ⊑-substᵗ-wt (singleTyEnv T) (singleTyEnv-Wf T wfT) h

infixl 8 _[_]↓
_[_]↓ :
  Down → Ty → Down
p [ T ]↓ = subst⊒ᵗ (singleTyEnv T) p

[]⊒ᵗ-wt :
  ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}
    {p : Down}
  → suc Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B
  → (T : Ty)
  → WfTy Δ Ψ T
  → Δ ∣ Ψ ∣ (substStoreᵗ (singleTyEnv T) Σ) ∣ Φ ⊢ (p [ T ]↓)
      ⦂ (A [ T ]ᵗ) ⊒ (B [ T ]ᵗ)
[]⊒ᵗ-wt h T wfT = ⊒-substᵗ-wt (singleTyEnv T) (singleTyEnv-Wf T wfT) h

⊑-[]ᵗ-seal :
  ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}{α : Seal}
    {p : Up}
  → α < Ψ
  → α ∈ Φ
  → suc Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B
  → Δ ∣ Ψ ∣ (substStoreᵗ (singleTyEnv (｀ α)) Σ) ∣ Φ ⊢ (p [ ｀ α ]↑)
      ⦂ (A [ ｀ α ]ᵗ) ⊑ (B [ ｀ α ]ᵗ)
⊑-[]ᵗ-seal {α = α} α<Ψ α∈Φ h = []⊑ᵗ-wt h (｀ α) (wfSeal α<Ψ)

⊒-[]ᵗ-seal :
  ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}{α : Seal}
    {p : Down}
  → α < Ψ
  → α ∈ Φ
  → suc Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B
  → Δ ∣ Ψ ∣ (substStoreᵗ (singleTyEnv (｀ α)) Σ) ∣ Φ ⊢ (p [ ｀ α ]↓)
      ⦂ (A [ ｀ α ]ᵗ) ⊒ (B [ ｀ α ]ᵗ)
⊒-[]ᵗ-seal {α = α} α<Ψ α∈Φ h = []⊒ᵗ-wt h (｀ α) (wfSeal α<Ψ)

------------------------------------------------------------------------
-- Instantiation shorthand for casts
------------------------------------------------------------------------

instVarExt⊑ : ((X : TyVar) → Up) → (X : TyVar) → Up
instVarExt⊑ var⊑ zero = id X₀
instVarExt⊑ var⊑ (suc X) = rename⊑ᵗ suc (var⊑ X)

instVarExt⊒ : ((X : TyVar) → Down) → (X : TyVar) → Down
instVarExt⊒ var⊒ zero = id X₀
instVarExt⊒ var⊒ (suc X) = rename⊒ᵗ suc (var⊒ X)

mutual
  substᵗ-up : ((X : TyVar) → Up) → ((X : TyVar) → Down) → Ty → Up
  substᵗ-up var⊑ var⊒ (＇ X) = var⊑ X
  substᵗ-up var⊑ var⊒ (｀ α) = id (｀ α)
  substᵗ-up var⊑ var⊒ (‵ ι) = id (‵ ι)
  substᵗ-up var⊑ var⊒ ★ = id ★
  substᵗ-up var⊑ var⊒ (A ⇒ B) = substᵗ-down var⊑ var⊒ A ↦ substᵗ-up var⊑ var⊒ B
  substᵗ-up var⊑ var⊒ (`∀ A) =
    ∀ᵖ (substᵗ-up (instVarExt⊑ var⊑) (instVarExt⊒ var⊒) A)

  substᵗ-down : ((X : TyVar) → Up) → ((X : TyVar) → Down) → Ty → Down
  substᵗ-down var⊑ var⊒ (＇ X) = var⊒ X
  substᵗ-down var⊑ var⊒ (｀ α) = id (｀ α)
  substᵗ-down var⊑ var⊒ (‵ ι) = id (‵ ι)
  substᵗ-down var⊑ var⊒ ★ = id ★
  substᵗ-down var⊑ var⊒ (A ⇒ B) = substᵗ-up var⊑ var⊒ A ↦ substᵗ-down var⊑ var⊒ B
  substᵗ-down var⊑ var⊒ (`∀ A) =
    ∀ᵖ (substᵗ-down (instVarExt⊑ var⊑) (instVarExt⊒ var⊒) A)

mutual
  instSubst⊑-wt :
    ∀ {Δ Δ′ Ψ}{Σ : Store} →
    (σ τ : Substᵗ) →
    (var⊑ : (X : TyVar) → Up) →
    (var⊒ : (X : TyVar) → Down) →
    ((X : TyVar) → X < Δ →
      Δ′ ∣ Ψ ∣ Σ ∣ (every Ψ) ⊢ (var⊑ X) ⦂ (σ X) ⊑ (τ X)) →
    ((X : TyVar) → X < Δ →
      Δ′ ∣ Ψ ∣ Σ ∣ (every Ψ) ⊢ (var⊒ X) ⦂ (τ X) ⊒ (σ X)) →
    (A : Ty) →
    WfTy Δ Ψ A →
    Δ′ ∣ Ψ ∣ Σ ∣ (every Ψ) ⊢ (substᵗ-up var⊑ var⊒ A)
      ⦂ (substᵗ σ A) ⊑ (substᵗ τ A)
  instSubst⊑-wt σ τ var⊑ var⊒ h⊑ h⊒ (＇ X) (wfVar X<Δ) =
    h⊑ X X<Δ
  instSubst⊑-wt σ τ var⊑ var⊒ h⊑ h⊒ (｀ α) (wfSeal α<Ψ) =
    wt-id (wfSeal α<Ψ)
  instSubst⊑-wt σ τ var⊑ var⊒ h⊑ h⊒ (‵ ι) wfBase = wt-id wfBase
  instSubst⊑-wt σ τ var⊑ var⊒ h⊑ h⊒ ★ wf★ = wt-id wf★
  instSubst⊑-wt σ τ var⊑ var⊒ h⊑ h⊒ (A ⇒ B) (wf⇒ wfA wfB) =
    wt-↦ (instSubst⊒-wt σ τ var⊑ var⊒ h⊑ h⊒ A wfA)
         (instSubst⊑-wt σ τ var⊑ var⊒ h⊑ h⊒ B wfB)
  instSubst⊑-wt {Δ = Δ} {Δ′ = Δ′} {Ψ = Ψ} {Σ = Σ}
    σ τ var⊑ var⊒ h⊑ h⊒ (`∀ A) (wf∀ wfA) =
    wt-∀ (instSubst⊑-wt (extsᵗ σ) (extsᵗ τ)
                          (instVarExt⊑ var⊑) (instVarExt⊒ var⊒)
                          h⊑′ h⊒′ A wfA)
    where
    h⊑′ : (X : TyVar) → X < suc Δ →
      suc Δ′ ∣ Ψ ∣ (⟰ᵗ Σ) ∣ (every Ψ) ⊢ (instVarExt⊑ var⊑ X)
        ⦂ (extsᵗ σ X) ⊑ (extsᵗ τ X)
    h⊑′ zero z<s = wt-id (wfVar z<s)
    h⊑′ (suc X) (s<s X<Δ) =
      ⊑-renameᵗ-wt suc TyRenameWf-suc (h⊑ X X<Δ)

    h⊒′ : (X : TyVar) → X < suc Δ →
      suc Δ′ ∣ Ψ ∣ (⟰ᵗ Σ) ∣ (every Ψ) ⊢ (instVarExt⊒ var⊒ X)
        ⦂ (extsᵗ τ X) ⊒ (extsᵗ σ X)
    h⊒′ zero z<s = wt-id (wfVar z<s)
    h⊒′ (suc X) (s<s X<Δ) =
      ⊒-renameᵗ-wt suc TyRenameWf-suc (h⊒ X X<Δ)

  instSubst⊒-wt :
    ∀ {Δ Δ′ Ψ}{Σ : Store} →
    (σ τ : Substᵗ) →
    (var⊑ : (X : TyVar) → Up) →
    (var⊒ : (X : TyVar) → Down) →
    ((X : TyVar) → X < Δ →
      Δ′ ∣ Ψ ∣ Σ ∣ (every Ψ) ⊢ (var⊑ X) ⦂ (σ X) ⊑ (τ X)) →
    ((X : TyVar) → X < Δ →
      Δ′ ∣ Ψ ∣ Σ ∣ (every Ψ) ⊢ (var⊒ X) ⦂ (τ X) ⊒ (σ X)) →
    (A : Ty) →
    WfTy Δ Ψ A →
    Δ′ ∣ Ψ ∣ Σ ∣ (every Ψ) ⊢ (substᵗ-down var⊑ var⊒ A)
      ⦂ (substᵗ τ A) ⊒ (substᵗ σ A)
  instSubst⊒-wt σ τ var⊑ var⊒ h⊑ h⊒ (＇ X) (wfVar X<Δ) =
    h⊒ X X<Δ
  instSubst⊒-wt σ τ var⊑ var⊒ h⊑ h⊒ (｀ α) (wfSeal α<Ψ) =
    wt-id (wfSeal α<Ψ)
  instSubst⊒-wt σ τ var⊑ var⊒ h⊑ h⊒ (‵ ι) wfBase = wt-id wfBase
  instSubst⊒-wt σ τ var⊑ var⊒ h⊑ h⊒ ★ wf★ = wt-id wf★
  instSubst⊒-wt σ τ var⊑ var⊒ h⊑ h⊒ (A ⇒ B) (wf⇒ wfA wfB) =
    wt-↦ (instSubst⊑-wt σ τ var⊑ var⊒ h⊑ h⊒ A wfA)
         (instSubst⊒-wt σ τ var⊑ var⊒ h⊑ h⊒ B wfB)
  instSubst⊒-wt {Δ = Δ} {Δ′ = Δ′} {Ψ = Ψ} {Σ = Σ}
    σ τ var⊑ var⊒ h⊑ h⊒ (`∀ A) (wf∀ wfA) =
    wt-∀ (instSubst⊒-wt (extsᵗ σ) (extsᵗ τ)
                          (instVarExt⊑ var⊑) (instVarExt⊒ var⊒)
                          h⊑′ h⊒′ A wfA)
    where
    h⊑′ : (X : TyVar) → X < suc Δ →
      suc Δ′ ∣ Ψ ∣ (⟰ᵗ Σ) ∣ (every Ψ) ⊢ (instVarExt⊑ var⊑ X)
        ⦂ (extsᵗ σ X) ⊑ (extsᵗ τ X)
    h⊑′ zero z<s = wt-id (wfVar z<s)
    h⊑′ (suc X) (s<s X<Δ) =
      ⊑-renameᵗ-wt suc TyRenameWf-suc (h⊑ X X<Δ)

    h⊒′ : (X : TyVar) → X < suc Δ →
      suc Δ′ ∣ Ψ ∣ (⟰ᵗ Σ) ∣ (every Ψ) ⊢ (instVarExt⊒ var⊒ X)
        ⦂ (extsᵗ τ X) ⊒ (extsᵗ σ X)
    h⊒′ zero z<s = wt-id (wfVar z<s)
    h⊒′ (suc X) (s<s X<Δ) =
      ⊒-renameᵗ-wt suc TyRenameWf-suc (h⊒ X X<Δ)

instSubst⊒ :
  ∀ {Δ Δ′ Ψ}{Σ : Store} →
  (σ τ : Substᵗ) →
  (var⊑ : (X : TyVar) → Up) →
  (var⊒ : (X : TyVar) → Down) →
  ((X : TyVar) → X < Δ →
    Δ′ ∣ Ψ ∣ Σ ∣ (every Ψ) ⊢ (var⊑ X) ⦂ (σ X) ⊑ (τ X)) →
  ((X : TyVar) → X < Δ →
    Δ′ ∣ Ψ ∣ Σ ∣ (every Ψ) ⊢ (var⊒ X) ⦂ (τ X) ⊒ (σ X)) →
  (A : Ty) →
  WfTy Δ Ψ A →
  Wt⊒ Δ′ Ψ Σ (every Ψ) (substᵗ τ A) (substᵗ σ A)
instSubst⊒ {Δ′ = Δ′} {Ψ = Ψ} {Σ = Σ} σ τ var⊑ var⊒ h⊑ h⊒ A wfA = p , hp
  where
  p : Down
  p = substᵗ-down var⊑ var⊒ A

  hp : Δ′ ∣ Ψ ∣ Σ ∣ (every Ψ) ⊢ p ⦂ (substᵗ τ A) ⊒ (substᵗ σ A)
  hp = instSubst⊒-wt σ τ var⊑ var⊒ h⊑ h⊒ A wfA

instVar⊑ : (A : Ty) → (α : Seal) → (X : TyVar) → Up
instVar⊑ A α zero = unseal α (id A)
instVar⊑ A α (suc X) = id (＇ X)

instVar⊑-wt :
  ∀ {Δ Ψ}{Σ : Store}{A : Ty}{α : Seal} →
  WfTy Δ Ψ A →
  (h : Σ ∋ˢ α ⦂ A) →
  (α∈ : α ∈conv every Ψ) →
  (X : TyVar) →
  X < suc Δ →
  Δ ∣ Ψ ∣ Σ ∣ (every Ψ) ⊢ (instVar⊑ A α X)
    ⦂ (singleTyEnv (｀ α) X) ⊑ (singleTyEnv A X)
instVar⊑-wt wfA h α∈ zero z<s = wt-unseal h α∈ (wt-id wfA)
instVar⊑-wt wfA h α∈ (suc X) (s<s X<Δ) = wt-id (wfVar X<Δ)

instVar⊒ : (A : Ty) → (α : Seal) → (X : TyVar) → Down
instVar⊒ A α zero = seal (id A) α
instVar⊒ A α (suc X) = id (＇ X)

instVar⊒-wt :
  ∀ {Δ Ψ}{Σ : Store}{A : Ty}{α : Seal} →
  WfTy Δ Ψ A →
  (h : Σ ∋ˢ α ⦂ A) →
  (α∈ : α ∈conv every Ψ) →
  (X : TyVar) →
  X < suc Δ →
  Δ ∣ Ψ ∣ Σ ∣ (every Ψ) ⊢ (instVar⊒ A α X)
    ⦂ (singleTyEnv A X) ⊒ (singleTyEnv (｀ α) X)
instVar⊒-wt wfA h α∈ zero z<s = wt-seal (wt-id wfA) h α∈
instVar⊒-wt wfA h α∈ (suc X) (s<s X<Δ) = wt-id (wfVar X<Δ)

instCast⊑ : ∀ {A B α} → Up
instCast⊑ {A = A} {B = B} {α = α} = substᵗ-up (instVar⊑ A α) (instVar⊒ A α) B

instCast⊑-wt :
  ∀ {Δ Ψ}{Σ : Store}{A : Ty}{B : Ty}{α : Seal} →
  WfTy Δ Ψ A →
  WfTy (suc Δ) Ψ B →
  (h : Σ ∋ˢ α ⦂ A) →
  α ∈conv every Ψ →
  Δ ∣ Ψ ∣ Σ ∣ (every Ψ) ⊢ (instCast⊑ {A = A} {B = B} {α = α})
    ⦂ (B [ ｀ α ]ᵗ) ⊑ (B [ A ]ᵗ)
instCast⊑-wt {A = A} {B = B} {α = α} wfA wfB h α∈ =
  instSubst⊑-wt (singleTyEnv (｀ α)) (singleTyEnv A)
                (instVar⊑ A α) (instVar⊒ A α)
                (instVar⊑-wt wfA h α∈) (instVar⊒-wt wfA h α∈)
                B wfB

instCast⊒ : ∀ {A B α} → Down
instCast⊒ {A = A} {B = B} {α = α} = substᵗ-down (instVar⊑ A α) (instVar⊒ A α) B

instCast⊒-wt :
  ∀ {Δ Ψ}{Σ : Store}{A : Ty}{B : Ty}{α : Seal} →
  WfTy Δ Ψ A →
  WfTy (suc Δ) Ψ B →
  (h : Σ ∋ˢ α ⦂ A) →
  α ∈conv every Ψ →
  Δ ∣ Ψ ∣ Σ ∣ (every Ψ) ⊢ (instCast⊒ {A = A} {B = B} {α = α})
    ⦂ (B [ A ]ᵗ) ⊒ (B [ ｀ α ]ᵗ)
instCast⊒-wt {A = A} {B = B} {α = α} wfA wfB h α∈ =
  instSubst⊒-wt (singleTyEnv (｀ α)) (singleTyEnv A)
                (instVar⊑ A α) (instVar⊒ A α)
                (instVar⊑-wt wfA h α∈) (instVar⊒-wt wfA h α∈)
                B wfB

reveal-⊑ : (A : Ty) (B : Ty) → Up
reveal-⊑ A B =
  substᵗ-up (instVar⊑ (⇑ˢ A) zero) (instVar⊒ (⇑ˢ A) zero) (⇑ˢ B)

inst-⇑ˢ : ∀ (A B : Ty) → (⇑ˢ B) [ ⇑ˢ A ]ᵗ ≡ ⇑ˢ (B [ A ]ᵗ)
inst-⇑ˢ A B =
  trans (substᵗ-cong env (⇑ˢ B))
        (substᵗ-⇑ˢ (singleTyEnv A) B)
  where
  env : (X : TyVar) → singleTyEnv (⇑ˢ A) X ≡ liftSubstˢ (singleTyEnv A) X
  env zero = refl
  env (suc X) = refl
