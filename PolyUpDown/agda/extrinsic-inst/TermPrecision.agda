module TermPrecision where

-- File Charter:
--   * Structural term imprecision for extrinsic-inst PolyUpDown.
--   * Defines precision contexts and the term-precision judgment without the
--   * cast-specific compatibility rules.
--   * Provides projections back to ordinary left/right typing derivations.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (zero; suc; _⊔_; _≤_; z≤n)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m)
open import Data.Nat.Properties using (<-irrelevant)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import Types
open import Ctx using (⤊ᵗ)
open import Imprecision
open import UpDown
open import Terms
open import TypeProperties
  using
    ( substᵗ-renameᵗ
    ; substᵗ-id
    ; renameᵗ-ground
    ; renameᵗ-⇑ˢ
    ; renameᵗ-ν-src
    )

------------------------------------------------------------------------
-- Precision contexts
------------------------------------------------------------------------

Prec : Set
Prec = Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] (A ⊑ B)

PCtx : Set
PCtx = List Prec

record TPEnv : Set where
  constructor ⟪_,_,_,_⟫
  field
    Δ : TyCtx
    Ψ : SealCtx
    store : Store
    Γ : PCtx
open TPEnv public

extendᴾ : TPEnv → Prec → TPEnv
extendᴾ E P = ⟪ TPEnv.Δ E , TPEnv.Ψ E , TPEnv.store E , P ∷ TPEnv.Γ E ⟫

leftTy : Prec → Ty
leftTy (A , B , p) = A

rightTy : Prec → Ty
rightTy (A , B , p) = B

leftCtx : PCtx → Ctx
leftCtx [] = []
leftCtx (P ∷ Γ) = leftTy P ∷ leftCtx Γ

rightCtx : PCtx → Ctx
rightCtx [] = []
rightCtx (P ∷ Γ) = rightTy P ∷ rightCtx Γ

infix 4 _∋ₚ_⦂_
data _∋ₚ_⦂_ : PCtx → Var → Prec → Set where
  Zₚ : ∀ {Γ P} →
    (P ∷ Γ) ∋ₚ zero ⦂ P

  Sₚ : ∀ {Γ P Q x} →
    Γ ∋ₚ x ⦂ P →
    (Q ∷ Γ) ∋ₚ suc x ⦂ P

lookup-left : ∀ {Γ x A B} {p : A ⊑ B} →
  Γ ∋ₚ x ⦂ (A , B , p) →
  leftCtx Γ ∋ x ⦂ A
lookup-left Zₚ = Z
lookup-left (Sₚ h) = S (lookup-left h)

lookup-right : ∀ {Γ x A B} {p : A ⊑ B} →
  Γ ∋ₚ x ⦂ (A , B , p) →
  rightCtx Γ ∋ x ⦂ B
lookup-right Zₚ = Z
lookup-right (Sₚ h) = S (lookup-right h)

------------------------------------------------------------------------
-- Type-binder lifting of precision contexts
------------------------------------------------------------------------

subst-as-renameᵗ : (ρ : Renameᵗ) → (A : Ty) → substᵗ (λ X → ＇ ρ X) A ≡ renameᵗ ρ A
subst-as-renameᵗ ρ A =
  trans
    (sym (substᵗ-renameᵗ ρ (λ X → ＇ X) A))
    (substᵗ-id (renameᵗ ρ A))

renameᵗ-⊑ : (ρ : Renameᵗ) → ∀ {A B} → A ⊑ B → renameᵗ ρ A ⊑ renameᵗ ρ B
renameᵗ-⊑ ρ ⊑-★★ = ⊑-★★
renameᵗ-⊑ ρ (⊑-★ A G g p) =
  ⊑-★ (renameᵗ ρ A) (renameᵗ ρ G) (renameᵗ-ground ρ g) (renameᵗ-⊑ ρ p)
renameᵗ-⊑ ρ (⊑-＇ X) = ⊑-＇ (ρ X)
renameᵗ-⊑ ρ (⊑-｀ αˡ αʳ) = ⊑-｀ αˡ αʳ
renameᵗ-⊑ ρ (⊑-‵ ι) = ⊑-‵ ι
renameᵗ-⊑ ρ (⊑-⇒ A A′ B B′ p q) =
  ⊑-⇒ (renameᵗ ρ A) (renameᵗ ρ A′) (renameᵗ ρ B) (renameᵗ ρ B′)
    (renameᵗ-⊑ ρ p) (renameᵗ-⊑ ρ q)
renameᵗ-⊑ ρ (⊑-∀ A B p) =
  ⊑-∀ (renameᵗ (extᵗ ρ) A) (renameᵗ (extᵗ ρ) B) (renameᵗ-⊑ (extᵗ ρ) p)
renameᵗ-⊑ ρ (⊑-ν A B p) =
  ⊑-ν (renameᵗ (extᵗ ρ) A) (renameᵗ ρ B)
    (cast-⊑ (renameᵗ-ν-src ρ A) (renameᵗ-⇑ˢ ρ B) (renameᵗ-⊑ ρ p))

⇑ᵗᴾ : PCtx → PCtx
⇑ᵗᴾ [] = []
⇑ᵗᴾ ((A , B , p) ∷ Γ) = (renameᵗ suc A , renameᵗ suc B , renameᵗ-⊑ suc p) ∷ ⇑ᵗᴾ Γ

leftCtx-⇑ᵗᴾ : (Γ : PCtx) → leftCtx (⇑ᵗᴾ Γ) ≡ ⤊ᵗ (leftCtx Γ)
leftCtx-⇑ᵗᴾ [] = refl
leftCtx-⇑ᵗᴾ ((A , B , p) ∷ Γ) = cong (renameᵗ suc A ∷_) (leftCtx-⇑ᵗᴾ Γ)

rightCtx-⇑ᵗᴾ : (Γ : PCtx) → rightCtx (⇑ᵗᴾ Γ) ≡ ⤊ᵗ (rightCtx Γ)
rightCtx-⇑ᵗᴾ [] = refl
rightCtx-⇑ᵗᴾ ((A , B , p) ∷ Γ) = cong (renameᵗ suc B ∷_) (rightCtx-⇑ᵗᴾ Γ)

⇑ᵗᴱ : TPEnv → TPEnv
⇑ᵗᴱ E = ⟪ suc (TPEnv.Δ E) , TPEnv.Ψ E , ⟰ᵗ (TPEnv.store E) , ⇑ᵗᴾ (TPEnv.Γ E) ⟫

ν-inst-⊑ : ∀ {Ψ} → (A B T : Ty) → WfTy 0 Ψ T
  → ((⇑ˢ A) [ α₀ ]ᵗ ⊑ ⇑ˢ B) → A [ T ]ᵗ ⊑ B
ν-inst-⊑ A B T hT p =
  cast-⊑ (substˢᵗ-single-ν-src hT A) (substˢᵗ-single-⇑ˢ-id hT B)
         (substˢ-⊑-closed hT p)

WfTy-irrel : ∀ {Δ Ψ A} → (h h′ : WfTy Δ Ψ A) → h ≡ h′
WfTy-irrel (wfVar X<Δ) (wfVar X<Δ′) = cong wfVar (<-irrelevant X<Δ X<Δ′)
WfTy-irrel (wfSeal α<Ψ) (wfSeal α<Ψ′) = cong wfSeal (<-irrelevant α<Ψ α<Ψ′)
WfTy-irrel wfBase wfBase = refl
WfTy-irrel wf★ wf★ = refl
WfTy-irrel (wf⇒ hA hB) (wf⇒ hA′ hB′) = cong₂ wf⇒ (WfTy-irrel hA hA′) (WfTy-irrel hB hB′)
WfTy-irrel (wf∀ hA) (wf∀ hA′) = cong wf∀ (WfTy-irrel hA hA′)

ν-inst-⊑-WfTy-irrel :
  ∀ {Ψ} (A B T : Ty) →
  (hT hT′ : WfTy 0 Ψ T) →
  (p : ((⇑ˢ A) [ α₀ ]ᵗ ⊑ ⇑ˢ B)) →
  ν-inst-⊑ A B T hT p ≡ ν-inst-⊑ A B T hT′ p
ν-inst-⊑-WfTy-irrel A B T hT hT′ p rewrite WfTy-irrel hT hT′ = refl

ν-inst-⊑-WfTy-irrel-Ψ :
  ∀ {Ψ Ψ′} (A B T : Ty) →
  (hT : WfTy 0 Ψ T) →
  (hT′ : WfTy 0 Ψ′ T) →
  (p : ((⇑ˢ A) [ α₀ ]ᵗ ⊑ ⇑ˢ B)) →
  ν-inst-⊑ A B T (WfTy-weakenˢ hT (m≤m⊔n Ψ Ψ′)) p
    ≡
  ν-inst-⊑ A B T (WfTy-weakenˢ hT′ (m≤n⊔m Ψ Ψ′)) p
ν-inst-⊑-WfTy-irrel-Ψ {Ψ} {Ψ′} A B T hT hT′ p =
  ν-inst-⊑-WfTy-irrel A B T
    (WfTy-weakenˢ hT (m≤m⊔n Ψ Ψ′))
    (WfTy-weakenˢ hT′ (m≤n⊔m Ψ Ψ′))
    p

------------------------------------------------------------------------
-- Term imprecision
------------------------------------------------------------------------

infix 4 _⊢_⊑_⦂_
data _⊢_⊑_⦂_ (E : TPEnv) : Term → Term → ∀ {A B} → A ⊑ B → Set where

  ⊑` : ∀ {x A B} {p : A ⊑ B} →
    TPEnv.Γ E ∋ₚ x ⦂ (A , B , p) →
    E ⊢ (` x) ⊑ (` x) ⦂ p

  ⊑ƛ : ∀ {A A′ B B′ M M′} {pA : A ⊑ A′} {pB : B ⊑ B′} →
    WfTy (TPEnv.Δ E) (TPEnv.Ψ E) A →
    WfTy (TPEnv.Δ E) (TPEnv.Ψ E) A′ →
    extendᴾ E (A , A′ , pA) ⊢ M ⊑ M′ ⦂ pB →
    E ⊢ (ƛ A ⇒ M) ⊑ (ƛ A′ ⇒ M′) ⦂ ⊑-⇒ A A′ B B′ pA pB

  ⊑· : ∀ {A A′ B B′ L L′ M M′} {pA : A ⊑ A′} {pB : B ⊑ B′} →
    E ⊢ L ⊑ L′ ⦂ ⊑-⇒ A A′ B B′ pA pB →
    E ⊢ M ⊑ M′ ⦂ pA →
    E ⊢ (L · M) ⊑ (L′ · M′) ⦂ pB

  ⊑Λ : ∀ {A B M M′} {p : A ⊑ B} →
    Value M →
    Value M′ →
    WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) A →
    WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) B →
    ⇑ᵗᴱ E ⊢ M ⊑ M′ ⦂ p →
    E ⊢ (Λ M) ⊑ (Λ M′) ⦂ ⊑-∀ A B p

  ⊑⦂∀ : ∀ {A B M M′ T} {p : A ⊑ B} →
    E ⊢ M ⊑ M′ ⦂ ⊑-∀ A B p →
    WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) A →
    WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) B →
    WfTy (TPEnv.Δ E) (TPEnv.Ψ E) T →
    E ⊢ (M ⦂∀ A [ T ]) ⊑ (M′ ⦂∀ B [ T ]) ⦂ substᵗ-⊑ (singleTyEnv T) p

  ⊑⦂∀-ν : ∀ (A B : Ty) {M M′ T} (p : ((⇑ˢ A) [ α₀ ]ᵗ ⊑ ⇑ˢ B)) →
    E ⊢ M ⊑ M′ ⦂ (⊑-ν A B p) →
    WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) A →
    (hT : WfTy 0 (TPEnv.Ψ E) T) →
    E ⊢ (M ⦂∀ A [ T ]) ⊑ M′ ⦂ ν-inst-⊑ A B T hT p

  ⊑$ : ∀ {n} →
    E ⊢ ($ (κℕ n)) ⊑ ($ (κℕ n)) ⦂ (⊑-‵ `ℕ)

  ⊑⊕ : ∀ {L L′ M M′} {op : Prim} →
    E ⊢ L ⊑ L′ ⦂ (⊑-‵ `ℕ) →
    E ⊢ M ⊑ M′ ⦂ (⊑-‵ `ℕ) →
    E ⊢ (L ⊕[ op ] M) ⊑ (L′ ⊕[ op ] M′) ⦂ (⊑-‵ `ℕ)

  ⊑up : ∀ {M M′ A A′ B B′} {pA : A ⊑ A′} {pB : B ⊑ B′} {u : Up} {u′ : Up}
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    E ⊢ M ⊑ M′ ⦂ pA →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u ⦂ A ⊑ B →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
    E ⊢ (M up u) ⊑ (M′ up u′) ⦂ pB

  ⊑upL : ∀ {M M′ A A′ B} {pA : A ⊑ A′} {pB : B ⊑ A′} {u : Up}
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    E ⊢ M ⊑ M′ ⦂ pA →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u ⦂ A ⊑ B →
    E ⊢ (M up u) ⊑ M′ ⦂ pB

  ⊑upR : ∀ {M M′ A A′ B′} {pA : A ⊑ A′} {pB : A ⊑ B′} {u′ : Up}
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    E ⊢ M ⊑ M′ ⦂ pA →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
    E ⊢ M ⊑ (M′ up u′) ⦂ pB

  ⊑down : ∀ {M M′ A A′ B B′} {pA : A ⊑ A′} {pB : B ⊑ B′} {d : Down} {d′ : Down}
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    E ⊢ M ⊑ M′ ⦂ pA →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d ⦂ A ⊒ B →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
    E ⊢ (M down d) ⊑ (M′ down d′) ⦂ pB

  ⊑downL : ∀ {M M′ A A′ B} {pA : A ⊑ A′} {pB : B ⊑ A′} {d : Down}
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    E ⊢ M ⊑ M′ ⦂ pA →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d ⦂ A ⊒ B →
    E ⊢ (M down d) ⊑ M′ ⦂ pB

  ⊑downR : ∀ {M M′ A A′ B′} {pA : A ⊑ A′} {pB : A ⊑ B′} {d′ : Down}
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    E ⊢ M ⊑ M′ ⦂ pA →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ (TPEnv.store E) ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
    E ⊢ M ⊑ (M′ down d′) ⦂ pB

  ⊑blameR : ∀ {M A B ℓ} {p : A ⊑ B} →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣ leftCtx (TPEnv.Γ E) ⊢ M ⦂ A →
    E ⊢ M ⊑ (blame ℓ) ⦂ p

------------------------------------------------------------------------
-- Projections back to ordinary typing
------------------------------------------------------------------------

⊑-left-typed :
  ∀ {E M M′ A B} {p : A ⊑ B} →
  E ⊢ M ⊑ M′ ⦂ p →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣ leftCtx (TPEnv.Γ E) ⊢ M ⦂ A
⊑-left-typed (⊑` h) = ⊢` (lookup-left h)
⊑-left-typed (⊑ƛ hA hA′ rel) = ⊢ƛ hA (⊑-left-typed rel)
⊑-left-typed (⊑· relL relM) = ⊢· (⊑-left-typed relL) (⊑-left-typed relM)
⊑-left-typed {E = E} (⊑Λ vM vM′ wfA wfB rel) =
  ⊢Λ vM
    (cong-⊢⦂ refl (leftCtx-⇑ᵗᴾ (TPEnv.Γ E)) refl refl (⊑-left-typed rel))
⊑-left-typed (⊑⦂∀ rel wfA wfB hT) =
  ⊢• (⊑-left-typed rel) wfA hT
⊑-left-typed (⊑⦂∀-ν A B {T = T} p rel wfA hT) =
  ⊢• (⊑-left-typed rel) wfA (WfTy-weakenᵗ hT z≤n)
⊑-left-typed (⊑$ {n}) = ⊢$ (κℕ n)
⊑-left-typed (⊑⊕ {op = op} relL relM) = ⊢⊕ (⊑-left-typed relL) op (⊑-left-typed relM)
⊑-left-typed (⊑up Φ lenΦ rel hu hu′) = ⊢up Φ lenΦ (⊑-left-typed rel) hu
⊑-left-typed (⊑upL Φ lenΦ rel hu) = ⊢up Φ lenΦ (⊑-left-typed rel) hu
⊑-left-typed (⊑upR Φ lenΦ rel hu′) = ⊑-left-typed rel
⊑-left-typed (⊑down Φ lenΦ rel hd hd′) = ⊢down Φ lenΦ (⊑-left-typed rel) hd
⊑-left-typed (⊑downL Φ lenΦ rel hd) = ⊢down Φ lenΦ (⊑-left-typed rel) hd
⊑-left-typed (⊑downR Φ lenΦ rel hd′) = ⊑-left-typed rel
⊑-left-typed (⊑blameR hM) = hM

⊑-right-typed :
  ∀ {E M M′ A B} {p : A ⊑ B} →
  E ⊢ M ⊑ M′ ⦂ p →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣ rightCtx (TPEnv.Γ E) ⊢ M′ ⦂ B
⊑-right-typed (⊑` h) = ⊢` (lookup-right h)
⊑-right-typed (⊑ƛ hA hA′ rel) = ⊢ƛ hA′ (⊑-right-typed rel)
⊑-right-typed (⊑· relL relM) = ⊢· (⊑-right-typed relL) (⊑-right-typed relM)
⊑-right-typed {E = E} (⊑Λ vM vM′ wfA wfB rel) =
  ⊢Λ vM′
    (cong-⊢⦂ refl (rightCtx-⇑ᵗᴾ (TPEnv.Γ E)) refl refl (⊑-right-typed rel))
⊑-right-typed (⊑⦂∀ rel wfA wfB hT) =
  ⊢• (⊑-right-typed rel) wfB hT
⊑-right-typed (⊑⦂∀-ν A B {T = T} p rel wfA hT) =
  ⊑-right-typed rel
⊑-right-typed (⊑$ {n}) = ⊢$ (κℕ n)
⊑-right-typed (⊑⊕ {op = op} relL relM) = ⊢⊕ (⊑-right-typed relL) op (⊑-right-typed relM)
⊑-right-typed (⊑up Φ lenΦ rel hu hu′) = ⊢up Φ lenΦ (⊑-right-typed rel) hu′
⊑-right-typed (⊑upL Φ lenΦ rel hu) = ⊑-right-typed rel
⊑-right-typed (⊑upR Φ lenΦ rel hu′) = ⊢up Φ lenΦ (⊑-right-typed rel) hu′
⊑-right-typed (⊑down Φ lenΦ rel hd hd′) = ⊢down Φ lenΦ (⊑-right-typed rel) hd′
⊑-right-typed (⊑downL Φ lenΦ rel hd) = ⊑-right-typed rel
⊑-right-typed (⊑downR Φ lenΦ rel hd′) = ⊢down Φ lenΦ (⊑-right-typed rel) hd′
⊑-right-typed (⊑blameR hM) = ⊢blame _

⊑-type-imprecision :
  ∀ {E M M′ A B} {p : A ⊑ B} →
  E ⊢ M ⊑ M′ ⦂ p →
  A ⊑ B
⊑-type-imprecision {p = p} rel = p
