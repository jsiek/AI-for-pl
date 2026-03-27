module Imprecision where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (_×_; Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import Types
open import TypeSubst
open import Store

------------------------------------------------------------------------
-- Intrinsic imprecision
--
--   p ::= g | id_⋆ | g;tag_G | seal_α;p | να.p[α]
------------------------------------------------------------------------

infixr 7 _→ᵖ_
infixl 8 _；tag_
infixr 8 seal_；_
infix 4 _∣_∣_⊢_⊑_
infix 4 _∣_∣_⊢ᶜ_⊑_
infix 4 _∉domⱽ_
infix 4 _∉domᴳ_
infix 4 _∈ˢ_

_∉domⱽ_ : ∀{Δ}{Ψ} → TVar Δ Ψ → Store Ψ → Set
(＇ X) ∉domⱽ Σ = ⊤
(｀ α) ∉domⱽ Σ = α ∉domˢ Σ

_∉domᴳ_ : ∀{Δ}{Ψ}{G : Ty Δ Ψ} → Ground G → Store Ψ → Set
_∉domᴳ_ (｀ α) Σ = α ∉domˢ Σ
_∉domᴳ_ (‵ ι) Σ = ⊤
_∉domᴳ_ ★⇒★   Σ = ⊤

data _∈ˢ_ {Δ}{Ψ} (α : Seal Ψ) : Ty Δ Ψ → Set where
  hereˢ : α ∈ˢ (｀ α)
  ⇒ˢˡ  : ∀{A B : Ty Δ Ψ} → α ∈ˢ A → α ∈ˢ (A ⇒ B)
  ⇒ˢʳ  : ∀{A B : Ty Δ Ψ} → α ∈ˢ B → α ∈ˢ (A ⇒ B)
  ∀ˢ   : ∀{A : Ty (suc Δ) Ψ} → α ∈ˢ A → α ∈ˢ (`∀ A)

Freshˢ :
  ∀{Δ}{Ψ} →
  Ty Δ Ψ → Store Ψ → Store Ψ → Set
Freshˢ A Σ Σ′ = ∀{α : Seal _} → α ∈ˢ A → α ∉domˢ Σ → α ∉domˢ Σ′

data Reachˢ {Δ}{Ψ} (Σ : Store Ψ) (A : Ty Δ Ψ) : Seal Ψ → Set where
  srcˢ  :
    ∀{α : Seal Ψ} →
    α ∈ˢ A →
    Reachˢ Σ A α

  stepˢ :
    ∀{α β : Seal Ψ}{A₀ : Ty 0 Ψ} →
    Reachˢ Σ A α →
    Σ ∋ˢ α ⦂ A₀ →
    β ∈ˢ wkTy0 {Δ = Δ} A₀ →
    Reachˢ Σ A β

FreshReachˢ :
  ∀{Δ}{Ψ} →
  Ty Δ Ψ → Store Ψ → Store Ψ → Set
FreshReachˢ A Σ Σ′ =
  ∀{α : Seal _} → Reachˢ Σ A α → α ∉domˢ Σ → α ∉domˢ Σ′

mutual
  data _∣_∣_⊢ᶜ_⊑_ (Δ : TyCtx) (Ψ : SealCtx) (Σ : Store Ψ)
       : Ty Δ Ψ → Ty Δ Ψ → Set where
    idα  : ∀ (α : Seal Ψ) →
           α ∉domˢ Σ →
           Δ ∣ Ψ ∣ Σ ⊢ᶜ (｀ α) ⊑ (｀ α)

    idX  : (X : TyVar Δ) →
           Δ ∣ Ψ ∣ Σ ⊢ᶜ (＇ X) ⊑ (＇ X)

    idι  : (ι : Base) →
           Δ ∣ Ψ ∣ Σ ⊢ᶜ (‵ ι) ⊑ (‵ ι)

    _→ᵖ_ : {A A′ B B′ : Ty Δ Ψ} →
           Δ ∣ Ψ ∣ Σ ⊢ A ⊑ A′ →
           Δ ∣ Ψ ∣ Σ ⊢ B ⊑ B′ →
           Δ ∣ Ψ ∣ Σ ⊢ᶜ (A ⇒ B) ⊑ (A′ ⇒ B′)

    ∀ᵖ_  : {A B : Ty (suc Δ) Ψ} →
           (suc Δ) ∣ Ψ ∣ Σ ⊢ A ⊑ B →
           Δ ∣ Ψ ∣ Σ ⊢ᶜ (`∀ A) ⊑ (`∀ B)

  data _∣_∣_⊢_⊑_ (Δ : TyCtx) (Ψ : SealCtx) (Σ : Store Ψ)
       : Ty Δ Ψ → Ty Δ Ψ → Set where
    ⌈_⌉ : {A B : Ty Δ Ψ} →
          Δ ∣ Ψ ∣ Σ ⊢ᶜ A ⊑ B →
          Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B

    id⋆ : Δ ∣ Ψ ∣ Σ ⊢ `★ ⊑ `★

    _；tag_ : {A G : Ty Δ Ψ}
             → Δ ∣ Ψ ∣ Σ ⊢ᶜ A ⊑ G
             → (g : Ground G)
             → {g∉Σ : g ∉domᴳ Σ}
             → Δ ∣ Ψ ∣ Σ ⊢ A ⊑ `★

    seal_；_ : {α : Seal Ψ} {A : Ty 0 Ψ} {B : Ty Δ Ψ} →
               Σ ∋ˢ α ⦂ A →
               Δ ∣ Ψ ∣ Σ ⊢ (wkTy0 A) ⊑ B →
               Δ ∣ Ψ ∣ Σ ⊢ (｀ α) ⊑ B

    ν_ : {A : Ty (suc Δ) Ψ} {B : Ty Δ Ψ} →
         Δ ∣ (suc Ψ) ∣ ((Zˢ , `★) ∷ ⟰ˢ Σ) ⊢ (((⇑ˢ A) [ ｀ Zˢ ]ᵗ)) ⊑ (⇑ˢ B) →
         Δ ∣ Ψ ∣ Σ ⊢ (`∀ A) ⊑ B

------------------------------------------------------------------------
-- Renaming/substitution for imprecision witnesses
------------------------------------------------------------------------

idⱽ :
  ∀{Δ}{Ψ}{Σ : Store Ψ} (A : TVar Δ Ψ) →
  A ∉domⱽ Σ →
  Δ ∣ Ψ ∣ Σ ⊢ᶜ tvTy A ⊑ tvTy A
idⱽ (＇ X) _ = idX X
idⱽ (｀ α) α∉Σ = idα α α∉Σ

SubstFreshᵗ :
  ∀{Δ}{Δ′}{Ψ} →
  Store Ψ → Substᵗ Δ Δ′ Ψ → Set
SubstFreshᵗ Σ σ = ∀ X → (σ X) ∉domⱽ Σ

renameᵗⱽ-∉domⱽ :
  ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ} →
  (ρ : Renameᵗ Δ Δ′) →
  (V : TVar Δ Ψ) →
  V ∉domⱽ Σ →
  renameᵗⱽ ρ V ∉domⱽ Σ
renameᵗⱽ-∉domⱽ ρ (＇ X) V∉Σ = tt
renameᵗⱽ-∉domⱽ ρ (｀ α) V∉Σ = V∉Σ

SubstFresh-exts :
  ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{σ : Substᵗ Δ Δ′ Ψ} →
  SubstFreshᵗ Σ σ →
  SubstFreshᵗ Σ (extsᵗ σ)
SubstFresh-exts fr Zᵗ = tt
SubstFresh-exts {σ = σ} fr (Sᵗ X) =
  renameᵗⱽ-∉domⱽ Sᵗ (σ X) (fr X)

Sˢ∉dom-ν :
  ∀{Ψ}{Σ : Store Ψ}{α : Seal Ψ}{A : Ty 0 (suc Ψ)} →
  α ∉domˢ Σ →
  Sˢ α ∉domˢ ((Zˢ , A) ∷ ⟰ˢ Σ)
Sˢ∉dom-ν α∉Σ (Z∋ˢ () A≡B)
Sˢ∉dom-ν α∉Σ (S∋ˢ h) = Sˢ∉dom-⟰ˢ α∉Σ h

⇑ˢⱽ-∉domⱽ :
  ∀{Δ}{Ψ}{Σ : Store Ψ} →
  (A : Ty 0 (suc Ψ)) →
  (V : TVar Δ Ψ) →
  V ∉domⱽ Σ →
  ⇑ˢⱽ V ∉domⱽ ((Zˢ , A) ∷ ⟰ˢ Σ)
⇑ˢⱽ-∉domⱽ A (＇ X) V∉Σ = tt
⇑ˢⱽ-∉domⱽ A (｀ α) V∉Σ = Sˢ∉dom-ν V∉Σ

SubstFresh-liftˢ :
  ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{σ : Substᵗ Δ Δ′ Ψ} →
  (A : Ty 0 (suc Ψ)) →
  SubstFreshᵗ Σ σ →
  SubstFreshᵗ ((Zˢ , A) ∷ ⟰ˢ Σ) (liftSubstˢ σ)
SubstFresh-liftˢ {σ = σ} A fr X =
  ⇑ˢⱽ-∉domⱽ A (σ X) (fr X)

∉domˢ-⊆ˢ :
  ∀{Ψ}{Σ Σ′ : Store Ψ}{α : Seal Ψ} →
  Σ′ ⊆ˢ Σ →
  α ∉domˢ Σ →
  α ∉domˢ Σ′
∉domˢ-⊆ˢ w α∉Σ h = α∉Σ (wkLookupˢ w h)

∉domⱽ-⊆ˢ :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ} →
  (w : Σ′ ⊆ˢ Σ) →
  (V : TVar Δ Ψ) →
  V ∉domⱽ Σ →
  V ∉domⱽ Σ′
∉domⱽ-⊆ˢ w (＇ X) V∉Σ = tt
∉domⱽ-⊆ˢ w (｀ α) V∉Σ = ∉domˢ-⊆ˢ w V∉Σ

SubstFresh-⊆ˢ :
  ∀{Δ}{Δ′}{Ψ}{Σ Σ′ : Store Ψ}{σ : Substᵗ Δ Δ′ Ψ} →
  Σ′ ⊆ˢ Σ →
  SubstFreshᵗ Σ σ →
  SubstFreshᵗ Σ′ σ
SubstFresh-⊆ˢ {σ = σ} w fr X = ∉domⱽ-⊆ˢ w (σ X) (fr X)

cong-⊑-≡ :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{A A′ B B′ : Ty Δ Ψ} →
  A ≡ A′ →
  B ≡ B′ →
  Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B →
  Δ ∣ Ψ ∣ Σ ⊢ A′ ⊑ B′
cong-⊑-≡ refl refl p = p

castΣ⊑ :
  ∀ {Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B : Ty Δ Ψ} →
  Σ ≡ Σ′ →
  Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B →
  Δ ∣ Ψ ∣ Σ′ ⊢ A ⊑ B
castΣ⊑ refl p = p

------------------------------------------------------------------------
-- Store weakening for imprecision witnesses
------------------------------------------------------------------------

reach-⇒ˡ :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ}{α : Seal Ψ} →
  Reachˢ Σ A α →
  Reachˢ Σ (A ⇒ B) α
reach-⇒ˡ (srcˢ α∈A) = srcˢ (⇒ˢˡ α∈A)
reach-⇒ˡ (stepˢ r h α∈A₀) = stepˢ (reach-⇒ˡ r) h α∈A₀

reach-⇒ʳ :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ}{α : Seal Ψ} →
  Reachˢ Σ B α →
  Reachˢ Σ (A ⇒ B) α
reach-⇒ʳ (srcˢ α∈B) = srcˢ (⇒ˢʳ α∈B)
reach-⇒ʳ (stepˢ r h α∈A₀) = stepˢ (reach-⇒ʳ r) h α∈A₀

fresh-⇒ˡ :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B : Ty Δ Ψ} →
  FreshReachˢ (A ⇒ B) Σ Σ′ →
  FreshReachˢ A Σ Σ′
fresh-⇒ˡ fr r α∉Σ = fr (reach-⇒ˡ r) α∉Σ

fresh-⇒ʳ :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B : Ty Δ Ψ} →
  FreshReachˢ (A ⇒ B) Σ Σ′ →
  FreshReachˢ B Σ Σ′
fresh-⇒ʳ fr r α∉Σ = fr (reach-⇒ʳ r) α∉Σ

∈ˢ-renameᵗ-irrelevant :
  ∀{Δ}{Δ′}{Δ″}{Ψ}{α : Seal Ψ}{A : Ty Δ Ψ} →
  (ρ : Renameᵗ Δ Δ′) →
  (ρ′ : Renameᵗ Δ Δ″) →
  α ∈ˢ renameᵗ ρ A →
  α ∈ˢ renameᵗ ρ′ A
∈ˢ-renameᵗ-irrelevant {A = ＇ X} ρ ρ′ ()
∈ˢ-renameᵗ-irrelevant {A = ｀ α} ρ ρ′ hereˢ = hereˢ
∈ˢ-renameᵗ-irrelevant {A = ‵ ι} ρ ρ′ ()
∈ˢ-renameᵗ-irrelevant {A = `★} ρ ρ′ ()
∈ˢ-renameᵗ-irrelevant {A = A ⇒ B} ρ ρ′ (⇒ˢˡ α∈A) =
  ⇒ˢˡ (∈ˢ-renameᵗ-irrelevant ρ ρ′ α∈A)
∈ˢ-renameᵗ-irrelevant {A = A ⇒ B} ρ ρ′ (⇒ˢʳ α∈B) =
  ⇒ˢʳ (∈ˢ-renameᵗ-irrelevant ρ ρ′ α∈B)
∈ˢ-renameᵗ-irrelevant {A = `∀ A} ρ ρ′ (∀ˢ α∈A) =
  ∀ˢ (∈ˢ-renameᵗ-irrelevant (extᵗ ρ) (extᵗ ρ′) α∈A)

wkTy0-∈ˢ-Δ :
  ∀{Δ}{Δ′}{Ψ}{α : Seal Ψ}{A : Ty 0 Ψ} →
  α ∈ˢ wkTy0 {Δ = Δ} A →
  α ∈ˢ wkTy0 {Δ = Δ′} A
wkTy0-∈ˢ-Δ {A = A} α∈A =
  ∈ˢ-renameᵗ-irrelevant {A = A} lift0ᵗ lift0ᵗ α∈A

reach-∀ :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty (suc Δ) Ψ}{α : Seal Ψ} →
  Reachˢ Σ A α →
  Reachˢ Σ (`∀ A) α
reach-∀ (srcˢ α∈A) = srcˢ (∀ˢ α∈A)
reach-∀ {Δ = Δ} (stepˢ r h β∈A₀) =
  stepˢ (reach-∀ r) h (wkTy0-∈ˢ-Δ {Δ = suc Δ} {Δ′ = Δ} β∈A₀)

fresh-∀ :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{A : Ty (suc Δ) Ψ} →
  FreshReachˢ (`∀ A) Σ Σ′ →
  FreshReachˢ A Σ Σ′
fresh-∀ fr r α∉Σ = fr (reach-∀ r) α∉Σ

reach-seal-payload :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{α : Seal Ψ}{A₀ : Ty 0 Ψ}{β : Seal Ψ} →
  Σ ∋ˢ α ⦂ A₀ →
  Reachˢ Σ (wkTy0 {Δ = Δ} A₀) β →
  Reachˢ Σ (｀ α) β
reach-seal-payload h (srcˢ β∈A₀) = stepˢ (srcˢ hereˢ) h β∈A₀
reach-seal-payload h (stepˢ r h′ β∈B₀) = stepˢ (reach-seal-payload h r) h′ β∈B₀

fresh-seal :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{α : Seal Ψ}{A₀ : Ty 0 Ψ} →
  FreshReachˢ (｀ α) Σ Σ′ →
  Σ ∋ˢ α ⦂ A₀ →
  FreshReachˢ (wkTy0 {Δ = Δ} A₀) Σ Σ′
fresh-seal fr h r β∉Σ = fr (reach-seal-payload h r) β∉Σ

seal-in-src :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty Δ Ψ}{α : Seal Ψ} →
  Δ ∣ Ψ ∣ Σ ⊢ᶜ A ⊑ (｀ α) →
  α ∈ˢ A
seal-in-src (idα α α∉Σ) = hereˢ

∉domᴳ-pres :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{A G : Ty Δ Ψ} →
  FreshReachˢ A Σ Σ′ →
  Δ ∣ Ψ ∣ Σ ⊢ᶜ A ⊑ G →
  (g : Ground G) →
  g ∉domᴳ Σ →
  g ∉domᴳ Σ′
∉domᴳ-pres fr p (｀ α) α∉Σ = fr (srcˢ (seal-in-src p)) α∉Σ
∉domᴳ-pres fr p (‵ ι) g∉Σ = tt
∉domᴳ-pres fr p ★⇒★ g∉Σ = tt

NoSealInSubst :
  ∀{Δ}{Δ′}{Ψ} →
  Seal Ψ → Substᵗ Δ Δ′ Ψ → Set
NoSealInSubst γ σ = ∀ X → γ ∈ˢ tvTy (σ X) → ⊥

∈ˢ-renameᵗⱽ-inv :
  ∀{Δ}{Δ′}{Ψ}{γ : Seal Ψ}{V : TVar Δ Ψ} →
  (ρ : Renameᵗ Δ Δ′) →
  γ ∈ˢ tvTy (renameᵗⱽ ρ V) →
  γ ∈ˢ tvTy V
∈ˢ-renameᵗⱽ-inv {V = ＇ X} ρ ()
∈ˢ-renameᵗⱽ-inv {V = ｀ α} ρ hereˢ = hereˢ

NoSealInSubst-exts :
  ∀{Δ}{Δ′}{Ψ}{γ : Seal Ψ}{σ : Substᵗ Δ Δ′ Ψ} →
  NoSealInSubst γ σ →
  NoSealInSubst γ (extsᵗ σ)
NoSealInSubst-exts noσ Zᵗ ()
NoSealInSubst-exts noσ (Sᵗ X) p =
  noσ X (∈ˢ-renameᵗⱽ-inv Sᵗ p)

∈ˢ-subst-noSeal-inv :
  ∀{Δ}{Δ′}{Ψ}{γ : Seal Ψ}{σ : Substᵗ Δ Δ′ Ψ}{A : Ty Δ Ψ} →
  NoSealInSubst γ σ →
  γ ∈ˢ substᵗ σ A →
  γ ∈ˢ A
∈ˢ-subst-noSeal-inv {A = ＇ X} noσ p = ⊥-elim (noσ X p)
∈ˢ-subst-noSeal-inv {A = ｀ α} noσ hereˢ = hereˢ
∈ˢ-subst-noSeal-inv {A = ‵ ι} noσ ()
∈ˢ-subst-noSeal-inv {A = `★} noσ ()
∈ˢ-subst-noSeal-inv {A = A ⇒ B} noσ (⇒ˢˡ p) =
  ⇒ˢˡ (∈ˢ-subst-noSeal-inv noσ p)
∈ˢ-subst-noSeal-inv {A = A ⇒ B} noσ (⇒ˢʳ p) =
  ⇒ˢʳ (∈ˢ-subst-noSeal-inv noσ p)
∈ˢ-subst-noSeal-inv {A = `∀ A} noσ (∀ˢ p) =
  ∀ˢ (∈ˢ-subst-noSeal-inv (NoSealInSubst-exts noσ) p)

NoSeal-singleZ-S :
  ∀{Δ}{Ψ}{β : Seal Ψ} →
  NoSealInSubst {Δ = suc Δ} {Δ′ = Δ} {Ψ = suc Ψ}
    (Sˢ β) (singleTyEnv (｀ Zˢ))
NoSeal-singleZ-S Zᵗ ()
NoSeal-singleZ-S (Sᵗ X) ()

∈ˢ-[Z]-S-inv :
  ∀{Δ}{Ψ}{A : Ty (suc Δ) (suc Ψ)}{β : Seal Ψ} →
  Sˢ β ∈ˢ (A [ ｀ Zˢ ]ᵗ) →
  Sˢ β ∈ˢ A
∈ˢ-[Z]-S-inv p = ∈ˢ-subst-noSeal-inv NoSeal-singleZ-S p

∈ˢ-renameˢ-S-inv :
  ∀{Δ}{Ψ}{A : Ty Δ Ψ}{β : Seal Ψ} →
  Sˢ β ∈ˢ renameˢ Sˢ A →
  β ∈ˢ A
∈ˢ-renameˢ-S-inv {A = ＇ X} ()
∈ˢ-renameˢ-S-inv {A = ｀ α} hereˢ = hereˢ
∈ˢ-renameˢ-S-inv {A = ‵ ι} ()
∈ˢ-renameˢ-S-inv {A = `★} ()
∈ˢ-renameˢ-S-inv {A = A ⇒ B} (⇒ˢˡ p) = ⇒ˢˡ (∈ˢ-renameˢ-S-inv p)
∈ˢ-renameˢ-S-inv {A = A ⇒ B} (⇒ˢʳ p) = ⇒ˢʳ (∈ˢ-renameˢ-S-inv p)
∈ˢ-renameˢ-S-inv {A = `∀ A} (∀ˢ p) = ∀ˢ (∈ˢ-renameˢ-S-inv p)

wkTy0-⇑ˢ-∈ˢ-S-inv :
  ∀{Δ}{Ψ}{A : Ty 0 Ψ}{β : Seal Ψ} →
  Sˢ β ∈ˢ wkTy0 {Δ = Δ} (⇑ˢ A) →
  β ∈ˢ wkTy0 {Δ = Δ} A
wkTy0-⇑ˢ-∈ˢ-S-inv {A = A} p =
  ∈ˢ-renameˢ-S-inv
    (subst (λ T → Sˢ _ ∈ˢ T) (sym (renameˢ-wkTy0 Sˢ A)) p)

ν-src-∈ˢ-S-inv :
  ∀{Δ}{Ψ}{A : Ty (suc Δ) Ψ}{β : Seal Ψ} →
  Sˢ β ∈ˢ (((⇑ˢ A) [ ｀ Zˢ ]ᵗ)) →
  β ∈ˢ (`∀ A)
ν-src-∈ˢ-S-inv p =
  ∀ˢ (∈ˢ-renameˢ-S-inv (∈ˢ-[Z]-S-inv p))

lookup-Sˢ-⟰ˢ′ :
  ∀{Ψ}{Σˢ : Store Ψ}{α : Seal Ψ}{A : Ty 0 (suc Ψ)} →
  ⟰ˢ Σˢ ∋ˢ Sˢ α ⦂ A →
  Σ (Ty 0 Ψ) (λ B → Σ (A ≡ ⇑ˢ B) (λ _ → Σˢ ∋ˢ α ⦂ B))
lookup-Sˢ-⟰ˢ′ {Σˢ = []} ()
lookup-Sˢ-⟰ˢ′ {Σˢ = (β , B) ∷ Σ} (Z∋ˢ α≡Sβ A≡⇑B) =
  B , A≡⇑B , Z∋ˢ (Sˢ-injective α≡Sβ) refl
lookup-Sˢ-⟰ˢ′ {Σˢ = (β , B) ∷ Σ} (S∋ˢ h)
  with lookup-Sˢ-⟰ˢ′ {Σˢ = Σ} h
... | C , A≡⇑C , hC = C , A≡⇑C , S∋ˢ hC

Sˢ∈wkTy0★-⊥ :
  ∀{Δ}{Ψ}{β : Seal Ψ} →
  Sˢ β ∈ˢ (wkTy0 {Δ = Δ} {Ψ = suc Ψ} `★) →
  ⊥
Sˢ∈wkTy0★-⊥ ()

lookup-Z-⟰ˢ-⊥ :
  ∀{Ψ}{Σ : Store Ψ}{A : Ty 0 (suc Ψ)} →
  ⟰ˢ Σ ∋ˢ Zˢ ⦂ A →
  ⊥
lookup-Z-⟰ˢ-⊥ h = Zˢ∉dom-⟰ˢ h

reach-ν-src-S :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A : Ty (suc Δ) Ψ}{β : Seal Ψ} →
  Reachˢ ((Zˢ , `★) ∷ ⟰ˢ Σ) (((⇑ˢ A) [ ｀ Zˢ ]ᵗ)) (Sˢ β) →
  Reachˢ Σ (`∀ A) β
reach-ν-src-S (srcˢ p) = srcˢ (ν-src-∈ˢ-S-inv p)
reach-ν-src-S {β = β} (stepˢ {α = α} r h p) with α | h
... | Zˢ | Z∋ˢ refl refl = ⊥-elim (Sˢ∈wkTy0★-⊥ p)
... | Zˢ | S∋ˢ h′ = ⊥-elim (lookup-Z-⟰ˢ-⊥ h′)
... | Sˢ γ | Z∋ˢ () _
... | Sˢ γ | S∋ˢ h′ with lookup-Sˢ-⟰ˢ′ h′
...   | B , A₀≡⇑B , hB =
        stepˢ (reach-ν-src-S r) hB
          (wkTy0-⇑ˢ-∈ˢ-S-inv (subst (λ T → Sˢ β ∈ˢ wkTy0 T) A₀≡⇑B p))

∉dom-ν-S-inv :
  ∀{Ψ}{Σ : Store Ψ}{β : Seal Ψ} →
  Sˢ β ∉domˢ ((Zˢ , `★) ∷ ⟰ˢ Σ) →
  β ∉domˢ Σ
∉dom-ν-S-inv Sβ∉ h =
  Sβ∉ (S∋ˢ (renameLookupˢ Sˢ h))

fresh-ν-src :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{A : Ty (suc Δ) Ψ} →
  FreshReachˢ (`∀ A) Σ Σ′ →
  FreshReachˢ (((⇑ˢ A) [ ｀ Zˢ ]ᵗ))
             ((Zˢ , `★) ∷ ⟰ˢ Σ)
             ((Zˢ , `★) ∷ ⟰ˢ Σ′)
fresh-ν-src fr {α = Zˢ} r Z∉ =
  ⊥-elim (Z∉ (Z∋ˢ refl refl))
fresh-ν-src {Σ′ = Σ′} fr {α = Sˢ β} r Sβ∉ =
  Sˢ∉dom-ν {Σ = Σ′} (fr (reach-ν-src-S r) (∉dom-ν-S-inv Sβ∉))

mutual
  wkΣᶜ :
    ∀ {Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B : Ty Δ Ψ} →
    Σ ⊆ˢ Σ′ →
    FreshReachˢ A Σ Σ′ →
    Δ ∣ Ψ ∣ Σ ⊢ᶜ A ⊑ B →
    Δ ∣ Ψ ∣ Σ′ ⊢ᶜ A ⊑ B
  wkΣᶜ w freshA (idα α α∉Σ) =
    idα α (freshA (srcˢ hereˢ) α∉Σ)
  wkΣᶜ w pres (idX X) = idX X
  wkΣᶜ w pres (idι ι) = idι ι
  wkΣᶜ {A = A ⇒ B} w freshAB (p →ᵖ q) =
    wkΣᵖ w (fresh-⇒ˡ freshAB) p →ᵖ wkΣᵖ w (fresh-⇒ʳ freshAB) q
  wkΣᶜ {A = `∀ A} w fresh∀ (∀ᵖ p) =
    ∀ᵖ (wkΣᵖ w (fresh-∀ fresh∀) p)

  wkΣᵖ :
    ∀ {Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B : Ty Δ Ψ} →
    Σ ⊆ˢ Σ′ →
    FreshReachˢ A Σ Σ′ →
    Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B →
    Δ ∣ Ψ ∣ Σ′ ⊢ A ⊑ B
  wkΣᵖ w freshA ⌈ g ⌉ = ⌈ wkΣᶜ w freshA g ⌉
  wkΣᵖ w freshA id⋆ = id⋆
  wkΣᵖ w freshA (_；tag_ p g {g∉Σ = g∉Σ}) =
    _；tag_ (wkΣᶜ w freshA p) g {g∉Σ = ∉domᴳ-pres freshA p g g∉Σ}
  wkΣᵖ w freshA (seal h ； p) =
    seal (wkLookupˢ w h) ； wkΣᵖ w (fresh-seal freshA h) p
  wkΣᵖ {A = `∀ A} w freshA (ν p) =
    ν (wkΣᵖ (ν-⊆ˢ `★ w) (fresh-ν-src freshA) p)

renameᵗ-∉domᴳ :
  ∀ {Δ}{Δ′}{Ψ}{Σ : Store Ψ}{G : Ty Δ Ψ}
  (ρ : Renameᵗ Δ Δ′) (g : Ground G) →
  g ∉domᴳ Σ →
  renameᵗ-ground ρ g ∉domᴳ Σ
renameᵗ-∉domᴳ ρ (｀ α) α∉Σ = α∉Σ
renameᵗ-∉domᴳ ρ (‵ ι) g∉Σ = tt
renameᵗ-∉domᴳ ρ ★⇒★ g∉Σ = tt

mutual
  renameᵗᶜ :
    ∀ {Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (ρ : Renameᵗ Δ Δ′) →
    Δ ∣ Ψ ∣ Σ ⊢ᶜ A ⊑ B →
    Δ′ ∣ Ψ ∣ Σ ⊢ᶜ renameᵗ ρ A ⊑ renameᵗ ρ B
  renameᵗᶜ ρ (idα α α∉Σ) = idα α α∉Σ
  renameᵗᶜ ρ (idX X) = idX (ρ X)
  renameᵗᶜ ρ (idι ι) = idι ι
  renameᵗᶜ ρ (p →ᵖ q) = renameᵗᵖ ρ p →ᵖ renameᵗᵖ ρ q
  renameᵗᶜ ρ (∀ᵖ p) = ∀ᵖ (renameᵗᵖ (extᵗ ρ) p)

  renameᵗᵖ :
    ∀ {Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (ρ : Renameᵗ Δ Δ′) →
    Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B →
    Δ′ ∣ Ψ ∣ Σ ⊢ renameᵗ ρ A ⊑ renameᵗ ρ B
  renameᵗᵖ ρ ⌈ g ⌉ = ⌈ renameᵗᶜ ρ g ⌉
  renameᵗᵖ ρ id⋆ = id⋆
  renameᵗᵖ {Δ′ = Δ′} {Ψ = Ψ} {Σ = Σ} {A = A}
    ρ (_；tag_ p g {g∉Σ = g∉Σ}) =
    _；tag_ (renameᵗᶜ ρ p) (renameᵗ-ground ρ g)
      {g∉Σ = renameᵗ-∉domᴳ ρ g g∉Σ}
  renameᵗᵖ {Δ′ = Δ′} {Ψ = Ψ} {Σ = Σ} {B = B} ρ (seal_；_ {A = A} h p) =
    seal h ；
      subst
        (λ T → Δ′ ∣ Ψ ∣ Σ ⊢ T ⊑ renameᵗ ρ B)
        (renameᵗ-wkTy0 ρ A)
        (renameᵗᵖ ρ p)
  renameᵗᵖ ρ (ν_ {A = A} {B = B} p) =
    ν (cong-⊑-≡ (renameᵗ-ν-src ρ A) (renameᵗ-⇑ˢ ρ B) (renameᵗᵖ ρ p))

substᵗ-∉domᴳ :
  ∀ {Δ}{Δ′}{Ψ}{Σ : Store Ψ}{G : Ty Δ Ψ}
  (σ : Substᵗ Δ Δ′ Ψ) (g : Ground G) →
  g ∉domᴳ Σ →
  substᵗ-ground σ g ∉domᴳ Σ
substᵗ-∉domᴳ σ (｀ α) α∉Σ = α∉Σ
substᵗ-∉domᴳ σ (‵ ι) g∉Σ = tt
substᵗ-∉domᴳ σ ★⇒★ g∉Σ = tt

mutual
  substᵗᶜ :
    ∀ {Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (σ : Substᵗ Δ Δ′ Ψ) →
    SubstFreshᵗ Σ σ →
    Δ ∣ Ψ ∣ Σ ⊢ᶜ A ⊑ B →
    Δ′ ∣ Ψ ∣ Σ ⊢ᶜ substᵗ σ A ⊑ substᵗ σ B
  substᵗᶜ σ freshσ (idα α α∉Σ) = idα α α∉Σ
  substᵗᶜ σ freshσ (idX X) = idⱽ (σ X) (freshσ X)
  substᵗᶜ σ freshσ (idι ι) = idι ι
  substᵗᶜ σ freshσ (p →ᵖ q) = substᵗᵖ σ freshσ p →ᵖ substᵗᵖ σ freshσ q
  substᵗᶜ σ freshσ (∀ᵖ p) = ∀ᵖ (substᵗᵖ (extsᵗ σ) (SubstFresh-exts freshσ) p)

  substᵗᵖ :
    ∀ {Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (σ : Substᵗ Δ Δ′ Ψ) →
    SubstFreshᵗ Σ σ →
    Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B →
    Δ′ ∣ Ψ ∣ Σ ⊢ substᵗ σ A ⊑ substᵗ σ B
  substᵗᵖ σ freshσ ⌈ g ⌉ = ⌈ substᵗᶜ σ freshσ g ⌉
  substᵗᵖ σ freshσ id⋆ = id⋆
  substᵗᵖ {Δ′ = Δ′} {Ψ = Ψ} {Σ = Σ} {A = A}
    σ freshσ (_；tag_ p G {g∉Σ = G∉Σ}) =
    _；tag_ (substᵗᶜ σ freshσ p) (substᵗ-ground σ G)
      {g∉Σ = substᵗ-∉domᴳ σ G G∉Σ}
  substᵗᵖ {Δ′ = Δ′} {Ψ = Ψ} {Σ = Σ} {B = B} σ freshσ (seal_；_ {A = A} h p) =
    seal h ；
      subst
        (λ T → Δ′ ∣ Ψ ∣ Σ ⊢ T ⊑ substᵗ σ B)
        (substᵗ-wkTy0 σ A)
        (substᵗᵖ σ freshσ p)
  substᵗᵖ σ freshσ (ν_ {A = A} {B = B} p) =
    ν (cong-⊑-≡ (substᵗ-ν-src σ A) (substᵗ-⇑ˢ σ B)
         (substᵗᵖ (liftSubstˢ σ) (SubstFresh-liftˢ `★ freshσ) p))

RenameFreshˢ :
  ∀{Ψ}{Ψ′} →
  Renameˢ Ψ Ψ′ → Set
RenameFreshˢ ρ =
  ∀{α β} →
  ρ α ≡ ρ β →
  α ≡ β

lookup-renameStoreˢ-inv :
  ∀{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}{Σˢ : Store Ψ}{α : Seal Ψ}{A : Ty 0 Ψ′} →
  RenameFreshˢ ρ →
  renameStoreˢ ρ Σˢ ∋ˢ ρ α ⦂ A →
  Σ (Ty 0 Ψ) (λ B → Σˢ ∋ˢ α ⦂ B)
lookup-renameStoreˢ-inv {Σˢ = []} fresh ()
lookup-renameStoreˢ-inv {ρ = ρ} {Σˢ = (β , B) ∷ Σ} {α = α} fresh (Z∋ˢ α≡ρβ A≡ρB) =
  B , Z∋ˢ (fresh α≡ρβ) refl
lookup-renameStoreˢ-inv {ρ = ρ} {Σˢ = (β , B) ∷ Σ} fresh (S∋ˢ h)
  with lookup-renameStoreˢ-inv {ρ = ρ} {Σˢ = Σ} fresh h
... | C , hC = C , S∋ˢ hC

renameFresh-∉domˢ :
  ∀{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}{Σ : Store Ψ}{α : Seal Ψ} →
  RenameFreshˢ ρ →
  α ∉domˢ Σ →
  ρ α ∉domˢ renameStoreˢ ρ Σ
renameFresh-∉domˢ {ρ = ρ} fresh α∉ h
  with lookup-renameStoreˢ-inv {ρ = ρ} fresh h
... | A , hA = α∉ hA

RenameFresh-extˢ :
  ∀{Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′} →
  RenameFreshˢ ρ →
  RenameFreshˢ (extˢ ρ)
RenameFresh-extˢ fresh {α = Zˢ} {β = Zˢ} refl = refl
RenameFresh-extˢ fresh {α = Zˢ} {β = Sˢ β} ()
RenameFresh-extˢ fresh {α = Sˢ α} {β = Zˢ} ()
RenameFresh-extˢ fresh {α = Sˢ α} {β = Sˢ β} eq =
  cong Sˢ (fresh (Sˢ-injective eq))

RenameFresh-Sˢ :
  ∀{Ψ} →
  RenameFreshˢ (Sˢ {Ψ = Ψ})
RenameFresh-Sˢ = Sˢ-injective

renameˢ-∉domᴳ :
  ∀ {Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{G : Ty Δ Ψ}
  (ρ : Renameˢ Ψ Ψ′) →
  RenameFreshˢ ρ →
  (g : Ground G) →
  g ∉domᴳ Σ →
  renameˢ-ground ρ g ∉domᴳ renameStoreˢ ρ Σ
renameˢ-∉domᴳ ρ fresh (｀ α) α∉Σ = renameFresh-∉domˢ fresh α∉Σ
renameˢ-∉domᴳ ρ fresh (‵ ι) g∉Σ = tt
renameˢ-∉domᴳ ρ fresh ★⇒★ g∉Σ = tt

mutual
  renameˢᶜ :
    ∀ {Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (ρ : Renameˢ Ψ Ψ′) →
    RenameFreshˢ ρ →
    Δ ∣ Ψ ∣ Σ ⊢ᶜ A ⊑ B →
    Δ ∣ Ψ′ ∣ renameStoreˢ ρ Σ ⊢ᶜ renameˢ ρ A ⊑ renameˢ ρ B
  renameˢᶜ ρ fresh (idα α α∉Σ) = idα (ρ α) (renameFresh-∉domˢ fresh α∉Σ)
  renameˢᶜ ρ fresh (idX X) = idX X
  renameˢᶜ ρ fresh (idι ι) = idι ι
  renameˢᶜ ρ fresh (p →ᵖ q) = renameˢᵖ ρ fresh p →ᵖ renameˢᵖ ρ fresh q
  renameˢᶜ ρ fresh (∀ᵖ p) = ∀ᵖ (renameˢᵖ ρ fresh p)

  renameˢᵖ :
    ∀ {Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (ρ : Renameˢ Ψ Ψ′) →
    RenameFreshˢ ρ →
    Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B →
    Δ ∣ Ψ′ ∣ renameStoreˢ ρ Σ ⊢ renameˢ ρ A ⊑ renameˢ ρ B
  renameˢᵖ ρ fresh ⌈ g ⌉ = ⌈ renameˢᶜ ρ fresh g ⌉
  renameˢᵖ ρ fresh id⋆ = id⋆
  renameˢᵖ ρ fresh (_；tag_ p g {g∉Σ = g∉Σ}) =
    _；tag_ (renameˢᶜ ρ fresh p) (renameˢ-ground ρ g)
      {g∉Σ = renameˢ-∉domᴳ ρ fresh g g∉Σ}
  renameˢᵖ {Δ = Δ} {Ψ = Ψ} {Ψ′ = Ψ′} {Σ = Σ} {B = B}
    ρ fresh (seal_；_ {A = A} h p) =
    seal (renameLookupˢ ρ h) ；
      subst
        (λ T → Δ ∣ Ψ′ ∣ renameStoreˢ ρ Σ ⊢ T ⊑ renameˢ ρ B)
        (renameˢ-wkTy0 ρ A)
        (renameˢᵖ ρ fresh p)
  renameˢᵖ {Δ = Δ} {Ψ = Ψ} {Ψ′ = Ψ′} {Σ = Σ}
    ρ fresh (ν_ {A = A} {B = B} p) =
    ν (castΣ⊑ (renameStoreˢ-↑★ ρ Σ)
         (cong-⊑-≡
           (renameˢ-ν-src ρ A)
           (renameˢ-⇑ˢ ρ B)
           (renameˢᵖ (extˢ ρ) (RenameFresh-extˢ fresh) p)))

------------------------------------------------------------------------
-- sealToTag (intrinsic): rewrite ν-opened seals into tags
------------------------------------------------------------------------

seal-≟ᵢ :
  ∀{Ψ} →
  (α β : Seal Ψ) →
  Dec (α ≡ β)
seal-≟ᵢ Zˢ Zˢ = yes refl
seal-≟ᵢ Zˢ (Sˢ β) = no (λ ())
seal-≟ᵢ (Sˢ α) Zˢ = no (λ ())
seal-≟ᵢ (Sˢ α) (Sˢ β) with seal-≟ᵢ α β
... | yes eq = yes (cong Sˢ eq)
... | no neq = no (λ { refl → neq refl })

replace :
  ∀{Ψ} →
  Seal Ψ → Seal Ψ → Seal Ψ → Seal Ψ
replace′ :
  ∀{Ψ}{α γ : Seal Ψ} →
  Dec (α ≡ γ) →
  Seal Ψ →
  Seal Ψ
replace′ {γ = γ} (yes _) β = β
replace′ {γ = γ} (no _)  β = γ

replace α β γ = replace′ {α = α} {γ = γ} (seal-≟ᵢ α γ) β

replaceᵗ :
  ∀{Δ}{Ψ} →
  Seal Ψ → Seal Ψ → Ty Δ Ψ → Ty Δ Ψ
replaceᵗ α β = renameˢ (replace α β)

SameDropˢ :
  ∀{Δ}{Ψ} →
  (α β δ : Seal Ψ) →
  Ty Δ Ψ →
  Store Ψ → Store Ψ → Set
SameDropˢ {Ψ = Ψ} α β δ A Σ Σ′ =
  ∀{γ : Seal Ψ}{A₀ : Ty 0 Ψ} →
  (γ ≡ α → ⊥) →
  Σ ∋ˢ γ ⦂ A₀ →
  (Σ′ ∋ˢ γ ⦂ replaceᵗ α β A₀) ⊎
  ((γ ≡ δ) × (Reachˢ Σ A γ → ⊥))

replaceᵗ-Z-⇑ˢ-id :
  ∀{Δ}{Ψ} →
  (β : Seal (suc Ψ)) →
  (A : Ty Δ Ψ) →
  replaceᵗ Zˢ β (⇑ˢ A) ≡ ⇑ˢ A
replaceᵗ-Z-⇑ˢ-id β (＇ X) = refl
replaceᵗ-Z-⇑ˢ-id β (｀ α) = refl
replaceᵗ-Z-⇑ˢ-id β (‵ ι) = refl
replaceᵗ-Z-⇑ˢ-id β `★ = refl
replaceᵗ-Z-⇑ˢ-id β (A ⇒ B) =
  cong₂ _⇒_ (replaceᵗ-Z-⇑ˢ-id β A) (replaceᵗ-Z-⇑ˢ-id β B)
replaceᵗ-Z-⇑ˢ-id β (`∀ A) =
  cong `∀ (replaceᵗ-Z-⇑ˢ-id β A)

replace-S-Z :
  ∀{Ψ} →
  (α β : Seal Ψ) →
  replace (Sˢ α) (Sˢ β) Zˢ ≡ Zˢ
replace-S-Z α β = refl

replace-S-S :
  ∀{Ψ} →
  (α β γ : Seal Ψ) →
  replace (Sˢ α) (Sˢ β) (Sˢ γ) ≡ Sˢ (replace α β γ)
replace-S-S α β γ with seal-≟ᵢ α γ
... | yes eq = refl
... | no neq = refl

replaceᵗ-S-⇑ˢ :
  ∀{Δ}{Ψ} →
  (α β : Seal Ψ) →
  (A : Ty Δ Ψ) →
  replaceᵗ (Sˢ α) (Sˢ β) (⇑ˢ A) ≡ ⇑ˢ (replaceᵗ α β A)
replaceᵗ-S-⇑ˢ α β (＇ X) = refl
replaceᵗ-S-⇑ˢ α β (｀ γ) = cong ｀_ (replace-S-S α β γ)
replaceᵗ-S-⇑ˢ α β (‵ ι) = refl
replaceᵗ-S-⇑ˢ α β `★ = refl
replaceᵗ-S-⇑ˢ α β (A ⇒ B) =
  cong₂ _⇒_ (replaceᵗ-S-⇑ˢ α β A) (replaceᵗ-S-⇑ˢ α β B)
replaceᵗ-S-⇑ˢ α β (`∀ A) =
  cong `∀ (replaceᵗ-S-⇑ˢ α β A)

replaceᵗ-S-ν-src :
  ∀{Δ}{Ψ} →
  (α β : Seal Ψ) →
  (A : Ty (suc Δ) Ψ) →
  replaceᵗ (Sˢ α) (Sˢ β) (((⇑ˢ A) [ ｀ Zˢ ]ᵗ)) ≡
  ((⇑ˢ (replaceᵗ α β A)) [ ｀ Zˢ ]ᵗ)
replaceᵗ-S-ν-src α β A =
  trans
    (renameˢ-[]ᵗ-commute (replace (Sˢ α) (Sˢ β)) (⇑ˢ A) (｀ Zˢ))
    (trans
      (cong
        (λ T → T [ ｀ replace (Sˢ α) (Sˢ β) Zˢ ]ᵗ)
        (replaceᵗ-S-⇑ˢ α β A))
      (cong
        (λ γ → (⇑ˢ (replaceᵗ α β A)) [ ｀ γ ]ᵗ)
        (replace-S-Z α β)))

sealToTag-∋Sα :
  ∀{Ψ}{Σ : Store Ψ}{α : Seal Ψ} →
  Σ ∋ˢ α ⦂ `★ →
  ((Zˢ , `★) ∷ ⟰ˢ Σ) ∋ˢ Sˢ α ⦂ `★
sealToTag-∋Sα ∋α = S∋ˢ (renameLookupˢ Sˢ ∋α)

sealToTag-Sβ∉ :
  ∀{Ψ}{Σ : Store Ψ}{β : Seal Ψ} →
  β ∉domˢ Σ →
  Sˢ β ∉domˢ ((Zˢ , `★) ∷ ⟰ˢ Σ)
sealToTag-Sβ∉ β∉ = Sˢ∉dom-ν β∉

sealToTag-u↑ :
  ∀{Ψ}{Σ : Store Ψ} →
  Uniqueˢ Σ →
  Uniqueˢ ((Zˢ , `★) ∷ ⟰ˢ Σ)
sealToTag-u↑ uΣ = unique-ν `★ uΣ

sealToTag-fresh↑ :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{A : Ty (suc Δ) Ψ} →
  FreshReachˢ (`∀ A) Σ Σ′ →
  FreshReachˢ (((⇑ˢ A) [ ｀ Zˢ ]ᵗ))
             ((Zˢ , `★) ∷ ⟰ˢ Σ)
             ((Zˢ , `★) ∷ ⟰ˢ Σ′)
sealToTag-fresh↑ = fresh-ν-src

sameDrop-⇒ˡ :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{α β δ : Seal Ψ}{A B : Ty Δ Ψ} →
  SameDropˢ α β δ (A ⇒ B) Σ Σ′ →
  SameDropˢ α β δ A Σ Σ′
sameDrop-⇒ˡ same α≢ h with same α≢ h
... | inj₁ h′ = inj₁ h′
... | inj₂ (γ≡δ , noAB) = inj₂ (γ≡δ , λ rA → noAB (reach-⇒ˡ rA))

sameDrop-⇒ʳ :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{α β δ : Seal Ψ}{A B : Ty Δ Ψ} →
  SameDropˢ α β δ (A ⇒ B) Σ Σ′ →
  SameDropˢ α β δ B Σ Σ′
sameDrop-⇒ʳ same α≢ h with same α≢ h
... | inj₁ h′ = inj₁ h′
... | inj₂ (γ≡δ , noAB) = inj₂ (γ≡δ , λ rB → noAB (reach-⇒ʳ rB))

sameDrop-∀ :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{α β δ : Seal Ψ}{A : Ty (suc Δ) Ψ} →
  SameDropˢ α β δ (`∀ A) Σ Σ′ →
  SameDropˢ α β δ A Σ Σ′
sameDrop-∀ same α≢ h with same α≢ h
... | inj₁ h′ = inj₁ h′
... | inj₂ (γ≡δ , no∀) = inj₂ (γ≡δ , λ rA → no∀ (reach-∀ rA))

sameDrop-seal :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{α β δ γ : Seal Ψ}{A₀ : Ty 0 Ψ} →
  Σ ∋ˢ γ ⦂ A₀ →
  SameDropˢ α β δ (｀ γ) Σ Σ′ →
  SameDropˢ α β δ (wkTy0 {Δ = Δ} A₀) Σ Σ′
sameDrop-seal h same α≢ hγ with same α≢ hγ
... | inj₁ h′ = inj₁ h′
... | inj₂ (γ≡δ , noγ) =
      inj₂ (γ≡δ , λ rA₀ → noγ (reach-seal-payload h rA₀))

sealToTag-same↑ :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}
   {A : Ty (suc Δ) Ψ}
   {α β δ : Seal Ψ} →
  SameDropˢ α β δ (`∀ A) Σ Σ′ →
  SameDropˢ (Sˢ α) (Sˢ β) (Sˢ δ)
            (((⇑ˢ A) [ ｀ Zˢ ]ᵗ))
            ((Zˢ , `★) ∷ ⟰ˢ Σ)
            ((Zˢ , `★) ∷ ⟰ˢ Σ′)
sealToTag-same↑ {α = α} {β = β} same {γ = Zˢ} {A₀ = A₀} neq (Z∋ˢ γ≡Z A₀≡★) =
  inj₁ (Z∋ˢ γ≡Z (trans (cong (replaceᵗ (Sˢ α) (Sˢ β)) A₀≡★) refl))
sealToTag-same↑ same {γ = Zˢ} neq (S∋ˢ h) with Zˢ∉dom-⟰ˢ h
... | ()
sealToTag-same↑ {α = α} {β = β} same {γ = Sˢ γ} {A₀ = A₀} neq (Z∋ˢ () _)
sealToTag-same↑ {α = α} {β = β} same
  {γ = Sˢ γ} {A₀ = A₀} neq (S∋ˢ h)
  with lookup-Sˢ-⟰ˢ′ h
... | B , A₀≡⇑B , hB with same (λ γ≡α → neq (cong Sˢ γ≡α)) hB
...   | inj₁ hB′ =
      let γ≢α : γ ≡ α → ⊥
          γ≢α γ≡α = neq (cong Sˢ γ≡α)
          hS′ = renameLookupˢ Sˢ hB′
          eqTy : replaceᵗ (Sˢ α) (Sˢ β) A₀ ≡ ⇑ˢ (replaceᵗ α β B)
          eqTy = trans
                   (cong (replaceᵗ (Sˢ α) (Sˢ β)) A₀≡⇑B)
                   (replaceᵗ-S-⇑ˢ α β B)
      in
      inj₁ (S∋ˢ (subst (λ T → _ ∋ˢ Sˢ γ ⦂ T) (sym eqTy) hS′))
...   | inj₂ (γ≡δ , noγ) =
      inj₂
        ( cong Sˢ γ≡δ
        , λ rS → noγ (reach-ν-src-S rS))


⊑-★-inv :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{B : Ty Δ Ψ} →
  Δ ∣ Ψ ∣ Σ ⊢ wkTy0 `★ ⊑ B →
  B ≡ `★
⊑-★-inv id⋆ = refl

sealToTag-hit-core :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B : Ty Δ Ψ} →
  (α β δ : Seal Ψ) →
  (∋α : Σ ∋ˢ α ⦂ `★) →
  (β∉Σ′ : β ∉domˢ Σ′) →
  SameDropˢ α β δ A Σ Σ′ →
  Uniqueˢ Σ →
  Δ ∣ Ψ ∣ Σ ⊢ wkTy0 `★ ⊑ B →
  Δ ∣ Ψ ∣ Σ′ ⊢ ｀ β ⊑ replaceᵗ α β B
sealToTag-hit-core α β δ ∋α β∉Σ′ same uΣ p =
  subst
    (λ T → _ ∣ _ ∣ _ ⊢ ｀ β ⊑ replaceᵗ α β T)
    (sym (⊑-★-inv p))
    (_；tag_ (idα β β∉Σ′) (｀ β) {g∉Σ = β∉Σ′})

replace-nohit :
  ∀{Ψ}{α β γ : Seal Ψ} →
  (α ≡ γ → ⊥) →
  replace α β γ ≡ γ
replace-nohit {α = α} {β = β} {γ = γ} α≢γ with seal-≟ᵢ α γ
... | yes eq = ⊥-elim (α≢γ eq)
... | no _ = refl

replace′-no :
  ∀{Ψ}{α γ : Seal Ψ} →
  (α≢γ : α ≡ γ → ⊥) →
  (β : Seal Ψ) →
  replace′ {α = α} {γ = γ} (no α≢γ) β ≡ γ
replace′-no α≢γ β = refl

sealToTag-∉domᴳ-core :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{A G : Ty Δ Ψ} →
  (α β δ : Seal Ψ) →
  (∋α : Σ ∋ˢ α ⦂ `★) →
  (β∉Σ′ : β ∉domˢ Σ′) →
  SameDropˢ α β δ A Σ Σ′ →
  Uniqueˢ Σ →
  FreshReachˢ A Σ Σ′ →
  Δ ∣ Ψ ∣ Σ ⊢ᶜ A ⊑ G →
  (g : Ground G) →
  g ∉domᴳ Σ →
  renameˢ-ground (replace α β) g ∉domᴳ Σ′
sealToTag-∉domᴳ-core {Σ = Σ} {Σ′ = Σ′} α β δ ∋α β∉Σ′ same uΣ freshA p (‵ ι) g∉Σ = tt
sealToTag-∉domᴳ-core {Σ = Σ} {Σ′ = Σ′} α β δ ∋α β∉Σ′ same uΣ freshA p ★⇒★ g∉Σ = tt
sealToTag-∉domᴳ-core {Σ = Σ} {Σ′ = Σ′} α β δ ∋α β∉Σ′ same uΣ freshA p (｀ γ) γ∉Σ with seal-≟ᵢ α γ
... | yes α≡γ =
      ⊥-elim (γ∉Σ (subst (λ δ → Σ ∋ˢ δ ⦂ `★) α≡γ ∋α))
... | no α≢γ =
      subst
        (λ δ → δ ∉domˢ Σ′)
        (sym (replace′-no α≢γ β))
        (freshA (srcˢ (seal-in-src p)) γ∉Σ)

mutual
  sealToTagᶜ-core :
    ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B : Ty Δ Ψ} →
    (α β δ : Seal Ψ) →
    Σ ∋ˢ α ⦂ `★ →
    β ∉domˢ Σ′ →
    SameDropˢ α β δ A Σ Σ′ →
    Uniqueˢ Σ →
    FreshReachˢ A Σ Σ′ →
    Δ ∣ Ψ ∣ Σ ⊢ᶜ A ⊑ B →
    Δ ∣ Ψ ∣ Σ′ ⊢ᶜ replaceᵗ α β A ⊑ replaceᵗ α β B
  sealToTagᶜ-core {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Σ′ = Σ′}
    α β δ ∋α β∉Σ′ same uΣ freshA (idα γ γ∉Σ) with seal-≟ᵢ α γ
  ... | yes α≡γ =
        ⊥-elim (γ∉Σ (subst (λ δ → Σ ∋ˢ δ ⦂ `★) α≡γ ∋α))
  ... | no α≢γ =
        subst
          (λ T → Δ ∣ Ψ ∣ Σ′ ⊢ᶜ T ⊑ T)
          (sym (cong ｀_ (replace′-no α≢γ β)))
          (idα γ (freshA (srcˢ hereˢ) γ∉Σ))
  sealToTagᶜ-core α β δ ∋α β∉Σ′ same uΣ freshA (idX X) = idX X
  sealToTagᶜ-core α β δ ∋α β∉Σ′ same uΣ freshA (idι ι) = idι ι
  sealToTagᶜ-core {A = A ⇒ B} α β δ ∋α β∉Σ′ same uΣ freshAB (p →ᵖ q) =
    sealToTag-core α β δ ∋α β∉Σ′ (sameDrop-⇒ˡ same) uΣ (fresh-⇒ˡ freshAB) p
    →ᵖ
    sealToTag-core α β δ ∋α β∉Σ′ (sameDrop-⇒ʳ same) uΣ (fresh-⇒ʳ freshAB) q
  sealToTagᶜ-core {A = `∀ A} α β δ ∋α β∉Σ′ same uΣ freshA (∀ᵖ p) =
    ∀ᵖ (sealToTag-core α β δ ∋α β∉Σ′ (sameDrop-∀ same) uΣ (fresh-∀ freshA) p)

  sealToTag-core :
    ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B : Ty Δ Ψ} →
    (α β δ : Seal Ψ) →
    Σ ∋ˢ α ⦂ `★ →
    β ∉domˢ Σ′ →
    SameDropˢ α β δ A Σ Σ′ →
    Uniqueˢ Σ →
    FreshReachˢ A Σ Σ′ →
    Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B →
    Δ ∣ Ψ ∣ Σ′ ⊢ replaceᵗ α β A ⊑ replaceᵗ α β B
  sealToTag-core α β δ ∋α β∉Σ′ same uΣ freshA ⌈ g ⌉ =
    ⌈ sealToTagᶜ-core α β δ ∋α β∉Σ′ same uΣ freshA g ⌉
  sealToTag-core α β δ ∋α β∉Σ′ same uΣ freshA id⋆ = id⋆
  sealToTag-core α β δ ∋α β∉Σ′ same uΣ freshA (_；tag_ p g {g∉Σ = g∉Σ}) =
    _；tag_ (sealToTagᶜ-core α β δ ∋α β∉Σ′ same uΣ freshA p)
      (renameˢ-ground (replace α β) g)
      {g∉Σ = sealToTag-∉domᴳ-core α β δ ∋α β∉Σ′ same uΣ freshA p g g∉Σ}
  sealToTag-core {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Σ′ = Σ′} {B = B}
    α β δ ∋α β∉Σ′ same uΣ freshA (seal_；_ {α = γ} {A = A₀} h p) with seal-≟ᵢ α γ
  ... | yes α≡γ =
        let hα : Σ ∋ˢ α ⦂ A₀
            hα = subst (λ δ → Σ ∋ˢ δ ⦂ A₀) (sym α≡γ) h
            A₀≡★ : A₀ ≡ `★
            A₀≡★ = lookup-unique uΣ hα ∋α
            p★ : Δ ∣ Ψ ∣ Σ ⊢ wkTy0 `★ ⊑ B
            p★ = subst (λ T → Δ ∣ Ψ ∣ Σ ⊢ wkTy0 T ⊑ B) A₀≡★ p
        in
        sealToTag-hit-core α β δ ∋α β∉Σ′ same uΣ p★
  ... | no α≢γ with same (λ γ≡α → α≢γ (sym γ≡α)) h
  ...   | inj₁ h′ =
          let p′ : Δ ∣ Ψ ∣ Σ′ ⊢ replaceᵗ α β (wkTy0 A₀) ⊑ replaceᵗ α β B
              p′ = sealToTag-core α β δ ∋α β∉Σ′ (sameDrop-seal h same) uΣ (fresh-seal freshA h) p
              p″ : Δ ∣ Ψ ∣ Σ′ ⊢ wkTy0 (replaceᵗ α β A₀) ⊑ replaceᵗ α β B
              p″ =
                subst
                  (λ T → Δ ∣ Ψ ∣ Σ′ ⊢ T ⊑ replaceᵗ α β B)
                  (renameˢ-wkTy0 (replace α β) A₀)
                  p′
              base : Δ ∣ Ψ ∣ Σ′ ⊢ ｀ γ ⊑ replaceᵗ α β B
              base = seal h′ ； p″
          in
          cong-⊑-≡
            (sym (cong ｀_ (replace′-no α≢γ β)))
            refl
            base
  ...   | inj₂ (γ≡δ , noγ) = ⊥-elim (noγ (srcˢ hereˢ))
  sealToTag-core {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Σ′ = Σ′}
    α β δ ∋α β∉Σ′ same uΣ fresh∀ (ν_ {A = A} {B = B} p) =
      let ∋Sα : ((Zˢ , `★) ∷ ⟰ˢ Σ) ∋ˢ Sˢ α ⦂ `★
          ∋Sα = sealToTag-∋Sα ∋α

          Sβ∉ : Sˢ β ∉domˢ ((Zˢ , `★) ∷ ⟰ˢ Σ′)
          Sβ∉ = sealToTag-Sβ∉ β∉Σ′

          same↑ :
            SameDropˢ (Sˢ α) (Sˢ β) (Sˢ δ)
                      (((⇑ˢ A) [ ｀ Zˢ ]ᵗ))
                      ((Zˢ , `★) ∷ ⟰ˢ Σ)
                      ((Zˢ , `★) ∷ ⟰ˢ Σ′)
          same↑ = sealToTag-same↑ same

          u↑ : Uniqueˢ ((Zˢ , `★) ∷ ⟰ˢ Σ)
          u↑ = sealToTag-u↑ uΣ

          fresh↑ :
            FreshReachˢ (((⇑ˢ A) [ ｀ Zˢ ]ᵗ))
                       ((Zˢ , `★) ∷ ⟰ˢ Σ)
                       ((Zˢ , `★) ∷ ⟰ˢ Σ′)
          fresh↑ = sealToTag-fresh↑ fresh∀

          qraw :
            Δ ∣ suc Ψ ∣ ((Zˢ , `★) ∷ ⟰ˢ Σ′) ⊢
              replaceᵗ (Sˢ α) (Sˢ β) (((⇑ˢ A) [ ｀ Zˢ ]ᵗ)) ⊑
              replaceᵗ (Sˢ α) (Sˢ β) (⇑ˢ B)
          qraw = sealToTag-core (Sˢ α) (Sˢ β) (Sˢ δ) ∋Sα Sβ∉ same↑ u↑ fresh↑ p

          q :
            Δ ∣ suc Ψ ∣ ((Zˢ , `★) ∷ ⟰ˢ Σ′) ⊢
              ((⇑ˢ (replaceᵗ α β A)) [ ｀ Zˢ ]ᵗ) ⊑
              ⇑ˢ (replaceᵗ α β B)
          q =
            cong-⊑-≡
              (replaceᵗ-S-ν-src α β A)
              (replaceᵗ-S-⇑ˢ α β B)
              qraw
      in
      ν q

-- Public transform: replace α with β on the source type only.
-- The caller supplies stability of the target type under replacement.
sealToTagᶜ :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B B′ : Ty Δ Ψ} →
  (α β δ : Seal Ψ) →
  Σ ∋ˢ α ⦂ `★ →
  β ∉domˢ Σ′ →
  SameDropˢ α β δ A Σ Σ′ →
  Uniqueˢ Σ →
  FreshReachˢ A Σ Σ′ →
  replaceᵗ α β B ≡ B′ →
  Δ ∣ Ψ ∣ Σ ⊢ᶜ A ⊑ B →
  Δ ∣ Ψ ∣ Σ′ ⊢ᶜ replaceᵗ α β A ⊑ B′
sealToTagᶜ {Δ = Δ} {Ψ = Ψ} {Σ′ = Σ′} {A = A}
  α β δ ∋α β∉Σ′ same uΣ freshA stableB g =
    subst
      (λ T → Δ ∣ Ψ ∣ Σ′ ⊢ᶜ replaceᵗ α β A ⊑ T)
      stableB
      (sealToTagᶜ-core α β δ ∋α β∉Σ′ same uΣ freshA g)

sealToTag :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B B′ : Ty Δ Ψ} →
  (α β δ : Seal Ψ) →
  Σ ∋ˢ α ⦂ `★ →
  β ∉domˢ Σ′ →
  SameDropˢ α β δ A Σ Σ′ →
  Uniqueˢ Σ →
  FreshReachˢ A Σ Σ′ →
  replaceᵗ α β B ≡ B′ →
  Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B →
  Δ ∣ Ψ ∣ Σ′ ⊢ replaceᵗ α β A ⊑ B′
sealToTag {Δ = Δ} {Ψ = Ψ} {Σ′ = Σ′} {A = A}
  α β δ ∋α β∉Σ′ same uΣ freshA stableB p =
    subst
      (λ T → Δ ∣ Ψ ∣ Σ′ ⊢ replaceᵗ α β A ⊑ T)
      stableB
      (sealToTag-core α β δ ∋α β∉Σ′ same uΣ freshA p)
