module NuEffectTyping where

-- File Charter:
--   * Prototype strengthened typing relation for Nu GTSF terms.
--   * Tracks the type variables a term may use in seal/unseal positions of
--     suspended casts.
--   * Uses effect-decorated types so functions carry the latent argument
--     effect needed by β-substitution, while erasing to ordinary Nu typing.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Nat using (_<_; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym)

open import Types
open import Ctx
open import Store using (_⊆_; complement)
open import Coercions
open import Primitives
open import NuTerms

------------------------------------------------------------------------
-- Effects and effect-decorated types
------------------------------------------------------------------------

Effect : Set
Effect = List TyVar

infix 4 _⊆ᵉ_
_⊆ᵉ_ : Effect → Effect → Set
E ⊆ᵉ F = ∀ {α} → α ∈ E → α ∈ F

WfEffect : TyCtx → Effect → Set
WfEffect Δ E = ∀ {α} → α ∈ E → α < Δ

renameᴱ : Renameᵗ → Effect → Effect
renameᴱ ρ [] = []
renameᴱ ρ (α ∷ E) = ρ α ∷ renameᴱ ρ E

drop0ᵉ : Effect → Effect
drop0ᵉ [] = []
drop0ᵉ (zero ∷ E) = drop0ᵉ E
drop0ᵉ (suc α ∷ E) = α ∷ drop0ᵉ E

openᴱ : Effect → TyVar → Effect
openᴱ E α = renameᴱ (singleRenameᵗ α) E

data EffTy : Set where
  ty-var  : TyVar → EffTy
  ty-base : Base → EffTy
  ty-star : EffTy
  _⇒[_]_  : EffTy → Effect → EffTy → EffTy
  ty-all  : Effect → EffTy → EffTy

infixr 7 _⇒[_]_

eraseᵉ : EffTy → Ty
eraseᵉ (ty-var α) = ＇ α
eraseᵉ (ty-base ι) = ‵ ι
eraseᵉ ty-star = ★
eraseᵉ (A ⇒[ E ] B) = eraseᵉ A ⇒ eraseᵉ B
eraseᵉ (ty-all E A) = `∀ (eraseᵉ A)

plainᵉ : Ty → EffTy
plainᵉ (＇ α) = ty-var α
plainᵉ (‵ ι) = ty-base ι
plainᵉ ★ = ty-star
plainᵉ (A ⇒ B) = plainᵉ A ⇒[ [] ] plainᵉ B
plainᵉ (`∀ A) = ty-all [] (plainᵉ A)

erase-plainᵉ :
  ∀ A →
  eraseᵉ (plainᵉ A) ≡ A
erase-plainᵉ (＇ α) = refl
erase-plainᵉ (‵ ι) = refl
erase-plainᵉ ★ = refl
erase-plainᵉ (A ⇒ B) =
  cong₂ _⇒_ (erase-plainᵉ A) (erase-plainᵉ B)
erase-plainᵉ (`∀ A) =
  cong `∀ (erase-plainᵉ A)

renameᵉ : Renameᵗ → EffTy → EffTy
renameᵉ ρ (ty-var α) = ty-var (ρ α)
renameᵉ ρ (ty-base ι) = ty-base ι
renameᵉ ρ ty-star = ty-star
renameᵉ ρ (A ⇒[ E ] B) = renameᵉ ρ A ⇒[ renameᴱ ρ E ] renameᵉ ρ B
renameᵉ ρ (ty-all E A) =
  ty-all (renameᴱ (extᵗ ρ) E) (renameᵉ (extᵗ ρ) A)

_[_]ᵉ : EffTy → TyVar → EffTy
A [ α ]ᵉ = renameᵉ (singleRenameᵗ α) A

erase-renameᵉ :
  ∀ ρ A →
  eraseᵉ (renameᵉ ρ A) ≡ renameᵗ ρ (eraseᵉ A)
erase-renameᵉ ρ (ty-var α) = refl
erase-renameᵉ ρ (ty-base ι) = refl
erase-renameᵉ ρ ty-star = refl
erase-renameᵉ ρ (A ⇒[ E ] B) =
  cong₂ _⇒_ (erase-renameᵉ ρ A) (erase-renameᵉ ρ B)
erase-renameᵉ ρ (ty-all E A) =
  cong `∀ (erase-renameᵉ (extᵗ ρ) A)

erase-openᵉ :
  ∀ A α →
  eraseᵉ (A [ α ]ᵉ) ≡ eraseᵉ A [ α ]ᴿ
erase-openᵉ A α = erase-renameᵉ (singleRenameᵗ α) A

data WfEffTy : TyCtx → EffTy → Set where
  wf-eff-var :
    ∀ {Δ α} →
    α < Δ →
    WfEffTy Δ (ty-var α)

  wf-eff-base :
    ∀ {Δ ι} →
    WfEffTy Δ (ty-base ι)

  wf-eff-star :
    ∀ {Δ} →
    WfEffTy Δ ty-star

  wf-eff-fun :
    ∀ {Δ A E B} →
    WfEffTy Δ A →
    WfEffect Δ E →
    WfEffTy Δ B →
    WfEffTy Δ (A ⇒[ E ] B)

  wf-eff-all :
    ∀ {Δ E A} →
    WfEffect (suc Δ) E →
    WfEffTy (suc Δ) A →
    WfEffTy Δ (ty-all E A)

forget-wf-eff :
  ∀ {Δ A} →
  WfEffTy Δ A →
  WfTy Δ (eraseᵉ A)
forget-wf-eff (wf-eff-var α<Δ) = wfVar α<Δ
forget-wf-eff wf-eff-base = wfBase
forget-wf-eff wf-eff-star = wf★
forget-wf-eff (wf-eff-fun hA wfE hB) =
  wf⇒ (forget-wf-eff hA) (forget-wf-eff hB)
forget-wf-eff (wf-eff-all wfE hA) = wf∀ (forget-wf-eff hA)

------------------------------------------------------------------------
-- Effect contexts
------------------------------------------------------------------------

EffCtx : Set
EffCtx = List (EffTy × Effect)

eraseCtxᵉ : EffCtx → Ctx
eraseCtxᵉ [] = []
eraseCtxᵉ ((A , E) ∷ Ξ) = eraseᵉ A ∷ eraseCtxᵉ Ξ

renameCtxᵉ : Renameᵗ → EffCtx → EffCtx
renameCtxᵉ ρ [] = []
renameCtxᵉ ρ ((A , E) ∷ Ξ) =
  (renameᵉ ρ A , renameᴱ ρ E) ∷ renameCtxᵉ ρ Ξ

eraseCtx-renameᵉ :
  ∀ ρ Ξ →
  eraseCtxᵉ (renameCtxᵉ ρ Ξ) ≡ map (renameᵗ ρ) (eraseCtxᵉ Ξ)
eraseCtx-renameᵉ ρ [] = refl
eraseCtx-renameᵉ ρ ((A , E) ∷ Ξ) =
  cong₂ _∷_ (erase-renameᵉ ρ A) (eraseCtx-renameᵉ ρ Ξ)

infix 4 _∋_⦂_▷_
data _∋_⦂_▷_ : EffCtx → Var → EffTy → Effect → Set₁ where
  Zᵉ :
    ∀ {Ξ A E} →
    ((A , E) ∷ Ξ) ∋ zero ⦂ A ▷ E

  Sᵉ :
    ∀ {Ξ x A B E F} →
    Ξ ∋ x ⦂ A ▷ E →
    ((B , F) ∷ Ξ) ∋ suc x ⦂ A ▷ E

lookup-eraseᵉ :
  ∀ {Ξ x A E} →
  Ξ ∋ x ⦂ A ▷ E →
  eraseCtxᵉ Ξ ∋ x ⦂ eraseᵉ A
lookup-eraseᵉ Zᵉ = Z
lookup-eraseᵉ (Sᵉ h) = S (lookup-eraseᵉ h)

------------------------------------------------------------------------
-- Coercion seal-use effects
------------------------------------------------------------------------

sealUsesᶜ : Coercion → Effect
sealUsesᶜ (id A) = []
sealUsesᶜ (c ︔ d) = sealUsesᶜ c ++ sealUsesᶜ d
sealUsesᶜ (c ↦ d) = sealUsesᶜ c ++ sealUsesᶜ d
sealUsesᶜ (`∀ c) = drop0ᵉ (sealUsesᶜ c)
sealUsesᶜ (G !) = []
sealUsesᶜ (G ？) = []
sealUsesᶜ (seal A α) = α ∷ []
sealUsesᶜ (unseal α A) = α ∷ []
sealUsesᶜ (gen A c) = drop0ᵉ (sealUsesᶜ c)
sealUsesᶜ (inst B c) = drop0ᵉ (sealUsesᶜ c)

SealSideExact : Coercion → Store → Set
SealSideExact c Π =
  ∀ {α A} →
  (α , A) ∈ Π →
  α ∈ sealUsesᶜ c

------------------------------------------------------------------------
-- Effect typing
------------------------------------------------------------------------

infix 4 _∣_∣_⊢_⦂_▷_

data _∣_∣_⊢_⦂_▷_
    (Δ : TyCtx) (Σ : Store) (Ξ : EffCtx) :
    Term → EffTy → Effect → Set₁ where

  eff-var : ∀ {x A E}
     → Ξ ∋ x ⦂ A ▷ E
      ----------------------
     → Δ ∣ Σ ∣ Ξ ⊢ (` x) ⦂ A ▷ E

  eff-lam : ∀ {M A B Earg Ebody}
     → WfEffTy Δ A
     → Δ ∣ Σ ∣ ((A , Earg) ∷ Ξ) ⊢ M ⦂ B ▷ Ebody
      ----------------------------
     → Δ ∣ Σ ∣ Ξ ⊢ (ƛ M) ⦂ (A ⇒[ Earg ] B) ▷ Ebody

  eff-app : ∀ {L M A B Earg EL EM}
     → Δ ∣ Σ ∣ Ξ ⊢ L ⦂ (A ⇒[ Earg ] B) ▷ EL
     → Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ EM
     → EM ⊆ᵉ Earg
      -------------------------
     → Δ ∣ Σ ∣ Ξ ⊢ (L · M) ⦂ B ▷ EL ++ EM

  eff-tylam : ∀ {M A E}
     → Value M
     → suc Δ ∣ ⟰ᵗ Σ ∣ renameCtxᵉ suc Ξ ⊢ M ⦂ A ▷ E
      ----------------------------
     → Δ ∣ Σ ∣ Ξ ⊢ (Λ M) ⦂ (ty-all E A) ▷ drop0ᵉ E

  eff-tyapp : ∀ {L B α E Ebody}
     → Δ ∣ Σ ∣ Ξ ⊢ L ⦂ (ty-all Ebody B) ▷ E
     → α < Δ
     → α ∉ E
     → occurs (suc α) (eraseᵉ B) ≡ false
      ----------------------------
     → Δ ∣ Σ ∣ Ξ ⊢ (L • α) ⦂ B [ α ]ᵉ ▷ E ++ openᴱ Ebody α

  eff-nu : ∀ {N A B E}
     → WfTy Δ A
     → suc Δ ∣ (0 , ⇑ᵗ A) ∷ ⟰ᵗ Σ ∣ renameCtxᵉ suc Ξ
         ⊢ N ⦂ renameᵉ suc B ▷ E
      --------------------------------------------
     → Δ ∣ Σ ∣ Ξ ⊢ (ν A N) ⦂ B ▷ drop0ᵉ E

  eff-const : ∀ (κ : Const)
      -------------------------------
     → Δ ∣ Σ ∣ Ξ ⊢ ($ κ) ⦂ plainᵉ (constTy κ) ▷ []

  eff-prim : ∀ {L M EL EM}
     → Δ ∣ Σ ∣ Ξ ⊢ L ⦂ ty-base `ℕ ▷ EL
     → (op : Prim)
     → Δ ∣ Σ ∣ Ξ ⊢ M ⦂ ty-base `ℕ ▷ EM
      -----------------------------------
     → Δ ∣ Σ ∣ Ξ ⊢ (L ⊕[ op ] M) ⦂ ty-base `ℕ ▷ EL ++ EM

  eff-cast : ∀ {M A B c Π E}
      → (d : Π ⊆ Σ)
      → Δ ∣ complement d ∣ Π ⊢ c ∶ eraseᵉ A =⇒ eraseᵉ B
      → SealSideExact c Π
      → Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ E
      -------------------------
      → Δ ∣ Σ ∣ Ξ ⊢ M ⟨ c ⟩ ⦂ B ▷ E ++ sealUsesᶜ c

  eff-blame : ∀ {A}
      → WfEffTy Δ A
      ----------------------------
      → Δ ∣ Σ ∣ Ξ ⊢ blame ⦂ A ▷ []

  eff-sub : ∀ {M A E F}
      → Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ E
      → E ⊆ᵉ F
      ----------------------------
      → Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ F

forget-effect :
  ∀ {Δ Σ Ξ M A E} →
  Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ E →
  Δ ∣ Σ ∣ eraseCtxᵉ Ξ ⊢ M ⦂ eraseᵉ A
forget-effect (eff-var hΞ) = ⊢` (lookup-eraseᵉ hΞ)
forget-effect (eff-lam hA hM) = ⊢ƛ (forget-wf-eff hA) (forget-effect hM)
forget-effect (eff-app hL hM EM⊆Earg) =
  ⊢· (forget-effect hL) (forget-effect hM)
forget-effect {Ξ = Ξ} (eff-tylam {M = M} {A = A} vM hM) =
  ⊢Λ vM
    (subst
      (λ Γ → _ ∣ _ ∣ Γ ⊢ M ⦂ eraseᵉ A)
      (eraseCtx-renameᵉ suc Ξ)
      (forget-effect hM))
forget-effect (eff-tyapp {B = B} {α = α} hL α<Δ α∉E noαB) =
  subst
    (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
    (sym (erase-openᵉ B α))
    (⊢• (forget-effect hL) α<Δ)
forget-effect {Ξ = Ξ} (eff-nu {N = N} {A = A} {B = B} hA hN) =
  ⊢ν hA
    (subst
      (λ T → _ ∣ _ ∣ ⤊ᵗ (eraseCtxᵉ Ξ) ⊢ N ⦂ T)
      (erase-renameᵉ suc B)
      (subst
        (λ Γ → _ ∣ _ ∣ Γ ⊢ N ⦂ eraseᵉ (renameᵉ suc B))
        (eraseCtx-renameᵉ suc Ξ)
        (forget-effect hN)))
forget-effect (eff-const κ) =
  subst
    (λ T → _ ∣ _ ∣ _ ⊢ ($ κ) ⦂ T)
    (sym (erase-plainᵉ (constTy κ)))
    (⊢$ κ)
forget-effect (eff-prim hL op hM) =
  ⊢⊕ (forget-effect hL) op (forget-effect hM)
forget-effect (eff-cast d c⊢ exact hM) = ⊢⟨⟩ d c⊢ (forget-effect hM)
forget-effect (eff-blame hA) = ⊢blame (forget-wf-eff hA)
forget-effect (eff-sub hM E⊆F) = forget-effect hM
