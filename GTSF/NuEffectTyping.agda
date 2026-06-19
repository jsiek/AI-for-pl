module NuEffectTyping where

-- File Charter:
--   * Prototype strengthened typing relation for Nu GTSF terms.
--   * Tracks the type variables a term may use in seal/unseal positions of
--     suspended casts.
--   * Distinguishes ordinary source `∀` variables from runtime `ν` variables
--     with a lightweight role context.
--   * Uses effect-decorated types so functions carry the latent argument
--     effect needed by β-substitution, while erasing to ordinary Nu typing.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Binary.Sublist.Propositional
  renaming ([] to []⊆; _∷_ to _∷⊆_; _∷ʳ_ to _∷ʳ⊆_)
  using ()
open import Data.Nat using (_<_; zero; suc; z<s; s<s)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import Ctx
open import Store using (_⊆_; complement)
open import Coercions
open import Primitives
open import NuTerms

------------------------------------------------------------------------
-- Effects and effect-decorated types
------------------------------------------------------------------------

data TyRole : Set where
  ordinary : TyRole
  runtime  : TyRole

RoleCtx : Set
RoleCtx = List TyRole

⌊_⌋ : RoleCtx → TyCtx
⌊ Δ ⌋ = length Δ

infix 4 _∋ᵣ_⦂_
data _∋ᵣ_⦂_ : RoleCtx → TyVar → TyRole → Set where
  Zᵣ :
    ∀ {Δ r} →
    (r ∷ Δ) ∋ᵣ zero ⦂ r

  Sᵣ :
    ∀ {Δ α r s} →
    Δ ∋ᵣ α ⦂ r →
    (s ∷ Δ) ∋ᵣ suc α ⦂ r

role-< :
  ∀ {Δ α r} →
  Δ ∋ᵣ α ⦂ r →
  α < ⌊ Δ ⌋
role-< Zᵣ = z<s
role-< (Sᵣ h) = s<s (role-< h)

Effect : Set
Effect = List TyVar

infix 4 _⊆ᵉ_
_⊆ᵉ_ : Effect → Effect → Set
E ⊆ᵉ F = ∀ {α} → α ∈ E → α ∈ F

WfEffect : RoleCtx → Effect → Set
WfEffect Δ E = ∀ {α} → α ∈ E → Δ ∋ᵣ α ⦂ runtime

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

------------------------------------------------------------------------
-- Effect-decorated stores
------------------------------------------------------------------------

EffStore : Set
EffStore = List (TyVar × EffTy)

eraseStoreᵉ : EffStore → Store
eraseStoreᵉ [] = []
eraseStoreᵉ ((α , A) ∷ Σ) = (α , eraseᵉ A) ∷ eraseStoreᵉ Σ

renameStoreᵉ : Renameᵗ → EffStore → EffStore
renameStoreᵉ ρ [] = []
renameStoreᵉ ρ ((α , A) ∷ Σ) =
  (ρ α , renameᵉ ρ A) ∷ renameStoreᵉ ρ Σ

⟰ᵉ : EffStore → EffStore
⟰ᵉ = renameStoreᵉ suc

eraseStore-renameᵉ :
  ∀ ρ Σ →
  eraseStoreᵉ (renameStoreᵉ ρ Σ) ≡ renameStoreᵗ ρ (eraseStoreᵉ Σ)
eraseStore-renameᵉ ρ [] = refl
eraseStore-renameᵉ ρ ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (erase-renameᵉ ρ A))
    (eraseStore-renameᵉ ρ Σ)

eraseStore-incl :
  ∀ {Π Σ : EffStore} →
  Π ⊆ Σ →
  eraseStoreᵉ Π ⊆ eraseStoreᵉ Σ
eraseStore-incl []⊆ = []⊆
eraseStore-incl ((α , A) ∷ʳ⊆ d) =
  (α , eraseᵉ A) ∷ʳ⊆ eraseStore-incl d
eraseStore-incl (refl ∷⊆ d) = refl ∷⊆ eraseStore-incl d

data WfEffTy : RoleCtx → EffTy → Set where
  wf-eff-var :
    ∀ {Δ α} →
    α < ⌊ Δ ⌋ →
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
    WfEffect (ordinary ∷ Δ) E →
    WfEffTy (ordinary ∷ Δ) A →
    WfEffTy Δ (ty-all E A)

forget-wf-eff :
  ∀ {Δ A} →
  WfEffTy Δ A →
  WfTy ⌊ Δ ⌋ (eraseᵉ A)
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

EffCtxWf : RoleCtx → EffCtx → Set₁
EffCtxWf Δ Ξ =
  ∀ {x A E} → Ξ ∋ x ⦂ A ▷ E → WfEffTy Δ A × WfEffect Δ E

effCtxWf-[] :
  ∀ {Δ} →
  EffCtxWf Δ []
effCtxWf-[] ()

effCtxWf-∷ :
  ∀ {Δ Ξ A E} →
  WfEffTy Δ A →
  WfEffect Δ E →
  EffCtxWf Δ Ξ →
  EffCtxWf Δ ((A , E) ∷ Ξ)
effCtxWf-∷ hA hE hΞ Zᵉ = hA , hE
effCtxWf-∷ hA hE hΞ (Sᵉ h) = hΞ h

------------------------------------------------------------------------
-- Coercion seal-use effects
------------------------------------------------------------------------

data RuntimeTy : RoleCtx → Ty → Set where
  rt-var :
    ∀ {Δ α} →
    Δ ∋ᵣ α ⦂ runtime →
    RuntimeTy Δ (＇ α)

  rt-base :
    ∀ {Δ ι} →
    RuntimeTy Δ (‵ ι)

  rt-star :
    ∀ {Δ} →
    RuntimeTy Δ ★

  rt-fun :
    ∀ {Δ A B} →
    RuntimeTy Δ A →
    RuntimeTy Δ B →
    RuntimeTy Δ (A ⇒ B)

  rt-all :
    ∀ {Δ A} →
    RuntimeTy (ordinary ∷ Δ) A →
    RuntimeTy Δ (`∀ A)

data CoercionRoles : RoleCtx → Coercion → Set where
  -- Ordinary `X` variables are allowed in identity coercion types, but the
  -- dynamic coercion forms below require runtime-only type annotations.
  roles-id :
    ∀ {Δ A} →
    CoercionRoles Δ (id A)

  roles-seq :
    ∀ {Δ c d} →
    CoercionRoles Δ c →
    CoercionRoles Δ d →
    CoercionRoles Δ (c ︔ d)

  roles-fun :
    ∀ {Δ c d} →
    CoercionRoles Δ c →
    CoercionRoles Δ d →
    CoercionRoles Δ (c ↦ d)

  roles-all :
    ∀ {Δ c} →
    CoercionRoles (ordinary ∷ Δ) c →
    CoercionRoles Δ (`∀ c)

  roles-tag :
    ∀ {Δ G} →
    RuntimeTy Δ G →
    CoercionRoles Δ (G !)

  roles-untag :
    ∀ {Δ G} →
    RuntimeTy Δ G →
    CoercionRoles Δ (G ？)

  roles-seal :
    ∀ {Δ A α} →
    RuntimeTy Δ A →
    Δ ∋ᵣ α ⦂ runtime →
    CoercionRoles Δ (seal A α)

  roles-unseal :
    ∀ {Δ A α} →
    RuntimeTy Δ A →
    Δ ∋ᵣ α ⦂ runtime →
    CoercionRoles Δ (unseal α A)

  roles-gen :
    ∀ {Δ A c} →
    RuntimeTy Δ A →
    CoercionRoles (runtime ∷ Δ) c →
    CoercionRoles Δ (gen A c)

  roles-inst :
    ∀ {Δ B c} →
    RuntimeTy Δ B →
    CoercionRoles (runtime ∷ Δ) c →
    CoercionRoles Δ (inst B c)

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

SealSideExact : Coercion → EffStore → Set
SealSideExact c Π =
  ∀ {α A} →
  (α , A) ∈ Π →
  α ∈ sealUsesᶜ c

SealSideEffect : Coercion → EffStore → Effect → Set
SealSideEffect c Π E =
  sealUsesᶜ c ⊆ᵉ E ×
  (∀ {α A} → (α , A) ∈ Π → α ∈ E)

data CastEndpoint : EffStore → Coercion → Effect → EffTy → EffTy → Set where
  end-id :
    ∀ {Π F A T} →
    CastEndpoint Π (id T) F A A

  end-seq :
    ∀ {Π c d F A B C} →
    CastEndpoint Π c F A B →
    CastEndpoint Π d F B C →
    CastEndpoint Π (c ︔ d) F A C

  end-fun :
    ∀ {Π p q F A A′ B B′ E E′} →
    CastEndpoint Π p F A′ A →
    CastEndpoint Π q F B B′ →
    E′ ++ F ⊆ᵉ E →
    CastEndpoint Π (p ↦ q) F (A ⇒[ E ] B) (A′ ⇒[ E′ ] B′)

  end-all :
    ∀ {Π c G F A B E E′} →
    CastEndpoint (⟰ᵉ Π) c G A B →
    drop0ᵉ G ⊆ᵉ F →
    drop0ᵉ E ⊆ᵉ drop0ᵉ E′ →
    CastEndpoint Π (`∀ c) F (ty-all E A) (ty-all E′ B)

  end-tag :
    ∀ {Π F G A} →
    CastEndpoint Π (G !) F A ty-star

  end-untag :
    ∀ {Π F G A} →
    CastEndpoint Π (G ？) F ty-star A

  end-seal :
    ∀ {Π F α A T} →
    (α , A) ∈ Π →
    CastEndpoint Π (seal T α) F A (ty-var α)

  end-unseal :
    ∀ {Π F α A T} →
    (α , A) ∈ Π →
    CastEndpoint Π (unseal α T) F (ty-var α) A

  end-gen :
    ∀ {Π c G F A B E T} →
    CastEndpoint (⟰ᵉ Π) c G (renameᵉ suc A) B →
    drop0ᵉ G ⊆ᵉ F →
    CastEndpoint Π (gen T c) F A (ty-all E B)

  end-inst :
    ∀ {Π c G F A B E T} →
    CastEndpoint ((zero , ty-star) ∷ ⟰ᵉ Π) c G A (renameᵉ suc B) →
    drop0ᵉ G ⊆ᵉ F →
    CastEndpoint Π (inst T c) F (ty-all E A) B

------------------------------------------------------------------------
-- Effect typing
------------------------------------------------------------------------

infix 4 _∣_∣_⊢_⦂_▷_

data _∣_∣_⊢_⦂_▷_
    (Δ : RoleCtx) (Σ : EffStore) (Ξ : EffCtx) :
    Term → EffTy → Effect → Set₁ where

  eff-var : ∀ {x A E}
     → Ξ ∋ x ⦂ A ▷ E
      ----------------------
     → Δ ∣ Σ ∣ Ξ ⊢ (` x) ⦂ A ▷ E

  eff-lam : ∀ {M A B Earg Ebody}
     → WfEffTy Δ A
     → WfEffect Δ Earg
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
     → ordinary ∷ Δ ∣ ⟰ᵉ Σ ∣ renameCtxᵉ suc Ξ ⊢ M ⦂ A ▷ E
      ----------------------------
     → Δ ∣ Σ ∣ Ξ ⊢ (Λ M) ⦂ (ty-all E A) ▷ drop0ᵉ E

  eff-tyapp : ∀ {L B α E Ebody}
     → Δ ∣ Σ ∣ Ξ ⊢ L ⦂ (ty-all Ebody B) ▷ E
     → Δ ∋ᵣ α ⦂ runtime
     → α ∉ E
      ----------------------------
     → Δ ∣ Σ ∣ Ξ ⊢ (L • α) ⦂ B [ α ]ᵉ ▷ E ++ drop0ᵉ Ebody

  eff-nu : ∀ {N A Aᵉ B E}
     → WfEffTy Δ Aᵉ
     → eraseᵉ Aᵉ ≡ A
     → WfEffTy Δ B
     → runtime ∷ Δ ∣ (zero , renameᵉ suc Aᵉ) ∷ ⟰ᵉ Σ
         ∣ renameCtxᵉ suc Ξ
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

  eff-cast : ∀ {M A B c Π E F}
      → (d : Π ⊆ Σ)
      → ⌊ Δ ⌋ ∣ complement (eraseStore-incl d) ∣ eraseStoreᵉ Π
          ⊢ c ∶ eraseᵉ A =⇒ eraseᵉ B
      → CoercionRoles Δ c
      → SealSideEffect c Π F
      → WfEffect Δ F
      → WfEffTy Δ B
      → CastEndpoint Π c F A B
      → Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ E
      -------------------------
      → Δ ∣ Σ ∣ Ξ ⊢ M ⟨ c ⟩ ⦂ B ▷ E ++ F

  eff-blame : ∀ {A}
      → WfEffTy Δ A
      ----------------------------
      → Δ ∣ Σ ∣ Ξ ⊢ blame ⦂ A ▷ []

  eff-sub : ∀ {M A E F}
      → Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ E
      → E ⊆ᵉ F
      → WfEffect Δ F
      ----------------------------
      → Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ F

forget-effect :
  ∀ {Δ Σ Ξ M A E} →
  Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ E →
  ⌊ Δ ⌋ ∣ eraseStoreᵉ Σ ∣ eraseCtxᵉ Ξ ⊢ M ⦂ eraseᵉ A
forget-effect (eff-var hΞ) = ⊢` (lookup-eraseᵉ hΞ)
forget-effect (eff-lam hA hE hM) =
  ⊢ƛ (forget-wf-eff hA) (forget-effect hM)
forget-effect (eff-app hL hM EM⊆Earg) =
  ⊢· (forget-effect hL) (forget-effect hM)
forget-effect {Δ = Δ} {Σ = Σ} {Ξ = Ξ}
    (eff-tylam {M = M} {A = A} vM hM) =
  ⊢Λ vM
    (subst
      (λ Γ → suc ⌊ Δ ⌋ ∣ ⟰ᵗ (eraseStoreᵉ Σ) ∣ Γ
        ⊢ M ⦂ eraseᵉ A)
      (eraseCtx-renameᵉ suc Ξ)
      (subst
        (λ Σ′ → suc ⌊ Δ ⌋ ∣ Σ′ ∣ eraseCtxᵉ (renameCtxᵉ suc Ξ)
          ⊢ M ⦂ eraseᵉ A)
        (eraseStore-renameᵉ suc Σ)
        (forget-effect hM)))
forget-effect (eff-tyapp {B = B} {α = α} hL hα α∉E) =
  subst
    (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
    (sym (erase-openᵉ B α))
    (⊢• (forget-effect hL) (role-< hα))
forget-effect {Δ = Δ} {Σ = Σ} {Ξ = Ξ}
    (eff-nu {N = N} {A = A} {Aᵉ = Aᵉ} {B = B} hAᵉ eqA hB hN) =
  ⊢ν hA
    (subst
      (λ T → suc ⌊ Δ ⌋ ∣ (zero , ⇑ᵗ A) ∷ ⟰ᵗ (eraseStoreᵉ Σ)
        ∣ ⤊ᵗ (eraseCtxᵉ Ξ) ⊢ N ⦂ T)
      (erase-renameᵉ suc B)
      (subst
        (λ Γ → suc ⌊ Δ ⌋ ∣ (zero , ⇑ᵗ A) ∷ ⟰ᵗ (eraseStoreᵉ Σ)
          ∣ Γ ⊢ N ⦂ eraseᵉ (renameᵉ suc B))
        (eraseCtx-renameᵉ suc Ξ)
        (subst
          (λ Σ′ → suc ⌊ Δ ⌋ ∣ Σ′ ∣ eraseCtxᵉ (renameCtxᵉ suc Ξ)
            ⊢ N ⦂ eraseᵉ (renameᵉ suc B))
          store-eq
          (forget-effect hN))))
  where
    hA : WfTy ⌊ Δ ⌋ A
    hA = subst (WfTy ⌊ Δ ⌋) eqA (forget-wf-eff hAᵉ)

    store-eq :
      eraseStoreᵉ ((zero , renameᵉ suc Aᵉ) ∷ ⟰ᵉ Σ) ≡
      (zero , ⇑ᵗ A) ∷ ⟰ᵗ (eraseStoreᵉ Σ)
    store-eq =
      cong₂ _∷_
        (cong₂ _,_ refl
          (trans (erase-renameᵉ suc Aᵉ) (cong ⇑ᵗ eqA)))
        (eraseStore-renameᵉ suc Σ)
forget-effect (eff-const κ) =
  subst
    (λ T → _ ∣ _ ∣ _ ⊢ ($ κ) ⦂ T)
    (sym (erase-plainᵉ (constTy κ)))
    (⊢$ κ)
forget-effect (eff-prim hL op hM) =
  ⊢⊕ (forget-effect hL) op (forget-effect hM)
forget-effect (eff-cast d c⊢ roles side hS hB endpoint hM) =
  ⊢⟨⟩ (eraseStore-incl d) c⊢ (forget-effect hM)
forget-effect (eff-blame hA) = ⊢blame (forget-wf-eff hA)
forget-effect (eff-sub hM E⊆F hF) = forget-effect hM
