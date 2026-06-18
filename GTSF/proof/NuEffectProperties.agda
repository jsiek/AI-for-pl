module proof.NuEffectProperties where

-- File Charter:
--   * Proof-only metatheory for the prototype Nu effect typing judgment.
--   * Starts with structural lemmas that are independent of the remaining
--     store-split exactness problem: subeffecting and term-variable renaming.
--   * Full preservation belongs here once the type-renaming and substitution
--     lemmas for the effect judgment are complete.

open import Data.List using ([]; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (_≤_; zero; suc; z<s; s<s; s≤s)
open import Data.Nat.Properties using (<-≤-trans; suc-injective)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; subst; sym; trans)

open import Types
open import Store
  using (StoreIncl; StoreIncl-cons; StoreIncl-refl; _⊆_; ⊆-trans)
open import Coercions
open import NuTerms
open import NuEffectTyping
open import proof.CoercionProperties
  using
    ( coercion-weaken
    ; coercion-renameᵗ
    ; complement-incl
    ; complement-rename
    ; renameᶜ-preserves-Inert
    )
open import proof.NuStoreProperties using (renameStoreᵗ-incl)
open import proof.NuTermProperties
  using (renameˣᵐ-preserves-Value; renameᵗᵐ-preserves-Value)
open import proof.TypeProperties
  using
    ( TyRenameWf
    ; TyRenameWf-ext
    ; TyRenameWf-suc
    ; WfTy-weakenᵗ
    ; occurs-raise
    ; raise-ext
    ; raiseVarFrom-injective
    ; rename-cong
    ; renameᵗ-compose
    ; renameᵗ-preserves-WfTy
    )

------------------------------------------------------------------------
-- Subeffecting
------------------------------------------------------------------------

⊆ᵉ-refl :
  ∀ {E} →
  E ⊆ᵉ E
⊆ᵉ-refl α∈E = α∈E

⊆ᵉ-trans :
  ∀ {E F G} →
  E ⊆ᵉ F →
  F ⊆ᵉ G →
  E ⊆ᵉ G
⊆ᵉ-trans E⊆F F⊆G α∈E = F⊆G (E⊆F α∈E)

∈-++ˡ :
  ∀ {E F : Effect} {α : TyVar} →
  α ∈ E →
  α ∈ E ++ F
∈-++ˡ (here refl) = here refl
∈-++ˡ (there α∈E) = there (∈-++ˡ α∈E)

∈-++ʳ :
  ∀ (E : Effect) {F : Effect} {α : TyVar} →
  α ∈ F →
  α ∈ E ++ F
∈-++ʳ [] α∈F = α∈F
∈-++ʳ (_ ∷ E) α∈F = there (∈-++ʳ E α∈F)

⊆ᵉ-++ˡ :
  ∀ {E F : Effect} →
  E ⊆ᵉ E ++ F
⊆ᵉ-++ˡ = ∈-++ˡ

⊆ᵉ-++ʳ :
  ∀ (E : Effect) {F : Effect} →
  F ⊆ᵉ E ++ F
⊆ᵉ-++ʳ E = ∈-++ʳ E

∈-renameᴱ :
  ∀ ρ {E α} →
  α ∈ E →
  ρ α ∈ renameᴱ ρ E
∈-renameᴱ ρ (here refl) = here refl
∈-renameᴱ ρ (there α∈E) = there (∈-renameᴱ ρ α∈E)

renameᴱ-cong :
  ∀ {ρ τ} →
  (∀ α → ρ α ≡ τ α) →
  ∀ E →
  renameᴱ ρ E ≡ renameᴱ τ E
renameᴱ-cong eq [] = refl
renameᴱ-cong eq (α ∷ E) =
  cong₂ _∷_ (eq α) (renameᴱ-cong eq E)

renameᴱ-compose :
  ∀ ρ τ E →
  renameᴱ τ (renameᴱ ρ E) ≡ renameᴱ (λ α → τ (ρ α)) E
renameᴱ-compose ρ τ [] = refl
renameᴱ-compose ρ τ (α ∷ E) =
  cong₂ _∷_ refl (renameᴱ-compose ρ τ E)

renameᴱ-++ :
  ∀ ρ E F →
  renameᴱ ρ (E ++ F) ≡ renameᴱ ρ E ++ renameᴱ ρ F
renameᴱ-++ ρ [] F = refl
renameᴱ-++ ρ (α ∷ E) F =
  cong (_∷_ (ρ α)) (renameᴱ-++ ρ E F)

drop0ᵉ-rename :
  ∀ ρ E →
  drop0ᵉ (renameᴱ (extᵗ ρ) E) ≡ renameᴱ ρ (drop0ᵉ E)
drop0ᵉ-rename ρ [] = refl
drop0ᵉ-rename ρ (zero ∷ E) = drop0ᵉ-rename ρ E
drop0ᵉ-rename ρ (suc α ∷ E) =
  cong (_∷_ (ρ α)) (drop0ᵉ-rename ρ E)

sealUsesᶜ-rename :
  ∀ ρ c →
  sealUsesᶜ (renameᶜ ρ c) ≡ renameᴱ ρ (sealUsesᶜ c)
sealUsesᶜ-rename ρ (id A) = refl
sealUsesᶜ-rename ρ (c ︔ d)
  rewrite sealUsesᶜ-rename ρ c
        | sealUsesᶜ-rename ρ d
        | renameᴱ-++ ρ (sealUsesᶜ c) (sealUsesᶜ d) = refl
sealUsesᶜ-rename ρ (c ↦ d)
  rewrite sealUsesᶜ-rename ρ c
        | sealUsesᶜ-rename ρ d
        | renameᴱ-++ ρ (sealUsesᶜ c) (sealUsesᶜ d) = refl
sealUsesᶜ-rename ρ (`∀ c)
  rewrite sealUsesᶜ-rename (extᵗ ρ) c =
  drop0ᵉ-rename ρ (sealUsesᶜ c)
sealUsesᶜ-rename ρ (G !) = refl
sealUsesᶜ-rename ρ (G ？) = refl
sealUsesᶜ-rename ρ (seal A α) = refl
sealUsesᶜ-rename ρ (unseal α A) = refl
sealUsesᶜ-rename ρ (gen A c)
  rewrite sealUsesᶜ-rename (extᵗ ρ) c =
  drop0ᵉ-rename ρ (sealUsesᶜ c)
sealUsesᶜ-rename ρ (inst B c)
  rewrite sealUsesᶜ-rename (extᵗ ρ) c =
  drop0ᵉ-rename ρ (sealUsesᶜ c)

SealSideExact-rename-raise :
  ∀ k {c Π} →
  SealSideExact c Π →
  SealSideExact
    (renameᶜ (raiseVarFrom k) c)
    (renameStoreᵗ (raiseVarFrom k) Π)
SealSideExact-rename-raise k {c = c} {Π = []} exact ()
SealSideExact-rename-raise k {c = c} {Π = (α , A) ∷ Π} exact
    (here refl) =
  subst
    (λ E → raiseVarFrom k α ∈ E)
    (sym (sealUsesᶜ-rename (raiseVarFrom k) c))
    (∈-renameᴱ (raiseVarFrom k) (exact (here refl)))
SealSideExact-rename-raise k {c = c} {Π = (β , B) ∷ Π} exact
    (there h) =
  SealSideExact-rename-raise k
    {c = c}
    {Π = Π}
    (λ β∈Π → exact (there β∈Π))
    h

renameᴱ-open-suc :
  ∀ E α →
  renameᴱ suc (openᴱ E α) ≡
  openᴱ (renameᴱ (extᵗ suc) E) (suc α)
renameᴱ-open-suc E α =
  trans
    (renameᴱ-compose (singleRenameᵗ α) suc E)
    (trans
      (renameᴱ-cong env-eq E)
      (sym (renameᴱ-compose (extᵗ suc) (singleRenameᵗ (suc α)) E)))
  where
    env-eq :
      ∀ β →
      suc (singleRenameᵗ α β) ≡
      singleRenameᵗ (suc α) (extᵗ suc β)
    env-eq zero = refl
    env-eq (suc β) = refl

renameᴱ-open-raise :
  ∀ k E α →
  renameᴱ (raiseVarFrom k) (openᴱ E α) ≡
  openᴱ (renameᴱ (extᵗ (raiseVarFrom k)) E) (raiseVarFrom k α)
renameᴱ-open-raise k E α =
  trans
    (renameᴱ-compose (singleRenameᵗ α) (raiseVarFrom k) E)
    (trans
      (renameᴱ-cong env-eq E)
      (sym
        (renameᴱ-compose
          (extᵗ (raiseVarFrom k))
          (singleRenameᵗ (raiseVarFrom k α))
          E)))
  where
    env-eq :
      ∀ β →
      raiseVarFrom k (singleRenameᵗ α β) ≡
      singleRenameᵗ (raiseVarFrom k α) (extᵗ (raiseVarFrom k) β)
    env-eq zero = refl
    env-eq (suc β) = refl

renameᴱ-mono :
  ∀ ρ {E F} →
  E ⊆ᵉ F →
  renameᴱ ρ E ⊆ᵉ renameᴱ ρ F
renameᴱ-mono ρ {E = []} E⊆F ()
renameᴱ-mono ρ {E = α ∷ E} E⊆F (here refl) =
  ∈-renameᴱ ρ (E⊆F (here refl))
renameᴱ-mono ρ {E = α ∷ E} E⊆F (there β∈E) =
  renameᴱ-mono ρ (λ γ∈E → E⊆F (there γ∈E)) β∈E

∈-renameᴱ-suc-inv :
  ∀ {E α} →
  suc α ∈ renameᴱ suc E →
  α ∈ E
∈-renameᴱ-suc-inv {E = []} ()
∈-renameᴱ-suc-inv {E = β ∷ E} (here eq) =
  here (suc-injective eq)
∈-renameᴱ-suc-inv {E = β ∷ E} (there α∈E) =
  there (∈-renameᴱ-suc-inv α∈E)

∉-renameᴱ-suc :
  ∀ {E α} →
  α ∉ E →
  suc α ∉ renameᴱ suc E
∉-renameᴱ-suc α∉E sucα∈ =
  α∉E (∈-renameᴱ-suc-inv sucα∈)

WfEffect-suc :
  ∀ {Δ E} →
  WfEffect Δ E →
  WfEffect (suc Δ) (renameᴱ suc E)
WfEffect-suc {E = []} wfE ()
WfEffect-suc {E = α ∷ E} wfE (here refl) = s<s (wfE (here refl))
WfEffect-suc {E = α ∷ E} wfE (there β∈) =
  WfEffect-suc (λ γ∈ → wfE (there γ∈)) β∈

WfEffect-rename :
  ∀ {Δ Δ′ E ρ} →
  TyRenameWf Δ Δ′ ρ →
  WfEffect Δ E →
  WfEffect Δ′ (renameᴱ ρ E)
WfEffect-rename {E = []} hρ wfE ()
WfEffect-rename {E = α ∷ E} hρ wfE (here refl) =
  hρ (wfE (here refl))
WfEffect-rename {E = α ∷ E} hρ wfE (there β∈) =
  WfEffect-rename hρ (λ γ∈ → wfE (there γ∈)) β∈

WfEffTy-rename :
  ∀ {Δ Δ′ A ρ} →
  TyRenameWf Δ Δ′ ρ →
  WfEffTy Δ A →
  WfEffTy Δ′ (renameᵉ ρ A)
WfEffTy-rename hρ (wf-eff-var α<Δ) = wf-eff-var (hρ α<Δ)
WfEffTy-rename hρ wf-eff-base = wf-eff-base
WfEffTy-rename hρ wf-eff-star = wf-eff-star
WfEffTy-rename hρ (wf-eff-fun hA wfE hB) =
  wf-eff-fun
    (WfEffTy-rename hρ hA)
    (WfEffect-rename hρ wfE)
    (WfEffTy-rename hρ hB)
WfEffTy-rename hρ (wf-eff-all wfE hA) =
  wf-eff-all
    (WfEffect-rename (TyRenameWf-ext hρ) wfE)
    (WfEffTy-rename (TyRenameWf-ext hρ) hA)

WfEffTy-suc :
  ∀ {Δ A} →
  WfEffTy Δ A →
  WfEffTy (suc Δ) (renameᵉ suc A)
WfEffTy-suc = WfEffTy-rename TyRenameWf-suc

TyRenameWf-raise :
  ∀ k {Δ} →
  k ≤ Δ →
  TyRenameWf Δ (suc Δ) (raiseVarFrom k)
TyRenameWf-raise zero k≤Δ X<Δ = s<s X<Δ
TyRenameWf-raise (suc k) (s≤s k≤Δ) {zero} z<s = z<s
TyRenameWf-raise (suc k) (s≤s k≤Δ) {suc X} (s<s X<Δ) =
  s<s (TyRenameWf-raise k k≤Δ X<Δ)

WfEffect-weaken :
  ∀ {Δ Δ′ E} →
  Δ ≤ Δ′ →
  WfEffect Δ E →
  WfEffect Δ′ E
WfEffect-weaken Δ≤Δ′ wfE α∈E =
  <-≤-trans (wfE α∈E) Δ≤Δ′

WfEffTy-weaken :
  ∀ {Δ Δ′ A} →
  Δ ≤ Δ′ →
  WfEffTy Δ A →
  WfEffTy Δ′ A
WfEffTy-weaken Δ≤Δ′ (wf-eff-var α<Δ) =
  wf-eff-var (<-≤-trans α<Δ Δ≤Δ′)
WfEffTy-weaken Δ≤Δ′ wf-eff-base = wf-eff-base
WfEffTy-weaken Δ≤Δ′ wf-eff-star = wf-eff-star
WfEffTy-weaken Δ≤Δ′ (wf-eff-fun hA wfE hB) =
  wf-eff-fun
    (WfEffTy-weaken Δ≤Δ′ hA)
    (WfEffect-weaken Δ≤Δ′ wfE)
    (WfEffTy-weaken Δ≤Δ′ hB)
WfEffTy-weaken Δ≤Δ′ (wf-eff-all wfE hA) =
  wf-eff-all
    (WfEffect-weaken (s≤s Δ≤Δ′) wfE)
    (WfEffTy-weaken (s≤s Δ≤Δ′) hA)

extᵗ-cong-env :
  ∀ {ρ τ} →
  (∀ α → ρ α ≡ τ α) →
  ∀ α →
  extᵗ ρ α ≡ extᵗ τ α
extᵗ-cong-env eq zero = refl
extᵗ-cong-env eq (suc α) = cong suc (eq α)

renameᵉ-cong :
  ∀ {ρ τ} →
  (∀ α → ρ α ≡ τ α) →
  ∀ A →
  renameᵉ ρ A ≡ renameᵉ τ A
renameᵉ-cong eq (ty-var α) = cong ty-var (eq α)
renameᵉ-cong eq (ty-base ι) = refl
renameᵉ-cong eq ty-star = refl
renameᵉ-cong eq (A ⇒[ E ] B)
  rewrite renameᵉ-cong eq A
        | renameᴱ-cong eq E
        | renameᵉ-cong eq B = refl
renameᵉ-cong eq (ty-all E A)
  rewrite renameᴱ-cong (extᵗ-cong-env eq) E
        | renameᵉ-cong (extᵗ-cong-env eq) A = refl

renameᵉ-compose :
  ∀ ρ τ A →
  renameᵉ τ (renameᵉ ρ A) ≡ renameᵉ (λ α → τ (ρ α)) A
renameᵉ-compose ρ τ (ty-var α) = refl
renameᵉ-compose ρ τ (ty-base ι) = refl
renameᵉ-compose ρ τ ty-star = refl
renameᵉ-compose ρ τ (A ⇒[ E ] B)
  rewrite renameᵉ-compose ρ τ A
        | renameᴱ-compose ρ τ E
        | renameᵉ-compose ρ τ B = refl
renameᵉ-compose ρ τ (ty-all E A)
  rewrite renameᴱ-compose (extᵗ ρ) (extᵗ τ) E
        | renameᵉ-compose (extᵗ ρ) (extᵗ τ) A =
  cong₂ ty-all (renameᴱ-cong env-eq E) (renameᵉ-cong env-eq A)
  where
    env-eq :
      ∀ α →
      extᵗ τ (extᵗ ρ α) ≡ extᵗ (λ β → τ (ρ β)) α
    env-eq zero = refl
    env-eq (suc α) = refl

renameᵉ-open-suc :
  ∀ A α →
  renameᵉ suc (A [ α ]ᵉ) ≡ renameᵉ (extᵗ suc) A [ suc α ]ᵉ
renameᵉ-open-suc A α =
  trans
    (renameᵉ-compose (singleRenameᵗ α) suc A)
    (trans
      (renameᵉ-cong env-eq A)
      (sym (renameᵉ-compose (extᵗ suc) (singleRenameᵗ (suc α)) A)))
  where
    env-eq :
      ∀ β →
      suc (singleRenameᵗ α β) ≡
      singleRenameᵗ (suc α) (extᵗ suc β)
    env-eq zero = refl
    env-eq (suc β) = refl

renameᵉ-open-raise :
  ∀ k A α →
  renameᵉ (raiseVarFrom k) (A [ α ]ᵉ) ≡
  renameᵉ (extᵗ (raiseVarFrom k)) A [ raiseVarFrom k α ]ᵉ
renameᵉ-open-raise k A α =
  trans
    (renameᵉ-compose (singleRenameᵗ α) (raiseVarFrom k) A)
    (trans
      (renameᵉ-cong env-eq A)
      (sym
        (renameᵉ-compose
          (extᵗ (raiseVarFrom k))
          (singleRenameᵗ (raiseVarFrom k α))
          A)))
  where
    env-eq :
      ∀ β →
      raiseVarFrom k (singleRenameᵗ α β) ≡
      singleRenameᵗ (raiseVarFrom k α) (extᵗ (raiseVarFrom k) β)
    env-eq zero = refl
    env-eq (suc β) = refl

renameᴱ-raise-ext :
  ∀ k E →
  renameᴱ (extᵗ (raiseVarFrom k)) E ≡
  renameᴱ (raiseVarFrom (suc k)) E
renameᴱ-raise-ext k E = renameᴱ-cong (raise-ext k) E

drop0ᵉ-rename-raise :
  ∀ k E →
  drop0ᵉ (renameᴱ (raiseVarFrom (suc k)) E) ≡
  renameᴱ (raiseVarFrom k) (drop0ᵉ E)
drop0ᵉ-rename-raise k E =
  trans
    (cong drop0ᵉ (sym (renameᴱ-raise-ext k E)))
    (drop0ᵉ-rename (raiseVarFrom k) E)

renameᵉ-raise-ext :
  ∀ k A →
  renameᵉ (extᵗ (raiseVarFrom k)) A ≡
  renameᵉ (raiseVarFrom (suc k)) A
renameᵉ-raise-ext k A = renameᵉ-cong (raise-ext k) A

∈-renameᴱ-raise-inv :
  ∀ k {E α} →
  raiseVarFrom k α ∈ renameᴱ (raiseVarFrom k) E →
  α ∈ E
∈-renameᴱ-raise-inv k {E = []} ()
∈-renameᴱ-raise-inv k {E = β ∷ E} (here eq) =
  here (raiseVarFrom-injective k eq)
∈-renameᴱ-raise-inv k {E = β ∷ E} (there α∈E) =
  there (∈-renameᴱ-raise-inv k α∈E)

∉-renameᴱ-raise :
  ∀ k {E α} →
  α ∉ E →
  raiseVarFrom k α ∉ renameᴱ (raiseVarFrom k) E
∉-renameᴱ-raise k α∉E raised∈ =
  α∉E (∈-renameᴱ-raise-inv k raised∈)

occurs-erase-renameᵉ-raise :
  ∀ k α A →
  occurs (raiseVarFrom k α) (eraseᵉ (renameᵉ (raiseVarFrom k) A)) ≡
  occurs α (eraseᵉ A)
occurs-erase-renameᵉ-raise k α A
  rewrite erase-renameᵉ (raiseVarFrom k) A =
  occurs-raise k α (eraseᵉ A)

occurs-erase-renameᵉ-tyapp-raise :
  ∀ k α A →
  occurs
    (suc (raiseVarFrom k α))
    (eraseᵉ (renameᵉ (extᵗ (raiseVarFrom k)) A))
    ≡ occurs (suc α) (eraseᵉ A)
occurs-erase-renameᵉ-tyapp-raise k α A
  rewrite renameᵉ-raise-ext k A =
  occurs-erase-renameᵉ-raise (suc k) (suc α) A

------------------------------------------------------------------------
-- Term-variable renaming
------------------------------------------------------------------------

RenameEffWf : EffCtx → EffCtx → Renameˣ → Set₁
RenameEffWf Ξ Ξ′ ρ =
  ∀ {x A E} → Ξ ∋ x ⦂ A ▷ E → Ξ′ ∋ ρ x ⦂ A ▷ E

RenameEffWf-ext :
  ∀ {Ξ Ξ′ A E ρ} →
  RenameEffWf Ξ Ξ′ ρ →
  RenameEffWf ((A , E) ∷ Ξ) ((A , E) ∷ Ξ′) (extʳ ρ)
RenameEffWf-ext hρ Zᵉ = Zᵉ
RenameEffWf-ext hρ (Sᵉ h) = Sᵉ (hρ h)

lookup-renameCtxᵉ :
  ∀ τ {Ξ x A E} →
  Ξ ∋ x ⦂ A ▷ E →
  renameCtxᵉ τ Ξ ∋ x ⦂ renameᵉ τ A ▷ renameᴱ τ E
lookup-renameCtxᵉ τ Zᵉ = Zᵉ
lookup-renameCtxᵉ τ (Sᵉ h) = Sᵉ (lookup-renameCtxᵉ τ h)

lookup-emptyᵉ :
  ∀ {x A E} →
  [] ∋ x ⦂ A ▷ E →
  ⊥
lookup-emptyᵉ ()

lookup-renameCtxᵉ-inv :
  ∀ τ Ξ {x A′ E′} →
  renameCtxᵉ τ Ξ ∋ x ⦂ A′ ▷ E′ →
  ∃[ A ] ∃[ E ] (Ξ ∋ x ⦂ A ▷ E ×
    A′ ≡ renameᵉ τ A × E′ ≡ renameᴱ τ E)
lookup-renameCtxᵉ-inv τ [] h = ⊥-elim (lookup-emptyᵉ h)
lookup-renameCtxᵉ-inv τ ((A , E) ∷ Ξ) Zᵉ =
  A , E , Zᵉ , refl , refl
lookup-renameCtxᵉ-inv τ ((B , F) ∷ Ξ) (Sᵉ h)
    with lookup-renameCtxᵉ-inv τ Ξ h
lookup-renameCtxᵉ-inv τ ((B , F) ∷ Ξ) (Sᵉ h)
    | A , E , hΞ , eqA , eqE =
  A , E , Sᵉ hΞ , eqA , eqE

renameCtxᵉ-cong :
  ∀ {ρ τ} →
  (∀ α → ρ α ≡ τ α) →
  ∀ Ξ →
  renameCtxᵉ ρ Ξ ≡ renameCtxᵉ τ Ξ
renameCtxᵉ-cong eq [] = refl
renameCtxᵉ-cong eq ((A , E) ∷ Ξ) =
  cong₂
    _∷_
    (cong₂ _,_ (renameᵉ-cong eq A) (renameᴱ-cong eq E))
    (renameCtxᵉ-cong eq Ξ)

renameCtxᵉ-raise-ext :
  ∀ k Ξ →
  renameCtxᵉ (extᵗ (raiseVarFrom k)) Ξ ≡
  renameCtxᵉ (raiseVarFrom (suc k)) Ξ
renameCtxᵉ-raise-ext k Ξ = renameCtxᵉ-cong (raise-ext k) Ξ

renameStoreᵗ-cong :
  ∀ {ρ τ} →
  (∀ α → ρ α ≡ τ α) →
  ∀ Σ →
  renameStoreᵗ ρ Σ ≡ renameStoreᵗ τ Σ
renameStoreᵗ-cong eq [] = refl
renameStoreᵗ-cong eq ((α , A) ∷ Σ) =
  cong₂
    _∷_
    (cong₂ _,_ (eq α) (rename-cong eq A))
    (renameStoreᵗ-cong eq Σ)

renameStoreᵗ-raise-ext :
  ∀ k Σ →
  renameStoreᵗ (extᵗ (raiseVarFrom k)) Σ ≡
  renameStoreᵗ (raiseVarFrom (suc k)) Σ
renameStoreᵗ-raise-ext k Σ = renameStoreᵗ-cong (raise-ext k) Σ

renameStoreᵗ-compose :
  ∀ ρ τ Σ →
  renameStoreᵗ τ (renameStoreᵗ ρ Σ) ≡
  renameStoreᵗ (λ α → τ (ρ α)) Σ
renameStoreᵗ-compose ρ τ [] = refl
renameStoreᵗ-compose ρ τ ((α , A) ∷ Σ)
  rewrite renameᵗ-compose ρ τ A
        | renameStoreᵗ-compose ρ τ Σ = refl

renameStoreᵗ-raise-suc-comm :
  ∀ k Σ →
  renameStoreᵗ (raiseVarFrom (suc k)) (⟰ᵗ Σ) ≡
  ⟰ᵗ (renameStoreᵗ (raiseVarFrom k) Σ)
renameStoreᵗ-raise-suc-comm k Σ =
  trans
    (renameStoreᵗ-compose suc (raiseVarFrom (suc k)) Σ)
    (trans
      (renameStoreᵗ-cong env-eq Σ)
      (sym (renameStoreᵗ-compose (raiseVarFrom k) suc Σ)))
  where
    env-eq :
      ∀ α →
      raiseVarFrom (suc k) (suc α) ≡ suc (raiseVarFrom k α)
    env-eq α = refl

renameCtxᵉ-compose :
  ∀ ρ τ Ξ →
  renameCtxᵉ τ (renameCtxᵉ ρ Ξ) ≡
  renameCtxᵉ (λ α → τ (ρ α)) Ξ
renameCtxᵉ-compose ρ τ [] = refl
renameCtxᵉ-compose ρ τ ((A , E) ∷ Ξ)
  rewrite renameᵉ-compose ρ τ A
        | renameᴱ-compose ρ τ E
        | renameCtxᵉ-compose ρ τ Ξ = refl

renameCtxᵉ-raise-suc-comm :
  ∀ k Ξ →
  renameCtxᵉ (raiseVarFrom (suc k)) (renameCtxᵉ suc Ξ) ≡
  renameCtxᵉ suc (renameCtxᵉ (raiseVarFrom k) Ξ)
renameCtxᵉ-raise-suc-comm k Ξ =
  trans
    (renameCtxᵉ-compose suc (raiseVarFrom (suc k)) Ξ)
    (trans
      (renameCtxᵉ-cong env-eq Ξ)
      (sym (renameCtxᵉ-compose (raiseVarFrom k) suc Ξ)))
  where
    env-eq :
      ∀ α →
      raiseVarFrom (suc k) (suc α) ≡ suc (raiseVarFrom k α)
    env-eq α = refl

RenameEffWf-renameCtxᵉ :
  ∀ {Ξ Ξ′ ρ} τ →
  RenameEffWf Ξ Ξ′ ρ →
  RenameEffWf (renameCtxᵉ τ Ξ) (renameCtxᵉ τ Ξ′) ρ
RenameEffWf-renameCtxᵉ {Ξ = Ξ} τ hρ h
    with lookup-renameCtxᵉ-inv τ Ξ h
RenameEffWf-renameCtxᵉ {Ξ = Ξ} τ hρ h
    | A , E , hΞ , refl , refl =
  lookup-renameCtxᵉ τ (hρ hΞ)

typing-renameˣ :
  ∀ {Δ Σ Ξ Ξ′ M A E ρ} →
  RenameEffWf Ξ Ξ′ ρ →
  Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ E →
  Δ ∣ Σ ∣ Ξ′ ⊢ renameˣᵐ ρ M ⦂ A ▷ E
typing-renameˣ hρ (eff-var hΞ) = eff-var (hρ hΞ)
typing-renameˣ hρ (eff-lam hA hM) =
  eff-lam hA (typing-renameˣ (RenameEffWf-ext hρ) hM)
typing-renameˣ hρ (eff-app hL hM EM⊆Earg) =
  eff-app (typing-renameˣ hρ hL) (typing-renameˣ hρ hM) EM⊆Earg
typing-renameˣ hρ (eff-tylam vM hM) =
  eff-tylam
    (renameˣᵐ-preserves-Value _ vM)
    (typing-renameˣ (RenameEffWf-renameCtxᵉ suc hρ) hM)
typing-renameˣ hρ (eff-tyapp hL α<Δ α∉E noαB) =
  eff-tyapp (typing-renameˣ hρ hL) α<Δ α∉E noαB
typing-renameˣ hρ (eff-nu hA hN) =
  eff-nu hA (typing-renameˣ (RenameEffWf-renameCtxᵉ suc hρ) hN)
typing-renameˣ hρ (eff-const κ) = eff-const κ
typing-renameˣ hρ (eff-prim hL op hM) =
  eff-prim (typing-renameˣ hρ hL) op (typing-renameˣ hρ hM)
typing-renameˣ hρ (eff-cast d c⊢ exact hM) =
  eff-cast d c⊢ exact (typing-renameˣ hρ hM)
typing-renameˣ hρ (eff-blame hA) = eff-blame hA
typing-renameˣ hρ (eff-sub hM E⊆F) =
  eff-sub (typing-renameˣ hρ hM) E⊆F

typing-renameˣ-shift :
  ∀ {Δ Σ Ξ M A B E F} →
  Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ E →
  Δ ∣ Σ ∣ ((B , F) ∷ Ξ) ⊢ renameˣᵐ suc M ⦂ A ▷ E
typing-renameˣ-shift hM =
  typing-renameˣ (λ h → Sᵉ h) hM

------------------------------------------------------------------------
-- Type-context and store weakening
------------------------------------------------------------------------

typing-weaken :
  ∀ {Δ Δ′ Σ Σ′ Ξ M A E} →
  Δ ≤ Δ′ →
  StoreIncl Σ Σ′ →
  Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ E →
  Δ′ ∣ Σ′ ∣ Ξ ⊢ M ⦂ A ▷ E
typing-weaken Δ≤Δ′ incl (eff-var hΞ) = eff-var hΞ
typing-weaken Δ≤Δ′ incl (eff-lam hA hM) =
  eff-lam
    (WfEffTy-weaken Δ≤Δ′ hA)
    (typing-weaken Δ≤Δ′ incl hM)
typing-weaken Δ≤Δ′ incl (eff-app hL hM EM⊆Earg) =
  eff-app
    (typing-weaken Δ≤Δ′ incl hL)
    (typing-weaken Δ≤Δ′ incl hM)
    EM⊆Earg
typing-weaken Δ≤Δ′ incl (eff-tylam vM hM) =
  eff-tylam vM
    (typing-weaken
      (s≤s Δ≤Δ′)
      (renameStoreᵗ-incl suc incl)
      hM)
typing-weaken Δ≤Δ′ incl (eff-tyapp hL α<Δ α∉E noαB) =
  eff-tyapp
    (typing-weaken Δ≤Δ′ incl hL)
    (<-≤-trans α<Δ Δ≤Δ′)
    α∉E
    noαB
typing-weaken Δ≤Δ′ incl (eff-nu hA hN) =
  eff-nu
    (WfTy-weakenᵗ hA Δ≤Δ′)
    (typing-weaken
      (s≤s Δ≤Δ′)
      (StoreIncl-cons (renameStoreᵗ-incl suc incl))
      hN)
typing-weaken Δ≤Δ′ incl (eff-const κ) = eff-const κ
typing-weaken Δ≤Δ′ incl (eff-prim hL op hM) =
  eff-prim
    (typing-weaken Δ≤Δ′ incl hL)
    op
    (typing-weaken Δ≤Δ′ incl hM)
typing-weaken Δ≤Δ′ incl (eff-cast d c⊢ exact hM) =
  eff-cast
    (⊆-trans d incl)
    (coercion-weaken Δ≤Δ′ (complement-incl d incl) StoreIncl-refl c⊢)
    exact
    (typing-weaken Δ≤Δ′ incl hM)
typing-weaken Δ≤Δ′ incl (eff-blame hA) =
  eff-blame (WfEffTy-weaken Δ≤Δ′ hA)
typing-weaken Δ≤Δ′ incl (eff-sub hM E⊆F) =
  eff-sub (typing-weaken Δ≤Δ′ incl hM) E⊆F

------------------------------------------------------------------------
-- Term substitution environments
------------------------------------------------------------------------

SubstEffWf : TyCtx → Store → EffCtx → EffCtx → Substˣ → Set₁
SubstEffWf Δ Σ Ξ Ξ′ σ =
  ∀ {x A E} → Ξ ∋ x ⦂ A ▷ E → Δ ∣ Σ ∣ Ξ′ ⊢ σ x ⦂ A ▷ E

SubstEffWf-exts :
  ∀ {Δ Σ Ξ Ξ′ A E σ} →
  SubstEffWf Δ Σ Ξ Ξ′ σ →
  SubstEffWf Δ Σ ((A , E) ∷ Ξ) ((A , E) ∷ Ξ′) (extˢˣ σ)
SubstEffWf-exts hσ Zᵉ = eff-var Zᵉ
SubstEffWf-exts hσ (Sᵉ h) = typing-renameˣ-shift (hσ h)

singleSubstEffWf :
  ∀ {Δ Σ Ξ A E V EV} →
  Δ ∣ Σ ∣ Ξ ⊢ V ⦂ A ▷ EV →
  EV ⊆ᵉ E →
  SubstEffWf Δ Σ ((A , E) ∷ Ξ) Ξ (singleEnv V)
singleSubstEffWf hV EV⊆E Zᵉ = eff-sub hV EV⊆E
singleSubstEffWf hV EV⊆E (Sᵉ h) = eff-var h
