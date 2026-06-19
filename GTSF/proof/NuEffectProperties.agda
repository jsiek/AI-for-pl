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
open import Data.List.Relation.Binary.Sublist.Propositional
  renaming ([] to []⊆; _∷_ to _∷⊆_; _∷ʳ_ to _∷ʳ⊆_)
  using ()
open import Data.Bool using (false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (_<_; _≤_; zero; suc; z<s; s<s; s≤s)
open import Data.Nat.Properties using (_≟_; ≤-refl; <-≤-trans; suc-injective)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; subst; sym; trans)
open import Relation.Nullary using (yes; no)

open import Types
open import Store
  using
    ( StoreIncl
    ; StoreIncl-cons
    ; StoreIncl-drop
    ; StoreIncl-refl
    ; _⊆_
    ; ⊆-refl
    ; complement
    ; ⊆-trans
    )
open import Coercions
open import NuTerms
open import NuReduction renaming (β to β-ƛ)
open import NuEffectTyping
open import Primitives using (κℕ; constTy; constTy-renameᵗ)
open import proof.CoercionProperties
  using
    ( coercion-weaken
    ; coercion-open-gen-tagged
    ; coercion-renameᵗ
    ; complement-incl
    ; complement-rename
    ; domˢ-incl
    ; domˢ-rename
    ; renameStoreᵗ-ext-suc-cons-comm
    ; renameᶜ-preserves-Inert
    )
open import proof.NuStoreProperties using (renameStoreᵗ-incl)
open import proof.NuTermProperties
  using
    ( renameˣᵐ-preserves-Value
    ; renameᵗᵐ-preserves-Value
    ; substˣᵐ-preserves-Value
    )
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
    ; renameStoreᵗ-ext-suc-comm
    ; renameᵗ-id
    ; renameᵗ-ext-suc-comm
    ; renameᵗ-compose
    ; renameᵗ-preserves-WfTy
    )

------------------------------------------------------------------------
-- Role-context renaming
------------------------------------------------------------------------

lookup-role :
  ∀ Δ {α} →
  α < ⌊ Δ ⌋ →
  ∃[ r ] Δ ∋ᵣ α ⦂ r
lookup-role [] ()
lookup-role (r ∷ Δ) {zero} z<s = r , Zᵣ
lookup-role (r ∷ Δ) {suc α} (s<s α<Δ)
    with lookup-role Δ α<Δ
lookup-role (r ∷ Δ) {suc α} (s<s α<Δ)
    | s , h = s , Sᵣ h

RoleRenameWf : RoleCtx → RoleCtx → Renameᵗ → Set
RoleRenameWf Δ Δ′ ρ =
  ∀ {α r} → Δ ∋ᵣ α ⦂ r → Δ′ ∋ᵣ ρ α ⦂ r

RoleRenameWf-ext :
  ∀ {Δ Δ′ ρ} r →
  RoleRenameWf Δ Δ′ ρ →
  RoleRenameWf (r ∷ Δ) (r ∷ Δ′) (extᵗ ρ)
RoleRenameWf-ext r hρ Zᵣ = Zᵣ
RoleRenameWf-ext r hρ (Sᵣ h) = Sᵣ (hρ h)

RoleRenameWf-suc :
  ∀ {Δ r} →
  RoleRenameWf Δ (r ∷ Δ) suc
RoleRenameWf-suc h = Sᵣ h

RoleRenameWf-to-TyRenameWf :
  ∀ {Δ Δ′ ρ} →
  RoleRenameWf Δ Δ′ ρ →
  TyRenameWf ⌊ Δ ⌋ ⌊ Δ′ ⌋ ρ
RoleRenameWf-to-TyRenameWf {Δ = Δ} hρ α<Δ
    with lookup-role Δ α<Δ
RoleRenameWf-to-TyRenameWf hρ α<Δ | r , h =
  role-< (hρ h)

RuntimeRenameWf : RoleCtx → RoleCtx → Renameᵗ → Set
RuntimeRenameWf Δ Δ′ ρ =
  ∀ {α} → Δ ∋ᵣ α ⦂ runtime → Δ′ ∋ᵣ ρ α ⦂ runtime

RuntimeRenameWf-ext :
  ∀ {Δ Δ′ ρ} r →
  RuntimeRenameWf Δ Δ′ ρ →
  RuntimeRenameWf (r ∷ Δ) (r ∷ Δ′) (extᵗ ρ)
RuntimeRenameWf-ext ordinary hρ {zero} ()
RuntimeRenameWf-ext ordinary hρ {suc α} (Sᵣ h) = Sᵣ (hρ h)
RuntimeRenameWf-ext runtime hρ Zᵣ = Zᵣ
RuntimeRenameWf-ext runtime hρ (Sᵣ h) = Sᵣ (hρ h)

RuntimeRenameWf-suc :
  ∀ {Δ r} →
  RuntimeRenameWf Δ (r ∷ Δ) suc
RuntimeRenameWf-suc h = Sᵣ h

RuntimeRenameInjective : RoleCtx → Renameᵗ → Set
RuntimeRenameInjective Δ ρ =
  ∀ {α β} →
  Δ ∋ᵣ α ⦂ runtime →
  Δ ∋ᵣ β ⦂ runtime →
  ρ α ≡ ρ β →
  α ≡ β

RuntimeRenameInjective-ext :
  ∀ {Δ ρ} r →
  RuntimeRenameInjective Δ ρ →
  RuntimeRenameInjective (r ∷ Δ) (extᵗ ρ)
RuntimeRenameInjective-ext ordinary inj {zero} ()
RuntimeRenameInjective-ext ordinary inj {suc α} {zero} (Sᵣ hα) ()
RuntimeRenameInjective-ext ordinary inj {suc α} {suc β} (Sᵣ hα) (Sᵣ hβ) eq =
  cong suc (inj hα hβ (suc-injective eq))
RuntimeRenameInjective-ext runtime inj Zᵣ Zᵣ eq = refl
RuntimeRenameInjective-ext runtime inj Zᵣ (Sᵣ hβ) ()
RuntimeRenameInjective-ext runtime inj (Sᵣ hα) Zᵣ ()
RuntimeRenameInjective-ext runtime inj (Sᵣ hα) (Sᵣ hβ) eq =
  cong suc (inj hα hβ (suc-injective eq))

RuntimeRenameInjective-suc :
  ∀ {Δ} →
  RuntimeRenameInjective Δ suc
RuntimeRenameInjective-suc hα hβ eq = suc-injective eq

RuntimeRenameInjective-open-ordinary :
  ∀ {Δ α} →
  RuntimeRenameInjective (ordinary ∷ Δ) (singleRenameᵗ α)
RuntimeRenameInjective-open-ordinary {α = α} {zero} ()
RuntimeRenameInjective-open-ordinary {α = α} {suc β} {zero} (Sᵣ hβ) ()
RuntimeRenameInjective-open-ordinary {α = α} {suc β} {suc γ}
    (Sᵣ hβ) (Sᵣ hγ) eq =
  cong suc eq

RoleRenameWf-to-RuntimeRenameWf :
  ∀ {Δ Δ′ ρ} →
  RoleRenameWf Δ Δ′ ρ →
  RuntimeRenameWf Δ Δ′ ρ
RoleRenameWf-to-RuntimeRenameWf hρ h = hρ h

RuntimeTy-rename :
  ∀ {Δ Δ′ A ρ} →
  RuntimeRenameWf Δ Δ′ ρ →
  RuntimeTy Δ A →
  RuntimeTy Δ′ (renameᵗ ρ A)
RuntimeTy-rename hρ (rt-var hα) = rt-var (hρ hα)
RuntimeTy-rename hρ rt-base = rt-base
RuntimeTy-rename hρ rt-star = rt-star
RuntimeTy-rename hρ (rt-fun hA hB) =
  rt-fun (RuntimeTy-rename hρ hA) (RuntimeTy-rename hρ hB)
RuntimeTy-rename hρ (rt-all hA) =
  rt-all (RuntimeTy-rename (RuntimeRenameWf-ext ordinary hρ) hA)

CoercionRoles-rename :
  ∀ {Δ Δ′ c ρ} →
  RuntimeRenameWf Δ Δ′ ρ →
  CoercionRoles Δ c →
  CoercionRoles Δ′ (renameᶜ ρ c)
CoercionRoles-rename hρ roles-id = roles-id
CoercionRoles-rename hρ (roles-seq hc hd) =
  roles-seq (CoercionRoles-rename hρ hc) (CoercionRoles-rename hρ hd)
CoercionRoles-rename hρ (roles-fun hc hd) =
  roles-fun (CoercionRoles-rename hρ hc) (CoercionRoles-rename hρ hd)
CoercionRoles-rename hρ (roles-all hc) =
  roles-all (CoercionRoles-rename (RuntimeRenameWf-ext ordinary hρ) hc)
CoercionRoles-rename hρ (roles-tag hG) =
  roles-tag (RuntimeTy-rename hρ hG)
CoercionRoles-rename hρ (roles-untag hG) =
  roles-untag (RuntimeTy-rename hρ hG)
CoercionRoles-rename hρ (roles-seal hA hα) =
  roles-seal (RuntimeTy-rename hρ hA) (hρ hα)
CoercionRoles-rename hρ (roles-unseal hA hα) =
  roles-unseal (RuntimeTy-rename hρ hA) (hρ hα)
CoercionRoles-rename hρ (roles-gen hA hc) =
  roles-gen
    (RuntimeTy-rename hρ hA)
    (CoercionRoles-rename (RuntimeRenameWf-ext runtime hρ) hc)
CoercionRoles-rename hρ (roles-inst hB hc) =
  roles-inst
    (RuntimeTy-rename hρ hB)
    (CoercionRoles-rename (RuntimeRenameWf-ext runtime hρ) hc)

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

∈-++-elim :
  ∀ {E F : Effect} {α : TyVar} →
  α ∈ E ++ F →
  α ∈ E ⊎ α ∈ F
∈-++-elim {E = []} α∈ = inj₂ α∈
∈-++-elim {E = β ∷ E} (here refl) = inj₁ (here refl)
∈-++-elim {E = β ∷ E} (there α∈)
    with ∈-++-elim {E = E} α∈
∈-++-elim {E = β ∷ E} (there α∈) | inj₁ α∈E =
  inj₁ (there α∈E)
∈-++-elim {E = β ∷ E} (there α∈) | inj₂ α∈F =
  inj₂ α∈F

⊆ᵉ-++ˡ :
  ∀ {E F : Effect} →
  E ⊆ᵉ E ++ F
⊆ᵉ-++ˡ = ∈-++ˡ

⊆ᵉ-++ʳ :
  ∀ (E : Effect) {F : Effect} →
  F ⊆ᵉ E ++ F
⊆ᵉ-++ʳ E = ∈-++ʳ E

⊆ᵉ-++ :
  ∀ {E F G : Effect} →
  E ⊆ᵉ G →
  F ⊆ᵉ G →
  E ++ F ⊆ᵉ G
⊆ᵉ-++ E⊆G F⊆G h with ∈-++-elim h
⊆ᵉ-++ E⊆G F⊆G h | inj₁ hE = E⊆G hE
⊆ᵉ-++ E⊆G F⊆G h | inj₂ hF = F⊆G hF

⊆ᵉ-++-mono :
  ∀ {E E′ F F′ : Effect} →
  E ⊆ᵉ E′ →
  F ⊆ᵉ F′ →
  E ++ F ⊆ᵉ E′ ++ F′
⊆ᵉ-++-mono E⊆E′ F⊆F′ =
  ⊆ᵉ-++ (λ h → ∈-++ˡ (E⊆E′ h))
         (λ h → ∈-++ʳ _ (F⊆F′ h))

⊆ᵉ-++-dup :
  ∀ {E F : Effect} →
  (E ++ F) ++ F ⊆ᵉ E ++ F
⊆ᵉ-++-dup =
  ⊆ᵉ-++ ⊆ᵉ-refl (⊆ᵉ-++ʳ _)

∉-++ˡ :
  ∀ {E F : Effect} {α : TyVar} →
  α ∉ E ++ F →
  α ∉ E
∉-++ˡ α∉EF α∈E = α∉EF (∈-++ˡ α∈E)

∉-++ʳ :
  ∀ {E F : Effect} {α : TyVar} →
  α ∉ E ++ F →
  α ∉ F
∉-++ʳ {E = E} α∉EF α∈F = α∉EF (∈-++ʳ E α∈F)

WfEffect-++ :
  ∀ {Δ E F} →
  WfEffect Δ E →
  WfEffect Δ F →
  WfEffect Δ (E ++ F)
WfEffect-++ {E = []} wfE wfF = wfF
WfEffect-++ {E = α ∷ E} wfE wfF (here refl) = wfE (here refl)
WfEffect-++ {E = α ∷ E} wfE wfF (there β∈) =
  WfEffect-++ (λ γ∈ → wfE (there γ∈)) wfF β∈

WfEffect-[] :
  ∀ {Δ} →
  WfEffect Δ []
WfEffect-[] ()

RoleStoreWf : RoleCtx → Store → Set
RoleStoreWf Δ Σ =
  ∀ {α} → Δ ∋ᵣ α ⦂ runtime → α ∈ domˢ Σ

RoleStoreWf-incl :
  ∀ {Δ Σ Σ′} →
  StoreIncl Σ Σ′ →
  RoleStoreWf Δ Σ →
  RoleStoreWf Δ Σ′
RoleStoreWf-incl incl wf hα = domˢ-incl incl (wf hα)

RoleStoreWf-ordinary :
  ∀ {Δ Σ} →
  RoleStoreWf Δ Σ →
  RoleStoreWf (ordinary ∷ Δ) (⟰ᵗ Σ)
RoleStoreWf-ordinary wf {zero} ()
RoleStoreWf-ordinary wf {suc α} (Sᵣ hα) = domˢ-rename suc (wf hα)

RoleStoreWf-runtime :
  ∀ {Δ Σ A} →
  RoleStoreWf Δ Σ →
  RoleStoreWf (runtime ∷ Δ) ((zero , A) ∷ ⟰ᵗ Σ)
RoleStoreWf-runtime wf Zᵣ = here refl
RoleStoreWf-runtime wf (Sᵣ hα) = there (domˢ-rename suc (wf hα))

RawSealSideExact : Coercion → Store → Set
RawSealSideExact c Π =
  ∀ {α A} →
  (α , A) ∈ Π →
  α ∈ sealUsesᶜ c

domˢ-complement :
  ∀ {Σ Π α} →
  (d : Π ⊆ Σ) →
  α ∈ domˢ Σ →
  (∀ {A} → (α , A) ∈ Π → ⊥) →
  α ∈ domˢ (complement d)
domˢ-complement []⊆ () noΠ
domˢ-complement ((β , B) ∷ʳ⊆ d) (here refl) noΠ = here refl
domˢ-complement ((β , B) ∷ʳ⊆ d) (there α∈Σ) noΠ =
  there (domˢ-complement d α∈Σ noΠ)
domˢ-complement (refl ∷⊆ d) (here refl) noΠ =
  ⊥-elim (noΠ (here refl))
domˢ-complement (refl ∷⊆ d) (there α∈Σ) noΠ =
  domˢ-complement d α∈Σ (λ h → noΠ (there h))

coercion-open-gen-effect :
  ∀ {Δ Σ Π c A B α} →
  (d : Π ⊆ Σ) →
  α < Δ →
  α ∈ domˢ Σ →
  α ∉ sealUsesᶜ (gen A c) →
  RawSealSideExact (gen A c) Π →
  suc Δ ∣ (zero , ★) ∷ ⟰ᵗ (complement d) ∣ ⟰ᵗ Π
    ⊢ c ∶ ⇑ᵗ A =⇒ B →
  Δ ∣ complement d ∣ Π ⊢ c [ α ]ᶜ ∶ A =⇒ B [ α ]ᴿ
coercion-open-gen-effect d α<Δ α∈Σ α∉seal exact c⊢ =
  coercion-open-gen-tagged
    α<Δ
    (domˢ-complement d α∈Σ (λ h → α∉seal (exact h)))
    c⊢

∈-renameᴱ :
  ∀ ρ {E α} →
  α ∈ E →
  ρ α ∈ renameᴱ ρ E
∈-renameᴱ ρ (here refl) = here refl
∈-renameᴱ ρ (there α∈E) = there (∈-renameᴱ ρ α∈E)

RenameInjective : Renameᵗ → Set
RenameInjective ρ = ∀ {α β} → ρ α ≡ ρ β → α ≡ β

RenameInjective-ext :
  ∀ {ρ} →
  RenameInjective ρ →
  RenameInjective (extᵗ ρ)
RenameInjective-ext inj {zero} {zero} eq = refl
RenameInjective-ext inj {zero} {suc β} ()
RenameInjective-ext inj {suc α} {zero} ()
RenameInjective-ext inj {suc α} {suc β} eq =
  cong suc (inj (suc-injective eq))

suc-RenameInjective : RenameInjective suc
suc-RenameInjective eq = suc-injective eq

raiseVarFrom-RenameInjective :
  ∀ k →
  RenameInjective (raiseVarFrom k)
raiseVarFrom-RenameInjective k eq = raiseVarFrom-injective k eq

∈-renameᴱ-inv :
  ∀ {ρ E α} →
  RenameInjective ρ →
  ρ α ∈ renameᴱ ρ E →
  α ∈ E
∈-renameᴱ-inv {E = []} inj ()
∈-renameᴱ-inv {E = β ∷ E} inj (here eq) = here (inj eq)
∈-renameᴱ-inv {E = β ∷ E} inj (there ρα∈) =
  there (∈-renameᴱ-inv inj ρα∈)

∉-renameᴱ :
  ∀ {ρ E α} →
  RenameInjective ρ →
  α ∉ E →
  ρ α ∉ renameᴱ ρ E
∉-renameᴱ inj α∉E ρα∈ =
  α∉E (∈-renameᴱ-inv inj ρα∈)

∉-renameᴱ-runtime :
  ∀ {Δ ρ E α} →
  RuntimeRenameInjective Δ ρ →
  WfEffect Δ E →
  Δ ∋ᵣ α ⦂ runtime →
  α ∉ E →
  ρ α ∉ renameᴱ ρ E
∉-renameᴱ-runtime {E = []} rinj wfE hα α∉E ()
∉-renameᴱ-runtime {E = β ∷ E} rinj wfE hα α∉E (here eq) =
  α∉E (here (rinj hα (wfE (here refl)) eq))
∉-renameᴱ-runtime {E = β ∷ E} rinj wfE hα α∉E (there h) =
  ∉-renameᴱ-runtime
    rinj
    (λ γ∈ → wfE (there γ∈))
    hα
    (λ α∈E → α∉E (there α∈E))
    h

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

∈-renameStoreᵉ :
  ∀ ρ {Π α A} →
  (α , A) ∈ Π →
  (ρ α , renameᵉ ρ A) ∈ renameStoreᵉ ρ Π
∈-renameStoreᵉ ρ (here refl) = here refl
∈-renameStoreᵉ ρ (there h) = there (∈-renameStoreᵉ ρ h)

SealSideExact-rename :
  ∀ ρ {c Π} →
  SealSideExact c Π →
  SealSideExact (renameᶜ ρ c) (renameStoreᵉ ρ Π)
SealSideExact-rename ρ {c = c} {Π = []} exact ()
SealSideExact-rename ρ {c = c} {Π = (α , A) ∷ Π} exact
    (here refl) =
  subst
    (λ E → ρ α ∈ E)
    (sym (sealUsesᶜ-rename ρ c))
    (∈-renameᴱ ρ (exact (here refl)))
SealSideExact-rename ρ {c = c} {Π = (β , B) ∷ Π} exact
    (there h) =
  SealSideExact-rename ρ
    {c = c}
    {Π = Π}
    (λ β∈Π → exact (there β∈Π))
    h

SealSideExact-rename-raise :
  ∀ k {c Π} →
  SealSideExact c Π →
  SealSideExact
    (renameᶜ (raiseVarFrom k) c)
    (renameStoreᵉ (raiseVarFrom k) Π)
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

renameᴱ-mono :
  ∀ ρ {E F} →
  E ⊆ᵉ F →
  renameᴱ ρ E ⊆ᵉ renameᴱ ρ F
renameᴱ-mono ρ {E = []} E⊆F ()
renameᴱ-mono ρ {E = α ∷ E} E⊆F (here refl) =
  ∈-renameᴱ ρ (E⊆F (here refl))
renameᴱ-mono ρ {E = α ∷ E} E⊆F (there β∈E) =
  renameᴱ-mono ρ (λ γ∈E → E⊆F (there γ∈E)) β∈E

SealSideEffect-store-rename :
  ∀ ρ {Π F} →
  (∀ {α A} → (α , A) ∈ Π → α ∈ F) →
  ∀ {β B} →
  (β , B) ∈ renameStoreᵉ ρ Π →
  β ∈ renameᴱ ρ F
SealSideEffect-store-rename ρ {Π = []} store⊆ ()
SealSideEffect-store-rename ρ {Π = (α , A) ∷ Π} store⊆
    (here refl) =
  ∈-renameᴱ ρ (store⊆ (here refl))
SealSideEffect-store-rename ρ {Π = (α , A) ∷ Π} store⊆
    (there h) =
  SealSideEffect-store-rename ρ
    (λ β∈Π → store⊆ (there β∈Π))
    h

SealSideEffect-rename :
  ∀ ρ {c Π F} →
  SealSideEffect c Π F →
  SealSideEffect (renameᶜ ρ c) (renameStoreᵉ ρ Π) (renameᴱ ρ F)
SealSideEffect-rename ρ {c = c} {F = F} (seal⊆ , store⊆) =
  seal⊆′ , SealSideEffect-store-rename ρ store⊆
  where
    seal⊆′ :
      sealUsesᶜ (renameᶜ ρ c) ⊆ᵉ renameᴱ ρ F
    seal⊆′ h =
      renameᴱ-mono ρ seal⊆
        (subst (λ E → _ ∈ E) (sealUsesᶜ-rename ρ c) h)

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

renameᴱ-open :
  ∀ ρ E α →
  renameᴱ ρ (openᴱ E α) ≡
  openᴱ (renameᴱ (extᵗ ρ) E) (ρ α)
renameᴱ-open ρ E α =
  trans
    (renameᴱ-compose (singleRenameᵗ α) ρ E)
    (trans
      (renameᴱ-cong env-eq E)
      (sym
        (renameᴱ-compose
          (extᵗ ρ)
          (singleRenameᵗ (ρ α))
          E)))
  where
    env-eq :
      ∀ β →
      ρ (singleRenameᵗ α β) ≡
      singleRenameᵗ (ρ α) (extᵗ ρ β)
    env-eq zero = refl
    env-eq (suc β) = refl

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

WfEffect-drop0 :
  ∀ {Δ E r} →
  WfEffect (r ∷ Δ) E →
  WfEffect Δ (drop0ᵉ E)
WfEffect-drop0 {E = []} wfE ()
WfEffect-drop0 {E = zero ∷ E} wfE α∈ =
  WfEffect-drop0 (λ β∈ → wfE (there β∈)) α∈
WfEffect-drop0 {E = suc α ∷ E} wfE (here refl)
    with wfE (here refl)
WfEffect-drop0 {E = suc α ∷ E} wfE (here refl) | Sᵣ hα = hα
WfEffect-drop0 {E = suc α ∷ E} wfE (there β∈) =
  WfEffect-drop0 (λ γ∈ → wfE (there γ∈)) β∈

WfEffect-open-ordinary :
  ∀ {Δ E α} →
  WfEffect (ordinary ∷ Δ) E →
  WfEffect Δ (openᴱ E α)
WfEffect-open-ordinary {E = []} wfE ()
WfEffect-open-ordinary {E = zero ∷ E} wfE (here refl)
    with wfE (here refl)
WfEffect-open-ordinary {E = zero ∷ E} wfE (here refl) | ()
WfEffect-open-ordinary {E = zero ∷ E} wfE (there β∈) =
  WfEffect-open-ordinary (λ γ∈ → wfE (there γ∈)) β∈
WfEffect-open-ordinary {E = suc α ∷ E} wfE (here refl)
    with wfE (here refl)
WfEffect-open-ordinary {E = suc α ∷ E} wfE (here refl) | Sᵣ hα = hα
WfEffect-open-ordinary {E = suc α ∷ E} wfE (there β∈) =
  WfEffect-open-ordinary (λ γ∈ → wfE (there γ∈)) β∈

openᴱ-drop0-ordinary :
  ∀ {Δ E α} →
  WfEffect (ordinary ∷ Δ) E →
  openᴱ E α ⊆ᵉ drop0ᵉ E
openᴱ-drop0-ordinary {E = []} wfE ()
openᴱ-drop0-ordinary {E = zero ∷ E} wfE (here refl)
    with wfE (here refl)
openᴱ-drop0-ordinary {E = zero ∷ E} wfE (here refl) | ()
openᴱ-drop0-ordinary {E = zero ∷ E} wfE (there β∈) =
  openᴱ-drop0-ordinary (λ γ∈ → wfE (there γ∈)) β∈
openᴱ-drop0-ordinary {E = suc α ∷ E} wfE (here refl) = here refl
openᴱ-drop0-ordinary {E = suc α ∷ E} wfE (there β∈) =
  there (openᴱ-drop0-ordinary (λ γ∈ → wfE (there γ∈)) β∈)

CoercionRoles-wf-sealUses :
  ∀ {Δ c} →
  CoercionRoles Δ c →
  WfEffect Δ (sealUsesᶜ c)
CoercionRoles-wf-sealUses roles-id ()
CoercionRoles-wf-sealUses (roles-seq hc hd) =
  WfEffect-++ (CoercionRoles-wf-sealUses hc)
               (CoercionRoles-wf-sealUses hd)
CoercionRoles-wf-sealUses (roles-fun hc hd) =
  WfEffect-++ (CoercionRoles-wf-sealUses hc)
               (CoercionRoles-wf-sealUses hd)
CoercionRoles-wf-sealUses (roles-all hc) =
  WfEffect-drop0 (CoercionRoles-wf-sealUses hc)
CoercionRoles-wf-sealUses (roles-tag hG) ()
CoercionRoles-wf-sealUses (roles-untag hG) ()
CoercionRoles-wf-sealUses (roles-seal hA hα) (here refl) = hα
CoercionRoles-wf-sealUses (roles-seal hA hα) (there ())
CoercionRoles-wf-sealUses (roles-unseal hA hα) (here refl) = hα
CoercionRoles-wf-sealUses (roles-unseal hA hα) (there ())
CoercionRoles-wf-sealUses (roles-gen hA hc) =
  WfEffect-drop0 (CoercionRoles-wf-sealUses hc)
CoercionRoles-wf-sealUses (roles-inst hB hc) =
  WfEffect-drop0 (CoercionRoles-wf-sealUses hc)

WfEffect-suc :
  ∀ {Δ E r} →
  WfEffect Δ E →
  WfEffect (r ∷ Δ) (renameᴱ suc E)
WfEffect-suc {E = []} wfE ()
WfEffect-suc {E = α ∷ E} wfE (here refl) = Sᵣ (wfE (here refl))
WfEffect-suc {E = α ∷ E} wfE (there β∈) =
  WfEffect-suc (λ γ∈ → wfE (there γ∈)) β∈

WfEffect-rename :
  ∀ {Δ Δ′ E ρ} →
  RuntimeRenameWf Δ Δ′ ρ →
  WfEffect Δ E →
  WfEffect Δ′ (renameᴱ ρ E)
WfEffect-rename {E = []} hρ wfE ()
WfEffect-rename {E = α ∷ E} hρ wfE (here refl) =
  hρ (wfE (here refl))
WfEffect-rename {E = α ∷ E} hρ wfE (there β∈) =
  WfEffect-rename hρ (λ γ∈ → wfE (there γ∈)) β∈

WfEffTy-rename :
  ∀ {Δ Δ′ A ρ} →
  TyRenameWf ⌊ Δ ⌋ ⌊ Δ′ ⌋ ρ →
  RuntimeRenameWf Δ Δ′ ρ →
  WfEffTy Δ A →
  WfEffTy Δ′ (renameᵉ ρ A)
WfEffTy-rename hTy hρ (wf-eff-var α<Δ) = wf-eff-var (hTy α<Δ)
WfEffTy-rename hTy hρ wf-eff-base = wf-eff-base
WfEffTy-rename hTy hρ wf-eff-star = wf-eff-star
WfEffTy-rename hTy hρ (wf-eff-fun hA wfE hB) =
  wf-eff-fun
    (WfEffTy-rename hTy hρ hA)
    (WfEffect-rename hρ wfE)
    (WfEffTy-rename hTy hρ hB)
WfEffTy-rename hTy hρ (wf-eff-all wfE hA) =
  wf-eff-all
    (WfEffect-rename (RuntimeRenameWf-ext ordinary hρ) wfE)
    (WfEffTy-rename
      (TyRenameWf-ext hTy)
      (RuntimeRenameWf-ext ordinary hρ)
      hA)

WfEffTy-suc :
  ∀ {Δ A r} →
  WfEffTy Δ A →
  WfEffTy (r ∷ Δ) (renameᵉ suc A)
WfEffTy-suc = WfEffTy-rename TyRenameWf-suc RuntimeRenameWf-suc

singleRenameᵗ-Wf-role :
  ∀ {Δ α} →
  Δ ∋ᵣ α ⦂ runtime →
  TyRenameWf ⌊ ordinary ∷ Δ ⌋ ⌊ Δ ⌋ (singleRenameᵗ α)
singleRenameᵗ-Wf-role hα {zero} z<s = role-< hα
singleRenameᵗ-Wf-role hα {suc β} (s<s β<Δ) = β<Δ

RuntimeRenameWf-open-ordinary :
  ∀ {Δ α} →
  RuntimeRenameWf (ordinary ∷ Δ) Δ (singleRenameᵗ α)
RuntimeRenameWf-open-ordinary {α = α} {zero} ()
RuntimeRenameWf-open-ordinary {α = α} {suc β} (Sᵣ hβ) = hβ

WfEffTy-open-ordinary :
  ∀ {Δ A α} →
  Δ ∋ᵣ α ⦂ runtime →
  WfEffTy (ordinary ∷ Δ) A →
  WfEffTy Δ (A [ α ]ᵉ)
WfEffTy-open-ordinary hα =
  WfEffTy-rename
    (singleRenameᵗ-Wf-role hα)
    RuntimeRenameWf-open-ordinary

TyRenameWf-raise :
  ∀ k {Δ} →
  k ≤ Δ →
  TyRenameWf Δ (suc Δ) (raiseVarFrom k)
TyRenameWf-raise zero k≤Δ X<Δ = s<s X<Δ
TyRenameWf-raise (suc k) (s≤s k≤Δ) {zero} z<s = z<s
TyRenameWf-raise (suc k) (s≤s k≤Δ) {suc X} (s<s X<Δ) =
  s<s (TyRenameWf-raise k k≤Δ X<Δ)

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

renameᵉ-open :
  ∀ ρ A α →
  renameᵉ ρ (A [ α ]ᵉ) ≡
  renameᵉ (extᵗ ρ) A [ ρ α ]ᵉ
renameᵉ-open ρ A α =
  trans
    (renameᵉ-compose (singleRenameᵗ α) ρ A)
    (trans
      (renameᵉ-cong env-eq A)
      (sym
        (renameᵉ-compose
          (extᵗ ρ)
          (singleRenameᵗ (ρ α))
          A)))
  where
    env-eq :
      ∀ β →
      ρ (singleRenameᵗ α β) ≡
      singleRenameᵗ (ρ α) (extᵗ ρ β)
    env-eq zero = refl
    env-eq (suc β) = refl

renameᵉ-ext-suc-comm :
  ∀ ρ A →
  renameᵉ (extᵗ ρ) (renameᵉ suc A) ≡
  renameᵉ suc (renameᵉ ρ A)
renameᵉ-ext-suc-comm ρ A =
  trans
    (renameᵉ-compose suc (extᵗ ρ) A)
    (sym (renameᵉ-compose ρ suc A))

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

occurs-rename-injective :
  ∀ {ρ} →
  RenameInjective ρ →
  ∀ α A →
  occurs (ρ α) (renameᵗ ρ A) ≡ occurs α A
occurs-rename-injective {ρ = ρ} inj α (＇ β)
    with α ≟ β | ρ α ≟ ρ β
occurs-rename-injective inj α (＇ .α)
    | yes refl | yes refl = refl
occurs-rename-injective inj α (＇ .α)
    | yes refl | no neq =
  ⊥-elim (neq refl)
occurs-rename-injective inj α (＇ β)
    | no neq | yes eq =
  ⊥-elim (neq (inj eq))
occurs-rename-injective inj α (＇ β)
    | no neq | no neq′ = refl
occurs-rename-injective inj α (‵ ι) = refl
occurs-rename-injective inj α ★ = refl
occurs-rename-injective inj α (A ⇒ B)
  rewrite occurs-rename-injective inj α A
        | occurs-rename-injective inj α B = refl
occurs-rename-injective inj α (`∀ A) =
  occurs-rename-injective (RenameInjective-ext inj) (suc α) A

occurs-erase-renameᵉ-injective :
  ∀ {ρ} →
  RenameInjective ρ →
  ∀ α A →
  occurs (ρ α) (eraseᵉ (renameᵉ ρ A)) ≡
  occurs α (eraseᵉ A)
occurs-erase-renameᵉ-injective {ρ = ρ} inj α A
  rewrite erase-renameᵉ ρ A =
  occurs-rename-injective inj α (eraseᵉ A)

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

EffCtxWf-rename :
  ∀ {Δ Δ′ Ξ ρ} →
  TyRenameWf ⌊ Δ ⌋ ⌊ Δ′ ⌋ ρ →
  RuntimeRenameWf Δ Δ′ ρ →
  EffCtxWf Δ Ξ →
  EffCtxWf Δ′ (renameCtxᵉ ρ Ξ)
EffCtxWf-rename {Ξ = Ξ} hTy hρ wfΞ h
    with lookup-renameCtxᵉ-inv _ Ξ h
EffCtxWf-rename {Ξ = Ξ} hTy hρ wfΞ h
    | A , E , hΞ , refl , refl
    with wfΞ hΞ
EffCtxWf-rename {Ξ = Ξ} hTy hρ wfΞ h
    | A , E , hΞ , refl , refl
    | hA , hE =
  WfEffTy-rename hTy hρ hA , WfEffect-rename hρ hE

EffCtxWf-suc :
  ∀ {Δ Ξ r} →
  EffCtxWf Δ Ξ →
  EffCtxWf (r ∷ Δ) (renameCtxᵉ suc Ξ)
EffCtxWf-suc = EffCtxWf-rename TyRenameWf-suc RuntimeRenameWf-suc

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

renameᴱ-id :
  ∀ E →
  renameᴱ (λ α → α) E ≡ E
renameᴱ-id [] = refl
renameᴱ-id (α ∷ E) = cong (_∷_ α) (renameᴱ-id E)

extᵗ-id :
  ∀ α →
  extᵗ (λ β → β) α ≡ α
extᵗ-id zero = refl
extᵗ-id (suc α) = refl

renameᵉ-id :
  ∀ A →
  renameᵉ (λ α → α) A ≡ A
renameᵉ-id (ty-var α) = refl
renameᵉ-id (ty-base ι) = refl
renameᵉ-id ty-star = refl
renameᵉ-id (A ⇒[ E ] B)
  rewrite renameᵉ-id A
        | renameᴱ-id E
        | renameᵉ-id B = refl
renameᵉ-id (ty-all E A)
  rewrite renameᴱ-cong extᵗ-id E
        | renameᴱ-id E
        | renameᵉ-cong extᵗ-id A
        | renameᵉ-id A = refl

renameCtxᵉ-id :
  ∀ Ξ →
  renameCtxᵉ (λ α → α) Ξ ≡ Ξ
renameCtxᵉ-id [] = refl
renameCtxᵉ-id ((A , E) ∷ Ξ)
  rewrite renameᵉ-id A
        | renameᴱ-id E
        | renameCtxᵉ-id Ξ = refl

renameStoreᵗ-id :
  ∀ Σ →
  renameStoreᵗ (λ α → α) Σ ≡ Σ
renameStoreᵗ-id [] = refl
renameStoreᵗ-id ((α , A) ∷ Σ)
  rewrite renameᵗ-id A
        | renameStoreᵗ-id Σ = refl

renameᴱ-single-suc-cancel :
  ∀ α E →
  renameᴱ (singleRenameᵗ α) (renameᴱ suc E) ≡ E
renameᴱ-single-suc-cancel α E =
  trans
    (renameᴱ-compose suc (singleRenameᵗ α) E)
    (trans (renameᴱ-cong (λ β → refl) E) (renameᴱ-id E))

renameᵉ-single-suc-cancel :
  ∀ α A →
  renameᵉ (singleRenameᵗ α) (renameᵉ suc A) ≡ A
renameᵉ-single-suc-cancel α A =
  trans
    (renameᵉ-compose suc (singleRenameᵗ α) A)
    (trans (renameᵉ-cong (λ β → refl) A) (renameᵉ-id A))

renameCtxᵉ-single-suc-cancel :
  ∀ α Ξ →
  renameCtxᵉ (singleRenameᵗ α) (renameCtxᵉ suc Ξ) ≡ Ξ
renameCtxᵉ-single-suc-cancel α Ξ =
  trans
    (renameCtxᵉ-compose suc (singleRenameᵗ α) Ξ)
    (trans (renameCtxᵉ-cong (λ β → refl) Ξ) (renameCtxᵉ-id Ξ))

renameStoreᵗ-single-suc-cancel :
  ∀ α Σ →
  renameStoreᵗ (singleRenameᵗ α) (⟰ᵗ Σ) ≡ Σ
renameStoreᵗ-single-suc-cancel α Σ =
  trans
    (renameStoreᵗ-compose suc (singleRenameᵗ α) Σ)
    (trans (renameStoreᵗ-cong (λ β → refl) Σ) (renameStoreᵗ-id Σ))

EffStoreIncl-refl :
  ∀ {Σ : EffStore} →
  Σ ⊆ Σ
EffStoreIncl-refl = ⊆-refl

EffStoreIncl-drop :
  ∀ {Σ : EffStore} {α : TyVar} {A : EffTy} →
  Σ ⊆ ((α , A) ∷ Σ)
EffStoreIncl-drop {α = α} {A = A} = (α , A) ∷ʳ⊆ ⊆-refl

EffStoreIncl-cons :
  ∀ {Σ Σ′ : EffStore} {x} →
  Σ ⊆ Σ′ →
  (x ∷ Σ) ⊆ (x ∷ Σ′)
EffStoreIncl-cons incl = refl ∷⊆ incl

renameStoreᵉ-incl :
  ∀ ρ {Σ Σ′ : EffStore} →
  Σ ⊆ Σ′ →
  renameStoreᵉ ρ Σ ⊆ renameStoreᵉ ρ Σ′
renameStoreᵉ-incl ρ []⊆ = []⊆
renameStoreᵉ-incl ρ ((α , A) ∷ʳ⊆ incl) =
  (ρ α , renameᵉ ρ A) ∷ʳ⊆ renameStoreᵉ-incl ρ incl
renameStoreᵉ-incl ρ (refl ∷⊆ incl) =
  refl ∷⊆ renameStoreᵉ-incl ρ incl

renameStoreᵉ-cong :
  ∀ {ρ τ} →
  (∀ α → ρ α ≡ τ α) →
  ∀ Σ →
  renameStoreᵉ ρ Σ ≡ renameStoreᵉ τ Σ
renameStoreᵉ-cong eq [] = refl
renameStoreᵉ-cong eq ((α , A) ∷ Σ) =
  cong₂
    _∷_
    (cong₂ _,_ (eq α) (renameᵉ-cong eq A))
    (renameStoreᵉ-cong eq Σ)

renameStoreᵉ-compose :
  ∀ ρ τ Σ →
  renameStoreᵉ τ (renameStoreᵉ ρ Σ) ≡
  renameStoreᵉ (λ α → τ (ρ α)) Σ
renameStoreᵉ-compose ρ τ [] = refl
renameStoreᵉ-compose ρ τ ((α , A) ∷ Σ)
  rewrite renameᵉ-compose ρ τ A
        | renameStoreᵉ-compose ρ τ Σ = refl

renameStoreᵉ-id :
  ∀ Σ →
  renameStoreᵉ (λ α → α) Σ ≡ Σ
renameStoreᵉ-id [] = refl
renameStoreᵉ-id ((α , A) ∷ Σ)
  rewrite renameᵉ-id A
        | renameStoreᵉ-id Σ = refl

renameStoreᵉ-ext-suc-comm :
  ∀ ρ Σ →
  renameStoreᵉ (extᵗ ρ) (⟰ᵉ Σ) ≡ ⟰ᵉ (renameStoreᵉ ρ Σ)
renameStoreᵉ-ext-suc-comm ρ [] = refl
renameStoreᵉ-ext-suc-comm ρ ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (renameᵉ-ext-suc-comm ρ A))
    (renameStoreᵉ-ext-suc-comm ρ Σ)

renameStoreᵉ-ext-suc-cons-comm :
  ∀ ρ Σ A →
  renameStoreᵉ (extᵗ ρ) ((zero , renameᵉ suc A) ∷ ⟰ᵉ Σ) ≡
  (zero , renameᵉ suc (renameᵉ ρ A)) ∷ ⟰ᵉ (renameStoreᵉ ρ Σ)
renameStoreᵉ-ext-suc-cons-comm ρ Σ A =
  cong₂ _∷_
    (cong₂ _,_ refl (renameᵉ-ext-suc-comm ρ A))
    (renameStoreᵉ-ext-suc-comm ρ Σ)

renameStoreᵉ-single-suc-cancel :
  ∀ α Σ →
  renameStoreᵉ (singleRenameᵗ α) (⟰ᵉ Σ) ≡ Σ
renameStoreᵉ-single-suc-cancel α Σ =
  trans
    (renameStoreᵉ-compose suc (singleRenameᵗ α) Σ)
    (trans (renameStoreᵉ-cong (λ β → refl) Σ) (renameStoreᵉ-id Σ))

complement-renameᵉ :
  ∀ ρ {Π Σ : EffStore} →
  (d : Π ⊆ Σ) →
  renameStoreᵗ ρ (complement (eraseStore-incl d)) ≡
  complement (eraseStore-incl (renameStoreᵉ-incl ρ d))
complement-renameᵉ ρ []⊆ = refl
complement-renameᵉ ρ ((α , A) ∷ʳ⊆ d) =
  cong₂ _∷_
    (cong₂ _,_ refl (sym (erase-renameᵉ ρ A)))
    (complement-renameᵉ ρ d)
complement-renameᵉ ρ (refl ∷⊆ d) =
  complement-renameᵉ ρ d

complement-inclᵉ :
  ∀ {Π Σ Σ′ : EffStore} →
  (d : Π ⊆ Σ) →
  (e : Σ ⊆ Σ′) →
  complement (eraseStore-incl d) ⊆
  complement (eraseStore-incl (⊆-trans d e))
complement-inclᵉ []⊆ []⊆ = []⊆
complement-inclᵉ d ((α , A) ∷ʳ⊆ e) =
  (α , eraseᵉ A) ∷ʳ⊆ complement-inclᵉ d e
complement-inclᵉ ((α , A) ∷ʳ⊆ d) (refl ∷⊆ e) =
  refl ∷⊆ complement-inclᵉ d e
complement-inclᵉ (refl ∷⊆ d) (refl ∷⊆ e) =
  complement-inclᵉ d e

CastEndpoint-rename :
  ∀ ρ {Π c F A B} →
  CastEndpoint Π c F A B →
  CastEndpoint (renameStoreᵉ ρ Π) (renameᶜ ρ c)
    (renameᴱ ρ F) (renameᵉ ρ A) (renameᵉ ρ B)
CastEndpoint-rename ρ end-id = end-id
CastEndpoint-rename ρ (end-seq hp hq) =
  end-seq (CastEndpoint-rename ρ hp) (CastEndpoint-rename ρ hq)
CastEndpoint-rename ρ (end-fun {F = F} {E = E} {E′ = E′} hp hq incl) =
  end-fun
    (CastEndpoint-rename ρ hp)
    (CastEndpoint-rename ρ hq)
    incl′
  where
    eq :
      renameᴱ ρ (E′ ++ F) ≡
      renameᴱ ρ E′ ++ renameᴱ ρ F
    eq = renameᴱ-++ ρ E′ F

    incl′ :
      renameᴱ ρ E′ ++ renameᴱ ρ F ⊆ᵉ renameᴱ ρ E
    incl′ h =
      renameᴱ-mono ρ incl (subst (λ F → _ ∈ F) (sym eq) h)
CastEndpoint-rename ρ {Π = Π}
    (end-all {c = c} {G = G} {F = F} {A = A} {B = B} {E = E}
      {E′ = E′} hc castIncl tyIncl) =
  end-all
    (subst
      (λ Π′ → CastEndpoint Π′ (renameᶜ (extᵗ ρ) c)
        (renameᴱ (extᵗ ρ) G)
        (renameᵉ (extᵗ ρ) A) (renameᵉ (extᵗ ρ) B))
      (renameStoreᵉ-ext-suc-comm ρ Π)
      (CastEndpoint-rename (extᵗ ρ) hc))
    castIncl′
    tyIncl′
  where
    castIncl′ :
      drop0ᵉ (renameᴱ (extᵗ ρ) G) ⊆ᵉ renameᴱ ρ F
    castIncl′ h =
      renameᴱ-mono ρ castIncl
        (subst (λ H → _ ∈ H) (drop0ᵉ-rename ρ G) h)

    tyIncl′ :
      drop0ᵉ (renameᴱ (extᵗ ρ) E) ⊆ᵉ
      drop0ᵉ (renameᴱ (extᵗ ρ) E′)
    tyIncl′ h =
      subst
        (λ G → _ ∈ G)
        (sym (drop0ᵉ-rename ρ E′))
        (renameᴱ-mono ρ tyIncl
          (subst (λ G → _ ∈ G) (drop0ᵉ-rename ρ E) h))
CastEndpoint-rename ρ end-tag = end-tag
CastEndpoint-rename ρ end-untag = end-untag
CastEndpoint-rename ρ (end-seal h) = end-seal (∈-renameStoreᵉ ρ h)
CastEndpoint-rename ρ (end-unseal h) = end-unseal (∈-renameStoreᵉ ρ h)
CastEndpoint-rename ρ {Π = Π}
    (end-gen {c = c} {G = G} {F = F} {A = A} {B = B} hc incl) =
  end-gen
    (subst
      (λ A′ → CastEndpoint (⟰ᵉ (renameStoreᵉ ρ Π))
        (renameᶜ (extᵗ ρ) c) (renameᴱ (extᵗ ρ) G)
        A′ (renameᵉ (extᵗ ρ) B))
      (renameᵉ-ext-suc-comm ρ A)
      (subst
        (λ Π′ → CastEndpoint Π′ (renameᶜ (extᵗ ρ) c)
          (renameᴱ (extᵗ ρ) G)
          (renameᵉ (extᵗ ρ) (renameᵉ suc A))
          (renameᵉ (extᵗ ρ) B))
        (renameStoreᵉ-ext-suc-comm ρ Π)
        (CastEndpoint-rename (extᵗ ρ) hc)))
    incl′
  where
    incl′ :
      drop0ᵉ (renameᴱ (extᵗ ρ) G) ⊆ᵉ renameᴱ ρ F
    incl′ h =
      renameᴱ-mono ρ incl
        (subst (λ H → _ ∈ H) (drop0ᵉ-rename ρ G) h)
CastEndpoint-rename ρ {Π = Π}
    (end-inst {c = c} {G = G} {F = F} {A = A} {B = B} hc incl) =
  end-inst
    (subst
      (λ B′ → CastEndpoint ((zero , ty-star) ∷ ⟰ᵉ (renameStoreᵉ ρ Π))
        (renameᶜ (extᵗ ρ) c) (renameᴱ (extᵗ ρ) G)
        (renameᵉ (extᵗ ρ) A) B′)
      (renameᵉ-ext-suc-comm ρ B)
      (subst
        (λ Π′ → CastEndpoint Π′ (renameᶜ (extᵗ ρ) c)
          (renameᴱ (extᵗ ρ) G)
          (renameᵉ (extᵗ ρ) A) (renameᵉ (extᵗ ρ) (renameᵉ suc B)))
        (renameStoreᵉ-ext-suc-cons-comm ρ Π ty-star)
        (CastEndpoint-rename (extᵗ ρ) hc)))
    incl′
  where
    incl′ :
      drop0ᵉ (renameᴱ (extᵗ ρ) G) ⊆ᵉ renameᴱ ρ F
    incl′ h =
      renameᴱ-mono ρ incl
        (subst (λ H → _ ∈ H) (drop0ᵉ-rename ρ G) h)

renameCtxᵉ-ext-suc-comm :
  ∀ ρ Ξ →
  renameCtxᵉ (extᵗ ρ) (renameCtxᵉ suc Ξ) ≡
  renameCtxᵉ suc (renameCtxᵉ ρ Ξ)
renameCtxᵉ-ext-suc-comm ρ Ξ =
  trans
    (renameCtxᵉ-compose suc (extᵗ ρ) Ξ)
    (trans
      (renameCtxᵉ-cong env-eq Ξ)
      (sym (renameCtxᵉ-compose ρ suc Ξ)))
  where
    env-eq :
      ∀ α →
      extᵗ ρ (suc α) ≡ suc (ρ α)
    env-eq α = refl

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

------------------------------------------------------------------------
-- Type-variable renaming
------------------------------------------------------------------------

plainᵉ-rename :
  ∀ ρ A →
  plainᵉ (renameᵗ ρ A) ≡ renameᵉ ρ (plainᵉ A)
plainᵉ-rename ρ (＇ α) = refl
plainᵉ-rename ρ (‵ ι) = refl
plainᵉ-rename ρ ★ = refl
plainᵉ-rename ρ (A ⇒ B)
  rewrite plainᵉ-rename ρ A
        | plainᵉ-rename ρ B = refl
plainᵉ-rename ρ (`∀ A)
  rewrite plainᵉ-rename (extᵗ ρ) A = refl

plainᵉ-const-rename :
  ∀ ρ κ →
  plainᵉ (constTy κ) ≡ renameᵉ ρ (plainᵉ (constTy κ))
plainᵉ-const-rename ρ κ =
  trans (cong plainᵉ (constTy-renameᵗ ρ κ))
        (plainᵉ-rename ρ (constTy κ))

plainᵉ-wf :
  ∀ {Δ A} →
  WfTy ⌊ Δ ⌋ A →
  WfEffTy Δ (plainᵉ A)
plainᵉ-wf (wfVar α<Δ) = wf-eff-var α<Δ
plainᵉ-wf wfBase = wf-eff-base
plainᵉ-wf wf★ = wf-eff-star
plainᵉ-wf (wf⇒ hA hB) =
  wf-eff-fun (plainᵉ-wf hA) WfEffect-[] (plainᵉ-wf hB)
plainᵉ-wf (wf∀ hA) =
  wf-eff-all WfEffect-[] (plainᵉ-wf hA)

plainᵉ-const-wf :
  ∀ {Δ} κ →
  WfEffTy Δ (plainᵉ (constTy κ))
plainᵉ-const-wf (κℕ n) = wf-eff-base

typing-wf :
  ∀ {Δ Σ Ξ M A E} →
  EffCtxWf Δ Ξ →
  Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ E →
  WfEffTy Δ A × WfEffect Δ E
typing-wf wfΞ (eff-var hΞ) = wfΞ hΞ
typing-wf wfΞ (eff-lam hA hE hM)
    with typing-wf (effCtxWf-∷ hA hE wfΞ) hM
typing-wf wfΞ (eff-lam hA hE hM) | hB , hBody =
  wf-eff-fun hA hE hB , hBody
typing-wf wfΞ (eff-app hL hM EM⊆Earg)
    with typing-wf wfΞ hL | typing-wf wfΞ hM
typing-wf wfΞ (eff-app hL hM EM⊆Earg)
    | wf-eff-fun hA hEarg hB , hEL | hMty , hEM =
  hB , WfEffect-++ hEL hEM
typing-wf wfΞ (eff-tylam vM hM)
    with typing-wf (EffCtxWf-suc wfΞ) hM
typing-wf wfΞ (eff-tylam vM hM) | hA , hE =
  wf-eff-all hE hA , WfEffect-drop0 hE
typing-wf wfΞ (eff-tyapp hL hα α∉E)
    with typing-wf wfΞ hL
typing-wf wfΞ (eff-tyapp hL hα α∉E)
    | wf-eff-all hEbody hB , hE =
  WfEffTy-open-ordinary hα hB ,
  WfEffect-++ hE (WfEffect-drop0 hEbody)
typing-wf wfΞ (eff-nu hAᵉ eqA hB hN)
    with typing-wf (EffCtxWf-suc wfΞ) hN
typing-wf wfΞ (eff-nu hAᵉ eqA hB hN) | hNty , hE =
  hB , WfEffect-drop0 hE
typing-wf wfΞ (eff-const κ) =
  plainᵉ-const-wf κ , WfEffect-[]
typing-wf wfΞ (eff-prim hL op hM)
    with typing-wf wfΞ hL | typing-wf wfΞ hM
typing-wf wfΞ (eff-prim hL op hM) | hLty , hEL | hMty , hEM =
  wf-eff-base , WfEffect-++ hEL hEM
typing-wf wfΞ (eff-cast d c⊢ roles side hS hB endpoint hM)
    with typing-wf wfΞ hM
typing-wf wfΞ (eff-cast d c⊢ roles side hS hB endpoint hM) | hA , hE =
  hB , WfEffect-++ hE hS
typing-wf wfΞ (eff-blame hA) = hA , WfEffect-[]
typing-wf wfΞ (eff-sub hM E⊆F hF)
    with typing-wf wfΞ hM
typing-wf wfΞ (eff-sub hM E⊆F hF) | hA , hE =
  hA , hF

typing-renameᵀ :
  ∀ {Δ Δ′ Σ Ξ M A E ρ} →
  TyRenameWf ⌊ Δ ⌋ ⌊ Δ′ ⌋ ρ →
  RuntimeRenameWf Δ Δ′ ρ →
  RuntimeRenameInjective Δ ρ →
  EffCtxWf Δ Ξ →
  Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ E →
  Δ′ ∣ renameStoreᵉ ρ Σ ∣ renameCtxᵉ ρ Ξ
    ⊢ renameᵗᵐ ρ M ⦂ renameᵉ ρ A ▷ renameᴱ ρ E
typing-renameᵀ hTy hρ rinj wfΞ (eff-var hΞ) =
  eff-var (lookup-renameCtxᵉ _ hΞ)
typing-renameᵀ hTy hρ rinj wfΞ (eff-lam hA hE hM) =
  eff-lam
    (WfEffTy-rename hTy hρ hA)
    (WfEffect-rename hρ hE)
    (typing-renameᵀ hTy hρ rinj (effCtxWf-∷ hA hE wfΞ) hM)
typing-renameᵀ {ρ = ρ} hTy hρ rinj wfΞ
    (eff-app {L = L} {M = M} {B = B} {EL = EL} {EM = EM}
      hL hM EM⊆Earg) =
  subst
    (λ F → _ ∣ _ ∣ _
      ⊢ renameᵗᵐ ρ L · renameᵗᵐ ρ M ⦂ renameᵉ ρ B ▷ F)
    (sym (renameᴱ-++ ρ EL EM))
    (eff-app
      (typing-renameᵀ hTy hρ rinj wfΞ hL)
      (typing-renameᵀ hTy hρ rinj wfΞ hM)
      (renameᴱ-mono ρ EM⊆Earg))
typing-renameᵀ {Δ′ = Δ′} {Σ = Σ} {Ξ = Ξ} {ρ = ρ}
    hTy hρ rinj wfΞ (eff-tylam {M = M} {A = A} {E = E} vM hM) =
  subst
    (λ F → Δ′ ∣ renameStoreᵉ ρ Σ ∣ renameCtxᵉ ρ Ξ
      ⊢ Λ renameᵗᵐ (extᵗ ρ) M
      ⦂ renameᵉ ρ (ty-all E A) ▷ F)
    (drop0ᵉ-rename ρ E)
    (eff-tylam
      (renameᵗᵐ-preserves-Value (extᵗ ρ) vM)
      (subst
        (λ Ξ′ → ordinary ∷ Δ′ ∣ ⟰ᵉ (renameStoreᵉ ρ Σ) ∣ Ξ′
          ⊢ renameᵗᵐ (extᵗ ρ) M
          ⦂ renameᵉ (extᵗ ρ) A ▷ renameᴱ (extᵗ ρ) E)
        (renameCtxᵉ-ext-suc-comm ρ Ξ)
        (subst
          (λ Σ′ → ordinary ∷ Δ′ ∣ Σ′
            ∣ renameCtxᵉ (extᵗ ρ) (renameCtxᵉ suc Ξ)
            ⊢ renameᵗᵐ (extᵗ ρ) M
            ⦂ renameᵉ (extᵗ ρ) A ▷ renameᴱ (extᵗ ρ) E)
          (renameStoreᵉ-ext-suc-comm ρ Σ)
          (typing-renameᵀ
            (TyRenameWf-ext hTy)
            (RuntimeRenameWf-ext ordinary hρ)
            (RuntimeRenameInjective-ext ordinary rinj)
            (EffCtxWf-suc wfΞ)
            hM))))
typing-renameᵀ {ρ = ρ} hTy hρ rinj wfΞ
    (eff-tyapp {L = L} {B = B} {α = α} {E = E}
      {Ebody = Ebody} hL hα α∉E) =
  subst
    (λ T → _ ∣ _ ∣ _ ⊢ renameᵗᵐ ρ L • ρ α ⦂ T
      ▷ renameᴱ ρ (E ++ drop0ᵉ Ebody))
    (sym (renameᵉ-open ρ B α))
    (subst
      (λ F → _ ∣ _ ∣ _ ⊢ renameᵗᵐ ρ L • ρ α
        ⦂ renameᵉ (extᵗ ρ) B [ ρ α ]ᵉ ▷ F)
      (sym eff-eq)
      (eff-tyapp
        (typing-renameᵀ hTy hρ rinj wfΞ hL)
        (hρ hα)
        (∉-renameᴱ-runtime rinj hE hα α∉E)))
  where
    hE : WfEffect _ E
    hE with typing-wf wfΞ hL
    hE | hAll , hEff = hEff

    eff-eq :
      renameᴱ ρ (E ++ drop0ᵉ Ebody) ≡
      renameᴱ ρ E ++ drop0ᵉ (renameᴱ (extᵗ ρ) Ebody)
    eff-eq =
      trans
        (renameᴱ-++ ρ E (drop0ᵉ Ebody))
        (cong (λ F → renameᴱ ρ E ++ F)
          (sym (drop0ᵉ-rename ρ Ebody)))
typing-renameᵀ {Δ′ = Δ′} {Σ = Σ} {Ξ = Ξ} {ρ = ρ}
    hTy hρ rinj wfΞ
    (eff-nu {N = N} {A = A} {Aᵉ = Aᵉ} {B = B} {E = E}
      hAᵉ eqA hB hN) =
  subst
    (λ F → Δ′ ∣ renameStoreᵉ ρ Σ ∣ renameCtxᵉ ρ Ξ
      ⊢ ν (renameᵗ ρ A) (renameᵗᵐ (extᵗ ρ) N)
      ⦂ renameᵉ ρ B ▷ F)
    (drop0ᵉ-rename ρ E)
    (eff-nu
      (WfEffTy-rename hTy hρ hAᵉ)
      (trans (erase-renameᵉ ρ Aᵉ) (cong (renameᵗ ρ) eqA))
      (WfEffTy-rename hTy hρ hB)
      (subst
        (λ T → runtime ∷ Δ′
          ∣ (zero , renameᵉ suc (renameᵉ ρ Aᵉ))
              ∷ ⟰ᵉ (renameStoreᵉ ρ Σ)
          ∣ renameCtxᵉ suc (renameCtxᵉ ρ Ξ)
          ⊢ renameᵗᵐ (extᵗ ρ) N ⦂ T ▷ renameᴱ (extᵗ ρ) E)
        (renameᵉ-ext-suc-comm ρ B)
        (subst
          (λ Ξ′ → runtime ∷ Δ′
            ∣ (zero , renameᵉ suc (renameᵉ ρ Aᵉ))
                ∷ ⟰ᵉ (renameStoreᵉ ρ Σ)
            ∣ Ξ′
            ⊢ renameᵗᵐ (extᵗ ρ) N
            ⦂ renameᵉ (extᵗ ρ) (renameᵉ suc B)
            ▷ renameᴱ (extᵗ ρ) E)
          (renameCtxᵉ-ext-suc-comm ρ Ξ)
          (subst
            (λ Σ′ → runtime ∷ Δ′ ∣ Σ′
              ∣ renameCtxᵉ (extᵗ ρ) (renameCtxᵉ suc Ξ)
              ⊢ renameᵗᵐ (extᵗ ρ) N
              ⦂ renameᵉ (extᵗ ρ) (renameᵉ suc B)
              ▷ renameᴱ (extᵗ ρ) E)
            (renameStoreᵉ-ext-suc-cons-comm ρ Σ Aᵉ)
            (typing-renameᵀ
              (TyRenameWf-ext hTy)
              (RuntimeRenameWf-ext runtime hρ)
              (RuntimeRenameInjective-ext runtime rinj)
              (EffCtxWf-suc wfΞ)
              hN)))))
typing-renameᵀ {ρ = ρ} hTy hρ rinj wfΞ (eff-const κ) =
  subst
    (λ T → _ ∣ _ ∣ _ ⊢ $ κ ⦂ T ▷ [])
    (plainᵉ-const-rename ρ κ)
    (eff-const κ)
typing-renameᵀ {ρ = ρ} hTy hρ rinj wfΞ
    (eff-prim {L = L} {M = M} {EL = EL} {EM = EM} hL op hM) =
  subst
    (λ F → _ ∣ _ ∣ _
      ⊢ renameᵗᵐ ρ L ⊕[ op ] renameᵗᵐ ρ M
      ⦂ ty-base `ℕ ▷ F)
    (sym (renameᴱ-++ ρ EL EM))
    (eff-prim
      (typing-renameᵀ hTy hρ rinj wfΞ hL)
      op
      (typing-renameᵀ hTy hρ rinj wfΞ hM))
typing-renameᵀ {ρ = ρ} hTy hρ rinj wfΞ
    (eff-cast {M = M} {A = A} {B = B} {c = c} {Π = Π}
      {E = E} {F = F} d c⊢ roles side hF hB endpoint hM) =
  subst
    (λ F → _ ∣ _ ∣ _ ⊢ renameᵗᵐ ρ M ⟨ renameᶜ ρ c ⟩
      ⦂ renameᵉ ρ B ▷ F)
    (sym eff-eq)
    (eff-cast
      (renameStoreᵉ-incl ρ d)
      c⊢′
      (CoercionRoles-rename hρ roles)
      (SealSideEffect-rename ρ {c = c} {Π = Π} {F = F} side)
      (WfEffect-rename hρ hF)
      (WfEffTy-rename hTy hρ hB)
      (CastEndpoint-rename ρ endpoint)
      (typing-renameᵀ hTy hρ rinj wfΞ hM))
  where
    c⊢′ :
      _ ∣ complement (eraseStore-incl (renameStoreᵉ-incl ρ d))
        ∣ eraseStoreᵉ (renameStoreᵉ ρ Π)
        ⊢ renameᶜ ρ c ∶ eraseᵉ (renameᵉ ρ A) =⇒ eraseᵉ (renameᵉ ρ B)
    c⊢′ =
      subst
        (λ T → _ ∣ complement (eraseStore-incl (renameStoreᵉ-incl ρ d))
          ∣ eraseStoreᵉ (renameStoreᵉ ρ Π)
          ⊢ renameᶜ ρ c ∶ T =⇒ eraseᵉ (renameᵉ ρ B))
        (sym (erase-renameᵉ ρ A))
        (subst
          (λ T → _ ∣ complement (eraseStore-incl (renameStoreᵉ-incl ρ d))
            ∣ eraseStoreᵉ (renameStoreᵉ ρ Π)
            ⊢ renameᶜ ρ c ∶ renameᵗ ρ (eraseᵉ A) =⇒ T)
          (sym (erase-renameᵉ ρ B))
          (subst
            (λ Σ′ → _ ∣ Σ′ ∣ eraseStoreᵉ (renameStoreᵉ ρ Π)
              ⊢ renameᶜ ρ c
              ∶ renameᵗ ρ (eraseᵉ A) =⇒ renameᵗ ρ (eraseᵉ B))
            (complement-renameᵉ ρ d)
            (subst
              (λ Π′ → _ ∣ renameStoreᵗ ρ (complement (eraseStore-incl d))
                ∣ Π′
                ⊢ renameᶜ ρ c
                ∶ renameᵗ ρ (eraseᵉ A) =⇒ renameᵗ ρ (eraseᵉ B))
              (sym (eraseStore-renameᵉ ρ Π))
              (coercion-renameᵗ hTy c⊢))))

    eff-eq :
      renameᴱ ρ (E ++ F) ≡ renameᴱ ρ E ++ renameᴱ ρ F
    eff-eq = renameᴱ-++ ρ E F
typing-renameᵀ hTy hρ rinj wfΞ (eff-blame hA) =
  eff-blame (WfEffTy-rename hTy hρ hA)
typing-renameᵀ {ρ = ρ} hTy hρ rinj wfΞ (eff-sub hM E⊆F hF) =
  eff-sub
    (typing-renameᵀ hTy hρ rinj wfΞ hM)
    (renameᴱ-mono ρ E⊆F)
    (WfEffect-rename hρ hF)

typing-renameᵀ-suc :
  ∀ {Δ Σ Ξ M A E r} →
  EffCtxWf Δ Ξ →
  Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ E →
  r ∷ Δ ∣ renameStoreᵉ suc Σ ∣ renameCtxᵉ suc Ξ
    ⊢ renameᵗᵐ suc M ⦂ renameᵉ suc A ▷ renameᴱ suc E
typing-renameᵀ-suc =
  typing-renameᵀ
    TyRenameWf-suc
    RuntimeRenameWf-suc
    RuntimeRenameInjective-suc

typing-open-existingᵀ :
  ∀ {Δ Σ Ξ M A E α} →
  EffCtxWf Δ Ξ →
  Δ ∋ᵣ α ⦂ runtime →
  ordinary ∷ Δ ∣ ⟰ᵉ Σ ∣ renameCtxᵉ suc Ξ ⊢ M ⦂ A ▷ E →
  Δ ∣ Σ ∣ Ξ ⊢ M [ α ]ᵀ ⦂ A [ α ]ᵉ ▷ openᴱ E α
typing-open-existingᵀ {Σ = Σ} {Ξ = Ξ} {M = M} {A = A} {E = E}
    {α = α} wfΞ hα hM =
  subst
    (λ Ξ′ → _ ∣ Σ ∣ Ξ′ ⊢ M [ α ]ᵀ ⦂ A [ α ]ᵉ ▷ openᴱ E α)
    (renameCtxᵉ-single-suc-cancel α Ξ)
    (subst
      (λ Σ′ → _ ∣ Σ′ ∣ renameCtxᵉ (singleRenameᵗ α) (renameCtxᵉ suc Ξ)
        ⊢ M [ α ]ᵀ ⦂ A [ α ]ᵉ ▷ openᴱ E α)
      (renameStoreᵉ-single-suc-cancel α Σ)
      (typing-renameᵀ
        (singleRenameᵗ-Wf-role hα)
        RuntimeRenameWf-open-ordinary
        RuntimeRenameInjective-open-ordinary
        (EffCtxWf-suc {r = ordinary} wfΞ)
        hM))

typing-open-existing-dropᵀ :
  ∀ {Δ Σ Ξ M A E α} →
  EffCtxWf Δ Ξ →
  Δ ∋ᵣ α ⦂ runtime →
  ordinary ∷ Δ ∣ ⟰ᵉ Σ ∣ renameCtxᵉ suc Ξ ⊢ M ⦂ A ▷ E →
  Δ ∣ Σ ∣ Ξ ⊢ M [ α ]ᵀ ⦂ A [ α ]ᵉ ▷ drop0ᵉ E
typing-open-existing-dropᵀ wfΞ hα hM
    with typing-wf (EffCtxWf-suc {r = ordinary} wfΞ) hM
typing-open-existing-dropᵀ wfΞ hα hM | hA , hE =
  eff-sub
    (typing-open-existingᵀ wfΞ hα hM)
    (openᴱ-drop0-ordinary hE)
    (WfEffect-drop0 hE)

typing-renameˣ :
  ∀ {Δ Σ Ξ Ξ′ M A E ρ} →
  RenameEffWf Ξ Ξ′ ρ →
  Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ E →
  Δ ∣ Σ ∣ Ξ′ ⊢ renameˣᵐ ρ M ⦂ A ▷ E
typing-renameˣ hρ (eff-var hΞ) = eff-var (hρ hΞ)
typing-renameˣ hρ (eff-lam hA hE hM) =
  eff-lam hA hE (typing-renameˣ (RenameEffWf-ext hρ) hM)
typing-renameˣ hρ (eff-app hL hM EM⊆Earg) =
  eff-app (typing-renameˣ hρ hL) (typing-renameˣ hρ hM) EM⊆Earg
typing-renameˣ hρ (eff-tylam vM hM) =
  eff-tylam
    (renameˣᵐ-preserves-Value _ vM)
    (typing-renameˣ (RenameEffWf-renameCtxᵉ suc hρ) hM)
typing-renameˣ hρ (eff-tyapp hL hα α∉E) =
  eff-tyapp (typing-renameˣ hρ hL) hα α∉E
typing-renameˣ hρ (eff-nu hAᵉ eqA hB hN) =
  eff-nu hAᵉ eqA hB (typing-renameˣ (RenameEffWf-renameCtxᵉ suc hρ) hN)
typing-renameˣ hρ (eff-const κ) = eff-const κ
typing-renameˣ hρ (eff-prim hL op hM) =
  eff-prim (typing-renameˣ hρ hL) op (typing-renameˣ hρ hM)
typing-renameˣ hρ (eff-cast d c⊢ roles side hS hB endpoint hM) =
  eff-cast d c⊢ roles side hS hB endpoint (typing-renameˣ hρ hM)
typing-renameˣ hρ (eff-blame hA) = eff-blame hA
typing-renameˣ hρ (eff-sub hM E⊆F hF) =
  eff-sub (typing-renameˣ hρ hM) E⊆F hF

typing-renameˣ-shift :
  ∀ {Δ Σ Ξ M A B E F} →
  Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ E →
  Δ ∣ Σ ∣ ((B , F) ∷ Ξ) ⊢ renameˣᵐ suc M ⦂ A ▷ E
typing-renameˣ-shift hM =
  typing-renameˣ (λ h → Sᵉ h) hM

------------------------------------------------------------------------
-- Type-context and store weakening
------------------------------------------------------------------------

typing-store-weaken :
  ∀ {Δ Σ Σ′ Ξ M A E} →
  Σ ⊆ Σ′ →
  Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ E →
  Δ ∣ Σ′ ∣ Ξ ⊢ M ⦂ A ▷ E
typing-store-weaken incl (eff-var hΞ) = eff-var hΞ
typing-store-weaken incl (eff-lam hA hE hM) =
  eff-lam
    hA
    hE
    (typing-store-weaken incl hM)
typing-store-weaken incl (eff-app hL hM EM⊆Earg) =
  eff-app
    (typing-store-weaken incl hL)
    (typing-store-weaken incl hM)
    EM⊆Earg
typing-store-weaken incl (eff-tylam vM hM) =
  eff-tylam vM
    (typing-store-weaken (renameStoreᵉ-incl suc incl) hM)
typing-store-weaken incl (eff-tyapp hL hα α∉E) =
  eff-tyapp
    (typing-store-weaken incl hL)
    hα
    α∉E
typing-store-weaken incl (eff-nu hAᵉ eqA hB hN) =
  eff-nu
    hAᵉ
    eqA
    hB
    (typing-store-weaken (EffStoreIncl-cons (renameStoreᵉ-incl suc incl)) hN)
typing-store-weaken incl (eff-const κ) = eff-const κ
typing-store-weaken incl (eff-prim hL op hM) =
  eff-prim
    (typing-store-weaken incl hL)
    op
    (typing-store-weaken incl hM)
typing-store-weaken incl (eff-cast d c⊢ roles side hS hB endpoint hM) =
  eff-cast
    (⊆-trans d incl)
    (coercion-weaken ≤-refl (complement-inclᵉ d incl) StoreIncl-refl c⊢)
    roles
    side
    hS
    hB
    endpoint
    (typing-store-weaken incl hM)
typing-store-weaken incl (eff-blame hA) = eff-blame hA
typing-store-weaken incl (eff-sub hM E⊆F hF) =
  eff-sub (typing-store-weaken incl hM) E⊆F hF

------------------------------------------------------------------------
-- Term substitution environments
------------------------------------------------------------------------

record SubstEffWf
    (Δ : RoleCtx) (Σ : EffStore) (Ξ Ξ′ : EffCtx) (σ : Substˣ) :
    Set₁ where
  constructor substEffWf
  field
    targetWf : EffCtxWf Δ Ξ′
    typed :
      ∀ {x A E} →
      Ξ ∋ x ⦂ A ▷ E →
      Δ ∣ Σ ∣ Ξ′ ⊢ σ x ⦂ A ▷ E

open SubstEffWf public

SubstEffWf-exts :
  ∀ {Δ Σ Ξ Ξ′ A E σ} →
  WfEffTy Δ A →
  WfEffect Δ E →
  SubstEffWf Δ Σ Ξ Ξ′ σ →
  SubstEffWf Δ Σ ((A , E) ∷ Ξ) ((A , E) ∷ Ξ′) (extˢˣ σ)
SubstEffWf-exts {A = A} {E = E} {σ = σ} hA hE hσ =
  substEffWf
    (effCtxWf-∷ hA hE (targetWf hσ))
    typed′
  where
    typed′ :
      ∀ {x B F} →
      ((A , E) ∷ _) ∋ x ⦂ B ▷ F →
      _ ∣ _ ∣ _ ⊢ extˢˣ σ x ⦂ B ▷ F
    typed′ Zᵉ = eff-var Zᵉ
    typed′ (Sᵉ h) = typing-renameˣ-shift (typed hσ h)

SubstEffWf-⇑ :
  ∀ {Δ Σ Ξ Ξ′ σ} →
  SubstEffWf Δ Σ Ξ Ξ′ σ →
  SubstEffWf
    (ordinary ∷ Δ)
    (⟰ᵉ Σ)
    (renameCtxᵉ suc Ξ)
    (renameCtxᵉ suc Ξ′)
    (↑ᵗᵐ σ)
SubstEffWf-⇑ {Ξ = Ξ} {σ = σ} hσ =
  substEffWf
    (EffCtxWf-suc {r = ordinary} (targetWf hσ))
    typed′
  where
    typed′ :
      ∀ {x A E} →
      renameCtxᵉ suc Ξ ∋ x ⦂ A ▷ E →
      _ ∣ _ ∣ _ ⊢ ↑ᵗᵐ σ x ⦂ A ▷ E
    typed′ h with lookup-renameCtxᵉ-inv suc Ξ h
    typed′ h | A , E , hΞ , refl , refl =
      typing-renameᵀ-suc {r = ordinary} (targetWf hσ) (typed hσ hΞ)

SubstEffWf-⇑ν :
  ∀ {Δ Σ Ξ Ξ′ σ A} →
  SubstEffWf Δ Σ Ξ Ξ′ σ →
  SubstEffWf
    (runtime ∷ Δ)
    ((zero , renameᵉ suc A) ∷ ⟰ᵉ Σ)
    (renameCtxᵉ suc Ξ)
    (renameCtxᵉ suc Ξ′)
    (↑ᵗᵐ σ)
SubstEffWf-⇑ν {Ξ = Ξ} {σ = σ} hσ =
  substEffWf
    (EffCtxWf-suc {r = runtime} (targetWf hσ))
    typed′
  where
    typed′ :
      ∀ {x B E} →
      renameCtxᵉ suc Ξ ∋ x ⦂ B ▷ E →
      _ ∣ _ ∣ _ ⊢ ↑ᵗᵐ σ x ⦂ B ▷ E
    typed′ h with lookup-renameCtxᵉ-inv suc Ξ h
    typed′ h | B , E , hΞ , refl , refl =
      typing-store-weaken EffStoreIncl-drop
        (typing-renameᵀ-suc {r = runtime} (targetWf hσ) (typed hσ hΞ))

typing-substˣ :
  ∀ {Δ Σ Ξ Ξ′ M A E σ} →
  SubstEffWf Δ Σ Ξ Ξ′ σ →
  Δ ∣ Σ ∣ Ξ ⊢ M ⦂ A ▷ E →
  Δ ∣ Σ ∣ Ξ′ ⊢ substˣᵐ σ M ⦂ A ▷ E
typing-substˣ hσ (eff-var hΞ) = typed hσ hΞ
typing-substˣ hσ (eff-lam hA hE hM) =
  eff-lam hA hE (typing-substˣ (SubstEffWf-exts hA hE hσ) hM)
typing-substˣ hσ (eff-app hL hM EM⊆Earg) =
  eff-app (typing-substˣ hσ hL) (typing-substˣ hσ hM) EM⊆Earg
typing-substˣ hσ (eff-tylam vM hM) =
  eff-tylam
    (substˣᵐ-preserves-Value _ vM)
    (typing-substˣ (SubstEffWf-⇑ hσ) hM)
typing-substˣ hσ (eff-tyapp hL hα α∉E) =
  eff-tyapp (typing-substˣ hσ hL) hα α∉E
typing-substˣ hσ (eff-nu hAᵉ eqA hB hN) =
  eff-nu hAᵉ eqA hB (typing-substˣ (SubstEffWf-⇑ν hσ) hN)
typing-substˣ hσ (eff-const κ) = eff-const κ
typing-substˣ hσ (eff-prim hL op hM) =
  eff-prim (typing-substˣ hσ hL) op (typing-substˣ hσ hM)
typing-substˣ hσ (eff-cast d c⊢ roles side hS hB endpoint hM) =
  eff-cast d c⊢ roles side hS hB endpoint (typing-substˣ hσ hM)
typing-substˣ hσ (eff-blame hA) = eff-blame hA
typing-substˣ hσ (eff-sub hM E⊆F hF) =
  eff-sub (typing-substˣ hσ hM) E⊆F hF

singleSubstEffWf :
  ∀ {Δ Σ Ξ A E V EV} →
  EffCtxWf Δ Ξ →
  Δ ∣ Σ ∣ Ξ ⊢ V ⦂ A ▷ EV →
  EV ⊆ᵉ E →
  WfEffect Δ E →
  SubstEffWf Δ Σ ((A , E) ∷ Ξ) Ξ (singleEnv V)
singleSubstEffWf {A = A} {E = E} {V = V} wfΞ hV EV⊆E hE =
  substEffWf wfΞ typed′
  where
    typed′ :
      ∀ {x B F} →
      ((A , E) ∷ _) ∋ x ⦂ B ▷ F →
      _ ∣ _ ∣ _ ⊢ singleEnv V x ⦂ B ▷ F
    typed′ Zᵉ = eff-sub hV EV⊆E hE
    typed′ (Sᵉ h) = eff-var h

typing-single-subst :
  ∀ {Δ Σ Ξ N V A B Earg Ebody EV} →
  EffCtxWf Δ Ξ →
  Δ ∣ Σ ∣ ((A , Earg) ∷ Ξ) ⊢ N ⦂ B ▷ Ebody →
  Δ ∣ Σ ∣ Ξ ⊢ V ⦂ A ▷ EV →
  EV ⊆ᵉ Earg →
  WfEffect Δ Earg →
  Δ ∣ Σ ∣ Ξ ⊢ N [ V ] ⦂ B ▷ Ebody
typing-single-subst wfΞ hN hV EV⊆Earg hEarg =
  typing-substˣ (singleSubstEffWf wfΞ hV EV⊆Earg hEarg) hN
