module proof.TypeInCoercionSubst where

-- File Charter:
--   * Type-variable renaming properties for GTPLC coercions.
--   * Preserves inertness and coercion typing under store weakening and
--     type renaming, and derives endpoint well-formedness.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import TyStore
open import Coercions
open import proof.TypeInTypeSubst
open import proof.TyStore

------------------------------------------------------------------------
-- Inert coercions and renaming algebra
------------------------------------------------------------------------

renameᶜ-preserves-Inert : ∀ ρ {c}
  → Inert c
  → Inert (renameᶜ ρ c)
renameᶜ-preserves-Inert ρ (G !) = renameᵍ ρ G !
renameᶜ-preserves-Inert ρ (seal α) = seal (ρ α)
renameᶜ-preserves-Inert ρ (c ↦ d) = renameᶜ ρ c ↦ renameᶜ ρ d
renameᶜ-preserves-Inert ρ (`∀ c) = `∀ (renameᶜ (extᵗ ρ) c)
renameᶜ-preserves-Inert ρ (gen c) = gen (renameᶜ (extᵗ ρ) c)

renameᶜ-cong : ∀ {ρ ψ}
  → (∀ X → ρ X ≡ ψ X)
  → ∀ c
  → renameᶜ ρ c ≡ renameᶜ ψ c
renameᶜ-cong eq id = refl
renameᶜ-cong eq error = refl
renameᶜ-cong eq (p ︔ q) =
  cong₂ _︔_ (renameᶜ-cong eq p) (renameᶜ-cong eq q)
renameᶜ-cong eq (p ↦ q) =
  cong₂ _↦_ (renameᶜ-cong eq p) (renameᶜ-cong eq q)
renameᶜ-cong eq (`∀ p) =
  cong `∀ (renameᶜ-cong ext-eq p)
  where
    ext-eq : ∀ X → extᵗ _ X ≡ extᵗ _ X
    ext-eq zero = refl
    ext-eq (suc X) = cong suc (eq X)
renameᶜ-cong eq (G !) = cong _! (renameᵍ-cong eq G)
renameᶜ-cong eq (G ？) = cong _？ (renameᵍ-cong eq G)
renameᶜ-cong eq (seal α) = cong seal (eq α)
renameᶜ-cong eq (unseal α) = cong unseal (eq α)
renameᶜ-cong eq (gen p) =
  cong gen (renameᶜ-cong ext-eq p)
  where
    ext-eq : ∀ X → extᵗ _ X ≡ extᵗ _ X
    ext-eq zero = refl
    ext-eq (suc X) = cong suc (eq X)
renameᶜ-cong eq (inst p) =
  cong inst (renameᶜ-cong ext-eq p)
  where
    ext-eq : ∀ X → extᵗ _ X ≡ extᵗ _ X
    ext-eq zero = refl
    ext-eq (suc X) = cong suc (eq X)

renameᶜ-id : ∀ c
  → renameᶜ (λ X → X) c ≡ c
renameᶜ-id id = refl
renameᶜ-id error = refl
renameᶜ-id (p ︔ q) = cong₂ _︔_ (renameᶜ-id p) (renameᶜ-id q)
renameᶜ-id (p ↦ q) = cong₂ _↦_ (renameᶜ-id p) (renameᶜ-id q)
renameᶜ-id (`∀ p) =
  cong `∀ (trans (renameᶜ-cong ext-id p) (renameᶜ-id p))
  where
    ext-id : ∀ X → extᵗ (λ Y → Y) X ≡ X
    ext-id zero = refl
    ext-id (suc X) = refl
renameᶜ-id (G !) = cong _! (renameᵍ-id G)
renameᶜ-id (G ？) = cong _？ (renameᵍ-id G)
renameᶜ-id (seal α) = refl
renameᶜ-id (unseal α) = refl
renameᶜ-id (gen p) =
  cong gen (trans (renameᶜ-cong ext-id p) (renameᶜ-id p))
  where
    ext-id : ∀ X → extᵗ (λ Y → Y) X ≡ X
    ext-id zero = refl
    ext-id (suc X) = refl
renameᶜ-id (inst p) =
  cong inst (trans (renameᶜ-cong ext-id p) (renameᶜ-id p))
  where
    ext-id : ∀ X → extᵗ (λ Y → Y) X ≡ X
    ext-id zero = refl
    ext-id (suc X) = refl

renameᶜ-compose : ∀ ρ ψ c
  → renameᶜ ψ (renameᶜ ρ c) ≡ renameᶜ (λ X → ψ (ρ X)) c
renameᶜ-compose ρ ψ id = refl
renameᶜ-compose ρ ψ error = refl
renameᶜ-compose ρ ψ (p ︔ q) =
  cong₂ _︔_ (renameᶜ-compose ρ ψ p) (renameᶜ-compose ρ ψ q)
renameᶜ-compose ρ ψ (p ↦ q) =
  cong₂ _↦_ (renameᶜ-compose ρ ψ p) (renameᶜ-compose ρ ψ q)
renameᶜ-compose ρ ψ (`∀ p) =
  cong `∀
    (trans (renameᶜ-compose (extᵗ ρ) (extᵗ ψ) p)
      (renameᶜ-cong ext-compose p))
  where
    ext-compose : ∀ X
      → extᵗ ψ (extᵗ ρ X) ≡ extᵗ (λ Y → ψ (ρ Y)) X
    ext-compose zero = refl
    ext-compose (suc X) = refl
renameᶜ-compose ρ ψ (G !) = cong _! (renameᵍ-compose ρ ψ G)
renameᶜ-compose ρ ψ (G ？) = cong _？ (renameᵍ-compose ρ ψ G)
renameᶜ-compose ρ ψ (seal α) = refl
renameᶜ-compose ρ ψ (unseal α) = refl
renameᶜ-compose ρ ψ (gen p) =
  cong gen
    (trans (renameᶜ-compose (extᵗ ρ) (extᵗ ψ) p)
      (renameᶜ-cong ext-compose p))
  where
    ext-compose : ∀ X
      → extᵗ ψ (extᵗ ρ X) ≡ extᵗ (λ Y → ψ (ρ Y)) X
    ext-compose zero = refl
    ext-compose (suc X) = refl
renameᶜ-compose ρ ψ (inst p) =
  cong inst
    (trans (renameᶜ-compose (extᵗ ρ) (extᵗ ψ) p)
      (renameᶜ-cong ext-compose p))
  where
    ext-compose : ∀ X
      → extᵗ ψ (extᵗ ρ X) ≡ extᵗ (λ Y → ψ (ρ Y)) X
    ext-compose zero = refl
    ext-compose (suc X) = refl

renameᶜ-left-inverse : ∀ {ρ ψ}
  → RenameLeftInverse ρ ψ
  → ∀ c
  → renameᶜ ψ (renameᶜ ρ c) ≡ c
renameᶜ-left-inverse {ρ = ρ} {ψ = ψ} inv c =
  trans (renameᶜ-compose ρ ψ c)
    (trans (renameᶜ-cong inv c) (renameᶜ-id c))

open0-ext-suc-cancelᶜ : ∀ c
  → renameᶜ (singleRenameᵗ zero) (renameᶜ (extᵗ suc) c) ≡ c
open0-ext-suc-cancelᶜ =
  renameᶜ-left-inverse open0-ext-suc-inv

renameᶜ-ext-suc-comm : ∀ ρ c
  → renameᶜ (extᵗ ρ) (⇑ᶜ c) ≡ ⇑ᶜ (renameᶜ ρ c)
renameᶜ-ext-suc-comm ρ c =
  trans (renameᶜ-compose suc (extᵗ ρ) c)
    (trans (renameᶜ-cong commute c)
      (sym (renameᶜ-compose ρ suc c)))
  where
    commute : ∀ X → extᵗ ρ (suc X) ≡ suc (ρ X)
    commute X = refl

------------------------------------------------------------------------
-- Mode environments under renaming
------------------------------------------------------------------------

ModeRename : Renameᵗ → ModeEnv → ModeEnv → Set
ModeRename ρ μ ν = ∀ X → μ X ≡ ν (ρ X)

ModeRename-ext : ∀ {ρ μ ν}
  → ModeRename ρ μ ν
  → ModeRename (extᵗ ρ) (extᵈ μ) (extᵈ ν)
ModeRename-ext rel zero = refl
ModeRename-ext rel (suc X) = rel X

ModeRename-gen : ∀ {ρ μ ν}
  → ModeRename ρ μ ν
  → ModeRename (extᵗ ρ) (genᵈ μ) (genᵈ ν)
ModeRename-gen rel zero = refl
ModeRename-gen rel (suc X) = rel X

ModeRename-inst : ∀ {ρ μ ν}
  → ModeRename ρ μ ν
  → ModeRename (extᵗ ρ) (instᵈ μ) (instᵈ ν)
ModeRename-inst rel zero = refl
ModeRename-inst rel (suc X) = rel X

modeRename-left-inverse : ∀ {ρ ψ μ}
  → RenameLeftInverse ρ ψ
  → ModeRename ρ μ (λ Y → μ (ψ Y))
modeRename-left-inverse {μ = μ} inv X = sym (cong μ (inv X))

modeRename-sealAllowed : ∀ {ρ μ ν α}
  → ModeRename ρ μ ν
  → sealModeAllowed (μ α) ≡ true
  → sealModeAllowed (ν (ρ α)) ≡ true
modeRename-sealAllowed {α = α} rel ok =
  trans (sym (cong sealModeAllowed (rel α))) ok

modeRename-tagAllowed : ∀ {ρ μ ν G}
  → ModeRename ρ μ ν
  → tagAllowed μ G ≡ true
  → tagAllowed ν (renameᵍ ρ G) ≡ true
modeRename-tagAllowed {G = ＇ X} rel ok =
  trans (sym (cong tagModeAllowed (rel X))) ok
modeRename-tagAllowed {G = ‵ ι} rel ok = refl
modeRename-tagAllowed {G = ★⇒★} rel ok = refl

------------------------------------------------------------------------
-- Coercion typing transport
------------------------------------------------------------------------

coercion-store-weaken : ∀ {μ Δ Σ Σ′ c A B}
  → Σ ⊆ Σ′
  → μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
  → μ ∣ Δ ∣ Σ′ ⊢ c ∶ A =⇒ B
coercion-store-weaken incl (cast-id hA) = cast-id hA
coercion-store-weaken incl (cast-error hA hB) =
  cast-error hA hB
coercion-store-weaken incl (cast-seal hA α∈Σ ok) =
  cast-seal hA (incl α∈Σ) ok
coercion-store-weaken incl (cast-unseal hA α∈Σ ok) =
  cast-unseal hA (incl α∈Σ) ok
coercion-store-weaken incl (cast-seq p⊢ q⊢) =
  cast-seq (coercion-store-weaken incl p⊢)
           (coercion-store-weaken incl q⊢)
coercion-store-weaken incl (cast-tag hG ok G꞉A) =
  cast-tag hG ok G꞉A
coercion-store-weaken incl (cast-untag hG ok G꞉A) =
  cast-untag hG ok G꞉A
coercion-store-weaken incl (cast-fun p⊢ q⊢) =
  cast-fun (coercion-store-weaken incl p⊢)
           (coercion-store-weaken incl q⊢)
coercion-store-weaken incl (cast-all c⊢) =
  cast-all (coercion-store-weaken (renameTyStoreᵗ-incl suc incl) c⊢)
coercion-store-weaken incl (cast-inst hB occ c⊢) =
  cast-inst hB occ
    (coercion-store-weaken
      (⊆-cons (renameTyStoreᵗ-incl suc incl)) c⊢)
coercion-store-weaken incl (cast-gen hA occ c⊢) =
  cast-gen hA occ
    (coercion-store-weaken (renameTyStoreᵗ-incl suc incl) c⊢)

coercion-renameᵗ : ∀ {Δ Δ′ Σ c A B ρ μ ν}
  → TyRenameWf Δ Δ′ ρ
  → ModeRename ρ μ ν
  → μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
  → ν ∣ Δ′ ∣ renameTyStoreᵗ ρ Σ ⊢ renameᶜ ρ c
      ∶ renameᵗ ρ A =⇒ renameᵗ ρ B
coercion-renameᵗ hρ rel (cast-id hA) =
  cast-id (renameᵗ-preserves-WfTy hA hρ)
coercion-renameᵗ hρ rel (cast-error hA hB) =
  cast-error
    (renameᵗ-preserves-WfTy hA hρ)
    (renameᵗ-preserves-WfTy hB hρ)
coercion-renameᵗ {ρ = ρ} {μ = μ} {ν = ν} hρ rel
    (cast-seal {α = α} hA α∈Σ ok) =
  cast-seal
    (renameᵗ-preserves-WfTy hA hρ)
    (∈-renameTyStoreᵗ ρ α∈Σ)
    (modeRename-sealAllowed
      {ρ = ρ} {μ = μ} {ν = ν} {α = α} rel ok)
coercion-renameᵗ {ρ = ρ} {μ = μ} {ν = ν} hρ rel
    (cast-unseal {α = α} hA α∈Σ ok) =
  cast-unseal
    (renameᵗ-preserves-WfTy hA hρ)
    (∈-renameTyStoreᵗ ρ α∈Σ)
    (modeRename-sealAllowed
      {ρ = ρ} {μ = μ} {ν = ν} {α = α} rel ok)
coercion-renameᵗ hρ rel (cast-seq p⊢ q⊢) =
  cast-seq (coercion-renameᵗ hρ rel p⊢)
           (coercion-renameᵗ hρ rel q⊢)
coercion-renameᵗ {ρ = ρ} {μ = μ} {ν = ν} hρ rel
    (cast-tag {G = G} hG ok G꞉A) =
  cast-tag
    (renameᵍ-preserves-WfTag hG hρ)
    (modeRename-tagAllowed
      {ρ = ρ} {μ = μ} {ν = ν} {G = G} rel ok)
    (rename-preserves-tagged ρ G꞉A)
coercion-renameᵗ {ρ = ρ} {μ = μ} {ν = ν} hρ rel
    (cast-untag {H = H} hG ok H꞉B) =
  cast-untag
    (renameᵍ-preserves-WfTag hG hρ)
    (modeRename-tagAllowed
      {ρ = ρ} {μ = μ} {ν = ν} {G = H} rel ok)
    (rename-preserves-tagged ρ H꞉B)
coercion-renameᵗ hρ rel (cast-fun p⊢ q⊢) =
  cast-fun (coercion-renameᵗ hρ rel p⊢)
           (coercion-renameᵗ hρ rel q⊢)
coercion-renameᵗ {ρ = ρ} hρ rel (cast-all c⊢) =
  cast-all
    (subst
      (λ Σ′ → _ ∣ _ ∣ Σ′ ⊢ renameᶜ (extᵗ ρ) _
        ∶ _ =⇒ _)
      (renameTyStoreᵗ-ext-suc-comm ρ _)
      (coercion-renameᵗ (TyRenameWf-ext hρ)
        (ModeRename-ext rel) c⊢))
coercion-renameᵗ {Δ′ = Δ′} {Σ = Σ} {ρ = ρ} {μ = μ} {ν = ν}
    hρ rel (cast-inst {A = A} {B = B} {s = c} hB occ c⊢) =
  cast-inst
    (renameᵗ-preserves-WfTy hB hρ)
    (rename-ext-preserves-zero∈ ρ occ)
    (subst
      (λ T → instᵈ ν ∣ suc Δ′
        ∣ (zero , ★) ∷ ⟰ᵗ (renameTyStoreᵗ ρ Σ)
        ⊢ renameᶜ (extᵗ ρ) c ∶ renameᵗ (extᵗ ρ) A =⇒ T)
      (renameᵗ-ext-suc-comm ρ B)
      renamed-store)
  where
    renamed-store :
      instᵈ ν ∣ suc Δ′
        ∣ (zero , ★) ∷ ⟰ᵗ (renameTyStoreᵗ ρ Σ)
        ⊢ renameᶜ (extᵗ ρ) c
          ∶ renameᵗ (extᵗ ρ) A =⇒ renameᵗ (extᵗ ρ) (⇑ᵗ B)
    renamed-store =
      subst
        (λ Σ′ → instᵈ ν ∣ suc Δ′ ∣ Σ′
          ⊢ renameᶜ (extᵗ ρ) c
            ∶ renameᵗ (extᵗ ρ) A =⇒ renameᵗ (extᵗ ρ) (⇑ᵗ B))
        (cong ((zero , ★) ∷_)
          (renameTyStoreᵗ-ext-suc-comm ρ Σ))
        (coercion-renameᵗ (TyRenameWf-ext hρ)
          (ModeRename-inst rel) c⊢)
coercion-renameᵗ {ρ = ρ} hρ rel
    (cast-gen {A = A} {B = B} hA occ c⊢) =
  cast-gen
    (renameᵗ-preserves-WfTy hA hρ)
    (rename-ext-preserves-zero∈ ρ occ)
    (subst
      (λ T → _ ∣ _ ∣ _ ⊢ renameᶜ (extᵗ ρ) _
        ∶ T =⇒ _)
      (renameᵗ-ext-suc-comm ρ A)
      (subst
        (λ Σ′ → _ ∣ _ ∣ Σ′ ⊢ renameᶜ (extᵗ ρ) _
          ∶ _ =⇒ _)
        (renameTyStoreᵗ-ext-suc-comm ρ _)
        (coercion-renameᵗ (TyRenameWf-ext hρ)
          (ModeRename-gen rel) c⊢)))

------------------------------------------------------------------------
-- Endpoint well-formedness
------------------------------------------------------------------------

coercion-wf : ∀ {μ Δ Σ c A B}
  → StoreWf Δ Σ
  → μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
  → WfTy Δ A × WfTy Δ B
coercion-wf wfΣ (cast-id hA) = hA , hA
coercion-wf wfΣ (cast-error hA hB) = hA , hB
coercion-wf wfΣ (cast-seal hA α∈Σ ok) =
  hA , wfVar (bound wfΣ α∈Σ)
coercion-wf wfΣ (cast-unseal hA α∈Σ ok) =
  wfVar (bound wfΣ α∈Σ) , hA
coercion-wf wfΣ (cast-seq p⊢ q⊢)
    with coercion-wf wfΣ p⊢ | coercion-wf wfΣ q⊢
coercion-wf wfΣ (cast-seq p⊢ q⊢)
    | hA , hB | hB′ , hC =
  hA , hC
coercion-wf wfΣ (cast-tag hG ok G꞉A) =
  tagged-wf hG G꞉A , wf★
coercion-wf wfΣ (cast-untag hG ok G꞉A) =
  wf★ , tagged-wf hG G꞉A
coercion-wf wfΣ (cast-fun p⊢ q⊢)
    with coercion-wf wfΣ p⊢ | coercion-wf wfΣ q⊢
coercion-wf wfΣ (cast-fun p⊢ q⊢)
    | hA′ , hA | hB , hB′ =
  wf⇒ hA hB , wf⇒ hA′ hB′
coercion-wf wfΣ (cast-all c⊢)
    with coercion-wf (StoreWf-⟰ᵗ wfΣ) c⊢
coercion-wf wfΣ (cast-all c⊢) | hA , hB =
  wf∀ hA , wf∀ hB
coercion-wf wfΣ (cast-inst hB occ c⊢)
    with coercion-wf (StoreWf-bind wfΣ wf★) c⊢
coercion-wf wfΣ (cast-inst hB occ c⊢) | hA , hB′ =
  wf∀ hA , hB
coercion-wf wfΣ (cast-gen hA occ c⊢)
    with coercion-wf (StoreWf-⟰ᵗ wfΣ) c⊢
coercion-wf wfΣ (cast-gen hA occ c⊢) | hA′ , hB =
  hA , wf∀ hB
