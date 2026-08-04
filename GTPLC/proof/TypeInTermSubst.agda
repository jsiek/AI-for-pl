module proof.TypeInTermSubst where

-- File Charter:
--   * Type-variable renaming properties for GTPLC terms and typing.
--   * Provides store weakening, typing well-formedness, value transport,
--     and binder-cancellation lemmas used by preservation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans)
  renaming (subst to subst≡)

open import Types
open import TyStore
open import Ctx
open import Coercions
open import Primitives
open import Terms
open import Reduction using (_•)
open import proof.TypeInTypeSubst
open import proof.TyStore
open import proof.TypeInCoercionSubst

------------------------------------------------------------------------
-- Renaming syntax
------------------------------------------------------------------------

renameᵗᵐ-preserves-Value : ∀ ρ {V}
  → Value V
  → Value (renameᵗᵐ ρ V)
renameᵗᵐ-preserves-Value ρ (ƛ N) = ƛ _
renameᵗᵐ-preserves-Value ρ (Λ vV) =
  Λ (renameᵗᵐ-preserves-Value (extᵗ ρ) vV)
renameᵗᵐ-preserves-Value ρ ($ κ) = $ κ
renameᵗᵐ-preserves-Value ρ (vV ⟨ i ⟩) =
  renameᵗᵐ-preserves-Value ρ vV ⟨ renameᶜ-preserves-Inert ρ i ⟩

ext-id-eq : ∀ X
  → extᵗ (λ Y → Y) X ≡ X
ext-id-eq zero = refl
ext-id-eq (suc X) = refl

ext-compose-eq : ∀ ρ ψ X
  → extᵗ ψ (extᵗ ρ X) ≡ extᵗ (λ Y → ψ (ρ Y)) X
ext-compose-eq ρ ψ zero = refl
ext-compose-eq ρ ψ (suc X) = refl

renameᵗᵐ-cong : ∀ {ρ ψ}
  → (∀ X → ρ X ≡ ψ X)
  → ∀ M
  → renameᵗᵐ ρ M ≡ renameᵗᵐ ψ M
renameᵗᵐ-cong eq (` x) = refl
renameᵗᵐ-cong eq (ƛ M) = cong ƛ_ (renameᵗᵐ-cong eq M)
renameᵗᵐ-cong eq (L · M) =
  cong₂ _·_ (renameᵗᵐ-cong eq L) (renameᵗᵐ-cong eq M)
renameᵗᵐ-cong eq (Λ M) =
  cong Λ_ (renameᵗᵐ-cong ext-eq M)
  where
    ext-eq : ∀ X → extᵗ _ X ≡ extᵗ _ X
    ext-eq zero = refl
    ext-eq (suc X) = cong suc (eq X)
renameᵗᵐ-cong eq (ν A · L •⟨ c ⟩) =
  cong₃ {f = ν_·_•⟨_⟩}
    (renameᵗ-cong eq A)
    (renameᵗᵐ-cong eq L)
    (renameᶜ-cong ext-eq c)
  where
    cong₃ : ∀ {A B C D : Set}{f : A → B → C → D}
      {x x′ y y′ z z′}
      → x ≡ x′
      → y ≡ y′
      → z ≡ z′
      → f x y z ≡ f x′ y′ z′
    cong₃ refl refl refl = refl

    ext-eq : ∀ X → extᵗ _ X ≡ extᵗ _ X
    ext-eq zero = refl
    ext-eq (suc X) = cong suc (eq X)
renameᵗᵐ-cong eq ($ κ) = refl
renameᵗᵐ-cong eq (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    (renameᵗᵐ-cong eq L) (renameᵗᵐ-cong eq M)
renameᵗᵐ-cong eq (M ⟨ c ⟩) =
  cong₂ _⟨_⟩ (renameᵗᵐ-cong eq M) (renameᶜ-cong eq c)
renameᵗᵐ-cong eq blame = refl

renameᵗᵐ-id : ∀ M
  → renameᵗᵐ (λ X → X) M ≡ M
renameᵗᵐ-id (` x) = refl
renameᵗᵐ-id (ƛ M) = cong ƛ_ (renameᵗᵐ-id M)
renameᵗᵐ-id (L · M) = cong₂ _·_ (renameᵗᵐ-id L) (renameᵗᵐ-id M)
renameᵗᵐ-id (Λ M) =
  cong Λ_ (trans (renameᵗᵐ-cong ext-id M) (renameᵗᵐ-id M))
  where
    ext-id : ∀ X → extᵗ (λ Y → Y) X ≡ X
    ext-id zero = refl
    ext-id (suc X) = refl
renameᵗᵐ-id (ν A · L •⟨ c ⟩)
    rewrite renameᵗ-id A | renameᵗᵐ-id L =
  cong (ν A · L •⟨_⟩)
    (trans (renameᶜ-cong ext-id-eq c) (renameᶜ-id c))
renameᵗᵐ-id ($ κ) = refl
renameᵗᵐ-id (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    (renameᵗᵐ-id L) (renameᵗᵐ-id M)
renameᵗᵐ-id (M ⟨ c ⟩) =
  cong₂ _⟨_⟩ (renameᵗᵐ-id M) (renameᶜ-id c)
renameᵗᵐ-id blame = refl

renameᵗᵐ-compose : ∀ ρ ψ M
  → renameᵗᵐ ψ (renameᵗᵐ ρ M) ≡
    renameᵗᵐ (λ X → ψ (ρ X)) M
renameᵗᵐ-compose ρ ψ (` x) = refl
renameᵗᵐ-compose ρ ψ (ƛ M) =
  cong ƛ_ (renameᵗᵐ-compose ρ ψ M)
renameᵗᵐ-compose ρ ψ (L · M) =
  cong₂ _·_ (renameᵗᵐ-compose ρ ψ L)
             (renameᵗᵐ-compose ρ ψ M)
renameᵗᵐ-compose ρ ψ (Λ M) =
  cong Λ_
    (trans (renameᵗᵐ-compose (extᵗ ρ) (extᵗ ψ) M)
      (renameᵗᵐ-cong ext-compose M))
  where
    ext-compose : ∀ X
      → extᵗ ψ (extᵗ ρ X) ≡ extᵗ (λ Y → ψ (ρ Y)) X
    ext-compose zero = refl
    ext-compose (suc X) = refl
renameᵗᵐ-compose ρ ψ (ν A · L •⟨ c ⟩)
    rewrite renameᵗ-compose ρ ψ A
          | renameᵗᵐ-compose ρ ψ L =
  cong (ν (renameᵗ (λ X → ψ (ρ X)) A)
          · renameᵗᵐ (λ X → ψ (ρ X)) L •⟨_⟩)
    (trans (renameᶜ-compose (extᵗ ρ) (extᵗ ψ) c)
      (renameᶜ-cong (ext-compose-eq ρ ψ) c))
renameᵗᵐ-compose ρ ψ ($ κ) = refl
renameᵗᵐ-compose ρ ψ (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    (renameᵗᵐ-compose ρ ψ L) (renameᵗᵐ-compose ρ ψ M)
renameᵗᵐ-compose ρ ψ (M ⟨ c ⟩) =
  cong₂ _⟨_⟩ (renameᵗᵐ-compose ρ ψ M)
    (renameᶜ-compose ρ ψ c)
renameᵗᵐ-compose ρ ψ blame = refl

renameᵗᵐ-left-inverse : ∀ {ρ ψ}
  → RenameLeftInverse ρ ψ
  → ∀ M
  → renameᵗᵐ ψ (renameᵗᵐ ρ M) ≡ M
renameᵗᵐ-left-inverse {ρ = ρ} {ψ = ψ} inv M =
  trans (renameᵗᵐ-compose ρ ψ M)
    (trans (renameᵗᵐ-cong inv M) (renameᵗᵐ-id M))

open0-ext-suc-cancelᵐ : ∀ M
  → renameᵗᵐ (singleRenameᵗ zero) (renameᵗᵐ (extᵗ suc) M) ≡ M
open0-ext-suc-cancelᵐ =
  renameᵗᵐ-left-inverse open0-ext-suc-inv

------------------------------------------------------------------------
-- Context and store weakening
------------------------------------------------------------------------

lookup-map : ∀ {Γ x A}{f : Ty → Ty}
  → Γ ∋ x ⦂ A
  → map f Γ ∋ x ⦂ f A
lookup-map Z = Z
lookup-map (S h) = S (lookup-map h)

lookup-map-inv : ∀ {Γ x B}{f : Ty → Ty}
  → map f Γ ∋ x ⦂ B
  → ∃[ A ] (Γ ∋ x ⦂ A × f A ≡ B)
lookup-map-inv {Γ = A ∷ Γ} Z = A , Z , refl
lookup-map-inv {Γ = A ∷ Γ} (S h)
    with lookup-map-inv h
lookup-map-inv {Γ = A ∷ Γ} (S h) | B , B∈Γ , eq =
  B , S B∈Γ , eq

map-rename-ext-suc-comm : ∀ ρ Γ
  → map (renameᵗ (extᵗ ρ)) (⤊ᵗ Γ) ≡
    ⤊ᵗ (map (renameᵗ ρ) Γ)
map-rename-ext-suc-comm ρ [] = refl
map-rename-ext-suc-comm ρ (A ∷ Γ) =
  cong₂ _∷_ (renameᵗ-ext-suc-comm ρ A)
             (map-rename-ext-suc-comm ρ Γ)

typing-store-weaken : ∀ {Δ Σ Σ′ Γ M A}
  → Σ ⊆ Σ′
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
  → ⟨ Δ , Σ′ , Γ ⟩ ⊢ M ⦂ A
typing-store-weaken incl (⊢` h) = ⊢` h
typing-store-weaken incl (⊢ƛ hA hM) =
  ⊢ƛ hA (typing-store-weaken incl hM)
typing-store-weaken incl (⊢· hL hM) =
  ⊢· (typing-store-weaken incl hL) (typing-store-weaken incl hM)
typing-store-weaken incl (⊢Λ vM hM) =
  ⊢Λ vM (typing-store-weaken (renameTyStoreᵗ-incl suc incl) hM)
typing-store-weaken incl (⊢ν hA hL c⊢) =
  ⊢ν hA (typing-store-weaken incl hL)
    (coercion-store-weaken
      (⊆-cons (renameTyStoreᵗ-incl suc incl)) c⊢)
typing-store-weaken incl (⊢$ κ) = ⊢$ κ
typing-store-weaken incl (⊢⊕ hL op hM) =
  ⊢⊕ (typing-store-weaken incl hL) op (typing-store-weaken incl hM)
typing-store-weaken incl (⊢⟨⟩ c⊢ hM) =
  ⊢⟨⟩ (coercion-store-weaken incl c⊢)
       (typing-store-weaken incl hM)
typing-store-weaken incl (⊢blame hA) = ⊢blame hA

------------------------------------------------------------------------
-- Typing under type renaming
------------------------------------------------------------------------

typing-renameᵗ : ∀ {Δ Δ′ Σ Γ M A ρ ψ}
  → TyRenameWf Δ Δ′ ρ
  → RenameLeftInverse ρ ψ
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
  → ⟨ Δ′ , renameTyStoreᵗ ρ Σ , map (renameᵗ ρ) Γ ⟩
      ⊢ renameᵗᵐ ρ M ⦂ renameᵗ ρ A
typing-renameᵗ hρ inv (⊢` h) = ⊢` (lookup-map h)
typing-renameᵗ {ρ = ρ} {ψ = ψ} hρ inv (⊢ƛ hA hM) =
  ⊢ƛ (renameᵗ-preserves-WfTy hA hρ)
     (typing-renameᵗ {ρ = ρ} {ψ = ψ} hρ inv hM)
typing-renameᵗ {ρ = ρ} {ψ = ψ} hρ inv (⊢· hL hM) =
  ⊢· (typing-renameᵗ {ρ = ρ} {ψ = ψ} hρ inv hL)
     (typing-renameᵗ {ρ = ρ} {ψ = ψ} hρ inv hM)
typing-renameᵗ {Δ′ = Δ′} {Σ = Σ} {Γ = Γ} {ρ = ρ} {ψ = ψ}
    hρ inv (⊢Λ vM hM) =
  ⊢Λ (renameᵗᵐ-preserves-Value (extᵗ ρ) vM) renamed-body
  where
    renamed :
      ⟨ suc Δ′
        , renameTyStoreᵗ (extᵗ ρ) (⟰ᵗ Σ)
        , map (renameᵗ (extᵗ ρ)) (⤊ᵗ Γ) ⟩
        ⊢ renameᵗᵐ (extᵗ ρ) _ ⦂ _
    renamed =
      typing-renameᵗ {ρ = extᵗ ρ} {ψ = extᵗ ψ}
        (TyRenameWf-ext hρ)
        (RenameLeftInverse-ext inv) hM

    renamed-store :
      ⟨ suc Δ′
        , ⟰ᵗ (renameTyStoreᵗ ρ Σ)
        , map (renameᵗ (extᵗ ρ)) (⤊ᵗ Γ) ⟩
        ⊢ renameᵗᵐ (extᵗ ρ) _ ⦂ _
    renamed-store =
      subst≡
        (λ Σ′ → ⟨ suc Δ′
          , Σ′
          , map (renameᵗ (extᵗ ρ)) (⤊ᵗ Γ) ⟩
          ⊢ renameᵗᵐ (extᵗ ρ) _ ⦂ _)
        (renameTyStoreᵗ-ext-suc-comm ρ Σ)
        renamed

    renamed-body :
      ⟨ suc Δ′
        , ⟰ᵗ (renameTyStoreᵗ ρ Σ)
        , ⤊ᵗ (map (renameᵗ ρ) Γ) ⟩
        ⊢ renameᵗᵐ (extᵗ ρ) _ ⦂ _
    renamed-body =
      subst≡
        (λ Γ′ → ⟨ suc Δ′ , ⟰ᵗ (renameTyStoreᵗ ρ Σ) , Γ′ ⟩
          ⊢ renameᵗᵐ (extᵗ ρ) _ ⦂ _)
        (map-rename-ext-suc-comm ρ Γ)
        renamed-store
typing-renameᵗ {Δ = Δ} {Δ′ = Δ′} {Σ = Σ}
    {M = ν A · L •⟨ c ⟩} {ρ = ρ} {ψ = ψ}
    hρ inv (⊢ν {A = A} {B = B} hA hL c⊢) =
  ⊢ν
    (renameᵗ-preserves-WfTy hA hρ)
    (typing-renameᵗ {ρ = ρ} {ψ = ψ} hρ inv hL)
    (renamed-coercion c⊢)
  where
    renamed-coercion : ∀ {C μ}
      → μ ∣ suc Δ ∣ (zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ
          ⊢ c ∶ C =⇒ ⇑ᵗ B
      → (λ Y → μ (extᵗ ψ Y)) ∣ suc Δ′
          ∣ (zero , ⇑ᵗ (renameᵗ ρ A))
              ∷ ⟰ᵗ (renameTyStoreᵗ ρ Σ)
          ⊢ renameᶜ (extᵗ ρ) c
            ∶ renameᵗ (extᵗ ρ) C =⇒ ⇑ᵗ (renameᵗ ρ B)
    renamed-coercion {C = C} {μ = μ} c⊢ =
      subst≡
        (λ T → (λ Y → μ (extᵗ ψ Y)) ∣ suc Δ′
          ∣ (zero , ⇑ᵗ (renameᵗ ρ A))
              ∷ ⟰ᵗ (renameTyStoreᵗ ρ Σ)
          ⊢ renameᶜ (extᵗ ρ) c
            ∶ renameᵗ (extᵗ ρ) C =⇒ T)
        (renameᵗ-ext-suc-comm ρ B)
        (subst≡
          (λ Σ′ → (λ Y → μ (extᵗ ψ Y)) ∣ suc Δ′ ∣ Σ′
            ⊢ renameᶜ (extᵗ ρ) c
              ∶ renameᵗ (extᵗ ρ) C
                =⇒ renameᵗ (extᵗ ρ) (⇑ᵗ B))
          (cong₂ _∷_
            (cong₂ _,_ refl (renameᵗ-ext-suc-comm ρ A))
            (renameTyStoreᵗ-ext-suc-comm ρ Σ))
          (coercion-renameᵗ
            (TyRenameWf-ext hρ)
            (modeRename-left-inverse
              {ρ = extᵗ ρ} {ψ = extᵗ ψ} {μ = μ}
              (RenameLeftInverse-ext inv))
            c⊢))
typing-renameᵗ hρ inv (⊢$ (κℕ n)) = ⊢$ (κℕ n)
typing-renameᵗ {ρ = ρ} {ψ = ψ} hρ inv (⊢⊕ hL op hM) =
  ⊢⊕ (typing-renameᵗ {ρ = ρ} {ψ = ψ} hρ inv hL) op
      (typing-renameᵗ {ρ = ρ} {ψ = ψ} hρ inv hM)
typing-renameᵗ {ρ = ρ} {ψ = ψ} hρ inv
    (⊢⟨⟩ {μ = μ} c⊢ hM) =
  ⊢⟨⟩ {μ = λ Y → μ (ψ Y)}
    (coercion-renameᵗ hρ
      (modeRename-left-inverse {ρ = ρ} {ψ = ψ} {μ = μ} inv) c⊢)
    (typing-renameᵗ {ρ = ρ} {ψ = ψ} hρ inv hM)
typing-renameᵗ hρ inv (⊢blame hA) =
  ⊢blame (renameᵗ-preserves-WfTy hA hρ)

typing-shiftᵗ : ∀ {Δ Σ Γ M A}
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
  → ⟨ suc Δ , ⟰ᵗ Σ , ⤊ᵗ Γ ⟩ ⊢ ⇑ᵗᵐ M ⦂ ⇑ᵗ A
typing-shiftᵗ M⊢ =
  typing-renameᵗ {ρ = suc} {ψ = predᵗ}
    TyRenameWf-suc RenameLeftInverse-suc M⊢

------------------------------------------------------------------------
-- Type application
------------------------------------------------------------------------

type-app-typing : ∀ {Δ Σ Γ V C A}
  → Value V
  → ⟨ Δ , Σ , Γ ⟩ ⊢ V ⦂ `∀ C
  → ⟨ suc Δ , (zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ , ⤊ᵗ Γ ⟩
      ⊢ (⇑ᵗᵐ V) • ⦂ C
type-app-typing (ƛ N) ()
type-app-typing (Λ vV) (⊢Λ vV′ V⊢) =
  subst≡
    (λ M → ⟨ _ , _ , _ ⟩ ⊢ M ⦂ _)
    (sym (open0-ext-suc-cancelᵐ _))
    (typing-store-weaken ⊆-drop V⊢)
type-app-typing ($ (κℕ n)) ()
type-app-typing (vV ⟨ G ! ⟩) (⊢⟨⟩ () V⊢)
type-app-typing (vV ⟨ seal α ⟩) (⊢⟨⟩ () V⊢)
type-app-typing (vV ⟨ p ↦ q ⟩) (⊢⟨⟩ () V⊢)
type-app-typing (vV ⟨ `∀ c ⟩)
    (⊢⟨⟩ (cast-all c⊢) V⊢) =
  ⊢⟨⟩
    (subst≡
      (λ d → _ ∣ _ ∣ _ ⊢ d ∶ _ =⇒ _)
      (sym (open0-ext-suc-cancelᶜ _))
      (coercion-store-weaken ⊆-drop c⊢))
    (type-app-typing vV V⊢)
type-app-typing (vV ⟨ gen c ⟩)
    (⊢⟨⟩ (cast-gen hA occ c⊢) V⊢) =
  ⊢⟨⟩
    (subst≡
      (λ d → _ ∣ _ ∣ _ ⊢ d ∶ _ =⇒ _)
      (sym (open0-ext-suc-cancelᶜ _))
      (coercion-store-weaken ⊆-drop c⊢))
    (typing-store-weaken ⊆-drop (typing-shiftᵗ V⊢))

------------------------------------------------------------------------
-- Typing produces well-formed types
------------------------------------------------------------------------

CtxWf-⤊ : ∀ {Δ Γ}
  → CtxWf Δ Γ
  → CtxWf (suc Δ) (⤊ᵗ Γ)
CtxWf-⤊ hΓ h
    with lookup-map-inv h
CtxWf-⤊ hΓ h | A , A∈Γ , refl =
  renameᵗ-preserves-WfTy (hΓ A∈Γ) TyRenameWf-suc

constTy-wf : ∀ {Δ} κ
  → WfTy Δ (constTy κ)
constTy-wf (κℕ n) = wfBase

typing-wf : ∀ {Δ Σ Γ M A}
  → StoreWf Δ Σ
  → CtxWf Δ Γ
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
  → WfTy Δ A
typing-wf wfΣ hΓ (⊢` h) = hΓ h
typing-wf wfΣ hΓ (⊢ƛ hA hM) =
  wf⇒ hA (typing-wf wfΣ (ctxWf-∷ hA hΓ) hM)
typing-wf wfΣ hΓ (⊢· hL hM)
    with typing-wf wfΣ hΓ hL
typing-wf wfΣ hΓ (⊢· hL hM) | wf⇒ hA hB = hB
typing-wf wfΣ hΓ (⊢Λ vM hM) =
  wf∀ (typing-wf (StoreWf-⟰ᵗ wfΣ) (CtxWf-⤊ hΓ) hM)
typing-wf wfΣ hΓ (⊢ν hA hL c⊢)
    with coercion-wf (StoreWf-bind wfΣ hA) c⊢
typing-wf wfΣ hΓ (⊢ν hA hL c⊢) | hC , hB =
  WfTy-un⇑ᵗ hB
typing-wf wfΣ hΓ (⊢$ κ) = constTy-wf κ
typing-wf wfΣ hΓ (⊢⊕ hL op hM) = wfBase
typing-wf wfΣ hΓ (⊢⟨⟩ c⊢ hM)
    with coercion-wf wfΣ c⊢
typing-wf wfΣ hΓ (⊢⟨⟩ c⊢ hM) | hA , hB = hB
typing-wf wfΣ hΓ (⊢blame hA) = hA

closedCtxWf : ∀ {Δ}
  → CtxWf Δ []
closedCtxWf ()
