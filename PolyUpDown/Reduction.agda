module Reduction where

-- File Charter:
--   * Dynamic semantics (values and one-step/multi-step reduction) for PolyUpDown terms.
--   * Cast dynamics for `_at[_]_` over widening/narrowing witnesses.
--   * Store-aware reduction, including the term-level `ν:=_∙_` step and congruence rules.
-- Note to self:
--   * Keep term substitution/weakening facts in `TermProperties.agda`.
--   * If a lemma is primarily about store shape rather than reduction, move it to `Store.agda`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Subset using (_∈_)
open import Data.List using (map; []; _∷_)
open import Data.Nat using (ℕ; _+_; suc; zero)
open import Data.Vec using (Vec; _∷_; here; there)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≢_; cong; cong₂; subst; sym; trans)

open import Types
open import TypeProperties
open import Store
open import UpDown
open import Terms
open import TermProperties

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data Value : ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A → Set where
  V-ƛ :
    ∀{Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{A B : Ty Δ Ψ}
    {N : Δ ∣ Ψ ∣ Σ ∣ (A ∷ Γ) ⊢ B} →
    Value (ƛ A ⇒ N)

  V-const :
    ∀{Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{κ : Const} →
    Value ($ {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ} κ refl)

  V-Λ :
    ∀{Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{A : Ty (suc Δ) Ψ}
    {N : (suc Δ) ∣ Ψ ∣ ⟰ᵗ Σ ∣ (⤊ᵗ Γ) ⊢ A} →
    Value (Λ N)

  V-at-up-tag :
    ∀{Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{G : Ty Δ Ψ}
    {g : Ground G}{Φ Ξ : Vec Bool Ψ}{gok : ⊢ g ok Ξ}{ℓ : Label}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ G} →
    Value V →
    Value (V at[ up ] ((id {Φ = Φ} {Ξ = Ξ}) ； tag g gok ℓ))

  V-at-up-↦ :
    ∀{Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{A A′ B B′ : Ty Δ Ψ}
    {Φ Ξ : Vec Bool Ψ}
    {p : Σ ∣ Φ ∣ Ξ ⊢ A′ ⊒ A}
    {q : Σ ∣ Φ ∣ Ξ ⊢ B ⊑ B′}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)} →
    Value V →
    Value (V at[ up ] (id ； (p ↦ q)))

  V-at-down-↦ :
    ∀{Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{A A′ B B′ : Ty Δ Ψ}
    {Φ Ξ : Vec Bool Ψ}
    {p : Σ ∣ Φ ∣ Ξ ⊢ A′ ⊑ A}
    {q : Σ ∣ Φ ∣ Ξ ⊢ B ⊒ B′}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)} →
    Value V →
    Value (V at[ down ] (id ； (p ↦ q)))

  V-at-up-∀ :
    ∀{Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}
    {A B : Ty (suc Δ) Ψ}
    {p : ⟰ᵗ Σ ∣ every Ψ ∣ none Ψ ⊢ A ⊑ B}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A)} →
    Value V →
    Value (V at[ up ] (id ； (∀ᵖ p)))

  V-at-down-∀ :
    ∀{Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}
    {A B : Ty (suc Δ) Ψ}
    {p : ⟰ᵗ Σ ∣ none Ψ ∣ every Ψ ⊢ A ⊒ B}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A)} →
    Value V →
    Value (V at[ down ] (id ； (∀ᵖ p)))

  V-at-down-ν :
    ∀{Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{A : Ty (suc Δ) Ψ}{B : Ty Δ Ψ}
    {p : ((Zˢ , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ false ∷ none Ψ ∣ true ∷ every Ψ ⊢ ⇑ˢ B ⊒ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ)}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B} →
    Value V →
    Value {A = `∀ A} (V at[ down ] (id ； (ν p)))

------------------------------------------------------------------------
-- One-step reduction helpers
------------------------------------------------------------------------

idˢ : ∀{Ψ} → Renameˢ Ψ Ψ
idˢ α = α

renameˢ-id :
  ∀{Δ}{Ψ}{A : Ty Δ Ψ} →
  renameˢ idˢ A ≡ A
renameˢ-id {A = ＇ X} = refl
renameˢ-id {A = ｀ α} = refl
renameˢ-id {A = ‵ ι} = refl
renameˢ-id {A = ★} = refl
renameˢ-id {A = A ⇒ B} = cong₂ _⇒_ renameˢ-id renameˢ-id
renameˢ-id {A = `∀ A} = cong `∀ renameˢ-id

map-renameˢ-id :
  ∀{Δ}{Ψ} →
  (Γ : Ctx Δ Ψ) →
  map (renameˢ idˢ) Γ ≡ Γ
map-renameˢ-id [] = refl
map-renameˢ-id (A ∷ Γ) = cong₂ _∷_ renameˢ-id (map-renameˢ-id Γ)

renameStoreˢ-id :
  ∀{Δ}{Ψ}{Σ : Store Δ Ψ} →
  renameStoreˢ idˢ Σ ≡ Σ
renameStoreˢ-id {Σ = []} = refl
renameStoreˢ-id {Σ = ((α , A) ∷ Σ)} =
  cong₂ _∷_
    (cong₂ _,_ refl renameˢ-id)
    renameStoreˢ-id

idˢ-⊆ˢ :
  ∀{Δ}{Ψ}{Σ : Store Δ Ψ} →
  renameStoreˢ idˢ Σ ⊆ˢ Σ
idˢ-⊆ˢ {Σ = Σ} rewrite renameStoreˢ-id {Σ = Σ} = ⊆ˢ-refl

id-step-term :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ ∣ Σ ∣ map (renameˢ idˢ) Γ ⊢ renameˢ idˢ A
id-step-term {Σ = Σ} M =
  cast⊢
    (renameStoreˢ-id {Σ = Σ})
    refl
    refl
    (renameˢ-term idˢ M)

openCast⊑ :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{Φ Ξ : Vec Bool Ψ}
    {A B : Ty (suc Δ) Ψ} →
  (p : ⟰ᵗ Σ ∣ Φ ∣ Ξ ⊢ A ⊑ B) →
  (α : Seal Ψ) →
  Σ ∣ Φ ∣ Ξ ⊢ A [ ｀ α ]ᵗ ⊑ B [ ｀ α ]ᵗ
openCast⊑ {Σ = Σ} p α =
  cast⊑
    (substStoreᵗ-singleTyEnv-⟰ᵗ (｀ α) Σ)
    refl
    refl
    refl
    refl
    (p [ ｀ α ]⊑ᵗ)

openCast⊒ :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{Φ Ξ : Vec Bool Ψ}
    {A B : Ty (suc Δ) Ψ} →
  (p : ⟰ᵗ Σ ∣ Φ ∣ Ξ ⊢ A ⊒ B) →
  (α : Seal Ψ) →
  Σ ∣ Φ ∣ Ξ ⊢ A [ ｀ α ]ᵗ ⊒ B [ ｀ α ]ᵗ
openCast⊒ {Σ = Σ} p α =
  cast⊒
    (substStoreᵗ-singleTyEnv-⟰ᵗ (｀ α) Σ)
    refl
    refl
    refl
    refl
    (p [ ｀ α ]⊒ᵗ)

top★-lookup :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ} →
  ((Zˢ , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∋ˢ Zˢ ⦂ ★
top★-lookup = Z∋ˢ refl refl

removeAtˢ :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{α : Seal Ψ}{A : Ty Δ Ψ} →
  Σ ∋ˢ α ⦂ A →
  Store Δ Ψ
removeAtˢ {Σ = (_ , _) ∷ Σ} (Z∋ˢ _ _) = Σ
removeAtˢ {Σ = (β , B) ∷ Σ} (S∋ˢ h) = (β , B) ∷ removeAtˢ h

data DropLookup
  {Δ}{Ψ}{Σ : Store Δ Ψ}{α : Seal Ψ}
  (h★ : Σ ∋ˢ α ⦂ ★)
  {β : Seal Ψ}{B : Ty Δ Ψ}
  (h : Σ ∋ˢ β ⦂ B) : Set where
  drop-hit :
    β ≡ α →
    B ≡ ★ →
    DropLookup h★ h

  drop-keep :
    removeAtˢ h★ ∋ˢ β ⦂ B →
    DropLookup h★ h

dropLookup :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{α : Seal Ψ}
    (h★ : Σ ∋ˢ α ⦂ ★)
    {β : Seal Ψ}{B : Ty Δ Ψ}
    (h : Σ ∋ˢ β ⦂ B) →
  DropLookup h★ h
dropLookup (Z∋ˢ α≡δ ★≡D) (Z∋ˢ β≡δ B≡D) =
  drop-hit (trans β≡δ (sym α≡δ)) (trans B≡D (sym ★≡D))
dropLookup (Z∋ˢ _ _) (S∋ˢ h) = drop-keep h
dropLookup (S∋ˢ h★) (Z∋ˢ β≡δ B≡D) = drop-keep (Z∋ˢ β≡δ B≡D)
dropLookup (S∋ˢ h★) (S∋ˢ h) with dropLookup h★ h
... | drop-hit β≡α B≡★ = drop-hit β≡α B≡★
... | drop-keep h′ = drop-keep (S∋ˢ h′)

removeAtˢ-renameLookup-S :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{α : Seal Ψ}{A : Ty Δ Ψ}
    (h : Σ ∋ˢ α ⦂ A) →
  removeAtˢ (renameLookupˢ Sˢ h) ≡ ⟰ˢ (removeAtˢ h)
removeAtˢ-renameLookup-S (Z∋ˢ _ _) = refl
removeAtˢ-renameLookup-S {Σ = (β , B) ∷ Σ} (S∋ˢ h) =
  cong₂ _∷_ refl (removeAtˢ-renameLookup-S h)

removeAtˢ-ν-lift :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{α : Seal Ψ}
    (h★ : Σ ∋ˢ α ⦂ ★) →
  removeAtˢ (S∋ˢ (renameLookupˢ Sˢ h★))
    ≡ ((Zˢ , ⇑ˢ ★) ∷ ⟰ˢ (removeAtˢ h★))
removeAtˢ-ν-lift h★ = cong₂ _∷_ refl (removeAtˢ-renameLookup-S h★)

removeAtˢ-renameLookupᵗ :
  ∀ {Δ}{Δ′}{Ψ}{Σ : Store Δ Ψ}{α : Seal Ψ}{A : Ty Δ Ψ}
    (ρ : Renameᵗ Δ Δ′) →
  (h : Σ ∋ˢ α ⦂ A) →
  removeAtˢ (renameLookupᵗ ρ h) ≡ renameStoreᵗ ρ (removeAtˢ h)
removeAtˢ-renameLookupᵗ ρ (Z∋ˢ _ _) = refl
removeAtˢ-renameLookupᵗ {Σ = (β , B) ∷ Σ} ρ (S∋ˢ h) =
  cong₂ _∷_
    refl
    (removeAtˢ-renameLookupᵗ ρ h)

mutual
  drop★⊒ :
    ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{α : Seal Ψ}
      {Φ Ξ : Vec Bool Ψ}{A B : Ty Δ Ψ} →
    (h★ : Σ ∋ˢ α ⦂ ★) →
    ⌊ α ⌋ ∈ Ξ →
    Σ ∣ Φ ∣ Ξ ⊢ A ⊒ B →
    removeAtˢ h★ ∣ Φ ∣ Ξ ⊢ A ⊒ B
  drop★⊒ h★ α∈Ξ (untag g gok ℓ) = untag g gok ℓ
  drop★⊒ {α = α} h★ α∈Ξ (seal h α∈Φ) with dropLookup h★ h
  ... | drop-keep h′ = seal h′ α∈Φ
  ... | drop-hit β≡α B≡★ =
    cast⊒
      refl
      refl
      refl
      (sym B≡★)
      (cong ｀_ (sym β≡α))
      (untag (｀ α) α∈Ξ zero)
  drop★⊒ h★ α∈Ξ (p ↦ q) = drop★⊑ h★ α∈Ξ p ↦ drop★⊒ h★ α∈Ξ q
  drop★⊒ h★ α∈Ξ (∀ᵖ p) =
    ∀ᵖ (cast⊒
          (removeAtˢ-renameLookupᵗ Sᵗ h★)
          refl
          refl
          refl
          refl
          (drop★⊒ (renameLookupᵗ Sᵗ h★) α∈Ξ p))
  drop★⊒ h★ α∈Ξ (ν p) =
    ν (cast⊒
         (removeAtˢ-ν-lift h★)
         refl
         refl
         refl
         refl
         (drop★⊒ (S∋ˢ (renameLookupˢ Sˢ h★)) (there α∈Ξ) p))
  drop★⊒ h★ α∈Ξ id = id
  drop★⊒ h★ α∈Ξ (p ； q) = drop★⊒ h★ α∈Ξ p ； drop★⊒ h★ α∈Ξ q

  drop★⊑ :
    ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{α : Seal Ψ}
      {Φ Ξ : Vec Bool Ψ}{A B : Ty Δ Ψ} →
    (h★ : Σ ∋ˢ α ⦂ ★) →
    ⌊ α ⌋ ∈ Ξ →
    Σ ∣ Φ ∣ Ξ ⊢ A ⊑ B →
    removeAtˢ h★ ∣ Φ ∣ Ξ ⊢ A ⊑ B
  drop★⊑ h★ α∈Ξ (tag g gok ℓ) = tag g gok ℓ
  drop★⊑ {α = α} h★ α∈Ξ (unseal h α∈Φ′) with dropLookup h★ h
  ... | drop-keep h′ = unseal h′ α∈Φ′
  ... | drop-hit β≡α B≡★ =
    cast⊑
      refl
      refl
      refl
      (cong ｀_ (sym β≡α))
      (sym B≡★)
      (tag (｀ α) α∈Ξ zero)
  drop★⊑ h★ α∈Ξ (p ↦ q) = drop★⊒ h★ α∈Ξ p ↦ drop★⊑ h★ α∈Ξ q
  drop★⊑ h★ α∈Ξ (∀ᵖ p) =
    ∀ᵖ (cast⊑
          (removeAtˢ-renameLookupᵗ Sᵗ h★)
          refl
          refl
          refl
          refl
          (drop★⊑ (renameLookupᵗ Sᵗ h★) α∈Ξ p))
  drop★⊑ h★ α∈Ξ (ν p) =
    ν (cast⊑
         (removeAtˢ-ν-lift h★)
         refl
         refl
         refl
         refl
         (drop★⊑ (S∋ˢ (renameLookupˢ Sˢ h★)) (there α∈Ξ) p))
  drop★⊑ h★ α∈Ξ id = id
  drop★⊑ h★ α∈Ξ (p ； q) = drop★⊑ h★ α∈Ξ p ； drop★⊑ h★ α∈Ξ q

openν-down :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}
    {Φ Ξ : Vec Bool Ψ}
    {A : Ty (suc Δ) Ψ}
    {B : Ty Δ Ψ} →
  (p : ((Zˢ , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ false ∷ Φ ∣ true ∷ Ξ ⊢ ⇑ˢ B ⊒ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ)) →
  (α : Seal Ψ) →
  ⌊ α ⌋ ∈ Ξ →
  Σ ∣ Φ ∣ Ξ ⊢ B ⊒ (A [ ｀ α ]ᵗ)
openν-down {Σ = Σ} {Φ = Φ} {Ξ = Ξ} {A = A} {B = B} p α α∈Ξ =
  drop★⊒ top★ α∈Ξ
    (cast⊒
      Σ-eq
      refl
      refl
      src-eq
      tgt-eq
      (⊒-renameˢ
        (singleSealEnv α)
        (RenOk-singleSealEnv-false {P = Φ})
        (RenOk-singleSealEnv-true α∈Ξ)
        p))
  where
    top★ :
      ((α , ★) ∷ Σ) ∋ˢ α ⦂ ★
    top★ = Z∋ˢ refl refl

    Σ-eq :
      renameStoreˢ (singleSealEnv α) ((Zˢ , ⇑ˢ ★) ∷ ⟰ˢ Σ) ≡ ((α , ★) ∷ Σ)
    Σ-eq =
      cong₂ _∷_
        (cong₂ _,_ refl (renameˢ-single-⇑ˢ-id α ★))
        (renameStoreˢ-single-⟰ˢ α Σ)

    src-eq :
      renameˢ (singleSealEnv α) (⇑ˢ B) ≡ B
    src-eq = renameˢ-single-⇑ˢ-id α B

    tgt-eq :
      renameˢ (singleSealEnv α) ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ≡ (A [ ｀ α ]ᵗ)
    tgt-eq =
      trans
        (renameˢ-[]ᵗ-seal (singleSealEnv α) (⇑ˢ A) Zˢ)
        (cong (λ T → T [ ｀ α ]ᵗ) (renameˢ-single-⇑ˢ-id α A))

openν-down-every :
  ∀ {Ψ}{Σ : Store 0 Ψ}
    {A : Ty (suc 0) Ψ}
    {B : Ty 0 Ψ}
    (p : ((Zˢ , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ false ∷ none Ψ ∣ true ∷ every Ψ ⊢ ⇑ˢ B ⊒ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ)) →
  (α : Seal Ψ) →
  Σ ∣ none Ψ ∣ every Ψ ⊢ B ⊒ (A [ ｀ α ]ᵗ)
openν-down-every {Ψ = Ψ} {Σ = Σ} {A = A} {B = B} p α =
  openν-down
    {Δ = 0}
    {Ψ = Ψ}
    {Σ = Σ}
    {Φ = none Ψ}
    {Ξ = every Ψ}
    {A = A}
    {B = B}
    p
    α
    (every-member α)

------------------------------------------------------------------------
-- One-step reduction
------------------------------------------------------------------------

infix 2 _—→[_]_
data _—→[_]_ :
  ∀ {Ψ}{Ψ′}{Σ : Store 0 Ψ}{Σ′ : Store 0 Ψ′}{A : Ty 0 Ψ} →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ A →
  (ρ : Renameˢ Ψ Ψ′) →
  0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A → Set where

  β :
    ∀ {Ψ}{Σ : Store 0 Ψ}{A B : Ty 0 Ψ}
      {N : 0 ∣ Ψ ∣ Σ ∣ (B ∷ []) ⊢ A}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ B} →
    Value V →
    (ƛ B ⇒ N) · V —→[ idˢ ] id-step-term (N [ V ])

  β-Λ :
    ∀ {Ψ}{Σ : Store 0 Ψ}
      {A : Ty (suc 0) Ψ}
      {V : (suc 0) ∣ Ψ ∣ ⟰ᵗ Σ ∣ (⤊ᵗ []) ⊢ A}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    ((Λ V) • α [ h ]) refl —→[ idˢ ] id-step-term (V [ ｀ α ]ᵀ)

  β-at-up-∀ :
    ∀ {Ψ}{Σ : Store 0 Ψ}
      {A B : Ty (suc 0) Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ `∀ A}
      {p : ⟰ᵗ Σ ∣ every Ψ ∣ none Ψ ⊢ A ⊑ B}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    (((V at[ up ] (id ； ∀ᵖ p)) • α [ h ]) refl)
      —→[ idˢ ]
    id-step-term ((((V • α [ h ]) refl) at[ up ] openCast⊑ p α))

  β-at-down-∀ :
    ∀ {Ψ}{Σ : Store 0 Ψ}
      {A B : Ty (suc 0) Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ `∀ A}
      {p : ⟰ᵗ Σ ∣ none Ψ ∣ every Ψ ⊢ A ⊒ B}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    (((V at[ down ] (id ； ∀ᵖ p)) • α [ h ]) refl)
      —→[ idˢ ]
    id-step-term ((((V • α [ h ]) refl) at[ down ] openCast⊒ p α))

  β-at-down-ν :
    ∀ {Ψ}{Σ : Store 0 Ψ}
      {A : Ty (suc 0) Ψ}
      {B : Ty 0 Ψ}
      {p : ((Zˢ , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ false ∷ none Ψ ∣ true ∷ every Ψ ⊢ ⇑ˢ B ⊒ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ)}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ B}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    (_•_[_]
      {Δ = 0} {Ψ = Ψ} {Σ = Σ} {Γ = []}
      {A = A} {B = A [ ｀ α ]ᵗ} {C = C}
      (V at[ down ] (id ； ν p)) α h refl)
      —→[ idˢ ]
    id-step-term {A = A [ ｀ α ]ᵗ}
      (V at[ down ] openν-down-every {A = A} {B = B} p α)

  β-at-up-↦ :
    ∀ {Ψ}{Σ : Store 0 Ψ}
      {A A′ B B′ : Ty 0 Ψ}
      {Φ Ξ : Vec Bool Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (A ⇒ B)}
      {W : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A′}
      {p : Σ ∣ Φ ∣ Ξ ⊢ A′ ⊒ A}
      {q : Σ ∣ Φ ∣ Ξ ⊢ B ⊑ B′} →
    (V at[ up ] (id ； (p ↦ q))) · W
      —→[ idˢ ]
    id-step-term ((V · (W at[ down ] p)) at[ up ] q)

  β-at-down-↦ :
    ∀ {Ψ}{Σ : Store 0 Ψ}
      {A A′ B B′ : Ty 0 Ψ}
      {Φ Ξ : Vec Bool Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (A ⇒ B)}
      {W : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A′}
      {p : Σ ∣ Φ ∣ Ξ ⊢ A′ ⊑ A}
      {q : Σ ∣ Φ ∣ Ξ ⊢ B ⊒ B′} →
    (V at[ down ] (id ； (p ↦ q))) · W
      —→[ idˢ ]
    id-step-term ((V · (W at[ up ] p)) at[ down ] q)

  β-ν :
    ∀ {Ψ}{Σ : Store 0 Ψ}
      {A B : Ty 0 Ψ}
      {N : 0 ∣ (suc Ψ) ∣ ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ) ∣ (⤊ˢ []) ⊢ (⇑ˢ B)} →
    (ν:= A ∙ N) —→[ Sˢ ] N

  at-id-up :
    ∀ {Ψ}{Σ : Store 0 Ψ}{A : Ty 0 Ψ}{Φ Ξ : Vec Bool Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A} →
    (V at[ up ] (id {Φ = Φ} {Ξ = Ξ})) —→[ idˢ ] id-step-term V

  at-id-down :
    ∀ {Ψ}{Σ : Store 0 Ψ}{A : Ty 0 Ψ}{Φ Ξ : Vec Bool Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A} →
    (V at[ down ] (id {Φ = Φ} {Ξ = Ξ})) —→[ idˢ ] id-step-term V

  at-up-tag-at-down-untag :
    ∀ {Ψ}{Σ : Store 0 Ψ}{G : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ G}
      {g g′ : Ground G}
      {gok : ⊢ g ok none Ψ}
      {gok′ : ⊢ g′ ok every Ψ}
      {ℓ ℓ′ : Label} →
    ((V at[ up ] ((id {Φ = none Ψ} {Ξ = none Ψ}) ； tag g gok ℓ))
      at[ down ] ((id {Φ = none Ψ} {Ξ = every Ψ}) ； untag g′ gok′ ℓ′))
    —→[ idˢ ]
    id-step-term V

  at-up-tag-at-down-untag-bad :
    ∀ {Ψ}{Σ : Store 0 Ψ}{G H : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ G}
      {g : Ground G}{h : Ground H}
      {gok : ⊢ g ok none Ψ}
      {hok : ⊢ h ok every Ψ}
      {ℓ ℓ′ : Label} →
    G ≢ H →
    ((V at[ up ] ((id {Φ = none Ψ} {Ξ = none Ψ}) ； tag g gok ℓ))
      at[ down ] ((id {Φ = none Ψ} {Ξ = every Ψ}) ； untag h hok ℓ′))
    —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = []} {A = H} (blame {A = H} ℓ′)

  β-at-up-； :
    ∀ {Ψ}{Σ : Store 0 Ψ}
      {A B C : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
      {p : Σ ∣ every Ψ ∣ none Ψ ⊢ A ⊑ B}
      {q : Σ ∣ every Ψ ∣ none Ψ ⊢ B ⊑ C} →
    V at[ up ] (p ； q) —→[ idˢ ] id-step-term ((V at[ up ] p) at[ up ] q)

  β-at-down-； :
    ∀ {Ψ}{Σ : Store 0 Ψ}
      {A B C : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
      {p : Σ ∣ none Ψ ∣ every Ψ ⊢ A ⊒ B}
      {q : Σ ∣ none Ψ ∣ every Ψ ⊢ B ⊒ C} →
    V at[ down ] (p ； q) —→[ idˢ ] id-step-term ((V at[ down ] p) at[ down ] q)

  β-at-up-ν :
    ∀ {Ψ}{Σ : Store 0 Ψ}
      {A : Ty (suc 0) Ψ}
      {B : Ty 0 Ψ}
      {p : ((Zˢ , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ true ∷ every Ψ ∣ false ∷ none Ψ ⊢ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ⊑ ⇑ˢ B}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (`∀ A)} →
    V at[ up ] (id ； ν p) —→[ idˢ ]
    id-step-term
      (ν:= ★ ∙
        ((((wkΣ-term (drop ⊆ˢ-refl) (⇑ˢᵐ V))
            • Zˢ [ top★-lookup ]) refl)
          at[ up ] p))

  ξ-·₁ :
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store 0 Ψ}{Σ′ : Store 0 Ψ′}
      {A B : Ty 0 Ψ}
      {L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (A ⇒ B)}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
      {L′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ (A ⇒ B)} →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    L —→[ ρ ] L′ →
    (L · M) —→[ ρ ] (L′ · wkΣ-term wρ (renameˢ-term ρ M))

  ξ-·₂ :
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store 0 Ψ}{Σ′ : Store 0 Ψ′}
      {A B : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (A ⇒ B)}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
      {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A} →
    Value V →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    M —→[ ρ ] M′ →
    (V · M) —→[ ρ ] (wkΣ-term wρ (renameˢ-term ρ V) · M′)

  ξ-·α :
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store 0 Ψ}{Σ′ : Store 0 Ψ′}
      {A : Ty (suc 0) Ψ}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (`∀ A)}
      {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ (`∀ A)}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    M —→[ ρ ] M′ →
    ((M • α [ h ]) refl)
      —→[ ρ ]
    cast⊢
      refl
      refl
      (sym (renameˢ-[]ᵗ-seal ρ A α))
      ((M′ • (ρ α) [ wkLookupˢ wρ (renameLookupˢ ρ h) ]) refl)

  ξ-at-up :
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store 0 Ψ}{Σ′ : Store 0 Ψ′}
      {A B : Ty 0 Ψ}
      {Φ Ξ : Vec Bool Ψ}
      {p : Cast up Σ Φ Ξ A B}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
      {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A} →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    M —→[ ρ ] M′ →
    (M at[ up ] p) —→[ ρ ] (M′ at[ up ] wkCast up wρ (renameCastˢ up ρ p))

  ξ-at-down :
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store 0 Ψ}{Σ′ : Store 0 Ψ′}
      {A B : Ty 0 Ψ}
      {Φ Ξ : Vec Bool Ψ}
      {p : Cast down Σ Φ Ξ A B}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
      {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A} →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    M —→[ ρ ] M′ →
    (M at[ down ] p) —→[ ρ ] (M′ at[ down ] wkCast down wρ (renameCastˢ down ρ p))

  ξ-⊕₁ :
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store 0 Ψ}{Σ′ : Store 0 Ψ′}
      {L M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)}
      {L′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ (‵ `ℕ)}
      {op : Prim} →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    L —→[ ρ ] L′ →
    (L ⊕[ op ] M) —→[ ρ ] (L′ ⊕[ op ] wkΣ-term wρ (renameˢ-term ρ M))

  ξ-⊕₂ :
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store 0 Ψ}{Σ′ : Store 0 Ψ′}
      {L M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)}
      {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ (‵ `ℕ)}
      {op : Prim} →
    Value L →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    M —→[ ρ ] M′ →
    (L ⊕[ op ] M) —→[ ρ ] (wkΣ-term wρ (renameˢ-term ρ L) ⊕[ op ] M′)

  δ-⊕ :
    ∀ {Ψ}{Σ : Store 0 Ψ}
      {m n : ℕ} →
    ($ {Δ = 0} {Ψ = Ψ} {Σ = Σ} {Γ = []} (κℕ m) refl
      ⊕[ addℕ ]
      $ {Δ = 0} {Ψ = Ψ} {Σ = Σ} {Γ = []} (κℕ n) refl)
      —→[ idˢ ]
    id-step-term ($ {Δ = 0} {Ψ = Ψ} {Σ = Σ} {Γ = []} (κℕ (m + n)) refl)

  blame-·₁ :
    ∀ {Ψ}{Σ : Store 0 Ψ}{A B : Ty 0 Ψ}
      {ℓ : Label}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A} →
    (blame {A = A ⇒ B} ℓ · M) —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = []} {A = B} (blame {A = B} ℓ)

  blame-·₂ :
    ∀ {Ψ}{Σ : Store 0 Ψ}{A B : Ty 0 Ψ}
      {ℓ : Label}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (A ⇒ B)} →
    Value V →
    (V · blame {A = A} ℓ) —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = []} {A = B} (blame {A = B} ℓ)

  blame-·α :
    ∀ {Ψ}{Σ : Store 0 Ψ}
      {A : Ty (suc 0) Ψ}
      {ℓ : Label}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    ((blame {A = `∀ A} ℓ • α [ h ]) refl)
      —→[ idˢ ]
    id-step-term
      {Σ = Σ}
      {Γ = []}
      {A = A [ ｀ α ]ᵗ}
      (blame {A = A [ ｀ α ]ᵗ} ℓ)

  blame-at :
    ∀ {Ψ}{Σ : Store 0 Ψ}
      {A B : Ty 0 Ψ}
      {d : Direction}
      {Φ Ξ : Vec Bool Ψ}
      {p : Cast d Σ Φ Ξ A B}
      {ℓ : Label} →
    ((blame {A = A} ℓ) at[ d ] p)
      —→[ idˢ ]
    id-step-term
      {Σ = Σ}
      {Γ = []}
      {A = B}
      (blame {A = B} ℓ)

  blame-⊕₁ :
    ∀ {Ψ}{Σ : Store 0 Ψ}
      {ℓ : Label}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)}
      {op : Prim} →
    (blame {A = ‵ `ℕ} ℓ ⊕[ op ] M) —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = []} {A = ‵ `ℕ} (blame {A = ‵ `ℕ} ℓ)

  blame-⊕₂ :
    ∀ {Ψ}{Σ : Store 0 Ψ}
      {ℓ : Label}
      {L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)}
      {op : Prim} →
    Value L →
    (L ⊕[ op ] blame {A = ‵ `ℕ} ℓ) —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = []} {A = ‵ `ℕ} (blame {A = ‵ `ℕ} ℓ)

------------------------------------------------------------------------
-- Store growth witness extracted from one step
------------------------------------------------------------------------

store-growth :
  ∀ {Ψ}{Ψ′}{Σ : Store 0 Ψ}{Σ′ : Store 0 Ψ′}{A : Ty 0 Ψ}
    {ρ : Renameˢ Ψ Ψ′}
    {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
    {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A} →
  M —→[ ρ ] M′ →
  renameStoreˢ ρ Σ ⊆ˢ Σ′
store-growth (β v) = idˢ-⊆ˢ
store-growth β-Λ = idˢ-⊆ˢ
store-growth β-at-up-∀ = idˢ-⊆ˢ
store-growth β-at-down-∀ = idˢ-⊆ˢ
store-growth (β-at-down-ν {A = A} {B = B}) = idˢ-⊆ˢ
store-growth β-at-up-↦ = idˢ-⊆ˢ
store-growth β-at-down-↦ = idˢ-⊆ˢ
store-growth β-ν = drop ⊆ˢ-refl
store-growth at-id-up = idˢ-⊆ˢ
store-growth at-id-down = idˢ-⊆ˢ
store-growth at-up-tag-at-down-untag = idˢ-⊆ˢ
store-growth (at-up-tag-at-down-untag-bad neq) = idˢ-⊆ˢ
store-growth β-at-up-； = idˢ-⊆ˢ
store-growth β-at-down-； = idˢ-⊆ˢ
store-growth β-at-up-ν = idˢ-⊆ˢ
store-growth (ξ-·₁ wρ red) = wρ
store-growth (ξ-·₂ v wρ red) = wρ
store-growth (ξ-·α wρ red) = wρ
store-growth (ξ-at-up wρ red) = wρ
store-growth (ξ-at-down wρ red) = wρ
store-growth (ξ-⊕₁ wρ red) = wρ
store-growth (ξ-⊕₂ v wρ red) = wρ
store-growth δ-⊕ = idˢ-⊆ˢ
store-growth blame-·₁ = idˢ-⊆ˢ
store-growth (blame-·₂ v) = idˢ-⊆ˢ
store-growth blame-·α = idˢ-⊆ˢ
store-growth blame-at = idˢ-⊆ˢ
store-growth blame-⊕₁ = idˢ-⊆ˢ
store-growth (blame-⊕₂ v) = idˢ-⊆ˢ

unique-store-step :
  ∀ {Ψ}{Ψ′}{Σ : Store 0 Ψ}{Σ′ : Store 0 Ψ′}{A : Ty 0 Ψ}
    {ρ : Renameˢ Ψ Ψ′}
    {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
    {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A} →
  Uniqueˢ Σ →
  M —→[ ρ ] M′ →
  Uniqueˢ Σ′
unique-store-step uΣ (β v) = uΣ
unique-store-step uΣ β-Λ = uΣ
unique-store-step uΣ β-at-up-∀ = uΣ
unique-store-step uΣ β-at-down-∀ = uΣ
unique-store-step uΣ (β-at-down-ν {A = A} {B = B}) = uΣ
unique-store-step uΣ β-at-up-↦ = uΣ
unique-store-step uΣ β-at-down-↦ = uΣ
unique-store-step uΣ (β-ν {A = A}) = unique-ν A uΣ
unique-store-step uΣ at-id-up = uΣ
unique-store-step uΣ at-id-down = uΣ
unique-store-step uΣ at-up-tag-at-down-untag = uΣ
unique-store-step uΣ (at-up-tag-at-down-untag-bad neq) = uΣ
unique-store-step uΣ β-at-up-； = uΣ
unique-store-step uΣ β-at-down-； = uΣ
unique-store-step uΣ β-at-up-ν = uΣ
unique-store-step uΣ (ξ-·₁ wρ red) = unique-store-step uΣ red
unique-store-step uΣ (ξ-·₂ v wρ red) = unique-store-step uΣ red
unique-store-step uΣ (ξ-·α wρ red) = unique-store-step uΣ red
unique-store-step uΣ (ξ-at-up wρ red) = unique-store-step uΣ red
unique-store-step uΣ (ξ-at-down wρ red) = unique-store-step uΣ red
unique-store-step uΣ (ξ-⊕₁ wρ red) = unique-store-step uΣ red
unique-store-step uΣ (ξ-⊕₂ v wρ red) = unique-store-step uΣ red
unique-store-step uΣ δ-⊕ = uΣ
unique-store-step uΣ blame-·₁ = uΣ
unique-store-step uΣ (blame-·₂ v) = uΣ
unique-store-step uΣ blame-·α = uΣ
unique-store-step uΣ blame-at = uΣ
unique-store-step uΣ blame-⊕₁ = uΣ
unique-store-step uΣ (blame-⊕₂ v) = uΣ

------------------------------------------------------------------------
-- Multi-step reduction on intrinsic closed terms
------------------------------------------------------------------------

infix 2 _—↠_
infix 3 _∎
infixr 2 _—→⟨_⟩_
infixr 2 _—↠⟨_⟩_

data _—↠_ :
  ∀ {Ψ}{Σ : Store 0 Ψ}{A : Ty 0 Ψ} →
  (L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A) →
  ∀ {Ψ′}{Σ′ : Store 0 Ψ′}{A′ : Ty 0 Ψ′} →
  (N : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ A′) →
  Set where
  _∎ :
    ∀ {Ψ}{Σ : Store 0 Ψ}{A : Ty 0 Ψ}
      (M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A) →
    M —↠ M

  _—→⟨_⟩_ :
    ∀ {Ψ}{Σ : Store 0 Ψ}{A : Ty 0 Ψ}
      (L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A)
      {Ψ′}{Σ′ : Store 0 Ψ′}
      {ρ : Renameˢ Ψ Ψ′}
      {M : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A}
      {Ψ″}{Σ″ : Store 0 Ψ″}
      {B : Ty 0 Ψ″}
      {N : 0 ∣ Ψ″ ∣ Σ″ ∣ [] ⊢ B} →
    L —→[ ρ ] M →
    M —↠ N →
    L —↠ N

multi-trans :
  ∀ {Ψ}{Σ : Store 0 Ψ}{A : Ty 0 Ψ}
    {L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
    {Ψ′}{Σ′ : Store 0 Ψ′}
    {B : Ty 0 Ψ′}
    {M : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ B}
    {Ψ″}{Σ″ : Store 0 Ψ″}
    {C : Ty 0 Ψ″}
    {N : 0 ∣ Ψ″ ∣ Σ″ ∣ [] ⊢ C} →
  L —↠ M →
  M —↠ N →
  L —↠ N
multi-trans (_ ∎) M—↠N = M—↠N
multi-trans (_ —→⟨ L—→M ⟩ M—↠N) N—↠P =
  _ —→⟨ L—→M ⟩ multi-trans M—↠N N—↠P

_—↠⟨_⟩_ :
  ∀ {Ψ}{Σ : Store 0 Ψ}{A : Ty 0 Ψ}
    (L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A)
    {Ψ′}{Σ′ : Store 0 Ψ′}
    {B : Ty 0 Ψ′}
    {M : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ B}
    {Ψ″}{Σ″ : Store 0 Ψ″}
    {C : Ty 0 Ψ″}
    {N : 0 ∣ Ψ″ ∣ Σ″ ∣ [] ⊢ C} →
  L —↠ M →
  M —↠ N →
  L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N = multi-trans L—↠M M—↠N
