module Coerce where

open import Agda.Builtin.Sigma renaming (Σ to Σ′)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)
  renaming (subst to substEq)

open import Types
open import Consistency
open import Coercions
open import Store using ()

data SealBinder : Set where
  bound-by-𝒢 : SealBinder
  bound-by-ℐ : SealBinder

data BinderCtx : ∀{Ψ} → List SealBinder → Store Ψ → Set where
  [] : ∀{Ψ}{Σ : Store Ψ} → BinderCtx [] Σ
  _∷_ : ∀{Ψ}{Σ : Store Ψ}{b bs} →
    BinderCtx bs Σ →
    BinderCtx (b ∷ bs) ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ)

Sˢ-injective :
  ∀{Ψ}{α β : Seal Ψ} →
  Sˢ α ≡ Sˢ β →
  α ≡ β
Sˢ-injective refl = refl

lookup-Sˢ-⟰ˢ′ :
  ∀{Ψ}{Σ : Store Ψ}{α : Seal Ψ}{A : Ty 0 (suc Ψ)} →
  ⟰ˢ Σ ∋ˢ Sˢ α ⦂ A →
  Σ′ (Ty 0 Ψ) (λ B → (A ≡ ⇑ˢ B) × (Σ ∋ˢ α ⦂ B))
lookup-Sˢ-⟰ˢ′ {Σ = []} ()
lookup-Sˢ-⟰ˢ′ {Σ = (β , B) ∷ Σ} (Z∋ˢ α≡β A≡B) =
  B , A≡B , Z∋ˢ (Sˢ-injective α≡β) refl
lookup-Sˢ-⟰ˢ′ {Σ = (β , B) ∷ Σ} (S∋ˢ h)
  with lookup-Sˢ-⟰ˢ′ {Σ = Σ} h
... | C , A≡C , hC = C , A≡C , S∋ˢ hC

lookup-Z-⟰ˢ-⊥ :
  ∀{Ψ}{Σ : Store Ψ}{A : Ty 0 (suc Ψ)} →
  ⟰ˢ Σ ∋ˢ Zˢ ⦂ A →
  ⊥
lookup-Z-⟰ˢ-⊥ {Σ = []} ()
lookup-Z-⟰ˢ-⊥ {Σ = (_ , _) ∷ Σ} (Z∋ˢ () _)
lookup-Z-⟰ˢ-⊥ {Σ = (_ , _) ∷ Σ} (S∋ˢ h) = lookup-Z-⟰ˢ-⊥ h

lookup-𝒢 :
  ∀{Ψ}{Σ : Store Ψ}{bs}{ctx : BinderCtx bs Σ}{α : Seal Ψ}{A : Ty 0 Ψ} →
  Σ ∋ˢ α ⦂ A →
  Maybe (A ≡ `★)
lookup-𝒢 {ctx = []} h = nothing
lookup-𝒢 {ctx = _∷_ {b = bound-by-ℐ} ctx} {α = Zˢ} h = nothing
lookup-𝒢 {ctx = _∷_ {b = bound-by-𝒢} ctx} {α = Zˢ} (Z∋ˢ refl A≡★) = just A≡★
lookup-𝒢 {ctx = _∷_ {b = bound-by-𝒢} ctx} {α = Zˢ} (S∋ˢ h) =
  ⊥-elim (lookup-Z-⟰ˢ-⊥ h)
lookup-𝒢 {ctx = _∷_ ctx} {α = Sˢ α} (Z∋ˢ () _)
lookup-𝒢 {ctx = _∷_ ctx} {α = Sˢ α} (S∋ˢ h)
  with lookup-Sˢ-⟰ˢ′ h
... | B , A≡⇑B , hB
  with lookup-𝒢 {ctx = ctx} hB
... | nothing = nothing
... | just B≡★ rewrite B≡★ = just A≡⇑B

seal-coerce :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{α : Seal Ψ}{A : Ty 0 Ψ} →
  (bs : List SealBinder) →
  BinderCtx bs Σ →
  Label →
  Σ ∋ˢ α ⦂ A →
  Σ ⊢ wkTy0 {Δ = Δ} A ⇨ᵃ ｀ α
seal-coerce {α = α} bs ctx l h
  with lookup-𝒢 {ctx = ctx} h
... | nothing = h ⁻
... | just A≡★ rewrite A≡★ = (｀ α) `? l

unseal-coerce :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{α : Seal Ψ}{A : Ty 0 Ψ} →
  (bs : List SealBinder) →
  BinderCtx bs Σ →
  Label →
  Σ ∋ˢ α ⦂ A →
  Σ ⊢ ｀ α ⇨ᵃ wkTy0 {Δ = Δ} A
unseal-coerce {α = α} bs ctx l h
  with lookup-𝒢 {ctx = ctx} h
... | nothing = h ⁺
... | just A≡★ rewrite A≡★ = (｀ α) !

coerce :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
  (bs : List SealBinder) →
  BinderCtx bs Σ →
  Label →
  Σ ⊢ A ~ B →
  Σ ⊢ A ⇨ B
coerce bs ctx l X~X = id
coerce bs ctx l α~α = id
coerce bs ctx l ι~ι = id
coerce bs ctx l ★~★ = id
coerce bs ctx l (★~G g) = 〔 g `? l 〕
coerce bs ctx l (G~★ g) = 〔 g ! 〕
coerce bs ctx l (★~⇒ c d) = 〔 ★⇒★ `? l 〕 ⨟ 〔 coerce bs ctx l c ↦ coerce bs ctx l d 〕
coerce bs ctx l (⇒~★ c d) = 〔 coerce bs ctx l c ↦ coerce bs ctx l d 〕 ⨟ 〔 ★⇒★ ! 〕
coerce bs ctx l (A~α h eq)
    with eq
... | refl = 〔 seal-coerce bs ctx l h 〕
coerce bs ctx l (A~α* h c) = coerce bs ctx l c ⨟ 〔 seal-coerce bs ctx l h 〕
coerce bs ctx l (α~A h eq)
    with eq
... | refl = 〔 unseal-coerce bs ctx l h 〕
coerce bs ctx l (α~A* h c) = 〔 unseal-coerce bs ctx l h 〕 ⨟ coerce bs ctx l c
coerce bs ctx l (↦~↦ c d) = 〔 coerce bs ctx l c ↦ coerce bs ctx l d 〕
coerce bs ctx l (∀~∀ c) = 〔 ∀ᶜ (coerce bs ctx l c) 〕
coerce bs ctx l (∀~ c) = 〔 ℐ (coerce (bound-by-ℐ ∷ bs) (_∷_ ctx) l c) 〕
coerce bs ctx l (~∀ c) = 〔 𝒢 (coerce (bound-by-𝒢 ∷ bs) (_∷_ ctx) l c) 〕
