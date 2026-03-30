module Reduction where

-- File Charter:
--   * Dynamic semantics (values and one-step/multi-step reduction) for PolyImp terms.
--   * Casts are `_at_` with up/down wrappers over imprecision witnesses.
--   * No separate imprecision-reduction relation is needed.
-- Note to self:
--   * Place substitution-specific facts in `TermSubst.agda`.

open import Data.Nat using (ℕ; _+_; suc; zero)
open import Data.List using ([]; _∷_; map)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; cong₂; subst; sym; trans; refl)
open import Types
open import Store
open import Imprecision
open import PolyImp
open import TypeSubst using (renameLookupˢ; renameˢ-single-⇑ˢ-id)
open import TermSubst

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data Value : ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A → Set where
  V-ƛ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A B : Ty Δ Ψ}
    {N : Δ ∣ Ψ ∣ Σ ∣ (A ∷ Γ) ⊢ B} →
    Value (ƛ A ⇒ N)

  V-const :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{κ : Const} →
    Value ($ {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ} κ refl)

  V-Λ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty (suc Δ) Ψ}
    {N : (suc Δ) ∣ Ψ ∣ Σ ∣ (⤊ᵗ Γ) ⊢ A} →
    Value (Λ N)

  V-at-up-tag :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{G : Ty Δ Ψ}
    {g : Ground G}{ℓ : Label}{V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ G} →
    Value V →
    Value (V at[ up ] (id ； tag g ℓ))

  V-at-down-seal :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty 0 Ψ}{α}
    {h : Σ ∋ˢ α ⦂ A}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ wkTy0 A} →
    Value V →
    Value (V at[ down ] (id ； seal h))

  V-at-up-↦ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A B C D : Ty Δ Ψ}
    {p : Σ ⊢ C ⊑ A}{q : Σ ⊢ B ⊑ D}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)} →
    Value V →
    Value (V at[ up ] (id ； (p ↦ q)))

  V-at-down-↦ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A B C D : Ty Δ Ψ}
    {p : Σ ⊢ C ⊑ A}{q : Σ ⊢ B ⊑ D}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (C ⇒ D)} →
    Value V →
    Value (V at[ down ] (id ； (p ↦ q)))

  V-at-up-∀ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
    {A B : Ty (suc Δ) Ψ}
    {p : Σ ⊢ A ⊑ B}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A)} →
    Value V →
    Value (V at[ up ] (id ； (∀ᵖ p)))

  V-at-down-∀ :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}
    {A B : Ty (suc Δ) Ψ}
    {p : Σ ⊢ A ⊑ B}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ B)} →
    Value V →
    Value (V at[ down ] (id ； (∀ᵖ p)))

  V-at-down-ν :
    ∀{Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty (suc Δ) Ψ}{B : Ty Δ Ψ}
    {i : ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ⊑ (⇑ˢ B)}
    {V : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B} →
    Value V →
    Value {A = `∀ A} (V at[ down ] (id ； (ν i)))

------------------------------------------------------------------------
-- One-step reduction
------------------------------------------------------------------------

idˢ : ∀{Ψ} → Renameˢ Ψ Ψ
idˢ α = α

renameˢ-id :
  ∀{Δ}{Ψ}{A : Ty Δ Ψ} →
  renameˢ idˢ A ≡ A
renameˢ-id {A = ＇ X} = refl
renameˢ-id {A = ｀ α} = refl
renameˢ-id {A = ‵ ι} = refl
renameˢ-id {A = `★} = refl
renameˢ-id {A = A ⇒ B} = cong₂ _⇒_ renameˢ-id renameˢ-id
renameˢ-id {A = `∀ A} = cong `∀ renameˢ-id

map-renameˢ-id :
  ∀{Δ}{Ψ} →
  (Γ : Ctx Δ Ψ) →
  map (renameˢ idˢ) Γ ≡ Γ
map-renameˢ-id [] = refl
map-renameˢ-id (A ∷ Γ) = cong₂ _∷_ renameˢ-id (map-renameˢ-id Γ)

renameStoreˢ-id :
  ∀{Ψ}{Σ : Store Ψ} →
  renameStoreˢ idˢ Σ ≡ Σ
renameStoreˢ-id {Σ = []} = refl
renameStoreˢ-id {Σ = ((α , A) ∷ Σ)} =
  cong₂ _∷_
    (cong₂ _,_ refl renameˢ-id)
    renameStoreˢ-id

idˢ-⊆ˢ :
  ∀{Ψ}{Σ : Store Ψ} →
  renameStoreˢ idˢ Σ ⊆ˢ Σ
idˢ-⊆ˢ {Σ = Σ} rewrite renameStoreˢ-id {Σ = Σ} = ⊆ˢ-refl

id-step-term :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ ∣ Σ ∣ map (renameˢ idˢ) Γ ⊢ renameˢ idˢ A
id-step-term {Γ = Γ} {A = A} M =
  cast⊢
    refl
    (sym (map-renameˢ-id Γ))
    (sym renameˢ-id)
    M

id-step :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ ∣ Σ ∣ map (renameˢ idˢ) Γ ⊢ renameˢ idˢ A
id-step = id-step-term

infixr 8 _▹_
_▹_ :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{Γ : Ctx Δ Ψ}{A B : Ty Δ Ψ} →
  A ≡ B →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B
_▹_ A≡B = cast⊢ refl refl A≡B

dir-src-∀ :
  ∀ {Ψ} (d : Direction) (A B : Ty (suc 0) Ψ) →
  dir-src d (`∀ A) (`∀ B) ≡ `∀ (dir-src d A B)
dir-src-∀ up A B = refl
dir-src-∀ down A B = refl

dir-tgt-∀ :
  ∀ {Ψ} (d : Direction) (A B : Ty (suc 0) Ψ) →
  dir-tgt d (`∀ A) (`∀ B) ≡ `∀ (dir-tgt d A B)
dir-tgt-∀ up A B = refl
dir-tgt-∀ down A B = refl

dir-src-⇒ :
  ∀ {Ψ} (d : Direction) (A B C D : Ty 0 Ψ) →
  dir-src d (A ⇒ B) (C ⇒ D) ≡ (dir-src d A C ⇒ dir-src d B D)
dir-src-⇒ up A B C D = refl
dir-src-⇒ down A B C D = refl

dir-tgt-⇒ :
  ∀ {Ψ} (d : Direction) (A B C D : Ty 0 Ψ) →
  dir-tgt d (A ⇒ B) (C ⇒ D) ≡ (dir-tgt d A C ⇒ dir-tgt d B D)
dir-tgt-⇒ up A B C D = refl
dir-tgt-⇒ down A B C D = refl

dir-src-[]ᵗ :
  ∀ {Ψ} (d : Direction) (A B : Ty (suc 0) Ψ) (α : Seal Ψ) →
  dir-src d (A [ ｀ α ]ᵗ) (B [ ｀ α ]ᵗ) ≡ (dir-src d A B) [ ｀ α ]ᵗ
dir-src-[]ᵗ up A B α = refl
dir-src-[]ᵗ down A B α = refl

dir-tgt-[]ᵗ :
  ∀ {Ψ} (d : Direction) (A B : Ty (suc 0) Ψ) (α : Seal Ψ) →
  dir-tgt d (A [ ｀ α ]ᵗ) (B [ ｀ α ]ᵗ) ≡ (dir-tgt d A B) [ ｀ α ]ᵗ
dir-tgt-[]ᵗ up A B α = refl
dir-tgt-[]ᵗ down A B α = refl

dir-tgt-src-swap :
  ∀ {Δ}{Ψ} (d : Direction) (A B : Ty Δ Ψ) →
  dir-tgt d A B ≡ dir-src d B A
dir-tgt-src-swap up A B = refl
dir-tgt-src-swap down A B = refl

dir-src-tgt-refl :
  ∀ {Δ}{Ψ} (d : Direction) (A : Ty Δ Ψ) →
  dir-src d A A ≡ dir-tgt d A A
dir-src-tgt-refl up A = refl
dir-src-tgt-refl down A = refl

top★-lookup :
  ∀ {Ψ}{Σ : Store Ψ} →
  ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ∋ˢ Zˢ ⦂ `★
top★-lookup = Z∋ˢ refl refl

removeAtˢ :
  ∀ {Ψ}{Σ : Store Ψ}{α : Seal Ψ}{A : Ty 0 Ψ} →
  Σ ∋ˢ α ⦂ A →
  Store Ψ
removeAtˢ {Σ = (_ , _) ∷ Σ} (Z∋ˢ _ _) = Σ
removeAtˢ {Σ = (β , B) ∷ Σ} (S∋ˢ h) = (β , B) ∷ removeAtˢ h

data DropLookup
  {Ψ}{Σ : Store Ψ}{α : Seal Ψ}
  (h★ : Σ ∋ˢ α ⦂ `★)
  {β : Seal Ψ}{B : Ty 0 Ψ}
  (h : Σ ∋ˢ β ⦂ B) : Set where
  drop-hit :
    β ≡ α →
    B ≡ `★ →
    DropLookup h★ h
  drop-keep :
    removeAtˢ h★ ∋ˢ β ⦂ B →
    DropLookup h★ h

dropLookup :
  ∀ {Ψ}{Σ : Store Ψ}{α : Seal Ψ}
    (h★ : Σ ∋ˢ α ⦂ `★)
    {β : Seal Ψ}{B : Ty 0 Ψ}
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
  ∀ {Ψ}{Σ : Store Ψ}{α : Seal Ψ}{A : Ty 0 Ψ}
    (h : Σ ∋ˢ α ⦂ A) →
  removeAtˢ (renameLookupˢ Sˢ h) ≡ ⟰ˢ (removeAtˢ h)
removeAtˢ-renameLookup-S (Z∋ˢ _ _) = refl
removeAtˢ-renameLookup-S {Σ = (β , B) ∷ Σ} (S∋ˢ h) =
  cong₂ _∷_ refl (removeAtˢ-renameLookup-S h)

removeAtˢ-ν-lift :
  ∀ {Ψ}{Σ : Store Ψ}{α : Seal Ψ}
    (h★ : Σ ∋ˢ α ⦂ `★) →
  removeAtˢ (S∋ˢ (renameLookupˢ Sˢ h★))
    ≡ ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ (removeAtˢ h★))
removeAtˢ-ν-lift h★ = cong₂ _∷_ refl (removeAtˢ-renameLookup-S h★)

mutual
  drop★-atom :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{α : Seal Ψ}{A B : Ty Δ Ψ} →
    (h★ : Σ ∋ˢ α ⦂ `★) →
    Σ ⊢ A ⊑ᵃ B →
    removeAtˢ h★ ⊢ A ⊑ B
  drop★-atom h★ (tag g ℓ) = 〔 tag g ℓ 〕
  drop★-atom h★ (`⊥ ℓ) = 〔 `⊥ ℓ 〕
  drop★-atom {α = α} h★ (seal h) with dropLookup h★ h
  ... | drop-keep h′ = 〔 seal h′ 〕
  ... | drop-hit β≡α B≡★ =
    castᵖ
      refl
      (cong ｀_ (sym β≡α))
      (sym (cong wkTy0 B≡★))
      (〔 tag (｀ α) zero 〕)
  drop★-atom h★ (p ↦ q) = 〔 drop★ h★ p ↦ drop★ h★ q 〕
  drop★-atom h★ (∀ᵖ p) = 〔 ∀ᵖ (drop★ h★ p) 〕
  drop★-atom h★ (ν i) =
    〔 ν (castᵖ
           (removeAtˢ-ν-lift h★)
           refl
           refl
           (drop★ (S∋ˢ (renameLookupˢ Sˢ h★)) i)) 〕

  drop★ :
    ∀ {Δ}{Ψ}{Σ : Store Ψ}{α : Seal Ψ}{A B : Ty Δ Ψ} →
    (h★ : Σ ∋ˢ α ⦂ `★) →
    Σ ⊢ A ⊑ B →
    removeAtˢ h★ ⊢ A ⊑ B
  drop★ h★ id = id
  drop★ h★ (p ； a) = drop★ h★ p ⨟ drop★-atom h★ a

openν :
  ∀ {Ψ}{Σ : Store Ψ}
    {A : Ty (suc 0) Ψ}
    {B : Ty 0 Ψ} →
  (i : ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ⊑ (⇑ˢ B)) →
  (α : Seal Ψ) →
  Σ ⊢ (A [ ｀ α ]ᵗ) ⊑ B
openν {Σ = Σ} {A = A} {B = B} i α =
  drop★ top★
    (castᵖ
      Σ-eq
      src-eq
      tgt-eq
      (renameᵖˢ (singleSealEnv α) i))
  where
    top★ :
      ((α , `★) ∷ Σ) ∋ˢ α ⦂ `★
    top★ = Z∋ˢ refl refl

    Σ-eq :
      renameStoreˢ (singleSealEnv α) ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ≡ ((α , `★) ∷ Σ)
    Σ-eq =
      cong₂ _∷_
        (cong₂ _,_ refl (renameˢ-single-⇑ˢ-id α `★))
        (renameStoreˢ-single-⟰ˢ α Σ)

    src-eq :
      renameˢ (singleSealEnv α) ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ≡ (A [ ｀ α ]ᵗ)
    src-eq =
      trans
        (renameˢ-[]ᵗ-sealᵖ (singleSealEnv α) (⇑ˢ A) Zˢ)
        (cong (λ T → T [ ｀ α ]ᵗ) (renameˢ-single-⇑ˢ-id α A))

    tgt-eq :
      renameˢ (singleSealEnv α) (⇑ˢ B) ≡ B
    tgt-eq = renameˢ-single-⇑ˢ-id α B

infix 2 _—→[_]_
data _—→[_]_ :
  ∀ {Ψ}{Ψ′}{Σ : Store Ψ}{Σ′ : Store Ψ′}{A : Ty 0 Ψ} →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ A →
  (ρ : Renameˢ Ψ Ψ′) →
  0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A → Set where

  β :
    ∀ {Ψ}{Σ : Store Ψ}{A B : Ty 0 Ψ}
      {N : 0 ∣ Ψ ∣ Σ ∣ (B ∷ []) ⊢ A}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ B} →
    Value V →
    (ƛ B ⇒ N) · V —→[ idˢ ] id-step-term (N [ V ])

  β-Λ :
    ∀ {Ψ}{Σ : Store Ψ}
      {A : Ty (suc 0) Ψ}
      {V : (suc 0) ∣ Ψ ∣ Σ ∣ (⤊ᵗ []) ⊢ A}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    ((Λ V) ·α α [ h ]) refl —→[ idˢ ] id-step-term (V [ ｀ α ]ᵀ)

  β-at-∀ :
    ∀ {Ψ}{Σ : Store Ψ}
      (d : Direction)
      {A B : Ty (suc 0) Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ dir-src d (`∀ A) (`∀ B)}
      {p : Σ ⊢ A ⊑ B}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    (((dir-tgt-∀ d A B ▹ (V at[ d ]  (〔 (∀ᵖ p) 〕)))
      ·α α [ h ]) refl)
      —→[ idˢ ]
    id-step
      ((dir-tgt-[]ᵗ d A B α ▹
        ((sym (dir-src-[]ᵗ d A B α) ▹
          (((dir-src-∀ d A B ▹ V) ·α α [ h ]) refl))
         at[ d ]  (p [ ｀ α ]ᵖᵗ))))

  β-at-down-ν :
    ∀ {Ψ}{Σ : Store Ψ}
      {A : Ty (suc 0) Ψ}
      {B : Ty 0 Ψ}
      {i : ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ⊑ (⇑ˢ B)}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ B}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    (_·α_[_]
      {Δ = 0} {Ψ = Ψ} {Σ = Σ} {Γ = []}
      {A = A} {C = C}
      (V at[ down ]  (〔 (ν i) 〕)) α h refl)
      —→[ idˢ ]
    id-step-term (V at[ down ]  (openν {A = A} {B = B} i α))

  β-at-↦ :
    ∀ {Ψ}{Σ : Store Ψ}
      (d : Direction)
      {A B C D : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (dir-src d (A ⇒ B) (C ⇒ D))}
      {W : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (dir-tgt d A C)}
      {p : Σ ⊢ C ⊑ A}
      {q : Σ ⊢ B ⊑ D} →
    (dir-tgt-⇒ d A B C D ▹ (V at[ d ]  (〔 (p ↦ q) 〕))) · W
      —→[ idˢ ]
    id-step
      (((dir-src-⇒ d A B C D ▹ V)
        · (dir-tgt-src-swap d C A ▹
            ((dir-tgt-src-swap d A C ▹ W) at[ d ]  p)))
      at[ d ]  q)

  β-ν :
    ∀ {Ψ}{Σ : Store Ψ}
      {A B : Ty 0 Ψ}
      {N : 0 ∣ (suc Ψ) ∣ ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ) ∣ (⤊ˢ []) ⊢ (⇑ˢ B)} →
    (ν:= A ∙ N) —→[ Sˢ ] N

  at-id :
    ∀ {Ψ}{Σ : Store Ψ}{A : Ty 0 Ψ}
      (d : Direction)
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ dir-src d A A} →
    (V at[ d ]  id) —→[ idˢ ]
    id-step-term (cast⊢ refl refl (dir-src-tgt-refl d A) V)

  at-down-seal-at-up-seal-★ :
    ∀ {Ψ}{Σ : Store Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ `★}
      {α}
      {h h′ : Σ ∋ˢ α ⦂ `★} →
    ((V at[ down ]  (〔 (seal h) 〕)) at[ up ]  (〔 seal h′ 〕))
      —→[ idˢ ]
    id-step-term V

  at-down-seal-at-up-seal :
    ∀ {Ψ}{Σ : Store Ψ}{A B : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ wkTy0 A}
      {α}
      {h : Σ ∋ˢ α ⦂ A}
      {h′ : Σ ∋ˢ α ⦂ B}
      (uΣ : Uniqueˢ Σ) →
    ((V at[ down ]  (〔 (seal h) 〕)) at[ up ]  (〔 seal h′ 〕))
      —→[ idˢ ]
    id-step-term
      (subst
        (λ T → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ T)
        (cong wkTy0 (lookup-unique uΣ h h′))
        V)

  at-up-tag-at-down-tag :
    ∀ {Ψ}{Σ : Store Ψ}{G : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ G}
      {g g′ : Ground G}{ℓ ℓ′ : Label} →
    ((V at[ up ]  (〔 (tag g ℓ) 〕)) at[ down ]  (〔 tag g′ ℓ′ 〕))
      —→[ idˢ ]
    id-step-term V

  at-up-tag-at-down-tag-bad :
    ∀ {Ψ}{Σ : Store Ψ}{G H : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ G}
      {g : Ground G}{h : Ground H}{ℓ ℓ′ : Label} →
    G ≢ H →
    ((V at[ up ]  (〔 (tag g ℓ) 〕)) at[ down ]  (〔 tag h ℓ′ 〕))
      —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = []} {A = H} (blame {A = H} ℓ′)

  β-at-up-； :
    ∀ {Ψ}{Σ : Store Ψ}
      {A B C D : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
      {p : Σ ⊢ A ⊑ B}
      {a : Σ ⊢ B ⊑ᵃ C}
      {b : Σ ⊢ C ⊑ᵃ D} →
    V at[ up ]  ((p ； a) ； b) —→[ idˢ ] id-step-term ((V at[ up ]  (p ； a)) at[ up ]  (〔 b 〕))

  β-at-down-； :
    ∀ {Ψ}{Σ : Store Ψ}
      {A B C D : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ D}
      {p : Σ ⊢ A ⊑ B}
      {a : Σ ⊢ B ⊑ᵃ C}
      {b : Σ ⊢ C ⊑ᵃ D} →
    V at[ down ]  ((p ； a) ； b) —→[ idˢ ] id-step-term ((V at[ down ]  (〔 b 〕)) at[ down ]  (p ； a))

  β-at-up-ν :
    ∀ {Ψ}{Σ : Store Ψ}
      {A : Ty (suc 0) Ψ}
      {B : Ty 0 Ψ}
      {i : ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ⊑ (⇑ˢ B)}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (`∀ A)} →
    V at[ up ]  (〔 (ν i) 〕) —→[ idˢ ]
    id-step-term
      (ν:= `★ ∙
        ((((wkΣ-term (drop ⊆ˢ-refl) (renameˢ-term Sˢ V))
            ·α Zˢ [ top★-lookup ]) refl)
          at[ up ]  i))

  β-at-⊥ :
    ∀ {Ψ}{Σ : Store Ψ}
      (d : Direction)
      {A B : Ty 0 Ψ}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ dir-src d A B}
      {ℓ : Label} →
    V at[ d ]  (〔 (`⊥ {A = A} {B = B} ℓ) 〕) —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = []} {A = dir-tgt d A B} (blame {A = dir-tgt d A B} ℓ)

  ξ-·₁ :
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store Ψ}{Σ′ : Store Ψ′}
      {A B : Ty 0 Ψ}
      {L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (A ⇒ B)}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
      {L′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ (A ⇒ B)} →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    L —→[ ρ ] L′ →
    (L · M) —→[ ρ ] (L′ · wkΣ-term wρ (renameˢ-term ρ M))

  ξ-·₂ :
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store Ψ}{Σ′ : Store Ψ′}
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
      {Σ : Store Ψ}{Σ′ : Store Ψ′}
      {A : Ty (suc 0) Ψ}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (`∀ A)}
      {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ (`∀ A)}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    M —→[ ρ ] M′ →
    ((M ·α α [ h ]) refl)
      —→[ ρ ]
    cast⊢
      refl
      refl
      (sym (renameˢ-[]ᵗ-seal ρ A α))
      ((M′ ·α (ρ α) [ wkLookupˢ wρ (renameLookupˢ ρ h) ]) refl)

  ξ-at-up :
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store Ψ}{Σ′ : Store Ψ′}
      {A B : Ty 0 Ψ}
      {p : Σ ⊢ A ⊑ B}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
      {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A} →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    M —→[ ρ ] M′ →
    (M at[ up ] p) —→[ ρ ] (M′ at[ up ] wkΣᵖ wρ (renameᵖˢ ρ p))

  ξ-at-down :
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store Ψ}{Σ′ : Store Ψ′}
      {A B : Ty 0 Ψ}
      {p : Σ ⊢ A ⊑ B}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ B}
      {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ B} →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    M —→[ ρ ] M′ →
    (M at[ down ] p) —→[ ρ ] (M′ at[ down ] wkΣᵖ wρ (renameᵖˢ ρ p))

  ξ-⊕₁ :
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store Ψ}{Σ′ : Store Ψ′}
      {L M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)}
      {L′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ (‵ `ℕ)}
      {op : Prim} →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    L —→[ ρ ] L′ →
    (L ⊕[ op ] M) —→[ ρ ] (L′ ⊕[ op ] wkΣ-term wρ (renameˢ-term ρ M))

  ξ-⊕₂ :
    ∀ {Ψ}{Ψ′}{ρ : Renameˢ Ψ Ψ′}
      {Σ : Store Ψ}{Σ′ : Store Ψ′}
      {L M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)}
      {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ (‵ `ℕ)}
      {op : Prim} →
    Value L →
    (wρ : renameStoreˢ ρ Σ ⊆ˢ Σ′) →
    M —→[ ρ ] M′ →
    (L ⊕[ op ] M) —→[ ρ ] (wkΣ-term wρ (renameˢ-term ρ L) ⊕[ op ] M′)

  δ-⊕ :
    ∀ {Ψ}{Σ : Store Ψ}
      {m n : ℕ} →
    ($ {Δ = 0} {Ψ = Ψ} {Σ = Σ} {Γ = []} (κℕ m) refl
      ⊕[ addℕ ]
      $ {Δ = 0} {Ψ = Ψ} {Σ = Σ} {Γ = []} (κℕ n) refl)
      —→[ idˢ ]
    id-step-term ($ {Δ = 0} {Ψ = Ψ} {Σ = Σ} {Γ = []} (κℕ (m + n)) refl)

  blame-·₁ :
    ∀ {Ψ}{Σ : Store Ψ}{A B : Ty 0 Ψ}
      {ℓ : Label}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A} →
    (blame {A = A ⇒ B} ℓ · M) —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = []} {A = B} (blame {A = B} ℓ)

  blame-·₂ :
    ∀ {Ψ}{Σ : Store Ψ}{A B : Ty 0 Ψ}
      {ℓ : Label}
      {V : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (A ⇒ B)} →
    Value V →
    (V · blame {A = A} ℓ) —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = []} {A = B} (blame {A = B} ℓ)

  blame-·α :
    ∀ {Ψ}{Σ : Store Ψ}
      {A : Ty (suc 0) Ψ}
      {ℓ : Label}
      {α : Seal Ψ}{C : Ty 0 Ψ}
      {h : Σ ∋ˢ α ⦂ C} →
    (_·α_[_]
      {Δ = 0} {Ψ = Ψ} {Σ = Σ} {Γ = []}
      {A = A} {C = C}
      (blame {A = `∀ A} ℓ) α h refl)
      —→[ idˢ ]
    id-step-term
      {Σ = Σ}
      {Γ = []}
      {A = A [ ｀ α ]ᵗ}
      (blame {A = A [ ｀ α ]ᵗ} ℓ)

  blame-at :
    ∀ {Ψ}{Σ : Store Ψ}
      {A B : Ty 0 Ψ}
      {d : Direction}
      {p : Σ ⊢ A ⊑ B}
      {ℓ : Label} →
    ((blame {A = dir-src d A B} ℓ) at[ d ] p)
      —→[ idˢ ]
    id-step-term
      {Σ = Σ}
      {Γ = []}
      {A = dir-tgt d A B}
      (blame {A = dir-tgt d A B} ℓ)

  blame-⊕₁ :
    ∀ {Ψ}{Σ : Store Ψ}
      {ℓ : Label}
      {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)}
      {op : Prim} →
    (blame {A = ‵ `ℕ} ℓ ⊕[ op ] M) —→[ idˢ ]
    id-step-term {Σ = Σ} {Γ = []} {A = ‵ `ℕ} (blame {A = ‵ `ℕ} ℓ)

  blame-⊕₂ :
    ∀ {Ψ}{Σ : Store Ψ}
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
  ∀ {Ψ}{Ψ′}{Σ : Store Ψ}{Σ′ : Store Ψ′}{A : Ty 0 Ψ}
    {ρ : Renameˢ Ψ Ψ′}
    {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
    {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A} →
  M —→[ ρ ] M′ →
  renameStoreˢ ρ Σ ⊆ˢ Σ′
store-growth (β v) = idˢ-⊆ˢ
store-growth β-Λ = idˢ-⊆ˢ
store-growth (β-at-∀ d) = idˢ-⊆ˢ
store-growth β-at-down-ν = idˢ-⊆ˢ
store-growth (β-at-↦ d) = idˢ-⊆ˢ
store-growth β-ν = drop ⊆ˢ-refl
store-growth (at-id d) = idˢ-⊆ˢ
store-growth at-down-seal-at-up-seal-★ = idˢ-⊆ˢ
store-growth (at-down-seal-at-up-seal uΣ) = idˢ-⊆ˢ
store-growth at-up-tag-at-down-tag = idˢ-⊆ˢ
store-growth (at-up-tag-at-down-tag-bad neq) = idˢ-⊆ˢ
store-growth β-at-up-； = idˢ-⊆ˢ
store-growth β-at-down-； = idˢ-⊆ˢ
store-growth β-at-up-ν = idˢ-⊆ˢ
store-growth (β-at-⊥ d) = idˢ-⊆ˢ
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
  ∀ {Ψ}{Ψ′}{Σ : Store Ψ}{Σ′ : Store Ψ′}{A : Ty 0 Ψ}
    {ρ : Renameˢ Ψ Ψ′}
    {M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
    {M′ : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A} →
  Uniqueˢ Σ →
  M —→[ ρ ] M′ →
  Uniqueˢ Σ′
unique-store-step uΣ (β v) = uΣ
unique-store-step uΣ β-Λ = uΣ
unique-store-step uΣ (β-at-∀ d) = uΣ
unique-store-step uΣ β-at-down-ν = uΣ
unique-store-step uΣ (β-at-↦ d) = uΣ
unique-store-step uΣ (β-ν {A = A}) = unique-ν A uΣ
unique-store-step uΣ (at-id d) = uΣ
unique-store-step uΣ at-down-seal-at-up-seal-★ = uΣ
unique-store-step uΣ (at-down-seal-at-up-seal uΣ′) = uΣ
unique-store-step uΣ at-up-tag-at-down-tag = uΣ
unique-store-step uΣ (at-up-tag-at-down-tag-bad neq) = uΣ
unique-store-step uΣ β-at-up-； = uΣ
unique-store-step uΣ β-at-down-； = uΣ
unique-store-step uΣ β-at-up-ν = uΣ
unique-store-step uΣ (β-at-⊥ d) = uΣ
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
  ∀ {Ψ}{Σ : Store Ψ}{A : Ty 0 Ψ} →
  (L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A) →
  ∀ {Ψ′}{Σ′ : Store Ψ′}{A′ : Ty 0 Ψ′} →
  (N : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ A′) →
  Set where
  _∎ :
    ∀ {Ψ}{Σ : Store Ψ}{A : Ty 0 Ψ}
      (M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A) →
    M —↠ M

  _—→⟨_⟩_ :
    ∀ {Ψ}{Σ : Store Ψ}{A : Ty 0 Ψ}
      (L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A)
      {Ψ′}{Σ′ : Store Ψ′}
      {ρ : Renameˢ Ψ Ψ′}
      {M : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ renameˢ ρ A}
      {Ψ″}{Σ″ : Store Ψ″}
      {B : Ty 0 Ψ″}
      {N : 0 ∣ Ψ″ ∣ Σ″ ∣ [] ⊢ B} →
    L —→[ ρ ] M →
    M —↠ N →
    L —↠ N

multi-trans :
  ∀ {Ψ}{Σ : Store Ψ}{A : Ty 0 Ψ}
    {L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A}
    {Ψ′}{Σ′ : Store Ψ′}
    {B : Ty 0 Ψ′}
    {M : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ B}
    {Ψ″}{Σ″ : Store Ψ″}
    {C : Ty 0 Ψ″}
    {N : 0 ∣ Ψ″ ∣ Σ″ ∣ [] ⊢ C} →
  L —↠ M →
  M —↠ N →
  L —↠ N
multi-trans (_ ∎) M—↠N = M—↠N
multi-trans (_ —→⟨ L—→M ⟩ M—↠N) N—↠P = _ —→⟨ L—→M ⟩ multi-trans M—↠N N—↠P

_—↠⟨_⟩_ :
  ∀ {Ψ}{Σ : Store Ψ}{A : Ty 0 Ψ}
    (L : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A)
    {Ψ′}{Σ′ : Store Ψ′}
    {B : Ty 0 Ψ′}
    {M : 0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ B}
    {Ψ″}{Σ″ : Store Ψ″}
    {C : Ty 0 Ψ″}
    {N : 0 ∣ Ψ″ ∣ Σ″ ∣ [] ⊢ C}
    → L —↠ M
    → M —↠ N
      ---------
    → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N = multi-trans L—↠M M—↠N
