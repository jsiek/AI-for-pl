module proof.NuPreservation where

-- File Charter:
--   * Type preservation for Nu GTSF telescope-threaded one-step reduction.
--   * States preservation directly over `Telescope`, with result types raised
--     when a step allocates a fresh head seal.
--   * The old `Ctx`/`Store` split is intentionally absent; the α-application
--     frame is decomposed into seal-renaming reflection, insertion bookkeeping,
--     and opening-coherence obligations.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (_+_; zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (_×_; _,_; ∃)
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq)

open import Types
open import Coercions
open import Primitives
open import NuTerms
open import NuReduction
open import proof.CoercionProperties using (coercion-wf)
open import proof.TypeProperties
open import proof.NuTermProperties

------------------------------------------------------------------------
-- Raw redex preservation
------------------------------------------------------------------------

postulate
  pure-preservation-• :
    ∀ {Γ L α N A} →
    Γ ⊢ L • α ⦂ A →
    L • α —→ N →
    Γ ⊢ N ⦂ A

------------------------------------------------------------------------
-- Focused obligations for the `ξ-·α` preservation case
------------------------------------------------------------------------

weakenBody :
  ∀ {Γ Γ′} →
  StepExt Γ Γ′ →
  Ty →
  Ty
weakenBody ext-refl B = B
weakenBody ext-seal B = rename (extᵗ idᵗ) suc B

weakenTy-∀ :
  ∀ {Γ Γ′ B} →
  (ext : StepExt Γ Γ′) →
  weakenTy ext (`∀ B) ≡ `∀ (weakenBody ext B)
weakenTy-∀ ext-refl = refl
weakenTy-∀ ext-seal = refl

weakenBody-wf :
  ∀ {Γ Γ′ B} →
  (ext : StepExt Γ Γ′) →
  WfTy (tyᵉ ∷ Γ) B →
  WfTy (tyᵉ ∷ Γ′) (weakenBody ext B)
weakenBody-wf ext-refl hB = hB
weakenBody-wf ext-seal hB =
  rename-preserves-WfTy
    (extᵗ-ty-renaming shiftˢ-ty-renaming)
    (extᵗ-seal-renaming shiftˢ-seal-renaming)
    hB

Injectiveˢ : Renameˢ → Set
Injectiveˢ σ = ∀ a b → σ a ≡ σ b → a ≡ b

extˢ-injective :
  ∀ {σ} →
  Injectiveˢ σ →
  Injectiveˢ (extˢ σ)
extˢ-injective inj zero zero eq = refl
extˢ-injective inj zero (suc b) ()
extˢ-injective inj (suc α) zero ()
extˢ-injective inj (suc a) (suc b) eq =
  cong suc (inj a b (suc-injective eq))

insertRenˢ-injective :
  ∀ {Γ⁻ Γ⁺ α} →
  (i : SealInsert Γ⁻ Γ⁺ α) →
  Injectiveˢ (insertRenˢ i)
insertRenˢ-injective here a b eq = suc-injective eq
insertRenˢ-injective (seal-above i eqᵢ) zero zero eq = refl
insertRenˢ-injective (seal-above i eqᵢ) zero (suc b) ()
insertRenˢ-injective (seal-above i eqᵢ) (suc a) zero ()
insertRenˢ-injective (seal-above i eqᵢ) (suc a) (suc b) eq =
  cong suc (insertRenˢ-injective i a b (suc-injective eq))

-- `RenameStep σ ext₀ ext σ′` is the context-only bookkeeping for stepping
-- a term that is already in the image of `renameᵐ idᵗ σ`.
--
-- If the head step does not allocate, the same renaming is still valid.  If it
-- allocates one fresh head seal, the source-side step also allocates a
-- corresponding seal, and the renaming under that fresh binder is `extˢ σ`.
data RenameStep (σ : Renameˢ) :
    ∀ {Γ Γ′ Γ₀ Γ₀′} →
    (ext₀ : StepExt Γ₀ Γ₀′) →
    (ext : StepExt Γ Γ′) →
    Renameˢ →
    Set where
  rename-step-refl : ∀ {Γ Γ₀} →
    RenameStep σ (ext-refl {Γ = Γ₀}) (ext-refl {Γ = Γ}) σ

  rename-step-seal : ∀ {Γ Γ₀ C C↑}
    → (eq : C↑ ≡ rename idᵗ σ C)
      -----------------------------------------------------------
    → RenameStep σ
        (ext-seal {Γ = Γ₀} {A = C})
        (ext-seal {Γ = Γ} {A = C↑})
        (extˢ σ)

rename-step-type :
  ∀ {Γ Γ′ Γ₀ Γ₀′ A σ σ′}
  → {ext₀ : StepExt Γ₀ Γ₀′}
  → {ext : StepExt Γ Γ′}
  → RenameStep σ ext₀ ext σ′
  → weakenTy ext (rename idᵗ σ A) ≡
    rename idᵗ σ′ (weakenTy ext₀ A)
rename-step-type {ext₀ = ext-refl} {ext = ext-refl} rename-step-refl =
  refl
rename-step-type {A = A} {σ = σ} {ext₀ = ext-seal} {ext = ext-seal}
    (rename-step-seal eq) =
  trans
    (rename-compose idᵗ idᵗ σ suc A)
    (sym (rename-compose idᵗ idᵗ suc (extˢ σ) A))

rename-step-injective :
  ∀ {Γ Γ′ Γ₀ Γ₀′ σ σ′}
  → {ext₀ : StepExt Γ₀ Γ₀′}
  → {ext : StepExt Γ Γ′}
  → Injectiveˢ σ
  → RenameStep σ ext₀ ext σ′
  → Injectiveˢ σ′
rename-step-injective inj rename-step-refl = inj
rename-step-injective inj (rename-step-seal eq) = extˢ-injective inj

headTyVar : Ty → TyVar
headTyVar (`X X) = X
headTyVar (`α α) = zero
headTyVar (‵ ι) = zero
headTyVar ★ = zero
headTyVar (A ⇒ B) = zero
headTyVar (`∀ A) = zero

headSealVar : Ty → SealVar
headSealVar (`X X) = zero
headSealVar (`α α) = α
headSealVar (‵ ι) = zero
headSealVar ★ = zero
headSealVar (A ⇒ B) = zero
headSealVar (`∀ A) = zero

arrDom : Ty → Ty
arrDom (`X X) = `X X
arrDom (`α α) = `α α
arrDom (‵ ι) = ‵ ι
arrDom ★ = ★
arrDom (A ⇒ B) = A
arrDom (`∀ A) = `∀ A

arrCod : Ty → Ty
arrCod (`X X) = `X X
arrCod (`α α) = `α α
arrCod (‵ ι) = ‵ ι
arrCod ★ = ★
arrCod (A ⇒ B) = B
arrCod (`∀ A) = `∀ A

∀Body : Ty → Ty
∀Body (`X X) = `X X
∀Body (`α α) = `α α
∀Body (‵ ι) = ‵ ι
∀Body ★ = ★
∀Body (A ⇒ B) = A ⇒ B
∀Body (`∀ A) = A

`X-injective :
  ∀ {X Y : TyVar} →
  `X X ≡ `X Y →
  X ≡ Y
`X-injective eq = cong headTyVar eq

`α-injective :
  ∀ {α b : SealVar} →
  `α α ≡ `α b →
  α ≡ b
`α-injective eq = cong headSealVar eq

⇒-injectiveˡ :
  ∀ {A B C D : Ty} →
  A ⇒ B ≡ C ⇒ D →
  A ≡ C
⇒-injectiveˡ eq = cong arrDom eq

⇒-injectiveʳ :
  ∀ {A B C D : Ty} →
  A ⇒ B ≡ C ⇒ D →
  B ≡ D
⇒-injectiveʳ eq = cong arrCod eq

∀-injective :
  ∀ {A B : Ty} →
  `∀ A ≡ `∀ B →
  A ≡ B
∀-injective eq = cong ∀Body eq

rename-injectiveˢ :
  ∀ {σ A B} →
  Injectiveˢ σ →
  rename idᵗ σ A ≡ rename idᵗ σ B →
  A ≡ B
rename-injectiveˢ {A = `X X} {B = `X Y} inj eq =
  cong `X_ (`X-injective eq)
rename-injectiveˢ {A = `X X} {B = `α b} inj ()
rename-injectiveˢ {A = `X X} {B = ‵ ι} inj ()
rename-injectiveˢ {A = `X X} {B = ★} inj ()
rename-injectiveˢ {A = `X X} {B = B ⇒ C} inj ()
rename-injectiveˢ {A = `X X} {B = `∀ B} inj ()
rename-injectiveˢ {A = `α α} {B = `X X} inj ()
rename-injectiveˢ {A = `α α} {B = `α b} inj eq =
  cong `α_ (inj α b (`α-injective eq))
rename-injectiveˢ {A = `α α} {B = ‵ ι} inj ()
rename-injectiveˢ {A = `α α} {B = ★} inj ()
rename-injectiveˢ {A = `α α} {B = B ⇒ C} inj ()
rename-injectiveˢ {A = `α α} {B = `∀ B} inj ()
rename-injectiveˢ {A = ‵ ι} {B = `X X} inj ()
rename-injectiveˢ {A = ‵ ι} {B = `α α} inj ()
rename-injectiveˢ {A = ‵ ι} {B = ‵ .ι} inj refl = refl
rename-injectiveˢ {A = ‵ ι} {B = ★} inj ()
rename-injectiveˢ {A = ‵ ι} {B = B ⇒ C} inj ()
rename-injectiveˢ {A = ‵ ι} {B = `∀ B} inj ()
rename-injectiveˢ {A = ★} {B = `X X} inj ()
rename-injectiveˢ {A = ★} {B = `α α} inj ()
rename-injectiveˢ {A = ★} {B = ‵ ι} inj ()
rename-injectiveˢ {A = ★} {B = ★} inj refl = refl
rename-injectiveˢ {A = ★} {B = B ⇒ C} inj ()
rename-injectiveˢ {A = ★} {B = `∀ B} inj ()
rename-injectiveˢ {A = A ⇒ B} {B = `X X} inj ()
rename-injectiveˢ {A = A ⇒ B} {B = `α α} inj ()
rename-injectiveˢ {A = A ⇒ B} {B = ‵ ι} inj ()
rename-injectiveˢ {A = A ⇒ B} {B = ★} inj ()
rename-injectiveˢ {A = A ⇒ B} {B = C ⇒ D} inj eq =
  cong₂ _⇒_
    (rename-injectiveˢ inj (⇒-injectiveˡ eq))
    (rename-injectiveˢ inj (⇒-injectiveʳ eq))
rename-injectiveˢ {A = A ⇒ B} {B = `∀ C} inj ()
rename-injectiveˢ {A = `∀ A} {B = `X X} inj ()
rename-injectiveˢ {A = `∀ A} {B = `α α} inj ()
rename-injectiveˢ {A = `∀ A} {B = ‵ ι} inj ()
rename-injectiveˢ {A = `∀ A} {B = ★} inj ()
rename-injectiveˢ {A = `∀ A} {B = B ⇒ C} inj ()
rename-injectiveˢ {A = `∀ A} {B = `∀ B} inj eq =
  cong `∀
    (rename-injectiveˢ inj
      (trans
        (sym (rename-cong (extᵗ-idlike idᵗ-like) (λ α → refl) A))
        (trans
          (∀-injective eq)
          (rename-cong (extᵗ-idlike idᵗ-like) (λ α → refl) B))))

renameᵐ-blame-injective :
  ∀ {σ M} →
  renameᵐ idᵗ σ M ≡ blame →
  M ≡ blame
renameᵐ-blame-injective {M = ` x} ()
renameᵐ-blame-injective {M = ƛ M} ()
renameᵐ-blame-injective {M = L · M} ()
renameᵐ-blame-injective {M = Λ M} ()
renameᵐ-blame-injective {M = L • α} ()
renameᵐ-blame-injective {M = ν A N} ()
renameᵐ-blame-injective {M = $ κ} ()
renameᵐ-blame-injective {M = L ⊕[ op ] M} ()
renameᵐ-blame-injective {M = M ⟨ c ⟩} ()
renameᵐ-blame-injective {M = blame} refl = refl

weakenSeal-rename-step :
  ∀ {Γ Γ′ Γ₀ Γ₀′ σ σ′ α}
  → {ext₀ : StepExt Γ₀ Γ₀′}
  → {ext : StepExt Γ Γ′}
  → RenameStep σ ext₀ ext σ′
  → weakenSeal ext (σ α) ≡ σ′ (weakenSeal ext₀ α)
weakenSeal-rename-step rename-step-refl = refl
weakenSeal-rename-step (rename-step-seal eq) = refl

weakenTerm-rename-step :
  ∀ {Γ Γ′ Γ₀ Γ₀′ σ σ′}
  → {ext₀ : StepExt Γ₀ Γ₀′}
  → {ext : StepExt Γ Γ′}
  → RenameStep σ ext₀ ext σ′
  → (M : Term)
  → weakenTerm ext (renameᵐ idᵗ σ M) ≡
    renameᵐ idᵗ σ′ (weakenTerm ext₀ M)
weakenTerm-rename-step rename-step-refl M = refl
weakenTerm-rename-step {σ = σ} (rename-step-seal eq) M =
  renameᵐ-shiftˢ-comm σ M

weakenCoercion-rename-step :
  ∀ {Γ Γ′ Γ₀ Γ₀′ σ σ′}
  → {ext₀ : StepExt Γ₀ Γ₀′}
  → {ext : StepExt Γ Γ′}
  → RenameStep σ ext₀ ext σ′
  → (c : Coercion)
  → weakenCoercion ext (renameᶜ idᵗ σ c) ≡
    renameᶜ idᵗ σ′ (weakenCoercion ext₀ c)
weakenCoercion-rename-step rename-step-refl c = refl
weakenCoercion-rename-step {σ = σ} (rename-step-seal eq) c =
  renameᶜ-shiftˢ-comm σ c

rename-pure-step-reflectˢ :
  ∀ {L L′ σ}
  → Injectiveˢ σ
  → renameᵐ idᵗ σ L —→ L′
  → ∃ λ L₀′ →
      (L —→ L₀′) ×
      L′ ≡ renameᵐ idᵗ σ L₀′
rename-pure-step-reflectˢ {L = $ (κℕ m) ⊕[ addℕ ] $ (κℕ n)} inj δ-⊕ =
  $ (κℕ (m + n)) , δ-⊕ , refl
rename-pure-step-reflectˢ {L = (ƛ N) · V} inj (β vV) =
  substˣᵐ (singleEnv V) N , β (renameᵐ-reflects-Value idᵗ _ vV) ,
  renameᵐ-substˣ-single _ N V
rename-pure-step-reflectˢ {L = (Λ V) • α} inj β-Λ =
  V [ α ]ᵀ , β-Λ , renameᵐ-openᵀ-seal _ V α
rename-pure-step-reflectˢ {L = V ⟨ id A ⟩} inj (β-id vV) =
  V , β-id (renameᵐ-reflects-Value idᵗ _ vV) , refl
rename-pure-step-reflectˢ {L = V ⟨ p ︔ q ⟩} inj (β-seq vV) =
  V ⟨ p ⟩ ⟨ q ⟩ , β-seq (renameᵐ-reflects-Value idᵗ _ vV) , refl
rename-pure-step-reflectˢ {L = (V ⟨ p ↦ q ⟩) · W} inj (β-↦ vV vW) =
  (V · (W ⟨ p ⟩)) ⟨ q ⟩ ,
  β-↦ (renameᵐ-reflects-Value idᵗ _ vV)
      (renameᵐ-reflects-Value idᵗ _ vW) ,
  refl
rename-pure-step-reflectˢ {L = V ⟨ `∀ c ⟩ • α} inj (β-∀ vV) =
  (V • α) ⟨ c [ α ]ᵀᶜ ⟩ ,
  β-∀ (renameᵐ-reflects-Value idᵗ _ vV) ,
  cong (λ c′ → (renameᵐ idᵗ _ V • _ ) ⟨ c′ ⟩)
       (renameᶜ-open∀-seal _ c α)
rename-pure-step-reflectˢ {L = V ⟨ gen c ⟩ • α} inj (β-gen vV) =
  V ⟨ c [ α ]ᶜ ⟩ ,
  β-gen (renameᵐ-reflects-Value idᵗ _ vV) ,
  cong (λ c′ → renameᵐ idᵗ _ V ⟨ c′ ⟩)
       (renameᶜ-openν-seal _ c α)
rename-pure-step-reflectˢ {L = V ⟨ inst c ⟩} inj (β-inst vV) =
  ν ★ (((⇑ˢᵐ V) • zero) ⟨ c ⟩) ,
  β-inst (renameᵐ-reflects-Value idᵗ _ vV) ,
  cong (λ M → ν ★ ((M • zero) ⟨ renameᶜ idᵗ _ c ⟩))
       (renameᵐ-shiftˢ-comm _ V)
rename-pure-step-reflectˢ {L = V ⟨ G ! ⟩ ⟨ H ？ ⟩} inj
    (tag-untag-ok vV eq) =
  V ,
  tag-untag-ok
    (renameᵐ-reflects-Value idᵗ _ vV)
    (rename-injectiveˢ inj eq) ,
  refl
rename-pure-step-reflectˢ {L = V ⟨ G ! ⟩ ⟨ H ？ ⟩} inj
    (tag-untag-bad vV G≢H) =
  blame ,
  tag-untag-bad
    (renameᵐ-reflects-Value idᵗ _ vV)
    (λ G≡H → G≢H (cong (rename idᵗ _) G≡H)) ,
  refl
rename-pure-step-reflectˢ {L = V ⟨ seal A α ⟩ ⟨ unseal b B ⟩} inj
    (seal-unseal vV eq) =
  V , seal-unseal (renameᵐ-reflects-Value idᵗ _ vV) (inj α b eq) , refl
rename-pure-step-reflectˢ {L = L · M} inj (blame-·₁ eq) =
  blame , blame-·₁ (renameᵐ-blame-injective eq) , refl
rename-pure-step-reflectˢ {L = V · M} inj (blame-·₂ vV eq) =
  blame ,
  blame-·₂ (renameᵐ-reflects-Value idᵗ _ vV)
            (renameᵐ-blame-injective eq) ,
  refl
rename-pure-step-reflectˢ {L = M • α} inj (blame-·α eq) =
  blame , blame-·α (renameᵐ-blame-injective eq) , refl
rename-pure-step-reflectˢ {L = M ⟨ c ⟩} inj (blame-⟨⟩ eq) =
  blame , blame-⟨⟩ (renameᵐ-blame-injective eq) , refl
rename-pure-step-reflectˢ {L = L ⊕[ op ] M} inj (blame-⊕₁ eq) =
  blame , blame-⊕₁ (renameᵐ-blame-injective eq) , refl
rename-pure-step-reflectˢ {L = L ⊕[ op ] M} inj (blame-⊕₂ vL eq) =
  blame ,
  blame-⊕₂ (renameᵐ-reflects-Value idᵗ _ vL)
            (renameᵐ-blame-injective eq) ,
  refl

-- `InsertStep i ext⁻ ext i′` is the insertion-specific view of
-- `RenameStep (insertRenˢ i) ext⁻ ext σ′`: after a renamed head step, it
-- remembers the updated `SealInsert` witness needed by `⊢•`.
data InsertStep {Γ⁻ Γ⁺ α} (i : SealInsert Γ⁻ Γ⁺ α) :
    ∀ {Γ′⁻ Γ′} →
    (ext⁻ : StepExt Γ⁻ Γ′⁻) →
    (ext : StepExt Γ⁺ Γ′) →
    SealInsert Γ′⁻ Γ′ (weakenSeal ext α) →
    Set where
  insert-step-refl :
    InsertStep i ext-refl ext-refl i

  insert-step-seal : ∀ {C C↑}
    → (eq : C↑ ≡ rename idᵗ (insertRenˢ i) C)
      ------------------------------------------------
    → InsertStep i ext-seal ext-seal (seal-above i eq)

insert-step-type :
  ∀ {Γ⁻ Γ⁺ Γ′⁻ Γ′ α A}
  → {i : SealInsert Γ⁻ Γ⁺ α}
  → {ext⁻ : StepExt Γ⁻ Γ′⁻}
  → {ext : StepExt Γ⁺ Γ′}
  → {i′ : SealInsert Γ′⁻ Γ′ (weakenSeal ext α)}
  → InsertStep i ext⁻ ext i′
  → weakenTy ext (rename idᵗ (insertRenˢ i) A)
    ≡ rename idᵗ (insertRenˢ i′) (weakenTy ext⁻ A)
insert-step-type insert-step-refl = refl
insert-step-type {A = A} {i = i} (insert-step-seal eq) =
  trans
    (rename-compose idᵗ idᵗ (insertRenˢ i) suc A)
    (sym (rename-compose idᵗ idᵗ suc (insertRenˢ (seal-above i eq)) A))

insert-rename-step :
  ∀ {Γ⁻ Γ⁺ Γ′⁻ Γ′ α σ′}
  → {i : SealInsert Γ⁻ Γ⁺ α}
  → {ext⁻ : StepExt Γ⁻ Γ′⁻}
  → {ext : StepExt Γ⁺ Γ′}
  → RenameStep (insertRenˢ i) ext⁻ ext σ′
  → ∃ λ (i′ : SealInsert Γ′⁻ Γ′ (weakenSeal ext α)) →
      InsertStep i ext⁻ ext i′ ×
      ((M : Term) →
        renameᵐ idᵗ σ′ M ≡ renameᵐ idᵗ (insertRenˢ i′) M)
insert-rename-step {ext⁻ = ext-refl} {ext = ext-refl} rename-step-refl =
  _ , insert-step-refl , λ M → refl
insert-rename-step {i = i} {ext⁻ = ext-seal} {ext = ext-seal}
    (rename-step-seal eq) =
  _ , insert-step-seal eq , λ M →
    renameᵐ-cong (λ X → refl) same-seal M
  where
    same-seal :
      ∀ α →
      extˢ (insertRenˢ i) α ≡ insertRenˢ (seal-above i eq) α
    same-seal zero = refl
    same-seal (suc α) = refl

-- Operational reflection for injective seal renamings.  If an injectively
-- seal-renamed term takes a step, then the source term takes the analogous
-- step and the reducts are still related by the context-extended renaming.
-- The injectivity hypothesis rules out behavioral artifacts such as collapsing
-- two distinct seals into one tag/untag match.
rename-step-reflectˢ :
  ∀ {Γ Γ′ Γ₀ L L′}
  → (σ : Renameˢ)
  → Injectiveˢ σ
  → (ext : StepExt Γ Γ′)
  → Γ ∣ renameᵐ idᵗ σ L —→ Γ′ ∣ L′
  → ∃ λ Γ₀′ →
    ∃ λ L₀′ →
    ∃ λ (ext₀ : StepExt Γ₀ Γ₀′) →
    ∃ λ σ′ →
      (Γ₀ ∣ L —→ Γ₀′ ∣ L₀′) ×
      RenameStep σ ext₀ ext σ′ ×
      L′ ≡ renameᵐ idᵗ σ′ L₀′

rename-step-reflectˢ-by-term :
  ∀ {Γ Γ′ Γ₀ L′}
  → (L : Term)
  → (σ : Renameˢ)
  → Injectiveˢ σ
  → (ext : StepExt Γ Γ′)
  → Γ ∣ renameᵐ idᵗ σ L —→ Γ′ ∣ L′
  → ∃ λ Γ₀′ →
    ∃ λ L₀′ →
    ∃ λ (ext₀ : StepExt Γ₀ Γ₀′) →
    ∃ λ σ′ →
      (Γ₀ ∣ L —→ Γ₀′ ∣ L₀′) ×
      RenameStep σ ext₀ ext σ′ ×
      L′ ≡ renameᵐ idᵗ σ′ L₀′
rename-step-reflectˢ-by-term (` x) σ inj ext-refl (pure-step ())
rename-step-reflectˢ-by-term (ƛ N) σ inj ext-refl (pure-step ())
rename-step-reflectˢ-by-term (Λ N) σ inj ext-refl (pure-step ())
rename-step-reflectˢ-by-term (ν A N) σ inj ext-refl (pure-step ())
rename-step-reflectˢ-by-term {Γ₀ = Γ₀} (ν A N) σ inj ext-seal ν-step =
  sealᵉ A ∷ Γ₀ , N , ext-seal , extˢ σ ,
  ν-step , rename-step-seal refl , refl
rename-step-reflectˢ-by-term ($ κ) σ inj ext-refl (pure-step ())
rename-step-reflectˢ-by-term (L ⊕[ op ] M) σ inj ext-refl
    (pure-step red)
    with rename-pure-step-reflectˢ inj red
... | L₀′ , red₀ , eqL′ =
  _ , L₀′ , ext-refl , σ ,
  pure-step red₀ , rename-step-refl , eqL′
rename-step-reflectˢ-by-term {Γ₀ = Γ₀} (L ⊕[ op ] M) σ inj ext
    (ξ-⊕₁ ext₁ red eq)
    rewrite stepExt-unique ext₁ ext
    with rename-step-reflectˢ-by-term L σ inj ext red
... | Γ₀′ , L₀′ , ext₀ , σ′ , red₀ , stepʳ , eqL′ =
  Γ₀′ , L₀′ ⊕[ op ] weakenTerm ext₀ M , ext₀ , σ′ ,
  ξ-⊕₁ ext₀ red₀ refl ,
  stepʳ ,
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    eqL′
    (trans eq (weakenTerm-rename-step stepʳ M))
rename-step-reflectˢ-by-term {Γ₀ = Γ₀} (L ⊕[ op ] M) σ inj ext
    (ξ-⊕₂ vL ext₁ red eq)
    rewrite stepExt-unique ext₁ ext
    with rename-step-reflectˢ-by-term M σ inj ext red
... | Γ₀′ , M₀′ , ext₀ , σ′ , red₀ , stepʳ , eqM′ =
  Γ₀′ , weakenTerm ext₀ L ⊕[ op ] M₀′ , ext₀ , σ′ ,
  ξ-⊕₂ (renameᵐ-reflects-Value idᵗ _ vL) ext₀ red₀ refl ,
  stepʳ ,
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    (trans eq (weakenTerm-rename-step stepʳ L))
    eqM′
rename-step-reflectˢ-by-term blame σ inj ext-refl (pure-step ())
rename-step-reflectˢ-by-term {Γ₀ = Γ₀} (L · M) σ inj ext-refl
    (pure-step red)
    with rename-pure-step-reflectˢ inj red
... | L₀′ , red₀ , eqL′ =
  Γ₀ , L₀′ , ext-refl , σ ,
  pure-step red₀ , rename-step-refl , eqL′
rename-step-reflectˢ-by-term {Γ₀ = Γ₀} (L · M) σ inj ext
    (ξ-·₁ ext₁ red eq)
    rewrite stepExt-unique ext₁ ext
    with rename-step-reflectˢ-by-term L σ inj ext red
... | Γ₀′ , L₀′ , ext₀ , σ′ , red₀ , stepʳ , eqL′ =
  Γ₀′ , L₀′ · weakenTerm ext₀ M , ext₀ , σ′ ,
  ξ-·₁ ext₀ red₀ refl ,
  stepʳ ,
  cong₂ _·_ eqL′ (trans eq (weakenTerm-rename-step stepʳ M))
rename-step-reflectˢ-by-term {Γ₀ = Γ₀} (V · M) σ inj ext
    (ξ-·₂ vV ext₁ red eq)
    rewrite stepExt-unique ext₁ ext
    with rename-step-reflectˢ-by-term M σ inj ext red
... | Γ₀′ , M₀′ , ext₀ , σ′ , red₀ , stepʳ , eqM′ =
  Γ₀′ , weakenTerm ext₀ V · M₀′ , ext₀ , σ′ ,
  ξ-·₂ (renameᵐ-reflects-Value idᵗ _ vV) ext₀ red₀ refl ,
  stepʳ ,
  cong₂ _·_ (trans eq (weakenTerm-rename-step stepʳ V)) eqM′
rename-step-reflectˢ-by-term {Γ₀ = Γ₀} (M • α) σ inj ext-refl
    (pure-step red)
    with rename-pure-step-reflectˢ inj red
... | L₀′ , red₀ , eqL′ =
  Γ₀ , L₀′ , ext-refl , σ ,
  pure-step red₀ , rename-step-refl , eqL′
rename-step-reflectˢ-by-term {Γ₀ = Γ₀} (M • α) σ inj ext
    (ξ-·α ext₁ red eq)
    rewrite stepExt-unique ext₁ ext
    with rename-step-reflectˢ-by-term M σ inj ext red
... | Γ₀′ , M₀′ , ext₀ , σ′ , red₀ , stepʳ , eqM′ =
  Γ₀′ , M₀′ • weakenSeal ext₀ α , ext₀ , σ′ ,
  ξ-·α ext₀ red₀ refl ,
  stepʳ ,
  cong₂ _•_ eqM′ (trans eq (weakenSeal-rename-step stepʳ))
rename-step-reflectˢ-by-term {Γ₀ = Γ₀} (M ⟨ c ⟩) σ inj ext-refl
    (pure-step red)
    with rename-pure-step-reflectˢ inj red
... | L₀′ , red₀ , eqL′ =
  Γ₀ , L₀′ , ext-refl , σ ,
  pure-step red₀ , rename-step-refl , eqL′
rename-step-reflectˢ-by-term {Γ₀ = Γ₀} (M ⟨ c ⟩) σ inj ext
    (ξ-⟨⟩ ext₁ red eq)
    rewrite stepExt-unique ext₁ ext
    with rename-step-reflectˢ-by-term M σ inj ext red
... | Γ₀′ , M₀′ , ext₀ , σ′ , red₀ , stepʳ , eqM′ =
  Γ₀′ , M₀′ ⟨ weakenCoercion ext₀ c ⟩ , ext₀ , σ′ ,
  ξ-⟨⟩ ext₀ red₀ refl ,
  stepʳ ,
  cong₂ _⟨_⟩ eqM′ (trans eq (weakenCoercion-rename-step stepʳ c))

rename-step-reflectˢ {L = L} σ inj ext red =
  rename-step-reflectˢ-by-term L σ inj ext red

rename-step-image :
  ∀ {Γ Γ′ Γ₀ L L′}
  → (σ : Renameˢ)
  → Injectiveˢ σ
  → (ext : StepExt Γ Γ′)
  → Γ ∣ renameᵐ idᵗ σ L —→ Γ′ ∣ L′
  → ∃ λ Γ₀′ →
    ∃ λ L₀′ →
    ∃ λ (ext₀ : StepExt Γ₀ Γ₀′) →
    ∃ λ σ′ →
      RenameStep σ ext₀ ext σ′ ×
      L′ ≡ renameᵐ idᵗ σ′ L₀′
rename-step-image σ inj ext red
    with rename-step-reflectˢ σ inj ext red
... | Γ₀′ , L₀′ , ext₀ , σ′ , red₀ , stepʳ , eqL′ =
  Γ₀′ , L₀′ , ext₀ , σ′ , stepʳ , eqL′

postulate
  -- The nontrivial substitution/renaming algebra for opening a `∀` body after
  -- a fresh seal is allocated above the focused seal.
  insert-open-step-seal :
    ∀ {Γ⁻ Γ⁺ α C C↑ B}
    → (i : SealInsert Γ⁻ Γ⁺ α)
    → (eq : C↑ ≡ rename idᵗ (insertRenˢ i) C)
    → ⇑ˢ (openTyWithInsertedSeal i B) ≡
      openTyWithInsertedSeal (seal-above i eq)
        (rename (extᵗ idᵗ) suc B)

insert-open-step :
  ∀ {Γ⁻ Γ⁺ Γ′⁻ Γ′ α B}
  → {i : SealInsert Γ⁻ Γ⁺ α}
  → {ext⁻ : StepExt Γ⁻ Γ′⁻}
  → {ext : StepExt Γ⁺ Γ′}
  → {i′ : SealInsert Γ′⁻ Γ′ (weakenSeal ext α)}
  → InsertStep i ext⁻ ext i′
  → weakenTy ext (openTyWithInsertedSeal i B) ≡
    openTyWithInsertedSeal i′ (weakenBody ext⁻ B)
insert-open-step insert-step-refl = refl
insert-open-step {i = i} (insert-step-seal eq) =
  insert-open-step-seal i eq

pure-preservation :
  ∀ {Γ M N A} →
  Γ ⊢ M ⦂ A →
  M —→ N →
  Γ ⊢ N ⦂ A
pure-preservation (⊢⊕ (⊢$ (κℕ m)) addℕ (⊢$ (κℕ n))) δ-⊕ =
  ⊢$ _
pure-preservation (⊢· (⊢ƛ hA hN) hV) (β vV) =
  typing-single-subst hN hV
pure-preservation hApp@(⊢• _ _ _ _ _) β-Λ =
  pure-preservation-• hApp β-Λ
pure-preservation (⊢⟨⟩ (cast-id hA) hV) (β-id vV) = hV
pure-preservation (⊢⟨⟩ (cast-seq p⊢ q⊢) hV) (β-seq vV) =
  ⊢⟨⟩ q⊢ (⊢⟨⟩ p⊢ hV)
pure-preservation
    (⊢· (⊢⟨⟩ (cast-fun p⊢ q⊢) hV) hW)
    (β-↦ vV vW) =
  ⊢⟨⟩ q⊢ (⊢· hV (⊢⟨⟩ p⊢ hW))
pure-preservation hApp@(⊢• _ _ _ _ _) (β-∀ vV) =
  pure-preservation-• hApp (β-∀ vV)
pure-preservation hApp@(⊢• _ _ _ _ _) (β-gen vV) =
  pure-preservation-• hApp (β-gen vV)
pure-preservation
    (⊢⟨⟩ (cast-inst hA hB occ c⊢) V⊢)
    (β-inst vV) =
  ⊢ν wf★ (⊢⟨⟩ c⊢ (⊢•-insert V⊢ hA wf★))
pure-preservation
    (⊢⟨⟩ (cast-unseal hB useB hαB)
      (⊢⟨⟩ (cast-seal hA useA hαA) V⊢))
    (seal-unseal vV refl) =
  substEq (λ T → _ ⊢ _ ⦂ T) (seal-lookup-unique hαA hαB) V⊢
pure-preservation
    (⊢⟨⟩ (cast-untag hG gG okG)
      (⊢⟨⟩ (cast-tag hG′ gG′ okG′) V⊢))
    (tag-untag-ok vV eq) =
  substEq (λ T → _ ⊢ _ ⦂ T) eq V⊢
pure-preservation
    (⊢⟨⟩ (cast-untag hH gH okH)
      (⊢⟨⟩ (cast-tag hG gG okG) V⊢))
    (tag-untag-bad vV G≢H) =
  ⊢blame hH
pure-preservation (⊢· (⊢blame (wf⇒ hA hB)) hM) (blame-·₁ refl) =
  ⊢blame hB
pure-preservation (⊢· hV (⊢blame hA)) (blame-·₂ vV refl)
    with typing-wf hV
pure-preservation (⊢· hV (⊢blame hA)) (blame-·₂ vV refl)
    | wf⇒ hA′ hB =
  ⊢blame hB
pure-preservation hApp@(⊢• _ _ _ _ _) (blame-·α refl) =
  pure-preservation-• hApp (blame-·α refl)
pure-preservation (⊢⟨⟩ c⊢ (⊢blame hA)) (blame-⟨⟩ refl)
    with coercion-wf c⊢
pure-preservation (⊢⟨⟩ c⊢ (⊢blame hA)) (blame-⟨⟩ refl)
    | hA′ , hB =
  ⊢blame hB
pure-preservation (⊢⊕ (⊢blame hA) op hM) (blame-⊕₁ refl) =
  ⊢blame wfBase
pure-preservation (⊢⊕ hL op (⊢blame hA)) (blame-⊕₂ vL refl) =
  ⊢blame wfBase

------------------------------------------------------------------------
-- Telescope-threaded preservation
------------------------------------------------------------------------

preservation :
  ∀ {Γ Γ′ M N A} →
  Γ ⊢ M ⦂ A →
  (red : Γ ∣ M —→ Γ′ ∣ N) →
  Γ′ ⊢ N ⦂ weakenTy (stepExt red) A
preservation M⊢ (pure-step red) =
  pure-preservation M⊢ red
preservation (⊢ν hA hN) ν-step = hN
preservation (⊢· L⊢ M⊢) (ξ-·₁ ext-refl red refl) =
  ⊢·
    (typing-stepExt-cong (stepExt-unique (stepExt red) ext-refl)
      (preservation L⊢ red))
    M⊢
preservation (⊢· L⊢ M⊢) (ξ-·₁ ext-seal red refl) =
  ⊢·
    (typing-stepExt-cong (stepExt-unique (stepExt red) ext-seal)
      (preservation L⊢ red))
    (typing-weaken-seal M⊢)
preservation (⊢· L⊢ M⊢) (ξ-·₂ vV ext-refl red refl) =
  ⊢· L⊢
    (typing-stepExt-cong (stepExt-unique (stepExt red) ext-refl)
      (preservation M⊢ red))
preservation (⊢· L⊢ M⊢) (ξ-·₂ vV ext-seal red refl) =
  ⊢· (typing-weaken-seal L⊢)
    (typing-stepExt-cong (stepExt-unique (stepExt red) ext-seal)
      (preservation M⊢ red))
preservation (⊢• {Γ⁻ = Γ⁻} {Γ⁺ = Γ⁺} {L = L} {B = B}
                i L⊢ hB refl refl)
             (ξ-·α ext red refl)
    with rename-step-reflectˢ {Γ₀ = Γ⁻}
           (insertRenˢ i) (insertRenˢ-injective i) ext red
preservation (⊢• {Γ⁻ = Γ⁻} {Γ⁺ = Γ⁺} {L = L} {B = B}
                i L⊢ hB refl refl)
             (ξ-·α ext red refl)
    | Γ′⁻ , L₀′ , ext⁻ , σ′ , red⁻ , stepʳ , eqL′
    with insert-rename-step {i = i} stepʳ
preservation (⊢• {Γ⁻ = Γ⁻} {Γ⁺ = Γ⁺} {L = L} {B = B}
                i L⊢ hB refl refl)
             (ξ-·α ext red refl)
    | Γ′⁻ , L₀′ , ext⁻ , σ′ , red⁻ , stepʳ , eqL′
    | i′ , stepᵢ , eqᵐ =
  substEq
    (λ T → _ ⊢ _ ⦂ T)
    (sym (insert-open-step stepᵢ))
    (⊢• i′ L₀′⊢ hB′ (trans eqL′ (eqᵐ L₀′)) refl)
  where
    L₀′⊢₀ :
      Γ′⁻ ⊢ L₀′ ⦂ weakenTy ext⁻ (`∀ B)
    L₀′⊢₀ =
      typing-stepExt-cong
        (stepExt-unique (stepExt red⁻) ext⁻)
        (preservation L⊢ red⁻)

    L₀′⊢ :
      Γ′⁻ ⊢ L₀′ ⦂ `∀ (weakenBody ext⁻ B)
    L₀′⊢ =
      substEq
        (λ T → Γ′⁻ ⊢ L₀′ ⦂ T)
        (weakenTy-∀ ext⁻)
        L₀′⊢₀

    hB′ :
      WfTy (tyᵉ ∷ Γ′⁻) (weakenBody ext⁻ B)
    hB′ =
      weakenBody-wf ext⁻ hB
preservation (⊢⟨⟩ c⊢ M⊢) (ξ-⟨⟩ ext-refl red refl) =
  ⊢⟨⟩ c⊢
    (typing-stepExt-cong (stepExt-unique (stepExt red) ext-refl)
      (preservation M⊢ red))
preservation (⊢⟨⟩ c⊢ M⊢) (ξ-⟨⟩ ext-seal red refl)
    with coercion-weaken-step ext-seal c⊢
preservation (⊢⟨⟩ c⊢ M⊢) (ξ-⟨⟩ ext-seal red refl)
    | μ′ , c↑⊢ =
  ⊢⟨⟩ c↑⊢
    (typing-stepExt-cong (stepExt-unique (stepExt red) ext-seal)
      (preservation M⊢ red))
preservation (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ ext-refl red refl) =
  ⊢⊕
    (typing-stepExt-cong (stepExt-unique (stepExt red) ext-refl)
      (preservation L⊢ red))
    op
    M⊢
preservation (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ ext-seal red refl) =
  ⊢⊕
    (typing-stepExt-cong (stepExt-unique (stepExt red) ext-seal)
      (preservation L⊢ red))
    op
    (typing-weaken-seal M⊢)
preservation (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL ext-refl red refl) =
  ⊢⊕ L⊢ op
    (typing-stepExt-cong (stepExt-unique (stepExt red) ext-refl)
      (preservation M⊢ red))
preservation (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL ext-seal red refl) =
  ⊢⊕ (typing-weaken-seal L⊢) op
    (typing-stepExt-cong (stepExt-unique (stepExt red) ext-seal)
      (preservation M⊢ red))
