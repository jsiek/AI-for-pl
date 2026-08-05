module GradualTermImprecision where

-- File Charter:
--   * Defines typed source-term imprecision for GTSFImp.
--   * Relates intrinsically scoped gradual terms and records type-imprecision
--     evidence for every related term and context entry.
--   * Provides source and target typing projections for related terms.
--   * Depends on GradualTerms, Imprecision, and Consistency.

open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
import Data.Fin as Fin
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Types
open import TermCtx using (TermCtx; ⇑ᶜ)
import TermCtx as T
open import Consistency using (_∼_)
open import GradualTerms
open import Imprecision
open import Primitives
  using (Const; Prim; κℕ; κ𝔹; addℕ; and𝔹; constTy; primArgTy;
         primResultTy; constTy-renameᵗ)
open import proof.Consistency
  using (rename-consistency-left-inverse; rename-left-inverse-injective)
open import proof.ImprecisionConsistency
  using (ty-var-injective; ty-fun-left-injective; ty-fun-right-injective;
         ty-all-injective; unrename-occurs)
open import proof.TypeInTermSubst using (rename-openᵗ; renameCtx-shift)

constTy-⊑ : ∀ {Δ} (μ : ImpEnv Δ) (κ : Const)
  → μ ⊢ constTy κ ⊑ constTy κ
constTy-⊑ μ (κℕ n) = ι⊑ι
constTy-⊑ μ (κ𝔹 b) = ι⊑ι

primResultTy-⊑ : ∀ {Δ} (μ : ImpEnv Δ) (op : Prim)
  → μ ⊢ primResultTy op ⊑ primResultTy op
primResultTy-⊑ μ addℕ = ι⊑ι
primResultTy-⊑ μ and𝔹 = ι⊑ι

------------------------------------------------------------------------
-- Term-context imprecision
------------------------------------------------------------------------

record CtxImpEntry {Δ : TyCtx} (μ : ImpEnv Δ) : Set where
  constructor ctx-imp
  field
    srcTyⁱ : Ty Δ
    tgtTyⁱ : Ty Δ
    impTyⁱ : μ ⊢ srcTyⁱ ⊑ tgtTyⁱ

open CtxImpEntry public

CtxImp : ∀ {Δ} → ImpEnv Δ → Set
CtxImp μ = List (CtxImpEntry μ)

srcCtxⁱ : ∀ {Δ} {μ : ImpEnv Δ} → CtxImp μ → TermCtx Δ
srcCtxⁱ = map srcTyⁱ

tgtCtxⁱ : ∀ {Δ} {μ : ImpEnv Δ} → CtxImp μ → TermCtx Δ
tgtCtxⁱ = map tgtTyⁱ

infix 4 _∋ⁱ_⦂_

data _∋ⁱ_⦂_ {Δ} {μ : ImpEnv Δ} :
    CtxImp μ → Nat.ℕ → CtxImpEntry μ → Set where
  Zⁱ : ∀ {γ A B p}
      -------------------------------------------
    → (ctx-imp A B p ∷ γ) ∋ⁱ Nat.zero ⦂ ctx-imp A B p

  Sⁱ : ∀ {γ e e′ x}
    → γ ∋ⁱ x ⦂ e
      ---------------------------
    → (e′ ∷ γ) ∋ⁱ Nat.suc x ⦂ e

data LiftCtxⁱ {Δ} {μ : ImpEnv Δ} (ν : ImpEnv (Nat.suc Δ)) :
    CtxImp μ → CtxImp ν → Set where
  lift-[] : LiftCtxⁱ ν [] []

  lift-∷ : ∀ {γ γ′ A B p p′}
    → LiftCtxⁱ ν γ γ′
      -------------------------------------------------------------
    → LiftCtxⁱ ν (ctx-imp A B p ∷ γ)
        (ctx-imp (⇑ᵗ A) (⇑ᵗ B) p′ ∷ γ′)

srcCtxⁱ-lift : ∀ {Δ} {μ : ImpEnv Δ}
    {ν : ImpEnv (Nat.suc Δ)} {γ : CtxImp μ} {γ′ : CtxImp ν}
  → LiftCtxⁱ ν γ γ′
  → srcCtxⁱ γ′ ≡ ⇑ᶜ (srcCtxⁱ γ)
srcCtxⁱ-lift lift-[] = refl
srcCtxⁱ-lift (lift-∷ liftγ) =
  cong₂ _∷_ refl (srcCtxⁱ-lift liftγ)

tgtCtxⁱ-lift : ∀ {Δ} {μ : ImpEnv Δ}
    {ν : ImpEnv (Nat.suc Δ)} {γ : CtxImp μ} {γ′ : CtxImp ν}
  → LiftCtxⁱ ν γ γ′
  → tgtCtxⁱ γ′ ≡ ⇑ᶜ (tgtCtxⁱ γ)
tgtCtxⁱ-lift lift-[] = refl
tgtCtxⁱ-lift (lift-∷ liftγ) =
  cong₂ _∷_ refl (tgtCtxⁱ-lift liftγ)

lookup-zero-eq : ∀ {Δ} {Γ : TermCtx Δ} {A B}
  → B ∷ Γ T.∋ Nat.zero ⦂ A
  → A ≡ B
lookup-zero-eq T.Z = refl

lookup-rename-preimage : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
    {Γ : TermCtx Δ} {x T}
  → T.renameCtx ρ Γ T.∋ x ⦂ T
  → ∃[ A ] (T ≡ renameᵗ ρ A × Γ T.∋ x ⦂ A)
lookup-rename-preimage {Γ = []} ()
lookup-rename-preimage {ρ = ρ} {Γ = A ∷ Γ} {x = Nat.zero} x∈ =
  A , lookup-zero-eq x∈ , T.Z
lookup-rename-preimage {Γ = B ∷ Γ} {x = Nat.suc x} (T.S x∈)
    with lookup-rename-preimage x∈
lookup-rename-preimage {Γ = B ∷ Γ} {x = Nat.suc x} (T.S x∈)
    | A , eq , x∈′ =
  A , eq , T.S x∈′

exts-left-inverse : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {σ : Δ′ ⇒ˢ Δ}
  → (∀ X → σ (ρ X) ≡ ＇ X)
  → ∀ X → extsᵗ σ (extᵗ ρ X) ≡ ＇ X
exts-left-inverse left Fin.zero = refl
exts-left-inverse left (Fin.suc X) =
  cong (renameᵗ Fin.suc) (left X)

var-left-inverse-injective : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
    {σ : Δ′ ⇒ˢ Δ}
  → (∀ X → σ (ρ X) ≡ ＇ X)
  → ∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y
var-left-inverse-injective {σ = σ} left {X} {Y} eq =
  ty-var-injective (trans (sym (left X)) (trans (cong σ eq) (left Y)))

primArgTy-renameᵗ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) op
  → primArgTy {Δ′} op ≡ renameᵗ ρ (primArgTy {Δ} op)
primArgTy-renameᵗ ρ addℕ = refl
primArgTy-renameᵗ ρ and𝔹 = refl

primResultTy-renameᵗ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) op
  → primResultTy {Δ′} op ≡ renameᵗ ρ (primResultTy {Δ} op)
primResultTy-renameᵗ ρ addℕ = refl
primResultTy-renameᵗ ρ and𝔹 = refl

rename-value-invᴳ : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {V}
  → Value (renameᵗᴳ ρ V)
  → Value V
rename-value-invᴳ {V = ` x} ()
rename-value-invᴳ {V = ƛ A ⇒ N} (ƛ A′ ⇒ N′) = ƛ A ⇒ N
rename-value-invᴳ {V = L ·[ ℓ ] M} ()
rename-value-invᴳ {V = Λ N} (Λ N′) = Λ N
rename-value-invᴳ {V = M `[ A ]} ()
rename-value-invᴳ {V = $ κ} ($ κ′) = $ κ
rename-value-invᴳ {V = L ⊕[ op at ℓ ] M} ()

typing-rename-preimageᴳ : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
    {σ : Δ′ ⇒ˢ Δ} {Γ : TermCtx Δ} {M T}
  → (∀ X → σ (ρ X) ≡ ＇ X)
  → Δ′ ∣ T.renameCtx ρ Γ ⊢ renameᵗᴳ ρ M ⦂ T
  → ∃[ A ] (T ≡ renameᵗ ρ A × Δ ∣ Γ ⊢ M ⦂ A)
typing-rename-preimageᴳ {M = ` x} left (⊢` x∈)
    with lookup-rename-preimage x∈
typing-rename-preimageᴳ {M = ` x} left (⊢` x∈)
    | A , eq , x∈′ =
  A , eq , ⊢` x∈′
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {Γ = Γ} {M = ƛ A ⇒ M}
    left (⊢ƛ M⊢)
    with typing-rename-preimageᴳ {ρ = ρ} {σ = σ}
      {Γ = A ∷ Γ} {M = M} left M⊢
typing-rename-preimageᴳ {M = ƛ A ⇒ M} left (⊢ƛ M⊢)
    | B , eq , M⊢′ =
  A ⇒ B , cong₂ _⇒_ refl eq , ⊢ƛ M⊢′
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {M = L ·[ ℓ ] M}
    left (⊢· L⊢ M⊢ A∼A′)
    with typing-rename-preimageᴳ {ρ = ρ} {σ = σ} left L⊢
       | typing-rename-preimageᴳ {ρ = ρ} {σ = σ} left M⊢
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {M = L ·[ ℓ ] M}
    left (⊢· L⊢ M⊢ A∼A′)
    | ＇ X , () , L⊢′ | A , eqA , M⊢′
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {M = L ·[ ℓ ] M}
    left (⊢· L⊢ M⊢ A∼A′)
    | ‵ ι , () , L⊢′ | A , eqA , M⊢′
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {M = L ·[ ℓ ] M}
    left (⊢· L⊢ M⊢ A∼A′)
    | ★ , () , L⊢′ | A , eqA , M⊢′
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {M = L ·[ ℓ ] M}
    left (⊢· L⊢ M⊢ A∼A′)
    | C ⇒ B , eqL , L⊢′ | A , eqA , M⊢′ =
  B , ty-fun-right-injective eqL ,
    ⊢· L⊢′ M⊢′
      (rename-consistency-left-inverse {ρ = ρ} {σ = σ} left
        (subst (λ R → R ∼ _)
          (ty-fun-left-injective eqL)
          (subst (λ R → _ ∼ R) eqA A∼A′)))
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {M = L ·[ ℓ ] M}
    left (⊢· L⊢ M⊢ A∼A′)
    | `∀ B , () , L⊢′ | A , eqA , M⊢′
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {M = L ·[ ℓ ] M}
    left (⊢·★ L⊢ M⊢ A′∼★)
    with typing-rename-preimageᴳ {ρ = ρ} {σ = σ} left L⊢
       | typing-rename-preimageᴳ {ρ = ρ} {σ = σ} left M⊢
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {M = L ·[ ℓ ] M}
    left (⊢·★ L⊢ M⊢ A′∼★)
    | A , eqL , L⊢′ | B , eqB , M⊢′ =
  ★ , refl ,
    ⊢·★
      (subst (λ T → _ ∣ _ ⊢ _ ⦂ T)
        (sym (rename-left-inverse-injective {ρ = ρ} {σ = σ}
          left eqL)) L⊢′)
      M⊢′
      (rename-consistency-left-inverse {ρ = ρ} {σ = σ} left
        (subst (λ R → R ∼ ★) eqB A′∼★))
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {Γ = Γ} {M = Λ M}
    left (⊢Λ {zero∈A = z∈T} vM M⊢)
    with typing-rename-preimageᴳ {ρ = extᵗ ρ} {σ = extsᵗ σ}
      {Γ = ⇑ᶜ Γ} {M = M} (exts-left-inverse left)
      (subst (λ Γ′ → _ ∣ Γ′ ⊢ _ ⦂ _)
        (sym (renameCtx-shift ρ Γ)) M⊢)
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {M = Λ M}
    left (⊢Λ {zero∈A = z∈T} vM M⊢)
    | A , eq , M⊢′ =
  `∀ A , cong `∀ eq ,
    ⊢Λ
      {zero∈A = unrename-occurs (extᵗ ρ)
        (var-left-inverse-injective {ρ = extᵗ ρ} {σ = extsᵗ σ}
          (exts-left-inverse {ρ = ρ} {σ = σ} left))
        (subst (λ T → Fin.zero ∈ᵗ T) eq z∈T)}
      (rename-value-invᴳ vM) M⊢′
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {M = M `[ A ]} left (⊢• M⊢)
    with typing-rename-preimageᴳ {ρ = ρ} {σ = σ} left M⊢
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {M = M `[ A ]} left (⊢• M⊢)
    | ＇ X , () , M⊢′
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {M = M `[ A ]} left (⊢• M⊢)
    | ‵ ι , () , M⊢′
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {M = M `[ A ]} left (⊢• M⊢)
    | ★ , () , M⊢′
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {M = M `[ A ]} left (⊢• M⊢)
    | B ⇒ C , () , M⊢′
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {M = M `[ A ]} left (⊢• M⊢)
    | `∀ B , eq , M⊢′ =
  B [ A ]ᵗ ,
    trans (cong (λ T → T [ renameᵗ ρ A ]ᵗ) (ty-all-injective eq))
      (sym (rename-openᵗ ρ B A)) ,
    ⊢• M⊢′
typing-rename-preimageᴳ {ρ = ρ} {M = $ κ} left (⊢$ κ′) =
  constTy κ , constTy-renameᵗ ρ κ , ⊢$ κ
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {M = L ⊕[ op at ℓ ] M}
    left (⊢⊕ op L⊢ A∼arg M⊢ B∼arg)
    with typing-rename-preimageᴳ {ρ = ρ} {σ = σ} left L⊢
       | typing-rename-preimageᴳ {ρ = ρ} {σ = σ} left M⊢
typing-rename-preimageᴳ {ρ = ρ} {σ = σ} {M = L ⊕[ op at ℓ ] M}
    left (⊢⊕ op L⊢ A∼arg M⊢ B∼arg)
    | A , eqA , L⊢′ | B , eqB , M⊢′ =
  primResultTy op , primResultTy-renameᵗ ρ op ,
    ⊢⊕ op L⊢′
      (rename-consistency-left-inverse {ρ = ρ} {σ = σ} left
        (subst (λ R → R ∼ _)
          eqA (subst (λ R → _ ∼ R) (primArgTy-renameᵗ ρ op) A∼arg)))
      M⊢′
      (rename-consistency-left-inverse {ρ = ρ} {σ = σ} left
        (subst (λ R → R ∼ _)
          eqB (subst (λ R → _ ∼ R) (primArgTy-renameᵗ ρ op) B∼arg)))

typing-rename-invᴳ : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
    {σ : Δ′ ⇒ˢ Δ} {Γ : TermCtx Δ} {M A}
  → (∀ X → σ (ρ X) ≡ ＇ X)
  → Δ′ ∣ T.renameCtx ρ Γ ⊢ renameᵗᴳ ρ M ⦂ renameᵗ ρ A
  → Δ ∣ Γ ⊢ M ⦂ A
typing-rename-invᴳ {ρ = ρ} {σ = σ} {M = M} {A = A} left M⊢
    with typing-rename-preimageᴳ {ρ = ρ} {σ = σ} left M⊢
typing-rename-invᴳ {ρ = ρ} {σ = σ} {M = M} {A = A} left M⊢
    | A′ , eq , M⊢′ =
  subst (λ T → _ ∣ _ ⊢ M ⦂ T)
    (sym (rename-left-inverse-injective {ρ = ρ} {σ = σ} left eq)) M⊢′

typing-shift-invᴳ : ∀ {Δ} {Γ : TermCtx Δ} {M A}
  → (Nat.suc Δ) ∣ ⇑ᶜ Γ ⊢ ⇑ᵗᴳ M ⦂ ⇑ᵗ A
  → Δ ∣ Γ ⊢ M ⦂ A
typing-shift-invᴳ M⊢ =
  typing-rename-invᴳ {ρ = Fin.suc} {σ = singleSubᵗ ★}
    (λ X → refl) M⊢

------------------------------------------------------------------------
-- Typed gradual-term imprecision
------------------------------------------------------------------------

infix 4 _∣_⊢ᴳ_⊑_⦂_⊑_∶_

data _∣_⊢ᴳ_⊑_⦂_⊑_∶_ {Δ} (μ : ImpEnv Δ) (γ : CtxImp μ) :
    GTerm Δ → GTerm Δ → (A B : Ty Δ) → μ ⊢ A ⊑ B → Set where

  x⊑xᴳ : ∀ {x A B p}
    → γ ∋ⁱ x ⦂ ctx-imp A B p
      ---------------------------------------------
    → μ ∣ γ ⊢ᴳ ` x ⊑ ` x ⦂ A ⊑ B ∶ p

  ƛ⊑ƛᴳ : ∀ {N N′ A A′ B B′ pA pB}
    → μ ∣ ctx-imp A A′ pA ∷ γ ⊢ᴳ N ⊑ N′ ⦂ B ⊑ B′ ∶ pB
      ----------------------------------------------------------
    → μ ∣ γ ⊢ᴳ ƛ A ⇒ N ⊑ ƛ A′ ⇒ N′
        ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ ⇒⊑⇒ pA pB

  ·⊑·ᴳ : ∀ {L L′ M M′ A A′ B B′ C C′ ℓ pA pB pC}
    → μ ∣ γ ⊢ᴳ L ⊑ L′
        ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ ⇒⊑⇒ pA pB
    → μ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC
    → A ∼ C
    → A′ ∼ C′
      ---------------------------------------------------------
    → μ ∣ γ ⊢ᴳ L ·[ ℓ ] M ⊑ L′ ·[ ℓ ] M′
        ⦂ B ⊑ B′ ∶ pB

  ·⊑·★ᴳ : ∀ {L L′ M M′ A B C C′ ℓ pA pB pC}
    → μ ∣ γ ⊢ᴳ L ⊑ L′ ⦂ A ⇒ B ⊑ ★ ∶ ⇒⊑★ pA pB
    → μ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC
    → A ∼ C
    → C′ ∼ ★
      -----------------------------------------------------
    → μ ∣ γ ⊢ᴳ L ·[ ℓ ] M ⊑ L′ ·[ ℓ ] M′
        ⦂ B ⊑ ★ ∶ pB

  ·★⊑·★ᴳ : ∀ {L L′ M M′ C C′ ℓ pC}
    → μ ∣ γ ⊢ᴳ L ⊑ L′ ⦂ ★ ⊑ ★ ∶ ★⊑★
    → μ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC
    → C ∼ ★
    → C′ ∼ ★
      -----------------------------------------------------
    → μ ∣ γ ⊢ᴳ L ·[ ℓ ] M ⊑ L′ ·[ ℓ ] M′
        ⦂ ★ ⊑ ★ ∶ ★⊑★

  Λ⊑Λᴳ : ∀ {γ′ V V′ A B p}
    → LiftCtxⁱ (extᵐ μ) γ γ′
    → Value V
    → Value V′
    → Fin.zero ∈ᵗ A
    → Fin.zero ∈ᵗ B
    → extᵐ μ ∣ γ′ ⊢ᴳ V ⊑ V′ ⦂ A ⊑ B ∶ p
      ----------------------------------------------------
    → μ ∣ γ ⊢ᴳ Λ V ⊑ Λ V′
        ⦂ `∀ A ⊑ `∀ B ∶ ∀⊑∀ p

  Λ⊑ᴳ : ∀ {γ′ V N′ A B p}
    → (Anv : NonVar A)
    → (zero∈A : Fin.zero ∈ᵗ A)
    → LiftCtxⁱ (instᵐ μ) γ γ′
    → Value V
    → instᵐ μ ∣ γ′ ⊢ᴳ V ⊑ ⇑ᵗᴳ N′
        ⦂ A ⊑ ⇑ᵗ B ∶ p
      --------------------------------------------------
    → μ ∣ γ ⊢ᴳ Λ V ⊑ N′
        ⦂ `∀ A ⊑ B ∶ ∀⊑ Anv zero∈A p

  []⊑[]ᴳ : ∀ {M M′ T T′ A B p}
    → μ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ `∀ A ⊑ `∀ B ∶ ∀⊑∀ p
    → (q : μ ⊢ T ⊑ T′)
    → (r : μ ⊢ A [ T ]ᵗ ⊑ B [ T′ ]ᵗ)
      ---------------------------------------------------------
    → μ ∣ γ ⊢ᴳ M `[ T ] ⊑ M′ `[ T′ ]
        ⦂ A [ T ]ᵗ ⊑ B [ T′ ]ᵗ ∶ r

  []⊑ᴳ : ∀ {M M′ T A B p Anv zero∈A}
    → μ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ `∀ A ⊑ B ∶ ∀⊑ Anv zero∈A p
    → (q : μ ⊢ T ⊑ ★)
    → (r : μ ⊢ A [ T ]ᵗ ⊑ B)
      -------------------------------------------------
    → μ ∣ γ ⊢ᴳ M `[ T ] ⊑ M′ ⦂ A [ T ]ᵗ ⊑ B ∶ r

  κ⊑κᴳ : ∀ (κ : Const)
      ------------------------------------------------------
    → μ ∣ γ ⊢ᴳ $ κ ⊑ $ κ
        ⦂ constTy κ ⊑ constTy κ ∶ constTy-⊑ μ κ

  ⊕⊑⊕ᴳ : ∀ {L L′ M M′ A A′ B B′ pA pB ℓ}
    → (op : Prim)
    → μ ∣ γ ⊢ᴳ L ⊑ L′ ⦂ A ⊑ A′ ∶ pA
    → A ∼ primArgTy op
    → A′ ∼ primArgTy op
    → μ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ B ⊑ B′ ∶ pB
    → B ∼ primArgTy op
    → B′ ∼ primArgTy op
      ----------------------------------------------------------
    → μ ∣ γ ⊢ᴳ L ⊕[ op at ℓ ] M ⊑ L′ ⊕[ op at ℓ ] M′
        ⦂ primResultTy op ⊑ primResultTy op ∶ primResultTy-⊑ μ op

------------------------------------------------------------------------
-- Typing projections
------------------------------------------------------------------------

lookup-srcⁱ : ∀ {Δ} {μ : ImpEnv Δ} {γ : CtxImp μ} {x A B p}
  → γ ∋ⁱ x ⦂ ctx-imp A B p
  → srcCtxⁱ γ T.∋ x ⦂ A
lookup-srcⁱ Zⁱ = T.Z
lookup-srcⁱ (Sⁱ x∈) = T.S (lookup-srcⁱ x∈)

lookup-tgtⁱ : ∀ {Δ} {μ : ImpEnv Δ} {γ : CtxImp μ} {x A B p}
  → γ ∋ⁱ x ⦂ ctx-imp A B p
  → tgtCtxⁱ γ T.∋ x ⦂ B
lookup-tgtⁱ Zⁱ = T.Z
lookup-tgtⁱ (Sⁱ x∈) = T.S (lookup-tgtⁱ x∈)

mutual
  gradual-term-imprecision-source-typing : ∀ {Δ} {μ : ImpEnv Δ}
      {γ : CtxImp μ} {M M′ A B p}
    → μ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p
    → Δ ∣ srcCtxⁱ γ ⊢ M ⦂ A

  gradual-term-imprecision-target-typing : ∀ {Δ} {μ : ImpEnv Δ}
      {γ : CtxImp μ} {M M′ A B p}
    → μ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p
    → Δ ∣ tgtCtxⁱ γ ⊢ M′ ⦂ B

  gradual-term-imprecision-source-typing (x⊑xᴳ x∈) =
    ⊢` (lookup-srcⁱ x∈)
  gradual-term-imprecision-source-typing (ƛ⊑ƛᴳ N⊑N′) =
    ⊢ƛ (gradual-term-imprecision-source-typing N⊑N′)
  gradual-term-imprecision-source-typing
      (·⊑·ᴳ L⊑L′ M⊑M′ A∼C A′∼C′) =
    ⊢· (gradual-term-imprecision-source-typing L⊑L′)
       (gradual-term-imprecision-source-typing M⊑M′)
       A∼C
  gradual-term-imprecision-source-typing
      (·⊑·★ᴳ L⊑L′ M⊑M′ A∼C C′∼★) =
    ⊢· (gradual-term-imprecision-source-typing L⊑L′)
       (gradual-term-imprecision-source-typing M⊑M′)
       A∼C
  gradual-term-imprecision-source-typing
      (·★⊑·★ᴳ L⊑L′ M⊑M′ C∼★ C′∼★) =
    ⊢·★ (gradual-term-imprecision-source-typing L⊑L′)
        (gradual-term-imprecision-source-typing M⊑M′)
        C∼★
  gradual-term-imprecision-source-typing
      (Λ⊑Λᴳ liftγ vV vV′ zero∈A zero∈B V⊑V′) =
    ⊢Λ {zero∈A = zero∈A} vV
      (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _) (srcCtxⁱ-lift liftγ)
        (gradual-term-imprecision-source-typing V⊑V′))
  gradual-term-imprecision-source-typing
      (Λ⊑ᴳ Anv zero∈A liftγ vV V⊑N′) =
    ⊢Λ {zero∈A = zero∈A} vV
      (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _) (srcCtxⁱ-lift liftγ)
        (gradual-term-imprecision-source-typing V⊑N′))
  gradual-term-imprecision-source-typing ([]⊑[]ᴳ M⊑M′ q r) =
    ⊢• (gradual-term-imprecision-source-typing M⊑M′)
  gradual-term-imprecision-source-typing ([]⊑ᴳ M⊑M′ q r) =
    ⊢• (gradual-term-imprecision-source-typing M⊑M′)
  gradual-term-imprecision-source-typing (κ⊑κᴳ κ) =
    ⊢$ κ
  gradual-term-imprecision-source-typing
      (⊕⊑⊕ᴳ op L⊑L′ A∼arg A′∼arg M⊑M′
        B∼arg B′∼arg) =
    ⊢⊕ op (gradual-term-imprecision-source-typing L⊑L′) A∼arg
      (gradual-term-imprecision-source-typing M⊑M′) B∼arg

  gradual-term-imprecision-target-typing (x⊑xᴳ x∈) =
    ⊢` (lookup-tgtⁱ x∈)
  gradual-term-imprecision-target-typing (ƛ⊑ƛᴳ N⊑N′) =
    ⊢ƛ (gradual-term-imprecision-target-typing N⊑N′)
  gradual-term-imprecision-target-typing
      (·⊑·ᴳ L⊑L′ M⊑M′ A∼C A′∼C′) =
    ⊢· (gradual-term-imprecision-target-typing L⊑L′)
       (gradual-term-imprecision-target-typing M⊑M′)
       A′∼C′
  gradual-term-imprecision-target-typing
      (·⊑·★ᴳ L⊑L′ M⊑M′ A∼C C′∼★) =
    ⊢·★ (gradual-term-imprecision-target-typing L⊑L′)
        (gradual-term-imprecision-target-typing M⊑M′)
        C′∼★
  gradual-term-imprecision-target-typing
      (·★⊑·★ᴳ L⊑L′ M⊑M′ C∼★ C′∼★) =
    ⊢·★ (gradual-term-imprecision-target-typing L⊑L′)
        (gradual-term-imprecision-target-typing M⊑M′)
        C′∼★
  gradual-term-imprecision-target-typing
      (Λ⊑Λᴳ liftγ vV vV′ zero∈A zero∈B V⊑V′) =
    ⊢Λ {zero∈A = zero∈B} vV′
      (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _) (tgtCtxⁱ-lift liftγ)
        (gradual-term-imprecision-target-typing V⊑V′))
  gradual-term-imprecision-target-typing
      (Λ⊑ᴳ Anv zero∈A liftγ vV V⊑N′) =
    typing-shift-invᴳ
      (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _) (tgtCtxⁱ-lift liftγ)
        (gradual-term-imprecision-target-typing V⊑N′))
  gradual-term-imprecision-target-typing ([]⊑[]ᴳ M⊑M′ q r) =
    ⊢• (gradual-term-imprecision-target-typing M⊑M′)
  gradual-term-imprecision-target-typing ([]⊑ᴳ M⊑M′ q r) =
    gradual-term-imprecision-target-typing M⊑M′
  gradual-term-imprecision-target-typing (κ⊑κᴳ κ) =
    ⊢$ κ
  gradual-term-imprecision-target-typing
      (⊕⊑⊕ᴳ op L⊑L′ A∼arg A′∼arg M⊑M′
        B∼arg B′∼arg) =
    ⊢⊕ op (gradual-term-imprecision-target-typing L⊑L′) A′∼arg
      (gradual-term-imprecision-target-typing M⊑M′) B′∼arg
