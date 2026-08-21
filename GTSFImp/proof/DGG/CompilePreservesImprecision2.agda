module proof.DGG.CompilePreservesImprecision2 where

-- File Charter:
--   * Proves the statement surface for compilation preserving gradual
--     term imprecision against the version-2 cast-term imprecision relation.
--   * The public initial world parks every source pivot in place: both
--     embeddings are identity, and the paired runtime stores are the same
--     compilation store.
--   * Depends on Compile, GradualTermImprecision,
--     proof.DGG.Elab, and proof.DGG.CastTermImprecision.

open import Data.List using ([]; _∷_)
open import Data.Fin using (zero)
import Data.Fin as Fin
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)

open import Types
open import TyStore using (TyStore; store-empty; store-lift)
open import TermCtx using (TermCtx; ⇑ᶜ)
import TermCtx as T
open import Consistency
  using (_⊢_∼_; _↪ᵗ_; id↪ᵗ; keep; skip; toRenameᵗ; symᶜ;
         renameᶜ)
open import Imprecision
open import GradualTerms using (GTerm)
import GradualTerms as G
import GradualTermImprecision as GTI
open import Compile using (compile; compile-value)
open import Primitives
  using (Const; Prim; addℕ; and𝔹; constTy; primArgTy; primResultTy;
         constTy-renameᵗ)
import CastTerms as C
open C using (⟨_,_,_⟩; _⊢_⦂_)
  renaming (`_ to `ᵀ_; ƛ_ to ƛᵀ_; _·_ to _·ᵀ_; Λ_ to Λᵀ_;
            _⦂∀_[_] to _⦂∀ᵀ_[_]; $ to $ᵀ;
            _⊕[_]_ to _⊕ᵀ[_]_; _⟨_⟩ to _⟨ᵀ_⟩)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open CTX using
  (World;
   initialWorld;
   initialWorld-ηᴸ;
   initialWorld-ηᴿ;
   initialWorld-sourceStore;
   initialWorld-targetStore;
   initialWorld-env)
open CTI2 using (_∣_⊢²_⊑_∶_)
import proof.DGG.Elab as CPI
import proof.DGG.ExampleTerms as Ex
import proof.DGG.Examples2 as Ex2
import proof.Imprecision as PI
open import proof.ImprecisionConsistency
  using (refl⊑; rename-⊑; toRenameᵗ-injective; ty-all-injective)
open import proof.TypeInTermSubst using
  (renameᵗ-pointwise-id; toRename-id-eq; toRename-keep-eq;
   rename-openᵗ; rename-occurs)

initial-embedᴸ : ∀ {Δ} {μ : ImpEnv Δ}
  → (A : Ty Δ)
  → CTX.embedᴸ (initialWorld μ) A ≡ A
initial-embedᴸ {μ = μ} A =
  trans (cong (λ η → renameᵗ (toRenameᵗ η) A) (initialWorld-ηᴸ μ))
    (renameᵗ-pointwise-id (toRenameᵗ id↪ᵗ) A toRename-id-eq)

initial-embedᴿ : ∀ {Δ} {μ : ImpEnv Δ}
  → (A : Ty Δ)
  → CTX.embedᴿ (initialWorld μ) A ≡ A
initial-embedᴿ {μ = μ} A =
  trans (cong (λ η → renameᵗ (toRenameᵗ η) A) (initialWorld-ηᴿ μ))
    (renameᵗ-pointwise-id (toRenameᵗ id↪ᵗ) A toRename-id-eq)

initial-⊑ : ∀ {Δ} {μ : ImpEnv Δ} {A B : Ty Δ}
  → μ ⊢ A ⊑ B
  → A CTX.⊑ᵂ⟨ initialWorld μ ⟩ B
initial-⊑ {μ = μ} {A = A} {B = B} p =
  CTX.imprecision-cong
    (trans
      (renameᵗ-pointwise-id (toRenameᵗ id↪ᵗ) A toRename-id-eq)
      (sym (initial-embedᴸ {μ = μ} A)))
    (trans
      (renameᵗ-pointwise-id (toRenameᵗ id↪ᵗ) B toRename-id-eq)
      (sym (initial-embedᴿ {μ = μ} B)))
    (rename-⊑ (toRenameᵗ id↪ᵗ) (toRenameᵗ-injective id↪ᵗ)
      (λ X eq →
        trans
          (cong (CTX.impEnvʷ (initialWorld μ)) (toRename-id-eq X))
          (trans (initialWorld-env μ X) eq)) p)

initialCtx : ∀ {Δ} {μ : ImpEnv Δ}
  → GTI.CtxImp μ
  → CTX.CtxImp (initialWorld μ)
initialCtx [] = []
initialCtx (GTI.ctx-imp A B p ∷ γ) =
  CTX.ctx-imp A B (initial-⊑ p) ∷
    initialCtx γ

initial-∋ : ∀ {Δ} {μ : ImpEnv Δ}
    {γ : GTI.CtxImp μ} {x A B p}
  → γ GTI.∋ⁱ x ⦂ GTI.ctx-imp A B p
  → initialCtx γ CTX.∋ʷ x ⦂
      CTX.ctx-imp A B (initial-⊑ p)
initial-∋ GTI.Zⁱ = CTX.Zʷ
initial-∋ (GTI.Sⁱ x∈) = CTX.Sʷ (initial-∋ x∈)

⊢²-retarget : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {M : C.Term Δᴸ} {M′ : C.Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p q : A CTX.⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W ∣ γ ⊢² M ⊑ M′ ∶ q
⊢²-retarget {W = W} {γ = γ} {M = M} {M′ = M′} {p = p} {q = q} d =
  subst≡ (λ r → W ∣ γ ⊢² M ⊑ M′ ∶ r) (PI.⊑-unique p q) d

SourceId : ∀ {Δᴿ Δ} → World Δ Δᴿ Δ → Set
SourceId W = ∀ X → toRenameᵗ (CTX.ηᴸʷ W) X ≡ X

EnvMatches : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ → ImpEnv Δ → Set
EnvMatches W μ = ∀ X → CTX.impEnvʷ W X ≡ μ X

matches-initial : ∀ {Δ} {μ : ImpEnv Δ}
  → EnvMatches (initialWorld μ) μ
matches-initial {μ = μ} = initialWorld-env μ

matches-liftBoth : ∀ {Δᴿ Δ} {μ : ImpEnv Δ}
    {W : World Δ Δᴿ Δ}
  → EnvMatches W μ
  → EnvMatches (CTX.liftWorldBoth X⊑X W) (extᵐ μ)
matches-liftBoth {W = W} matches Fin.zero = refl
matches-liftBoth {W = W} matches (Fin.suc X) = matches X

matches-liftLeft : ∀ {Δᴿ Δ} {μ : ImpEnv Δ}
    {W : World Δ Δᴿ Δ}
  → EnvMatches W μ
  → EnvMatches (CTX.liftWorldLeft W) (instᵐ μ)
matches-liftLeft {W = W} matches Fin.zero = refl
matches-liftLeft {W = W} matches (Fin.suc X) = matches X

sourceId-initial : ∀ {Δ} {μ : ImpEnv Δ}
  → SourceId (initialWorld μ)
sourceId-initial {μ = μ} X =
  trans (cong (λ η → toRenameᵗ η X) (initialWorld-ηᴸ μ))
    (toRename-id-eq X)

sourceId-liftBoth : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
  → (v : VarImp)
  → SourceId W
  → SourceId (CTX.liftWorldBoth v W)
sourceId-liftBoth v sid zero = refl
sourceId-liftBoth v sid (Fin.suc X) =
  cong Fin.suc (sid X)

sourceId-liftLeft : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
  → (v : VarImp)
  → SourceId W
  → SourceId (CTX.liftWorldLeft W)
sourceId-liftLeft v sid zero = refl
sourceId-liftLeft v sid (Fin.suc X) =
  cong Fin.suc (sid X)

sourceId-embedᴸ : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
  → SourceId W
  → (A : Ty Δ)
  → CTX.embedᴸ W A ≡ A
sourceId-embedᴸ {W = W} sid A =
  renameᵗ-pointwise-id (toRenameᵗ (CTX.ηᴸʷ W)) A sid

sourceId-⊑ : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {A : Ty Δ} {B : Ty Δᴿ}
  → (sid : SourceId W)
  → CTX.impEnvʷ W ⊢ A ⊑ CTX.embedᴿ W B
  → A CTX.⊑ᵂ⟨ W ⟩ B
sourceId-⊑ {W = W} {A = A} {B = B} sid p =
  subst≡ (λ L → CTX.impEnvʷ W ⊢ L ⊑ CTX.embedᴿ W B)
    (sym (sourceId-embedᴸ {W = W} sid A)) p

matched-⊑ : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {μ : ImpEnv Δ} {A B : Ty Δ}
  → EnvMatches W μ
  → μ ⊢ A ⊑ B
  → CTX.impEnvʷ W ⊢ A ⊑ B
matched-⊑ {W = W} {μ = μ} {A = A} {B = B} matches p =
  CTX.imprecision-cong
    (renameᵗ-pointwise-id (toRenameᵗ id↪ᵗ) A toRename-id-eq)
    (renameᵗ-pointwise-id (toRenameᵗ id↪ᵗ) B toRename-id-eq)
    (rename-⊑ (toRenameᵗ id↪ᵗ) (toRenameᵗ-injective id↪ᵗ)
      (λ X eq →
        trans
          (cong (CTX.impEnvʷ W) (toRename-id-eq X))
          (trans (matches X) eq)) p)

sourceId-⊑-eq : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {μ : ImpEnv Δ}
    {A : Ty Δ} {Bᶜ : Ty Δ} {B : Ty Δᴿ}
  → (sid : SourceId W)
  → Bᶜ ≡ CTX.embedᴿ W B
  → μ ⊢ A ⊑ Bᶜ
  → EnvMatches W μ
  → A CTX.⊑ᵂ⟨ W ⟩ B
sourceId-⊑-eq {W = W} {μ = μ} sid refl p matches =
  sourceId-⊑ {W = W} sid (matched-⊑ {W = W} {μ = μ} matches p)

renameᵗ-id↪ᵗ : ∀ {Δ} (A : Ty Δ)
  → renameᵗ (toRenameᵗ id↪ᵗ) A ≡ A
renameᵗ-id↪ᵗ A =
  renameᵗ-pointwise-id (toRenameᵗ id↪ᵗ) A toRename-id-eq

renameᵗ-skip-eq : ∀ {Δᴿ Δ} (η : Δᴿ ↪ᵗ Δ) (B : Ty Δᴿ)
  → renameᵗ (toRenameᵗ (skip η)) B
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) B)
renameᵗ-skip-eq η B =
  trans (renameᵗ-cong B (λ X → refl))
    (sym (renameᵗ-comp (toRenameᵗ η) Fin.suc B))

embedᴿ-liftBoth-shift : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
  → (v : VarImp)
  → (B : Ty Δᴿ)
  → CTX.embedᴿ (CTX.liftWorldBoth v W) (⇑ᵗ B)
      ≡ ⇑ᵗ (CTX.embedᴿ W B)
embedᴿ-liftBoth-shift {W = W} v B =
  trans (renameᵗ-cong (⇑ᵗ B) (toRename-keep-eq (CTX.ηᴿʷ W)))
    (renameᵗ-shift (toRenameᵗ (CTX.ηᴿʷ W)) B)

embedᴿ-liftLeft : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
  → (v : VarImp)
  → (B : Ty Δᴿ)
  → CTX.embedᴿ (CTX.liftWorldLeft W) B
      ≡ ⇑ᵗ (CTX.embedᴿ W B)
embedᴿ-liftLeft {W = W} v B =
  renameᵗ-skip-eq (CTX.ηᴿʷ W) B

constTy-embedᴿ : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
  → (κ : Const)
  → CTX.embedᴿ W (constTy κ) ≡ constTy κ
constTy-embedᴿ {W = W} κ =
  sym (constTy-renameᵗ (toRenameᵗ (CTX.ηᴿʷ W)) κ)

primArgTy-embedᴿ : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
  → (op : Prim)
  → CTX.embedᴿ W (primArgTy op) ≡ primArgTy op
primArgTy-embedᴿ addℕ = refl
primArgTy-embedᴿ and𝔹 = refl

primResultTy-embedᴿ : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
  → (op : Prim)
  → CTX.embedᴿ W (primResultTy op) ≡ primResultTy op
primResultTy-embedᴿ addℕ = refl
primResultTy-embedᴿ and𝔹 = refl

Grenameᵐ-rename : ∀ {Δ₀ Δ Δ′} (ρ : Δ ⇒ʳ Δ′)
    (η : Δ₀ ↪ᵗ Δ) (η′ : Δ₀ ↪ᵗ Δ′)
  → (∀ X → ρ (toRenameᵗ η X) ≡ toRenameᵗ η′ X)
  → (M : GTerm Δ₀)
  → G.renameᵗᴳ ρ (CPI.Grenameᵐ η M) ≡ CPI.Grenameᵐ η′ M
Grenameᵐ-rename ρ η η′ eq (G.` x) = refl
Grenameᵐ-rename ρ η η′ eq (G.ƛ A ⇒ M) =
  cong₂ G.ƛ_⇒_ A-eq (Grenameᵐ-rename ρ η η′ eq M)
  where
  A-eq =
    trans (renameᵗ-comp (toRenameᵗ η) ρ A)
      (renameᵗ-cong A eq)
Grenameᵐ-rename ρ η η′ eq (L G.·[ ℓ ] M) =
  cong₂ (λ L′ M′ → L′ G.·[ ℓ ] M′)
    (Grenameᵐ-rename ρ η η′ eq L)
    (Grenameᵐ-rename ρ η η′ eq M)
Grenameᵐ-rename ρ η η′ eq (G.Λ M) =
  cong G.Λ_ (Grenameᵐ-rename (extᵗ ρ) (keep η) (keep η′) ext-eq M)
  where
  ext-eq : ∀ X
    → extᵗ ρ (toRenameᵗ (keep η) X) ≡ toRenameᵗ (keep η′) X
  ext-eq Fin.zero = refl
  ext-eq (Fin.suc X) = cong Fin.suc (eq X)
Grenameᵐ-rename ρ η η′ eq (M G.`[ A ]) =
  cong₂ G._`[_] (Grenameᵐ-rename ρ η η′ eq M) A-eq
  where
  A-eq =
    trans (renameᵗ-comp (toRenameᵗ η) ρ A)
      (renameᵗ-cong A eq)
Grenameᵐ-rename ρ η η′ eq (G.$ κ) = refl
Grenameᵐ-rename ρ η η′ eq (L G.⊕[ op at ℓ ] M) =
  cong₂ (λ L′ M′ → L′ G.⊕[ op at ℓ ] M′)
    (Grenameᵐ-rename ρ η η′ eq L)
    (Grenameᵐ-rename ρ η η′ eq M)

Grenameᵐ-skip : ∀ {Δᴿ Δ} (η : Δᴿ ↪ᵗ Δ) (M : GTerm Δᴿ)
  → G.⇑ᵗᴳ (CPI.Grenameᵐ η M) ≡ CPI.Grenameᵐ (skip η) M
Grenameᵐ-skip η M =
  Grenameᵐ-rename Fin.suc η (skip η) (λ X → refl) M

Grenameᵐ-id : ∀ {Δ} (M : GTerm Δ)
  → CPI.Grenameᵐ id↪ᵗ M ≡ M
Grenameᵐ-id (G.` x) = refl
Grenameᵐ-id (G.ƛ A ⇒ M) =
  cong₂ G.ƛ_⇒_ (renameᵗ-id↪ᵗ A) (Grenameᵐ-id M)
Grenameᵐ-id (L G.·[ ℓ ] M) =
  cong₂ (λ L′ M′ → L′ G.·[ ℓ ] M′)
    (Grenameᵐ-id L) (Grenameᵐ-id M)
Grenameᵐ-id (G.Λ M) =
  cong G.Λ_ (Grenameᵐ-id M)
Grenameᵐ-id (M G.`[ A ]) =
  cong₂ G._`[_] (Grenameᵐ-id M) (renameᵗ-id↪ᵗ A)
Grenameᵐ-id (G.$ κ) = refl
Grenameᵐ-id (L G.⊕[ op at ℓ ] M) =
  cong₂ (λ L′ M′ → L′ G.⊕[ op at ℓ ] M′)
    (Grenameᵐ-id L) (Grenameᵐ-id M)

data EmbeddedCtx {Δᴿ Δ} (W : World Δ Δᴿ Δ) (sid : SourceId W)
    {μ : ImpEnv Δ} (matches : EnvMatches W μ) :
    GTI.CtxImp μ → TermCtx Δᴿ →
    CTX.CtxImp W → Set where

  embedded-[] : EmbeddedCtx W sid matches [] [] []

  embedded-∷ : ∀ {γ Γ δ A Bᶜ B p q}
    → (eqB : Bᶜ ≡ CTX.embedᴿ W B)
    → q ≡ sourceId-⊑-eq {W = W} sid eqB p matches
    → EmbeddedCtx W sid matches γ Γ δ
      ---------------------------------------------------------------
    → EmbeddedCtx W sid matches
        (GTI.ctx-imp A Bᶜ p ∷ γ)
        (B ∷ Γ)
        (CTX.ctx-imp A B q ∷ δ)

embeddedMatches : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {μ : ImpEnv Δ} {sid : SourceId W} {matches : EnvMatches W μ}
    {γ Γ δ}
  → EmbeddedCtx W sid matches γ Γ δ
  → EnvMatches W μ
embeddedMatches {matches = matches} rel = matches

embedded-sourceId-⊑-eq : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {μ : ImpEnv Δ} {sid : SourceId W} {matches : EnvMatches W μ}
    {γ Γ δ A Bᶜ B}
  → EmbeddedCtx W sid matches γ Γ δ
  → Bᶜ ≡ CTX.embedᴿ W B
  → μ ⊢ A ⊑ Bᶜ
  → A CTX.⊑ᵂ⟨ W ⟩ B
embedded-sourceId-⊑-eq {W = W} {sid = sid} {matches = matches}
    rel eqB p =
  sourceId-⊑-eq {W = W} sid eqB p matches

embeddedCtx-target : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {μ : ImpEnv Δ} {sid : SourceId W} {matches : EnvMatches W μ}
    {γ Γ δ}
  → EmbeddedCtx W sid matches γ Γ δ
  → GTI.tgtCtxⁱ γ ≡ T.renameCtx (toRenameᵗ (CTX.ηᴿʷ W)) Γ
embeddedCtx-target embedded-[] = refl
embeddedCtx-target (embedded-∷ eqB q-ok rel) =
  cong₂ _∷_ eqB (embeddedCtx-target rel)

embeddedCtx-targetʷ : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {μ : ImpEnv Δ} {sid : SourceId W} {matches : EnvMatches W μ}
    {γ Γ δ}
  → EmbeddedCtx W sid matches γ Γ δ
  → CTX.tgtCtxʷ δ ≡ Γ
embeddedCtx-targetʷ embedded-[] = refl
embeddedCtx-targetʷ (embedded-∷ eqB q-ok rel) =
  cong (_ ∷_) (embeddedCtx-targetʷ rel)

record EmbeddedLookup {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {μ : ImpEnv Δ} {sid : SourceId W} {matches : EnvMatches W μ}
    {γ Γ δ x A Bᶜ p}
    (rel : EmbeddedCtx W sid matches γ Γ δ)
    (x∈ : γ GTI.∋ⁱ x ⦂ GTI.ctx-imp A Bᶜ p) : Set where
  constructor embedded-lookup
  field
    B : Ty Δᴿ
    eqB : Bᶜ ≡ CTX.embedᴿ W B
    q : A CTX.⊑ᵂ⟨ W ⟩ B
    q-ok : q ≡ sourceId-⊑-eq {W = W} sid eqB p matches
    Γ∋ : Γ T.∋ x ⦂ B
    δ∋ : δ CTX.∋ʷ x ⦂ CTX.ctx-imp A B q

embedded-lookup-at : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {μ : ImpEnv Δ} {sid : SourceId W} {matches : EnvMatches W μ}
    {γ Γ δ x A Bᶜ p}
  → (rel : EmbeddedCtx W sid matches γ Γ δ)
  → (x∈ : γ GTI.∋ⁱ x ⦂ GTI.ctx-imp A Bᶜ p)
  → EmbeddedLookup rel x∈
embedded-lookup-at (embedded-∷ {B = B} {q = q} eqB q-ok rel) GTI.Zⁱ =
  embedded-lookup B eqB q q-ok T.Z CTX.Zʷ
embedded-lookup-at (embedded-∷ eqB q-ok rel) (GTI.Sⁱ x∈)
    with embedded-lookup-at rel x∈
embedded-lookup-at (embedded-∷ eqB q-ok rel) (GTI.Sⁱ x∈)
    | embedded-lookup B eqB′ q q-ok′ Γ∋ δ∋ =
  embedded-lookup B eqB′ q q-ok′ (T.S Γ∋) (CTX.Sʷ δ∋)

record LiftBothPack {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {μ : ImpEnv Δ} {sid : SourceId W} {matches : EnvMatches W μ}
    {γ Γ δ γ′}
    (rel : EmbeddedCtx W sid matches γ Γ δ)
    (liftγ : GTI.LiftCtxⁱ (extᵐ μ) γ γ′)
    : Set where
  constructor lift-both-pack
  field
    δ′ : CTX.CtxImp (CTX.liftWorldBoth X⊑X W)
    lift² : CTX.LiftCtx X⊑X δ δ′
    rel′ : EmbeddedCtx (CTX.liftWorldBoth X⊑X W)
      (sourceId-liftBoth {W = W} X⊑X sid)
      (matches-liftBoth {W = W} matches) γ′ (⇑ᶜ Γ) δ′

record LiftLeftPack {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {μ : ImpEnv Δ} {sid : SourceId W} {matches : EnvMatches W μ}
    {γ Γ δ γ′}
    (rel : EmbeddedCtx W sid matches γ Γ δ)
    (liftγ : GTI.LiftCtxⁱ (instᵐ μ) γ γ′)
    : Set where
  constructor lift-left-pack
  field
    δ′ : CTX.CtxImp (CTX.liftWorldLeft W)
    lift² : CTX.LiftCtxᴸ X⊑★ δ δ′
    rel′ : EmbeddedCtx (CTX.liftWorldLeft W)
      (sourceId-liftLeft {W = W} X⊑★ sid)
      (matches-liftLeft {W = W} matches) γ′ Γ δ′

embedded-liftBoth : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {μ : ImpEnv Δ} {sid : SourceId W} {matches : EnvMatches W μ}
    {γ Γ δ γ′}
  → (rel : EmbeddedCtx W sid matches γ Γ δ)
  → (liftγ : GTI.LiftCtxⁱ (extᵐ μ) γ γ′)
  → LiftBothPack rel liftγ
embedded-liftBoth embedded-[] GTI.lift-[] =
  record { δ′ = [] ; lift² = CTX.lift-[] ; rel′ = embedded-[] }
embedded-liftBoth {W = W} {sid = sid} {matches = matches}
    (embedded-∷ {A = A} {B = B} eqB q-ok rel)
    (GTI.lift-∷ {p′ = p′} liftγ)
    with embedded-liftBoth rel liftγ
embedded-liftBoth {W = W} {sid = sid} {matches = matches}
    (embedded-∷ {A = A} {B = B} eqB q-ok rel)
    (GTI.lift-∷ {p′ = p′} liftγ)
    | lift-both-pack δ′ lift² rel′ =
  record
    { δ′ = CTX.ctx-imp (⇑ᵗ A) (⇑ᵗ B) q′ ∷ δ′
    ; lift² = CTX.lift-∷ lift²
    ; rel′ = embedded-∷ {W = CTX.liftWorldBoth X⊑X W}
        eqB′ refl rel′
    }
  where
  eqB′ =
    trans (cong ⇑ᵗ eqB)
      (sym (embedᴿ-liftBoth-shift {W = W} X⊑X B))

  q′ =
    sourceId-⊑-eq {W = CTX.liftWorldBoth X⊑X W}
      (sourceId-liftBoth {W = W} X⊑X sid)
      eqB′ p′ (matches-liftBoth {W = W} matches)

embedded-liftLeft : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {μ : ImpEnv Δ} {sid : SourceId W} {matches : EnvMatches W μ}
    {γ Γ δ γ′}
  → (rel : EmbeddedCtx W sid matches γ Γ δ)
  → (liftγ : GTI.LiftCtxⁱ (instᵐ μ) γ γ′)
  → LiftLeftPack rel liftγ
embedded-liftLeft embedded-[] GTI.lift-[] =
  record { δ′ = [] ; lift² = CTX.liftᴸ-[] ; rel′ = embedded-[] }
embedded-liftLeft {W = W} {sid = sid} {matches = matches}
    (embedded-∷ {A = A} {B = B} eqB q-ok rel)
    (GTI.lift-∷ {p′ = p′} liftγ)
    with embedded-liftLeft rel liftγ
embedded-liftLeft {W = W} {sid = sid} {matches = matches}
    (embedded-∷ {A = A} {B = B} eqB q-ok rel)
    (GTI.lift-∷ {p′ = p′} liftγ)
    | lift-left-pack δ′ lift² rel′ =
  record
    { δ′ = CTX.ctx-imp (⇑ᵗ A) B q′ ∷ δ′
    ; lift² = CTX.liftᴸ-∷ lift²
    ; rel′ = embedded-∷ {W = CTX.liftWorldLeft W}
        eqB′ refl rel′
    }
  where
  eqB′ =
    trans (cong ⇑ᵗ eqB)
      (sym (embedᴿ-liftLeft {W = W} X⊑★ B))

  q′ =
    sourceId-⊑-eq {W = CTX.liftWorldLeft W}
      (sourceId-liftLeft {W = W} X⊑★ sid)
      eqB′ p′ (matches-liftLeft {W = W} matches)

embedded-elab-gradual-typing : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {μ : ImpEnv Δ} {sid : SourceId W} {matches : EnvMatches W μ}
    {γ Γ δ M′ Mᴿ Bᶜ B N}
  → (rel : EmbeddedCtx W sid matches γ Γ δ)
  → M′ ≡ CPI.Grenameᵐ (CTX.ηᴿʷ W) Mᴿ
  → Bᶜ ≡ CTX.embedᴿ W B
  → CPI.Elab (CTX.targetStoreʷ W) Γ Mᴿ N B
  → Δ G.∣ GTI.tgtCtxⁱ γ ⊢ M′ ⦂ Bᶜ
embedded-elab-gradual-typing {W = W} rel eqM eqB Mᴱ =
  subst≡ (λ T → _ G.∣ _ ⊢ _ ⦂ T) (sym eqB)
    (subst≡ (λ M → _ G.∣ _ ⊢ M ⦂ CTX.embedᴿ W _)
      (sym eqM)
      (subst≡ (λ Γ → _ G.∣ Γ ⊢ _ ⦂ CTX.embedᴿ W _)
        (sym (embeddedCtx-target rel))
        (CPI.elab-gradual-typing
          (CPI.rename-elab {Σ′ = CTX.sourceStoreʷ W}
            (CTX.ηᴿʷ W) Mᴱ))))

embedded-elab-cast-typing : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {μ : ImpEnv Δ} {sid : SourceId W} {matches : EnvMatches W μ}
    {γ Γ δ Mᴿ N B}
  → (rel : EmbeddedCtx W sid matches γ Γ δ)
  → CPI.Elab (CTX.targetStoreʷ W) Γ Mᴿ N B
  → ⟨ Δᴿ , CTX.targetStoreʷ W , CTX.tgtCtxʷ δ ⟩ ⊢ N ⦂ B
embedded-elab-cast-typing rel Mᴱ =
  subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
    (sym (embeddedCtx-targetʷ rel)) (CPI.elab-cast-typing Mᴱ)

compile-preserves-embedded² : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    (sid : SourceId W)
    {μ : ImpEnv Δ} {matches : EnvMatches W μ}
    {γ : GTI.CtxImp μ} {Γ : TermCtx Δᴿ}
    {δ : CTX.CtxImp W} {M M′ : GTerm Δ} {Mᴿ : GTerm Δᴿ}
    {A Bᶜ : Ty Δ} {B : Ty Δᴿ} {p} {N : C.Term Δᴿ}
  → (rel : EmbeddedCtx W sid matches γ Γ δ)
  → (M⊑M′ : μ GTI.∣ γ ⊢ᴳ M ⊑ M′
      ⦂ A ⊑ Bᶜ ∶ p)
  → (eqM : M′ ≡ CPI.Grenameᵐ (CTX.ηᴿʷ W) Mᴿ)
  → (eqB : Bᶜ ≡ CTX.embedᴿ W B)
  → CPI.Elab (CTX.targetStoreʷ W) Γ Mᴿ N B
  → W ∣ δ ⊢²
      proj₁ (compile {Σ = CTX.sourceStoreʷ W}
        (GTI.gradual-term-imprecision-source-typing M⊑M′))
      ⊑ N ∶ sourceId-⊑-eq {W = W} sid eqB p matches
compile-preserves-embedded² sid rel (GTI.x⊑xᴳ x∈) refl eqB
    (CPI.E-` x∈′)
    with embedded-lookup-at rel x∈
compile-preserves-embedded² sid rel (GTI.x⊑xᴳ x∈) refl eqB
    (CPI.E-` x∈′)
    | embedded-lookup B eqB′ q q-ok Γ∋ δ∋
    with CPI.lookup-uniqueᴳ Γ∋ x∈′
compile-preserves-embedded² sid rel (GTI.x⊑xᴳ x∈) refl eqB
    (CPI.E-` x∈′)
    | embedded-lookup B eqB′ q q-ok Γ∋ δ∋ | refl =
  ⊢²-retarget (CTI2.x⊑x² δ∋)
compile-preserves-embedded² {W = W} sid rel
    (GTI.ƛ⊑ƛᴳ N⊑N′) refl refl (CPI.E-ƛ N′ᴱ)
    with compile {Σ = CTX.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing N⊑N′)
       | compile-preserves-embedded² sid
      (embedded-∷ refl refl rel) N⊑N′ refl refl N′ᴱ
compile-preserves-embedded² {W = W} sid rel
    (GTI.ƛ⊑ƛᴳ N⊑N′) refl refl (CPI.E-ƛ N′ᴱ)
    | N , N⊢ | N⊑N′² =
  ⊢²-retarget (CTI2.ƛ⊑ƛ² N⊑N′²)
compile-preserves-embedded² {W = W} sid rel
    (GTI.·⊑·ᴳ {pA = pA} {pB = pB}
      L⊑L′ M⊑M′ A∼C A′∼C′)
    refl refl (CPI.E-· L′ᴱ M′ᴱ A′∼D′ d′)
    with CPI.typing-uniqueᴳ
      (embedded-elab-gradual-typing rel refl refl L′ᴱ)
      (GTI.gradual-term-imprecision-target-typing L⊑L′)
       | CPI.typing-uniqueᴳ
      (embedded-elab-gradual-typing rel refl refl M′ᴱ)
      (GTI.gradual-term-imprecision-target-typing M⊑M′)
compile-preserves-embedded² {W = W} sid rel
    (GTI.·⊑·ᴳ {pA = pA} {pB = pB}
      L⊑L′ M⊑M′ A∼C A′∼C′)
    refl refl (CPI.E-· L′ᴱ M′ᴱ A′∼D′ d′)
    | refl | refl
    with compile {Σ = CTX.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing L⊑L′)
       | compile-preserves-embedded² sid rel L⊑L′ refl refl L′ᴱ
       | compile {Σ = CTX.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile-preserves-embedded² sid rel M⊑M′ refl refl M′ᴱ
compile-preserves-embedded² {W = W} sid rel
    (GTI.·⊑·ᴳ {pA = pA} {pB = pB}
      L⊑L′ M⊑M′ A∼C A′∼C′)
    refl refl (CPI.E-· L′ᴱ M′ᴱ A′∼D′ d′)
    | refl | refl | L , L⊢ | L⊑L′² | M , M⊢ | M⊑M′² =
  ⊢²-retarget
    (CTI2.·⊑·²
      (⊢²-retarget
        {q = ⇒⊑⇒ (embedded-sourceId-⊑-eq rel refl pA)
                  (embedded-sourceId-⊑-eq rel refl pB)}
        L⊑L′²)
      (CTI2.cast⊑cast² (symᶜ A∼C) d′ M⊑M′²
        (embedded-sourceId-⊑-eq rel refl pA)))
compile-preserves-embedded² sid rel
    (GTI.·⊑·ᴳ L⊑L′ M⊑M′ A∼C A′∼C′)
    refl eqB (CPI.E-·★ L′ᴱ M′ᴱ D′∼★ c′ d′)
    with CPI.typing-uniqueᴳ
      (GTI.gradual-term-imprecision-target-typing L⊑L′)
      (embedded-elab-gradual-typing rel refl refl L′ᴱ)
compile-preserves-embedded² sid rel
    (GTI.·⊑·ᴳ L⊑L′ M⊑M′ A∼C A′∼C′)
    refl eqB (CPI.E-·★ L′ᴱ M′ᴱ D′∼★ c′ d′)
    | ()
compile-preserves-embedded² sid rel
    (GTI.·⊑·★ᴳ L⊑L′ M⊑M′ A∼C C′∼★)
    refl eqB (CPI.E-· L′ᴱ M′ᴱ A′∼D′ d′)
    with CPI.typing-uniqueᴳ
      (GTI.gradual-term-imprecision-target-typing L⊑L′)
      (embedded-elab-gradual-typing rel refl refl L′ᴱ)
compile-preserves-embedded² sid rel
    (GTI.·⊑·★ᴳ L⊑L′ M⊑M′ A∼C C′∼★)
    refl eqB (CPI.E-· L′ᴱ M′ᴱ A′∼D′ d′)
    | ()
compile-preserves-embedded² {W = W} sid rel
    (GTI.·⊑·★ᴳ {pA = pA} {pB = pB}
      L⊑L′ M⊑M′ A∼C C′∼★)
    refl refl (CPI.E-·★ L′ᴱ M′ᴱ D′∼★ c′ d′)
    with CPI.typing-uniqueᴳ
      (embedded-elab-gradual-typing rel refl refl M′ᴱ)
      (GTI.gradual-term-imprecision-target-typing M⊑M′)
compile-preserves-embedded² {W = W} sid rel
    (GTI.·⊑·★ᴳ {pA = pA} {pB = pB}
      L⊑L′ M⊑M′ A∼C C′∼★)
    refl refl (CPI.E-·★ L′ᴱ M′ᴱ D′∼★ c′ d′)
    | refl
    with compile {Σ = CTX.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing L⊑L′)
       | compile-preserves-embedded² sid rel L⊑L′ refl refl L′ᴱ
       | compile {Σ = CTX.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile-preserves-embedded² sid rel M⊑M′ refl refl M′ᴱ
compile-preserves-embedded² {W = W} sid rel
    (GTI.·⊑·★ᴳ {pA = pA} {pB = pB}
      L⊑L′ M⊑M′ A∼C C′∼★)
    refl refl (CPI.E-·★ L′ᴱ M′ᴱ D′∼★ c′ d′)
    | refl | L , L⊢ | L⊑L′² | M , M⊢ | M⊑M′² =
  ⊢²-retarget
    (CTI2.·⊑·²
      (⊢²-retarget
        {q = ⇒⊑⇒ (embedded-sourceId-⊑-eq rel refl pA)
                  (embedded-sourceId-⊑-eq rel refl pB)}
        (CTI2.⊑cast² c′ L⊑L′²
          (embedded-sourceId-⊑-eq rel refl (⇒⊑⇒ pA pB))))
      (CTI2.cast⊑cast² (symᶜ A∼C) d′ M⊑M′²
        (embedded-sourceId-⊑-eq rel refl pA)))
compile-preserves-embedded² sid rel
    (GTI.·★⊑·★ᴳ L⊑L′ M⊑M′ C∼★ C′∼★)
    refl eqB (CPI.E-· L′ᴱ M′ᴱ A′∼D′ d′)
    with CPI.typing-uniqueᴳ
      (GTI.gradual-term-imprecision-target-typing L⊑L′)
      (embedded-elab-gradual-typing rel refl refl L′ᴱ)
compile-preserves-embedded² sid rel
    (GTI.·★⊑·★ᴳ L⊑L′ M⊑M′ C∼★ C′∼★)
    refl eqB (CPI.E-· L′ᴱ M′ᴱ A′∼D′ d′)
    | ()
compile-preserves-embedded² {W = W} sid rel
    (GTI.·★⊑·★ᴳ L⊑L′ M⊑M′ C∼★ C′∼★)
    refl refl (CPI.E-·★ L′ᴱ M′ᴱ D′∼★ c′ d′)
    with CPI.typing-uniqueᴳ
      (embedded-elab-gradual-typing rel refl refl M′ᴱ)
      (GTI.gradual-term-imprecision-target-typing M⊑M′)
compile-preserves-embedded² {W = W} sid rel
    (GTI.·★⊑·★ᴳ L⊑L′ M⊑M′ C∼★ C′∼★)
    refl refl (CPI.E-·★ L′ᴱ M′ᴱ D′∼★ c′ d′)
    | refl
    with compile {Σ = CTX.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing L⊑L′)
       | compile-preserves-embedded² sid rel L⊑L′ refl refl L′ᴱ
       | compile {Σ = CTX.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile-preserves-embedded² sid rel M⊑M′ refl refl M′ᴱ
compile-preserves-embedded² {W = W} sid rel
    (GTI.·★⊑·★ᴳ L⊑L′ M⊑M′ C∼★ C′∼★)
    refl refl (CPI.E-·★ L′ᴱ M′ᴱ D′∼★ c′ d′)
    | refl | L , L⊢ | L⊑L′² | M , M⊢ | M⊑M′² =
  ⊢²-retarget
    (CTI2.·⊑·²
      (⊢²-retarget
        {q = ⇒⊑⇒ (embedded-sourceId-⊑-eq rel refl ★⊑★)
                  (embedded-sourceId-⊑-eq rel refl ★⊑★)}
        (CTI2.cast⊑cast² CPI.dynamic-function-cast c′ L⊑L′²
          (embedded-sourceId-⊑-eq rel refl (⇒⊑⇒ ★⊑★ ★⊑★))))
      (CTI2.cast⊑cast² C∼★ d′ M⊑M′²
        (embedded-sourceId-⊑-eq rel refl ★⊑★)))
compile-preserves-embedded² {W = W} sid {matches = matches} rel
    (GTI.Λ⊑Λᴳ {p = p} liftγ vV vV′ zero∈A zero∈B V⊑V′)
    refl eqB (CPI.E-Λ zero∈B′ vV′′ vN′ V′ᴱ)
    rewrite CPI.compile-Λ-term {Σ = CTX.sourceStoreʷ W}
      {Γ = GTI.srcCtxⁱ _}
      {zero∈A = zero∈A} vV
      (subst≡ (λ Γ → _ G.∣ Γ ⊢ _ ⦂ _) (GTI.srcCtxⁱ-lift liftγ)
        (GTI.gradual-term-imprecision-source-typing V⊑V′))
      | CPI.compile-context-subst
      {Σ = store-lift (CTX.sourceStoreʷ W)}
      (GTI.srcCtxⁱ-lift liftγ)
      (GTI.gradual-term-imprecision-source-typing V⊑V′)
    with embedded-liftBoth rel liftγ
compile-preserves-embedded² {W = W} sid {matches = matches} rel
    (GTI.Λ⊑Λᴳ {p = p} liftγ vV vV′ zero∈A zero∈B V⊑V′)
    refl eqB (CPI.E-Λ zero∈B′ vV′′ vN′ V′ᴱ)
    | lift-both-pack δ′ lift² rel′ =
  ⊢²-retarget
    (CTI2.Λ⊑Λ² lift²
      (compile-value {Σ = store-lift (CTX.sourceStoreʷ W)} vV
        (GTI.gradual-term-imprecision-source-typing V⊑V′))
      vN′
      (compile-preserves-embedded²
        (sourceId-liftBoth {W = W} X⊑X sid)
        {matches = matches-liftBoth {W = W} matches}
        rel′ V⊑V′ refl body-eq V′ᴱ)
      (embedded-sourceId-⊑-eq rel eqB (∀⊑∀ p)))
  where
  body-eq =
    trans (ty-all-injective eqB)
      (sym (renameᵗ-cong _ (toRename-keep-eq (CTX.ηᴿʷ W))))
compile-preserves-embedded² {W = W} sid {matches = matches} rel
    (GTI.Λ⊑ᴳ {p = p} Anv zero∈A liftγ vV N′⊢ V⊑N′)
    eqM eqB N′ᴱ
    rewrite CPI.compile-Λ-term {Σ = CTX.sourceStoreʷ W}
      {Γ = GTI.srcCtxⁱ _}
      {zero∈A = zero∈A} vV
      (subst≡ (λ Γ → _ G.∣ Γ ⊢ _ ⦂ _) (GTI.srcCtxⁱ-lift liftγ)
        (GTI.gradual-term-imprecision-source-typing V⊑N′))
      | CPI.compile-context-subst
      {Σ = store-lift (CTX.sourceStoreʷ W)}
      (GTI.srcCtxⁱ-lift liftγ)
      (GTI.gradual-term-imprecision-source-typing V⊑N′)
    with embedded-liftLeft rel liftγ
compile-preserves-embedded² {W = W} sid {matches = matches} rel
    (GTI.Λ⊑ᴳ {p = p} Anv zero∈A liftγ vV N′⊢ V⊑N′)
    eqM eqB N′ᴱ
    | lift-left-pack δ′ lift² rel′ =
  ⊢²-retarget
    (CTI2.Λ⊑² Anv zero∈A lift²
      (compile-value {Σ = store-lift (CTX.sourceStoreʷ W)} vV
        (GTI.gradual-term-imprecision-source-typing V⊑N′))
      (embedded-elab-cast-typing rel N′ᴱ)
      (compile-preserves-embedded²
        (sourceId-liftLeft {W = W} X⊑★ sid)
        {matches = matches-liftLeft {W = W} matches}
        rel′ V⊑N′ term-eq type-eq N′ᴱ)
      (embedded-sourceId-⊑-eq rel eqB (∀⊑ Anv zero∈A p)))
  where
  term-eq =
    trans (cong G.⇑ᵗᴳ eqM)
      (Grenameᵐ-skip (CTX.ηᴿʷ W) _)

  type-eq =
    trans (cong ⇑ᵗ eqB)
      (sym (embedᴿ-liftLeft {W = W} X⊑★ _))
compile-preserves-embedded² {W = W} sid rel
    (GTI.[]⊑[]ᴳ {p = p} M⊑M′ q r)
    refl eqB (CPI.E-[] M′ᴱ eq)
    with CPI.typing-uniqueᴳ
      (GTI.gradual-term-imprecision-target-typing M⊑M′)
      (embedded-elab-gradual-typing rel refl refl M′ᴱ)
compile-preserves-embedded² {W = W} sid rel
    (GTI.[]⊑[]ᴳ {p = p} M⊑M′ q r)
    refl eqB (CPI.E-[] M′ᴱ eq)
    | body-eq
    with eq
compile-preserves-embedded² {W = W} sid rel
    (GTI.[]⊑[]ᴳ {p = p} M⊑M′ q r)
    refl eqB (CPI.E-[] M′ᴱ eq)
    | body-eq | refl
    with compile {Σ = CTX.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile-preserves-embedded² sid rel M⊑M′ refl body-eq M′ᴱ
compile-preserves-embedded² {W = W} sid rel
    (GTI.[]⊑[]ᴳ {p = p} M⊑M′ q r)
    refl eqB (CPI.E-[] M′ᴱ eq)
    | body-eq | refl | M , M⊢ | M⊑M′² =
  ⊢²-retarget
    (CTI2.•⊑•²
      (embedded-sourceId-⊑-eq rel body-eq (∀⊑∀ p))
      M⊑M′²
      (embedded-sourceId-⊑-eq rel refl q)
      (embedded-sourceId-⊑-eq rel eqB r))
compile-preserves-embedded² {W = W} sid rel
    (GTI.[]⊑ᴳ {p = p} {Anv = Anv} {zero∈A = zero∈A}
      M⊑M′ q r)
    eqM eqB M′ᴱ
    with compile {Σ = CTX.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile-preserves-embedded² sid rel M⊑M′ eqM eqB M′ᴱ
compile-preserves-embedded² {W = W} sid rel
    (GTI.[]⊑ᴳ {p = p} {Anv = Anv} {zero∈A = zero∈A}
      M⊑M′ q r)
    eqM eqB M′ᴱ
    | M , M⊢ | M⊑M′² =
  ⊢²-retarget
    (CTI2.•⊑²
      (embedded-sourceId-⊑-eq rel eqB (∀⊑ Anv zero∈A p))
      M⊑M′²
      (embedded-sourceId-⊑-eq rel refl q)
      (embedded-sourceId-⊑-eq rel eqB r))
compile-preserves-embedded² {W = W} sid {μ = μ} rel
    (GTI.κ⊑κᴳ κ) refl eqB (CPI.E-$ .κ) =
  ⊢²-retarget
    (CTI2.κ⊑κ² κ
      (embedded-sourceId-⊑-eq {B = constTy κ} rel
        (sym (constTy-embedᴿ {W = W} κ))
        (GTI.constTy-⊑ μ κ)))
compile-preserves-embedded² {W = W} sid {μ = μ} rel
    (GTI.⊕⊑⊕ᴳ op L⊑L′ A∼arg A′∼arg M⊑M′
      B∼arg B′∼arg)
    refl eqB
    (CPI.E-⊕ .op L′ᴱ A′∼arg′ c′ M′ᴱ B′∼arg′ d′)
    with CPI.typing-uniqueᴳ
      (embedded-elab-gradual-typing rel refl refl L′ᴱ)
      (GTI.gradual-term-imprecision-target-typing L⊑L′)
       | CPI.typing-uniqueᴳ
      (embedded-elab-gradual-typing rel refl refl M′ᴱ)
      (GTI.gradual-term-imprecision-target-typing M⊑M′)
compile-preserves-embedded² {W = W} sid {μ = μ} rel
    (GTI.⊕⊑⊕ᴳ op L⊑L′ A∼arg A′∼arg M⊑M′
      B∼arg B′∼arg)
    refl eqB
    (CPI.E-⊕ .op L′ᴱ A′∼arg′ c′ M′ᴱ B′∼arg′ d′)
    | refl | refl
    with compile {Σ = CTX.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing L⊑L′)
       | compile-preserves-embedded² sid rel L⊑L′ refl refl L′ᴱ
       | compile {Σ = CTX.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile-preserves-embedded² sid rel M⊑M′ refl refl M′ᴱ
compile-preserves-embedded² {W = W} sid {μ = μ} rel
    (GTI.⊕⊑⊕ᴳ op L⊑L′ A∼arg A′∼arg M⊑M′
      B∼arg B′∼arg)
    refl eqB
    (CPI.E-⊕ .op L′ᴱ A′∼arg′ c′ M′ᴱ B′∼arg′ d′)
    | refl | refl | L , L⊢ | L⊑L′² | M , M⊢ | M⊑M′² =
  ⊢²-retarget
    {q = embedded-sourceId-⊑-eq rel eqB
      (GTI.primResultTy-⊑ μ op)}
    (CTI2.⊕⊑⊕² op
      (CTI2.cast⊑cast² A∼arg c′ L⊑L′²
        (embedded-sourceId-⊑-eq {B = primArgTy op} rel
          (sym (primArgTy-embedᴿ {W = W} op))
          (refl⊑ (primArgTy op))))
      (CTI2.cast⊑cast² B∼arg d′ M⊑M′²
        (embedded-sourceId-⊑-eq {B = primArgTy op} rel
          (sym (primArgTy-embedᴿ {W = W} op))
          (refl⊑ (primArgTy op))))
      (embedded-sourceId-⊑-eq {B = primResultTy op} rel
        (sym (primResultTy-embedᴿ {W = W} op))
        (GTI.primResultTy-⊑ μ op)))

compile-preserves-identity-world² : ∀ {Δ}
    {W : World Δ Δ Δ} {μ : ImpEnv Δ}
    {M M′ : GTerm Δ} {A B p}
  → (source-id : CTX.ηᴸʷ W ≡ id↪ᵗ)
  → (target-id : CTX.ηᴿʷ W ≡ id↪ᵗ)
  → (matches : EnvMatches W μ)
  → (M⊑M′ : μ GTI.∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p)
  → W ∣ [] ⊢²
      proj₁ (compile {Σ = CTX.sourceStoreʷ W}
        (GTI.gradual-term-imprecision-source-typing M⊑M′))
      ⊑ proj₁ (compile {Σ = CTX.targetStoreʷ W}
        (GTI.gradual-term-imprecision-target-typing M⊑M′))
      ∶ sourceId-⊑-eq {W = W} {μ = μ} {A = A} {Bᶜ = B} {B = B}
          (λ X → trans (cong (λ η → toRenameᵗ η X) source-id)
            (toRename-id-eq X))
          (trans (sym (renameᵗ-id↪ᵗ B))
            (sym (cong
              (λ η → renameᵗ (toRenameᵗ η) B) target-id)))
          p matches
compile-preserves-identity-world² {W = W} {μ = μ} {M′ = M′} {B = B}
    source-id target-id matches M⊑M′ =
  compile-preserves-embedded² {W = W} sid {μ = μ} {matches = matches}
    (embedded-[] {W = W} {sid = sid} {matches = matches}) M⊑M′
    target-term-id target-type-id
    (CPI.compile-elab
      (GTI.gradual-term-imprecision-target-typing M⊑M′))
  where
  sid : SourceId W
  sid X = trans (cong (λ η → toRenameᵗ η X) source-id)
    (toRename-id-eq X)

  target-term-id : M′ ≡ CPI.Grenameᵐ (CTX.ηᴿʷ W) M′
  target-term-id =
    trans (sym (Grenameᵐ-id M′))
      (sym (cong (λ η → CPI.Grenameᵐ η M′) target-id))

  target-type-id : B ≡ CTX.embedᴿ W B
  target-type-id =
    trans (sym (renameᵗ-id↪ᵗ B))
      (sym (cong (λ η → renameᵗ (toRenameᵗ η) B) target-id))

initialEmbeddedCtx : ∀ {Δ} {μ : ImpEnv Δ}
  → (γ : GTI.CtxImp μ)
  → EmbeddedCtx (initialWorld μ) (sourceId-initial {μ = μ})
      (matches-initial {μ = μ}) γ
      (GTI.tgtCtxⁱ γ) (initialCtx γ)
initialEmbeddedCtx [] = embedded-[]
initialEmbeddedCtx {μ = μ} (GTI.ctx-imp A B p ∷ γ) =
  embedded-∷ (sym (initial-embedᴿ {μ = μ} B))
    (PI.⊑-unique (initial-⊑ p)
      (sourceId-⊑-eq {W = initialWorld μ}
        (sourceId-initial {μ = μ})
        (sym (initial-embedᴿ {μ = μ} B)) p
        (matches-initial {μ = μ})))
    (initialEmbeddedCtx γ)

compile-preserves-elab² : ∀ {Δ} {μ : ImpEnv Δ}
    {γ : GTI.CtxImp μ} {M M′ : GTerm Δ} {A B p}
    {N : C.Term Δ}
  → (M⊑M′ : μ GTI.∣ γ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p)
  → CPI.Elab (CTX.emptyStore Δ) (GTI.tgtCtxⁱ γ) M′ N B
  → initialWorld μ ∣ initialCtx γ ⊢²
      proj₁ (compile {Σ = CTX.emptyStore Δ}
        (GTI.gradual-term-imprecision-source-typing M⊑M′))
      ⊑ N ∶ initial-⊑ p
compile-preserves-elab² {μ = μ} {γ = γ} {M′ = M′}
    {B = B} {p = p} {N = N}
    M⊑M′ M′ᴱ =
  subst≡
    (λ L → initialWorld μ ∣ initialCtx γ ⊢²
      L ⊑ N ∶ initial-⊑ p)
    (cong
      (λ Σ → proj₁ (compile {Σ = Σ}
        (GTI.gradual-term-imprecision-source-typing M⊑M′)))
      (initialWorld-sourceStore μ))
    (⊢²-retarget
      (compile-preserves-embedded² {W = initialWorld μ}
        (sourceId-initial {μ = μ})
        (initialEmbeddedCtx γ) M⊑M′
        (trans (sym (Grenameᵐ-id M′))
          (sym (cong (λ η → CPI.Grenameᵐ η M′)
            (initialWorld-ηᴿ μ))))
        (sym (initial-embedᴿ {μ = μ} B))
        (subst≡
          (λ Σ → CPI.Elab Σ (GTI.tgtCtxⁱ γ) M′ N B)
          (sym (initialWorld-targetStore μ)) M′ᴱ)))

compile-preserves-imprecision²-statement : Set
compile-preserves-imprecision²-statement =
  ∀ {Δ} {μ : ImpEnv Δ}
    {γ : GTI.CtxImp μ} {M M′ : GTerm Δ} {A B p}
  → (M⊑M′ : μ GTI.∣ γ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p)
  → initialWorld μ ∣ initialCtx γ ⊢²
      proj₁ (compile {Σ = CTX.emptyStore Δ}
        (GTI.gradual-term-imprecision-source-typing M⊑M′))
      ⊑ proj₁ (compile {Σ = CTX.emptyStore Δ}
        (GTI.gradual-term-imprecision-target-typing M⊑M′))
      ∶ initial-⊑ p

compile-preserves-imprecision² :
  compile-preserves-imprecision²-statement
compile-preserves-imprecision² M⊑M′ =
  compile-preserves-elab² M⊑M′
    (CPI.compile-elab
      (GTI.gradual-term-imprecision-target-typing M⊑M′))

polyIdᴳ : GTerm 0
polyIdᴳ = G.Λ (G.ƛ ＇ 0 ⇒ G.` 0)

polyId⊑polyIdᴳ :
  idᵐ GTI.∣ [] ⊢ᴳ polyIdᴳ ⊑ polyIdᴳ
    ⦂ `∀ Ex.X⇒X ⊑ `∀ Ex.X⇒X ∶ ∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)
polyId⊑polyIdᴳ =
  GTI.Λ⊑Λᴳ GTI.lift-[] (G.ƛ ＇ 0 ⇒ G.` 0)
    (G.ƛ ＇ 0 ⇒ G.` 0)
    (∈-fun-left var-∈) (∈-fun-left var-∈)
    (GTI.ƛ⊑ƛᴳ (GTI.x⊑xᴳ GTI.Zⁱ))

polyId-validation :
  initialWorld (idᵐ {Δ = 0})
    ∣ initialCtx {μ = idᵐ {Δ = 0}} [] ⊢²
    proj₁ (compile {Σ = store-empty}
      (GTI.gradual-term-imprecision-source-typing polyId⊑polyIdᴳ))
    ⊑ proj₁ (compile {Σ = store-empty}
      (GTI.gradual-term-imprecision-target-typing polyId⊑polyIdᴳ))
    ∶ initial-⊑ {μ = idᵐ {Δ = 0}} (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X))
polyId-validation =
  subst≡
    (λ q → initialWorld (idᵐ {Δ = 0}) ∣ [] ⊢² Ex.polyId
      ⊑ Ex.polyId ∶ q)
    (PI.⊑-unique Ex2.example12-∀⊑∀
      (initial-⊑ {μ = idᵐ {Δ = 0}}
        (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X))))
    (Ex2.polyId-refl²ʷ {W = initialWorld (idᵐ {Δ = 0})})

polyId-validation-from-theorem :
  initialWorld (idᵐ {Δ = 0})
    ∣ initialCtx {μ = idᵐ {Δ = 0}} [] ⊢²
    proj₁ (compile {Σ = store-empty}
      (GTI.gradual-term-imprecision-source-typing polyId⊑polyIdᴳ))
    ⊑ proj₁ (compile {Σ = store-empty}
      (GTI.gradual-term-imprecision-target-typing polyId⊑polyIdᴳ))
    ∶ initial-⊑ {μ = idᵐ {Δ = 0}} (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X))
polyId-validation-from-theorem =
  compile-preserves-imprecision² polyId⊑polyIdᴳ
