module proof.DGG.CompilePreservesImprecision2 where

-- File Charter:
--   * Proves the statement surface for compilation preserving gradual
--     term imprecision against the version-2 cast-term imprecision relation.
--   * The public initial world parks every source pivot in place: both
--     embeddings are identity, and the paired runtime stores are the same
--     compilation store.
--   * Depends on Compile, GradualTermImprecision,
--     proof.DGG.Elab, and proof.DGG.CastTermImprecision2.

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
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using (World; world; _∣_⊢²_⊑_∶_)
import proof.DGG.Elab as CPI
import proof.DGG.ExampleTerms as Ex
import proof.DGG.Examples2 as Ex2
import proof.Imprecision as PI
open import proof.ImprecisionConsistency
  using (refl⊑; ty-all-injective)
open import proof.TypeInTermSubst using
  (renameᵗ-pointwise-id; toRename-id-eq; toRename-keep-eq;
   rename-openᵗ; rename-occurs)

initialWorld : ∀ {Δ} → ImpEnv Δ → TyStore Δ → World Δ Δ Δ
initialWorld μ Σ = world id↪ᵗ id↪ᵗ μ Σ Σ

initialWorld-ηᴸ : ∀ {Δ} (μ : ImpEnv Δ) (Σ : TyStore Δ)
  → CTI2.ηᴸʷ (initialWorld μ Σ) ≡ id↪ᵗ
initialWorld-ηᴸ μ Σ = refl

initialWorld-ηᴿ : ∀ {Δ} (μ : ImpEnv Δ) (Σ : TyStore Δ)
  → CTI2.ηᴿʷ (initialWorld μ Σ) ≡ id↪ᵗ
initialWorld-ηᴿ μ Σ = refl

initial-embedᴸ : ∀ {Δ} {μ : ImpEnv Δ} {Σ : TyStore Δ}
  → (A : Ty Δ)
  → CTI2.embedᴸ (initialWorld μ Σ) A ≡ A
initial-embedᴸ A =
  renameᵗ-pointwise-id (toRenameᵗ id↪ᵗ) A toRename-id-eq

initial-embedᴿ : ∀ {Δ} {μ : ImpEnv Δ} {Σ : TyStore Δ}
  → (A : Ty Δ)
  → CTI2.embedᴿ (initialWorld μ Σ) A ≡ A
initial-embedᴿ A =
  renameᵗ-pointwise-id (toRenameᵗ id↪ᵗ) A toRename-id-eq

initial-⊑ : ∀ {Δ} {μ : ImpEnv Δ} {Σ : TyStore Δ} {A B : Ty Δ}
  → μ ⊢ A ⊑ B
  → A CTI2.⊑ᵂ⟨ initialWorld μ Σ ⟩ B
initial-⊑ {μ = μ} {Σ = Σ} {A = A} {B = B} p =
  subst≡ (λ L → μ ⊢ L ⊑ CTI2.embedᴿ (initialWorld μ Σ) B)
    (sym (initial-embedᴸ {μ = μ} {Σ = Σ} A))
    (subst≡ (λ R → μ ⊢ A ⊑ R)
      (sym (initial-embedᴿ {μ = μ} {Σ = Σ} B)) p)

initialCtx : ∀ {Δ} {μ : ImpEnv Δ} {Σ : TyStore Δ}
  → GTI.CtxImp μ
  → CTI2.CtxImp (initialWorld μ Σ)
initialCtx [] = []
initialCtx {Σ = Σ} (GTI.ctx-imp A B p ∷ γ) =
  CTI2.ctx-imp A B (initial-⊑ {Σ = Σ} p) ∷
    initialCtx {Σ = Σ} γ

initial-∋ : ∀ {Δ} {μ : ImpEnv Δ} {Σ : TyStore Δ}
    {γ : GTI.CtxImp μ} {x A B p}
  → γ GTI.∋ⁱ x ⦂ GTI.ctx-imp A B p
  → initialCtx {Σ = Σ} γ CTI2.∋ʷ x ⦂
      CTI2.ctx-imp A B (initial-⊑ {Σ = Σ} p)
initial-∋ GTI.Zⁱ = CTI2.Zʷ
initial-∋ (GTI.Sⁱ x∈) = CTI2.Sʷ (initial-∋ x∈)

⊢²-retarget : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W} {M : C.Term Δᴸ} {M′ : C.Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p q : A CTI2.⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W ∣ γ ⊢² M ⊑ M′ ∶ q
⊢²-retarget {W = W} {γ = γ} {M = M} {M′ = M′} {p = p} {q = q} d =
  subst≡ (λ r → W ∣ γ ⊢² M ⊑ M′ ∶ r) (PI.⊑-unique p q) d

initial-liftCtx : ∀ {Δ} {μ : ImpEnv Δ} {Σ : TyStore Δ}
    {γ : GTI.CtxImp μ} {γ′ : GTI.CtxImp (extᵐ μ)}
  → GTI.LiftCtxⁱ (extᵐ μ) γ γ′
  → CTI2.LiftCtx X⊑X (initialCtx {Σ = Σ} γ)
      (initialCtx {Σ = store-lift Σ} γ′)
initial-liftCtx GTI.lift-[] = CTI2.lift-[]
initial-liftCtx (GTI.lift-∷ liftγ) =
  CTI2.lift-∷ (initial-liftCtx liftγ)

SourceId : ∀ {Δᴿ Δ} → World Δ Δᴿ Δ → Set
SourceId W = ∀ X → toRenameᵗ (CTI2.ηᴸʷ W) X ≡ X

sourceId-initial : ∀ {Δ} {μ : ImpEnv Δ} {Σ : TyStore Δ}
  → SourceId (initialWorld μ Σ)
sourceId-initial = toRename-id-eq

sourceId-liftBoth : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
  → (v : VarImp)
  → SourceId W
  → SourceId (CTI2.liftWorldBoth v W)
sourceId-liftBoth v sid zero = refl
sourceId-liftBoth v sid (Fin.suc X) =
  cong Fin.suc (sid X)

sourceId-liftLeft : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
  → (v : VarImp)
  → SourceId W
  → SourceId (CTI2.liftWorldLeft v W)
sourceId-liftLeft v sid zero = refl
sourceId-liftLeft v sid (Fin.suc X) =
  cong Fin.suc (sid X)

sourceId-embedᴸ : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
  → SourceId W
  → (A : Ty Δ)
  → CTI2.embedᴸ W A ≡ A
sourceId-embedᴸ {W = W} sid A =
  renameᵗ-pointwise-id (toRenameᵗ (CTI2.ηᴸʷ W)) A sid

sourceId-⊑ : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {A : Ty Δ} {B : Ty Δᴿ}
  → (sid : SourceId W)
  → CTI2.impEnvʷ W ⊢ A ⊑ CTI2.embedᴿ W B
  → A CTI2.⊑ᵂ⟨ W ⟩ B
sourceId-⊑ {W = W} {A = A} {B = B} sid p =
  subst≡ (λ L → CTI2.impEnvʷ W ⊢ L ⊑ CTI2.embedᴿ W B)
    (sym (sourceId-embedᴸ {W = W} sid A)) p

sourceId-⊑-eq : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {A : Ty Δ} {Bᶜ : Ty Δ} {B : Ty Δᴿ}
  → (sid : SourceId W)
  → Bᶜ ≡ CTI2.embedᴿ W B
  → CTI2.impEnvʷ W ⊢ A ⊑ Bᶜ
  → A CTI2.⊑ᵂ⟨ W ⟩ B
sourceId-⊑-eq {W = W} sid refl p = sourceId-⊑ {W = W} sid p

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
  → CTI2.embedᴿ (CTI2.liftWorldBoth v W) (⇑ᵗ B)
      ≡ ⇑ᵗ (CTI2.embedᴿ W B)
embedᴿ-liftBoth-shift {W = W} v B =
  trans (renameᵗ-cong (⇑ᵗ B) (toRename-keep-eq (CTI2.ηᴿʷ W)))
    (renameᵗ-shift (toRenameᵗ (CTI2.ηᴿʷ W)) B)

embedᴿ-liftLeft : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
  → (v : VarImp)
  → (B : Ty Δᴿ)
  → CTI2.embedᴿ (CTI2.liftWorldLeft v W) B
      ≡ ⇑ᵗ (CTI2.embedᴿ W B)
embedᴿ-liftLeft {W = W} v B =
  renameᵗ-skip-eq (CTI2.ηᴿʷ W) B

constTy-embedᴿ : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
  → (κ : Const)
  → CTI2.embedᴿ W (constTy κ) ≡ constTy κ
constTy-embedᴿ {W = W} κ =
  sym (constTy-renameᵗ (toRenameᵗ (CTI2.ηᴿʷ W)) κ)

primArgTy-embedᴿ : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
  → (op : Prim)
  → CTI2.embedᴿ W (primArgTy op) ≡ primArgTy op
primArgTy-embedᴿ addℕ = refl
primArgTy-embedᴿ and𝔹 = refl

primResultTy-embedᴿ : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
  → (op : Prim)
  → CTI2.embedᴿ W (primResultTy op) ≡ primResultTy op
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

data EmbeddedCtx {Δᴿ Δ} (W : World Δ Δᴿ Δ) (sid : SourceId W) :
    GTI.CtxImp (CTI2.impEnvʷ W) → TermCtx Δᴿ →
    CTI2.CtxImp W → Set where

  embedded-[] : EmbeddedCtx W sid [] [] []

  embedded-∷ : ∀ {γ Γ δ A Bᶜ B p q}
    → (eqB : Bᶜ ≡ CTI2.embedᴿ W B)
    → q ≡ sourceId-⊑-eq {W = W} sid eqB p
    → EmbeddedCtx W sid γ Γ δ
      ---------------------------------------------------------------
    → EmbeddedCtx W sid
        (GTI.ctx-imp A Bᶜ p ∷ γ)
        (B ∷ Γ)
        (CTI2.ctx-imp A B q ∷ δ)

embeddedCtx-target : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {sid : SourceId W} {γ Γ δ}
  → EmbeddedCtx W sid γ Γ δ
  → GTI.tgtCtxⁱ γ ≡ T.renameCtx (toRenameᵗ (CTI2.ηᴿʷ W)) Γ
embeddedCtx-target embedded-[] = refl
embeddedCtx-target (embedded-∷ eqB q-ok rel) =
  cong₂ _∷_ eqB (embeddedCtx-target rel)

embeddedCtx-targetʷ : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {sid : SourceId W} {γ Γ δ}
  → EmbeddedCtx W sid γ Γ δ
  → CTI2.tgtCtxʷ δ ≡ Γ
embeddedCtx-targetʷ embedded-[] = refl
embeddedCtx-targetʷ (embedded-∷ eqB q-ok rel) =
  cong (_ ∷_) (embeddedCtx-targetʷ rel)

record EmbeddedLookup {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {sid : SourceId W} {γ Γ δ x A Bᶜ p}
    (rel : EmbeddedCtx W sid γ Γ δ)
    (x∈ : γ GTI.∋ⁱ x ⦂ GTI.ctx-imp A Bᶜ p) : Set where
  constructor embedded-lookup
  field
    B : Ty Δᴿ
    eqB : Bᶜ ≡ CTI2.embedᴿ W B
    q : A CTI2.⊑ᵂ⟨ W ⟩ B
    q-ok : q ≡ sourceId-⊑-eq {W = W} sid eqB p
    Γ∋ : Γ T.∋ x ⦂ B
    δ∋ : δ CTI2.∋ʷ x ⦂ CTI2.ctx-imp A B q

embedded-lookup-at : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {sid : SourceId W} {γ Γ δ x A Bᶜ p}
  → (rel : EmbeddedCtx W sid γ Γ δ)
  → (x∈ : γ GTI.∋ⁱ x ⦂ GTI.ctx-imp A Bᶜ p)
  → EmbeddedLookup rel x∈
embedded-lookup-at (embedded-∷ {B = B} {q = q} eqB q-ok rel) GTI.Zⁱ =
  embedded-lookup B eqB q q-ok T.Z CTI2.Zʷ
embedded-lookup-at (embedded-∷ eqB q-ok rel) (GTI.Sⁱ x∈)
    with embedded-lookup-at rel x∈
embedded-lookup-at (embedded-∷ eqB q-ok rel) (GTI.Sⁱ x∈)
    | embedded-lookup B eqB′ q q-ok′ Γ∋ δ∋ =
  embedded-lookup B eqB′ q q-ok′ (T.S Γ∋) (CTI2.Sʷ δ∋)

record LiftBothPack {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {sid : SourceId W} {γ Γ δ γ′}
    (rel : EmbeddedCtx W sid γ Γ δ)
    (liftγ : GTI.LiftCtxⁱ (extᵐ (CTI2.impEnvʷ W)) γ γ′)
    : Set where
  constructor lift-both-pack
  field
    δ′ : CTI2.CtxImp (CTI2.liftWorldBoth X⊑X W)
    lift² : CTI2.LiftCtx X⊑X δ δ′
    rel′ : EmbeddedCtx (CTI2.liftWorldBoth X⊑X W)
      (sourceId-liftBoth {W = W} X⊑X sid) γ′ (⇑ᶜ Γ) δ′

record LiftLeftPack {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {sid : SourceId W} {γ Γ δ γ′}
    (rel : EmbeddedCtx W sid γ Γ δ)
    (liftγ : GTI.LiftCtxⁱ (instᵐ (CTI2.impEnvʷ W)) γ γ′)
    : Set where
  constructor lift-left-pack
  field
    δ′ : CTI2.CtxImp (CTI2.liftWorldLeft X⊑★ W)
    lift² : CTI2.LiftCtxᴸ X⊑★ δ δ′
    rel′ : EmbeddedCtx (CTI2.liftWorldLeft X⊑★ W)
      (sourceId-liftLeft {W = W} X⊑★ sid) γ′ Γ δ′

embedded-liftBoth : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {sid : SourceId W} {γ Γ δ γ′}
  → (rel : EmbeddedCtx W sid γ Γ δ)
  → (liftγ : GTI.LiftCtxⁱ (extᵐ (CTI2.impEnvʷ W)) γ γ′)
  → LiftBothPack rel liftγ
embedded-liftBoth embedded-[] GTI.lift-[] =
  record { δ′ = [] ; lift² = CTI2.lift-[] ; rel′ = embedded-[] }
embedded-liftBoth {W = W} {sid = sid}
    (embedded-∷ {A = A} {B = B} eqB q-ok rel)
    (GTI.lift-∷ {p′ = p′} liftγ)
    with embedded-liftBoth rel liftγ
embedded-liftBoth {W = W} {sid = sid}
    (embedded-∷ {A = A} {B = B} eqB q-ok rel)
    (GTI.lift-∷ {p′ = p′} liftγ)
    | lift-both-pack δ′ lift² rel′ =
  record
    { δ′ = CTI2.ctx-imp (⇑ᵗ A) (⇑ᵗ B) q′ ∷ δ′
    ; lift² = CTI2.lift-∷ lift²
    ; rel′ = embedded-∷ eqB′ refl rel′
    }
  where
  eqB′ =
    trans (cong ⇑ᵗ eqB)
      (sym (embedᴿ-liftBoth-shift {W = W} X⊑X B))

  q′ =
    sourceId-⊑-eq {W = CTI2.liftWorldBoth X⊑X W}
      (sourceId-liftBoth {W = W} X⊑X sid)
      eqB′ p′

embedded-liftLeft : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {sid : SourceId W} {γ Γ δ γ′}
  → (rel : EmbeddedCtx W sid γ Γ δ)
  → (liftγ : GTI.LiftCtxⁱ (instᵐ (CTI2.impEnvʷ W)) γ γ′)
  → LiftLeftPack rel liftγ
embedded-liftLeft embedded-[] GTI.lift-[] =
  record { δ′ = [] ; lift² = CTI2.liftᴸ-[] ; rel′ = embedded-[] }
embedded-liftLeft {W = W} {sid = sid}
    (embedded-∷ {A = A} {B = B} eqB q-ok rel)
    (GTI.lift-∷ {p′ = p′} liftγ)
    with embedded-liftLeft rel liftγ
embedded-liftLeft {W = W} {sid = sid}
    (embedded-∷ {A = A} {B = B} eqB q-ok rel)
    (GTI.lift-∷ {p′ = p′} liftγ)
    | lift-left-pack δ′ lift² rel′ =
  record
    { δ′ = CTI2.ctx-imp (⇑ᵗ A) B q′ ∷ δ′
    ; lift² = CTI2.liftᴸ-∷ lift²
    ; rel′ = embedded-∷ eqB′ refl rel′
    }
  where
  eqB′ =
    trans (cong ⇑ᵗ eqB)
      (sym (embedᴿ-liftLeft {W = W} X⊑★ B))

  q′ =
    sourceId-⊑-eq {W = CTI2.liftWorldLeft X⊑★ W}
      (sourceId-liftLeft {W = W} X⊑★ sid)
      eqB′ p′

embedded-elab-gradual-typing : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {sid : SourceId W} {γ Γ δ M′ Mᴿ Bᶜ B N}
  → (rel : EmbeddedCtx W sid γ Γ δ)
  → M′ ≡ CPI.Grenameᵐ (CTI2.ηᴿʷ W) Mᴿ
  → Bᶜ ≡ CTI2.embedᴿ W B
  → CPI.Elab (CTI2.targetStoreʷ W) Γ Mᴿ N B
  → Δ G.∣ GTI.tgtCtxⁱ γ ⊢ M′ ⦂ Bᶜ
embedded-elab-gradual-typing {W = W} rel eqM eqB Mᴱ =
  subst≡ (λ T → _ G.∣ _ ⊢ _ ⦂ T) (sym eqB)
    (subst≡ (λ M → _ G.∣ _ ⊢ M ⦂ CTI2.embedᴿ W _)
      (sym eqM)
      (subst≡ (λ Γ → _ G.∣ Γ ⊢ _ ⦂ CTI2.embedᴿ W _)
        (sym (embeddedCtx-target rel))
        (CPI.elab-gradual-typing
          (CPI.rename-elab {Σ′ = CTI2.sourceStoreʷ W}
            (CTI2.ηᴿʷ W) Mᴱ))))

embedded-elab-cast-typing : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    {sid : SourceId W} {γ Γ δ Mᴿ N B}
  → (rel : EmbeddedCtx W sid γ Γ δ)
  → CPI.Elab (CTI2.targetStoreʷ W) Γ Mᴿ N B
  → ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ δ ⟩ ⊢ N ⦂ B
embedded-elab-cast-typing rel Mᴱ =
  subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
    (sym (embeddedCtx-targetʷ rel)) (CPI.elab-cast-typing Mᴱ)

compile-preserves-embedded² : ∀ {Δᴿ Δ} {W : World Δ Δᴿ Δ}
    (sid : SourceId W)
    {γ : GTI.CtxImp (CTI2.impEnvʷ W)} {Γ : TermCtx Δᴿ}
    {δ : CTI2.CtxImp W} {M M′ : GTerm Δ} {Mᴿ : GTerm Δᴿ}
    {A Bᶜ : Ty Δ} {B : Ty Δᴿ} {p} {N : C.Term Δᴿ}
  → (rel : EmbeddedCtx W sid γ Γ δ)
  → (M⊑M′ : CTI2.impEnvʷ W GTI.∣ γ ⊢ᴳ M ⊑ M′
      ⦂ A ⊑ Bᶜ ∶ p)
  → (eqM : M′ ≡ CPI.Grenameᵐ (CTI2.ηᴿʷ W) Mᴿ)
  → (eqB : Bᶜ ≡ CTI2.embedᴿ W B)
  → CPI.Elab (CTI2.targetStoreʷ W) Γ Mᴿ N B
  → W ∣ δ ⊢²
      proj₁ (compile {Σ = CTI2.sourceStoreʷ W}
        (GTI.gradual-term-imprecision-source-typing M⊑M′))
      ⊑ N ∶ sourceId-⊑-eq {W = W} sid eqB p
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
    with compile {Σ = CTI2.sourceStoreʷ W}
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
    with compile {Σ = CTI2.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing L⊑L′)
       | compile-preserves-embedded² sid rel L⊑L′ refl refl L′ᴱ
       | compile {Σ = CTI2.sourceStoreʷ W}
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
        {q = ⇒⊑⇒ (sourceId-⊑-eq {W = W} sid refl pA)
                  (sourceId-⊑-eq {W = W} sid refl pB)}
        L⊑L′²)
      (CTI2.cast⊑cast² (symᶜ A∼C) d′ M⊑M′²
        (sourceId-⊑-eq {W = W} sid refl pA)))
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
    with compile {Σ = CTI2.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing L⊑L′)
       | compile-preserves-embedded² sid rel L⊑L′ refl refl L′ᴱ
       | compile {Σ = CTI2.sourceStoreʷ W}
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
        {q = ⇒⊑⇒ (sourceId-⊑-eq {W = W} sid refl pA)
                  (sourceId-⊑-eq {W = W} sid refl pB)}
        (CTI2.⊑cast² c′ L⊑L′²
          (sourceId-⊑-eq {W = W} sid refl (⇒⊑⇒ pA pB))))
      (CTI2.cast⊑cast² (symᶜ A∼C) d′ M⊑M′²
        (sourceId-⊑-eq {W = W} sid refl pA)))
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
    with compile {Σ = CTI2.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing L⊑L′)
       | compile-preserves-embedded² sid rel L⊑L′ refl refl L′ᴱ
       | compile {Σ = CTI2.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile-preserves-embedded² sid rel M⊑M′ refl refl M′ᴱ
compile-preserves-embedded² {W = W} sid rel
    (GTI.·★⊑·★ᴳ L⊑L′ M⊑M′ C∼★ C′∼★)
    refl refl (CPI.E-·★ L′ᴱ M′ᴱ D′∼★ c′ d′)
    | refl | L , L⊢ | L⊑L′² | M , M⊢ | M⊑M′² =
  ⊢²-retarget
    (CTI2.·⊑·²
      (⊢²-retarget
        {q = ⇒⊑⇒ (sourceId-⊑-eq {W = W} sid refl ★⊑★)
                  (sourceId-⊑-eq {W = W} sid refl ★⊑★)}
        (CTI2.cast⊑cast² CPI.dynamic-function-cast c′ L⊑L′²
          (sourceId-⊑-eq {W = W} sid refl (⇒⊑⇒ ★⊑★ ★⊑★))))
      (CTI2.cast⊑cast² C∼★ d′ M⊑M′²
        (sourceId-⊑-eq {W = W} sid refl ★⊑★)))
compile-preserves-embedded² {W = W} sid rel
    (GTI.Λ⊑Λᴳ {p = p} liftγ vV vV′ zero∈A zero∈B V⊑V′)
    refl eqB (CPI.E-Λ zero∈B′ vV′′ vN′ V′ᴱ)
    rewrite CPI.compile-Λ-term {Σ = CTI2.sourceStoreʷ W}
      {Γ = GTI.srcCtxⁱ _}
      {zero∈A = zero∈A} vV
      (subst≡ (λ Γ → _ G.∣ Γ ⊢ _ ⦂ _) (GTI.srcCtxⁱ-lift liftγ)
        (GTI.gradual-term-imprecision-source-typing V⊑V′))
      | CPI.compile-context-subst
      {Σ = store-lift (CTI2.sourceStoreʷ W)}
      (GTI.srcCtxⁱ-lift liftγ)
      (GTI.gradual-term-imprecision-source-typing V⊑V′)
    with embedded-liftBoth rel liftγ
compile-preserves-embedded² {W = W} sid rel
    (GTI.Λ⊑Λᴳ {p = p} liftγ vV vV′ zero∈A zero∈B V⊑V′)
    refl eqB (CPI.E-Λ zero∈B′ vV′′ vN′ V′ᴱ)
    | lift-both-pack δ′ lift² rel′ =
  ⊢²-retarget
    (CTI2.Λ⊑Λ² lift²
      (compile-value {Σ = store-lift (CTI2.sourceStoreʷ W)} vV
        (GTI.gradual-term-imprecision-source-typing V⊑V′))
      vN′
      (compile-preserves-embedded²
        (sourceId-liftBoth {W = W} X⊑X sid)
        rel′ V⊑V′ refl body-eq V′ᴱ)
      (sourceId-⊑-eq {W = W} sid eqB (∀⊑∀ p)))
  where
  body-eq =
    trans (ty-all-injective eqB)
      (sym (renameᵗ-cong _ (toRename-keep-eq (CTI2.ηᴿʷ W))))
compile-preserves-embedded² {W = W} sid rel
    (GTI.Λ⊑ᴳ {p = p} Anv zero∈A liftγ vV N′⊢ V⊑N′)
    eqM eqB N′ᴱ
    rewrite CPI.compile-Λ-term {Σ = CTI2.sourceStoreʷ W}
      {Γ = GTI.srcCtxⁱ _}
      {zero∈A = zero∈A} vV
      (subst≡ (λ Γ → _ G.∣ Γ ⊢ _ ⦂ _) (GTI.srcCtxⁱ-lift liftγ)
        (GTI.gradual-term-imprecision-source-typing V⊑N′))
      | CPI.compile-context-subst
      {Σ = store-lift (CTI2.sourceStoreʷ W)}
      (GTI.srcCtxⁱ-lift liftγ)
      (GTI.gradual-term-imprecision-source-typing V⊑N′)
    with embedded-liftLeft rel liftγ
compile-preserves-embedded² {W = W} sid rel
    (GTI.Λ⊑ᴳ {p = p} Anv zero∈A liftγ vV N′⊢ V⊑N′)
    eqM eqB N′ᴱ
    | lift-left-pack δ′ lift² rel′ =
  ⊢²-retarget
    (CTI2.Λ⊑² Anv zero∈A lift²
      (compile-value {Σ = store-lift (CTI2.sourceStoreʷ W)} vV
        (GTI.gradual-term-imprecision-source-typing V⊑N′))
      (embedded-elab-cast-typing rel N′ᴱ)
      (compile-preserves-embedded²
        (sourceId-liftLeft {W = W} X⊑★ sid)
        rel′ V⊑N′ term-eq type-eq N′ᴱ)
      (sourceId-⊑-eq {W = W} sid eqB (∀⊑ Anv zero∈A p)))
  where
  term-eq =
    trans (cong G.⇑ᵗᴳ eqM)
      (Grenameᵐ-skip (CTI2.ηᴿʷ W) _)

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
    with compile {Σ = CTI2.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile-preserves-embedded² sid rel M⊑M′ refl body-eq M′ᴱ
compile-preserves-embedded² {W = W} sid rel
    (GTI.[]⊑[]ᴳ {p = p} M⊑M′ q r)
    refl eqB (CPI.E-[] M′ᴱ eq)
    | body-eq | refl | M , M⊢ | M⊑M′² =
  ⊢²-retarget
    (CTI2.•⊑•²
      (sourceId-⊑-eq {W = W} sid body-eq (∀⊑∀ p))
      M⊑M′²
      (sourceId-⊑-eq {W = W} sid refl q)
      (sourceId-⊑-eq {W = W} sid eqB r))
compile-preserves-embedded² {W = W} sid rel
    (GTI.[]⊑ᴳ {p = p} {Anv = Anv} {zero∈A = zero∈A}
      M⊑M′ q r)
    eqM eqB M′ᴱ
    with compile {Σ = CTI2.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile-preserves-embedded² sid rel M⊑M′ eqM eqB M′ᴱ
compile-preserves-embedded² {W = W} sid rel
    (GTI.[]⊑ᴳ {p = p} {Anv = Anv} {zero∈A = zero∈A}
      M⊑M′ q r)
    eqM eqB M′ᴱ
    | M , M⊢ | M⊑M′² =
  ⊢²-retarget
    (CTI2.•⊑²
      (sourceId-⊑-eq {W = W} sid eqB (∀⊑ Anv zero∈A p))
      M⊑M′²
      (sourceId-⊑-eq {W = W} sid refl q)
      (sourceId-⊑-eq {W = W} sid eqB r))
compile-preserves-embedded² {W = W} sid rel
    (GTI.κ⊑κᴳ κ) refl eqB (CPI.E-$ .κ) =
  ⊢²-retarget
    (CTI2.κ⊑κ² κ
      (sourceId-⊑-eq {W = W} {B = constTy κ} sid
        (sym (constTy-embedᴿ {W = W} κ))
        (GTI.constTy-⊑ (CTI2.impEnvʷ W) κ)))
compile-preserves-embedded² {W = W} sid rel
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
compile-preserves-embedded² {W = W} sid rel
    (GTI.⊕⊑⊕ᴳ op L⊑L′ A∼arg A′∼arg M⊑M′
      B∼arg B′∼arg)
    refl eqB
    (CPI.E-⊕ .op L′ᴱ A′∼arg′ c′ M′ᴱ B′∼arg′ d′)
    | refl | refl
    with compile {Σ = CTI2.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing L⊑L′)
       | compile-preserves-embedded² sid rel L⊑L′ refl refl L′ᴱ
       | compile {Σ = CTI2.sourceStoreʷ W}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile-preserves-embedded² sid rel M⊑M′ refl refl M′ᴱ
compile-preserves-embedded² {W = W} sid rel
    (GTI.⊕⊑⊕ᴳ op L⊑L′ A∼arg A′∼arg M⊑M′
      B∼arg B′∼arg)
    refl eqB
    (CPI.E-⊕ .op L′ᴱ A′∼arg′ c′ M′ᴱ B′∼arg′ d′)
    | refl | refl | L , L⊢ | L⊑L′² | M , M⊢ | M⊑M′² =
  ⊢²-retarget
    {q = sourceId-⊑-eq {W = W} sid eqB
      (GTI.primResultTy-⊑ (CTI2.impEnvʷ W) op)}
    (CTI2.⊕⊑⊕² op
      (CTI2.cast⊑cast² A∼arg c′ L⊑L′²
        (sourceId-⊑-eq {W = W} {B = primArgTy op} sid
          (sym (primArgTy-embedᴿ {W = W} op))
          (refl⊑ (primArgTy op))))
      (CTI2.cast⊑cast² B∼arg d′ M⊑M′²
        (sourceId-⊑-eq {W = W} {B = primArgTy op} sid
          (sym (primArgTy-embedᴿ {W = W} op))
          (refl⊑ (primArgTy op))))
      (sourceId-⊑-eq {W = W} {B = primResultTy op} sid
        (sym (primResultTy-embedᴿ {W = W} op))
        (GTI.primResultTy-⊑ (CTI2.impEnvʷ W) op)))

initialEmbeddedCtx : ∀ {Δ} {μ : ImpEnv Δ} {Σ : TyStore Δ}
  → (γ : GTI.CtxImp μ)
  → EmbeddedCtx (initialWorld μ Σ) (sourceId-initial {μ = μ} {Σ = Σ}) γ
      (GTI.tgtCtxⁱ γ) (initialCtx {Σ = Σ} γ)
initialEmbeddedCtx [] = embedded-[]
initialEmbeddedCtx {μ = μ} {Σ = Σ} (GTI.ctx-imp A B p ∷ γ) =
  embedded-∷ (sym (initial-embedᴿ {μ = μ} {Σ = Σ} B))
    (PI.⊑-unique (initial-⊑ {Σ = Σ} p)
      (sourceId-⊑-eq {W = initialWorld μ Σ}
        (sourceId-initial {μ = μ} {Σ = Σ})
        (sym (initial-embedᴿ {μ = μ} {Σ = Σ} B)) p))
    (initialEmbeddedCtx {Σ = Σ} γ)

compile-preserves-elab² : ∀ {Δ} {μ : ImpEnv Δ} {Σ : TyStore Δ}
    {γ : GTI.CtxImp μ} {M M′ : GTerm Δ} {A B p}
    {N : C.Term Δ}
  → (M⊑M′ : μ GTI.∣ γ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p)
  → CPI.Elab Σ (GTI.tgtCtxⁱ γ) M′ N B
  → initialWorld μ Σ ∣ initialCtx {Σ = Σ} γ ⊢²
      proj₁ (compile {Σ = Σ}
        (GTI.gradual-term-imprecision-source-typing M⊑M′))
      ⊑ N ∶ initial-⊑ {Σ = Σ} p
compile-preserves-elab² {μ = μ} {Σ = Σ} {γ = γ} {M′ = M′}
    {B = B}
    M⊑M′ M′ᴱ =
  ⊢²-retarget
    (compile-preserves-embedded² {W = initialWorld μ Σ}
      (sourceId-initial {μ = μ} {Σ = Σ})
      (initialEmbeddedCtx {Σ = Σ} γ) M⊑M′ (sym (Grenameᵐ-id M′))
      (sym (initial-embedᴿ {μ = μ} {Σ = Σ} B)) M′ᴱ)

compile-preserves-imprecision²-statement : Set
compile-preserves-imprecision²-statement =
  ∀ {Δ} {μ : ImpEnv Δ} {Σ : TyStore Δ}
    {γ : GTI.CtxImp μ} {M M′ : GTerm Δ} {A B p}
  → (M⊑M′ : μ GTI.∣ γ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p)
  → initialWorld μ Σ ∣ initialCtx {Σ = Σ} γ ⊢²
      proj₁ (compile {Σ = Σ}
        (GTI.gradual-term-imprecision-source-typing M⊑M′))
      ⊑ proj₁ (compile {Σ = Σ}
        (GTI.gradual-term-imprecision-target-typing M⊑M′))
      ∶ initial-⊑ {Σ = Σ} p

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
  initialWorld idᵐ store-empty
    ∣ initialCtx {Σ = store-empty} [] ⊢²
    proj₁ (compile {Σ = store-empty}
      (GTI.gradual-term-imprecision-source-typing polyId⊑polyIdᴳ))
    ⊑ proj₁ (compile {Σ = store-empty}
      (GTI.gradual-term-imprecision-target-typing polyId⊑polyIdᴳ))
    ∶ initial-⊑ {Σ = store-empty} (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X))
polyId-validation =
  subst≡
    (λ q → initialWorld idᵐ store-empty ∣ [] ⊢² Ex.polyId
      ⊑ Ex.polyId ∶ q)
    (PI.⊑-unique Ex2.example12-∀⊑∀
      (initial-⊑ {Σ = store-empty}
        (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X))))
    Ex2.polyId-refl²

polyId-validation-from-theorem :
  initialWorld idᵐ store-empty
    ∣ initialCtx {Σ = store-empty} [] ⊢²
    proj₁ (compile {Σ = store-empty}
      (GTI.gradual-term-imprecision-source-typing polyId⊑polyIdᴳ))
    ⊑ proj₁ (compile {Σ = store-empty}
      (GTI.gradual-term-imprecision-target-typing polyId⊑polyIdᴳ))
    ∶ initial-⊑ {Σ = store-empty} (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X))
polyId-validation-from-theorem =
  compile-preserves-imprecision² polyId⊑polyIdᴳ
