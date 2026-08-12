module proof.DGG.Elab where

-- File Charter:
--   * Records the elaboration view of the gradual-to-cast compiler.
--   * Provides compiler-shape lemmas, elaboration typing projections, and
--     type-store renaming lemmas used by DGG compile preservation.
--   * Does not depend on either version of the cast-term imprecision relation.

open import Data.Product using (_,_; proj₁)
open import Data.Fin using (zero)
open import Data.List using (_∷_)
import Data.Fin as Fin
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Types
open import TyStore using (TyStore; store-lift)
open import TermCtx using (TermCtx; ⇑ᶜ)
import TermCtx as T
open import Consistency
  using (_⊢_∼_; _∼_; id; _↦_; ？_; symᶜ; renameᶜ;
         _↪ᵗ_; keep; toRenameᵗ; wk↪ᵗ; renameᵐᶜ)
open import Imprecision
open import GradualTerms using (GTerm; _∣_⊢_⦂_)
import GradualTerms as G
open import Primitives
  using (Prim; constTy; primArgTy; primResultTy;
         constTy-renameᵗ; addℕ; and𝔹)
import CastTerms as C
open C using ()
  renaming (`_ to `ᵀ_; ƛ_ to ƛᵀ_; _·_ to _·ᵀ_; Λ_ to Λᵀ_;
            _⦂∀_[_] to _⦂∀ᵀ_[_]; $ to $ᵀ;
            _⊕[_]_ to _⊕ᵀ[_]_; _⟨_⟩ to _⟨ᵀ_⟩)
open import Compile using (compile; compile-value)
open import proof.ImprecisionConsistency
  using (rename-occurs; toRenameᵗ-injective; ty-all-injective)
open import proof.TypeInTermSubst
  using (renameCtx-wk-eq; renameᵗ-wk-eq; renameCtx-keep-shift;
         rename-openᵗ; toRename-keep-eq;
         toRename-wk-eq; renameᵗᵐ-preserves-Value)

dynamic-function-cast : ∀ {Δ} → _∼_ {Δ} ★ (★ ⇒ ★)
dynamic-function-cast = ？ (id ★ ↦ id ★)

lookup-uniqueᴳ : ∀ {Δ} {Γ : TermCtx Δ} {x A B}
  → Γ T.∋ x ⦂ A
  → Γ T.∋ x ⦂ B
  → A ≡ B
lookup-uniqueᴳ T.Z T.Z = refl
lookup-uniqueᴳ (T.S x∈) (T.S x∈′) =
  lookup-uniqueᴳ x∈ x∈′

typing-uniqueᴳ : ∀ {Δ} {Γ : TermCtx Δ} {M A B}
  → Δ ∣ Γ ⊢ M ⦂ A
  → Δ ∣ Γ ⊢ M ⦂ B
  → A ≡ B
typing-uniqueᴳ (G.⊢` x∈) (G.⊢` x∈′) =
  lookup-uniqueᴳ x∈ x∈′
typing-uniqueᴳ (G.⊢ƛ M⊢) (G.⊢ƛ M⊢′) =
  cong (_ ⇒_) (typing-uniqueᴳ M⊢ M⊢′)
typing-uniqueᴳ (G.⊢· L⊢ M⊢ A∼C)
    (G.⊢· L⊢′ M⊢′ B∼D)
    with typing-uniqueᴳ L⊢ L⊢′
typing-uniqueᴳ (G.⊢· L⊢ M⊢ A∼C)
    (G.⊢· L⊢′ M⊢′ B∼D)
    | refl =
  refl
typing-uniqueᴳ (G.⊢· L⊢ M⊢ A∼C)
    (G.⊢·★ L⊢′ M⊢′ B∼★)
    with typing-uniqueᴳ L⊢ L⊢′
typing-uniqueᴳ (G.⊢· L⊢ M⊢ A∼C)
    (G.⊢·★ L⊢′ M⊢′ B∼★)
    | ()
typing-uniqueᴳ (G.⊢·★ L⊢ M⊢ A∼★)
    (G.⊢· L⊢′ M⊢′ B∼D)
    with typing-uniqueᴳ L⊢ L⊢′
typing-uniqueᴳ (G.⊢·★ L⊢ M⊢ A∼★)
    (G.⊢· L⊢′ M⊢′ B∼D)
    | ()
typing-uniqueᴳ (G.⊢·★ L⊢ M⊢ A∼★)
    (G.⊢·★ L⊢′ M⊢′ B∼★) =
  refl
typing-uniqueᴳ (G.⊢Λ vM M⊢) (G.⊢Λ vM′ M⊢′) =
  cong `∀ (typing-uniqueᴳ M⊢ M⊢′)
typing-uniqueᴳ (G.⊢• {A = A} M⊢) (G.⊢• M⊢′) =
  cong (λ B → B [ A ]ᵗ)
    (ty-all-injective (typing-uniqueᴳ M⊢ M⊢′))
typing-uniqueᴳ (G.⊢$ κ) (G.⊢$ κ′) = refl
typing-uniqueᴳ (G.⊢⊕ op L⊢ A∼arg M⊢ B∼arg)
    (G.⊢⊕ op′ L⊢′ A′∼arg M⊢′ B′∼arg) =
  refl

compile-context-subst : ∀ {Δ} {Σ : TyStore Δ}
    {Γ Γ′ : TermCtx Δ} {M : GTerm Δ} {A : Ty Δ}
  → (Γ≡Γ′ : Γ ≡ Γ′)
  → (M⊢ : Δ ∣ Γ ⊢ M ⦂ A)
  → proj₁ (compile {Σ = Σ}
      (subst (λ Γ₀ → Δ ∣ Γ₀ ⊢ M ⦂ A) Γ≡Γ′ M⊢))
    ≡ proj₁ (compile {Σ = Σ} M⊢)
compile-context-subst refl M⊢ = refl

compile-Λ-term : ∀ {Δ} {Σ : TyStore Δ} {Γ : TermCtx Δ}
    {M : GTerm (Nat.suc Δ)} {A : Ty (Nat.suc Δ)}
    {zero∈A : zero ∈ᵗ A}
  → (vM : G.Value M)
  → (M⊢ : Nat.suc Δ ∣ ⇑ᶜ Γ ⊢ M ⦂ A)
  → proj₁ (compile {Σ = Σ} (G.⊢Λ {zero∈A = zero∈A} vM M⊢))
    ≡ Λᵀ (proj₁ (compile {Σ = store-lift Σ} M⊢))
compile-Λ-term {Σ = Σ} vM M⊢
    with compile {Σ = store-lift Σ} M⊢
       | compile-value {Σ = store-lift Σ} vM M⊢
compile-Λ-term {Σ = Σ} vM M⊢ | N , N⊢ | vN = refl

-- Embedding-directed renaming follows cast-term renaming under binders.
Grenameᵐ : ∀ {Δ Δ′} → Δ ↪ᵗ Δ′ → GTerm Δ → GTerm Δ′
Grenameᵐ η (G.` x) = G.` x
Grenameᵐ η (G.ƛ A ⇒ M) =
  G.ƛ renameᵗ (toRenameᵗ η) A ⇒ Grenameᵐ η M
Grenameᵐ η (L G.·[ ℓ ] M) =
  Grenameᵐ η L G.·[ ℓ ] Grenameᵐ η M
Grenameᵐ η (G.Λ M) = G.Λ (Grenameᵐ (keep η) M)
Grenameᵐ η (M G.`[ A ]) =
  Grenameᵐ η M G.`[ renameᵗ (toRenameᵗ η) A ]
Grenameᵐ η (G.$ κ) = G.$ κ
Grenameᵐ η (L G.⊕[ op at ℓ ] M) =
  Grenameᵐ η L G.⊕[ op at ℓ ] Grenameᵐ η M

rename-valueᵐᴳ : ∀ {Δ Δ′} (η : Δ ↪ᵗ Δ′) {V}
  → G.Value V
  → G.Value (Grenameᵐ η V)
rename-valueᵐᴳ η (G.ƛ A ⇒ N) =
  G.ƛ renameᵗ (toRenameᵗ η) A ⇒ Grenameᵐ η N
rename-valueᵐᴳ η (G.$ κ) = G.$ κ
rename-valueᵐᴳ η (G.Λ N) =
  G.Λ (Grenameᵐ (keep η) N)

-- Compilation shape, abstracting over the chosen consistency evidence.
data Elab {Δ : TyCtx} (Σ : TyStore Δ) (Γ : TermCtx Δ) :
    GTerm Δ → C.Term Δ → Ty Δ → Set where
  E-` : ∀ {x A}
    → Γ T.∋ x ⦂ A
    → Elab Σ Γ (G.` x) (`ᵀ x) A

  E-ƛ : ∀ {M N A B}
    → Elab Σ (A ∷ Γ) M N B
    → Elab Σ Γ (G.ƛ A ⇒ M) (ƛᵀ N) (A ⇒ B)

  E-· : ∀ {L Lᶜ M Mᶜ A B D ν ℓ}
    → Elab Σ Γ L Lᶜ (A ⇒ B)
    → Elab Σ Γ M Mᶜ D
    → A ∼ D
    → (c : _⊢_∼_ {Δ = Δ} ν D A)
    → Elab Σ Γ (L G.·[ ℓ ] M)
        (Lᶜ ·ᵀ (Mᶜ ⟨ᵀ c ⟩)) B

  E-·★ : ∀ {L Lᶜ M Mᶜ A ν ν′ ℓ}
    → Elab Σ Γ L Lᶜ ★
    → Elab Σ Γ M Mᶜ A
    → A ∼ ★
    → (c : _⊢_∼_ {Δ = Δ} ν ★ (★ ⇒ ★))
    → (d : _⊢_∼_ {Δ = Δ} ν′ A ★)
    → Elab Σ Γ (L G.·[ ℓ ] M)
        ((Lᶜ ⟨ᵀ c ⟩) ·ᵀ (Mᶜ ⟨ᵀ d ⟩)) ★

  E-Λ : ∀ {M N A}
    → (zero∈A : zero ∈ᵗ A)
    → G.Value M
    → C.Value N
    → Elab (store-lift Σ) (⇑ᶜ Γ) M N A
    → Elab Σ Γ (G.Λ M) (Λᵀ N) (`∀ A)

  E-[] : ∀ {M N B A C}
    → Elab Σ Γ M N (`∀ B)
    → B [ A ]ᵗ ≡ C
    → Elab Σ Γ (M G.`[ A ])
        (N ⦂∀ᵀ B [ A ]) C

  E-$ : ∀ κ
    → Elab Σ Γ (G.$ κ) ($ᵀ κ) (constTy κ)

  E-⊕ : ∀ {L Lᶜ M Mᶜ A B ν ν′ ℓ}
    → (op : Prim)
    → Elab Σ Γ L Lᶜ A
    → A ∼ primArgTy op
    → (c : _⊢_∼_ {Δ = Δ} ν A (primArgTy op))
    → Elab Σ Γ M Mᶜ B
    → B ∼ primArgTy op
    → (d : _⊢_∼_ {Δ = Δ} ν′ B (primArgTy op))
    → Elab Σ Γ (L G.⊕[ op at ℓ ] M)
        ((Lᶜ ⟨ᵀ c ⟩) ⊕ᵀ[ op ] (Mᶜ ⟨ᵀ d ⟩))
        (primResultTy op)

elab-gradual-typing : ∀ {Δ} {Σ : TyStore Δ} {Γ : TermCtx Δ}
    {M : GTerm Δ} {N : C.Term Δ} {A : Ty Δ}
  → Elab Σ Γ M N A
  → Δ ∣ Γ ⊢ M ⦂ A
elab-gradual-typing (E-` x∈) = G.⊢` x∈
elab-gradual-typing (E-ƛ Mᴱ) =
  G.⊢ƛ (elab-gradual-typing Mᴱ)
elab-gradual-typing (E-· Lᴱ Mᴱ A∼D c) =
  G.⊢· (elab-gradual-typing Lᴱ)
    (elab-gradual-typing Mᴱ) A∼D
elab-gradual-typing (E-·★ Lᴱ Mᴱ A∼★ c d) =
  G.⊢·★ (elab-gradual-typing Lᴱ)
    (elab-gradual-typing Mᴱ) A∼★
elab-gradual-typing (E-Λ zero∈A vM vN Mᴱ) =
  G.⊢Λ {zero∈A = zero∈A} vM (elab-gradual-typing Mᴱ)
elab-gradual-typing (E-[] Mᴱ eq) =
  subst (λ T → _ ∣ _ ⊢ _ ⦂ T) eq
    (G.⊢• (elab-gradual-typing Mᴱ))
elab-gradual-typing (E-$ κ) = G.⊢$ κ
elab-gradual-typing (E-⊕ op Lᴱ A∼arg c Mᴱ B∼arg d) =
  G.⊢⊕ op (elab-gradual-typing Lᴱ) A∼arg
    (elab-gradual-typing Mᴱ) B∼arg

elab-cast-typing : ∀ {Δ} {Σ : TyStore Δ} {Γ : TermCtx Δ}
    {M : GTerm Δ} {N : C.Term Δ} {A : Ty Δ}
  → Elab Σ Γ M N A
  → C.⟨ Δ , Σ , Γ ⟩ C.⊢ N ⦂ A
elab-cast-typing (E-` x∈) = C.⊢` x∈
elab-cast-typing (E-ƛ Mᴱ) =
  C.⊢ƛ (elab-cast-typing Mᴱ)
elab-cast-typing (E-· Lᴱ Mᴱ A∼D c) =
  C.⊢· (elab-cast-typing Lᴱ)
    (C.⊢⟨⟩ (elab-cast-typing Mᴱ) c)
elab-cast-typing (E-·★ Lᴱ Mᴱ A∼★ c d) =
  C.⊢· (C.⊢⟨⟩ (elab-cast-typing Lᴱ) c)
    (C.⊢⟨⟩ (elab-cast-typing Mᴱ) d)
elab-cast-typing (E-Λ zero∈A vM vN Mᴱ) =
  C.⊢Λ vN (elab-cast-typing Mᴱ)
elab-cast-typing (E-[] Mᴱ eq) =
  subst (λ T → C.⟨ _ , _ , _ ⟩ C.⊢ _ ⦂ T) eq
    (C.⊢• (elab-cast-typing Mᴱ))
elab-cast-typing (E-$ κ) = C.⊢$ κ
elab-cast-typing (E-⊕ op Lᴱ A∼arg c Mᴱ B∼arg d) =
  C.⊢⊕ op (C.⊢⟨⟩ (elab-cast-typing Lᴱ) c)
    (C.⊢⟨⟩ (elab-cast-typing Mᴱ) d)

compile-elab : ∀ {Δ} {Σ : TyStore Δ} {Γ : TermCtx Δ}
    {M : GTerm Δ} {A : Ty Δ}
  → (M⊢ : Δ ∣ Γ ⊢ M ⦂ A)
  → Elab Σ Γ M (proj₁ (compile {Σ = Σ} M⊢)) A
compile-elab (G.⊢` x∈) = E-` x∈
compile-elab {Σ = Σ} (G.⊢ƛ M⊢)
    with compile {Σ = Σ} M⊢ | compile-elab {Σ = Σ} M⊢
compile-elab {Σ = Σ} (G.⊢ƛ M⊢)
    | N , N⊢ | Nᴱ =
  E-ƛ Nᴱ
compile-elab {Σ = Σ} (G.⊢· L⊢ M⊢ A∼D)
    with compile {Σ = Σ} L⊢ | compile-elab {Σ = Σ} L⊢
       | compile {Σ = Σ} M⊢ | compile-elab {Σ = Σ} M⊢
compile-elab {Σ = Σ} (G.⊢· L⊢ M⊢ A∼D)
    | Lᶜ , Lᶜ⊢ | Lᴱ | Mᶜ , Mᶜ⊢ | Mᴱ =
  E-· Lᴱ Mᴱ A∼D (symᶜ A∼D)
compile-elab {Σ = Σ} (G.⊢·★ L⊢ M⊢ A∼★)
    with compile {Σ = Σ} L⊢ | compile-elab {Σ = Σ} L⊢
       | compile {Σ = Σ} M⊢ | compile-elab {Σ = Σ} M⊢
compile-elab {Σ = Σ} (G.⊢·★ L⊢ M⊢ A∼★)
    | Lᶜ , Lᶜ⊢ | Lᴱ | Mᶜ , Mᶜ⊢ | Mᴱ =
  E-·★ Lᴱ Mᴱ A∼★ dynamic-function-cast A∼★
compile-elab {Σ = Σ} (G.⊢Λ {zero∈A = zero∈A} vM M⊢)
    with compile {Σ = store-lift Σ} M⊢
       | compile-value {Σ = store-lift Σ} vM M⊢
       | compile-elab {Σ = store-lift Σ} M⊢
compile-elab {Σ = Σ} (G.⊢Λ {zero∈A = zero∈A} vM M⊢)
    | N , N⊢ | vN | Nᴱ =
  E-Λ zero∈A vM vN Nᴱ
compile-elab {Σ = Σ} (G.⊢• M⊢)
    with compile {Σ = Σ} M⊢ | compile-elab {Σ = Σ} M⊢
compile-elab {Σ = Σ} (G.⊢• M⊢) | N , N⊢ | Nᴱ =
  E-[] Nᴱ refl
compile-elab (G.⊢$ κ) = E-$ κ
compile-elab {Σ = Σ} (G.⊢⊕ op L⊢ A∼arg M⊢ B∼arg)
    with compile {Σ = Σ} L⊢ | compile-elab {Σ = Σ} L⊢
       | compile {Σ = Σ} M⊢ | compile-elab {Σ = Σ} M⊢
compile-elab {Σ = Σ} (G.⊢⊕ op L⊢ A∼arg M⊢ B∼arg)
    | Lᶜ , Lᶜ⊢ | Lᴱ | Mᶜ , Mᶜ⊢ | Mᴱ =
  E-⊕ op Lᴱ A∼arg A∼arg Mᴱ B∼arg B∼arg

renameᵗᴳ-cong : ∀ {Δ Δ′} {ρ σ : Δ ⇒ʳ Δ′}
  → (M : GTerm Δ)
  → (∀ X → ρ X ≡ σ X)
  → G.renameᵗᴳ ρ M ≡ G.renameᵗᴳ σ M
renameᵗᴳ-cong (G.` x) eq = refl
renameᵗᴳ-cong (G.ƛ A ⇒ M) eq =
  cong₂ G.ƛ_⇒_ (renameᵗ-cong A eq) (renameᵗᴳ-cong M eq)
renameᵗᴳ-cong (L G.·[ ℓ ] M) eq =
  cong₂ (λ L′ M′ → L′ G.·[ ℓ ] M′)
    (renameᵗᴳ-cong L eq) (renameᵗᴳ-cong M eq)
renameᵗᴳ-cong (G.Λ M) eq =
  cong G.Λ_ (renameᵗᴳ-cong M ext-eq)
  where
  ext-eq : ∀ X → extᵗ _ X ≡ extᵗ _ X
  ext-eq Fin.zero = refl
  ext-eq (Fin.suc X) = cong Fin.suc (eq X)
renameᵗᴳ-cong (M G.`[ A ]) eq =
  cong₂ G._`[_] (renameᵗᴳ-cong M eq) (renameᵗ-cong A eq)
renameᵗᴳ-cong (G.$ κ) eq = refl
renameᵗᴳ-cong (L G.⊕[ op at ℓ ] M) eq =
  cong₂ (λ L′ M′ → L′ G.⊕[ op at ℓ ] M′)
    (renameᵗᴳ-cong L eq) (renameᵗᴳ-cong M eq)

Grenameᵐ-to-rename : ∀ {Δ Δ′} (η : Δ ↪ᵗ Δ′) (M : GTerm Δ)
  → Grenameᵐ η M ≡ G.renameᵗᴳ (toRenameᵗ η) M
Grenameᵐ-to-rename η (G.` x) = refl
Grenameᵐ-to-rename η (G.ƛ A ⇒ M) =
  cong (G.ƛ renameᵗ (toRenameᵗ η) A ⇒_)
    (Grenameᵐ-to-rename η M)
Grenameᵐ-to-rename η (L G.·[ ℓ ] M) =
  cong₂ (λ L′ M′ → L′ G.·[ ℓ ] M′)
    (Grenameᵐ-to-rename η L) (Grenameᵐ-to-rename η M)
Grenameᵐ-to-rename η (G.Λ M) =
  cong G.Λ_
    (trans (Grenameᵐ-to-rename (keep η) M)
      (renameᵗᴳ-cong M (toRename-keep-eq η)))
Grenameᵐ-to-rename η (M G.`[ A ]) =
  cong (λ M′ → M′ G.`[ renameᵗ (toRenameᵗ η) A ])
    (Grenameᵐ-to-rename η M)
Grenameᵐ-to-rename η (G.$ κ) = refl
Grenameᵐ-to-rename η (L G.⊕[ op at ℓ ] M) =
  cong₂ (λ L′ M′ → L′ G.⊕[ op at ℓ ] M′)
    (Grenameᵐ-to-rename η L) (Grenameᵐ-to-rename η M)

rename-elab : ∀ {Δ Δ′} {Σ : TyStore Δ} {Σ′ : TyStore Δ′}
    {Γ : TermCtx Δ} {M : GTerm Δ} {N : C.Term Δ} {A : Ty Δ}
    (η : Δ ↪ᵗ Δ′)
  → Elab Σ Γ M N A
  → Elab Σ′ (T.renameCtx (toRenameᵗ η) Γ)
      (Grenameᵐ η M) (C.renameᵗᵐ η N)
      (renameᵗ (toRenameᵗ η) A)
rename-elab η (E-` x∈) =
  E-` (T.renameᵗ-∋ (toRenameᵗ η) x∈)
rename-elab η (E-ƛ Mᴱ) =
  E-ƛ (rename-elab η Mᴱ)
rename-elab η (E-· Lᴱ Mᴱ A∼D c) =
  E-· (rename-elab η Lᴱ) (rename-elab η Mᴱ)
    (renameᶜ (toRenameᵗ η) A∼D) (renameᵐᶜ η c)
rename-elab η (E-·★ Lᴱ Mᴱ A∼★ c d) =
  E-·★ (rename-elab η Lᴱ) (rename-elab η Mᴱ)
    (renameᶜ (toRenameᵗ η) A∼★)
    (renameᵐᶜ η c) (renameᵐᶜ η d)
rename-elab {Σ′ = Σ′} {Γ = Γ} η
    (E-Λ {M = M} {N = N} {A = A} zero∈A vM vN Mᴱ) =
  subst
    (λ T′ → Elab Σ′ (T.renameCtx (toRenameᵗ η) Γ)
      (G.Λ (Grenameᵐ (keep η) M))
      (Λᵀ (C.renameᵗᵐ (keep η) N)) T′)
    (cong `∀ (renameᵗ-cong A (toRename-keep-eq η)))
    (E-Λ
      (rename-occurs (toRenameᵗ (keep η))
        (toRenameᵗ-injective (keep η)) zero∈A)
      (rename-valueᵐᴳ (keep η) vM)
      (renameᵗᵐ-preserves-Value (keep η) vN)
      (subst
        (λ Γ′ → Elab (store-lift Σ′) Γ′
          (Grenameᵐ (keep η) M)
          (C.renameᵗᵐ (keep η) N)
          (renameᵗ (toRenameᵗ (keep η)) A))
        (renameCtx-keep-shift η Γ)
        (rename-elab (keep η) Mᴱ)))
rename-elab {Σ′ = Σ′} {Γ = Γ} η
    (E-[] {M = M} {N = N} {B = B} {A = A} Mᴱ eq) =
  subst
    (λ T′ → Elab Σ′ (T.renameCtx (toRenameᵗ η) Γ)
      (Grenameᵐ η M G.`[ renameᵗ (toRenameᵗ η) A ])
      (C.renameᵗᵐ η N
        ⦂∀ᵀ renameᵗ (toRenameᵗ (keep η)) B
        [ renameᵗ (toRenameᵗ η) A ])
      T′)
    (trans result-eq (cong (renameᵗ (toRenameᵗ η)) eq))
    (E-[] (subst
      (λ T′ → Elab Σ′ (T.renameCtx (toRenameᵗ η) Γ)
        (Grenameᵐ η M) (C.renameᵗᵐ η N) (`∀ T′))
      (sym body-eq) (rename-elab η Mᴱ)) refl)
  where
  body-eq =
    renameᵗ-cong B (toRename-keep-eq η)

  result-eq =
    trans (cong (λ T′ →
        T′ [ renameᵗ (toRenameᵗ η) A ]ᵗ) body-eq)
      (sym (rename-openᵗ (toRenameᵗ η) B A))
rename-elab {Σ′ = Σ′} {Γ = Γ} η (E-$ κ) =
  subst
    (λ T′ → Elab Σ′ (T.renameCtx (toRenameᵗ η) Γ)
      (G.$ κ) ($ᵀ κ) T′)
    (constTy-renameᵗ (toRenameᵗ η) κ) (E-$ κ)
rename-elab η
    (E-⊕ addℕ Lᴱ A∼arg c Mᴱ B∼arg d) =
  E-⊕ addℕ (rename-elab η Lᴱ)
    (renameᶜ (toRenameᵗ η) A∼arg) (renameᵐᶜ η c)
    (rename-elab η Mᴱ)
    (renameᶜ (toRenameᵗ η) B∼arg) (renameᵐᶜ η d)
rename-elab η
    (E-⊕ and𝔹 Lᴱ A∼arg c Mᴱ B∼arg d) =
  E-⊕ and𝔹 (rename-elab η Lᴱ)
    (renameᶜ (toRenameᵗ η) A∼arg) (renameᵐᶜ η c)
    (rename-elab η Mᴱ)
    (renameᶜ (toRenameᵗ η) B∼arg) (renameᵐᶜ η d)

shift-elab : ∀ {Δ} {Σ : TyStore Δ} {Γ : TermCtx Δ}
    {M : GTerm Δ} {N : C.Term Δ} {A : Ty Δ}
  → Elab Σ Γ M N A
  → Elab (store-lift Σ) (⇑ᶜ Γ)
      (G.⇑ᵗᴳ M) (C.⇑ᵗᵐ N) (⇑ᵗ A)
shift-elab {Σ = Σ} {Γ = Γ} {M = M} {N = N} {A = A} Mᴱ =
  subst
    (λ T′ → Elab (store-lift Σ) (⇑ᶜ Γ)
      (G.⇑ᵗᴳ M) (C.⇑ᵗᵐ N) T′)
    (renameᵗ-wk-eq A)
    (subst
      (λ M′ → Elab (store-lift Σ) (⇑ᶜ Γ)
        M′ (C.⇑ᵗᵐ N) (renameᵗ (toRenameᵗ wk↪ᵗ) A))
      term-eq
      (subst
        (λ Γ′ → Elab (store-lift Σ) Γ′
          (Grenameᵐ wk↪ᵗ M) (C.⇑ᵗᵐ N)
          (renameᵗ (toRenameᵗ wk↪ᵗ) A))
        (renameCtx-wk-eq Γ)
        (rename-elab {Σ′ = store-lift Σ} wk↪ᵗ Mᴱ)))
  where
  term-eq =
    trans (Grenameᵐ-to-rename wk↪ᵗ M)
      (renameᵗᴳ-cong M toRename-wk-eq)
