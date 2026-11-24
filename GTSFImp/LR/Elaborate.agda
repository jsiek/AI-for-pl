module LR.Elaborate where

-- File Charter:
--   * Elaboration of the gradual source language into the cast calculus
--     with casts in eager normal form (notes/denotational-dgg.md,
--     Section 7a).
--   * `compileᴱ` is `Compile.compile` with `eager` applied to every
--     inserted cast.  `Compile.compile` itself is unchanged: its
--     application casts are `symᶜ` of the typing evidence, and `symᶜ`
--     turns `lower?`'s eager `inst (gen …)` into `gen (inst …)`.
--   * `ElabE` is the elaboration relation: `proof.DGG.Elab.Elab` with
--     every inserted cast in normal form, and without the type store
--     index, which never affects the produced term.  It abstracts over
--     the consistency evidence, so related source terms can be
--     elaborated from different typing derivations.
--   * `compileᴱ` produces an `ElabE`, and an `ElabE` is an `Elab`.

open import Data.List using (_∷_)
open import Data.Fin using (zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (TyStore; store-lift)
open import TermCtx using (TermCtx; ⇑ᶜ)
import TermCtx as T
open import Consistency
  using (_⊢_∼_; _∼_; Env∼; id; _↦_; ？_; symᶜ)
open import GradualTerms using (GTerm; _∣_⊢_⦂_)
import GradualTerms as G
open import Primitives using (Prim; constTy; primArgTy; primResultTy)
import CastTerms as C
open C using ()
  renaming (`_ to `ᵀ_; ƛ_ to ƛᵀ_; _·_ to _·ᵀ_; Λ_ to Λᵀ_;
            _⦂∀_[_] to _⦂∀ᵀ_[_]; $ to $ᵀ;
            _⊕[_]_ to _⊕ᵀ[_]_; _⟨_⟩ to _⟨ᵀ_⟩)
open import proof.DGG.Elab
  using (Elab; E-`; E-ƛ; E-·; E-·★; E-Λ; E-[]; E-$; E-⊕;
         dynamic-function-cast)
open import LR.EagerCast
open import proof.LR.EagerCast using () renaming (eager-eager to eager-normal)

------------------------------------------------------------------------
-- The relation
------------------------------------------------------------------------

data ElabE {Δ : TyCtx} (Γ : TermCtx Δ) :
    GTerm Δ → C.Term Δ → Ty Δ → Set where
  Eᴱ-` : ∀ {x A}
    → Γ T.∋ x ⦂ A
    → ElabE Γ (G.` x) (`ᵀ x) A

  Eᴱ-ƛ : ∀ {M N A B}
    → ElabE (A ∷ Γ) M N B
    → ElabE Γ (G.ƛ A ⇒ M) (ƛᵀ N) (A ⇒ B)

  Eᴱ-· : ∀ {L Lᶜ M Mᶜ A B D ℓ} {ν : Env∼ Δ}
    → ElabE Γ L Lᶜ (A ⇒ B)
    → ElabE Γ M Mᶜ D
    → A ∼ D
    → (c : ν ⊢ D ∼ A)
    → Eager c
    → ElabE Γ (L G.·[ ℓ ] M) (Lᶜ ·ᵀ (Mᶜ ⟨ᵀ c ⟩)) B

  Eᴱ-·★ : ∀ {L Lᶜ M Mᶜ A ℓ} {ν ν′ : Env∼ Δ}
    → ElabE Γ L Lᶜ ★
    → ElabE Γ M Mᶜ A
    → A ∼ ★
    → (c : ν ⊢ ★ ∼ (★ ⇒ ★))
    → Eager c
    → (d : ν′ ⊢ A ∼ ★)
    → Eager d
    → ElabE Γ (L G.·[ ℓ ] M) ((Lᶜ ⟨ᵀ c ⟩) ·ᵀ (Mᶜ ⟨ᵀ d ⟩)) ★

  Eᴱ-Λ : ∀ {M N A}
    → (zero∈A : zero ∈ᵗ A)
    → G.Value M
    → C.Value N
    → ElabE (⇑ᶜ Γ) M N A
    → ElabE Γ (G.Λ M) (Λᵀ N) (`∀ A)

  Eᴱ-[] : ∀ {M N B A C}
    → ElabE Γ M N (`∀ B)
    → B [ A ]ᵗ ≡ C
    → ElabE Γ (M G.`[ A ]) (N ⦂∀ᵀ B [ A ]) C

  Eᴱ-$ : ∀ κ
    → ElabE Γ (G.$ κ) ($ᵀ κ) (constTy κ)

  Eᴱ-⊕ : ∀ {L Lᶜ M Mᶜ A B ℓ} {ν ν′ : Env∼ Δ}
    → (op : Prim)
    → ElabE Γ L Lᶜ A
    → A ∼ primArgTy op
    → (c : ν ⊢ A ∼ primArgTy op)
    → Eager c
    → ElabE Γ M Mᶜ B
    → B ∼ primArgTy op
    → (d : ν′ ⊢ B ∼ primArgTy op)
    → Eager d
    → ElabE Γ (L G.⊕[ op at ℓ ] M)
        ((Lᶜ ⟨ᵀ c ⟩) ⊕ᵀ[ op ] (Mᶜ ⟨ᵀ d ⟩)) (primResultTy op)

toElab : ∀ {Δ} {Σ : TyStore Δ} {Γ : TermCtx Δ} {M N A}
  → ElabE Γ M N A → Elab Σ Γ M N A
toElab (Eᴱ-` x∈) = E-` x∈
toElab (Eᴱ-ƛ Mᴱ) = E-ƛ (toElab Mᴱ)
toElab (Eᴱ-· Lᴱ Mᴱ A∼D c Ec) = E-· (toElab Lᴱ) (toElab Mᴱ) A∼D c
toElab (Eᴱ-·★ Lᴱ Mᴱ A∼★ c Ec d Ed) =
  E-·★ (toElab Lᴱ) (toElab Mᴱ) A∼★ c d
toElab {Σ = Σ} (Eᴱ-Λ z vM vN Mᴱ) =
  E-Λ z vM vN (toElab {Σ = store-lift Σ} Mᴱ)
toElab (Eᴱ-[] Mᴱ eq) = E-[] (toElab Mᴱ) eq
toElab (Eᴱ-$ κ) = E-$ κ
toElab (Eᴱ-⊕ op Lᴱ A∼ c Ec Mᴱ B∼ d Ed) =
  E-⊕ op (toElab Lᴱ) A∼ c (toElab Mᴱ) B∼ d

------------------------------------------------------------------------
-- The compiler
------------------------------------------------------------------------

dynamic-function-cast-eager : ∀ {Δ} → Eager (dynamic-function-cast {Δ})
dynamic-function-cast-eager = e-？ (e-↦ e-id e-id)

compileᴱ : ∀ {Δ} {Γ : TermCtx Δ} {M : GTerm Δ} {A : Ty Δ}
  → Δ ∣ Γ ⊢ M ⦂ A → C.Term Δ
compileᴱ (G.⊢` {x = x} x∈) = `ᵀ x
compileᴱ (G.⊢ƛ M⊢) = ƛᵀ compileᴱ M⊢
compileᴱ (G.⊢· L⊢ M⊢ A∼D) =
  compileᴱ L⊢ ·ᵀ (compileᴱ M⊢ ⟨ᵀ eager (symᶜ A∼D) ⟩)
compileᴱ (G.⊢·★ L⊢ M⊢ A∼★) =
  (compileᴱ L⊢ ⟨ᵀ dynamic-function-cast ⟩)
    ·ᵀ (compileᴱ M⊢ ⟨ᵀ eager A∼★ ⟩)
compileᴱ (G.⊢Λ vM M⊢) = Λᵀ compileᴱ M⊢
compileᴱ (G.⊢• {B = B} {A = A} M⊢) = compileᴱ M⊢ ⦂∀ᵀ B [ A ]
compileᴱ (G.⊢$ κ) = $ᵀ κ
compileᴱ (G.⊢⊕ op L⊢ A∼arg M⊢ B∼arg) =
  (compileᴱ L⊢ ⟨ᵀ eager A∼arg ⟩) ⊕ᵀ[ op ] (compileᴱ M⊢ ⟨ᵀ eager B∼arg ⟩)

compileᴱ-value : ∀ {Δ} {Γ : TermCtx Δ} {M : GTerm Δ} {A : Ty Δ}
  → G.Value M → (M⊢ : Δ ∣ Γ ⊢ M ⦂ A) → C.Value (compileᴱ M⊢)
compileᴱ-value (G.ƛ A ⇒ N) (G.⊢ƛ M⊢) = C.ƛ compileᴱ M⊢
compileᴱ-value (G.$ κ) (G.⊢$ .κ) = C.$ κ
compileᴱ-value (G.Λ N) (G.⊢Λ vN M⊢) = C.Λ (compileᴱ-value vN M⊢)

compileᴱ-elab : ∀ {Δ} {Γ : TermCtx Δ} {M : GTerm Δ} {A : Ty Δ}
  → (M⊢ : Δ ∣ Γ ⊢ M ⦂ A) → ElabE Γ M (compileᴱ M⊢) A
compileᴱ-elab (G.⊢` x∈) = Eᴱ-` x∈
compileᴱ-elab (G.⊢ƛ M⊢) = Eᴱ-ƛ (compileᴱ-elab M⊢)
compileᴱ-elab (G.⊢· L⊢ M⊢ A∼D) =
  Eᴱ-· (compileᴱ-elab L⊢) (compileᴱ-elab M⊢) A∼D
    (eager (symᶜ A∼D)) (eager-normal (symᶜ A∼D))
compileᴱ-elab (G.⊢·★ L⊢ M⊢ A∼★) =
  Eᴱ-·★ (compileᴱ-elab L⊢) (compileᴱ-elab M⊢) A∼★
    dynamic-function-cast dynamic-function-cast-eager
    (eager A∼★) (eager-normal A∼★)
compileᴱ-elab (G.⊢Λ {zero∈A = z} vM M⊢) =
  Eᴱ-Λ z vM (compileᴱ-value vM M⊢) (compileᴱ-elab M⊢)
compileᴱ-elab (G.⊢• M⊢) = Eᴱ-[] (compileᴱ-elab M⊢) refl
compileᴱ-elab (G.⊢$ κ) = Eᴱ-$ κ
compileᴱ-elab (G.⊢⊕ op L⊢ A∼arg M⊢ B∼arg) =
  Eᴱ-⊕ op (compileᴱ-elab L⊢) A∼arg (eager A∼arg) (eager-normal A∼arg)
    (compileᴱ-elab M⊢) B∼arg (eager B∼arg) (eager-normal B∼arg)
