module strong.Reduction where

-- Strong System F — v3 REDUCTION (notes/notes-v3.md §"Reduction Rules").
--
-- The v3 rules, in de Bruijn form.  Two families of runtime forms drive
-- them: the SCOPE BOUNDARY ᵇ[M] = `M ⟦ b ⟧` and the CONVERSION
-- M⟨c⟩ = `M ⟨ c ⟩`.
--
-- Supporting operations defined here:
--   crossArg b W   the argument crossing `⁻ᵇ[W]` of the application rule —
--                  the dual boundary (strong.CtxMorph `dualᵇ`) applied to
--                  W, with W weakened past the fresh binder when b = intro.
--   c [ A ]ᶜ       conversion instantiation — substitute the type A for the
--                  outermost binder of a conversion, used by
--                  `V⟨∀X.c⟩@B[A] -→ (V A)⟨c⟩`.
--
-- DEFERRED to the proof phase (this file defines the RELATION only):
--   value-¬step, det (determinism), and the ξ/preservation metatheory.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Var; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; _[_]ᵗ
        ; Substᵗ; substᵗ; extsᵗ; singleTyEnv)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.CtxMorph
open import strong.TermSubst

------------------------------------------------------------------------
-- 0.  Supporting operations
------------------------------------------------------------------------

-- The argument crossing  ⁻ᵇ[W]  (notes' application rule).  The dual tag
-- `dualᵇ b` (strong.CtxMorph) wraps W; when b introduces a binder, W is
-- also weakened past it.
crossArg : Bnd → Term → Term
crossArg (intro A)   W = (⇑ᴹ W) ⟦ conceal (0 ∷ []) ⟧
crossArg (reveal χ)  W = W ⟦ conceal χ ⟧
crossArg (conceal χ) W = W ⟦ reveal χ ⟧

-- The de Bruijn variable underlying a type (junk 0 if not a variable — a
-- seal/unseal is never instantiated at its own bound slot, so the junk
-- branch is dead on well-typed conversions).
tyVar : Ty → ℕ
tyVar (` X) = X
tyVar _     = 0

-- Conversion instantiation under a type substitution: id-payloads move by
-- `substᵗ`, seal/unseal names by the variable action of σ, structural on
-- the rest.
instConvσ : Substᵗ → Conv → Conv
instConvσ σ (id A)     = id (substᵗ σ A)
instConvσ σ (seal X)   = seal (tyVar (σ X))
instConvσ σ (unseal X) = unseal (tyVar (σ X))
instConvσ σ (s ↦ t)    = instConvσ σ s ↦ instConvσ σ t
instConvσ σ (`∀ s)     = `∀ (instConvσ (extsᵗ σ) s)

-- c [ A ]ᶜ : substitute A for the outermost conversion binder.
infix 8 _[_]ᶜ
_[_]ᶜ : Conv → Ty → Conv
c [ A ]ᶜ = instConvσ (singleTyEnv A) c

-- The positive boundary tags (intro / reveal), for the positive
-- type-application rule.
data Positive : Bnd → Set where
  pos-intro  : ∀ {A} → Positive (intro A)
  pos-reveal : ∀ {χ} → Positive (reveal χ)

------------------------------------------------------------------------
-- 1.  The reduction relation
------------------------------------------------------------------------

infix 2 _⊢_-→_
data _⊢_-→_ : Ctxᵗ → Term → Term → Set where

  -- (λx:A.N)·W -→ N[x:=W : A]
  Beta : ∀ {Δ A N W} → Value W
    → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ∶ A ]ᵐ

  -- V⟨c→d⟩·W -→ (V (W⟨c⟩))⟨d⟩       (c = s domain, d = t codomain)
  ConvFun : ∀ {Δ V W s t} → Value V → Value W
    → Δ ⊢ (V ⟨ s ↦ t ⟩) · W -→ (V · (W ⟨ s ⟩)) ⟨ t ⟩

  -- ᵇ[Vˢ]·W -→ ᵇ[Vˢ · ⁻ᵇ[W]]   (if ᵇ[Vˢ] is a value; Vˢ simple)
  AppBnd : ∀ {Δ M b W} → Simple M → Value (M ⟦ b ⟧) → Value W
    → Δ ⊢ (M ⟦ b ⟧) · W -→ (M · crossArg b W) ⟦ b ⟧

  -- V⟨-X⟩⟨+X⟩ -→ V              (-X = seal, +X = unseal, same X)
  Cancel : ∀ {Δ V X} → Value V
    → Δ ⊢ (V ⟨ seal X ⟩) ⟨ unseal X ⟩ -→ V

  -- V⟨id⟩ -→ V
  DropId : ∀ {Δ V A} → Value V
    → Δ ⊢ V ⟨ id A ⟩ -→ V

  -- ᵇ[k] -→ k                    (k a numeral)
  DropNum : ∀ {Δ n b}
    → Δ ⊢ ($ n) ⟦ b ⟧ -→ $ n

  -- (ΛX.V)@B[A] -→ ⁺ˣ⁼ᴬ[V⟨+X(B)⟩]
  TyBeta : ∀ {Δ V B A} → Value V
    → Δ ⊢ (Λ V) ·[ B , A ] -→ (V ⟨ revTy 0 B ⟩) ⟦ intro A ⟧

  -- V⟨∀X.c⟩@B[A] -→ (V A)⟨c[A]⟩.  The source ∀-body A₀ is premise-
  -- determined (conv-src-unique), exactly as v2's TyPeelR did.
  TyConv : ∀ {Δ V s A₀ B A} → Value V
    → (unmasked abst ∷ Δ) ⊢ s ∶ A₀ ⇝ B
    → Δ ⊢ (V ⟨ `∀ s ⟩) ·[ B , A ] -→ (V ·[ A₀ , A ]) ⟨ s [ A ]ᶜ ⟩

  -- ⁺ᵖ[V⁺]@B[A] -→ ⁺ʸ⁼ᴬ[⁺ᵖ[⁻ʸ[V⁺]@B[Y]]]   (Y fresh = new binder 0)
  TyPos : ∀ {Δ M b B A} → Positive b → Value (M ⟦ b ⟧)
    → Δ ⊢ (M ⟦ b ⟧) ·[ B , A ]
        -→ ((((renᴹ (extN (numBindsᵇ b) suc) M) ⟦ conceal (0 ∷ []) ⟧)
               ·[ renameᵗ (extᵗ suc) B , ` 0 ]) ⟦ renBnd suc b ⟧) ⟦ intro A ⟧

  -- ⁻χ[ΛY.V]@B[A] -→ ⁺ʸ⁼ᴬ[⁻χ[V]]   (Y fresh; V moves out, χ shifts past Y)
  TyConceal : ∀ {Δ χ V B A} → NonEmpty χ → Value V
    → Δ ⊢ ((Λ V) ⟦ conceal χ ⟧) ·[ B , A ]
        -→ (V ⟦ conceal (map suc χ) ⟧) ⟦ intro A ⟧

  -- ⁻χ[Vᶜ⟨cⁱ⟩] -→ ⁻χ[Vᶜ]⟨cⁱ⟩       (cⁱ inert)
  PushConv : ∀ {Δ M c χ} → Cnv M → Inert c
    → Δ ⊢ (M ⟨ c ⟩) ⟦ conceal χ ⟧ -→ (M ⟦ conceal χ ⟧) ⟨ c ⟩

  -- ⁺⁰[V⁺] -→ V⁺
  DropReveal : ∀ {Δ M} → Pos M
    → Δ ⊢ M ⟦ reveal [] ⟧ -→ M

  -- ⁻⁰[Vˢ] -→ Vˢ
  DropConceal : ∀ {Δ M} → Simple M
    → Δ ⊢ M ⟦ conceal [] ⟧ -→ M

  -- ⁻χ¹[⁺χ²[V⁺]] -→ ⁺χ³[⁻χ⁴[V⁺]]   (χ3 = χ2 ∖ χ1, χ4 = χ1 ∖ χ2)
  Commute : ∀ {Δ M χ₁ χ₂} → Pos M → NonEmpty χ₁ → NonEmpty χ₂
    → Δ ⊢ (M ⟦ reveal χ₂ ⟧) ⟦ conceal χ₁ ⟧
        -→ (M ⟦ conceal (χ₁ ∖ χ₂) ⟧) ⟦ reveal (χ₂ ∖ χ₁) ⟧

  -- ⁻χ[⁺ʸ⁼ᴬ[V⁺]] -→ ⁺ʸ⁼ᴬ[⁻χ[V⁺]]   (conceal past intro; χ shifts past Y)
  PushIntro : ∀ {Δ M A χ} → Pos M → NonEmpty χ
    → Δ ⊢ (M ⟦ intro A ⟧) ⟦ conceal χ ⟧
        -→ (M ⟦ conceal (map suc χ) ⟧) ⟦ intro A ⟧

  -- ⁻χ¹[⁻χ²[Vˢ]] -→ ⁻χ¹χ²[Vˢ]
  MergeConceal : ∀ {Δ M χ₁ χ₂} → Simple M → NonEmpty χ₁ → NonEmpty χ₂
    → Δ ⊢ (M ⟦ conceal χ₂ ⟧) ⟦ conceal χ₁ ⟧ -→ M ⟦ conceal (χ₁ ∪ χ₂) ⟧

  -- congruences
  ξ-·-l : ∀ {Δ L L′ M} → Δ ⊢ L -→ L′ → Δ ⊢ L · M -→ L′ · M
  ξ-·-r : ∀ {Δ V M M′} → Value V → Δ ⊢ M -→ M′ → Δ ⊢ V · M -→ V · M′
  ξ-·[] : ∀ {Δ L L′ B A} → Δ ⊢ L -→ L′ → Δ ⊢ L ·[ B , A ] -→ L′ ·[ B , A ]
  ξ-Λ   : ∀ {Δ N N′} → (unmasked abst ∷ Δ) ⊢ N -→ N′ → Δ ⊢ Λ N -→ Λ N′
  ξ-⟨⟩  : ∀ {Δ M M′ c} → Δ ⊢ M -→ M′ → Δ ⊢ M ⟨ c ⟩ -→ M′ ⟨ c ⟩
  ξ-⟦⟧  : ∀ {Δ M M′ b} → applyᵇ b Δ ⊢ M -→ M′ → Δ ⊢ M ⟦ b ⟧ -→ M′ ⟦ b ⟧

infix 2 _⊢_-→*_
data _⊢_-→*_ : Ctxᵗ → Term → Term → Set where
  done   : ∀ {Δ M} → Δ ⊢ M -→* M
  _then_ : ∀ {Δ L M N} → Δ ⊢ L -→ M → Δ ⊢ M -→* N → Δ ⊢ L -→* N

infixr 2 _then_
