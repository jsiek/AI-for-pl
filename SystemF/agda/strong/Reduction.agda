module strong.Reduction where

-- Strong System F — v3 REDUCTION (notes/notes-v3.md §"Reduction Rules").
--
-- The v3 rules, in de Bruijn form.  Two families of runtime forms drive
-- them: the SCOPE BOUNDARY ᵇ[M] = `ν b [ M ]` and the CONVERSION
-- M⟨c⟩ = `M ⟨ c ⟩`.
--
-- Supporting operations defined here:
--   shiftIn b W    the shift the interior of b forces on an entering term:
--                  `⇑ᴹ W` for an `intro` (it binds), W itself otherwise.
--                  The application rule writes its argument crossing
--                  `⁻ᵇ[W]` out in full as `ν dualᵇ b [ shiftIn b W ]`.
--   c [ A ]ᶜ       conversion instantiation — substitute the type A for the
--                  outermost binder of a conversion, used by
--                  `V⟨∀X.c⟩@B[A] -→ (V A)⟨c⟩`.
--
-- COLOUR ANNOTATIONS.  `κ` ranges over the colour sets that source nodes
-- carry (strong.Terms `⟪ κ ⟫`); `χ` still ranges over boundary TAG sets.
-- EXACTLY TWO rules recompute a κ — `AppBnd` and `TyPos`, the two that
-- move a node across a boundary — and both compute it from the node's own
-- old κ and the tag, via `scopeᵇ` (strong.CtxMorph §5).  Every other rule
-- transports annotations unchanged, which is what makes Preservation
-- imply colour preservation.
--
-- DEFERRED to the proof phase (this file defines the RELATION only):
--   value-¬step, det (determinism), and the ξ/preservation metatheory.

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
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

-- The de Bruijn shift the interior of a boundary forces on a term
-- ENTERING it.  ONLY `intro` causes one, because only `intro` adds a
-- binder; `reveal`/`conceal` rename nothing.
shiftIn : Bnd → Term → Term
shiftIn (intro A)   W = ⇑ᴹ W
shiftIn (reveal χ)  W = W
shiftIn (conceal χ) W = W

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

-- The meaning of a primitive operator  ⟦⊕⟧.
⟦_⟧ᵖ : Prim → ℕ → ℕ → ℕ
⟦ p+ ⟧ᵖ m n = m + n
⟦ p× ⟧ᵖ m n = m * n

------------------------------------------------------------------------
-- 1.  The reduction relation
------------------------------------------------------------------------

infix 2 _⊢_-→_
data _⊢_-→_ : Ctxᵗ → Term → Term → Set where

  -- (λx:A.N)·W -→ N[x:=W : A]
  Beta : ∀ {Δ A N W κ₁ κ₂} → Value W
    → Δ ⊢ (ƛ A ∙ N ⟪ κ₁ ⟫) · W ⟪ κ₂ ⟫ -→ N [ W ∶ A ]ᵐ

  -- V⟨c→d⟩·W -→ (V (W⟨c⟩))⟨d⟩       (c = s domain, d = t codomain)
  ConvFun : ∀ {Δ V W s t κ} → Value V → Value W
    → Δ ⊢ (V ⟨ s ↦ t ⟩) · W ⟪ κ ⟫ -→ (V · (W ⟨ s ⟩) ⟪ κ ⟫) ⟨ t ⟩

  -- ᵇ[V⁺]·W -→ ᵇ[V⁺ · ⁻ᵇ[W]]   (if ᵇ[V⁺] is a value).  Generalised past the
  -- notes' `Vˢ` to ANY value under the boundary — closing the Progress gap
  -- for a positive boundary around a non-simple value (audit item).  The
  -- `Value (ν b [ M ])` premise still pins the operator to a value, so it
  -- cannot overlap ξ-·-l.
  --
  -- The argument enters under the DUAL tag `dualᵇ b` (CtxMorph), shifted
  -- only if b binds.  That crossing restores W's frame EXACTLY —
  -- `lock-unlock` / `unlock-lock` — so every annotation W carries is
  -- still right on the inside, and so is every annotation in M.
  --
  -- COLOUR.  This is ONE OF THE TWO rules that move a node ACROSS a
  -- boundary: the application node itself lands at the INTERIOR frame
  -- `applyᵇ b Δ`, so it is REBUILT with the interior colour set
  -- `scopeᵇ b κ`.  It is the ONLY thing here whose colours change.
  AppBnd : ∀ {Δ M b W κ} → Value (ν b [ M ]) → Value W
    → Δ ⊢ (ν b [ M ]) · W ⟪ κ ⟫
        -→ ν b [ M · (ν dualᵇ b [ shiftIn b W ]) ⟪ scopeᵇ b κ ⟫ ]

  -- V⟨-X⟩⟨+X⟩ -→ V              (-X = seal, +X = unseal, same X)
  Cancel : ∀ {Δ V X} → Value V
    → Δ ⊢ (V ⟨ seal X ⟩) ⟨ unseal X ⟩ -→ V

  -- V⟨id⟩ -→ V
  DropId : ∀ {Δ V A} → Value V
    → Δ ⊢ V ⟨ id A ⟩ -→ V

  -- ᵇ[k] -→ k                    (k a constant: numeral or boolean)
  DropConst : ∀ {Δ k b} → Const k
    → Δ ⊢ ν b [ k ] -→ k

  -- n₁ ⊕ n₂ -→ n₁ ⟦⊕⟧ n₂
  PrimBeta : ∀ {Δ p m n κ}
    → Δ ⊢ ($ m) ⊕[ p ] ($ n) ⟪ κ ⟫ -→ $ (⟦ p ⟧ᵖ m n)

  -- (ΛX.V)@B[A] -→ ⁺ˣ⁼ᴬ[V⟨+X(B)⟩]
  -- COLOUR: none changes.  V's frame goes from `unmasked abst ∷ Δ` to
  -- `unmasked (bind A) ∷ Δ` — both UNMASKED, so scopeᵗ is the same list.
  -- The Λ-bound colour simply becomes the intro'd one.
  TyBeta : ∀ {Δ V B A κ₁ κ₂} → Value V
    → Δ ⊢ (Λ V ⟪ κ₁ ⟫) • B [ A ]⟪ κ₂ ⟫ -→ ν intro A [ V ⟨ revTy 0 B ⟩ ]

  -- V⟨∀X.c⟩@B[A] -→ (V A)⟨c[A]⟩.  The source ∀-body A₀ is premise-
  -- determined (conv-src-unique), exactly as v2's TyPeelR did.
  TyConv : ∀ {Δ V s A₀ B A κ} → Value V
    → (unmasked abst ∷ Δ) ⊢ s ∶ A₀ ⇝ B
    → Δ ⊢ (V ⟨ `∀ s ⟩) • B [ A ]⟪ κ ⟫ -→ (V • A₀ [ A ]⟪ κ ⟫) ⟨ s [ A ]ᶜ ⟩

  -- ⁺ᵖ[V⁺]@B[A] -→ ⁺ʸ⁼ᴬ[⁺ᵖ[⁻ʸ[V⁺]@B[Y]]]   (Y fresh = new binder 0)
  --
  -- COLOUR.  The OTHER boundary-crossing rule: the type-application node
  -- is rebuilt two boundaries deeper, so its colour set is `κ` pushed
  -- through the fresh binder and then through the (shifted) tag b.  M's
  -- own annotations are SHIFTED by the same `renᴹ` that shifts its type
  -- variables — that shift is the frame-exactness tripwire.
  TyPos : ∀ {Δ M b B A κ} → Positive b → Value (ν b [ M ])
    → Δ ⊢ (ν b [ M ]) • B [ A ]⟪ κ ⟫
        -→ ν intro A [ ν renBnd suc b
             [ (ν conceal (0 ∷ []) [ renᴹ (extN (numBindsᵇ b) suc) M ])
                 • renameᵗ (extᵗ suc) B [ ` 0 ]⟪
                     scopeᵇ (renBnd suc b) (scopeᵇ (intro A) κ) ⟫ ] ]

  -- ⁻χ[ΛY.V]@B[A] -→ ⁺ʸ⁼ᴬ[⁻χ[V]]   (Y fresh; V moves out, χ shifts past Y)
  -- COLOUR: none changes.  V's frame goes from `unmasked abst ∷ lockχ χ Δ`
  -- to `lockχ (map suc χ) (unmasked (bind A) ∷ Δ)` — the SAME context.
  TyConceal : ∀ {Δ χ V B A κ₁ κ₂} → NonEmpty χ → Value V
    → Δ ⊢ (ν conceal χ [ Λ V ⟪ κ₁ ⟫ ]) • B [ A ]⟪ κ₂ ⟫
        -→ ν intro A [ ν conceal (map suc χ) [ V ] ]

  -- ⁻χ[Vᶜ⟨cⁱ⟩] -→ ⁻χ[Vᶜ]⟨cⁱ⟩       (cⁱ inert)
  PushConv : ∀ {Δ M c χ} → Cnv M → Inert c
    → Δ ⊢ ν conceal χ [ M ⟨ c ⟩ ] -→ (ν conceal χ [ M ]) ⟨ c ⟩

  -- ⁺⁰[V⁺] -→ V⁺
  DropReveal : ∀ {Δ M} → Pos M
    → Δ ⊢ ν reveal [] [ M ] -→ M

  -- ⁻⁰[Vˢ] -→ Vˢ
  DropConceal : ∀ {Δ M} → Simple M
    → Δ ⊢ ν conceal [] [ M ] -→ M

  -- ⁻χ¹[⁺χ²[V⁺]] -→ ⁺χ³[⁻χ⁴[V⁺]]   (χ3 = χ2 ∖ χ1, χ4 = χ1 ∖ χ2)
  Commute : ∀ {Δ M χ₁ χ₂} → Pos M → NonEmpty χ₁ → NonEmpty χ₂
    → Δ ⊢ ν conceal χ₁ [ ν reveal χ₂ [ M ] ]
        -→ ν reveal (χ₂ ∖ χ₁) [ ν conceal (χ₁ ∖ χ₂) [ M ] ]

  -- ⁻χ[⁺ʸ⁼ᴬ[V⁺]] -→ ⁺ʸ⁼ᴬ[⁻χ[V⁺]]   (conceal past intro; χ shifts past Y)
  PushIntro : ∀ {Δ M A χ} → Pos M → NonEmpty χ
    → Δ ⊢ ν conceal χ [ ν intro A [ M ] ]
        -→ ν intro A [ ν conceal (map suc χ) [ M ] ]

  -- ⁻χ¹[⁻χ²[Vˢ]] -→ ⁻χ¹χ²[Vˢ]
  MergeConceal : ∀ {Δ M χ₁ χ₂} → Simple M → NonEmpty χ₁ → NonEmpty χ₂
    → Δ ⊢ ν conceal χ₁ [ ν conceal χ₂ [ M ] ] -→ ν conceal (χ₁ ∪ χ₂) [ M ]

  -- congruences
  -- The congruences keep every annotation, their own included: a
  -- congruence changes no frame.
  ξ-⊕-l : ∀ {Δ L L′ M p κ} → Δ ⊢ L -→ L′
        → Δ ⊢ L ⊕[ p ] M ⟪ κ ⟫ -→ L′ ⊕[ p ] M ⟪ κ ⟫
  ξ-⊕-r : ∀ {Δ V M M′ p κ} → Value V → Δ ⊢ M -→ M′
        → Δ ⊢ V ⊕[ p ] M ⟪ κ ⟫ -→ V ⊕[ p ] M′ ⟪ κ ⟫
  ξ-·-l : ∀ {Δ L L′ M κ} → Δ ⊢ L -→ L′ → Δ ⊢ L · M ⟪ κ ⟫ -→ L′ · M ⟪ κ ⟫
  ξ-·-r : ∀ {Δ V M M′ κ} → Value V → Δ ⊢ M -→ M′
        → Δ ⊢ V · M ⟪ κ ⟫ -→ V · M′ ⟪ κ ⟫
  ξ-•[] : ∀ {Δ L L′ B A κ} → Δ ⊢ L -→ L′
        → Δ ⊢ L • B [ A ]⟪ κ ⟫ -→ L′ • B [ A ]⟪ κ ⟫
  ξ-Λ   : ∀ {Δ N N′ κ} → (unmasked abst ∷ Δ) ⊢ N -→ N′
        → Δ ⊢ Λ N ⟪ κ ⟫ -→ Λ N′ ⟪ κ ⟫
  ξ-⟨⟩  : ∀ {Δ M M′ c} → Δ ⊢ M -→ M′ → Δ ⊢ M ⟨ c ⟩ -→ M′ ⟨ c ⟩
  ξ-ν   : ∀ {Δ M M′ b} → applyᵇ b Δ ⊢ M -→ M′ → Δ ⊢ ν b [ M ] -→ ν b [ M′ ]

infix 2 _⊢_-→*_
data _⊢_-→*_ : Ctxᵗ → Term → Term → Set where
  done   : ∀ {Δ M} → Δ ⊢ M -→* M
  _then_ : ∀ {Δ L M N} → Δ ⊢ L -→ M → Δ ⊢ M -→* N → Δ ⊢ L -→* N

infixr 2 _then_
