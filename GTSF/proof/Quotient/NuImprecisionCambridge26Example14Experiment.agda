module
  proof.Quotient.NuImprecisionCambridge26Example14Experiment
  where

-- File Charter:
--   * Tests the complete smaller term-imprecision relation on Cambridge26
--     Example 14: instantiation/generalization repeated twice.
--   * Constructs the exact initial relation using only ordinary one-sided
--     cast rules, matched `ν`, application, and constants.
--   * Tests the allocation-heavy reduction square separately from the top
--     edge; no example-specific term-imprecision constructor is introduced.
--   * Imports no live term-imprecision judgment and contains no postulate,
--     hole, permissive option, termination bypass, or catch-all clause.

open import Agda.Builtin.Equality using (refl)
open import CastImprecisionShape using
  ( shape-fun
  ; shape-gen
  ; shape-inst
  ; shape-seal
  ; shape-tag-var
  ; shape-unseal
  ; shape-untag-var
  )
import Coercions as C
open C using (_!; _？)
open import Conversion using
  (RevealConversion; conceal-seal; reveal-fun; reveal-unseal)
open import ConversionIndexCompatibility using
  ( _[_↦_⊑⟨_⟩_↤_]ᴾ_
  ; replace-paired-function
  ; replace-paired-variables
  )
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (suc; zero; z<s)
open import Data.Product using (_,_)
open import Imprecision using (_ˣ⊑★; _ˣ⊑ˣ_)
open import ImprecisionComposition using
  ( comp-idˣ-tagˣ
  ; comp-↦-↦
  ; comp-∀-ν
  )
open import ImprecisionWf using
  ( _↦_
  ; _∣_⊢_⊑_⊣_
  ; idι
  ; idˣ
  ; tagˣ
  ; ∀ⁱ_
  ; ν
  )
import NarrowWiden as NW
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( lift-store-[]
  ; StoreImp
  ; store-matched
  ; store-right
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( ctx-imp
  ; lift-ctx-[]
  )
open import proof.Core.Properties.SealModeProperties using
  (seal★-tag-or-id)
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; no•-`
  ; no•-ƛ
  ; no•-Λ
  ; no•-$
  ; no•-⟨⟩
  ; `_
  ; ƛ_
  ; Λ_
  ; ν
  ; _·_
  ; _⟨_⟩
  ; $
  )
open import NuReduction using
  ( bind
  ; keep
  ; pure-step
  ; β
  ; β-gen•
  ; β-inst
  ; β-Λ•
  ; β-↦
  ; seal-unseal
  ; tag-untag-ok
  ; ν-step
  ; ξ-⟨⟩
  ; ↠-refl
  ; ↠-step
  ; _—↠[_]_
  )
open import Primitives using (κℕ)
open import TermTyping using (cast-tag-or-id)
open import Types using
  ( wfBase
  ; wf★
  ; wf⇒
  ; wfVar
  ; ★
  ; ‵_
  ; ＇_
  ; _⇒_
  ; `∀
  )
open import
  proof.Core.Properties.NuImprecisionIndexedRenamingProperties
  using (⊑-lift∀ᵢ; ⊑-target-lift-rightᵢ)
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
open import proof.Core.Properties.ReductionProperties using
  (cast-↠; ν-↠; ·₁-↠; ↠-trans)


private
  I : Term
  I = ƛ (` zero)

  vI : Value I
  vI = ƛ (` zero)

  noI : No• I
  noI = no•-ƛ no•-`

  F = ＇ zero ⇒ ＇ zero

  H = ★ ⇒ ★

  pX :
    ((zero ˣ⊑ˣ zero) ∷ [])
      ∣ suc zero ⊢ ＇ zero ⊑ ＇ zero ⊣ suc zero
  pX = idˣ (here refl) z<s z<s

  pF :
    ((zero ˣ⊑ˣ zero) ∷ [])
      ∣ suc zero ⊢ F ⊑ F ⊣ suc zero
  pF = pX ↦ pX

  p∀F :
    [] ∣ zero ⊢ `∀ F ⊑ `∀ F ⊣ zero
  p∀F = ∀ⁱ pF

  pX★ :
    ((zero ˣ⊑★) ∷ [])
      ∣ suc zero ⊢ ＇ zero ⊑ ★ ⊣ zero
  pX★ = tagˣ (here refl) z<s

  pFH :
    ((zero ˣ⊑★) ∷ [])
      ∣ suc zero ⊢ F ⊑ H ⊣ zero
  pFH = pX★ ↦ pX★

  p∀H :
    [] ∣ zero ⊢ `∀ F ⊑ H ⊣ zero
  p∀H = ν Imprecision.nonvar-fun refl pFH

  inst-body-at : Data.Nat.ℕ → C.Coercion
  inst-body-at α =
    C.seal ★ α C.↦ C.unseal α ★

  gen-body-at : Data.Nat.ℕ → C.Coercion
  gen-body-at α =
    ((＇ α) !) C.↦ ((＇ α) ？)

  inst-body : C.Coercion
  inst-body = inst-body-at zero

  gen-body : C.Coercion
  gen-body = gen-body-at zero

  inst-cast : C.Coercion
  inst-cast =
    C.inst H inst-body

  gen-cast : C.Coercion
  gen-cast =
    C.gen H gen-body

  inst-cast-typing :
    C.tag-or-idᵈ ∣ zero ∣ []
      ⊢ inst-cast ∶ `∀ F ⊑ H
  inst-cast-typing =
    C.cast-inst (wf⇒ wf★ wf★) refl
      (C.cast-fun
        (C.cast-seal wf★ (here refl) refl)
        (C.cast-unseal wf★ (here refl) refl)) ,
    NW.inst
      (NW.safe-fun
        (NW.sealⁿ ★ zero)
        (NW.unsealʷ zero ★))

  gen-cast-typing :
    C.tag-or-idᵈ ∣ zero ∣ []
      ⊢ gen-cast ∶ H ⊒ `∀ F
  gen-cast-typing =
    C.cast-gen (wf⇒ wf★ wf★) refl
      (C.cast-fun
        (C.cast-tag (wfVar z<s) (＇ zero) refl)
        (C.cast-untag (wfVar z<s) (＇ zero) refl)) ,
    NW.gen
      (NW.safe-fun
        (NW.tag (＇ zero))
        (NW.untag (＇ zero)))

  cast-index-composition =
    comp-∀-ν
      (comp-↦-↦ comp-idˣ-tagˣ comp-idˣ-tagˣ)

  polymorphic-identityᴿ :
    [] ∣ zero ∣ zero ∣ [] ∣ []
      ⊢ᴿ Λ I ⊑ Λ I
      ⦂ `∀ F ⊑ `∀ F ∶ p∀F
  polymorphic-identityᴿ =
    Λ⊑Λᴿ lift-store-[] lift-ctx-[]
      vI vI
      (ƛ⊑ƛᴿ (wfVar z<s) (wfVar z<s)
        (x⊑xᴿ Types.Z))

  one-instᴿ :
    [] ∣ zero ∣ zero ∣ [] ∣ []
      ⊢ᴿ Λ I ⊑ (Λ I) ⟨ inst-cast ⟩
      ⦂ `∀ F ⊑ H ∶ p∀H
  one-instᴿ =
    ⊑cast⊑ᴿ cast-tag-or-id seal★-tag-or-id
      inst-cast-typing polymorphic-identityᴿ p∀H
      (shape-inst (shape-fun shape-seal shape-unseal))
      cast-index-composition

  one-round-tripᴿ :
    [] ∣ zero ∣ zero ∣ [] ∣ []
      ⊢ᴿ Λ I
        ⊑ ((Λ I) ⟨ inst-cast ⟩) ⟨ gen-cast ⟩
      ⦂ `∀ F ⊑ `∀ F ∶ p∀F
  one-round-tripᴿ =
    ⊑cast⊒ᴿ cast-tag-or-id seal★-tag-or-id
      gen-cast-typing one-instᴿ p∀F
      (shape-gen (shape-fun shape-tag-var shape-untag-var))
      cast-index-composition

  two-instᴿ :
    [] ∣ zero ∣ zero ∣ [] ∣ []
      ⊢ᴿ Λ I
        ⊑
          (((Λ I) ⟨ inst-cast ⟩) ⟨ gen-cast ⟩)
            ⟨ inst-cast ⟩
      ⦂ `∀ F ⊑ H ∶ p∀H
  two-instᴿ =
    ⊑cast⊑ᴿ cast-tag-or-id seal★-tag-or-id
      inst-cast-typing one-round-tripᴿ p∀H
      (shape-inst (shape-fun shape-seal shape-unseal))
      cast-index-composition

  two-round-tripsᴿ :
    [] ∣ zero ∣ zero ∣ [] ∣ []
      ⊢ᴿ Λ I
        ⊑
          ((((Λ I) ⟨ inst-cast ⟩) ⟨ gen-cast ⟩)
            ⟨ inst-cast ⟩) ⟨ gen-cast ⟩
      ⦂ `∀ F ⊑ `∀ F ∶ p∀F
  two-round-tripsᴿ =
    ⊑cast⊒ᴿ cast-tag-or-id seal★-tag-or-id
      gen-cast-typing two-instᴿ p∀F
      (shape-gen (shape-fun shape-tag-var shape-untag-var))
      cast-index-composition

  one-inst-trace :
    (Λ I) ⟨ inst-cast ⟩
      —↠[ keep ∷ bind ★ ∷ keep ∷ [] ]
    I ⟨ inst-body-at zero ⟩
  one-inst-trace =
    ↠-step (pure-step (β-inst (Λ vI)))
      (↠-step
        (ν-step (Λ vI) (no•-Λ noI))
        (↠-step
          (ξ-⟨⟩ (pure-step (β-Λ• vI)))
          ↠-refl))

  first-round-value :
    Value ((I ⟨ inst-body-at zero ⟩) ⟨ gen-cast ⟩)
  first-round-value =
    (vI ⟨ C.seal ★ zero C.↦ C.unseal zero ★ ⟩)
      ⟨ C.gen H gen-body ⟩

  first-round-no-bullet :
    No• ((I ⟨ inst-body-at zero ⟩) ⟨ gen-cast ⟩)
  first-round-no-bullet =
    no•-⟨⟩ (no•-⟨⟩ noI)

  second-inst-trace :
    (((I ⟨ inst-body-at zero ⟩) ⟨ gen-cast ⟩)
      ⟨ inst-cast ⟩)
      —↠[ keep ∷ bind ★ ∷ keep ∷ [] ]
    ((I ⟨ inst-body-at (suc zero) ⟩)
      ⟨ gen-body-at zero ⟩) ⟨ inst-body-at zero ⟩
  second-inst-trace =
    ↠-step (pure-step (β-inst first-round-value))
      (↠-step
        (ν-step first-round-value first-round-no-bullet)
        (↠-step
          (ξ-⟨⟩
            (pure-step
              (β-gen•
                (vI
                  ⟨ C.seal ★ (suc zero)
                    C.↦ C.unseal (suc zero) ★ ⟩))))
          ↠-refl))

  two-round-trips-value-trace :
    ((((Λ I) ⟨ inst-cast ⟩) ⟨ gen-cast ⟩)
      ⟨ inst-cast ⟩) ⟨ gen-cast ⟩
      —↠[
        keep ∷ bind ★ ∷ keep ∷
        keep ∷ bind ★ ∷ keep ∷ []
      ]
    (((I ⟨ inst-body-at (suc zero) ⟩)
      ⟨ gen-body-at zero ⟩)
      ⟨ inst-body-at zero ⟩) ⟨ gen-cast ⟩
  two-round-trips-value-trace =
    ↠-trans
      (cast-↠ (cast-↠ (cast-↠ one-inst-trace)))
      (cast-↠ second-inst-trace)

  pι :
    [] ∣ zero
      ⊢ ‵ Types.`ℕ ⊑ ‵ Types.`ℕ ⊣ zero
  pι =
    idι {ι = Types.`ℕ}

  pι⇒ι :
    [] ∣ zero
      ⊢ (‵ Types.`ℕ ⇒ ‵ Types.`ℕ)
        ⊑ (‵ Types.`ℕ ⇒ ‵ Types.`ℕ)
      ⊣ zero
  pι⇒ι =
    pι ↦ pι

  reveal-ι : C.Coercion
  reveal-ι =
    C.seal (‵ Types.`ℕ) zero
      C.↦ C.unseal zero (‵ Types.`ℕ)

  reveal-ι-conversion :
    RevealConversion C.seal-or-idᵈ (suc zero)
      ((zero , ‵ Types.`ℕ) ∷ [])
      zero (‵ Types.`ℕ) reveal-ι
      F (‵ Types.`ℕ ⇒ ‵ Types.`ℕ)
  reveal-ι-conversion =
    reveal-fun
      (conceal-seal wfBase (here refl) refl)
      (reveal-unseal wfBase (here refl) refl)

  reveal-ι-replacement :
    pF
      [ zero ↦ ‵ Types.`ℕ
      ⊑⟨ ⊑-lift∀ᵢ pι ⟩
      ‵ Types.`ℕ ↤ zero ]ᴾ
    ⊑-lift∀ᵢ pι⇒ι
  reveal-ι-replacement =
    replace-paired-function
      (replace-paired-variables refl)
      (replace-paired-variables refl)

  two-round-trips-value :
    Value
      ((((I ⟨ inst-body-at (suc zero) ⟩)
        ⟨ gen-body-at zero ⟩)
        ⟨ inst-body-at zero ⟩) ⟨ gen-cast ⟩)
  two-round-trips-value =
    (((vI
      ⟨ C.seal ★ (suc zero)
        C.↦ C.unseal (suc zero) ★ ⟩)
      ⟨ ((＇ zero) !) C.↦ ((＇ zero) ？) ⟩)
      ⟨ C.seal ★ zero C.↦ C.unseal zero ★ ⟩)
      ⟨ C.gen H gen-body ⟩

  two-round-trips-no-bullet :
    No•
      ((((I ⟨ inst-body-at (suc zero) ⟩)
        ⟨ gen-body-at zero ⟩)
        ⟨ inst-body-at zero ⟩) ⟨ gen-cast ⟩)
  two-round-trips-no-bullet =
    no•-⟨⟩ (no•-⟨⟩ (no•-⟨⟩ (no•-⟨⟩ noI)))

  simple-ν-function-trace :
    ν (‵ Types.`ℕ) (Λ I) reveal-ι
      —↠[ bind (‵ Types.`ℕ) ∷ keep ∷ [] ]
    I ⟨ reveal-ι ⟩
  simple-ν-function-trace =
    ↠-step
      (ν-step (Λ vI) (no•-Λ noI))
      (↠-step
        (ξ-⟨⟩ (pure-step (β-Λ• vI)))
        ↠-refl)

  complex-ν-function-trace :
    ν (‵ Types.`ℕ)
      (((((Λ I) ⟨ inst-cast ⟩) ⟨ gen-cast ⟩)
        ⟨ inst-cast ⟩) ⟨ gen-cast ⟩)
      reveal-ι
      —↠[
        keep ∷ bind ★ ∷ keep ∷
        keep ∷ bind ★ ∷ keep ∷
        bind (‵ Types.`ℕ) ∷ keep ∷ []
      ]
    ((((I ⟨ inst-body-at (suc (suc zero)) ⟩)
      ⟨ gen-body-at (suc zero) ⟩)
      ⟨ inst-body-at (suc zero) ⟩)
      ⟨ gen-body-at zero ⟩) ⟨ reveal-ι ⟩
  complex-ν-function-trace =
    ↠-trans
      (ν-↠ two-round-trips-value-trace)
      (↠-step
        (ν-step two-round-trips-value
          two-round-trips-no-bullet)
        (↠-step
          (ξ-⟨⟩
            (pure-step
              (β-gen•
                (((vI
                  ⟨ C.seal ★ (suc (suc zero))
                    C.↦ C.unseal (suc (suc zero)) ★ ⟩)
                  ⟨ ((＇ (suc zero)) !)
                    C.↦ ((＇ (suc zero)) ？) ⟩)
                  ⟨ C.seal ★ (suc zero)
                    C.↦ C.unseal (suc zero) ★ ⟩))))
          ↠-refl))

  simple-function-application-trace :
    (I ⟨ reveal-ι ⟩) · $ (κℕ zero)
      —↠[ keep ∷ keep ∷ keep ∷ [] ]
    $ (κℕ zero)
  simple-function-application-trace =
    ↠-step
      (pure-step (β-↦ vI ($ (κℕ zero))))
      (↠-step
        (ξ-⟨⟩
          (pure-step
            (β
              (($ (κℕ zero))
                ⟨ C.seal (‵ Types.`ℕ) zero ⟩))))
        (↠-step
          (pure-step (seal-unseal ($ (κℕ zero))))
          ↠-refl))

  complex-function-application-trace :
    (((((I ⟨ inst-body-at (suc (suc zero)) ⟩)
      ⟨ gen-body-at (suc zero) ⟩)
      ⟨ inst-body-at (suc zero) ⟩)
      ⟨ gen-body-at zero ⟩) ⟨ reveal-ι ⟩)
      · $ (κℕ zero)
      —↠[
        keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ []
      ]
    (((((((((($ (κℕ zero))
      ⟨ C.seal (‵ Types.`ℕ) zero ⟩)
      ⟨ (＇ zero) ! ⟩)
      ⟨ C.seal ★ (suc zero) ⟩)
      ⟨ (＇ (suc zero)) ! ⟩)
      ⟨ C.seal ★ (suc (suc zero)) ⟩)
      ⟨ C.unseal (suc (suc zero)) ★ ⟩)
      ⟨ (＇ (suc zero)) ？ ⟩)
      ⟨ C.unseal (suc zero) ★ ⟩)
      ⟨ (＇ zero) ？ ⟩)
      ⟨ C.unseal zero (‵ Types.`ℕ) ⟩
  complex-function-application-trace =
    ↠-step
      (pure-step
        (β-↦
          ((((vI
            ⟨ C.seal ★ (suc (suc zero))
              C.↦ C.unseal (suc (suc zero)) ★ ⟩)
            ⟨ ((＇ (suc zero)) !)
              C.↦ ((＇ (suc zero)) ？) ⟩)
            ⟨ C.seal ★ (suc zero)
              C.↦ C.unseal (suc zero) ★ ⟩)
            ⟨ ((＇ zero) !) C.↦ ((＇ zero) ？) ⟩)
          ($ (κℕ zero))))
      (↠-step
        (ξ-⟨⟩
          (pure-step
            (β-↦
              (((vI
                ⟨ C.seal ★ (suc (suc zero))
                  C.↦ C.unseal (suc (suc zero)) ★ ⟩)
                ⟨ ((＇ (suc zero)) !)
                  C.↦ ((＇ (suc zero)) ？) ⟩)
                ⟨ C.seal ★ (suc zero)
                  C.↦ C.unseal (suc zero) ★ ⟩)
              (($ (κℕ zero))
                ⟨ C.seal (‵ Types.`ℕ) zero ⟩))))
        (↠-step
          (ξ-⟨⟩
            (ξ-⟨⟩
              (pure-step
                (β-↦
                  ((vI
                    ⟨ C.seal ★ (suc (suc zero))
                      C.↦ C.unseal (suc (suc zero)) ★ ⟩)
                    ⟨ ((＇ (suc zero)) !)
                      C.↦ ((＇ (suc zero)) ？) ⟩)
                  ((($ (κℕ zero))
                    ⟨ C.seal (‵ Types.`ℕ) zero ⟩)
                    ⟨ (＇ zero) ! ⟩)))))
          (↠-step
            (ξ-⟨⟩
              (ξ-⟨⟩
                (ξ-⟨⟩
                  (pure-step
                    (β-↦
                      (vI
                        ⟨ C.seal ★ (suc (suc zero))
                          C.↦ C.unseal
                            (suc (suc zero)) ★ ⟩)
                      (((($ (κℕ zero))
                        ⟨ C.seal (‵ Types.`ℕ) zero ⟩)
                        ⟨ (＇ zero) ! ⟩)
                        ⟨ C.seal ★ (suc zero) ⟩))))))
            (↠-step
              (ξ-⟨⟩
                (ξ-⟨⟩
                  (ξ-⟨⟩
                    (ξ-⟨⟩
                      (pure-step
                        (β-↦ vI
                          ((((($ (κℕ zero))
                            ⟨ C.seal
                              (‵ Types.`ℕ) zero ⟩)
                            ⟨ (＇ zero) ! ⟩)
                            ⟨ C.seal ★ (suc zero) ⟩)
                            ⟨ (＇ (suc zero)) ! ⟩)))))))
              (↠-step
                (ξ-⟨⟩
                  (ξ-⟨⟩
                    (ξ-⟨⟩
                      (ξ-⟨⟩
                        (ξ-⟨⟩
                          (pure-step
                            (β
                              (((((($ (κℕ zero))
                                ⟨ C.seal
                                  (‵ Types.`ℕ) zero ⟩)
                                ⟨ (＇ zero) ! ⟩)
                                ⟨ C.seal ★ (suc zero) ⟩)
                                ⟨ (＇ (suc zero)) ! ⟩)
                                ⟨ C.seal ★
                                  (suc (suc zero)) ⟩))))))))
                ↠-refl)))))

  complex-cast-cancellation-trace :
    (((((((((($ (κℕ zero))
      ⟨ C.seal (‵ Types.`ℕ) zero ⟩)
      ⟨ (＇ zero) ! ⟩)
      ⟨ C.seal ★ (suc zero) ⟩)
      ⟨ (＇ (suc zero)) ! ⟩)
      ⟨ C.seal ★ (suc (suc zero)) ⟩)
      ⟨ C.unseal (suc (suc zero)) ★ ⟩)
      ⟨ (＇ (suc zero)) ？ ⟩)
      ⟨ C.unseal (suc zero) ★ ⟩)
      ⟨ (＇ zero) ？ ⟩)
      ⟨ C.unseal zero (‵ Types.`ℕ) ⟩
      —↠[ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]
    $ (κℕ zero)
  complex-cast-cancellation-trace =
    ↠-step
      (ξ-⟨⟩
        (ξ-⟨⟩
          (ξ-⟨⟩
            (ξ-⟨⟩
              (pure-step
                (seal-unseal
                  ((((($ (κℕ zero))
                    ⟨ C.seal (‵ Types.`ℕ) zero ⟩)
                    ⟨ (＇ zero) ! ⟩)
                    ⟨ C.seal ★ (suc zero) ⟩)
                    ⟨ (＇ (suc zero)) ! ⟩)))))))
      (↠-step
        (ξ-⟨⟩
          (ξ-⟨⟩
            (ξ-⟨⟩
              (pure-step
                (tag-untag-ok
                  (((($ (κℕ zero))
                    ⟨ C.seal (‵ Types.`ℕ) zero ⟩)
                    ⟨ (＇ zero) ! ⟩)
                    ⟨ C.seal ★ (suc zero) ⟩))))))
        (↠-step
          (ξ-⟨⟩
            (ξ-⟨⟩
              (pure-step
                (seal-unseal
                  ((($ (κℕ zero))
                    ⟨ C.seal (‵ Types.`ℕ) zero ⟩)
                    ⟨ (＇ zero) ! ⟩)))))
          (↠-step
            (ξ-⟨⟩
              (pure-step
                (tag-untag-ok
                  (($ (κℕ zero))
                    ⟨ C.seal (‵ Types.`ℕ) zero ⟩))))
            (↠-step
              (pure-step (seal-unseal ($ (κℕ zero))))
              ↠-refl))))

  complex-function-complete-trace :
    (((((I ⟨ inst-body-at (suc (suc zero)) ⟩)
      ⟨ gen-body-at (suc zero) ⟩)
      ⟨ inst-body-at (suc zero) ⟩)
      ⟨ gen-body-at zero ⟩) ⟨ reveal-ι ⟩)
      · $ (κℕ zero)
      —↠[
        keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷
        keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ []
      ]
    $ (κℕ zero)
  complex-function-complete-trace =
    ↠-trans
      complex-function-application-trace
      complex-cast-cancellation-trace

  simple-program-trace :
    (ν (‵ Types.`ℕ) (Λ I) reveal-ι) · $ (κℕ zero)
      —↠[
        bind (‵ Types.`ℕ) ∷ keep ∷
        keep ∷ keep ∷ keep ∷ []
      ]
    $ (κℕ zero)
  simple-program-trace =
    ↠-trans
      (·₁-↠ no•-$ simple-ν-function-trace)
      simple-function-application-trace

  complex-program-trace :
    (ν (‵ Types.`ℕ)
      (((((Λ I) ⟨ inst-cast ⟩) ⟨ gen-cast ⟩)
        ⟨ inst-cast ⟩) ⟨ gen-cast ⟩)
      reveal-ι) · $ (κℕ zero)
      —↠[
        keep ∷ bind ★ ∷ keep ∷
        keep ∷ bind ★ ∷ keep ∷
        bind (‵ Types.`ℕ) ∷ keep ∷
        keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷
        keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ []
      ]
    $ (κℕ zero)
  complex-program-trace =
    ↠-trans
      (·₁-↠ no•-$ complex-ν-function-trace)
      complex-function-complete-trace

  result-pι :
    ((zero ˣ⊑ˣ zero) ∷ [])
      ∣ suc zero
      ⊢ ‵ Types.`ℕ ⊑ ‵ Types.`ℕ
      ⊣ suc (suc (suc zero))
  result-pι =
    ⊑-lift∀ᵢ
      (⊑-target-lift-rightᵢ
        (⊑-target-lift-rightᵢ pι))

  example14-result-store :
    StoreImp ((zero ˣ⊑ˣ zero) ∷ [])
      (suc zero) (suc (suc (suc zero)))
  example14-result-store =
    store-matched zero (‵ Types.`ℕ)
      zero (‵ Types.`ℕ) result-pι ∷
    store-right (suc zero) ★ wf★ ∷
    store-right (suc (suc zero)) ★ wf★ ∷
    []

  example14-functionsᴿ :
    [] ∣ zero ∣ zero ∣ [] ∣ []
      ⊢ᴿ ν (‵ Types.`ℕ) (Λ I) reveal-ι
        ⊑
          ν (‵ Types.`ℕ)
            (((((Λ I) ⟨ inst-cast ⟩) ⟨ gen-cast ⟩)
              ⟨ inst-cast ⟩) ⟨ gen-cast ⟩)
            reveal-ι
      ⦂ (‵ Types.`ℕ ⇒ ‵ Types.`ℕ)
        ⊑ (‵ Types.`ℕ ⇒ ‵ Types.`ℕ)
      ∶ pι⇒ι
  example14-functionsᴿ =
    ν⊑νᴿ wfBase wfBase
      reveal-ι-conversion reveal-ι-conversion
      pι (⊑-lift∀ᵢ pι)
      lift-store-[] lift-ctx-[]
      two-round-tripsᴿ
      reveal-ι-replacement


cambridge26-example14-initialᴿ :
  [] ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿ
      (ν (‵ Types.`ℕ) (Λ I) reveal-ι) · $ (κℕ zero)
      ⊑
      (ν (‵ Types.`ℕ)
        (((((Λ I) ⟨ inst-cast ⟩) ⟨ gen-cast ⟩)
          ⟨ inst-cast ⟩) ⟨ gen-cast ⟩)
        reveal-ι) · $ (κℕ zero)
    ⦂ ‵ Types.`ℕ ⊑ ‵ Types.`ℕ ∶ pι
cambridge26-example14-initialᴿ =
  example14-functionsᴿ ·ᴿ κ⊑κᴿ


cambridge26-example14-squareᴿ :
  [] ∣ zero ∣ zero ∣ []
    ⊢ᴿ↠
      (ν (‵ Types.`ℕ) (Λ I) reveal-ι) · $ (κℕ zero)
      ⊑
      (ν (‵ Types.`ℕ)
        (((((Λ I) ⟨ inst-cast ⟩) ⟨ gen-cast ⟩)
          ⟨ inst-cast ⟩) ⟨ gen-cast ⟩)
        reveal-ι) · $ (κℕ zero)
    ⦂ ‵ Types.`ℕ ⊑ ‵ Types.`ℕ ∶ pι
cambridge26-example14-squareᴿ =
  record
    { sourceChanges =
        bind (‵ Types.`ℕ) ∷ keep ∷
        keep ∷ keep ∷ keep ∷ []
    ; targetChanges =
        keep ∷ bind ★ ∷ keep ∷
        keep ∷ bind ★ ∷ keep ∷
        bind (‵ Types.`ℕ) ∷ keep ∷
        keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷
        keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ []
    ; sourceResult = $ (κℕ zero)
    ; targetResult = $ (κℕ zero)
    ; resultCtx = (zero ˣ⊑ˣ zero) ∷ []
    ; resultLeftCtx = suc zero
    ; resultRightCtx = suc (suc (suc zero))
    ; sourceCtxResult = refl
    ; targetCtxResult = refl
    ; resultStore = example14-result-store
    ; sourceStoreResult = refl
    ; targetStoreResult = refl
    ; resultSourceType = ‵ Types.`ℕ
    ; resultTargetType = ‵ Types.`ℕ
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType =
        λ relation →
          ⊑-lift∀ᵢ
            (⊑-target-lift-rightᵢ
              (⊑-target-lift-rightᵢ relation))
    ; sourceReduction = simple-program-trace
    ; targetReduction = complex-program-trace
    ; resultImprecision = κ⊑κᴿ
    }
