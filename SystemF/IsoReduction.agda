module IsoReduction where

open import Relation.Binary.PropositionalEquality
  using (_≡_)

open import TermsIso
  using (IntrinsicWT; eraseTerm; toExtrinsic; extrinsicTerm)
open import TypesIso using (erase)

open import intrinsic.Types as I
open import intrinsic.Ctx as IC
open import intrinsic.Terms as IT
open import intrinsic.Reduction as IR

open import extrinsic.SystemF as ET

postulate
  erase-β-subst : ∀ {Δ} {Γ : IC.Ctx Δ} {A B : I.Type Δ}
    (N : IT._;_⊢_ Δ (Γ IC., A) B)
    (M : IT._;_⊢_ Δ Γ A)
    → eraseTerm (IT.subst (M IT.• IT.id) N) ≡ eraseTerm N ET.[ eraseTerm M ]

postulate
  erase-[]ᵀ : ∀ {Δ} {Γ : IC.Ctx Δ} {A : I.Type (Δ I.,α)}
    (N : IT._;_⊢_ (Δ I.,α) (IC.⇑ᶜ Γ) A)
    (B : I.Type Δ)
    → eraseTerm (N IT.[ B ]ᵀ) ≡ eraseTerm N ET.[ erase B ]ᵀ

eraseValue : ∀ {Δ} {Γ : IC.Ctx Δ} {A : I.Type Δ} {V : IT._;_⊢_ Δ Γ A}
  → IR.Value V
  → ET.Value (eraseTerm V)
eraseValue IR.V-zero = ET.vZero
eraseValue (IR.V-suc vV) = ET.vSuc (eraseValue vV)
eraseValue IR.V-true = ET.vTrue
eraseValue IR.V-false = ET.vFalse
eraseValue IR.V-ƛ = ET.vLam
eraseValue IR.V-Λ = ET.vTlam

erase-—→ : ∀ {Δ} {Γ : IC.Ctx Δ} {A : I.Type Δ}
  {M N : IT._;_⊢_ Δ Γ A}
  → M IR.—→ N
  → eraseTerm M ET.—→ eraseTerm N
erase-—→ (IR.ξ-suc M—→N) = ET.ξ-suc (erase-—→ M—→N)
erase-—→ (IR.ξ-case-nat L—→L′) = ET.ξ-case (erase-—→ L—→L′)
erase-—→ (IR.ξ-if L—→L′) = ET.ξ-if (erase-—→ L—→L′)
erase-—→ (IR.ξ-·₁ L—→L′) = ET.ξ-·₁ (erase-—→ L—→L′)
erase-—→ (IR.ξ-·₂ vV M—→M′) = ET.ξ-·₂ (eraseValue vV) (erase-—→ M—→M′)
erase-—→ (IR.ξ-∙ M—→M′) = ET.ξ-·[] (erase-—→ M—→M′)
erase-—→ {N = N} (IR.β-ƛ {N = N₁} {W = W} vW)
  rewrite erase-β-subst N₁ W =
  ET.β-ƛ (eraseValue vW)
erase-—→ IR.β-zero = ET.β-zero
erase-—→ {N = N} (IR.β-suc {V = V} {N = N₁} vV)
  rewrite erase-β-subst N₁ V =
  ET.β-suc (eraseValue vV)
erase-—→ IR.β-true = ET.β-true
erase-—→ IR.β-false = ET.β-false
erase-—→ {M = IT._∙_ {A = A} (IT.Λ_ N) B} IR.β-Λ
  rewrite erase-[]ᵀ N B =
  ET.β-Λ {A = erase B}

erase-—↠ : ∀ {Δ} {Γ : IC.Ctx Δ} {A : I.Type Δ}
  {M N : IT._;_⊢_ Δ Γ A}
  → M IR.—↠ N
  → eraseTerm M ET.—↠ eraseTerm N
erase-—↠ (M IR.∎) = eraseTerm M ET.∎
erase-—↠ (L IR.—→⟨ L—→M ⟩ M—↠N) =
  eraseTerm L ET.—→⟨ erase-—→ L—→M ⟩ erase-—↠ M—↠N

toExtrinsic-respects-—→ : ∀ {Δ} {Γ : IC.Ctx Δ} {A : I.Type Δ}
  {m n : IntrinsicWT Γ A}
  → m IR.—→ n
  → extrinsicTerm (toExtrinsic m) ET.—→ extrinsicTerm (toExtrinsic n)
toExtrinsic-respects-—→ = erase-—→

toExtrinsic-respects-—↠ : ∀ {Δ} {Γ : IC.Ctx Δ} {A : I.Type Δ}
  {m n : IntrinsicWT Γ A}
  → m IR.—↠ n
  → extrinsicTerm (toExtrinsic m) ET.—↠ extrinsicTerm (toExtrinsic n)
toExtrinsic-respects-—↠ = erase-—↠
