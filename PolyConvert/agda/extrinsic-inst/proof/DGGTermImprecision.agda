module proof.DGGTermImprecision where

-- File Charter:
--   * Term-imprecision preservation infrastructure needed by the DGG proof.
--   * Owns weakening, term substitution, type instantiation, and fresh-seal
--     bridge obligations for `TermImprecision`.
--   * Intended as one independent worker-owned proof surface.

open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc; _≤_)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import Imprecision
open import Store
open import Terms
open import TermImprecision
open import Reduction
open import proof.PreservationTermSubst using
  ( Renameˣ-wt
  ; renameˣᵐ-wt
  ; substˣ-wt
  ; renameˣᵐ-value
  ; substˣᵐ-value
  ; wkImp-plains
  )
open import proof.DGGCommon

postulate
  wk-left-world-⊑ :
    ∀ {Ψˡ Ψˡ′ Ψʳ Ψʳ′ Σˡ Σˡ′ Σʳ Σʳ′ M M′ A B} →
    StoreWf 0 Ψˡ′ Σˡ′ →
    StoreWf 0 Ψʳ′ Σʳ′ →
    Ψˡ ≤ Ψˡ′ →
    Σˡ ⊆ˢ Σˡ′ →
    TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A B →
    TermRel Ψˡ′ Σˡ′ Ψʳ′ Σʳ′ M M′ A B

  fresh-seal-rename-⊑ :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ M M′ A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A B →
    ∃[ Ψ ] ∃[ Σ ] (StoreWf 0 Ψ Σ × TermRel Ψ Σ Ψ Σ M M′ A B)

replaceΓᴾ : (E : TPEnv) → PCtx (TPEnv.Δ E) (TPEnv.Ψ E) → TPEnv
replaceΓᴾ E Γ′ =
  ⟪ TPEnv.Δ E , TPEnv.Ψ E , TPEnv.store E , Γ′ ⟫

RightLookupᴾ :
  ∀ {Δ Ψ} → PCtx Δ Ψ → Var → Ty → Set
RightLookupᴾ {Δ} {Ψ} Γ x B =
  Σ[ A ∈ Ty ] Σ[ p ∈ Imp ]
    Σ[ p⊢ ∈ Ψ ∣ plains Δ [] ⊢ p ⦂ A ⊑ B ]
      Γ ∋ₚ x ⦂ (A , B , p , p⊢)

lookup-right-inv :
  ∀ {Δ Ψ Γ x B} →
  rightCtx {Δ} {Ψ} Γ ∋ x ⦂ B →
  RightLookupᴾ Γ x B
lookup-right-inv {Γ = (A , B , p , p⊢) ∷ Γ} Z =
  A , p , p⊢ , Zₚ
lookup-right-inv {Γ = P ∷ Γ} (S h) with lookup-right-inv h
lookup-right-inv {Γ = P ∷ Γ} (S h) | A , p , p⊢ , hₚ =
  A , p , p⊢ , Sₚ hₚ

lookup-⇑ᵗᴾ :
  ∀ {Δ Ψ Γ x A B p p⊢} →
  Γ ∋ₚ x ⦂ (A , B , p , p⊢) →
  ⇑ᵗᴾ {Δ} {Ψ} Γ ∋ₚ x ⦂
    (⇑ᵗ A , ⇑ᵗ B , renameImp suc p , wkImp-plains zero p⊢)
lookup-⇑ᵗᴾ Zₚ = Zₚ
lookup-⇑ᵗᴾ (Sₚ h) = Sₚ (lookup-⇑ᵗᴾ h)

⇑ᵗᴾ-un∋ :
  ∀ {Δ Ψ Γ x P} →
  ⇑ᵗᴾ {Δ} {Ψ} Γ ∋ₚ x ⦂ P →
  Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Σ[ p ∈ Imp ]
    Σ[ p⊢ ∈ Ψ ∣ plains Δ [] ⊢ p ⦂ A ⊑ B ]
      (P ≡ (⇑ᵗ A , ⇑ᵗ B , renameImp suc p , wkImp-plains zero p⊢) ×
       Γ ∋ₚ x ⦂ (A , B , p , p⊢))
⇑ᵗᴾ-un∋ {Γ = (A , B , p , p⊢) ∷ Γ} Zₚ =
  A , B , p , p⊢ , refl , Zₚ
⇑ᵗᴾ-un∋ {Γ = P ∷ Γ} (Sₚ h) with ⇑ᵗᴾ-un∋ h
⇑ᵗᴾ-un∋ {Γ = P ∷ Γ} (Sₚ h) | A , B , p , p⊢ , eq , h′ =
  A , B , p , p⊢ , eq , Sₚ h′

map-lookup-⇑ᵗᴾ :
  ∀ {Δ Ψ} {Γ Γ′ : PCtx Δ Ψ} {ρ : Renameˣ} {x : Var}
    {P : Prec (suc Δ) Ψ} →
  (∀ {x A B p p⊢} →
    Γ ∋ₚ x ⦂ (A , B , p , p⊢) →
    Γ′ ∋ₚ ρ x ⦂ (A , B , p , p⊢)) →
  ⇑ᵗᴾ {Δ} {Ψ} Γ ∋ₚ x ⦂ P →
  ⇑ᵗᴾ Γ′ ∋ₚ ρ x ⦂ P
map-lookup-⇑ᵗᴾ hρ h with ⇑ᵗᴾ-un∋ h
map-lookup-⇑ᵗᴾ hρ h | A , B , p , p⊢ , refl , h′ =
  lookup-⇑ᵗᴾ (hρ h′)

renameᴾ-right-wt :
  ∀ {E} {Γ′ : PCtx (TPEnv.Δ E) (TPEnv.Ψ E)} {ρ : Renameˣ} →
  (∀ {x A B p p⊢} →
    TPEnv.Γ E ∋ₚ x ⦂ (A , B , p , p⊢) →
    Γ′ ∋ₚ ρ x ⦂ (A , B , p , p⊢)) →
  Renameˣ-wt (rightCtx (TPEnv.Γ E)) (rightCtx Γ′) ρ
renameᴾ-right-wt hρ h with lookup-right-inv h
renameᴾ-right-wt hρ h | A , p , p⊢ , hₚ = lookup-right (hρ hₚ)

extᴾ-map :
  ∀ {Δ Ψ} {Γ Γ′ : PCtx Δ Ψ} {ρ : Renameˣ} {A A′ : Ty} {p : Imp}
    {p⊢ : Ψ ∣ plains Δ [] ⊢ p ⦂ A ⊑ A′} →
  (∀ {x B B′ q q⊢} →
    Γ ∋ₚ x ⦂ (B , B′ , q , q⊢) →
    Γ′ ∋ₚ ρ x ⦂ (B , B′ , q , q⊢)) →
  ∀ {x B B′ q q⊢} →
  ((A , A′ , p , p⊢) ∷ Γ) ∋ₚ x ⦂ (B , B′ , q , q⊢) →
  ((A , A′ , p , p⊢) ∷ Γ′) ∋ₚ extʳ ρ x ⦂ (B , B′ , q , q⊢)
extᴾ-map hρ Zₚ = Zₚ
extᴾ-map hρ (Sₚ h) = Sₚ (hρ h)

renameˣ-⊑ :
  ∀ {E} {Γ′ : PCtx (TPEnv.Δ E) (TPEnv.Ψ E)}
    {ρ : Renameˣ} {M M′ : Term} {A B : Ty} →
  (∀ {x A B p p⊢} →
    TPEnv.Γ E ∋ₚ x ⦂ (A , B , p , p⊢) →
    Γ′ ∋ₚ ρ x ⦂ (A , B , p , p⊢)) →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  replaceΓᴾ E Γ′ ⊢ renameˣᵐ ρ M ⊑ renameˣᵐ ρ M′ ⦂ A ⊑ B
renameˣ-⊑ hρ (⊑` h) = ⊑` (hρ h)
renameˣ-⊑ hρ
  (⊑ƛ {pA = pA} {pB = pB} {pA⊢ = pA⊢} {pB⊢ = pB⊢} hA hA′ rel) =
  ⊑ƛ {pA = pA} {pB = pB} {pA⊢ = pA⊢} {pB⊢ = pB⊢}
    hA hA′ (renameˣ-⊑ (extᴾ-map hρ) rel)
renameˣ-⊑ hρ (⊑· relL relM) =
  ⊑· (renameˣ-⊑ hρ relL) (renameˣ-⊑ hρ relM)
renameˣ-⊑ hρ (⊑Λ vM vM′ rel) =
  ⊑Λ
    (renameˣᵐ-value _ vM)
    (renameˣᵐ-value _ vM′)
    (renameˣ-⊑ (map-lookup-⇑ᵗᴾ hρ) rel)
renameˣ-⊑ hρ (⊑⦂∀ rel wfA wfB wfT pT⊢) =
  ⊑⦂∀ (renameˣ-⊑ hρ rel) wfA wfB wfT pT⊢
renameˣ-⊑ hρ (⊑⦂∀-ν rel wfA wfT pT⊢) =
  ⊑⦂∀-ν (renameˣ-⊑ hρ rel) wfA wfT pT⊢
renameˣ-⊑ hρ ⊑$ = ⊑$
renameˣ-⊑ hρ (⊑⊕ relL relM) =
  ⊑⊕ (renameˣ-⊑ hρ relL) (renameˣ-⊑ hρ relM)
renameˣ-⊑ hρ (⊑⇑ rel p⊢ p′⊢ pB⊢) =
  ⊑⇑ (renameˣ-⊑ hρ rel) p⊢ p′⊢ pB⊢
renameˣ-⊑ hρ (⊑⇑L rel p⊢ pB⊢) =
  ⊑⇑L (renameˣ-⊑ hρ rel) p⊢ pB⊢
renameˣ-⊑ hρ (⊑⇑R rel p′⊢ pB⊢) =
  ⊑⇑R (renameˣ-⊑ hρ rel) p′⊢ pB⊢
renameˣ-⊑ hρ (⊑⇓ rel p⊢ p′⊢ pB⊢) =
  ⊑⇓ (renameˣ-⊑ hρ rel) p⊢ p′⊢ pB⊢
renameˣ-⊑ hρ (⊑⇓L rel p⊢ pB⊢) =
  ⊑⇓L (renameˣ-⊑ hρ rel) p⊢ pB⊢
renameˣ-⊑ hρ (⊑⇓R rel p′⊢ pB⊢) =
  ⊑⇓R (renameˣ-⊑ hρ rel) p′⊢ pB⊢
renameˣ-⊑ hρ (⊑↑ rel c⊢ c′⊢ pB⊢) =
  ⊑↑ (renameˣ-⊑ hρ rel) c⊢ c′⊢ pB⊢
renameˣ-⊑ hρ (⊑↑L rel c⊢ pB⊢) =
  ⊑↑L (renameˣ-⊑ hρ rel) c⊢ pB⊢
renameˣ-⊑ hρ (⊑↑R rel c′⊢ pB⊢) =
  ⊑↑R (renameˣ-⊑ hρ rel) c′⊢ pB⊢
renameˣ-⊑ hρ (⊑↓ rel c⊢ c′⊢ pB⊢) =
  ⊑↓ (renameˣ-⊑ hρ rel) c⊢ c′⊢ pB⊢
renameˣ-⊑ hρ (⊑↓L rel c⊢ pB⊢) =
  ⊑↓L (renameˣ-⊑ hρ rel) c⊢ pB⊢
renameˣ-⊑ hρ (⊑↓R rel c′⊢ pB⊢) =
  ⊑↓R (renameˣ-⊑ hρ rel) c′⊢ pB⊢
renameˣ-⊑ {E = E} {Γ′ = Γ′} {ρ = ρ} hρ
  (⊑blameR {p = p} {ℓ = ℓ} hM p⊢) =
  ⊑blameR {p = p} {ℓ = ℓ}
    (renameˣᵐ-wt ρ (renameᴾ-right-wt {E = E} {Γ′ = Γ′} hρ) hM) p⊢

Substᴾ : (E : TPEnv) → PCtx (TPEnv.Δ E) (TPEnv.Ψ E) →
  Substˣ → Substˣ → Set
Substᴾ E Γ′ σ σ′ =
  ∀ {x A B p p⊢} →
  TPEnv.Γ E ∋ₚ x ⦂ (A , B , p , p⊢) →
  replaceΓᴾ E Γ′ ⊢ σ x ⊑ σ′ x ⦂ A ⊑ B

substᴾ-right-wt :
  ∀ {E Γ′ σ σ′} →
  Substᴾ E Γ′ σ σ′ →
  ∀ {A x} →
  rightCtx (TPEnv.Γ E) ∋ x ⦂ A →
  TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣ rightCtx Γ′ ⊢ σ′ x ⦂ A
substᴾ-right-wt hσ h with lookup-right-inv h
substᴾ-right-wt hσ h | A , p , p⊢ , hₚ = ⊑-right-typed (hσ hₚ)

extˢˣᴾ :
  ∀ {E Γ′ σ σ′ A B p p⊢} →
  Substᴾ E Γ′ σ σ′ →
  Substᴾ (extendᴾ E (A , B , p , p⊢)) ((A , B , p , p⊢) ∷ Γ′)
    (extˢˣ σ) (extˢˣ σ′)
extˢˣᴾ hσ Zₚ = ⊑` Zₚ
extˢˣᴾ hσ (Sₚ h) = renameˣ-⊑ (λ q → Sₚ q) (hσ h)

postulate
  renameᵗ-suc-⊑ :
    ∀ {E M M′ A B} →
    E ⊢ M ⊑ M′ ⦂ A ⊑ B →
    ⇑ᵗᴱ E ⊢ renameᵗᵐ suc M ⊑ renameᵗᵐ suc M′ ⦂ ⇑ᵗ A ⊑ ⇑ᵗ B

↑ᵗᵐᴾ :
  ∀ {E Γ′ σ σ′} →
  Substᴾ E Γ′ σ σ′ →
  Substᴾ (⇑ᵗᴱ E) (⇑ᵗᴾ Γ′) (↑ᵗᵐ σ) (↑ᵗᵐ σ′)
↑ᵗᵐᴾ {E = ⟪ Δ , Ψ , Σ , [] ⟫} hσ ()
↑ᵗᵐᴾ {E = ⟪ Δ , Ψ , Σ , (A , B , p , p⊢) ∷ Γ ⟫}
  hσ Zₚ =
  renameᵗ-suc-⊑ (hσ Zₚ)
↑ᵗᵐᴾ {E = ⟪ Δ , Ψ , Σ , P ∷ Γ ⟫} hσ (Sₚ h) =
  ↑ᵗᵐᴾ {E = ⟪ Δ , Ψ , Σ , Γ ⟫} (λ q → hσ (Sₚ q)) h

substᴾ-⊑ :
  ∀ {E Γ′ σ σ′ M M′ A B} →
  Substᴾ E Γ′ σ σ′ →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  replaceΓᴾ E Γ′ ⊢ substˣᵐ σ M ⊑ substˣᵐ σ′ M′ ⦂ A ⊑ B
substᴾ-⊑ hσ (⊑` h) = hσ h
substᴾ-⊑ hσ
  (⊑ƛ {pA = pA} {pB = pB} {pA⊢ = pA⊢} {pB⊢ = pB⊢} hA hA′ rel) =
  ⊑ƛ {pA = pA} {pB = pB} {pA⊢ = pA⊢} {pB⊢ = pB⊢}
    hA hA′ (substᴾ-⊑ (extˢˣᴾ hσ) rel)
substᴾ-⊑ hσ (⊑· relL relM) =
  ⊑· (substᴾ-⊑ hσ relL) (substᴾ-⊑ hσ relM)
substᴾ-⊑ hσ (⊑Λ vM vM′ rel) =
  ⊑Λ
    (substˣᵐ-value _ vM)
    (substˣᵐ-value _ vM′)
    (substᴾ-⊑ (↑ᵗᵐᴾ hσ) rel)
substᴾ-⊑ hσ (⊑⦂∀ rel wfA wfB wfT pT⊢) =
  ⊑⦂∀ (substᴾ-⊑ hσ rel) wfA wfB wfT pT⊢
substᴾ-⊑ hσ (⊑⦂∀-ν rel wfA wfT pT⊢) =
  ⊑⦂∀-ν (substᴾ-⊑ hσ rel) wfA wfT pT⊢
substᴾ-⊑ hσ ⊑$ = ⊑$
substᴾ-⊑ hσ (⊑⊕ relL relM) =
  ⊑⊕ (substᴾ-⊑ hσ relL) (substᴾ-⊑ hσ relM)
substᴾ-⊑ hσ (⊑⇑ rel p⊢ p′⊢ pB⊢) =
  ⊑⇑ (substᴾ-⊑ hσ rel) p⊢ p′⊢ pB⊢
substᴾ-⊑ hσ (⊑⇑L rel p⊢ pB⊢) =
  ⊑⇑L (substᴾ-⊑ hσ rel) p⊢ pB⊢
substᴾ-⊑ hσ (⊑⇑R rel p′⊢ pB⊢) =
  ⊑⇑R (substᴾ-⊑ hσ rel) p′⊢ pB⊢
substᴾ-⊑ hσ (⊑⇓ rel p⊢ p′⊢ pB⊢) =
  ⊑⇓ (substᴾ-⊑ hσ rel) p⊢ p′⊢ pB⊢
substᴾ-⊑ hσ (⊑⇓L rel p⊢ pB⊢) =
  ⊑⇓L (substᴾ-⊑ hσ rel) p⊢ pB⊢
substᴾ-⊑ hσ (⊑⇓R rel p′⊢ pB⊢) =
  ⊑⇓R (substᴾ-⊑ hσ rel) p′⊢ pB⊢
substᴾ-⊑ hσ (⊑↑ rel c⊢ c′⊢ pB⊢) =
  ⊑↑ (substᴾ-⊑ hσ rel) c⊢ c′⊢ pB⊢
substᴾ-⊑ hσ (⊑↑L rel c⊢ pB⊢) =
  ⊑↑L (substᴾ-⊑ hσ rel) c⊢ pB⊢
substᴾ-⊑ hσ (⊑↑R rel c′⊢ pB⊢) =
  ⊑↑R (substᴾ-⊑ hσ rel) c′⊢ pB⊢
substᴾ-⊑ hσ (⊑↓ rel c⊢ c′⊢ pB⊢) =
  ⊑↓ (substᴾ-⊑ hσ rel) c⊢ c′⊢ pB⊢
substᴾ-⊑ hσ (⊑↓L rel c⊢ pB⊢) =
  ⊑↓L (substᴾ-⊑ hσ rel) c⊢ pB⊢
substᴾ-⊑ hσ (⊑↓R rel c′⊢ pB⊢) =
  ⊑↓R (substᴾ-⊑ hσ rel) c′⊢ pB⊢
substᴾ-⊑ hσ (⊑blameR hM p⊢) =
  ⊑blameR (substˣ-wt _ (substᴾ-right-wt hσ) hM) p⊢

singleSubstᴾ :
  ∀ {E A A′ W W′ p p⊢} →
  E ⊢ W ⊑ W′ ⦂ A ⊑ A′ →
  Substᴾ (extendᴾ E (A , A′ , p , p⊢)) (TPEnv.Γ E)
    (singleEnv W) (singleEnv W′)
singleSubstᴾ W⊑W′ Zₚ = W⊑W′
singleSubstᴾ W⊑W′ (Sₚ h) = ⊑` h

subst-⊑ :
  ∀ {Ψ Σ M M′ N N′ A A′ B B′ p p⊢} →
  TermRel Ψ Σ Ψ Σ N N′ A A′ →
  ⟪ 0 , Ψ , Σ , (A , A′ , p , p⊢) ∷ [] ⟫ ⊢ M ⊑ M′ ⦂ B ⊑ B′ →
  TermRel Ψ Σ Ψ Σ (M [ N ]) (M′ [ N′ ]) B B′
subst-⊑ N⊑N′ rel = substᴾ-⊑ (singleSubstᴾ N⊑N′) rel

postulate
  tysubst-body-⊑ :
    ∀ {Ψ Σ M M′ A B T} →
    WfTy 0 Ψ T →
    ⟪ 1 , Ψ , ⟰ᵗ Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ A ⊑ B →
    TermRel Ψ Σ Ψ Σ (M [ T ]ᵀ) (M′ [ T ]ᵀ) (A [ T ]ᵗ) (B [ T ]ᵗ)

tysubst-⊑ :
  ∀ {Ψ Σ M M′ A B T} →
  WfTy 0 Ψ T →
  TermRel Ψ Σ Ψ Σ (Λ M) (Λ M′) (`∀ A) (`∀ B) →
  TermRel Ψ Σ Ψ Σ (M [ T ]ᵀ) (M′ [ T ]ᵀ) (A [ T ]ᵗ) (B [ T ]ᵗ)
tysubst-⊑ hT (⊑Λ vM vM′ rel) = tysubst-body-⊑ hT rel
