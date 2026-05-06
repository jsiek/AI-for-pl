module proof.DGGTermImprecision where

-- File Charter:
--   * Term-imprecision preservation infrastructure needed by the DGG proof.
--   * Owns weakening, term substitution, type instantiation, and fresh-seal
--     bridge obligations for `TermImprecision`.
--   * Intended as one independent worker-owned proof surface.

open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc; _+_; _≤_)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; subst; sym; trans)

open import Types
open import Imprecision
open import Store
open import Conversion
open import Terms
open import TermImprecision
open import Reduction
open import proof.PreservationTermSubst using
  ( Renameˣ-wt
  ; cong₃
  ; raiseWfPlus
  ; renSubst-raise-wf
  ; substᵗ-ren
  ; substStoreᵗ-ren
  ; renameᵗ-[]ᵗ
  ; renameStoreᵗ-raise-⟰ᵗ
  ; renameˣᵐ-wt
  ; renameᵗᵐ-cong
  ; renameᵗᵐ-raise-wt
  ; renameᵗᵐ-value
  ; substˣ-wt
  ; renameˣᵐ-value
  ; substˣᵐ-value
  ; wkImp-plains
  )
open import proof.PreservationBetaRevealConceal using
  (cong-⊢↑; cong-⊢↓; subst↑-wt; subst↓-wt)
open import proof.PreservationBetaUpNu using
  (cong-⊢⊑-raw; raiseVarFrom; raise-ext; rename-raise-⇑ᵗ)
open import proof.PreservationWkImp using (wk-⊑; wk-⊒)
open import proof.PreservationWkConv using (⟰ᵗ-⊆ˢ; wk-conv↑; wk-conv↓)
open import proof.PreservationWkTerm using (wk-term)
open import proof.TypeProperties using (WfTy-weakenˢ)
open import proof.DGGCommon

Conv↑Wt : TyCtx → SealCtx → Store → Conv↑ → Ty → Ty → Set
Conv↑Wt Δ Ψ Σ c A B = Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↑ˢ B

Conv↓Wt : TyCtx → SealCtx → Store → Conv↓ → Ty → Ty → Set
Conv↓Wt Δ Ψ Σ c A B = Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↓ˢ B

postulate
  fresh-seal-rename-⊑ :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ M M′ A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    ⟪ 0 , Ψˡ , Σˡ , Ψʳ , Σʳ , [] ⟫ ⊢ M ⊑ M′ ⦂ A ⊑ B →
    ∃[ Ψ ] ∃[ Σ ]
      (StoreWf 0 Ψ Σ ×
       ⟪ 0 , Ψ , Σ , Ψ , Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ A ⊑ B)

replaceΓᴾ : (E : TPEnv) → PCtx (TPEnv.Δ E) (TPEnv.Ψ E) → TPEnv
replaceΓᴾ E Γ′ =
  ⟪ TPEnv.Δ E , TPEnv.Ψ E , TPEnv.store E ,
    TPEnv.Ψʳ E , TPEnv.storeʳ E , Γ′ ⟫

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

renameˣᵐ-id :
  (ρ : Renameˣ) →
  ((x : Var) → ρ x ≡ x) →
  (M : Term) →
  renameˣᵐ ρ M ≡ M
renameˣᵐ-id ρ hρ (` x) = cong `_ (hρ x)
renameˣᵐ-id ρ hρ (ƛ A ⇒ M) =
  cong (ƛ A ⇒_) (renameˣᵐ-id (extʳ ρ) h-ext M)
  where
    h-ext : (x : Var) → extʳ ρ x ≡ x
    h-ext zero = refl
    h-ext (suc x) = cong suc (hρ x)
renameˣᵐ-id ρ hρ (L · M) =
  cong₂ _·_ (renameˣᵐ-id ρ hρ L) (renameˣᵐ-id ρ hρ M)
renameˣᵐ-id ρ hρ (Λ M) = cong Λ_ (renameˣᵐ-id ρ hρ M)
renameˣᵐ-id ρ hρ (M ⦂∀ B [ T ]) =
  cong (λ N → N ⦂∀ B [ T ]) (renameˣᵐ-id ρ hρ M)
renameˣᵐ-id ρ hρ ($ κ) = refl
renameˣᵐ-id ρ hρ (L ⊕[ op ] M) =
  cong₃ _⊕[_]_ (renameˣᵐ-id ρ hρ L) refl (renameˣᵐ-id ρ hρ M)
renameˣᵐ-id ρ hρ (M ⇑ p) = cong (_⇑ p) (renameˣᵐ-id ρ hρ M)
renameˣᵐ-id ρ hρ (M ⇓ p) = cong (_⇓ p) (renameˣᵐ-id ρ hρ M)
renameˣᵐ-id ρ hρ (M ↑ c) = cong (_↑ c) (renameˣᵐ-id ρ hρ M)
renameˣᵐ-id ρ hρ (M ↓ c) = cong (_↓ c) (renameˣᵐ-id ρ hρ M)
renameˣᵐ-id ρ hρ (blame ℓ) = refl

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
renameˣ-⊑ hρ (⊑↓ rel c⊢ c′⊢ pB⊢) =
  ⊑↓ (renameˣ-⊑ hρ rel) c⊢ c′⊢ pB⊢
renameˣ-⊑ {E = E} {Γ′ = Γ′} {ρ = ρ} hρ
  (⊑blameL {p = p} {ℓ = ℓ} hM p⊢) =
  ⊑blameL {p = p} {ℓ = ℓ}
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

RenameᵗPCtxMap :
  ∀ k {Δ : TyCtx} {Ψ : SealCtx} →
  PCtx (k + Δ) Ψ →
  PCtx (suc (k + Δ)) Ψ →
  Set
RenameᵗPCtxMap k {Δ} {Ψ} Γ Γ′ =
  ∀ {x A B p p⊢} →
  Γ ∋ₚ x ⦂ (A , B , p , p⊢) →
  Σ[ A′ ∈ Ty ] Σ[ B′ ∈ Ty ] Σ[ p′ ∈ Imp ]
    Σ[ p⊢′ ∈ Ψ ∣ plains (suc (k + Δ)) [] ⊢ p′ ⦂ A′ ⊑ B′ ]
      ( A′ ≡ renameᵗ (raiseVarFrom k) A ×
        B′ ≡ renameᵗ (raiseVarFrom k) B ×
        Γ′ ∋ₚ x ⦂ (A′ , B′ , p′ , p⊢′) )

renameᵗPCtxMap-⇑ᵗᴾ :
  ∀ k {Δ Ψ} {Γ : PCtx (k + Δ) Ψ}
    {Γ′ : PCtx (suc (k + Δ)) Ψ} →
  RenameᵗPCtxMap k Γ Γ′ →
  RenameᵗPCtxMap (suc k) (⇑ᵗᴾ Γ) (⇑ᵗᴾ Γ′)
renameᵗPCtxMap-⇑ᵗᴾ k hΓ h with ⇑ᵗᴾ-un∋ h
renameᵗPCtxMap-⇑ᵗᴾ k hΓ h | A , B , p , p⊢ , refl , h′
  with hΓ h′
renameᵗPCtxMap-⇑ᵗᴾ k hΓ h | A , B , p , p⊢ , refl , h′
  | A′ , B′ , p′ , p⊢′ , eqA , eqB , h″ =
  ⇑ᵗ A′ , ⇑ᵗ B′ , renameImp suc p′ , wkImp-plains zero p⊢′ ,
  trans (cong ⇑ᵗ eqA) (sym (rename-raise-⇑ᵗ k A)) ,
  trans (cong ⇑ᵗ eqB) (sym (rename-raise-⇑ᵗ k B)) ,
  lookup-⇑ᵗᴾ h″

renameᵗPCtxMap-ext :
  ∀ k {Δ Ψ} {Γ : PCtx (k + Δ) Ψ}
    {Γ′ : PCtx (suc (k + Δ)) Ψ} {A A′ : Ty} {p : Imp}
    {p⊢ : Ψ ∣ plains (k + Δ) [] ⊢ p ⦂ A ⊑ A′} →
  RenameᵗPCtxMap k Γ Γ′ →
  RenameᵗPCtxMap k
    ((A , A′ , p , p⊢) ∷ Γ)
    ( ( renameᵗ (raiseVarFrom k) A
      , renameᵗ (raiseVarFrom k) A′
      , renameImp (raiseVarFrom k) p
      , wkImp-plains k p⊢ )
      ∷ Γ′ )
renameᵗPCtxMap-ext k hΓ {A = A} {B = B} {p = p} {p⊢ = p⊢} Zₚ =
  renameᵗ (raiseVarFrom k) A ,
  renameᵗ (raiseVarFrom k) B ,
  renameImp (raiseVarFrom k) p ,
  wkImp-plains k p⊢ ,
  refl , refl , Zₚ
renameᵗPCtxMap-ext k hΓ (Sₚ h) with hΓ h
renameᵗPCtxMap-ext k hΓ (Sₚ h)
  | A′ , B′ , p′ , p⊢′ , eqA , eqB , h′ =
  A′ , B′ , p′ , p⊢′ , eqA , eqB , Sₚ h′

renameᵗPCtxMap-⇑ᵗᴾ-zero :
  ∀ {Δ Ψ} {Γ : PCtx Δ Ψ} →
  RenameᵗPCtxMap zero Γ (⇑ᵗᴾ Γ)
renameᵗPCtxMap-⇑ᵗᴾ-zero {Γ = []} ()
renameᵗPCtxMap-⇑ᵗᴾ-zero {Γ = (A , B , p , p⊢) ∷ Γ} Zₚ =
  ⇑ᵗ A , ⇑ᵗ B , renameImp suc p , wkImp-plains zero p⊢ ,
  refl , refl , Zₚ
renameᵗPCtxMap-⇑ᵗᴾ-zero {Γ = P ∷ Γ} (Sₚ h)
  with renameᵗPCtxMap-⇑ᵗᴾ-zero {Γ = Γ} h
renameᵗPCtxMap-⇑ᵗᴾ-zero {Γ = P ∷ Γ} (Sₚ h)
  | A′ , B′ , p′ , p⊢′ , eqA , eqB , h′ =
  A′ , B′ , p′ , p⊢′ , eqA , eqB , Sₚ h′

unmap-right-renameᵗᴾ :
  ∀ k {Δ Ψ} {Γ : PCtx (k + Δ) Ψ} {x C} →
  Data.List.map (renameᵗ (raiseVarFrom k)) (rightCtx Γ) ∋ x ⦂ C →
  Σ[ B ∈ Ty ] Σ[ A ∈ Ty ] Σ[ p ∈ Imp ]
    Σ[ p⊢ ∈ Ψ ∣ plains (k + Δ) [] ⊢ p ⦂ A ⊑ B ]
      (C ≡ renameᵗ (raiseVarFrom k) B ×
       Γ ∋ₚ x ⦂ (A , B , p , p⊢))
unmap-right-renameᵗᴾ k {Γ = (A , B , p , p⊢) ∷ Γ} Z =
  B , A , p , p⊢ , refl , Zₚ
unmap-right-renameᵗᴾ k {Γ = P ∷ Γ} (S h)
  with unmap-right-renameᵗᴾ k {Γ = Γ} h
unmap-right-renameᵗᴾ k {Γ = P ∷ Γ} (S h)
  | B , A , p , p⊢ , eq , h′ =
  B , A , p , p⊢ , eq , Sₚ h′

renameᵗPCtxMap-right-wt :
  ∀ k {Δ Ψ} {Γ : PCtx (k + Δ) Ψ}
    {Γ′ : PCtx (suc (k + Δ)) Ψ} →
  RenameᵗPCtxMap k Γ Γ′ →
  Renameˣ-wt
    (Data.List.map (renameᵗ (raiseVarFrom k)) (rightCtx Γ))
    (rightCtx Γ′)
    (λ x → x)
renameᵗPCtxMap-right-wt k hΓ h
  with unmap-right-renameᵗᴾ k h
renameᵗPCtxMap-right-wt k hΓ h
  | B , A , p , p⊢ , refl , hₚ with hΓ hₚ
renameᵗPCtxMap-right-wt k hΓ h
  | B , A , p , p⊢ , refl , hₚ
  | A′ , B′ , p′ , p⊢′ , eqA , eqB , h′ =
  subst (λ T → rightCtx _ ∋ _ ⦂ T) eqB (lookup-right h′)

rename↑-raise-wt :
  ∀ k {Δ Ψ}{Σ Σ′ : Store}{c A B} →
  Σ′ ≡ renameStoreᵗ (raiseVarFrom k) Σ →
  Conv↑Wt (k + Δ) Ψ Σ c A B →
  Conv↑Wt (suc (k + Δ)) Ψ Σ′
    (subst↑ (λ X → ＇ raiseVarFrom k X) c)
    (renameᵗ (raiseVarFrom k) A)
    (renameᵗ (raiseVarFrom k) B)
rename↑-raise-wt k {Σ = Σ} eqΣ c⊢ =
  cong-⊢↑
    (trans (substStoreᵗ-ren (raiseVarFrom k) Σ) (sym eqΣ))
    refl
    (substᵗ-ren (raiseVarFrom k) _)
    (substᵗ-ren (raiseVarFrom k) _)
    (subst↑-wt (renSubst-raise-wf k) c⊢)

rename↓-raise-wt :
  ∀ k {Δ Ψ}{Σ Σ′ : Store}{c A B} →
  Σ′ ≡ renameStoreᵗ (raiseVarFrom k) Σ →
  Conv↓Wt (k + Δ) Ψ Σ c A B →
  Conv↓Wt (suc (k + Δ)) Ψ Σ′
    (subst↓ (λ X → ＇ raiseVarFrom k X) c)
    (renameᵗ (raiseVarFrom k) A)
    (renameᵗ (raiseVarFrom k) B)
rename↓-raise-wt k {Σ = Σ} eqΣ c⊢ =
  cong-⊢↓
    (trans (substStoreᵗ-ren (raiseVarFrom k) Σ) (sym eqΣ))
    refl
    (substᵗ-ren (raiseVarFrom k) _)
    (substᵗ-ren (raiseVarFrom k) _)
    (subst↓-wt (renSubst-raise-wf k) c⊢)

⊑-term-cast :
  ∀ {E M M₁ M′ M₁′ A B} →
  M ≡ M₁ →
  M′ ≡ M₁′ →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  E ⊢ M₁ ⊑ M₁′ ⦂ A ⊑ B
⊑-term-cast refl refl rel = rel

mutual
  renameᵗ-raise-⊑ :
    ∀ k {Δ Ψ Ψʳ}{Σ Σ′ Σʳ Σʳ′ : Store}
      {Γ : PCtx (k + Δ) Ψ} {Γ′ : PCtx (suc (k + Δ)) Ψ}
      {M M′ : Term} {A B : Ty} →
    Σ′ ≡ renameStoreᵗ (raiseVarFrom k) Σ →
    Σʳ′ ≡ renameStoreᵗ (raiseVarFrom k) Σʳ →
    RenameᵗPCtxMap k Γ Γ′ →
    ⟪ k + Δ , Ψ , Σ , Ψʳ , Σʳ , Γ ⟫ ⊢ M ⊑ M′ ⦂ A ⊑ B →
    ⟪ suc (k + Δ) , Ψ , Σ′ , Ψʳ , Σʳ′ , Γ′ ⟫ ⊢
      renameᵗᵐ (raiseVarFrom k) M ⊑
      renameᵗᵐ (raiseVarFrom k) M′ ⦂
      renameᵗ (raiseVarFrom k) A ⊑ renameᵗ (raiseVarFrom k) B
  renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ (⊑` h) with hΓ h
  renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ (⊑` h)
    | A′ , B′ , p′ , p⊢′ , eqA , eqB , h′ =
    ⊑-index-cast eqA eqB (⊑` h′)
  renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ
    (⊑ƛ {pA = pA} {pB = pB} {pA⊢ = pA⊢} {pB⊢ = pB⊢}
      hA hA′ rel) =
    ⊑ƛ
      {pA = renameImp (raiseVarFrom k) pA}
      {pB = renameImp (raiseVarFrom k) pB}
      {pA⊢ = wkImp-plains k pA⊢}
      {pB⊢ = wkImp-plains k pB⊢}
      (renameᵗ-preserves-WfTy hA (raiseWfPlus k))
      (renameᵗ-preserves-WfTy hA′ (raiseWfPlus k))
      (renameᵗ-raise-⊑ k eqΣ eqΣʳ (renameᵗPCtxMap-ext k hΓ) rel)
  renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ (⊑· relL relM) =
    ⊑· (renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ relL)
       (renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ relM)
  renameᵗ-raise-⊑ k {Σ = Σ} {Σʳ = Σʳ} {M = Λ M} {M′ = Λ M′}
    {A = `∀ A} {B = `∀ B} eqΣ eqΣʳ hΓ (⊑Λ vM vM′ rel) =
    ⊑Λ
      (renameᵗᵐ-value (extᵗ (raiseVarFrom k)) vM)
      (renameᵗᵐ-value (extᵗ (raiseVarFrom k)) vM′)
      (⊑-index-cast
        (rename-cong (λ X → sym (raise-ext k X)) A)
        (rename-cong (λ X → sym (raise-ext k X)) B)
        (⊑-term-cast
          (renameᵗᵐ-cong (λ X → sym (raise-ext k X)) M)
          (renameᵗᵐ-cong (λ X → sym (raise-ext k X)) M′)
          (renameᵗ-raise-⊑ (suc k)
            (trans (cong ⟰ᵗ eqΣ) (sym (renameStoreᵗ-raise-⟰ᵗ k Σ)))
            (trans (cong ⟰ᵗ eqΣʳ) (sym (renameStoreᵗ-raise-⟰ᵗ k Σʳ)))
            (renameᵗPCtxMap-⇑ᵗᴾ k hΓ)
            rel)))
  renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ
    (⊑⦂∀ {A = A} {B = B} {T = T} rel wfA wfB wfT pT⊢) =
    ⊑-index-cast
      (sym (renameᵗ-[]ᵗ (raiseVarFrom k) A T))
      (sym (renameᵗ-[]ᵗ (raiseVarFrom k) B T))
      (⊑⦂∀
        (renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ rel)
        (renameᵗ-preserves-WfTy wfA (TyRenameWf-ext (raiseWfPlus k)))
        (renameᵗ-preserves-WfTy wfB (TyRenameWf-ext (raiseWfPlus k)))
        (renameᵗ-preserves-WfTy wfT (raiseWfPlus k))
        (cong-⊢⊑-raw refl
          (renameᵗ-[]ᵗ (raiseVarFrom k) A T)
          (renameᵗ-[]ᵗ (raiseVarFrom k) B T)
          (wkImp-plains k pT⊢)))
  renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ
    (⊑⦂∀-ν {A = A} {T = T} rel wfA wfT pT⊢) =
    ⊑-index-cast
      (sym (renameᵗ-[]ᵗ (raiseVarFrom k) A T))
      refl
      (⊑⦂∀-ν
        (renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ rel)
        (renameᵗ-preserves-WfTy wfA (TyRenameWf-ext (raiseWfPlus k)))
        (renameᵗ-preserves-WfTy wfT (raiseWfPlus k))
        (cong-⊢⊑-raw refl
          (renameᵗ-[]ᵗ (raiseVarFrom k) A T)
          refl
          (wkImp-plains k pT⊢)))
  renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ ⊑$ = ⊑$
  renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ (⊑⊕ relL relM) =
    ⊑⊕ (renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ relL)
        (renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ relM)
  renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ (⊑⇑ rel p⊢ p′⊢ pB⊢) =
    ⊑⇑ (renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ rel)
      (wkImp-plains k p⊢) (wkImp-plains k p′⊢)
      (wkImp-plains k pB⊢)
  renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ (⊑⇑L rel p⊢ pB⊢) =
    ⊑⇑L (renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ rel)
      (wkImp-plains k p⊢) (wkImp-plains k pB⊢)
  renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ (⊑⇑R rel p′⊢ pB⊢) =
    ⊑⇑R (renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ rel)
      (wkImp-plains k p′⊢) (wkImp-plains k pB⊢)
  renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ (⊑⇓ rel p⊢ p′⊢ pB⊢) =
    ⊑⇓ (renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ rel)
      (wkImp-plains k p⊢) (wkImp-plains k p′⊢)
      (wkImp-plains k pB⊢)
  renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ (⊑⇓L rel p⊢ pB⊢) =
    ⊑⇓L (renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ rel)
      (wkImp-plains k p⊢) (wkImp-plains k pB⊢)
  renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ (⊑⇓R rel p′⊢ pB⊢) =
    ⊑⇓R (renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ rel)
      (wkImp-plains k p′⊢) (wkImp-plains k pB⊢)
  renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ (⊑↑ rel c⊢ c′⊢ pB⊢) =
    ⊑↑ (renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ rel)
      (rename↑-raise-wt k eqΣ c⊢)
      (rename↑-raise-wt k eqΣ c′⊢)
      (wkImp-plains k pB⊢)
  renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ (⊑↓ rel c⊢ c′⊢ pB⊢) =
    ⊑↓ (renameᵗ-raise-⊑ k eqΣ eqΣʳ hΓ rel)
      (rename↓-raise-wt k eqΣ c⊢)
      (rename↓-raise-wt k eqΣ c′⊢)
      (wkImp-plains k pB⊢)
  renameᵗ-raise-⊑ k {Σʳ = Σʳ} {M′ = M′} eqΣ eqΣʳ hΓ
    (⊑blameL {p = p} {ℓ = ℓ} hM p⊢) =
    ⊑blameL {p = renameImp (raiseVarFrom k) p} {ℓ = ℓ}
      (cong-⊢⦂
        (sym eqΣ)
        refl
        (renameˣᵐ-id (λ x → x) (λ x → refl)
          (renameᵗᵐ (raiseVarFrom k) M′))
        refl
        (renameˣᵐ-wt (λ x → x)
          (renameᵗPCtxMap-right-wt k hΓ)
          (renameᵗᵐ-raise-wt k hM)))
      (wkImp-plains k p⊢)

renameᵗ-suc-⊑ :
  ∀ {E M M′ A B} →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  ⇑ᵗᴱ E ⊢ renameᵗᵐ suc M ⊑ renameᵗᵐ suc M′ ⦂ ⇑ᵗ A ⊑ ⇑ᵗ B
renameᵗ-suc-⊑ {E = ⟪ Δ , Ψ , Σ , Ψʳ , Σʳ , Γ ⟫} rel =
  renameᵗ-raise-⊑ zero refl refl renameᵗPCtxMap-⇑ᵗᴾ-zero rel

↑ᵗᵐᴾ :
  ∀ {E Γ′ σ σ′} →
  Substᴾ E Γ′ σ σ′ →
  Substᴾ (⇑ᵗᴱ E) (⇑ᵗᴾ Γ′) (↑ᵗᵐ σ) (↑ᵗᵐ σ′)
↑ᵗᵐᴾ {E = ⟪ Δ , Ψ , Σ , Ψʳ , Σʳ , [] ⟫} hσ ()
↑ᵗᵐᴾ {E = ⟪ Δ , Ψ , Σ , Ψʳ , Σʳ , (A , B , p , p⊢) ∷ Γ ⟫}
  hσ Zₚ =
  renameᵗ-suc-⊑ (hσ Zₚ)
↑ᵗᵐᴾ {E = ⟪ Δ , Ψ , Σ , Ψʳ , Σʳ , P ∷ Γ ⟫} hσ (Sₚ h) =
  ↑ᵗᵐᴾ {E = ⟪ Δ , Ψ , Σ , Ψʳ , Σʳ , Γ ⟫}
    (λ q → hσ (Sₚ q)) h

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
substᴾ-⊑ hσ (⊑↓ rel c⊢ c′⊢ pB⊢) =
  ⊑↓ (substᴾ-⊑ hσ rel) c⊢ c′⊢ pB⊢
substᴾ-⊑ hσ (⊑blameL hM p⊢) =
  ⊑blameL (substˣ-wt _ (substᴾ-right-wt hσ) hM) p⊢

singleSubstᴾ :
  ∀ {E A A′ W W′ p p⊢} →
  E ⊢ W ⊑ W′ ⦂ A ⊑ A′ →
  Substᴾ (extendᴾ E (A , A′ , p , p⊢)) (TPEnv.Γ E)
    (singleEnv W) (singleEnv W′)
singleSubstᴾ W⊑W′ Zₚ = W⊑W′
singleSubstᴾ W⊑W′ (Sₚ h) = ⊑` h

subst-⊑ :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ M M′ N N′ A A′ B B′ p p⊢} →
  ⟪ 0 , Ψˡ , Σˡ , Ψʳ , Σʳ , [] ⟫ ⊢ N ⊑ N′ ⦂ A ⊑ A′ →
  ⟪ 0 , Ψˡ , Σˡ , Ψʳ , Σʳ , (A , A′ , p , p⊢) ∷ [] ⟫
    ⊢ M ⊑ M′ ⦂ B ⊑ B′ →
  ⟪ 0 , Ψˡ , Σˡ , Ψʳ , Σʳ , [] ⟫
    ⊢ (M [ N ]) ⊑ (M′ [ N′ ]) ⦂ B ⊑ B′
subst-⊑ N⊑N′ rel = substᴾ-⊑ (singleSubstᴾ N⊑N′) rel

WkPCtxMap :
  ∀ {Δ : TyCtx} {Ψ Ψ′ : SealCtx} →
  Ψ ≤ Ψ′ →
  PCtx Δ Ψ →
  PCtx Δ Ψ′ →
  Set
WkPCtxMap {Δ} {Ψ′ = Ψ′} Ψ≤Ψ′ Γ Γ′ =
  ∀ {x A B p p⊢} →
  Γ ∋ₚ x ⦂ (A , B , p , p⊢) →
  Σ[ p⊢′ ∈ Ψ′ ∣ plains Δ [] ⊢ p ⦂ A ⊑ B ]
    Γ′ ∋ₚ x ⦂ (A , B , p , p⊢′)

wkᴾ :
  ∀ {Δ : TyCtx} {Ψ Ψ′ : SealCtx} →
  Ψ ≤ Ψ′ →
  PCtx Δ Ψ →
  PCtx Δ Ψ′
wkᴾ Ψ≤Ψ′ [] = []
wkᴾ Ψ≤Ψ′ ((A , B , p , p⊢) ∷ Γ) =
  (A , B , p , wk-⊑ Ψ≤Ψ′ p⊢) ∷ wkᴾ Ψ≤Ψ′ Γ

wkᴾ-map :
  ∀ {Δ : TyCtx} {Ψ Ψ′ : SealCtx} {Γ : PCtx Δ Ψ} →
  (Ψ≤Ψ′ : Ψ ≤ Ψ′) →
  WkPCtxMap Ψ≤Ψ′ Γ (wkᴾ Ψ≤Ψ′ Γ)
wkᴾ-map {Γ = []} Ψ≤Ψ′ ()
wkᴾ-map {Γ = (A , B , p , p⊢) ∷ Γ} Ψ≤Ψ′ Zₚ =
  wk-⊑ Ψ≤Ψ′ p⊢ , Zₚ
wkᴾ-map {Γ = (A , B , p , p⊢) ∷ Γ} Ψ≤Ψ′ (Sₚ h)
    with wkᴾ-map {Γ = Γ} Ψ≤Ψ′ h
wkᴾ-map {Γ = (A , B , p , p⊢) ∷ Γ} Ψ≤Ψ′ (Sₚ h) | p⊢′ , h′ =
  p⊢′ , Sₚ h′

WkPCtxMap-right-wt :
  ∀ {Δ : TyCtx} {Ψ Ψ′ : SealCtx} {Γ : PCtx Δ Ψ}
    {Γ′ : PCtx Δ Ψ′} {Ψ≤Ψ′ : Ψ ≤ Ψ′} →
  WkPCtxMap Ψ≤Ψ′ Γ Γ′ →
  Renameˣ-wt (rightCtx Γ) (rightCtx Γ′) (λ x → x)
WkPCtxMap-right-wt hΓ h with lookup-right-inv h
WkPCtxMap-right-wt hΓ h | A , p , p⊢ , hₚ with hΓ hₚ
WkPCtxMap-right-wt hΓ h | A , p , p⊢ , hₚ | p⊢′ , h′ =
  lookup-right h′

extWkPCtxMap :
  ∀ {Δ : TyCtx} {Ψ Ψ′ : SealCtx} {Γ : PCtx Δ Ψ}
    {Γ′ : PCtx Δ Ψ′} {A A′ : Ty} {p : Imp}
    {p⊢ : Ψ ∣ plains Δ [] ⊢ p ⦂ A ⊑ A′}
    {Ψ≤Ψ′ : Ψ ≤ Ψ′} →
  WkPCtxMap Ψ≤Ψ′ Γ Γ′ →
  WkPCtxMap Ψ≤Ψ′
    ((A , A′ , p , p⊢) ∷ Γ)
    ((A , A′ , p , wk-⊑ Ψ≤Ψ′ p⊢) ∷ Γ′)
extWkPCtxMap hΓ Zₚ = _ , Zₚ
extWkPCtxMap hΓ (Sₚ h) with hΓ h
extWkPCtxMap hΓ (Sₚ h) | p⊢′ , h′ = p⊢′ , Sₚ h′

liftᵗWkPCtxMap :
  ∀ {Δ : TyCtx} {Ψ Ψ′ : SealCtx} {Γ : PCtx Δ Ψ}
    {Γ′ : PCtx Δ Ψ′} {Ψ≤Ψ′ : Ψ ≤ Ψ′} →
  WkPCtxMap Ψ≤Ψ′ Γ Γ′ →
  WkPCtxMap Ψ≤Ψ′ (⇑ᵗᴾ Γ) (⇑ᵗᴾ Γ′)
liftᵗWkPCtxMap hΓ h with ⇑ᵗᴾ-un∋ h
liftᵗWkPCtxMap hΓ h | A , B , p , p⊢ , refl , h′ with hΓ h′
liftᵗWkPCtxMap hΓ h | A , B , p , p⊢ , refl , h′ | p⊢′ , h″ =
  wkImp-plains zero p⊢′ , lookup-⇑ᵗᴾ h″

wk-rel-⊑ :
  ∀ {E : TPEnv} {Ψ′ : SealCtx} {Σ′ : Store}
    {Γ′ : PCtx (TPEnv.Δ E) Ψ′} {M M′ : Term} {A B : Ty} →
  (Ψ≤Ψ′ : TPEnv.Ψ E ≤ Ψ′) →
  TPEnv.store E ⊆ˢ Σ′ →
  WkPCtxMap Ψ≤Ψ′ (TPEnv.Γ E) Γ′ →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  ⟪ TPEnv.Δ E , Ψ′ , Σ′ , TPEnv.Ψʳ E , TPEnv.storeʳ E , Γ′ ⟫
    ⊢ M ⊑ M′ ⦂ A ⊑ B
wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ (⊑` h) with hΓ h
wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ (⊑` h) | p⊢′ , h′ = ⊑` h′
wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ
  (⊑ƛ {pA = pA} {pB = pB} {pA⊢ = pA⊢} {pB⊢ = pB⊢} hA hA′ rel) =
  ⊑ƛ {pA = pA} {pB = pB}
    {pA⊢ = wk-⊑ Ψ≤Ψ′ pA⊢} {pB⊢ = wk-⊑ Ψ≤Ψ′ pB⊢}
    (WfTy-weakenˢ hA Ψ≤Ψ′)
    (WfTy-weakenˢ hA′ Ψ≤Ψ′)
    (wk-rel-⊑ Ψ≤Ψ′ wΣ (extWkPCtxMap hΓ) rel)
wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ (⊑· relL relM) =
  ⊑· (wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ relL)
     (wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ relM)
wk-rel-⊑ {E = E} {Γ′ = Γ′} Ψ≤Ψ′ wΣ hΓ (⊑Λ vM vM′ rel) =
  ⊑Λ vM vM′
    (wk-rel-⊑ {E = ⇑ᵗᴱ E} {Γ′ = ⇑ᵗᴾ Γ′}
      Ψ≤Ψ′ (⟰ᵗ-⊆ˢ wΣ)
      (liftᵗWkPCtxMap {Ψ≤Ψ′ = Ψ≤Ψ′} hΓ)
      rel)
wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ (⊑⦂∀ rel wfA wfB wfT pT⊢) =
  ⊑⦂∀
    (wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ rel)
    (WfTy-weakenˢ wfA Ψ≤Ψ′)
    (WfTy-weakenˢ wfB Ψ≤Ψ′)
    (WfTy-weakenˢ wfT Ψ≤Ψ′)
    (wk-⊑ Ψ≤Ψ′ pT⊢)
wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ (⊑⦂∀-ν rel wfA wfT pT⊢) =
  ⊑⦂∀-ν
    (wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ rel)
    (WfTy-weakenˢ wfA Ψ≤Ψ′)
    (WfTy-weakenˢ wfT Ψ≤Ψ′)
    (wk-⊑ Ψ≤Ψ′ pT⊢)
wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ ⊑$ = ⊑$
wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ (⊑⊕ relL relM) =
  ⊑⊕ (wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ relL)
      (wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ relM)
wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ (⊑⇑ rel p⊢ p′⊢ pB⊢) =
  ⊑⇑ (wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ rel)
    (wk-⊑ Ψ≤Ψ′ p⊢) (wk-⊑ Ψ≤Ψ′ p′⊢) (wk-⊑ Ψ≤Ψ′ pB⊢)
wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ (⊑⇑L rel p⊢ pB⊢) =
  ⊑⇑L (wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ rel)
    (wk-⊑ Ψ≤Ψ′ p⊢) (wk-⊑ Ψ≤Ψ′ pB⊢)
wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ (⊑⇑R rel p′⊢ pB⊢) =
  ⊑⇑R (wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ rel)
    (wk-⊑ Ψ≤Ψ′ p′⊢) (wk-⊑ Ψ≤Ψ′ pB⊢)
wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ (⊑⇓ rel p⊢ p′⊢ pB⊢) =
  ⊑⇓ (wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ rel)
    (wk-⊒ Ψ≤Ψ′ p⊢) (wk-⊒ Ψ≤Ψ′ p′⊢) (wk-⊑ Ψ≤Ψ′ pB⊢)
wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ (⊑⇓L rel p⊢ pB⊢) =
  ⊑⇓L (wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ rel)
    (wk-⊒ Ψ≤Ψ′ p⊢) (wk-⊑ Ψ≤Ψ′ pB⊢)
wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ (⊑⇓R rel p′⊢ pB⊢) =
  ⊑⇓R (wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ rel)
    (wk-⊒ Ψ≤Ψ′ p′⊢) (wk-⊑ Ψ≤Ψ′ pB⊢)
wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ (⊑↑ rel c⊢ c′⊢ pB⊢) =
  ⊑↑ (wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ rel)
    (wk-conv↑ Ψ≤Ψ′ wΣ c⊢)
    (wk-conv↑ Ψ≤Ψ′ wΣ c′⊢)
    (wk-⊑ Ψ≤Ψ′ pB⊢)
wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ (⊑↓ rel c⊢ c′⊢ pB⊢) =
  ⊑↓ (wk-rel-⊑ Ψ≤Ψ′ wΣ hΓ rel)
    (wk-conv↓ Ψ≤Ψ′ wΣ c⊢)
    (wk-conv↓ Ψ≤Ψ′ wΣ c′⊢)
    (wk-⊑ Ψ≤Ψ′ pB⊢)
wk-rel-⊑ {E = E} {Γ′ = Γ′} Ψ≤Ψ′ wΣ hΓ
 (⊑blameL {M = M} {p = p} {ℓ = ℓ} hM p⊢) =
  ⊑blameL {p = p} {ℓ = ℓ}
    (cong-⊢⦂ refl refl (renameˣᵐ-id (λ x → x) (λ x → refl) M) refl
      (renameˣᵐ-wt (λ x → x)
        (WkPCtxMap-right-wt {Γ = TPEnv.Γ E} {Γ′ = Γ′}
          {Ψ≤Ψ′ = Ψ≤Ψ′} hΓ)
        (wk-term Ψ≤Ψ′ wΣ hM)))
    (wk-⊑ Ψ≤Ψ′ p⊢)

postulate
  wk-right-world-⊑ :
    ∀ {E : TPEnv} {Ψʳ′ : SealCtx} {Σʳ′ : Store}
      {M M′ : Term} {A B : Ty} →
    StoreWf (TPEnv.Δ E) Ψʳ′ Σʳ′ →
    E ⊢ M ⊑ M′ ⦂ A ⊑ B →
    ⟪ TPEnv.Δ E , TPEnv.Ψ E , TPEnv.store E ,
      Ψʳ′ , Σʳ′ , TPEnv.Γ E ⟫ ⊢ M ⊑ M′ ⦂ A ⊑ B

  wk-left-world-⊑ :
    ∀ {Ψˡ Ψˡ′ Ψʳ Ψʳ′ Σˡ Σˡ′ Σʳ Σʳ′ M M′ A B} →
    StoreWf 0 Ψˡ′ Σˡ′ →
    StoreWf 0 Ψʳ′ Σʳ′ →
    Ψˡ ≤ Ψˡ′ →
    Σˡ ⊆ˢ Σˡ′ →
    ⟪ 0 , Ψˡ , Σˡ , Ψʳ , Σʳ , [] ⟫ ⊢ M ⊑ M′ ⦂ A ⊑ B →
    ⟪ 0 , Ψˡ′ , Σˡ′ , Ψʳ′ , Σʳ′ , [] ⟫ ⊢ M ⊑ M′ ⦂ A ⊑ B

postulate
  tysubst-body-⊑ :
    ∀ {Ψ Σ M M′ A B T} →
    WfTy 0 Ψ T →
    ⟪ 1 , Ψ , ⟰ᵗ Σ , Ψ , ⟰ᵗ Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ A ⊑ B →
    ⟪ 0 , Ψ , Σ , Ψ , Σ , [] ⟫
      ⊢ (M [ T ]ᵀ) ⊑ (M′ [ T ]ᵀ) ⦂ (A [ T ]ᵗ) ⊑ (B [ T ]ᵗ)

tysubst-⊑ :
  ∀ {Ψ Σ M M′ A B T} →
  WfTy 0 Ψ T →
  ⟪ 0 , Ψ , Σ , Ψ , Σ , [] ⟫ ⊢ (Λ M) ⊑ (Λ M′) ⦂ `∀ A ⊑ `∀ B →
  ⟪ 0 , Ψ , Σ , Ψ , Σ , [] ⟫
    ⊢ (M [ T ]ᵀ) ⊑ (M′ [ T ]ᵀ) ⦂ (A [ T ]ᵗ) ⊑ (B [ T ]ᵗ)
tysubst-⊑ hT (⊑Λ vM vM′ rel) = tysubst-body-⊑ hT rel
