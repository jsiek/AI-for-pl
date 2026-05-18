module proof.GradualTermProperties where

-- File Charter:
--   * Structural properties of gradual precision contexts and gradual terms.
--   * Includes lookup projections for `GPCtx` and type-renaming inversion for
--     gradual typing derivations.
--   * Main SGG case analysis belongs in `proof.StaticGradualGuarantee`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Nat using (zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import Types
open import Ctx using (⤊ᵗ)
open import Imprecision
  using
    ( Imp
    ; plains
    ; renameImp
    ; _∣_⊢_⦂_⊑_
    )
open import Consistency
open import GradualTerms
open import Primitives using (constTy; constTy-renameᵗ; constTy-⇑ᵗ)
open import Terms
open import proof.ConsistencyProperties
open import proof.TypeProperties
  using
    ( raise-ext
    ; raiseVarFrom-<-inv
    ; rename-raise-ext
    ; renameᵗ-ground-id
    ; renameᵗ-inv-WfTy
    )
open import proof.PreservationTermSubst
  using (renameᵗ-[]ᵗ; unmap∋-⤊ᵗ; wkImp-plains)

infix 4 _∋ᴳ_⦂_
data _∋ᴳ_⦂_ {Δ : TyCtx} :
    GPCtx Δ → Var → GPrec Δ → Set where

  Zᴳ : ∀ {Γ P} →
    (P ∷ Γ) ∋ᴳ zero ⦂ P

  Sᴳ : ∀ {Γ P Q x} →
    Γ ∋ᴳ x ⦂ P →
    (Q ∷ Γ) ∋ᴳ suc x ⦂ P

lookup-leftᴳ :
  ∀ {Δ} {Γ : GPCtx Δ} {x A B p p⊢} →
  Γ ∋ᴳ x ⦂ (A , B , p , p⊢) →
  leftGCtx Γ ∋ x ⦂ A
lookup-leftᴳ Zᴳ = Z
lookup-leftᴳ (Sᴳ h) = S (lookup-leftᴳ h)

lookup-rightᴳ :
  ∀ {Δ} {Γ : GPCtx Δ} {x A B p p⊢} →
  Γ ∋ᴳ x ⦂ (A , B , p , p⊢) →
  rightGCtx Γ ∋ x ⦂ B
lookup-rightᴳ Zᴳ = Z
lookup-rightᴳ (Sᴳ h) = S (lookup-rightᴳ h)

lookup-leftᴳ-inv :
  ∀ {Δ} {Γ : GPCtx Δ} {x A} →
  leftGCtx Γ ∋ x ⦂ A →
  Σ[ B ∈ Ty ] Σ[ p ∈ Imp ]
    Σ[ p⊢ ∈ (0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B) ]
      (Γ ∋ᴳ x ⦂ (A , B , p , p⊢))
lookup-leftᴳ-inv {Γ = (A , B , p , p⊢) ∷ Γ} Z =
  B , p , p⊢ , Zᴳ
lookup-leftᴳ-inv {Γ = P ∷ Γ} (S h)
    with lookup-leftᴳ-inv {Γ = Γ} h
lookup-leftᴳ-inv {Γ = P ∷ Γ} (S h) | B , p , p⊢ , hᴳ =
  B , p , p⊢ , Sᴳ hᴳ

⇑ᵗᴳPrec : ∀ {Δ} → GPrec Δ → GPrec (suc Δ)
⇑ᵗᴳPrec (A , B , p , p⊢) =
  ⇑ᵗ A , ⇑ᵗ B , renameImp suc p , wkImp-plains zero p⊢

⇑ᵗᴳPCtx : ∀ {Δ} → GPCtx Δ → GPCtx (suc Δ)
⇑ᵗᴳPCtx [] = []
⇑ᵗᴳPCtx (P ∷ Γ) = ⇑ᵗᴳPrec P ∷ ⇑ᵗᴳPCtx Γ

leftGCtx-⇑ᵗᴳPCtx :
  ∀ {Δ} → (Γ : GPCtx Δ) →
  leftGCtx (⇑ᵗᴳPCtx Γ) ≡ ⤊ᵗ (leftGCtx Γ)
leftGCtx-⇑ᵗᴳPCtx [] = refl
leftGCtx-⇑ᵗᴳPCtx ((A , B , p , p⊢) ∷ Γ) =
  cong (⇑ᵗ A ∷_) (leftGCtx-⇑ᵗᴳPCtx Γ)

rightGCtx-⇑ᵗᴳPCtx :
  ∀ {Δ} → (Γ : GPCtx Δ) →
  rightGCtx (⇑ᵗᴳPCtx Γ) ≡ ⤊ᵗ (rightGCtx Γ)
rightGCtx-⇑ᵗᴳPCtx [] = refl
rightGCtx-⇑ᵗᴳPCtx ((A , B , p , p⊢) ∷ Γ) =
  cong (⇑ᵗ B ∷_) (rightGCtx-⇑ᵗᴳPCtx Γ)

DropRenameGTypingResult : TyCtx → Ctx → GTerm → Ty → Set
DropRenameGTypingResult Δ Γ M B′ =
  Σ[ B ∈ Ty ] ((B′ ≡ ⇑ᵗ B) × (Δ ∣ Γ ⊢ M ⦂ B))

DropRenameGTypingAtResult : CCtx → CCtx → Ctx → GTerm → Ty → Set
DropRenameGTypingAtResult Φ Γᶜ Γ M B′ =
  Σ[ B ∈ Ty ]
    ((B′ ≡ renameᵗ (raiseVarFrom (length Φ)) B) ×
     (length (Φ ++ Γᶜ) ∣ Γ ⊢ M ⦂ B))

unmap∋-renameCtxAt :
  ∀ k {Γ x A′} →
  renameCtxAt k Γ ∋ x ⦂ A′ →
  Σ[ A ∈ Ty ] (A′ ≡ renameᵗ (raiseVarFrom k) A) × (Γ ∋ x ⦂ A)
unmap∋-renameCtxAt k {Γ = A ∷ Γ} Z = A , refl , Z
unmap∋-renameCtxAt k {Γ = A ∷ Γ} (S x∈)
    with unmap∋-renameCtxAt k x∈
unmap∋-renameCtxAt k {Γ = A ∷ Γ} (S x∈) | B , eq , x∈′ =
  B , eq , S x∈′

drop-renameᵗᴳ-at-wt :
  ∀ {d Φ Γᶜ Γ M B′} →
  length (Φ ++ d ∷ Γᶜ) ∣ renameCtxAt (length Φ) Γ ⊢
    renameᵗᴳ (raiseVarFrom (length Φ)) M ⦂ B′ →
  DropRenameGTypingAtResult Φ Γᶜ Γ M B′
drop-renameᵗᴳ-at-wt {Φ = Φ} {M = ` x} (⊢` x∈)
    with unmap∋-renameCtxAt (length Φ) x∈
drop-renameᵗᴳ-at-wt {Φ = Φ} {M = ` x} (⊢` x∈)
    | A , eq , x∈′ =
  A , eq , ⊢` x∈′
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = ƛ A ⇒ M} (⊢ƛ wfA M⊢)
    with drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} M⊢
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = ƛ A ⇒ M} (⊢ƛ wfA M⊢)
    | B , refl , M⊢′ =
  A ⇒ B , refl ,
  ⊢ƛ (drop-boths-WfTy {d = d} {Φ = Φ} {Γ = Γᶜ} wfA) M⊢′
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = L · M} (⊢· L⊢ M⊢ A~A′)
    with drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} L⊢
       | drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} M⊢
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = L · M} (⊢· L⊢ M⊢ A~A′)
    | A ⇒ B , refl , L⊢′ | A′ , refl , M⊢′ =
  B , refl ,
  ⊢· L⊢′ M⊢′ (drop-boths-at-~ {d = d} {Φ = Φ} {Γ = Γᶜ} A~A′)
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = L · M} (⊢·★ L⊢ M⊢ A~★)
    with drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} L⊢
       | drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} M⊢
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = L · M} (⊢·★ L⊢ M⊢ A~★)
    | ★ , refl , L⊢′ | A , refl , M⊢′ =
  ★ , refl ,
  ⊢·★ L⊢′ M⊢′ (drop-boths-at-~ {d = d} {Φ = Φ} {Γ = Γᶜ} A~★)
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} {Γ = Γ}
    {M = Λ M} (⊢Λ vM M⊢)
    with drop-renameᵗᴳ-at-wt {d = d} {Φ = both ∷ Φ} {Γᶜ = Γᶜ}
      {Γ = ⤊ᵗ Γ} {M = M}
      (subst
        (λ N → length ((both ∷ Φ) ++ d ∷ Γᶜ) ∣
          renameCtxAt (suc (length Φ)) (⤊ᵗ Γ) ⊢ N ⦂ _)
        (renameᵗᴳ-cong (raise-ext (length Φ)) M)
        (subst
          (λ Γ′ → length ((both ∷ Φ) ++ d ∷ Γᶜ) ∣ Γ′ ⊢
            renameᵗᴳ (extᵗ (raiseVarFrom (length Φ))) M ⦂ _)
          (sym (renameCtxAt-⤊ᵗ (length Φ) Γ))
          M⊢))
drop-renameᵗᴳ-at-wt {Φ = Φ} {M = Λ M} (⊢Λ vM M⊢)
    | B , eqB , M⊢′ =
  `∀ B ,
  cong `∀ (trans eqB (sym (rename-raise-ext (length Φ) B))) ,
  ⊢Λ (renameᵗᴳ-value-inv vM) M⊢′
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = M `[ T ]} (⊢• M⊢ wfB wfT)
    with drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} M⊢
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = M `[ T ]} (⊢• M⊢ wfB wfT)
    | `∀ B , refl , M⊢′ =
  B [ T ]ᵗ ,
  sym (renameᵗ-[]ᵗ (raiseVarFrom (length Φ)) B T) ,
  ⊢• M⊢′
    (drop-boths-WfTy {d = d} {Φ = both ∷ Φ} {Γ = Γᶜ} {A = B}
      (subst (λ B′ → WfTy (suc (length (Φ ++ d ∷ Γᶜ))) 0 B′)
        (rename-raise-ext (length Φ) B)
        wfB))
    (drop-boths-WfTy {d = d} {Φ = Φ} {Γ = Γᶜ} wfT)
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = M `[ T ]} (⊢•★ M⊢ wfT)
    with drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} M⊢
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = M `[ T ]} (⊢•★ M⊢ wfT)
    | ★ , refl , M⊢′ =
  ★ , refl ,
  ⊢•★ M⊢′
    (renameᵗ-inv-WfTy (raiseVarFrom-<-inv (length Φ)) wfT)
drop-renameᵗᴳ-at-wt {Φ = Φ} {M = $ κ} (⊢$ κ) =
  constTy κ , constTy-renameᵗ (raiseVarFrom (length Φ)) κ , ⊢$ κ
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = L ⊕[ op ] M} (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    with drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} L⊢
       | drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} M⊢
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = L ⊕[ op ] M} (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | A , refl , L⊢′ | B , refl , M⊢′ =
  ‵ `ℕ , refl ,
  ⊢⊕ L⊢′ (drop-boths-at-~ {d = d} {Φ = Φ} {Γ = Γᶜ} A~ℕ) op
      M⊢′ (drop-boths-at-~ {d = d} {Φ = Φ} {Γ = Γᶜ} B~ℕ)

drop-renameᵗᴳ-wt :
  ∀ {Δ Γ M B′} →
  suc Δ ∣ ⤊ᵗ Γ ⊢ renameᵗᴳ suc M ⦂ B′ →
  DropRenameGTypingResult Δ Γ M B′
drop-renameᵗᴳ-wt {M = ` x} (⊢` x∈) with unmap∋-⤊ᵗ x∈
drop-renameᵗᴳ-wt {M = ` x} (⊢` x∈) | A , eq , x∈′ =
  A , eq , ⊢` x∈′
drop-renameᵗᴳ-wt {M = ƛ A ⇒ M} (⊢ƛ wfA M⊢)
    with drop-renameᵗᴳ-wt M⊢
drop-renameᵗᴳ-wt {M = ƛ A ⇒ M} (⊢ƛ wfA M⊢)
    | B , refl , M⊢′ =
  A ⇒ B , refl ,
  ⊢ƛ (drop-⇑ᵗ-WfTy-plains wfA) M⊢′
drop-renameᵗᴳ-wt {M = L · M} (⊢· L⊢ M⊢ A~A′)
    with drop-renameᵗᴳ-wt L⊢ | drop-renameᵗᴳ-wt M⊢
drop-renameᵗᴳ-wt {M = L · M} (⊢· L⊢ M⊢ A~A′)
    | A ⇒ B , refl , L⊢′ | A′ , refl , M⊢′ =
  B , refl , ⊢· L⊢′ M⊢′ (drop-both-~ A~A′)
drop-renameᵗᴳ-wt {M = L · M} (⊢·★ L⊢ M⊢ A~★)
    with drop-renameᵗᴳ-wt L⊢ | drop-renameᵗᴳ-wt M⊢
drop-renameᵗᴳ-wt {M = L · M} (⊢·★ L⊢ M⊢ A~★)
    | ★ , refl , L⊢′ | A , refl , M⊢′ =
  ★ , refl , ⊢·★ L⊢′ M⊢′ (drop-both-~ A~★)
drop-renameᵗᴳ-wt {Δ = Δ} {Γ = Γ} {M = Λ M} (⊢Λ vM M⊢)
    with drop-renameᵗᴳ-at-wt {d = both} {Φ = both ∷ []}
      {Γᶜ = boths Δ []} {Γ = ⤊ᵗ Γ} {M = M}
      (cong-⊢ᴳ⦂
        (cong suc (cong suc (sym (length-boths[] Δ))))
        (sym (trans (renameCtxAt-⤊ᵗ zero Γ)
                    (cong ⤊ᵗ (renameCtxAt-zero Γ))))
        (renameᵗᴳ-cong (raise-ext zero) M)
        refl
        M⊢)
drop-renameᵗᴳ-wt {M = Λ M} (⊢Λ vM M⊢) | B , eqB , M⊢′ =
  `∀ B , cong `∀ (trans eqB (sym (rename-raise-ext zero B))) ,
  ⊢Λ (renameᵗᴳ-value-inv vM)
    (cong-⊢ᴳ⦂ (cong suc (length-boths[] _)) refl refl refl M⊢′)
drop-renameᵗᴳ-wt {Δ = Δ} {Γ = Γ} {M = M `[ T ]} M[T]⊢
    with drop-renameᵗᴳ-at-wt {d = both} {Φ = []}
      {Γᶜ = boths Δ []} {Γ = Γ} {M = M `[ T ]}
      (cong-⊢ᴳ⦂
        (cong suc (sym (length-boths[] Δ)))
        (sym (renameCtxAt-zero Γ))
        refl
        refl
        M[T]⊢)
drop-renameᵗᴳ-wt {Δ = Δ} {M = M `[ T ]} M[T]⊢
    | B , eqB , M[T]⊢′ =
  B , eqB , cong-⊢ᴳ⦂ (length-boths[] Δ) refl refl refl M[T]⊢′
drop-renameᵗᴳ-wt {M = $ κ} (⊢$ κ) = constTy κ , constTy-⇑ᵗ κ , ⊢$ κ
drop-renameᵗᴳ-wt {M = L ⊕[ op ] M} (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    with drop-renameᵗᴳ-wt L⊢ | drop-renameᵗᴳ-wt M⊢
drop-renameᵗᴳ-wt {M = L ⊕[ op ] M} (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | A , refl , L⊢′ | B , refl , M⊢′ =
  ‵ `ℕ , refl ,
  ⊢⊕ L⊢′ (drop-both-~ A~ℕ) op M⊢′ (drop-both-~ B~ℕ)
