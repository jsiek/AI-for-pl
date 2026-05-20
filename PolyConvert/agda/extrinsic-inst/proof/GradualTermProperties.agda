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
    ; VarPrecCtx
    ; extend-X⊑X
    ; X⊑X
    ; renameImp
    ; _∣_⊢_⦂_⊑_
    )
open import Consistency
open import GradualTerms
open import Primitives using (κℕ; constTy; constTy-renameᵗ; constTy-⇑ᵗ)
open import Terms
open import proof.ConsistencyProperties
open import proof.ImprecisionProperties using (reflImp-wt-extend-X⊑X; wkImpAt)
open import proof.TypeProperties
  using
    ( raise-ext
    ; raiseVarFrom-<-inv
    ; rename-raise-ext
    ; renameᵗ-ground-id
    ; renameᵗ-inv-WfTy
    )
open import proof.PreservationTermSubst
  using (renameᵗ-[]ᵗ; unmap∋-⤊ᵗ)

⊢ᴳ-refl :
  ∀ {Δ Γ M A} →
  Δ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ extend-X⊑X Δ [] ⊢ᴳ M ⊑ M
⊢ᴳ-refl (⊢` x∈) = ⊑`
⊢ᴳ-refl (⊢ƛ wfA M⊢) = ⊑ƛ (reflImp-wt-extend-X⊑X wfA) (⊢ᴳ-refl M⊢)
⊢ᴳ-refl (⊢· L⊢ M⊢ A~A′) = ⊑· (⊢ᴳ-refl L⊢) (⊢ᴳ-refl M⊢)
⊢ᴳ-refl (⊢·★ L⊢ M⊢ A′~★) = ⊑· (⊢ᴳ-refl L⊢) (⊢ᴳ-refl M⊢)
⊢ᴳ-refl (⊢Λ vM M⊢) = ⊑Λ vM vM (⊢ᴳ-refl M⊢)
⊢ᴳ-refl (⊢• M⊢ wfB wfT) =
  ⊑`[] (⊢ᴳ-refl M⊢) (reflImp-wt-extend-X⊑X wfT)
⊢ᴳ-refl (⊢$ (κℕ n)) = ⊑$
⊢ᴳ-refl (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ) =
  ⊑⊕ (⊢ᴳ-refl L⊢) (⊢ᴳ-refl M⊢)

infix 4 _∋ᴳ_⦂_
data _∋ᴳ_⦂_ {Φ : VarPrecCtx} :
    GPCtx Φ → Var → GPrec Φ → Set where

  Zᴳ : ∀ {Γ : GPCtx Φ} {P : GPrec Φ} →
    (P ∷ Γ) ∋ᴳ zero ⦂ P

  Sᴳ : ∀ {Γ : GPCtx Φ} {P Q : GPrec Φ} {x} →
    Γ ∋ᴳ x ⦂ P →
    (Q ∷ Γ) ∋ᴳ suc x ⦂ P

lookup-leftᴳ :
  ∀ {Φ} {Γ : GPCtx Φ} {x A B p p⊢} →
  Γ ∋ᴳ x ⦂ (A , B , p , p⊢) →
  leftGCtx {Φ} Γ ∋ x ⦂ A
lookup-leftᴳ {Φ} Zᴳ = Z
lookup-leftᴳ {Φ} (Sᴳ h) = S (lookup-leftᴳ {Φ} h)

lookup-rightᴳ :
  ∀ {Φ} {Γ : GPCtx Φ} {x A B p p⊢} →
  Γ ∋ᴳ x ⦂ (A , B , p , p⊢) →
  rightGCtx {Φ} Γ ∋ x ⦂ B
lookup-rightᴳ {Φ} Zᴳ = Z
lookup-rightᴳ {Φ} (Sᴳ h) = S (lookup-rightᴳ {Φ} h)

lookup-leftᴳ-inv :
  ∀ {Φ} {Γ : GPCtx Φ} {x A} →
  leftGCtx {Φ} Γ ∋ x ⦂ A →
  Σ[ B ∈ Ty ] Σ[ p ∈ Imp ]
    Σ[ p⊢ ∈ (0 ∣ Φ ⊢ p ⦂ A ⊑ B) ]
      (Γ ∋ᴳ x ⦂ (A , B , p , p⊢))
lookup-leftᴳ-inv {Φ} {Γ = (A , B , p , p⊢) ∷ Γ} Z =
  B , p , p⊢ , Zᴳ
lookup-leftᴳ-inv {Φ} {Γ = P ∷ Γ} (S h)
    with lookup-leftᴳ-inv {Φ} {Γ = Γ} h
lookup-leftᴳ-inv {Φ} {Γ = P ∷ Γ} (S h) | B , p , p⊢ , hᴳ =
  B , p , p⊢ , Sᴳ hᴳ

⇑ᵗᴳPrec : ∀ {Φ m} → GPrec Φ → GPrec (m ∷ Φ)
⇑ᵗᴳPrec {m = m} (A , B , p , p⊢) =
  ⇑ᵗ A , ⇑ᵗ B , renameImp suc p , wkImpAt {Φ = []} p⊢

⇑ᵗᴳPCtx : ∀ {Φ m} → GPCtx Φ → GPCtx (m ∷ Φ)
⇑ᵗᴳPCtx {m = m} [] = []
⇑ᵗᴳPCtx {m = m} (P ∷ Γ) = ⇑ᵗᴳPrec {m = m} P ∷ ⇑ᵗᴳPCtx {m = m} Γ

leftGCtx-⇑ᵗᴳPCtx :
  ∀ {Φ m} → (Γ : GPCtx Φ) →
  leftGCtx {m ∷ Φ} (⇑ᵗᴳPCtx {m = m} Γ) ≡
  ⤊ᵗ (leftGCtx {Φ} Γ)
leftGCtx-⇑ᵗᴳPCtx {m = m} [] = refl
leftGCtx-⇑ᵗᴳPCtx {m = m} ((A , B , p , p⊢) ∷ Γ) =
  cong (⇑ᵗ A ∷_) (leftGCtx-⇑ᵗᴳPCtx {m = m} Γ)

rightGCtx-⇑ᵗᴳPCtx :
  ∀ {Φ m} → (Γ : GPCtx Φ) →
  rightGCtx {m ∷ Φ} (⇑ᵗᴳPCtx {m = m} Γ) ≡
  ⤊ᵗ (rightGCtx {Φ} Γ)
rightGCtx-⇑ᵗᴳPCtx {m = m} [] = refl
rightGCtx-⇑ᵗᴳPCtx {m = m} ((A , B , p , p⊢) ∷ Γ) =
  cong (⇑ᵗ B ∷_) (rightGCtx-⇑ᵗᴳPCtx {m = m} Γ)

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
  ⊢ƛ (drop-extend-X~X-WfTy {d = d} {Φ = Φ} {Γ = Γᶜ} wfA) M⊢′
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = L · M} (⊢· L⊢ M⊢ A~A′)
    with drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} L⊢
       | drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} M⊢
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = L · M} (⊢· L⊢ M⊢ A~A′)
    | A ⇒ B , refl , L⊢′ | A′ , refl , M⊢′ =
  B , refl ,
  ⊢· L⊢′ M⊢′ (drop-extend-X~X-at-~ {d = d} {Φ = Φ} {Γ = Γᶜ} A~A′)
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = L · M} (⊢·★ L⊢ M⊢ A~★)
    with drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} L⊢
       | drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} M⊢
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = L · M} (⊢·★ L⊢ M⊢ A~★)
    | ★ , refl , L⊢′ | A , refl , M⊢′ =
  ★ , refl ,
  ⊢·★ L⊢′ M⊢′ (drop-extend-X~X-at-~ {d = d} {Φ = Φ} {Γ = Γᶜ} A~★)
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} {Γ = Γ}
    {M = Λ M} (⊢Λ vM M⊢)
    with drop-renameᵗᴳ-at-wt {d = d} {Φ = X~X ∷ Φ} {Γᶜ = Γᶜ}
      {Γ = ⤊ᵗ Γ} {M = M}
      (subst
        (λ N → length ((X~X ∷ Φ) ++ d ∷ Γᶜ) ∣
          renameCtxAt (suc (length Φ)) (⤊ᵗ Γ) ⊢ N ⦂ _)
        (renameᵗᴳ-cong (raise-ext (length Φ)) M)
        (subst
          (λ Γ′ → length ((X~X ∷ Φ) ++ d ∷ Γᶜ) ∣ Γ′ ⊢
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
    (drop-extend-X~X-WfTy {d = d} {Φ = X~X ∷ Φ} {Γ = Γᶜ} {A = B}
      (subst (λ B′ → WfTy (suc (length (Φ ++ d ∷ Γᶜ))) 0 B′)
        (rename-raise-ext (length Φ) B)
        wfB))
    (drop-extend-X~X-WfTy {d = d} {Φ = Φ} {Γ = Γᶜ} wfT)
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
  ⊢⊕ L⊢′ (drop-extend-X~X-at-~ {d = d} {Φ = Φ} {Γ = Γᶜ} A~ℕ) op
      M⊢′ (drop-extend-X~X-at-~ {d = d} {Φ = Φ} {Γ = Γᶜ} B~ℕ)

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
  ⊢ƛ (drop-⇑ᵗ-WfTy-extend-X⊑X wfA) M⊢′
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
    with drop-renameᵗᴳ-at-wt {d = X~X} {Φ = X~X ∷ []}
      {Γᶜ = extend-X~X Δ []} {Γ = ⤊ᵗ Γ} {M = M}
      (cong-⊢ᴳ⦂
        (cong suc (cong suc (sym (length-extend-X~X[] Δ))))
        (sym (trans (renameCtxAt-⤊ᵗ zero Γ)
                    (cong ⤊ᵗ (renameCtxAt-zero Γ))))
        (renameᵗᴳ-cong (raise-ext zero) M)
        refl
        M⊢)
drop-renameᵗᴳ-wt {M = Λ M} (⊢Λ vM M⊢) | B , eqB , M⊢′ =
  `∀ B , cong `∀ (trans eqB (sym (rename-raise-ext zero B))) ,
  ⊢Λ (renameᵗᴳ-value-inv vM)
    (cong-⊢ᴳ⦂ (cong suc (length-extend-X~X[] _)) refl refl refl M⊢′)
drop-renameᵗᴳ-wt {Δ = Δ} {Γ = Γ} {M = M `[ T ]} M[T]⊢
    with drop-renameᵗᴳ-at-wt {d = X~X} {Φ = []}
      {Γᶜ = extend-X~X Δ []} {Γ = Γ} {M = M `[ T ]}
      (cong-⊢ᴳ⦂
        (cong suc (sym (length-extend-X~X[] Δ)))
        (sym (renameCtxAt-zero Γ))
        refl
        refl
        M[T]⊢)
drop-renameᵗᴳ-wt {Δ = Δ} {M = M `[ T ]} M[T]⊢
    | B , eqB , M[T]⊢′ =
  B , eqB , cong-⊢ᴳ⦂ (length-extend-X~X[] Δ) refl refl refl M[T]⊢′
drop-renameᵗᴳ-wt {M = $ κ} (⊢$ κ) = constTy κ , constTy-⇑ᵗ κ , ⊢$ κ
drop-renameᵗᴳ-wt {M = L ⊕[ op ] M} (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    with drop-renameᵗᴳ-wt L⊢ | drop-renameᵗᴳ-wt M⊢
drop-renameᵗᴳ-wt {M = L ⊕[ op ] M} (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | A , refl , L⊢′ | B , refl , M⊢′ =
  ‵ `ℕ , refl ,
  ⊢⊕ L⊢′ (drop-both-~ A~ℕ) op M⊢′ (drop-both-~ B~ℕ)
