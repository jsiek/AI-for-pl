{-# OPTIONS --allow-unsolved-metas #-}

module proof.DynamicGradualGuarantee where

-- File Charter:
--   * Top-down mechanization skeleton for the dynamic gradual guarantee from
--     cambridge25.
--   * Keeps the theorem statement and proof case analysis separate from local
--     inversion work such as Left Seal Narrowing Inversion.
--   * The proof follows the cambridge25 section "Gradual Guarantee": recurse on
--     term narrowing and on the right-hand reduction, invoking named lemmas for
--     catch-up, inversion, wrapping, and cast movement.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)

open import Types
open import Coercions
open import Primitives using (addℕ; κℕ)
open import NuTerms
open import NuReduction
open import NuStore using (StoreWf; at)
open import NarrowWiden
open import TermNarrowing
open import proof.CoercionProperties using (coercion-wf)
open import proof.Catchup using (catchup-lemma; runtime-⇑ᵗᵐ)
open import proof.CatchupStore using
  ( combineStoreNrw
  ; combineStoreNrw-empty-⊒ˢ
  ; combineStoreNrw-applyStores
  )
open import proof.NarrowWidenProperties using
  ( tgtStoreⁿ-⊒ˢ
  ; ⊒ˢ-empty-anyᵗ
  )
open import proof.ReductionProperties using
  ( applyCoercions
  ; applyCoercions-dual
  ; applyStores-++
  ; applyTerms-const
  ; applyTerms-preserves-No•
  ; applyTerms-preserves-Value
  ; applyTys-ℕ
  ; applyTys-ℕ-applyTys
  ; type-rename-step-⇑ᵗᵐ
  ; ↠-trans
  ; ·₂-↠
  ; ⊕₁-↠
  ; ⊕₂-↠
  )
open import proof.TermSubstitutionNarrowing using
  (term-substitution-narrowingᵗ)
open import proof.NuTermProperties using (renameᵗᵐ-reflects-Value)
open import proof.NuProgress using (canonical-ℕ; NatView; nv-const)
open import proof.NuPreservation using
  (runtime-·₁; runtime-•; runtime-⟨⟩; runtime-ν; runtime-⊕₁)

runtime-·₂-any :
  ∀ {L M} →
  RuntimeOK (L · M) →
  RuntimeOK M
runtime-·₂-any (ok-no (no•-· noL noM)) = ok-no noM
runtime-·₂-any (ok-·₁ okL noM) = ok-no noM
runtime-·₂-any (ok-·₂ vL noL okM) = okM

applyTerm-preserves-RuntimeOK :
  ∀ χ {M} →
  RuntimeOK M →
  RuntimeOK (applyTerm χ M)
applyTerm-preserves-RuntimeOK keep okM = okM
applyTerm-preserves-RuntimeOK (bind A) okM = runtime-⇑ᵗᵐ okM

applyTerms-preserves-RuntimeOK :
  ∀ χs {M} →
  RuntimeOK M →
  RuntimeOK (applyTerms χs M)
applyTerms-preserves-RuntimeOK [] okM = okM
applyTerms-preserves-RuntimeOK (χ ∷ χs) okM =
  applyTerms-preserves-RuntimeOK χs (applyTerm-preserves-RuntimeOK χ okM)

runtime-⊕₂-any :
  ∀ {L op M} →
  RuntimeOK (L ⊕[ op ] M) →
  RuntimeOK M
runtime-⊕₂-any (ok-no (no•-⊕ noL noM)) = ok-no noM
runtime-⊕₂-any (ok-⊕₁ okL noM) = ok-no noM
runtime-⊕₂-any (ok-⊕₂ vL noL okM) = okM

------------------------------------------------------------------------
-- Lemmas used by the cambridge25 top-down proof
------------------------------------------------------------------------

typed-term-narrowing-target-typing-⊒ˢ :
  ∀ {Δ σ Σ′ M M′ p A B} →
  Δ ⊢ σ ꞉ srcStoreⁿ σ ⊒ˢ Σ′ →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  Δ ∣ Σ′ ∣ [] ⊢ M′ ⦂ B
typed-term-narrowing-target-typing-⊒ˢ {Δ = Δ} {σ = σ} {Σ′ = Σ′}
    {M′ = M′} {B = B} σ⊒ M⊒M′ =
  subst
    (λ Σ₀ → Δ ∣ Σ₀ ∣ [] ⊢ M′ ⦂ B)
    (sym (tgtStoreⁿ-⊒ˢ σ⊒))
    (typed-term-narrowing-target-typing M⊒M′)

source-nat-typing :
  ∀ {Δ σ W V p A B} →
  A ≡ ‵ `ℕ →
  Δ ∣ σ ∣ [] ⊢ W ⊒ V ∶ p ⦂ A ⊒ B →
  Δ ∣ srcStoreⁿ σ ∣ [] ⊢ W ⦂ ‵ `ℕ
source-nat-typing {Δ = Δ} {σ = σ} {W = W} A≡ℕ W⊒V =
  subst (λ A → Δ ∣ srcStoreⁿ σ ∣ [] ⊢ W ⦂ A) A≡ℕ
    (typed-term-narrowing-source-typing W⊒V)

canonical-⊕-δ-step :
  ∀ {ΔL ΔR ΣL ΣR χsL χsR L R} →
  Value L →
  ΔL ∣ ΣL ∣ [] ⊢ L ⦂ ‵ `ℕ →
  Value R →
  ΔR ∣ ΣR ∣ [] ⊢ R ⦂ ‵ `ℕ →
  ∃[ m ] ∃[ n ]
    (applyTerms χsL L ⊕[ addℕ ] applyTerms χsR R
      —↠[ keep ∷ [] ] $ (κℕ (m + n)))
canonical-⊕-δ-step {χsL = χsL} {χsR = χsR} vL L⊢ vR R⊢
    with canonical-ℕ vL L⊢ | canonical-ℕ vR R⊢
canonical-⊕-δ-step {χsL = χsL} {χsR = χsR} vL L⊢ vR R⊢
    | nv-const {n = m} L≡ | nv-const {n = n} R≡
    rewrite L≡ | applyTerms-const χsL (κℕ m)
          | R≡ | applyTerms-const χsR (κℕ n) =
  m , n , ↠-step (pure-step δ-⊕) ↠-refl

constant-⊕-δ-step :
  ∀ {χsL χsR L R m n} →
  L ≡ $ (κℕ m) →
  R ≡ $ (κℕ n) →
  applyTerms χsL L ⊕[ addℕ ] applyTerms χsR R
    —↠[ keep ∷ [] ] $ (κℕ (m + n))
constant-⊕-δ-step {χsL = χsL} {χsR = χsR} {m = m} {n = n}
    L≡ R≡
    rewrite L≡ | applyTerms-const χsL (κℕ m)
          | R≡ | applyTerms-const χsR (κℕ n) =
  ↠-step (pure-step δ-⊕) ↠-refl

applyCoercion-id-ℕ :
  ∀ χ →
  applyCoercion χ (id (‵ `ℕ)) ≡ id (‵ `ℕ)
applyCoercion-id-ℕ keep = refl
applyCoercion-id-ℕ (bind A) = refl

applyCoercions-id-ℕ :
  ∀ χs →
  applyCoercions χs (id (‵ `ℕ)) ≡ id (‵ `ℕ)
applyCoercions-id-ℕ [] = refl
applyCoercions-id-ℕ (χ ∷ χs) rewrite applyCoercion-id-ℕ χ =
  applyCoercions-id-ℕ χs

applyCoercions-id-ℕ-applyCoercions :
  ∀ χs χs′ →
  applyCoercions χs′ (applyCoercions χs (id (‵ `ℕ))) ≡ id (‵ `ℕ)
applyCoercions-id-ℕ-applyCoercions χs χs′ =
  trans (cong (applyCoercions χs′) (applyCoercions-id-ℕ χs))
    (applyCoercions-id-ℕ χs′)

const-narrowing-target :
  ∀ {Δ σ γ M M′ p A B m n} →
  M ≡ $ (κℕ m) →
  M′ ≡ $ (κℕ n) →
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  m ≡ n
const-narrowing-target eqM eqM′ (extendᵗ qᶜ pαᶜ M⊒N′) =
  const-narrowing-target eqM eqM′ M⊒N′
const-narrowing-target eqM eqM′
    (splitᵗ {N = N} {α = α} {αᵢ = αᵢ} qᶜ pαᶜ N⊒N′) =
  const-narrowing-target
    (renameᵗᵐ-const-change (singleRenameᵗ αᵢ) (singleRenameᵗ α) eqM)
    eqM′
    N⊒N′
  where
    renameᵗᵐ-const-reflect :
      ∀ {ρ M κ} →
      renameᵗᵐ ρ M ≡ $ κ →
      M ≡ $ κ
    renameᵗᵐ-const-reflect {M = ` x} ()
    renameᵗᵐ-const-reflect {M = ƛ M} ()
    renameᵗᵐ-const-reflect {M = L · M} ()
    renameᵗᵐ-const-reflect {M = Λ M} ()
    renameᵗᵐ-const-reflect {M = M •} ()
    renameᵗᵐ-const-reflect {M = ν A L c} ()
    renameᵗᵐ-const-reflect {M = $ κ} refl = refl
    renameᵗᵐ-const-reflect {M = L ⊕[ op ] M} ()
    renameᵗᵐ-const-reflect {M = M ⟨ c ⟩} ()
    renameᵗᵐ-const-reflect {M = blame} ()

    renameᵗᵐ-const-change :
      ∀ ρ ρ′ {M κ} →
      renameᵗᵐ ρ M ≡ $ κ →
      renameᵗᵐ ρ′ M ≡ $ κ
    renameᵗᵐ-const-change ρ ρ′ eq
        rewrite renameᵗᵐ-const-reflect eq =
      refl
const-narrowing-target refl refl (κ⊒κᵗ (κℕ n)) = refl

value-id-ℕ-narrowing-target-const :
  ∀ {Δ σ W n} →
  Value W →
  Δ ∣ σ ∣ [] ⊢ W ⊒ $ (κℕ n)
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ →
  W ≡ $ (κℕ n)
value-id-ℕ-narrowing-target-const {W = W} vW W⊒
    with canonical-ℕ vW (typed-term-narrowing-source-typing W⊒)
value-id-ℕ-narrowing-target-const {W = W} vW W⊒
    | nv-const {n = m} W≡
    rewrite W≡ | const-narrowing-target refl refl W⊒ =
  refl

value-normalized-id-ℕ-target-const :
  ∀ {Δ σ W T p A B n} →
  Value W →
  T ≡ $ (κℕ n) →
  p ≡ id (‵ `ℕ) →
  A ≡ ‵ `ℕ →
  B ≡ ‵ `ℕ →
  Δ ∣ σ ∣ [] ⊢ W ⊒ T ∶ p ⦂ A ⊒ B →
  W ≡ $ (κℕ n)
value-normalized-id-ℕ-target-const target-value T≡ p≡ A≡ B≡ W⊒ =
  value-id-ℕ-narrowing-target-const target-value
    (subst
      (λ T → _ ∣ _ ∣ [] ⊢ _ ⊒ T ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ)
      T≡
      (subst
        (λ p → _ ∣ _ ∣ [] ⊢ _ ⊒ _ ∶ p ⦂ ‵ `ℕ ⊒ ‵ `ℕ)
        p≡
        (subst
          (λ A → _ ∣ _ ∣ [] ⊢ _ ⊒ _ ∶ _ ⦂ A ⊒ ‵ `ℕ)
          A≡
          (subst
            (λ B → _ ∣ _ ∣ [] ⊢ _ ⊒ _ ∶ _ ⦂ _ ⊒ B)
            B≡
            W⊒))))

------------------------------------------------------------------------
-- Function application simulation
------------------------------------------------------------------------

applyTerms-ƛ :
  ∀ χs N →
  applyTerms χs (ƛ N) ≡ ƛ applyTerms χs N
applyTerms-ƛ [] N = refl
applyTerms-ƛ (keep ∷ χs) N = applyTerms-ƛ χs N
applyTerms-ƛ (bind A ∷ χs) N = applyTerms-ƛ χs (⇑ᵗᵐ N)

applyCoercions-↦ :
  ∀ χs p q →
  applyCoercions χs (p ↦ q) ≡ applyCoercions χs p ↦ applyCoercions χs q
applyCoercions-↦ [] p q = refl
applyCoercions-↦ (keep ∷ χs) p q = applyCoercions-↦ χs p q
applyCoercions-↦ (bind A ∷ χs) p q =
  applyCoercions-↦ χs (⇑ᶜ p) (⇑ᶜ q)

applyCoercions-dual-applyCoercions :
  ∀ χs χs′ p →
  applyCoercions χs′ (applyCoercions χs (- p)) ≡
    - applyCoercions χs′ (applyCoercions χs p)
applyCoercions-dual-applyCoercions χs χs′ p =
  trans
    (cong (applyCoercions χs′) (applyCoercions-dual χs p))
    (applyCoercions-dual χs′ (applyCoercions χs p))

sim-beta :
  ∀ {σ WL NL WR VR}
    {ΔL σL pL qL AL BL}
    {ΔR σR AR BR} →
  ΔL ∣ σL ∣ [] ⊢ WL ⊒ ƛ NL ∶ pL ↦ qL ⦂ AL ⊒ BL →
  Value WL →
  No• WL →
  ΔR ∣ σR ∣ [] ⊢ WR ⊒ VR ∶ - pL ⦂ AR ⊒ BR →
  Value WR →
  No• WR →
  Value VR →
  ∃[ χs ] ∃[ N ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
  ∃[ C ] ∃[ D ] ∃[ r ]
    (WL · WR —↠[ χs ] N) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ N ⊒ NL [ VR ] ∶ r ⦂ C ⊒ D
sim-beta
    WL⊒ƛ vWL noWL
    WR⊒VR vWR noWR vVR =
  {! ? !}

------------------------------------------------------------------------
-- Primitive application
------------------------------------------------------------------------

⊕-δ-left-first :
  ∀ {Δ σ M N m′ n′} →
  RuntimeOK M →
  No• N →
  Δ ∣ σ ∣ [] ⊢ M ⊒ $ (κℕ m′)
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ →
  Δ ∣ σ ∣ [] ⊢ N ⊒ $ (κℕ n′)
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ →
  ∃[ χs ] ∃[ P ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
  ∃[ A′ ] ∃[ B′ ] ∃[ p′ ]
    (M ⊕[ addℕ ] N —↠[ χs ] P) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ P ⊒ $ (κℕ (m′ + n′)) ∶ p′ ⦂ A′ ⊒ B′
⊕-δ-left-first {σ = σ} {M = M} {N = N} {m′ = m′} {n′ = n′}
    okM noN M⊒M′ N⊒N′
    with catchup-lemma okM ($ (κℕ m′)) M⊒M′
⊕-δ-left-first {σ = σ} {M = M} {N = N} {m′ = m′} {n′ = n′}
    okM noN M⊒M′ N⊒N′
    | χsM , WM , ΔM , ΠM , ΠM′ , πM ,
      vWM , noWM , M↠WM , ΔM≡ , ΠM≡ , ΠM′≡ , πM⊒ , WM⊒M′ =
  let
    left-steps :
      M ⊕[ addℕ ] N —↠[ χsM ] WM ⊕[ addℕ ] applyTerms χsM N
    left-steps = ⊕₁-↠ noN M↠WM

    N⊒N′L :
      ΔM ∣ combineStoreNrw πM σ ∣ []
        ⊢ applyTerms χsM N ⊒ applyTerms χsM ($ (κℕ n′))
          ∶ applyCoercions χsM (id (‵ `ℕ))
            ⦂ applyTys χsM (‵ `ℕ) ⊒ applyTys χsM (‵ `ℕ)
    N⊒N′L = {! ? !}

    right :
      ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
        Value W ×
        No• W ×
        (applyTerms χsM N —↠[ χs ] W) ×
        (Δ′ ≡ applyTyCtxs χs ΔM) ×
        (Π ≡ applyStores χs []) ×
        (Π′ ≡ applyStore keep []) ×
        Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
        Δ′ ∣ combineStoreNrw π (combineStoreNrw πM σ) ∣ []
          ⊢ W ⊒ applyTerms χs (applyTerms χsM ($ (κℕ n′)))
            ∶ applyCoercions χs (applyCoercions χsM (id (‵ `ℕ)))
              ⦂ applyTys χs (applyTys χsM (‵ `ℕ))
                ⊒ applyTys χs (applyTys χsM (‵ `ℕ))
    right =
      catchup-lemma
        (ok-no (applyTerms-preserves-No• χsM noN))
        (applyTerms-preserves-Value χsM ($ (κℕ n′)))
        N⊒N′L

    χsR : StoreChanges
    χsR = proj₁ right

    W : Term
    W = proj₁ (proj₂ right)

    ΔR : TyCtx
    ΔR = proj₁ (proj₂ (proj₂ right))

    ΠR : Store
    ΠR =
      proj₁ (proj₂ (proj₂ (proj₂ right)))

    ΠR′ : Store
    ΠR′ =
      proj₁ (proj₂ (proj₂ (proj₂ (proj₂ right))))

    πR : StoreNrw
    πR =
      proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ right)))))

    tail :
      Value W ×
      No• W ×
      (applyTerms χsM N —↠[ χsR ] W) ×
      (ΔR ≡ applyTyCtxs χsR ΔM) ×
      (ΠR ≡ applyStores χsR []) ×
      (ΠR′ ≡ applyStore keep []) ×
      (ΔR ⊢ πR ꞉
        ΠR ⊒ˢ ΠR′) ×
      ΔR
        ∣ combineStoreNrw πR (combineStoreNrw πM σ) ∣ []
        ⊢ W ⊒ applyTerms χsR (applyTerms χsM ($ (κℕ n′)))
          ∶ applyCoercions χsR
              (applyCoercions χsM (id (‵ `ℕ)))
            ⦂ applyTys χsR (applyTys χsM (‵ `ℕ))
              ⊒ applyTys χsR (applyTys χsM (‵ `ℕ))
    tail =
      proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ right)))))

    ΠR≡ : ΠR ≡ applyStores χsR []
    ΠR≡ =
      proj₁
        (proj₂
          (proj₂
            (proj₂
              (proj₂ tail))))

    ΠR′≡ : ΠR′ ≡ applyStore keep []
    ΠR′≡ =
      proj₁
        (proj₂
          (proj₂
            (proj₂
              (proj₂
                (proj₂ tail)))))

    πR⊒ :
      ΔR ⊢ πR ꞉
        ΠR ⊒ˢ ΠR′
    πR⊒ =
      proj₁
        (proj₂
          (proj₂
            (proj₂
              (proj₂
                (proj₂
                  (proj₂ tail))))))

    vW : Value W
    vW = proj₁ tail

    N↠W :
      applyTerms χsM N —↠[ χsR ] W
    N↠W =
      proj₁
        (proj₂
          (proj₂ tail))

    operands-term : Term
    operands-term =
      applyTerms χsR WM ⊕[ addℕ ] W

    right-steps :
      WM ⊕[ addℕ ] applyTerms χsM N —↠[ χsR ] operands-term
    right-steps = ⊕₂-↠ vWM noWM N↠W

    operands-ready :
      M ⊕[ addℕ ] N —↠[ χsM ++ χsR ] operands-term
    operands-ready = ↠-trans left-steps right-steps

    WM⊢ℕ :
      _ ∣ _ ∣ [] ⊢ WM ⦂ ‵ `ℕ
    WM⊢ℕ = source-nat-typing (applyTys-ℕ χsM) WM⊒M′

    W⊒N′ :
      ΔR
        ∣ combineStoreNrw πR (combineStoreNrw πM σ) ∣ []
        ⊢ W ⊒ applyTerms χsR (applyTerms χsM ($ (κℕ n′)))
          ∶ applyCoercions χsR
              (applyCoercions χsM (id (‵ `ℕ)))
            ⦂ applyTys χsR (applyTys χsM (‵ `ℕ))
              ⊒ applyTys χsR (applyTys χsM (‵ `ℕ))
    W⊒N′ =
      proj₂
        (proj₂
          (proj₂
            (proj₂
              (proj₂
                (proj₂
                  (proj₂ tail))))))

    W⊢ℕ :
      _ ∣ _ ∣ [] ⊢ W ⦂ ‵ `ℕ
    W⊢ℕ =
      source-nat-typing
        (applyTys-ℕ-applyTys χsM χsR)
        W⊒N′

    WM≡target : WM ≡ $ (κℕ m′)
    WM≡target =
      value-normalized-id-ℕ-target-const
        vWM
        (applyTerms-const χsM (κℕ m′))
        (applyCoercions-id-ℕ χsM)
        (applyTys-ℕ χsM)
        (applyTys-ℕ χsM)
        WM⊒M′

    W≡target : W ≡ $ (κℕ n′)
    W≡target =
      value-normalized-id-ℕ-target-const
        vW
        (trans
          (cong (applyTerms χsR)
            (applyTerms-const χsM (κℕ n′)))
          (applyTerms-const χsR (κℕ n′)))
        (applyCoercions-id-ℕ-applyCoercions χsM χsR)
        (applyTys-ℕ-applyTys χsM χsR)
        (applyTys-ℕ-applyTys χsM χsR)
        W⊒N′

    source-δ :
      operands-term —↠[ keep ∷ [] ] $ (κℕ (m′ + n′))
    source-δ =
      constant-⊕-δ-step
        {χsL = χsR} {χsR = []}
        WM≡target
        W≡target

    χs : StoreChanges
    χs = (χsM ++ χsR) ++ keep ∷ []

    Δ′ : TyCtx
    Δ′ = ΔR

    Π : Store
    Π = srcStoreⁿ (combineStoreNrw πR πM)

    Π′ : Store
    Π′ = []

    π : StoreNrw
    π = combineStoreNrw πR πM

    source-steps :
      M ⊕[ addℕ ] N —↠[ χs ] $ (κℕ (m′ + n′))
    source-steps = ↠-trans operands-ready source-δ

    Π≡ : Π ≡ applyStores χs []
    Π≡ =
      trans
        (combineStoreNrw-applyStores
          {χs₂ = χsR} {χs₁ = χsM}
          πR⊒
          ΠR≡
          ΠR′≡
          πM⊒
          ΠM≡
          ΠM′≡)
        (sym (applyStores-++ (χsM ++ χsR) (keep ∷ []) []))

    Π′≡ : Π′ ≡ applyStore keep []
    Π′≡ = refl

    πM⊒-empty : Δ′ ⊢ πM ꞉ ΠM ⊒ˢ []
    πM⊒-empty =
      ⊒ˢ-empty-anyᵗ Δ′
        (subst (λ Π₀ → ΔM ⊢ πM ꞉ ΠM ⊒ˢ Π₀) ΠM′≡ πM⊒)

    πR⊒-empty :
      Δ′ ⊢ πR ꞉ ΠR ⊒ˢ []
    πR⊒-empty =
      subst
        (λ Π₀ → Δ′ ⊢ πR ꞉ ΠR ⊒ˢ Π₀)
        ΠR′≡
        πR⊒

    π⊒ : Δ′ ⊢ π ꞉ Π ⊒ˢ Π′
    π⊒ =
      combineStoreNrw-empty-⊒ˢ
        πR⊒-empty
        πM⊒-empty

    result⊒ :
      Δ′ ∣ combineStoreNrw π σ ∣ []
        ⊢ $ (κℕ (m′ + n′)) ⊒ $ (κℕ (m′ + n′))
          ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ
    result⊒ =
      κ⊒κᵗ
        (κℕ (m′ + n′))
        {typing =
          term-typing-endpoints
            (⊢$ (κℕ (m′ + n′)))
            (⊢$ (κℕ (m′ + n′)))}
  in
  χs , $ (κℕ (m′ + n′)) , Δ′ , Π , Π′ , π ,
  ‵ `ℕ , ‵ `ℕ , id (‵ `ℕ) ,
  source-steps ,
  Π≡ ,
  Π′≡ ,
  π⊒ ,
  result⊒

⊕-δ-right-first :
  ∀ {Δ σ M N m′ n′} →
  Value M →
  No• M →
  RuntimeOK N →
  Δ ∣ σ ∣ [] ⊢ M ⊒ $ (κℕ m′)
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ →
  Δ ∣ σ ∣ [] ⊢ N ⊒ $ (κℕ n′)
    ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ →
  ∃[ χs ] ∃[ P ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
  ∃[ A′ ] ∃[ B′ ] ∃[ p′ ]
    (M ⊕[ addℕ ] N —↠[ χs ] P) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ P ⊒ $ (κℕ (m′ + n′)) ∶ p′ ⦂ A′ ⊒ B′
⊕-δ-right-first {σ = σ} {M = M} {N = N} {m′ = m′} {n′ = n′}
    vM noM okN M⊒M′ N⊒N′
    with catchup-lemma okN ($ (κℕ n′)) N⊒N′
⊕-δ-right-first {σ = σ} {M = M} {N = N} {m′ = m′} {n′ = n′}
    vM noM okN M⊒M′ N⊒N′
    | χsN , WN , ΔN , ΠN , ΠN′ , πN ,
      vWN , noWN , N↠WN , ΔN≡ , ΠN≡ , ΠN′≡ , πN⊒ , WN⊒N′ =
  let
    right-steps :
      M ⊕[ addℕ ] N —↠[ χsN ] applyTerms χsN M ⊕[ addℕ ] WN
    right-steps = ⊕₂-↠ vM noM N↠WN

    M⊒M′R :
      ΔN ∣ combineStoreNrw πN σ ∣ []
        ⊢ applyTerms χsN M ⊒ applyTerms χsN ($ (κℕ m′))
          ∶ applyCoercions χsN (id (‵ `ℕ))
            ⦂ applyTys χsN (‵ `ℕ) ⊒ applyTys χsN (‵ `ℕ)
    M⊒M′R = {! ? !}

    left :
      ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
        Value W ×
        No• W ×
        (applyTerms χsN M —↠[ χs ] W) ×
        (Δ′ ≡ applyTyCtxs χs ΔN) ×
        (Π ≡ applyStores χs []) ×
        (Π′ ≡ applyStore keep []) ×
        Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
        Δ′ ∣ combineStoreNrw π (combineStoreNrw πN σ) ∣ []
          ⊢ W ⊒ applyTerms χs (applyTerms χsN ($ (κℕ m′)))
            ∶ applyCoercions χs (applyCoercions χsN (id (‵ `ℕ)))
              ⦂ applyTys χs (applyTys χsN (‵ `ℕ))
                ⊒ applyTys χs (applyTys χsN (‵ `ℕ))
    left =
      catchup-lemma
        (ok-no (applyTerms-preserves-No• χsN noM))
        (applyTerms-preserves-Value χsN ($ (κℕ m′)))
        M⊒M′R

    χsL : StoreChanges
    χsL = proj₁ left

    W : Term
    W = proj₁ (proj₂ left)

    ΔL : TyCtx
    ΔL = proj₁ (proj₂ (proj₂ left))

    ΠL : Store
    ΠL =
      proj₁ (proj₂ (proj₂ (proj₂ left)))

    ΠL′ : Store
    ΠL′ =
      proj₁ (proj₂ (proj₂ (proj₂ (proj₂ left))))

    πL : StoreNrw
    πL =
      proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ left)))))

    tail :
      Value W ×
      No• W ×
      (applyTerms χsN M —↠[ χsL ] W) ×
      (ΔL ≡ applyTyCtxs χsL ΔN) ×
      (ΠL ≡ applyStores χsL []) ×
      (ΠL′ ≡ applyStore keep []) ×
      (ΔL ⊢ πL ꞉
        ΠL ⊒ˢ ΠL′) ×
      ΔL
        ∣ combineStoreNrw πL (combineStoreNrw πN σ) ∣ []
        ⊢ W ⊒
          applyTerms χsL (applyTerms χsN ($ (κℕ m′)))
          ∶ applyCoercions χsL
              (applyCoercions χsN (id (‵ `ℕ)))
            ⦂ applyTys χsL (applyTys χsN (‵ `ℕ))
              ⊒ applyTys χsL (applyTys χsN (‵ `ℕ))
    tail =
      proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ left)))))

    ΠL≡ : ΠL ≡ applyStores χsL []
    ΠL≡ =
      proj₁
        (proj₂
          (proj₂
            (proj₂
              (proj₂ tail))))

    ΠL′≡ : ΠL′ ≡ applyStore keep []
    ΠL′≡ =
      proj₁
        (proj₂
          (proj₂
            (proj₂
              (proj₂
                (proj₂ tail)))))

    πL⊒ :
      ΔL ⊢ πL ꞉
        ΠL ⊒ˢ ΠL′
    πL⊒ =
      proj₁
        (proj₂
          (proj₂
            (proj₂
              (proj₂
                (proj₂
                  (proj₂ tail))))))

    vW : Value W
    vW = proj₁ tail

    M↠W :
      applyTerms χsN M —↠[ χsL ] W
    M↠W =
      proj₁
        (proj₂
          (proj₂ tail))

    operands-term : Term
    operands-term =
      W ⊕[ addℕ ] applyTerms χsL WN

    left-steps :
      applyTerms χsN M ⊕[ addℕ ] WN
        —↠[ χsL ] operands-term
    left-steps = ⊕₁-↠ noWN M↠W

    operands-ready :
      M ⊕[ addℕ ] N —↠[ χsN ++ χsL ] operands-term
    operands-ready = ↠-trans right-steps left-steps

    W⊒M′ :
      ΔL
        ∣ combineStoreNrw πL (combineStoreNrw πN σ) ∣ []
        ⊢ W ⊒ applyTerms χsL (applyTerms χsN ($ (κℕ m′)))
          ∶ applyCoercions χsL
              (applyCoercions χsN (id (‵ `ℕ)))
            ⦂ applyTys χsL (applyTys χsN (‵ `ℕ))
              ⊒ applyTys χsL (applyTys χsN (‵ `ℕ))
    W⊒M′ =
      proj₂
        (proj₂
          (proj₂
            (proj₂
              (proj₂
                (proj₂
                  (proj₂ tail))))))

    W⊢ℕ :
      _ ∣ _ ∣ [] ⊢ W ⦂ ‵ `ℕ
    W⊢ℕ =
      source-nat-typing
        (applyTys-ℕ-applyTys χsN χsL)
        W⊒M′

    WN⊢ℕ :
      _ ∣ _ ∣ [] ⊢ WN ⦂ ‵ `ℕ
    WN⊢ℕ = source-nat-typing (applyTys-ℕ χsN) WN⊒N′

    W≡target : W ≡ $ (κℕ m′)
    W≡target =
      value-normalized-id-ℕ-target-const
        vW
        (trans
          (cong (applyTerms χsL)
            (applyTerms-const χsN (κℕ m′)))
          (applyTerms-const χsL (κℕ m′)))
        (applyCoercions-id-ℕ-applyCoercions χsN χsL)
        (applyTys-ℕ-applyTys χsN χsL)
        (applyTys-ℕ-applyTys χsN χsL)
        W⊒M′

    WN≡target : WN ≡ $ (κℕ n′)
    WN≡target =
      value-normalized-id-ℕ-target-const
        vWN
        (applyTerms-const χsN (κℕ n′))
        (applyCoercions-id-ℕ χsN)
        (applyTys-ℕ χsN)
        (applyTys-ℕ χsN)
        WN⊒N′

    source-δ :
      operands-term —↠[ keep ∷ [] ] $ (κℕ (m′ + n′))
    source-δ =
      constant-⊕-δ-step
        {χsL = []} {χsR = χsL}
        W≡target
        WN≡target

    χs : StoreChanges
    χs = (χsN ++ χsL) ++ keep ∷ []

    Δ′ : TyCtx
    Δ′ = ΔL

    Π : Store
    Π = srcStoreⁿ (combineStoreNrw πL πN)

    Π′ : Store
    Π′ = []

    π : StoreNrw
    π = combineStoreNrw πL πN

    source-steps :
      M ⊕[ addℕ ] N —↠[ χs ] $ (κℕ (m′ + n′))
    source-steps = ↠-trans operands-ready source-δ

    Π≡ : Π ≡ applyStores χs []
    Π≡ =
      trans
        (combineStoreNrw-applyStores
          {χs₂ = χsL} {χs₁ = χsN}
          πL⊒
          ΠL≡
          ΠL′≡
          πN⊒
          ΠN≡
          ΠN′≡)
        (sym (applyStores-++ (χsN ++ χsL) (keep ∷ []) []))

    Π′≡ : Π′ ≡ applyStore keep []
    Π′≡ = refl

    πN⊒-empty : Δ′ ⊢ πN ꞉ ΠN ⊒ˢ []
    πN⊒-empty =
      ⊒ˢ-empty-anyᵗ Δ′
        (subst (λ Π₀ → ΔN ⊢ πN ꞉ ΠN ⊒ˢ Π₀) ΠN′≡ πN⊒)

    πL⊒-empty :
      Δ′ ⊢ πL ꞉ ΠL ⊒ˢ []
    πL⊒-empty =
      subst
        (λ Π₀ → Δ′ ⊢ πL ꞉ ΠL ⊒ˢ Π₀)
        ΠL′≡
        πL⊒

    π⊒ : Δ′ ⊢ π ꞉ Π ⊒ˢ Π′
    π⊒ =
      combineStoreNrw-empty-⊒ˢ
        πL⊒-empty
        πN⊒-empty

    result⊒ :
      Δ′ ∣ combineStoreNrw π σ ∣ []
        ⊢ $ (κℕ (m′ + n′)) ⊒ $ (κℕ (m′ + n′))
          ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ
    result⊒ =
      κ⊒κᵗ
        (κℕ (m′ + n′))
        {typing =
          term-typing-endpoints
            (⊢$ (κℕ (m′ + n′)))
            (⊢$ (κℕ (m′ + n′)))}
  in
  χs , $ (κℕ (m′ + n′)) , Δ′ , Π , Π′ , π ,
  ‵ `ℕ , ‵ `ℕ , id (‵ `ℕ) ,
  source-steps ,
  Π≡ ,
  Π′≡ ,
  π⊒ ,
  result⊒

------------------------------------------------------------------------
-- Dynamic gradual guarantee
------------------------------------------------------------------------

dynamicGradualGuarantee :
  ∀ {Δ σ Σ′ M M′ N′ A B p χ′} →
  StoreWf Δ (srcStoreⁿ σ) →
  RuntimeOK M →
  Δ ⊢ σ ꞉ srcStoreⁿ σ ⊒ˢ Σ′ →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  M′ —→[ χ′ ] N′ →
  ∃[ χs ] ∃[ N ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
  ∃[ A′ ] ∃[ B′ ] ∃[ p′ ]
    (M —↠[ χs ] N) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore χ′ []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ [] ⊢ N ⊒ N′ ∶ p′ ⦂ A′ ⊒ B′
dynamicGradualGuarantee wfΣ okM σ⊒ pᶜ
    M⊒M′@(α⊒αᵗ {L′ = blame} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step blame-•) =
  [] , _ , _ , [] , [] , [] , _ , _ , _ ,
  ↠-refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  ⊒blameᵗ
    {typing =
      term-typing-endpoints
        (typed-term-narrowing-source-typing M⊒M′)
        (⊢blame
          (proj₂ (coercion-wf (at wfΣ) (tag-or-idᵈ , proj₁ pαᶜ))))}
    pαᶜ
dynamicGradualGuarantee wfΣ okM σ⊒ pᶜ
    (α⊒αᵗ {γ = []} {L′ = Λ V′} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step (β-Λ• vV′))
    with catchup-lemma (runtime-• okM)
         (Λ (renameᵗᵐ-reflects-Value (extᵗ suc) V′ vV′))
         L⊒L′
dynamicGradualGuarantee wfΣ okM σ⊒ pᶜ
    (α⊒αᵗ {γ = []} {L′ = Λ V′} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step (β-Λ• vV′))
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , L↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒Λ =
  {! ? !}
dynamicGradualGuarantee wfΣ okM σ⊒ pᶜ
    (α⊒αᵗ {γ = []} {L′ = V′ ⟨ `∀ c ⟩} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step (β-∀• vV′))
    with catchup-lemma (runtime-• okM) {! ? !} L⊒L′
dynamicGradualGuarantee wfΣ okM σ⊒ pᶜ
    (α⊒αᵗ {γ = []} {L′ = V′ ⟨ `∀ c ⟩} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step (β-∀• vV′))
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , L↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒∀ =
  {! ? !}
dynamicGradualGuarantee wfΣ okM σ⊒ pᶜ
    (α⊒αᵗ {γ = []} {L′ = V′ ⟨ gen A c ⟩} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step (β-gen• vV′))
    with catchup-lemma (runtime-• okM) {! ? !} L⊒L′
dynamicGradualGuarantee wfΣ okM σ⊒ pᶜ
    (α⊒αᵗ {γ = []} {L′ = V′ ⟨ gen A c ⟩} γ′≡ qᶜ pαᶜ L⊒L′)
    (pure-step (β-gen• vV′))
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , L↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒gen =
  {! ? !}
dynamicGradualGuarantee wfΣ okM σ⊒ pᶜ
    (α⊒αᵗ γ′≡ qᶜ pαᶜ L⊒L′) red = {! ? !}
dynamicGradualGuarantee wfΣ okM σ⊒ pᶜ
    M⊒M′@(⊒αᵗ {L′ = blame} γ′≡ pαᶜ L⊒L′) (pure-step blame-•) =
  [] , _ , _ , [] , [] , [] , _ , _ , _ ,
  ↠-refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  ⊒blameᵗ
    {typing =
      term-typing-endpoints
        (typed-term-narrowing-source-typing M⊒M′)
        (⊢blame
          (proj₂ (coercion-wf (at wfΣ) (tag-or-idᵈ , proj₁ pαᶜ))))}
    pαᶜ
dynamicGradualGuarantee wfΣ okM σ⊒ pᶜ
    (⊒αᵗ {γ = []} {L′ = Λ V′} γ′≡ pαᶜ L⊒L′)
    (pure-step (β-Λ• vV′))
    with catchup-lemma {! ? !} {! ? !} L⊒L′
dynamicGradualGuarantee wfΣ okM σ⊒ pᶜ
    (⊒αᵗ {γ = []} {L′ = Λ V′} γ′≡ pαᶜ L⊒L′)
    (pure-step (β-Λ• vV′))
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , L↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒Λ =
  {! ? !}
dynamicGradualGuarantee wfΣ okM σ⊒ pᶜ
    (⊒αᵗ {γ = []} {L′ = V′ ⟨ `∀ c ⟩} γ′≡ pαᶜ L⊒L′)
    (pure-step (β-∀• vV′))
    with catchup-lemma {! ? !} {! ? !} L⊒L′
dynamicGradualGuarantee wfΣ okM σ⊒ pᶜ
    (⊒αᵗ {γ = []} {L′ = V′ ⟨ `∀ c ⟩} γ′≡ pαᶜ L⊒L′)
    (pure-step (β-∀• vV′))
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , L↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒∀ =
  {! ? !}
dynamicGradualGuarantee wfΣ okM σ⊒ pᶜ
    (⊒αᵗ {γ = []} {L′ = V′ ⟨ gen A c ⟩} γ′≡ pαᶜ L⊒L′)
    (pure-step (β-gen• vV′))
    with catchup-lemma {! ? !} {! ? !} L⊒L′
dynamicGradualGuarantee wfΣ okM σ⊒ pᶜ
    (⊒αᵗ {γ = []} {L′ = V′ ⟨ gen A c ⟩} γ′≡ pαᶜ L⊒L′)
    (pure-step (β-gen• vV′))
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , L↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒gen =
  {! ? !}
dynamicGradualGuarantee wfΣ okM σ⊒ pᶜ
    (⊒αᵗ γ′≡ pαᶜ L⊒L′) red =
  {! ? !}
dynamicGradualGuarantee {Δ = Δ} {σ = σ}
    {M = L · R} {M′ = (ƛ N′) · V′}
    wfΣ okM σ⊒ qᶜ
    (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′)
    (pure-step (β vV)) =
  let
    χsL , WL , ΔL , _ , _ , πL ,
      vWL , noWL , L↠WL , _ , _ , _ , _ , WL⊒ƛraw =
      catchup-lemma
        (runtime-·₁ okM)
        (ƛ N′)
        L⊒L′

    WL⊒ƛ :
      ΔL ∣ combineStoreNrw πL σ ∣ []
        ⊢ WL ⊒ ƛ applyTerms χsL N′
          ∶ applyCoercions χsL _ ↦ applyCoercions χsL _
            ⦂ applyTys χsL _ ⊒ applyTys χsL _
    WL⊒ƛ =
      subst
        (λ c →
          ΔL ∣ combineStoreNrw πL σ ∣ []
            ⊢ WL ⊒ ƛ applyTerms χsL N′ ∶ c
              ⦂ applyTys χsL _ ⊒ applyTys χsL _)
        (applyCoercions-↦ χsL _ _)
        (subst
          (λ T →
            ΔL ∣ combineStoreNrw πL σ ∣ []
              ⊢ WL ⊒ T ∶ applyCoercions χsL _
                ⦂ applyTys χsL _ ⊒ applyTys χsL _)
          (applyTerms-ƛ χsL N′)
          WL⊒ƛraw)

    R⊒V′L :
      ΔL ∣ combineStoreNrw πL σ ∣ []
        ⊢ applyTerms χsL R ⊒ applyTerms χsL V′
          ∶ applyCoercions χsL _
            ⦂ applyTys χsL _ ⊒ applyTys χsL _
    R⊒V′L = {! ? !}

    χsR , WR , ΔR , _ , _ , πR ,
      vWR , noWR , R↠WR , _ , _ , _ , _ , WR⊒V′raw =
      catchup-lemma
        (applyTerms-preserves-RuntimeOK χsL (runtime-·₂-any okM))
        (applyTerms-preserves-Value χsL vV)
        R⊒V′L

    WLF⊒ƛ :
      ΔR ∣ combineStoreNrw πR (combineStoreNrw πL σ) ∣ []
        ⊢ applyTerms χsR WL
          ⊒ ƛ applyTerms χsR (applyTerms χsL N′)
          ∶ applyCoercions χsR (applyCoercions χsL _)
              ↦ applyCoercions χsR (applyCoercions χsL _)
            ⦂ applyTys χsR (applyTys χsL _)
              ⊒ applyTys χsR (applyTys χsL _)
    WLF⊒ƛ = {! ? !}

    WR⊒V′ :
      ΔR ∣ combineStoreNrw πR (combineStoreNrw πL σ) ∣ []
        ⊢ WR ⊒ applyTerms χsR (applyTerms χsL V′)
          ∶ - applyCoercions χsR (applyCoercions χsL _)
            ⦂ applyTys χsR (applyTys χsL _)
              ⊒ applyTys χsR (applyTys χsL _)
    WR⊒V′ =
      subst
        (λ c →
          ΔR ∣ combineStoreNrw πR (combineStoreNrw πL σ) ∣ []
            ⊢ WR ⊒ applyTerms χsR (applyTerms χsL V′) ∶ c
              ⦂ applyTys χsR (applyTys χsL _)
                ⊒ applyTys χsR (applyTys χsL _))
        (applyCoercions-dual-applyCoercions χsL χsR _)
        WR⊒V′raw

    left-ready :
      L · R —↠[ χsL ] WL · applyTerms χsL R
    left-ready = {! ? !}

    right-ready :
      WL · applyTerms χsL R —↠[ χsR ] applyTerms χsR WL · WR
    right-ready = ·₂-↠ vWL noWL R↠WR

    ready :
      ∃[ χs₀ ] (L · R —↠[ χs₀ ] applyTerms χsR WL · WR)
    ready = χsL ++ χsR , ↠-trans left-ready right-ready

    tail :
      ∃[ χs ] ∃[ N ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
      ∃[ C ] ∃[ D ] ∃[ r ]
        (applyTerms χsR WL · WR —↠[ χs ] N) ×
        (Π ≡ applyStores χs []) ×
        (Π′ ≡ []) ×
        Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
        Δ′ ∣ combineStoreNrw π
               (combineStoreNrw πR (combineStoreNrw πL σ)) ∣ []
          ⊢ N ⊒
              (applyTerms χsR (applyTerms χsL N′))
              [ applyTerms χsR (applyTerms χsL V′) ]
            ∶ r ⦂ C ⊒ D
    tail =
      sim-beta
        WLF⊒ƛ
        (applyTerms-preserves-Value χsR vWL)
        (applyTerms-preserves-No• χsR noWL)
        WR⊒V′
        vWR
        noWR
        (applyTerms-preserves-Value χsR
          (applyTerms-preserves-Value χsL vV))
  in
  {! ? !}
dynamicGradualGuarantee wfΣ okM σ⊒ qᶜ
    (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′)
    (ξ-·₁ L′→N′ shiftM) =
  let
    rec =
      dynamicGradualGuarantee
        wfΣ
        (runtime-·₁ okM)
        σ⊒
        p↦qᶜ
        L⊒L′
        L′→N′
  in
  {! ? !}
dynamicGradualGuarantee {σ = σ} wfΣ (ok-no (no•-⊕ noM noN)) σ⊒ qᶜ
    (⊕⊒⊕ᵗ {M = M} {N = N} M⊒M′ N⊒N′)
    (pure-step (δ-⊕ {m = m′} {n = n′})) =
  ⊕-δ-left-first {σ = σ} {M = M} {N = N}
    {m′ = m′} {n′ = n′}
    (ok-no noM) noN M⊒M′ N⊒N′
dynamicGradualGuarantee {σ = σ} wfΣ (ok-⊕₁ okM noN) σ⊒ qᶜ
    (⊕⊒⊕ᵗ {M = M} {N = N} M⊒M′ N⊒N′)
    (pure-step (δ-⊕ {m = m′} {n = n′})) =
  ⊕-δ-left-first {σ = σ} {M = M} {N = N}
    {m′ = m′} {n′ = n′}
    okM noN M⊒M′ N⊒N′
dynamicGradualGuarantee {σ = σ} wfΣ (ok-⊕₂ vM noM okN) σ⊒ qᶜ
    (⊕⊒⊕ᵗ {M = M} {N = N} M⊒M′ N⊒N′)
    (pure-step (δ-⊕ {m = m′} {n = n′})) =
  ⊕-δ-right-first {σ = σ} {M = M} {N = N}
    {m′ = m′} {n′ = n′}
    vM noM okN M⊒M′ N⊒N′
dynamicGradualGuarantee wfΣ okM σ⊒ qᶜ
    (⊒cast+ᵗ {s = id A} q₀ᶜ wfΠ q⊒ s⊒ q⨟s≈r M⊒M′)
    (pure-step (β-id vV))
    with catchup-lemma okM vV M⊒M′
dynamicGradualGuarantee wfΣ okM σ⊒ qᶜ
    (⊒cast+ᵗ {s = id A} q₀ᶜ wfΠ q⊒ s⊒ q⨟s≈r M⊒M′)
    (pure-step (β-id vV))
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , M↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒M′ =
  {! ? !}
dynamicGradualGuarantee wfΣ okM σ⊒ qᶜ
    (⊒cast-ᵗ {s = id A} q₀ᶜ rᶜ wfΠ q⊒ s⊒ q⨟s≈r M⊒M′)
    (pure-step (β-id vV))
    with catchup-lemma okM vV M⊒M′
dynamicGradualGuarantee wfΣ okM σ⊒ qᶜ
    (⊒cast-ᵗ {s = id A} q₀ᶜ rᶜ wfΠ q⊒ s⊒ q⨟s≈r M⊒M′)
    (pure-step (β-id vV))
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , noW , M↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒M′ =
  {! ? !}
dynamicGradualGuarantee wfΣ okM σ⊒ pᶜ M⊒M′ M′→N′ = {! ? !}
