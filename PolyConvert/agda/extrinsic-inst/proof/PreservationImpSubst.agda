module proof.PreservationImpSubst where

-- File Charter:
--   * Type-variable substitution preservation for PolyConvert imprecision typing.
--   * Proves the general `⊑-substᵗ-wt` theorem for `substImp` under
--     well-formed type substitutions and mode-aware variable evidence.
--   * Exports the `singleTyEnv` corollary `[]⊑ᵗ-wt` used by raw preservation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; _∨_)
open import Data.List using ([]; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _<_; z<s; s<s)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import proof.TypeProperties
  using
    ( TySubstWf
    ; TySubstWf-exts
    ; occurs-raise
    ; occurs-raise-fresh
    ; singleTyEnv-Wf
    ; substᵗ-ground
    ; substᵗ-preserves-WfTy
    )
open import Imprecision
open import proof.ImprecisionProperties
  using
    ( VarSubst
    ; cong-⊢⊑
    ; length-plains[]
    ; lookup-mode
    ; plain-var-subst
    ; wkImpAt
    ; wk-VarSubst
    )

------------------------------------------------------------------------
-- Occurrence preservation for binder-protected substitutions
------------------------------------------------------------------------

extsFrom : ℕ → Substᵗ → Substᵗ
extsFrom zero σ = σ
extsFrom (suc k) σ = extsᵗ (extsFrom k σ)

extsFrom-protect-var :
  ∀ k σ X Y →
  X < k →
  occurs X (extsFrom k σ Y) ≡ occurs X (＇ Y)
extsFrom-protect-var zero σ X Y ()
extsFrom-protect-var (suc k) σ X zero X<sk = refl
extsFrom-protect-var (suc k) σ zero (suc Y) z<s =
  occurs-raise-fresh zero (extsFrom k σ Y)
extsFrom-protect-var (suc k) σ (suc X) (suc Y) (s<s X<k) =
  trans
    (occurs-raise zero X (extsFrom k σ Y))
    (trans
      (extsFrom-protect-var k σ X Y X<k)
      (sym (occurs-raise zero X (＇ Y))))

occurs-subst-protected :
  ∀ k σ X A →
  X < k →
  occurs X (substᵗ (extsFrom k σ) A) ≡ occurs X A
occurs-subst-protected k σ X (＇ Y) X<k =
  extsFrom-protect-var k σ X Y X<k
occurs-subst-protected k σ X (｀ α) X<k = refl
occurs-subst-protected k σ X (‵ ι) X<k = refl
occurs-subst-protected k σ X ★ X<k = refl
occurs-subst-protected k σ X (A ⇒ B) X<k
  rewrite occurs-subst-protected k σ X A X<k
        | occurs-subst-protected k σ X B X<k = refl
occurs-subst-protected k σ X (`∀ A) X<k =
  occurs-subst-protected (suc k) σ (suc X) A (s<s X<k)

occurs-subst-exts-zero :
  ∀ σ A →
  occurs zero (substᵗ (extsᵗ σ) A) ≡ occurs zero A
occurs-subst-exts-zero σ A =
  occurs-subst-protected (suc zero) σ zero A z<s

------------------------------------------------------------------------
-- Mode-aware type substitutions for imprecision evidence
------------------------------------------------------------------------

ImpSubstWt : SealCtx → VarPrecCtx → VarPrecCtx → Substᵗ → Set
ImpSubstWt Ψ Γ Γ′ σ =
  ∀ {X m} →
  Γ ∋ X ∶ m →
  VarSubst Ψ Γ′ (σ X) m

ImpSubstWt-exts :
  ∀ {Ψ Γ Γ′ σ m′} →
  ImpSubstWt Ψ Γ Γ′ σ →
  ImpSubstWt Ψ (m′ ∷ Γ) (m′ ∷ Γ′) (extsᵗ σ)
ImpSubstWt-exts {m′ = X⊑X} hσ here = ⊢X-⊑-X here
ImpSubstWt-exts {m′ = X⊑★} hσ here = ⊢X-⊑-★ here
ImpSubstWt-exts {m′ = m′} hσ (there x∈) =
  wk-VarSubst {m′ = m′} (hσ x∈)

------------------------------------------------------------------------
-- Parallel substitution that sends all X⊑★ variables to ★
------------------------------------------------------------------------

ν★Subst : VarPrecCtx → Substᵗ
ν★Subst [] X = ＇ X
ν★Subst (X⊑X ∷ Γ) zero = ＇ zero
ν★Subst (X⊑X ∷ Γ) (suc X) = ⇑ᵗ (ν★Subst Γ X)
ν★Subst (X⊑★ ∷ Γ) zero = ★
ν★Subst (X⊑★ ∷ Γ) (suc X) = ⇑ᵗ (ν★Subst Γ X)

ν★Subst-plain-exts :
  ∀ Γ X →
  ν★Subst (X⊑X ∷ Γ) X ≡ extsᵗ (ν★Subst Γ) X
ν★Subst-plain-exts Γ zero = refl
ν★Subst-plain-exts Γ (suc X) = refl

wk-ν★-var-⊑ :
  ∀ {Ψ Γ X p m′} →
  Ψ ∣ Γ ⊢ p ⦂ ＇ X ⊑ ν★Subst Γ X →
  Ψ ∣ (m′ ∷ Γ) ⊢ renameImp suc p ⦂
    ＇ suc X ⊑ ⇑ᵗ (ν★Subst Γ X)
wk-ν★-var-⊑ p⊢ = wkImpAt {Φ = []} p⊢

ν★-var-⊑ :
  ∀ {Ψ Γ X m} →
  Γ ∋ X ∶ m →
  ∃[ p ] Ψ ∣ Γ ⊢ p ⦂ ＇ X ⊑ ν★Subst Γ X
ν★-var-⊑ {Γ = X⊑X ∷ Γ} here =
  X-⊑-X zero , ⊢X-⊑-X here
ν★-var-⊑ {Γ = X⊑★ ∷ Γ} here =
  X-⊑-★ zero , ⊢X-⊑-★ here
ν★-var-⊑ {Γ = X⊑X ∷ Γ} {X = suc X} (there x∈)
    with ν★-var-⊑ x∈
ν★-var-⊑ {Γ = X⊑X ∷ Γ} {X = suc X} (there x∈) | p , p⊢ =
  renameImp suc p , wk-ν★-var-⊑ p⊢
ν★-var-⊑ {Γ = X⊑★ ∷ Γ} {X = suc X} (there x∈)
    with ν★-var-⊑ x∈
ν★-var-⊑ {Γ = X⊑★ ∷ Γ} {X = suc X} (there x∈) | p , p⊢ =
  renameImp suc p , wk-ν★-var-⊑ p⊢

ν★-⊑ :
  ∀ {Ψ Γ A} →
  WfTy (length Γ) Ψ A →
  ∃[ p ] Ψ ∣ Γ ⊢ p ⦂ A ⊑ substᵗ (ν★Subst Γ) A
ν★-⊑ {Γ = Γ} (wfVar X<Γ) with lookup-mode Γ X<Γ
ν★-⊑ {Γ = Γ} (wfVar X<Γ) | m , x∈ = ν★-var-⊑ x∈
ν★-⊑ (wfSeal α<Ψ) = α-⊑-α _ , ⊢α-⊑-α (wfSeal α<Ψ)
ν★-⊑ wfBase = ι-⊑-ι _ , ⊢ι-⊑-ι
ν★-⊑ wf★ = ★-⊑-★ , ⊢★-⊑-★
ν★-⊑ (wf⇒ wfA wfB) with ν★-⊑ wfA | ν★-⊑ wfB
ν★-⊑ (wf⇒ wfA wfB) | p , p⊢ | q , q⊢ =
  A⇒B-⊑-A′⇒B′ p q , ⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢
ν★-⊑ {Γ = Γ} {A = `∀ A} (wf∀ wfA)
    with ν★-⊑ {Γ = X⊑X ∷ Γ} wfA
ν★-⊑ {Γ = Γ} {A = `∀ A} (wf∀ wfA) | p , p⊢ =
  ∀A-⊑-∀B p ,
  ⊢∀A-⊑-∀B
    (cong-⊢⊑
      refl
      (substᵗ-cong (ν★Subst-plain-exts Γ) A)
      p⊢)

ν★Subst-plains-id :
  ∀ Δ X →
  ν★Subst (plains Δ []) X ≡ ＇ X
ν★Subst-plains-id zero X = refl
ν★Subst-plains-id (suc Δ) zero = refl
ν★Subst-plains-id (suc Δ) (suc X) =
  cong ⇑ᵗ (ν★Subst-plains-id Δ X)

singleν★Subst : Substᵗ
singleν★Subst zero = ★
singleν★Subst (suc X) = ＇ suc X

ν★Subst-singleν★ :
  ∀ Δ X →
  ν★Subst (X⊑★ ∷ plains Δ []) X ≡ singleν★Subst X
ν★Subst-singleν★ Δ zero = refl
ν★Subst-singleν★ Δ (suc X) = cong ⇑ᵗ (ν★Subst-plains-id Δ X)

ν★-⊑-single :
  ∀ {Δ Ψ A} →
  WfTy (suc Δ) Ψ A →
  ∃[ p ] Ψ ∣ (X⊑★ ∷ plains Δ []) ⊢ p ⦂
    A ⊑ substᵗ singleν★Subst A
ν★-⊑-single {Δ = Δ} {A = A} wfA
    with ν★-⊑ {Γ = X⊑★ ∷ plains Δ []}
      (subst (λ n → WfTy (suc n) _ A) (sym (length-plains[] Δ)) wfA)
ν★-⊑-single {Δ = Δ} {A = A} wfA | p , p⊢ =
  p ,
  cong-⊢⊑
    refl
    (substᵗ-cong (ν★Subst-singleν★ Δ) A)
    p⊢

------------------------------------------------------------------------
-- Plain contexts provide reflexive imprecision for well-formed types
------------------------------------------------------------------------

plains-lookup :
  ∀ {Δ X} →
  X < Δ →
  plains Δ [] ∋ X ∶ X⊑X
plains-lookup {Δ = zero} ()
plains-lookup {Δ = suc Δ} {X = zero} z<s = here
plains-lookup {Δ = suc Δ} {X = suc X} (s<s X<Δ) =
  there (plains-lookup X<Δ)

reflImp-wt-plains :
  ∀ {Δ Ψ A} →
  WfTy Δ Ψ A →
  Ψ ∣ plains Δ [] ⊢ reflImp A ⦂ A ⊑ A
reflImp-wt-plains (wfVar X<Δ) =
  ⊢X-⊑-X (plains-lookup X<Δ)
reflImp-wt-plains (wfSeal α<Ψ) = ⊢α-⊑-α (wfSeal α<Ψ)
reflImp-wt-plains wfBase = ⊢ι-⊑-ι
reflImp-wt-plains wf★ = ⊢★-⊑-★
reflImp-wt-plains (wf⇒ wfA wfB) =
  ⊢A⇒B-⊑-A′⇒B′ (reflImp-wt-plains wfA) (reflImp-wt-plains wfB)
reflImp-wt-plains (wf∀ wfA) = ⊢∀A-⊑-∀B (reflImp-wt-plains wfA)

singleTyEnv-ImpSubstWt :
  ∀ {Δ Ψ T} →
  WfTy Δ Ψ T →
  ImpSubstWt Ψ (X⊑X ∷ plains Δ []) (plains Δ []) (singleTyEnv T)
singleTyEnv-ImpSubstWt wfT here = reflImp-wt-plains wfT
singleTyEnv-ImpSubstWt wfT (there x∈) = plain-var-subst x∈

singleTyEnv-TySubstWf-plains :
  ∀ {Δ Ψ T} →
  WfTy Δ Ψ T →
  TySubstWf
    (length (X⊑X ∷ plains Δ []))
    (length (plains Δ []))
    Ψ
    (singleTyEnv T)
singleTyEnv-TySubstWf-plains {Δ = Δ} {T = T} wfT
  rewrite length-plains[] Δ =
  singleTyEnv-Wf T wfT

------------------------------------------------------------------------
-- Type-variable substitution preserves imprecision typing
------------------------------------------------------------------------

⊑-substᵗ-wt :
  ∀ {Ψ Γ Γ′ σ p A B} →
  TySubstWf (length Γ) (length Γ′) Ψ σ →
  ImpSubstWt Ψ Γ Γ′ σ →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  Ψ ∣ Γ′ ⊢ substImp σ p ⦂ substᵗ σ A ⊑ substᵗ σ B
⊑-substᵗ-wt hσ hᵢ ⊢★-⊑-★ = ⊢★-⊑-★
⊑-substᵗ-wt hσ hᵢ (⊢X-⊑-★ xν) = hᵢ xν
⊑-substᵗ-wt hσ hᵢ (⊢A-⊑-★ g p⊢) =
  ⊢A-⊑-★ (substᵗ-ground _ g) (⊑-substᵗ-wt hσ hᵢ p⊢)
⊑-substᵗ-wt hσ hᵢ (⊢X-⊑-X x∈) = hᵢ x∈
⊑-substᵗ-wt hσ hᵢ (⊢α-⊑-α (wfSeal α<Ψ)) = ⊢α-⊑-α (wfSeal α<Ψ)
⊑-substᵗ-wt hσ hᵢ ⊢ι-⊑-ι = ⊢ι-⊑-ι
⊑-substᵗ-wt hσ hᵢ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  ⊢A⇒B-⊑-A′⇒B′ (⊑-substᵗ-wt hσ hᵢ p⊢) (⊑-substᵗ-wt hσ hᵢ q⊢)
⊑-substᵗ-wt hσ hᵢ (⊢∀A-⊑-∀B p⊢) =
  ⊢∀A-⊑-∀B (⊑-substᵗ-wt (TySubstWf-exts hσ) (ImpSubstWt-exts hᵢ) p⊢)
⊑-substᵗ-wt {σ = σ} hσ hᵢ (⊢∀A-⊑-B {A = A} {B = B} wfB p⊢) =
  ⊢∀A-⊑-B
    (substᵗ-preserves-WfTy wfB hσ)
    (cong-⊢⊑
      refl
      (substᵗ-suc-renameᵗ-suc σ B)
      (⊑-substᵗ-wt (TySubstWf-exts hσ) (ImpSubstWt-exts hᵢ) p⊢))

[]⊑ᵗ-wt :
  ∀ {Δ Ψ}{p : Imp}{A B T : Ty} →
  Ψ ∣ (X⊑X ∷ plains Δ []) ⊢ p ⦂ A ⊑ B →
  WfTy Δ Ψ T →
  Ψ ∣ plains Δ [] ⊢ p [ T ]⊑ ⦂
    src⊑ p [ T ]ᵗ ⊑ tgt⊑ p [ T ]ᵗ
[]⊑ᵗ-wt {Δ = Δ} {T = T} p⊢ wfT =
  cong-⊢⊑
    (cong (λ A → A [ T ]ᵗ) (sym (src⊑-correct p⊢)))
    (cong (λ B → B [ T ]ᵗ) (sym (tgt⊑-correct p⊢)))
    (⊑-substᵗ-wt
      (singleTyEnv-TySubstWf-plains wfT)
      (singleTyEnv-ImpSubstWt wfT)
      p⊢)
