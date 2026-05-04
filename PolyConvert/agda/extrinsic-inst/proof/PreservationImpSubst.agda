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
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import proof.TypeProperties
  using
    ( TySubstWf
    ; TySubstWf-exts
    ; singleTyEnv-Wf
    ; substᵗ-ground
    ; substᵗ-preserves-WfTy
    )
open import Imprecision
open import proof.PreservationBetaUpNu
  using
    ( VarSubst
    ; cong-⊢⊑
    ; length-plains[]
    ; occurs-raise
    ; occurs-raise-fresh
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

ImpSubstWt : SealCtx → ICtx → ICtx → Substᵗ → Set
ImpSubstWt Ψ Γ Γ′ σ =
  ∀ {X m} →
  Γ ∋ X ∶ m →
  VarSubst Ψ Γ′ (σ X) m

ImpSubstWt-exts :
  ∀ {Ψ Γ Γ′ σ m′} →
  ImpSubstWt Ψ Γ Γ′ σ →
  ImpSubstWt Ψ (m′ ∷ Γ) (m′ ∷ Γ′) (extsᵗ σ)
ImpSubstWt-exts {m′ = plain} hσ here = ⊑-＇ here
ImpSubstWt-exts {m′ = ν-bound} hσ here = ⊑-★ν here
ImpSubstWt-exts {m′ = m′} hσ (there x∈) =
  wk-VarSubst {m′ = m′} (hσ x∈)

------------------------------------------------------------------------
-- Plain contexts provide reflexive imprecision for well-formed types
------------------------------------------------------------------------

plains-lookup :
  ∀ {Δ X} →
  X < Δ →
  plains Δ [] ∋ X ∶ plain
plains-lookup {Δ = zero} ()
plains-lookup {Δ = suc Δ} {X = zero} z<s = here
plains-lookup {Δ = suc Δ} {X = suc X} (s<s X<Δ) =
  there (plains-lookup X<Δ)

reflImp-wt-plains :
  ∀ {Δ Ψ A} →
  WfTy Δ Ψ A →
  Ψ ∣ plains Δ [] ⊢ reflImp A ⦂ A ⊑ A
reflImp-wt-plains (wfVar X<Δ) = ⊑-＇ (plains-lookup X<Δ)
reflImp-wt-plains (wfSeal α<Ψ) = ⊑-｀ (wfSeal α<Ψ)
reflImp-wt-plains wfBase = ⊑-‵
reflImp-wt-plains wf★ = ⊑-★★
reflImp-wt-plains (wf⇒ wfA wfB) =
  ⊑-⇒ (reflImp-wt-plains wfA) (reflImp-wt-plains wfB)
reflImp-wt-plains (wf∀ wfA) = ⊑-∀ (reflImp-wt-plains wfA)

plain-var-subst :
  ∀ {Δ Ψ X m} →
  plains Δ [] ∋ X ∶ m →
  VarSubst Ψ (plains Δ []) (＇ X) m
plain-var-subst {Δ = zero} ()
plain-var-subst {Δ = suc Δ} here = ⊑-＇ here
plain-var-subst {Δ = suc Δ} {Ψ = Ψ} (there x∈) =
  wk-VarSubst {m′ = plain} (plain-var-subst {Ψ = Ψ} x∈)

singleTyEnv-ImpSubstWt :
  ∀ {Δ Ψ T} →
  WfTy Δ Ψ T →
  ImpSubstWt Ψ (plain ∷ plains Δ []) (plains Δ []) (singleTyEnv T)
singleTyEnv-ImpSubstWt wfT here = reflImp-wt-plains wfT
singleTyEnv-ImpSubstWt wfT (there x∈) = plain-var-subst x∈

singleTyEnv-TySubstWf-plains :
  ∀ {Δ Ψ T} →
  WfTy Δ Ψ T →
  TySubstWf
    (length (plain ∷ plains Δ []))
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
⊑-substᵗ-wt hσ hᵢ ⊑-★★ = ⊑-★★
⊑-substᵗ-wt hσ hᵢ (⊑-★ν xν) = hᵢ xν
⊑-substᵗ-wt hσ hᵢ (⊑-★ g p⊢) =
  ⊑-★ (substᵗ-ground _ g) (⊑-substᵗ-wt hσ hᵢ p⊢)
⊑-substᵗ-wt hσ hᵢ (⊑-＇ x∈) = hᵢ x∈
⊑-substᵗ-wt hσ hᵢ (⊑-｀ (wfSeal α<Ψ)) = ⊑-｀ (wfSeal α<Ψ)
⊑-substᵗ-wt hσ hᵢ ⊑-‵ = ⊑-‵
⊑-substᵗ-wt hσ hᵢ (⊑-⇒ p⊢ q⊢) =
  ⊑-⇒ (⊑-substᵗ-wt hσ hᵢ p⊢) (⊑-substᵗ-wt hσ hᵢ q⊢)
⊑-substᵗ-wt hσ hᵢ (⊑-∀ p⊢) =
  ⊑-∀ (⊑-substᵗ-wt (TySubstWf-exts hσ) (ImpSubstWt-exts hᵢ) p⊢)
⊑-substᵗ-wt {σ = σ} hσ hᵢ (⊑-ν {A = A} {B = B} wfB occ p⊢) =
  ⊑-ν
    (substᵗ-preserves-WfTy wfB hσ)
    (trans (occurs-subst-exts-zero σ A) occ)
    (cong-⊢⊑
      refl
      (substᵗ-suc-renameᵗ-suc σ B)
      (⊑-substᵗ-wt (TySubstWf-exts hσ) (ImpSubstWt-exts hᵢ) p⊢))

[]⊑ᵗ-wt :
  ∀ {Δ Ψ}{p : Imp}{A B T : Ty} →
  Ψ ∣ (plain ∷ plains Δ []) ⊢ p ⦂ A ⊑ B →
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
