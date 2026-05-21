module proof.PreservationImpSubst where

-- File Charter:
--   * Type-variable substitution preservation for PolyConvert imprecision typing.
--   * Proves the general `⊑-substᵗ-wt` theorem for `substImp` under
--     well-formed type substitutions and mode-aware variable evidence.
--   * Exports the `singleTyEnv` corollary `[]⊑ᵗ-wt` used by raw preservation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; _∨_)
open import Data.List using ([]; _∷_; length)
open import Data.Nat using (ℕ; _+_; zero; suc; _<_; z<s; s<s)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_)
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
    ; extend-X⊑X-lookup
    ; length-extend-X⊑X[]
    ; lookup-mode
    ; plain-var-subst
    ; reflImp-wt-extend-X⊑X
    ; src⊑-correct
    ; tgt⊑-correct
    ; wkImpAt
    ; wk-VarSubst
    )
open import proof.PreservationTermSubst using (wkImp-extend-X⊑X)

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

VarSubstRel : SealCtx → VarPrecCtx → Ty → Ty → VarPrec → Set
VarSubstRel Ψ Γ A B X⊑X = Σ[ p ∈ Imp ] Ψ ∣ Γ ⊢ p ⦂ A ⊑ B
VarSubstRel Ψ Γ A B X⊑★ = Σ[ p ∈ Imp ] Ψ ∣ Γ ⊢ p ⦂ A ⊑ ★

ImpSubstRel : SealCtx → VarPrecCtx → VarPrecCtx → Substᵗ → Substᵗ → Set
ImpSubstRel Ψ Γ Γ′ σ τ =
  ∀ {X m} →
  Γ ∋ X ∶ m →
  VarSubstRel Ψ Γ′ (σ X) (τ X) m

wk-VarSubstRel :
  ∀ {Ψ Γ A B m m′} →
  VarSubstRel Ψ Γ A B m →
  VarSubstRel Ψ (m′ ∷ Γ) (⇑ᵗ A) (⇑ᵗ B) m
wk-VarSubstRel {m = X⊑X} (p , p⊢) =
  renameImp suc p , wkImpAt {Φ = []} p⊢
wk-VarSubstRel {m = X⊑★} (p , p⊢) =
  renameImp suc p , wkImpAt {Φ = []} p⊢

ImpSubstRel-exts :
  ∀ {Ψ Γ Γ′ σ τ m′} →
  ImpSubstRel Ψ Γ Γ′ σ τ →
  ImpSubstRel Ψ (m′ ∷ Γ) (m′ ∷ Γ′) (extsᵗ σ) (extsᵗ τ)
ImpSubstRel-exts {m′ = X⊑X} h here = X-⊑-X zero , ⊢X-⊑-X here
ImpSubstRel-exts {m′ = X⊑★} h here = X-⊑-★ zero , ⊢X-⊑-★ here
ImpSubstRel-exts {m′ = m′} h (there x∈) =
  wk-VarSubstRel {m′ = m′} (h x∈)

VarSubst⊑Rel : SealCtx → VarPrecCtx → Imp → Ty → Ty → VarPrec → Set
VarSubst⊑Rel Ψ Γ p A B X⊑X = Ψ ∣ Γ ⊢ p ⦂ A ⊑ B
VarSubst⊑Rel Ψ Γ p A B X⊑★ = Ψ ∣ Γ ⊢ p ⦂ A ⊑ ★

ImpSubst⊑Rel :
  SealCtx → VarPrecCtx → VarPrecCtx → Subst⊑ → Substᵗ → Substᵗ → Set
ImpSubst⊑Rel Ψ Γ Γ′ σ τˡ τʳ =
  ∀ {X m} →
  Γ ∋ X ∶ m →
  VarSubst⊑Rel Ψ Γ′ (σ X m) (τˡ X) (τʳ X) m

wk-VarSubst⊑Rel :
  ∀ {Ψ Γ p A B m m′} →
  VarSubst⊑Rel Ψ Γ p A B m →
  VarSubst⊑Rel Ψ (m′ ∷ Γ) (renameImp suc p) (⇑ᵗ A) (⇑ᵗ B) m
wk-VarSubst⊑Rel {m = X⊑X} p⊢ = wkImpAt {Φ = []} p⊢
wk-VarSubst⊑Rel {m = X⊑★} p⊢ = wkImpAt {Φ = []} p⊢

ImpSubst⊑Rel-exts :
  ∀ {Ψ Γ Γ′ σ τˡ τʳ m′} →
  ImpSubst⊑Rel Ψ Γ Γ′ σ τˡ τʳ →
  ImpSubst⊑Rel Ψ (m′ ∷ Γ) (m′ ∷ Γ′)
    (exts⊑ σ) (extsᵗ τˡ) (extsᵗ τʳ)
ImpSubst⊑Rel-exts {m′ = X⊑X} h here =
  ⊢X-⊑-X here
ImpSubst⊑Rel-exts {m′ = X⊑★} h here =
  ⊢X-⊑-★ here
ImpSubst⊑Rel-exts {m′ = m′} h (there x∈) =
  wk-VarSubst⊑Rel {m′ = m′} (h x∈)

⊑-subst⊑-rel :
  ∀ {Ψ Γ Γ′ σ τˡ τʳ p A B} →
  TySubstWf (length Γ) (length Γ′) Ψ τʳ →
  ImpSubst⊑Rel Ψ Γ Γ′ σ τˡ τʳ →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  Ψ ∣ Γ′ ⊢ subst⊑ σ p ⦂ substᵗ τˡ A ⊑ substᵗ τʳ B
⊑-subst⊑-rel hτʳ hᵢ ⊢★-⊑-★ = ⊢★-⊑-★
⊑-subst⊑-rel hτʳ hᵢ (⊢X-⊑-★ xν) = hᵢ xν
⊑-subst⊑-rel hτʳ hᵢ (⊢A-⊑-★ g p⊢) =
  ⊢A-⊑-★ (substᵗ-ground _ g) (⊑-subst⊑-rel hτʳ hᵢ p⊢)
⊑-subst⊑-rel hτʳ hᵢ (⊢X-⊑-X x∈) = hᵢ x∈
⊑-subst⊑-rel hτʳ hᵢ (⊢α-⊑-α (wfSeal α<Ψ)) =
  ⊢α-⊑-α (wfSeal α<Ψ)
⊑-subst⊑-rel hτʳ hᵢ ⊢ι-⊑-ι = ⊢ι-⊑-ι
⊑-subst⊑-rel hτʳ hᵢ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  ⊢A⇒B-⊑-A′⇒B′
    (⊑-subst⊑-rel hτʳ hᵢ p⊢)
    (⊑-subst⊑-rel hτʳ hᵢ q⊢)
⊑-subst⊑-rel hτʳ hᵢ (⊢∀A-⊑-∀B p⊢) =
  ⊢∀A-⊑-∀B
    (⊑-subst⊑-rel (TySubstWf-exts hτʳ) (ImpSubst⊑Rel-exts hᵢ) p⊢)
⊑-subst⊑-rel {τʳ = τʳ} hτʳ hᵢ (⊢∀A-⊑-B {B = B} wfB p⊢) =
  ⊢∀A-⊑-B
    (substᵗ-preserves-WfTy wfB hτʳ)
    (cong-⊢⊑
      refl
      (substᵗ-suc-renameᵗ-suc τʳ B)
      (⊑-subst⊑-rel
        (TySubstWf-exts hτʳ) (ImpSubst⊑Rel-exts hᵢ) p⊢))

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

ν★Subst-extend-X⊑X-id :
  ∀ Δ X →
  ν★Subst (extend-X⊑X Δ []) X ≡ ＇ X
ν★Subst-extend-X⊑X-id zero X = refl
ν★Subst-extend-X⊑X-id (suc Δ) zero = refl
ν★Subst-extend-X⊑X-id (suc Δ) (suc X) =
  cong ⇑ᵗ (ν★Subst-extend-X⊑X-id Δ X)

singleν★Subst : Substᵗ
singleν★Subst zero = ★
singleν★Subst (suc X) = ＇ suc X

ν★Subst-singleν★ :
  ∀ Δ X →
  ν★Subst (X⊑★ ∷ extend-X⊑X Δ []) X ≡ singleν★Subst X
ν★Subst-singleν★ Δ zero = refl
ν★Subst-singleν★ Δ (suc X) = cong ⇑ᵗ (ν★Subst-extend-X⊑X-id Δ X)

ν★-⊑-single :
  ∀ {Δ Ψ A} →
  WfTy (suc Δ) Ψ A →
  ∃[ p ] Ψ ∣ (X⊑★ ∷ extend-X⊑X Δ []) ⊢ p ⦂
    A ⊑ substᵗ singleν★Subst A
ν★-⊑-single {Δ = Δ} {A = A} wfA
    with ν★-⊑ {Γ = X⊑★ ∷ extend-X⊑X Δ []}
      (subst (λ n → WfTy (suc n) _ A) (sym (length-extend-X⊑X[] Δ)) wfA)
ν★-⊑-single {Δ = Δ} {A = A} wfA | p , p⊢ =
  p ,
  cong-⊢⊑
    refl
    (substᵗ-cong (ν★Subst-singleν★ Δ) A)
    p⊢

------------------------------------------------------------------------
-- Plain contexts provide reflexive imprecision for well-formed types
------------------------------------------------------------------------

tysubst-right-at-⊑ :
  ∀ k {Δ A T T′ pT} →
  WfTy (suc (k + Δ)) 0 A →
  0 ∣ extend-X⊑X Δ [] ⊢ pT ⦂ T ⊑ T′ →
  Σ[ p ∈ Imp ]
    (0 ∣ extend-X⊑X (k + Δ) [] ⊢ p ⦂
      substᵗ (substVarFrom k T) A ⊑
      substᵗ (substVarFrom k T′) A)
tysubst-right-at-⊑ zero {A = ＇ zero} (wfVar z<s) pT⊢ =
  _ , pT⊢
tysubst-right-at-⊑ zero {A = ＇ suc X} (wfVar (s<s X<Δ)) pT⊢ =
  reflImp (＇ X) , reflImp-wt-extend-X⊑X (wfVar X<Δ)
tysubst-right-at-⊑ (suc k) {A = ＇ zero} (wfVar z<s) pT⊢ =
  reflImp (＇ zero) , reflImp-wt-extend-X⊑X (wfVar z<s)
tysubst-right-at-⊑ (suc k) {A = ＇ suc X} (wfVar (s<s X<Δ)) pT⊢
    with tysubst-right-at-⊑ k (wfVar X<Δ) pT⊢
tysubst-right-at-⊑ (suc k) {A = ＇ suc X} (wfVar (s<s X<Δ)) pT⊢
    | p , p⊢ =
  renameImp suc p , wkImp-extend-X⊑X zero p⊢
tysubst-right-at-⊑ k {A = ｀ α} (wfSeal ()) pT⊢
tysubst-right-at-⊑ k {A = ‵ ι} wfBase pT⊢ =
  reflImp (‵ ι) , reflImp-wt-extend-X⊑X wfBase
tysubst-right-at-⊑ k {A = ★} wf★ pT⊢ =
  reflImp ★ , reflImp-wt-extend-X⊑X wf★
tysubst-right-at-⊑ k {A = A ⇒ B} (wf⇒ wfA wfB) pT⊢
    with tysubst-right-at-⊑ k wfA pT⊢
       | tysubst-right-at-⊑ k wfB pT⊢
tysubst-right-at-⊑ k {A = A ⇒ B} (wf⇒ wfA wfB) pT⊢
    | p , p⊢ | q , q⊢ =
  A⇒B-⊑-A′⇒B′ p q , ⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢
tysubst-right-at-⊑ k {A = `∀ A} (wf∀ wfA) pT⊢
    with tysubst-right-at-⊑ (suc k) wfA pT⊢
tysubst-right-at-⊑ k {A = `∀ A} (wf∀ wfA) pT⊢
    | p , p⊢ =
  ∀A-⊑-∀B p , ⊢∀A-⊑-∀B p⊢

tysubst-right-⊑ :
  ∀ {Δ A T T′ pT} →
  WfTy (suc Δ) 0 A →
  0 ∣ extend-X⊑X Δ [] ⊢ pT ⦂ T ⊑ T′ →
  Σ[ p ∈ Imp ] (0 ∣ extend-X⊑X Δ [] ⊢ p ⦂ A [ T ]ᵗ ⊑ A [ T′ ]ᵗ)
tysubst-right-⊑ wfA pT⊢ = tysubst-right-at-⊑ zero wfA pT⊢

singleTyEnv-ImpSubstWt :
  ∀ {Δ Ψ T} →
  WfTy Δ Ψ T →
  ImpSubstWt Ψ (X⊑X ∷ extend-X⊑X Δ []) (extend-X⊑X Δ []) (singleTyEnv T)
singleTyEnv-ImpSubstWt wfT here = reflImp-wt-extend-X⊑X wfT
singleTyEnv-ImpSubstWt wfT (there x∈) = plain-var-subst x∈

singleTyEnv-TySubstWf-extend-X⊑X :
  ∀ {Δ Ψ T} →
  WfTy Δ Ψ T →
  TySubstWf
    (length (X⊑X ∷ extend-X⊑X Δ []))
    (length (extend-X⊑X Δ []))
    Ψ
    (singleTyEnv T)
singleTyEnv-TySubstWf-extend-X⊑X {Δ = Δ} {T = T} wfT
  rewrite length-extend-X⊑X[] Δ =
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

⊑-substᵗ-rel :
  ∀ {Ψ Γ Γ′ σ τ p A B} →
  TySubstWf (length Γ) (length Γ′) Ψ τ →
  ImpSubstRel Ψ Γ Γ′ σ τ →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  Σ[ q ∈ Imp ] Ψ ∣ Γ′ ⊢ q ⦂ substᵗ σ A ⊑ substᵗ τ B
⊑-substᵗ-rel hτ hᵢ ⊢★-⊑-★ = ★-⊑-★ , ⊢★-⊑-★
⊑-substᵗ-rel hτ hᵢ (⊢X-⊑-★ xν) = hᵢ xν
⊑-substᵗ-rel hτ hᵢ (⊢A-⊑-★ g p⊢)
    with ⊑-substᵗ-rel hτ hᵢ p⊢
⊑-substᵗ-rel hτ hᵢ (⊢A-⊑-★ g p⊢) | q , q⊢ =
  A-⊑-★ q , ⊢A-⊑-★ (substᵗ-ground _ g) q⊢
⊑-substᵗ-rel hτ hᵢ (⊢X-⊑-X x∈) = hᵢ x∈
⊑-substᵗ-rel hτ hᵢ (⊢α-⊑-α (wfSeal α<Ψ)) =
  α-⊑-α _ , ⊢α-⊑-α (wfSeal α<Ψ)
⊑-substᵗ-rel hτ hᵢ ⊢ι-⊑-ι = ι-⊑-ι _ , ⊢ι-⊑-ι
⊑-substᵗ-rel hτ hᵢ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢)
    with ⊑-substᵗ-rel hτ hᵢ p⊢ | ⊑-substᵗ-rel hτ hᵢ q⊢
⊑-substᵗ-rel hτ hᵢ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢)
    | p′ , p′⊢ | q′ , q′⊢ =
  A⇒B-⊑-A′⇒B′ p′ q′ , ⊢A⇒B-⊑-A′⇒B′ p′⊢ q′⊢
⊑-substᵗ-rel hτ hᵢ (⊢∀A-⊑-∀B p⊢)
    with ⊑-substᵗ-rel (TySubstWf-exts hτ) (ImpSubstRel-exts hᵢ) p⊢
⊑-substᵗ-rel hτ hᵢ (⊢∀A-⊑-∀B p⊢) | q , q⊢ =
  ∀A-⊑-∀B q , ⊢∀A-⊑-∀B q⊢
⊑-substᵗ-rel {τ = τ} hτ hᵢ (⊢∀A-⊑-B {B = B} wfB p⊢)
    with ⊑-substᵗ-rel (TySubstWf-exts hτ) (ImpSubstRel-exts hᵢ) p⊢
⊑-substᵗ-rel {τ = τ} hτ hᵢ (⊢∀A-⊑-B {B = B} wfB p⊢)
    | q , q⊢ =
  ∀A-⊑-B q ,
  ⊢∀A-⊑-B
    (substᵗ-preserves-WfTy wfB hτ)
    (cong-⊢⊑ refl (substᵗ-suc-renameᵗ-suc τ B) q⊢)

var-subst-rel-id :
  ∀ {Ψ Γ X m} →
  Γ ∋ X ∶ m →
  VarSubstRel Ψ Γ (＇ X) (＇ X) m
var-subst-rel-id {m = X⊑X} x∈ = X-⊑-X _ , ⊢X-⊑-X x∈
var-subst-rel-id {m = X⊑★} x∈ = X-⊑-★ _ , ⊢X-⊑-★ x∈

singleTyEnv-TySubstWf :
  ∀ {Φ Ψ T} →
  WfTy (length Φ) Ψ T →
  TySubstWf (length (X⊑X ∷ Φ)) (length Φ) Ψ (singleTyEnv T)
singleTyEnv-TySubstWf wfT {zero} z<s = wfT
singleTyEnv-TySubstWf wfT {suc X} (s<s X<Φ) = wfVar X<Φ

singleTyEnv-ImpSubstRel :
  ∀ {Φ Ψ T T′ pT} →
  Ψ ∣ Φ ⊢ pT ⦂ T ⊑ T′ →
  ImpSubstRel Ψ (X⊑X ∷ Φ) Φ (singleTyEnv T) (singleTyEnv T′)
singleTyEnv-ImpSubstRel pT⊢ here = _ , pT⊢
singleTyEnv-ImpSubstRel pT⊢ (there x∈) = var-subst-rel-id x∈

singleImpEnv-ImpSubst⊑Rel :
  ∀ {Φ Ψ T T′ pT} →
  Ψ ∣ Φ ⊢ pT ⦂ T ⊑ T′ →
  ImpSubst⊑Rel Ψ (X⊑X ∷ Φ) Φ
    (singleImpEnv pT) (singleTyEnv T) (singleTyEnv T′)
singleImpEnv-ImpSubst⊑Rel pT⊢ here = pT⊢
singleImpEnv-ImpSubst⊑Rel {pT = pT} pT⊢ (there {m = X⊑X} x∈) =
  ⊢X-⊑-X x∈
singleImpEnv-ImpSubst⊑Rel {pT = pT} pT⊢ (there {m = X⊑★} x∈) =
  ⊢X-⊑-★ x∈

singleImpEnv-ImpSubst⊑StarRel :
  ∀ {Φ Ψ T pT} →
  Ψ ∣ Φ ⊢ pT ⦂ T ⊑ ★ →
  ImpSubst⊑Rel Ψ (X⊑★ ∷ Φ) Φ
    (singleImpEnv pT) (singleTyEnv T) (singleTyEnv ★)
singleImpEnv-ImpSubst⊑StarRel pT⊢ here = pT⊢
singleImpEnv-ImpSubst⊑StarRel {pT = pT} pT⊢ (there {m = X⊑X} x∈) =
  ⊢X-⊑-X x∈
singleImpEnv-ImpSubst⊑StarRel {pT = pT} pT⊢ (there {m = X⊑★} x∈) =
  ⊢X-⊑-★ x∈

[]⊑ᵗ-rel-wt :
  ∀ {Φ Ψ p A B T T′ pT} →
  Ψ ∣ (X⊑X ∷ Φ) ⊢ p ⦂ A ⊑ B →
  WfTy (length Φ) Ψ T′ →
  Ψ ∣ Φ ⊢ pT ⦂ T ⊑ T′ →
  Σ[ q ∈ Imp ] Ψ ∣ Φ ⊢ q ⦂ A [ T ]ᵗ ⊑ B [ T′ ]ᵗ
[]⊑ᵗ-rel-wt {Φ = Φ} p⊢ wfT′ pT⊢ =
  ⊑-substᵗ-rel
    (singleTyEnv-TySubstWf {Φ = Φ} wfT′)
    (singleTyEnv-ImpSubstRel {Φ = Φ} pT⊢)
    p⊢

[]⊑ᵢ-rel-wt :
  ∀ {Φ Ψ p A B T T′ pT} →
  Ψ ∣ (X⊑X ∷ Φ) ⊢ p ⦂ A ⊑ B →
  WfTy (length Φ) Ψ T′ →
  Ψ ∣ Φ ⊢ pT ⦂ T ⊑ T′ →
  Ψ ∣ Φ ⊢ p [ pT ]⊑ᵢ ⦂ A [ T ]ᵗ ⊑ B [ T′ ]ᵗ
[]⊑ᵢ-rel-wt {Φ = Φ} p⊢ wfT′ pT⊢ =
  ⊑-subst⊑-rel
    (singleTyEnv-TySubstWf {Φ = Φ} wfT′)
    (singleImpEnv-ImpSubst⊑Rel {Φ = Φ} pT⊢)
    p⊢

[]⊑ᵢ-star-rel-wt :
  ∀ {Φ Ψ p A B T pT} →
  Ψ ∣ (X⊑★ ∷ Φ) ⊢ p ⦂ A ⊑ B →
  Ψ ∣ Φ ⊢ pT ⦂ T ⊑ ★ →
  Ψ ∣ Φ ⊢ p [ pT ]⊑ᵢ ⦂ A [ T ]ᵗ ⊑ B [ ★ ]ᵗ
[]⊑ᵢ-star-rel-wt {Φ = Φ} p⊢ pT⊢ =
  ⊑-subst⊑-rel
    (singleTyEnv-TySubstWf {Φ = Φ} wf★)
    (singleImpEnv-ImpSubst⊑StarRel {Φ = Φ} pT⊢)
    p⊢

[]⊑ᵗ-wt :
  ∀ {Δ Ψ}{p : Imp}{A B T : Ty} →
  Ψ ∣ (X⊑X ∷ extend-X⊑X Δ []) ⊢ p ⦂ A ⊑ B →
  WfTy Δ Ψ T →
  Ψ ∣ extend-X⊑X Δ [] ⊢ p [ T ]⊑ ⦂
    src⊑ p [ T ]ᵗ ⊑ tgt⊑ p [ T ]ᵗ
[]⊑ᵗ-wt {Δ = Δ} {T = T} p⊢ wfT =
  cong-⊢⊑
    (cong (λ A → A [ T ]ᵗ) (sym (src⊑-correct p⊢)))
    (cong (λ B → B [ T ]ᵗ) (sym (tgt⊑-correct p⊢)))
    (⊑-substᵗ-wt
      (singleTyEnv-TySubstWf-extend-X⊑X wfT)
      (singleTyEnv-ImpSubstWt wfT)
      p⊢)
