module proof.ImprecisionCompose where

-- File Charter:
--   * Structural transitivity for PolyConvert type imprecision.
--   * The main export is `⊑-trans`; `trans-ctx-⊑` is the strengthened
--     induction principle that allows plain type binders on the left to become
--     ν-bound binders on the right.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; length)
open import Data.Nat using (zero; suc)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import Types
open import Imprecision
open import proof.PreservationBetaUpNu using (occurs-raise; wkImpAt)
open import proof.TypeProperties using (renameᵗ-ground)

------------------------------------------------------------------------
-- Context imprecision for the induction
------------------------------------------------------------------------

data ModeLe : VarMode → VarMode → Set where
  plain≤plain : ModeLe plain plain
  plain≤ν : ModeLe plain ν-bound
  ν≤ν : ModeLe ν-bound ν-bound

infix 4 _≤ᵢ_
data _≤ᵢ_ : ICtx → ICtx → Set where
  []≤ᵢ : [] ≤ᵢ []
  _∷≤ᵢ_ : ∀ {m m′ Γ Γ′} →
    ModeLe m m′ →
    Γ ≤ᵢ Γ′ →
    (m ∷ Γ) ≤ᵢ (m′ ∷ Γ′)

≤ᵢ-refl : ∀ {Γ} → Γ ≤ᵢ Γ
≤ᵢ-refl {Γ = []} = []≤ᵢ
≤ᵢ-refl {Γ = plain ∷ Γ} = plain≤plain ∷≤ᵢ ≤ᵢ-refl
≤ᵢ-refl {Γ = ν-bound ∷ Γ} = ν≤ν ∷≤ᵢ ≤ᵢ-refl

≤ᵢ-length :
  ∀ {Γ Γ′} →
  Γ ≤ᵢ Γ′ →
  length Γ ≡ length Γ′
≤ᵢ-length []≤ᵢ = refl
≤ᵢ-length (m≤m′ ∷≤ᵢ Γ≤Γ′) = cong suc (≤ᵢ-length Γ≤Γ′)

≤ᵢ-ν-lookup :
  ∀ {Γ Γ′ X} →
  Γ ≤ᵢ Γ′ →
  Γ ∋ X ∶ ν-bound →
  Γ′ ∋ X ∶ ν-bound
≤ᵢ-ν-lookup (ν≤ν ∷≤ᵢ Γ≤Γ′) here = here
≤ᵢ-ν-lookup (m≤m′ ∷≤ᵢ Γ≤Γ′) (there xν) =
  there (≤ᵢ-ν-lookup Γ≤Γ′ xν)

wf-length-cast :
  ∀ {Ψ Γ Γ′ A} →
  Γ ≤ᵢ Γ′ →
  WfTy (length Γ) Ψ A →
  WfTy (length Γ′) Ψ A
wf-length-cast Γ≤Γ′ wfA =
  subst (λ Δ → WfTy Δ _ _) (≤ᵢ-length Γ≤Γ′) wfA

------------------------------------------------------------------------
-- Occurrence inversion for plain variables
------------------------------------------------------------------------

false≢true : false ≡ true → ⊥
false≢true ()

occurs-⇑ᵗ-suc :
  ∀ X A →
  occurs (suc X) (⇑ᵗ A) ≡ occurs X A
occurs-⇑ᵗ-suc X A = occurs-raise zero X A

plain-target-occurs-source :
  ∀ {Ψ Γ X A B p} →
  Γ ∋ X ∶ plain →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  occurs X B ≡ true →
  occurs X A ≡ true
plain-target-occurs-source x∈ ⊑-★★ ()
plain-target-occurs-source x∈ (⊑-★ν xν) ()
plain-target-occurs-source x∈ (⊑-★ g p⊢) ()
plain-target-occurs-source x∈ (⊑-＇ y∈) occ = occ
plain-target-occurs-source x∈ (⊑-｀ wfα) ()
plain-target-occurs-source x∈ ⊑-‵ ()
plain-target-occurs-source {X = X} x∈
    (⊑-⇒ {A = A} {A′ = A′} {B = B} {B′ = B′} p⊢ q⊢) occ
    with occurs X A′ in occA′ | occurs X A in occA
plain-target-occurs-source {X = X} x∈
    (⊑-⇒ {A = A} {A′ = A′} {B = B} {B′ = B′} p⊢ q⊢) occ
    | true | true = refl
plain-target-occurs-source {X = X} x∈
    (⊑-⇒ {A = A} {A′ = A′} {B = B} {B′ = B′} p⊢ q⊢) occ
    | true | false =
  ⊥-elim (false≢true
    (trans (sym occA) (plain-target-occurs-source x∈ p⊢ occA′)))
plain-target-occurs-source {X = X} x∈
    (⊑-⇒ {A = A} {A′ = A′} {B = B} {B′ = B′} p⊢ q⊢) occ
    | false | true = refl
plain-target-occurs-source {X = X} x∈
    (⊑-⇒ {A = A} {A′ = A′} {B = B} {B′ = B′} p⊢ q⊢) occ
    | false | false =
  plain-target-occurs-source x∈ q⊢ occ
plain-target-occurs-source x∈ (⊑-∀ p⊢) occ =
  plain-target-occurs-source (there x∈) p⊢ occ
plain-target-occurs-source {X = X} x∈ (⊑-ν {B = B} wfB occA p⊢) occB =
  plain-target-occurs-source (there x∈) p⊢
    (trans (occurs-⇑ᵗ-suc X B) occB)

------------------------------------------------------------------------
-- Transport across plain-to-ν context changes
------------------------------------------------------------------------

mutual
  transport-to-star-⊑ :
    ∀ {Ψ Γ Γ′ A p} →
    Γ ≤ᵢ Γ′ →
    Ψ ∣ Γ ⊢ p ⦂ A ⊑ ★ →
    Σ[ r ∈ Imp ] Ψ ∣ Γ′ ⊢ r ⦂ A ⊑ ★
  transport-to-star-⊑ Γ≤Γ′ ⊑-★★ = ★⊑★ , ⊑-★★
  transport-to-star-⊑ Γ≤Γ′ (⊑-★ν xν) =
    _ , ⊑-★ν (≤ᵢ-ν-lookup Γ≤Γ′ xν)
  transport-to-star-⊑ Γ≤Γ′ (⊑-★ g p⊢)
      with transport-to-ground-⊑ Γ≤Γ′ g p⊢
  transport-to-star-⊑ Γ≤Γ′ (⊑-★ g p⊢) | r , r⊢ =
    A⊑★ r , ⊑-★ g r⊢
  transport-to-star-⊑ Γ≤Γ′ (⊑-ν {B = ★} wf★ occ p⊢)
      with transport-to-star-⊑ (ν≤ν ∷≤ᵢ Γ≤Γ′) p⊢
  transport-to-star-⊑ Γ≤Γ′ (⊑-ν {B = ★} wf★ occ p⊢)
      | r , r⊢ =
    `∀A⊑B ★ r , ⊑-ν (wf-length-cast Γ≤Γ′ wf★) occ r⊢

  transport-to-ground-⊑ :
    ∀ {Ψ Γ Γ′ A G p} →
    Γ ≤ᵢ Γ′ →
    Ground G →
    Ψ ∣ Γ ⊢ p ⦂ A ⊑ G →
    Σ[ r ∈ Imp ] Ψ ∣ Γ′ ⊢ r ⦂ A ⊑ G
  transport-to-ground-⊑ Γ≤Γ′ (｀ α) (⊑-｀ wfα) =
    α⊑α α , ⊑-｀ (wf-length-cast Γ≤Γ′ wfα)
  transport-to-ground-⊑ Γ≤Γ′ (‵ ι) ⊑-‵ =
    ι⊑ι ι , ⊑-‵
  transport-to-ground-⊑ Γ≤Γ′ ★⇒★ (⊑-⇒ p⊢ q⊢)
      with transport-to-star-⊑ Γ≤Γ′ p⊢
         | transport-to-star-⊑ Γ≤Γ′ q⊢
  transport-to-ground-⊑ Γ≤Γ′ ★⇒★ (⊑-⇒ p⊢ q⊢)
      | p′ , p′⊢ | q′ , q′⊢ =
    A⇒B⊑A′⇒B′ p′ q′ , ⊑-⇒ p′⊢ q′⊢
  transport-to-ground-⊑ Γ≤Γ′ g (⊑-ν {B = B} wfB occ p⊢)
      with transport-to-ground-⊑ (ν≤ν ∷≤ᵢ Γ≤Γ′) (renameᵗ-ground suc g) p⊢
  transport-to-ground-⊑ Γ≤Γ′ g (⊑-ν {B = B} wfB occ p⊢)
      | r , r⊢ =
    `∀A⊑B B r , ⊑-ν (wf-length-cast Γ≤Γ′ wfB) occ r⊢

------------------------------------------------------------------------
-- Full transitivity
------------------------------------------------------------------------

trans-ctx-⊑ :
  ∀ {Ψ Γ Γ′ A B C p q} →
  Γ ≤ᵢ Γ′ →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  Ψ ∣ Γ′ ⊢ q ⦂ B ⊑ C →
  Σ[ r ∈ Imp ] Ψ ∣ Γ′ ⊢ r ⦂ A ⊑ C
trans-ctx-⊑ Γ≤Γ′ (⊑-ν {B = B} wfB occB p⊢) q⊢
    with trans-ctx-⊑ (ν≤ν ∷≤ᵢ Γ≤Γ′) p⊢ (wkImpAt {Φ = []} q⊢)
trans-ctx-⊑ Γ≤Γ′ (⊑-ν {B = B} wfB occB p⊢) q⊢
    | r , r⊢ =
  `∀A⊑B _ r , ⊑-ν (⊑-tgt-wf q⊢) occB r⊢
trans-ctx-⊑ Γ≤Γ′ p⊢ ⊑-★★ = transport-to-star-⊑ Γ≤Γ′ p⊢
trans-ctx-⊑ Γ≤Γ′ p⊢ (⊑-★ν xν) =
  trans-to-starν Γ≤Γ′ p⊢ xν
  where
    trans-to-starν :
      ∀ {Ψ Γ Γ′ A X p} →
      Γ ≤ᵢ Γ′ →
      Ψ ∣ Γ ⊢ p ⦂ A ⊑ ＇ X →
      Γ′ ∋ X ∶ ν-bound →
      Σ[ r ∈ Imp ] Ψ ∣ Γ′ ⊢ r ⦂ A ⊑ ★
    trans-to-starν Γ≤Γ′ (⊑-＇ x∈) xν = X⊑★ _ , ⊑-★ν xν
    trans-to-starν Γ≤Γ′ (⊑-ν {B = ＇ X} wfB occ p⊢) xν
        with trans-ctx-⊑ (ν≤ν ∷≤ᵢ Γ≤Γ′) p⊢ (wkImpAt {Φ = []} (⊑-★ν xν))
    trans-to-starν Γ≤Γ′ (⊑-ν {B = ＇ X} wfB occ p⊢) xν
        | r , r⊢ =
      `∀A⊑B ★ r , ⊑-ν wf★ occ r⊢
trans-ctx-⊑ Γ≤Γ′ p⊢ (⊑-★ g q⊢)
    with trans-ctx-⊑ Γ≤Γ′ p⊢ q⊢
trans-ctx-⊑ Γ≤Γ′ p⊢ (⊑-★ g q⊢) | r , r⊢ =
  A⊑★ r , ⊑-★ g r⊢
trans-ctx-⊑ Γ≤Γ′ (⊑-＇ x∈) (⊑-＇ x∈′) =
  _ , ⊑-＇ x∈′
trans-ctx-⊑ Γ≤Γ′ p⊢ (⊑-｀ wfα) =
  transport-to-ground-⊑ Γ≤Γ′ (｀ _) p⊢
trans-ctx-⊑ Γ≤Γ′ p⊢ ⊑-‵ =
  transport-to-ground-⊑ Γ≤Γ′ (‵ _) p⊢
trans-ctx-⊑ Γ≤Γ′ (⊑-⇒ p⊢ q⊢) (⊑-⇒ p⊢′ q⊢′)
    with trans-ctx-⊑ Γ≤Γ′ p⊢ p⊢′
       | trans-ctx-⊑ Γ≤Γ′ q⊢ q⊢′
trans-ctx-⊑ Γ≤Γ′ (⊑-⇒ p⊢ q⊢) (⊑-⇒ p⊢′ q⊢′)
    | r₁ , r₁⊢ | r₂ , r₂⊢ =
  A⇒B⊑A′⇒B′ r₁ r₂ , ⊑-⇒ r₁⊢ r₂⊢
trans-ctx-⊑ Γ≤Γ′ (⊑-∀ p⊢) (⊑-∀ q⊢)
    with trans-ctx-⊑ (plain≤plain ∷≤ᵢ Γ≤Γ′) p⊢ q⊢
trans-ctx-⊑ Γ≤Γ′ (⊑-∀ p⊢) (⊑-∀ q⊢) | r , r⊢ =
  `∀A⊑∀B r , ⊑-∀ r⊢
trans-ctx-⊑ Γ≤Γ′ (⊑-∀ p⊢) (⊑-ν {B = B} wfB occB q⊢)
    with trans-ctx-⊑ (plain≤ν ∷≤ᵢ Γ≤Γ′) p⊢ q⊢
trans-ctx-⊑ Γ≤Γ′ (⊑-∀ p⊢) (⊑-ν {B = B} wfB occB q⊢)
    | r , r⊢ =
  `∀A⊑B B r ,
  ⊑-ν wfB (plain-target-occurs-source here p⊢ occB) r⊢

⊑-trans :
  ∀ {Ψ Γ A B C p q} →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  Ψ ∣ Γ ⊢ q ⦂ B ⊑ C →
  Σ[ r ∈ Imp ] Ψ ∣ Γ ⊢ r ⦂ A ⊑ C
⊑-trans = trans-ctx-⊑ ≤ᵢ-refl
