module TypeCheckDec where

-- File Charter:
--   * Decidable type checking for PolyConvert raw extrinsic terms.
--   * Provides structural deciders for type well-formedness, imprecision
--     evidence, conversion evidence, and blame-free term typing.
--   * The checker follows the current PolyConvert typing rules for `⇑`/`⇓`
--     imprecision and `↑`/`↓` conversion terms.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim; ⊥-elim-irr)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _<_; z<s; s<s)
open import Data.Nat.Properties using (_<?_; _≟_)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (subst; sym; refl; cong; cong₂; trans; inspect; [_])

open import Types
open import Ctx using (⤊ᵗ; CtxWf; ctxWf-∷)
open import Imprecision
open import Conversion
open import Terms
open import Store

------------------------------------------------------------------------
-- Local propositions
------------------------------------------------------------------------

HasSomeType : TyCtx → SealCtx → Store → Ctx → Term → Set
HasSomeType Δ Ψ Σ Γ M = Σ[ A ∈ Ty ] Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A

WellTyped : Term → Set
WellTyped M = HasSomeType 0 0 ∅ˢ [] M

data BlameFree : Term → Set where
  bf-` : ∀ {x} → BlameFree (` x)
  bf-ƛ : ∀ {A M} → BlameFree M → BlameFree (ƛ A ⇒ M)
  bf-· : ∀ {L M} → BlameFree L → BlameFree M → BlameFree (L · M)
  bf-Λ : ∀ {M} → BlameFree M → BlameFree (Λ M)
  bf-⦂∀ : ∀ {M B T} → BlameFree M → BlameFree (M ⦂∀ B [ T ])
  bf-$ : ∀ {κ} → BlameFree ($ κ)
  bf-⊕ : ∀ {L op M} → BlameFree L → BlameFree M → BlameFree (L ⊕[ op ] M)
  bf-⇑ : ∀ {M p} → BlameFree M → BlameFree (M ⇑ p)
  bf-⇓ : ∀ {M p} → BlameFree M → BlameFree (M ⇓ p)
  bf-↑ : ∀ {M c} → BlameFree M → BlameFree (M ↑ c)
  bf-↓ : ∀ {M c} → BlameFree M → BlameFree (M ↓ c)

HasSomeTypeBF : TyCtx → SealCtx → Store → Ctx → Term → Set
HasSomeTypeBF Δ Ψ Σ Γ M = HasSomeType Δ Ψ Σ Γ M × BlameFree M

WellTypedBF : Term → Set
WellTypedBF M = HasSomeTypeBF 0 0 ∅ˢ [] M

upValue? : (p : Imp) → Dec (UpValue p)
upValue? ★⊑★ = no (λ ())
upValue? (X⊑★ X) = yes tagν
upValue? (A⊑★ p) = yes tag
upValue? (X⊑X X) = no (λ ())
upValue? (α⊑α α) = no (λ ())
upValue? (ι⊑ι ι) = no (λ ())
upValue? (A⇒B⊑A′⇒B′ p q) = yes (_↦_)
upValue? (`∀A⊑∀B p) = yes `∀
upValue? (`∀A⊑B B p) = no (λ ())

downValue? : (p : Imp) → Dec (DownValue p)
downValue? ★⊑★ = no (λ ())
downValue? (X⊑★ X) = no (λ ())
downValue? (A⊑★ p) = no (λ ())
downValue? (X⊑X X) = no (λ ())
downValue? (α⊑α α) = no (λ ())
downValue? (ι⊑ι ι) = no (λ ())
downValue? (A⇒B⊑A′⇒B′ p q) = yes (_↦_)
downValue? (`∀A⊑∀B p) = yes `∀
downValue? (`∀A⊑B B p) = yes (ν_)

revealValue? : (c : Conv↑) → Dec (RevealValue c)
revealValue? (↑-unseal α) = no (λ ())
revealValue? (↑-⇒ p q) = yes (_↦_)
revealValue? (↑-∀ c) = yes `∀
revealValue? (↑-id A) = no (λ ())

concealValue? : (c : Conv↓) → Dec (ConcealValue c)
concealValue? (↓-seal α) = yes seal
concealValue? (↓-⇒ p q) = yes (_↦_)
concealValue? (↓-∀ c) = yes `∀
concealValue? (↓-id A) = no (λ ())

value? : (M : Term) → Dec (Value M)
value? (` x) = no (λ ())
value? (ƛ A ⇒ M) = yes (ƛ A ⇒ M)
value? (L · M) = no (λ ())
value? (Λ M) = yes (Λ M)
value? (M ⦂∀ B [ T ]) = no (λ ())
value? ($ κ) = yes ($ κ)
value? (L ⊕[ op ] M) = no (λ ())
value? (M ⇑ p) with value? M | upValue? p
value? (M ⇑ p) | yes vM | yes vp = yes (vM ⇑ vp)
value? (M ⇑ p) | no ¬vM | _ = no (λ { (vM ⇑ vp) → ¬vM vM })
value? (M ⇑ p) | yes vM | no ¬vp = no (λ { (vM ⇑ vp) → ¬vp vp })
value? (M ⇓ p) with value? M | downValue? p
value? (M ⇓ p) | yes vM | yes vp = yes (vM ⇓ vp)
value? (M ⇓ p) | no ¬vM | _ = no (λ { (vM ⇓ vp) → ¬vM vM })
value? (M ⇓ p) | yes vM | no ¬vp = no (λ { (vM ⇓ vp) → ¬vp vp })
value? (M ↑ c) with value? M | revealValue? c
value? (M ↑ c) | yes vM | yes vc = yes (vM ↑ vc)
value? (M ↑ c) | no ¬vM | _ = no (λ { (vM ↑ vc) → ¬vM vM })
value? (M ↑ c) | yes vM | no ¬vc = no (λ { (vM ↑ vc) → ¬vc vc })
value? (M ↓ c) with value? M | concealValue? c
value? (M ↓ c) | yes vM | yes vc = yes (vM ↓ vc)
value? (M ↓ c) | no ¬vM | _ = no (λ { (vM ↓ vc) → ¬vM vM })
value? (M ↓ c) | yes vM | no ¬vc = no (λ { (vM ↓ vc) → ¬vc vc })
value? (blame ℓ) = no (λ ())

LookupAny : Ctx → Var → Set
LookupAny Γ x = Σ[ A ∈ Ty ] Γ ∋ x ⦂ A

data NonArrow : Ty → Set where
  na-var : ∀ X → NonArrow (＇ X)
  na-seal : ∀ α → NonArrow (｀ α)
  na-base : ∀ ι → NonArrow (‵ ι)
  na-star : NonArrow ★
  na-all : ∀ A → NonArrow (`∀ A)

data NonForall : Ty → Set where
  nf-var : ∀ X → NonForall (＇ X)
  nf-seal : ∀ α → NonForall (｀ α)
  nf-base : ∀ ι → NonForall (‵ ι)
  nf-star : NonForall ★
  nf-⇒ : ∀ A B → NonForall (A ⇒ B)

domTy : Ty → Ty
domTy (A ⇒ B) = A
domTy (＇ X) = ＇ X
domTy (｀ α) = ｀ α
domTy (‵ ι) = ‵ ι
domTy ★ = ★
domTy (`∀ A) = `∀ A

codTy : Ty → Ty
codTy (A ⇒ B) = B
codTy (＇ X) = ＇ X
codTy (｀ α) = ｀ α
codTy (‵ ι) = ‵ ι
codTy ★ = ★
codTy (`∀ A) = `∀ A

forallBodyTy : Ty → Ty
forallBodyTy (`∀ A) = A
forallBodyTy (A ⇒ B) = A ⇒ B
forallBodyTy (＇ X) = ＇ X
forallBodyTy (｀ α) = ｀ α
forallBodyTy (‵ ι) = ‵ ι
forallBodyTy ★ = ★

nonArrow-≠⇒ : ∀ {A B C : Ty} → NonArrow A → A ≡ (B ⇒ C) → ⊥
nonArrow-≠⇒ (na-var X) ()
nonArrow-≠⇒ (na-seal α) ()
nonArrow-≠⇒ (na-base ι) ()
nonArrow-≠⇒ na-star ()
nonArrow-≠⇒ (na-all A) ()

nonForall-≠∀ : ∀ {A B : Ty} → NonForall A → A ≡ `∀ B → ⊥
nonForall-≠∀ (nf-var X) ()
nonForall-≠∀ (nf-seal α) ()
nonForall-≠∀ (nf-base ι) ()
nonForall-≠∀ nf-star ()
nonForall-≠∀ (nf-⇒ A B) ()

ctxWf-⤊ᵗ : ∀ {Δ Ψ Γ} → CtxWf Δ Ψ Γ → CtxWf (suc Δ) Ψ (⤊ᵗ Γ)
ctxWf-⤊ᵗ {Γ = []} wfΓ ()
ctxWf-⤊ᵗ {Γ = B ∷ Γ} wfΓ Z =
  renameᵗ-preserves-WfTy (wfΓ Z) TyRenameWf-suc
ctxWf-⤊ᵗ {Γ = B ∷ Γ} wfΓ (S h) =
  ctxWf-⤊ᵗ (λ {x A} h′ → wfΓ (S h′)) h

------------------------------------------------------------------------
-- Decidable type and context helpers
------------------------------------------------------------------------

infix 4 _≟Ty_
_≟Ty_ : (A B : Ty) → Dec (A ≡ B)
(＇ X) ≟Ty (＇ Y) with X ≟ Y
... | yes eq = yes (cong ＇_ eq)
... | no neq = no (λ { refl → neq refl })
(＇ X) ≟Ty (｀ α) = no (λ ())
(＇ X) ≟Ty (‵ ι) = no (λ ())
(＇ X) ≟Ty ★ = no (λ ())
(＇ X) ≟Ty (B ⇒ C) = no (λ ())
(＇ X) ≟Ty (`∀ B) = no (λ ())
(｀ α) ≟Ty (＇ Y) = no (λ ())
(｀ α) ≟Ty (｀ β) with seal-≟ α β
... | yes eq = yes (cong ｀_ eq)
... | no neq = no (λ { refl → neq refl })
(｀ α) ≟Ty (‵ ι) = no (λ ())
(｀ α) ≟Ty ★ = no (λ ())
(｀ α) ≟Ty (B ⇒ C) = no (λ ())
(｀ α) ≟Ty (`∀ B) = no (λ ())
(‵ ι) ≟Ty (＇ Y) = no (λ ())
(‵ ι) ≟Ty (｀ β) = no (λ ())
(‵ ι) ≟Ty (‵ ι′) with ι ≟Base ι′
... | yes eq = yes (cong ‵_ eq)
... | no neq = no (λ { refl → neq refl })
(‵ ι) ≟Ty ★ = no (λ ())
(‵ ι) ≟Ty (B ⇒ C) = no (λ ())
(‵ ι) ≟Ty (`∀ B) = no (λ ())
★ ≟Ty (＇ Y) = no (λ ())
★ ≟Ty (｀ β) = no (λ ())
★ ≟Ty (‵ ι) = no (λ ())
★ ≟Ty ★ = yes refl
★ ≟Ty (B ⇒ C) = no (λ ())
★ ≟Ty (`∀ B) = no (λ ())
(A ⇒ B) ≟Ty (＇ Y) = no (λ ())
(A ⇒ B) ≟Ty (｀ β) = no (λ ())
(A ⇒ B) ≟Ty (‵ ι) = no (λ ())
(A ⇒ B) ≟Ty ★ = no (λ ())
(A ⇒ B) ≟Ty (C ⇒ D) with A ≟Ty C | B ≟Ty D
... | yes refl | yes refl = yes refl
... | no A≢C | _ = no (λ { refl → A≢C refl })
... | _ | no B≢D = no (λ { refl → B≢D refl })
(A ⇒ B) ≟Ty (`∀ C) = no (λ ())
(`∀ A) ≟Ty (＇ Y) = no (λ ())
(`∀ A) ≟Ty (｀ β) = no (λ ())
(`∀ A) ≟Ty (‵ ι) = no (λ ())
(`∀ A) ≟Ty ★ = no (λ ())
(`∀ A) ≟Ty (C ⇒ D) = no (λ ())
(`∀ A) ≟Ty (`∀ B) with A ≟Ty B
... | yes refl = yes refl
... | no A≢B = no (λ { refl → A≢B refl })

wfTyDec : (Δ : TyCtx) → (Ψ : SealCtx) → (A : Ty) → Dec (WfTy Δ Ψ A)
wfTyDec Δ Ψ (＇ X) with X <? Δ
... | yes X<Δ = yes (wfVar X<Δ)
... | no X≮Δ = no (λ { (wfVar X<Δ) → X≮Δ X<Δ })
wfTyDec Δ Ψ (｀ α) with α <? Ψ
... | yes α<Ψ = yes (wfSeal α<Ψ)
... | no α≮Ψ = no (λ { (wfSeal α<Ψ) → α≮Ψ α<Ψ })
wfTyDec Δ Ψ (‵ ι) = yes wfBase
wfTyDec Δ Ψ ★ = yes wf★
wfTyDec Δ Ψ (A ⇒ B) with wfTyDec Δ Ψ A | wfTyDec Δ Ψ B
... | yes hA | yes hB = yes (wf⇒ hA hB)
... | no ¬hA | _ = no (λ { (wf⇒ hA hB) → ¬hA hA })
... | _ | no ¬hB = no (λ { (wf⇒ hA hB) → ¬hB hB })
wfTyDec Δ Ψ (`∀ A) with wfTyDec (suc Δ) Ψ A
... | yes hA = yes (wf∀ hA)
... | no ¬hA = no (λ { (wf∀ hA) → ¬hA hA })

groundTyDec : (G : Ty) → Dec (Ground G)
groundTyDec (＇ X) = no (λ ())
groundTyDec (｀ α) = yes (｀ α)
groundTyDec (‵ ι) = yes (‵ ι)
groundTyDec ★ = no (λ ())
groundTyDec (`∀ A) = no (λ ())
groundTyDec (A ⇒ B) with A | B
... | ★ | ★ = yes ★⇒★
... | ★ | ＇ X = no (λ ())
... | ★ | ｀ α = no (λ ())
... | ★ | ‵ ι = no (λ ())
... | ★ | B₁ ⇒ B₂ = no (λ ())
... | ★ | `∀ B′ = no (λ ())
... | ＇ X | _ = no (λ ())
... | ｀ α | _ = no (λ ())
... | ‵ ι | _ = no (λ ())
... | A₁ ⇒ A₂ | _ = no (λ ())
... | `∀ A′ | _ = no (λ ())

lookupAnyDec : (Γ : Ctx) → (x : Var) → Dec (LookupAny Γ x)
lookupAnyDec [] x = no (λ { (A , ()) })
lookupAnyDec (A ∷ Γ) zero = yes (A , Z)
lookupAnyDec (A ∷ Γ) (suc x) with lookupAnyDec Γ x
... | yes (B , h) = yes (B , S h)
... | no ¬lookup = no (λ { (B , S h) → ¬lookup (B , h) })

modeEqDec : (m n : VarMode) → Dec (m ≡ n)
modeEqDec plain plain = yes refl
modeEqDec plain ν-bound = no (λ ())
modeEqDec ν-bound plain = no (λ ())
modeEqDec ν-bound ν-bound = yes refl

lookupModeDec : (Γ : ICtx) → (X : TyVar) → (m : VarMode) → Dec (Γ ∋ X ∶ m)
lookupModeDec [] X m = no (λ ())
lookupModeDec (n ∷ Γ) zero m with modeEqDec n m
... | yes refl = yes here
... | no n≢m = no (λ { here → n≢m refl })
lookupModeDec (n ∷ Γ) (suc X) m with lookupModeDec Γ X m
... | yes h = yes (there h)
... | no ¬h = no (λ { (there h) → ¬h h })

trueDec : (b : Bool) → Dec (b ≡ true)
trueDec true = yes refl
trueDec false = no (λ ())

false≢true-irr : .(false ≡ true) → ⊥
false≢true-irr ()

------------------------------------------------------------------------
-- Decidable imprecision and conversion evidence
------------------------------------------------------------------------

⊑-to-computed :
  ∀ {Ψ Γ p A B} →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  Ψ ∣ Γ ⊢ p ⦂ src⊑ p ⊑ tgt⊑ p
⊑-to-computed {p = p} p⊢ =
  subst
    (λ A → _ ∣ _ ⊢ p ⦂ A ⊑ tgt⊑ p)
    (sym (src⊑-correct p⊢))
    (subst
      (λ B → _ ∣ _ ⊢ p ⦂ _ ⊑ B)
      (sym (tgt⊑-correct p⊢))
      p⊢)

mutual
  imp-check :
    (Ψ : SealCtx) →
    (Γ : ICtx) →
    (p : Imp) →
    Dec (Ψ ∣ Γ ⊢ p ⦂ src⊑ p ⊑ tgt⊑ p)
  imp-check Ψ Γ ★⊑★ = yes ⊑-★★
  imp-check Ψ Γ (X⊑★ X) with lookupModeDec Γ X ν-bound
  ... | yes xν = yes (⊑-★ν xν)
  ... | no ¬xν = no (λ { (⊑-★ν xν) → ¬xν xν })
  imp-check Ψ Γ (A⊑★ p) with groundTyDec (tgt⊑ p) | imp-check Ψ Γ p
  ... | yes g | yes p⊢ = yes (⊑-★ g p⊢)
  ... | no ¬g | _ =
      no
        (λ
          { (⊑-★ g p⊢) →
              ¬g (subst Ground (sym (tgt⊑-correct p⊢)) g)
          })
  ... | yes g | no ¬p = no (λ { (⊑-★ g p⊢) → ¬p (⊑-to-computed p⊢) })
  imp-check Ψ Γ (X⊑X X) with lookupModeDec Γ X plain
  ... | yes xp = yes (⊑-＇ xp)
  ... | no ¬xp = no (λ { (⊑-＇ xp) → ¬xp xp })
  imp-check Ψ Γ (α⊑α α) with wfTyDec (length Γ) Ψ (｀ α)
  ... | yes wfα = yes (⊑-｀ wfα)
  ... | no ¬wfα = no (λ { (⊑-｀ wfα) → ¬wfα wfα })
  imp-check Ψ Γ (ι⊑ι ι) = yes ⊑-‵
  imp-check Ψ Γ (A⇒B⊑A′⇒B′ p q) with imp-check Ψ Γ p | imp-check Ψ Γ q
  ... | yes p⊢ | yes q⊢ = yes (⊑-⇒ p⊢ q⊢)
  ... | no ¬p | _ = no (λ { (⊑-⇒ p⊢ q⊢) → ¬p (⊑-to-computed p⊢) })
  ... | _ | no ¬q = no (λ { (⊑-⇒ p⊢ q⊢) → ¬q (⊑-to-computed q⊢) })
  imp-check Ψ Γ (`∀A⊑∀B p) with imp-check Ψ (plain ∷ Γ) p
  ... | yes p⊢ = yes (⊑-∀ p⊢)
  ... | no ¬p = no (λ { (⊑-∀ p⊢) → ¬p (⊑-to-computed p⊢) })
  imp-check Ψ Γ (`∀A⊑B B p) with wfTyDec (length Γ) Ψ B
  imp-check Ψ Γ (`∀A⊑B B p) | no ¬wfB =
      no (λ { (⊑-ν wfB occ p⊢) → ¬wfB wfB })
  imp-check Ψ Γ (`∀A⊑B B p) | yes wfB
      with imp-check Ψ (ν-bound ∷ Γ) p
  imp-check Ψ Γ (`∀A⊑B B p) | yes wfB | no ¬p =
      no (λ { (⊑-ν wfB′ occ p⊢) → ¬p (⊑-to-computed p⊢) })
  imp-check Ψ Γ (`∀A⊑B B p) | yes wfB | yes p⊢
      with tgt⊑ p ≟Ty ⇑ᵗ B
  imp-check Ψ Γ (`∀A⊑B B p) | yes wfB | yes p⊢ | no tgt≢ =
      no (λ { (⊑-ν wfB′ occ p⊢′) → tgt≢ (tgt⊑-correct p⊢′) })
  imp-check Ψ Γ (`∀A⊑B B p) | yes wfB | yes p⊢ | yes eq
      with occurs zero (src⊑ p) | inspect (λ A → occurs zero A) (src⊑ p)
  imp-check Ψ Γ (`∀A⊑B B p) | yes wfB | yes p⊢ | yes eq | true | [ occ ] =
      yes
        (⊑-ν {A = src⊑ p} wfB occ
          (subst
            (λ C → Ψ ∣ (ν-bound ∷ Γ) ⊢ p ⦂ src⊑ p ⊑ C)
            eq
            p⊢))
  imp-check Ψ Γ (`∀A⊑B B p) | yes wfB | yes p⊢ | yes eq | false | [ occ ] =
      no
        (λ
          { (⊑-ν wfB′ occ′ p⊢′) →
              ⊥-elim-irr
                (false≢true-irr
                  (subst (λ b → b ≡ true) occ occ′))
          })

imp-check-any :
  (Ψ : SealCtx) →
  (Γ : ICtx) →
  (p : Imp) →
  Dec (Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Ψ ∣ Γ ⊢ p ⦂ A ⊑ B)
imp-check-any Ψ Γ p with imp-check Ψ Γ p
... | yes p⊢ = yes (src⊑ p , (tgt⊑ p , p⊢))
... | no ¬p =
    no (λ { (A , (B , p⊢)) → ¬p (⊑-to-computed p⊢) })

imp-down-check-any :
  (Ψ : SealCtx) →
  (Γ : ICtx) →
  (p : Imp) →
  Dec (Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Ψ ∣ Γ ⊢ p ⦂ A ⊒ B)
imp-down-check-any Ψ Γ p with imp-check-any Ψ Γ p
... | yes (B , (A , p⊢)) = yes (A , (B , p⊢))
... | no ¬p =
    no (λ { (A , (B , p⊢)) → ¬p (B , (A , p⊢)) })

↑-to-computed :
  ∀ {Δ Ψ Σ c A B} →
  StoreWf Δ Ψ Σ →
  Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↑ˢ B →
  Δ ∣ Ψ ∣ Σ ⊢ c ⦂ src↑ Σ c ↑ˢ tgt↑ Σ c
↑-to-computed {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {c = c} wfΣ c⊢ =
  subst
    (λ A → Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↑ˢ tgt↑ Σ c)
    (sym (src↑-correct wfΣ c⊢))
    (subst
      (λ B → Δ ∣ Ψ ∣ Σ ⊢ c ⦂ _ ↑ˢ B)
      (sym (tgt↑-correct wfΣ c⊢))
      c⊢)

↓-to-computed :
  ∀ {Δ Ψ Σ c A B} →
  StoreWf Δ Ψ Σ →
  Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↓ˢ B →
  Δ ∣ Ψ ∣ Σ ⊢ c ⦂ src↓ Σ c ↓ˢ tgt↓ Σ c
↓-to-computed {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {c = c} wfΣ c⊢ =
  subst
    (λ A → Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↓ˢ tgt↓ Σ c)
    (sym (src↓-correct wfΣ c⊢))
    (subst
      (λ B → Δ ∣ Ψ ∣ Σ ⊢ c ⦂ _ ↓ˢ B)
      (sym (tgt↓-correct wfΣ c⊢))
      c⊢)

mutual
  conv↑-check :
    (Δ : TyCtx) →
    (Ψ : SealCtx) →
    (Σ : Store) →
    StoreWf Δ Ψ Σ →
    (c : Conv↑) →
    Dec (Δ ∣ Ψ ∣ Σ ⊢ c ⦂ src↑ Σ c ↑ˢ tgt↑ Σ c)
  conv↑-check Δ Ψ Σ wfΣ (↑-unseal α) with lookupStoreAnyDec Σ α
  ... | yes (A , h) =
      yes
        (subst
          (λ B → Δ ∣ Ψ ∣ Σ ⊢ ↑-unseal α ⦂ ｀ α ↑ˢ B)
          (sym (lookupTyˢ-lookup (storeWf-unique wfΣ) h))
          (⊢↑-unseal h))
  ... | no ¬h = no (λ { (⊢↑-unseal h) → ¬h (_ , h) })
  conv↑-check Δ Ψ Σ wfΣ (↑-⇒ p q)
      with conv↓-check Δ Ψ Σ wfΣ p | conv↑-check Δ Ψ Σ wfΣ q
  ... | yes p⊢ | yes q⊢ = yes (⊢↑-⇒ p⊢ q⊢)
  ... | no ¬p | _ = no (λ { (⊢↑-⇒ p⊢ q⊢) → ¬p (↓-to-computed wfΣ p⊢) })
  ... | _ | no ¬q = no (λ { (⊢↑-⇒ p⊢ q⊢) → ¬q (↑-to-computed wfΣ q⊢) })
  conv↑-check Δ Ψ Σ wfΣ (↑-∀ c)
      with conv↑-check (suc Δ) Ψ (⟰ᵗ Σ) (storeWf-⟰ᵗ wfΣ) c
  ... | yes c⊢ = yes (⊢↑-∀ c⊢)
  ... | no ¬c =
      no (λ { (⊢↑-∀ c⊢) → ¬c (↑-to-computed (storeWf-⟰ᵗ wfΣ) c⊢) })
  conv↑-check Δ Ψ Σ wfΣ (↑-id A) with wfTyDec Δ Ψ A
  ... | yes wfA = yes (⊢↑-id wfA)
  ... | no ¬wfA = no (λ { (⊢↑-id wfA) → ¬wfA wfA })

  conv↓-check :
    (Δ : TyCtx) →
    (Ψ : SealCtx) →
    (Σ : Store) →
    StoreWf Δ Ψ Σ →
    (c : Conv↓) →
    Dec (Δ ∣ Ψ ∣ Σ ⊢ c ⦂ src↓ Σ c ↓ˢ tgt↓ Σ c)
  conv↓-check Δ Ψ Σ wfΣ (↓-seal α) with lookupStoreAnyDec Σ α
  ... | yes (A , h) =
      yes
        (subst
          (λ A′ → Δ ∣ Ψ ∣ Σ ⊢ ↓-seal α ⦂ A′ ↓ˢ ｀ α)
          (sym (lookupTyˢ-lookup (storeWf-unique wfΣ) h))
          (⊢↓-seal h))
  ... | no ¬h = no (λ { (⊢↓-seal h) → ¬h (_ , h) })
  conv↓-check Δ Ψ Σ wfΣ (↓-⇒ p q)
      with conv↑-check Δ Ψ Σ wfΣ p | conv↓-check Δ Ψ Σ wfΣ q
  ... | yes p⊢ | yes q⊢ = yes (⊢↓-⇒ p⊢ q⊢)
  ... | no ¬p | _ = no (λ { (⊢↓-⇒ p⊢ q⊢) → ¬p (↑-to-computed wfΣ p⊢) })
  ... | _ | no ¬q = no (λ { (⊢↓-⇒ p⊢ q⊢) → ¬q (↓-to-computed wfΣ q⊢) })
  conv↓-check Δ Ψ Σ wfΣ (↓-∀ c)
      with conv↓-check (suc Δ) Ψ (⟰ᵗ Σ) (storeWf-⟰ᵗ wfΣ) c
  ... | yes c⊢ = yes (⊢↓-∀ c⊢)
  ... | no ¬c =
      no (λ { (⊢↓-∀ c⊢) → ¬c (↓-to-computed (storeWf-⟰ᵗ wfΣ) c⊢) })
  conv↓-check Δ Ψ Σ wfΣ (↓-id A) with wfTyDec Δ Ψ A
  ... | yes wfA = yes (⊢↓-id wfA)
  ... | no ¬wfA = no (λ { (⊢↓-id wfA) → ¬wfA wfA })

conv↑-check-any :
  (Δ : TyCtx) →
  (Ψ : SealCtx) →
  (Σ : Store) →
  StoreWf Δ Ψ Σ →
  (c : Conv↑) →
  Dec (Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↑ˢ B)
conv↑-check-any Δ Ψ Σ wfΣ c with conv↑-check Δ Ψ Σ wfΣ c
... | yes c⊢ = yes (src↑ Σ c , (tgt↑ Σ c , c⊢))
... | no ¬c = no (λ { (A , (B , c⊢)) → ¬c (↑-to-computed wfΣ c⊢) })

conv↓-check-any :
  (Δ : TyCtx) →
  (Ψ : SealCtx) →
  (Σ : Store) →
  StoreWf Δ Ψ Σ →
  (c : Conv↓) →
  Dec (Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↓ˢ B)
conv↓-check-any Δ Ψ Σ wfΣ c with conv↓-check Δ Ψ Σ wfΣ c
... | yes c⊢ = yes (src↓ Σ c , (tgt↓ Σ c , c⊢))
... | no ¬c = no (λ { (A , (B , c⊢)) → ¬c (↓-to-computed wfΣ c⊢) })

------------------------------------------------------------------------
-- Blame-free type uniqueness
------------------------------------------------------------------------

lookup-unique-ctx :
  ∀ {Γ : Ctx} {x : Var} {A B : Ty} →
  Γ ∋ x ⦂ A →
  Γ ∋ x ⦂ B →
  A ≡ B
lookup-unique-ctx Z Z = refl
lookup-unique-ctx {x = suc x} (S hA) (S hB) = lookup-unique-ctx hA hB

type-unique-blamefree :
  ∀ {Δ Ψ Σ Γ M A B} →
  StoreWf Δ Ψ Σ →
  BlameFree M →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ B →
  A ≡ B
type-unique-blamefree wfΣ bf-` (⊢` x:A) (⊢` x:B) =
  lookup-unique-ctx x:A x:B
type-unique-blamefree wfΣ (bf-ƛ {A = A} bfM) (⊢ƛ wfA M:A) (⊢ƛ wfA′ M:B) =
  cong (A ⇒_) (type-unique-blamefree wfΣ bfM M:A M:B)
type-unique-blamefree wfΣ (bf-· bfL bfM)
  (⊢· {A = A} {B = B} L:AB M:A)
  (⊢· {A = A′} {B = B′} L:A′B′ M:A′) =
  cong codTy (type-unique-blamefree wfΣ bfL L:AB L:A′B′)
type-unique-blamefree wfΣ (bf-Λ bfM) (⊢Λ vM M:A) (⊢Λ vM′ M:B) =
  cong `∀ (type-unique-blamefree (storeWf-⟰ᵗ wfΣ) bfM M:A M:B)
type-unique-blamefree wfΣ (bf-⦂∀ bfM)
  (⊢• {B = B} {T = T} M:∀B wfB wfT)
  (⊢• {B = B′} {T = T′} M:∀B′ wfB′ wfT′) = refl
type-unique-blamefree wfΣ bf-$ (⊢$ κ) (⊢$ κ′) = refl
type-unique-blamefree wfΣ (bf-⊕ bfL bfM) (⊢⊕ L:ℕ op M:ℕ) (⊢⊕ L:ℕ′ op′ M:ℕ′) = refl
type-unique-blamefree wfΣ (bf-⇑ bfM) (⊢up p⊢ M:A) (⊢up p⊢′ M:A′) =
  trans (sym (tgt⊑-correct p⊢)) (tgt⊑-correct p⊢′)
type-unique-blamefree wfΣ (bf-⇓ bfM) (⊢down p⊢ M:A) (⊢down p⊢′ M:A′) =
  trans (sym (src⊑-correct p⊢)) (src⊑-correct p⊢′)
type-unique-blamefree wfΣ (bf-↑ bfM) (⊢reveal c⊢ M:A) (⊢reveal c⊢′ M:A′) =
  trans (sym (tgt↑-correct wfΣ c⊢)) (tgt↑-correct wfΣ c⊢′)
type-unique-blamefree wfΣ (bf-↓ bfM) (⊢conceal c⊢ M:A) (⊢conceal c⊢′ M:A′) =
  trans (sym (tgt↓-correct wfΣ c⊢)) (tgt↓-correct wfΣ c⊢′)

------------------------------------------------------------------------
-- Decidable type checking
------------------------------------------------------------------------

type-check-app-from :
  ∀ {Δ Ψ Σ Γ L M} →
  (wfΣ : StoreWf Δ Ψ Σ) →
  (A : Ty) →
  (L:A : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L ⦂ A) →
  (bfL : BlameFree L) →
  (B : Ty) →
  (M:B : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ B) →
  (bfM : BlameFree M) →
  Dec (HasSomeTypeBF Δ Ψ Σ Γ (L · M))
type-check-app-from wfΣ (＇ X) L:X bfL B M:B bfM =
  no
    (λ
      { ((C , ⊢· {A = A′} L:fun M:A′) , bf-· bfL′ bfM′) →
          nonArrow-≠⇒ (na-var X)
            (type-unique-blamefree wfΣ bfL L:X L:fun)
      })
type-check-app-from wfΣ (｀ α) L:α bfL B M:B bfM =
  no
    (λ
      { ((C , ⊢· {A = A′} L:fun M:A′) , bf-· bfL′ bfM′) →
          nonArrow-≠⇒ (na-seal α)
            (type-unique-blamefree wfΣ bfL L:α L:fun)
      })
type-check-app-from wfΣ (‵ ι) L:ι bfL B M:B bfM =
  no
    (λ
      { ((C , ⊢· {A = A′} L:fun M:A′) , bf-· bfL′ bfM′) →
          nonArrow-≠⇒ (na-base ι)
            (type-unique-blamefree wfΣ bfL L:ι L:fun)
      })
type-check-app-from wfΣ ★ L:★ bfL B M:B bfM =
  no
    (λ
      { ((C , ⊢· {A = A′} L:fun M:A′) , bf-· bfL′ bfM′) →
          nonArrow-≠⇒ na-star
            (type-unique-blamefree wfΣ bfL L:★ L:fun)
      })
type-check-app-from wfΣ (A₁ ⇒ B₁) L:AB bfL B M:B bfM with A₁ ≟Ty B
... | yes refl = yes ((B₁ , ⊢· L:AB M:B) , bf-· bfL bfM)
... | no A₁≢B =
  no
    (λ
      { ((C , ⊢· {A = A′} L:AC M:A′) , bf-· bfL′ bfM′) →
          let eqFun = type-unique-blamefree wfΣ bfL L:AB L:AC in
          let eqArgL = cong domTy eqFun in
          let eqArgM = type-unique-blamefree wfΣ bfM M:A′ M:B in
          A₁≢B (trans eqArgL eqArgM)
      })
type-check-app-from wfΣ (`∀ A′) L:∀ bfL B M:B bfM =
  no
    (λ
      { ((C , ⊢· {A = A″} L:fun M:A″) , bf-· bfL′ bfM′) →
          nonArrow-≠⇒ (na-all A′)
            (type-unique-blamefree wfΣ bfL L:∀ L:fun)
      })

type-check :
  (Δ : TyCtx) →
  (Ψ : SealCtx) →
  (Σ : Store) →
  (Γ : Ctx) →
  (wfΓ : CtxWf Δ Ψ Γ) →
  (wfΣ : StoreWf Δ Ψ Σ) →
  (M : Term) →
  Dec (HasSomeTypeBF Δ Ψ Σ Γ M)

type-check Δ Ψ Σ Γ wfΓ wfΣ (` x) with lookupAnyDec Γ x
... | yes (A , x:A) = yes ((A , ⊢` x:A) , bf-`)
... | no ¬x = no (λ { ((A , ⊢` x:A) , bf-`) → ¬x (A , x:A) })

type-check Δ Ψ Σ Γ wfΓ wfΣ (ƛ A ⇒ N) with wfTyDec Δ Ψ A
... | no ¬wfA = no (λ { ((B , ⊢ƛ wfA N:B) , bf-ƛ bfN) → ¬wfA wfA })
... | yes wfA
    with type-check Δ Ψ Σ (A ∷ Γ) (ctxWf-∷ wfA wfΓ) wfΣ N
... | yes ((B , N:B) , bfN) =
    yes ((A ⇒ B , ⊢ƛ wfA N:B) , bf-ƛ bfN)
... | no ¬N =
    no (λ { ((A ⇒ C , ⊢ƛ wfA′ N:C) , bf-ƛ bfN′) → ¬N ((C , N:C) , bfN′) })

type-check Δ Ψ Σ Γ wfΓ wfΣ (L · M)
    with type-check Δ Ψ Σ Γ wfΓ wfΣ L | type-check Δ Ψ Σ Γ wfΓ wfΣ M
... | yes ((A , L:A) , bfL) | yes ((B , M:B) , bfM) =
    type-check-app-from wfΣ A L:A bfL B M:B bfM
... | no ¬L | _ =
    no
      (λ
        { ((C , ⊢· {A = A′} L:AC M:A′) , bf-· bfL bfM) →
            ¬L ((A′ ⇒ C , L:AC) , bfL)
        })
... | yes ((A , L:A) , bfL) | no ¬M =
    no
      (λ
        { ((C , ⊢· {A = A′} L:AC M:A′) , bf-· bfL′ bfM) →
            ¬M ((A′ , M:A′) , bfM)
        })

type-check Δ Ψ Σ Γ wfΓ wfΣ (Λ M)
    with type-check (suc Δ) Ψ (⟰ᵗ Σ) (⤊ᵗ Γ)
           (ctxWf-⤊ᵗ wfΓ) (storeWf-⟰ᵗ wfΣ) M | value? M
... | yes ((A , M:A) , bfM) | yes vM =
    yes ((`∀ A , ⊢Λ vM M:A) , bf-Λ bfM)
... | yes ((A , M:A) , bfM) | no ¬vM =
    no (λ { ((`∀ B , ⊢Λ vM M:B) , bf-Λ bfM′) → ¬vM vM })
... | no ¬M | _ =
    no (λ { ((`∀ B , ⊢Λ vM M:B) , bf-Λ bfM) → ¬M ((B , M:B) , bfM) })

type-check Δ Ψ Σ Γ wfΓ wfΣ (M ⦂∀ B [ T ]) with type-check Δ Ψ Σ Γ wfΓ wfΣ M
... | no ¬M =
    no (λ { ((C , ⊢• M:∀ wfB wfT) , bf-⦂∀ bfM) → ¬M ((`∀ _ , M:∀) , bfM) })
... | yes ((＇ X , M:X) , bfM) =
    no (λ { ((C , ⊢• M:∀ wfB wfT) , bf-⦂∀ bfM′) →
      nonForall-≠∀ (nf-var X) (type-unique-blamefree wfΣ bfM M:X M:∀) })
... | yes ((｀ α , M:α) , bfM) =
    no (λ { ((C , ⊢• M:∀ wfB wfT) , bf-⦂∀ bfM′) →
      nonForall-≠∀ (nf-seal α) (type-unique-blamefree wfΣ bfM M:α M:∀) })
... | yes ((‵ ι , M:ι) , bfM) =
    no (λ { ((C , ⊢• M:∀ wfB wfT) , bf-⦂∀ bfM′) →
      nonForall-≠∀ (nf-base ι) (type-unique-blamefree wfΣ bfM M:ι M:∀) })
... | yes ((★ , M:★) , bfM) =
    no (λ { ((C , ⊢• M:∀ wfB wfT) , bf-⦂∀ bfM′) →
      nonForall-≠∀ nf-star (type-unique-blamefree wfΣ bfM M:★ M:∀) })
... | yes ((A ⇒ B′ , M:AB) , bfM) =
    no (λ { ((C , ⊢• M:∀ wfB wfT) , bf-⦂∀ bfM′) →
      nonForall-≠∀ (nf-⇒ A B′) (type-unique-blamefree wfΣ bfM M:AB M:∀) })
... | yes ((`∀ B′ , M:∀B′) , bfM)
    with B′ ≟Ty B | wfTyDec (suc Δ) Ψ B | wfTyDec Δ Ψ T
...   | no B′≢B | _ | _ =
      no
        (λ
          { ((C , ⊢• M:∀B wfB wfT) , bf-⦂∀ bfM′) →
              B′≢B (cong forallBodyTy (type-unique-blamefree wfΣ bfM M:∀B′ M:∀B))
          })
...   | yes refl | no ¬wfB | _ =
      no (λ { ((C , ⊢• M:∀B wfB wfT) , bf-⦂∀ bfM′) → ¬wfB wfB })
...   | yes refl | yes wfB | no ¬wfT =
      no (λ { ((C , ⊢• M:∀B wfB′ wfT) , bf-⦂∀ bfM′) → ¬wfT wfT })
...   | yes refl | yes wfB | yes wfT =
      yes ((B [ T ]ᵗ , ⊢• M:∀B′ wfB wfT) , bf-⦂∀ bfM)

type-check Δ Ψ Σ Γ wfΓ wfΣ ($ κ) = yes ((constTy κ , ⊢$ κ) , bf-$)

type-check Δ Ψ Σ Γ wfΓ wfΣ (L ⊕[ op ] M)
    with type-check Δ Ψ Σ Γ wfΓ wfΣ L | type-check Δ Ψ Σ Γ wfΓ wfΣ M
... | yes ((A , L:A) , bfL) | yes ((B , M:B) , bfM)
    with A ≟Ty (‵ `ℕ) | B ≟Ty (‵ `ℕ)
...   | yes refl | yes refl = yes (((‵ `ℕ) , ⊢⊕ L:A op M:B) , bf-⊕ bfL bfM)
...   | no A≢ℕ | _ =
      no
        (λ
          { ((C , ⊢⊕ L:ℕ op′ M:ℕ) , bf-⊕ bfL′ bfM′) →
              A≢ℕ (type-unique-blamefree wfΣ bfL L:A L:ℕ)
          })
...   | _ | no B≢ℕ =
      no
        (λ
          { ((C , ⊢⊕ L:ℕ op′ M:ℕ) , bf-⊕ bfL′ bfM′) →
              B≢ℕ (type-unique-blamefree wfΣ bfM M:B M:ℕ)
          })
type-check Δ Ψ Σ Γ wfΓ wfΣ (L ⊕[ op ] M) | no ¬L | _ =
    no (λ { ((C , ⊢⊕ L:ℕ op′ M:ℕ) , bf-⊕ bfL bfM) → ¬L (((‵ `ℕ) , L:ℕ) , bfL) })
type-check Δ Ψ Σ Γ wfΓ wfΣ (L ⊕[ op ] M) | yes ((A , L:A) , bfL) | no ¬M =
    no (λ { ((C , ⊢⊕ L:ℕ op′ M:ℕ) , bf-⊕ bfL′ bfM) → ¬M (((‵ `ℕ) , M:ℕ) , bfM) })

type-check Δ Ψ Σ Γ wfΓ wfΣ (M ⇑ p) with type-check Δ Ψ Σ Γ wfΓ wfΣ M
... | no ¬M =
    no (λ { ((B , ⊢up p⊢ M:A′) , bf-⇑ bfM) → ¬M ((_ , M:A′) , bfM) })
... | yes ((A , M:A) , bfM) with imp-check-any Ψ (plains Δ []) p
...   | no ¬p =
      no (λ { ((B , ⊢up p⊢ M:A′) , bf-⇑ bfM′) → ¬p (_ , (_ , p⊢)) })
...   | yes (A′ , (B , p⊢)) with A′ ≟Ty A
...     | yes refl = yes ((B , ⊢up p⊢ M:A) , bf-⇑ bfM)
...     | no A′≢A =
        no
          (λ
            { ((C , ⊢up {A = A″} p⊢′ M:A″) , bf-⇑ bfM′) →
                let eqImp = trans (sym (src⊑-correct p⊢)) (src⊑-correct p⊢′) in
                let eqTerm = type-unique-blamefree wfΣ bfM M:A″ M:A in
                A′≢A (trans eqImp eqTerm)
            })

type-check Δ Ψ Σ Γ wfΓ wfΣ (M ⇓ p) with type-check Δ Ψ Σ Γ wfΓ wfΣ M
... | no ¬M =
    no (λ { ((B , ⊢down p⊢ M:A′) , bf-⇓ bfM) → ¬M ((_ , M:A′) , bfM) })
... | yes ((A , M:A) , bfM) with imp-down-check-any Ψ (plains Δ []) p
...   | no ¬p =
      no (λ { ((B , ⊢down p⊢ M:A′) , bf-⇓ bfM′) → ¬p (_ , (_ , p⊢)) })
...   | yes (A′ , (B , p⊢)) with A′ ≟Ty A
...     | yes refl = yes ((B , ⊢down p⊢ M:A) , bf-⇓ bfM)
...     | no A′≢A =
        no
          (λ
            { ((C , ⊢down {A = A″} p⊢′ M:A″) , bf-⇓ bfM′) →
                let eqImp = trans (sym (tgt⊑-correct p⊢)) (tgt⊑-correct p⊢′) in
                let eqTerm = type-unique-blamefree wfΣ bfM M:A″ M:A in
                A′≢A (trans eqImp eqTerm)
            })

type-check Δ Ψ Σ Γ wfΓ wfΣ (M ↑ c) with type-check Δ Ψ Σ Γ wfΓ wfΣ M
... | no ¬M =
    no (λ { ((B , ⊢reveal c⊢ M:A′) , bf-↑ bfM) → ¬M ((_ , M:A′) , bfM) })
... | yes ((A , M:A) , bfM) with conv↑-check-any Δ Ψ Σ wfΣ c
...   | no ¬c =
      no (λ { ((B , ⊢reveal c⊢ M:A′) , bf-↑ bfM′) → ¬c (_ , (_ , c⊢)) })
...   | yes (A′ , (B , c⊢)) with A′ ≟Ty A
...     | yes refl = yes ((B , ⊢reveal c⊢ M:A) , bf-↑ bfM)
...     | no A′≢A =
        no
          (λ
            { ((C , ⊢reveal {A = A″} c⊢′ M:A″) , bf-↑ bfM′) →
                let eqConv = trans (sym (src↑-correct wfΣ c⊢)) (src↑-correct wfΣ c⊢′) in
                let eqTerm = type-unique-blamefree wfΣ bfM M:A″ M:A in
                A′≢A (trans eqConv eqTerm)
            })

type-check Δ Ψ Σ Γ wfΓ wfΣ (M ↓ c) with type-check Δ Ψ Σ Γ wfΓ wfΣ M
... | no ¬M =
    no (λ { ((B , ⊢conceal c⊢ M:A′) , bf-↓ bfM) → ¬M ((_ , M:A′) , bfM) })
... | yes ((A , M:A) , bfM) with conv↓-check-any Δ Ψ Σ wfΣ c
...   | no ¬c =
      no (λ { ((B , ⊢conceal c⊢ M:A′) , bf-↓ bfM′) → ¬c (_ , (_ , c⊢)) })
...   | yes (A′ , (B , c⊢)) with A′ ≟Ty A
...     | yes refl = yes ((B , ⊢conceal c⊢ M:A) , bf-↓ bfM)
...     | no A′≢A =
        no
          (λ
            { ((C , ⊢conceal {A = A″} c⊢′ M:A″) , bf-↓ bfM′) →
                let eqConv = trans (sym (src↓-correct wfΣ c⊢)) (src↓-correct wfΣ c⊢′) in
                let eqTerm = type-unique-blamefree wfΣ bfM M:A″ M:A in
                A′≢A (trans eqConv eqTerm)
            })

type-check Δ Ψ Σ Γ wfΓ wfΣ (blame ℓ) =
  no (λ { ((A , M:A) , ()) })

------------------------------------------------------------------------
-- Type check against an expected type
------------------------------------------------------------------------

type-check-expect :
  (Δ : TyCtx) →
  (Ψ : SealCtx) →
  (Σ : Store) →
  (Γ : Ctx) →
  (wfΓ : CtxWf Δ Ψ Γ) →
  (wfΣ : StoreWf Δ Ψ Σ) →
  (M : Term) →
  (A : Ty) →
  Dec ((Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A) × BlameFree M)
type-check-expect Δ Ψ Σ Γ wfΓ wfΣ M A with type-check Δ Ψ Σ Γ wfΓ wfΣ M
... | no ¬M =
  no (λ { (M:A , bfM) → ¬M ((A , M:A) , bfM) })
... | yes ((B , M:B) , bfM) with B ≟Ty A
... | yes refl = yes (M:B , bfM)
... | no B≢A =
  no
    (λ
      { (M:A , bfM′) →
          B≢A (type-unique-blamefree wfΣ bfM M:B M:A)
      })
