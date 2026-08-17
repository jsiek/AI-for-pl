module proof.DGG.notes.probes.PartnerLiftDraft where

-- File Charter:
--   * Type-checks D4.4(ii) partner-lift candidate statements.
--   * Candidate A is checked against the existing target-insert geometry.
--   * Candidate B is recorded as constructor-type statements only; this
--     probe does not change the live partner relation.

import Data.Fin as Fin
open import Data.Maybe using (Maybe; just)
import Data.Nat as Nat

open import Types using (Ty; TyCtx; TyVar; ★; ＇_)
open import Consistency using
  (Env∼; _⊢_∼_; _↪ᵗ_; wk↪ᵗ)
open import Conversion using (Conv↑; Conv↓; `∀↑_; `∀↓_; seal)
open import CastTerms using (Term; ⇑ᵗᵐ; _⟨_⟩; _↑_; _↓_)
open import Reduction using (bind; _∷_; [])
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralWorldExtendDef using
  (mapPivotChanges; StructuralWorldExtendᴿ; structural-bind; structural-[])


CandidateA-SealTargetBindᵀ : Set₁
CandidateA-SealTargetBindᵀ =
  ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {π : Δ ↪ᵗ Δ₁} {B : Ty Δᴿ}
    {X : TyVar Δᴸ} {P : Term Δᴸ} {R : Ty Δᴸ}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
  → TE.TargetInsert wk↪ᵗ π W W₁
  → CTI2.SealPartnerOK W X P R Xᴿ? V
  → CTI2.SealPartnerOK W₁ X P R
      (mapPivotChanges (bind B ∷ []) Xᴿ?) (⇑ᵗᵐ V)


candidateA-seal-target-bind : CandidateA-SealTargetBindᵀ
candidateA-seal-target-bind ins =
  TE.renameSealPartnerOK (TE.align-insert ins)
    (TE.targetInsertNoTargetAtSource ins)


CandidateA-SourceConcealTargetBindᵀ : Set₁
CandidateA-SourceConcealTargetBindᵀ =
  ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {π : Δ ↪ᵗ Δ₁} {B : Ty Δᴿ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
  → TE.TargetInsert wk↪ᵗ π W W₁
  → CTI2.SourceConcealPartnerOK W P c Xᴿ? V
  → CTI2.SourceConcealPartnerOK W₁ P c
      (mapPivotChanges (bind B ∷ []) Xᴿ?) (⇑ᵗᵐ V)


candidateA-source-conceal-target-bind :
  CandidateA-SourceConcealTargetBindᵀ
candidateA-source-conceal-target-bind ins =
  TE.renameSourceConcealPartnerOK (TE.align-insert ins)
    (TE.targetInsertNoTargetAtSource ins)


CandidateA-MatchedConcealTargetBindᵀ : Set₁
CandidateA-MatchedConcealTargetBindᵀ =
  ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {π : Δ ↪ᵗ Δ₁} {B : Ty Δᴿ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
  → TE.TargetInsert wk↪ᵗ π W W₁
  → CTI2.MatchedConcealPartnerOK W P c Xᴿ? V
  → CTI2.MatchedConcealPartnerOK W₁ P c
      (mapPivotChanges (bind B ∷ []) Xᴿ?) (⇑ᵗᵐ V)


candidateA-matched-conceal-target-bind :
  CandidateA-MatchedConcealTargetBindᵀ
candidateA-matched-conceal-target-bind ins =
  TE.renameMatchedConcealPartnerOK (TE.align-insert ins)


CandidateA-SealStructuralBindᵀ : Set₁
CandidateA-SealStructuralBindᵀ =
  ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {B : Ty Δᴿ}
    {X : TyVar Δᴸ} {P : Term Δᴸ} {R : Ty Δᴸ}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
  → StructuralWorldExtendᴿ (bind B ∷ []) W W₁
  → CTI2.SealPartnerOK W X P R Xᴿ? V
  → CTI2.SealPartnerOK W₁ X P R
      (mapPivotChanges (bind B ∷ []) Xᴿ?) (⇑ᵗᵐ V)


candidateA-seal-structural-bind : CandidateA-SealStructuralBindᵀ
candidateA-seal-structural-bind {B = B}
    (structural-bind ins follows structural-[]) =
  candidateA-seal-target-bind {B = B} ins


CandidateA-SourceConcealStructuralBindᵀ : Set₁
CandidateA-SourceConcealStructuralBindᵀ =
  ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {B : Ty Δᴿ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
  → StructuralWorldExtendᴿ (bind B ∷ []) W W₁
  → CTI2.SourceConcealPartnerOK W P c Xᴿ? V
  → CTI2.SourceConcealPartnerOK W₁ P c
      (mapPivotChanges (bind B ∷ []) Xᴿ?) (⇑ᵗᵐ V)


candidateA-source-conceal-structural-bind :
  CandidateA-SourceConcealStructuralBindᵀ
candidateA-source-conceal-structural-bind {B = B}
    (structural-bind ins follows structural-[]) =
  candidateA-source-conceal-target-bind {B = B} ins


CandidateA-MatchedConcealStructuralBindᵀ : Set₁
CandidateA-MatchedConcealStructuralBindᵀ =
  ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {B : Ty Δᴿ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
  → StructuralWorldExtendᴿ (bind B ∷ []) W W₁
  → CTI2.MatchedConcealPartnerOK W P c Xᴿ? V
  → CTI2.MatchedConcealPartnerOK W₁ P c
      (mapPivotChanges (bind B ∷ []) Xᴿ?) (⇑ᵗᵐ V)


candidateA-matched-conceal-structural-bind :
  CandidateA-MatchedConcealStructuralBindᵀ
candidateA-matched-conceal-structural-bind {B = B}
    (structural-bind ins follows structural-[]) =
  candidateA-matched-conceal-target-bind {B = B} ins


candidateA-notTopTag-lift : ∀ {Δ} {V : Term Δ}
  → CTI2.NotTopTag V
  → CTI2.NotTopTag (⇑ᵗᵐ V)
candidateA-notTopTag-lift =
  TE.notTopTag-rename wk↪ᵗ


candidateA-name-protected-shape-target-bind :
  ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {π : Δ ↪ᵗ Δ₁} {B : Ty Δᴿ}
    {X : TyVar Δᴸ} {P : Term Δᴸ} {R : Ty Δᴸ}
    {Y : TyVar Δᴿ} {S : Ty Δᴿ} {V : Term Δᴿ}
    {μ : Env∼ Δᴿ} {c : μ ⊢ (＇ Y) ∼ ★}
  → TE.TargetInsert wk↪ᵗ π W W₁
  → CTI2.SealPartnerOK W₁ X P R
      (mapPivotChanges (bind B ∷ []) (just Y))
      (⇑ᵗᵐ ((V ↓ seal Y S) ⟨ c ⟩))
candidateA-name-protected-shape-target-bind {B = B} ins =
  candidateA-seal-target-bind {B = B} ins CTI2.name-protected-target


candidateA-source-reveal-wrapper-output :
  ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {π : Δ ↪ᵗ Δ₁} {B₀ : Ty Δᴿ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {B C : Ty (Nat.suc Δᴿ)}
    {cˢ : Conv↓ Δᴸ A A′} {d : Conv↑ (Nat.suc Δᴿ) C B}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
  → TE.TargetInsert wk↪ᵗ π W W₁
  → CTI2.SourceConcealPartnerOK W P cˢ Xᴿ? (V ↑ `∀↑ d)
  → CTI2.SourceConcealPartnerOK W₁ P cˢ
      (mapPivotChanges (bind B₀ ∷ []) Xᴿ?)
      (⇑ᵗᵐ (V ↑ `∀↑ d))
candidateA-source-reveal-wrapper-output {B₀ = B₀} =
  candidateA-source-conceal-target-bind {B = B₀}


candidateA-source-conceal-wrapper-output :
  ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {π : Δ ↪ᵗ Δ₁} {B₀ : Ty Δᴿ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {B C : Ty (Nat.suc Δᴿ)}
    {cˢ : Conv↓ Δᴸ A A′} {d : Conv↓ (Nat.suc Δᴿ) C B}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
  → TE.TargetInsert wk↪ᵗ π W W₁
  → CTI2.SourceConcealPartnerOK W P cˢ Xᴿ? (V ↓ `∀↓ d)
  → CTI2.SourceConcealPartnerOK W₁ P cˢ
      (mapPivotChanges (bind B₀ ∷ []) Xᴿ?)
      (⇑ᵗᵐ (V ↓ `∀↓ d))
candidateA-source-conceal-wrapper-output {B₀ = B₀} =
  candidateA-source-conceal-target-bind {B = B₀}


CandidateB-SealLiftedRevealConstructorᵀ : Set
CandidateB-SealLiftedRevealConstructorᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {P : Term Δᴸ} {R : Ty Δᴸ}
    {B₀ : Ty Δᴿ} {B C : Ty (Nat.suc Δᴿ)}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
    {d : Conv↑ (Nat.suc Δᴿ) C B}
  → CTI2.SealPartnerOK W X P R Xᴿ? (V ↑ `∀↑ d)
  → CTI2.SealPartnerOK (CTI2.rightOnlyWorld W B₀) X P R
      (mapPivotChanges (bind B₀ ∷ []) Xᴿ?) (⇑ᵗᵐ V)


CandidateB-SealLiftedConcealConstructorᵀ : Set
CandidateB-SealLiftedConcealConstructorᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {P : Term Δᴸ} {R : Ty Δᴸ}
    {B₀ : Ty Δᴿ} {B C : Ty (Nat.suc Δᴿ)}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
    {d : Conv↓ (Nat.suc Δᴿ) C B}
  → CTI2.SealPartnerOK W X P R Xᴿ? (V ↓ `∀↓ d)
  → CTI2.SealPartnerOK (CTI2.rightOnlyWorld W B₀) X P R
      (mapPivotChanges (bind B₀ ∷ []) Xᴿ?) (⇑ᵗᵐ V)


CandidateB-SourceLiftedRevealConstructorᵀ : Set
CandidateB-SourceLiftedRevealConstructorᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {B₀ : Ty Δᴿ} {B C : Ty (Nat.suc Δᴿ)}
    {cˢ : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
    {d : Conv↑ (Nat.suc Δᴿ) C B}
  → CTI2.SourceConcealPartnerOK W P cˢ Xᴿ? (V ↑ `∀↑ d)
  → CTI2.SourceConcealPartnerOK (CTI2.rightOnlyWorld W B₀) P cˢ
      (mapPivotChanges (bind B₀ ∷ []) Xᴿ?) (⇑ᵗᵐ V)


CandidateB-SourceLiftedConcealConstructorᵀ : Set
CandidateB-SourceLiftedConcealConstructorᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {B₀ : Ty Δᴿ} {B C : Ty (Nat.suc Δᴿ)}
    {cˢ : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
    {d : Conv↓ (Nat.suc Δᴿ) C B}
  → CTI2.SourceConcealPartnerOK W P cˢ Xᴿ? (V ↓ `∀↓ d)
  → CTI2.SourceConcealPartnerOK (CTI2.rightOnlyWorld W B₀) P cˢ
      (mapPivotChanges (bind B₀ ∷ []) Xᴿ?) (⇑ᵗᵐ V)


CandidateB-MatchedLiftedRevealConstructorᵀ : Set
CandidateB-MatchedLiftedRevealConstructorᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {B₀ : Ty Δᴿ} {B C : Ty (Nat.suc Δᴿ)}
    {cˢ : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
    {d : Conv↑ (Nat.suc Δᴿ) C B}
  → CTI2.MatchedConcealPartnerOK W P cˢ Xᴿ? (V ↑ `∀↑ d)
  → CTI2.MatchedConcealPartnerOK (CTI2.rightOnlyWorld W B₀) P cˢ
      (mapPivotChanges (bind B₀ ∷ []) Xᴿ?) (⇑ᵗᵐ V)


CandidateB-MatchedLiftedConcealConstructorᵀ : Set
CandidateB-MatchedLiftedConcealConstructorᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {B₀ : Ty Δᴿ} {B C : Ty (Nat.suc Δᴿ)}
    {cˢ : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
    {d : Conv↓ (Nat.suc Δᴿ) C B}
  → CTI2.MatchedConcealPartnerOK W P cˢ Xᴿ? (V ↓ `∀↓ d)
  → CTI2.MatchedConcealPartnerOK (CTI2.rightOnlyWorld W B₀) P cˢ
      (mapPivotChanges (bind B₀ ∷ []) Xᴿ?) (⇑ᵗᵐ V)


record CandidateBConstructors : Set where
  field
    seal-lifted-reveal-target :
      CandidateB-SealLiftedRevealConstructorᵀ
    seal-lifted-conceal-target :
      CandidateB-SealLiftedConcealConstructorᵀ
    source-lifted-reveal-target :
      CandidateB-SourceLiftedRevealConstructorᵀ
    source-lifted-conceal-target :
      CandidateB-SourceLiftedConcealConstructorᵀ
    matched-lifted-reveal-target :
      CandidateB-MatchedLiftedRevealConstructorᵀ
    matched-lifted-conceal-target :
      CandidateB-MatchedLiftedConcealConstructorᵀ
