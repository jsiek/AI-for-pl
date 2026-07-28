module proof.Compilation.CompileCanonicalPendingCloseExperiment where

-- File Charter:
--   * Tests a compiler-only pending-close boundary for canonical consistency
--     cast plans without changing the live term-imprecision relation.
--   * Shows that paired narrowing can be recorded immediately, ordinary
--     closing remains available in compatible cases, and value catch-up can
--     consume the pending boundary without widening compatibility.
--   * Includes the polymorphic-identity versus dynamic-function compiler pair
--     that refutes unconditional canonical widening compatibility.

import Coercions as C
open import Agda.Builtin.Equality using (_≡_; refl)
open import Compile using
  ( cast
  ; consistency-cast-plan
  ; down
  ; down-shape
  ; down⊒
  ; lower
  ; lower-selected
  ; lower⊑source
  ; lower⊑target
  ; up
  ; up-shape
  ; up⊑
  )
open import Data.List using ([])
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; z<s)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
import Imprecision as Imp
open import ImprecisionComposition using
  ( ⌊_⌋
  ; _；⌊_⌋≋ᵖ_；_
  )
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
import ImprecisionWf as IWF
open import NuStore using (StoreWf)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; blame
  ; no•-`
  ; no•-ƛ
  ; no•-Λ
  ; no•-⟨⟩
  ; ok-no
  ; Λ_
  ; ƛ_
  ; `_
  ; _⟨_⟩
  )
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  (CtxImp)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentLeftCatchupIndexedResult)
open import
  proof.WorldCoherent.Quotient.Final.NuImprecisionWorldCoherentQuotientFinalCatchupDef
  using (WorldCoherentQuotientFinalCatchupᵀ)
open import QuotientImprecisionCompatibility using
  ( QuotientNarrowingEliminationCompatible
  ; ReductionClosedQuotientWideningCompatible
  ; id-only↓
  ; non-function-elimination
  ; non-function-universal
  ; source-non-function
  )
open import QuotientedTermImprecision using
  ( Λ⊑ᵀ
  ; ƛ⊑ƛᵀ
  ; closeᵀ
  ; paired-downᵀ
  ; quotient-id-widening
  ; x⊑xᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types
open import
  proof.Compilation.CompileCastWideningCompatibilityCounterexample
  using
    ( source-consistency
    ; source-plan
    ; target-consistency
    ; target-plan
    )
open import
  proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleQuotient
  using (MLB-monotoneᵖ)
open import proof.DGG.Core.NuDGGClosedWorld using
  (empty-store-wf; empty-world-coherent)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityProof
  using (source-name-exclusive-empty)
import proof.NuCore.Relations.NuImprecisionTermContextDef as NTI
import proof.Store.Core.NuImprecisionRelationalStoreDef as NTS


data CanonicalPendingClose
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ A A′ : Ty}
    (ℓ : Label)
    (source-consistency : Δᴸ Imp.⊢ C ~ A)
    (target-consistency : Δᴿ Imp.⊢ C′ ~ A′)
    (pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
    (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ)
    (q :
      let plan = consistency-cast-plan ℓ source-consistency
          plan′ = consistency-cast-plan ℓ target-consistency
      in
      Φ ∣ Δᴸ ⊢ lower plan ⊑ᵖ lower plan′ ⊣ Δᴿ) : Set₁ where

  pending-close :
    let plan = consistency-cast-plan ℓ source-consistency
        plan′ = consistency-cast-plan ℓ target-consistency
    in
    Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ γ
      ⊢ᴺ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC →
    ⌊ lower⊑source plan ⌋ ；⌊ pC ⌋≋ᵖ q ；
      ⌊ lower⊑source plan′ ⌋ →
    ⌊ lower⊑target plan ⌋ ；⌊ pA ⌋≋ᵖ q ；
      ⌊ lower⊑target plan′ ⌋ →
    QuotientNarrowingEliminationCompatible
      Φ Δᴸ Δᴿ (down plan) (down plan′) pC q
      ⌊ lower⊑source plan ⌋ ⌊ lower⊑source plan′ ⌋ →
    CanonicalPendingClose ℓ source-consistency target-consistency pC pA q


pending-down :
  ∀ {Φ Δᴸ Δᴿ γ M M′ C C′ A A′ ℓ}
    {source-consistency : Δᴸ Imp.⊢ C ~ A}
    {target-consistency : Δᴿ Imp.⊢ C′ ~ A′}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q :
      let plan = consistency-cast-plan ℓ source-consistency
          plan′ = consistency-cast-plan ℓ target-consistency
      in
      Φ ∣ Δᴸ ⊢ lower plan ⊑ᵖ lower plan′ ⊣ Δᴿ} →
  CanonicalPendingClose ℓ source-consistency target-consistency pC pA q →
  let plan = consistency-cast-plan ℓ source-consistency
      plan′ = consistency-cast-plan ℓ target-consistency
  in
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ γ
    ⊢ᴺᵖ M ⟨ down plan ⟩ ⊑ M′ ⟨ down plan′ ⟩
    ⦂ lower plan ⊑ᵖ lower plan′
    ∶ q
pending-down
    {ℓ = ℓ}
    {source-consistency = source-consistency}
    {target-consistency = target-consistency}
    (pending-close inner down-square up-square down-compatible) =
  let plan = consistency-cast-plan ℓ source-consistency
      plan′ = consistency-cast-plan ℓ target-consistency
  in
  paired-downᵀ inner
    id-only↓ (down⊒ plan) (down-shape plan)
    id-only↓ (down⊒ plan′) (down-shape plan′)
    down-square down-compatible


pending-compatible-close :
  ∀ {Φ Δᴸ Δᴿ γ M M′ C C′ A A′ ℓ}
    {source-consistency : Δᴸ Imp.⊢ C ~ A}
    {target-consistency : Δᴿ Imp.⊢ C′ ~ A′}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q :
      let plan = consistency-cast-plan ℓ source-consistency
          plan′ = consistency-cast-plan ℓ target-consistency
      in
      Φ ∣ Δᴸ ⊢ lower plan ⊑ᵖ lower plan′ ⊣ Δᴿ} →
  (pending :
    CanonicalPendingClose
      ℓ source-consistency target-consistency pC pA q) →
  let plan = consistency-cast-plan ℓ source-consistency
      plan′ = consistency-cast-plan ℓ target-consistency
  in
  ReductionClosedQuotientWideningCompatible
    Φ Δᴸ Δᴿ (up plan) (up plan′)
    q pA ⌊ lower⊑target plan ⌋ ⌊ lower⊑target plan′ ⌋ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ γ
    ⊢ᴺ cast plan M ⊑ cast plan′ M′ ⦂ A ⊑ A′ ∶ pA
pending-compatible-close
    {ℓ = ℓ}
    {source-consistency = source-consistency}
    {target-consistency = target-consistency}
    {pA = pA}
    pending@(pending-close _ _ up-square _)
    up-compatible =
  let plan = consistency-cast-plan ℓ source-consistency
      plan′ = consistency-cast-plan ℓ target-consistency
  in
  closeᵀ
    (pending-down pending)
    (quotient-id-widening (up⊑ plan) (up⊑ plan′))
    pA (up-shape plan) (up-shape plan′) up-square up-compatible


pending-final-catchup :
  ∀ {Φ Δᴸ Δᴿ C C′ A A′ V V′ ℓ}
    {source-consistency : Δᴸ Imp.⊢ C ~ A}
    {target-consistency : Δᴿ Imp.⊢ C′ ~ A′}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q :
      let plan = consistency-cast-plan ℓ source-consistency
          plan′ = consistency-cast-plan ℓ target-consistency
      in
      Φ ∣ Δᴸ ⊢ lower plan ⊑ᵖ lower plan′ ⊣ Δᴿ} →
  WorldCoherentQuotientFinalCatchupᵀ →
  WorldCoherent {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} [] →
  SourceNameExclusive Φ →
  StoreWf Δᴸ [] →
  (pending :
    CanonicalPendingClose
      {γ = []} {M = V} {M′ = V′}
      ℓ source-consistency target-consistency pC pA q) →
  let plan = consistency-cast-plan ℓ source-consistency
      plan′ = consistency-cast-plan ℓ target-consistency
  in
  RuntimeOK (cast plan V) →
  Value V′ →
  No• V′ →
  C.Inert (down plan′) →
  C.Inert (up plan′) →
  ((Value V × No• V) ⊎ V ≡ blame) →
  WorldCoherentLeftCatchupIndexedResult
    {N = cast plan V}
    {V′ = cast plan′ V′}
    {ρ = []} pA
pending-final-catchup
    {ℓ = ℓ}
    {source-consistency = source-consistency}
    {target-consistency = target-consistency}
    final coherent exclusive store-wf
    pending@(pending-close _ _ up-square _)
    runtime value′ no-bullet′ inert-down′ inert-up′ final-source =
  let plan = consistency-cast-plan ℓ source-consistency
      plan′ = consistency-cast-plan ℓ target-consistency
  in
  final coherent exclusive store-wf runtime value′ no-bullet′
    inert-down′ inert-up′
    (pending-down pending)
    (quotient-id-widening (up⊑ plan) (up⊑ plan′))
    (up-shape plan) (up-shape plan′) up-square final-source


concrete-input-imprecision :
  [] ∣ zero ⊢
    `∀ (＇ zero ⇒ ＇ zero) ⊑ ★ ⇒ ★
    ⊣ zero
concrete-input-imprecision =
  IWF.ν Imp.nonvar-fun refl
    ((IWF.tagˣ (here refl) z<s) IWF.↦
     (IWF.tagˣ (here refl) z<s))


concrete-inner :
  [] ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ Λ (ƛ (` zero)) ⊑ ƛ (` zero)
    ⦂ `∀ (＇ zero ⇒ ＇ zero) ⊑ ★ ⇒ ★
    ∶ concrete-input-imprecision
concrete-inner =
  Λ⊑ᵀ refl
    NTS.lift-left-store-[]
    NTI.lift-left-ctx-[]
    (Value.ƛ (` zero))
    (ƛ⊑ƛᵀ (wfVar z<s) wf★ (x⊑xᵀ Z))


concrete-canonical-pending-close :
  Σ[ q ∈ [] ∣ zero ⊢
      lower source-plan ⊑ᵖ lower target-plan ⊣ zero ]
    CanonicalPendingClose
      {M = Λ (ƛ (` zero))}
      {M′ = ƛ (` zero)}
      zero source-consistency target-consistency
      concrete-input-imprecision IWF.id★ q
concrete-canonical-pending-close
    with MLB-monotoneᵖ
      concrete-input-imprecision IWF.id★
      (lower-selected source-plan)
      (lower-selected target-plan)
concrete-canonical-pending-close
    | q , down-square , up-square =
  q ,
  pending-close concrete-inner down-square up-square
    (non-function-elimination
      (source-non-function non-function-universal))


concrete-operational-final-catchup :
  WorldCoherentQuotientFinalCatchupᵀ →
  WorldCoherentLeftCatchupIndexedResult
    {N = cast source-plan (Λ (ƛ (` zero)))}
    {V′ = cast target-plan (ƛ (` zero))}
    {ρ = []} IWF.id★
concrete-operational-final-catchup final
    with concrete-canonical-pending-close
concrete-operational-final-catchup final | q , pending =
  pending-final-catchup final
    empty-world-coherent source-name-exclusive-empty empty-store-wf
    pending
    (ok-no
      (no•-⟨⟩
        (no•-⟨⟩ (no•-Λ (no•-ƛ no•-`)))))
    (Value.ƛ (` zero))
    (no•-ƛ no•-`)
    (C._↦_ (C.id ★) (C.id ★))
    ((★ ⇒ ★) C.!)
    (inj₁
      ( Value.Λ (Value.ƛ (` zero))
      , no•-Λ (no•-ƛ no•-`)
      ))
