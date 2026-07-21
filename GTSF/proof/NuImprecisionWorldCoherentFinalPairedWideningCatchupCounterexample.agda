module
  proof.NuImprecisionWorldCoherentFinalPairedWideningCatchupCounterexample
  where

-- File Charter:
--   * Refutes unrestricted exact-world terminal paired-widening catch-up.
--   * Uses a matched dynamic store and the active-source-unseal versus
--     inert-target-variable-tag combination.
--   * Contains no postulates, holes, permissive options, or dispatcher import.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc; z<s)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import Coercions as C
open import Coercions using
  ( Inert
  ; instᵈ
  ; seal-or-idᵈ
  ; tag-or-idᵈ
  ; _!
  )
open import Conversion using (conceal-seal)
open import Imprecision using (_ˣ⊑ˣ_)
open import ImprecisionWf using
  ( id★
  ; idˣ
  ; tag_
  ; _∣_⊢_⊑_⊣_
  )
import NarrowWiden as NW
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
import NuReduction as R
open import NuReduction using
  ( StoreChanges
  ; keep
  ; seal-unseal
  ; _—→[_]_
  ; _—↠[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreCorresponds
  ; StoreImp
  ; correspondence-stored
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; seal★-tag-or-id
  ; store-matched
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; blame
  ; no•-$
  ; no•-⟨⟩
  ; _⟨_⟩
  ; $
  )
open import Primitives using (κℕ)
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; conv⊑convᵀ
  ; κ⊑κᵀ
  ; paired-conceal
  ; paired-conversion
  ; paired-widening
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑cast⊑ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( cast-inst
  ; cast-tag-or-id
  ; SealModeStore★
  )
open import Types using
  ( Ground
  ; Ty
  ; wfBase
  ; wfVar
  ; wf★
  ; ★
  ; ＇_
  ; ‵_
  ; `ℕ
  )
import Types as T
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionSimulationResultDef using
  ( LeftCatchupIndexedResult
  ; canonicalIndexedResults
  ; catchupIndexedResult
  ; catchupIndexedInvariant
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; sourceCatchup
  ; sourceIsValueOrBlame
  ; targetTail
  ; weak-indexed-result
  ; weakIndexedResult
  )
open import proof.NuImprecisionSourceTagCancellationLemma using
  (source-tag-cancellationᵀ)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent; world-coherent)
open import
  proof.NuImprecisionWorldCoherentFinalPairedWideningCatchupDef
  using (WorldCoherentFinalPairedWideningCatchupᵀ)
open import proof.NuImprecisionWorldCoherentResultDef using
  ( WorldCoherentLeftCatchupIndexedResult
  ; worldCatchupResult
  )
open import proof.NuReductionDeterminism using
  (pure-full-deterministic; value-irreducible)


private
  Φ₀ = (zero ˣ⊑ˣ zero) ∷ []

  Nat : Ty
  Nat = ‵ `ℕ

  ρ₀ : StoreImp Φ₀ (suc zero) (suc zero)
  ρ₀ = store-matched zero ★ zero ★ id★ ∷ []

  K : Term
  K = $ (κℕ zero)

  Tagged : Term
  Tagged = K ⟨ Nat ! ⟩

  Sealed : Term
  Sealed = Tagged ⟨ C.seal ★ zero ⟩

  Target : Term
  Target = Sealed ⟨ (＇ zero) ! ⟩

  SourceRedex : Term
  SourceRedex = Sealed ⟨ C.unseal zero ★ ⟩

  id-var : Φ₀ ∣ suc zero ⊢ ＇ zero ⊑ ＇ zero ⊣ suc zero
  id-var = idˣ (here refl) z<s z<s

  correspondence :
    StoreCorresponds ρ₀ zero ★ zero ★ id★
  correspondence = correspondence-stored (here refl)

  coherent : WorldCoherent ρ₀
  coherent = world-coherent
    λ { (here refl) (here refl) (here refl) →
          id★ , correspondence
      ; (here refl) (here refl) (there ())
      ; (here refl) (there ()) right∈
      ; (there ()) left∈ right∈
      }

  exclusive : SourceNameExclusive Φ₀
  exclusive (here ()) match∈
  exclusive (there ()) match∈

  source-store-wf : StoreWf (suc zero) (leftStoreⁱ ρ₀)
  source-store-wf =
    record
      { at = record
          { bound = λ { (here refl) → z<s ; (there ()) }
          ; wfTy = λ { (here refl) → wf★ ; (there ()) }
          }
      ; unique = λ
          { (here refl) (here refl) → refl
          ; (here refl) (there ())
          ; (there ()) right∈
          }
      }

  source-seal★ :
    SealModeStore★ (instᵈ tag-or-idᵈ) (leftStoreⁱ ρ₀)
  source-seal★ zero refl = here refl
  source-seal★ (suc α) ()

  value-K : Value K
  value-K = $ (κℕ zero)

  value-tagged : Value Tagged
  value-tagged = value-K ⟨ Nat ! ⟩

  value-sealed : Value Sealed
  value-sealed = value-tagged ⟨ C.seal ★ zero ⟩

  value-target : Value Target
  value-target = value-sealed ⟨ (＇ zero) ! ⟩

  no-tagged : No• Tagged
  no-tagged = no•-⟨⟩ no•-$

  no-sealed : No• Sealed
  no-sealed = no•-⟨⟩ no-tagged

  no-target : No• Target
  no-target = no•-⟨⟩ no-sealed

  tagged-bases :
    Φ₀ ∣ suc zero ∣ suc zero ∣ ρ₀ ∣ []
      ⊢ᴺ Tagged ⊑ Tagged ⦂ ★ ⊑ ★ ∶ id★
  tagged-bases =
    conv⊑convᵀ
      (paired-widening
        cast-tag-or-id seal★-tag-or-id
        (C.cast-tag wfBase (T.‵ `ℕ) refl , NW.tag (T.‵ `ℕ))
        cast-tag-or-id seal★-tag-or-id
        (C.cast-tag wfBase (T.‵ `ℕ) refl , NW.tag (T.‵ `ℕ)))
      κ⊑κᵀ

  matched-seals :
    Φ₀ ∣ suc zero ∣ suc zero ∣ ρ₀ ∣ []
      ⊢ᴺ Sealed ⊑ Sealed
      ⦂ ＇ zero ⊑ ＇ zero ∶ id-var
  matched-seals =
    conv⊑convᵀ
      (paired-conversion
        (paired-conceal
          { μ = seal-or-idᵈ } { μ′ = seal-or-idᵈ }
          correspondence
          (conceal-seal wf★ (here refl) refl)
          (conceal-seal wf★ (here refl) refl)))
      tagged-bases

  source-widening :
    instᵈ tag-or-idᵈ
      ∣ suc zero ∣ leftStoreⁱ ρ₀
      ⊢ C.unseal zero ★ ∶ ＇ zero ⊑ ★
  source-widening =
    C.cast-unseal wf★ (here refl) refl , NW.unsealʷ zero ★

  target-widening :
    tag-or-idᵈ ∣ suc zero ∣ rightStoreⁱ ρ₀
      ⊢ (＇ zero) ! ∶ ＇ zero ⊑ ★
  target-widening =
    C.cast-tag (wfVar z<s) (T.＇ zero) refl , NW.tag (T.＇ zero)

  target-inert : Inert ((＇ zero) !)
  target-inert = (＇ zero) !


value-trace-refl :
  ∀ {V N χs} →
  Value V →
  V —↠[ χs ] N →
  (χs ≡ []) × (N ≡ V)
value-trace-refl vV R.↠-refl = refl , refl
value-trace-refl vV (R.↠-step V→N trace) =
  ⊥-elim (value-irreducible vV V→N)


source-redex-not-final :
  ((Value SourceRedex × No• SourceRedex) ⊎
    (SourceRedex ≡ blame)) →
  ⊥
source-redex-not-final (inj₁ ((vV ⟨ () ⟩) , no-redex))
source-redex-not-final (inj₂ ())


source-trace-final :
  ∀ {χs N} →
  SourceRedex —↠[ χs ] N →
  ((Value N × No• N) ⊎ (N ≡ blame)) →
  (χs ≡ keep ∷ []) × (N ≡ Tagged)
source-trace-final R.↠-refl final =
  ⊥-elim (source-redex-not-final final)
source-trace-final (R.↠-step first tail) final
    with pure-full-deterministic (seal-unseal value-tagged) first
source-trace-final (R.↠-step first tail) final
    | refl , refl
    with value-trace-refl value-tagged tail
source-trace-final (R.↠-step first tail) final
    | refl , refl | refl , refl =
  refl , refl


no-base-var-relation :
  ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M N : Term}
    {p : Φ ∣ Δᴸ ⊢ Nat ⊑ ＇ zero ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ N ⦂ Nat ⊑ ＇ zero ∶ p →
  ⊥
no-base-var-relation {p = ()}


no-K-target-relation :
  ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ Nat ⊑ ★ ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ K ⊑ Target ⦂ Nat ⊑ ★ ∶ p →
  ⊥
no-K-target-relation
    (⊑cast⊒ᵀ mode seal★
      (C.cast-tag hG ground ok , NW.cross ()) inner q)
no-K-target-relation
    (⊑cast⊑ᵀ mode seal★
      (C.cast-tag hG (T.＇ .zero) ok , NW.tag (T.＇ .zero))
      inner q) =
  no-base-var-relation inner
no-K-target-relation
    (⊑cast⊑idᵀ seal★
      (C.cast-tag hG ground () , widening) inner q)
no-K-target-relation
    (allocation-prefixᵀ prefix inner K⊢ Target⊢) =
  no-K-target-relation inner


no-final-relation :
  ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ ★ ⊑ ★ ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ Tagged ⊑ Target ⦂ ★ ⊑ ★ ∶ p →
  ⊥
no-final-relation relation =
  no-K-target-relation
    (source-tag-cancellationᵀ
      (T.‵ `ℕ) value-K value-target no-target relation (tag `ℕ))


no-catchup :
  LeftCatchupIndexedResult
    {N = SourceRedex} {V′ = Target} {ρ = ρ₀} id★ →
  ⊥
no-catchup
    catchup@(left-indexed-catchup
      (weak-indexed-result result canonical)
      (left-catchup-invariant silent final)
      transport coherence)
    with source-trace-final (sourceCatchup result) final
       | value-trace-refl value-target (targetTail result)
no-catchup
    catchup@(left-indexed-catchup
      (weak-indexed-result result canonical)
      (left-catchup-invariant silent final)
      transport coherence)
    | refl , refl | refl , refl =
  no-final-relation canonical


world-coherent-final-paired-widening-catchup-fails :
  WorldCoherentFinalPairedWideningCatchupᵀ →
  ⊥
world-coherent-final-paired-widening-catchup-fails catchup =
  no-catchup
    (worldCatchupResult
      (catchup coherent exclusive source-store-wf
        (inj₁ (value-sealed , no-sealed))
        value-sealed no-sealed target-inert
        (cast-inst cast-tag-or-id) source-seal★ source-widening
        cast-tag-or-id seal★-tag-or-id target-widening
        matched-seals))
