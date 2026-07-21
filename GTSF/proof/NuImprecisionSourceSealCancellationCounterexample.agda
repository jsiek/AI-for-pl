module proof.NuImprecisionSourceSealCancellationCounterexample where

-- File Charter:
--   * Records a strict counterexample to source-seal cancellation without
--     source-name role exclusivity.
--   * Isolates the incompatible `tagˣ` branch: the source name can also occur
--     in a matched row whose target seal remains beneath a target tag.
--   * Contains no postulates, holes, permissive options, or simulation import.

open import Agda.Builtin.Equality using (refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc; z<s)
open import Data.Product using (_×_; _,_)
import Coercions as C
open import Coercions using (_!)
open import Conversion using (conceal-seal)
open import Imprecision using (_ˣ⊑★; _ˣ⊑ˣ_)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; idι; idˣ; tag_; tagˣ)
import NarrowWiden as NW
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
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑cast⊑ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (cast-tag-or-id)
open import Types using
  (Ty; wfBase; wfVar; ★; ＇_; ‵_; `ℕ)
import Types as T
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent; world-coherent)


private
  Φ₀ = (zero ˣ⊑★) ∷ (zero ˣ⊑ˣ zero) ∷ []

  Nat : Ty
  Nat = ‵ `ℕ

  ρ₀ : StoreImp Φ₀ (suc zero) (suc zero)
  ρ₀ = store-matched zero Nat zero Nat idι ∷ []

  K : Term
  K = $ (κℕ zero)

  SourceSealed : Term
  SourceSealed = K ⟨ C.seal Nat zero ⟩

  TargetSealed : Term
  TargetSealed = K ⟨ C.seal Nat zero ⟩

  TargetTagged : Term
  TargetTagged = TargetSealed ⟨ (＇ zero) ! ⟩

  id-var : Φ₀ ∣ suc zero ⊢ ＇ zero ⊑ ＇ zero ⊣ suc zero
  id-var = idˣ (there (here refl)) z<s z<s

  tag-var : Φ₀ ∣ suc zero ⊢ ＇ zero ⊑ ★ ⊣ suc zero
  tag-var = tagˣ (here refl) z<s

  tag-nat : Φ₀ ∣ suc zero ⊢ Nat ⊑ ★ ⊣ suc zero
  tag-nat = tag `ℕ

  correspondence :
    StoreCorresponds ρ₀ zero Nat zero Nat idι
  correspondence = correspondence-stored (here refl)

  coherent : WorldCoherent ρ₀
  coherent = world-coherent
    λ { (here ())
      ; (there (here refl)) (here refl) (here refl) →
          idι , correspondence
      ; (there (here refl)) (here refl) (there ())
      ; (there (here refl)) (there ()) right∈
      ; (there (there ()))
      }

  source-store-wf : StoreWf (suc zero) (leftStoreⁱ ρ₀)
  source-store-wf =
    record
      { at = record
          { bound = λ { (here refl) → z<s ; (there ()) }
          ; wfTy = λ { (here refl) → wfBase ; (there ()) }
          }
      ; unique = λ
          { (here refl) (here refl) → refl
          ; (here refl) (there ())
          ; (there ()) right∈
          }
      }

  value-K : Value K
  value-K = $ (κℕ zero)

  value-source-sealed : Value SourceSealed
  value-source-sealed = value-K ⟨ C.seal Nat zero ⟩

  value-target-sealed : Value TargetSealed
  value-target-sealed = value-K ⟨ C.seal Nat zero ⟩

  value-target-tagged : Value TargetTagged
  value-target-tagged = value-target-sealed ⟨ (＇ zero) ! ⟩

  no-target-tagged : No• TargetTagged
  no-target-tagged = no•-⟨⟩ (no•-⟨⟩ no•-$)

  matched-seals :
    Φ₀ ∣ suc zero ∣ suc zero ∣ ρ₀ ∣ []
      ⊢ᴺ SourceSealed ⊑ TargetSealed
      ⦂ ＇ zero ⊑ ＇ zero ∶ id-var
  matched-seals =
    conv⊑convᵀ
      (paired-conversion
        (paired-conceal
          {μ = C.seal-or-idᵈ} {μ′ = C.seal-or-idᵈ} correspondence
          (conceal-seal wfBase (here refl) refl)
          (conceal-seal wfBase (here refl) refl)))
      κ⊑κᵀ

  cancellation-premise :
    Φ₀ ∣ suc zero ∣ suc zero ∣ ρ₀ ∣ []
      ⊢ᴺ SourceSealed ⊑ TargetTagged
      ⦂ ＇ zero ⊑ ★ ∶ tag-var
  cancellation-premise =
    ⊑cast⊑ᵀ cast-tag-or-id seal★-tag-or-id
      (C.cast-tag (wfVar z<s) (T.＇ zero) refl ,
        NW.tag (T.＇ zero))
      matched-seals tag-var

  no-base-var-relation :
    ∀ {ρ : StoreImp Φ₀ (suc zero) (suc zero)}
      {M N : Term}
      {p : Φ₀ ∣ suc zero ⊢ Nat ⊑ ＇ zero ⊣ suc zero} →
    Φ₀ ∣ suc zero ∣ suc zero ∣ ρ ∣ []
      ⊢ᴺ M ⊑ N ⦂ Nat ⊑ ＇ zero ∶ p →
    ⊥
  no-base-var-relation {p = ()}

  no-cancellation-conclusion :
    ∀ {ρ : StoreImp Φ₀ (suc zero) (suc zero)} →
    Φ₀ ∣ suc zero ∣ suc zero ∣ ρ ∣ []
      ⊢ᴺ K ⊑ TargetTagged ⦂ Nat ⊑ ★ ∶ tag-nat →
    ⊥
  no-cancellation-conclusion
      (⊑cast⊒ᵀ mode seal★
        (C.cast-tag hG ground ok , NW.cross ()) inner q)
  no-cancellation-conclusion
      (⊑cast⊑ᵀ mode seal★
        (C.cast-tag hG (T.＇ .zero) ok , NW.tag (T.＇ .zero))
        inner q) =
    no-base-var-relation inner
  no-cancellation-conclusion
      (⊑cast⊑idᵀ seal★
        (C.cast-tag hG ground () , widening) inner q)
  no-cancellation-conclusion
      (allocation-prefixᵀ prefix inner K⊢ TargetTagged⊢) =
    no-cancellation-conclusion inner


source-seal-cancellation-needs-exclusivity :
  (Φ₀ ∣ suc zero ∣ suc zero ∣ ρ₀ ∣ []
    ⊢ᴺ SourceSealed ⊑ TargetTagged
    ⦂ ＇ zero ⊑ ★ ∶ tag-var) ×
  (Φ₀ ∣ suc zero ∣ suc zero ∣ ρ₀ ∣ []
    ⊢ᴺ K ⊑ TargetTagged ⦂ Nat ⊑ ★ ∶ tag-nat →
    ⊥)
source-seal-cancellation-needs-exclusivity =
  cancellation-premise , no-cancellation-conclusion
