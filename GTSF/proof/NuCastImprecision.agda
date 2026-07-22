module proof.NuCastImprecision where

-- File Charter:
--   * Embeds typed narrowing and widening coercions into type imprecision
--     under the sparse Nu-store well-formedness invariant.
--   * Mirrors the dense-store cast embedding while using only live-name
--     bounds, store typing, and uniqueness.
--   * Provides the intermediate precision edge needed by quotient `inst`
--     catch-up without strengthening the DGG world invariant.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_<_; suc; zero)
open import Data.Product using (_,_; proj₁)

open import Types
open import Coercions using (genᵈ; instᵈ)
import Coercions as C
open import ImprecisionWf
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
import NarrowWiden as NW
import NuStore as NS
open import TermTyping using (SealModeStore★)
open import proof.CastImprecision using
  ( castᵢ
  ; castᵢ-id-lookup
  ; castᵢ-star-lookup
  ; drop-target-castᵢ-gen
  ; drop-target-castᵢ-inst
  ; drop-targetᵢ
  ; instSafe-source-admissible
  ; genSafe-target-admissible
  ; ground⊑★
  ; sealMode⇒starAllowed
  ; seal★-ext-shift
  ; seal★-gen-shift
  ; seal★-inst-shift
  ; strictCrossNarrowing⇒crossNarrowing
  ; strictCrossWidening⇒crossWidening
  ; strictNarrowing⇒narrowing
  ; strictWidening⇒widening
  ; ⊑-trans-castᵢ
  )
open import proof.NuStoreProperties using
  (StoreWf-⟰ᵗ; StoreWf-bind)


nu-seal⊑★ :
  ∀ {μ Δ Σ α} →
  NS.StoreWf Δ Σ →
  C.sealModeAllowed (μ α) ≡ true →
  (α , ★) ∈ Σ →
  castᵢ μ Δ ∣ Δ ⊢ ＇ α ⊑ ★ ⊣ Δ
nu-seal⊑★ {α = α} wfΣ ok α★∈Σ =
  tagˣ (castᵢ-star-lookup α<Δ (sealMode⇒starAllowed ok)) α<Δ
  where
  α<Δ : α < _
  α<Δ = NS.bound (NS.at wfΣ) α★∈Σ

mutual
  nu-narrowing-gen⇒⊑ᵢ :
    ∀ {μ Δ Σ A B c} →
    NS.StoreWf Δ Σ →
    SealModeStore★ μ Σ →
    WfTy Δ A →
    occurs zero B ≡ true →
    genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ ⇑ᵗ A ⊒ B →
    NW.GenSafe c →
    castᵢ μ Δ ∣ Δ ⊢ `∀ B ⊑ A ⊣ Δ
  nu-narrowing-gen⇒⊑ᵢ {μ = μ} {Δ = Δ} wfΣ seal★ hA occB c⊒ safe =
    ν (genSafe-target-admissible (proj₁ c⊒) safe) occB
      (drop-targetᵢ hA (drop-target-castᵢ-gen {μ = μ} {Δ = Δ})
        (nu-narrowing⇒⊑ᵢ (StoreWf-⟰ᵗ wfΣ)
          (seal★-gen-shift seal★) c⊒))

  nu-widening-inst⇒⊑ᵢ :
    ∀ {μ Δ Σ A B c} →
    NS.StoreWf Δ Σ →
    SealModeStore★ μ Σ →
    WfTy Δ B →
    occurs zero A ≡ true →
    instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ
      ⊢ c ∶ A ⊑ ⇑ᵗ B →
    NW.InstSafe c →
    castᵢ μ Δ ∣ Δ ⊢ `∀ A ⊑ B ⊣ Δ
  nu-widening-inst⇒⊑ᵢ {μ = μ} {Δ = Δ}
      wfΣ seal★ hB occA c⊑ safe =
    ν (instSafe-source-admissible (proj₁ c⊑) safe) occA
      (drop-targetᵢ hB (drop-target-castᵢ-inst {μ = μ} {Δ = Δ})
        (nu-widening⇒⊑ᵢ (StoreWf-bind wfΣ wf★)
          (seal★-inst-shift seal★) c⊑))

  nu-narrowing⇒⊑ᵢ :
    ∀ {μ Δ Σ A B c} →
    NS.StoreWf Δ Σ →
    SealModeStore★ μ Σ →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    castᵢ μ Δ ∣ Δ ⊢ B ⊑ A ⊣ Δ
  nu-narrowing⇒⊑ᵢ wfΣ seal★
      (C.cast-id (wfVar X<Δ) ok , NW.cross (NW.id-＇ X)) =
    idˣ (castᵢ-id-lookup X<Δ) X<Δ X<Δ
  nu-narrowing⇒⊑ᵢ wfΣ seal★
      (C.cast-id wfBase ok , NW.cross (NW.id-‵ ι)) =
    idι
  nu-narrowing⇒⊑ᵢ wfΣ seal★
      (C.cast-id wf★ ok , NW.id★) =
    id★
  nu-narrowing⇒⊑ᵢ wfΣ seal★
      (C.cast-fun s⊢ t⊢ , NW.cross (sʷ NW.↦ tⁿ)) =
    nu-widening⇒⊑ᵢ wfΣ seal★ (s⊢ , sʷ)
      ↦ nu-narrowing⇒⊑ᵢ wfΣ seal★ (t⊢ , tⁿ)
  nu-narrowing⇒⊑ᵢ wfΣ seal★
      (C.cast-all c⊢ , NW.cross (NW.`∀ cⁿ)) =
    ∀ⁱ (nu-narrowing⇒⊑ᵢ (StoreWf-⟰ᵗ wfΣ)
          (seal★-ext-shift seal★) (c⊢ , cⁿ))
  nu-narrowing⇒⊑ᵢ wfΣ seal★
      (C.cast-gen hA occB c⊢ , NW.gen cⁿ) =
    nu-narrowing-gen⇒⊑ᵢ wfΣ seal★ hA occB
      (c⊢ , NW.genSafe→narrowing cⁿ) cⁿ
  nu-narrowing⇒⊑ᵢ wfΣ seal★
      (C.cast-untag hG G ok , NW.untag _) =
    ground⊑★ hG G ok
  nu-narrowing⇒⊑ᵢ wfΣ seal★
      (C.cast-seq s⊢ t⊢ , G NW.？︔ gⁿ) =
    ⊑-trans-castᵢ
      (nu-narrowing⇒⊑ᵢ wfΣ seal★
        (t⊢ , NW.cross (strictCrossNarrowing⇒crossNarrowing gⁿ)))
      (nu-narrowing⇒⊑ᵢ wfΣ seal★ (s⊢ , NW.untag G))
  nu-narrowing⇒⊑ᵢ wfΣ seal★
      (C.cast-seq s⊢ (C.cast-gen hG occ t⊢) ,
       NW.fun-untag-gen safe) =
    ⊑-trans-castᵢ
      (nu-narrowing-gen⇒⊑ᵢ wfΣ seal★ hG occ
        (t⊢ , NW.genSafe→narrowing safe) safe)
      (nu-narrowing⇒⊑ᵢ wfΣ seal★ (s⊢ , NW.untag ★⇒★))
  nu-narrowing⇒⊑ᵢ wfΣ seal★
      (C.cast-seal hA α∈Σ ok , NW.sealⁿ A α)
      rewrite NS.unique wfΣ α∈Σ (seal★ α ok) =
    nu-seal⊑★ wfΣ ok (seal★ α ok)
  nu-narrowing⇒⊑ᵢ wfΣ seal★
      (C.cast-seq s⊢ t⊢ , n NW.︔seal α) =
    ⊑-trans-castᵢ
      (nu-narrowing⇒⊑ᵢ wfΣ seal★ (t⊢ , NW.sealⁿ _ α))
      (nu-narrowing⇒⊑ᵢ wfΣ seal★
        (s⊢ , strictNarrowing⇒narrowing n))

  nu-widening⇒⊑ᵢ :
    ∀ {μ Δ Σ A B c} →
    NS.StoreWf Δ Σ →
    SealModeStore★ μ Σ →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    castᵢ μ Δ ∣ Δ ⊢ A ⊑ B ⊣ Δ
  nu-widening⇒⊑ᵢ wfΣ seal★
      (C.cast-id (wfVar X<Δ) ok , NW.cross (NW.id-＇ X)) =
    idˣ (castᵢ-id-lookup X<Δ) X<Δ X<Δ
  nu-widening⇒⊑ᵢ wfΣ seal★
      (C.cast-id wfBase ok , NW.cross (NW.id-‵ ι)) =
    idι
  nu-widening⇒⊑ᵢ wfΣ seal★
      (C.cast-id wf★ ok , NW.id★) =
    id★
  nu-widening⇒⊑ᵢ wfΣ seal★
      (C.cast-fun s⊢ t⊢ , NW.cross (sⁿ NW.↦ tʷ)) =
    nu-narrowing⇒⊑ᵢ wfΣ seal★ (s⊢ , sⁿ)
      ↦ nu-widening⇒⊑ᵢ wfΣ seal★ (t⊢ , tʷ)
  nu-widening⇒⊑ᵢ wfΣ seal★
      (C.cast-all c⊢ , NW.cross (NW.`∀ cʷ)) =
    ∀ⁱ (nu-widening⇒⊑ᵢ (StoreWf-⟰ᵗ wfΣ)
          (seal★-ext-shift seal★) (c⊢ , cʷ))
  nu-widening⇒⊑ᵢ wfΣ seal★
      (C.cast-inst hB occA c⊢ , NW.inst cʷ) =
    nu-widening-inst⇒⊑ᵢ wfΣ seal★ hB occA
      (c⊢ , NW.instSafe→widening cʷ) cʷ
  nu-widening⇒⊑ᵢ wfΣ seal★
      (C.cast-tag hG G ok , NW.tag _) =
    ground⊑★ hG G ok
  nu-widening⇒⊑ᵢ wfΣ seal★
      (C.cast-seq s⊢ t⊢ , gʷ NW.︔ G !) =
    ⊑-trans-castᵢ
      (nu-widening⇒⊑ᵢ wfΣ seal★
        (s⊢ , NW.cross (strictCrossWidening⇒crossWidening gʷ)))
      (nu-widening⇒⊑ᵢ wfΣ seal★ (t⊢ , NW.tag G))
  nu-widening⇒⊑ᵢ wfΣ seal★
      (C.cast-seq (C.cast-inst hG occ s⊢) t⊢ ,
       NW.inst-fun-tag safe) =
    ⊑-trans-castᵢ
      (nu-widening-inst⇒⊑ᵢ wfΣ seal★ hG occ
        (s⊢ , NW.instSafe→widening safe) safe)
      (nu-widening⇒⊑ᵢ wfΣ seal★ (t⊢ , NW.tag ★⇒★))
  nu-widening⇒⊑ᵢ wfΣ seal★
      (C.cast-unseal hA α∈Σ ok , NW.unsealʷ α A)
      rewrite NS.unique wfΣ α∈Σ (seal★ α ok) =
    nu-seal⊑★ wfΣ ok (seal★ α ok)
  nu-widening⇒⊑ᵢ wfΣ seal★
      (C.cast-seq s⊢ t⊢ , NW.unseal︔_ α w) =
    ⊑-trans-castᵢ
      (nu-widening⇒⊑ᵢ wfΣ seal★ (s⊢ , NW.unsealʷ α _))
      (nu-widening⇒⊑ᵢ wfΣ seal★
        (t⊢ , strictWidening⇒widening w))
