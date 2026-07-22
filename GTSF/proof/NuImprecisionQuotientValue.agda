module proof.NuImprecisionQuotientValue where

-- File Charter:
--   * Isolates the active value-shaped quotient cast-spine obligation.
--   * Closes the body-blame and inert/inert source cases.
--   * Returns outer `inst` allocation traces to the recursive dispatcher.
--   * Depends only on the stable weak-simulation core and quotient relation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; _×_; proj₁; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import Relation.Nullary using (no; yes)

open import ImprecisionWf using
  ( _∣_⊢_⊑_⊣_
  ; id★
  ; idˣ
  ; idι
  ; tag_
  ; tag_⇛_
  ; tagˣ
  )
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import Coercions using
  ( Inert
  ; gen
  ; inst
  ; seal
  ; unseal
  ; _︔_
  ; _!
  ; _？
  ; _↦_
  ; `∀
  ; ⇑ᶜ
  ; _∣_∣_⊢_∶_=⇒_
  )
import Coercions as C
import NarrowWiden as NW
open NW using (_∣_∣_⊢_∶_⊑_)
open NW using (_∣_∣_⊢_∶_⊒_)
open import NuReduction using
  ( β-id
  ; β-inst
  ; β-seq
  ; bind
  ; blame-⟨⟩
  ; keep
  ; pure-step
  ; seal-unseal
  ; tag-untag-bad
  ; tag-untag-ok
  ; ξ-⟨⟩
  ; ν-step
  ; _—→_
  ; _—→[_]_
  ; _—↠[_]_
  ; ↠-refl
  ; ↠-step
  )
open import NuTerms using
  ( No•
  ; Value
  ; blame
  ; no•-⟨⟩
  ; ok-no
  ; _•
  ; _⟨_⟩
  )
import NuTerms as NT
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ; seal★-tag-or-id)
open import QuotientedTermImprecision
open import TermTyping using (forget; _∣_∣_⊢_⦂_)
open import Types using (Ground; ★)
import Types as T
open import proof.CoercionProperties using (inert-dec)
open import proof.CastImprecision using
  ( strictCrossNarrowing⇒crossNarrowing
  ; strictCrossWidening⇒crossWidening
  )
open import proof.ForallPermutationProperties using
  (⊑ᵖ-arrow-left-shape; ⊑ᵖ-ground-left
  ; ⊑ᵖ-star-left-eq)
open import proof.GenSafeProperties using (genSafe-star-source⊥)
open import proof.NuImprecisionCatchupComposition using
  (left-catchup-indexed-prepend-keepᵀ)
open import proof.NuImprecisionSimulationCore
open import proof.NuImprecisionSimulationResultDef
open import proof.NuPreservation using (value-no-step)
open import proof.NuProgress using
  (Progress; crash; done; progress-cast; step)
open import TermTyping using (cast-gen; cast-tag-or-id)

false≢true : false ≡ true → ⊥
false≢true ()

id-only-no-seal : ∀ α → C.sealModeAllowed (C.id-onlyᵈ α) ≡ false
id-only-no-seal α = refl

gen-tag-or-id-no-seal :
  ∀ α →
  C.sealModeAllowed (C.genᵈ C.tag-or-idᵈ α) ≡ false
gen-tag-or-id-no-seal zero = refl
gen-tag-or-id-no-seal (suc α) = refl

ground-imprecision-target-all-impossible :
  ∀ {Φ Δᴸ Δᴿ G B} →
  Ground G →
  Φ ∣ Δᴸ ⊢ G ⊑ T.`∀ B ⊣ Δᴿ →
  ⊥
ground-imprecision-target-all-impossible (T.＇ α) ()
ground-imprecision-target-all-impossible (T.‵ ι) ()
ground-imprecision-target-all-impossible T.★⇒★ ()

ground-star-inert-narrowing-no-seal :
  ∀ {Φ Δᴸ Δᴿ μ Σ G d D} →
  (∀ α → C.sealModeAllowed (μ α) ≡ false) →
  Ground G →
  Φ ∣ Δᴸ ⊢ G ⊑ D ⊣ Δᴿ →
  μ ∣ Δᴿ ∣ Σ ⊢ d ∶ ★ ⊒ D →
  Inert d →
  ⊥
ground-star-inert-narrowing-no-seal
    no-seal gG q (_ , NW.cross ()) (G !)
ground-star-inert-narrowing-no-seal no-seal gG q
    (C.cast-seal h★ α∈Σ ok , narrowing) (seal ★ α) =
  false≢true (trans (sym (no-seal α)) ok)
ground-star-inert-narrowing-no-seal
    no-seal gG q (() , narrowing) (c ↦ d)
ground-star-inert-narrowing-no-seal
    no-seal gG q (() , narrowing) (`∀ c)
ground-star-inert-narrowing-no-seal no-seal gG q
    (C.cast-gen h★ occ c⊢ , NW.gen narrowing) (gen ★ c) =
  ground-imprecision-target-all-impossible gG q

inert-narrowing-target-var-no-seal :
  ∀ {μ Δ Σ d C α} →
  (∀ β → C.sealModeAllowed (μ β) ≡ false) →
  μ ∣ Δ ∣ Σ ⊢ d ∶ C ⊒ T.＇ α →
  Inert d →
  ⊥
inert-narrowing-target-var-no-seal
    no-seal (_ , NW.cross ()) (G !)
inert-narrowing-target-var-no-seal no-seal
    (C.cast-seal hA α∈Σ ok , narrowing) (seal A α) =
  false≢true (trans (sym (no-seal α)) ok)
inert-narrowing-target-var-no-seal
    no-seal (() , narrowing) (c ↦ d)
inert-narrowing-target-var-no-seal
    no-seal (() , narrowing) (`∀ c)
inert-narrowing-target-var-no-seal
    no-seal (() , narrowing) (gen A c)

inert-narrowing-target-base :
  ∀ {μ Δ Σ d C ι} →
  μ ∣ Δ ∣ Σ ⊢ d ∶ C ⊒ T.‵ ι →
  Inert d →
  ⊥
inert-narrowing-target-base (_ , NW.cross ()) (G !)
inert-narrowing-target-base (() , narrowing) (seal A α)
inert-narrowing-target-base (() , narrowing) (c ↦ d)
inert-narrowing-target-base (() , narrowing) (`∀ c)
inert-narrowing-target-base (() , narrowing) (gen A c)

inert-narrowing-target-star :
  ∀ {μ Δ Σ d C} →
  μ ∣ Δ ∣ Σ ⊢ d ∶ C ⊒ ★ →
  Inert d →
  ⊥
inert-narrowing-target-star (_ , NW.cross ()) (G !)
inert-narrowing-target-star (() , narrowing) (seal A α)
inert-narrowing-target-star (() , narrowing) (c ↦ d)
inert-narrowing-target-star (() , narrowing) (`∀ c)
inert-narrowing-target-star (() , narrowing) (gen A c)

inert-narrowing-star-to-arrow :
  ∀ {μ Δ Σ d A B} →
  μ ∣ Δ ∣ Σ ⊢ d ∶ ★ ⊒ A T.⇒ B →
  Inert d →
  ⊥
inert-narrowing-star-to-arrow (_ , NW.cross ()) (G !)
inert-narrowing-star-to-arrow (() , narrowing) (seal A α)
inert-narrowing-star-to-arrow (() , narrowing) (c ↦ d)
inert-narrowing-star-to-arrow (() , narrowing) (`∀ c)
inert-narrowing-star-to-arrow (() , narrowing) (gen A c)

inert-narrowing-source-star-no-seal :
  ∀ {μ Δ Σ d B} →
  (∀ α → C.sealModeAllowed (μ α) ≡ false) →
  μ ∣ Δ ∣ Σ ⊢ d ∶ ★ ⊒ B →
  Inert d →
  ⊥
inert-narrowing-source-star-no-seal
    no-seal (_ , NW.cross ()) (G !)
inert-narrowing-source-star-no-seal no-seal
    (C.cast-seal hA α∈Σ ok , narrowing) (seal A α) =
  false≢true (trans (sym (no-seal α)) ok)
inert-narrowing-source-star-no-seal
    no-seal (() , narrowing) (c ↦ d)
inert-narrowing-source-star-no-seal
    no-seal (() , narrowing) (`∀ c)
inert-narrowing-source-star-no-seal no-seal
    (C.cast-gen h★ occ c⊢ , NW.gen safe) (gen ★ c) =
  genSafe-star-source⊥ c⊢ safe

cast-value-inert :
  ∀ {V c} →
  Value (V ⟨ c ⟩) →
  Inert c
cast-value-inert (vV ⟨ inert ⟩) = inert

strict-cross-widening-inert :
  ∀ {c} →
  NW.StrictCrossWidening c →
  Inert c
strict-cross-widening-inert (NW.cw-funˡ n w) = _ ↦ _
strict-cross-widening-inert (NW.cw-funʳ n w) = _ ↦ _
strict-cross-widening-inert (NW.cw-all w) = `∀ _

strict-cross-widening-ground-star :
  ∀ {Φ Δᴸ Δᴿ μ Σ s D G} →
  Ground G →
  NW.StrictCrossWidening s →
  μ ∣ Δᴸ ∣ Σ ⊢ s ∶ D ⊑ G →
  Φ ∣ Δᴸ ⊢ G ⊑ ★ ⊣ Δᴿ
strict-cross-widening-ground-star
    (T.＇ α) (NW.cw-funˡ n w) ()
strict-cross-widening-ground-star
    (T.＇ α) (NW.cw-funʳ n w) ()
strict-cross-widening-ground-star
    (T.＇ α) (NW.cw-all w) ()
strict-cross-widening-ground-star
    (T.‵ ι) (NW.cw-funˡ n w) ()
strict-cross-widening-ground-star
    (T.‵ ι) (NW.cw-funʳ n w) ()
strict-cross-widening-ground-star
    (T.‵ ι) (NW.cw-all w) ()
strict-cross-widening-ground-star
    T.★⇒★ (NW.cw-funˡ n w) (C.cast-fun s⊢ t⊢ , widening) =
  tag id★ ⇛ id★
strict-cross-widening-ground-star
    T.★⇒★ (NW.cw-funʳ n w) (C.cast-fun s⊢ t⊢ , widening) =
  tag id★ ⇛ id★
strict-cross-widening-ground-star
    T.★⇒★ (NW.cw-all w) ()

strict-cross-narrowing-inert :
  ∀ {c} →
  NW.StrictCrossNarrowing c →
  Inert c
strict-cross-narrowing-inert (NW.cn-funˡ w n) = _ ↦ _
strict-cross-narrowing-inert (NW.cn-funʳ w n) = _ ↦ _
strict-cross-narrowing-inert (NW.cn-all n) = `∀ _

strict-cross-narrowing-ground-star :
  ∀ {Φ Δᴸ Δᴿ μ Σ g G D} →
  Ground G →
  NW.StrictCrossNarrowing g →
  μ ∣ Δᴸ ∣ Σ ⊢ g ∶ G ⊒ D →
  Φ ∣ Δᴸ ⊢ G ⊑ ★ ⊣ Δᴿ
strict-cross-narrowing-ground-star
    (T.＇ α) (NW.cn-funˡ w n) ()
strict-cross-narrowing-ground-star
    (T.＇ α) (NW.cn-funʳ w n) ()
strict-cross-narrowing-ground-star
    (T.＇ α) (NW.cn-all n) ()
strict-cross-narrowing-ground-star
    (T.‵ ι) (NW.cn-funˡ w n) ()
strict-cross-narrowing-ground-star
    (T.‵ ι) (NW.cn-funʳ w n) ()
strict-cross-narrowing-ground-star
    (T.‵ ι) (NW.cn-all n) ()
strict-cross-narrowing-ground-star
    T.★⇒★ (NW.cn-funˡ w n) (C.cast-fun s⊢ t⊢ , narrowing) =
  tag id★ ⇛ id★
strict-cross-narrowing-ground-star
    T.★⇒★ (NW.cn-funʳ w n) (C.cast-fun s⊢ t⊢ , narrowing) =
  tag id★ ⇛ id★
strict-cross-narrowing-ground-star
    T.★⇒★ (NW.cn-all n) ()

strict-cross-narrowing-ground-target-arrow :
  ∀ {Δ Σ μ g G D} →
  Ground G →
  NW.StrictCrossNarrowing g →
  μ ∣ Δ ∣ Σ ⊢ g ∶ G ⊒ D →
  ∃[ A ] ∃[ B ] D ≡ A T.⇒ B
strict-cross-narrowing-ground-target-arrow
    (T.＇ α) (NW.cn-funˡ w n) ()
strict-cross-narrowing-ground-target-arrow
    (T.＇ α) (NW.cn-funʳ w n) ()
strict-cross-narrowing-ground-target-arrow
    (T.＇ α) (NW.cn-all n) ()
strict-cross-narrowing-ground-target-arrow
    (T.‵ ι) (NW.cn-funˡ w n) ()
strict-cross-narrowing-ground-target-arrow
    (T.‵ ι) (NW.cn-funʳ w n) ()
strict-cross-narrowing-ground-target-arrow
    (T.‵ ι) (NW.cn-all n) ()
strict-cross-narrowing-ground-target-arrow
    T.★⇒★ (NW.cn-funˡ w n) (C.cast-fun s⊢ t⊢ , narrowing) =
  _ , _ , refl
strict-cross-narrowing-ground-target-arrow
    T.★⇒★ (NW.cn-funʳ w n) (C.cast-fun s⊢ t⊢ , narrowing) =
  _ , _ , refl
strict-cross-narrowing-ground-target-arrow
    T.★⇒★ (NW.cn-all n) ()

star-imprecision-target :
  ∀ {Φ Δᴸ Δᴿ B} →
  Φ ∣ Δᴸ ⊢ ★ ⊑ B ⊣ Δᴿ →
  B ≡ ★
star-imprecision-target id★ = refl

star-term-imprecision-target :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ B}
  {p : Φ ∣ Δᴸ ⊢ ★ ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ M ⊑ M′ ⦂ ★ ⊑ B ∶ p →
  B ≡ ★
star-term-imprecision-target {p = p} M⊑M′ =
  star-imprecision-target p

cast-value-step-change :
  ∀ {χ V c N} →
  Value V →
  (V ⟨ c ⟩) —→[ χ ] N →
  χ ≡ keep
cast-value-step-change vV (pure-step red) = refl
cast-value-step-change vV (ξ-⟨⟩ V→N) =
  ⊥-elim (value-no-step vV V→N)

active-value-cast-step :
  ∀ {μ Δ Σ V c A B} →
  Value V →
  No• V →
  NT._∣_∣_⊢_⦂_ Δ Σ [] V A →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  (Inert c → ⊥) →
  ∃[ N ] ((V ⟨ c ⟩) —→[ keep ] N)
active-value-cast-step {V = V} {c = c} vV noV V⊢ c⊢ not-inert
    with progress-cast (ok-no noV) c⊢ V⊢
active-value-cast-step {V = V} {c = c} vV noV V⊢ c⊢ not-inert
    | done (vW ⟨ inert ⟩) =
  ⊥-elim (not-inert inert)
active-value-cast-step {V = V} {c = c} vV noV V⊢ c⊢ not-inert
    | step {χ = χ} {N = N} cast→ =
  N , subst
    (λ χ′ → (V ⟨ c ⟩) —→[ χ′ ] N)
    (cast-value-step-change vV cast→) cast→
active-value-cast-step {V = V} {c = c} vV noV V⊢ c⊢ not-inert
    | crash ()

active-double-cast-step :
  ∀ {μ ν Δ Σ V d u C D A} →
  Value V →
  No• V →
  NT._∣_∣_⊢_⦂_ Δ Σ [] V C →
  μ ∣ Δ ∣ Σ ⊢ d ∶ C =⇒ D →
  ν ∣ Δ ∣ Σ ⊢ u ∶ D =⇒ A →
  (Inert d × Inert u → ⊥) →
  ∃[ N ] (((V ⟨ d ⟩) ⟨ u ⟩) —→[ keep ] N)
active-double-cast-step vV noV V⊢ d⊢ u⊢ source-active
    with inert-dec _
active-double-cast-step vV noV V⊢ d⊢ u⊢ source-active
    | no not-inert-d
    with active-value-cast-step vV noV V⊢ d⊢ not-inert-d
active-double-cast-step vV noV V⊢ d⊢ u⊢ source-active
    | no not-inert-d | N , source→ =
  N ⟨ _ ⟩ , ξ-⟨⟩ source→
active-double-cast-step vV noV V⊢ d⊢ u⊢ source-active
    | yes inert-d
    with active-value-cast-step
      (vV ⟨ inert-d ⟩) (no•-⟨⟩ noV)
      (NT.⊢⟨⟩ d⊢ V⊢) u⊢
      (λ inert-u → source-active (inert-d , inert-u))
active-double-cast-step vV noV V⊢ d⊢ u⊢ source-active
    | yes inert-d | N , source→ =
  N , source→

outer-inst-allocation-trace :
  ∀ {V d B s} →
  No• V →
  Value (V ⟨ d ⟩) →
  ((V ⟨ d ⟩) ⟨ inst B s ⟩)
    —↠[ keep ∷ bind ★ ∷ [] ]
      ((NT.⇑ᵗᵐ (V ⟨ d ⟩)) •) ⟨ s ⟩
outer-inst-allocation-trace noV vW =
  ↠-step (pure-step (β-inst vW))
    (↠-step (ν-step vW (no•-⟨⟩ noV)) ↠-refl)

outer-inst-fun-tag-allocation-trace :
  ∀ {V d B s} →
  No• V →
  Value (V ⟨ d ⟩) →
  ((V ⟨ d ⟩) ⟨ inst B s ︔ ((★ T.⇒ ★) !) ⟩)
    —↠[ keep ∷ keep ∷ bind ★ ∷ [] ]
      ((((NT.⇑ᵗᵐ (V ⟨ d ⟩)) •) ⟨ s ⟩)
        ⟨ ⇑ᶜ ((★ T.⇒ ★) !) ⟩)
outer-inst-fun-tag-allocation-trace noV vW =
  ↠-step (pure-step (β-seq vW))
    (↠-step (ξ-⟨⟩ (pure-step (β-inst vW)))
      (↠-step
        (ξ-⟨⟩ (ν-step vW (no•-⟨⟩ noV))) ↠-refl))

inner-inst-allocation-trace :
  ∀ {V B s u} →
  Value V →
  No• V →
  ((V ⟨ inst B s ⟩) ⟨ u ⟩)
    —↠[ keep ∷ bind ★ ∷ [] ]
      (((NT.⇑ᵗᵐ V) •) ⟨ s ⟩) ⟨ ⇑ᶜ u ⟩
inner-inst-allocation-trace vV noV =
  ↠-step (ξ-⟨⟩ (pure-step (β-inst vV)))
    (↠-step (ξ-⟨⟩ (ν-step vV noV)) ↠-refl)

left-catchup-indexed-one-keep-valueᵀ :
  ∀ {Φ Δᴸ Δᴿ M N V′ A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  M —→[ keep ] N →
  Value N →
  No• N →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ V′ ⦂ A ⊑ B ∶ p →
  LeftCatchupIndexedResult {N = M} {V′ = V′} {ρ = ρ} p
left-catchup-indexed-one-keep-valueᵀ M→N vN noN N⊑V′ =
  left-indexed-catchup
    (weak-indexed-result result N⊑V′)
    (left-catchup-invariant
      (left-silent-invariant refl refl) (inj₁ (vN , noN)))
    (weak-step-transport (λ noL noL′ L⊑L′ → L⊑L′))
    (weak-step-type-coherence
      (λ pC pD → refl) (λ q → refl))
  where
  result = record
    { sourceChanges = keep ∷ []
    ; targetTailChanges = []
    ; sourceResult = _
    ; targetResult = _
    ; resultCtx = _
    ; resultLeftCtx = _
    ; resultRightCtx = _
    ; sourceCtxResult = refl
    ; targetCtxResult = refl
    ; resultStore = _
    ; resultSourceType = _
    ; resultTargetType = _
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = λ q → q
    ; transportAllBody = λ q → q
    ; transportRightBody = λ q → q
    ; resultType = _
    ; sourceCatchup = ↠-step M→N ↠-refl
    ; targetTail = ↠-refl
    ; sourceStoreResult = refl
    ; targetStoreResult = refl
    ; relatedResults = N⊑V′
    }

left-catchup-indexed-double-cast-blameᵀ :
  ∀ {Φ Δᴸ Δᴿ V′ d u} {A B : T.Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ V′ ⦂ B →
  LeftCatchupIndexedResult
    {N = (blame ⟨ d ⟩) ⟨ u ⟩}
    {V′ = V′} {A = A} {B = B} {ρ = ρ} p
left-catchup-indexed-double-cast-blameᵀ V′⊢ =
  left-indexed-catchup
    (weak-indexed-result result blame-relation)
    (left-catchup-invariant
      (left-silent-invariant refl refl) (inj₂ refl))
    (weak-step-transport (λ noL noL′ L⊑L′ → L⊑L′))
    (weak-step-type-coherence
      (λ pC pD → refl) (λ q → refl))
  where
  blame-relation = blame⊑ᵀ V′⊢

  result = record
    { sourceChanges = keep ∷ keep ∷ []
    ; targetTailChanges = []
    ; sourceResult = blame
    ; targetResult = _
    ; resultCtx = _
    ; resultLeftCtx = _
    ; resultRightCtx = _
    ; sourceCtxResult = refl
    ; targetCtxResult = refl
    ; resultStore = _
    ; resultSourceType = _
    ; resultTargetType = _
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = λ q → q
    ; transportAllBody = λ q → q
    ; transportRightBody = λ q → q
    ; resultType = _
    ; sourceCatchup =
        ↠-step (ξ-⟨⟩ (pure-step blame-⟨⟩))
          (↠-step (pure-step blame-⟨⟩) ↠-refl)
    ; targetTail = ↠-refl
    ; sourceStoreResult = refl
    ; targetStoreResult = refl
    ; relatedResults = blame-relation
    }

left-catchup-indexed-two-keep-to-blameᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′} {A B : T.Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  M —↠[ keep ∷ keep ∷ [] ] blame →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ V′ ⦂ B →
  LeftCatchupIndexedResult {N = M} {V′ = V′} {A = A} {B = B}
    {ρ = ρ} p
left-catchup-indexed-two-keep-to-blameᵀ M↠blame V′⊢ =
  left-indexed-catchup
    (weak-indexed-result result blame-relation)
    (left-catchup-invariant
      (left-silent-invariant refl refl) (inj₂ refl))
    (weak-step-transport (λ noL noL′ L⊑L′ → L⊑L′))
    (weak-step-type-coherence
      (λ pC pD → refl) (λ q → refl))
  where
  blame-relation = blame⊑ᵀ V′⊢

  result = record
    { sourceChanges = keep ∷ keep ∷ []
    ; targetTailChanges = []
    ; sourceResult = blame
    ; targetResult = _
    ; resultCtx = _
    ; resultLeftCtx = _
    ; resultRightCtx = _
    ; sourceCtxResult = refl
    ; targetCtxResult = refl
    ; resultStore = _
    ; resultSourceType = _
    ; resultTargetType = _
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = λ q → q
    ; transportAllBody = λ q → q
    ; transportRightBody = λ q → q
    ; resultType = _
    ; sourceCatchup = M↠blame
    ; targetTail = ↠-refl
    ; sourceStoreResult = refl
    ; targetStoreResult = refl
    ; relatedResults = blame-relation
    }

left-catchup-indexed-final-quotient-inertᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ A A′ pA d d′ u u′}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value V →
  No• V →
  Inert d →
  Inert u →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ (V ⟨ d ⟩) ⟨ u ⟩
      ⊑ (V′ ⟨ d′ ⟩) ⟨ u′ ⟩
    ⦂ A ⊑ A′ ∶ pA) →
  LeftCatchupIndexedResult
    {N = (V ⟨ d ⟩) ⟨ u ⟩}
    {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ} pA
left-catchup-indexed-final-quotient-inertᵀ
    vV noV inert-d inert-u relation =
  left-catchup-indexed-relatedᵀ
    (inj₁
      (vV ⟨ inert-d ⟩ ⟨ inert-u ⟩ ,
       no•-⟨⟩ (no•-⟨⟩ noV)))
    relation

source-quotient-down-tag-impossible :
  ∀ {Φ Δᴸ Δᴿ W W′ G d′ D D′ qD}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ (W ⟨ G ! ⟩) ⊑ (W′ ⟨ d′ ⟩)
    ⦂ D ⊑ᵖ D′ ∶ qD) →
  ⊥
source-quotient-down-tag-impossible
    (down⊑downᵀ (_ , NW.cross ()) d′⊒ W⊑W′ qD)
source-quotient-down-tag-impossible
    (gen-down⊑gen-downᵀ (_ , NW.cross ()) d′⊒ W⊑W′ qD)

source-quotient-down-unseal-impossible :
  ∀ {Φ Δᴸ Δᴿ W W′ α X d′ D D′ qD}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ (W ⟨ unseal α X ⟩) ⊑ (W′ ⟨ d′ ⟩)
    ⦂ D ⊑ᵖ D′ ∶ qD) →
  ⊥
source-quotient-down-unseal-impossible
    (down⊑downᵀ (_ , NW.cross ()) d′⊒ W⊑W′ qD)
source-quotient-down-unseal-impossible
    (gen-down⊑gen-downᵀ (_ , NW.cross ()) d′⊒ W⊑W′ qD)

source-quotient-down-seal-impossible :
  ∀ {Φ Δᴸ Δᴿ V V′ X α d′ D D′ qD}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ (V ⟨ seal X α ⟩) ⊑ (V′ ⟨ d′ ⟩)
    ⦂ D ⊑ᵖ D′ ∶ qD) →
  ⊥
source-quotient-down-seal-impossible
    (down⊑downᵀ
      (C.cast-seal hX α∈Σ ok , NW.sealⁿ X α)
      d′⊒ V⊑V′ qD) =
  false≢true (trans (sym (id-only-no-seal α)) ok)
source-quotient-down-seal-impossible
    (gen-down⊑gen-downᵀ
      (C.cast-seal hX α∈Σ ok , NW.sealⁿ X α)
      d′⊒ V⊑V′ qD) =
  false≢true (trans (sym (gen-tag-or-id-no-seal α)) ok)

source-quotient-down-seal-tail-impossible :
  ∀ {Φ Δᴸ Δᴿ V V′ n X α d′ D D′ qD}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ (V ⟨ (n ︔ seal X α) ⟩) ⊑ (V′ ⟨ d′ ⟩)
    ⦂ D ⊑ᵖ D′ ∶ qD) →
  ⊥
source-quotient-down-seal-tail-impossible
    (down⊑downᵀ
      (C.cast-seq n⊢ (C.cast-seal hX α∈Σ ok) ,
        nⁿ NW.︔seal α)
      d′⋒ V⊑V′ qD) =
  false≢true (trans (sym (id-only-no-seal α)) ok)
source-quotient-down-seal-tail-impossible
    (gen-down⊑gen-downᵀ
      (C.cast-seq n⊢ (C.cast-seal hX α∈Σ ok) ,
        nⁿ NW.︔seal α)
      d′⋒ V⊑V′ qD) =
  false≢true (trans (sym (gen-tag-or-id-no-seal α)) ok)

source-quotient-down-untag-index-ground :
  ∀ {Φ Δᴸ Δᴿ W V′ G d′ D D′ qD}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ ((W ⟨ G ! ⟩) ⟨ G ？ ⟩) ⊑ (V′ ⟨ d′ ⟩)
    ⦂ D ⊑ᵖ D′ ∶ qD) →
  Ground D
source-quotient-down-untag-index-ground
    (down⊑downᵀ
      (C.cast-untag hG gG ok , NW.untag gG′)
      d′⊒ V⊑V′ qD) =
  gG
source-quotient-down-untag-index-ground
    (gen-down⊑gen-downᵀ
      (C.cast-untag hG gG ok , NW.untag gG′)
      d′⊒ V⊑V′ qD) =
  gG

source-inert-quotient-down-var-impossible :
  ∀ {Φ Δᴸ Δᴿ V V′ d d′ α D′ qD}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value (V ⟨ d ⟩) →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ (V ⟨ d ⟩) ⊑ (V′ ⟨ d′ ⟩)
    ⦂ T.＇ α ⊑ᵖ D′ ∶ qD) →
  ⊥
source-inert-quotient-down-var-impossible vW
    (down⊑downᵀ d⊒ d′⊒ V⊑V′ qD) =
  inert-narrowing-target-var-no-seal
    id-only-no-seal d⊒ (cast-value-inert vW)
source-inert-quotient-down-var-impossible vW
    (gen-down⊑gen-downᵀ d⊒ d′⊒ V⊑V′ qD) =
  inert-narrowing-target-var-no-seal
    gen-tag-or-id-no-seal d⊒ (cast-value-inert vW)

source-inert-quotient-down-base-impossible :
  ∀ {Φ Δᴸ Δᴿ V V′ d d′ ι D′ qD}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value (V ⟨ d ⟩) →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ (V ⟨ d ⟩) ⊑ (V′ ⟨ d′ ⟩)
    ⦂ T.‵ ι ⊑ᵖ D′ ∶ qD) →
  ⊥
source-inert-quotient-down-base-impossible vW
    (down⊑downᵀ d⊒ d′⊒ V⊑V′ qD) =
  inert-narrowing-target-base d⊒ (cast-value-inert vW)
source-inert-quotient-down-base-impossible vW
    (gen-down⊑gen-downᵀ d⊒ d′⊒ V⊑V′ qD) =
  inert-narrowing-target-base d⊒ (cast-value-inert vW)

source-inert-quotient-down-star-impossible :
  ∀ {Φ Δᴸ Δᴿ V V′ d d′ D′ qD}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value (V ⟨ d ⟩) →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ (V ⟨ d ⟩) ⊑ (V′ ⟨ d′ ⟩)
    ⦂ ★ ⊑ᵖ D′ ∶ qD) →
  ⊥
source-inert-quotient-down-star-impossible vW
    (down⊑downᵀ d⊒ d′⊒ V⊑V′ qD) =
  inert-narrowing-target-star d⊒ (cast-value-inert vW)
source-inert-quotient-down-star-impossible vW
    (gen-down⊑gen-downᵀ d⊒ d′⊒ V⊑V′ qD) =
  inert-narrowing-target-star d⊒ (cast-value-inert vW)

source-inert-quotient-down-before-id-widening-impossible :
  ∀ {Φ Δᴸ Δᴿ μ V V′ d d′ X A D D′ qD}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value (V ⟨ d ⟩) →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ (V ⟨ d ⟩) ⊑ (V′ ⟨ d′ ⟩)
    ⦂ D ⊑ᵖ D′ ∶ qD) →
  μ ∣ Δᴸ ∣ NuTermImprecision.leftStoreⁱ ρ
    ⊢ C.id X ∶ D ⊑ A →
  ⊥
source-inert-quotient-down-before-id-widening-impossible
    vW down (C.cast-id hA ok , NW.cross (NW.id-＇ α)) =
  source-inert-quotient-down-var-impossible vW down
source-inert-quotient-down-before-id-widening-impossible
    vW down (C.cast-id hA ok , NW.cross (NW.id-‵ ι)) =
  source-inert-quotient-down-base-impossible vW down
source-inert-quotient-down-before-id-widening-impossible
    vW down (C.cast-id hA ok , NW.id★) =
  source-inert-quotient-down-star-impossible vW down

target-inert-after-var-imprecision-no-seal :
  ∀ {Φ Δᴸ Δᴿ μ Σ d C α D′} →
  (∀ β → C.sealModeAllowed (μ β) ≡ false) →
  Φ ∣ Δᴸ ⊢ T.＇ α ⊑ D′ ⊣ Δᴿ →
  μ ∣ Δᴿ ∣ Σ ⊢ d ∶ C ⊒ D′ →
  Inert d →
  ⊥
target-inert-after-var-imprecision-no-seal no-seal
    (idˣ X⊑Y X<Δᴸ Y<Δᴿ) d⊒ inert-d =
  inert-narrowing-target-var-no-seal no-seal d⊒ inert-d
target-inert-after-var-imprecision-no-seal no-seal
    (tagˣ X⊑★ X<Δᴸ) d⊒ inert-d =
  inert-narrowing-target-star d⊒ inert-d

target-inert-after-base-imprecision :
  ∀ {Φ Δᴸ Δᴿ μ Σ d C ι D′} →
  Φ ∣ Δᴸ ⊢ T.‵ ι ⊑ D′ ⊣ Δᴿ →
  μ ∣ Δᴿ ∣ Σ ⊢ d ∶ C ⊒ D′ →
  Inert d →
  ⊥
target-inert-after-base-imprecision idι d⊒ inert-d =
  inert-narrowing-target-base d⊒ inert-d
target-inert-after-base-imprecision (tag ι) d⊒ inert-d =
  inert-narrowing-target-star d⊒ inert-d

target-inert-quotient-down-after-source-id-impossible :
  ∀ {Φ Δᴸ Δᴿ V V′ X d′ D D′ qD}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Inert d′ →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ (V ⟨ C.id X ⟩) ⊑ (V′ ⟨ d′ ⟩)
    ⦂ D ⊑ᵖ D′ ∶ qD) →
  ⊥
target-inert-quotient-down-after-source-id-impossible inert-d′
    (down⊑downᵀ
      (C.cast-id hX ok , NW.cross (NW.id-＇ α))
      d′⊒ V⊑V′ qD) =
  target-inert-after-var-imprecision-no-seal id-only-no-seal
    (⊑ᵖ-ground-left (T.＇ α) qD) d′⊒ inert-d′
target-inert-quotient-down-after-source-id-impossible inert-d′
    (down⊑downᵀ
      (C.cast-id hX ok , NW.cross (NW.id-‵ ι))
      d′⊒ V⊑V′ qD) =
  target-inert-after-base-imprecision
    (⊑ᵖ-ground-left (T.‵ ι) qD) d′⊒ inert-d′
target-inert-quotient-down-after-source-id-impossible
    {Δᴿ = Δᴿ} {ρ = ρ} inert-d′
    (down⊑downᵀ
      (C.cast-id hX ok , NW.id★) d′⊒ V⊑V′ qD) =
  inert-narrowing-target-star star-d′⊒ inert-d′
  where
  star-d′⊒ =
    subst
      (λ Y → C.id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ _ ∶ _ ⊒ Y)
      (⊑ᵖ-star-left-eq qD) d′⊒
target-inert-quotient-down-after-source-id-impossible inert-d′
    (gen-down⊑gen-downᵀ
      (C.cast-id hX ok , NW.cross (NW.id-＇ α))
      d′⊒ V⊑V′ qD) =
  target-inert-after-var-imprecision-no-seal gen-tag-or-id-no-seal
    (⊑ᵖ-ground-left (T.＇ α) qD) d′⊒ inert-d′
target-inert-quotient-down-after-source-id-impossible inert-d′
    (gen-down⊑gen-downᵀ
      (C.cast-id hX ok , NW.cross (NW.id-‵ ι))
      d′⊒ V⊑V′ qD) =
  target-inert-after-base-imprecision
    (⊑ᵖ-ground-left (T.‵ ι) qD) d′⊒ inert-d′
target-inert-quotient-down-after-source-id-impossible
    {Δᴿ = Δᴿ} {ρ = ρ} inert-d′
    (gen-down⊑gen-downᵀ
      (C.cast-id hX ok , NW.id★) d′⊒ V⊑V′ qD) =
  inert-narrowing-target-star star-d′⊒ inert-d′
  where
  star-d′⊒ =
    subst
      (λ Y → C.genᵈ C.tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ _ ∶ _ ⊒ Y)
      (⊑ᵖ-star-left-eq qD) d′⊒

target-inert-after-source-untag-impossible :
  ∀ {Φ Δᴸ Δᴿ W V′ G d′ D D′ qD}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Inert d′ →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ ((W ⟨ G ! ⟩) ⟨ G ？ ⟩) ⊑ (V′ ⟨ d′ ⟩)
    ⦂ D ⊑ᵖ D′ ∶ qD) →
  ⊥
target-inert-after-source-untag-impossible
    {Δᴿ = Δᴿ} {ρ = ρ} inert-d′
    (down⊑downᵀ
      (C.cast-untag hG gG ok , NW.untag gG′)
      d′⊒ W⊑V′ qD) =
  ground-star-inert-narrowing-no-seal
    id-only-no-seal gG ordinary-qD star-d′⊒ inert-d′
  where
  ordinary-qD = ⊑ᵖ-ground-left gG qD
  star-d′⊒ =
    subst
      (λ C′ → C.id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ _ ∶ C′ ⊒ _)
      (star-term-imprecision-target W⊑V′) d′⊒
target-inert-after-source-untag-impossible
    {Δᴿ = Δᴿ} {ρ = ρ} inert-d′
    (gen-down⊑gen-downᵀ
      (C.cast-untag hG gG ok , NW.untag gG′)
      d′⊒ W⊑V′ qD) =
  ground-star-inert-narrowing-no-seal
    gen-tag-or-id-no-seal gG ordinary-qD star-d′⊒ inert-d′
  where
  ordinary-qD = ⊑ᵖ-ground-left gG qD
  star-d′⊒ =
    subst
      (λ C′ → C.genᵈ C.tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ _ ∶ C′ ⊒ _)
      (star-term-imprecision-target W⊑V′) d′⊒

target-inert-after-source-untag-sequence-impossible :
  ∀ {Φ Δᴸ Δᴿ V V′ G g d′ D D′ qD}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Inert d′ →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ (V ⟨ (G ？) ︔ g ⟩) ⊑ (V′ ⟨ d′ ⟩)
    ⦂ D ⊑ᵖ D′ ∶ qD) →
  ⊥
target-inert-after-source-untag-sequence-impossible
    inert-d′
    down@(down⊑downᵀ
      (C.cast-seq
        (C.cast-untag hG gG⊢ ok)
        (C.cast-seal hX α∈Σ seal-ok) ,
        NW.strict-untag gG NW.︔seal α)
      d′⊒ V⊑V′ qD) =
  source-quotient-down-seal-tail-impossible down
target-inert-after-source-untag-sequence-impossible
    {Δᴿ = Δᴿ} {ρ = ρ} inert-d′
    (down⊑downᵀ
      (C.cast-seq (C.cast-untag hG gG⊢ ok)
                  (C.cast-gen hA occ g⊢) ,
       NW.fun-untag-gen safe)
      d′⊒ V⊑V′ qD) =
  inert-narrowing-source-star-no-seal
    id-only-no-seal star-d′⊒ inert-d′
  where
  star-d′⊒ =
    subst
      (λ X → C.id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ _ ∶ X ⊒ _)
      (star-term-imprecision-target V⊑V′) d′⊒
target-inert-after-source-untag-sequence-impossible
    {Δᴿ = Δᴿ} {ρ = ρ} inert-d′
    (down⊑downᵀ
      (C.cast-seq (C.cast-untag hG gG⊢ ok) g⊢ ,
        gG NW.？︔ gⁿ)
      d′⊒ V⊑V′ qD)
    with strict-cross-narrowing-ground-target-arrow
      gG gⁿ (g⊢ , NW.cross
        (strictCrossNarrowing⇒crossNarrowing gⁿ))
target-inert-after-source-untag-sequence-impossible
    {Δᴿ = Δᴿ} {ρ = ρ} inert-d′
    (down⊑downᵀ
      (C.cast-seq (C.cast-untag hG gG⊢ ok) g⊢ ,
        gG NW.？︔ gⁿ)
      d′⊒ V⊑V′ qD)
    | A , B , refl with ⊑ᵖ-arrow-left-shape qD
target-inert-after-source-untag-sequence-impossible
    {Δᴿ = Δᴿ} {ρ = ρ} inert-d′
    (down⊑downᵀ
      (C.cast-seq (C.cast-untag hG gG⊢ ok) g⊢ ,
        gG NW.？︔ gⁿ)
      d′⊒ V⊑V′ qD)
    | A , B , refl | inj₁ (A′ , B′ , refl) =
  inert-narrowing-star-to-arrow star-d′⊒ inert-d′
  where
  star-d′⊒ =
    subst
      (λ X → C.id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ _ ∶ X ⊒ _)
      (star-term-imprecision-target V⊑V′) d′⊒
target-inert-after-source-untag-sequence-impossible
    {Δᴿ = Δᴿ} {ρ = ρ} inert-d′
    (down⊑downᵀ
      (C.cast-seq (C.cast-untag hG gG⊢ ok) g⊢ ,
        gG NW.？︔ gⁿ)
      d′⊒ V⊑V′ qD)
    | A , B , refl | inj₂ refl =
  inert-narrowing-target-star star-d′⊒ inert-d′
  where
  star-d′⊒ =
    subst
      (λ X → C.id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ _ ∶ X ⊒ ★)
      (star-term-imprecision-target V⊑V′) d′⊒
target-inert-after-source-untag-sequence-impossible
    inert-d′
    down@(gen-down⊑gen-downᵀ
      (C.cast-seq
        (C.cast-untag hG gG⊢ ok)
        (C.cast-seal hX α∈Σ seal-ok) ,
        NW.strict-untag gG NW.︔seal α)
      d′⊒ V⊑V′ qD) =
  source-quotient-down-seal-tail-impossible down
target-inert-after-source-untag-sequence-impossible
    {Δᴿ = Δᴿ} {ρ = ρ} inert-d′
    (gen-down⊑gen-downᵀ
      (C.cast-seq (C.cast-untag hG gG⊢ ok)
                  (C.cast-gen hA occ g⊢) ,
       NW.fun-untag-gen safe)
      d′⊒ V⊑V′ qD) =
  inert-narrowing-source-star-no-seal
    gen-tag-or-id-no-seal star-d′⊒ inert-d′
  where
  star-d′⊒ =
    subst
      (λ X → C.genᵈ C.tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ _ ∶ X ⊒ _)
      (star-term-imprecision-target V⊑V′) d′⊒
target-inert-after-source-untag-sequence-impossible
    {Δᴿ = Δᴿ} {ρ = ρ} inert-d′
    (gen-down⊑gen-downᵀ
      (C.cast-seq (C.cast-untag hG gG⊢ ok) g⊢ ,
        gG NW.？︔ gⁿ)
      d′⊒ V⊑V′ qD)
    with strict-cross-narrowing-ground-target-arrow
      gG gⁿ (g⊢ , NW.cross
        (strictCrossNarrowing⇒crossNarrowing gⁿ))
target-inert-after-source-untag-sequence-impossible
    {Δᴿ = Δᴿ} {ρ = ρ} inert-d′
    (gen-down⊑gen-downᵀ
      (C.cast-seq (C.cast-untag hG gG⊢ ok) g⊢ ,
        gG NW.？︔ gⁿ)
      d′⊒ V⊑V′ qD)
    | A , B , refl with ⊑ᵖ-arrow-left-shape qD
target-inert-after-source-untag-sequence-impossible
    {Δᴿ = Δᴿ} {ρ = ρ} inert-d′
    (gen-down⊑gen-downᵀ
      (C.cast-seq (C.cast-untag hG gG⊢ ok) g⊢ ,
        gG NW.？︔ gⁿ)
      d′⊒ V⊑V′ qD)
    | A , B , refl | inj₁ (A′ , B′ , refl) =
  inert-narrowing-star-to-arrow star-d′⊒ inert-d′
  where
  star-d′⊒ =
    subst
      (λ X → C.genᵈ C.tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ _ ∶ X ⊒ _)
      (star-term-imprecision-target V⊑V′) d′⊒
target-inert-after-source-untag-sequence-impossible
    {Δᴿ = Δᴿ} {ρ = ρ} inert-d′
    (gen-down⊑gen-downᵀ
      (C.cast-seq (C.cast-untag hG gG⊢ ok) g⊢ ,
        gG NW.？︔ gⁿ)
      d′⊒ V⊑V′ qD)
    | A , B , refl | inj₂ refl =
  inert-narrowing-target-star star-d′⊒ inert-d′
  where
  star-d′⊒ =
    subst
      (λ X → C.genᵈ C.tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ _ ∶ X ⊒ ★)
      (star-term-imprecision-target V⊑V′) d′⊒

inner-sequence-residualᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ G g d′ u u′}
    {D D′ A A′ : T.Ty}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ (V ⟨ ((G ？) ︔ g) ⟩) ⊑ (V′ ⟨ d′ ⟩)
    ⦂ D ⊑ᵖ D′ ∶ qD) →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ ((V ⟨ G ？ ⟩) ⟨ g ⟩) ⟨ u ⟩
      ⊑ (V′ ⟨ d′ ⟩) ⟨ u′ ⟩
    ⦂ A ⊑ A′ ∶ pA
inner-sequence-residualᵀ
    down@(down⊑downᵀ
      (C.cast-seq
        (C.cast-untag hG gG⊢ ok)
        (C.cast-seal hX α∈Σ seal-ok) ,
        NW.strict-untag gG NW.︔seal α)
      d′⊒ V⊑V′ qD)
    widening pA =
  ⊥-elim (source-quotient-down-seal-tail-impossible down)
inner-sequence-residualᵀ
    (down⊑downᵀ
      (C.cast-seq (C.cast-untag hG gG⊢ ok)
                  (C.cast-gen hA occ g⊢) ,
       NW.fun-untag-gen safe)
      d′⊒ V⊑V′ qD)
    widening pA =
  up⊑upᵀ split-down widening pA
  where
  G⊑C′ =
    subst (λ X → _ ∣ _ ⊢ _ ⊑ X ⊣ _)
      (sym (star-term-imprecision-target V⊑V′))
      (tag id★ ⇛ id★)
  untag⊒ =
    NW.narrow-mode-relax { μ = C.id-onlyᵈ }
      C.id-only≤tag-or-idᵈ
      (C.cast-untag hG gG⊢ ok , NW.untag gG⊢)
  untag-relation =
    cast⊒⊑ᵀ cast-tag-or-id seal★-tag-or-id untag⊒
      V⊑V′ G⊑C′
  gen⊒ = C.cast-gen hA occ g⊢ , NW.gen safe
  split-down = down⊑downᵀ gen⊒ d′⊒ untag-relation qD
inner-sequence-residualᵀ
    (down⊑downᵀ
      (C.cast-seq
        (C.cast-untag hG gG⊢ ok) g⊢ ,
        gG NW.？︔ gⁿ)
      d′⊒ V⊑V′ qD)
    widening pA =
  up⊑upᵀ split-down widening pA
  where
  g⊒ =
    g⊢ , NW.cross (strictCrossNarrowing⇒crossNarrowing gⁿ)
  G⊑★ = strict-cross-narrowing-ground-star gG gⁿ g⊒
  G⊑C′ =
    subst (λ X → _ ∣ _ ⊢ _ ⊑ X ⊣ _)
      (sym (star-term-imprecision-target V⊑V′)) G⊑★
  untag⊒ =
    NW.narrow-mode-relax C.id-only≤tag-or-idᵈ
      (C.cast-untag hG gG⊢ ok , NW.untag gG)
  untag-relation =
    cast⊒⊑ᵀ cast-tag-or-id seal★-tag-or-id untag⊒
      V⊑V′ G⊑C′
  split-down = down⊑downᵀ g⊒ d′⊒ untag-relation qD
inner-sequence-residualᵀ
    down@(gen-down⊑gen-downᵀ
      (C.cast-seq
        (C.cast-untag hG gG⊢ ok)
        (C.cast-seal hX α∈Σ seal-ok) ,
        NW.strict-untag gG NW.︔seal α)
      d′⊒ V⊑V′ qD)
    widening pA =
  ⊥-elim (source-quotient-down-seal-tail-impossible down)
inner-sequence-residualᵀ
    (gen-down⊑gen-downᵀ
      (C.cast-seq (C.cast-untag hG gG⊢ ok)
                  (C.cast-gen hA occ g⊢) ,
       NW.fun-untag-gen safe)
      d′⊒ V⊑V′ qD)
    widening pA =
  up⊑upᵀ split-down widening pA
  where
  G⊑C′ =
    subst (λ X → _ ∣ _ ⊢ _ ⊑ X ⊣ _)
      (sym (star-term-imprecision-target V⊑V′))
      (tag id★ ⇛ id★)
  untag⊒ = C.cast-untag hG gG⊢ ok , NW.untag gG⊢
  untag-relation =
    cast⊒⊑ᵀ (cast-gen cast-tag-or-id)
      seal★-gen-tag-or-id untag⊒ V⊑V′ G⊑C′
  gen⊒ = C.cast-gen hA occ g⊢ , NW.gen safe
  split-down =
    gen-down⊑gen-downᵀ gen⊒ d′⊒ untag-relation qD
inner-sequence-residualᵀ
    (gen-down⊑gen-downᵀ
      (C.cast-seq
        (C.cast-untag hG gG⊢ ok) g⊢ ,
        gG NW.？︔ gⁿ)
      d′⊒ V⊑V′ qD)
    widening pA =
  up⊑upᵀ split-down widening pA
  where
  g⊒ =
    g⊢ , NW.cross (strictCrossNarrowing⇒crossNarrowing gⁿ)
  G⊑★ = strict-cross-narrowing-ground-star gG gⁿ g⊒
  G⊑C′ =
    subst (λ X → _ ∣ _ ⊢ _ ⊑ X ⊣ _)
      (sym (star-term-imprecision-target V⊑V′)) G⊑★
  untag⊒ = C.cast-untag hG gG⊢ ok , NW.untag gG
  untag-relation =
    cast⊒⊑ᵀ (cast-gen cast-tag-or-id)
      seal★-gen-tag-or-id untag⊒ V⊑V′ G⊑C′
  split-down =
    gen-down⊑gen-downᵀ g⊒ d′⊒ untag-relation qD

left-catchup-indexed-final-quotient-outer-pureᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ L d d′ u u′}
    {D D′ A A′ : T.Ty}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  ((V ⟨ d ⟩) ⟨ u ⟩) —→ L →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  Inert d′ →
  Inert u′ →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ (V ⟨ d ⟩) ⊑ (V′ ⟨ d′ ⟩)
    ⦂ D ⊑ᵖ D′ ∶ qD) →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  LeftCatchupIndexedResult
      {N = (V ⟨ d ⟩) ⟨ u ⟩}
      {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
      {ρ = ρ} pA
  ⊎ ∃[ B ] ∃[ s ]
      (u ≡ inst B s) ×
      (((V ⟨ d ⟩) ⟨ u ⟩)
        —↠[ keep ∷ bind ★ ∷ [] ]
          ((NT.⇑ᵗᵐ (V ⟨ d ⟩)) •) ⟨ s ⟩)
  ⊎ ∃[ B ] ∃[ s ]
      (u ≡ (inst B s ︔ ((★ T.⇒ ★) !))) ×
      (((V ⟨ d ⟩) ⟨ u ⟩)
        —↠[ keep ∷ keep ∷ bind ★ ∷ [] ]
          ((((NT.⇑ᵗᵐ (V ⟨ d ⟩)) •) ⟨ s ⟩)
            ⟨ ⇑ᶜ ((★ T.⇒ ★) !) ⟩))
left-catchup-indexed-final-quotient-outer-pureᵀ
    (β-id vW) vV noV vV′ noV′ inert-d′ inert-u′
    down (quotient-id-widening u⊑ u′⊑) pA =
  inj₁ (⊥-elim
    (source-inert-quotient-down-before-id-widening-impossible
      vW down u⊑))
left-catchup-indexed-final-quotient-outer-pureᵀ
    (β-id vW) vV noV vV′ noV′ inert-d′ inert-u′
    down
    (quotient-cast-widening mode seal★ u⊑ mode′ seal★′ u′⊑)
    pA =
  inj₁ (⊥-elim
    (source-inert-quotient-down-before-id-widening-impossible
      vW down u⊑))
left-catchup-indexed-final-quotient-outer-pureᵀ
    (β-seq vW) vV noV vV′ noV′ inert-d′ inert-u′
    down
    (quotient-id-widening
      (C.cast-seq s⊢ (C.cast-tag hG gG⊢ ok) ,
        sʷ NW.︔ gG !) u′⊑)
    pA =
  inj₁ (left-catchup-indexed-one-keep-valueᵀ
    (pure-step (β-seq vW))
    (vW ⟨ strict-cross-widening-inert sʷ ⟩ ⟨ _ ! ⟩)
    (no•-⟨⟩ (no•-⟨⟩ (no•-⟨⟩ noV))) final-relation)
  where
  s⊑ =
    s⊢ , NW.cross (strictCrossWidening⇒crossWidening sʷ)
  G⊑★ = strict-cross-widening-ground-star gG sʷ s⊑
  G⊑A′ =
    subst (λ X → _ ∣ _ ⊢ _ ⊑ X ⊣ _)
      (sym (star-imprecision-target pA)) G⊑★
  split-relation =
    up⊑upᵀ down (quotient-id-widening s⊑ u′⊑) G⊑A′
  tag⊑ =
    NW.widen-mode-relax C.id-only≤tag-or-idᵈ
      (C.cast-tag hG gG⊢ ok , NW.tag gG)
  final-relation =
    cast⊑⊑ᵀ cast-tag-or-id seal★-tag-or-id tag⊑
      split-relation pA
left-catchup-indexed-final-quotient-outer-pureᵀ
    (β-seq vW) vV noV vV′ noV′ inert-d′ inert-u′
    down
    (quotient-id-widening
      (C.cast-seq (C.cast-unseal hA α∈Σ ok) t⊢ ,
        NW.unseal︔_ α tʷ)
      u′⊑)
    pA =
  inj₁ (⊥-elim
    (source-inert-quotient-down-var-impossible vW down))
left-catchup-indexed-final-quotient-outer-pureᵀ
    (β-seq vW) vV noV vV′ noV′ inert-d′ inert-u′
    down
    (quotient-cast-widening
      mode seal★
      (C.cast-seq s⊢ (C.cast-tag hG gG⊢ ok) ,
        sʷ NW.︔ gG !)
      mode′ seal★′ u′⊑)
    pA =
  inj₁ (left-catchup-indexed-one-keep-valueᵀ
    (pure-step (β-seq vW))
    (vW ⟨ strict-cross-widening-inert sʷ ⟩ ⟨ _ ! ⟩)
    (no•-⟨⟩ (no•-⟨⟩ (no•-⟨⟩ noV))) final-relation)
  where
  s⊑ =
    s⊢ , NW.cross (strictCrossWidening⇒crossWidening sʷ)
  G⊑★ = strict-cross-widening-ground-star gG sʷ s⊑
  G⊑A′ =
    subst (λ X → _ ∣ _ ⊢ _ ⊑ X ⊣ _)
      (sym (star-imprecision-target pA)) G⊑★
  split-relation =
    up⊑upᵀ down
      (quotient-cast-widening
        mode seal★ s⊑ mode′ seal★′ u′⊑)
      G⊑A′
  tag⊑ = C.cast-tag hG gG⊢ ok , NW.tag gG
  final-relation =
    cast⊑⊑ᵀ mode seal★ tag⊑ split-relation pA
left-catchup-indexed-final-quotient-outer-pureᵀ
    (β-seq vW) vV noV vV′ noV′ inert-d′ inert-u′
    down
    (quotient-cast-widening
      mode seal★
      (C.cast-seq (C.cast-unseal hA α∈Σ ok) t⊢ ,
        NW.unseal︔_ α tʷ)
      mode′ seal★′ u′⊑)
    pA =
  inj₁ (⊥-elim
    (source-inert-quotient-down-var-impossible vW down))
left-catchup-indexed-final-quotient-outer-pureᵀ
    (β-seq vW) vV noV vV′ noV′ inert-d′ inert-u′
    down
    (quotient-id-widening
      (C.cast-seq (C.cast-inst hB occ s⊢)
                  (C.cast-tag hG gG⊢ ok) ,
       NW.inst-fun-tag safe)
      u′⊑)
    pA =
  inj₂
    (inj₂ (_ , _ , refl ,
      outer-inst-fun-tag-allocation-trace noV vW))
left-catchup-indexed-final-quotient-outer-pureᵀ
    (β-seq vW) vV noV vV′ noV′ inert-d′ inert-u′
    down
    (quotient-cast-widening mode seal★
      (C.cast-seq (C.cast-inst hB occ s⊢)
                  (C.cast-tag hG gG⊢ ok) ,
       NW.inst-fun-tag safe)
      mode′ seal★′ u′⊑)
    pA =
  inj₂
    (inj₂ (_ , _ , refl ,
      outer-inst-fun-tag-allocation-trace noV vW))
left-catchup-indexed-final-quotient-outer-pureᵀ
    (β-inst vW) vV noV vV′ noV′ inert-d′ inert-u′
    down
    (quotient-id-widening
      (C.cast-inst hB occ s⊢ , NW.inst sʷ) u′⊑)
    pA =
  inj₂ (inj₁ (_ , _ , refl , outer-inst-allocation-trace noV vW))
left-catchup-indexed-final-quotient-outer-pureᵀ
    (β-inst vW) vV noV vV′ noV′ inert-d′ inert-u′
    down
    (quotient-cast-widening mode seal★
      (C.cast-inst hB occ s⊢ , NW.inst sʷ)
      mode′ seal★′ u′⊑)
    pA =
  inj₂ (inj₁ (_ , _ , refl , outer-inst-allocation-trace noV vW))
left-catchup-indexed-final-quotient-outer-pureᵀ
    (tag-untag-ok vW) vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA =
  inj₁ (⊥-elim (source-quotient-down-tag-impossible down))
left-catchup-indexed-final-quotient-outer-pureᵀ
    (tag-untag-bad vW G≢H) vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA =
  inj₁ (⊥-elim (source-quotient-down-tag-impossible down))
left-catchup-indexed-final-quotient-outer-pureᵀ {qD = qD}
    (seal-unseal vW) vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA =
  inj₁ (⊥-elim (source-quotient-down-seal-impossible down))

left-catchup-indexed-final-quotient-inner-stepᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ L d d′ u u′}
    {D D′ A A′ : T.Ty}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (V ⟨ d ⟩) —→[ keep ] L →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  Inert d′ →
  Inert u′ →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ (V ⟨ d ⟩) ⊑ (V′ ⟨ d′ ⟩)
    ⦂ D ⊑ᵖ D′ ∶ qD) →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  LeftCatchupIndexedResult
    {N = (V ⟨ d ⟩) ⟨ u ⟩}
    {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ} pA
left-catchup-indexed-final-quotient-inner-stepᵀ
    (pure-step (β-id vW)) vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA =
  ⊥-elim
    (target-inert-quotient-down-after-source-id-impossible
      inert-d′ down)
left-catchup-indexed-final-quotient-inner-stepᵀ
    (pure-step (β-seq vW)) vV noV vV′ noV′ inert-d′ inert-u′
    down@(down⊑downᵀ
      (C.cast-seq s⊢ t⊢ , NW.fun-untag-gen safe)
      d′⋒ V⊑V′ qD)
    widening pA =
  ⊥-elim
    (target-inert-after-source-untag-sequence-impossible
      inert-d′ down)
left-catchup-indexed-final-quotient-inner-stepᵀ
    (pure-step (β-seq vW)) vV noV vV′ noV′ inert-d′ inert-u′
    down@(down⊑downᵀ
      (C.cast-seq s⊢ t⊢ , gG NW.？︔ gⁿ)
      d′⋒ V⊑V′ qD)
    widening pA =
  ⊥-elim
    (target-inert-after-source-untag-sequence-impossible
      inert-d′ down)
left-catchup-indexed-final-quotient-inner-stepᵀ
    (pure-step (β-seq vW)) vV noV vV′ noV′ inert-d′ inert-u′
    down@(down⊑downᵀ
      (C.cast-seq s⊢ (C.cast-seal hX α∈Σ ok) ,
        nⁿ NW.︔seal α)
      d′⋒ V⊑V′ qD)
    widening pA =
  ⊥-elim (source-quotient-down-seal-tail-impossible down)
left-catchup-indexed-final-quotient-inner-stepᵀ
    (pure-step (β-seq vW)) vV noV vV′ noV′ inert-d′ inert-u′
    down@(gen-down⊑gen-downᵀ
      (C.cast-seq s⊢ t⊢ , NW.fun-untag-gen safe)
      d′⋒ V⊑V′ qD)
    widening pA =
  ⊥-elim
    (target-inert-after-source-untag-sequence-impossible
      inert-d′ down)
left-catchup-indexed-final-quotient-inner-stepᵀ
    (pure-step (β-seq vW)) vV noV vV′ noV′ inert-d′ inert-u′
    down@(gen-down⊑gen-downᵀ
      (C.cast-seq s⊢ t⊢ , gG NW.？︔ gⁿ)
      d′⋒ V⊑V′ qD)
    widening pA =
  ⊥-elim
    (target-inert-after-source-untag-sequence-impossible
      inert-d′ down)
left-catchup-indexed-final-quotient-inner-stepᵀ
    (pure-step (β-seq vW)) vV noV vV′ noV′ inert-d′ inert-u′
    down@(gen-down⊑gen-downᵀ
      (C.cast-seq s⊢ (C.cast-seal hX α∈Σ ok) ,
        nⁿ NW.︔seal α)
      d′⋒ V⊑V′ qD)
    widening pA =
  ⊥-elim (source-quotient-down-seal-tail-impossible down)
left-catchup-indexed-final-quotient-inner-stepᵀ
    (pure-step (β-inst vW)) vV noV vV′ noV′ inert-d′ inert-u′
    (down⊑downᵀ (d⊢ , NW.cross ()) d′⊒ V⊑V′ qD)
    widening pA
left-catchup-indexed-final-quotient-inner-stepᵀ
    (pure-step (β-inst vW)) vV noV vV′ noV′ inert-d′ inert-u′
    (gen-down⊑gen-downᵀ (d⊢ , NW.cross ()) d′⊒ V⊑V′ qD)
    widening pA
left-catchup-indexed-final-quotient-inner-stepᵀ {qD = qD}
    (pure-step (tag-untag-ok vW)) vV noV vV′ noV′
    inert-d′ inert-u′ down widening pA =
  ⊥-elim (target-inert-after-source-untag-impossible inert-d′ down)
left-catchup-indexed-final-quotient-inner-stepᵀ
    (pure-step (tag-untag-bad vW G≢H)) vV noV vV′ noV′
    inert-d′ inert-u′ down widening pA =
  left-catchup-indexed-two-keep-to-blameᵀ
    (↠-step (ξ-⟨⟩ (pure-step (tag-untag-bad vW G≢H)))
      (↠-step (pure-step blame-⟨⟩) ↠-refl))
    (nu-term-imprecision-target-typing
      (up⊑upᵀ down widening pA))
left-catchup-indexed-final-quotient-inner-stepᵀ
    (pure-step (seal-unseal vW)) vV noV vV′ noV′
    inert-d′ inert-u′ down widening pA =
  ⊥-elim (source-quotient-down-unseal-impossible down)
left-catchup-indexed-final-quotient-inner-stepᵀ
    (pure-step blame-⟨⟩) () noV vV′ noV′ inert-d′ inert-u′
    down widening pA
left-catchup-indexed-final-quotient-inner-stepᵀ
    (ξ-⟨⟩ V→) vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA =
  ⊥-elim (value-no-step vV V→)

left-catchup-indexed-final-quotient-after-source-stepᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ L d d′ u u′}
    {D D′ A A′ : T.Ty}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  Inert d′ →
  Inert u′ →
  ((V ⟨ d ⟩) ⟨ u ⟩) —→[ keep ] L →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ V ⟨ d ⟩ ⊑ V′ ⟨ d′ ⟩
    ⦂ D ⊑ᵖ D′ ∶ qD) →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  LeftCatchupIndexedResult
      {N = (V ⟨ d ⟩) ⟨ u ⟩}
      {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
      {ρ = ρ} pA
  ⊎ ∃[ B ] ∃[ s ]
      (u ≡ inst B s) ×
      (((V ⟨ d ⟩) ⟨ u ⟩)
        —↠[ keep ∷ bind ★ ∷ [] ]
          ((NT.⇑ᵗᵐ (V ⟨ d ⟩)) •) ⟨ s ⟩)
  ⊎ ∃[ B ] ∃[ s ]
      (u ≡ (inst B s ︔ ((★ T.⇒ ★) !))) ×
      (((V ⟨ d ⟩) ⟨ u ⟩)
        —↠[ keep ∷ keep ∷ bind ★ ∷ [] ]
          ((((NT.⇑ᵗᵐ (V ⟨ d ⟩)) •) ⟨ s ⟩)
            ⟨ ⇑ᶜ ((★ T.⇒ ★) !) ⟩))
left-catchup-indexed-final-quotient-after-source-stepᵀ
    vV noV vV′ noV′ inert-d′ inert-u′
    (pure-step source→) down widening pA =
  left-catchup-indexed-final-quotient-outer-pureᵀ {pA = pA}
    source→ vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA
left-catchup-indexed-final-quotient-after-source-stepᵀ
    vV noV vV′ noV′ inert-d′ inert-u′
    (ξ-⟨⟩ source→) down widening pA =
  inj₁ (left-catchup-indexed-final-quotient-inner-stepᵀ {pA = pA}
    source→ vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA)

left-catchup-indexed-final-quotient-activeᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ d d′ u u′}
    {D D′ A A′ : T.Ty}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  Inert d′ →
  Inert u′ →
  (Inert d × Inert u → ⊥) →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ V ⟨ d ⟩ ⊑ V′ ⟨ d′ ⟩
    ⦂ D ⊑ᵖ D′ ∶ qD) →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  LeftCatchupIndexedResult
      {N = (V ⟨ d ⟩) ⟨ u ⟩}
      {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
      {ρ = ρ} pA
  ⊎ ∃[ B ] ∃[ s ]
      (u ≡ inst B s) ×
      (((V ⟨ d ⟩) ⟨ u ⟩)
        —↠[ keep ∷ bind ★ ∷ [] ]
          ((NT.⇑ᵗᵐ (V ⟨ d ⟩)) •) ⟨ s ⟩)
  ⊎ ∃[ B ] ∃[ s ]
      (u ≡ (inst B s ︔ ((★ T.⇒ ★) !))) ×
      (((V ⟨ d ⟩) ⟨ u ⟩)
        —↠[ keep ∷ keep ∷ bind ★ ∷ [] ]
          ((((NT.⇑ᵗᵐ (V ⟨ d ⟩)) •) ⟨ s ⟩)
            ⟨ ⇑ᶜ ((★ T.⇒ ★) !) ⟩))
left-catchup-indexed-final-quotient-activeᵀ
    vV noV vV′ noV′ inert-d′ inert-u′
    source-active
    down@(down⊑downᵀ d⊒ d′⊒ V⊑V′ qD)
    widening@(quotient-id-widening u⊑ u′⊑) pA
    with active-double-cast-step vV noV
      (forget (nu-term-imprecision-source-typing V⊑V′))
      (proj₁ d⊒) (proj₁ u⊑) source-active
left-catchup-indexed-final-quotient-activeᵀ
    vV noV vV′ noV′ inert-d′ inert-u′
    source-active
    down@(down⊑downᵀ d⊒ d′⊒ V⊑V′ qD)
    widening@(quotient-id-widening u⊑ u′⊑) pA
    | L , source→ =
  left-catchup-indexed-final-quotient-after-source-stepᵀ {pA = pA}
    vV noV vV′ noV′ inert-d′ inert-u′
    source→ down widening pA
left-catchup-indexed-final-quotient-activeᵀ
    vV noV vV′ noV′ inert-d′ inert-u′
    source-active
    down@(down⊑downᵀ d⊒ d′⊒ V⊑V′ qD)
    widening@(quotient-cast-widening
      mode seal★ u⊑ mode′ seal★′ u′⊑) pA
    with active-double-cast-step vV noV
      (forget (nu-term-imprecision-source-typing V⊑V′))
      (proj₁ d⊒) (proj₁ u⊑) source-active
left-catchup-indexed-final-quotient-activeᵀ
    vV noV vV′ noV′ inert-d′ inert-u′
    source-active
    down@(down⊑downᵀ d⊒ d′⊒ V⊑V′ qD)
    widening@(quotient-cast-widening
      mode seal★ u⊑ mode′ seal★′ u′⊑) pA
    | L , source→ =
  left-catchup-indexed-final-quotient-after-source-stepᵀ {pA = pA}
    vV noV vV′ noV′ inert-d′ inert-u′
    source→ down widening pA
left-catchup-indexed-final-quotient-activeᵀ
    vV noV vV′ noV′ inert-d′ inert-u′
    source-active
    down@(gen-down⊑gen-downᵀ d⊒ d′⊒ V⊑V′ qD)
    widening@(quotient-id-widening u⊑ u′⊑) pA
    with active-double-cast-step vV noV
      (forget (nu-term-imprecision-source-typing V⊑V′))
      (proj₁ d⊒) (proj₁ u⊑) source-active
left-catchup-indexed-final-quotient-activeᵀ
    vV noV vV′ noV′ inert-d′ inert-u′
    source-active
    down@(gen-down⊑gen-downᵀ d⊒ d′⊒ V⊑V′ qD)
    widening@(quotient-id-widening u⊑ u′⊑) pA
    | L , source→ =
  left-catchup-indexed-final-quotient-after-source-stepᵀ {pA = pA}
    vV noV vV′ noV′ inert-d′ inert-u′
    source→ down widening pA
left-catchup-indexed-final-quotient-activeᵀ
    vV noV vV′ noV′ inert-d′ inert-u′
    source-active
    down@(gen-down⊑gen-downᵀ d⊒ d′⊒ V⊑V′ qD)
    widening@(quotient-cast-widening
      mode seal★ u⊑ mode′ seal★′ u′⊑) pA
    with active-double-cast-step vV noV
      (forget (nu-term-imprecision-source-typing V⊑V′))
      (proj₁ d⊒) (proj₁ u⊑) source-active
left-catchup-indexed-final-quotient-activeᵀ
    vV noV vV′ noV′ inert-d′ inert-u′
    source-active
    down@(gen-down⊑gen-downᵀ d⊒ d′⊒ V⊑V′ qD)
    widening@(quotient-cast-widening
      mode seal★ u⊑ mode′ seal★′ u′⊑) pA
    | L , source→ =
  left-catchup-indexed-final-quotient-after-source-stepᵀ {pA = pA}
    vV noV vV′ noV′ inert-d′ inert-u′
    source→ down widening pA

left-catchup-indexed-final-quotient-valueᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ d d′ u u′}
    {D D′ A A′ : T.Ty}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  Inert d′ →
  Inert u′ →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ V ⟨ d ⟩ ⊑ V′ ⟨ d′ ⟩
    ⦂ D ⊑ᵖ D′ ∶ qD) →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  LeftCatchupIndexedResult
      {N = (V ⟨ d ⟩) ⟨ u ⟩}
      {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
      {ρ = ρ} pA
  ⊎ ∃[ B ] ∃[ s ]
      (u ≡ inst B s) ×
      (((V ⟨ d ⟩) ⟨ u ⟩)
        —↠[ keep ∷ bind ★ ∷ [] ]
          ((NT.⇑ᵗᵐ (V ⟨ d ⟩)) •) ⟨ s ⟩)
  ⊎ ∃[ B ] ∃[ s ]
      (u ≡ (inst B s ︔ ((★ T.⇒ ★) !))) ×
      (((V ⟨ d ⟩) ⟨ u ⟩)
        —↠[ keep ∷ keep ∷ bind ★ ∷ [] ]
          ((((NT.⇑ᵗᵐ (V ⟨ d ⟩)) •) ⟨ s ⟩)
            ⟨ ⇑ᶜ ((★ T.⇒ ★) !) ⟩))
left-catchup-indexed-final-quotient-valueᵀ
    vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA
    with inert-dec _ | inert-dec _
left-catchup-indexed-final-quotient-valueᵀ
    vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA
    | yes inert-d | yes inert-u =
  inj₁ (left-catchup-indexed-final-quotient-inertᵀ
    vV noV inert-d inert-u (up⊑upᵀ down widening pA))
left-catchup-indexed-final-quotient-valueᵀ
    vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA
    | yes inert-d | no not-inert-u =
  left-catchup-indexed-final-quotient-activeᵀ {pA = pA}
    vV noV vV′ noV′ inert-d′ inert-u′
    (λ { (source-d , source-u) → not-inert-u source-u })
    down widening pA
left-catchup-indexed-final-quotient-valueᵀ
    vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA
    | no not-inert-d | yes inert-u =
  left-catchup-indexed-final-quotient-activeᵀ {pA = pA}
    vV noV vV′ noV′ inert-d′ inert-u′
    (λ { (source-d , source-u) → not-inert-d source-d })
    down widening pA
left-catchup-indexed-final-quotient-valueᵀ
    vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA
    | no not-inert-d | no not-inert-u =
  left-catchup-indexed-final-quotient-activeᵀ {pA = pA}
    vV noV vV′ noV′ inert-d′ inert-u′
    (λ { (source-d , source-u) → not-inert-d source-d })
    down widening pA

left-catchup-indexed-final-quotientᵀ :
  ∀ {Φ Δᴸ Δᴿ V V′ d d′ u u′}
    {D D′ A A′ : T.Ty}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value V′ →
  No• V′ →
  Inert d′ →
  Inert u′ →
  (Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ V ⟨ d ⟩ ⊑ V′ ⟨ d′ ⟩
    ⦂ D ⊑ᵖ D′ ∶ qD) →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  ((Value V × No• V) ⊎ V ≡ blame) →
  LeftCatchupIndexedResult
      {N = (V ⟨ d ⟩) ⟨ u ⟩}
      {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
      {ρ = ρ} pA
  ⊎ ∃[ B ] ∃[ s ]
      (u ≡ inst B s) ×
      (((V ⟨ d ⟩) ⟨ u ⟩)
        —↠[ keep ∷ bind ★ ∷ [] ]
          ((NT.⇑ᵗᵐ (V ⟨ d ⟩)) •) ⟨ s ⟩)
  ⊎ ∃[ B ] ∃[ s ]
      (u ≡ (inst B s ︔ ((★ T.⇒ ★) !))) ×
      (((V ⟨ d ⟩) ⟨ u ⟩)
        —↠[ keep ∷ keep ∷ bind ★ ∷ [] ]
          ((((NT.⇑ᵗᵐ (V ⟨ d ⟩)) •) ⟨ s ⟩)
            ⟨ ⇑ᶜ ((★ T.⇒ ★) !) ⟩))
left-catchup-indexed-final-quotientᵀ
    vV′ noV′ inert-d′ inert-u′
    down widening pA (inj₁ (vV , noV)) =
  left-catchup-indexed-final-quotient-valueᵀ {pA = pA}
    vV noV vV′ noV′ inert-d′ inert-u′
    down widening pA
left-catchup-indexed-final-quotientᵀ
    vV′ noV′ inert-d′ inert-u′
    down widening pA (inj₂ refl) =
  inj₁ (left-catchup-indexed-double-cast-blameᵀ {p = pA}
    (nu-term-imprecision-target-typing
      (up⊑upᵀ down widening pA)))
