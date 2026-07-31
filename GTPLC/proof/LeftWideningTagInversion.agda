module proof.LeftWideningTagInversion where

-- File Charter:
--   * Inverts factored term narrowing whose left value has a tag coercion.
--   * Identifies the tag from the normalized left narrowing composition.
--   * Preserves the shared relocation and right narrowing components.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true)
open import Data.Nat using (_<_)
open import Data.Product using (_×_; _,_; proj₁; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; refl; subst; sym; trans)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore
open import Coercions
open import Terms
open import TypeRelocate
open import NarrowWiden
open import FactoredTypeNarrowing
open import EnvironmentNarrowing
open import ImprecisionTheorems using (dualʷ; _⨟ⁿ_)
open import TermNarrowing
open import proof.TypeInTypeSubst using (tagged-unique)
open import proof.NarrowWidenDeterminism using (narrowing-determined)

------------------------------------------------------------------------
-- The leading untag of a normalized tag composition
------------------------------------------------------------------------

data UntagPrefix (G : Tag) : Coercion → Set where
  prefix-only : UntagPrefix G (G ？)
  prefix-seq : ∀ {c d}
    → UntagPrefix G c
    → UntagPrefix G (c ︔ d)

untag-prefix-unique : ∀ {G H c}
  → UntagPrefix G c
  → UntagPrefix H c
  → G ≡ H
untag-prefix-unique prefix-only prefix-only = refl
untag-prefix-unique (prefix-seq p) (prefix-seq q) =
  untag-prefix-unique p q

tagged-narrowing-star⊥ : ∀ {μ Δ Σ G A c}
  → G ꞉ A
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ ★
  → ⊥
tagged-narrowing-star⊥ (tag-var X) ()
tagged-narrowing-star⊥ (tag-base ι) ()
tagged-narrowing-star⊥ tag-fun ()

wrap-untag-prefix : ∀ {μ Δ Σ G A B c}
    (hG : WfTag Δ G)
    (allowed : tagAllowed μ G ≡ true)
    (G꞉A : G ꞉ A)
    (p : μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B)
  → UntagPrefix G (proj₁ (wrap-untag hG allowed G꞉A p))
wrap-untag-prefix hG allowed G꞉A (idᵃ (＇ X) hX) = prefix-only
wrap-untag-prefix hG allowed (tag-var X)
    (seal X<Δ hA X,A∈Σ seal-ok) =
  prefix-seq prefix-only
wrap-untag-prefix hG allowed (tag-base ι)
    (seal X<Δ hA X,A∈Σ seal-ok) =
  prefix-seq prefix-only
wrap-untag-prefix hG allowed tag-fun
    (seal X<Δ hA X,A∈Σ seal-ok) =
  prefix-seq prefix-only
wrap-untag-prefix hG allowed G꞉A
    (seal-seq {B = ＇ Y} p X<Δ X,B∈Σ seal-ok A≢B)
    with wrap-untag-prefix hG allowed G꞉A p
wrap-untag-prefix hG allowed G꞉A
    (seal-seq {B = ＇ Y} p X<Δ X,B∈Σ seal-ok A≢B) | prefix =
  prefix-seq prefix
wrap-untag-prefix hG allowed G꞉A
    (seal-seq {B = ‵ ι} p X<Δ X,B∈Σ seal-ok A≢B)
    with wrap-untag-prefix hG allowed G꞉A p
wrap-untag-prefix hG allowed G꞉A
    (seal-seq {B = ‵ ι} p X<Δ X,B∈Σ seal-ok A≢B) | prefix =
  prefix-seq prefix
wrap-untag-prefix hG allowed G꞉A
    (seal-seq {B = ★} p X<Δ X,B∈Σ seal-ok A≢B) =
  ⊥-elim (tagged-narrowing-star⊥ G꞉A p)
wrap-untag-prefix hG allowed G꞉A
    (seal-seq {B = B ⇒ C} p X<Δ X,B∈Σ seal-ok A≢B)
    with wrap-untag-prefix hG allowed G꞉A p
wrap-untag-prefix hG allowed G꞉A
    (seal-seq {B = B ⇒ C} p X<Δ X,B∈Σ seal-ok A≢B) | prefix =
  prefix-seq prefix
wrap-untag-prefix hG allowed G꞉A
    (seal-seq {B = `∀ B} p X<Δ X,B∈Σ seal-ok A≢B)
    with wrap-untag-prefix hG allowed G꞉A p
wrap-untag-prefix hG allowed G꞉A
    (seal-seq {B = `∀ B} p X<Δ X,B∈Σ seal-ok A≢B) | prefix =
  prefix-seq prefix
wrap-untag-prefix {A = A} {B = ‵ ι} hG allowed G꞉A p
    with A ≟Ty (‵ ι)
wrap-untag-prefix hG allowed G꞉A p | yes refl = prefix-only
wrap-untag-prefix hG allowed G꞉A p | no A≢B = prefix-seq prefix-only
wrap-untag-prefix {A = A} {B = ★} hG allowed G꞉A p =
  ⊥-elim (tagged-narrowing-star⊥ G꞉A p)
wrap-untag-prefix {A = A} {B = B ⇒ C} hG allowed G꞉A p
    with A ≟Ty (B ⇒ C)
wrap-untag-prefix hG allowed G꞉A p | yes refl = prefix-only
wrap-untag-prefix hG allowed G꞉A p | no A≢B = prefix-seq prefix-only
wrap-untag-prefix {A = A} {B = `∀ B} hG allowed G꞉A p
    with A ≟Ty (`∀ B)
wrap-untag-prefix hG allowed G꞉A p | yes refl = prefix-only
wrap-untag-prefix hG allowed G꞉A p | no A≢B = prefix-seq prefix-only

dual-tag-composition-prefix : ∀ {μ Δ Σ G A B}
    (u⊑ : μ ∣ Δ ∣ Σ ⊢ G ! ⦂ A ⊑ ★)
    (p : μ ∣ Δ ∣ Σ ⊢ A ⊒ B)
  → UntagPrefix G (proj₁ (dualʷ (G ! , u⊑) ⨟ⁿ p))
dual-tag-composition-prefix
    (tag G hG allowed G꞉A) (c , p) =
  wrap-untag-prefix hG allowed G꞉A p

dual-tag-composition-tags-equal : ∀ {μ Δ Σ G H A B C}
    {u⊑ : μ ∣ Δ ∣ Σ ⊢ G ! ⦂ A ⊑ ★}
    {v⊑ : μ ∣ Δ ∣ Σ ⊢ H ! ⦂ B ⊑ ★}
    {p : μ ∣ Δ ∣ Σ ⊢ A ⊒ C}
    {q : μ ∣ Δ ∣ Σ ⊢ B ⊒ C}
  → proj₁ (dualʷ (G ! , u⊑) ⨟ⁿ p) ≡
    proj₁ (dualʷ (H ! , v⊑) ⨟ⁿ q)
  → G ≡ H
dual-tag-composition-tags-equal {u⊑ = u⊑} {v⊑ = v⊑}
    {p = p} {q = q} eq =
  untag-prefix-unique
    (dual-tag-composition-prefix u⊑ p)
    (Relation.Binary.PropositionalEquality.subst
      (UntagPrefix _) (sym eq)
      (dual-tag-composition-prefix v⊑ q))

------------------------------------------------------------------------
-- Cancellation of a shared tag prefix
------------------------------------------------------------------------

tag-seal-modes-exclusive : ∀ {μ X}
  → tagAllowed μ (＇ X) ≡ true
  → sealModeAllowed (μ X) ≡ true
  → ⊥
tag-seal-modes-exclusive {μ} {X} tag-ok seal-ok with μ X
tag-seal-modes-exclusive tag-ok () | id-only
tag-seal-modes-exclusive tag-ok () | tag-or-id
tag-seal-modes-exclusive () seal-ok | seal-or-id

variable-tag-endomorphism : ∀ {μ Δ Σ X c}
  → tagAllowed μ (＇ X) ≡ true
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ＇ X ⊒ ＇ X
  → c ≡ id
variable-tag-endomorphism tag-ok (idᵃ (＇ X) hX) = refl
variable-tag-endomorphism {μ = μ} {X = X} tag-ok
    (seal X<Δ hX X,X∈Σ seal-ok) =
  ⊥-elim (tag-seal-modes-exclusive {μ = μ} {X = X}
    tag-ok seal-ok)
variable-tag-endomorphism {μ = μ} {X = X} tag-ok
    (seal-seq p X<Δ X,A∈Σ seal-ok X≢A) =
  ⊥-elim (tag-seal-modes-exclusive {μ = μ} {X = X}
    tag-ok seal-ok)

base-tag-endomorphism : ∀ {μ Δ Σ ι c}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ‵ ι ⊒ ‵ ι
  → c ≡ id
base-tag-endomorphism (idᵃ (‵ ι) hι) = refl

star-widening-endomorphism : ∀ {μ Δ Σ c}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ★ ⊑ ★
  → c ≡ id
star-widening-endomorphism (idᵃ ★ h★) = refl
star-widening-endomorphism
    (tag-seq G p hG allowed G꞉B nonvar★ ★≢B) =
  ⊥-elim (★≢B (sym (star-widening-target p)))
  where
  star-widening-target : ∀ {μ Δ Σ c B}
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ ★ ⊑ B
    → B ≡ ★
  star-widening-target (idᵃ ★ h★) = refl
  star-widening-target
    (tag-seq G q hG allowed G꞉B nonvar★ A≢B) = refl

star-narrowing-endomorphism : ∀ {μ Δ Σ c}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ★ ⊒ ★
  → c ≡ id
star-narrowing-endomorphism (idᵃ ★ h★) = refl
star-narrowing-endomorphism
    (untag-seq G hG allowed G꞉A p nonvar★ A≢★) =
  ⊥-elim (A≢★ (narrowing-target-star p))
  where
  narrowing-target-star : ∀ {μ Δ Σ c A}
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ ★
    → A ≡ ★
  narrowing-target-star (idᵃ ★ h★) = refl
  narrowing-target-star
      (untag-seq G hG allowed G꞉A q nonvar★ A≢★) = refl

function-tag-endomorphism : ∀ {μ Δ Σ c}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ (★ ⇒ ★) ⊒ (★ ⇒ ★)
  → c ≡ (id ↦ id)
function-tag-endomorphism (p ↦ q)
    rewrite star-widening-endomorphism p
      | star-narrowing-endomorphism q =
  refl

tag-endomorphism-unique : ∀ {μ Δ Σ G A c d}
  → tagAllowed μ G ≡ true
  → G ꞉ A
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ A
  → μ ∣ Δ ∣ Σ ⊢ d ⦂ A ⊒ A
  → c ≡ d
tag-endomorphism-unique allowed (tag-var X) p q =
  trans (variable-tag-endomorphism allowed p)
    (sym (variable-tag-endomorphism allowed q))
tag-endomorphism-unique allowed (tag-base ι) p q =
  trans (base-tag-endomorphism p) (sym (base-tag-endomorphism q))
tag-endomorphism-unique allowed tag-fun p q =
  trans (function-tag-endomorphism p)
    (sym (function-tag-endomorphism q))

sequence-tail-injective : ∀ {c d e}
  → (c ︔ d) ≡ (c ︔ e)
  → d ≡ e
sequence-tail-injective refl = refl

tag-prefix-cancel : ∀ {μ Δ Σ G A C}
    {u v : μ ∣ Δ ∣ Σ ⊢ G ! ⦂ A ⊑ ★}
    {p q : μ ∣ Δ ∣ Σ ⊢ A ⊒ C}
  → StoreWf Δ Σ
  → (dualʷ (G ! , u) ⨟ⁿ p) ≐ⁿ
      (dualʷ (G ! , v) ⨟ⁿ q)
  → p ≐ⁿ q
tag-prefix-cancel {p = p} {q = q} wfΣ eq =
  narrowing-determined wfΣ p q

------------------------------------------------------------------------
-- Left widening tag inversion
------------------------------------------------------------------------

left-widening-tag-inversion-match :
    ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ V V′ A B C C′ G H}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}}
      {v⊑ : ρ ⊢ᴸʷ H ! ⦂ A ⊑ ★}
      {pᴸ : ρ ⊢ᴸⁿ A ⊒ C}
      {qᴸ : ρ ⊢ᴸⁿ ★ ⊒ C}
      {relocation : Φ ⊢ C ≈ C′}
      {pᴿ : ρ ⊢ᴿⁿ C′ ⊒ B}
  → StoreWf Δᴸ Σᴸ
  → Value V
  → Value V′
  → ρ ⊢ᴺ V ⟨ G ! ⟩ ⊒ V′
      ∶ (qᴸ ⨟ᶠ relocation ⨟ᶠ pᴿ)
  → (dualʷ (H ! , v⊑) ⨟ⁿ pᴸ) ≐ⁿ qᴸ
  → (G ≡ H)
    × Σ[ pᴸ′ ∈ ρ ⊢ᴸⁿ A ⊒ C ]
        (pᴸ′ ≐ⁿ pᴸ)
      × (ρ ⊢ᴺ V ⊒ V′
          ∶ (pᴸ′ ⨟ᶠ relocation ⨟ᶠ pᴿ))
left-widening-tag-inversion-match wfΣᴸ vV () (⊒blame M⊢) eq
left-widening-tag-inversion-match
    {v⊑ = tag H hH allowedH H꞉A}
    wfΣᴸ vV vV′
    (castʷ⊒
      {pᴸ = pᴸ′}
      {s⦂ = tag G hG allowedG G꞉A′}
      V⊒V′ eq′) eq
    with dual-tag-composition-tags-equal
      {u⊑ = tag G hG allowedG G꞉A′}
      {v⊑ = tag H hH allowedH H꞉A}
      {p = pᴸ′} {q = _}
      (trans eq′ (sym eq))
left-widening-tag-inversion-match
    {v⊑ = tag .G hH allowedH H꞉A}
    wfΣᴸ vV vV′
    (castʷ⊒
      {pᴸ = pᴸ′}
      {s⦂ = tag G hG allowedG G꞉A′}
      V⊒V′ eq′) eq
    | refl with tagged-unique G꞉A′ H꞉A
left-widening-tag-inversion-match
    {v⊑ = tag .G hH allowedH H꞉A}
    wfΣᴸ vV vV′
    (castʷ⊒
      {pᴸ = pᴸ′}
      {s⦂ = tag G hG allowedG G꞉A′}
      V⊒V′ eq′) eq
    | refl | refl =
  refl , pᴸ′ ,
  tag-prefix-cancel
    {u = tag G hG allowedG G꞉A′}
    {v = tag G hH allowedH H꞉A}
    {p = pᴸ′}
    wfΣᴸ
    (trans eq′ (sym eq)) ,
  V⊒V′
left-widening-tag-inversion-match wfΣᴸ vV vV′
    (⊒Λ {B≢★ = B≢★} extension vW′ W⊒W′) eq =
  ⊥-elim (B≢★ refl)
left-widening-tag-inversion-match wfΣᴸ vV vV′
    (⊒⟨ν⟩ {B≢★ = B≢★} vW′ W′⊢ hC c⊢ W⊒W′) eq =
  ⊥-elim (B≢★ refl)
left-widening-tag-inversion-match {v⊑ = v⊑} {pᴸ = pᴸ}
    wfΣᴸ vV (vW′ ⟨ i′ ⟩)
    (⊒castⁿ {t⦂ = t⦂} W⊒W′ eq′) eq
    with left-widening-tag-inversion-match
      {v⊑ = v⊑} {pᴸ = pᴸ} wfΣᴸ vV vW′ W⊒W′ eq
left-widening-tag-inversion-match wfΣᴸ vV (vW′ ⟨ i′ ⟩)
    (⊒castⁿ {t⦂ = t⦂} W⊒W′ eq′) eq
    | G≡H , pᴸ′ , pᴸ′≐pᴸ , V⊒W′ =
  G≡H , pᴸ′ , pᴸ′≐pᴸ ,
  ⊒castⁿ {t⦂ = t⦂} V⊒W′ eq′
left-widening-tag-inversion-match {v⊑ = v⊑} {pᴸ = pᴸ}
    wfΣᴸ vV (vW′ ⟨ i′ ⟩)
    (⊒castʷ {t⦂ = t⦂} W⊒W′ eq′) eq
    with left-widening-tag-inversion-match
      {v⊑ = v⊑} {pᴸ = pᴸ} wfΣᴸ vV vW′ W⊒W′ eq
left-widening-tag-inversion-match wfΣᴸ vV (vW′ ⟨ i′ ⟩)
    (⊒castʷ {t⦂ = t⦂} W⊒W′ eq′) eq
    | G≡H , pᴸ′ , pᴸ′≐pᴸ , V⊒W′ =
  G≡H , pᴸ′ , pᴸ′≐pᴸ ,
  ⊒castʷ {t⦂ = t⦂} V⊒W′ eq′

left-widening-tag-inversion :
    ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ V V′ A B C C′ G}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {ρ : NarrowingEnv Φ {Σᴸ} {Σᴿ} {Γᴸ} {Γᴿ}}
      {u⊑ : ρ ⊢ᴸʷ G ! ⦂ A ⊑ ★}
      {pᴸ : ρ ⊢ᴸⁿ A ⊒ C}
      {qᴸ : ρ ⊢ᴸⁿ ★ ⊒ C}
      {relocation : Φ ⊢ C ≈ C′}
      {pᴿ : ρ ⊢ᴿⁿ C′ ⊒ B}
  → StoreWf Δᴸ Σᴸ
  → Value V
  → Value V′
  → ρ ⊢ᴺ V ⟨ G ! ⟩ ⊒ V′
      ∶ (qᴸ ⨟ᶠ relocation ⨟ᶠ pᴿ)
  → (dualʷ (G ! , u⊑) ⨟ⁿ pᴸ) ≐ⁿ qᴸ
  → Σ[ pᴸ′ ∈ ρ ⊢ᴸⁿ A ⊒ C ]
      (pᴸ′ ≐ⁿ pᴸ)
    × (ρ ⊢ᴺ V ⊒ V′
        ∶ (pᴸ′ ⨟ᶠ relocation ⨟ᶠ pᴿ))
left-widening-tag-inversion {G = G} {u⊑ = u⊑}
    wfΣᴸ vV vV′ taggedV⊒V′ eq
    with left-widening-tag-inversion-match
      {H = G} {v⊑ = u⊑} wfΣᴸ vV vV′ taggedV⊒V′ eq
left-widening-tag-inversion wfΣᴸ vV vV′ taggedV⊒V′ eq
    | refl , pᴸ′ , pᴸ′≐pᴸ , untaggedV⊒V′ =
  pᴸ′ , pᴸ′≐pᴸ , untaggedV⊒V′
