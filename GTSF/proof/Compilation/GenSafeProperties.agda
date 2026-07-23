module proof.Compilation.GenSafeProperties where

-- File charter:
--   * Relates the narrowing-only `GenSafe` grammar to operational `Inert`.
--   * Proves that a `GenSafe` cast preserves values and that every narrowing
--     `gen` exposes a `GenSafe` body.
--   * Isolates the one structural difference between the two categories:
--     standalone seal coercions are inert narrowings but cannot be well-typed
--     generalization bodies.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
import Coercions as C
open C using
  ( Coercion
  ; Inert
  ; ModeEnv
  ; cast-seal
  ; cast-gen
  ; cast-inst
  ; genᵈ
  ; seal
  ; _↦_
  ; `∀
  ; _∣_∣_⊢_∶_=⇒_
  )
open import NarrowWiden
open import NuTerms using (Term; Value; _⟨_⟩)

data GenSafeShape : Ty → Set where
  shape-fun : ∀ {A B} → GenSafeShape (A ⇒ B)
  shape-all : ∀ {A} → GenSafeShape (`∀ A)

genSafe-source-shape :
  ∀ {μ : ModeEnv} {Δ Σ A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  GenSafe c →
  GenSafeShape A
genSafe-source-shape (C.cast-fun s⊢ t⊢) (safe-fun sʷ tⁿ) = shape-fun
genSafe-source-shape (C.cast-all c⊢) (safe-all sⁿ) = shape-all
genSafe-source-shape {A = ＇ α}
    (cast-gen hA occ c⊢) (safe-gen safe)
    with genSafe-source-shape c⊢ safe
genSafe-source-shape {A = ＇ α}
    (cast-gen hA occ c⊢) (safe-gen safe) | ()
genSafe-source-shape {A = ‵ ι}
    (cast-gen hA occ c⊢) (safe-gen safe)
    with genSafe-source-shape c⊢ safe
genSafe-source-shape {A = ‵ ι}
    (cast-gen hA occ c⊢) (safe-gen safe) | ()
genSafe-source-shape {A = ★}
    (cast-gen hA occ c⊢) (safe-gen safe)
    with genSafe-source-shape c⊢ safe
genSafe-source-shape {A = ★}
    (cast-gen hA occ c⊢) (safe-gen safe) | ()
genSafe-source-shape {A = A ⇒ B}
    (cast-gen hA occ c⊢) (safe-gen safe) = shape-fun
genSafe-source-shape {A = `∀ A}
    (cast-gen hA occ c⊢) (safe-gen safe) = shape-all

genSafe-target-shape :
  ∀ {μ : ModeEnv} {Δ Σ A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  GenSafe c →
  GenSafeShape B
genSafe-target-shape (C.cast-fun s⊢ t⊢) (safe-fun sʷ tⁿ) = shape-fun
genSafe-target-shape (C.cast-all c⊢) (safe-all sⁿ) = shape-all
genSafe-target-shape (cast-gen hA occ c⊢) (safe-gen safe) = shape-all

instSafe-source-shape :
  ∀ {μ : ModeEnv} {Δ Σ A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  InstSafe c →
  GenSafeShape A
instSafe-source-shape (C.cast-fun s⊢ t⊢) (safe-fun sⁿ tʷ) = shape-fun
instSafe-source-shape (C.cast-all c⊢) (safe-all sʷ) = shape-all
instSafe-source-shape (cast-inst hB occ c⊢) (safe-inst safe) = shape-all

instSafe-target-shape :
  ∀ {μ : ModeEnv} {Δ Σ A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  InstSafe c →
  GenSafeShape B
instSafe-target-shape (C.cast-fun s⊢ t⊢) (safe-fun sⁿ tʷ) = shape-fun
instSafe-target-shape (C.cast-all c⊢) (safe-all sʷ) = shape-all
instSafe-target-shape {B = ＇ α}
    (cast-inst hB occ c⊢) (safe-inst safe)
    with instSafe-target-shape c⊢ safe
instSafe-target-shape {B = ＇ α}
    (cast-inst hB occ c⊢) (safe-inst safe) | ()
instSafe-target-shape {B = ‵ ι}
    (cast-inst hB occ c⊢) (safe-inst safe)
    with instSafe-target-shape c⊢ safe
instSafe-target-shape {B = ‵ ι}
    (cast-inst hB occ c⊢) (safe-inst safe) | ()
instSafe-target-shape {B = ★}
    (cast-inst hB occ c⊢) (safe-inst safe)
    with instSafe-target-shape c⊢ safe
instSafe-target-shape {B = ★}
    (cast-inst hB occ c⊢) (safe-inst safe) | ()
instSafe-target-shape {B = A ⇒ B}
    (cast-inst hB occ c⊢) (safe-inst safe) = shape-fun
instSafe-target-shape {B = `∀ B}
    (cast-inst hB occ c⊢) (safe-inst safe) = shape-all

raise-genSafeShape :
  ∀ {A} →
  GenSafeShape A →
  GenSafeShape (⇑ᵗ A)
raise-genSafeShape shape-fun = shape-fun
raise-genSafeShape shape-all = shape-all

lower-genSafeShape :
  ∀ {A} →
  GenSafeShape (⇑ᵗ A) →
  GenSafeShape A
lower-genSafeShape {A = ＇ α} ()
lower-genSafeShape {A = ‵ ι} ()
lower-genSafeShape {A = ★} ()
lower-genSafeShape {A = A ⇒ B} shape = shape-fun
lower-genSafeShape {A = `∀ A} shape = shape-all

ground-genSafeShape→fun :
  ∀ {G} →
  Ground G →
  GenSafeShape (⇑ᵗ G) →
  G ≡ (★ ⇒ ★)
ground-genSafeShape→fun (＇ α) ()
ground-genSafeShape→fun (‵ ι) ()
ground-genSafeShape→fun ★⇒★ shape-fun = refl

eager-gen-ground-function :
  ∀ {μ : ModeEnv} {Δ Σ G B c} →
  Ground G →
  genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ ⇑ᵗ G =⇒ B →
  GenSafe c →
  G ≡ (★ ⇒ ★)
eager-gen-ground-function gG c⊢ safe =
  ground-genSafeShape→fun gG (genSafe-source-shape c⊢ safe)

eager-inst-ground-function :
  ∀ {μ : ModeEnv} {Δ Σ G A c} →
  Ground G →
  C.instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ
    ⊢ c ∶ A =⇒ ⇑ᵗ G →
  InstSafe c →
  G ≡ (★ ⇒ ★)
eager-inst-ground-function gG c⊢ safe =
  ground-genSafeShape→fun gG (instSafe-target-shape c⊢ safe)

crossNarrowing-source-shape :
  ∀ {μ : ModeEnv} {Δ Σ A B c} →
  GenSafeShape B →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  CrossNarrowing c →
  GenSafeShape A
crossNarrowing-source-shape () (C.cast-id hA ok) (id-＇ α)
crossNarrowing-source-shape () (C.cast-id hA ok) (id-‵ ι)
crossNarrowing-source-shape shape-fun
    (C.cast-fun s⊢ t⊢) (sʷ ↦ tⁿ) =
  shape-fun
crossNarrowing-source-shape shape-all
    (C.cast-all c⊢) (`∀ sⁿ) =
  shape-all

crossWidening-target-shape :
  ∀ {μ : ModeEnv} {Δ Σ A B c} →
  GenSafeShape A →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  CrossWidening c →
  GenSafeShape B
crossWidening-target-shape () (C.cast-id hA ok) (id-＇ α)
crossWidening-target-shape () (C.cast-id hA ok) (id-‵ ι)
crossWidening-target-shape shape-fun
    (C.cast-fun s⊢ t⊢) (sⁿ ↦ tʷ) =
  shape-fun
crossWidening-target-shape shape-all
    (C.cast-all c⊢) (`∀ sʷ) =
  shape-all


genSafe-value :
  ∀ {V : Term} {c : Coercion} →
  Value V →
  GenSafe c →
  Value (V ⟨ c ⟩)
genSafe-value vV safe = vV ⟨ genSafe→inert safe ⟩

gen-body-genSafe :
  ∀ {A c} →
  Narrowing (C.gen A c) →
  GenSafe c
gen-body-genSafe (gen safe) = safe

genSafe→narrowing×inert :
  ∀ {c} →
  GenSafe c →
  Narrowing c × Inert c
genSafe→narrowing×inert safe =
  genSafe→narrowing safe , genSafe→inert safe

genSafe-star-source⊥ :
  ∀ {μ : ModeEnv} {Δ Σ B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ ★ =⇒ B →
  GenSafe c →
  ⊥
genSafe-star-source⊥ () (safe-fun sʷ tⁿ)
genSafe-star-source⊥ () (safe-all sⁿ)
genSafe-star-source⊥ (cast-gen hA occ c⊢) (safe-gen safe) =
  genSafe-star-source⊥ c⊢ safe

instSafe-star-target⊥ :
  ∀ {μ : ModeEnv} {Δ Σ A c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ ★ →
  InstSafe c →
  ⊥
instSafe-star-target⊥ () (safe-fun sⁿ tʷ)
instSafe-star-target⊥ () (safe-all sʷ)
instSafe-star-target⊥ (cast-inst hB occ c⊢) (safe-inst safe) =
  instSafe-star-target⊥ c⊢ safe

narrowing-inert-view :
  ∀ {c} →
  Narrowing c →
  Inert c →
  GenSafe c ⊎ ∃[ A ] ∃[ α ] c ≡ C.seal A α
narrowing-inert-view (cross (id-＇ α)) ()
narrowing-inert-view (cross (id-‵ ι)) ()
narrowing-inert-view (cross (sʷ ↦ tⁿ)) (_ ↦ _) =
  inj₁ (safe-fun sʷ tⁿ)
narrowing-inert-view (cross (`∀ sⁿ)) (`∀ _) = inj₁ (safe-all sⁿ)
narrowing-inert-view id★ ()
narrowing-inert-view (gen safe) (C.gen _ _) = inj₁ (safe-gen safe)
narrowing-inert-view (untag gG) ()
narrowing-inert-view (gG ？︔ gˢ) ()
narrowing-inert-view (sealⁿ A α) (C.seal _ _) = inj₂ (A , α , refl)
narrowing-inert-view (sˢ ︔seal α) ()

gen-body-seal⊥ :
  ∀ {μ : ModeEnv} {Δ Σ A B D α} →
  genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ C.seal D α ∶ A =⇒ B →
  occurs zero B ≡ true →
  ⊥
gen-body-seal⊥ {α = zero} (cast-seal hD α∈Σ ()) occ
gen-body-seal⊥ {α = suc α} (cast-seal hD α∈Σ ok) ()

narrowing-at-genSafe-source :
  ∀ {μ : ModeEnv} {Δ Σ A B c} →
  GenSafeShape A →
  genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ A =⇒ B →
  occurs zero B ≡ true →
  Narrowing c →
  GenSafe c
narrowing-at-genSafe-source shape-fun
    (C.cast-fun s⊢ t⊢) occ (cross (sʷ ↦ tⁿ)) =
  safe-fun sʷ tⁿ
narrowing-at-genSafe-source shape-all
    (C.cast-all c⊢) occ (cross (`∀ sⁿ)) =
  safe-all sⁿ
narrowing-at-genSafe-source shape-fun
    (cast-gen hA occB c⊢) occ (gen safe) =
  safe-gen safe
narrowing-at-genSafe-source shape-all
    (cast-gen hA occB c⊢) occ (gen safe) =
  safe-gen safe
narrowing-at-genSafe-source shape-all
    (cast-inst hB occA c⊢) occ (cross ())
narrowing-at-genSafe-source ()
    (C.cast-id hA ok) occ (cross (id-＇ α))
narrowing-at-genSafe-source ()
    (C.cast-id hA ok) occ (cross (id-‵ ι))
narrowing-at-genSafe-source () (C.cast-id hA ok) occ id★
narrowing-at-genSafe-source ()
    (C.cast-untag hG gG ok) occ (untag gG′)
narrowing-at-genSafe-source ()
    (C.cast-seq (C.cast-untag hG gG ok) c⊢) occ (gG′ ？︔ cⁿ)
narrowing-at-genSafe-source ()
    (C.cast-seq (C.cast-untag hG gG ok) (cast-gen hA occ c⊢))
    occB (fun-untag-gen safe)
narrowing-at-genSafe-source shape c⊢ occ (sealⁿ A α) =
  ⊥-elim (gen-body-seal⊥ c⊢ occ)
narrowing-at-genSafe-source shape
    (C.cast-seq s⊢ t⊢) occ (sⁿ ︔seal α) =
  ⊥-elim (gen-body-seal⊥ t⊢ occ)

narrowing-cross-all-fun⊥ :
  ∀ {μ : ModeEnv} {Δ Σ A B C c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ `∀ A =⇒ (B ⇒ C) →
  CrossNarrowing c →
  ⊥
narrowing-cross-all-fun⊥ () (id-＇ α)
narrowing-cross-all-fun⊥ () (id-‵ ι)
narrowing-cross-all-fun⊥ () (sʷ ↦ tⁿ)
narrowing-cross-all-fun⊥ () (`∀ sⁿ)

widening-cross-fun-all⊥ :
  ∀ {μ : ModeEnv} {Δ Σ A B C c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ (A ⇒ B) =⇒ `∀ C →
  CrossWidening c →
  ⊥
widening-cross-fun-all⊥ () (id-＇ α)
widening-cross-fun-all⊥ () (id-‵ ι)
widening-cross-fun-all⊥ () (sⁿ ↦ tʷ)
widening-cross-fun-all⊥ () (`∀ sʷ)

narrowing-between-genSafe-shapes :
  ∀ {μ : ModeEnv} {Δ Σ A B c} →
  GenSafeShape A →
  GenSafeShape B →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  Narrowing c →
  GenSafe c
narrowing-between-genSafe-shapes shape-fun shape-fun
    (C.cast-fun s⊢ t⊢) (cross (sʷ ↦ tⁿ)) =
  safe-fun sʷ tⁿ
narrowing-between-genSafe-shapes shape-all shape-all
    (C.cast-all c⊢) (cross (`∀ sⁿ)) =
  safe-all sⁿ
narrowing-between-genSafe-shapes shape-fun shape-all
    (cast-gen hA occ c⊢) (gen safe) =
  safe-gen safe
narrowing-between-genSafe-shapes shape-all shape-all
    (cast-gen hA occ c⊢) (gen safe) =
  safe-gen safe
narrowing-between-genSafe-shapes shape-all shape-fun
    c⊢ (cross cⁿ) =
  ⊥-elim (narrowing-cross-all-fun⊥ c⊢ cⁿ)
narrowing-between-genSafe-shapes shape-all shape-fun
    (C.cast-seq () t⊢)
    (fun-untag-gen safe)
narrowing-between-genSafe-shapes shape-all shape-fun
    (C.cast-seq s⊢ () ) (sⁿ ︔seal α)
narrowing-between-genSafe-shapes () shapeB
    (C.cast-id hA ok) (cross (id-＇ α))
narrowing-between-genSafe-shapes () shapeB
    (C.cast-id hA ok) (cross (id-‵ ι))
narrowing-between-genSafe-shapes () shapeB (C.cast-id hA ok) id★
narrowing-between-genSafe-shapes () shapeB
    (C.cast-untag hG gG ok) (untag gG′)
narrowing-between-genSafe-shapes () shapeB
    (C.cast-seq (C.cast-untag hG gG ok) c⊢) (gG′ ？︔ cⁿ)
narrowing-between-genSafe-shapes () shapeB
    (C.cast-seq (C.cast-untag hG ★⇒★ ok)
                (cast-gen hA occ c⊢))
    (fun-untag-gen safe)
narrowing-between-genSafe-shapes shapeA ()
    (C.cast-seal hA α∈Σ ok) (sealⁿ A α)
narrowing-between-genSafe-shapes shapeA ()
    (C.cast-seq s⊢ (C.cast-seal hA α∈Σ ok)) (sⁿ ︔seal α)

widening-between-genSafe-shapes :
  ∀ {μ : ModeEnv} {Δ Σ A B c} →
  GenSafeShape A →
  GenSafeShape B →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  Widening c →
  InstSafe c
widening-between-genSafe-shapes shape-fun shape-fun
    (C.cast-fun s⊢ t⊢) (cross (sⁿ ↦ tʷ)) =
  safe-fun sⁿ tʷ
widening-between-genSafe-shapes shape-all shape-all
    (C.cast-all c⊢) (cross (`∀ sʷ)) =
  safe-all sʷ
widening-between-genSafe-shapes shape-all shape-fun
    (cast-inst hB occ c⊢) (inst safe) =
  safe-inst safe
widening-between-genSafe-shapes shape-all shape-all
    (cast-inst hB occ c⊢) (inst safe) =
  safe-inst safe
widening-between-genSafe-shapes shape-fun shape-all
    c⊢ (cross cʷ) =
  ⊥-elim (widening-cross-fun-all⊥ c⊢ cʷ)
widening-between-genSafe-shapes shape-fun shape-all
    (C.cast-seq () t⊢)
    (inst-fun-tag safe)
widening-between-genSafe-shapes shape-fun shape-all
    (C.cast-seq () c⊢) (unseal︔_ α cʷ)
widening-between-genSafe-shapes () shapeB
    (C.cast-id hA ok) (cross (id-＇ α))
widening-between-genSafe-shapes () shapeB
    (C.cast-id hA ok) (cross (id-‵ ι))
widening-between-genSafe-shapes () shapeB (C.cast-id hA ok) id★
widening-between-genSafe-shapes shapeA ()
    (C.cast-tag hG gG ok) (tag gG′)
widening-between-genSafe-shapes shapeA ()
    (C.cast-seq c⊢ (C.cast-tag hG gG ok)) (cʷ ︔ gG′ !)
widening-between-genSafe-shapes shapeA ()
    (C.cast-seq (cast-inst hB occ c⊢) (C.cast-tag hG ★⇒★ ok))
    (inst-fun-tag safe)
widening-between-genSafe-shapes () shapeB
    (C.cast-unseal hA α∈Σ ok) (unsealʷ α A)
widening-between-genSafe-shapes () shapeB
    (C.cast-seq (C.cast-unseal hA α∈Σ ok) c⊢) (unseal︔_ α cʷ)

typed-gen-body-inert→genSafe :
  ∀ {μ : ModeEnv} {Δ Σ A B c} →
  genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ ⇑ᵗ A =⇒ B →
  occurs zero B ≡ true →
  Narrowing c →
  Inert c →
  GenSafe c
typed-gen-body-inert→genSafe c⊢ occ narrowing inert
    with narrowing-inert-view narrowing inert
typed-gen-body-inert→genSafe c⊢ occ narrowing inert | inj₁ safe = safe
typed-gen-body-inert→genSafe c⊢ occ narrowing inert
    | inj₂ (A , α , refl) =
  ⊥-elim (gen-body-seal⊥ c⊢ occ)
