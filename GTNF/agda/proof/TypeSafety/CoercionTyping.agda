module proof.TypeSafety.CoercionTyping where

-- File Charter:
--   * Connects a coercion typing derivation to its computed endpoints.
--   * Records that closing a shifted type at `★` restores that type.
--   * Proves that evidence-shaped coercion typing is preserved by closing
--     one ordinary type variable at `★`.

open import Data.Nat using (ℕ; zero; suc; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (map-++; length-map)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans; subst)

open import Types
open import proof.TypeSubst
open import Ctx
open import Coercion

lower-⇑ : (A : Ty) → lowerᵗ (⇑ᵗ A) ≡ A
lower-⇑ A =
  trans (rename-subst-commute suc (singleTyEnv ★) A)
        (trans (subst-cong (λ X → refl) A) (subst-id A))

mutual
  coercion-src : ∀ {Δ μ p A B}
    → Δ ∣ μ ⊢ᵖ p ∶ A ⟹ B
    → srcᵖ p ≡ A
  coercion-src (⊢id a wA) = refl
  coercion-src (⊢tag g) = refl
  coercion-src (⊢tag-var tv mode ok) = refl
  coercion-src (⊢check g) = refl
  coercion-src (⊢check-var tv mode ok) = refl
  coercion-src (⊢fun ⊢p ⊢q) =
    cong₂ _⇒_ (coercion-trg ⊢p) (coercion-src ⊢q)
  coercion-src (⊢all ⊢p) = cong `∀ (coercion-src ⊢p)
  coercion-src (⊢inst ⊢p wB nv occ ns) = cong `∀ (coercion-src ⊢p)
  coercion-src {p = genᵖ p} (⊢gen ⊢p wA nv occ ns safe) =
    trans (cong lowerᵗ (coercion-src ⊢p)) (lower-⇑ _)
  coercion-src (⊢seq-tag ⊢p tg ns) = coercion-src ⊢p
  coercion-src (⊢seq-check cg ⊢p ns) = refl
  coercion-src ⊢bot-elim = refl
  coercion-src ⊢bot-intro = refl

  coercion-trg : ∀ {Δ μ p A B}
    → Δ ∣ μ ⊢ᵖ p ∶ A ⟹ B
    → trgᵖ p ≡ B
  coercion-trg (⊢id a wA) = refl
  coercion-trg (⊢tag g) = refl
  coercion-trg (⊢tag-var tv mode ok) = refl
  coercion-trg (⊢check g) = refl
  coercion-trg (⊢check-var tv mode ok) = refl
  coercion-trg (⊢fun ⊢p ⊢q) =
    cong₂ _⇒_ (coercion-src ⊢p) (coercion-trg ⊢q)
  coercion-trg (⊢all ⊢p) = cong `∀ (coercion-trg ⊢p)
  coercion-trg {p = instᵖ p} (⊢inst ⊢p wB nv occ ns) =
    trans (cong lowerᵗ (coercion-trg ⊢p)) (lower-⇑ _)
  coercion-trg (⊢gen ⊢p wA nv occ ns safe) =
    cong `∀ (coercion-trg ⊢p)
  coercion-trg (⊢seq-tag ⊢p tg ns) = refl
  coercion-trg (⊢seq-check cg ⊢p ns) = coercion-trg ⊢p
  coercion-trg ⊢bot-elim = refl
  coercion-trg ⊢bot-intro = refl

------------------------------------------------------------------------
-- Closing support
------------------------------------------------------------------------

underN : ℕ → Ctxᵗ → Ctxᵗ
underN zero    Δ = Δ
underN (suc k) Δ = underΛ (underN k Δ)

shiftReps-lookup⁻ : ∀ {η X α}
  → shiftReps η ∋ˡ X := α
  → ∃[ β ] ((α ≡ suc β) × (η ∋ˡ X := β))
shiftReps-lookup⁻ {η = []} ()
shiftReps-lookup⁻ {η = β ∷ η} here = β , refl , here
shiftReps-lookup⁻ {η = β ∷ η} (there d) with shiftReps-lookup⁻ d
shiftReps-lookup⁻ {η = β ∷ η} (there d) | α′ , refl , d′ =
  α′ , refl , there d′

underΛ-tv-zero : ∀ {Δ} → underΛ Δ ∋tv zero
underΛ-tv-zero = zero , here

underΛ-tv-suc : ∀ {Δ X} → Δ ∋tv X → underΛ Δ ∋tv suc X
underΛ-tv-suc (α , d) = suc α , there (map-lookup-suc d)
  where
  map-lookup-suc : ∀ {η X α}
    → η ∋ˡ X := α
    → shiftReps η ∋ˡ X := suc α
  map-lookup-suc here = here
  map-lookup-suc (there d) = there (map-lookup-suc d)

underΛ-tv-tail : ∀ {Δ X} → underΛ Δ ∋tv suc X → Δ ∋tv X
underΛ-tv-tail (α , there d) with shiftReps-lookup⁻ d
underΛ-tv-tail (α , there d) | β , refl , d′ = β , d′

WfRen : Ctxᵗ → Ctxᵗ → Renameᵗ → Set
WfRen Δ Δ′ ρ = ∀ {X} → Δ ∋tv X → Δ′ ∋tv ρ X

WfRen-ext : ∀ {Δ Δ′ ρ}
  → WfRen Δ Δ′ ρ
  → WfRen (underΛ Δ) (underΛ Δ′) (extᵗ ρ)
WfRen-ext {Δ = Δ} {Δ′ = Δ′} h {zero} tv = underΛ-tv-zero {Δ = Δ′}
WfRen-ext {Δ = Δ} {Δ′ = Δ′} h {suc X} tv =
  underΛ-tv-suc {Δ = Δ′} (h (underΛ-tv-tail {Δ = Δ} tv))

wf-ren : ∀ {Δ Δ′ ρ A}
  → WfRen Δ Δ′ ρ
  → Δ ⊢ᵗ A
  → Δ′ ⊢ᵗ renameᵗ ρ A
wf-ren h (wf-var tv) = wf-var (h tv)
wf-ren h wf-ℕ = wf-ℕ
wf-ren h wf-𝔹 = wf-𝔹
wf-ren h wf-★ = wf-★
wf-ren h (wf-⇒ wA wB) = wf-⇒ (wf-ren h wA) (wf-ren h wB)
wf-ren {Δ = Δ} {Δ′ = Δ′} {ρ = ρ} {A = `∀ A} h (wf-∀ wA) =
  wf-∀ (wf-ren {Δ = underΛ Δ} {Δ′ = underΛ Δ′}
          {ρ = extᵗ ρ} {A = A}
          (WfRen-ext {Δ = Δ} {Δ′ = Δ′} {ρ = ρ} h) wA)

wf-shift : ∀ {Δ A} → Δ ⊢ᵗ A → underΛ Δ ⊢ᵗ ⇑ᵗ A
wf-shift {Δ = Δ} = wf-ren (underΛ-tv-suc {Δ = Δ})

close-var-wf : ∀ (k) {Δ X}
  → underN k (underΛ Δ) ∋tv X
  → underN k Δ ⊢ᵗ closeEnv k X
close-var-wf zero {X = zero} tv = wf-★
close-var-wf zero {Δ = Δ} {X = suc X} tv =
  wf-var (underΛ-tv-tail {Δ = Δ} tv)
close-var-wf (suc k) {Δ = Δ} {X = zero} tv =
  wf-var (underΛ-tv-zero {Δ = underN k Δ})
close-var-wf (suc k) {Δ = Δ} {X = suc X} tv =
  wf-shift (close-var-wf k
    (underΛ-tv-tail {Δ = underN k (underΛ Δ)} tv))

wf-close : ∀ (k) {Δ A}
  → underN k (underΛ Δ) ⊢ᵗ A
  → underN k Δ ⊢ᵗ closeTy k A
wf-close k (wf-var tv) = close-var-wf k tv
wf-close k wf-ℕ = wf-ℕ
wf-close k wf-𝔹 = wf-𝔹
wf-close k wf-★ = wf-★
wf-close k (wf-⇒ wA wB) = wf-⇒ (wf-close k wA) (wf-close k wB)
wf-close k (wf-∀ wA) = wf-∀ (wf-close (suc k) wA)

close-⇑ : ∀ k A → closeTy (suc k) (⇑ᵗ A) ≡ ⇑ᵗ (closeTy k A)
close-⇑ k A =
  trans (rename-subst-commute suc (closeEnv (suc k)) A)
        (trans (subst-cong (λ X → refl) A)
               (sym (rename-subst suc (closeEnv k) A)))

nonvar-occurs-nonstar : ∀ {X A}
  → NonVar A
  → X ∈ᵗ A
  → NonStar A
nonvar-occurs-nonstar nv-ℕ ()
nonvar-occurs-nonstar nv-𝔹 ()
nonvar-occurs-nonstar nv-★ ()
nonvar-occurs-nonstar nv-⇒ occ = ns-⇒
nonvar-occurs-nonstar nv-∀ occ = ns-∀

nonstar-nonvar-to-var-impossible : ∀ {Δ μ p A X}
  → Δ ∣ μ ⊢ᵖ p ∶ A ⟹ ` X
  → NonVar A
  → NonStar A
  → ⊥
nonstar-nonvar-to-var-impossible (⊢id a wA) () ns
nonstar-nonvar-to-var-impossible (⊢check-var tv mode ok) nv-★ ()
nonstar-nonvar-to-var-impossible
    (⊢inst ⊢p wB nvA occ nsB) nv-∀ ns =
  nonstar-nonvar-to-var-impossible ⊢p nvA
    (nonvar-occurs-nonstar nvA occ)
nonstar-nonvar-to-var-impossible (⊢seq-check cg ⊢p nsB) nv-★ ()

inst-to-var-occurs-impossible : ∀ {Δ μ p A X}
  → Δ ∣ μ ⊢ᵖ p ∶ A ⟹ ` X
  → NonVar A
  → zero ∈ᵗ A
  → ⊥
inst-to-var-occurs-impossible ⊢p nvA occ =
  nonstar-nonvar-to-var-impossible ⊢p nvA
    (nonvar-occurs-nonstar nvA occ)

var-to-nonstar-nonvar-impossible : ∀ {Δ μ p B X}
  → Δ ∣ μ ⊢ᵖ p ∶ ` X ⟹ B
  → NonVar B
  → NonStar B
  → ⊥
var-to-nonstar-nonvar-impossible (⊢id a wA) () ns
var-to-nonstar-nonvar-impossible (⊢tag-var tv mode ok) nv-★ ()
var-to-nonstar-nonvar-impossible
    (⊢gen ⊢p wA nvB occ nsA safe) nv-∀ ns =
  var-to-nonstar-nonvar-impossible ⊢p nvB
    (nonvar-occurs-nonstar nvB occ)
var-to-nonstar-nonvar-impossible (⊢seq-tag ⊢p tg nsA) nv-★ ()

gen-from-var-occurs-impossible : ∀ {Δ μ p B X}
  → Δ ∣ μ ⊢ᵖ p ∶ ` X ⟹ B
  → NonVar B
  → zero ∈ᵗ B
  → ⊥
gen-from-var-occurs-impossible ⊢p nvB occ =
  var-to-nonstar-nonvar-impossible ⊢p nvB
    (nonvar-occurs-nonstar nvB occ)

coercion-var-to-var : ∀ {Δ μ p X Y}
  → Δ ∣ μ ⊢ᵖ p ∶ ` X ⟹ ` Y
  → X ≡ Y
coercion-var-to-var (⊢id a wA) = refl

close-nonvar : ∀ k {A} → NonVar A → NonVar (closeTy k A)
close-nonvar k nv-ℕ = nv-ℕ
close-nonvar k nv-𝔹 = nv-𝔹
close-nonvar k nv-★ = nv-★
close-nonvar k nv-⇒ = nv-⇒
close-nonvar k nv-∀ = nv-∀

close-nonstar-nonvar : ∀ k {A}
  → NonVar A
  → NonStar A
  → NonStar (closeTy k A)
close-nonstar-nonvar k nv-ℕ ns-ℕ = ns-ℕ
close-nonstar-nonvar k nv-𝔹 ns-𝔹 = ns-𝔹
close-nonstar-nonvar k nv-⇒ ns-⇒ = ns-⇒
close-nonstar-nonvar k nv-∀ ns-∀ = ns-∀

closeEnv-hit : ∀ k → closeEnv k k ≡ ★
closeEnv-hit zero = refl
closeEnv-hit (suc k) = cong ⇑ᵗ (closeEnv-hit k)

closeEnv-miss-zero : ∀ X → closeEnv zero (suc X) ≡ ` X
closeEnv-miss-zero X = refl

closeTag-hit : ∀ k → closeTag k (` k) ≡ idᵖ ★
closeTag-hit k with k ≟ k
closeTag-hit k | yes refl = refl
closeTag-hit k | no ne = ⊥-elim (ne refl)

closeTag-miss : ∀ {k X} → k ≢ X
  → closeTag k (` X) ≡ closeTy k (` X) !
closeTag-miss {k} {X} ne with k ≟ X
closeTag-miss ne | yes eq = ⊥-elim (ne eq)
closeTag-miss ne | no neq = refl

closeCheck-hit : ∀ k ℓ → closeCheck k (` k) ℓ ≡ idᵖ ★
closeCheck-hit k ℓ with k ≟ k
closeCheck-hit k ℓ | yes refl = refl
closeCheck-hit k ℓ | no ne = ⊥-elim (ne refl)

closeCheck-miss : ∀ {k X ℓ} → k ≢ X
  → closeCheck k (` X) ℓ ≡ closeTy k (` X) ？ ℓ
closeCheck-miss {k} {X} {ℓ} ne with k ≟ X
closeCheck-miss ne | yes eq = ⊥-elim (ne eq)
closeCheck-miss ne | no neq = refl

closeSeqTag-hit : ∀ k p → closeSeqTag k p (` k) ≡ p
closeSeqTag-hit k p with k ≟ k
closeSeqTag-hit k p | yes refl = refl
closeSeqTag-hit k p | no ne = ⊥-elim (ne refl)

closeSeqTag-miss : ∀ {k X p} → k ≢ X
  → closeSeqTag k p (` X) ≡ p ︔ closeTy k (` X) !
closeSeqTag-miss {k} {X} {p} ne with k ≟ X
closeSeqTag-miss ne | yes eq = ⊥-elim (ne eq)
closeSeqTag-miss ne | no neq = refl

closeSeqCheck-hit : ∀ k ℓ p → closeSeqCheck k (` k) ℓ p ≡ p
closeSeqCheck-hit k ℓ p with k ≟ k
closeSeqCheck-hit k ℓ p | yes refl = refl
closeSeqCheck-hit k ℓ p | no ne = ⊥-elim (ne refl)

closeSeqCheck-miss : ∀ {k X ℓ p} → k ≢ X
  → closeSeqCheck k (` X) ℓ p ≡ closeTy k (` X) ？ ℓ ︔ p
closeSeqCheck-miss {k} {X} {ℓ} {p} ne with k ≟ X
closeSeqCheck-miss ne | yes eq = ⊥-elim (ne eq)
closeSeqCheck-miss ne | no neq = refl

data CloseVar (ν : List Mode) (Δ : Ctxᵗ) (μ : ModeEnv)
    (m : Mode) (X : ℕ) (n : Mode) : Set where
  cv-closed : length ν ≡ X → CloseVar ν Δ μ m X n
  cv-kept : ∀ {Y}
    → length ν ≢ X
    → closeEnv (length ν) X ≡ ` Y
    → underN (length ν) Δ ∋tv Y
    → (ν ++ μ) ∋ˡ Y := n
    → CloseVar ν Δ μ m X n

close-var : ∀ (ν : List Mode) {Δ μ m X n}
  → underN (length ν) (underΛ Δ) ∋tv X
  → (ν ++ m ∷ μ) ∋ˡ X := n
  → CloseVar ν Δ μ m X n
close-var [] {X = zero} tv here = cv-closed refl
close-var [] {Δ = Δ} {X = suc X} tv (there mode) =
  cv-kept (λ ()) (closeEnv-miss-zero X)
          (underΛ-tv-tail {Δ = Δ} tv) mode
close-var (n ∷ ν) {Δ = Δ} {X = zero} tv here =
  cv-kept (λ ()) refl (underΛ-tv-zero {Δ = underN (length ν) Δ}) here
close-var (n ∷ ν) {Δ = Δ} {μ = μ} {m = m} {X = suc X} tv (there mode)
    with close-var ν {Δ = Δ} {μ = μ} {m = m}
           (underΛ-tv-tail {Δ = underN (length ν) (underΛ Δ)} tv) mode
close-var (n ∷ ν) {Δ = Δ} {μ = μ} {m = m} {X = suc X}
    tv (there mode) | cv-closed eq =
  cv-closed (cong suc eq)
close-var (n ∷ ν) {Δ = Δ} {μ = μ} {m = m} {X = suc X} tv (there mode)
    | cv-kept ne eq tv′ mode′ =
  cv-kept (λ where refl → ne refl) (cong ⇑ᵗ eq)
          (underΛ-tv-suc {Δ = underN (length ν) Δ} tv′) (there mode′)

close-tag-var : ∀ (ν : List Mode) {Δ μ m X n}
  → underN (length ν) (underΛ Δ) ∋tv X
  → (ν ++ m ∷ μ) ∋ˡ X := n
  → TagOK n
  → underN (length ν) Δ ∣ ν ++ μ
      ⊢ᵖ closeTag (length ν) (` X) ∶ closeTy (length ν) (` X) ⟹ ★
close-tag-var ν tv mode ok with close-var ν tv mode
close-tag-var ν tv mode ok | cv-closed refl
  rewrite closeTag-hit (length ν) | closeEnv-hit (length ν) = ⊢id atom-★ wf-★
close-tag-var ν tv mode ok | cv-kept ne eq tv′ mode′
  rewrite closeTag-miss ne | eq = ⊢tag-var tv′ mode′ ok

close-check-var : ∀ (ν : List Mode) {Δ μ m X n ℓ}
  → underN (length ν) (underΛ Δ) ∋tv X
  → (ν ++ m ∷ μ) ∋ˡ X := n
  → CheckOK n
  → underN (length ν) Δ ∣ ν ++ μ
      ⊢ᵖ closeCheck (length ν) (` X) ℓ
        ∶ ★ ⟹ closeTy (length ν) (` X)
close-check-var ν tv mode ok with close-var ν tv mode
close-check-var ν {ℓ = ℓ} tv mode ok | cv-closed refl
  rewrite closeCheck-hit (length ν) ℓ | closeEnv-hit (length ν) =
  ⊢id atom-★ wf-★
close-check-var ν {ℓ = ℓ} tv mode ok | cv-kept ne eq tv′ mode′
  rewrite closeCheck-miss {ℓ = ℓ} ne | eq = ⊢check-var tv′ mode′ ok

ground-nonvar : ∀ {G} → GroundNV G → NonVar G
ground-nonvar g-ℕ = nv-ℕ
ground-nonvar g-𝔹 = nv-𝔹
ground-nonvar g-⇒ = nv-⇒
ground-nonvar g-∀ = nv-∀

ground-nonstar : ∀ {G} → GroundNV G → NonStar G
ground-nonstar g-ℕ = ns-ℕ
ground-nonstar g-𝔹 = ns-𝔹
ground-nonstar g-⇒ = ns-⇒
ground-nonstar g-∀ = ns-∀

close-tag-ground : ∀ k {Δ μ G}
  → GroundNV G
  → Δ ∣ μ ⊢ᵖ closeTag k G ∶ closeTy k G ⟹ ★
close-tag-ground k g-ℕ = ⊢tag g-ℕ
close-tag-ground k g-𝔹 = ⊢tag g-𝔹
close-tag-ground k g-⇒ = ⊢tag g-⇒
close-tag-ground k g-∀ = ⊢tag g-∀

close-check-ground : ∀ k {Δ μ G ℓ}
  → GroundNV G
  → Δ ∣ μ ⊢ᵖ closeCheck k G ℓ ∶ ★ ⟹ closeTy k G
close-check-ground k g-ℕ = ⊢check g-ℕ
close-check-ground k g-𝔹 = ⊢check g-𝔹
close-check-ground k g-⇒ = ⊢check g-⇒
close-check-ground k g-∀ = ⊢check g-∀

closeEnv-var-miss : ∀ {k X}
  → k ≢ X
  → ∃[ Y ] closeEnv k X ≡ ` Y
closeEnv-var-miss {zero} {zero} ne = ⊥-elim (ne refl)
closeEnv-var-miss {zero} {suc X} ne = X , refl
closeEnv-var-miss {suc k} {zero} ne = zero , refl
closeEnv-var-miss {suc k} {suc X} ne
    with closeEnv-var-miss (λ eq → ne (cong suc eq))
closeEnv-var-miss {suc k} {suc X} ne | Y , eq = suc Y , cong ⇑ᵗ eq

close-nonstar-var-miss : ∀ {k X}
  → k ≢ X
  → NonStar (closeEnv k X)
close-nonstar-var-miss ne with closeEnv-var-miss ne
close-nonstar-var-miss ne | Y , eq = subst NonStar (sym eq) ns-var

close-source-nonstar-ground : ∀ k {Δ μ p A G}
  → Δ ∣ μ ⊢ᵖ p ∶ A ⟹ G
  → GroundNV G
  → NonStar A
  → NonStar (closeTy k A)
close-source-nonstar-ground k {A = ` X} ⊢p g ns-var =
  ⊥-elim (var-to-nonstar-nonvar-impossible ⊢p
            (ground-nonvar g) (ground-nonstar g))
close-source-nonstar-ground k {A = `ℕ} ⊢p g ns-ℕ = ns-ℕ
close-source-nonstar-ground k {A = `𝔹} ⊢p g ns-𝔹 = ns-𝔹
close-source-nonstar-ground k {A = A ⇒ B} ⊢p g ns-⇒ = ns-⇒
close-source-nonstar-ground k {A = `∀ A} ⊢p g ns-∀ = ns-∀

close-target-nonstar-ground : ∀ k {Δ μ p B G}
  → Δ ∣ μ ⊢ᵖ p ∶ G ⟹ B
  → GroundNV G
  → NonStar B
  → NonStar (closeTy k B)
close-target-nonstar-ground k {B = ` X} ⊢p g ns-var =
  ⊥-elim (nonstar-nonvar-to-var-impossible ⊢p
            (ground-nonvar g) (ground-nonstar g))
close-target-nonstar-ground k {B = `ℕ} ⊢p g ns-ℕ = ns-ℕ
close-target-nonstar-ground k {B = `𝔹} ⊢p g ns-𝔹 = ns-𝔹
close-target-nonstar-ground k {B = A ⇒ B} ⊢p g ns-⇒ = ns-⇒
close-target-nonstar-ground k {B = `∀ B} ⊢p g ns-∀ = ns-∀

close-source-nonstar-kept : ∀ k {Δ μ p A X}
  → Δ ∣ μ ⊢ᵖ p ∶ A ⟹ ` X
  → k ≢ X
  → NonStar A
  → NonStar (closeTy k A)
close-source-nonstar-kept k {A = ` Y} ⊢p X-kept ns-var with k ≟ Y
close-source-nonstar-kept k {A = ` Y} ⊢p X-kept ns-var | yes refl =
  ⊥-elim (X-kept (coercion-var-to-var ⊢p))
close-source-nonstar-kept k {A = ` Y} ⊢p X-kept ns-var | no Y-kept =
  close-nonstar-var-miss Y-kept
close-source-nonstar-kept k {A = `ℕ} ⊢p X-kept ns-ℕ = ns-ℕ
close-source-nonstar-kept k {A = `𝔹} ⊢p X-kept ns-𝔹 = ns-𝔹
close-source-nonstar-kept k {A = A ⇒ B} ⊢p X-kept ns-⇒ = ns-⇒
close-source-nonstar-kept k {A = `∀ A} ⊢p X-kept ns-∀ = ns-∀

close-target-nonstar-kept : ∀ k {Δ μ p B X}
  → Δ ∣ μ ⊢ᵖ p ∶ ` X ⟹ B
  → k ≢ X
  → NonStar B
  → NonStar (closeTy k B)
close-target-nonstar-kept k {B = ` Y} ⊢p X-kept ns-var with k ≟ Y
close-target-nonstar-kept k {B = ` Y} ⊢p X-kept ns-var | yes eq =
  ⊥-elim (X-kept (trans eq (sym (coercion-var-to-var ⊢p))))
close-target-nonstar-kept k {B = ` Y} ⊢p X-kept ns-var | no Y-kept =
  close-nonstar-var-miss Y-kept
close-target-nonstar-kept k {B = `ℕ} ⊢p X-kept ns-ℕ = ns-ℕ
close-target-nonstar-kept k {B = `𝔹} ⊢p X-kept ns-𝔹 = ns-𝔹
close-target-nonstar-kept k {B = A ⇒ B} ⊢p X-kept ns-⇒ = ns-⇒
close-target-nonstar-kept k {B = `∀ B} ⊢p X-kept ns-∀ = ns-∀

close-seq-tag-ground : ∀ k {Δ μ p A G}
  → GroundNV G
  → Δ ∣ μ ⊢ᵖ p ∶ closeTy k A ⟹ closeTy k G
  → NonStar (closeTy k A)
  → Δ ∣ μ ⊢ᵖ closeSeqTag k p G ∶ closeTy k A ⟹ ★
close-seq-tag-ground k g-ℕ ⊢p ns = ⊢seq-tag ⊢p (tg-nv g-ℕ) ns
close-seq-tag-ground k g-𝔹 ⊢p ns = ⊢seq-tag ⊢p (tg-nv g-𝔹) ns
close-seq-tag-ground k g-⇒ ⊢p ns = ⊢seq-tag ⊢p (tg-nv g-⇒) ns
close-seq-tag-ground k g-∀ ⊢p ns = ⊢seq-tag ⊢p (tg-nv g-∀) ns

close-seq-check-ground : ∀ k {Δ μ p B G ℓ}
  → GroundNV G
  → Δ ∣ μ ⊢ᵖ p ∶ closeTy k G ⟹ closeTy k B
  → NonStar (closeTy k B)
  → Δ ∣ μ ⊢ᵖ closeSeqCheck k G ℓ p ∶ ★ ⟹ closeTy k B
close-seq-check-ground k g-ℕ ⊢p ns = ⊢seq-check (cg-nv g-ℕ) ⊢p ns
close-seq-check-ground k g-𝔹 ⊢p ns = ⊢seq-check (cg-nv g-𝔹) ⊢p ns
close-seq-check-ground k g-⇒ ⊢p ns = ⊢seq-check (cg-nv g-⇒) ⊢p ns
close-seq-check-ground k g-∀ ⊢p ns = ⊢seq-check (cg-nv g-∀) ⊢p ns

occurs-close-before : ∀ {X k A}
  → X < k
  → X ∈ᵗ A
  → X ∈ᵗ closeTy k A
occurs-close-before lt ∈-var =
  subst (λ A → _ ∈ᵗ A) (sym (closeEnv-before lt)) ∈-var
  where
  closeEnv-before : ∀ {X k} → X < k → closeEnv k X ≡ ` X
  closeEnv-before {zero} {zero} ()
  closeEnv-before {zero} {suc k} lt = refl
  closeEnv-before {suc X} {zero} ()
  closeEnv-before {suc X} {suc k} (s≤s lt) =
    cong ⇑ᵗ (closeEnv-before lt)
occurs-close-before lt (∈-⇒ˡ occ) = ∈-⇒ˡ (occurs-close-before lt occ)
occurs-close-before lt (∈-⇒ʳ occ) = ∈-⇒ʳ (occurs-close-before lt occ)
occurs-close-before lt (∈-∀ occ) =
  ∈-∀ (occurs-close-before (s≤s lt) occ)

occurs-zero-close : ∀ k {A}
  → zero ∈ᵗ A
  → zero ∈ᵗ closeTy (suc k) A
occurs-zero-close k = occurs-close-before {X = zero} {k = suc k}
  (s≤s z≤n)

close-genSafe : ∀ k {p} → GenSafe p → GenSafe (closeᵖ k p)
close-genSafe k safe-↦ = safe-↦
close-genSafe k safe-∀ = safe-∀
close-genSafe k safe-inst = safe-inst
close-genSafe k (safe-gen safe) = safe-gen (close-genSafe (suc k) safe)

coercion-typing-cast : ∀ {Δ Δ′ μ μ′ p p′ A A′ B B′}
  → Δ ≡ Δ′
  → μ ≡ μ′
  → p ≡ p′
  → A ≡ A′
  → B ≡ B′
  → Δ ∣ μ ⊢ᵖ p ∶ A ⟹ B
  → Δ′ ∣ μ′ ⊢ᵖ p′ ∶ A′ ⟹ B′
coercion-typing-cast refl refl refl refl refl ⊢p = ⊢p

------------------------------------------------------------------------
-- Closing preserves coercion typing
------------------------------------------------------------------------

closeᵖ-typing-under : ∀ (ν : List Mode) {Δ μ m p A B}
  → underN (length ν) (underΛ Δ) ∣ ν ++ m ∷ μ ⊢ᵖ p ∶ A ⟹ B
  → underN (length ν) Δ ∣ ν ++ μ
      ⊢ᵖ closeᵖ (length ν) p
        ∶ closeTy (length ν) A ⟹ closeTy (length ν) B
closeᵖ-typing-under ν (⊢id a wA) = ⊢id (atom-close (length ν) a) (wf-close (length ν) wA)
closeᵖ-typing-under ν (⊢tag g) = close-tag-ground (length ν) g
closeᵖ-typing-under ν (⊢tag-var tv mode ok) =
  close-tag-var ν tv mode ok
closeᵖ-typing-under ν (⊢check g) = close-check-ground (length ν) g
closeᵖ-typing-under ν (⊢check-var tv mode ok) =
  close-check-var ν tv mode ok
closeᵖ-typing-under ν {Δ = Δ} {μ = μ} {m = m}
    (⊢fun {p = p} {A′ = A′} {A = A} ⊢p ⊢q) =
  ⊢fun closed-domain (closeᵖ-typing-under ν ⊢q)
  where
  len-eq : length (map flipᵐ ν) ≡ length ν
  len-eq = length-map flipᵐ ν

  source-mode-eq : flipEnv (ν ++ m ∷ μ)
    ≡ map flipᵐ ν ++ flipᵐ m ∷ flipEnv μ
  source-mode-eq = map-++ flipᵐ ν (m ∷ μ)

  target-mode-eq : map flipᵐ ν ++ flipEnv μ ≡ flipEnv (ν ++ μ)
  target-mode-eq = sym (map-++ flipᵐ ν μ)

  domain-source : underN (length (map flipᵐ ν)) (underΛ Δ)
      ∣ map flipᵐ ν ++ flipᵐ m ∷ flipEnv μ ⊢ᵖ p ∶ A′ ⟹ A
  domain-source =
    coercion-typing-cast
      (cong (λ k → underN k (underΛ Δ)) (sym len-eq))
      source-mode-eq refl refl refl ⊢p

  domain-closed = closeᵖ-typing-under (map flipᵐ ν) domain-source

  closed-domain : underN (length ν) Δ ∣ flipEnv (ν ++ μ)
      ⊢ᵖ closeᵖ (length ν) p
        ∶ closeTy (length ν) A′ ⟹ closeTy (length ν) A
  closed-domain =
    coercion-typing-cast
      (cong (λ k → underN k Δ) len-eq)
      target-mode-eq
      (cong (λ k → closeᵖ k p) len-eq)
      (cong (λ k → closeTy k A′) len-eq)
      (cong (λ k → closeTy k A) len-eq)
      domain-closed
closeᵖ-typing-under ν (⊢all ⊢p) =
  ⊢all (closeᵖ-typing-under (X∼X ∷ ν) ⊢p)
closeᵖ-typing-under ν (⊢inst {B = ` X} ⊢p wB nvA occ nsB) =
  ⊥-elim (inst-to-var-occurs-impossible ⊢p nvA occ)
closeᵖ-typing-under ν (⊢inst {B = `ℕ} ⊢p wB nvA occ nsB) =
  ⊢inst aligned-p
        (wf-close (length ν) wB) (close-nonvar (suc (length ν)) nvA)
        (occurs-zero-close (length ν) occ) ns-ℕ
  where
  closed-p = closeᵖ-typing-under (X∼★ ∷ ν) ⊢p
  aligned-p = coercion-typing-cast refl refl refl refl
                (close-⇑ (length ν) `ℕ) closed-p
closeᵖ-typing-under ν (⊢inst {B = `𝔹} ⊢p wB nvA occ nsB) =
  ⊢inst aligned-p
        (wf-close (length ν) wB) (close-nonvar (suc (length ν)) nvA)
        (occurs-zero-close (length ν) occ) ns-𝔹
  where
  closed-p = closeᵖ-typing-under (X∼★ ∷ ν) ⊢p
  aligned-p = coercion-typing-cast refl refl refl refl
                (close-⇑ (length ν) `𝔹) closed-p
closeᵖ-typing-under ν (⊢inst {B = B ⇒ C} ⊢p wB nvA occ nsB) =
  ⊢inst aligned-p
        (wf-close (length ν) wB) (close-nonvar (suc (length ν)) nvA)
        (occurs-zero-close (length ν) occ) ns-⇒
  where
  closed-p = closeᵖ-typing-under (X∼★ ∷ ν) ⊢p
  aligned-p = coercion-typing-cast refl refl refl refl
                (close-⇑ (length ν) (B ⇒ C)) closed-p
closeᵖ-typing-under ν (⊢inst {B = `∀ B} ⊢p wB nvA occ nsB) =
  ⊢inst aligned-p
        (wf-close (length ν) wB) (close-nonvar (suc (length ν)) nvA)
        (occurs-zero-close (length ν) occ) ns-∀
  where
  closed-p = closeᵖ-typing-under (X∼★ ∷ ν) ⊢p
  aligned-p = coercion-typing-cast refl refl refl refl
                (close-⇑ (length ν) (`∀ B)) closed-p
closeᵖ-typing-under ν (⊢gen {A = ` X} ⊢p wA nvB occ nsA safe) =
  ⊥-elim (gen-from-var-occurs-impossible ⊢p nvB occ)
closeᵖ-typing-under ν (⊢gen {A = `ℕ} ⊢p wA nvB occ nsA safe) =
  ⊢gen aligned-p
       (wf-close (length ν) wA) (close-nonvar (suc (length ν)) nvB)
       (occurs-zero-close (length ν) occ) ns-ℕ
       (close-genSafe (suc (length ν)) safe)
  where
  closed-p = closeᵖ-typing-under (★∼X ∷ ν) ⊢p
  aligned-p = coercion-typing-cast refl refl refl
                (close-⇑ (length ν) `ℕ) refl closed-p
closeᵖ-typing-under ν (⊢gen {A = `𝔹} ⊢p wA nvB occ nsA safe) =
  ⊢gen aligned-p
       (wf-close (length ν) wA) (close-nonvar (suc (length ν)) nvB)
       (occurs-zero-close (length ν) occ) ns-𝔹
       (close-genSafe (suc (length ν)) safe)
  where
  closed-p = closeᵖ-typing-under (★∼X ∷ ν) ⊢p
  aligned-p = coercion-typing-cast refl refl refl
                (close-⇑ (length ν) `𝔹) refl closed-p
closeᵖ-typing-under ν (⊢gen {A = B ⇒ C} ⊢p wA nvB occ nsA safe) =
  ⊢gen aligned-p
       (wf-close (length ν) wA) (close-nonvar (suc (length ν)) nvB)
       (occurs-zero-close (length ν) occ) ns-⇒
       (close-genSafe (suc (length ν)) safe)
  where
  closed-p = closeᵖ-typing-under (★∼X ∷ ν) ⊢p
  aligned-p = coercion-typing-cast refl refl refl
                (close-⇑ (length ν) (B ⇒ C)) refl closed-p
closeᵖ-typing-under ν (⊢gen {A = `∀ A} ⊢p wA nvB occ nsA safe) =
  ⊢gen aligned-p
       (wf-close (length ν) wA) (close-nonvar (suc (length ν)) nvB)
       (occurs-zero-close (length ν) occ) ns-∀
       (close-genSafe (suc (length ν)) safe)
  where
  closed-p = closeᵖ-typing-under (★∼X ∷ ν) ⊢p
  aligned-p = coercion-typing-cast refl refl refl
                (close-⇑ (length ν) (`∀ A)) refl closed-p
closeᵖ-typing-under ν (⊢seq-tag {A = A} ⊢p (tg-nv g) nsA) =
  close-seq-tag-ground (length ν) {A = A} g
    (closeᵖ-typing-under ν ⊢p)
    (close-source-nonstar-ground (length ν) {A = A} ⊢p g nsA)
closeᵖ-typing-under ν
    (⊢seq-tag {p = p} ⊢p (tg-var {X = X} tv mode ok) nsA)
    with close-var ν tv mode
closeᵖ-typing-under ν
    (⊢seq-tag {p = p} ⊢p (tg-var {X = X} tv mode ok) nsA)
    | cv-closed refl
    rewrite closeSeqTag-hit (length ν) (closeᵖ (length ν) p) =
  coercion-typing-cast refl refl refl refl (closeEnv-hit (length ν))
    (closeᵖ-typing-under ν ⊢p)
closeᵖ-typing-under ν
    (⊢seq-tag {p = p} ⊢p (tg-var {X = X} tv mode ok) nsA)
    | cv-kept {Y} ne eq tv′ mode′
    rewrite closeSeqTag-miss {p = closeᵖ (length ν) p} ne =
  ⊢seq-tag (closeᵖ-typing-under ν ⊢p)
    (subst (TagGround _ _) (sym eq) (tg-var tv′ mode′ ok))
    (close-source-nonstar-kept (length ν) ⊢p ne nsA)
closeᵖ-typing-under ν (⊢seq-check {B = B} (cg-nv g) ⊢p nsB) =
  close-seq-check-ground (length ν) {B = B} g
    (closeᵖ-typing-under ν ⊢p)
    (close-target-nonstar-ground (length ν) {B = B} ⊢p g nsB)
closeᵖ-typing-under ν
    (⊢seq-check {p = p} {ℓ = ℓ} (cg-var {X = X} tv mode ok) ⊢p nsB)
    with close-var ν tv mode
closeᵖ-typing-under ν
    (⊢seq-check {p = p} {ℓ = ℓ} (cg-var {X = X} tv mode ok) ⊢p nsB)
    | cv-closed refl
    rewrite closeSeqCheck-hit (length ν) ℓ (closeᵖ (length ν) p) =
  coercion-typing-cast refl refl refl (closeEnv-hit (length ν)) refl
    (closeᵖ-typing-under ν ⊢p)
closeᵖ-typing-under ν
    (⊢seq-check {p = p} {ℓ = ℓ} (cg-var {X = X} tv mode ok) ⊢p nsB)
    | cv-kept {Y} ne eq tv′ mode′
    rewrite closeSeqCheck-miss {ℓ = ℓ} {p = closeᵖ (length ν) p} ne =
  ⊢seq-check
    (subst (CheckGround _ _) (sym eq) (cg-var tv′ mode′ ok))
    (closeᵖ-typing-under ν ⊢p)
    (close-target-nonstar-kept (length ν) ⊢p ne nsB)
closeᵖ-typing-under ν ⊢bot-elim = ⊢bot-elim
closeᵖ-typing-under ν ⊢bot-intro = ⊢bot-intro

closeᵖ-typing : ∀ {Δ μ m p A B}
  → underΛ Δ ∣ m ∷ μ ⊢ᵖ p ∶ A ⟹ B
  → Δ ∣ μ ⊢ᵖ closeᵖ zero p ∶ closeTy zero A ⟹ closeTy zero B
closeᵖ-typing = closeᵖ-typing-under []
