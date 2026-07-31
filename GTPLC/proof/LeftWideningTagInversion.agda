module proof.LeftWideningTagInversion where

-- File Charter:
--   * Inverts term narrowing whose left value has a widening tag.
--   * Uses a candidate untagged index and its composition equation.
--   * Excludes quotient-only counterexamples that have no untagged index.
--   * Depends on typed imprecision composition and term narrowing.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; cong; cong₂; refl; sym; trans)
open import Relation.Nullary using (yes; no)

open import Types
open import Coercions
open import Coercions using ()
  renaming (id to idᶜ; _︔_ to _︔ᶜ_; _↦_ to _↦ᶜ_)
open import Terms
open import NarrowWiden
open import EnvironmentNarrowing
open import ImprecisionTheorems using
  ( dualⁿ
  ; dualʷ
  ; LeftOneSidedᵢ
  ; RightOneSidedᵢ
  ; left-compose
  ; left-id-one-sidedᵢ
  ; right-compose
  ; right-id-one-sidedᵢ
  ; _⨟ⁿ[_]_
  ; _⨟ˡⁿ[_]_
  ; _≐ⁿ_
  )
open import TermNarrowing
open import proof.TermNarrowing using (castⁿ⊒castⁿ)
open import proof.ImprecisionComposition using
  ( _⨟ᵢ_⇒_
  ; both-both
  ; freshᴿ-both
  ; keepᴿ
  ; compose-id-left
  ; compose-right-star
  ; composeⁿ
  ; composeʷ
  ; fun-idⁿ
  ; recontext-from-funⁿ
  ; strip-tag★⇒★
  ; strip-untag★⇒★
  )

------------------------------------------------------------------------
-- Tag-prefix cancellation
------------------------------------------------------------------------

base-target-no-member :
    ∀ {Δᴸ Δᴿ c ι B X}
      {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ∣ Δᴸ ⊢ c ⦂ ‵ ι ⊒ B ⊣ Δᴿ
  → X ∈ᵗ B
  → ⊥
base-target-no-member
    (idᵃ (‵ ι) (‵ κ) hA hB refl) ()
base-target-no-member
    (gen nonvarA zero∈A p B≢★) (∈-all X∈) =
  base-target-no-member p X∈

no-star-to-function-widening :
    ∀ {Δᴸ Δᴿ c A B}
      {Φ : ImpCtx Δᴿ Δᴸ}
  → Φ ∣ Δᴸ ⊢ c ⦂ ★ ⊑ A ⇒ B ⊣ Δᴿ
  → ⊥
no-star-to-function-widening
    (idᵃ ★ () hA hB a⊑b)

no-function-to-star-narrowing :
    ∀ {Δᴸ Δᴿ c A B}
      {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⇒ B ⊒ ★ ⊣ Δᴿ
  → ⊥
no-function-to-star-narrowing
    (idᵃ () ★ hA hB a⊒b)

no-base-to-star-narrowing :
    ∀ {Δᴸ Δᴿ c ι}
      {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ∣ Δᴸ ⊢ c ⦂ ‵ ι ⊒ ★ ⊣ Δᴿ
  → ⊥
no-base-to-star-narrowing
    (idᵃ (‵ ι) ★ hA hB ())

no-base-to-function-narrowing :
    ∀ {Δᴸ Δᴿ c ι A B}
      {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ∣ Δᴸ ⊢ c ⦂ ‵ ι ⊒ A ⇒ B ⊣ Δᴿ
  → ⊥
no-base-to-function-narrowing
    (idᵃ (‵ ι) () hA hB a⊒b)

no-base-to-all-narrowing :
    ∀ {Δᴸ Δᴿ c ι A}
      {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ∣ Δᴸ ⊢ c ⦂ ‵ ι ⊒ `∀ A ⊣ Δᴿ
  → ⊥
no-base-to-all-narrowing
    (idᵃ (‵ ι) () hA hB a⊒b)
no-base-to-all-narrowing
    (gen nonvarA zero∈A p B≢★) =
  base-target-no-member p zero∈A

no-base-to-variable-narrowing :
    ∀ {Δᴸ Δᴿ c ι X}
      {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ∣ Δᴸ ⊢ c ⦂ ‵ ι ⊒ ＇ X ⊣ Δᴿ
  → ⊥
no-base-to-variable-narrowing
    (idᵃ (‵ ι) (＇ X) hA hB ())

no-function-to-base-narrowing :
    ∀ {Δᴸ Δᴿ c A B ι}
      {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⇒ B ⊒ ‵ ι ⊣ Δᴿ
  → ⊥
no-function-to-base-narrowing
    (idᵃ () (‵ ι) hA hB a⊒b)

no-function-to-variable-narrowing :
    ∀ {Δᴸ Δᴿ c A B X}
      {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⇒ B ⊒ ＇ X ⊣ Δᴿ
  → ⊥
no-function-to-variable-narrowing
    (idᵃ () (＇ X) hA hB a⊒b)

star-function-narrowing-coercion :
    ∀ {Δᴸ Δᴿ c}
      {Φ : ImpCtx Δᴸ Δᴿ}
  → Φ ∣ Δᴸ ⊢ c ⦂ (★ ⇒ ★) ⊒ (★ ⇒ ★) ⊣ Δᴿ
  → c ≡ idᶜ ↦ᶜ idᶜ
star-function-narrowing-coercion
    (idᵃ ★ ★ hA hB a⊒b ↦ idᵃ ★ ★ hA′ hB′ a⊒b′) =
  refl
star-function-narrowing-coercion
    ((p ︔tag★⇒★[ A≢★⇒★ ]) ↦ q) =
  ⊥-elim (no-star-to-function-widening p)
star-function-narrowing-coercion
    (p ↦ untag★⇒★︔ q [ ★⇒★≢B ]) =
  ⊥-elim (no-function-to-star-narrowing q)

sequence-tail-injective : ∀ {a b c}
  → a ︔ᶜ b ≡ a ︔ᶜ c
  → b ≡ c
sequence-tail-injective refl = refl

sequence-head-injective : ∀ {a b c}
  → a ︔ᶜ c ≡ b ︔ᶜ c
  → a ≡ b
sequence-head-injective refl = refl

star-left-identity-composition :
    ∀ {Δᴸ Δᴿ B}
      {Φ : ImpCtx Δᴸ Δᴿ}
      (i : Φ ∣ Δᴸ ⊢ idᶜ ⦂ ★ ⊒ ★ ⊣ Δᴿ)
      (q : idᵢ Δᴿ ∣ Δᴿ ⊢ ★ ⊒ B ⊣ Δᴿ)
  → proj₁ ((idᶜ , i) ⨟ⁿ[ right-id-one-sidedᵢ ] q) ≡ proj₁ q
star-left-identity-composition
    (idᵃ ★ ★ hA hB a⊒b)
    (_ , idᵃ ★ ★ hA′ hB′ a⊒b′) =
  refl
star-left-identity-composition
    (idᵃ ★ ★ hA hB a⊒b)
    (_ , untag ι) =
  refl
star-left-identity-composition
    (idᵃ ★ ★ hA hB a⊒b)
    (_ , untag★⇒★) =
  refl
star-left-identity-composition
    (idᵃ ★ ★ hA hB a⊒b)
    (_ , untag★⇒★︔ q [ ★⇒★≢B ]) =
  refl
star-left-identity-composition
    (idᵃ ★ ★ hA hB a⊒b)
    (_ , seal X⊑★) =
  refl
star-left-identity-composition
    (idᵃ ★ ★ hA hB a⊒b)
    (_ , q ︔seal X⊑★ [ ★≢B ]) =
  refl
star-left-identity-composition
    (idᵃ ★ ★ hA hB a⊒b)
    (_ , gen nonvarA zero∈A q ★≢★) =
  ⊥-elim (★≢★ refl)

no-member-star : ∀ {X}
  → X ∈ᵗ ★
  → ⊥
no-member-star ()

no-member-star-function : ∀ {X}
  → X ∈ᵗ (★ ⇒ ★)
  → ⊥
no-member-star-function (∈-fun-left X∈) =
  no-member-star X∈
no-member-star-function (∈-fun-right X∈) =
  no-member-star X∈

member-not-star-function : ∀ {A X}
  → X ∈ᵗ A
  → (★ ⇒ ★) ≢ A
member-not-star-function X∈ refl =
  no-member-star-function X∈

function-tag-stripᶜ :
    ∀ {Δᴸ Δᴿ A c}
      {Φᴸ : ImpCtx Δᴸ Δᴿ}
      {Φᴵ : ImpCtx Δᴸ Δᴸ}
      {Φᴼ : ImpCtx Δᴸ Δᴿ}
      (comp : Φᴵ ⨟ᵢ Φᴸ ⇒ Φᴼ)
      (nonvarA : NonVar A)
      (zero∈A : zero ∈ᵗ A)
      (p : Φᴸ ∣ Δᴸ ⊢ c ⦂ (★ ⇒ ★) ⊒ A ⊣ Δᴿ)
  → proj₁
      (strip-untag★⇒★ nonvarA zero∈A
        (proj₂
          (composeⁿ comp (untag★⇒★ {Φ = Φᴵ}) p)))
      ≡ c
function-tag-stripᶜ {A = A ⇒ B} comp
    nonvar-fun zero∈A (p₁ ↦ p₂)
    with ★ ≟Ty A | ★ ≟Ty B
function-tag-stripᶜ comp nonvar-fun zero∈A (p₁ ↦ p₂)
    | yes refl | yes refl =
  ⊥-elim (no-member-star-function zero∈A)
function-tag-stripᶜ comp nonvar-fun zero∈A (p₁ ↦ p₂)
    | yes ★≡A | no ★≢B =
  refl
function-tag-stripᶜ comp nonvar-fun zero∈A (p₁ ↦ p₂)
    | no ★≢A | yes ★≡B =
  refl
function-tag-stripᶜ comp nonvar-fun zero∈A (p₁ ↦ p₂)
    | no ★≢A | no ★≢B =
  refl
function-tag-stripᶜ {Δᴸ = Δᴸ} comp
    nonvar-all (∈-all zero∈A)
    (gen nonvarA zero∈A′ p B≢★) =
  refl

function-tag-strip :
    ∀ {Δᴸ Δᴿ A c}
      {Φ : ImpCtx Δᴸ Δᴿ}
      (nonvarA : NonVar A)
      (zero∈A : zero ∈ᵗ A)
      (p : Φ ∣ Δᴸ ⊢ c ⦂ (★ ⇒ ★) ⊒ A ⊣ Δᴿ)
  → proj₁
      (strip-untag★⇒★ nonvarA zero∈A
        (proj₂
          (dualʷ (★⇒★ ! , tag★⇒★)
            ⨟ˡⁿ[ left-id-one-sidedᵢ ]
            (c , p))))
      ≡ c
function-tag-strip = function-tag-stripᶜ compose-id-left

function-tag-gen-composition :
    ∀ {Δᴸ Δᴿ A c}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {nonvarA : NonVar A}
      {zero∈A : zero ∈ᵗ A}
      {p : freshᴿ Φ ∣ Δᴸ
        ⊢ c ⦂ (★ ⇒ ★) ⊒ A ⊣ suc Δᴿ}
      {B≢★ : (★ ⇒ ★) ≢ ★}
  → proj₁
      (dualʷ (★⇒★ ! , tag★⇒★)
        ⨟ˡⁿ[ left-id-one-sidedᵢ ]
        (Coercions.gen c ,
          gen nonvarA zero∈A p {{freshⁿᵢ}} B≢★))
      ≡ (★⇒★ ？) ︔ᶜ Coercions.gen c
function-tag-gen-composition
    {nonvarA = nonvarA} {zero∈A = zero∈A}
    {p = p₁ ↦ p₂} =
  refl
function-tag-gen-composition
    {nonvarA = nonvar-all} {zero∈A = ∈-all zero∈A}
    {p = gen nonvarA zero∈A′ p B≢★} =
  refl

function-tag-gen-compositionᶜ :
    ∀ {Δᴸ Δᴿ A c}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {Ψ : ImpCtx Δᴸ Δᴸ}
      (left : LeftOneSidedᵢ Φ Ψ)
      {nonvarA : NonVar A}
      {zero∈A : zero ∈ᵗ A}
      {p : freshᴿ Φ ∣ Δᴸ
        ⊢ c ⦂ (★ ⇒ ★) ⊒ A ⊣ suc Δᴿ}
      {B≢★ : (★ ⇒ ★) ≢ ★}
  → proj₁
      ((★⇒★ ？ , untag★⇒★ {Φ = Ψ}) ⨟ˡⁿ[ left ]
        (Coercions.gen c ,
          gen nonvarA zero∈A p {{freshⁿᵢ}} B≢★))
      ≡ (★⇒★ ？) ︔ᶜ Coercions.gen c
function-tag-gen-compositionᶜ
    left
    {nonvarA = nonvarA} {zero∈A = zero∈A}
    {p = p₁ ↦ p₂} =
  refl
function-tag-gen-compositionᶜ
    left
    {nonvarA = nonvar-all} {zero∈A = ∈-all zero∈A}
    {p = gen nonvarA zero∈A′ p B≢★} =
  refl

function-tag-sequence :
    ∀ {Δᴸ Δᴿ B c}
      {Φ : ImpCtx Δᴸ Δᴿ}
      (p : Φ ∣ Δᴸ ⊢ c ⦂ (★ ⇒ ★) ⊒ B ⊣ Δᴿ)
      (★⇒★≢B : (★ ⇒ ★) ≢ B)
  → proj₁
      (dualʷ (★⇒★ ! , tag★⇒★)
        ⨟ˡⁿ[ left-id-one-sidedᵢ ] (c , p))
      ≡ (★⇒★ ？) ︔ᶜ c
function-tag-sequence {B = A ⇒ B} (p₁ ↦ p₂) ★⇒★≢B
    with ★ ≟Ty A | ★ ≟Ty B
function-tag-sequence (p₁ ↦ p₂) ★⇒★≢B
    | yes refl | yes refl =
  ⊥-elim (★⇒★≢B refl)
function-tag-sequence (p₁ ↦ p₂) ★⇒★≢B
    | yes ★≡A | no ★≢B =
  refl
function-tag-sequence (p₁ ↦ p₂) ★⇒★≢B
    | no ★≢A | yes ★≡B =
  refl
function-tag-sequence (p₁ ↦ p₂) ★⇒★≢B
    | no ★≢A | no ★≢B =
  refl
function-tag-sequence
    (gen nonvarA zero∈A p B≢★) ★⇒★≢∀A =
  function-tag-gen-composition
    {nonvarA = nonvarA} {zero∈A = zero∈A}
    {p = p} {B≢★ = B≢★}

function-tag-sequenceᶜ :
    ∀ {Δᴸ Δᴿ B c}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {Ψ : ImpCtx Δᴸ Δᴸ}
      (left : LeftOneSidedᵢ Φ Ψ)
      (p : Φ ∣ Δᴸ ⊢ c ⦂ (★ ⇒ ★) ⊒ B ⊣ Δᴿ)
      (★⇒★≢B : (★ ⇒ ★) ≢ B)
  → proj₁
      ((★⇒★ ？ , untag★⇒★ {Φ = Ψ}) ⨟ˡⁿ[ left ] (c , p))
      ≡ (★⇒★ ？) ︔ᶜ c
function-tag-sequenceᶜ {B = A ⇒ B} left
    (p₁ ↦ p₂) ★⇒★≢B
    with ★ ≟Ty A | ★ ≟Ty B
function-tag-sequenceᶜ left (p₁ ↦ p₂) ★⇒★≢B
    | yes refl | yes refl =
  ⊥-elim (★⇒★≢B refl)
function-tag-sequenceᶜ left (p₁ ↦ p₂) ★⇒★≢B
    | yes ★≡A | no ★≢B =
  refl
function-tag-sequenceᶜ left (p₁ ↦ p₂) ★⇒★≢B
    | no ★≢A | yes ★≡B =
  refl
function-tag-sequenceᶜ left (p₁ ↦ p₂) ★⇒★≢B
    | no ★≢A | no ★≢B =
  refl
function-tag-sequenceᶜ left
    (gen nonvarA zero∈A p B≢★) ★⇒★≢∀A =
  function-tag-gen-compositionᶜ
    left
    {nonvarA = nonvarA} {zero∈A = zero∈A}
    {p = p} {B≢★ = B≢★}

wrap-untag-cong :
    ∀ {Δᴸ Δᴿ B c d}
      {Φ : ImpCtx Δᴸ Δᴿ}
      (p : Φ ∣ Δᴸ ⊢ c ⦂ (★ ⇒ ★) ⊒ B ⊣ Δᴿ)
      (q : Φ ∣ Δᴸ ⊢ d ⦂ (★ ⇒ ★) ⊒ B ⊣ Δᴿ)
  → c ≡ d
  → proj₁ (wrap-untag★⇒★ p) ≡
      proj₁ (wrap-untag★⇒★ q)
wrap-untag-cong {B = B} p q eq
    with (★ ⇒ ★) ≟Ty B
wrap-untag-cong p q eq | yes refl =
  refl
wrap-untag-cong p q eq | no B≢★⇒★ =
  cong (λ c → (★⇒★ ？) ︔ᶜ c) eq

wrap-tag-cong :
    ∀ {Δᴸ Δᴿ A c d}
      {Φ : ImpCtx Δᴿ Δᴸ}
      (p : Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ (★ ⇒ ★) ⊣ Δᴿ)
      (q : Φ ∣ Δᴸ ⊢ d ⦂ A ⊑ (★ ⇒ ★) ⊣ Δᴿ)
  → c ≡ d
  → proj₁ (wrap-tag★⇒★ p) ≡
      proj₁ (wrap-tag★⇒★ q)
wrap-tag-cong {A = A} p q eq
    with A ≟Ty (★ ⇒ ★)
wrap-tag-cong p q eq | yes refl =
  refl
wrap-tag-cong p q eq | no A≢★⇒★ =
  cong (λ c → c ︔ᶜ (★⇒★ !)) eq

strip-untag-cong :
    ∀ {Δᴸ Δᴿ B c d}
      {Φ : ImpCtx Δᴸ Δᴿ}
      (nonvarB : NonVar B)
      (zero∈B : zero ∈ᵗ B)
      (p : Φ ∣ Δᴸ ⊢ c ⦂ ★ ⊒ B ⊣ Δᴿ)
      (q : Φ ∣ Δᴸ ⊢ d ⦂ ★ ⊒ B ⊣ Δᴿ)
  → c ≡ d
  → proj₁ (strip-untag★⇒★ nonvarB zero∈B p) ≡
      proj₁ (strip-untag★⇒★ nonvarB zero∈B q)
strip-untag-cong nonvar-fun zero∈B
    untag★⇒★ untag★⇒★ eq =
  refl
strip-untag-cong nonvar-fun zero∈B
    (untag★⇒★︔ p [ ★⇒★≢B ])
    (untag★⇒★︔ q [ ★⇒★≢B′ ]) eq =
  sequence-tail-injective eq
strip-untag-cong nonvar-all zero∈B
    (untag★⇒★︔ p [ ★⇒★≢B ])
    (untag★⇒★︔ q [ ★⇒★≢B′ ]) eq =
  sequence-tail-injective eq
strip-untag-cong nonvar-all zero∈B
    (gen nonvarB zero∈B′ p ★≢★)
    (gen nonvarB′ zero∈B″ q ★≢★′) eq =
  ⊥-elim (★≢★ refl)

strip-tag-cong :
    ∀ {Δᴸ Δᴿ A c d}
      {Φ : ImpCtx Δᴿ Δᴸ}
      (nonvarA : NonVar A)
      (zero∈A : zero ∈ᵗ A)
      (p : Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ ★ ⊣ Δᴿ)
      (q : Φ ∣ Δᴸ ⊢ d ⦂ A ⊑ ★ ⊣ Δᴿ)
  → c ≡ d
  → proj₁ (strip-tag★⇒★ nonvarA zero∈A p) ≡
      proj₁ (strip-tag★⇒★ nonvarA zero∈A q)
strip-tag-cong nonvar-fun zero∈A
    tag★⇒★ tag★⇒★ eq =
  refl
strip-tag-cong nonvar-fun zero∈A
    (p ︔tag★⇒★[ A≢★⇒★ ])
    (q ︔tag★⇒★[ A≢★⇒★′ ]) eq =
  sequence-head-injective eq
strip-tag-cong nonvar-all zero∈A
    (p ︔tag★⇒★[ A≢★⇒★ ])
    (q ︔tag★⇒★[ A≢★⇒★′ ]) eq =
  sequence-head-injective eq
strip-tag-cong nonvar-all zero∈A
    (inst nonvarA zero∈A′ p ★≢★)
    (inst nonvarA′ zero∈A″ q ★≢★′) eq =
  ⊥-elim (★≢★ refl)

star-gen-normal-cong :
    ∀ {Δᴸ Δᴿ A c d}
      {Φ : ImpCtx Δᴸ Δᴿ}
      (nonvarA : NonVar A)
      (zero∈A : zero ∈ᵗ A)
      (p : freshᴿ Φ ∣ Δᴸ ⊢ c ⦂ ★ ⊒ A ⊣ suc Δᴿ)
      (q : freshᴿ Φ ∣ Δᴸ ⊢ d ⦂ ★ ⊒ A ⊣ suc Δᴿ)
  → c ≡ d
  → proj₁
      (wrap-untag★⇒★
        (gen nonvarA zero∈A
          (proj₂ (strip-untag★⇒★ nonvarA zero∈A p))
          {{freshⁿᵢ}}
          (λ ())))
      ≡ proj₁
        (wrap-untag★⇒★
          (gen nonvarA zero∈A
            (proj₂ (strip-untag★⇒★ nonvarA zero∈A q))
            {{freshⁿᵢ}}
            (λ ())))
star-gen-normal-cong nonvarA zero∈A p q eq =
  wrap-untag-cong
    (gen nonvarA zero∈A
      (proj₂ (strip-untag★⇒★ nonvarA zero∈A p))
      {{freshⁿᵢ}}
      (λ ()))
    (gen nonvarA zero∈A
      (proj₂ (strip-untag★⇒★ nonvarA zero∈A q))
      {{freshⁿᵢ}}
      (λ ()))
    (cong Coercions.gen
      (strip-untag-cong nonvarA zero∈A p q eq))

star-inst-normal-cong :
    ∀ {Δᴸ Δᴿ A c d}
      {Φ : ImpCtx Δᴿ Δᴸ}
      (nonvarA : NonVar A)
      (zero∈A : zero ∈ᵗ A)
      (p : freshᴿ Φ ∣ suc Δᴸ ⊢ c ⦂ A ⊑ ★ ⊣ Δᴿ)
      (q : freshᴿ Φ ∣ suc Δᴸ ⊢ d ⦂ A ⊑ ★ ⊣ Δᴿ)
  → c ≡ d
  → proj₁
      (wrap-tag★⇒★
        (inst nonvarA zero∈A
          (proj₂ (strip-tag★⇒★ nonvarA zero∈A p))
          {{freshʷᵢ}}
          (λ ())))
      ≡ proj₁
        (wrap-tag★⇒★
          (inst nonvarA zero∈A
            (proj₂ (strip-tag★⇒★ nonvarA zero∈A q))
            {{freshʷᵢ}}
            (λ ())))
star-inst-normal-cong nonvarA zero∈A p q eq =
  wrap-tag-cong
    (inst nonvarA zero∈A
      (proj₂ (strip-tag★⇒★ nonvarA zero∈A p))
      {{freshʷᵢ}}
      (λ ()))
    (inst nonvarA zero∈A
      (proj₂ (strip-tag★⇒★ nonvarA zero∈A q))
      {{freshʷᵢ}}
      (λ ()))
    (cong Coercions.inst
      (strip-tag-cong nonvarA zero∈A p q eq))

special-no-zero-var : ∀ {Δᴸ Δᴿ X} {Φ : ImpCtx Δᴸ Δᴿ}
  → freshᴿ Φ ⊢ X ≈ˣ zero
  → ⊥
special-no-zero-var ()

variable-target-no-zero :
    ∀ {Δᴸ Δᴿ X A c}
      {Φ : ImpCtx Δᴸ Δᴿ}
  → freshᴿ Φ ∣ Δᴸ ⊢ c ⦂ ＇ X ⊒ A ⊣ suc Δᴿ
  → zero ∈ᵗ A
  → ⊥
variable-target-no-zero
    (idᵃ (＇ X) (＇ zero) hA hB X≈zero)
    var-∈ =
  special-no-zero-var X≈zero
variable-target-no-zero
    (gen nonvarA zero∈A p B≢★) X∈ =
  variable-target-no-zero p zero∈A

widening-variable-target-no-zero :
    ∀ {Δᴸ Δᴿ X A c}
      {Φ : ImpCtx Δᴸ Δᴿ}
  → freshᴿ Φ ∣ suc Δᴿ ⊢ c ⦂ A ⊑ ＇ X ⊣ Δᴸ
  → zero ∈ᵗ A
  → ⊥
widening-variable-target-no-zero
    (idᵃ (＇ zero) (＇ X) hA hB X≈zero) var-∈ =
  special-no-zero-var X≈zero
widening-variable-target-no-zero
    (inst nonvarA zero∈A p B≢★) X∈ =
  widening-variable-target-no-zero p zero∈A

------------------------------------------------------------------------
-- Composition ignores derivation evidence
------------------------------------------------------------------------

mutual

  star-left-identity-composeᶜ :
      ∀ {Δ₀ Δ₁ Δ₂ B d}
        {Φ₀₁ : ImpCtx Δ₀ Δ₁}
        {Φ₁₂ : ImpCtx Δ₁ Δ₂}
        {Φ₀₂ : ImpCtx Δ₀ Δ₂}
        (comp : Φ₀₁ ⨟ᵢ Φ₁₂ ⇒ Φ₀₂)
        (i : Φ₀₁ ∣ Δ₀ ⊢ idᶜ ⦂ ★ ⊒ ★ ⊣ Δ₁)
        (q : Φ₁₂ ∣ Δ₁ ⊢ d ⦂ ★ ⊒ B ⊣ Δ₂)
    → proj₁ (composeⁿ comp i q) ≡ d
  star-left-identity-composeᶜ comp
      (idᵃ ★ ★ hA hB a⊒b)
      (idᵃ ★ ★ hA′ hB′ a⊒b′) =
    refl
  star-left-identity-composeᶜ comp
      (idᵃ ★ ★ hA hB a⊒b) (untag ι) =
    refl
  star-left-identity-composeᶜ comp
      (idᵃ ★ ★ hA hB a⊒b) untag★⇒★ =
    refl
  star-left-identity-composeᶜ comp
      (idᵃ ★ ★ hA hB a⊒b)
      (untag★⇒★︔ q [ ★⇒★≢B ]) =
    refl
  star-left-identity-composeᶜ comp
      (idᵃ ★ ★ hA hB a⊒b)
      (seal X⊑★) =
    refl
  star-left-identity-composeᶜ comp
      (idᵃ ★ ★ hA hB a⊒b)
      (q ︔seal X⊑★ [ ★≢B ]) =
    refl
  star-left-identity-composeᶜ comp
      (idᵃ ★ ★ hA hB a⊒b)
      (gen nonvarA zero∈A q ★≢★) =
    ⊥-elim (★≢★ refl)

  star-right-identity-composeʷ :
      ∀ {Δ₀ Δ₁ Δ₂ A c}
        {Φ₀₁ : ImpCtx Δ₀ Δ₁}
        {Φ₁₂ : ImpCtx Δ₁ Δ₂}
        {Φ₀₂ : ImpCtx Δ₀ Δ₂}
        (comp : Φ₀₁ ⨟ᵢ Φ₁₂ ⇒ Φ₀₂)
        (p : Φ₁₂ ∣ Δ₂ ⊢ c ⦂ A ⊑ ★ ⊣ Δ₁)
        (i : Φ₀₁ ∣ Δ₁ ⊢ idᶜ ⦂ ★ ⊑ ★ ⊣ Δ₀)
    → proj₁ (composeʷ comp p i) ≡ c
  star-right-identity-composeʷ comp
      (idᵃ ★ ★ hA hB a⊑b)
      (idᵃ ★ ★ hA′ hB′ a⊑b′) =
    refl
  star-right-identity-composeʷ comp
      (tag ι) (idᵃ ★ ★ hA hB a⊑b) =
    refl
  star-right-identity-composeʷ comp
      tag★⇒★ (idᵃ ★ ★ hA hB a⊑b) =
    refl
  star-right-identity-composeʷ comp
      (p ︔tag★⇒★[ A≢★⇒★ ])
      (idᵃ ★ ★ hA hB a⊑b) =
    refl
  star-right-identity-composeʷ comp
      (unseal X⊑★) (idᵃ ★ ★ hA hB a⊑b) =
    refl
  star-right-identity-composeʷ comp
      (unseal X⊑★ ︔ p [ A≢★ ])
      (idᵃ ★ ★ hA hB a⊑b) =
    refl
  star-right-identity-composeʷ comp
      (inst nonvarA zero∈A p ★≢★)
      (idᵃ ★ ★ hA hB a⊑b) =
    ⊥-elim (★≢★ refl)

  function-left-identity-composeᶜ :
      ∀ {Δ₀ Δ₁ Δ₂ B d}
        {Φ₀₁ : ImpCtx Δ₀ Δ₁}
        {Φ₁₂ : ImpCtx Δ₁ Δ₂}
        {Φ₀₂ : ImpCtx Δ₀ Δ₂}
        (comp : Φ₀₁ ⨟ᵢ Φ₁₂ ⇒ Φ₀₂)
        (i : Φ₀₁ ∣ Δ₀ ⊢ idᶜ ↦ᶜ idᶜ
          ⦂ (★ ⇒ ★) ⊒ (★ ⇒ ★) ⊣ Δ₁)
        (q : Φ₁₂ ∣ Δ₁ ⊢ d ⦂ (★ ⇒ ★) ⊒ B ⊣ Δ₂)
    → proj₁ (composeⁿ comp i q) ≡ d
  function-left-identity-composeᶜ comp
      (idᵃ ★ ★ hA hB a⊒b ↦
       idᵃ ★ ★ hA′ hB′ a⊒b′)
      (q₁ ↦ q₂) =
    cong₂ _↦ᶜ_
      (star-right-identity-composeʷ comp q₁
        (idᵃ ★ ★ hA hB a⊒b))
      (star-left-identity-composeᶜ comp
        (idᵃ ★ ★ hA′ hB′ a⊒b′) q₂)
  function-left-identity-composeᶜ comp
      (idᵃ ★ ★ hA hB a⊒b ↦
       idᵃ ★ ★ hA′ hB′ a⊒b′)
      (gen nonvarC zero∈C q B≢★) =
    cong Coercions.gen
      (function-left-identity-composeᶜ
        (keepᴿ comp)
        (idᵃ ★ ★ hA hB a⊒b ↦
         idᵃ ★ ★ hA′ hB′ a⊒b′)
        q)

  composeⁿ-left-evidence :
      ∀ {Δ₀ Δ₁ Δ₂ A B C c d}
        {Φ₀₁ : ImpCtx Δ₀ Δ₁}
        {Φ₁₂ : ImpCtx Δ₁ Δ₂}
        {Φ₀₂ : ImpCtx Δ₀ Δ₂}
        (comp : Φ₀₁ ⨟ᵢ Φ₁₂ ⇒ Φ₀₂)
        (p p′ : Φ₀₁ ∣ Δ₀ ⊢ c ⦂ A ⊒ B ⊣ Δ₁)
        (q : Φ₁₂ ∣ Δ₁ ⊢ d ⦂ B ⊒ C ⊣ Δ₂)
    → proj₁ (composeⁿ comp p q) ≡
        proj₁ (composeⁿ comp p′ q)
  composeⁿ-left-evidence comp
      (idᵃ (＇ W) (＇ X) hA hB W≈X)
      (idᵃ (＇ W′) (＇ .X) hA′ hB′ W′≈X)
      (idᵃ (＇ .X) (＇ Y) hB″ hC X≈Y) =
    refl
  composeⁿ-left-evidence comp
      (seal X⊑★) (seal X⊑★′)
      (idᵃ (＇ X) (＇ Y) hB hC X≈Y) =
    refl
  composeⁿ-left-evidence comp
      (p ︔seal X⊑★ [ ★≢B ])
      (p′ ︔seal X⊑★′ [ ★≢B′ ])
      (idᵃ (＇ X) (＇ Y) hB hC X≈Y) =
    refl
  composeⁿ-left-evidence comp
      (idᵃ (‵ i) (‵ j) hA hB refl)
      (idᵃ (‵ k) (‵ l) hA′ hB′ refl)
      (idᵃ (‵ m) (‵ n) hB″ hC refl) =
    refl
  composeⁿ-left-evidence comp
      (untag ι) (untag .ι)
      (idᵃ (‵ .ι) (‵ κ) hB hC refl) =
    refl
  composeⁿ-left-evidence comp
      (idᵃ ★ ★ hA hB a⊒b)
      (idᵃ ★ ★ hA′ hB′ a⊒b′) q =
    trans (star-left-identity-composeᶜ comp
      (idᵃ ★ ★ hA hB a⊒b) q)
      (sym (star-left-identity-composeᶜ comp
        (idᵃ ★ ★ hA′ hB′ a⊒b′) q))
  composeⁿ-left-evidence comp untag★⇒★ untag★⇒★ q =
    refl
  composeⁿ-left-evidence comp
      (untag★⇒★︔ p [ ★⇒★≢B ])
      (untag★⇒★︔ p′ [ ★⇒★≢B′ ]) (q₁ ↦ q₂) =
    wrap-untag-cong
      (proj₂ (composeⁿ comp p (q₁ ↦ q₂)))
      (proj₂ (composeⁿ comp p′ (q₁ ↦ q₂)))
      (composeⁿ-left-evidence comp p p′ (q₁ ↦ q₂))
  composeⁿ-left-evidence comp
      (untag★⇒★︔ p [ ★⇒★≢B ])
      (untag★⇒★︔ p′ [ ★⇒★≢B′ ]) (∀ⁿ q) =
    wrap-untag-cong
      (proj₂ (composeⁿ comp p (∀ⁿ q)))
      (proj₂ (composeⁿ comp p′ (∀ⁿ q)))
      (composeⁿ-left-evidence comp p p′ (∀ⁿ q))
  composeⁿ-left-evidence comp
      (untag★⇒★︔ p [ ★⇒★≢B ])
      (untag★⇒★︔ p′ [ ★⇒★≢B′ ])
      (gen nonvarC occC q B≢★) =
    wrap-untag-cong
      (proj₂
        (composeⁿ comp p (gen nonvarC occC q B≢★)))
      (proj₂
        (composeⁿ comp p′ (gen nonvarC occC q B≢★)))
      (composeⁿ-left-evidence comp p p′
        (gen nonvarC occC q B≢★))
  composeⁿ-left-evidence comp
      (untag★⇒★︔ p [ ★⇒★≢B ])
      (untag★⇒★︔ p′ [ ★⇒★≢B′ ])
      (idᵃ (＇ X) (＇ Y) hB hC X≈Y) =
    ⊥-elim (no-function-to-variable-narrowing p)
  composeⁿ-left-evidence comp
      (untag★⇒★︔ p [ ★⇒★≢B ])
      (untag★⇒★︔ p′ [ ★⇒★≢B′ ])
      (idᵃ (‵ ι) (‵ κ) hB hC refl) =
    ⊥-elim (no-function-to-base-narrowing p)
  composeⁿ-left-evidence comp
      (untag★⇒★︔ p [ ★⇒★≢B ])
      (untag★⇒★︔ p′ [ ★⇒★≢B′ ])
      (idᵃ ★ ★ hB hC ★⊒★) =
    ⊥-elim (no-function-to-star-narrowing p)
  composeⁿ-left-evidence comp
      (untag★⇒★︔ p [ ★⇒★≢B ])
      (untag★⇒★︔ p′ [ ★⇒★≢B′ ])
      (untag ι) =
    ⊥-elim (no-function-to-star-narrowing p)
  composeⁿ-left-evidence comp
      (untag★⇒★︔ p [ ★⇒★≢B ])
      (untag★⇒★︔ p′ [ ★⇒★≢B′ ])
      untag★⇒★ =
    ⊥-elim (no-function-to-star-narrowing p)
  composeⁿ-left-evidence comp
      (untag★⇒★︔ p [ ★⇒★≢B ])
      (untag★⇒★︔ p′ [ ★⇒★≢B′ ])
      (untag★⇒★︔ q [ ★⇒★≢C ]) =
    ⊥-elim (no-function-to-star-narrowing p)
  composeⁿ-left-evidence comp
      (untag★⇒★︔ p [ ★⇒★≢B ])
      (untag★⇒★︔ p′ [ ★⇒★≢B′ ])
      (seal X⊑★) =
    ⊥-elim (no-function-to-star-narrowing p)
  composeⁿ-left-evidence comp
      (untag★⇒★︔ p [ ★⇒★≢B ])
      (untag★⇒★︔ p′ [ ★⇒★≢B′ ])
      (q ︔seal X⊑★ [ ★≢C ]) =
    ⊥-elim (no-function-to-star-narrowing p)
  composeⁿ-left-evidence comp
      (gen nonvarB occB p B≢★)
      (gen nonvarB′ occB′ p′ B≢★′)
      (∀ⁿ q) =
    cong Coercions.gen
      (composeⁿ-left-evidence
        (freshᴿ-both comp) p p′ q)
  composeⁿ-left-evidence comp
      (idᵃ (＇ X) (＇ Y) hA hB X⊒Y)
      (idᵃ (＇ X′) (＇ Y′) hA′ hB′ X⊒Y′)
      (gen nonvarC occC q B≢★) =
    cong Coercions.gen
      (composeⁿ-left-evidence (keepᴿ comp)
        (idᵃ (＇ X) (＇ Y) hA hB X⊒Y)
        (idᵃ (＇ X′) (＇ Y′) hA′ hB′ X⊒Y′) q)
  composeⁿ-left-evidence comp
      (idᵃ (‵ ι) (‵ κ) hA hB a⊒b)
      (idᵃ (‵ ι′) (‵ κ′) hA′ hB′ a⊒b′)
      (gen nonvarC occC q B≢★) =
    ⊥-elim (base-target-no-member q occC)
  composeⁿ-left-evidence comp
      (p₁ ↦ p₂) (p₁′ ↦ p₂′)
      (gen nonvarC occC q B≢★) =
    cong Coercions.gen
      (composeⁿ-left-evidence (keepᴿ comp)
        (p₁ ↦ p₂) (p₁′ ↦ p₂′) q)
  composeⁿ-left-evidence comp
      (∀ⁿ p) (∀ⁿ p′)
      (gen nonvarC occC q B≢★) =
    cong Coercions.gen
      (composeⁿ-left-evidence (keepᴿ comp)
        (∀ⁿ p) (∀ⁿ p′) q)
  composeⁿ-left-evidence comp
      (untag ι) (untag .ι)
      (gen nonvarC occC q B≢★) =
    ⊥-elim (base-target-no-member q occC)
  composeⁿ-left-evidence comp
      (seal X⊑★) (seal X⊑★′)
      (gen nonvarC occC q B≢★) =
    ⊥-elim (variable-target-no-zero q occC)
  composeⁿ-left-evidence comp
      (p ︔seal X⊑★ [ ★≢B ])
      (p′ ︔seal X⊑★′ [ ★≢B′ ])
      (gen nonvarC occC q B≢★) =
    ⊥-elim (variable-target-no-zero q occC)
  composeⁿ-left-evidence {A = A} comp
      (gen nonvarA occA p {{extensionP}} A≢★)
      (gen nonvarA′ occA′ p′ {{extensionP′}} A≢★′)
      (gen nonvarC occC q B≢★)
      with composeⁿ-left-evidence (keepᴿ comp)
        (gen nonvarA occA p {{extensionP}} A≢★)
        (gen nonvarA′ occA′ p′ {{extensionP′}} A≢★′)
        q
         | A ≟Ty ★
  composeⁿ-left-evidence {A = .★} comp
      (gen nonvarA occA p {{extensionP}} ★≢★)
      (gen nonvarA′ occA′ p′ {{extensionP′}} ★≢★′)
      (gen nonvarC occC q B≢★)
      | recEq | yes refl =
    ⊥-elim (★≢★ refl)
  composeⁿ-left-evidence {A = A} comp
      (gen nonvarA occA p {{extensionP}} A≢★)
      (gen nonvarA′ occA′ p′ {{extensionP′}} A≢★′)
      (gen nonvarC occC q B≢★)
      | recEq | no A≢★′′ =
    cong Coercions.gen recEq
  composeⁿ-left-evidence comp
      (p₁ ↦ p₂) (p₁′ ↦ p₂′) (q₁ ↦ q₂) =
    cong₂ _↦ᶜ_
      (composeʷ-right-evidence comp q₁ p₁ p₁′)
      (composeⁿ-left-evidence comp p₂ p₂′ q₂)
  composeⁿ-left-evidence comp
      (∀ⁿ p) (∀ⁿ p′) (∀ⁿ q) =
    cong Coercions.`∀
      (composeⁿ-left-evidence
        (both-both comp) p p′ q)

  composeʷ-right-evidence :
      ∀ {Δ₀ Δ₁ Δ₂ A B C c d}
        {Φ₀₁ : ImpCtx Δ₀ Δ₁}
        {Φ₁₂ : ImpCtx Δ₁ Δ₂}
        {Φ₀₂ : ImpCtx Δ₀ Δ₂}
        (comp : Φ₀₁ ⨟ᵢ Φ₁₂ ⇒ Φ₀₂)
        (p : Φ₁₂ ∣ Δ₂ ⊢ c ⦂ A ⊑ B ⊣ Δ₁)
        (q q′ : Φ₀₁ ∣ Δ₁ ⊢ d ⦂ B ⊑ C ⊣ Δ₀)
    → proj₁ (composeʷ comp p q) ≡
        proj₁ (composeʷ comp p q′)
  composeʷ-right-evidence comp p
      (idᵃ ★ ★ hB hC a⊑b)
      (idᵃ ★ ★ hB′ hC′ a⊑b′) =
    trans
      (star-right-identity-composeʷ comp p
        (idᵃ ★ ★ hB hC a⊑b))
      (sym (star-right-identity-composeʷ comp p
        (idᵃ ★ ★ hB′ hC′ a⊑b′)))
  composeʷ-right-evidence comp
      (idᵃ (‵ ι) (‵ κ) hA hB refl)
      (idᵃ (‵ .κ) (‵ κ₂) hB′ hC refl)
      (idᵃ (‵ κ₃) (‵ κ₄) hB″ hC′ refl) =
    refl
  composeʷ-right-evidence comp
      (idᵃ (‵ ι) (‵ κ) hA hB refl)
      (tag .κ) (tag .κ) =
    refl
  composeʷ-right-evidence comp
      (idᵃ (＇ X) (＇ Y) hA hB X⊑Y)
      (idᵃ (＇ .Y) (＇ z) hB′ hC Y⊑z)
      (idᵃ (＇ Y′) (＇ z′) hB″ hC′ Y′⊑z′) =
    refl
  composeʷ-right-evidence comp
      (idᵃ (＇ X) (＇ Y) hA hB X⊑Y)
      (unseal Y⊑★) (unseal Y⊑★′) =
    refl
  composeʷ-right-evidence comp
      (idᵃ (＇ X) (＇ Y) hA hB X⊑Y)
      (unseal Y⊑★ ︔ q [ A≢★ ])
      (unseal Y⊑★′ ︔ q′ [ A≢★′ ]) =
    refl
  composeʷ-right-evidence comp
      (idᵃ (‵ ι) (＇ Y) hA hB ())
      (unseal Y⊑★ ︔ q [ A≢★ ])
      (unseal Y⊑★′ ︔ q′ [ A≢★′ ])
  composeʷ-right-evidence comp
      (idᵃ ★ (＇ Y) hA hB ())
      (unseal Y⊑★ ︔ q [ A≢★ ])
      (unseal Y⊑★′ ︔ q′ [ A≢★′ ])
  composeʷ-right-evidence {A = A ⇒ B} comp
      (idᵃ () (＇ Y) hA hB a⊑b)
      (unseal Y⊑★ ︔ q [ A≢★ ])
      (unseal Y⊑★′ ︔ q′ [ A≢★′ ])
  composeʷ-right-evidence {A = `∀ A} comp
      (idᵃ () (＇ Y) hA hB a⊑b)
      (unseal Y⊑★ ︔ q [ A≢★ ])
      (unseal Y⊑★′ ︔ q′ [ A≢★′ ])
  composeʷ-right-evidence comp
      (inst nonvarA zero∈A p B≢★)
      (unseal Y⊑★ ︔ q [ A≢★ ])
      (unseal Y⊑★′ ︔ q′ [ A≢★′ ]) =
    ⊥-elim (widening-variable-target-no-zero p zero∈A)
  composeʷ-right-evidence comp p tag★⇒★ tag★⇒★ =
    refl
  composeʷ-right-evidence comp p
      (q ︔tag★⇒★[ B≢★⇒★ ])
      (q′ ︔tag★⇒★[ B≢★⇒★′ ])
      with composeʷ comp p q
         | composeʷ comp p q′
         | composeʷ-right-evidence comp p q q′
  composeʷ-right-evidence comp p
      (q ︔tag★⇒★[ B≢★⇒★ ])
      (q′ ︔tag★⇒★[ B≢★⇒★′ ])
      | r , r⊢ | .r , r⊢′ | refl =
    wrap-tag-cong r⊢ r⊢′ refl
  composeʷ-right-evidence comp (∀ʷ p)
      (inst nonvarB occB q C≢★)
      (inst nonvarB′ occB′ q′ C≢★′) =
    cong Coercions.inst
      (composeʷ-right-evidence
        (freshᴿ-both comp) p q q′)
  composeʷ-right-evidence comp
      (inst nonvarA occA p B≢★)
      (idᵃ (＇ X) (＇ Y) hB hC X⊑Y)
      (idᵃ (＇ X′) (＇ Y′) hB′ hC′ X′⊑Y′) =
    cong Coercions.inst
      (composeʷ-right-evidence (keepᴿ comp) p
        (idᵃ (＇ X) (＇ Y) hB hC X⊑Y)
        (idᵃ (＇ X′) (＇ Y′) hB′ hC′ X′⊑Y′))
  composeʷ-right-evidence comp
      (inst nonvarA occA p B≢★)
      (idᵃ (‵ ι) (‵ κ) hB hC a⊑b)
      (idᵃ (‵ ι′) (‵ κ′) hB′ hC′ a⊑b′) =
    cong Coercions.inst
      (composeʷ-right-evidence (keepᴿ comp) p
        (idᵃ (‵ ι) (‵ κ) hB hC a⊑b)
        (idᵃ (‵ ι′) (‵ κ′) hB′ hC′ a⊑b′))
  composeʷ-right-evidence comp
      (inst nonvarA occA p B≢★)
      (tag ι) (tag .ι) =
    refl
  composeʷ-right-evidence comp
      (inst nonvarA occA p B≢★)
      (unseal X⊑★) (unseal X⊑★′) =
    star-inst-normal-cong nonvarA occA
      (proj₂
        (composeʷ (keepᴿ comp) p (unseal X⊑★)))
      (proj₂
        (composeʷ (keepᴿ comp) p (unseal X⊑★′)))
      (composeʷ-right-evidence (keepᴿ comp)
        p (unseal X⊑★) (unseal X⊑★′))
  composeʷ-right-evidence {C = C} comp
      (inst nonvarA occA p B≢★)
      (inst nonvarB occB q {{extensionQ}} C≢★)
      (inst nonvarB′ occB′ q′ {{extensionQ′}} C≢★′)
      with composeʷ-right-evidence (keepᴿ comp) p
        (inst nonvarB occB q {{extensionQ}} C≢★)
        (inst nonvarB′ occB′ q′ {{extensionQ′}} C≢★′)
         | C ≟Ty ★
  composeʷ-right-evidence {C = .★} comp
      (inst nonvarA occA p B≢★)
      (inst nonvarB occB q {{extensionQ}} ★≢★)
      (inst nonvarB′ occB′ q′ {{extensionQ′}} ★≢★′)
      | recEq | yes refl =
    ⊥-elim (★≢★ refl)
  composeʷ-right-evidence {C = C} comp
      (inst nonvarA occA p B≢★)
      (inst nonvarB occB q {{extensionQ}} C≢★)
      (inst nonvarB′ occB′ q′ {{extensionQ′}} C≢★′)
      | recEq | no C≢★′′ =
    cong Coercions.inst recEq
  composeʷ-right-evidence comp
      (inst nonvarA occA p B≢★)
      (q₁ ↦ q₂) (q₁′ ↦ q₂′) =
    cong Coercions.inst
      (composeʷ-right-evidence (keepᴿ comp)
        p (q₁ ↦ q₂) (q₁′ ↦ q₂′))
  composeʷ-right-evidence comp
      (inst nonvarA occA p B≢★)
      (∀ʷ q) (∀ʷ q′) =
    cong Coercions.inst
      (composeʷ-right-evidence (keepᴿ comp)
        p (∀ʷ q) (∀ʷ q′))
  composeʷ-right-evidence comp
      (p₁ ↦ p₂) (q₁ ↦ q₂) (q₁′ ↦ q₂′) =
    cong₂ _↦ᶜ_
      (composeⁿ-left-evidence comp q₁ q₁′ p₁)
      (composeʷ-right-evidence comp p₂ q₂ q₂′)
  composeʷ-right-evidence comp
      (∀ʷ p) (∀ʷ q) (∀ʷ q′) =
    cong Coercions.`∀
      (composeʷ-right-evidence
        (both-both comp) p q q′)

tag-prefix-cancel :
    ∀ {Δᴸ Δᴿ A B G}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {u⊑ : idᵢ Δᴸ ∣ Δᴸ ⊢ G ! ⦂ A ⊑ ★ ⊣ Δᴸ}
      {p q : Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ}
  → dualʷ (G ! , u⊑) ⨟ˡⁿ[ left-id-one-sidedᵢ ] p ≐ⁿ
      dualʷ (G ! , u⊑) ⨟ˡⁿ[ left-id-one-sidedᵢ ] q
  → p ≐ⁿ q
tag-prefix-cancel {u⊑ = tag ι}
    {p = _ , idᵃ a b hA hB a⊒b}
    {q = _ , idᵃ a′ b′ hA′ hB′ a⊒b′} eq =
  refl
tag-prefix-cancel {u⊑ = tag ι}
    {p = _ , gen nonvarA zero∈A p B≢★}
    {q = _ , gen nonvarA′ zero∈A′ q B≢★′} eq =
  ⊥-elim (base-target-no-member p zero∈A)
tag-prefix-cancel {B = B} {u⊑ = tag★⇒★}
    {p = _ , p₁ ↦ p₂}
    {q = _ , q₁ ↦ q₂} eq
    with (★ ⇒ ★) ≟Ty B
tag-prefix-cancel {u⊑ = tag★⇒★}
    {p = _ , p₁ ↦ p₂}
    {q = _ , q₁ ↦ q₂} eq | yes refl =
  trans (star-function-narrowing-coercion (p₁ ↦ p₂))
    (sym (star-function-narrowing-coercion (q₁ ↦ q₂)))
tag-prefix-cancel {u⊑ = tag★⇒★}
    {p = _ , p₁ ↦ p₂}
    {q = _ , q₁ ↦ q₂} eq | no B≢★⇒★ =
  sequence-tail-injective eq
tag-prefix-cancel {u⊑ = tag★⇒★}
    {p = _ , gen nonvarA zero∈A p B≢★}
    {q = _ , gen nonvarA′ zero∈A′ q B≢★′} eq =
  sequence-tail-injective
    (trans
      (sym (function-tag-gen-composition
        {nonvarA = nonvarA} {zero∈A = zero∈A}
        {p = p} {B≢★ = B≢★}))
      (trans eq
        (function-tag-gen-composition
          {nonvarA = nonvarA′} {zero∈A = zero∈A′}
          {p = q} {B≢★ = B≢★′})))

tag-prefix-cancelᶜ :
    ∀ {Δᴸ Δᴿ A B G}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {Ψ Ψ′ : ImpCtx Δᴸ Δᴸ}
      {left : LeftOneSidedᵢ Φ Ψ}
      {left′ : LeftOneSidedᵢ Φ Ψ′}
      {u⊑ : Ψ ∣ Δᴸ ⊢ G ! ⦂ A ⊑ ★ ⊣ Δᴸ}
      {v⊑ : Ψ′ ∣ Δᴸ ⊢ G ! ⦂ A ⊑ ★ ⊣ Δᴸ}
      {p q : Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ}
  → dualʷ (G ! , u⊑) ⨟ˡⁿ[ left ] p ≐ⁿ
      dualʷ (G ! , v⊑) ⨟ˡⁿ[ left′ ] q
  → p ≐ⁿ q
tag-prefix-cancelᶜ {u⊑ = tag ι} {v⊑ = tag .ι}
    {p = _ , idᵃ a b hA hB a⊒b}
    {q = _ , idᵃ a′ b′ hA′ hB′ a⊒b′} eq =
  refl
tag-prefix-cancelᶜ {u⊑ = tag ι} {v⊑ = tag .ι}
    {p = _ , gen nonvarA zero∈A p B≢★}
    {q = _ , gen nonvarA′ zero∈A′ q B≢★′} eq =
  ⊥-elim (base-target-no-member p zero∈A)
tag-prefix-cancelᶜ {B = B}
    {u⊑ = tag★⇒★} {v⊑ = tag★⇒★}
    {p = _ , p₁ ↦ p₂}
    {q = _ , q₁ ↦ q₂} eq
    with (★ ⇒ ★) ≟Ty B
tag-prefix-cancelᶜ
    {u⊑ = tag★⇒★} {v⊑ = tag★⇒★}
    {p = _ , p₁ ↦ p₂}
    {q = _ , q₁ ↦ q₂} eq | yes refl =
  trans (star-function-narrowing-coercion (p₁ ↦ p₂))
    (sym (star-function-narrowing-coercion (q₁ ↦ q₂)))
tag-prefix-cancelᶜ
    {u⊑ = tag★⇒★} {v⊑ = tag★⇒★}
    {p = _ , p₁ ↦ p₂}
    {q = _ , q₁ ↦ q₂} eq | no B≢★⇒★ =
  sequence-tail-injective eq
tag-prefix-cancelᶜ
    {left = left} {left′ = left′}
    {u⊑ = tag★⇒★} {v⊑ = tag★⇒★}
    {p = _ , gen nonvarA zero∈A p B≢★}
    {q = _ , gen nonvarA′ zero∈A′ q B≢★′} eq =
  sequence-tail-injective
    (trans
      (sym (function-tag-gen-compositionᶜ left
        {nonvarA = nonvarA} {zero∈A = zero∈A}
        {p = p} {B≢★ = B≢★}))
      (trans eq
        (function-tag-gen-compositionᶜ left′
          {nonvarA = nonvarA′} {zero∈A = zero∈A′}
          {p = q} {B≢★ = B≢★′})))

base-common-target :
    ∀ {Δᴸ Δᴿ ι κ B}
      {Φ : ImpCtx Δᴸ Δᴿ}
  → (a : Atom (‵ ι))
  → (a′ : Atom (‵ κ))
  → (b : Atom B)
  → (b′ : Atom B)
  → Φ ⊢ a ≈ᵃ b
  → Φ ⊢ a′ ≈ᵃ b′
  → ι ≡ κ
base-common-target (‵ ι) (‵ κ) b b′ μ≡ι μ≡κ with b | b′
base-common-target (‵ ι) (‵ κ) b b′ () μ≡κ | ＇ X | ＇ Y
base-common-target (‵ ι) (‵ κ) b b′ μ≡ι μ≡κ
    | ‵ μ | ‵ μ′ =
  trans μ≡ι (sym μ≡κ)
base-common-target (‵ ι) (‵ κ) b b′ () μ≡κ | ★ | ★

base-tag : Base → Tag
base-tag ι = ‵ ι

tag-prefix-match :
    ∀ {Δᴸ Δᴿ A C B G H}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {u⊑ : idᵢ Δᴸ ∣ Δᴸ ⊢ G ! ⦂ A ⊑ ★ ⊣ Δᴸ}
      {v⊑ : idᵢ Δᴸ ∣ Δᴸ ⊢ H ! ⦂ C ⊑ ★ ⊣ Δᴸ}
      {p : Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ C ⊒ B ⊣ Δᴿ}
  → dualʷ (G ! , u⊑) ⨟ˡⁿ[ left-id-one-sidedᵢ ] p ≐ⁿ
      dualʷ (H ! , v⊑) ⨟ˡⁿ[ left-id-one-sidedᵢ ] q
  → G ≡ H
tag-prefix-match
    {u⊑ = tag ι} {v⊑ = tag κ}
    {p = _ , idᵃ a b hA hB a⊒b}
    {q = _ , idᵃ a′ b′ hA′ hB′ a⊒b′} eq =
  cong base-tag (base-common-target a a′ b b′ a⊒b a⊒b′)
tag-prefix-match
    {u⊑ = tag ι} {v⊑ = tag κ}
    {p = _ , gen nonvarB zero∈B p B≢★}
    {q = q} eq =
  ⊥-elim (no-base-to-all-narrowing
    (gen nonvarB zero∈B p {{freshⁿᵢ}} B≢★))
tag-prefix-match
    {u⊑ = tag ι} {v⊑ = tag★⇒★}
    {p = _ , idᵃ (‵ .ι) (‵ μ) hA hB refl}
    {q = _ , q} eq =
  ⊥-elim (no-function-to-base-narrowing q)
tag-prefix-match
    {u⊑ = tag ι} {v⊑ = tag★⇒★}
    {p = _ , gen nonvarB zero∈B p B≢★}
    {q = q} eq =
  ⊥-elim (no-base-to-all-narrowing
    (gen nonvarB zero∈B p {{freshⁿᵢ}} B≢★))
tag-prefix-match
    {u⊑ = tag★⇒★} {v⊑ = tag κ}
    {p = _ , p}
    {q = _ , idᵃ (‵ .κ) (‵ μ) hA hB refl} eq =
  ⊥-elim (no-function-to-base-narrowing p)
tag-prefix-match
    {u⊑ = tag★⇒★} {v⊑ = tag κ}
    {p = p}
    {q = _ , gen nonvarB zero∈B q B≢★} eq =
  ⊥-elim (no-base-to-all-narrowing
    (gen nonvarB zero∈B q {{freshⁿᵢ}} B≢★))
tag-prefix-match
    {u⊑ = tag★⇒★} {v⊑ = tag★⇒★} eq =
  refl

tag-prefix-matchᶜ :
    ∀ {Δᴸ Δᴿ A C B G H}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {Ψ Ψ′ : ImpCtx Δᴸ Δᴸ}
      {left : LeftOneSidedᵢ Φ Ψ}
      {left′ : LeftOneSidedᵢ Φ Ψ′}
      {u⊑ : Ψ ∣ Δᴸ ⊢ G ! ⦂ A ⊑ ★ ⊣ Δᴸ}
      {v⊑ : Ψ′ ∣ Δᴸ ⊢ H ! ⦂ C ⊑ ★ ⊣ Δᴸ}
      {p : Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ C ⊒ B ⊣ Δᴿ}
  → dualʷ (G ! , u⊑) ⨟ˡⁿ[ left ] p ≐ⁿ
      dualʷ (H ! , v⊑) ⨟ˡⁿ[ left′ ] q
  → G ≡ H
tag-prefix-matchᶜ
    {u⊑ = tag ι} {v⊑ = tag κ}
    {p = _ , idᵃ a b hA hB a⊒b}
    {q = _ , idᵃ a′ b′ hA′ hB′ a⊒b′} eq =
  cong base-tag (base-common-target a a′ b b′ a⊒b a⊒b′)
tag-prefix-matchᶜ
    {u⊑ = tag ι} {v⊑ = tag κ}
    {p = _ , gen nonvarB zero∈B p B≢★}
    {q = q} eq =
  ⊥-elim (no-base-to-all-narrowing
    (gen nonvarB zero∈B p {{freshⁿᵢ}} B≢★))
tag-prefix-matchᶜ
    {u⊑ = tag ι} {v⊑ = tag★⇒★}
    {p = _ , idᵃ (‵ .ι) (‵ μ) hA hB refl}
    {q = _ , q} eq =
  ⊥-elim (no-function-to-base-narrowing q)
tag-prefix-matchᶜ
    {u⊑ = tag ι} {v⊑ = tag★⇒★}
    {p = _ , gen nonvarB zero∈B p B≢★}
    {q = q} eq =
  ⊥-elim (no-base-to-all-narrowing
    (gen nonvarB zero∈B p {{freshⁿᵢ}} B≢★))
tag-prefix-matchᶜ
    {u⊑ = tag★⇒★} {v⊑ = tag κ}
    {p = _ , p}
    {q = _ , idᵃ (‵ .κ) (‵ μ) hA hB refl} eq =
  ⊥-elim (no-function-to-base-narrowing p)
tag-prefix-matchᶜ
    {u⊑ = tag★⇒★} {v⊑ = tag κ}
    {p = p}
    {q = _ , gen nonvarB zero∈B q B≢★} eq =
  ⊥-elim (no-base-to-all-narrowing
    (gen nonvarB zero∈B q {{freshⁿᵢ}} B≢★))
tag-prefix-matchᶜ
    {u⊑ = tag★⇒★} {v⊑ = tag★⇒★} eq =
  refl

------------------------------------------------------------------------
-- Moving a right narrowing beneath a tag prefix
------------------------------------------------------------------------

tag-prefix-compose-right-narrowing :
    ∀ {Δᴸ Δᴿ A B C G d}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {Ψ′ : ImpCtx Δᴿ Δᴿ}
      {u⊑ : idᵢ Δᴸ ∣ Δᴸ ⊢ G ! ⦂ A ⊑ ★ ⊣ Δᴸ}
      {p : Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ ★ ⊒ B ⊣ Δᴿ}
      {d⊒ : Ψ′ ∣ Δᴿ ⊢ d ⦂ B ⊒ C ⊣ Δᴿ}
  → (right : RightOneSidedᵢ Φ Ψ′)
  → Inert d
  → dualʷ (G ! , u⊑) ⨟ˡⁿ[ left-id-one-sidedᵢ ] p ≐ⁿ q
  → q ⨟ⁿ[ right ] (d , d⊒) ≐ⁿ
      dualʷ (G ! , u⊑) ⨟ˡⁿ[ left-id-one-sidedᵢ ]
        (p ⨟ⁿ[ right ] (d , d⊒))
tag-prefix-compose-right-narrowing
    {u⊑ = tag ι} {p = _ , p}
    {d⊒ = c ↦ d} right (c′ ↦ d′) eq =
  ⊥-elim (no-base-to-function-narrowing p)
tag-prefix-compose-right-narrowing
    {u⊑ = tag ι} {p = _ , p}
    {d⊒ = ∀ⁿ c} right (`∀ c′) eq =
  ⊥-elim (no-base-to-all-narrowing p)
tag-prefix-compose-right-narrowing
    {u⊑ = tag ι} {p = _ , p}
    {d⊒ = seal X⊑★} right (seal X) eq =
  ⊥-elim (no-base-to-star-narrowing p)
tag-prefix-compose-right-narrowing
    {u⊑ = tag ι}
    {p = _ , idᵃ (‵ .ι) (‵ κ) hA hB refl}
    {d⊒ = gen nonvarC zero∈C d B≢★} right (gen d′) eq =
  ⊥-elim (base-target-no-member d zero∈C)
tag-prefix-compose-right-narrowing
    {u⊑ = tag ι}
    {p = _ , gen nonvarB zero∈B p B≢★}
    {d⊒ = gen nonvarC zero∈C d B′≢★} right (gen d′) eq =
  ⊥-elim (no-base-to-all-narrowing
    (gen nonvarB zero∈B p {{freshⁿᵢ}} B≢★))
tag-prefix-compose-right-narrowing
    {u⊑ = tag★⇒★} {p = _ , p}
    {d⊒ = seal X⊑★} right (seal X) eq =
  ⊥-elim (no-function-to-star-narrowing p)
tag-prefix-compose-right-narrowing
    {u⊑ = tag★⇒★}
    {q = _ , idᵃ ★ ★ hA hB a⊒b}
    {d⊒ = gen nonvarC zero∈C d B≢★} right (gen d′) eq =
  ⊥-elim (B≢★ refl)
tag-prefix-compose-right-narrowing
    {u⊑ = tag★⇒★}
    {q = _ , untag ι}
    {d⊒ = gen nonvarC zero∈C d B≢★} right (gen d′) eq =
  ⊥-elim (base-target-no-member d zero∈C)
tag-prefix-compose-right-narrowing
    {u⊑ = tag★⇒★}
    {p = _ , ((p ︔tag★⇒★[ A≢★⇒★ ]) ↦ q)}
    {q = _ , untag★⇒★} right i eq =
  ⊥-elim (no-star-to-function-widening p)
tag-prefix-compose-right-narrowing
    {u⊑ = tag★⇒★}
    {p = _ , (p ↦ untag★⇒★︔ q [ ★⇒★≢B ])}
    {q = _ , untag★⇒★} right i eq =
  ⊥-elim (no-function-to-star-narrowing q)
tag-prefix-compose-right-narrowing
    {u⊑ = tag★⇒★}
    {q = _ , seal X⊑★}
    {d⊒ = gen nonvarC zero∈C d B≢★} right (gen d′) eq =
  ⊥-elim (variable-target-no-zero d zero∈C)
tag-prefix-compose-right-narrowing
    {u⊑ = tag★⇒★}
    {q = _ , q ︔seal X⊑★ [ ★≢B ]}
    {d⊒ = gen nonvarC zero∈C d B′≢★} right (gen d′) eq =
  ⊥-elim (variable-target-no-zero d zero∈C)
tag-prefix-compose-right-narrowing
    {u⊑ = tag★⇒★}
    {q = _ , gen nonvarB zero∈B q ★≢★}
    {d⊒ = gen nonvarC zero∈C d B≢★} right (gen d′) eq =
  ⊥-elim (★≢★ refl)
tag-prefix-compose-right-narrowing
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {u⊑ = tag★⇒★}
    {p = _ ,
      (idᵃ ★ ★ hA hB a⊒b ↦
       idᵃ ★ ★ hA′ hB′ a⊒b′)}
    {q = _ , untag★⇒★}
    {d⊒ = d₁ ↦ d₂} right (d₁′ ↦ d₂′) eq =
  wrap-untag-cong
    (recontext-from-funⁿ
      (compose-right-star (right-compose right))
      (d₁ ↦ d₂))
    (recontext-from-funⁿ (compose-right-star compose-id-left)
      (proj₂
        (composeⁿ (right-compose right)
          (idᵃ ★ ★ hA hB a⊒b ↦
           idᵃ ★ ★ hA′ hB′ a⊒b′)
          (d₁ ↦ d₂))))
    (cong₂ _↦ᶜ_
      (sym (star-right-identity-composeʷ (right-compose right) d₁
        (idᵃ ★ ★ hA hB a⊒b)))
      (sym
        (star-left-identity-composeᶜ (right-compose right)
          (idᵃ ★ ★ hA′ hB′ a⊒b′)
          d₂)))
tag-prefix-compose-right-narrowing
    {u⊑ = tag★⇒★}
    {p = _ , p₁ ↦ p₂}
    {q = _ , untag★⇒★︔ q [ ★⇒★≢B ]}
    {d⊒ = d₁ ↦ d₂} right (d₁′ ↦ d₂′) eq
    with tag-prefix-cancel
      {u⊑ = tag★⇒★}
      {p = _ , p₁ ↦ p₂}
      {q = _ , q}
      (trans eq
        (sym (function-tag-sequence q ★⇒★≢B)))
tag-prefix-compose-right-narrowing
    {u⊑ = tag★⇒★}
    {p = _ , p₁ ↦ p₂}
    {q = _ , untag★⇒★︔ q [ ★⇒★≢B ]}
    {d⊒ = d₁ ↦ d₂} right (d₁′ ↦ d₂′) eq | refl =
  wrap-untag-cong
    (proj₂
      (composeⁿ (right-compose right)
        q (d₁ ↦ d₂)))
    (recontext-from-funⁿ (compose-right-star compose-id-left)
      (proj₂
        (composeⁿ (right-compose right)
          (p₁ ↦ p₂) (d₁ ↦ d₂))))
    (composeⁿ-left-evidence (right-compose right)
      q (p₁ ↦ p₂) (d₁ ↦ d₂))
tag-prefix-compose-right-narrowing
    {u⊑ = tag★⇒★}
    {p = _ , gen nonvarB zero∈B p
      {{extensionP}} B≢★}
    {q = _ , untag★⇒★︔ q [ ★⇒★≢B ]}
    {d⊒ = ∀ⁿ d} right (`∀ d′) eq
    with tag-prefix-cancel
      {u⊑ = tag★⇒★}
      {p = _ , gen nonvarB zero∈B p
        {{extensionP}} B≢★}
      {q = _ , q}
      (trans eq
        (sym (function-tag-sequence q ★⇒★≢B)))
tag-prefix-compose-right-narrowing
    {u⊑ = tag★⇒★}
    {p = _ , gen nonvarB zero∈B p
      {{extensionP}} B≢★}
    {q = _ , untag★⇒★︔ q [ ★⇒★≢B ]}
    {d⊒ = ∀ⁿ d} right (`∀ d′) eq | refl =
  trans
    (cong (λ c → (★⇒★ ？) ︔ᶜ c)
      (composeⁿ-left-evidence (right-compose right)
        q (gen nonvarB zero∈B p {{extensionP}} B≢★) (∀ⁿ d)))
    (sym
      (function-tag-sequence
        (proj₂
          (composeⁿ (right-compose right)
            (gen nonvarB zero∈B p {{extensionP}} B≢★) (∀ⁿ d)))
        (λ ())))
tag-prefix-compose-right-narrowing
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {u⊑ = tag★⇒★}
    {p = _ ,
      (idᵃ ★ ★ hA hB a⊒b ↦
       idᵃ ★ ★ hA′ hB′ a⊒b′)}
    {q = _ , untag★⇒★}
    {d⊒ = gen nonvarC zero∈C d B≢★} right (gen d′) eq =
  cong (λ c → (★⇒★ ？) ︔ᶜ Coercions.gen c)
    (sym
      (function-left-identity-composeᶜ
        (keepᴿ (right-compose right))
        (idᵃ ★ ★ hA hB a⊒b ↦
         idᵃ ★ ★ hA′ hB′ a⊒b′)
        d))
tag-prefix-compose-right-narrowing
    {u⊑ = tag★⇒★}
    {p = _ , p₁ ↦ p₂}
    {q = _ , untag★⇒★︔ q [ ★⇒★≢B ]}
    {d⊒ = gen nonvarC zero∈C d B′≢★} right (gen d′) eq
    with tag-prefix-cancel
      {u⊑ = tag★⇒★}
      {p = _ , p₁ ↦ p₂}
      {q = _ , q}
      (trans eq
        (sym (function-tag-sequence q ★⇒★≢B)))
tag-prefix-compose-right-narrowing
    {u⊑ = tag★⇒★}
    {p = _ , p₁ ↦ p₂}
    {q = _ , untag★⇒★︔ q [ ★⇒★≢B ]}
    {d⊒ = gen nonvarC zero∈C d B′≢★}
    right (gen d′) eq | refl =
  trans
    (cong (λ c → (★⇒★ ？) ︔ᶜ c)
      (composeⁿ-left-evidence (right-compose right)
        q (p₁ ↦ p₂)
        (gen nonvarC zero∈C d B′≢★)))
    (sym
      (function-tag-sequence
        (proj₂
          (composeⁿ (right-compose right)
            (p₁ ↦ p₂)
            (gen nonvarC zero∈C d {{freshⁿᵢ}} B′≢★)))
        (λ ())))
tag-prefix-compose-right-narrowing
    {u⊑ = tag★⇒★}
    {p = _ , gen nonvarB zero∈B p
      {{extensionP}} B≢★}
    {q = _ , untag★⇒★︔ q [ ★⇒★≢B ]}
    {d⊒ = gen nonvarC zero∈C d
      {{extensionD}} B′≢★} right (gen d′) eq
    with tag-prefix-cancel
      {u⊑ = tag★⇒★}
      {p = _ , gen nonvarB zero∈B p
        {{extensionP}} B≢★}
      {q = _ , q}
      (trans eq
        (sym (function-tag-sequence q ★⇒★≢B)))
tag-prefix-compose-right-narrowing
    {u⊑ = tag★⇒★}
    {p = _ , gen nonvarB zero∈B p
      {{extensionP}} B≢★}
    {q = _ , untag★⇒★︔ q [ ★⇒★≢B ]}
    {d⊒ = gen nonvarC zero∈C d
      {{extensionD}} B′≢★}
    right (gen d′) eq | refl =
  trans
    (cong (λ c → (★⇒★ ？) ︔ᶜ c)
      (composeⁿ-left-evidence (right-compose right)
        q (gen nonvarB zero∈B p {{extensionP}} B≢★)
        (gen nonvarC zero∈C d {{extensionD}} B′≢★)))
    (sym
      (function-tag-sequence
        (proj₂
          (composeⁿ (right-compose right)
            (gen nonvarB zero∈B p {{extensionP}} B≢★)
            (gen nonvarC zero∈C d {{extensionD}} B′≢★)))
        (λ ())))

tag-factor-right-narrowing :
    ∀ {Δᴸ Δᴿ A B C G d}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {Ψ′ : ImpCtx Δᴿ Δᴿ}
      {u⊑ : idᵢ Δᴸ ∣ Δᴸ ⊢ G ! ⦂ A ⊑ ★ ⊣ Δᴸ}
      {q : Φ ∣ Δᴸ ⊢ ★ ⊒ B ⊣ Δᴿ}
      {r : Φ ∣ Δᴸ ⊢ ★ ⊒ C ⊣ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ A ⊒ C ⊣ Δᴿ}
  → (right : RightOneSidedᵢ Φ Ψ′)
  → (d⊒ : Ψ′ ∣ Δᴿ ⊢ d ⦂ B ⊒ C ⊣ Δᴿ)
  → Inert d
  → q ⨟ⁿ[ right ] (d , d⊒) ≐ⁿ r
  → dualʷ (G ! , u⊑) ⨟ˡⁿ[ left-id-one-sidedᵢ ] p ≐ⁿ r
  → Σ[ s ∈ (Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ) ]
      (dualʷ (G ! , u⊑)
        ⨟ˡⁿ[ left-id-one-sidedᵢ ] s ≐ⁿ q)
    × (s ⨟ⁿ[ right ] (d , d⊒) ≐ⁿ p)
tag-factor-right-narrowing
    {u⊑ = tag ι} {p = _ , p}
    right (c ↦ d) (c′ ↦ d′) eq′ eq =
  ⊥-elim (no-base-to-function-narrowing p)
tag-factor-right-narrowing
    {u⊑ = tag ι} {p = _ , p}
    right (∀ⁿ c) (`∀ c′) eq′ eq =
  ⊥-elim (no-base-to-all-narrowing p)
tag-factor-right-narrowing
    {u⊑ = tag ι} {p = _ , p}
    right (seal X⊑★) (seal X) eq′ eq =
  ⊥-elim (no-base-to-variable-narrowing p)
tag-factor-right-narrowing
    {u⊑ = tag ι} {p = _ , p}
    right (gen nonvarC zero∈C d B≢★) (gen d′) eq′ eq =
  ⊥-elim (no-base-to-all-narrowing p)
tag-factor-right-narrowing
    {u⊑ = tag★⇒★}
    {q = _ , idᵃ ★ ★ hA hB a⊒b}
    {p = _ , p}
    right (seal X⊑★) (seal X) eq′ eq =
  ⊥-elim (no-function-to-variable-narrowing p)
tag-factor-right-narrowing
    {u⊑ = tag★⇒★}
    {q = _ , idᵃ ★ ★ hA hB a⊒b}
    right (gen nonvarC zero∈C d ★≢★) (gen d′) eq′ eq =
  ⊥-elim (★≢★ refl)
tag-factor-right-narrowing
    {u⊑ = tag★⇒★}
    {q = _ , untag ι}
    right (gen nonvarC zero∈C d B≢★) (gen d′) eq′ eq =
  ⊥-elim (base-target-no-member d zero∈C)
tag-factor-right-narrowing
    {u⊑ = tag★⇒★}
    {q = _ , seal X⊑★}
    right (gen nonvarC zero∈C d B≢★) (gen d′) eq′ eq =
  ⊥-elim (variable-target-no-zero d zero∈C)
tag-factor-right-narrowing
    {u⊑ = tag★⇒★}
    {q = _ , q ︔seal X⊑★ [ ★≢B ]}
    right (gen nonvarC zero∈C d B′≢★) (gen d′) eq′ eq =
  ⊥-elim (variable-target-no-zero d zero∈C)
tag-factor-right-narrowing
    {u⊑ = tag★⇒★}
    {q = _ , gen nonvarB zero∈B q ★≢★}
    right d⊒ i eq′ eq =
  ⊥-elim (★≢★ refl)
tag-factor-right-narrowing
    {u⊑ = tag★⇒★}
    {q = _ , untag★⇒★}
    {p = p}
    right d⊒ i eq′ eq =
  (_ , fun-idⁿ) , refl ,
  tag-prefix-cancel
    {u⊑ = tag★⇒★}
    {p = (_ , fun-idⁿ) ⨟ⁿ[ right ] (_ , d⊒)}
    {q = p}
    (trans
      (sym
        (tag-prefix-compose-right-narrowing
          {u⊑ = tag★⇒★}
          {p = _ , fun-idⁿ}
          {q = _ , untag★⇒★}
          {d⊒ = d⊒} right i refl))
      (trans eq′ (sym eq)))
tag-factor-right-narrowing
    {u⊑ = tag★⇒★}
    {q = _ , untag★⇒★︔ q [ ★⇒★≢B ]}
    {p = p}
    right d⊒ i eq′ eq =
  (_ , q) , function-tag-sequence q ★⇒★≢B ,
  tag-prefix-cancel
    {u⊑ = tag★⇒★}
    {p = (_ , q) ⨟ⁿ[ right ] (_ , d⊒)}
    {q = p}
    (trans
      (sym
        (tag-prefix-compose-right-narrowing
          {u⊑ = tag★⇒★}
          {p = _ , q}
          {q = _ , untag★⇒★︔ q [ ★⇒★≢B ]}
          {d⊒ = d⊒} right i
          (function-tag-sequence q ★⇒★≢B)))
      (trans eq′ (sym eq)))

------------------------------------------------------------------------
-- Moving a right widening beneath a tag prefix
------------------------------------------------------------------------

tag-prefix-compose-right-widening :
    ∀ {Δᴸ Δᴿ A B C G u′}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {Ψ′ : ImpCtx Δᴿ Δᴿ}
      {u⊑ : idᵢ Δᴸ ∣ Δᴸ ⊢ G ! ⦂ A ⊑ ★ ⊣ Δᴸ}
      {p : Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ ★ ⊒ B ⊣ Δᴿ}
      {u′⊑ : Ψ′ ∣ Δᴿ ⊢ u′ ⦂ C ⊑ B ⊣ Δᴿ}
  → (comp′ : RightOneSidedᵢ Φ Ψ′)
  → Inert u′
  → dualʷ (G ! , u⊑) ⨟ˡⁿ[ left-id-one-sidedᵢ ] p ≐ⁿ q
  → q ⨟ⁿ[ comp′ ] dualʷ (u′ , u′⊑) ≐ⁿ
      dualʷ (G ! , u⊑) ⨟ˡⁿ[ left-id-one-sidedᵢ ]
        (p ⨟ⁿ[ comp′ ] dualʷ (u′ , u′⊑))
tag-prefix-compose-right-widening
    {u⊑ = tag ι} {p = _ , p}
    {u′⊑ = tag κ} comp′ ((‵ .κ) !) eq =
  ⊥-elim (no-base-to-star-narrowing p)
tag-prefix-compose-right-widening
    {u⊑ = tag ι} {p = _ , p}
    {u′⊑ = tag★⇒★} comp′ (★⇒★ !) eq =
  ⊥-elim (no-base-to-star-narrowing p)
tag-prefix-compose-right-widening
    {u⊑ = tag ι} {p = _ , p}
    {u′⊑ = c ↦ d} comp′ (c′ ↦ d′) eq =
  ⊥-elim (no-base-to-function-narrowing p)
tag-prefix-compose-right-widening
    {u⊑ = tag ι} {p = _ , p}
    {u′⊑ = ∀ʷ c} comp′ (`∀ c′) eq =
  ⊥-elim (no-base-to-all-narrowing p)
tag-prefix-compose-right-widening
    {u⊑ = tag★⇒★} {p = _ , p}
    {u′⊑ = tag κ} comp′ ((‵ .κ) !) eq =
  ⊥-elim (no-function-to-star-narrowing p)
tag-prefix-compose-right-widening
    {u⊑ = tag★⇒★} {p = _ , p}
    {u′⊑ = tag★⇒★} comp′ (★⇒★ !) eq =
  ⊥-elim (no-function-to-star-narrowing p)
tag-prefix-compose-right-widening
    {C = A ⇒ B} {u⊑ = tag★⇒★}
    {p = _ ,
      (idᵃ ★ ★ hA hB a⊒b ↦
       idᵃ ★ ★ hA′ hB′ a⊒b′)}
    {q = _ , untag★⇒★}
    {u′⊑ = c ↦ d} comp′ (c′ ↦ d′) eq
    with ★ ≟Ty A | ★ ≟Ty B
tag-prefix-compose-right-widening
    {u⊑ = tag★⇒★}
    {p = _ ,
      (idᵃ ★ ★ hA hB a⊒b ↦
       idᵃ ★ ★ hA′ hB′ a⊒b′)}
    {q = _ , untag★⇒★}
    {u′⊑ = c ↦ d} comp′ (c′ ↦ d′) eq
    | yes refl | yes refl =
  refl
tag-prefix-compose-right-widening
    {u⊑ = tag★⇒★}
    {p = _ ,
      (idᵃ ★ ★ hA hB a⊒b ↦
       idᵃ ★ ★ hA′ hB′ a⊒b′)}
    {q = _ , untag★⇒★}
    {u′⊑ = c ↦ d} comp′ (c′ ↦ d′) eq
    | yes ★≡A | no ★≢B =
  cong (λ e → (★⇒★ ？) ︔ᶜ e)
    (cong₂ _↦ᶜ_
      (sym (star-right-identity-composeʷ (right-compose comp′)
        (proj₂ (dualⁿ (c′ , c)))
        (idᵃ ★ ★ hA hB a⊒b)))
      (sym (star-left-identity-composeᶜ (right-compose comp′)
        (idᵃ ★ ★ hA′ hB′ a⊒b′)
        (proj₂ (dualʷ (d′ , d))))))
tag-prefix-compose-right-widening
    {u⊑ = tag★⇒★}
    {p = _ ,
      (idᵃ ★ ★ hA hB a⊒b ↦
       idᵃ ★ ★ hA′ hB′ a⊒b′)}
    {q = _ , untag★⇒★}
    {u′⊑ = c ↦ d} comp′ (c′ ↦ d′) eq
    | no ★≢A | yes ★≡B =
  cong (λ e → (★⇒★ ？) ︔ᶜ e)
    (cong₂ _↦ᶜ_
      (sym (star-right-identity-composeʷ (right-compose comp′)
        (proj₂ (dualⁿ (c′ , c)))
        (idᵃ ★ ★ hA hB a⊒b)))
      (sym (star-left-identity-composeᶜ (right-compose comp′)
        (idᵃ ★ ★ hA′ hB′ a⊒b′)
        (proj₂ (dualʷ (d′ , d))))))
tag-prefix-compose-right-widening
    {u⊑ = tag★⇒★}
    {p = _ ,
      (idᵃ ★ ★ hA hB a⊒b ↦
       idᵃ ★ ★ hA′ hB′ a⊒b′)}
    {q = _ , untag★⇒★}
    {u′⊑ = c ↦ d} comp′ (c′ ↦ d′) eq
    | no ★≢A | no ★≢B =
  cong (λ e → (★⇒★ ？) ︔ᶜ e)
    (cong₂ _↦ᶜ_
      (sym (star-right-identity-composeʷ (right-compose comp′)
        (proj₂ (dualⁿ (c′ , c)))
        (idᵃ ★ ★ hA hB a⊒b)))
      (sym (star-left-identity-composeᶜ (right-compose comp′)
        (idᵃ ★ ★ hA′ hB′ a⊒b′)
        (proj₂ (dualʷ (d′ , d))))))
tag-prefix-compose-right-widening
    {u⊑ = tag★⇒★}
    {p = _ , ((p ︔tag★⇒★[ A≢★⇒★ ]) ↦ q)}
    {q = _ , untag★⇒★}
    {u′⊑ = c ↦ d} comp′ (c′ ↦ d′) eq =
  ⊥-elim (no-star-to-function-widening p)
tag-prefix-compose-right-widening
    {u⊑ = tag★⇒★}
    {p = _ , (p ↦ untag★⇒★︔ q [ ★⇒★≢B ])}
    {q = _ , untag★⇒★}
    {u′⊑ = c ↦ d} comp′ (c′ ↦ d′) eq =
  ⊥-elim (no-function-to-star-narrowing q)
tag-prefix-compose-right-widening
    {u⊑ = tag★⇒★}
    {p = _ , p₁ ↦ p₂}
    {q = _ , untag★⇒★︔ q [ ★⇒★≢B ]}
    {u′⊑ = c ↦ d} comp′ (c′ ↦ d′) eq
    with tag-prefix-cancel
      {u⊑ = tag★⇒★}
      {p = _ , p₁ ↦ p₂}
      {q = _ , q}
      (trans eq
        (sym (function-tag-sequence q ★⇒★≢B)))
tag-prefix-compose-right-widening
    {Φ = Φ} {u⊑ = tag★⇒★}
    {p = _ , p₁ ↦ p₂}
    {q = _ , untag★⇒★︔ q [ ★⇒★≢B ]}
    {u′⊑ = c ↦ d} comp′ (c′ ↦ d′) eq | refl =
  wrap-untag-cong
    (proj₂
      (composeⁿ (right-compose comp′)
        q (proj₂ (dualʷ (c′ ↦ᶜ d′ , c ↦ d)))))
    (recontext-from-funⁿ {Φ = Φ} {Ψ = Φ}
      (compose-right-star compose-id-left)
      (proj₂
        (composeⁿ (right-compose comp′)
          (p₁ ↦ p₂)
          (proj₂
            (dualʷ (c′ ↦ᶜ d′ , c ↦ d))))))
    (composeⁿ-left-evidence (right-compose comp′)
      q (p₁ ↦ p₂)
      (proj₂ (dualʷ (c′ ↦ᶜ d′ , c ↦ d))))
tag-prefix-compose-right-widening
    {u⊑ = tag★⇒★}
    {p = _ , gen nonvarA zero∈A p
      {{extensionP}} B≢★}
    {q = _ , untag★⇒★︔ q [ ★⇒★≢B ]}
    {u′⊑ = ∀ʷ c} comp′ (`∀ c′) eq
    with tag-prefix-cancel
      {u⊑ = tag★⇒★}
      {p = _ , gen nonvarA zero∈A p
        {{extensionP}} B≢★}
      {q = _ , q}
      (trans eq
        (sym (function-tag-sequence q ★⇒★≢B)))
tag-prefix-compose-right-widening
    {u⊑ = tag★⇒★}
    {p = _ , gen nonvarA zero∈A p
      {{extensionP}} B≢★}
    {q = _ , untag★⇒★︔ q [ ★⇒★≢B ]}
    {u′⊑ = ∀ʷ c} comp′ (`∀ c′) eq | refl =
  trans
    (cong (λ c → (★⇒★ ？) ︔ᶜ c)
      (composeⁿ-left-evidence (right-compose comp′)
        q (gen nonvarA zero∈A p {{extensionP}} B≢★)
        (proj₂ (dualʷ (`∀ c′ , ∀ʷ c)))))
    (sym
      (function-tag-sequence
        (proj₂
          (composeⁿ (right-compose comp′)
            (gen nonvarA zero∈A p {{extensionP}} B≢★)
            (proj₂ (dualʷ (`∀ c′ , ∀ʷ c)))))
        (λ ())))

------------------------------------------------------------------------
-- Left widening tag inversion
------------------------------------------------------------------------

left-widening-tag-inversion :
    ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ V V′ A B G}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {σ : Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ}
      {γ : Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ}
      {u⊑ : idᵢ Δᴸ ∣ Δᴸ ⊢ G ! ⦂ A ⊑ ★ ⊣ Δᴸ}
      {r : Φ ∣ Δᴸ ⊢ ★ ⊒ B ⊣ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ}
  → Value V
  → Value V′
  → Φ ∣ Δᴸ ∣ Δᴿ ∣ σ ∣ γ
      ⊢ᴺ V ⟨ G ! ⟩ ⊒ V′ ⦂ ★ ⊒ B ∶ r
  → dualʷ (G ! , u⊑) ⨟ˡⁿ[ left-id-one-sidedᵢ ] p ≐ⁿ r
  → Σ[ p′ ∈ (Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ) ]
      (p′ ≐ⁿ p)
    × (Φ ∣ Δᴸ ∣ Δᴿ ∣ σ ∣ γ
        ⊢ᴺ V ⊒ V′ ⦂ A ⊒ B ∶ p′)
left-widening-tag-inversion vV ()
  (⊒blame M⊢) eq
left-widening-tag-inversion {u⊑ = tag ι} {r = r} {p = p}
    vV (vV′ ⟨ iu′ ⟩)
    (up⊒up {u⊑ = tag ι} {u′⊑ = u′⊑}
      (down⊒down {p = p₀} {d⊒ = d⊒} {d′⊒ = d′⊒}
        {q = q} M⊒M′ leftD rightD d⊢ d′⊢ eqDown)
      leftU rightU u⊢ u′⊢ eqUp) eq =
  p , refl ,
  ⊒castʷ {u′⊑ = u′⊑} {p = q} {q = p}
    rightU u′⊢
    (castⁿ⊒castⁿ {left = leftD} {right = rightD}
      {s⊒ = d⊒} {t⊒ = d′⊒}
      M⊒M′ d⊢ d′⊢ eqDown)
    (sym
      (tag-prefix-cancelᶜ
        {left = leftU}
        {left′ = left-id-one-sidedᵢ}
        {u⊑ = tag ι}
        {v⊑ = tag ι}
        {p = q}
        {q = p ⨟ⁿ[ rightU ] dualʷ (_ , u′⊑)}
        (trans eqUp
          (tag-prefix-compose-right-widening
            {u⊑ = tag ι} {p = p} {q = r}
            {u′⊑ = u′⊑} rightU iu′ eq))))
left-widening-tag-inversion {u⊑ = tag★⇒★} {r = r} {p = p}
    vV (vV′ ⟨ iu′ ⟩)
    (up⊒up {u⊑ = tag★⇒★} {u′⊑ = u′⊑}
      (down⊒down {p = p₀} {d⊒ = d⊒} {d′⊒ = d′⊒}
        {q = q} M⊒M′ leftD rightD d⊢ d′⊢ eqDown)
      leftU rightU u⊢ u′⊢ eqUp) eq =
  p , refl ,
  ⊒castʷ {u′⊑ = u′⊑} {p = q} {q = p}
    rightU u′⊢
    (castⁿ⊒castⁿ {left = leftD} {right = rightD}
      {s⊒ = d⊒} {t⊒ = d′⊒}
      M⊒M′ d⊢ d′⊢ eqDown)
    (sym
      (tag-prefix-cancelᶜ
        {left = leftU}
        {left′ = left-id-one-sidedᵢ}
        {u⊑ = tag★⇒★}
        {v⊑ = tag★⇒★}
        {p = q}
        {q = p ⨟ⁿ[ rightU ] dualʷ (_ , u′⊑)}
        (trans eqUp
          (tag-prefix-compose-right-widening
            {u⊑ = tag★⇒★} {p = p} {q = r}
            {u′⊑ = u′⊑} rightU iu′ eq))))
left-widening-tag-inversion {u⊑ = tag ι} {p = p}
    vV vV′
    (castʷ⊒ {u⊑ = tag .ι} {p = p′}
      left′ u⊢ V⊒V′ eq′) eq =
  p′ , tag-prefix-cancelᶜ
    {left = left′} {left′ = left-id-one-sidedᵢ}
    {u⊑ = tag ι} {v⊑ = tag ι} {p = p′} {q = p}
    (trans eq′ (sym eq)) , V⊒V′
left-widening-tag-inversion {u⊑ = tag★⇒★} {p = p}
    vV vV′
    (castʷ⊒ {u⊑ = tag★⇒★} {p = p′}
      left′ u⊢ V⊒V′ eq′) eq =
  p′ , tag-prefix-cancelᶜ
    {left = left′} {left′ = left-id-one-sidedᵢ}
    {u⊑ = tag★⇒★} {v⊑ = tag★⇒★} {p = p′} {q = p}
    (trans eq′ (sym eq)) , V⊒V′
left-widening-tag-inversion vV vV′
    (⊒Λ {B≢★ = B≢★}
      extension preservation vV″ V⊒V″) eq =
  ⊥-elim (B≢★ refl)
left-widening-tag-inversion vV vV′
    (⊒⟨ν⟩ {B≢★ = B≢★}
      vV″ V″⊢ hC c⊢ V⊒V″) eq =
  ⊥-elim (B≢★ refl)
left-widening-tag-inversion {u⊑ = u⊑} {p = p}
    vV (vV′ ⟨ id′ ⟩)
    (⊒castⁿ {d′ = d′} {d′⊒ = d′⊒}
      {p = p₀} {q = r} right′ d′⊢ V⊒V′ eq′) eq
    with tag-factor-right-narrowing
      {u⊑ = u⊑} {q = p₀} {r = r} {p = p}
      right′ d′⊒ id′ eq′ eq
left-widening-tag-inversion {u⊑ = u⊑} {p = p}
    vV (vV′ ⟨ id′ ⟩)
    (⊒castⁿ {d′ = d′} {d′⊒ = d′⊒}
      {p = p₀} {q = r} right′ d′⊢ V⊒V′ eq′) eq
    | (s , s⊒) , prefix , suffix
    with left-widening-tag-inversion
      {u⊑ = u⊑} {p = s , s⊒}
      vV vV′ V⊒V′ prefix
left-widening-tag-inversion {p = p}
    vV (vV′ ⟨ id′ ⟩)
    (⊒castⁿ {d′⊒ = d′⊒}
      right′ d′⊢ V⊒V′ eq′) eq
    | (s , s⊒) , prefix , suffix
    | (.s , s′⊒) , refl , V⊒V″ =
  p , refl ,
  ⊒castⁿ {d′⊒ = d′⊒} {p = s , s′⊒} {q = p}
    right′ d′⊢ V⊒V″
    (trans
      (composeⁿ-left-evidence (right-compose right′)
        s′⊒ s⊒ d′⊒)
      suffix)
left-widening-tag-inversion {u⊑ = u⊑} {p = p}
    vV (vV″ ⟨ iu′ ⟩)
    (⊒castʷ {u′ = u′} {u′⊑ = u′⊑}
      {p = p₀} {q = r} right′ u′⊢ V⊒V′ eq′) eq
    with left-widening-tag-inversion
      {u⊑ = u⊑}
      {p = p ⨟ⁿ[ right′ ] dualʷ (u′ , u′⊑)}
      vV vV″ V⊒V′
      (trans
        (sym
          (tag-prefix-compose-right-widening
            {u⊑ = u⊑} {p = p} {q = r}
            {u′⊑ = u′⊑} right′ iu′ eq))
        eq′)
... | p′ , p′≐p⨟u′ , V⊒V″ =
  p , refl ,
  ⊒castʷ {u′⊑ = u′⊑} {p = p′} {q = p}
    right′ u′⊢ V⊒V″ (sym p′≐p⨟u′)

------------------------------------------------------------------------
-- Left widening tag inversion with a separately supplied tag
------------------------------------------------------------------------

left-widening-tag-inversion-match :
    ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ V V′ C B G H}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {σ : Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ}
      {γ : Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ}
      {v⊑ : idᵢ Δᴸ ∣ Δᴸ ⊢ H ! ⦂ C ⊑ ★ ⊣ Δᴸ}
      {r : Φ ∣ Δᴸ ⊢ ★ ⊒ B ⊣ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ C ⊒ B ⊣ Δᴿ}
  → Value V
  → Value V′
  → Φ ∣ Δᴸ ∣ Δᴿ ∣ σ ∣ γ
      ⊢ᴺ V ⟨ G ! ⟩ ⊒ V′ ⦂ ★ ⊒ B ∶ r
  → dualʷ (H ! , v⊑) ⨟ˡⁿ[ left-id-one-sidedᵢ ] p ≐ⁿ r
  → Σ[ G≡H ∈ G ≡ H ]
      Σ[ p′ ∈ (Φ ∣ Δᴸ ⊢ C ⊒ B ⊣ Δᴿ) ]
        (p′ ≐ⁿ p)
      × (Φ ∣ Δᴸ ∣ Δᴿ ∣ σ ∣ γ
          ⊢ᴺ V ⊒ V′ ⦂ C ⊒ B ∶ p′)
left-widening-tag-inversion-match vV ()
    (⊒blame M⊢) eq
left-widening-tag-inversion-match {v⊑ = tag κ} {r = r} {p = p}
    vV (vV′ ⟨ iu′ ⟩)
    (up⊒up {u⊑ = tag ι} {u′⊑ = u′⊑}
      (down⊒down {p = p₀} {d⊒ = d⊒} {d′⊒ = d′⊒}
        {q = q} M⊒M′ leftD rightD d⊢ d′⊢ eqDown)
      leftU rightU u⊢ u′⊢ eqUp) eq
    with tag-prefix-matchᶜ
      {left = leftU} {left′ = left-id-one-sidedᵢ}
      {u⊑ = tag ι} {v⊑ = tag κ}
      {p = q}
      {q = p ⨟ⁿ[ rightU ] dualʷ (_ , u′⊑)}
      (trans eqUp
        (tag-prefix-compose-right-widening
          {u⊑ = tag κ} {p = p} {q = r}
          {u′⊑ = u′⊑} rightU iu′ eq))
left-widening-tag-inversion-match {v⊑ = tag κ} {r = r} {p = p}
    vV (vV′ ⟨ iu′ ⟩)
    (up⊒up {u⊑ = tag ι} {u′⊑ = u′⊑}
      (down⊒down {p = p₀} {d⊒ = d⊒} {d′⊒ = d′⊒}
        {q = q} M⊒M′ leftD rightD d⊢ d′⊢ eqDown)
      leftU rightU u⊢ u′⊢ eqUp) eq | refl =
  refl , p , refl ,
  ⊒castʷ {u′⊑ = u′⊑} {p = q} {q = p}
    rightU u′⊢
    (castⁿ⊒castⁿ {left = leftD} {right = rightD}
      {s⊒ = d⊒} {t⊒ = d′⊒}
      M⊒M′ d⊢ d′⊢ eqDown)
    (sym
      (tag-prefix-cancelᶜ
        {left = leftU} {left′ = left-id-one-sidedᵢ}
        {u⊑ = tag κ}
        {v⊑ = tag κ}
        {p = q}
        {q = p ⨟ⁿ[ rightU ] dualʷ (_ , u′⊑)}
        (trans eqUp
          (tag-prefix-compose-right-widening
            {u⊑ = tag κ} {p = p} {q = r}
            {u′⊑ = u′⊑} rightU iu′ eq))))
left-widening-tag-inversion-match {v⊑ = tag★⇒★} {r = r} {p = p}
    vV (vV′ ⟨ iu′ ⟩)
    (up⊒up {u⊑ = tag ι} {u′⊑ = u′⊑}
      (down⊒down {p = p₀} {d⊒ = d⊒} {d′⊒ = d′⊒}
        {q = q} M⊒M′ leftD rightD d⊢ d′⊢ eqDown)
      leftU rightU u⊢ u′⊢ eqUp) eq
    with tag-prefix-matchᶜ
      {left = leftU} {left′ = left-id-one-sidedᵢ}
      {u⊑ = tag ι} {v⊑ = tag★⇒★}
      {p = q}
      {q = p ⨟ⁿ[ rightU ] dualʷ (_ , u′⊑)}
      (trans eqUp
        (tag-prefix-compose-right-widening
          {u⊑ = tag★⇒★} {p = p} {q = r}
          {u′⊑ = u′⊑} rightU iu′ eq))
left-widening-tag-inversion-match {v⊑ = tag★⇒★} {r = r} {p = p}
    vV (vV′ ⟨ iu′ ⟩)
    (up⊒up {u⊑ = tag ι} {u′⊑ = u′⊑}
      (down⊒down {p = p₀} {d⊒ = d⊒} {d′⊒ = d′⊒}
        {q = q} M⊒M′ leftD rightD d⊢ d′⊢ eqDown)
      leftU rightU u⊢ u′⊢ eqUp) eq | ()
left-widening-tag-inversion-match {v⊑ = tag ι} {r = r} {p = p}
    vV (vV′ ⟨ iu′ ⟩)
    (up⊒up {u⊑ = tag★⇒★} {u′⊑ = u′⊑}
      (down⊒down {p = p₀} {d⊒ = d⊒} {d′⊒ = d′⊒}
        {q = q} M⊒M′ leftD rightD d⊢ d′⊢ eqDown)
      leftU rightU u⊢ u′⊢ eqUp) eq
    with tag-prefix-matchᶜ
      {left = leftU} {left′ = left-id-one-sidedᵢ}
      {u⊑ = tag★⇒★} {v⊑ = tag ι}
      {p = q}
      {q = p ⨟ⁿ[ rightU ] dualʷ (_ , u′⊑)}
      (trans eqUp
        (tag-prefix-compose-right-widening
          {u⊑ = tag ι} {p = p} {q = r}
          {u′⊑ = u′⊑} rightU iu′ eq))
left-widening-tag-inversion-match {v⊑ = tag ι} {r = r} {p = p}
    vV (vV′ ⟨ iu′ ⟩)
    (up⊒up {u⊑ = tag★⇒★} {u′⊑ = u′⊑}
      (down⊒down {p = p₀} {d⊒ = d⊒} {d′⊒ = d′⊒}
        {q = q} M⊒M′ leftD rightD d⊢ d′⊢ eqDown)
      leftU rightU u⊢ u′⊢ eqUp) eq | ()
left-widening-tag-inversion-match {v⊑ = tag★⇒★} {r = r} {p = p}
    vV (vV′ ⟨ iu′ ⟩)
    (up⊒up {u⊑ = tag★⇒★} {u′⊑ = u′⊑}
      (down⊒down {p = p₀} {d⊒ = d⊒} {d′⊒ = d′⊒}
        {q = q} M⊒M′ leftD rightD d⊢ d′⊢ eqDown)
      leftU rightU u⊢ u′⊢ eqUp) eq
    with tag-prefix-matchᶜ
      {left = leftU} {left′ = left-id-one-sidedᵢ}
      {u⊑ = tag★⇒★} {v⊑ = tag★⇒★}
      {p = q}
      {q = p ⨟ⁿ[ rightU ] dualʷ (_ , u′⊑)}
      (trans eqUp
        (tag-prefix-compose-right-widening
          {u⊑ = tag★⇒★} {p = p} {q = r}
          {u′⊑ = u′⊑} rightU iu′ eq))
left-widening-tag-inversion-match {v⊑ = tag★⇒★} {r = r} {p = p}
    vV (vV′ ⟨ iu′ ⟩)
    (up⊒up {u⊑ = tag★⇒★} {u′⊑ = u′⊑}
      (down⊒down {p = p₀} {d⊒ = d⊒} {d′⊒ = d′⊒}
        {q = q} M⊒M′ leftD rightD d⊢ d′⊢ eqDown)
      leftU rightU u⊢ u′⊢ eqUp) eq | refl =
  refl , p , refl ,
  ⊒castʷ {u′⊑ = u′⊑} {p = q} {q = p}
    rightU u′⊢
    (castⁿ⊒castⁿ {left = leftD} {right = rightD}
      {s⊒ = d⊒} {t⊒ = d′⊒}
      M⊒M′ d⊢ d′⊢ eqDown)
    (sym
      (tag-prefix-cancelᶜ
        {left = leftU} {left′ = left-id-one-sidedᵢ}
        {u⊑ = tag★⇒★}
        {v⊑ = tag★⇒★}
        {p = q}
        {q = p ⨟ⁿ[ rightU ] dualʷ (_ , u′⊑)}
        (trans eqUp
          (tag-prefix-compose-right-widening
            {u⊑ = tag★⇒★} {p = p} {q = r}
            {u′⊑ = u′⊑} rightU iu′ eq))))
left-widening-tag-inversion-match {v⊑ = tag κ} {p = p}
    vV vV′
    (castʷ⊒ {u⊑ = tag ι} {p = p′}
      left′ u⊢ V⊒V′ eq′) eq
    with tag-prefix-matchᶜ
      {left = left′} {left′ = left-id-one-sidedᵢ}
      {u⊑ = tag ι} {v⊑ = tag κ} {p = p′} {q = p}
      (trans eq′ (sym eq))
left-widening-tag-inversion-match {v⊑ = tag κ} {p = p}
    vV vV′
    (castʷ⊒ {u⊑ = tag ι} {p = p′}
      left′ u⊢ V⊒V′ eq′) eq | refl =
  refl , p′ ,
  tag-prefix-cancelᶜ
    {left = left′} {left′ = left-id-one-sidedᵢ}
    {u⊑ = tag κ} {v⊑ = tag κ} {p = p′} {q = p}
    (trans eq′ (sym eq)) ,
  V⊒V′
left-widening-tag-inversion-match {v⊑ = tag★⇒★} {p = p}
    vV vV′
    (castʷ⊒ {u⊑ = tag ι} {p = p′}
      left′ u⊢ V⊒V′ eq′) eq
    with tag-prefix-matchᶜ
      {left = left′} {left′ = left-id-one-sidedᵢ}
      {u⊑ = tag ι} {v⊑ = tag★⇒★} {p = p′} {q = p}
      (trans eq′ (sym eq))
left-widening-tag-inversion-match {v⊑ = tag★⇒★} {p = p}
    vV vV′
    (castʷ⊒ {u⊑ = tag ι} {p = p′}
      left′ u⊢ V⊒V′ eq′) eq | ()
left-widening-tag-inversion-match {v⊑ = tag κ} {p = p}
    vV vV′
    (castʷ⊒ {u⊑ = tag★⇒★} {p = p′}
      left′ u⊢ V⊒V′ eq′) eq
    with tag-prefix-matchᶜ
      {left = left′} {left′ = left-id-one-sidedᵢ}
      {u⊑ = tag★⇒★} {v⊑ = tag κ} {p = p′} {q = p}
      (trans eq′ (sym eq))
left-widening-tag-inversion-match {v⊑ = tag κ} {p = p}
    vV vV′
    (castʷ⊒ {u⊑ = tag★⇒★} {p = p′}
      left′ u⊢ V⊒V′ eq′) eq | ()
left-widening-tag-inversion-match {v⊑ = tag★⇒★} {p = p}
    vV vV′
    (castʷ⊒ {u⊑ = tag★⇒★} {p = p′}
      left′ u⊢ V⊒V′ eq′) eq
    with tag-prefix-matchᶜ
      {left = left′} {left′ = left-id-one-sidedᵢ}
      {u⊑ = tag★⇒★} {v⊑ = tag★⇒★} {p = p′} {q = p}
      (trans eq′ (sym eq))
left-widening-tag-inversion-match {v⊑ = tag★⇒★} {p = p}
    vV vV′
    (castʷ⊒ {u⊑ = tag★⇒★} {p = p′}
      left′ u⊢ V⊒V′ eq′) eq | refl =
  refl , p′ ,
  tag-prefix-cancelᶜ
    {left = left′} {left′ = left-id-one-sidedᵢ}
    {u⊑ = tag★⇒★} {v⊑ = tag★⇒★} {p = p′} {q = p}
    (trans eq′ (sym eq)) ,
  V⊒V′
left-widening-tag-inversion-match vV vV′
    (⊒Λ {B≢★ = B≢★}
      extension preservation vV″ V⊒V″) eq =
  ⊥-elim (B≢★ refl)
left-widening-tag-inversion-match vV vV′
    (⊒⟨ν⟩ {B≢★ = B≢★}
      vV″ V″⊢ hC c⊢ V⊒V″) eq =
  ⊥-elim (B≢★ refl)
left-widening-tag-inversion-match {v⊑ = v⊑} {p = p}
    vV (vV′ ⟨ id′ ⟩)
    (⊒castⁿ {d′ = d′} {d′⊒ = d′⊒}
      {p = p₀} {q = r} right′ d′⊢ V⊒V′ eq′) eq
    with tag-factor-right-narrowing
      {u⊑ = v⊑} {q = p₀} {r = r} {p = p}
      right′ d′⊒ id′ eq′ eq
left-widening-tag-inversion-match {v⊑ = v⊑} {p = p}
    vV (vV′ ⟨ id′ ⟩)
    (⊒castⁿ {d′ = d′} {d′⊒ = d′⊒}
      {p = p₀} {q = r} right′ d′⊢ V⊒V′ eq′) eq
    | (s , s⊒) , prefix , suffix
    with left-widening-tag-inversion-match
      {v⊑ = v⊑} {p = s , s⊒}
      vV vV′ V⊒V′ prefix
left-widening-tag-inversion-match {p = p}
    vV (vV′ ⟨ id′ ⟩)
    (⊒castⁿ {d′⊒ = d′⊒}
      right′ d′⊢ V⊒V′ eq′) eq
    | (s , s⊒) , prefix , suffix
    | G≡H , (.s , s′⊒) , refl , V⊒V″ =
  G≡H , p , refl ,
  ⊒castⁿ {d′⊒ = d′⊒} {p = s , s′⊒} {q = p}
    right′ d′⊢ V⊒V″
    (trans
      (composeⁿ-left-evidence (right-compose right′)
        s′⊒ s⊒ d′⊒)
      suffix)
left-widening-tag-inversion-match {v⊑ = v⊑} {p = p}
    vV (vV″ ⟨ iu′ ⟩)
    (⊒castʷ {u′ = u′} {u′⊑ = u′⊑}
      {p = p₀} {q = r} right′ u′⊢ V⊒V′ eq′) eq
    with left-widening-tag-inversion-match
      {v⊑ = v⊑}
      {p = p ⨟ⁿ[ right′ ] dualʷ (u′ , u′⊑)}
      vV vV″ V⊒V′
      (trans
        (sym
          (tag-prefix-compose-right-widening
            {u⊑ = v⊑} {p = p} {q = r}
            {u′⊑ = u′⊑} right′ iu′ eq))
        eq′)
left-widening-tag-inversion-match {p = p}
    vV (vV″ ⟨ iu′ ⟩)
    (⊒castʷ {u′⊑ = u′⊑}
      right′ u′⊢ V⊒V′ eq′) eq
    | G≡H , p′ , p′≐p⨟u′ , V⊒V″ =
  G≡H , p , refl ,
  ⊒castʷ {u′⊑ = u′⊑} {p = p′} {q = p}
    right′ u′⊢ V⊒V″ (sym p′≐p⨟u′)

------------------------------------------------------------------------
-- Recontextualized supplied tags
------------------------------------------------------------------------

tag-under-id :
    ∀ {Δ A G}
      {Ψ : ImpCtx Δ Δ}
  → Ψ ∣ Δ ⊢ G ! ⦂ A ⊑ ★ ⊣ Δ
  → idᵢ Δ ∣ Δ ⊢ G ! ⦂ A ⊑ ★ ⊣ Δ
tag-under-id (tag ι) = tag ι
tag-under-id tag★⇒★ = tag★⇒★

tag-prefix-recontext :
    ∀ {Δᴸ Δᴿ A B G}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {Ψ : ImpCtx Δᴸ Δᴸ}
      {left : LeftOneSidedᵢ Φ Ψ}
      {v⊑ : Ψ ∣ Δᴸ ⊢ G ! ⦂ A ⊑ ★ ⊣ Δᴸ}
      {p : Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ}
  → proj₁ (dualʷ (G ! , v⊑) ⨟ˡⁿ[ left ] p)
      ≡ proj₁ (dualʷ (G ! , tag-under-id v⊑)
        ⨟ˡⁿ[ left-id-one-sidedᵢ ] p)
tag-prefix-recontext
    {left = record { left-one-sided = one ; left-compose = comp }}
    {v⊑ = tag ι}
    {p = _ , idᵃ (‵ .ι) (‵ κ) hA hB refl} =
  refl
tag-prefix-recontext
    {left = record { left-one-sided = one ; left-compose = comp }}
    {v⊑ = tag ι}
    {p = _ , gen nonvarA zero∈A p B≢★} =
  ⊥-elim (base-target-no-member p zero∈A)
tag-prefix-recontext {B = B}
    {left = record { left-one-sided = one ; left-compose = comp }}
    {v⊑ = tag★⇒★} {p = _ , p}
    with (★ ⇒ ★) ≟Ty B
tag-prefix-recontext
    {left = record { left-one-sided = one ; left-compose = comp }}
    {v⊑ = tag★⇒★}
    {p = _ , p₁ ↦ p₂} | yes refl =
  refl
tag-prefix-recontext
    {left = record { left-one-sided = one ; left-compose = comp }}
    {v⊑ = tag★⇒★} {p = _ , p} | no ★⇒★≢B =
  refl

left-widening-tag-inversion-match-one-sided :
    ∀ {Δᴸ Δᴿ Σᴸ Σᴿ Γᴸ Γᴿ V V′ C B G H}
      {Φ : ImpCtx Δᴸ Δᴿ}
      {Ψ : ImpCtx Δᴸ Δᴸ}
      {σ : Φ ∣ Δᴸ ⊢ Σᴸ ⊒ˢ Σᴿ ⊣ Δᴿ}
      {γ : Φ ∣ Δᴸ ⊢ Γᴸ ⊒ᵍ Γᴿ ⊣ Δᴿ}
      {left : LeftOneSidedᵢ Φ Ψ}
      {v⊑ : Ψ ∣ Δᴸ ⊢ H ! ⦂ C ⊑ ★ ⊣ Δᴸ}
      {r : Φ ∣ Δᴸ ⊢ ★ ⊒ B ⊣ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ C ⊒ B ⊣ Δᴿ}
  → Value V
  → Value V′
  → Φ ∣ Δᴸ ∣ Δᴿ ∣ σ ∣ γ
      ⊢ᴺ V ⟨ G ! ⟩ ⊒ V′ ⦂ ★ ⊒ B ∶ r
  → dualʷ (H ! , v⊑) ⨟ˡⁿ[ left ] p ≐ⁿ r
  → Σ[ G≡H ∈ G ≡ H ]
      Σ[ p′ ∈ (Φ ∣ Δᴸ ⊢ C ⊒ B ⊣ Δᴿ) ]
        (p′ ≐ⁿ p)
      × (Φ ∣ Δᴸ ∣ Δᴿ ∣ σ ∣ γ
          ⊢ᴺ V ⊒ V′ ⦂ C ⊒ B ∶ p′)
left-widening-tag-inversion-match-one-sided
    {left = left} {v⊑ = tag ι} {p = p}
    vV vV′ V⊒V′ eq =
  left-widening-tag-inversion-match
    {v⊑ = tag ι} {p = p} vV vV′ V⊒V′
    (trans
      (sym (tag-prefix-recontext
        {left = left} {v⊑ = tag ι} {p = p}))
      eq)
left-widening-tag-inversion-match-one-sided
    {left = left} {v⊑ = tag★⇒★} {p = p}
    vV vV′ V⊒V′ eq =
  left-widening-tag-inversion-match
    {v⊑ = tag★⇒★} {p = p} vV vV′ V⊒V′
    (trans
      (sym (tag-prefix-recontext
        {left = left} {v⊑ = tag★⇒★} {p = p}))
      eq)
