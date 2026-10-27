module proof.DenotGradualGuarantee where

-- File Charter:
--   * The dynamic gradual guarantee in observational form, proved through
--     the graph model with errors: compile both programs, relate their
--     denotations by the fundamental lemma, and move between reduction and
--     denotation by soundness and adequacy.
--   * Observations: a value shows its numeral or that it is a function
--     (observe); a denotational element likewise (obs).

open import Agda.Builtin.List using ([])
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)

open import Types
open import Contexts
open import GTLC
open import CastCalculus
open import Compile using (compile)
open import DynamicGradualGuaranteeDefinitions
open import GraphModel
open import Denotation
open import proof.CompileMeta using (compile-preserves; compile-precision)
open import proof.TypeSafety using (type-safety)
open import proof.DenotSoundness using (sound-val; sound-blame)
open import proof.DenotAdequacy using (adequacy-val; adequacy-err)
open import proof.DenotRelation
open import proof.DenotFundamental

------------------------------------------------------------------------
-- Observations
------------------------------------------------------------------------

observe-irrelevant : ∀ {V} (v w : Valueᶜ V) → observe v ≡ observe w
observe-irrelevant V-$ V-$ = refl
observe-irrelevant V-ƛ V-ƛ = refl
observe-irrelevant (V-cast! v) (V-cast! w) = observe-irrelevant v w
observe-irrelevant (V-cast↦ v) (V-cast↦ w) = refl

-- a justified left value has a right value with the same observation
◃ᵛ-obs : ∀ {A A′} (p : A ⊑ A′) d {D′}
  → p ⊢ d ◃ᵛ D′ → Σ[ d′ ∈ Val ] (d′ ∈ D′ × d′ ≢ ω × obs d ≡ obs d′)
◃ᵛ-obs ⊑-ℕ (nat n) (lift m) = nat n , m , (λ ()) , refl
◃ᵛ-obs ⊑-ℕ (V ⟼ w) ()
◃ᵛ-obs ⊑-ℕ ν ()
◃ᵛ-obs ⊑-ℕ ω ()
◃ᵛ-obs ⊑-ℕ (tag t u) ()
◃ᵛ-obs (⊑-★ {★}) (nat n) ()
◃ᵛ-obs (⊑-★ {★}) (V ⟼ w) ()
◃ᵛ-obs (⊑-★ {★}) ν ()
◃ᵛ-obs (⊑-★ {★}) ω ()
◃ᵛ-obs (⊑-★ {★}) (tag t u) r with ◃ᵛ-obs (tag⊑ t) u r
... | v , m , _ , eq = tag t v , m , (λ ()) , eq
◃ᵛ-obs (⊑-★ {ℕ}) (nat n) ()
◃ᵛ-obs (⊑-★ {ℕ}) (V ⟼ w) ()
◃ᵛ-obs (⊑-★ {ℕ}) ν ()
◃ᵛ-obs (⊑-★ {ℕ}) ω ()
◃ᵛ-obs (⊑-★ {ℕ}) (tag ℕᵗ u) r = ◃ᵛ-obs ⊑-ℕ u r
◃ᵛ-obs (⊑-★ {ℕ}) (tag ⇒ᵗ u) ()
◃ᵛ-obs (⊑-★ {A ⇒ B}) (nat n) ()
◃ᵛ-obs (⊑-★ {A ⇒ B}) (V ⟼ w) ()
◃ᵛ-obs (⊑-★ {A ⇒ B}) ν ()
◃ᵛ-obs (⊑-★ {A ⇒ B}) ω ()
◃ᵛ-obs (⊑-★ {A ⇒ B}) (tag ℕᵗ u) ()
◃ᵛ-obs (⊑-★ {A ⇒ B}) (tag ⇒ᵗ u) r =
  ◃ᵛ-obs (⊑-⇒ (⊑-★ {A}) (⊑-★ {B})) u r
◃ᵛ-obs (⊑-⇒ p q) (nat n) ()
◃ᵛ-obs (⊑-⇒ p q) (U ⟼ w) (lift m , _) = ν , m , (λ ()) , refl
◃ᵛ-obs (⊑-⇒ p q) ν (lift m) = ν , m , (λ ()) , refl
◃ᵛ-obs (⊑-⇒ p q) ω ()
◃ᵛ-obs (⊑-⇒ p q) (tag t u) ()

-- a justified right value has a left value with the same observation
▹ᵛ-obs : ∀ {A A′} (p : A ⊑ A′) d′ {D}
  → p ⊢ D ▹ᵛ d′ → Σ[ d ∈ Val ] (d ∈ D × d ≢ ω × obs d ≡ obs d′)
▹ᵛ-obs ⊑-ℕ (nat n) (lift m) = nat n , m , (λ ()) , refl
▹ᵛ-obs ⊑-ℕ (V ⟼ w) ()
▹ᵛ-obs ⊑-ℕ ν ()
▹ᵛ-obs ⊑-ℕ ω ()
▹ᵛ-obs ⊑-ℕ (tag t u) ()
▹ᵛ-obs (⊑-★ {★}) (nat n) ()
▹ᵛ-obs (⊑-★ {★}) (V ⟼ w) ()
▹ᵛ-obs (⊑-★ {★}) ν ()
▹ᵛ-obs (⊑-★ {★}) ω ()
▹ᵛ-obs (⊑-★ {★}) (tag t u) r with ▹ᵛ-obs (tag⊑ t) u r
... | v , m , _ , eq = tag t v , m , (λ ()) , eq
▹ᵛ-obs (⊑-★ {ℕ}) (nat n) (lift m) = tag ℕᵗ (nat n) , m , (λ ()) , refl
▹ᵛ-obs (⊑-★ {ℕ}) (V ⟼ w) ()
▹ᵛ-obs (⊑-★ {ℕ}) ν ()
▹ᵛ-obs (⊑-★ {ℕ}) ω ()
▹ᵛ-obs (⊑-★ {ℕ}) (tag t u) ()
▹ᵛ-obs (⊑-★ {A ⇒ B}) (nat n) ()
▹ᵛ-obs (⊑-★ {A ⇒ B}) (V ⟼ w) (lift m , _) =
  tag ⇒ᵗ ν , m , (λ ()) , refl
▹ᵛ-obs (⊑-★ {A ⇒ B}) ν (lift m) = tag ⇒ᵗ ν , m , (λ ()) , refl
▹ᵛ-obs (⊑-★ {A ⇒ B}) ω ()
▹ᵛ-obs (⊑-★ {A ⇒ B}) (tag t u) ()
▹ᵛ-obs (⊑-⇒ p q) (nat n) ()
▹ᵛ-obs (⊑-⇒ p q) (V ⟼ w) (lift m , _) = ν , m , (λ ()) , refl
▹ᵛ-obs (⊑-⇒ p q) ν (lift m) = ν , m , (λ ()) , refl
▹ᵛ-obs (⊑-⇒ p q) ω ()
▹ᵛ-obs (⊑-⇒ p q) (tag t u) ()

------------------------------------------------------------------------
-- The dynamic gradual guarantee
------------------------------------------------------------------------

dynamic-gradual-guarantee-observational : ∀ {M M′ A A′}
  → M ⊑ᵀ M′
  → [] ⊢ M ⦂ A
  → [] ⊢ M′ ⦂ A′
  → (∀ V′ (v′ : Valueᶜ V′)
       → M′ ⇓ V′
       → ∃[ V ] Σ[ v ∈ Valueᶜ V ] (M ⇓ V × observe v ≡ observe v′))
    × (Diverges M′ → Diverges M)
    × (∀ V (v : Valueᶜ V)
         → M ⇓ V
         → (∃[ V′ ] Σ[ v′ ∈ Valueᶜ V′ ] (M′ ⇓ V′ × observe v ≡ observe v′))
           ⊎ Blames M′)
    × (Diverges M → DivergeOrBlame M′)
dynamic-gradual-guarantee-observational {M} {M′} {A} {A′} M≤M′ M⦂A M′⦂A′ =
  forward , diverge , backward , diverge-or-blame
  where
  forward : ∀ V′ (v′ : Valueᶜ V′) → M′ ⇓ V′
    → ∃[ V ] Σ[ v ∈ Valueᶜ V ] (M ⇓ V × observe v ≡ observe v′)
  forward V′ v′ (A″ , wt′ , red′ , r-val .V′ v″)
      with sound-val (compile-preserves wt′) v″ red′
  ... | d′ , d′∈ , d′≢ , ob′
      with ▹ᵛ-obs p d′
             (▹-val p d′ d′≢ (fundamental▹ prec p ρ₀▹ d′ d′∈))
    where
    prec = compile-precision M≤M′ M⦂A wt′
    p = ⊑ᶜᵀ-type-precision prec
  ...   | d , d∈ , d≢ , obd with adequacy-val d∈ d≢
  ...     | V , v , red , obV =
    V , v , (A , M⦂A , red , r-val V v)
    , trans obV (trans obd (trans ob′ (observe-irrelevant v″ v′)))
  forward .(blame {ℓ = ℓ}) () (A″ , wt′ , red′ , r-blame {ℓ = ℓ})

  diverge : Diverges M′ → Diverges M
  diverge (A″ , wt′ , div′) = A , M⦂A , λ conv → div′ (conv′ conv)
    where
    prec = compile-precision M≤M′ M⦂A wt′
    p = ⊑ᶜᵀ-type-precision prec
    conv′ : Convergesᶜ (compile M⦂A) → Convergesᶜ (compile wt′)
    conv′ (W , red , inj₁ vW)
        with sound-val (compile-preserves M⦂A) vW red
    ... | d , d∈ , d≢ , _ with fundamental◃ prec p ρ₀◃ d d∈
    ...   | inj₁ (lift ω∈) with adequacy-err ω∈
    ...     | ℓ , red′ = blame , red′ , inj₂ (ℓ , refl)
    conv′ (W , red , inj₁ vW)
        | d , d∈ , d≢ , _ | inj₂ r with ◃ᵛ-obs p d r
    ...     | d′ , d′∈ , d′≢ , _ with adequacy-val d′∈ d′≢
    ...       | V′ , v′ , red′ , _ = V′ , red′ , inj₁ v′
    conv′ (W , red , inj₂ (ℓ , refl))
        with adequacy-err
               (◃-ω p (fundamental◃ prec p ρ₀◃ ω
                         (sound-blame (compile-preserves M⦂A) red)))
    ... | ℓ′ , red′ = blame , red′ , inj₂ (ℓ′ , refl)

  backward : ∀ V (v : Valueᶜ V) → M ⇓ V
    → (∃[ V′ ] Σ[ v′ ∈ Valueᶜ V′ ] (M′ ⇓ V′ × observe v ≡ observe v′))
      ⊎ Blames M′
  backward V v (A″ , wt , red , r-val .V v″)
      with sound-val (compile-preserves wt) v″ red
  ... | d , d∈ , d≢ , ob with fundamental◃ prec p ρ₀◃ d d∈
    where
    prec = compile-precision M≤M′ wt M′⦂A′
    p = ⊑ᶜᵀ-type-precision prec
  ...   | inj₁ (lift ω∈) with adequacy-err ω∈
  ...     | ℓ , red′ = inj₂ (ℓ , A′ , M′⦂A′ , red′ , r-blame)
  backward V v (A″ , wt , red , r-val .V v″)
      | d , d∈ , d≢ , ob | inj₂ r with ◃ᵛ-obs p d r
    where
    prec = compile-precision M≤M′ wt M′⦂A′
    p = ⊑ᶜᵀ-type-precision prec
  ...     | d′ , d′∈ , d′≢ , obd with adequacy-val d′∈ d′≢
  ...       | V′ , v′ , red′ , obV′ =
    inj₁ (V′ , v′ , (A′ , M′⦂A′ , red′ , r-val V′ v′)
          , trans (observe-irrelevant v v″)
              (trans (sym ob) (trans obd (sym obV′))))
  backward .(blame {ℓ = ℓ}) () (A″ , wt , red , r-blame {ℓ = ℓ})

  diverge-or-blame : Diverges M → DivergeOrBlame M′
  diverge-or-blame (A₀ , wt₀ , div) = A′ , M′⦂A′ , dob
    where
    prec = compile-precision M≤M′ wt₀ M′⦂A′
    p = ⊑ᶜᵀ-type-precision prec
    dob : DivergeOrBlameᶜ (compile M′⦂A′)
    dob N′ red′ with type-safety M′⦂A′ red′
    ... | inj₁ step = inj₂ step
    ... | inj₂ (r-blame {ℓ = ℓ}) = inj₁ (ℓ , refl)
    ... | inj₂ (r-val .N′ v′)
        with sound-val (compile-preserves M′⦂A′) v′ red′
    ...   | d′ , d′∈ , d′≢ , _
        with ▹ᵛ-obs p d′
               (▹-val p d′ d′≢ (fundamental▹ prec p ρ₀▹ d′ d′∈))
    ...     | d , d∈ , d≢ , _ with adequacy-val d∈ d≢
    ...       | V , v , red , _ = ⊥-elim (div (V , red , inj₁ v))
