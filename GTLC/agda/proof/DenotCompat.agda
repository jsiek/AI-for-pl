module proof.DenotCompat where

-- File Charter:
--   * Compatibility of the preservation (◃) and reflection (▹) relations
--     with the operators of the semantics: bind, application, and a cast
--     on one side only.
--   * The right side of a preservation may hold both ω and values, and
--     whether it holds ω cannot be decided.  So bind for ◃ (fbind◃) works
--     one element at a time: each element of F ⌊ D ⌋ needs only a finite
--     list of elements of D (F is finitary), and on a finite list either
--     some element escapes (the right side errs) or all are justified by
--     the values of the right side.
--   * Coe◃ and Coe▹: the statements of the coercion lemma, used here for a
--     cast on the right only (idlift◃, idlift▹).

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _⋵_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; subst)

open import Types
open import Coercions using (Coercion; idᶜ)
open import GraphModel
open import Denotation
open import proof.DenotProps using (Mono; Finitary; ⌊⌋-⊆)
open import proof.DenotRelation

------------------------------------------------------------------------
-- Set helpers
------------------------------------------------------------------------

Conv-⌊⌋ : ∀ {D} → Conv D → Conv ⌊ D ⌋
Conv-⌊⌋ (x , x∈ , x≢) = x , (x∈ , x≢) , x≢

⌊⌋-Conv : ∀ {D} → Conv ⌊ D ⌋ → Conv D
⌊⌋-Conv (x , (x∈ , _) , x≢) = x , x∈ , x≢

ValSet-⌊⌋ : ∀ D → ValSet ⌊ D ⌋
ValSet-⌊⌋ D = valset λ { (_ , ω≢) → ω≢ refl }

-- the bind of a set with a value
≫=-val-⊆ : ∀ {D F} → Conv D → F ⌊ D ⌋ ⊆ (D ≫= F)
≫=-val-⊆ cD x x∈ = inj₂ (cD , x∈)

-- the bind of a value set
≫=-ValSet-⊆ : ∀ {D F} → ValSet D → (D ≫= F) ⊆ F ⌊ D ⌋
≫=-ValSet-⊆ vD x (inj₁ (_ , ω∈)) = ⊥-elim (ω∉ vD ω∈)
≫=-ValSet-⊆ vD x (inj₂ (_ , x∈)) = x∈

-- the bind of a set with the identity coercion
≫=-id-⊆ : ∀ {A D} → (D ≫= ⟦ idᶜ A ⟧ᶜ) ⊆ D
≫=-id-⊆ x (inj₁ (refl , ω∈)) = ω∈
≫=-id-⊆ x (inj₂ (_ , x∈ , _)) = x∈

ValSet-sing : ∀ {w} → w ≢ ω → ValSet (mem (w ∷ []))
ValSet-sing w≢ = valset λ { (here eq) → w≢ (sym eq) ; (there ()) }

------------------------------------------------------------------------
-- The coercion lemma's statements
------------------------------------------------------------------------

Coe◃ : ∀ {A A′ B B′} → A ⊑ A′ → B ⊑ B′ → Coercion → Coercion → Set₁
Coe◃ pA pB c c′ =
  ∀ X X′ → ValSet X → ValSet X′ → Conv X → Conv X′
  → pA ⊢ X ◃ˢ X′ → pB ⊢ ⟦ c ⟧ᶜ X ◃ˢ ⟦ c′ ⟧ᶜ X′

Coe▹ : ∀ {A A′ B B′} → A ⊑ A′ → B ⊑ B′ → Coercion → Coercion → Set₁
Coe▹ pA pB c c′ =
  ∀ X X′ → ValSet X → ValSet X′ → Conv X → Conv X′
  → pA ⊢ X ▹ˢ X′ → pB ⊢ ⟦ c ⟧ᶜ X ▹ˢ ⟦ c′ ⟧ᶜ X′

------------------------------------------------------------------------
-- Bind
------------------------------------------------------------------------

fbind◃ : ∀ {A A′ B B′} (p : A ⊑ A′) (q : B ⊑ B′) {D D′ F F′}
  → p ⊢ D ◃ˢ D′ → Finitary F → Mono F
  → (∀ Y Y′ → ValSet Y → ValSet Y′ → Conv Y → Conv Y′
       → p ⊢ Y ◃ˢ Y′ → q ⊢ F Y ◃ˢ F′ Y′)
  → q ⊢ (D ≫= F) ◃ˢ (D′ ≫= F′)
fbind◃ p q rD fin mono h w (inj₁ (refl , ω∈D)) =
  inj₁ (lift (inj₁ (refl , ◃-ω p (rD ω ω∈D))))
fbind◃ p q {D} {D′} {F} {F′} rD fin mono h w
    (inj₂ ((d₀ , d₀∈ , d₀≢) , w∈))
    with fin ⌊ D ⌋ w w∈
... | L , L⊆ , w∈L
    with all◃ p (d₀ ∷ L) inK
  where
  inK : ∀ u → u ⋵ (d₀ ∷ L) → p ⊢ u ◃ D′
  inK u (here refl) = rD d₀ d₀∈
  inK u (there u∈) = rD u (proj₁ (L⊆ u u∈))
...   | inj₁ (lift ω∈) = inj₁ (lift (inj₁ (refl , ω∈)))
...   | inj₂ rs =
  ◃-mono q w (≫=-val-⊆ {D = D′} {F = F′} (⌊⌋-Conv cD′))
    (h (mem (d₀ ∷ L)) ⌊ D′ ⌋ vK (ValSet-⌊⌋ D′) (d₀ , here refl , d₀≢) cD′
       (λ u u∈ → ◃*-∈ p rs u u∈) w (mono (λ x → there) w w∈L))
  where
  cD′ : Conv ⌊ D′ ⌋
  cD′ = ◃ᵛ-conv p d₀ (◃-val p d₀ (ValSet-⌊⌋ D′) (proj₁ rs))
  vK : ValSet (mem (d₀ ∷ L))
  vK = valset λ { (here eq) → d₀≢ (sym eq)
                ; (there ω∈) → proj₂ (L⊆ ω ω∈) refl }

bind▹ : ∀ {A A′ B B′} (p : A ⊑ A′) (q : B ⊑ B′) {D D′ F F′}
  → p ⊢ D ▹ˢ D′
  → (∀ Y Y′ → ValSet Y → ValSet Y′ → Conv Y → Conv Y′
       → p ⊢ Y ▹ˢ Y′ → q ⊢ F Y ▹ˢ F′ Y′)
  → q ⊢ (D ≫= F) ▹ˢ (D′ ≫= F′)
bind▹ p q rD h w′ (inj₁ (refl , _)) = inj₁ (lift refl)
bind▹ p q {D} {D′} {F} {F′} rD h w′ (inj₂ ((d₀′ , d₀′∈ , d₀′≢) , w′∈)) =
  ▹-mono q w′ (≫=-val-⊆ {D = D} {F = F} cD)
    (h ⌊ D ⌋ ⌊ D′ ⌋ (ValSet-⌊⌋ D) (ValSet-⌊⌋ D′) (Conv-⌊⌋ cD)
       (d₀′ , (d₀′∈ , d₀′≢) , d₀′≢) rel w′ w′∈)
  where
  cD : Conv D
  cD = ▹ᵛ-conv p d₀′ (▹-val p d₀′ d₀′≢ (rD d₀′ d₀′∈))
  rel : p ⊢ ⌊ D ⌋ ▹ˢ ⌊ D′ ⌋
  rel v′ (v′∈ , v′≢) = inj₂ (▹ᵛ-vals p v′ (▹-val p v′ v′≢ (rD v′ v′∈)))

------------------------------------------------------------------------
-- Application
------------------------------------------------------------------------

app◃ : ∀ {A A′ B B′} (p : A ⊑ A′) (q : B ⊑ B′) {X X′ Y Y′}
  → ValSet X′ → ValSet Y′
  → ⊑-⇒ p q ⊢ X ◃ˢ X′ → p ⊢ Y ◃ˢ Y′ → q ⊢ (X ● Y) ◃ˢ (X′ ● Y′)
app◃ p q {X′ = X′} {Y′ = Y′} vX′ vY′ rX rY w (U , e∈ , U⊆ , U≢)
    with ◃-val (⊑-⇒ p q) (U ⟼ w) {X′} vX′ (rX (U ⟼ w) e∈)
... | lift ν∈ , f =
  ◃-mono q w (●-monoˡ (⌊⌋-⊆ {X′}))
    (f Y′ vY′ U≢ (◃*-intro p U (λ u u∈ → rY u (U⊆ u u∈))))

app▹ : ∀ {A A′ B B′} (p : A ⊑ A′) (q : B ⊑ B′) {X X′ Y Y′}
  → ValSet Y → ValSet Y′
  → ⊑-⇒ p q ⊢ X ▹ˢ X′ → p ⊢ Y ▹ˢ Y′ → q ⊢ (X ● Y) ▹ˢ (X′ ● Y′)
app▹ p q {X = X} {Y = Y} vY vY′ rX rY w′ (V′ , e′∈ , V′⊆ , V′≢)
    with ▹-val (⊑-⇒ p q) (V′ ⟼ w′) {X} (λ ()) (rX (V′ ⟼ w′) e′∈)
... | lift ν∈ , g =
  ▹-mono q w′ (●-monoˡ (⌊⌋-⊆ {X}))
    (g Y vY V′≢ (λ ω∈ → ω∉ vY′ (V′⊆ ω ω∈))
       (▹*-intro p V′ (λ v′ v′∈ → rY v′ (V′⊆ v′ v′∈))))

------------------------------------------------------------------------
-- A cast on the right only
------------------------------------------------------------------------

idlift◃ : ∀ {A A′ B′ c′} (p : A ⊑ A′) (q : A ⊑ B′)
  → Coe◃ p q (idᶜ A) c′
  → ∀ w {S} → p ⊢ w ◃ S → q ⊢ w ◃ (S ≫= ⟦ c′ ⟧ᶜ)
idlift◃ p q h w (inj₁ (lift ω∈)) = inj₁ (lift (inj₁ (refl , ω∈)))
idlift◃ {c′ = c′} p q h w {S} (inj₂ r) =
  ◃-mono q w (≫=-val-⊆ {D = S} {F = ⟦ c′ ⟧ᶜ} (⌊⌋-Conv cS))
    (h (mem (w ∷ [])) ⌊ S ⌋ (ValSet-sing w≢) (ValSet-⌊⌋ S)
       (w , here refl , w≢) cS rel w (here refl))
  where
  r′ = ◃ᵛ-vals p w r
  cS : Conv ⌊ S ⌋
  cS = ◃ᵛ-conv p w r′
  w≢ : w ≢ ω
  w≢ eq = ◃ᵛ-ω p (subst (λ x → p ⊢ x ◃ᵛ S) eq r)
  rel : p ⊢ mem (w ∷ []) ◃ˢ ⌊ S ⌋
  rel u (here refl) = inj₂ r′
  rel u (there ())

idlift◃ˢ : ∀ {A A′ B′ c′} (p : A ⊑ A′) (q : A ⊑ B′)
  → Coe◃ p q (idᶜ A) c′
  → ∀ {D S} → p ⊢ D ◃ˢ S → q ⊢ D ◃ˢ (S ≫= ⟦ c′ ⟧ᶜ)
idlift◃ˢ {c′ = c′} p q h {D} {S} rD w w∈ =
  idlift◃ {c′ = c′} p q h w {S} (rD w w∈)

idlift▹ : ∀ {A A′ B′ c′} (p : A ⊑ A′) (q : A ⊑ B′)
  → Coe▹ p q (idᶜ A) c′
  → ∀ {D S} → p ⊢ D ▹ˢ S → q ⊢ D ▹ˢ (S ≫= ⟦ c′ ⟧ᶜ)
idlift▹ p q h rD w′ (inj₁ (refl , _)) = inj₁ (lift refl)
idlift▹ p q h {D} {S} rD w′ (inj₂ ((s₀ , s₀∈ , s₀≢) , w′∈)) =
  ▹-mono q w′ ⌊⌋-⊆
    (h ⌊ D ⌋ ⌊ S ⌋ (ValSet-⌊⌋ D) (ValSet-⌊⌋ S) (Conv-⌊⌋ cD)
       (s₀ , (s₀∈ , s₀≢) , s₀≢) rel w′ w′∈)
  where
  cD : Conv D
  cD = ▹ᵛ-conv p s₀ (▹-val p s₀ s₀≢ (rD s₀ s₀∈))
  rel : p ⊢ ⌊ D ⌋ ▹ˢ ⌊ S ⌋
  rel v′ (v′∈ , v′≢) = inj₂ (▹ᵛ-vals p v′ (▹-val p v′ v′≢ (rD v′ v′∈)))
