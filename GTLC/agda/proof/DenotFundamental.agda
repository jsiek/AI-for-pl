module proof.DenotFundamental where

-- File Charter:
--   * The fundamental lemma of the denotational proof of the dynamic gradual
--     guarantee: term precision implies both relations between the
--     denotations, under related environments.
--   * The two directions are separate inductions on the precision
--     derivation; casts go through the coercion lemma, and a cast on one side
--     only is a cast against the identity.

open import Agda.Builtin.Nat using (zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst)

open import Types
open import Contexts
open import Coercions
open import CastCalculus
open import GraphModel
open import Denotation
open import proof.DenotProps
  using (Mono; Finitary; ⟦⟧ᶜ-fin; ⟦⟧ᶜ-mono; Λ-β; ≫=-mono; ●-mono; ⌊⌋-⊆)
open import proof.DenotSoundness using (≫=-unit)
open import proof.DenotRelation
open import proof.DenotCompat
open import proof.DenotCoercion using (coe)

------------------------------------------------------------------------
-- Environments
------------------------------------------------------------------------

Env◃ : ∀ {Γ Γ′} → Γ ⊑ᵉ Γ′ → Env → Env → Set₁
Env◃ {Γ} {Γ′} ρ⊑ ρ ρ′ =
  ∀ x A A′ (∋x : Γ ∋ x ⦂ A) (∋x′ : Γ′ ∋ x ⦂ A′)
  → ρ⊑ x A A′ ∋x ∋x′ ⊢ ρ x ◃ˢ ρ′ x

Env▹ : ∀ {Γ Γ′} → Γ ⊑ᵉ Γ′ → Env → Env → Set₁
Env▹ {Γ} {Γ′} ρ⊑ ρ ρ′ =
  ∀ x A A′ (∋x : Γ ∋ x ⦂ A) (∋x′ : Γ′ ∋ x ⦂ A′)
  → ρ⊑ x A A′ ∋x ∋x′ ⊢ ρ x ▹ˢ ρ′ x

ext◃ : ∀ {Γ Γ′ A A′} {ρ⊑ : Γ ⊑ᵉ Γ′} (p : A ⊑ A′) {ρ ρ′ D D′}
  → Env◃ ρ⊑ ρ ρ′ → p ⊢ D ◃ˢ D′
  → Env◃ (extend-⊑ᵉ p ρ⊑) (D • ρ) (D′ • ρ′)
ext◃ p rρ rD zero A A′ Z Z = rD
ext◃ p rρ rD (suc x) A A′ (S ∋x) (S ∋x′) = rρ x A A′ ∋x ∋x′

ext▹ : ∀ {Γ Γ′ A A′} {ρ⊑ : Γ ⊑ᵉ Γ′} (p : A ⊑ A′) {ρ ρ′ D D′}
  → Env▹ ρ⊑ ρ ρ′ → p ⊢ D ▹ˢ D′
  → Env▹ (extend-⊑ᵉ p ρ⊑) (D • ρ) (D′ • ρ′)
ext▹ p rρ rD zero A A′ Z Z = rD
ext▹ p rρ rD (suc x) A A′ (S ∋x) (S ∋x′) = rρ x A A′ ∋x ∋x′

-- the closed environments are related
ρ₀◃ : Env◃ []⊑[] ρ₀ ρ₀
ρ₀◃ x A A′ ()

ρ₀▹ : Env▹ []⊑[] ρ₀ ρ₀
ρ₀▹ x A A′ ()

------------------------------------------------------------------------
-- Application, as a bind of its operator and of its operand
------------------------------------------------------------------------

app-op : 𝒫 → 𝒫 → 𝒫
app-op DM F = DM ≫= λ X → F ● X

app-op-fin : ∀ DM → Finitary (app-op DM)
app-op-fin DM F w (inj₁ (refl , ω∈)) = [] , (λ d ()) , inj₁ (refl , ω∈)
app-op-fin DM F w (inj₂ (cD , V , e∈ , V⊆ , V≢)) =
  (V ⟼ w ∷ []) , (λ { d (here refl) → e∈ ; d (there ()) })
  , inj₂ (cD , V , here refl , V⊆ , V≢)

app-op-mono : ∀ DM → Mono (app-op DM)
app-op-mono DM {F} {F′} sub =
  ≫=-mono {D = DM} {D′ = DM} {F = λ X → F ● X} {F′ = λ X → F′ ● X}
    (λ d d∈ → d∈) (λ X⊆ → ●-mono sub X⊆)

●ʳ-fin : ∀ F → Finitary (λ X → F ● X)
●ʳ-fin F X w (V , e∈ , V⊆ , V≢) = V , V⊆ , V , e∈ , (λ d d∈ → d∈) , V≢

●ʳ-mono : ∀ F → Mono (λ X → F ● X)
●ʳ-mono F sub = ●-monoʳ {D = F} sub

------------------------------------------------------------------------
-- The fundamental lemma
------------------------------------------------------------------------

fundamental◃ : ∀ {Γ Γ′} {ρ⊑ : Γ ⊑ᵉ Γ′} {M M′ A A′}
  → ρ⊑ ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → (p : A ⊑ A′) → ∀ {ρ ρ′} → Env◃ ρ⊑ ρ ρ′
  → p ⊢ ⟦ M ⟧ ρ ◃ˢ ⟦ M′ ⟧ ρ′
fundamental◃ {ρ⊑ = ρ⊑} (⊑` {A₁ = A} {A₂ = A′} {x = x} ∋x ∋x′) p rρ
    rewrite ⊑-unique p (ρ⊑ x A A′ ∋x ∋x′) = rρ x A A′ ∋x ∋x′
fundamental◃ ⊑$ ⊑-ℕ rρ d refl = inj₂ (lift refl)
fundamental◃ (⊑ƛ {A = A} {A′ = A′} {N = N} {M = N′} A⊑A′ N⊑) (⊑-⇒ pa pb) {ρ} {ρ′} rρ = el
  where
  el : ⊑-⇒ pa pb ⊢ ⟦ ƛ A ⇒ N ⟧ ρ ◃ˢ ⟦ ƛ A′ ⇒ N′ ⟧ ρ′
  el ν _ = inj₂ (lift tt)
  el (U ⟼ w) (w∈ , U≢ , ne) = inj₂ (lift tt , clause)
    where
    clause : ∀ E′ → ValSet E′ → U ≢ [] → pa ⊢ U ◃* E′
      → pb ⊢ w ◃ (⌊ ⟦ ƛ A′ ⇒ N′ ⟧ ρ′ ⌋ ● E′)
    clause E′ vE′ _ rU =
      ◃-mono pb w
        (λ x x∈ → ●-monoˡ
                    (λ e e∈ → e∈ , Λ≢ω {F = λ Y → ⟦ N′ ⟧ (Y • ρ′)} e e∈) x
                    (Λ-β N′ ρ′ vE′ (◃*-conv pa U U≢ vE′ rU) x x∈))
        (fundamental◃ N⊑ pb
           (ext◃ A⊑A′ rρ
              (subst (λ q → q ⊢ mem U ◃ˢ E′) (⊑-unique pa A⊑A′)
                 (λ u u∈ → ◃*-∈ pa rU u u∈)))
           w w∈)
  el (nat n) ()
  el ω ()
  el (tag t u) ()
fundamental◃ (⊑· {A = A} {A′ = A′} {L = L} {L′ = L′} {M = M} {M′ = M′}
    L⊑ M⊑) q {ρ} {ρ′} rρ =
  fbind◃ (⊑-⇒ pa q) q {D = ⟦ L ⟧ ρ} {D′ = ⟦ L′ ⟧ ρ′}
    {F = app-op (⟦ M ⟧ ρ)} {F′ = app-op (⟦ M′ ⟧ ρ′)}
    (fundamental◃ L⊑ (⊑-⇒ pa q) rρ) (app-op-fin _) (app-op-mono _)
    (λ Y Y′ vY vY′ cY cY′ rY →
       fbind◃ pa q {D = ⟦ M ⟧ ρ} {D′ = ⟦ M′ ⟧ ρ′}
         {F = λ X → Y ● X} {F′ = λ X → Y′ ● X}
         (fundamental◃ M⊑ pa rρ) (●ʳ-fin Y) (●ʳ-mono Y)
         (λ Z Z′ vZ vZ′ cZ cZ′ rZ → app◃ pa q vY′ vZ′ rY rZ))
  where
  pa : A ⊑ A′
  pa = ⊑ᶜᵀ-type-precision M⊑
fundamental◃ (⊑cast {A = A} {A′ = A′} {M = M} {M′ = M′} {c = c} {c′ = c′}
    M⊑ c⊑ cwt c′wt) q {ρ} {ρ′} rρ =
  fbind◃ pA q {D = ⟦ M ⟧ ρ} {D′ = ⟦ M′ ⟧ ρ′} {F = ⟦ c ⟧ᶜ}
    {F′ = ⟦ c′ ⟧ᶜ} (fundamental◃ M⊑ pA rρ) (⟦⟧ᶜ-fin c) (⟦⟧ᶜ-mono c)
    (proj₁ (coe c⊑ cwt c′wt pA q))
  where
  pA : A ⊑ A′
  pA = ⊑ᶜᵀ-type-precision M⊑
fundamental◃ (⊑castL {A = A} {A′ = A′} {M = M} {M′ = M′} {c = c}
    M⊑ cwt c⊑id) q {ρ} {ρ′} rρ d d∈ =
  ◃-mono q d (≫=-id-⊆ {A = A′} {D = ⟦ M′ ⟧ ρ′})
    (fbind◃ pA q {D = ⟦ M ⟧ ρ} {D′ = ⟦ M′ ⟧ ρ′} {F = ⟦ c ⟧ᶜ}
       {F′ = ⟦ idᶜ A′ ⟧ᶜ} (fundamental◃ M⊑ pA rρ) (⟦⟧ᶜ-fin c)
       (⟦⟧ᶜ-mono c) (proj₁ (coe c⊑id cwt ⊢idᶜ pA q)) d d∈)
  where
  pA : A ⊑ A′
  pA = ⊑ᶜᵀ-type-precision M⊑
fundamental◃ (⊑castR {A = A} {A′ = A′} {c′ = c′} M⊑ c′wt id⊑c′) q rρ =
  idlift◃ˢ {c′ = c′} pA q (proj₁ (coe id⊑c′ ⊢idᶜ c′wt pA q))
    (fundamental◃ M⊑ pA rρ)
  where
  pA : A ⊑ A′
  pA = ⊑ᶜᵀ-type-precision M⊑
fundamental◃ (⊑blameR M⦂ A⊑A′) q rρ d d∈ = inj₁ (lift refl)

fundamental▹ : ∀ {Γ Γ′} {ρ⊑ : Γ ⊑ᵉ Γ′} {M M′ A A′}
  → ρ⊑ ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → (p : A ⊑ A′) → ∀ {ρ ρ′} → Env▹ ρ⊑ ρ ρ′
  → p ⊢ ⟦ M ⟧ ρ ▹ˢ ⟦ M′ ⟧ ρ′
fundamental▹ {ρ⊑ = ρ⊑} (⊑` {A₁ = A} {A₂ = A′} {x = x} ∋x ∋x′) p rρ
    rewrite ⊑-unique p (ρ⊑ x A A′ ∋x ∋x′) = rρ x A A′ ∋x ∋x′
fundamental▹ ⊑$ ⊑-ℕ rρ d′ refl = inj₂ (lift refl)
fundamental▹ (⊑ƛ {A = A} {A′ = A′} {N = N} {M = N′} A⊑A′ N⊑) (⊑-⇒ pa pb) {ρ} {ρ′} rρ = el
  where
  el : ⊑-⇒ pa pb ⊢ ⟦ ƛ A ⇒ N ⟧ ρ ▹ˢ ⟦ ƛ A′ ⇒ N′ ⟧ ρ′
  el ν _ = inj₂ (lift tt)
  el (V′ ⟼ w′) (w′∈ , V′≢ , ne′) = inj₂ (lift tt , clause)
    where
    clause : ∀ E → ValSet E → V′ ≢ [] → NoErr V′ → pa ⊢ E ▹* V′
      → pb ⊢ (⌊ ⟦ ƛ A ⇒ N ⟧ ρ ⌋ ● E) ▹ w′
    clause E vE _ _ rV =
      ▹-mono pb w′
        (λ x x∈ → ●-monoˡ
                    (λ e e∈ → e∈ , Λ≢ω {F = λ Y → ⟦ N ⟧ (Y • ρ)} e e∈) x
                    (Λ-β N ρ vE (▹*-conv pa V′ V′≢ ne′ rV) x x∈))
        (fundamental▹ N⊑ pb
           (ext▹ A⊑A′ rρ
              (subst (λ q → q ⊢ E ▹ˢ mem V′) (⊑-unique pa A⊑A′)
                 (λ v′ v′∈ → ▹*-∈ pa rV v′ v′∈)))
           w′ w′∈)
  el (nat n) ()
  el ω ()
  el (tag t u) ()
fundamental▹ (⊑· {A = A} {A′ = A′} {L = L} {L′ = L′} {M = M} {M′ = M′}
    L⊑ M⊑) q {ρ} {ρ′} rρ =
  bind▹ (⊑-⇒ pa q) q {D = ⟦ L ⟧ ρ} {D′ = ⟦ L′ ⟧ ρ′}
    {F = app-op (⟦ M ⟧ ρ)} {F′ = app-op (⟦ M′ ⟧ ρ′)}
    (fundamental▹ L⊑ (⊑-⇒ pa q) rρ)
    (λ Y Y′ vY vY′ cY cY′ rY →
       bind▹ pa q {D = ⟦ M ⟧ ρ} {D′ = ⟦ M′ ⟧ ρ′}
         {F = λ X → Y ● X} {F′ = λ X → Y′ ● X}
         (fundamental▹ M⊑ pa rρ)
         (λ Z Z′ vZ vZ′ cZ cZ′ rZ → app▹ pa q vZ vZ′ rY rZ))
  where
  pa : A ⊑ A′
  pa = ⊑ᶜᵀ-type-precision M⊑
fundamental▹ (⊑cast {A = A} {A′ = A′} {M = M} {M′ = M′} {c = c} {c′ = c′}
    M⊑ c⊑ cwt c′wt) q {ρ} {ρ′} rρ =
  bind▹ pA q {D = ⟦ M ⟧ ρ} {D′ = ⟦ M′ ⟧ ρ′} {F = ⟦ c ⟧ᶜ}
    {F′ = ⟦ c′ ⟧ᶜ} (fundamental▹ M⊑ pA rρ)
    (proj₂ (coe c⊑ cwt c′wt pA q))
  where
  pA : A ⊑ A′
  pA = ⊑ᶜᵀ-type-precision M⊑
fundamental▹ (⊑castL {A = A} {A′ = A′} {M = M} {M′ = M′} {c = c}
    M⊑ cwt c⊑id) q {ρ} {ρ′} rρ d′ d′∈ =
  bind▹ pA q {D = ⟦ M ⟧ ρ} {D′ = ⟦ M′ ⟧ ρ′} {F = ⟦ c ⟧ᶜ}
    {F′ = ⟦ idᶜ A′ ⟧ᶜ} (fundamental▹ M⊑ pA rρ)
    (proj₂ (coe c⊑id cwt ⊢idᶜ pA q)) d′
    (≫=-unit {D = ⟦ M′ ⟧ ρ′} d′ d′∈)
  where
  pA : A ⊑ A′
  pA = ⊑ᶜᵀ-type-precision M⊑
fundamental▹ (⊑castR {A = A} {A′ = A′} {c′ = c′} M⊑ c′wt id⊑c′) q rρ =
  idlift▹ {c′ = c′} pA q (proj₂ (coe id⊑c′ ⊢idᶜ c′wt pA q))
    (fundamental▹ M⊑ pA rρ)
  where
  pA : A ⊑ A′
  pA = ⊑ᶜᵀ-type-precision M⊑
fundamental▹ (⊑blameR M⦂ A⊑A′) q rρ d′ eq = inj₁ (lift eq)
