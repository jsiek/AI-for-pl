module proof.DenotCoercion where

-- File Charter:
--   * The coercion lemma of the denotational proof of the dynamic gradual
--     guarantee: if c ⊑ᶜ c′ then ⟦ c ⟧ᶜ and ⟦ c′ ⟧ᶜ preserve both relations
--     (Coe◃ and Coe▹, on value sets).
--   * By induction on the coercion-precision derivation.  The injection and
--     projection cases are stated for a tag t (the ground type tagTy t); the
--     function cases go through application to whole argument sets (Λ-βᶜ);
--     the sequence cases through bind; a missing coercion on one side is
--     the identity, absorbed by the inclusions E1–E4 below.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; subst)

open import Types
open import Coercions
open import GraphModel
open import Denotation
open import proof.DenotProps
  using (⟦⟧ᶜ-fin; ⟦⟧ᶜ-mono; wrap-fin; wrap-mono; Λ-βᶜ; ≫=-mono; ●-mono;
         ⌊⌋-⊆; ⌊⌋-mono)
open import proof.DenotSoundness using (≫=-unit; ω?)
open import proof.DenotRelation
open import proof.DenotCompat

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

valset-⊆⌊⌋ : ∀ {D} → ValSet D → D ⊆ ⌊ D ⌋
valset-⊆⌊⌋ {D} vD x x∈ = x∈ , λ eq → ω∉ vD (subst (λ y → y ∈ D) eq x∈)

valset-≢ : ∀ {D d} → ValSet D → d ∈ D → d ≢ ω
valset-≢ {D} vD d∈ eq = ω∉ vD (subst (λ y → y ∈ D) eq d∈)

tagTy-inj : ∀ {t t′} → tagTy t ≡ tagTy t′ → t ≡ t′
tagTy-inj {ℕᵗ} {ℕᵗ} refl = refl
tagTy-inj {ℕᵗ} {⇒ᵗ} ()
tagTy-inj {⇒ᵗ} {ℕᵗ} ()
tagTy-inj {⇒ᵗ} {⇒ᵗ} refl = refl

_≟ᵗ_ : (t t′ : Tag) → t ≡ t′ ⊎ t ≢ t′
ℕᵗ ≟ᵗ ℕᵗ = inj₁ refl
ℕᵗ ≟ᵗ ⇒ᵗ = inj₂ (λ ())
⇒ᵗ ≟ᵗ ℕᵗ = inj₂ (λ ())
⇒ᵗ ≟ᵗ ⇒ᵗ = inj₁ refl

-- ★ ⊑ A′ against the tag t of the ground type below A′
★◃-elimᵗ : ∀ t {A′} (pG : tagTy t ⊑ A′) d {D′}
  → ⊑-★ {A′} ⊢ d ◃ᵛ D′
  → Σ[ u ∈ Val ] (d ≡ tag t u × pG ⊢ u ◃ᵛ D′)
★◃-elimᵗ ℕᵗ ⊑-ℕ d r = ★◃-elim G-ℕ ⊑-ℕ d r
★◃-elimᵗ ⇒ᵗ (⊑-⇒ ⊑-★ ⊑-★) d r = ★◃-elim G-⇒ (⊑-⇒ ⊑-★ ⊑-★) d r

★◃-introᵗ : ∀ t {A′} (pG : tagTy t ⊑ A′) u {D′}
  → pG ⊢ u ◃ᵛ D′ → ⊑-★ {A′} ⊢ tag t u ◃ᵛ D′
★◃-introᵗ ℕᵗ ⊑-ℕ u r = r
★◃-introᵗ ⇒ᵗ (⊑-⇒ ⊑-★ ⊑-★) u r = r

★▹-unfoldᵗ : ∀ t {A′} (pG : tagTy t ⊑ A′) d′ {D}
  → ⊑-★ {A′} ⊢ D ▹ᵛ d′ → pG ⊢ untag t D ▹ᵛ d′
★▹-unfoldᵗ ℕᵗ ⊑-ℕ d′ r = ★▹-unfold G-ℕ ⊑-ℕ d′ r
★▹-unfoldᵗ ⇒ᵗ (⊑-⇒ ⊑-★ ⊑-★) d′ r = ★▹-unfold G-⇒ (⊑-⇒ ⊑-★ ⊑-★) d′ r

★▹-foldᵗ : ∀ t {A′} (pG : tagTy t ⊑ A′) d′ {D}
  → pG ⊢ untag t D ▹ᵛ d′ → ⊑-★ {A′} ⊢ D ▹ᵛ d′
★▹-foldᵗ ℕᵗ ⊑-ℕ d′ r = ★▹-fold G-ℕ ⊑-ℕ d′ r
★▹-foldᵗ ⇒ᵗ (⊑-⇒ ⊑-★ ⊑-★) d′ r = ★▹-fold G-⇒ (⊑-⇒ ⊑-★ ⊑-★) d′ r

Coe : ∀ {A A′ B B′} → A ⊑ A′ → B ⊑ B′ → Coercion → Coercion → Set₁
Coe pA pB c c′ = Coe◃ pA pB c c′ × Coe▹ pA pB c c′

------------------------------------------------------------------------
-- Changing the coercion on either side along inclusions
------------------------------------------------------------------------

coe-adj : ∀ {A A′ B B′} {pA : A ⊑ A′} {pB : B ⊑ B′} {c₁ c₂ c₁′ c₂′}
  → (∀ X → ValSet X → Conv X → ⟦ c₂ ⟧ᶜ X ⊆ ⟦ c₁ ⟧ᶜ X)
  → (∀ X → ValSet X → Conv X → ⟦ c₁ ⟧ᶜ X ⊆ ⟦ c₂ ⟧ᶜ X)
  → (∀ X′ → ValSet X′ → Conv X′ → ⟦ c₁′ ⟧ᶜ X′ ⊆ ⟦ c₂′ ⟧ᶜ X′)
  → (∀ X′ → ValSet X′ → Conv X′ → ⟦ c₂′ ⟧ᶜ X′ ⊆ ⟦ c₁′ ⟧ᶜ X′)
  → Coe pA pB c₁ c₁′ → Coe pA pB c₂ c₂′
coe-adj {pB = pB} l21 l12 r12 r21 (h◃ , h▹) =
  (λ X X′ vX vX′ cX cX′ r d d∈ →
     ◃-mono pB d (r12 X′ vX′ cX′)
       (h◃ X X′ vX vX′ cX cX′ r d (l21 X vX cX d d∈)))
  , (λ X X′ vX vX′ cX cX′ r d′ d′∈ →
     ▹-mono pB d′ (l12 X vX cX)
       (h▹ X X′ vX vX′ cX cX′ r d′ (r21 X′ vX′ cX′ d′ d′∈)))

-- E1: an identity before c
E1 : ∀ {A} c X → ValSet X → Conv X → ⟦ idᶜ A ⨟ c ⟧ᶜ X ⊆ ⟦ c ⟧ᶜ X
E1 c X vX cX x x∈ =
  ⟦⟧ᶜ-mono c ⌊⌋-⊆ x (≫=-ValSet-⊆ {D = X} {F = ⟦ c ⟧ᶜ} vX x x∈)

E2 : ∀ {A} c X → ValSet X → Conv X → ⟦ c ⟧ᶜ X ⊆ ⟦ idᶜ A ⨟ c ⟧ᶜ X
E2 c X vX cX x x∈ = inj₂ (cX , ⟦⟧ᶜ-mono c (valset-⊆⌊⌋ vX) x x∈)

-- E3: an identity after c
E3 : ∀ {B} c X → ValSet X → Conv X → ⟦ c ⨟ idᶜ B ⟧ᶜ X ⊆ ⟦ c ⟧ᶜ X
E3 {B} c X vX cX = ≫=-id-⊆ {A = B} {D = ⟦ c ⟧ᶜ X}

E4 : ∀ {B} c X → ValSet X → Conv X → ⟦ c ⟧ᶜ X ⊆ ⟦ c ⨟ idᶜ B ⟧ᶜ X
E4 c X vX cX = ≫=-unit {D = ⟦ c ⟧ᶜ X}

------------------------------------------------------------------------
-- Identities, errors, and sequences
------------------------------------------------------------------------

idid : ∀ {A A′} (p q : A ⊑ A′) → Coe p q (idᶜ A) (idᶜ A′)
idid p q rewrite ⊑-unique p q =
  (λ X X′ vX vX′ cX cX′ r → r) , (λ X X′ vX vX′ cX cX′ r → r)

bot : ∀ {A A′ B B′} (pA : A ⊑ A′) (pB : B ⊑ B′) c {C D ℓ}
  → Coe pA pB c (⊥ᶜ C ⇨ D at ℓ)
bot pA pB c =
  (λ X X′ vX vX′ cX cX′ r d d∈ → inj₁ (lift (cX′ , refl)))
  , (λ X X′ vX vX′ cX cX′ r d′ (_ , eq) → inj₁ (lift eq))

seq : ∀ {A A′ M M′ B B′} (pA : A ⊑ A′) (pM : M ⊑ M′) (pB : B ⊑ B′)
  {c c′ d d′}
  → Coe pA pM c c′ → Coe pM pB d d′ → Coe pA pB (c ⨟ d) (c′ ⨟ d′)
seq pA pM pB {c} {c′} {d} {d′} (hc◃ , hc▹) (hd◃ , hd▹) =
  (λ X X′ vX vX′ cX cX′ r →
     fbind◃ pM pB {D = ⟦ c ⟧ᶜ X} {D′ = ⟦ c′ ⟧ᶜ X′} {F = ⟦ d ⟧ᶜ}
       {F′ = ⟦ d′ ⟧ᶜ} (hc◃ X X′ vX vX′ cX cX′ r) (⟦⟧ᶜ-fin d)
       (⟦⟧ᶜ-mono d) hd◃)
  , (λ X X′ vX vX′ cX cX′ r →
     bind▹ pM pB {D = ⟦ c ⟧ᶜ X} {D′ = ⟦ c′ ⟧ᶜ X′} {F = ⟦ d ⟧ᶜ}
       {F′ = ⟦ d′ ⟧ᶜ} (hc▹ X X′ vX vX′ cX cX′ r) hd▹)

------------------------------------------------------------------------
-- Injections and projections, at the tag t of the ground type tagTy t
------------------------------------------------------------------------

-- tagTy t ! ⊑ᶜ tagTy t !
injinj : ∀ t → Coe (tag⊑ t) (⊑-★ {★}) (tagTy t !) (tagTy t !)
injinj t = el◃ , el▹
  where
  el◃ : Coe◃ (tag⊑ t) (⊑-★ {★}) (tagTy t !) (tagTy t !)
  el◃ X X′ vX vX′ cX cX′ r (tag t′ v) (eq , v∈) with tagTy-inj eq
  ... | refl =
    inj₂ (◃ᵛ-mono (tag⊑ t) v {X′} {untag t (inj (tagTy t) X′)}
            (λ v′ m → refl , m) (◃-val (tag⊑ t) v vX′ (r v v∈)))
  el◃ X X′ vX vX′ cX cX′ r (nat n) ()
  el◃ X X′ vX vX′ cX cX′ r (V ⟼ w) ()
  el◃ X X′ vX vX′ cX cX′ r ν ()
  el◃ X X′ vX vX′ cX cX′ r ω ()
  el▹ : Coe▹ (tag⊑ t) (⊑-★ {★}) (tagTy t !) (tagTy t !)
  el▹ X X′ vX vX′ cX cX′ r (tag t′ v′) (eq , v′∈) with tagTy-inj eq
  ... | refl =
    inj₂ (▹ᵛ-mono (tag⊑ t) v′ {X} {untag t (inj (tagTy t) X)}
            (λ x m → refl , m)
            (▹-val (tag⊑ t) v′ {X} (valset-≢ vX′ v′∈) (r v′ v′∈)))
  el▹ X X′ vX vX′ cX cX′ r (nat n) ()
  el▹ X X′ vX vX′ cX cX′ r (V ⟼ w) ()
  el▹ X X′ vX vX′ cX cX′ r ν ()
  el▹ X X′ vX vX′ cX cX′ r ω ()

-- tagTy t ?ℓ ⊑ᶜ tagTy t ?ℓ
projproj : ∀ t {ℓ ℓ′}
  → Coe (⊑-★ {★}) (tag⊑ t) ((_`? {ℓ = ℓ}) (tagTy t))
                            ((_`? {ℓ = ℓ′}) (tagTy t))
projproj t {ℓ} {ℓ′} = el◃ {ℓ} {ℓ′} , el▹ {ℓ} {ℓ′}
  where
  el◃ : ∀ {ℓ ℓ′} → Coe◃ (⊑-★ {★}) (tag⊑ t) ((_`? {ℓ = ℓ}) (tagTy t))
                                           ((_`? {ℓ = ℓ′}) (tagTy t))
  el◃ X X′ vX vX′ cX cX′ r w (inj₁ (t′ , eq , m)) with tagTy-inj eq
  ... | refl =
    inj₂ (◃ᵛ-mono (tag⊑ t) w {untag t X′} {proj (tagTy t) X′}
            (λ v m′ → inj₁ (t , refl , m′))
            (◃-val (⊑-★ {★}) (tag t w) vX′ (r (tag t w) m)))
  el◃ X X′ vX vX′ cX cX′ r w (inj₂ (refl , t′ , v , m , ne))
      with ◃ᵛ-conv (tag⊑ t′) v {untag t′ X′}
             (◃-val (⊑-★ {★}) (tag t′ v) vX′ (r (tag t′ v) m))
  ... | v′ , m′ , _ = inj₁ (lift (inj₂ (refl , t′ , v′ , m′ , ne)))
  el▹ : ∀ {ℓ ℓ′} → Coe▹ (⊑-★ {★}) (tag⊑ t) ((_`? {ℓ = ℓ}) (tagTy t))
                                           ((_`? {ℓ = ℓ′}) (tagTy t))
  el▹ X X′ vX vX′ cX cX′ r w′ (inj₁ (t′ , eq , m′)) with tagTy-inj eq
  ... | refl =
    ▹-mono (tag⊑ t) w′ {untag t X} {proj (tagTy t) X}
      (λ v m → inj₁ (t , refl , m))
      (inj₂ (▹-val (⊑-★ {★}) (tag t w′) {X} (λ ()) (r (tag t w′) m′)))
  el▹ X X′ vX vX′ cX cX′ r w′ (inj₂ (refl , _)) = inj₁ (lift refl)

-- id ★ ⊑ᶜ tagTy t !
injidL : ∀ t → Coe (⊑-★ {tagTy t}) (⊑-★ {★}) (idᶜ ★) (tagTy t !)
injidL t = el◃ , el▹
  where
  el◃ : Coe◃ (⊑-★ {tagTy t}) (⊑-★ {★}) (idᶜ ★) (tagTy t !)
  el◃ X X′ vX vX′ cX cX′ r d d∈
      with ★◃-elimᵗ t (tag⊑ t) d {X′} (◃-val (⊑-★ {tagTy t}) d vX′ (r d d∈))
  ... | u , refl , r′ =
    inj₂ (◃ᵛ-mono (tag⊑ t) u {X′} {untag t (inj (tagTy t) X′)}
            (λ v m → refl , m) r′)
  el▹ : Coe▹ (⊑-★ {tagTy t}) (⊑-★ {★}) (idᶜ ★) (tagTy t !)
  el▹ X X′ vX vX′ cX cX′ r (tag t′ v′) (eq , v′∈) with tagTy-inj eq
  ... | refl =
    inj₂ (★▹-unfoldᵗ t (tag⊑ t) v′ {X}
            (▹-val (⊑-★ {tagTy t}) v′ {X} (valset-≢ vX′ v′∈) (r v′ v′∈)))
  el▹ X X′ vX vX′ cX cX′ r (nat n) ()
  el▹ X X′ vX vX′ cX cX′ r (V ⟼ w) ()
  el▹ X X′ vX vX′ cX cX′ r ν ()
  el▹ X X′ vX vX′ cX cX′ r ω ()

-- id ★ ⊑ᶜ tagTy t ?ℓ
projidL : ∀ t {ℓ}
  → Coe (⊑-★ {★}) (⊑-★ {tagTy t}) (idᶜ ★) ((_`? {ℓ = ℓ}) (tagTy t))
projidL t {ℓ} = el◃ {ℓ} , el▹ {ℓ}
  where
  el◃ : ∀ {ℓ} → Coe◃ (⊑-★ {★}) (⊑-★ {tagTy t}) (idᶜ ★)
                       ((_`? {ℓ = ℓ}) (tagTy t))
  el◃ X X′ vX vX′ cX cX′ r d d∈
      with ★★◃-elim d {X′} (◃-val (⊑-★ {★}) d vX′ (r d d∈))
  ... | t′ , u , refl , r′ with t′ ≟ᵗ t
  ...   | inj₁ refl =
    inj₂ (★◃-introᵗ t (tag⊑ t) u
            (◃ᵛ-mono (tag⊑ t) u {untag t X′} {proj (tagTy t) X′}
               (λ v m → inj₁ (t , refl , m)) r′))
  ...   | inj₂ ne with ◃ᵛ-conv (tag⊑ t′) u {untag t′ X′} r′
  ...     | v′ , m′ , _ =
    inj₁ (lift (inj₂ (refl , t′ , v′ , m′ , λ eq → ne (tagTy-inj eq))))
  el▹ : ∀ {ℓ} → Coe▹ (⊑-★ {★}) (⊑-★ {tagTy t}) (idᶜ ★)
                       ((_`? {ℓ = ℓ}) (tagTy t))
  el▹ X X′ vX vX′ cX cX′ r w′ (inj₁ (t′ , eq , m′)) with tagTy-inj eq
  ... | refl =
    inj₂ (★▹-foldᵗ t (tag⊑ t) w′ {X}
            (▹-val (⊑-★ {★}) (tag t w′) {X} (λ ()) (r (tag t w′) m′)))
  el▹ X X′ vX vX′ cX cX′ r w′ (inj₂ (refl , _)) = inj₁ (lift refl)

-- tagTy t ! ⊑ᶜ id A′
injidR : ∀ t {A′} (pG : tagTy t ⊑ A′)
  → Coe pG (⊑-★ {A′}) (tagTy t !) (idᶜ A′)
injidR t {A′} pG = el◃ , el▹
  where
  el◃ : Coe◃ pG (⊑-★ {A′}) (tagTy t !) (idᶜ A′)
  el◃ X X′ vX vX′ cX cX′ r (tag t′ v) (eq , v∈) with tagTy-inj eq
  ... | refl = inj₂ (★◃-introᵗ t pG v (◃-val pG v vX′ (r v v∈)))
  el◃ X X′ vX vX′ cX cX′ r (nat n) ()
  el◃ X X′ vX vX′ cX cX′ r (V ⟼ w) ()
  el◃ X X′ vX vX′ cX cX′ r ν ()
  el◃ X X′ vX vX′ cX cX′ r ω ()
  el▹ : Coe▹ pG (⊑-★ {A′}) (tagTy t !) (idᶜ A′)
  el▹ X X′ vX vX′ cX cX′ r x′ x′∈ =
    inj₂ (★▹-foldᵗ t pG x′
            (▹ᵛ-mono pG x′ {X} {untag t (inj (tagTy t) X)}
               (λ v m → refl , m)
               (▹-val pG x′ {X} (valset-≢ vX′ x′∈) (r x′ x′∈))))

-- tagTy t ?ℓ ⊑ᶜ id A′
projidR : ∀ t {A′ ℓ} (pG : tagTy t ⊑ A′)
  → Coe (⊑-★ {A′}) pG ((_`? {ℓ = ℓ}) (tagTy t)) (idᶜ A′)
projidR t {A′} {ℓ} pG = el◃ {ℓ} , el▹ {ℓ}
  where
  el◃ : ∀ {ℓ} → Coe◃ (⊑-★ {A′}) pG ((_`? {ℓ = ℓ}) (tagTy t)) (idᶜ A′)
  el◃ X X′ vX vX′ cX cX′ r w (inj₁ (t′ , eq , m)) with tagTy-inj eq
  ... | refl
      with ★◃-elimᵗ t pG (tag t w) {X′}
             (◃-val (⊑-★ {A′}) (tag t w) vX′ (r _ m))
  ...   | u , refl , r′ = inj₂ r′
  el◃ X X′ vX vX′ cX cX′ r w (inj₂ (refl , t′ , v , m , ne))
      with ★◃-elimᵗ t pG (tag t′ v) {X′}
             (◃-val (⊑-★ {A′}) (tag t′ v) vX′ (r _ m))
  ... | u , refl , r′ = ⊥-elim (ne refl)
  el▹ : ∀ {ℓ} → Coe▹ (⊑-★ {A′}) pG ((_`? {ℓ = ℓ}) (tagTy t)) (idᶜ A′)
  el▹ X X′ vX vX′ cX cX′ r x′ x′∈ =
    ▹-mono pG x′ {untag t X} {proj (tagTy t) X}
      (λ v m → inj₁ (t , refl , m))
      (inj₂ (★▹-unfoldᵗ t pG x′ {X}
               (▹-val (⊑-★ {A′}) x′ {X} (valset-≢ vX′ x′∈) (r x′ x′∈))))

------------------------------------------------------------------------
-- Function coercions
------------------------------------------------------------------------

-- the body of a function wrapper
wrapF : Coercion → Coercion → 𝒫 → 𝒫 → 𝒫
wrapF c d X Y = ⟦ c ⟧ᶜ Y ≫= λ Y₁ → (X ● Y₁) ≫= ⟦ d ⟧ᶜ

-- the entries of a wrapped function are values
guard-Λ-⌊⌋ : ∀ {X} F → Conv X → Λ F ⊆ ⌊ guard X (Λ F) ⌋
guard-Λ-⌊⌋ F cX e e∈ = (cX , e∈) , Λ≢ω e e∈

-- c ↦ d ⊑ᶜ c′ ↦ d′
wrap : ∀ {A₁ A₁′ B₁ B₁′ C C′ D D′}
  (pa : A₁ ⊑ A₁′) (pb : B₁ ⊑ B₁′) (pc : C ⊑ C′) (pd : D ⊑ D′) {c c′ d d′}
  → Coe pc pa c c′ → Coe pb pd d d′
  → Coe (⊑-⇒ pa pb) (⊑-⇒ pc pd) (c ↦ d) (c′ ↦ d′)
wrap pa pb pc pd {c} {c′} {d} {d′} (hc◃ , hc▹) (hd◃ , hd▹) = el◃ , el▹
  where
  el◃ : Coe◃ (⊑-⇒ pa pb) (⊑-⇒ pc pd) (c ↦ d) (c′ ↦ d′)
  el◃ X X′ vX vX′ cX cX′ rX ν (_ , _) = inj₂ (lift (cX′ , tt))
  el◃ X X′ vX vX′ cX cX′ rX (U ⟼ w) (_ , w∈ , U≢ , ne) =
    inj₂ (lift (cX′ , tt) , clause)
    where
    clause : ∀ E′ → ValSet E′ → U ≢ [] → pc ⊢ U ◃* E′
      → pd ⊢ w ◃ (⌊ ⟦ c′ ↦ d′ ⟧ᶜ X′ ⌋ ● E′)
    clause E′ vE′ _ rU =
      ◃-mono pd w
        (λ x x∈ → ●-monoˡ (guard-Λ-⌊⌋ (wrapF c′ d′ X′) cX′) x
                    (Λ-βᶜ c′ d′ X′ vE′ cE′ x x∈))
        (fbind◃ pa pd {D = ⟦ c ⟧ᶜ (mem U)} {D′ = ⟦ c′ ⟧ᶜ E′}
           {F = λ Y → (X ● Y) ≫= ⟦ d ⟧ᶜ}
           {F′ = λ Y′ → (X′ ● Y′) ≫= ⟦ d′ ⟧ᶜ}
           (hc◃ (mem U) E′ (valset ne) vE′ (list-conv U U≢ ne) cE′
              (λ u u∈ → ◃*-∈ pc rU u u∈))
           (wrap-fin X d) (wrap-mono X d) inner w w∈)
      where
      cE′ = ◃*-conv pc U U≢ vE′ rU
      inner : ∀ Y Y′ → ValSet Y → ValSet Y′ → Conv Y → Conv Y′
        → pa ⊢ Y ◃ˢ Y′
        → pd ⊢ ((X ● Y) ≫= ⟦ d ⟧ᶜ) ◃ˢ ((X′ ● Y′) ≫= ⟦ d′ ⟧ᶜ)
      inner Y Y′ vY vY′ cY cY′ rY =
        fbind◃ pb pd {D = X ● Y} {D′ = X′ ● Y′} {F = ⟦ d ⟧ᶜ}
          {F′ = ⟦ d′ ⟧ᶜ} (app◃ pa pb vX′ vY′ rX rY) (⟦⟧ᶜ-fin d)
          (⟦⟧ᶜ-mono d) hd◃
  el◃ X X′ vX vX′ cX cX′ rX (nat n) (_ , ())
  el◃ X X′ vX vX′ cX cX′ rX ω (_ , ())
  el◃ X X′ vX vX′ cX cX′ rX (tag t u) (_ , ())
  el▹ : Coe▹ (⊑-⇒ pa pb) (⊑-⇒ pc pd) (c ↦ d) (c′ ↦ d′)
  el▹ X X′ vX vX′ cX cX′ rX ν (_ , _) = inj₂ (lift (cX , tt))
  el▹ X X′ vX vX′ cX cX′ rX (V′ ⟼ w′) (_ , w′∈ , V′≢ , ne′) =
    inj₂ (lift (cX , tt) , clause)
    where
    clause : ∀ E → ValSet E → V′ ≢ [] → NoErr V′ → pc ⊢ E ▹* V′
      → pd ⊢ (⌊ ⟦ c ↦ d ⟧ᶜ X ⌋ ● E) ▹ w′
    clause E vE _ _ rV =
      ▹-mono pd w′
        (λ x x∈ → ●-monoˡ (guard-Λ-⌊⌋ (wrapF c d X) cX) x
                    (Λ-βᶜ c d X vE cE x x∈))
        (bind▹ pa pd {D = ⟦ c ⟧ᶜ E} {D′ = ⟦ c′ ⟧ᶜ (mem V′)}
           {F = λ Y → (X ● Y) ≫= ⟦ d ⟧ᶜ}
           {F′ = λ Y′ → (X′ ● Y′) ≫= ⟦ d′ ⟧ᶜ}
           (hc▹ E (mem V′) vE (valset ne′) cE (list-conv V′ V′≢ ne′)
              (λ v′ v′∈ → ▹*-∈ pc rV v′ v′∈))
           inner w′ w′∈)
      where
      cE = ▹*-conv pc V′ V′≢ ne′ rV
      inner : ∀ Y Y′ → ValSet Y → ValSet Y′ → Conv Y → Conv Y′
        → pa ⊢ Y ▹ˢ Y′
        → pd ⊢ ((X ● Y) ≫= ⟦ d ⟧ᶜ) ▹ˢ ((X′ ● Y′) ≫= ⟦ d′ ⟧ᶜ)
      inner Y Y′ vY vY′ cY cY′ rY =
        bind▹ pb pd {D = X ● Y} {D′ = X′ ● Y′} {F = ⟦ d ⟧ᶜ}
          {F′ = ⟦ d′ ⟧ᶜ} (app▹ pa pb vY vY′ rX rY) hd▹
  el▹ X X′ vX vX′ cX cX′ rX (nat n) (_ , ())
  el▹ X X′ vX vX′ cX cX′ rX ω (_ , ())
  el▹ X X′ vX vX′ cX cX′ rX (tag t u) (_ , ())

-- id (A ⇒ B) ⊑ᶜ c′ ↦ d′, one function element at a time
wrapR◃ᵛ : ∀ {A B A₁′ B₁′ C′ D′}
  (pa : A ⊑ A₁′) (pb : B ⊑ B₁′) (pc : A ⊑ C′) (pd : B ⊑ D′) {c′ d′}
  → Coe◃ pc pa (idᶜ A) c′ → Coe◃ pb pd (idᶜ B) d′
  → ∀ {X′} → ValSet X′ → Conv X′
  → ∀ u → ⊑-⇒ pa pb ⊢ u ◃ᵛ X′ → ⊑-⇒ pc pd ⊢ u ◃ᵛ ⟦ c′ ↦ d′ ⟧ᶜ X′
wrapR◃ᵛ pa pb pc pd hc hd vX′ cX′ (nat n) ()
wrapR◃ᵛ pa pb pc pd hc hd vX′ cX′ ν (lift ν∈) = lift (cX′ , tt)
wrapR◃ᵛ pa pb pc pd hc hd vX′ cX′ ω ()
wrapR◃ᵛ pa pb pc pd hc hd vX′ cX′ (tag t u) ()
wrapR◃ᵛ pa pb pc pd {c′} {d′} hc hd {X′} vX′ cX′ (U ⟼ w) (lift ν∈ , f) =
  lift (cX′ , tt) , clause
  where
  clause : ∀ E′ → ValSet E′ → U ≢ [] → pc ⊢ U ◃* E′
    → pd ⊢ w ◃ (⌊ ⟦ c′ ↦ d′ ⟧ᶜ X′ ⌋ ● E′)
  clause E′ vE′ U≢ rU =
    ◃-mono pd w
      (λ x x∈ → ●-monoˡ (guard-Λ-⌊⌋ (wrapF c′ d′ X′) cX′) x
                  (Λ-βᶜ c′ d′ X′ vE′ cE′ x x∈))
      body
    where
    cE′ = ◃*-conv pc U U≢ vE′ rU
    neU = ◃*-noerr pc U vE′ rU
    C = ⟦ c′ ⟧ᶜ E′
    s1 : pa ⊢ mem U ◃ˢ C
    s1 = hc (mem U) E′ (valset neU) vE′ (list-conv U U≢ neU) cE′
           (λ u u∈ → ◃*-∈ pc rU u u∈)
    body : pd ⊢ w ◃ (C ≫= λ Y → (X′ ● Y) ≫= ⟦ d′ ⟧ᶜ)
    body with all◃ pa U s1
    ... | inj₁ (lift ω∈) = inj₁ (lift (inj₁ (refl , ω∈)))
    ... | inj₂ rs =
      ◃-mono pd w sub2
        (idlift◃ {c′ = d′} pb pd hd w {⌊ X′ ⌋ ● ⌊ C ⌋}
           (f ⌊ C ⌋ (ValSet-⌊⌋ C) U≢ rs))
      where
      cC : Conv C
      cC = ⌊⌋-Conv (◃*-conv pa U U≢ (ValSet-⌊⌋ C) rs)
      sub2 : ((⌊ X′ ⌋ ● ⌊ C ⌋) ≫= ⟦ d′ ⟧ᶜ)
             ⊆ (C ≫= λ Y → (X′ ● Y) ≫= ⟦ d′ ⟧ᶜ)
      sub2 x x∈ =
        inj₂ (cC , ≫=-mono {D = ⌊ X′ ⌋ ● ⌊ C ⌋} {D′ = X′ ● ⌊ C ⌋}
                     {F = ⟦ d′ ⟧ᶜ} {F′ = ⟦ d′ ⟧ᶜ}
                     (●-monoˡ (⌊⌋-⊆ {X′})) (⟦⟧ᶜ-mono d′) x x∈)

wrapR▹ : ∀ {A B A₁′ B₁′ C′ D′}
  (pa : A ⊑ A₁′) (pb : B ⊑ B₁′) (pc : A ⊑ C′) (pd : B ⊑ D′) {c′ d′}
  → Coe▹ pc pa (idᶜ A) c′ → Coe▹ pb pd (idᶜ B) d′
  → ∀ {X₀ X′} → ValSet X′ → Conv X′
  → ⊑-⇒ pa pb ⊢ X₀ ▹ˢ X′ → ⊑-⇒ pc pd ⊢ X₀ ▹ˢ ⟦ c′ ↦ d′ ⟧ᶜ X′
wrapR▹ pa pb pc pd {c′} {d′} hc hd {X₀} {X′} vX′ cX′ rX = el
  where
  ν∈X₀ : ν ∈ X₀
  ν∈X₀ =
    ▹ᵛ⇒-ν pa pb (proj₁ cX′)
      (▹-val (⊑-⇒ pa pb) (proj₁ cX′) (proj₂ (proj₂ cX′))
         (rX (proj₁ cX′) (proj₁ (proj₂ cX′))))
  el : ⊑-⇒ pc pd ⊢ X₀ ▹ˢ ⟦ c′ ↦ d′ ⟧ᶜ X′
  el ν _ = inj₂ (lift ν∈X₀)
  el (V′ ⟼ w′) (_ , w′∈ , V′≢ , ne′) = inj₂ (lift ν∈X₀ , clause)
    where
    clause : ∀ E → ValSet E → V′ ≢ [] → NoErr V′ → pc ⊢ E ▹* V′
      → pd ⊢ (⌊ X₀ ⌋ ● E) ▹ w′
    clause E vE _ _ rV = go w′∈
      where
      cE = ▹*-conv pc V′ V′≢ ne′ rV
      C = ⟦ c′ ⟧ᶜ (mem V′)
      s1 : pa ⊢ E ▹ˢ C
      s1 = hc E (mem V′) vE (valset ne′) cE (list-conv V′ V′≢ ne′)
             (λ v′ v′∈ → ▹*-∈ pc rV v′ v′∈)
      go : w′ ∈ (C ≫= λ Y → (X′ ● Y) ≫= ⟦ d′ ⟧ᶜ)
        → pd ⊢ (⌊ X₀ ⌋ ● E) ▹ w′
      go (inj₁ (refl , _)) = inj₁ (lift refl)
      go (inj₂ (cC , inj₁ (refl , _))) = inj₁ (lift refl)
      go (inj₂ (cC , inj₂ (cXY , w′∈d))) =
        ▹-mono pd w′ (●-⌊⌋ {D = X₀} {E = E})
          (idlift▹ {c′ = d′} pb pd hd {D = X₀ ● E} {S = X′ ● ⌊ C ⌋}
             (app▹ pa pb {X = X₀} {X′ = X′} {Y = E} {Y′ = ⌊ C ⌋}
                vE (ValSet-⌊⌋ C) rX
                (λ v (v∈ , v≢) → s1 v v∈))
             w′ (inj₂ (cXY , w′∈d)))
  el (nat n) (_ , ())
  el ω (_ , ())
  el (tag t u) (_ , ())

-- id (A ⇒ B) ⊑ᶜ c′ ↦ d′
idL↦ : ∀ {A B A₁′ B₁′ C′ D′}
  (pa : A ⊑ A₁′) (pb : B ⊑ B₁′) (pc : A ⊑ C′) (pd : B ⊑ D′) {c′ d′}
  → Coe pc pa (idᶜ A) c′ → Coe pb pd (idᶜ B) d′
  → Coe (⊑-⇒ pa pb) (⊑-⇒ pc pd) (idᶜ (A ⇒ B)) (c′ ↦ d′)
idL↦ pa pb pc pd {c′} {d′} (hc◃ , hc▹) (hd◃ , hd▹) =
  (λ X X′ vX vX′ cX cX′ r d d∈ →
     inj₂ (wrapR◃ᵛ pa pb pc pd {c′} {d′} hc◃ hd◃ vX′ cX′ d
             (◃-val (⊑-⇒ pa pb) d vX′ (r d d∈))))
  , (λ X X′ vX vX′ cX cX′ r →
       wrapR▹ pa pb pc pd {c′} {d′} hc▹ hd▹ {X} vX′ cX′ r)

-- id ★ ⊑ᶜ c′ ↦ d′
idL↦★ : ∀ {A₁′ B₁′ C′ D′} {c′ d′}
  → Coe (⊑-★ {C′}) (⊑-★ {A₁′}) (idᶜ ★) c′
  → Coe (⊑-★ {B₁′}) (⊑-★ {D′}) (idᶜ ★) d′
  → Coe (⊑-★ {A₁′ ⇒ B₁′}) (⊑-★ {C′ ⇒ D′}) (idᶜ ★) (c′ ↦ d′)
idL↦★ {A₁′} {B₁′} {C′} {D′} {c′} {d′} (hc◃ , hc▹) (hd◃ , hd▹) =
  el◃ , el▹
  where
  p⇒ : (★ ⇒ ★) ⊑ (A₁′ ⇒ B₁′)
  p⇒ = ⊑-⇒ ⊑-★ ⊑-★
  q⇒ : (★ ⇒ ★) ⊑ (C′ ⇒ D′)
  q⇒ = ⊑-⇒ ⊑-★ ⊑-★
  el◃ : Coe◃ (⊑-★ {A₁′ ⇒ B₁′}) (⊑-★ {C′ ⇒ D′}) (idᶜ ★) (c′ ↦ d′)
  el◃ X X′ vX vX′ cX cX′ r d d∈
      with ★◃-elim G-⇒ p⇒ d {X′}
             (◃-val (⊑-★ {A₁′ ⇒ B₁′}) d vX′ (r d d∈))
  ... | u , refl , r′ =
    inj₂ (★◃-intro G-⇒ q⇒ u
            (wrapR◃ᵛ (⊑-★ {A₁′}) (⊑-★ {B₁′}) (⊑-★ {C′}) (⊑-★ {D′})
               {c′} {d′} hc◃ hd◃ vX′ cX′ u r′))
  el▹ : Coe▹ (⊑-★ {A₁′ ⇒ B₁′}) (⊑-★ {C′ ⇒ D′}) (idᶜ ★) (c′ ↦ d′)
  el▹ X X′ vX vX′ cX cX′ r y′ y′∈
      with wrapR▹ (⊑-★ {A₁′}) (⊑-★ {B₁′}) (⊑-★ {C′}) (⊑-★ {D′})
             {c′} {d′} hc▹ hd▹ {X₀ = untag ⇒ᵗ X} vX′ cX′ rel0 y′ y′∈
    where
    rel0 : p⇒ ⊢ untag ⇒ᵗ X ▹ˢ X′
    rel0 x′ x′∈ with r x′ x′∈
    ... | inj₁ e = inj₁ e
    ... | inj₂ r′ = inj₂ (★▹-unfold G-⇒ p⇒ x′ {X} r′)
  ... | inj₁ e = inj₁ e
  ... | inj₂ r″ = inj₂ (★▹-fold G-⇒ q⇒ y′ {X} r″)

-- c ↦ d ⊑ᶜ id (A′ ⇒ B′)
wrapL : ∀ {A₁ B₁ C D A′ B′}
  (pa : A₁ ⊑ A′) (pb : B₁ ⊑ B′) (pc : C ⊑ A′) (pd : D ⊑ B′) {c d}
  → Coe pc pa c (idᶜ A′) → Coe pb pd d (idᶜ B′)
  → Coe (⊑-⇒ pa pb) (⊑-⇒ pc pd) (c ↦ d) (idᶜ (A′ ⇒ B′))
wrapL {A′ = A′} {B′ = B′} pa pb pc pd {c} {d} (hc◃ , hc▹) (hd◃ , hd▹) =
  el◃ , el▹
  where
  el◃ : Coe◃ (⊑-⇒ pa pb) (⊑-⇒ pc pd) (c ↦ d) (idᶜ (A′ ⇒ B′))
  el◃ X X′ vX vX′ cX cX′ rX w w∈ = go w w∈
    where
    ν∈X′ : ν ∈ X′
    ν∈X′ =
      ◃ᵛ⇒-ν pa pb (proj₁ cX)
        (◃-val (⊑-⇒ pa pb) (proj₁ cX) vX′
           (rX (proj₁ cX) (proj₁ (proj₂ cX))))
    go : ∀ w → w ∈ ⟦ c ↦ d ⟧ᶜ X → ⊑-⇒ pc pd ⊢ w ◃ X′
    go ν _ = inj₂ (lift ν∈X′)
    go (U ⟼ w) (_ , w∈ , U≢ , ne) = inj₂ (lift ν∈X′ , clause)
      where
      clause : ∀ E′ → ValSet E′ → U ≢ [] → pc ⊢ U ◃* E′
        → pd ⊢ w ◃ (⌊ X′ ⌋ ● E′)
      clause E′ vE′ _ rU =
        ◃-mono pd w sub
          (fbind◃ pa pd {D = ⟦ c ⟧ᶜ (mem U)} {D′ = E′}
             {F = λ Y → (X ● Y) ≫= ⟦ d ⟧ᶜ}
             {F′ = λ Y′ → (X′ ● Y′) ≫= ⟦ idᶜ B′ ⟧ᶜ}
             (hc◃ (mem U) E′ (valset ne) vE′ (list-conv U U≢ ne) cE′
                (λ u u∈ → ◃*-∈ pc rU u u∈))
             (wrap-fin X d) (wrap-mono X d) inner w w∈)
        where
        cE′ = ◃*-conv pc U U≢ vE′ rU
        inner : ∀ Y Y′ → ValSet Y → ValSet Y′ → Conv Y → Conv Y′
          → pa ⊢ Y ◃ˢ Y′
          → pd ⊢ ((X ● Y) ≫= ⟦ d ⟧ᶜ) ◃ˢ ((X′ ● Y′) ≫= ⟦ idᶜ B′ ⟧ᶜ)
        inner Y Y′ vY vY′ cY cY′ rY =
          fbind◃ pb pd {D = X ● Y} {D′ = X′ ● Y′} {F = ⟦ d ⟧ᶜ}
            {F′ = ⟦ idᶜ B′ ⟧ᶜ} (app◃ pa pb vX′ vY′ rX rY) (⟦⟧ᶜ-fin d)
            (⟦⟧ᶜ-mono d) hd◃
        sub : (E′ ≫= λ Y′ → (X′ ● Y′) ≫= ⟦ idᶜ B′ ⟧ᶜ) ⊆ (⌊ X′ ⌋ ● E′)
        sub x x∈ =
          ●-mono (valset-⊆⌊⌋ vX′) ⌊⌋-⊆ x
            (≫=-id-⊆ {A = B′} {D = X′ ● ⌊ E′ ⌋} x
               (≫=-ValSet-⊆ {D = E′}
                  {F = λ Y′ → (X′ ● Y′) ≫= ⟦ idᶜ B′ ⟧ᶜ} vE′ x x∈))
    go (nat n) (_ , ())
    go ω (_ , ())
    go (tag t u) (_ , ())
  el▹ : Coe▹ (⊑-⇒ pa pb) (⊑-⇒ pc pd) (c ↦ d) (idᶜ (A′ ⇒ B′))
  el▹ X X′ vX vX′ cX cX′ rX x′ x′∈ = go x′ (rX x′ x′∈)
    where
    go : ∀ x′ → ⊑-⇒ pa pb ⊢ X ▹ x′ → ⊑-⇒ pc pd ⊢ ⟦ c ↦ d ⟧ᶜ X ▹ x′
    go x′ (inj₁ e) = inj₁ e
    go ν (inj₂ (lift _)) = inj₂ (lift (cX , tt))
    go (V′ ⟼ w′) (inj₂ (lift _ , g)) = inj₂ (lift (cX , tt) , clause)
      where
      clause : ∀ E → ValSet E → V′ ≢ [] → NoErr V′ → pc ⊢ E ▹* V′
        → pd ⊢ (⌊ ⟦ c ↦ d ⟧ᶜ X ⌋ ● E) ▹ w′
      clause E vE V′≢ neV rV = finish (ω? w′)
        where
        cE = ▹*-conv pc V′ V′≢ neV rV
        C = ⟦ c ⟧ᶜ E
        s1 : pa ⊢ C ▹ˢ mem V′
        s1 = hc▹ E (mem V′) vE (valset neV) cE (list-conv V′ V′≢ neV)
               (λ v′ v′∈ → ▹*-∈ pc rV v′ v′∈)
        cC : Conv C
        cC = ▹*-conv pa V′ V′≢ neV
               (▹*-intro pa V′ (λ v′ v′∈ → s1 v′ v′∈))
        rw : pb ⊢ (⌊ X ⌋ ● ⌊ C ⌋) ▹ w′
        rw = g ⌊ C ⌋ (ValSet-⌊⌋ C) V′≢ neV
               (▹*-intro pa V′ (λ v′ v′∈ → ▹-vals pa v′ (s1 v′ v′∈)))
        finish : w′ ≡ ω ⊎ w′ ≢ ω → pd ⊢ (⌊ ⟦ c ↦ d ⟧ᶜ X ⌋ ● E) ▹ w′
        finish (inj₁ refl) = inj₁ (lift refl)
        finish (inj₂ w′≢) =
          ▹-mono pd w′ sub
            (hd▹ ⌊ S ⌋ (mem (w′ ∷ [])) (ValSet-⌊⌋ S) (ValSet-sing w′≢)
               cS (w′ , here refl , w′≢) rel w′ (here refl))
          where
          S = ⌊ X ⌋ ● ⌊ C ⌋
          r′ = ▹ᵛ-vals pb w′ (▹-val pb w′ w′≢ rw)
          cS : Conv ⌊ S ⌋
          cS = ▹ᵛ-conv pb w′ r′
          rel : pb ⊢ ⌊ S ⌋ ▹ˢ mem (w′ ∷ [])
          rel v (here refl) = inj₂ r′
          rel v (there ())
          cXC : Conv (X ● ⌊ C ⌋)
          cXC =
            proj₁ cS
            , ●-monoˡ (⌊⌋-⊆ {X}) (proj₁ cS) (proj₁ (proj₁ (proj₂ cS)))
            , proj₂ (proj₂ cS)
          sub : ⟦ d ⟧ᶜ ⌊ S ⌋ ⊆ (⌊ ⟦ c ↦ d ⟧ᶜ X ⌋ ● E)
          sub x x∈ =
            ●-monoˡ (guard-Λ-⌊⌋ (wrapF c d X) cX) x
              (Λ-βᶜ c d X vE cE x
                 (inj₂ (cC , inj₂ (cXC ,
                   ⟦⟧ᶜ-mono d (⌊⌋-mono (●-monoˡ (⌊⌋-⊆ {X}))) x x∈))))
    go (nat n) (inj₂ ())
    go ω (inj₂ ())
    go (tag t u) (inj₂ ())

------------------------------------------------------------------------
-- The coercion lemma
------------------------------------------------------------------------

coe : ∀ {c c′ A B A′ B′}
  → c ⊑ᶜ c′ → ⊢ c ⦂ A ⇨ B → ⊢ c′ ⦂ A′ ⇨ B′
  → (pA : A ⊑ A′) (pB : B ⊑ B′) → Coe pA pB c c′
coe (⊑idᶜ _) ⊢idᶜ ⊢idᶜ pA pB = idid pA pB
coe (⊑! _) (⊢! G-ℕ) (⊢! G-ℕ) ⊑-ℕ ⊑-★ = injinj ℕᵗ
coe (⊑! _) (⊢! G-⇒) (⊢! G-⇒) (⊑-⇒ ⊑-★ ⊑-★) ⊑-★ = injinj ⇒ᵗ
coe (⊑? _) (⊢? {ℓ = ℓ} G-ℕ) (⊢? {ℓ = ℓ′} G-ℕ) ⊑-★ ⊑-ℕ =
  projproj ℕᵗ {ℓ} {ℓ′}
coe (⊑? _) (⊢? {ℓ = ℓ} G-⇒) (⊢? {ℓ = ℓ′} G-⇒) ⊑-★ (⊑-⇒ ⊑-★ ⊑-★) =
  projproj ⇒ᵗ {ℓ} {ℓ′}
coe (⊑↦ c⊑ d⊑) (⊢↦ {c = c} {d = d} cwt dwt)
    (⊢↦ {c = c′} {d = d′} c′wt d′wt) (⊑-⇒ pa pb) (⊑-⇒ pc pd) =
  wrap pa pb pc pd {c} {c′} {d} {d′}
    (coe c⊑ cwt c′wt pc pa) (coe d⊑ dwt d′wt pb pd)
coe (⊑⨟ c⊑ d⊑) (⊢⨟ {c = c} {d = d} cwt dwt)
    (⊢⨟ {c = c′} {d = d′} c′wt d′wt) pA pB =
  seq pA pM pB {c} {c′} {d} {d′}
    (coe c⊑ cwt c′wt pA pM) (coe d⊑ dwt d′wt pM pB)
  where
  pM = proj₂ (⊑ᶜ→⊑ c′wt cwt c⊑)
coe (⊑idL atom-idᶜ _ _ _) ⊢idᶜ ⊢idᶜ pA pB = idid pA pB
coe (⊑idL atom-! _ _ _) ⊢idᶜ (⊢! G-ℕ) ⊑-★ ⊑-★ = injidL ℕᵗ
coe (⊑idL atom-! _ _ _) ⊢idᶜ (⊢! G-⇒) ⊑-★ ⊑-★ = injidL ⇒ᵗ
coe (⊑idL atom-? _ _ _) ⊢idᶜ (⊢? {ℓ = ℓ} G-ℕ) ⊑-★ ⊑-★ = projidL ℕᵗ {ℓ}
coe (⊑idL atom-? _ _ _) ⊢idᶜ (⊢? {ℓ = ℓ} G-⇒) ⊑-★ ⊑-★ = projidL ⇒ᵗ {ℓ}
coe (⊑idL↦★ c⊑ d⊑) ⊢idᶜ (⊢↦ {c = c′} {d = d′} c′wt d′wt) ⊑-★ ⊑-★ =
  idL↦★ {c′ = c′} {d′ = d′} (coe c⊑ ⊢idᶜ c′wt ⊑-★ ⊑-★) (coe d⊑ ⊢idᶜ d′wt ⊑-★ ⊑-★)
coe (⊑idL↦ c⊑ d⊑) ⊢idᶜ (⊢↦ {c = c′} {d = d′} c′wt d′wt)
    (⊑-⇒ pa pb) (⊑-⇒ pc pd) =
  idL↦ pa pb pc pd {c′} {d′} (coe c⊑ ⊢idᶜ c′wt pc pa) (coe d⊑ ⊢idᶜ d′wt pb pd)
coe (⊑idL⨟ {c = c′} {d = d′} c⊑ d⊑) (⊢idᶜ {A = A}) (⊢⨟ c′wt d′wt) pA pB =
  coe-adj {pA = pA} {pB = pB} {c₁ = idᶜ A ⨟ idᶜ A} {c₂ = idᶜ A}
    {c₁′ = c′ ⨟ d′} {c₂′ = c′ ⨟ d′}
    (λ X vX cX → E4 {B = A} (idᶜ A) X vX cX)
    (λ X vX cX → E3 {B = A} (idᶜ A) X vX cX)
    (λ X′ vX′ cX′ x x∈ → x∈) (λ X′ vX′ cX′ x x∈ → x∈)
    (seq pA pM pB {c = idᶜ A} {c′ = c′} {d = idᶜ A} {d′ = d′}
       (coe c⊑ ⊢idᶜ c′wt pA pM) (coe d⊑ ⊢idᶜ d′wt pM pB))
  where
  pM = proj₂ (⊑ᶜ→⊑ c′wt ⊢idᶜ c⊑)
coe (⊑idR atom-idᶜ _ _ _) ⊢idᶜ ⊢idᶜ pA pB = idid pA pB
coe (⊑idR atom-! _ _ _) (⊢! G-ℕ) ⊢idᶜ pA ⊑-★ = injidR ℕᵗ pA
coe (⊑idR atom-! _ _ _) (⊢! G-⇒) ⊢idᶜ pA ⊑-★ = injidR ⇒ᵗ pA
coe (⊑idR atom-? _ _ _) (⊢? {ℓ = ℓ} G-ℕ) ⊢idᶜ ⊑-★ pB =
  projidR ℕᵗ {ℓ = ℓ} pB
coe (⊑idR atom-? _ _ _) (⊢? {ℓ = ℓ} G-⇒) ⊢idᶜ ⊑-★ pB =
  projidR ⇒ᵗ {ℓ = ℓ} pB
coe (⊑idR↦ c⊑ d⊑) (⊢↦ {c = c} {d = d} cwt dwt) ⊢idᶜ
    (⊑-⇒ pa pb) (⊑-⇒ pc pd) =
  wrapL pa pb pc pd {c} {d} (coe c⊑ cwt ⊢idᶜ pc pa) (coe d⊑ dwt ⊢idᶜ pb pd)
coe (⊑idR⨟ {A = A′} {c = c} {d = d} c⊑ d⊑) (⊢⨟ cwt dwt) ⊢idᶜ pA pB =
  coe-adj {pA = pA} {pB = pB} {c₁ = c ⨟ d} {c₂ = c ⨟ d}
    {c₁′ = idᶜ A′ ⨟ idᶜ A′} {c₂′ = idᶜ A′}
    (λ X vX cX x x∈ → x∈) (λ X vX cX x x∈ → x∈)
    (λ X′ vX′ cX′ → E3 {B = A′} (idᶜ A′) X′ vX′ cX′)
    (λ X′ vX′ cX′ → E4 {B = A′} (idᶜ A′) X′ vX′ cX′)
    (seq pA pM pB {c = c} {c′ = idᶜ A′} {d = d} {d′ = idᶜ A′}
       (coe c⊑ cwt ⊢idᶜ pA pM) (coe d⊑ dwt ⊢idᶜ pM pB))
  where
  pM = proj₂ (⊑ᶜ→⊑ ⊢idᶜ cwt c⊑)
coe {A′ = A′} (⊑drop? {c = c′} {c′ = c} {ℓ = ℓ} c⊑) (⊢⨟ (⊢? G-⇒) cwt)
    c′wt ⊑-★ pB =
  coe-adj {pA = ⊑-★ {A′}} {pB = pB}
    {c₁ = (_`? {ℓ = ℓ}) (★ ⇒ ★) ⨟ c} {c₂ = (_`? {ℓ = ℓ}) (★ ⇒ ★) ⨟ c}
    {c₁′ = idᶜ A′ ⨟ c′} {c₂′ = c′}
    (λ X vX cX x x∈ → x∈) (λ X vX cX x x∈ → x∈)
    (λ X′ vX′ cX′ → E1 {A = A′} c′ X′ vX′ cX′)
    (λ X′ vX′ cX′ → E2 {A = A′} c′ X′ vX′ cX′)
    (seq (⊑-★ {A′}) pM pB {c = (_`? {ℓ = ℓ}) (★ ⇒ ★)} {c′ = idᶜ A′}
       {d = c} {d′ = c′} (projidR ⇒ᵗ {ℓ = ℓ} pM) (coe c⊑ cwt c′wt pM pB))
  where
  pM : (★ ⇒ ★) ⊑ A′
  pM = proj₁ (⊑ᶜ→⊑ c′wt cwt c⊑)
coe (⊑drop! {c = c′} {c′ = c} c⊑) (⊢⨟ cwt (⊢! G-⇒)) c′wt pA
    (⊑-★ {B′}) =
  coe-adj {pA = pA} {pB = ⊑-★ {B′}} {c₁ = c ⨟ ((★ ⇒ ★) !)}
    {c₂ = c ⨟ ((★ ⇒ ★) !)} {c₁′ = c′ ⨟ idᶜ B′} {c₂′ = c′}
    (λ X vX cX x x∈ → x∈) (λ X vX cX x x∈ → x∈)
    (λ X′ vX′ cX′ → E3 {B = B′} c′ X′ vX′ cX′)
    (λ X′ vX′ cX′ → E4 {B = B′} c′ X′ vX′ cX′)
    (seq pA pM (⊑-★ {B′}) {c = c} {c′ = c′} {d = (★ ⇒ ★) !}
       {d′ = idᶜ B′} (coe c⊑ cwt c′wt pA pM) (injidR ⇒ᵗ pM))
  where
  pM : (★ ⇒ ★) ⊑ B′
  pM = proj₂ (⊑ᶜ→⊑ c′wt cwt c⊑)
coe {c = c} (⊑⊥ _ _ _) cwt (⊢⊥ {A = C} {B = D} {ℓ = ℓ}) pA pB =
  bot pA pB c {C} {D} {ℓ}
