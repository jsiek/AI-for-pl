module proof.LR.GroundAgree where

-- File Charter:
--   * Ground agreement (notes/logrel-dgg.md, "Ground agreement"): the
--     ground at which a right cast injects is determined by the left
--     type, through the *shape* of a type: a base type, a variable, a
--     function, a `∀` whose ground is `∀★` (its variable dead, or
--     `∀X.X`), or `★`.  A `∀` whose variable occurs has its body's
--     shape.
--   * A cast between types other than `★` keeps the shape
--     (`shape-cast`): it needs only that a variable of mode `X∼X`
--     occurs in a cast's target exactly when it occurs in its source
--     (`occ→`, `occ←`), for the binder of `∀ᶜ`.
--   * A precision whose right type is not `★` relates the shapes of its
--     two types (`shape-prec`).
--   * So two casts from related types (C ⊑ C′, the right one not from
--     `★`) reach related shapes (`groundAgree`).  Consequences:
--       - two grounds reached that way are related by precision
--         (`ground⊑`; the row `!` against `!`);
--       - a left type B ⊑ ★ predicts the ground of the right's
--         injection (`injOf-fun`, `injOf-all`; the conjunct of the
--         `∀⊑`-into-`★` clause, F1);
--       - at a function ground, B ⊑ ★→★ (`⊑★⇒★`; the row `inst`
--         against `(inst)!`).

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Nat using () renaming (suc to sucℕ)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Types
open import Consistency
open import CastTerms using (Term)
open import LR.Precision
open import LR.Relation using (injOf; injFun; injAll)
open import proof.ImprecisionConsistency using (rename-occurs;
  unrename-occurs; ext-injective; fin-suc-injective; shift-occurs;
  unshift-occurs)
open import proof.LR.ConvBase using (↔-only-⊥)

private
  variable
    Δ Δ′ : TyCtx

------------------------------------------------------------------------
-- Occurrences
------------------------------------------------------------------------

∈∉ : ∀ {X : TyVar Δ} {A} → X ∈ᵗ A → X ∉ᵗ A → ⊥
∈∉ var-∈ (∉-var ne) = ≢ᶠ→≢ ne refl
∈∉ (∈-fun-left i) (∉-fun n m) = ∈∉ i n
∈∉ (∈-fun-right n′ i) (∉-fun n m) = ∈∉ i m
∈∉ (∈-all i) (∉-all n) = ∈∉ i n

-- an occurrence in a function's codomain
∈⇒R : ∀ {X : TyVar Δ} {A B} → X ∈ᵗ B → X ∈ᵗ A ⇒ B
∈⇒R {X = X} {A} i with occurs? X A
∈⇒R {X = X} {A} i | present j = ∈-fun-left j
∈⇒R {X = X} {A} i | absent n = ∈-fun-right n i

-- a variable of mode `X∼X` is not projected from or injected into `★`
noTo★ : ∀ {μ : Env∼ Δ} {G} {X} → Ground G → μ ⊢ G ∼★ → μ ‼ X ≡ X∼X
  → X ∈ᵗ G → ⊥
noTo★ (＇ Y) (X∼★ᵍ e) eq var-∈ with trans (sym eq) e
noTo★ (＇ Y) (X∼★ᵍ e) eq var-∈ | ()
noTo★ (＇ Y) (X∼★ᶜ e) eq var-∈ with trans (sym eq) e
noTo★ (＇ Y) (X∼★ᶜ e) eq var-∈ | ()
noTo★ ★⇒★ s eq (∈-fun-left ())
noTo★ ★⇒★ s eq (∈-fun-right n ())
noTo★ ∀★ s eq (∈-all ())

noFrom★ : ∀ {μ : Env∼ Δ} {G} {X} → Ground G → μ ⊢★∼ G → μ ‼ X ≡ X∼X
  → X ∈ᵗ G → ⊥
noFrom★ (＇ Y) (★∼Xᵍ e) eq var-∈ with trans (sym eq) e
noFrom★ (＇ Y) (★∼Xᵍ e) eq var-∈ | ()
noFrom★ (＇ Y) (★∼Xᶜ e) eq var-∈ with trans (sym eq) e
noFrom★ (＇ Y) (★∼Xᶜ e) eq var-∈ | ()
noFrom★ ★⇒★ s eq (∈-fun-left ())
noFrom★ ★⇒★ s eq (∈-fun-right n ())
noFrom★ ∀★ s eq (∈-all ())

flip-XX : ∀ (μ : Env∼ Δ) X → μ ‼ X ≡ X∼X → flipᵐ μ ‼ X ≡ X∼X
flip-XX μ X eq = trans (flipᵐ-‼ μ X) (cong flipVar∼ eq)

-- a variable of mode `X∼X` occurs in a cast's target exactly when it
-- occurs in its source
mutual
  occ→ : ∀ {μ : Env∼ Δ} {A B} → μ ⊢ A ∼ B → ∀ {X} → μ ‼ X ≡ X∼X
    → X ∈ᵗ A → X ∈ᵗ B
  occ→ (id a) eq i = i
  occ→ {μ = μ} (c ↦ d) {X} eq (∈-fun-left i) =
    ∈-fun-left (occ← c (flip-XX μ X eq) i)
  occ→ (c ↦ d) eq (∈-fun-right n i) = ∈⇒R (occ→ d eq i)
  occ→ (∀ᶜ c) eq (∈-all i) = ∈-all (occ→ c eq i)
  occ→ (_! ⦃ Gᵍ = g ⦄ ⦃ G∼★ = s ⦄ c) eq i = ⊥-elim (noTo★ g s eq (occ→ c eq i))
  occ→ (？ c) eq ()
  occ→ ((inst c) n) eq (∈-all i) = unshift-occurs (occ→ c eq i)
  occ→ ((gen c) n) eq i = ∈-all (occ→ c eq (shift-occurs i))
  occ→ bot-elim eq (∈-all ())
  occ→ bot-intro eq (∈-all ())

  occ← : ∀ {μ : Env∼ Δ} {A B} → μ ⊢ A ∼ B → ∀ {X} → μ ‼ X ≡ X∼X
    → X ∈ᵗ B → X ∈ᵗ A
  occ← (id a) eq i = i
  occ← {μ = μ} (c ↦ d) {X} eq (∈-fun-left i) =
    ∈-fun-left (occ→ c (flip-XX μ X eq) i)
  occ← (c ↦ d) eq (∈-fun-right n i) = ∈⇒R (occ← d eq i)
  occ← (∀ᶜ c) eq (∈-all i) = ∈-all (occ← c eq i)
  occ← (c !) eq ()
  occ← (？_ ⦃ Gᵍ = g ⦄ ⦃ ★∼G = s ⦄ c) eq i =
    ⊥-elim (noFrom★ g s eq (occ← c eq i))
  occ← ((inst c) n) eq i = ∈-all (occ← c eq (shift-occurs i))
  occ← ((gen c) n) eq (∈-all i) = unshift-occurs (occ← c eq i)
  occ← bot-elim eq (∈-all ())
  occ← bot-intro eq (∈-all ())

------------------------------------------------------------------------
-- Shapes
------------------------------------------------------------------------

data Shape (Δ : TyCtx) : Set where
  sb : Base → Shape Δ
  sv : TyVar Δ → Shape Δ
  sf sa sn : Shape Δ

-- a `∀`'s shape from its body's, when the bound variable occurs
down : Shape (sucℕ Δ) → Shape Δ
down (sb ι) = sb ι
down (sv zero) = sa
down (sv (suc X)) = sv X
down sf = sf
down sa = sa
down sn = sn

renS : (Δ ⇒ʳ Δ′) → Shape Δ → Shape Δ′
renS ρ (sb ι) = sb ι
renS ρ (sv X) = sv (ρ X)
renS ρ sf = sf
renS ρ sa = sa
renS ρ sn = sn

mutual
  shapeOf : Ty Δ → Shape Δ
  shapeOf (＇ X) = sv X
  shapeOf (‵ ι) = sb ι
  shapeOf ★ = sn
  shapeOf (A ⇒ B) = sf
  shapeOf (`∀ A) = shape∀ A (occurs? zero A)

  shape∀ : (A : Ty (sucℕ Δ)) → Occurs? zero A → Shape Δ
  shape∀ A (present i) = down (shapeOf A)
  shape∀ A (absent n) = sa

shape-in : ∀ {A : Ty (sucℕ Δ)} → zero ∈ᵗ A
  → shapeOf (`∀ A) ≡ down (shapeOf A)
shape-in {A = A} i with occurs? zero A
shape-in {A = A} i | present j = refl
shape-in {A = A} i | absent n = ⊥-elim (∈∉ i n)

down-ren : ∀ (ρ : Δ ⇒ʳ Δ′) s → down (renS (extᵗ ρ) s) ≡ renS ρ (down s)
down-ren ρ (sb ι) = refl
down-ren ρ (sv zero) = refl
down-ren ρ (sv (suc X)) = refl
down-ren ρ sf = refl
down-ren ρ sa = refl
down-ren ρ sn = refl

down-up : ∀ (s : Shape Δ) → down (renS suc s) ≡ s
down-up (sb ι) = refl
down-up (sv X) = refl
down-up sf = refl
down-up sa = refl
down-up sn = refl

-- shapes under an injective renaming
shape-ren : ∀ (ρ : Δ ⇒ʳ Δ′) → (∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y) → ∀ A
  → shapeOf (renameᵗ ρ A) ≡ renS ρ (shapeOf A)
shape-ren ρ inj (＇ X) = refl
shape-ren ρ inj (‵ ι) = refl
shape-ren ρ inj ★ = refl
shape-ren ρ inj (A ⇒ B) = refl
shape-ren ρ inj (`∀ A) with occurs? zero A
shape-ren ρ inj (`∀ A) | present i =
  trans (shape-in (rename-occurs (extᵗ ρ) (ext-injective inj) i))
    (trans (cong down (shape-ren (extᵗ ρ) (ext-injective inj) A))
      (down-ren ρ (shapeOf A)))
shape-ren ρ inj (`∀ A) | absent n
    with occurs? zero (renameᵗ (extᵗ ρ) A)
shape-ren ρ inj (`∀ A) | absent n | present j =
  ⊥-elim (∈∉ (unrename-occurs (extᵗ ρ) (ext-injective inj) j) n)
shape-ren ρ inj (`∀ A) | absent n | absent m = refl

shape-⇑ : ∀ (A : Ty Δ) → down (shapeOf (⇑ᵗ A)) ≡ shapeOf A
shape-⇑ A =
  trans (cong down (shape-ren suc fin-suc-injective A)) (down-up (shapeOf A))

------------------------------------------------------------------------
-- Casts keep the shape
------------------------------------------------------------------------

ren≢★ : ∀ (ρ : Δ ⇒ʳ Δ′) {A} → A ≢ ★ → renameᵗ ρ A ≢ ★
ren≢★ ρ {＇ X} ne ()
ren≢★ ρ {‵ ι} ne ()
ren≢★ ρ {★} ne eq = ne refl
ren≢★ ρ {A ⇒ B} ne ()
ren≢★ ρ {`∀ A} ne ()

∈≢★ : ∀ {X : TyVar Δ} {A} → X ∈ᵗ A → A ≢ ★
∈≢★ i refl with i
∈≢★ i refl | ()

shape-cast : ∀ {μ : Env∼ Δ} {A B} → μ ⊢ A ∼ B → A ≢ ★ → B ≢ ★
  → shapeOf A ≡ shapeOf B
shape-cast (id a) na nb = refl
shape-cast (c ↦ d) na nb = refl
shape-cast {A = `∀ A} {`∀ B} (∀ᶜ c) na nb with occurs? zero A
shape-cast {A = `∀ A} {`∀ B} (∀ᶜ c) na nb | present i =
  trans (cong down (shape-cast c (∈≢★ i) (∈≢★ j))) (sym (shape-in j))
  where j = occ→ c refl i
shape-cast {A = `∀ A} {`∀ B} (∀ᶜ c) na nb | absent n
    with occurs? zero B
shape-cast {A = `∀ A} {`∀ B} (∀ᶜ c) na nb | absent n | present j =
  ⊥-elim (∈∉ (occ← c refl j) n)
shape-cast {A = `∀ A} {`∀ B} (∀ᶜ c) na nb | absent n | absent m =
  refl
shape-cast (c !) na nb = ⊥-elim (nb refl)
shape-cast (？ c) na nb = ⊥-elim (na refl)
shape-cast {B = B} ((inst_ ⦃ z∈A = z ⦄ c) n) na nb =
  trans (shape-in z)
    (trans (cong down (shape-cast c (∈≢★ z) (ren≢★ suc n))) (shape-⇑ B))
shape-cast {A = A} ((gen_ ⦃ z∈B = z ⦄ c) n) na nb =
  trans (sym (shape-⇑ A))
    (trans (cong down (shape-cast c (ren≢★ suc n) (∈≢★ z)))
      (sym (shape-in z)))
shape-cast bot-elim na nb = refl
shape-cast bot-intro na nb = refl

------------------------------------------------------------------------
-- Precision relates the shapes
------------------------------------------------------------------------

data ShapeRel {Δ Δ′} (Φ : Corr Δ Δ′) : Shape Δ → Shape Δ′ → Set where
  rb : ∀ {ι} → ShapeRel Φ (sb ι) (sb ι)
  rv : ∀ {X Y} → Φ ∋ X ↔ Y → ShapeRel Φ (sv X) (sv Y)
  rf : ShapeRel Φ sf sf
  ra : ShapeRel Φ sa sa

-- a variable below `★` is left-only
only★ : ∀ {Φ : Corr Δ Δ′} {A X} → Φ ⊢ A ⊑ ★ → X ∈ᵗ A → Φ ∋ X only
only★ ★⊑★ ()
only★ (⇒⊑★ p q) (∈-fun-left i) = only★ p i
only★ (⇒⊑★ p q) (∈-fun-right n i) = only★ q i
only★ ι⊑★ ()
only★ (X⊑★ o) var-∈ = o
only★ (∀⊑ a z p) (∈-all i) with only★ p i
only★ (∀⊑ a z p) (∈-all i) | only-only o = o
only★ ∀★⊑★ (∈-all ())
only★ (∀⊑★ ns p) (∈-all i) with only★ p i
only★ (∀⊑★ ns p) (∈-all i) | only-dead o = o
only★ bot⊑★ (∈-all ())

↔-fun : ∀ {Φ : Corr Δ Δ′} {X Y Y′} → Φ ∋ X ↔ Y → Φ ∋ X ↔ Y′ → Y ≡ Y′
↔-fun ↔-here ↔-here = refl
↔-fun (↔-pair x) (↔-pair y) = cong suc (↔-fun x y)
↔-fun (↔-only x) (↔-only y) = ↔-fun x y
↔-fun (↔-dead x) (↔-dead y) = ↔-fun x y

↔-inj : ∀ {Φ : Corr Δ Δ′} {X X′ Y} → Φ ∋ X ↔ Y → Φ ∋ X′ ↔ Y → X ≡ X′
↔-inj ↔-here ↔-here = refl
↔-inj (↔-pair x) (↔-pair y) = cong suc (↔-inj x y)
↔-inj (↔-only x) (↔-only y) = cong suc (↔-inj x y)
↔-inj (↔-dead x) (↔-dead y) = cong suc (↔-inj x y)

-- a paired variable occurs on the left exactly when its partner occurs
-- on the right
mutual
  pair→ : ∀ {Φ : Corr Δ Δ′} {A B X Y} → Φ ⊢ A ⊑ B → Φ ∋ X ↔ Y
    → X ∈ᵗ A → Y ∈ᵗ B
  pair→ ★⊑★ x ()
  pair→ ι⊑ι x ()
  pair→ (X⊑Y x′) x var-∈ rewrite ↔-fun x x′ = var-∈
  pair→ (⇒⊑⇒ p q) x (∈-fun-left i) = ∈-fun-left (pair→ p x i)
  pair→ (⇒⊑⇒ p q) x (∈-fun-right n i) = ∈⇒R (pair→ q x i)
  pair→ (∀⊑∀ p) x (∈-all i) = ∈-all (pair→ p (↔-pair x) i)
  pair→ r@(⇒⊑★ p q) x i = ⊥-elim (↔-only-⊥ x (only★ r i))
  pair→ ι⊑★ x ()
  pair→ (X⊑★ o) x var-∈ = ⊥-elim (↔-only-⊥ x o)
  pair→ (∀⊑ a z p) x (∈-all i) = pair→ p (↔-only x) i
  pair→ ∀★⊑★ x (∈-all ())
  pair→ r@(∀⊑★ ns p) x i = ⊥-elim (↔-only-⊥ x (only★ r i))
  pair→ bot-elim x (∈-all ())
  pair→ bot⊑★ x (∈-all ())

  pair← : ∀ {Φ : Corr Δ Δ′} {A B X Y} → Φ ⊢ A ⊑ B → Φ ∋ X ↔ Y
    → Y ∈ᵗ B → X ∈ᵗ A
  pair← ★⊑★ x ()
  pair← ι⊑ι x ()
  pair← (X⊑Y x′) x var-∈ rewrite ↔-inj x x′ = var-∈
  pair← (⇒⊑⇒ p q) x (∈-fun-left i) = ∈-fun-left (pair← p x i)
  pair← (⇒⊑⇒ p q) x (∈-fun-right n i) = ∈⇒R (pair← q x i)
  pair← (∀⊑∀ p) x (∈-all i) = ∈-all (pair← p (↔-pair x) i)
  pair← (⇒⊑★ p q) x ()
  pair← ι⊑★ x ()
  pair← (X⊑★ o) x ()
  pair← (∀⊑ a z p) x i = ∈-all (pair← p (↔-only x) i)
  pair← ∀★⊑★ x ()
  pair← (∀⊑★ ns p) x ()
  pair← bot-elim x (∈-all ())
  pair← bot⊑★ x ()

downP : ∀ {Φ : Corr Δ Δ′} {s s′} → ShapeRel (pair Φ) s s′
  → ShapeRel Φ (down s) (down s′)
downP rb = rb
downP (rv ↔-here) = ra
downP (rv (↔-pair x)) = rv x
downP rf = rf
downP ra = ra

downO : ∀ {Φ : Corr Δ Δ′} {s s′} → ShapeRel (only Φ) s s′
  → ShapeRel Φ (down s) s′
downO rb = rb
downO (rv (↔-only x)) = rv x
downO rf = rf
downO ra = ra

shape-prec : ∀ {Φ : Corr Δ Δ′} {C C′} → Φ ⊢ C ⊑ C′ → C′ ≢ ★
  → ShapeRel Φ (shapeOf C) (shapeOf C′)
shape-prec ★⊑★ ne = ⊥-elim (ne refl)
shape-prec ι⊑ι ne = rb
shape-prec (X⊑Y x) ne = rv x
shape-prec (⇒⊑⇒ p q) ne = rf
shape-prec {C = `∀ A} {`∀ B} (∀⊑∀ p) ne with occurs? zero A
shape-prec {C = `∀ A} {`∀ B} (∀⊑∀ p) ne | present i =
  subst (ShapeRel _ (down (shapeOf A))) (sym (shape-in j))
    (downP (shape-prec p (∈≢★ j)))
  where j = pair→ p ↔-here i
shape-prec {C = `∀ A} {`∀ B} (∀⊑∀ p) ne | absent n with occurs? zero B
shape-prec {C = `∀ A} {`∀ B} (∀⊑∀ p) ne | absent n | present j =
  ⊥-elim (∈∉ (pair← p ↔-here j) n)
shape-prec {C = `∀ A} {`∀ B} (∀⊑∀ p) ne | absent n | absent m = ra
shape-prec (⇒⊑★ p q) ne = ⊥-elim (ne refl)
shape-prec ι⊑★ ne = ⊥-elim (ne refl)
shape-prec (X⊑★ o) ne = ⊥-elim (ne refl)
shape-prec {C = `∀ A} {C′} (∀⊑ a z p) ne =
  subst (λ s → ShapeRel _ s (shapeOf C′)) (sym (shape-in z))
    (downO (shape-prec p ne))
shape-prec ∀★⊑★ ne = ⊥-elim (ne refl)
shape-prec (∀⊑★ ns p) ne = ⊥-elim (ne refl)
shape-prec bot-elim ne = ra
shape-prec bot⊑★ ne = ⊥-elim (ne refl)

------------------------------------------------------------------------
-- Ground agreement
------------------------------------------------------------------------

⊑≢★ : ∀ {Φ : Corr Δ Δ′} {C C′} → Φ ⊢ C ⊑ C′ → C′ ≢ ★ → C ≢ ★
⊑≢★ ★⊑★ ne refl = ne refl

-- Casts from related types, the right one not from `★` and neither into
-- `★`, reach related shapes.
groundAgree : ∀ {Φ : Corr Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′}
    {C B : Ty Δ} {C′ B′ : Ty Δ′}
  → Φ ⊢ C ⊑ C′ → C′ ≢ ★
  → ν ⊢ C ∼ B → B ≢ ★ → ν′ ⊢ C′ ∼ B′ → B′ ≢ ★
  → ShapeRel Φ (shapeOf B) (shapeOf B′)
groundAgree p ne c nb c′ nb′ =
  subst (λ s → ShapeRel _ s _) (shape-cast c (⊑≢★ p ne) nb)
    (subst (ShapeRel _ _) (shape-cast c′ ne nb′) (shape-prec p ne))

-- two grounds with related shapes are related by precision
ground⊑ : ∀ {Φ : Corr Δ Δ′} {G G′} → Ground G → Ground G′
  → ShapeRel Φ (shapeOf G) (shapeOf G′) → Φ ⊢ G ⊑ G′
ground⊑ (＇ X) (＇ Y) (rv x) = X⊑Y x
ground⊑ (‵ ι) (‵ .ι) rb = ι⊑ι
ground⊑ ★⇒★ ★⇒★ rf = ⇒⊑⇒ ★⊑★ ★⊑★
ground⊑ ∀★ ∀★ ra = ∀⊑∀ ★⊑★
ground⊑ (＇ X) (‵ ι) ()
ground⊑ (＇ X) ★⇒★ ()
ground⊑ (＇ X) ∀★ ()
ground⊑ (‵ ι) (＇ Y) ()
ground⊑ (‵ ι) ★⇒★ ()
ground⊑ (‵ ι) ∀★ ()
ground⊑ ★⇒★ (＇ Y) ()
ground⊑ ★⇒★ (‵ ι) ()
ground⊑ ★⇒★ ∀★ ()
ground⊑ ∀★ (＇ Y) ()
ground⊑ ∀★ (‵ ι) ()
ground⊑ ∀★ ★⇒★ ()

------------------------------------------------------------------------
-- The ground a left type below `★` predicts
------------------------------------------------------------------------

down≡sf : ∀ (s : Shape (sucℕ Δ)) → down s ≡ sf → s ≡ sf
down≡sf (sb ι) ()
down≡sf (sv zero) ()
down≡sf (sv (suc X)) ()
down≡sf sf refl = refl
down≡sf sa ()
down≡sf sn ()

down≡sa : ∀ (s : Shape (sucℕ Δ)) → down s ≡ sa → s ≢ sv zero → s ≡ sa
down≡sa (sb ι) () ne
down≡sa (sv zero) refl ne = ⊥-elim (ne refl)
down≡sa (sv (suc X)) () ne
down≡sa sf () ne
down≡sa sa refl ne = refl
down≡sa sn () ne

down-sv : ∀ (s : Shape (sucℕ Δ)) {X} → down s ≡ sv X → s ≡ sv (suc X)
down-sv (sb ι) ()
down-sv (sv zero) ()
down-sv (sv (suc Y)) refl = refl
down-sv sf ()
down-sv sa ()
down-sv sn ()

noZero : ∀ {X : TyVar Δ} → zero ∈ᵗ ＇ (suc X) → ⊥
noZero ()

-- only a variable has a variable shape
shape-sv : ∀ (A : Ty Δ) {X} → shapeOf A ≡ sv X → A ≡ ＇ X
shape-sv (＇ Y) refl = refl
shape-sv (‵ ι) ()
shape-sv ★ ()
shape-sv (A ⇒ B) ()
shape-sv (`∀ A) eq with occurs? zero A
shape-sv (`∀ A) eq | present i with shape-sv A (down-sv (shapeOf A) eq)
shape-sv (`∀ A) eq | present i | refl = ⊥-elim (noZero i)
shape-sv (`∀ A) () | absent n

nv-sv : ∀ {A : Ty Δ} {X} → NonVar A → shapeOf A ≢ sv X
nv-sv {A = A} nv eq with shape-sv A eq
nv-sv {A = .(＇ _)} () eq | refl

-- the body of a `∀` over a dead variable does not mention it
deadShape : ∀ {Φ : Corr Δ Δ′} {A} → dead Φ ⊢ A ⊑ ★ → shapeOf (`∀ A) ≡ sa
deadShape {A = A} p with occurs? zero A
deadShape {A = A} p | present i with only★ p i
deadShape {A = A} p | present i | ()
deadShape {A = A} p | absent n = refl

-- F1: a left type below `★` of function shape predicts an injection at
-- `★ → ★`, and of `∀★` shape one at `∀★`
injOf-sf : ∀ {Φ : Corr Δ Δ′} {B} (r : Φ ⊢ B ⊑ ★) → shapeOf B ≡ sf
  → ∀ {Θ} {V : Term Θ} → injFun V → injOf r V
injOf-sf ★⊑★ () i
injOf-sf (⇒⊑★ p q) eq i = i
injOf-sf ι⊑★ () i
injOf-sf (X⊑★ o) () i
injOf-sf {B = `∀ A} (∀⊑ a z p) eq {V = V} i =
  injOf-sf p (down≡sf (shapeOf A) (trans (sym (shape-in z)) eq)) {V = V} i
injOf-sf ∀★⊑★ () i
injOf-sf (∀⊑★ ns p) eq i with trans (sym (deadShape p)) eq
injOf-sf (∀⊑★ ns p) eq i | ()
injOf-sf bot⊑★ () i

injOf-sa : ∀ {Φ : Corr Δ Δ′} {B} (r : Φ ⊢ B ⊑ ★) → shapeOf B ≡ sa
  → ∀ {Θ} {V : Term Θ} → injAll V → injOf r V
injOf-sa ★⊑★ () i
injOf-sa (⇒⊑★ p q) () i
injOf-sa ι⊑★ () i
injOf-sa (X⊑★ o) () i
injOf-sa {B = `∀ A} (∀⊑ a z p) eq {V = V} i =
  injOf-sa p
    (down≡sa (shapeOf A) (trans (sym (shape-in z)) eq) (nv-sv a)) {V = V} i
injOf-sa ∀★⊑★ eq i = i
injOf-sa (∀⊑★ ns p) eq i = i
injOf-sa bot⊑★ eq i = tt

-- at a right ground `★ → ★` or `∀★` reached as in `groundAgree`
injOf-fun : ∀ {Φ : Corr Δ Δ′} {B} (r : Φ ⊢ B ⊑ ★)
  → ShapeRel Φ (shapeOf B) (shapeOf {Δ′} (★ ⇒ ★))
  → ∀ {Θ} {V : Term Θ} → injFun V → injOf r V
injOf-fun {B = B} r h with shapeOf B in eq
injOf-fun {B = B} r rf | sf = injOf-sf r eq

injOf-all : ∀ {Φ : Corr Δ Δ′} {B} (r : Φ ⊢ B ⊑ ★)
  → ShapeRel Φ (shapeOf B) (shapeOf {Δ′} (`∀ ★))
  → ∀ {Θ} {V : Term Θ} → injAll V → injOf r V
injOf-all {B = B} r h with shapeOf B in eq
injOf-all {B = B} r ra | sa = injOf-sa r eq

-- a left type below `★` of function shape is below `★ → ★`
⊑★⇒★ : ∀ {Φ : Corr Δ Δ′} {B} → Φ ⊢ B ⊑ ★ → shapeOf B ≡ sf
  → Φ ⊢ B ⊑ ★ ⇒ ★
⊑★⇒★ ★⊑★ ()
⊑★⇒★ (⇒⊑★ p q) eq = ⇒⊑⇒ p q
⊑★⇒★ ι⊑★ ()
⊑★⇒★ (X⊑★ o) ()
⊑★⇒★ {B = `∀ A} (∀⊑ a z p) eq =
  ∀⊑ a z (⊑★⇒★ p (down≡sf (shapeOf A) (trans (sym (shape-in z)) eq)))
⊑★⇒★ ∀★⊑★ ()
⊑★⇒★ (∀⊑★ ns p) eq with trans (sym (deadShape p)) eq
⊑★⇒★ (∀⊑★ ns p) eq | ()
⊑★⇒★ bot⊑★ ()
