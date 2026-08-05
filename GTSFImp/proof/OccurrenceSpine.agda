module proof.OccurrenceSpine where

-- File Charter:
--   * Defines endpoint spines for comparing types around inserted binders.
--   * Tracks a selected type-variable occurrence through forall/inst/gen
--     shape changes.
--   * Provides freshness and star-exclusion lemmas for spine arguments.
--   * Depends only on Types and basic occurrence inversion facts.

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans; subst)

open import Types
open import proof.ImprecisionConsistency
  using (fin-suc-injective; ext-injective; unshift-occurs)

not-occurs : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
  → X ∉ᵗ A
  → X ∈ᵗ A
  → ⊥
not-occurs (∉-var X≠Y) var-∈ = X≠Y refl
not-occurs ∉-base ()
not-occurs ∉-star ()
not-occurs (∉-fun X∉A X∉B) (∈-fun-left X∈A) =
  not-occurs X∉A X∈A
not-occurs (∉-fun X∉A X∉B) (∈-fun-right X∉A′ X∈B) =
  not-occurs X∉B X∈B
not-occurs (∉-all X∉A) (∈-all X∈A) =
  not-occurs X∉A X∈A

insertʳ : ∀ {Δ} → TyVar (Nat.suc Δ) → Δ ⇒ʳ Nat.suc Δ
insertʳ zero Y = suc Y
insertʳ {Nat.suc Δ} (suc X) zero = zero
insertʳ {Nat.suc Δ} (suc X) (suc Y) = suc (insertʳ X Y)

insertʳ-ext : ∀ {Δ} (X : TyVar (Nat.suc Δ))
  → ∀ Y → extᵗ (insertʳ X) Y ≡ insertʳ (suc X) Y
insertʳ-ext X zero = refl
insertʳ-ext X (suc Y) = refl

renameᵗ-id′ : ∀ {Δ} (A : Ty Δ) → renameᵗ (λ X → X) A ≡ A
renameᵗ-id′ (＇ X) = refl
renameᵗ-id′ (‵ ι) = refl
renameᵗ-id′ ★ = refl
renameᵗ-id′ (A ⇒ B)
    rewrite renameᵗ-id′ A | renameᵗ-id′ B =
  refl
renameᵗ-id′ (`∀ A) =
  cong `∀ (trans (renameᵗ-cong A ext-id) (renameᵗ-id′ A))
  where
  ext-id : ∀ X → extᵗ (λ Y → Y) X ≡ X
  ext-id zero = refl
  ext-id (suc X) = refl

insertʳ-fresh-var : ∀ {Δ} (X : TyVar (Nat.suc Δ))
  → ∀ Y → X ≢ insertʳ X Y
insertʳ-fresh-var zero Y ()
insertʳ-fresh-var {Nat.suc Δ} (suc X) zero ()
insertʳ-fresh-var {Nat.suc Δ} (suc X) (suc Y) eq =
  insertʳ-fresh-var X Y (fin-suc-injective eq)

insert-fresh : ∀ {Δ} (X : TyVar (Nat.suc Δ))
  → ∀ (A : Ty Δ) → X ∉ᵗ renameᵗ (insertʳ X) A
insert-fresh X (＇ Y) = ∉-var (insertʳ-fresh-var X Y)
insert-fresh X (‵ ι) = ∉-base
insert-fresh X ★ = ∉-star
insert-fresh X (A ⇒ B) =
  ∉-fun (insert-fresh X A) (insert-fresh X B)
insert-fresh X (`∀ A)
    rewrite renameᵗ-cong A (insertʳ-ext X) =
  ∉-all (insert-fresh (suc X) A)

Fresh : ∀ {Δ} → TyVar Δ → Ty Δ → Set
Fresh X A = X ∈ᵗ A → ⊥

fresh-fun-left : ∀ {Δ} {X : TyVar Δ} {A B : Ty Δ}
  → Fresh X (A ⇒ B)
  → Fresh X A
fresh-fun-left fresh occ = fresh (∈-fun-left occ)

fresh-fun-right : ∀ {Δ} {X : TyVar Δ} {A B : Ty Δ}
  → Fresh X (A ⇒ B)
  → Fresh X B
fresh-fun-right {X = X} {A = A} fresh occ with occurs? X A
fresh-fun-right fresh occ | present X∈A = fresh (∈-fun-left X∈A)
fresh-fun-right fresh occ | absent X∉A = fresh (∈-fun-right X∉A occ)

fresh-all : ∀ {Δ} {X : TyVar Δ} {A : Ty (Nat.suc Δ)}
  → Fresh X (`∀ A)
  → Fresh (suc X) A
fresh-all fresh occ = fresh (∈-all occ)

fresh-shift : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
  → Fresh X A
  → Fresh (suc X) (⇑ᵗ A)
fresh-shift fresh occ = fresh (unshift-occurs occ)

------------------------------------------------------------------------
-- Endpoint spines
------------------------------------------------------------------------

data EndpointSpine : ∀ {Δᴸ Δᴿ} → Ty Δᴸ → Ty Δᴿ → Set where
  spine-renamed : ∀ {Δ₀ Δᴸ Δᴿ} {L : Ty Δᴸ} {R : Ty Δᴿ}
      {T : Ty Δ₀} {ρ : Δ₀ ⇒ʳ Δᴸ} {τ : Δ₀ ⇒ʳ Δᴿ}
    → L ≡ renameᵗ ρ T
    → R ≡ renameᵗ τ T
    → EndpointSpine L R

  spine-left-all : ∀ {Δᴸ Δᴿ} {L : Ty (Nat.suc Δᴸ)} {R : Ty Δᴿ}
    → EndpointSpine L R
    → EndpointSpine (`∀ L) R

  spine-right-all : ∀ {Δᴸ Δᴿ} {L : Ty Δᴸ} {R : Ty (Nat.suc Δᴿ)}
    → EndpointSpine L R
    → EndpointSpine L (`∀ R)

spine-map-left : ∀ {Δᴸ Δᴸ′ Δᴿ}
    (ρ : Δᴸ ⇒ʳ Δᴸ′) {L : Ty Δᴸ} {R : Ty Δᴿ}
  → EndpointSpine L R
  → EndpointSpine (renameᵗ ρ L) R
spine-map-left ρ
    (spine-renamed {T = T} {ρ = σ} {τ = τ} refl refl) =
  spine-renamed (renameᵗ-comp σ ρ T) refl
spine-map-left ρ (spine-left-all sp) =
  spine-left-all (spine-map-left (extᵗ ρ) sp)
spine-map-left ρ (spine-right-all sp) =
  spine-right-all (spine-map-left ρ sp)

spine-map-right : ∀ {Δᴸ Δᴿ Δᴿ′}
    (ρ : Δᴿ ⇒ʳ Δᴿ′) {L : Ty Δᴸ} {R : Ty Δᴿ}
  → EndpointSpine L R
  → EndpointSpine L (renameᵗ ρ R)
spine-map-right ρ
    (spine-renamed {T = T} {ρ = σ} {τ = τ} refl refl) =
  spine-renamed refl (renameᵗ-comp τ ρ T)
spine-map-right ρ (spine-left-all sp) =
  spine-left-all (spine-map-right ρ sp)
spine-map-right ρ (spine-right-all sp) =
  spine-right-all (spine-map-right (extᵗ ρ) sp)

spine-peel-right : ∀ {Δᴸ Δᴸ′ Δᴿ}
    (ρ : Δᴸ ⇒ʳ Δᴸ′) {L : Ty Δᴸ} {R : Ty (Nat.suc Δᴿ)}
  → EndpointSpine L (`∀ R)
  → EndpointSpine (renameᵗ ρ L) R
spine-peel-right ρ (spine-renamed {T = ＇ β} eqL ())
spine-peel-right ρ (spine-renamed {T = ‵ ι} eqL ())
spine-peel-right ρ (spine-renamed {T = ★} eqL ())
spine-peel-right ρ (spine-renamed {T = T₁ ⇒ T₂} eqL ())
spine-peel-right ρ
    (spine-renamed {T = `∀ T} {ρ = σ} {τ = τ} refl refl) =
  spine-left-all
    (spine-renamed
      (renameᵗ-comp (extᵗ σ) (extᵗ ρ) T)
      refl)
spine-peel-right ρ (spine-left-all sp) =
  spine-left-all (spine-peel-right (extᵗ ρ) sp)
spine-peel-right ρ (spine-right-all sp) =
  spine-map-left ρ sp

spine-peel-left : ∀ {Δᴸ Δᴿ Δᴿ′}
    (ρ : Δᴿ ⇒ʳ Δᴿ′) {L : Ty (Nat.suc Δᴸ)} {R : Ty Δᴿ}
  → EndpointSpine (`∀ L) R
  → EndpointSpine L (renameᵗ ρ R)
spine-peel-left ρ (spine-renamed {T = ＇ β} () eqR)
spine-peel-left ρ (spine-renamed {T = ‵ ι} () eqR)
spine-peel-left ρ (spine-renamed {T = ★} () eqR)
spine-peel-left ρ (spine-renamed {T = T₁ ⇒ T₂} () eqR)
spine-peel-left ρ
    (spine-renamed {T = `∀ T} {ρ = σ} {τ = τ} refl refl) =
  spine-right-all
    (spine-renamed
      refl
      (renameᵗ-comp (extᵗ τ) (extᵗ ρ) T))
spine-peel-left ρ (spine-left-all sp) =
  spine-map-right ρ sp
spine-peel-left ρ (spine-right-all sp) =
  spine-right-all (spine-peel-left (extᵗ ρ) sp)

spine-peel-right-id : ∀ {Δᴸ Δᴿ} {L : Ty Δᴸ}
    {R : Ty (Nat.suc Δᴿ)}
  → EndpointSpine L (`∀ R)
  → EndpointSpine L R
spine-peel-right-id (spine-renamed {T = ＇ β} eqL ())
spine-peel-right-id (spine-renamed {T = ‵ ι} eqL ())
spine-peel-right-id (spine-renamed {T = ★} eqL ())
spine-peel-right-id (spine-renamed {T = T₁ ⇒ T₂} eqL ())
spine-peel-right-id
    (spine-renamed {T = `∀ T} {ρ = ρ} {τ = τ} refl refl) =
  spine-left-all (spine-renamed refl refl)
spine-peel-right-id (spine-left-all sp) =
  spine-left-all (spine-peel-right-id sp)
spine-peel-right-id (spine-right-all sp) = sp

spine-peel-left-id : ∀ {Δᴸ Δᴿ} {L : Ty (Nat.suc Δᴸ)}
    {R : Ty Δᴿ}
  → EndpointSpine (`∀ L) R
  → EndpointSpine L R
spine-peel-left-id (spine-renamed {T = ＇ β} () eqR)
spine-peel-left-id (spine-renamed {T = ‵ ι} () eqR)
spine-peel-left-id (spine-renamed {T = ★} () eqR)
spine-peel-left-id (spine-renamed {T = T₁ ⇒ T₂} () eqR)
spine-peel-left-id
    (spine-renamed {T = `∀ T} {ρ = ρ} {τ = τ} refl refl) =
  spine-right-all (spine-renamed refl refl)
spine-peel-left-id (spine-left-all sp) = sp
spine-peel-left-id (spine-right-all sp) =
  spine-right-all (spine-peel-left-id sp)

spine-strip-both : ∀ {Δᴸ Δᴿ} {L : Ty (Nat.suc Δᴸ)}
    {R : Ty (Nat.suc Δᴿ)}
  → EndpointSpine (`∀ L) (`∀ R)
  → EndpointSpine L R
spine-strip-both (spine-renamed {T = ＇ β} () eqR)
spine-strip-both (spine-renamed {T = ‵ ι} () eqR)
spine-strip-both (spine-renamed {T = ★} () eqR)
spine-strip-both (spine-renamed {T = T₁ ⇒ T₂} () eqR)
spine-strip-both
    (spine-renamed {T = `∀ T} {ρ = ρ} {τ = τ} refl refl) =
  spine-renamed refl refl
spine-strip-both (spine-left-all sp) = spine-peel-right-id sp
spine-strip-both (spine-right-all sp) = spine-peel-left-id sp

spine-fun-left : ∀ {Δᴸ Δᴿ} {A₁ A₂ : Ty Δᴸ}
    {B₁ B₂ : Ty Δᴿ}
  → EndpointSpine (A₁ ⇒ A₂) (B₁ ⇒ B₂)
  → EndpointSpine A₁ B₁
spine-fun-left
    (spine-renamed {T = T₁ ⇒ T₂} refl refl) =
  spine-renamed refl refl

spine-fun-right : ∀ {Δᴸ Δᴿ} {A₁ A₂ : Ty Δᴸ}
    {B₁ B₂ : Ty Δᴿ}
  → EndpointSpine (A₁ ⇒ A₂) (B₁ ⇒ B₂)
  → EndpointSpine A₂ B₂
spine-fun-right
    (spine-renamed {T = T₁ ⇒ T₂} refl refl) =
  spine-renamed refl refl

insert-spine : ∀ {Δ} (X : TyVar (Nat.suc Δ))
    {B : Ty (Nat.suc Δ)}
  → EndpointSpine B (renameᵗ (insertʳ X) (`∀ B))
insert-spine X {B = B} =
  spine-right-all
    (spine-renamed {T = B} {ρ = λ Y → Y} {τ = extᵗ (insertʳ X)}
      (sym (renameᵗ-id′ B)) refl)

insert-fresh-occ : ∀ {Δ} (X : TyVar (Nat.suc Δ))
    (A : Ty Δ)
  → Fresh X (renameᵗ (insertʳ X) A)
insert-fresh-occ X A = not-occurs (insert-fresh X A)

------------------------------------------------------------------------
-- Endpoint gaps generated by an inserted binder
------------------------------------------------------------------------

data EndpointGap : ∀ {Δᴸ Δᴿ} → TyVar Δᴿ → Ty Δᴸ → Ty Δᴿ → Set where
  end-insert : ∀ {Δ} {X : TyVar (Nat.suc Δ)} {B : Ty (Nat.suc Δ)}
    → EndpointGap X B (renameᵗ (insertʳ X) (`∀ B))

  end-all : ∀ {Δᴸ Δᴿ} {X : TyVar Δᴿ}
      {B : Ty (Nat.suc Δᴸ)} {C : Ty (Nat.suc Δᴿ)}
    → EndpointGap (suc X) B C
    → EndpointGap X (`∀ B) (`∀ C)

  end-shift : ∀ {Δᴸ Δᴿ} {X : TyVar Δᴿ}
      {B : Ty Δᴸ} {C : Ty Δᴿ} {B′ : Ty (Nat.suc Δᴸ)}
      {C′ : Ty (Nat.suc Δᴿ)}
    → EndpointGap X B C
    → B′ ≡ ⇑ᵗ B
    → C′ ≡ ⇑ᵗ C
    → EndpointGap (suc X) B′ C′

  end-right-inst-all : ∀ {Δᴸ Δᴿ} {X : TyVar Δᴿ}
      {B : Ty (Nat.suc Δᴸ)} {C : Ty Δᴿ} {C′ : Ty (Nat.suc Δᴿ)}
    → EndpointGap X (`∀ B) C
    → C′ ≡ ⇑ᵗ C
    → EndpointGap (suc X) B C′

  end-left-inst-all : ∀ {Δᴸ Δᴿ} {X : TyVar Δᴿ}
      {B : Ty Δᴸ} {C : Ty (Nat.suc Δᴿ)}
      {B′ : Ty (Nat.suc Δᴸ)}
    → EndpointGap X B (`∀ C)
    → B′ ≡ ⇑ᵗ B
    → EndpointGap (suc X) B′ C

  end-strip-both : ∀ {Δᴸ Δᴿ} {X : TyVar Δᴿ}
      {B : Ty (Nat.suc Δᴸ)} {C : Ty (Nat.suc Δᴿ)}
    → EndpointGap X (`∀ B) (`∀ C)
    → EndpointGap (suc X) B C

endpoint-gap-spine : ∀ {Δᴸ Δᴿ} {X : TyVar Δᴿ}
    {B : Ty Δᴸ} {C : Ty Δᴿ}
  → EndpointGap X B C
  → EndpointSpine B C
endpoint-gap-spine end-insert = insert-spine _
endpoint-gap-spine (end-all gap) =
  spine-left-all (spine-right-all (endpoint-gap-spine gap))
endpoint-gap-spine (end-shift gap refl refl) =
  spine-map-right suc (spine-map-left suc (endpoint-gap-spine gap))
endpoint-gap-spine (end-right-inst-all gap refl) =
  spine-peel-left suc (endpoint-gap-spine gap)
endpoint-gap-spine (end-left-inst-all gap refl) =
  spine-peel-right suc (endpoint-gap-spine gap)
endpoint-gap-spine (end-strip-both gap) =
  spine-strip-both (endpoint-gap-spine gap)

endpoint-gap-fresh : ∀ {Δᴸ Δᴿ} {X : TyVar Δᴿ}
    {B : Ty Δᴸ} {C : Ty Δᴿ}
  → EndpointGap X B C
  → Fresh X C
endpoint-gap-fresh end-insert = insert-fresh-occ _ _
endpoint-gap-fresh (end-all gap) (∈-all X∈C) =
  endpoint-gap-fresh gap X∈C
endpoint-gap-fresh (end-shift gap refl refl) =
  fresh-shift (endpoint-gap-fresh gap)
endpoint-gap-fresh (end-right-inst-all gap refl) =
  fresh-shift (endpoint-gap-fresh gap)
endpoint-gap-fresh (end-left-inst-all gap refl) =
  fresh-all (endpoint-gap-fresh gap)
endpoint-gap-fresh (end-strip-both gap) =
  fresh-all (endpoint-gap-fresh gap)

gap-shift : ∀ {Δᴸ Δᴿ} {X : TyVar Δᴿ}
    {B : Ty Δᴸ} {C : Ty Δᴿ}
  → EndpointGap X B C
  → EndpointGap (suc X) (⇑ᵗ B) (⇑ᵗ C)
gap-shift gap = end-shift gap refl refl

gap-peel-left-all : ∀ {Δᴸ Δᴿ} {X : TyVar Δᴿ}
    {B : Ty (Nat.suc Δᴸ)} {C : Ty Δᴿ}
  → EndpointGap X (`∀ B) C
  → EndpointGap (suc X) B (⇑ᵗ C)
gap-peel-left-all gap = end-right-inst-all gap refl

gap-peel-right-all : ∀ {Δᴸ Δᴿ} {X : TyVar Δᴿ}
    {B : Ty Δᴸ} {C : Ty (Nat.suc Δᴿ)}
  → EndpointGap X B (`∀ C)
  → EndpointGap (suc X) (⇑ᵗ B) C
gap-peel-right-all gap = end-left-inst-all gap refl

gap-strip-both : ∀ {Δᴸ Δᴿ} {X : TyVar Δᴿ}
    {B : Ty (Nat.suc Δᴸ)} {C : Ty (Nat.suc Δᴿ)}
  → EndpointGap X (`∀ B) (`∀ C)
  → EndpointGap (suc X) B C
gap-strip-both = end-strip-both

gap-fun-left : ∀ {Δ} {X : TyVar Δ}
    {A A′ B B′ : Ty Δ}
  → EndpointGap X (A ⇒ A′) (B ⇒ B′)
  → EndpointGap X A B
{-# TERMINATING #-}
gap-fun-left (end-shift {B = A₀ ⇒ A₁} {C = B₀ ⇒ B₁}
    gap refl refl) =
  gap-shift (gap-fun-left gap)
gap-fun-left (end-right-inst-all {C = B₀ ⇒ B₁} gap refl) =
  gap-fun-left (gap-peel-left-all gap)
gap-fun-left (end-left-inst-all {B = A₀ ⇒ A₁} gap refl) =
  gap-fun-left (gap-peel-right-all gap)
gap-fun-left (end-strip-both gap) =
  gap-fun-left (gap-strip-both gap)

gap-fun-right : ∀ {Δ} {X : TyVar Δ}
    {A A′ B B′ : Ty Δ}
  → EndpointGap X (A ⇒ A′) (B ⇒ B′)
  → EndpointGap X A′ B′
{-# TERMINATING #-}
gap-fun-right (end-shift {B = A₀ ⇒ A₁} {C = B₀ ⇒ B₁}
    gap refl refl) =
  gap-shift (gap-fun-right gap)
gap-fun-right (end-right-inst-all {C = B₀ ⇒ B₁} gap refl) =
  gap-fun-right (gap-peel-left-all gap)
gap-fun-right (end-left-inst-all {B = A₀ ⇒ A₁} gap refl) =
  gap-fun-right (gap-peel-right-all gap)
gap-fun-right (end-strip-both gap) =
  gap-fun-right (gap-strip-both gap)

------------------------------------------------------------------------
-- Occurrence paths
------------------------------------------------------------------------

data OccPath : ∀ {Δ} → TyVar Δ → Ty Δ → Ty Δ → Set where
  op-var : ∀ {Δ} {X : TyVar Δ}
    → OccPath X (＇ X) (＇ X)

  op-fun-left : ∀ {Δ X A A′ B B′}
    → OccPath {Δ} X A A′
    → OccPath X (A ⇒ B) (A′ ⇒ B′)

  op-fun-right : ∀ {Δ X A A′ B B′}
    → OccPath {Δ} X B B′
    → OccPath X (A ⇒ B) (A′ ⇒ B′)

  op-all : ∀ {Δ X A B}
    → OccPath {Nat.suc Δ} (suc X) A B
    → OccPath {Δ} X (`∀ A) (`∀ B)

  op-inst : ∀ {Δ X A B}
    → OccPath {Nat.suc Δ} (suc X) A (⇑ᵗ B)
    → OccPath {Δ} X (`∀ A) B

  op-gen : ∀ {Δ X A B}
    → OccPath {Nat.suc Δ} (suc X) (⇑ᵗ A) B
    → OccPath {Δ} X A (`∀ B)

path-rename : ∀ {Δ Δ′ X A B}
  → (ρ : Δ ⇒ʳ Δ′)
  → OccPath X A B
  → OccPath (ρ X) (renameᵗ ρ A) (renameᵗ ρ B)
path-rename ρ op-var = op-var
path-rename ρ (op-fun-left p) = op-fun-left (path-rename ρ p)
path-rename ρ (op-fun-right p) = op-fun-right (path-rename ρ p)
path-rename ρ (op-all p) = op-all (path-rename (extᵗ ρ) p)
path-rename ρ (op-inst {B = B} p) =
  op-inst
    (subst (λ T → OccPath _ _ T) (renameᵗ-shift ρ B)
      (path-rename (extᵗ ρ) p))
path-rename ρ (op-gen {A = A} p) =
  op-gen
    (subst (λ T → OccPath _ T _) (renameᵗ-shift ρ A)
      (path-rename (extᵗ ρ) p))

path-shift : ∀ {Δ X A B}
  → OccPath {Δ} X A B
  → OccPath (suc X) (⇑ᵗ A) (⇑ᵗ B)
path-shift = path-rename suc

path-source-occurs : ∀ {Δ} {X : TyVar Δ} {A B : Ty Δ}
  → OccPath X A B
  → X ∈ᵗ A
path-target-occurs : ∀ {Δ} {X : TyVar Δ} {A B : Ty Δ}
  → OccPath X A B
  → X ∈ᵗ B

path-source-occurs op-var = var-∈
path-source-occurs (op-fun-left p) =
  ∈-fun-left (path-source-occurs p)
path-source-occurs {X = X} {A = A ⇒ B} (op-fun-right p)
    with occurs? X A
path-source-occurs {A = A ⇒ B} (op-fun-right p) | present X∈A =
  ∈-fun-left X∈A
path-source-occurs {A = A ⇒ B} (op-fun-right p) | absent X∉A =
  ∈-fun-right X∉A (path-source-occurs p)
path-source-occurs (op-all p) =
  ∈-all (path-source-occurs p)
path-source-occurs (op-inst p) =
  ∈-all (path-source-occurs p)
path-source-occurs (op-gen p) =
  unshift-occurs (path-source-occurs p)

path-target-occurs op-var = var-∈
path-target-occurs (op-fun-left p) =
  ∈-fun-left (path-target-occurs p)
path-target-occurs {X = X} {B = A ⇒ B} (op-fun-right p)
    with occurs? X A
path-target-occurs {B = A ⇒ B} (op-fun-right p) | present X∈A =
  ∈-fun-left X∈A
path-target-occurs {B = A ⇒ B} (op-fun-right p) | absent X∉A =
  ∈-fun-right X∉A (path-target-occurs p)
path-target-occurs (op-all p) =
  ∈-all (path-target-occurs p)
path-target-occurs (op-inst p) =
  unshift-occurs (path-target-occurs p)
path-target-occurs (op-gen p) =
  ∈-all (path-target-occurs p)

path-left-star-spine⊥ : ∀ {Δ Δ★} {X : TyVar Δ}
    {A B : Ty Δ}
  → OccPath X A B
  → EndpointSpine A (★ {Δ★})
  → ⊥
path-left-star-spine⊥ op-var
    (spine-renamed {T = ＇ β} refl ())
path-left-star-spine⊥ (op-fun-left p)
    (spine-renamed {T = T₁ ⇒ T₂} refl ())
path-left-star-spine⊥ (op-fun-right p)
    (spine-renamed {T = T₁ ⇒ T₂} refl ())
path-left-star-spine⊥ (op-all p) (spine-left-all sp) =
  path-left-star-spine⊥ p sp
path-left-star-spine⊥ (op-all p)
    (spine-renamed {T = `∀ T} refl ())
path-left-star-spine⊥ (op-inst p) (spine-left-all sp) =
  path-left-star-spine⊥ p sp
path-left-star-spine⊥ (op-inst p)
    (spine-renamed {T = `∀ T} refl ())
path-left-star-spine⊥ (op-gen p) sp =
  path-left-star-spine⊥ p (spine-map-left suc sp)

path-right-star-spine⊥ : ∀ {Δ Δ★} {X : TyVar Δ}
    {A B : Ty Δ}
  → OccPath X A B
  → EndpointSpine B (★ {Δ★})
  → ⊥
path-right-star-spine⊥ op-var
    (spine-renamed {T = ＇ β} refl ())
path-right-star-spine⊥ (op-fun-left p)
    (spine-renamed {T = T₁ ⇒ T₂} refl ())
path-right-star-spine⊥ (op-fun-right p)
    (spine-renamed {T = T₁ ⇒ T₂} refl ())
path-right-star-spine⊥ (op-all p) (spine-left-all sp) =
  path-right-star-spine⊥ p sp
path-right-star-spine⊥ (op-all p)
    (spine-renamed {T = `∀ T} refl ())
path-right-star-spine⊥ (op-inst p) sp =
  path-right-star-spine⊥ p (spine-map-left suc sp)
path-right-star-spine⊥ (op-gen p) (spine-left-all sp) =
  path-right-star-spine⊥ p sp
path-right-star-spine⊥ (op-gen p)
    (spine-renamed {T = `∀ T} refl ())

occurs-left-star-spine⊥ : ∀ {Δ Δ★} {X : TyVar Δ}
    {A : Ty Δ}
  → X ∈ᵗ A
  → EndpointSpine A (★ {Δ★})
  → ⊥
occurs-left-star-spine⊥ var-∈
    (spine-renamed {T = ＇ β} refl ())
occurs-left-star-spine⊥ (∈-fun-left X∈A)
    (spine-renamed {T = T₁ ⇒ T₂} refl ())
occurs-left-star-spine⊥ (∈-fun-right X∉A X∈B)
    (spine-renamed {T = T₁ ⇒ T₂} refl ())
occurs-left-star-spine⊥ (∈-all X∈A) (spine-left-all sp) =
  occurs-left-star-spine⊥ X∈A sp
occurs-left-star-spine⊥ (∈-all X∈A)
    (spine-renamed {T = `∀ T} refl ())
