module proof.Imprecision where

-- File Charter:
--   * Proves that every closed type is less precise than the dynamic type.
--   * Uses occurrence information to choose between structural universal
--     imprecision and instantiation at the dynamic type.
--   * Proves uniqueness for occurrence and type-imprecision evidence.
--   * Depends only on Types and Imprecision.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)

open import Types
open import FunExt using (funext)
import Imprecision as I

private

  ¬-unique : ∀ {A : Set} (p q : A → ⊥) → p ≡ q
  ¬-unique p q = funext (λ x → ⊥-elim (p x))

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
  not-occurs (∉-all X∉A) (∈-all X∈A) = not-occurs X∉A X∈A

  varImp-disjoint : ∀ {v : I.VarImp}
    → v ≡ I.X⊑X
    → v ≡ I.X⊑★
    → ⊥
  varImp-disjoint refl ()

  occurs-not-star : ∀ {Δ} {μ : I.ImpEnv Δ} {X : TyVar Δ} {A : Ty Δ}
    → μ X ≡ I.X⊑X
    → X ∈ᵗ A
    → I._⊢_⊑_ μ A ★
    → ⊥
  occurs-not-star same () I.★⊑★
  occurs-not-star same () I.ι⊑★
  occurs-not-star same var-∈ (I.X⊑★ to-star) =
    varImp-disjoint same to-star
  occurs-not-star same (∈-fun-left X∈A) (I.⇒⊑★ A⊑★ B⊑★) =
    occurs-not-star same X∈A A⊑★
  occurs-not-star same (∈-fun-right X∉A X∈B) (I.⇒⊑★ A⊑★ B⊑★) =
    occurs-not-star same X∈B B⊑★
  occurs-not-star same (∈-all X∈A) (I.∀⊑ Anv zero∈A A⊑★) =
    occurs-not-star same X∈A A⊑★
  occurs-not-star same (∈-all ()) I.∀★⊑★
  occurs-not-star same (∈-all X∈A) (I.∀⊑★ Ans A⊑★) =
    occurs-not-star same X∈A A⊑★
  occurs-not-star same (∈-all ()) I.bot⊑★

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

  suc-injectiveᶠ : ∀ {Δ} {X Y : TyVar Δ}
    → suc X ≡ suc Y
    → X ≡ Y
  suc-injectiveᶠ refl = refl

  ext-injective : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {X Y}
    → (∀ {Z W} → ρ Z ≡ ρ W → Z ≡ W)
    → extᵗ ρ X ≡ extᵗ ρ Y
    → X ≡ Y
  ext-injective {X = zero} {Y = zero} inj eq = refl
  ext-injective {X = zero} {Y = suc Y} inj ()
  ext-injective {X = suc X} {Y = zero} inj ()
  ext-injective {X = suc X} {Y = suc Y} inj eq =
    cong suc (inj (suc-injectiveᶠ eq))

  rename-fresh : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {X : TyVar Δ}
      {A : Ty Δ}
    → (∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
    → X ∉ᵗ A
    → ρ X ∉ᵗ renameᵗ ρ A
  rename-fresh inj (∉-var X≢Y) =
    ∉-var (λ eq → X≢Y (inj eq))
  rename-fresh inj ∉-base = ∉-base
  rename-fresh inj ∉-star = ∉-star
  rename-fresh inj (∉-fun X∉A X∉B) =
    ∉-fun (rename-fresh inj X∉A) (rename-fresh inj X∉B)
  rename-fresh inj (∉-all X∉A) =
    ∉-all (rename-fresh (ext-injective inj) X∉A)

  shift-fresh : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
    → X ∉ᵗ A
    → suc X ∉ᵗ ⇑ᵗ A
  shift-fresh = rename-fresh suc-injectiveᶠ

  insertʳ-fresh-var : ∀ {Δ} (X : TyVar (Nat.suc Δ))
    → ∀ Y → X ≢ insertʳ X Y
  insertʳ-fresh-var zero Y ()
  insertʳ-fresh-var {Nat.suc Δ} (suc X) zero ()
  insertʳ-fresh-var {Nat.suc Δ} (suc X) (suc Y) eq =
    insertʳ-fresh-var X Y (suc-injectiveᶠ eq)

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

  data WidenPath : ∀ {Δ} → TyVar Δ → Ty Δ → Ty Δ → Set where
    wp-var : ∀ {Δ} {X : TyVar Δ}
      → WidenPath X (＇ X) (＇ X)

    wp-fun-left : ∀ {Δ X A A′ B B′}
      → WidenPath {Δ} X A A′
      → WidenPath X (A ⇒ B) (A′ ⇒ B′)

    wp-fun-right : ∀ {Δ X A A′ B B′}
      → WidenPath {Δ} X B B′
      → WidenPath X (A ⇒ B) (A′ ⇒ B′)

    wp-all : ∀ {Δ X A B}
      → WidenPath {Nat.suc Δ} (suc X) A B
      → WidenPath {Δ} X (`∀ A) (`∀ B)

    wp-inst : ∀ {Δ X A B}
      → WidenPath {Nat.suc Δ} (suc X) A (⇑ᵗ B)
      → WidenPath {Δ} X (`∀ A) B

  source-path-same : ∀ {Δ} {μ : I.ImpEnv Δ} {X : TyVar Δ}
      {A B : Ty Δ}
    → μ X ≡ I.X⊑X
    → I._⊢_⊑_ μ A B
    → X ∈ᵗ A
    → WidenPath X A B
  source-path-same same I.★⊑★ ()
  source-path-same same I.ι⊑ι ()
  source-path-same same I.X⊑X var-∈ = wp-var
  source-path-same same (I.⇒⊑⇒ A⊑A′ B⊑B′)
      (∈-fun-left X∈A) =
    wp-fun-left (source-path-same same A⊑A′ X∈A)
  source-path-same same (I.⇒⊑⇒ A⊑A′ B⊑B′)
      (∈-fun-right X∉A X∈B) =
    wp-fun-right (source-path-same same B⊑B′ X∈B)
  source-path-same same (I.∀⊑∀ A⊑B) (∈-all X∈A) =
    wp-all (source-path-same same A⊑B X∈A)
  source-path-same same p@(I.⇒⊑★ A⊑★ B⊑★) X∈A =
    ⊥-elim (occurs-not-star same X∈A p)
  source-path-same same I.ι⊑★ ()
  source-path-same same (I.X⊑★ x⊑★) var-∈ =
    ⊥-elim (varImp-disjoint same x⊑★)
  source-path-same same (I.∀⊑ Anv zero∈A A⊑B) (∈-all X∈A) =
    wp-inst (source-path-same same A⊑B X∈A)
  source-path-same same I.∀★⊑★ (∈-all ())
  source-path-same same (I.∀⊑★ Ans A⊑★) (∈-all X∈A) =
    ⊥-elim (occurs-not-star same X∈A A⊑★)
  source-path-same same I.bot-elim (∈-all ())
  source-path-same same I.bot⊑★ (∈-all ())

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
    spine-renamed
      (renameᵗ-comp σ ρ T)
      refl
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
    spine-renamed
      refl
      (renameᵗ-comp τ ρ T)
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

  insert-spine : ∀ {Δ} (X : TyVar (Nat.suc Δ))
      {B : Ty (Nat.suc Δ)}
    → EndpointSpine B (renameᵗ (insertʳ X) (`∀ B))
  insert-spine X {B = B} =
    spine-right-all
      (spine-renamed {T = B} {ρ = λ Y → Y} {τ = extᵗ (insertʳ X)}
        (sym (renameᵗ-id′ B)) refl)

  widen-path-star-spine⊥ : ∀ {Δ Δ★} {X : TyVar Δ}
      {A B : Ty Δ}
    → WidenPath X A B
    → EndpointSpine B (★ {Δ★})
    → ⊥
  widen-path-star-spine⊥ wp-var
      (spine-renamed {T = ＇ β} refl ())
  widen-path-star-spine⊥ (wp-fun-left p)
      (spine-renamed {T = T₁ ⇒ T₂} refl ())
  widen-path-star-spine⊥ (wp-fun-right p)
      (spine-renamed {T = T₁ ⇒ T₂} refl ())
  widen-path-star-spine⊥ (wp-all p) (spine-left-all sp) =
    widen-path-star-spine⊥ p sp
  widen-path-star-spine⊥ (wp-all p)
      (spine-renamed {T = `∀ T} refl ())
  widen-path-star-spine⊥ (wp-inst p) sp =
    widen-path-star-spine⊥ p (spine-map-left suc sp)

  widen-spine-overlap⊥ : ∀ {Δ}
      {ν : I.ImpEnv Δ} {X : TyVar Δ}
      {A B C : Ty Δ}
    → ν X ≡ I.X⊑★
    → WidenPath X A B
    → EndpointSpine B C
    → X ∉ᵗ C
    → I._⊢_⊑_ ν A C
    → ⊥
  widen-spine-overlap⊥ to-star wp-var sp fresh I.X⊑X =
    not-occurs fresh var-∈
  widen-spine-overlap⊥ to-star wp-var sp fresh (I.X⊑★ x⊑★) =
    widen-path-star-spine⊥ wp-var sp
  widen-spine-overlap⊥ to-star (wp-fun-left p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl)
      (∉-fun fresh₁ fresh₂) (I.⇒⊑⇒ q₁ q₂) =
    widen-spine-overlap⊥ to-star p (spine-renamed refl refl) fresh₁ q₁
  widen-spine-overlap⊥ to-star (wp-fun-right p)
      (spine-renamed {T = T₁ ⇒ T₂} refl refl)
      (∉-fun fresh₁ fresh₂) (I.⇒⊑⇒ q₁ q₂) =
    widen-spine-overlap⊥ to-star p (spine-renamed refl refl) fresh₂ q₂
  widen-spine-overlap⊥ {Δ = Δ} to-star path@(wp-fun-left p) sp fresh
      (I.⇒⊑★ q₁ q₂) =
    widen-path-star-spine⊥ {Δ = Δ} {Δ★ = Δ} path sp
  widen-spine-overlap⊥ {Δ = Δ} to-star path@(wp-fun-right p) sp fresh
      (I.⇒⊑★ q₁ q₂) =
    widen-path-star-spine⊥ {Δ = Δ} {Δ★ = Δ} path sp
  widen-spine-overlap⊥ to-star (wp-all p) sp (∉-all fresh)
      (I.∀⊑∀ q) =
    widen-spine-overlap⊥ to-star p (spine-strip-both sp) fresh q
  widen-spine-overlap⊥ to-star (wp-all p) sp fresh
      (I.∀⊑ Anv zero∈A q) =
    widen-spine-overlap⊥ to-star p (spine-peel-left suc sp)
      (shift-fresh fresh) q
  widen-spine-overlap⊥ to-star (wp-all p) sp fresh I.∀★⊑★ =
    widen-path-star-spine⊥ (wp-all p) sp
  widen-spine-overlap⊥ to-star (wp-all p) sp fresh
      (I.∀⊑★ Ans q) =
    widen-path-star-spine⊥ (wp-all p) sp
  widen-spine-overlap⊥ to-star (wp-all ()) sp fresh I.bot-elim
  widen-spine-overlap⊥ to-star (wp-all p) sp fresh I.bot⊑★ =
    widen-path-star-spine⊥ (wp-all p) sp
  widen-spine-overlap⊥ to-star (wp-inst p) sp (∉-all fresh)
      (I.∀⊑∀ q) =
    widen-spine-overlap⊥ to-star p (spine-peel-right suc sp) fresh q
  widen-spine-overlap⊥ to-star (wp-inst p) sp fresh
      (I.∀⊑ Anv zero∈A q) =
    widen-spine-overlap⊥ to-star p
      (spine-map-right suc (spine-map-left suc sp))
      (shift-fresh fresh) q
  widen-spine-overlap⊥ to-star (wp-inst p) sp fresh I.∀★⊑★ =
    widen-path-star-spine⊥ (wp-inst p) sp
  widen-spine-overlap⊥ to-star (wp-inst p) sp fresh
      (I.∀⊑★ Ans q) =
    widen-path-star-spine⊥ (wp-inst p) sp
  widen-spine-overlap⊥ to-star (wp-inst ()) sp fresh I.bot-elim
  widen-spine-overlap⊥ to-star (wp-inst p) sp fresh I.bot⊑★ =
    widen-path-star-spine⊥ (wp-inst p) sp

  insert-disjoint : ∀ {Δ} {μ ν : I.ImpEnv (Nat.suc Δ)}
      {A B : Ty (Nat.suc Δ)} {X : TyVar (Nat.suc Δ)}
    → μ X ≡ I.X⊑X
    → ν X ≡ I.X⊑★
    → X ∈ᵗ A
    → I._⊢_⊑_ μ A B
    → I._⊢_⊑_ ν A (renameᵗ (insertʳ X) (`∀ B))
    → ⊥
  insert-disjoint {_} {_} {_} {_} {B} {X} same to-star X∈A p q =
    widen-spine-overlap⊥ to-star (source-path-same same p X∈A)
      (insert-spine X) (insert-fresh X (`∀ B)) q

  ∀⊑∀-∀⊑-disjoint : ∀ {Δ} {μ : I.ImpEnv Δ}
      {A B : Ty (Nat.suc Δ)}
    → zero ∈ᵗ A
    → I._⊢_⊑_ (I.extᵐ μ) A B
    → I._⊢_⊑_ (I.instᵐ μ) A (⇑ᵗ (`∀ B))
    → ⊥
  ∀⊑∀-∀⊑-disjoint zero∈A p q =
    insert-disjoint refl refl zero∈A p q

  dynamic-domain : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
    → (∀ X → X ∈ᵗ A ⇒ B → μ X ≡ I.X⊑★)
    → ∀ X → X ∈ᵗ A → μ X ≡ I.X⊑★
  dynamic-domain dynamic X X∈A = dynamic X (∈-fun-left X∈A)

  dynamic-codomain : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
    → (∀ X → X ∈ᵗ A ⇒ B → μ X ≡ I.X⊑★)
    → ∀ X → X ∈ᵗ B → μ X ≡ I.X⊑★
  dynamic-codomain {A = A} dynamic X X∈B with occurs? X A
  dynamic-codomain dynamic X X∈B | present X∈A =
    dynamic X (∈-fun-left X∈A)
  dynamic-codomain dynamic X X∈B | absent X∉A =
    dynamic X (∈-fun-right X∉A X∈B)

  dynamic-under-inst : ∀ {Δ} {μ : I.ImpEnv Δ}
      {A : Ty (Nat.suc Δ)}
    → (∀ X → X ∈ᵗ `∀ A → μ X ≡ I.X⊑★)
    → ∀ X → X ∈ᵗ A → I.instᵐ μ X ≡ I.X⊑★
  dynamic-under-inst dynamic zero X∈A = refl
  dynamic-under-inst dynamic (suc X) X∈A =
    dynamic X (∈-all X∈A)

  dynamic-under-ext : ∀ {Δ} {μ : I.ImpEnv Δ}
      {A : Ty (Nat.suc Δ)}
    → (∀ X → X ∈ᵗ `∀ A → μ X ≡ I.X⊑★)
    → zero ∉ᵗ A
    → ∀ X → X ∈ᵗ A → I.extᵐ μ X ≡ I.X⊑★
  dynamic-under-ext dynamic zero∉A zero zero∈A =
    ⊥-elim (not-occurs zero∉A zero∈A)
  dynamic-under-ext dynamic zero∉A (suc X) X∈A =
    dynamic X (∈-all X∈A)

  data Shape : ∀ {Δ} → Ty Δ → Set where
    var-shape : ∀ {Δ} {X : TyVar Δ} → Shape (＇ X)
    base-shape : ∀ {Δ ι} → Shape (‵_ {Δ} ι)
    star-shape : ∀ {Δ} → Shape (★ {Δ})
    fun-shape : ∀ {Δ} {A B : Ty Δ}
      → Shape A
      → Shape B
      → Shape (A ⇒ B)
    all-shape : ∀ {Δ} {A : Ty (Nat.suc Δ)}
      → Shape A
      → Shape (`∀ A)

  shape : ∀ {Δ} (A : Ty Δ) → Shape A
  shape (＇ X) = var-shape
  shape (‵ ι) = base-shape
  shape ★ = star-shape
  shape (A ⇒ B) = fun-shape (shape A) (shape B)
  shape (`∀ A) = all-shape (shape A)

  data AllChoice {Δ : TyCtx} : Ty (Nat.suc Δ) → Set where
    bottom-choice : AllChoice (＇ zero)
    star-choice : AllChoice ★
    inst-choice : ∀ {A}
      → NonVar A
      → zero ∈ᵗ A
      → AllChoice A
    structural-choice : ∀ {A}
      → NonStar A
      → zero ∉ᵗ A
      → AllChoice A

  all-choice : ∀ {Δ} (A : Ty (Nat.suc Δ)) → AllChoice A
  all-choice (＇ zero) = bottom-choice
  all-choice (＇ (suc X)) = structural-choice nonstar-X (∉-var (λ ()))
  all-choice (‵ ι) = structural-choice nonstar-ι ∉-base
  all-choice ★ = star-choice
  all-choice (A ⇒ B) with occurs? zero (A ⇒ B)
  all-choice (A ⇒ B) | present zero∈A⇒B =
    inst-choice nonvar-fun zero∈A⇒B
  all-choice (A ⇒ B) | absent zero∉A⇒B =
    structural-choice nonstar-⇒ zero∉A⇒B
  all-choice (`∀ A) with occurs? zero (`∀ A)
  all-choice (`∀ A) | present zero∈∀A =
    inst-choice nonvar-all zero∈∀A
  all-choice (`∀ A) | absent zero∉∀A =
    structural-choice nonstar-∀ zero∉∀A

  imprecise-star-shape : ∀ {Δ} {μ : I.ImpEnv Δ} {A : Ty Δ}
    → Shape A
    → (∀ X → X ∈ᵗ A → μ X ≡ I.X⊑★)
    → I._⊢_⊑_ μ A ★
  imprecise-star-shape var-shape dynamic =
    I.X⊑★ (dynamic _ var-∈)
  imprecise-star-shape base-shape dynamic = I.ι⊑★
  imprecise-star-shape star-shape dynamic = I.★⊑★
  imprecise-star-shape (fun-shape shape-A shape-B) dynamic =
    I.⇒⊑★ (imprecise-star-shape shape-A (dynamic-domain dynamic))
      (imprecise-star-shape shape-B (dynamic-codomain dynamic))
  imprecise-star-shape (all-shape {A = A} shape-A) dynamic =
    decide (all-choice A)
    where
    decide : AllChoice A → I._⊢_⊑_ _ (`∀ A) ★
    decide bottom-choice = I.bot⊑★
    decide star-choice = I.∀★⊑★
    decide (inst-choice Anv zero∈A) =
      I.∀⊑ Anv zero∈A
        (imprecise-star-shape shape-A (dynamic-under-inst dynamic))
    decide (structural-choice Ans zero∉A) =
      I.∀⊑★ Ans
        (imprecise-star-shape shape-A
          (dynamic-under-ext dynamic zero∉A))

imprecise-star : ∀ (A : Ty 0) → I._⊑_ A ★
imprecise-star A = imprecise-star-shape (shape A) (\ ())

------------------------------------------------------------------------
-- Fresh type-variable consequences
------------------------------------------------------------------------

imprecision-no-to-distinct-variable : ∀ {Δ : TyCtx}
    {μ : I.ImpEnv Δ} {A : Ty Δ} {X Y : TyVar Δ}
  → μ Y ≡ I.X⊑★
  → μ X ≡ I.X⊑X
  → I._⊢_⊑_ μ A (＇ X)
  → Y ∈ᵗ A
  → ⊥
imprecision-no-to-distinct-variable Y★ XX (I.X⊑X {X = X}) var-∈ =
  varImp-disjoint XX Y★
imprecision-no-to-distinct-variable Y★ XX
    (I.∀⊑ Anv zero∈A A⊑X) (∈-all Y∈A) =
  imprecision-no-to-distinct-variable Y★ XX A⊑X Y∈A

imprecision-to-fresh : ∀ {Δ : TyCtx} {μ : I.ImpEnv Δ}
    {A : Ty (Nat.suc Δ)}
  → I._⊢_⊑_ (I.extᵐ μ) A (＇ zero)
  → A ≡ ＇ zero
imprecision-to-fresh (I.X⊑X {X = zero}) = refl
imprecision-to-fresh (I.∀⊑ Anv zero∈A A⊑X) =
  ⊥-elim (imprecision-no-to-distinct-variable refl refl A⊑X zero∈A)

imprecision-no-star-to-bot : ∀ {Δ : TyCtx}
    {μ : I.ImpEnv Δ} {A : Ty Δ} {Y : TyVar Δ}
  → μ Y ≡ I.X⊑★
  → I._⊢_⊑_ μ A (`∀ (＇ zero))
  → Y ∈ᵗ A
  → ⊥
imprecision-no-star-to-bot {Y = Y} Y★ (I.∀⊑∀ A⊑X) (∈-all Y∈A) =
  imprecision-no-to-distinct-variable {X = zero} {Y = suc Y}
    Y★ refl A⊑X Y∈A
imprecision-no-star-to-bot {Y = Y} Y★
    (I.∀⊑ Anv zero∈A A⊑B) (∈-all Y∈A) =
  imprecision-no-star-to-bot {Y = suc Y} Y★ A⊑B Y∈A

------------------------------------------------------------------------
-- Uniqueness of occurrence evidence
------------------------------------------------------------------------

∉ᵗ-unique : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
  → (p q : X ∉ᵗ A)
  → p ≡ q
∉ᵗ-unique (∉-var X≢Y) (∉-var X≢Y′) =
  cong ∉-var (¬-unique X≢Y X≢Y′)
∉ᵗ-unique ∉-base ∉-base = refl
∉ᵗ-unique ∉-star ∉-star = refl
∉ᵗ-unique (∉-fun X∉A X∉B) (∉-fun X∉A′ X∉B′)
    rewrite ∉ᵗ-unique X∉A X∉A′
          | ∉ᵗ-unique X∉B X∉B′ =
  refl
∉ᵗ-unique (∉-all X∉A) (∉-all X∉A′)
    rewrite ∉ᵗ-unique X∉A X∉A′ =
  refl

∈ᵗ-unique : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
  → (p q : X ∈ᵗ A)
  → p ≡ q
∈ᵗ-unique var-∈ var-∈ = refl
∈ᵗ-unique (∈-fun-left X∈A) (∈-fun-left X∈A′)
    rewrite ∈ᵗ-unique X∈A X∈A′ =
  refl
∈ᵗ-unique (∈-fun-left X∈A) (∈-fun-right X∉A X∈B) =
  ⊥-elim (not-occurs X∉A X∈A)
∈ᵗ-unique (∈-fun-right X∉A X∈B) (∈-fun-left X∈A) =
  ⊥-elim (not-occurs X∉A X∈A)
∈ᵗ-unique (∈-fun-right X∉A X∈B) (∈-fun-right X∉A′ X∈B′)
    rewrite ∉ᵗ-unique X∉A X∉A′
          | ∈ᵗ-unique X∈B X∈B′ =
  refl
∈ᵗ-unique (∈-all X∈A) (∈-all X∈A′)
    rewrite ∈ᵗ-unique X∈A X∈A′ =
  refl

------------------------------------------------------------------------
-- Uniqueness of type imprecision
------------------------------------------------------------------------

varImp-eq-unique : ∀ {v w : I.VarImp}
  → (p q : v ≡ w)
  → p ≡ q
varImp-eq-unique refl refl = refl

⊑-unique : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
  → (p q : I._⊢_⊑_ μ A B)
  → p ≡ q
⊑-unique I.★⊑★ I.★⊑★ = refl
⊑-unique I.ι⊑ι I.ι⊑ι = refl
⊑-unique I.X⊑X I.X⊑X = refl
⊑-unique (I.⇒⊑⇒ A⊑A′ B⊑B′) (I.⇒⊑⇒ A⊑A″ B⊑B″)
    rewrite ⊑-unique A⊑A′ A⊑A″
          | ⊑-unique B⊑B′ B⊑B″ =
  refl
⊑-unique (I.∀⊑∀ A⊑B) (I.∀⊑∀ A⊑B′)
    rewrite ⊑-unique A⊑B A⊑B′ =
  refl
⊑-unique (I.∀⊑∀ A⊑B) (I.∀⊑ Anv zero∈A A⊑B′) =
  ⊥-elim (∀⊑∀-∀⊑-disjoint zero∈A A⊑B A⊑B′)
⊑-unique (I.∀⊑∀ A⊑★) I.bot-elim =
  ⊥-elim (occurs-not-star refl var-∈ A⊑★)
⊑-unique (I.⇒⊑★ A⊑★ B⊑★) (I.⇒⊑★ A⊑★′ B⊑★′)
    rewrite ⊑-unique A⊑★ A⊑★′
          | ⊑-unique B⊑★ B⊑★′ =
  refl
⊑-unique I.ι⊑★ I.ι⊑★ = refl
⊑-unique (I.X⊑★ x⊑★) (I.X⊑★ x⊑★′)
    rewrite varImp-eq-unique x⊑★ x⊑★′ =
  refl
⊑-unique (I.∀⊑ Anv zero∈A A⊑B)
    (I.∀⊑ Anv′ zero∈A′ A⊑B′)
    rewrite nonVar-unique Anv Anv′
          | ∈ᵗ-unique zero∈A zero∈A′
          | ⊑-unique A⊑B A⊑B′ =
  refl
⊑-unique (I.∀⊑ Anv zero∈A A⊑B) (I.∀⊑∀ A⊑B′) =
  ⊥-elim (∀⊑∀-∀⊑-disjoint zero∈A A⊑B′ A⊑B)
⊑-unique (I.∀⊑ Anv zero∈A A⊑B) (I.∀⊑★ Ans A⊑★) =
  ⊥-elim (occurs-not-star refl zero∈A A⊑★)
⊑-unique I.∀★⊑★ I.∀★⊑★ = refl
⊑-unique (I.∀⊑★ Ans A⊑★) (I.∀⊑★ Ans′ A⊑★′)
    rewrite nonStar-unique Ans Ans′
          | ⊑-unique A⊑★ A⊑★′ =
  refl
⊑-unique (I.∀⊑★ Ans A⊑★) (I.∀⊑ Anv zero∈A A⊑B) =
  ⊥-elim (occurs-not-star refl zero∈A A⊑★)
⊑-unique (I.∀⊑★ Ans A⊑★) I.bot⊑★ =
  ⊥-elim (occurs-not-star refl var-∈ A⊑★)
⊑-unique I.bot-elim I.bot-elim = refl
⊑-unique I.bot-elim (I.∀⊑∀ A⊑★) =
  ⊥-elim (occurs-not-star refl var-∈ A⊑★)
⊑-unique I.bot⊑★ I.bot⊑★ = refl
⊑-unique I.bot⊑★ (I.∀⊑★ Ans A⊑★) =
  ⊥-elim (occurs-not-star refl var-∈ A⊑★)
