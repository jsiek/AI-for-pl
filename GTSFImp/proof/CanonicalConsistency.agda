module proof.CanonicalConsistency where

-- File Charter:
--   * Defines a canonical, ordered variant of type consistency.
--   * Orders generated-forall consistency by blocking only an immediate
--     `gen` step under `inst`.
--   * Proves soundness into declarative consistency.
--   * Proves proof irrelevance for ground-to-dynamic consistency fragments.

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
import Data.Nat as Nat
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (no; yes)

open import Types
open import Consistency
  using (Env∼; Var∼; X∼X; X∼★; ★∼X; extᵐ; instᵐ; genᵐ;
         _⊢_∼★; _⊢★∼_; ⇒∼★; ι∼★; X∼★ᵍ; ∀∼★;
         ★∼⇒; ★∼ι; ★∼Xᵍ; ★∼∀)
import Consistency as C
import proof.Consistency as CP
open import proof.Imprecision using (∈ᵗ-unique)
open import proof.ImprecisionConsistency
  using (consistency-source-occurs-target; fin-suc-injective;
         rename-not-occurs; rename-occurs; shift-occurs;
         unshift-occurs; ground-self-occurs⊥)
open import proof.OccurrenceSpine
  using (EndpointSpine; EndpointGap; Fresh; OccPath; op-var; op-fun-left;
         op-fun-right; op-all; op-inst; op-gen; spine-renamed;
         spine-left-all; spine-right-all; spine-map-left; spine-map-right;
         spine-peel-left; spine-peel-right; spine-strip-both;
         spine-fun-left; spine-fun-right;
         path-shift; path-left-star-spine⊥; path-right-star-spine⊥;
         path-source-occurs; path-target-occurs;
         fresh-fun-left; fresh-fun-right; fresh-all; fresh-shift;
         insertʳ; insertʳ-ext; insert-spine; insert-fresh-occ; not-occurs;
         end-insert; endpoint-gap-spine; endpoint-gap-fresh;
         gap-shift; gap-peel-left-all; gap-peel-right-all;
         gap-strip-both; gap-fun-left; gap-fun-right;
         occurs-left-star-spine⊥)

private
  postulate
    funext : Extensionality 0ℓ 0ℓ

  ¬-unique : ∀ {A : Set} (p q : A → ⊥) → p ≡ q
  ¬-unique p q = funext (λ x → ⊥-elim (p x))

data GenMode : Set where
  gen-ok : GenMode
  gen-blocked : GenMode

data CanGen : GenMode → Set where
  can-gen : CanGen gen-ok

infix 4 _⊢_∼ᵏ[_]_
infixr 7 _↦ᵏ_
infix 8 _!ᵏ ？ᵏ_

data _⊢_∼ᵏ[_]_ {Δ : TyCtx} (μ : Env∼ Δ) :
    Ty Δ → GenMode → Ty Δ → Set where

  idᵏ : ∀ {m A}
    → Atom A
      ---------
    → μ ⊢ A ∼ᵏ[ m ] A

  _↦ᵏ_ : ∀ {m A A′ B B′}
    → μ ⊢ A ∼ᵏ[ gen-ok ] A′
    → μ ⊢ B ∼ᵏ[ gen-ok ] B′
      --------------------------------
    → μ ⊢ (A ⇒ B) ∼ᵏ[ m ] (A′ ⇒ B′)

  ∀ᵏ_ : ∀ {m A B}
    → extᵐ μ ⊢ A ∼ᵏ[ gen-ok ] B
      ----------------------------
    → μ ⊢ (`∀ A) ∼ᵏ[ m ] (`∀ B)

  _!ᵏ : ∀ {m A G}
    → ⦃ Gᵍ : Ground G ⦄
    → ⦃ G∼★ : μ ⊢ G ∼★ ⦄
    → μ ⊢ A ∼ᵏ[ gen-ok ] G
    → ⦃ Ans : NonStar A ⦄
      ----------------
    → μ ⊢ A ∼ᵏ[ m ] ★

  ？ᵏ_ : ∀ {m G B}
    → ⦃ Gᵍ : Ground G ⦄
    → ⦃ ★∼G : μ ⊢★∼ G ⦄
    → μ ⊢ G ∼ᵏ[ gen-ok ] B
    → ⦃ Bns : NonStar B ⦄
      ----------------
    → μ ⊢ ★ ∼ᵏ[ m ] B

  instᵏ_ : ∀ {m A B}
    → ⦃ Anv : NonVar A ⦄
    → ⦃ z∈A : zero ∈ᵗ A ⦄
    → instᵐ μ ⊢ A ∼ᵏ[ gen-blocked ] ⇑ᵗ B
    → B ≢ ★
      --------------------------------
    → μ ⊢ (`∀ A) ∼ᵏ[ m ] B

  genᵏ_ : ∀ {A B}
    → ⦃ Bnv : NonVar B ⦄
    → ⦃ z∈B : zero ∈ᵗ B ⦄
    → genᵐ μ ⊢ ⇑ᵗ A ∼ᵏ[ gen-ok ] B
    → A ≢ ★
      --------------------------------------
    → μ ⊢ A ∼ᵏ[ gen-ok ] (`∀ B)

  bot-elimᵏ : ∀ {m}
      ---------------------------------------
    → μ ⊢ (`∀ (＇ zero)) ∼ᵏ[ m ] (`∀ ★)

  bot-introᵏ : ∀ {m}
      ---------------------------------------
    → μ ⊢ (`∀ ★) ∼ᵏ[ m ] (`∀ (＇ zero))

infix 4 _∼ᵏ_

_∼ᵏ_ : ∀ {Δ} → Ty Δ → Ty Δ → Set
A ∼ᵏ B = C.idᶜ ⊢ A ∼ᵏ[ gen-ok ] B

forgetᵏ : ∀ {Δ} {μ : Env∼ Δ} {m A B}
  → μ ⊢ A ∼ᵏ[ m ] B
  → C._⊢_∼_ μ A B
forgetᵏ (idᵏ a) = C.id a
forgetᵏ (c ↦ᵏ d) = forgetᵏ c C.↦ forgetᵏ d
forgetᵏ (∀ᵏ c) = C.∀ᶜ (forgetᵏ c)
forgetᵏ (_!ᵏ ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄) =
  C._! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (forgetᵏ c) ⦃ Ans ⦄
forgetᵏ (？ᵏ_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) =
  C.？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ (forgetᵏ c) ⦃ Bns ⦄
forgetᵏ (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) =
  C.inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ (forgetᵏ c) B≢★
forgetᵏ (genᵏ_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) =
  C.gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ (forgetᵏ c) A≢★
forgetᵏ bot-elimᵏ = C.bot-elim
forgetᵏ bot-introᵏ = C.bot-intro

∼★-unique : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
  → (c d : μ ⊢ A ∼★)
  → c ≡ d
∼★-unique = CP.∼★-unique

★∼-unique : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
  → (c d : μ ⊢★∼ A)
  → c ≡ d
★∼-unique = CP.★∼-unique

rename-∈ᵗ : ∀ {Δ Δ′} {X : TyVar Δ} {A : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → X ∈ᵗ A
  → ρ X ∈ᵗ renameᵗ ρ A
rename-∈ᵗ ρ var-∈ = var-∈
rename-∈ᵗ ρ (∈-fun-left X∈A) =
  ∈-fun-left (rename-∈ᵗ ρ X∈A)
rename-∈ᵗ {X = X} {A = A ⇒ B} ρ (∈-fun-right X∉A X∈B)
    with occurs? (ρ X) (renameᵗ ρ A)
rename-∈ᵗ {X = X} {A = A ⇒ B} ρ (∈-fun-right X∉A X∈B)
    | present ρX∈A =
  ∈-fun-left ρX∈A
rename-∈ᵗ {X = X} {A = A ⇒ B} ρ (∈-fun-right X∉A X∈B)
    | absent ρX∉A =
  ∈-fun-right ρX∉A (rename-∈ᵗ ρ X∈B)
rename-∈ᵗ ρ (∈-all X∈A) =
  ∈-all (rename-∈ᵗ (extᵗ ρ) X∈A)

rename-≢★ : ∀ {Δ Δ′} {A : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → A ≢ ★
  → renameᵗ ρ A ≢ ★
rename-≢★ {A = ＇ X} ρ A≢★ ()
rename-≢★ {A = ‵ ι} ρ A≢★ ()
rename-≢★ {A = ★} ρ A≢★ refl = A≢★ refl
rename-≢★ {A = A ⇒ B} ρ A≢★ ()
rename-≢★ {A = `∀ A} ρ A≢★ ()

shift-∉ᵗ : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
  → X ∉ᵗ A
  → suc X ∉ᵗ ⇑ᵗ A
shift-∉ᵗ = rename-not-occurs suc fin-suc-injective

rename-insert-ext : ∀ {Δ} (X : TyVar (Nat.suc Δ))
    (A : Ty (Nat.suc Δ))
  → renameᵗ (extᵗ (insertʳ X)) A ≡ renameᵗ (insertʳ (suc X)) A
rename-insert-ext X A = renameᵗ-cong A (insertʳ-ext X)

data InsertOverlapState : ∀ {Δ}
    → Env∼ Δ
    → Env∼ Δ
    → TyVar Δ
    → GenMode
    → GenMode
    → Ty Δ
    → Ty Δ
    → Ty Δ
    → Ty Δ
    → Set where

  ios-base : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty (Nat.suc Δ)}
    → InsertOverlapState (instᵐ μ) (genᵐ μ) zero
        gen-blocked gen-ok A B (⇑ᵗ (`∀ B)) (⇑ᵗ (`∀ A))

  ios-fun-left : ∀ {Δ} {μ ν : Env∼ Δ} {X : TyVar Δ}
      {m n} {A A′ B B′ C C′ D D′ : Ty Δ}
    → InsertOverlapState μ ν X m n
        (A ⇒ A′) (B ⇒ B′) (C ⇒ C′) (D ⇒ D′)
    → InsertOverlapState μ ν X gen-ok gen-ok A B C D

  ios-fun-right : ∀ {Δ} {μ ν : Env∼ Δ} {X : TyVar Δ}
      {m n} {A A′ B B′ C C′ D D′ : Ty Δ}
    → InsertOverlapState μ ν X m n
        (A ⇒ A′) (B ⇒ B′) (C ⇒ C′) (D ⇒ D′)
    → InsertOverlapState μ ν X gen-ok gen-ok A′ B′ C′ D′

  ios-∀∀ : ∀ {Δ} {μ ν : Env∼ Δ} {X : TyVar Δ}
      {m n} {A B C D : Ty (Nat.suc Δ)}
    → InsertOverlapState μ ν X m n
        (`∀ A) (`∀ B) (`∀ C) (`∀ D)
    → InsertOverlapState (extᵐ μ) (extᵐ ν) (suc X)
        gen-ok gen-ok A B C D

  ios-∀inst : ∀ {Δ} {μ ν : Env∼ Δ} {X : TyVar Δ}
      {m n} {A C D : Ty (Nat.suc Δ)} {B : Ty Δ}
    → InsertOverlapState μ ν X m n
        (`∀ A) B (`∀ C) (`∀ D)
    → InsertOverlapState (extᵐ μ) (instᵐ ν) (suc X)
        gen-ok gen-blocked A (⇑ᵗ B) C D

  ios-∀gen : ∀ {Δ} {μ ν : Env∼ Δ} {X : TyVar Δ}
      {m n} {A B C : Ty (Nat.suc Δ)} {D : Ty Δ}
    → CanGen n
    → InsertOverlapState μ ν X m n
        (`∀ A) (`∀ B) (`∀ C) D
    → InsertOverlapState (extᵐ μ) (genᵐ ν) (suc X)
        gen-ok gen-ok A B C (⇑ᵗ D)

  ios-inst∀ : ∀ {Δ} {μ ν : Env∼ Δ} {X : TyVar Δ}
      {m n} {A B D : Ty (Nat.suc Δ)} {C : Ty Δ}
    → InsertOverlapState μ ν X m n
        (`∀ A) (`∀ B) C (`∀ D)
    → InsertOverlapState (instᵐ μ) (extᵐ ν) (suc X)
        gen-blocked gen-ok A B (⇑ᵗ C) D

  ios-instinst : ∀ {Δ} {μ ν : Env∼ Δ} {X : TyVar Δ}
      {m n} {A D : Ty (Nat.suc Δ)} {B C : Ty Δ}
    → InsertOverlapState μ ν X m n
        (`∀ A) B C (`∀ D)
    → InsertOverlapState (instᵐ μ) (instᵐ ν) (suc X)
        gen-blocked gen-blocked A (⇑ᵗ B) (⇑ᵗ C) D

  ios-instgen : ∀ {Δ} {μ ν : Env∼ Δ} {X : TyVar Δ}
      {m n} {A B : Ty (Nat.suc Δ)} {C D : Ty Δ}
    → CanGen n
    → InsertOverlapState μ ν X m n
        (`∀ A) (`∀ B) C D
    → InsertOverlapState (instᵐ μ) (genᵐ ν) (suc X)
        gen-blocked gen-ok A B (⇑ᵗ C) (⇑ᵗ D)

  ios-gen∀ : ∀ {Δ} {μ ν : Env∼ Δ} {X : TyVar Δ}
      {m n} {A : Ty Δ} {B C D : Ty (Nat.suc Δ)}
    → CanGen m
    → InsertOverlapState μ ν X m n
        A (`∀ B) (`∀ C) (`∀ D)
    → InsertOverlapState (genᵐ μ) (extᵐ ν) (suc X)
        gen-ok gen-ok (⇑ᵗ A) B C D

  ios-geninst : ∀ {Δ} {μ ν : Env∼ Δ} {X : TyVar Δ}
      {m n} {A B : Ty Δ} {C D : Ty (Nat.suc Δ)}
    → CanGen m
    → InsertOverlapState μ ν X m n
        A B (`∀ C) (`∀ D)
    → InsertOverlapState (genᵐ μ) (instᵐ ν) (suc X)
        gen-ok gen-blocked (⇑ᵗ A) (⇑ᵗ B) C D

  ios-gengen : ∀ {Δ} {μ ν : Env∼ Δ} {X : TyVar Δ}
      {m n} {A D : Ty Δ} {B C : Ty (Nat.suc Δ)}
    → CanGen m
    → CanGen n
    → InsertOverlapState μ ν X m n
        A (`∀ B) (`∀ C) D
    → InsertOverlapState (genᵐ μ) (genᵐ ν) (suc X)
        gen-ok gen-ok (⇑ᵗ A) B C (⇑ᵗ D)

  ios-left∀ : ∀ {Δ} {μ ν : Env∼ Δ} {X : TyVar Δ}
      {m n} {A C : Ty (Nat.suc Δ)} {B D : Ty Δ}
    → InsertOverlapState μ ν X m n
        (`∀ A) B (`∀ C) D
    → InsertOverlapState (extᵐ μ) (extᵐ ν) (suc X)
        gen-ok n A (⇑ᵗ B) C (⇑ᵗ D)

  ios-left-inst : ∀ {Δ} {μ ν : Env∼ Δ} {X : TyVar Δ}
      {m n} {A : Ty (Nat.suc Δ)} {B C D : Ty Δ}
    → InsertOverlapState μ ν X m n
        (`∀ A) B C D
    → InsertOverlapState (instᵐ μ) (extᵐ ν) (suc X)
        gen-blocked n A (⇑ᵗ B) (⇑ᵗ C) (⇑ᵗ D)

  ios-left-gen : ∀ {Δ} {μ ν : Env∼ Δ} {X : TyVar Δ}
      {m n} {A B D : Ty Δ} {C : Ty (Nat.suc Δ)}
    → CanGen m
    → InsertOverlapState μ ν X m n
        A B (`∀ C) D
    → InsertOverlapState (genᵐ μ) (extᵐ ν) (suc X)
        gen-ok n (⇑ᵗ A) (⇑ᵗ B) C (⇑ᵗ D)

  ios-right∀ : ∀ {Δ} {μ ν : Env∼ Δ} {X : TyVar Δ}
      {m n} {A C : Ty Δ} {B D : Ty (Nat.suc Δ)}
    → InsertOverlapState μ ν X m n
        A (`∀ B) C (`∀ D)
    → InsertOverlapState (extᵐ μ) (extᵐ ν) (suc X)
        m gen-ok (⇑ᵗ A) B (⇑ᵗ C) D

  ios-right-inst : ∀ {Δ} {μ ν : Env∼ Δ} {X : TyVar Δ}
      {m n} {A B C : Ty Δ} {D : Ty (Nat.suc Δ)}
    → InsertOverlapState μ ν X m n
        A B C (`∀ D)
    → InsertOverlapState (extᵐ μ) (instᵐ ν) (suc X)
        m gen-blocked (⇑ᵗ A) (⇑ᵗ B) (⇑ᵗ C) D

  ios-right-gen : ∀ {Δ} {μ ν : Env∼ Δ} {X : TyVar Δ}
      {m n} {A C D : Ty Δ} {B : Ty (Nat.suc Δ)}
    → CanGen n
    → InsertOverlapState μ ν X m n
        A (`∀ B) C D
    → InsertOverlapState (extᵐ μ) (genᵐ ν) (suc X)
        m gen-ok (⇑ᵗ A) B (⇑ᵗ C) (⇑ᵗ D)

state-to : ∀ {Δ} {μ ν : Env∼ Δ} {X m n A B C D}
  → InsertOverlapState μ ν X m n A B C D
  → μ X ≡ X∼★
state-to ios-base = refl
state-to (ios-fun-left st) = state-to st
state-to (ios-fun-right st) = state-to st
state-to (ios-∀∀ st) = state-to st
state-to (ios-∀inst st) = state-to st
state-to (ios-∀gen _ st) = state-to st
state-to (ios-inst∀ st) = state-to st
state-to (ios-instinst st) = state-to st
state-to (ios-instgen _ st) = state-to st
state-to (ios-gen∀ _ st) = state-to st
state-to (ios-geninst _ st) = state-to st
state-to (ios-gengen _ _ st) = state-to st
state-to (ios-left∀ st) = state-to st
state-to (ios-left-inst st) = state-to st
state-to (ios-left-gen _ st) = state-to st
state-to (ios-right∀ st) = state-to st
state-to (ios-right-inst st) = state-to st
state-to (ios-right-gen _ st) = state-to st

state-from : ∀ {Δ} {μ ν : Env∼ Δ} {X m n A B C D}
  → InsertOverlapState μ ν X m n A B C D
  → ν X ≡ ★∼X
state-from ios-base = refl
state-from (ios-fun-left st) = state-from st
state-from (ios-fun-right st) = state-from st
state-from (ios-∀∀ st) = state-from st
state-from (ios-∀inst st) = state-from st
state-from (ios-∀gen _ st) = state-from st
state-from (ios-inst∀ st) = state-from st
state-from (ios-instinst st) = state-from st
state-from (ios-instgen _ st) = state-from st
state-from (ios-gen∀ _ st) = state-from st
state-from (ios-geninst _ st) = state-from st
state-from (ios-gengen _ _ st) = state-from st
state-from (ios-left∀ st) = state-from st
state-from (ios-left-inst st) = state-from st
state-from (ios-left-gen _ st) = state-from st
state-from (ios-right∀ st) = state-from st
state-from (ios-right-inst st) = state-from st
state-from (ios-right-gen _ st) = state-from st

state-spineC : ∀ {Δ} {μ ν : Env∼ Δ} {X m n A B C D}
  → InsertOverlapState μ ν X m n A B C D
  → EndpointSpine B C
state-spineC (ios-base {B = B}) = insert-spine zero {B = B}
state-spineC (ios-fun-left st) = spine-fun-left (state-spineC st)
state-spineC (ios-fun-right st) = spine-fun-right (state-spineC st)
state-spineC (ios-∀∀ st) = spine-strip-both (state-spineC st)
state-spineC (ios-∀inst st) = spine-peel-right suc (state-spineC st)
state-spineC (ios-∀gen _ st) = spine-strip-both (state-spineC st)
state-spineC (ios-inst∀ st) = spine-peel-left suc (state-spineC st)
state-spineC (ios-instinst st) =
  spine-map-right suc (spine-map-left suc (state-spineC st))
state-spineC (ios-instgen _ st) = spine-peel-left suc (state-spineC st)
state-spineC (ios-gen∀ _ st) = spine-strip-both (state-spineC st)
state-spineC (ios-geninst _ st) = spine-peel-right suc (state-spineC st)
state-spineC (ios-gengen _ _ st) = spine-strip-both (state-spineC st)
state-spineC (ios-left∀ st) = spine-peel-right suc (state-spineC st)
state-spineC (ios-left-inst st) =
  spine-map-right suc (spine-map-left suc (state-spineC st))
state-spineC (ios-left-gen _ st) = spine-peel-right suc (state-spineC st)
state-spineC (ios-right∀ st) = spine-peel-left suc (state-spineC st)
state-spineC (ios-right-inst st) =
  spine-map-right suc (spine-map-left suc (state-spineC st))
state-spineC (ios-right-gen _ st) = spine-peel-left suc (state-spineC st)

state-spineD : ∀ {Δ} {μ ν : Env∼ Δ} {X m n A B C D}
  → InsertOverlapState μ ν X m n A B C D
  → EndpointSpine A D
state-spineD (ios-base {A = A}) = insert-spine zero {B = A}
state-spineD (ios-fun-left st) = spine-fun-left (state-spineD st)
state-spineD (ios-fun-right st) = spine-fun-right (state-spineD st)
state-spineD (ios-∀∀ st) = spine-strip-both (state-spineD st)
state-spineD (ios-∀inst st) = spine-strip-both (state-spineD st)
state-spineD (ios-∀gen _ st) = spine-peel-left suc (state-spineD st)
state-spineD (ios-inst∀ st) = spine-strip-both (state-spineD st)
state-spineD (ios-instinst st) = spine-strip-both (state-spineD st)
state-spineD (ios-instgen _ st) = spine-peel-left suc (state-spineD st)
state-spineD (ios-gen∀ _ st) = spine-peel-right suc (state-spineD st)
state-spineD (ios-geninst _ st) = spine-peel-right suc (state-spineD st)
state-spineD (ios-gengen _ _ st) =
  spine-map-right suc (spine-map-left suc (state-spineD st))
state-spineD (ios-left∀ st) = spine-peel-left suc (state-spineD st)
state-spineD (ios-left-inst st) = spine-peel-left suc (state-spineD st)
state-spineD (ios-left-gen _ st) =
  spine-map-right suc (spine-map-left suc (state-spineD st))
state-spineD (ios-right∀ st) = spine-peel-right suc (state-spineD st)
state-spineD (ios-right-inst st) = spine-peel-right suc (state-spineD st)
state-spineD (ios-right-gen _ st) =
  spine-map-right suc (spine-map-left suc (state-spineD st))

state-gapC : ∀ {Δ} {μ ν : Env∼ Δ} {X m n A B C D}
  → InsertOverlapState μ ν X m n A B C D
  → EndpointGap X B C
state-gapC ios-base = end-insert
state-gapC (ios-fun-left st) = gap-fun-left (state-gapC st)
state-gapC (ios-fun-right st) = gap-fun-right (state-gapC st)
state-gapC (ios-∀∀ st) = gap-strip-both (state-gapC st)
state-gapC (ios-∀inst st) = gap-peel-right-all (state-gapC st)
state-gapC (ios-∀gen _ st) = gap-strip-both (state-gapC st)
state-gapC (ios-inst∀ st) = gap-peel-left-all (state-gapC st)
state-gapC (ios-instinst st) = gap-shift (state-gapC st)
state-gapC (ios-instgen _ st) = gap-peel-left-all (state-gapC st)
state-gapC (ios-gen∀ _ st) = gap-strip-both (state-gapC st)
state-gapC (ios-geninst _ st) = gap-peel-right-all (state-gapC st)
state-gapC (ios-gengen _ _ st) = gap-strip-both (state-gapC st)
state-gapC (ios-left∀ st) = gap-peel-right-all (state-gapC st)
state-gapC (ios-left-inst st) = gap-shift (state-gapC st)
state-gapC (ios-left-gen _ st) = gap-peel-right-all (state-gapC st)
state-gapC (ios-right∀ st) = gap-peel-left-all (state-gapC st)
state-gapC (ios-right-inst st) = gap-shift (state-gapC st)
state-gapC (ios-right-gen _ st) = gap-peel-left-all (state-gapC st)

state-gapD : ∀ {Δ} {μ ν : Env∼ Δ} {X m n A B C D}
  → InsertOverlapState μ ν X m n A B C D
  → EndpointGap X A D
state-gapD ios-base = end-insert
state-gapD (ios-fun-left st) = gap-fun-left (state-gapD st)
state-gapD (ios-fun-right st) = gap-fun-right (state-gapD st)
state-gapD (ios-∀∀ st) = gap-strip-both (state-gapD st)
state-gapD (ios-∀inst st) = gap-strip-both (state-gapD st)
state-gapD (ios-∀gen _ st) = gap-peel-left-all (state-gapD st)
state-gapD (ios-inst∀ st) = gap-strip-both (state-gapD st)
state-gapD (ios-instinst st) = gap-strip-both (state-gapD st)
state-gapD (ios-instgen _ st) = gap-peel-left-all (state-gapD st)
state-gapD (ios-gen∀ _ st) = gap-peel-right-all (state-gapD st)
state-gapD (ios-geninst _ st) = gap-peel-right-all (state-gapD st)
state-gapD (ios-gengen _ _ st) = gap-shift (state-gapD st)
state-gapD (ios-left∀ st) = gap-peel-left-all (state-gapD st)
state-gapD (ios-left-inst st) = gap-peel-left-all (state-gapD st)
state-gapD (ios-left-gen _ st) = gap-shift (state-gapD st)
state-gapD (ios-right∀ st) = gap-peel-right-all (state-gapD st)
state-gapD (ios-right-inst st) = gap-peel-right-all (state-gapD st)
state-gapD (ios-right-gen _ st) = gap-shift (state-gapD st)

state-freshC : ∀ {Δ} {μ ν : Env∼ Δ} {X m n A B C D}
  → InsertOverlapState μ ν X m n A B C D
  → Fresh X C
state-freshC (ios-base {B = B}) = insert-fresh-occ zero (`∀ B)
state-freshC (ios-fun-left st) = fresh-fun-left (state-freshC st)
state-freshC (ios-fun-right st) = fresh-fun-right (state-freshC st)
state-freshC (ios-∀∀ st) = fresh-all (state-freshC st)
state-freshC (ios-∀inst st) = fresh-all (state-freshC st)
state-freshC (ios-∀gen _ st) = fresh-all (state-freshC st)
state-freshC (ios-inst∀ st) = fresh-shift (state-freshC st)
state-freshC (ios-instinst st) = fresh-shift (state-freshC st)
state-freshC (ios-instgen _ st) = fresh-shift (state-freshC st)
state-freshC (ios-gen∀ _ st) = fresh-all (state-freshC st)
state-freshC (ios-geninst _ st) = fresh-all (state-freshC st)
state-freshC (ios-gengen _ _ st) = fresh-all (state-freshC st)
state-freshC (ios-left∀ st) = fresh-all (state-freshC st)
state-freshC (ios-left-inst st) = fresh-shift (state-freshC st)
state-freshC (ios-left-gen _ st) = fresh-all (state-freshC st)
state-freshC (ios-right∀ st) = fresh-shift (state-freshC st)
state-freshC (ios-right-inst st) = fresh-shift (state-freshC st)
state-freshC (ios-right-gen _ st) = fresh-shift (state-freshC st)

state-freshD : ∀ {Δ} {μ ν : Env∼ Δ} {X m n A B C D}
  → InsertOverlapState μ ν X m n A B C D
  → Fresh X D
state-freshD (ios-base {A = A}) = insert-fresh-occ zero (`∀ A)
state-freshD (ios-fun-left st) = fresh-fun-left (state-freshD st)
state-freshD (ios-fun-right st) = fresh-fun-right (state-freshD st)
state-freshD (ios-∀∀ st) = fresh-all (state-freshD st)
state-freshD (ios-∀inst st) = fresh-all (state-freshD st)
state-freshD (ios-∀gen _ st) = fresh-shift (state-freshD st)
state-freshD (ios-inst∀ st) = fresh-all (state-freshD st)
state-freshD (ios-instinst st) = fresh-all (state-freshD st)
state-freshD (ios-instgen _ st) = fresh-shift (state-freshD st)
state-freshD (ios-gen∀ _ st) = fresh-all (state-freshD st)
state-freshD (ios-geninst _ st) = fresh-all (state-freshD st)
state-freshD (ios-gengen _ _ st) = fresh-shift (state-freshD st)
state-freshD (ios-left∀ st) = fresh-shift (state-freshD st)
state-freshD (ios-left-inst st) = fresh-shift (state-freshD st)
state-freshD (ios-left-gen _ st) = fresh-shift (state-freshD st)
state-freshD (ios-right∀ st) = fresh-all (state-freshD st)
state-freshD (ios-right-inst st) = fresh-all (state-freshD st)
state-freshD (ios-right-gen _ st) = fresh-shift (state-freshD st)

renameGroundᵏ : ∀ {Δ Δ′} {G : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → Ground G
  → Ground (renameᵗ ρ G)
renameGroundᵏ ρ ★⇒★ = ★⇒★
renameGroundᵏ ρ (‵ ι) = ‵ ι
renameGroundᵏ ρ (＇ X) = ＇ (ρ X)
renameGroundᵏ ρ ∀★ = ∀★

extᵐ-renameᵏ : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
  → (ρ : Δ ⇒ʳ Δ′)
  → (∀ X → μ′ (ρ X) ≡ μ X)
  → ∀ X → extᵐ μ′ (extᵗ ρ X) ≡ extᵐ μ X
extᵐ-renameᵏ ρ eq zero = refl
extᵐ-renameᵏ ρ eq (suc X) = eq X

instᵐ-renameᵏ : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
  → (ρ : Δ ⇒ʳ Δ′)
  → (∀ X → μ′ (ρ X) ≡ μ X)
  → ∀ X → instᵐ μ′ (extᵗ ρ X) ≡ instᵐ μ X
instᵐ-renameᵏ ρ eq zero = refl
instᵐ-renameᵏ ρ eq (suc X) = eq X

genᵐ-renameᵏ : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
  → (ρ : Δ ⇒ʳ Δ′)
  → (∀ X → μ′ (ρ X) ≡ μ X)
  → ∀ X → genᵐ μ′ (extᵗ ρ X) ≡ genᵐ μ X
genᵐ-renameᵏ ρ eq zero = refl
genᵐ-renameᵏ ρ eq (suc X) = eq X

subst-left-∼ᵏ : ∀ {Δ} {μ : Env∼ Δ} {m A A′ B}
  → A ≡ A′
  → μ ⊢ A ∼ᵏ[ m ] B
  → μ ⊢ A′ ∼ᵏ[ m ] B
subst-left-∼ᵏ refl c = c

subst-right-∼ᵏ : ∀ {Δ} {μ : Env∼ Δ} {m A B B′}
  → B ≡ B′
  → μ ⊢ A ∼ᵏ[ m ] B
  → μ ⊢ A ∼ᵏ[ m ] B′
subst-right-∼ᵏ refl c = c

rename∼★ᵏ : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
    {G : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → (∀ X → μ′ (ρ X) ≡ μ X)
  → μ ⊢ G ∼★
  → μ′ ⊢ renameᵗ ρ G ∼★
rename∼★ᵏ ρ eq ⇒∼★ = ⇒∼★
rename∼★ᵏ ρ eq ι∼★ = ι∼★
rename∼★ᵏ ρ eq (X∼★ᵍ {X = X} eq-X) =
  X∼★ᵍ (trans (eq X) eq-X)
rename∼★ᵏ ρ eq ∀∼★ = ∀∼★

rename★∼ᵏ : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
    {G : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → (∀ X → μ′ (ρ X) ≡ μ X)
  → μ ⊢★∼ G
  → μ′ ⊢★∼ renameᵗ ρ G
rename★∼ᵏ ρ eq ★∼⇒ = ★∼⇒
rename★∼ᵏ ρ eq ★∼ι = ★∼ι
rename★∼ᵏ ρ eq (★∼Xᵍ {X = X} eq-X) =
  ★∼Xᵍ (trans (eq X) eq-X)
rename★∼ᵏ ρ eq ★∼∀ = ★∼∀

renameᵏ : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {m A B}
  → (ρ : Δ ⇒ʳ Δ′)
  → (∀ X → μ′ (ρ X) ≡ μ X)
  → μ ⊢ A ∼ᵏ[ m ] B
  → μ′ ⊢ renameᵗ ρ A ∼ᵏ[ m ] renameᵗ ρ B
renameᵏ ρ eq (idᵏ ★) = idᵏ ★
renameᵏ ρ eq (idᵏ (‵ ι)) = idᵏ (‵ ι)
renameᵏ ρ eq (idᵏ (＇ X)) = idᵏ (＇ (ρ X))
renameᵏ ρ eq (c ↦ᵏ d) = renameᵏ ρ eq c ↦ᵏ renameᵏ ρ eq d
renameᵏ ρ eq (∀ᵏ c) =
  ∀ᵏ (renameᵏ (extᵗ ρ) (extᵐ-renameᵏ ρ eq) c)
renameᵏ ρ eq (_!ᵏ ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄) =
  _!ᵏ ⦃ renameGroundᵏ ρ Gᵍ ⦄ ⦃ rename∼★ᵏ ρ eq G∼★ ⦄
    (renameᵏ ρ eq c) ⦃ C.renameNonStar ρ Ans ⦄
renameᵏ ρ eq (？ᵏ_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) =
  ？ᵏ_ ⦃ renameGroundᵏ ρ Gᵍ ⦄ ⦃ rename★∼ᵏ ρ eq ★∼G ⦄
    (renameᵏ ρ eq c) ⦃ C.renameNonStar ρ Bns ⦄
renameᵏ ρ eq
    (instᵏ_ {B = B} ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) =
  instᵏ_ ⦃ renameNonVar (extᵗ ρ) Anv ⦄
    ⦃ rename-∈ᵗ (extᵗ ρ) z∈A ⦄
    (subst-right-∼ᵏ (renameᵗ-shift ρ B)
      (renameᵏ (extᵗ ρ) (instᵐ-renameᵏ ρ eq) c))
    (rename-≢★ ρ B≢★)
renameᵏ ρ eq
    (genᵏ_ {A = A} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) =
  genᵏ_ ⦃ renameNonVar (extᵗ ρ) Bnv ⦄
    ⦃ rename-∈ᵗ (extᵗ ρ) z∈B ⦄
    (subst-left-∼ᵏ (renameᵗ-shift ρ A)
      (renameᵏ (extᵗ ρ) (genᵐ-renameᵏ ρ eq) c))
    (rename-≢★ ρ A≢★)
renameᵏ ρ eq bot-elimᵏ = bot-elimᵏ
renameᵏ ρ eq bot-introᵏ = bot-introᵏ

consistency-var-self-not-from-star : X∼X ≡ ★∼X → ⊥
consistency-var-self-not-from-star ()

ground-self-occurs-from⊥ : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
    {X : TyVar Δ} {G : Ty Δ}
  → ν X ≡ X∼X
  → ν ⊢★∼ G
  → X ∈ᵗ G
  → ⊥
ground-self-occurs-from⊥ same ★∼⇒ (∈-fun-left ())
ground-self-occurs-from⊥ same ★∼⇒ (∈-fun-right X∉A ())
ground-self-occurs-from⊥ same ★∼ι ()
ground-self-occurs-from⊥ same (★∼Xᵍ eq) var-∈ =
  consistency-var-self-not-from-star (trans (sym same) eq)
ground-self-occurs-from⊥ same ★∼∀ (∈-all ())

consistency-var-to-star-not-from-star : X∼★ ≡ ★∼X → ⊥
consistency-var-to-star-not-from-star ()

consistency-var-from-star-not-to-star : ★∼X ≡ X∼★ → ⊥
consistency-var-from-star-not-to-star ()

ground-from-star-occurs-to⊥ : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
    {X : TyVar Δ} {G : Ty Δ}
  → ν X ≡ X∼★
  → ν ⊢★∼ G
  → X ∈ᵗ G
  → ⊥
ground-from-star-occurs-to⊥ same ★∼⇒ (∈-fun-left ())
ground-from-star-occurs-to⊥ same ★∼⇒ (∈-fun-right X∉A ())
ground-from-star-occurs-to⊥ same ★∼ι ()
ground-from-star-occurs-to⊥ same (★∼Xᵍ eq) var-∈ =
  consistency-var-to-star-not-from-star (trans (sym same) eq)
ground-from-star-occurs-to⊥ same ★∼∀ (∈-all ())

ground-to-star-occurs-from⊥ : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
    {X : TyVar Δ} {G : Ty Δ}
  → ν X ≡ ★∼X
  → ν ⊢ G ∼★
  → X ∈ᵗ G
  → ⊥
ground-to-star-occurs-from⊥ same ⇒∼★ (∈-fun-left ())
ground-to-star-occurs-from⊥ same ⇒∼★ (∈-fun-right X∉A ())
ground-to-star-occurs-from⊥ same ι∼★ ()
ground-to-star-occurs-from⊥ same (X∼★ᵍ eq) var-∈ =
  consistency-var-from-star-not-to-star (trans (sym same) eq)
ground-to-star-occurs-from⊥ same ∀∼★ (∈-all ())

ground-occurs-forces-to-starᵏ : ∀ {Δ : TyCtx} {μ : Env∼ Δ}
    {X : TyVar Δ} {G : Ty Δ}
  → μ ⊢ G ∼★
  → X ∈ᵗ G
  → μ X ≡ X∼★
ground-occurs-forces-to-starᵏ ⇒∼★ (∈-fun-left ())
ground-occurs-forces-to-starᵏ ⇒∼★ (∈-fun-right X∉A ())
ground-occurs-forces-to-starᵏ ι∼★ ()
ground-occurs-forces-to-starᵏ (X∼★ᵍ eq) var-∈ = eq
ground-occurs-forces-to-starᵏ ∀∼★ (∈-all ())

ground-occurs-forces-from-starᵏ : ∀ {Δ : TyCtx} {μ : Env∼ Δ}
    {X : TyVar Δ} {G : Ty Δ}
  → μ ⊢★∼ G
  → X ∈ᵗ G
  → μ X ≡ ★∼X
ground-occurs-forces-from-starᵏ ★∼⇒ (∈-fun-left ())
ground-occurs-forces-from-starᵏ ★∼⇒ (∈-fun-right X∉A ())
ground-occurs-forces-from-starᵏ ★∼ι ()
ground-occurs-forces-from-starᵏ (★∼Xᵍ eq) var-∈ = eq
ground-occurs-forces-from-starᵏ ★∼∀ (∈-all ())

flip-self : ∀ {Δ} {μ : Env∼ Δ} {X}
  → μ X ≡ X∼X
  → C.flipᵐ μ X ≡ X∼X
flip-self {μ = μ} {X = X} same with μ X
flip-self same | X∼X = refl
flip-self () | X∼★
flip-self () | ★∼X

source-path-self : ∀ {Δ} {μ : Env∼ Δ} {m X A B}
  → μ X ≡ X∼X
  → μ ⊢ A ∼ᵏ[ m ] B
  → X ∈ᵗ A
  → OccPath X A B
target-path-self : ∀ {Δ} {μ : Env∼ Δ} {m X A B}
  → μ X ≡ X∼X
  → μ ⊢ A ∼ᵏ[ m ] B
  → X ∈ᵗ B
  → OccPath X A B

source-path-self same (idᵏ (＇ X)) var-∈ = op-var
source-path-self same (idᵏ (‵ ι)) ()
source-path-self same (idᵏ ★) ()
source-path-self same (c ↦ᵏ d) (∈-fun-left X∈A) =
  op-fun-left (source-path-self same c X∈A)
source-path-self {X = X} same (c ↦ᵏ d) (∈-fun-right X∉A X∈B) =
  op-fun-right (source-path-self same d X∈B)
source-path-self same (∀ᵏ c) (∈-all X∈A) =
  op-all (source-path-self same c X∈A)
source-path-self same
    (_!ᵏ ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans ⦄) X∈A =
  ⊥-elim
    (ground-self-occurs⊥ same G∼★
      (consistency-source-occurs-target same (forgetᵏ c) X∈A))
source-path-self same (？ᵏ_ c ⦃ Bns ⦄) ()
source-path-self same (instᵏ_ c B≢★) (∈-all X∈A) =
  op-inst (source-path-self same c X∈A)
source-path-self same (genᵏ_ c A≢★) X∈A =
  op-gen (source-path-self same c (shift-occurs X∈A))
source-path-self same bot-elimᵏ (∈-all ())
source-path-self same bot-introᵏ (∈-all ())

target-path-self same (idᵏ (＇ X)) var-∈ = op-var
target-path-self same (idᵏ (‵ ι)) ()
target-path-self same (idᵏ ★) ()
target-path-self same (c ↦ᵏ d) (∈-fun-left X∈A) =
  op-fun-left (target-path-self same c X∈A)
target-path-self {X = X} same (c ↦ᵏ d) (∈-fun-right X∉A X∈B) =
  op-fun-right (target-path-self same d X∈B)
target-path-self same (∀ᵏ c) (∈-all X∈B) =
  op-all (target-path-self same c X∈B)
target-path-self same (_!ᵏ c ⦃ Ans ⦄) ()
target-path-self {μ = μ} {X = X} same
    (？ᵏ_ ⦃ ★∼G = ★∼G ⦄ c ⦃ Bns ⦄) X∈B =
  ⊥-elim
    (ground-self-occurs-from⊥ same ★∼G
      (consistency-source-occurs-target {ν = C.flipᵐ μ} {X = X}
        (flip-self {μ = μ} {X = X} same)
        (C.sym∼ (forgetᵏ c)) X∈B))
target-path-self same (instᵏ_ c B≢★) X∈B =
  op-inst (target-path-self same c (shift-occurs X∈B))
target-path-self same (genᵏ_ c A≢★) (∈-all X∈B) =
  op-gen (target-path-self same c X∈B)
target-path-self same bot-elimᵏ (∈-all ())
target-path-self same bot-introᵏ (∈-all ())

target-occurs-source-to-starᵏ : ∀ {Δ} {μ : Env∼ Δ}
    {m X A B}
  → μ X ≡ X∼★
  → μ ⊢ A ∼ᵏ[ m ] B
  → X ∈ᵗ B
  → X ∈ᵗ A
source-occurs-target-from-starᵏ : ∀ {Δ} {μ : Env∼ Δ}
    {m X A B}
  → μ X ≡ ★∼X
  → μ ⊢ A ∼ᵏ[ m ] B
  → X ∈ᵗ A
  → X ∈ᵗ B

target-occurs-source-to-starᵏ same (idᵏ (＇ X)) var-∈ = var-∈
target-occurs-source-to-starᵏ same (idᵏ (‵ ι)) ()
target-occurs-source-to-starᵏ same (idᵏ ★) ()
target-occurs-source-to-starᵏ same (c ↦ᵏ d) (∈-fun-left X∈A) =
  ∈-fun-left (target-occurs-source-to-starᵏ same c X∈A)
target-occurs-source-to-starᵏ {X = X} same (c ↦ᵏ d)
    (∈-fun-right X∉A X∈B)
    with occurs? X _
target-occurs-source-to-starᵏ {X = X} same (c ↦ᵏ d)
    (∈-fun-right X∉A X∈B)
    | present X∈A′ =
  ∈-fun-left X∈A′
target-occurs-source-to-starᵏ {X = X} same (c ↦ᵏ d)
    (∈-fun-right X∉A X∈B)
    | absent X∉A′ =
  ∈-fun-right X∉A′ (target-occurs-source-to-starᵏ same d X∈B)
target-occurs-source-to-starᵏ same (∀ᵏ c) (∈-all X∈B) =
  ∈-all (target-occurs-source-to-starᵏ same c X∈B)
target-occurs-source-to-starᵏ same (_!ᵏ c ⦃ Ans ⦄) ()
target-occurs-source-to-starᵏ {X = X} same
    (？ᵏ_ ⦃ ★∼G = ★∼G ⦄ c ⦃ Bns ⦄) X∈B =
  ⊥-elim
    (ground-from-star-occurs-to⊥ same ★∼G
      (target-occurs-source-to-starᵏ same c X∈B))
target-occurs-source-to-starᵏ same (instᵏ_ c B≢★) X∈B =
  ∈-all (target-occurs-source-to-starᵏ same c
    (shift-occurs X∈B))
target-occurs-source-to-starᵏ same (genᵏ_ c A≢★) (∈-all X∈B) =
  unshift-occurs (target-occurs-source-to-starᵏ same c X∈B)
target-occurs-source-to-starᵏ same bot-elimᵏ (∈-all ())
target-occurs-source-to-starᵏ same bot-introᵏ (∈-all ())

source-occurs-target-from-starᵏ same (idᵏ (＇ X)) var-∈ = var-∈
source-occurs-target-from-starᵏ same (idᵏ (‵ ι)) ()
source-occurs-target-from-starᵏ same (idᵏ ★) ()
source-occurs-target-from-starᵏ same (c ↦ᵏ d) (∈-fun-left X∈A) =
  ∈-fun-left (source-occurs-target-from-starᵏ same c X∈A)
source-occurs-target-from-starᵏ {X = X} same (c ↦ᵏ d)
    (∈-fun-right X∉A X∈B)
    with occurs? X _
source-occurs-target-from-starᵏ {X = X} same (c ↦ᵏ d)
    (∈-fun-right X∉A X∈B)
    | present X∈A′ =
  ∈-fun-left X∈A′
source-occurs-target-from-starᵏ {X = X} same (c ↦ᵏ d)
    (∈-fun-right X∉A X∈B)
    | absent X∉A′ =
  ∈-fun-right X∉A′ (source-occurs-target-from-starᵏ same d X∈B)
source-occurs-target-from-starᵏ same (∀ᵏ c) (∈-all X∈A) =
  ∈-all (source-occurs-target-from-starᵏ same c X∈A)
source-occurs-target-from-starᵏ {X = X} same
    (_!ᵏ ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans ⦄) X∈A =
  ⊥-elim
    (ground-to-star-occurs-from⊥ same G∼★
      (source-occurs-target-from-starᵏ same c X∈A))
source-occurs-target-from-starᵏ same (？ᵏ_ c ⦃ Bns ⦄) ()
source-occurs-target-from-starᵏ same (instᵏ_ c B≢★)
    (∈-all X∈A) =
  unshift-occurs (source-occurs-target-from-starᵏ same c X∈A)
source-occurs-target-from-starᵏ same (genᵏ_ c A≢★) X∈A =
  ∈-all (source-occurs-target-from-starᵏ same c
    (shift-occurs X∈A))
source-occurs-target-from-starᵏ same bot-elimᵏ (∈-all ())
source-occurs-target-from-starᵏ same bot-introᵏ (∈-all ())

source-absent-target-to-starᵏ : ∀ {Δ} {μ : Env∼ Δ}
    {m X A B}
  → μ X ≡ X∼★
  → μ ⊢ A ∼ᵏ[ m ] B
  → X ∉ᵗ A
  → Fresh X B
source-absent-target-to-starᵏ same c X∉A X∈B =
  not-occurs X∉A (target-occurs-source-to-starᵏ same c X∈B)

target-absent-source-from-starᵏ : ∀ {Δ} {μ : Env∼ Δ}
    {m X A B}
  → μ X ≡ ★∼X
  → μ ⊢ A ∼ᵏ[ m ] B
  → X ∉ᵗ B
  → Fresh X A
target-absent-source-from-starᵏ same c X∉B X∈A =
  not-occurs X∉B (source-occurs-target-from-starᵏ same c X∈A)

target-occurs-source-not-from-starᵏ : ∀ {Δ} {μ : Env∼ Δ}
    {m X A B}
  → μ X ≢ ★∼X
  → μ ⊢ A ∼ᵏ[ m ] B
  → X ∈ᵗ B
  → X ∈ᵗ A
source-occurs-target-not-to-starᵏ : ∀ {Δ} {μ : Env∼ Δ}
    {m X A B}
  → μ X ≢ X∼★
  → μ ⊢ A ∼ᵏ[ m ] B
  → X ∈ᵗ A
  → X ∈ᵗ B

target-occurs-source-not-from-starᵏ not-from (idᵏ (＇ X)) var-∈ =
  var-∈
target-occurs-source-not-from-starᵏ not-from (idᵏ (‵ ι)) ()
target-occurs-source-not-from-starᵏ not-from (idᵏ ★) ()
target-occurs-source-not-from-starᵏ not-from (c ↦ᵏ d)
    (∈-fun-left X∈A) =
  ∈-fun-left (target-occurs-source-not-from-starᵏ not-from c X∈A)
target-occurs-source-not-from-starᵏ {X = X} not-from (c ↦ᵏ d)
    (∈-fun-right X∉A X∈B)
    with occurs? X _
target-occurs-source-not-from-starᵏ {X = X} not-from (c ↦ᵏ d)
    (∈-fun-right X∉A X∈B)
    | present X∈A′ =
  ∈-fun-left X∈A′
target-occurs-source-not-from-starᵏ {X = X} not-from (c ↦ᵏ d)
    (∈-fun-right X∉A X∈B)
    | absent X∉A′ =
  ∈-fun-right X∉A′
    (target-occurs-source-not-from-starᵏ not-from d X∈B)
target-occurs-source-not-from-starᵏ not-from (∀ᵏ c) (∈-all X∈B) =
  ∈-all (target-occurs-source-not-from-starᵏ not-from c X∈B)
target-occurs-source-not-from-starᵏ not-from (_!ᵏ c ⦃ Ans ⦄) ()
target-occurs-source-not-from-starᵏ not-from
    (？ᵏ_ ⦃ ★∼G = ★∼G ⦄ c ⦃ Bns ⦄) X∈B =
  ⊥-elim (not-from (ground-occurs-forces-from-starᵏ ★∼G
    (target-occurs-source-not-from-starᵏ not-from c X∈B)))
target-occurs-source-not-from-starᵏ not-from (instᵏ_ c B≢★) X∈B =
  ∈-all
    (target-occurs-source-not-from-starᵏ not-from c
      (shift-occurs X∈B))
target-occurs-source-not-from-starᵏ not-from (genᵏ_ c A≢★)
    (∈-all X∈B) =
  unshift-occurs (target-occurs-source-not-from-starᵏ not-from c X∈B)
target-occurs-source-not-from-starᵏ not-from bot-elimᵏ (∈-all ())
target-occurs-source-not-from-starᵏ not-from bot-introᵏ (∈-all ())

source-occurs-target-not-to-starᵏ not-to (idᵏ (＇ X)) var-∈ = var-∈
source-occurs-target-not-to-starᵏ not-to (idᵏ (‵ ι)) ()
source-occurs-target-not-to-starᵏ not-to (idᵏ ★) ()
source-occurs-target-not-to-starᵏ not-to (c ↦ᵏ d) (∈-fun-left X∈A) =
  ∈-fun-left (source-occurs-target-not-to-starᵏ not-to c X∈A)
source-occurs-target-not-to-starᵏ {X = X} not-to (c ↦ᵏ d)
    (∈-fun-right X∉A X∈B)
    with occurs? X _
source-occurs-target-not-to-starᵏ {X = X} not-to (c ↦ᵏ d)
    (∈-fun-right X∉A X∈B)
    | present X∈A′ =
  ∈-fun-left X∈A′
source-occurs-target-not-to-starᵏ {X = X} not-to (c ↦ᵏ d)
    (∈-fun-right X∉A X∈B)
    | absent X∉A′ =
  ∈-fun-right X∉A′
    (source-occurs-target-not-to-starᵏ not-to d X∈B)
source-occurs-target-not-to-starᵏ not-to (∀ᵏ c) (∈-all X∈A) =
  ∈-all (source-occurs-target-not-to-starᵏ not-to c X∈A)
source-occurs-target-not-to-starᵏ not-to
    (_!ᵏ ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans ⦄) X∈A =
  ⊥-elim (not-to (ground-occurs-forces-to-starᵏ G∼★
    (source-occurs-target-not-to-starᵏ not-to c X∈A)))
source-occurs-target-not-to-starᵏ not-to (？ᵏ_ c ⦃ Bns ⦄) ()
source-occurs-target-not-to-starᵏ not-to (instᵏ_ c B≢★)
    (∈-all X∈A) =
  unshift-occurs (source-occurs-target-not-to-starᵏ not-to c X∈A)
source-occurs-target-not-to-starᵏ not-to (genᵏ_ c A≢★) X∈A =
  ∈-all
    (source-occurs-target-not-to-starᵏ not-to c
      (shift-occurs X∈A))
source-occurs-target-not-to-starᵏ not-to bot-elimᵏ (∈-all ())
source-occurs-target-not-to-starᵏ not-to bot-introᵏ (∈-all ())

nonvar-occurs-nonstar : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
  → NonVar A
  → X ∈ᵗ A
  → NonStar A
nonvar-occurs-nonstar nonvar-base ()
nonvar-occurs-nonstar nonvar-star ()
nonvar-occurs-nonstar nonvar-fun X∈A = nonstar-⇒
nonvar-occurs-nonstar nonvar-all X∈A = nonstar-∀

to-var-nonstar-nonvar⊥ : ∀ {Δ} {μ : Env∼ Δ} {m X B}
  → μ X ≡ X∼★
  → μ ⊢ ＇ X ∼ᵏ[ m ] B
  → NonVar B
  → NonStar B
  → ⊥
to-var-nonstar-nonvar⊥ to (idᵏ (＇ X)) ()
to-var-nonstar-nonvar⊥ to (_!ᵏ c ⦃ Ans ⦄) nonvar-star ()
to-var-nonstar-nonvar⊥ {X = X} to
    (genᵏ_ ⦃ Bnv = Bnv ⦄ ⦃ z∈B = z∈B ⦄ c A≢★)
    nonvar-all Bns =
  to-var-nonstar-nonvar⊥ {X = suc X} to c Bnv
    (nonvar-occurs-nonstar Bnv z∈B)

from-nonstar-nonvar-to-var⊥ : ∀ {Δ} {μ : Env∼ Δ} {m X A}
  → μ X ≡ ★∼X
  → μ ⊢ A ∼ᵏ[ m ] ＇ X
  → NonVar A
  → NonStar A
  → ⊥
from-nonstar-nonvar-to-var⊥ from (idᵏ (＇ X)) ()
from-nonstar-nonvar-to-var⊥ from (？ᵏ_ c ⦃ Bns ⦄) nonvar-star ()
from-nonstar-nonvar-to-var⊥ {X = X} from
    (instᵏ_ ⦃ Anv = Anv ⦄ ⦃ z∈A = z∈A ⦄ c B≢★)
    nonvar-all Ans =
  from-nonstar-nonvar-to-var⊥ {X = suc X} from c Anv
    (nonvar-occurs-nonstar Anv z∈A)

var-var-eqᵏ : ∀ {Δ} {μ : Env∼ Δ} {m X Y}
  → μ ⊢ ＇ X ∼ᵏ[ m ] ＇ Y
  → X ≡ Y
var-var-eqᵏ (idᵏ (＇ X)) = refl

refl∼ᵏ : ∀ {Δ} {μ : Env∼ Δ} {m} (A : Ty Δ) → μ ⊢ A ∼ᵏ[ m ] A
refl∼ᵏ (＇ X) = idᵏ (＇ X)
refl∼ᵏ (‵ ι) = idᵏ (‵ ι)
refl∼ᵏ ★ = idᵏ ★
refl∼ᵏ (A ⇒ B) = refl∼ᵏ A ↦ᵏ refl∼ᵏ B
refl∼ᵏ (`∀ A) = ∀ᵏ (refl∼ᵏ A)

record SubstEnv∼ᵏ {Δ Δ′ : TyCtx}
    (μ : Env∼ Δ) (ν : Env∼ Δ′) (σ : Δ ⇒ˢ Δ′) : Set where
  constructor subst-env∼ᵏ
  field
    self : ∀ {m} X → ν ⊢ σ X ∼ᵏ[ m ] σ X
    to-★ : ∀ {m} X → μ X ≡ X∼★ → ν ⊢ σ X ∼ᵏ[ m ] ★
    from-★ : ∀ {m} X → μ X ≡ ★∼X → ν ⊢ ★ ∼ᵏ[ m ] σ X

open SubstEnv∼ᵏ

private

  ext-SubstEnv∼ᵏ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′}
    → SubstEnv∼ᵏ μ ν σ
    → SubstEnv∼ᵏ (extᵐ μ) (extᵐ ν) (extsᵗ σ)
  ext-SubstEnv∼ᵏ (subst-env∼ᵏ self to-★ from-★) =
    subst-env∼ᵏ self′ to-★′ from-★′
    where
    self′ : ∀ {m} X → extᵐ _ ⊢ extsᵗ _ X ∼ᵏ[ m ] extsᵗ _ X
    self′ zero = idᵏ (＇ zero)
    self′ (suc X) = renameᵏ suc (λ Y → refl) (self X)

    to-★′ : ∀ {m} X
      → extᵐ _ X ≡ X∼★
      → extᵐ _ ⊢ extsᵗ _ X ∼ᵏ[ m ] ★
    to-★′ zero ()
    to-★′ (suc X) eq = renameᵏ suc (λ Y → refl) (to-★ X eq)

    from-★′ : ∀ {m} X
      → extᵐ _ X ≡ ★∼X
      → extᵐ _ ⊢ ★ ∼ᵏ[ m ] extsᵗ _ X
    from-★′ zero ()
    from-★′ (suc X) eq = renameᵏ suc (λ Y → refl) (from-★ X eq)

  inst-SubstEnv∼ᵏ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′}
    → SubstEnv∼ᵏ μ ν σ
    → SubstEnv∼ᵏ (instᵐ μ) (instᵐ ν) (extsᵗ σ)
  inst-SubstEnv∼ᵏ {ν = ν} (subst-env∼ᵏ self to-★ from-★) =
    subst-env∼ᵏ self′ to-★′ from-★′
    where
    self′ : ∀ {m} X → instᵐ _ ⊢ extsᵗ _ X ∼ᵏ[ m ] extsᵗ _ X
    self′ zero = idᵏ (＇ zero)
    self′ (suc X) = renameᵏ suc (λ Y → refl) (self X)

    to-★′ : ∀ {m} X
      → instᵐ _ X ≡ X∼★
      → instᵐ _ ⊢ extsᵗ _ X ∼ᵏ[ m ] ★
    to-★′ zero eq =
      _!ᵏ ⦃ G∼★ = X∼★ᵍ refl ⦄ (idᵏ (＇ zero))
        ⦃ nonstar-X ⦄
    to-★′ (suc X) eq = renameᵏ suc (λ Y → refl) (to-★ X eq)

    from-★′ : ∀ {m} X
      → instᵐ _ X ≡ ★∼X
      → instᵐ _ ⊢ ★ ∼ᵏ[ m ] extsᵗ _ X
    from-★′ zero ()
    from-★′ (suc X) eq = renameᵏ suc (λ Y → refl) (from-★ X eq)

  gen-SubstEnv∼ᵏ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′}
    → SubstEnv∼ᵏ μ ν σ
    → SubstEnv∼ᵏ (genᵐ μ) (genᵐ ν) (extsᵗ σ)
  gen-SubstEnv∼ᵏ {ν = ν} (subst-env∼ᵏ self to-★ from-★) =
    subst-env∼ᵏ self′ to-★′ from-★′
    where
    self′ : ∀ {m} X → genᵐ _ ⊢ extsᵗ _ X ∼ᵏ[ m ] extsᵗ _ X
    self′ zero = idᵏ (＇ zero)
    self′ (suc X) = renameᵏ suc (λ Y → refl) (self X)

    to-★′ : ∀ {m} X
      → genᵐ _ X ≡ X∼★
      → genᵐ _ ⊢ extsᵗ _ X ∼ᵏ[ m ] ★
    to-★′ zero ()
    to-★′ (suc X) eq = renameᵏ suc (λ Y → refl) (to-★ X eq)

    from-★′ : ∀ {m} X
      → genᵐ _ X ≡ ★∼X
      → genᵐ _ ⊢ ★ ∼ᵏ[ m ] extsᵗ _ X
    from-★′ zero eq =
      ？ᵏ_ ⦃ ★∼G = ★∼Xᵍ refl ⦄ (idᵏ (＇ zero))
        ⦃ nonstar-X ⦄
    from-★′ (suc X) eq = renameᵏ suc (λ Y → refl) (from-★ X eq)

  subst-∈ᵗ : ∀ {Δ Δ′} {σ : Δ ⇒ˢ Δ′} {X : TyVar Δ}
      {Y : TyVar Δ′} {A : Ty Δ}
    → X ∈ᵗ A
    → Y ∈ᵗ σ X
    → Y ∈ᵗ substᵗ σ A
  subst-∈ᵗ var-∈ Y∈σX = Y∈σX
  subst-∈ᵗ (∈-fun-left X∈A) Y∈σX =
    ∈-fun-left (subst-∈ᵗ X∈A Y∈σX)
  subst-∈ᵗ {σ = σ} {Y = Y} {A = A ⇒ B}
      (∈-fun-right X∉A X∈B) Y∈σX
      with occurs? Y (substᵗ σ A)
  subst-∈ᵗ {σ = σ} {Y = Y} {A = A ⇒ B}
      (∈-fun-right X∉A X∈B) Y∈σX
      | present Y∈A =
    ∈-fun-left Y∈A
  subst-∈ᵗ {σ = σ} {Y = Y} {A = A ⇒ B}
      (∈-fun-right X∉A X∈B) Y∈σX
      | absent Y∉A =
    ∈-fun-right Y∉A (subst-∈ᵗ X∈B Y∈σX)
  subst-∈ᵗ {σ = σ} (∈-all X∈A) Y∈σX =
    ∈-all (subst-∈ᵗ {σ = extsᵗ σ} X∈A
      (rename-∈ᵗ suc Y∈σX))

  tag-source-nonvar-⇒ᵏ : ∀ {Δ} {μ : Env∼ Δ} {m A}
    → μ ⊢ A ∼ᵏ[ m ] (★ ⇒ ★)
    → NonStar A
    → NonVar A
  tag-source-nonvar-⇒ᵏ (c ↦ᵏ d) Ans = nonvar-fun
  tag-source-nonvar-⇒ᵏ (？ᵏ_ ⦃ g ⦄ c ⦃ Gns ⦄) Ans =
    ⊥-elim (nonStar≢★ Ans refl)
  tag-source-nonvar-⇒ᵏ (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★)
      Ans =
    nonvar-all

  tag-source-nonvar-ιᵏ : ∀ {Δ} {μ : Env∼ Δ} {m A ι}
    → μ ⊢ A ∼ᵏ[ m ] (‵ ι)
    → NonStar A
    → NonVar A
  tag-source-nonvar-ιᵏ (idᵏ (‵ ι)) Ans = nonvar-base
  tag-source-nonvar-ιᵏ (？ᵏ_ ⦃ g ⦄ c ⦃ Gns ⦄) Ans =
    ⊥-elim (nonStar≢★ Ans refl)
  tag-source-nonvar-ιᵏ (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★)
      Ans =
    nonvar-all

  tag-source-nonvar-∀ᵏ : ∀ {Δ} {μ : Env∼ Δ} {m A}
    → μ ⊢ A ∼ᵏ[ m ] (`∀ ★)
    → NonStar A
    → NonVar A
  tag-source-nonvar-∀ᵏ (∀ᵏ c) Ans = nonvar-all
  tag-source-nonvar-∀ᵏ (？ᵏ_ ⦃ g ⦄ c ⦃ Gns ⦄) Ans =
    ⊥-elim (nonStar≢★ Ans refl)
  tag-source-nonvar-∀ᵏ (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★)
      Ans =
    nonvar-all
  tag-source-nonvar-∀ᵏ bot-elimᵏ Ans = nonvar-all

  untag-target-nonvar-⇒ᵏ : ∀ {Δ} {μ : Env∼ Δ} {m B}
    → μ ⊢ (★ ⇒ ★) ∼ᵏ[ m ] B
    → NonStar B
    → NonVar B
  untag-target-nonvar-⇒ᵏ (c ↦ᵏ d) Bns = nonvar-fun
  untag-target-nonvar-⇒ᵏ (_!ᵏ ⦃ g ⦄ c ⦃ Gns ⦄) Bns =
    ⊥-elim (nonStar≢★ Bns refl)
  untag-target-nonvar-⇒ᵏ (genᵏ_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★)
      Bns =
    nonvar-all

  untag-target-nonvar-ιᵏ : ∀ {Δ} {μ : Env∼ Δ} {m B ι}
    → μ ⊢ (‵ ι) ∼ᵏ[ m ] B
    → NonStar B
    → NonVar B
  untag-target-nonvar-ιᵏ (idᵏ (‵ ι)) Bns = nonvar-base
  untag-target-nonvar-ιᵏ (_!ᵏ ⦃ g ⦄ c ⦃ Gns ⦄) Bns =
    ⊥-elim (nonStar≢★ Bns refl)
  untag-target-nonvar-ιᵏ (genᵏ_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★)
      Bns =
    nonvar-all

  untag-target-nonvar-∀ᵏ : ∀ {Δ} {μ : Env∼ Δ} {m B}
    → μ ⊢ (`∀ ★) ∼ᵏ[ m ] B
    → NonStar B
    → NonVar B
  untag-target-nonvar-∀ᵏ (∀ᵏ c) Bns = nonvar-all
  untag-target-nonvar-∀ᵏ (_!ᵏ ⦃ g ⦄ c ⦃ Gns ⦄) Bns =
    ⊥-elim (nonStar≢★ Bns refl)
  untag-target-nonvar-∀ᵏ (genᵏ_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★)
      Bns =
    nonvar-all
  untag-target-nonvar-∀ᵏ bot-introᵏ Bns = nonvar-all

  nonstar-nonvar-to-var-impossibleᵏ : ∀ {Δ} {μ : Env∼ Δ}
      {m} {A : Ty Δ} {X}
    → μ ⊢ A ∼ᵏ[ m ] ＇ X
    → NonVar A
    → NonStar A
    → ⊥
  nonstar-nonvar-to-var-impossibleᵏ (idᵏ (＇ X)) () Ans
  nonstar-nonvar-to-var-impossibleᵏ (？ᵏ_ c ⦃ Bns ⦄)
      nonvar-star ()
  nonstar-nonvar-to-var-impossibleᵏ
      (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) nonvar-all Ans =
    nonstar-nonvar-to-var-impossibleᵏ c Anv
      (nonvar-occurs-nonstar Anv z∈A)

  var-to-nonstar-nonvar-impossibleᵏ : ∀ {Δ} {μ : Env∼ Δ}
      {m} {B : Ty Δ} {X}
    → μ ⊢ ＇ X ∼ᵏ[ m ] B
    → NonVar B
    → NonStar B
    → ⊥
  var-to-nonstar-nonvar-impossibleᵏ (idᵏ (＇ X)) () Bns
  var-to-nonstar-nonvar-impossibleᵏ (_!ᵏ c ⦃ Ans ⦄)
      nonvar-star ()
  var-to-nonstar-nonvar-impossibleᵏ
      (genᵏ_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) nonvar-all Bns =
    var-to-nonstar-nonvar-impossibleᵏ c Bnv
      (nonvar-occurs-nonstar Bnv z∈B)

  subst-to-star-varᵏ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′} {m} {A : Ty Δ} {X}
    → SubstEnv∼ᵏ μ ν σ
    → μ ⊢ A ∼ᵏ[ gen-ok ] ＇ X
    → μ X ≡ X∼★
    → NonStar A
    → ν ⊢ substᵗ σ A ∼ᵏ[ m ] ★
  subst-to-star-varᵏ s (idᵏ (＇ X)) eq Ans = to-★ s X eq
  subst-to-star-varᵏ s (？ᵏ_ c ⦃ Bns ⦄) eq ()
  subst-to-star-varᵏ s c@(instᵏ_ ⦃ Anv ⦄ d B≢★) eq Ans =
    ⊥-elim (nonstar-nonvar-to-var-impossibleᵏ c nonvar-all Ans)

  subst-from-star-varᵏ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′} {m} {B : Ty Δ} {X}
    → SubstEnv∼ᵏ μ ν σ
    → μ ⊢ ＇ X ∼ᵏ[ gen-ok ] B
    → μ X ≡ ★∼X
    → NonStar B
    → ν ⊢ ★ ∼ᵏ[ m ] substᵗ σ B
  subst-from-star-varᵏ s (idᵏ (＇ X)) eq Bns = from-★ s X eq
  subst-from-star-varᵏ s (_!ᵏ c ⦃ Ans ⦄) eq ()
  subst-from-star-varᵏ s c@(genᵏ_ ⦃ Bnv ⦄ d A≢★) eq Bns =
    ⊥-elim (var-to-nonstar-nonvar-impossibleᵏ c nonvar-all Bns)

  subst-nonvar-nonstar : ∀ {Δ Δ′} {A : Ty Δ}
    → (σ : Δ ⇒ˢ Δ′)
    → NonVar A
    → NonStar A
    → NonStar (substᵗ σ A)
  subst-nonvar-nonstar σ nonvar-base Ans = nonstar-ι
  subst-nonvar-nonstar σ nonvar-star ()
  subst-nonvar-nonstar σ nonvar-fun Ans = nonstar-⇒
  subst-nonvar-nonstar σ nonvar-all Ans = nonstar-∀

  inst-to-var-occurs-impossibleᵏ : ∀ {Δ} {μ : Env∼ Δ}
      {m} {A : Ty (Nat.suc Δ)} {X}
    → instᵐ μ ⊢ A ∼ᵏ[ m ] ＇ X
    → instᵐ μ X ≡ X∼★
    → NonVar A
    → X ∈ᵗ A
    → ⊥
  inst-to-var-occurs-impossibleᵏ (idᵏ (＇ X)) eq () X∈A
  inst-to-var-occurs-impossibleᵏ (？ᵏ_ ⦃ g ⦄ c ⦃ Bns ⦄)
      eq nonvar-star ()
  inst-to-var-occurs-impossibleᵏ
      (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) eq nonvar-all
      (∈-all X∈A) =
    inst-to-var-occurs-impossibleᵏ c eq Anv X∈A

  gen-from-var-occurs-impossibleᵏ : ∀ {Δ} {μ : Env∼ Δ}
      {m} {B : Ty (Nat.suc Δ)} {X}
    → genᵐ μ ⊢ ＇ X ∼ᵏ[ m ] B
    → genᵐ μ X ≡ ★∼X
    → NonVar B
    → X ∈ᵗ B
    → ⊥
  gen-from-var-occurs-impossibleᵏ (idᵏ (＇ X)) eq () X∈B
  gen-from-var-occurs-impossibleᵏ (_!ᵏ ⦃ g ⦄ c ⦃ Ans ⦄)
      eq nonvar-star ()
  gen-from-var-occurs-impossibleᵏ
      (genᵏ_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) eq nonvar-all
      (∈-all X∈B) =
    gen-from-var-occurs-impossibleᵏ c eq Bnv X∈B

  block-ground-targetᵏ : ∀ {Δ} {μ : Env∼ Δ} {A G : Ty Δ}
    → Ground G
    → μ ⊢ A ∼ᵏ[ gen-ok ] G
    → μ ⊢ A ∼ᵏ[ gen-blocked ] G
  block-ground-targetᵏ ★⇒★ (c ↦ᵏ d) = c ↦ᵏ d
  block-ground-targetᵏ ★⇒★
      (？ᵏ_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) =
    ？ᵏ_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄
  block-ground-targetᵏ ★⇒★
      (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) =
    instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★
  block-ground-targetᵏ (‵ ι) (idᵏ (‵ ι)) = idᵏ (‵ ι)
  block-ground-targetᵏ (‵ ι)
      (？ᵏ_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) =
    ？ᵏ_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄
  block-ground-targetᵏ (‵ ι)
      (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) =
    instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★
  block-ground-targetᵏ (＇ X) (idᵏ (＇ X)) = idᵏ (＇ X)
  block-ground-targetᵏ (＇ X)
      (？ᵏ_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) =
    ？ᵏ_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄
  block-ground-targetᵏ (＇ X)
      (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) =
    instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★
  block-ground-targetᵏ ∀★ (∀ᵏ c) = ∀ᵏ c
  block-ground-targetᵏ ∀★
      (？ᵏ_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) =
    ？ᵏ_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄
  block-ground-targetᵏ ∀★
      (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) =
    instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★
  block-ground-targetᵏ ∀★ bot-elimᵏ = bot-elimᵏ

  factor-inst-starᵏ : ∀ {Δ} {μ : Env∼ Δ} {m}
      {A : Ty (Nat.suc Δ)}
    → instᵐ μ ⊢ A ∼ᵏ[ gen-blocked ] ★
    → NonVar A
    → zero ∈ᵗ A
    → μ ⊢ (`∀ A) ∼ᵏ[ m ] ★
  factor-inst-starᵏ (idᵏ ★) Anv ()
  factor-inst-starᵏ (_!ᵏ ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Ans ⦄)
      Anv z∈A =
    _!ᵏ ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄
      (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄
        (block-ground-targetᵏ ★⇒★ c) (λ ())) ⦃ nonstar-∀ ⦄
  factor-inst-starᵏ (_!ᵏ ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Ans ⦄)
      Anv z∈A =
    _!ᵏ ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄
      (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄
        (block-ground-targetᵏ (‵ ι) c) (λ ())) ⦃ nonstar-∀ ⦄
  factor-inst-starᵏ
      (_!ᵏ ⦃ Gᵍ = ＇ zero ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄
        c ⦃ Ans ⦄)
      Anv z∈A =
    ⊥-elim (inst-to-var-occurs-impossibleᵏ c eq Anv z∈A)
  factor-inst-starᵏ
      (_!ᵏ ⦃ Gᵍ = ＇ suc X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄
        c ⦃ Ans ⦄)
      Anv z∈A =
    _!ᵏ ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄
      (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄
        (block-ground-targetᵏ (＇ suc X) c) (λ ()))
      ⦃ nonstar-∀ ⦄
  factor-inst-starᵏ (_!ᵏ ⦃ Gᵍ = ∀★ ⦄ c ⦃ Ans ⦄)
      Anv z∈A =
    _!ᵏ ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄
      (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄
        (block-ground-targetᵏ ∀★ c) (λ ())) ⦃ nonstar-∀ ⦄
  factor-inst-starᵏ (？ᵏ_ ⦃ g ⦄ c ⦃ Bns ⦄) Anv ()
  factor-inst-starᵏ (instᵏ_ ⦃ Anv′ ⦄ ⦃ z∈A′ ⦄ c ★≢★)
      Anv z∈A =
    ⊥-elim (★≢★ refl)

  factor-gen-starᵏ : ∀ {Δ} {μ : Env∼ Δ} {B : Ty (Nat.suc Δ)}
    → genᵐ μ ⊢ ★ ∼ᵏ[ gen-ok ] B
    → NonVar B
    → zero ∈ᵗ B
    → μ ⊢ ★ ∼ᵏ[ gen-ok ] (`∀ B)
  factor-gen-starᵏ (idᵏ ★) Bnv ()
  factor-gen-starᵏ (_!ᵏ ⦃ g ⦄ c ⦃ () ⦄) Bnv z∈B
  factor-gen-starᵏ (？ᵏ_ ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Bns ⦄)
      Bnv z∈B =
    ？ᵏ_ ⦃ Gᵍ = ★⇒★ ⦄ ⦃ ★∼G = ★∼⇒ ⦄
      (genᵏ_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c (λ ())) ⦃ nonstar-∀ ⦄
  factor-gen-starᵏ (？ᵏ_ ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Bns ⦄)
      Bnv z∈B =
    ？ᵏ_ ⦃ Gᵍ = ‵ ι ⦄ ⦃ ★∼G = ★∼ι ⦄
      (genᵏ_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c (λ ())) ⦃ nonstar-∀ ⦄
  factor-gen-starᵏ
      (？ᵏ_ ⦃ Gᵍ = ＇ zero ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄
        c ⦃ Bns ⦄)
      Bnv z∈B =
    ⊥-elim (gen-from-var-occurs-impossibleᵏ c eq Bnv z∈B)
  factor-gen-starᵏ
      (？ᵏ_ ⦃ Gᵍ = ＇ suc X ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄
        c ⦃ Bns ⦄)
      Bnv z∈B =
    ？ᵏ_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄
      (genᵏ_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c (λ ())) ⦃ nonstar-∀ ⦄
  factor-gen-starᵏ (？ᵏ_ ⦃ Gᵍ = ∀★ ⦄ c ⦃ Bns ⦄)
      Bnv z∈B =
    ？ᵏ_ ⦃ Gᵍ = ∀★ ⦄ ⦃ ★∼G = ★∼∀ ⦄
      (genᵏ_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c (λ ())) ⦃ nonstar-∀ ⦄
  factor-gen-starᵏ (genᵏ_ ⦃ Bnv′ ⦄ ⦃ z∈B′ ⦄ c ★≢★)
      Bnv z∈B =
    ⊥-elim (★≢★ refl)

substᵏ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
    {σ : Δ ⇒ˢ Δ′} {m A B}
  → SubstEnv∼ᵏ μ ν σ
  → μ ⊢ A ∼ᵏ[ m ] B
  → ν ⊢ substᵗ σ A ∼ᵏ[ m ] substᵗ σ B
substᵏ s (idᵏ ★) = idᵏ ★
substᵏ s (idᵏ (‵ ι)) = idᵏ (‵ ι)
substᵏ s (idᵏ (＇ X)) = self s X
substᵏ s (c ↦ᵏ d) = substᵏ s c ↦ᵏ substᵏ s d
substᵏ s (∀ᵏ c) = ∀ᵏ (substᵏ (ext-SubstEnv∼ᵏ s) c)
substᵏ {σ = σ} s (_!ᵏ ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Ans ⦄) =
  _!ᵏ ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ (substᵏ s c)
    ⦃ subst-nonvar-nonstar σ (tag-source-nonvar-⇒ᵏ c Ans) Ans ⦄
substᵏ {σ = σ} s (_!ᵏ ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Ans ⦄) =
  _!ᵏ ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄ (substᵏ s c)
    ⦃ subst-nonvar-nonstar σ (tag-source-nonvar-ιᵏ c Ans) Ans ⦄
substᵏ s (_!ᵏ ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄
    c ⦃ Ans ⦄) =
  subst-to-star-varᵏ s c eq Ans
substᵏ {σ = σ} s (_!ᵏ ⦃ Gᵍ = ∀★ ⦄ c ⦃ Ans ⦄) =
  _!ᵏ ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ (substᵏ s c)
    ⦃ subst-nonvar-nonstar σ (tag-source-nonvar-∀ᵏ c Ans) Ans ⦄
substᵏ {σ = σ} s (？ᵏ_ ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Bns ⦄) =
  ？ᵏ_ ⦃ Gᵍ = ★⇒★ ⦄ ⦃ ★∼G = ★∼⇒ ⦄ (substᵏ s c)
    ⦃ subst-nonvar-nonstar σ (untag-target-nonvar-⇒ᵏ c Bns) Bns ⦄
substᵏ {σ = σ} s (？ᵏ_ ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Bns ⦄) =
  ？ᵏ_ ⦃ Gᵍ = ‵ ι ⦄ ⦃ ★∼G = ★∼ι ⦄ (substᵏ s c)
    ⦃ subst-nonvar-nonstar σ (untag-target-nonvar-ιᵏ c Bns) Bns ⦄
substᵏ s (？ᵏ_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄
    c ⦃ Bns ⦄) =
  subst-from-star-varᵏ s c eq Bns
substᵏ {σ = σ} s (？ᵏ_ ⦃ Gᵍ = ∀★ ⦄ c ⦃ Bns ⦄) =
  ？ᵏ_ ⦃ Gᵍ = ∀★ ⦄ ⦃ ★∼G = ★∼∀ ⦄ (substᵏ s c)
    ⦃ subst-nonvar-nonstar σ (untag-target-nonvar-∀ᵏ c Bns) Bns ⦄
substᵏ {σ = σ} s
    (instᵏ_ {B = B} ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★)
    with substᵗ σ B ≟Ty ★
substᵏ {σ = σ} s
    (instᵏ_ {B = B} ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★)
    | no Bσ≢★ =
  instᵏ_ ⦃ substNonVar (extsᵗ σ) Anv ⦄
    ⦃ subst-∈ᵗ z∈A var-∈ ⦄
    (subst-right-∼ᵏ (substᵗ-shift σ B)
      (substᵏ (inst-SubstEnv∼ᵏ s) c)) Bσ≢★
substᵏ {σ = σ} s
    (instᵏ_ {B = B} ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★)
    | yes Bσ≡★ rewrite Bσ≡★ =
  factor-inst-starᵏ
    (subst-right-∼ᵏ
      (trans (substᵗ-shift σ B) (cong (renameᵗ suc) Bσ≡★))
      (substᵏ (inst-SubstEnv∼ᵏ s) c))
    (substNonVar (extsᵗ σ) Anv)
    (subst-∈ᵗ z∈A var-∈)
substᵏ {σ = σ} s
    (genᵏ_ {A = A} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★)
    with substᵗ σ A ≟Ty ★
substᵏ {σ = σ} s
    (genᵏ_ {A = A} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★)
    | no Aσ≢★ =
  genᵏ_ ⦃ substNonVar (extsᵗ σ) Bnv ⦄
    ⦃ subst-∈ᵗ z∈B var-∈ ⦄
    (subst-left-∼ᵏ (substᵗ-shift σ A)
      (substᵏ (gen-SubstEnv∼ᵏ s) c)) Aσ≢★
substᵏ {σ = σ} s
    (genᵏ_ {A = A} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★)
    | yes Aσ≡★ rewrite Aσ≡★ =
  factor-gen-starᵏ
    (subst-left-∼ᵏ
      (trans (substᵗ-shift σ A) (cong (renameᵗ suc) Aσ≡★))
      (substᵏ (gen-SubstEnv∼ᵏ s) c))
    (substNonVar (extsᵗ σ) Bnv)
    (subst-∈ᵗ z∈B var-∈)
substᵏ s bot-elimᵏ = bot-elimᵏ
substᵏ s bot-introᵏ = bot-introᵏ

private

  close-inst-selfᵏ : ∀ {Δ} {μ : Env∼ Δ} {m}
      (X : TyVar (Nat.suc Δ))
    → μ ⊢ singleSubᵗ ★ X ∼ᵏ[ m ] singleSubᵗ ★ X
  close-inst-selfᵏ X = refl∼ᵏ (singleSubᵗ ★ X)

  close-inst-to-★ᵏ : ∀ {Δ} {μ : Env∼ Δ} {m}
      (X : TyVar (Nat.suc Δ))
    → instᵐ μ X ≡ X∼★
    → μ ⊢ singleSubᵗ ★ X ∼ᵏ[ m ] ★
  close-inst-to-★ᵏ zero eq = idᵏ ★
  close-inst-to-★ᵏ {μ = μ} (suc X) eq =
    _!ᵏ ⦃ G∼★ = X∼★ᵍ eq ⦄ (idᵏ (＇ X)) ⦃ nonstar-X ⦄

  close-inst-from-★ᵏ : ∀ {Δ} {μ : Env∼ Δ} {m}
      (X : TyVar (Nat.suc Δ))
    → instᵐ μ X ≡ ★∼X
    → μ ⊢ ★ ∼ᵏ[ m ] singleSubᵗ ★ X
  close-inst-from-★ᵏ zero ()
  close-inst-from-★ᵏ {μ = μ} (suc X) eq =
    ？ᵏ_ ⦃ ★∼G = ★∼Xᵍ eq ⦄ (idᵏ (＇ X)) ⦃ nonstar-X ⦄

close-instᵏ : ∀ {Δ} {μ : Env∼ Δ} {m} {A : Ty (Nat.suc Δ)}
    {B : Ty Δ}
  → instᵐ μ ⊢ A ∼ᵏ[ m ] ⇑ᵗ B
  → μ ⊢ A [ ★ ]ᵗ ∼ᵏ[ m ] B
syntax close-instᵏ c = c [ ★/0 ]ᵏ

close-instᵏ {B = B} c =
  subst-right-∼ᵏ (shift-openᵗ B ★)
    (substᵏ
      (subst-env∼ᵏ close-inst-selfᵏ close-inst-to-★ᵏ
        close-inst-from-★ᵏ)
      c)

private

  close-gen-selfᵏ : ∀ {Δ} {μ : Env∼ Δ} {m}
      (X : TyVar (Nat.suc Δ))
    → μ ⊢ singleSubᵗ ★ X ∼ᵏ[ m ] singleSubᵗ ★ X
  close-gen-selfᵏ X = refl∼ᵏ (singleSubᵗ ★ X)

  close-gen-to-★ᵏ : ∀ {Δ} {μ : Env∼ Δ} {m}
      (X : TyVar (Nat.suc Δ))
    → genᵐ μ X ≡ X∼★
    → μ ⊢ singleSubᵗ ★ X ∼ᵏ[ m ] ★
  close-gen-to-★ᵏ zero ()
  close-gen-to-★ᵏ {μ = μ} (suc X) eq =
    _!ᵏ ⦃ G∼★ = X∼★ᵍ eq ⦄ (idᵏ (＇ X)) ⦃ nonstar-X ⦄

  close-gen-from-★ᵏ : ∀ {Δ} {μ : Env∼ Δ} {m}
      (X : TyVar (Nat.suc Δ))
    → genᵐ μ X ≡ ★∼X
    → μ ⊢ ★ ∼ᵏ[ m ] singleSubᵗ ★ X
  close-gen-from-★ᵏ zero eq = idᵏ ★
  close-gen-from-★ᵏ {μ = μ} (suc X) eq =
    ？ᵏ_ ⦃ ★∼G = ★∼Xᵍ eq ⦄ (idᵏ (＇ X)) ⦃ nonstar-X ⦄

close-genᵏ : ∀ {Δ} {μ : Env∼ Δ} {m} {A : Ty Δ}
    {B : Ty (Nat.suc Δ)}
  → genᵐ μ ⊢ ⇑ᵗ A ∼ᵏ[ m ] B
  → μ ⊢ A ∼ᵏ[ m ] B [ ★ ]ᵗ
syntax close-genᵏ c = c [ 0/★ ]ᵏ

close-genᵏ {A = A} c =
  subst-left-∼ᵏ (shift-openᵗ A ★)
    (substᵏ
      (subst-env∼ᵏ close-gen-selfᵏ close-gen-to-★ᵏ
        close-gen-from-★ᵏ)
      c)

private

  open-selfᵏ : ∀ {Δ} {μ : Env∼ Δ} {m}
      (C : Ty Δ) (X : TyVar (Nat.suc Δ))
    → μ ⊢ singleSubᵗ C X ∼ᵏ[ m ] singleSubᵗ C X
  open-selfᵏ C X = refl∼ᵏ (singleSubᵗ C X)

  open-to-★ᵏ : ∀ {Δ} {μ : Env∼ Δ} {m}
      (C : Ty Δ) (X : TyVar (Nat.suc Δ))
    → extᵐ μ X ≡ X∼★
    → μ ⊢ singleSubᵗ C X ∼ᵏ[ m ] ★
  open-to-★ᵏ C zero ()
  open-to-★ᵏ {μ = μ} C (suc X) eq =
    _!ᵏ ⦃ G∼★ = X∼★ᵍ eq ⦄ (idᵏ (＇ X)) ⦃ nonstar-X ⦄

  open-from-★ᵏ : ∀ {Δ} {μ : Env∼ Δ} {m}
      (C : Ty Δ) (X : TyVar (Nat.suc Δ))
    → extᵐ μ X ≡ ★∼X
    → μ ⊢ ★ ∼ᵏ[ m ] singleSubᵗ C X
  open-from-★ᵏ C zero ()
  open-from-★ᵏ {μ = μ} C (suc X) eq =
    ？ᵏ_ ⦃ ★∼G = ★∼Xᵍ eq ⦄ (idᵏ (＇ X)) ⦃ nonstar-X ⦄

infixl 8 _[_]ᵏ
_[_]ᵏ : ∀ {Δ} {μ : Env∼ Δ} {m} {A B : Ty (Nat.suc Δ)}
  → extᵐ μ ⊢ A ∼ᵏ[ m ] B
  → (C : Ty Δ)
  → μ ⊢ A [ C ]ᵗ ∼ᵏ[ m ] B [ C ]ᵗ
_[_]ᵏ {μ = μ} c C =
  substᵏ
    (subst-env∼ᵏ (open-selfᵏ C) (open-to-★ᵏ {μ = μ} C)
      (open-from-★ᵏ C))
    c

{-# TERMINATING #-}
source-spine-overlap⊥ : ∀ {Δ} {μ : Env∼ Δ} {m X A B C}
  → μ X ≡ X∼★
  → OccPath X A B
  → EndpointSpine B C
  → Fresh X C
  → μ ⊢ A ∼ᵏ[ m ] C
  → ⊥
source-spine-overlap⊥ to-star path sp fresh (idᵏ a) =
  fresh (path-source-occurs path)
source-spine-overlap⊥ {μ = μ} to-star (op-gen p) sp fresh c =
  source-spine-overlap⊥ {μ = extᵐ μ} to-star p
    (spine-peel-left suc sp) (fresh-shift fresh)
    (renameᵏ {μ′ = extᵐ μ} suc (λ X → refl) c)
source-spine-overlap⊥ to-star (op-fun-left p)
    (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh (c ↦ᵏ d) =
  source-spine-overlap⊥ to-star p (spine-renamed refl refl)
    (fresh-fun-left fresh) c
source-spine-overlap⊥ to-star (op-fun-right p)
    (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh (c ↦ᵏ d) =
  source-spine-overlap⊥ to-star p (spine-renamed refl refl)
    (fresh-fun-right fresh) d
source-spine-overlap⊥ to-star (op-all p) sp fresh (∀ᵏ c) =
  source-spine-overlap⊥ to-star p (spine-strip-both sp)
    (fresh-all fresh) c
source-spine-overlap⊥ to-star (op-inst p) sp fresh (∀ᵏ c) =
  source-spine-overlap⊥ to-star p (spine-peel-right suc sp)
    (fresh-all fresh) c
source-spine-overlap⊥ to-star path sp fresh (_!ᵏ c) =
  path-right-star-spine⊥ path sp
source-spine-overlap⊥ to-star (op-all p) sp fresh (instᵏ_ c C≢★) =
  source-spine-overlap⊥ to-star p (spine-peel-left suc sp)
    (fresh-shift fresh) c
source-spine-overlap⊥ to-star (op-inst p) sp fresh (instᵏ_ c C≢★) =
  source-spine-overlap⊥ to-star p
    (spine-map-right suc (spine-map-left suc sp))
    (fresh-shift fresh) c
source-spine-overlap⊥ to-star path sp fresh (genᵏ_ c C≢★) =
  source-spine-overlap⊥ to-star (path-shift path)
    (spine-peel-right suc sp) (fresh-all fresh) c
source-spine-overlap⊥ to-star path sp fresh bot-elimᵏ
    with path-source-occurs path
source-spine-overlap⊥ to-star path sp fresh bot-elimᵏ
    | ∈-all ()
source-spine-overlap⊥ to-star path sp fresh bot-introᵏ
    with path-source-occurs path
source-spine-overlap⊥ to-star path sp fresh bot-introᵏ
    | ∈-all ()

{-# TERMINATING #-}
target-spine-overlap⊥ : ∀ {Δ} {μ : Env∼ Δ} {m X A B C}
  → μ X ≡ ★∼X
  → OccPath X A B
  → EndpointSpine A C
  → Fresh X C
  → μ ⊢ C ∼ᵏ[ m ] B
  → ⊥
target-spine-overlap⊥ from-star path sp fresh (idᵏ a) =
  fresh (path-target-occurs path)
target-spine-overlap⊥ {μ = μ} from-star (op-inst p) sp fresh c =
  target-spine-overlap⊥ {μ = extᵐ μ} from-star p
    (spine-peel-left suc sp) (fresh-shift fresh)
    (renameᵏ {μ′ = extᵐ μ} suc (λ X → refl) c)
target-spine-overlap⊥ from-star (op-fun-left p)
    (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh (c ↦ᵏ d) =
  target-spine-overlap⊥ from-star p (spine-renamed refl refl)
    (fresh-fun-left fresh) c
target-spine-overlap⊥ from-star (op-fun-right p)
    (spine-renamed {T = T₁ ⇒ T₂} refl refl) fresh (c ↦ᵏ d) =
  target-spine-overlap⊥ from-star p (spine-renamed refl refl)
    (fresh-fun-right fresh) d
target-spine-overlap⊥ from-star (op-all p) sp fresh (∀ᵏ c) =
  target-spine-overlap⊥ from-star p (spine-strip-both sp)
    (fresh-all fresh) c
target-spine-overlap⊥ from-star (op-gen p) sp fresh (∀ᵏ c) =
  target-spine-overlap⊥ from-star p (spine-peel-right suc sp)
    (fresh-all fresh) c
target-spine-overlap⊥ from-star path sp fresh (？ᵏ_ c ⦃ Bns ⦄) =
  path-left-star-spine⊥ path sp
target-spine-overlap⊥ from-star path sp fresh (instᵏ_ c B≢★) =
  target-spine-overlap⊥ from-star (path-shift path)
    (spine-peel-right suc sp) (fresh-all fresh) c
target-spine-overlap⊥ from-star (op-all p) sp fresh (genᵏ_ c C≢★) =
  target-spine-overlap⊥ from-star p (spine-peel-left suc sp)
    (fresh-shift fresh) c
target-spine-overlap⊥ from-star (op-gen p) sp fresh (genᵏ_ c C≢★) =
  target-spine-overlap⊥ from-star p
    (spine-map-right suc (spine-map-left suc sp))
    (fresh-shift fresh) c
target-spine-overlap⊥ from-star path sp fresh bot-elimᵏ
    with path-target-occurs path
target-spine-overlap⊥ from-star path sp fresh bot-elimᵏ
    | ∈-all ()
target-spine-overlap⊥ from-star path sp fresh bot-introᵏ
    with path-target-occurs path
target-spine-overlap⊥ from-star path sp fresh bot-introᵏ
    | ∈-all ()

∀-inst-overlap⊥ : ∀ {Δ} {μ : Env∼ Δ} {m A B}
  → zero ∈ᵗ A
  → extᵐ μ ⊢ A ∼ᵏ[ gen-ok ] B
  → instᵐ μ ⊢ A ∼ᵏ[ m ] ⇑ᵗ (`∀ B)
  → ⊥
∀-inst-overlap⊥ {B = B} z∈A c d =
  source-spine-overlap⊥ refl (source-path-self refl c z∈A)
    (insert-spine zero {B = B}) (insert-fresh-occ zero (`∀ B)) d

∀-gen-overlap⊥ : ∀ {Δ} {μ : Env∼ Δ} {m A B}
  → zero ∈ᵗ B
  → extᵐ μ ⊢ A ∼ᵏ[ gen-ok ] B
  → genᵐ μ ⊢ ⇑ᵗ (`∀ A) ∼ᵏ[ m ] B
  → ⊥
∀-gen-overlap⊥ {A = A} z∈B c d =
  target-spine-overlap⊥ refl (target-path-self refl c z∈B)
    (insert-spine zero {B = A}) (insert-fresh-occ zero (`∀ A)) d

strict-cross-left-route : ∀ {Δ} {μ ν : Env∼ Δ}
    {m n X A A′ B B′ C C′ D D′}
  → InsertOverlapState μ ν X m n
      (A ⇒ A′) (B ⇒ B′) (C ⇒ C′) (D ⇒ D′)
  → X ∈ᵗ A
  → X ∉ᵗ A′
  → X ∉ᵗ B
  → X ∈ᵗ B′
  → μ ⊢ A ∼ᵏ[ gen-ok ] C
  → ν ⊢ D′ ∼ᵏ[ gen-ok ] B′
  → (∃[ Y ] (Y ∈ᵗ C′ × Y ∉ᵗ A′ × μ Y ≢ ★∼X))
    ⊎
    (∃[ Y ] (Y ∈ᵗ D × Y ∉ᵗ B × ν Y ≢ X∼★))
strict-cross-left-route st X∈A X∉A′ X∉B X∈B′ (idᵏ a) d₂ =
  ⊥-elim (fresh-fun-left (state-freshC st) X∈A)
strict-cross-left-route st X∈A X∉A′ X∉B X∈B′ c₁ (idᵏ a) =
  ⊥-elim (fresh-fun-right (state-freshD st) X∈B′)
strict-cross-left-route st () X∉A′ X∉B X∈B′ (？ᵏ_ c₁ ⦃ Bns ⦄) d₂
strict-cross-left-route st X∈A X∉A′ X∉B () c₁ (_!ᵏ d₂ ⦃ Ans ⦄)
strict-cross-left-route st (∈-all ()) X∉A′ X∉B X∈B′ bot-elimᵏ d₂
strict-cross-left-route st (∈-all ()) X∉A′ X∉B X∈B′ bot-introᵏ d₂
strict-cross-left-route st X∈A X∉A′ X∉B (∈-all ()) c₁ bot-elimᵏ
strict-cross-left-route st X∈A X∉A′ X∉B (∈-all ()) c₁ bot-introᵏ
strict-cross-left-route st X∈A X∉A′ X∉B X∈B′ c₁ d₂ =
  {!!}

strict-cross-right-route : ∀ {Δ} {μ ν : Env∼ Δ}
    {m n X A A′ B B′ C C′ D D′}
  → InsertOverlapState μ ν X m n
      (A ⇒ A′) (B ⇒ B′) (C ⇒ C′) (D ⇒ D′)
  → X ∉ᵗ A
  → X ∈ᵗ A′
  → X ∈ᵗ B
  → X ∉ᵗ B′
  → μ ⊢ A′ ∼ᵏ[ gen-ok ] C′
  → ν ⊢ D ∼ᵏ[ gen-ok ] B
  → (∃[ Y ] (Y ∈ᵗ C × Y ∉ᵗ A × μ Y ≢ ★∼X))
    ⊎
    (∃[ Y ] (Y ∈ᵗ D′ × Y ∉ᵗ B′ × ν Y ≢ X∼★))
strict-cross-right-route st X∉A X∈A′ X∈B X∉B′ (idᵏ a) d₁ =
  ⊥-elim (fresh-fun-right (state-freshC st) X∈A′)
strict-cross-right-route st X∉A X∈A′ X∈B X∉B′ c₂ (idᵏ a) =
  ⊥-elim (fresh-fun-left (state-freshD st) X∈B)
strict-cross-right-route st X∉A () X∈B X∉B′ (？ᵏ_ c₂ ⦃ Bns ⦄) d₁
strict-cross-right-route st X∉A X∈A′ () X∉B′ c₂ (_!ᵏ d₁ ⦃ Ans ⦄)
strict-cross-right-route st X∉A (∈-all ()) X∈B X∉B′ bot-elimᵏ d₁
strict-cross-right-route st X∉A (∈-all ()) X∈B X∉B′ bot-introᵏ d₁
strict-cross-right-route st X∉A X∈A′ (∈-all ()) X∉B′ c₂ bot-elimᵏ
strict-cross-right-route st X∉A X∈A′ (∈-all ()) X∉B′ c₂ bot-introᵏ
strict-cross-right-route st X∉A X∈A′ X∈B X∉B′ c₂ d₁ =
  {!!}

strict-cross-left⊥ : ∀ {Δ} {μ ν : Env∼ Δ}
    {m n X A A′ B B′ C C′ D D′}
  → InsertOverlapState μ ν X m n
      (A ⇒ A′) (B ⇒ B′) (C ⇒ C′) (D ⇒ D′)
  → X ∈ᵗ A
  → X ∉ᵗ A′
  → X ∉ᵗ B
  → X ∈ᵗ B′
  → μ ⊢ A ∼ᵏ[ gen-ok ] C
  → μ ⊢ A′ ∼ᵏ[ gen-ok ] C′
  → ν ⊢ D ∼ᵏ[ gen-ok ] B
  → ν ⊢ D′ ∼ᵏ[ gen-ok ] B′
  → ⊥
strict-cross-left⊥ st X∈A X∉A′ X∉B X∈B′ c₁ c₂ d₁ d₂
    with strict-cross-left-route st X∈A X∉A′ X∉B X∈B′ c₁ d₂
strict-cross-left⊥ st X∈A X∉A′ X∉B X∈B′ c₁ c₂ d₁ d₂
    | inj₁ (Y , Y∈C′ , Y∉A′ , μY≢from) =
  not-occurs Y∉A′
    (target-occurs-source-not-from-starᵏ μY≢from c₂ Y∈C′)
strict-cross-left⊥ st X∈A X∉A′ X∉B X∈B′ c₁ c₂ d₁ d₂
    | inj₂ (Y , Y∈D , Y∉B , νY≢to) =
  not-occurs Y∉B
    (source-occurs-target-not-to-starᵏ νY≢to d₁ Y∈D)

strict-cross-right⊥ : ∀ {Δ} {μ ν : Env∼ Δ}
    {m n X A A′ B B′ C C′ D D′}
  → InsertOverlapState μ ν X m n
      (A ⇒ A′) (B ⇒ B′) (C ⇒ C′) (D ⇒ D′)
  → X ∉ᵗ A
  → X ∈ᵗ A′
  → X ∈ᵗ B
  → X ∉ᵗ B′
  → μ ⊢ A ∼ᵏ[ gen-ok ] C
  → μ ⊢ A′ ∼ᵏ[ gen-ok ] C′
  → ν ⊢ D ∼ᵏ[ gen-ok ] B
  → ν ⊢ D′ ∼ᵏ[ gen-ok ] B′
  → ⊥
strict-cross-right⊥ st X∉A X∈A′ X∈B X∉B′ c₁ c₂ d₁ d₂
    with strict-cross-right-route st X∉A X∈A′ X∈B X∉B′ c₂ d₁
strict-cross-right⊥ st X∉A X∈A′ X∈B X∉B′ c₁ c₂ d₁ d₂
    | inj₁ (Y , Y∈C , Y∉A , μY≢from) =
  not-occurs Y∉A
    (target-occurs-source-not-from-starᵏ μY≢from c₁ Y∈C)
strict-cross-right⊥ st X∉A X∈A′ X∈B X∉B′ c₁ c₂ d₁ d₂
    | inj₂ (Y , Y∈D′ , Y∉B′ , νY≢to) =
  not-occurs Y∉B′
    (source-occurs-target-not-to-starᵏ νY≢to d₂ Y∈D′)

insert-overlap-state⊥ : ∀ {Δ} {μ ν : Env∼ Δ}
    {m n X A B C D}
  → InsertOverlapState μ ν X m n A B C D
  → X ∈ᵗ A
  → X ∈ᵗ B
  → μ ⊢ A ∼ᵏ[ m ] C
  → ν ⊢ D ∼ᵏ[ n ] B
  → ⊥
{-# TERMINATING #-}
insert-overlap-state⊥ st X∈A X∈B (idᵏ a) d =
  state-freshC st X∈A
insert-overlap-state⊥ st X∈A X∈B c (idᵏ a) =
  state-freshD st X∈B
insert-overlap-state⊥ st (∈-fun-left X∈A) (∈-fun-left X∈B)
    (c₁ ↦ᵏ c₂) (d₁ ↦ᵏ d₂) =
  insert-overlap-state⊥ (ios-fun-left st) X∈A X∈B c₁ d₁
insert-overlap-state⊥ st (∈-fun-left X∈A)
    (∈-fun-right X∉B X∈B) (c₁ ↦ᵏ c₂) (d₁ ↦ᵏ d₂)
    with occurs? _ _
insert-overlap-state⊥ st (∈-fun-left X∈A)
    (∈-fun-right X∉B X∈B) (c₁ ↦ᵏ c₂) (d₁ ↦ᵏ d₂)
    | present X∈A′ =
  insert-overlap-state⊥ (ios-fun-right st) X∈A′ X∈B c₂ d₂
insert-overlap-state⊥ st (∈-fun-left X∈A)
    (∈-fun-right X∉B X∈B) (c₁ ↦ᵏ c₂) (d₁ ↦ᵏ d₂)
    | absent X∉A′ =
  strict-cross-left⊥ st X∈A X∉A′ X∉B X∈B c₁ c₂ d₁ d₂
insert-overlap-state⊥ st (∈-fun-right X∉A X∈A)
    (∈-fun-left X∈B) (c₁ ↦ᵏ c₂) (d₁ ↦ᵏ d₂)
    with occurs? _ _
insert-overlap-state⊥ st (∈-fun-right X∉A X∈A)
    (∈-fun-left X∈B) (c₁ ↦ᵏ c₂) (d₁ ↦ᵏ d₂)
    | present X∈B′ =
  insert-overlap-state⊥ (ios-fun-right st) X∈A X∈B′ c₂ d₂
insert-overlap-state⊥ st (∈-fun-right X∉A X∈A)
    (∈-fun-left X∈B) (c₁ ↦ᵏ c₂) (d₁ ↦ᵏ d₂)
    | absent X∉B′ =
  strict-cross-right⊥ st X∉A X∈A X∈B X∉B′ c₁ c₂ d₁ d₂
insert-overlap-state⊥ st (∈-fun-right X∉A X∈A)
    (∈-fun-right X∉B X∈B) (c₁ ↦ᵏ c₂) (d₁ ↦ᵏ d₂) =
  insert-overlap-state⊥ (ios-fun-right st) X∈A X∈B c₂ d₂
insert-overlap-state⊥ st X∈A (∈-all X∈B)
    (c₁ ↦ᵏ c₂) (∀ᵏ d) =
  insert-overlap-state⊥ (ios-right∀ st) (shift-occurs X∈A) X∈B
    (renameᵏ suc (λ X → refl) (c₁ ↦ᵏ c₂)) d
insert-overlap-state⊥ st X∈A X∈B
    (c₁ ↦ᵏ c₂) (instᵏ_ d B≢★) =
  insert-overlap-state⊥ (ios-right-inst st)
    (shift-occurs X∈A) (shift-occurs X∈B)
    (renameᵏ suc (λ X → refl) (c₁ ↦ᵏ c₂)) d
insert-overlap-state⊥ st X∈A (∈-all X∈B)
    (c₁ ↦ᵏ c₂) (genᵏ_ d A≢★) =
  insert-overlap-state⊥ (ios-right-gen can-gen st) (shift-occurs X∈A)
    X∈B (renameᵏ suc (λ X → refl) (c₁ ↦ᵏ c₂)) d
insert-overlap-state⊥ st X∈A X∈B (_!ᵏ c ⦃ Ans ⦄) d =
  occurs-left-star-spine⊥ X∈B (state-spineC st)
insert-overlap-state⊥ st () X∈B (？ᵏ_ c ⦃ Bns ⦄) d
insert-overlap-state⊥ st X∈A X∈B c (？ᵏ_ d ⦃ Bns ⦄) =
  occurs-left-star-spine⊥ X∈A (state-spineD st)
insert-overlap-state⊥ st X∈A () c (_!ᵏ d ⦃ Ans ⦄)
insert-overlap-state⊥ st (∈-all X∈A) (∈-all X∈B)
    (∀ᵏ c) (∀ᵏ d) =
  insert-overlap-state⊥ (ios-∀∀ st) X∈A X∈B c d
insert-overlap-state⊥ st (∈-all X∈A) X∈B
    (∀ᵏ c) (instᵏ_ d B≢★) =
  insert-overlap-state⊥ (ios-∀inst st) X∈A (shift-occurs X∈B) c d
insert-overlap-state⊥ st (∈-all X∈A) (∈-all X∈B)
    (∀ᵏ c) (genᵏ_ d A≢★) =
  insert-overlap-state⊥ (ios-∀gen can-gen st) X∈A X∈B c d
insert-overlap-state⊥ st (∈-all X∈A) X∈B
    (∀ᵏ c) (d₁ ↦ᵏ d₂) =
  insert-overlap-state⊥ (ios-left∀ st) X∈A (shift-occurs X∈B)
    c (renameᵏ suc (λ X → refl) (d₁ ↦ᵏ d₂))
insert-overlap-state⊥ st (∈-all X∈A) (∈-all X∈B)
    (instᵏ_ c B≢★) (∀ᵏ d) =
  insert-overlap-state⊥ (ios-inst∀ st) X∈A X∈B c d
insert-overlap-state⊥ st (∈-all X∈A) X∈B
    (instᵏ_ c B≢★) (instᵏ_ d B≢★′) =
  insert-overlap-state⊥ (ios-instinst st) X∈A
    (shift-occurs X∈B) c d
insert-overlap-state⊥ st (∈-all X∈A) (∈-all X∈B)
    (instᵏ_ c B≢★) (genᵏ_ d A≢★) =
  insert-overlap-state⊥ (ios-instgen can-gen st) X∈A X∈B c d
insert-overlap-state⊥ st (∈-all X∈A) X∈B
    (instᵏ_ c B≢★) (d₁ ↦ᵏ d₂) =
  insert-overlap-state⊥ (ios-left-inst st) X∈A
    (shift-occurs X∈B) c (renameᵏ suc (λ X → refl) (d₁ ↦ᵏ d₂))
insert-overlap-state⊥ st X∈A (∈-all X∈B)
    (genᵏ_ c A≢★) (∀ᵏ d) =
  insert-overlap-state⊥ (ios-gen∀ can-gen st)
    (shift-occurs X∈A) X∈B c d
insert-overlap-state⊥ st X∈A X∈B
    (genᵏ_ c A≢★) (instᵏ_ d B≢★) =
  insert-overlap-state⊥ (ios-geninst can-gen st) (shift-occurs X∈A)
    (shift-occurs X∈B) c d
insert-overlap-state⊥ st X∈A (∈-all X∈B)
    (genᵏ_ c A≢★) (genᵏ_ d A≢★′) =
  insert-overlap-state⊥ (ios-gengen can-gen can-gen st)
    (shift-occurs X∈A) X∈B c d
insert-overlap-state⊥ st X∈A X∈B
    (genᵏ_ c A≢★) (d₁ ↦ᵏ d₂) =
  insert-overlap-state⊥ (ios-left-gen can-gen st) (shift-occurs X∈A)
    (shift-occurs X∈B) c (renameᵏ suc (λ X → refl) (d₁ ↦ᵏ d₂))
insert-overlap-state⊥ st (∈-all ()) X∈B bot-elimᵏ d
insert-overlap-state⊥ st (∈-all ()) X∈B bot-introᵏ d
insert-overlap-state⊥ st X∈A (∈-all ()) c bot-elimᵏ
insert-overlap-state⊥ st X∈A (∈-all ()) c bot-introᵏ

inst-gen-overlap⊥ : ∀ {Δ} {μ : Env∼ Δ} {A B}
  → zero ∈ᵗ A
  → zero ∈ᵗ B
  → instᵐ μ ⊢ A ∼ᵏ[ gen-blocked ] ⇑ᵗ (`∀ B)
  → genᵐ μ ⊢ ⇑ᵗ (`∀ A) ∼ᵏ[ gen-ok ] B
  → ⊥
inst-gen-overlap⊥ z∈A z∈B c d =
  insert-overlap-state⊥ ios-base z∈A z∈B c d

canonical-unique : ∀ {Δ} {μ : Env∼ Δ} {m A B}
  → (c d : μ ⊢ A ∼ᵏ[ m ] B)
  → c ≡ d
canonical-unique (idᵏ a) (idᵏ b)
    rewrite CP.atom-unique a b =
  refl
canonical-unique (c ↦ᵏ d) (c′ ↦ᵏ d′)
    rewrite canonical-unique c c′
          | canonical-unique d d′ =
  refl
canonical-unique (∀ᵏ c) (∀ᵏ d)
    rewrite canonical-unique c d =
  refl
canonical-unique (∀ᵏ c) (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ d B≢★) =
  ⊥-elim (∀-inst-overlap⊥ z∈A c d)
canonical-unique (∀ᵏ c) (genᵏ_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ d A≢★) =
  ⊥-elim (∀-gen-overlap⊥ z∈B c d)
canonical-unique (∀ᵏ c) bot-elimᵏ
    with consistency-source-occurs-target refl (forgetᵏ c) var-∈
canonical-unique (∀ᵏ c) bot-elimᵏ | ()
canonical-unique (∀ᵏ c) bot-introᵏ
    with consistency-source-occurs-target refl (C.sym∼ (forgetᵏ c)) var-∈
canonical-unique (∀ᵏ c) bot-introᵏ | ()
canonical-unique (_!ᵏ c ⦃ Ans ⦄) (instᵏ_ d B≢★) =
  ⊥-elim (B≢★ refl)
canonical-unique (_!ᵏ ⦃ Gᵍ = gG ⦄ ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans ⦄)
    (_!ᵏ ⦃ Gᵍ = gH ⦄ ⦃ G∼★ = H∼★ ⦄ d ⦃ Ans′ ⦄)
    with CP.tag-ground-unique Ans gG gH (forgetᵏ c) (forgetᵏ d)
canonical-unique (_!ᵏ ⦃ Gᵍ = gG ⦄ ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans ⦄)
    (_!ᵏ ⦃ Gᵍ = gH ⦄ ⦃ G∼★ = H∼★ ⦄ d ⦃ Ans′ ⦄)
    | refl
    rewrite ground-unique gG gH
          | ∼★-unique G∼★ H∼★
          | nonStar-unique Ans Ans′
          | canonical-unique c d =
  refl
canonical-unique (？ᵏ_ ⦃ Gᵍ = gG ⦄ ⦃ ★∼G = ★∼G ⦄ c ⦃ Bns ⦄)
    (？ᵏ_ ⦃ Gᵍ = gH ⦄ ⦃ ★∼G = ★∼H ⦄ d ⦃ Bns′ ⦄)
    with CP.untag-ground-unique Bns gG gH (forgetᵏ c) (forgetᵏ d)
canonical-unique (？ᵏ_ ⦃ Gᵍ = gG ⦄ ⦃ ★∼G = ★∼G ⦄ c ⦃ Bns ⦄)
    (？ᵏ_ ⦃ Gᵍ = gH ⦄ ⦃ ★∼G = ★∼H ⦄ d ⦃ Bns′ ⦄)
    | refl
    rewrite ground-unique gG gH
          | ★∼-unique ★∼G ★∼H
          | nonStar-unique Bns Bns′
          | canonical-unique c d =
  refl
canonical-unique (？ᵏ_ c ⦃ Bns ⦄) (genᵏ_ d A≢★) =
  ⊥-elim (A≢★ refl)
canonical-unique (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★)
    (∀ᵏ d) =
  ⊥-elim (∀-inst-overlap⊥ z∈A d c)
canonical-unique (instᵏ_ c B≢★) (_!ᵏ d ⦃ Ans ⦄) =
  ⊥-elim (B≢★ refl)
canonical-unique (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★)
    (instᵏ_ ⦃ Anv′ ⦄ ⦃ z∈A′ ⦄ d B≢★′)
    rewrite nonVar-unique Anv Anv′
          | ∈ᵗ-unique z∈A z∈A′
          | canonical-unique c d
          | ¬-unique B≢★ B≢★′ =
  refl
canonical-unique (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★)
    (genᵏ_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ d A≢★) =
  ⊥-elim (inst-gen-overlap⊥ z∈A z∈B c d)
canonical-unique (genᵏ_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★)
    (∀ᵏ d) =
  ⊥-elim (∀-gen-overlap⊥ z∈B d c)
canonical-unique (genᵏ_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★)
    (instᵏ_ ⦃ Anv ⦄ ⦃ z∈A ⦄ d B≢★) =
  ⊥-elim (inst-gen-overlap⊥ z∈A z∈B d c)
canonical-unique (genᵏ_ c A≢★) (？ᵏ_ d ⦃ Bns ⦄) =
  ⊥-elim (A≢★ refl)
canonical-unique (genᵏ_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★)
    (genᵏ_ ⦃ Bnv′ ⦄ ⦃ z∈B′ ⦄ d A≢★′)
    rewrite nonVar-unique Bnv Bnv′
          | ∈ᵗ-unique z∈B z∈B′
          | canonical-unique c d
          | ¬-unique A≢★ A≢★′ =
  refl
canonical-unique bot-elimᵏ (∀ᵏ d)
    with consistency-source-occurs-target refl (forgetᵏ d) var-∈
canonical-unique bot-elimᵏ (∀ᵏ d) | ()
canonical-unique bot-elimᵏ bot-elimᵏ = refl
canonical-unique bot-introᵏ (∀ᵏ d)
    with consistency-source-occurs-target refl (C.sym∼ (forgetᵏ d)) var-∈
canonical-unique bot-introᵏ (∀ᵏ d) | ()
canonical-unique bot-introᵏ bot-introᵏ = refl
