module proof.LR.CastSubst where

-- File Charter:
--   * Cast substitution laws, for case 6 of the cast lemma
--     (proof/LR/CastLemma.agda, `Case6`, `AtReplay.Ob`).
--   * `_≅ᶜ_`: equality of casts across their indices (mode
--     environment and types); `≅ᶜ-⟨⟩` turns it into equality of cast
--     terms.  The side conditions inside a cast (Ground, NonStar,
--     NonVar, occurrence, the gates into and out of `★`) have unique
--     proofs, and `B ≢ ★` has definitionally unique proofs (⊥ has eta),
--     so casts with equal sub-casts are equal.
--   * Traversal laws, each by induction on the cast:
--       - `transport-≅`: `transport-env∼` is the identity;
--       - `ren-ren`: renaming composes;
--       - `ren-sym`: renaming commutes with `sym∼`;
--       - `ren-ext`/`ren-≅`: renaming at pointwise equal renamings,
--         and at equal casts.
--   * `subst-factorI`, `subst-factorG` (and `ren-factorI/G`,
--     `sym-factorI/G`): substitution, renaming and `sym∼` commute with
--     the factorings `factor-inst-star`/`factor-gen-star` (the `≟Ty ★`
--     branches of `subst∼`).
--   * Laws between substitution, renaming and `sym∼`, each by induction
--     on the cast, at environments related at the variables by a
--     record closed under `ext`, `inst`, `gen` and `flip`:
--       - `srn` (`SRel`): substitution after renaming;
--       - `rns` (`RRel`): renaming after substitution;
--       - `subst-sym` (`FlipM`): substitution commutes with `sym∼`.
--   * `subst-subst`: substitution composes, at any three environments
--     that agree at the variables (`Fuse`).  It is `Fusion.ss` at the
--     family `Fuse`, whose closure under `ext`/`inst`/`gen` uses `srn`
--     and `rns` (`shift-law`) and under `flip` uses `subst-sym`.
--   * `subst-id`: substitution at an environment that is the identity
--     at the variables (`IdS`, e.g. `idE`) is the identity; hence
--     `subst-ren` (substitution at a renaming is the renaming) and
--     `subst-⇑` (after the shift).
--   * `Agree ρ s s′`: s′ at ρ X has the casts of s at X; `agree-ren`
--     moves an agreement along a further renaming.
--   * Environments built from others: `seqE` (composite, `seq-fuse`),
--     `preRen` (read before a renaming, `pre-rel`), `renAfter` (followed
--     by a renaming, `ren-after`), `openE` (the opening `_[_]ᶜ`).
--   * Case 6 of the cast lemma:
--       - `CastL.castL`, `CastR.castR`: the obligations `castL₂` and
--         `castR₂`, at the environments `CastL.envL`, `CastR.envR`
--         (to be taken for `sL`, `sR` of `hyp₂`), at any substitution
--         equal to the composite (`σC`, computed by `σC-suc`, `σC-eq`);
--       - `CastL.envL-old`, `CastR.envR-old`: at the old variables,
--         those environments have the casts of sL, sR renamed into the
--         future (for `VarI` there);
--       - `eager-close`: `c [ ★/0 ]ᶜ` is eager when c is (`subst-eager`,
--         at environments whose fields have no `inst`/`gen`, `NoIGEnv`);
--       - `castSize-case6`: the induction measure decreases.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
import Data.Nat as ℕ
open import Data.Nat using (_≤_; _<_; s≤s; _+_)
open import Data.Nat.Properties using (≤-trans; n≤1+n; +-monoʳ-≤)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency
open import CastTerms using (Term; _⟨_⟩)
open import LR.EagerCast using (Eager; NotInst; e-id; e-↦; e-∀; e-!; e-？;
  e-inst; e-gen; e-bot-elim; e-bot-intro)
open import proof.Consistency using (castSize; castSize-↑ᶜ;
  castSize-close-inst-≤)
open import proof.LR.SubstLemma using (substᵗ-∘)

open SubstEnv∼

------------------------------------------------------------------------
-- Unique proofs
------------------------------------------------------------------------

uip : ∀ {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
uip refl refl = refl

∼★-unique : ∀ {Δ} {μ : Env∼ Δ} {G : Ty Δ} (p q : μ ⊢ G ∼★) → p ≡ q
∼★-unique ⇒∼★ ⇒∼★ = refl
∼★-unique ι∼★ ι∼★ = refl
∼★-unique (X∼★ᵍ e) (X∼★ᵍ e′) = cong X∼★ᵍ (uip e e′)
∼★-unique (X∼★ᵍ e) (X∼★ᶜ e′) with trans (sym e) e′
∼★-unique (X∼★ᵍ e) (X∼★ᶜ e′) | ()
∼★-unique (X∼★ᶜ e) (X∼★ᵍ e′) with trans (sym e) e′
∼★-unique (X∼★ᶜ e) (X∼★ᵍ e′) | ()
∼★-unique (X∼★ᶜ e) (X∼★ᶜ e′) = cong X∼★ᶜ (uip e e′)
∼★-unique ∀∼★ ∀∼★ = refl

★∼-unique : ∀ {Δ} {μ : Env∼ Δ} {G : Ty Δ} (p q : μ ⊢★∼ G) → p ≡ q
★∼-unique ★∼⇒ ★∼⇒ = refl
★∼-unique ★∼ι ★∼ι = refl
★∼-unique (★∼Xᵍ e) (★∼Xᵍ e′) = cong ★∼Xᵍ (uip e e′)
★∼-unique (★∼Xᵍ e) (★∼Xᶜ e′) with trans (sym e) e′
★∼-unique (★∼Xᵍ e) (★∼Xᶜ e′) | ()
★∼-unique (★∼Xᶜ e) (★∼Xᵍ e′) with trans (sym e) e′
★∼-unique (★∼Xᶜ e) (★∼Xᵍ e′) | ()
★∼-unique (★∼Xᶜ e) (★∼Xᶜ e′) = cong ★∼Xᶜ (uip e e′)
★∼-unique ★∼∀ ★∼∀ = refl

∉-unique : ∀ {Δ} {X : TyVar Δ} {A} (p q : X ∉ᵗ A) → p ≡ q
∉-unique (∉-var d) (∉-var d′) = cong ∉-var (≢ᶠ-unique d d′)
∉-unique ∉-base ∉-base = refl
∉-unique ∉-star ∉-star = refl
∉-unique (∉-fun p₁ p₂) (∉-fun q₁ q₂) =
  cong₂ ∉-fun (∉-unique p₁ q₁) (∉-unique p₂ q₂)
∉-unique (∉-all p) (∉-all q) = cong ∉-all (∉-unique p q)

∈∉ : ∀ {Δ} {X : TyVar Δ} {A} → X ∈ᵗ A → X ∉ᵗ A → ⊥
∈∉ var-∈ (∉-var d) = ≢ᶠ→≢ d refl
∈∉ (∈-fun-left p) (∉-fun n₁ n₂) = ∈∉ p n₁
∈∉ (∈-fun-right n p) (∉-fun n₁ n₂) = ∈∉ p n₂
∈∉ (∈-all p) (∉-all n) = ∈∉ p n

∈-unique : ∀ {Δ} {X : TyVar Δ} {A} (p q : X ∈ᵗ A) → p ≡ q
∈-unique var-∈ var-∈ = refl
∈-unique (∈-fun-left p) (∈-fun-left q) = cong ∈-fun-left (∈-unique p q)
∈-unique (∈-fun-left p) (∈-fun-right n q) = ⊥-elim (∈∉ p n)
∈-unique (∈-fun-right n p) (∈-fun-left q) = ⊥-elim (∈∉ q n)
∈-unique (∈-fun-right n p) (∈-fun-right n′ q) =
  cong₂ ∈-fun-right (∉-unique n n′) (∈-unique p q)
∈-unique (∈-all p) (∈-all q) = cong ∈-all (∈-unique p q)

-- pointwise equal environments are equal
env-≡ : ∀ {Δ} {μ ν : Env∼ Δ} → Env∼Eq μ ν → μ ≡ ν
env-≡ {μ = []} {[]} e = refl
env-≡ {μ = v ∷ μ} {w ∷ ν} e =
  cong₂ _∷_ (pointwise e zero) (env-≡ (env∼-eq (λ X → pointwise e (suc X))))

------------------------------------------------------------------------
-- Equality of casts across their indices
------------------------------------------------------------------------

infix 4 _≅ᶜ_

data _≅ᶜ_ {Δ} {μ : Env∼ Δ} {A B : Ty Δ} (c : μ ⊢ A ∼ B)
    : ∀ {μ′ : Env∼ Δ} {A′ B′ : Ty Δ} → μ′ ⊢ A′ ∼ B′ → Set where
  hrefl : c ≅ᶜ c

module _ {Δ} {μ μ′ : Env∼ Δ} {A B A′ B′ : Ty Δ} {c : μ ⊢ A ∼ B}
    {c′ : μ′ ⊢ A′ ∼ B′} where

  ≅-env : c ≅ᶜ c′ → μ ≡ μ′
  ≅-env hrefl = refl

  ≅-src : c ≅ᶜ c′ → A ≡ A′
  ≅-src hrefl = refl

  ≅-tgt : c ≅ᶜ c′ → B ≡ B′
  ≅-tgt hrefl = refl

  ≅-sym : c ≅ᶜ c′ → c′ ≅ᶜ c
  ≅-sym hrefl = hrefl

  ≅ᶜ-⟨⟩ : (Q : Term Δ) → c ≅ᶜ c′ → Q ⟨ c ⟩ ≡ Q ⟨ c′ ⟩
  ≅ᶜ-⟨⟩ Q hrefl = refl

≅-trans : ∀ {Δ} {μ₁ μ₂ μ₃ : Env∼ Δ} {A₁ B₁ A₂ B₂ A₃ B₃}
    {c₁ : μ₁ ⊢ A₁ ∼ B₁} {c₂ : μ₂ ⊢ A₂ ∼ B₂} {c₃ : μ₃ ⊢ A₃ ∼ B₃}
  → c₁ ≅ᶜ c₂ → c₂ ≅ᶜ c₃ → c₁ ≅ᶜ c₃
≅-trans hrefl hrefl = hrefl

infixr 2 _⟫_
_⟫_ = ≅-trans

sr-≅ : ∀ {Δ} {μ : Env∼ Δ} {A B B′} (e : B ≡ B′) (c : μ ⊢ A ∼ B)
  → subst-right-∼ e c ≅ᶜ c
sr-≅ refl c = hrefl

sl-≅ : ∀ {Δ} {μ : Env∼ Δ} {A A′ B} (e : A ≡ A′) (c : μ ⊢ A ∼ B)
  → subst-left-∼ e c ≅ᶜ c
sl-≅ refl c = hrefl

------------------------------------------------------------------------
-- Congruences
------------------------------------------------------------------------

id-≅ : ∀ {Δ} {μ μ′ : Env∼ Δ} {A A′} {a : Atom A} {a′ : Atom A′}
  → μ ≡ μ′ → A ≡ A′ → (∀ {A} (x y : Atom A) → x ≡ y)
  → id {μ = μ} a ≅ᶜ id {μ = μ′} a′
id-≅ {a = a} {a′} refl refl u rewrite u a a′ = hrefl

atom-unique : ∀ {Δ} {A : Ty Δ} (x y : Atom A) → x ≡ y
atom-unique (＇ X) (＇ .X) = refl
atom-unique (‵ ι) (‵ .ι) = refl
atom-unique ★ ★ = refl

idX-≅ : ∀ {Δ} {μ μ′ : Env∼ Δ} {X Y : TyVar Δ} → μ ≡ μ′ → X ≡ Y
  → id {μ = μ} (＇ X) ≅ᶜ id {μ = μ′} (＇ Y)
idX-≅ refl refl = hrefl

↦-≅ : ∀ {Δ} {μ μ′ : Env∼ Δ} {A A′ B B′ C C′ D D′ : Ty Δ}
    {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
    {c′ : flipᵐ μ′ ⊢ C′ ∼ C} {d′ : μ′ ⊢ D ∼ D′}
  → d ≅ᶜ d′ → c ≅ᶜ c′ → (c ↦ d) ≅ᶜ (c′ ↦ d′)
↦-≅ hrefl hrefl = hrefl

∀-≅ : ∀ {Δ} {μ μ′ : Env∼ Δ} {A B A′ B′}
    {c : extᵐ μ ⊢ A ∼ B} {c′ : extᵐ μ′ ⊢ A′ ∼ B′}
  → c ≅ᶜ c′ → ∀ᶜ c ≅ᶜ ∀ᶜ c′
∀-≅ hrefl = hrefl

!-≅ : ∀ {Δ} {μ μ′ : Env∼ Δ} {A G A′ G′ : Ty Δ}
    {c : μ ⊢ A ∼ G} {c′ : μ′ ⊢ A′ ∼ G′}
    {g : Ground G} {g′ : Ground G′} {t : μ ⊢ G ∼★} {t′ : μ′ ⊢ G′ ∼★}
    {a : NonStar A} {a′ : NonStar A′}
  → c ≅ᶜ c′ → _! ⦃ g ⦄ ⦃ t ⦄ c ⦃ a ⦄ ≅ᶜ _! ⦃ g′ ⦄ ⦃ t′ ⦄ c′ ⦃ a′ ⦄
!-≅ {g = g} {g′} {t} {t′} {a} {a′} hrefl
  rewrite ground-unique g g′ | ∼★-unique t t′ | nonStar-unique a a′ =
  hrefl

？-≅ : ∀ {Δ} {μ μ′ : Env∼ Δ} {G B G′ B′ : Ty Δ}
    {c : μ ⊢ G ∼ B} {c′ : μ′ ⊢ G′ ∼ B′}
    {g : Ground G} {g′ : Ground G′} {t : μ ⊢★∼ G} {t′ : μ′ ⊢★∼ G′}
    {b : NonStar B} {b′ : NonStar B′}
  → c ≅ᶜ c′ → ？_ ⦃ g ⦄ ⦃ t ⦄ c ⦃ b ⦄ ≅ᶜ ？_ ⦃ g′ ⦄ ⦃ t′ ⦄ c′ ⦃ b′ ⦄
？-≅ {g = g} {g′} {t} {t′} {b} {b′} hrefl
  rewrite ground-unique g g′ | ★∼-unique t t′ | nonStar-unique b b′ =
  hrefl

inst-≅ : ∀ {Δ} {μ μ′ : Env∼ Δ} {A A′ : Ty (ℕ.suc Δ)} {B B′ : Ty Δ}
    {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B} {c′ : instᵐ μ′ ⊢ A′ ∼ ⇑ᵗ B′}
    {nv : NonVar A} {nv′ : NonVar A′} {z : zero ∈ᵗ A} {z′ : zero ∈ᵗ A′}
    {n : B ≢ ★} {n′ : B′ ≢ ★}
  → B ≡ B′ → c ≅ᶜ c′
  → inst_ ⦃ nv ⦄ ⦃ z ⦄ c n ≅ᶜ inst_ ⦃ nv′ ⦄ ⦃ z′ ⦄ c′ n′
inst-≅ {nv = nv} {nv′} {z} {z′} refl hrefl
  rewrite nonVar-unique nv nv′ | ∈-unique z z′ = hrefl

gen-≅ : ∀ {Δ} {μ μ′ : Env∼ Δ} {A A′ : Ty Δ} {B B′ : Ty (ℕ.suc Δ)}
    {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B} {c′ : genᵐ μ′ ⊢ ⇑ᵗ A′ ∼ B′}
    {nv : NonVar B} {nv′ : NonVar B′} {z : zero ∈ᵗ B} {z′ : zero ∈ᵗ B′}
    {n : A ≢ ★} {n′ : A′ ≢ ★}
  → A ≡ A′ → c ≅ᶜ c′
  → gen_ ⦃ nv ⦄ ⦃ z ⦄ c n ≅ᶜ gen_ ⦃ nv′ ⦄ ⦃ z′ ⦄ c′ n′
gen-≅ {nv = nv} {nv′} {z} {z′} refl hrefl
  rewrite nonVar-unique nv nv′ | ∈-unique z z′ = hrefl

bot-elim-≅ : ∀ {Δ} {μ μ′ : Env∼ Δ} → μ ≡ μ′
  → bot-elim {μ = μ} ≅ᶜ bot-elim {μ = μ′}
bot-elim-≅ refl = hrefl

bot-intro-≅ : ∀ {Δ} {μ μ′ : Env∼ Δ} → μ ≡ μ′
  → bot-intro {μ = μ} ≅ᶜ bot-intro {μ = μ′}
bot-intro-≅ refl = hrefl

------------------------------------------------------------------------
-- `transport-env∼` is the identity
------------------------------------------------------------------------

transport-≅ : ∀ {Δ} {μ ν : Env∼ Δ} {A B} (e : Env∼Eq μ ν)
  (c : μ ⊢ A ∼ B) → transport-env∼ e c ≅ᶜ c
transport-≅ e (id a) = id-≅ (sym (env-≡ e)) refl atom-unique
transport-≅ e (c ↦ d) =
  ↦-≅ (transport-≅ e d) (transport-≅ (flipEnv∼Eq e) c)
transport-≅ e (∀ᶜ c) = ∀-≅ (transport-≅ (extEnv∼Eq e) c)
transport-≅ e (_! c) = !-≅ (transport-≅ e c)
transport-≅ e (？_ c) = ？-≅ (transport-≅ e c)
transport-≅ e (inst_ c n) = inst-≅ refl (transport-≅ (instEnv∼Eq e) c)
transport-≅ e (gen_ c n) = gen-≅ refl (transport-≅ (genEnv∼Eq e) c)
transport-≅ e bot-elim = bot-elim-≅ (sym (env-≡ e))
transport-≅ e bot-intro = bot-intro-≅ (sym (env-≡ e))

------------------------------------------------------------------------
-- Renaming
------------------------------------------------------------------------

private
  ext-h : ∀ {Δ₁ Δ₂ Δ₃} {ρ₁ : Δ₁ ⇒ʳ Δ₂} {ρ₂ : Δ₂ ⇒ʳ Δ₃} {ρ₃ : Δ₁ ⇒ʳ Δ₃}
    → (∀ X → ρ₂ (ρ₁ X) ≡ ρ₃ X)
    → ∀ X → extᵗ ρ₂ (extᵗ ρ₁ X) ≡ extᵗ ρ₃ X
  ext-h h zero = refl
  ext-h h (suc X) = cong suc (h X)

  ext-h′ : ∀ {Δ₁ Δ₂} {ρ ρ′ : Δ₁ ⇒ʳ Δ₂}
    → (∀ X → ρ X ≡ ρ′ X) → ∀ X → extᵗ ρ X ≡ extᵗ ρ′ X
  ext-h′ h zero = refl
  ext-h′ h (suc X) = cong suc (h X)

ren-sr : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {A B B′} (ρ : Δ ⇒ʳ Δ′)
    (e : ∀ X → μ′ ‼ ρ X ≡ μ ‼ X) (r : B ≡ B′) (c : μ ⊢ A ∼ B)
  → rename∼ {μ = μ} {μ′} ρ e (subst-right-∼ r c)
    ≅ᶜ rename∼ {μ = μ} {μ′} ρ e c
ren-sr ρ e refl c = hrefl

ren-sl : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {A A′ B} (ρ : Δ ⇒ʳ Δ′)
    (e : ∀ X → μ′ ‼ ρ X ≡ μ ‼ X) (r : A ≡ A′) (c : μ ⊢ A ∼ B)
  → rename∼ {μ = μ} {μ′} ρ e (subst-left-∼ r c)
    ≅ᶜ rename∼ {μ = μ} {μ′} ρ e c
ren-sl ρ e refl c = hrefl

-- renaming at pointwise equal renamings, with any mode proofs
ren-ext : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {A B}
    {ρ ρ′ : Δ ⇒ʳ Δ′} (e : ∀ X → μ′ ‼ ρ X ≡ μ ‼ X)
    (e′ : ∀ X → μ′ ‼ ρ′ X ≡ μ ‼ X)
  → (∀ X → ρ X ≡ ρ′ X) → (c : μ ⊢ A ∼ B)
  → rename∼ {μ = μ} {μ′} ρ e c ≅ᶜ rename∼ {μ = μ} {μ′} ρ′ e′ c
ren-ext e e′ h (id ★) = hrefl
ren-ext e e′ h (id (‵ ι)) = hrefl
ren-ext e e′ h (id (＇ X)) = idX-≅ refl (h X)
ren-ext {μ = μ} {μ′} {ρ = ρ} {ρ′} e e′ h (c ↦ d) =
  ↦-≅ (ren-ext {μ = μ} {μ′} e e′ h d)
    (ren-ext {μ = flipᵐ μ} {flipᵐ μ′}
      (flip-rename-env {μ = μ} {μ′} ρ e)
      (flip-rename-env {μ = μ} {μ′} ρ′ e′) h c)
ren-ext {μ = μ} {μ′} {ρ = ρ} {ρ′} e e′ h (∀ᶜ c) =
  ∀-≅ (ren-ext {μ = extᵐ μ} {extᵐ μ′} (extᵐ-rename ρ e)
    (extᵐ-rename ρ′ e′) (ext-h′ h) c)
ren-ext {μ = μ} {μ′} e e′ h (_! c) = !-≅ (ren-ext {μ = μ} {μ′} e e′ h c)
ren-ext {μ = μ} {μ′} e e′ h (？_ c) = ？-≅ (ren-ext {μ = μ} {μ′} e e′ h c)
ren-ext {μ = μ} {μ′} {ρ = ρ} {ρ′} e e′ h (inst_ {B = B} c n) =
  inst-≅ (renameᵗ-cong B h)
    (sr-≅ (renameᵗ-shift ρ B) _
     ⟫ ren-ext {μ = instᵐ μ} {instᵐ μ′} (instᵐ-rename ρ e)
         (instᵐ-rename ρ′ e′) (ext-h′ h) c
     ⟫ ≅-sym (sr-≅ (renameᵗ-shift ρ′ B) _))
ren-ext {μ = μ} {μ′} {ρ = ρ} {ρ′} e e′ h (gen_ {A = A} c n) =
  gen-≅ (renameᵗ-cong A h)
    (sl-≅ (renameᵗ-shift ρ A) _
     ⟫ ren-ext {μ = genᵐ μ} {genᵐ μ′} (genᵐ-rename ρ e)
         (genᵐ-rename ρ′ e′) (ext-h′ h) c
     ⟫ ≅-sym (sl-≅ (renameᵗ-shift ρ′ A) _))
ren-ext e e′ h bot-elim = hrefl
ren-ext e e′ h bot-intro = hrefl

ren-≅ : ∀ {Δ Δ′} {μ μ₂ : Env∼ Δ} {μ′ : Env∼ Δ′} {A B A₂ B₂}
    {ρ : Δ ⇒ʳ Δ′} {c : μ ⊢ A ∼ B} {c₂ : μ₂ ⊢ A₂ ∼ B₂}
    (e : ∀ X → μ′ ‼ ρ X ≡ μ ‼ X) (e₂ : ∀ X → μ′ ‼ ρ X ≡ μ₂ ‼ X)
  → c ≅ᶜ c₂
  → rename∼ {μ = μ} {μ′} ρ e c ≅ᶜ rename∼ {μ = μ₂} {μ′} ρ e₂ c₂
ren-≅ {μ = μ} {μ′ = μ′} {c = c} e e₂ hrefl =
  ren-ext {μ = μ} {μ′} e e₂ (λ X → refl) c

-- renaming composes
ren-ren : ∀ {Δ₁ Δ₂ Δ₃} {μ₁ : Env∼ Δ₁} {μ₂ : Env∼ Δ₂} {μ₃ : Env∼ Δ₃}
    {A B} {ρ₁ : Δ₁ ⇒ʳ Δ₂} {ρ₂ : Δ₂ ⇒ʳ Δ₃} {ρ₃ : Δ₁ ⇒ʳ Δ₃}
    (e₁ : ∀ X → μ₂ ‼ ρ₁ X ≡ μ₁ ‼ X) (e₂ : ∀ X → μ₃ ‼ ρ₂ X ≡ μ₂ ‼ X)
    (e₃ : ∀ X → μ₃ ‼ ρ₃ X ≡ μ₁ ‼ X)
  → (∀ X → ρ₂ (ρ₁ X) ≡ ρ₃ X) → (c : μ₁ ⊢ A ∼ B)
  → rename∼ {μ = μ₂} {μ₃} ρ₂ e₂ (rename∼ {μ = μ₁} {μ₂} ρ₁ e₁ c)
    ≅ᶜ rename∼ {μ = μ₁} {μ₃} ρ₃ e₃ c
ren-ren e₁ e₂ e₃ h (id ★) = hrefl
ren-ren e₁ e₂ e₃ h (id (‵ ι)) = hrefl
ren-ren e₁ e₂ e₃ h (id (＇ X)) = idX-≅ refl (h X)
ren-ren {μ₁ = μ₁} {μ₂} {μ₃} {ρ₁ = ρ₁} {ρ₂} {ρ₃} e₁ e₂ e₃ h (c ↦ d) =
  ↦-≅ (ren-ren {μ₁ = μ₁} {μ₂} {μ₃} e₁ e₂ e₃ h d)
    (ren-ren {μ₁ = flipᵐ μ₁} {flipᵐ μ₂} {flipᵐ μ₃}
      (flip-rename-env {μ = μ₁} {μ₂} ρ₁ e₁)
      (flip-rename-env {μ = μ₂} {μ₃} ρ₂ e₂)
      (flip-rename-env {μ = μ₁} {μ₃} ρ₃ e₃) h c)
ren-ren {μ₁ = μ₁} {μ₂} {μ₃} {ρ₁ = ρ₁} {ρ₂} {ρ₃} e₁ e₂ e₃ h (∀ᶜ c) =
  ∀-≅ (ren-ren {μ₁ = extᵐ μ₁} {extᵐ μ₂} {extᵐ μ₃}
    (extᵐ-rename ρ₁ e₁) (extᵐ-rename ρ₂ e₂)
    (extᵐ-rename ρ₃ e₃) (ext-h h) c)
ren-ren {μ₁ = μ₁} {μ₂} {μ₃} e₁ e₂ e₃ h (_! c) =
  !-≅ (ren-ren {μ₁ = μ₁} {μ₂} {μ₃} e₁ e₂ e₃ h c)
ren-ren {μ₁ = μ₁} {μ₂} {μ₃} e₁ e₂ e₃ h (？_ c) =
  ？-≅ (ren-ren {μ₁ = μ₁} {μ₂} {μ₃} e₁ e₂ e₃ h c)
ren-ren {μ₁ = μ₁} {μ₂} {μ₃} {ρ₁ = ρ₁} {ρ₂} {ρ₃} e₁ e₂ e₃ h
    (inst_ {B = B} c n) =
  inst-≅ (trans (renameᵗ-comp ρ₁ ρ₂ B) (renameᵗ-cong B h))
    (sr-≅ (renameᵗ-shift ρ₂ (renameᵗ ρ₁ B)) _
     ⟫ ren-sr {μ = instᵐ μ₂} {instᵐ μ₃} (extᵗ ρ₂) (instᵐ-rename ρ₂ e₂)
         (renameᵗ-shift ρ₁ B) _
     ⟫ ren-ren {μ₁ = instᵐ μ₁} {instᵐ μ₂} {instᵐ μ₃}
         (instᵐ-rename ρ₁ e₁) (instᵐ-rename ρ₂ e₂)
         (instᵐ-rename ρ₃ e₃) (ext-h h) c
     ⟫ ≅-sym (sr-≅ (renameᵗ-shift ρ₃ B) _))
ren-ren {μ₁ = μ₁} {μ₂} {μ₃} {ρ₁ = ρ₁} {ρ₂} {ρ₃} e₁ e₂ e₃ h
    (gen_ {A = A} c n) =
  gen-≅ (trans (renameᵗ-comp ρ₁ ρ₂ A) (renameᵗ-cong A h))
    (sl-≅ (renameᵗ-shift ρ₂ (renameᵗ ρ₁ A)) _
     ⟫ ren-sl {μ = genᵐ μ₂} {genᵐ μ₃} (extᵗ ρ₂) (genᵐ-rename ρ₂ e₂)
         (renameᵗ-shift ρ₁ A) _
     ⟫ ren-ren {μ₁ = genᵐ μ₁} {genᵐ μ₂} {genᵐ μ₃}
         (genᵐ-rename ρ₁ e₁) (genᵐ-rename ρ₂ e₂)
         (genᵐ-rename ρ₃ e₃) (ext-h h) c
     ⟫ ≅-sym (sl-≅ (renameᵗ-shift ρ₃ A) _))
ren-ren e₁ e₂ e₃ h bot-elim = hrefl
ren-ren e₁ e₂ e₃ h bot-intro = hrefl

------------------------------------------------------------------------
-- `sym∼`
------------------------------------------------------------------------

sym-≅ : ∀ {Δ} {μ μ′ : Env∼ Δ} {A B A′ B′}
    {c : μ ⊢ A ∼ B} {c′ : μ′ ⊢ A′ ∼ B′}
  → c ≅ᶜ c′ → sym∼ c ≅ᶜ sym∼ c′
sym-≅ hrefl = hrefl

sym-sr : ∀ {Δ} {μ : Env∼ Δ} {A B B′} (r : B ≡ B′) (c : μ ⊢ A ∼ B)
  → sym∼ (subst-right-∼ r c) ≅ᶜ sym∼ c
sym-sr refl c = hrefl

sym-sl : ∀ {Δ} {μ : Env∼ Δ} {A A′ B} (r : A ≡ A′) (c : μ ⊢ A ∼ B)
  → sym∼ (subst-left-∼ r c) ≅ᶜ sym∼ c
sym-sl refl c = hrefl

private
  flip-ext-eq : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {ρ : Δ ⇒ʳ Δ′} v
    → (∀ X → flipᵐ μ′ ‼ ρ X ≡ flipᵐ μ ‼ X)
    → ∀ X → flipᵐ (v ∷ μ′) ‼ extᵗ ρ X ≡ flipᵐ (v ∷ μ) ‼ X
  flip-ext-eq v e′ zero = refl
  flip-ext-eq v e′ (suc X) = e′ X

-- renaming commutes with `sym∼`
ren-sym : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {A B} (ρ : Δ ⇒ʳ Δ′)
    (e : ∀ X → μ′ ‼ ρ X ≡ μ ‼ X)
    (e′ : ∀ X → flipᵐ μ′ ‼ ρ X ≡ flipᵐ μ ‼ X) (c : μ ⊢ A ∼ B)
  → rename∼ {μ = flipᵐ μ} {flipᵐ μ′} ρ e′ (sym∼ c)
    ≅ᶜ sym∼ (rename∼ {μ = μ} {μ′} ρ e c)
ren-sym ρ e e′ (id ★) = hrefl
ren-sym ρ e e′ (id (‵ ι)) = hrefl
ren-sym ρ e e′ (id (＇ X)) = hrefl
ren-sym {μ = μ} {μ′} ρ e e′ (c ↦ d) =
  ↦-≅ (ren-sym {μ = μ} {μ′} ρ e e′ d)
    (ren-sym {μ = flipᵐ μ} {flipᵐ μ′} ρ
      (flip-rename-env {μ = μ} {μ′} ρ e)
      (flip-rename-env {μ = flipᵐ μ} {flipᵐ μ′} ρ e′) c)
ren-sym {μ = μ} {μ′} ρ e e′ (∀ᶜ c) =
  ∀-≅ (ren-≅ {μ = extᵐ (flipᵐ μ)} {flipᵐ (extᵐ μ)} {extᵐ (flipᵐ μ′)}
      (extᵐ-rename ρ e′) (flip-ext-eq X∼X e′)
      (transport-≅ flip-extᵐ (sym∼ c))
    ⟫ ren-sym {μ = extᵐ μ} {extᵐ μ′} (extᵗ ρ) (extᵐ-rename ρ e)
        (flip-ext-eq X∼X e′) c
    ⟫ ≅-sym (transport-≅ flip-extᵐ _))
ren-sym {μ = μ} {μ′} ρ e e′ (_! c) = ？-≅ (ren-sym {μ = μ} {μ′} ρ e e′ c)
ren-sym {μ = μ} {μ′} ρ e e′ (？_ c) = !-≅ (ren-sym {μ = μ} {μ′} ρ e e′ c)
ren-sym {μ = μ} {μ′} ρ e e′ (inst_ {B = B} c n) =
  gen-≅ refl
    (sl-≅ (renameᵗ-shift ρ B) _
     ⟫ ren-≅ {μ = genᵐ (flipᵐ μ)} {flipᵐ (instᵐ μ)} {genᵐ (flipᵐ μ′)}
         (genᵐ-rename ρ e′) (flip-ext-eq X∼★ e′)
         (transport-≅ flip-instᵐ (sym∼ c))
     ⟫ ren-sym {μ = instᵐ μ} {instᵐ μ′} (extᵗ ρ) (instᵐ-rename ρ e)
         (flip-ext-eq X∼★ e′) c
     ⟫ ≅-sym (sym-sr (renameᵗ-shift ρ B) _)
     ⟫ ≅-sym (transport-≅ flip-instᵐ _))
ren-sym {μ = μ} {μ′} ρ e e′ (gen_ {A = A} c n) =
  inst-≅ refl
    (sr-≅ (renameᵗ-shift ρ A) _
     ⟫ ren-≅ {μ = instᵐ (flipᵐ μ)} {flipᵐ (genᵐ μ)} {instᵐ (flipᵐ μ′)}
         (instᵐ-rename ρ e′) (flip-ext-eq ★∼X e′)
         (transport-≅ flip-genᵐ (sym∼ c))
     ⟫ ren-sym {μ = genᵐ μ} {genᵐ μ′} (extᵗ ρ) (genᵐ-rename ρ e)
         (flip-ext-eq ★∼X e′) c
     ⟫ ≅-sym (sym-sl (renameᵗ-shift ρ A) _)
     ⟫ ≅-sym (transport-≅ flip-genᵐ _))
ren-sym ρ e e′ bot-elim = hrefl
ren-sym ρ e e′ bot-intro = hrefl

------------------------------------------------------------------------
-- Substitution: the factorings at `★`
------------------------------------------------------------------------

subst-sr : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′} {σ} {A B B′}
    (s : SubstEnv∼ μ ν σ) (r : B ≡ B′) (c : μ ⊢ A ∼ B)
  → subst∼ s (subst-right-∼ r c) ≅ᶜ subst∼ s c
subst-sr s refl c = hrefl

subst-sl : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′} {σ} {A A′ B}
    (s : SubstEnv∼ μ ν σ) (r : A ≡ A′) (c : μ ⊢ A ∼ B)
  → subst∼ s (subst-left-∼ r c) ≅ᶜ subst∼ s c
subst-sl s refl c = hrefl

factorI-≅ : ∀ {Δ} {μ μ′ : Env∼ Δ} {A A′ : Ty (ℕ.suc Δ)}
    {x : instᵐ μ ⊢ A ∼ ★} {x′ : instᵐ μ′ ⊢ A′ ∼ ★}
    {nv : NonVar A} {nv′ : NonVar A′} {z : zero ∈ᵗ A} {z′ : zero ∈ᵗ A′}
  → x ≅ᶜ x′ → factor-inst-star x nv z ≅ᶜ factor-inst-star x′ nv′ z′
factorI-≅ {nv = nv} {nv′} {z} {z′} hrefl
  rewrite nonVar-unique nv nv′ | ∈-unique z z′ = hrefl

factorG-≅ : ∀ {Δ} {μ μ′ : Env∼ Δ} {B B′ : Ty (ℕ.suc Δ)}
    {x : genᵐ μ ⊢ ★ ∼ B} {x′ : genᵐ μ′ ⊢ ★ ∼ B′}
    {nv : NonVar B} {nv′ : NonVar B′} {z : zero ∈ᵗ B} {z′ : zero ∈ᵗ B′}
  → x ≅ᶜ x′ → factor-gen-star x nv z ≅ᶜ factor-gen-star x′ nv′ z′
factorG-≅ {nv = nv} {nv′} {z} {z′} hrefl
  rewrite nonVar-unique nv nv′ | ∈-unique z z′ = hrefl

nv-occ : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ} → NonVar A → X ∈ᵗ A → NonStar A
nv-occ nonvar-fun x = nonstar-⇒
nv-occ nonvar-all x = nonstar-∀

-- the shifted equation in the `≟Ty ★` branches of `subst∼`
sh : ∀ {Δ Δ′} (σ : Δ ⇒ˢ Δ′) {B} → substᵗ σ B ≡ ★
  → substᵗ (extsᵗ σ) (⇑ᵗ B) ≡ ⇑ᵗ ★
sh σ {B} e = trans (substᵗ-shift σ B) (cong (renameᵗ suc) e)

-- substitution commutes with the factoring of `inst` through a tag
subst-factorI : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′} {σ}
    {A : Ty (ℕ.suc Δ)} (s : SubstEnv∼ μ ν σ) (x : instᵐ μ ⊢ A ∼ ★)
    (nv : NonVar A) (z : zero ∈ᵗ A) (nv′ : NonVar (substᵗ (extsᵗ σ) A))
    (z′ : zero ∈ᵗ substᵗ (extsᵗ σ) A)
  → subst∼ s (factor-inst-star x nv z)
    ≅ᶜ factor-inst-star (subst∼ (inst-SubstEnv∼ s) x) nv′ z′
subst-factorI s (_! ⦃ Gᵍ = ★⇒★ ⦄ c) nv z nv′ z′ =
  !-≅ (inst-≅ refl (sr-≅ _ _))
subst-factorI s (_! ⦃ Gᵍ = ‵ ι ⦄ c) nv z nv′ z′ =
  !-≅ (inst-≅ refl (sr-≅ _ _))
subst-factorI s (_! ⦃ Gᵍ = ＇ zero ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ c) nv z nv′ z′ =
  ⊥-elim (inst-to-var-occurs-impossible c eq nv z)
subst-factorI s (_! ⦃ Gᵍ = ＇ zero ⦄ ⦃ G∼★ = X∼★ᶜ () ⦄ c) nv z nv′ z′
subst-factorI s (_! ⦃ Gᵍ = ＇ suc X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ c) nv z nv′ z′ =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nv (nv-occ nv z))
subst-factorI s (_! ⦃ Gᵍ = ＇ suc X ⦄ ⦃ G∼★ = X∼★ᶜ eq ⦄ c) nv z nv′ z′ =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nv (nv-occ nv z))
subst-factorI s (_! ⦃ Gᵍ = ∀★ ⦄ c) nv z nv′ z′ =
  !-≅ (inst-≅ refl (sr-≅ _ _))
subst-factorI s (？_ c) nv () nv′ z′
subst-factorI s (inst_ c n) nv z nv′ z′ = ⊥-elim (n refl)

-- substitution commutes with the factoring of `gen` through a tag
subst-factorG : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′} {σ}
    {B : Ty (ℕ.suc Δ)} (s : SubstEnv∼ μ ν σ) (x : genᵐ μ ⊢ ★ ∼ B)
    (nv : NonVar B) (z : zero ∈ᵗ B) (nv′ : NonVar (substᵗ (extsᵗ σ) B))
    (z′ : zero ∈ᵗ substᵗ (extsᵗ σ) B)
  → subst∼ s (factor-gen-star x nv z)
    ≅ᶜ factor-gen-star (subst∼ (gen-SubstEnv∼ s) x) nv′ z′
subst-factorG s (_! c ⦃ () ⦄) nv z nv′ z′
subst-factorG s (？_ ⦃ Gᵍ = ★⇒★ ⦄ c) nv z nv′ z′ =
  ？-≅ (gen-≅ refl (sl-≅ _ _))
subst-factorG s (？_ ⦃ Gᵍ = ‵ ι ⦄ c) nv z nv′ z′ =
  ？-≅ (gen-≅ refl (sl-≅ _ _))
subst-factorG s (？_ ⦃ Gᵍ = ＇ zero ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c) nv z nv′ z′ =
  ⊥-elim (gen-from-var-occurs-impossible c eq nv z)
subst-factorG s (？_ ⦃ Gᵍ = ＇ zero ⦄ ⦃ ★∼G = ★∼Xᶜ () ⦄ c) nv z nv′ z′
subst-factorG s (？_ ⦃ Gᵍ = ＇ suc X ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c) nv z nv′ z′ =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nv (nv-occ nv z))
subst-factorG s (？_ ⦃ Gᵍ = ＇ suc X ⦄ ⦃ ★∼G = ★∼Xᶜ eq ⦄ c) nv z nv′ z′ =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nv (nv-occ nv z))
subst-factorG s (？_ ⦃ Gᵍ = ∀★ ⦄ c) nv z nv′ z′ =
  ？-≅ (gen-≅ refl (sl-≅ _ _))
subst-factorG s (gen_ c n) nv z nv′ z′ = ⊥-elim (n refl)

------------------------------------------------------------------------
-- Substitution composes
------------------------------------------------------------------------

-- s₃ agrees with s₁ followed by s₂ at the variables
record Fuse {Δ₁ Δ₂ Δ₃} {μ₁ : Env∼ Δ₁} {μ₂ : Env∼ Δ₂} {μ₃ : Env∼ Δ₃}
    {σ₁ : Δ₁ ⇒ˢ Δ₂} {σ₂ : Δ₂ ⇒ˢ Δ₃} {σ₃ : Δ₁ ⇒ˢ Δ₃}
    (s₁ : SubstEnv∼ μ₁ μ₂ σ₁) (s₂ : SubstEnv∼ μ₂ μ₃ σ₂)
    (s₃ : SubstEnv∼ μ₁ μ₃ σ₃) : Set where
  field
    fself : ∀ X → subst∼ s₂ (self s₁ X) ≅ᶜ self s₃ X
    fto : ∀ X e → subst∼ s₂ (to-★ s₁ X e) ≅ᶜ to-★ s₃ X e
    ffrom : ∀ X e → subst∼ s₂ (from-★ s₁ X e) ≅ᶜ from-★ s₃ X e
    fcto : ∀ X e → subst∼ s₂ (cross-to-★ s₁ X e) ≅ᶜ cross-to-★ s₃ X e
    fcfrom : ∀ X e
      → subst∼ s₂ (cross-from-★ s₁ X e) ≅ᶜ cross-from-★ s₃ X e

  tyEq : ∀ A → substᵗ σ₂ (substᵗ σ₁ A) ≡ substᵗ σ₃ A
  tyEq A = trans (substᵗ-∘ σ₂ σ₁ A) (substᵗ-cong A (λ X → ≅-src (fself X)))

open Fuse public

-- the triples at which substitution composes, given that they are
-- closed under going under binders and under flipping
module Fusion
    (P : ∀ {Δ₁ Δ₂ Δ₃} {μ₁ : Env∼ Δ₁} {μ₂ : Env∼ Δ₂} {μ₃ : Env∼ Δ₃}
      {σ₁ : Δ₁ ⇒ˢ Δ₂} {σ₂ : Δ₂ ⇒ˢ Δ₃} {σ₃ : Δ₁ ⇒ˢ Δ₃}
      → SubstEnv∼ μ₁ μ₂ σ₁ → SubstEnv∼ μ₂ μ₃ σ₂ → SubstEnv∼ μ₁ μ₃ σ₃
      → Set)
    (P-fuse : ∀ {Δ₁ Δ₂ Δ₃} {μ₁ : Env∼ Δ₁} {μ₂ : Env∼ Δ₂} {μ₃ : Env∼ Δ₃}
      {σ₁ σ₂ σ₃} {s₁ : SubstEnv∼ μ₁ μ₂ σ₁} {s₂ : SubstEnv∼ μ₂ μ₃ σ₂}
      {s₃ : SubstEnv∼ μ₁ μ₃ σ₃} → P s₁ s₂ s₃ → Fuse s₁ s₂ s₃)
    (P-ext : ∀ {Δ₁ Δ₂ Δ₃} {μ₁ : Env∼ Δ₁} {μ₂ : Env∼ Δ₂} {μ₃ : Env∼ Δ₃}
      {σ₁ σ₂ σ₃} {s₁ : SubstEnv∼ μ₁ μ₂ σ₁} {s₂ : SubstEnv∼ μ₂ μ₃ σ₂}
      {s₃ : SubstEnv∼ μ₁ μ₃ σ₃} → P s₁ s₂ s₃
      → P (ext-SubstEnv∼ s₁) (ext-SubstEnv∼ s₂) (ext-SubstEnv∼ s₃))
    (P-inst : ∀ {Δ₁ Δ₂ Δ₃} {μ₁ : Env∼ Δ₁} {μ₂ : Env∼ Δ₂} {μ₃ : Env∼ Δ₃}
      {σ₁ σ₂ σ₃} {s₁ : SubstEnv∼ μ₁ μ₂ σ₁} {s₂ : SubstEnv∼ μ₂ μ₃ σ₂}
      {s₃ : SubstEnv∼ μ₁ μ₃ σ₃} → P s₁ s₂ s₃
      → P (inst-SubstEnv∼ s₁) (inst-SubstEnv∼ s₂) (inst-SubstEnv∼ s₃))
    (P-gen : ∀ {Δ₁ Δ₂ Δ₃} {μ₁ : Env∼ Δ₁} {μ₂ : Env∼ Δ₂} {μ₃ : Env∼ Δ₃}
      {σ₁ σ₂ σ₃} {s₁ : SubstEnv∼ μ₁ μ₂ σ₁} {s₂ : SubstEnv∼ μ₂ μ₃ σ₂}
      {s₃ : SubstEnv∼ μ₁ μ₃ σ₃} → P s₁ s₂ s₃
      → P (gen-SubstEnv∼ s₁) (gen-SubstEnv∼ s₂) (gen-SubstEnv∼ s₃))
    (P-flip : ∀ {Δ₁ Δ₂ Δ₃} {μ₁ : Env∼ Δ₁} {μ₂ : Env∼ Δ₂} {μ₃ : Env∼ Δ₃}
      {σ₁ σ₂ σ₃} {s₁ : SubstEnv∼ μ₁ μ₂ σ₁} {s₂ : SubstEnv∼ μ₂ μ₃ σ₂}
      {s₃ : SubstEnv∼ μ₁ μ₃ σ₃} → P s₁ s₂ s₃
      → P (flip-SubstEnv∼ s₁) (flip-SubstEnv∼ s₂) (flip-SubstEnv∼ s₃))
  where

  ss : ∀ {Δ₁ Δ₂ Δ₃} {μ₁ : Env∼ Δ₁} {μ₂ : Env∼ Δ₂} {μ₃ : Env∼ Δ₃}
      {σ₁ σ₂ σ₃} {s₁ : SubstEnv∼ μ₁ μ₂ σ₁} {s₂ : SubstEnv∼ μ₂ μ₃ σ₂}
      {s₃ : SubstEnv∼ μ₁ μ₃ σ₃} {A B}
    → P s₁ s₂ s₃ → (c : μ₁ ⊢ A ∼ B)
    → subst∼ s₂ (subst∼ s₁ c) ≅ᶜ subst∼ s₃ c
  ss p (id ★) = hrefl
  ss p (id (‵ ι)) = hrefl
  ss p (id (＇ X)) = fself (P-fuse p) X
  ss p (c ↦ d) = ↦-≅ (ss p d) (ss (P-flip p) c)
  ss p (∀ᶜ c) = ∀-≅ (ss (P-ext p) c)
  ss p (_! ⦃ Gᵍ = ★⇒★ ⦄ c) = !-≅ (ss p c)
  ss p (_! ⦃ Gᵍ = ‵ ι ⦄ c) = !-≅ (ss p c)
  ss p (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ (id (＇ _))) =
    fto (P-fuse p) X eq
  ss p (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ (？_ c) ⦃ () ⦄)
  ss p (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ c@(inst_ c₀ n) ⦃ a ⦄) =
    ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all a)
  ss p (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ eq ⦄ (id (＇ _))) =
    fcto (P-fuse p) X eq
  ss p (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ eq ⦄ (？_ c) ⦃ () ⦄)
  ss p (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ eq ⦄ c@(inst_ c₀ n) ⦃ a ⦄) =
    ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all a)
  ss p (_! ⦃ Gᵍ = ∀★ ⦄ c) = !-≅ (ss p c)
  ss p (？_ ⦃ Gᵍ = ★⇒★ ⦄ c) = ？-≅ (ss p c)
  ss p (？_ ⦃ Gᵍ = ‵ ι ⦄ c) = ？-≅ (ss p c)
  ss p (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ (id (＇ _))) =
    ffrom (P-fuse p) X eq
  ss p (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ (_! c) ⦃ () ⦄)
  ss p (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c@(gen_ c₀ n) ⦃ b ⦄) =
    ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all b)
  ss p (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ eq ⦄ (id (＇ _))) =
    fcfrom (P-fuse p) X eq
  ss p (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ eq ⦄ (_! c) ⦃ () ⦄)
  ss p (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ eq ⦄ c@(gen_ c₀ n) ⦃ b ⦄) =
    ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all b)
  ss p (？_ ⦃ Gᵍ = ∀★ ⦄ c) = ？-≅ (ss p c)
  ss {σ₁ = σ₁} p (inst_ {B = B} c n) with substᵗ σ₁ B ≟Ty ★
  ss {σ₁ = σ₁} {σ₂} {σ₃} p (inst_ {B = B} c n) | no n₁
      with substᵗ σ₂ (substᵗ σ₁ B) ≟Ty ★ | substᵗ σ₃ B ≟Ty ★
  ss {σ₁ = σ₁} {σ₂} {σ₃} {s₁} {s₂} p (inst_ {B = B} c n) | no n₁
      | no n₂ | no n₃ =
    inst-≅ (tyEq (P-fuse p) B)
      (sr-≅ (substᵗ-shift σ₂ (substᵗ σ₁ B)) _
       ⟫ subst-sr (inst-SubstEnv∼ s₂) (substᵗ-shift σ₁ B)
           (subst∼ (inst-SubstEnv∼ s₁) c)
       ⟫ ss (P-inst p) c ⟫ ≅-sym (sr-≅ (substᵗ-shift σ₃ B) _))
  ss {σ₁ = σ₁} {σ₂} {σ₃} p (inst_ {B = B} c n) | no n₁
      | no n₂ | yes e₃ =
    ⊥-elim (n₂ (trans (tyEq (P-fuse p) B) e₃))
  ss {σ₁ = σ₁} {σ₂} {σ₃} p (inst_ {B = B} c n) | no n₁
      | yes e₂ | no n₃ =
    ⊥-elim (n₃ (trans (sym (tyEq (P-fuse p) B)) e₂))
  ss {σ₁ = σ₁} {σ₂} {σ₃} {s₁} {s₂} p (inst_ {B = B} c n) | no n₁
      | yes e₂ | yes e₃ =
    sr-≅ (sym e₂) _
    ⟫ factorI-≅ (sr-≅ (sh σ₂ {substᵗ σ₁ B} e₂) _
       ⟫ subst-sr (inst-SubstEnv∼ s₂) (substᵗ-shift σ₁ B)
           (subst∼ (inst-SubstEnv∼ s₁) c)
       ⟫ ss (P-inst p) c ⟫ ≅-sym (sr-≅ (sh σ₃ {B} e₃) _))
    ⟫ ≅-sym (sr-≅ (sym e₃) _)
  ss {σ₁ = σ₁} {σ₂} {σ₃} p (inst_ {B = B} c n) | yes e₁
      with substᵗ σ₃ B ≟Ty ★
  ss {σ₁ = σ₁} {σ₂} {σ₃} p (inst_ {B = B} c n) | yes e₁ | no n₃ =
    ⊥-elim (n₃ (trans (sym (tyEq (P-fuse p) B)) (cong (substᵗ σ₂) e₁)))
  ss {σ₁ = σ₁} {σ₂} {σ₃} {s₁} {s₂} p (inst_ {B = B} ⦃ nv ⦄ ⦃ z ⦄ c n)
      | yes e₁ | yes e₃ =
    subst-sr s₂ (sym e₁) _
    ⟫ subst-factorI s₂
        (subst-right-∼ (sh σ₁ {B} e₁) (subst∼ (inst-SubstEnv∼ s₁) c))
        (substNonVar (extsᵗ σ₁) nv) (subst-∈ᵗ z var-∈)
        (substNonVar (extsᵗ σ₂) (substNonVar (extsᵗ σ₁) nv))
        (subst-∈ᵗ (subst-∈ᵗ z var-∈) var-∈)
    ⟫ factorI-≅ (subst-sr (inst-SubstEnv∼ s₂) (sh σ₁ {B} e₁)
           (subst∼ (inst-SubstEnv∼ s₁) c)
       ⟫ ss (P-inst p) c ⟫ ≅-sym (sr-≅ (sh σ₃ {B} e₃) _))
    ⟫ ≅-sym (sr-≅ (sym e₃) _)
  ss {σ₁ = σ₁} p (gen_ {A = A} c n) with substᵗ σ₁ A ≟Ty ★
  ss {σ₁ = σ₁} {σ₂} {σ₃} p (gen_ {A = A} c n) | no n₁
      with substᵗ σ₂ (substᵗ σ₁ A) ≟Ty ★ | substᵗ σ₃ A ≟Ty ★
  ss {σ₁ = σ₁} {σ₂} {σ₃} {s₁} {s₂} p (gen_ {A = A} c n) | no n₁
      | no n₂ | no n₃ =
    gen-≅ (tyEq (P-fuse p) A)
      (sl-≅ (substᵗ-shift σ₂ (substᵗ σ₁ A)) _
       ⟫ subst-sl (gen-SubstEnv∼ s₂) (substᵗ-shift σ₁ A)
           (subst∼ (gen-SubstEnv∼ s₁) c)
       ⟫ ss (P-gen p) c ⟫ ≅-sym (sl-≅ (substᵗ-shift σ₃ A) _))
  ss {σ₁ = σ₁} {σ₂} {σ₃} p (gen_ {A = A} c n) | no n₁
      | no n₂ | yes e₃ =
    ⊥-elim (n₂ (trans (tyEq (P-fuse p) A) e₃))
  ss {σ₁ = σ₁} {σ₂} {σ₃} p (gen_ {A = A} c n) | no n₁
      | yes e₂ | no n₃ =
    ⊥-elim (n₃ (trans (sym (tyEq (P-fuse p) A)) e₂))
  ss {σ₁ = σ₁} {σ₂} {σ₃} {s₁} {s₂} p (gen_ {A = A} c n) | no n₁
      | yes e₂ | yes e₃ =
    sl-≅ (sym e₂) _
    ⟫ factorG-≅ (sl-≅ (sh σ₂ {substᵗ σ₁ A} e₂) _
       ⟫ subst-sl (gen-SubstEnv∼ s₂) (substᵗ-shift σ₁ A)
           (subst∼ (gen-SubstEnv∼ s₁) c)
       ⟫ ss (P-gen p) c ⟫ ≅-sym (sl-≅ (sh σ₃ {A} e₃) _))
    ⟫ ≅-sym (sl-≅ (sym e₃) _)
  ss {σ₁ = σ₁} {σ₂} {σ₃} p (gen_ {A = A} c n) | yes e₁
      with substᵗ σ₃ A ≟Ty ★
  ss {σ₁ = σ₁} {σ₂} {σ₃} p (gen_ {A = A} c n) | yes e₁ | no n₃ =
    ⊥-elim (n₃ (trans (sym (tyEq (P-fuse p) A)) (cong (substᵗ σ₂) e₁)))
  ss {σ₁ = σ₁} {σ₂} {σ₃} {s₁} {s₂} p (gen_ {A = A} ⦃ nv ⦄ ⦃ z ⦄ c n)
      | yes e₁ | yes e₃ =
    subst-sl s₂ (sym e₁) _
    ⟫ subst-factorG s₂
        (subst-left-∼ (sh σ₁ {A} e₁) (subst∼ (gen-SubstEnv∼ s₁) c))
        (substNonVar (extsᵗ σ₁) nv) (subst-∈ᵗ z var-∈)
        (substNonVar (extsᵗ σ₂) (substNonVar (extsᵗ σ₁) nv))
        (subst-∈ᵗ (subst-∈ᵗ z var-∈) var-∈)
    ⟫ factorG-≅ (subst-sl (gen-SubstEnv∼ s₂) (sh σ₁ {A} e₁)
           (subst∼ (gen-SubstEnv∼ s₁) c)
       ⟫ ss (P-gen p) c ⟫ ≅-sym (sl-≅ (sh σ₃ {A} e₃) _))
    ⟫ ≅-sym (sl-≅ (sym e₃) _)
  ss p bot-elim = hrefl
  ss p bot-intro = hrefl

------------------------------------------------------------------------
-- Helpers for the instances
------------------------------------------------------------------------

private
  ≡→≅ : ∀ {Δ} {μ : Env∼ Δ} {A B} {c c′ : μ ⊢ A ∼ B} → c ≡ c′ → c ≅ᶜ c′
  ≡→≅ refl = hrefl

  ren≡★ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {A : Ty Δ} → renameᵗ ρ A ≡ ★ → A ≡ ★
  ren≡★ ρ {＇ X} ()
  ren≡★ ρ {‵ ι} ()
  ren≡★ ρ {★} e = refl
  ren≡★ ρ {A ⇒ B} ()
  ren≡★ ρ {`∀ A} ()

subst-≅ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′} {σ} {A B}
    (s : SubstEnv∼ μ ν σ) {c c′ : μ ⊢ A ∼ B}
  → c ≅ᶜ c′ → subst∼ s c ≅ᶜ subst∼ s c′
subst-≅ s hrefl = hrefl

-- the shift into one more variable, of mode v
⇑ᶜ : ∀ {Δ} {v} {μ : Env∼ Δ} {A B} → μ ⊢ A ∼ B → (v ∷ μ) ⊢ ⇑ᵗ A ∼ ⇑ᵗ B
⇑ᶜ {v = v} {μ} c = rename∼ {μ = μ} {v ∷ μ} suc (λ Y → refl) c

⇑-≅ : ∀ {Δ} {v} {μ μ₂ : Env∼ Δ} {A B A₂ B₂}
    {c : μ ⊢ A ∼ B} {c₂ : μ₂ ⊢ A₂ ∼ B₂}
  → c ≅ᶜ c₂ → ⇑ᶜ {v = v} c ≅ᶜ ⇑ᶜ {v = v} c₂
⇑-≅ hrefl = hrefl

private
  ⇑-cong : ∀ {Δ} {v} {μ : Env∼ Δ} {A B} {T : Set} (f : T → μ ⊢ A ∼ B)
      {x y : T}
    → x ≡ y → ⇑ᶜ {v = v} (f x) ≅ᶜ ⇑ᶜ {v = v} (f y)
  ⇑-cong f refl = hrefl

------------------------------------------------------------------------
-- Renaming: the factorings at `★`
------------------------------------------------------------------------

-- renaming commutes with the factoring of `inst` through a tag
ren-factorI : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {A : Ty (ℕ.suc Δ)}
    (ρ : Δ ⇒ʳ Δ′) (e : ∀ X → μ′ ‼ ρ X ≡ μ ‼ X)
    (x : instᵐ μ ⊢ A ∼ ★) (nv : NonVar A) (z : zero ∈ᵗ A)
    {A″} {x″ : instᵐ μ′ ⊢ A″ ∼ ★} {nv″ : NonVar A″} {z″ : zero ∈ᵗ A″}
  → x″ ≅ᶜ rename∼ {μ = instᵐ μ} {instᵐ μ′} (extᵗ ρ) (instᵐ-rename ρ e) x
  → rename∼ {μ = μ} {μ′} ρ e (factor-inst-star x nv z)
    ≅ᶜ factor-inst-star x″ nv″ z″
ren-factorI ρ e (_! ⦃ Gᵍ = ★⇒★ ⦄ c) nv z hrefl =
  !-≅ (inst-≅ refl (sr-≅ _ _))
ren-factorI ρ e (_! ⦃ Gᵍ = ‵ ι ⦄ c) nv z hrefl =
  !-≅ (inst-≅ refl (sr-≅ _ _))
ren-factorI ρ e (_! ⦃ Gᵍ = ＇ zero ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ c) nv z q =
  ⊥-elim (inst-to-var-occurs-impossible c eq nv z)
ren-factorI ρ e (_! ⦃ Gᵍ = ＇ zero ⦄ ⦃ G∼★ = X∼★ᶜ () ⦄ c) nv z q
ren-factorI ρ e (_! ⦃ Gᵍ = ＇ suc X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ c) nv z q =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nv (nv-occ nv z))
ren-factorI ρ e (_! ⦃ Gᵍ = ＇ suc X ⦄ ⦃ G∼★ = X∼★ᶜ eq ⦄ c) nv z q =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nv (nv-occ nv z))
ren-factorI ρ e (_! ⦃ Gᵍ = ∀★ ⦄ c) nv z hrefl =
  !-≅ (inst-≅ refl (sr-≅ _ _))
ren-factorI ρ e (？_ c) nv () q
ren-factorI ρ e (inst_ c n) nv z q = ⊥-elim (n refl)

-- renaming commutes with the factoring of `gen` through a tag
ren-factorG : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {B : Ty (ℕ.suc Δ)}
    (ρ : Δ ⇒ʳ Δ′) (e : ∀ X → μ′ ‼ ρ X ≡ μ ‼ X)
    (x : genᵐ μ ⊢ ★ ∼ B) (nv : NonVar B) (z : zero ∈ᵗ B)
    {B″} {x″ : genᵐ μ′ ⊢ ★ ∼ B″} {nv″ : NonVar B″} {z″ : zero ∈ᵗ B″}
  → x″ ≅ᶜ rename∼ {μ = genᵐ μ} {genᵐ μ′} (extᵗ ρ) (genᵐ-rename ρ e) x
  → rename∼ {μ = μ} {μ′} ρ e (factor-gen-star x nv z)
    ≅ᶜ factor-gen-star x″ nv″ z″
ren-factorG ρ e (_! c ⦃ () ⦄) nv z q
ren-factorG ρ e (？_ ⦃ Gᵍ = ★⇒★ ⦄ c) nv z hrefl =
  ？-≅ (gen-≅ refl (sl-≅ _ _))
ren-factorG ρ e (？_ ⦃ Gᵍ = ‵ ι ⦄ c) nv z hrefl =
  ？-≅ (gen-≅ refl (sl-≅ _ _))
ren-factorG ρ e (？_ ⦃ Gᵍ = ＇ zero ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c) nv z q =
  ⊥-elim (gen-from-var-occurs-impossible c eq nv z)
ren-factorG ρ e (？_ ⦃ Gᵍ = ＇ zero ⦄ ⦃ ★∼G = ★∼Xᶜ () ⦄ c) nv z q
ren-factorG ρ e (？_ ⦃ Gᵍ = ＇ suc X ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c) nv z q =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nv (nv-occ nv z))
ren-factorG ρ e (？_ ⦃ Gᵍ = ＇ suc X ⦄ ⦃ ★∼G = ★∼Xᶜ eq ⦄ c) nv z q =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nv (nv-occ nv z))
ren-factorG ρ e (？_ ⦃ Gᵍ = ∀★ ⦄ c) nv z hrefl =
  ？-≅ (gen-≅ refl (sl-≅ _ _))
ren-factorG ρ e (gen_ c n) nv z q = ⊥-elim (n refl)

------------------------------------------------------------------------
-- Substitution after renaming
------------------------------------------------------------------------

-- s₂ at ρ X agrees with s₃ at X
record SRel {Δ Δ′ Θ} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {ν : Env∼ Θ}
    (ρ : Δ ⇒ʳ Δ′) {σ₂ : Δ′ ⇒ˢ Θ} {σ₃ : Δ ⇒ˢ Θ}
    (s₂ : SubstEnv∼ μ′ ν σ₂) (s₃ : SubstEnv∼ μ ν σ₃) : Set where
  field
    rself : ∀ X → self s₂ (ρ X) ≅ᶜ self s₃ X
    rto : ∀ X e e′ → to-★ s₂ (ρ X) e ≅ᶜ to-★ s₃ X e′
    rfrom : ∀ X e e′ → from-★ s₂ (ρ X) e ≅ᶜ from-★ s₃ X e′
    rcto : ∀ X e e′ → cross-to-★ s₂ (ρ X) e ≅ᶜ cross-to-★ s₃ X e′
    rcfrom : ∀ X e e′
      → cross-from-★ s₂ (ρ X) e ≅ᶜ cross-from-★ s₃ X e′

  rtyEq : ∀ A → substᵗ σ₂ (renameᵗ ρ A) ≡ substᵗ σ₃ A
  rtyEq A =
    trans (substᵗ-rename σ₂ ρ A) (substᵗ-cong A (λ X → ≅-src (rself X)))

open SRel public

module _ {Δ Δ′ Θ} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {ν : Env∼ Θ}
    {ρ : Δ ⇒ʳ Δ′} {σ₂ : Δ′ ⇒ˢ Θ} {σ₃ : Δ ⇒ˢ Θ}
    {s₂ : SubstEnv∼ μ′ ν σ₂} {s₃ : SubstEnv∼ μ ν σ₃} where

  sr-ext : SRel ρ s₂ s₃
    → SRel (extᵗ ρ) (ext-SubstEnv∼ s₂) (ext-SubstEnv∼ s₃)
  rself (sr-ext r) zero = hrefl
  rself (sr-ext r) (suc X) = ⇑-≅ (rself r X)
  rto (sr-ext r) zero () e′
  rto (sr-ext r) (suc X) e e′ = ⇑-≅ (rto r X e e′)
  rfrom (sr-ext r) zero () e′
  rfrom (sr-ext r) (suc X) e e′ = ⇑-≅ (rfrom r X e e′)
  rcto (sr-ext r) zero () e′
  rcto (sr-ext r) (suc X) e e′ = ⇑-≅ (rcto r X e e′)
  rcfrom (sr-ext r) zero () e′
  rcfrom (sr-ext r) (suc X) e e′ = ⇑-≅ (rcfrom r X e e′)

  sr-inst : SRel ρ s₂ s₃
    → SRel (extᵗ ρ) (inst-SubstEnv∼ s₂) (inst-SubstEnv∼ s₃)
  rself (sr-inst r) zero = hrefl
  rself (sr-inst r) (suc X) = ⇑-≅ (rself r X)
  rto (sr-inst r) zero e e′ = hrefl
  rto (sr-inst r) (suc X) e e′ = ⇑-≅ (rto r X e e′)
  rfrom (sr-inst r) zero () e′
  rfrom (sr-inst r) (suc X) e e′ = ⇑-≅ (rfrom r X e e′)
  rcto (sr-inst r) zero () e′
  rcto (sr-inst r) (suc X) e e′ = ⇑-≅ (rcto r X e e′)
  rcfrom (sr-inst r) zero () e′
  rcfrom (sr-inst r) (suc X) e e′ = ⇑-≅ (rcfrom r X e e′)

  sr-gen : SRel ρ s₂ s₃
    → SRel (extᵗ ρ) (gen-SubstEnv∼ s₂) (gen-SubstEnv∼ s₃)
  rself (sr-gen r) zero = hrefl
  rself (sr-gen r) (suc X) = ⇑-≅ (rself r X)
  rto (sr-gen r) zero () e′
  rto (sr-gen r) (suc X) e e′ = ⇑-≅ (rto r X e e′)
  rfrom (sr-gen r) zero e e′ = hrefl
  rfrom (sr-gen r) (suc X) e e′ = ⇑-≅ (rfrom r X e e′)
  rcto (sr-gen r) zero () e′
  rcto (sr-gen r) (suc X) e e′ = ⇑-≅ (rcto r X e e′)
  rcfrom (sr-gen r) zero () e′
  rcfrom (sr-gen r) (suc X) e e′ = ⇑-≅ (rcfrom r X e e′)

  sr-flip : SRel ρ s₂ s₃
    → SRel ρ (flip-SubstEnv∼ s₂) (flip-SubstEnv∼ s₃)
  rself (sr-flip r) X = sym-≅ (rself r X)
  rto (sr-flip r) X e e′ =
    sym-≅ (rfrom r X (flipVar∼-to-X∼★ (flipᵐ-‼⁻ μ′ (ρ X) e))
      (flipVar∼-to-X∼★ (flipᵐ-‼⁻ μ X e′)))
  rfrom (sr-flip r) X e e′ =
    sym-≅ (rto r X (flipVar∼-to-★∼X (flipᵐ-‼⁻ μ′ (ρ X) e))
      (flipVar∼-to-★∼X (flipᵐ-‼⁻ μ X e′)))
  rcto (sr-flip r) X e e′ =
    sym-≅ (rcfrom r X (flipVar∼-to-★∼X∼★ (flipᵐ-‼⁻ μ′ (ρ X) e))
      (flipVar∼-to-★∼X∼★ (flipᵐ-‼⁻ μ X e′)))
  rcfrom (sr-flip r) X e e′ =
    sym-≅ (rcto r X (flipVar∼-to-★∼X∼★ (flipᵐ-‼⁻ μ′ (ρ X) e))
      (flipVar∼-to-★∼X∼★ (flipᵐ-‼⁻ μ X e′)))

-- substitution after renaming is substitution
srn : ∀ {Δ Δ′ Θ} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {ν : Env∼ Θ}
    {σ₂ : Δ′ ⇒ˢ Θ} {σ₃ : Δ ⇒ˢ Θ} {s₂ : SubstEnv∼ μ′ ν σ₂}
    {s₃ : SubstEnv∼ μ ν σ₃} {A B} (ρ : Δ ⇒ʳ Δ′)
    (eq : ∀ X → μ′ ‼ ρ X ≡ μ ‼ X)
  → SRel ρ s₂ s₃ → (c : μ ⊢ A ∼ B)
  → subst∼ s₂ (rename∼ {μ = μ} {μ′} ρ eq c) ≅ᶜ subst∼ s₃ c
srn ρ eq r (id ★) = hrefl
srn ρ eq r (id (‵ ι)) = hrefl
srn ρ eq r (id (＇ X)) = rself r X
srn {μ = μ} {μ′} ρ eq r (c ↦ d) =
  ↦-≅ (srn ρ eq r d)
    (srn {μ = flipᵐ μ} {flipᵐ μ′} ρ (flip-rename-env {μ = μ} {μ′} ρ eq)
      (sr-flip r) c)
srn {μ = μ} {μ′} ρ eq r (∀ᶜ c) =
  ∀-≅ (srn {μ = extᵐ μ} {extᵐ μ′} (extᵗ ρ) (extᵐ-rename ρ eq)
    (sr-ext r) c)
srn ρ eq r (_! ⦃ Gᵍ = ★⇒★ ⦄ c) = !-≅ (srn ρ eq r c)
srn ρ eq r (_! ⦃ Gᵍ = ‵ ι ⦄ c) = !-≅ (srn ρ eq r c)
srn ρ eq r (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ e ⦄ (id (＇ _))) =
  rto r X (trans (eq X) e) e
srn ρ eq r (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ e ⦄ (？_ c) ⦃ () ⦄)
srn ρ eq r (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ e ⦄ c@(inst_ c₀ n) ⦃ a ⦄) =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all a)
srn ρ eq r (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ e ⦄ (id (＇ _))) =
  rcto r X (trans (eq X) e) e
srn ρ eq r (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ e ⦄ (？_ c) ⦃ () ⦄)
srn ρ eq r (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ e ⦄ c@(inst_ c₀ n) ⦃ a ⦄) =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all a)
srn ρ eq r (_! ⦃ Gᵍ = ∀★ ⦄ c) = !-≅ (srn ρ eq r c)
srn ρ eq r (？_ ⦃ Gᵍ = ★⇒★ ⦄ c) = ？-≅ (srn ρ eq r c)
srn ρ eq r (？_ ⦃ Gᵍ = ‵ ι ⦄ c) = ？-≅ (srn ρ eq r c)
srn ρ eq r (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ e ⦄ (id (＇ _))) =
  rfrom r X (trans (eq X) e) e
srn ρ eq r (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ e ⦄ (_! c) ⦃ () ⦄)
srn ρ eq r (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ e ⦄ c@(gen_ c₀ n) ⦃ b ⦄) =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all b)
srn ρ eq r (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ e ⦄ (id (＇ _))) =
  rcfrom r X (trans (eq X) e) e
srn ρ eq r (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ e ⦄ (_! c) ⦃ () ⦄)
srn ρ eq r (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ e ⦄ c@(gen_ c₀ n) ⦃ b ⦄) =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all b)
srn ρ eq r (？_ ⦃ Gᵍ = ∀★ ⦄ c) = ？-≅ (srn ρ eq r c)
srn {σ₂ = σ₂} {σ₃} ρ eq r (inst_ {B = B} c n)
    with substᵗ σ₂ (renameᵗ ρ B) ≟Ty ★ | substᵗ σ₃ B ≟Ty ★
srn {μ = μ} {μ′} {σ₂ = σ₂} {σ₃} {s₂} ρ eq r (inst_ {B = B} c n)
    | no n₂ | no n₃ =
  inst-≅ (rtyEq r B)
    (sr-≅ (substᵗ-shift σ₂ (renameᵗ ρ B)) _
     ⟫ subst-sr (inst-SubstEnv∼ s₂) (renameᵗ-shift ρ B) _
     ⟫ srn {μ = instᵐ μ} {instᵐ μ′} (extᵗ ρ) (instᵐ-rename ρ eq)
         (sr-inst r) c
     ⟫ ≅-sym (sr-≅ (substᵗ-shift σ₃ B) _))
srn {σ₂ = σ₂} {σ₃} ρ eq r (inst_ {B = B} c n) | no n₂ | yes e₃ =
  ⊥-elim (n₂ (trans (rtyEq r B) e₃))
srn {σ₂ = σ₂} {σ₃} ρ eq r (inst_ {B = B} c n) | yes e₂ | no n₃ =
  ⊥-elim (n₃ (trans (sym (rtyEq r B)) e₂))
srn {μ = μ} {μ′} {σ₂ = σ₂} {σ₃} {s₂} ρ eq r (inst_ {B = B} c n)
    | yes e₂ | yes e₃ =
  sr-≅ (sym e₂) _
  ⟫ factorI-≅ (sr-≅ (sh σ₂ {renameᵗ ρ B} e₂) _
     ⟫ subst-sr (inst-SubstEnv∼ s₂) (renameᵗ-shift ρ B) _
     ⟫ srn {μ = instᵐ μ} {instᵐ μ′} (extᵗ ρ) (instᵐ-rename ρ eq)
         (sr-inst r) c
     ⟫ ≅-sym (sr-≅ (sh σ₃ {B} e₃) _))
  ⟫ ≅-sym (sr-≅ (sym e₃) _)
srn {σ₂ = σ₂} {σ₃} ρ eq r (gen_ {A = A} c n)
    with substᵗ σ₂ (renameᵗ ρ A) ≟Ty ★ | substᵗ σ₃ A ≟Ty ★
srn {μ = μ} {μ′} {σ₂ = σ₂} {σ₃} {s₂} ρ eq r (gen_ {A = A} c n)
    | no n₂ | no n₃ =
  gen-≅ (rtyEq r A)
    (sl-≅ (substᵗ-shift σ₂ (renameᵗ ρ A)) _
     ⟫ subst-sl (gen-SubstEnv∼ s₂) (renameᵗ-shift ρ A) _
     ⟫ srn {μ = genᵐ μ} {genᵐ μ′} (extᵗ ρ) (genᵐ-rename ρ eq)
         (sr-gen r) c
     ⟫ ≅-sym (sl-≅ (substᵗ-shift σ₃ A) _))
srn {σ₂ = σ₂} {σ₃} ρ eq r (gen_ {A = A} c n) | no n₂ | yes e₃ =
  ⊥-elim (n₂ (trans (rtyEq r A) e₃))
srn {σ₂ = σ₂} {σ₃} ρ eq r (gen_ {A = A} c n) | yes e₂ | no n₃ =
  ⊥-elim (n₃ (trans (sym (rtyEq r A)) e₂))
srn {μ = μ} {μ′} {σ₂ = σ₂} {σ₃} {s₂} ρ eq r (gen_ {A = A} c n)
    | yes e₂ | yes e₃ =
  sl-≅ (sym e₂) _
  ⟫ factorG-≅ (sl-≅ (sh σ₂ {renameᵗ ρ A} e₂) _
     ⟫ subst-sl (gen-SubstEnv∼ s₂) (renameᵗ-shift ρ A) _
     ⟫ srn {μ = genᵐ μ} {genᵐ μ′} (extᵗ ρ) (genᵐ-rename ρ eq)
         (sr-gen r) c
     ⟫ ≅-sym (sl-≅ (sh σ₃ {A} e₃) _))
  ⟫ ≅-sym (sl-≅ (sym e₃) _)
srn ρ eq r bot-elim = hrefl
srn ρ eq r bot-intro = hrefl

------------------------------------------------------------------------
-- Renaming after substitution
------------------------------------------------------------------------

-- s′ agrees with s followed by the renaming ρ
record RRel {Δ Θ Θ′} {μ : Env∼ Δ} {ν : Env∼ Θ} {ν′ : Env∼ Θ′}
    (ρ : Θ ⇒ʳ Θ′) (eν : ∀ X → ν′ ‼ ρ X ≡ ν ‼ X) {σ : Δ ⇒ˢ Θ}
    {σ′ : Δ ⇒ˢ Θ′} (s : SubstEnv∼ μ ν σ) (s′ : SubstEnv∼ μ ν′ σ′)
    : Set where
  field
    qself : ∀ X → self s′ X ≅ᶜ rename∼ {μ = ν} {ν′} ρ eν (self s X)
    qto : ∀ X e
      → to-★ s′ X e ≅ᶜ rename∼ {μ = ν} {ν′} ρ eν (to-★ s X e)
    qfrom : ∀ X e
      → from-★ s′ X e ≅ᶜ rename∼ {μ = ν} {ν′} ρ eν (from-★ s X e)
    qcto : ∀ X e → cross-to-★ s′ X e
      ≅ᶜ rename∼ {μ = ν} {ν′} ρ eν (cross-to-★ s X e)
    qcfrom : ∀ X e → cross-from-★ s′ X e
      ≅ᶜ rename∼ {μ = ν} {ν′} ρ eν (cross-from-★ s X e)

  qtyEq : ∀ A → renameᵗ ρ (substᵗ σ A) ≡ substᵗ σ′ A
  qtyEq A = trans (renameᵗ-subst ρ σ A)
    (substᵗ-cong A (λ X → sym (≅-src (qself X))))

open RRel public

private
  -- a renamed field, shifted under one more variable
  rq-suc : ∀ {Θ Θ′} {v} {ν : Env∼ Θ} {ν′ : Env∼ Θ′} (ρ : Θ ⇒ʳ Θ′)
      (eν : ∀ X → ν′ ‼ ρ X ≡ ν ‼ X)
      (e₂ : ∀ X → (v ∷ ν′) ‼ extᵗ ρ X ≡ (v ∷ ν) ‼ X)
      {A B A′ B′} (c : ν ⊢ A ∼ B) {c′ : ν′ ⊢ A′ ∼ B′}
    → c′ ≅ᶜ rename∼ {μ = ν} {ν′} ρ eν c
    → ⇑ᶜ {v = v} c′
      ≅ᶜ rename∼ {μ = v ∷ ν} {v ∷ ν′} (extᵗ ρ) e₂ (⇑ᶜ {v = v} c)
  rq-suc {v = v} {ν} {ν′} ρ eν e₂ c h =
    ⇑-≅ h
    ⟫ ren-ren {μ₁ = ν} {ν′} {v ∷ ν′} {ρ₁ = ρ} {suc} {λ X → suc (ρ X)}
        eν (λ Y → refl) eν (λ X → refl) c
    ⟫ ≅-sym (ren-ren {μ₁ = ν} {v ∷ ν} {v ∷ ν′} {ρ₁ = suc} {extᵗ ρ}
        {λ X → suc (ρ X)} (λ Y → refl) e₂ eν (λ X → refl) c)

module _ {Δ Θ Θ′} {μ : Env∼ Δ} {ν : Env∼ Θ} {ν′ : Env∼ Θ′}
    {ρ : Θ ⇒ʳ Θ′} {eν : ∀ X → ν′ ‼ ρ X ≡ ν ‼ X} {σ : Δ ⇒ˢ Θ}
    {σ′ : Δ ⇒ˢ Θ′} {s : SubstEnv∼ μ ν σ} {s′ : SubstEnv∼ μ ν′ σ′} where

  rq-ext : RRel ρ eν s s′
    → RRel (extᵗ ρ) (extᵐ-rename {μ = ν} {ν′} ρ eν) (ext-SubstEnv∼ s)
        (ext-SubstEnv∼ s′)
  qself (rq-ext q) zero = hrefl
  qself (rq-ext q) (suc X) =
    rq-suc ρ eν (extᵐ-rename ρ eν) (self s X) (qself q X)
  qto (rq-ext q) zero ()
  qto (rq-ext q) (suc X) e =
    rq-suc ρ eν (extᵐ-rename ρ eν) (to-★ s X e) (qto q X e)
  qfrom (rq-ext q) zero ()
  qfrom (rq-ext q) (suc X) e =
    rq-suc ρ eν (extᵐ-rename ρ eν) (from-★ s X e) (qfrom q X e)
  qcto (rq-ext q) zero ()
  qcto (rq-ext q) (suc X) e =
    rq-suc ρ eν (extᵐ-rename ρ eν) (cross-to-★ s X e) (qcto q X e)
  qcfrom (rq-ext q) zero ()
  qcfrom (rq-ext q) (suc X) e =
    rq-suc ρ eν (extᵐ-rename ρ eν) (cross-from-★ s X e) (qcfrom q X e)

  rq-inst : RRel ρ eν s s′
    → RRel (extᵗ ρ) (instᵐ-rename {μ = ν} {ν′} ρ eν) (inst-SubstEnv∼ s)
        (inst-SubstEnv∼ s′)
  qself (rq-inst q) zero = hrefl
  qself (rq-inst q) (suc X) =
    rq-suc ρ eν (instᵐ-rename ρ eν) (self s X) (qself q X)
  qto (rq-inst q) zero e = !-≅ hrefl
  qto (rq-inst q) (suc X) e =
    rq-suc ρ eν (instᵐ-rename ρ eν) (to-★ s X e) (qto q X e)
  qfrom (rq-inst q) zero ()
  qfrom (rq-inst q) (suc X) e =
    rq-suc ρ eν (instᵐ-rename ρ eν) (from-★ s X e) (qfrom q X e)
  qcto (rq-inst q) zero ()
  qcto (rq-inst q) (suc X) e =
    rq-suc ρ eν (instᵐ-rename ρ eν) (cross-to-★ s X e) (qcto q X e)
  qcfrom (rq-inst q) zero ()
  qcfrom (rq-inst q) (suc X) e =
    rq-suc ρ eν (instᵐ-rename ρ eν) (cross-from-★ s X e) (qcfrom q X e)

  rq-gen : RRel ρ eν s s′
    → RRel (extᵗ ρ) (genᵐ-rename {μ = ν} {ν′} ρ eν) (gen-SubstEnv∼ s)
        (gen-SubstEnv∼ s′)
  qself (rq-gen q) zero = hrefl
  qself (rq-gen q) (suc X) =
    rq-suc ρ eν (genᵐ-rename ρ eν) (self s X) (qself q X)
  qto (rq-gen q) zero ()
  qto (rq-gen q) (suc X) e =
    rq-suc ρ eν (genᵐ-rename ρ eν) (to-★ s X e) (qto q X e)
  qfrom (rq-gen q) zero e = ？-≅ hrefl
  qfrom (rq-gen q) (suc X) e =
    rq-suc ρ eν (genᵐ-rename ρ eν) (from-★ s X e) (qfrom q X e)
  qcto (rq-gen q) zero ()
  qcto (rq-gen q) (suc X) e =
    rq-suc ρ eν (genᵐ-rename ρ eν) (cross-to-★ s X e) (qcto q X e)
  qcfrom (rq-gen q) zero ()
  qcfrom (rq-gen q) (suc X) e =
    rq-suc ρ eν (genᵐ-rename ρ eν) (cross-from-★ s X e) (qcfrom q X e)

  rq-flip : RRel ρ eν s s′
    → RRel ρ (flip-rename-env {μ = ν} {ν′} ρ eν) (flip-SubstEnv∼ s)
        (flip-SubstEnv∼ s′)
  qself (rq-flip q) X =
    sym-≅ (qself q X) ⟫ ≅-sym (ren-sym {μ = ν} {ν′} ρ eν fe (self s X))
    where fe = flip-rename-env {μ = ν} {ν′} ρ eν
  qto (rq-flip q) X e =
    sym-≅ (qfrom q X P) ⟫ ≅-sym (ren-sym {μ = ν} {ν′} ρ eν fe (from-★ s X P))
    where fe = flip-rename-env {μ = ν} {ν′} ρ eν
          P = flipVar∼-to-X∼★ (flipᵐ-‼⁻ μ X e)
  qfrom (rq-flip q) X e =
    sym-≅ (qto q X P) ⟫ ≅-sym (ren-sym {μ = ν} {ν′} ρ eν fe (to-★ s X P))
    where fe = flip-rename-env {μ = ν} {ν′} ρ eν
          P = flipVar∼-to-★∼X (flipᵐ-‼⁻ μ X e)
  qcto (rq-flip q) X e =
    sym-≅ (qcfrom q X P)
    ⟫ ≅-sym (ren-sym {μ = ν} {ν′} ρ eν fe (cross-from-★ s X P))
    where fe = flip-rename-env {μ = ν} {ν′} ρ eν
          P = flipVar∼-to-★∼X∼★ (flipᵐ-‼⁻ μ X e)
  qcfrom (rq-flip q) X e =
    sym-≅ (qcto q X P)
    ⟫ ≅-sym (ren-sym {μ = ν} {ν′} ρ eν fe (cross-to-★ s X P))
    where fe = flip-rename-env {μ = ν} {ν′} ρ eν
          P = flipVar∼-to-★∼X∼★ (flipᵐ-‼⁻ μ X e)

-- renaming after substitution is substitution
rns : ∀ {Δ Θ Θ′} {μ : Env∼ Δ} {ν : Env∼ Θ} {ν′ : Env∼ Θ′}
    {σ : Δ ⇒ˢ Θ} {σ′ : Δ ⇒ˢ Θ′} {s : SubstEnv∼ μ ν σ}
    {s′ : SubstEnv∼ μ ν′ σ′} {A B} (ρ : Θ ⇒ʳ Θ′)
    (eν : ∀ X → ν′ ‼ ρ X ≡ ν ‼ X)
  → RRel ρ eν s s′ → (c : μ ⊢ A ∼ B)
  → rename∼ {μ = ν} {ν′} ρ eν (subst∼ s c) ≅ᶜ subst∼ s′ c
rns ρ eν q (id ★) = hrefl
rns ρ eν q (id (‵ ι)) = hrefl
rns ρ eν q (id (＇ X)) = ≅-sym (qself q X)
rns {ν = ν} {ν′} ρ eν q (c ↦ d) =
  ↦-≅ (rns ρ eν q d)
    (rns {ν = flipᵐ ν} {flipᵐ ν′} ρ (flip-rename-env {μ = ν} {ν′} ρ eν)
      (rq-flip q) c)
rns {ν = ν} {ν′} ρ eν q (∀ᶜ c) =
  ∀-≅ (rns {ν = extᵐ ν} {extᵐ ν′} (extᵗ ρ) (extᵐ-rename ρ eν)
    (rq-ext q) c)
rns ρ eν q (_! ⦃ Gᵍ = ★⇒★ ⦄ c) = !-≅ (rns ρ eν q c)
rns ρ eν q (_! ⦃ Gᵍ = ‵ ι ⦄ c) = !-≅ (rns ρ eν q c)
rns ρ eν q (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ e ⦄ (id (＇ _))) =
  ≅-sym (qto q X e)
rns ρ eν q (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ e ⦄ (？_ c) ⦃ () ⦄)
rns ρ eν q (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ e ⦄ c@(inst_ c₀ n) ⦃ a ⦄) =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all a)
rns ρ eν q (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ e ⦄ (id (＇ _))) =
  ≅-sym (qcto q X e)
rns ρ eν q (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ e ⦄ (？_ c) ⦃ () ⦄)
rns ρ eν q (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ e ⦄ c@(inst_ c₀ n) ⦃ a ⦄) =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all a)
rns ρ eν q (_! ⦃ Gᵍ = ∀★ ⦄ c) = !-≅ (rns ρ eν q c)
rns ρ eν q (？_ ⦃ Gᵍ = ★⇒★ ⦄ c) = ？-≅ (rns ρ eν q c)
rns ρ eν q (？_ ⦃ Gᵍ = ‵ ι ⦄ c) = ？-≅ (rns ρ eν q c)
rns ρ eν q (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ e ⦄ (id (＇ _))) =
  ≅-sym (qfrom q X e)
rns ρ eν q (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ e ⦄ (_! c) ⦃ () ⦄)
rns ρ eν q (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ e ⦄ c@(gen_ c₀ n) ⦃ b ⦄) =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all b)
rns ρ eν q (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ e ⦄ (id (＇ _))) =
  ≅-sym (qcfrom q X e)
rns ρ eν q (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ e ⦄ (_! c) ⦃ () ⦄)
rns ρ eν q (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ e ⦄ c@(gen_ c₀ n) ⦃ b ⦄) =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all b)
rns ρ eν q (？_ ⦃ Gᵍ = ∀★ ⦄ c) = ？-≅ (rns ρ eν q c)
rns {σ = σ} {σ′} ρ eν q (inst_ {B = B} c n)
    with substᵗ σ B ≟Ty ★ | substᵗ σ′ B ≟Ty ★
rns {ν = ν} {ν′} {σ = σ} {σ′} ρ eν q (inst_ {B = B} c n)
    | no n₁ | no n₃ =
  inst-≅ (qtyEq q B)
    (sr-≅ (renameᵗ-shift ρ (substᵗ σ B)) _
     ⟫ ren-sr {μ = instᵐ ν} {instᵐ ν′} (extᵗ ρ) (instᵐ-rename ρ eν)
         (substᵗ-shift σ B) _
     ⟫ rns {ν = instᵐ ν} {instᵐ ν′} (extᵗ ρ) (instᵐ-rename ρ eν)
         (rq-inst q) c
     ⟫ ≅-sym (sr-≅ (substᵗ-shift σ′ B) _))
rns {σ = σ} {σ′} ρ eν q (inst_ {B = B} c n) | no n₁ | yes e₃ =
  ⊥-elim (n₁ (ren≡★ ρ (trans (qtyEq q B) e₃)))
rns {σ = σ} {σ′} ρ eν q (inst_ {B = B} c n) | yes e₁ | no n₃ =
  ⊥-elim (n₃ (trans (sym (qtyEq q B)) (cong (renameᵗ ρ) e₁)))
rns {ν = ν} {ν′} {σ = σ} {σ′} {s} ρ eν q
    (inst_ {B = B} ⦃ nv ⦄ ⦃ z ⦄ c n) | yes e₁ | yes e₃ =
  ren-sr {μ = ν} {ν′} ρ eν (sym e₁) _
  ⟫ ren-factorI ρ eν
      (subst-right-∼ (sh σ {B} e₁) (subst∼ (inst-SubstEnv∼ s) c))
      (substNonVar (extsᵗ σ) nv) (subst-∈ᵗ z var-∈)
      (sr-≅ (sh σ′ {B} e₃) _
       ⟫ ≅-sym (rns {ν = instᵐ ν} {instᵐ ν′} (extᵗ ρ)
           (instᵐ-rename ρ eν) (rq-inst q) c)
       ⟫ ≅-sym (ren-sr {μ = instᵐ ν} {instᵐ ν′} (extᵗ ρ)
           (instᵐ-rename ρ eν) (sh σ {B} e₁) _))
  ⟫ ≅-sym (sr-≅ (sym e₃) _)
rns {σ = σ} {σ′} ρ eν q (gen_ {A = A} c n)
    with substᵗ σ A ≟Ty ★ | substᵗ σ′ A ≟Ty ★
rns {ν = ν} {ν′} {σ = σ} {σ′} ρ eν q (gen_ {A = A} c n)
    | no n₁ | no n₃ =
  gen-≅ (qtyEq q A)
    (sl-≅ (renameᵗ-shift ρ (substᵗ σ A)) _
     ⟫ ren-sl {μ = genᵐ ν} {genᵐ ν′} (extᵗ ρ) (genᵐ-rename ρ eν)
         (substᵗ-shift σ A) _
     ⟫ rns {ν = genᵐ ν} {genᵐ ν′} (extᵗ ρ) (genᵐ-rename ρ eν)
         (rq-gen q) c
     ⟫ ≅-sym (sl-≅ (substᵗ-shift σ′ A) _))
rns {σ = σ} {σ′} ρ eν q (gen_ {A = A} c n) | no n₁ | yes e₃ =
  ⊥-elim (n₁ (ren≡★ ρ (trans (qtyEq q A) e₃)))
rns {σ = σ} {σ′} ρ eν q (gen_ {A = A} c n) | yes e₁ | no n₃ =
  ⊥-elim (n₃ (trans (sym (qtyEq q A)) (cong (renameᵗ ρ) e₁)))
rns {ν = ν} {ν′} {σ = σ} {σ′} {s} ρ eν q
    (gen_ {A = A} ⦃ nv ⦄ ⦃ z ⦄ c n) | yes e₁ | yes e₃ =
  ren-sl {μ = ν} {ν′} ρ eν (sym e₁) _
  ⟫ ren-factorG ρ eν
      (subst-left-∼ (sh σ {A} e₁) (subst∼ (gen-SubstEnv∼ s) c))
      (substNonVar (extsᵗ σ) nv) (subst-∈ᵗ z var-∈)
      (sl-≅ (sh σ′ {A} e₃) _
       ⟫ ≅-sym (rns {ν = genᵐ ν} {genᵐ ν′} (extᵗ ρ)
           (genᵐ-rename ρ eν) (rq-gen q) c)
       ⟫ ≅-sym (ren-sl {μ = genᵐ ν} {genᵐ ν′} (extᵗ ρ)
           (genᵐ-rename ρ eν) (sh σ {A} e₁) _))
  ⟫ ≅-sym (sl-≅ (sym e₃) _)
rns ρ eν q bot-elim = hrefl
rns ρ eν q bot-intro = hrefl

------------------------------------------------------------------------
-- Substitution commutes with `sym∼`
------------------------------------------------------------------------

-- `sym∼` turns the factoring of `inst` into the factoring of `gen`
sym-factorI : ∀ {Δ} {μ : Env∼ Δ} {A : Ty (ℕ.suc Δ)}
    (x : instᵐ μ ⊢ A ∼ ★) (nv : NonVar A) (z : zero ∈ᵗ A)
    {x″ : genᵐ (flipᵐ μ) ⊢ ★ ∼ A} {nv″ : NonVar A} {z″ : zero ∈ᵗ A}
  → x″ ≅ᶜ transport-env∼ (flip-instᵐ {μ = μ}) (sym∼ x)
  → sym∼ (factor-inst-star x nv z) ≅ᶜ factor-gen-star x″ nv″ z″
sym-factorI (_! ⦃ Gᵍ = ★⇒★ ⦄ c) nv z hrefl = ？-≅ (gen-≅ refl hrefl)
sym-factorI (_! ⦃ Gᵍ = ‵ ι ⦄ c) nv z hrefl = ？-≅ (gen-≅ refl hrefl)
sym-factorI (_! ⦃ Gᵍ = ＇ zero ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ c) nv z q =
  ⊥-elim (inst-to-var-occurs-impossible c eq nv z)
sym-factorI (_! ⦃ Gᵍ = ＇ zero ⦄ ⦃ G∼★ = X∼★ᶜ () ⦄ c) nv z q
sym-factorI (_! ⦃ Gᵍ = ＇ suc X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ c) nv z q =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nv (nv-occ nv z))
sym-factorI (_! ⦃ Gᵍ = ＇ suc X ⦄ ⦃ G∼★ = X∼★ᶜ eq ⦄ c) nv z q =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nv (nv-occ nv z))
sym-factorI (_! ⦃ Gᵍ = ∀★ ⦄ c) nv z hrefl = ？-≅ (gen-≅ refl hrefl)
sym-factorI (？_ c) nv () q
sym-factorI (inst_ c n) nv z q = ⊥-elim (n refl)

-- `sym∼` turns the factoring of `gen` into the factoring of `inst`
sym-factorG : ∀ {Δ} {μ : Env∼ Δ} {B : Ty (ℕ.suc Δ)}
    (x : genᵐ μ ⊢ ★ ∼ B) (nv : NonVar B) (z : zero ∈ᵗ B)
    {x″ : instᵐ (flipᵐ μ) ⊢ B ∼ ★} {nv″ : NonVar B} {z″ : zero ∈ᵗ B}
  → x″ ≅ᶜ transport-env∼ (flip-genᵐ {μ = μ}) (sym∼ x)
  → sym∼ (factor-gen-star x nv z) ≅ᶜ factor-inst-star x″ nv″ z″
sym-factorG (_! c ⦃ () ⦄) nv z q
sym-factorG (？_ ⦃ Gᵍ = ★⇒★ ⦄ c) nv z hrefl = !-≅ (inst-≅ refl hrefl)
sym-factorG (？_ ⦃ Gᵍ = ‵ ι ⦄ c) nv z hrefl = !-≅ (inst-≅ refl hrefl)
sym-factorG (？_ ⦃ Gᵍ = ＇ zero ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c) nv z q =
  ⊥-elim (gen-from-var-occurs-impossible c eq nv z)
sym-factorG (？_ ⦃ Gᵍ = ＇ zero ⦄ ⦃ ★∼G = ★∼Xᶜ () ⦄ c) nv z q
sym-factorG (？_ ⦃ Gᵍ = ＇ suc X ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c) nv z q =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nv (nv-occ nv z))
sym-factorG (？_ ⦃ Gᵍ = ＇ suc X ⦄ ⦃ ★∼G = ★∼Xᶜ eq ⦄ c) nv z q =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nv (nv-occ nv z))
sym-factorG (？_ ⦃ Gᵍ = ∀★ ⦄ c) nv z hrefl = !-≅ (inst-≅ refl hrefl)
sym-factorG (gen_ c n) nv z q = ⊥-elim (n refl)

-- s′ agrees with s flipped
record FlipM {Δ Θ} {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : Δ ⇒ˢ Θ}
    (s : SubstEnv∼ μ ν σ) (s′ : SubstEnv∼ (flipᵐ μ) (flipᵐ ν) σ)
    : Set where
  field
    mself : ∀ X → self s′ X ≅ᶜ sym∼ (self s X)
    mto : ∀ X e e′ → to-★ s′ X e ≅ᶜ sym∼ (from-★ s X e′)
    mfrom : ∀ X e e′ → from-★ s′ X e ≅ᶜ sym∼ (to-★ s X e′)
    mcto : ∀ X e e′ → cross-to-★ s′ X e ≅ᶜ sym∼ (cross-from-★ s X e′)
    mcfrom : ∀ X e e′ → cross-from-★ s′ X e ≅ᶜ sym∼ (cross-to-★ s X e′)

open FlipM public

private
  -- a flipped field, shifted under one more variable
  fm-suc : ∀ {Θ} {v} {ν : Env∼ Θ} {A B A′ B′} (c : ν ⊢ A ∼ B)
      {c′ : flipᵐ ν ⊢ A′ ∼ B′}
    → c′ ≅ᶜ sym∼ c → ⇑ᶜ {v = flipVar∼ v} c′ ≅ᶜ sym∼ (⇑ᶜ {v = v} c)
  fm-suc {v = v} {ν} c h =
    ⇑-≅ h ⟫ ren-sym {μ = ν} {v ∷ ν} suc (λ Y → refl) (λ Y → refl) c

module _ {Δ Θ} {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : Δ ⇒ˢ Θ}
    {s : SubstEnv∼ μ ν σ} {s′ : SubstEnv∼ (flipᵐ μ) (flipᵐ ν) σ} where

  fm-flip : FlipM s s′ → FlipM (flip-SubstEnv∼ s) (flip-SubstEnv∼ s′)
  mself (fm-flip m) X = sym-≅ (mself m X)
  mto (fm-flip m) X e e′ =
    sym-≅ (mfrom m X (flipVar∼-to-X∼★ (flipᵐ-‼⁻ (flipᵐ μ) X e))
      (flipVar∼-to-★∼X (flipᵐ-‼⁻ μ X e′)))
  mfrom (fm-flip m) X e e′ =
    sym-≅ (mto m X (flipVar∼-to-★∼X (flipᵐ-‼⁻ (flipᵐ μ) X e))
      (flipVar∼-to-X∼★ (flipᵐ-‼⁻ μ X e′)))
  mcto (fm-flip m) X e e′ =
    sym-≅ (mcfrom m X (flipVar∼-to-★∼X∼★ (flipᵐ-‼⁻ (flipᵐ μ) X e))
      (flipVar∼-to-★∼X∼★ (flipᵐ-‼⁻ μ X e′)))
  mcfrom (fm-flip m) X e e′ =
    sym-≅ (mcto m X (flipVar∼-to-★∼X∼★ (flipᵐ-‼⁻ (flipᵐ μ) X e))
      (flipVar∼-to-★∼X∼★ (flipᵐ-‼⁻ μ X e′)))

  fm-ext : FlipM s s′ → FlipM (ext-SubstEnv∼ s) (ext-SubstEnv∼ s′)
  mself (fm-ext m) zero = hrefl
  mself (fm-ext m) (suc X) = fm-suc (self s X) (mself m X)
  mto (fm-ext m) zero () e′
  mto (fm-ext m) (suc X) e e′ = fm-suc (from-★ s X e′) (mto m X e e′)
  mfrom (fm-ext m) zero () e′
  mfrom (fm-ext m) (suc X) e e′ = fm-suc (to-★ s X e′) (mfrom m X e e′)
  mcto (fm-ext m) zero () e′
  mcto (fm-ext m) (suc X) e e′ =
    fm-suc (cross-from-★ s X e′) (mcto m X e e′)
  mcfrom (fm-ext m) zero () e′
  mcfrom (fm-ext m) (suc X) e e′ =
    fm-suc (cross-to-★ s X e′) (mcfrom m X e e′)

  fm-inst : FlipM s s′ → FlipM (inst-SubstEnv∼ s) (gen-SubstEnv∼ s′)
  mself (fm-inst m) zero = hrefl
  mself (fm-inst m) (suc X) = fm-suc (self s X) (mself m X)
  mto (fm-inst m) zero () e′
  mto (fm-inst m) (suc X) e e′ = fm-suc (from-★ s X e′) (mto m X e e′)
  mfrom (fm-inst m) zero e e′ = ？-≅ hrefl
  mfrom (fm-inst m) (suc X) e e′ = fm-suc (to-★ s X e′) (mfrom m X e e′)
  mcto (fm-inst m) zero () e′
  mcto (fm-inst m) (suc X) e e′ =
    fm-suc (cross-from-★ s X e′) (mcto m X e e′)
  mcfrom (fm-inst m) zero () e′
  mcfrom (fm-inst m) (suc X) e e′ =
    fm-suc (cross-to-★ s X e′) (mcfrom m X e e′)

  fm-gen : FlipM s s′ → FlipM (gen-SubstEnv∼ s) (inst-SubstEnv∼ s′)
  mself (fm-gen m) zero = hrefl
  mself (fm-gen m) (suc X) = fm-suc (self s X) (mself m X)
  mto (fm-gen m) zero e e′ = !-≅ hrefl
  mto (fm-gen m) (suc X) e e′ = fm-suc (from-★ s X e′) (mto m X e e′)
  mfrom (fm-gen m) zero () e′
  mfrom (fm-gen m) (suc X) e e′ = fm-suc (to-★ s X e′) (mfrom m X e e′)
  mcto (fm-gen m) zero () e′
  mcto (fm-gen m) (suc X) e e′ =
    fm-suc (cross-from-★ s X e′) (mcto m X e e′)
  mcfrom (fm-gen m) zero () e′
  mcfrom (fm-gen m) (suc X) e e′ =
    fm-suc (cross-to-★ s X e′) (mcfrom m X e e′)

-- substitution commutes with `sym∼`
subst-sym : ∀ {Δ Θ} {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : Δ ⇒ˢ Θ}
    {s : SubstEnv∼ μ ν σ} {s′ : SubstEnv∼ (flipᵐ μ) (flipᵐ ν) σ} {A B}
  → FlipM s s′ → (c : μ ⊢ A ∼ B)
  → subst∼ s′ (sym∼ c) ≅ᶜ sym∼ (subst∼ s c)
subst-sym m (id ★) = hrefl
subst-sym m (id (‵ ι)) = hrefl
subst-sym m (id (＇ X)) = mself m X
subst-sym m (c ↦ d) = ↦-≅ (subst-sym m d) (subst-sym (fm-flip m) c)
subst-sym {μ = μ} {s′ = s′} m (∀ᶜ c) =
  ∀-≅ (subst-≅ (ext-SubstEnv∼ s′)
      (transport-≅ (flip-extᵐ {μ = μ}) (sym∼ c))
    ⟫ subst-sym (fm-ext m) c
    ⟫ ≅-sym (transport-≅ flip-extᵐ _))
subst-sym m (_! ⦃ Gᵍ = ★⇒★ ⦄ c) = ？-≅ (subst-sym m c)
subst-sym m (_! ⦃ Gᵍ = ‵ ι ⦄ c) = ？-≅ (subst-sym m c)
subst-sym m (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ e ⦄ (id (＇ _))) =
  mfrom m X _ e
subst-sym m (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ e ⦄ (？_ c) ⦃ () ⦄)
subst-sym m (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ e ⦄ c@(inst_ c₀ n) ⦃ a ⦄) =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all a)
subst-sym m (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ e ⦄ (id (＇ _))) =
  mcfrom m X _ e
subst-sym m (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ e ⦄ (？_ c) ⦃ () ⦄)
subst-sym m (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ e ⦄ c@(inst_ c₀ n) ⦃ a ⦄) =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all a)
subst-sym m (_! ⦃ Gᵍ = ∀★ ⦄ c) = ？-≅ (subst-sym m c)
subst-sym m (？_ ⦃ Gᵍ = ★⇒★ ⦄ c) = !-≅ (subst-sym m c)
subst-sym m (？_ ⦃ Gᵍ = ‵ ι ⦄ c) = !-≅ (subst-sym m c)
subst-sym m (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ e ⦄ (id (＇ _))) =
  mto m X _ e
subst-sym m (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ e ⦄ (_! c) ⦃ () ⦄)
subst-sym m (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ e ⦄ c@(gen_ c₀ n) ⦃ b ⦄) =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all b)
subst-sym m (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ e ⦄ (id (＇ _))) =
  mcto m X _ e
subst-sym m (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ e ⦄ (_! c) ⦃ () ⦄)
subst-sym m (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ e ⦄ c@(gen_ c₀ n) ⦃ b ⦄) =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all b)
subst-sym m (？_ ⦃ Gᵍ = ∀★ ⦄ c) = !-≅ (subst-sym m c)
subst-sym {σ = σ} m (inst_ {B = B} c n) with substᵗ σ B ≟Ty ★
subst-sym {μ = μ} {σ = σ} {s} {s′} m (inst_ {B = B} c n) | no n₁ =
  gen-≅ refl
    (sl-≅ (substᵗ-shift σ B) _
     ⟫ subst-≅ (gen-SubstEnv∼ s′)
         (transport-≅ (flip-instᵐ {μ = μ}) (sym∼ c))
     ⟫ subst-sym (fm-inst m) c
     ⟫ ≅-sym (sym-sr (substᵗ-shift σ B) _)
     ⟫ ≅-sym (transport-≅ flip-instᵐ _))
subst-sym {μ = μ} {σ = σ} {s} {s′} m (inst_ {B = B} ⦃ nv ⦄ ⦃ z ⦄ c n)
    | yes e =
  sl-≅ (sym e) _
  ⟫ ≅-sym (sym-factorI
      (subst-right-∼ (sh σ {B} e) (subst∼ (inst-SubstEnv∼ s) c))
      (substNonVar (extsᵗ σ) nv) (subst-∈ᵗ z var-∈)
      (sl-≅ (sh σ {B} e) _
       ⟫ subst-≅ (gen-SubstEnv∼ s′)
           (transport-≅ (flip-instᵐ {μ = μ}) (sym∼ c))
       ⟫ subst-sym (fm-inst m) c
       ⟫ ≅-sym (sym-sr (sh σ {B} e) _)
       ⟫ ≅-sym (transport-≅ flip-instᵐ _)))
  ⟫ ≅-sym (sym-sr (sym e) _)
subst-sym {σ = σ} m (gen_ {A = A} c n) with substᵗ σ A ≟Ty ★
subst-sym {μ = μ} {σ = σ} {s} {s′} m (gen_ {A = A} c n) | no n₁ =
  inst-≅ refl
    (sr-≅ (substᵗ-shift σ A) _
     ⟫ subst-≅ (inst-SubstEnv∼ s′)
         (transport-≅ (flip-genᵐ {μ = μ}) (sym∼ c))
     ⟫ subst-sym (fm-gen m) c
     ⟫ ≅-sym (sym-sl (substᵗ-shift σ A) _)
     ⟫ ≅-sym (transport-≅ flip-genᵐ _))
subst-sym {μ = μ} {σ = σ} {s} {s′} m (gen_ {A = A} ⦃ nv ⦄ ⦃ z ⦄ c n)
    | yes e =
  sr-≅ (sym e) _
  ⟫ ≅-sym (sym-factorG
      (subst-left-∼ (sh σ {A} e) (subst∼ (gen-SubstEnv∼ s) c))
      (substNonVar (extsᵗ σ) nv) (subst-∈ᵗ z var-∈)
      (sr-≅ (sh σ {A} e) _
       ⟫ subst-≅ (inst-SubstEnv∼ s′)
           (transport-≅ (flip-genᵐ {μ = μ}) (sym∼ c))
       ⟫ subst-sym (fm-gen m) c
       ⟫ ≅-sym (sym-sl (sh σ {A} e) _)
       ⟫ ≅-sym (transport-≅ flip-genᵐ _)))
  ⟫ ≅-sym (sym-sl (sym e) _)
subst-sym m bot-elim = hrefl
subst-sym m bot-intro = hrefl

------------------------------------------------------------------------
-- Substitution composes: the instance at `Fuse`
------------------------------------------------------------------------

-- s followed by the renaming ρ
renAfter : ∀ {Δ Θ Θ′} {μ : Env∼ Δ} {ν : Env∼ Θ} {ν′ : Env∼ Θ′}
    {σ : Δ ⇒ˢ Θ} (ρ : Θ ⇒ʳ Θ′) (eν : ∀ X → ν′ ‼ ρ X ≡ ν ‼ X)
  → SubstEnv∼ μ ν σ → SubstEnv∼ μ ν′ (λ X → renameᵗ ρ (σ X))
renAfter {ν = ν} {ν′} ρ eν s = subst-env∼
  (λ X → rename∼ {μ = ν} {ν′} ρ eν (self s X))
  (λ X e → rename∼ {μ = ν} {ν′} ρ eν (to-★ s X e))
  (λ X e → rename∼ {μ = ν} {ν′} ρ eν (from-★ s X e))
  (λ X e → rename∼ {μ = ν} {ν′} ρ eν (cross-to-★ s X e))
  (λ X e → rename∼ {μ = ν} {ν′} ρ eν (cross-from-★ s X e))

ren-after : ∀ {Δ Θ Θ′} {μ : Env∼ Δ} {ν : Env∼ Θ} {ν′ : Env∼ Θ′}
    {σ : Δ ⇒ˢ Θ} (ρ : Θ ⇒ʳ Θ′) (eν : ∀ X → ν′ ‼ ρ X ≡ ν ‼ X)
    (s : SubstEnv∼ μ ν σ)
  → RRel ρ eν s (renAfter {ν′ = ν′} ρ eν s)
qself (ren-after ρ eν s) X = hrefl
qto (ren-after ρ eν s) X e = hrefl
qfrom (ren-after ρ eν s) X e = hrefl
qcto (ren-after ρ eν s) X e = hrefl
qcfrom (ren-after ρ eν s) X e = hrefl

-- s followed by the shift into one more variable, of mode v
shiftE : ∀ {Δ Θ} v {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : Δ ⇒ˢ Θ}
  → SubstEnv∼ μ ν σ → SubstEnv∼ μ (v ∷ ν) (λ X → ⇑ᵗ (σ X))
shiftE v {ν = ν} s = renAfter {ν′ = v ∷ ν} suc (λ Y → refl) s

private
  shift-ext : ∀ {Δ Θ} {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : Δ ⇒ˢ Θ}
      (s : SubstEnv∼ μ ν σ)
    → SRel suc (ext-SubstEnv∼ s) (shiftE X∼X s)
  rself (shift-ext s) X = hrefl
  rto (shift-ext s) X e e′ = ⇑-cong (to-★ s X) (uip e e′)
  rfrom (shift-ext s) X e e′ = ⇑-cong (from-★ s X) (uip e e′)
  rcto (shift-ext s) X e e′ = ⇑-cong (cross-to-★ s X) (uip e e′)
  rcfrom (shift-ext s) X e e′ = ⇑-cong (cross-from-★ s X) (uip e e′)

  shift-inst : ∀ {Δ Θ} {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : Δ ⇒ˢ Θ}
      (s : SubstEnv∼ μ ν σ)
    → SRel suc (inst-SubstEnv∼ s) (shiftE X∼★ s)
  rself (shift-inst s) X = hrefl
  rto (shift-inst s) X e e′ = ⇑-cong (to-★ s X) (uip e e′)
  rfrom (shift-inst s) X e e′ = ⇑-cong (from-★ s X) (uip e e′)
  rcto (shift-inst s) X e e′ = ⇑-cong (cross-to-★ s X) (uip e e′)
  rcfrom (shift-inst s) X e e′ = ⇑-cong (cross-from-★ s X) (uip e e′)

  shift-gen : ∀ {Δ Θ} {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : Δ ⇒ˢ Θ}
      (s : SubstEnv∼ μ ν σ)
    → SRel suc (gen-SubstEnv∼ s) (shiftE ★∼X s)
  rself (shift-gen s) X = hrefl
  rto (shift-gen s) X e e′ = ⇑-cong (to-★ s X) (uip e e′)
  rfrom (shift-gen s) X e e′ = ⇑-cong (from-★ s X) (uip e e′)
  rcto (shift-gen s) X e e′ = ⇑-cong (cross-to-★ s X) (uip e e′)
  rcfrom (shift-gen s) X e e′ = ⇑-cong (cross-from-★ s X) (uip e e′)

  -- substitution under a binder commutes with the shift
  shift-law : ∀ {Δ Θ} {v} {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : Δ ⇒ˢ Θ}
      {s : SubstEnv∼ μ ν σ} {S : SubstEnv∼ (v ∷ μ) (v ∷ ν) (extsᵗ σ)}
      {A B}
    → SRel suc S (shiftE v s) → (c : μ ⊢ A ∼ B)
    → subst∼ S (⇑ᶜ c) ≅ᶜ ⇑ᶜ {v = v} (subst∼ s c)
  shift-law {v = v} {μ} {ν} {s = s} r c =
    srn {μ = μ} {v ∷ μ} suc (λ Y → refl) r c
    ⟫ ≅-sym (rns {ν = ν} {v ∷ ν} suc (λ Y → refl)
        (ren-after {ν′ = v ∷ ν} suc (λ Y → refl) s) c)

  fm-refl : ∀ {Δ Θ} {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : Δ ⇒ˢ Θ}
      (s : SubstEnv∼ μ ν σ) → FlipM s (flip-SubstEnv∼ s)
  mself (fm-refl s) X = hrefl
  mto (fm-refl {μ = μ} s) X e e′ =
    sym-≅ (≡→≅ (cong (from-★ s X)
      (uip (flipVar∼-to-X∼★ (flipᵐ-‼⁻ μ X e)) e′)))
  mfrom (fm-refl {μ = μ} s) X e e′ =
    sym-≅ (≡→≅ (cong (to-★ s X)
      (uip (flipVar∼-to-★∼X (flipᵐ-‼⁻ μ X e)) e′)))
  mcto (fm-refl {μ = μ} s) X e e′ =
    sym-≅ (≡→≅ (cong (cross-from-★ s X)
      (uip (flipVar∼-to-★∼X∼★ (flipᵐ-‼⁻ μ X e)) e′)))
  mcfrom (fm-refl {μ = μ} s) X e e′ =
    sym-≅ (≡→≅ (cong (cross-to-★ s X)
      (uip (flipVar∼-to-★∼X∼★ (flipᵐ-‼⁻ μ X e)) e′)))

module _ {Δ₁ Δ₂ Δ₃} {μ₁ : Env∼ Δ₁} {μ₂ : Env∼ Δ₂} {μ₃ : Env∼ Δ₃}
    {σ₁ : Δ₁ ⇒ˢ Δ₂} {σ₂ : Δ₂ ⇒ˢ Δ₃} {σ₃ : Δ₁ ⇒ˢ Δ₃}
    {s₁ : SubstEnv∼ μ₁ μ₂ σ₁} {s₂ : SubstEnv∼ μ₂ μ₃ σ₂}
    {s₃ : SubstEnv∼ μ₁ μ₃ σ₃} where

  fuse-ext : Fuse s₁ s₂ s₃
    → Fuse (ext-SubstEnv∼ s₁) (ext-SubstEnv∼ s₂) (ext-SubstEnv∼ s₃)
  fself (fuse-ext p) zero = hrefl
  fself (fuse-ext p) (suc X) =
    shift-law (shift-ext s₂) (self s₁ X) ⟫ ⇑-≅ (fself p X)
  fto (fuse-ext p) zero ()
  fto (fuse-ext p) (suc X) e =
    shift-law (shift-ext s₂) (to-★ s₁ X e) ⟫ ⇑-≅ (fto p X e)
  ffrom (fuse-ext p) zero ()
  ffrom (fuse-ext p) (suc X) e =
    shift-law (shift-ext s₂) (from-★ s₁ X e) ⟫ ⇑-≅ (ffrom p X e)
  fcto (fuse-ext p) zero ()
  fcto (fuse-ext p) (suc X) e =
    shift-law (shift-ext s₂) (cross-to-★ s₁ X e) ⟫ ⇑-≅ (fcto p X e)
  fcfrom (fuse-ext p) zero ()
  fcfrom (fuse-ext p) (suc X) e =
    shift-law (shift-ext s₂) (cross-from-★ s₁ X e) ⟫ ⇑-≅ (fcfrom p X e)

  fuse-inst : Fuse s₁ s₂ s₃
    → Fuse (inst-SubstEnv∼ s₁) (inst-SubstEnv∼ s₂) (inst-SubstEnv∼ s₃)
  fself (fuse-inst p) zero = hrefl
  fself (fuse-inst p) (suc X) =
    shift-law (shift-inst s₂) (self s₁ X) ⟫ ⇑-≅ (fself p X)
  fto (fuse-inst p) zero e = hrefl
  fto (fuse-inst p) (suc X) e =
    shift-law (shift-inst s₂) (to-★ s₁ X e) ⟫ ⇑-≅ (fto p X e)
  ffrom (fuse-inst p) zero ()
  ffrom (fuse-inst p) (suc X) e =
    shift-law (shift-inst s₂) (from-★ s₁ X e) ⟫ ⇑-≅ (ffrom p X e)
  fcto (fuse-inst p) zero ()
  fcto (fuse-inst p) (suc X) e =
    shift-law (shift-inst s₂) (cross-to-★ s₁ X e) ⟫ ⇑-≅ (fcto p X e)
  fcfrom (fuse-inst p) zero ()
  fcfrom (fuse-inst p) (suc X) e =
    shift-law (shift-inst s₂) (cross-from-★ s₁ X e) ⟫ ⇑-≅ (fcfrom p X e)

  fuse-gen : Fuse s₁ s₂ s₃
    → Fuse (gen-SubstEnv∼ s₁) (gen-SubstEnv∼ s₂) (gen-SubstEnv∼ s₃)
  fself (fuse-gen p) zero = hrefl
  fself (fuse-gen p) (suc X) =
    shift-law (shift-gen s₂) (self s₁ X) ⟫ ⇑-≅ (fself p X)
  fto (fuse-gen p) zero ()
  fto (fuse-gen p) (suc X) e =
    shift-law (shift-gen s₂) (to-★ s₁ X e) ⟫ ⇑-≅ (fto p X e)
  ffrom (fuse-gen p) zero e = hrefl
  ffrom (fuse-gen p) (suc X) e =
    shift-law (shift-gen s₂) (from-★ s₁ X e) ⟫ ⇑-≅ (ffrom p X e)
  fcto (fuse-gen p) zero ()
  fcto (fuse-gen p) (suc X) e =
    shift-law (shift-gen s₂) (cross-to-★ s₁ X e) ⟫ ⇑-≅ (fcto p X e)
  fcfrom (fuse-gen p) zero ()
  fcfrom (fuse-gen p) (suc X) e =
    shift-law (shift-gen s₂) (cross-from-★ s₁ X e) ⟫ ⇑-≅ (fcfrom p X e)

  fuse-flip : Fuse s₁ s₂ s₃
    → Fuse (flip-SubstEnv∼ s₁) (flip-SubstEnv∼ s₂) (flip-SubstEnv∼ s₃)
  fself (fuse-flip p) X =
    subst-sym (fm-refl s₂) (self s₁ X) ⟫ sym-≅ (fself p X)
  fto (fuse-flip p) X e =
    subst-sym (fm-refl s₂) (from-★ s₁ X P) ⟫ sym-≅ (ffrom p X P)
    where P = flipVar∼-to-X∼★ (flipᵐ-‼⁻ μ₁ X e)
  ffrom (fuse-flip p) X e =
    subst-sym (fm-refl s₂) (to-★ s₁ X P) ⟫ sym-≅ (fto p X P)
    where P = flipVar∼-to-★∼X (flipᵐ-‼⁻ μ₁ X e)
  fcto (fuse-flip p) X e =
    subst-sym (fm-refl s₂) (cross-from-★ s₁ X P) ⟫ sym-≅ (fcfrom p X P)
    where P = flipVar∼-to-★∼X∼★ (flipᵐ-‼⁻ μ₁ X e)
  fcfrom (fuse-flip p) X e =
    subst-sym (fm-refl s₂) (cross-to-★ s₁ X P) ⟫ sym-≅ (fcto p X P)
    where P = flipVar∼-to-★∼X∼★ (flipᵐ-‼⁻ μ₁ X e)

private
  module FuseI = Fusion Fuse (λ p → p) fuse-ext fuse-inst fuse-gen fuse-flip

-- substitution composes, at environments that agree at the variables
subst-subst : ∀ {Δ₁ Δ₂ Δ₃} {μ₁ : Env∼ Δ₁} {μ₂ : Env∼ Δ₂} {μ₃ : Env∼ Δ₃}
    {σ₁ σ₂ σ₃} {s₁ : SubstEnv∼ μ₁ μ₂ σ₁} {s₂ : SubstEnv∼ μ₂ μ₃ σ₂}
    {s₃ : SubstEnv∼ μ₁ μ₃ σ₃} {A B}
  → Fuse s₁ s₂ s₃ → (c : μ₁ ⊢ A ∼ B)
  → subst∼ s₂ (subst∼ s₁ c) ≅ᶜ subst∼ s₃ c
subst-subst = FuseI.ss

------------------------------------------------------------------------
-- Substitution at the identity, and at a renaming
------------------------------------------------------------------------

-- s is the identity at the variables
record IdS {Δ} {μ : Env∼ Δ} {σ : Δ ⇒ˢ Δ} (s : SubstEnv∼ μ μ σ) : Set where
  field
    iself : ∀ X → self s X ≅ᶜ id {μ = μ} (＇ X)
    ito : ∀ X e → to-★ s X e
      ≅ᶜ _! ⦃ G∼★ = X∼★ᵍ e ⦄ (id {μ = μ} (＇ X)) ⦃ nonstar-X ⦄
    ifrom : ∀ X e → from-★ s X e
      ≅ᶜ ？_ ⦃ ★∼G = ★∼Xᵍ e ⦄ (id {μ = μ} (＇ X)) ⦃ nonstar-X ⦄
    icto : ∀ X e → cross-to-★ s X e
      ≅ᶜ _! ⦃ G∼★ = X∼★ᶜ e ⦄ (id {μ = μ} (＇ X)) ⦃ nonstar-X ⦄
    icfrom : ∀ X e → cross-from-★ s X e
      ≅ᶜ ？_ ⦃ ★∼G = ★∼Xᶜ e ⦄ (id {μ = μ} (＇ X)) ⦃ nonstar-X ⦄

  idTy : ∀ A → substᵗ σ A ≡ A
  idTy A = trans (substᵗ-cong A (λ X → ≅-src (iself X))) (substᵗ-id A)

open IdS public

module _ {Δ} {μ : Env∼ Δ} {σ : Δ ⇒ˢ Δ} {s : SubstEnv∼ μ μ σ} where

  id-ext : IdS s → IdS (ext-SubstEnv∼ s)
  iself (id-ext r) zero = hrefl
  iself (id-ext r) (suc X) = ⇑-≅ (iself r X)
  ito (id-ext r) zero ()
  ito (id-ext r) (suc X) e = ⇑-≅ (ito r X e) ⟫ !-≅ hrefl
  ifrom (id-ext r) zero ()
  ifrom (id-ext r) (suc X) e = ⇑-≅ (ifrom r X e) ⟫ ？-≅ hrefl
  icto (id-ext r) zero ()
  icto (id-ext r) (suc X) e = ⇑-≅ (icto r X e) ⟫ !-≅ hrefl
  icfrom (id-ext r) zero ()
  icfrom (id-ext r) (suc X) e = ⇑-≅ (icfrom r X e) ⟫ ？-≅ hrefl

  id-inst : IdS s → IdS (inst-SubstEnv∼ s)
  iself (id-inst r) zero = hrefl
  iself (id-inst r) (suc X) = ⇑-≅ (iself r X)
  ito (id-inst r) zero e = !-≅ hrefl
  ito (id-inst r) (suc X) e = ⇑-≅ (ito r X e) ⟫ !-≅ hrefl
  ifrom (id-inst r) zero ()
  ifrom (id-inst r) (suc X) e = ⇑-≅ (ifrom r X e) ⟫ ？-≅ hrefl
  icto (id-inst r) zero ()
  icto (id-inst r) (suc X) e = ⇑-≅ (icto r X e) ⟫ !-≅ hrefl
  icfrom (id-inst r) zero ()
  icfrom (id-inst r) (suc X) e = ⇑-≅ (icfrom r X e) ⟫ ？-≅ hrefl

  id-gen : IdS s → IdS (gen-SubstEnv∼ s)
  iself (id-gen r) zero = hrefl
  iself (id-gen r) (suc X) = ⇑-≅ (iself r X)
  ito (id-gen r) zero ()
  ito (id-gen r) (suc X) e = ⇑-≅ (ito r X e) ⟫ !-≅ hrefl
  ifrom (id-gen r) zero e = ？-≅ hrefl
  ifrom (id-gen r) (suc X) e = ⇑-≅ (ifrom r X e) ⟫ ？-≅ hrefl
  icto (id-gen r) zero ()
  icto (id-gen r) (suc X) e = ⇑-≅ (icto r X e) ⟫ !-≅ hrefl
  icfrom (id-gen r) zero ()
  icfrom (id-gen r) (suc X) e = ⇑-≅ (icfrom r X e) ⟫ ？-≅ hrefl

  id-flip : IdS s → IdS (flip-SubstEnv∼ s)
  iself (id-flip r) X = sym-≅ (iself r X)
  ito (id-flip r) X e =
    sym-≅ (ifrom r X (flipVar∼-to-X∼★ (flipᵐ-‼⁻ μ X e))) ⟫ !-≅ hrefl
  ifrom (id-flip r) X e =
    sym-≅ (ito r X (flipVar∼-to-★∼X (flipᵐ-‼⁻ μ X e))) ⟫ ？-≅ hrefl
  icto (id-flip r) X e =
    sym-≅ (icfrom r X (flipVar∼-to-★∼X∼★ (flipᵐ-‼⁻ μ X e))) ⟫ !-≅ hrefl
  icfrom (id-flip r) X e =
    sym-≅ (icto r X (flipVar∼-to-★∼X∼★ (flipᵐ-‼⁻ μ X e))) ⟫ ？-≅ hrefl

-- substitution at the identity
subst-id : ∀ {Δ} {μ : Env∼ Δ} {σ : Δ ⇒ˢ Δ} {s : SubstEnv∼ μ μ σ} {A B}
  → IdS s → (c : μ ⊢ A ∼ B) → subst∼ s c ≅ᶜ c
subst-id r (id ★) = hrefl
subst-id r (id (‵ ι)) = hrefl
subst-id r (id (＇ X)) = iself r X
subst-id r (c ↦ d) = ↦-≅ (subst-id r d) (subst-id (id-flip r) c)
subst-id r (∀ᶜ c) = ∀-≅ (subst-id (id-ext r) c)
subst-id r (_! ⦃ Gᵍ = ★⇒★ ⦄ c) = !-≅ (subst-id r c)
subst-id r (_! ⦃ Gᵍ = ‵ ι ⦄ c) = !-≅ (subst-id r c)
subst-id r (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ e ⦄ (id (＇ _))) =
  ito r X e ⟫ !-≅ hrefl
subst-id r (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ e ⦄ (？_ c) ⦃ () ⦄)
subst-id r (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ e ⦄ c@(inst_ c₀ n) ⦃ a ⦄) =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all a)
subst-id r (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ e ⦄ (id (＇ _))) =
  icto r X e ⟫ !-≅ hrefl
subst-id r (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ e ⦄ (？_ c) ⦃ () ⦄)
subst-id r (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ e ⦄ c@(inst_ c₀ n) ⦃ a ⦄) =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all a)
subst-id r (_! ⦃ Gᵍ = ∀★ ⦄ c) = !-≅ (subst-id r c)
subst-id r (？_ ⦃ Gᵍ = ★⇒★ ⦄ c) = ？-≅ (subst-id r c)
subst-id r (？_ ⦃ Gᵍ = ‵ ι ⦄ c) = ？-≅ (subst-id r c)
subst-id r (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ e ⦄ (id (＇ _))) =
  ifrom r X e ⟫ ？-≅ hrefl
subst-id r (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ e ⦄ (_! c) ⦃ () ⦄)
subst-id r (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ e ⦄ c@(gen_ c₀ n) ⦃ b ⦄) =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all b)
subst-id r (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ e ⦄ (id (＇ _))) =
  icfrom r X e ⟫ ？-≅ hrefl
subst-id r (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ e ⦄ (_! c) ⦃ () ⦄)
subst-id r (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ e ⦄ c@(gen_ c₀ n) ⦃ b ⦄) =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all b)
subst-id r (？_ ⦃ Gᵍ = ∀★ ⦄ c) = ？-≅ (subst-id r c)
subst-id {σ = σ} r (inst_ {B = B} c n) with substᵗ σ B ≟Ty ★
subst-id {σ = σ} r (inst_ {B = B} c n) | no n₁ =
  inst-≅ (idTy r B)
    (sr-≅ (substᵗ-shift σ B) _ ⟫ subst-id (id-inst r) c)
subst-id {σ = σ} r (inst_ {B = B} c n) | yes e₁ =
  ⊥-elim (n (trans (sym (idTy r B)) e₁))
subst-id {σ = σ} r (gen_ {A = A} c n) with substᵗ σ A ≟Ty ★
subst-id {σ = σ} r (gen_ {A = A} c n) | no n₁ =
  gen-≅ (idTy r A)
    (sl-≅ (substᵗ-shift σ A) _ ⟫ subst-id (id-gen r) c)
subst-id {σ = σ} r (gen_ {A = A} c n) | yes e₁ =
  ⊥-elim (n (trans (sym (idTy r A)) e₁))
subst-id r bot-elim = hrefl
subst-id r bot-intro = hrefl

-- the identity environment
idE : ∀ {Δ} {μ : Env∼ Δ} → SubstEnv∼ μ μ (λ X → ＇ X)
idE = subst-env∼ (λ X → id (＇ X))
  (λ X e → _! ⦃ G∼★ = X∼★ᵍ e ⦄ (id (＇ X)) ⦃ nonstar-X ⦄)
  (λ X e → ？_ ⦃ ★∼G = ★∼Xᵍ e ⦄ (id (＇ X)) ⦃ nonstar-X ⦄)
  (λ X e → _! ⦃ G∼★ = X∼★ᶜ e ⦄ (id (＇ X)) ⦃ nonstar-X ⦄)
  (λ X e → ？_ ⦃ ★∼G = ★∼Xᶜ e ⦄ (id (＇ X)) ⦃ nonstar-X ⦄)

idE-id : ∀ {Δ} {μ : Env∼ Δ} → IdS (idE {μ = μ})
iself idE-id X = hrefl
ito idE-id X e = hrefl
ifrom idE-id X e = hrefl
icto idE-id X e = hrefl
icfrom idE-id X e = hrefl

-- substitution at a renaming is the renaming
subst-ren : ∀ {Δ Θ} {μ : Env∼ Δ} {ν : Env∼ Θ} (ρ : Δ ⇒ʳ Θ)
    (eν : ∀ X → ν ‼ ρ X ≡ μ ‼ X) {A B} (c : μ ⊢ A ∼ B)
  → subst∼ (renAfter {ν′ = ν} ρ eν idE) c ≅ᶜ rename∼ {μ = μ} {ν} ρ eν c
subst-ren {μ = μ} {ν} ρ eν c =
  ≅-sym (rns {ν = μ} {ν} ρ eν (ren-after {ν′ = ν} ρ eν idE) c)
  ⟫ ren-≅ {μ′ = ν} eν eν (subst-id idE-id c)

-- a substitution that reads suc X as the renaming ρ, after the shift
subst-⇑ : ∀ {Δ Θ} {v} {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : ℕ.suc Δ ⇒ˢ Θ}
    {s : SubstEnv∼ (v ∷ μ) ν σ} (ρ : Δ ⇒ʳ Θ)
    (eν : ∀ X → ν ‼ ρ X ≡ μ ‼ X) {A B}
  → SRel suc s (renAfter {ν′ = ν} ρ eν idE) → (c : μ ⊢ A ∼ B)
  → subst∼ s (⇑ᶜ {v = v} c) ≅ᶜ rename∼ {μ = μ} {ν} ρ eν c
subst-⇑ {v = v} {μ} ρ eν r c =
  srn {μ = μ} {v ∷ μ} suc (λ Y → refl) r c ⟫ subst-ren ρ eν c

------------------------------------------------------------------------
-- Environments that agree at the variables
------------------------------------------------------------------------

-- s′ at ρ X has the casts of s at X
record Agree {Δ Δ′ Θ} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {ν ν′ : Env∼ Θ}
    (ρ : Δ ⇒ʳ Δ′) {σ : Δ ⇒ˢ Θ} {σ′ : Δ′ ⇒ˢ Θ}
    (s : SubstEnv∼ μ ν σ) (s′ : SubstEnv∼ μ′ ν′ σ′) : Set where
  field
    aself : ∀ X → self s′ (ρ X) ≅ᶜ self s X
    ato : ∀ X e e′ → to-★ s′ (ρ X) e ≅ᶜ to-★ s X e′
    afrom : ∀ X e e′ → from-★ s′ (ρ X) e ≅ᶜ from-★ s X e′
    acto : ∀ X e e′ → cross-to-★ s′ (ρ X) e ≅ᶜ cross-to-★ s X e′
    acfrom : ∀ X e e′ → cross-from-★ s′ (ρ X) e ≅ᶜ cross-from-★ s X e′

open Agree public

-- renaming twice is renaming once, at equal target environments
ren-ren′ : ∀ {Δ₁ Δ₂ Δ₃} {μ₁ : Env∼ Δ₁} {μ₂ : Env∼ Δ₂} {μ₃ μ₄ : Env∼ Δ₃}
    {A B} {ρ₁ : Δ₁ ⇒ʳ Δ₂} {ρ₂ : Δ₂ ⇒ʳ Δ₃} {ρ₃ : Δ₁ ⇒ʳ Δ₃}
    (e₁ : ∀ X → μ₂ ‼ ρ₁ X ≡ μ₁ ‼ X) (e₂ : ∀ X → μ₃ ‼ ρ₂ X ≡ μ₂ ‼ X)
    (e₃ : ∀ X → μ₄ ‼ ρ₃ X ≡ μ₁ ‼ X) → μ₃ ≡ μ₄
  → (∀ X → ρ₂ (ρ₁ X) ≡ ρ₃ X) → (c : μ₁ ⊢ A ∼ B)
  → rename∼ {μ = μ₂} {μ₃} ρ₂ e₂ (rename∼ {μ = μ₁} {μ₂} ρ₁ e₁ c)
    ≅ᶜ rename∼ {μ = μ₁} {μ₄} ρ₃ e₃ c
ren-ren′ e₁ e₂ e₃ refl h c = ren-ren e₁ e₂ e₃ h c

-- an agreement with s renamed along π₁, renamed further along π₂, is
-- an agreement with s renamed along the composite π₃
agree-ren : ∀ {Δ Δ′ Θ₀ Θ₁ Θ₂} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
    {ν₀ : Env∼ Θ₀} {ν₁ : Env∼ Θ₁} {ν₂ ν₃ : Env∼ Θ₂} {ρ : Δ ⇒ʳ Δ′}
    {σ : Δ ⇒ˢ Θ₀} {σ′ : Δ′ ⇒ˢ Θ₁} {s : SubstEnv∼ μ ν₀ σ}
    {s′ : SubstEnv∼ μ′ ν₁ σ′} (π₁ : Θ₀ ⇒ʳ Θ₁) (π₂ : Θ₁ ⇒ʳ Θ₂)
    (π₃ : Θ₀ ⇒ʳ Θ₂) (e₁ : ∀ X → ν₁ ‼ π₁ X ≡ ν₀ ‼ X)
    (e₂ : ∀ X → ν₂ ‼ π₂ X ≡ ν₁ ‼ X) (e₃ : ∀ X → ν₃ ‼ π₃ X ≡ ν₀ ‼ X)
  → ν₂ ≡ ν₃ → (∀ X → π₂ (π₁ X) ≡ π₃ X)
  → Agree ρ (renAfter {ν′ = ν₁} π₁ e₁ s) s′
  → Agree ρ (renAfter {ν′ = ν₃} π₃ e₃ s) (renAfter {ν′ = ν₂} π₂ e₂ s′)
aself (agree-ren {ν₂ = ν₂} {s = s} π₁ π₂ π₃ e₁ e₂ e₃ eq h a) X =
  ren-≅ {μ′ = ν₂} e₂ e₂ (aself a X) ⟫ ren-ren′ e₁ e₂ e₃ eq h (self s X)
ato (agree-ren {ν₂ = ν₂} {s = s} π₁ π₂ π₃ e₁ e₂ e₃ eq h a) X e e′ =
  ren-≅ {μ′ = ν₂} e₂ e₂ (ato a X e e′)
  ⟫ ren-ren′ e₁ e₂ e₃ eq h (to-★ s X e′)
afrom (agree-ren {ν₂ = ν₂} {s = s} π₁ π₂ π₃ e₁ e₂ e₃ eq h a) X e e′ =
  ren-≅ {μ′ = ν₂} e₂ e₂ (afrom a X e e′)
  ⟫ ren-ren′ e₁ e₂ e₃ eq h (from-★ s X e′)
acto (agree-ren {ν₂ = ν₂} {s = s} π₁ π₂ π₃ e₁ e₂ e₃ eq h a) X e e′ =
  ren-≅ {μ′ = ν₂} e₂ e₂ (acto a X e e′)
  ⟫ ren-ren′ e₁ e₂ e₃ eq h (cross-to-★ s X e′)
acfrom (agree-ren {ν₂ = ν₂} {s = s} π₁ π₂ π₃ e₁ e₂ e₃ eq h a) X e e′ =
  ren-≅ {μ′ = ν₂} e₂ e₂ (acfrom a X e e′)
  ⟫ ren-ren′ e₁ e₂ e₃ eq h (cross-from-★ s X e′)

------------------------------------------------------------------------
-- Composite environments
------------------------------------------------------------------------

-- s₁ followed by s₂, at any substitution equal to their composite
seqE : ∀ {Δ₁ Δ₂ Δ₃} {μ₁ : Env∼ Δ₁} {μ₂ : Env∼ Δ₂} {μ₃ : Env∼ Δ₃}
    {σ₁ : Δ₁ ⇒ˢ Δ₂} {σ₂ : Δ₂ ⇒ˢ Δ₃} {τ : Δ₁ ⇒ˢ Δ₃}
  → (∀ X → substᵗ σ₂ (σ₁ X) ≡ τ X)
  → SubstEnv∼ μ₁ μ₂ σ₁ → SubstEnv∼ μ₂ μ₃ σ₂ → SubstEnv∼ μ₁ μ₃ τ
seqE h s₁ s₂ = subst-env∼
  (λ X → subst-left-∼ (h X) (subst-right-∼ (h X) (subst∼ s₂ (self s₁ X))))
  (λ X e → subst-left-∼ (h X) (subst∼ s₂ (to-★ s₁ X e)))
  (λ X e → subst-right-∼ (h X) (subst∼ s₂ (from-★ s₁ X e)))
  (λ X e → subst-left-∼ (h X) (subst∼ s₂ (cross-to-★ s₁ X e)))
  (λ X e → subst-right-∼ (h X) (subst∼ s₂ (cross-from-★ s₁ X e)))

seq-fuse : ∀ {Δ₁ Δ₂ Δ₃} {μ₁ : Env∼ Δ₁} {μ₂ : Env∼ Δ₂} {μ₃ : Env∼ Δ₃}
    {σ₁ : Δ₁ ⇒ˢ Δ₂} {σ₂ : Δ₂ ⇒ˢ Δ₃} {τ : Δ₁ ⇒ˢ Δ₃}
    (h : ∀ X → substᵗ σ₂ (σ₁ X) ≡ τ X)
    (s₁ : SubstEnv∼ μ₁ μ₂ σ₁) (s₂ : SubstEnv∼ μ₂ μ₃ σ₂)
  → Fuse s₁ s₂ (seqE h s₁ s₂)
fself (seq-fuse h s₁ s₂) X = ≅-sym (sl-≅ (h X) _ ⟫ sr-≅ (h X) _)
fto (seq-fuse h s₁ s₂) X e = ≅-sym (sl-≅ (h X) _)
ffrom (seq-fuse h s₁ s₂) X e = ≅-sym (sr-≅ (h X) _)
fcto (seq-fuse h s₁ s₂) X e = ≅-sym (sl-≅ (h X) _)
fcfrom (seq-fuse h s₁ s₂) X e = ≅-sym (sr-≅ (h X) _)

-- s read before the renaming ρ, at any substitution equal to s ∘ ρ
preRen : ∀ {Δ Δ′ Θ} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {ν : Env∼ Θ}
    {σ : Δ′ ⇒ˢ Θ} {τ : Δ ⇒ˢ Θ} (ρ : Δ ⇒ʳ Δ′)
    (eq : ∀ X → μ′ ‼ ρ X ≡ μ ‼ X)
  → (∀ X → σ (ρ X) ≡ τ X) → SubstEnv∼ μ′ ν σ → SubstEnv∼ μ ν τ
preRen ρ eq h s = subst-env∼
  (λ X → subst-left-∼ (h X) (subst-right-∼ (h X) (self s (ρ X))))
  (λ X e → subst-left-∼ (h X) (to-★ s (ρ X) (trans (eq X) e)))
  (λ X e → subst-right-∼ (h X) (from-★ s (ρ X) (trans (eq X) e)))
  (λ X e → subst-left-∼ (h X) (cross-to-★ s (ρ X) (trans (eq X) e)))
  (λ X e → subst-right-∼ (h X) (cross-from-★ s (ρ X) (trans (eq X) e)))

pre-rel : ∀ {Δ Δ′ Θ} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {ν : Env∼ Θ}
    {σ : Δ′ ⇒ˢ Θ} {τ : Δ ⇒ˢ Θ} (ρ : Δ ⇒ʳ Δ′)
    (eq : ∀ X → μ′ ‼ ρ X ≡ μ ‼ X) (h : ∀ X → σ (ρ X) ≡ τ X)
    (s : SubstEnv∼ μ′ ν σ)
  → SRel ρ s (preRen {μ = μ} {μ′} ρ eq h s)
rself (pre-rel ρ eq h s) X = ≅-sym (sl-≅ (h X) _ ⟫ sr-≅ (h X) _)
rto (pre-rel ρ eq h s) X e e′ =
  ≡→≅ (cong (to-★ s (ρ X)) (uip e (trans (eq X) e′)))
  ⟫ ≅-sym (sl-≅ (h X) _)
rfrom (pre-rel ρ eq h s) X e e′ =
  ≡→≅ (cong (from-★ s (ρ X)) (uip e (trans (eq X) e′)))
  ⟫ ≅-sym (sr-≅ (h X) _)
rcto (pre-rel ρ eq h s) X e e′ =
  ≡→≅ (cong (cross-to-★ s (ρ X)) (uip e (trans (eq X) e′)))
  ⟫ ≅-sym (sl-≅ (h X) _)
rcfrom (pre-rel ρ eq h s) X e e′ =
  ≡→≅ (cong (cross-from-★ s (ρ X)) (uip e (trans (eq X) e′)))
  ⟫ ≅-sym (sr-≅ (h X) _)

-- substitution at variables is renaming
subst-varᵗ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) (A : Ty Δ)
  → substᵗ (λ X → ＇ ρ X) A ≡ renameᵗ ρ A
subst-varᵗ ρ A =
  trans (sym (substᵗ-rename (λ X → ＇ X) ρ A)) (substᵗ-id (renameᵗ ρ A))

-- the opening at T, as `_[_]ᶜ` reads it
openE : ∀ {Δ} {μ : Env∼ Δ} (T : Ty Δ)
  → SubstEnv∼ (extᵐ μ) μ (singleSubᵗ T)
openE {μ = μ} T = subst-env∼
  (λ X → _[_]ᶜ {μ = μ} (id (＇ X)) T)
  (λ X e → _[_]ᶜ {μ = μ} (_! ⦃ G∼★ = X∼★ᵍ e ⦄ (id (＇ X))) T)
  (λ X e → _[_]ᶜ {μ = μ} (？_ ⦃ ★∼G = ★∼Xᵍ e ⦄ (id (＇ X))) T)
  (λ X e → _[_]ᶜ {μ = μ} (_! ⦃ G∼★ = X∼★ᶜ e ⦄ (id (＇ X))) T)
  (λ X e → _[_]ᶜ {μ = μ} (？_ ⦃ ★∼G = ★∼Xᶜ e ⦄ (id (＇ X))) T)

------------------------------------------------------------------------
-- Case 6: the casts read through the extended interpretation
------------------------------------------------------------------------

-- The left's body cast c at the extended interpretation (`castL₂` in
-- `CastLemma.AtReplay.Ob`): sL is the cast's environment at w, ρ the
-- renaming into w′, T the left's instantiation, and ρ″ the renaming
-- into the future w″.  `envL h` is the environment to take for
-- `sL (hyp₂ e″)`, at any substitution τ equal to the composite σC.
module CastL {Δ Θ Θ′ Θ″} {ν : Env∼ Δ} {νL : Env∼ Θ} {σL : Δ ⇒ˢ Θ}
    (sL : SubstEnv∼ ν νL σL) (ρ : Θ ↪ᵗ Θ′) (T : Ty Θ′)
    (ρ″ : Θ′ ↪ᵗ Θ″) where

  eL : ∀ X → extᵐ (renameEnv∼ ρ νL) ‼ extᵗ (toRenameᵗ ρ) X ≡ extᵐ νL ‼ X
  eL = extᵐ-rename (toRenameᵗ ρ) (renameEnv∼-preserves ρ νL)

  σM : ℕ.suc Θ ⇒ˢ Θ″
  σM X = renameᵗ (toRenameᵗ ρ″) (singleSubᵗ T (extᵗ (toRenameᵗ ρ) X))

  -- the opening at T and the renaming ρ″, read before the renaming ρ
  M : SubstEnv∼ (extᵐ νL) (renameEnv∼ ρ″ (renameEnv∼ ρ νL)) σM
  M = preRen {μ = extᵐ νL} {extᵐ (renameEnv∼ ρ νL)}
        (extᵗ (toRenameᵗ ρ)) eL (λ X → refl)
        (renAfter {ν′ = renameEnv∼ ρ″ (renameEnv∼ ρ νL)} (toRenameᵗ ρ″)
          (renameEnv∼-preserves ρ″ (renameEnv∼ ρ νL)) (openE T))

  σC : ℕ.suc Δ ⇒ˢ Θ″
  σC X = substᵗ σM (extsᵗ σL X)

  σC-zero : σC zero ≡ renameᵗ (toRenameᵗ ρ″) T
  σC-zero = refl

  σC-suc : ∀ X
    → σC (suc X) ≡ renameᵗ (λ Y → toRenameᵗ ρ″ (toRenameᵗ ρ Y)) (σL X)
  σC-suc X = trans (substᵗ-rename σM suc (σL X))
    (subst-varᵗ (λ Y → toRenameᵗ ρ″ (toRenameᵗ ρ Y)) (σL X))

  envL : ∀ {τ : ℕ.suc Δ ⇒ˢ Θ″} → (∀ X → σC X ≡ τ X)
    → SubstEnv∼ (extᵐ ν) (renameEnv∼ ρ″ (renameEnv∼ ρ νL)) τ
  envL h = seqE h (ext-SubstEnv∼ sL) M

  castL : ∀ {τ : ℕ.suc Δ ⇒ˢ Θ″} (h : ∀ X → σC X ≡ τ X) {A B}
      (c : extᵐ ν ⊢ A ∼ B)
      (Q : Term Θ″)
    → Q ⟨ subst∼ (envL h) c ⟩
      ≡ Q ⟨ renameᵐᶜ ρ″
              (rename∼ (extᵗ (toRenameᵗ ρ)) eL
                (subst∼ (ext-SubstEnv∼ sL) c) [ T ]ᶜ) ⟩
  castL h c Q = ≅ᶜ-⟨⟩ Q
    (≅-sym (subst-subst (seq-fuse h (ext-SubstEnv∼ sL) M) c)
     ⟫ ≅-sym (srn (extᵗ (toRenameᵗ ρ)) eL
         (pre-rel {μ = extᵐ νL} {extᵐ (renameEnv∼ ρ νL)}
           (extᵗ (toRenameᵗ ρ)) eL (λ X → refl) R)
         (subst∼ (ext-SubstEnv∼ sL) c))
     ⟫ ≅-sym (rns (toRenameᵗ ρ″) eR
         (ren-after {ν′ = νR″} (toRenameᵗ ρ″) eR (openE T))
         (rename∼ (extᵗ (toRenameᵗ ρ)) eL
           (subst∼ (ext-SubstEnv∼ sL) c))))
    where
    νR″ = renameEnv∼ ρ″ (renameEnv∼ ρ νL)
    eR = renameEnv∼-preserves ρ″ (renameEnv∼ ρ νL)
    R = renAfter {ν′ = νR″} (toRenameᵗ ρ″) eR (openE T)

  -- at the old variables, envL has the casts of sL renamed along ρ and
  -- then ρ″
  πL : Θ ⇒ʳ Θ″
  πL Y = toRenameᵗ ρ″ (toRenameᵗ ρ Y)

  eπL : ∀ X → renameEnv∼ ρ″ (renameEnv∼ ρ νL) ‼ πL X ≡ νL ‼ X
  eπL X = trans (renameEnv∼-preserves ρ″ (renameEnv∼ ρ νL) (toRenameᵗ ρ X))
    (renameEnv∼-preserves ρ νL X)

  M-suc : SRel suc M
    (renAfter {ν′ = renameEnv∼ ρ″ (renameEnv∼ ρ νL)} πL eπL (idE {μ = νL}))
  rself M-suc X = hrefl
  rto M-suc X e e′ = !-≅ hrefl
  rfrom M-suc X e e′ = ？-≅ hrefl
  rcto M-suc X e e′ = !-≅ hrefl
  rcfrom M-suc X e e′ = ？-≅ hrefl

  envL-old : ∀ {τ : ℕ.suc Δ ⇒ˢ Θ″} (h : ∀ X → σC X ≡ τ X)
    → Agree suc
        (renAfter {ν′ = renameEnv∼ ρ″ (renameEnv∼ ρ νL)} πL eπL sL)
        (envL h)
  aself (envL-old h) X =
    sl-≅ (h (suc X)) _ ⟫ sr-≅ (h (suc X)) _
    ⟫ subst-⇑ πL eπL M-suc (self sL X)
  ato (envL-old h) X e e′ =
    sl-≅ (h (suc X)) _ ⟫ subst-⇑ πL eπL M-suc (to-★ sL X e)
    ⟫ ≡→≅ (cong (λ q → rename∼ πL eπL (to-★ sL X q)) (uip e e′))
  afrom (envL-old h) X e e′ =
    sr-≅ (h (suc X)) _ ⟫ subst-⇑ πL eπL M-suc (from-★ sL X e)
    ⟫ ≡→≅ (cong (λ q → rename∼ πL eπL (from-★ sL X q)) (uip e e′))
  acto (envL-old h) X e e′ =
    sl-≅ (h (suc X)) _ ⟫ subst-⇑ πL eπL M-suc (cross-to-★ sL X e)
    ⟫ ≡→≅ (cong (λ q → rename∼ πL eπL (cross-to-★ sL X q)) (uip e e′))
  acfrom (envL-old h) X e e′ =
    sr-≅ (h (suc X)) _ ⟫ subst-⇑ πL eπL M-suc (cross-from-★ sL X e)
    ⟫ ≡→≅ (cong (λ q → rename∼ πL eπL (cross-from-★ sL X q)) (uip e e′))

-- The right's body cast c at the extended interpretation (`castR₂`):
-- sR is the cast's environment at w and ρS the renaming of the right's
-- world after its allocation into the future w″.  `envR h` is the
-- environment to take for `sR (hyp₂ e″)`, at any substitution τ equal
-- to σC.
module CastR {Δ′ Θ Θ″} {ν′ : Env∼ Δ′} {νR : Env∼ Θ} {σR : Δ′ ⇒ˢ Θ}
    (sR : SubstEnv∼ ν′ νR σR) (ρS : ℕ.suc Θ ↪ᵗ Θ″) where

  νC : Env∼ Θ″
  νC = renameEnv∼ ρS (renameEnv∼ wk↪ᵗ νR)

  ρC : Θ ⇒ʳ Θ″
  ρC X = toRenameᵗ ρS (toRenameᵗ wk↪ᵗ X)

  eW : ∀ X → renameEnv∼ wk↪ᵗ νR ‼ toRenameᵗ wk↪ᵗ X ≡ νR ‼ X
  eW = renameEnv∼-preserves wk↪ᵗ νR

  eS : ∀ X → νC ‼ toRenameᵗ ρS X ≡ renameEnv∼ wk↪ᵗ νR ‼ X
  eS = renameEnv∼-preserves ρS (renameEnv∼ wk↪ᵗ νR)

  eC : ∀ X → νC ‼ ρC X ≡ νR ‼ X
  eC X = trans (eS (toRenameᵗ wk↪ᵗ X)) (eW X)

  σM : ℕ.suc Θ ⇒ˢ Θ″
  σM X = renameᵗ ρC (singleSubᵗ ★ X)

  -- the right's instantiation, then the closing at `★` and the renaming
  RC : SubstEnv∼ (instᵐ νR) νC σM
  RC = renAfter {ν′ = νC} ρC eC (close-inst-env {μ = νR})

  XE : SubstEnv∼ (instᵐ ν′) νC (λ X → substᵗ σM (extsᵗ σR X))
  XE = seqE (λ X → refl) (inst-SubstEnv∼ sR) RC

  XE-fuse : Fuse (inst-SubstEnv∼ sR) RC XE
  XE-fuse = seq-fuse (λ X → refl) (inst-SubstEnv∼ sR) RC

  σC : Δ′ ⇒ˢ Θ″
  σC X = substᵗ σM (extsᵗ σR (suc X))

  σC-eq : ∀ X → σC X ≡ renameᵗ ρC (σR X)
  σC-eq X = trans (substᵗ-rename σM suc (σR X)) (subst-varᵗ ρC (σR X))

  envR : ∀ {τ : Δ′ ⇒ˢ Θ″} → (∀ X → σC X ≡ τ X) → SubstEnv∼ ν′ νC τ
  envR h = preRen {μ = ν′} {instᵐ ν′} suc (λ X → refl) h XE

  fuseR : ∀ {τ : Δ′ ⇒ˢ Θ″} (h : ∀ X → σC X ≡ τ X)
    → Fuse (close-inst-env {μ = ν′}) (envR h) XE
  fself (fuseR h) zero = hrefl
  fself (fuseR h) (suc X) = sl-≅ (h X) _ ⟫ sr-≅ (h X) _
  fto (fuseR h) zero e = hrefl
  fto (fuseR h) (suc X) e = sl-≅ (h X) _
  ffrom (fuseR h) zero ()
  ffrom (fuseR h) (suc X) e = sr-≅ (h X) _
  fcto (fuseR h) zero ()
  fcto (fuseR h) (suc X) e = sl-≅ (h X) _
  fcfrom (fuseR h) zero ()
  fcfrom (fuseR h) (suc X) e = sr-≅ (h X) _

  castR : ∀ {τ : Δ′ ⇒ˢ Θ″} (h : ∀ X → σC X ≡ τ X) {A B}
      (c : instᵐ ν′ ⊢ A ∼ ⇑ᵗ B) (Q : Term Θ″)
    → Q ⟨ subst∼ (envR h) (c [ ★/0 ]ᶜ) ⟩
      ≡ Q ⟨ renameᵐᶜ ρS (↑ᶜ ((subst-right-∼ (substᵗ-shift σR B)
              (subst∼ (inst-SubstEnv∼ sR) c)) [ ★/0 ]ᶜ)) ⟩
  castR h {B = B} c Q = ≅ᶜ-⟨⟩ Q
    (subst-sr (envR h) (shift-openᵗ B ★) _
     ⟫ subst-subst (fuseR h) c
     ⟫ ≅-sym (subst-subst XE-fuse c)
     ⟫ ≅-sym (rns ρC eC (ren-after {ν′ = νC} ρC eC CI) Z)
     ⟫ ≅-sym (ren-ren {μ₁ = νR} {renameEnv∼ wk↪ᵗ νR} {νC}
         {ρ₁ = toRenameᵗ wk↪ᵗ} {toRenameᵗ ρS} {ρC} eW eS eC (λ X → refl)
         (subst∼ CI Z))
     ⟫ ≅-sym (ren-≅ {ρ = toRenameᵗ ρS} eS eS
         (ren-≅ {ρ = toRenameᵗ wk↪ᵗ} eW eW
           (subst-sr CI (substᵗ-shift σR B) Z)))
     ⟫ ≅-sym (ren-≅ {ρ = toRenameᵗ ρS} eS eS
         (ren-sr {μ = νR} {renameEnv∼ wk↪ᵗ νR} (toRenameᵗ wk↪ᵗ) eW
           (shift-openᵗ (substᵗ σR B) ★) _)))
    where
    CI = close-inst-env {μ = νR}
    Z = subst∼ (inst-SubstEnv∼ sR) c

  -- envR has the casts of sR renamed along ρC
  RC-suc : SRel suc RC (renAfter {ν′ = νC} ρC eC (idE {μ = νR}))
  rself RC-suc X = hrefl
  rto RC-suc X e e′ = !-≅ hrefl
  rfrom RC-suc X e e′ = ？-≅ hrefl
  rcto RC-suc X e e′ = !-≅ hrefl
  rcfrom RC-suc X e e′ = ？-≅ hrefl

  envR-old : ∀ {τ : Δ′ ⇒ˢ Θ″} (h : ∀ X → σC X ≡ τ X)
    → Agree (λ Y → Y) (renAfter {ν′ = νC} ρC eC sR) (envR h)
  aself (envR-old h) X =
    sl-≅ (h X) _ ⟫ sr-≅ (h X) _ ⟫ subst-⇑ ρC eC RC-suc (self sR X)
  ato (envR-old h) X e e′ =
    sl-≅ (h X) _ ⟫ subst-⇑ ρC eC RC-suc (to-★ sR X e)
    ⟫ ≡→≅ (cong (λ q → rename∼ ρC eC (to-★ sR X q)) (uip e e′))
  afrom (envR-old h) X e e′ =
    sr-≅ (h X) _ ⟫ subst-⇑ ρC eC RC-suc (from-★ sR X e)
    ⟫ ≡→≅ (cong (λ q → rename∼ ρC eC (from-★ sR X q)) (uip e e′))
  acto (envR-old h) X e e′ =
    sl-≅ (h X) _ ⟫ subst-⇑ ρC eC RC-suc (cross-to-★ sR X e)
    ⟫ ≡→≅ (cong (λ q → rename∼ ρC eC (cross-to-★ sR X q)) (uip e e′))
  acfrom (envR-old h) X e e′ =
    sr-≅ (h X) _ ⟫ subst-⇑ ρC eC RC-suc (cross-from-★ sR X e)
    ⟫ ≡→≅ (cong (λ q → rename∼ ρC eC (cross-from-★ sR X q)) (uip e e′))

------------------------------------------------------------------------
-- Case 6: the closing at `★` keeps the eager normal form
------------------------------------------------------------------------

-- no `inst` and no `gen` anywhere
NoIG : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ} → μ ⊢ A ∼ B → Set
NoIG (id a) = ⊤
NoIG (c ↦ d) = NoIG c × NoIG d
NoIG (∀ᶜ c) = NoIG c
NoIG (c !) = NoIG c
NoIG (？ c) = NoIG c
NoIG ((inst c) n) = ⊥
NoIG ((gen c) n) = ⊥
NoIG bot-elim = ⊤
NoIG bot-intro = ⊤

private
  noig-eager : ∀ {Δ} {μ : Env∼ Δ} {A B} (c : μ ⊢ A ∼ B)
    → NoIG c → Eager c
  noig-eager (id a) n = e-id
  noig-eager (c ↦ d) (n , m) = e-↦ (noig-eager c n) (noig-eager d m)
  noig-eager (∀ᶜ c) n = e-∀ (noig-eager c n)
  noig-eager (c !) n = e-! (noig-eager c n)
  noig-eager (？ c) n = e-？ (noig-eager c n)
  noig-eager ((inst c) x) ()
  noig-eager ((gen c) x) ()
  noig-eager bot-elim n = e-bot-elim
  noig-eager bot-intro n = e-bot-intro

  noig-notinst : ∀ {Δ} {μ : Env∼ Δ} {A B} (c : μ ⊢ A ∼ B)
    → NoIG c → NotInst c
  noig-notinst (id a) n = tt
  noig-notinst (c ↦ d) n = tt
  noig-notinst (∀ᶜ c) n = tt
  noig-notinst (c !) n = tt
  noig-notinst (？ c) n = tt
  noig-notinst ((inst c) x) ()
  noig-notinst ((gen c) x) ()
  noig-notinst bot-elim n = tt
  noig-notinst bot-intro n = tt

  noig-rename : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {A B}
      (ρ : Δ ⇒ʳ Δ′) (e : ∀ X → μ′ ‼ ρ X ≡ μ ‼ X) (c : μ ⊢ A ∼ B)
    → NoIG c → NoIG (rename∼ {μ = μ} {μ′} ρ e c)
  noig-rename ρ e (id ★) n = tt
  noig-rename ρ e (id (‵ ι)) n = tt
  noig-rename ρ e (id (＇ X)) n = tt
  noig-rename {μ = μ} {μ′} ρ e (c ↦ d) (n , m) =
    noig-rename {μ = flipᵐ μ} {flipᵐ μ′} ρ
      (flip-rename-env {μ = μ} {μ′} ρ e) c n
    , noig-rename ρ e d m
  noig-rename {μ = μ} {μ′} ρ e (∀ᶜ c) n =
    noig-rename {μ = extᵐ μ} {extᵐ μ′} (extᵗ ρ) (extᵐ-rename ρ e) c n
  noig-rename ρ e (c !) n = noig-rename ρ e c n
  noig-rename ρ e (？ c) n = noig-rename ρ e c n
  noig-rename ρ e ((inst c) x) ()
  noig-rename ρ e ((gen c) x) ()
  noig-rename ρ e bot-elim n = tt
  noig-rename ρ e bot-intro n = tt

  noig-transport : ∀ {Δ} {μ ν : Env∼ Δ} {A B} (e : Env∼Eq μ ν)
      (c : μ ⊢ A ∼ B)
    → NoIG c → NoIG (transport-env∼ e c)
  noig-transport e (id a) n = tt
  noig-transport e (c ↦ d) (n , m) =
    noig-transport (flipEnv∼Eq e) c n , noig-transport e d m
  noig-transport e (∀ᶜ c) n = noig-transport (extEnv∼Eq e) c n
  noig-transport e (c !) n = noig-transport e c n
  noig-transport e (？ c) n = noig-transport e c n
  noig-transport e ((inst c) x) ()
  noig-transport e ((gen c) x) ()
  noig-transport e bot-elim n = tt
  noig-transport e bot-intro n = tt

  noig-sym : ∀ {Δ} {μ : Env∼ Δ} {A B} (c : μ ⊢ A ∼ B)
    → NoIG c → NoIG (sym∼ c)
  noig-sym (id a) n = tt
  noig-sym (c ↦ d) (n , m) = noig-sym c n , noig-sym d m
  noig-sym (∀ᶜ c) n = noig-transport flip-extᵐ (sym∼ c) (noig-sym c n)
  noig-sym (c !) n = noig-sym c n
  noig-sym (？ c) n = noig-sym c n
  noig-sym ((inst c) x) ()
  noig-sym ((gen c) x) ()
  noig-sym bot-elim n = tt
  noig-sym bot-intro n = tt

  noig-refl : ∀ {Δ} {μ : Env∼ Δ} (A : Ty Δ) → NoIG (refl∼ {μ = μ} A)
  noig-refl (＇ X) = tt
  noig-refl (‵ ι) = tt
  noig-refl ★ = tt
  noig-refl (A ⇒ B) = noig-refl A , noig-refl B
  noig-refl (`∀ A) = noig-refl A

  eager-sr : ∀ {Δ} {μ : Env∼ Δ} {A B B′} (e : B ≡ B′) (c : μ ⊢ A ∼ B)
    → Eager c → Eager (subst-right-∼ e c)
  eager-sr refl c x = x

  eager-sl : ∀ {Δ} {μ : Env∼ Δ} {A A′ B} (e : A ≡ A′) (c : μ ⊢ A ∼ B)
    → Eager c → Eager (subst-left-∼ e c)
  eager-sl refl c x = x

  notinst-sl : ∀ {Δ} {μ : Env∼ Δ} {A A′ B} (e : A ≡ A′) (c : μ ⊢ A ∼ B)
    → NotInst c → NotInst (subst-left-∼ e c)
  notinst-sl refl c x = x

  -- a cast out of a ground type is not an `inst`
  ground-notinst : ∀ {Δ} {μ : Env∼ Δ} {G B : Ty Δ} → Ground G
    → (c : μ ⊢ G ∼ B) → NotInst c
  ground-notinst g (id a) = tt
  ground-notinst g (c ↦ d) = tt
  ground-notinst g (∀ᶜ c) = tt
  ground-notinst g (c !) = tt
  ground-notinst g (？ c) = tt
  ground-notinst ∀★ (inst_ ⦃ z∈A = () ⦄ c n)
  ground-notinst g ((gen c) n) = tt
  ground-notinst g bot-elim = tt
  ground-notinst g bot-intro = tt

  eager-factorI : ∀ {Δ} {μ : Env∼ Δ} {A : Ty (ℕ.suc Δ)}
      (x : instᵐ μ ⊢ A ∼ ★) (nv : NonVar A) (z : zero ∈ᵗ A)
    → Eager x → Eager (factor-inst-star x nv z)
  eager-factorI (_! ⦃ Gᵍ = ★⇒★ ⦄ c) nv z (e-! x) = e-! (e-inst ⦃ nv ⦄ ⦃ z ⦄ x)
  eager-factorI (_! ⦃ Gᵍ = ‵ ι ⦄ c) nv z (e-! x) = e-! (e-inst ⦃ nv ⦄ ⦃ z ⦄ x)
  eager-factorI (_! ⦃ Gᵍ = ＇ zero ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ c) nv z x =
    ⊥-elim (inst-to-var-occurs-impossible c eq nv z)
  eager-factorI (_! ⦃ Gᵍ = ＇ zero ⦄ ⦃ G∼★ = X∼★ᶜ () ⦄ c) nv z x
  eager-factorI (_! ⦃ Gᵍ = ＇ suc X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ c) nv z x =
    ⊥-elim (nonstar-nonvar-to-var-impossible c nv (nv-occ nv z))
  eager-factorI (_! ⦃ Gᵍ = ＇ suc X ⦄ ⦃ G∼★ = X∼★ᶜ eq ⦄ c) nv z x =
    ⊥-elim (nonstar-nonvar-to-var-impossible c nv (nv-occ nv z))
  eager-factorI (_! ⦃ Gᵍ = ∀★ ⦄ c) nv z (e-! x) = e-! (e-inst ⦃ nv ⦄ ⦃ z ⦄ x)
  eager-factorI (？_ c) nv () x
  eager-factorI (inst_ c n) nv z x = ⊥-elim (n refl)

  eager-factorG : ∀ {Δ} {μ : Env∼ Δ} {B : Ty (ℕ.suc Δ)}
      (x : genᵐ μ ⊢ ★ ∼ B) (nv : NonVar B) (z : zero ∈ᵗ B)
    → Eager x → Eager (factor-gen-star x nv z)
  eager-factorG (_! c ⦃ () ⦄) nv z x
  eager-factorG (？_ ⦃ Gᵍ = ★⇒★ ⦄ c) nv z (e-？ x) =
    e-？ (e-gen ⦃ nv ⦄ ⦃ z ⦄ x (ground-notinst ★⇒★ c))
  eager-factorG (？_ ⦃ Gᵍ = ‵ ι ⦄ c) nv z (e-？ x) =
    e-？ (e-gen ⦃ nv ⦄ ⦃ z ⦄ x (ground-notinst (‵ ι) c))
  eager-factorG (？_ ⦃ Gᵍ = ＇ zero ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c) nv z x =
    ⊥-elim (gen-from-var-occurs-impossible c eq nv z)
  eager-factorG (？_ ⦃ Gᵍ = ＇ zero ⦄ ⦃ ★∼G = ★∼Xᶜ () ⦄ c) nv z x
  eager-factorG (？_ ⦃ Gᵍ = ＇ suc X ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c) nv z x =
    ⊥-elim (var-to-nonstar-nonvar-impossible c nv (nv-occ nv z))
  eager-factorG (？_ ⦃ Gᵍ = ＇ suc X ⦄ ⦃ ★∼G = ★∼Xᶜ eq ⦄ c) nv z x =
    ⊥-elim (var-to-nonstar-nonvar-impossible c nv (nv-occ nv z))
  eager-factorG (？_ ⦃ Gᵍ = ∀★ ⦄ c) nv z (e-？ x) =
    e-？ (e-gen ⦃ nv ⦄ ⦃ z ⦄ x (ground-notinst ∀★ c))
  eager-factorG (gen_ c n) nv z x = ⊥-elim (n refl)

  notinst-factorG : ∀ {Δ} {μ : Env∼ Δ} {B : Ty (ℕ.suc Δ)}
      (x : genᵐ μ ⊢ ★ ∼ B) (nv : NonVar B) (z : zero ∈ᵗ B)
    → NotInst (factor-gen-star x nv z)
  notinst-factorG (_! c ⦃ () ⦄) nv z
  notinst-factorG (？_ ⦃ Gᵍ = ★⇒★ ⦄ c) nv z = tt
  notinst-factorG (？_ ⦃ Gᵍ = ‵ ι ⦄ c) nv z = tt
  notinst-factorG (？_ ⦃ Gᵍ = ＇ zero ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c) nv z =
    ⊥-elim (gen-from-var-occurs-impossible c eq nv z)
  notinst-factorG (？_ ⦃ Gᵍ = ＇ zero ⦄ ⦃ ★∼G = ★∼Xᶜ () ⦄ c) nv z
  notinst-factorG (？_ ⦃ Gᵍ = ＇ suc X ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c) nv z = tt
  notinst-factorG (？_ ⦃ Gᵍ = ＇ suc X ⦄ ⦃ ★∼G = ★∼Xᶜ eq ⦄ c) nv z = tt
  notinst-factorG (？_ ⦃ Gᵍ = ∀★ ⦄ c) nv z = tt
  notinst-factorG (gen_ c n) nv z = ⊥-elim (n refl)

-- every field of s is free of `inst` and `gen`
record NoIGEnv {Δ Θ} {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : Δ ⇒ˢ Θ}
    (s : SubstEnv∼ μ ν σ) : Set where
  field
    gself : ∀ X → NoIG (self s X)
    gto : ∀ X e → NoIG (to-★ s X e)
    gfrom : ∀ X e → NoIG (from-★ s X e)
    gcto : ∀ X e → NoIG (cross-to-★ s X e)
    gcfrom : ∀ X e → NoIG (cross-from-★ s X e)

open NoIGEnv public

module _ {Δ Θ} {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : Δ ⇒ˢ Θ}
    {s : SubstEnv∼ μ ν σ} where

  private
    up : ∀ {v} {A B} (c : ν ⊢ A ∼ B) → NoIG c → NoIG (⇑ᶜ {v = v} c)
    up {v} c = noig-rename {μ = ν} {v ∷ ν} suc (λ Y → refl) c

  ig-ext : NoIGEnv s → NoIGEnv (ext-SubstEnv∼ s)
  gself (ig-ext g) zero = tt
  gself (ig-ext g) (suc X) = up (self s X) (gself g X)
  gto (ig-ext g) zero ()
  gto (ig-ext g) (suc X) e = up (to-★ s X e) (gto g X e)
  gfrom (ig-ext g) zero ()
  gfrom (ig-ext g) (suc X) e = up (from-★ s X e) (gfrom g X e)
  gcto (ig-ext g) zero ()
  gcto (ig-ext g) (suc X) e = up (cross-to-★ s X e) (gcto g X e)
  gcfrom (ig-ext g) zero ()
  gcfrom (ig-ext g) (suc X) e = up (cross-from-★ s X e) (gcfrom g X e)

  ig-inst : NoIGEnv s → NoIGEnv (inst-SubstEnv∼ s)
  gself (ig-inst g) zero = tt
  gself (ig-inst g) (suc X) = up (self s X) (gself g X)
  gto (ig-inst g) zero e = tt
  gto (ig-inst g) (suc X) e = up (to-★ s X e) (gto g X e)
  gfrom (ig-inst g) zero ()
  gfrom (ig-inst g) (suc X) e = up (from-★ s X e) (gfrom g X e)
  gcto (ig-inst g) zero ()
  gcto (ig-inst g) (suc X) e = up (cross-to-★ s X e) (gcto g X e)
  gcfrom (ig-inst g) zero ()
  gcfrom (ig-inst g) (suc X) e = up (cross-from-★ s X e) (gcfrom g X e)

  ig-gen : NoIGEnv s → NoIGEnv (gen-SubstEnv∼ s)
  gself (ig-gen g) zero = tt
  gself (ig-gen g) (suc X) = up (self s X) (gself g X)
  gto (ig-gen g) zero ()
  gto (ig-gen g) (suc X) e = up (to-★ s X e) (gto g X e)
  gfrom (ig-gen g) zero e = tt
  gfrom (ig-gen g) (suc X) e = up (from-★ s X e) (gfrom g X e)
  gcto (ig-gen g) zero ()
  gcto (ig-gen g) (suc X) e = up (cross-to-★ s X e) (gcto g X e)
  gcfrom (ig-gen g) zero ()
  gcfrom (ig-gen g) (suc X) e = up (cross-from-★ s X e) (gcfrom g X e)

  ig-flip : NoIGEnv s → NoIGEnv (flip-SubstEnv∼ s)
  gself (ig-flip g) X = noig-sym (self s X) (gself g X)
  gto (ig-flip g) X e = noig-sym (from-★ s X P) (gfrom g X P)
    where P = flipVar∼-to-X∼★ (flipᵐ-‼⁻ μ X e)
  gfrom (ig-flip g) X e = noig-sym (to-★ s X P) (gto g X P)
    where P = flipVar∼-to-★∼X (flipᵐ-‼⁻ μ X e)
  gcto (ig-flip g) X e = noig-sym (cross-from-★ s X P) (gcfrom g X P)
    where P = flipVar∼-to-★∼X∼★ (flipᵐ-‼⁻ μ X e)
  gcfrom (ig-flip g) X e = noig-sym (cross-to-★ s X P) (gcto g X P)
    where P = flipVar∼-to-★∼X∼★ (flipᵐ-‼⁻ μ X e)

-- substitution keeps a head that is not `inst`
subst-notinst : ∀ {Δ Θ} {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : Δ ⇒ˢ Θ}
    {s : SubstEnv∼ μ ν σ} {A B}
  → NoIGEnv s → (c : μ ⊢ A ∼ B) → NotInst c → NotInst (subst∼ s c)
subst-notinst g (id ★) t = tt
subst-notinst g (id (‵ ι)) t = tt
subst-notinst {s = s} g (id (＇ X)) t = noig-notinst (self s X) (gself g X)
subst-notinst g (c ↦ d) t = tt
subst-notinst g (∀ᶜ c) t = tt
subst-notinst g (_! ⦃ Gᵍ = ★⇒★ ⦄ c) t = tt
subst-notinst g (_! ⦃ Gᵍ = ‵ ι ⦄ c) t = tt
subst-notinst {s = s} g
    (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ e ⦄ (id (＇ _))) t =
  noig-notinst (to-★ s X e) (gto g X e)
subst-notinst g (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ e ⦄ (？_ c) ⦃ () ⦄) t
subst-notinst g
    (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ e ⦄ c@(inst_ c₀ n) ⦃ a ⦄) t =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all a)
subst-notinst {s = s} g
    (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ e ⦄ (id (＇ _))) t =
  noig-notinst (cross-to-★ s X e) (gcto g X e)
subst-notinst g (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ e ⦄ (？_ c) ⦃ () ⦄) t
subst-notinst g
    (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ e ⦄ c@(inst_ c₀ n) ⦃ a ⦄) t =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all a)
subst-notinst g (_! ⦃ Gᵍ = ∀★ ⦄ c) t = tt
subst-notinst g (？_ ⦃ Gᵍ = ★⇒★ ⦄ c) t = tt
subst-notinst g (？_ ⦃ Gᵍ = ‵ ι ⦄ c) t = tt
subst-notinst {s = s} g
    (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ e ⦄ (id (＇ _))) t =
  noig-notinst (from-★ s X e) (gfrom g X e)
subst-notinst g (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ e ⦄ (_! c) ⦃ () ⦄) t
subst-notinst g
    (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ e ⦄ c@(gen_ c₀ n) ⦃ b ⦄) t =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all b)
subst-notinst {s = s} g
    (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ e ⦄ (id (＇ _))) t =
  noig-notinst (cross-from-★ s X e) (gcfrom g X e)
subst-notinst g (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ e ⦄ (_! c) ⦃ () ⦄) t
subst-notinst g
    (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ e ⦄ c@(gen_ c₀ n) ⦃ b ⦄) t =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all b)
subst-notinst g (？_ ⦃ Gᵍ = ∀★ ⦄ c) t = tt
subst-notinst g (inst_ c n) ()
subst-notinst {σ = σ} g (gen_ {A = A} c n) t with substᵗ σ A ≟Ty ★
subst-notinst {σ = σ} g (gen_ {A = A} c n) t | no n₁ = tt
subst-notinst {σ = σ} {s} g (gen_ {A = A} ⦃ nv ⦄ ⦃ z ⦄ c n) t
    | yes e =
  notinst-sl (sym e) _
    (notinst-factorG
      (subst-left-∼ (sh σ {A} e) (subst∼ (gen-SubstEnv∼ s) c))
      (substNonVar (extsᵗ σ) nv) (subst-∈ᵗ z var-∈))
subst-notinst g bot-elim t = tt
subst-notinst g bot-intro t = tt

-- substitution keeps the eager normal form
subst-eager : ∀ {Δ Θ} {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : Δ ⇒ˢ Θ}
    {s : SubstEnv∼ μ ν σ} {A B}
  → NoIGEnv s → (c : μ ⊢ A ∼ B) → Eager c → Eager (subst∼ s c)
subst-eager g (id ★) x = e-id
subst-eager g (id (‵ ι)) x = e-id
subst-eager {s = s} g (id (＇ X)) x = noig-eager (self s X) (gself g X)
subst-eager g (c ↦ d) (e-↦ x y) =
  e-↦ (subst-eager (ig-flip g) c x) (subst-eager g d y)
subst-eager g (∀ᶜ c) (e-∀ x) = e-∀ (subst-eager (ig-ext g) c x)
subst-eager g (_! ⦃ Gᵍ = ★⇒★ ⦄ c) (e-! x) = e-! ⦃ Ans = _ ⦄ (subst-eager g c x)
subst-eager g (_! ⦃ Gᵍ = ‵ ι ⦄ c) (e-! x) = e-! ⦃ Ans = _ ⦄ (subst-eager g c x)
subst-eager {s = s} g
    (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ e ⦄ (id (＇ _))) x =
  noig-eager (to-★ s X e) (gto g X e)
subst-eager g (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ e ⦄ (？_ c) ⦃ () ⦄) x
subst-eager g
    (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ e ⦄ c@(inst_ c₀ n) ⦃ a ⦄) x =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all a)
subst-eager {s = s} g
    (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ e ⦄ (id (＇ _))) x =
  noig-eager (cross-to-★ s X e) (gcto g X e)
subst-eager g (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ e ⦄ (？_ c) ⦃ () ⦄) x
subst-eager g
    (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ e ⦄ c@(inst_ c₀ n) ⦃ a ⦄) x =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all a)
subst-eager g (_! ⦃ Gᵍ = ∀★ ⦄ c) (e-! x) = e-! ⦃ Ans = _ ⦄ (subst-eager g c x)
subst-eager g (？_ ⦃ Gᵍ = ★⇒★ ⦄ c) (e-？ x) = e-？ ⦃ Bns = _ ⦄ (subst-eager g c x)
subst-eager g (？_ ⦃ Gᵍ = ‵ ι ⦄ c) (e-？ x) = e-？ ⦃ Bns = _ ⦄ (subst-eager g c x)
subst-eager {s = s} g
    (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ e ⦄ (id (＇ _))) x =
  noig-eager (from-★ s X e) (gfrom g X e)
subst-eager g (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ e ⦄ (_! c) ⦃ () ⦄) x
subst-eager g
    (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ e ⦄ c@(gen_ c₀ n) ⦃ b ⦄) x =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all b)
subst-eager {s = s} g
    (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ e ⦄ (id (＇ _))) x =
  noig-eager (cross-from-★ s X e) (gcfrom g X e)
subst-eager g (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ e ⦄ (_! c) ⦃ () ⦄) x
subst-eager g
    (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ e ⦄ c@(gen_ c₀ n) ⦃ b ⦄) x =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all b)
subst-eager g (？_ ⦃ Gᵍ = ∀★ ⦄ c) (e-？ x) = e-？ ⦃ Bns = _ ⦄ (subst-eager g c x)
subst-eager {σ = σ} g (inst_ {B = B} c n) (e-inst x)
    with substᵗ σ B ≟Ty ★
subst-eager {σ = σ} {s} g (inst_ {B = B} c n) (e-inst x) | no n₁ =
  e-inst ⦃ Anv = _ ⦄ ⦃ z∈A = _ ⦄ (eager-sr (substᵗ-shift σ B) _
    (subst-eager (ig-inst g) c x))
subst-eager {σ = σ} {s} g (inst_ {B = B} ⦃ nv ⦄ ⦃ z ⦄ c n) (e-inst x)
    | yes e =
  eager-sr (sym e) _
    (eager-factorI
      (subst-right-∼ (sh σ {B} e) (subst∼ (inst-SubstEnv∼ s) c))
      (substNonVar (extsᵗ σ) nv) (subst-∈ᵗ z var-∈)
      (eager-sr (sh σ {B} e) _ (subst-eager (ig-inst g) c x)))
subst-eager {σ = σ} g (gen_ {A = A} c n) (e-gen x t)
    with substᵗ σ A ≟Ty ★
subst-eager {σ = σ} {s} g (gen_ {A = A} c n) (e-gen x t) | no n₁ =
  e-gen ⦃ Bnv = _ ⦄ ⦃ z∈B = _ ⦄
    (eager-sl (substᵗ-shift σ A) _ (subst-eager (ig-gen g) c x))
    (notinst-sl (substᵗ-shift σ A) _ (subst-notinst (ig-gen g) c t))
subst-eager {σ = σ} {s} g (gen_ {A = A} ⦃ nv ⦄ ⦃ z ⦄ c n) (e-gen x t)
    | yes e =
  eager-sl (sym e) _
    (eager-factorG
      (subst-left-∼ (sh σ {A} e) (subst∼ (gen-SubstEnv∼ s) c))
      (substNonVar (extsᵗ σ) nv) (subst-∈ᵗ z var-∈)
      (eager-sl (sh σ {A} e) _ (subst-eager (ig-gen g) c x)))
subst-eager g bot-elim x = e-bot-elim
subst-eager g bot-intro x = e-bot-intro

close-noig : ∀ {Δ} {μ : Env∼ Δ} → NoIGEnv (close-inst-env {μ = μ})
gself close-noig X = noig-refl (singleSubᵗ ★ X)
gto close-noig zero e = tt
gto close-noig (suc X) e = tt
gfrom close-noig zero ()
gfrom close-noig (suc X) e = tt
gcto close-noig zero ()
gcto close-noig (suc X) e = tt
gcfrom close-noig zero ()
gcfrom close-noig (suc X) e = tt

-- the closing at `★` keeps the eager normal form (the right's cast in
-- the induction hypothesis of case 6)
eager-close : ∀ {Δ} {μ : Env∼ Δ} {A : Ty (ℕ.suc Δ)} {B : Ty Δ}
    (c : instᵐ μ ⊢ A ∼ ⇑ᵗ B)
  → Eager c → Eager (c [ ★/0 ]ᶜ)
eager-close {B = B} c x =
  eager-sr (shift-openᵗ B ★) _ (subst-eager close-noig c x)

------------------------------------------------------------------------
-- Case 6: the induction measure decreases
------------------------------------------------------------------------

castSize-close-≤ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty (ℕ.suc Δ)} {B : Ty Δ}
    (c : instᵐ μ ⊢ A ∼ ⇑ᵗ B)
  → castSize (c [ ★/0 ]ᶜ) ≤ castSize c
castSize-close-≤ c =
  subst (_≤ castSize c) (castSize-↑ᶜ (c [ ★/0 ]ᶜ)) (castSize-close-inst-≤ c)

-- the induction hypothesis of case 6 is at a smaller pair of casts
castSize-case6 : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′}
    {C₁ A₁ : Ty (ℕ.suc Δ)} {C₁′ : Ty (ℕ.suc Δ′)} {B′ : Ty Δ′}
    ⦃ Anv′ : NonVar C₁′ ⦄ ⦃ z′ : zero ∈ᵗ C₁′ ⦄
    (c₁ : extᵐ ν ⊢ C₁ ∼ A₁) (c₁′ : instᵐ ν′ ⊢ C₁′ ∼ ⇑ᵗ B′)
    (B≢★ : B′ ≢ ★)
  → castSize c₁ + castSize (c₁′ [ ★/0 ]ᶜ)
    < castSize (∀ᶜ c₁) + castSize ((inst c₁′) B≢★)
castSize-case6 c₁ c₁′ B≢★ =
  s≤s (+-monoʳ-≤ (castSize c₁)
    (≤-trans (castSize-close-≤ c₁′) (n≤1+n (castSize c₁′))))
