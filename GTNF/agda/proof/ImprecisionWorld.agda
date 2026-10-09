module proof.ImprecisionWorld where

-- File Charter:
--   * HELPER FACTS ABOUT THE WORLDS OF ImprecisionWorld (an ordinary
--     helper module; no statements of major lemmas).
--   * NAMED UNIQUENESS (design.md D25): it holds trivially on a side
--     with at most one name (`namedᴸ-≤1`, `namedᴿ-≤1`, with `≤1-[]`,
--     `≤1-∷[]`), which covers most example worlds: `NamedUniqueᴸ W`
--     is `namedᴸ-≤1 W ≤1-[]` when Δ has no name.
--   * RENAMING: `NonVar`, `NonStar` and `_∈ᵗ_` along a renaming;
--     payload imprecision `RepImp` (D23) along a renaming of the free
--     rep. vars of each side that maps paired rep. vars to paired rep.
--     vars (`⊑ᴿ-ren`; local ∀-bound variables are untouched, the
--     renaming acts under `extN (length μ)`).
--   * THE JOINED WORLD `W ⊕⁺^ β` (the join of the opening of
--     `bind 0 β`, design.md D31; history: D26's opening, D27's pop;
--     before D26 the premise world of ∀⊑⟪+⟫) IS WELL FORMED (`wf-⊕⁺`)
--     when W is, β:=★, and β has no left partner to which a type
--     variable of Δ is bound (`NoNamedPartner`, the scoped form of
--     D13's dropped `NoLeftPartner`).  β may have other left partners,
--     e.g. a store rep. var of an earlier catch-up
--     (proof/DGG/notes/D25.md, L3c/R3c).
--   * PERMISSIONS (design.md D28, D31): `permit-here` (a permitted
--     rep. var at the head) and `here★`, for the derived marks of
--     example worlds; a boundary's permissions keep well-formedness
--     (`wf+κ`) and keep a permission (`permit-++`, `hasPP-+κ`);
--     R1/R2's condition read as membership (`unpermitted→`,
--     `→unpermitted`), its failure `HasPermittedPartner`/`r1-fails`, and
--     its invariance under a boundary (`unpermitted-int`, `hasPP-int`,
--     `hasPP-conv`: an interior or conversion world keeps ϱ and κ).

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length; map; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; [])
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Types
open import Ctx
open import Imprecision using (ImpEnv; X⊑X; X⊑★; extᵐ; instᵐ)
open import Coercion
  using (NonVar; nv-ℕ; nv-𝔹; nv-★; nv-⇒; nv-∀;
         NonStar; ns-var; ns-ℕ; ns-𝔹; ns-⇒; ns-∀;
         _∈ᵗ_; ∈-var; ∈-⇒ˡ; ∈-⇒ʳ; ∈-∀)
open import ImprecisionWorld
open import proof.Ctx using (renameᵗ-cong; renameᵗ-⇑; ∋ˡ-ren⁻)
open import proof.Occurs using (∈-⇒ʳ′)

private
  variable
    Δ Δ′ Δ₁ Δ′₁ Δᵢ Δ′ᵢ Δᶜ Δ′ᶜ : Ctxᵗ

------------------------------------------------------------------------
-- 1. Named uniqueness on a side with at most one name
------------------------------------------------------------------------

AtMostOneName : TyCtx → Set
AtMostOneName ns = ∀ {α α′} → ns ∋ᵅ α → ns ∋ᵅ α′ → α ≡ α′

≤1-[] : AtMostOneName []
≤1-[] (_ , ()) _

≤1-∷[] : ∀ {γ} → AtMostOneName (γ ∷ [])
≤1-∷[] (_ , here) (_ , here) = refl
≤1-∷[] (_ , here) (_ , there ())
≤1-∷[] (_ , there ()) _

-- the world is explicit: `NamedUniqueᴸ W` unfolds to a Π-type, from
-- which W cannot be inferred
namedᴸ-≤1 : (W : World Δ Δ′) → AtMostOneName (names Δ) → NamedUniqueᴸ W
namedᴸ-≤1 W h a a′ _ _ _ = h a a′

namedᴿ-≤1 : (W : World Δ Δ′) → AtMostOneName (names Δ′) → NamedUniqueᴿ W
namedᴿ-≤1 W h _ b b′ _ _ = h b b′

------------------------------------------------------------------------
-- 2. Side conditions along a renaming
------------------------------------------------------------------------

∈ᵗ-ren : ∀ {X A} (ρ : Renameᵗ) → X ∈ᵗ A → ρ X ∈ᵗ renameᵗ ρ A
∈ᵗ-ren ρ ∈-var      = ∈-var
∈ᵗ-ren ρ (∈-⇒ˡ p)   = ∈-⇒ˡ (∈ᵗ-ren ρ p)
∈ᵗ-ren ρ (∈-⇒ʳ _ p) = ∈-⇒ʳ′ (∈ᵗ-ren ρ p)
∈ᵗ-ren ρ (∈-∀ p)    = ∈-∀ (∈ᵗ-ren (extᵗ ρ) p)

nonvar-ren : ∀ {A} (ρ : Renameᵗ) → NonVar A → NonVar (renameᵗ ρ A)
nonvar-ren ρ nv-ℕ = nv-ℕ
nonvar-ren ρ nv-𝔹 = nv-𝔹
nonvar-ren ρ nv-★ = nv-★
nonvar-ren ρ nv-⇒ = nv-⇒
nonvar-ren ρ nv-∀ = nv-∀

nonstar-ren : ∀ {A} (ρ : Renameᵗ) → NonStar A → NonStar (renameᵗ ρ A)
nonstar-ren ρ ns-var = ns-var
nonstar-ren ρ ns-ℕ   = ns-ℕ
nonstar-ren ρ ns-𝔹   = ns-𝔹
nonstar-ren ρ ns-⇒   = ns-⇒
nonstar-ren ρ ns-∀   = ns-∀

renameᵗ-id : ∀ A → renameᵗ (λ X → X) A ≡ A
renameᵗ-id (` X)   = refl
renameᵗ-id `ℕ      = refl
renameᵗ-id `𝔹      = refl
renameᵗ-id ★       = refl
renameᵗ-id (A ⇒ B) = trans (cong (_⇒ renameᵗ (λ X → X) B) (renameᵗ-id A))
                           (cong (A ⇒_) (renameᵗ-id B))
renameᵗ-id (`∀ A)  =
  cong `∀ (trans (renameᵗ-cong ext-id A) (renameᵗ-id A))
  where
  ext-id : ∀ X → extᵗ (λ Y → Y) X ≡ X
  ext-id zero    = refl
  ext-id (suc X) = refl

------------------------------------------------------------------------
-- 3. Payload imprecision along a renaming of the free rep. vars
------------------------------------------------------------------------

-- a local variable (index < length μ) is untouched
extN-local : ∀ {A : Set} {μ : List A} {X m} (f : Renameᵗ)
  → μ ∋ˡ X := m → extN (length μ) f X ≡ X
extN-local f here      = refl
extN-local f (there d) = cong suc (extN-local f d)

-- a free rep. var (index length μ + α) is renamed
extN-+ : ∀ n (f : Renameᵗ) α → extN n f (n + α) ≡ n + f α
extN-+ zero    f α = refl
extN-+ (suc n) f α = cong suc (extN-+ n f α)

PairedRen : World Δ Δ′ → World Δ₁ Δ′₁ → Renameᵗ → Renameᵗ → Set
PairedRen W W₁ f g = ∀ {α β} → Paired W α β → Paired W₁ (f α) (g β)

⊑ᴿ-ren : ∀ {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁} (f g : Renameᵗ)
  → PairedRen W W₁ f g
  → ∀ {μ R R′} → μ ⊢ R ⊑ᴿ⟨ W ⟩ R′
  → μ ⊢ renameᵗ (extN (length μ) f) R ⊑ᴿ⟨ W₁ ⟩
        renameᵗ (extN (length μ) g) R′
⊑ᴿ-ren f g h ★⊑★ = ★⊑★
⊑ᴿ-ren f g h (ι⊑ι base-ℕ) = ι⊑ι base-ℕ
⊑ᴿ-ren f g h (ι⊑ι base-𝔹) = ι⊑ι base-𝔹
⊑ᴿ-ren f g h (X⊑X d)
  rewrite extN-local f d | extN-local g d = X⊑X d
⊑ᴿ-ren f g h (α⊑β {μ = μ} {α = α} {β = β} p)
  rewrite extN-+ (length μ) f α | extN-+ (length μ) g β = α⊑β (h p)
⊑ᴿ-ren f g h (⇒⊑⇒ p q) = ⇒⊑⇒ (⊑ᴿ-ren f g h p) (⊑ᴿ-ren f g h q)
⊑ᴿ-ren f g h (∀⊑∀ p) = ∀⊑∀ (⊑ᴿ-ren f g h p)
⊑ᴿ-ren f g h (⇒⊑★ p q) = ⇒⊑★ (⊑ᴿ-ren f g h p) (⊑ᴿ-ren f g h q)
⊑ᴿ-ren f g h (ι⊑★ base-ℕ) = ι⊑★ base-ℕ
⊑ᴿ-ren f g h (ι⊑★ base-𝔹) = ι⊑★ base-𝔹
⊑ᴿ-ren f g h (X⊑★ d) rewrite extN-local f d = X⊑★ d
⊑ᴿ-ren f g h (α⊑★ {μ = μ} {α = α})
  rewrite extN-+ (length μ) f α = α⊑★
⊑ᴿ-ren {W₁ = W₁} f g h (∀⊑ {μ = μ} {R′ = R′} nv occ p) =
  ∀⊑ (nonvar-ren (extᵗ (extN (length μ) f)) nv)
     (∈ᵗ-ren (extᵗ (extN (length μ) f)) occ)
     (subst (λ T → instᵐ μ ⊢ _ ⊑ᴿ⟨ W₁ ⟩ T)
            (renameᵗ-⇑ (extN (length μ) g) R′) (⊑ᴿ-ren f g h p))
⊑ᴿ-ren f g h ∀★⊑★ = ∀★⊑★
⊑ᴿ-ren f g h (∀⊑★ {μ = μ} ns p) =
  ∀⊑★ (nonstar-ren (extᵗ (extN (length μ) f)) ns) (⊑ᴿ-ren f g h p)
⊑ᴿ-ren f g h bot-elim = bot-elim
⊑ᴿ-ren f g h bot⊑★ = bot⊑★

------------------------------------------------------------------------
-- 4. The joined world W ⊕⁺^ β (formerly ∀⊑⟪+⟫'s premise world)
------------------------------------------------------------------------

shiftᴸ-∋ : ∀ {ϱ α β} → ϱ ∋ᵨ α ⇔ β → shiftᴸ ϱ ∋ᵨ suc α ⇔ β
shiftᴸ-∋ here⇔      = here⇔
shiftᴸ-∋ (there⇔ x) = there⇔ (shiftᴸ-∋ x)

shiftᴸ-∋⁻ : ∀ {a β} (ϱ : RepRel) → shiftᴸ ϱ ∋ᵨ a ⇔ β
  → ∃[ α ] ((a ≡ suc α) × (ϱ ∋ᵨ α ⇔ β))
shiftᴸ-∋⁻ ((α , b) ∷ ϱ) here⇔ = α , refl , here⇔
shiftᴸ-∋⁻ ((α , b) ∷ ϱ) (there⇔ x) with shiftᴸ-∋⁻ ϱ x
shiftᴸ-∋⁻ ((α , b) ∷ ϱ) (there⇔ x) | α′ , eq , y = α′ , eq , there⇔ y

-- a named left rep. var other than the new binder's is one of Δ's
named-suc : ∀ (ns : TyCtx) {α} → (zero ∷ shiftReps ns) ∋ᵅ suc α
  → ns ∋ᵅ α
named-suc ns (_ , there d) with ∋ˡ-ren⁻ suc ns d
named-suc ns (_ , there d) | α , d′ , refl = _ , d′

-- the right names inside the boundary: β's, and Δ′'s
named-bind : ∀ {β} (ns : TyCtx) {b} → (β ∷ ns) ∋ᵅ b
  → (b ≡ β) ⊎ (ns ∋ᵅ b)
named-bind ns (_ , here)    = inj₁ refl
named-bind ns (_ , there d) = inj₂ (_ , d)

module _ {W : World Δ Δ′} {β : RVar} where

  private
    W⁺ = W ⊕⁺^ β

  paired-⊕⁺ : PairedRen W W⁺ suc (λ b → b)
  paired-⊕⁺ (inj₁ x) = inj₁ (shiftᴸ-∋ x)
  paired-⊕⁺ (inj₂ x) = inj₂ (there⇔ (shiftᴸ-∋ x))

  -- every pair of the premise world is (0, β) or a shifted pair of W
  paired-⊕⁺⁻ : ∀ {a b} → Paired W⁺ a b
    → ((a ≡ zero) × (b ≡ β)) ⊎ (∃[ α ] ((a ≡ suc α) × Paired W α b))
  paired-⊕⁺⁻ (inj₁ x) with shiftᴸ-∋⁻ (ϱᵍʷ W) x
  paired-⊕⁺⁻ (inj₁ x) | α , eq , y = inj₂ (α , eq , inj₁ y)
  paired-⊕⁺⁻ (inj₂ here⇔) = inj₁ (refl , refl)
  paired-⊕⁺⁻ (inj₂ (there⇔ x)) with shiftᴸ-∋⁻ (ϱˡʷ W) x
  paired-⊕⁺⁻ (inj₂ (there⇔ x)) | α , eq , y = inj₂ (α , eq , inj₂ y)

  -- a pair's agreement survives: the left side is under one more Λ
  agree-⊕⁺ : ∀ {α b} → Agree W α b → Agree W⁺ (suc α) b
  agree-⊕⁺ (abst-abst l r) = abst-abst (r-there-abst l) r
  agree-⊕⁺ (abst-★ l r)    = abst-★ (r-there-abst l) r
  agree-⊕⁺ (rep-rep {R′ = R′} l r p) =
    rep-rep (r-there-abst l) r
      (subst (λ T → [] ⊢ _ ⊑ᴿ⟨ W⁺ ⟩ T) (renameᵗ-id R′)
             (⊑ᴿ-ren suc (λ b → b) paired-⊕⁺ p))

  joint-⊕⁺ : ∀ {ns ns′ n} {ι : ns ↪ n} {ι′ : ns′ ↪ n}
    → Joint (Paired W) ι ι′ → Joint (Paired W⁺) (relabel suc ι) ι′
  joint-⊕⁺ joint[]          = joint[]
  joint-⊕⁺ (both p j)       = both (paired-⊕⁺ p) (joint-⊕⁺ j)
  joint-⊕⁺ (left-only j)    = left-only (joint-⊕⁺ j)
  joint-⊕⁺ (right-only j)   = right-only (joint-⊕⁺ j)

  wf-⊕⁺ : WfWorld W → Δ′ ∋rep β := ★ → NoNamedPartner W β
    → WfWorld W⁺
  wf-⊕⁺ wf hβ nn = wf-world (both (inj₂ here⇔) (joint-⊕⁺ (wf-joint wf)))
                            agree namedᴸ namedᴿ (wf-permits wf)
    where
    agree : ∀ {a b} → Paired W⁺ a b → Agree W⁺ a b
    agree x with paired-⊕⁺⁻ x
    agree x | inj₁ (refl , refl)     = abst-★ r-here hβ
    agree x | inj₂ (α , refl , p)    = agree-⊕⁺ (wf-agree wf p)

    -- each of the two pairs is (0, β) or a shifted pair of W
    PairOf : ℕ → RVar → Set
    PairOf a b = ((a ≡ zero) × (b ≡ β)) ⊎ (∃[ α ] ((a ≡ suc α) × Paired W α b))

    -- two shifted pairs of W at a right name b: b is β's (excluded by
    -- `nn`) or one of Δ′'s (W's named uniqueness)
    shiftedᴸ : ∀ {α α′ b} → names Δ ∋ᵅ α → names Δ ∋ᵅ α′
      → (b ≡ β) ⊎ (names Δ′ ∋ᵅ b) → Paired W α b → Paired W α′ b
      → suc α ≡ suc α′
    shiftedᴸ n n′ (inj₁ refl) p p′ = ⊥-elim (nn n p)
    shiftedᴸ n n′ (inj₂ c) p p′    = cong suc (wf-namedᴸ wf n n′ c p p′)

    namedᴸ-pairs : ∀ {a a′ b}
      → (zero ∷ shiftReps (names Δ)) ∋ᵅ a
      → (zero ∷ shiftReps (names Δ)) ∋ᵅ a′
      → (β ∷ names Δ′) ∋ᵅ b → PairOf a b → PairOf a′ b → a ≡ a′
    namedᴸ-pairs na na′ nb (inj₁ (refl , _)) (inj₁ (refl , _)) = refl
    namedᴸ-pairs na na′ nb (inj₁ (refl , refl)) (inj₂ (_ , refl , p′)) =
      ⊥-elim (nn (named-suc (names Δ) na′) p′)
    namedᴸ-pairs na na′ nb (inj₂ (_ , refl , p)) (inj₁ (refl , refl)) =
      ⊥-elim (nn (named-suc (names Δ) na) p)
    namedᴸ-pairs na na′ nb (inj₂ (_ , refl , p)) (inj₂ (_ , refl , p′)) =
      shiftedᴸ (named-suc (names Δ) na) (named-suc (names Δ) na′)
               (named-bind (names Δ′) nb) p p′

    namedᴸ : NamedUniqueᴸ W⁺
    namedᴸ na na′ nb x y =
      namedᴸ-pairs na na′ nb (paired-⊕⁺⁻ x) (paired-⊕⁺⁻ y)

    -- one shifted pair of W at a right name b, from a named α
    unnamedβ : ∀ {α b} → names Δ ∋ᵅ α → (b ≡ β) ⊎ (names Δ′ ∋ᵅ b)
      → Paired W α b → names Δ′ ∋ᵅ b
    unnamedβ n (inj₁ refl) p = ⊥-elim (nn n p)
    unnamedβ n (inj₂ c) p    = c

    namedᴿ-pairs : ∀ {a b b′}
      → (zero ∷ shiftReps (names Δ)) ∋ᵅ a
      → (β ∷ names Δ′) ∋ᵅ b → (β ∷ names Δ′) ∋ᵅ b′
      → PairOf a b → PairOf a b′ → b ≡ b′
    namedᴿ-pairs na nb nb′ (inj₁ (_ , refl)) (inj₁ (_ , refl)) = refl
    namedᴿ-pairs na nb nb′ (inj₁ (refl , _)) (inj₂ (_ , () , _))
    namedᴿ-pairs na nb nb′ (inj₂ (_ , () , _)) (inj₁ (refl , _))
    namedᴿ-pairs na nb nb′ (inj₂ (_ , refl , p)) (inj₂ (_ , refl , p′)) =
      wf-namedᴿ wf n (unnamedβ n (named-bind (names Δ′) nb) p)
                     (unnamedβ n (named-bind (names Δ′) nb′) p′) p p′
      where n = named-suc (names Δ) na

    namedᴿ : NamedUniqueᴿ W⁺
    namedᴿ na nb nb′ x y =
      namedᴿ-pairs na nb nb′ (paired-⊕⁺⁻ x) (paired-⊕⁺⁻ y)

------------------------------------------------------------------------
-- 5. Permissions (design.md D28)
------------------------------------------------------------------------

≡ᵇ-refl : ∀ n → (n ≡ᵇ n) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc n) = ≡ᵇ-refl n

-- a rep. var at the head of κ is permitted
permit-here : ∀ β κ → permit β (β ∷ κ) ≡ X⊑★
permit-here β κ rewrite ≡ᵇ-refl β = refl

-- a lookup at the head whose value is X⊑★ up to an equation
here★ : ∀ {m} {μ : ImpEnv} → m ≡ X⊑★ → (m ∷ μ) ∋ˡ 0 := X⊑★
here★ refl = here

-- R1/R2's condition, its two readings, and which world (design.md
-- D28; checked first in proof/DGG/notes/PermissionsR.agda §6a)

-- membership in a permission list
infix 4 _∈κ_
data _∈κ_ (β : RVar) : List RVar → Set where
  here∈  : ∀ {κ} → β ∈κ (β ∷ κ)
  there∈ : ∀ {γ κ} → β ∈κ κ → β ∈κ (γ ∷ κ)

T-≡ᵇ : ∀ m n → (m ≡ᵇ n) ≡ true → m ≡ n
T-≡ᵇ zero    zero    _  = refl
T-≡ᵇ zero    (suc n) ()
T-≡ᵇ (suc m) zero    ()
T-≡ᵇ (suc m) (suc n) e  = cong suc (T-≡ᵇ m n e)

permit-∈ : ∀ β κ → permit β κ ≡ X⊑★ → β ∈κ κ
permit-∈ β []      ()
permit-∈ β (γ ∷ κ) h with β ≡ᵇ γ in eq
permit-∈ β (γ ∷ κ) h | true  rewrite T-≡ᵇ β γ eq = here∈
permit-∈ β (γ ∷ κ) h | false = there∈ (permit-∈ β κ h)

∈-permit : ∀ {β κ} → β ∈κ κ → permit β κ ≡ X⊑★
∈-permit {β} {β ∷ κ} here∈ = permit-here β κ
∈-permit {β} {γ ∷ κ} (there∈ m) with β ≡ᵇ γ
∈-permit {β} {γ ∷ κ} (there∈ m) | true  = refl
∈-permit {β} {γ ∷ κ} (there∈ m) | false = ∈-permit m

permit-X⊑X : ∀ β κ → permit β κ ≢ X⊑★ → permit β κ ≡ X⊑X
permit-X⊑X β κ n with permit β κ
permit-X⊑X β κ n | X⊑X = refl
permit-X⊑X β κ n | X⊑★ = ⊥-elim (n refl)

-- `Unpermitted W α` is exactly  ¬ ∃ β. Paired W α β × β ∈ κʷ W
unpermitted→ : ∀ {W : World Δ Δ′} {α} → Unpermitted W α
  → ¬ (Σ[ β ∈ RVar ] Paired W α β × β ∈κ κʷ W)
unpermitted→ u (β , pr , m) with trans (sym (∈-permit m)) (u pr)
... | ()

→unpermitted : ∀ {W : World Δ Δ′} {α}
  → ¬ (Σ[ β ∈ RVar ] Paired W α β × β ∈κ κʷ W) → Unpermitted W α
→unpermitted {W = W} n {β} pr =
  permit-X⊑X β (κʷ W) (λ h → n (β , pr , permit-∈ β (κʷ W) h))

-- the negation, as the negative proofs use it
HasPermittedPartner : World Δ Δ′ → RVar → Set
HasPermittedPartner W α =
  Σ[ β ∈ RVar ] Paired W α β × (permit β (κʷ W) ≡ X⊑★)

r1-fails : ∀ {W : World Δ Δ′} {α} → HasPermittedPartner W α
  → ¬ Unpermitted W α
r1-fails (β , pr , pm) u with trans (sym pm) (u pr)
... | ()

-- WHICH WORLD: a boundary keeps ϱ and κ, so R1 reads the same in the
-- conclusion world W and the interior world Wᵢ (and R2 likewise in the
-- conversion world and the exterior)
Paired-int : ∀ {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ α β}
  → Interior W Θ Θ′ Wᵢ → Paired W α β → Paired Wᵢ α β
Paired-int I (inj₁ h) = inj₁ (subst (λ ϱ → ϱ ∋ᵨ _ ⇔ _) (sym (same-ϱᵍ I)) h)
Paired-int I (inj₂ h) = inj₂ (subst (λ ϱ → ϱ ∋ᵨ _ ⇔ _) (sym (same-ϱˡ I)) h)

Paired-int⁻ : ∀ {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ α β}
  → Interior W Θ Θ′ Wᵢ → Paired Wᵢ α β → Paired W α β
Paired-int⁻ I (inj₁ h) = inj₁ (subst (λ ϱ → ϱ ∋ᵨ _ ⇔ _) (same-ϱᵍ I) h)
Paired-int⁻ I (inj₂ h) = inj₂ (subst (λ ϱ → ϱ ∋ᵨ _ ⇔ _) (same-ϱˡ I) h)

unpermitted-int : ∀ {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ α}
  → Interior W Θ Θ′ Wᵢ → Unpermitted W α → Unpermitted Wᵢ α
unpermitted-int I u {β} pr =
  subst (λ κ → permit β κ ≡ X⊑X) (sym (same-κ I)) (u (Paired-int⁻ I pr))

unpermitted-int⁻ : ∀ {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ α}
  → Interior W Θ Θ′ Wᵢ → Unpermitted Wᵢ α → Unpermitted W α
unpermitted-int⁻ I u {β} pr =
  subst (λ κ → permit β κ ≡ X⊑X) (same-κ I) (u (Paired-int I pr))

hasPP-int : ∀ {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ α}
  → Interior W Θ Θ′ Wᵢ → HasPermittedPartner W α
  → HasPermittedPartner Wᵢ α
hasPP-int I (β , pr , pm) =
  β , Paired-int I pr , subst (λ κ → permit β κ ≡ X⊑★) (sym (same-κ I)) pm

hasPP-conv : ∀ {W : World Δ Δ′} {Wᶜ : World Δᶜ Δ′ᶜ} {Θ Θ′ α}
  → ConversionInterior W Θ Θ′ Wᶜ → HasPermittedPartner W α
  → HasPermittedPartner Wᶜ α
hasPP-conv ci (β , inj₁ h , pm) =
  β , inj₁ (subst (λ ϱ → ϱ ∋ᵨ _ ⇔ _) (sym (conv-same-ϱᵍ ci)) h)
    , subst (λ κ → permit β κ ≡ X⊑★) (sym (conv-same-κ ci)) pm
hasPP-conv ci (β , inj₂ h , pm) =
  β , inj₂ (subst (λ ϱ → ϱ ∋ᵨ _ ⇔ _) (sym (conv-same-ϱˡ ci)) h)
    , subst (λ κ → permit β κ ≡ X⊑★) (sym (conv-same-κ ci)) pm

------------------------------------------------------------------------
-- 6. The permissions a boundary adds (design.md D31)
------------------------------------------------------------------------

private
  ++All : ∀ {A : Set} {P : A → Set} {xs ys}
    → All P xs → All P ys → All P (xs ++ ys)
  ++All []       qs = qs
  ++All (p ∷ ps) qs = p ∷ ++All ps qs

-- payload imprecision and agreement read only ϱ: a world with the
-- same pairs (e.g. `W +κ K`) has the same ones
module _ {W : World Δ Δ′} {W′ : World Δ Δ′}
    (pp : ∀ {α β} → Paired W α β → Paired W′ α β) where
  repW : ∀ {μ R R′} → RepImp W μ R R′ → RepImp W′ μ R R′
  repW ★⊑★          = ★⊑★
  repW (ι⊑ι b)      = ι⊑ι b
  repW (X⊑X h)      = X⊑X h
  repW (α⊑β p)      = α⊑β (pp p)
  repW (⇒⊑⇒ a b)    = ⇒⊑⇒ (repW a) (repW b)
  repW (∀⊑∀ a)      = ∀⊑∀ (repW a)
  repW (⇒⊑★ a b)    = ⇒⊑★ (repW a) (repW b)
  repW (ι⊑★ b)      = ι⊑★ b
  repW (X⊑★ h)      = X⊑★ h
  repW α⊑★          = α⊑★
  repW (∀⊑ nv o a)  = ∀⊑ nv o (repW a)
  repW ∀★⊑★         = ∀★⊑★
  repW (∀⊑★ ns a)   = ∀⊑★ ns (repW a)
  repW bot-elim     = bot-elim
  repW bot⊑★        = bot⊑★

  agreeW : ∀ {α β} → Agree W α β → Agree W′ α β
  agreeW (abst-abst a b) = abst-abst a b
  agreeW (abst-★ a b)    = abst-★ a b
  agreeW (rep-rep a b r) = rep-rep a b (repW r)

-- a world with permissions added is well formed when the added rep.
-- vars are right rep. vars
wf+κ : ∀ {W : World Δ Δ′} {K} → WfWorld W → All (reps Δ′ ∋ʳ_) K
  → WfWorld (W +κ K)
wf+κ {W = W} {K} wf ps = wf-world (wf-joint wf)
  (λ pr → agreeW {W = W} {W′ = W +κ K} (λ p → p) (wf-agree wf pr))
  (wf-namedᴸ wf) (wf-namedᴿ wf) (++All ps (wf-permits wf))

-- more permissions keep a permission
permit-++ : ∀ β K κ → permit β κ ≡ X⊑★ → permit β (K ++ κ) ≡ X⊑★
permit-++ β []      κ p = p
permit-++ β (γ ∷ K) κ p with β ≡ᵇ γ
... | true  = refl
... | false = permit-++ β K κ p

hasPP-+κ : ∀ {W : World Δ Δ′} {K α} → HasPermittedPartner W α
  → HasPermittedPartner (W +κ K) α
hasPP-+κ {W = W} {K} (β , pr , pm) = β , pr , permit-++ β K (κʷ W) pm
