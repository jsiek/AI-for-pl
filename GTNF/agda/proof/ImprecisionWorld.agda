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
--   * THE POPPED WORLD `W ⊕⁺ m ^ β` (the pop of the pending name of
--     `bind 0 β`, design.md D27; D26's opening; before D26 the premise
--     world of ∀⊑⟪+⟫) IS WELL FORMED (`wf-⊕⁺`) when W is,
--     β:=★, and β has no left partner NAMED in Δ (`NoNamedPartner`,
--     the scoped form of D13's dropped `NoLeftPartner`).  β may have
--     unnamed left partners, e.g. a store rep. var of an earlier
--     catch-up (proof/DGG/notes/D25.md, L3c/R3c).

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length; map)
open import Data.List.Relation.Unary.All using (All; [])
open import Data.List.Relation.Unary.AllPairs using (AllPairs; [])
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Types
open import Ctx
open import Imprecision using (VarImp; ImpEnv; extᵐ; instᵐ)
open import Coercion
  using (NonVar; nv-ℕ; nv-𝔹; nv-★; nv-⇒; nv-∀;
         NonStar; ns-var; ns-ℕ; ns-𝔹; ns-⇒; ns-∀;
         _∈ᵗ_; ∈-var; ∈-⇒ˡ; ∈-⇒ʳ; ∈-∀)
open import ImprecisionWorld
open import proof.Ctx using (renameᵗ-cong; renameᵗ-⇑; ∋ˡ-ren⁻)
open import proof.Occurs using (∈-⇒ʳ′)

private
  variable
    Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ

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
-- 4. The popped world W ⊕⁺ m ^ β (formerly ∀⊑⟪+⟫'s premise world)
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

module _ {W : World Δ Δ′} {m : VarImp} {β : RVar} where

  private
    W⁺ = W ⊕⁺ m ^ β

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

  joint-⊕⁺ : ∀ {ns ns′ Ω} {ι : ns ↪ Ω} {ι′ : ns′ ↪ Ω}
    → Joint (Paired W) ι ι′ → Joint (Paired W⁺) (relabel suc ι) ι′
  joint-⊕⁺ joint[]          = joint[]
  joint-⊕⁺ (both p j)       = both (paired-⊕⁺ p) (joint-⊕⁺ j)
  joint-⊕⁺ (left-only j)    = left-only (joint-⊕⁺ j)
  joint-⊕⁺ (right-only j)   = right-only (joint-⊕⁺ j)

  -- at a world with no pending name (design.md D27; the pending names
  -- of W ⊕⁺ m ^ β are W's, moved one position up)
  wf-⊕⁺ : WfWorld W → Δ′ ∋rep β := ★ → NoNamedPartner W β
    → πʷ W ≡ [] → WfWorld W⁺
  wf-⊕⁺ wf hβ nn e = wf-world (both (inj₂ here⇔) (joint-⊕⁺ (wf-joint wf)))
                              agree namedᴸ namedᴿ (no-pending e)
                              (no-pending≢ e)
    where
    no-pending : ∀ {P : ℕ → Set} {π} → π ≡ [] → All P (map suc π)
    no-pending refl = []

    no-pending≢ : ∀ {π} → π ≡ [] → AllPairs _≢_ (map suc π)
    no-pending≢ refl = []

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
