module nu-cancel-id.proof.Flags where

-- File Charter:
--   * LEMMAS ABOUT FLAGS, NAMES AND SPELLING.
--     §1 flag update: hit, miss, idempotence, overwrite, commutation,
--     and the two inclusions (a hide removes names, a reveal adds them).
--     §2 names: a named cell has a name, and a name denotes a named
--     cell; name lookup is functional and injective.  §3 spelling is
--     functional and injective, and a named type can be re-read in a
--     context with more names.  §4 spelling after inserting a cell:
--     an unnamed one at depth k (allocation), or a named one under k
--     binders (a `Λ`, for `crossΛ`).

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂)

open import nu-cancel-id.Types
open import nu-cancel-id.Ctx
open import nu-cancel-id.proof.Types

private
  variable
    Φ Φ′ : Flags
    α β X Y : ℕ
    b b′ b″ : Bool
    A B R R′ : Ty

------------------------------------------------------------------------
-- 1. Flag update
------------------------------------------------------------------------

setFlag-hit : Φ ∋ᶠ α ⦂ b → setFlag α b′ Φ ∋ᶠ α ⦂ b′
setFlag-hit f-here      = f-here
setFlag-hit (f-there f) = f-there (setFlag-hit f)

∋ᶠ-unique : Φ ∋ᶠ α ⦂ b → Φ ∋ᶠ α ⦂ b′ → b ≡ b′
∋ᶠ-unique f-here      f-here      = refl
∋ᶠ-unique (f-there f) (f-there g) = ∋ᶠ-unique f g

true≢false : true ≡ false → ⊥
true≢false ()

false≢true : false ≡ true → ⊥
false≢true ()

-- inside a boundary on cell α, α's flag is the one the entry set
flag-clash : Φ ∋ᶠ α ⦂ b → setFlag α b′ Φ ∋ᶠ α ⦂ b″ → b′ ≡ b″
flag-clash f g = ∋ᶠ-unique (setFlag-hit f) g

setFlag-miss : α ≢ β → Φ ∋ᶠ β ⦂ b → setFlag α b′ Φ ∋ᶠ β ⦂ b
setFlag-miss {α = zero}  α≢β f-here      = ⊥-elim (α≢β refl)
setFlag-miss {α = zero}  α≢β (f-there f) = f-there f
setFlag-miss {α = suc α} α≢β f-here      = f-here
setFlag-miss {α = suc α} α≢β (f-there f) =
  f-there (setFlag-miss (λ eq → α≢β (cong suc eq)) f)

setFlag-miss⁻¹ : α ≢ β → setFlag α b′ Φ ∋ᶠ β ⦂ b → Φ ∋ᶠ β ⦂ b
setFlag-miss⁻¹ {α = zero}  {Φ = _ ∷ _} α≢β f-here      = ⊥-elim (α≢β refl)
setFlag-miss⁻¹ {α = zero}  {Φ = _ ∷ _} α≢β (f-there f) = f-there f
setFlag-miss⁻¹ {α = suc α} {Φ = _ ∷ _} α≢β f-here      = f-here
setFlag-miss⁻¹ {α = suc α} {Φ = _ ∷ _} α≢β (f-there f) =
  f-there (setFlag-miss⁻¹ (λ eq → α≢β (cong suc eq)) f)

setFlag-idem : Φ ∋ᶠ α ⦂ b → setFlag α b Φ ≡ Φ
setFlag-idem f-here      = refl
setFlag-idem (f-there f) = cong (_ ∷_) (setFlag-idem f)

setFlag-twice : ∀ α b b′ Φ → setFlag α b (setFlag α b′ Φ) ≡ setFlag α b Φ
setFlag-twice α       b b′ []       = refl
setFlag-twice zero    b b′ (_ ∷ Φ)  = refl
setFlag-twice (suc α) b b′ (b₀ ∷ Φ) = cong (b₀ ∷_) (setFlag-twice α b b′ Φ)

setFlag-comm : ∀ {α β} b b′ Φ → α ≢ β
  → setFlag α b (setFlag β b′ Φ) ≡ setFlag β b′ (setFlag α b Φ)
setFlag-comm b b′ [] α≢β = refl
setFlag-comm {zero}  {zero}  b b′ (_ ∷ Φ) α≢β = ⊥-elim (α≢β refl)
setFlag-comm {zero}  {suc β} b b′ (_ ∷ Φ) α≢β = refl
setFlag-comm {suc α} {zero}  b b′ (_ ∷ Φ) α≢β = refl
setFlag-comm {suc α} {suc β} b b′ (b₀ ∷ Φ) α≢β =
  cong (b₀ ∷_) (setFlag-comm b b′ Φ (λ eq → α≢β (cong suc eq)))

-- every cell named after a hide was named before it
hide-⊆ : setFlag α false Φ ∋ᶠ β ⦂ true → Φ ∋ᶠ β ⦂ true
hide-⊆ {α = zero}  {Φ = _ ∷ _} (f-there f) = f-there f
hide-⊆ {α = suc α} {Φ = _ ∷ _} f-here      = f-here
hide-⊆ {α = suc α} {Φ = _ ∷ _} (f-there f) = f-there (hide-⊆ f)

-- every cell named before a reveal is named after it
reveal-⊆ : Φ ∋ᶠ β ⦂ true → setFlag α true Φ ∋ᶠ β ⦂ true
reveal-⊆ {α = zero}  f-here      = f-here
reveal-⊆ {α = zero}  (f-there f) = f-there f
reveal-⊆ {α = suc α} f-here      = f-here
reveal-⊆ {α = suc α} (f-there f) = f-there (reveal-⊆ f)

------------------------------------------------------------------------
-- 2. Names
------------------------------------------------------------------------

named-flag : Φ ∋ⁿ X ↦ α → Φ ∋ᶠ α ⦂ true
named-flag n-here       = f-here
named-flag (n-named x)  = f-there (named-flag x)
named-flag (n-hidden x) = f-there (named-flag x)

flag-named : Φ ∋ᶠ α ⦂ true → ∃[ X ] Φ ∋ⁿ X ↦ α
flag-named f-here = _ , n-here
flag-named {Φ = true ∷ Φ} (f-there f) =
  let (X , x) = flag-named f in suc X , n-named x
flag-named {Φ = false ∷ Φ} (f-there f) =
  let (X , x) = flag-named f in X , n-hidden x

∋ⁿ-unique : Φ ∋ⁿ X ↦ α → Φ ∋ⁿ X ↦ β → α ≡ β
∋ⁿ-unique n-here       n-here       = refl
∋ⁿ-unique (n-named x)  (n-named y)  = cong suc (∋ⁿ-unique x y)
∋ⁿ-unique (n-hidden x) (n-hidden y) = cong suc (∋ⁿ-unique x y)

∋ⁿ-inj : Φ ∋ⁿ X ↦ α → Φ ∋ⁿ Y ↦ α → X ≡ Y
∋ⁿ-inj n-here       n-here       = refl
∋ⁿ-inj (n-named x)  (n-named y)  = cong suc (∋ⁿ-inj x y)
∋ⁿ-inj (n-hidden x) (n-hidden y) = ∋ⁿ-inj x y

------------------------------------------------------------------------
-- 3. Spelling
------------------------------------------------------------------------

⇝-unique : Φ ⊢ A ⇝ R → Φ ⊢ A ⇝ R′ → R ≡ R′
⇝-unique (s-var x) (s-var y) = cong `_ (∋ⁿ-unique x y)
⇝-unique s-ℕ       s-ℕ       = refl
⇝-unique s-𝔹       s-𝔹       = refl
⇝-unique (s-⇒ a b) (s-⇒ c d) = cong₂ _⇒_ (⇝-unique a c) (⇝-unique b d)
⇝-unique (s-∀ a)   (s-∀ c)   = cong `∀ (⇝-unique a c)

⇝-inj : Φ ⊢ A ⇝ R → Φ ⊢ B ⇝ R → A ≡ B
⇝-inj (s-var x) (s-var y) = cong `_ (∋ⁿ-inj x y)
⇝-inj s-ℕ       s-ℕ       = refl
⇝-inj s-𝔹       s-𝔹       = refl
⇝-inj (s-⇒ a b) (s-⇒ c d) = cong₂ _⇒_ (⇝-inj a c) (⇝-inj b d)
⇝-inj (s-∀ a)   (s-∀ c)   = cong `∀ (⇝-inj a c)

-- a context that names every cell Φ names can name every type Φ can
reread : (∀ {β} → Φ ∋ᶠ β ⦂ true → Φ′ ∋ᶠ β ⦂ true)
  → Φ ⊢ A ⇝ R
  → ∃[ A′ ] Φ′ ⊢ A′ ⇝ R
reread ⊆ (s-var x) = let (X , x′) = flag-named (⊆ (named-flag x))
                     in ` X , s-var x′
reread ⊆ s-ℕ       = `ℕ , s-ℕ
reread ⊆ s-𝔹       = `𝔹 , s-𝔹
reread ⊆ (s-⇒ a b) = let (A′ , a′) = reread ⊆ a
                         (B′ , b′) = reread ⊆ b
                     in A′ ⇒ B′ , s-⇒ a′ b′
reread ⊆ (s-∀ a)   = let (A′ , a′) = reread ⊆′ a in `∀ A′ , s-∀ a′
  where
  ⊆′ : ∀ {β} → (true ∷ _) ∋ᶠ β ⦂ true → (true ∷ _) ∋ᶠ β ⦂ true
  ⊆′ f-here      = f-here
  ⊆′ (f-there f) = f-there (⊆ f)

------------------------------------------------------------------------
-- 4. Spelling after inserting a cell
------------------------------------------------------------------------

-- an unnamed cell at depth k
insᶠ : ℕ → Flags → Flags
insᶠ zero    Φ       = false ∷ Φ
insᶠ (suc k) []      = []
insᶠ (suc k) (b ∷ Φ) = b ∷ insᶠ k Φ

ins-∋ᶠ : ∀ k → Φ ∋ᶠ α ⦂ b → insᶠ k Φ ∋ᶠ extⁿ k suc α ⦂ b
ins-∋ᶠ zero    f           = f-there f
ins-∋ᶠ (suc k) f-here      = f-here
ins-∋ᶠ (suc k) (f-there f) = f-there (ins-∋ᶠ k f)

ins-setFlag : ∀ k α b Φ
  → insᶠ k (setFlag α b Φ) ≡ setFlag (extⁿ k suc α) b (insᶠ k Φ)
ins-setFlag zero    α       b Φ        = refl
ins-setFlag (suc k) α       b []       = refl
ins-setFlag (suc k) zero    b (_ ∷ Φ)  = refl
ins-setFlag (suc k) (suc α) b (b₀ ∷ Φ) = cong (b₀ ∷_) (ins-setFlag k α b Φ)

ins-∋ⁿ : ∀ k → Φ ∋ⁿ X ↦ α → insᶠ k Φ ∋ⁿ X ↦ extⁿ k suc α
ins-∋ⁿ zero    x            = n-hidden x
ins-∋ⁿ (suc k) n-here       = n-here
ins-∋ⁿ (suc k) (n-named x)  = n-named (ins-∋ⁿ k x)
ins-∋ⁿ (suc k) (n-hidden x) = n-hidden (ins-∋ⁿ k x)

ins-⇝ : ∀ k → Φ ⊢ A ⇝ R → insᶠ k Φ ⊢ A ⇝ renameᵗ (extⁿ k suc) R
ins-⇝ k (s-var x) = s-var (ins-∋ⁿ k x)
ins-⇝ k s-ℕ       = s-ℕ
ins-⇝ k s-𝔹       = s-𝔹
ins-⇝ k (s-⇒ a b) = s-⇒ (ins-⇝ k a) (ins-⇝ k b)
ins-⇝ k (s-∀ a)   = s-∀ (ins-⇝ (suc k) a)

-- a named cell under k binders: names and cells both shift
trues : ℕ → Flags → Flags
trues zero    Φ = Φ
trues (suc k) Φ = true ∷ trues k Φ

⇑-∋ⁿ : ∀ k → trues k Φ ∋ⁿ X ↦ α
  → trues k (true ∷ Φ) ∋ⁿ extⁿ k suc X ↦ extⁿ k suc α
⇑-∋ⁿ zero    x           = n-named x
⇑-∋ⁿ (suc k) n-here      = n-here
⇑-∋ⁿ (suc k) (n-named x) = n-named (⇑-∋ⁿ k x)

⇑-⇝ : ∀ k → trues k Φ ⊢ A ⇝ R
  → trues k (true ∷ Φ) ⊢ renameᵗ (extⁿ k suc) A ⇝ renameᵗ (extⁿ k suc) R
⇑-⇝ k (s-var x) = s-var (⇑-∋ⁿ k x)
⇑-⇝ k s-ℕ       = s-ℕ
⇑-⇝ k s-𝔹       = s-𝔹
⇑-⇝ k (s-⇒ a b) = s-⇒ (⇑-⇝ k a) (⇑-⇝ k b)
⇑-⇝ k (s-∀ a)   = s-∀ (⇑-⇝ (suc k) a)
