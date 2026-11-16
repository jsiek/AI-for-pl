module proof.DenotAdequacy where

-- File Charter:
--   * Adequacy of the denotation (Denotation.agda) for reduction, without
--     typing: an element `ret v m` of ⟦ M ⟧ θ₀ ρ₀ (length Σ) comes from a
--     reduction of M from Σ to a value with the observation of v, in a
--     store of length m; `err` comes from a reduction to ℧.
--   * Proved with a logical relation 𝕍 between denotational values and
--     syntactic values, by recursion on the denotational value, and its
--     extension 𝔼 to results, for any store whose length is the starting
--     counter.  Reduction only reads the length of the store.  The
--     fundamental property (fundamental) is stated for the closing
--     instance `subst γ (substᵀ (sealsₙ θ) M)` of an open term; casts
--     (adequacyᶜ) and stacks (adequacyˢ) are handled separately.
--   * Stuck casts denote nothing: a cast at ⇒ is guarded by νλ and one at
--     ∀ by ν∀, and these relate only to function values and to proxies.
--   * Determinism of reduction gives all the values of one group of a
--     bind one common syntactic value (common).
--   * The only syntactic invariant is that the program is Scoped 0
--     (DenotInvariants.agda), so that the closing instance is itself.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _⋵_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
  renaming (subst to substEq)

open import Types
open import Terms
open import Reduction
open import GraphModel
open import Denotation
open import GradualityDefinitions using (observe)
open import DenotInvariants using (Scoped)
open import proof.TypeSubst using (stack-substᵀ)
open import proof.TermSubst
  using (substᵖ-fuse; substˢ-fuse; substᵀ-fuse; subst-id; _•ˢ_; subst-β;
         subst-⇑ˢ-open; subst-exts-⇑ˢ-open)
open import proof.ScopedProps using (closed-substᵀ)
open import proof.Determinism using (value-irreducible; —→-deterministic)

------------------------------------------------------------------------
-- Multi-step reduction
------------------------------------------------------------------------

infixr 2 _++↠_

_++↠_ : ∀ {Σ Σ′ Σ″ L M N}
  → Σ ▷ L —↠ Σ′ ▷ M → Σ′ ▷ M —↠ Σ″ ▷ N → Σ ▷ L —↠ Σ″ ▷ N
(M ∎) ++↠ r = r
(L —→⟨ s ⟩ r₁) ++↠ r₂ = L —→⟨ s ⟩ (r₁ ++↠ r₂)

one : ∀ {Σ Σ′ M N} → Σ ▷ M —→ Σ′ ▷ N → Σ ▷ M —↠ Σ′ ▷ N
one {M = M} {N} s = M —→⟨ s ⟩ (N ∎)

ξ* : ∀ {Σ Σ′ M N} F → Σ ▷ M —↠ Σ′ ▷ N → Σ ▷ plug F M —↠ Σ′ ▷ plug F N
ξ* F (M ∎) = plug F M ∎
ξ* F (M —→⟨ s ⟩ r) = plug F M —→⟨ ξ F s ⟩ ξ* F r

-- evaluation contexts: stacks of frames, outermost first
plug* : List Frame → Term → Term
plug* [] M = M
plug* (F ∷ C) M = plug F (plug* C M)

ξ** : ∀ {Σ Σ′ M N} C → Σ ▷ M —↠ Σ′ ▷ N
  → Σ ▷ plug* C M —↠ Σ′ ▷ plug* C N
ξ** [] r = r
ξ** (F ∷ C) r = ξ* F (ξ** C r)

℧** : ∀ {Σ} C → Σ ▷ plug* C ℧ —↠ Σ ▷ ℧
℧** [] = ℧ ∎
℧** (F ∷ C) = ξ* F (℧** C) ++↠ one (ξ-℧ F)

-- a term reaches at most one value
—↠-value-unique : ∀ {Σ Σ₁ Σ₂ M V₁ V₂}
  → Σ ▷ M —↠ Σ₁ ▷ V₁ → Σ ▷ M —↠ Σ₂ ▷ V₂ → Value V₁ → Value V₂
  → Σ₁ ≡ Σ₂ × V₁ ≡ V₂
—↠-value-unique (M ∎) (M ∎) v₁ v₂ = refl , refl
—↠-value-unique (M ∎) (M —→⟨ s ⟩ r) v₁ v₂ =
  ⊥-elim (value-irreducible v₁ s)
—↠-value-unique (M —→⟨ s ⟩ r) (M ∎) v₁ v₂ =
  ⊥-elim (value-irreducible v₂ s)
—↠-value-unique (M —→⟨ s₁ ⟩ r₁) (M —→⟨ s₂ ⟩ r₂) v₁ v₂
  with —→-deterministic s₁ s₂
—↠-value-unique (M —→⟨ s₁ ⟩ r₁) (M —→⟨ s₂ ⟩ r₂) v₁ v₂ | refl , refl =
  —↠-value-unique r₁ r₂ v₁ v₂

------------------------------------------------------------------------
-- The logical relation
------------------------------------------------------------------------

-- the values that a function entry or νλ describes
FunVal : Term → Set
FunVal V =
  (Σ[ A ∈ Ty ] Σ[ N ∈ Term ] (V ≡ ƛ A N))
  ⊎ (Σ[ d ∈ Dir ] Σ[ p ∈ Prec ] Σ[ q ∈ Prec ] Σ[ W ∈ Term ]
       (V ≡ cast d (p ⇒⊑ q) W × Value W))

mutual
  𝕍 : Val → Term → Set
  𝕍 vtrue V = V ≡ true
  𝕍 vfalse V = V ≡ false
  𝕍 (sealᵛ σ v) V = Σ[ W ∈ Term ] (V ≡ seal (tseal σ) W × 𝕍 v W)
  𝕍 (injᵛ G v) V = Σ[ W ∈ Term ] (V ≡ inj G W × 𝕍 v W)
  𝕍 (U ⟼ r at m) V =
    FunVal V
    × (∀ Σ W → length Σ ≡ m → Value W → 𝕍* U W → 𝔼′ r Σ (V · W))
  𝕍 (σ ⟼∀ r) V =
    Σ[ cs ∈ Stack ] Σ[ N ∈ Term ]
      (V ≡ Λν cs N
       × (∀ Σ → length Σ ≡ suc σ → 𝔼′ r Σ (stack cs N [ tseal σ ]ᵀ)))
  𝕍 νλ V = FunVal V
  𝕍 ν∀ V = Σ[ cs ∈ Stack ] Σ[ N ∈ Term ] (V ≡ Λν cs N)

  𝕍* : List Val → Term → Set
  𝕍* [] W = ⊤
  𝕍* (u ∷ U) W = 𝕍 u W × 𝕍* U W

  -- results, for a run from the store Σ
  𝔼′ : Res → Store → Term → Set
  𝔼′ (ret v m) Σ M =
    Σ[ Σ′ ∈ Store ] Σ[ W ∈ Term ]
      ((Σ ▷ M —↠ Σ′ ▷ W) × Value W × length Σ′ ≡ m × 𝕍 v W)
  𝔼′ err Σ M = Σ[ Σ′ ∈ Store ] (Σ ▷ M —↠ Σ′ ▷ ℧)

-- 𝔼′ wrapped in a record, so that Agda can infer r, Σ and M
record 𝔼 (r : Res) (Σ : Store) (M : Term) : Set where
  constructor ⟨_⟩
  field 𝔼-out : 𝔼′ r Σ M
open 𝔼 public

-- the relation on environments and closing substitutions
𝔾 : Env → Subst → Set
𝔾 ρ γ = ∀ x v → v ∈ ρ x → 𝕍 v (γ x)

------------------------------------------------------------------------
-- Properties of the relation
------------------------------------------------------------------------

FunVal→Value : ∀ {V} → FunVal V → Value V
FunVal→Value (inj₁ (A , N , refl)) = V-ƛ
FunVal→Value (inj₂ (d , p , q , W , refl , w)) = V-cast⇒ w

𝕍→Value : ∀ v {V} → 𝕍 v V → Value V
𝕍→Value vtrue refl = V-true
𝕍→Value vfalse refl = V-false
𝕍→Value (sealᵛ σ v) (W , refl , rel) = V-seal (𝕍→Value v rel)
𝕍→Value (injᵛ G v) (W , refl , rel) = V-inj (𝕍→Value v rel)
𝕍→Value (U ⟼ r at m) (fv , app) = FunVal→Value fv
𝕍→Value (σ ⟼∀ r) (cs , N , refl , body) = V-Λν
𝕍→Value νλ fv = FunVal→Value fv
𝕍→Value ν∀ (cs , N , refl) = V-Λν

𝕍→𝔼 : ∀ v V {Σ m} → 𝕍 v V → length Σ ≡ m → 𝔼 (ret v m) Σ V
𝕍→𝔼 v V {Σ} rel len = ⟨ Σ , V , (V ∎) , 𝕍→Value v rel , len , rel ⟩

𝔼-expand : ∀ {r Σ Σ₁ M M′} → Σ ▷ M —↠ Σ₁ ▷ M′ → 𝔼 r Σ₁ M′ → 𝔼 r Σ M
𝔼-expand {ret v m} M↠ ⟨ Σ′ , W , M′↠W , w , len , rel ⟩ =
  ⟨ Σ′ , W , (M↠ ++↠ M′↠W) , w , len , rel ⟩
𝔼-expand {err} M↠ ⟨ Σ′ , M′↠℧ ⟩ = ⟨ Σ′ , (M↠ ++↠ M′↠℧) ⟩

𝔼-≡ : ∀ {r Σ M M′} → M ≡ M′ → 𝔼 r Σ M′ → 𝔼 r Σ M
𝔼-≡ refl e = e

𝕍*-∋ : ∀ {U W u} → 𝕍* U W → u ⋵ U → 𝕍 u W
𝕍*-∋ (rel , rels) (here refl) = rel
𝕍*-∋ (rel , rels) (there u∈) = 𝕍*-∋ rels u∈

𝕍*-from : ∀ U {W} → (∀ u → u ⋵ U → 𝕍 u W) → 𝕍* U W
𝕍*-from [] h = tt
𝕍*-from (u ∷ U) h =
  h u (here refl) , 𝕍*-from U (λ u′ u′∈ → h u′ (there u′∈))

obs-𝕍 : ∀ v {V} → 𝕍 v V → (vV : Value V) → obs v ≡ observe vV
obs-𝕍 vtrue refl V-true = refl
obs-𝕍 vfalse refl V-false = refl
obs-𝕍 (sealᵛ σ v) (W , refl , rel) (V-seal w) = obs-𝕍 v rel w
obs-𝕍 (injᵛ G v) (W , refl , rel) (V-inj w) = obs-𝕍 v rel w
obs-𝕍 (U ⟼ r at m) (inj₁ (A , N , refl) , app) V-ƛ = refl
obs-𝕍 (U ⟼ r at m) (inj₂ (d , p , q , W , refl , w) , app) (V-cast⇒ w′) =
  refl
obs-𝕍 (σ ⟼∀ r) (cs , N , refl , body) V-Λν = refl
obs-𝕍 νλ (inj₁ (A , N , refl)) V-ƛ = refl
obs-𝕍 νλ (inj₂ (d , p , q , W , refl , w)) (V-cast⇒ w′) = refl
obs-𝕍 ν∀ (cs , N , refl) V-Λν = refl

------------------------------------------------------------------------
-- Binds
------------------------------------------------------------------------

-- all the values of one group are related to one syntactic value
common : ∀ {R Σ M m v₀}
  → (∀ r → r ∈ᴿ R → 𝔼 r Σ M)
  → ret v₀ m ∈ᴿ R
  → Σ[ Σ′ ∈ Store ] Σ[ W ∈ Term ]
      ((Σ ▷ M —↠ Σ′ ▷ W) × Value W × length Σ′ ≡ m
       × (∀ v → v ∈ ⌊ R ⌋ m → 𝕍 v W))
common {R} {m = m} {v₀} h v₀∈ with h (ret v₀ m) v₀∈
common {R} {m = m} {v₀} h v₀∈ | ⟨ Σ₀ , W₀ , M↠W₀ , w₀ , len₀ , rel₀ ⟩ =
  Σ₀ , W₀ , M↠W₀ , w₀ , len₀ , all
  where
  all : ∀ v → v ∈ ⌊ R ⌋ m → 𝕍 v W₀
  all v v∈ with h (ret v m) v∈
  all v v∈ | ⟨ Σ₁ , W₁ , M↠W₁ , w₁ , len₁ , rel₁ ⟩
    with —↠-value-unique M↠W₀ M↠W₁ w₀ w₁
  all v v∈ | ⟨ Σ₁ , W₁ , M↠W₁ , w₁ , len₁ , rel₁ ⟩ | refl , refl = rel₁

-- a bind evaluates its left side in a context, then continues with the
-- common value of each group
bind-𝔼 : ∀ C {R K Σ M}
  → (∀ r → r ∈ᴿ R → 𝔼 r Σ M)
  → (∀ m D Σ′ W → length Σ′ ≡ m → Value W → (∀ v → v ∈ D → 𝕍 v W)
       → ∀ r → r ∈ᴿ K D m → 𝔼 r Σ′ (plug* C W))
  → ∀ r → r ∈ᴿ (R ≫= K) → 𝔼 r Σ (plug* C M)
bind-𝔼 C h k r (inj₁ (refl , e∈)) with h err e∈
bind-𝔼 C h k r (inj₁ (refl , e∈)) | ⟨ Σ′ , M↠℧ ⟩ =
  ⟨ Σ′ , (ξ** C M↠℧ ++↠ ℧** C) ⟩
bind-𝔼 C {R} h k r (inj₂ (m , (v₀ , v₀∈) , r∈)) with common h v₀∈
bind-𝔼 C {R} h k r (inj₂ (m , (v₀ , v₀∈) , r∈))
  | Σ₁ , W , M↠W , w , len , all =
  𝔼-expand (ξ** C M↠W) (k m (⌊ R ⌋ m) Σ₁ W len w all r r∈)

------------------------------------------------------------------------
-- Closing instances
------------------------------------------------------------------------

-- the name substitution that closes a term under a seal environment
sealsₙ : SEnv → NSubst
sealsₙ θ i = tseal (θ i)

seals-name : ∀ θ α → substₙ (sealsₙ θ) α ≡ tseal (⟦ α ⟧ₙ θ)
seals-name θ (tvar i) = refl
seals-name θ (tseal s) = refl

seals-ground : ∀ θ G → substG (sealsₙ θ) G ≡ ⟦ G ⟧ᴳ θ
seals-ground θ (G‵ α) = cong G‵ (seals-name θ α)
seals-ground θ G𝔹 = refl
seals-ground θ G⇒ = refl
seals-ground θ G∀ = refl

seals-open : ∀ θ σ i
  → substₙ (singleₙ (tseal σ)) (extₙ (sealsₙ θ) i) ≡ sealsₙ (σ •ᵗ θ) i
seals-open θ σ zero = refl
seals-open θ σ (suc i) = refl

-- steps at closed names and grounds
unseal-step : ∀ {Σ α σ W} → α ≡ tseal σ → Value W
  → Σ ▷ unseal α (seal (tseal σ) W) —→ Σ ▷ W
unseal-step refl w = β-unseal w

is-yes-step : ∀ {Σ G G₀ W} → G ≡ G₀ → Value W
  → Σ ▷ is G (inj G₀ W) —→ Σ ▷ true
is-yes-step refl w = β-is-yes w

tag-down-step : ∀ {Σ G G₀ p W} → G ≡ G₀ → Value W
  → Σ ▷ cast down (tag G p) (inj G₀ W) —→ Σ ▷ cast down p W
tag-down-step refl w = β-tag-down w

------------------------------------------------------------------------
-- Inversions of the operators
------------------------------------------------------------------------

seal-inv : ∀ {σ D} w → w ∈ sealᴾ σ D → Σ[ u ∈ Val ] (w ≡ sealᵛ σ u × u ∈ D)
seal-inv (sealᵛ σ′ u) (refl , u∈) = u , refl , u∈
seal-inv vtrue ()
seal-inv vfalse ()
seal-inv (injᵛ G u) ()
seal-inv (U ⟼ r at m) ()
seal-inv (σ′ ⟼∀ r) ()
seal-inv νλ ()
seal-inv ν∀ ()

inj-inv : ∀ {G D} w → w ∈ injᴾ G D → Σ[ u ∈ Val ] (w ≡ injᵛ G u × u ∈ D)
inj-inv (injᵛ H u) (refl , u∈) = u , refl , u∈
inj-inv vtrue ()
inj-inv vfalse ()
inj-inv (sealᵛ σ u) ()
inj-inv (U ⟼ r at m) ()
inj-inv (σ ⟼∀ r) ()
inj-inv νλ ()
inj-inv ν∀ ()

test-inv : ∀ {G D} w → w ∈ testᴾ G D
  → (w ≡ vtrue × Σ[ u ∈ Val ] (injᵛ G u ∈ D))
    ⊎ (w ≡ vfalse × Σ[ H ∈ Ground ] Σ[ u ∈ Val ] (injᵛ H u ∈ D × H ≢ G))
test-inv vtrue t = inj₁ (refl , t)
test-inv vfalse t = inj₂ (refl , t)
test-inv (sealᵛ σ u) ()
test-inv (injᵛ H u) ()
test-inv (U ⟼ r at m) ()
test-inv (σ ⟼∀ r) ()
test-inv νλ ()
test-inv ν∀ ()

Λ-inv : ∀ {F} w → w ∈ Λ F
  → w ≡ νλ
    ⊎ (Σ[ U ∈ List Val ] Σ[ r ∈ Res ] Σ[ m ∈ ℕ ]
         (w ≡ (U ⟼ r at m) × r ∈ᴿ F (mem U) m))
Λ-inv (U ⟼ r at m) (r∈ , ne , c) = inj₂ (U , r , m , refl , r∈)
Λ-inv νλ tt = inj₁ refl
Λ-inv vtrue ()
Λ-inv vfalse ()
Λ-inv (sealᵛ σ u) ()
Λ-inv (injᵛ G u) ()
Λ-inv (σ ⟼∀ r) ()
Λ-inv ν∀ ()

Λᴾ-inv : ∀ {F} w → w ∈ Λᴾ F
  → w ≡ ν∀ ⊎ (Σ[ σ ∈ Seal ] Σ[ r ∈ Res ] (w ≡ (σ ⟼∀ r) × r ∈ᴿ F σ))
Λᴾ-inv (σ ⟼∀ r) r∈ = inj₂ (σ , r , refl , r∈)
Λᴾ-inv ν∀ tt = inj₁ refl
Λᴾ-inv vtrue ()
Λᴾ-inv vfalse ()
Λᴾ-inv (sealᵛ σ u) ()
Λᴾ-inv (injᵛ G u) ()
Λᴾ-inv (U ⟼ r at m) ()
Λᴾ-inv νλ ()

-- an entry of D instantiated at σ, from a result of a bind on D ◆ σ
◆-entry : ∀ {D σ K r} → r ∈ᴿ ((D ◆ σ) ≫= K) → Σ[ r′ ∈ Res ] ((σ ⟼∀ r′) ∈ D)
◆-entry (inj₁ (eq , e∈)) = err , e∈
◆-entry (inj₂ (m , (v , v∈) , r∈)) = ret v m , v∈

------------------------------------------------------------------------
-- Casts and stacks
------------------------------------------------------------------------

adequacyᶜ : ∀ d p θ {E m Σ W} → length Σ ≡ m → Value W
  → (∀ v → v ∈ E → 𝕍 v W)
  → ∀ r → r ∈ᴿ ⟦ d , p ⟧ᶜ θ E m → 𝔼 r Σ (cast d (substᵖ (sealsₙ θ) p) W)
adequacyᶜ d ★⊑ θ {W = W} len w h (ret v m′) (eq , v∈) =
  𝔼-expand (one (β-id at★ w)) (𝕍→𝔼 v W (h v v∈) (trans len (sym eq)))
adequacyᶜ d 𝔹⊑ θ {W = W} len w h (ret v m′) (eq , v∈) =
  𝔼-expand (one (β-id at𝔹 w)) (𝕍→𝔼 v W (h v v∈) (trans len (sym eq)))
adequacyᶜ d (‵⊑ α) θ {W = W} len w h (ret v m′) (eq , v∈) =
  𝔼-expand (one (β-id at‵ w)) (𝕍→𝔼 v W (h v v∈) (trans len (sym eq)))
adequacyᶜ d (p ⇒⊑ q) θ {E} {W = W} len w h (ret u m′) (νλ∈ , eq , u∈)
  with Λ-inv u u∈
adequacyᶜ d (p ⇒⊑ q) θ {E} {W = W} len w h (ret u m′) (νλ∈ , eq , u∈)
  | inj₁ refl =
  𝕍→𝔼 νλ (cast d (p′ ⇒⊑ q′) W) (inj₂ (d , p′ , q′ , W , refl , w))
    (trans len (sym eq))
  where
  p′ = substᵖ (sealsₙ θ) p
  q′ = substᵖ (sealsₙ θ) q
adequacyᶜ d (p ⇒⊑ q) θ {E} {W = W} len w h (ret u m′) (νλ∈ , eq , u∈)
  | inj₂ (U , r , m″ , refl , r∈) =
  𝕍→𝔼 (U ⟼ r at m″) (cast d (p′ ⇒⊑ q′) W)
    (inj₂ (d , p′ , q′ , W , refl , w) , app) (trans len (sym eq))
  where
  p′ = substᵖ (sealsₙ θ) p
  q′ = substᵖ (sealsₙ θ) q
  app : ∀ Σ′ W′ → length Σ′ ≡ m″ → Value W′ → 𝕍* U W′
    → 𝔼′ r Σ′ (cast d (p′ ⇒⊑ q′) W · W′)
  app Σ′ W′ len′ w′ relU = 𝔼-out (
    𝔼-expand (one (β-cast⇒ w w′))
      (bind-𝔼 (cast□ d q′ ∷ app□ W w ∷ [])
        (adequacyᶜ (flip d) p θ len′ w′ (λ v v∈ → 𝕍*-∋ relU v∈)) k₁ r r∈))
    where
    k₁ : ∀ m₁ D₁ Σ₁ W₁ → length Σ₁ ≡ m₁ → Value W₁
      → (∀ v → v ∈ D₁ → 𝕍 v W₁)
      → ∀ r′ → r′ ∈ᴿ ((E ●[ m₁ ] D₁) ≫= ⟦ d , q ⟧ᶜ θ)
      → 𝔼 r′ Σ₁ (cast d q′ (W · W₁))
    k₁ m₁ D₁ Σ₁ W₁ len₁ w₁ all₁ r′ r′∈ =
      bind-𝔼 (cast□ d q′ ∷ []) applied
        (λ m₂ D₂ Σ₂ W₂ len₂ w₂ all₂ → adequacyᶜ d q θ len₂ w₂ all₂) r′ r′∈
      where
      applied : ∀ r″ → r″ ∈ᴿ (E ●[ m₁ ] D₁) → 𝔼 r″ Σ₁ (W · W₁)
      applied r″ (U′ , e∈ , U′⊆ , ne) =
        ⟨ proj₂ (h _ e∈) Σ₁ W₁ len₁ w₁
            (𝕍*-from U′ (λ u′ u′∈ → all₁ u′ (U′⊆ u′ u′∈))) ⟩
adequacyᶜ d (∀⊑ p) θ {E} len w h (ret u m′) (ν∀∈ , eq , u∈)
  with h ν∀ ν∀∈
adequacyᶜ d (∀⊑ p) θ {E} len w h (ret u m′) (ν∀∈ , eq , u∈)
  | cs , P , refl =
  𝔼-expand (one β-cast∀)
    (𝕍→𝔼 u (Λν ((d , p″) ∷ cs) P) (rel u u∈) (trans len (sym eq)))
  where
  p″ = substᵖ (extₙ (sealsₙ θ)) p
  rel : ∀ u → u ∈ Λᴾ (λ σ → (E ◆ σ) ≫= ⟦ d , p ⟧ᶜ (σ •ᵗ θ))
    → 𝕍 u (Λν ((d , p″) ∷ cs) P)
  rel u u∈ with Λᴾ-inv u u∈
  rel u u∈ | inj₁ refl = (d , p″) ∷ cs , P , refl
  rel u u∈ | inj₂ (σ , r , refl , r∈) =
    (d , p″) ∷ cs , P , refl , body
    where
    p-eq : substᵖ (singleₙ (tseal σ)) p″ ≡ substᵖ (sealsₙ (σ •ᵗ θ)) p
    p-eq = substᵖ-fuse (seals-open θ σ) p
    body : ∀ Σ′ → length Σ′ ≡ suc σ
      → 𝔼′ r Σ′ (stack ((d , p″) ∷ cs) P [ tseal σ ]ᵀ)
    body Σ′ len′ = 𝔼-out (
      𝔼-≡ (cong (λ p₁ → cast d p₁ (stack cs P [ tseal σ ]ᵀ)) p-eq)
        (bind-𝔼 (cast□ d (substᵖ (sealsₙ (σ •ᵗ θ)) p) ∷ []) inner
          (λ m₂ D₂ Σ₂ W₂ len₂ w₂ all₂ →
            adequacyᶜ d p (σ •ᵗ θ) len₂ w₂ all₂) r r∈))
      where
      inner : ∀ r′ → r′ ∈ᴿ (E ◆ σ) → 𝔼 r′ Σ′ (stack cs P [ tseal σ ]ᵀ)
      inner r′ r′∈ with h (σ ⟼∀ r′) r′∈
      inner r′ r′∈ | cs₂ , P₂ , refl , body₂ = ⟨ body₂ Σ′ len′ ⟩
adequacyᶜ up (tag G p) θ {W = W} len w h r r∈ =
  𝔼-expand (one (β-tag-up w))
    (bind-𝔼 (inj□ G′ ∷ []) (adequacyᶜ up p θ len w h) k r r∈)
  where
  G′ = substG (sealsₙ θ) G
  k : ∀ m₁ D₁ Σ₁ W₁ → length Σ₁ ≡ m₁ → Value W₁
    → (∀ v → v ∈ D₁ → 𝕍 v W₁)
    → ∀ r′ → r′ ∈ᴿ retᴿ (injᴾ (⟦ G ⟧ᴳ θ) D₁) m₁ → 𝔼 r′ Σ₁ (inj G′ W₁)
  k m₁ D₁ Σ₁ W₁ len₁ w₁ all₁ (ret v m₂) (eq , v∈) with inj-inv v v∈
  k m₁ D₁ Σ₁ W₁ len₁ w₁ all₁ (ret v m₂) (eq , v∈)
    | u , refl , u∈ =
    𝕍→𝔼 (injᵛ (⟦ G ⟧ᴳ θ) u) (inj G′ W₁)
      (W₁ , cong (λ H → inj H W₁) (seals-ground θ G) , all₁ u u∈)
      (trans len₁ (sym eq))
adequacyᶜ down (tag G p) θ len w h err (inj₁ (refl , H , u , u∈ , H≢G))
  with h (injᵛ H u) u∈
adequacyᶜ down (tag G p) θ {Σ = Σ} len w h err
    (inj₁ (refl , H , u , u∈ , H≢G))
  | W′ , refl , rel =
  ⟨ Σ , one (β-tag-down-℧ (𝕍→Value u rel) G′≢H) ⟩
  where
  G′≢H : substG (sealsₙ θ) G ≢ H
  G′≢H e = H≢G (trans (sym e) (seals-ground θ G))
adequacyᶜ down (tag G p) θ {E} {m} len w h r
    (inj₂ (m₁ , (u₀ , e₁ , u₀∈) , r∈))
  with h (injᵛ (⟦ G ⟧ᴳ θ) u₀) u₀∈
adequacyᶜ down (tag G p) θ {E} {m} len w h r
    (inj₂ (m₁ , (u₀ , e₁ , u₀∈) , r∈))
  | W′ , refl , rel₀ =
  𝔼-expand (one (tag-down-step (seals-ground θ G) w′))
    (adequacyᶜ down p θ (trans len (sym e₁)) w′ h′ r r∈)
  where
  w′ = 𝕍→Value u₀ rel₀
  h′ : ∀ v → v ∈ ⌊ proj (⟦ G ⟧ᴳ θ) E m ⌋ m₁ → 𝕍 v W′
  h′ v (e , v∈) with h (injᵛ (⟦ G ⟧ᴳ θ) v) v∈
  h′ v (e , v∈) | W″ , refl , rel = rel

adequacyˢ : ∀ cs θ {R Σ M}
  → (∀ r → r ∈ᴿ R → 𝔼 r Σ M)
  → ∀ r → r ∈ᴿ ⟦ cs ⟧ˢ θ R → 𝔼 r Σ (stack (substˢ (sealsₙ θ) cs) M)
adequacyˢ [] θ h = h
adequacyˢ ((d , p) ∷ cs) θ h =
  bind-𝔼 (cast□ d (substᵖ (sealsₙ θ) p) ∷ []) (adequacyˢ cs θ h)
    (λ m D Σ′ W len w all → adequacyᶜ d p θ len w all)

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

length-snoc : ∀ (Σ : Store) B → length (Σ ++ (B ∷ [])) ≡ suc (length Σ)
length-snoc [] B = refl
length-snoc (A ∷ Σ) B = cong suc (length-snoc Σ B)

ext-𝔾 : ∀ {ρ γ D W} → 𝔾 ρ γ → (∀ v → v ∈ D → 𝕍 v W)
  → 𝔾 (D • ρ) (W •ˢ γ)
ext-𝔾 g all zero = all
ext-𝔾 g all (suc x) = g x

fundamental : ∀ M θ {ρ γ n Σ} → 𝔾 ρ γ → length Σ ≡ n
  → ∀ r → r ∈ᴿ ⟦ M ⟧ θ ρ n → 𝔼 r Σ (subst γ (substᵀ (sealsₙ θ) M))
fundamental (` x) θ {γ = γ} g len (ret v m) (eq , v∈) =
  𝕍→𝔼 v (γ x) (g x v v∈) (trans len (sym eq))
fundamental ℧ θ {Σ = Σ} g len err tt = ⟨ Σ , (℧ ∎) ⟩
fundamental true θ g len (ret v m) (eq , refl) =
  𝕍→𝔼 vtrue true refl (trans len (sym eq))
fundamental false θ g len (ret v m) (eq , refl) =
  𝕍→𝔼 vfalse false refl (trans len (sym eq))
fundamental (if L M N) θ {ρ} {γ} g len =
  bind-𝔼 (if□ M′ N′ ∷ []) (fundamental L θ g len) k
  where
  M′ = subst γ (substᵀ (sealsₙ θ) M)
  N′ = subst γ (substᵀ (sealsₙ θ) N)
  k : ∀ m D Σ′ W → length Σ′ ≡ m → Value W → (∀ v → v ∈ D → 𝕍 v W)
    → ∀ r → r ∈ᴿ condᴿ D (⟦ M ⟧ θ ρ m) (⟦ N ⟧ θ ρ m)
    → 𝔼 r Σ′ (if W M′ N′)
  k m D Σ′ W len′ w all r (inj₁ (t∈ , r∈)) with all vtrue t∈
  k m D Σ′ W len′ w all r (inj₁ (t∈ , r∈)) | refl =
    𝔼-expand (one β-if-true) (fundamental M θ g len′ r r∈)
  k m D Σ′ W len′ w all r (inj₂ (f∈ , r∈)) with all vfalse f∈
  k m D Σ′ W len′ w all r (inj₂ (f∈ , r∈)) | refl =
    𝔼-expand (one β-if-false) (fundamental N θ g len′ r r∈)
fundamental (ƛ A M) θ {ρ} {γ} g len (ret w m) (eq , w∈) =
  𝕍→𝔼 w (ƛ A′ Mb) (rel w w∈) (trans len (sym eq))
  where
  A′ = substᵗ (sealsₙ θ) A
  Mθ = substᵀ (sealsₙ θ) M
  Mb = subst (exts γ) Mθ
  rel : ∀ w → w ∈ Λ (λ E m → ⟦ M ⟧ θ (E • ρ) m) → 𝕍 w (ƛ A′ Mb)
  rel w w∈ with Λ-inv w w∈
  rel w w∈ | inj₁ refl = inj₁ (A′ , Mb , refl)
  rel w w∈ | inj₂ (U , r , m′ , refl , r∈) = inj₁ (A′ , Mb , refl) , app
    where
    app : ∀ Σ′ W → length Σ′ ≡ m′ → Value W → 𝕍* U W
      → 𝔼′ r Σ′ (ƛ A′ Mb · W)
    app Σ′ W len′ w′ relU =
      𝔼-out (𝔼-expand (one (β-ƛ w′))
        (𝔼-≡ (subst-β γ W Mθ)
          (fundamental M θ (ext-𝔾 g (λ v v∈ → 𝕍*-∋ relU v∈)) len′ r r∈)))
fundamental (L · M) θ {ρ} {γ} g len =
  bind-𝔼 (□· M′ ∷ []) (fundamental L θ g len) k₁
  where
  M′ = subst γ (substᵀ (sealsₙ θ) M)
  k₁ : ∀ n₁ D Σ₁ W → length Σ₁ ≡ n₁ → Value W → (∀ v → v ∈ D → 𝕍 v W)
    → ∀ r → r ∈ᴿ (⟦ M ⟧ θ ρ n₁ ≫= λ E n₂ → D ●[ n₂ ] E)
    → 𝔼 r Σ₁ (W · M′)
  k₁ n₁ D Σ₁ W len₁ w all r r∈ =
    bind-𝔼 (app□ W w ∷ []) (fundamental M θ g len₁) k₂ r r∈
    where
    k₂ : ∀ n₂ E Σ₂ W′ → length Σ₂ ≡ n₂ → Value W′
      → (∀ v → v ∈ E → 𝕍 v W′)
      → ∀ r′ → r′ ∈ᴿ (D ●[ n₂ ] E) → 𝔼 r′ Σ₂ (W · W′)
    k₂ n₂ E Σ₂ W′ len₂ w′ all′ r′ (U , e∈ , U⊆ , ne) =
      ⟨ proj₂ (all _ e∈) Σ₂ W′ len₂ w′
          (𝕍*-from U (λ u u∈ → all′ u (U⊆ u u∈))) ⟩
fundamental (letv M N) θ {ρ} {γ} g len =
  bind-𝔼 (letv□ N′ ∷ []) (fundamental M θ g len) k
  where
  Nθ = substᵀ (sealsₙ θ) N
  N′ = subst (exts γ) Nθ
  k : ∀ m D Σ′ W → length Σ′ ≡ m → Value W → (∀ v → v ∈ D → 𝕍 v W)
    → ∀ r → r ∈ᴿ ⟦ N ⟧ θ (D • ρ) m → 𝔼 r Σ′ (letv W N′)
  k m D Σ′ W len′ w all r r∈ =
    𝔼-expand (one (β-letv w))
      (𝔼-≡ (subst-β γ W Nθ) (fundamental N θ (ext-𝔾 g all) len′ r r∈))
fundamental (seal α M) θ {ρ} {γ} g len =
  bind-𝔼 (seal□ α′ ∷ []) (fundamental M θ g len) k
  where
  α′ = substₙ (sealsₙ θ) α
  σ = ⟦ α ⟧ₙ θ
  k : ∀ m D Σ′ W → length Σ′ ≡ m → Value W → (∀ v → v ∈ D → 𝕍 v W)
    → ∀ r → r ∈ᴿ retᴿ (sealᴾ σ D) m → 𝔼 r Σ′ (seal α′ W)
  k m D Σ′ W len′ w all (ret v m′) (eq , v∈) with seal-inv v v∈
  k m D Σ′ W len′ w all (ret v m′) (eq , v∈) | u , refl , u∈ =
    𝕍→𝔼 (sealᵛ σ u) (seal α′ W)
      (W , cong (λ a → seal a W) (seals-name θ α) , all u u∈)
      (trans len′ (sym eq))
fundamental (unseal α M) θ {ρ} {γ} g len =
  bind-𝔼 (unseal□ α′ ∷ []) (fundamental M θ g len) k
  where
  α′ = substₙ (sealsₙ θ) α
  σ = ⟦ α ⟧ₙ θ
  k : ∀ m D Σ′ W → length Σ′ ≡ m → Value W → (∀ v → v ∈ D → 𝕍 v W)
    → ∀ r → r ∈ᴿ retᴿ (unsealᴾ σ D) m → 𝔼 r Σ′ (unseal α′ W)
  k m D Σ′ W len′ w all (ret v m′) (eq , sv∈) with all (sealᵛ σ v) sv∈
  k m D Σ′ W len′ w all (ret v m′) (eq , sv∈) | W′ , refl , rel =
    𝔼-expand (one (unseal-step (seals-name θ α) (𝕍→Value v rel)))
      (𝕍→𝔼 v W′ rel (trans len′ (sym eq)))
fundamental (is G M) θ {ρ} {γ} g len =
  bind-𝔼 (is□ G′ ∷ []) (fundamental M θ g len) k
  where
  G′ = substG (sealsₙ θ) G
  G₀ = ⟦ G ⟧ᴳ θ
  yes : ∀ {Σ′ W m′ u} → length Σ′ ≡ m′ → 𝕍 (injᵛ G₀ u) W
    → 𝔼 (ret vtrue m′) Σ′ (is G′ W)
  yes {u = u} len′ (W′ , refl , rel) =
    𝔼-expand (one (is-yes-step (seals-ground θ G) (𝕍→Value u rel)))
      (𝕍→𝔼 vtrue true refl len′)
  no : ∀ {Σ′ W m′ H u} → length Σ′ ≡ m′ → H ≢ G₀ → 𝕍 (injᵛ H u) W
    → 𝔼 (ret vfalse m′) Σ′ (is G′ W)
  no {u = u} len′ H≢G (W′ , refl , rel) =
    𝔼-expand (one (β-is-no (𝕍→Value u rel)
                     (λ e → H≢G (trans (sym e) (seals-ground θ G)))))
      (𝕍→𝔼 vfalse false refl len′)
  k : ∀ m D Σ′ W → length Σ′ ≡ m → Value W → (∀ v → v ∈ D → 𝕍 v W)
    → ∀ r → r ∈ᴿ retᴿ (testᴾ G₀ D) m → 𝔼 r Σ′ (is G′ W)
  k m D Σ′ W len′ w all (ret v m′) (eq , v∈) with test-inv v v∈
  k m D Σ′ W len′ w all (ret v m′) (eq , v∈)
    | inj₁ (refl , u , iu∈) = yes (trans len′ (sym eq)) (all _ iu∈)
  k m D Σ′ W len′ w all (ret v m′) (eq , v∈)
    | inj₂ (refl , H , u , iu∈ , H≢G) =
    no (trans len′ (sym eq)) H≢G (all _ iu∈)
fundamental (inj G M) θ {ρ} {γ} g len =
  bind-𝔼 (inj□ G′ ∷ []) (fundamental M θ g len) k
  where
  G′ = substG (sealsₙ θ) G
  G₀ = ⟦ G ⟧ᴳ θ
  k : ∀ m D Σ′ W → length Σ′ ≡ m → Value W → (∀ v → v ∈ D → 𝕍 v W)
    → ∀ r → r ∈ᴿ retᴿ (injᴾ G₀ D) m → 𝔼 r Σ′ (inj G′ W)
  k m D Σ′ W len′ w all (ret v m′) (eq , v∈) with inj-inv v v∈
  k m D Σ′ W len′ w all (ret v m′) (eq , v∈) | u , refl , u∈ =
    𝕍→𝔼 (injᵛ G₀ u) (inj G′ W)
      (W , cong (λ H → inj H W) (seals-ground θ G) , all u u∈)
      (trans len′ (sym eq))
fundamental (cast d p M) θ g len =
  bind-𝔼 (cast□ d (substᵖ (sealsₙ θ) p) ∷ []) (fundamental M θ g len)
    (λ m D Σ′ W len′ w all → adequacyᶜ d p θ len′ w all)
fundamental (Λν cs M) θ {ρ} {γ} g len (ret w m) (eq , w∈) =
  𝕍→𝔼 w (Λν cs′ P) (rel w w∈) (trans len (sym eq))
  where
  cs′ = substˢ (extₙ (sealsₙ θ)) cs
  P = subst (⇑ˢ γ) (substᵀ (extₙ (sealsₙ θ)) M)
  eqT : ∀ σ → stack cs′ P [ tseal σ ]ᵀ
    ≡ stack (substˢ (sealsₙ (σ •ᵗ θ)) cs)
            (subst γ (substᵀ (sealsₙ (σ •ᵗ θ)) M))
  eqT σ =
    trans (stack-substᵀ (singleₙ (tseal σ)) cs′ P)
      (cong₂ stack (substˢ-fuse (seals-open θ σ) cs)
        (trans (subst-⇑ˢ-open γ (substᵀ (extₙ (sealsₙ θ)) M) (tseal σ))
               (cong (subst γ) (substᵀ-fuse (seals-open θ σ) M))))
  rel : ∀ w
    → w ∈ Λᴾ (λ σ → ⟦ cs ⟧ˢ (σ •ᵗ θ) (⟦ M ⟧ (σ •ᵗ θ) ρ (suc σ)))
    → 𝕍 w (Λν cs′ P)
  rel w w∈ with Λᴾ-inv w w∈
  rel w w∈ | inj₁ refl = cs′ , P , refl
  rel w w∈ | inj₂ (σ , r , refl , r∈) = cs′ , P , refl , body
    where
    body : ∀ Σ′ → length Σ′ ≡ suc σ → 𝔼′ r Σ′ (stack cs′ P [ tseal σ ]ᵀ)
    body Σ′ len′ =
      𝔼-out (𝔼-≡ (eqT σ)
        (adequacyˢ cs (σ •ᵗ θ) (fundamental M (σ •ᵗ θ) g len′) r r∈))
fundamental (inst M B N) θ {ρ} {γ} g len =
  bind-𝔼 (inst□ B′ N′ ∷ []) (fundamental M θ g len) k
  where
  B′ = substᵗ (sealsₙ θ) B
  Nθ = substᵀ (extₙ (sealsₙ θ)) N
  N′ = subst (exts (⇑ˢ γ)) Nθ
  eqN : ∀ n₁ W → (N′ [ tseal n₁ ]ᵀ) [ W ]
    ≡ subst (W •ˢ γ) (substᵀ (sealsₙ (n₁ •ᵗ θ)) N)
  eqN n₁ W =
    trans (cong (_[ W ])
            (trans (subst-exts-⇑ˢ-open γ Nθ (tseal n₁))
                   (cong (subst (exts γ)) (substᵀ-fuse (seals-open θ n₁) N))))
          (subst-β γ W (substᵀ (sealsₙ (n₁ •ᵗ θ)) N))
  k : ∀ m D Σ₁ W → length Σ₁ ≡ m → Value W → (∀ v → v ∈ D → 𝕍 v W)
    → ∀ r → r ∈ᴿ ((D ◆ m) ≫= λ E n₂ → ⟦ N ⟧ (m •ᵗ θ) (E • ρ) n₂)
    → 𝔼 r Σ₁ (inst W B′ N′)
  k _ D Σ₁ W refl w all r r∈
    with ◆-entry {D = D} {σ = length Σ₁}
           {K = λ E n₂ → ⟦ N ⟧ (length Σ₁ •ᵗ θ) (E • ρ) n₂} r∈
  k _ D Σ₁ W refl w all r r∈ | r₀ , e∈ with all (length Σ₁ ⟼∀ r₀) e∈
  k _ D Σ₁ W refl w all r r∈ | r₀ , e∈ | cs , P , refl , body₀ =
    𝔼-expand (one β-inst)
      (bind-𝔼 (letv□ (N′ [ tseal n₁ ]ᵀ) ∷ []) inner k₂ r r∈)
    where
    n₁ = length Σ₁
    inner : ∀ r′ → r′ ∈ᴿ (D ◆ n₁)
      → 𝔼 r′ (Σ₁ ++ (B′ ∷ [])) (stack cs P [ tseal n₁ ]ᵀ)
    inner r′ r′∈ with all (n₁ ⟼∀ r′) r′∈
    inner r′ r′∈ | cs₂ , P₂ , refl , body₂ =
      ⟨ body₂ (Σ₁ ++ (B′ ∷ [])) (length-snoc Σ₁ B′) ⟩
    k₂ : ∀ n₂ E Σ₃ W′ → length Σ₃ ≡ n₂ → Value W′
      → (∀ v → v ∈ E → 𝕍 v W′)
      → ∀ r′ → r′ ∈ᴿ ⟦ N ⟧ (n₁ •ᵗ θ) (E • ρ) n₂
      → 𝔼 r′ Σ₃ (letv W′ (N′ [ tseal n₁ ]ᵀ))
    k₂ n₂ E Σ₃ W′ len₃ w′ all′ r′ r′∈ =
      𝔼-expand (one (β-letv w′))
        (𝔼-≡ (eqN n₁ W′)
          (fundamental N (n₁ •ᵗ θ) (ext-𝔾 g all′) len₃ r′ r′∈))

------------------------------------------------------------------------
-- Adequacy
------------------------------------------------------------------------

adequacy : ∀ {M Σ} → Scoped 0 M
  → ∀ r → r ∈ᴿ ⟦ M ⟧ θ₀ ρ₀ (length Σ) → 𝔼 r Σ M
adequacy {M} sc r r∈ =
  𝔼-≡ (sym (trans (subst-id (substᵀ (sealsₙ θ₀) M)) (closed-substᵀ sc)))
    (fundamental M θ₀ (λ x v ()) refl r r∈)

adequacy-val : ∀ {M Σ v m} → Scoped 0 M
  → ret v m ∈ᴿ ⟦ M ⟧ θ₀ ρ₀ (length Σ)
  → Σ[ Σ′ ∈ Store ] Σ[ V ∈ Term ] Σ[ vV ∈ Value V ]
      ((Σ ▷ M —↠ Σ′ ▷ V) × length Σ′ ≡ m × obs v ≡ observe vV)
adequacy-val {v = v} {m} sc v∈ with adequacy sc (ret v m) v∈
adequacy-val {v = v} {m} sc v∈ | ⟨ Σ′ , V , M↠V , vV , len , rel ⟩ =
  Σ′ , V , vV , M↠V , len , obs-𝕍 v rel vV

adequacy-err : ∀ {M Σ} → Scoped 0 M
  → err ∈ᴿ ⟦ M ⟧ θ₀ ρ₀ (length Σ)
  → Σ[ Σ′ ∈ Store ] (Σ ▷ M —↠ Σ′ ▷ ℧)
adequacy-err sc e∈ with adequacy sc err e∈
adequacy-err sc e∈ | ⟨ Σ′ , M↠℧ ⟩ = Σ′ , M↠℧
