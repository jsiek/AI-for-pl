module strong.DualRepProof where

-- THE REPAIRED DualRep≈, AND THE CONTEXT-WELL-FORMEDNESS THREADING IT NEEDS.
--
-- strong.DualDef's DualRep≈ is FALSE as stated (notes/probes/DualRepProbe.agda
-- §1): nothing in  Δ ∣ intOf Δ Θ ⊢ᵇ Θ  constrains Δ's OWN entries, so Δ may
-- store a rep that is not even a type of its own tail, and the dual copies it
-- verbatim.  Adding  ⊢ Δ  is necessary but NOT sufficient (§2): BlkRepWf≈
-- quantifies over the copy width k and the slot i with no relation between
-- them, while the only call site (rvlsᴳ, via bwf-rvlsᴳ) always has
-- suc (i + k) ≡ cmax Θ.  BlkRepWf below adds both.
--
-- §1  numeric scope: Δ ⊢ A depends on Δ only through its length
-- §2  the two copy steps: the dfree-guarded down-shift and the block lift
-- §3  ⊢ Δ's projections: an entry is well formed in its own tail
-- §4  DualRep-wf — THE DELIVERABLE
-- §5  the threading lemmas, ⊢ (intOf Δ Θ) among them
-- §6  the repair plugs in: bwf-dualᴳ with ⊢ Δ in place of the parameter,
--     so residue (1) is GONE and only DualCnc≈ / DualInt≈ remain

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; s≤s; z≤n;
                            _<?_; _≤?_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-assoc;
  +-monoʳ-≤; ∸-monoʳ-≤; ∸-+-assoc; +-suc; +-comm; +-identityʳ;
  ≤-reflexive; _≟_)
open import Data.Bool using (Bool; true; false; _∨_; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (Dec; ⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import strong.Types
open import strong.Context
  using (TCtx; TyEntry; abst; rvld; xrvld; _↓_; _⊢_; entAt;
         wf-var; wf-ℕ; wf-𝔹; wf-⇒; wf-∀;
         _∋tv_; here-abst; here-rvld; here-xrvld;
         skip-abst; skip-rvld; skip-xrvld;
         ⊢_; ⊢∅; ⊢abst; ⊢rvld; ⊢xrvld)
open import strong.Weakening
  using (_∈ᵗ_; fv-var; fv-⇒l; fv-⇒r; fv-∀; fv-scope;
         wf-⇑-abst; wf-⇑-rvld; wf-⇑-xrvld)
open import strong.Unfold using (unfSub; unfoldᵉ)
open import strong.Boundary
open import strong.BReduction
  using (repOf; copyRep; unfEnt; dualᴳ; entᴳ; rvlsᴳ; cncOfRevs;
         bwf-ent; bwf-cncOfRevs)
open import strong.DualDef
  using (repOf-wf; rvl-inj; ⋆≢rvl; entᴳ-⋆; entᴳ-x; entᴳ-B; entᴳ-U;
         entᴳ-B⋆; dual-rep-conc; dual-rep-ok; cnc⋆-licensed;
         DualCnc≈; DualInt≈)

------------------------------------------------------------------------
-- Small arithmetic and Boolean facts, kept local.
------------------------------------------------------------------------

∧-elim : ∀ b₁ b₂ → (b₁ ∧ b₂) ≡ true → (b₁ ≡ true) × (b₂ ≡ true)
∧-elim true  true  e  = refl , refl
∧-elim true  false ()
∧-elim false b₂    ()

-- m ≤ k + (m ∸ k) : the down-shift never loses more than it must
m≤k+m∸k : ∀ m k → m ≤ k + (m ∸ k)
m≤k+m∸k m       zero    = ≤-refl
m≤k+m∸k zero    (suc k) = z≤n
m≤k+m∸k (suc m) (suc k) = s≤s (m≤k+m∸k m k)

-- the down-shift is strictly monotone above its floor
∸-lt : ∀ k X n → k ≤ X → X < k + n → (X ∸ k) < n
∸-lt zero    X       n le       lt       = lt
∸-lt (suc k) zero    n ()       lt
∸-lt (suc k) (suc X) n (s≤s le) (s≤s lt) = ∸-lt k X n le lt

∸-lt′ : ∀ c Y L → c ≤ Y → Y < L → (Y ∸ c) < (L ∸ c)
∸-lt′ zero    Y       L       le       lt       = lt
∸-lt′ (suc c) zero    L       ()       lt
∸-lt′ (suc c) (suc Y) (suc L) (s≤s le) (s≤s lt) = ∸-lt′ c Y L le lt

+-lt : ∀ m {X n} → X < n → (m + X) < (m + n)
+-lt zero    lt = lt
+-lt (suc m) lt = s≤s (+-lt m lt)

m+n≮m : ∀ m n → ¬ ((m + n) < m)
m+n≮m (suc m) n (s≤s lt) = m+n≮m m n lt

------------------------------------------------------------------------
-- §1  NUMERIC SCOPE.  Δ ⊢ A reads Δ only through its length, so the
-- index arithmetic of the copy can be done on numbers.
------------------------------------------------------------------------

data Cl : ℕ → Ty → Set where
  cl-var : ∀ {n X} → X < n           → Cl n (` X)
  cl-ℕ   : ∀ {n}                     → Cl n `ℕ
  cl-𝔹   : ∀ {n}                     → Cl n `𝔹
  cl-⇒   : ∀ {n A B} → Cl n A → Cl n B → Cl n (A ⇒ B)
  cl-∀   : ∀ {n A} → Cl (suc n) A    → Cl n (`∀ A)

∋tv→< : ∀ {Δ X} → Δ ∋tv X → X < length Δ
∋tv→< here-abst      = s≤s z≤n
∋tv→< here-rvld      = s≤s z≤n
∋tv→< here-xrvld     = s≤s z≤n
∋tv→< (skip-abst p)  = s≤s (∋tv→< p)
∋tv→< (skip-rvld p)  = s≤s (∋tv→< p)
∋tv→< (skip-xrvld p) = s≤s (∋tv→< p)

<→∋tv : ∀ (Δ : TCtx) {X} → X < length Δ → Δ ∋tv X
<→∋tv []             ()
<→∋tv (abst ∷ Δ)    {zero}  lt       = here-abst
<→∋tv (rvld C ∷ Δ)  {zero}  lt       = here-rvld
<→∋tv (xrvld C ∷ Δ) {zero}  lt       = here-xrvld
<→∋tv (abst ∷ Δ)    {suc X} (s≤s lt) = skip-abst (<→∋tv Δ lt)
<→∋tv (rvld C ∷ Δ)  {suc X} (s≤s lt) = skip-rvld (<→∋tv Δ lt)
<→∋tv (xrvld C ∷ Δ) {suc X} (s≤s lt) = skip-xrvld (<→∋tv Δ lt)

⊢→Cl : ∀ {Δ A} → Δ ⊢ A → Cl (length Δ) A
⊢→Cl (wf-var p) = cl-var (∋tv→< p)
⊢→Cl wf-ℕ       = cl-ℕ
⊢→Cl wf-𝔹       = cl-𝔹
⊢→Cl (wf-⇒ a b) = cl-⇒ (⊢→Cl a) (⊢→Cl b)
⊢→Cl (wf-∀ a)   = cl-∀ (⊢→Cl a)

Cl→⊢ : ∀ (Δ : TCtx) {A} → Cl (length Δ) A → Δ ⊢ A
Cl→⊢ Δ (cl-var lt) = wf-var (<→∋tv Δ lt)
Cl→⊢ Δ cl-ℕ        = wf-ℕ
Cl→⊢ Δ cl-𝔹        = wf-𝔹
Cl→⊢ Δ (cl-⇒ a b)  = wf-⇒ (Cl→⊢ Δ a) (Cl→⊢ Δ b)
Cl→⊢ Δ (cl-∀ a)    = wf-∀ (Cl→⊢ (abst ∷ Δ) a)

cl-mono : ∀ {m n A} → m ≤ n → Cl m A → Cl n A
cl-mono le (cl-var lt) = cl-var (≤-trans lt le)
cl-mono le cl-ℕ        = cl-ℕ
cl-mono le cl-𝔹        = cl-𝔹
cl-mono le (cl-⇒ a b)  = cl-⇒ (cl-mono le a) (cl-mono le b)
cl-mono le (cl-∀ a)    = cl-∀ (cl-mono (s≤s le) a)

------------------------------------------------------------------------
-- §2  THE TWO COPY STEPS.  copyRep k n B = renameᵗ (n +_) (dnT k B).
------------------------------------------------------------------------

-- the block lift: any renaming that respects the bound
cl-ren : ∀ {m n} (ρ : Renameᵗ) {A} → (∀ X → X < m → ρ X < n)
       → Cl m A → Cl n (renameᵗ ρ A)
cl-ren ρ h (cl-var lt) = cl-var (h _ lt)
cl-ren ρ h cl-ℕ        = cl-ℕ
cl-ren ρ h cl-𝔹        = cl-𝔹
cl-ren ρ h (cl-⇒ a b)  = cl-⇒ (cl-ren ρ h a) (cl-ren ρ h b)
cl-ren {m} {n} ρ h (cl-∀ a) = cl-∀ (cl-ren (extᵗ ρ) h′ a)
  where
    h′ : ∀ X → X < suc m → extᵗ ρ X < suc n
    h′ zero    lt       = s≤s z≤n
    h′ (suc X) (s≤s lt) = s≤s (h X lt)

-- reading the guard off a variable
dfree-var : ∀ b k X → dfree b k (` X) ≡ true → (X < b) ⊎ ((b + k) ≤ X)
dfree-var b k X df = go (X <? b) ((b + k) ≤? X) df
  where
    go : (d₁ : Dec (X < b)) (d₂ : Dec ((b + k) ≤ X))
       → (⌊ d₁ ⌋ ∨ ⌊ d₂ ⌋) ≡ true → (X < b) ⊎ ((b + k) ≤ X)
    go (yes p) d₂       e  = inj₁ p
    go (no ¬p) (yes q)  e  = inj₂ q
    go (no ¬p) (no ¬q)  ()

-- the DOWN-SHIFT step, guarded by dfree.  b counts the binders already
-- passed; the forbidden window is [b , b + k), which is exactly what
-- ρ is not asked about.
cl-dn : ∀ (ρ : Renameᵗ) b k n A
      → (∀ X → X < b → ρ X < (b + n))
      → (∀ X → (b + k) ≤ X → X < (b + k + n) → ρ X < (b + n))
      → dfree b k A ≡ true → Cl (b + k + n) A
      → Cl (b + n) (renameᵗ ρ A)
cl-dn ρ b k n (` X) h₁ h₂ df (cl-var lt) with dfree-var b k X df
cl-dn ρ b k n (` X) h₁ h₂ df (cl-var lt) | inj₁ p = cl-var (h₁ X p)
cl-dn ρ b k n (` X) h₁ h₂ df (cl-var lt) | inj₂ q = cl-var (h₂ X q lt)
cl-dn ρ b k n `ℕ      h₁ h₂ df cl-ℕ       = cl-ℕ
cl-dn ρ b k n `𝔹      h₁ h₂ df cl-𝔹       = cl-𝔹
cl-dn ρ b k n (A ⇒ B) h₁ h₂ df (cl-⇒ a c) =
  cl-⇒ (cl-dn ρ b k n A h₁ h₂ (proj₁ (∧-elim _ _ df)) a)
       (cl-dn ρ b k n B h₁ h₂ (proj₂ (∧-elim _ _ df)) c)
cl-dn ρ b k n (`∀ A) h₁ h₂ df (cl-∀ a) =
  cl-∀ (cl-dn (extᵗ ρ) (suc b) k n A h₁′ h₂′ df a)
  where
    h₁′ : ∀ X → X < suc b → extᵗ ρ X < (suc b + n)
    h₁′ zero    lt       = s≤s z≤n
    h₁′ (suc X) (s≤s lt) = s≤s (h₁ X lt)
    h₂′ : ∀ X → (suc b + k) ≤ X → X < (suc b + k + n)
        → extᵗ ρ X < (suc b + n)
    h₂′ zero    ()       lt
    h₂′ (suc X) (s≤s le) (s≤s lt) = s≤s (h₂ X le lt)

-- the two steps, in the shape copyRep asks for
cl-dnT : ∀ k n B → dfree 0 k B ≡ true → Cl (k + n) B → Cl n (dnT k B)
cl-dnT k n B df c = cl-dn (_∸ k) 0 k n B h₁ h₂ df c
  where
    h₁ : ∀ X → X < 0 → (X ∸ k) < n
    h₁ X ()
    h₂ : ∀ X → k ≤ X → X < (k + n) → (X ∸ k) < n
    h₂ X le lt = ∸-lt k X n le lt

cl-copyRep : ∀ k r n B → dfree 0 k B ≡ true → Cl (k + n) B
           → Cl (r + n) (copyRep k r B)
cl-copyRep k r n B df c =
  cl-ren (r +_) (λ X lt → +-lt r lt) (cl-dnT k n B df c)

------------------------------------------------------------------------
-- §3  ⊢ Δ's PROJECTIONS.  What the preservation statement would carry.
------------------------------------------------------------------------

⊢-↓ : ∀ {Δ : TCtx} i → ⊢ Δ → ⊢ (Δ ↓ i)
⊢-↓ {[]}          i       d            = ⊢∅
⊢-↓ {abst ∷ Δ}    zero    (⊢abst d)    = d
⊢-↓ {rvld C ∷ Δ}  zero    (⊢rvld d _)  = d
⊢-↓ {xrvld C ∷ Δ} zero    (⊢xrvld d)   = d
⊢-↓ {abst ∷ Δ}    (suc i) (⊢abst d)    = ⊢-↓ i d
⊢-↓ {rvld C ∷ Δ}  (suc i) (⊢rvld d _)  = ⊢-↓ i d
⊢-↓ {xrvld C ∷ Δ} (suc i) (⊢xrvld d)   = ⊢-↓ i d

-- THE FACT DualDef's comment names: a knowledge entry is well formed in its
-- own tail, and that tail is exactly the prefix Δ ↓ i.
⊢-entAt : ∀ (Δ : TCtx) i B → ⊢ Δ → entAt Δ i ≡ rvld B → (Δ ↓ i) ⊢ B
⊢-entAt []            i       B d           ()
⊢-entAt (abst ∷ Δ)    zero    B (⊢abst _)   ()
⊢-entAt (xrvld C ∷ Δ) zero    B (⊢xrvld _)  ()
⊢-entAt (rvld C ∷ Δ)  zero    B (⊢rvld _ w) refl = w
⊢-entAt (abst ∷ Δ)    (suc i) B (⊢abst d)   e = ⊢-entAt Δ i B d e
⊢-entAt (rvld C ∷ Δ)  (suc i) B (⊢rvld d _) e = ⊢-entAt Δ i B d e
⊢-entAt (xrvld C ∷ Δ) (suc i) B (⊢xrvld d)  e = ⊢-entAt Δ i B d e

-- substitution, restricted to the FREE variables (the subst analogue of
-- strong.Weakening's wf-rename-fv)
wf-subst-fv : ∀ {Δ₁ Δ₂ : TCtx} (σ : Substᵗ) {A}
            → (∀ Y → Y ∈ᵗ A → Δ₂ ⊢ σ Y) → Δ₁ ⊢ A → Δ₂ ⊢ substᵗ σ A
wf-subst-fv σ h (wf-var p) = h _ fv-var
wf-subst-fv σ h wf-ℕ       = wf-ℕ
wf-subst-fv σ h wf-𝔹       = wf-𝔹
wf-subst-fv σ h (wf-⇒ a b) =
  wf-⇒ (wf-subst-fv σ (λ Y y → h Y (fv-⇒l y)) a)
       (wf-subst-fv σ (λ Y y → h Y (fv-⇒r y)) b)
wf-subst-fv {Δ₂ = Δ₂} σ h (wf-∀ {A = A₀} a) =
  wf-∀ (wf-subst-fv (extsᵗ σ) h′ a)
  where
    h′ : ∀ Y → Y ∈ᵗ A₀ → (abst ∷ Δ₂) ⊢ extsᵗ σ Y
    h′ zero    y = wf-var here-abst
    h′ (suc Y) y = wf-⇑-abst (h Y (fv-∀ y))

-- the unfolding of a well-formed type in a well-formed context is well
-- formed there — what the SECOND-CHANCE copy (unfEnt) needs
unfSub-wf : ∀ (Δ : TCtx) → ⊢ Δ → ∀ X → Δ ∋tv X → Δ ⊢ unfSub Δ X
unfSub-wf [] d X ()
unfSub-wf (abst ∷ Δ)    (⊢abst d)    zero    p = wf-var here-abst
unfSub-wf (xrvld C ∷ Δ) (⊢xrvld d)   zero    p = wf-var here-xrvld
unfSub-wf (rvld C ∷ Δ)  (⊢rvld d w)  zero    p =
  wf-⇑-rvld (wf-subst-fv (unfSub Δ) (λ Y y → unfSub-wf Δ d Y (fv-scope w y)) w)
unfSub-wf (abst ∷ Δ) (⊢abst d) (suc X) (skip-abst p) =
  wf-⇑-abst (unfSub-wf Δ d X p)
unfSub-wf (rvld C ∷ Δ) (⊢rvld d w) (suc X) (skip-rvld p) =
  wf-⇑-rvld (unfSub-wf Δ d X p)
unfSub-wf (xrvld C ∷ Δ) (⊢xrvld d) (suc X) (skip-xrvld p) =
  wf-⇑-xrvld (unfSub-wf Δ d X p)

unfold-wf : ∀ (Δ : TCtx) → ⊢ Δ → ∀ {A} → Δ ⊢ A → Δ ⊢ unfoldᵉ Δ A
unfold-wf Δ d {A} w =
  wf-subst-fv (unfSub Δ) (λ Y y → unfSub-wf Δ d Y (fv-scope w y)) w

------------------------------------------------------------------------
-- §4  DUALREP, REPAIRED AND PROVED.  The two premises the refutations ask
-- for: ⊢ Δ (notes/probes/DualRepProbe.agda §1) and the call site's index
-- relation cmax Θ ≤ suc (i + k) (§2 there).  bwf is NOT used.
------------------------------------------------------------------------

len-↓ : ∀ (Δ : TCtx) i → length (Δ ↓ i) ≡ length Δ ∸ suc i
len-↓ []            i       = refl
len-↓ (abst ∷ Δ)    zero    = refl
len-↓ (rvld C ∷ Δ)  zero    = refl
len-↓ (xrvld C ∷ Δ) zero    = refl
len-↓ (abst ∷ Δ)    (suc i) = len-↓ Δ i
len-↓ (rvld C ∷ Δ)  (suc i) = len-↓ Δ i
len-↓ (xrvld C ∷ Δ) (suc i) = len-↓ Δ i

len-dropN : ∀ n (Δ : TCtx) → length (dropN n Δ) ≡ length Δ ∸ n
len-dropN zero    Δ       = refl
len-dropN (suc n) []      = refl
len-dropN (suc n) (E ∷ Δ) = len-dropN n Δ

len-intOf : ∀ (Δ : TCtx) Θ
          → length (intOf Δ Θ) ≡ revs Θ + (length Δ ∸ cmax Θ)
len-intOf Δ Θ =
  trans (length-++ (revEnts Θ 0 Θ))
        (cong₂ _+_ (len-revEnts Θ 0 Θ) (len-dropN (cmax Θ) Δ))

-- THE COPY LEMMA.  A rep well formed in its own tail Δ ↓ i, copied k slots
-- down and lifted over the dual's reveal block, is well formed in the dual's
-- exterior intOf Δ Θ — provided the drop is no wider than the slot's own
-- depth plus the copy width.
copy-wf : ∀ (Δ : TCtx) Θ k i B → cmax Θ ≤ suc (i + k) → (Δ ↓ i) ⊢ B
        → dfree 0 k B ≡ true → intOf Δ Θ ⊢ copyRep k (revs Θ) B
copy-wf Δ Θ k i B hc w df =
  Cl→⊢ (intOf Δ Θ)
    (subst (λ n → Cl n (copyRep k (revs Θ) B)) (sym (len-intOf Δ Θ))
      (cl-copyRep k (revs Θ) (length Δ ∸ cmax Θ) B df
        (cl-mono bound clB)))
  where
    clB : Cl (length Δ ∸ suc i) B
    clB = subst (λ n → Cl n B) (len-↓ Δ i) (⊢→Cl w)
    step : ((length Δ ∸ suc i) ∸ k) ≤ (length Δ ∸ cmax Θ)
    step = subst (λ n → n ≤ (length Δ ∸ cmax Θ))
                 (sym (∸-+-assoc (length Δ) (suc i) k))
                 (∸-monoʳ-≤ (length Δ) hc)
    bound : (length Δ ∸ suc i) ≤ (k + (length Δ ∸ cmax Θ))
    bound = ≤-trans (m≤k+m∸k (length Δ ∸ suc i) k) (+-monoʳ-≤ k step)

-- THE REPAIRED STATEMENT (contrast strong.DualDef's BlkRepWf≈, which has
-- neither premise and is refuted in notes/probes/DualRepProbe.agda).
BlkRepWf : TCtx → BCtx → Set
BlkRepWf Δ Θ = ∀ k i B → cmax Θ ≤ suc (i + k) → isConc i Θ ≡ false
  → entAt Δ i ≡ rvld B
  → (dfree 0 k B ≡ true → intOf Δ Θ ⊢ copyRep k (revs Θ) B)
  × (dfree 0 k B ≡ false → dfree 0 k (unfEnt Δ i B) ≡ true
     → intOf Δ Θ ⊢ copyRep k (revs Θ) (unfEnt Δ i B))

-- *** THE DELIVERABLE ***
DualRep-wf : ∀ {Δ : TCtx} {Θ : BCtx} → ⊢ Δ → Δ ∣ intOf Δ Θ ⊢ᵇ Θ
           → BlkRepWf Δ Θ
DualRep-wf {Δ} {Θ} d bwf k i B hc hnc he =
    (λ df → copy-wf Δ Θ k i B hc wB df)
  , (λ df du → copy-wf Δ Θ k i (unfEnt Δ i B) hc wU du)
  where
    wB : (Δ ↓ i) ⊢ B
    wB = ⊢-entAt Δ i B d he
    wU : (Δ ↓ i) ⊢ unfEnt Δ i B
    wU = unfold-wf (Δ ↓ i) (⊢-↓ i d) wB

DualRepWf : Set
DualRepWf = ∀ {Δ : TCtx} {Θ : BCtx} → ⊢ Δ → Δ ∣ intOf Δ Θ ⊢ᵇ Θ
          → BlkRepWf Δ Θ

dual-rep-wf : DualRepWf
dual-rep-wf = DualRep-wf

------------------------------------------------------------------------
-- §5  THE THREADING LEMMAS.  If preservation gains a ⊢ Δ premise, every
-- context extension a ξ rule performs must preserve it: ⊢ [] for the
-- top-level statement, ⊢ (abst ∷ Δ) for ξ-Λ, and ⊢ (intOf Δ Θ) for ξ-⟪⟫.
-- The last is the real one: it says the interior's MINTED entries are well
-- formed, which is a fact about ⟦_⟧ᴴ's two guards.
------------------------------------------------------------------------

⊢-dropN : ∀ n (Δ : TCtx) → ⊢ Δ → ⊢ (dropN n Δ)
⊢-dropN zero    Δ            d           = d
⊢-dropN (suc n) []           d           = ⊢∅
⊢-dropN (suc n) (abst ∷ Δ)   (⊢abst d)   = ⊢-dropN n Δ d
⊢-dropN (suc n) (rvld C ∷ Δ) (⊢rvld d _) = ⊢-dropN n Δ d
⊢-dropN (suc n) (xrvld C ∷ Δ) (⊢xrvld d) = ⊢-dropN n Δ d

-- reading the bfree guard off one free variable
m+n∸m : ∀ m n → (m + n) ∸ m ≡ n
m+n∸m zero    n = refl
m+n∸m (suc m) n = m+n∸m m n

bfree-var : ∀ Θ d Y → bfree Θ d (` (d + Y)) ≡ true
          → isOk (slotAt Θ Y) ≡ true
bfree-var Θ d Y bf = go ((d + Y) <? d) bf
  where
    go : (dc : Dec ((d + Y) < d))
       → (⌊ dc ⌋ ∨ isOk (slotAt Θ ((d + Y) ∸ d))) ≡ true
       → isOk (slotAt Θ Y) ≡ true
    go (yes p) e = ⊥-elim (m+n≮m d Y p)
    go (no ¬p) e =
      subst (λ n → isOk (slotAt Θ n) ≡ true) (m+n∸m d Y) e

bfree-fv : ∀ Θ d {A} → bfree Θ d A ≡ true → ∀ {Y} → (d + Y) ∈ᵗ A
         → isOk (slotAt Θ Y) ≡ true
bfree-fv Θ d {` X}     bf {Y} fv-var    = bfree-var Θ d Y bf
bfree-fv Θ d {A₁ ⇒ A₂} bf {Y} (fv-⇒l y) =
  bfree-fv Θ d (proj₁ (∧-elim _ _ bf)) y
bfree-fv Θ d {A₁ ⇒ A₂} bf {Y} (fv-⇒r y) =
  bfree-fv Θ d (proj₂ (∧-elim _ _ bf)) y
bfree-fv Θ d {`∀ A₀}   bf {Y} (fv-∀ y)  = bfree-fv Θ (suc d) bf y

-- an ACCESSIBLE slot is kept or concealed
slotAt-ok : ∀ Θ Y → isOk (slotAt Θ Y) ≡ true
          → (cmax Θ ≤ Y) ⊎ (isConc Y Θ ≡ true)
slotAt-ok Θ Y h with cmax Θ ≤? Y | h
slotAt-ok Θ Y h | yes p | _  = inj₁ p
slotAt-ok Θ Y h | no ¬p | h′ with isConc Y Θ | h′
slotAt-ok Θ Y h | no ¬p | h′ | true  | _  = inj₂ refl
slotAt-ok Θ Y h | no ¬p | h′ | false | ()

-- ONE CONCEAL of the reading map: its image is the rep (well formed in the
-- interior by the boundary's own licence) or the kept slot's index
cnc-step : ∀ {Ψ : TCtx} X A Ξ r m Y → Ψ ⊢ A
  → (isConc Y Ξ ≡ true → Ψ ⊢ γcnc r m Ξ Y)
  → (isConc Y Ξ ≡ false → γcnc r m Ξ Y ≡ ` (r + (Y ∸ m)))
  → (isConc Y (cnc X A ∷ Ξ) ≡ true → Ψ ⊢ γcnc r m (cnc X A ∷ Ξ) Y)
  × (isConc Y (cnc X A ∷ Ξ) ≡ false
     → γcnc r m (cnc X A ∷ Ξ) Y ≡ ` (r + (Y ∸ m)))
cnc-step X A Ξ r m Y w h₁ h₂ with X ≟ Y | Y ≟ X
cnc-step X A Ξ r m Y w h₁ h₂ | yes e | yes q = (λ _ → w) , (λ ())
cnc-step X A Ξ r m Y w h₁ h₂ | yes e | no ¬q = ⊥-elim (¬q (sym e))
cnc-step X A Ξ r m Y w h₁ h₂ | no ¬e | yes q = ⊥-elim (¬e (sym q))
cnc-step X A Ξ r m Y w h₁ h₂ | no ¬e | no ¬q = h₁ , h₂

γ-wf : ∀ {Δ Ψ : TCtx} Θ Ξ r m → Bwf Δ Ψ Θ Ξ → ∀ Y
     → (isConc Y Ξ ≡ true → Ψ ⊢ γcnc r m Ξ Y)
     × (isConc Y Ξ ≡ false → γcnc r m Ξ Y ≡ ` (r + (Y ∸ m)))
γ-wf Θ []            r m bwf[]                Y = (λ ()) , (λ _ → refl)
γ-wf Θ (rvl A ∷ Ξ)   r m (bwf↑ w b)           Y = γ-wf Θ Ξ r m b Y
γ-wf Θ (rvl⋆ ∷ Ξ)    r m (bwf⋆ b)             Y = γ-wf Θ Ξ r m b Y
γ-wf Θ (cnc⋆ X ∷ Ξ)  r m (bwf⋆↓ p b)          Y = γ-wf Θ Ξ r m b Y
γ-wf Θ (cnc X A ∷ Ξ) r m (bwf↓ p rev w b)     Y =
  cnc-step X A Ξ r m Y w (proj₁ (γ-wf Θ Ξ r m b Y))
                         (proj₂ (γ-wf Θ Ξ r m b Y))
γ-wf Θ (cnc X A ∷ Ξ) r m (bwf↓x p so sk w b)  Y =
  cnc-step X A Ξ r m Y w (proj₁ (γ-wf Θ Ξ r m b Y))
                         (proj₂ (γ-wf Θ Ξ r m b Y))

-- THE RAW READING IS A TYPE OF THE INTERIOR.  This is exactly what the
-- bfree guard of ⟦_⟧ᴴ buys: a blocked slot would have no honest image.
rawRead-wf : ∀ {Δ : TCtx} Θ A → Δ ∣ intOf Δ Θ ⊢ᵇ Θ → Δ ⊢ A
           → bfree Θ 0 A ≡ true → intOf Δ Θ ⊢ rawRead Θ A
rawRead-wf {Δ} Θ A bwf w bf = wf-subst-fv (rdSub Θ) hyp w
  where
    hyp : ∀ Y → Y ∈ᵗ A → intOf Δ Θ ⊢ rdSub Θ Y
    hyp Y y = go (isConc Y Θ) refl
      where
        okY : isOk (slotAt Θ Y) ≡ true
        okY = bfree-fv Θ 0 bf y
        go : ∀ b → isConc Y Θ ≡ b → intOf Δ Θ ⊢ rdSub Θ Y
        go true  e = proj₁ (γ-wf Θ Θ (revs Θ) (cmax Θ) bwf Y) e
        go false e =
          subst (λ T → intOf Δ Θ ⊢ T)
                (sym (proj₂ (γ-wf Θ Θ (revs Θ) (cmax Θ) bwf Y) e))
                wfvar
          where
            hc : cmax Θ ≤ Y
            hc with slotAt-ok Θ Y okY
            hc | inj₁ p  = p
            hc | inj₂ q  with trans (sym q) e
            hc | inj₂ q  | ()
            lt : (revs Θ + (Y ∸ cmax Θ)) < length (intOf Δ Θ)
            lt = subst (λ n → (revs Θ + (Y ∸ cmax Θ)) < n)
                       (sym (len-intOf Δ Θ))
                       (+-lt (revs Θ)
                         (∸-lt′ (cmax Θ) Y (length Δ) hc
                           (∋tv→< (fv-scope w y))))
            wfvar : intOf Δ Θ ⊢ ` (revs Θ + (Y ∸ cmax Θ))
            wfvar = wf-var (<→∋tv (intOf Δ Θ) lt)

-- THE INTERIOR'S MINTED ENTRIES ARE WELL FORMED.  The reveal block is
-- walked with j counting the entries already emitted; the invariant
-- j + revs Ξ ≡ revs Θ is what places the entry's own tail.
⊢-revEnts : ∀ {Δ : TCtx} Θ Ξ j → ⊢ Δ → Δ ∣ intOf Δ Θ ⊢ᵇ Θ
          → Bwf Δ (intOf Δ Θ) Θ Ξ → j + revs Ξ ≡ revs Θ
          → ⊢ (revEnts Θ j Ξ ++ dropN (cmax Θ) Δ)
⊢-revEnts {Δ} Θ [] j d bwf bwf[] eq = ⊢-dropN (cmax Θ) Δ d
⊢-revEnts {Δ} Θ (rvl⋆ ∷ Ξ) j d bwf (bwf⋆ b) eq =
  ⊢abst (⊢-revEnts Θ Ξ (suc j) d bwf b
          (trans (sym (+-suc j (revs Ξ))) eq))
⊢-revEnts {Δ} Θ (cnc X A ∷ Ξ) j d bwf (bwf↓ p rev w b) eq =
  ⊢-revEnts Θ Ξ j d bwf b eq
⊢-revEnts {Δ} Θ (cnc X A ∷ Ξ) j d bwf (bwf↓x p so sk w b) eq =
  ⊢-revEnts Θ Ξ j d bwf b eq
⊢-revEnts {Δ} Θ (cnc⋆ X ∷ Ξ) j d bwf (bwf⋆↓ p b) eq =
  ⊢-revEnts Θ Ξ j d bwf b eq
⊢-revEnts {Δ} Θ (rvl A ∷ Ξ) j d bwf (bwf↑ w b) eq =
  go (expr Θ j A) refl
  where
    dd : ℕ
    dd = length Δ ∸ cmax Θ
    rest : TCtx
    rest = revEnts Θ (suc j) Ξ ++ dropN (cmax Θ) Δ
    eq′ : suc j + revs Ξ ≡ revs Θ
    eq′ = trans (sym (+-suc j (revs Ξ))) eq
    ih : ⊢ rest
    ih = ⊢-revEnts Θ Ξ (suc j) d bwf b eq′
    len-rest : length rest ≡ revs Ξ + dd
    len-rest =
      trans (length-++ (revEnts Θ (suc j) Ξ))
            (cong₂ _+_ (len-revEnts Θ (suc j) Ξ) (len-dropN (cmax Θ) Δ))
    shape : revs Θ + dd ≡ suc j + (revs Ξ + dd)
    shape = trans (cong (_+ dd) (sym eq′)) (+-assoc (suc j) (revs Ξ) dd)
    wfdn : expr Θ j A ≡ true → rest ⊢ dnT (suc j) (rawRead Θ A)
    wfdn ex =
      Cl→⊢ rest
        (subst (λ n → Cl n (dnT (suc j) (rawRead Θ A)))
               (sym len-rest)
               (cl-dnT (suc j) (revs Ξ + dd) (rawRead Θ A)
                       (proj₂ (∧-elim _ _ ex))
                       (subst (λ n → Cl n (rawRead Θ A)) shape clR)))
      where
        clR : Cl (revs Θ + dd) (rawRead Θ A)
        clR = subst (λ n → Cl n (rawRead Θ A)) (len-intOf Δ Θ)
                (⊢→Cl (rawRead-wf Θ A bwf w (proj₁ (∧-elim _ _ ex))))
    go : ∀ bl → expr Θ j A ≡ bl
       → ⊢ ((if bl then rvld (dnT (suc j) (rawRead Θ A))
                   else xrvld A) ∷ rest)
    go true  e = ⊢rvld ih (wfdn e)
    go false e = ⊢xrvld ih

------------------------------------------------------------------------
-- THE THREE THREADING LEMMAS, in the shape a ⊢ Δ-carrying preservation
-- would consume them: one per context extension a ξ rule performs.
------------------------------------------------------------------------

⊢-[] : ⊢ []
⊢-[] = ⊢∅

⊢-abst : ∀ {Δ : TCtx} → ⊢ Δ → ⊢ (abst ∷ Δ)          -- ξ-Λ
⊢-abst = ⊢abst

⊢-intOf : ∀ {Δ : TCtx} {Θ : BCtx}                    -- ξ-⟪⟫
        → ⊢ Δ → Δ ∣ intOf Δ Θ ⊢ᵇ Θ → ⊢ (intOf Δ Θ)
⊢-intOf {Δ} {Θ} d bwf = ⊢-revEnts Θ Θ 0 d bwf bwf refl

-- and the dual's own interior, which is one more application of the same
-- lemma once the dual is known to be well formed there
⊢-intOf-dual : ∀ {Δ : TCtx} {Θ : BCtx} → ⊢ Δ → Δ ∣ intOf Δ Θ ⊢ᵇ Θ
             → intOf Δ Θ ∣ intOf (intOf Δ Θ) (dualᴳ Δ Θ) ⊢ᵇ dualᴳ Δ Θ
             → ⊢ (intOf (intOf Δ Θ) (dualᴳ Δ Θ))
⊢-intOf-dual d bwf bwfᵈ = ⊢-intOf (⊢-intOf d bwf) bwfᵈ

------------------------------------------------------------------------
-- §6  THE REPAIR PLUGS IN.  strong.BReduction's bwf-rvlsᴳ asks its
-- hypothesis for EVERY (k , s), which is why strong.DualDef's BlkRepWf≈ had
-- to as well.  The dual's reveal block is built by rvlsᴳ (cmax Θ) 0, whose
-- recursion keeps  k + s ≡ cmax Θ , so the entry at (s , k) always has
-- suc (s + k) ≡ cmax Θ — exactly BlkRepWf's premise.  Carrying that
-- invariant, DualRep≈ is DISCHARGED: bwf-dualᴳ needs only ⊢ Δ.
------------------------------------------------------------------------

bwf-rvlsᴳ-idx : ∀ {Ψ Δ' Θᵈ} k s (Γ : TCtx) Θ Ξ₀ → k + s ≡ cmax Θ
  → (∀ k′ s′ R → suc (s′ + k′) ≡ cmax Θ → entᴳ Γ Θ s′ k′ ≡ rvl R → Ψ ⊢ R)
  → Bwf Ψ Δ' Θᵈ Ξ₀
  → Bwf Ψ Δ' Θᵈ (rvlsᴳ k s Γ Θ ++ Ξ₀)
bwf-rvlsᴳ-idx zero    s Γ Θ Ξ₀ eq h b = b
bwf-rvlsᴳ-idx (suc k) s Γ Θ Ξ₀ eq h b =
  bwf-ent Γ Θ s k (rvlsᴳ k (suc s) Γ Θ ++ Ξ₀)
    (λ R e → h k s R idx e)
    (bwf-rvlsᴳ-idx k (suc s) Γ Θ Ξ₀ eq′ h b)
  where
    idx : suc (s + k) ≡ cmax Θ
    idx = trans (cong suc (+-comm s k)) eq
    eq′ : k + suc s ≡ cmax Θ
    eq′ = trans (+-suc k s) eq

-- the same assembly as strong.DualDef's bwf-dualᴳ, with the BlkRepWf≈
-- PARAMETER replaced by the ⊢ Δ THEOREM
bwf-dualᴳ-wf : ∀ {Δ Δ' : TCtx} Θ → ⊢ Δ → Δ ∣ intOf Δ Θ ⊢ᵇ Θ
  → Bwf (intOf Δ Θ) Δ' (dualᴳ Δ Θ) (cncOfRevs 0 Θ)
  → intOf Δ Θ ∣ Δ' ⊢ᵇ dualᴳ Δ Θ
bwf-dualᴳ-wf {Δ} {Δ'} Θ dd bwf bcnc =
  bwf-rvlsᴳ-idx (cmax Θ) 0 Δ Θ (cncOfRevs 0 Θ)
    (+-identityʳ (cmax Θ)) hrvl bcnc
  where
    hrvl : ∀ k s R → suc (s + k) ≡ cmax Θ → entᴳ Δ Θ s k ≡ rvl R
         → intOf Δ Θ ⊢ R
    hrvl k s R idx e = go (isConc s Θ) refl
      where
        hc : cmax Θ ≤ suc (s + k)
        hc = ≤-reflexive (sym idx)
        go : ∀ bl → isConc s Θ ≡ bl → intOf Δ Θ ⊢ R
        go true  ec = dual-rep-conc Θ bwf k s ec R e
        go false ec = blkcase (entAt Δ s) refl
          where
            blkcase : ∀ (E : TyEntry) → entAt Δ s ≡ E → intOf Δ Θ ⊢ R
            blkcase abst      ee =
              ⊥-elim (⋆≢rvl (trans (sym (entᴳ-⋆ Δ Θ s k ec ee)) e))
            blkcase (xrvld B) ee =
              ⊥-elim (⋆≢rvl (trans (sym (entᴳ-x Δ Θ s k B ec ee)) e))
            blkcase (rvld B)  ee = guardcase (dfree 0 k B) refl
              where
                blkw : (dfree 0 k B ≡ true
                       → intOf Δ Θ ⊢ copyRep k (revs Θ) B)
                    × (dfree 0 k B ≡ false
                       → dfree 0 k (unfEnt Δ s B) ≡ true
                       → intOf Δ Θ ⊢ copyRep k (revs Θ) (unfEnt Δ s B))
                blkw = DualRep-wf dd bwf k s B hc ec ee
                guardcase : ∀ g → dfree 0 k B ≡ g → intOf Δ Θ ⊢ R
                guardcase true  eg =
                  subst (λ T → intOf Δ Θ ⊢ T)
                        (rvl-inj
                          (trans (sym (entᴳ-B Δ Θ s k B ec ee eg)) e))
                        (proj₁ blkw eg)
                guardcase false eg =
                  ucase (dfree 0 k (unfEnt Δ s B)) refl
                  where
                    ucase : ∀ u → dfree 0 k (unfEnt Δ s B) ≡ u
                          → intOf Δ Θ ⊢ R
                    ucase true  eu =
                      subst (λ T → intOf Δ Θ ⊢ T)
                            (rvl-inj
                              (trans (sym (entᴳ-U Δ Θ s k B ec ee eg eu))
                                     e))
                            (proj₂ blkw eg eu)
                    ucase false eu =
                      ⊥-elim (⋆≢rvl
                        (trans (sym (entᴳ-B⋆ Δ Θ s k B ec ee eg eu)) e))

-- … and so the dual's well-formedness now rests on TWO residues, not
-- three: DualRep≈ is gone, replaced by the ⊢ Δ the ξ-⟪⟫ threading supplies.
bwf-dual-wf : DualCnc≈ → DualInt≈
  → ∀ {Δ : TCtx} {Θ : BCtx} → ⊢ Δ → Δ ∣ intOf Δ Θ ⊢ᵇ Θ
  → intOf Δ Θ ∣ intOf (intOf Δ Θ) (dualᴳ Δ Θ) ⊢ᵇ dualᴳ Δ Θ
bwf-dual-wf dc di {Δ} {Θ} dd bwf =
  bwf-dualᴳ-wf Θ dd bwf
    (bwf-cncOfRevs 0 Θ (dc bwf)
      (λ k lt → dual-rep-ok Θ bwf (di bwf) k lt)
      (λ k lt → cnc⋆-licensed Δ Θ (0 + k) lt))
