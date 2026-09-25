module strong-rep-nu.proof.ErasureTypes where

-- File Charter:
--   * THE TYPE-LEVEL FACTS ABOUT ERASURE (strong-rep-nu.Erasure).
--     §1 lookups and the name map (`lookupⁿ-sound`, `nameσ-underΛ`,
--     `nameσ-alloc`, `nameσ-live`); §2 small substitution algebra;
--     §3 what a stored cell denotes (`env-bind`); §4 a READING erases
--     through the store (`erase-~`, `erase-≈`); §5 CONVERSIONS ARE
--     ERASURE-IDENTITIES (`conv-erase`) and their endpoints are read
--     (`conv-scoped`); §6 `Λ` and `⇑` (`erase-underΛ`, `erase-⇑`,
--     `eraseCtx-⤊`); §7 scoping (`erase-wf`); §8 source-side
--     helpers (weakening, `substˢᵗ-cong`, `substˢᵗ-id`); §9 values;
--     §10 `inside-sound`.
--   * THE JUNK LAW.  `nameσ` sends an UNNAMED ordinary variable to
--     itself, so facts that change the store or the name map hold only
--     on READ types; they go through `_⊢_~_` (§4), never pointwise on
--     `nameσ`.

open import Data.Nat using (ℕ; zero; suc; _<_; _+_; s≤s; z≤n)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.List.Properties using (map-++)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Product using (Σ; Σ-syntax; ∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.Boundary
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
  using (Term; Ctx; ⤊; _∋_⦂_; here; there; Simple; Value; S-$; S-true;
         S-false; S-ƛ; S-Λ; V-simple; V-⟪⟫)
open import strong-rep-nu.Source
open import strong-rep-nu.SourceReduction
open import strong-rep-nu.Erasure
open import strong-rep-nu.proof.TypeSubst
  using (subst-cong; subst-id; sub-sub; _⨟ᵗ_; rename-subst-commute;
         rename-subst)
open import strong-rep-nu.proof.Preserve using (shiftReps-∋⁻; wf-same)

------------------------------------------------------------------------
-- 1. Lookups and the name map
------------------------------------------------------------------------

lookupⁿ-map : ∀ (ρ : Renameᵗ) η X
  → lookupⁿ (map ρ η) X ≡ Maybe.map ρ (lookupⁿ η X)
lookupⁿ-map ρ []      X       = refl
lookupⁿ-map ρ (α ∷ η) zero    = refl
lookupⁿ-map ρ (α ∷ η) (suc X) = lookupⁿ-map ρ η X

lookupⁿ-sound : ∀ {η X α} → η ∋ˡ X := α → lookupⁿ η X ≡ just α
lookupⁿ-sound here      = refl
lookupⁿ-sound (there d) = lookupⁿ-sound d

nameσ-live : ∀ {Δ X α} → names Δ ∋ˡ X := α → nameσ Δ X ≡ env (reps Δ) α
nameσ-live {Δ = Ξ ∣ η} {X = X} d = cong (resolve Ξ X) (lookupⁿ-sound d)

private
  resolve-abs : ∀ Ξ X m
    → resolve (abstR ∷ Ξ) (suc X) (Maybe.map suc m) ≡ ⇑ᵗ (resolve Ξ X m)
  resolve-abs Ξ X (just α) = refl
  resolve-abs Ξ X nothing  = refl

  resolve-bind : ∀ Ξ R X m
    → resolve (bindR R ∷ Ξ) X (Maybe.map suc m) ≡ resolve Ξ X m
  resolve-bind Ξ R X (just α) = refl
  resolve-bind Ξ R X nothing  = refl

-- the name map under Λ denotes the extended substitution
nameσ-underΛ : ∀ Δ X → nameσ (underΛ Δ) X ≡ extsᵗ (nameσ Δ) X
nameσ-underΛ (Ξ ∣ η) zero    = refl
nameσ-underΛ (Ξ ∣ η) (suc X) =
  trans (cong (resolve (abstR ∷ Ξ) (suc X)) (lookupⁿ-map suc η X))
        (resolve-abs Ξ X (lookupⁿ η X))

-- an allocation renumbers nothing a name denotes
nameσ-alloc : ∀ R Δ X → nameσ (allocate R Δ) X ≡ nameσ Δ X
nameσ-alloc R (Ξ ∣ η) X =
  trans (cong (resolve (bindR R ∷ Ξ) X) (lookupⁿ-map suc η X))
        (resolve-bind Ξ R X (lookupⁿ η X))

------------------------------------------------------------------------
-- 2. Substitution algebra
------------------------------------------------------------------------

⇑-subst : ∀ (τ : Substᵗ) A
  → substᵗ (λ α → ⇑ᵗ (τ α)) A ≡ ⇑ᵗ (substᵗ τ A)
⇑-subst τ A = sym (rename-subst suc τ A)

exts-⇑ : ∀ (τ : Substᵗ) A → substᵗ (extsᵗ τ) (⇑ᵗ A) ≡ ⇑ᵗ (substᵗ τ A)
exts-⇑ τ A = trans (rename-subst-commute suc (extsᵗ τ) A) (⇑-subst τ A)

single-⇑ : ∀ B A → substᵗ (singleTyEnv B) (⇑ᵗ A) ≡ A
single-⇑ B A =
  trans (rename-subst-commute suc (singleTyEnv B) A) (subst-id A)

-- two substitutions composed, pointwise
subst-∘ : ∀ (σ τ υ : Substᵗ) → (∀ X → υ X ≡ substᵗ τ (σ X))
  → ∀ A → substᵗ υ A ≡ substᵗ τ (substᵗ σ A)
subst-∘ σ τ υ h A = trans (subst-cong h A) (sym (sub-sub σ τ A))

------------------------------------------------------------------------
-- 3. What a stored cell denotes
------------------------------------------------------------------------

-- a concrete cell denotes its (looked-up, hence shifted) payload
env-bind : ∀ {Ξ α b} → Ξ ∋ʳ α := b
  → ∀ R → b ≡ bindR R → env Ξ α ≡ substᵗ (env Ξ) R
env-bind (r-here {b = abstR}) R ()
env-bind (r-here {b = bindR R₀} {Ξ = Ξ}) R refl =
  sym (rename-subst-commute suc (env (bindR R₀ ∷ Ξ)) R₀)
env-bind (r-there {b = abstR} d) R ()
env-bind (r-there {Ξ = Ξ} {b = bindR R₀} {R = R₁} d) R refl =
  trans (env-bind d R₀ refl)
        (sym (rename-subst-commute suc (env (bindR R₁ ∷ Ξ)) R₀))
env-bind (r-there-abst {b = abstR} d) R ()
env-bind (r-there-abst {Ξ = Ξ} {b = bindR R₀} d) R refl =
  trans (cong ⇑ᵗ (env-bind d R₀ refl))
    (trans (sym (⇑-subst (env Ξ) R₀))
           (sym (rename-subst-commute suc (env (abstR ∷ Ξ)) R₀)))

------------------------------------------------------------------------
-- 4. A reading erases through the store
------------------------------------------------------------------------

erase-~gen : ∀ {η A R} (σ τ : Substᵗ)
  → (∀ {X α} → η ∋ˡ X := α → σ X ≡ τ α)
  → η ⊢ A ~ R → substᵗ σ A ≡ substᵗ τ R
erase-~gen σ τ h (same-var d) = h d
erase-~gen σ τ h same-ℕ = refl
erase-~gen σ τ h same-𝔹 = refl
erase-~gen σ τ h (same-⇒ p q) =
  cong₂ _⇒_ (erase-~gen σ τ h p) (erase-~gen σ τ h q)
erase-~gen {η = η} σ τ h (same-∀ p) =
  cong `∀ (erase-~gen (extsᵗ σ) (extsᵗ τ) h′ p)
  where
  h′ : ∀ {X α} → (zero ∷ shiftReps η) ∋ˡ X := α → extsᵗ σ X ≡ extsᵗ τ α
  h′ here = refl
  h′ (there d) with shiftReps-∋⁻ d
  h′ (there d) | α , refl , d′ = cong ⇑ᵗ (h d′)

erase-~ : ∀ {Δ A R} → names Δ ⊢ A ~ R
  → eraseTy Δ A ≡ substᵗ (env (reps Δ)) R
erase-~ {Δ = Δ} p = erase-~gen (nameσ Δ) (env (reps Δ)) (nameσ-live {Δ = Δ}) p

erase-≈ : ∀ {Δ₁ Δ₂ A B} → reps Δ₁ ≡ reps Δ₂ → Δ₁ ⊢ A ≈ B ⊣ Δ₂
  → eraseTy Δ₁ A ≡ eraseTy Δ₂ B
erase-≈ {Δ₁} {Δ₂} eq (R , p , q) =
  trans (erase-~ {Δ = Δ₁} p)
    (trans (cong (λ Ξ → substᵗ (env Ξ) R) eq) (sym (erase-~ {Δ = Δ₂} q)))

-- the lookup square: X denotes what A denotes
erase-lookup : ∀ {Δ X A} → Δ ∋ X := A → eraseTy Δ (` X) ≡ eraseTy Δ A
erase-lookup {Δ = Δ} (α , R , nm , rp , sm) =
  trans (nameσ-live {Δ = Δ} nm)
    (trans (env-bind rp R refl) (sym (erase-~ {Δ = Δ} sm)))

------------------------------------------------------------------------
-- 6 (used by 5). Λ and ⇑
------------------------------------------------------------------------

erase-underΛ : ∀ Δ A → eraseTy (underΛ Δ) A ≡ substᵗ (extsᵗ (nameσ Δ)) A
erase-underΛ Δ A = subst-cong (nameσ-underΛ Δ) A

erase-∀ : ∀ Δ A → eraseTy Δ (`∀ A) ≡ `∀ (eraseTy (underΛ Δ) A)
erase-∀ Δ A = cong `∀ (sym (erase-underΛ Δ A))

erase-⇑ : ∀ Δ A → eraseTy (underΛ Δ) (⇑ᵗ A) ≡ ⇑ᵗ (eraseTy Δ A)
erase-⇑ Δ A = trans (erase-underΛ Δ (⇑ᵗ A)) (exts-⇑ (nameσ Δ) A)

eraseCtx-⤊ : ∀ Δ Γ → eraseCtx (underΛ Δ) (⤊ Γ) ≡ ⤊ (eraseCtx Δ Γ)
eraseCtx-⤊ Δ []      = refl
eraseCtx-⤊ Δ (A ∷ Γ) = cong₂ _∷_ (erase-⇑ Δ A) (eraseCtx-⤊ Δ Γ)

------------------------------------------------------------------------
-- 5. Conversions are erasure-identities
------------------------------------------------------------------------

mutual
  convᵐ-erase : ∀ {Δ g A B} → Δ ⊢ᵐ g ∶ A ⇝ B → eraseTy Δ A ≡ eraseTy Δ B
  convᵐ-erase (conv-id b) = refl
  convᵐ-erase (conv-idv tv) = refl
  convᵐ-erase (conv-fun s c) =
    cong₂ _⇒_ (sym (conv-erase s)) (conv-erase c)
  convᵐ-erase {Δ = Δ} (conv-all {A = A} {B = B} s) =
    trans (erase-∀ Δ A) (trans (cong `∀ (conv-erase s)) (sym (erase-∀ Δ B)))

  convᵀ-erase : ∀ {Δ t A B} → Δ ⊢ᵀ t ∶ A ⇝ B → eraseTy Δ A ≡ eraseTy Δ B
  convᵀ-erase (conv-mid g) = convᵐ-erase g
  convᵀ-erase (conv-seal lk) = sym (erase-lookup lk)
  convᵀ-erase (conv-seal-seq t lk n) =
    trans (convᵀ-erase t) (sym (erase-lookup lk))

  conv-erase : ∀ {Δ c A B} → Δ ⊢ c ∶ A ⇝ B → eraseTy Δ A ≡ eraseTy Δ B
  conv-erase (conv-tail t) = convᵀ-erase t
  conv-erase (conv-unseal lk) = erase-lookup lk
  conv-erase (conv-unseal-seq lk c n m) =
    trans (erase-lookup lk) (conv-erase c)

-- a conversion's endpoints are read at its context
Read : Ctxᵗ → Ty → Set
Read Δ A = ∃[ R ] (names Δ ⊢ A ~ R)

mutual
  convᵐ-scoped : ∀ {Δ g A B} → Δ ⊢ᵐ g ∶ A ⇝ B → Read Δ A × Read Δ B
  convᵐ-scoped (conv-id base-ℕ) = (`ℕ , same-ℕ) , (`ℕ , same-ℕ)
  convᵐ-scoped (conv-id base-𝔹) = (`𝔹 , same-𝔹) , (`𝔹 , same-𝔹)
  convᵐ-scoped (conv-idv (α , d)) = (` α , same-var d) , (` α , same-var d)
  convᵐ-scoped (conv-fun s c) with conv-scoped s | conv-scoped c
  convᵐ-scoped (conv-fun s c) | (R₁ , p₁) , (R₂ , p₂)
                              | (S₁ , q₁) , (S₂ , q₂) =
    (R₂ ⇒ S₁ , same-⇒ p₂ q₁) , (R₁ ⇒ S₂ , same-⇒ p₁ q₂)
  convᵐ-scoped (conv-all s) with conv-scoped s
  convᵐ-scoped (conv-all s) | (R₁ , p₁) , (R₂ , p₂) =
    (`∀ R₁ , same-∀ p₁) , (`∀ R₂ , same-∀ p₂)

  convᵀ-scoped : ∀ {Δ t A B} → Δ ⊢ᵀ t ∶ A ⇝ B → Read Δ A × Read Δ B
  convᵀ-scoped (conv-mid g) = convᵐ-scoped g
  convᵀ-scoped (conv-seal (α , R , nm , rp , sm)) =
    (R , sm) , (` α , same-var nm)
  convᵀ-scoped (conv-seal-seq t (α , R , nm , rp , sm) n)
    with convᵀ-scoped t
  convᵀ-scoped (conv-seal-seq t (α , R , nm , rp , sm) n) | rA , rB =
    rA , (` α , same-var nm)

  conv-scoped : ∀ {Δ c A B} → Δ ⊢ c ∶ A ⇝ B → Read Δ A × Read Δ B
  conv-scoped (conv-tail t) = convᵀ-scoped t
  conv-scoped (conv-unseal (α , R , nm , rp , sm)) =
    (` α , same-var nm) , (R , sm)
  conv-scoped (conv-unseal-seq (α , R , nm , rp , sm) c n m)
    with conv-scoped c
  conv-scoped (conv-unseal-seq (α , R , nm , rp , sm) c n m) | rA , rB =
    (` α , same-var nm) , rB

------------------------------------------------------------------------
-- 7. Scoping
------------------------------------------------------------------------

ren-wfˢ : ∀ {n m A} {ρ : Renameᵗ} → (∀ {X} → X < n → ρ X < m)
  → n ⊢ˢ A → m ⊢ˢ renameᵗ ρ A
ren-wfˢ h (swf-var p) = swf-var (h p)
ren-wfˢ h swf-ℕ = swf-ℕ
ren-wfˢ h swf-𝔹 = swf-𝔹
ren-wfˢ h (swf-⇒ a b) = swf-⇒ (ren-wfˢ h a) (ren-wfˢ h b)
ren-wfˢ {ρ = ρ} h (swf-∀ a) = swf-∀ (ren-wfˢ h′ a)
  where
  h′ : ∀ {X} → X < suc _ → extᵗ ρ X < suc _
  h′ {zero}  p       = s≤s z≤n
  h′ {suc X} (s≤s p) = s≤s (h p)

⇑-wfˢ : ∀ {n A} → n ⊢ˢ A → suc n ⊢ˢ ⇑ᵗ A
⇑-wfˢ = ren-wfˢ s≤s

subst-wfᴿ : ∀ {Ξ k R m} {σ : Substᵗ} → Ξ ⊢ᴿ[ k ] R
  → (∀ {i} → Ξ ⊢ref[ k ] i → m ⊢ˢ σ i)
  → m ⊢ˢ substᵗ σ R
subst-wfᴿ (wfᴿ-var r) h = h r
subst-wfᴿ wfᴿ-ℕ h = swf-ℕ
subst-wfᴿ wfᴿ-𝔹 h = swf-𝔹
subst-wfᴿ (wfᴿ-⇒ r s) h = swf-⇒ (subst-wfᴿ r h) (subst-wfᴿ s h)
subst-wfᴿ {Ξ} {k} {σ = σ} (wfᴿ-∀ r) h = swf-∀ (subst-wfᴿ r h′)
  where
  h′ : ∀ {i} → Ξ ⊢ref[ suc k ] i → suc _ ⊢ˢ extsᵗ σ i
  h′ {zero}  r′                  = swf-var (s≤s z≤n)
  h′ {suc i} (local-ref (s≤s p)) = ⇑-wfˢ (h (local-ref p))
  h′ {suc i} (free-ref d)        = ⇑-wfˢ (h (free-ref d))

env-wf : ∀ {Ξ α b} → WfRepCtx Ξ → Ξ ∋ˡ α := b → srcScope Ξ ⊢ˢ env Ξ α
env-wf (wf-abstR wr) here      = swf-var (s≤s z≤n)
env-wf (wf-abstR wr) (there d) = ⇑-wfˢ (env-wf wr d)
env-wf {Ξ = bindR R ∷ Ξ} (wf-bindR wR wr) here = subst-wfᴿ wR h
  where
  h : ∀ {i} → Ξ ⊢ref[ zero ] i → srcScope Ξ ⊢ˢ env Ξ i
  h (free-ref d) = env-wf wr d
env-wf (wf-bindR wR wr) (there d) = env-wf wr d

erase-wf : ∀ {Δ A} → WfCtx Δ → Δ ⊢ᵗ A → srcScope (reps Δ) ⊢ˢ eraseTy Δ A
erase-wf {Δ} {A} w wA with wf-same wA
erase-wf {Δ} {A} w wA | R , p =
  subst (srcScope (reps Δ) ⊢ˢ_) (sym (erase-~ {Δ = Δ} p))
    (subst-wfᴿ (same-wfᴿ′ p) h)
  where
  h : ∀ {i} → reps Δ ⊢ref[ zero ] i → srcScope (reps Δ) ⊢ˢ env (reps Δ) i
  h (free-ref d) = env-wf (wf-reps w) d
  same-wfᴿ′ : ∀ {A R} → names Δ ⊢ A ~ R → reps Δ ⊢ᴿ R
  same-wfᴿ′ = strong-rep-nu.proof.Preserve.same-wfᴿ w

------------------------------------------------------------------------
-- 8. Source-side helpers
------------------------------------------------------------------------

∋-map : ∀ {f : Ty → Ty} {Γ x A} → Γ ∋ x ⦂ A → map f Γ ∋ x ⦂ f A
∋-map here      = here
∋-map (there d) = there (∋-map d)

∋-++ : ∀ {Γ₀ Γ x A} → Γ₀ ∋ x ⦂ A → (Γ₀ ++ Γ) ∋ x ⦂ A
∋-++ here      = here
∋-++ (there d) = there (∋-++ d)

⊢ˢ-weaken-++ : ∀ {n Γ₀ M A} Γ → n ∣ Γ₀ ⊢ˢ M ⦂ A → n ∣ Γ₀ ++ Γ ⊢ˢ M ⦂ A
⊢ˢ-weaken-++ Γ (⊢ˢ` d) = ⊢ˢ` (∋-++ d)
⊢ˢ-weaken-++ Γ ⊢ˢ$ = ⊢ˢ$
⊢ˢ-weaken-++ Γ ⊢ˢtrue = ⊢ˢtrue
⊢ˢ-weaken-++ Γ ⊢ˢfalse = ⊢ˢfalse
⊢ˢ-weaken-++ Γ (⊢ˢƛ w d) = ⊢ˢƛ w (⊢ˢ-weaken-++ Γ d)
⊢ˢ-weaken-++ Γ (⊢ˢ· d e) = ⊢ˢ· (⊢ˢ-weaken-++ Γ d) (⊢ˢ-weaken-++ Γ e)
⊢ˢ-weaken-++ {n} {Γ₀} {A = `∀ C} Γ (⊢ˢΛ {N = N} v d) =
  ⊢ˢΛ v (subst (λ Γ′ → suc n ∣ Γ′ ⊢ˢ N ⦂ C) (sym (map-++ ⇑ᵗ Γ₀ Γ))
              (⊢ˢ-weaken-++ (⤊ Γ) d))
⊢ˢ-weaken-++ Γ (⊢ˢ[] d w) = ⊢ˢ[] (⊢ˢ-weaken-++ Γ d) w

⊢ˢ-weaken : ∀ {n Γ M A} → n ∣ [] ⊢ˢ M ⦂ A → n ∣ Γ ⊢ˢ M ⦂ A
⊢ˢ-weaken {Γ = Γ} d = ⊢ˢ-weaken-++ Γ d

substˢᵗ-cong : ∀ {σ τ : Substᵗ} → (∀ X → σ X ≡ τ X)
  → ∀ M → substˢᵗ σ M ≡ substˢᵗ τ M
substˢᵗ-cong h (` x)     = refl
substˢᵗ-cong h ($ k)     = refl
substˢᵗ-cong h `true     = refl
substˢᵗ-cong h `false    = refl
substˢᵗ-cong h (ƛ A ∙ N) =
  cong₂ ƛ_∙_ (subst-cong h A) (substˢᵗ-cong h N)
substˢᵗ-cong h (L · M)   = cong₂ _·_ (substˢᵗ-cong h L) (substˢᵗ-cong h M)
substˢᵗ-cong {σ} {τ} h (Λ N) = cong Λ_ (substˢᵗ-cong h-ext N)
  where
  h-ext : ∀ X → extsᵗ σ X ≡ extsᵗ τ X
  h-ext zero    = refl
  h-ext (suc X) = cong ⇑ᵗ (h X)
substˢᵗ-cong h (L [ A ]) = cong₂ _[_] (substˢᵗ-cong h L) (subst-cong h A)

substˢᵗ-id : ∀ {σ : Substᵗ} → (∀ X → σ X ≡ ` X) → ∀ M → substˢᵗ σ M ≡ M
substˢᵗ-id h (` x)     = refl
substˢᵗ-id h ($ k)     = refl
substˢᵗ-id h `true     = refl
substˢᵗ-id h `false    = refl
substˢᵗ-id h (ƛ A ∙ N) =
  cong₂ ƛ_∙_ (trans (subst-cong h A) (subst-id A)) (substˢᵗ-id h N)
substˢᵗ-id h (L · M)   = cong₂ _·_ (substˢᵗ-id h L) (substˢᵗ-id h M)
substˢᵗ-id {σ} h (Λ N) = cong Λ_ (substˢᵗ-id h-ext N)
  where
  h-ext : ∀ X → extsᵗ σ X ≡ ` X
  h-ext zero    = refl
  h-ext (suc X) = cong ⇑ᵗ (h X)
substˢᵗ-id h (L [ A ]) =
  cong₂ _[_] (substˢᵗ-id h L) (trans (subst-cong h A) (subst-id A))

------------------------------------------------------------------------
-- 9. Values erase to values
------------------------------------------------------------------------

mutual
  simple-erase : ∀ {Δ U} → Simple U → SValue (erase Δ U)
  simple-erase S-$     = SV-$
  simple-erase S-true  = SV-true
  simple-erase S-false = SV-false
  simple-erase S-ƛ     = SV-ƛ
  simple-erase (S-Λ v) = SV-Λ (value-erase v)

  value-erase : ∀ {Δ V} → Value V → SValue (erase Δ V)
  value-erase (V-simple u) = simple-erase u
  value-erase (V-⟪⟫ u it)  = simple-erase u

------------------------------------------------------------------------
-- 10. The computed interior IS the relational one
------------------------------------------------------------------------

private
  delete-sound : ∀ {α η X η′} → α ⊢- η at X ⇒ η′ → deleteAt X η ≡ η′
  delete-sound del-here      = refl
  delete-sound (del-there d) = cong (_ ∷_) (delete-sound d)

  insert-sound : ∀ {α η X η′} → α ⊢+ η at X ⇒ η′ → insertAt X α η ≡ η′
  insert-sound ins-here      = refl
  insert-sound (ins-there i) = cong (_ ∷_) (insert-sound i)

  act-sound : ∀ {Ξ η δ η′} → Ξ ∣ η ⊢δ δ ⇒ η′ → act δ η ≡ η′
  act-sound (step-unbind v d f) = delete-sound d
  act-sound (step-bind v f i)   = insert-sound i

  changes-sound : ∀ {Ξ η Θ η′} → Ξ ∣ η ⊢χ Θ ⇒ η′ → interiorⁿ Θ η ≡ η′
  changes-sound changes[] = refl
  changes-sound (changes∷ {δ = δ} cs st) =
    trans (cong (act δ) (changes-sound cs)) (act-sound st)

inside-sound : ∀ {Δ Θ Δᵢ} → Δ ⊢ⁱ Θ ⇒ Δᵢ → inside Δ Θ ≡ Δᵢ
inside-sound (interior cs) = cong (_ ∣_) (changes-sound cs)
