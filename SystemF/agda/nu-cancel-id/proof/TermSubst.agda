module nu-cancel-id.proof.TermSubst where

-- File Charter:
--   * LAWS OF RENAMING AND SUBSTITUTION (nu-cancel-id.TermSubst), and
--     the substitution lemma that types Beta.
--   * §1 congruence: equal environments give equal results.  §2
--     renaming is substitution by `ren`, and `idˢ` is the identity.  §3
--     composition, for environments whose values the second
--     substitution leaves alone (`Fixed`), as a closed value is.  §4
--     single substitution: `substᵐ` at a variable, and under a `Λ`.
--   * §5 typing.  Lookups transport along `map ⇑ᵗ`.  A renaming keeps
--     types, and so does a well-typed environment, whose values are
--     closed.  Under a `Λ` a value is `crossΛ V`, which hides the `Λ`'s
--     cell, so the copy is typed with every name it had: its body by
--     weakening with an unnamed cell, its exterior type `⇑ᵗ A` read with
--     the `Λ`'s name in front.

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)
  renaming (subst to substᵉ)

open import nu-cancel-id.Types
open import nu-cancel-id.Ctx
open import nu-cancel-id.Terms
open import nu-cancel-id.TermSubst
open import nu-cancel-id.proof.Flags
open import nu-cancel-id.proof.Weaken

private
  variable
    Γ : Ctx
    Δ Δ′ : List Ty
    x y : ℕ
    A B R : Ty
    M N V : Term

------------------------------------------------------------------------
-- 1. Congruence
------------------------------------------------------------------------

ext-cong : ∀ {ρ ρ′ : Rename} → (∀ x → ρ x ≡ ρ′ x)
  → ∀ x → ext ρ x ≡ ext ρ′ x
ext-cong h zero    = refl
ext-cong h (suc x) = cong suc (h x)

rename-cong : ∀ {ρ ρ′ : Rename} → (∀ x → ρ x ≡ ρ′ x)
  → ∀ M → rename ρ M ≡ rename ρ′ M
rename-cong h (` x)               = cong `_ (h x)
rename-cong h ($ k)               = refl
rename-cong h (ƛ A ∙ N)           =
  cong (ƛ A ∙_) (rename-cong (ext-cong h) N)
rename-cong h (L · M)             =
  cong₂ _·_ (rename-cong h L) (rename-cong h M)
rename-cong h (Λ N)               = cong Λ_ (rename-cong h N)
rename-cong h (ν A · L ⟨ c ⟩)     =
  cong (λ L′ → ν A · L′ ⟨ c ⟩) (rename-cong h L)
rename-cong h ([ s , α ] M ⟨ c ⟩) = refl

exts-cong : ∀ {σ τ : Subst} → (∀ x → σ x ≡ τ x)
  → ∀ x → exts σ x ≡ exts τ x
exts-cong h zero    = refl
exts-cong h (suc x) = cong shiftˢ (h x)

liftΛ-cong : ∀ {σ τ : Subst} → (∀ x → σ x ≡ τ x)
  → ∀ x → liftΛ σ x ≡ liftΛ τ x
liftΛ-cong h x = cong crossˢ (h x)

subst-cong : ∀ {σ τ : Subst} → (∀ x → σ x ≡ τ x)
  → ∀ M → subst σ M ≡ subst τ M
subst-cong h (` x)               = cong ⌊_⌋ (h x)
subst-cong h ($ k)               = refl
subst-cong h (ƛ A ∙ N)           =
  cong (ƛ A ∙_) (subst-cong (exts-cong h) N)
subst-cong h (L · M)             =
  cong₂ _·_ (subst-cong h L) (subst-cong h M)
subst-cong h (Λ N)               = cong Λ_ (subst-cong (liftΛ-cong h) N)
subst-cong h (ν A · L ⟨ c ⟩)     =
  cong (λ L′ → ν A · L′ ⟨ c ⟩) (subst-cong h L)
subst-cong h ([ s , α ] M ⟨ c ⟩) = refl

------------------------------------------------------------------------
-- 2. Renaming as substitution; the identity
------------------------------------------------------------------------

ren-ext : ∀ ρ x → exts (ren ρ) x ≡ ren (ext ρ) x
ren-ext ρ zero    = refl
ren-ext ρ (suc x) = refl

rename-subst : ∀ ρ M → rename ρ M ≡ subst (ren ρ) M
rename-subst ρ (` x)               = refl
rename-subst ρ ($ k)               = refl
rename-subst ρ (ƛ A ∙ N)           =
  cong (ƛ A ∙_)
    (trans (rename-subst (ext ρ) N)
           (subst-cong (λ x → sym (ren-ext ρ x)) N))
rename-subst ρ (L · M)             =
  cong₂ _·_ (rename-subst ρ L) (rename-subst ρ M)
rename-subst ρ (Λ N)               = cong Λ_ (rename-subst ρ N)
rename-subst ρ (ν A · L ⟨ c ⟩)     =
  cong (λ L′ → ν A · L′ ⟨ c ⟩) (rename-subst ρ L)
rename-subst ρ ([ s , α ] M ⟨ c ⟩) = refl

exts-id : ∀ x → exts idˢ x ≡ idˢ x
exts-id zero    = refl
exts-id (suc x) = refl

sub-id : ∀ M → subst idˢ M ≡ M
sub-id (` x)               = refl
sub-id ($ k)               = refl
sub-id (ƛ A ∙ N)           =
  cong (ƛ A ∙_) (trans (subst-cong exts-id N) (sub-id N))
sub-id (L · M)             = cong₂ _·_ (sub-id L) (sub-id M)
sub-id (Λ N)               = cong Λ_ (sub-id N)
sub-id (ν A · L ⟨ c ⟩)     = cong (λ L′ → ν A · L′ ⟨ c ⟩) (sub-id L)
sub-id ([ s , α ] M ⟨ c ⟩) = refl

------------------------------------------------------------------------
-- 3. Composition
------------------------------------------------------------------------

-- the values of σ are left alone by every substitution
Fixed : Subst → Set
Fixed σ = ∀ x {V} → σ x ≡ val V → ∀ τ → subst τ V ≡ V

exts-⨟ : ∀ σ τ x → (exts σ ⨟ exts τ) x ≡ exts (σ ⨟ τ) x
exts-⨟ σ τ zero = refl
exts-⨟ σ τ (suc x) with σ x
exts-⨟ σ τ (suc x) | var y = refl
exts-⨟ σ τ (suc x) | val V = refl

liftΛ-⨟ : ∀ σ τ x → (liftΛ σ ⨟ liftΛ τ) x ≡ liftΛ (σ ⨟ τ) x
liftΛ-⨟ σ τ x with σ x
liftΛ-⨟ σ τ x | var y = refl
liftΛ-⨟ σ τ x | val V = refl

exts-fixed : ∀ {σ} → Fixed σ → Fixed (exts σ)
exts-fixed fx zero    ()
exts-fixed {σ = σ} fx (suc x) eq with σ x in e
exts-fixed fx (suc x) refl | val V = fx x e

liftΛ-fixed : ∀ {σ} → Fixed σ → Fixed (liftΛ σ)
liftΛ-fixed {σ = σ} fx x eq with σ x
liftΛ-fixed fx x refl | val V = λ τ → refl

sub-sub : ∀ {σ} τ M → Fixed σ
  → subst τ (subst σ M) ≡ subst (σ ⨟ τ) M
sub-sub {σ = σ} τ (` x) fx with σ x in e
sub-sub τ (` x) fx | var y = refl
sub-sub τ (` x) fx | val V = fx x e τ
sub-sub τ ($ k) fx               = refl
sub-sub {σ = σ} τ (ƛ A ∙ N) fx   =
  cong (ƛ A ∙_)
    (trans (sub-sub (exts τ) N (exts-fixed fx))
           (subst-cong (exts-⨟ σ τ) N))
sub-sub τ (L · M) fx             =
  cong₂ _·_ (sub-sub τ L fx) (sub-sub τ M fx)
sub-sub {σ = σ} τ (Λ N) fx       =
  cong Λ_
    (trans (sub-sub (liftΛ τ) N (liftΛ-fixed fx))
           (subst-cong (liftΛ-⨟ σ τ) N))
sub-sub τ (ν A · L ⟨ c ⟩) fx     =
  cong (λ L′ → ν A · L′ ⟨ c ⟩) (sub-sub τ L fx)
sub-sub τ ([ s , α ] M ⟨ c ⟩) fx = refl

------------------------------------------------------------------------
-- 4. Single substitution
------------------------------------------------------------------------

fromHitˢ : Hit → Term → Sub
fromHitˢ hit      V = val V
fromHitˢ (miss y) V = var y

shift-hit : ∀ h V → shiftˢ (fromHitˢ h V) ≡ fromHitˢ (sucHit h) V
shift-hit hit      V = refl
shift-hit (miss y) V = refl

extsⁿ-hit : ∀ j V x → extsⁿ j (V • idˢ) x ≡ fromHitˢ (hitVar x j) V
extsⁿ-hit zero    V zero    = refl
extsⁿ-hit zero    V (suc x) = refl
extsⁿ-hit (suc j) V zero    = refl
extsⁿ-hit (suc j) V (suc x) =
  trans (cong shiftˢ (extsⁿ-hit j V x)) (shift-hit (hitVar x j) V)

substᵐ-var : ∀ j V x → substᵐ j V (` x) ≡ fromHit (hitVar x j) V
substᵐ-var j V x with hitVar x j | extsⁿ-hit j V x
substᵐ-var j V x | hit    | e = cong ⌊_⌋ e
substᵐ-var j V x | miss y | e = cong ⌊_⌋ e

substᵐ-hit : ∀ {j x} V → hitVar x j ≡ hit → substᵐ j V (` x) ≡ V
substᵐ-hit {j} {x} V h =
  trans (substᵐ-var j V x) (cong (λ h′ → fromHit h′ V) h)

liftΛ-extsⁿ : ∀ j V x
  → liftΛ (extsⁿ j (V • idˢ)) x ≡ extsⁿ j (crossΛ V • idˢ) x
liftΛ-extsⁿ j V x =
  trans (cong crossˢ (extsⁿ-hit j V x))
        (trans (cross-hit (hitVar x j)) (sym (extsⁿ-hit j (crossΛ V) x)))
  where
  cross-hit : ∀ h → crossˢ (fromHitˢ h V) ≡ fromHitˢ h (crossΛ V)
  cross-hit hit      = refl
  cross-hit (miss y) = refl

-- under a `Λ`, the substituted value crosses it
substᵐ-Λ : ∀ j V N → substᵐ j V (Λ N) ≡ Λ substᵐ j (crossΛ V) N
substᵐ-Λ j V N = cong Λ_ (subst-cong (liftΛ-extsⁿ j V) N)

------------------------------------------------------------------------
-- 5. Typing
------------------------------------------------------------------------

∋ˣ-map : ∀ {f : Ty → Ty} → Δ ∋ˣ x ⦂ A → map f Δ ∋ˣ x ⦂ f A
∋ˣ-map x-here      = x-here
∋ˣ-map (x-there l) = x-there (∋ˣ-map l)

∋ˣ-map⁻ : ∀ {f : Ty → Ty} Δ → map f Δ ∋ˣ x ⦂ B
  → ∃[ A ] (Δ ∋ˣ x ⦂ A × B ≡ f A)
∋ˣ-map⁻ (A ∷ Δ) x-here      = A , x-here , refl
∋ˣ-map⁻ (A ∷ Δ) (x-there l) with ∋ˣ-map⁻ Δ l
∋ˣ-map⁻ (A ∷ Δ) (x-there l) | C , l′ , eq = C , x-there l′ , eq

-- a renaming from Δ to Δ′
_⦂ʳ_⇒_ : Rename → List Ty → List Ty → Set
ρ ⦂ʳ Δ ⇒ Δ′ = ∀ {x A} → Δ ∋ˣ x ⦂ A → Δ′ ∋ˣ ρ x ⦂ A

⊢ext : ∀ {ρ} → ρ ⦂ʳ Δ ⇒ Δ′ → ext ρ ⦂ʳ (A ∷ Δ) ⇒ (A ∷ Δ′)
⊢ext ⊢ρ x-here      = x-here
⊢ext ⊢ρ (x-there l) = x-there (⊢ρ l)

⊢extΛ : ∀ {ρ} → ρ ⦂ʳ Δ ⇒ Δ′ → ρ ⦂ʳ map ⇑ᵗ Δ ⇒ map ⇑ᵗ Δ′
⊢extΛ {Δ = Δ} ⊢ρ l with ∋ˣ-map⁻ Δ l
⊢extΛ ⊢ρ l | A , l′ , refl = ∋ˣ-map (⊢ρ l′)

⊢rename : ∀ {ρ} → ρ ⦂ʳ Δ ⇒ Δ′ → Γ ∣ Δ ⊢ M ⦂ A → Γ ∣ Δ′ ⊢ rename ρ M ⦂ A
⊢rename ⊢ρ (⊢` l)        = ⊢` (⊢ρ l)
⊢rename ⊢ρ ⊢nat          = ⊢nat
⊢rename ⊢ρ ⊢bool         = ⊢bool
⊢rename ⊢ρ (⊢ƛ sp ⊢N)    = ⊢ƛ sp (⊢rename (⊢ext ⊢ρ) ⊢N)
⊢rename ⊢ρ (⊢· ⊢L ⊢M)    = ⊢· (⊢rename ⊢ρ ⊢L) (⊢rename ⊢ρ ⊢M)
⊢rename ⊢ρ (⊢Λ ⊢N)       = ⊢Λ (⊢rename (⊢extΛ ⊢ρ) ⊢N)
⊢rename ⊢ρ (⊢ν sp ⊢L spC spB ⊢c) = ⊢ν sp (⊢rename ⊢ρ ⊢L) spC spB ⊢c
⊢rename ⊢ρ (⊢[] coh ⊢M spA spB ⊢c) = ⊢[] coh ⊢M spA spB ⊢c

map-++ : ∀ (f : Ty → Ty) (xs ys : List Ty)
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f []       ys = refl
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

∋ˣ-++ : Δ ∋ˣ x ⦂ A → Δ ++ Δ′ ∋ˣ x ⦂ A
∋ˣ-++ x-here      = x-here
∋ˣ-++ (x-there l) = x-there (∋ˣ-++ l)

-- a closed value is typed in any term context
⊢-extend : Γ ∣ Δ ⊢ M ⦂ A → Γ ∣ Δ ++ Δ′ ⊢ M ⦂ A
⊢-extend (⊢` l)         = ⊢` (∋ˣ-++ l)
⊢-extend ⊢nat           = ⊢nat
⊢-extend ⊢bool          = ⊢bool
⊢-extend (⊢ƛ sp ⊢N)     = ⊢ƛ sp (⊢-extend ⊢N)
⊢-extend (⊢· ⊢L ⊢M)     = ⊢· (⊢-extend ⊢L) (⊢-extend ⊢M)
⊢-extend {Δ′ = Δ′} (⊢Λ {Γₜ = Δ} ⊢N) =
  ⊢Λ (substᵉ (λ Θ → _ ∣ Θ ⊢ _ ⦂ _) (sym (map-++ ⇑ᵗ Δ Δ′)) (⊢-extend ⊢N))
⊢-extend (⊢ν sp ⊢L spC spB ⊢c) = ⊢ν sp (⊢-extend ⊢L) spC spB ⊢c
⊢-extend (⊢[] coh ⊢M spA spB ⊢c) = ⊢[] coh ⊢M spA spB ⊢c

-- an entry of type A: a variable of Δ′, or a closed value
data _∣_⊢ˢ_⦂_ : Ctx → List Ty → Sub → Ty → Set where
  ⊢var : Δ′ ∋ˣ y ⦂ A → Γ ∣ Δ′ ⊢ˢ var y ⦂ A
  ⊢val : Γ ∣ [] ⊢ V ⦂ A → flags Γ ⊢ A ⇝ R → Γ ∣ Δ′ ⊢ˢ val V ⦂ A

-- an environment from Δ to Δ′
_∣_⦂ˢ_⇒_ : Ctx → Subst → List Ty → List Ty → Set
Γ ∣ σ ⦂ˢ Δ ⇒ Δ′ = ∀ {x A} → Δ ∋ˣ x ⦂ A → Γ ∣ Δ′ ⊢ˢ σ x ⦂ A

⊢crossΛ : Γ ∣ [] ⊢ V ⦂ A
  → flags Γ ⊢ A ⇝ R
  → underΛ Γ ∣ [] ⊢ crossΛ V ⦂ ⇑ᵗ A
⊢crossΛ ⊢V sp = ⊢[] f-here (ins-⊢ zero ⊢V) (ins-⇝ zero sp) (⇑-⇝ zero sp) c-id

⊢shift : ∀ {e} → Γ ∣ Δ′ ⊢ˢ e ⦂ A → Γ ∣ B ∷ Δ′ ⊢ˢ shiftˢ e ⦂ A
⊢shift (⊢var l)     = ⊢var (x-there l)
⊢shift (⊢val ⊢V sp) = ⊢val ⊢V sp

⊢cross : ∀ {e} → Γ ∣ Δ′ ⊢ˢ e ⦂ A
  → underΛ Γ ∣ map ⇑ᵗ Δ′ ⊢ˢ crossˢ e ⦂ ⇑ᵗ A
⊢cross (⊢var l)     = ⊢var (∋ˣ-map l)
⊢cross (⊢val ⊢V sp) = ⊢val (⊢crossΛ ⊢V sp) (⇑-⇝ zero sp)

⊢exts : ∀ {σ} → Γ ∣ σ ⦂ˢ Δ ⇒ Δ′ → Γ ∣ exts σ ⦂ˢ (A ∷ Δ) ⇒ (A ∷ Δ′)
⊢exts ⊢σ x-here      = ⊢var x-here
⊢exts ⊢σ (x-there l) = ⊢shift (⊢σ l)

⊢liftΛ : ∀ {σ} → Γ ∣ σ ⦂ˢ Δ ⇒ Δ′
  → underΛ Γ ∣ liftΛ σ ⦂ˢ map ⇑ᵗ Δ ⇒ map ⇑ᵗ Δ′
⊢liftΛ {Δ = Δ} ⊢σ l with ∋ˣ-map⁻ Δ l
⊢liftΛ ⊢σ l | A , l′ , refl = ⊢cross (⊢σ l′)

-- the term an entry stands for
⊢⌊⌋ : ∀ {e} → Γ ∣ Δ′ ⊢ˢ e ⦂ A → Γ ∣ Δ′ ⊢ ⌊ e ⌋ ⦂ A
⊢⌊⌋ (⊢var l)     = ⊢` l
⊢⌊⌋ (⊢val ⊢V sp) = ⊢-extend ⊢V

⊢subst : ∀ {σ} → Γ ∣ σ ⦂ˢ Δ ⇒ Δ′ → Γ ∣ Δ ⊢ M ⦂ A
  → Γ ∣ Δ′ ⊢ subst σ M ⦂ A
⊢subst ⊢σ (⊢` l)        = ⊢⌊⌋ (⊢σ l)
⊢subst ⊢σ ⊢nat          = ⊢nat
⊢subst ⊢σ ⊢bool         = ⊢bool
⊢subst ⊢σ (⊢ƛ sp ⊢N)    = ⊢ƛ sp (⊢subst (⊢exts ⊢σ) ⊢N)
⊢subst ⊢σ (⊢· ⊢L ⊢M)    = ⊢· (⊢subst ⊢σ ⊢L) (⊢subst ⊢σ ⊢M)
⊢subst ⊢σ (⊢Λ ⊢N)       = ⊢Λ (⊢subst (⊢liftΛ ⊢σ) ⊢N)
⊢subst ⊢σ (⊢ν sp ⊢L spC spB ⊢c) = ⊢ν sp (⊢subst ⊢σ ⊢L) spC spB ⊢c
⊢subst ⊢σ (⊢[] coh ⊢M spA spB ⊢c) = ⊢[] coh ⊢M spA spB ⊢c

-- Beta
⊢• : Γ ∣ [] ⊢ V ⦂ A → flags Γ ⊢ A ⇝ R → Γ ∣ (V • idˢ) ⦂ˢ (A ∷ Δ) ⇒ Δ
⊢• ⊢V sp x-here      = ⊢val ⊢V sp
⊢• ⊢V sp (x-there l) = ⊢var l

⊢single : Γ ∣ A ∷ [] ⊢ N ⦂ B → Γ ∣ [] ⊢ V ⦂ A → flags Γ ⊢ A ⇝ R
  → Γ ∣ [] ⊢ N [ V ] ⦂ B
⊢single ⊢N ⊢V sp = ⊢subst (⊢• ⊢V sp) ⊢N
