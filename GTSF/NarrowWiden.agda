-- This is based on the cambridge22 notes.

module NarrowWiden where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.Nat using
  (ℕ; _<_; _≤_; _+_; _∸_; zero; suc; z<s; s<s; z≤n; s≤s;
   s≤s⁻¹)
open import Data.Nat.Properties using
  (_≟_; ≤-refl; ≤-trans; +-assoc; +-comm; +-mono-≤; +-monoʳ-≤;
   +-monoˡ-≤; +-suc; m+[n∸m]≡n; m≤m+n; m≤n+m; n≤1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (subst; cong; cong₂; sym; trans)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import Coercions
open import proof.TypeProperties
  using
    ( TyRenameWf
    ; TyRenameWf-ext
    ; TyRenameWf-suc
    ; renameᵗ-ground
    ; renameᵗ-preserves-WfTy
    ; renameᵗ-ext-suc-comm
    ; renameStoreᵗ-ext-suc-comm
    )

------------------------------------------------------------------------
-- Narrowing and Widening
------------------------------------------------------------------------

infix 4 _∣_⊢_∶_⊒_
infix 4 _∣_⊢_∶_⊑_

mutual
  data _∣_⊢_∶_⊒_ : TyCtx → Store → Coercion → Ty → Ty → Set where

    nrw-id : ∀{Δ : TyCtx}{Σ : Store}{A : Ty}{aA : Atom A}
      → WfTy Δ A
       ---------------------
      → Δ ∣ Σ ⊢ id A ∶ A ⊒ A

    nrw-fun : ∀{Δ : TyCtx}{Σ : Store}{A A′ B B′ : Ty}{s t : Coercion}
      → Δ ∣ Σ ⊢ s ∶ A′ ⊑ A
      → Δ ∣ Σ ⊢ t ∶ B ⊒ B′
       ---------------------------------------
      → Δ ∣ Σ ⊢ (s ↦ t) ∶ (A ⇒ B) ⊒ (A′ ⇒ B′)

    nrw-all : ∀{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
      → suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A ⊒ B
       ----------------------------------
      → Δ ∣ Σ ⊢ (`∀ s) ∶ (`∀ A) ⊒ (`∀ B)

    -- ν
    nrw-gen : ∀{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
      → WfTy Δ A
      → suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ ⇑ᵗ A ⊒ B
       ----------------------------------
      → Δ ∣ Σ ⊢ (gen A s) ∶ A ⊒ (`∀ B)

    nrw-untag : ∀{Δ : TyCtx}{Σ : Store}{G B : Ty}{g}
      → WfTy Δ G
      → Ground G
      → Δ ∣ Σ ⊢ g ∶ G ⊒ B
       -----------------------------
      → Δ ∣ Σ ⊢ ((G ？) ︔ g) ∶ ★ ⊒ B

    nrw-untagˢ : ∀{Δ : TyCtx}{Σ : Store}{α : TyVar}{A : Ty}{g}
      → WfTy Δ A
      → (α , A) ∈ Σ
      → Δ ∣ Σ ⊢ g ∶ ★ ⊒ A
       ------------------------------------------------
      → Δ ∣ Σ ⊢ (((＇ α) ？) ︔ id (＇ α)) ∶ ★ ⊒ ＇ α

    -- α♯ 
    nrw-seal : ∀{Δ : TyCtx}{Σ : Store}{α : TyVar}{A A′ : Ty}{s}
      → WfTy Δ A′
      → (α , A′) ∈ Σ
      → Δ ∣ Σ ⊢ s ∶ A ⊒ A′
       ------------------------------------
      → Δ ∣ Σ ⊢ (s ︔ seal A′ α) ∶ A ⊒ (＇ α)


  data _∣_⊢_∶_⊑_ : TyCtx → Store → Coercion → Ty → Ty → Set where

    wid-id : ∀{Δ : TyCtx}{Σ : Store}{A : Ty}{aA : Atom A}
      → WfTy Δ A
       ---------------------
      → Δ ∣ Σ ⊢ id A ∶ A ⊑ A

    wid-fun : ∀{Δ : TyCtx}{Σ : Store}{A A′ B B′ : Ty}{s t : Coercion}
      → Δ ∣ Σ ⊢ s ∶ A′ ⊒ A
      → Δ ∣ Σ ⊢ t ∶ B ⊑ B′
       ---------------------------------------
      → Δ ∣ Σ ⊢ (s ↦ t) ∶ (A ⇒ B) ⊑ (A′ ⇒ B′)

    wid-all : ∀{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
      → suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A ⊑ B
       ----------------------------------
      → Δ ∣ Σ ⊢ (`∀ s) ∶ (`∀ A) ⊑ (`∀ B)

    -- ν̅ 
    wid-inst : ∀{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
      → WfTy Δ B
      → suc Δ ∣ (0 , ★) ∷ ⟰ᵗ Σ ⊢ s ∶ A ⊑ ⇑ᵗ B
       ----------------------------------------
      → Δ ∣ Σ ⊢ (inst B s) ∶ (`∀ A) ⊑ B

    wid-tag : ∀{Δ : TyCtx}{Σ : Store}{A G : Ty}{g : Coercion}
      → WfTy Δ G
      → Ground G
      → Δ ∣ Σ ⊢ g ∶ A ⊑ G
       ----------------------------
      → Δ ∣ Σ ⊢ (g ︔ (G !)) ∶ A ⊑ ★

    wid-tagˢ : ∀{Δ : TyCtx}{Σ : Store}{α : TyVar}{A : Ty}{g}
      → WfTy Δ A
      → (α , A) ∈ Σ
      → Δ ∣ Σ ⊢ g ∶ A ⊑ ★
       ------------------------------------------------
      → Δ ∣ Σ ⊢ (id (＇ α) ︔ ((＇ α) !)) ∶ ＇ α ⊑ ★

    wid-tagˢ-comp : ∀{Δ : TyCtx}{Σ : Store}{α : TyVar}
        {A A′ : Ty}{s g}
      → WfTy Δ A′
      → (α , A′) ∈ Σ
      → Δ ∣ Σ ⊢ s ∶ A ⊑ ＇ α
      → Δ ∣ Σ ⊢ g ∶ A′ ⊑ ★
       -------------------------------------
      → Δ ∣ Σ ⊢ (s ︔ ((＇ α) !)) ∶ A ⊑ ★

    -- α♭
    wid-unseal : ∀{Δ : TyCtx}{Σ : Store}{α : TyVar}{A′ B : Ty}{s : Coercion}
      → WfTy Δ A′
      → (α , A′) ∈ Σ
      → Δ ∣ Σ ⊢ s ∶ A′ ⊑ B
       ---------------------------------------
      → Δ ∣ Σ ⊢ (unseal α A′ ︔ s) ∶ (＇ α) ⊑ B

------------------------------------------------------------------------
-- Narrowing and Widening Grammar
------------------------------------------------------------------------

mutual
  data CrossNarrowing : Coercion → Set where
    cn-id-var : ∀ {α} →
      CrossNarrowing (id (＇ α))

    cn-id-base : ∀ {ι} →
      CrossNarrowing (id (‵ ι))

    cn-fun : ∀ {s t} →
      Widening s →
      Narrowing t →
      CrossNarrowing (s ↦ t)

    cn-all : ∀ {s} →
      Narrowing s →
      CrossNarrowing (`∀ s)

  data Narrowing : Coercion → Set where
    n-cross : ∀ {g} →
      CrossNarrowing g →
      Narrowing g

    n-id★ :
      Narrowing (id ★)

    n-gen : ∀ {A s} →
      Narrowing s →
      Narrowing (gen A s)

    n-untag : ∀ {G g} →
      Ground G →
      CrossNarrowing g →
      Narrowing ((G ？) ︔ g)

    n-seal : ∀ {A α s} →
      Narrowing s →
      Narrowing (s ︔ seal A α)

  data CrossWidening : Coercion → Set where
    cw-id-var : ∀ {α} →
      CrossWidening (id (＇ α))

    cw-id-base : ∀ {ι} →
      CrossWidening (id (‵ ι))

    cw-fun : ∀ {s t} →
      Narrowing s →
      Widening t →
      CrossWidening (s ↦ t)

    cw-all : ∀ {s} →
      Widening s →
      CrossWidening (`∀ s)

  data Widening : Coercion → Set where
    w-cross : ∀ {g} →
      CrossWidening g →
      Widening g

    w-id★ :
      Widening (id ★)

    w-inst : ∀ {B s} →
      Widening s →
      Widening (inst B s)

    w-tag : ∀ {G g} →
      Ground G →
      CrossWidening g →
      Widening (g ︔ (G !))

    w-unseal : ∀ {α A s} →
      Widening s →
      Widening (unseal α A ︔ s)

------------------------------------------------------------------------
-- Well-Typed Mode-Indexed Narrowing and Widening
------------------------------------------------------------------------

infix 4 _∣_∣_⊢_∶_⊒_
infix 4 _∣_∣_⊢_∶_⊑_

_∣_∣_⊢_∶_⊒_ : ModeEnv → TyCtx → Store → Coercion → Ty → Ty → Set
μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B =
  (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × Narrowing c

_∣_∣_⊢_∶_⊑_ : ModeEnv → TyCtx → Store → Coercion → Ty → Ty → Set
μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B =
  (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × Widening c

------------------------------------------------------------------------
-- Coercion composition
------------------------------------------------------------------------

infixr 7 _⨟_

sizeᶜ : Coercion → ℕ
sizeᶜ (id A) = suc zero
sizeᶜ (c ︔ d) = suc (sizeᶜ c + sizeᶜ d)
sizeᶜ (c ↦ d) = suc (sizeᶜ c + sizeᶜ d)
sizeᶜ (`∀ c) = suc (sizeᶜ c)
sizeᶜ (G !) = suc zero
sizeᶜ (G ？) = suc zero
sizeᶜ (seal A α) = suc zero
sizeᶜ (unseal α A) = suc zero
sizeᶜ (gen A c) = suc (sizeᶜ c)
sizeᶜ (inst B c) = suc (sizeᶜ c)

sizeᶜ-renameᶜ : ∀ ρ c → sizeᶜ (renameᶜ ρ c) ≡ sizeᶜ c
sizeᶜ-renameᶜ ρ (id A) = refl
sizeᶜ-renameᶜ ρ (c ︔ d) =
  cong suc (cong₂ _+_ (sizeᶜ-renameᶜ ρ c) (sizeᶜ-renameᶜ ρ d))
sizeᶜ-renameᶜ ρ (c ↦ d) =
  cong suc (cong₂ _+_ (sizeᶜ-renameᶜ ρ c) (sizeᶜ-renameᶜ ρ d))
sizeᶜ-renameᶜ ρ (`∀ c) = cong suc (sizeᶜ-renameᶜ (extᵗ ρ) c)
sizeᶜ-renameᶜ ρ (G !) = refl
sizeᶜ-renameᶜ ρ (G ？) = refl
sizeᶜ-renameᶜ ρ (seal A α) = refl
sizeᶜ-renameᶜ ρ (unseal α A) = refl
sizeᶜ-renameᶜ ρ (gen A c) =
  cong suc (sizeᶜ-renameᶜ (extᵗ ρ) c)
sizeᶜ-renameᶜ ρ (inst B c) =
  cong suc (sizeᶜ-renameᶜ (extᵗ ρ) c)

sizeᶜ-⇑ᶜ : ∀ c → sizeᶜ (⇑ᶜ c) ≡ sizeᶜ c
sizeᶜ-⇑ᶜ = sizeᶜ-renameᶜ suc

≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
≤-step {n = n} m≤n = ≤-trans m≤n (n≤1+n n)

seq-fuel≤ : ∀ a b e → a + b ≤ a + (b + e)
seq-fuel≤ a b e = +-monoʳ-≤ a (m≤m+n b e)

arrow-left-fuel≤ :
  ∀ a b c d → c + a ≤ (a + b) + suc (c + d)
arrow-left-fuel≤ a b c d =
  ≤-trans c+a≤a+c a+c≤target
  where
    c≤target : c ≤ b + suc (c + d)
    c≤target =
      ≤-trans (m≤m+n c d)
        (≤-trans (n≤1+n (c + d)) (m≤n+m (suc (c + d)) b))

    a+c≤target : a + c ≤ (a + b) + suc (c + d)
    a+c≤target =
      subst
        (λ x → a + c ≤ x)
        (sym (+-assoc a b (suc (c + d))))
        (+-monoʳ-≤ a c≤target)

    c+a≤a+c : c + a ≤ a + c
    c+a≤a+c = subst (λ x → c + a ≤ x) (+-comm c a) ≤-refl

arrow-right-fuel≤ :
  ∀ a b c d → b + d ≤ (a + b) + suc (c + d)
arrow-right-fuel≤ a b c d =
  ≤-trans b+d≤b+suc-c+d b+suc-c+d≤target
  where
    d≤suc-c+d : d ≤ suc (c + d)
    d≤suc-c+d = ≤-trans (m≤n+m d c) (n≤1+n (c + d))

    b+d≤b+suc-c+d : b + d ≤ b + suc (c + d)
    b+d≤b+suc-c+d = +-monoʳ-≤ b d≤suc-c+d

    b+suc-c+d≤a+b+suc-c+d :
      b + suc (c + d) ≤ a + (b + suc (c + d))
    b+suc-c+d≤a+b+suc-c+d =
      m≤n+m (b + suc (c + d)) a

    b+suc-c+d≤target :
      b + suc (c + d) ≤ (a + b) + suc (c + d)
    b+suc-c+d≤target =
      subst
        (λ x → b + suc (c + d) ≤ x)
        (sym (+-assoc a b (suc (c + d))))
        b+suc-c+d≤a+b+suc-c+d

left-seq-fuel≤ : ∀ a b e → a + e ≤ (b + a) + e
left-seq-fuel≤ a b e = +-monoˡ-≤ e (m≤n+m a b)

data ComposeView : Coercion → Coercion → Set where
  view-idʳ : ∀ c A → ComposeView c (id A)
  view-genʳ : ∀ c B d → ComposeView c (gen B d)
  view-sealʳ : ∀ c d A α → ComposeView c (d ︔ seal A α)
  view-tagʳ : ∀ c d G → ComposeView c (d ︔ (G !))
  view-idˡ : ∀ A d → ComposeView (id A) d
  view-fun : ∀ c d c′ d′ → ComposeView (c ↦ d) (c′ ↦ d′)
  view-all : ∀ c d → ComposeView (`∀ c) (`∀ d)
  view-gen-all : ∀ A c d → ComposeView (gen A c) (`∀ d)
  view-all-inst : ∀ c B d → ComposeView (`∀ c) (inst B d)
  view-instˡ : ∀ A c d → ComposeView (inst A c) d
  view-untagˡ : ∀ G c d → ComposeView ((G ？) ︔ c) d
  view-unsealˡ : ∀ α A c d → ComposeView (unseal α A ︔ c) d
  view-default : ∀ c d → ComposeView c d

composeView : ∀ c d → ComposeView c d
composeView c (id A) = view-idʳ c A
composeView c (gen B d) = view-genʳ c B d
composeView c (d ︔ seal A α) = view-sealʳ c d A α
composeView c (d ︔ (G !)) = view-tagʳ c d G
composeView (id A) d = view-idˡ A d
composeView (c ↦ d) (c′ ↦ d′) = view-fun c d c′ d′
composeView (`∀ c) (`∀ d) = view-all c d
composeView (gen A c) (`∀ d) = view-gen-all A c d
composeView (`∀ c) (inst B d) = view-all-inst c B d
composeView (inst A c) d = view-instˡ A c d
composeView ((G ？) ︔ c) d = view-untagˡ G c d
composeView (unseal α A ︔ c) d = view-unsealˡ α A c d
composeView c d = view-default c d

composeᶜ : ℕ → Coercion → Coercion → Coercion
composeᶜ zero c d = c ︔ d
composeᶜ (suc n) c d with composeView c d
composeᶜ (suc n) c .(id A) | view-idʳ .c A = c
composeᶜ (suc n) c .(gen B d) | view-genʳ .c B d =
  gen (src c) (composeᶜ n (⇑ᶜ c) d)
composeᶜ (suc n) c .(d ︔ seal A α) | view-sealʳ .c d A α =
  composeᶜ n c d ︔ seal A α
composeᶜ (suc n) c .(d ︔ (G !)) | view-tagʳ .c d G =
  composeᶜ n c d ︔ (G !)
composeᶜ (suc n) .(id A) d | view-idˡ A .d = d
composeᶜ (suc n) .(c ↦ d) .(c′ ↦ d′) | view-fun c d c′ d′ =
  composeᶜ n c′ c ↦ composeᶜ n d d′
composeᶜ (suc n) .(`∀ c) .(`∀ d) | view-all c d =
  `∀ (composeᶜ n c d)
composeᶜ (suc n) .(gen A c) .(`∀ d) | view-gen-all A c d =
  gen A (composeᶜ n c d)
composeᶜ (suc n) .(`∀ c) .(inst B d) | view-all-inst c B d =
  inst B (composeᶜ n c d)
composeᶜ (suc n) .(inst A c) d | view-instˡ A c .d =
  inst (tgt d) (composeᶜ n c (⇑ᶜ d))
composeᶜ (suc n) .((G ？) ︔ c) d | view-untagˡ G c .d =
  (G ？) ︔ composeᶜ n c d
composeᶜ (suc n) .(unseal α A ︔ c) d | view-unsealˡ α A c .d =
  unseal α A ︔ composeᶜ n c d
composeᶜ (suc n) c d | view-default .c .d = c ︔ d

_⨟_ : Coercion → Coercion → Coercion
c ⨟ d = composeᶜ (sizeᶜ c + sizeᶜ d) c d

composeᶜ-idʳ : ∀ n c {A} → composeᶜ (suc n) c (id A) ≡ c
composeᶜ-idʳ n c = refl

⨟-idʳ : ∀ c {A} → c ⨟ id A ≡ c
⨟-idʳ (id A) = refl
⨟-idʳ (c ︔ d) = refl
⨟-idʳ (c ↦ d) = refl
⨟-idʳ (`∀ c) = refl
⨟-idʳ (G !) = refl
⨟-idʳ (G ？) = refl
⨟-idʳ (seal A α) = refl
⨟-idʳ (unseal α A) = refl
⨟-idʳ (gen A c) = refl
⨟-idʳ (inst B c) = refl

composeᶜ-mono :
  ∀ n c d →
  sizeᶜ c + sizeᶜ d ≤ n →
  composeᶜ (suc n) c d ≡ composeᶜ n c d
composeᶜ-mono zero (id A) d ()
composeᶜ-mono zero (c ︔ d) e ()
composeᶜ-mono zero (c ↦ d) e ()
composeᶜ-mono zero (`∀ c) d ()
composeᶜ-mono zero (G !) d ()
composeᶜ-mono zero (G ？) d ()
composeᶜ-mono zero (seal A α) d ()
composeᶜ-mono zero (unseal α A) d ()
composeᶜ-mono zero (gen A c) d ()
composeᶜ-mono zero (inst B c) d ()
composeᶜ-mono (suc n) c d h with composeView c d
composeᶜ-mono (suc n) c .(id A) h | view-idʳ .c A = refl
composeᶜ-mono (suc n) c .(gen B d) h | view-genʳ .c B d
    rewrite +-suc (sizeᶜ c) (sizeᶜ d) =
  cong (gen (src c))
    (composeᶜ-mono n (⇑ᶜ c) d
      (subst (λ m → m + sizeᶜ d ≤ n) (sym (sizeᶜ-⇑ᶜ c))
        (s≤s⁻¹ h)))
composeᶜ-mono (suc n) c .(d ︔ seal A α) h | view-sealʳ .c d A α
    rewrite +-suc (sizeᶜ c) (sizeᶜ d + suc zero) =
  cong (λ q → q ︔ seal A α)
    (composeᶜ-mono n c d
      (≤-trans (seq-fuel≤ (sizeᶜ c) (sizeᶜ d) (suc zero))
        (s≤s⁻¹ h)))
composeᶜ-mono (suc n) c .(d ︔ (G !)) h | view-tagʳ .c d G
    rewrite +-suc (sizeᶜ c) (sizeᶜ d + suc zero) =
  cong (λ q → q ︔ (G !))
    (composeᶜ-mono n c d
      (≤-trans (seq-fuel≤ (sizeᶜ c) (sizeᶜ d) (suc zero))
        (s≤s⁻¹ h)))
composeᶜ-mono (suc n) .(id A) d h | view-idˡ A .d = refl
composeᶜ-mono (suc n) .(c ↦ d) .(c′ ↦ d′) h
    | view-fun c d c′ d′ =
  cong₂ _↦_
    (composeᶜ-mono n c′ c
      (≤-trans
        (arrow-left-fuel≤ (sizeᶜ c) (sizeᶜ d) (sizeᶜ c′) (sizeᶜ d′))
        (s≤s⁻¹ h)))
    (composeᶜ-mono n d d′
      (≤-trans
        (arrow-right-fuel≤ (sizeᶜ c) (sizeᶜ d) (sizeᶜ c′) (sizeᶜ d′))
        (s≤s⁻¹ h)))
composeᶜ-mono (suc n) .(`∀ c) .(`∀ d) h | view-all c d =
  cong `∀
    (composeᶜ-mono n c d
      (≤-trans (+-monoʳ-≤ (sizeᶜ c) (n≤1+n (sizeᶜ d)))
        (s≤s⁻¹ h)))
composeᶜ-mono (suc n) .(gen A c) .(`∀ d) h
    | view-gen-all A c d =
  cong (gen A)
    (composeᶜ-mono n c d
      (≤-trans (+-monoʳ-≤ (sizeᶜ c) (n≤1+n (sizeᶜ d)))
        (s≤s⁻¹ h)))
composeᶜ-mono (suc n) .(`∀ c) .(inst B d) h
    | view-all-inst c B d =
  cong (inst B)
    (composeᶜ-mono n c d
      (≤-trans (+-monoʳ-≤ (sizeᶜ c) (n≤1+n (sizeᶜ d)))
        (s≤s⁻¹ h)))
composeᶜ-mono (suc n) .(inst A c) d h | view-instˡ A c .d =
  cong (inst (tgt d))
    (composeᶜ-mono n c (⇑ᶜ d)
      (subst (λ m → sizeᶜ c + m ≤ n) (sym (sizeᶜ-⇑ᶜ d))
        (s≤s⁻¹ h)))
composeᶜ-mono (suc n) .((G ？) ︔ c) d h | view-untagˡ G c .d =
  cong ((G ？) ︔_)
    (composeᶜ-mono n c d
      (≤-trans (left-seq-fuel≤ (sizeᶜ c) (suc zero) (sizeᶜ d))
        (s≤s⁻¹ h)))
composeᶜ-mono (suc n) .(unseal α A ︔ c) d h
    | view-unsealˡ α A c .d =
  cong (unseal α A ︔_)
    (composeᶜ-mono n c d
      (≤-trans (left-seq-fuel≤ (sizeᶜ c) (suc zero) (sizeᶜ d))
        (s≤s⁻¹ h)))
composeᶜ-mono (suc n) c d h | view-default .c .d = refl

composeᶜ-extra :
  ∀ k c d →
  composeᶜ (k + (sizeᶜ c + sizeᶜ d)) c d ≡ c ⨟ d
composeᶜ-extra zero c d = refl
composeᶜ-extra (suc k) c d =
  trans
    (composeᶜ-mono (k + (sizeᶜ c + sizeᶜ d)) c d
      (m≤n+m (sizeᶜ c + sizeᶜ d) k))
    (composeᶜ-extra k c d)

composeᶜ-sufficient :
  ∀ n c d →
  sizeᶜ c + sizeᶜ d ≤ n →
  composeᶜ n c d ≡ c ⨟ d
composeᶜ-sufficient n c d h =
  subst
    (λ m → composeᶜ m c d ≡ c ⨟ d)
    n≡extra+need
    (composeᶜ-extra (n ∸ need) c d)
  where
    need = sizeᶜ c + sizeᶜ d

    n≡extra+need : (n ∸ need) + need ≡ n
    n≡extra+need =
      trans (+-comm (n ∸ need) need) (m+[n∸m]≡n h)

⨟-genʳ : ∀ c B d → c ⨟ gen B d ≡ gen (src c) (⇑ᶜ c ⨟ d)
⨟-genʳ c B d rewrite +-suc (sizeᶜ c) (sizeᶜ d) =
  cong (gen (src c))
    (composeᶜ-sufficient (sizeᶜ c + sizeᶜ d) (⇑ᶜ c) d
      (subst (λ m → m + sizeᶜ d ≤ sizeᶜ c + sizeᶜ d)
        (sym (sizeᶜ-⇑ᶜ c)) ≤-refl))

⨟-sealʳ :
  ∀ c d A α →
  c ⨟ (d ︔ seal A α) ≡ (c ⨟ d) ︔ seal A α
⨟-sealʳ c d A α rewrite +-suc (sizeᶜ c) (sizeᶜ d + suc zero) =
  cong (λ q → q ︔ seal A α)
    (composeᶜ-sufficient (sizeᶜ c + (sizeᶜ d + suc zero)) c d
      (seq-fuel≤ (sizeᶜ c) (sizeᶜ d) (suc zero)))

⨟-tagʳ :
  ∀ c d G →
  c ⨟ (d ︔ (G !)) ≡ (c ⨟ d) ︔ (G !)
⨟-tagʳ c d G rewrite +-suc (sizeᶜ c) (sizeᶜ d + suc zero) =
  cong (λ q → q ︔ (G !))
    (composeᶜ-sufficient (sizeᶜ c + (sizeᶜ d + suc zero)) c d
      (seq-fuel≤ (sizeᶜ c) (sizeᶜ d) (suc zero)))

⨟-↦ :
  ∀ c d c′ d′ →
  (c ↦ d) ⨟ (c′ ↦ d′) ≡ (c′ ⨟ c) ↦ (d ⨟ d′)
⨟-↦ c d c′ d′ =
  cong₂ _↦_
    (composeᶜ-sufficient
      (sizeᶜ c + sizeᶜ d + sizeᶜ (c′ ↦ d′)) c′ c
      (arrow-left-fuel≤ (sizeᶜ c) (sizeᶜ d) (sizeᶜ c′) (sizeᶜ d′)))
    (composeᶜ-sufficient
      (sizeᶜ c + sizeᶜ d + sizeᶜ (c′ ↦ d′)) d d′
      (arrow-right-fuel≤ (sizeᶜ c) (sizeᶜ d) (sizeᶜ c′) (sizeᶜ d′)))

⨟-∀ : ∀ c d → (`∀ c) ⨟ (`∀ d) ≡ `∀ (c ⨟ d)
⨟-∀ c d =
  cong `∀
    (composeᶜ-sufficient (sizeᶜ c + sizeᶜ (`∀ d)) c d
      (+-monoʳ-≤ (sizeᶜ c) (n≤1+n (sizeᶜ d))))

⨟-gen-∀ : ∀ A c d → gen A c ⨟ (`∀ d) ≡ gen A (c ⨟ d)
⨟-gen-∀ A c d =
  cong (gen A)
    (composeᶜ-sufficient (sizeᶜ c + sizeᶜ (`∀ d)) c d
      (+-monoʳ-≤ (sizeᶜ c) (n≤1+n (sizeᶜ d))))

⨟-∀-inst : ∀ c B d → (`∀ c) ⨟ inst B d ≡ inst B (c ⨟ d)
⨟-∀-inst c B d =
  cong (inst B)
    (composeᶜ-sufficient (sizeᶜ c + sizeᶜ (inst B d)) c d
      (+-monoʳ-≤ (sizeᶜ c) (n≤1+n (sizeᶜ d))))


------------------------------------------------------------------------
-- Context widening
------------------------------------------------------------------------

-- σ,π  ::=  ∅ | σ, α:=p | σ, α:=A | σ, α:=☆

data StWid : Set where
  _꞉_ : TyVar → Coercion → StWid
  _꞉=_⊑ : TyVar → Ty → StWid
  ⊑_꞉=☆ : TyVar → StWid

StoreWid : Set
StoreWid = List StWid

⇑ʷ : StWid → StWid
⇑ʷ (X ꞉ p) = suc X ꞉ ⇑ᶜ p
⇑ʷ (X ꞉= A ⊑) = suc X ꞉= ⇑ᵗ A ⊑
⇑ʷ (⊑ X ꞉=☆) = ⊑ suc X ꞉=☆

⇑ˢ : StoreWid → StoreWid
⇑ˢ = map ⇑ʷ

-- σ ꞉ Σ ⊑ Σ′

data _⊢_꞉_⊑ˢ_ : TyCtx → StoreWid → Store → Store → Set where
  ⊑ˢ-nil : ∀{Δ}
     ------------------
    → Δ ⊢ [] ꞉ [] ⊑ˢ []
  
  ⊑ˢ-left : ∀{Δ}{Σ Σ′}{A : Ty}{X : TyVar}{σ}
    → WfTy Δ A
    → Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′
     -----------------------------------------
    → Δ ⊢ (X ꞉= A ⊑ ∷ σ) ꞉ ((X , A) ∷ Σ) ⊑ˢ Σ′

  ⊑ˢ-right : ∀{Δ}{Σ Σ′}{X : TyVar}{σ}
    → Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′
     ---------------------------------------
    → Δ ⊢ (⊑ X ꞉=☆ ∷ σ) ꞉ Σ ⊑ˢ ((X , ★) ∷ Σ′)
    
  ⊑ˢ-both : ∀{Δ}{Σ Σ′}{s}{A A′ : Ty}{X : TyVar}{σ}
    → WfTy Δ A
    → WfTy Δ A′
    → Δ ∣ Σ ⊢ s ∶ A ⊑ A′
    → Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′
     ---------------------------------------------------
    → Δ ⊢ (X ꞉ s ∷ σ) ꞉ ((X , A) ∷ Σ) ⊑ˢ ((X , A′) ∷ Σ′)
    

-- γ

CtxWid : Set
CtxWid = List Coercion

-- Γ ⊑ Γ′

data _∣_⊢_꞉_⊑ᵍ_ : TyCtx → Store → CtxWid → Ctx → Ctx → Set where
  ⊑ᵍ-nil : ∀{Δ}{Σ} → Δ ∣ Σ ⊢ [] ꞉ [] ⊑ᵍ []
  
  ⊑ᵍ-cons : ∀{Δ}{Σ}{γ : CtxWid}{Γ Γ′ : Ctx}{s}{A B : Ty}
    → Δ ∣ Σ ⊢ s ∶ A ⊑ B
    → Δ ∣ Σ ⊢ γ ꞉ Γ ⊑ᵍ Γ′
     -------------------------------------
    → Δ ∣ Σ ⊢ (s ∷ γ)꞉ (A ∷ Γ) ⊑ᵍ (B ∷ Γ′)


------------------------------------------------------------------------
-- Narrowing and Widening Equivalence
------------------------------------------------------------------------

private
  renameᵗ-atom :
    ∀ ρ {A} →
    Atom A →
    Atom (renameᵗ ρ A)
  renameᵗ-atom ρ (＇ α) = ＇ (ρ α)
  renameᵗ-atom ρ (‵ ι) = ‵ ι
  renameᵗ-atom ρ ★ = ★

  ∈-renameStoreᵗ :
    ∀ ρ {Σ α A} →
    (α , A) ∈ Σ →
    (ρ α , renameᵗ ρ A) ∈ renameStoreᵗ ρ Σ
  ∈-renameStoreᵗ ρ (here refl) = here refl
  ∈-renameStoreᵗ ρ (there x∈) = there (∈-renameStoreᵗ ρ x∈)

  mutual
    narrow-renameᵗ :
      ∀ {Δ Δ′ Σ A B c ρ} →
      TyRenameWf Δ Δ′ ρ →
      Δ ∣ Σ ⊢ c ∶ A ⊒ B →
      Δ′ ∣ renameStoreᵗ ρ Σ
        ⊢ renameᶜ ρ c ∶ renameᵗ ρ A ⊒ renameᵗ ρ B
    narrow-renameᵗ hρ (nrw-id {aA = aA} hA) =
      nrw-id {aA = renameᵗ-atom _ aA}
        (renameᵗ-preserves-WfTy hA hρ)
    narrow-renameᵗ hρ (nrw-fun s t) =
      nrw-fun (widen-renameᵗ hρ s) (narrow-renameᵗ hρ t)
    narrow-renameᵗ {Δ′ = Δ′} {Σ = Σ} {ρ = ρ} hρ (nrw-all s) =
      nrw-all
        (subst
          (λ Σ′ → suc Δ′ ∣ Σ′
            ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊒ _)
          (renameStoreᵗ-ext-suc-comm ρ Σ)
          (narrow-renameᵗ (TyRenameWf-ext hρ) s))
    narrow-renameᵗ {Δ′ = Δ′} {Σ = Σ} {A = A} {ρ = ρ}
        hρ (nrw-gen hA s) =
      nrw-gen
        (renameᵗ-preserves-WfTy hA hρ)
        (subst
          (λ T → suc Δ′ ∣ ⟰ᵗ (renameStoreᵗ ρ Σ)
            ⊢ renameᶜ (extᵗ ρ) _ ∶ T ⊒ _)
          (renameᵗ-ext-suc-comm ρ A)
          (subst
            (λ Σ′ → suc Δ′ ∣ Σ′
              ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊒ _)
            (renameStoreᵗ-ext-suc-comm ρ Σ)
            (narrow-renameᵗ (TyRenameWf-ext hρ) s)))
    narrow-renameᵗ hρ (nrw-untag hG gG s) =
      nrw-untag
        (renameᵗ-preserves-WfTy hG hρ)
        (renameᵗ-ground _ gG)
        (narrow-renameᵗ hρ s)
    narrow-renameᵗ hρ (nrw-untagˢ hA α∈Σ s) =
      nrw-untagˢ
        (renameᵗ-preserves-WfTy hA hρ)
        (∈-renameStoreᵗ _ α∈Σ)
        (narrow-renameᵗ hρ s)
    narrow-renameᵗ hρ (nrw-seal hA′ α∈Σ s) =
      nrw-seal
        (renameᵗ-preserves-WfTy hA′ hρ)
        (∈-renameStoreᵗ _ α∈Σ)
        (narrow-renameᵗ hρ s)

    widen-renameᵗ :
      ∀ {Δ Δ′ Σ A B c ρ} →
      TyRenameWf Δ Δ′ ρ →
      Δ ∣ Σ ⊢ c ∶ A ⊑ B →
      Δ′ ∣ renameStoreᵗ ρ Σ
        ⊢ renameᶜ ρ c ∶ renameᵗ ρ A ⊑ renameᵗ ρ B
    widen-renameᵗ hρ (wid-id {aA = aA} hA) =
      wid-id {aA = renameᵗ-atom _ aA}
        (renameᵗ-preserves-WfTy hA hρ)
    widen-renameᵗ hρ (wid-fun s t) =
      wid-fun (narrow-renameᵗ hρ s) (widen-renameᵗ hρ t)
    widen-renameᵗ {Δ′ = Δ′} {Σ = Σ} {ρ = ρ} hρ (wid-all s) =
      wid-all
        (subst
          (λ Σ′ → suc Δ′ ∣ Σ′
            ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊑ _)
          (renameStoreᵗ-ext-suc-comm ρ Σ)
          (widen-renameᵗ (TyRenameWf-ext hρ) s))
    widen-renameᵗ {Δ′ = Δ′} {Σ = Σ} {B = B} {ρ = ρ}
        hρ (wid-inst hB s) =
      wid-inst
        (renameᵗ-preserves-WfTy hB hρ)
        (subst
          (λ T → suc Δ′
            ∣ (zero , ★) ∷ ⟰ᵗ (renameStoreᵗ ρ Σ)
            ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊑ T)
          (renameᵗ-ext-suc-comm ρ B)
          (subst
            (λ Σ′ → suc Δ′ ∣ (zero , ★) ∷ Σ′
              ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊑ _)
            (renameStoreᵗ-ext-suc-comm ρ Σ)
            (widen-renameᵗ (TyRenameWf-ext hρ) s)))
    widen-renameᵗ hρ (wid-tag hG gG s) =
      wid-tag
        (renameᵗ-preserves-WfTy hG hρ)
        (renameᵗ-ground _ gG)
        (widen-renameᵗ hρ s)
    widen-renameᵗ hρ (wid-tagˢ hA α∈Σ s) =
      wid-tagˢ
        (renameᵗ-preserves-WfTy hA hρ)
        (∈-renameStoreᵗ _ α∈Σ)
        (widen-renameᵗ hρ s)
    widen-renameᵗ hρ (wid-tagˢ-comp hA α∈Σ s t) =
      wid-tagˢ-comp
        (renameᵗ-preserves-WfTy hA hρ)
        (∈-renameStoreᵗ _ α∈Σ)
        (widen-renameᵗ hρ s)
        (widen-renameᵗ hρ t)
    widen-renameᵗ hρ (wid-unseal hA′ α∈Σ s) =
      wid-unseal
        (renameᵗ-preserves-WfTy hA′ hρ)
        (∈-renameStoreᵗ _ α∈Σ)
        (widen-renameᵗ hρ s)

  narrow-⇑ᵗ :
    ∀ {Δ Σ A B c} →
    Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    suc Δ ∣ ⟰ᵗ Σ ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊒ ⇑ᵗ B
  narrow-⇑ᵗ = narrow-renameᵗ TyRenameWf-suc

  widen-⇑ᵗ :
    ∀ {Δ Σ A B c} →
    Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    suc Δ ∣ ⟰ᵗ Σ ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊑ ⇑ᵗ B
  widen-⇑ᵗ = widen-renameᵗ TyRenameWf-suc

  StoreWid-⇑ˢ :
    ∀ {Δ σ Σ Σ′} →
    Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′ →
    suc Δ ⊢ ⇑ˢ σ ꞉ ⟰ᵗ Σ ⊑ˢ ⟰ᵗ Σ′
  StoreWid-⇑ˢ ⊑ˢ-nil = ⊑ˢ-nil
  StoreWid-⇑ˢ (⊑ˢ-left hA σ⊢) =
    ⊑ˢ-left (renameᵗ-preserves-WfTy hA TyRenameWf-suc)
      (StoreWid-⇑ˢ σ⊢)
  StoreWid-⇑ˢ (⊑ˢ-right σ⊢) =
    ⊑ˢ-right (StoreWid-⇑ˢ σ⊢)
  StoreWid-⇑ˢ (⊑ˢ-both hA hA′ s⊢ σ⊢) =
    ⊑ˢ-both
      (renameᵗ-preserves-WfTy hA TyRenameWf-suc)
      (renameᵗ-preserves-WfTy hA′ TyRenameWf-suc)
      (widen-⇑ᵗ s⊢)
      (StoreWid-⇑ˢ σ⊢)

  StoreWid-id∈ :
    ∀ {Δ σ Σ Σ′ α A} →
    Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′ →
    (α ꞉ id A) ∈ σ →
    (α , A) ∈ Σ × (α , A) ∈ Σ′
  StoreWid-id∈ ⊑ˢ-nil ()
  StoreWid-id∈ (⊑ˢ-left hA σ⊢) (there α∈σ)
      with StoreWid-id∈ σ⊢ α∈σ
  StoreWid-id∈ (⊑ˢ-left hA σ⊢) (there α∈σ)
      | α∈Σ , α∈Σ′ =
    there α∈Σ , α∈Σ′
  StoreWid-id∈ (⊑ˢ-right σ⊢) (there α∈σ)
      with StoreWid-id∈ σ⊢ α∈σ
  StoreWid-id∈ (⊑ˢ-right σ⊢) (there α∈σ)
      | α∈Σ , α∈Σ′ =
    α∈Σ , there α∈Σ′
  StoreWid-id∈ (⊑ˢ-both hA hA′ (wid-id hA₁) σ⊢) (here refl) =
    here refl , here refl
  StoreWid-id∈ (⊑ˢ-both hA hA′ s⊢ σ⊢) (there α∈σ)
      with StoreWid-id∈ σ⊢ α∈σ
  StoreWid-id∈ (⊑ˢ-both hA hA′ s⊢ σ⊢) (there α∈σ)
      | α∈Σ , α∈Σ′ =
    there α∈Σ , there α∈Σ′

infix 4 _⊨_≈id_

data _⊨_≈id_ : StoreWid → TyVar → Ty → Set where
  ≈id-id : ∀{σ α A}
    → (α ꞉ id A) ∈ σ
      ----------------
    → σ ⊨ α ≈id A

  ≈id-exact : ∀{σ α A}
    → (α ꞉= A ⊑) ∈ σ
      ----------------
    → σ ⊨ α ≈id A

infix 4 _∣_⊢_≈_∶_⊒_
infix 4 _∣_⊢_≈_∶_⊑_

mutual
  data _∣_⊢_≈_∶_⊒_ :
      TyCtx → StoreWid → Coercion → Coercion → Ty → Ty → Set where

    id≈idⁿ : ∀{Δ σ A}{aA : Atom A}
      → WfTy Δ A
       -------------------------------
      → Δ ∣ σ ⊢ id A ≈ id A ∶ A ⊒ A

    ↦≈↦ⁿ : ∀{Δ σ A A′ B B′ s t s′ t′}
      → Δ ∣ σ ⊢ s ≈ s′ ∶ A′ ⊑ A
      → Δ ∣ σ ⊢ t ≈ t′ ∶ B ⊒ B′
       -------------------------------------------------
      → Δ ∣ σ ⊢ (s ↦ t) ≈ (s′ ↦ t′) ∶ (A ⇒ B) ⊒ (A′ ⇒ B′)

    ∀≈∀ⁿ : ∀{Δ σ A B s t}
      → suc Δ ∣ ⇑ˢ σ ⊢ s ≈ t ∶ A ⊒ B
       ------------------------------------------------
      → Δ ∣ σ ⊢ (`∀ s) ≈ (`∀ t) ∶ (`∀ A) ⊒ (`∀ B)

    ν≈νⁿ : ∀{Δ σ A B s t}
      → WfTy Δ A
      → suc Δ ∣ ⇑ˢ σ ⊢ s ≈ t ∶ ⇑ᵗ A ⊒ B
       ------------------------------------------------
      → Δ ∣ σ ⊢ gen A s ≈ gen A t ∶ A ⊒ (`∀ B)

    ?≈?ⁿ : ∀{Δ σ G B s t}
      → WfTy Δ G
      → Ground G
      → Δ ∣ σ ⊢ s ≈ t ∶ G ⊒ B
       ------------------------------------------------
      → Δ ∣ σ ⊢ ((G ？) ︔ s) ≈ ((G ？) ︔ t) ∶ ★ ⊒ B

    ?≈seal★ⁿ : ∀{Δ σ α}
      → (α ꞉ id ★) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (((＇ α) ？) ︔ id (＇ α))
          ≈ (id ★ ︔ seal ★ α) ∶ ★ ⊒ ＇ α

    seal★≈?ⁿ : ∀{Δ σ α}
      → (α ꞉ id ★) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (id ★ ︔ seal ★ α)
          ≈ (((＇ α) ？) ︔ id (＇ α)) ∶ ★ ⊒ ＇ α

    ?≈sealGⁿ : ∀{Δ σ α G}{aG : Atom G}
      → WfTy Δ G
      → Ground G
      → (α ꞉ id G) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (((＇ α) ？) ︔ id (＇ α))
          ≈ (((G ？) ︔ id G) ︔ seal G α) ∶ ★ ⊒ ＇ α

    sealG≈?ⁿ : ∀{Δ σ α G}{aG : Atom G}
      → WfTy Δ G
      → Ground G
      → (α ꞉ id G) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (((G ？) ︔ id G) ︔ seal G α)
          ≈ (((＇ α) ？) ︔ id (＇ α)) ∶ ★ ⊒ ＇ α

  data _∣_⊢_≈_∶_⊑_ :
      TyCtx → StoreWid → Coercion → Coercion → Ty → Ty → Set where

    id≈id : ∀{Δ σ A}{aA : Atom A}
      → WfTy Δ A
       ------------------------------
      → Δ ∣ σ ⊢ id A ≈ id A ∶ A ⊑ A

    !≈! : ∀{Δ σ A G g g′}
      → WfTy Δ G
      → Ground G
      → Δ ∣ σ ⊢ g ≈ g′ ∶ A ⊑ G
       ------------------------------------------------
      → Δ ∣ σ ⊢ (g ︔ (G !)) ≈ (g′ ︔ (G !)) ∶ A ⊑ ★

    !≈unseal★ : ∀{Δ σ α}
      → (α ꞉ id ★) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (id (＇ α) ︔ ((＇ α) !))
          ≈ (unseal α ★ ︔ id ★) ∶ ＇ α ⊑ ★

    unseal★≈! : ∀{Δ σ α}
      → (α ꞉ id ★) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (unseal α ★ ︔ id ★)
          ≈ (id (＇ α) ︔ ((＇ α) !)) ∶ ＇ α ⊑ ★

    !≈unsealG : ∀{Δ σ α G}{aG : Atom G}
      → WfTy Δ G
      → Ground G
      → (α ꞉ id G) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (id (＇ α) ︔ ((＇ α) !))
          ≈ ((unseal α G ︔ id G) ︔ (G !)) ∶ ＇ α ⊑ ★

    unsealG≈! : ∀{Δ σ α G}{aG : Atom G}
      → WfTy Δ G
      → Ground G
      → (α ꞉ id G) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ ((unseal α G ︔ id G) ︔ (G !))
          ≈ (id (＇ α) ︔ ((＇ α) !)) ∶ ＇ α ⊑ ★

    ↦≈↦ : ∀{Δ σ A A′ B B′ s t s′ t′}
      → Δ ∣ σ ⊢ s ≈ s′ ∶ A′ ⊒ A
      → Δ ∣ σ ⊢ t ≈ t′ ∶ B ⊑ B′
       ------------------------------------------------
      → Δ ∣ σ ⊢ (s ↦ t) ≈ (s′ ↦ t′) ∶ (A ⇒ B) ⊑ (A′ ⇒ B′)

    ∀≈∀ : ∀{Δ σ A B s t}
      → suc Δ ∣ ⇑ˢ σ ⊢ s ≈ t ∶ A ⊑ B
       -----------------------------------------------
      → Δ ∣ σ ⊢ (`∀ s) ≈ (`∀ t) ∶ (`∀ A) ⊑ (`∀ B)

    ν≈ν : ∀{Δ σ A B s t}
      → WfTy Δ B
      → suc Δ ∣ (0 ꞉ id ★) ∷ ⇑ˢ σ ⊢ s ≈ t ∶ A ⊑ ⇑ᵗ B
       ------------------------------------------------
      → Δ ∣ σ ⊢ inst B s ≈ inst B t ∶ (`∀ A) ⊑ B

mutual
  ≈ⁿ-sound :
    ∀{Δ}{σ : StoreWid}{Σ Σ′ : Store}{s t : Coercion}{A B : Ty}
    → Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′
    → Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B
    → Δ ∣ Σ ⊢ s ∶ A ⊒ B × Δ ∣ Σ′ ⊢ t ∶ A ⊒ B
  ≈ⁿ-sound σ⊢ (id≈idⁿ {aA = aA} hA) =
    nrw-id {aA = aA} hA , nrw-id {aA = aA} hA
  ≈ⁿ-sound σ⊢ (↦≈↦ⁿ s≈ t≈) with ≈-sound σ⊢ s≈ | ≈ⁿ-sound σ⊢ t≈
  ≈ⁿ-sound σ⊢ (↦≈↦ⁿ s≈ t≈) | s⊢ , s′⊢ | t⊢ , t′⊢ =
    nrw-fun s⊢ t⊢ , nrw-fun s′⊢ t′⊢
  ≈ⁿ-sound σ⊢ (∀≈∀ⁿ s≈) with ≈ⁿ-sound (StoreWid-⇑ˢ σ⊢) s≈
  ≈ⁿ-sound σ⊢ (∀≈∀ⁿ s≈) | s⊢ , t⊢ =
    nrw-all s⊢ , nrw-all t⊢
  ≈ⁿ-sound σ⊢ (ν≈νⁿ hA s≈) with ≈ⁿ-sound (StoreWid-⇑ˢ σ⊢) s≈
  ≈ⁿ-sound σ⊢ (ν≈νⁿ hA s≈) | s⊢ , t⊢ =
    nrw-gen hA s⊢ , nrw-gen hA t⊢
  ≈ⁿ-sound σ⊢ (?≈?ⁿ hG gG s≈) with ≈ⁿ-sound σ⊢ s≈
  ≈ⁿ-sound σ⊢ (?≈?ⁿ hG gG s≈) | s⊢ , t⊢ =
    nrw-untag hG gG s⊢ , nrw-untag hG gG t⊢
  ≈ⁿ-sound σ⊢ (?≈seal★ⁿ α∈σ) with StoreWid-id∈ σ⊢ α∈σ
  ≈ⁿ-sound σ⊢ (?≈seal★ⁿ α∈σ) | α∈Σ , α∈Σ′ =
    nrw-untagˢ wf★ α∈Σ (nrw-id {aA = ★} wf★) ,
    nrw-seal wf★ α∈Σ′ (nrw-id {aA = ★} wf★)
  ≈ⁿ-sound σ⊢ (seal★≈?ⁿ α∈σ) with StoreWid-id∈ σ⊢ α∈σ
  ≈ⁿ-sound σ⊢ (seal★≈?ⁿ α∈σ) | α∈Σ , α∈Σ′ =
    nrw-seal wf★ α∈Σ (nrw-id {aA = ★} wf★) ,
    nrw-untagˢ wf★ α∈Σ′ (nrw-id {aA = ★} wf★)
  ≈ⁿ-sound σ⊢ (?≈sealGⁿ hG gG α∈σ) with StoreWid-id∈ σ⊢ α∈σ
  ≈ⁿ-sound σ⊢ (?≈sealGⁿ {aG = aG} hG gG α∈σ) | α∈Σ , α∈Σ′ =
    nrw-untagˢ hG α∈Σ
      (nrw-untag hG gG (nrw-id {aA = aG} hG)) ,
    nrw-seal hG α∈Σ′
      (nrw-untag hG gG (nrw-id {aA = aG} hG))
  ≈ⁿ-sound σ⊢ (sealG≈?ⁿ hG gG α∈σ) with StoreWid-id∈ σ⊢ α∈σ
  ≈ⁿ-sound σ⊢ (sealG≈?ⁿ {aG = aG} hG gG α∈σ) | α∈Σ , α∈Σ′ =
    nrw-seal hG α∈Σ
      (nrw-untag hG gG (nrw-id {aA = aG} hG)) ,
    nrw-untagˢ hG α∈Σ′
      (nrw-untag hG gG (nrw-id {aA = aG} hG))

  ≈-sound :
    ∀{Δ}{σ : StoreWid}{Σ Σ′ : Store}{s t : Coercion}{A B : Ty}
    → Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′
    → Δ ∣ σ ⊢ s ≈ t ∶ A ⊑ B
    → Δ ∣ Σ ⊢ s ∶ A ⊑ B × Δ ∣ Σ′ ⊢ t ∶ A ⊑ B
  ≈-sound σ⊢ (id≈id {aA = aA} hA) =
    wid-id {aA = aA} hA , wid-id {aA = aA} hA
  ≈-sound σ⊢ (!≈! hG gG g≈) with ≈-sound σ⊢ g≈
  ≈-sound σ⊢ (!≈! hG gG g≈) | g⊢ , g′⊢ =
    wid-tag hG gG g⊢ , wid-tag hG gG g′⊢
  ≈-sound σ⊢ (!≈unseal★ α∈σ) with StoreWid-id∈ σ⊢ α∈σ
  ≈-sound σ⊢ (!≈unseal★ α∈σ) | α∈Σ , α∈Σ′ =
    wid-tagˢ wf★ α∈Σ (wid-id {aA = ★} wf★) ,
    wid-unseal wf★ α∈Σ′ (wid-id {aA = ★} wf★)
  ≈-sound σ⊢ (unseal★≈! α∈σ) with StoreWid-id∈ σ⊢ α∈σ
  ≈-sound σ⊢ (unseal★≈! α∈σ) | α∈Σ , α∈Σ′ =
    wid-unseal wf★ α∈Σ (wid-id {aA = ★} wf★) ,
    wid-tagˢ wf★ α∈Σ′ (wid-id {aA = ★} wf★)
  ≈-sound σ⊢ (!≈unsealG hG gG α∈σ) with StoreWid-id∈ σ⊢ α∈σ
  ≈-sound σ⊢ (!≈unsealG {aG = aG} hG gG α∈σ) | α∈Σ , α∈Σ′ =
    wid-tagˢ hG α∈Σ (wid-tag hG gG (wid-id {aA = aG} hG)) ,
    wid-tag hG gG (wid-unseal hG α∈Σ′ (wid-id {aA = aG} hG))
  ≈-sound σ⊢ (unsealG≈! hG gG α∈σ) with StoreWid-id∈ σ⊢ α∈σ
  ≈-sound σ⊢ (unsealG≈! {aG = aG} hG gG α∈σ) | α∈Σ , α∈Σ′ =
    wid-tag hG gG (wid-unseal hG α∈Σ (wid-id {aA = aG} hG)) ,
    wid-tagˢ hG α∈Σ′ (wid-tag hG gG (wid-id {aA = aG} hG))
  ≈-sound σ⊢ (↦≈↦ s≈ t≈) with ≈ⁿ-sound σ⊢ s≈ | ≈-sound σ⊢ t≈
  ≈-sound σ⊢ (↦≈↦ s≈ t≈) | s⊢ , s′⊢ | t⊢ , t′⊢ =
    wid-fun s⊢ t⊢ , wid-fun s′⊢ t′⊢
  ≈-sound σ⊢ (∀≈∀ s≈) with ≈-sound (StoreWid-⇑ˢ σ⊢) s≈
  ≈-sound σ⊢ (∀≈∀ s≈) | s⊢ , t⊢ =
    wid-all s⊢ , wid-all t⊢
  ≈-sound σ⊢ (ν≈ν hB s≈)
      with ≈-sound
        (⊑ˢ-both wf★ wf★ (wid-id {aA = ★} wf★) (StoreWid-⇑ˢ σ⊢))
        s≈
  ≈-sound σ⊢ (ν≈ν hB s≈) | s⊢ , t⊢ =
    wid-inst hB s⊢ , wid-inst hB t⊢

≈-sanity : ∀{Δ}{σ : StoreWid}{Σ Σ′ : Store}{s t : Coercion}{A B : Ty}
  → Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′
  → Δ ∣ σ ⊢ s ≈ t ∶ A ⊑ B
  → ∃[ A ] ∃[ B ] Δ ∣ Σ ⊢ s ∶ A ⊑ B × Δ ∣ Σ′ ⊢ t ∶ A ⊑ B
≈-sanity σ⊢ s≈ with ≈-sound σ⊢ s≈
≈-sanity σ⊢ s≈ | s⊢ , t⊢ = _ , _ , s⊢ , t⊢

------------------------------------------------------------------------
-- Term-narrowing cast side-condition equivalence
------------------------------------------------------------------------

infix 4 _∣_⊢_≈ᵗ_∶_⊒_
infix 4 _∣_⊢_≈ᵗ_∶_⊑_

mutual
  data _∣_⊢_≈ᵗ_∶_⊒_ :
      TyCtx → StoreWid → Coercion → Coercion → Ty → Ty → Set where

    ≈ᵗ-oldⁿ : ∀{Δ σ A B s t}
      → Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B
       -------------------------------
      → Δ ∣ σ ⊢ s ≈ᵗ t ∶ A ⊒ B

    ↦≈↦ᵗⁿ : ∀{Δ σ A A′ B B′ s t s′ t′}
      → Δ ∣ σ ⊢ s ≈ᵗ s′ ∶ A′ ⊑ A
      → Δ ∣ σ ⊢ t ≈ᵗ t′ ∶ B ⊒ B′
       -------------------------------------------------
      → Δ ∣ σ ⊢ (s ↦ t) ≈ᵗ (s′ ↦ t′) ∶ (A ⇒ B) ⊒ (A′ ⇒ B′)

    ?≈seal★ᵗⁿ : ∀{Δ σ α}
      → σ ⊨ α ≈id ★
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (((＇ α) ？) ︔ id (＇ α))
          ≈ᵗ (id ★ ︔ seal ★ α) ∶ ★ ⊒ ＇ α

    seal★≈?ᵗⁿ : ∀{Δ σ α}
      → σ ⊨ α ≈id ★
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (id ★ ︔ seal ★ α)
          ≈ᵗ (((＇ α) ？) ︔ id (＇ α)) ∶ ★ ⊒ ＇ α

    ?≈sealGᵗⁿ : ∀{Δ σ α G}
      → WfTy Δ G
      → Ground G
      → σ ⊨ α ≈id G
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (((＇ α) ？) ︔ id (＇ α))
          ≈ᵗ (((G ？) ︔ id G) ︔ seal G α) ∶ ★ ⊒ ＇ α

    sealG≈?ᵗⁿ : ∀{Δ σ α G}
      → WfTy Δ G
      → Ground G
      → σ ⊨ α ≈id G
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (((G ？) ︔ id G) ︔ seal G α)
          ≈ᵗ (((＇ α) ？) ︔ id (＇ α)) ∶ ★ ⊒ ＇ α

  data _∣_⊢_≈ᵗ_∶_⊑_ :
      TyCtx → StoreWid → Coercion → Coercion → Ty → Ty → Set where

    ≈ᵗ-old : ∀{Δ σ A B s t}
      → Δ ∣ σ ⊢ s ≈ t ∶ A ⊑ B
       ------------------------------
      → Δ ∣ σ ⊢ s ≈ᵗ t ∶ A ⊑ B

    ↦≈↦ᵗ : ∀{Δ σ A A′ B B′ s t s′ t′}
      → Δ ∣ σ ⊢ s ≈ᵗ s′ ∶ A′ ⊒ A
      → Δ ∣ σ ⊢ t ≈ᵗ t′ ∶ B ⊑ B′
       ------------------------------------------------
      → Δ ∣ σ ⊢ (s ↦ t) ≈ᵗ (s′ ↦ t′) ∶ (A ⇒ B) ⊑ (A′ ⇒ B′)

    !≈unseal★ᵗ : ∀{Δ σ α}
      → σ ⊨ α ≈id ★
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (id (＇ α) ︔ ((＇ α) !))
          ≈ᵗ (unseal α ★ ︔ id ★) ∶ ＇ α ⊑ ★

    unseal★≈!ᵗ : ∀{Δ σ α}
      → σ ⊨ α ≈id ★
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (unseal α ★ ︔ id ★)
          ≈ᵗ (id (＇ α) ︔ ((＇ α) !)) ∶ ＇ α ⊑ ★

    !≈unsealGᵗ : ∀{Δ σ α G}
      → WfTy Δ G
      → Ground G
      → σ ⊨ α ≈id G
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (id (＇ α) ︔ ((＇ α) !))
          ≈ᵗ ((unseal α G ︔ id G) ︔ (G !)) ∶ ＇ α ⊑ ★

    unsealG≈!ᵗ : ∀{Δ σ α G}
      → WfTy Δ G
      → Ground G
      → σ ⊨ α ≈id G
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ ((unseal α G ︔ id G) ︔ (G !))
          ≈ᵗ (id (＇ α) ︔ ((＇ α) !)) ∶ ＇ α ⊑ ★
