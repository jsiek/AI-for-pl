-- This is based on the cambridge22 notes.

module Coercions where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; false; true; _∧_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.Nat using
  (ℕ; _<_; _≤_; _+_; _∸_; zero; suc; z<s; s<s; s≤s⁻¹)
open import Data.Nat.Properties using
  (_≟_; ≤-refl; ≤-trans; +-assoc; +-comm; +-monoʳ-≤; +-monoˡ-≤;
   +-suc; m+[n∸m]≡n; m≤m+n; m≤n+m; n≤1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (subst; cong; cong₂; sym; trans)
open import Relation.Nullary using (Dec; yes; no)

open import Types

Label = ℕ

------------------------------------------------------------------------
-- Raw coercions
------------------------------------------------------------------------

data Coercion : Set where
 id : Ty → Coercion
 _︔_ : Coercion → Coercion → Coercion
 _↦_ : Coercion → Coercion → Coercion
 `∀ : Coercion → Coercion
 _! : Ty → Coercion
 _？ : Ty → Coercion
 seal : Ty → TyVar → Coercion
 unseal : TyVar → Ty → Coercion
 gen : Ty → Coercion → Coercion
 inst : Ty → Coercion → Coercion


------------------------------------------------------------------------
-- Source and target type of a coercion
------------------------------------------------------------------------

src : Coercion → Ty
tgt : Coercion → Ty

src (id A) = A
src (c ︔ d) = src c
src (c ↦ d) = tgt c ⇒ src d
src (`∀ c) = `∀ (src c)
src (G !) = G
src (G ？) = ★
src (seal A α) = A
src (unseal α A) = ＇ α
src (gen A c) = A
src (inst B c) = `∀ (src c)

tgt (id A) = A
tgt (c ︔ d) = tgt d
tgt (c ↦ d) = src c ⇒ tgt d
tgt (`∀ c) = `∀ (tgt c)
tgt (G !) = ★
tgt (H ？) = H
tgt (seal A α) = ＇ α
tgt (unseal α B) = B
tgt (gen A c) = `∀ (tgt c)
tgt (inst B c) = B

------------------------------------------------------------------------
-- Inert coercions, i.e., part of a value
------------------------------------------------------------------------

data Inert : Coercion → Set where
  _! : (G : Ty) → Inert (G !)
  seal : (A : Ty) → (α : TyVar) → Inert (seal A α)
  _↦_ : (c d : Coercion) → Inert (c ↦ d)
  `∀ : (c : Coercion) → Inert (`∀ c)
  gen : (A : Ty) → (c : Coercion) → Inert (gen A c)

------------------------------------------------------------------------
-- reveal/conceal B α C generate coercions between B[α] and B[C]
------------------------------------------------------------------------

mutual
  reveal : Ty → TyVar → Ty → Coercion
  reveal (＇ β) α C with α ≟ β
  reveal (＇ .α) α C | yes refl = unseal α C
  reveal (＇ β) α C | no neq = id (＇ β)
  reveal (‵ ι) α C = id (‵ ι)
  reveal ★ α C = id ★
  reveal (A ⇒ B) α C = conceal A α C ↦ reveal B α C
  reveal (`∀ A) α C = `∀ (reveal A (suc α) (⇑ᵗ C))

  conceal : Ty → TyVar → Ty → Coercion
  conceal (＇ β) α C with α ≟ β
  conceal (＇ .α) α C | yes refl = seal C α
  conceal (＇ β) α C | no neq = id (＇ β)
  conceal (‵ ι) α C = id (‵ ι)
  conceal ★ α C = id ★
  conceal (A ⇒ B) α C = reveal A α C ↦ conceal B α C
  conceal (`∀ A) α C = `∀ (conceal A (suc α) (⇑ᵗ C))

------------------------------------------------------------------------
-- Renaming Type Variables
------------------------------------------------------------------------

renameᶜ : Renameᵗ → Coercion → Coercion
renameᶜ ρ (id A) = id (renameᵗ ρ A)
renameᶜ ρ (p ︔ q) = renameᶜ ρ p ︔ renameᶜ ρ q
renameᶜ ρ (A !) = renameᵗ ρ A !
renameᶜ ρ (A ？) = renameᵗ ρ A ？
renameᶜ ρ (unseal α A) = unseal (ρ α) (renameᵗ ρ A)
renameᶜ ρ (seal A α) = seal (renameᵗ ρ A) (ρ α)
renameᶜ ρ (p ↦ q) = renameᶜ ρ p ↦ renameᶜ ρ q
renameᶜ ρ (`∀ p) = `∀ (renameᶜ (extᵗ ρ) p)
renameᶜ ρ (gen A p) = gen (renameᵗ ρ A) (renameᶜ (extᵗ ρ) p)
renameᶜ ρ (inst B p) = inst (renameᵗ ρ B) (renameᶜ (extᵗ ρ) p)

data Mode : Set where
  id-only tag-or-id seal-or-id : Mode

ModeEnv : Set
ModeEnv = TyVar → Mode

id-onlyᵈ : ModeEnv
id-onlyᵈ X = id-only

tag-or-idᵈ : ModeEnv
tag-or-idᵈ X = tag-or-id

seal-or-idᵈ : ModeEnv
seal-or-idᵈ X = seal-or-id

extᵈ : ModeEnv → ModeEnv
extᵈ μ zero = id-only
extᵈ μ (suc X) = μ X

genᵈ : ModeEnv → ModeEnv
genᵈ μ zero = tag-or-id
genᵈ μ (suc X) = μ X

instᵈ : ModeEnv → ModeEnv
instᵈ μ zero = seal-or-id
instᵈ μ (suc X) = μ X

mode≤ : Mode → Mode → Bool
mode≤ id-only id-only = true
mode≤ id-only tag-or-id = true
mode≤ id-only seal-or-id = true
mode≤ tag-or-id id-only = false
mode≤ tag-or-id tag-or-id = true
mode≤ tag-or-id seal-or-id = false
mode≤ seal-or-id id-only = false
mode≤ seal-or-id tag-or-id = false
mode≤ seal-or-id seal-or-id = true

ModeIncl : ModeEnv → ModeEnv → Set
ModeIncl μ ν = ∀ X → mode≤ (μ X) (ν X) ≡ true

modeIncl-refl : ∀ {μ} → ModeIncl μ μ
modeIncl-refl {μ} X with μ X
modeIncl-refl X | id-only = refl
modeIncl-refl X | tag-or-id = refl
modeIncl-refl X | seal-or-id = refl

idModeAllowed : Mode → Bool
idModeAllowed id-only = true
idModeAllowed tag-or-id = true
idModeAllowed seal-or-id = true

tagModeAllowed : Mode → Bool
tagModeAllowed id-only = false
tagModeAllowed tag-or-id = true
tagModeAllowed seal-or-id = false

sealModeAllowed : Mode → Bool
sealModeAllowed id-only = false
sealModeAllowed tag-or-id = false
sealModeAllowed seal-or-id = true

idTyAllowed : ModeEnv → Ty → Bool
idTyAllowed μ (＇ α) = idModeAllowed (μ α)
idTyAllowed μ (‵ ι) = true
idTyAllowed μ ★ = true
idTyAllowed μ (A ⇒ B) = idTyAllowed μ A ∧ idTyAllowed μ B
idTyAllowed μ (`∀ A) = idTyAllowed (extᵈ μ) A

tagTyAllowed : ModeEnv → Ty → Bool
tagTyAllowed μ (＇ α) = tagModeAllowed (μ α)
tagTyAllowed μ (‵ ι) = true
tagTyAllowed μ ★ = true
tagTyAllowed μ (A ⇒ B) = true
tagTyAllowed μ (`∀ A) = true

data DualAction : Set where
  normal tag-to-seal seal-to-tag : DualAction

DualActionEnv : Set
DualActionEnv = TyVar → DualAction

normalᵃ : DualActionEnv
normalᵃ X = normal

extᵃ : DualActionEnv → DualActionEnv
extᵃ η zero = normal
extᵃ η (suc X) = η X

genᵃ : DualActionEnv → DualActionEnv
genᵃ η zero = tag-to-seal
genᵃ η (suc X) = η X

instᵃ : DualActionEnv → DualActionEnv
instᵃ η zero = seal-to-tag
instᵃ η (suc X) = η X

dualTag : DualActionEnv → Ty → Coercion
dualTag η (＇ α) with η α
dualTag η (＇ α) | normal = (＇ α) ？
dualTag η (＇ α) | tag-to-seal = seal ★ α
dualTag η (＇ α) | seal-to-tag = (＇ α) ？
dualTag η (‵ ι) = (‵ ι) ？
dualTag η ★ = ★ ？
dualTag η (A ⇒ B) = (A ⇒ B) ？
dualTag η (`∀ A) = (`∀ A) ？

dualUntag : DualActionEnv → Ty → Coercion
dualUntag η (＇ α) with η α
dualUntag η (＇ α) | normal = (＇ α) !
dualUntag η (＇ α) | tag-to-seal = unseal α ★
dualUntag η (＇ α) | seal-to-tag = (＇ α) !
dualUntag η (‵ ι) = (‵ ι) !
dualUntag η ★ = ★ !
dualUntag η (A ⇒ B) = (A ⇒ B) !
dualUntag η (`∀ A) = (`∀ A) !

dualSeal : DualActionEnv → Ty → TyVar → Coercion
dualSeal η A α with η α
dualSeal η A α | normal = unseal α A
dualSeal η A α | tag-to-seal = unseal α A
dualSeal η A α | seal-to-tag = (＇ α) !

dualUnseal : DualActionEnv → TyVar → Ty → Coercion
dualUnseal η α A with η α
dualUnseal η α A | normal = seal A α
dualUnseal η α A | tag-to-seal = seal A α
dualUnseal η α A | seal-to-tag = (＇ α) ？

infix 8 -_

dual : DualActionEnv → Coercion → Coercion
dual η (id A) = id A
dual η (c ︔ d) = dual η d ︔ dual η c
dual η (c ↦ d) = dual η c ↦ dual η d
dual η (`∀ c) = `∀ (dual (extᵃ η) c)
dual η (G !) = dualTag η G
dual η (G ？) = dualUntag η G
dual η (seal A α) = dualSeal η A α
dual η (unseal α A) = dualUnseal η α A
dual η (gen A c) = inst A (dual (genᵃ η) c)
dual η (inst B c) = gen B (dual (instᵃ η) c)

-_ : Coercion → Coercion
-_ = dual normalᵃ

⇑ᶜ : Coercion → Coercion
⇑ᶜ = renameᶜ suc

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

_[_]ᶜ : Coercion → TyVar → Coercion
c [ X ]ᶜ = renameᶜ (singleRenameᵗ X) c


-- Phil: What about the restriction that we don't allow
--  X to ★ casts.

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

infix 4 _∣_∣_⊢_∶_=⇒_

data _∣_∣_⊢_∶_=⇒_ : ModeEnv → TyCtx → Store → Coercion → Ty → Ty → Set where

  cast-id : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{A : Ty}
    → WfTy Δ A
    → idTyAllowed μ A ≡ true
     -------------------
    → μ ∣ Δ ∣ Σ ⊢ id A ∶ A =⇒ A

  cast-seal : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{α : TyVar}{A : Ty}
    → WfTy Δ A
    → (α , A) ∈ Σ
    → sealModeAllowed (μ α) ≡ true
     ---------------------------
    → μ ∣ Δ ∣ Σ ⊢ seal A α ∶ A =⇒ (＇ α)

  cast-unseal : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{α : TyVar}{A : Ty}
    → WfTy Δ A
    → (α , A) ∈ Σ
    → sealModeAllowed (μ α) ≡ true
     -----------------------------
    → μ ∣ Δ ∣ Σ ⊢ unseal α A ∶ (＇ α) =⇒ A

  -- Phil: s and t have different Σ's, they combine, with side condition
  cast-seq : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{A B C : Ty}{s t : Coercion}
    → μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ B
    → μ ∣ Δ ∣ Σ ⊢ t ∶ B =⇒ C
     -------------------------
    → μ ∣ Δ ∣ Σ ⊢ (s ︔ t) ∶ A =⇒ C

  cast-tag : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{G : Ty}
    → WfTy Δ G
    → Ground G
    → tagTyAllowed μ G ≡ true
    -- If G is α, then α ∉ dom(Σ)
     ---------------------
    → μ ∣ Δ ∣ Σ ⊢ G ! ∶ G =⇒ ★

  cast-untag : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{H : Ty}
    → WfTy Δ H
    → Ground H
    → tagTyAllowed μ H ≡ true
     -----------------------
    → μ ∣ Δ ∣ Σ ⊢ H ？ ∶ ★ =⇒ H

  cast-fun : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{A A′ B B′ : Ty}{s t : Coercion}
    → μ ∣ Δ ∣ Σ ⊢ s ∶ A′ =⇒ A
    → μ ∣ Δ ∣ Σ ⊢ t ∶ B =⇒ B′
     ---------------------------------------
    → μ ∣ Δ ∣ Σ ⊢ (s ↦ t) ∶ (A ⇒ B) =⇒ (A′ ⇒ B′)

  cast-all : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
    → extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A =⇒ B
     ----------------------------------
    → μ ∣ Δ ∣ Σ ⊢ (`∀ s) ∶ (`∀ A) =⇒ (`∀ B)

  -- ν̅ 
  cast-inst : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
    → WfTy Δ B
    → occurs zero A ≡ true
    → instᵈ μ ∣ suc Δ ∣ (0 , ★) ∷ ⟰ᵗ Σ ⊢ s ∶ A =⇒ ⇑ᵗ B
     ----------------------------------------
    → μ ∣ Δ ∣ Σ ⊢ (inst B s) ∶ (`∀ A) =⇒ B

  -- ν
  cast-gen : ∀{μ : ModeEnv}{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
    → WfTy Δ A
    → occurs zero B ≡ true
    → genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ ⇑ᵗ A =⇒ B
     ----------------------------------
    → μ ∣ Δ ∣ Σ ⊢ (gen A s) ∶ A =⇒ (`∀ B)

infix 4 _∣_⊢_∶_=⇒_

_∣_⊢_∶_=⇒_ : TyCtx → Store → Coercion → Ty → Ty → Set
Δ ∣ Σ ⊢ c ∶ A =⇒ B = ∃[ μ ] μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B

  
