module ImprecisionIndexed where

-- File Charter:
--   * Defines the indexed type imprecision relation for extrinsic-inst.
--   * The relation distinguishes plain and ν-bound type variables, requires
--   * plain lookup for variable identity, and gives ν-bound variables a
--   * non-recursive path to ★.
--   * Proves proof irrelevance for imprecision by excluding the ∀/ν overlap
--   * with an occurrence-path invariant.

open import Types
open import TypeProperties using
  ( rename-cong
  ; renameᵗ-ground
  ; renameᵗ-suc-comm
  ; substᵗ-ground
  ; substᵗ-suc-renameᵗ-suc
  )
open import TypeCheckDec using
  (raiseVarFrom; raiseVarFrom-≢; suc-injectiveᵛ)
open import Data.Bool using (Bool; false; true; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _<_; z<s; s<s)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (Σ; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; subst; sym; trans)

data VarMode : Set where
  plain ν-bound : VarMode

ICtx : Set
ICtx = List VarMode

interpSeal : ICtx → Seal → Seal
interpSeal [] α = α
interpSeal (plain ∷ Γ) α = interpSeal Γ α
interpSeal (ν-bound ∷ Γ) α = suc (interpSeal Γ α)

interpVar : ICtx → TyVar → Ty
interpVar [] X = ＇ X
interpVar (plain ∷ Γ) zero = ＇ zero
interpVar (plain ∷ Γ) (suc X) = ⇑ᵗ (interpVar Γ X)
interpVar (ν-bound ∷ Γ) zero = ｀ zero
interpVar (ν-bound ∷ Γ) (suc X) = ⇑ˢ (interpVar Γ X)

interp : ICtx → Ty → Ty
interp Γ (＇ X) = interpVar Γ X
interp Γ (｀ α) = ｀ (interpSeal Γ α)
interp Γ (‵ ι) = ‵ ι
interp Γ ★ = ★
interp Γ (A ⇒ B) = interp Γ A ⇒ interp Γ B
interp Γ (`∀ A) = `∀ (interp (plain ∷ Γ) A)

plains : ℕ → ICtx → ICtx
plains zero Γ = Γ
plains (suc n) Γ = plain ∷ plains n Γ

replacePlainAt : ℕ → ICtx → ICtx
replacePlainAt zero [] = []
replacePlainAt zero (plain ∷ Γ) = ν-bound ∷ Γ
replacePlainAt zero (ν-bound ∷ Γ) = ν-bound ∷ Γ
replacePlainAt (suc k) [] = []
replacePlainAt (suc k) (m ∷ Γ) = m ∷ replacePlainAt k Γ

insertνAt : ℕ → ICtx → ICtx
insertνAt zero Γ = ν-bound ∷ Γ
insertνAt (suc k) [] = ν-bound ∷ insertνAt k []
insertνAt (suc k) (m ∷ Γ) = m ∷ insertνAt k Γ

insertPlainAt : ℕ → ICtx → ICtx
insertPlainAt zero Γ = plain ∷ Γ
insertPlainAt (suc k) [] = plain ∷ insertPlainAt k []
insertPlainAt (suc k) (m ∷ Γ) = m ∷ insertPlainAt k Γ

substVarFrom : TyVar → Ty → Substᵗ
substVarFrom zero T = singleTyEnv T
substVarFrom (suc k) T = extsᵗ (substVarFrom k T)

renameᵗ-cong :
  ∀ {ρ ϱ} →
  (∀ X → ρ X ≡ ϱ X) →
  ∀ A → renameᵗ ρ A ≡ renameᵗ ϱ A
renameᵗ-cong = rename-cong

substVarFrom-⇑ᵗ :
  ∀ k T A →
  substᵗ (substVarFrom (suc k) T) (⇑ᵗ A) ≡
  ⇑ᵗ (substᵗ (substVarFrom k T) A)
substVarFrom-⇑ᵗ k T A = substᵗ-suc-renameᵗ-suc (substVarFrom k T) A

raise-ext : ∀ k X → extᵗ (raiseVarFrom k) X ≡ raiseVarFrom (suc k) X
raise-ext k zero = refl
raise-ext k (suc X) = refl

rename-raise-⇑ᵗ :
  ∀ k A →
  renameᵗ (raiseVarFrom (suc k)) (⇑ᵗ A) ≡
  ⇑ᵗ (renameᵗ (raiseVarFrom k) A)
rename-raise-⇑ᵗ k A =
  trans
    (renameᵗ-cong (λ X → sym (raise-ext k X)) (⇑ᵗ A))
    (sym (renameᵗ-suc-comm (raiseVarFrom k) A))

infix 4 _∋_∶_
data _∋_∶_ : ICtx → TyVar → VarMode → Set where
  here : ∀ {Γ m} → (m ∷ Γ) ∋ zero ∶ m
  there : ∀ {Γ X m m′} → Γ ∋ X ∶ m → (m′ ∷ Γ) ∋ suc X ∶ m

data PlainCtx : ICtx → Set where
  plain-[] : PlainCtx []
  plain-∷ : ∀ {Γ} → PlainCtx Γ → PlainCtx (plain ∷ Γ)

plainCtx-lookup :
  ∀ {Γ X} →
  PlainCtx Γ →
  X < length Γ →
  Γ ∋ X ∶ plain
plainCtx-lookup plain-[] ()
plainCtx-lookup {X = zero} (plain-∷ h) z<s = here
plainCtx-lookup {X = suc X} (plain-∷ h) (s<s X<Γ) =
  there (plainCtx-lookup h X<Γ)

insertPlain-lookup :
  ∀ {Γ X m} k →
  Γ ∋ X ∶ m →
  insertPlainAt k Γ ∋ raiseVarFrom k X ∶ m
insertPlain-lookup zero x∈ = there x∈
insertPlain-lookup (suc k) here = here
insertPlain-lookup (suc k) (there x∈) =
  there (insertPlain-lookup k x∈)

insertν-lookup :
  ∀ {Γ X m} k →
  Γ ∋ X ∶ m →
  insertνAt k Γ ∋ raiseVarFrom k X ∶ m
insertν-lookup zero x∈ = there x∈
insertν-lookup (suc k) here = here
insertν-lookup (suc k) (there x∈) = there (insertν-lookup k x∈)

data StarSourceᵢ : Ty → Set where
  star-＇ : (X : TyVar) → StarSourceᵢ (＇ X)
  star-｀ : (α : Seal) → StarSourceᵢ (｀ α)
  star-‵ : (ι : Base) → StarSourceᵢ (‵ ι)
  star-⇒ : (A B : Ty) → StarSourceᵢ (A ⇒ B)

rename-StarSourceᵢ :
  ∀ ρ {A} →
  StarSourceᵢ A →
  StarSourceᵢ (renameᵗ ρ A)
rename-StarSourceᵢ ρ (star-＇ X) = star-＇ (ρ X)
rename-StarSourceᵢ ρ (star-｀ α) = star-｀ α
rename-StarSourceᵢ ρ (star-‵ ι) = star-‵ ι
rename-StarSourceᵢ ρ (star-⇒ A B) =
  star-⇒ (renameᵗ ρ A) (renameᵗ ρ B)

data TyPath : Set where
  path-＇ : TyPath
  path-⇒ˡ : TyPath → TyPath
  path-⇒ʳ : TyPath → TyPath

data At : TyPath → Ty → Ty → Set where
  at-＇ : ∀ {X} → At path-＇ (＇ X) (＇ X)
  at-｀ : ∀ {α} → At path-＇ (｀ α) (｀ α)
  at-‵ : ∀ {ι} → At path-＇ (‵ ι) (‵ ι)
  at-★ : ∀ {p} → At p ★ ★
  at-⇒ˡ : ∀ {p A B C} → At p A C → At (path-⇒ˡ p) (A ⇒ B) C
  at-⇒ʳ : ∀ {p A B C} → At p B C → At (path-⇒ʳ p) (A ⇒ B) C
  at-∀ : ∀ {p A B} → At p A B → At p (`∀ A) (`∀ B)

data UsesRoot : TyVar → Ty → Set where
  usesRoot-＇ : ∀ {X} → UsesRoot X (＇ X)
  usesRoot-∀ : ∀ {X A} → UsesRoot (suc X) A → UsesRoot X (`∀ A)

data VarRoot : Ty → Set where
  varRoot-＇ : ∀ {X} → VarRoot (＇ X)
  varRoot-∀ : ∀ {A} → VarRoot A → VarRoot (`∀ A)

data StarRoot : Ty → Set where
  starRoot-★ : StarRoot ★
  starRoot-∀ : ∀ {A} → StarRoot A → StarRoot (`∀ A)

UsesAt : TyVar → TyPath → Ty → Set
UsesAt X p A = Σ Ty (λ B → Σ (At p A B) (λ _ → UsesRoot X B))

VarAt : TyPath → Ty → Set
VarAt p A = Σ Ty (λ B → Σ (At p A B) (λ _ → VarRoot B))

StarAt : TyPath → Ty → Set
StarAt p A = Σ Ty (λ B → Σ (At p A B) (λ _ → StarRoot B))

usesAt-＇ : ∀ {X} → UsesAt X path-＇ (＇ X)
usesAt-＇ = _ , at-＇ , usesRoot-＇

starAt-★ : ∀ {p} → StarAt p ★
starAt-★ = _ , at-★ , starRoot-★

usesAt-⇒ˡ : ∀ {X p A B} → UsesAt X p A → UsesAt X (path-⇒ˡ p) (A ⇒ B)
usesAt-⇒ˡ (_ , a , r) = _ , at-⇒ˡ a , r

usesAt-⇒ʳ : ∀ {X p A B} → UsesAt X p B → UsesAt X (path-⇒ʳ p) (A ⇒ B)
usesAt-⇒ʳ (_ , a , r) = _ , at-⇒ʳ a , r

usesAt-∀ : ∀ {X p A} → UsesAt (suc X) p A → UsesAt X p (`∀ A)
usesAt-∀ (_ , a , r) = _ , at-∀ a , usesRoot-∀ r

varAt-∀ : ∀ {p A} → VarAt p A → VarAt p (`∀ A)
varAt-∀ (_ , a , r) = _ , at-∀ a , varRoot-∀ r

starAt-⇒ˡ : ∀ {p A B} → StarAt p A → StarAt (path-⇒ˡ p) (A ⇒ B)
starAt-⇒ˡ (_ , a , r) = _ , at-⇒ˡ a , r

starAt-⇒ʳ : ∀ {p A B} → StarAt p B → StarAt (path-⇒ʳ p) (A ⇒ B)
starAt-⇒ʳ (_ , a , r) = _ , at-⇒ʳ a , r

starAt-∀ : ∀ {p A} → StarAt p A → StarAt p (`∀ A)
starAt-∀ (_ , a , r) = _ , at-∀ a , starRoot-∀ r

usesRoot-ren-varRoot :
  ∀ ρ {X A} →
  UsesRoot X A →
  VarRoot (renameᵗ ρ A)
usesRoot-ren-varRoot ρ usesRoot-＇ = varRoot-＇
usesRoot-ren-varRoot ρ (usesRoot-∀ u) =
  varRoot-∀ (usesRoot-ren-varRoot (extᵗ ρ) u)

at-star-varRoot-⊥ :
  ∀ {p A B C} →
  At p A B →
  StarRoot B →
  At p A C →
  VarRoot C →
  ⊥
at-star-varRoot-⊥ at-＇ () at-＇ v
at-star-varRoot-⊥ at-｀ () at-｀ ()
at-star-varRoot-⊥ at-‵ () at-‵ ()
at-star-varRoot-⊥ at-★ starRoot-★ at-★ ()
at-star-varRoot-⊥ (at-⇒ˡ sAt) sRoot (at-⇒ˡ vAt) vRoot =
  at-star-varRoot-⊥ sAt sRoot vAt vRoot
at-star-varRoot-⊥ (at-⇒ʳ sAt) sRoot (at-⇒ʳ vAt) vRoot =
  at-star-varRoot-⊥ sAt sRoot vAt vRoot
at-star-varRoot-⊥ (at-∀ sAt) (starRoot-∀ sRoot)
    (at-∀ vAt) (varRoot-∀ vRoot) =
  at-star-varRoot-⊥ sAt sRoot vAt vRoot

starAt-varAt-⊥ :
  ∀ {p A} →
  StarAt p A →
  VarAt p A →
  ⊥
starAt-varAt-⊥ (_ , sAt , sRoot) (_ , vAt , vRoot) =
  at-star-varRoot-⊥ sAt sRoot vAt vRoot

at-rename :
  ∀ ρ {p A B} →
  At p A B →
  At p (renameᵗ ρ A) (renameᵗ ρ B)
at-rename ρ at-＇ = at-＇
at-rename ρ at-｀ = at-｀
at-rename ρ at-‵ = at-‵
at-rename ρ at-★ = at-★
at-rename ρ (at-⇒ˡ a) = at-⇒ˡ (at-rename ρ a)
at-rename ρ (at-⇒ʳ a) = at-⇒ʳ (at-rename ρ a)
at-rename ρ (at-∀ a) = at-∀ (at-rename (extᵗ ρ) a)

starAt-rename-lower :
  ∀ ρ {p A} →
  StarAt p (renameᵗ ρ A) →
  StarAt p A
starAt-rename-lower ρ {A = ＇ X} (_ , at-＇ , ())
starAt-rename-lower ρ {A = ｀ α} (_ , at-｀ , ())
starAt-rename-lower ρ {A = ‵ ι} (_ , at-‵ , ())
starAt-rename-lower ρ {A = ★} (_ , at-★ , starRoot-★) =
  ★ , at-★ , starRoot-★
starAt-rename-lower ρ {A = A ⇒ B} (_ , at-⇒ˡ sAt , sRoot) =
  let _ , a , r = starAt-rename-lower ρ (_ , sAt , sRoot) in
  _ , at-⇒ˡ a , r
starAt-rename-lower ρ {A = A ⇒ B} (_ , at-⇒ʳ sAt , sRoot) =
  let _ , a , r = starAt-rename-lower ρ (_ , sAt , sRoot) in
  _ , at-⇒ʳ a , r
starAt-rename-lower ρ {A = `∀ A} (_ , at-∀ sAt , starRoot-∀ sRoot) =
  let _ , a , r = starAt-rename-lower (extᵗ ρ) (_ , sAt , sRoot) in
  _ , at-∀ a , starRoot-∀ r

starAt-⇑ᵗ-lower :
  ∀ {p A} →
  StarAt p (⇑ᵗ A) →
  StarAt p A
starAt-⇑ᵗ-lower = starAt-rename-lower suc

usesAt-ren-varAt :
  ∀ ρ {X p A} →
  UsesAt X p A →
  VarAt p (renameᵗ ρ A)
usesAt-ren-varAt ρ (_ , a , u) =
  _ , at-rename ρ a , usesRoot-ren-varRoot ρ u

usesRoot-var-eq :
  ∀ {X Y} →
  UsesRoot X (＇ Y) →
  X ≡ Y
usesRoot-var-eq usesRoot-＇ = refl

occurs : TyVar → Ty → Bool
occurs X (＇ Y) with X ≟ Y
occurs X (＇ Y) | yes eq = true
occurs X (＇ Y) | no neq = false
occurs X (｀ α) = false
occurs X (‵ ι) = false
occurs X ★ = false
occurs X (A ⇒ B) = occurs X A ∨ occurs X B
occurs X (`∀ A) = occurs (suc X) A

no-usesAt-occurs-false :
  ∀ {X A} →
  (∀ p → UsesAt X p A → ⊥) →
  occurs X A ≡ false
no-usesAt-occurs-false {X} {＇ Y} no-use with X ≟ Y
no-usesAt-occurs-false {X} {＇ .X} no-use | yes refl =
  ⊥-elim (no-use path-＇ usesAt-＇)
no-usesAt-occurs-false {X} {＇ Y} no-use | no neq = refl
no-usesAt-occurs-false {A = ｀ α} no-use = refl
no-usesAt-occurs-false {A = ‵ ι} no-use = refl
no-usesAt-occurs-false {A = ★} no-use = refl
no-usesAt-occurs-false {A = A ⇒ B} no-use
  rewrite no-usesAt-occurs-false
            (λ p u → no-use (path-⇒ˡ p) (usesAt-⇒ˡ u))
        | no-usesAt-occurs-false
            (λ p u → no-use (path-⇒ʳ p) (usesAt-⇒ʳ u)) = refl
no-usesAt-occurs-false {A = `∀ A} no-use =
  no-usesAt-occurs-false (λ p u → no-use p (usesAt-∀ u))

false≢trueᵢ : .(false ≡ true) → ⊥
false≢trueᵢ ()

infix 4 _⊢_⊑ₒ_ _⊢_⊑ᵢ_
data _⊢_⊑ₒ_ (Γ : ICtx) : Ty → Ty → Set where
  ⊑ₒ-★★ : Γ ⊢ ★ ⊑ₒ ★
  ⊑ₒ-★ν : ∀ {X} →
    Γ ∋ X ∶ ν-bound →
    Γ ⊢ ＇ X ⊑ₒ ★
  ⊑ₒ-★ : (A G : Ty) →
    StarSourceᵢ A →
    Ground G →
    Γ ⊢ A ⊑ₒ G →
    Γ ⊢ A ⊑ₒ ★
  ⊑ₒ-＇ : ∀ {X} → Γ ∋ X ∶ plain → Γ ⊢ ＇ X ⊑ₒ ＇ X
  ⊑ₒ-｀ : (α : Seal) → Γ ⊢ ｀ α ⊑ₒ ｀ α
  ⊑ₒ-‵ : (ι : Base) → Γ ⊢ ‵ ι ⊑ₒ ‵ ι
  ⊑ₒ-⇒ : (A A′ B B′ : Ty) →
    Γ ⊢ A ⊑ₒ A′ →
    Γ ⊢ B ⊑ₒ B′ →
    Γ ⊢ (A ⇒ B) ⊑ₒ (A′ ⇒ B′)
  ⊑ₒ-∀ : (A B : Ty) →
    (plain ∷ Γ) ⊢ A ⊑ₒ B →
    Γ ⊢ (`∀ A) ⊑ₒ (`∀ B)
  ⊑ₒ-ν : (A B : Ty) →
    .(occurs zero A ≡ true) →
    (ν-bound ∷ Γ) ⊢ A ⊑ₒ ⇑ᵗ B →
    Γ ⊢ (`∀ A) ⊑ₒ B

_⊢_⊑ᵢ_ : ICtx → Ty → Ty → Set
Γ ⊢ A ⊑ᵢ B = Γ ⊢ A ⊑ₒ B

pattern ⊑ᵢ-★★ = ⊑ₒ-★★
pattern ⊑ᵢ-★ν x = ⊑ₒ-★ν x
pattern ⊑ᵢ-★ A G s g p = ⊑ₒ-★ A G s g p
pattern ⊑ᵢ-＇ x = ⊑ₒ-＇ x
pattern ⊑ᵢ-｀ α = ⊑ₒ-｀ α
pattern ⊑ᵢ-‵ ι = ⊑ₒ-‵ ι
pattern ⊑ᵢ-⇒ A A′ B B′ p q = ⊑ₒ-⇒ A A′ B B′ p q
pattern ⊑ᵢ-∀ A B p = ⊑ₒ-∀ A B p
pattern ⊑ᵢ-ν A B occ p = ⊑ₒ-ν A B occ p

⊑ᵢ-refl-plain :
  ∀ {Γ Ψ A} →
  PlainCtx Γ →
  WfTy (length Γ) Ψ A →
  Γ ⊢ A ⊑ᵢ A
⊑ᵢ-refl-plain plainΓ (wfVar X<Γ) =
  ⊑ₒ-＇ (plainCtx-lookup plainΓ X<Γ)
⊑ᵢ-refl-plain plainΓ (wfSeal α<Ψ) = ⊑ₒ-｀ _
⊑ᵢ-refl-plain plainΓ wfBase = ⊑ₒ-‵ _
⊑ᵢ-refl-plain plainΓ wf★ = ⊑ₒ-★★
⊑ᵢ-refl-plain plainΓ (wf⇒ wfA wfB) =
  ⊑ₒ-⇒ _ _ _ _
    (⊑ᵢ-refl-plain plainΓ wfA)
    (⊑ᵢ-refl-plain plainΓ wfB)
⊑ᵢ-refl-plain plainΓ (wf∀ wfA) =
  ⊑ₒ-∀ _ _ (⊑ᵢ-refl-plain (plain-∷ plainΓ) wfA)

ground-reflᵢ :
  ∀ {Γ G} →
  Ground G →
  Γ ⊢ G ⊑ᵢ G
ground-reflᵢ (｀ α) = ⊑ᵢ-｀ α
ground-reflᵢ (‵ ι) = ⊑ᵢ-‵ ι
ground-reflᵢ ★⇒★ = ⊑ᵢ-⇒ ★ ★ ★ ★ ⊑ᵢ-★★ ⊑ᵢ-★★

∋-irrel :
  ∀ {Γ X m} →
  (x y : Γ ∋ X ∶ m) →
  x ≡ y
∋-irrel here here = refl
∋-irrel (there x) (there y) = cong there (∋-irrel x y)

mode-plain≠ν : plain ≡ ν-bound → ⊥
mode-plain≠ν ()

∋-mode-unique :
  ∀ {Γ X m n} →
  Γ ∋ X ∶ m →
  Γ ∋ X ∶ n →
  m ≡ n
∋-mode-unique here here = refl
∋-mode-unique (there x) (there y) = ∋-mode-unique x y

∋-plain-not-ν :
  ∀ {Γ X} →
  Γ ∋ X ∶ plain →
  Γ ∋ X ∶ ν-bound →
  ⊥
∋-plain-not-ν x y = mode-plain≠ν (∋-mode-unique x y)

plains-lookup :
  ∀ {Γ Δ X} →
  X < Δ →
  plains Δ Γ ∋ X ∶ plain
plains-lookup {Δ = suc Δ} {X = zero} z<s = here
plains-lookup {Δ = suc Δ} {X = suc X} (s<s X<) =
  there (plains-lookup X<)

wf-plains-reflᵢ :
  ∀ {Γ Δ Ψ A} →
  WfTy Δ Ψ A →
  plains Δ Γ ⊢ A ⊑ᵢ A
wf-plains-reflᵢ (wfVar X<) = ⊑ᵢ-＇ (plains-lookup X<)
wf-plains-reflᵢ (wfSeal {α = α} α<Ψ) = ⊑ᵢ-｀ α
wf-plains-reflᵢ (wfBase {ι = ι}) = ⊑ᵢ-‵ ι
wf-plains-reflᵢ wf★ = ⊑ᵢ-★★
wf-plains-reflᵢ (wf⇒ {A = A} {B = B} hA hB) =
  ⊑ᵢ-⇒ A A B B (wf-plains-reflᵢ hA) (wf-plains-reflᵢ hB)
wf-plains-reflᵢ (wf∀ {A = A} hA) = ⊑ᵢ-∀ A A (wf-plains-reflᵢ hA)

closed-reflᵢ :
  ∀ {Γ Ψ A} →
  WfTy 0 Ψ A →
  Γ ⊢ A ⊑ᵢ A
closed-reflᵢ = wf-plains-reflᵢ

Ground-irrel :
  ∀ {G} →
  (g h : Ground G) →
  g ≡ h
Ground-irrel (｀ α) (｀ .α) = refl
Ground-irrel (‵ ι) (‵ .ι) = refl
Ground-irrel ★⇒★ ★⇒★ = refl

StarSourceᵢ-irrel :
  ∀ {A} →
  (s t : StarSourceᵢ A) →
  s ≡ t
StarSourceᵢ-irrel (star-＇ X) (star-＇ .X) = refl
StarSourceᵢ-irrel (star-｀ α) (star-｀ .α) = refl
StarSourceᵢ-irrel (star-‵ ι) (star-‵ .ι) = refl
StarSourceᵢ-irrel (star-⇒ A B) (star-⇒ .A .B) = refl

inserted-∀-varAt :
  ∀ k {p B} →
  UsesAt k p B →
  VarAt p (renameᵗ (raiseVarFrom k) (`∀ B))
inserted-∀-varAt k u =
  varAt-∀ (usesAt-ren-varAt (extᵗ (raiseVarFrom k)) u)

starAt-inserted-∀-usesAt-⊥ :
  ∀ k {p B} →
  StarAt p (renameᵗ (raiseVarFrom k) (`∀ B)) →
  UsesAt k p B →
  ⊥
starAt-inserted-∀-usesAt-⊥ k s u =
  starAt-varAt-⊥ s (inserted-∀-varAt k u)

rename-raise-ext :
  ∀ k A →
  renameᵗ (extᵗ (raiseVarFrom k)) A ≡
  renameᵗ (raiseVarFrom (suc k)) A
rename-raise-ext k A = rename-cong (raise-ext k) A

raiseVarFrom-injective :
  ∀ k {X Y} →
  raiseVarFrom k X ≡ raiseVarFrom k Y →
  X ≡ Y
raiseVarFrom-injective zero eq = suc-injectiveᵛ eq
raiseVarFrom-injective (suc k) {zero} {zero} eq = refl
raiseVarFrom-injective (suc k) {zero} {suc Y} ()
raiseVarFrom-injective (suc k) {suc X} {zero} ()
raiseVarFrom-injective (suc k) {suc X} {suc Y} eq =
  cong suc (raiseVarFrom-injective k (suc-injectiveᵛ eq))

usesAt-raise-lower :
  ∀ k {X p A} →
  UsesAt (raiseVarFrom k X) p (renameᵗ (raiseVarFrom k) A) →
  UsesAt X p A
usesAt-raise-lower k {X} {path-＇} {A = ＇ Y} (_ , at-＇ , u) =
  subst (λ Z → UsesAt X path-＇ (＇ Z))
    (raiseVarFrom-injective k (usesRoot-var-eq u))
    usesAt-＇
usesAt-raise-lower k {p = path-⇒ˡ p} {A = ＇ Y} ()
usesAt-raise-lower k {p = path-⇒ʳ p} {A = ＇ Y} ()
usesAt-raise-lower k {A = ｀ α} (_ , at-｀ , ())
usesAt-raise-lower k {A = ‵ ι} (_ , at-‵ , ())
usesAt-raise-lower k {A = ★} (_ , at-★ , ())
usesAt-raise-lower k {p = path-＇} {A = A ⇒ B} ()
usesAt-raise-lower k {A = A ⇒ B} (_ , at-⇒ˡ uAt , uRoot) =
  usesAt-⇒ˡ (usesAt-raise-lower k (_ , uAt , uRoot))
usesAt-raise-lower k {A = A ⇒ B} (_ , at-⇒ʳ uAt , uRoot) =
  usesAt-⇒ʳ (usesAt-raise-lower k (_ , uAt , uRoot))
usesAt-raise-lower k {X} {A = `∀ A} (_ , at-∀ uAt , usesRoot-∀ uRoot) =
  usesAt-∀ (usesAt-raise-lower (suc k) {X = suc X}
    (subst UsesAt-target (rename-raise-ext k A) (_ , uAt , uRoot)))
  where
    UsesAt-target : Ty → Set
    UsesAt-target T = UsesAt (raiseVarFrom (suc k) (suc X)) _ T

occurs-raise :
  ∀ k X A →
  occurs (raiseVarFrom k X) (renameᵗ (raiseVarFrom k) A) ≡
  occurs X A
occurs-raise k X (＇ Y) with X ≟ Y | raiseVarFrom k X ≟ raiseVarFrom k Y
occurs-raise k X (＇ .X) | yes refl | yes refl = refl
occurs-raise k X (＇ .X) | yes refl | no neq = ⊥-elim (neq refl)
occurs-raise k X (＇ Y) | no neq | yes eq =
  ⊥-elim (neq (raiseVarFrom-injective k eq))
occurs-raise k X (＇ Y) | no neq | no neq′ = refl
occurs-raise k X (｀ α) = refl
occurs-raise k X (‵ ι) = refl
occurs-raise k X ★ = refl
occurs-raise k X (A ⇒ B)
  rewrite occurs-raise k X A
        | occurs-raise k X B = refl
occurs-raise k X (`∀ A)
  rewrite rename-raise-ext k A =
  occurs-raise (suc k) (suc X) A

occurs-zero-rename-ext-raise :
  ∀ k A →
  occurs zero (renameᵗ (extᵗ (raiseVarFrom k)) A) ≡ occurs zero A
occurs-zero-rename-ext-raise k A =
  trans (cong (occurs zero) (rename-raise-ext k A))
        (occurs-raise (suc k) zero A)

usesAt-⇑ᵗ-lower :
  ∀ {X p A} →
  UsesAt (suc X) p (⇑ᵗ A) →
  UsesAt X p A
usesAt-⇑ᵗ-lower = usesAt-raise-lower zero

ground-no-useAt∈ :
  ∀ {X p G} →
  Ground G →
  UsesAt X p G →
  ⊥
ground-no-useAt∈ (｀ α) (_ , at-｀ , ())
ground-no-useAt∈ (‵ ι) (_ , at-‵ , ())
ground-no-useAt∈ ★⇒★ (_ , at-⇒ˡ at-★ , ())
ground-no-useAt∈ ★⇒★ (_ , at-⇒ʳ at-★ , ())

ν-source-useAt-target-starAt∈ :
  ∀ {Γ X p A B} →
  Γ ∋ X ∶ ν-bound →
  Γ ⊢ A ⊑ₒ B →
  UsesAt X p A →
  StarAt p B
ν-source-useAt-target-starAt∈ xν ⊑ₒ-★★ (_ , at-★ , ())
ν-source-useAt-target-starAt∈ xν (⊑ₒ-★ν yν) (_ , at-＇ , usesRoot-＇) =
  starAt-★
ν-source-useAt-target-starAt∈ xν (⊑ₒ-★ A G s g p) u =
  starAt-★
ν-source-useAt-target-starAt∈ xν (⊑ₒ-＇ y∈) (_ , at-＇ , usesRoot-＇) =
  ⊥-elim (∋-plain-not-ν y∈ xν)
ν-source-useAt-target-starAt∈ xν (⊑ₒ-｀ α) (_ , at-｀ , ())
ν-source-useAt-target-starAt∈ xν (⊑ₒ-‵ ι) (_ , at-‵ , ())
ν-source-useAt-target-starAt∈ xν
    (⊑ₒ-⇒ A A′ B B′ p q) (_ , at-⇒ˡ uAt , uRoot) =
  starAt-⇒ˡ (ν-source-useAt-target-starAt∈ xν p (_ , uAt , uRoot))
ν-source-useAt-target-starAt∈ xν
    (⊑ₒ-⇒ A A′ B B′ p q) (_ , at-⇒ʳ uAt , uRoot) =
  starAt-⇒ʳ (ν-source-useAt-target-starAt∈ xν q (_ , uAt , uRoot))
ν-source-useAt-target-starAt∈ xν
    (⊑ₒ-∀ A B p) (_ , at-∀ uAt , usesRoot-∀ uRoot) =
  starAt-∀ (ν-source-useAt-target-starAt∈ (there xν) p
    (_ , uAt , uRoot))
ν-source-useAt-target-starAt∈ xν
    (⊑ₒ-ν A B occ p) (_ , at-∀ uAt , usesRoot-∀ uRoot) =
  starAt-⇑ᵗ-lower (ν-source-useAt-target-starAt∈ (there xν) p
    (_ , uAt , uRoot))

plain-source-useAt-target-useAt∈ :
  ∀ {Γ X p A B} →
  Γ ∋ X ∶ plain →
  Γ ⊢ A ⊑ₒ B →
  UsesAt X p A →
  UsesAt X p B
plain-source-useAt-target-useAt∈ x∈ ⊑ₒ-★★ (_ , at-★ , ())
plain-source-useAt-target-useAt∈ x∈ (⊑ₒ-★ν yν) (_ , at-＇ , usesRoot-＇) =
  ⊥-elim (∋-plain-not-ν x∈ yν)
plain-source-useAt-target-useAt∈ x∈ (⊑ₒ-★ A G s g p) u =
  ⊥-elim (ground-no-useAt∈ g
    (plain-source-useAt-target-useAt∈ x∈ p u))
plain-source-useAt-target-useAt∈ x∈ (⊑ₒ-＇ y∈) (_ , at-＇ , usesRoot-＇) =
  usesAt-＇
plain-source-useAt-target-useAt∈ x∈ (⊑ₒ-｀ α) (_ , at-｀ , ())
plain-source-useAt-target-useAt∈ x∈ (⊑ₒ-‵ ι) (_ , at-‵ , ())
plain-source-useAt-target-useAt∈ x∈
    (⊑ₒ-⇒ A A′ B B′ p q) (_ , at-⇒ˡ uAt , uRoot) =
  usesAt-⇒ˡ (plain-source-useAt-target-useAt∈ x∈ p (_ , uAt , uRoot))
plain-source-useAt-target-useAt∈ x∈
    (⊑ₒ-⇒ A A′ B B′ p q) (_ , at-⇒ʳ uAt , uRoot) =
  usesAt-⇒ʳ (plain-source-useAt-target-useAt∈ x∈ q (_ , uAt , uRoot))
plain-source-useAt-target-useAt∈ x∈
    (⊑ₒ-∀ A B p) (_ , at-∀ uAt , usesRoot-∀ uRoot) =
  usesAt-∀ (plain-source-useAt-target-useAt∈ (there x∈) p
    (_ , uAt , uRoot))
plain-source-useAt-target-useAt∈ x∈
    (⊑ₒ-ν A B occ p) (_ , at-∀ uAt , usesRoot-∀ uRoot) =
  usesAt-⇑ᵗ-lower (plain-source-useAt-target-useAt∈ (there x∈) p
    (_ , uAt , uRoot))

star-rest-target-unique :
  ∀ {Γ A G H} →
  StarSourceᵢ A →
  Γ ⊢ A ⊑ₒ G →
  Ground G →
  Γ ⊢ A ⊑ₒ H →
  Ground H →
  G ≡ H
star-rest-target-unique (star-＇ X) (⊑ₒ-★ν x) () q h
star-rest-target-unique (star-＇ X) (⊑ₒ-★ .(＇ X) G s g p) () q h
star-rest-target-unique (star-＇ X) (⊑ₒ-＇ x) () q h
star-rest-target-unique (star-｀ α) (⊑ₒ-｀ .α) (｀ .α)
    (⊑ₒ-｀ .α) (｀ .α) = refl
star-rest-target-unique (star-‵ ι) (⊑ₒ-‵ .ι) (‵ .ι)
    (⊑ₒ-‵ .ι) (‵ .ι) = refl
star-rest-target-unique (star-⇒ A B) (⊑ₒ-⇒ .A A′ .B B′ p₁ p₂)
    ★⇒★ (⊑ₒ-⇒ .A .A′ .B .B′ q₁ q₂) ★⇒★ = refl

var-ground-⊥ :
  ∀ {Γ X G} →
  Γ ⊢ ＇ X ⊑ₒ G →
  Ground G →
  ⊥
var-ground-⊥ (⊑ₒ-★ν x∈) ()
var-ground-⊥ (⊑ₒ-★ .(＇ _) G s g p) ()
var-ground-⊥ (⊑ₒ-＇ x∈) ()

∀ν-overlap-useAt-⊥ :
  ∀ {Γ A B p} →
  UsesAt zero p A →
  (plain ∷ Γ) ⊢ A ⊑ₒ B →
  (ν-bound ∷ Γ) ⊢ A ⊑ₒ ⇑ᵗ (`∀ B) →
  ⊥
∀ν-overlap-useAt-⊥ u p q =
  starAt-inserted-∀-usesAt-⊥ zero
    (ν-source-useAt-target-starAt∈ here q u)
    (plain-source-useAt-target-useAt∈ here p u)

∀ν-overlap-occurs-false :
  ∀ {Γ A B} →
  (plain ∷ Γ) ⊢ A ⊑ₒ B →
  (ν-bound ∷ Γ) ⊢ A ⊑ₒ ⇑ᵗ (`∀ B) →
  occurs zero A ≡ false
∀ν-overlap-occurs-false p q =
  no-usesAt-occurs-false λ r uAt →
    ∀ν-overlap-useAt-⊥ uAt p q

∀ν-overlap-⊥ :
  ∀ {Γ A B} →
  .(occurs zero A ≡ true) →
  (plain ∷ Γ) ⊢ A ⊑ₒ B →
  (ν-bound ∷ Γ) ⊢ A ⊑ₒ ⇑ᵗ (`∀ B) →
  ⊥
∀ν-overlap-⊥ occ p q
  rewrite ∀ν-overlap-occurs-false p q =
  false≢trueᵢ occ

⊑ₒ-proof-irrel :
  ∀ {Γ A B} →
  (p q : Γ ⊢ A ⊑ₒ B) →
  p ≡ q
⊑ₒ-proof-irrel ⊑ₒ-★★ ⊑ₒ-★★ = refl
⊑ₒ-proof-irrel (⊑ₒ-★ν x) (⊑ₒ-★ν y) =
  cong ⊑ₒ-★ν (∋-irrel x y)
⊑ₒ-proof-irrel (⊑ₒ-★ν x) (⊑ₒ-★ .(＇ _) G s g q) =
  ⊥-elim (var-ground-⊥ q g)
⊑ₒ-proof-irrel (⊑ₒ-★ .(＇ _) G s g p) (⊑ₒ-★ν x) =
  ⊥-elim (var-ground-⊥ p g)
⊑ₒ-proof-irrel (⊑ₒ-★ A G s g p) (⊑ₒ-★ .A H s′ g′ q)
  with star-rest-target-unique s p g q g′
⊑ₒ-proof-irrel (⊑ₒ-★ A G s g p) (⊑ₒ-★ .A .G s′ g′ q) | refl
  rewrite StarSourceᵢ-irrel s s′
        | Ground-irrel g g′
        | ⊑ₒ-proof-irrel p q = refl
⊑ₒ-proof-irrel (⊑ₒ-＇ x) (⊑ₒ-＇ y) = cong ⊑ₒ-＇ (∋-irrel x y)
⊑ₒ-proof-irrel (⊑ₒ-｀ α) (⊑ₒ-｀ .α) = refl
⊑ₒ-proof-irrel (⊑ₒ-‵ ι) (⊑ₒ-‵ .ι) = refl
⊑ₒ-proof-irrel (⊑ₒ-⇒ A A′ B B′ p₁ p₂)
    (⊑ₒ-⇒ .A .A′ .B .B′ q₁ q₂)
  rewrite ⊑ₒ-proof-irrel p₁ q₁
        | ⊑ₒ-proof-irrel p₂ q₂ = refl
⊑ₒ-proof-irrel (⊑ₒ-∀ A B p) (⊑ₒ-∀ .A .B q)
  rewrite ⊑ₒ-proof-irrel p q = refl
⊑ₒ-proof-irrel (⊑ₒ-∀ A B p) (⊑ₒ-ν .A .(`∀ B) occ q) =
  ⊥-elim (∀ν-overlap-⊥ occ p q)
⊑ₒ-proof-irrel (⊑ₒ-ν A .(`∀ B) occ p) (⊑ₒ-∀ .A B q) =
  ⊥-elim (∀ν-overlap-⊥ occ q p)
⊑ₒ-proof-irrel (⊑ₒ-ν A B occ p) (⊑ₒ-ν .A .B occ′ q)
  rewrite ⊑ₒ-proof-irrel p q = refl

⊑ᵢ-proof-irrel :
  ∀ {Γ A B} →
  (p q : Γ ⊢ A ⊑ᵢ B) →
  p ≡ q
⊑ᵢ-proof-irrel = ⊑ₒ-proof-irrel

⊑ᵢ-cast :
  ∀ {Γ A A′ B B′} →
  A ≡ A′ →
  B ≡ B′ →
  Γ ⊢ A ⊑ᵢ B →
  Γ ⊢ A′ ⊑ᵢ B′
⊑ᵢ-cast refl refl p = p

plain-weakenAt⊑ᵢ :
  ∀ k {Γ A B} →
  Γ ⊢ A ⊑ᵢ B →
  insertPlainAt k Γ ⊢
    renameᵗ (raiseVarFrom k) A ⊑ᵢ renameᵗ (raiseVarFrom k) B
plain-weakenAt⊑ᵢ k ⊑ₒ-★★ = ⊑ₒ-★★
plain-weakenAt⊑ᵢ k (⊑ₒ-★ν xν) =
  ⊑ₒ-★ν (insertPlain-lookup k xν)
plain-weakenAt⊑ᵢ k (⊑ₒ-★ A G s g p) =
  ⊑ₒ-★
    (renameᵗ (raiseVarFrom k) A)
    (renameᵗ (raiseVarFrom k) G)
    (rename-StarSourceᵢ (raiseVarFrom k) s)
    (renameᵗ-ground (raiseVarFrom k) g)
    (plain-weakenAt⊑ᵢ k p)
plain-weakenAt⊑ᵢ k (⊑ₒ-＇ x∈) =
  ⊑ₒ-＇ (insertPlain-lookup k x∈)
plain-weakenAt⊑ᵢ k (⊑ₒ-｀ α) = ⊑ₒ-｀ α
plain-weakenAt⊑ᵢ k (⊑ₒ-‵ ι) = ⊑ₒ-‵ ι
plain-weakenAt⊑ᵢ k (⊑ₒ-⇒ A A′ B B′ p q) =
  ⊑ₒ-⇒
    (renameᵗ (raiseVarFrom k) A)
    (renameᵗ (raiseVarFrom k) A′)
    (renameᵗ (raiseVarFrom k) B)
    (renameᵗ (raiseVarFrom k) B′)
    (plain-weakenAt⊑ᵢ k p)
    (plain-weakenAt⊑ᵢ k q)
plain-weakenAt⊑ᵢ k (⊑ₒ-∀ A B p) =
  ⊑ₒ-∀
    (renameᵗ (extᵗ (raiseVarFrom k)) A)
    (renameᵗ (extᵗ (raiseVarFrom k)) B)
    (⊑ᵢ-cast
      (renameᵗ-cong (λ X → sym (raise-ext k X)) A)
      (renameᵗ-cong (λ X → sym (raise-ext k X)) B)
      (plain-weakenAt⊑ᵢ (suc k) p))
plain-weakenAt⊑ᵢ k (⊑ₒ-ν A B occ p) =
  ⊑ₒ-ν
    (renameᵗ (extᵗ (raiseVarFrom k)) A)
    (renameᵗ (raiseVarFrom k) B)
    (trans (occurs-zero-rename-ext-raise k A) occ)
    (⊑ᵢ-cast
      (renameᵗ-cong (λ X → sym (raise-ext k X)) A)
      (rename-raise-⇑ᵗ k B)
      (plain-weakenAt⊑ᵢ (suc k) p))

-- Historical note: the old proof had the same generalized
-- `plain-weakenAt⊑ᵢ` recursion and the same casts in the `∀`/`ν` cases. The
-- differences are exactly the new relation changes: `Ground` no longer needs a
-- context-indexed weakening lemma, `⊑ₒ-★ν` is a direct lookup case, `⊑ₒ-＇`
-- weakens its plain lookup witness, and `⊑ₒ-ν` transports its occurrence side
-- condition with `occurs-zero-rename-ext-raise`.
plain-weaken⊑ᵢ :
  ∀ {Γ A B} →
  Γ ⊢ A ⊑ᵢ B →
  (plain ∷ Γ) ⊢ ⇑ᵗ A ⊑ᵢ ⇑ᵗ B
plain-weaken⊑ᵢ = plain-weakenAt⊑ᵢ zero

ν-weakenAt⊑ᵢ :
  ∀ k {Γ A B} →
  Γ ⊢ A ⊑ᵢ B →
  insertνAt k Γ ⊢
    renameᵗ (raiseVarFrom k) A ⊑ᵢ renameᵗ (raiseVarFrom k) B
ν-weakenAt⊑ᵢ k ⊑ₒ-★★ = ⊑ₒ-★★
ν-weakenAt⊑ᵢ k (⊑ₒ-★ν xν) = ⊑ₒ-★ν (insertν-lookup k xν)
ν-weakenAt⊑ᵢ k (⊑ₒ-★ A G s g p) =
  ⊑ₒ-★
    (renameᵗ (raiseVarFrom k) A)
    (renameᵗ (raiseVarFrom k) G)
    (rename-StarSourceᵢ (raiseVarFrom k) s)
    (renameᵗ-ground (raiseVarFrom k) g)
    (ν-weakenAt⊑ᵢ k p)
ν-weakenAt⊑ᵢ k (⊑ₒ-＇ x∈) = ⊑ₒ-＇ (insertν-lookup k x∈)
ν-weakenAt⊑ᵢ k (⊑ₒ-｀ α) = ⊑ₒ-｀ α
ν-weakenAt⊑ᵢ k (⊑ₒ-‵ ι) = ⊑ₒ-‵ ι
ν-weakenAt⊑ᵢ k (⊑ₒ-⇒ A A′ B B′ p q) =
  ⊑ₒ-⇒
    (renameᵗ (raiseVarFrom k) A)
    (renameᵗ (raiseVarFrom k) A′)
    (renameᵗ (raiseVarFrom k) B)
    (renameᵗ (raiseVarFrom k) B′)
    (ν-weakenAt⊑ᵢ k p)
    (ν-weakenAt⊑ᵢ k q)
ν-weakenAt⊑ᵢ k (⊑ₒ-∀ A B p) =
  ⊑ₒ-∀
    (renameᵗ (extᵗ (raiseVarFrom k)) A)
    (renameᵗ (extᵗ (raiseVarFrom k)) B)
    (⊑ᵢ-cast
      (renameᵗ-cong (λ X → sym (raise-ext k X)) A)
      (renameᵗ-cong (λ X → sym (raise-ext k X)) B)
      (ν-weakenAt⊑ᵢ (suc k) p))
ν-weakenAt⊑ᵢ k (⊑ₒ-ν A B occ p) =
  ⊑ₒ-ν
    (renameᵗ (extᵗ (raiseVarFrom k)) A)
    (renameᵗ (raiseVarFrom k) B)
    (trans (occurs-zero-rename-ext-raise k A) occ)
    (⊑ᵢ-cast
      (renameᵗ-cong (λ X → sym (raise-ext k X)) A)
      (rename-raise-⇑ᵗ k B)
      (ν-weakenAt⊑ᵢ (suc k) p))

ν-weaken⊑ᵢ :
  ∀ {Γ A B} →
  Γ ⊢ A ⊑ᵢ B →
  (ν-bound ∷ Γ) ⊢ ⇑ᵗ A ⊑ᵢ ⇑ᵗ B
ν-weaken⊑ᵢ = ν-weakenAt⊑ᵢ zero

postulate
  ν-close-inst⊑ᵢ :
    ∀ {Γ Ψ A B T} →
    WfTy 0 Ψ T →
    (ν-bound ∷ Γ) ⊢ A ⊑ᵢ ⇑ᵗ B →
    Γ ⊢ A [ T ]ᵗ ⊑ᵢ B

replacePlainAt-ν-lookup :
  ∀ k {Γ X} →
  Γ ∋ X ∶ ν-bound →
  replacePlainAt k Γ ∋ X ∶ ν-bound
replacePlainAt-ν-lookup zero {Γ = []} ()
replacePlainAt-ν-lookup zero {Γ = plain ∷ Γ} (there x∈) = there x∈
replacePlainAt-ν-lookup zero {Γ = ν-bound ∷ Γ} here = here
replacePlainAt-ν-lookup zero {Γ = ν-bound ∷ Γ} (there x∈) = there x∈
replacePlainAt-ν-lookup (suc k) {Γ = []} ()
replacePlainAt-ν-lookup (suc k) {Γ = m ∷ Γ} here = here
replacePlainAt-ν-lookup (suc k) {Γ = m ∷ Γ} (there x∈) =
  there (replacePlainAt-ν-lookup k x∈)

record νClosedInstᵢ {Γ A B T}
    (pν : (ν-bound ∷ Γ) ⊢ A ⊑ᵢ ⇑ᵗ B)
    (pT : Γ ⊢ A [ T ]ᵗ ⊑ᵢ B) : Set where
  constructor ν-closed-instᵢ
  field
    ν-inst-Ψᵢ : SealCtx
    ν-inst-wfTᵢ : WfTy 0 ν-inst-Ψᵢ T
    ν-inst-eqᵢ : pT ≡ ν-close-inst⊑ᵢ ν-inst-wfTᵢ pν
open νClosedInstᵢ public

ν-close-inst-evidenceᵢ :
  ∀ {Γ Ψ A B T}
    (hT : WfTy 0 Ψ T)
    (pν : (ν-bound ∷ Γ) ⊢ A ⊑ᵢ ⇑ᵗ B) →
  νClosedInstᵢ pν (ν-close-inst⊑ᵢ hT pν)
ν-close-inst-evidenceᵢ hT pν = ν-closed-instᵢ _ hT refl

SubstPlainOk : ℕ → ICtx → Ty → Set
SubstPlainOk k Γ T =
  ∀ {X} →
  insertPlainAt k Γ ∋ X ∶ plain →
  Γ ⊢ substVarFrom k T X ⊑ᵢ substVarFrom k T X

SubstPlainOk-zero :
  ∀ {Γ T} →
  Γ ⊢ T ⊑ᵢ T →
  SubstPlainOk zero Γ T
SubstPlainOk-zero T⊑T here = T⊑T
SubstPlainOk-zero T⊑T (there x∈) = ⊑ₒ-＇ x∈

SubstPlainOk-plain :
  ∀ {k Γ T} →
  SubstPlainOk k Γ T →
  SubstPlainOk (suc k) (plain ∷ Γ) T
SubstPlainOk-plain ok here = ⊑ₒ-＇ here
SubstPlainOk-plain ok (there x∈) = plain-weaken⊑ᵢ (ok x∈)

SubstPlainOk-ν :
  ∀ {k Γ T} →
  SubstPlainOk k Γ T →
  SubstPlainOk (suc k) (ν-bound ∷ Γ) T
SubstPlainOk-ν ok (there x∈) = ν-weaken⊑ᵢ (ok x∈)

insertPlainAt-empty-no-ν :
  ∀ k {X} →
  insertPlainAt k [] ∋ X ∶ ν-bound →
  ⊥
insertPlainAt-empty-no-ν zero (there ())
insertPlainAt-empty-no-ν (suc k) (there x∈) =
  insertPlainAt-empty-no-ν k x∈

substPlain-ν-lookup :
  ∀ k {Γ X T} →
  insertPlainAt k Γ ∋ X ∶ ν-bound →
  Σ TyVar
    (λ Y → Σ (Γ ∋ Y ∶ ν-bound)
      (λ _ → substVarFrom k T X ≡ ＇ Y))
substPlain-ν-lookup zero (there x∈) = _ , x∈ , refl
substPlain-ν-lookup (suc k) {Γ = []} (there x∈) =
  ⊥-elim (insertPlainAt-empty-no-ν k x∈)
substPlain-ν-lookup (suc k) {Γ = ν-bound ∷ Γ} here =
  zero , here , refl
substPlain-ν-lookup (suc k) {Γ = m ∷ Γ} (there x∈)
  with substPlain-ν-lookup k x∈
substPlain-ν-lookup (suc k) {Γ = m ∷ Γ} (there x∈)
  | Y , y∈ , eq = suc Y , there y∈ , cong ⇑ᵗ eq

substPlainAt-StarSourceᵢ :
  ∀ k T {Γ A G} →
  StarSourceᵢ A →
  Ground G →
  insertPlainAt k Γ ⊢ A ⊑ᵢ G →
  StarSourceᵢ (substᵗ (substVarFrom k T) A)
substPlainAt-StarSourceᵢ k T (star-＇ X) g p =
  ⊥-elim (var-ground-⊥ p g)
substPlainAt-StarSourceᵢ k T (star-｀ α) g p = star-｀ α
substPlainAt-StarSourceᵢ k T (star-‵ ι) g p = star-‵ ι
substPlainAt-StarSourceᵢ k T (star-⇒ A B) g p =
  star-⇒
    (substᵗ (substVarFrom k T) A)
    (substᵗ (substVarFrom k T) B)

occurs-raise-fresh :
  ∀ k A →
  occurs k (renameᵗ (raiseVarFrom k) A) ≡ false
occurs-raise-fresh k (＇ X) with k ≟ raiseVarFrom k X
occurs-raise-fresh k (＇ X) | yes eq =
  ⊥-elim (raiseVarFrom-≢ k X (sym eq))
occurs-raise-fresh k (＇ X) | no neq = refl
occurs-raise-fresh k (｀ α) = refl
occurs-raise-fresh k (‵ ι) = refl
occurs-raise-fresh k ★ = refl
occurs-raise-fresh k (A ⇒ B)
  rewrite occurs-raise-fresh k A
        | occurs-raise-fresh k B = refl
occurs-raise-fresh k (`∀ A)
  rewrite rename-raise-ext k A =
  occurs-raise-fresh (suc k) A

occurs-substVarFrom-var-< :
  ∀ k X Y T →
  X < k →
  occurs X (substVarFrom k T Y) ≡ occurs X (＇ Y)
occurs-substVarFrom-var-< zero X Y T ()
occurs-substVarFrom-var-< (suc k) zero zero T z<s = refl
occurs-substVarFrom-var-< (suc k) zero (suc Y) T z<s
  rewrite occurs-raise-fresh zero (substVarFrom k T Y) = refl
occurs-substVarFrom-var-< (suc k) (suc X) zero T (s<s X<k) =
  refl
occurs-substVarFrom-var-< (suc k) (suc X) (suc Y) T (s<s X<k)
  rewrite occurs-raise zero X (substVarFrom k T Y)
        | occurs-substVarFrom-var-< k X Y T X<k
        | occurs-raise zero X (＇ Y) = refl

occurs-substVarFrom-<-ty :
  ∀ A k X T →
  X < k →
  occurs X (substᵗ (substVarFrom k T) A) ≡ occurs X A
occurs-substVarFrom-<-ty (＇ Y) k X T X<k =
  occurs-substVarFrom-var-< k X Y T X<k
occurs-substVarFrom-<-ty (｀ α) k X T X<k = refl
occurs-substVarFrom-<-ty (‵ ι) k X T X<k = refl
occurs-substVarFrom-<-ty ★ k X T X<k = refl
occurs-substVarFrom-<-ty (A ⇒ B) k X T X<k
  rewrite occurs-substVarFrom-<-ty A k X T X<k
        | occurs-substVarFrom-<-ty B k X T X<k = refl
occurs-substVarFrom-<-ty (`∀ A) k X T X<k =
  occurs-substVarFrom-<-ty A (suc k) (suc X) T (s<s X<k)

occurs-substVarFrom-< :
  ∀ k X T A →
  X < k →
  occurs X (substᵗ (substVarFrom k T) A) ≡ occurs X A
occurs-substVarFrom-< k X T A =
  occurs-substVarFrom-<-ty A k X T

substPlainAt⊑ᵢ :
  ∀ k T {Γ A B} →
  SubstPlainOk k Γ T →
  insertPlainAt k Γ ⊢ A ⊑ᵢ B →
  Γ ⊢ substᵗ (substVarFrom k T) A
    ⊑ᵢ substᵗ (substVarFrom k T) B
substPlainAt⊑ᵢ k T ok ⊑ₒ-★★ = ⊑ₒ-★★
substPlainAt⊑ᵢ k T ok (⊑ₒ-★ν xν)
  with substPlain-ν-lookup k xν
substPlainAt⊑ᵢ k T ok (⊑ₒ-★ν xν) | Y , yν , eq =
  ⊑ᵢ-cast (sym eq) refl (⊑ₒ-★ν yν)
substPlainAt⊑ᵢ k T ok (⊑ₒ-★ A G s g p) =
  ⊑ₒ-★
    (substᵗ (substVarFrom k T) A)
    (substᵗ (substVarFrom k T) G)
    (substPlainAt-StarSourceᵢ k T s g p)
    (substᵗ-ground (substVarFrom k T) g)
    (substPlainAt⊑ᵢ k T ok p)
substPlainAt⊑ᵢ k T ok (⊑ₒ-＇ x∈) = ok x∈
substPlainAt⊑ᵢ k T ok (⊑ₒ-｀ α) = ⊑ₒ-｀ α
substPlainAt⊑ᵢ k T ok (⊑ₒ-‵ ι) = ⊑ₒ-‵ ι
substPlainAt⊑ᵢ k T ok (⊑ₒ-⇒ A A′ B B′ p q) =
  ⊑ₒ-⇒
    (substᵗ (substVarFrom k T) A)
    (substᵗ (substVarFrom k T) A′)
    (substᵗ (substVarFrom k T) B)
    (substᵗ (substVarFrom k T) B′)
    (substPlainAt⊑ᵢ k T ok p)
    (substPlainAt⊑ᵢ k T ok q)
substPlainAt⊑ᵢ k T ok (⊑ₒ-∀ A B p) =
  ⊑ₒ-∀
    (substᵗ (substVarFrom (suc k) T) A)
    (substᵗ (substVarFrom (suc k) T) B)
    (substPlainAt⊑ᵢ (suc k) T (SubstPlainOk-plain ok) p)
substPlainAt⊑ᵢ k T ok (⊑ₒ-ν A B occ p) =
  ⊑ₒ-ν
    (substᵗ (substVarFrom (suc k) T) A)
    (substᵗ (substVarFrom k T) B)
    (trans (occurs-substVarFrom-< (suc k) zero T A z<s) occ)
    (⊑ᵢ-cast
      refl
      (substVarFrom-⇑ᵗ k T B)
      (substPlainAt⊑ᵢ (suc k) T (SubstPlainOk-ν ok) p))

substPlain⊑ᵢ :
  ∀ T {Γ A B} →
  Γ ⊢ T ⊑ᵢ T →
  (plain ∷ Γ) ⊢ A ⊑ᵢ B →
  Γ ⊢ A [ T ]ᵗ ⊑ᵢ B [ T ]ᵗ
substPlain⊑ᵢ T T⊑T p =
  substPlainAt⊑ᵢ zero T (SubstPlainOk-zero T⊑T) p
