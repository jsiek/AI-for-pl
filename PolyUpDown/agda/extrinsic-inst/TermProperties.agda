module TermProperties where

-- File Charter:
--   * Term-variable metatheory for extrinsic-inst terms.
--   * Renaming/substitution environments for term variables, with lifting through
--   * type binders and typing-preservation theorems.
--   * Single-variable and single-type substitution APIs used by reduction.
-- Note to self:
--   * Keep raw term syntax and type/seal structural actions in `Terms.agda`;
--   * this file owns term-variable substitution infrastructure.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; map; []; _∷_)
open import Data.Nat using (_<_; suc; zero; z<s; s<s)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym)

open import Types
open import TypeProperties
open import Store
open import Ctx using (⤊ᵗ)
open import UpDown
open import Terms hiding (_[_]ᵀ)

------------------------------------------------------------------------
-- Term-variable renaming and substitution environments
------------------------------------------------------------------------

Renameˣ : Set
Renameˣ = Var → Var

Renameˣ-wt : (Γ Γ′ : Ctx) (ρ : Renameˣ) → Set
Renameˣ-wt Γ Γ′ ρ = ∀ {A : Ty}{x : Var} → (h : Γ ∋ x ⦂ A) → Γ′ ∋ ρ x ⦂ A

Substˣ : Set
Substˣ = Var → Term

Substˣ-wt : ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx} → (σ : Substˣ) → Set
Substˣ-wt {Δ} {Ψ} {Σ} {Γ} {Γ′} σ =
  ∀ {A : Ty}{x : Var} → (h : Γ ∋ x ⦂ A) → Δ ∣ Ψ ∣ Σ ∣ Γ′ ⊢ σ x ⦂ A

extʳ : Renameˣ → Renameˣ
extʳ ρ zero = zero
extʳ ρ (suc x) = suc (ρ x)

extʳ-wt : ∀ {Γ Γ′ : Ctx}{A : Ty} → (ρ : Renameˣ) →
  Renameˣ-wt Γ Γ′ ρ →
  Renameˣ-wt (A ∷ Γ) (A ∷ Γ′) (extʳ ρ)
extʳ-wt ρ hρ Z = Z
extʳ-wt ρ hρ (S h) = S (hρ h)

wkʳ : Renameˣ
wkʳ x = suc x

wkʳ-wt : ∀ {Γ : Ctx}{A B : Ty}{x : Var} →
  (h : Γ ∋ x ⦂ A) →
  (B ∷ Γ) ∋ wkʳ x ⦂ A
wkʳ-wt h = S h

map∋ : ∀ {Γ : Ctx}{x : Var}{A : Ty} → (f : Ty → Ty) →
  Γ ∋ x ⦂ A →
  map f Γ ∋ x ⦂ f A
map∋ f Z = Z
map∋ f (S h) = S (map∋ f h)

unmap∋-⤊ᵗ : ∀ {Γ : Ctx}{x : Var}{A : Ty} →
  ⤊ᵗ Γ ∋ x ⦂ A →
  Σ[ B ∈ Ty ] Σ[ _ ∈ (A ≡ renameᵗ suc B) ] (Γ ∋ x ⦂ B)
unmap∋-⤊ᵗ {Γ = B ∷ Γ} Z = B , refl , Z
unmap∋-⤊ᵗ {Γ = B ∷ Γ} (S h) with unmap∋-⤊ᵗ {Γ = Γ} h
... | C , eq , h′ = C , eq , S h′

liftᵗʳ : Renameˣ → Renameˣ
liftᵗʳ ρ x = ρ x

liftᵗʳ-wt : ∀ {Γ Γ′ : Ctx} → (ρ : Renameˣ) →
  Renameˣ-wt Γ Γ′ ρ →
  Renameˣ-wt (⤊ᵗ Γ) (⤊ᵗ Γ′) (liftᵗʳ ρ)
liftᵗʳ-wt {Γ′ = Γ′} ρ hρ {x = x} h with unmap∋-⤊ᵗ h
... | B , eq , h₀ =
  subst
    (λ T → ⤊ᵗ Γ′ ∋ ρ x ⦂ T)
    (sym eq)
    (map∋ (renameᵗ suc) (hρ h₀))

------------------------------------------------------------------------
-- Renaming and substitution actions on terms (term variables)
------------------------------------------------------------------------

renameˣᵐ : Renameˣ → Term → Term
renameˣᵐ ρ (` x) = ` (ρ x)
renameˣᵐ ρ (ƛ A ⇒ M) = ƛ A ⇒ renameˣᵐ (extʳ ρ) M
renameˣᵐ ρ (L · M) = renameˣᵐ ρ L · renameˣᵐ ρ M
renameˣᵐ ρ (Λ M) = Λ (renameˣᵐ (liftᵗʳ ρ) M)
renameˣᵐ ρ (M ⦂∀ B [ T ]) = renameˣᵐ ρ M ⦂∀ B [ T ]
renameˣᵐ ρ ($ κ) = $ κ
renameˣᵐ ρ (L ⊕[ op ] M) = renameˣᵐ ρ L ⊕[ op ] renameˣᵐ ρ M
renameˣᵐ ρ (M up p) = renameˣᵐ ρ M up p
renameˣᵐ ρ (M down p) = renameˣᵐ ρ M down p
renameˣᵐ ρ (blame ℓ) = blame ℓ

renameˣ-term-wt : ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx}{M : Term}{A : Ty} →
  (ρ : Renameˣ) →
  Renameˣ-wt Γ Γ′ ρ →
  (M⊢ : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A) →
  Δ ∣ Ψ ∣ Σ ∣ Γ′ ⊢ renameˣᵐ ρ M ⦂ A
renameˣ-term-wt ρ hρ (⊢` h) = ⊢` (hρ h)
renameˣ-term-wt ρ hρ (⊢ƛ {A = A} wfA M) =
  ⊢ƛ wfA (renameˣ-term-wt (extʳ ρ) (extʳ-wt ρ hρ) M)
renameˣ-term-wt ρ hρ (⊢· L M) =
  ⊢· (renameˣ-term-wt ρ hρ L) (renameˣ-term-wt ρ hρ M)
renameˣ-term-wt ρ hρ (⊢Λ M) =
  ⊢Λ (renameˣ-term-wt (liftᵗʳ ρ) (liftᵗʳ-wt ρ hρ) M)
renameˣ-term-wt ρ hρ (⊢• {B = B} M wfT) =
  ⊢• {B = B} (renameˣ-term-wt ρ hρ M) wfT
renameˣ-term-wt ρ hρ (⊢$ κ) = ⊢$ κ
renameˣ-term-wt ρ hρ (⊢⊕ L op M) =
  ⊢⊕ (renameˣ-term-wt ρ hρ L) op (renameˣ-term-wt ρ hρ M)
renameˣ-term-wt ρ hρ (⊢up {p = p} Φ M hp) =
  ⊢up {p = p} Φ (renameˣ-term-wt ρ hρ M) hp
renameˣ-term-wt ρ hρ (⊢down {p = p} Φ M hp) =
  ⊢down {p = p} Φ (renameˣ-term-wt ρ hρ M) hp
renameˣ-term-wt ρ hρ (⊢blame ℓ) = ⊢blame ℓ

↑ᵗᵐ : Substˣ → Substˣ
↑ᵗᵐ σ x = renameᵗᵐ suc (σ x)

↑ᵗᵐ-wt : ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx} →
  (σ : Substˣ) →
  Substˣ-wt {Δ} {Ψ} {Σ} {Γ} {Γ′} σ →
  Substˣ-wt {suc Δ} {Ψ} {⟰ᵗ Σ} {⤊ᵗ Γ} {⤊ᵗ Γ′} (↑ᵗᵐ σ)
↑ᵗᵐ-wt σ hσ {x = x} h with unmap∋-⤊ᵗ h
... | B , eq , h₀ =
  cong-⊢⦂
    refl
    refl
    refl
    (sym eq)
    (renameᵗ-term suc TyRenameWf-suc (hσ {x = x} h₀))

extˣ : Substˣ → Substˣ
extˣ σ zero = ` zero
extˣ σ (suc x) = renameˣᵐ wkʳ (σ x)

extˣ-wt : ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx}{A : Ty} →
  (σ : Substˣ) →
  (hσ : Substˣ-wt {Δ} {Ψ} {Σ} {Γ} {Γ′} σ) →
  Substˣ-wt {Δ} {Ψ} {Σ} {A ∷ Γ} {A ∷ Γ′} (extˣ σ)
extˣ-wt σ hσ Z = ⊢` Z
extˣ-wt σ hσ (S h) = renameˣ-term-wt wkʳ wkʳ-wt (hσ h)

substˣ-term : Substˣ → Term → Term
substˣ-term σ (` x) = σ x
substˣ-term σ (ƛ A ⇒ M) = ƛ A ⇒ substˣ-term (extˣ σ) M
substˣ-term σ (L · M) = substˣ-term σ L · substˣ-term σ M
substˣ-term σ (Λ M) = Λ (substˣ-term (↑ᵗᵐ σ) M)
substˣ-term σ (M ⦂∀ B [ T ]) = substˣ-term σ M ⦂∀ B [ T ]
substˣ-term σ ($ κ) = $ κ
substˣ-term σ (L ⊕[ op ] M) = substˣ-term σ L ⊕[ op ] substˣ-term σ M
substˣ-term σ (M up p) = substˣ-term σ M up p
substˣ-term σ (M down p) = substˣ-term σ M down p
substˣ-term σ (blame ℓ) = blame ℓ

substˣ-term-wt : ∀ {Δ Ψ}{Σ : Store}{Γ Γ′ : Ctx}{M : Term}{A : Ty} →
  (σ : Substˣ) →
  (hσ : Substˣ-wt {Δ} {Ψ} {Σ} {Γ} {Γ′} σ) →
  (M⊢ : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A) →
  Δ ∣ Ψ ∣ Σ ∣ Γ′ ⊢ substˣ-term σ M ⦂ A
substˣ-term-wt σ hσ (⊢` h) = hσ h
substˣ-term-wt σ hσ (⊢ƛ {A = A} wfA M) =
  ⊢ƛ wfA (substˣ-term-wt (extˣ σ) (extˣ-wt {A = A} σ hσ) M)
substˣ-term-wt σ hσ (⊢· L M) =
  ⊢· (substˣ-term-wt σ hσ L) (substˣ-term-wt σ hσ M)
substˣ-term-wt σ hσ (⊢Λ M) =
  ⊢Λ (substˣ-term-wt (↑ᵗᵐ σ) (↑ᵗᵐ-wt σ hσ) M)
substˣ-term-wt σ hσ (⊢• {B = B} M wfT) =
  ⊢• {B = B} (substˣ-term-wt σ hσ M) wfT
substˣ-term-wt σ hσ (⊢$ κ) = ⊢$ κ
substˣ-term-wt σ hσ (⊢⊕ L op M) =
  ⊢⊕ (substˣ-term-wt σ hσ L) op (substˣ-term-wt σ hσ M)
substˣ-term-wt σ hσ (⊢up {p = p} Φ M hp) =
  ⊢up {p = p} Φ (substˣ-term-wt σ hσ M) hp
substˣ-term-wt σ hσ (⊢down {p = p} Φ M hp) =
  ⊢down {p = p} Φ (substˣ-term-wt σ hσ M) hp
substˣ-term-wt σ hσ (⊢blame ℓ) = ⊢blame ℓ

------------------------------------------------------------------------
-- Single-variable and single-type substitution APIs
------------------------------------------------------------------------

infixl 8 _[_]
infixl 8 _[_]ᵀ

singleVarEnv : Term → Substˣ
singleVarEnv V zero = V
singleVarEnv V (suc x) = ` x

singleVarEnv-wt : ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{V : Term}{A : Ty} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ V ⦂ A →
  Substˣ-wt {Δ} {Ψ} {Σ} {A ∷ Γ} {Γ} (singleVarEnv V)
singleVarEnv-wt {V = V} V⊢ Z = V⊢
singleVarEnv-wt V⊢ (S h) = ⊢` h

_[_] : Term → Term → Term
N [ V ] = substˣ-term (singleVarEnv V) N

[]-wt : ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{N V : Term}{A B : Ty} →
  (N⊢ : Δ ∣ Ψ ∣ Σ ∣ (A ∷ Γ) ⊢ N ⦂ B) →
  (V⊢ : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ V ⦂ A) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (N [ V ]) ⦂ B
[]-wt {V = V} N⊢ V⊢ =
  substˣ-term-wt (singleVarEnv V) (singleVarEnv-wt V⊢) N⊢

map-singleTyEnv-⤊ᵗ : (T : Ty) (Γ : Ctx) →
  map (substᵗ (singleTyEnv T)) (⤊ᵗ Γ) ≡ Γ
map-singleTyEnv-⤊ᵗ T [] = refl
map-singleTyEnv-⤊ᵗ T (A ∷ Γ) =
  cong₂ _∷_
    (open-renᵗ-suc A T)
    (map-singleTyEnv-⤊ᵗ T Γ)

singleTyEnv-Wf : ∀ {Δ Ψ} (T : Ty) →
  WfTy Δ Ψ T →
  TySubstWf (suc Δ) Δ Ψ (singleTyEnv T)
singleTyEnv-Wf T wfT {zero} z<s = wfT
singleTyEnv-Wf T wfT {suc X} (s<s X<Δ) = wfVar X<Δ

_[_]ᵀ : Term → Ty → Term
M [ T ]ᵀ = substᵗᵐ (singleTyEnv T) M

[]ᵀ-wt :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{M : Term}{A : Ty} →
  (M⊢ : (suc Δ) ∣ Ψ ∣ ⟰ᵗ Σ ∣ (⤊ᵗ Γ) ⊢ M ⦂ A) →
  (T : Ty) →
  (wfT : WfTy Δ Ψ T) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (M [ T ]ᵀ) ⦂ (A [ T ]ᵗ)
[]ᵀ-wt {Σ = Σ} {Γ = Γ} {M = M} {A = A} M⊢ T wfT =
  cong-⊢⦂
    (substStoreᵗ-singleTyEnv-⟰ᵗ T Σ)
    (map-singleTyEnv-⤊ᵗ T Γ)
    refl
    refl
    (substᵗ-wt (singleTyEnv T) (singleTyEnv-Wf T wfT) M⊢)

------------------------------------------------------------------------
-- Permission-list well-formedness and practical renaming shortcut
------------------------------------------------------------------------

PermWf : SealCtx → List CastPerm → Set
PermWf Ψ P = ∀ {α} → α ∈ P → α < Ψ

PermWf-every :
  ∀ {Ψ} →
  PermWf Ψ (every Ψ)
PermWf-every = every-index

PermWf-ext-true :
  ∀ {Ψ}{P : List CastPerm} →
  PermWf Ψ P →
  PermWf (suc Ψ) (conv ∷ P)
PermWf-ext-true wfP {zero} here-conv = z<s
PermWf-ext-true wfP {suc α} (there p) = s<s (wfP p)

PermWf-ext-false :
  ∀ {Ψ}{P : List CastPerm} →
  PermWf Ψ P →
  PermWf (suc Ψ) (cast-tag ∷ P)
PermWf-ext-false wfP {zero} ()
PermWf-ext-false wfP {suc α} (there p) = s<s (wfP p)

RenOk-every-from-PermWf :
  ∀ {Ψ Ψ′} {ρ : Renameˢ} {P : List CastPerm} →
  SealRenameWf Ψ Ψ′ ρ →
  PermWf Ψ P →
  RenOk ρ P (every Ψ′)
RenOk-every-from-PermWf hρ wfP p = every-member _ (hρ (wfP p))

RenOk-ext-true-every :
  ∀ {Ψ′}{ρ : Renameˢ}{P : List CastPerm} →
  RenOk ρ P (every Ψ′) →
  RenOk (extˢ ρ) (conv ∷ P) (every (suc Ψ′))
RenOk-ext-true-every ok {zero} here-conv = here-conv
RenOk-ext-true-every ok {suc α} (there p) = there (ok p)

RenOk-ext-false-every :
  ∀ {Ψ′}{ρ : Renameˢ}{P : List CastPerm} →
  RenOk ρ P (every Ψ′) →
  RenOk (extˢ ρ) (cast-tag ∷ P) (every (suc Ψ′))
RenOk-ext-false-every ok {zero} ()
RenOk-ext-false-every ok {suc α} (there p) = there (ok p)

pred-< :
  ∀ {α Ψ} →
  suc α < suc Ψ →
  α < Ψ
pred-< (s<s α<Ψ) = α<Ψ

tail-PermWf :
  ∀ {Ψ}{b : CastPerm}{P : List CastPerm} →
  PermWf (suc Ψ) (b ∷ P) →
  PermWf Ψ P
tail-PermWf wf {α} p = pred-< (wf (there p))

shift-Renameˢ :
  Renameˢ →
  Renameˢ
shift-Renameˢ ρ α = ρ (suc α)

shift-SealRenameWf :
  ∀ {Ψ Ψ′}{ρ : Renameˢ} →
  SealRenameWf (suc Ψ) Ψ′ ρ →
  SealRenameWf Ψ Ψ′ (shift-Renameˢ ρ)
shift-SealRenameWf hρ α<Ψ = hρ (s<s α<Ψ)

setPerm :
  Seal →
  List CastPerm →
  List CastPerm
setPerm zero [] = conv ∷ []
setPerm zero (b ∷ P) = conv ∷ P
setPerm (suc α) [] = cast-tag ∷ setPerm α []
setPerm (suc α) (b ∷ P) = b ∷ setPerm α P

setPerm-hit :
  (α : Seal) →
  (P : List CastPerm) →
  α ∈ setPerm α P
setPerm-hit zero [] = here-conv
setPerm-hit zero (b ∷ P) = here-conv
setPerm-hit (suc α) [] = there (setPerm-hit α [])
setPerm-hit (suc α) (b ∷ P) = there (setPerm-hit α P)

setPerm-preserve :
  ∀ {α β}{P : List CastPerm} →
  β ∈ P →
  β ∈ setPerm α P
setPerm-preserve {α = zero} {β = zero} here-conv = here-conv
setPerm-preserve {α = zero} {β = zero} here-seal = here-conv
setPerm-preserve {α = zero} {β = suc β} (there p) = there p
setPerm-preserve {α = suc α} {β = zero} here-conv = here-conv
setPerm-preserve {α = suc α} {β = zero} here-seal = here-seal
setPerm-preserve {α = suc α} {β = suc β} (there p) =
  there (setPerm-preserve {α = α} {β = β} p)

renamePerm :
  ∀ {Ψ Ψ′} →
  (ρ : Renameˢ) →
  SealRenameWf Ψ Ψ′ ρ →
  List CastPerm →
  List CastPerm
renamePerm {Ψ = zero} {Ψ′ = Ψ′} ρ hρ P = none Ψ′
renamePerm {Ψ = suc Ψ} ρ hρ [] =
  renamePerm
    {Ψ = Ψ}
    (shift-Renameˢ ρ)
    (shift-SealRenameWf hρ)
    []
renamePerm {Ψ = suc Ψ} ρ hρ (cast-tag ∷ P) =
  renamePerm
    {Ψ = Ψ}
    (shift-Renameˢ ρ)
    (shift-SealRenameWf hρ)
    P
renamePerm {Ψ = suc Ψ} ρ hρ (conv ∷ P) =
  setPerm
    (ρ zero)
    (renamePerm
      {Ψ = Ψ}
      (shift-Renameˢ ρ)
      (shift-SealRenameWf hρ)
      P)
renamePerm {Ψ = suc Ψ} ρ hρ (cast-seal ∷ P) =
  setPerm
    (ρ zero)
    (renamePerm
      {Ψ = Ψ}
      (shift-Renameˢ ρ)
      (shift-SealRenameWf hρ)
      P)

renamePerm-ok :
  ∀ {Ψ Ψ′} {ρ : Renameˢ} {P : List CastPerm} →
  (hρ : SealRenameWf Ψ Ψ′ ρ) →
  PermWf Ψ P →
  RenOk ρ P (renamePerm ρ hρ P)
renamePerm-ok {Ψ = zero} hρ wfP {α} α∈P with wfP α∈P
renamePerm-ok {Ψ = zero} hρ wfP {α} α∈P | ()
renamePerm-ok {Ψ = suc Ψ} {ρ = ρ} {P = []} hρ wfP {α} ()
renamePerm-ok {Ψ = suc Ψ} {ρ = ρ} {P = cast-tag ∷ P} hρ wfP {zero} ()
renamePerm-ok {Ψ = suc Ψ} {ρ = ρ} {P = cast-tag ∷ P} hρ wfP {suc α} (there α∈P) =
  renamePerm-ok
    (shift-SealRenameWf hρ)
    (tail-PermWf wfP)
    α∈P
renamePerm-ok {Ψ = suc Ψ} {ρ = ρ} {P = conv ∷ P} hρ wfP {zero} here-conv =
  setPerm-hit
    (ρ zero)
    (renamePerm
      {Ψ = Ψ}
      (shift-Renameˢ ρ)
      (shift-SealRenameWf hρ)
      P)
renamePerm-ok {Ψ = suc Ψ} {ρ = ρ} {P = conv ∷ P} hρ wfP {suc α} (there α∈P) =
  setPerm-preserve
    (renamePerm-ok
      (shift-SealRenameWf hρ)
      (tail-PermWf wfP)
      α∈P)
renamePerm-ok {Ψ = suc Ψ} {ρ = ρ} {P = cast-seal ∷ P} hρ wfP {zero} here-seal =
  setPerm-hit
    (ρ zero)
    (renamePerm
      {Ψ = Ψ}
      (shift-Renameˢ ρ)
      (shift-SealRenameWf hρ)
      P)
renamePerm-ok {Ψ = suc Ψ} {ρ = ρ} {P = cast-seal ∷ P} hρ wfP {suc α} (there α∈P) =
  setPerm-preserve
    (renamePerm-ok
      (shift-SealRenameWf hρ)
      (tail-PermWf wfP)
      α∈P)
