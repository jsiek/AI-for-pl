module alt.ThetaTermSubst where

-- File Charter:
--   * Proves typing preservation for parallel term renaming and
--     regular-context injection renaming in the Θ-indexed calculus.
--   * Defines the action of regular-context injections on binder telescopes
--     and proves typing preservation for the general term action
--     `renameᵗᵐ` from alt.ThetaReduction.
--   * DEVIATION / OBSTRUCTION: the requested literal Λ-descent weakening and
--     hence unrestricted `⊢subst`/`⊢[]` are false for the present `TyEnv`-
--     indexed crossing rules.  If Ψ ends in `,typ[ Y ]`, weakening a conceal
--     node maps its slot to `suc Y`, so its typing conclusion must end in
--     `,typ[ suc Y ]`; the requested target `Ψ ,typ[ zero ]` ends in a
--     different constructor argument.  This file states the valid canonical
--     weakening corollary under `renameTyEnv wk↪ᵗ Ψ`; it uses no assumption
--     or purported substitution theorem to hide that mismatch.
--   * The requested `∋:=-transport` itself is valid and stated below, but the
--     whole-term `⊢shiftᶿ` is blocked by the same conceal/telescope
--     inversion:
--     `Ψ ,:= B` ends in `,:=` when a conceal conclusion must end in `,typ`.

open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)
  renaming (subst to subst≡)

open import Types
open import TermCtx
open import Consistency
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction

private
  variable
    Θ Θ′ : AnchorCtx
    Δ Δ′ : TyCtx
    Ψ Ψ′ : TyEnv Θ Δ
    Γ Γ′ : TermCtx Δ
    A B C : Ty Δ
    L M N : Term Θ Δ

------------------------------------------------------------------------
-- Injection identities used by telescope and conversion transport
------------------------------------------------------------------------

toRename-keep-eq : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) X
  → toRenameᵗ (keep ρ) X ≡ extᵗ (toRenameᵗ ρ) X
toRename-keep-eq ρ zero = refl
toRename-keep-eq ρ (suc X) = refl

toRename-id-eq : ∀ {Δ} (X : TyVar Δ)
  → toRenameᵗ id↪ᵗ X ≡ X
toRename-id-eq {zero} ()
toRename-id-eq {suc Δ} zero = refl
toRename-id-eq {suc Δ} (suc X) = cong suc (toRename-id-eq X)

toRename-wk-eq : ∀ {Δ} (X : TyVar Δ)
  → toRenameᵗ wk↪ᵗ X ≡ suc X
toRename-wk-eq X = cong suc (toRename-id-eq X)

renameᵗ-wk-eq : ∀ {Δ} (A : Ty Δ)
  → renameᵗ (toRenameᵗ wk↪ᵗ) A ≡ ⇑ᵗ A
renameᵗ-wk-eq A = renameᵗ-cong A toRename-wk-eq

delete-insert↪ᵗ : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Y : TyVar (suc Δ))
  → delete↪ᵗ (insert↪ᵗ ρ Y) Y ≡ ρ
delete-insert↪ᵗ ρ zero = refl
delete-insert↪ᵗ (keep ρ) (suc Y) =
  cong keep (delete-insert↪ᵗ ρ Y)
delete-insert↪ᵗ (skip ρ) (suc Y) =
  cong skip (delete-insert↪ᵗ ρ (suc Y))

insert-punchIn : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Y : TyVar (suc Δ)) (X : TyVar Δ)
  → toRenameᵗ (insert↪ᵗ ρ Y) (punchIn Y X)
    ≡ punchIn (toRenameᵗ (insert↪ᵗ ρ Y) Y) (toRenameᵗ ρ X)
insert-punchIn ρ zero X = refl
insert-punchIn (keep ρ) (suc Y) zero = refl
insert-punchIn (keep ρ) (suc Y) (suc X) =
  cong suc (insert-punchIn ρ Y X)
insert-punchIn (skip ρ) (suc Y) X =
  cong suc (insert-punchIn ρ (suc Y) X)

delete-punchIn : ∀ {Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y : TyVar (suc Δ)) (X : TyVar Δ)
  → toRenameᵗ ρ (punchIn Y X)
    ≡ punchIn (toRenameᵗ ρ Y) (toRenameᵗ (delete↪ᵗ ρ Y) X)
delete-punchIn (keep ρ) zero X = refl
delete-punchIn (keep (keep ρ)) (suc Y) zero = refl
delete-punchIn (keep (keep ρ)) (suc Y) (suc X) =
  cong suc (delete-punchIn (keep ρ) Y X)
delete-punchIn (keep (skip ρ)) (suc Y) zero = refl
delete-punchIn (keep (skip ρ)) (suc Y) (suc X) =
  cong suc (delete-punchIn (skip ρ) Y X)
delete-punchIn (skip (keep ρ)) Y X =
  cong suc (delete-punchIn (keep ρ) Y X)
delete-punchIn (skip (skip ρ)) Y X =
  cong suc (delete-punchIn (skip ρ) Y X)

rename-insert-wk : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Y : TyVar (suc Δ)) (A : Ty Δ)
  → renameᵗ (toRenameᵗ (insert↪ᵗ ρ Y)) (wkᵗ Y A)
    ≡ wkᵗ (toRenameᵗ (insert↪ᵗ ρ Y) Y)
        (renameᵗ (toRenameᵗ ρ) A)
rename-insert-wk ρ Y A =
  trans (renameᵗ-comp (punchIn Y)
           (toRenameᵗ (insert↪ᵗ ρ Y)) A)
    (trans (renameᵗ-cong A (insert-punchIn ρ Y))
      (sym (renameᵗ-comp (toRenameᵗ ρ)
        (punchIn (toRenameᵗ (insert↪ᵗ ρ Y) Y)) A)))

rename-delete-wk : ∀ {Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y : TyVar (suc Δ)) (A : Ty Δ)
  → renameᵗ (toRenameᵗ ρ) (wkᵗ Y A)
    ≡ wkᵗ (toRenameᵗ ρ Y)
        (renameᵗ (toRenameᵗ (delete↪ᵗ ρ Y)) A)
rename-delete-wk ρ Y A =
  trans (renameᵗ-comp (punchIn Y) (toRenameᵗ ρ) A)
    (trans (renameᵗ-cong A (delete-punchIn ρ Y))
      (sym (renameᵗ-comp (toRenameᵗ (delete↪ᵗ ρ Y))
        (punchIn (toRenameᵗ ρ Y)) A)))

------------------------------------------------------------------------
-- Conversion typing under regular-context injections
------------------------------------------------------------------------

renameAtom : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {A : Ty Δ}
  → Atom A
  → Atom (renameᵗ ρ A)
renameAtom ρ (＇ X) = ＇ ρ X
renameAtom ρ (‵ ι) = ‵ ι
renameAtom ρ ★ = ★

mutual
  rename-⊢↑ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′)
      {X : TyVar Δ} {R A B : Ty Δ} {c : Reveal}
    → ⊢↑[ X ⦂ R ] c ⦂ A ↝ B
    → ⊢↑[ ρ X ⦂ renameᵗ ρ R ] c
        ⦂ renameᵗ ρ A ↝ renameᵗ ρ B
  rename-⊢↑ ρ ⊢unseal = ⊢unseal
  rename-⊢↑ ρ (⊢↑-⇒ c⊢ d⊢) =
    ⊢↑-⇒ (rename-⊢↓ ρ c⊢) (rename-⊢↑ ρ d⊢)
  rename-⊢↑ ρ (⊢↑-∀ {R = R} c⊢) =
    ⊢↑-∀
      (subst≡
        (λ R′ → ⊢↑[ suc _ ⦂ R′ ] _ ⦂ _ ↝ _)
        (renameᵗ-shift ρ R)
        (rename-⊢↑ (extᵗ ρ) c⊢))
  rename-⊢↑ ρ (⊢id↑ a) = ⊢id↑ (renameAtom ρ a)

  rename-⊢↓ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′)
      {X : TyVar Δ} {R A B : Ty Δ} {c : Conceal}
    → ⊢↓[ X ⦂ R ] c ⦂ A ↝ B
    → ⊢↓[ ρ X ⦂ renameᵗ ρ R ] c
        ⦂ renameᵗ ρ A ↝ renameᵗ ρ B
  rename-⊢↓ ρ ⊢seal = ⊢seal
  rename-⊢↓ ρ (⊢↓-⇒ c⊢ d⊢) =
    ⊢↓-⇒ (rename-⊢↑ ρ c⊢) (rename-⊢↓ ρ d⊢)
  rename-⊢↓ ρ (⊢↓-∀ {R = R} c⊢) =
    ⊢↓-∀
      (subst≡
        (λ R′ → ⊢↓[ suc _ ⦂ R′ ] _ ⦂ _ ↝ _)
        (renameᵗ-shift ρ R)
        (rename-⊢↓ (extᵗ ρ) c⊢))
  rename-⊢↓ ρ (⊢id↓ a) = ⊢id↓ (renameAtom ρ a)

------------------------------------------------------------------------
-- Term-variable renaming preserves typing
------------------------------------------------------------------------

ext-∋ : ∀ {Δ} {Γ Γ′ : TermCtx Δ} {ρ : Rename} {A : Ty Δ}
  → (∀ {x B} → Γ ∋ x ⦂ B → Γ′ ∋ ρ x ⦂ B)
  → ∀ {x B} → A ∷ Γ ∋ x ⦂ B → A ∷ Γ′ ∋ ext ρ x ⦂ B
ext-∋ hρ Z = Z
ext-∋ hρ (S x∈) = S (hρ x∈)

lookup-renameCtx-inv : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
    {Γ : TermCtx Δ} {x A}
  → renameCtx ρ Γ ∋ x ⦂ A
  → ∃[ B ] (Γ ∋ x ⦂ B × renameᵗ ρ B ≡ A)
lookup-renameCtx-inv {Γ = B ∷ Γ} Z = B , Z , refl
lookup-renameCtx-inv {Γ = C ∷ Γ} (S x∈)
    with lookup-renameCtx-inv x∈
lookup-renameCtx-inv {Γ = C ∷ Γ} (S x∈) | B , B∈ , refl =
  B , S B∈ , refl

renameCtx-∋ : ∀ {Δ Δ′} {ρᵗ : Δ ⇒ʳ Δ′}
    {Γ Γ′ : TermCtx Δ} {ρ : Rename}
  → (∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A)
  → ∀ {x A}
  → renameCtx ρᵗ Γ ∋ x ⦂ A
  → renameCtx ρᵗ Γ′ ∋ ρ x ⦂ A
renameCtx-∋ hρ x∈ with lookup-renameCtx-inv x∈
renameCtx-∋ {ρᵗ = ρᵗ} hρ x∈ | B , B∈ , refl =
  renameᵗ-∋ ρᵗ (hρ B∈)

⊢rename : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ Γ′ : TermCtx Δ}
    {ρ : Rename} {M : Term Θ Δ} {B : Ty Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A)
  → Ψ ∣ Γ ⊢ M ⦂ B
  → Ψ ∣ Γ′ ⊢ rename ρ M ⦂ B
⊢rename hρ (⊢` x∈) = ⊢` (hρ x∈)
⊢rename hρ (⊢ƛ M⊢) = ⊢ƛ (⊢rename (ext-∋ hρ) M⊢)
⊢rename hρ (⊢· L⊢ M⊢) =
  ⊢· (⊢rename hρ L⊢) (⊢rename hρ M⊢)
⊢rename hρ (⊢Λ M⊢) = ⊢Λ (⊢rename (renameCtx-∋ hρ) M⊢)
⊢rename hρ (⊢⦂∀ L⊢) = ⊢⦂∀ (⊢rename hρ L⊢)
⊢rename hρ (⊢$ κ) = ⊢$ κ
⊢rename hρ (⊢⊕ op L⊢ M⊢) =
  ⊢⊕ op (⊢rename hρ L⊢) (⊢rename hρ M⊢)
⊢rename hρ (⊢⟨⟩ M⊢ c) = ⊢⟨⟩ (⊢rename hρ M⊢) c
⊢rename hρ (⊢ν M⊢) = ⊢ν M⊢
⊢rename hρ (⊢reveal α∈ c⊢ M⊢) = ⊢reveal α∈ c⊢ M⊢
⊢rename hρ (⊢conceal α∈ c⊢ M⊢) = ⊢conceal α∈ c⊢ M⊢
⊢rename hρ ⊢blame = ⊢blame

⊢rename-suc : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A B : Ty Δ}
  → Ψ ∣ Γ ⊢ M ⦂ A
  → Ψ ∣ B ∷ Γ ⊢ rename suc M ⦂ A
⊢rename-suc M⊢ = ⊢rename (λ x∈ → S x∈) M⊢

------------------------------------------------------------------------
-- Regular-context injections act on binder telescopes
------------------------------------------------------------------------

emptyTyEnv : ∀ {Θ} (Δ : TyCtx) → TyEnv Θ zero → TyEnv Θ Δ
emptyTyEnv zero Ψ = Ψ
emptyTyEnv (suc Δ) Ψ = emptyTyEnv Δ Ψ ,typ[ zero ]

renameTyEnv : ∀ {Θ Δ Δ′}
  → Δ ↪ᵗ Δ′
  → TyEnv Θ Δ
  → TyEnv Θ Δ′
renameTyEnv {Δ′ = Δ′} ρ ∅ = emptyTyEnv Δ′ ∅
renameTyEnv ρ (Ψ ,:= A) =
  renameTyEnv ρ Ψ ,:= renameᵗ (toRenameᵗ ρ) A
renameTyEnv (keep ρ) (Ψ ,typ[ Y ]) =
  renameTyEnv (delete↪ᵗ (keep ρ) Y) Ψ
    ,typ[ toRenameᵗ (keep ρ) Y ]
renameTyEnv (skip ρ) (Ψ ,typ[ Y ]) =
  renameTyEnv (delete↪ᵗ (skip ρ) Y) Ψ
    ,typ[ toRenameᵗ (skip ρ) Y ]

renameTyEnv-insert : ∀ {Θ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Ψ : TyEnv Θ Δ) (Y : TyVar (suc Δ))
  → renameTyEnv (insert↪ᵗ ρ Y) (Ψ ,typ[ Y ])
    ≡ renameTyEnv ρ Ψ ,typ[ toRenameᵗ (insert↪ᵗ ρ Y) Y ]
renameTyEnv-insert ρ Ψ zero = refl
renameTyEnv-insert (keep ρ) Ψ (suc Y)
    rewrite delete-insert↪ᵗ ρ Y =
  refl
renameTyEnv-insert (skip ρ) Ψ (suc Y)
    rewrite delete-insert↪ᵗ ρ (suc Y) =
  refl

rename-∋:= : ∀ {Θ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    {Ψ : TyEnv Θ Δ} {α : TyVar Θ} {A : Ty Δ}
  → Ψ ∋ α := A
  → renameTyEnv ρ Ψ ∋ α := renameᵗ (toRenameᵗ ρ) A
rename-∋:= ρ Z = Z
rename-∋:= ρ (S α∈) = S (rename-∋:= ρ α∈)
rename-∋:= (keep ρ) (skip-typ {Ψ = Ψ} {A = A} {Y = Y} α∈) =
  subst≡
    (λ C → renameTyEnv (keep ρ) (Ψ ,typ[ Y ]) ∋ _ := C)
    (sym (rename-delete-wk (keep ρ) Y A))
    (skip-typ (rename-∋:= (delete↪ᵗ (keep ρ) Y) α∈))
rename-∋:= (skip ρ) (skip-typ {Ψ = Ψ} {A = A} {Y = Y} α∈) =
  subst≡
    (λ C → renameTyEnv (skip ρ) (Ψ ,typ[ Y ]) ∋ _ := C)
    (sym (rename-delete-wk (skip ρ) Y A))
    (skip-typ (rename-∋:= (delete↪ᵗ (skip ρ) Y) α∈))

------------------------------------------------------------------------
-- Type-variable renaming preserves typing
------------------------------------------------------------------------

renameCtx-keep-shift : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Γ : TermCtx Δ)
  → renameCtx (toRenameᵗ (keep ρ)) (renameCtx suc Γ)
    ≡ renameCtx suc (renameCtx (toRenameᵗ ρ) Γ)
renameCtx-keep-shift ρ [] = refl
renameCtx-keep-shift ρ (A ∷ Γ) =
  cong₂ _∷_
    (trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq ρ))
      (renameᵗ-shift (toRenameᵗ ρ) A))
    (renameCtx-keep-shift ρ Γ)

rename-open↪ᵗ : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (C : Ty (suc Δ)) (A : Ty Δ)
  → renameᵗ (toRenameᵗ ρ) (C [ A ]ᵗ)
    ≡ renameᵗ (toRenameᵗ (keep ρ)) C
        [ renameᵗ (toRenameᵗ ρ) A ]ᵗ
rename-open↪ᵗ ρ C A =
  trans (renameᵗ-subst (toRenameᵗ ρ) (singleSubᵗ A) C)
    (trans (substᵗ-cong C env-eq)
      (sym (substᵗ-rename
        (singleSubᵗ (renameᵗ (toRenameᵗ ρ) A))
        (toRenameᵗ (keep ρ)) C)))
  where
  env-eq : ∀ X
    → renameᵗ (toRenameᵗ ρ) (singleSubᵗ A X)
      ≡ singleSubᵗ (renameᵗ (toRenameᵗ ρ) A)
          (toRenameᵗ (keep ρ) X)
  env-eq zero = refl
  env-eq (suc X) = refl

⊢renameᵗᵐ : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → Ψ ∣ Γ ⊢ M ⦂ A
  → renameTyEnv ρ Ψ ∣ renameCtx (toRenameᵗ ρ) Γ
      ⊢ renameᵗᵐ ρ M ⦂ renameᵗ (toRenameᵗ ρ) A
⊢renameᵗᵐ (⊢` x∈) = ⊢` (renameᵗ-∋ _ x∈)
⊢renameᵗᵐ (⊢ƛ M⊢) = ⊢ƛ (⊢renameᵗᵐ M⊢)
⊢renameᵗᵐ (⊢· L⊢ M⊢) =
  ⊢· (⊢renameᵗᵐ L⊢) (⊢renameᵗᵐ M⊢)
⊢renameᵗᵐ {ρ = ρ} {Ψ = Ψ} {Γ = Γ} (⊢Λ {A = A} M⊢) =
  ⊢Λ body⊢
  where
  renamed-body⊢ = ⊢renameᵗᵐ M⊢

  body-context⊢ =
    subst≡
      (λ Γ′ → renameTyEnv ρ Ψ ,typ[ zero ] ∣ Γ′
        ⊢ renameᵗᵐ (keep ρ) _ ⦂ _)
      (renameCtx-keep-shift ρ Γ) renamed-body⊢

  body⊢ =
    subst≡
      (λ B → renameTyEnv ρ Ψ ,typ[ zero ] ∣
        renameCtx suc (renameCtx (toRenameᵗ ρ) Γ)
          ⊢ renameᵗᵐ (keep ρ) _ ⦂ B)
      (renameᵗ-cong A (toRename-keep-eq ρ)) body-context⊢
⊢renameᵗᵐ {Δ′ = Δ′} {ρ = ρ} {Ψ = Ψ} {Γ = Γ}
    {M = L ⦂∀ C [ A ]} (⊢⦂∀ L⊢) =
  subst≡
    (λ B → renameTyEnv ρ Ψ ∣ renameCtx (toRenameᵗ ρ) Γ
      ⊢ renameᵗᵐ ρ L ⦂∀ renameᵗ (toRenameᵗ (keep ρ)) C
        [ renameᵗ (toRenameᵗ ρ) A ] ⦂ B)
    result-eq (⊢⦂∀ body⊢)
  where
  body-eq = renameᵗ-cong C (toRename-keep-eq ρ)

  body⊢ =
    subst≡
      (λ B → renameTyEnv ρ Ψ ∣ renameCtx (toRenameᵗ ρ) Γ
        ⊢ renameᵗᵐ ρ L ⦂ `∀ B)
      (sym body-eq) (⊢renameᵗᵐ L⊢)

  result-eq = sym (rename-open↪ᵗ ρ C A)
⊢renameᵗᵐ {ρ = ρ} (⊢$ κ) =
  subst≡ (λ A → _ ∣ _ ⊢ $ κ ⦂ A)
    (constTy-renameᵗ (toRenameᵗ ρ) κ) (⊢$ κ)
⊢renameᵗᵐ (⊢⊕ addℕ L⊢ M⊢) =
  ⊢⊕ addℕ (⊢renameᵗᵐ L⊢) (⊢renameᵗᵐ M⊢)
⊢renameᵗᵐ (⊢⊕ and𝔹 L⊢ M⊢) =
  ⊢⊕ and𝔹 (⊢renameᵗᵐ L⊢) (⊢renameᵗᵐ M⊢)
⊢renameᵗᵐ {ρ = ρ} (⊢⟨⟩ M⊢ c) =
  ⊢⟨⟩ (⊢renameᵗᵐ M⊢) (renameᵐᶜ ρ c)
⊢renameᵗᵐ (⊢ν M⊢) = ⊢ν (⊢renameᵗᵐ M⊢)
⊢renameᵗᵐ {ρ = ρ}
    (⊢reveal {A = A} {B = B} {C = C} {Y = Y} α∈ c⊢ M⊢) =
  ⊢reveal (rename-∋:= ρ α∈) conversion⊢ body⊢
  where
  ρ⁺ = insert↪ᵗ ρ Y
  Y′ = toRenameᵗ ρ⁺ Y

  body⊢ =
    subst≡
      (λ Ψ′ → Ψ′ ∣ [] ⊢ renameᵗᵐ ρ⁺ _
        ⦂ renameᵗ (toRenameᵗ ρ⁺) A)
      (renameTyEnv-insert ρ _ Y) (⊢renameᵗᵐ M⊢)

  conversion-representation⊢ =
    subst≡
      (λ R → ⊢↑[ Y′ ⦂ R ] _
        ⦂ renameᵗ (toRenameᵗ ρ⁺) A
        ↝ renameᵗ (toRenameᵗ ρ⁺) (wkᵗ Y B))
      (rename-insert-wk ρ Y C)
      (rename-⊢↑ (toRenameᵗ ρ⁺) c⊢)

  conversion⊢ =
    subst≡
      (λ B′ →
        ⊢↑[ Y′ ⦂ wkᵗ Y′ (renameᵗ (toRenameᵗ ρ) C) ] _
          ⦂ renameᵗ (toRenameᵗ ρ⁺) A ↝ B′)
      (rename-insert-wk ρ Y B) conversion-representation⊢
⊢renameᵗᵐ {ρ = keep ρ}
    (⊢conceal {A = A} {C = C} {B = B} {Y = Y} α∈ c⊢ M⊢) =
  ⊢conceal (rename-∋:= ρ⁻ α∈) conversion⊢ (⊢renameᵗᵐ M⊢)
  where
  ρ⁻ = delete↪ᵗ (keep ρ) Y
  Y′ = toRenameᵗ (keep ρ) Y

  conversion-representation⊢ =
    subst≡
      (λ R → ⊢↓[ Y′ ⦂ R ] _
        ⦂ renameᵗ (toRenameᵗ (keep ρ)) (wkᵗ Y A)
        ↝ renameᵗ (toRenameᵗ (keep ρ)) B)
      (rename-delete-wk (keep ρ) Y C)
      (rename-⊢↓ (toRenameᵗ (keep ρ)) c⊢)

  conversion⊢ =
    subst≡
      (λ A′ →
        ⊢↓[ Y′ ⦂ wkᵗ Y′ (renameᵗ (toRenameᵗ ρ⁻) C) ] _
          ⦂ A′ ↝ renameᵗ (toRenameᵗ (keep ρ)) B)
      (rename-delete-wk (keep ρ) Y A) conversion-representation⊢
⊢renameᵗᵐ {ρ = skip ρ}
    (⊢conceal {A = A} {C = C} {B = B} {Y = Y} α∈ c⊢ M⊢) =
  ⊢conceal (rename-∋:= ρ⁻ α∈) conversion⊢ (⊢renameᵗᵐ M⊢)
  where
  ρ⁻ = delete↪ᵗ (skip ρ) Y
  Y′ = toRenameᵗ (skip ρ) Y

  conversion-representation⊢ =
    subst≡
      (λ R → ⊢↓[ Y′ ⦂ R ] _
        ⦂ renameᵗ (toRenameᵗ (skip ρ)) (wkᵗ Y A)
        ↝ renameᵗ (toRenameᵗ (skip ρ)) B)
      (rename-delete-wk (skip ρ) Y C)
      (rename-⊢↓ (toRenameᵗ (skip ρ)) c⊢)

  conversion⊢ =
    subst≡
      (λ A′ →
        ⊢↓[ Y′ ⦂ wkᵗ Y′ (renameᵗ (toRenameᵗ ρ⁻) C) ] _
          ⦂ A′ ↝ renameᵗ (toRenameᵗ (skip ρ)) B)
      (rename-delete-wk (skip ρ) Y A) conversion-representation⊢
⊢renameᵗᵐ ⊢blame = ⊢blame

------------------------------------------------------------------------
-- Canonical regular-context weakening corollary
------------------------------------------------------------------------

-- DEVIATION FROM THE REQUESTED Λ-DESCENT STATEMENT:
-- The valid corollary has the canonical telescope `renameTyEnv wk↪ᵗ Ψ`.
-- In general it cannot be replaced by `Ψ ,typ[ zero ]`.  If Ψ itself ends
-- in `,typ[ Y ]`, a well-typed conceal node weakens to slot `suc Y`, whose
-- typing conclusion must end in `,typ[ suc Y ]`; `Ψ ,typ[ zero ]` instead
-- ends in `,typ[ zero ]`.  Consequently the unrestricted PLFA `⊢subst`
-- requested below is also blocked in its Λ case: `liftˢ` uses precisely this
-- false outside-last weakening judgment.

renameCtx-wk-eq : ∀ {Δ} (Γ : TermCtx Δ)
  → renameCtx (toRenameᵗ wk↪ᵗ) Γ ≡ renameCtx suc Γ
renameCtx-wk-eq [] = refl
renameCtx-wk-eq (A ∷ Γ) =
  cong₂ _∷_ (renameᵗ-wk-eq A) (renameCtx-wk-eq Γ)

⊢weakenᵗᵐ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → Ψ ∣ Γ ⊢ M ⦂ A
  → renameTyEnv wk↪ᵗ Ψ ∣ renameCtx suc Γ
      ⊢ weakenᵗᵐ zero M ⦂ ⇑ᵗ A
⊢weakenᵗᵐ {Ψ = Ψ} {Γ = Γ} {M = M} {A = A} M⊢ =
  subst≡
    (λ B → renameTyEnv wk↪ᵗ Ψ ∣ renameCtx suc Γ
      ⊢ weakenᵗᵐ zero M ⦂ B)
    (renameᵗ-wk-eq A)
    (subst≡
      (λ Γ′ → renameTyEnv wk↪ᵗ Ψ ∣ Γ′
        ⊢ weakenᵗᵐ zero M ⦂ renameᵗ (toRenameᵗ wk↪ᵗ) A)
      (renameCtx-wk-eq Γ)
      (⊢renameᵗᵐ {ρ = wk↪ᵗ} M⊢))

------------------------------------------------------------------------
-- Anchor lookup weakening (whole-term weakening is obstructed above)
------------------------------------------------------------------------

∋:=-shift : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {α : TyVar Θ} {A B : Ty Δ}
  → Ψ ∋ α := A
  → (Ψ ,:= B) ∋ suc α := A
∋:=-shift = S
