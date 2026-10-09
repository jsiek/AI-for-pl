module proof.DGG.ImprecisionTypingProof where

-- File Charter:
--   * PROOF of `ImprecisionTyping` (ImprecisionTypingDef): a `⊑`
--     derivation gives both typings, by induction on the derivation.
--     Each rule carries exactly the side premises the typing rule needs
--     (TermImprecision's charter); the one-sided boundary rules type a
--     term-closed interior at `[]`, which `⊢closed` (CtxWeaken) moves to
--     the conclusion's term context.  Slots (design.md D31) change no
--     typing: a join's premise types the body at `underΛ Δ`, as `Λ⊑`'s
--     fresh binder does, and the premise of `⊑⟪⟫` with new slots types
--     the left term itself; a boundary's permissions K change only
--     marks.
--   * No module parameters: the proof uses no other DGG lemma.
--   * Orientation: the LEFT term is the more precise one.

open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; sym)

open import Types using (Ty; ⇑ᵗ)
open import Ctx using (Ctxᵗ; underΛ)
open import Terms
open import ImprecisionWorld
open import TermImprecision
open import proof.DGG.CtxWeaken using (⊢closed)
open import proof.DGG.ImprecisionTypingDef using (ImprecisionTyping)

private
  variable
    Δ Δ′ : Ctxᵗ

∋ʷ-lhs : ∀ {ns ns′ n μ} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
    {γ : Entries μ ηᴸ ηᴿ} {x A A′ p}
  → γ ∋ʷ x ⦂ ctx-imp A A′ p → lhs γ ∋ x ⦂ A
∋ʷ-lhs Zʷ     = here
∋ʷ-lhs (Sʷ x) = there (∋ʷ-lhs x)

∋ʷ-rhs : ∀ {ns ns′ n μ} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
    {γ : Entries μ ηᴸ ηᴿ} {x A A′ p}
  → γ ∋ʷ x ⦂ ctx-imp A A′ p → rhs γ ∋ x ⦂ A′
∋ʷ-rhs Zʷ     = here
∋ʷ-rhs (Sʷ x) = there (∋ʷ-rhs x)

lift-lhs : ∀ {ns ns′ n μ ns₁ ns′₁ n₁ μ₁} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
    {ηᴸ₁ : ns₁ ↪ n₁} {ηᴿ₁ : ns′₁ ↪ n₁}
    {γ : Entries μ ηᴸ ηᴿ} {γ′ : Entries μ₁ ηᴸ₁ ηᴿ₁}
  → LiftCtx γ γ′ → lhs γ′ ≡ ⤊ (lhs γ)
lift-lhs lift-[]    = refl
lift-lhs (lift-∷ l) = cong (_ ∷_) (lift-lhs l)

lift-rhs : ∀ {ns ns′ n μ ns₁ ns′₁ n₁ μ₁} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
    {ηᴸ₁ : ns₁ ↪ n₁} {ηᴿ₁ : ns′₁ ↪ n₁}
    {γ : Entries μ ηᴸ ηᴿ} {γ′ : Entries μ₁ ηᴸ₁ ηᴿ₁}
  → LiftCtx γ γ′ → rhs γ′ ≡ ⤊ (rhs γ)
lift-rhs lift-[]    = refl
lift-rhs (lift-∷ l) = cong (_ ∷_) (lift-rhs l)

liftᴸ-lhs : ∀ {ns ns′ n μ ns₁ n₁ μ₁} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
    {ηᴸ₁ : ns₁ ↪ n₁} {ηᴿ₁ : ns′ ↪ n₁}
    {γ : Entries μ ηᴸ ηᴿ} {γ′ : Entries μ₁ ηᴸ₁ ηᴿ₁}
  → LiftCtxᴸ γ γ′ → lhs γ′ ≡ ⤊ (lhs γ)
liftᴸ-lhs liftᴸ-[]    = refl
liftᴸ-lhs (liftᴸ-∷ l) = cong (_ ∷_) (liftᴸ-lhs l)

liftᴸ-rhs : ∀ {ns ns′ n μ ns₁ n₁ μ₁} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
    {ηᴸ₁ : ns₁ ↪ n₁} {ηᴿ₁ : ns′ ↪ n₁}
    {γ : Entries μ ηᴸ ηᴿ} {γ′ : Entries μ₁ ηᴸ₁ ηᴿ₁}
  → LiftCtxᴸ γ γ′ → rhs γ′ ≡ rhs γ
liftᴸ-rhs liftᴸ-[]    = refl
liftᴸ-rhs (liftᴸ-∷ l) = cong (_ ∷_) (liftᴸ-rhs l)

⊢Γ-cast : ∀ {Δ Γ Γ′ M A} → Γ ≡ Γ′ → Δ ∣ Γ ⊢ M ⦂ A → Δ ∣ Γ′ ⊢ M ⦂ A
⊢Γ-cast refl ⊢M = ⊢M

imprecision-typing : ImprecisionTyping
imprecision-typing (x⊑x x) = ⊢` (∋ʷ-lhs x) , ⊢` (∋ʷ-rhs x)
imprecision-typing (κ⊑κ k p) = ⊢lit k , ⊢lit k
imprecision-typing (ƛ⊑ƛ wA wA′ N⊑N′)
  with imprecision-typing N⊑N′
imprecision-typing (ƛ⊑ƛ wA wA′ N⊑N′) | ⊢N , ⊢N′ = ⊢ƛ wA ⊢N , ⊢ƛ wA′ ⊢N′
imprecision-typing (·⊑· L⊑L′ M⊑M′)
  with imprecision-typing L⊑L′ | imprecision-typing M⊑M′
imprecision-typing (·⊑· L⊑L′ M⊑M′) | ⊢L , ⊢L′ | ⊢M , ⊢M′ =
  ⊢· ⊢L ⊢M , ⊢· ⊢L′ ⊢M′
imprecision-typing (blame⊑ wA ⊢M′ p) = ⊢blame wA , ⊢M′
imprecision-typing (cast⊑cast M⊑M′ ct ct′ q)
  with imprecision-typing M⊑M′
imprecision-typing (cast⊑cast M⊑M′ ct ct′ q) | ⊢M , ⊢M′ =
  ⊢cast′ ct ⊢M , ⊢cast′ ct′ ⊢M′
imprecision-typing (cast⊑ cc M⊑M′ ct q) with imprecision-typing M⊑M′
imprecision-typing (cast⊑ cc M⊑M′ ct q) | ⊢M , ⊢M′ = ⊢cast′ ct ⊢M , ⊢M′
imprecision-typing (⊑cast M⊑M′ ct′ q) with imprecision-typing M⊑M′
imprecision-typing (⊑cast M⊑M′ ct′ q) | ⊢M , ⊢M′ = ⊢M , ⊢cast′ ct′ ⊢M′
imprecision-typing (Λ⊑Λ l v v′ V⊑V′ q) with imprecision-typing V⊑V′
imprecision-typing (Λ⊑Λ l v v′ V⊑V′ q) | ⊢V , ⊢V′ =
  ⊢Λ v (⊢Γ-cast (lift-lhs l) ⊢V) , ⊢Λ v′ (⊢Γ-cast (lift-rhs l) ⊢V′)
imprecision-typing (Λ⊑ bd nv occ l v V⊑M′ q) with imprecision-typing V⊑M′
imprecision-typing (Λ⊑ bd nv occ l v V⊑M′ q) | ⊢V , ⊢M′ =
  ⊢Λ v (⊢Γ-cast (liftᴸ-lhs l) ⊢V) , ⊢Γ-cast (liftᴸ-rhs l) ⊢M′
imprecision-typing (ν⊑ν L⊑L′ pA n n′ ci q) with imprecision-typing L⊑L′
imprecision-typing (ν⊑ν L⊑L′ pA n n′ ci q) | ⊢L , ⊢L′ =
  ⊢ν′ n ⊢L , ⊢ν′ n′ ⊢L′
imprecision-typing (ν⊑ L⊑M′ pA n q) with imprecision-typing L⊑M′
imprecision-typing (ν⊑ L⊑M′ pA n q) | ⊢L , ⊢M′ = ⊢ν′ n ⊢L , ⊢M′
imprecision-typing (⟪⟫⊑⟪⟫ i ks wi pay M⊑M′ b b′ ci q)
  with imprecision-typing M⊑M′
imprecision-typing (⟪⟫⊑⟪⟫ i ks wi pay M⊑M′ b b′ ci q) | ⊢M , ⊢M′ =
  ⊢⟪⟫′ b ⊢M , ⊢⟪⟫′ b′ ⊢M′
imprecision-typing (⟪⟫⊑ i ok bo ks wi pay M⊑M′ b q)
  with imprecision-typing M⊑M′
imprecision-typing (⟪⟫⊑ i ok bo ks wi pay M⊑M′ b q) | ⊢M , ⊢M′ =
  ⊢⟪⟫′ b ⊢M , ⊢closed ⊢M′
imprecision-typing (⊑⟪⟫ i pu so sn ks wi pay M⊑M′ b′ q)
  with imprecision-typing M⊑M′
imprecision-typing (⊑⟪⟫ i pu so sn ks wi pay M⊑M′ b′ q) | ⊢M , ⊢M′ =
  ⊢closed ⊢M , ⊢⟪⟫′ b′ ⊢M′
