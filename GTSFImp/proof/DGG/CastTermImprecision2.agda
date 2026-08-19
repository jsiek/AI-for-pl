module proof.DGG.CastTermImprecision2 where

-- File Charter:
--   * Experiments with the Issue 117 redesign of cast-term imprecision.
--   * Keeps type imprecision single-context, but makes each term-imprecision
--     premise carry its current local source/target embeddings into that
--     center context.
--   * Represents local rebasing explicitly, letting reveal/conceal wrappers
--     descend with a different alignment.
--   * Rebasing is asymmetric: a RebaseAt keeps the runtime stores and
--     the center context fixed, may move only the source pivot, and
--     freezes every old target variable's center.  Imprecision marks are
--     not pinned by the rebase; instead every wrapper rule carries
--     ImpEnvMono, letting marks decay toward X⊑★ from conclusion to
--     premise, and WFWorld names the worlds whose precise marks are
--     honestly aligned.
--   * Store representations are canonical: a pivot variable is compared
--     through resolveVar, which follows the store's representation chain
--     to its end instead of stopping at an arbitrary intermediate type.
--   * Conversion typing is indexed by an optional pivot.  A conversion
--     built only from identity leaves has no pivot and its wrapper rule
--     keeps the world fixed; only a conversion that seals or unseals an
--     actual variable can rebase, and only at that variable.
--   * Source-only structure needs no target counterpart: Λ⊑² lifts the
--     world on the left only and compares the target term unweakened,
--     and a rebase-onlyᴸ pivot handles a source variable with no
--     aligned target variable, justified by the target seeing ★ there.
--     There is no right-only mirror because type imprecision has no
--     rule with a bare variable on the imprecise side.
--   * The more rules in this relation, the more cases to prove in the DGG.
--     So don't add rules unless they are absolutely necessary!
--     Avoid rules that are not syntax directed.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as Nat using (ℕ)
open import Data.Product using (Σ-syntax; _,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import TermCtx using (TermCtx)
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _∼_; _↪ᵗ_; empty; keep; skip;
   toRenameᵗ; id; _!)
open import Conversion using (Conv↑; Conv↓; _⊢↑_; _⊢↓_)
open import Conversion using
  (unseal; _↦↑_; `∀↑_; id↑; seal; _↦↓_; `∀↓_; id↓;
   ⊢↑-∀; ⊢↑-id; PivotJoin; join-none; join-left; join-right; join-both;
   _⊢↑[_]_; ⊢↑-unsealˣ; ⊢↑-⇒ˣ; ⊢↑-∀ˣ; ⊢↑-∀-idˣ; ⊢↑-idˣ;
   _⊢↓[_]_; ⊢↓-sealˣ; ⊢↓-⇒ˣ; ⊢↓-∀ˣ; ⊢↓-∀-idˣ; ⊢↓-idˣ)
open import Imprecision
open import Primitives using (Const; Prim; constTy; primArgTy; primResultTy)
open import CastTerms
  using
    (Term; Var; Value; Ctx; ⟨_,_,_⟩; _⊢_⦂_; `_ ; ƛ_; _·_; Λ_;
     _⦂∀_[_]; $; _⊕[_]_; _⟨_⟩; _↑_; _↓_; blame; ⇑ᵗᵐ;
     ⊢·; ⊢⟨⟩; ⊢•; ⊢reveal)

open import proof.DGG.CtxImp

------------------------------------------------------------------------
-- Typed cast-term imprecision with recursive worlds
------------------------------------------------------------------------

infix 4 _∣_⊢²_⊑_∶_

data _∣_⊢²_⊑_∶_ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W) :
    Term Δᴸ → Term Δᴿ → {A : Ty Δᴸ} {B : Ty Δᴿ}
    → A ⊑ᵂ⟨ W ⟩ B → Set where

  x⊑x² : ∀ {x A B p}
    → γ ∋ʷ x ⦂ ctx-imp A B p
      --------------------------------
    → W ∣ γ ⊢² ` x ⊑ ` x ∶ p

  ƛ⊑ƛ² : ∀ {M M′ A A′ B B′}
      {pA : A ⊑ᵂ⟨ W ⟩ A′}
      {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ ctx-imp A A′ pA ∷ γ ⊢² M ⊑ M′ ∶ pB
      ---------------------------------------------------
    → W ∣ γ ⊢² ƛ M ⊑ ƛ M′ ∶ ⇒⊑⇒ pA pB

  ·⊑·² : ∀ {L L′ M M′ A A′ B B′}
      {pA : A ⊑ᵂ⟨ W ⟩ A′}
      {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB
    → W ∣ γ ⊢² M ⊑ M′ ∶ pA
      ------------------------------------------------
    → W ∣ γ ⊢² L · M ⊑ L′ · M′ ∶ pB

  Λ⊑Λ² : ∀ {γ′ V V′ A B}
      {p : A ⊑ᵂ⟨ liftWorldBoth X⊑X W ⟩ B}
    → LiftCtx X⊑X γ γ′
    → Value V
    → Value V′
    → liftWorldBoth X⊑X W ∣ γ′ ⊢² V ⊑ V′ ∶ p
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ B)
      -------------------------------------------------
    → W ∣ γ ⊢² Λ V ⊑ Λ V′ ∶ q

  -- The NonVar and occurrence premises mirror the ∀⊑ type rule; the
  -- extra-cast-right inversion needs them to refute the ∀⊑∀ and
  -- bot-elim views of q.
  Λ⊑² : ∀ {γ′ V M A B}
      {p : A ⊑ᵂ⟨ liftWorldLeft X⊑★ W ⟩ B}
    → NonVar A
    → Fin.zero ∈ᵗ A
    → LiftCtxᴸ X⊑★ γ γ′
    → Value V
    → ⟨ Δᴿ , targetStoreʷ W , tgtCtxʷ γ ⟩ ⊢ M ⦂ B
    → liftWorldLeft X⊑★ W ∣ γ′ ⊢² V ⊑ M ∶ p
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B)
      -------------------------------------------
    → W ∣ γ ⊢² Λ V ⊑ M ∶ q

  Λ⊑²-smart-comma :
      ∀ {Δᵐ}
      {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
      {γᵐ : CtxImp Wᵐ}
      {V : Term (Nat.suc Δᴸ)} {M : Term Δᴿ}
      {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ}
      {p : A ⊑ᵂ⟨ Wᵐ ⟩ B}
    → NonVar A
    → Fin.zero ∈ᵗ A
    → SmartCommaLiftᴸ W Wᵐ
    → SmartLiftCtxᴸ {W = W} {Wᵐ = Wᵐ} γ γᵐ
    → Value V
    → ⟨ Δᴿ , targetStoreʷ W , tgtCtxʷ γ ⟩ ⊢ M ⦂ B
    → Wᵐ ∣ γᵐ ⊢² V ⊑ M ∶ p
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B)
      -------------------------------------------
    → W ∣ γ ⊢² Λ V ⊑ M ∶ q

  •⊑•² : ∀ {M M′ C C′ A A′}
    → (p∀ : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′)
    → W ∣ γ ⊢² M ⊑ M′ ∶ p∀
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → (r : (C [ A ]ᵗ) ⊑ᵂ⟨ W ⟩ (C′ [ A′ ]ᵗ))
      --------------------------------------------------
    → W ∣ γ ⊢² M ⦂∀ C [ A ] ⊑ M′ ⦂∀ C′ [ A′ ] ∶ r

  •⊑² : ∀ {M M′ C A B}
    → (p∀ : `∀ C ⊑ᵂ⟨ W ⟩ B)
    → W ∣ γ ⊢² M ⊑ M′ ∶ p∀
    → (q : A ⊑ᵂ⟨ W ⟩ ★)
    → (r : (C [ A ]ᵗ) ⊑ᵂ⟨ W ⟩ B)
      ----------------------------------------
    → W ∣ γ ⊢² M ⦂∀ C [ A ] ⊑ M′ ∶ r

  κ⊑κ² : ∀ (κ : Const)
    → (p : constTy κ ⊑ᵂ⟨ W ⟩ constTy κ)
      ----------------------------------------------------
    → W ∣ γ ⊢² $ κ ⊑ $ κ ∶ p

  cast⊑cast² : ∀ {M M′ C C′ A A′}
      {p : C ⊑ᵂ⟨ W ⟩ C′} {ν : Env∼ Δᴸ} {ν′ : Env∼ Δᴿ}
    → (c : ν ⊢ C ∼ A)
    → (c′ : ν′ ⊢ C′ ∼ A′)
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
      -------------------------------------
    → W ∣ γ ⊢² M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ∶ q

  ⊑cast² : ∀ {M M′ A B B′}
      {p : A ⊑ᵂ⟨ W ⟩ B} {ν : Env∼ Δᴿ}
    → (c′ : ν ⊢ B ∼ B′)
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
      -----------------------------
    → W ∣ γ ⊢² M ⊑ M′ ⟨ c′ ⟩ ∶ q

  ⊑reveal² : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A B B′ Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c′ : Conv↑ Δᴿ B B′}
    → ImpEnvMono W W′
    → RebaseAtᴿ W W′ Xᴿ?
    → SameCtx γ γ′
    → targetStoreʷ W ⊢↑[ Xᴿ? ] c′
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
      -----------------------------
    → W ∣ γ ⊢² M ⊑ M′ ↑ c′ ∶ q

  ⊑conceal² : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A B B′ Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c′ : Conv↓ Δᴿ B B′}
    → ImpEnvMono W W′
    → RebaseAtᴿ W′ W Xᴿ?
    → SameCtx γ γ′
    → targetStoreʷ W ⊢↓[ Xᴿ? ] c′
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
      -----------------------------
    → W ∣ γ ⊢² M ⊑ M′ ↓ c′ ∶ q

  cast⊑² : ∀ {M M′ A A′ B}
      {p : A ⊑ᵂ⟨ W ⟩ B} {ν : Env∼ Δᴸ}
    → (c : ν ⊢ A ∼ A′)
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢² M ⟨ c ⟩ ⊑ M′ ∶ q

  reveal⊑² : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↑ Δᴸ A A′}
    → ImpEnvMono W W′
    → RebaseAtᴸ W W′ Xᴸ?
    → SameCtx γ γ′
    → sourceStoreʷ W ⊢↑[ Xᴸ? ] c
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢² M ↑ c ⊑ M′ ∶ q

  -- Source-only `seal X ★` sees through only under
  -- `NoTargetOccupantAtSource`; remaining non-`★`/non-seal cases use
  -- `SourceConcealOK`.
  conceal⊑²-seal-star-open : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ B X}
      {p : ★ ⊑ᵂ⟨ W′ ⟩ B}
    → NoTargetOccupantAtSource W′ X
    → ImpEnvMono W W′
    → TagRebaseAtᴸ W′ W (just X) nothing
    → SameCtx γ γ′
    → sourceStoreʷ W ⊢↓[ just X ] seal X ★
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : (＇ X) ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢² M ↓ seal X ★ ⊑ M′ ∶ q

  conceal⊑²-source-ok : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ A A′ B Xᴸ? Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↓ Δᴸ A A′}
    → SourceConcealOK W′ M c Xᴿ? M′
    → ImpEnvMono W W′
    → TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
    → SameCtx γ γ′
    → sourceStoreʷ W ⊢↓[ Xᴸ? ] c
    → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢² M ↓ c ⊑ M′ ∶ q

  reveal⊑reveal² : ∀
      {Wᵖ : World Δᴸ Δᴿ Δ} {γᵖ : CtxImp Wᵖ}
      {M M′ A A′ B B′ Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ Wᵖ ⟩ A′}
      {c : Conv↑ Δᴸ A B} {c′ : Conv↑ Δᴿ A′ B′}
    → ImpEnvMono W Wᵖ
    → RebaseAt W Wᵖ Xᴸ Xᴿ
    → SameCtx γ γᵖ
    → sourceStoreʷ W ⊢↑[ just Xᴸ ] c
    → targetStoreʷ W ⊢↑[ just Xᴿ ] c′
    → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
      -------------------------------------
    → W ∣ γ ⊢² M ↑ c ⊑ M′ ↑ c′ ∶ q

  conceal⊑conceal² : ∀
      {Wᵖ : World Δᴸ Δᴿ Δ} {γᵖ : CtxImp Wᵖ}
      {M M′ A A′ B B′ Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ Wᵖ ⟩ A′}
      {c : Conv↓ Δᴸ A B} {c′ : Conv↓ Δᴿ A′ B′}
    → MatchedConcealPartnerOK Wᵖ M c (just Xᴿ) M′
    → ImpEnvMono W Wᵖ
    → RebaseAt Wᵖ W Xᴸ Xᴿ
    → SameCtx γ γᵖ
    → sourceStoreʷ W ⊢↓[ just Xᴸ ] c
    → targetStoreʷ W ⊢↓[ just Xᴿ ] c′
    → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
      -------------------------------------
    → W ∣ γ ⊢² M ↓ c ⊑ M′ ↓ c′ ∶ q

  packaged-seal-star² : ∀
      {Wᵖ : World Δᴸ Δᴿ Δ} {γᵖ : CtxImp Wᵖ}
      {M M′ Xᴸ Xᴿ Xᴿ?}
      {p★ : ★ ⊑ᵂ⟨ Wᵖ ⟩ ★}
      {qᵖ : (＇ Xᴸ) ⊑ᵂ⟨ Wᵖ ⟩ ★}
    → MatchedConcealPartnerOK Wᵖ M (seal Xᴸ ★) Xᴿ? M′
    → ImpEnvMono W Wᵖ
    → RebaseAt Wᵖ W Xᴸ Xᴿ
    → SameCtx γ γᵖ
    → sourceStoreʷ W ⊢↓[ just Xᴸ ] seal Xᴸ ★
    → targetStoreʷ W ⊢↓[ just Xᴿ ] seal Xᴿ ★
    → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p★
    → Wᵖ ∣ γᵖ ⊢² M ↓ seal Xᴸ ★ ⊑ M′ ∶ qᵖ
    → (q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Xᴿ))
      --------------------------------------------------------
    → W ∣ γ ⊢² M ↓ seal Xᴸ ★ ⊑ M′ ↓ seal Xᴿ ★ ∶ q

  -- Source blame is below any well-typed target term.  The left side
  -- is the more static one (A ⊑ ★ for any closed type A, with ★ on
  -- the right): once the more static side has blamed, imprecision
  -- places no constraint on the more dynamic side.
  blame⊑² : ∀ {M′ A B}
    → ⟨ Δᴿ , targetStoreʷ W , tgtCtxʷ γ ⟩ ⊢ M′ ⦂ B
    → (p : A ⊑ᵂ⟨ W ⟩ B)
      ------------------------------
    → W ∣ γ ⊢² blame ⊑ M′ ∶ p

  ⊕⊑⊕² : (op : Prim)
    → ∀ {L L′ M M′}
      {p q : primArgTy op ⊑ᵂ⟨ W ⟩ primArgTy op}
    → W ∣ γ ⊢² L ⊑ L′ ∶ p
    → W ∣ γ ⊢² M ⊑ M′ ∶ q
    → (r : primResultTy op ⊑ᵂ⟨ W ⟩ primResultTy op)
      ------------------------------------------------
    → W ∣ γ ⊢² L ⊕[ op ] M ⊑ L′ ⊕[ op ] M′ ∶ r
