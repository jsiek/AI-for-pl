module proof.DGG.ReachabilityCatalog where

-- File Charter:
--   * Provides the Phase-1 source-level reachability catalog for the DGG
--     crossing investigation.
--   * Admits each closed source pair with one gradual-term imprecision proof
--     and records the ordinary compiler output for the two projected
--     gradual typings.
--   * Runs refl screening through a local proof-erased compiler mirror because
--     the ordinary compiler's consistency transports block normalization.
--   * Records evaluator-backed crossing-screen expectations as refl gates.

open import Data.Bool using (true)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)
import Data.Nat as Nat
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (store-empty)
open import TermCtx using (TermCtx; Z; ⇑ᶜ)
open import Consistency using
  (Env∼; flipᵐ; genᵐ; idᶜ; instᵐ; _⊢_∼_; _∼_; id; _!;
   ？_; _↦_; ∀ᶜ_; inst_; gen_; bot-elim; bot-intro; sym∼;
   X∼★ᵍ; ★∼Xᵍ)
open import GradualTerms
open import GradualTypeCheck
  using (fromJust; is-just; type-check-expect)
open import GradualTermImprecision using
  (CtxImp; ctx-imp; _∣_⊢ᴳ_⊑_⦂_⊑_∶_; _∋ⁱ_⦂_;
   Zⁱ; Sⁱ; LiftCtxⁱ; lift-[]; lift-∷; x⊑xᴳ; ƛ⊑ƛᴳ;
   ·⊑·ᴳ; ·★⊑·★ᴳ; Λ⊑Λᴳ; Λ⊑ᴳ; []⊑[]ᴳ; []⊑ᴳ;
   κ⊑κᴳ; ⊕⊑⊕ᴳ; gradual-term-imprecision-source-typing;
   gradual-term-imprecision-target-typing)
open import Compile using (compile)
import Imprecision as I
import CastTerms as C
open import Conversion using
  (Conv↑; Conv↓; unseal; _↦↑_; `∀↑_; id↑; seal; _↦↓_;
   `∀↓_; id↓)
open import Primitives using (Const; Prim; κℕ; κ𝔹; addℕ; and𝔹)
import proof.DGG.ReachabilityScreen as RS
import proof.ImprecisionConsistency as IC

Δ₀ : TyCtx
Δ₀ = Nat.zero

Δ₁ : TyCtx
Δ₁ = Nat.suc Nat.zero

------------------------------------------------------------------------
-- Source entries and compilation into the runtime screen
------------------------------------------------------------------------

record SourceEntry : Set where
  constructor source-entry
  field
    more-preciseᴳ : GTerm Δ₀
    more-impreciseᴳ : GTerm Δ₀
    gasᴸ : ℕ
    gasᴿ : ℕ
    typeᴸ : Ty Δ₀
    typeᴿ : Ty Δ₀
    type⊑ᴳ : I.idᵐ I.⊢ typeᴸ ⊑ typeᴿ
    typingᴸᴳ : Δ₀ ∣ [] ⊢ more-preciseᴳ ⦂ typeᴸ
    typingᴿᴳ : Δ₀ ∣ [] ⊢ more-impreciseᴳ ⦂ typeᴿ
    initial⊑ᴳ :
      I.idᵐ ∣ [] ⊢ᴳ more-preciseᴳ ⊑ more-impreciseᴳ
        ⦂ typeᴸ ⊑ typeᴿ ∶ type⊑ᴳ

open SourceEntry

typingᴸ : (e : SourceEntry)
  → Δ₀ ∣ [] ⊢ more-preciseᴳ e ⦂ typeᴸ e
typingᴸ e = typingᴸᴳ e

typingᴿ : (e : SourceEntry)
  → Δ₀ ∣ [] ⊢ more-impreciseᴳ e ⦂ typeᴿ e
typingᴿ e = typingᴿᴳ e

compiled-standard : SourceEntry → RS.Entry
compiled-standard e =
  RS.entry (proj₁ (compile {Σ = store-empty} (typingᴸ e)))
    (proj₁ (compile {Σ = store-empty} (typingᴿ e)))
    (gasᴸ e) (gasᴿ e)

inst-X! : ∀ {Δ} {μ : Env∼ Δ}
  → instᵐ μ ⊢ ＇ Fin.zero ∼ ★
inst-X! =
  _! ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ G∼★ = X∼★ᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Ans = nonstar-X ⦄

gen-★?X : ∀ {Δ} {μ : Env∼ Δ}
  → genᵐ μ ⊢ ★ ∼ ＇ Fin.zero
gen-★?X =
  ？_ ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ ★∼G = ★∼Xᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Bns = nonstar-X ⦄

flip-inst-★?X : ∀ {Δ} {μ : Env∼ Δ}
  → flipᵐ (instᵐ μ) ⊢ ★ ∼ ＇ Fin.zero
flip-inst-★?X =
  ？_ ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ ★∼G = ★∼Xᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Bns = nonstar-X ⦄

flip-gen-X! : ∀ {Δ} {μ : Env∼ Δ}
  → flipᵐ (genᵐ μ) ⊢ ＇ Fin.zero ∼ ★
flip-gen-X! =
  _! ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ G∼★ = X∼★ᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Ans = nonstar-X ⦄

sym-screen : ∀ {Δ} {μ : Env∼ Δ} {A B}
  → μ ⊢ A ∼ B
  → flipᵐ μ ⊢ B ∼ A
sym-screen (id a) = id a
sym-screen (c ↦ d) = sym∼ c ↦ sym∼ d
sym-screen (∀ᶜ (id (＇ Fin.zero) ↦ id (＇ Fin.zero))) =
  ∀ᶜ (id (＇ Fin.zero) ↦ id (＇ Fin.zero))
sym-screen (∀ᶜ c) = sym∼ (∀ᶜ c)
sym-screen (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄) =
  sym∼ (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄)
sym-screen (？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) =
  sym∼ (？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄)
sym-screen {μ = μ} {A = `∀ ((＇ Fin.zero) ⇒ (＇ Fin.zero))}
    {B = ★ ⇒ ★}
    (inst_ c B≢★) =
  gen_ ⦃ Bnv = nonvar-fun ⦄ ⦃ z∈B = ∈-fun-left var-∈ ⦄
    (flip-gen-X! {μ = flipᵐ μ} ↦ gen-★?X {μ = flipᵐ μ}) (λ ())
sym-screen (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) =
  sym∼ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★)
sym-screen {μ = μ} {A = ★ ⇒ ★}
    {B = `∀ ((＇ Fin.zero) ⇒ (＇ Fin.zero))}
    (gen_ c A≢★) =
  inst_ ⦃ Anv = nonvar-fun ⦄ ⦃ z∈A = ∈-fun-left var-∈ ⦄
    (flip-inst-★?X {μ = flipᵐ μ} ↦ inst-X! {μ = flipᵐ μ}) (λ ())
sym-screen (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) =
  sym∼ (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★)
sym-screen bot-elim = bot-intro
sym-screen bot-intro = bot-elim

-- The ordinary compiler wraps application symmetry in a transport proof.
-- That proof is irrelevant to typing but opaque to the executable evaluator.
-- This local term compiler mirrors `Compile.compile` and keeps `sym∼`
-- computational so the reachability screen can run by refl.
compile-screen : ∀ {Δ Γ M A}
  → Δ ∣ Γ ⊢ M ⦂ A
  → C.Term Δ
compile-screen (⊢` {x = x} x∈) =
  C.` x
compile-screen (⊢ƛ M⊢) =
  C.ƛ compile-screen M⊢
compile-screen (⊢· L⊢ M⊢ A∼A′) =
  compile-screen L⊢ C.· (compile-screen M⊢ C.⟨ sym-screen A∼A′ ⟩)
compile-screen {Δ = Δ} (⊢·★ L⊢ M⊢ A′∼★) =
  let c : idᶜ {Δ = Δ} ⊢ ★ ∼ (★ ⇒ ★)
      c = ？ (id ★ ↦ id ★) in
  (compile-screen L⊢ C.⟨ c ⟩) C.·
    (compile-screen M⊢ C.⟨ A′∼★ ⟩)
compile-screen (⊢Λ vM M⊢) =
  C.Λ (compile-screen M⊢)
compile-screen (⊢• {B = B} {A = A} M⊢) =
  compile-screen M⊢ C.⦂∀ B [ A ]
compile-screen (⊢$ κ) =
  C.$ κ
compile-screen (⊢⊕ op L⊢ A∼arg M⊢ B∼arg) =
  (compile-screen L⊢ C.⟨ A∼arg ⟩) C.⊕[ op ]
    (compile-screen M⊢ C.⟨ B∼arg ⟩)

compiled : SourceEntry → RS.Entry
compiled e =
  RS.entry (compile-screen (typingᴸ e)) (compile-screen (typingᴿ e))
    (gasᴸ e) (gasᴿ e)

------------------------------------------------------------------------
-- Proof-erased compiler skeletons
------------------------------------------------------------------------

data CastSkeleton (Δ : TyCtx) : Set where
  cast-shape : Ty Δ → Ty Δ → CastSkeleton Δ

mutual

  data RevealSkeleton (Δ : TyCtx) : Set where
    reveal-unseal : TyVar Δ → Ty Δ → RevealSkeleton Δ
    reveal-fun : ConcealSkeleton Δ → RevealSkeleton Δ
      → RevealSkeleton Δ
    reveal-all : RevealSkeleton (suc Δ) → RevealSkeleton Δ
    reveal-id : Ty Δ → RevealSkeleton Δ

  data ConcealSkeleton (Δ : TyCtx) : Set where
    conceal-seal : TyVar Δ → Ty Δ → ConcealSkeleton Δ
    conceal-fun : RevealSkeleton Δ → ConcealSkeleton Δ
      → ConcealSkeleton Δ
    conceal-all : ConcealSkeleton (suc Δ) → ConcealSkeleton Δ
    conceal-id : Ty Δ → ConcealSkeleton Δ

data TermSkeleton : TyCtx → Set where
  term-var : ∀ {Δ} → ℕ → TermSkeleton Δ
  term-lam : ∀ {Δ} → TermSkeleton Δ → TermSkeleton Δ
  term-app : ∀ {Δ} → TermSkeleton Δ → TermSkeleton Δ
    → TermSkeleton Δ
  term-tylam : ∀ {Δ} → TermSkeleton (suc Δ) → TermSkeleton Δ
  term-tyapp : ∀ {Δ} → TermSkeleton Δ → Ty (suc Δ) → Ty Δ
    → TermSkeleton Δ
  term-const : ∀ {Δ} → Const → TermSkeleton Δ
  term-prim : ∀ {Δ} → Prim → TermSkeleton Δ → TermSkeleton Δ
    → TermSkeleton Δ
  term-cast : ∀ {Δ} → TermSkeleton Δ → CastSkeleton Δ
    → TermSkeleton Δ
  term-reveal : ∀ {Δ} → TermSkeleton Δ → RevealSkeleton Δ
    → TermSkeleton Δ
  term-conceal : ∀ {Δ} → TermSkeleton Δ → ConcealSkeleton Δ
    → TermSkeleton Δ
  term-blame : ∀ {Δ} → TermSkeleton Δ

-- `Eval.step?` recurses on term syntax.  At cast nodes it calls `value?`,
-- `inert?`, and `cast-redex?`; those helpers inspect consistency
-- constructors and, for `!`/`？`, ground endpoints.  This skeleton is a
-- compiler-fidelity gate: it preserves every cast node and the intrinsic
-- source/target types, but erases transported consistency derivations so
-- `compile-screen` can be compared with `compile`.  Reveal/conceal evidence
-- is not transported by `compile`, and `Eval` branches on its constructors
-- and seal payloads, so the conversion skeleton keeps those constructors.
cast-skeleton : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → μ ⊢ A ∼ B
  → CastSkeleton Δ
cast-skeleton {A = A} {B = B} c = cast-shape A B

mutual

  reveal-skeleton : ∀ {Δ} {A B : Ty Δ}
    → Conv↑ Δ A B
    → RevealSkeleton Δ
  reveal-skeleton (unseal X R) = reveal-unseal X R
  reveal-skeleton (c ↦↑ d) =
    reveal-fun (conceal-skeleton c) (reveal-skeleton d)
  reveal-skeleton (`∀↑ c) = reveal-all (reveal-skeleton c)
  reveal-skeleton (id↑ A) = reveal-id A

  conceal-skeleton : ∀ {Δ} {A B : Ty Δ}
    → Conv↓ Δ A B
    → ConcealSkeleton Δ
  conceal-skeleton (seal X R) = conceal-seal X R
  conceal-skeleton (c ↦↓ d) =
    conceal-fun (reveal-skeleton c) (conceal-skeleton d)
  conceal-skeleton (`∀↓ c) = conceal-all (conceal-skeleton c)
  conceal-skeleton (id↓ A) = conceal-id A

skeleton : ∀ {Δ} → C.Term Δ → TermSkeleton Δ
skeleton (C.` x) = term-var x
skeleton (C.ƛ M) = term-lam (skeleton M)
skeleton (L C.· M) = term-app (skeleton L) (skeleton M)
skeleton (C.Λ M) = term-tylam (skeleton M)
skeleton (M C.⦂∀ B [ A ]) = term-tyapp (skeleton M) B A
skeleton (C.$ κ) = term-const κ
skeleton (L C.⊕[ op ] M) = term-prim op (skeleton L) (skeleton M)
skeleton (M C.⟨ c ⟩) = term-cast (skeleton M) (cast-skeleton c)
skeleton (M C.↑ c) = term-reveal (skeleton M) (reveal-skeleton c)
skeleton (M C.↓ c) = term-conceal (skeleton M) (conceal-skeleton c)
skeleton C.blame = term-blame

record EntrySkeleton : Set where
  constructor entry-skeleton
  field
    left : TermSkeleton Δ₀
    right : TermSkeleton Δ₀

entry-skeleton-of : RS.Entry → EntrySkeleton
entry-skeleton-of e =
  entry-skeleton (skeleton (RS.Entry.more-precise e))
    (skeleton (RS.Entry.more-imprecise e))

skeleton-gate : SourceEntry → Set
skeleton-gate e =
  entry-skeleton-of (compiled e) ≡
  entry-skeleton-of (compiled-standard e)

------------------------------------------------------------------------
-- Reflexive source-imprecision helper
------------------------------------------------------------------------

refl⊑ᵗ : ∀ {Δ} (μ : I.ImpEnv Δ) (A : Ty Δ)
  → μ I.⊢ A ⊑ A
refl⊑ᵗ μ A = IC.refl⊑ A

reflCtxⁱ : ∀ {Δ} (μ : I.ImpEnv Δ) → TermCtx Δ → CtxImp μ
reflCtxⁱ μ [] = []
reflCtxⁱ μ (A ∷ Γ) =
  ctx-imp A A (refl⊑ᵗ μ A) ∷ reflCtxⁱ μ Γ

lookup-reflⁱ : ∀ {Δ Γ x A} (μ : I.ImpEnv Δ)
  → Γ TermCtx.∋ x ⦂ A
  → reflCtxⁱ μ Γ ∋ⁱ x ⦂ ctx-imp A A (refl⊑ᵗ μ A)
lookup-reflⁱ μ Z = Zⁱ
lookup-reflⁱ μ (TermCtx.S x∈) = Sⁱ (lookup-reflⁱ μ x∈)

lift-reflCtxⁱ : ∀ {Δ Γ} (μ : I.ImpEnv Δ)
  → LiftCtxⁱ (I.extᵐ μ) (reflCtxⁱ μ Γ)
      (reflCtxⁱ (I.extᵐ μ) (⇑ᶜ Γ))
lift-reflCtxⁱ {Γ = []} μ = lift-[]
lift-reflCtxⁱ {Γ = A ∷ Γ} μ =
  lift-∷ (lift-reflCtxⁱ {Γ = Γ} μ)

reflᴳ : ∀ {Δ Γ M A} (μ : I.ImpEnv Δ)
  → Δ ∣ Γ ⊢ M ⦂ A
  → μ ∣ reflCtxⁱ μ Γ ⊢ᴳ M ⊑ M ⦂ A ⊑ A ∶ refl⊑ᵗ μ A
reflᴳ μ (⊢` x∈) =
  x⊑xᴳ (lookup-reflⁱ μ x∈)
reflᴳ μ (⊢ƛ M⊢) =
  ƛ⊑ƛᴳ (reflᴳ μ M⊢)
reflᴳ μ (⊢· L⊢ M⊢ A∼C) =
  ·⊑·ᴳ (reflᴳ μ L⊢) (reflᴳ μ M⊢) A∼C A∼C
reflᴳ μ (⊢·★ L⊢ M⊢ C∼★) =
  ·★⊑·★ᴳ (reflᴳ μ L⊢) (reflᴳ μ M⊢) C∼★ C∼★
reflᴳ {Γ = Γ} μ (⊢Λ {zero∈A = zero∈A} vM M⊢) =
  Λ⊑Λᴳ (lift-reflCtxⁱ {Γ = Γ} μ) vM vM zero∈A zero∈A
    (reflᴳ (I.extᵐ μ) M⊢)
reflᴳ μ (⊢• {B = B} {A = A} M⊢) =
  []⊑[]ᴳ (reflᴳ μ M⊢) (refl⊑ᵗ μ A) (refl⊑ᵗ μ (B [ A ]ᵗ))
reflᴳ μ (⊢$ (κℕ n)) =
  κ⊑κᴳ (κℕ n)
reflᴳ μ (⊢$ (κ𝔹 b)) =
  κ⊑κᴳ (κ𝔹 b)
reflᴳ μ (⊢⊕ addℕ L⊢ A∼arg M⊢ B∼arg) =
  ⊕⊑⊕ᴳ addℕ (reflᴳ μ L⊢) A∼arg A∼arg
    (reflᴳ μ M⊢) B∼arg B∼arg
reflᴳ μ (⊢⊕ and𝔹 L⊢ A∼arg M⊢ B∼arg) =
  ⊕⊑⊕ᴳ and𝔹 (reflᴳ μ L⊢) A∼arg A∼arg
    (reflᴳ μ M⊢) B∼arg B∼arg

same-entry : ∀ {M A}
  → Δ₀ ∣ [] ⊢ M ⦂ A
  → ℕ
  → SourceEntry
same-entry {M = M} {A = A} M⊢ gas =
  source-entry M M gas gas A A (refl⊑ᵗ I.idᵐ A)
    M⊢ M⊢ (reflᴳ I.idᵐ M⊢)

------------------------------------------------------------------------
-- Shared source terms and typings
------------------------------------------------------------------------

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

ℕ₀ : Ty Δ₀
ℕ₀ = ℕᵗ

𝔹ᵗ : ∀ {Δ} → Ty Δ
𝔹ᵗ = ‵ `𝔹

𝔹₀ : Ty Δ₀
𝔹₀ = 𝔹ᵗ

Xᵗ : ∀ {Δ} → Ty (suc Δ)
Xᵗ = ＇ Fin.zero

X₀ : Ty Δ₁
X₀ = Xᵗ {Δ = Δ₀}

X⇒X : ∀ {Δ} → Ty (suc Δ)
X⇒X = Xᵗ ⇒ Xᵗ

X₀⇒X₀ : Ty Δ₁
X₀⇒X₀ = X₀ ⇒ X₀

X⇒★ : ∀ {Δ} → Ty (suc Δ)
X⇒★ = Xᵗ ⇒ ★

X₀⇒★ : Ty Δ₁
X₀⇒★ = X₀ ⇒ ★

★⇒★ᵗ : ∀ {Δ} → Ty Δ
★⇒★ᵗ = ★ ⇒ ★

★⇒★₀ : Ty Δ₀
★⇒★₀ = ★⇒★ᵗ

∀X⇒X : ∀ {Δ} → Ty Δ
∀X⇒X = `∀ X⇒X

∀X⇒X₀ : Ty Δ₀
∀X⇒X₀ = `∀ X₀⇒X₀

X∈X⇒X : ∀ {Δ} → Fin.zero ∈ᵗ X⇒X {Δ}
X∈X⇒X = ∈-fun-left var-∈

X∈X⇒★ : ∀ {Δ} → Fin.zero ∈ᵗ X⇒★ {Δ}
X∈X⇒★ = ∈-fun-left var-∈

nat : ∀ {Δ} → ℕ → GTerm Δ
nat n = $ (κℕ n)

nat⊢ : ∀ {Δ Γ} n → Δ ∣ Γ ⊢ nat n ⦂ ℕᵗ
nat⊢ n = ⊢$ (κℕ n)

bool : ∀ {Δ} → GTerm Δ
bool = $ (κ𝔹 true)

bool⊢ : ∀ {Δ Γ} → Δ ∣ Γ ⊢ bool ⦂ 𝔹ᵗ
bool⊢ = ⊢$ (κ𝔹 true)

polyId : ∀ {Δ} → GTerm Δ
polyId = Λ (ƛ Xᵗ ⇒ ` 0)

polyId⊢ : ∀ {Δ Γ} → Δ ∣ Γ ⊢ polyId ⦂ ∀X⇒X
polyId⊢ =
  ⊢Λ {zero∈A = X∈X⇒X} (ƛ Xᵗ ⇒ ` 0) (⊢ƛ (⊢` Z))

dynId : ∀ {Δ} → GTerm Δ
dynId = ƛ ★ ⇒ ` 0

dynId⊢ : ∀ {Δ Γ} → Δ ∣ Γ ⊢ dynId ⦂ ★⇒★ᵗ
dynId⊢ = ⊢ƛ (⊢` Z)

∀X⇒X⊑★⇒★ᵗ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ ∀X⇒X ⊑ ★⇒★ᵗ
∀X⇒X⊑★⇒★ᵗ =
  I.∀⊑ nonvar-fun (∈-fun-left var-∈)
    (I.⇒⊑⇒ (I.X⊑★ refl) (I.X⊑★ refl))

★⇒★⊑★⇒★ᵗ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ ★⇒★ᵗ ⊑ ★⇒★ᵗ
★⇒★⊑★⇒★ᵗ = I.⇒⊑⇒ I.★⊑★ I.★⊑★

ℕ⇒ℕ⊑★⇒★ᵗ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ (ℕᵗ ⇒ ℕᵗ) ⊑ ★⇒★ᵗ
ℕ⇒ℕ⊑★⇒★ᵗ = I.⇒⊑⇒ I.ι⊑★ I.ι⊑★

ℕ⇒ℕ⊑★⇒★₀ : I.idᵐ I.⊢ (ℕ₀ ⇒ ℕ₀) ⊑ ★⇒★₀
ℕ⇒ℕ⊑★⇒★₀ = ℕ⇒ℕ⊑★⇒★ᵗ

𝔹⇒𝔹⊑★⇒★₀ :
  I.idᵐ I.⊢ (𝔹₀ ⇒ 𝔹₀) ⊑ ★⇒★₀
𝔹⇒𝔹⊑★⇒★₀ = I.⇒⊑⇒ I.ι⊑★ I.ι⊑★

starfun∼∀X⇒X : ∀ {Δ} → ★⇒★ᵗ {Δ} ∼ ∀X⇒X {Δ}
starfun∼∀X⇒X =
  gen_ ⦃ z∈B = ∈-fun-left var-∈ ⦄
    (flip-gen-X! {μ = idᶜ} ↦ gen-★?X {μ = idᶜ}) (λ ())

∀X⇒X∼★⇒★ : ∀ {Δ} → ∀X⇒X {Δ} ∼ ★⇒★ᵗ {Δ}
∀X⇒X∼★⇒★ =
  inst_ ⦃ z∈A = ∈-fun-left var-∈ ⦄
    (flip-inst-★?X {μ = idᶜ} ↦ inst-X! {μ = idᶜ}) (λ ())

★⇒★∼★⇒★ : ∀ {Δ} → ★⇒★ᵗ {Δ} ∼ ★⇒★ᵗ {Δ}
★⇒★∼★⇒★ = id ★ ↦ id ★

∀X⇒X∼∀X⇒X : ∀ {Δ} → ∀X⇒X {Δ} ∼ ∀X⇒X {Δ}
∀X⇒X∼∀X⇒X = ∀ᶜ (id (＇ Fin.zero) ↦ id (＇ Fin.zero))

polyId⊑dynId :
  I.idᵐ ∣ [] ⊢ᴳ polyId {Δ = Δ₀} ⊑ dynId {Δ = Δ₀}
    ⦂ ∀X⇒X₀ ⊑ ★⇒★₀ ∶ ∀X⇒X⊑★⇒★ᵗ
polyId⊑dynId =
  Λ⊑ᴳ nonvar-fun (∈-fun-left var-∈) lift-[]
    (ƛ X₀ ⇒ ` 0) (dynId⊢ {Δ = Δ₀} {Γ = []})
    (ƛ⊑ƛᴳ (x⊑xᴳ Zⁱ))

polyIdℕ⊑dynId :
  I.idᵐ ∣ [] ⊢ᴳ (polyId {Δ = Δ₀} `[ ℕ₀ ]) ⊑ dynId
    ⦂ (ℕ₀ ⇒ ℕ₀) ⊑ ★⇒★₀ ∶ ℕ⇒ℕ⊑★⇒★₀
polyIdℕ⊑dynId =
  []⊑ᴳ polyId⊑dynId I.ι⊑★ ℕ⇒ℕ⊑★⇒★₀

polyId𝔹⊑dynId :
  I.idᵐ ∣ [] ⊢ᴳ (polyId {Δ = Δ₀} `[ 𝔹₀ ]) ⊑ dynId
    ⦂ (𝔹₀ ⇒ 𝔹₀) ⊑ ★⇒★₀ ∶ 𝔹⇒𝔹⊑★⇒★₀
polyId𝔹⊑dynId =
  []⊑ᴳ polyId⊑dynId I.ι⊑★ 𝔹⇒𝔹⊑★⇒★₀

------------------------------------------------------------------------
-- Reusable chain-and-tag source programs
------------------------------------------------------------------------

polyIdNatApp : GTerm Δ₀
polyIdNatApp = (polyId {Δ = Δ₀} `[ ℕ₀ ]) ·[ 11 ] nat 7

polyIdNatApp⊢ : Δ₀ ∣ [] ⊢ polyIdNatApp ⦂ ℕ₀
polyIdNatApp⊢ =
  ⊢· (⊢• (polyId⊢ {Δ = Δ₀})) (nat⊢ 7) (id (‵ `ℕ))

polyIdBoolApp : GTerm Δ₀
polyIdBoolApp = (polyId {Δ = Δ₀} `[ 𝔹₀ ]) ·[ 12 ] bool

polyIdBoolApp⊢ : Δ₀ ∣ [] ⊢ polyIdBoolApp ⦂ 𝔹₀
polyIdBoolApp⊢ =
  ⊢· (⊢• (polyId⊢ {Δ = Δ₀})) bool⊢ (id (‵ `𝔹))

polyIdSelf : GTerm Δ₀
polyIdSelf = (polyId {Δ = Δ₀} `[ ∀X⇒X₀ ]) ·[ 13 ] polyId

polyIdSelf⊢ : Δ₀ ∣ [] ⊢ polyIdSelf ⦂ ∀X⇒X₀
polyIdSelf⊢ =
  ⊢· (⊢• (polyId⊢ {Δ = Δ₀})) (polyId⊢ {Δ = Δ₀})
    (∀X⇒X∼∀X⇒X {Δ = Δ₀})

polyIdSelfNatApp : GTerm Δ₀
polyIdSelfNatApp = (polyIdSelf `[ ℕ₀ ]) ·[ 14 ] nat 9

polyIdSelfNatApp⊢ : Δ₀ ∣ [] ⊢ polyIdSelfNatApp ⦂ ℕ₀
polyIdSelfNatApp⊢ =
  ⊢· (⊢• polyIdSelf⊢) (nat⊢ 9) (id (‵ `ℕ))

polyIdSelfBoolApp : GTerm Δ₀
polyIdSelfBoolApp = (polyIdSelf `[ 𝔹₀ ]) ·[ 15 ] bool

polyIdSelfBoolApp⊢ : Δ₀ ∣ [] ⊢ polyIdSelfBoolApp ⦂ 𝔹₀
polyIdSelfBoolApp⊢ =
  ⊢· (⊢• polyIdSelf⊢) bool⊢ (id (‵ `𝔹))

polyIdSelfStarApp : GTerm Δ₀
polyIdSelfStarApp = (polyIdSelf `[ ★ ]) ·[ 16 ] nat 9

polyIdSelfStarApp⊢ : Δ₀ ∣ [] ⊢ polyIdSelfStarApp ⦂ ★
polyIdSelfStarApp⊢ =
  ⊢· (⊢• polyIdSelf⊢) (nat⊢ 9) (？ (id (‵ `ℕ)))

idAtX : GTerm Δ₁
idAtX = (polyId {Δ = Δ₁} `[ X₀ ]) ·[ 21 ] (` 0)

idAtX⊢ : ∀ {Γ} → Δ₁ ∣ X₀ ∷ Γ ⊢ idAtX ⦂ X₀
idAtX⊢ =
  ⊢· (⊢• (polyId⊢ {Δ = Δ₁})) (⊢` Z) (id (＇ Fin.zero))

idAtX² : GTerm Δ₁
idAtX² = (polyId {Δ = Δ₁} `[ X₀ ]) ·[ 22 ] idAtX

idAtX²⊢ : ∀ {Γ} → Δ₁ ∣ X₀ ∷ Γ ⊢ idAtX² ⦂ X₀
idAtX²⊢ =
  ⊢· (⊢• (polyId⊢ {Δ = Δ₁})) idAtX⊢ (id (＇ Fin.zero))

idAtX³ : GTerm Δ₁
idAtX³ = (polyId {Δ = Δ₁} `[ X₀ ]) ·[ 23 ] idAtX²

idAtX³⊢ : ∀ {Γ} → Δ₁ ∣ X₀ ∷ Γ ⊢ idAtX³ ⦂ X₀
idAtX³⊢ =
  ⊢· (⊢• (polyId⊢ {Δ = Δ₁})) idAtX²⊢ (id (＇ Fin.zero))

starBody : GTerm Δ₁
starBody = (polyId {Δ = Δ₁} `[ ★ ]) ·[ 24 ] nat 6

starBody⊢ : ∀ {Γ} → Δ₁ ∣ X₀ ∷ Γ ⊢ starBody ⦂ ★
starBody⊢ =
  ⊢· (⊢• (polyId⊢ {Δ = Δ₁})) (nat⊢ 6) (？ (id (‵ `ℕ)))

chainFun : GTerm Δ₁ → GTerm Δ₀
chainFun body = Λ (ƛ X₀ ⇒ body)

chainFunX⊢ : ∀ {body}
  → Δ₁ ∣ X₀ ∷ [] ⊢ body ⦂ X₀
  → Δ₀ ∣ [] ⊢ chainFun body ⦂ `∀ X₀⇒X₀
chainFunX⊢ {body = body} body⊢ =
  ⊢Λ {zero∈A = X∈X⇒X} (ƛ X₀ ⇒ body) (⊢ƛ body⊢)

chainFun★⊢ : ∀ {body}
  → Δ₁ ∣ X₀ ∷ [] ⊢ body ⦂ ★
  → Δ₀ ∣ [] ⊢ chainFun body ⦂ `∀ X₀⇒★
chainFun★⊢ {body = body} body⊢ =
  ⊢Λ {zero∈A = X∈X⇒★} (ƛ X₀ ⇒ body) (⊢ƛ body⊢)

runChainℕ : GTerm Δ₁ → GTerm Δ₀
runChainℕ body = (chainFun body `[ ℕ₀ ]) ·[ 25 ] nat 7

runChainX⊢ : ∀ {body}
  → Δ₁ ∣ X₀ ∷ [] ⊢ body ⦂ X₀
  → Δ₀ ∣ [] ⊢ runChainℕ body ⦂ ℕ₀
runChainX⊢ body⊢ =
  ⊢· (⊢• (chainFunX⊢ body⊢)) (nat⊢ 7) (id (‵ `ℕ))

runChain★⊢ : ∀ {body}
  → Δ₁ ∣ X₀ ∷ [] ⊢ body ⦂ ★
  → Δ₀ ∣ [] ⊢ runChainℕ body ⦂ ★
runChain★⊢ body⊢ =
  ⊢· (⊢• (chainFun★⊢ body⊢)) (nat⊢ 7) (id (‵ `ℕ))

runChain★Inst : GTerm Δ₁ → GTerm Δ₀
runChain★Inst body = (chainFun body `[ ★ ]) ·[ 26 ] nat 7

runChain★Inst⊢ : ∀ {body}
  → Δ₁ ∣ X₀ ∷ [] ⊢ body ⦂ ★
  → Δ₀ ∣ [] ⊢ runChain★Inst body ⦂ ★
runChain★Inst⊢ body⊢ =
  ⊢· (⊢• (chainFun★⊢ body⊢)) (nat⊢ 7) (？ (id (‵ `ℕ)))

polyId★App : GTerm Δ₀
polyId★App = (polyId {Δ = Δ₀} `[ ★ ]) ·[ 31 ] nat 7

polyId★App⊢ : Δ₀ ∣ [] ⊢ polyId★App ⦂ ★
polyId★App⊢ =
  ⊢· (⊢• (polyId⊢ {Δ = Δ₀})) (nat⊢ 7) (？ (id (‵ `ℕ)))

leftOnlyInstPathᴸ : GTerm Δ₀
leftOnlyInstPathᴸ = (polyId {Δ = Δ₀} `[ ℕ₀ ]) ·[ 46 ] nat 5

leftOnlyInstPathᴿ : GTerm Δ₀
leftOnlyInstPathᴿ = dynId ·[ 46 ] nat 5

leftOnlyInstPathᴸ⊢ : Δ₀ ∣ [] ⊢ leftOnlyInstPathᴸ ⦂ ℕ₀
leftOnlyInstPathᴸ⊢ =
  ⊢· (⊢• (polyId⊢ {Δ = Δ₀})) (nat⊢ 5) (id (‵ `ℕ))

leftOnlyInstPathᴿ⊢ : Δ₀ ∣ [] ⊢ leftOnlyInstPathᴿ ⦂ ★
leftOnlyInstPathᴿ⊢ =
  ⊢· dynId⊢ (nat⊢ 5) (？ (id (‵ `ℕ)))

leftOnlyInstPath⊑ :
  I.idᵐ ∣ [] ⊢ᴳ leftOnlyInstPathᴸ ⊑ leftOnlyInstPathᴿ
    ⦂ ℕ₀ ⊑ ★ ∶ I.ι⊑★
leftOnlyInstPath⊑ =
  ·⊑·ᴳ polyIdℕ⊑dynId (κ⊑κᴳ (κℕ 5))
    (id (‵ `ℕ)) (？ (id (‵ `ℕ)))


genPathLeftCallee : GTerm Δ₀
genPathLeftCallee = ƛ ∀X⇒X₀ ⇒ ` 0

genPathRightCallee : GTerm Δ₀
genPathRightCallee = ƛ ★⇒★₀ ⇒ ` 0

genPathLeftCallee⊢ :
  Δ₀ ∣ [] ⊢ genPathLeftCallee ⦂ ∀X⇒X₀ ⇒ ∀X⇒X₀
genPathLeftCallee⊢ = ⊢ƛ (⊢` Z)

genPathRightCallee⊢ :
  Δ₀ ∣ [] ⊢ genPathRightCallee ⦂ ★⇒★₀ ⇒ ★⇒★₀
genPathRightCallee⊢ = ⊢ƛ (⊢` Z)

genPathLeftInner : GTerm Δ₀
genPathLeftInner = genPathLeftCallee ·[ 47 ] dynId

genPathRightInner : GTerm Δ₀
genPathRightInner = genPathRightCallee ·[ 47 ] dynId

genPathLeftInner⊢ : Δ₀ ∣ [] ⊢ genPathLeftInner ⦂ ∀X⇒X₀
genPathLeftInner⊢ =
  ⊢· genPathLeftCallee⊢ dynId⊢ (∀X⇒X∼★⇒★ {Δ = Δ₀})

genPathRightInner⊢ : Δ₀ ∣ [] ⊢ genPathRightInner ⦂ ★⇒★₀
genPathRightInner⊢ =
  ⊢· genPathRightCallee⊢ dynId⊢ (★⇒★∼★⇒★ {Δ = Δ₀})

leftOnlyGenPathᴸ : GTerm Δ₀
leftOnlyGenPathᴸ = (genPathLeftInner `[ ℕ₀ ]) ·[ 48 ] nat 5

leftOnlyGenPathᴿ : GTerm Δ₀
leftOnlyGenPathᴿ = genPathRightInner ·[ 48 ] nat 5

leftOnlyGenPathᴸ⊢ : Δ₀ ∣ [] ⊢ leftOnlyGenPathᴸ ⦂ ℕ₀
leftOnlyGenPathᴸ⊢ =
  ⊢· (⊢• genPathLeftInner⊢) (nat⊢ 5) (id (‵ `ℕ))

leftOnlyGenPathᴿ⊢ : Δ₀ ∣ [] ⊢ leftOnlyGenPathᴿ ⦂ ★
leftOnlyGenPathᴿ⊢ =
  ⊢· genPathRightInner⊢ (nat⊢ 5) (？ (id (‵ `ℕ)))

genPathCallee⊑ :
  I.idᵐ ∣ [] ⊢ᴳ genPathLeftCallee ⊑ genPathRightCallee
    ⦂ ∀X⇒X₀ ⇒ ∀X⇒X₀ ⊑ ★⇒★₀ ⇒ ★⇒★₀ ∶
      I.⇒⊑⇒ ∀X⇒X⊑★⇒★ᵗ ∀X⇒X⊑★⇒★ᵗ
genPathCallee⊑ = ƛ⊑ƛᴳ (x⊑xᴳ Zⁱ)

dynId⊑dynId :
  I.idᵐ ∣ [] ⊢ᴳ dynId {Δ = Δ₀} ⊑ dynId
    ⦂ ★⇒★₀ ⊑ ★⇒★₀ ∶ ★⇒★⊑★⇒★ᵗ
dynId⊑dynId = ƛ⊑ƛᴳ (x⊑xᴳ Zⁱ)

genPathInner⊑ :
  I.idᵐ ∣ [] ⊢ᴳ genPathLeftInner ⊑ genPathRightInner
    ⦂ ∀X⇒X₀ ⊑ ★⇒★₀ ∶ ∀X⇒X⊑★⇒★ᵗ
genPathInner⊑ =
  ·⊑·ᴳ genPathCallee⊑ dynId⊑dynId
    (∀X⇒X∼★⇒★ {Δ = Δ₀}) (★⇒★∼★⇒★ {Δ = Δ₀})

genPathInst⊑ :
  I.idᵐ ∣ [] ⊢ᴳ (genPathLeftInner `[ ℕ₀ ]) ⊑ genPathRightInner
    ⦂ ℕ₀ ⇒ ℕ₀ ⊑ ★⇒★₀ ∶ ℕ⇒ℕ⊑★⇒★₀
genPathInst⊑ =
  []⊑ᴳ genPathInner⊑ I.ι⊑★ ℕ⇒ℕ⊑★⇒★₀

leftOnlyGenPath⊑ :
  I.idᵐ ∣ [] ⊢ᴳ leftOnlyGenPathᴸ ⊑ leftOnlyGenPathᴿ
    ⦂ ℕ₀ ⊑ ★ ∶ I.ι⊑★
leftOnlyGenPath⊑ =
  ·⊑·ᴳ genPathInst⊑ (κ⊑κᴳ (κℕ 5))
    (id (‵ `ℕ)) (？ (id (‵ `ℕ)))


polyAtX : GTerm Δ₁
polyAtX = polyId {Δ = Δ₁} `[ X₀ ]

polyAtX⊢ : ∀ {Γ} → Δ₁ ∣ X₀ ∷ Γ ⊢ polyAtX ⦂ X₀⇒X₀
polyAtX⊢ = ⊢• (polyId⊢ {Δ = Δ₁})

X⇒X⇒X : ∀ {Δ} → Ty (suc Δ)
X⇒X⇒X = Xᵗ ⇒ X⇒X

X₀⇒X₀⇒X₀ : Ty Δ₁
X₀⇒X₀⇒X₀ = X₀ ⇒ X₀⇒X₀

X∈X⇒X⇒X : ∀ {Δ} → Fin.zero ∈ᵗ X⇒X⇒X {Δ}
X∈X⇒X⇒X = ∈-fun-left var-∈

returnPolyAtX : GTerm Δ₀
returnPolyAtX =
  ((Λ (ƛ X₀ ⇒ polyAtX)) `[ ★ ]) ·[ 35 ] nat 7

returnPolyAtX⊢ : Δ₀ ∣ [] ⊢ returnPolyAtX ⦂ ★⇒★₀
returnPolyAtX⊢ =
  fromJust
    (type-check-expect Δ₀ [] returnPolyAtX ★⇒★₀)
    is-just

badDynBool : GTerm Δ₀
badDynBool =
  (dynId ·[ 36 ] ($ (κ𝔹 true))) ⊕[ addℕ at 37 ] nat 1

badDynBool⊢ : Δ₀ ∣ [] ⊢ badDynBool ⦂ ℕ₀
badDynBool⊢ =
  fromJust
    (type-check-expect Δ₀ [] badDynBool ℕ₀)
    is-just

returnPolyFun : GTerm Δ₀
returnPolyFun = ƛ ℕ₀ ⇒ polyId

returnPolyFun⊢ : Δ₀ ∣ [] ⊢ returnPolyFun ⦂ ℕ₀ ⇒ ∀X⇒X₀
returnPolyFun⊢ = ⊢ƛ (polyId⊢ {Δ = Δ₀})

returnPolyUse : GTerm Δ₀
returnPolyUse = ((returnPolyFun ·[ 41 ] nat 0) `[ ℕ₀ ]) ·[ 42 ] nat 2

returnPolyUse⊢ : Δ₀ ∣ [] ⊢ returnPolyUse ⦂ ℕ₀
returnPolyUse⊢ =
  fromJust
    (type-check-expect Δ₀ [] returnPolyUse ℕ₀)
    is-just

usePolyNat : GTerm Δ₀
usePolyNat = ƛ ∀X⇒X₀ ⇒ (((` 0) `[ ℕ₀ ]) ·[ 43 ] nat 5)

usePolyNat⊢ : Δ₀ ∣ [] ⊢ usePolyNat ⦂ ∀X⇒X₀ ⇒ ℕ₀
usePolyNat⊢ =
  ⊢ƛ (⊢· (⊢• (⊢` Z)) (nat⊢ 5) (id (‵ `ℕ)))

higherOrderPolyArg : GTerm Δ₀
higherOrderPolyArg = usePolyNat ·[ 44 ] polyId

higherOrderPolyArg⊢ : Δ₀ ∣ [] ⊢ higherOrderPolyArg ⦂ ℕ₀
higherOrderPolyArg⊢ =
  fromJust
    (type-check-expect Δ₀ [] higherOrderPolyArg ℕ₀)
    is-just

higherOrderSharedArg : GTerm Δ₀
higherOrderSharedArg = usePolyNat ·[ 45 ] polyIdSelf

higherOrderSharedArg⊢ : Δ₀ ∣ [] ⊢ higherOrderSharedArg ⦂ ℕ₀
higherOrderSharedArg⊢ =
  fromJust
    (type-check-expect Δ₀ [] higherOrderSharedArg ℕ₀)
    is-just

------------------------------------------------------------------------
-- Phase-1 catalog entries
------------------------------------------------------------------------

-- a. Baseline: direct source analogue at ★; expected clean.
baseline-direct : SourceEntry
baseline-direct =
  same-entry {M = polyId★App} {A = ★} polyId★App⊢ 40

-- a. Baseline: exact Nat instantiation; expected clean.
baseline-nat-direct : SourceEntry
baseline-nat-direct =
  same-entry {M = polyIdNatApp} {A = ℕ₀} polyIdNatApp⊢ 35

-- a. Baseline: exact Bool instantiation; expected clean.
baseline-bool-direct : SourceEntry
baseline-bool-direct =
  same-entry {M = polyIdBoolApp} {A = 𝔹₀} polyIdBoolApp⊢ 35

-- a. Baseline: left instantiates a polymorphic value, right uses ★; clean.
baseline-poly-to-dyn : SourceEntry
baseline-poly-to-dyn =
  source-entry
    ((polyId `[ ℕᵗ ]) ·[ 1 ] nat 7)
    (dynId ·[ 1 ] nat 7)
    40 40 ℕ₀ ★ I.ι⊑★
    (⊢· (⊢• (polyId⊢ {Δ = Δ₀})) (nat⊢ 7) (id (‵ `ℕ)))
    (⊢· dynId⊢ (nat⊢ 7) (？ (id (‵ `ℕ))))
    (·⊑·ᴳ polyIdℕ⊑dynId (κ⊑κᴳ (κℕ 7))
      (id (‵ `ℕ)) (？ (id (‵ `ℕ))))

-- queued: `(ΛX.λx:X.x)[ℕ] 5 ⊑ (λx:★.x) 5`; expected clean.
left-only-inst-path : SourceEntry
left-only-inst-path =
  source-entry
    leftOnlyInstPathᴸ
    leftOnlyInstPathᴿ
    40 40 ℕ₀ ★ I.ι⊑★
    leftOnlyInstPathᴸ⊢
    leftOnlyInstPathᴿ⊢
    leftOnlyInstPath⊑

-- a. Baseline: Bool variant of the polymorphic-to-dynamic run; clean.
baseline-bool-to-dyn : SourceEntry
baseline-bool-to-dyn =
  source-entry
    ((polyId {Δ = Δ₀} `[ 𝔹₀ ]) ·[ 2 ] bool)
    (dynId ·[ 2 ] bool)
    40 40 𝔹₀ ★ I.ι⊑★
    (⊢· (⊢• (polyId⊢ {Δ = Δ₀})) bool⊢ (id (‵ `𝔹)))
    (⊢· dynId⊢ bool⊢ (？ (id (‵ `𝔹))))
    (·⊑·ᴳ polyId𝔹⊑dynId (κ⊑κᴳ (κ𝔹 true))
      (id (‵ `𝔹)) (？ (id (‵ `𝔹))))

-- a. Baseline: function value compared to ★ ⇒ ★; expected clean.
baseline-fun-to-dyn : SourceEntry
baseline-fun-to-dyn =
  source-entry
    (polyId {Δ = Δ₀} `[ ℕ₀ ])
    dynId
    20 20 (ℕ₀ ⇒ ℕ₀) ★⇒★₀ ℕ⇒ℕ⊑★⇒★₀
    (⊢• (polyId⊢ {Δ = Δ₀}))
    dynId⊢
    polyIdℕ⊑dynId

-- a. Baseline: higher-order source analogue of the Examples2 detour; clean.
baseline-higher-order : SourceEntry
baseline-higher-order =
  same-entry
    {M = polyId {Δ = Δ₀} `[ ℕ₀ ]}
    {A = ℕ₀ ⇒ ℕ₀}
    (⊢• (polyId⊢ {Δ = Δ₀}))
    30

-- b. Seal-chain depth 1: variable passes through one type instantiation; clean.
seal-chain-depth1 : SourceEntry
seal-chain-depth1 =
  same-entry
    {M = runChainℕ (` 0)}
    {A = ℕ₀}
    (runChainX⊢ {body = ` 0} (⊢` Z))
    50

-- b. Seal-chain depth 2: one source variable instantiation; expected clean.
seal-chain-depth2 : SourceEntry
seal-chain-depth2 =
  same-entry {M = returnPolyAtX} {A = ★⇒★₀} returnPolyAtX⊢ 50

-- b. Store telescope plus two source variable instantiations; expected clean.
seal-chain-depth3 : SourceEntry
seal-chain-depth3 =
  same-entry
    {M = runChainℕ idAtX²}
    {A = ℕ₀}
    (runChainX⊢ {body = idAtX²} idAtX²⊢)
    70

-- b. Store telescope with three nested source instantiations; expected clean.
seal-chain-depth4 : SourceEntry
seal-chain-depth4 =
  same-entry
    {M = runChainℕ idAtX³}
    {A = ℕ₀}
    (runChainX⊢ {body = idAtX³} idAtX³⊢)
    80

-- c. Instantiation-order skew analogue: one nested instantiation; clean.
skew-tag-depth2 : SourceEntry
skew-tag-depth2 =
  same-entry
    {M = runChainℕ idAtX}
    {A = ℕ₀}
    (runChainX⊢ {body = idAtX} idAtX⊢)
    80

-- c. Instantiation-order skew analogue: two nested instantiations; clean.
skew-tag-depth3 : SourceEntry
skew-tag-depth3 =
  same-entry
    {M = runChainℕ idAtX²}
    {A = ℕ₀}
    (runChainX⊢ {body = idAtX²} idAtX²⊢)
    90

-- c. Skew with right-side ★ instantiation; source-admitted and clean.
skew-star-inst : SourceEntry
skew-star-inst =
  same-entry
    {M = runChain★Inst starBody}
    {A = ★}
    (runChain★Inst⊢ {body = starBody} starBody⊢)
    70

-- d. Tag-boundary source analogue over a depth-4 chain; expected clean.
tag-boundary-depth4 : SourceEntry
tag-boundary-depth4 =
  same-entry
    {M = runChainℕ idAtX³}
    {A = ℕ₀}
    (runChainX⊢ {body = idAtX³} idAtX³⊢)
    100

-- d. Tag-boundary source analogue with ★ instantiation; expected clean.
tag-boundary-star-inst : SourceEntry
tag-boundary-star-inst =
  same-entry
    {M = runChain★Inst starBody}
    {A = ★}
    (runChain★Inst⊢ {body = starBody} starBody⊢)
    70

-- e. gen/inst interleaving: polymorphic result returned by a call; clean.
gen-inst-return-poly : SourceEntry
gen-inst-return-poly =
  same-entry {M = returnPolyUse} {A = ℕ₀} returnPolyUse⊢ 70

-- queued:
-- `((λf:(∀X.X→X).f)·(λx:★.x))[ℕ] 5
--    ⊑ ((λf:★→★.f)·(λx:★.x)) 5`; expected clean.
left-only-gen-path : SourceEntry
left-only-gen-path =
  source-entry
    leftOnlyGenPathᴸ
    leftOnlyGenPathᴿ
    80 80 ℕ₀ ★ I.ι⊑★
    leftOnlyGenPathᴸ⊢
    leftOnlyGenPathᴿ⊢
    leftOnlyGenPath⊑

-- e. gen/inst interleaving: self application then Nat instantiation; clean.
gen-inst-self-nat : SourceEntry
gen-inst-self-nat =
  same-entry {M = polyIdSelfNatApp} {A = ℕ₀} polyIdSelfNatApp⊢ 70

-- f. ∀ wrapper crosses an application boundary and then ★; expected clean.
reveal-conceal-self-star : SourceEntry
reveal-conceal-self-star =
  same-entry {M = polyIdSelfStarApp} {A = ★} polyIdSelfStarApp⊢ 80

-- f. Returned ∀ wrapper crosses a term application; expected clean.
reveal-conceal-return-poly : SourceEntry
reveal-conceal-return-poly =
  same-entry {M = returnPolyUse} {A = ℕ₀} returnPolyUse⊢ 80

-- g. Shared store prefix, Nat suffix; expected clean.
shared-prefix-nat : SourceEntry
shared-prefix-nat =
  same-entry {M = polyIdSelfNatApp} {A = ℕ₀} polyIdSelfNatApp⊢ 80

-- g. Shared store prefix, Bool suffix; expected clean.
shared-prefix-bool : SourceEntry
shared-prefix-bool =
  same-entry {M = polyIdSelfBoolApp} {A = 𝔹₀} polyIdSelfBoolApp⊢ 80

-- g. Shared store prefix, ★ suffix; expected clean.
shared-prefix-star : SourceEntry
shared-prefix-star =
  same-entry {M = polyIdSelfStarApp} {A = ★} polyIdSelfStarApp⊢ 80

-- h. Higher-order: callee instantiates polymorphic argument; expected clean.
higher-order-poly-arg : SourceEntry
higher-order-poly-arg =
  same-entry {M = higherOrderPolyArg} {A = ℕ₀} higherOrderPolyArg⊢ 70

-- h. Higher-order with shared-prefix argument; expected clean.
higher-order-shared-arg : SourceEntry
higher-order-shared-arg =
  same-entry
    {M = higherOrderSharedArg}
    {A = ℕ₀}
    higherOrderSharedArg⊢
    90

-- i. Adversarial source analogue of the center-crossing chain; clean.
adversarial-source-chain : SourceEntry
adversarial-source-chain =
  same-entry
    {M = runChainℕ idAtX³}
    {A = ℕ₀}
    (runChainX⊢ {body = idAtX³} idAtX³⊢)
    120

-- i. Adversarial ★-right source analogue; expected clean.
adversarial-source-star : SourceEntry
adversarial-source-star =
  same-entry
    {M = runChain★Inst starBody}
    {A = ★}
    (runChain★Inst⊢ {body = starBody} starBody⊢)
    90

-- j. Blame path: dynamic Bool projected at Nat by a primitive; clean screen.
blame-dyn-bool : SourceEntry
blame-dyn-bool =
  same-entry {M = badDynBool} {A = ℕ₀} badDynBool⊢ 30

------------------------------------------------------------------------
-- Compiler fidelity gates
------------------------------------------------------------------------

baseline-direct-skeleton-gate : skeleton-gate baseline-direct
baseline-direct-skeleton-gate = refl

baseline-nat-direct-skeleton-gate : skeleton-gate baseline-nat-direct
baseline-nat-direct-skeleton-gate = refl

baseline-bool-direct-skeleton-gate : skeleton-gate baseline-bool-direct
baseline-bool-direct-skeleton-gate = refl

baseline-poly-to-dyn-skeleton-gate : skeleton-gate baseline-poly-to-dyn
baseline-poly-to-dyn-skeleton-gate = refl

left-only-inst-path-skeleton-gate : skeleton-gate left-only-inst-path
left-only-inst-path-skeleton-gate = refl

baseline-bool-to-dyn-skeleton-gate : skeleton-gate baseline-bool-to-dyn
baseline-bool-to-dyn-skeleton-gate = refl

baseline-fun-to-dyn-skeleton-gate : skeleton-gate baseline-fun-to-dyn
baseline-fun-to-dyn-skeleton-gate = refl

baseline-higher-order-skeleton-gate :
  skeleton-gate baseline-higher-order
baseline-higher-order-skeleton-gate = refl

seal-chain-depth1-skeleton-gate : skeleton-gate seal-chain-depth1
seal-chain-depth1-skeleton-gate = refl

seal-chain-depth2-skeleton-gate : skeleton-gate seal-chain-depth2
seal-chain-depth2-skeleton-gate = refl

seal-chain-depth3-skeleton-gate : skeleton-gate seal-chain-depth3
seal-chain-depth3-skeleton-gate = refl

seal-chain-depth4-skeleton-gate : skeleton-gate seal-chain-depth4
seal-chain-depth4-skeleton-gate = refl

skew-tag-depth2-skeleton-gate : skeleton-gate skew-tag-depth2
skew-tag-depth2-skeleton-gate = refl

skew-tag-depth3-skeleton-gate : skeleton-gate skew-tag-depth3
skew-tag-depth3-skeleton-gate = refl

skew-star-inst-skeleton-gate : skeleton-gate skew-star-inst
skew-star-inst-skeleton-gate = refl

tag-boundary-depth4-skeleton-gate : skeleton-gate tag-boundary-depth4
tag-boundary-depth4-skeleton-gate = refl

tag-boundary-star-inst-skeleton-gate :
  skeleton-gate tag-boundary-star-inst
tag-boundary-star-inst-skeleton-gate = refl

gen-inst-return-poly-skeleton-gate :
  skeleton-gate gen-inst-return-poly
gen-inst-return-poly-skeleton-gate = refl

left-only-gen-path-skeleton-gate : skeleton-gate left-only-gen-path
left-only-gen-path-skeleton-gate = refl

gen-inst-self-nat-skeleton-gate : skeleton-gate gen-inst-self-nat
gen-inst-self-nat-skeleton-gate = refl

reveal-conceal-self-star-skeleton-gate :
  skeleton-gate reveal-conceal-self-star
reveal-conceal-self-star-skeleton-gate = refl

reveal-conceal-return-poly-skeleton-gate :
  skeleton-gate reveal-conceal-return-poly
reveal-conceal-return-poly-skeleton-gate = refl

shared-prefix-nat-skeleton-gate : skeleton-gate shared-prefix-nat
shared-prefix-nat-skeleton-gate = refl

shared-prefix-bool-skeleton-gate : skeleton-gate shared-prefix-bool
shared-prefix-bool-skeleton-gate = refl

shared-prefix-star-skeleton-gate : skeleton-gate shared-prefix-star
shared-prefix-star-skeleton-gate = refl

higher-order-poly-arg-skeleton-gate :
  skeleton-gate higher-order-poly-arg
higher-order-poly-arg-skeleton-gate = refl

higher-order-shared-arg-skeleton-gate :
  skeleton-gate higher-order-shared-arg
higher-order-shared-arg-skeleton-gate = refl

adversarial-source-chain-skeleton-gate :
  skeleton-gate adversarial-source-chain
adversarial-source-chain-skeleton-gate = refl

adversarial-source-star-skeleton-gate :
  skeleton-gate adversarial-source-star
adversarial-source-star-skeleton-gate = refl

blame-dyn-bool-skeleton-gate : skeleton-gate blame-dyn-bool
blame-dyn-bool-skeleton-gate = refl

------------------------------------------------------------------------
-- Refl-run screening gates
------------------------------------------------------------------------

baseline-direct-screens-clean :
  RS.crossing-suspect (compiled baseline-direct) ≡ RS.clean
baseline-direct-screens-clean = refl

baseline-nat-direct-screens-clean :
  RS.crossing-suspect (compiled baseline-nat-direct) ≡ RS.clean
baseline-nat-direct-screens-clean = refl

baseline-bool-direct-screens-clean :
  RS.crossing-suspect (compiled baseline-bool-direct) ≡ RS.clean
baseline-bool-direct-screens-clean = refl

baseline-poly-to-dyn-screens-clean :
  RS.crossing-suspect (compiled baseline-poly-to-dyn) ≡ RS.clean
baseline-poly-to-dyn-screens-clean = refl

left-only-inst-path-screens-clean :
  RS.crossing-suspect (compiled left-only-inst-path) ≡ RS.clean
left-only-inst-path-screens-clean = refl

baseline-bool-to-dyn-screens-clean :
  RS.crossing-suspect (compiled baseline-bool-to-dyn) ≡ RS.clean
baseline-bool-to-dyn-screens-clean = refl

baseline-fun-to-dyn-screens-clean :
  RS.crossing-suspect (compiled baseline-fun-to-dyn) ≡ RS.clean
baseline-fun-to-dyn-screens-clean = refl

baseline-higher-order-screens-clean :
  RS.crossing-suspect (compiled baseline-higher-order) ≡ RS.clean
baseline-higher-order-screens-clean = refl

seal-chain-depth1-screens-clean :
  RS.crossing-suspect (compiled seal-chain-depth1) ≡ RS.clean
seal-chain-depth1-screens-clean = refl

seal-chain-depth2-screens-clean :
  RS.crossing-suspect (compiled seal-chain-depth2) ≡ RS.clean
seal-chain-depth2-screens-clean = refl

seal-chain-depth3-screens-clean :
  RS.crossing-suspect (compiled seal-chain-depth3) ≡ RS.clean
seal-chain-depth3-screens-clean = refl

seal-chain-depth4-screens-clean :
  RS.crossing-suspect (compiled seal-chain-depth4) ≡ RS.clean
seal-chain-depth4-screens-clean = refl

skew-tag-depth2-screens-clean :
  RS.crossing-suspect (compiled skew-tag-depth2) ≡ RS.clean
skew-tag-depth2-screens-clean = refl

skew-tag-depth3-screens-clean :
  RS.crossing-suspect (compiled skew-tag-depth3) ≡ RS.clean
skew-tag-depth3-screens-clean = refl

skew-star-inst-screens-clean :
  RS.crossing-suspect (compiled skew-star-inst) ≡ RS.clean
skew-star-inst-screens-clean = refl

tag-boundary-depth4-screens-clean :
  RS.crossing-suspect (compiled tag-boundary-depth4) ≡ RS.clean
tag-boundary-depth4-screens-clean = refl

tag-boundary-star-inst-screens-clean :
  RS.crossing-suspect (compiled tag-boundary-star-inst) ≡ RS.clean
tag-boundary-star-inst-screens-clean = refl

gen-inst-return-poly-screens-clean :
  RS.crossing-suspect (compiled gen-inst-return-poly) ≡ RS.clean
gen-inst-return-poly-screens-clean = refl

left-only-gen-path-screens-clean :
  RS.crossing-suspect (compiled left-only-gen-path) ≡ RS.clean
left-only-gen-path-screens-clean = refl

gen-inst-self-nat-screens-clean :
  RS.crossing-suspect (compiled gen-inst-self-nat) ≡ RS.clean
gen-inst-self-nat-screens-clean = refl

reveal-conceal-self-star-screens-clean :
  RS.crossing-suspect (compiled reveal-conceal-self-star) ≡ RS.clean
reveal-conceal-self-star-screens-clean = refl

reveal-conceal-return-poly-screens-clean :
  RS.crossing-suspect (compiled reveal-conceal-return-poly) ≡ RS.clean
reveal-conceal-return-poly-screens-clean = refl

shared-prefix-nat-screens-clean :
  RS.crossing-suspect (compiled shared-prefix-nat) ≡ RS.clean
shared-prefix-nat-screens-clean = refl

shared-prefix-bool-screens-clean :
  RS.crossing-suspect (compiled shared-prefix-bool) ≡ RS.clean
shared-prefix-bool-screens-clean = refl

shared-prefix-star-screens-clean :
  RS.crossing-suspect (compiled shared-prefix-star) ≡ RS.clean
shared-prefix-star-screens-clean = refl

higher-order-poly-arg-screens-clean :
  RS.crossing-suspect (compiled higher-order-poly-arg) ≡ RS.clean
higher-order-poly-arg-screens-clean = refl

higher-order-shared-arg-screens-clean :
  RS.crossing-suspect (compiled higher-order-shared-arg) ≡ RS.clean
higher-order-shared-arg-screens-clean = refl

adversarial-source-chain-screens-clean :
  RS.crossing-suspect (compiled adversarial-source-chain) ≡ RS.clean
adversarial-source-chain-screens-clean = refl

adversarial-source-star-screens-clean :
  RS.crossing-suspect (compiled adversarial-source-star) ≡ RS.clean
adversarial-source-star-screens-clean = refl

blame-dyn-bool-screens-clean :
  RS.crossing-suspect (compiled blame-dyn-bool) ≡ RS.clean
blame-dyn-bool-screens-clean = refl
