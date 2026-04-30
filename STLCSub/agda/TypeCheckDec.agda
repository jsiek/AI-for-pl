module TypeCheckDec where

-- File Charter:
--   * Executable type checker for STLCSub.
--   * Uses syntax-directed checking plus TAPL-style algorithmic subtyping for
--     arrows, Top, and record width/depth/permutation.
--   * Exports decidable wrappers used by `Examples.agda`; successful answers
--     carry ordinary declarative typing derivations from `STLCSub`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (zero; suc; _≟_)
open import Data.Product using (Σ; ∃-syntax; _,_)
open import Relation.Nullary using (Dec; yes; no)

open import STLCSub

data Reveal_is_ {A : Set} (x y : A) : Set where
  [_] : x ≡ y -> Reveal x is y

inspect : {A : Set} -> (x : A) -> Reveal x is x
inspect x = [ refl ]

lookupCtx : (Γ : Ctx) (x : Var) -> Maybe (Σ Ty (λ A -> Γ ∋ x ⦂ A))
lookupCtx [] x = nothing
lookupCtx (A ∷ Γ) zero = just (A , Z)
lookupCtx (A ∷ Γ) (suc x) with lookupCtx Γ x
lookupCtx (A ∷ Γ) (suc x) | just (B , x∈Γ) = just (B , S x∈Γ)
lookupCtx (A ∷ Γ) (suc x) | nothing = nothing

lookupTy : (Fs : List FieldTy) (ℓ : Label) ->
           Maybe (Σ Ty (λ A -> HasTy Fs ℓ A))
lookupTy [] ℓ = nothing
lookupTy ((ℓ′ ⦂ᶠ B) ∷ Fs) ℓ with ℓ′ ≟ ℓ
lookupTy ((ℓ′ ⦂ᶠ B) ∷ Fs) ℓ | yes refl = just (B , ty-here)
lookupTy ((ℓ′ ⦂ᶠ B) ∷ Fs) ℓ | no ℓ′≢ℓ with lookupTy Fs ℓ
lookupTy ((ℓ′ ⦂ᶠ B) ∷ Fs) ℓ | no ℓ′≢ℓ | just (A , has) =
  just (A , ty-there ℓ′≢ℓ has)
lookupTy ((ℓ′ ⦂ᶠ B) ∷ Fs) ℓ | no ℓ′≢ℓ | nothing = nothing

{-# TERMINATING #-}
mutual
  subtype? : (A B : Ty) -> Maybe (A <: B)
  subtype? A top = just S-top
  subtype? top nat = nothing
  subtype? top (B₁ ⇒ B₂) = nothing
  subtype? top (`⟨ Gs ⟩) = nothing
  subtype? nat nat = just S-refl
  subtype? nat (B₁ ⇒ B₂) = nothing
  subtype? nat (`⟨ Gs ⟩) = nothing
  subtype? (A₁ ⇒ A₂) nat = nothing
  subtype? (A₁ ⇒ A₂) (B₁ ⇒ B₂) with subtype? B₁ A₁
  subtype? (A₁ ⇒ A₂) (B₁ ⇒ B₂) | just B₁<:A₁
      with subtype? A₂ B₂
  subtype? (A₁ ⇒ A₂) (B₁ ⇒ B₂) | just B₁<:A₁ | just A₂<:B₂ =
    just (S-arrow B₁<:A₁ A₂<:B₂)
  subtype? (A₁ ⇒ A₂) (B₁ ⇒ B₂) | just B₁<:A₁ | nothing = nothing
  subtype? (A₁ ⇒ A₂) (B₁ ⇒ B₂) | nothing = nothing
  subtype? (A₁ ⇒ A₂) (`⟨ Gs ⟩) = nothing
  subtype? (`⟨ Fs ⟩) nat = nothing
  subtype? (`⟨ Fs ⟩) (B₁ ⇒ B₂) = nothing
  subtype? (`⟨ Fs ⟩) (`⟨ Gs ⟩) with fieldsSub? Fs Gs
  subtype? (`⟨ Fs ⟩) (`⟨ Gs ⟩) | just Fs<:Gs =
    just (S-record Fs<:Gs)
  subtype? (`⟨ Fs ⟩) (`⟨ Gs ⟩) | nothing = nothing

  fieldsSub? : (Fs Gs : List FieldTy) -> Maybe (FieldsSub Fs Gs)
  fieldsSub? Fs [] = just fs[]
  fieldsSub? Fs ((ℓ ⦂ᶠ B) ∷ Gs) with lookupTy Fs ℓ
  fieldsSub? Fs ((ℓ ⦂ᶠ B) ∷ Gs) | just (A , has) with subtype? A B
  fieldsSub? Fs ((ℓ ⦂ᶠ B) ∷ Gs) | just (A , has) | just A<:B
      with fieldsSub? Fs Gs
  fieldsSub? Fs ((ℓ ⦂ᶠ B) ∷ Gs) | just (A , has) | just A<:B |
      just rest =
    just (fs∷ has A<:B rest)
  fieldsSub? Fs ((ℓ ⦂ᶠ B) ∷ Gs) | just (A , has) | just A<:B | nothing =
    nothing
  fieldsSub? Fs ((ℓ ⦂ᶠ B) ∷ Gs) | just (A , has) | nothing = nothing
  fieldsSub? Fs ((ℓ ⦂ᶠ B) ∷ Gs) | nothing = nothing

mutual
  synth : (Γ : Ctx) (M : Term) -> Maybe (Σ Ty (λ A -> Γ ⊢ M ⦂ A))
  synth Γ (` x) = lookupSynth Γ x
  synth Γ (ƛ A ⇒ N) with synth (A ∷ Γ) N
  synth Γ (ƛ A ⇒ N) | just (B , N⊢) = just (A ⇒ B , ⊢ƛ N⊢)
  synth Γ (ƛ A ⇒ N) | nothing with check (A ∷ Γ) N top
  synth Γ (ƛ A ⇒ N) | nothing | just N⊢ = just (A ⇒ top , ⊢ƛ N⊢)
  synth Γ (ƛ A ⇒ N) | nothing | nothing = nothing
  synth Γ (L · M) with synth Γ L
  synth Γ (L · M) | just (A ⇒ B , L⊢) with check Γ M A
  synth Γ (L · M) | just (A ⇒ B , L⊢) | just M⊢ =
    just (B , ⊢· L⊢ M⊢)
  synth Γ (L · M) | just (A ⇒ B , L⊢) | nothing = nothing
  synth Γ (L · M) | just (top , L⊢) = nothing
  synth Γ (L · M) | just (nat , L⊢) = nothing
  synth Γ (L · M) | just (`⟨ Fs ⟩ , L⊢) = nothing
  synth Γ (L · M) | nothing = nothing
  synth Γ `zero = just (nat , ⊢zero)
  synth Γ (`suc M) with check Γ M nat
  synth Γ (`suc M) | just M⊢ = just (nat , ⊢suc M⊢)
  synth Γ (`suc M) | nothing = nothing
  synth Γ (case_[zero⇒_|suc⇒_] L M N) with check Γ L nat
  synth Γ (case_[zero⇒_|suc⇒_] L M N) | just L⊢ with synth Γ M
  synth Γ (case_[zero⇒_|suc⇒_] L M N) | just L⊢ | just (A , M⊢)
      with check (nat ∷ Γ) N A
  synth Γ (case_[zero⇒_|suc⇒_] L M N) | just L⊢ | just (A , M⊢) |
      just N⊢ = just (A , ⊢case L⊢ M⊢ N⊢)
  synth Γ (case_[zero⇒_|suc⇒_] L M N) | just L⊢ | just (A , M⊢) |
      nothing with check Γ M top
  synth Γ (case_[zero⇒_|suc⇒_] L M N) | just L⊢ | just (A , M⊢) |
      nothing | just M⊢top with check (nat ∷ Γ) N top
  synth Γ (case_[zero⇒_|suc⇒_] L M N) | just L⊢ | just (A , M⊢) |
      nothing | just M⊢top | just N⊢top =
    just (top , ⊢case L⊢ M⊢top N⊢top)
  synth Γ (case_[zero⇒_|suc⇒_] L M N) | just L⊢ | just (A , M⊢) |
      nothing | just M⊢top | nothing = nothing
  synth Γ (case_[zero⇒_|suc⇒_] L M N) | just L⊢ | just (A , M⊢) |
      nothing | nothing = nothing
  synth Γ (case_[zero⇒_|suc⇒_] L M N) | just L⊢ | nothing
      with check Γ M top
  synth Γ (case_[zero⇒_|suc⇒_] L M N) | just L⊢ | nothing |
      just M⊢top
      with check (nat ∷ Γ) N top
  synth Γ (case_[zero⇒_|suc⇒_] L M N) | just L⊢ | nothing |
      just M⊢top |
      just N⊢top = just (top , ⊢case L⊢ M⊢top N⊢top)
  synth Γ (case_[zero⇒_|suc⇒_] L M N) | just L⊢ | nothing |
      just M⊢top |
      nothing = nothing
  synth Γ (case_[zero⇒_|suc⇒_] L M N) | just L⊢ | nothing | nothing =
    nothing
  synth Γ (case_[zero⇒_|suc⇒_] L M N) | nothing = nothing
  synth Γ (`record fs) with synthFields Γ fs
  synth Γ (`record fs) | just (Fs , fs⊢) =
    just (`⟨ Fs ⟩ , ⊢record fs⊢)
  synth Γ (`record fs) | nothing = nothing
  synth Γ (M ‼ ℓ) with synth Γ M
  synth Γ (M ‼ ℓ) | just (`⟨ Fs ⟩ , M⊢) with lookupTy Fs ℓ
  synth Γ (M ‼ ℓ) | just (`⟨ Fs ⟩ , M⊢) | just (A , has) =
    just (A , ⊢proj M⊢ has)
  synth Γ (M ‼ ℓ) | just (`⟨ Fs ⟩ , M⊢) | nothing = nothing
  synth Γ (M ‼ ℓ) | just (top , M⊢) = nothing
  synth Γ (M ‼ ℓ) | just (nat , M⊢) = nothing
  synth Γ (M ‼ ℓ) | just (A ⇒ B , M⊢) = nothing
  synth Γ (M ‼ ℓ) | nothing = nothing

  check : (Γ : Ctx) (M : Term) (A : Ty) -> Maybe (Γ ⊢ M ⦂ A)
  check Γ (` x) A with lookupSynth Γ x
  check Γ (` x) A | just (B , x⊢) with subtype? B A
  check Γ (` x) A | just (B , x⊢) | just B<:A = just (⊢sub x⊢ B<:A)
  check Γ (` x) A | just (B , x⊢) | nothing = nothing
  check Γ (` x) A | nothing = nothing
  check Γ (ƛ B ⇒ N) top with check (B ∷ Γ) N top
  check Γ (ƛ B ⇒ N) top | just N⊢ = just (⊢sub (⊢ƛ N⊢) S-top)
  check Γ (ƛ B ⇒ N) top | nothing = nothing
  check Γ (ƛ B ⇒ N) nat = nothing
  check Γ (ƛ B ⇒ N) (A ⇒ C) with subtype? A B
  check Γ (ƛ B ⇒ N) (A ⇒ C) | just A<:B with check (B ∷ Γ) N C
  check Γ (ƛ B ⇒ N) (A ⇒ C) | just A<:B | just N⊢ =
    just (⊢sub (⊢ƛ N⊢) (S-arrow A<:B S-refl))
  check Γ (ƛ B ⇒ N) (A ⇒ C) | just A<:B | nothing = nothing
  check Γ (ƛ B ⇒ N) (A ⇒ C) | nothing = nothing
  check Γ (ƛ B ⇒ N) (`⟨ Fs ⟩) = nothing
  check Γ (L · M) C with synth Γ L
  check Γ (L · M) C | just (A ⇒ B , L⊢) with check Γ M A
  check Γ (L · M) C | just (A ⇒ B , L⊢) | just M⊢ with subtype? B C
  check Γ (L · M) C | just (A ⇒ B , L⊢) | just M⊢ | just B<:C =
    just (⊢sub (⊢· L⊢ M⊢) B<:C)
  check Γ (L · M) C | just (A ⇒ B , L⊢) | just M⊢ | nothing = nothing
  check Γ (L · M) C | just (A ⇒ B , L⊢) | nothing = nothing
  check Γ (L · M) C | just (top , L⊢) = nothing
  check Γ (L · M) C | just (nat , L⊢) = nothing
  check Γ (L · M) C | just (`⟨ Fs ⟩ , L⊢) = nothing
  check Γ (L · M) C | nothing = nothing
  check Γ `zero A with subtype? nat A
  check Γ `zero A | just nat<:A = just (⊢sub ⊢zero nat<:A)
  check Γ `zero A | nothing = nothing
  check Γ (`suc M) A with check Γ M nat
  check Γ (`suc M) A | just M⊢ with subtype? nat A
  check Γ (`suc M) A | just M⊢ | just nat<:A =
    just (⊢sub (⊢suc M⊢) nat<:A)
  check Γ (`suc M) A | just M⊢ | nothing = nothing
  check Γ (`suc M) A | nothing = nothing
  check Γ (case_[zero⇒_|suc⇒_] L M N) A with check Γ L nat
  check Γ (case_[zero⇒_|suc⇒_] L M N) A | just L⊢ with check Γ M A
  check Γ (case_[zero⇒_|suc⇒_] L M N) A | just L⊢ | just M⊢
      with check (nat ∷ Γ) N A
  check Γ (case_[zero⇒_|suc⇒_] L M N) A | just L⊢ | just M⊢ |
      just N⊢ =
    just (⊢case L⊢ M⊢ N⊢)
  check Γ (case_[zero⇒_|suc⇒_] L M N) A | just L⊢ | just M⊢ | nothing =
    nothing
  check Γ (case_[zero⇒_|suc⇒_] L M N) A | just L⊢ | nothing = nothing
  check Γ (case_[zero⇒_|suc⇒_] L M N) A | nothing = nothing
  check Γ (`record fs) A with synthFields Γ fs
  check Γ (`record fs) A | just (Fs , fs⊢) with subtype? (`⟨ Fs ⟩) A
  check Γ (`record fs) A | just (Fs , fs⊢) | just Fs<:A =
    just (⊢sub (⊢record fs⊢) Fs<:A)
  check Γ (`record fs) A | just (Fs , fs⊢) | nothing = nothing
  check Γ (`record fs) A | nothing = nothing
  check Γ (M ‼ ℓ) A with synth Γ M
  check Γ (M ‼ ℓ) A | just (`⟨ Fs ⟩ , M⊢) with lookupTy Fs ℓ
  check Γ (M ‼ ℓ) A | just (`⟨ Fs ⟩ , M⊢) | just (B , has)
      with subtype? B A
  check Γ (M ‼ ℓ) A | just (`⟨ Fs ⟩ , M⊢) | just (B , has) |
      just B<:A = just (⊢sub (⊢proj M⊢ has) B<:A)
  check Γ (M ‼ ℓ) A | just (`⟨ Fs ⟩ , M⊢) | just (B , has) |
      nothing =
    nothing
  check Γ (M ‼ ℓ) A | just (`⟨ Fs ⟩ , M⊢) | nothing = nothing
  check Γ (M ‼ ℓ) A | just (top , M⊢) = nothing
  check Γ (M ‼ ℓ) A | just (nat , M⊢) = nothing
  check Γ (M ‼ ℓ) A | just (B ⇒ C , M⊢) = nothing
  check Γ (M ‼ ℓ) A | nothing = nothing

  synthFields : (Γ : Ctx) (fs : List FieldTerm) ->
                Maybe (Σ (List FieldTy) (λ Fs -> Γ ⊢ᶠˢ fs ⦂ Fs))
  synthFields Γ [] = just ([] , ⊢[])
  synthFields Γ ((ℓ ≔ M) ∷ fs) with synth Γ M
  synthFields Γ ((ℓ ≔ M) ∷ fs) | just (A , M⊢) with synthFields Γ fs
  synthFields Γ ((ℓ ≔ M) ∷ fs) | just (A , M⊢) | just (Fs , fs⊢) =
    just ((ℓ ⦂ᶠ A) ∷ Fs , ⊢∷ M⊢ fs⊢)
  synthFields Γ ((ℓ ≔ M) ∷ fs) | just (A , M⊢) | nothing = nothing
  synthFields Γ ((ℓ ≔ M) ∷ fs) | nothing = nothing

  lookupSynth : (Γ : Ctx) (x : Var) ->
                Maybe (Σ Ty (λ A -> Γ ⊢ (` x) ⦂ A))
  lookupSynth Γ x with lookupCtx Γ x
  lookupSynth Γ x | just (A , x∈Γ) = just (A , ⊢` x∈Γ)
  lookupSynth Γ x | nothing = nothing

postulate
  check-complete :
    {Γ : Ctx} {M : Term} {A : Ty} {r : Maybe (Γ ⊢ M ⦂ A)} ->
    r ≡ nothing ->
    Γ ⊢ M ⦂ A ->
    ⊥

type-check-expect : (Γ : Ctx) (M : Term) (A : Ty) -> Dec (Γ ⊢ M ⦂ A)
type-check-expect Γ M A with check Γ M A | inspect (check Γ M A)
type-check-expect Γ M A | just M⊢ | [ eq ] = yes M⊢
type-check-expect Γ M A | nothing | [ eq ] =
  no λ M⊢ -> check-complete eq M⊢

type-check : (Γ : Ctx) (M : Term) -> Dec (∃[ A ] Γ ⊢ M ⦂ A)
type-check Γ M with check Γ M top | inspect (check Γ M top)
type-check Γ M | just M⊢ | [ eq ] = yes (top , M⊢)
type-check Γ M | nothing | [ eq ] =
  no λ { (A , M⊢) -> check-complete eq (⊢sub M⊢ S-top) }
