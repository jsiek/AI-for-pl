module proof.TypeSafety where

-- File Charter:
--   * Private progress/preservation development for STLCSub.
--   * Proves substitution, subtyping lookup support, preservation, progress,
--     and the public multi-step type-safety corollary.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List)
open import Data.Nat using (suc)
open import Data.Product using (Σ; _,_; _×_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import STLCSub

------------------------------------------------------------------------
-- Subtyping support
------------------------------------------------------------------------

fieldsSub-lookup :
  {Fs Gs : List FieldTy} {ℓ : Label} {B : Ty} ->
  FieldsSub Fs Gs ->
  HasTy Gs ℓ B ->
  Σ Ty (λ A -> HasTy Fs ℓ A × (A <: B))
fieldsSub-lookup fs[] ()
fieldsSub-lookup (fs∷ h A<:B rest) ty-here = _ , h , A<:B
fieldsSub-lookup (fs∷ h A<:B rest) (ty-there neq has) =
  fieldsSub-lookup rest has

{-# TERMINATING #-}
mutual
  <:-trans : {A B C : Ty} -> A <: B -> B <: C -> A <: C
  <:-trans A<:B S-refl = A<:B
  <:-trans S-refl B<:C = B<:C
  <:-trans A<:B S-top = S-top
  <:-trans (S-arrow B₁<:A₁ A₂<:B₂) (S-arrow C₁<:B₁ B₂<:C₂) =
    S-arrow (<:-trans C₁<:B₁ B₁<:A₁) (<:-trans A₂<:B₂ B₂<:C₂)
  <:-trans (S-record Fs<:Gs) (S-record Gs<:Hs) =
    S-record (fieldsSub-trans Fs<:Gs Gs<:Hs)

  fieldsSub-trans :
    {Fs Gs Hs : List FieldTy} ->
    FieldsSub Fs Gs ->
    FieldsSub Gs Hs ->
    FieldsSub Fs Hs
  fieldsSub-trans Fs<:Gs fs[] = fs[]
  fieldsSub-trans Fs<:Gs (fs∷ h B<:C Gs<:Hs)
    with fieldsSub-lookup Fs<:Gs h
  fieldsSub-trans Fs<:Gs (fs∷ h B<:C Gs<:Hs) | A , hA , A<:B =
    fs∷ hA (<:-trans A<:B B<:C) (fieldsSub-trans Fs<:Gs Gs<:Hs)

------------------------------------------------------------------------
-- Structural lemmas
------------------------------------------------------------------------

mutual
  typing-rename :
    {Γ Δ : Ctx} {ρ : Rename} {M : Term} {A : Ty} ->
    (∀ {i B} -> Γ ∋ i ⦂ B -> Δ ∋ (ρ i) ⦂ B) ->
    Γ ⊢ M ⦂ A ->
    Δ ⊢ rename ρ M ⦂ A
  typing-rename hρ (⊢` hV) = ⊢` (hρ hV)
  typing-rename {Γ} {Δ} {ρ} hρ (⊢ƛ {A = A} hN) =
    ⊢ƛ (typing-rename hExt hN)
    where
      hExt : ∀ {i C} -> (A ∷ Γ) ∋ i ⦂ C -> (A ∷ Δ) ∋ ext ρ i ⦂ C
      hExt Z = Z
      hExt (S hV) = S (hρ hV)
  typing-rename hρ (⊢· hL hM) =
    ⊢· (typing-rename hρ hL) (typing-rename hρ hM)
  typing-rename hρ ⊢zero = ⊢zero
  typing-rename hρ (⊢suc hM) = ⊢suc (typing-rename hρ hM)
  typing-rename {Γ} {Δ} {ρ} hρ (⊢case hL hM hN) =
    ⊢case (typing-rename hρ hL) (typing-rename hρ hM)
           (typing-rename hExt hN)
    where
      hExt : ∀ {i C} -> (nat ∷ Γ) ∋ i ⦂ C -> (nat ∷ Δ) ∋ ext ρ i ⦂ C
      hExt Z = Z
      hExt (S hV) = S (hρ hV)
  typing-rename hρ (⊢record hfs) =
    ⊢record (typing-rename-fields hρ hfs)
  typing-rename hρ (⊢proj hM has) =
    ⊢proj (typing-rename hρ hM) has
  typing-rename hρ (⊢sub hM A<:B) =
    ⊢sub (typing-rename hρ hM) A<:B

  typing-rename-fields :
    {Γ Δ : Ctx} {ρ : Rename} {fs : List FieldTerm} {Fs : List FieldTy} ->
    (∀ {i B} -> Γ ∋ i ⦂ B -> Δ ∋ (ρ i) ⦂ B) ->
    Γ ⊢ᶠˢ fs ⦂ Fs ->
    Δ ⊢ᶠˢ renameFields ρ fs ⦂ Fs
  typing-rename-fields hρ ⊢[] = ⊢[]
  typing-rename-fields hρ (⊢∷ hM hfs) =
    ⊢∷ (typing-rename hρ hM) (typing-rename-fields hρ hfs)

mutual
  typing-subst :
    {Γ Δ : Ctx} {σ : Subst} {M : Term} {A : Ty} ->
    (∀ {i B} -> Γ ∋ i ⦂ B -> Δ ⊢ σ i ⦂ B) ->
    Γ ⊢ M ⦂ A ->
    Δ ⊢ subst σ M ⦂ A
  typing-subst hs (⊢` hV) = hs hV
  typing-subst {Γ} {Δ} {σ} hs (⊢ƛ {A = A} hN) =
    ⊢ƛ (typing-subst hsExt hN)
    where
      shift : ∀ {i B} -> Δ ∋ i ⦂ B -> (A ∷ Δ) ∋ suc i ⦂ B
      shift hV = S hV

      hsExt : ∀ {i C} -> (A ∷ Γ) ∋ i ⦂ C -> (A ∷ Δ) ⊢ exts σ i ⦂ C
      hsExt Z = ⊢` Z
      hsExt (S hV) = typing-rename {ρ = suc} shift (hs hV)
  typing-subst hs (⊢· hL hM) =
    ⊢· (typing-subst hs hL) (typing-subst hs hM)
  typing-subst hs ⊢zero = ⊢zero
  typing-subst hs (⊢suc hM) = ⊢suc (typing-subst hs hM)
  typing-subst {Γ} {Δ} {σ} hs (⊢case hL hM hN) =
    ⊢case (typing-subst hs hL) (typing-subst hs hM)
           (typing-subst hsExt hN)
    where
      shift : ∀ {i B} -> Δ ∋ i ⦂ B -> (nat ∷ Δ) ∋ suc i ⦂ B
      shift hV = S hV

      hsExt : ∀ {i C} -> (nat ∷ Γ) ∋ i ⦂ C -> (nat ∷ Δ) ⊢ exts σ i ⦂ C
      hsExt Z = ⊢` Z
      hsExt (S hV) = typing-rename {ρ = suc} shift (hs hV)
  typing-subst hs (⊢record hfs) =
    ⊢record (typing-subst-fields hs hfs)
  typing-subst hs (⊢proj hM has) =
    ⊢proj (typing-subst hs hM) has
  typing-subst hs (⊢sub hM A<:B) =
    ⊢sub (typing-subst hs hM) A<:B

  typing-subst-fields :
    {Γ Δ : Ctx} {σ : Subst} {fs : List FieldTerm} {Fs : List FieldTy} ->
    (∀ {i B} -> Γ ∋ i ⦂ B -> Δ ⊢ σ i ⦂ B) ->
    Γ ⊢ᶠˢ fs ⦂ Fs ->
    Δ ⊢ᶠˢ substFields σ fs ⦂ Fs
  typing-subst-fields hs ⊢[] = ⊢[]
  typing-subst-fields hs (⊢∷ hM hfs) =
    ⊢∷ (typing-subst hs hM) (typing-subst-fields hs hfs)

typing-single-subst :
  {Γ : Ctx} {A B : Ty} {N M : Term} ->
  (B ∷ Γ) ⊢ N ⦂ A ->
  Γ ⊢ M ⦂ B ->
  Γ ⊢ N [ M ] ⦂ A
typing-single-subst {Γ} {B = B} {M = M} hN hM =
  typing-subst hσ hN
  where
    hσ : ∀ {i C} -> (B ∷ Γ) ∋ i ⦂ C -> Γ ⊢ singleEnv M i ⦂ C
    hσ Z = hM
    hσ (S hV) = ⊢` hV

------------------------------------------------------------------------
-- Record lookup inversion
------------------------------------------------------------------------

field-present :
  {Γ : Ctx} {fs : List FieldTerm} {Fs : List FieldTy} {ℓ : Label} {A : Ty} ->
  Γ ⊢ᶠˢ fs ⦂ Fs ->
  HasTy Fs ℓ A ->
  Σ Term (λ M -> HasTerm fs ℓ M)
field-present ⊢[] ()
field-present (⊢∷ hM hfs) ty-here = _ , tm-here
field-present (⊢∷ hM hfs) (ty-there neq has)
  with field-present hfs has
field-present (⊢∷ hM hfs) (ty-there neq has) | M , ht =
  M , tm-there neq ht

field-typing :
  {Γ : Ctx} {fs : List FieldTerm} {Fs : List FieldTy}
  {ℓ : Label} {M : Term} {A : Ty} ->
  Γ ⊢ᶠˢ fs ⦂ Fs ->
  HasTerm fs ℓ M ->
  HasTy Fs ℓ A ->
  Γ ⊢ M ⦂ A
field-typing ⊢[] ()
field-typing (⊢∷ hM hfs) tm-here ty-here = hM
field-typing (⊢∷ hM hfs) tm-here (ty-there neq has) = ⊥-elim (neq refl)
field-typing (⊢∷ hM hfs) (tm-there neq ht) ty-here = ⊥-elim (neq refl)
field-typing (⊢∷ hM hfs) (tm-there neq₁ ht) (ty-there neq₂ has) =
  field-typing hfs ht has

record-field-present :
  {fs : List FieldTerm} {Fs : List FieldTy} {ℓ : Label} {A : Ty} ->
  [] ⊢ `record fs ⦂ `⟨ Fs ⟩ ->
  HasTy Fs ℓ A ->
  Σ Term (λ M -> HasTerm fs ℓ M)
record-field-present (⊢record hfs) has = field-present hfs has
record-field-present (⊢sub hM S-refl) has = record-field-present hM has
record-field-present (⊢sub hM (S-record Fs<:Gs)) has
  with fieldsSub-lookup Fs<:Gs has
record-field-present (⊢sub hM (S-record Fs<:Gs)) has | A , src , A<:B =
  record-field-present hM src

record-field-typing :
  {fs : List FieldTerm} {Fs : List FieldTy}
  {ℓ : Label} {M : Term} {A : Ty} ->
  [] ⊢ `record fs ⦂ `⟨ Fs ⟩ ->
  HasTerm fs ℓ M ->
  HasTy Fs ℓ A ->
  [] ⊢ M ⦂ A
record-field-typing (⊢record hfs) ht has = field-typing hfs ht has
record-field-typing (⊢sub hM S-refl) ht has = record-field-typing hM ht has
record-field-typing (⊢sub hM (S-record Fs<:Gs)) ht has
  with fieldsSub-lookup Fs<:Gs has
record-field-typing (⊢sub hM (S-record Fs<:Gs)) ht has | A , src , A<:B =
  ⊢sub (record-field-typing hM ht src) A<:B

------------------------------------------------------------------------
-- Canonical forms
------------------------------------------------------------------------

lam-inv :
  {Γ : Ctx} {A : Ty} {N : Term} {B C : Ty} ->
  Γ ⊢ ƛ A ⇒ N ⦂ (B ⇒ C) ->
  Σ Ty (λ D -> (B <: A) × ((A ∷ Γ) ⊢ N ⦂ D) × (D <: C))
lam-inv (⊢ƛ hN) = _ , S-refl , hN , S-refl
lam-inv (⊢sub hN S-refl) = lam-inv hN
lam-inv (⊢sub hN (S-arrow B<:A C<:D)) with lam-inv hN
lam-inv (⊢sub hN (S-arrow B<:A C<:D)) | E , D<:A , N⊢ , E<:C =
  E , <:-trans B<:A D<:A , N⊢ , <:-trans E<:C C<:D

canonical-fun :
  {V : Term} {A B : Ty} ->
  [] ⊢ V ⦂ (A ⇒ B) ->
  Value V ->
  Σ Ty (λ C -> Σ Term (λ N -> V ≡ ƛ C ⇒ N))
canonical-fun (⊢ƛ hN) (ƛ A ⇒ N) = A , N , refl
canonical-fun (⊢sub hV S-refl) vV = canonical-fun hV vV
canonical-fun (⊢sub hV (S-arrow A<:B C<:D)) vV = canonical-fun hV vV

canonical-nat :
  {V : Term} ->
  [] ⊢ V ⦂ nat ->
  Value V ->
  (V ≡ `zero) ⊎ Σ Term (λ W -> Value W × (V ≡ `suc W))
canonical-nat ⊢zero `zero = inj₁ refl
canonical-nat (⊢suc hV) (`suc vV) = inj₂ (_ , vV , refl)
canonical-nat (⊢sub hV S-refl) vV = canonical-nat hV vV

canonical-record :
  {V : Term} {Fs : List FieldTy} ->
  [] ⊢ V ⦂ `⟨ Fs ⟩ ->
  Value V ->
  Σ (List FieldTerm) (λ fs -> V ≡ `record fs)
canonical-record (⊢record hfs) (`record fs) = fs , refl
canonical-record (⊢sub hV S-refl) vV = canonical-record hV vV
canonical-record (⊢sub hV (S-record Fs<:Gs)) vV = canonical-record hV vV

------------------------------------------------------------------------
-- Preservation
------------------------------------------------------------------------

preservation :
  {M N : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  M —→ N ->
  [] ⊢ N ⦂ A
preservation (⊢sub hM A<:B) M→N = ⊢sub (preservation hM M→N) A<:B
preservation (⊢· hL hM) (ξ-·₁ L→L′) =
  ⊢· (preservation hL L→L′) hM
preservation (⊢· hL hM) (ξ-·₂ (_ , M→M′)) =
  ⊢· hL (preservation hM M→M′)
preservation (⊢· hL hM) (β-ƛ vW) with lam-inv hL
preservation (⊢· hL hM) (β-ƛ vW) | D , B<:A , N⊢ , D<:C =
  ⊢sub (typing-single-subst N⊢ (⊢sub hM B<:A)) D<:C
preservation (⊢suc hM) (ξ-suc M→M′) =
  ⊢suc (preservation hM M→M′)
preservation (⊢case hL hM hN) (ξ-case L→L′) =
  ⊢case (preservation hL L→L′) hM hN
preservation (⊢case hL hM hN) β-zero = hM
preservation (⊢case (⊢suc hV) hM hN) (β-suc vV) =
  typing-single-subst hN hV
preservation (⊢case (⊢sub hL S-refl) hM hN) (β-suc vV) =
  preservation (⊢case hL hM hN) (β-suc vV)
preservation (⊢proj hM has) (ξ-proj M→M′) =
  ⊢proj (preservation hM M→M′) has
preservation (⊢proj hM has) (β-proj ht) =
  record-field-typing hM ht has

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

progress :
  {M : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  (∃[ N ] (M —→ N)) ⊎ Value M
progress (⊢` ())
progress (⊢ƛ hN) = inj₂ (ƛ _ ⇒ _)
progress (⊢· hL hM) with progress hL
progress (⊢· hL hM) | inj₁ (L′ , L→L′) = inj₁ (_ , ξ-·₁ L→L′)
progress (⊢· hL hM) | inj₂ vL with progress hM
progress (⊢· hL hM) | inj₂ vL | inj₁ (M′ , M→M′) =
  inj₁ (_ , ξ-·₂ (vL , M→M′))
progress (⊢· hL hM) | inj₂ vL | inj₂ vM with canonical-fun hL vL
progress (⊢· hL hM) | inj₂ vL | inj₂ vM | C , N , refl =
  inj₁ (_ , β-ƛ vM)
progress ⊢zero = inj₂ `zero
progress (⊢suc hM) with progress hM
progress (⊢suc hM) | inj₁ (M′ , M→M′) = inj₁ (_ , ξ-suc M→M′)
progress (⊢suc hM) | inj₂ vM = inj₂ (`suc vM)
progress (⊢case hL hM hN) with progress hL
progress (⊢case hL hM hN) | inj₁ (L′ , L→L′) =
  inj₁ (_ , ξ-case L→L′)
progress (⊢case hL hM hN) | inj₂ vL with canonical-nat hL vL
progress (⊢case hL hM hN) | inj₂ vL | inj₁ refl =
  inj₁ (_ , β-zero)
progress (⊢case hL hM hN) | inj₂ vL | inj₂ (V , vV , refl) =
  inj₁ (_ , β-suc vV)
progress (⊢record hfs) = inj₂ (`record _)
progress (⊢proj hM has) with progress hM
progress (⊢proj hM has) | inj₁ (M′ , M→M′) =
  inj₁ (_ , ξ-proj M→M′)
progress (⊢proj hM has) | inj₂ vM with canonical-record hM vM
progress (⊢proj hM has) | inj₂ vM | fs , refl
  with record-field-present hM has
progress (⊢proj hM has) | inj₂ vM | fs , refl | N , ht =
  inj₁ (N , β-proj ht)
progress (⊢sub hM A<:B) = progress hM

------------------------------------------------------------------------
-- Type safety
------------------------------------------------------------------------

type-safety-↠ :
  {M N : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  M —↠ N ->
  [] ⊢ N ⦂ A
type-safety-↠ M⊢ (_ ∎) = M⊢
type-safety-↠ M⊢ (_ —→⟨ M→L ⟩ L↠N) =
  type-safety-↠ (preservation M⊢ M→L) L↠N

type-safety :
  {M N : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  M —↠ N ->
  (∃[ N′ ] (N —→ N′)) ⊎ Value N
type-safety M⊢ M↠N = progress (type-safety-↠ M⊢ M↠N)
