module proof.TypingSubst where

-- File Charter:
--   * Structural properties of the PolyCν typing judgment
--     Σ ∣ Δ ∣ Γ ⊢ M ⦂ A:
--       - store weakening (⊢-weaken-store, ⊢-extend-store);
--       - term renaming and term substitution (⊢-rename, ⊢-subst, ⊢-[]);
--       - substitution of names for type variables (⊢-substᵀ), with the
--         corollaries ⊢-⇑ᵀ (weakening by a type binder) and
--         ⊢-inst-body / ⊢-inst-cont (the two substitutions of β-inst).
--   * Type substitution needs the store to be closed (StoreWf): store
--     types are read under type binders without shifting.
--   * Consumed by proof/Preservation.agda.

open import Data.List using (List; []; _∷_; map; length; _++_)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
  renaming (subst to substEq)

open import Types
open import Terms
open import Typing
open import StoreWf
open import proof.TypeSubst

------------------------------------------------------------------------
-- Rewriting the indices of a typing judgment
------------------------------------------------------------------------

cong-⊢ : ∀ {Σ Δ Γ Γ′ M M′ A A′}
  → Γ ≡ Γ′ → M ≡ M′ → A ≡ A′
  → Σ ∣ Δ ∣ Γ ⊢ M ⦂ A
  → Σ ∣ Δ ∣ Γ′ ⊢ M′ ⦂ A′
cong-⊢ refl refl refl ⊢M = ⊢M

------------------------------------------------------------------------
-- Stores
------------------------------------------------------------------------

infix 4 _⊆ˢ_

_⊆ˢ_ : Store → Store → Set
Σ ⊆ˢ Σ′ = ∀ {s A} → Σ ∋ˢ s ⦂ A → Σ′ ∋ˢ s ⦂ A

storeWf-lookup : ∀ {Σ s A} → StoreWf Σ → Σ ∋ˢ s ⦂ A → WfTy 0 A
storeWf-lookup (wfˢ∷ wfA wfΣ) Zˢ = wfA
storeWf-lookup (wfˢ∷ wfA wfΣ) (Sˢ h) = storeWf-lookup wfΣ h

storeWf-snoc : ∀ {Σ B ℓ}
  → StoreWf Σ → WfTy 0 B → StoreWf (Σ ++ ((B , ℓ) ∷ []))
storeWf-snoc wfˢ[] wfB = wfˢ∷ wfB wfˢ[]
storeWf-snoc (wfˢ∷ wfA wfΣ) wfB = wfˢ∷ wfA (storeWf-snoc wfΣ wfB)

NameTy-weaken : ∀ {Σ Σ′ Δ α A}
  → Σ ⊆ˢ Σ′ → NameTy Σ Δ α A → NameTy Σ′ Δ α A
NameTy-weaken Σ⊆ (nt-var h) = nt-var h
NameTy-weaken Σ⊆ (nt-seal h) = nt-seal (Σ⊆ h)

NameTy-unique : ∀ {Σ Δ α A B}
  → (∀ {i A B} → Δ ∋ i ≅ A → Δ ∋ i ≅ B → A ≡ B)
  → NameTy Σ Δ α A → NameTy Σ Δ α B → A ≡ B
NameTy-unique uniq (nt-var h) (nt-var h′) = uniq h h′
NameTy-unique uniq (nt-seal h) (nt-seal h′) = ∋ˢ-unique h h′

⊢-weaken-store : ∀ {Σ Σ′ Δ Γ M A}
  → Σ ⊆ˢ Σ′
  → Σ ∣ Δ ∣ Γ ⊢ M ⦂ A
  → Σ′ ∣ Δ ∣ Γ ⊢ M ⦂ A
⊢-weaken-store Σ⊆ (⊢` h) = ⊢` h
⊢-weaken-store Σ⊆ ⊢℧ = ⊢℧
⊢-weaken-store Σ⊆ ⊢true = ⊢true
⊢-weaken-store Σ⊆ ⊢false = ⊢false
⊢-weaken-store Σ⊆ (⊢if ⊢L ⊢M ⊢N) =
  ⊢if (⊢-weaken-store Σ⊆ ⊢L) (⊢-weaken-store Σ⊆ ⊢M) (⊢-weaken-store Σ⊆ ⊢N)
⊢-weaken-store Σ⊆ (⊢ƛ ⊢M) = ⊢ƛ (⊢-weaken-store Σ⊆ ⊢M)
⊢-weaken-store Σ⊆ (⊢· ⊢L ⊢M) =
  ⊢· (⊢-weaken-store Σ⊆ ⊢L) (⊢-weaken-store Σ⊆ ⊢M)
⊢-weaken-store Σ⊆ (⊢letv ⊢M ⊢N) =
  ⊢letv (⊢-weaken-store Σ⊆ ⊢M) (⊢-weaken-store Σ⊆ ⊢N)
⊢-weaken-store Σ⊆ (⊢seal nt ⊢M) =
  ⊢seal (NameTy-weaken Σ⊆ nt) (⊢-weaken-store Σ⊆ ⊢M)
⊢-weaken-store Σ⊆ (⊢unseal nt ⊢M) =
  ⊢unseal (NameTy-weaken Σ⊆ nt) (⊢-weaken-store Σ⊆ ⊢M)
⊢-weaken-store Σ⊆ (⊢is wfG ⊢M) = ⊢is wfG (⊢-weaken-store Σ⊆ ⊢M)
⊢-weaken-store Σ⊆ (⊢inj wfG ⊢M) = ⊢inj wfG (⊢-weaken-store Σ⊆ ⊢M)
⊢-weaken-store Σ⊆ (⊢up p⊢ ⊢M) = ⊢up p⊢ (⊢-weaken-store Σ⊆ ⊢M)
⊢-weaken-store Σ⊆ (⊢down p⊢ ⊢M) = ⊢down p⊢ (⊢-weaken-store Σ⊆ ⊢M)
⊢-weaken-store Σ⊆ (⊢Λν ⊢M) = ⊢Λν (⊢-weaken-store Σ⊆ ⊢M)
⊢-weaken-store Σ⊆ (⊢inst ⊢M wfB ⊢N) =
  ⊢inst (⊢-weaken-store Σ⊆ ⊢M) wfB (⊢-weaken-store Σ⊆ ⊢N)

-- typing is preserved by extending the store
⊢-extend-store : ∀ {Σ Δ Γ M A} Θ
  → Σ ∣ Δ ∣ Γ ⊢ M ⦂ A
  → (Σ ++ Θ) ∣ Δ ∣ Γ ⊢ M ⦂ A
⊢-extend-store Θ = ⊢-weaken-store (∋ˢ-++ Θ)

------------------------------------------------------------------------
-- Context lookups under map
------------------------------------------------------------------------

map-∋ : ∀ {Γ x A} (f : Ty → Ty) → Γ ∋ x ⦂ A → map f Γ ∋ x ⦂ f A
map-∋ f Z = Z
map-∋ f (S h) = S (map-∋ f h)

unmap-∋ : ∀ {Γ x B} (f : Ty → Ty)
  → map f Γ ∋ x ⦂ B
  → ∃[ A ] (Γ ∋ x ⦂ A × B ≡ f A)
unmap-∋ {Γ = A ∷ Γ} f Z = A , Z , refl
unmap-∋ {Γ = A ∷ Γ} f (S h) with unmap-∋ f h
unmap-∋ {Γ = A ∷ Γ} f (S h) | A′ , h′ , eq = A′ , S h′ , eq

------------------------------------------------------------------------
-- Term renaming
------------------------------------------------------------------------

ext-ren : ∀ {Γ Γ′ B} (ρ : Rename)
  → (∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A)
  → ∀ {x A} → (B ∷ Γ) ∋ x ⦂ A → (B ∷ Γ′) ∋ ext ρ x ⦂ A
ext-ren ρ ρ⊢ Z = Z
ext-ren ρ ρ⊢ (S h) = S (ρ⊢ h)

⤊-ren : ∀ {Γ Γ′} (ρ : Rename)
  → (∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A)
  → ∀ {x A} → ⤊ Γ ∋ x ⦂ A → ⤊ Γ′ ∋ ρ x ⦂ A
⤊-ren ρ ρ⊢ h with unmap-∋ ⇑ᵗ h
⤊-ren ρ ρ⊢ h | A , h′ , refl = map-∋ ⇑ᵗ (ρ⊢ h′)

⊢-rename : ∀ {Σ Δ Γ Γ′ M A} (ρ : Rename)
  → (∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A)
  → Σ ∣ Δ ∣ Γ ⊢ M ⦂ A
  → Σ ∣ Δ ∣ Γ′ ⊢ rename ρ M ⦂ A
⊢-rename ρ ρ⊢ (⊢` h) = ⊢` (ρ⊢ h)
⊢-rename ρ ρ⊢ ⊢℧ = ⊢℧
⊢-rename ρ ρ⊢ ⊢true = ⊢true
⊢-rename ρ ρ⊢ ⊢false = ⊢false
⊢-rename ρ ρ⊢ (⊢if ⊢L ⊢M ⊢N) =
  ⊢if (⊢-rename ρ ρ⊢ ⊢L) (⊢-rename ρ ρ⊢ ⊢M) (⊢-rename ρ ρ⊢ ⊢N)
⊢-rename ρ ρ⊢ (⊢ƛ ⊢M) = ⊢ƛ (⊢-rename (ext ρ) (ext-ren ρ ρ⊢) ⊢M)
⊢-rename ρ ρ⊢ (⊢· ⊢L ⊢M) = ⊢· (⊢-rename ρ ρ⊢ ⊢L) (⊢-rename ρ ρ⊢ ⊢M)
⊢-rename ρ ρ⊢ (⊢letv ⊢M ⊢N) =
  ⊢letv (⊢-rename ρ ρ⊢ ⊢M) (⊢-rename (ext ρ) (ext-ren ρ ρ⊢) ⊢N)
⊢-rename ρ ρ⊢ (⊢seal nt ⊢M) = ⊢seal nt (⊢-rename ρ ρ⊢ ⊢M)
⊢-rename ρ ρ⊢ (⊢unseal nt ⊢M) = ⊢unseal nt (⊢-rename ρ ρ⊢ ⊢M)
⊢-rename ρ ρ⊢ (⊢is wfG ⊢M) = ⊢is wfG (⊢-rename ρ ρ⊢ ⊢M)
⊢-rename ρ ρ⊢ (⊢inj wfG ⊢M) = ⊢inj wfG (⊢-rename ρ ρ⊢ ⊢M)
⊢-rename ρ ρ⊢ (⊢up p⊢ ⊢M) = ⊢up p⊢ (⊢-rename ρ ρ⊢ ⊢M)
⊢-rename ρ ρ⊢ (⊢down p⊢ ⊢M) = ⊢down p⊢ (⊢-rename ρ ρ⊢ ⊢M)
⊢-rename ρ ρ⊢ (⊢Λν {cs = cs} {M = M} ⊢M) =
  ⊢Λν (cong-⊢ refl (stack-rename ρ cs M) refl
        (⊢-rename ρ (⤊-ren ρ ρ⊢) ⊢M))
⊢-rename ρ ρ⊢ (⊢inst ⊢M wfB ⊢N) =
  ⊢inst (⊢-rename ρ ρ⊢ ⊢M) wfB
        (⊢-rename (ext ρ) (ext-ren ρ (⤊-ren ρ ρ⊢)) ⊢N)

------------------------------------------------------------------------
-- Substitution of names for type variables
------------------------------------------------------------------------

substI : NSubst → TyInfo → TyInfo
substI σ abs = abs
substI σ (known A) = known (substᵗ σ A)

-- σ maps the type variables of Δ to names of Δ′, respecting known
-- types, and Σ′ contains Σ
record TySubstOK (Σ Σ′ : Store) (Δ Δ′ : TyEnv) (σ : NSubst) : Set where
  field
    ok-wf   : ∀ {i} → i < tsize Δ → WfName (tsize Δ′) (σ i)
    ok-var  : ∀ {i A} → Δ ∋ i ≅ A → NameTy Σ′ Δ′ (σ i) (substᵗ σ A)
    ok-seal : Σ ⊆ˢ Σ′

open TySubstOK

NameTy-⇑ : ∀ {Σ Δ I α A}
  → StoreWf Σ
  → NameTy Σ Δ α A
  → NameTy Σ (I ∷ Δ) (⇑ₙ α) (⇑ᵗ A)
NameTy-⇑ wfΣ (nt-var h) = nt-var (S≅ h)
NameTy-⇑ wfΣ (nt-seal h) =
  nt-seal (substEq (λ T → _ ∋ˢ _ ⦂ T)
                   (sym (closed-subst (storeWf-lookup wfΣ h))) h)

TySubstOK-ext : ∀ {Σ Σ′ Δ Δ′ σ} I
  → StoreWf Σ′
  → TySubstOK Σ Σ′ Δ Δ′ σ
  → TySubstOK Σ Σ′ (I ∷ Δ) (substI σ I ∷ Δ′) (extₙ σ)
TySubstOK-ext {σ = σ} I wfΣ′ ok = record
  { ok-wf = WfName-ext (ok-wf ok)
  ; ok-var = var
  ; ok-seal = ok-seal ok
  }
  where
  var : ∀ {i A} → (I ∷ _) ∋ i ≅ A
    → NameTy _ (substI σ I ∷ _) (extₙ σ i) (substᵗ (extₙ σ) A)
  var (Z≅ {A = A}) =
    substEq (NameTy _ _ (tvar zero)) (sym (ext-⇑ᵗ σ A)) (nt-var Z≅)
  var (S≅ {A = A} h) =
    substEq (NameTy _ _ _) (sym (ext-⇑ᵗ σ A))
            (NameTy-⇑ wfΣ′ (ok-var ok h))

NameTy-subst : ∀ {Σ Σ′ Δ Δ′ σ α A}
  → StoreWf Σ
  → TySubstOK Σ Σ′ Δ Δ′ σ
  → NameTy Σ Δ α A
  → NameTy Σ′ Δ′ (substₙ σ α) (substᵗ σ A)
NameTy-subst wfΣ ok (nt-var h) = ok-var ok h
NameTy-subst wfΣ ok (nt-seal h) =
  nt-seal (substEq (λ T → _ ∋ˢ _ ⦂ T)
                   (sym (closed-subst (storeWf-lookup wfΣ h)))
                   (ok-seal ok h))

⊢-substᵀ : ∀ {Σ Σ′ Δ Δ′ σ Γ M A}
  → StoreWf Σ
  → StoreWf Σ′
  → TySubstOK Σ Σ′ Δ Δ′ σ
  → Σ ∣ Δ ∣ Γ ⊢ M ⦂ A
  → Σ′ ∣ Δ′ ∣ map (substᵗ σ) Γ ⊢ substᵀ σ M ⦂ substᵗ σ A
⊢-substᵀ {σ = σ} wfΣ wfΣ′ ok (⊢` h) = ⊢` (map-∋ (substᵗ σ) h)
⊢-substᵀ wfΣ wfΣ′ ok ⊢℧ = ⊢℧
⊢-substᵀ wfΣ wfΣ′ ok ⊢true = ⊢true
⊢-substᵀ wfΣ wfΣ′ ok ⊢false = ⊢false
⊢-substᵀ wfΣ wfΣ′ ok (⊢if ⊢L ⊢M ⊢N) =
  ⊢if (⊢-substᵀ wfΣ wfΣ′ ok ⊢L) (⊢-substᵀ wfΣ wfΣ′ ok ⊢M)
      (⊢-substᵀ wfΣ wfΣ′ ok ⊢N)
⊢-substᵀ wfΣ wfΣ′ ok (⊢ƛ ⊢M) = ⊢ƛ (⊢-substᵀ wfΣ wfΣ′ ok ⊢M)
⊢-substᵀ wfΣ wfΣ′ ok (⊢· ⊢L ⊢M) =
  ⊢· (⊢-substᵀ wfΣ wfΣ′ ok ⊢L) (⊢-substᵀ wfΣ wfΣ′ ok ⊢M)
⊢-substᵀ wfΣ wfΣ′ ok (⊢letv ⊢M ⊢N) =
  ⊢letv (⊢-substᵀ wfΣ wfΣ′ ok ⊢M) (⊢-substᵀ wfΣ wfΣ′ ok ⊢N)
⊢-substᵀ wfΣ wfΣ′ ok (⊢seal nt ⊢M) =
  ⊢seal (NameTy-subst wfΣ ok nt) (⊢-substᵀ wfΣ wfΣ′ ok ⊢M)
⊢-substᵀ wfΣ wfΣ′ ok (⊢unseal nt ⊢M) =
  ⊢unseal (NameTy-subst wfΣ ok nt) (⊢-substᵀ wfΣ wfΣ′ ok ⊢M)
⊢-substᵀ wfΣ wfΣ′ ok (⊢is wfG ⊢M) =
  ⊢is (WfGround-subst (ok-wf ok) wfG) (⊢-substᵀ wfΣ wfΣ′ ok ⊢M)
⊢-substᵀ {σ = σ} wfΣ wfΣ′ ok (⊢inj {G = G} wfG ⊢M) =
  ⊢inj (WfGround-subst (ok-wf ok) wfG)
       (cong-⊢ refl refl (groundTy-subst σ G) (⊢-substᵀ wfΣ wfΣ′ ok ⊢M))
⊢-substᵀ wfΣ wfΣ′ ok (⊢up p⊢ ⊢M) =
  ⊢up (⊑-subst (ok-wf ok) p⊢) (⊢-substᵀ wfΣ wfΣ′ ok ⊢M)
⊢-substᵀ wfΣ wfΣ′ ok (⊢down p⊢ ⊢M) =
  ⊢down (⊑-subst (ok-wf ok) p⊢) (⊢-substᵀ wfΣ wfΣ′ ok ⊢M)
⊢-substᵀ {σ = σ} {Γ = Γ} wfΣ wfΣ′ ok (⊢Λν {cs = cs} {M = M} ⊢M) =
  ⊢Λν (cong-⊢ (map-ext-⤊ σ Γ) (stack-substᵀ (extₙ σ) cs M) refl
        (⊢-substᵀ wfΣ wfΣ′ (TySubstOK-ext abs wfΣ′ ok) ⊢M))
⊢-substᵀ {σ = σ} {Γ = Γ} wfΣ wfΣ′ ok (⊢inst {A = A} {C = C} ⊢M wfB ⊢N) =
  ⊢inst (⊢-substᵀ wfΣ wfΣ′ ok ⊢M) (WfTy-subst (ok-wf ok) wfB)
        (cong-⊢ (cong (substᵗ (extₙ σ) A ∷_) (map-ext-⤊ σ Γ)) refl
                (ext-⇑ᵗ σ C)
                (⊢-substᵀ wfΣ wfΣ′ (TySubstOK-ext (known _) wfΣ′ ok) ⊢N))

-- weakening by a type binder
⊢-⇑ᵀ : ∀ {Σ Δ Γ M A} I
  → StoreWf Σ
  → Σ ∣ Δ ∣ Γ ⊢ M ⦂ A
  → Σ ∣ (I ∷ Δ) ∣ ⤊ Γ ⊢ ⇑ᵀ M ⦂ ⇑ᵗ A
⊢-⇑ᵀ I wfΣ = ⊢-substᵀ wfΣ wfΣ ok
  where
  ok : TySubstOK _ _ _ (I ∷ _) ↑ₙ
  ok = record
    { ok-wf = s≤s
    ; ok-var = λ h → nt-var (S≅ h)
    ; ok-seal = λ h → h
    }

-- the body of a proxy, instantiated with the new seal
⊢-inst-body : ∀ {Σ B ℓ M A}
  → StoreWf Σ
  → WfTy 0 B
  → Σ ∣ (abs ∷ []) ∣ [] ⊢ M ⦂ A
  → (Σ ++ ((B , ℓ) ∷ [])) ∣ [] ∣ [] ⊢ M [ tseal (length Σ) ]ᵀ
      ⦂ A [ tseal (length Σ) ]ᵗ
⊢-inst-body {Σ} {B} {ℓ} wfΣ wfB =
  ⊢-substᵀ wfΣ (storeWf-snoc wfΣ wfB) ok
  where
  wf : ∀ {i} → i < 1 → WfName 0 (singleₙ (tseal (length Σ)) i)
  wf {zero} i<1 = tt
  wf {suc i} (s≤s ())

  var : ∀ {i A} → (abs ∷ []) ∋ i ≅ A
    → NameTy (Σ ++ ((B , ℓ) ∷ [])) [] (singleₙ (tseal (length Σ)) i)
        (A [ tseal (length Σ) ]ᵗ)
  var (S≅ ())

  ok : TySubstOK Σ (Σ ++ ((B , ℓ) ∷ [])) (abs ∷ []) []
         (singleₙ (tseal (length Σ)))
  ok = record { ok-wf = wf ; ok-var = var ; ok-seal = ∋ˢ-++ ((B , ℓ) ∷ []) }

-- the continuation of an instantiation, with X ≅ B replaced by the new
-- seal
⊢-inst-cont : ∀ {Σ B ℓ N A C}
  → StoreWf Σ
  → WfTy 0 B
  → Σ ∣ (known B ∷ []) ∣ (A ∷ []) ⊢ N ⦂ ⇑ᵗ C
  → (Σ ++ ((B , ℓ) ∷ [])) ∣ [] ∣ (A [ tseal (length Σ) ]ᵗ ∷ [])
      ⊢ N [ tseal (length Σ) ]ᵀ ⦂ C
⊢-inst-cont {Σ} {B} {ℓ} {C = C} wfΣ wfB ⊢N =
  cong-⊢ refl refl (⇑ᵗ-[]ᵗ C (tseal (length Σ)))
    (⊢-substᵀ wfΣ (storeWf-snoc wfΣ wfB) ok ⊢N)
  where
  wf : ∀ {i} → i < 1 → WfName 0 (singleₙ (tseal (length Σ)) i)
  wf {zero} i<1 = tt
  wf {suc i} (s≤s ())

  var : ∀ {i A} → (known B ∷ []) ∋ i ≅ A
    → NameTy (Σ ++ ((B , ℓ) ∷ [])) [] (singleₙ (tseal (length Σ)) i)
        (A [ tseal (length Σ) ]ᵗ)
  var Z≅ =
    nt-seal (substEq (λ T → (Σ ++ ((B , ℓ) ∷ [])) ∋ˢ length Σ ⦂ T)
                     (sym (⇑ᵗ-[]ᵗ B (tseal (length Σ)))) (∋ˢ-length Σ))
  var (S≅ ())

  ok : TySubstOK Σ (Σ ++ ((B , ℓ) ∷ [])) (known B ∷ []) []
         (singleₙ (tseal (length Σ)))
  ok = record { ok-wf = wf ; ok-var = var ; ok-seal = ∋ˢ-++ ((B , ℓ) ∷ []) }

------------------------------------------------------------------------
-- Term substitution
------------------------------------------------------------------------

exts-⊢ : ∀ {Σ Δ Γ Γ′ σ B}
  → (∀ {x A} → Γ ∋ x ⦂ A → Σ ∣ Δ ∣ Γ′ ⊢ σ x ⦂ A)
  → ∀ {x A} → (B ∷ Γ) ∋ x ⦂ A → Σ ∣ Δ ∣ (B ∷ Γ′) ⊢ exts σ x ⦂ A
exts-⊢ σ⊢ Z = ⊢` Z
exts-⊢ σ⊢ (S h) = ⊢-rename suc S (σ⊢ h)

⇑ˢ-⊢ : ∀ {Σ Δ Γ Γ′ σ} I
  → StoreWf Σ
  → (∀ {x A} → Γ ∋ x ⦂ A → Σ ∣ Δ ∣ Γ′ ⊢ σ x ⦂ A)
  → ∀ {x A} → ⤊ Γ ∋ x ⦂ A → Σ ∣ (I ∷ Δ) ∣ ⤊ Γ′ ⊢ ⇑ˢ σ x ⦂ A
⇑ˢ-⊢ I wfΣ σ⊢ h with unmap-∋ ⇑ᵗ h
⇑ˢ-⊢ I wfΣ σ⊢ h | A , h′ , refl = ⊢-⇑ᵀ I wfΣ (σ⊢ h′)

⊢-subst : ∀ {Σ Δ Γ Γ′ σ M A}
  → StoreWf Σ
  → (∀ {x A} → Γ ∋ x ⦂ A → Σ ∣ Δ ∣ Γ′ ⊢ σ x ⦂ A)
  → Σ ∣ Δ ∣ Γ ⊢ M ⦂ A
  → Σ ∣ Δ ∣ Γ′ ⊢ subst σ M ⦂ A
⊢-subst wfΣ σ⊢ (⊢` h) = σ⊢ h
⊢-subst wfΣ σ⊢ ⊢℧ = ⊢℧
⊢-subst wfΣ σ⊢ ⊢true = ⊢true
⊢-subst wfΣ σ⊢ ⊢false = ⊢false
⊢-subst wfΣ σ⊢ (⊢if ⊢L ⊢M ⊢N) =
  ⊢if (⊢-subst wfΣ σ⊢ ⊢L) (⊢-subst wfΣ σ⊢ ⊢M) (⊢-subst wfΣ σ⊢ ⊢N)
⊢-subst wfΣ σ⊢ (⊢ƛ ⊢M) = ⊢ƛ (⊢-subst wfΣ (exts-⊢ σ⊢) ⊢M)
⊢-subst wfΣ σ⊢ (⊢· ⊢L ⊢M) = ⊢· (⊢-subst wfΣ σ⊢ ⊢L) (⊢-subst wfΣ σ⊢ ⊢M)
⊢-subst wfΣ σ⊢ (⊢letv ⊢M ⊢N) =
  ⊢letv (⊢-subst wfΣ σ⊢ ⊢M) (⊢-subst wfΣ (exts-⊢ σ⊢) ⊢N)
⊢-subst wfΣ σ⊢ (⊢seal nt ⊢M) = ⊢seal nt (⊢-subst wfΣ σ⊢ ⊢M)
⊢-subst wfΣ σ⊢ (⊢unseal nt ⊢M) = ⊢unseal nt (⊢-subst wfΣ σ⊢ ⊢M)
⊢-subst wfΣ σ⊢ (⊢is wfG ⊢M) = ⊢is wfG (⊢-subst wfΣ σ⊢ ⊢M)
⊢-subst wfΣ σ⊢ (⊢inj wfG ⊢M) = ⊢inj wfG (⊢-subst wfΣ σ⊢ ⊢M)
⊢-subst wfΣ σ⊢ (⊢up p⊢ ⊢M) = ⊢up p⊢ (⊢-subst wfΣ σ⊢ ⊢M)
⊢-subst wfΣ σ⊢ (⊢down p⊢ ⊢M) = ⊢down p⊢ (⊢-subst wfΣ σ⊢ ⊢M)
⊢-subst {σ = σ} wfΣ σ⊢ (⊢Λν {cs = cs} {M = M} ⊢M) =
  ⊢Λν (cong-⊢ refl (stack-subst (⇑ˢ σ) cs M) refl
        (⊢-subst wfΣ (⇑ˢ-⊢ abs wfΣ σ⊢) ⊢M))
⊢-subst wfΣ σ⊢ (⊢inst ⊢M wfB ⊢N) =
  ⊢inst (⊢-subst wfΣ σ⊢ ⊢M) wfB
        (⊢-subst wfΣ (exts-⊢ (⇑ˢ-⊢ (known _) wfΣ σ⊢)) ⊢N)

-- single substitution
⊢-[] : ∀ {Σ Δ Γ N V A B}
  → StoreWf Σ
  → Σ ∣ Δ ∣ (A ∷ Γ) ⊢ N ⦂ B
  → Σ ∣ Δ ∣ Γ ⊢ V ⦂ A
  → Σ ∣ Δ ∣ Γ ⊢ N [ V ] ⦂ B
⊢-[] wfΣ ⊢N ⊢V = ⊢-subst wfΣ σ⊢ ⊢N
  where
  σ⊢ : ∀ {x A} → (_ ∷ _) ∋ x ⦂ A → _ ∣ _ ∣ _ ⊢ single _ x ⦂ A
  σ⊢ Z = ⊢V
  σ⊢ (S h) = ⊢` h
