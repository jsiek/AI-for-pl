module proof.TypeSafety where

-- File Charter:
--   * Private progress/preservation development and type-safety proof
--     for STLCRef.
--   * Tracks store typing invariants and one-step store-typing growth.
--   * Exported through public wrappers in `MetaTheory.agda`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.Nat renaming (Nat to ℕ; zero to zeroℕ; suc to sucℕ)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_++_; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (_×_; ∃; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans; _≢_)
  renaming (subst to substEq)

open import STLCRef

------------------------------------------------------------------------
-- Basic lookup and equality lemmas
------------------------------------------------------------------------

∋-unique :
  {Γ : Ctx} {x : Var} {A B : Ty} ->
  Γ ∋ x ⦂ A ->
  Γ ∋ x ⦂ B ->
  A ≡ B
∋-unique Z Z = refl
∋-unique (S hA) (S hB) = ∋-unique hA hB

just-injective :
  {A : Set} {x y : A} ->
  just x ≡ just y ->
  x ≡ y
just-injective refl = refl

nothing≢just :
  {A : Set} {x : A} ->
  nothing ≡ just x ->
  ⊥
nothing≢just ()

nat-eq-dec : (m n : ℕ) -> Dec (m ≡ n)
nat-eq-dec zeroℕ zeroℕ = yes refl
nat-eq-dec zeroℕ (sucℕ n) = no (λ ())
nat-eq-dec (sucℕ m) zeroℕ = no (λ ())
nat-eq-dec (sucℕ m) (sucℕ n) with nat-eq-dec m n
... | yes eq = yes (cong sucℕ eq)
... | no neq = no (λ { refl -> neq refl })

------------------------------------------------------------------------
-- Typing infrastructure (renaming, substitution, weakening)
------------------------------------------------------------------------

typing_rename :
  {Γ Δ : Ctx} {Σ : StoreTy} {ρ : Rename} {M : Term} {A : Ty} ->
  (∀ {i B} -> Γ ∋ i ⦂ B -> Δ ∋ (ρ i) ⦂ B) ->
  Γ ∣ Σ ⊢ M ⦂ A ->
  Δ ∣ Σ ⊢ (rename ρ M) ⦂ A
typing_rename hρ (⊢` hV) = ⊢` (hρ hV)
typing_rename {Γ} {Δ} {Σ} {ρ} hρ (⊢ƛ {A = A} hN) =
  ⊢ƛ (typing_rename hrExt hN)
  where
    hrExt :
      ∀ {i C} ->
      (A ∷ Γ) ∋ i ⦂ C ->
      (A ∷ Δ) ∋ (ext ρ i) ⦂ C
    hrExt STLCRef.Z = STLCRef.Z
    hrExt (STLCRef.S hV') = STLCRef.S (hρ hV')
typing_rename hρ (⊢· hL hM) =
  ⊢· (typing_rename hρ hL) (typing_rename hρ hM)
typing_rename hρ ⊢zero = ⊢zero
typing_rename hρ (⊢suc hM) = ⊢suc (typing_rename hρ hM)
typing_rename {Γ} {Δ} {Σ} {ρ} hρ (⊢case hL hM hN) =
  ⊢case
    (typing_rename hρ hL)
    (typing_rename hρ hM)
    (typing_rename hrExt hN)
  where
    hrExt :
      ∀ {i C} ->
      (nat ∷ Γ) ∋ i ⦂ C ->
      (nat ∷ Δ) ∋ (ext ρ i) ⦂ C
    hrExt STLCRef.Z = STLCRef.Z
    hrExt (STLCRef.S hV') = STLCRef.S (hρ hV')
typing_rename hρ ⊢unit = ⊢unit
typing_rename hρ (⊢ref hM) = ⊢ref (typing_rename hρ hM)
typing_rename hρ (⊢! hM) = ⊢! (typing_rename hρ hM)
typing_rename hρ (⊢:= hL hM) =
  ⊢:= (typing_rename hρ hL) (typing_rename hρ hM)
typing_rename hρ (⊢loc hL) = ⊢loc hL

typing_subst :
  {Γ Δ : Ctx} {Σ : StoreTy} {σ : Subst} {M : Term} {A : Ty} ->
  (∀ {i B} -> Γ ∋ i ⦂ B -> Δ ∣ Σ ⊢ (σ i) ⦂ B) ->
  Γ ∣ Σ ⊢ M ⦂ A ->
  Δ ∣ Σ ⊢ (subst σ M) ⦂ A
typing_subst hs (⊢` hV) = hs hV
typing_subst {Γ} {Δ} {Σ} {σ} hs (⊢ƛ {A = A} hN) =
  ⊢ƛ (typing_subst hsExt hN)
  where
    shift :
      ∀ {i B} ->
      Δ ∋ i ⦂ B ->
      (A ∷ Δ) ∋ sucℕ i ⦂ B
    shift hV = STLCRef.S hV

    hsExt :
      ∀ {i C} ->
      (A ∷ Γ) ∋ i ⦂ C ->
      (A ∷ Δ) ∣ Σ ⊢ (exts σ i) ⦂ C
    hsExt x = hsExtAux x
      where
        hsExtAux :
          ∀ {i C} ->
          (A ∷ Γ) ∋ i ⦂ C ->
          (A ∷ Δ) ∣ Σ ⊢ (exts σ i) ⦂ C
        hsExtAux STLCRef.Z = ⊢` STLCRef.Z
        hsExtAux (STLCRef.S hV') =
          typing_rename {ρ = sucℕ} shift (hs hV')
typing_subst hs (⊢· hL hM) =
  ⊢· (typing_subst hs hL) (typing_subst hs hM)
typing_subst hs ⊢zero = ⊢zero
typing_subst hs (⊢suc hM) = ⊢suc (typing_subst hs hM)
typing_subst {Γ} {Δ} {Σ} {σ} hs (⊢case hL hM hN) =
  ⊢case
    (typing_subst hs hL)
    (typing_subst hs hM)
    (typing_subst hsExt hN)
  where
    shift :
      ∀ {i B} ->
      Δ ∋ i ⦂ B ->
      (nat ∷ Δ) ∋ sucℕ i ⦂ B
    shift hV = STLCRef.S hV

    hsExt :
      ∀ {i C} ->
      (nat ∷ Γ) ∋ i ⦂ C ->
      (nat ∷ Δ) ∣ Σ ⊢ (exts σ i) ⦂ C
    hsExt x = hsExtAux x
      where
        hsExtAux :
          ∀ {i C} ->
          (nat ∷ Γ) ∋ i ⦂ C ->
          (nat ∷ Δ) ∣ Σ ⊢ (exts σ i) ⦂ C
        hsExtAux STLCRef.Z = ⊢` STLCRef.Z
        hsExtAux (STLCRef.S hV') =
          typing_rename {ρ = sucℕ} shift (hs hV')
typing_subst hs ⊢unit = ⊢unit
typing_subst hs (⊢ref hM) = ⊢ref (typing_subst hs hM)
typing_subst hs (⊢! hM) = ⊢! (typing_subst hs hM)
typing_subst hs (⊢:= hL hM) =
  ⊢:= (typing_subst hs hL) (typing_subst hs hM)
typing_subst hs (⊢loc hL) = ⊢loc hL

typing_single_subst :
  {Γ : Ctx} {Σ : StoreTy} {A B : Ty} {N M : Term} ->
  (B ∷ Γ) ∣ Σ ⊢ N ⦂ A ->
  Γ ∣ Σ ⊢ M ⦂ B ->
  Γ ∣ Σ ⊢ (N [ M ]) ⦂ A
typing_single_subst {Γ} {Σ} {A} {B} {N} {M} hN hM =
  typing_subst hσ hN
  where
    hσ :
      ∀ {i C} ->
      (B ∷ Γ) ∋ i ⦂ C ->
      Γ ∣ Σ ⊢ (singleEnv M i) ⦂ C
    hσ STLCRef.Z = hM
    hσ (STLCRef.S hVar') = ⊢` hVar'

lookup-weaken-++ :
  {Σ : StoreTy} {l : ℕ} {A : Ty} ->
  Σ ∋ l ⦂ A ->
  (Δ : StoreTy) ->
  (Σ ++ Δ) ∋ l ⦂ A
lookup-weaken-++ STLCRef.Z Δ = STLCRef.Z
lookup-weaken-++ (STLCRef.S h) Δ = STLCRef.S (lookup-weaken-++ h Δ)

typing-store-weaken :
  {Γ : Ctx} {Σ : StoreTy} {M : Term} {A : Ty} ->
  Γ ∣ Σ ⊢ M ⦂ A ->
  (Δ : StoreTy) ->
  Γ ∣ (Σ ++ Δ) ⊢ M ⦂ A
typing-store-weaken (⊢` h) Δ = ⊢` h
typing-store-weaken (⊢ƛ hN) Δ = ⊢ƛ (typing-store-weaken hN Δ)
typing-store-weaken (⊢· hL hM) Δ =
  ⊢· (typing-store-weaken hL Δ) (typing-store-weaken hM Δ)
typing-store-weaken ⊢zero Δ = ⊢zero
typing-store-weaken (⊢suc hM) Δ = ⊢suc (typing-store-weaken hM Δ)
typing-store-weaken (⊢case hL hM hN) Δ =
  ⊢case
    (typing-store-weaken hL Δ)
    (typing-store-weaken hM Δ)
    (typing-store-weaken hN Δ)
typing-store-weaken ⊢unit Δ = ⊢unit
typing-store-weaken (⊢ref hM) Δ = ⊢ref (typing-store-weaken hM Δ)
typing-store-weaken (⊢! hM) Δ = ⊢! (typing-store-weaken hM Δ)
typing-store-weaken (⊢:= hL hM) Δ =
  ⊢:= (typing-store-weaken hL Δ) (typing-store-weaken hM Δ)
typing-store-weaken (⊢loc hL) Δ = ⊢loc (lookup-weaken-++ hL Δ)

StoreExt : StoreTy -> StoreTy -> Set
StoreExt Σ Σ' = ∃[ Δ ] (Σ' ≡ Σ ++ Δ)

storeExt-refl : {Σ : StoreTy} -> StoreExt Σ Σ
storeExt-refl {Σ} = [] , sym (++-identityʳ Σ)

typing-store-ext :
  {Γ : Ctx} {Σ Σ' : StoreTy} {M : Term} {A : Ty} ->
  Γ ∣ Σ ⊢ M ⦂ A ->
  StoreExt Σ Σ' ->
  Γ ∣ Σ' ⊢ M ⦂ A
typing-store-ext hM (Δ , refl) = typing-store-weaken hM Δ

------------------------------------------------------------------------
-- Store typing invariant
------------------------------------------------------------------------

record StoreWellTyped (Σ : StoreTy) (μ : Store) : Set where
  constructor mkStoreWellTyped
  field
    len : length μ ≡ length Σ
    lookupTyped :
      ∀ {l A} ->
      Σ ∋ l ⦂ A ->
      ∃[ V ] (lookupStore μ l ≡ just V) × ([] ∣ Σ ⊢ V ⦂ A) × Value V

open StoreWellTyped public

store-wt-empty : StoreWellTyped [] []
store-wt-empty =
  mkStoreWellTyped
    refl
    (λ { () })

------------------------------------------------------------------------
-- Store/list helper lemmas
------------------------------------------------------------------------

length-++-one :
  {X : Set} ->
  (xs : List X) ->
  (x : X) ->
  length (xs ++ (x ∷ [])) ≡ sucℕ (length xs)
length-++-one [] x = refl
length-++-one (y ∷ xs) x = cong sucℕ (length-++-one xs x)

∋-last :
  (Σ : StoreTy) ->
  (A : Ty) ->
  (Σ ++ (A ∷ [])) ∋ length Σ ⦂ A
∋-last [] A = STLCRef.Z
∋-last (B ∷ Σ) A = STLCRef.S (∋-last Σ A)

lookupStore-append-right-new :
  (μ : Store) ->
  (V : Term) ->
  lookupStore (μ ++ (V ∷ [])) (length μ) ≡ just V
lookupStore-append-right-new [] V = refl
lookupStore-append-right-new (W ∷ μ) V =
  lookupStore-append-right-new μ V

lookupStore-append-right-old :
  {μ : Store} {l : ℕ} {W V : Term} ->
  lookupStore μ l ≡ just W ->
  lookupStore (μ ++ (V ∷ [])) l ≡ just W
lookupStore-append-right-old {μ = []} ()
lookupStore-append-right-old {μ = W ∷ μ} {l = zeroℕ} eq = eq
lookupStore-append-right-old {μ = W ∷ μ} {l = sucℕ l} eq =
  lookupStore-append-right-old {μ = μ} {l = l} eq

lookupStore-update-same :
  {μ μ' : Store} {l : ℕ} {V : Term} ->
  updateStore μ l V ≡ just μ' ->
  lookupStore μ' l ≡ just V
lookupStore-update-same {μ = []} ()
lookupStore-update-same {μ = W ∷ μ} {l = zeroℕ} refl = refl
lookupStore-update-same {μ = W ∷ μ} {l = sucℕ l} {V = V} eq with updateStore μ l V in upd
lookupStore-update-same {μ = W ∷ μ} {l = sucℕ l} {V = V} eq | nothing =
  ⊥-elim (nothing≢just eq)
lookupStore-update-same {μ = W ∷ μ} {l = sucℕ l} {V = V} eq | just μ'' with eq
lookupStore-update-same {μ = W ∷ μ} {l = sucℕ l} {V = V} eq | just μ'' | refl =
  lookupStore-update-same {μ = μ} {μ' = μ''} {l = l} {V = V} upd

lookupStore-update-other :
  {μ μ' : Store} {k l : ℕ} {V : Term} ->
  k ≢ l ->
  updateStore μ l V ≡ just μ' ->
  lookupStore μ' k ≡ lookupStore μ k
lookupStore-update-other {μ = []} neq ()
lookupStore-update-other {μ = W ∷ μ} {k = zeroℕ} {l = zeroℕ} neq eq =
  ⊥-elim (neq refl)
lookupStore-update-other {μ = W ∷ μ} {k = zeroℕ} {l = sucℕ l} {V = V} neq eq
  with updateStore μ l V in upd
lookupStore-update-other {μ = W ∷ μ} {k = zeroℕ} {l = sucℕ l} {V = V} neq eq
  | nothing =
  ⊥-elim (nothing≢just eq)
lookupStore-update-other {μ = W ∷ μ} {k = zeroℕ} {l = sucℕ l} {V = V} neq eq
  | just μ'' with eq
lookupStore-update-other {μ = W ∷ μ} {k = zeroℕ} {l = sucℕ l} {V = V} neq eq
  | just μ'' | refl = refl
lookupStore-update-other {μ = W ∷ μ} {k = sucℕ k} {l = zeroℕ} neq refl = refl
lookupStore-update-other {μ = W ∷ μ} {k = sucℕ k} {l = sucℕ l} {V = V} neq eq
  with updateStore μ l V in upd
lookupStore-update-other {μ = W ∷ μ} {k = sucℕ k} {l = sucℕ l} {V = V} neq eq
  | nothing =
  ⊥-elim (nothing≢just eq)
lookupStore-update-other {μ = W ∷ μ} {k = sucℕ k} {l = sucℕ l} {V = V} neq eq
  | just μ'' with eq
lookupStore-update-other {μ = W ∷ μ} {k = sucℕ k} {l = sucℕ l} {V = V} neq eq
  | just μ'' | refl =
  lookupStore-update-other
    {μ = μ}
    {μ' = μ''}
    {k = k}
    {l = l}
    {V = V}
    (λ p -> neq (cong sucℕ p))
    upd

updateStore-length :
  {μ μ' : Store} {l : ℕ} {V : Term} ->
  updateStore μ l V ≡ just μ' ->
  length μ' ≡ length μ
updateStore-length {μ = []} ()
updateStore-length {μ = W ∷ μ} {l = zeroℕ} refl = refl
updateStore-length {μ = W ∷ μ} {l = sucℕ l} {V = V} eq with updateStore μ l V in upd
updateStore-length {μ = W ∷ μ} {l = sucℕ l} {V = V} eq | nothing =
  ⊥-elim (nothing≢just eq)
updateStore-length {μ = W ∷ μ} {l = sucℕ l} {V = V} eq | just μ'' with eq
updateStore-length {μ = W ∷ μ} {l = sucℕ l} {V = V} eq | just μ'' | refl =
  cong sucℕ (updateStore-length {μ = μ} {μ' = μ''} {l = l} {V = V} upd)

updateStore-suc :
  {μ μ' : Store} {l : ℕ} {V W : Term} ->
  updateStore μ l V ≡ just μ' ->
  updateStore (W ∷ μ) (sucℕ l) V ≡ just (W ∷ μ')
updateStore-suc {W = W} upd rewrite upd = refl

updateStore-total-from-lookup :
  {μ : Store} {l : ℕ} {T V : Term} ->
  lookupStore μ l ≡ just T ->
  ∃[ μ' ] (updateStore μ l V ≡ just μ')
updateStore-total-from-lookup {μ = []} ()
updateStore-total-from-lookup {μ = U ∷ μ} {l = zeroℕ} {V = V} eq =
  (V ∷ μ) , refl
updateStore-total-from-lookup {μ = U ∷ μ} {l = sucℕ l} {T = T} {V = V} eq
  with updateStore-total-from-lookup {μ = μ} {l = l} {T = T} {V = V} eq
updateStore-total-from-lookup {μ = U ∷ μ} {l = sucℕ l} {T = T} {V = V} eq
  | μ' , upd =
  (U ∷ μ') , updateStore-suc {μ = μ} {μ' = μ'} {l = l} {V = V} {W = U} upd

data AppendOneSplit (Σ : StoreTy) (A : Ty) : (l : ℕ) -> (B : Ty) -> Set where
  old :
    ∀ {l B} ->
    Σ ∋ l ⦂ B ->
    AppendOneSplit Σ A l B

  new :
    ∀ {B} ->
    B ≡ A ->
    AppendOneSplit Σ A (length Σ) B

append-one-split :
  {Σ : StoreTy} {A B : Ty} {l : ℕ} ->
  (Σ ++ (A ∷ [])) ∋ l ⦂ B ->
  AppendOneSplit Σ A l B
append-one-split {Σ = []} STLCRef.Z = new refl
append-one-split {Σ = []} (STLCRef.S ())
append-one-split {Σ = C ∷ Σ} STLCRef.Z = old STLCRef.Z
append-one-split {Σ = C ∷ Σ} (STLCRef.S h) with append-one-split {Σ = Σ} h
... | old h' = old (STLCRef.S h')
... | new eqB = new eqB

store-wt-alloc :
  {Σ : StoreTy} {μ : Store} {A : Ty} {V : Term} ->
  StoreWellTyped Σ μ ->
  [] ∣ Σ ⊢ V ⦂ A ->
  Value V ->
  StoreWellTyped (Σ ++ (A ∷ [])) (μ ++ (V ∷ []))
store-wt-alloc {Σ} {μ} {A} {V} wt V⊢ vV =
  mkStoreWellTyped len' lookup'
  where
    len' : length (μ ++ (V ∷ [])) ≡ length (Σ ++ (A ∷ []))
    len' =
      trans
        (length-++-one μ V)
        (trans
          (cong sucℕ (len wt))
          (sym (length-++-one Σ A)))

    lookup-old :
      ∀ {l B} ->
      Σ ∋ l ⦂ B ->
      ∃[ W ]
        (lookupStore (μ ++ (V ∷ [])) l ≡ just W) ×
        ([] ∣ (Σ ++ (A ∷ [])) ⊢ W ⦂ B) ×
        Value W
    lookup-old {l} {B} hOld with lookupTyped wt hOld
    lookup-old {l} {B} hOld | W , eqW , W⊢ , vW =
      W ,
      lookupStore-append-right-old {μ = μ} {l = l} {W = W} {V = V} eqW ,
      typing-store-weaken W⊢ (A ∷ []) ,
      vW

    lookup' :
      ∀ {l B} ->
      (Σ ++ (A ∷ [])) ∋ l ⦂ B ->
      ∃[ W ]
        (lookupStore (μ ++ (V ∷ [])) l ≡ just W) ×
        ([] ∣ (Σ ++ (A ∷ [])) ⊢ W ⦂ B) ×
        Value W
    lookup' {l} {B} h with append-one-split {Σ = Σ} {A = A} h
    lookup' {l} {B} h | old hOld = lookup-old hOld
    lookup' {l} {B} h | new eqB rewrite sym (len wt) | eqB =
      V ,
      lookupStore-append-right-new μ V ,
      typing-store-weaken V⊢ (A ∷ []) ,
      vV

store-wt-update :
  {Σ : StoreTy} {μ μ' : Store}
  {l : ℕ} {A : Ty} {V : Term} ->
  StoreWellTyped Σ μ ->
  Σ ∋ l ⦂ A ->
  [] ∣ Σ ⊢ V ⦂ A ->
  Value V ->
  updateStore μ l V ≡ just μ' ->
  StoreWellTyped Σ μ'
store-wt-update {Σ} {μ} {μ'} {l} {A} {V} wt hLoc V⊢ vV upd =
  mkStoreWellTyped len' lookup'
  where
    len' : length μ' ≡ length Σ
    len' = trans (updateStore-length {μ = μ} {μ' = μ'} {l = l} {V = V} upd)
                 (len wt)

    lookup' :
      ∀ {k B} ->
      Σ ∋ k ⦂ B ->
      ∃[ W ]
        (lookupStore μ' k ≡ just W) ×
        ([] ∣ Σ ⊢ W ⦂ B) ×
        Value W
    lookup' {k} {B} h with nat-eq-dec k l
    lookup' {k} {B} h | yes k≡l rewrite k≡l =
      let
        BA : B ≡ A
        BA = ∋-unique h hLoc
      in
      V ,
      lookupStore-update-same {μ = μ} {μ' = μ'} {l = l} {V = V} upd ,
      substEq (λ T -> [] ∣ Σ ⊢ V ⦂ T) (sym BA) V⊢ ,
      vV
    lookup' {k} {B} h | no k≢l with lookupTyped wt h
    lookup' {k} {B} h | no k≢l | W , eqW , W⊢ , vW =
      W ,
      trans (lookupStore-update-other
               {μ = μ}
               {μ' = μ'}
               {k = k}
               {l = l}
               {V = V}
               k≢l
               upd)
            eqW ,
      W⊢ ,
      vW

------------------------------------------------------------------------
-- Canonical/value-shape lemmas
------------------------------------------------------------------------

noZeroFn : {Σ : StoreTy} {A B : Ty} -> [] ∣ Σ ⊢ `zero ⦂ (A ⇒ B) -> ⊥
noZeroFn ()

noSucFn :
  {Σ : StoreTy} {A B : Ty} {M : Term} ->
  [] ∣ Σ ⊢ (`suc M) ⦂ (A ⇒ B) ->
  ⊥
noSucFn ()

noUnitFn : {Σ : StoreTy} {A B : Ty} -> [] ∣ Σ ⊢ `unit ⦂ (A ⇒ B) -> ⊥
noUnitFn ()

noLocFn :
  {Σ : StoreTy} {A B : Ty} {l : ℕ} ->
  [] ∣ Σ ⊢ (`loc l) ⦂ (A ⇒ B) ->
  ⊥
noLocFn ()

noLamNat :
  {Σ : StoreTy} {A : Ty} {N : Term} ->
  [] ∣ Σ ⊢ (ƛ A ⇒ N) ⦂ nat ->
  ⊥
noLamNat ()

noUnitNat : {Σ : StoreTy} -> [] ∣ Σ ⊢ `unit ⦂ nat -> ⊥
noUnitNat ()

noLocNat :
  {Σ : StoreTy} {l : ℕ} ->
  [] ∣ Σ ⊢ (`loc l) ⦂ nat ->
  ⊥
noLocNat ()

ref-value-loc :
  {Σ : StoreTy} {V : Term} {A : Ty} ->
  [] ∣ Σ ⊢ V ⦂ ref A ->
  Value V ->
  ∃[ l ] (V ≡ `loc l) × (Σ ∋ l ⦂ A)
ref-value-loc (⊢loc hLoc) (`loc l) = l , refl , hLoc

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

progress :
  {M : Term} {A : Ty} {Σ : StoreTy} {μ : Store} ->
  [] ∣ Σ ⊢ M ⦂ A ->
  StoreWellTyped Σ μ ->
  (∃[ c' ] ((M , μ) —→ c')) ⊎ Value M
progress (⊢` ()) wt
progress (⊢ƛ hN) wt = inj₂ (ƛ _ ⇒ _)
progress (⊢· hL hM) wt with progress hL wt
... | inj₁ ((L' , μ') , s) = inj₁ ((_ , _) , ξ-·₁ s)
... | inj₂ vL with progress hM wt
...   | inj₁ ((M' , μ') , s) = inj₁ ((_ , _) , ξ-·₂ vL s)
...   | inj₂ vM with vL
...     | ƛ A ⇒ N = inj₁ ((_ , _) , β-ƛ vM)
...     | `zero = ⊥-elim (noZeroFn hL)
...     | `suc v = ⊥-elim (noSucFn hL)
...     | `unit = ⊥-elim (noUnitFn hL)
...     | `loc l = ⊥-elim (noLocFn hL)
progress ⊢zero wt = inj₂ `zero
progress (⊢suc hM) wt with progress hM wt
... | inj₁ ((M' , μ') , s) = inj₁ ((_ , _) , ξ-suc s)
... | inj₂ vM = inj₂ (`suc vM)
progress (⊢case hL hM hN) wt with progress hL wt
... | inj₁ ((L' , μ') , s) = inj₁ ((_ , _) , ξ-case s)
... | inj₂ vL with vL
...   | `zero = inj₁ ((_ , _) , β-zero)
...   | `suc v = inj₁ ((_ , _) , β-suc v)
...   | ƛ A ⇒ N = ⊥-elim (noLamNat hL)
...   | `unit = ⊥-elim (noUnitNat hL)
...   | `loc l = ⊥-elim (noLocNat hL)
progress ⊢unit wt = inj₂ `unit
progress (⊢ref hM) wt with progress hM wt
... | inj₁ ((M' , μ') , s) = inj₁ ((_ , _) , ξ-ref s)
... | inj₂ vM = inj₁ ((_ , _) , β-ref vM)
progress (⊢! hM) wt with progress hM wt
... | inj₁ ((M' , μ') , s) = inj₁ ((_ , _) , ξ-! s)
... | inj₂ vM with ref-value-loc hM vM
...   | l , refl , hLoc with lookupTyped wt hLoc
...     | V , eq , V⊢ , vV = inj₁ ((_ , _) , β-! eq)
progress {μ = μ} (⊢:= {M = M} hL hM) wt with progress hL wt
... | inj₁ ((L' , μ') , s) = inj₁ ((_ , _) , ξ-:=₁ s)
... | inj₂ vL with ref-value-loc hL vL
...   | l , refl , hLoc with progress hM wt
...     | inj₁ ((M' , μ') , s) = inj₁ ((_ , _) , ξ-:=₂ (`loc l) s)
...     | inj₂ vM with lookupTyped wt hLoc
...       | W , eqW , W⊢ , vW with updateStore-total-from-lookup
                                     {μ = μ}
                                     {l = l}
                                     {T = W}
                                     {V = M}
                                     eqW
...         | μ' , upd = inj₁ ((_ , _) , β-:= vM upd)
progress (⊢loc hL) wt = inj₂ (`loc _)

------------------------------------------------------------------------
-- Preservation (with store-typing growth)
------------------------------------------------------------------------

preservation :
  {M M' : Term} {A : Ty} {Σ : StoreTy} {μ μ' : Store} ->
  [] ∣ Σ ⊢ M ⦂ A ->
  StoreWellTyped Σ μ ->
  (M , μ) —→ (M' , μ') ->
  ∃[ Σ' ]
    StoreExt Σ Σ' ×
    ([] ∣ Σ' ⊢ M' ⦂ A) ×
    StoreWellTyped Σ' μ'
preservation (⊢· (⊢ƛ hN) hM) wt (β-ƛ vW) =
  _ ,
  storeExt-refl ,
  typing_single_subst hN hM ,
  wt
preservation (⊢case hL hM hN) wt β-zero =
  _ ,
  storeExt-refl ,
  hM ,
  wt
preservation (⊢case (⊢suc hL) hM hN) wt (β-suc vV) =
  _ ,
  storeExt-refl ,
  typing_single_subst hN hL ,
  wt
preservation (⊢· hL hM) wt (ξ-·₁ s) with preservation hL wt s
... | Σ' , ext , hL' , wt' =
      Σ' ,
      ext ,
      ⊢· hL' (typing-store-ext hM ext) ,
      wt'
preservation (⊢· hL hM) wt (ξ-·₂ vV s) with preservation hM wt s
... | Σ' , ext , hM' , wt' =
      Σ' ,
      ext ,
      ⊢· (typing-store-ext hL ext) hM' ,
      wt'
preservation (⊢suc hM) wt (ξ-suc s) with preservation hM wt s
... | Σ' , ext , hM' , wt' =
      Σ' ,
      ext ,
      ⊢suc hM' ,
      wt'
preservation (⊢case hL hM hN) wt (ξ-case s) with preservation hL wt s
... | Σ' , ext , hL' , wt' =
      Σ' ,
      ext ,
      ⊢case hL' (typing-store-ext hM ext) (typing-store-ext hN ext) ,
      wt'
preservation (⊢ref hM) wt (ξ-ref s) with preservation hM wt s
... | Σ' , ext , hM' , wt' =
      Σ' ,
      ext ,
      ⊢ref hM' ,
      wt'
preservation {Σ = Σ} (⊢ref {A = A} hV) wt (β-ref vV) =
  (Σ ++ (A ∷ [])) ,
  ((A ∷ []) , refl) ,
  (⊢loc (substEq (λ n -> (Σ ++ (A ∷ [])) ∋ n ⦂ A)
                  (sym (len wt))
                  (∋-last Σ A))) ,
  (store-wt-alloc wt hV vV)
preservation (⊢! hM) wt (ξ-! s) with preservation hM wt s
... | Σ' , ext , hM' , wt' =
      Σ' ,
      ext ,
      ⊢! hM' ,
      wt'
preservation {Σ = Σ} (⊢! (⊢loc hLoc)) wt (β-! {V = V} eq)
  with lookupTyped wt hLoc
... | V₀ , eq₀ , V₀⊢ , vV₀ =
      let
        V₀≡V : V₀ ≡ V
        V₀≡V = just-injective (trans (sym eq₀) eq)
      in
      _ ,
      storeExt-refl ,
      substEq (λ X -> [] ∣ Σ ⊢ X ⦂ _) V₀≡V V₀⊢ ,
      wt
preservation (⊢:= hL hM) wt (ξ-:=₁ s) with preservation hL wt s
... | Σ' , ext , hL' , wt' =
      Σ' ,
      ext ,
      ⊢:= hL' (typing-store-ext hM ext) ,
      wt'
preservation (⊢:= hL hM) wt (ξ-:=₂ vL s) with preservation hM wt s
... | Σ' , ext , hM' , wt' =
      Σ' ,
      ext ,
      ⊢:= (typing-store-ext hL ext) hM' ,
      wt'
preservation (⊢:= (⊢loc hLoc) hV) wt (β-:= vV upd) =
  _ ,
  storeExt-refl ,
  ⊢unit ,
  store-wt-update wt hLoc hV vV upd

------------------------------------------------------------------------
-- Multi-step type safety
------------------------------------------------------------------------

preservation-↠ :
  {M N : Term} {A : Ty} {Σ : StoreTy} {μ ν : Store} ->
  [] ∣ Σ ⊢ M ⦂ A ->
  StoreWellTyped Σ μ ->
  (M , μ) —↠ (N , ν) ->
  ∃[ Σ' ] ([] ∣ Σ' ⊢ N ⦂ A) × StoreWellTyped Σ' ν
preservation-↠ hM wt (_ ∎) = _ , hM , wt
preservation-↠ hM wt (_ —→⟨ s ⟩ ms) with preservation hM wt s
... | Σ₁ , ext₁ , hM₁ , wt₁ = preservation-↠ hM₁ wt₁ ms

typeSafety :
  {M N : Term} {A : Ty} {μ : Store} ->
  [] ∣ [] ⊢ M ⦂ A ->
  (M , []) —↠ (N , μ) ->
  (∃[ c' ] ((N , μ) —→ c')) ⊎ Value N
typeSafety hM M—↠N with preservation-↠ hM store-wt-empty M—↠N
... | Σ' , hN , wtN = progress hN wtN
