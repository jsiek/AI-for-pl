module proof.Fundamental where

-- File Charter:
--   * Step-indexed logical-relation skeleton for STLCRec (de Bruijn style).
--   * Starts from `lemma-𝓖` and proceeds toward `fundamental`, following
--     the structure of `StepIndexedLR5`.

open import Data.Nat using (ℕ; _+_; _<_; _≤_; _∸_; z≤n; s≤s) renaming (zero to zeroℕ; suc to sucℕ)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat.Properties using
  (+-∸-assoc; +-assoc; +-comm; +-identityʳ; +-suc; <⇒≤; ≤-pred; ≤-refl; ≤-trans;
   +-monoʳ-≤; m+[n∸m]≡n; m+n≤o⇒m≤o; m+n≤o⇒m≤o∸n; m+n≤o⇒n≤o; m+n∸m≡n; m≤m+n; m≤n+m; m∸n≤m;
   m∸[m∸n]≡n; suc-injective; ∸-+-assoc; ∸-monoˡ-<; ∸-monoʳ-≤)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
  renaming (subst to substEq)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import STLCRec
open import proof.Subst using (subst_id; consSub; exts_sub_cons)

≤-step : ∀ {m n : ℕ} -> m ≤ n -> m ≤ sucℕ n
≤-step z≤n = z≤n
≤-step (s≤s m≤n) = s≤s (≤-step m≤n)

m≡n→m≤n : ∀ {m n} -> m ≡ n -> m ≤ n
m≡n→m≤n refl = ≤-refl

ax∸bx : ∀ a b x -> x ≤ b -> a ∸ x ∸ (b ∸ x) ≡ a ∸ b
ax∸bx a b x x≤b =
  trans (∸-+-assoc a x (b ∸ x))
        (cong (a ∸_) (m+[n∸m]≡n x≤b))

m∸[n∸o]≡m+o∸n : ∀ m n o -> o ≤ n -> m ∸ (n ∸ o) ≡ (o + m) ∸ n
m∸[n∸o]≡m+o∸n m n zeroℕ o≤n = refl
m∸[n∸o]≡m+o∸n m (sucℕ n) (sucℕ o) (s≤s o≤n) =
  m∸[n∸o]≡m+o∸n m n o o≤n

1+m≡o⇒m≡o∸1 : ∀ m o -> sucℕ m ≡ o -> m ≡ o ∸ 1
1+m≡o⇒m≡o∸1 m .(sucℕ m) refl = refl

k+m≡o⇒m≡o∸k : ∀ k m o -> k + m ≡ o -> m ≡ o ∸ k
k+m≡o⇒m≡o∸k k m .(k + m) refl = sym (m+n∸m≡n k m)

1+m≤o⇒m≤o∸1 : ∀ m o -> sucℕ m ≤ o -> m ≤ o ∸ 1
1+m≤o⇒m≤o∸1 m .(sucℕ _) (s≤s m≤o) = m≤o

j∸m<k∸m : ∀ j k m -> m ≤ j -> j < k -> j ∸ m < k ∸ m
j∸m<k∸m j k m m≤j j<k = ∸-monoˡ-< j<k m≤j

j≤k⇒j∸1<k : ∀ j k -> 1 ≤ j -> sucℕ j ≤ sucℕ k -> j ∸ 1 < k
j≤k⇒j∸1<k (sucℕ j) k (s≤s z≤n) (s≤s j<k) = j<k

lemma-+≤ : ∀ {lMM' lWM'N lL'MN lLL' j : ℕ}
  -> lMM' + lWM'N ≡ lL'MN
  -> lLL' + lL'MN ≡ j
  -> lMM' ≤ j
lemma-+≤ {lMM'} {lWM'N} {lL'MN} {lLL'} {j} l+≡₁ l+≡₂ =
  ≤-trans (m+n≤o⇒m≤o lMM' (m≡n→m≤n l+≡₁))
          (m+n≤o⇒n≤o lLL' (m≡n→m≤n l+≡₂))

lemma-aux : ∀ m n o n' -> m + n ≤ o -> n' ≤ n -> m + n' ≤ o
lemma-aux m n o n' m+n≤o n'≤n = ≤-trans (+-monoʳ-≤ m n'≤n) m+n≤o

lemma-+≤₂ : ∀ {lMM' lWM'N lL'MN lLL' j : ℕ}
  -> lMM' + lWM'N ≡ lL'MN
  -> lLL' + lL'MN ≡ j
  -> lLL' + lMM' ≤ j
lemma-+≤₂ {lMM'} {lWM'N} {lL'MN} {lLL'} {j} l+≡₁ l+≡₂ =
  lemma-aux lLL' lL'MN j lMM' (m≡n→m≤n l+≡₂)
            (m+n≤o⇒m≤o lMM' (m≡n→m≤n l+≡₁))

m∸a+b≤m∸a : ∀ m a b -> m ∸ (a + b) ≤ m ∸ a
m∸a+b≤m∸a m zeroℕ b = m∸n≤m m b
m∸a+b≤m∸a zeroℕ (sucℕ a) b = z≤n
m∸a+b≤m∸a (sucℕ m) (sucℕ a) b = m∸a+b≤m∸a m a b

------------------------------------------------------------------------
-- StepIndexedLR5-inspired semantic domains (de Bruijn adaptation)
------------------------------------------------------------------------

len : ∀ {M N : Term} -> M —↠ N -> ℕ
len (_ ∎) = zeroℕ
len (_ —→⟨ _ ⟩ M↠N) = sucℕ (len M↠N)

irred : Term -> Set
irred M = ¬ (∃[ N ] (M —→ N))

mutual
  𝓥 : Ty -> Term -> ℕ -> Set

  𝓥 nat (` i) k = ⊥
  𝓥 nat (ƛ A ⇒ N) k = ⊥
  𝓥 nat (L · M) k = ⊥
  𝓥 nat `zero k = ⊤
  𝓥 nat (`suc M) k = 𝓥 nat M k
  𝓥 nat (case_[zero⇒_|suc⇒_] L M N) k = ⊥
  𝓥 nat (μ A ⇒ N) k = ⊥

  𝓥 (A ⇒ B) (` i) k = ⊥
  𝓥 (A ⇒ B) (ƛ C ⇒ N) k =
    (j : ℕ) -> j < k -> (V : Term) -> 𝓥 A V j -> ℰ B (N [ V ]) j
  𝓥 (A ⇒ B) (L · M) k = ⊥
  𝓥 (A ⇒ B) `zero k = ⊥
  𝓥 (A ⇒ B) (`suc M) k = ⊥
  𝓥 (A ⇒ B) (case_[zero⇒_|suc⇒_] L M N) k = ⊥
  𝓥 (A ⇒ B) (μ C ⇒ N) zeroℕ = ⊤
  𝓥 (A ⇒ B) (μ C ⇒ N) (sucℕ k) = 𝓥 (A ⇒ B) (N [ μ C ⇒ N ]) k

  ℰ : Ty -> Term -> ℕ -> Set
  ℰ A M k =
    ∀ j -> j < k -> ∀ N ->
    (M↠N : M —↠ N) ->
    len M↠N ≡ j ->
    irred N ->
    Σ Term (λ W -> (N ≡ W) × 𝓥 A W (k ∸ j))

𝓖 : Ctx -> Subst -> ℕ -> Set
𝓖 [] σ k = ⊤
𝓖 (A ∷ Γ) σ k = 𝓖 Γ (λ i -> σ (sucℕ i)) k × 𝓥 A (σ zeroℕ) k

lemma-𝓖 :
  (Γ : Ctx) -> (σ : Subst) -> (k : ℕ) ->
  𝓖 Γ σ k ->
  ∀ {i A} -> Γ ∋ i ⦂ A -> 𝓥 A (σ i) k
lemma-𝓖 [] σ k g ()
lemma-𝓖 (A ∷ Γ) σ k ⟨ 𝓖Γσk , 𝓥Aσ0k ⟩ Z = 𝓥Aσ0k
lemma-𝓖 (A ∷ Γ) σ k ⟨ 𝓖Γσk , 𝓥Aσ0k ⟩ (S i∋) =
  lemma-𝓖 Γ (λ j -> σ (sucℕ j)) k 𝓖Γσk i∋

𝓥-monotone : ∀ A M k -> 𝓥 A M (sucℕ k) -> 𝓥 A M k
𝓥-monotone nat (` i) k ()
𝓥-monotone nat (ƛ A ⇒ N) k ()
𝓥-monotone nat (L · M) k ()
𝓥-monotone nat `zero k 𝓥nat = tt
𝓥-monotone nat (`suc M) k 𝓥nat = 𝓥-monotone nat M k 𝓥nat
𝓥-monotone nat (case_[zero⇒_|suc⇒_] L M N) k ()
𝓥-monotone nat (μ A ⇒ N) k ()
𝓥-monotone (A ⇒ B) (` i) k ()
𝓥-monotone (A ⇒ B) (ƛ C ⇒ N) k 𝓥fun =
  λ j j<k V 𝓥Vj -> 𝓥fun j (≤-step j<k) V 𝓥Vj
𝓥-monotone (A ⇒ B) (L · M) k ()
𝓥-monotone (A ⇒ B) `zero k ()
𝓥-monotone (A ⇒ B) (`suc M) k ()
𝓥-monotone (A ⇒ B) (case_[zero⇒_|suc⇒_] L M N) k ()
𝓥-monotone (A ⇒ B) (μ C ⇒ N) zeroℕ 𝓥μ = tt
𝓥-monotone (A ⇒ B) (μ C ⇒ N) (sucℕ k) 𝓥μ =
  𝓥-monotone (A ⇒ B) (N [ μ C ⇒ N ]) k 𝓥μ

𝓔-monotone : ∀ A M k -> ℰ A M (sucℕ k) -> ℰ A M k
𝓔-monotone A M k 𝓔AM j j<k N M↠N len≡ irrN
  with 𝓔AM j (≤-step j<k) N M↠N len≡ irrN
... | ⟨ W , ⟨ N≡W , 𝓥AW[suc-k∸j] ⟩ ⟩ =
  ⟨ W , ⟨ N≡W , 𝓥-monotone A W (k ∸ j) 𝓥AW[suc[k∸j]] ⟩ ⟩
  where
    𝓥AW[suc[k∸j]] : 𝓥 A W (sucℕ (k ∸ j))
    𝓥AW[suc[k∸j]] =
      substEq (𝓥 A W) (+-∸-assoc 1 (<⇒≤ j<k)) 𝓥AW[suc-k∸j]

𝓖-monotone : ∀ Γ σ k -> 𝓖 Γ σ (sucℕ k) -> 𝓖 Γ σ k
𝓖-monotone [] σ k 𝓖[] = tt
𝓖-monotone (A ∷ Γ) σ k ⟨ 𝓖Γσk+1 , 𝓥Aσ0k+1 ⟩ =
  ⟨ 𝓖-monotone Γ (λ i -> σ (sucℕ i)) k 𝓖Γσk+1
  , 𝓥-monotone A (σ zeroℕ) k 𝓥Aσ0k+1
  ⟩

𝓖-monotone* :
  ∀ Γ σ k -> 𝓖 Γ σ k ->
  ∀ j -> j ≤ k -> 𝓖 Γ σ (k ∸ j)
𝓖-monotone* Γ σ k 𝓖Γσk zeroℕ j≤k = 𝓖Γσk
𝓖-monotone* Γ σ zeroℕ 𝓖Γσk (sucℕ j) ()
𝓖-monotone* Γ σ (sucℕ k) 𝓖Γσk (sucℕ j) (s≤s j≤k) =
  𝓖-monotone* Γ σ k (𝓖-monotone Γ σ k 𝓖Γσk) j j≤k

𝓖-<-monotone : ∀ Γ σ k j -> 𝓖 Γ σ k -> j < k -> 𝓖 Γ σ j
𝓖-<-monotone Γ σ k j 𝓖Γσk j<k =
  substEq (𝓖 Γ σ) (m∸[m∸n]≡n (<⇒≤ j<k)) 𝓖k∸[k∸j]
  where
    𝓖k∸[k∸j] : 𝓖 Γ σ (k ∸ (k ∸ j))
    𝓖k∸[k∸j] = 𝓖-monotone* Γ σ k 𝓖Γσk (k ∸ j) (m∸n≤m k j)

𝓥-monotone* :
  ∀ A V k -> 𝓥 A V k ->
  ∀ j -> j ≤ k -> 𝓥 A V (k ∸ j)
𝓥-monotone* A V k 𝓥AVk zeroℕ j≤k = 𝓥AVk
𝓥-monotone* A V zeroℕ 𝓥AVk (sucℕ j) ()
𝓥-monotone* A V (sucℕ k) 𝓥AVk (sucℕ j) (s≤s j≤k) =
  𝓥-monotone* A V k (𝓥-monotone A V k 𝓥AVk) j j≤k

𝓥-≤-monotone : ∀ A V k n -> 𝓥 A V k -> n ≤ k -> 𝓥 A V n
𝓥-≤-monotone A V k n 𝓥AVk n≤k =
  substEq (𝓥 A V) (m∸[m∸n]≡n n≤k) (𝓥-monotone* A V k 𝓥AVk (k ∸ n) (m∸n≤m k n))

𝓥-value : ∀ {A W k} -> 𝓥 A W k -> Value W
𝓥-value {A = nat} {W = ` i} ()
𝓥-value {A = nat} {W = ƛ A ⇒ N} ()
𝓥-value {A = nat} {W = L · M} ()
𝓥-value {A = nat} {W = `zero} w = `zero
𝓥-value {A = nat} {W = `suc W} w = `suc (𝓥-value {A = nat} {W = W} w)
𝓥-value {A = nat} {W = case_[zero⇒_|suc⇒_] L M N} ()
𝓥-value {A = nat} {W = μ A ⇒ N} ()
𝓥-value {A = A ⇒ B} {W = ` i} ()
𝓥-value {A = A ⇒ B} {W = ƛ C ⇒ N} w = ƛ C ⇒ N
𝓥-value {A = A ⇒ B} {W = L · M} ()
𝓥-value {A = A ⇒ B} {W = `zero} ()
𝓥-value {A = A ⇒ B} {W = `suc M} ()
𝓥-value {A = A ⇒ B} {W = case_[zero⇒_|suc⇒_] L M N} ()
𝓥-value {A = A ⇒ B} {W = μ C ⇒ N} {k = zeroℕ} w = μ C ⇒ N
𝓥-value {A = A ⇒ B} {W = μ C ⇒ N} {k = sucℕ k} w = μ C ⇒ N

value-¬→ : ∀ {V N} -> Value V -> ¬ (V —→ N)
value-¬→ (ƛ A ⇒ N) ()
value-¬→ `zero ()
value-¬→ (`suc vV) (ξ-suc V→N) = value-¬→ vV V→N
value-¬→ (μ A ⇒ N) ()

value? : (M : Term) -> Dec (Value M)
value? (` i) = no (λ ())
value? (ƛ A ⇒ N) = yes (ƛ A ⇒ N)
value? (L · M) = no (λ ())
value? `zero = yes `zero
value? (`suc M) with value? M
... | yes vM = yes (`suc vM)
... | no ¬vM = no (λ { (`suc vM) -> ¬vM vM })
value? (case_[zero⇒_|suc⇒_] L M N) = no (λ ())
value? (μ A ⇒ N) = yes (μ A ⇒ N)

reducible? : (M : Term) -> Dec (∃[ N ] (M —→ N))
reducible? (` i) = no (λ ())
reducible? (ƛ A ⇒ N) = no (λ ())
reducible? (L · M) with reducible? L
reducible? (L · M) | yes ⟨ L' , L→L' ⟩ = yes ⟨ L' · M , ξ-·₁ L→L' ⟩
reducible? (L · M) | no ¬L→ with value? L
reducible? (L · M) | no ¬L→ | no ¬vL = no λ
  { ⟨ _ , ξ-·₁ L→L' ⟩ -> ¬L→ ⟨ _ , L→L' ⟩
  ; ⟨ _ , ξ-·₂ ⟨ vL , M→M' ⟩ ⟩ -> ¬vL vL
  ; ⟨ _ , β-ƛ vM ⟩ -> ¬vL (ƛ _ ⇒ _)
  ; ⟨ _ , β-μ vM ⟩ -> ¬vL (μ _ ⇒ _)
  }
reducible? (L · M) | no ¬L→ | yes vL with reducible? M
reducible? (L · M) | no ¬L→ | yes vL | yes ⟨ M' , M→M' ⟩ =
  yes ⟨ L · M' , ξ-·₂ ⟨ vL , M→M' ⟩ ⟩
reducible? (L · M) | no ¬L→ | yes (ƛ A ⇒ N) | no ¬M→ with value? M
reducible? (L · M) | no ¬L→ | yes (ƛ A ⇒ N) | no ¬M→ | yes vM =
  yes ⟨ N [ M ] , β-ƛ vM ⟩
reducible? (L · M) | no ¬L→ | yes (ƛ A ⇒ N) | no ¬M→ | no ¬vM = no λ
  { ⟨ _ , ξ-·₁ L→L' ⟩ -> ¬L→ ⟨ _ , L→L' ⟩
  ; ⟨ _ , ξ-·₂ ⟨ _ , M→M' ⟩ ⟩ -> ¬M→ ⟨ _ , M→M' ⟩
  ; ⟨ _ , β-ƛ vM ⟩ -> ¬vM vM
  }
reducible? (L · M) | no ¬L→ | yes (μ A ⇒ N) | no ¬M→ with value? M
reducible? (L · M) | no ¬L→ | yes (μ A ⇒ N) | no ¬M→ | yes vM =
  yes ⟨ (N [ μ A ⇒ N ]) · M , β-μ vM ⟩
reducible? (L · M) | no ¬L→ | yes (μ A ⇒ N) | no ¬M→ | no ¬vM = no λ
  { ⟨ _ , ξ-·₁ L→L' ⟩ -> ¬L→ ⟨ _ , L→L' ⟩
  ; ⟨ _ , ξ-·₂ ⟨ _ , M→M' ⟩ ⟩ -> ¬M→ ⟨ _ , M→M' ⟩
  ; ⟨ _ , β-μ vM ⟩ -> ¬vM vM
  }
reducible? (L · M) | no ¬L→ | yes `zero | no ¬M→ = no λ
  { ⟨ _ , ξ-·₁ L→L' ⟩ -> ¬L→ ⟨ _ , L→L' ⟩
  ; ⟨ _ , ξ-·₂ ⟨ _ , M→M' ⟩ ⟩ -> ¬M→ ⟨ _ , M→M' ⟩
  }
reducible? (L · M) | no ¬L→ | yes (`suc v) | no ¬M→ = no λ
  { ⟨ _ , ξ-·₁ L→L' ⟩ -> ¬L→ ⟨ _ , L→L' ⟩
  ; ⟨ _ , ξ-·₂ ⟨ _ , M→M' ⟩ ⟩ -> ¬M→ ⟨ _ , M→M' ⟩
  }
reducible? `zero = no (λ ())
reducible? (`suc M) with reducible? M
... | yes ⟨ M' , M→M' ⟩ = yes ⟨ `suc M' , ξ-suc M→M' ⟩
... | no ¬M→ = no λ
  { ⟨ _ , ξ-suc M→M' ⟩ -> ¬M→ ⟨ _ , M→M' ⟩
  }
reducible? (case_[zero⇒_|suc⇒_] L M N) with reducible? L
... | yes ⟨ L' , L→L' ⟩ = yes ⟨ case_[zero⇒_|suc⇒_] L' M N , ξ-case L→L' ⟩
... | no ¬L→ with value? L
... | no ¬vL = no λ
  { ⟨ _ , ξ-case L→L' ⟩ -> ¬L→ ⟨ _ , L→L' ⟩
  ; ⟨ _ , β-zero ⟩ -> ¬vL `zero
  ; ⟨ _ , β-suc v ⟩ -> ¬vL (`suc v)
  }
... | yes `zero = yes ⟨ M , β-zero ⟩
... | yes (`suc v) = yes ⟨ _ , β-suc v ⟩
... | yes (ƛ A ⇒ V) = no λ
  { ⟨ _ , ξ-case L→L' ⟩ -> ¬L→ ⟨ _ , L→L' ⟩
  }
... | yes (μ A ⇒ V) = no λ
  { ⟨ _ , ξ-case L→L' ⟩ -> ¬L→ ⟨ _ , L→L' ⟩
  }
reducible? (μ A ⇒ N) = no (λ ())

irred-app-1 : ∀ {L M} -> irred (L · M) -> irred L
irred-app-1 {M = M} irrLM = λ { ⟨ L' , L→L' ⟩ -> irrLM ⟨ L' · M , ξ-·₁ L→L' ⟩ }

irred-app-2 : ∀ {V M} -> irred (V · M) -> Value V -> irred M
irred-app-2 {V = V} irrVM vV = λ { ⟨ M' , M→M' ⟩ -> irrVM ⟨ V · M' , ξ-·₂ ⟨ vV , M→M' ⟩ ⟩ }

irred-value : ∀ {V} -> Value V -> irred V
irred-value vV = λ { ⟨ N , V→N ⟩ -> value-¬→ vV V→N }

irred-app-len-1 : ∀ {L M N}
  -> (j : ℕ)
  -> (LM↠N : L · M —↠ N)
  -> len LM↠N ≡ j
  -> irred N
  -> ∃[ L' ] (Σ (L —↠ L') λ L↠L' ->
       irred L' × Σ (L' · M —↠ N) λ L'M↠N ->
       len L↠L' + len L'M↠N ≡ j)
irred-app-len-1 zeroℕ (L · M ∎) refl irrN =
  ⟨ L , ⟨ L ∎ , ⟨ irred-app-1 irrN , ⟨ L · M ∎ , refl ⟩ ⟩ ⟩ ⟩
irred-app-len-1 (sucℕ j) (L · M —→⟨ ξ-·₁ L→L₁ ⟩ L₁M↠N) len≡ irrN
  with irred-app-len-1 j L₁M↠N (suc-injective len≡) irrN
... | ⟨ L' , ⟨ L₁↠L' , ⟨ irrL' , ⟨ L'M↠N , len+≡ ⟩ ⟩ ⟩ ⟩ =
  ⟨ L' , ⟨ L —→⟨ L→L₁ ⟩ L₁↠L' , ⟨ irrL' , ⟨ L'M↠N , cong sucℕ len+≡ ⟩ ⟩ ⟩ ⟩
irred-app-len-1 (sucℕ j) L'M↠N@(L · M —→⟨ ξ-·₂ ⟨ vL , M→M' ⟩ ⟩ LM↠N) len≡ irrN =
  ⟨ L , ⟨ L ∎ , ⟨ irred-value vL , ⟨ L'M↠N , len≡ ⟩ ⟩ ⟩ ⟩
irred-app-len-1 (sucℕ j) L'M↠N@((ƛ A ⇒ N₀) · M —→⟨ β-ƛ x ⟩ LM↠N) len≡ irrN =
  ⟨ ƛ A ⇒ N₀ , ⟨ (ƛ A ⇒ N₀) ∎ , ⟨ irred-value (ƛ A ⇒ N₀) , ⟨ L'M↠N , len≡ ⟩ ⟩ ⟩ ⟩
irred-app-len-1 (sucℕ j) L'M↠N@((μ C ⇒ V) · M —→⟨ β-μ x ⟩ LM↠N) len≡ irrN =
  ⟨ μ C ⇒ V , ⟨ (μ C ⇒ V) ∎ , ⟨ irred-value (μ C ⇒ V) , ⟨ L'M↠N , len≡ ⟩ ⟩ ⟩ ⟩

irred-app-len-2 : ∀ {M W N}
  -> Value W
  -> (j : ℕ)
  -> (WM↠N : W · M —↠ N)
  -> len WM↠N ≡ j
  -> irred N
  -> ∃[ M' ] (Σ (M —↠ M') λ M↠M' ->
       irred M' × Σ (W · M' —↠ N) λ WM'↠N ->
       len M↠M' + len WM'↠N ≡ j)
irred-app-len-2 {M} {W} vW zeroℕ (W · M ∎) refl irrN =
  ⟨ M , ⟨ M ∎ , ⟨ irred-app-2 irrN vW , ⟨ W · M ∎ , refl ⟩ ⟩ ⟩ ⟩
irred-app-len-2 {M} {W} vW (sucℕ j) (W · M —→⟨ ξ-·₁ W→W₁ ⟩ W₁M↠N) len≡ irrN =
  ⊥-elim (value-¬→ vW W→W₁)
irred-app-len-2 {M} {W} vW (sucℕ j) (W · M —→⟨ ξ-·₂ x ⟩ WM₁↠N) len≡ irrN
  with x
... | ⟨ _ , M→M₁ ⟩
  with irred-app-len-2 vW j WM₁↠N (suc-injective len≡) irrN
... | ⟨ M' , ⟨ M₁↠M' , ⟨ irrM' , ⟨ WM'↠N , len+≡ ⟩ ⟩ ⟩ ⟩ =
  ⟨ M' , ⟨ M —→⟨ M→M₁ ⟩ M₁↠M' , ⟨ irrM' , ⟨ WM'↠N , cong sucℕ len+≡ ⟩ ⟩ ⟩ ⟩
irred-app-len-2 {M} {W} vW (sucℕ j) WM↠N@(W · M —→⟨ β-ƛ x ⟩ W'M↠N) len≡ irrN =
  ⟨ M , ⟨ M ∎ , ⟨ irred-value x , ⟨ WM↠N , len≡ ⟩ ⟩ ⟩ ⟩
irred-app-len-2 {M} {W} vW (sucℕ j) WM↠N@(W · M —→⟨ β-μ x ⟩ W'M↠N) len≡ irrN =
  ⟨ M , ⟨ M ∎ , ⟨ irred-value x , ⟨ WM↠N , len≡ ⟩ ⟩ ⟩ ⟩

irred-suc-M : ∀ {M} -> irred (`suc M) -> irred M
irred-suc-M irr-suc-M =
  λ { ⟨ M' , M→M' ⟩ -> irr-suc-M ⟨ `suc M' , ξ-suc M→M' ⟩ }

suc-↠-inv : ∀ {M N} -> (sucM↠N : `suc M —↠ N) ->
  Σ Term (λ N' ->
    Σ (M —↠ N') (λ M↠N' ->
      (N ≡ `suc N') × (len M↠N' ≡ len sucM↠N)))
suc-↠-inv (`suc M ∎) = ⟨ M , ⟨ M ∎ , ⟨ refl , refl ⟩ ⟩ ⟩
suc-↠-inv (`suc M —→⟨ ξ-suc M→M₁ ⟩ sucM₁↠N)
  with suc-↠-inv sucM₁↠N
suc-↠-inv (`suc M —→⟨ ξ-suc M→M₁ ⟩ sucM₁↠N)
  | ⟨ N' , ⟨ M₁↠N' , ⟨ N≡sucN' , lenM₁↠N'≡lenSucM₁↠N ⟩ ⟩ ⟩ =
    ⟨ N' , ⟨ M —→⟨ M→M₁ ⟩ M₁↠N' ,
      ⟨ N≡sucN' , cong sucℕ lenM₁↠N'≡lenSucM₁↠N ⟩ ⟩ ⟩

irred-case-L : ∀ {L M N} -> irred (case_[zero⇒_|suc⇒_] L M N) -> irred L
irred-case-L {M = M} {N = N} irrCase =
  λ { ⟨ L' , L→L' ⟩ -> irrCase ⟨ case_[zero⇒_|suc⇒_] L' M N , ξ-case L→L' ⟩ }

irred-case-len : ∀ {L M N R}
  -> (j : ℕ)
  -> (case↠R : case_[zero⇒_|suc⇒_] L M N —↠ R)
  -> len case↠R ≡ j
  -> irred R
  -> ∃[ L' ] (Σ (L —↠ L') λ L↠L' ->
       irred L' × Σ (case_[zero⇒_|suc⇒_] L' M N —↠ R) λ caseL'↠R ->
       len L↠L' + len caseL'↠R ≡ j)
irred-case-len zeroℕ (case_[zero⇒_|suc⇒_] L M N ∎) refl irrR =
  ⟨ L , ⟨ L ∎ , ⟨ irred-case-L irrR , ⟨ case_[zero⇒_|suc⇒_] L M N ∎ , refl ⟩ ⟩ ⟩ ⟩
irred-case-len (sucℕ j) (case_[zero⇒_|suc⇒_] L M N —→⟨ ξ-case L→L₁ ⟩ caseL₁↠R) len≡ irrR
  with irred-case-len j caseL₁↠R (suc-injective len≡) irrR
... | ⟨ L' , ⟨ L₁↠L' , ⟨ irrL' , ⟨ caseL'↠R , len+≡ ⟩ ⟩ ⟩ ⟩ =
  ⟨ L' , ⟨ L —→⟨ L→L₁ ⟩ L₁↠L' , ⟨ irrL' , ⟨ caseL'↠R , cong sucℕ len+≡ ⟩ ⟩ ⟩ ⟩
irred-case-len (sucℕ j) case0↠R@(case_[zero⇒_|suc⇒_] `zero M N —→⟨ β-zero ⟩ M↠R) len≡ irrR =
  ⟨ `zero , ⟨ `zero ∎ , ⟨ irred-value `zero , ⟨ case0↠R , len≡ ⟩ ⟩ ⟩ ⟩
irred-case-len (sucℕ j) caseS↠R@(case_[zero⇒_|suc⇒_] (`suc V) M N —→⟨ β-suc vV ⟩ NV↠R) len≡ irrR =
  ⟨ `suc V , ⟨ (`suc V) ∎ , ⟨ irred-value (`suc vV) , ⟨ caseS↠R , len≡ ⟩ ⟩ ⟩ ⟩

apply-𝓥 : ∀ {A B W V}
  -> (k : ℕ)
  -> 𝓥 (A ⇒ B) W k
  -> 𝓥 A V k
  -> ℰ B (W · V) k
apply-𝓥 zeroℕ 𝓥ABWk 𝓥AVk j () N WV↠N len≡ irrN
apply-𝓥 {A} {B} {` i} {V} (sucℕ k) () 𝓥AVk j j<k N WV↠N len≡ irrN
apply-𝓥 {A} {B} {ƛ C ⇒ M} {V} (sucℕ k) 𝓥fun 𝓥AVk j j<k N WV↠N len≡ irrN
  with WV↠N
... | _ ∎ = ⊥-elim (irrN ⟨ M [ V ] , β-ƛ (𝓥-value {A = A} 𝓥AVk) ⟩)
... | _ —→⟨ ξ-·₁ () ⟩ _
... | _ —→⟨ ξ-·₂ ⟨ _ , V→V' ⟩ ⟩ _ =
  ⊥-elim (value-¬→ (𝓥-value {A = A} 𝓥AVk) V→V')
... | _ —→⟨ β-ƛ vV ⟩ MV↠N =
  substEq (λ q -> Σ Term (λ W' -> (N ≡ W') × 𝓥 B W' q))
          (m∸[n∸o]≡m+o∸n k j 1 1≤j)
          (𝓔BMVk (j ∸ 1) (j≤k⇒j∸1<k j k 1≤j j<k) N MV↠N lenMV↠N≡ irrN)
  where
    1≤j : 1 ≤ j
    1≤j = substEq (λ n -> 1 ≤ n) len≡ (s≤s z≤n)

    lenMV↠N≡ : len MV↠N ≡ j ∸ 1
    lenMV↠N≡ = 1+m≡o⇒m≡o∸1 (len MV↠N) j len≡

    𝓔BMVk : ℰ B (M [ V ]) k
    𝓔BMVk = 𝓥fun k (s≤s ≤-refl) V (𝓥-monotone A V k 𝓥AVk)
apply-𝓥 {A} {B} {L · M} {V} (sucℕ k) () 𝓥AVk j j<k N WV↠N len≡ irrN
apply-𝓥 {A} {B} {`zero} {V} (sucℕ k) () 𝓥AVk j j<k N WV↠N len≡ irrN
apply-𝓥 {A} {B} {`suc W} {V} (sucℕ k) () 𝓥AVk j j<k N WV↠N len≡ irrN
apply-𝓥 {A} {B} {case_[zero⇒_|suc⇒_] L M N₁} {V} (sucℕ k) () 𝓥AVk j j<k N WV↠N len≡ irrN
apply-𝓥 {A} {B} {μ C ⇒ M} {V} (sucℕ k) 𝓥ABWk 𝓥AVk j j<k N WV↠N len≡ irrN
  with WV↠N
... | _ ∎ = ⊥-elim (irrN ⟨ (M [ μ C ⇒ M ]) · V , β-μ (𝓥-value {A = A} 𝓥AVk) ⟩)
... | _ —→⟨ ξ-·₁ () ⟩ _
... | _ —→⟨ ξ-·₂ ⟨ _ , V→V' ⟩ ⟩ _ =
  ⊥-elim (value-¬→ (𝓥-value {A = A} 𝓥AVk) V→V')
... | _ —→⟨ β-μ vV ⟩ MV↠N =
  substEq (λ q -> Σ Term (λ W' -> (N ≡ W') × 𝓥 B W' q))
          (m∸[n∸o]≡m+o∸n k j 1 1≤j)
          (𝓔BMVk (j ∸ 1) (j≤k⇒j∸1<k j k 1≤j j<k) N MV↠N lenMV↠N≡ irrN)
  where
    1≤j : 1 ≤ j
    1≤j = substEq (λ n -> 1 ≤ n) len≡ (s≤s z≤n)

    lenMV↠N≡ : len MV↠N ≡ j ∸ 1
    lenMV↠N≡ = 1+m≡o⇒m≡o∸1 (len MV↠N) j len≡

    𝓔BMVk : ℰ B ((M [ μ C ⇒ M ]) · V) k
    𝓔BMVk = apply-𝓥 k 𝓥ABWk (𝓥-monotone A V k 𝓥AVk)

safe : Term -> Set
safe M = ∀ N -> (M —↠ N) -> Value N ⊎ ∃[ N' ] (N —→ N')

infix 4 _⊨_⦂_
_⊨_⦂_ : Ctx -> Term -> Ty -> Set
Γ ⊨ M ⦂ A = ∀ k (σ : Subst) -> 𝓖 Γ σ k -> ℰ A (subst σ M) k

infix 4 _⊨ⱽ_⦂_
_⊨ⱽ_⦂_ : Ctx -> Term -> Ty -> Set
Γ ⊨ⱽ V ⦂ A = ∀ k (σ : Subst) -> 𝓖 Γ σ k -> 𝓥 A (subst σ V) k

safety : ∀ M A -> [] ⊨ M ⦂ A -> safe M
safety M A sem N M↠N with reducible? N
... | yes N→N' = inj₂ N→N'
... | no irrN with substEq (λ X -> X —↠ N) (sym (subst_id M)) M↠N
... | M₀↠N with sem (sucℕ (len M₀↠N)) `_ tt (len M₀↠N) ≤-refl N M₀↠N refl irrN
... | ⟨ W , ⟨ N≡W , 𝓥AW ⟩ ⟩ rewrite N≡W = inj₁ (𝓥-value {A = A} 𝓥AW)

compatible-μ : ∀ {Γ A B N}
  -> ((A ⇒ B) ∷ Γ) ⊨ⱽ N ⦂ (A ⇒ B)
  -> Γ ⊨ⱽ (μ (A ⇒ B) ⇒ N) ⦂ (A ⇒ B)
compatible-μ {Γ} {A} {B} {N} semN zeroℕ σ 𝓖Γσ0 = tt
compatible-μ {Γ} {A} {B} {N} semN (sucℕ k) σ 𝓖Γσk =
  substEq (λ M -> 𝓥 (A ⇒ B) M k) (sym eq-unfold) body-in-𝓥
  where
    𝓖Γσk' : 𝓖 Γ σ k
    𝓖Γσk' = 𝓖-monotone Γ σ k 𝓖Γσk

    μσN : Term
    μσN = subst σ (μ (A ⇒ B) ⇒ N)

    head-in-𝓥 : 𝓥 (A ⇒ B) μσN k
    head-in-𝓥 =
      compatible-μ {Γ = Γ} {A = A} {B = B} {N = N} semN k σ 𝓖Γσk'

    ext-env : 𝓖 ((A ⇒ B) ∷ Γ) (consSub σ μσN) k
    ext-env = ⟨ 𝓖Γσk' , head-in-𝓥 ⟩

    body-in-𝓥 : 𝓥 (A ⇒ B) (subst (consSub σ μσN) N) k
    body-in-𝓥 = semN k (consSub σ μσN) ext-env

    eq-unfold :
      (subst (exts σ) N) [ μσN ] ≡
      subst (consSub σ μσN) N
    eq-unfold = exts_sub_cons {σ = σ} {N = N} {V = μσN}

compatible-var : ∀ {Γ i A}
  -> Γ ∋ i ⦂ A
  -> Γ ⊨ ` i ⦂ A
compatible-var {Γ} {i} {A} i∋A k σ 𝓖Γσk j j<k N σi↠N len≡ irrN
  with lemma-𝓖 Γ σ k 𝓖Γσk i∋A
... | 𝓥Aσi with σi↠N
... | .(σ i) ∎ rewrite sym len≡ = ⟨ σ i , ⟨ refl , 𝓥Aσi ⟩ ⟩
... | .(σ i) —→⟨ σi→N' ⟩ _ =
  ⊥-elim (value-¬→ (𝓥-value {A = A} 𝓥Aσi) σi→N')

compatible-lam : ∀ {Γ A B N}
  -> ((A ∷ Γ) ⊨ N ⦂ B)
  -> Γ ⊨ⱽ (ƛ A ⇒ N) ⦂ (A ⇒ B)
compatible-lam {Γ} {A} {B} {N} semN k σ 𝓖Γσk =
  λ j j<k V 𝓥AVj ->
    let 𝓖Γσj : 𝓖 Γ σ j
        𝓖Γσj = 𝓖-<-monotone Γ σ k j 𝓖Γσk j<k
    in
    substEq (λ T -> ℰ B T j)
            (sym (exts_sub_cons {σ = σ} {N = N} {V = V}))
            (semN j (consSub σ V) ⟨ 𝓖Γσj , 𝓥AVj ⟩)

compatible-val : ∀ {Γ V A}
  -> Γ ⊨ⱽ V ⦂ A
  -> Γ ⊨ V ⦂ A
compatible-val {Γ} {V} {A} semV k σ 𝓖Γσk j j<k N Vσ↠N len≡ irrN
  with semV k σ 𝓖Γσk
... | 𝓥AVσ with Vσ↠N
... | .(subst σ V) ∎ rewrite sym len≡ = ⟨ subst σ V , ⟨ refl , 𝓥AVσ ⟩ ⟩
... | .(subst σ V) —→⟨ Vσ→N' ⟩ _ =
  ⊥-elim (value-¬→ (𝓥-value {A = A} 𝓥AVσ) Vσ→N')

compatible-app : ∀ {Γ L M A B}
  -> Γ ⊨ L ⦂ (A ⇒ B)
  -> Γ ⊨ M ⦂ A
  -> Γ ⊨ (L · M) ⦂ B
compatible-app semL semM zeroℕ σ 𝓖Γσk j () N LM↠N len≡ irrN
compatible-app {Γ} {L} {M} {A} {B} semL semM (sucℕ k) σ 𝓖Γσk j j<k N LM↠N len≡ irrN
  with irred-app-len-1 j LM↠N len≡ irrN
... | ⟨ L' , ⟨ L↠L' , ⟨ irrL' , ⟨ L'M↠N , len+≡ ⟩ ⟩ ⟩ ⟩
  with semL (sucℕ k) σ 𝓖Γσk (len L↠L') lenL<k L' L↠L' refl irrL'
  where
    lenL≤j : len L↠L' ≤ j
    lenL≤j =
      substEq (λ n -> len L↠L' ≤ n)
              len+≡
              (m≤m+n (len L↠L') (len L'M↠N))

    lenL<k : len L↠L' < sucℕ k
    lenL<k = ≤-trans (s≤s lenL≤j) j<k
... | ⟨ W , ⟨ L'≡W , 𝓥W[k∸lenL] ⟩ ⟩ rewrite L'≡W
  with irred-app-len-2 (𝓥-value {A = A ⇒ B} 𝓥W[k∸lenL]) (len L'M↠N) L'M↠N refl irrN
... | ⟨ M' , ⟨ M↠M' , ⟨ irrM' , ⟨ WM'↠N , len+≡₁ ⟩ ⟩ ⟩ ⟩
  with semM (sucℕ k) σ 𝓖Γσk (len M↠M') lenM<k M' M↠M' refl irrM'
  where
    lenM<k : len M↠M' < sucℕ k
    lenM<k = s≤s (≤-trans (lemma-+≤ len+≡₁ len+≡) (≤-pred j<k))
... | ⟨ V , ⟨ M'≡V , 𝓥Vk+1 ⟩ ⟩ rewrite M'≡V with W | WM'↠N
... | ` i | _ = ⊥-elim 𝓥W[k∸lenL]
... | ƛ C ⇒ MM | _ ∎ =
  ⊥-elim (irrN ⟨ MM [ V ] , β-ƛ (𝓥-value {A = A} 𝓥Vk+1) ⟩)
... | ƛ C ⇒ MM | _ —→⟨ ξ-·₁ () ⟩ _
... | ƛ C ⇒ MM | _ —→⟨ ξ-·₂ ⟨ _ , V→V' ⟩ ⟩ _ =
  ⊥-elim (value-¬→ (𝓥-value {A = A} 𝓥Vk+1) V→V')
... | ƛ C ⇒ MM | _ —→⟨ β-ƛ vV ⟩ MM[x:=V]↠N =
  substEq (λ jjj -> Σ Term (λ W₁ -> (N ≡ W₁) × 𝓥 B W₁ jjj))
          ≡k+1∸j
          (𝓔BMM (j ∸ 1 ∸ len L↠L' ∸ len M↠M')
                j∸1∸lLL'∸lMM'<k∸lLL'∸lMM'
                N
                MM[x:=V]↠N
                len++≡j∸1
                irrN)
  where
    1≤lL'MN : 1 ≤ len L'M↠N
    1≤lL'MN =
      ≤-trans (≤-trans (s≤s z≤n)
                      (m≤n+m (sucℕ (len MM[x:=V]↠N)) (len M↠M')))
              (m≡n→m≤n len+≡₁)

    1≤j : 1 ≤ j
    1≤j =
      ≤-trans 1≤lL'MN
              (≤-trans (m≤n+m (len L'M↠N) (len L↠L'))
                        (m≡n→m≤n len+≡))

    len++≡ : len L↠L' + (len M↠M' + sucℕ (len MM[x:=V]↠N)) ≡ j
    len++≡ = trans (cong (len L↠L' +_) len+≡₁) len+≡

    len++≡₂ : sucℕ (len L↠L' + (len M↠M' + len MM[x:=V]↠N)) ≡ j
    len++≡₂ =
      trans (trans (sym (+-suc (len L↠L') (len M↠M' + len MM[x:=V]↠N)))
                   (cong (len L↠L' +_) (sym (+-suc (len M↠M') (len MM[x:=V]↠N)))))
            len++≡

    len++≡₃ : sucℕ (len L↠L' + len M↠M') + len MM[x:=V]↠N ≡ j
    len++≡₃ =
      trans (cong sucℕ (+-assoc (len L↠L') (len M↠M') (len MM[x:=V]↠N))) len++≡₂

    len++≡a : (len L↠L' + len M↠M') + len MM[x:=V]↠N ≡ j ∸ 1
    len++≡a =
      1+m≡o⇒m≡o∸1 (len L↠L' + len M↠M' + len MM[x:=V]↠N) j len++≡₃

    len++≡b : len MM[x:=V]↠N ≡ j ∸ 1 ∸ (len L↠L' + len M↠M')
    len++≡b =
      k+m≡o⇒m≡o∸k (len L↠L' + len M↠M') (len MM[x:=V]↠N) (j ∸ 1) len++≡a

    len++≡j∸1 : len MM[x:=V]↠N ≡ j ∸ 1 ∸ len L↠L' ∸ len M↠M'
    len++≡j∸1 = trans len++≡b (sym (∸-+-assoc (j ∸ 1) (len L↠L') (len M↠M')))

    lLL'+lMM'≤j∸1 : len L↠L' + len M↠M' ≤ j ∸ 1
    lLL'+lMM'≤j∸1 =
      1+m≤o⇒m≤o∸1 (len L↠L' + len M↠M') j
                 (m+n≤o⇒m≤o (sucℕ (len L↠L' + len M↠M'))
                            (m≡n→m≤n len++≡₃))

    j∸1∸lLL'∸lMM'<k∸lLL'∸lMM' :
      (j ∸ 1 ∸ len L↠L' ∸ len M↠M') < (k ∸ len L↠L' ∸ len M↠M')
    j∸1∸lLL'∸lMM'<k∸lLL'∸lMM'
      rewrite ∸-+-assoc (j ∸ 1) (len L↠L') (len M↠M')
            | ∸-+-assoc k (len L↠L') (len M↠M') =
        j∸m<k∸m (j ∸ 1) k (len L↠L' + len M↠M')
               lLL'+lMM'≤j∸1
               (j≤k⇒j∸1<k j k 1≤j j<k)

    ≡k+1∸j :
      (k ∸ len L↠L' ∸ len M↠M' ∸ (j ∸ 1 ∸ len L↠L' ∸ len M↠M')) ≡ sucℕ k ∸ j
    ≡k+1∸j =
      trans (cong (_∸ (j ∸ 1 ∸ len L↠L' ∸ len M↠M'))
                  (∸-+-assoc k (len L↠L') (len M↠M')))
            (trans (cong (k ∸ (len L↠L' + len M↠M') ∸_)
                         (∸-+-assoc (j ∸ 1) (len L↠L') (len M↠M')))
                   (trans (ax∸bx k (j ∸ 1) (len L↠L' + len M↠M') lLL'+lMM'≤j∸1)
                          (m∸[n∸o]≡m+o∸n k j 1 1≤j)))

    suc[k∸lLL'∸lMM']≤suck∸lLL' :
      sucℕ (k ∸ len L↠L' ∸ len M↠M') ≤ sucℕ k ∸ len L↠L'
    suc[k∸lLL'∸lMM']≤suck∸lLL' =
      ≤-trans (m≡n→m≤n (cong sucℕ (∸-+-assoc k (len L↠L') (len M↠M'))))
              (≤-trans (m≡n→m≤n
                (sym (+-∸-assoc 1 (≤-trans lLL'+lMM'≤j∸1
                                           (<⇒≤ (j≤k⇒j∸1<k j k 1≤j j<k))))))
                (m∸a+b≤m∸a (sucℕ k) (len L↠L') (len M↠M')))

    𝓥AV' : 𝓥 A V (sucℕ k ∸ len L↠L' ∸ len M↠M')
    𝓥AV' =
      substEq (𝓥 A V)
              (trans (∸-+-assoc (sucℕ k) (len M↠M') (len L↠L'))
                     (trans (cong (sucℕ k ∸_) (+-comm (len M↠M') (len L↠L')))
                            (sym (∸-+-assoc (sucℕ k) (len L↠L') (len M↠M')))))
              (𝓥-monotone* A V (sucℕ k ∸ len M↠M') 𝓥Vk+1 (len L↠L')
                (m+n≤o⇒m≤o∸n (len L↠L') {n = len M↠M'} {o = sucℕ k}
                  (≤-trans (lemma-+≤₂ len+≡₁ len+≡) (≤-step (≤-pred j<k)))))

    𝓔BMM : ℰ B (MM [ V ]) (((sucℕ k ∸ 1) ∸ len L↠L') ∸ len M↠M')
    𝓔BMM =
      𝓥W[k∸lenL] (((sucℕ k ∸ 1) ∸ len L↠L') ∸ len M↠M')
                  suc[k∸lLL'∸lMM']≤suck∸lLL'
                  V
                  (𝓥-monotone A V (sucℕ k ∸ 1 ∸ len L↠L' ∸ len M↠M')
                    (substEq (𝓥 A V)
                      (trans (∸-+-assoc (sucℕ k) (len L↠L') (len M↠M'))
                             (trans (+-∸-assoc 1
                                      (≤-trans (lemma-+≤₂ len+≡₁ len+≡) (≤-pred j<k)))
                                    (cong sucℕ (sym (∸-+-assoc k (len L↠L') (len M↠M'))))))
                      𝓥AV'))
... | L₁ · M₁ | _ = ⊥-elim 𝓥W[k∸lenL]
... | `zero | _ = ⊥-elim 𝓥W[k∸lenL]
... | `suc W₁ | _ = ⊥-elim 𝓥W[k∸lenL]
... | case_[zero⇒_|suc⇒_] L₁ M₁ N₁ | _ = ⊥-elim 𝓥W[k∸lenL]
... | μ C ⇒ WW | WM'↠N =
  substEq (λ q -> Σ Term (λ W' -> (N ≡ W') × 𝓥 B W' q))
          eq-final
          (𝓔BWW (len WM'↠N) lenWM<idx N WM'↠N refl irrN)
  where
    lenLM≤j : len L↠L' + len M↠M' ≤ j
    lenLM≤j = lemma-+≤₂ len+≡₁ len+≡

    lenM≤suck∸lenL : len M↠M' ≤ sucℕ k ∸ len L↠L'
    lenM≤suck∸lenL =
      m+n≤o⇒m≤o∸n (len M↠M') {n = len L↠L'} {o = sucℕ k}
        (substEq (_≤ sucℕ k) (sym (+-comm (len M↠M') (len L↠L')))
          (≤-trans lenLM≤j (≤-step (≤-pred j<k))))

    𝓥W[idx] : 𝓥 (A ⇒ B) (μ C ⇒ WW) (sucℕ k ∸ len L↠L' ∸ len M↠M')
    𝓥W[idx] =
      𝓥-monotone* (A ⇒ B) (μ C ⇒ WW) (sucℕ k ∸ len L↠L') 𝓥W[k∸lenL]
                  (len M↠M') lenM≤suck∸lenL

    𝓥AVidx : 𝓥 A V (sucℕ k ∸ len L↠L' ∸ len M↠M')
    𝓥AVidx =
      substEq (𝓥 A V)
              (trans (∸-+-assoc (sucℕ k) (len M↠M') (len L↠L'))
                     (trans (cong (sucℕ k ∸_) (+-comm (len M↠M') (len L↠L')))
                            (sym (∸-+-assoc (sucℕ k) (len L↠L') (len M↠M')))))
              (𝓥-monotone* A V (sucℕ k ∸ len M↠M') 𝓥Vk+1 (len L↠L')
                (m+n≤o⇒m≤o∸n (len L↠L') {n = len M↠M'} {o = sucℕ k}
                  (≤-trans lenLM≤j (≤-step (≤-pred j<k)))))

    𝓔BWW : ℰ B ((μ C ⇒ WW) · V) (sucℕ k ∸ len L↠L' ∸ len M↠M')
    𝓔BWW = apply-𝓥 (sucℕ k ∸ len L↠L' ∸ len M↠M') 𝓥W[idx] 𝓥AVidx

    lenWM≡L'MN∸M : len WM'↠N ≡ len L'M↠N ∸ len M↠M'
    lenWM≡L'MN∸M =
      k+m≡o⇒m≡o∸k (len M↠M') (len WM'↠N) (len L'M↠N) len+≡₁

    lenL'MN≡j∸L : len L'M↠N ≡ j ∸ len L↠L'
    lenL'MN≡j∸L =
      k+m≡o⇒m≡o∸k (len L↠L') (len L'M↠N) j len+≡

    lenWM≡j∸LM : len WM'↠N ≡ j ∸ (len L↠L' + len M↠M')
    lenWM≡j∸LM =
      trans lenWM≡L'MN∸M
            (trans (cong (_∸ len M↠M') lenL'MN≡j∸L)
                   (∸-+-assoc j (len L↠L') (len M↠M')))

    lenWM<idx : len WM'↠N < sucℕ k ∸ len L↠L' ∸ len M↠M'
    lenWM<idx =
      substEq (λ n -> len WM'↠N < n)
              (sym (∸-+-assoc (sucℕ k) (len L↠L') (len M↠M')))
              (substEq (λ n -> n < (sucℕ k ∸ (len L↠L' + len M↠M')))
                       (sym lenWM≡j∸LM)
                       (j∸m<k∸m j (sucℕ k) (len L↠L' + len M↠M')
                               lenLM≤j j<k))

    eq-final :
      (sucℕ k ∸ len L↠L' ∸ len M↠M') ∸ len WM'↠N ≡ sucℕ k ∸ j
    eq-final =
      trans (cong (_∸ len WM'↠N) (∸-+-assoc (sucℕ k) (len L↠L') (len M↠M')))
            (trans (cong (sucℕ k ∸ (len L↠L' + len M↠M') ∸_) lenWM≡j∸LM)
                   (ax∸bx (sucℕ k) j (len L↠L' + len M↠M') lenLM≤j))

compatible-zero : ∀ {Γ} -> Γ ⊨ⱽ `zero ⦂ nat
compatible-zero k σ 𝓖Γσk = tt

compatible-sucⱽ : ∀ {Γ V}
  -> Γ ⊨ⱽ V ⦂ nat
  -> Γ ⊨ⱽ (`suc V) ⦂ nat
compatible-sucⱽ semV k σ 𝓖Γσk = semV k σ 𝓖Γσk

compatible-suc : ∀ {Γ M}
  -> Γ ⊨ M ⦂ nat
  -> Γ ⊨ (`suc M) ⦂ nat
compatible-suc semM zeroℕ σ 𝓖Γσk j () N sucσM↠N len≡ irrN
compatible-suc {Γ} {M} semM (sucℕ k) σ 𝓖Γσk j j<k N sucσM↠N len≡ irrN
  with suc-↠-inv sucσM↠N
compatible-suc {Γ} {M} semM (sucℕ k) σ 𝓖Γσk j j<k N sucσM↠N len≡ irrN
  | ⟨ N' , ⟨ Mσ↠N' , ⟨ N≡sucN' , lenMσ↠N'≡lenSucσM↠N ⟩ ⟩ ⟩
  with semM (sucℕ k) σ 𝓖Γσk j j<k N' Mσ↠N'
            (trans lenMσ↠N'≡lenSucσM↠N len≡)
            (irred-suc-M (substEq irred N≡sucN' irrN))
compatible-suc {Γ} {M} semM (sucℕ k) σ 𝓖Γσk j j<k N sucσM↠N len≡ irrN
  | ⟨ N' , ⟨ Mσ↠N' , ⟨ N≡sucN' , lenMσ↠N'≡lenSucσM↠N ⟩ ⟩ ⟩
  | ⟨ W' , ⟨ N'≡W' , 𝓥natW' ⟩ ⟩ =
    ⟨ `suc W' , ⟨ trans N≡sucN' (cong `suc_ N'≡W') , 𝓥natW' ⟩ ⟩

compatible-case : ∀ {Γ L M N A}
  -> Γ ⊨ L ⦂ nat
  -> Γ ⊨ M ⦂ A
  -> (nat ∷ Γ) ⊨ N ⦂ A
  -> Γ ⊨ (case_[zero⇒_|suc⇒_] L M N) ⦂ A
compatible-case semL semM semN zeroℕ σ 𝓖Γσk j () R caseσ↠R len≡ irrR
compatible-case {Γ} {L} {M} {N} {A} semL semM semN (sucℕ k) σ 𝓖Γσk j j<k R caseσ↠R len≡ irrR
  with irred-case-len j caseσ↠R len≡ irrR
... | ⟨ L' , ⟨ L↠L' , ⟨ irrL' , ⟨ caseL'↠R , len+≡ ⟩ ⟩ ⟩ ⟩
  with semL (sucℕ k) σ 𝓖Γσk (len L↠L') lenL<k L' L↠L' refl irrL'
  where
    lenL≤j : len L↠L' ≤ j
    lenL≤j = substEq (λ n -> len L↠L' ≤ n) len+≡ (m≤m+n (len L↠L') (len caseL'↠R))

    lenL<k : len L↠L' < sucℕ k
    lenL<k = ≤-trans (s≤s lenL≤j) j<k
... | ⟨ ` i , ⟨ refl , () ⟩ ⟩
... | ⟨ ƛ B ⇒ V , ⟨ refl , () ⟩ ⟩
... | ⟨ L₁ · M₁ , ⟨ refl , () ⟩ ⟩
... | ⟨ `zero , ⟨ refl , 𝓥zero ⟩ ⟩ with caseL'↠R
... | _ ∎ = ⊥-elim (irrR ⟨ subst σ M , β-zero ⟩)
... | _ —→⟨ ξ-case () ⟩ _
... | _ —→⟨ β-zero ⟩ Mσ↠R
  =
  let
    lenM≤j : len Mσ↠R ≤ j
    lenM≤j =
      substEq (λ n -> len Mσ↠R ≤ n) len+≡
        (≤-trans (m≤n+m (len Mσ↠R) 1)
                 (m≤n+m (sucℕ (len Mσ↠R)) (len L↠L')))

    lenM<k : len Mσ↠R < sucℕ k
    lenM<k = ≤-trans (s≤s lenM≤j) j<k

    ⟨ W , ⟨ R≡W , 𝓥AWidx ⟩ ⟩ = semM (sucℕ k) σ 𝓖Γσk (len Mσ↠R) lenM<k R Mσ↠R refl irrR

    target≤source : sucℕ k ∸ j ≤ sucℕ k ∸ len Mσ↠R
    target≤source = ∸-monoʳ-≤ (sucℕ k) lenM≤j
  in
  ⟨ W , ⟨ R≡W , 𝓥-≤-monotone A W (sucℕ k ∸ len Mσ↠R) (sucℕ k ∸ j) 𝓥AWidx target≤source ⟩ ⟩
compatible-case {Γ} {L} {M} {N} {A} semL semM semN (sucℕ k) σ 𝓖Γσk j j<k R caseσ↠R len≡ irrR
  | ⟨ L' , ⟨ L↠L' , ⟨ irrL' , ⟨ caseL'↠R , len+≡ ⟩ ⟩ ⟩ ⟩
  | ⟨ `suc V , ⟨ refl , 𝓥natVidxL ⟩ ⟩ with caseL'↠R
... | _ ∎ = ⊥-elim (irrR ⟨ (subst (exts σ) N) [ V ] , β-suc (𝓥-value {A = nat} 𝓥natVidxL) ⟩)
... | _ —→⟨ ξ-case (ξ-suc V→V') ⟩ _ =
  ⊥-elim (value-¬→ (𝓥-value {A = nat} 𝓥natVidxL) V→V')
... | _ —→⟨ β-suc vV ⟩ NσV↠R
  with (let lenL≤j : len L↠L' ≤ j
            lenL≤j = substEq (λ n -> len L↠L' ≤ n) len+≡ (m≤m+n (len L↠L') (sucℕ (len NσV↠R)))

            lenL≤suc-k : len L↠L' ≤ sucℕ k
            lenL≤suc-k = ≤-trans lenL≤j (<⇒≤ j<k)

            ext-env : 𝓖 (nat ∷ Γ) (consSub σ V) (sucℕ k ∸ len L↠L')
            ext-env = ⟨ 𝓖-monotone* Γ σ (sucℕ k) 𝓖Γσk (len L↠L') lenL≤suc-k , 𝓥natVidxL ⟩
        in
        substEq (λ T -> ℰ A T (sucℕ k ∸ len L↠L'))
                (sym (exts_sub_cons {σ = σ} {N = N} {V = V}))
                (semN (sucℕ k ∸ len L↠L') (consSub σ V) ext-env))
... | 𝓔ANσV
  with 𝓔ANσV (len NσV↠R)
              (let lenL≤j : len L↠L' ≤ j
                   lenL≤j = substEq (λ n -> len L↠L' ≤ n) len+≡ (m≤m+n (len L↠L') (sucℕ (len NσV↠R)))

                   lenCaseEq : j ∸ len L↠L' ≡ sucℕ (len NσV↠R)
                   lenCaseEq = sym (k+m≡o⇒m≡o∸k (len L↠L') (sucℕ (len NσV↠R)) j len+≡)

                   sucLenNσV<idxL : sucℕ (len NσV↠R) < sucℕ k ∸ len L↠L'
                   sucLenNσV<idxL = substEq (λ n -> n < (sucℕ k ∸ len L↠L')) lenCaseEq
                                            (j∸m<k∸m j (sucℕ k) (len L↠L') lenL≤j j<k)
               in
               ≤-trans (≤-step ≤-refl) sucLenNσV<idxL)
              R NσV↠R refl irrR
... | ⟨ W , ⟨ R≡W , 𝓥AWsource ⟩ ⟩ =
  ⟨ W , ⟨ R≡W , 𝓥-≤-monotone A W source target 𝓥AWsource target≤source ⟩ ⟩
  where
    lenL≤j : len L↠L' ≤ j
    lenL≤j = substEq (λ n -> len L↠L' ≤ n) len+≡ (m≤m+n (len L↠L') (sucℕ (len NσV↠R)))

    lenL≤suc-k : len L↠L' ≤ sucℕ k
    lenL≤suc-k = ≤-trans lenL≤j (<⇒≤ j<k)

    source : ℕ
    source = (sucℕ k ∸ len L↠L') ∸ len NσV↠R

    target : ℕ
    target = sucℕ k ∸ j

    eq-target : target ≡ (sucℕ k ∸ len L↠L') ∸ sucℕ (len NσV↠R)
    eq-target =
      trans (cong (sucℕ k ∸_) (sym len+≡))
            (sym (∸-+-assoc (sucℕ k) (len L↠L') (sucℕ (len NσV↠R))))

    target≤source : target ≤ source
    target≤source =
      substEq (λ n -> n ≤ source) (sym eq-target)
              (∸-monoʳ-≤ (sucℕ k ∸ len L↠L') (m≤n+m (len NσV↠R) 1))
compatible-case {Γ} {L} {M} {N} {A} semL semM semN (sucℕ k) σ 𝓖Γσk j j<k R caseσ↠R len≡ irrR
  | ⟨ L' , ⟨ L↠L' , ⟨ irrL' , ⟨ caseL'↠R , len+≡ ⟩ ⟩ ⟩ ⟩
  | ⟨ case_[zero⇒_|suc⇒_] L₁ M₁ N₁ , ⟨ refl , () ⟩ ⟩
compatible-case {Γ} {L} {M} {N} {A} semL semM semN (sucℕ k) σ 𝓖Γσk j j<k R caseσ↠R len≡ irrR
  | ⟨ L' , ⟨ L↠L' , ⟨ irrL' , ⟨ caseL'↠R , len+≡ ⟩ ⟩ ⟩ ⟩
  | ⟨ μ B ⇒ V , ⟨ refl , () ⟩ ⟩

mutual
  fundamental : ∀ {Γ M A}
    -> Γ ⊢ M ⦂ A
    -> Γ ⊨ M ⦂ A
  fundamental {Γ} {` i} {A} (⊢` {i = i} {A = A} i∋A) =
    compatible-var {Γ = Γ} {i = i} {A = A} i∋A
  fundamental {Γ} {ƛ A ⇒ N} {A ⇒ B} (⊢ƛ {A = A} {B = B} {N = N} ⊢N) =
    compatible-val {Γ = Γ} {V = ƛ A ⇒ N} {A = A ⇒ B}
      (fundamentalⱽ {Γ = Γ} {V = ƛ A ⇒ N} {A = A ⇒ B}
                   (⊢ƛ {A = A} {B = B} {N = N} ⊢N)
                   (ƛ A ⇒ N))
  fundamental {Γ} {L · M} {B} (⊢· {A = A} {B = B} {L = L} {M = M} ⊢L ⊢M) =
    compatible-app {Γ = Γ} {L = L} {M = M} {A = A} {B = B}
      (fundamental {Γ = Γ} {M = L} {A = A ⇒ B} ⊢L)
      (fundamental {Γ = Γ} {M = M} {A = A} ⊢M)
  fundamental {Γ} {`zero} {nat} ⊢zero =
    compatible-val {Γ = Γ} {V = `zero} {A = nat}
      (fundamentalⱽ {Γ = Γ} {V = `zero} {A = nat} ⊢zero `zero)
  fundamental {Γ} {`suc M} {nat} (⊢suc {M = M} ⊢M) =
    compatible-suc {Γ = Γ} {M = M}
      (fundamental {Γ = Γ} {M = M} {A = nat} ⊢M)
  fundamental {Γ} {case_[zero⇒_|suc⇒_] L M N} {A}
              (⊢case {A = A} {L = L} {M = M} {N = N} ⊢L ⊢M ⊢N) =
    compatible-case {Γ = Γ} {L = L} {M = M} {N = N} {A = A}
      (fundamental {Γ = Γ} {M = L} {A = nat} ⊢L)
      (fundamental {Γ = Γ} {M = M} {A = A} ⊢M)
      (fundamental {Γ = nat ∷ Γ} {M = N} {A = A} ⊢N)
  fundamental {Γ} {μ (A ⇒ B) ⇒ V} {A ⇒ B}
              (⊢μ {A = A} {B = B} {V = V} vV ⊢V) =
    compatible-val {Γ = Γ} {V = μ (A ⇒ B) ⇒ V} {A = A ⇒ B}
      (fundamentalⱽ {Γ = Γ} {V = μ (A ⇒ B) ⇒ V} {A = A ⇒ B}
                   (⊢μ {A = A} {B = B} {V = V} vV ⊢V)
                   (μ (A ⇒ B) ⇒ V))

  fundamentalⱽ : ∀ {Γ V A}
    -> Γ ⊢ V ⦂ A
    -> Value V
    -> Γ ⊨ⱽ V ⦂ A
  fundamentalⱽ {Γ} {` i} {A} (⊢` i∋A) ()
  fundamentalⱽ {Γ} {ƛ A ⇒ N} {A ⇒ B} (⊢ƛ {A = A} {B = B} {N = N} ⊢N) (ƛ .A ⇒ .N) =
    compatible-lam {Γ = Γ} {A = A} {B = B} {N = N}
      (fundamental {Γ = A ∷ Γ} {M = N} {A = B} ⊢N)
  fundamentalⱽ {Γ} {L · M} {A} (⊢· ⊢L ⊢M) ()
  fundamentalⱽ {Γ} {`zero} {nat} ⊢zero `zero = compatible-zero
  fundamentalⱽ {Γ} {`suc V} {nat} (⊢suc {M = V} ⊢V) (`suc vV) =
    compatible-sucⱽ {Γ = Γ} {V = V}
      (fundamentalⱽ {Γ = Γ} {V = V} {A = nat} ⊢V vV)
  fundamentalⱽ {Γ} {case_[zero⇒_|suc⇒_] L M N} {A} (⊢case ⊢L ⊢M ⊢N) ()
  fundamentalⱽ {Γ} {μ (A ⇒ B) ⇒ V} {A ⇒ B}
              (⊢μ {A = A} {B = B} {V = V} vV ⊢V) (μ .(A ⇒ B) ⇒ .V) =
    compatible-μ {Γ = Γ} {A = A} {B = B} {N = V}
      (fundamentalⱽ {Γ = (A ⇒ B) ∷ Γ} {V = V} {A = A ⇒ B} ⊢V vV)
