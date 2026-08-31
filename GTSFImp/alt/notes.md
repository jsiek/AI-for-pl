Types (with variables as names)

  X,Y,Z ∈ TyVar
  A,B,C ::= X | ℕ | 𝔹 | A → B | ∀X.A

Terms (with variables as names)

  n ∈ ℕ
  b ∈ 𝔹
  x ∈ Var
  k ::= n | b
  L,M,N ::= x | k | λx:A. N | L · M | ΛX.N | L [A] | M ↑[X:=A] | M ↓[X:=A]

Values

  F ::= G | F ↓[X:=A]
  G ::= λx:A. N | ΛX.V | G ↑[X:=A]
  V,W ::= n | F | V ↓[X:=A]

Frames

  R ::= □ · M | V · □ | □ ↑[X:=A] | □ ↓[X:=A] | □ [A]

Reduction rules

(Beta)        (λx:A. N) · V     -→ N[x:=V]
(TyBeta)      (Λ X. V) [A]      -→ V ↑[X:=A]
(WrapReveal)  F ↑[X:=A] · W     -→ (F · W↓[X:=A]) ↑[X:=A]
(WrapConceal) F ↓[X:=A] · W     -→ (F · W↑[X:=A]) ↓[X:=A]
(TyWrapRevl)  F ↑[X:=A] [B]     -→ F [B] ↑[X:=A]
(TyWrapCncl)  F ↓[X:=A] [B]     -→ F [B[X:=A]] ↓[X:=A]

(Cancel)      V ↓[X:=A] ↑[X:=A] -→ V
(Drop)        V ↓[Y:=B] ↑[X:=A] -→ V ↓[Y:=B]  if X ≠ Y and X ∉ V↓[Y:=B]
(RevealCnst)  k ↑[X:=A]         -→ k

(ξ)           R[M]              -→ R[M′]      if M -→ M′


Example 1

                  (Λ Y. λy:Y. (ΛX.λx:X.y) [Y] ) [N] · 7 · 3
    → TyBeta      (λy:Y. (ΛX.λx:X.y) [Y] ) ↑[Y:=N] · 7 · 3
    → WrapReveal  ((λy:Y. (ΛX.λx:X.y) [Y] ) · 7↓[Y:=N]) ↑[Y:=N] · 3
    → Beta        (ΛX. λx:X. 7↓[Y:=N]) [Y] ↑[Y:=N] · 3
    → TyBeta      (λx:X. 7↓[Y:=N]) ↑[X:=Y] ↑[Y:=N] · 3
    → WrapReveal  ((λx:X. 7↓[Y:=N]) ↑[X:=Y] · 3↓[Y:=N]) ↑[Y:=N]
    → WrapReveal  ((λx:X. 7↓[Y:=N]) · 3↓[Y:=N]↓[X:=Y]) ↑[X:=Y] ↑[Y:=N]
    → Beta        7↓[Y:=N] ↑[X:=Y] ↑[Y:=N]
    → Drop        7↓[Y:=N] ↑[Y:=N]
    → Cancel      7


Example 2

                  (ΛX. λf:X→X. λy:X. f·y) [ℕ] · (λn:ℕ.n+1) · 7
    → TyBeta      (λf. λy. f·y) ↑[X:=ℕ] · (λn.n+1) · 7
    → WrapReveal  ((λf. λy. f·y) · (λn.n+1)↓[X:=ℕ]) ↑[X:=ℕ] · 7
    → Beta        (λy. (λn.n+1)↓[X:=ℕ] · y) ↑[X:=ℕ] · 7
    → WrapReveal  ((λy. (λn.n+1)↓[X:=ℕ] · y) · 7↓[X:=ℕ]) ↑[X:=ℕ]
    → Beta        ((λn.n+1)↓[X:=ℕ] · 7↓[X:=ℕ]) ↑[X:=ℕ]        -- sealed fn in head position
    → WrapConceal ((λn.n+1) · (7↓[X:=ℕ]↑[X:=ℕ])) ↓[X:=ℕ] ↑[X:=ℕ]
    → Cancel      ((λn.n+1) · 7) ↓[X:=ℕ] ↑[X:=ℕ]
    → Beta        8 ↓[X:=ℕ] ↑[X:=ℕ]
    → Cancel      8


Example 3   (type application to wrapped polymorphic values)

                  (ΛX. λf:(∀Z.Z→Z). f [X]) [𝔹] · ((ΛY. ΛZ. λz:Z. z) [ℕ])
    → TyBeta      (λf:(∀Z.Z→Z). f [X]) ↑[X:=𝔹] · ((ΛY. ΛZ. λz:Z. z) [ℕ])
    → TyBeta      (λf:(∀Z.Z→Z). f [X]) ↑[X:=𝔹] · (ΛZ. λz:Z. z) ↑[Y:=ℕ]
    → WrapReveal  ((λf. f [X]) · (ΛZ. λz:Z. z) ↑[Y:=ℕ] ↓[X:=𝔹]) ↑[X:=𝔹]
    → Beta        ((ΛZ. λz:Z. z) ↑[Y:=ℕ] ↓[X:=𝔹] [X]) ↑[X:=𝔹]
    → TyWrapCncl  ((ΛZ. λz:Z. z) ↑[Y:=ℕ] [𝔹]) ↓[X:=𝔹] ↑[X:=𝔹]        -- X[X:=𝔹] = 𝔹
    → TyWrapRevl  ((ΛZ. λz:Z. z) [𝔹]) ↑[Y:=ℕ] ↓[X:=𝔹] ↑[X:=𝔹]
    → TyBeta      (λz:Z. z) ↑[Z:=𝔹] ↑[Y:=ℕ] ↓[X:=𝔹] ↑[X:=𝔹]
    → Cancel      (λz:Z. z) ↑[Z:=𝔹] ↑[Y:=ℕ]


Example 4   (a constant escaping a reveal)

                  (ΛX. λx:X. 7) [ℕ] · 5
    → TyBeta      (λx:X. 7) ↑[X:=ℕ] · 5
    → WrapReveal  ((λx:X. 7) · 5↓[X:=ℕ]) ↑[X:=ℕ]
    → Beta        7 ↑[X:=ℕ]
    → RevealCnst  7
