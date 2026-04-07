namespace Intrinsic

set_option autoImplicit false

inductive TyCtx : Type where
  | empty : TyCtx
  | snoc : TyCtx → TyCtx
  deriving DecidableEq, Repr

notation "∅" => TyCtx.empty
notation:65 Δ " ,α" => TyCtx.snoc Δ

inductive TyVar : TyCtx → Type where
  | Z : {Δ : TyCtx} → TyVar (Δ ,α)
  | S : {Δ : TyCtx} → TyVar Δ → TyVar (Δ ,α)
  deriving DecidableEq, Repr

inductive Ty : TyCtx → Type where
  | var : {Δ : TyCtx} → TyVar Δ → Ty Δ
  | nat : {Δ : TyCtx} → Ty Δ
  | bool : {Δ : TyCtx} → Ty Δ
  | fn : {Δ : TyCtx} → Ty Δ → Ty Δ → Ty Δ
  | all : {Δ : TyCtx} → Ty (Δ ,α) → Ty Δ
  deriving DecidableEq, Repr

prefix:100 "#" => Ty.var
@[match_pattern] abbrev TNat {Δ : TyCtx} : Ty Δ := Ty.nat
@[match_pattern] abbrev TBool {Δ : TyCtx} : Ty Δ := Ty.bool
infixr:60 " ⇒ " => Ty.fn
prefix:80 "∀ₜ " => Ty.all

abbrev RenameT (Δ Δ' : TyCtx) : Type := TyVar Δ → TyVar Δ'
abbrev SubstT (Δ Δ' : TyCtx) : Type := TyVar Δ → Ty Δ'

abbrev idRenameT {Δ : TyCtx} : RenameT Δ Δ := fun x => x
abbrev idSubstT {Δ : TyCtx} : SubstT Δ Δ := fun x => #x

def extT {Δ Δ' : TyCtx} (ρ : RenameT Δ Δ') : RenameT (Δ ,α) (Δ' ,α)
  | .Z => .Z
  | .S x => .S (ρ x)

def renameT {Δ Δ' : TyCtx} (ρ : RenameT Δ Δ') : Ty Δ → Ty Δ'
  | .var x => .var (ρ x)
  | .nat => .nat
  | .bool => .bool
  | .fn A B => .fn (renameT ρ A) (renameT ρ B)
  | .all A => .all (renameT (extT ρ) A)

def extsT {Δ Δ' : TyCtx} (σ : SubstT Δ Δ') : SubstT (Δ ,α) (Δ' ,α)
  | .Z => #TyVar.Z
  | .S x => renameT TyVar.S (σ x)

def substT {Δ Δ' : TyCtx} (σ : SubstT Δ Δ') : Ty Δ → Ty Δ'
  | .var x => σ x
  | .nat => .nat
  | .bool => .bool
  | .fn A B => .fn (substT σ A) (substT σ B)
  | .all A => .all (substT (extsT σ) A)

def consSubT {Δ Δ' : TyCtx} (A : Ty Δ') (σ : SubstT Δ Δ') : SubstT (Δ ,α) Δ'
  | .Z => A
  | .S x => σ x

infixr:61 " •ₜ " => consSubT

def compSubT {Δ₁ Δ₂ Δ₃ : TyCtx} (σ : SubstT Δ₁ Δ₂) (τ : SubstT Δ₂ Δ₃) : SubstT Δ₁ Δ₃ :=
  fun x => substT τ (σ x)

infixr:67 " ⨟ᵗ " => compSubT

def singleTyEnv {Δ : TyCtx} (B : Ty Δ) : SubstT (Δ ,α) Δ := B •ₜ idSubstT

def substOneT {Δ : TyCtx} (A : Ty (Δ ,α)) (B : Ty Δ) : Ty Δ :=
  substT (singleTyEnv B) A

notation:67 A " [ " B " ]ₜ" => substOneT A B

theorem renameT_cong {Δ Δ' : TyCtx} {ρ ρ' : RenameT Δ Δ'}
    (h : ∀ x, ρ x = ρ' x) :
    ∀ A, renameT ρ A = renameT ρ' A
  | .var x => by simpa [renameT, h x]
  | .nat => rfl
  | .bool => rfl
  | .fn A B => by simp [renameT, renameT_cong h A, renameT_cong h B]
  | .all A => by
      refine congrArg Ty.all ?_
      apply renameT_cong
      intro x
      cases x with
      | Z => rfl
      | S y => simpa [extT] using congrArg TyVar.S (h y)

theorem substT_cong {Δ Δ' : TyCtx} {σ τ : SubstT Δ Δ'}
    (h : ∀ x, σ x = τ x) :
    ∀ A, substT σ A = substT τ A
  | .var x => h x
  | .nat => rfl
  | .bool => rfl
  | .fn A B => by simp [substT, substT_cong h A, substT_cong h B]
  | .all A => by
      refine congrArg Ty.all ?_
      apply substT_cong
      intro x
      cases x with
      | Z => rfl
      | S y => simpa [extsT] using congrArg (renameT TyVar.S) (h y)

theorem extT_comp {Δ₁ Δ₂ Δ₃ : TyCtx} (ρ₁ : RenameT Δ₁ Δ₂) (ρ₂ : RenameT Δ₂ Δ₃) :
    (fun x => extT ρ₂ (extT ρ₁ x)) = extT (fun x => ρ₂ (ρ₁ x)) := by
  funext x
  cases x <;> rfl

theorem renameT_comp {Δ₁ Δ₂ Δ₃ : TyCtx} (ρ₁ : RenameT Δ₁ Δ₂) (ρ₂ : RenameT Δ₂ Δ₃) :
    ∀ A, renameT ρ₂ (renameT ρ₁ A) = renameT (fun x => ρ₂ (ρ₁ x)) A
  | .var x => rfl
  | .nat => rfl
  | .bool => rfl
  | .fn A B => by simp [renameT, renameT_comp ρ₁ ρ₂ A, renameT_comp ρ₁ ρ₂ B]
  | .all A => by
      simp [renameT]
      rw [renameT_comp (extT ρ₁) (extT ρ₂) A, extT_comp ρ₁ ρ₂]

theorem extsT_extT {Δ₁ Δ₂ Δ₃ : TyCtx} (ρ : RenameT Δ₁ Δ₂) (σ : SubstT Δ₂ Δ₃) :
    (fun x => extsT σ (extT ρ x)) = extsT (fun y => σ (ρ y)) := by
  funext x
  cases x <;> rfl

theorem ren_subT {Δ₁ Δ₂ Δ₃ : TyCtx} (ρ : RenameT Δ₁ Δ₂) (σ : SubstT Δ₂ Δ₃) :
    ∀ A, substT σ (renameT ρ A) = substT (fun x => σ (ρ x)) A
  | .var x => rfl
  | .nat => rfl
  | .bool => rfl
  | .fn A B => by simp [renameT, substT, ren_subT ρ σ A, ren_subT ρ σ B]
  | .all A => by
      simp [renameT, substT]
      rw [ren_subT (extT ρ) (extsT σ) A, extsT_extT ρ σ]

theorem renameT_shift {Δ Δ' : TyCtx} (ρ : RenameT Δ Δ') :
    ∀ A, renameT (extT ρ) (renameT TyVar.S A) = renameT TyVar.S (renameT ρ A)
  | A => by
      calc
        renameT (extT ρ) (renameT TyVar.S A)
            = renameT (fun x => extT ρ (TyVar.S x)) A := by
                exact renameT_comp TyVar.S (extT ρ) A
        _ = renameT (fun x => TyVar.S (ρ x)) A := by
              apply renameT_cong
              intro x
              rfl
        _ = renameT TyVar.S (renameT ρ A) := by
              symm
              exact renameT_comp ρ TyVar.S A

theorem extT_extsT {Δ₁ Δ₂ Δ₃ : TyCtx} (ρ : RenameT Δ₂ Δ₃) (σ : SubstT Δ₁ Δ₂) :
    (fun x => renameT (extT ρ) (extsT σ x)) = extsT (fun y => renameT ρ (σ y)) := by
  funext x
  cases x with
  | Z => rfl
  | S y =>
      simpa [extsT] using renameT_shift ρ (σ y)

theorem sub_renT {Δ₁ Δ₂ Δ₃ : TyCtx} (ρ : RenameT Δ₂ Δ₃) (σ : SubstT Δ₁ Δ₂) :
    ∀ A, renameT ρ (substT σ A) = substT (fun x => renameT ρ (σ x)) A
  | .var x => rfl
  | .nat => rfl
  | .bool => rfl
  | .fn A B => by simp [renameT, substT, sub_renT ρ σ A, sub_renT ρ σ B]
  | .all A => by
      simp [renameT, substT]
      rw [sub_renT (extT ρ) (extsT σ) A]
      simpa using congrArg (fun env => substT env A) (extT_extsT ρ σ)

theorem extsT_substT {Δ₁ Δ₂ Δ₃ : TyCtx} (σ : SubstT Δ₁ Δ₂) (τ : SubstT Δ₂ Δ₃) :
    (fun x => substT (extsT τ) (extsT σ x)) = extsT (σ ⨟ᵗ τ) := by
  funext x
  cases x with
  | Z => rfl
  | S y =>
      calc
        substT (extsT τ) (extsT σ (TyVar.S y))
            = substT (extsT τ) (renameT TyVar.S (σ y)) := rfl
        _ = substT (fun a => extsT τ (TyVar.S a)) (σ y) := by
              exact ren_subT TyVar.S (extsT τ) (σ y)
        _ = substT (fun a => renameT TyVar.S (τ a)) (σ y) := by rfl
        _ = renameT TyVar.S (substT τ (σ y)) := by
              symm
              exact sub_renT TyVar.S τ (σ y)
        _ = extsT (σ ⨟ᵗ τ) (TyVar.S y) := rfl

theorem sub_subT {Δ₁ Δ₂ Δ₃ : TyCtx} (σ : SubstT Δ₁ Δ₂) (τ : SubstT Δ₂ Δ₃) :
    ∀ A, substT τ (substT σ A) = substT (σ ⨟ᵗ τ) A
  | .var x => rfl
  | .nat => rfl
  | .bool => rfl
  | .fn A B => by simp [substT, sub_subT σ τ A, sub_subT σ τ B]
  | .all A => by
      simp [substT]
      rw [sub_subT (extsT σ) (extsT τ) A]
      simpa using congrArg (fun env => substT env A) (extsT_substT σ τ)

theorem sub_idT {Δ : TyCtx} : ∀ (A : Ty Δ), substT idSubstT A = A
  | .var _ => rfl
  | .nat => rfl
  | .bool => rfl
  | .fn A B => by simp [substT, sub_idT A, sub_idT B]
  | .all A => by
      simp [substT]
      have h : extsT (idSubstT (Δ := Δ)) = (idSubstT (Δ := Δ ,α)) := by
        funext x
        cases x <;> rfl
      rw [h, sub_idT A]

theorem renameT_substOne {Δ Δ' : TyCtx} (ρ : RenameT Δ Δ') (A : Ty (Δ ,α)) (B : Ty Δ) :
    renameT ρ (A [ B ]ₜ) = (renameT (extT ρ) A) [ renameT ρ B ]ₜ := by
  dsimp [substOneT]
  rw [sub_renT ρ (singleTyEnv B), ren_subT (extT ρ) (singleTyEnv (renameT ρ B))]
  apply congrArg (fun env => substT env A)
  funext x
  cases x <;> rfl

theorem substT_substOne {Δ Δ' : TyCtx} (σ : SubstT Δ Δ') (A : Ty (Δ ,α)) (B : Ty Δ) :
    substT σ (A [ B ]ₜ) = (substT (extsT σ) A) [ substT σ B ]ₜ := by
  dsimp [substOneT]
  rw [sub_subT (singleTyEnv B) σ, sub_subT (extsT σ) (singleTyEnv (substT σ B))]
  apply congrArg (fun env => substT env A)
  funext x
  cases x with
  | Z => rfl
  | S y =>
      calc
        substT σ (singleTyEnv B (TyVar.S y)) = σ y := rfl
        _ = substT (singleTyEnv (substT σ B)) (renameT TyVar.S (σ y)) := by
              symm
              calc
                substT (singleTyEnv (substT σ B)) (renameT TyVar.S (σ y))
                    = substT (fun a => singleTyEnv (substT σ B) (TyVar.S a)) (σ y) := by
                        exact ren_subT TyVar.S (singleTyEnv (substT σ B)) (σ y)
                _ = substT idSubstT (σ y) := by rfl
                _ = σ y := sub_idT (σ y)

end Intrinsic
