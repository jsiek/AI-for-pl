import extrinsic.Parametricity

namespace Extrinsic

def idR {A : Ty} (V : Term) : Rel A A :=
  fun V' W' _ _ => V = V' ∧ V = W'

axiom free_theorem_id :
  ∀ {A : Ty} (M V : Term),
    HasType 0 [] M (.all (.fn (.var 0) (.var 0))) →
    HasType 0 [] V A →
    Value V →
    (.app (.tapp M) V) —↠ V

def neg : Term :=
  .lam (.ite (.var 0) .tfalse .ttrue)

def flip : Term :=
  .lam (.natCase (.var 0) (.suc .zero) .zero)

def R : Rel .bool .nat :=
  fun V W _ _ =>
    (V = .ttrue ∧ W = .suc .zero) ∨
    (V = .tfalse ∧ W = .zero)

axiom neg_flip_related :
  VRel (.fn (.var 0) (.var 0)) (extendRelSub emptyRelSub .bool .nat R) neg flip Value.vLam Value.vLam

axiom free_theorem_rep :
  ∀ (M : Term),
    HasType 0 [] M (.all (.fn (.var 0) (.fn (.fn (.var 0) (.var 0)) (.var 0)))) →
    Σ V, Σ W, Σ (v : Value V), Σ (w : Value W),
      PProd ((.app (.app (.tapp M) .ttrue) neg) —↠ V)
        (PProd ((.app (.app (.tapp M) (.suc .zero)) flip) —↠ W)
          (R V W v w))

end Extrinsic
