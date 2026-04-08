import curry.TypeSafety

-- File Charter:
--   * Fuel-bounded evaluator for closed curry System F terms.
--   * Produces an explicit reduction trace using `progress` and `preservation`.
--   * Stops once a value is reached or when fuel runs out.

namespace Curry

structure EvalResult (M : Term) : Type where
  term : Term
  trace : M —↠ term
  value : Value term

noncomputable def eval {Δ : TyCtx} {M : Term} {A : Ty} :
    Nat → Δ ⊢ [] ⊢ M ⦂ A → Option (EvalResult M)
  | 0, hM =>
      match progress hM with
      | .done v => some ⟨M, .refl M, v⟩
      | .step _ => none
  | fuel + 1, hM =>
      match progress hM with
      | .done v => some ⟨M, .refl M, v⟩
      | .step s =>
          match eval fuel (preservation hM s) with
          | none => none
          | some r =>
              some ⟨r.term, .step M s r.trace, r.value⟩

end Curry
