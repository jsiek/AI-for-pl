import FullBetaReduction

namespace Progress

open Lambda

def progress (M : Term) : Normal M ⊕ Σ N, M —→ N :=
  match M with
  | .var _ =>
      Sum.inl (.neu .var)
  | .lam N =>
      match progress N with
      | Sum.inl hN => Sum.inl (.lam hN)
      | Sum.inr ⟨N', s⟩ => Sum.inr ⟨.lam N', .xi_lam s⟩
  | .app L R =>
      match progress L with
      | Sum.inr ⟨L', sL⟩ =>
          Sum.inr ⟨.app L' R, .xi_app1 sL⟩
      | Sum.inl hLNorm =>
          match progress R with
          | Sum.inr ⟨R', sR⟩ =>
              Sum.inr ⟨.app L R', .xi_app2 sR⟩
          | Sum.inl hRNorm =>
              match hLNorm with
              | .neu hLNeu =>
                  Sum.inl (.neu (.app hLNeu hRNorm))
              | .lam hNNorm =>
                  Sum.inr ⟨single_subst _ R, .β_lam⟩

end Progress
