M6 foundation blocker: `castSize-↑close-inst`

Date: 2026-08-11

Command used to validate the counterexample before deleting the scratch:

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
    GTSFImp/proof/DGG/Catchup/M6CounterexampleScratch.agda

Blocked statement:

  castSize-↑close-inst : ∀ {Δ} {ν : Env∼ Δ}
      {A : Ty (suc Δ)} {B : Ty Δ}
      {c : instᵐ ν ⊢ A ∼ ⇑ᵗ B}
    → castSize (↑ᶜ (close-instᶜ c)) ≡ castSize c

The statement is false without excluding `B = ★`.

Checked counterexample:

  ν₀ : Env∼ zero
  ν₀ ()

  bad-c : instᵐ ν₀ ⊢ ＇ Fin.zero ∼ ⇑ᵗ ★
  bad-c = _! ⦃ G∼★ = X∼★ᵍ refl ⦄ (id (＇ Fin.zero))

  bad-original : castSize bad-c ≡ suc (suc zero)
  bad-original = refl

  bad-closed : castSize (↑ᶜ (close-instᶜ bad-c)) ≡ suc zero
  bad-closed = refl

Thus the blocked theorem instance normalizes to:

  suc zero ≡ suc (suc zero)

The failure mechanism is that `close-instᶜ` substitutes the inst-bound
variable with `★`.  In this case the original tag-to-dynamic cast

  instᵐ ν₀ ⊢ ＇ zero ∼ ★

is represented as `_! (id (＇ zero))`, whose size is `2`; closing at `★`
collapses it to `id ★`, whose size is `1`.  The intended M6 allocation
decrease uses a `B ≢ ★` premise, but the support lemma as stated does not.
