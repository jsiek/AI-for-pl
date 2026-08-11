M6 foundation blocker: `inst-alloc-decrease`

Date: 2026-08-11

Blocked statement:

  inst-alloc-decrease : ∀ {Δ} {ν : Env∼ Δ}
      {A : Ty (suc Δ)} {B : Ty Δ}
      {c : instᵐ ν ⊢ A ∼ ⇑ᵗ B}
      ⦃ Anv : NonVar A ⦄ ⦃ z∈A : Fin.zero ∈ᵗ A ⦄
    → (B≢★ : B ≢ ★)
    → castSize (↑ᶜ (close-instᶜ c)) < castSize ((inst c) B≢★)

The scratch proof was:

  inst-alloc-decrease {c = c} B≢★
      rewrite castSize-↑close-inst {c = c} =
    n<1+n (castSize c)

That route is blocked because `castSize-↑close-inst` is false as stated
when `B = ★`; see
`m6-foundation-castSize-↑close-inst-blocked.red`.

The `B≢★` premise excludes the concrete counterexample recorded there, so
this decrease may still be provable from a restricted replacement lemma:

  B ≢ ★ →
  castSize (↑ᶜ (close-instᶜ c)) ≡ castSize c

or directly from a non-increasing close-inst size theorem.  Such a repair
would change the support surface relative to the scratch, so it was not
introduced in this foundation pass.
