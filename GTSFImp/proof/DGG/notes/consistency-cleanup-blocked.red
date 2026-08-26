Consistency cleanup blocked after flipping `_↦_`.

Command:

  env \
    agda -i GTSFImp -v0 GTSFImp/All.agda

Failure:

  GTSFImp/proof/ImprecisionConsistency.agda:423,17-20
  A′ != A₁ of type (Ty Δ)
  when checking that the expression A⊑L has type φ ⊢ A ⊑ A₁

Reason this is not mechanical plumbing:

  `consistent-common-lowerᵐ` currently states:

    LowerEnv μ φ ψ
    -> μ ⊢ A ∼ B
    -> ∃[ D ] φ ⊢ D ⊑ A × ψ ⊢ D ⊑ B

  After the requested constructor change, a function consistency proof

    c ↦ d : μ ⊢ (A ⇒ B) ∼ (A′ ⇒ B′)

  contains:

    c : μ ⊢ A′ ∼ A
    d : μ ⊢ B ∼ B′

  Recursing on `c` with the current theorem gives a domain lower bound in
  the order:

    φ ⊢ D ⊑ A′
    ψ ⊢ D ⊑ A

  But the lower bound needed for the whole function type is:

    φ ⊢ D ⊑ A
    ψ ⊢ D ⊑ A′

  Those are swapped.  This cannot be repaired by changing constructor
  argument order or by inserting `sym∼`; it requires a polarity-aware
  redesign of the environment/lower-bound theorem, or a different theorem
  statement.

Concrete open counterexample to the old env-indexed statement:

  Let Δ = 1, μ zero = X∼★, φ zero = X⊑X, and ψ zero = X⊑★.
  Then `LowerEnv μ φ ψ` holds by `var-to-star`.

  Let:

    c = id (＇ zero) !

  Then:

    c : μ ⊢ ＇ zero ∼ ★
    c ↦ id (‵ ι) : μ ⊢ (★ ⇒ ‵ ι) ∼ (＇ zero ⇒ ‵ ι)

  The old theorem would require some `D` with:

    φ ⊢ D ⊑ (★ ⇒ ‵ ι)
    ψ ⊢ D ⊑ (＇ zero ⇒ ‵ ι)

  Any arrow-shaped common lower would need a domain `E` such that:

    φ ⊢ E ⊑ ★
    ψ ⊢ E ⊑ ＇ zero

  The second judgment forces `E = ＇ zero`, but the first would then require
  `φ zero = X⊑★`, contradicting `φ zero = X⊑X`.

Work completed before the blocker:

  * Added `GTSFImp/FunExt.agda` with the centralized `funext` postulate.
  * Removed the private `funext` postulates from `Consistency.agda` and
    `proof/Imprecision.agda`.
  * Added `FunExt` to `All.agda`.
  * Flipped `_↦_` in `Consistency.agda` to the requested domain orientation.
  * Simplified `β-⇒` in `Reduction.agda` and updated the direct uses in
    `Eval.agda`, `proof/TypeSafety/Progress.agda`, and
    `proof/TypeSafety/Preservation.agda`.
  * Reoriented the first consistency example sites that became invalid in
    negative function-domain positions.

Continuation blocker after supervisor's mutual-swap direction:

  The proposed companion has the shape:

    consistent-common-lowerᵐ-swap :
      LowerEnv μ φ ψ
      -> μ ⊢ A ∼ B
      -> ∃[ D ] ψ ⊢ D ⊑ A × φ ⊢ D ⊑ B

  This is enough for the arrow-domain position if it exists: for
  `c : μ ⊢ A′ ∼ A`, the main arrow case can use the swapped result
  `ψ ⊢ Dc ⊑ A′` and `φ ⊢ Dc ⊑ A`.

  The companion itself cannot mirror the variable-ground `_!` case.  Let
  `Δ = 1`, `μ zero = X∼★`, `φ zero = X⊑X`, and `ψ zero = X⊑★`.
  Then `LowerEnv μ φ ψ` holds by `var-to-star`.

  Let:

    c = id (＇ zero)
    x-to-star = _! {G = ＇ zero} ⦃ Gᵍ = ＇ zero ⦄
      ⦃ G∼★ = X∼★ᵍ refl ⦄ c ⦃ nonstar-X ⦄

  Then:

    x-to-star : μ ⊢ ＇ zero ∼ ★

  The swapped companion would require some `D` with:

    ψ ⊢ D ⊑ ＇ zero
    φ ⊢ D ⊑ ★

  The first judgment forces the source to be exactly `＇ zero` up to the
  structural universal-instantiation cases, and each such case still needs an
  inner source that lowers to `＇ zero`.  The direct variable case leaves
  `D = ＇ zero`, and then the second judgment would require:

    φ zero = X⊑★

  But `LowerEnv μ φ ψ` gives `φ zero = X⊑X` for `μ zero = X∼★`.
  This is the side-specific helper obstruction: the existing
  `var-right-to-star` works on the `ψ` side because `var-to-star` gives
  `ψ zero = X⊑★`; the mirrored `_!` branch would need a `φ`-side
  helper for the same `X∼★` evidence, which contradicts `var-to-star`.

  I stopped here per the instruction:

    If the swap companion hits a case that genuinely cannot mirror: STOP with
    the case to a .red.
