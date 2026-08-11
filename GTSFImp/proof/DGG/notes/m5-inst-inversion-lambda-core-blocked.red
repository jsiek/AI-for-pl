M5 instantiation inversion blocker: Λ core `Λ⊑²`

Date: 2026-08-11

Blocked target:

  InstInversionPackage.Λ-package

The promoted package field asks the Λ branch to construct an
`InstPostCatalogPackage` from:

  rel : W ∣ γ ⊢² M ⊑ Λ V′ ∶ p
  Value M
  Value (Λ V′)
  c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′
  q : A ⊑ᵂ⟨ W ⟩ B′

After the `β-inst` prefix and the catalogued Λ target step, the package
needs a post-step relation of the form:

  W₂ ∣ γ₂ ⊢² M ⊑ postΛ V′ ∶ p₂

where `postΛ V′` is the target body exposed by the generated type
application/reveal sequence in the right-extended world, and `p₂` is the
source-side obligation for the residual
`↑ᶜ (close-instᶜ c′)`.

The source-strip recursion can rebuild through source-side wrappers
(`cast⊑²`, `reveal⊑²`, `conceal⊑²`). The first core shape that does not
determine the needed post relation is:

  rel =
    CTI2.Λ⊑² Anv zero∈A liftγ vV target⊢ bodyRel p

with the target term specialized by the branch equality:

  M′ = Λ V′

The available body premise is:

  bodyRel :
    CTI2.liftWorldLeft X⊑★ W ∣ γ′ ⊢² V ⊑ Λ V′ ∶ body-p

To rebuild the required output for the unchanged source value `Λ V`,
the only applicable constructor against the post-β target body is again
`CTI2.Λ⊑²`, which would require:

  bodyRel-post :
    CTI2.liftWorldLeft X⊑★ W₂ ∣ γ₂′
      ⊢² V ⊑ postΛ V′ ∶ body-p₂

There is no premise in the approved `InstPostCatalogPackage` /
`InstInversionPackage` surface that transforms `bodyRel` into
`bodyRel-post`. This is not a missing ground-other obligation for the
residual cast; it is a second instantiation-inversion/descent obligation
under the source Λ introduced by the `Λ⊑²` constructor.

The `Λ⊑Λ²` core is not the blocker: it exposes a body-to-body relation.
The blocked geometry is specifically the one-sided source-polymorphic
constructor `Λ⊑²`, which relates the source body to the whole target
term. The smallest statement change that would unblock the proof is to
extend the Λ inversion package with a recursive core-continuation field
for this `Λ⊑²` case, well-founded on the source-strip/core relation
derivation or on an explicit target-instantiation descent measure. The
current package records only target wrapper descent after the catalog
step, not this source-core descent.

No live statement was weakened, and no postulate or hole was added.
