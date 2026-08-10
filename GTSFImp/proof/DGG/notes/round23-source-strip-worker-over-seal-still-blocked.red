SourceStripWorkerProof performance split attempt 3 blocked at cast-over-seal.

Command used for the target file:

  AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/SourceStripWorkerProof.agda

Current structural state:

* `source-spine-strip-worker` is now only a coarse `SpineValue` dispatcher.
* Cast shape is split into:
  * `source-spine-strip-worker-cast-cast`
  * `source-spine-strip-worker-cast-step`
  * `source-spine-strip-worker-cast`
* `source-spine-strip-worker-cast-step` is split into:
  * `source-spine-strip-worker-cast-step-nonvar`
  * `source-spine-strip-worker-cast-step-over-seal`
  * `source-spine-strip-worker-cast-step-wrap`
* `source-spine-strip-worker-cast-step-over-seal` is split into:
  * `source-spine-strip-worker-cast-step-over-seal-star`
  * `source-spine-strip-worker-cast-step-over-seal-name`
* Seal shape is split into:
  * `source-spine-strip-worker-seal-nonvar`
  * `source-spine-strip-worker-seal-cast`
  * `source-spine-strip-worker-seal-source`
  * `source-spine-strip-worker-seal`

Measured timings:

* Full target after first constructor split: stopped after about 300s.
* Full target after cast/seal split: concrete helper error after 405.71s.
* Full target after restoring the missing seal-cast impossible clause:
  stopped after more than 420s with no diagnostic.
* Prefix through `source-spine-strip-worker-cast-cast`: 20.51s.
* Prefix through `source-spine-strip-worker-cast-step` before seal split:
  timed out at 180.07s.
* Prefix through `source-spine-strip-worker-cast-step-nonvar`: 58.72s.
* Prefix through `source-spine-strip-worker-cast-step-over-seal` before
  star/name split: timed out at 180.06s.
* Prefix through `source-spine-strip-worker-cast-step-over-seal-star` and
  `source-spine-strip-worker-cast-step-over-seal-name`: timed out at 180.06s.

Remaining slow shape:

The first remaining slow slice is the source-cast-over-seal helper group:

  `source-spine-strip-worker-cast-step-over-seal-star`
  `source-spine-strip-worker-cast-step-over-seal-name`

The blocked square is:

$$
\begin{array}{ccc}
((V \downarrow \mathsf{seal}\ X\ R_i)\langle c\rangle)
  \downarrow \mathsf{seal}\ X_L\ \star
& \sqsubseteq &
U \downarrow \mathsf{seal}\ Y\ S
\\
\downarrow^{*} & & \downarrow^{*}
\\
\mathsf{strip}(V, X, R_i, c, X_L)
& \sqsubseteq &
\mathsf{strip}(U, Y, S)
\end{array}
$$

The exposed premise used by the branch is still:

$$
W_i \mid \gamma_i \vdash^2
  V \sqsubseteq U \downarrow \mathsf{seal}\ Y\ S
  : R_i \sqsubseteq_{W_i} \mathsf{`var}\ Y
$$

Likely next step:

The helper groups are still too broad with type `SourceSpineStrip`. The next
split should give the star/name over-seal helpers specialized types whose
source term is fixed to `(V ↓ seal X Rᵢ) ⟨ c ⟩`, whose source store member has
type `★`, and whose derivation argument is fixed to the corresponding
`cast⊑² (conceal⊑² ...)` head. That should avoid Agda rechecking unrelated
`SourceSpineStrip` constructors such as `•⊑²` while processing these helpers.
