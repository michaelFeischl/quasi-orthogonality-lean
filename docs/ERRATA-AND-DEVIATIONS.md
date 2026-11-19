# Errata and deviations

This record concerns the revised manuscript in [sources/main.tex](../sources/main.tex),
SHA-256 `3a26b8d6e731720e84b1b739814f707a8cfd30c8a6344628eaa68c722d7894ff`.
Locations use its section numbers and LaTeX labels; no PDF comparison is claimed.
An erratum is a false printed assertion; proof supplements and explicit
interpretations are counted as deviations. Counts are numbered entries.

| Source | Errata | Deviations |
| --- | ---: | ---: |
| Revised manuscript | 1 | 5 |

## Erratum

1. **Section 2, final separation constant.** The printed value
   `Csep = 4 L⁴ / (α⁴ M⁴)` must be replaced by **`4 L⁴ M⁴ / α⁴`**.
   The author approved this correction. The preceding estimates give
   `(α/M²) E ≤ L d z` and `(α²/(4L²)) d² ≤ E`, which imply
   `E ≤ (4 L⁴ M⁴/α⁴) z²`, including the zero-variance case.

   A counterexample to the printed coefficient is `U=V=ℝ`,
   `A(x)(y)=xy`, `T(x)=2x`, `L=1`, `M=α=2`, and trial/test spaces `{0}`
   before level 3 and `ℝ` from level 3 onward. For `f(y)=y`, the solutions
   at levels 1,2,3 are `0,0,1`. For `J={2,3}`, equal weights maximize the
   variance of the transformed points `0,2`: the mean and variance are both
   1. The earlier point `v=0` is admissible, so the printed coefficient would
   require `1 ≤ 1/64`. This counterexample is a mathematical calculation,
   not a separately certified Lean theorem.

   The corrected assertion is proved in
   [`petrov_galerkin_assumptions`](../Autoformalization/PetrovGalerkin/Frozen/Assumptions.lean).
   The abstract Theorem 1 retains its displayed exponent unchanged; substitution
   of the corrected constant gives `1/(16 Csep)=α⁴/(64L⁴M⁴)`.

## Deviations

1. **Theorem 1 and the variance definition: domains.** Use natural `n ≥ 1`
   and nonempty finite index sets inside `{1,…,n}`. Empty sets admit no
   probability weights. Finite sequences are represented by a natural-indexed
   family with all abstract assumptions restricted to the chosen prefix.
   See [Theorem 1](../Autoformalization/HilbertSequence/Frozen/QuasiOrthogonality.lean)
   and [the variance definition](../Autoformalization/PetrovGalerkin/Frozen/Variance.lean).

2. **Separation (`eq:sep`): interpretation.** Read `i ≤ J` as `i ≤ j` for
   every `j ∈ J`. Require the estimate for every maximizing weight vector
   and every point of the indicated convex hull. No uniqueness of weights is
   asserted. The formal carrier is a real Hilbert space; a complex Hilbert
   space may be viewed over the reals. These are the interpretations used by
   [Theorem 1](../Autoformalization/HilbertSequence/Frozen/QuasiOrthogonality.lean).

3. **Variance and degenerate cases: proof supplements.** Existence, attainment,
   the full upper-bound property and uniqueness of the maximum value are proved
   before defining variance. Singleton sets, coincident endpoints and zero
   variance are handled explicitly. See the
   [complete characterization](../Autoformalization/PetrovGalerkin/Frozen/VarianceCharacterization.lean)
   and [Section 2 estimates](../Autoformalization/PetrovGalerkin/AssumptionEstimates.lean).
   No maximum-existence or positive-variance premise is added to the results.

4. **Theorem 1, Step 3: aggregation route and constant.** The proof uses binary
   groups that may be truncated and handles both parities directly, rather
   than reducing first to a power-of-two window. It chooses `C = 8 Ccea²`
   before the space, sequence or length, preserves the original endpoint
   distance and covers all `n ≥ 1`. See the
   [provider](../Autoformalization/HilbertSequence/Providers/QuasiOrthogonality.lean)
   and [finite aggregation](../Autoformalization/PetrovGalerkin/DyadicAggregation.lean).
   The displayed merger and pair estimates govern the proof: the pair bound is
   `‖x_i-x_j‖² ≤ 4 E_{i,j}`. Informal growth descriptions in the introduction
   are not used as additional assertions.

5. **Scope.** Theorem 1, the Section 2 assumptions check, and discrete
   well-posedness (Lemma 2) are formalized. Section 3 and commented alternatives
   are excluded. The previous Petrov–Galerkin theorem remains available for
   compatibility and is pinned to the
   [archived manuscript](../sources/versions/main-2026-11-18.tex).

General analysis and convexity results come from the pinned Mathlib dependency.
No comparison with the manuscript's bibliographic references is claimed.
