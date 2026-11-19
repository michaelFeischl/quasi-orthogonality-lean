# Errata and deviations

This record distinguishes source errors from explicit interpretations, proof
supplements, and changes of presentation. A supplied argument for a true step is
counted as a deviation, not an erratum. The source is Michael Feischl and David
Niederkofler, *Quasi-orthogonality for strongly monotone Galerkin methods*, in
the [included LaTeX manuscript](../sources/main.tex), SHA-256
`be9c5173799359b30b4e452145e49ca98f5368a07bbe351d906c1a452b15f372`.
Locations below use its theorem numbers, LaTeX labels, and proof steps; no PDF
or published-version comparison is claimed. Counts are numbered entries, with
related details grouped together. No correction to Lemma 1 or Theorem 2 is
claimed. Their Lean proofs use only `propext`, `Classical.choice`, and
`Quot.sound`.

| Source | Errata | Deviations |
| --- | ---: | ---: |
| Included manuscript | 0 | 7 |

## Included manuscript

### Errata

None claimed.

### Deviations

1. **Theorem 2 (`thm:qo`) and Step 1, definition of variance: explicit domains.**
   The theorem leaves the range of `n` implicit, and Step 1 writes
   `I ⊆ {1,…,n}` without excluding the empty set. The formal theorem holds for
   every natural `n ≥ 1`. Variance is defined only for nonempty finite subsets
   of `{1,…,n}`, since an empty set admits no weights with sum one. The proof
   includes `n = 1` and `n = 2`; it does not assign a fallback variance to the
   empty set. These domain choices appear in
   [`quasi_orthogonality`](../Autoformalization/PetrovGalerkin/Frozen/QuasiOrthogonality.lean)
   and [`maximalVariance`](../Autoformalization/PetrovGalerkin/Frozen/Variance.lean).

2. **Standing assumptions (`eq:pg-map-bound`, `eq:pg-monotonicity`): local-domain
   interpretation.** The trailing condition `x,y ∈ U_j` is read as applying
   to both estimates in the aligned display. Accordingly, the bound for `T`
   and paired monotonicity are required on each trial subspace, while the
   Lipschitz bound for `A` is global. No linearity of `T`, condition `T(0)=0`,
   or global bound `α ≤ LM` is added. See the complete hypotheses of
   [`quasi_orthogonality`](../Autoformalization/PetrovGalerkin/Frozen/QuasiOrthogonality.lean).
   This makes the domain interpretation explicit without strengthening it.

3. **Discrete equation (`eq:discrete`), Lemma 1 (`lem:pg-wellposed`), and
   Theorem 2: explicit solution family.** The manuscript refers to the
   solutions `u_j`. The formal estimate quantifies over any sequence `u`
   whose values belong to the trial spaces and satisfy the discrete equations
   for one common right-hand side. Existence and uniqueness at each level are
   separately proved by
   [`exists_unique_discrete_solution`](../Autoformalization/PetrovGalerkin/Frozen/DiscreteWellposedness.lean).
   The estimate does not itself construct a canonical sequence; its hypotheses
   express exactly the discrete solutions under discussion.

4. **Theorem 2, Step 1: general variance theorem and maximum attainment.**
   The manuscript uses `x_i = T u_i` and refers to corresponding maximizing
   weights. The formal variance construction works for arbitrary points
   `x : ℕ → V` in a real Hilbert space. Compactness of the finite probability
   simplex and continuity of the objective prove attainment and uniqueness of
   the maximum value in
   [`exists_unique_maximal_variance`](../Autoformalization/PetrovGalerkin/Frozen/VarianceExistence.lean).
   [`maximalVariance_characterization`](../Autoformalization/PetrovGalerkin/Frozen/VarianceCharacterization.lean)
   gives attainment, the upper bound for every admissible weight, and uniqueness
   for the value selected by `maximalVariance`. Maximizing weights need not be
   unique. Specializing to `x_i = T u_i` recovers the manuscript's quantity;
   no maximum-existence hypothesis is added to Theorem 2.

5. **Theorem 2, Step 2, endpoint estimate and cancellation: degenerate cases.**
   The proof explicitly treats coincident endpoints and zero variance before
   cancelling any positive quantity. The two-point estimate in
   [`pair_sq_distance_le_maximalVariance`](../Autoformalization/PetrovGalerkin/VarianceBasic.lean)
   allows equal indices, and
   [`scalar_separation_gain`](../Autoformalization/PetrovGalerkin/SeparationGain.lean)
   separates zero from positive variance. These supplements include singleton
   sets and do not require nonzero increments or positive variance in the
   final theorem.

6. **Theorem 2, Step 4: direct finite aggregation and explicit constant.**
   Instead of first reducing to a power-of-two window, the formal proof merges
   each parity collection using binary groups that may be truncated. The
   resulting [`finite_energy_sum_le`](../Autoformalization/PetrovGalerkin/DyadicAggregation.lean)
   applies directly to every `n ≥ 1`. The manuscript's first/last-window
   inequality is also proved there as `half_sum_le_max_dyadic_windows`.
   The Céa estimate is used in
   [`maximalVariance_le_galerkin_endpoint`](../Autoformalization/PetrovGalerkin/PGVarianceBounds.lean)
   to keep the original endpoint distance `‖u_n-u_1‖`. The
   [proof of `quasi_orthogonality`](../Autoformalization/PetrovGalerkin/Providers/QuasiOrthogonality.lean)
   chooses `C = 8 * (L * M / α)^4` before introducing spaces, maps, the right-hand
   side, the sequence, or `n`. This supplies the manuscript's existential
   constant while preserving its exact exponent and parameter dependence.

7. **Section 2 and commented alternatives: scope.** The formalization covers
   Theorem 2 and its Section 1 prerequisites, including Lemma 1. Section 2 and
   commented-out alternatives in the LaTeX source are not formalized. The
   [public Lean entry point](../Autoformalization.lean) exports the implemented
   Section 1 results; inclusion of the complete manuscript is not a claim to
   have formalized its other material.

## Proof route and interpretation

The proof follows the displayed variance merger, separation, and reduction
estimates, then uses the finite aggregation in item 6. In particular, it uses
the precise display `eq:reduction`, `E_I + E_J ≤ q E_(I∪J)` with `q < 2`,
rather than treating the introductory description of an increase by a factor
larger than two as a separate assertion. No numerical correction to the
displayed inequalities or to Theorem 2 is made.

## Outside scope and other references

The scope exclusion is item 7. General Hilbert-space, compactness, and fixed-point
results are supplied by the pinned Mathlib dependency recorded in
[`lake-manifest.json`](../lake-manifest.json). Bibliographic works mentioned by
the manuscript are not additional formalization targets, and no independent
comparison with those works is claimed.
