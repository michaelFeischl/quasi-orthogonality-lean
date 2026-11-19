# Quasi-orthogonality for strongly monotone Galerkin methods

Lean formalization of **Theorem 2** and its Section 1 dependencies in
Michael Feischl and David Niederkofler,
*Quasi-orthogonality for strongly monotone Galerkin methods*
([paper source](sources/main.tex)). Section 2 is not formalized.

| Paper result | Lean declaration / file |
| --- | --- |
| Theorem 2 (`thm:qo`) — quasi-orthogonality | [`quasi_orthogonality`](Autoformalization/PetrovGalerkin/Frozen/QuasiOrthogonality.lean) |
| Lemma 1 (`lem:pg-wellposed`) — discrete well-posedness | [`exists_unique_discrete_solution`](Autoformalization/PetrovGalerkin/Frozen/DiscreteWellposedness.lean) |

Both declarations are in the namespace `Autoformalization.PetrovGalerkin`.
The proof constructs a uniform constant `C = 8 * (L * M / α)^4`.
The formalization uses natural `n ≥ 1` and nonempty variance index sets;
see [errata and deviations](docs/ERRATA-AND-DEVIATIONS.md).

## Verify

Requires **Linux (or WSL), Git, Bash, `flock`, Python 3.12+, and elan**.
Lean **4.36.0** and Mathlib are pinned by `lean-toolchain` and `lake-manifest.json`.
From the repository directory:

```sh
lake exe cache get       # fetch the pinned dependencies and compiled Mathlib cache
./scripts/verify        # build every project module, check anchors and final axioms
```

For a build alone, run `./scripts/build`. To use the results in Lean:

```lean
import Autoformalization
#check Autoformalization.PetrovGalerkin.quasi_orthogonality
```

All five frozen exports are proved, with no `sorry` or custom axioms.
Their axiom closure uses only `propext`, `Classical.choice`, and `Quot.sound`.
Named-binder warnings in the approved statements are harmless.
The build and verifier are self-contained apart from the listed dependencies.

## Errata and deviations

For the pinned paper: **0 claimed errata and 7 grouped deviations**; see the
[full record](docs/ERRATA-AND-DEVIATIONS.md). The formalization makes `n ≥ 1`
and nonempty variance sets explicit, proves existence and uniqueness of the
maximum variance value, and supplies the degenerate cases and dyadic aggregation.
Theorem 2's exponent and assumptions are preserved.

Third-party checker attribution: [notice](scripts/vendor/NOTICE.md).
A project-wide license for the proofs and manuscript has not been specified.
