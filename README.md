# Quasi-orthogonality is a geometric property

Lean formalization of the abstract quasi-orthogonality theorem and the
Petrov–Galerkin assumptions check in *Quasi-orthogonality is a geometric property*
by Michael Feischl and David Niederkofler.

| Result | Lean declaration |
| --- | --- |
| Abstract quasi-orthogonality | [`HilbertSequence.quasi_orthogonality`](Autoformalization/HilbertSequence/Frozen/QuasiOrthogonality.lean) |
| Petrov–Galerkin assumptions | [`PetrovGalerkin.petrov_galerkin_assumptions`](Autoformalization/PetrovGalerkin/Frozen/Assumptions.lean) |
| Discrete well-posedness | [`PetrovGalerkin.exists_unique_discrete_solution`](Autoformalization/PetrovGalerkin/Frozen/DiscreteWellposedness.lean) |

All names have prefix `Autoformalization`. The Lean declarations specify the
precise hypotheses and conclusions.

## Verify

Requires Linux (or WSL), Git, Bash, `flock`, Python 3.12+, and elan.
Lean **4.36.0** and Mathlib are pinned in `lean-toolchain` and `lake-manifest.json`.
From the repository directory:

```sh
lake exe cache get       # obtain the pinned dependencies and compiled Mathlib cache
./scripts/verify        # build every module, reject proof holes, check export axioms
```

For a build alone, run `./scripts/build`. To use the results:

```lean
import Autoformalization
#check Autoformalization.HilbertSequence.quasi_orthogonality
#check Autoformalization.PetrovGalerkin.petrov_galerkin_assumptions
```

All 29 modules compile without `sorry`. The seven principal exports depend
only on the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
Verification is self-contained.

A project-wide license has not been specified.
