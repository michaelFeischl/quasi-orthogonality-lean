# Quasi-orthogonality for strongly monotone Galerkin methods

Lean formalization of **Theorem 1 and Section 2** of *Quasi-orthogonality is a geometric property* (ArXiv Link TBD)

| Paper result | Lean declaration / file |
| --- | --- |
| Theorem 1 (`thm:qo`) | [`HilbertSequence.quasi_orthogonality`](Autoformalization/HilbertSequence/Frozen/QuasiOrthogonality.lean) |
| Section 2: both assumptions | [`PetrovGalerkin.petrov_galerkin_assumptions`](Autoformalization/PetrovGalerkin/Frozen/Assumptions.lean) |
| Lemma 2: discrete well-posedness | [`PetrovGalerkin.exists_unique_discrete_solution`](Autoformalization/PetrovGalerkin/Frozen/DiscreteWellposedness.lean) |


## Verify

Requires Linux (or WSL), Git, Bash, `flock`, Python 3.12+, and elan.
Lean **4.36.0** and Mathlib are pinned in `lean-toolchain` and `lake-manifest.json`.
From the repository directory:

```sh
lake exe cache get       # obtain the pinned dependencies and compiled Mathlib cache
./scripts/verify        # build all modules, check frozen statements and final axioms
```

For a build alone, run `./scripts/build`. To use the results:

```lean
import Autoformalization
#check Autoformalization.HilbertSequence.quasi_orthogonality
#check Autoformalization.PetrovGalerkin.petrov_galerkin_assumptions
```

All seven frozen exports are proved, with no `sorry` or custom axioms; their
axiom closure uses only `propext`, `Classical.choice`, and `Quot.sound`.
The [verification summary](docs/VERIFICATION.md) records the independent
source audit and the check that Section 2 supplies Theorem 1's assumptions. Named-binder warnings in
approved signatures are harmless. Verification needs no agent tooling.

Third-party checker attribution: [notice](scripts/vendor/NOTICE.md).
A project-wide license for the proofs and manuscript has not been specified.
