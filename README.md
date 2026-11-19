# Quasi-orthogonality for strongly monotone Galerkin methods

Lean formalization of **Theorem 1 and Section 2** of Michael Feischl and David
Niederkofler's *Quasi-orthogonality for strongly monotone Galerkin methods*
([paper source](sources/main.tex)). Section 3 is excluded.

| Paper result | Lean declaration / file |
| --- | --- |
| Theorem 1 (`thm:qo`) | [`HilbertSequence.quasi_orthogonality`](Autoformalization/HilbertSequence/Frozen/QuasiOrthogonality.lean) |
| Section 2: both assumptions | [`PetrovGalerkin.petrov_galerkin_assumptions`](Autoformalization/PetrovGalerkin/Frozen/Assumptions.lean) |
| Lemma 2: discrete well-posedness | [`PetrovGalerkin.exists_unique_discrete_solution`](Autoformalization/PetrovGalerkin/Frozen/DiscreteWellposedness.lean) |

All names have prefix `Autoformalization`. Theorem 1's proof chooses
`C = 8 * Ccea²`. The Section 2 check proves `Ccea = (L*M/α)³` and the
**author-approved corrected constant `Csep = 4*L⁴*M⁴/α⁴`**.

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

## Errata and deviations

The revised source has **1 confirmed erratum and 5 grouped deviations** in the
[record](docs/ERRATA-AND-DEVIATIONS.md): the corrected separation constant,
explicit domains and separation quantifiers, variance construction, and direct
finite aggregation. Section 3 remains outside scope. Earlier exports remain
available against the [archived manuscript](sources/versions/main-2026-11-18.tex).

Third-party checker attribution: [notice](scripts/vendor/NOTICE.md).
A project-wide license for the proofs and manuscript has not been specified.
