# Verification

From the repository directory, with the prerequisites listed in the [README](../README.md):

```sh
lake exe cache get
./scripts/verify
source scripts/env.sh
python3 scripts/test_campaign_guard.py
```

The verifier builds all **29 project modules**, checks source/dependency pins,
frozen statements and draft isolation, and inspects all **seven public manifest
exports**. Every export is proved; its axiom closure contains only `propext`,
`Classical.choice`, and `Quot.sound`. There are no Lean placeholders or custom
axioms. The guard mutation suite has **31 tests**, including both source pins
and the new declarations' draft isolation. Named-binder warnings in the exact
approved signatures are retained intentionally.

Independent source and semantics review checked the exact declarations, variance
construction and characterization, constant dependence, all source premises,
and the corrected Section 2 estimate. A full-type Lean composition check
confirmed that `petrov_galerkin_assumptions` supplies the assumptions of
`HilbertSequence.quasi_orthogonality`, with the uniform constant chosen before
the spaces, maps, solution sequence and length.

All **28 modules containing declarations** have successful exact-module kernel
replays: 22 unchanged certificates and six new checks. The public root contains
only imports. An individual replay can be reproduced with:

```sh
./scripts/build --replay Autoformalization.HilbertSequence.Frozen.QuasiOrthogonality
./scripts/build --replay Autoformalization.PetrovGalerkin.Frozen.Assumptions
```

The mathematical source differences and excluded Section 3 are documented in
[errata and deviations](ERRATA-AND-DEVIATIONS.md). The direct finite aggregation
proof replaces the printed window/reindexing detour; the unused intermediate
steps in that detour are not claimed separately formalized. All premises of
the implemented proof are discharged.

Independent dead-code review found no safe deletion. Two clean project-only
builds took **17.543 s** and **16.741 s**, with all 58 serial file profiles passing.
The largest measured local phase was about 1.1 s, so no performance edit was
justified. These are measurements of identical Lean sources, not a speedup claim;
wall time includes build-lock and guard overhead. Timings used Python monotonic
elapsed time and OS process accounting because GNU time was unavailable.

The public export is also checked from empty project build artifacts using the
existing pinned dependency cache. This does not retest network cache downloads.
Verification tooling is included in the repository; no external agent skills
are required. Third-party checker attribution is in the [notice](../scripts/vendor/NOTICE.md).
