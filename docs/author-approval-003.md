# Frozen declaration provenance

This public summary identifies the exact declaration records referenced by the
manifest. Original interactive review records are retained privately. The manifest
and Lean source files are unchanged from the completed formalization.

| Export | Source contract | Lean file |
| --- | --- | --- |
| `Autoformalization.PetrovGalerkin.exists_unique_maximal_variance` | `variance:max-value` | [source](../Autoformalization/PetrovGalerkin/Frozen/VarianceExistence.lean) |

The source is [the manuscript](../sources/main.tex), SHA-256
`be9c5173799359b30b4e452145e49ca98f5368a07bbe351d906c1a452b15f372`.
These source groups are unsplit. The theorem range is natural `n ≥ 1`, and
variance is defined on nonempty finite index sets. No statement changes are
introduced by this public summary.

The [manifest](frozen-anchor-manifest.json) records exact frozen source hashes
and elaborated type fingerprints. Successful `./scripts/verify` checks the
frozen source regions and public exports, including their axiom dependencies.
Type fingerprints alone are not proof certificates.
