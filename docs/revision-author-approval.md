# Revised declaration provenance

The [manifest](frozen-anchor-manifest.json) binds these two declarations to the
[revised manuscript](../sources/main.tex), SHA-256
`3a26b8d6e731720e84b1b739814f707a8cfd30c8a6344628eaa68c722d7894ff`:

- [Abstract Theorem 1](../Autoformalization/HilbertSequence/Frozen/QuasiOrthogonality.lean),
  `Autoformalization.HilbertSequence.quasi_orthogonality`.
- [Both Section 2 assumptions](../Autoformalization/PetrovGalerkin/Frozen/Assumptions.lean),
  `Autoformalization.PetrovGalerkin.petrov_galerkin_assumptions`.

The complete declarations received independent source review and author approval
before their proofs were completed. Both source groups are unsplit; the Section 2
result checks both assumptions jointly with their explicit constants. The author
approved `Csep=4L⁴M⁴/α⁴`, inclusive earlier indices, every maximizing weight vector,
`n≥1`, and nonempty variance sets. See [errata and deviations](ERRATA-AND-DEVIATIONS.md).

Only the proof bodies changed during completion. The manifest retains exact
prefix/suffix hashes, fully elaborated type fingerprints and the unchanged
variance-definition hash. Final imported type fingerprints match those reviewed.
Both declarations are proved without placeholders or extra source premises.
Original interactive review records remain private; this file is their public
provenance summary, not a replacement proof certificate. Readers can reproduce
the build and axiom checks using the [verification instructions](VERIFICATION.md).
