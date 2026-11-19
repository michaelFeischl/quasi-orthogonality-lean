-- FROZEN_ANCHOR_PREFIX_BEGIN
module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Order.Interval.Finset.Nat

import Autoformalization.PetrovGalerkin.Providers.QuasiOrthogonality

public section
universe u v
namespace Autoformalization.PetrovGalerkin

theorem quasi_orthogonality :
    ∀
    (L M α : ℝ) (hL : 0 < L) (hM : 0 < M) (hα : 0 < α),
    let δ : ℝ := 1 - Real.logb 2
      (max (3 / 2 : ℝ) ((1 / 2 : ℝ) + α ^ 4 / (64 * L ^ 4 * M ^ 4))⁻¹)
    0 < δ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (U : Type u) (V : Type v)
        [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
        [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
        (A : U → (V →L[ℝ] ℝ)) (T : U → V)
        (Uj : ℕ → Submodule ℝ U) (Vj : ℕ → Submodule ℝ V),
        (∀ j, FiniteDimensional ℝ (Uj j)) →
        (∀ j, FiniteDimensional ℝ (Vj j)) →
        (∀ j, Uj j ≤ Uj (j + 1)) →
        (∀ j, Vj j ≤ Vj (j + 1)) →
        (∀ x y : U, ‖A x - A y‖ ≤ L * ‖x - y‖) →
        Function.Surjective T →
        (∀ j, Set.MapsTo T (Uj j) (Vj j)) →
        (∀ j, Set.SurjOn T (Uj j) (Vj j)) →
        (∀ j, ∀ x ∈ Uj j, ∀ y ∈ Uj j,
          ‖T x - T y‖ ≤ M * ‖x - y‖) →
        (∀ j, ∀ x ∈ Uj j, ∀ y ∈ Uj j,
          α * ‖x - y‖ ^ 2 ≤ (A x - A y) (T x - T y)) →
        ∀ (f : V →L[ℝ] ℝ) (u : ℕ → U),
          (∀ j, u j ∈ Uj j) →
          (∀ j, ∀ z ∈ Vj j, A (u j) z = f z) →
          ∀ n : ℕ, 1 ≤ n →
            (∑ i ∈ Finset.Ico 1 n, ‖u (i + 1) - u i‖ ^ 2) ≤
              C * Real.rpow (n : ℝ) (1 - δ) * ‖u n - u 1‖ ^ 2 :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact Autoformalization.PetrovGalerkin.Provider.quasi_orthogonality
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end Autoformalization.PetrovGalerkin
-- FROZEN_ANCHOR_SUFFIX_END
