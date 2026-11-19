module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Order.Interval.Finset.Nat

import Autoformalization.PetrovGalerkin.Providers.VarianceExistence

public section
universe v
namespace Autoformalization.PetrovGalerkin

theorem exists_unique_maximal_variance :
    ∀ (V : Type v) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [CompleteSpace V] (x : ℕ → V) (n : ℕ),
      1 ≤ n → ∀ I : Finset ℕ, I.Nonempty → I ⊆ Finset.Icc 1 n →
      ∃! E : ℝ,
        (∃ w : ℕ → ℝ,
          (∀ i ∈ I, 0 ≤ w i ∧ w i ≤ 1) ∧
          (∑ i ∈ I, w i) = 1 ∧
          (∑ i ∈ I, w i * ‖x i - ∑ j ∈ I, w j • x j‖ ^ 2) = E) ∧
        (∀ w : ℕ → ℝ,
          (∀ i ∈ I, 0 ≤ w i ∧ w i ≤ 1) →
          (∑ i ∈ I, w i) = 1 →
          (∑ i ∈ I, w i * ‖x i - ∑ j ∈ I, w j • x j‖ ^ 2) ≤ E) :=
by exact Autoformalization.PetrovGalerkin.Provider.exists_unique_maximal_variance

end Autoformalization.PetrovGalerkin
