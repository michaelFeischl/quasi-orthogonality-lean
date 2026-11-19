module

public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring

/-!
# Finite weighted variance identities

Real Hilbert-space identities for finite weighted sums.
-/

public section

namespace Autoformalization.PetrovGalerkin

variable {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Expand the weighted squared distances about an arbitrary center. -/
theorem weighted_sq_distance_eq (I : Finset ι) (w : ι → ℝ) (x : ι → V)
    (hw : ∑ i ∈ I, w i = 1) (z : V) :
    (∑ i ∈ I, w i * ‖x i - z‖ ^ 2) =
      (∑ i ∈ I, w i * ‖x i‖ ^ 2) -
        2 * inner ℝ (∑ i ∈ I, w i • x i) z + ‖z‖ ^ 2 := by
  have hi : (∑ i ∈ I, w i * inner ℝ (x i) z) =
      inner ℝ (∑ i ∈ I, w i • x i) z := by
    simp only [sum_inner, real_inner_smul_left]
  calc
    (∑ i ∈ I, w i * ‖x i - z‖ ^ 2) =
        ∑ i ∈ I, (w i * ‖x i‖ ^ 2 -
          2 * (w i * inner ℝ (x i) z) + w i * ‖z‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_sub_sq_real]
      ring
    _ = (∑ i ∈ I, w i * ‖x i‖ ^ 2) -
        2 * (∑ i ∈ I, w i * inner ℝ (x i) z) +
          (∑ i ∈ I, w i) * ‖z‖ ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]
    _ = _ := by rw [hi, hw, one_mul]

/-- Variance is the second moment minus the squared norm of the mean. -/
theorem weighted_variance_eq (I : Finset ι) (w : ι → ℝ) (x : ι → V)
    (hw : ∑ i ∈ I, w i = 1) :
    (∑ i ∈ I, w i * ‖x i - ∑ j ∈ I, w j • x j‖ ^ 2) =
      (∑ i ∈ I, w i * ‖x i‖ ^ 2) - ‖∑ j ∈ I, w j • x j‖ ^ 2 := by
  rw [weighted_sq_distance_eq I w x hw, real_inner_self_eq_norm_sq]
  ring

/-- Moving the center away from the mean adds exactly its squared distance. -/
theorem weighted_sq_distance_eq_variance_add (I : Finset ι) (w : ι → ℝ)
    (x : ι → V) (hw : ∑ i ∈ I, w i = 1) (z : V) :
    (∑ i ∈ I, w i * ‖x i - z‖ ^ 2) =
      (∑ i ∈ I, w i * ‖x i - ∑ j ∈ I, w j • x j‖ ^ 2) +
        ‖(∑ j ∈ I, w j • x j) - z‖ ^ 2 := by
  rw [weighted_sq_distance_eq I w x hw, weighted_variance_eq I w x hw,
    norm_sub_sq_real]
  ring

/-- The weighted mean minimizes the weighted sum of squared distances. -/
theorem weighted_mean_minimizes (I : Finset ι) (w : ι → ℝ) (x : ι → V)
    (hw : ∑ i ∈ I, w i = 1) (z : V) :
    (∑ i ∈ I, w i * ‖x i - ∑ j ∈ I, w j • x j‖ ^ 2) ≤
      ∑ i ∈ I, w i * ‖x i - z‖ ^ 2 := by
  rw [weighted_sq_distance_eq_variance_add I w x hw z]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Nonnegative weights give a nonnegative variance. -/
theorem weighted_variance_nonneg (I : Finset ι) (w : ι → ℝ) (x : ι → V)
    (hw : ∀ i ∈ I, 0 ≤ w i) :
    0 ≤ ∑ i ∈ I, w i * ‖x i - ∑ j ∈ I, w j • x j‖ ^ 2 := by
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))

end Autoformalization.PetrovGalerkin
