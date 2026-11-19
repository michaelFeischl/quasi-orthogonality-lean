module

public import Autoformalization.PetrovGalerkin.WeightedVariance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A half-weight mixture on disjoint finite sets

Finite-sum identities for a mixture of weights on disjoint index sets.
-/

public section

namespace Autoformalization.PetrovGalerkin

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Mixing two admissible weight families equally adds one quarter of the
squared distance between their means to their average variance. -/
theorem exists_half_mixture (I J : Finset ℕ) (hIJ : Disjoint I J)
    (w v : ℕ → ℝ) (x : ℕ → V)
    (hw : ∀ i ∈ I, 0 ≤ w i ∧ w i ≤ 1)
    (hv : ∀ i ∈ J, 0 ≤ v i ∧ v i ≤ 1)
    (hw_sum : ∑ i ∈ I, w i = 1) (hv_sum : ∑ i ∈ J, v i = 1) :
    ∃ m : ℕ → ℝ,
      (∀ i ∈ I ∪ J, 0 ≤ m i ∧ m i ≤ 1) ∧
      (∑ i ∈ I ∪ J, m i = 1) ∧
      (∑ i ∈ I ∪ J, m i * ‖x i - ∑ j ∈ I ∪ J, m j • x j‖ ^ 2) =
        ((∑ i ∈ I, w i * ‖x i - ∑ j ∈ I, w j • x j‖ ^ 2) +
          (∑ i ∈ J, v i * ‖x i - ∑ j ∈ J, v j • x j‖ ^ 2)) / 2 +
          ‖(∑ i ∈ I, w i • x i) - (∑ i ∈ J, v i • x i)‖ ^ 2 / 4 := by
  let m : ℕ → ℝ := fun i => if i ∈ I then w i / 2 else v i / 2
  have hmI (i : ℕ) (hi : i ∈ I) : m i = w i / 2 := by
    simp only [m, ite_eq_left hi]
  have hmJ (i : ℕ) (hi : i ∈ J) : m i = v i / 2 := by
    simp only [m, ite_eq_right (Finset.disjoint_right.mp hIJ hi)]
  have hsplit (f : ℕ → ℝ → ℝ) :
      (∑ i ∈ I ∪ J, f i (m i)) =
        (∑ i ∈ I, f i (w i / 2)) + (∑ i ∈ J, f i (v i / 2)) := by
    rw [Finset.sum_union hIJ]
    congr 1
    · exact Finset.sum_congr rfl (fun i hi => congrArg (f i) (hmI i hi))
    · exact Finset.sum_congr rfl (fun i hi => congrArg (f i) (hmJ i hi))
  have hm_sum : ∑ i ∈ I ∪ J, m i = 1 := by
    rw [hsplit (fun _ a => a), ← Finset.sum_div, ← Finset.sum_div, hw_sum, hv_sum]
    norm_num
  have hm_mean : (∑ i ∈ I ∪ J, m i • x i) =
      (1 / 2 : ℝ) • ((∑ i ∈ I, w i • x i) + (∑ i ∈ J, v i • x i)) := by
    rw [Finset.sum_union hIJ, smul_add, Finset.smul_sum, Finset.smul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [hmI i hi, smul_smul]
      congr 1
      ring
    · apply Finset.sum_congr rfl
      intro i hi
      rw [hmJ i hi, smul_smul]
      congr 1
      ring
  have hm_second : (∑ i ∈ I ∪ J, m i * ‖x i‖ ^ 2) =
      ((∑ i ∈ I, w i * ‖x i‖ ^ 2) + (∑ i ∈ J, v i * ‖x i‖ ^ 2)) / 2 := by
    rw [hsplit (fun i a => a * ‖x i‖ ^ 2), add_div]
    simp only [div_mul_eq_mul_div, Finset.sum_div]
  refine ⟨m, ?_, hm_sum, ?_⟩
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · rw [hmI i hi]
      constructor <;> linarith only [(hw i hi).1, (hw i hi).2]
    · rw [hmJ i hi]
      constructor <;> linarith only [(hv i hi).1, (hv i hi).2]
  · rw [weighted_variance_eq (I ∪ J) m x hm_sum,
      weighted_variance_eq I w x hw_sum, weighted_variance_eq J v x hv_sum,
      hm_second, hm_mean, norm_smul, Real.norm_eq_abs]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    rw [mul_pow, norm_add_sq_real, norm_sub_sq_real]
    ring

end Autoformalization.PetrovGalerkin
