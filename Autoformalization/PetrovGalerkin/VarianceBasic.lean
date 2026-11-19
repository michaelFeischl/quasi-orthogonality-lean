module

public import Autoformalization.PetrovGalerkin.Frozen.VarianceCharacterization
public import Autoformalization.PetrovGalerkin.WeightedVariance
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Basic estimates for the attained maximum variance

Consequences of the complete variance characterization on nonempty
subsets of `{1,…,n}`.
-/

public section

namespace Autoformalization.PetrovGalerkin

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] (x : ℕ → V) (n : ℕ) (hn : 1 ≤ n)

/-- The maximum variance is attained by admissible weights. -/
theorem exists_weights_maximalVariance (I : Finset ℕ) (hI : I.Nonempty)
    (hIn : I ⊆ Finset.Icc 1 n) :
    ∃ w : ℕ → ℝ, (∀ i ∈ I, 0 ≤ w i ∧ w i ≤ 1) ∧
      (∑ i ∈ I, w i) = 1 ∧
      (∑ i ∈ I, w i * ‖x i - ∑ j ∈ I, w j • x j‖ ^ 2) =
        maximalVariance V x n hn I hI hIn :=
  (maximalVariance_characterization V x n hn I hI hIn).1.1

/-- Every admissible weighted objective is bounded by the maximum variance. -/
theorem objective_le_maximalVariance (I : Finset ℕ) (hI : I.Nonempty)
    (hIn : I ⊆ Finset.Icc 1 n) (w : ℕ → ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i ∧ w i ≤ 1) (hs : ∑ i ∈ I, w i = 1) :
    (∑ i ∈ I, w i * ‖x i - ∑ j ∈ I, w j • x j‖ ^ 2) ≤
      maximalVariance V x n hn I hI hIn :=
  (maximalVariance_characterization V x n hn I hI hIn).1.2 w hw hs

/-- Attainment transfers a bound on every admissible objective to its maximum. -/
theorem maximalVariance_le_of_forall (I : Finset ℕ) (hI : I.Nonempty)
    (hIn : I ⊆ Finset.Icc 1 n) (B : ℝ)
    (hB : ∀ w : ℕ → ℝ, (∀ i ∈ I, 0 ≤ w i ∧ w i ≤ 1) →
      (∑ i ∈ I, w i) = 1 →
      (∑ i ∈ I, w i * ‖x i - ∑ j ∈ I, w j • x j‖ ^ 2) ≤ B) :
    maximalVariance V x n hn I hI hIn ≤ B := by
  obtain ⟨w, hw, hs, he⟩ := exists_weights_maximalVariance V x n hn I hI hIn
  rw [← he]
  exact hB w hw hs

/-- The maximum variance is nonnegative. -/
theorem maximalVariance_nonneg (I : Finset ℕ) (hI : I.Nonempty)
    (hIn : I ⊆ Finset.Icc 1 n) :
    0 ≤ maximalVariance V x n hn I hI hIn := by
  obtain ⟨w, hw, _, he⟩ := exists_weights_maximalVariance V x n hn I hI hIn
  rw [← he]
  exact weighted_variance_nonneg I w x (fun i hi => (hw i hi).1)

/-- Extending weights by zero proves monotonicity under inclusion. -/
theorem maximalVariance_mono (I J : Finset ℕ) (hI : I.Nonempty) (hJ : J.Nonempty)
    (hIn : I ⊆ Finset.Icc 1 n) (hJn : J ⊆ Finset.Icc 1 n) (hIJ : I ⊆ J) :
    maximalVariance V x n hn I hI hIn ≤ maximalVariance V x n hn J hJ hJn := by
  obtain ⟨w, hw, hs, he⟩ := exists_weights_maximalVariance V x n hn I hI hIn
  let m : ℕ → ℝ := fun i => if i ∈ I then w i else 0
  have hm (i : ℕ) (hi : i ∈ I) : m i = w i := by simp only [m, ite_eq_left hi]
  have hm0 (i : ℕ) (hi : i ∉ I) : m i = 0 := by simp only [m, ite_eq_right hi]
  have hmb : ∀ i ∈ J, 0 ≤ m i ∧ m i ≤ 1 := by
    intro i _
    by_cases hi : i ∈ I
    · rw [hm i hi]
      exact hw i hi
    · rw [hm0 i hi]
      norm_num
  have hms : ∑ i ∈ J, m i = 1 := calc
    _ = ∑ i ∈ I, m i := (Finset.sum_subset hIJ (fun i _ hi => hm0 i hi)).symm
    _ = ∑ i ∈ I, w i := Finset.sum_congr rfl (fun i hi => hm i hi)
    _ = 1 := hs
  have hmean : (∑ i ∈ J, m i • x i) = ∑ i ∈ I, w i • x i := calc
    _ = ∑ i ∈ I, m i • x i := (Finset.sum_subset hIJ (by
      intro i _ hi
      rw [hm0 i hi, zero_smul])).symm
    _ = ∑ i ∈ I, w i • x i := Finset.sum_congr rfl (fun i hi => by rw [hm i hi])
  have hobj : (∑ i ∈ J, m i * ‖x i - ∑ j ∈ J, m j • x j‖ ^ 2) =
      ∑ i ∈ I, w i * ‖x i - ∑ j ∈ I, w j • x j‖ ^ 2 := by
    rw [hmean]
    calc
      _ = ∑ i ∈ I, m i * ‖x i - ∑ j ∈ I, w j • x j‖ ^ 2 :=
        (Finset.sum_subset hIJ (by intro i _ hi; rw [hm0 i hi, zero_mul])).symm
      _ = _ := Finset.sum_congr rfl (fun i hi => by rw [hm i hi])
  have hbound := objective_le_maximalVariance V x n hn J hJ hJn m hmb hms
  rw [hobj, he] at hbound
  exact hbound

/-- A uniform squared-distance bound about any center bounds the maximum variance. -/
theorem maximalVariance_le_of_sq_distance_le (I : Finset ℕ) (hI : I.Nonempty)
    (hIn : I ⊆ Finset.Icc 1 n) (z : V) (B : ℝ)
    (hB : ∀ i ∈ I, ‖x i - z‖ ^ 2 ≤ B) :
    maximalVariance V x n hn I hI hIn ≤ B := by
  apply maximalVariance_le_of_forall V x n hn I hI hIn B
  intro w hw hs
  calc
    _ ≤ ∑ i ∈ I, w i * ‖x i - z‖ ^ 2 := weighted_mean_minimizes I w x hs z
    _ ≤ ∑ i ∈ I, w i * B := Finset.sum_le_sum
      (fun i hi => mul_le_mul_of_nonneg_left (hB i hi) (hw i hi).1)
    _ = B := by rw [← Finset.sum_mul, hs, one_mul]

/-- Equal mass on two indices gives the endpoint lower bound, even when they coincide. -/
theorem pair_sq_distance_le_maximalVariance (I : Finset ℕ) (hI : I.Nonempty)
    (hIn : I ⊆ Finset.Icc 1 n) (a b : ℕ) (ha : a ∈ I) (hb : b ∈ I) :
    ‖x a - x b‖ ^ 2 / 4 ≤ maximalVariance V x n hn I hI hIn := by
  by_cases hab : a = b
  · subst b
    simpa only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_div] using maximalVariance_nonneg V x n hn I hI hIn
  have hp : ({a, b} : Finset ℕ) ⊆ I := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ha
    · have hib := Finset.mem_singleton.mp hi
      simpa only [hib] using hb
  have hpn : ({a, b} : Finset ℕ) ⊆ Finset.Icc 1 n := hp.trans hIn
  have hpne : ({a, b} : Finset ℕ).Nonempty := Finset.insert_nonempty _ _
  have hs : ∑ i ∈ ({a, b} : Finset ℕ), (1 / 2 : ℝ) = 1 := by
    rw [Finset.sum_pair hab]
    norm_num
  have hobj : (∑ i ∈ ({a, b} : Finset ℕ), (1 / 2 : ℝ) *
      ‖x i - ∑ j ∈ ({a, b} : Finset ℕ), (1 / 2 : ℝ) • x j‖ ^ 2) =
      ‖x a - x b‖ ^ 2 / 4 := by
    rw [weighted_variance_eq _ (fun _ => (1 / 2 : ℝ)) x hs,
      Finset.sum_pair hab, Finset.sum_pair hab, ← smul_add, norm_smul, Real.norm_eq_abs]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    rw [mul_pow, norm_add_sq_real, norm_sub_sq_real]
    ring
  have hbound := objective_le_maximalVariance V x n hn {a, b} hpne hpn
    (fun _ => (1 / 2 : ℝ)) (by intro i hi; norm_num) hs
  rw [hobj] at hbound
  exact hbound.trans (maximalVariance_mono V x n hn {a, b} I hpne hI hpn hIn hp)

end Autoformalization.PetrovGalerkin
