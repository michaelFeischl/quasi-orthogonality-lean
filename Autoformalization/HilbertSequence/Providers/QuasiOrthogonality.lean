module

public import Autoformalization.HilbertSequence.VarianceEstimates
public import Autoformalization.PetrovGalerkin.DyadicAggregation
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quasi-orthogonality for separated Hilbert-space sequences

Céa and convex-hull separation estimates imply quasi-orthogonality.
Truncated binary grouping handles every positive length directly.
-/

public section
universe u
namespace Autoformalization.HilbertSequence.Provider

open Autoformalization.PetrovGalerkin

theorem quasi_orthogonality :
    ∀ (Ccea Csep : ℝ) (hCcea : 0 < Ccea) (hCsep : 0 < Csep),
    let δ : ℝ := 1 - Real.logb 2
      (max (3 / 2 : ℝ) ((1 / 2 : ℝ) + 1 / (16 * Csep))⁻¹)
    0 < δ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (U : Type u)
        [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
        (x : ℕ → U) (n : ℕ) (hn : 1 ≤ n),
        (∀ i j k l : ℕ, 1 ≤ i → i ≤ j → j ≤ k → k ≤ l → l ≤ n →
          ‖x k - x j‖ ≤ Ccea * ‖x l - x i‖) →
        (∀ (J : Finset ℕ) (hJ : J.Nonempty) (hJn : J ⊆ Finset.Icc 1 n)
          (w : ℕ → ℝ),
          (∀ j ∈ J, 0 ≤ w j ∧ w j ≤ 1) →
          (∑ j ∈ J, w j) = 1 →
          (∑ j ∈ J, w j * ‖x j - ∑ k ∈ J, w k • x k‖ ^ 2) =
            Autoformalization.PetrovGalerkin.maximalVariance U x n hn J hJ hJn →
          ∀ v ∈ convexHull ℝ
            (x '' {i : ℕ | 1 ≤ i ∧ i ≤ n ∧ ∀ j ∈ J, i ≤ j}),
            Autoformalization.PetrovGalerkin.maximalVariance U x n hn J hJ hJn ≤
              Csep * ‖(∑ j ∈ J, w j • x j) - v‖ ^ 2) →
        (∑ i ∈ Finset.Ico 1 n, ‖x (i + 1) - x i‖ ^ 2) ≤
          C * Real.rpow (n : ℝ) (1 - δ) * ‖x n - x 1‖ ^ 2 :=
by
  intro Ccea Csep hCcea hCsep
  dsimp only
  obtain ⟨hqlower, hqupper⟩ := separation_factor_bounds Csep hCsep
  refine ⟨(logb_two_exponent_bounds _ hqlower hqupper).1,
    8 * Ccea ^ 2, by positivity, ?_⟩
  intro U _ _ _ x n hn hcea hsep
  let q : ℝ := max (3 / 2 : ℝ) (1 / 2 + 1 / (16 * Csep))⁻¹
  let E : ∀ I : Finset ℕ, I.Nonempty → I ⊆ Finset.Icc 1 n → ℝ :=
    maximalVariance U x n hn
  have hq : 1 ≤ q := le_trans (by norm_num) hqlower
  have hE : ∀ I hI hIn, 0 ≤ E I hI hIn := maximalVariance_nonneg U x n hn
  have hEmono : ∀ I J hI hJ hIn hJn, I ⊆ J → E I hI hIn ≤ E J hJ hJn :=
    maximalVariance_mono U x n hn
  have hEmerge : ∀ I J hI hJ hIn hJn,
      (∀ i ∈ I, ∀ j ∈ J, i < j) →
      E I hI hIn + E J hJ hJn ≤ q *
        E (I ∪ J) (hI.mono Finset.subset_union_left) (Finset.union_subset hIn hJn) :=
    HilbertSequence.maximalVariance_ordered_reduction U x n hn Csep hCsep hsep
  have hpair : ∀ i (hi : 1 ≤ i) (hin : i < n),
      ‖x (i + 1) - x i‖ ^ 2 ≤ 4 * E {i, i + 1} (Finset.insert_nonempty _ _)
        (by intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            simp only [Finset.mem_Icc]; omega) := by
    intro i hi hin
    have hIn : ({i, i + 1} : Finset ℕ) ⊆ Finset.Icc 1 n := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      simp only [Finset.mem_Icc]
      omega
    have hp := pair_sq_distance_le_maximalVariance U x n hn {i, i + 1}
      (Finset.insert_nonempty _ _) hIn (i + 1) i
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      (Finset.mem_insert_self _ _)
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hp |>.trans_eq (mul_comm _ _)
  have hsum := finite_energy_sum_le n hn E q 4 hq (by norm_num) hE hEmono hEmerge
    (fun i => ‖x (i + 1) - x i‖ ^ 2) hpair
  have hfull := maximalVariance_le_cea_endpoint U x n hn Ccea hCcea hcea
    (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) (Finset.Subset.refl _)
  have hpow : 0 ≤ (n : ℝ) ^ Real.logb 2 q := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hexp : (1 : ℝ) - (1 - Real.logb 2 q) = Real.logb 2 q := by ring
  change (∑ i ∈ Finset.Ico 1 n, ‖x (i + 1) - x i‖ ^ 2) ≤
    (8 * Ccea ^ 2) * (n : ℝ) ^ (1 - (1 - Real.logb 2 q)) * ‖x n - x 1‖ ^ 2
  rw [hexp]
  calc
    _ ≤ (2 * 4) * (n : ℝ) ^ Real.logb 2 q *
        E (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) (Finset.Subset.refl _) := hsum
    _ ≤ (2 * 4) * (n : ℝ) ^ Real.logb 2 q *
        (Ccea ^ 2 * ‖x n - x 1‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hfull (mul_nonneg (by norm_num) hpow)
    _ = _ := by ring

end Autoformalization.HilbertSequence.Provider
