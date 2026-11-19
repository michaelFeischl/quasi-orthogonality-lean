module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Autoformalization.PetrovGalerkin.VarianceReduction
public import Autoformalization.PetrovGalerkin.DyadicAggregation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform quasi-orthogonality

The characterized variance and Galerkin estimates supply the energy bounds.
The resulting constant depends only on the Lipschitz and monotonicity constants.
-/

public section
universe u v
namespace Autoformalization.PetrovGalerkin.Provider

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
              C * Real.rpow (n : ℝ) (1 - δ) * ‖u n - u 1‖ ^ 2 := by
  intro L M α hL hM hα
  dsimp only
  refine ⟨(quasi_orthogonality_exponent_bounds L M α hL hM hα).1,
    8 * (L * M / α) ^ 4, by positivity, ?_⟩
  intro U V _ _ _ _ _ _ A T Uj Vj _ _ hUn hVn hA _ hmaps _ hT hmono f u hu hgal n hn
  have hU : Monotone Uj := monotone_nat_of_le_succ hUn
  have hV : Monotone Vj := monotone_nat_of_le_succ hVn
  let q : ℝ := max (3 / 2 : ℝ) (1 / 2 + α ^ 4 / (64 * L ^ 4 * M ^ 4))⁻¹
  let B : ℝ := 4 * L ^ 2 / α ^ 2
  let E : ∀ I : Finset ℕ, I.Nonempty → I ⊆ Finset.Icc 1 n → ℝ :=
    maximalVariance V (fun i => T (u i)) n hn
  have hq : 1 ≤ q := le_trans (by norm_num)
    (quasi_orthogonality_factor_bounds L M α hL hM hα).1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE : ∀ I hI hIn, 0 ≤ E I hI hIn :=
    maximalVariance_nonneg V (fun i => T (u i)) n hn
  have hEmono : ∀ I J hI hJ hIn hJn, I ⊆ J → E I hI hIn ≤ E J hJ hJn :=
    maximalVariance_mono V (fun i => T (u i)) n hn
  have hEmerge : ∀ I J hI hJ hIn hJn,
      (∀ i ∈ I, ∀ j ∈ J, i < j) →
      E I hI hIn + E J hJ hJn ≤ q *
        E (I ∪ J) (hI.mono Finset.subset_union_left) (Finset.union_subset hIn hJn) :=
    maximalVariance_ordered_reduction A T Uj Vj L M α hL hM hα hU hV hA
      hmaps hT hmono f u hu hgal n hn
  have hpair : ∀ i (hi : 1 ≤ i) (hin : i < n),
      ‖u (i + 1) - u i‖ ^ 2 ≤ B * E {i, i + 1} (Finset.insert_nonempty _ _)
        (by intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            simp only [Finset.mem_Icc]; omega) := by
    intro i hi hin
    have hIn : ({i, i + 1} : Finset ℕ) ⊆ Finset.Icc 1 n := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      simp only [Finset.mem_Icc]
      omega
    have hp := endpoint_le_maximalVariance A T Uj L α hL hα hU hA hmono u hu n hn
      {i, i + 1} (Finset.insert_nonempty _ _) hIn i (i + 1)
      (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    calc
      _ = B * (α ^ 2 / (4 * L ^ 2) * ‖u (i + 1) - u i‖ ^ 2) := by
        dsimp [B]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hB
  have hsum := finite_energy_sum_le n hn E q B hq hB hE hEmono hEmerge
    (fun i => ‖u (i + 1) - u i‖ ^ 2) hpair
  have hfull := maximalVariance_le_galerkin_endpoint A T Uj Vj L M α hL hM hα
    hU hV hA hmaps hT hmono f u hu hgal n hn (Finset.Icc 1 n)
    (Finset.nonempty_Icc.mpr hn) (Finset.Subset.refl _)
  have hpow : 0 ≤ (n : ℝ) ^ Real.logb 2 q := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hexp : (1 : ℝ) - (1 - Real.logb 2 q) = Real.logb 2 q := by ring
  change (∑ i ∈ Finset.Ico 1 n, ‖u (i + 1) - u i‖ ^ 2) ≤
    (8 * (L * M / α) ^ 4) * (n : ℝ) ^ (1 - (1 - Real.logb 2 q)) * ‖u n - u 1‖ ^ 2
  rw [hexp]
  calc
    _ ≤ (2 * B) * (n : ℝ) ^ Real.logb 2 q *
        E (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) (Finset.Subset.refl _) := hsum
    _ ≤ (2 * B) * (n : ℝ) ^ Real.logb 2 q *
        (M ^ 2 * (L * M / α) ^ 2 * ‖u n - u 1‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hfull (mul_nonneg (mul_nonneg (by norm_num) hB) hpow)
    _ = _ := by dsimp [B]; ring

end Autoformalization.PetrovGalerkin.Provider
