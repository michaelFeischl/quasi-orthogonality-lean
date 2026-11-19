/-
Copyright (c) 2026. All rights reserved.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar reduction and the quasi-orthogonality exponent

Arithmetic estimates for the scalar reduction and quasi-orthogonality exponent.
The reduction assumes monotonicity and merging inequalities.
-/

public section

namespace Autoformalization.PetrovGalerkin

/-- Positivity of the coefficient in `eq:quadest`. -/
theorem reduction_coefficient_pos (L M α : ℝ)
    (hL : 0 < L) (hM : 0 < M) (hα : 0 < α) :
    0 < α ^ 4 / (16 * L ^ 4 * M ^ 4) := by
  positivity

/-- The factor from the two scalar cases lies between `3/2` and `2`. -/
theorem reduction_factor_bounds (c : ℝ) (hc : 0 < c) :
    3 / 2 ≤ max (3 / 2 : ℝ) (1 / 2 + c / 4)⁻¹ ∧
      max (3 / 2 : ℝ) (1 / 2 + c / 4)⁻¹ < 2 := by
  refine ⟨le_max_left _ _, max_lt (by norm_num) ?_⟩
  have hden : 0 < (1 / 2 : ℝ) + c / 4 := by positivity
  rw [inv_eq_one_div, div_lt_iff₀ hden]
  linarith only [hc]

/-- The literal parameter in `thm:qo` satisfies the required strict bound,
without an additional relation between `α`, `L`, and `M`. -/
theorem quasi_orthogonality_factor_bounds (L M α : ℝ)
    (hL : 0 < L) (hM : 0 < M) (hα : 0 < α) :
    3 / 2 ≤ max (3 / 2 : ℝ) (1 / 2 + α ^ 4 / (64 * L ^ 4 * M ^ 4))⁻¹ ∧
      max (3 / 2 : ℝ) (1 / 2 + α ^ 4 / (64 * L ^ 4 * M ^ 4))⁻¹ < 2 := by
  have hquarter : α ^ 4 / (16 * L ^ 4 * M ^ 4) / 4 =
      α ^ 4 / (64 * L ^ 4 * M ^ 4) := by ring
  simpa only [hquarter] using reduction_factor_bounds
    (α ^ 4 / (16 * L ^ 4 * M ^ 4)) (reduction_coefficient_pos L M α hL hM hα)

/-- Scalar implication used in `eq:reduction`. Nonnegativity of `e` follows
from `ha` and `hmono`; `hmerge` must be proved by the variance argument. -/
theorem scalar_reduction (a b e c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 < c) (hmono : a ≤ e) (hmerge : (a + b) / 2 + c * b ≤ e) :
    a + b ≤ max (3 / 2 : ℝ) (1 / 2 + c / 4)⁻¹ * e := by
  have he : 0 ≤ e := ha.trans hmono
  by_cases hcase : a / 2 ≤ b
  · have hquarter : (a + b) / 4 ≤ b := by linarith only [hcase, hb]
    have hmul := mul_le_mul_of_nonneg_left hquarter hc.le
    have hbound : (a + b) * (1 / 2 + c / 4) ≤ e := by
      nlinarith only [hmerge, hmul]
    have hden : 0 < (1 / 2 : ℝ) + c / 4 := by positivity
    calc
      a + b ≤ e / (1 / 2 + c / 4) := (le_div_iff₀ hden).mpr hbound
      _ = (1 / 2 + c / 4)⁻¹ * e := by rw [div_eq_mul_inv, mul_comm]
      _ ≤ max (3 / 2 : ℝ) (1 / 2 + c / 4)⁻¹ * e :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) he
  · calc
      a + b ≤ (3 / 2 : ℝ) * a := by linarith only [hcase]
      _ ≤ (3 / 2 : ℝ) * e := mul_le_mul_of_nonneg_left hmono (by norm_num)
      _ ≤ max (3 / 2 : ℝ) (1 / 2 + c / 4)⁻¹ * e :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) he

/-- A factor in `[3/2,2)` gives a positive decay improvement and a
nonnegative exponent. -/
theorem logb_two_exponent_bounds (q : ℝ) (hlower : 3 / 2 ≤ q) (hupper : q < 2) :
    0 < 1 - Real.logb 2 q ∧ 0 ≤ Real.logb 2 q := by
  have hq : 0 < q := lt_of_lt_of_le (by norm_num) hlower
  have hlog : Real.logb 2 q < 1 := by
    apply (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) hq).mpr
    simpa only [Real.rpow_one] using hupper
  exact ⟨sub_pos.mpr hlog,
    Real.logb_nonneg (by norm_num) (le_trans (by norm_num) hlower)⟩

/-- Positivity of the literal `δ` from `thm:qo`, with its exponent bound. -/
theorem quasi_orthogonality_exponent_bounds (L M α : ℝ)
    (hL : 0 < L) (hM : 0 < M) (hα : 0 < α) :
    0 < 1 - Real.logb 2
      (max (3 / 2 : ℝ) (1 / 2 + α ^ 4 / (64 * L ^ 4 * M ^ 4))⁻¹) ∧
    0 ≤ Real.logb 2
      (max (3 / 2 : ℝ) (1 / 2 + α ^ 4 / (64 * L ^ 4 * M ^ 4))⁻¹) := by
  obtain ⟨hlower, hupper⟩ := quasi_orthogonality_factor_bounds L M α hL hM hα
  exact logb_two_exponent_bounds _ hlower hupper

/-- Change of base for the quasi-orthogonality exponent. -/
theorem rpow_logb_two_comm (q n : ℝ) (hq : 0 < q) (hn : 0 < n) :
    q ^ Real.logb 2 n = n ^ Real.logb 2 q := by
  rw [Real.rpow_def_of_pos hq, Real.rpow_def_of_pos hn, Real.logb, Real.logb]
  congr 1
  ring

end Autoformalization.PetrovGalerkin
