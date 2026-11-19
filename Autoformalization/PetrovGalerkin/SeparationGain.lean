module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar gain from weighted separation

The conditional arithmetic step in Section 1, Step 2 of `sources/main.tex`,
lines 202–215. Applications must separately prove the separation and endpoint
variance estimates. This module asserts no maximum-variance theorem.
-/

public section

namespace Autoformalization.PetrovGalerkin

/-- The separation estimate and the two-point endpoint bound imply the
additional variance gain, including the zero-variance case. -/
theorem scalar_separation_gain (L M α e d s : ℝ)
    (hL : 0 < L) (hM : 0 < M) (hα : 0 < α)
    (he : 0 ≤ e) (hd : 0 ≤ d) (hs : 0 ≤ s)
    (hsep : α / M ^ 2 * e ≤ L * d * s)
    (hend : α ^ 2 / (4 * L ^ 2) * d ^ 2 ≤ e) :
    α ^ 4 / (16 * L ^ 4 * M ^ 4) * e ≤ s ^ 2 / 4 := by
  rcases eq_or_lt_of_le he with hezero | hepos
  · rw [← hezero, mul_zero]
    exact div_nonneg (sq_nonneg _) (by norm_num)
  have hM2 : 0 < M ^ 2 := sq_pos_of_pos hM
  have h4L2 : 0 < 4 * L ^ 2 := by positivity
  have hsep' : α * e ≤ L * d * s * M ^ 2 := by
    rw [div_mul_eq_mul_div] at hsep
    exact (div_le_iff₀ hM2).mp hsep
  have hend' : α ^ 2 * d ^ 2 ≤ e * (4 * L ^ 2) := by
    rw [div_mul_eq_mul_div] at hend
    exact (div_le_iff₀ h4L2).mp hend
  have hsq : (α * e) ^ 2 ≤ (L * d * s * M ^ 2) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hα.le he) (by positivity)).mpr hsep'
  have hbound : α ^ 4 * e ^ 2 ≤ (4 * L ^ 4 * M ^ 4 * s ^ 2) * e := calc
    α ^ 4 * e ^ 2 = α ^ 2 * (α * e) ^ 2 := by ring
    _ ≤ α ^ 2 * (L * d * s * M ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = (L ^ 2 * M ^ 4 * s ^ 2) * (α ^ 2 * d ^ 2) := by ring
    _ ≤ (L ^ 2 * M ^ 4 * s ^ 2) * (e * (4 * L ^ 2)) :=
      mul_le_mul_of_nonneg_left hend' (by positivity)
    _ = (4 * L ^ 4 * M ^ 4 * s ^ 2) * e := by ring
  have hcancel : α ^ 4 * e ≤ 4 * L ^ 4 * M ^ 4 * s ^ 2 := by
    apply (mul_le_mul_iff_left₀ hepos).mp
    simpa only [pow_two, mul_assoc] using hbound
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 16 * L ^ 4 * M ^ 4)).mpr
  calc
    α ^ 4 * e ≤ 4 * L ^ 4 * M ^ 4 * s ^ 2 := hcancel
    _ = s ^ 2 / 4 * (16 * L ^ 4 * M ^ 4) := by ring

end Autoformalization.PetrovGalerkin
