module

public import Autoformalization.PetrovGalerkin.Cea
public import Autoformalization.PetrovGalerkin.WeightedVariance
import Mathlib.Tactic.Ring

/-!
# Weighted separation of ordered Galerkin index sets

Finite-sum separation estimates for ordered Galerkin index sets.
-/

public section

namespace Autoformalization.PetrovGalerkin

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (A : U → V →L[ℝ] ℝ) (T : U → V)
  (Uj : ℕ → Submodule ℝ U) (Vj : ℕ → Submodule ℝ V)
  (hU : Monotone Uj) (hV : Monotone Vj)
  (hmaps : ∀ j, Set.MapsTo T (Uj j) (Vj j))
  (f : V →L[ℝ] ℝ) (u : ℕ → U) (hu : ∀ j, u j ∈ Uj j)
  (hgal : ∀ j, ∀ z ∈ Vj j, A (u j) z = f z)

include hV hmaps hu hgal

/-- Galerkin orthogonality rewrites the pairing between two weighted means. -/
theorem weighted_galerkin_pairing (I J : Finset ℕ) (w v : ℕ → ℝ)
    {a b : ℕ} (hab : a ≤ b) (hIa : ∀ i ∈ I, i ≤ a)
    (hJ : ∀ j ∈ J, a ≤ j ∧ j ≤ b) :
    (A (u b) - A (u a))
        ((∑ j ∈ J, v j • T (u j)) - (∑ i ∈ I, w i • T (u i))) =
      ∑ j ∈ J, v j * ((A (u j) - A (u a)) (T (u j) - T (u a))) := by
  have hzeroI (i : ℕ) (hi : i ∈ I) : (A (u b) - A (u a)) (T (u i)) = 0 :=
    galerkin_sub_apply_eq_zero A Vj hV f u hgal hab
      (hV (hIa i hi) (hmaps i (hu i)))
  have heqJ (j : ℕ) (hj : j ∈ J) :
      (A (u b) - A (u a)) (T (u j)) =
        (A (u j) - A (u a)) (T (u j) - T (u a)) := by
    have hzero := galerkin_sub_apply_eq_zero A Vj hV f u hgal (hJ j hj).1
      (hmaps a (hu a))
    rw [map_sub, hzero, sub_zero, sub_apply, sub_apply,
      hgal b _ (hV (hJ j hj).2 (hmaps j (hu j))), hgal j _ (hmaps j (hu j))]
  rw [map_sub, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]
  have hleft : (∑ i ∈ I, w i * (A (u b) - A (u a)) (T (u i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzeroI i hi, mul_zero]
  rw [hleft, sub_zero]
  exact Finset.sum_congr rfl (fun j hj => congrArg (v j * ·) (heqJ j hj))

include hU

/-- Strong monotonicity separates the two weighted means in norm. -/
theorem weighted_separation (L α : ℝ)
    (hA : ∀ x y : U, ‖A x - A y‖ ≤ L * ‖x - y‖)
    (hmono : ∀ j, ∀ x ∈ Uj j, ∀ y ∈ Uj j,
      α * ‖x - y‖ ^ 2 ≤ (A x - A y) (T x - T y))
    (I J : Finset ℕ) (w v : ℕ → ℝ) (hv : ∀ j ∈ J, 0 ≤ v j)
    {a b : ℕ} (hab : a ≤ b) (hIa : ∀ i ∈ I, i ≤ a)
    (hJ : ∀ j ∈ J, a ≤ j ∧ j ≤ b) :
    α * (∑ j ∈ J, v j * ‖u j - u a‖ ^ 2) ≤
      L * ‖u b - u a‖ *
        ‖(∑ i ∈ I, w i • T (u i)) - (∑ j ∈ J, v j • T (u j))‖ := by
  have hsum : α * (∑ j ∈ J, v j * ‖u j - u a‖ ^ 2) ≤
      ∑ j ∈ J, v j * ((A (u j) - A (u a)) (T (u j) - T (u a))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    calc
      α * (v j * ‖u j - u a‖ ^ 2) = v j * (α * ‖u j - u a‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hmono j (u j) (hu j) (u a) (hU (hJ j hj).1 (hu a))) (hv j hj)
  rw [← weighted_galerkin_pairing A T Uj Vj hV hmaps f u hu hgal I J w v hab hIa hJ]
    at hsum
  calc
    _ ≤ _ := hsum
    _ ≤ ‖A (u b) - A (u a)‖ *
        ‖(∑ j ∈ J, v j • T (u j)) - (∑ i ∈ I, w i • T (u i))‖ :=
      (le_abs_self _).trans ((A (u b) - A (u a)).le_opNorm _)
    _ ≤ (L * ‖u b - u a‖) *
        ‖(∑ j ∈ J, v j • T (u j)) - (∑ i ∈ I, w i • T (u i))‖ :=
      mul_le_mul_of_nonneg_right (hA (u b) (u a)) (norm_nonneg _)
    _ = _ := by rw [norm_sub_rev (∑ j ∈ J, v j • T (u j)) (∑ i ∈ I, w i • T (u i))]

omit hV hmaps hgal

/-- The variance of the transformed points is controlled by distance to any
common earlier discrete point. -/
theorem weighted_image_variance_le (M : ℝ) (hM : 0 ≤ M)
    (hT : ∀ j, ∀ x ∈ Uj j, ∀ y ∈ Uj j, ‖T x - T y‖ ≤ M * ‖x - y‖)
    (J : Finset ℕ) (v : ℕ → ℝ) (hv : ∀ j ∈ J, 0 ≤ v j)
    (hv_sum : ∑ j ∈ J, v j = 1) {a : ℕ} (hJa : ∀ j ∈ J, a ≤ j) :
    (∑ j ∈ J, v j * ‖T (u j) - ∑ i ∈ J, v i • T (u i)‖ ^ 2) ≤
      M ^ 2 * (∑ j ∈ J, v j * ‖u j - u a‖ ^ 2) := by
  calc
    _ ≤ ∑ j ∈ J, v j * ‖T (u j) - T (u a)‖ ^ 2 :=
      weighted_mean_minimizes J v (fun j => T (u j)) hv_sum (T (u a))
    _ ≤ ∑ j ∈ J, v j * (M * ‖u j - u a‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (hv j hj)
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mpr
        (hT j (u j) (hu j) (u a) (hU (hJa j hj) (hu a)))
    _ = _ := by
      simp only [mul_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

end Autoformalization.PetrovGalerkin
