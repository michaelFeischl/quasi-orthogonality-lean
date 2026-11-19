module

public import Autoformalization.PetrovGalerkin.Cea
public import Autoformalization.PetrovGalerkin.PGVarianceBounds
public import Autoformalization.PetrovGalerkin.WeightedSeparation
public import Autoformalization.PetrovGalerkin.SeparationGain
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Petrov–Galerkin checks for the abstract sequence assumptions

The transformed Céa comparison and convex separation in Section 2 of the revised
`sources/main.tex`. The separation constant is the corrected `4 L^4 M^4 / α^4`.
-/

public section
namespace Autoformalization.PetrovGalerkin

/-- Four ordered transformed solutions satisfy the source Céa constant. -/
theorem norm_image_sub_le_cea_cube_mul_norm_image_sub
    {U V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (A : U → V →L[ℝ] ℝ) (T : U → V)
    (Uj : ℕ → Submodule ℝ U) (Vj : ℕ → Submodule ℝ V)
    (L M α : ℝ) (hL : 0 < L) (hM : 0 < M) (hα : 0 < α)
    (hU : Monotone Uj) (hV : Monotone Vj)
    (hA : ∀ x y : U, ‖A x - A y‖ ≤ L * ‖x - y‖)
    (hmaps : ∀ j, Set.MapsTo T (Uj j) (Vj j))
    (hT : ∀ j, ∀ x ∈ Uj j, ∀ y ∈ Uj j, ‖T x - T y‖ ≤ M * ‖x - y‖)
    (hmono : ∀ j, ∀ x ∈ Uj j, ∀ y ∈ Uj j,
      α * ‖x - y‖ ^ 2 ≤ (A x - A y) (T x - T y))
    (f : V →L[ℝ] ℝ) (u : ℕ → U) (hu : ∀ j, u j ∈ Uj j)
    (hgal : ∀ j, ∀ z ∈ Vj j, A (u j) z = f z)
    {i j k l : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    ‖T (u k) - T (u j)‖ ≤ (L * M / α) ^ 3 * ‖T (u l) - T (u i)‖ := by
  have hcea := norm_sub_le_cea_sq_mul_norm_sub A T Uj Vj L M α hL hM hα
    hU hV hA hmaps hT hmono f u hu hgal hij hjk hkl
  have hinv := norm_sub_le_mul_norm_image_sub A T L α hL hα (u l) (u i)
    (hA (u l) (u i))
    (hmono l (u l) (hu l) (u i) (hU (hij.trans (hjk.trans hkl)) (hu i)))
  calc
    ‖T (u k) - T (u j)‖ ≤ M * ‖u k - u j‖ :=
      hT k (u k) (hu k) (u j) (hU hjk (hu j))
    _ ≤ M * ((L * M / α) ^ 2 * ‖u l - u i‖) :=
      mul_le_mul_of_nonneg_left hcea hM.le
    _ ≤ M * ((L * M / α) ^ 2 * ((L / α) * ‖T (u l) - T (u i)‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinv (sq_nonneg _)) hM.le
    _ = (L * M / α) ^ 3 * ‖T (u l) - T (u i)‖ := by ring

section Separation

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (A : U → V →L[ℝ] ℝ) (T : U → V)
  (Uj : ℕ → Submodule ℝ U) (Vj : ℕ → Submodule ℝ V)
  (L M α : ℝ) (hL : 0 < L) (hM : 0 < M) (hα : 0 < α)
  (hU : Monotone Uj) (hV : Monotone Vj)
  (hA : ∀ x y : U, ‖A x - A y‖ ≤ L * ‖x - y‖)
  (hmaps : ∀ j, Set.MapsTo T (Uj j) (Vj j))
  (hT : ∀ j, ∀ x ∈ Uj j, ∀ y ∈ Uj j, ‖T x - T y‖ ≤ M * ‖x - y‖)
  (hmono : ∀ j, ∀ x ∈ Uj j, ∀ y ∈ Uj j,
    α * ‖x - y‖ ^ 2 ≤ (A x - A y) (T x - T y))
  (f : V →L[ℝ] ℝ) (u : ℕ → U) (hu : ∀ j, u j ∈ Uj j)
  (hgal : ∀ j, ∀ z ∈ Vj j, A (u j) z = f z)

include hU hV hA hmaps hmono hu hgal

omit [CompleteSpace U] [CompleteSpace V] in
/-- A weighted later Galerkin block is separated from every point in an earlier
 test space. Membership in that space is discharged by convexity below. -/
theorem weighted_separation_of_mem (J : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ j ∈ J, 0 ≤ w j) {a b : ℕ} (hab : a ≤ b)
    (hJ : ∀ j ∈ J, a ≤ j ∧ j ≤ b) (v : V) (hv : v ∈ Vj a) :
    α * (∑ j ∈ J, w j * ‖u j - u a‖ ^ 2) ≤
      L * ‖u b - u a‖ * ‖(∑ j ∈ J, w j • T (u j)) - v‖ := by
  have hpair := weighted_galerkin_pairing A T Uj Vj hV hmaps f u hu hgal
    ∅ J (fun _ => 0) w hab (by simp only [Finset.notMem_empty, false_implies, implies_true]) hJ
  simp only [Finset.sum_empty, sub_zero] at hpair
  have hzero := galerkin_sub_apply_eq_zero A Vj hV f u hgal hab hv
  have hsum : α * (∑ j ∈ J, w j * ‖u j - u a‖ ^ 2) ≤
      ∑ j ∈ J, w j * ((A (u j) - A (u a)) (T (u j) - T (u a))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    calc
      α * (w j * ‖u j - u a‖ ^ 2) = w j * (α * ‖u j - u a‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hmono j (u j) (hu j) (u a) (hU (hJ j hj).1 (hu a))) (hw j hj)
  calc
    _ ≤ (A (u b) - A (u a)) (∑ j ∈ J, w j • T (u j)) := by rw [hpair]; exact hsum
    _ = (A (u b) - A (u a)) ((∑ j ∈ J, w j • T (u j)) - v) := by
      rw [map_sub, hzero, sub_zero]
    _ ≤ ‖A (u b) - A (u a)‖ * ‖(∑ j ∈ J, w j • T (u j)) - v‖ :=
      (le_abs_self _).trans ((A (u b) - A (u a)).le_opNorm _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (hA (u b) (u a)) (norm_nonneg _)

include hL hM hα hT

/-- Every maximizing variance mean is separated from the test space at the
 first index, with the corrected Section 2 constant. -/
theorem maximalVariance_separation_of_mem (n : ℕ) (hn : 1 ≤ n)
    (J : Finset ℕ) (hJ : J.Nonempty) (hJn : J ⊆ Finset.Icc 1 n)
    (w : ℕ → ℝ) (hw : ∀ j ∈ J, 0 ≤ w j ∧ w j ≤ 1)
    (hws : ∑ j ∈ J, w j = 1)
    (hwe : (∑ j ∈ J, w j * ‖T (u j) - ∑ k ∈ J, w k • T (u k)‖ ^ 2) =
      maximalVariance V (fun i => T (u i)) n hn J hJ hJn)
    (v : V) (hv : v ∈ Vj (J.min' hJ)) :
    maximalVariance V (fun i => T (u i)) n hn J hJ hJn ≤
      (4 * L ^ 4 * M ^ 4 / α ^ 4) * ‖(∑ j ∈ J, w j • T (u j)) - v‖ ^ 2 := by
  let a := J.min' hJ
  let b := J.max' hJ
  have ha : a ∈ J := J.min'_mem hJ
  have hb : b ∈ J := J.max'_mem hJ
  have hab : a ≤ b := J.min'_le_max' hJ
  have hJa : ∀ j ∈ J, a ≤ j := fun j hj => J.min'_le j hj
  have hJb : ∀ j ∈ J, j ≤ b := fun j hj => J.le_max' j hj
  have hvimage := weighted_image_variance_le T Uj hU u hu M hM.le hT
    J w (fun j hj => (hw j hj).1) hws hJa
  rw [hwe] at hvimage
  have hweighted := weighted_separation_of_mem A T Uj Vj L α hU hV hA hmaps
    hmono f u hu hgal J w (fun j hj => (hw j hj).1) hab
    (fun j hj => ⟨hJa j hj, hJb j hj⟩) v hv
  have hsep : α / M ^ 2 * maximalVariance V (fun i => T (u i)) n hn J hJ hJn ≤
      L * ‖u b - u a‖ * ‖(∑ j ∈ J, w j • T (u j)) - v‖ := calc
    _ ≤ α / M ^ 2 * (M ^ 2 * (∑ j ∈ J, w j * ‖u j - u a‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hvimage (by positivity)
    _ = α * (∑ j ∈ J, w j * ‖u j - u a‖ ^ 2) := by field_simp
    _ ≤ _ := hweighted
  have hend := endpoint_le_maximalVariance A T Uj L α hL hα hU hA hmono u hu
    n hn J hJ hJn a b ha hb
  have hgain := scalar_separation_gain L M α
    (maximalVariance V (fun i => T (u i)) n hn J hJ hJn)
    ‖u b - u a‖ ‖(∑ j ∈ J, w j • T (u j)) - v‖
    hL hM hα (maximalVariance_nonneg V (fun i => T (u i)) n hn J hJ hJn)
    (norm_nonneg _) (norm_nonneg _) hsep hend
  calc
    _ = (16 * L ^ 4 * M ^ 4 / α ^ 4) *
        (α ^ 4 / (16 * L ^ 4 * M ^ 4) *
          maximalVariance V (fun i => T (u i)) n hn J hJ hJn) := by field_simp
    _ ≤ (16 * L ^ 4 * M ^ 4 / α ^ 4) *
        (‖(∑ j ∈ J, w j • T (u j)) - v‖ ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left hgain (by positivity)
    _ = _ := by ring

end Separation
end Autoformalization.PetrovGalerkin
