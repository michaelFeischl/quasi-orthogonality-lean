module

public import Autoformalization.PetrovGalerkin.VarianceBasic
public import Autoformalization.PetrovGalerkin.InverseEstimate
public import Autoformalization.PetrovGalerkin.Cea
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Endpoint bounds for Petrov–Galerkin variance

Two-point lower bounds and total-variance upper bounds on nonempty index sets.
-/

public section
namespace Autoformalization.PetrovGalerkin

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

include hL hα hU hA hmono hu

/-- Any two indices in a variance set control their trial-space distance. -/
theorem endpoint_le_maximalVariance (n : ℕ) (hn : 1 ≤ n)
    (I : Finset ℕ) (hI : I.Nonempty) (hIn : I ⊆ Finset.Icc 1 n)
    (a b : ℕ) (ha : a ∈ I) (hb : b ∈ I) :
    α ^ 2 / (4 * L ^ 2) * ‖u b - u a‖ ^ 2 ≤
      maximalVariance V (fun i => T (u i)) n hn I hI hIn := by
  have han : a ≤ n := (Finset.mem_Icc.mp (hIn ha)).2
  have hbn : b ≤ n := (Finset.mem_Icc.mp (hIn hb)).2
  have hinv := norm_sub_le_mul_norm_image_sub A T L α hL hα (u b) (u a)
    (hA (u b) (u a)) (hmono n (u b) (hU hbn (hu b)) (u a) (hU han (hu a)))
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hinv
  calc
    _ ≤ α ^ 2 / (4 * L ^ 2) * ((L / α) * ‖T (u b) - T (u a)‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = ‖T (u b) - T (u a)‖ ^ 2 / 4 := by
      field_simp
    _ ≤ _ := pair_sq_distance_le_maximalVariance V (fun i => T (u i)) n hn
      I hI hIn b a hb ha

include hM hV hmaps hT hgal

omit [CompleteSpace U] in
/-- All transformed solutions lie in a ball controlled by the final trial
increment, so every nonempty subset has the stated variance bound. -/
theorem maximalVariance_le_galerkin_endpoint (n : ℕ) (hn : 1 ≤ n)
    (I : Finset ℕ) (hI : I.Nonempty) (hIn : I ⊆ Finset.Icc 1 n) :
    maximalVariance V (fun i => T (u i)) n hn I hI hIn ≤
      M ^ 2 * (L * M / α) ^ 2 * ‖u n - u 1‖ ^ 2 := by
  apply maximalVariance_le_of_sq_distance_le V (fun i => T (u i)) n hn
    I hI hIn (T (u 1))
  intro i hi
  obtain ⟨h1i, hin⟩ := Finset.mem_Icc.mp (hIn hi)
  have hcea := norm_sub_le_cea_mul_norm_sub_right A T Uj Vj L M α hL hM hα
    hU hV hA hmaps hT hmono f u hu hgal h1i hin
  have hbound : ‖T (u i) - T (u 1)‖ ≤ M * ((L * M / α) * ‖u n - u 1‖) :=
    (hT i (u i) (hu i) (u 1) (hU h1i (hu 1))).trans
      (mul_le_mul_of_nonneg_left hcea hM.le)
  calc
    _ ≤ (M * ((L * M / α) * ‖u n - u 1‖)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbound
    _ = _ := by ring

end Autoformalization.PetrovGalerkin
