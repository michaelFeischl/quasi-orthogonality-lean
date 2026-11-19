module

public import Autoformalization.PetrovGalerkin.AssumptionEstimates
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Positivity

/-!
# Verification of the abstract sequence assumptions

Section 2 of the revised `sources/main.tex`: the transformed solutions satisfy
both checks with their explicit constants. The corrected separation coefficient
is `4 L^4 M^4 / α^4`; no estimate is added to the standing source hypotheses.
-/

public section
universe u v
namespace Autoformalization.PetrovGalerkin.Provider

theorem petrov_galerkin_assumptions :
    ∀ (L M α : ℝ) (hL : 0 < L) (hM : 0 < M) (hα : 0 < α)
      (U : Type u) (V : Type v)
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
        0 < (L * M / α) ^ 3 ∧
        0 < 4 * L ^ 4 * M ^ 4 / α ^ 4 ∧
        (∀ i j k l : ℕ, i ≤ j → j ≤ k → k ≤ l →
          ‖T (u k) - T (u j)‖ ≤
            (L * M / α) ^ 3 * ‖T (u l) - T (u i)‖) ∧
        ∀ (n : ℕ) (hn : 1 ≤ n)
          (J : Finset ℕ) (hJ : J.Nonempty) (hJn : J ⊆ Finset.Icc 1 n)
          (w : ℕ → ℝ),
          (∀ j ∈ J, 0 ≤ w j ∧ w j ≤ 1) →
          (∑ j ∈ J, w j) = 1 →
          (∑ j ∈ J, w j * ‖T (u j) - ∑ k ∈ J, w k • T (u k)‖ ^ 2) =
            maximalVariance V (fun i => T (u i)) n hn J hJ hJn →
          ∀ v ∈ convexHull ℝ
            ((fun i => T (u i)) ''
              {i : ℕ | 1 ≤ i ∧ i ≤ n ∧ ∀ j ∈ J, i ≤ j}),
            maximalVariance V (fun i => T (u i)) n hn J hJ hJn ≤
              (4 * L ^ 4 * M ^ 4 / α ^ 4) *
                ‖(∑ j ∈ J, w j • T (u j)) - v‖ ^ 2 :=
by
  intro L M α hL hM hα U V _ _ _ _ _ _ A T Uj Vj _ _ hUn hVn hA _ hmaps _
    hT hmono f u hu hgal
  have hU : Monotone Uj := monotone_nat_of_le_succ hUn
  have hV : Monotone Vj := monotone_nat_of_le_succ hVn
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · intro i j k l hij hjk hkl
    exact norm_image_sub_le_cea_cube_mul_norm_image_sub A T Uj Vj L M α hL hM hα
      hU hV hA hmaps hT hmono f u hu hgal hij hjk hkl
  · intro n hn J hJ hJn w hw hws hwe v hv
    have hmem : v ∈ Vj (J.min' hJ) := by
      apply convexHull_min (t := (Vj (J.min' hJ) : Set V)) ?_
        (Vj (J.min' hJ)).convex hv
      rintro z ⟨i, hi, rfl⟩
      exact hV (hi.2.2 (J.min' hJ) (J.min'_mem hJ)) (hmaps i (hu i))
    exact maximalVariance_separation_of_mem A T Uj Vj L M α hL hM hα
      hU hV hA hmaps hT hmono f u hu hgal n hn J hJ hJn w hw hws hwe v hmem

end Autoformalization.PetrovGalerkin.Provider
