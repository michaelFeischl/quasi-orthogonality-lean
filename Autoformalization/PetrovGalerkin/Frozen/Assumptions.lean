module
public import Autoformalization.PetrovGalerkin.Frozen.VarianceCharacterization
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Autoformalization.PetrovGalerkin.Providers.Assumptions

public section
universe u v
namespace Autoformalization.PetrovGalerkin

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
by exact Autoformalization.PetrovGalerkin.Provider.petrov_galerkin_assumptions

end Autoformalization.PetrovGalerkin
