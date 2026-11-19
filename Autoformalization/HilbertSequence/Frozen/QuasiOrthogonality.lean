-- FROZEN_ANCHOR_PREFIX_BEGIN
module
public import Autoformalization.PetrovGalerkin.Frozen.VarianceCharacterization
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Autoformalization.HilbertSequence.Providers.QuasiOrthogonality

public section
universe u
namespace Autoformalization.HilbertSequence

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
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact Autoformalization.HilbertSequence.Provider.quasi_orthogonality
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end Autoformalization.HilbertSequence
-- FROZEN_ANCHOR_SUFFIX_END
