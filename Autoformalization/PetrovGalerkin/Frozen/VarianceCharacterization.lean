-- FROZEN_ANCHOR_PREFIX_BEGIN
module
public import Autoformalization.PetrovGalerkin.Frozen.Variance
import Autoformalization.PetrovGalerkin.Providers.VarianceCharacterization

public section
universe v
namespace Autoformalization.PetrovGalerkin

theorem maximalVariance_characterization :
    ∀ (V : Type v) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [CompleteSpace V] (x : ℕ → V) (n : ℕ) (hn : 1 ≤ n)
      (I : Finset ℕ) (hI : I.Nonempty) (hIn : I ⊆ Finset.Icc 1 n),
      let P : ℝ → Prop := fun E =>
        (∃ w : ℕ → ℝ,
          (∀ i ∈ I, 0 ≤ w i ∧ w i ≤ 1) ∧
          (∑ i ∈ I, w i) = 1 ∧
          (∑ i ∈ I, w i * ‖x i - ∑ j ∈ I, w j • x j‖ ^ 2) = E) ∧
        (∀ w : ℕ → ℝ,
          (∀ i ∈ I, 0 ≤ w i ∧ w i ≤ 1) →
          (∑ i ∈ I, w i) = 1 →
          (∑ i ∈ I, w i * ‖x i - ∑ j ∈ I, w j • x j‖ ^ 2) ≤ E)
      P (maximalVariance V x n hn I hI hIn) ∧
        ∀ E : ℝ, P E → E = maximalVariance V x n hn I hI hIn :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact Autoformalization.PetrovGalerkin.Provider.maximalVariance_characterization
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end Autoformalization.PetrovGalerkin
-- FROZEN_ANCHOR_SUFFIX_END
