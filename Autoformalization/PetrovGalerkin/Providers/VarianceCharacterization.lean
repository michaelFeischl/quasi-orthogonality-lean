module
public import Autoformalization.PetrovGalerkin.Frozen.Variance

public section
universe v
namespace Autoformalization.PetrovGalerkin.Provider

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
        ∀ E : ℝ, P E → E = maximalVariance V x n hn I hI hIn := by
  intro V _ _ _ x n hn I hI hIn
  exact Classical.choose_spec (exists_unique_maximal_variance V x n hn I hI hIn)

end Autoformalization.PetrovGalerkin.Provider
