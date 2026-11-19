module
public import Autoformalization.PetrovGalerkin.Frozen.VarianceExistence

public section
universe v
namespace Autoformalization.PetrovGalerkin

@[expose] noncomputable def maximalVariance
    (V : Type v) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (x : ℕ → V) (n : ℕ) (hn : 1 ≤ n)
    (I : Finset ℕ) (hI : I.Nonempty) (hIn : I ⊆ Finset.Icc 1 n) : ℝ :=
  Classical.choose (exists_unique_maximal_variance V x n hn I hI hIn)

end Autoformalization.PetrovGalerkin
