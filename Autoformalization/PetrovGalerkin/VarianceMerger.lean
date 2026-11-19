module

public import Autoformalization.PetrovGalerkin.Frozen.VarianceCharacterization
public import Autoformalization.PetrovGalerkin.WeightedMixture

/-!
# Merger of maximum variances

Merging maximum variances using maximizing weights supplied by the
complete variance characterization.
-/

public section
namespace Autoformalization.PetrovGalerkin

/-- Equal mixing of two maximizing weights bounds the variance on their union. -/
theorem maximalVariance_merge
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (x : ℕ → V) (n : ℕ) (hn : 1 ≤ n)
    (I J : Finset ℕ) (hI : I.Nonempty) (hJ : J.Nonempty)
    (hIn : I ⊆ Finset.Icc 1 n) (hJn : J ⊆ Finset.Icc 1 n)
    (hIJ : Disjoint I J) (w v : ℕ → ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i ∧ w i ≤ 1)
    (hv : ∀ i ∈ J, 0 ≤ v i ∧ v i ≤ 1)
    (hws : ∑ i ∈ I, w i = 1) (hvs : ∑ i ∈ J, v i = 1)
    (hwe : (∑ i ∈ I, w i * ‖x i - ∑ j ∈ I, w j • x j‖ ^ 2) =
      maximalVariance V x n hn I hI hIn)
    (hve : (∑ i ∈ J, v i * ‖x i - ∑ j ∈ J, v j • x j‖ ^ 2) =
      maximalVariance V x n hn J hJ hJn) :
    (maximalVariance V x n hn I hI hIn + maximalVariance V x n hn J hJ hJn) / 2 +
      ‖(∑ i ∈ I, w i • x i) - (∑ j ∈ J, v j • x j)‖ ^ 2 / 4 ≤
        maximalVariance V x n hn (I ∪ J) (hI.mono Finset.subset_union_left)
          (Finset.union_subset hIn hJn) := by
  obtain ⟨m, hm, hms, hme⟩ := exists_half_mixture I J hIJ w v x hw hv hws hvs
  have h := (maximalVariance_characterization V x n hn (I ∪ J)
    (hI.mono Finset.subset_union_left) (Finset.union_subset hIn hJn)).1.2 m hm hms
  rw [hme, hwe, hve] at h
  exact h

end Autoformalization.PetrovGalerkin
