module

public import Autoformalization.PetrovGalerkin.VarianceBasic
public import Autoformalization.PetrovGalerkin.VarianceMerger
public import Autoformalization.PetrovGalerkin.ScalarReduction
public import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Variance estimates for separated Hilbert-space sequences

The variance bound and ordered reduction in Theorem 1 of `sources/main.tex`,
Section 1. The energies are the characterized maxima, and the only quantitative
premises are the source's Cea estimate and convex-hull separation estimate.
-/

public section
namespace Autoformalization.HilbertSequence

open Autoformalization.PetrovGalerkin

/-- The literal reduction factor associated with a positive separation constant. -/
theorem separation_factor_bounds (Csep : ℝ) (hCsep : 0 < Csep) :
    3 / 2 ≤ max (3 / 2 : ℝ) (1 / 2 + 1 / (16 * Csep))⁻¹ ∧
      max (3 / 2 : ℝ) (1 / 2 + 1 / (16 * Csep))⁻¹ < 2 := by
  have hquarter : (1 / (4 * Csep) : ℝ) / 4 = 1 / (16 * Csep) := by ring
  simpa only [hquarter] using reduction_factor_bounds (1 / (4 * Csep)) (by positivity)

variable (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [CompleteSpace U] (x : ℕ → U) (n : ℕ) (hn : 1 ≤ n)

/-- The Cea estimate bounds every variance by the original endpoint distance. -/
theorem maximalVariance_le_cea_endpoint (Ccea : ℝ) (hCcea : 0 < Ccea)
    (hcea : ∀ i j k l : ℕ, 1 ≤ i → i ≤ j → j ≤ k → k ≤ l → l ≤ n →
      ‖x k - x j‖ ≤ Ccea * ‖x l - x i‖)
    (I : Finset ℕ) (hI : I.Nonempty) (hIn : I ⊆ Finset.Icc 1 n) :
    maximalVariance U x n hn I hI hIn ≤ Ccea ^ 2 * ‖x n - x 1‖ ^ 2 := by
  apply maximalVariance_le_of_sq_distance_le U x n hn I hI hIn (x 1)
  intro i hi
  obtain ⟨h1i, hin⟩ := Finset.mem_Icc.mp (hIn hi)
  have hbound := hcea 1 1 i n (le_refl _) (le_refl _) h1i hin (le_refl _)
  calc
    ‖x i - x 1‖ ^ 2 ≤ (Ccea * ‖x n - x 1‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hCcea.le (norm_nonneg _))).mpr hbound
    _ = _ := mul_pow _ _ _

/-- Separation applied to the earlier maximizing mean gives ordered reduction. -/
theorem maximalVariance_ordered_reduction (Csep : ℝ) (hCsep : 0 < Csep)
    (hsep : ∀ (J : Finset ℕ) (hJ : J.Nonempty) (hJn : J ⊆ Finset.Icc 1 n)
      (w : ℕ → ℝ),
      (∀ j ∈ J, 0 ≤ w j ∧ w j ≤ 1) →
      (∑ j ∈ J, w j) = 1 →
      (∑ j ∈ J, w j * ‖x j - ∑ k ∈ J, w k • x k‖ ^ 2) =
        maximalVariance U x n hn J hJ hJn →
      ∀ v ∈ convexHull ℝ
        (x '' {i : ℕ | 1 ≤ i ∧ i ≤ n ∧ ∀ j ∈ J, i ≤ j}),
        maximalVariance U x n hn J hJ hJn ≤
          Csep * ‖(∑ j ∈ J, w j • x j) - v‖ ^ 2)
    (I J : Finset ℕ) (hI : I.Nonempty) (hJ : J.Nonempty)
    (hIn : I ⊆ Finset.Icc 1 n) (hJn : J ⊆ Finset.Icc 1 n)
    (horder : ∀ i ∈ I, ∀ j ∈ J, i < j) :
    maximalVariance U x n hn I hI hIn + maximalVariance U x n hn J hJ hJn ≤
      max (3 / 2 : ℝ) (1 / 2 + 1 / (16 * Csep))⁻¹ *
        maximalVariance U x n hn (I ∪ J)
          (hI.mono Finset.subset_union_left) (Finset.union_subset hIn hJn) := by
  have hdis : Disjoint I J := Finset.disjoint_left.mpr (by
    intro i hi hj
    exact (lt_irrefl i) (horder i hi i hj))
  obtain ⟨w, hw, hws, hwe⟩ := exists_weights_maximalVariance U x n hn I hI hIn
  obtain ⟨v, hv, hvs, hve⟩ := exists_weights_maximalVariance U x n hn J hJ hJn
  have hmem : (∑ i ∈ I, w i • x i) ∈ convexHull ℝ
      (x '' {i : ℕ | 1 ≤ i ∧ i ≤ n ∧ ∀ j ∈ J, i ≤ j}) := by
    apply (convex_convexHull ℝ _).sum_mem (fun i hi => (hw i hi).1) hws
    intro i hi
    apply subset_convexHull ℝ _
    obtain ⟨h1i, hin⟩ := Finset.mem_Icc.mp (hIn hi)
    exact ⟨i, ⟨h1i, hin, fun j hj => (horder i hi j hj).le⟩, rfl⟩
  have hseparated := hsep J hJ hJn v hv hvs hve _ hmem
  have hgap : (1 / (4 * Csep)) * maximalVariance U x n hn J hJ hJn ≤
      ‖(∑ i ∈ I, w i • x i) - (∑ j ∈ J, v j • x j)‖ ^ 2 / 4 := by
    have hdivide : maximalVariance U x n hn J hJ hJn / Csep ≤
        ‖(∑ j ∈ J, v j • x j) - (∑ i ∈ I, w i • x i)‖ ^ 2 :=
      (div_le_iff₀ hCsep).mpr (by simpa only [mul_comm Csep] using hseparated)
    calc
      _ = (maximalVariance U x n hn J hJ hJn / Csep) / 4 := by ring
      _ ≤ ‖(∑ j ∈ J, v j • x j) - (∑ i ∈ I, w i • x i)‖ ^ 2 / 4 :=
        div_le_div_of_nonneg_right hdivide (by norm_num)
      _ = _ := by rw [norm_sub_rev]
  have hmerge := maximalVariance_merge U x n hn I J hI hJ hIn hJn hdis
    w v hw hv hws hvs hwe hve
  have hgain := (add_le_add (le_refl
    ((maximalVariance U x n hn I hI hIn + maximalVariance U x n hn J hJ hJn) / 2))
    hgap).trans hmerge
  have hmono := maximalVariance_mono U x n hn I (I ∪ J)
    hI (hI.mono Finset.subset_union_left) hIn (Finset.union_subset hIn hJn)
    Finset.subset_union_left
  have h := scalar_reduction
    (maximalVariance U x n hn I hI hIn)
    (maximalVariance U x n hn J hJ hJn)
    (maximalVariance U x n hn (I ∪ J)
      (hI.mono Finset.subset_union_left) (Finset.union_subset hIn hJn))
    (1 / (4 * Csep))
    (maximalVariance_nonneg U x n hn I hI hIn)
    (maximalVariance_nonneg U x n hn J hJ hJn)
    (by positivity) hmono hgain
  have hquarter : (1 / (4 * Csep) : ℝ) / 4 = 1 / (16 * Csep) := by ring
  simpa only [hquarter] using h

end Autoformalization.HilbertSequence
