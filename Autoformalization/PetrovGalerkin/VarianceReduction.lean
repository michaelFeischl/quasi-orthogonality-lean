module

public import Autoformalization.PetrovGalerkin.PGVarianceBounds
public import Autoformalization.PetrovGalerkin.VarianceMerger
public import Autoformalization.PetrovGalerkin.WeightedSeparation
public import Autoformalization.PetrovGalerkin.SeparationGain
public import Autoformalization.PetrovGalerkin.ScalarReduction
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reduction for ordered Petrov–Galerkin variance sets

The source estimates `eq:quadest` and `eq:reduction`, sources/main.tex191–228.
All maximum, separation and endpoint premises are discharged inside these proofs.
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

include hL hM hα hU hV hA hmaps hT hmono hu hgal

/-- Ordered sets have a strict additional merger gain proportional to the later variance. -/
theorem maximalVariance_ordered_gain (n : ℕ) (hn : 1 ≤ n)
    (I J : Finset ℕ) (hI : I.Nonempty) (hJ : J.Nonempty)
    (hIn : I ⊆ Finset.Icc 1 n) (hJn : J ⊆ Finset.Icc 1 n)
    (horder : ∀ i ∈ I, ∀ j ∈ J, i < j) :
    (maximalVariance V (fun i => T (u i)) n hn I hI hIn +
      maximalVariance V (fun i => T (u i)) n hn J hJ hJn) / 2 +
      (α ^ 4 / (16 * L ^ 4 * M ^ 4)) *
        maximalVariance V (fun i => T (u i)) n hn J hJ hJn ≤
      maximalVariance V (fun i => T (u i)) n hn (I ∪ J)
        (hI.mono Finset.subset_union_left) (Finset.union_subset hIn hJn) := by
  have hdis : Disjoint I J := Finset.disjoint_left.mpr (by
    intro i hi hj
    exact (lt_irrefl i) (horder i hi i hj))
  obtain ⟨w, hw, hws, hwe⟩ := exists_weights_maximalVariance V (fun i => T (u i))
    n hn I hI hIn
  obtain ⟨v, hv, hvs, hve⟩ := exists_weights_maximalVariance V (fun i => T (u i))
    n hn J hJ hJn
  let a := J.min' hJ
  let b := J.max' hJ
  have ha : a ∈ J := J.min'_mem hJ
  have hb : b ∈ J := J.max'_mem hJ
  have hab : a ≤ b := J.min'_le_max' hJ
  have hJa : ∀ j ∈ J, a ≤ j := fun j hj => J.min'_le j hj
  have hJb : ∀ j ∈ J, j ≤ b := fun j hj => J.le_max' j hj
  have hIa : ∀ i ∈ I, i ≤ a := fun i hi => (horder i hi a ha).le
  have hvimage := weighted_image_variance_le T Uj hU u hu M hM.le hT
    J v (fun j hj => (hv j hj).1) hvs hJa
  rw [hve] at hvimage
  have hweighted := weighted_separation A T Uj Vj hU hV hmaps f u hu hgal
    L α hA hmono I J w v (fun j hj => (hv j hj).1) hab hIa
    (fun j hj => ⟨hJa j hj, hJb j hj⟩)
  have hsep : α / M ^ 2 * maximalVariance V (fun i => T (u i)) n hn J hJ hJn ≤
      L * ‖u b - u a‖ *
        ‖(∑ i ∈ I, w i • T (u i)) - (∑ j ∈ J, v j • T (u j))‖ := calc
    _ ≤ α / M ^ 2 * (M ^ 2 * (∑ j ∈ J, v j * ‖u j - u a‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hvimage (by positivity)
    _ = α * (∑ j ∈ J, v j * ‖u j - u a‖ ^ 2) := by field_simp
    _ ≤ _ := hweighted
  have hend := endpoint_le_maximalVariance A T Uj L α hL hα hU hA hmono u hu
    n hn J hJ hJn a b ha hb
  have hgain := scalar_separation_gain L M α
    (maximalVariance V (fun i => T (u i)) n hn J hJ hJn)
    ‖u b - u a‖ ‖(∑ i ∈ I, w i • T (u i)) - (∑ j ∈ J, v j • T (u j))‖
    hL hM hα (maximalVariance_nonneg V (fun i => T (u i)) n hn J hJ hJn)
    (norm_nonneg _) (norm_nonneg _) hsep hend
  have hmerge := maximalVariance_merge V (fun i => T (u i)) n hn I J hI hJ
    hIn hJn hdis w v hw hv hws hvs hwe hve
  exact (add_le_add (le_refl _) hgain).trans hmerge

/-- The two-case scalar argument gives the source reduction factor below two. -/
theorem maximalVariance_ordered_reduction (n : ℕ) (hn : 1 ≤ n)
    (I J : Finset ℕ) (hI : I.Nonempty) (hJ : J.Nonempty)
    (hIn : I ⊆ Finset.Icc 1 n) (hJn : J ⊆ Finset.Icc 1 n)
    (horder : ∀ i ∈ I, ∀ j ∈ J, i < j) :
    maximalVariance V (fun i => T (u i)) n hn I hI hIn +
      maximalVariance V (fun i => T (u i)) n hn J hJ hJn ≤
      max (3 / 2 : ℝ) (1 / 2 + α ^ 4 / (64 * L ^ 4 * M ^ 4))⁻¹ *
        maximalVariance V (fun i => T (u i)) n hn (I ∪ J)
          (hI.mono Finset.subset_union_left) (Finset.union_subset hIn hJn) := by
  have hgain := maximalVariance_ordered_gain A T Uj Vj L M α hL hM hα
    hU hV hA hmaps hT hmono f u hu hgal n hn I J hI hJ hIn hJn horder
  have hinc := maximalVariance_mono V (fun i => T (u i)) n hn I (I ∪ J)
    hI (hI.mono Finset.subset_union_left) hIn (Finset.union_subset hIn hJn)
    Finset.subset_union_left
  have h := scalar_reduction
    (maximalVariance V (fun i => T (u i)) n hn I hI hIn)
    (maximalVariance V (fun i => T (u i)) n hn J hJ hJn)
    (maximalVariance V (fun i => T (u i)) n hn (I ∪ J)
      (hI.mono Finset.subset_union_left) (Finset.union_subset hIn hJn))
    (α ^ 4 / (16 * L ^ 4 * M ^ 4))
    (maximalVariance_nonneg V (fun i => T (u i)) n hn I hI hIn)
    (maximalVariance_nonneg V (fun i => T (u i)) n hn J hJ hJn)
    (reduction_coefficient_pos L M α hL hM hα) hinc hgain
  have hquarter : α ^ 4 / (16 * L ^ 4 * M ^ 4) / 4 =
      α ^ 4 / (64 * L ^ 4 * M ^ 4) := by ring
  simpa only [hquarter] using h

end Autoformalization.PetrovGalerkin
