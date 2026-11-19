/-
Copyright (c) 2026. All rights reserved.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.Order.Compact

/-!
# Existence and uniqueness of the maximal variance value

The finite simplex is compact and the weighted variance is continuous. Its maximum
extends to weights on the natural numbers; only the maximum value is unique.
This quarantined provider implements the approved source anchor at main.tex:170–180.
-/

public section

universe v

namespace Autoformalization.PetrovGalerkin.Provider

/-- A nonempty finite family has a uniquely determined attained maximal variance value. -/
theorem exists_unique_maximal_variance :
    ∀ (V : Type v) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [CompleteSpace V] (x : ℕ → V) (n : ℕ),
      1 ≤ n → ∀ I : Finset ℕ, I.Nonempty → I ⊆ Finset.Icc 1 n →
      ∃! E : ℝ,
        (∃ w : ℕ → ℝ,
          (∀ i ∈ I, 0 ≤ w i ∧ w i ≤ 1) ∧
          (∑ i ∈ I, w i) = 1 ∧
          (∑ i ∈ I, w i * ‖x i - ∑ j ∈ I, w j • x j‖ ^ 2) = E) ∧
        (∀ w : ℕ → ℝ,
          (∀ i ∈ I, 0 ≤ w i ∧ w i ≤ 1) →
          (∑ i ∈ I, w i) = 1 →
          (∑ i ∈ I, w i * ‖x i - ∑ j ∈ I, w j • x j‖ ^ 2) ≤ E) := by
  classical
  intro V _ _ _ x n _ I hI _
  let S := Convexity.StdSimplex ℝ I
  let extend : S → ℕ → ℝ := fun s i => if hi : i ∈ I then s.weights ⟨i, hi⟩ else 0
  have extend_apply (s : S) (i : ℕ) (hi : i ∈ I) :
      extend s i = s.weights ⟨i, hi⟩ := dite_eq_left hi
  have extend_continuous (i : ℕ) : Continuous (fun s : S => extend s i) := by
    by_cases hi : i ∈ I
    · simpa only [extend, dite_eq_left hi] using
        (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) (⟨i, hi⟩ : I))
    · simp only [extend, dite_eq_right hi]
      exact continuous_const
  have extend_bounds (s : S) : ∀ i ∈ I, 0 ≤ extend s i ∧ extend s i ≤ 1 := by
    intro i hi
    rw [extend_apply s i hi]
    exact ⟨s.weights_nonneg _, s.weights_apply_le_one _⟩
  have extend_total (s : S) : ∑ i ∈ I, extend s i = 1 := by
    rw [← Finset.sum_coe_sort]
    simp only [extend_apply s _ (Subtype.prop _)]
    exact s.total_of_fintype
  let variance : (ℕ → ℝ) → ℝ := fun w =>
    ∑ i ∈ I, w i * ‖x i - ∑ j ∈ I, w j • x j‖ ^ 2
  have variance_congr {w z : ℕ → ℝ} (h : ∀ i ∈ I, w i = z i) :
      variance w = variance z := by
    have hmean : (∑ j ∈ I, w j • x j) = ∑ j ∈ I, z j • x j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [h j hj]
    dsimp only [variance]
    rw [hmean]
    apply Finset.sum_congr rfl
    intro i hi
    rw [h i hi]
  have continuous_mean : Continuous (fun s : S => ∑ j ∈ I, extend s j • x j) := by
    exact continuous_finsetSum I (fun j _ => (extend_continuous j).smul continuous_const)
  have continuous_variance : Continuous (fun s : S => variance (extend s)) := by
    exact continuous_finsetSum I (fun i _ =>
      (extend_continuous i).mul ((continuous_const.sub continuous_mean).norm.pow 2))
  have nonempty_simplex : Nonempty S := by
    obtain ⟨i, hi⟩ := hI
    exact ⟨Convexity.StdSimplex.single ⟨i, hi⟩⟩
  let : Nonempty S := nonempty_simplex
  obtain ⟨s, _, hs⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set S).Nonempty) continuous_variance.continuousOn
  have upper_bound (w : ℕ → ℝ) (hw : ∀ i ∈ I, 0 ≤ w i ∧ w i ≤ 1)
      (ht : ∑ i ∈ I, w i = 1) : variance w ≤ variance (extend s) := by
    let t : S := {
      weights := Finsupp.equivFunOnFinite.symm (fun i : I => w i)
      nonneg := by
        intro i
        exact (hw i i.property).1
      total := by
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
        simpa only [Finsupp.coe_equivFunOnFinite_symm, Finset.sum_coe_sort] using ht }
    have heq : variance (extend t) = variance w := by
      apply variance_congr
      intro i hi
      rw [extend_apply t i hi]
      rfl
    rw [← heq]
    exact hs (Set.mem_univ t)
  refine ⟨variance (extend s), ⟨?_, upper_bound⟩, ?_⟩
  · exact ⟨extend s, extend_bounds s, extend_total s, rfl⟩
  · intro E hE
    obtain ⟨⟨w, hw, ht, hvalue⟩, hupper⟩ := hE
    apply le_antisymm
    · rw [← hvalue]
      exact upper_bound w hw ht
    · exact hupper (extend s) (extend_bounds s) (extend_total s)

end Autoformalization.PetrovGalerkin.Provider
