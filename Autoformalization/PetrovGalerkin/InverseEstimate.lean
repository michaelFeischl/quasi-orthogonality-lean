/-
Copyright (c) 2026. All rights reserved.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Data.Set.Function
import Mathlib.Tactic.Ring

/-!
# Inverse estimates for the discrete Petrov–Galerkin map

These helpers establish the estimate and restricted bijectivity in
`sources/main.tex`, lines 85–93 (`eq:invLipschitz`). The pointwise hypotheses
are specializations of the source inequalities, not additional assumptions
for the frozen well-posedness theorem. No inverse object is defined here.
-/

public section

namespace Autoformalization.PetrovGalerkin

/-- The two inequalities in `eq:invLipschitz`, specialized to two points. -/
theorem pairing_norm_bounds
    {U V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (A : U → V →L[ℝ] ℝ) (T : U → V) (L α : ℝ) (x y : U)
    (hA : ‖A x - A y‖ ≤ L * ‖x - y‖)
    (hmono : α * ‖x - y‖ ^ 2 ≤ (A x - A y) (T x - T y)) :
    α * ‖x - y‖ ^ 2 ≤ ‖A x - A y‖ * ‖T x - T y‖ ∧
      ‖A x - A y‖ * ‖T x - T y‖ ≤ L * ‖x - y‖ * ‖T x - T y‖ := by
  constructor
  · exact hmono.trans ((le_abs_self _).trans ((A x - A y).le_opNorm (T x - T y)))
  · exact mul_le_mul_of_nonneg_right hA (norm_nonneg _)

/-- The inverse-Lipschitz estimate, before choosing an inverse. -/
theorem norm_sub_le_mul_norm_image_sub
    {U V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (A : U → V →L[ℝ] ℝ) (T : U → V) (L α : ℝ)
    (hL : 0 < L) (hα : 0 < α) (x y : U)
    (hA : ‖A x - A y‖ ≤ L * ‖x - y‖)
    (hmono : α * ‖x - y‖ ^ 2 ≤ (A x - A y) (T x - T y)) :
    ‖x - y‖ ≤ (L / α) * ‖T x - T y‖ := by
  obtain ⟨hfirst, hsecond⟩ := pairing_norm_bounds A T L α x y hA hmono
  have hbound : α * ‖x - y‖ ^ 2 ≤ (L * ‖T x - T y‖) * ‖x - y‖ := calc
    α * ‖x - y‖ ^ 2 ≤ L * ‖x - y‖ * ‖T x - T y‖ := hfirst.trans hsecond
    _ = (L * ‖T x - T y‖) * ‖x - y‖ := by ring
  rcases eq_or_lt_of_le (norm_nonneg (x - y)) with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg (div_nonneg (le_of_lt hL) (le_of_lt hα)) (norm_nonneg _)
  · rw [pow_two, ← mul_assoc] at hbound
    have hcancel : α * ‖x - y‖ ≤ L * ‖T x - T y‖ :=
      (mul_le_mul_iff_left₀ hpos).mp hbound
    calc
      ‖x - y‖ ≤ (L * ‖T x - T y‖) / α := (le_div_iff₀ hα).mpr (by
        simpa only [mul_comm α] using hcancel)
      _ = (L / α) * ‖T x - T y‖ := by ring

/-- Local monotonicity and the operator bound make the discrete map injective. -/
theorem injOn_of_pairing_bound
    {U V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (A : U → V →L[ℝ] ℝ) (T : U → V) (L α : ℝ)
    (hL : 0 < L) (hα : 0 < α) (S : Submodule ℝ U)
    (hA : ∀ x y : U, ‖A x - A y‖ ≤ L * ‖x - y‖)
    (hmono : ∀ x ∈ S, ∀ y ∈ S,
      α * ‖x - y‖ ^ 2 ≤ (A x - A y) (T x - T y)) :
    Set.InjOn T S := by
  intro x hx y hy hxy
  have hbound := norm_sub_le_mul_norm_image_sub A T L α hL hα x y
    (hA x y) (hmono x hx y hy)
  rw [hxy, sub_self, norm_zero, mul_zero] at hbound
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _)))

/-- The assumed image containment and surjectivity give a bijective restriction. -/
theorem bijective_restrict_of_pairing_bound
    {U V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (A : U → V →L[ℝ] ℝ) (T : U → V) (L α : ℝ)
    (hL : 0 < L) (hα : 0 < α) (S : Submodule ℝ U) (W : Submodule ℝ V)
    (hA : ∀ x y : U, ‖A x - A y‖ ≤ L * ‖x - y‖)
    (hmono : ∀ x ∈ S, ∀ y ∈ S,
      α * ‖x - y‖ ^ 2 ≤ (A x - A y) (T x - T y))
    (hmaps : Set.MapsTo T S W) (honto : Set.SurjOn T S W) :
    Function.Bijective (hmaps.restrict T S W) := by
  exact Set.BijOn.bijective
    ⟨hmaps, injOn_of_pairing_bound A T L α hL hα S hA hmono, honto⟩

end Autoformalization.PetrovGalerkin
