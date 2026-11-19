/-
Copyright (c) 2026.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Ring

/-!
# Cea comparisons for nested Petrov–Galerkin solutions

The two comparisons and their combination are the estimates in
`sources/main.tex`, lines 144–155. The hypotheses use the source's local
quantitative assumptions. No linearity or zero preservation of `T` is required.
-/

public section

namespace Autoformalization.PetrovGalerkin

private theorem norm_le_of_sq_le_mul {a b C α : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C) (hα : 0 < α)
    (h : α * a ^ 2 ≤ (C * b) * a) : a ≤ (C / α) * b := by
  rcases eq_or_lt_of_le ha with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg (div_nonneg hC hα.le) hb
  · rw [pow_two, ← mul_assoc] at h
    have hcancel : α * a ≤ C * b := (mul_le_mul_iff_left₀ hpos).mp h
    calc
      a ≤ (C * b) / α := (le_div_iff₀ hα).mpr (by
        simpa only [mul_comm α] using hcancel)
      _ = (C / α) * b := by ring

section Galerkin

variable {U V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (A : U → V →L[ℝ] ℝ) (Vj : ℕ → Submodule ℝ V)
  (hV : Monotone Vj) (f : V →L[ℝ] ℝ) (u : ℕ → U)
  (hgal : ∀ j, ∀ z ∈ Vj j, A (u j) z = f z)

include hV hgal

/-- Differences of Galerkin functionals annihilate every earlier test space. -/
theorem galerkin_sub_apply_eq_zero {i j : ℕ} (hij : i ≤ j)
    {z : V} (hz : z ∈ Vj i) : (A (u j) - A (u i)) z = 0 := by
  rw [sub_apply, hgal j z (hV hij hz), hgal i z hz, sub_self]

end Galerkin

section Comparisons

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
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

/-- The first Cea comparison: changing the earlier endpoint within a nested interval. -/
theorem norm_sub_le_cea_mul_norm_sub_left {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    ‖u k - u j‖ ≤ (L * M / α) * ‖u k - u i‖ := by
  have hjmem : u j ∈ Uj k := hU hjk (hu j)
  have himem : u i ∈ Uj k := hU (hij.trans hjk) (hu i)
  have hzj := galerkin_sub_apply_eq_zero A Vj hV f u hgal hjk (hmaps j (hu j))
  have hzi := galerkin_sub_apply_eq_zero A Vj hV f u hgal hjk
    (hV hij (hmaps i (hu i)))
  have hpair : (A (u k) - A (u j)) (T (u k) - T (u j)) =
      (A (u k) - A (u j)) (T (u k) - T (u i)) := by
    rw [map_sub, map_sub, hzj, hzi]
  have hbound : α * ‖u k - u j‖ ^ 2 ≤
      ((L * M) * ‖u k - u i‖) * ‖u k - u j‖ := calc
    α * ‖u k - u j‖ ^ 2 ≤ (A (u k) - A (u j)) (T (u k) - T (u j)) :=
      hmono k (u k) (hu k) (u j) hjmem
    _ = (A (u k) - A (u j)) (T (u k) - T (u i)) := hpair
    _ ≤ ‖A (u k) - A (u j)‖ * ‖T (u k) - T (u i)‖ :=
      (le_abs_self _).trans ((A (u k) - A (u j)).le_opNorm _)
    _ ≤ (L * ‖u k - u j‖) * (M * ‖u k - u i‖) :=
      mul_le_mul (hA (u k) (u j)) (hT k (u k) (hu k) (u i) himem)
        (norm_nonneg _) (mul_nonneg hL.le (norm_nonneg _))
    _ = ((L * M) * ‖u k - u i‖) * ‖u k - u j‖ := by ring
  exact norm_le_of_sq_le_mul (norm_nonneg _) (norm_nonneg _)
    (mul_nonneg hL.le hM.le) hα hbound

/-- The second Cea comparison: extending the later endpoint of a nested interval. -/
theorem norm_sub_le_cea_mul_norm_sub_right {i k l : ℕ} (hik : i ≤ k) (hkl : k ≤ l) :
    ‖u k - u i‖ ≤ (L * M / α) * ‖u l - u i‖ := by
  have himem : u i ∈ Uj k := hU hik (hu i)
  have hz : T (u k) - T (u i) ∈ Vj k :=
    (Vj k).sub_mem (hmaps k (hu k)) (hV hik (hmaps i (hu i)))
  have heq : A (u k) (T (u k) - T (u i)) = A (u l) (T (u k) - T (u i)) :=
    (hgal k _ hz).trans (hgal l _ (hV hkl hz)).symm
  have hpair : (A (u k) - A (u i)) (T (u k) - T (u i)) =
      (A (u l) - A (u i)) (T (u k) - T (u i)) := by
    rw [sub_apply, sub_apply, heq]
  have hbound : α * ‖u k - u i‖ ^ 2 ≤
      ((L * M) * ‖u l - u i‖) * ‖u k - u i‖ := calc
    α * ‖u k - u i‖ ^ 2 ≤ (A (u k) - A (u i)) (T (u k) - T (u i)) :=
      hmono k (u k) (hu k) (u i) himem
    _ = (A (u l) - A (u i)) (T (u k) - T (u i)) := hpair
    _ ≤ ‖A (u l) - A (u i)‖ * ‖T (u k) - T (u i)‖ :=
      (le_abs_self _).trans ((A (u l) - A (u i)).le_opNorm _)
    _ ≤ (L * ‖u l - u i‖) * (M * ‖u k - u i‖) :=
      mul_le_mul (hA (u l) (u i)) (hT k (u k) (hu k) (u i) himem)
        (norm_nonneg _) (mul_nonneg hL.le (norm_nonneg _))
    _ = ((L * M) * ‖u l - u i‖) * ‖u k - u i‖ := by ring
  exact norm_le_of_sq_le_mul (norm_nonneg _) (norm_nonneg _)
    (mul_nonneg hL.le hM.le) hα hbound

/-- The combined Cea estimate for four ordered indices. -/
theorem norm_sub_le_cea_sq_mul_norm_sub {i j k l : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    ‖u k - u j‖ ≤ (L * M / α) ^ 2 * ‖u l - u i‖ := by
  have hfirst := norm_sub_le_cea_mul_norm_sub_left A T Uj Vj L M α hL hM hα
    hU hV hA hmaps hT hmono f u hu hgal hij hjk
  have hsecond := norm_sub_le_cea_mul_norm_sub_right A T Uj Vj L M α hL hM hα
    hU hV hA hmaps hT hmono f u hu hgal (hij.trans hjk) hkl
  calc
    ‖u k - u j‖ ≤ (L * M / α) * ‖u k - u i‖ := hfirst
    _ ≤ (L * M / α) * ((L * M / α) * ‖u l - u i‖) :=
      mul_le_mul_of_nonneg_left hsecond (div_nonneg (mul_nonneg hL.le hM.le) hα.le)
    _ = (L * M / α) ^ 2 * ‖u l - u i‖ := by ring

end Comparisons

end Autoformalization.PetrovGalerkin
