/-
Copyright (c) 2026. All rights reserved.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Surjectivity of Lipschitz strongly monotone Hilbert maps

A contraction argument proves surjectivity, including the zero space
and the zero contraction factor.
-/

public section

open scoped NNReal

namespace Autoformalization.PetrovGalerkin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A globally Lipschitz, strongly monotone self-map of a complete real Hilbert
space has a unique preimage of every point. -/
theorem existsUnique_preimage_of_lipschitz_stronglyMonotone [CompleteSpace H]
    (F : H → H) {Λ β : ℝ} (hΛ : 0 < Λ) (hβ : 0 < β)
    (hLip : ∀ x y, ‖F x - F y‖ ≤ Λ * ‖x - y‖)
    (hMono : ∀ x y, β * ‖x - y‖ ^ 2 ≤ inner ℝ (F x - F y) (x - y))
    (g : H) : ∃! x, F x = g := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · exact ⟨0, Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
  have hβΛ : β ≤ Λ := by
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    have hn : 0 < ‖x - 0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
    have hh := (hMono x 0).trans (real_inner_le_norm (F x - F 0) (x - 0))
    have hl := mul_le_mul_of_nonneg_right (hLip x 0) (norm_nonneg (x - 0))
    have hp : β * ‖x - 0‖ ^ 2 ≤ Λ * ‖x - 0‖ ^ 2 := by
      nlinarith only [hh, hl]
    exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hn)).mp hp
  have hΛsq : 0 < Λ ^ 2 := sq_pos_of_pos hΛ
  have hβsq : 0 < β ^ 2 := sq_pos_of_pos hβ
  have hratio : 0 < β ^ 2 / Λ ^ 2 := div_pos hβsq hΛsq
  have hrad : 0 ≤ 1 - β ^ 2 / Λ ^ 2 := by
    have hsq : β ^ 2 ≤ Λ ^ 2 := by nlinarith only [hβΛ, hβ, hΛ]
    exact sub_nonneg.mpr ((div_le_one hΛsq).mpr hsq)
  let t : ℝ := β / Λ ^ 2
  have ht : 0 < t := div_pos hβ hΛsq
  have hcoef : 1 - 2 * t * β + t ^ 2 * Λ ^ 2 = 1 - β ^ 2 / Λ ^ 2 := by
    dsimp [t]
    field_simp
    ring
  let q : ℝ≥0 := ⟨Real.sqrt (1 - β ^ 2 / Λ ^ 2), Real.sqrt_nonneg _⟩
  have hq : q < 1 := by
    change Real.sqrt (1 - β ^ 2 / Λ ^ 2) < 1
    exact (Real.sqrt_lt hrad (by norm_num)).mpr (by linarith only [hratio])
  have hqsq : (q : ℝ) ^ 2 = 1 - β ^ 2 / Λ ^ 2 := Real.sq_sqrt hrad
  let C : H → H := fun x => x - t • (F x - g)
  have hC : ContractingWith q C := by
    refine ⟨hq, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    have hdiff : C x - C y = (x - y) - t • (F x - F y) := by
      dsimp [C]
      rw [← sub_sub_sub_comm, ← smul_sub]
      congr 2
      abel
    have hexpand : ‖C x - C y‖ ^ 2 = ‖x - y‖ ^ 2 -
        2 * t * inner ℝ (F x - F y) (x - y) + t ^ 2 * ‖F x - F y‖ ^ 2 := by
      rw [hdiff, norm_sub_sq_real, real_inner_smul_right, real_inner_comm,
        norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      ring
    have hLipSq : ‖F x - F y‖ ^ 2 ≤ Λ ^ 2 * ‖x - y‖ ^ 2 := by
      have hh := hLip x y
      have hnn := norm_nonneg (F x - F y)
      have hr : 0 ≤ Λ * ‖x - y‖ := mul_nonneg hΛ.le (norm_nonneg _)
      nlinarith only [hh, hnn, hr]
    have hm := mul_le_mul_of_nonneg_left (hMono x y) (show 0 ≤ 2 * t by positivity)
    have hl := mul_le_mul_of_nonneg_left hLipSq (sq_nonneg t)
    have hbound : ‖C x - C y‖ ^ 2 ≤ (1 - β ^ 2 / Λ ^ 2) * ‖x - y‖ ^ 2 := by
      calc
        ‖C x - C y‖ ^ 2 ≤
            (1 - 2 * t * β + t ^ 2 * Λ ^ 2) * ‖x - y‖ ^ 2 := by
          nlinarith only [hexpand, hm, hl]
        _ = _ := by rw [hcoef]
    have hrnonneg : 0 ≤ (q : ℝ) * ‖x - y‖ := mul_nonneg q.coe_nonneg (norm_nonneg _)
    have hrSq : ((q : ℝ) * ‖x - y‖) ^ 2 =
        (1 - β ^ 2 / Λ ^ 2) * ‖x - y‖ ^ 2 := by rw [mul_pow, hqsq]
    nlinarith only [hbound, hrSq, hrnonneg, norm_nonneg (C x - C y)]
  have hfix (x : H) : Function.IsFixedPt C x ↔ F x = g := by
    change x - t • (F x - g) = x ↔ F x = g
    rw [sub_eq_self, smul_eq_zero]
    simp only [ne_of_gt ht, false_or, sub_eq_zero]
  refine ⟨hC.fixedPoint C, (hfix _).mp hC.fixedPoint_isFixedPt, ?_⟩
  intro y hy
  exact hC.fixedPoint_unique ((hfix y).mpr hy)

end Autoformalization.PetrovGalerkin
