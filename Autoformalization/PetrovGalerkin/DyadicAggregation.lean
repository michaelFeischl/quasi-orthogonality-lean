module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Log
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Conditional dyadic aggregation of consecutive pairs

The finite combinatorics underlying Section 1, Step 4 of `sources/main.tex`.
The interval energy is a parameter defined only on nonempty subintervals of
`{1,...,n}`. Its reduction, monotonicity and pair estimates are explicit inputs
of these intermediate implications; applications must establish all of them.
-/

public section

namespace Autoformalization.PetrovGalerkin

section IntervalEnergy

variable {n : ℕ} (E : ∀ a b : ℕ, 1 ≤ a → a < b → b ≤ n + 1 → ℝ)
  (q B : ℝ) (hq : 1 ≤ q) (hB : 0 ≤ B)
  (hE : ∀ a b ha hab hb, 0 ≤ E a b ha hab hb)
  (hmerge : ∀ a b c (ha : 1 ≤ a) (hab : a < b) (hbc : b < c) (hc : c ≤ n + 1),
    E a b ha hab (hbc.le.trans hc) + E b c (ha.trans hab.le) hbc hc ≤
      q * E a c ha (hab.trans hbc) hc)
  (d : ℕ → ℝ)
  (hpair : ∀ i (hi : 1 ≤ i) (hin : i + 2 ≤ n + 1),
    d i ≤ B * E i (i + 2) hi (Nat.lt_add_of_pos_right (Nat.zero_lt_succ 1)) hin)

include hq hB hE hmerge hpair

/-- Aggregate a nonempty collection of consecutive disjoint pairs in at most
`k` binary levels, including truncated collections of fewer than `2^k` pairs. -/
theorem dyadic_pair_sum_le (k a m : ℕ) (ha : 1 ≤ a) (hm : 0 < m)
    (hlen : m ≤ 2 ^ k) (hbound : a + 2 * m ≤ n + 1) :
    (∑ j ∈ Finset.range m, d (a + 2 * j)) ≤
      B * q ^ k * E a (a + 2 * m) ha
        (Nat.lt_add_of_pos_right (Nat.mul_pos (Nat.zero_lt_succ 1) hm)) hbound := by
  induction k generalizing a m with
  | zero =>
    have hmone : m = 1 := by simpa only [pow_zero] using (Nat.le_antisymm hlen hm)
    subst m
    simpa only [Finset.sum_range_one, mul_zero, add_zero, pow_zero, mul_one] using
      hpair a ha (by simpa only [mul_one] using hbound)
  | succ k ih =>
    by_cases hsmall : m ≤ 2 ^ k
    · calc
        _ ≤ B * q ^ k * E a (a + 2 * m) ha (by omega) hbound :=
          ih a m ha hm hsmall hbound
        _ ≤ B * q ^ (k + 1) * E a (a + 2 * m) ha (by omega) hbound := by
          apply mul_le_mul_of_nonneg_right _ (hE _ _ _ _ _)
          apply mul_le_mul_of_nonneg_left _ hB
          exact pow_le_pow_right₀ hq (Nat.le_succ k)
    · let p := 2 ^ k
      have hp : 0 < p := pow_pos (by decide) k
      have hpm : p < m := Nat.lt_of_not_ge hsmall
      have hr : 0 < m - p := Nat.sub_pos_of_lt hpm
      have hrem : m - p ≤ 2 ^ k := by
        rw [pow_succ] at hlen
        dsimp [p] at *
        omega
      have hab : a < a + 2 * p := by omega
      have hbc : a + 2 * p < a + 2 * m := by omega
      have hsplit : a + 2 * p + 2 * (m - p) = a + 2 * m := by omega
      have hfirst := ih a p ha hp (le_refl _) (by omega)
      have hlast := ih (a + 2 * p) (m - p) (by omega) hr hrem (by omega)
      have hsums : (∑ j ∈ Finset.range m, d (a + 2 * j)) =
          (∑ j ∈ Finset.range p, d (a + 2 * j)) +
          ∑ j ∈ Finset.range (m - p), d (a + 2 * p + 2 * j) := by
        conv_lhs => rw [← Nat.add_sub_of_le hpm.le]
        rw [Finset.sum_range_add]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        ring
      have hlast' : (∑ j ∈ Finset.range (m - p), d (a + 2 * p + 2 * j)) ≤
          B * q ^ k * E (a + 2 * p) (a + 2 * m) (by omega) hbc hbound := by
        simpa only [hsplit] using hlast
      calc
        _ = _ := hsums
        _ ≤ B * q ^ k * E a (a + 2 * p) ha hab (by omega) +
            B * q ^ k * E (a + 2 * p) (a + 2 * m) (by omega) hbc hbound :=
          add_le_add hfirst hlast'
        _ = B * q ^ k * (E a (a + 2 * p) ha hab (by omega) +
            E (a + 2 * p) (a + 2 * m) (by omega) hbc hbound) := by ring
        _ ≤ B * q ^ k * (q * E a (a + 2 * m) ha (by omega) hbound) :=
          mul_le_mul_of_nonneg_left (hmerge a (a + 2 * p) (a + 2 * m) ha hab hbc hbound)
            (mul_nonneg hB (pow_nonneg (le_trans (by norm_num) hq) k))
        _ = _ := by rw [pow_succ]; ring

end IntervalEnergy

/-- Split a finite consecutive sum into its two parity classes. -/
theorem sum_range_parity (d : ℕ → ℝ) (N a : ℕ) :
    (∑ i ∈ Finset.range N, d (a + i)) =
      (∑ j ∈ Finset.range ((N + 1) / 2), d (a + 2 * j)) +
      ∑ j ∈ Finset.range (N / 2), d (a + 1 + 2 * j) := by
  induction N using Nat.twoStepInduction generalizing a with
  | zero => simp only [Nat.zero_add, Nat.reduceDiv, Finset.sum_range_zero, add_zero]
  | one => simp only [Nat.reduceAdd, Nat.reduceDiv, Finset.sum_range_one,
      Finset.sum_range_zero, mul_zero, add_zero]
  | more N ih _ =>
    have hdiv : (N + 2) / 2 = N / 2 + 1 := by omega
    have hdiv' : (N + 2 + 1) / 2 = (N + 1) / 2 + 1 := by omega
    have hs : (∑ i ∈ Finset.range (N + 2), d (a + i)) =
        d a + d (a + 1) + ∑ i ∈ Finset.range N, d (a + 2 + i) := by
      rw [show N + 2 = 2 + N by omega, Finset.sum_range_add]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, add_zero, zero_add]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      omega
    rw [hs, ih (a + 2), hdiv, hdiv',
      Finset.sum_range_succ' (fun j => d (a + 2 * j)),
      Finset.sum_range_succ' (fun j => d (a + 1 + 2 * j))]
    simp only [mul_zero, add_zero]
    have h1 : (∑ j ∈ Finset.range ((N + 1) / 2), d (a + 2 * (j + 1))) =
        ∑ j ∈ Finset.range ((N + 1) / 2), d (a + 2 + 2 * j) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ring
    have h2 : (∑ j ∈ Finset.range (N / 2), d (a + 1 + 2 * (j + 1))) =
        ∑ j ∈ Finset.range (N / 2), d (a + 2 + 1 + 2 * j) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ring
    rw [h1, h2]
    ring

/-- The integer dyadic depth is bounded by the real-power growth factor. -/
theorem pow_nat_log_two_le_rpow (n : ℕ) (hn : 1 ≤ n) (q : ℝ) (hq : 1 ≤ q) :
    q ^ Nat.log 2 n ≤ (n : ℝ) ^ Real.logb 2 q := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hnat : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hreal : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by exact_mod_cast hnat
  have heq : ((2 : ℝ) ^ Nat.log 2 n) ^ Real.logb 2 q = q ^ Nat.log 2 n := by
    rw [← Real.rpow_natCast_mul (by norm_num), mul_comm (Nat.log 2 n : ℝ),
      Real.rpow_mul_natCast (by norm_num),
      Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hqpos]
  rw [← heq]
  exact Real.rpow_le_rpow (by positivity) hreal (Real.logb_nonneg (by norm_num) hq)

/-- Conditional aggregation for an energy on nonempty bounded intervals.
The two parity collections yield the constant `2`; all geometric inputs are
explicit obligations for the application. -/
theorem interval_energy_sum_le (n : ℕ) (hn : 1 ≤ n)
    (E : ∀ a b : ℕ, 1 ≤ a → a < b → b ≤ n + 1 → ℝ)
    (q B : ℝ) (hq : 1 ≤ q) (hB : 0 ≤ B)
    (hE : ∀ a b ha hab hb, 0 ≤ E a b ha hab hb)
    (hmerge : ∀ a b c (ha : 1 ≤ a) (hab : a < b) (hbc : b < c) (hc : c ≤ n + 1),
      E a b ha hab (hbc.le.trans hc) + E b c (ha.trans hab.le) hbc hc ≤
        q * E a c ha (hab.trans hbc) hc)
    (hmono : ∀ a b ha hab hb,
      E a b ha hab hb ≤ E 1 (n + 1) (le_refl _) (Nat.lt_succ_of_le hn) (le_refl _))
    (d : ℕ → ℝ)
    (hpair : ∀ i (hi : 1 ≤ i) (hin : i + 2 ≤ n + 1),
      d i ≤ B * E i (i + 2) hi (Nat.lt_add_of_pos_right (Nat.zero_lt_succ 1)) hin) :
    (∑ i ∈ Finset.Ico 1 n, d i) ≤
      (2 * B) * (n : ℝ) ^ Real.logb 2 q * E 1 (n + 1) (le_refl _) (Nat.lt_succ_of_le hn) (le_refl _) := by
  let k := Nat.log 2 n
  have hk : n < 2 ^ k * 2 := by
    simpa only [pow_succ] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq
  have hblock (a m : ℕ) (ha : 1 ≤ a) (hlen : m ≤ 2 ^ k)
      (hbound : a + 2 * m ≤ n + 1) :
      (∑ j ∈ Finset.range m, d (a + 2 * j)) ≤
        B * q ^ k * E 1 (n + 1) (le_refl _) (Nat.lt_succ_of_le hn) (le_refl _) := by
    by_cases hm : m = 0
    · subst m
      rw [Finset.sum_range_zero]
      exact mul_nonneg (mul_nonneg hB (pow_nonneg hq0 k)) (hE _ _ _ _ _)
    · calc
        _ ≤ B * q ^ k * E a (a + 2 * m) ha (by omega) hbound :=
          dyadic_pair_sum_le E q B hq hB hE hmerge d hpair k a m ha (by omega) hlen hbound
        _ ≤ _ := mul_le_mul_of_nonneg_left (hmono _ _ _ _ _)
          (mul_nonneg hB (pow_nonneg hq0 k))
  have hodd := hblock 1 (n / 2) (by omega) (by omega) (by omega)
  have heven := hblock 2 ((n - 1) / 2) (by omega) (by omega) (by omega)
  have hsplit : (∑ i ∈ Finset.Ico 1 n, d i) =
      (∑ j ∈ Finset.range (n / 2), d (1 + 2 * j)) +
      ∑ j ∈ Finset.range ((n - 1) / 2), d (2 + 2 * j) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have h := sum_range_parity d (n - 1) 1
    simpa only [Nat.sub_add_cancel hn, Nat.reduceAdd] using h
  calc
    _ = _ := hsplit
    _ ≤ B * q ^ k * E 1 (n + 1) (le_refl _) (Nat.lt_succ_of_le hn) (le_refl _) +
        B * q ^ k * E 1 (n + 1) (le_refl _) (Nat.lt_succ_of_le hn) (le_refl _) :=
      add_le_add hodd heven
    _ = (2 * B) * q ^ k * E 1 (n + 1) (le_refl _) (Nat.lt_succ_of_le hn) (le_refl _) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_nat_log_two_le_rpow n hn q hq) (by positivity))
      (hE _ _ _ _ _)

/-- Conditional finite-set form of the aggregation estimate. All energies are
restricted to nonempty subsets of the original index domain. -/
theorem finite_energy_sum_le (n : ℕ) (hn : 1 ≤ n)
    (E : ∀ I : Finset ℕ, I.Nonempty → I ⊆ Finset.Icc 1 n → ℝ)
    (q B : ℝ) (hq : 1 ≤ q) (hB : 0 ≤ B)
    (hE : ∀ I hI hIn, 0 ≤ E I hI hIn)
    (hmono : ∀ I J hI hJ hIn hJn, I ⊆ J → E I hI hIn ≤ E J hJ hJn)
    (hmerge : ∀ I J hI hJ hIn hJn,
      (∀ i ∈ I, ∀ j ∈ J, i < j) →
      E I hI hIn + E J hJ hJn ≤ q *
        E (I ∪ J) (hI.mono Finset.subset_union_left) (Finset.union_subset hIn hJn))
    (d : ℕ → ℝ)
    (hpair : ∀ i (hi : 1 ≤ i) (hin : i < n),
      d i ≤ B * E {i, i + 1} (Finset.insert_nonempty _ _) (by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        simp only [Finset.mem_Icc]
        omega)) :
    (∑ i ∈ Finset.Ico 1 n, d i) ≤
      (2 * B) * (n : ℝ) ^ Real.logb 2 q *
        E (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) (Finset.Subset.refl _) := by
  let EI : ∀ a b : ℕ, 1 ≤ a → a < b → b ≤ n + 1 → ℝ :=
    fun a b ha hab hb => E (Finset.Ico a b) (Finset.nonempty_Ico.mpr hab) (by
      intro i hi
      have hi' := Finset.mem_Ico.mp hi
      exact Finset.mem_Icc.mpr ⟨ha.trans hi'.1, by omega⟩)
  have hEI (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ n + 1) :
      0 ≤ EI a b ha hab hb := hE _ _ _
  have hEImerge (a b c : ℕ) (ha : 1 ≤ a) (hab : a < b) (hbc : b < c)
      (hc : c ≤ n + 1) :
      EI a b ha hab (hbc.le.trans hc) + EI b c (ha.trans hab.le) hbc hc ≤
        q * EI a c ha (hab.trans hbc) hc := by
    have h := hmerge (Finset.Ico a b) (Finset.Ico b c)
      (Finset.nonempty_Ico.mpr hab) (Finset.nonempty_Ico.mpr hbc)
      (by intro i hi; have := Finset.mem_Ico.mp hi; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      (by intro i hi; have := Finset.mem_Ico.mp hi; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      (by intro i hi j hj; exact (Finset.mem_Ico.mp hi).2.trans_le (Finset.mem_Ico.mp hj).1)
    simpa only [EI, Finset.Ico_union_Ico_eq_Ico hab.le hbc.le] using h
  have hEImono (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ n + 1) :
      EI a b ha hab hb ≤ EI 1 (n + 1) (by omega) (by omega) (le_refl _) := by
    apply hmono
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hEIpair (i : ℕ) (hi : 1 ≤ i) (hin : i + 2 ≤ n + 1) :
      d i ≤ B * EI i (i + 2) hi (by omega) hin := by
    have heq : ({i, i + 1} : Finset ℕ) = Finset.Ico i (i + 2) := by
      ext j
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Ico]
      omega
    have h := hpair i hi (by omega)
    simpa only [heq, EI] using h
  have h := interval_energy_sum_le n hn EI q B hq hB hEI hEImerge hEImono d hEIpair
  simpa only [EI, Finset.Ico_add_one_right_eq_Icc] using h

/-- The first and last windows cover all increments when their lengths overlap.
This is the literal coverage step behind the source's first WLOG reduction. -/
theorem sum_Ico_le_first_add_last (d : ℕ → ℝ) (n m : ℕ)
    (hd : ∀ i ∈ Finset.Ico 1 n, 0 ≤ d i) (hm : m ≤ n - 1)
    (hcover : n - 1 ≤ 2 * m) :
    (∑ i ∈ Finset.Ico 1 n, d i) ≤
      (∑ i ∈ Finset.Ico 1 (m + 1), d i) +
      ∑ i ∈ Finset.Ico (n - m) n, d i := by
  have hsub : Finset.Ico 1 n ⊆ Finset.Ico 1 (m + 1) ∪ Finset.Ico (n - m) n := by
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    simp only [Finset.mem_union, Finset.mem_Ico]
    omega
  have hreverse : Finset.Ico 1 (m + 1) ∪ Finset.Ico (n - m) n ⊆ Finset.Ico 1 n := by
    intro i hi
    simp only [Finset.mem_union, Finset.mem_Ico] at hi ⊢
    omega
  have heq := Finset.Subset.antisymm hsub hreverse
  calc
    _ = ∑ i ∈ Finset.Ico 1 (m + 1) ∪ Finset.Ico (n - m) n, d i := by rw [← heq]
    _ ≤ _ := by
      rw [← Finset.sum_union_inter]
      apply le_add_of_nonneg_right
      apply Finset.sum_nonneg
      intro i hi
      exact hd i (hreverse (Finset.mem_union_left _ (Finset.mem_inter.mp hi).1))

/-- The precise first/last power-of-two window inequality from Step 4.
The separate aggregation theorem also covers `n = 1`, where this logarithmic
window construction is unnecessary. -/
theorem half_sum_le_max_dyadic_windows (d : ℕ → ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hd : ∀ i ∈ Finset.Ico 1 n, 0 ≤ d i) :
    (∑ i ∈ Finset.Ico 1 n, d i) / 2 ≤
      max (∑ i ∈ Finset.Ico 1 (2 ^ Nat.log 2 (n - 1) + 1), d i)
        (∑ i ∈ Finset.Ico (n - 2 ^ Nat.log 2 (n - 1)) n, d i) := by
  have hm : 2 ^ Nat.log 2 (n - 1) ≤ n - 1 :=
    Nat.pow_log_le_self 2 (by omega)
  have hcover : n - 1 ≤ 2 * 2 ^ Nat.log 2 (n - 1) := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n - 1)
    rw [pow_succ] at h
    omega
  have hsum := sum_Ico_le_first_add_last d n (2 ^ Nat.log 2 (n - 1)) hd hm hcover
  have hleft := le_max_left
    (∑ i ∈ Finset.Ico 1 (2 ^ Nat.log 2 (n - 1) + 1), d i)
    (∑ i ∈ Finset.Ico (n - 2 ^ Nat.log 2 (n - 1)) n, d i)
  have hright := le_max_right
    (∑ i ∈ Finset.Ico 1 (2 ^ Nat.log 2 (n - 1) + 1), d i)
    (∑ i ∈ Finset.Ico (n - 2 ^ Nat.log 2 (n - 1)) n, d i)
  linarith only [hsum, hleft, hright]

end Autoformalization.PetrovGalerkin
