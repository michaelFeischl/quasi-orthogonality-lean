module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Autoformalization.PetrovGalerkin.InverseEstimate
import Autoformalization.PetrovGalerkin.HilbertSurjectivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Discrete Petrov–Galerkin well-posedness

This provider proves the exact approved proposition from `sources/main.tex`,
lines 50–130. The discrete inverse is local to the proof. Restriction to the
test space and the Riesz isometry transport the equation to a Lipschitz,
strongly monotone Hilbert-space map.
-/

public section
universe u v
namespace Autoformalization.PetrovGalerkin.Provider

theorem exists_unique_discrete_solution :
    ∀
    (U : Type u) (V : Type v)
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (L M α : ℝ) (hL : 0 < L) (hM : 0 < M) (hα : 0 < α)
    (A : U → (V →L[ℝ] ℝ)) (T : U → V)
    (Uj : ℕ → Submodule ℝ U) (Vj : ℕ → Submodule ℝ V)
    (hUfin : ∀ j, FiniteDimensional ℝ (Uj j))
    (hVfin : ∀ j, FiniteDimensional ℝ (Vj j))
    (hUnested : ∀ j, Uj j ≤ Uj (j + 1))
    (hVnested : ∀ j, Vj j ≤ Vj (j + 1))
    (hA : ∀ x y : U, ‖A x - A y‖ ≤ L * ‖x - y‖)
    (hTsurj : Function.Surjective T)
    (hTmaps : ∀ j, Set.MapsTo T (Uj j) (Vj j))
    (hTonto : ∀ j, Set.SurjOn T (Uj j) (Vj j))
    (hTbound : ∀ j, ∀ x ∈ Uj j, ∀ y ∈ Uj j,
      ‖T x - T y‖ ≤ M * ‖x - y‖)
    (hmono : ∀ j, ∀ x ∈ Uj j, ∀ y ∈ Uj j,
      α * ‖x - y‖ ^ 2 ≤ (A x - A y) (T x - T y)),
    ∀ (f : V →L[ℝ] ℝ) (j : ℕ),
      ∃! w : Uj j, ∀ z : Vj j, A (w : U) (z : V) = f (z : V) :=
by
  intro U V _ _ _ _ _ _ L M α hL hM hα A T Uj Vj hUfin hVfin
    hUnested hVnested hA hTsurj hTmaps hTonto hTbound hmono f j
  classical
  let : FiniteDimensional ℝ (Vj j) := hVfin j
  let e : Uj j ≃ Vj j := Equiv.ofBijective ((hTmaps j).restrict T (Uj j) (Vj j))
    (bijective_restrict_of_pairing_bound A T L α hL hα (Uj j) (Vj j)
      hA (hmono j) (hTmaps j) (hTonto j))
  have he (z : Vj j) : T (e.symm z : U) = (z : V) :=
    congrArg Subtype.val (e.apply_symm_apply z)
  have hinv (z w : Vj j) :
      ‖(e.symm z : U) - (e.symm w : U)‖ ≤ (L / α) * ‖z - w‖ := by
    have h := norm_sub_le_mul_norm_image_sub A T L α hL hα
      (e.symm z) (e.symm w) (hA _ _)
      (hmono j _ (e.symm z).property _ (e.symm w).property)
    simpa only [he, ← Submodule.coe_sub, Submodule.norm_coe] using h
  let B : Vj j → (Vj j →L[ℝ] ℝ) := fun z =>
    (A (e.symm z : U)).comp (Vj j).subtypeL
  let R := InnerProductSpace.toDual ℝ (Vj j)
  let F : Vj j → Vj j := fun z => R.symm (B z)
  have hrestrict (z w : Vj j) : ‖B z - B w‖ ≤ ‖A (e.symm z : U) - A (e.symm w : U)‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact (A (e.symm z : U) - A (e.symm w : U)).le_opNorm (x : V)
  have hLip (z w : Vj j) : ‖F z - F w‖ ≤ (L ^ 2 / α) * ‖z - w‖ := by
    change ‖R.symm (B z) - R.symm (B w)‖ ≤ _
    rw [← map_sub, R.symm.norm_map]
    calc
      ‖B z - B w‖ ≤ ‖A (e.symm z : U) - A (e.symm w : U)‖ := hrestrict z w
      _ ≤ L * ‖(e.symm z : U) - (e.symm w : U)‖ := hA _ _
      _ ≤ L * ((L / α) * ‖z - w‖) := mul_le_mul_of_nonneg_left (hinv z w) hL.le
      _ = (L ^ 2 / α) * ‖z - w‖ := by ring
  have hMono (z w : Vj j) :
      (α / M ^ 2) * ‖z - w‖ ^ 2 ≤ inner ℝ (F z - F w) (z - w) := by
    have hb : ‖z - w‖ ≤ M * ‖(e.symm z : U) - (e.symm w : U)‖ := by
      have h := hTbound j _ (e.symm z).property _ (e.symm w).property
      simpa only [he, ← Submodule.coe_sub, Submodule.norm_coe] using h
    have hbsq : ‖z - w‖ ^ 2 ≤ M ^ 2 * ‖(e.symm z : U) - (e.symm w : U)‖ ^ 2 := by
      nlinarith only [hb, norm_nonneg (z - w),
        mul_nonneg hM.le (norm_nonneg ((e.symm z : U) - (e.symm w : U)))]
    have hs : (α / M ^ 2) * ‖z - w‖ ^ 2 ≤
        α * ‖(e.symm z : U) - (e.symm w : U)‖ ^ 2 := by
      calc
        (α / M ^ 2) * ‖z - w‖ ^ 2 = α * (‖z - w‖ ^ 2 / M ^ 2) := by ring
        _ ≤ α * ‖(e.symm z : U) - (e.symm w : U)‖ ^ 2 :=
          mul_le_mul_of_nonneg_left
            ((div_le_iff₀ (sq_pos_of_pos hM)).mpr (by
              simpa only [mul_comm (M ^ 2)] using hbsq)) hα.le
    have hm := hmono j _ (e.symm z).property _ (e.symm w).property
    have hi : inner ℝ (F z - F w) (z - w) =
        (A (e.symm z : U) - A (e.symm w : U)) (T (e.symm z : U) - T (e.symm w : U)) := by
      change inner ℝ (R.symm (B z) - R.symm (B w)) (z - w) = _
      rw [← map_sub, InnerProductSpace.toDual_symm_apply, he, he]
      rfl
    rw [hi]
    exact hs.trans hm
  obtain ⟨z, hz, huniq⟩ := existsUnique_preimage_of_lipschitz_stronglyMonotone F
    (div_pos (sq_pos_of_pos hL) hα) (div_pos hα (sq_pos_of_pos hM))
    hLip hMono (R.symm (f.comp (Vj j).subtypeL))
  have heq (w : Uj j) : F (e w) = R.symm (f.comp (Vj j).subtypeL) ↔
      ∀ x : Vj j, A (w : U) (x : V) = f (x : V) := by
    change R.symm (B (e w)) = R.symm (f.comp (Vj j).subtypeL) ↔ _
    rw [R.symm.injective.eq_iff]
    constructor
    · intro h x
      have hx := congrArg (fun g : Vj j →L[ℝ] ℝ => g x) h
      simpa only [B, e.symm_apply_apply, ContinuousLinearMap.comp_apply,
        Submodule.subtypeL_apply] using hx
    · intro h
      ext x
      simpa only [B, e.symm_apply_apply, ContinuousLinearMap.comp_apply,
        Submodule.subtypeL_apply] using h x
  refine ⟨e.symm z, (heq _).mp ?_, ?_⟩
  · simpa only [e.apply_symm_apply] using hz
  · intro w hw
    apply e.injective
    rw [e.apply_symm_apply]
    exact huniq (e w) ((heq w).mpr hw)

end Autoformalization.PetrovGalerkin.Provider
