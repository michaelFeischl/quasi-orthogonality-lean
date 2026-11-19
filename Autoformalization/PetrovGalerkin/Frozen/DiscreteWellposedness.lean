-- FROZEN_ANCHOR_PREFIX_BEGIN
module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Order.Interval.Finset.Nat

import Autoformalization.PetrovGalerkin.Providers.DiscreteWellposedness

public section
universe u v
namespace Autoformalization.PetrovGalerkin

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
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact Autoformalization.PetrovGalerkin.Provider.exists_unique_discrete_solution
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end Autoformalization.PetrovGalerkin
-- FROZEN_ANCHOR_SUFFIX_END
