module

public import Mathlib.Analysis.BoxIntegral.UnitPartition
public import Mathlib.Data.Pi.Interval
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Index-image counting bounds for the scaled integer lattice

Counting bounds for the image `index n '' T ⊆ ι → ℤ` of a set under the unit-partition `index`
map. Finiteness for bounded `T` (`setFinite_index_image_of_isBounded`), a diameter bound
(`ncard_index_image_le_of_diam_le`), and the resulting `O(nᵈ⁻¹)` boundary-cell bounds for a single
Lipschitz chart (`ncard_index_image_chart_le`) and for a Lipschitz-covered frontier
(`ncard_index_image_frontier_le`). These are the boundary-cell inputs to the effective
lattice-point count in `LatticePointCount.lean`.

## References

* Serge Lang, *Algebraic Number Theory*, 2nd ed., GTM 110, Springer 1994, Ch. VI §3 (p. 129).
* S. Gun, O. Ramaré, J. Sivaraman, *Counting ideals in ray classes*, J. Number Theory 243 (2023)
  §3.3, after K. Debaene.
-/

open Submodule Pointwise MeasureTheory Set BoxIntegral BoxIntegral.unitPartition

open scoped NNReal

namespace Chebotarev

@[expose] public section

section Sublemmas

variable {ι : Type*} [Fintype ι]

private lemma ceil_natCast_mul_le_ceil_natCast_mul_add (n : ℕ) {a b r : ℝ} (h : a ≤ b + r) :
    (⌈(n : ℝ) * a⌉ : ℤ) ≤ ⌈(n : ℝ) * b⌉ + ⌈(n : ℝ) * r⌉ :=
  calc (⌈(n : ℝ) * a⌉ : ℤ)
      ≤ ⌈(n : ℝ) * b + (n : ℝ) * r⌉ :=
        Int.ceil_le_ceil (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    _ ≤ ⌈(n : ℝ) * b⌉ + ⌈(n : ℝ) * r⌉ := Int.ceil_add_le _ _

private lemma abs_sub_le_one_div_of_ceil_natCast_mul_eq {n : ℕ} (hn : 0 < (n : ℝ)) {a b : ℝ}
    (h : ⌈(n : ℝ) * a⌉ = ⌈(n : ℝ) * b⌉) : |a - b| ≤ 1 / n := by
  have hr : (⌈(n : ℝ) * a⌉ : ℝ) = ⌈(n : ℝ) * b⌉ := by exact_mod_cast h
  rw [show a - b = ((n : ℝ) * a - (n : ℝ) * b) / n by field_simp, abs_div, abs_of_pos hn,
    div_le_div_iff_of_pos_right hn, abs_le]
  constructor <;>
    nlinarith [Int.le_ceil ((n : ℝ) * a), Int.le_ceil ((n : ℝ) * b),
      Int.ceil_lt_add_one ((n : ℝ) * a), Int.ceil_lt_add_one ((n : ℝ) * b), hr]

-- The `Fintype ι` instance is needed for the `sup`-metric on `ι → ℝ`, so the
-- `unusedFintypeInType` linter (which only inspects the conclusion) is a false positive here.
set_option linter.unusedFintypeInType false in
/-- The `index n`-image of a bounded set is finite: only finitely many cells of the `n⁻¹ℤ^ι`
grid meet a bounded set. -/
theorem setFinite_index_image_of_isBounded (n : ℕ) {T : Set (ι → ℝ)}
    (hbdd : Bornology.IsBounded T) : (index n '' T).Finite := by
  classical
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall (0 : ι → ℝ)
  set F : Finset (ι → ℤ) :=
    Fintype.piFinset fun _ : ι ↦ Finset.Icc (⌈-((n : ℝ) * R)⌉ - 1) (⌈(n : ℝ) * R⌉ - 1) with hF
  refine Set.Finite.subset (Finset.finite_toSet F) ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [hF, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc, index_apply]
  intro i
  have hxi : |x i| ≤ R := by
    have hd : dist (x i) ((0 : ι → ℝ) i) ≤ dist x 0 := dist_le_pi_dist x 0 i
    rw [Real.dist_eq, Pi.zero_apply, sub_zero] at hd
    exact hd.trans (by simpa [Real.dist_eq] using hR hx)
  rcases abs_le.mp hxi with ⟨hlo, hhi⟩
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact ⟨sub_le_sub_right (Int.ceil_le_ceil (by nlinarith)) 1,
    sub_le_sub_right (Int.ceil_le_ceil (by nlinarith)) 1⟩

end Sublemmas

end

end Chebotarev
