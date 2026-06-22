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

omit [Fintype ι] in
/-- The `index n`-image of a bounded set is finite: only finitely many cells of the `n⁻¹ℤ^ι`
grid meet a bounded set. -/
theorem setFinite_index_image_of_isBounded [Finite ι] (n : ℕ) {T : Set (ι → ℝ)}
    (hbdd : Bornology.IsBounded T) : (index n '' T).Finite := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
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

private lemma ceil_natCast_mul_le_ceil_natCast_mul_add (n : ℕ) {a b r : ℝ} (h : a ≤ b + r) :
    (⌈(n : ℝ) * a⌉ : ℤ) ≤ ⌈(n : ℝ) * b⌉ + ⌈(n : ℝ) * r⌉ :=
  calc (⌈(n : ℝ) * a⌉ : ℤ)
      ≤ ⌈(n : ℝ) * b + (n : ℝ) * r⌉ :=
        Int.ceil_le_ceil (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    _ ≤ ⌈(n : ℝ) * b⌉ + ⌈(n : ℝ) * r⌉ := Int.ceil_add_le _ _

/-- **Bounded-diameter cell incidence.** A set `T ⊆ ι → ℝ` of diameter `≤ r` meets at most
`(2⌈n·r⌉₊ + 1)ᵈ` cells of the `n⁻¹ℤ^ι` grid, i.e. its `index n`-image has at most that many
points. (Here `ι → ℝ` carries the sup metric, so a cube of side `1/n` has diameter `1/n`.) -/
theorem ncard_index_image_le_of_diam_le (n : ℕ) [NeZero n] {T : Set (ι → ℝ)} {r : ℝ}
    (hr : 0 ≤ r) (hdiam : Metric.diam T ≤ r) (hbdd : Bornology.IsBounded T) :
    (index n '' T).ncard ≤ (2 * ⌈(n : ℝ) * r⌉₊ + 1) ^ Fintype.card ι := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  set K : ℕ := ⌈(n : ℝ) * r⌉₊ with hK
  set c : ι → ℤ := index n x₀ with hc
  set F : Finset (ι → ℤ) := Fintype.piFinset fun i ↦ Finset.Icc (c i - K) (c i + K) with hF
  have hsub : index n '' T ⊆ ↑F := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [hF, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have hdx : |x i - x₀ i| ≤ r := by
      have h1 : dist (x i) (x₀ i) ≤ dist x x₀ := dist_le_pi_dist x x₀ i
      rw [Real.dist_eq] at h1
      exact h1.trans ((Metric.dist_le_diam_of_mem hbdd hx hx₀).trans hdiam)
    rcases abs_le.mp hdx with ⟨hlo, hhi⟩
    have hKeq : (K : ℤ) = ⌈(n : ℝ) * r⌉ := hK ▸ Int.natCast_ceil_eq_ceil (by positivity)
    have hub :=
      ceil_natCast_mul_le_ceil_natCast_mul_add n (a := x i) (b := x₀ i) (r := r) (by linarith)
    have hlb :=
      ceil_natCast_mul_le_ceil_natCast_mul_add n (a := x₀ i) (b := x i) (r := r) (by linarith)
    simp only [index_apply, hc]
    constructor <;> lia
  refine (Set.ncard_le_ncard hsub F.finite_toSet).trans ?_
  rw [Set.ncard_coe_finset, hF, Fintype.card_piFinset]
  have hcard : ∀ i, (Finset.Icc (c i - K) (c i + K)).card = 2 * K + 1 := by
    intro i
    rw [Int.card_Icc]
    lia
  rw [Finset.prod_congr rfl fun i _ ↦ hcard i, Finset.prod_const, Finset.card_univ]

end Sublemmas

end

end Chebotarev
