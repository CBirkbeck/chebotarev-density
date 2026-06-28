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

private lemma abs_sub_le_one_div_of_ceil_natCast_mul_eq {n : ℕ} (hn : 0 < n) {a b : ℝ}
    (h : ⌈(n : ℝ) * a⌉ = ⌈(n : ℝ) * b⌉) : |a - b| ≤ 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : (⌈(n : ℝ) * a⌉ : ℝ) = ⌈(n : ℝ) * b⌉ := by exact_mod_cast h
  rw [show a - b = ((n : ℝ) * a - (n : ℝ) * b) / n by field_simp, abs_div, abs_of_pos hn',
    div_le_div_iff_of_pos_right hn', abs_le]
  constructor <;>
    nlinarith [Int.le_ceil ((n : ℝ) * a), Int.le_ceil ((n : ℝ) * b),
      Int.ceil_lt_add_one ((n : ℝ) * a), Int.ceil_lt_add_one ((n : ℝ) * b), hr]

/-- A fibre of the grid-quantization map `y ↦ (⌈n · yₖ⌉)ₖ` has diameter `≤ 1/n`: two points
landing in the same cell agree to within `1/n` in each coordinate (sup metric). -/
private lemma diam_Icc_inter_ceil_preimage_le {κ : Type*} [Fintype κ] {n : ℕ} (hn : 0 < n)
    (v : κ → ℤ) :
    Metric.diam (Set.Icc 0 1 ∩ (fun (y : κ → ℝ) k ↦ ⌈(n : ℝ) * y k⌉) ⁻¹' {v}) ≤ 1 / n := by
  refine Metric.diam_le_of_forall_dist_le (by positivity) fun y hy y' hy' ↦ ?_
  rw [dist_pi_le_iff (by positivity)]
  intro k
  have hce : ⌈(n : ℝ) * y k⌉ = ⌈(n : ℝ) * y' k⌉ :=
    (congrFun hy.2 k).trans (congrFun hy'.2 k).symm
  rw [Real.dist_eq]
  exact abs_sub_le_one_div_of_ceil_natCast_mul_eq hn hce

/-- The `index n`-image of a Lipschitz image of a set of diameter `≤ 1/n` meets at most
`(2⌈M⌉₊ + 1)ᵈ` cells: the image has diameter `≤ M/n`, so this is `ncard_index_image_le_of_diam_le`
with `r = M·(1/n)`. -/
private lemma ncard_index_image_le_of_diam_le_lipschitz {κ : Type*} [Fintype κ] {M : ℝ≥0}
    {n : ℕ} [NeZero n] {φ : (κ → ℝ) → (ι → ℝ)} (hφ : LipschitzWith M φ) {S : Set (κ → ℝ)}
    (hbdd : Bornology.IsBounded S) (hdiam : Metric.diam S ≤ 1 / n) :
    (index n '' (φ '' S)).ncard ≤ (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hdimg : Metric.diam (φ '' S) ≤ (M : ℝ) * (1 / n) :=
    (hφ.diam_image_le S hbdd).trans (mul_le_mul_of_nonneg_left hdiam (by positivity))
  refine (ncard_index_image_le_of_diam_le n (by positivity) hdimg
    (hφ.isBounded_image hbdd)).trans ?_
  rw [show (n : ℝ) * ((M : ℝ) * (1 / n)) = (M : ℝ) by field_simp]

/-- **Single-chart cell count.** For one `M`-Lipschitz map `φ : (Fin (d-1) → ℝ) → (ι → ℝ)`,
the number of grid cells of the `n⁻¹ℤ^ι` grid meeting the image `φ '' [0,1]ᵈ⁻¹` is at most
`(2⌈M⌉₊ + 1)ᵈ · (n+1)ᵈ⁻¹ = O(nᵈ⁻¹)`. -/
theorem ncard_index_image_chart_le {M : ℝ≥0} {φ : (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)}
    (hφ : LipschitzWith M φ) {n : ℕ} (hn : 1 ≤ n) :
    (index n '' (φ '' Set.Icc 0 1)).ncard
      ≤ (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * (n + 1) ^ (Fintype.card ι - 1) := by
  classical
  have hne : NeZero n := ⟨Nat.one_le_iff_ne_zero.mp hn⟩
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hne.out
  set q : (Fin (Fintype.card ι - 1) → ℝ) → (Fin (Fintype.card ι - 1) → ℤ) :=
    fun y k ↦ ⌈(n : ℝ) * y k⌉ with hq
  set T : Finset (Fin (Fintype.card ι - 1) → ℤ) :=
    Finset.Icc (0 : Fin (Fintype.card ι - 1) → ℤ) (fun _ ↦ (n : ℤ)) with hT
  have hdiam : ∀ v : Fin (Fintype.card ι - 1) → ℤ,
      Metric.diam (Set.Icc 0 1 ∩ q ⁻¹' {v}) ≤ 1 / n :=
    fun v ↦ by rw [hq]; exact diam_Icc_inter_ceil_preimage_le hn v
  have hcover : index n '' (φ '' Set.Icc 0 1) ⊆
      ⋃ v ∈ T, index n '' (φ '' (Set.Icc 0 1 ∩ q ⁻¹' {v})) := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hyT : q y ∈ T := by
      rw [hT, Finset.mem_Icc]
      refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
      · simp only [hq, Pi.zero_apply]
        rw [Int.le_ceil_iff]
        push_cast
        linarith [mul_nonneg hn0.le (hy.1 k)]
      · simp only [hq]
        rw [Int.ceil_le]
        have hyk : y k ≤ 1 := hy.2 k
        push_cast
        nlinarith [hn0]
    exact Set.mem_biUnion hyT ⟨φ y, ⟨y, ⟨hy, rfl⟩, rfl⟩, rfl⟩
  have hpiece : ∀ v : Fin (Fintype.card ι - 1) → ℤ,
      (index n '' (φ '' (Set.Icc 0 1 ∩ q ⁻¹' {v}))).ncard
        ≤ (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι :=
    fun v ↦ ncard_index_image_le_of_diam_le_lipschitz hφ
      ((Metric.isBounded_Icc 0 1).subset Set.inter_subset_left) (hdiam v)
  have hfin : ∀ v : Fin (Fintype.card ι - 1) → ℤ,
      (index n '' (φ '' (Set.Icc 0 1 ∩ q ⁻¹' {v}))).Finite :=
    fun v ↦ setFinite_index_image_of_isBounded n
      (hφ.isBounded_image ((Metric.isBounded_Icc 0 1).subset Set.inter_subset_left))
  refine (Set.ncard_le_ncard hcover (T.finite_toSet.biUnion fun v _ ↦ hfin v)).trans ?_
  refine (Finset.set_ncard_biUnion_le T _).trans ?_
  refine (Finset.sum_le_sum fun v _ ↦ hpiece v).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcardT : T.card = (n + 1) ^ (Fintype.card ι - 1) := by
    rw [hT, Pi.card_Icc]
    simp [Int.card_Icc]
  rw [hcardT, Nat.cast_id]

end Sublemmas

end

end Chebotarev
