module

public import Mathlib.Analysis.BoxIntegral.UnitPartition
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Effective lattice-point count with a Lipschitz-boundary error term

The effective (with explicit `O(tᵈ⁻¹)` rate) strengthening of
`tendsto_card_div_pow_atTop_volume`: for a bounded measurable region whose boundary is
covered by finitely many Lipschitz images of the unit cube, the number of points of the
scaled integer lattice inside the region equals the volume times `nᵈ` up to `O(nᵈ⁻¹)`.

This is the single deepest analytic input to the class-field-theory-free formalisation of
Chebotarev's density theorem: it upgrades the leading-term ideal count to an effective count
with a power-saving error, hence the analytic continuation of the abelian `L`-functions past
`Re s = 1`. It is stated here for a future mathlib contribution.

## Main statement

* `Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le`

## References

* Serge Lang, *Algebraic Number Theory*, 2nd ed., GTM 110, Springer 1994, Ch. V §2 and
  Ch. VI §3 (Theorem 3), p. 129 (the boundary-cell estimate).
* S. Gun, O. Ramaré, J. Sivaraman, *Counting ideals in ray classes*, J. Number Theory 243
  (2023) 13–37, §3.3 (Lipschitz class of the boundary) and §3.5 (counting points), after
  K. Debaene.
-/

open Submodule Pointwise MeasureTheory Set

open scoped NNReal

namespace Chebotarev

@[expose] public section

/-- **Effective lattice-point count (Lang GTM 110 Ch. V §2 / p. 129; Gun–Ramaré–Sivaraman,
*Counting ideals in ray classes*, J. Number Theory 243 (2023) §3.3–3.5, after Debaene).**
For a bounded measurable set `s ⊆ ι → ℝ` whose frontier is covered by finitely many
Lipschitz images of the unit cube `[0,1]^{d-1}` (`d = #ι`), the number of points of the
scaled integer lattice `n⁻¹·ℤ^ι` lying in `s` equals `vol(s)·nᵈ` up to an error `O(nᵈ⁻¹)`.
This is the effective form of `tendsto_card_div_pow_atTop_volume` (whose conclusion is the
rate-free limit `card / nᵈ → vol s`). -/
theorem exists_card_inter_smul_lattice_sub_volume_mul_pow_le
    {ι : Type*} [Fintype ι] (s : Set (ι → ℝ))
    (hbdd : Bornology.IsBounded s) (hmeas : MeasurableSet s)
    (hlip : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ frontier s ⊆ ⋃ j, φ j '' Set.Icc 0 1) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(Nat.card ↑(s ∩ (n : ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) : ℝ)
          - volume.real s * (n : ℝ) ^ Fintype.card ι|
        ≤ C * (n : ℝ) ^ (Fintype.card ι - 1) := by
  sorry

end

end Chebotarev
