module

public import Mathlib.GroupTheory.FiniteAbelian.Duality

/-!
# Character orthogonality for finite abelian groups

The two orthogonality relations for the characters `G →* Mˣ` of a finite commutative group `G`
valued in a domain `M`:

* `sum_char_apply_eq_zero_of_ne_one` — **column orthogonality**: for `g ≠ 1`, the sum
  `∑ χ : G →* Mˣ, χ g` over all characters vanishes (needs enough roots of unity in `M`).
* `sum_char_self_eq_zero_of_ne_one` — **row orthogonality**: for a nontrivial character `χ`, the
  sum `∑ g : G, χ g` over the group vanishes.

Both rest on the same translation trick: a separating datum scales the sum by a value distinct
from `1`, forcing the sum to be `0` (a domain has no nonzero fixed point of multiplication by a
non-`1` element). The column version draws its separating character from
`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`; the row version separates by a group
element directly.

These are kept in the root namespace as candidates for upstreaming to mathlib; the
Fourier-inversion consequences are added in a follow-up.
-/

@[expose] public section

noncomputable section

private theorem sum_eq_zero_of_mulLeft_mul_const_aux {H : Type*} [Group H] [Fintype H] {M₀ : Type*}
    [Semiring M₀] [IsRightCancelMulZero M₀] (f : H → M₀) (h₀ : H) {c : M₀} (hc : c ≠ 1)
    (hf : ∀ h, f (h₀ * h) = c * f h) : ∑ h : H, f h = 0 := by
  refine eq_zero_of_mul_eq_self_left hc ?_
  rw [Finset.mul_sum]
  exact Fintype.sum_bijective (h₀ * ·) (Group.mulLeft_bijective h₀) _ _ fun h ↦ (hf h).symm

variable {G : Type*} [CommGroup G] {M : Type*} [CommRing M] [IsDomain M]

/-- **Character-column orthogonality** for a finite commutative group `G` valued in a domain `M`
with enough roots of unity: for `g ≠ 1`, the sum of `χ g` over all characters `χ : G →* Mˣ`
vanishes. -/
theorem sum_char_apply_eq_zero_of_ne_one [Finite G]
    [HasEnoughRootsOfUnity M (Monoid.exponent G)] [Fintype (G →* Mˣ)] {g : G} (hg : g ≠ 1) :
    ∑ χ : G →* Mˣ, ((χ g : Mˣ) : M) = 0 := by
  obtain ⟨χ₀, hχ₀⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G M hg
  exact sum_eq_zero_of_mulLeft_mul_const_aux _ χ₀ (fun h ↦ hχ₀ (Units.ext h))
    fun χ ↦ by rw [MonoidHom.mul_apply, Units.val_mul]

variable [Fintype G]

/-- **Character-row orthogonality** for a finite commutative group `G` valued in a domain `M`:
for a nontrivial character `χ : G →* Mˣ`, the sum of `χ g` over all `g : G` vanishes. -/
theorem sum_char_self_eq_zero_of_ne_one {χ : G →* Mˣ} (hχ : χ ≠ 1) :
    ∑ g : G, ((χ g : Mˣ) : M) = 0 := by
  obtain ⟨g₀, hg₀⟩ := DFunLike.ne_iff.mp hχ
  rw [MonoidHom.one_apply] at hg₀
  exact sum_eq_zero_of_mulLeft_mul_const_aux _ g₀ (fun h ↦ hg₀ (Units.ext h))
    fun g ↦ by rw [map_mul, Units.val_mul]
