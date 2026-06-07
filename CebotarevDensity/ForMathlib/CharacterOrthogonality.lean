module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Character orthogonality for finite abelian groups (complex-valued)

The two orthogonality relations for the complex characters `G →* ℂˣ` of a finite commutative
group `G`, in the form needed for finite-abelian Fourier inversion:

* `sum_char_apply_eq_zero_of_ne_one` — **column orthogonality**: for `g ≠ 1`, the sum
  `∑ χ : G →* ℂˣ, χ g` over all characters vanishes.
* `sum_char_self_eq_zero_of_ne_one` — **row orthogonality**: for a nontrivial character
  `χ`, the sum `∑ g : G, χ g` over the group vanishes.

Both rest on the same translation trick: a separating datum scales the sum by a root of unity
distinct from `1`, forcing the sum to be `0`. The column version draws its separating character
from `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity` (using that `ℂ` is algebraically
closed, hence `HasEnoughRootsOfUnity ℂ`); the row version separates by an element directly.

Neither lemma mentions number fields or Dirichlet density; they are kept in the root namespace
as candidates for upstreaming to mathlib.
-/

@[expose] public section

noncomputable section

private theorem sum_eq_zero_of_mulLeft_mul_const_aux {H : Type*} [Group H] [Fintype H] {M₀ : Type*}
    [Semiring M₀] [IsRightCancelMulZero M₀] (f : H → M₀) (h₀ : H) {c : M₀} (hc : c ≠ 1)
    (hf : ∀ h, f (h₀ * h) = c * f h) : ∑ h : H, f h = 0 := by
  refine eq_zero_of_mul_eq_self_left hc ?_
  rw [Finset.mul_sum]
  exact Fintype.sum_bijective (h₀ * ·) (Group.mulLeft_bijective h₀) _ _ fun h => (hf h).symm

/-- **Character-column orthogonality** for a finite commutative group `G`: for `g ≠ 1`, the sum
of `χ g` over all characters `χ : G →* ℂˣ` vanishes. -/
theorem sum_char_apply_eq_zero_of_ne_one {G : Type*} [CommGroup G] [Finite G]
    [Fintype (G →* ℂˣ)] {g : G} (hg : g ≠ 1) : ∑ χ : G →* ℂˣ, ((χ g : ℂˣ) : ℂ) = 0 := by
  obtain ⟨χ₀, hχ₀⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hg
  exact sum_eq_zero_of_mulLeft_mul_const_aux _ χ₀ (fun h => hχ₀ (Units.ext h))
    fun χ => by rw [MonoidHom.mul_apply, Units.val_mul]

/-- **Character-row orthogonality** for a finite commutative group `G`: for a nontrivial character
`χ : G →* ℂˣ`, the sum of `χ g` over all `g : G` vanishes. -/
theorem sum_char_self_eq_zero_of_ne_one {G : Type*} [CommGroup G] [Fintype G]
    {χ : G →* ℂˣ} (hχ : χ ≠ 1) : ∑ g : G, ((χ g : ℂˣ) : ℂ) = 0 := by
  obtain ⟨g₀, hg₀⟩ := DFunLike.ne_iff.mp hχ
  rw [MonoidHom.one_apply] at hg₀
  exact sum_eq_zero_of_mulLeft_mul_const_aux _ g₀ (fun h => hg₀ (Units.ext h))
    fun g => by rw [map_mul, Units.val_mul]
