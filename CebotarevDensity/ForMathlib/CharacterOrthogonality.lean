module

public import Mathlib.GroupTheory.FiniteAbelian.Duality

/-!
# Character orthogonality for finite abelian groups

The two orthogonality relations for the characters `G →* Mˣ` of a finite commutative group `G`
valued in a domain `M`, in the form needed for finite-abelian Fourier inversion:

* `sum_char_apply_eq_zero_of_ne_one` — **column orthogonality**: for `g ≠ 1`, the sum
  `∑ χ : G →* Mˣ, χ g` over all characters vanishes (needs enough roots of unity in `M`).
* `sum_char_self_eq_zero_of_ne_one` — **row orthogonality**: for a nontrivial character
  `χ`, the sum `∑ g : G, χ g` over the group vanishes.

Both rest on the same translation trick: a separating datum scales the sum by a value
distinct from `1`, forcing the sum to be `0` (a domain has no nonzero fixed point of
multiplication by a non-`1` element). The column version draws its separating character
from `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`; the row version separates by a
group element directly.

From column orthogonality we package the standard **Fourier-inversion** consequence:

* `card_mul_eq_sum_of_sum_char_mul_eq_zero` — a function `f : G → M` whose nontrivial character
  moments `∑ s, χ s · f s` all vanish equals its average, `(#(G →* Mˣ)) · f u = ∑ s, f s`.
* `eq_of_sum_char_mul_eq_zero` — over a characteristic-zero domain the same hypothesis forces
  `f` to be constant on `G`.

None of these lemmas mention number fields or Dirichlet density; they are kept in the root
namespace as candidates for upstreaming to mathlib.
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

/-- **Character-row orthogonality** for a finite commutative group `G` valued in a domain `M`:
for a nontrivial character `χ : G →* Mˣ`, the sum of `χ g` over all `g : G` vanishes. -/
theorem sum_char_self_eq_zero_of_ne_one [Fintype G] {χ : G →* Mˣ} (hχ : χ ≠ 1) :
    ∑ g : G, ((χ g : Mˣ) : M) = 0 := by
  obtain ⟨g₀, hg₀⟩ := DFunLike.ne_iff.mp hχ
  rw [MonoidHom.one_apply] at hg₀
  exact sum_eq_zero_of_mulLeft_mul_const_aux _ g₀ (fun h ↦ hg₀ (Units.ext h))
    fun g ↦ by rw [map_mul, Units.val_mul]

/-- **Finite-abelian Fourier inversion.** If every nontrivial character moment of `f : G → M`
vanishes — `∑ s, χ s · f s = 0` for each `χ ≠ 1` — then `f` is recovered from its average: for
every `u`, `(#(G →* Mˣ)) · f u = ∑ s, f s`. The proof expands the right side by column
orthogonality (`sum_char_apply_eq_zero_of_ne_one`) and collapses the character sum to its
principal term using the hypothesis. -/
theorem card_mul_eq_sum_of_sum_char_mul_eq_zero [Fintype G]
    [HasEnoughRootsOfUnity M (Monoid.exponent G)] [Fintype (G →* Mˣ)] (f : G → M)
    (hf : ∀ χ : G →* Mˣ, χ ≠ 1 → ∑ s : G, ((χ s : Mˣ) : M) * f s = 0) (u : G) :
    (Fintype.card (G →* Mˣ) : M) * f u = ∑ s : G, f s := by
  classical
  have horth : ∀ s : G, (∑ χ : G →* Mˣ, ((χ (u⁻¹ * s) : Mˣ) : M))
      = if s = u then (Fintype.card (G →* Mˣ) : M) else 0 := by
    intro s
    by_cases hs : s = u
    · subst hs; simp
    · rw [if_neg hs]
      exact sum_char_apply_eq_zero_of_ne_one fun h ↦ hs (inv_mul_eq_one.mp h).symm
  calc (Fintype.card (G →* Mˣ) : M) * f u
      = ∑ s : G, (if s = u then (Fintype.card (G →* Mˣ) : M) else 0) * f s := by
        simp
    _ = ∑ s : G, (∑ χ : G →* Mˣ, ((χ (u⁻¹ * s) : Mˣ) : M)) * f s := by
        refine Finset.sum_congr rfl fun s _ ↦ ?_; rw [horth s]
    _ = ∑ s : G, ∑ χ : G →* Mˣ, ((χ (u⁻¹ * s) : Mˣ) : M) * f s := by
        refine Finset.sum_congr rfl fun s _ ↦ ?_; rw [Finset.sum_mul]
    _ = ∑ χ : G →* Mˣ, ∑ s : G, ((χ (u⁻¹ * s) : Mˣ) : M) * f s := Finset.sum_comm
    _ = ∑ χ : G →* Mˣ, ((χ u⁻¹ : Mˣ) : M) * ∑ s : G, ((χ s : Mˣ) : M) * f s := by
        refine Finset.sum_congr rfl fun χ _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        rw [map_mul, Units.val_mul, mul_assoc]
    _ = ∑ s : G, f s := by
        rw [Finset.sum_eq_single_of_mem (1 : G →* Mˣ) (Finset.mem_univ _)
          fun χ _ hχ ↦ by rw [hf χ hχ, mul_zero]]
        simp

/-- **Vanishing nontrivial Fourier coefficients force a constant.** Over a characteristic-zero
domain, if every nontrivial character moment of `f : G → M` vanishes (`∑ s, χ s · f s = 0` for
`χ ≠ 1`), then `f` takes the same value at every pair of points. Immediate from
`card_mul_eq_sum_of_sum_char_mul_eq_zero` (both values equal the common average) after cancelling
the nonzero dual cardinality. -/
theorem eq_of_sum_char_mul_eq_zero [Fintype G] [CharZero M]
    [HasEnoughRootsOfUnity M (Monoid.exponent G)] (f : G → M)
    (hf : ∀ χ : G →* Mˣ, χ ≠ 1 → ∑ s : G, ((χ s : Mˣ) : M) * f s = 0) (u u' : G) :
    f u = f u' := by
  have : Fintype (G →* Mˣ) := Fintype.ofFinite _
  have hcard0 : (Fintype.card (G →* Mˣ) : M) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact mul_left_cancel₀ hcard0
    ((card_mul_eq_sum_of_sum_char_mul_eq_zero f hf u).trans
      (card_mul_eq_sum_of_sum_char_mul_eq_zero f hf u').symm)
