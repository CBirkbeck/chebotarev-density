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

/-- **Character-column orthogonality** for a finite commutative group `G`: for `g ≠ 1`, the sum
of `χ g` over all characters `χ : G →* ℂˣ` vanishes. -/
theorem sum_char_apply_eq_zero_of_ne_one {G : Type*} [CommGroup G] [Finite G]
    [Fintype (G →* ℂˣ)] {g : G} (hg : g ≠ 1) : ∑ χ : G →* ℂˣ, ((χ g : ℂˣ) : ℂ) = 0 := by
  classical
  haveI : NeZero ((Monoid.exponent G : ℕ) : ℂ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩
  obtain ⟨χ₀, hχ₀⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hg
  have hshift : ((χ₀ g : ℂˣ) : ℂ) * ∑ χ : G →* ℂˣ, ((χ g : ℂˣ) : ℂ) =
      ∑ χ : G →* ℂˣ, ((χ g : ℂˣ) : ℂ) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_bijective (χ₀ * ·) (Group.mulLeft_bijective χ₀)
      (fun χ => ((χ₀ g : ℂˣ) : ℂ) * ((χ g : ℂˣ) : ℂ)) (fun χ => ((χ g : ℂˣ) : ℂ)) fun χ => ?_
    rw [MonoidHom.mul_apply, Units.val_mul]
  have h0 : (((χ₀ g : ℂˣ) : ℂ) - 1) * ∑ χ : G →* ℂˣ, ((χ g : ℂˣ) : ℂ) = 0 := by
    rw [sub_mul, one_mul, hshift, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (Units.ext (by simpa using sub_eq_zero.mp h)) hχ₀
  · exact h

/-- **Character-row orthogonality** for a finite commutative group `G`: for a nontrivial character
`χ : G →* ℂˣ`, the sum of `χ g` over all `g : G` vanishes. -/
theorem sum_char_self_eq_zero_of_ne_one {G : Type*} [CommGroup G] [Fintype G]
    {χ : G →* ℂˣ} (hχ : χ ≠ 1) : ∑ g : G, ((χ g : ℂˣ) : ℂ) = 0 := by
  classical
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : G, χ g₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact hχ (MonoidHom.ext fun g => by simpa using h g)
  have hshift : ((χ g₀ : ℂˣ) : ℂ) * ∑ g : G, ((χ g : ℂˣ) : ℂ) = ∑ g : G, ((χ g : ℂˣ) : ℂ) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_bijective (g₀ * ·) (Group.mulLeft_bijective g₀)
      (fun g => ((χ g₀ : ℂˣ) : ℂ) * ((χ g : ℂˣ) : ℂ)) (fun g => ((χ g : ℂˣ) : ℂ)) fun g => ?_
    rw [map_mul, Units.val_mul]
  have h0 : (((χ g₀ : ℂˣ) : ℂ) - 1) * ∑ g : G, ((χ g : ℂˣ) : ℂ) = 0 := by
    rw [sub_mul, one_mul, hshift, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (Units.ext (sub_eq_zero.mp h)) hg₀
  · exact h
