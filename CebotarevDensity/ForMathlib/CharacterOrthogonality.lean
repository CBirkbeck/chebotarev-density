module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.IntegralDomain

/-!
# Character orthogonality for finite abelian groups

The two orthogonality relations for the characters `G →* Mˣ` of a finite commutative group `G`
valued in a domain `M`, packaged in the form needed for finite-abelian Fourier inversion:

* `sum_char_apply_eq_zero_of_ne_one` — **column orthogonality**: for `g ≠ 1`, the sum
  `∑ χ : G →* Mˣ, χ g` over all characters vanishes (needs enough roots of unity in `M`).
* `sum_char_self_eq_zero_of_ne_one` — **row orthogonality**: for a nontrivial character `χ`, the
  sum `∑ g : G, χ g` over the group vanishes.

Both are thin corollaries of mathlib's `sum_hom_units_eq_zero` (a monoid hom `f : H → R` into a
domain with `f ≠ 1` sums to `0` over a finite group `H`): the row version applies it to
`(Units.coeHom M).comp χ` directly; the column version applies it on the dual group `G →* Mˣ`
along the evaluation hom `χ ↦ χ g`, whose nontriviality comes from
`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`.

From column orthogonality we package the standard **Fourier-inversion** consequence:

* `sum_eq_card_mul_of_sum_char_mul_eq_zero` — a function `f : G → M` whose nontrivial character
  moments `∑ s, χ s · f s` all vanish equals its average, `∑ s, f s = (#(G →* Mˣ)) · f u`.
* `exists_const_of_sum_char_mul_eq_zero` — over a characteristic-zero domain the same hypothesis
  forces `f` to be constant on `G` (`∃ c, f = Function.const G c`).

None of these lemmas mention number fields or Dirichlet density.
-/

@[expose] public section

noncomputable section

variable {G : Type*} [CommGroup G] {M : Type*} [CommRing M] [IsDomain M]

/-- **Character-column orthogonality** for a finite commutative group `G` valued in a domain `M`
with enough roots of unity: for `g ≠ 1`, the sum of `χ g` over all characters `χ : G →* Mˣ`
vanishes. A specialisation of `sum_hom_units_eq_zero` on the dual group `G →* Mˣ` along the
evaluation hom `χ ↦ χ g`. -/
theorem sum_char_apply_eq_zero_of_ne_one [Finite G] [HasEnoughRootsOfUnity M (Monoid.exponent G)]
    [Fintype (G →* Mˣ)] {g : G} (hg : g ≠ 1) :
    ∑ χ : G →* Mˣ, ((χ g : Mˣ) : M) = 0 := by
  obtain ⟨χ₀, hχ₀⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G M hg
  exact sum_hom_units_eq_zero ((Units.coeHom M).comp
    { toFun := fun χ : G →* Mˣ ↦ χ g, map_one' := rfl, map_mul' := fun _ _ ↦ rfl })
    fun h ↦ hχ₀ (Units.val_eq_one.mp (DFunLike.congr_fun h χ₀))

variable [Fintype G]

/-- **Character-row orthogonality** for a finite commutative group `G` valued in a domain `M`:
for a nontrivial character `χ : G →* Mˣ`, the sum of `χ g` over all `g : G` vanishes. A
specialisation of `sum_hom_units_eq_zero` to `(Units.coeHom M).comp χ`. -/
theorem sum_char_self_eq_zero_of_ne_one {χ : G →* Mˣ} (hχ : χ ≠ 1) :
    ∑ g : G, ((χ g : Mˣ) : M) = 0 := by
  obtain ⟨g₀, hg₀⟩ := DFunLike.ne_iff.mp hχ
  rw [MonoidHom.one_apply] at hg₀
  exact sum_hom_units_eq_zero ((Units.coeHom M).comp χ)
    fun h ↦ hg₀ (Units.val_eq_one.mp (DFunLike.congr_fun h g₀))

section

variable [HasEnoughRootsOfUnity M (Monoid.exponent G)]

/-- **Finite-abelian Fourier inversion.** If every nontrivial character moment of `f : G → M`
vanishes — `∑ s, χ s · f s = 0` for each `χ ≠ 1` — then `f` is recovered from its average: for
every `u`, `∑ s, f s = (#(G →* Mˣ)) · f u`. The proof expands `(#(G →* Mˣ)) · f u` by column
orthogonality (`sum_char_apply_eq_zero_of_ne_one`) and collapses the character sum to its
principal term using the hypothesis. -/
theorem sum_eq_card_mul_of_sum_char_mul_eq_zero (f : G → M)
    (hf : ∀ χ : G →* Mˣ, χ ≠ 1 → ∑ s : G, ((χ s : Mˣ) : M) * f s = 0) (u : G) :
    ∑ s : G, f s = (Nat.card (G →* Mˣ) : M) * f u := by
  classical
  have : Fintype (G →* Mˣ) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  symm
  have horth : ∀ s : G, (∑ χ : G →* Mˣ, ((χ (u⁻¹ * s) : Mˣ) : M))
      = if s = u then (Fintype.card (G →* Mˣ) : M) else 0 := by
    intro s
    by_cases hs : s = u
    · simp [hs]
    · rw [if_neg hs]
      exact sum_char_apply_eq_zero_of_ne_one fun h ↦ hs (inv_mul_eq_one.mp h).symm
  calc (Fintype.card (G →* Mˣ) : M) * f u
      = ∑ s : G, (if s = u then (Fintype.card (G →* Mˣ) : M) else 0) * f s := by
        simp
    _ = ∑ s : G, (∑ χ : G →* Mˣ, ((χ (u⁻¹ * s) : Mˣ) : M)) * f s :=
        Finset.sum_congr rfl fun s _ ↦ by rw [horth s]
    _ = ∑ s : G, ∑ χ : G →* Mˣ, ((χ (u⁻¹ * s) : Mˣ) : M) * f s :=
        Finset.sum_congr rfl fun s _ ↦ by rw [Finset.sum_mul]
    _ = ∑ χ : G →* Mˣ, ∑ s : G, ((χ (u⁻¹ * s) : Mˣ) : M) * f s := Finset.sum_comm
    _ = ∑ χ : G →* Mˣ, ((χ u⁻¹ : Mˣ) : M) * ∑ s : G, ((χ s : Mˣ) : M) * f s := by
        refine Finset.sum_congr rfl fun χ _ ↦ ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ ↦ by rw [map_mul, Units.val_mul, mul_assoc]
    _ = ∑ s : G, f s := by
        rw [Finset.sum_eq_single_of_mem (1 : G →* Mˣ) (Finset.mem_univ _)
          fun χ _ hχ ↦ by rw [hf χ hχ, mul_zero]]
        simp

/-- **Vanishing nontrivial Fourier coefficients force a constant.** Over a characteristic-zero
domain, if every nontrivial character moment of `f : G → M` vanishes (`∑ s, χ s · f s = 0` for
`χ ≠ 1`), then `f` is constant. Immediate from `sum_eq_card_mul_of_sum_char_mul_eq_zero`
(every value equals the common average) after cancelling the nonzero dual cardinality. -/
theorem exists_const_of_sum_char_mul_eq_zero [CharZero M] (f : G → M)
    (hf : ∀ χ : G →* Mˣ, χ ≠ 1 → ∑ s : G, ((χ s : Mˣ) : M) * f s = 0) :
    ∃ c, f = Function.const G c := by
  have hcard0 : (Nat.card (G →* Mˣ) : M) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine ⟨f 1, funext fun u ↦ ?_⟩
  exact mul_left_cancel₀ hcard0
    ((sum_eq_card_mul_of_sum_char_mul_eq_zero f hf u).symm.trans
      (sum_eq_card_mul_of_sum_char_mul_eq_zero f hf 1))

end
