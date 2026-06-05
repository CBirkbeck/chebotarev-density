module

public import CebotarevDensity.ForMathlib.LatticePointCount
public import CebotarevDensity.ForMathlib.NormLeOneLipschitz
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics

/-!
# Effective counting of ideals by class and norm residue

The effective (`O(N^{1-1/d})`-error) refinement of mathlib's ideal-counting asymptotics
(`NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop`), additionally split by the residue of
the ideal norm modulo a fixed modulus `c`. This is the arithmetic engine of the
Frobenius-fibre equidistribution (Gap B / L2): for `L = K(μ_m)` the Frobenius of an ideal is cut
out by its norm residue, so the fibre count reduces to the counts provided here.

Sources: Gun–Ramaré–Sivaraman, *Counting ideals in ray classes*, JNT 243 (2023) (Thm 1, §3),
specialised; Lang, *Algebraic Number Theory* GTM 110, Ch. VI §3 Thm 3 (the classical
fundamental-domain count); Widmer (Trans. AMS 362 (2010)) for the lattice-point input, already
formalised as `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` (L1) with the Lipschitz
frontier input `normLeOne_frontier_lipschitz_cover` (Gap A).

## Architecture

* `exists_card_coset_inter_smul_sub_volume_mul_rpow_le` — the workhorse: for a full lattice
  `Λ = T '' ℤ^ι` (`T` a linear automorphism), a bounded measurable region `D` with
  Lipschitz-covered frontier, and **any coset translate `ξ` and real dilation `t ≥ 1`**:
  `#((ξ + Λ) ∩ t • D) = vol D / covol Λ · t^d + O(t^{d-1})`, the constant uniform in `ξ`
  (it depends only on the frontier-cover data, as in L1). Proof: linear transport of L1
  (`T⁻¹` carries `Λ` to `ℤ^ι`, scales the volume by `|det T|⁻¹` and composes the Lipschitz
  cover), a translation reduction (translate the region; the cover data is
  translation-invariant), and the floor sandwich `⌊t⌋ • D ⊆ t • D ⊆ ⌈t⌉ • D` to pass from the
  natural dilations of L1 to real `t`.

* sign-orthant refinement: on the region cut out by a fixed sign pattern of the real
  coordinates, the **algebraic** norm of a lattice point has constant sign, so the condition
  `|Norm x| ≡ b (mod c)` becomes `Norm x ≡ ±b`, which is constant on cosets of `c • Λ`
  (`Norm (x + c y) ≡ Norm x (mod c)`). The orthant-cut regions keep Lipschitz-covered
  frontiers (`frontier (A ∩ orthant) ⊆ frontier A ∪ (closure A ∩ coordinate hyperplanes)`,
  and bounded hyperplane pieces are Lipschitz images of the cube).

* `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le` — the per-residue effective ideal
  count: `#{I : N(I) ≤ N, N(I) ≡ a (mod c)} = κ_a N + O(N^{1-1/d})`. Proof: split by ideal
  class; per class, mathlib's principalization dictionary (the `tendsto_norm_le_and_mk_eq_*`
  reduction: ideals of class `C` and norm `≤ s` ↔ cone points of the ideal lattice of a
  representative `J` of norm `≤ s·N(J)`, up to torsion); refine by the norm-residue condition,
  which on the lattice side is a union of cosets of `(c·N(J)) • Λ_J` per sign-orthant; count
  each coset by the workhorse with the Gap-A frontier cover.

* `card_norm_le_norm_residue_kappa_mul_eq` — the κ-transfer: multiplication by a fixed
  nonzero ideal `𝔟` with `N(𝔟)` coprime to `c` is an injection
  `{N(I) ≤ N, N(I) ≡ a} ↪ {N(I) ≤ N·N(𝔟), N(I) ≡ a·N(𝔟)}` (with controlled complement),
  so the leading densities satisfy `κ_a = κ_{a·N(𝔟) mod c}`. This is a statement about the
  limits only — no error rate is needed for the transfer — and provides the
  `g`-independence of the Frobenius-fibre density over the image subgroup of ideal norms.
-/

@[expose] public section

noncomputable section

namespace Chebotarev

open NumberField Set Submodule

open scoped NNReal nonZeroDivisors Pointwise

/-! ### The workhorse: coset lattice points in real dilations of a Lipschitz-bounded region -/

/-- **Effective coset lattice-point count** (Widmer / GRS Theorem 3 as used; the
translate-and-transport closure of L1). For a full lattice `T '' ℤ^ι` (`T` a linear
automorphism of `ι → ℝ`) and a bounded measurable region `D` whose frontier is covered by
finitely many Lipschitz images of the unit cube, the number of points of **any** coset
`ξ + T '' ℤ^ι` in the real dilation `t • D` is `vol D / |det T| · t ^ d + O(t ^ (d-1))`,
with the implied constant **uniform in the translate `ξ`** (it depends only on the cover
data and `T`, as the L1 constant depends only on the cover data). -/
theorem exists_card_coset_inter_smul_sub_volume_mul_rpow_le
    {ι : Type*} [Fintype ι] (T : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (D : Set (ι → ℝ))
    (hbdd : Bornology.IsBounded D) (hmeas : MeasurableSet D)
    (hlip : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ frontier D ⊆ ⋃ j, φ j '' Set.Icc 0 1) :
    ∃ C : ℝ, ∀ ξ : ι → ℝ, ∀ t : ℝ, 1 ≤ t →
      |(Nat.card ↑((ξ +ᵥ (T '' (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)))) ∩ t • D) : ℝ)
          - MeasureTheory.volume.real D / |LinearMap.det (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))|
            * t ^ (Fintype.card ι)|
        ≤ C * t ^ (Fintype.card ι - 1 : ℕ) := by
  sorry

/-! ### The per-residue effective ideal count -/

/-- **Effective ideal count by norm residue.** For a number field `K` and a modulus `c`, the
number of nonzero integral ideals of norm `≤ N` with norm residue `a (mod c)` is
`κ_a · N + O(N^{1-1/d})`, `d = [K:ℚ]`. Proof plan: split by ideal class (finitely many); per
class, mathlib's principalization dictionary (`tendsto_norm_le_and_mk_eq_div_atTop`'s aux
equivalences) trades ideals of class `C`, norm `≤ N` for cone points of the ideal lattice
`Λ_J` of a representative `J` with `mixedEmbedding.norm ≤ N·N(J)`, up to the torsion order;
the norm-residue condition becomes, per sign-orthant of the real coordinates, a union of
cosets of `(c·N(J)) • Λ_J` (the algebraic norm is constant mod `c·N(J)` on such cosets and
has constant sign per orthant); each orthant-cut region has Lipschitz-covered frontier
(Gap A's `normLeOne_frontier_lipschitz_cover` plus bounded hyperplane pieces), so the
workhorse `exists_card_coset_inter_smul_sub_volume_mul_rpow_le` counts each coset with the
uniform `O(t^{d-1})` error at `t = (N·N(J))^{1/d}`. -/
theorem exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le
    (K : Type*) [Field K] [NumberField K] (c : ℕ) [NeZero c] (a : ZMod c) :
    ∃ κ C' : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a} : ℝ)
          - κ * N|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  sorry

/-- **Norm-residue density transfer (κ-uniformity over realized residues).** If every residue
in a subgroup `S ≤ (ℤ/c)ˣ` is realized as the norm residue of some nonzero ideal, then the
leading densities of `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le` can be taken
**equal across `S`**: multiplication by a fixed ideal `𝔟` with `(N𝔟 : ZMod c) = t` injects
`{N(I) ≤ N, N(I) ≡ a}` into `{N(I) ≤ N·N𝔟, N(I) ≡ a·t}` with complement of relative density
`0`, so the leading constants — which are pinned as the limits of `count/N` by the effective
bounds — satisfy `κ_a ≤ N𝔟 · κ_{a·t}` and (using the inverse residue, `S` a group)
conversely; a short sandwich gives `κ_a = κ_{a·t}` for all `t` realized, hence constancy on
`S`-cosets, in particular on `S`. This is the `g`-independence input of the Frobenius-fibre
equidistribution (the `ℚ(i)`-trap avoidance: uniformity over the **image subgroup** of ideal
norms, never over all of `(ℤ/c)ˣ`). -/
theorem exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform
    (K : Type*) [Field K] [NumberField K] (c : ℕ) [NeZero c] (S : Subgroup (ZMod c)ˣ)
    (hS : ∀ a ∈ S, ∃ 𝔟 : (Ideal (𝓞 K))⁰,
      ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) = (a : ZMod c)) :
    ∃ κ C' : ℝ, ∀ a ∈ S, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = (a : ZMod c)} : ℝ)
          - κ * N|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  sorry

end Chebotarev
