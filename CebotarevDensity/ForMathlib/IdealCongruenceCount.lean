module

public import CebotarevDensity.ForMathlib.LatticePointCount
public import CebotarevDensity.ForMathlib.NormLeOneLipschitz
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic

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

section RealScale

open MeasureTheory BoxIntegral BoxIntegral.unitPartition

variable {ι : Type*} [Fintype ι]

/-- The image of `ι → ℤ` inside `ι → ℝ`, abbreviated as in `LatticePointCount`. -/
local notation "Λ" => span ℤ (Set.range (Pi.basisFun ℝ ι))

/-- **Real-scale scaled-translated chart count.** For an `M`-Lipschitz map `φ` and a real scale
`c ≥ 1`, the number of unit grid cells (`index 1`) meeting the scaled-and-translated chart image
`{v + c • φ y : y ∈ [0,1]ᵈ⁻¹}` is at most `(2⌈M⌉₊ + 1)ᵈ · (⌈c⌉₊ + 1)ᵈ⁻¹ = O(cᵈ⁻¹)`. This is the
chart core of `LatticePointCount`'s `ncard_index_image_chart_le` adapted to count the *unit* grid
against the *region scaled by `c`*: subdivide `[0,1]ᵈ⁻¹` into the `(⌈c⌉₊+1)ᵈ⁻¹` fibres of
`y ↦ ⌈⌈c⌉₊ yₖ⌉`; each fibre has diameter `≤ 1/⌈c⌉₊`, so the `(v + c • φ ·)`-image has diameter
`≤ c·M/⌈c⌉₊ ≤ M` (as `c ≤ ⌈c⌉₊`), hence meets `≤ (2⌈M⌉₊+1)ᵈ` unit cells. -/
private theorem ncard_index1_image_smul_chart_le {M : ℝ≥0}
    {φ : (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)} (hφ : LipschitzWith M φ)
    {c : ℝ} (hc : 1 ≤ c) (v : ι → ℝ) :
    (index 1 '' ((fun y ↦ v + c • φ y) '' Set.Icc 0 1)).ncard
      ≤ (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * (⌈c⌉₊ + 1) ^ (Fintype.card ι - 1) := by
  classical
  set N : ℕ := ⌈c⌉₊ with hN
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  have hN1 : 1 ≤ N := Nat.one_le_ceil_iff.mpr hcpos
  have hNne : NeZero N := ⟨Nat.one_le_iff_ne_zero.mp hN1⟩
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hNne.out
  have hcN : c ≤ (N : ℝ) := Nat.le_ceil c
  set ψ : (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ) := fun y ↦ v + c • φ y with hψ
  have hψbdd : ∀ A : Set (Fin (Fintype.card ι - 1) → ℝ), Bornology.IsBounded A →
      Bornology.IsBounded (ψ '' A) := by
    intro A hA
    have hb : Bornology.IsBounded (φ '' A) := hφ.isBounded_image hA
    have heq : ψ '' A = v +ᵥ (c • (φ '' A)) := by
      ext z
      simp only [hψ, Set.mem_image, Set.mem_vadd_set, Set.mem_smul_set]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact ⟨c • φ y, ⟨φ y, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨u, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩; exact ⟨y, hy, rfl⟩
    rw [heq]
    exact (hb.smul₀ c).vadd v
  -- The "domain grid" map: which subcube of side `1/N` of `[0,1]ᵈ⁻¹` a point lies in.
  set q : (Fin (Fintype.card ι - 1) → ℝ) → (Fin (Fintype.card ι - 1) → ℤ) :=
    fun y k ↦ ⌈(N : ℝ) * y k⌉ with hq
  -- The finite index set of admissible subcubes: `[0,N]ᵈ⁻¹ ∩ ℤᵈ⁻¹`.
  set T : Finset (Fin (Fintype.card ι - 1) → ℤ) :=
    Finset.Icc (0 : Fin (Fintype.card ι - 1) → ℤ) (fun _ ↦ (N : ℤ)) with hT
  -- Each fibre of `q` inside `[0,1]ᵈ⁻¹` has diameter `≤ 1/N`.
  have hdiam : ∀ w : Fin (Fintype.card ι - 1) → ℤ,
      Metric.diam (Set.Icc (0 : Fin (Fintype.card ι - 1) → ℝ) 1 ∩ q ⁻¹' {w}) ≤ 1 / N := by
    intro w
    refine Metric.diam_le_of_forall_dist_le (by positivity) fun y hy y' hy' ↦ ?_
    rw [dist_pi_le_iff (by positivity)]
    intro k
    have hyv : (⌈(N : ℝ) * y k⌉ : ℤ) = w k := congrFun hy.2 k
    have hyv' : (⌈(N : ℝ) * y' k⌉ : ℤ) = w k := congrFun hy'.2 k
    have hce : ⌈(N : ℝ) * y k⌉ = ⌈(N : ℝ) * y' k⌉ := hyv.trans hyv'.symm
    have h1 : (⌈(N : ℝ) * y k⌉ : ℝ) - 1 < (N : ℝ) * y k ∧ (N : ℝ) * y k ≤ ⌈(N : ℝ) * y k⌉ :=
      Int.ceil_eq_iff.mp rfl
    have h2 : (⌈(N : ℝ) * y' k⌉ : ℝ) - 1 < (N : ℝ) * y' k ∧ (N : ℝ) * y' k ≤ ⌈(N : ℝ) * y' k⌉ :=
      Int.ceil_eq_iff.mp rfl
    rw [hce] at h1
    have habs : |(N : ℝ) * y k - (N : ℝ) * y' k| ≤ 1 := by
      rw [abs_le]
      constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
    rw [Real.dist_eq, show y k - y' k = ((N : ℝ) * y k - (N : ℝ) * y' k) / N by
        field_simp, abs_div, abs_of_pos hN0]
    rw [div_le_div_iff_of_pos_right hN0]
    exact habs
  -- The chart image is covered by the `index 1`-images of the `ψ`-images of the fibres.
  have hcover : index 1 '' (ψ '' Set.Icc 0 1) ⊆
      ⋃ w ∈ T, index 1 '' (ψ '' (Set.Icc (0 : Fin (Fintype.card ι - 1) → ℝ) 1 ∩ q ⁻¹' {w})) := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hyT : q y ∈ T := by
      rw [hT, Finset.mem_Icc]
      refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
      · simp only [hq, Pi.zero_apply]
        rw [Int.le_ceil_iff]
        have h0 : (0 : ℝ) ≤ (N : ℝ) * y k := mul_nonneg hN0.le (hy.1 k)
        push_cast
        linarith
      · simp only [hq]
        rw [Int.ceil_le]
        have hyk : y k ≤ 1 := (hy.2 k)
        push_cast
        nlinarith [hN0]
    exact Set.mem_biUnion hyT ⟨ψ y, ⟨y, ⟨hy, rfl⟩, rfl⟩, rfl⟩
  -- Each piece has at most `(2⌈M⌉₊+1)ᵈ` points by the incidence bound at unit scale.
  have hpiece : ∀ w : Fin (Fintype.card ι - 1) → ℤ,
      (index 1 '' (ψ '' (Set.Icc (0 : Fin (Fintype.card ι - 1) → ℝ) 1 ∩ q ⁻¹' {w}))).ncard
        ≤ (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι := by
    intro w
    set S : Set (Fin (Fintype.card ι - 1) → ℝ) :=
      Set.Icc (0 : Fin (Fintype.card ι - 1) → ℝ) 1 ∩ q ⁻¹' {w} with hS
    have hSbdd : Bornology.IsBounded S :=
      (Metric.isBounded_Icc 0 1).subset Set.inter_subset_left
    have hbddφ : Bornology.IsBounded (ψ '' S) := hψbdd S hSbdd
    -- Diameter of the scaled-translated image: `≤ |c|·M/N ≤ M`, via `dist_smul₀`.
    have hdimg : Metric.diam (ψ '' S) ≤ (M : ℝ) := by
      refine Metric.diam_le_of_forall_dist_le M.coe_nonneg ?_
      rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
      have hdd : dist (ψ y) (ψ y') = |c| * dist (φ y) (φ y') := by
        simp only [hψ, dist_add_left, dist_smul₀, Real.norm_eq_abs]
      have hφd : dist (φ y) (φ y') ≤ (M : ℝ) * (1 / N) := by
        refine (hφ.dist_le_mul y y').trans ?_
        refine mul_le_mul_of_nonneg_left ?_ M.coe_nonneg
        exact (Metric.dist_le_diam_of_mem hSbdd hy hy').trans (hdiam w)
      rw [hdd, abs_of_pos hcpos]
      have hfin : c * ((M : ℝ) * (1 / N)) ≤ (M : ℝ) := by
        rw [mul_one_div, mul_div_assoc', div_le_iff₀ hN0]
        nlinarith [hcN, M.coe_nonneg]
      exact le_trans (mul_le_mul_of_nonneg_left hφd hcpos.le) hfin
    refine (ncard_index_image_le_of_diam_le 1 M.coe_nonneg ?_ hbddφ).trans ?_
    · simpa using hdimg
    · simp
  -- Assemble.
  have hfin : ∀ w : Fin (Fintype.card ι - 1) → ℤ,
      (index 1 '' (ψ '' (Set.Icc (0 : Fin (Fintype.card ι - 1) → ℝ) 1 ∩ q ⁻¹' {w}))).Finite :=
    fun w ↦ setFinite_index_image_of_isBounded 1
      (hψbdd _ ((Metric.isBounded_Icc 0 1).subset Set.inter_subset_left))
  refine (Set.ncard_le_ncard hcover (T.finite_toSet.biUnion fun w _ ↦ hfin w)).trans ?_
  refine (Finset.set_ncard_biUnion_le T _).trans ?_
  refine (Finset.sum_le_sum fun w _ ↦ hpiece w).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcardT : T.card = (N + 1) ^ (Fintype.card ι - 1) := by
    rw [hT, Pi.card_Icc]
    simp only [Pi.zero_apply]
    have hk : ∀ k : Fin (Fintype.card ι - 1),
        (Finset.Icc (0 : ℤ) (N : ℤ)).card = N + 1 := by
      intro k
      rw [Int.card_Icc]
      simp
    rw [Finset.prod_congr rfl fun k _ ↦ hk k, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [hcardT, Nat.cast_id]

/-- **Translate-uniform, real-scale lattice-point count (explicit constant).** For a bounded
measurable `s` whose frontier is covered by `m` images of `M`-Lipschitz maps, *any* coset
translate `w` of the standard lattice, and *any* real dilation `c ≥ 1`, the number of points of
`c⁻¹ • (w +ᵥ ℤ^ι)` in `s` differs from `vol(s)·cᵈ` by at most
`(m·(2⌈M⌉₊+1)ᵈ·3ᵈ⁻¹)·cᵈ⁻¹`. The constant depends only on the cover data and the dimension —
crucially **not** on `w`, `c`, or `vol s` — so it survives the translation reduction in the main
proof, where the translate `w/c` varies. The proof reduces, via a scaling bijection (`x ↦ c•x`)
and a translation bijection (`x ↦ x - w`), to the unit-grid count of `LatticePointCount`'s
`abs_card_inter_sub_volume_mul_pow_le` applied to the region `R = -w +ᵥ c•s`, whose boundary
cells are counted by `ncard_index1_image_smul_chart_le`. -/
private theorem abs_cardR_translate_sub_volume_le {s : Set (ι → ℝ)}
    (hbdd : Bornology.IsBounded s) (hmeas : MeasurableSet s) {m : ℕ} {M : ℝ≥0}
    {φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)} (hφ : ∀ j, LipschitzWith M (φ j))
    (hcov : frontier s ⊆ ⋃ j, φ j '' Set.Icc 0 1) (w : ι → ℝ) {c : ℝ} (hc : 1 ≤ c) :
    |(Nat.card ↑(s ∩ c⁻¹ • (w +ᵥ (Λ : Set (ι → ℝ)))) : ℝ) - volume.real s * c ^ Fintype.card ι|
      ≤ (m * (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * 3 ^ (Fintype.card ι - 1) : ℕ)
          * c ^ (Fintype.card ι - 1) := by
  classical
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  have hc0 : c ≠ 0 := hcpos.ne'
  -- The region `R = -w +ᵥ c•s`.
  set R : Set (ι → ℝ) := (-w) +ᵥ (c • s) with hR
  -- Count identity: `#(s ∩ c⁻¹•(w +ᵥ Λ)) = #(R ∩ Λ)`.
  have hcount : Nat.card ↑(s ∩ c⁻¹ • (w +ᵥ (Λ : Set (ι → ℝ)))) = Nat.card ↑(R ∩ Λ) := by
    -- bijection 1: scaling `x ↦ c•x` on the general set `L := w +ᵥ Λ`.
    have hbij1 : ↑(s ∩ c⁻¹ • (w +ᵥ (Λ : Set (ι → ℝ)))) ≃ ↑(c • s ∩ (w +ᵥ (Λ : Set (ι → ℝ)))) :=
      Equiv.subtypeEquiv (Equiv.smulRight hc0) (fun x ↦ by
        simp_rw [Set.mem_inter_iff, Equiv.smulRight_apply, Set.smul_mem_smul_set_iff₀ hc0,
          ← Set.mem_inv_smul_set_iff₀ hc0])
    rw [Nat.card_congr hbij1]
    -- bijection 2: translation `x ↦ -w +ᵥ x`.
    have heq : (-w) +ᵥ ((c • s) ∩ (w +ᵥ (Λ : Set (ι → ℝ)))) = R ∩ Λ := by
      rw [Set.vadd_set_inter, hR]
      congr 1
      rw [vadd_vadd]
      simp
    rw [← heq]
    exact (Nat.card_image_of_injective (fun a b h ↦ by simpa using h) _).symm
  rw [hcount]
  -- Apply the natural-scale unit-grid bridge to `R` at `n = 1`.
  have hRbdd : Bornology.IsBounded R := (hbdd.smul₀ c).vadd (-w)
  have hRmeas : MeasurableSet R := (hmeas.const_smul_of_ne_zero hc0).const_vadd (-w)
  have hbridge := abs_card_inter_sub_volume_mul_pow_le hRbdd hRmeas (n := 1) le_rfl
  rw [Nat.cast_one, inv_one, one_smul, one_pow, mul_one] at hbridge
  -- Volume: `vol.real R = cᵈ · vol.real s`.
  have hvolR : volume.real R = c ^ Fintype.card ι * volume.real s := by
    rw [hR, Measure.real, measure_vadd, ← Measure.real,
      show volume.real (c • s) = |c| ^ (Fintype.card ι) * volume.real s by
        rw [Measure.real, Measure.real, MeasureTheory.Measure.addHaar_smul,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), abs_pow, Module.finrank_pi],
      abs_of_pos hcpos]
  rw [hvolR] at hbridge
  -- Boundary cover of `R`: each chart becomes `y ↦ -w + c • φⱼ y`.
  have hchart_eq : ∀ j, (-w) +ᵥ (c • (φ j '' Set.Icc 0 1))
      = (fun y ↦ (-w) + c • φ j y) '' Set.Icc 0 1 := by
    intro j
    ext z
    simp only [Set.mem_vadd_set, Set.mem_smul_set, Set.mem_image]
    constructor
    · rintro ⟨u, ⟨v, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩; exact ⟨y, hy, by simp [vadd_eq_add]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨c • φ j y, ⟨φ j y, ⟨y, hy, rfl⟩, rfl⟩, by simp [vadd_eq_add]⟩
  have hfrontR : frontier R ⊆ ⋃ j, (fun y ↦ (-w) + c • φ j y) '' Set.Icc 0 1 := by
    have hcfr : c • frontier s = frontier (c • s) := by
      have := (Homeomorph.smulOfNeZero c hc0).image_frontier s
      simpa using this
    have hfr : frontier R = (-w) +ᵥ (c • frontier s) := by
      have h1 : frontier R = (Homeomorph.addLeft (-w)) '' frontier (c • s) :=
        ((Homeomorph.addLeft (-w)).image_frontier (c • s)).symm
      rw [h1, ← hcfr]
      rfl
    rw [hfr]
    refine (Set.vadd_set_mono (Set.smul_set_mono hcov)).trans ?_
    rw [Set.smul_set_iUnion, Set.vadd_set_iUnion]
    exact Set.iUnion_mono fun j ↦ (hchart_eq j).le
  -- Boundary-cell count: cover `index 1 '' frontier R` by the chart images and apply Helper 1.
  have hbdcell : (index 1 '' frontier R).ncard ≤
      (m * (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι) * (⌈c⌉₊ + 1) ^ (Fintype.card ι - 1) := by
    have hfin : ∀ j : Fin m, (index 1 '' ((fun y ↦ (-w) + c • φ j y) '' Set.Icc 0 1)).Finite := by
      intro j
      refine setFinite_index_image_of_isBounded 1 ?_
      have hb : Bornology.IsBounded (φ j '' Set.Icc 0 1) :=
        (hφ j).isBounded_image (Metric.isBounded_Icc 0 1)
      rw [← hchart_eq j]
      exact ((hb.smul₀ c).vadd (-w))
    have hsub : index 1 '' frontier R ⊆
        ⋃ j, index 1 '' ((fun y ↦ (-w) + c • φ j y) '' Set.Icc 0 1) := by
      rw [← Set.image_iUnion]
      exact Set.image_mono hfrontR
    refine (Set.ncard_le_ncard hsub (Set.finite_iUnion hfin)).trans ?_
    refine (Set.ncard_iUnion_le_of_fintype _).trans ?_
    refine (Finset.sum_le_sum fun j _ ↦ ncard_index1_image_smul_chart_le (hφ j) hc (-w)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring_nf
    rfl
  -- Combine: bridge + boundary bound, then convert `⌈c⌉₊ + 1 ≤ 3c` to land on `cᵈ⁻¹`.
  rw [mul_comm (c ^ Fintype.card ι) (volume.real s)] at hbridge
  refine hbridge.trans ((Nat.cast_le.mpr hbdcell).trans ?_)
  push_cast
  have hpow : ((⌈c⌉₊ : ℝ) + 1) ^ (Fintype.card ι - 1) ≤
      3 ^ (Fintype.card ι - 1) * c ^ (Fintype.card ι - 1) := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have h1 : (⌈c⌉₊ : ℝ) < c + 1 := Nat.ceil_lt_add_one hcpos.le
    nlinarith [hc]
  calc (m : ℝ) * (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * ((⌈c⌉₊ : ℝ) + 1) ^ (Fintype.card ι - 1)
      ≤ (m : ℝ) * (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι
          * (3 ^ (Fintype.card ι - 1) * c ^ (Fintype.card ι - 1)) := by
        gcongr
    _ = (m : ℝ) * (2 * ⌈(M : ℝ)⌉₊ + 1) ^ Fintype.card ι * 3 ^ (Fintype.card ι - 1)
          * c ^ (Fintype.card ι - 1) := by ring

end RealScale

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
  classical
  obtain ⟨m, M, φ, hφ, hcov⟩ := hlip
  -- Transport the data through `T.symm`: `D' = T.symm '' D` is bounded, measurable, and its
  -- frontier inherits a Lipschitz cover (compose the charts with the continuous-linear `T.symm`).
  set D' : Set (ι → ℝ) := T.symm '' D with hD'
  set Ts : (ι → ℝ) →L[ℝ] (ι → ℝ) := (T.symm.toContinuousLinearEquiv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    with hTs
  have hTslip : LipschitzWith ‖Ts‖₊ (T.symm : (ι → ℝ) → (ι → ℝ)) := by
    have := Ts.lipschitz; simpa [hTs] using this
  have hD'bdd : Bornology.IsBounded D' := hTslip.isBounded_image hbdd
  have hD'meas : MeasurableSet D' :=
    (T.symm.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv).measurableSet_image.mpr hmeas
  -- Transported Lipschitz cover of `frontier D'`.
  set M' : ℝ≥0 := ‖Ts‖₊ * M with hM'
  set φ' : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ) := fun j ↦ T.symm ∘ φ j with hφ'
  have hφ'lip : ∀ j, LipschitzWith M' (φ' j) := fun j ↦ hTslip.comp (hφ j)
  have hcov' : frontier D' ⊆ ⋃ j, φ' j '' Set.Icc 0 1 := by
    have hfr : frontier D' = T.symm '' frontier D := by
      have h := (T.symm.toContinuousLinearEquiv.toHomeomorph).image_frontier D
      simpa [hD'] using h.symm
    rw [hfr]
    refine (Set.image_mono hcov).trans ?_
    rw [Set.image_iUnion]
    refine Set.iUnion_mono fun j ↦ ?_
    rw [Set.image_image]
    exact le_of_eq rfl
  -- The volume `vol.real D' = vol.real D / |det T|`.
  have hvolD' : MeasureTheory.volume.real D' =
      MeasureTheory.volume.real D / |LinearMap.det (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))| := by
    have hcoe : (⇑T.symm : (ι → ℝ) → (ι → ℝ)) = ⇑(T.symm : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) := rfl
    rw [hD', MeasureTheory.Measure.real, MeasureTheory.Measure.real, hcoe,
      MeasureTheory.Measure.addHaar_image_linearMap,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
    have hdet : LinearMap.det (T.symm : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) =
        (LinearMap.det (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)))⁻¹ := by
      rw [← LinearEquiv.coe_det, ← LinearEquiv.coe_det, LinearEquiv.det_symm]
      simp [Units.val_inv_eq_inv_val]
    rw [hdet, abs_inv, div_eq_mul_inv]
    ring
  -- The uniform constant from the translate-real-scale bridge applied to `D'`.
  refine ⟨(m * (2 * ⌈(M' : ℝ)⌉₊ + 1) ^ Fintype.card ι * 3 ^ (Fintype.card ι - 1) : ℕ), ?_⟩
  intro ξ t ht
  have ht0 : t ≠ 0 := (lt_of_lt_of_le one_pos ht).ne'
  -- Count identity: linear transport + scaling reduces to the translated-lattice count of `D'`.
  have hcount : Nat.card ↑((ξ +ᵥ (T '' (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ))))
        ∩ t • D)
      = Nat.card ↑(D' ∩ t⁻¹ • ((T.symm ξ) +ᵥ
          (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)))) := by
    have hinj : Function.Injective (T.symm : (ι → ℝ) → (ι → ℝ)) := T.symm.injective
    rw [← Nat.card_image_of_injective hinj, Set.image_inter hinj]
    have h1 : T.symm '' (ξ +ᵥ (T '' (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ))))
        = (T.symm ξ) +ᵥ (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)) := by
      rw [show (ξ +ᵥ (T '' (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ))))
            = (fun x ↦ ξ + x) '' (T '' (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)))
          from rfl, Set.image_image, Set.image_image,
        show ((T.symm ξ) +ᵥ (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)))
            = (fun z ↦ T.symm ξ + z) '' (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ))
          from rfl]
      apply Set.image_congr'
      intro z
      simp only [map_add, LinearEquiv.symm_apply_apply]
    have h2 : T.symm '' (t • D) = t • D' := by
      rw [hD']
      ext z
      simp only [Set.mem_image, Set.mem_smul_set]
      constructor
      · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨T.symm y, ⟨y, hy, rfl⟩, by rw [map_smul]⟩
      · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨t • y, ⟨y, hy, rfl⟩, by rw [map_smul]⟩
    rw [h1, h2, Set.inter_comm]
    have hbij : ↑(D' ∩ t⁻¹ • ((T.symm ξ) +ᵥ
          (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)))) ≃
        ↑(t • D' ∩ ((T.symm ξ) +ᵥ (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)))) :=
      Equiv.subtypeEquiv (Equiv.smulRight ht0) (fun x ↦ by
        simp_rw [Set.mem_inter_iff, Equiv.smulRight_apply, Set.smul_mem_smul_set_iff₀ ht0,
          ← Set.mem_inv_smul_set_iff₀ ht0])
    rw [Nat.card_congr hbij]
  rw [hcount, ← hvolD']
  exact abs_cardR_translate_sub_volume_le hD'bdd hD'meas hφ'lip hcov' (T.symm ξ) ht

/-! ### Arithmetic input: the integer norm is constant modulo `M` on cosets of `M · 𝓞_K` -/

/-- **Norm is coset-constant modulo `M`.** For `x y : 𝓞 K` and `M : ℕ`, the algebraic norm
satisfies `Algebra.norm ℤ (x + M·y) ≡ Algebra.norm ℤ x (mod M)`. Proof: the norm is the
determinant of the left-multiplication matrix in a fixed `ℤ`-basis; reducing the matrix entries
mod `M` kills the `M·(leftMulMatrix y)` summand (the determinant commutes with the reduction ring
hom), so the two determinants agree in `ZMod M`. -/
private theorem natCast_algebraNorm_add_nsmul_mul {K : Type*} [Field K] [NumberField K]
    (M : ℕ) (x y : 𝓞 K) :
    ((Algebra.norm ℤ (x + (M : 𝓞 K) * y) : ℤ) : ZMod M) = ((Algebra.norm ℤ x : ℤ) : ZMod M) := by
  classical
  let b := Module.Free.chooseBasis ℤ (𝓞 K)
  have hN : ∀ z : 𝓞 K, (Algebra.norm ℤ z : ℤ) = (Algebra.leftMulMatrix b z).det :=
    fun z ↦ Algebra.norm_eq_matrix_det b z
  rw [hN, hN]
  rw [show ((Algebra.leftMulMatrix b (x + (M : 𝓞 K) * y)).det : ZMod M) =
      (((Int.castRingHom (ZMod M)).mapMatrix
        (Algebra.leftMulMatrix b (x + (M : 𝓞 K) * y))).det) by rw [← RingHom.map_det]; rfl]
  rw [show ((Algebra.leftMulMatrix b x).det : ZMod M) =
      (((Int.castRingHom (ZMod M)).mapMatrix (Algebra.leftMulMatrix b x)).det) by
        rw [← RingHom.map_det]; rfl]
  congr 1
  have hMy : (M : 𝓞 K) * y = M • y := by rw [nsmul_eq_mul]
  rw [hMy, map_add, map_nsmul]
  ext i j
  simp only [Matrix.add_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply,
    eq_intCast, Int.cast_add]
  rw [show (((M • (Algebra.leftMulMatrix b) y i j) : ℤ) : ZMod M) = 0 by
    rw [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]]
  rw [add_zero]

/-! ### Sign of the algebraic norm via the real embeddings -/

open Classical NumberField.InfinitePlace in
/-- **Signed product formula for the rational norm.** For `y : K`,
`Algebra.norm ℚ y = (∏_{w real} σ_w y) · (∏_{w complex} ‖σ_w y‖²)`, where `σ_w` is the embedding
attached to the place `w` (real-valued for a real place). The complex factor is nonnegative, so
the **sign** of the norm is the product of the signs of the real embeddings — the input to the
sign-orthant decomposition. Proof: group `Algebra.norm_eq_prod_embeddings` over the fibres of
`InfinitePlace.mk`; a real place contributes its single real embedding, a complex place its
conjugate pair `σ · conj σ = ‖σ‖²`. -/
private theorem norm_eq_prod_real_emb_mul_prod_complex {K : Type*} [Field K] [NumberField K]
    (y : K) :
    ((Algebra.norm ℚ y : ℝ)) =
      (∏ w : {w : InfinitePlace K // IsReal w}, embedding_of_isReal w.2 y) *
        (∏ w : {w : InfinitePlace K // IsComplex w}, ‖(w.1.embedding) y‖ ^ 2) := by
  classical
  have hcc : ((Algebra.norm ℚ y : ℝ) : ℂ) =
      ((∏ w : {w : InfinitePlace K // IsReal w}, embedding_of_isReal w.2 y : ℝ) : ℂ) *
        ((∏ w : {w : InfinitePlace K // IsComplex w}, ‖(w.1.embedding) y‖ ^ 2 : ℝ) : ℂ) := by
    have hperplace : ∀ w : InfinitePlace K,
        ∏ ψ ∈ Finset.univ.filter (fun ψ : K →+* ℂ => mk ψ = w), ψ y =
          if hw : IsReal w then ((embedding_of_isReal hw y : ℝ) : ℂ)
          else (‖(embedding w) y‖ ^ 2 : ℝ) := by
      intro w
      have hfilter : Finset.univ.filter (fun ψ : K →+* ℂ => mk ψ = w)
          = {embedding w, ComplexEmbedding.conjugate (embedding w)} := by
        ext ψ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        conv_lhs => rw [← mk_embedding w, mk_eq_iff, ComplexEmbedding.conjugate,
          star_involutive.eq_iff]
      rw [hfilter]
      by_cases hw : IsReal w
      · rw [dif_pos hw, ComplexEmbedding.isReal_iff.mp (isReal_iff.mp hw),
          Finset.insert_eq_self.mpr (Finset.mem_singleton_self _), Finset.prod_singleton,
          embedding_of_isReal_apply hw]
      · rw [dif_neg hw, Finset.prod_pair]
        · rw [ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj]
          norm_cast
          rw [Complex.normSq_eq_norm_sq]
        · rw [Ne, eq_comm, ← ComplexEmbedding.isReal_iff, ← isReal_iff]; exact hw
    have hemb : (algebraMap ℚ ℂ) (Algebra.norm ℚ y) = ∏ ψ : K →+* ℂ, ψ y := by
      rw [Algebra.norm_eq_prod_embeddings ℚ ℂ y]
      exact (Fintype.prod_equiv RingHom.equivRatAlgHom (fun ψ : K →+* ℂ => ψ y)
        (fun σ : K →ₐ[ℚ] ℂ => σ y) (fun ψ => by simp [RingHom.equivRatAlgHom_apply])).symm
    rw [show ((Algebra.norm ℚ y : ℝ) : ℂ) = (algebraMap ℚ ℂ) (Algebra.norm ℚ y) by
        rw [eq_ratCast (algebraMap ℚ ℂ), Complex.ofReal_ratCast], hemb,
      ← Finset.prod_fiberwise (g := fun ψ : K →+* ℂ => mk ψ) (f := fun ψ => ψ y) Finset.univ]
    simp_rw [hperplace]
    rw [prod_eq_prod_mul_prod]
    congr 1
    · rw [Finset.prod_congr rfl (fun w _ => by rw [dif_pos w.2]), Complex.ofReal_prod]
    · rw [Finset.prod_congr rfl (fun w _ => by rw [dif_neg (not_isReal_iff_isComplex.mpr w.2)]),
        Complex.ofReal_prod]
  exact_mod_cast hcc

/-- **Sign of a product of reals from a sign pattern.** If `f w < 0` exactly for `w ∈ s` and
`f w > 0` otherwise, then `∏ w, f w = (-1)^{#s} · ∏ w, |f w|`. -/
private theorem prod_eq_neg_one_pow_card_mul_prod_abs {ι : Type*} [Fintype ι] (s : Finset ι)
    (f : ι → ℝ) (hpos : ∀ w ∉ s, 0 < f w) (hneg : ∀ w ∈ s, f w < 0) :
    (∏ w, f w) = (-1) ^ (s.card) * (∏ w, |f w|) := by
  classical
  rw [← Finset.prod_mul_prod_compl s (fun w => |f w|),
    show ((-1 : ℝ)) ^ s.card = ∏ w ∈ s, (-1 : ℝ) by rw [Finset.prod_const],
    ← Finset.prod_mul_prod_compl s f, ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  · exact Finset.prod_congr rfl (fun w hw => by rw [neg_one_mul, abs_of_neg (hneg w hw), neg_neg])
  · exact Finset.prod_congr rfl (fun w hw => (abs_of_pos (hpos w (Finset.mem_compl.mp hw))).symm)

open Classical NumberField.InfinitePlace NumberField.mixedEmbedding in
/-- **Sign of the integer norm on a sign-orthant.** If the real coordinates of
`mixedEmbedding K y` are negative exactly on `s` (and positive off `s`), then
`(Algebra.norm ℤ y).natAbs = (-1)^{#s} · Algebra.norm ℤ y` in `ℤ`. This makes the *absolute*
norm residue equal to a coset-constant (signed) residue on each orthant. -/
private theorem natAbs_norm_eq_neg_one_pow_mul_norm {K : Type*} [Field K] [NumberField K]
    (y : 𝓞 K) (s : Finset {w : InfinitePlace K // IsReal w})
    (hneg : ∀ w ∈ s, (mixedEmbedding K (y : K)).1 w < 0)
    (hpos : ∀ w ∉ s, 0 < (mixedEmbedding K (y : K)).1 w) :
    ((Algebra.norm ℤ y).natAbs : ℤ) = (-1) ^ (s.card) * (Algebra.norm ℤ y : ℤ) := by
  classical
  have hcoe : ((Algebra.norm ℤ y : ℤ) : ℝ) = Algebra.norm ℚ (y : K) := by
    rw [← Algebra.coe_norm_int]; push_cast; ring
  have hcpx : 0 ≤
      (∏ w : {w : InfinitePlace K // IsComplex w}, ‖(w.1.embedding) (y : K)‖ ^ 2) :=
    Finset.prod_nonneg (fun w _ => sq_nonneg _)
  -- The sign hypotheses, phrased on the real embeddings (which equal the mixed coordinates).
  have hmix : ∀ w : {w : InfinitePlace K // IsReal w},
      embedding_of_isReal w.2 (y : K) = (mixedEmbedding K (y : K)).1 w := fun w => by
    rw [mixedEmbedding_apply_isReal]
  have hneg' : ∀ w ∈ s, embedding_of_isReal w.2 (y : K) < 0 := fun w hw => by
    rw [hmix]; exact hneg w hw
  have hpos' : ∀ w ∉ s, 0 < embedding_of_isReal w.2 (y : K) := fun w hw => by
    rw [hmix]; exact hpos w hw
  have hsign := prod_eq_neg_one_pow_card_mul_prod_abs s
    (fun w : {w : InfinitePlace K // IsReal w} => embedding_of_isReal w.2 (y : K)) hpos' hneg'
  have hnf := norm_eq_prod_real_emb_mul_prod_complex (K := K) (y : K)
  -- `|↑norm| = (∏|real emb|)·(∏complex)`, since the complex factor is nonnegative.
  have habs : |((Algebra.norm ℚ (y : K) : ℝ))|
      = (∏ w : {w : InfinitePlace K // IsReal w}, |embedding_of_isReal w.2 (y : K)|) *
        (∏ w : {w : InfinitePlace K // IsComplex w}, ‖(w.1.embedding) (y : K)‖ ^ 2) := by
    rw [hnf, abs_mul, abs_of_nonneg hcpx, Finset.abs_prod]
  -- Real-number identity: `(↑norm : ℝ) = (-1)^#s · |↑norm|`.
  have hkeyR : ((Algebra.norm ℚ (y : K) : ℝ))
      = (-1) ^ (s.card) * |((Algebra.norm ℚ (y : K) : ℝ))| := by
    rw [habs]
    conv_lhs => rw [hnf, hsign]
    ring
  -- Transfer to `ℤ` via the cast: `norm = (-1)^#s · natAbs`.
  have hZ' : (Algebra.norm ℤ y : ℤ) = (-1) ^ (s.card) * ((Algebra.norm ℤ y).natAbs : ℤ) := by
    have hZ : ((Algebra.norm ℤ y : ℤ) : ℝ)
        = ((-1) ^ (s.card) * ((Algebra.norm ℤ y).natAbs : ℤ) : ℤ) := by
      push_cast
      rw [hcoe]
      exact hkeyR
    exact_mod_cast hZ
  -- Invert using `((-1)^#s)² = 1`.
  have hsq : ((-1 : ℤ)) ^ s.card * (-1) ^ s.card = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  calc ((Algebra.norm ℤ y).natAbs : ℤ)
      = 1 * ((Algebra.norm ℤ y).natAbs : ℤ) := (one_mul _).symm
    _ = ((-1) ^ s.card * (-1) ^ s.card) * ((Algebra.norm ℤ y).natAbs : ℤ) := by rw [hsq]
    _ = (-1) ^ s.card * ((-1) ^ s.card * ((Algebra.norm ℤ y).natAbs : ℤ)) := by ring
    _ = (-1) ^ s.card * (Algebra.norm ℤ y : ℤ) := by rw [← hZ']

/-! ### Splitting the count by ideal class -/

open Ideal in
/-- **Class split of the residue count.** The number of nonzero integral ideals of norm `≤ N`
with norm residue `a (mod c)` is the sum over the (finite) class group of the per-class counts.
The class group is a `Fintype`; finiteness of each fibre follows from
`Ideal.finite_setOf_absNorm_le₀`. -/
private theorem card_norm_le_residue_eq_sum_class {K : Type*} [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (a : ZMod c) (N : ℕ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a}
    = ∑ C : ClassGroup (𝓞 K),
        Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C} := by
  classical
  have hbase : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N} :=
    Ideal.finite_setOf_absNorm_le₀ N
  have hfin : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a} :=
    Finite.of_injective (fun I => (⟨I.1, I.2.1⟩ :
      {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N}))
      (fun x y h => Subtype.ext (by simpa using h))
  have hfinC : ∀ C : ClassGroup (𝓞 K), Finite {I : (Ideal (𝓞 K))⁰ //
      (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C} := fun C =>
    Finite.of_injective (fun I => (⟨I.1, I.2.1.1⟩ :
      {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N}))
      (fun x y h => Subtype.ext (by simpa using h))
  have hF : Fintype {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a} := Fintype.ofFinite _
  have hFC : ∀ C, Fintype {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C} :=
    fun C => Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,
    Finset.sum_congr rfl (fun C _ => Nat.card_eq_fintype_card (α := {I : (Ideal (𝓞 K))⁰ //
      (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C})),
    ← Fintype.card_sigma]
  refine Fintype.card_congr ((Equiv.sigmaFiberEquiv (fun I :
    {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
      ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a} => ClassGroup.mk0 I.1)).symm.trans ?_)
  refine Equiv.sigmaCongrRight (fun C => ?_)
  exact {
    toFun := fun I => ⟨I.1.1, I.1.2, I.2⟩
    invFun := fun I => ⟨⟨I.1, I.2.1⟩, I.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-! ### Principalization: reducing a class to `J`-divisible principal ideals -/

/-- **Modular cancellation.** `m ≡ a (mod c)` iff `m·NJ ≡ a·NJ (mod c·NJ)` (for `NJ > 0`).
This transports the norm residue through the principalization map `I ↦ J · I`, under which the
norm is multiplied by `N(J)`. -/
private theorem natCast_eq_iff_mul_natCast_eq (cc NJ m a : ℕ) (hNJ : 0 < NJ) :
    ((m : ZMod cc) = (a : ZMod cc)) ↔
      (((m * NJ : ℕ) : ZMod (cc * NJ)) = ((a * NJ : ℕ) : ZMod (cc * NJ))) := by
  rw [ZMod.natCast_eq_natCast_iff, ZMod.natCast_eq_natCast_iff, Nat.ModEq, Nat.ModEq,
    Nat.mul_mod_mul_right, Nat.mul_mod_mul_right]
  exact ⟨fun h => by rw [h], fun h => Nat.eq_of_mul_eq_mul_right hNJ h⟩

open Ideal Submodule in
/-- **Principalization correspondence (per ideal).** Under `I ↦ J · I` (`Equiv.dvd J`, with
`ClassGroup.mk0 J = C⁻¹`), the predicate "`I` has norm `≤ N`, residue `a (mod c)`, and class `C`"
corresponds to "`J · I` is principal, has norm `≤ N·N(J)`, and residue `a·N(J) (mod c·N(J))`":
`mk0 I = C ↔ IsPrincipal (J·I)` (since `mk0 (J·I) = C⁻¹·mk0 I`), the norm scales by `N(J)`, and
the residue transports by `natCast_eq_iff_mul_natCast_eq`. -/
private theorem principalize_iff {K : Type*} [Field K] [NumberField K] (c : ℕ) [NeZero c]
    (a : ZMod c) (N : ℕ) (C : ClassGroup (𝓞 K)) (J I : (Ideal (𝓞 K))⁰)
    (hJ : ClassGroup.mk0 J = C⁻¹) (hNJ : 0 < Ideal.absNorm (J : Ideal (𝓞 K))) :
    ((Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C) ↔
      (IsPrincipal (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ∧
        Ideal.absNorm (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ≤
          N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
        ((Ideal.absNorm (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) :
            ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K)))) =
          ((a.val * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
            ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K)))))) := by
  classical
  have hnorm : absNorm (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
      = absNorm (I : Ideal (𝓞 K)) * absNorm (J : Ideal (𝓞 K)) := by
    simp_rw [Equiv.dvd_apply, Submonoid.coe_mul, _root_.map_mul]; ring
  have hprin : IsPrincipal (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ↔
      ClassGroup.mk0 I = C := by
    have hmem : (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰ :=
      SetLike.coe_mem _
    rw [← ClassGroup.mk0_eq_one_iff hmem]
    have hmk : ClassGroup.mk0 (⟨(((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)), hmem⟩ :
        (Ideal (𝓞 K))⁰) = ClassGroup.mk0 ((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) := by congr 1
    rw [hmk, Equiv.dvd_apply, map_mul, hJ, inv_mul_eq_one, eq_comm]
  rw [hprin, hnorm]
  have hres : (((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ↔
      (((Ideal.absNorm (I : Ideal (𝓞 K)) * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
          ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K)))) =
        ((a.val * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
          ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K))))) := by
    rw [show ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a ↔
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = ((a.val : ℕ) : ZMod c) by
      rw [ZMod.natCast_val, ZMod.cast_id]]
    exact natCast_eq_iff_mul_natCast_eq c (absNorm (J : Ideal (𝓞 K)))
      (absNorm (I : Ideal (𝓞 K))) a.val hNJ
  have hnle : (absNorm (I : Ideal (𝓞 K)) * absNorm (J : Ideal (𝓞 K)) ≤
      N * absNorm (J : Ideal (𝓞 K))) ↔ (absNorm (I : Ideal (𝓞 K)) ≤ N) :=
    Nat.mul_le_mul_right_iff hNJ
  rw [hnle, ← hres]
  tauto

open Ideal Submodule in
/-- **Principalization (`Nat.card` level).** With `ClassGroup.mk0 J = C⁻¹`, the count of class-`C`
ideals of norm `≤ N` and residue `a (mod c)` equals the count of `J`-divisible principal ideals
of norm `≤ N·N(J)` and residue `a·N(J) (mod c·N(J))`. The bijection is `I ↦ J · I`
(`Equiv.dvd J`); the predicate correspondence is `principalize_iff`. -/
private theorem card_principalize {K : Type*} [Field K] [NumberField K] (c : ℕ) [NeZero c]
    (a : ZMod c) (N : ℕ) (C : ClassGroup (𝓞 K)) (J : (Ideal (𝓞 K))⁰)
    (hJ : ClassGroup.mk0 J = C⁻¹) (hNJ : 0 < Ideal.absNorm (J : Ideal (𝓞 K))) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C}
    = Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K)) ∧
        (IsPrincipal (I : Ideal (𝓞 K)) ∧
        Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K)))) =
          ((a.val * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
            ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K))))))} := by
  classical
  simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
  exact Nat.card_congr
    (((Equiv.dvd J).subtypeEquiv (fun I => principalize_iff c a N C J I hJ hNJ)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ ↦ J ∣ I) _))

/-! ### Geometric infrastructure: linear-equiv transport and the residue-decorated torsion bridge

The geometric core transports the cone-point count to the standard coordinate space `index K → ℝ`
(the ambient of the workhorse `exists_card_coset_inter_smul_sub_volume_mul_rpow_le`) via the chart
`Φ = (stdBasis K).equivFunL`. `map_span_int_linearEquiv` carries `ℤ`-spans through `Φ` (so the
ideal lattice becomes `T '' ℤ^ι`); `card_isPrincipal_dvd_norm_le_residue` is mathlib's
`card_isPrincipal_dvd_norm_le` refined by a norm-residue condition (carried along the per-norm
fibre equivalence `idealSetEquivNorm`). -/

/-- **`ℤ`-span transport along an `ℝ`-linear equivalence.** For an `ℝ`-linear equivalence `f` and a
set `S`, the image of the `ℤ`-span of `S` is the `ℤ`-span of the image (as sets). -/
private theorem map_span_int_linearEquiv {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (f : E ≃ₗ[ℝ] F) (S : Set E) :
    f '' (span ℤ S : Set E) = (span ℤ (f '' S) : Set F) := by
  have key : (span ℤ ((f.restrictScalars ℤ) '' S) : Submodule ℤ F)
      = (span ℤ S).map (f.restrictScalars ℤ).toLinearMap := (Submodule.map_span _ S).symm
  have himg : (f '' (span ℤ S : Set E))
      = ((span ℤ S).map (f.restrictScalars ℤ).toLinearMap : Set F) := by
    rw [Submodule.map_coe]; rfl
  rw [himg, ← key]; rfl

open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone in
/-- **Homogeneity of the norm-bounded cone region.** For `t ≥ 1`, the slice of the fundamental
cone of mixed norm `≤ t ^ d` (`d = [K:ℚ]`) is the real dilation `t • normLeOne K`: scaling by `t`
preserves the cone (`smul_mem_iff_mem`) and multiplies the norm by `t ^ d`
(`mixedEmbedding.norm_smul`, `|t| = t`). -/
private theorem cone_normLe_eq_smul_normLeOne {K : Type*} [Field K] [NumberField K] {t : ℝ}
    (ht : 1 ≤ t) :
    {x : mixedSpace K | x ∈ fundamentalCone K ∧
        mixedEmbedding.norm x ≤ t ^ (Module.finrank ℚ K)} = t • normLeOne K := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have htne : t ≠ 0 := ht0.ne'
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_smul_set, normLeOne, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hcone, hnorm⟩
    refine ⟨t⁻¹ • x, ⟨(smul_mem_iff_mem (inv_ne_zero htne)).mpr hcone, ?_⟩, ?_⟩
    · rw [mixedEmbedding.norm_smul, abs_of_pos (inv_pos.mpr ht0), inv_pow,
        inv_mul_le_one₀ (by positivity)]
      exact hnorm
    · rw [smul_smul, mul_inv_cancel₀ htne, one_smul]
  · rintro ⟨y, ⟨hcone, hnorm⟩, rfl⟩
    refine ⟨(smul_mem_iff_mem htne).mpr hcone, ?_⟩
    rw [mixedEmbedding.norm_smul, abs_of_pos ht0]
    calc t ^ (Module.finrank ℚ K) * mixedEmbedding.norm y
        ≤ t ^ (Module.finrank ℚ K) * 1 :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = t ^ (Module.finrank ℚ K) := mul_one _

open NumberField.mixedEmbedding in
/-- **The ideal lattice is a full lattice in the standard chart.** Transporting
`idealLattice K (mk0 K J)` along the chart `Φ = (stdBasis K).equivFunL : mixedSpace K ≃ index K → ℝ`
turns it into `T '' ℤ^(index K)` for an explicit `ℝ`-linear automorphism `T`: take the basis `c`
formed by `Φ` applied to the `ℝ`-basis `fractionalIdealLatticeBasis` (reindexed to `index K`, whose
cardinality matches by `fractionalIdeal_rank`/`finrank`), and let `T` send the standard basis to
`c` (`Basis.equiv`). Then `T '' ℤ^ι = span ℤ (range c) = Φ '' (span ℤ idealLatticeBasis)`
(`map_span_int_linearEquiv`, `span_idealLatticeBasis`). -/
private theorem exists_latticeEquiv_image_idealLattice {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) :
    ∃ T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ),
      T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)) := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  set I := FractionalIdeal.mk0 K J with hI
  have e : Module.Free.ChooseBasisIndex ℤ I ≃ index K := by
    apply Fintype.equivOfCardEq
    rw [← Module.finrank_eq_card_chooseBasisIndex, NumberField.fractionalIdeal_rank,
      RingOfIntegers.rank, ← Module.finrank_eq_card_basis (mixedEmbedding.stdBasis K),
      mixedEmbedding.finrank]
  set c : Module.Basis (index K) ℝ (index K → ℝ) :=
    ((mixedEmbedding.fractionalIdealLatticeBasis K I).map Φ.toLinearEquiv).reindex e with hc
  refine ⟨(Pi.basisFun ℝ (index K)).equiv c (Equiv.refl (index K)), ?_⟩
  have hcrange : Set.range c
      = Φ '' (Set.range (mixedEmbedding.fractionalIdealLatticeBasis K I)) := by
    rw [hc, Module.Basis.range_reindex, ← Set.range_comp]; rfl
  rw [map_span_int_linearEquiv]
  have hrange : ((Pi.basisFun ℝ (index K)).equiv c (Equiv.refl (index K)))
      '' (Set.range (Pi.basisFun ℝ (index K))) = Set.range c := by
    rw [← Set.range_comp]
    congr 1; ext i
    simp only [Function.comp_apply, Module.Basis.equiv_apply, Equiv.refl_apply]
  rw [hrange, hcrange, ← mixedEmbedding.span_idealLatticeBasis K I]
  exact (map_span_int_linearEquiv Φ.toLinearEquiv _).symm

/-- **Bounded coordinate-hyperplane pieces are Lipschitz cube-coverable.** For a coordinate `j` and
radius `R ≥ 0`, the slab `{x : x j = 0, ∀ i, |x i| ≤ R}` of the hyperplane `{x j = 0}` in `ι → ℝ`
is contained in a single Lipschitz image of the unit cube `[0,1]^(card ι - 1)` (constant `2R`):
parametrise the `card ι - 1` free coordinates affinely by `c ↦ 2R·c - R` (a bijection
`Fin (card ι - 1) ≃ {i // i ≠ j}` supplies the indices) and set coordinate `j` to `0`. This is the
boundary contribution of an orthant cut, feeding the workhorse's frontier-cover hypothesis. -/
private theorem exists_lipschitz_cube_cover_hyperplane_slab {ι : Type*} [Fintype ι]
    (j : ι) {R : ℝ} (hR : 0 ≤ R) :
    ∃ (M : ℝ≥0) (φ : (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      LipschitzWith M φ ∧
        {x : ι → ℝ | x j = 0 ∧ ∀ i, |x i| ≤ R} ⊆ φ '' Set.Icc 0 1 := by
  classical
  have hcard : Fintype.card {i : ι // i ≠ j} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl]; simp
  set σ : Fin (Fintype.card ι - 1) ≃ {i : ι // i ≠ j} :=
    (Fintype.equivFinOfCardEq hcard).symm with hσ
  set φ : (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ) :=
    fun c i => if h : i = j then 0 else (2 * R) * c (σ.symm ⟨i, h⟩) - R with hφ
  refine ⟨(2 * R).toNNReal, φ, ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun c c' => ?_
    rw [dist_pi_le_iff (by positivity)]
    intro i
    by_cases hij : i = j
    · simp only [hφ, dif_pos hij, dist_self]; positivity
    · simp only [hφ, dif_neg hij]
      rw [Real.dist_eq, show (2 * R) * c (σ.symm ⟨i, hij⟩) - R - ((2 * R) * c' (σ.symm ⟨i, hij⟩) - R)
            = (2 * R) * (c (σ.symm ⟨i, hij⟩) - c' (σ.symm ⟨i, hij⟩)) by ring,
        abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * R),
        Real.coe_toNNReal _ (by positivity)]
      gcongr
      rw [← Real.dist_eq]
      exact dist_le_pi_dist c c' (σ.symm ⟨i, hij⟩)
  · rintro x ⟨hxj, hxbd⟩
    rcases eq_or_lt_of_le hR with hR0 | hR0
    · have hx0 : x = 0 := by
        ext i; have := hxbd i; rw [← hR0] at this; exact abs_nonpos_iff.mp this
      refine ⟨0, ⟨le_refl _, zero_le_one⟩, ?_⟩
      ext i; simp only [hφ]
      by_cases hij : i = j
      · rw [dif_pos hij, hx0]; rfl
      · rw [dif_neg hij, hx0]; simp [← hR0]
    · refine ⟨fun k => (x (σ k) + R) / (2 * R), ⟨?_, ?_⟩, ?_⟩
      · intro k; simp only [Pi.zero_apply]
        rw [le_div_iff₀ (by positivity)]; have := (abs_le.mp (hxbd (σ k))).1; linarith
      · intro k; simp only [Pi.one_apply]
        rw [div_le_one (by positivity)]; have := (abs_le.mp (hxbd (σ k))).2; linarith
      · ext i
        by_cases hij : i = j
        · rw [hφ]; simp only; rw [dif_pos hij, hij]; exact hxj.symm
        · rw [hφ]; simp only [dif_neg hij, Equiv.apply_symm_apply]; field_simp; ring

open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone in
/-- **Coset translate of cone points translates the generator by `m · J`.** If two cone points
`a₁, a₂ ∈ idealSet K J` differ by a vector of `m • (idealLattice K (mk0 K J))` (the `m`-sublattice),
then their generators differ by `m · w` for some `w ∈ J`: a lattice vector is `mixedEmbedding K y`
with `y ∈ J` (integral, as `mk0 K J = ↑J`), and `mixedEmbedding` is injective, so the integral
preimages satisfy `gen₁ = gen₂ + m·w`. This is the `ℤ`-linearity that makes the norm residue
coset-constant (via `natCast_algebraNorm_add_nsmul_mul`). -/
private theorem exists_generator_diff_of_coset {K : Type*} [Field K] [NumberField K] (m : ℕ)
    (J : (Ideal (𝓞 K))⁰) (a₁ a₂ : idealSet K J)
    (hcoset : (a₁ : mixedSpace K) - (a₂ : mixedSpace K) ∈
      (m : ℝ) • (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) : Set (mixedSpace K))) :
    ∃ w : 𝓞 K, (w : 𝓞 K) ∈ (J : Set (𝓞 K)) ∧
      (preimageOfMemIntegerSet (idealSetMap K J a₁) : 𝓞 K) =
        (preimageOfMemIntegerSet (idealSetMap K J a₂) : 𝓞 K) + (m : 𝓞 K) * w := by
  obtain ⟨v, hv, hveq⟩ := hcoset
  simp only at hveq
  rw [SetLike.mem_coe, mem_idealLattice] at hv
  obtain ⟨y, hy, hyeq⟩ := hv
  simp only [FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal] at hy
  obtain ⟨w, hwJ, hweq⟩ := hy
  rw [Algebra.linearMap_apply] at hweq
  refine ⟨w, hwJ, ?_⟩
  have hg1 : mixedEmbedding K ((preimageOfMemIntegerSet (idealSetMap K J a₁) : 𝓞 K) : K)
      = (a₁ : mixedSpace K) := by rw [mixedEmbedding_preimageOfMemIntegerSet, idealSetMap_apply]
  have hg2 : mixedEmbedding K ((preimageOfMemIntegerSet (idealSetMap K J a₂) : 𝓞 K) : K)
      = (a₂ : mixedSpace K) := by rw [mixedEmbedding_preimageOfMemIntegerSet, idealSetMap_apply]
  have hkey : mixedEmbedding K (((preimageOfMemIntegerSet (idealSetMap K J a₁) : 𝓞 K)
      - (preimageOfMemIntegerSet (idealSetMap K J a₂) : 𝓞 K) : 𝓞 K) : K)
      = mixedEmbedding K ((m : 𝓞 K) * w : 𝓞 K) := by
    push_cast
    rw [map_sub, hg1, hg2, ← hveq, ← hyeq, ← hweq, Nat.cast_smul_eq_nsmul, ← map_nsmul]
    congr 1
    rw [nsmul_eq_mul]
  have heq := RingOfIntegers.coe_injective (K := K) ((mixedEmbedding_injective K) hkey)
  linear_combination heq

/-! ### Lipschitz-cover combinators and orthant boundary for the per-piece workhorse -/

/-- **Union of two Lipschitz cube covers.** If `A` and `B` are each covered by finitely many
`Lipschitz`-images of `[0,1]^(card ι - 1)`, so is `A ∪ B` (concatenate the families, take the max
constant). -/
private theorem exists_lipschitz_cover_union {ι : Type*} [Fintype ι] (A B : Set (ι → ℝ))
    (h1 : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ A ⊆ ⋃ j, φ j '' Set.Icc 0 1)
    (h2 : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ B ⊆ ⋃ j, φ j '' Set.Icc 0 1) :
    ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ (A ∪ B : Set (ι → ℝ)) ⊆ ⋃ j, φ j '' Set.Icc 0 1 := by
  obtain ⟨m1, M1, φ1, hL1, hc1⟩ := h1
  obtain ⟨m2, M2, φ2, hL2, hc2⟩ := h2
  refine ⟨m1 + m2, max M1 M2, fun j => Sum.elim φ1 φ2 (finSumFinEquiv.symm j), ?_, ?_⟩
  · intro j
    simp only
    rcases h : finSumFinEquiv.symm j with k | k
    · rw [Sum.elim_inl]; exact (hL1 k).weaken (le_max_left _ _)
    · rw [Sum.elim_inr]; exact (hL2 k).weaken (le_max_right _ _)
  · refine Set.union_subset ?_ ?_
    · refine hc1.trans (Set.iUnion_subset fun k => ?_)
      refine Set.subset_iUnion_of_subset (finSumFinEquiv (Sum.inl k)) ?_
      simp only [Equiv.symm_apply_apply, Sum.elim_inl, subset_refl]
    · refine hc2.trans (Set.iUnion_subset fun k => ?_)
      refine Set.subset_iUnion_of_subset (finSumFinEquiv (Sum.inr k)) ?_
      simp only [Equiv.symm_apply_apply, Sum.elim_inr, subset_refl]

/-- **Finite union of Lipschitz cube covers.** A `Fintype`-indexed union of sets, each Lipschitz
cube-covered, is itself Lipschitz cube-covered (concatenate over `Σ g, Fin (mf g)`, take the
`Finset.sup` of the constants). -/
private theorem exists_lipschitz_cover_iUnion {ι : Type*} [Fintype ι] {γ : Type*} [Fintype γ]
    (A : γ → Set (ι → ℝ))
    (h : ∀ g, ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ A g ⊆ ⋃ j, φ j '' Set.Icc 0 1) :
    ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ (⋃ g, A g) ⊆ ⋃ j, φ j '' Set.Icc 0 1 := by
  classical
  choose mf Mf φf hLf hcf using h
  set e := Fintype.equivFin (Σ g, Fin (mf g)) with he
  set Ψ : (Σ g, Fin (mf g)) → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ) :=
    fun p => φf p.1 p.2 with hΨ
  refine ⟨Fintype.card (Σ g, Fin (mf g)), Finset.univ.sup Mf, fun j => Ψ (e.symm j), ?_, ?_⟩
  · intro j
    exact (hLf (e.symm j).1 (e.symm j).2).weaken (Finset.le_sup (Finset.mem_univ _))
  · refine Set.iUnion_subset fun g => (hcf g).trans (Set.iUnion_subset fun k => ?_)
    refine Set.subset_iUnion_of_subset (e ⟨g, k⟩) ?_
    simp only [hΨ, Equiv.symm_apply_apply, subset_refl]

/-- **Frontier of a closed sign-orthant cut.** The closed orthant in `ι → ℝ` cutting the coordinates
`g k` (`k ∈ s` forces `≤ 0`, `k ∉ s` forces `≥ 0`) has frontier inside the union of the coordinate
hyperplanes `{y (g k) = 0}`. Proof: the orthant is closed, its strict version is open and contained
in it, so a boundary point lies in the orthant but not its interior, forcing some `y (g k) = 0`. -/
private theorem frontier_signOrthant_subset {ι κ : Type*} [Fintype ι] [Fintype κ] (g : κ → ι)
    (s : Finset κ) :
    frontier ({y : ι → ℝ | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))})
      ⊆ ⋃ k : κ, {y : ι → ℝ | y (g k) = 0} := by
  classical
  set O : Set (ι → ℝ) := {y | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))} with hO
  set Os : Set (ι → ℝ) := {y | (∀ k ∈ s, y (g k) < 0) ∧ (∀ k ∉ s, 0 < y (g k))} with hOs
  have hOclosed : IsClosed O := by
    rw [hO, setOf_and]
    refine IsClosed.inter ?_ ?_
    · have h : {y : ι → ℝ | ∀ k ∈ s, y (g k) ≤ 0} = ⋂ k ∈ s, {y : ι → ℝ | y (g k) ≤ 0} := by
        ext y; simp
      rw [h]
      exact isClosed_biInter (fun k _ => isClosed_le (continuous_apply (g k)) continuous_const)
    · have h : {y : ι → ℝ | ∀ k ∉ s, 0 ≤ y (g k)}
          = ⋂ k ∈ (sᶜ : Finset κ), {y : ι → ℝ | 0 ≤ y (g k)} := by ext y; simp
      rw [h]
      exact isClosed_biInter (fun k _ => isClosed_le continuous_const (continuous_apply (g k)))
  have hOsopen : IsOpen Os := by
    rw [hOs, setOf_and]
    refine IsOpen.inter ?_ ?_
    · have h : {y : ι → ℝ | ∀ k ∈ s, y (g k) < 0} = ⋂ k ∈ s, {y : ι → ℝ | y (g k) < 0} := by
        ext y; simp
      rw [h]
      exact isOpen_biInter_finset (fun k _ => isOpen_lt (continuous_apply (g k)) continuous_const)
    · have h : {y : ι → ℝ | ∀ k ∉ s, 0 < y (g k)}
          = ⋂ k ∈ (sᶜ : Finset κ), {y : ι → ℝ | 0 < y (g k)} := by ext y; simp
      rw [h]
      exact isOpen_biInter_finset (fun k _ => isOpen_lt continuous_const (continuous_apply (g k)))
  have hsub : Os ⊆ O := fun y hy => ⟨fun k hk => (hy.1 k hk).le, fun k hk => (hy.2 k hk).le⟩
  intro y hy
  have hyO : y ∈ O := hOclosed.closure_eq ▸ frontier_subset_closure hy
  have hyni : y ∉ interior O := by
    rw [frontier_eq_closure_inter_closure] at hy
    rw [interior_eq_compl_closure_compl]; exact fun hh => hh hy.2
  by_contra hcon
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hcon
  apply hyni
  exact mem_interior.mpr ⟨Os, hsub, hOsopen,
    ⟨fun k hk => lt_of_le_of_ne (hyO.1 k hk) (hcon k),
     fun k hk => lt_of_le_of_ne (hyO.2 k hk) (Ne.symm (hcon k))⟩⟩

/-- **Lipschitz frontier cover of an orthant-cut region.** If `D₀` is bounded with a Lipschitz cube
cover of its frontier, then `D₀ ∩ orthant` (orthant cutting the coordinates `g k`) also has a
Lipschitz cube-covered frontier: `frontier (D₀ ∩ O) ⊆ frontier D₀ ∪ (closure D₀ ∩ frontier O)`
(`frontier_inter_subset`), the orthant boundary lands in finitely many coordinate hyperplanes
(`frontier_signOrthant_subset`), and each bounded hyperplane slice is cube-covered
(`exists_lipschitz_cube_cover_hyperplane_slab`); combine via the cover combinators. -/
private theorem exists_frontier_cover_inter_orthant {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    (g : κ → ι) (s : Finset κ) (D₀ : Set (ι → ℝ)) (hbdd : Bornology.IsBounded D₀)
    (hcov : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ frontier D₀ ⊆ ⋃ j, φ j '' Set.Icc 0 1) :
    ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧
        frontier (D₀ ∩ {y : ι → ℝ | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))})
          ⊆ ⋃ j, φ j '' Set.Icc 0 1 := by
  classical
  obtain ⟨R, hR0, hRbd⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ closure D₀, ∀ i, |x i| ≤ R := by
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbdd.closure
    refine ⟨max R 0, le_max_right _ _, fun x hx i => ?_⟩
    calc |x i| = ‖x i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x‖ := norm_le_pi_norm x i
      _ ≤ max R 0 := le_max_of_le_left (hR x hx)
  set O : Set (ι → ℝ) := {y | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))} with hO
  have hsub : frontier (D₀ ∩ O)
      ⊆ frontier D₀ ∪ ⋃ k : κ, {x : ι → ℝ | x (g k) = 0 ∧ ∀ i, |x i| ≤ R} := by
    refine (frontier_inter_subset D₀ O).trans (Set.union_subset ?_ ?_)
    · exact Set.inter_subset_left.trans Set.subset_union_left
    · refine fun x hx => Or.inr ?_
      obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp (frontier_signOrthant_subset g s hx.2)
      exact Set.mem_iUnion.mpr ⟨k, hxk, fun i => hRbd x hx.1 i⟩
  obtain ⟨m, M, φ, hL, hc⟩ := exists_lipschitz_cover_union (frontier D₀)
    (⋃ k : κ, {x : ι → ℝ | x (g k) = 0 ∧ ∀ i, |x i| ≤ R}) hcov
    (exists_lipschitz_cover_iUnion (fun k => {x : ι → ℝ | x (g k) = 0 ∧ ∀ i, |x i| ≤ R})
      (fun k => by
        obtain ⟨M, φ, hL, hc⟩ := exists_lipschitz_cube_cover_hyperplane_slab (g k) hR0
        exact ⟨1, M, fun _ => φ, fun _ => hL, hc.trans (Set.subset_iUnion_of_subset 0 subset_rfl)⟩))
  exact ⟨m, M, φ, hL, hsub.trans hc⟩

/-- **Membership in the standard integer lattice ⟺ integer coordinates.** A point of `ι → ℝ` lies in
`span ℤ (range (Pi.basisFun ℝ ι))` iff every coordinate is an integer. -/
private theorem mem_span_int_basisFun_iff {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    v ∈ span ℤ (Set.range (Pi.basisFun ℝ ι)) ↔ ∀ i, ∃ n : ℤ, v i = (n : ℝ) := by
  classical
  constructor
  · intro hv i
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [Pi.basisFun_apply, Pi.single_apply]
      by_cases hij : i = j
      · exact ⟨1, by simp [hij]⟩
      · exact ⟨0, by simp [hij]⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨a, ha⟩ := ihx; obtain ⟨b, hb⟩ := ihy
      exact ⟨a + b, by rw [Pi.add_apply, ha, hb]; push_cast; ring⟩
    | smul c x _ ih =>
      obtain ⟨a, ha⟩ := ih
      exact ⟨c * a, by rw [Pi.smul_apply, ha, zsmul_eq_mul]; push_cast; ring⟩
  · intro h
    choose n hn using h
    have hv : v = ∑ i, (n i) • (Pi.basisFun ℝ ι i) := by
      ext j
      rw [Finset.sum_apply, hn j, Finset.sum_eq_single j]
      · simp [Pi.basisFun_apply]
      · intro b _ hbj; simp [Pi.basisFun_apply, Ne.symm hbj]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [hv]
    exact sum_mem (fun i _ => zsmul_mem (subset_span (Set.mem_range_self i)) _)

open Ideal NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone Units in
set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- **Residue-decorated torsion bridge.** Mathlib's `card_isPrincipal_dvd_norm_le` refined by a
norm-residue condition: the number of `J`-divisible principal ideals of norm `≤ s` whose norm is
`≡ b (mod m)`, times the torsion order, equals the number of cone points `a ∈ idealSet K J` of
norm `≤ s` whose integer norm `intNorm (idealSetEquiv K J a)` is `≡ b (mod m)`. The residue is a
function of the norm value, so it rides along the per-norm fibre equivalence `idealSetEquivNorm`
(fibres where `(i : ZMod m) ≠ b` are empty on both sides). -/
private theorem card_isPrincipal_dvd_norm_le_residue {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (m b : ℕ) (s : ℝ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ Submodule.IsPrincipal
        (I : Ideal (𝓞 K)) ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m))} * torsionOrder K =
        Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ s ∧
          ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))} := by
  obtain hs | hs := le_or_gt 0 s
  · rw [torsionOrder, ← Nat.card_eq_fintype_card, ← Nat.card_prod]
    refine Nat.card_congr <| @Equiv.ofFiberEquiv _ (γ := Finset.Iic ⌊s⌋₊) _
      (fun I ↦ ⟨Ideal.absNorm I.1.val.1, Finset.mem_Iic.mpr (Nat.le_floor I.1.prop.2.2.1)⟩)
      (fun a ↦ ⟨intNorm (idealSetEquiv K J a.1).1, Finset.mem_Iic.mpr
        (Nat.le_floor (by rw [intNorm_idealSetEquiv_apply]; exact a.prop.1))⟩) fun ⟨i, hi⟩ ↦ ?_
    simp_rw [Subtype.mk.injEq]
    have hile : (i : ℝ) ≤ s := (Nat.le_floor_iff hs).mp (Finset.mem_Iic.mp hi)
    by_cases hib : (i : ZMod m) = (b : ZMod m)
    · calc _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ Submodule.IsPrincipal
                (I : Ideal (𝓞 K)) ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧
                ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m))} //
                Ideal.absNorm I.1.1 = i} × torsion K := Equiv.prodSubtypeFstEquivSubtypeProd
          _ ≃ {I : (Ideal (𝓞 K))⁰ // ((J : Ideal (𝓞 K)) ∣ I ∧ Submodule.IsPrincipal
                (I : Ideal (𝓞 K)) ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧
                ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m))) ∧
                Ideal.absNorm I.1 = i} × torsion K :=
              Equiv.prodCongrLeft fun _ ↦ Equiv.subtypeSubtypeEquivSubtypeInter
                (p := fun I : (Ideal (𝓞 K))⁰ => (J : Ideal (𝓞 K)) ∣ I ∧ Submodule.IsPrincipal
                  (I : Ideal (𝓞 K)) ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧
                  ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m)))
                (q := fun I => Ideal.absNorm (I : Ideal (𝓞 K)) = i)
          _ ≃ {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ Submodule.IsPrincipal
                (I : Ideal (𝓞 K)) ∧ Ideal.absNorm (I : Ideal (𝓞 K)) = i} × torsion K :=
              Equiv.prodCongrLeft fun _ ↦ Equiv.subtypeEquivRight fun I ↦ by
                constructor
                · rintro ⟨⟨h1, h2, _, _⟩, h5⟩; exact ⟨h1, h2, h5⟩
                · rintro ⟨h1, h2, h3⟩
                  exact ⟨⟨h1, h2, by rw [h3]; exact hile, by rw [h3]; exact hib⟩, h3⟩
          _ ≃ {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) = i} :=
                (idealSetEquivNorm K J i).symm
          _ ≃ {a : idealSet K J // intNorm (idealSetEquiv K J a).1 = i} := by
                simp_rw [← intNorm_idealSetEquiv_apply, Nat.cast_inj]; rfl
          _ ≃ _ := (Equiv.subtypeSubtypeEquivSubtype (p := fun a : idealSet K J =>
                mixedEmbedding.norm (a : mixedSpace K) ≤ s ∧
                  ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m)))
                (q := fun a => intNorm (idealSetEquiv K J a).1 = i) fun {a} h ↦ by
                rw [← intNorm_idealSetEquiv_apply, h]
                exact ⟨by exact_mod_cast hile, by rw [h] at *; exact hib⟩).symm
    · haveI : IsEmpty {a : {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ s ∧
          ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))} //
          intNorm (idealSetEquiv K J a.1).1 = i} := ⟨fun a ↦ hib (by rw [← a.2]; exact a.1.2.2)⟩
      haveI : IsEmpty {a : ({I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ Submodule.IsPrincipal
          (I : Ideal (𝓞 K)) ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m))} × torsion K) //
          Ideal.absNorm a.1.1.1 = i} := ⟨fun a ↦ hib (by rw [← a.2]; exact a.1.1.2.2.2.2)⟩
      exact Equiv.equivOfIsEmpty _ _
  · haveI : IsEmpty {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ Submodule.IsPrincipal
        (I : Ideal (𝓞 K)) ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m))} :=
      ⟨fun I ↦ absurd I.2.2.2.1 (not_le.mpr (lt_of_lt_of_le hs (Nat.cast_nonneg _)))⟩
    haveI : IsEmpty {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ s ∧
        ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))} :=
      ⟨fun a ↦ absurd a.2.1 (not_le.mpr (lt_of_lt_of_le hs (mixedEmbedding.norm_nonneg _)))⟩
    rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty, zero_mul]

/-! ### The per-(orthant, coset) workhorse wrapper -/

set_option linter.unusedFintypeInType false in
/-- **Per-cell effective count.** Specialisation of the workhorse
`exists_card_coset_inter_smul_sub_volume_mul_rpow_le` to the `m`-sublattice `m • (T '' ℤ^ι)`
(realised as `T' '' ℤ^ι` with `T' = (m • ·) ∘ T`) and the orthant-cut region `D₀ ∩ orthant`
(whose Lipschitz frontier comes from `exists_frontier_cover_inter_orthant`). For any coset
translate `ξ` and any real dilation `t ≥ 1`, the cell count is `κ · t^d + O(t^{d-1})`, with the
constant uniform in `ξ`. -/
private theorem exists_card_cell_sub_mul_rpow_le {ι : Type*} [Fintype ι]
    (T : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (m : ℕ) (hm : (m : ℝ) ≠ 0) (D₀ : Set (ι → ℝ))
    (hbdd : Bornology.IsBounded D₀) (hmeas : MeasurableSet D₀)
    (hlip : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ frontier D₀ ⊆ ⋃ j, φ j '' Set.Icc 0 1)
    {κ : Type*} [Fintype κ] (g : κ → ι) (s : Finset κ) :
    ∃ leadC C : ℝ, ∀ ξ : ι → ℝ, ∀ t : ℝ, 1 ≤ t →
      |(Nat.card ↑((ξ +ᵥ
          (((LinearEquiv.smulOfNeZero ℝ (ι → ℝ) (m : ℝ) hm).trans T) ''
            (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)))) ∩
            t • (D₀ ∩ {y : ι → ℝ | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))})) : ℝ)
          - leadC * t ^ (Fintype.card ι)|
        ≤ C * t ^ (Fintype.card ι - 1 : ℕ) := by
  set T' : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) := (LinearEquiv.smulOfNeZero ℝ (ι → ℝ) (m : ℝ) hm).trans T with hT'
  set Ds : Set (ι → ℝ) :=
    D₀ ∩ {y : ι → ℝ | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))} with hDs
  have hDsbdd : Bornology.IsBounded Ds := hbdd.subset Set.inter_subset_left
  have hOclosed : IsClosed {y : ι → ℝ | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))} := by
    classical
    rw [setOf_and]
    refine IsClosed.inter ?_ ?_
    · have h : {y : ι → ℝ | ∀ k ∈ s, y (g k) ≤ 0} = ⋂ k ∈ s, {y : ι → ℝ | y (g k) ≤ 0} := by
        ext y; simp
      rw [h]
      exact isClosed_biInter (fun k _ => isClosed_le (continuous_apply (g k)) continuous_const)
    · have h : {y : ι → ℝ | ∀ k ∉ s, 0 ≤ y (g k)}
          = ⋂ k ∈ (sᶜ : Finset κ), {y : ι → ℝ | 0 ≤ y (g k)} := by ext y; simp
      rw [h]
      exact isClosed_biInter (fun k _ => isClosed_le continuous_const (continuous_apply (g k)))
  have hDsmeas : MeasurableSet Ds := hmeas.inter hOclosed.measurableSet
  obtain ⟨C, hC⟩ := exists_card_coset_inter_smul_sub_volume_mul_rpow_le T' Ds hDsbdd hDsmeas
    (exists_frontier_cover_inter_orthant g s D₀ hbdd hlip)
  exact ⟨MeasureTheory.volume.real Ds / |LinearMap.det (T' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))|, C, hC⟩

/-! ### The coset class and constancy of the residue on cells -/

open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone in
/-- The integer coordinates of a lattice point in the chart `T`. Since
`Φ x ∈ Φ '' idealLattice = T '' ℤ^ι`, the vector `T.symm (Φ x)` has integer entries
(`mem_span_int_basisFun_iff`). -/
private theorem exists_int_coord_of_mem {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    {x : mixedSpace K} (hx : x ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))
    (i : index K) :
    ∃ n : ℤ, (T.symm ((mixedEmbedding.stdBasis K).equivFunL x)) i = (n : ℝ) := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  have hmem : Φ x ∈ T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K)))) := by
    rw [hT]; exact ⟨x, hx, rfl⟩
  obtain ⟨v, hv, hveq⟩ := hmem
  have hsymm : T.symm (Φ x) = v := by rw [← hveq, LinearEquiv.symm_apply_apply]
  rw [hsymm]
  exact (mem_span_int_basisFun_iff v).mp hv i

open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone in
/-- **Coset class collapses to a lattice translation.** If two lattice points have the same
reduced integer coordinates mod `m` (in the chart `T`), then their difference lies in the
`m`-sublattice `(m : ℝ) • idealLattice`. -/
private theorem sub_mem_nsmul_of_coord_eq {K : Type*} [Field K] [NumberField K]
    (m : ℕ) (J : (Ideal (𝓞 K))⁰) (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    {x₁ x₂ : mixedSpace K}
    (hx₁ : x₁ ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))
    (hx₂ : x₂ ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))
    (hcos : ∀ i, ((round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL x₁)) i) : ZMod m)) =
      ((round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL x₂)) i) : ZMod m))) :
    x₁ - x₂ ∈
      (m : ℝ) • (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) : Set (mixedSpace K)) := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  choose n₁ hn₁ using exists_int_coord_of_mem J T hT hx₁
  choose n₂ hn₂ using exists_int_coord_of_mem J T hT hx₂
  rw [← hΦ] at hn₁ hn₂
  have hround : ∀ (x : mixedSpace K) (n : index K → ℤ),
      (∀ i, (T.symm (Φ x)) i = (n i : ℝ)) →
        ∀ i, round ((T.symm (Φ x)) i) = n i := fun x n h i => by
    rw [h i, round_intCast]
  -- coordinatewise divisibility, then the integer quotient vector `p`
  have hdvd : ∀ i, (m : ℤ) ∣ (n₁ i - n₂ i) := fun i => by
    have h := hcos i
    rw [hround x₁ n₁ hn₁ i, hround x₂ n₂ hn₂ i] at h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]
    exact h
  choose p hp using hdvd
  -- the chart difference is `m` times the integer vector `p`
  have hdiff : T.symm (Φ x₁) - T.symm (Φ x₂) = (m : ℝ) • (fun i => (p i : ℝ)) := by
    funext i
    rw [Pi.sub_apply, Pi.smul_apply, hn₁ i, hn₂ i, smul_eq_mul]
    have hZ : (n₁ i - n₂ i : ℤ) = (m : ℤ) * p i := hp i
    have : (n₁ i : ℝ) - (n₂ i : ℝ) = (m : ℝ) * (p i : ℝ) := by exact_mod_cast hZ
    linarith
  -- `T (↑p)` lies in the lattice image, so `↑p` lifts to a lattice element `z`
  have hpmem : (fun i => (p i : ℝ)) ∈ span ℤ (Set.range (Pi.basisFun ℝ (index K))) :=
    (mem_span_int_basisFun_iff _).mpr (fun i => ⟨p i, rfl⟩)
  have hTp : T (fun i => (p i : ℝ)) ∈ Φ '' (mixedEmbedding.idealLattice K
      (FractionalIdeal.mk0 K J) : Set (mixedSpace K)) := by
    rw [← hT]; exact ⟨_, hpmem, rfl⟩
  obtain ⟨z, hzmem, hzeq⟩ := hTp
  -- transport the difference back through `Φ`
  refine ⟨z, hzmem, ?_⟩
  have hkey : Φ (x₁ - x₂) = Φ ((m : ℝ) • z) := by
    rw [map_sub, map_smul]
    have h1 : Φ x₁ - Φ x₂ = T (T.symm (Φ x₁) - T.symm (Φ x₂)) := by
      rw [map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rw [h1, hdiff, map_smul, hzeq]
  exact (Φ.injective hkey).symm

open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone in
open NumberField.mixedEmbedding in
/-- **Signed norm class is coset-constant.** If the mixed embeddings of two algebraic integers
`x, y` differ by a vector of the `m`-sublattice, then `x = y + m·w` for some `w : 𝓞 K`
(`mixedEmbedding` injective), so the algebraic norm is constant mod `m`
(`natCast_algebraNorm_add_nsmul_mul`). -/
private theorem norm_zmod_eq_of_emb_sub_mem {K : Type*} [Field K] [NumberField K]
    (m : ℕ) (J : (Ideal (𝓞 K))⁰) (x y : 𝓞 K)
    (hsub : mixedEmbedding K (x : K) - mixedEmbedding K (y : K) ∈
      (m : ℝ) • (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) : Set (mixedSpace K))) :
    ((Algebra.norm ℤ x : ℤ) : ZMod m) = ((Algebra.norm ℤ y : ℤ) : ZMod m) := by
  obtain ⟨v, hv, hveq⟩ := hsub
  simp only at hveq
  rw [SetLike.mem_coe, mem_idealLattice] at hv
  obtain ⟨yK, hyK, hyeq⟩ := hv
  simp only [FractionalIdeal.coe_mk0] at hyK
  obtain ⟨w, _, hweq⟩ := hyK
  rw [Algebra.linearMap_apply] at hweq
  -- `x = y + m·w` in `𝓞 K`
  have hkey : mixedEmbedding K ((x - y : 𝓞 K) : K)
      = mixedEmbedding K (((m : 𝓞 K) * w : 𝓞 K) : K) := by
    push_cast
    rw [map_sub, ← hveq, ← hyeq, ← hweq, Nat.cast_smul_eq_nsmul, ← map_nsmul]
    congr 1
    rw [nsmul_eq_mul]
  have hxy : x - y = (m : 𝓞 K) * w :=
    RingOfIntegers.coe_injective (K := K) ((mixedEmbedding_injective K) hkey)
  have hx : x = y + (m : 𝓞 K) * w := by linear_combination hxy
  rw [hx]
  exact natCast_algebraNorm_add_nsmul_mul m y w

open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace in
/-- **Residue ⟺ signed residue on an orthant.** On the orthant where the real coordinates of `a`
are negative exactly on `s`, the absolute norm residue `intNorm a ≡ b (mod m)` becomes the signed
residue `(-1)^{#s} · Norm gen_a ≡ b (mod m)` (`natAbs_norm_eq_neg_one_pow_mul_norm`). -/
private theorem residue_iff_signed_on_orthant {K : Type*} [Field K] [NumberField K]
    (m b : ℕ) (J : (Ideal (𝓞 K))⁰) (a : idealSet K J)
    (s : Finset {w : InfinitePlace K // IsReal w})
    (hneg : ∀ w ∈ s, (a : mixedSpace K).1 w < 0)
    (hpos : ∀ w ∉ s, 0 < (a : mixedSpace K).1 w) :
    ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m)) ↔
      (((-1) ^ s.card * (Algebra.norm ℤ (preimageOfMemIntegerSet (idealSetMap K J a) : 𝓞 K) : ℤ) :
        ℤ) : ZMod m) = (b : ZMod m) := by
  set gen : 𝓞 K := (preimageOfMemIntegerSet (idealSetMap K J a) : 𝓞 K) with hgen
  have hema : mixedEmbedding K (gen : K) = (a : mixedSpace K) := by
    rw [hgen, mixedEmbedding_preimageOfMemIntegerSet, idealSetMap_apply]
  have hsign := natAbs_norm_eq_neg_one_pow_mul_norm gen s
    (fun w hw => by rw [hema]; exact hneg w hw) (fun w hw => by rw [hema]; exact hpos w hw)
  have hRes : intNorm (idealSetEquiv K J a).val = (Algebra.norm ℤ gen).natAbs := rfl
  have hcast : ((intNorm (idealSetEquiv K J a).val : ℕ) : ZMod m) =
      (((-1) ^ s.card * (Algebra.norm ℤ gen : ℤ) : ℤ) : ZMod m) := by
    rw [hRes, ← hsign, Int.cast_natCast]
  rw [hcast]

/-! ### The geometric per-cell bijection -/

open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone in
/-- **Coset membership ⟺ coset class.** For a lattice point `x`, the chart image `Φ x` lies in the
coset `T(k') + (m·T)(ℤ^ι)` (`k'` the canonical lift of `k`) iff the reduced integer coordinates
of `x` are `k` mod `m`. -/
private theorem mem_coset_iff_cos_eq {K : Type*} [Field K] [NumberField K]
    (m : ℕ) [NeZero m] (hm : (m : ℝ) ≠ 0) (J : (Ideal (𝓞 K))⁰)
    (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    (k : index K → ZMod m) {x : mixedSpace K}
    (hx : x ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)) :
    (mixedEmbedding.stdBasis K).equivFunL x ∈
        ((T (fun i => ((k i).val : ℝ)) : index K → ℝ) +ᵥ
          (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T) ''
            (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)))) ↔
      (∀ i, ((round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL x)) i) : ZMod m)) = k i) := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  choose n hn using exists_int_coord_of_mem J T hT hx
  rw [← hΦ] at hn
  have hround : ∀ i, round ((T.symm (Φ x)) i) = n i := fun i => by rw [hn i, round_intCast]
  simp only [hround, Set.mem_vadd_set, Set.mem_image, SetLike.mem_coe]
  -- reduce the goal class equality to the integer divisibility criterion
  have hgoal : (∀ i, ((n i : ZMod m)) = k i) ↔ (∀ i, (m : ℤ) ∣ (n i - (k i).val)) := by
    refine forall_congr' fun i => ?_
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero, Int.cast_natCast,
      ZMod.natCast_zmod_val]
  rw [hgoal]
  -- key: the coset element corresponds to the integer vector `p` with `n i = (k i).val + m·p i`
  have hkey : ∀ p : index K → ℤ,
      (T ((fun i => ((k i).val : ℝ)) + (m : ℝ) • (fun i => (p i : ℝ))) = Φ x) ↔
        (∀ i, n i = (k i).val + (m : ℤ) * p i) := fun p => by
    rw [← (LinearEquiv.eq_symm_apply T)]
    constructor
    · intro heq i
      have hc := congrFun heq i
      rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hn i] at hc
      have : (n i : ℝ) = ((k i).val + (m : ℤ) * p i : ℤ) := by push_cast; linarith
      exact_mod_cast this
    · intro h
      funext i
      rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hn i]
      have := h i; push_cast [this]; ring
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, hweq⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, vadd_eq_add, ← map_add] at hweq
    rw [mem_span_int_basisFun_iff] at hv
    choose p hp using hv
    have hpp : v = (fun i => (p i : ℝ)) := funext hp
    rw [hpp] at hweq
    exact fun i => ⟨p i, by rw [(hkey p).mp hweq i]; ring⟩
  · intro h
    choose p hp using h
    refine ⟨(LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T (fun i => (p i : ℝ)),
      ⟨_, (mem_span_int_basisFun_iff _).mpr (fun i => ⟨p i, rfl⟩), rfl⟩, ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, vadd_eq_add, ← map_add]
    exact (hkey p).mpr (fun i => by have := hp i; omega)

open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace Classical in
/-- **Cone points in a cell ⟷ lattice points in the dilated orthant cell.** Transport by the chart
`Φ` identifies the cone points of `idealSet K J` of norm `≤ t^d` in sign-orthant `s` and `m`-coset
`k` with the points of the coset `ξ_k + m·(T '' ℤ^ι)` inside the dilation `t • (D₀ ∩ orthant_s)`
(`D₀ = Φ '' normLeOne K`). Uses the cone-region homogeneity `cone_normLe_eq_smul_normLeOne`,
`Φ`-linearity, and `stdBasis_apply_isReal` (the real coordinates of `Φ x` are the real coordinates
of `x`). -/
private theorem card_fibre_eq_card_cell {K : Type*} [Field K] [NumberField K]
    (m : ℕ) [NeZero m] (hm : (m : ℝ) ≠ 0) (J : (Ideal (𝓞 K))⁰)
    (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    (s : Finset {w : InfinitePlace K // IsReal w}) (k : index K → ZMod m)
    {t : ℝ} (ht : 1 ≤ t) :
    Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
        (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} =>
          (a : mixedSpace K).1 w < 0) = s) ∧
        (fun i => (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
          (a : mixedSpace K))) i) : ZMod m)) = k}
    = Nat.card ↑(((T (fun i => ((k i).val : ℝ)) : index K → ℝ) +ᵥ
        (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T) ''
          (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)))) ∩
        t • ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩
          {y : index K → ℝ | (∀ w ∈ s, y (Sum.inl w) ≤ 0) ∧ (∀ w ∉ s, 0 ≤ y (Sum.inl w))})) := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  set d := Module.finrank ℚ K with hd
  set T' : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ) :=
    (LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T with hT'
  -- real coordinates of `Φ x` are the real coordinates of `x`
  have hΦreal : ∀ (x : mixedSpace K) (w : {w : InfinitePlace K // IsReal w}),
      Φ x (Sum.inl w) = x.1 w := fun x w => by
    rw [hΦ, Module.Basis.equivFunL_apply, mixedEmbedding.stdBasis_apply_isReal]
  -- the cone-region homogeneity
  have hcone : {x : mixedSpace K | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ t ^ d}
      = t • normLeOne K := cone_normLe_eq_smul_normLeOne ht
  set f : {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ d ∧
      (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} =>
        (a : mixedSpace K).1 w < 0) = s) ∧
      (fun i => (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k} → (index K → ℝ) :=
    fun a => Φ (a.1 : mixedSpace K) with hf
  have hfinj : Function.Injective f := fun a₁ a₂ h => by
    apply Subtype.ext; apply Subtype.ext
    exact Φ.injective h
  have ht0 : t ≠ 0 := (lt_of_lt_of_le one_pos ht).ne'
  have htinv : (0 : ℝ) < t⁻¹ := inv_pos.mpr (lt_of_lt_of_le one_pos ht)
  have himg : Φ '' (t • normLeOne K) = t • (Φ '' normLeOne K) :=
    Set.image_smul_comm Φ t _ (fun b => map_smul Φ t b)
  set Os : Set (index K → ℝ) :=
    {y : index K → ℝ | (∀ w ∈ s, y (Sum.inl w) ≤ 0) ∧ (∀ w ∉ s, 0 ≤ y (Sum.inl w))} with hOs
  -- cone points have nonzero real coordinates
  have hnz : ∀ x ∈ t • normLeOne K, ∀ w : {w : InfinitePlace K // IsReal w}, x.1 w ≠ 0 := by
    rintro _ ⟨z, hz, rfl⟩ w
    have hcx : t • z ∈ fundamentalCone K := smul_mem_of_mem hz.1 ht0
    have hp := fundamentalCone.normAtPlace_pos_of_mem hcx w.1
    rw [mixedEmbedding.normAtPlace_apply_of_isReal w.2] at hp
    exact fun h => by simp [h] at hp
  -- the region membership equivalence
  have hreg : ∀ x : mixedSpace K, x ∈ idealSet K J →
      (Φ x ∈ t • ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩ Os) ↔
        (mixedEmbedding.norm x ≤ t ^ d ∧
          Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} => x.1 w < 0) = s)) := by
    intro x hx
    rw [Set.smul_set_inter₀ ht0, Set.mem_inter_iff, ← hΦ, ← himg]
    constructor
    · rintro ⟨hmem, horth⟩
      rw [Set.mem_image] at hmem
      obtain ⟨z, hz, hzeq⟩ := hmem
      have hxcone : x ∈ t • normLeOne K := by rwa [Φ.injective hzeq] at hz
      have hnorm : x ∈ {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ t ^ d} := by
        rw [hcone]; exact hxcone
      refine ⟨hnorm.2, ?_⟩
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht0] at horth
      obtain ⟨hneg, hpos⟩ := horth
      refine ⟨fun hlt => ?_, fun hw => ?_⟩
      · by_contra hws
        have h2 := hpos w hws
        rw [Pi.smul_apply, smul_eq_mul, hΦreal] at h2
        nlinarith [h2, htinv, hlt]
      · have h2 := hneg w hw
        rw [Pi.smul_apply, smul_eq_mul, hΦreal] at h2
        rcases lt_or_gt_of_ne (hnz x hxcone w) with h | h
        · exact h
        · nlinarith [h2, htinv, h]
    · rintro ⟨hnorm, horth⟩
      have hxcone : x ∈ t • normLeOne K := by rw [← hcone]; exact ⟨hx.1, hnorm⟩
      refine ⟨⟨x, hxcone, rfl⟩, ?_⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht0]
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · rw [Pi.smul_apply, smul_eq_mul, hΦreal]
        have hlt : x.1 w < 0 := by
          have : w ∈ Finset.univ.filter (fun w => x.1 w < 0) := horth ▸ hw
          simpa using this
        nlinarith [hlt, htinv]
      · rw [Pi.smul_apply, smul_eq_mul, hΦreal]
        have hxw : ¬ x.1 w < 0 := fun hlt => hw (by
          have : w ∈ Finset.univ.filter (fun w => x.1 w < 0) := by simpa using hlt
          rwa [horth] at this)
        nlinarith [not_lt.mp hxw, htinv]
  -- the coset is contained in the chart image of the ideal lattice
  have hsub : ((T (fun i => ((k i).val : ℝ)) : index K → ℝ) +ᵥ
      (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T) ''
        (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))))
      ⊆ (Φ '' (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)) := by
    rw [← hT]
    rintro _ ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    simp only [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, vadd_eq_add]
    rw [← map_add]
    refine ⟨_, ?_, rfl⟩
    refine add_mem ((mem_span_int_basisFun_iff _).mpr (fun i => ⟨(k i).val, rfl⟩)) ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hv _
  have hset : Set.range f =
      (((T (fun i => ((k i).val : ℝ)) : index K → ℝ) +ᵥ
        (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T) ''
          (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)))) ∩
        t • ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩ Os)) := by
    ext y
    simp only [hf, Set.mem_range, Subtype.exists, Set.mem_inter_iff]
    constructor
    · rintro ⟨a, ha, hP, rfl⟩
      refine ⟨(mem_coset_iff_cos_eq m hm J T hT k ha.2).mpr (fun i => congrFun hP.2.2 i), ?_⟩
      exact hreg a ha |>.mpr ⟨hP.1, hP.2.1⟩
    · rintro ⟨hcoset, hregion⟩
      obtain ⟨z, hzlat, hzeq⟩ := hsub hcoset
      have hzcone : z ∈ idealSet K J := by
        obtain ⟨hmem, _⟩ := (by rwa [Set.smul_set_inter₀ ht0, Set.mem_inter_iff] at hregion :
          y ∈ t • (Φ '' normLeOne K) ∧ y ∈ t • Os)
        rw [← himg, Set.mem_image] at hmem
        obtain ⟨z', hz', hz'eq⟩ := hmem
        have hzn : z ∈ t • normLeOne K := by
          rw [show z = z' from Φ.injective (by rw [hz'eq, hzeq])]; exact hz'
        exact ⟨(by obtain ⟨z'', hz'', rfl⟩ := hzn; exact smul_mem_of_mem hz''.1 ht0), hzlat⟩
      refine ⟨z, hzcone, ⟨?_, ?_, ?_⟩, hzeq⟩
      · exact (hreg z hzcone |>.mp (by rw [hzeq]; exact hregion)).1
      · exact (hreg z hzcone |>.mp (by rw [hzeq]; exact hregion)).2
      · funext i
        exact (mem_coset_iff_cos_eq m hm J T hT k hzcone.2).mp (by rw [hzeq]; exact hcoset) i
  rw [← Nat.card_range_of_injective hfinj, hset]

open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace Classical in
/-- **Per-(orthant, coset) effective residue count.** For a fixed sign-orthant `s` and `m`-coset
`k`, the number of cone points of `idealSet K J` of norm `≤ t^d` in orthant `s`, coset `k`, **and**
carrying the residue `b` is `L·t^d + O(t^{d-1})`. The residue is constant on the cell (orthant +
coset determine it, via `residue_iff_signed_on_orthant`, `sub_mem_nsmul_of_coord_eq` and
`norm_zmod_eq_of_emb_sub_mem`): if it holds, the count is the workhorse cell count
(`card_fibre_eq_card_cell` + `exists_card_cell_sub_mul_rpow_le`); else the cell is empty. -/
private theorem exists_card_residue_fibre_sub_mul_rpow_le {K : Type*} [Field K] [NumberField K]
    (m : ℕ) [NeZero m] (hm : (m : ℝ) ≠ 0) (b : ℕ) (J : (Ideal (𝓞 K))⁰)
    (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    (hcov : ∃ (mc : ℕ) (M : ℝ≥0) (φ : Fin mc → (Fin (Fintype.card (index K) - 1) → ℝ) →
        (index K → ℝ)), (∀ j, LipschitzWith M (φ j)) ∧
      frontier ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K)) ⊆ ⋃ j, φ j '' Set.Icc 0 1)
    (s : Finset {w : InfinitePlace K // IsReal w}) (k : index K → ZMod m) :
    ∃ L C : ℝ, ∀ t : ℝ, 1 ≤ t →
      |(Nat.card {a : idealSet K J //
          (mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
            ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))) ∧
          (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} =>
            (a : mixedSpace K).1 w < 0) = s) ∧
          (fun i => (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
            (a : mixedSpace K))) i) : ZMod m)) = k} : ℝ) - L * t ^ Module.finrank ℚ K|
        ≤ C * t ^ (Module.finrank ℚ K - 1 : ℕ) := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  have hcard : Fintype.card (index K) = Module.finrank ℚ K := by
    rw [← Module.finrank_eq_card_basis (mixedEmbedding.stdBasis K), mixedEmbedding.finrank]
  -- residue is determined by (orthant, coset)
  have hconst : ∀ a a' : idealSet K J,
      Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} => (a : mixedSpace K).1 w < 0)
        = s →
      (fun i => (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k →
      Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} => (a' : mixedSpace K).1 w < 0)
        = s →
      (fun i => (round ((T.symm (Φ (a' : mixedSpace K))) i) : ZMod m)) = k →
      (((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m)) ↔
        ((intNorm (idealSetEquiv K J a').val : ZMod m) = (b : ZMod m))) := by
    intro a a' horth hcos horth' hcos'
    have hsign : ∀ c : idealSet K J,
        Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} =>
          (c : mixedSpace K).1 w < 0) = s →
        (((intNorm (idealSetEquiv K J c).val : ZMod m) = (b : ZMod m)) ↔
          (((-1) ^ s.card *
            (Algebra.norm ℤ (preimageOfMemIntegerSet (idealSetMap K J c) : 𝓞 K) : ℤ) : ℤ) :
            ZMod m) = (b : ZMod m)) := by
      intro c hc
      refine residue_iff_signed_on_orthant m b J c s (fun w hw => ?_) (fun w hw => ?_)
      · have : w ∈ Finset.univ.filter (fun w => (c : mixedSpace K).1 w < 0) := hc ▸ hw
        simpa using this
      · have hcw : (c : mixedSpace K).1 w ≠ 0 := by
          have hcone : (c : mixedSpace K) ∈ fundamentalCone K := c.2.1
          have hp := fundamentalCone.normAtPlace_pos_of_mem hcone w.1
          rw [mixedEmbedding.normAtPlace_apply_of_isReal w.2] at hp
          exact fun h => by simp [h] at hp
        have hge : ¬ (c : mixedSpace K).1 w < 0 := fun hlt => hw (by
          have : w ∈ Finset.univ.filter (fun w => (c : mixedSpace K).1 w < 0) := by simpa using hlt
          rwa [hc] at this)
        exact lt_of_le_of_ne (not_lt.mp hge) (Ne.symm hcw)
    rw [hsign a horth, hsign a' horth']
    have hnormeq : ((Algebra.norm ℤ (preimageOfMemIntegerSet (idealSetMap K J a) : 𝓞 K) : ℤ) :
          ZMod m) =
        ((Algebra.norm ℤ (preimageOfMemIntegerSet (idealSetMap K J a') : 𝓞 K) : ℤ) : ZMod m) := by
      refine norm_zmod_eq_of_emb_sub_mem m J _ _ ?_
      rw [show mixedEmbedding K ((preimageOfMemIntegerSet (idealSetMap K J a) : 𝓞 K) : K) =
            (a : mixedSpace K) from by
          rw [mixedEmbedding_preimageOfMemIntegerSet, idealSetMap_apply],
        show mixedEmbedding K ((preimageOfMemIntegerSet (idealSetMap K J a') : 𝓞 K) : K) =
            (a' : mixedSpace K) from by
          rw [mixedEmbedding_preimageOfMemIntegerSet, idealSetMap_apply]]
      exact sub_mem_nsmul_of_coord_eq m J T hT a.2.2 a'.2.2 (fun i => by
        rw [congrFun hcos i, congrFun hcos' i])
    push_cast
    rw [hnormeq]
  -- abbreviation for the residue-free fibre predicate
  by_cases hQ : ∃ a : idealSet K J,
      (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} =>
        (a : mixedSpace K).1 w < 0) = s) ∧
      ((fun i => (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k) ∧
      ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))
  · -- residue holds on the whole cell: count equals the cell count
    obtain ⟨a₀, horth₀, hcos₀, hres₀⟩ := hQ
    obtain ⟨leadC, cellC, hcell⟩ := exists_card_cell_sub_mul_rpow_le T m hm
      (Φ '' (normLeOne K)) (Φ.lipschitz.isBounded_image (isBounded_normLeOne K))
      ((Φ.toHomeomorph.toMeasurableEquiv).measurableSet_image.mpr (measurableSet_normLeOne K))
      hcov (Sum.inl : {w : InfinitePlace K // IsReal w} → index K) s
    refine ⟨leadC, cellC, fun t ht => ?_⟩
    have hfibre : Nat.card {a : idealSet K J //
        (mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
          ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))) ∧
        (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} =>
          (a : mixedSpace K).1 w < 0) = s) ∧
        (fun i => (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k}
        = Nat.card {a : idealSet K J //
          mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
          (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} =>
            (a : mixedSpace K).1 w < 0) = s) ∧
          (fun i => (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
      constructor
      · rintro ⟨⟨hn, _⟩, ho, hc⟩; exact ⟨hn, ho, hc⟩
      · rintro ⟨hn, ho, hc⟩
        exact ⟨⟨hn, (hconst a a₀ ho hc horth₀ hcos₀).mpr hres₀⟩, ho, hc⟩
    rw [hfibre, card_fibre_eq_card_cell m hm J T hT s k ht]
    have hpow1 : t ^ Module.finrank ℚ K = t ^ Fintype.card (index K) := by rw [hcard]
    have hpow2 : t ^ (Module.finrank ℚ K - 1 : ℕ) = t ^ (Fintype.card (index K) - 1 : ℕ) := by
      rw [hcard]
    rw [hpow1, hpow2]
    exact hcell (T (fun i => ((k i).val : ℝ))) t ht
  · -- residue fails on the whole cell: count is zero
    refine ⟨0, 0, fun t ht => ?_⟩
    have hempty : IsEmpty {a : idealSet K J //
        (mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
          ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))) ∧
        (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} =>
          (a : mixedSpace K).1 w < 0) = s) ∧
        (fun i => (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k} := by
      refine ⟨fun a => hQ ⟨a.1, a.2.2.1, a.2.2.2, a.2.1.2⟩⟩
    rw [Nat.card_of_isEmpty]
    simp

open Ideal NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone Units in
/-- **Finiteness of bounded-norm cone points.** The cone points of `idealSet K J` of norm `≤ s`
form a finite set: they inject (via `integerSetEquiv ∘ idealSetMap`) into the product of the
finite set of integral ideals of norm `≤ ⌊s⌋` (`Ideal.finite_setOf_absNorm_le₀`) with the finite
torsion group. -/
private theorem finite_idealSet_norm_le {K : Type*} [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (s : ℝ) :
    Finite {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ s} := by
  classical
  have hbase : Finite ({I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ ⌊s⌋₊} ×
      torsion K) := by
    haveI : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ ⌊s⌋₊} :=
      (Ideal.finite_setOf_absNorm_le₀ ⌊s⌋₊).to_subtype
    infer_instance
  refine Finite.of_injective (β := {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ ⌊s⌋₊} ×
      torsion K) (fun a => ⟨⟨(integerSetEquiv K (idealSetMap K J a.1)).1.1, ?_⟩,
    (integerSetEquiv K (idealSetMap K J a.1)).2⟩) ?_
  · have hnorm : Ideal.absNorm ((integerSetEquiv K (idealSetMap K J a.1)).1.1 : Ideal (𝓞 K))
        = intNorm (idealSetMap K J a.1) := by
      rw [integerSetEquiv_apply_fst, intNorm, absNorm_span_singleton]
    rw [hnorm]
    refine Nat.le_floor ?_
    rw [intNorm_coe, idealSetMap_apply]
    exact a.2
  · intro a a' h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    have : integerSetEquiv K (idealSetMap K J a.1) = integerSetEquiv K (idealSetMap K J a'.1) :=
      Prod.ext (Subtype.ext h.1) h.2
    have h2 : idealSetMap K J a.1 = idealSetMap K J a'.1 := (integerSetEquiv K).injective this
    exact Subtype.ext (Subtype.ext (by
      have := congrArg (Subtype.val) h2; simpa [idealSetMap_apply] using this))

open Ideal in
open Ideal NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace in
/-- **Effective count of cone points of `idealSet K J` with a norm residue** (the Widmer / GRS
geometric core). For a fixed nonzero ideal `J`, a modulus `m` and a residue `b`, the number of
cone points `a ∈ idealSet K J` of `mixedEmbedding.norm ≤ N·N(J)` whose integer norm
`intNorm (idealSetEquiv K J a)` is `≡ b (mod m)` is `κ·N + O(N^{1-1/d})`, `d = [K:ℚ]`.

This is the substantive analytic input. Proof (Gun–Ramaré–Sivaraman, *Counting ideals in ray
classes*, JNT 243 (2023), §3, after Widmer, Trans. AMS 362 (2010)): transport the count to the
standard coordinate space `index K → ℝ` along the chart `Φ = (stdBasis K).equivFunL`
(`map_span_int_linearEquiv` carries `idealLattice K J` to a full lattice `Λ_J = T '' ℤ^ι`); the
norm-region `fundamentalCone ∩ {norm ≤ N·N(J)}` is the real dilation `t • normLeOne K` at
`t = (N·N(J))^{1/d}` (norm-homogeneity `mixedEmbedding.norm_smul` + cone `smul`-stability
`smul_mem_iff_mem`), so the count is the number of points of `Λ_J ∩ (t • Φ '' normLeOne K)`
carrying the residue. Partition by the sign pattern `s` of the real coordinates (the orthant
decomposition `plusPart`/`negAt`); on each orthant `natAbs_norm_eq_neg_one_pow_mul_norm` turns the
absolute residue `|Norm| ≡ b` into the signed residue `Norm ≡ ±b`, which is constant on cosets of
`m • Λ_J` (`natCast_algebraNorm_add_nsmul_mul`). Count each qualifying (orthant, coset) by the
workhorse `exists_card_coset_inter_smul_sub_volume_mul_rpow_le` (the frontier cover from
`normLeOne_frontier_lipschitz_cover_index` together with the bounded coordinate-hyperplane pieces
cut by the orthant), and sum the finitely many estimates: the leading terms give `κ·N` (with
`t^d = N·N(J)`) and the error terms `O(t^{d-1}) = O((N·N(J))^{1-1/d}) = O(N^{1-1/d})`
(`Real.rpow` algebra, `N(J) ≥ 1`). -/
private theorem exists_card_idealSet_residue_le {K : Type*} [Field K] [NumberField K]
    (m : ℕ) [NeZero m] (b : ℕ) (J : (Ideal (𝓞 K))⁰) :
    ∃ κ C' : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤
            ((N * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℝ) ∧
          ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))} : ℝ) - κ * N|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  set d := Module.finrank ℚ K with hd
  have hdpos : 0 < d := Module.finrank_pos
  have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
  set NJ := Ideal.absNorm (J : Ideal (𝓞 K)) with hNJdef
  have hNJ : 0 < NJ := absNorm_pos_of_nonZeroDivisors J
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  obtain ⟨T, hT⟩ := exists_latticeEquiv_image_idealLattice J
  obtain ⟨mc, M, φ, hφ, hcovraw⟩ := normLeOne_frontier_lipschitz_cover_index K
  have hcov : ∃ (mc : ℕ) (M : ℝ≥0) (φ : Fin mc → (Fin (Fintype.card (index K) - 1) → ℝ) →
      (index K → ℝ)), (∀ j, LipschitzWith M (φ j)) ∧
      frontier (Φ '' (normLeOne K)) ⊆ ⋃ j, φ j '' Set.Icc 0 1 := ⟨mc, M, φ, hφ, hcovraw⟩
  -- per-(orthant,coset) effective estimates
  choose L C hLC using fun p : Finset {w : InfinitePlace K // IsReal w} × (index K → ZMod m) =>
    exists_card_residue_fibre_sub_mul_rpow_le m hm b J T hT hcov p.1 p.2
  refine ⟨(∑ p, L p) * NJ, (∑ p, |C p|) * (NJ : ℝ) ^ (1 - (d : ℝ)⁻¹), fun N hN => ?_⟩
  set tN : ℝ := ((N * NJ : ℕ) : ℝ) ^ ((d : ℝ)⁻¹) with htN
  have hNN1 : 1 ≤ ((N * NJ : ℕ) : ℝ) := by
    rw [Nat.one_le_cast]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hN) hNJ.ne')
  have htN1 : 1 ≤ tN := Real.one_le_rpow hNN1 (by positivity)
  have htNd : tN ^ d = ((N * NJ : ℕ) : ℝ) := by
    rw [htN, ← Real.rpow_natCast (((N * NJ : ℕ) : ℝ) ^ ((d : ℝ)⁻¹)) d, ← Real.rpow_mul
      (by positivity), inv_mul_cancel₀ hdne, Real.rpow_one]
  -- partition the count by (orthant, coset)
  have hpart : Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤
        ((N * NJ : ℕ) : ℝ) ∧ ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))}
      = ∑ p : Finset {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} ×
          (index K → ZMod m),
        Nat.card {a : idealSet K J //
          (mixedEmbedding.norm (a : mixedSpace K) ≤ tN ^ d ∧
            ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))) ∧
          (Finset.univ.filter (fun w : {w : NumberField.InfinitePlace K //
            NumberField.InfinitePlace.IsReal w} => (a : mixedSpace K).1 w < 0) = p.1) ∧
          (fun i => (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = p.2} := by
    rw [htNd]
    let cls : {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ ((N * NJ : ℕ) : ℝ) ∧
        ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))} →
        Finset {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} ×
          (index K → ZMod m) :=
      fun a => (Finset.univ.filter (fun w => (a.1 : mixedSpace K).1 w < 0),
        fun i => (round ((T.symm (Φ (a.1 : mixedSpace K))) i) : ZMod m))
    haveI hfinbase : Finite {a : idealSet K J //
        mixedEmbedding.norm (a : mixedSpace K) ≤ ((N * NJ : ℕ) : ℝ)} :=
      finite_idealSet_norm_le J _
    haveI : ∀ p : Finset {w : NumberField.InfinitePlace K //
        NumberField.InfinitePlace.IsReal w} × (index K → ZMod m),
        Finite {a : idealSet K J //
          (mixedEmbedding.norm (a : mixedSpace K) ≤ ((N * NJ : ℕ) : ℝ) ∧
            ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))) ∧
          (Finset.univ.filter (fun w : {w : NumberField.InfinitePlace K //
            NumberField.InfinitePlace.IsReal w} => (a : mixedSpace K).1 w < 0) = p.1) ∧
          (fun i => (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = p.2} := fun p =>
      Finite.of_injective (fun a => (⟨a.1, a.2.1.1⟩ : {a : idealSet K J //
        mixedEmbedding.norm (a : mixedSpace K) ≤ ((N * NJ : ℕ) : ℝ)}))
        (fun x y h => Subtype.ext (by simpa using h))
    rw [← Nat.card_sigma]
    refine Nat.card_congr ((Equiv.sigmaFiberEquiv cls).symm.trans (Equiv.sigmaCongrRight fun p =>
      ?_))
    exact {
      toFun := fun a => ⟨a.1.1, ⟨a.1.2, by
          have := a.2; simp only [cls, Prod.ext_iff] at this; exact ⟨this.1, this.2⟩⟩⟩
      invFun := fun a => ⟨⟨a.1, a.2.1⟩, by simp only [cls, Prod.ext_iff]; exact ⟨a.2.2.1, a.2.2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hpart, Nat.cast_sum]
  -- the error exponent: `tN^(d-1) = N^(1-1/d) · NJ^(1-1/d)`
  have htNd1 : tN ^ (d - 1 : ℕ) = (N : ℝ) ^ (1 - (d : ℝ)⁻¹) * (NJ : ℝ) ^ (1 - (d : ℝ)⁻¹) := by
    have hdcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub hdpos]; simp
    rw [htN, ← Real.rpow_natCast (((N * NJ : ℕ) : ℝ) ^ ((d : ℝ)⁻¹)) (d - 1),
      ← Real.rpow_mul (by positivity), hdcast, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg N) (Nat.cast_nonneg NJ)]
    congr 1 <;> · rw [inv_mul_eq_div, sub_div, div_self hdne, one_div]
  -- rewrite the leading term as a sum and bound termwise
  have hlead : (∑ p, L p) * (NJ : ℝ) * (N : ℝ) = ∑ p, L p * tN ^ d := by
    rw [← Finset.sum_mul]
    rw [htNd]; push_cast; ring
  rw [hlead, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hbound : (∑ p, |C p|) * (NJ : ℝ) ^ (1 - (d : ℝ)⁻¹) * (N : ℝ) ^ (1 - (d : ℝ)⁻¹)
      = ∑ p, |C p| * tN ^ (d - 1 : ℕ) := by
    simp_rw [htNd1, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p _ => by ring)
  rw [hbound]
  refine Finset.sum_le_sum (fun p _ => ?_)
  refine (hLC p tN htN1).trans ?_
  gcongr
  exact le_abs_self _

open Ideal NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone Units in
/-- **Effective count of `J`-divisible principal ideals with a norm residue** (the geometric core
of the per-class count). For a fixed nonzero ideal `J` and a residue `b (mod m)`, the number of
`J`-divisible principal ideals of norm `≤ N·N(J)` with norm residue `b (mod m)` is
`κ·N + O(N^{1-1/d})`.

Reduction to the cone-point count `exists_card_idealSet_residue_le`: the residue-decorated torsion
bridge `card_isPrincipal_dvd_norm_le_residue` (at `s = N·N(J)`) equates the ideal count times
`torsionOrder K` with the cone-point count carrying the same residue; dividing the effective
cone-point estimate by the (nonzero) torsion order gives the bound, with `κ` and `C'` scaled by
`1/torsionOrder K`. -/
private theorem exists_card_dvd_principal_residue_eq_sub_mul_rpow_le
    {K : Type*} [Field K] [NumberField K] (m : ℕ) [NeZero m] (b : ℕ) (J : (Ideal (𝓞 K))⁰) :
    ∃ κ C' : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K)) ∧
            (IsPrincipal (I : Ideal (𝓞 K)) ∧
            Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m)))} : ℝ)
          - κ * N|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨κ, C', hcore⟩ := exists_card_idealSet_residue_le m b J
  have htors : (0 : ℝ) < torsionOrder K := by
    exact_mod_cast (torsionOrder K).pos_of_ne_zero (torsionOrder_ne_zero K)
  refine ⟨κ / torsionOrder K, C' / torsionOrder K, fun N hN => ?_⟩
  have hcount : (Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K)) ∧
      (IsPrincipal (I : Ideal (𝓞 K)) ∧
      Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
      ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m)))} : ℝ) * torsionOrder K
      = (Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤
          ((N * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℝ) ∧
        ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))} : ℝ) := by
    rw [← Nat.cast_mul]; congr 1
    rw [← card_isPrincipal_dvd_norm_le_residue J m b
      ((N * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℝ)]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun I => by simp only [Nat.cast_le])
  have he : |(Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K)) ∧
      (IsPrincipal (I : Ideal (𝓞 K)) ∧
      Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
      ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m)))} : ℝ) - κ / torsionOrder K * N|
      = |(Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤
          ((N * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℝ) ∧
        ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))} : ℝ) - κ * N| /
        torsionOrder K := by
    rw [eq_div_iff htors.ne', ← hcount,
      show ((Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K)) ∧
          (IsPrincipal (I : Ideal (𝓞 K)) ∧
          Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m)))} : ℝ) *
            (torsionOrder K : ℝ) - κ * N)
        = (torsionOrder K : ℝ) * ((Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣
          (I : Ideal (𝓞 K)) ∧ (IsPrincipal (I : Ideal (𝓞 K)) ∧
          Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m)))} : ℝ) -
            κ / torsionOrder K * N) by field_simp,
      abs_mul, abs_of_pos htors, mul_comm]
  rw [he, div_le_iff₀ htors]
  calc |(Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤
          ((N * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℝ) ∧
        ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))} : ℝ) - κ * N|
      ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := hcore N hN
    _ = C' / torsionOrder K * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) * torsionOrder K := by
        field_simp

open Ideal in
/-- **Per-class effective residue count.** For a fixed ideal class `C`, the number of nonzero
integral ideals of norm `≤ N`, norm residue `a (mod c)`, **and class `C`** equals
`κ_C · N + O(N^{1-1/d})`. Summed over the finite class group by
`card_norm_le_residue_eq_sum_class`, this is the full effective count
`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`. Proof: principalize to `J`-divisible
principal ideals (`card_principalize`, with `ClassGroup.mk0 J = C⁻¹`), then invoke the geometric
core `exists_card_dvd_principal_residue_eq_sub_mul_rpow_le` at modulus `c·N(J)` and residue
`a·N(J)`. -/
private theorem exists_card_norm_le_residue_class_eq_sub_mul_rpow_le
    {K : Type*} [Field K] [NumberField K] (c : ℕ) [NeZero c] (a : ZMod c) (C : ClassGroup (𝓞 K)) :
    ∃ κ C' : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C} : ℝ)
          - κ * N|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  -- Pick a representative `J` of `C⁻¹`.
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  have hNJ : 0 < Ideal.absNorm (J : Ideal (𝓞 K)) := absNorm_pos_of_nonZeroDivisors J
  -- The residue on the principalized side is modulo `c·N(J)` at value `a.val·N(J)`.
  haveI : NeZero (c * Ideal.absNorm (J : Ideal (𝓞 K))) :=
    ⟨Nat.mul_ne_zero (NeZero.ne c) hNJ.ne'⟩
  obtain ⟨κ, C', hκ⟩ := exists_card_dvd_principal_residue_eq_sub_mul_rpow_le
    (c * Ideal.absNorm (J : Ideal (𝓞 K))) (a.val * Ideal.absNorm (J : Ideal (𝓞 K))) J
  refine ⟨κ, C', fun N hN => ?_⟩
  rw [card_principalize c a N C J hJ hNJ]
  exact hκ N hN

/-- **The leading constant is the limit of `count / N`.** An effective estimate
`|f N - κ·N| ≤ C'·N^{1-1/d}` (with `d ≥ 1`) pins `κ` as the limit of `f N / N`: the relative
error is `|f N / N - κ| ≤ |C'|·N^{-1/d} → 0`. In particular two leading constants for the same
counting function `f` must coincide (`Filter.Tendsto.unique`). This makes the per-residue
density of `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le` a well-defined invariant of the
residue, independent of the `∃`-witness. -/
private theorem tendsto_div_atTop_of_sub_mul_rpow_le {f : ℕ → ℝ} {κ C' : ℝ} {d : ℕ}
    (hd : 0 < d) (hbound : ∀ N : ℕ, 1 ≤ N → |f N - κ * N| ≤ C' * (N : ℝ) ^ (1 - (d : ℝ)⁻¹)) :
    Filter.Tendsto (fun N : ℕ => f N / (N : ℝ)) Filter.atTop (nhds κ) := by
  have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hdpos : (0 : ℝ) < (d : ℝ)⁻¹ := by positivity
  -- The dominating sequence `|C'| · N^{-1/d}` tends to `0`.
  have hzero : Filter.Tendsto (fun N : ℕ => |C'| * (N : ℝ) ^ (-(d : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
      by
    have h1 : Filter.Tendsto (fun x : ℝ => x ^ (-(d : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
      tendsto_rpow_neg_atTop hdpos
    have h2 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
      h1.comp tendsto_natCast_atTop_atTop
    simpa using h2.const_mul |C'|
  -- Squeeze `‖f N / N - κ‖ = |f N / N - κ|` between `0` and the dominating sequence.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _) ?_ hzero
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  rw [Real.norm_eq_abs, div_sub' hNne, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos,
    mul_comm (N : ℝ) κ]
  refine (hbound N hN).trans ?_
  -- `C' · N^{1-1/d} ≤ |C'| · N^{-1/d} · N`, using `N^{1-1/d} = N^{-1/d} · N`.
  have hsplit : (N : ℝ) ^ (1 - (d : ℝ)⁻¹) = (N : ℝ) ^ (-(d : ℝ)⁻¹) * (N : ℝ) := by
    rw [show (1 : ℝ) - (d : ℝ)⁻¹ = -(d : ℝ)⁻¹ + 1 by ring, Real.rpow_add hNpos, Real.rpow_one]
  rw [hsplit, ← mul_assoc]
  gcongr
  exact le_abs_self C'

/-- **Effective ideal count by norm residue.** For a number field `K` and a modulus `c`, the
number of nonzero integral ideals of norm `≤ N` with norm residue `a (mod c)` is
`κ_a · N + O(N^{1-1/d})`, `d = [K:ℚ]`. Proof: split by ideal class (finitely many)
(`card_norm_le_residue_eq_sum_class`); sum the per-class effective counts
(`exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`) and bound the total error by the
triangle inequality over the (finite) class group. -/
theorem exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le
    (K : Type*) [Field K] [NumberField K] (c : ℕ) [NeZero c] (a : ZMod c) :
    ∃ κ C' : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a} : ℝ)
          - κ * N|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  -- Per-class constants.
  choose κf C'f hκf using fun C : ClassGroup (𝓞 K) =>
    exists_card_norm_le_residue_class_eq_sub_mul_rpow_le (K := K) c a C
  refine ⟨∑ C : ClassGroup (𝓞 K), κf C, ∑ C : ClassGroup (𝓞 K), |C'f C|, fun N hN => ?_⟩
  -- Split the count and the leading term over the class group.
  rw [card_norm_le_residue_eq_sum_class c a N]
  rw [show ((∑ C : ClassGroup (𝓞 K),
        Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C} : ℕ) : ℝ)
      = ∑ C : ClassGroup (𝓞 K),
        (Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C} : ℝ) by
    push_cast; rfl]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun C _ => ?_)
  refine (hκf C N hN).trans ?_
  gcongr
  exact le_abs_self _

/-- **Norm-residue count, abbreviation.** `cardNormLeResidue K c a N` is the number of nonzero
integral ideals of `𝓞 K` of norm `≤ N` whose norm is `≡ a (mod c)`. The leading constant of its
effective estimate (`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`) is, by
`tendsto_div_atTop_of_sub_mul_rpow_le`, the limit of `cardNormLeResidue K c a N / N`. -/
private def cardNormLeResidue (K : Type*) [Field K] [NumberField K] (c : ℕ) (a : ZMod c)
    (N : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
    ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a}

/-- The density `lim cardNormLeResidue K c a N / N` exists and equals the leading constant of
`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`. -/
private theorem exists_tendsto_cardNormLeResidue_div (K : Type*) [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (a : ZMod c) :
    ∃ κ : ℝ, Filter.Tendsto (fun N : ℕ => (cardNormLeResidue K c a N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ) := by
  obtain ⟨κ, C', hκ⟩ := exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le K c a
  exact ⟨κ, tendsto_div_atTop_of_sub_mul_rpow_le Module.finrank_pos
    (fun N hN => hκ N hN)⟩

/-- **Character-column orthogonality** for a finite commutative group `G`: for `g ≠ 1`, the sum
of `χ g` over all characters `χ : G →* ℂˣ` vanishes. A separating character `χ₀` with
`χ₀ g ≠ 1` exists (`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`, with
`HasEnoughRootsOfUnity ℂ` from algebraic closedness), and reindexing the sum by translation
with `χ₀` scales it by `χ₀ g`, forcing it to vanish. -/
private theorem sum_char_apply_eq_zero_of_ne_one {G : Type*} [CommGroup G] [Finite G]
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

open scoped Classical in
/-- **κ-uniformity over the realized-residue subgroup (the geometric core).** The Dirichlet
density of ideals with a fixed norm residue is **constant on the subgroup `S` of realized
residues**: if `a, a' ∈ S` and the counts `cardNormLeResidue K c a` and `cardNormLeResidue K c a'`
have densities `κ` and `κ'` (limits of `count / N`), then `κ = κ'`.

This is the analytic heart of the Chebotarev abelian step (the `g`-independence of the
Frobenius-fibre density over the image subgroup of ideal norms — the `ℚ(i)`-trap avoidance:
uniformity over the **image subgroup**, never over all of `(ℤ/c)ˣ`).

### Status: the single remaining gap of `IdealCongruenceCount`.

The classical statement (Lang, *Algebraic Number Theory* GTM 110, Ch. VI §3 Thm 3;
Gun–Ramaré–Sivaraman, JNT 243 (2023), Thm 1) is **true**, but the elementary `κ`-transfer
sketched in earlier drafts (multiply by a realizing ideal `𝔟`, sandwich) does **not** close:
multiplication by `𝔟` scales the norm by `N𝔟 ≥ 1`, so it only yields the lossy
`κ_a ≤ N𝔟 · κ_{a·t}` (and, with the inverse, `1 ≤ N𝔟 · N𝔟'`), never the needed equality —
there is no norm-preserving ideal map shifting the residue. The genuine proof is geometric and
goes through the per-`(orthant, coset)` cell structure already built in this file
(`exists_card_idealSet_residue_le`): the per-residue density is
`κ_a = N(J)·∑_{cells (s,k)} ⟦residue holds on cell⟧ · vol(D₀ ∩ orthant s)/|det T'|`, summed over
ideal classes. Two ingredients close it:

* **Orthant volume symmetry.** `vol(D₀ ∩ orthant s)` is independent of the sign pattern `s`,
  since `D₀ = Φ '' normLeOne K` is sign-symmetric (mathlib's `volume_negAt_plusPart` /
  `volume_eq_two_pow_mul_volume_plusPart`, transported through the chart `Φ`). Hence each cell
  contributes the same `κ₀ = vol(D₀)/(2^{r₁}·|det T'|)` and `κ_a = κ₀·N(J)·#{qualifying cells}`.

* **Equinumerosity of qualifying cells across `S`.** Multiplication by an element `y ∈ 𝓞 K`
  invertible mod the per-class modulus `c·N(J)` permutes the cells `(s,k)` and shifts the
  signed-norm residue by `Norm y`, giving a bijection between the qualifying-cell sets for
  residues `a` and `a·(Norm y)`. The obstruction is that this needs **element** realizers `y`
  coprime to `c·N(J)`, whereas the available hypothesis `hS` supplies **ideal** realizers `𝔟`
  with no control of coprimality to the (class-dependent) factor `N(J)`.

**The proof here is instead the Fourier route**: the hypothesis `hF` — for every nontrivial
character `χ` of `S`, the `χ`-twisted count average `(∑_{s ∈ S} χ(s)·count_s(N))/N → 0` — says
all nontrivial Fourier coefficients of the density function `s ↦ κ_s` on `S` vanish, so by
finite-abelian Fourier inversion (`sum_char_apply_eq_zero_of_ne_one` orthogonality) that
function is constant on `S`. `hF` is discharged by the Gap-B consumer (`ZetaProduct.lean`) via
the proven LF3 character-sum bound `character_sum_geometry_of_numbers_bound` through
`autToPow_frobeniusClass_out`: each character of the realized subgroup pulls back to a Galois
character of `Gal(K(μ_m)/K)`, and the twisted counts are the `galoisCharacterOnIdeal` partial
sums up to the bad-prime corrections. -/
private theorem cardNormLeResidue_density_eq_of_mem_subgroup {K : Type*} [Field K] [NumberField K]
    {c : ℕ} [NeZero c] {S : Subgroup (ZMod c)ˣ}
    (hF : ∀ χ : S →* ℂˣ, χ ≠ 1 →
      Filter.Tendsto (fun N : ℕ => (∑ s : S, ((χ s : ℂˣ) : ℂ) *
          (cardNormLeResidue K c ((s : (ZMod c)ˣ) : ZMod c) N : ℂ)) / (N : ℂ))
        Filter.atTop (nhds 0))
    {a a' : (ZMod c)ˣ} (ha : a ∈ S) (ha' : a' ∈ S) {κ κ' : ℝ}
    (hκ : Filter.Tendsto (fun N : ℕ => (cardNormLeResidue K c (a : ZMod c) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ))
    (hκ' : Filter.Tendsto (fun N : ℕ => (cardNormLeResidue K c (a' : ZMod c) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ')) :
    κ = κ' := by
  haveI : NeZero ((Monoid.exponent S : ℕ) : ℂ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩
  haveI : Fintype (S →* ℂˣ) := Fintype.ofFinite _
  choose κf hκf using fun s : S =>
    exists_tendsto_cardNormLeResidue_div K c ((s : (ZMod c)ˣ) : ZMod c)
  have hκa : κ = κf ⟨a, ha⟩ := tendsto_nhds_unique hκ (hκf ⟨a, ha⟩)
  have hκa' : κ' = κf ⟨a', ha'⟩ := tendsto_nhds_unique hκ' (hκf ⟨a', ha'⟩)
  -- All nontrivial `S`-Fourier coefficients of `s ↦ κf s` vanish.
  have hhat : ∀ χ : S →* ℂˣ, χ ≠ 1 →
      ∑ s : S, ((χ s : ℂˣ) : ℂ) * (κf s : ℂ) = 0 := by
    intro χ hχ
    refine tendsto_nhds_unique ?_ (hF χ hχ)
    have hsum := tendsto_finset_sum Finset.univ fun s (_ : s ∈ Finset.univ) =>
      ((Complex.continuous_ofReal.tendsto (κf s)).comp (hκf s)).const_mul ((χ s : ℂˣ) : ℂ)
    refine hsum.congr fun N => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Function.comp_apply]
    push_cast
    ring
  -- Fourier inversion: `card · κf u = ∑ κf` for every `u`, hence `κf` is constant.
  have hinv : ∀ u : S, (Fintype.card (S →* ℂˣ) : ℂ) * (κf u : ℂ) = ∑ s : S, (κf s : ℂ) := by
    intro u
    have horth : ∀ s : S, (∑ χ : S →* ℂˣ, ((χ (u⁻¹ * s) : ℂˣ) : ℂ))
        = if s = u then (Fintype.card (S →* ℂˣ) : ℂ) else 0 := by
      intro s
      by_cases hs : s = u
      · subst hs
        simp
      · rw [if_neg hs]
        exact sum_char_apply_eq_zero_of_ne_one fun h => hs (inv_mul_eq_one.mp h).symm
    calc (Fintype.card (S →* ℂˣ) : ℂ) * (κf u : ℂ)
        = ∑ s : S, (if s = u then (Fintype.card (S →* ℂˣ) : ℂ) else 0) * (κf s : ℂ) := by
          simp [ite_mul]
      _ = ∑ s : S, (∑ χ : S →* ℂˣ, ((χ (u⁻¹ * s) : ℂˣ) : ℂ)) * (κf s : ℂ) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [horth s]
      _ = ∑ s : S, ∑ χ : S →* ℂˣ, ((χ (u⁻¹ * s) : ℂˣ) : ℂ) * (κf s : ℂ) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ χ : S →* ℂˣ, ∑ s : S, ((χ (u⁻¹ * s) : ℂˣ) : ℂ) * (κf s : ℂ) := Finset.sum_comm
      _ = ∑ χ : S →* ℂˣ, ((χ u⁻¹ : ℂˣ) : ℂ) * ∑ s : S, ((χ s : ℂˣ) : ℂ) * (κf s : ℂ) := by
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [map_mul, Units.val_mul, mul_assoc]
      _ = ∑ s : S, (κf s : ℂ) := by
          rw [Finset.sum_eq_single (1 : S →* ℂˣ)]
          · simp
          · intro χ _ hχ
            rw [hhat χ hχ, mul_zero]
          · intro h
            exact absurd (Finset.mem_univ _) h
  have hcard0 : ((Fintype.card (S →* ℂˣ) : ℂ)) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hfc : (κf ⟨a, ha⟩ : ℂ) = (κf ⟨a', ha'⟩ : ℂ) :=
    mul_left_cancel₀ hcard0 ((hinv ⟨a, ha⟩).trans (hinv ⟨a', ha'⟩).symm)
  rw [hκa, hκa']
  exact_mod_cast hfc

open scoped Classical in
/-- **Norm-residue density transfer (κ-uniformity over realized residues).** Under the
Fourier-decay hypothesis `hF` — for every nontrivial character `χ` of `S ≤ (ℤ/c)ˣ`, the
`χ`-twisted count average over `S` tends to `0` — the leading densities of
`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le` can be taken **equal across `S`**: there
is **one** pair `(κ, C')` for which the effective estimate
`|#{N(I) ≤ N, N(I) ≡ a} − κ·N| ≤ C'·N^{1-1/d}` holds for every `a ∈ S` simultaneously. This is
the `g`-independence input of the Frobenius-fibre equidistribution (the `ℚ(i)`-trap avoidance:
uniformity over the **image subgroup** of ideal norms, never over all of `(ℤ/c)ˣ`).

`hF` is discharged by the consumer (Gap B in `ZetaProduct.lean`) via the proven
`character_sum_geometry_of_numbers_bound` (LF3) through `autToPow_frobeniusClass_out`: each
`S`-character pulls back to a Galois character, and the twisted counts are the
`galoisCharacterOnIdeal` partial sums up to bad-prime corrections.

Proof: the per-residue leading constants are the limits of `count / N`
(`tendsto_div_atTop_of_sub_mul_rpow_le`), so they are constant on `S` by Fourier inversion
(`cardNormLeResidue_density_eq_of_mem_subgroup`); take that common value as `κ` and the sum of
the per-residue error constants over the finite `ZMod c` as `C'`. -/
theorem exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform
    (K : Type*) [Field K] [NumberField K] (c : ℕ) [NeZero c] (S : Subgroup (ZMod c)ˣ)
    (hF : ∀ χ : S →* ℂˣ, χ ≠ 1 →
      Filter.Tendsto (fun N : ℕ => (∑ s : S, ((χ s : ℂˣ) : ℂ) *
          (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = ((s : (ZMod c)ˣ) : ZMod c)} : ℂ))
          / (N : ℂ))
        Filter.atTop (nhds 0)) :
    ∃ κ C' : ℝ, ∀ a ∈ S, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = (a : ZMod c)} : ℝ)
          - κ * N|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  -- Per-residue effective constants and the per-residue density (limit of `count / N`).
  choose κf C'f hκf using exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le K c
  choose κlim hκlim using exists_tendsto_cardNormLeResidue_div K c
  -- The leading constant for residue `a` is its density.
  have hκfeq : ∀ a : ZMod c, κf a = κlim a := fun a =>
    tendsto_nhds_unique
      (tendsto_div_atTop_of_sub_mul_rpow_le Module.finrank_pos (fun N hN => hκf a N hN)) (hκlim a)
  refine ⟨κlim ((1 : (ZMod c)ˣ) : ZMod c), ∑ b : ZMod c, |C'f b|, fun a ha N hN => ?_⟩
  -- Constancy of the density over `S`: `κlim a = κlim 1`.
  have hconst : κlim ((a : (ZMod c)ˣ) : ZMod c) = κlim ((1 : (ZMod c)ˣ) : ZMod c) :=
    cardNormLeResidue_density_eq_of_mem_subgroup hF ha (one_mem S)
      (hκlim ((a : (ZMod c)ˣ) : ZMod c)) (hκlim ((1 : (ZMod c)ˣ) : ZMod c))
  rw [← hconst, ← hκfeq ((a : (ZMod c)ˣ) : ZMod c)]
  -- Reduce to the per-residue effective bound and dominate the error constant.
  refine (hκf ((a : (ZMod c)ˣ) : ZMod c) N hN).trans
    (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  exact (le_abs_self _).trans (Finset.single_le_sum
    (f := fun b => |C'f b|) (fun b _ => abs_nonneg _) (Finset.mem_univ _))

/-! ### Realizer-driven Fourier decay (the `hF` producer) -/

/-- **Row orthogonality** for a finite commutative group `G`: for a nontrivial character
`χ : G →* ℂˣ`, the sum of `χ g` over all `g : G` vanishes. A separating element `g₀` with
`χ g₀ ≠ 1` exists (else `χ = 1`); reindexing the sum by left translation with `g₀` scales it by
`χ g₀`, forcing it to vanish. This is the companion of the column orthogonality
`sum_char_apply_eq_zero_of_ne_one`. -/
private theorem sum_char_self_eq_zero_of_ne_one {G : Type*} [CommGroup G] [Finite G] [Fintype G]
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

/-! ### Per-class densities and the realizer transfer (Lang VI §3 Thm 3)

The honest proof of κ-constancy over the realized subgroup `S` (Lang, *Algebraic Number Theory*
GTM 110, Ch. VI §3, Thm 3) is *not* the lossy multiply-by-`𝔟`-and-sandwich argument (which only
gives `κ_a ≤ N(𝔟)·κ_{a·t}`). It goes through the **per-class** densities. We isolate the single
irreducible geometric fact — the per-class realizer transfer — and assemble the global statement
around it cleanly:

* `cardNormLeResidueClass` / `exists_tendsto_cardNormLeResidueClass_div` — the per-class count and
  its density `κ_{C,y} = lim #{N(I) ≤ N, N(I) ≡ y, [I] = C}/N`.
* `tendsto_cardNormLeResidue_div_eq_sum_class` — the density splits over the class group,
  `κ_y = ∑_C κ_{C,y}` (from `card_norm_le_residue_eq_sum_class`).
* `cardNormLeResidueClass_density_transfer` — **the geometric heart**: for a realizer `𝔟` of a
  unit `u = N(𝔟) mod c`, the per-class density transfers as `κ_{C,x} = κ_{C·[𝔟], x·u}`. Proof:
  the norm-multiplying bijection `I ↦ 𝔟·I` gives the exact identity
  `#{[I]=C, N(I)≡x, N(I)≤M} = #{[J]=C·[𝔟], N(J)≡x·u, 𝔟∣J, N(J)≤M·N(𝔟)}` (Route A); the
  `𝔟`-divisible class-`C·[𝔟]` density is `1/N(𝔟)` of the full class-`C·[𝔟]` density at the same
  residue (Route B, the Lang covolume/CRT equidistribution `cardNormLeResidueClass_div_density`),
  so the `N(𝔟)`-factors cancel.
* `cardNormLeResidue_density_const_of_realized` — the global statement: sum the transfer over the
  class group and reindex by `Equiv.mulRight [𝔟]`.
-/

open Ideal in
/-- **Per-class norm-residue count.** The number of nonzero integral ideals of `𝓞 K` of norm `≤ N`,
norm residue `y (mod c)`, and ideal class `C`. -/
private def cardNormLeResidueClass {K : Type*} [Field K] [NumberField K] (c : ℕ) (y : ZMod c)
    (C : ClassGroup (𝓞 K)) (N : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
    ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = y) ∧ ClassGroup.mk0 I = C}

/-- The per-class density `κ_{C,y} = lim #{N(I) ≤ N, N(I) ≡ y, [I] = C}/N` exists, as the leading
constant of the per-class effective estimate `exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`
(via `tendsto_div_atTop_of_sub_mul_rpow_le`). -/
private theorem exists_tendsto_cardNormLeResidueClass_div {K : Type*} [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (y : ZMod c) (C : ClassGroup (𝓞 K)) :
    ∃ κ : ℝ, Filter.Tendsto (fun N : ℕ => (cardNormLeResidueClass c y C N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ) := by
  obtain ⟨κ, C', hκ⟩ := exists_card_norm_le_residue_class_eq_sub_mul_rpow_le (K := K) c y C
  exact ⟨κ, tendsto_div_atTop_of_sub_mul_rpow_le Module.finrank_pos (fun N hN => hκ N hN)⟩

open Ideal in
/-- **The norm-residue density splits over the class group.** `κ_y = ∑_C κ_{C,y}`: the count
`cardNormLeResidue` is the finite sum of the per-class counts (`card_norm_le_residue_eq_sum_class`),
so its density (where it exists) is the sum of the per-class densities. -/
private theorem tendsto_cardNormLeResidue_div_eq_sum_class {K : Type*} [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (y : ZMod c) {κ : ℝ}
    (hκ : Filter.Tendsto (fun N : ℕ => (cardNormLeResidue K c y N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ))
    (κf : ClassGroup (𝓞 K) → ℝ)
    (hκf : ∀ C, Filter.Tendsto (fun N : ℕ => (cardNormLeResidueClass c y C N : ℝ) / (N : ℝ))
      Filter.atTop (nhds (κf C))) :
    κ = ∑ C : ClassGroup (𝓞 K), κf C := by
  refine tendsto_nhds_unique hκ ?_
  have hsum := tendsto_finsetSum Finset.univ fun C (_ : C ∈ Finset.univ) => hκf C
  refine hsum.congr fun N => ?_
  rw [cardNormLeResidue, card_norm_le_residue_eq_sum_class c y N, Nat.cast_sum, Finset.sum_div]
  rfl

open Ideal in
/-- **`𝔟`-divisible per-class norm-residue count.** The number of nonzero integral ideals of
`𝓞 K` divisible by `𝔟`, of norm `≤ N`, norm residue `y (mod c)`, and ideal class `D`. -/
private def cardNormLeResidueClassDvd {K : Type*} [Field K] [NumberField K] (c : ℕ)
    (𝔟 : (Ideal (𝓞 K))⁰) (y : ZMod c) (D : ClassGroup (𝓞 K)) (N : ℕ) : ℕ :=
  Nat.card {J : (Ideal (𝓞 K))⁰ // (𝔟 : Ideal (𝓞 K)) ∣ (J : Ideal (𝓞 K)) ∧
    ((Ideal.absNorm (J : Ideal (𝓞 K)) ≤ N ∧
      ((Ideal.absNorm (J : Ideal (𝓞 K)) : ZMod c)) = y) ∧ ClassGroup.mk0 J = D)}

open Ideal in
/-- **Route A (the norm-multiplying bijection, exact).** Multiplication by `𝔟` is a bijection from
class-`C` ideals of norm `≤ N` and residue `x` onto the `𝔟`-divisible class-`C·[𝔟]` ideals of norm
`≤ N·N(𝔟)` and residue `x·N(𝔟)`. (`N(𝔟) (mod c)` is a unit so the residue condition transports both
ways; the norm scales by `N(𝔟)`, the class by `[𝔟]`, and `𝔟 ∣ 𝔟·I` is automatic.) -/
private theorem cardNormLeResidueClass_eq_dvd {K : Type*} [Field K] [NumberField K] (c : ℕ)
    [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰)
    (hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)))
    (x : ZMod c) (C : ClassGroup (𝓞 K)) (N : ℕ) :
    cardNormLeResidueClass c x C N =
      cardNormLeResidueClassDvd c 𝔟 (x * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c))
        (C * ClassGroup.mk0 𝔟) (N * Ideal.absNorm (𝔟 : Ideal (𝓞 K))) := by
  classical
  have hNb : 0 < Ideal.absNorm (𝔟 : Ideal (𝓞 K)) := absNorm_pos_of_nonZeroDivisors 𝔟
  rw [cardNormLeResidueClass, cardNormLeResidueClassDvd]
  simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
  refine Nat.card_congr
    (((Equiv.dvd 𝔟).subtypeEquiv (fun I => ?_)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun J : (Ideal (𝓞 K))⁰ ↦ 𝔟 ∣ J) _))
  -- predicate correspondence under `I ↦ 𝔟 · I`
  have hnorm : absNorm (((Equiv.dvd 𝔟) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
      = absNorm (𝔟 : Ideal (𝓞 K)) * absNorm (I : Ideal (𝓞 K)) := by
    simp_rw [Equiv.dvd_apply, Submonoid.coe_mul, _root_.map_mul]
  have hcls : ClassGroup.mk0 ((Equiv.dvd 𝔟) I) = ClassGroup.mk0 I * ClassGroup.mk0 𝔟 := by
    rw [Equiv.dvd_apply, map_mul, mul_comm]
  -- norm `≤`
  have hle : (absNorm (((Equiv.dvd 𝔟) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ≤
      N * absNorm (𝔟 : Ideal (𝓞 K))) ↔ (absNorm (I : Ideal (𝓞 K)) ≤ N) := by
    rw [hnorm, mul_comm (absNorm (𝔟 : Ideal (𝓞 K))) (absNorm (I : Ideal (𝓞 K))),
      Nat.mul_le_mul_right_iff hNb]
  -- residue
  have hres : (((absNorm (I : Ideal (𝓞 K)) : ZMod c)) = x) ↔
      (((absNorm (((Equiv.dvd 𝔟) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ZMod c)) =
        x * (absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) := by
    rw [hnorm, Nat.cast_mul, mul_comm ((absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c))
      ((absNorm (I : Ideal (𝓞 K)) : ZMod c)), hu.mul_left_inj]
  -- class
  have hcl : (ClassGroup.mk0 I = C) ↔
      (ClassGroup.mk0 ((Equiv.dvd 𝔟) I) = C * ClassGroup.mk0 𝔟) := by
    rw [hcls, mul_left_inj]
  rw [← hle, ← hres, ← hcl]

open Ideal in
/-- **Route B (the Lang covolume / CRT equidistribution).** For a realizer `𝔟` with `N(𝔟) (mod c)`
a unit, the `𝔟`-divisible class-`D` norm-residue density is `1/N(𝔟)` of the full class-`D` density
at the same residue: `κ^{÷𝔟}_{D,y}·N(𝔟) = κ_{D,y}`.

Geometric content (the single irreducible fact of `IdealCongruenceCount`, Lang, *Algebraic Number
Theory* GTM 110, Ch. VI §3, Thm 3; Gun–Ramaré–Sivaraman, JNT 243 (2023), Thm 1). Principalize the
class-`D` ideals at a representative `J` of `D⁻¹` **chosen coprime to `𝔟`** (every ideal class
contains a representative coprime to a given ideal, by prime avoidance / CRT in the Dedekind domain
`𝓞 K`). The full count becomes principal ideals `(g)` with `J ∣ (g)`, norm `≤ X·N(J)`, norm
`≡ y·N(J) (mod c·N(J))`; the `𝔟`-divisible count adds `𝔟 ∣ (g)·J⁻¹ ⟺ g ∈ 𝔟J` (since `J` is
coprime to `𝔟`), i.e. the generator lies in the index-`N(𝔟)` sublattice `𝔟J ⊆ J` of the ideal
lattice. By `gcd(N(𝔟), c·N(J)) = 1` (`N(𝔟)` is a unit mod `c`, and `N(J)` coprime to `N(𝔟)` from
the coprime rep), the norm-residue selector mod `c·N(J)` and the `𝔟J`-coset mod `N(𝔟)` are
CRT-independent, so the selector is equidistributed across the `N(𝔟)` cosets of `𝔟J` in `J`. Hence
the `𝔟`-divisible cone-point count is `1/N(𝔟)` of the full one (the per-`(orthant, coset)` cell
densities of `exists_card_idealSet_residue_le` are translate-uniform — `vol(D₀ ∩ orthant)/|det T'|`,
independent of the coset — so the equidistributed selector gives exactly the covolume ratio
`covol(J)/covol(𝔟J) = 1/N(𝔟)`).

This is the **one** fact the elementary κ-transfer cannot reach (there is no norm-preserving
residue-shifting ideal map; multiplication by `𝔟` only gives the lossy `κ_a ≤ N(𝔟)·κ_{a·t}`). All
of `IdealCongruenceCount`'s remaining structure — Route A (`cardNormLeResidueClass_eq_dvd`), the
limit glue, the class-group reindexing — is proven around it. -/
private theorem cardNormLeResidueClass_div_density {K : Type*} [Field K] [NumberField K] (c : ℕ)
    [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰)
    (hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)))
    (y : ZMod c) (D : ClassGroup (𝓞 K)) {κfull : ℝ}
    (hκfull : Filter.Tendsto (fun N : ℕ => (cardNormLeResidueClass c y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κfull)) :
    Filter.Tendsto (fun N : ℕ => (cardNormLeResidueClassDvd c 𝔟 y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds (κfull / (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℝ))) := by
  sorry

open Ideal in
/-- **Per-class realizer transfer (the geometric heart, Lang VI §3 Thm 3).** For a fixed nonzero
ideal `𝔟` whose norm residue `N(𝔟) (mod c)` is a unit, the per-class norm-residue density
transfers along multiplication by `[𝔟]`:
`κ_{C,x} = κ_{C·[𝔟], x·N(𝔟)}` (both densities limits of `count/N`).

Proof (the two routes whose `N(𝔟)`-factors cancel). **Route A** (`cardNormLeResidueClass_eq_dvd`,
the norm-multiplying bijection, exact): `I ↦ 𝔟·I` is a bijection
`{[I]=C, N(I)≡x, N(I)≤M} ≃ {[J]=C·[𝔟], 𝔟∣J, N(J)≡x·N(𝔟), N(J)≤M·N(𝔟)}`, so
`κ_{C,x} = N(𝔟)·κ^{÷𝔟}_{C·[𝔟], x·N(𝔟)}` where `κ^{÷𝔟}` is the `𝔟`-divisible density. **Route B**
(`cardNormLeResidueClass_div_density`): `κ^{÷𝔟}_{C·[𝔟], y}·N(𝔟) = κ_{C·[𝔟], y}`. Cancel `N(𝔟)`. -/
private theorem cardNormLeResidueClass_density_transfer {K : Type*} [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰)
    (hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)))
    (x : ZMod c) (C : ClassGroup (𝓞 K)) {κ κ' : ℝ}
    (hκ : Filter.Tendsto (fun N : ℕ => (cardNormLeResidueClass c x C N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ))
    (hκ' : Filter.Tendsto (fun N : ℕ => (cardNormLeResidueClass c
        (x * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) (C * ClassGroup.mk0 𝔟) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ')) :
    κ = κ' := by
  classical
  set NB : ℕ := Ideal.absNorm (𝔟 : Ideal (𝓞 K)) with hNBdef
  have hNB : 0 < NB := absNorm_pos_of_nonZeroDivisors 𝔟
  have hNB0 : (NB : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNB.ne'
  set y : ZMod c := x * (NB : ZMod c) with hy
  set D : ClassGroup (𝓞 K) := C * ClassGroup.mk0 𝔟 with hD
  -- Route B: the `𝔟`-divisible density is `κ'/NB`.
  have hκd : Filter.Tendsto (fun N : ℕ => (cardNormLeResidueClassDvd c 𝔟 y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds (κ' / (NB : ℝ))) := cardNormLeResidueClass_div_density c 𝔟 hu y D hκ'
  -- Route A as a limit: `cardNormLeResidueClass x C M / M = NB · (Dvd (M·NB) / (M·NB))`.
  have hAlim : Filter.Tendsto
      (fun M : ℕ => (cardNormLeResidueClass c x C M : ℝ) / (M : ℝ))
      Filter.atTop (nhds ((NB : ℝ) * (κ' / (NB : ℝ)))) := by
    have hcomp : Filter.Tendsto (fun M : ℕ => M * NB) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun M => Nat.le_mul_of_pos_right M hNB) Filter.tendsto_id
    have hd2 : Filter.Tendsto
        (fun M : ℕ => (cardNormLeResidueClassDvd c 𝔟 y D (M * NB) : ℝ) / ((M * NB : ℕ) : ℝ))
        Filter.atTop (nhds (κ' / (NB : ℝ))) := hκd.comp hcomp
    refine (hd2.const_mul (NB : ℝ)).congr fun M => ?_
    rw [cardNormLeResidueClass_eq_dvd c 𝔟 hu x C M, ← hy, ← hD]
    rcases Nat.eq_zero_or_pos M with hM0 | hMpos
    · simp [hM0]
    · have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hMpos.ne'
      rw [Nat.cast_mul]
      field_simp
      ring
  rw [tendsto_nhds_unique hκ hAlim, mul_div_cancel₀ _ hNB0]

open Ideal in
/-- **Global realizer transfer.** Summing the per-class transfer over the class group (reindexing
by `Equiv.mulRight [𝔟]`): for a realizer `𝔟` with `N(𝔟) (mod c)` a unit, `κ_x = κ_{x·N(𝔟)}`, the
densities of `cardNormLeResidue` at residues `x` and `x·N(𝔟)`. -/
private theorem cardNormLeResidue_density_transfer {K : Type*} [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰)
    (hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)))
    (x : ZMod c) {κ κ' : ℝ}
    (hκ : Filter.Tendsto (fun N : ℕ => (cardNormLeResidue K c x N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ))
    (hκ' : Filter.Tendsto (fun N : ℕ => (cardNormLeResidue K c
        (x * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ')) :
    κ = κ' := by
  classical
  -- Per-class densities for both residues.
  choose κf hκf using fun C => exists_tendsto_cardNormLeResidueClass_div (K := K) c x C
  choose κf' hκf' using fun C =>
    exists_tendsto_cardNormLeResidueClass_div (K := K) c
      (x * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) C
  -- `κ = ∑_C κf C`, `κ' = ∑_C κf' C`.
  have hsplit : κ = ∑ C : ClassGroup (𝓞 K), κf C :=
    tendsto_cardNormLeResidue_div_eq_sum_class c x hκ κf hκf
  have hsplit' : κ' = ∑ C : ClassGroup (𝓞 K), κf' C :=
    tendsto_cardNormLeResidue_div_eq_sum_class c
      (x * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) hκ' κf' hκf'
  -- Per-class transfer: `κf C = κf' (C·[𝔟])`.
  have htrans : ∀ C : ClassGroup (𝓞 K), κf C = κf' (C * ClassGroup.mk0 𝔟) := fun C =>
    cardNormLeResidueClass_density_transfer c 𝔟 hu x C (hκf C) (hκf' (C * ClassGroup.mk0 𝔟))
  rw [hsplit, hsplit']
  rw [Finset.sum_congr rfl fun C _ => htrans C]
  exact Equiv.sum_comp (Equiv.mulRight (ClassGroup.mk0 𝔟)) κf'

open scoped Classical in
/-- **κ-constancy over the realized-residue subgroup (Lang VI §3 Thm 3).** If `a, a'` lie in a
subgroup `S ≤ (ℤ/c)ˣ` *all of whose elements are realized as ideal-norm residues* (`hS`), then the
per-residue ideal densities of `a` and `a'` coincide: `κ = κ'`.

This is the geometry-of-numbers heart of the abelian Chebotarev step, the per-ray-class ideal
count with class-independent leading constant (Lang, *Algebraic Number Theory* GTM 110, Ch. VI §3,
Thm 3; equivalently Gun–Ramaré–Sivaraman, *Counting ideals in ray classes*, JNT 243 (2023), Thm 1).

The statement is **true** and is the converse direction of the in-file Fourier dictionary
`cardNormLeResidue_density_eq_of_mem_subgroup` (which derives κ-constancy *from* the Fourier-decay
hypothesis `hF`). It is what `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized` consumes to
*produce* `hF`. The proof exposes the leading constants of the opaque-`κ` cell estimates built
above (`exists_card_idealSet_residue_le`): writing
`κ_a = ∑_C (N(J_C)·vol(D₀ ∩ orthant_s)/|det T_{m_C}|)·#{qualifying cells for a}`, two facts close
it. (i) *Orthant volume symmetry*: `vol(D₀ ∩ orthant_s)` is independent of the sign pattern `s`,
because
`negAt s` (mathlib `volume_preserving_negAt`, `norm_negAt`) is a volume- and norm-preserving
involution carrying orthant `∅` to orthant `s` inside `normLeOne K`; combined with the Lang
covolume cancellation `|det T_{m_C}| = m_C^d · N(J_C) · 2^{-r₂}√|discr|`
(`NumberField.mixedEmbedding.covolume_idealLattice`) each cell contributes the same universal
`κ₀ = vol(D₀)/(2^{r₁} c^d 2^{-r₂}√|discr|)`. (ii) *Equinumerosity of qualifying cells across `S`*:
multiplication by an element of `(𝓞/m_C)ˣ` of signed norm-residue `t = a'·a⁻¹` permutes the cells
and shifts the residue selector by `t` (the in-file `natCast_algebraNorm_add_nsmul_mul` /
`norm_zmod_eq_of_emb_sub_mem` congruence), so the qualifying-cell counts for `a` and `a'` agree once
`t ∈ S` is realized — which `hS` supplies. -/
private theorem cardNormLeResidue_density_const_of_realized
    {K : Type*} [Field K] [NumberField K] {c : ℕ} [NeZero c] {S : Subgroup (ZMod c)ˣ}
    (hS : ∀ a ∈ S, ∃ 𝔟 : (Ideal (𝓞 K))⁰,
      ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) = (a : ZMod c))
    {a a' : (ZMod c)ˣ} (ha : a ∈ S) (ha' : a' ∈ S) {κ κ' : ℝ}
    (hκ : Filter.Tendsto (fun N : ℕ => (cardNormLeResidue K c (a : ZMod c) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ))
    (hκ' : Filter.Tendsto (fun N : ℕ => (cardNormLeResidue K c (a' : ZMod c) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ')) :
    κ = κ' := by
  classical
  -- Realizers of `a` and `a'` (their norm residues are the units `↑a`, `↑a'`).
  obtain ⟨𝔟, h𝔟⟩ := hS a ha
  obtain ⟨𝔟', h𝔟'⟩ := hS a' ha'
  have hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) := h𝔟 ▸ a.isUnit
  have hu' : IsUnit ((Ideal.absNorm (𝔟' : Ideal (𝓞 K)) : ZMod c)) := h𝔟' ▸ a'.isUnit
  -- The density at residue `1`.
  obtain ⟨κ₁, hκ₁⟩ := exists_tendsto_cardNormLeResidue_div K c (1 : ZMod c)
  -- Transfer `1 → 1·N(𝔟) = ↑a` gives `κ₁ = κ`; similarly `κ₁ = κ'`.
  have hone_eq : (1 : ZMod c) * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c) = (a : ZMod c) := by
    rw [one_mul, h𝔟]
  have hone_eq' : (1 : ZMod c) * (Ideal.absNorm (𝔟' : Ideal (𝓞 K)) : ZMod c) = (a' : ZMod c) := by
    rw [one_mul, h𝔟']
  have hκ_a : Filter.Tendsto (fun N : ℕ => (cardNormLeResidue K c
      ((1 : ZMod c) * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ) := by rw [hone_eq]; exact hκ
  have hκ_a' : Filter.Tendsto (fun N : ℕ => (cardNormLeResidue K c
      ((1 : ZMod c) * (Ideal.absNorm (𝔟' : Ideal (𝓞 K)) : ZMod c)) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ') := by rw [hone_eq']; exact hκ'
  have h1 : κ₁ = κ := cardNormLeResidue_density_transfer c 𝔟 hu (1 : ZMod c) hκ₁ hκ_a
  have h2 : κ₁ = κ' := cardNormLeResidue_density_transfer c 𝔟' hu' (1 : ZMod c) hκ₁ hκ_a'
  rw [← h1, h2]

open scoped Classical in
/-- **Fourier decay from realized residues (the `hF` producer).** Let `S ≤ (ℤ/c)ˣ` be a subgroup
all of whose elements are realized as ideal-norm residues (`hS`). Then for every **nontrivial**
character `χ` of `S`, the `χ`-twisted norm-residue count average over `S` tends to `0`:

`(∑_{s ∈ S} χ(s)·#{N(I) ≤ N, N(I) ≡ s}) / N → 0`.

This is exactly the Fourier-decay hypothesis `hF` consumed by
`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform` (and by
`cardNormLeResidue_density_eq_of_mem_subgroup`): when the consumer's `S` is the full image
subgroup of ideal-norm residues, `hS` holds tautologically, so this theorem discharges its `hF`
and hands back the `κ`-uniform effective ideal count. (The avoidance of the `ℚ(i)`-trap is built
in: realization, hence decay, is asserted only over the **image subgroup** `S`, never over all of
`(ℤ/c)ˣ`.)

Proof: each per-residue count has a density `κ_s = lim #{N(I) ≤ N, N(I) ≡ s}/N`
(`exists_tendsto_cardNormLeResidue_div`), and the realizer hypothesis makes these densities
constant on `S` (`cardNormLeResidue_density_const_of_realized`, Lang VI §3 Thm 3). Hence the
twisted average tends to `(∑_{s ∈ S} χ(s))·κ`, which vanishes by row orthogonality
`sum_char_self_eq_zero_of_ne_one` for the nontrivial `χ`. -/
theorem tendsto_sum_char_mul_cardNormLeResidue_div_of_realized
    (K : Type*) [Field K] [NumberField K] (c : ℕ) [NeZero c] (S : Subgroup (ZMod c)ˣ)
    (hS : ∀ a ∈ S, ∃ 𝔟 : (Ideal (𝓞 K))⁰,
      ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) = (a : ZMod c))
    (χ : S →* ℂˣ) (hχ : χ ≠ 1) :
    Filter.Tendsto (fun N : ℕ => (∑ s : S, ((χ s : ℂˣ) : ℂ) *
        (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = ((s : (ZMod c)ˣ) : ZMod c)} : ℂ))
        / (N : ℂ))
      Filter.atTop (nhds 0) := by
  classical
  -- Per-residue densities `κf s = lim count_s / N`.
  choose κf hκf using fun s : S =>
    exists_tendsto_cardNormLeResidue_div K c ((s : (ZMod c)ˣ) : ZMod c)
  -- All densities over `S` are equal (Lang VI §3 Thm 3 via the realizer hypothesis).
  have hconst : ∀ s : S, κf s = κf 1 := fun s =>
    cardNormLeResidue_density_const_of_realized hS s.2 (one_mem S) (hκf s) (hκf 1)
  -- The twisted average tends to `(∑_{s} χ s)·κf 1`.
  have hlim : Filter.Tendsto (fun N : ℕ => (∑ s : S, ((χ s : ℂˣ) : ℂ) *
        (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = ((s : (ZMod c)ˣ) : ZMod c)} : ℂ))
        / (N : ℂ))
      Filter.atTop (nhds (∑ s : S, ((χ s : ℂˣ) : ℂ) * (κf s : ℂ))) := by
    have hsum := tendsto_finsetSum Finset.univ fun s (_ : s ∈ Finset.univ) =>
      ((Complex.continuous_ofReal.tendsto (κf s)).comp (hκf s)).const_mul ((χ s : ℂˣ) : ℂ)
    refine hsum.congr fun N => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Function.comp_apply, cardNormLeResidue]
    push_cast
    ring
  -- The limiting value vanishes: factor out the common density, use row orthogonality.
  have hval : (∑ s : S, ((χ s : ℂˣ) : ℂ) * (κf s : ℂ)) = 0 := by
    have hrw : (∑ s : S, ((χ s : ℂˣ) : ℂ) * (κf s : ℂ))
        = (∑ s : S, ((χ s : ℂˣ) : ℂ)) * (κf 1 : ℂ) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hconst s]
    rw [hrw, sum_char_self_eq_zero_of_ne_one hχ, zero_mul]
  rw [hval] at hlim
  exact hlim

end Chebotarev
