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
