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

/-! ### The per-residue effective ideal count -/

open Ideal in
open Ideal NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone in
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
  sorry

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
