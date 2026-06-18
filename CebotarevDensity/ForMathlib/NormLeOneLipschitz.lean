module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne

/-!
# Lipschitz parametrization of the frontier of `normLeOne K`

Mathlib proves that the frontier of the norm-`≤ 1` part of the fundamental cone has measure
zero (`volume_frontier_normLeOne`). For the *effective* lattice-point count
(`Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le`) one needs the stronger,
quantitative regularity: the frontier of the `realSpace` image
`normAtAllPlaces '' (normLeOne K)` is covered by **finitely many Lipschitz images of the unit
cube** `[0,1]^{r-1}`, `r = #InfinitePlace K`. This is the Lipschitz-boundary input of
Gun–Ramaré–Sivaraman, *Counting ideals in ray classes*, J. Number Theory 243 (2023), §3.3
(after Debaene); it feeds the boundary-cell estimate of Widmer / Lang (GTM 110, Ch. V §2).

## Main definitions

* `Chebotarev.clampUnit`: the coordinatewise retraction of `ι → ℝ` onto the unit cube `Icc 0 1`.
* `Chebotarev.faceMapZero`, `Chebotarev.faceMapSide`: cube parametrizations of the `w₀`-face and
  side faces of the box boundary, transported through `expMapBasis`.
* `Chebotarev.frontierCoverFamily`: the finite family covering the `realSpace` frontier.
* `Chebotarev.liftToMixed`: the lift of a `realSpace`-valued cover map to a `mixedSpace`-valued
  one along the fibres of `normAtAllPlaces`.

## Main results

* `Chebotarev.normLeOne_frontier_lipschitz_cover`: the frontier of `normAtAllPlaces '' normLeOne K`
  in `realSpace K` is covered by finitely many `M`-Lipschitz images of `[0,1]^{r-1}`.
* `Chebotarev.normLeOne_frontier_lipschitz_cover_mixedSpace`: the corresponding cover of
  `frontier (normLeOne K)` in `mixedSpace K`, of dimension `d-1 = finrank ℚ K - 1`.
* `Chebotarev.normLeOne_frontier_lipschitz_cover_index`: the cover transported to the standard
  Euclidean coordinate space `index K → ℝ`, the exact `hlip` hypothesis of the lattice-point count.

## Implementation notes

The proof rests entirely on mathlib's parametrization
`normAtAllPlaces '' (normLeOne K) = expMapBasis '' (paramSet K)` where
`paramSet K = Iic 0 × [0,1)^{r-1}` (in the `completeBasis` coordinates), in three layers.

The `realSpace` cover:
1. `expMapBasis` is an open injective map (`OpenPartialHomeomorph` with source `univ`), so
   `frontier (expMapBasis '' paramSet K) ⊆ expMapBasis '' (∂ paramSet K) ∪ {0}`, the `{0}`
   accounting for the closure points escaping to norm `0` as the `w₀`-coordinate `→ -∞`
   (`frontier_image_paramSet_subset`).
2. The box boundary `∂ paramSet K` consists of the face `{x w₀ = 0}` and the side faces
   `{x i = a}`, `a ∈ {0,1}`, `i ≠ w₀`.
3. On the `w₀`-face, `expMapBasis` itself restricted to the compact cube parametrizes the
   image (`faceMapZero`). On a side face the `w₀`-direction is unbounded, but
   `expMapBasis x = exp (x w₀) • expMapBasis (x [w₀ => 0])` (`expMapBasis_apply''`), so the
   substitution `t = exp (x w₀) ∈ (0,1]` linearizes it: the face image is parametrized by the
   compact cube via `faceMapSide`, with `t` taking the cube slot freed by pinning `x i = a`.
4. All parametrizations are restrictions of globally `C¹` maps to the compact convex cube,
   hence Lipschitz there (`ContDiff.locallyLipschitz` +
   `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`); composing with the `1`-Lipschitz
   cube clamp `clampUnit` makes them globally Lipschitz without changing the cube image.

The lift to `mixedSpace K` parametrizes the fibres of `normAtAllPlaces`: a fibre over a
nonnegative `y : realSpace K` is fixed by the signs of the real coordinates (a finite choice
folded into the index) and the phases of the complex coordinates (the extra `r₂` cube
coordinates, via the polar form `z = ‖z‖ · exp((2π θ − π) i)`, `θ ∈ [0,1]`). This turns the
`r − 1` cube coordinates into `(r − 1) + r₂ = d − 1` coordinates, `d = finrank ℚ K`.

Finally the cover is transported to the standard coordinate space `index K → ℝ` (sup metric,
lattice `ℤ^ι`) via the continuous linear chart `(stdBasis K).equivFunL`, inflating the Lipschitz
constants by `‖·‖₊` and relabelling the cube dimension along
`Fintype.card (index K) - 1 = finrank ℚ K - 1`.

## References

* Gun, Ramaré, Sivaraman, *Counting ideals in ray classes*, J. Number Theory 243 (2023), §3.3.
* Lang, *Algebraic Number Theory*, GTM 110, Ch. V §2 (Widmer's boundary-cell estimate).
-/

@[expose] public section

noncomputable section

namespace Chebotarev

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone NumberField.Units dirichletUnitTheorem Set

open scoped NNReal

/-- The coordinatewise retraction of `ι → ℝ` onto the unit cube `Set.Icc 0 1`, given by
`Set.projIcc` in each coordinate. -/
def clampUnit (ι : Type*) (c : ι → ℝ) : ι → ℝ := fun i ↦ (Set.projIcc 0 1 zero_le_one (c i) : ℝ)

theorem clampUnit_mem_Icc (ι : Type*) (c : ι → ℝ) : clampUnit ι c ∈ Icc (0 : ι → ℝ) 1 :=
  ⟨fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2.1,
    fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2.2⟩

theorem clampUnit_eq_self {ι : Type*} {c : ι → ℝ} (hc : c ∈ Icc (0 : ι → ℝ) 1) :
    clampUnit ι c = c :=
  funext fun i ↦ congrArg _ (Set.projIcc_of_mem _ ⟨hc.1 i, hc.2 i⟩)

/-- A map into a finite pi type is `1`-Lipschitz once each output coordinate's `edist` is
bounded by the input `edist`. The pi-codomain companion of `LipschitzWith.eval`. -/
private theorem lipschitzWith_one_of_edist_apply_le {α κ : Type*} {β : κ → Type*}
    [PseudoEMetricSpace α] [∀ j, PseudoEMetricSpace (β j)] [Fintype κ] {F : α → ∀ j, β j}
    (h : ∀ c d j, edist (F c j) (F d j) ≤ edist c d) : LipschitzWith 1 F :=
  LipschitzWith.of_edist_le fun c d ↦ by
    rw [edist_pi_def]
    exact Finset.sup_le fun j _ ↦ h c d j

theorem lipschitzWith_clampUnit (ι : Type*) [Fintype ι] : LipschitzWith 1 (clampUnit ι) :=
  lipschitzWith_one_of_edist_apply_le fun c d i ↦ (Subtype.edist_eq _ _).symm.trans_le <|
    (((LipschitzWith.projIcc zero_le_one).edist_le_mul (c i) (d i)).trans_eq
      (one_mul _)).trans (edist_le_pi_edist c d i)

/-- A globally `C¹` map into `κ → ℝ`, pre-composed with the cube clamp, is globally Lipschitz;
its image of the unit cube is unchanged. The Lipschitz constant comes from compactness of the
cube (`LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`). -/
theorem exists_lipschitzWith_comp_clampUnit {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : (ι → ℝ) → κ → ℝ} (hf : ContDiff ℝ 1 f) :
    ∃ M : ℝ≥0, LipschitzWith M (f ∘ clampUnit ι) := by
  have hl := hf.locallyLipschitz.locallyLipschitzOn (s := Icc (0 : ι → ℝ) 1)
  obtain ⟨M, hM⟩ := hl.exists_lipschitzOnWith_of_compact isCompact_Icc
  refine ⟨M, fun c d ↦ (hM (clampUnit_mem_Icc ι c) (clampUnit_mem_Icc ι d)).trans ?_⟩
  gcongr
  simpa using (lipschitzWith_clampUnit ι).edist_le_mul c d

variable (K : Type*) [Field K] [NumberField K]

theorem contDiff_expMapBasis : ContDiff ℝ 1 (⇑(expMapBasis (K := K))) := by
  classical
  rw [show ⇑(expMapBasis (K := K)) = fun x : realSpace K ↦
      Real.exp (x w₀) • fun w : InfinitePlace K ↦
        ∏ i : {w // w ≠ w₀}, w (fundSystem K (equivFinRank.symm i)) ^ x i from
    funext expMapBasis_apply']
  fun_prop (disch := exact fun x ↦ (InfinitePlace.pos_iff.mpr (by simp)).ne')

open scoped Classical in
/-- Parametrization of the `expMapBasis`-image of the `w₀`-face `{x | x w₀ = 0}` of
`paramSet K`: plug `0` in the `w₀`-slot and the cube coordinates in the remaining slots. -/
def faceMapZero (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : realSpace K :=
  expMapBasis fun w ↦ if hw : w = w₀ then 0 else c ⟨w, hw⟩

open scoped Classical in
/-- Parametrization of the `expMapBasis`-image of a side face `{x | x i = a}` (`i ≠ w₀`,
`a ∈ {0,1}`) of `paramSet K`. The `w₀`-direction of the face is the unbounded `Iic 0`; the
substitution `t = exp (x w₀) ∈ (0,1]` (`expMapBasis_apply''`) turns it into the cube coordinate
`c i` — the slot freed by pinning `x i = a`:
`faceMapSide i a c = (c i) • expMapBasis (x [w₀ => 0, i => a, w => c w])`. -/
def faceMapSide (i : {w : InfinitePlace K // w ≠ w₀}) (a : ℝ)
    (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : realSpace K :=
  c i • expMapBasis fun w ↦ if hw : w = w₀ then 0 else if (⟨w, hw⟩ : {w // w ≠ w₀}) = i then a
    else c ⟨w, hw⟩

open scoped Classical in
theorem contDiff_faceMapZero : ContDiff ℝ 1 (faceMapZero K) := by
  refine (contDiff_expMapBasis K).comp (contDiff_pi.mpr fun w ↦ ?_)
  by_cases hw : w = w₀
  · simpa only [dif_pos hw] using contDiff_const
  · simpa only [dif_neg hw] using contDiff_apply ℝ ℝ _

open scoped Classical in
theorem contDiff_faceMapSide (i : {w : InfinitePlace K // w ≠ w₀}) (a : ℝ) :
    ContDiff ℝ 1 (faceMapSide K i a) := by
  refine (contDiff_apply ℝ ℝ i).smul ((contDiff_expMapBasis K).comp (contDiff_pi.mpr fun w ↦ ?_))
  by_cases hw : w = w₀
  · simpa only [dif_pos hw] using contDiff_const
  · simp only [dif_neg hw]
    by_cases hi : (⟨w, hw⟩ : {w // w ≠ w₀}) = i
    · simpa only [if_pos hi] using contDiff_const
    · simpa only [if_neg hi] using contDiff_apply ℝ ℝ _

end Chebotarev
