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

/-- **Topological reduction.** Since `expMapBasis` is open and injective with source `univ`,
the frontier of `expMapBasis '' paramSet K` is contained in the image of the box boundary
`closure (paramSet K) \ interior (paramSet K)`, together with `{0}` (the escape to norm `0`):
`closure (expMapBasis '' paramSet K) ⊆ compactSet K = expMapBasis '' closure (paramSet K) ∪ {0}`
while `expMapBasis '' interior (paramSet K)` is open, hence inside the interior. -/
theorem frontier_image_paramSet_subset :
    frontier (expMapBasis '' paramSet K) ⊆
      expMapBasis '' (closure (paramSet K) \ interior (paramSet K)) ∪ {0} := by
  have hcl : closure (expMapBasis '' paramSet K) ⊆ compactSet K :=
    (isCompact_compactSet K).isClosed.closure_subset_iff.mpr
      ((Set.image_mono subset_closure).trans (expMapBasis_closure_subset_compactSet K))
  have hint : expMapBasis '' interior (paramSet K) ⊆ interior (expMapBasis '' paramSet K) :=
    (expMapBasis.isOpen_image_of_subset_source isOpen_interior
      (by simp [expMapBasis_source])).subset_interior_iff.mpr (Set.image_mono interior_subset)
  refine (Set.diff_subset_diff hcl hint).trans ?_
  rw [compactSet_eq_union, Set.union_diff_distrib,
    ← Set.image_diff (injective_expMapBasis K)]
  exact Set.union_subset_union_right _ Set.diff_subset

open scoped Classical in
private theorem expMapBasis_mem_iUnion_faceMapSide
    {y : realSpace K} {w : InfinitePlace K} (hwe : w ≠ w₀) (hw₀ : y w₀ ≤ 0)
    (hIcc : ∀ v : InfinitePlace K, v ≠ w₀ → y v ∈ Icc (0 : ℝ) 1) (ha : y w = 0 ∨ y w = 1) :
    (expMapBasis y : realSpace K) ∈
      ⋃ i : {w : InfinitePlace K // w ≠ w₀}, ⋃ a ∈ ({0, 1} : Set ℝ),
        faceMapSide K i a '' Icc 0 1 := by
  set i : {w : InfinitePlace K // w ≠ w₀} := ⟨w, hwe⟩ with hi
  set c : {w : InfinitePlace K // w ≠ w₀} → ℝ :=
    fun j ↦ if j = i then Real.exp (y w₀) else y j.1 with hc
  have hcmem : c ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 := by
    refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩ <;> simp only [hc] <;> split_ifs
    · exact Real.exp_nonneg _
    · exact (hIcc j.1 j.2).1
    · exact Real.exp_le_one_iff.mpr hw₀
    · exact (hIcc j.1 j.2).2
  have hkey : faceMapSide K i (y w) c = expMapBasis y := by
    have hci : c i = Real.exp (y w₀) := by simp [hc]
    have hfun : (fun w' ↦ if hw' : w' = w₀ then (0 : ℝ) else
        if (⟨w', hw'⟩ : {w // w ≠ w₀}) = i then y w else c ⟨w', hw'⟩) =
        fun w' ↦ if w' = w₀ then 0 else y w' := by
      funext w'
      by_cases hw'₀ : w' = w₀
      · simp only [dif_pos hw'₀, if_pos hw'₀]
      · simp only [dif_neg hw'₀, if_neg hw'₀]
        by_cases hw'w : (⟨w', hw'₀⟩ : {w // w ≠ w₀}) = i
        · obtain rfl : w' = w := by rw [hi, Subtype.mk_eq_mk] at hw'w; exact hw'w
          simp only [if_pos hw'w]
        · simp only [hc, if_neg hw'w]
    rw [faceMapSide, expMapBasis_apply'' y, hci, hfun]
  refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion₂.mpr ⟨y w, ?_, ⟨c, hcmem, hkey⟩⟩⟩
  rcases ha with h | h <;> simp [h]

/-- **Face covering.** Every point of the image of the box boundary, together with `0`, lies in
a face-parametrization image of the unit cube: a boundary point has `x w₀ = 0` (the `w₀`-face,
covered by `faceMapZero`) or `x i ∈ {0,1}` for some `i ≠ w₀` (a side face, covered by
`faceMapSide i a` via `t = exp (x w₀)`); `0` itself is the `t = 0` slice of any side face, or
the value of the (degenerate, `r = 1`) zero map handled in the final assembly. -/
theorem image_boundary_subset_faces :
    expMapBasis '' (closure (paramSet K) \ interior (paramSet K)) ⊆
      faceMapZero K '' Icc 0 1 ∪
        ⋃ i : {w : InfinitePlace K // w ≠ w₀}, ⋃ a ∈ ({0, 1} : Set ℝ),
          faceMapSide K i a '' Icc 0 1 := by
  classical
  rintro _ ⟨y, ⟨hyc, hyni⟩, rfl⟩
  rw [closure_paramSet, Set.mem_univ_pi] at hyc
  rw [interior_paramSet, Set.mem_univ_pi] at hyni
  push Not at hyni
  obtain ⟨w, hw⟩ := hyni
  have hw₀ : y w₀ ≤ 0 := by simpa using hyc w₀
  have hIcc : ∀ v : InfinitePlace K, v ≠ w₀ → y v ∈ Icc (0 : ℝ) 1 := fun v hv ↦ by
    simpa [hv] using hyc v
  by_cases hwe : w = w₀
  · rw [if_pos hwe, Set.mem_Iio, not_lt, hwe] at hw
    have hy0 : y w₀ = 0 := le_antisymm hw₀ hw
    refine Or.inl ⟨fun i ↦ y i.1, ⟨fun i ↦ (hIcc i.1 i.2).1, fun i ↦ (hIcc i.1 i.2).2⟩, ?_⟩
    rw [faceMapZero]
    congr 1
    funext v
    by_cases hv : v = w₀
    · rw [dif_pos hv, hv, hy0]
    · simp only [dif_neg hv]
  · rw [if_neg hwe] at hw
    have h1 := hIcc w hwe
    rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hw
    refine Or.inr (expMapBasis_mem_iUnion_faceMapSide K hwe hw₀ hIcc ?_)
    rcases hw with h | h
    · exact Or.inl (le_antisymm h h1.1)
    · exact Or.inr (le_antisymm h1.2 h)

/-- Relabel cube coordinates `Fin (#InfinitePlace K - 1) → ℝ` by the non-distinguished places
`{w ≠ w₀}` via `equivFinRank`. -/
def cubeRelabel (c : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) :
    {w : InfinitePlace K // w ≠ w₀} → ℝ :=
  fun j ↦ c (equivFinRank.symm j)

open scoped Classical in
theorem lipschitzWith_cubeRelabel : LipschitzWith 1 (cubeRelabel K) :=
  lipschitzWith_one_of_edist_apply_le (F := cubeRelabel K)
    fun c d j ↦ edist_le_pi_edist c d (equivFinRank.symm j)

theorem cubeRelabel_mem_Icc {c : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ}
    (hc : c ∈ Icc (0 : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) 1) :
    cubeRelabel K c ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 :=
  ⟨fun _ ↦ hc.1 _, fun _ ↦ hc.2 _⟩

theorem exists_cubeRelabel_eq {c' : {w : InfinitePlace K // w ≠ w₀} → ℝ}
    (hc' : c' ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1) :
    ∃ c ∈ Icc (0 : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) 1, cubeRelabel K c = c' :=
  ⟨fun j ↦ c' (equivFinRank j), ⟨fun j ↦ hc'.1 _, fun j ↦ hc'.2 _⟩,
    funext fun j ↦ by simp [cubeRelabel]⟩

/-- The finite family covering the frontier: the zero map (index `inl ()`), the `w₀`-face map
(`inr (inl ())`), and the side-face maps `faceMapSide i a` for `i ≠ w₀`, `a ∈ {0,1}`
(`inr (inr (i, b))`, `a = if b then 1 else 0`), each post-clamped to the unit cube and relabelled
through `cubeRelabel`. -/
def frontierCoverFamily :
    (Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool)) →
      (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K :=
  Sum.elim (fun _ _ ↦ 0)
    (Sum.elim (fun _ ↦ faceMapZero K ∘ clampUnit _ ∘ cubeRelabel K)
      fun p ↦ faceMapSide K p.1 (if p.2 then 1 else 0) ∘ clampUnit _ ∘ cubeRelabel K)

/-- Every member of `frontierCoverFamily` is `M`-Lipschitz for a common constant `M`: each face
map is `C¹` on the compact cube hence Lipschitz there (`exists_lipschitzWith_comp_clampUnit`), and
pre-composing with the `1`-Lipschitz `cubeRelabel` preserves the constant; take `M` to be the
supremum over the finitely many faces. -/
theorem exists_lipschitzWith_frontierCoverFamily :
    ∃ M : ℝ≥0, ∀ s, LipschitzWith M (frontierCoverFamily K s) := by
  classical
  obtain ⟨M₀, hM₀⟩ := exists_lipschitzWith_comp_clampUnit (contDiff_faceMapZero K)
  choose Ms hMs using fun p : {w : InfinitePlace K // w ≠ w₀} × Bool ↦
    exists_lipschitzWith_comp_clampUnit (contDiff_faceMapSide K p.1 (if p.2 then 1 else 0))
  refine ⟨M₀ ⊔ Finset.univ.sup Ms, fun s ↦ ?_⟩
  rcases s with _ | _ | p
  · exact (LipschitzWith.const _).weaken zero_le
  · exact (hM₀.comp (lipschitzWith_cubeRelabel K)).weaken (by rw [mul_one]; exact le_sup_left)
  · exact ((hMs p).comp (lipschitzWith_cubeRelabel K)).weaken
      (by rw [mul_one]; exact le_sup_of_le_right (Finset.le_sup (Finset.mem_univ p)))

/-- The frontier of `normAtAllPlaces '' normLeOne K` is covered by the cube images of
`frontierCoverFamily`. The chain is: frontier → box-boundary image `∪ {0}`
(`frontier_image_paramSet_subset`) → the face images (`image_boundary_subset_faces`), then each
face image is the corresponding family member after undoing the relabelling
(`exists_cubeRelabel_eq`) and the clamp (`clampUnit_eq_self`), with `{0}` the value of the zero
map. -/
theorem frontier_subset_frontierCoverFamily :
    frontier (normAtAllPlaces '' normLeOne K) ⊆
      ⋃ s, frontierCoverFamily K s '' Icc 0 1 := by
  classical
  rw [normAtAllPlaces_normLeOne_eq_image]
  refine (frontier_image_paramSet_subset K).trans
    (Set.union_subset ((image_boundary_subset_faces K).trans (Set.union_subset ?_ ?_)) ?_)
  · rintro x ⟨c', hc', rfl⟩
    obtain ⟨c, hc, rfl⟩ := exists_cubeRelabel_eq K hc'
    refine Set.mem_iUnion.mpr ⟨Sum.inr (Sum.inl ()), c, hc, ?_⟩
    change faceMapZero K (clampUnit _ (cubeRelabel K c)) = faceMapZero K (cubeRelabel K c)
    rw [clampUnit_eq_self (cubeRelabel_mem_Icc K hc)]
  · rintro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, a, ha, c', hc', rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := exists_cubeRelabel_eq K hc'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    obtain ⟨b, rfl⟩ : ∃ b : Bool, (if b then (1 : ℝ) else 0) = a := by
      rcases ha with rfl | rfl
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
    refine Set.mem_iUnion.mpr ⟨Sum.inr (Sum.inr (i, b)), c, hc, ?_⟩
    change faceMapSide K i (if b then (1 : ℝ) else 0) (clampUnit _ (cubeRelabel K c)) = _
    rw [clampUnit_eq_self (cubeRelabel_mem_Icc K hc)]
  · rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Set.mem_iUnion.mpr ⟨Sum.inl (), 0, ⟨le_rfl, fun _ ↦ zero_le_one⟩, rfl⟩

/-- **The Lipschitz cover of the frontier of `normAtAllPlaces '' (normLeOne K)`**
(Gun–Ramaré–Sivaraman §3.3, after Debaene). This is the exact `hlip` regularity hypothesis of
the effective lattice-point count `exists_card_inter_smul_lattice_sub_volume_mul_pow_le`,
specialized to the ideal-counting region: finitely many `M`-Lipschitz maps from
`[0,1]^{r-1}`, `r = #InfinitePlace K`, whose cube images cover the frontier. -/
theorem normLeOne_frontier_lipschitz_cover :
    ∃ (m : ℕ) (M : ℝ≥0)
      (φ : Fin m → (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K),
      (∀ j, LipschitzWith M (φ j)) ∧
        frontier (normAtAllPlaces '' normLeOne K) ⊆ ⋃ j, φ j '' Icc 0 1 := by
  classical
  obtain ⟨M, hM⟩ := exists_lipschitzWith_frontierCoverFamily K
  set e := Fintype.equivFin (Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool))
  refine ⟨_, M, fun j ↦ frontierCoverFamily K (e.symm j), fun j ↦ hM _, ?_⟩
  rw [e.symm.surjective.iUnion_comp fun s ↦ frontierCoverFamily K s '' Icc 0 1]
  exact frontier_subset_frontierCoverFamily K

end Chebotarev
