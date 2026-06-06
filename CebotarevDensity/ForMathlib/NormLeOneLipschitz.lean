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

The proof rests entirely on mathlib's parametrization
`normAtAllPlaces '' (normLeOne K) = expMapBasis '' (paramSet K)` where
`paramSet K = Iic 0 × [0,1)^{r-1}` (in the `completeBasis` coordinates):

1. `expMapBasis` is an open injective map (`OpenPartialHomeomorph` with source `univ`), so
   `frontier (expMapBasis '' paramSet K) ⊆ expMapBasis '' (∂ paramSet K) ∪ {0}`, the `{0}`
   accounting for the closure points escaping to norm `0` as the `w₀`-coordinate `→ -∞`
   (`frontier_image_paramSet_subset`).
2. The box boundary `∂ paramSet K` consists of the face `{x w₀ = 0}` and the side faces
   `{x i = a}`, `a ∈ {0,1}`, `i ≠ w₀`.
3. On the `w₀`-face, `expMapBasis` itself restricted to the compact cube parametrizes the
   image (`faceMapZero`). On a side face the `w₀`-direction is unbounded, but
   `expMapBasis x = exp (x w₀) • expMapBasis (x [w₀ ↦ 0])` (`expMapBasis_apply''`), so the
   substitution `t = exp (x w₀) ∈ (0,1]` linearizes it: the face image is parametrized by the
   compact cube via `faceMapSide` — `t` taking the cube slot freed by pinning `x i = a` — and
   the `t = 0` slice absorbs the leftover `{0}` (`faceMapSide_zero`).
4. All parametrizations are restrictions of globally `C¹` maps to the compact convex cube,
   hence Lipschitz there (`ContDiff.locallyLipschitz` +
   `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`); composing with the `1`-Lipschitz
   cube clamp `clampUnit` makes them globally Lipschitz without changing the cube image.

The final statement `normLeOne_frontier_lipschitz_cover` has exactly the `hlip` shape consumed
by `exists_card_inter_smul_lattice_sub_volume_mul_pow_le`.
-/

@[expose] public section

noncomputable section

namespace Chebotarev

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone NumberField.Units dirichletUnitTheorem Set

open scoped NNReal

/-! ### The cube clamp

`clampUnit` retracts `ι → ℝ` onto the unit cube `Icc 0 1`; it is `1`-Lipschitz and fixes the
cube pointwise, so post-composition turns a cube-Lipschitz map into a globally Lipschitz map
with the same cube image. -/

/-- The coordinatewise retraction of `ι → ℝ` onto the unit cube `Set.Icc 0 1`. -/
def clampUnit (ι : Type*) (c : ι → ℝ) : ι → ℝ := fun i => max 0 (min 1 (c i))

theorem clampUnit_mem_Icc (ι : Type*) (c : ι → ℝ) : clampUnit ι c ∈ Icc (0 : ι → ℝ) 1 :=
  ⟨fun _ => le_max_left _ _, fun _ => max_le zero_le_one (min_le_left _ _)⟩

theorem clampUnit_eq_self {ι : Type*} {c : ι → ℝ} (hc : c ∈ Icc (0 : ι → ℝ) 1) :
    clampUnit ι c = c := by
  funext i
  have h1 : (0 : ℝ) ≤ c i := hc.1 i
  have h2 : c i ≤ 1 := hc.2 i
  rw [clampUnit, min_eq_right h2, max_eq_right h1]

theorem lipschitzWith_clampUnit (ι : Type*) [Fintype ι] : LipschitzWith 1 (clampUnit ι) := by
  refine LipschitzWith.of_dist_le_mul fun c d => ?_
  rw [NNReal.coe_one, one_mul]
  refine (dist_pi_le_iff dist_nonneg).mpr fun i => ?_
  refine le_trans ?_ (dist_le_pi_dist c d i)
  rw [Real.dist_eq, Real.dist_eq]
  simp only [clampUnit]
  rw [max_comm (0 : ℝ) (min 1 (c i)), max_comm (0 : ℝ) (min 1 (d i))]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  simpa [abs_sub_comm] using abs_min_sub_min_le_max (1 : ℝ) (c i) 1 (d i)

/-- A globally `C¹` map into `κ → ℝ`, pre-composed with the cube clamp, is globally Lipschitz;
its image of the unit cube is unchanged. The Lipschitz constant comes from compactness of the
cube (`LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`). -/
theorem exists_lipschitzWith_comp_clampUnit {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : (ι → ℝ) → κ → ℝ} (hf : ContDiff ℝ 1 f) :
    ∃ M : ℝ≥0, LipschitzWith M (f ∘ clampUnit ι) := by
  have hl : LocallyLipschitzOn (Icc (0 : ι → ℝ) 1) f := hf.locallyLipschitz.locallyLipschitzOn
  obtain ⟨M, hM⟩ := hl.exists_lipschitzOnWith_of_compact isCompact_Icc
  refine ⟨M, fun c d => ?_⟩
  calc edist (f (clampUnit ι c)) (f (clampUnit ι d))
      ≤ M * edist (clampUnit ι c) (clampUnit ι d) :=
        hM (clampUnit_mem_Icc ι c) (clampUnit_mem_Icc ι d)
    _ ≤ M * (1 * edist c d) := by gcongr; exact lipschitzWith_clampUnit ι c d
    _ = M * edist c d := by rw [one_mul]

variable (K : Type*) [Field K] [NumberField K]

/-! ### Smoothness of `expMapBasis`

In coordinates, `(expMapBasis x) w = exp (x w₀) · ∏ i, w (fundSystem K i) ^ x i` is the
exponential of an affine function of `x` (the bases `w (fundSystem K i)` are positive), hence
`expMapBasis` is `C¹` (indeed `C^∞`) as a map `realSpace K → realSpace K`. -/

theorem contDiff_expMapBasis : ContDiff ℝ 1 (⇑(expMapBasis (K := K))) := by
  classical
  have h : ⇑(expMapBasis (K := K)) = fun x : realSpace K =>
      Real.exp (x w₀) • fun w : InfinitePlace K =>
        ∏ i : {w // w ≠ w₀}, w (fundSystem K (equivFinRank.symm i)) ^ x i :=
    funext fun x => expMapBasis_apply' x
  rw [h]
  refine (Real.contDiff_exp.comp (contDiff_apply ℝ _ w₀)).smul
    (contDiff_pi.mpr fun w => contDiff_prod fun i _ => ?_)
  exact (contDiff_const (c := w (fundSystem K (equivFinRank.symm i)))).rpow
    (contDiff_apply ℝ ℝ (i : InfinitePlace K)) fun x => (InfinitePlace.pos_iff.mpr (by simp)).ne'

/-! ### The face parametrizations -/

open scoped Classical in
/-- Parametrization of the `expMapBasis`-image of the `w₀`-face `{x | x w₀ = 0}` of
`paramSet K`: plug `0` in the `w₀`-slot and the cube coordinates in the remaining slots. -/
def faceMapZero (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : realSpace K :=
  expMapBasis fun w => if hw : w = w₀ then 0 else c ⟨w, hw⟩

open scoped Classical in
/-- Parametrization of the `expMapBasis`-image of a side face `{x | x i = a}` (`i ≠ w₀`,
`a ∈ {0,1}`) of `paramSet K`. The `w₀`-direction of the face is the unbounded `Iic 0`; the
substitution `t = exp (x w₀) ∈ (0,1]` (`expMapBasis_apply''`) turns it into the cube coordinate
`c i` — the slot freed by pinning `x i = a`:
`faceMapSide i a c = (c i) • expMapBasis (x [w₀ ↦ 0, i ↦ a, w ↦ c w])`. -/
def faceMapSide (i : {w : InfinitePlace K // w ≠ w₀}) (a : ℝ)
    (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : realSpace K :=
  c i • expMapBasis fun w => if hw : w = w₀ then 0 else if (⟨w, hw⟩ : {w // w ≠ w₀}) = i then a
    else c ⟨w, hw⟩

open scoped Classical in
theorem contDiff_faceMapZero : ContDiff ℝ 1 (faceMapZero K) := by
  refine (contDiff_expMapBasis K).comp (contDiff_pi.mpr fun w => ?_)
  by_cases hw : w = w₀
  · simp only [dif_pos hw]
    exact contDiff_const
  · simp only [dif_neg hw]
    exact contDiff_apply ℝ ℝ _

open scoped Classical in
theorem contDiff_faceMapSide (i : {w : InfinitePlace K // w ≠ w₀}) (a : ℝ) :
    ContDiff ℝ 1 (faceMapSide K i a) := by
  refine (contDiff_apply ℝ ℝ i).smul ((contDiff_expMapBasis K).comp (contDiff_pi.mpr fun w => ?_))
  by_cases hw : w = w₀
  · simp only [dif_pos hw]
    exact contDiff_const
  · simp only [dif_neg hw]
    by_cases hi : (⟨w, hw⟩ : {w // w ≠ w₀}) = i
    · simp only [if_pos hi]
      exact contDiff_const
    · simp only [if_neg hi]
      exact contDiff_apply ℝ ℝ _

/-! ### The frontier is contained in the face images -/

/-- **Topological reduction.** Since `expMapBasis` is open and injective with source `univ`,
the frontier of `expMapBasis '' paramSet K` is contained in the image of the box boundary
`closure (paramSet K) \ interior (paramSet K)`, together with `{0}` (the escape to norm `0`):
`closure (expMapBasis '' paramSet K) ⊆ compactSet K = expMapBasis '' closure (paramSet K) ∪ {0}`
while `expMapBasis '' interior (paramSet K)` is open, hence inside the interior. -/
theorem frontier_image_paramSet_subset :
    frontier (expMapBasis '' paramSet K) ⊆
      expMapBasis '' (closure (paramSet K) \ interior (paramSet K)) ∪ {0} := by
  -- The closure of the image lands in the compact set.
  have hcl : closure (expMapBasis '' paramSet K) ⊆ compactSet K :=
    (isCompact_compactSet K).isClosed.closure_subset_iff.mpr
      ((Set.image_mono subset_closure).trans (expMapBasis_closure_subset_compactSet K))
  -- The image of the interior is open, hence contained in the interior of the image.
  have hopen : IsOpen (expMapBasis '' interior (paramSet K)) :=
    expMapBasis.isOpen_image_of_subset_source isOpen_interior (by simp [expMapBasis_source])
  have hint : expMapBasis '' interior (paramSet K) ⊆ interior (expMapBasis '' paramSet K) :=
    hopen.subset_interior_iff.mpr (Set.image_mono interior_subset)
  -- `frontier = closure \ interior`, so it is contained in `compactSet \ image-of-interior`.
  have hfront : frontier (expMapBasis '' paramSet K) ⊆
      compactSet K \ expMapBasis '' interior (paramSet K) :=
    Set.diff_subset_diff hcl hint
  refine hfront.trans ?_
  rw [compactSet_eq_union, Set.union_diff_distrib,
    ← Set.image_diff (injective_expMapBasis K)]
  exact Set.union_subset_union_right _ (Set.diff_subset.trans (by rfl))

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
  -- From closure: `y w₀ ≤ 0` and `y v ∈ [0,1]` for `v ≠ w₀`.
  have hw₀ : y w₀ ≤ 0 := by simpa using hyc w₀
  have hIcc : ∀ v : InfinitePlace K, v ≠ w₀ → y v ∈ Icc (0 : ℝ) 1 := fun v hv => by
    simpa [hv] using hyc v
  by_cases hwe : w = w₀
  · -- The boundary coordinate is `w₀`, so `y w₀ = 0`: a `w₀`-face point.
    rw [if_pos hwe, Set.mem_Iio, not_lt, hwe] at hw
    have hy0 : y w₀ = 0 := le_antisymm hw₀ hw
    refine Or.inl ⟨fun i => y i.1, ⟨fun i => (hIcc i.1 i.2).1, fun i => (hIcc i.1 i.2).2⟩, ?_⟩
    rw [faceMapZero]
    congr 1
    funext v
    by_cases hv : v = w₀
    · simp only [dif_pos hv]
      rw [hv, hy0]
    · simp only [dif_neg hv]
  · -- The boundary coordinate is `w ≠ w₀`, so `y w ∈ {0,1}`: a side-face point.
    rw [if_neg hwe] at hw
    have ha : y w = 0 ∨ y w = 1 := by
      have h1 := hIcc w hwe
      rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hw
      rcases hw with h | h
      · exact Or.inl (le_antisymm h h1.1)
      · exact Or.inr (le_antisymm h1.2 h)
    set i : {w : InfinitePlace K // w ≠ w₀} := ⟨w, hwe⟩ with hi
    set c : {w : InfinitePlace K // w ≠ w₀} → ℝ :=
      fun j => if j = i then Real.exp (y w₀) else y j.1 with hc
    have hcmem : c ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 := by
      refine ⟨fun j => ?_, fun j => ?_⟩
      · simp only [hc]
        split_ifs
        · exact Real.exp_nonneg _
        · exact (hIcc j.1 j.2).1
      · simp only [hc]
        split_ifs
        · exact Real.exp_le_one_iff.mpr hw₀
        · exact (hIcc j.1 j.2).2
    have hkey : faceMapSide K i (y w) c = expMapBasis y := by
      have hci : c i = Real.exp (y w₀) := by simp [hc]
      have hfun : (fun w' => if hw' : w' = w₀ then (0 : ℝ) else
          if (⟨w', hw'⟩ : {w // w ≠ w₀}) = i then y w else c ⟨w', hw'⟩) =
          fun w' => if w' = w₀ then 0 else y w' := by
        funext w'
        by_cases hw'₀ : w' = w₀
        · simp only [dif_pos hw'₀, if_pos hw'₀]
        · simp only [dif_neg hw'₀, if_neg hw'₀]
          by_cases hw'w : (⟨w', hw'₀⟩ : {w // w ≠ w₀}) = i
          · simp only [if_pos hw'w]
            have : w' = w := by rw [hi] at hw'w; exact Subtype.ext_iff.mp hw'w
            rw [this]
          · simp only [hc, if_neg hw'w]
      rw [faceMapSide, expMapBasis_apply'' y, hci, hfun]
    refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion₂.mpr ⟨y w, ?_, ⟨c, hcmem, hkey⟩⟩⟩)
    rcases ha with h | h <;> simp [h]

/-! ### Cube relabelling and the covering family

The frontier statement indexes its cube by `Fin (#InfinitePlace K - 1)`, while the face maps are
indexed by the non-distinguished places `{w ≠ w₀}`. `cubeRelabel` transports the cube along
`equivFinRank`; it is `1`-Lipschitz, maps the unit cube into itself, and is onto the unit cube. The
covering family `frontierCoverFamily` collects the zero map, the `w₀`-face map, and the side-face
maps, each clamped to the cube and relabelled. -/

/-- Relabel cube coordinates `Fin (#InfinitePlace K - 1) → ℝ` by the non-distinguished places
`{w ≠ w₀}` via `equivFinRank`. -/
def cubeRelabel (c : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) :
    {w : InfinitePlace K // w ≠ w₀} → ℝ :=
  fun j => c (equivFinRank.symm j)

open scoped Classical in
theorem lipschitzWith_cubeRelabel : LipschitzWith 1 (cubeRelabel K) :=
  LipschitzWith.of_edist_le fun c d => by
    simp only [cubeRelabel, edist_pi_def]
    exact Finset.sup_le fun j _ => edist_le_pi_edist c d (equivFinRank.symm j)

theorem cubeRelabel_mem_Icc {c : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ}
    (hc : c ∈ Icc (0 : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) 1) :
    cubeRelabel K c ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 :=
  ⟨fun _ => hc.1 _, fun _ => hc.2 _⟩

theorem exists_cubeRelabel_eq {c' : {w : InfinitePlace K // w ≠ w₀} → ℝ}
    (hc' : c' ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1) :
    ∃ c ∈ Icc (0 : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) 1, cubeRelabel K c = c' :=
  ⟨fun j => c' (equivFinRank j), ⟨fun j => hc'.1 _, fun j => hc'.2 _⟩,
    funext fun j => by simp [cubeRelabel]⟩

/-- The finite family covering the frontier: the zero map (index `inl ()`), the `w₀`-face map
(`inr (inl ())`), and the side-face maps `faceMapSide i a` for `i ≠ w₀`, `a ∈ {0,1}`
(`inr (inr (i, b))`, `a = if b then 1 else 0`), each post-clamped to the unit cube and relabelled
through `cubeRelabel`. -/
def frontierCoverFamily :
    (Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool)) →
      (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K :=
  Sum.elim (fun _ _ => 0)
    (Sum.elim (fun _ => faceMapZero K ∘ clampUnit _ ∘ cubeRelabel K)
      fun p => faceMapSide K p.1 (if p.2 then 1 else 0) ∘ clampUnit _ ∘ cubeRelabel K)

/-- Every member of `frontierCoverFamily` is `M`-Lipschitz for a common constant `M`: each face
map is `C¹` on the compact cube hence Lipschitz there (`exists_lipschitzWith_comp_clampUnit`), and
pre-composing with the `1`-Lipschitz `cubeRelabel` preserves the constant; take `M` to be the
supremum over the finitely many faces. -/
theorem exists_lipschitzWith_frontierCoverFamily :
    ∃ M : ℝ≥0, ∀ s, LipschitzWith M (frontierCoverFamily K s) := by
  classical
  obtain ⟨M₀, hM₀⟩ := exists_lipschitzWith_comp_clampUnit (contDiff_faceMapZero K)
  choose Ms hMs using fun p : {w : InfinitePlace K // w ≠ w₀} × Bool =>
    exists_lipschitzWith_comp_clampUnit (contDiff_faceMapSide K p.1 (if p.2 then 1 else 0))
  refine ⟨M₀ ⊔ Finset.univ.sup Ms, fun s => ?_⟩
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
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, hx⟩ := hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨a, ha, c', hc', rfl⟩ := hx
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
    exact Set.mem_iUnion.mpr ⟨Sum.inl (), 0, ⟨le_rfl, fun _ => zero_le_one⟩, rfl⟩

/-! ### Assembly -/

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
  -- Reindex the sum-typed family by `Fin (card …)` to match the statement shape.
  set e := Fintype.equivFin (Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool))
  refine ⟨_, M, fun j => frontierCoverFamily K (e.symm j), fun j => hM _, ?_⟩
  rw [e.symm.surjective.iUnion_comp fun s => frontierCoverFamily K s '' Icc 0 1]
  exact frontier_subset_frontierCoverFamily K

/-! ### Lifting the cover from `realSpace K` to `mixedSpace K`

The frontier cover above lives in `realSpace K = InfinitePlace K → ℝ`, the target of
`normAtAllPlaces`. Since `normLeOne K = normAtAllPlaces ⁻¹' (normAtAllPlaces '' normLeOne K)`
(`normLeOne_eq_preimage_image`) and `normAtAllPlaces` is continuous
(`continuous_normAtAllPlaces`), the frontier of `normLeOne K` in `mixedSpace K` is contained in
the `normAtAllPlaces`-preimage of the (already covered) real-space frontier
(`Continuous.frontier_preimage_subset`).

The fibre of `normAtAllPlaces` over a nonnegative `y : realSpace K` is parametrized by the signs
of the real coordinates (`x.1 w = ± y w`, a finite choice folded into the index) and the phases
of the complex coordinates (`x.2 w = y w · exp((2π θ_w − π) i)`, `θ_w ∈ [0,1]`, the extra `r₂`
cube coordinates). Lifting each cover map `ψ` along this parametrization turns the `r − 1`
cube coordinates into `(r − 1) + r₂ = d − 1` coordinates (`d = finrank ℚ K`), matching the
target dimension `Fin (finrank ℚ K - 1)`. -/

/-- The unit-circle exponential `t ↦ exp(t i)` is globally `1`-Lipschitz: factoring
`exp(α i) − exp(β i) = exp(β i)(exp((α − β) i) − 1)` reduces to the bound
`‖exp(t i) − 1‖ ≤ |t|`, i.e. `2 − 2 cos t ≤ t²` via the half-angle `|sin (t/2)| ≤ |t/2|`. -/
theorem lipschitzWith_exp_ofReal_mul_I :
    LipschitzWith 1 (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) := by
  have hcos : ∀ t : ℝ, 2 - 2 * Real.cos t ≤ t ^ 2 := by
    intro t
    have heq : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
      have h := Real.cos_add (t / 2) (t / 2)
      have h2 := Real.sin_sq_add_cos_sq (t / 2)
      have ht : t / 2 + t / 2 = t := by ring
      rw [ht] at h; nlinarith [h, h2]
    have hs2 : Real.sin (t / 2) ^ 2 ≤ (t / 2) ^ 2 := by
      rw [← sq_abs (Real.sin (t / 2)), ← sq_abs (t / 2)]
      exact pow_le_pow_left₀ (abs_nonneg _) Real.abs_sin_le_abs 2
    rw [heq]; nlinarith [hs2]
  have hsub : ∀ t : ℝ, ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ≤ |t| := by
    intro t
    have h1 : Complex.exp ((t : ℂ) * Complex.I) - 1
        = ((Real.cos t - 1 : ℝ) : ℂ) + ((Real.sin t : ℝ) : ℂ) * Complex.I := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; push_cast; ring
    rw [h1, Complex.norm_def, Complex.normSq_add_mul_I,
      show (Real.cos t - 1) ^ 2 + Real.sin t ^ 2 = 2 - 2 * Real.cos t from by
        nlinarith [Real.sin_sq_add_cos_sq t],
      show |t| = Real.sqrt (t ^ 2) from (Real.sqrt_sq_eq_abs t).symm]
    exact Real.sqrt_le_sqrt (hcos t)
  refine LipschitzWith.of_dist_le_mul fun α β => ?_
  rw [NNReal.coe_one, one_mul, Complex.dist_eq, Real.dist_eq]
  have key : Complex.exp ((α : ℂ) * Complex.I) - Complex.exp ((β : ℂ) * Complex.I)
      = Complex.exp ((β : ℂ) * Complex.I)
        * (Complex.exp (((α - β : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; push_cast; ring_nf
  rw [key, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact hsub (α - β)

/-- The phase reparametrization `θ ↦ exp((2π θ − π) i)` is `2π`-Lipschitz: it is the
unit-circle exponential (`1`-Lipschitz) composed with the `2π`-Lipschitz affine map
`θ ↦ 2π θ − π`. -/
theorem lipschitzWith_phase :
    LipschitzWith (2 * Real.pi).toNNReal
      (fun t : ℝ =>
        Complex.exp ((2 * (Real.pi : ℂ) * (t : ℂ) - (Real.pi : ℂ)) * Complex.I)) := by
  have haff : LipschitzWith (2 * Real.pi).toNNReal (fun t : ℝ => 2 * Real.pi * t - Real.pi) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity),
      show 2 * Real.pi * x - Real.pi - (2 * Real.pi * y - Real.pi) = 2 * Real.pi * (x - y) from by
        ring, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  have hcomp : (fun t : ℝ =>
        Complex.exp ((2 * (Real.pi : ℂ) * (t : ℂ) - (Real.pi : ℂ)) * Complex.I))
      = (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
        ∘ (fun t : ℝ => 2 * Real.pi * t - Real.pi) := by
    funext t; simp only [Function.comp_apply]; push_cast; ring_nf
  rw [hcomp]
  have := lipschitzWith_exp_ofReal_mul_I.comp haff
  rwa [one_mul] at this

/-- Polar parametrization of a complex coordinate by a phase in the unit interval: every
`z : ℂ` equals `‖z‖ · exp((2π θ − π) i)` for some `θ ∈ [0,1]` (`θ = (arg z + π)/(2π)`, lying in
`(0,1]` since `arg z ∈ (−π, π]`). -/
theorem exists_phase_mem_Icc_mul_exp (z : ℂ) :
    ∃ θ : ℝ, θ ∈ Icc (0 : ℝ) 1 ∧
      (‖z‖ : ℂ) * Complex.exp ((2 * Real.pi * θ - Real.pi) * Complex.I) = z := by
  refine ⟨(z.arg + Real.pi) / (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
  · exact div_nonneg (by linarith [Complex.neg_pi_lt_arg z]) (by positivity)
  · rw [div_le_one (by positivity)]; linarith [Complex.arg_le_pi z]
  · have hreal : (2 * Real.pi * ((z.arg + Real.pi) / (2 * Real.pi)) - Real.pi : ℝ) = z.arg := by
      field_simp; ring
    rw [show ((2 : ℂ) * (Real.pi : ℂ) * (((z.arg + Real.pi) / (2 * Real.pi) : ℝ) : ℂ)
          - (Real.pi : ℂ))
        = ((2 * Real.pi * ((z.arg + Real.pi) / (2 * Real.pi)) - Real.pi : ℝ) : ℂ) from by
          push_cast; ring, hreal]
    exact Complex.norm_mul_exp_arg_mul_I z

open scoped Classical in
/-- The lift splits the `d − 1` cube coordinates into the `r − 1 = #InfinitePlace K − 1`
"modulus" coordinates (fed to a `realSpace`-valued cover map) and the `r₂` "phase" coordinates
(one per complex place). The cardinalities match: `(d − 1) = (r − 1) + r₂` follows from
`r₁ + 2 r₂ = d` (`card_add_two_mul_card_eq_rank`) and `r = r₁ + r₂`
(`card_eq_nrRealPlaces_add_nrComplexPlaces`), with `r ≥ 1` (`Fintype.card_pos`). -/
noncomputable def mixedCubeEquiv :
    Fin (Module.finrank ℚ K - 1)
      ≃ Fin (Fintype.card (InfinitePlace K) - 1) ⊕ {w : InfinitePlace K // IsComplex w} := by
  apply Fintype.equivOfCardEq
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  have h1 : Fintype.card (InfinitePlace K) = nrRealPlaces K + nrComplexPlaces K :=
    card_eq_nrRealPlaces_add_nrComplexPlaces K
  have h2 : nrRealPlaces K + 2 * nrComplexPlaces K = Module.finrank ℚ K :=
    card_add_two_mul_card_eq_rank K
  have hpos : 1 ≤ Fintype.card (InfinitePlace K) := Fintype.card_pos
  have h3 : nrComplexPlaces K = Fintype.card {w : InfinitePlace K // IsComplex w} := rfl
  omega

open scoped Classical in
/-- Lift a `realSpace`-valued cover map `ψ` to a `mixedSpace`-valued map, using the first
`r − 1` cube coordinates as the modulus input to `ψ` and the last `r₂` coordinates as the phases
of the complex places, with the real places carrying the sign pattern `ε`.

At a real place `w` the coordinate is `± (ψ ·) w`; at a complex place `w` it is
`(ψ ·) w · exp((2π θ_w − π) i)`. By construction `normAtAllPlaces (liftToMixed ψ ε c) = ψ (…)`
whenever the modulus values `(ψ ·) w` are nonnegative. -/
noncomputable def liftToMixed
    (ψ : (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K)
    (ε : {w : InfinitePlace K // IsReal w} → Bool)
    (c : Fin (Module.finrank ℚ K - 1) → ℝ) : mixedSpace K :=
  (fun w : {w : InfinitePlace K // IsReal w} =>
      (if ε w then (1 : ℝ) else -1) * ψ (fun i => c ((mixedCubeEquiv K).symm (Sum.inl i))) w.1,
    fun w : {w : InfinitePlace K // IsComplex w} =>
      (ψ (fun i => c ((mixedCubeEquiv K).symm (Sum.inl i))) w.1 : ℂ) *
        Complex.exp ((2 * Real.pi * c ((mixedCubeEquiv K).symm (Sum.inr w)) - Real.pi) *
          Complex.I))

open scoped Classical in
/-- If the cover map `ψ` is `M₀`-Lipschitz and uniformly bounded by `B` on the cube image, then
its lift `liftToMixed K ψ ε` is globally Lipschitz. The real coordinates are isometric copies of
`ψ`-coordinates (`M₀`); a complex coordinate `(ψ ·) w · exp((2π θ − π) i)` is bounded by the
product estimate `dist (a u) (b v) ≤ ‖a‖ · dist u v + ‖v‖ · dist a b`, contributing
`B · 2π` from the phase (`lipschitzWith_exp_ofReal_mul_I`) and `M₀` from the modulus. -/
theorem lipschitzWith_liftToMixed
    {ψ : (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K}
    {M₀ : ℝ≥0} {B : ℝ}
    (hψ : LipschitzWith M₀ ψ) (hB : ∀ c, ‖ψ c‖ ≤ B)
    (ε : {w : InfinitePlace K // IsReal w} → Bool) :
    LipschitzWith (M₀ + (B * (2 * Real.pi)).toNNReal) (liftToMixed K ψ ε) := by
  have hBnn : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  -- abbreviations for the modulus input
  set N : ℝ≥0 := M₀ + (B * (2 * Real.pi)).toNNReal with hN
  refine LipschitzWith.of_dist_le_mul fun c d => ?_
  set yc : realSpace K := ψ (fun i => c ((mixedCubeEquiv K).symm (Sum.inl i))) with hyc
  set yd : realSpace K := ψ (fun i => d ((mixedCubeEquiv K).symm (Sum.inl i))) with hyd
  -- modulus map is M₀-Lipschitz in the cube point
  have hmod : dist yc yd ≤ M₀ * dist c d := by
    rw [hyc, hyd]
    refine le_trans (hψ.dist_le_mul _ _) ?_
    gcongr
    exact (dist_pi_le_iff dist_nonneg).mpr fun i => dist_le_pi_dist c d _
  rw [liftToMixed, liftToMixed, Prod.dist_eq]
  refine max_le ?_ ?_
  · -- real coordinates
    refine (dist_pi_le_iff (by positivity)).mpr fun w => ?_
    simp only
    have hsign : dist ((if ε w then (1 : ℝ) else -1) * yc w.1)
        ((if ε w then (1 : ℝ) else -1) * yd w.1) = dist (yc w.1) (yd w.1) := by
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
      split_ifs <;> simp
    rw [hsign]
    calc dist (yc w.1) (yd w.1) ≤ dist yc yd := dist_le_pi_dist yc yd w.1
      _ ≤ M₀ * dist c d := hmod
      _ ≤ N * dist c d := by gcongr; rw [hN]; exact_mod_cast le_self_add
  · -- complex coordinates
    refine (dist_pi_le_iff (by positivity)).mpr fun w => ?_
    simp only
    set θc : ℝ := c ((mixedCubeEquiv K).symm (Sum.inr w)) with hθc
    set θd : ℝ := d ((mixedCubeEquiv K).symm (Sum.inr w)) with hθd
    set uc : ℂ :=
      Complex.exp ((2 * (Real.pi : ℂ) * (θc : ℂ) - (Real.pi : ℂ)) * Complex.I) with huc
    set ud : ℂ :=
      Complex.exp ((2 * (Real.pi : ℂ) * (θd : ℂ) - (Real.pi : ℂ)) * Complex.I) with hud
    -- product estimate: dist (a u) (b v) ≤ ‖a‖ · dist u v + ‖v‖ · dist a b
    have hprod : dist ((yc w.1 : ℂ) * uc) ((yd w.1 : ℂ) * ud)
        ≤ ‖(yc w.1 : ℂ)‖ * dist uc ud + ‖ud‖ * dist (yc w.1 : ℂ) (yd w.1 : ℂ) := by
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm,
        show (yc w.1 : ℂ) * uc - (yd w.1 : ℂ) * ud
          = (yc w.1 : ℂ) * (uc - ud) + ((yc w.1 : ℂ) - (yd w.1 : ℂ)) * ud from by ring]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]; ring_nf; rfl
    refine hprod.trans ?_
    -- bound the three factors
    have hav : ‖ud‖ = 1 := by
      rw [hud, Complex.norm_exp, show ((2 * (Real.pi : ℂ) * (θd : ℂ) - (Real.pi : ℂ)) *
        Complex.I).re = 0 from by simp, Real.exp_zero]
    have ha : ‖(yc w.1 : ℂ)‖ ≤ B := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_trans (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm yc w.1) (hB _)
    -- phase factor is 2π-Lipschitz in the phase coordinate
    have hphase : dist uc ud ≤ 2 * Real.pi * dist c d := by
      have h := lipschitzWith_phase.dist_le_mul θc θd
      rw [huc, hud]
      refine h.trans ?_
      rw [Real.coe_toNNReal _ (by positivity)]
      gcongr
      exact dist_le_pi_dist c d _
    -- modulus difference at this place
    have hmodc : dist (yc w.1 : ℂ) (yd w.1 : ℂ) ≤ M₀ * dist c d := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        ← Real.dist_eq]
      exact le_trans (dist_le_pi_dist yc yd w.1) hmod
    have hddnn : (0 : ℝ) ≤ dist c d := dist_nonneg
    calc ‖(yc w.1 : ℂ)‖ * dist uc ud + ‖ud‖ * dist (yc w.1 : ℂ) (yd w.1 : ℂ)
        ≤ B * (2 * Real.pi * dist c d) + 1 * (M₀ * dist c d) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul ha hphase dist_nonneg hBnn
          · rw [hav]
            exact mul_le_mul_of_nonneg_left hmodc zero_le_one
      _ = (↑M₀ + ↑(B * (2 * Real.pi)).toNNReal) * dist c d := by
          rw [Real.coe_toNNReal _ (by positivity)]; ring
      _ = ↑N * dist c d := by rw [hN, NNReal.coe_add]

/-- Every member of `frontierCoverFamily` is **globally bounded** by a single constant `B`:
each face map is continuous and is only ever evaluated on the compact cube (the clamp
`clampUnit` lands in `Icc 0 1`), so its range is bounded; take the supremum over the finitely
many faces. This is the boundedness hypothesis feeding `lipschitzWith_liftToMixed`. -/
theorem exists_bound_frontierCoverFamily :
    ∃ B : ℝ, ∀ s c, ‖frontierCoverFamily K s c‖ ≤ B := by
  classical
  have hbd : ∀ (g : ({w : InfinitePlace K // w ≠ w₀} → ℝ) → realSpace K),
      Continuous g → ∃ B : ℝ, ∀ c, ‖g (clampUnit _ (cubeRelabel K c))‖ ≤ B := by
    intro g hg
    obtain ⟨B, hB⟩ := (isCompact_Icc.image hg).isBounded.subset_closedBall 0
    refine ⟨B, fun c => ?_⟩
    have := hB (mem_image_of_mem g (clampUnit_mem_Icc _ (cubeRelabel K c)))
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  obtain ⟨B₀, hB₀⟩ := hbd _ (contDiff_faceMapZero K).continuous
  choose Bs hBs using fun p : {w : InfinitePlace K // w ≠ w₀} × Bool =>
    hbd _ (contDiff_faceMapSide K p.1 (if p.2 then 1 else 0)).continuous
  refine ⟨↑(B₀.toNNReal ⊔ Finset.univ.sup fun p => (Bs p).toNNReal), fun s c => ?_⟩
  rcases s with _ | _ | p
  · have h0 : ‖frontierCoverFamily K (Sum.inl ()) c‖ = 0 := by simp [frontierCoverFamily]
    rw [h0]; positivity
  · refine le_trans (hB₀ c) ?_
    refine (Real.le_coe_toNNReal B₀).trans ?_
    exact_mod_cast le_sup_left
  · refine le_trans (hBs p c) ?_
    refine (Real.le_coe_toNNReal (Bs p)).trans ?_
    have hsup : (Bs p).toNNReal ≤ Finset.univ.sup fun q => (Bs q).toNNReal :=
      Finset.le_sup (f := fun q => (Bs q).toNNReal) (Finset.mem_univ p)
    have : (Bs p).toNNReal ≤ max B₀.toNNReal (Finset.univ.sup fun q => (Bs q).toNNReal) :=
      le_sup_of_le_right hsup
    exact_mod_cast this

open scoped Classical in
/-- **Fibre covering.** If a point `y` of the `realSpace` frontier cover is `normAtAllPlaces x`,
then `x` lies in the cube image of `liftToMixed K ψ ε` for the sign pattern `ε` reading off the
signs of the real coordinates of `x`: the modulus coordinates `(ψ ·) w = normAtPlace w x` are the
absolute values / norms of the coordinates of `x`, and the phases come from the polar form of the
complex coordinates (`exists_phase_mem_Icc_mul_exp`). -/
theorem mem_iUnion_image_liftToMixed_of_eq
    {ψ : (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K}
    {c' : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ} (hc' : c' ∈ Icc (0 : _) 1)
    {x : mixedSpace K} (hx : normAtAllPlaces x = ψ c') :
    x ∈ ⋃ ε : {w : InfinitePlace K // IsReal w} → Bool, liftToMixed K ψ ε '' Icc 0 1 := by
  -- the phase of each complex coordinate
  choose θ hθmem hθeq using fun w : {w : InfinitePlace K // IsComplex w} =>
    exists_phase_mem_Icc_mul_exp (x.2 w)
  -- the sign of each real coordinate
  set ε : {w : InfinitePlace K // IsReal w} → Bool := fun w => decide (0 ≤ x.1 w) with hε
  set c : Fin (Module.finrank ℚ K - 1) → ℝ :=
    fun k => Sum.elim c' θ (mixedCubeEquiv K k) with hc
  -- the modulus input recovers c'
  have hproj : (fun i => c ((mixedCubeEquiv K).symm (Sum.inl i))) = c' := by
    funext i; rw [hc]; simp
  refine Set.mem_iUnion.mpr ⟨ε, c, ⟨fun k => ?_, fun k => ?_⟩, ?_⟩
  · -- 0 ≤ c k
    change (0 : ℝ) ≤ Sum.elim c' θ (mixedCubeEquiv K k)
    rcases (mixedCubeEquiv K k) with i | w
    · exact hc'.1 i
    · exact (hθmem w).1
  · -- c k ≤ 1
    change Sum.elim c' θ (mixedCubeEquiv K k) ≤ (1 : ℝ)
    rcases (mixedCubeEquiv K k) with i | w
    · exact hc'.2 i
    · exact (hθmem w).2
  · -- liftToMixed K ψ ε c = x
    rw [liftToMixed, hproj]
    -- the phase coordinate recovers θ
    have hcph : ∀ w : {w : InfinitePlace K // IsComplex w},
        c ((mixedCubeEquiv K).symm (Sum.inr w)) = θ w := fun w => by rw [hc]; simp
    -- modulus values are the place-norms of x
    have hmodreal : ∀ w : {w : InfinitePlace K // IsReal w}, ψ c' w.1 = |x.1 w| := fun w => by
      rw [← hx, normAtAllPlaces_apply, normAtPlace_apply_of_isReal w.2, ← Real.norm_eq_abs]
    have hmodcplx : ∀ w : {w : InfinitePlace K // IsComplex w}, ψ c' w.1 = ‖x.2 w‖ :=
      fun w => by rw [← hx, normAtAllPlaces_apply, normAtPlace_apply_of_isComplex w.2]
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · -- real coordinate: ±|x.1 w| = x.1 w
      simp only [hε, hmodreal w]
      by_cases hpos : 0 ≤ x.1 w
      · rw [decide_eq_true hpos, if_pos rfl, one_mul, abs_of_nonneg hpos]
      · rw [decide_eq_false hpos, if_neg (by simp), abs_of_neg (not_le.mp hpos)]; ring
    · -- complex coordinate: (‖x.2 w‖ : ℂ) · exp(...) = x.2 w
      simp only [hcph w, hmodcplx w]
      exact hθeq w

/-- The frontier of `normLeOne K` in `mixedSpace K` is contained in the `normAtAllPlaces`-preimage
of the frontier of its `realSpace` image: `normLeOne K` is the preimage of its image
(`normLeOne_eq_preimage_image`), and `normAtAllPlaces` is continuous, so
`frontier (f ⁻¹' s) ⊆ f ⁻¹' (frontier s)` (`Continuous.frontier_preimage_subset`). -/
theorem frontier_normLeOne_subset_preimage :
    frontier (normLeOne K) ⊆
      normAtAllPlaces ⁻¹' frontier (normAtAllPlaces '' normLeOne K) := by
  conv_lhs => rw [normLeOne_eq_preimage_image K]
  exact (continuous_normAtAllPlaces K).frontier_preimage_subset _

open Classical MeasureTheory in
/-- **The Lipschitz cover of the frontier of `normLeOne K` in `mixedSpace K`.** Lifting the
`realSpace` frontier cover (`normLeOne_frontier_lipschitz_cover`) along the fibres of
`normAtAllPlaces`: the real-place signs are folded into a finite index together with the existing
faces, and the complex-place phases supply the extra `r₂` cube coordinates, giving
`(r − 1) + r₂ = d − 1` coordinates (`d = finrank ℚ K`). This is the `mixedSpace`-level boundary
regularity needed for the lattice-point count in the mixed embedding. -/
theorem normLeOne_frontier_lipschitz_cover_mixedSpace :
    ∃ (m : ℕ) (M : ℝ≥0)
      (φ : Fin m → (Fin (Module.finrank ℚ K - 1) → ℝ) → mixedSpace K),
      (∀ j, LipschitzWith M (φ j)) ∧
        frontier (normLeOne K) ⊆ ⋃ j, φ j '' Icc 0 1 := by
  classical
  obtain ⟨M₀, hM₀⟩ := exists_lipschitzWith_frontierCoverFamily K
  obtain ⟨B, hB⟩ := exists_bound_frontierCoverFamily K
  -- index over (faces) × (real-place sign patterns)
  set S := (Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool)) ×
    ({w : InfinitePlace K // IsReal w} → Bool) with hS
  set Φ : S → (Fin (Module.finrank ℚ K - 1) → ℝ) → mixedSpace K :=
    fun p => liftToMixed K (frontierCoverFamily K p.1) p.2 with hΦ
  have hΦlip : ∀ p, LipschitzWith (M₀ + (B * (2 * Real.pi)).toNNReal) (Φ p) := fun p =>
    lipschitzWith_liftToMixed (hψ := hM₀ p.1) (hB := hB p.1) (ε := p.2)
  -- coverage of the frontier by the cube images of Φ
  have hcover : frontier (normLeOne K) ⊆ ⋃ p, Φ p '' Icc 0 1 := by
    refine (frontier_normLeOne_subset_preimage K).trans ?_
    refine (Set.preimage_mono (frontier_subset_frontierCoverFamily K)).trans ?_
    rw [Set.preimage_iUnion]
    refine Set.iUnion_subset fun s => ?_
    rintro x ⟨c', hc', hxeq⟩
    obtain ⟨ε, hε⟩ := Set.mem_iUnion.mp
      (mem_iUnion_image_liftToMixed_of_eq (ψ := frontierCoverFamily K s) (c' := c')
        (hc' := hc') (x := x) (hx := hxeq.symm))
    exact Set.mem_iUnion.mpr ⟨(s, ε), hε⟩
  -- reindex S by Fin (card S)
  set e := Fintype.equivFin S
  refine ⟨_, M₀ + (B * (2 * Real.pi)).toNNReal, fun j => Φ (e.symm j), fun j => hΦlip _, ?_⟩
  rw [e.symm.surjective.iUnion_comp fun p => Φ p '' Icc 0 1]
  exact hcover

end Chebotarev
