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
  -- Relabel the cube coordinates by the non-distinguished places (`rank K = r - 1`).
  set e : Fin (Fintype.card (InfinitePlace K) - 1) ≃ {w : InfinitePlace K // w ≠ w₀} :=
    equivFinRank with he
  set ρ : (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) →
      ({w : InfinitePlace K // w ≠ w₀} → ℝ) := fun c j => c (e.symm j) with hρ
  have hρ_lip : LipschitzWith 1 ρ := LipschitzWith.of_edist_le fun c d => by
    rw [hρ, edist_pi_def]
    exact Finset.sup_le fun j _ => edist_le_pi_edist c d (e.symm j)
  have hρ_mem : ∀ c ∈ Icc (0 : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) 1,
      ρ c ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 :=
    fun c hc => ⟨fun j => hc.1 _, fun j => hc.2 _⟩
  have hρ_surj : ∀ c' ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1,
      ∃ c ∈ Icc (0 : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) 1, ρ c = c' := by
    intro c' hc'
    refine ⟨fun j => c' (e j), ⟨fun j => hc'.1 _, fun j => hc'.2 _⟩, ?_⟩
    funext j
    rw [hρ]
    simp
  -- The Lipschitz constants of the clamped face maps, and their common bound `M`.
  obtain ⟨M₀, hM₀⟩ := exists_lipschitzWith_comp_clampUnit (contDiff_faceMapZero K)
  choose Ms hMs using fun p : {w : InfinitePlace K // w ≠ w₀} × Bool =>
    exists_lipschitzWith_comp_clampUnit (contDiff_faceMapSide K p.1 (if p.2 then 1 else 0))
  set M : ℝ≥0 := M₀ ⊔ Finset.univ.sup Ms with hM
  -- The family: the zero map, the `w₀`-face map, and the side-face maps.
  set fam : (Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool)) →
      (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K :=
    Sum.elim (fun _ _ => 0)
      (Sum.elim (fun _ => faceMapZero K ∘ clampUnit _ ∘ ρ)
        (fun p => faceMapSide K p.1 (if p.2 then 1 else 0) ∘ clampUnit _ ∘ ρ)) with hfam
  refine ⟨Fintype.card (Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool)), M,
    fam ∘ (Fintype.equivFin _).symm, fun j => ?_, ?_⟩
  · -- Every member of the family is `M`-Lipschitz.
    change LipschitzWith M (fam ((Fintype.equivFin _).symm j))
    generalize (Fintype.equivFin _).symm j = x
    rcases x with _ | _ | p
    · exact (LipschitzWith.const _).weaken zero_le
    · exact (hM₀.comp hρ_lip).weaken (by rw [mul_one, hM]; exact le_sup_left)
    · exact ((hMs p).comp hρ_lip).weaken
        (by rw [mul_one, hM]; exact le_sup_of_le_right (Finset.le_sup (Finset.mem_univ p)))
  · -- The coverage chain: frontier → box boundary image ∪ {0} → face images → the family.
    rw [normAtAllPlaces_normLeOne_eq_image]
    refine (frontier_image_paramSet_subset K).trans
      (Set.union_subset ((image_boundary_subset_faces K).trans (Set.union_subset ?_ ?_)) ?_)
    · -- the `w₀`-face piece, via the index `inr (inl ())`
      rintro x ⟨c', hc', rfl⟩
      obtain ⟨c, hc, rfl⟩ := hρ_surj c' hc'
      refine Set.mem_iUnion.mpr ⟨Fintype.equivFin _ (Sum.inr (Sum.inl ())), c, hc, ?_⟩
      change fam ((Fintype.equivFin _).symm (Fintype.equivFin _ _)) c = _
      rw [Equiv.symm_apply_apply, hfam]
      change faceMapZero K (clampUnit _ (ρ c)) = faceMapZero K (ρ c)
      rw [clampUnit_eq_self (hρ_mem c hc)]
    · -- the side-face pieces, via the indices `inr (inr (i, b))`
      rintro x hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨i, hx⟩ := hx
      rw [Set.mem_iUnion₂] at hx
      obtain ⟨a, ha, c', hc', rfl⟩ := hx
      obtain ⟨c, hc, rfl⟩ := hρ_surj c' hc'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      have hb : ∃ b : Bool, (if b then (1 : ℝ) else 0) = a := by
        rcases ha with rfl | rfl
        · exact ⟨false, rfl⟩
        · exact ⟨true, rfl⟩
      obtain ⟨b, rfl⟩ := hb
      refine Set.mem_iUnion.mpr ⟨Fintype.equivFin _ (Sum.inr (Sum.inr (i, b))), c, hc, ?_⟩
      change fam ((Fintype.equivFin _).symm (Fintype.equivFin _ _)) c = _
      rw [Equiv.symm_apply_apply, hfam]
      change faceMapSide K i (if b then (1 : ℝ) else 0) (clampUnit _ (ρ c)) = _
      rw [clampUnit_eq_self (hρ_mem c hc)]
    · -- the `{0}` piece, via the zero map at index `inl ()`
      rintro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      refine Set.mem_iUnion.mpr ⟨Fintype.equivFin _ (Sum.inl ()), 0, ⟨le_rfl, ?_⟩, ?_⟩
      · exact fun _ => zero_le_one
      · change fam ((Fintype.equivFin _).symm (Fintype.equivFin _ _)) 0 = 0
        rw [Equiv.symm_apply_apply, hfam]
        rfl

end Chebotarev
