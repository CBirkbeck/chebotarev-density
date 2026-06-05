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
  sorry

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
  sorry

open scoped Classical in
theorem contDiff_faceMapSide (i : {w : InfinitePlace K // w ≠ w₀}) (a : ℝ) :
    ContDiff ℝ 1 (faceMapSide K i a) := by
  sorry

/-! ### The frontier is contained in the face images -/

/-- **Topological reduction.** Since `expMapBasis` is open and injective with source `univ`,
the frontier of `expMapBasis '' paramSet K` is contained in the image of the box boundary
`closure (paramSet K) \ interior (paramSet K)`, together with `{0}` (the escape to norm `0`):
`closure (expMapBasis '' paramSet K) ⊆ compactSet K = expMapBasis '' closure (paramSet K) ∪ {0}`
while `expMapBasis '' interior (paramSet K)` is open, hence inside the interior. -/
theorem frontier_image_paramSet_subset :
    frontier (expMapBasis '' paramSet K) ⊆
      expMapBasis '' (closure (paramSet K) \ interior (paramSet K)) ∪ {0} := by
  sorry

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
  sorry

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
  sorry

end Chebotarev
