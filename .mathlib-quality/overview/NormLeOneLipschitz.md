# Inventory: `CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean`

**File path**: `/Users/mcu22seu/Documents/GitHub/chebotarev-density/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean`

Module header: `module` / `public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne`; whole file under `@[expose] public section`, `noncomputable section`, `namespace Chebotarev`. Opens `NumberField`, `NumberField.InfinitePlace`, `NumberField.mixedEmbedding`, `…fundamentalCone`, `NumberField.Units`, `dirichletUnitTheorem`, `Set`, and `open scoped NNReal`. A single `variable (K : Type*) [Field K] [NumberField K]` (line 98) governs everything from there down. Several declarations carry a local `open scoped Classical in`.

**Goal of the file** (from the module docstring, lines 5–40): produce the quantitative boundary regularity needed by the effective lattice-point count — the frontier of `normAtAllPlaces '' (normLeOne K)` (and, lifted, of `normLeOne K` itself, and transported, of `(stdBasis K).equivFunL '' normLeOne K`) is covered by **finitely many Lipschitz images of the unit cube** `[0,1]^{r-1}`. This is the Gun–Ramaré–Sivaraman §3.3 / Debaene / Widmer–Lang "Lipschitz boundary" input. The engine is mathlib's parametrization `normAtAllPlaces '' (normLeOne K) = expMapBasis '' (paramSet K)`.

---

### `def clampUnit`
- **Type**: `(ι : Type*) → (ι → ℝ) → (ι → ℝ)`, defined as `fun i =&gt; max 0 (min 1 (c i))`.
- **What**: Coordinatewise retraction of the function space `ι → ℝ` onto the unit cube `Icc 0 1` (clamp each coordinate into `[0,1]`).
- **How**: Direct formula; nests `min 1 ·` inside `max 0 ·`.
- **Hypotheses**: None (`ι` arbitrary).
- **Uses from project**: []
- **Used by**: `clampUnit_mem_Icc`, `clampUnit_eq_self`, `lipschitzWith_clampUnit`, `exists_lipschitzWith_comp_clampUnit`, `frontierCoverFamily`, `frontier_subset_frontierCoverFamily`, `exists_bound_frontierCoverFamily`.
- **Visibility**: public (in `@[expose] public section`).
- **Lines**: 59–60.
- **Notes**: —

### `theorem clampUnit_mem_Icc`
- **Type**: `∀ (ι : Type*) (c : ι → ℝ), clampUnit ι c ∈ Icc (0 : ι → ℝ) 1`.
- **What**: The clamped point always lies in the unit cube.
- **How**: Pointwise: lower bound `0 ≤ max 0 _` by `le_max_left`; upper bound `max 0 (min 1 _) ≤ 1` by `max_le zero_le_one (min_le_left …)`.
- **Hypotheses**: None.
- **Uses from project**: [`clampUnit`]
- **Used by**: `exists_lipschitzWith_comp_clampUnit`, `exists_bound_frontierCoverFamily`.
- **Visibility**: public.
- **Lines**: 62–63.
- **Notes**: —

### `theorem clampUnit_eq_self`
- **Type**: `{ι : Type*} {c : ι → ℝ} → c ∈ Icc (0 : ι → ℝ) 1 → clampUnit ι c = c`.
- **What**: The clamp is the identity on points already inside the cube.
- **How**: `funext i`; extract `0 ≤ c i` and `c i ≤ 1` from membership, then rewrite `min_eq_right h2` and `max_eq_right h1` to collapse the clamp.
- **Hypotheses**: `c ∈ Icc 0 1` (each coordinate in `[0,1]`).
- **Uses from project**: [`clampUnit`]
- **Used by**: `frontier_subset_frontierCoverFamily`.
- **Visibility**: public.
- **Lines**: 65–70.
- **Notes**: —

### `theorem lipschitzWith_clampUnit`
- **Type**: `(ι : Type*) [Fintype ι] → LipschitzWith 1 (clampUnit ι)`.
- **What**: The cube clamp is `1`-Lipschitz in the sup metric on `ι → ℝ`.
- **How**: `LipschitzWith.of_dist_le_mul`; reduce to per-coordinate via `dist_pi_le_iff`, bound by `dist_le_pi_dist`; rewrite each side with `Real.dist_eq`; after `max_comm`, chain `abs_max_sub_max_le_abs` (Lipschitzness of `max`) with `abs_min_sub_min_le_max` (Lipschitzness of `min`) and `abs_sub_comm`.
- **Hypotheses**: `Fintype ι` (finite product so the sup metric / `dist_pi` API applies).
- **Uses from project**: [`clampUnit`]
- **Used by**: `exists_lipschitzWith_comp_clampUnit`.
- **Visibility**: public.
- **Lines**: 72–81.
- **Notes**: —

### `theorem exists_lipschitzWith_comp_clampUnit`
- **Type**: `{ι κ : Type*} [Fintype ι] [Fintype κ] {f : (ι → ℝ) → κ → ℝ} → ContDiff ℝ 1 f → ∃ M : ℝ≥0, LipschitzWith M (f ∘ clampUnit ι)`.
- **What**: A globally `C¹` map precomposed with the cube clamp is globally Lipschitz (with the cube image of `f` unchanged, as remarked in the docstring).
- **How**: `f` is locally Lipschitz (`ContDiff.locallyLipschitz`), hence locally Lipschitz on the cube; by **compactness of the cube** `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc` yields a constant `M` with `f` `M`-Lipschitz on `Icc 0 1`. Since `clampUnit` always lands in the cube (`clampUnit_mem_Icc`) and is `1`-Lipschitz (`lipschitzWith_clampUnit`), a two-step `edist` `calc` (`gcongr` for the product) gives `edist (f(clamp c)) (f(clamp d)) ≤ M · edist c d`.
- **Hypotheses**: `f` is `ContDiff ℝ 1`; `ι, κ` finite (sup-metric products; cube compactness).
- **Uses from project**: [`clampUnit`, `clampUnit_mem_Icc`, `lipschitzWith_clampUnit`]
- **Used by**: `exists_lipschitzWith_frontierCoverFamily`.
- **Visibility**: public.
- **Lines**: 83–98 (body 86–98, 13 lines).
- **Notes**: —

### `theorem contDiff_expMapBasis`
- **Type**: `ContDiff ℝ 1 (⇑(expMapBasis (K := K)))`.
- **What**: mathlib's `expMapBasis : realSpace K → realSpace K` is `C¹`.
- **How**: Rewrite `expMapBasis x = exp(x w₀) • (fun w =&gt; ∏ i, w (fundSystem K (equivFinRank.symm i)) ^ x i)` via mathlib's `expMapBasis_apply'`. The scalar factor is `Real.contDiff_exp.comp (contDiff_apply ℝ _ w₀)` (smooth `exp` of a coordinate). The vector factor is smooth componentwise (`contDiff_pi`) and as a finite product (`contDiff_prod`); each factor is a constant base raised to a coordinate power, smooth by `ContDiff.rpow` of `contDiff_const` and `contDiff_apply`, where positivity of the base `w (fundSystem K …) &gt; 0` (via `InfinitePlace.pos_iff`) lets `rpow` be `C¹`.
- **Hypotheses**: number field `K` (from the `variable` line).
- **Uses from project**: []
- **Used by**: `contDiff_faceMapZero`, `contDiff_faceMapSide`.
- **Visibility**: public.
- **Lines**: 100–116 (body 106–116, 11 lines).
- **Notes**: `classical`. Relies on mathlib `expMapBasis_apply'`, `equivFinRank`, `fundSystem`.

### `def faceMapZero`
- **Type**: `({w : InfinitePlace K // w ≠ w₀} → ℝ) → realSpace K`, `c ↦ expMapBasis (fun w =&gt; if w = w₀ then 0 else c ⟨w,_⟩)`.
- **What**: Parametrizes the `expMapBasis`-image of the `w₀`-face `{x | x w₀ = 0}` of `paramSet K`: plug `0` into the `w₀`-slot, cube coordinates elsewhere.
- **How**: Direct: compose `expMapBasis` with the coordinate-insertion `fun w =&gt; if w = w₀ then 0 else c ⟨w,_⟩`.
- **Hypotheses**: number field `K`.
- **Uses from project**: []
- **Used by**: `contDiff_faceMapZero`, `image_boundary_subset_faces`, `frontierCoverFamily`, `frontier_subset_frontierCoverFamily`, `exists_bound_frontierCoverFamily`.
- **Visibility**: public.
- **Lines**: 120–124.
- **Notes**: `open scoped Classical in` (for the `dite`).

### `def faceMapSide`
- **Type**: `(i : {w // w ≠ w₀}) → (a : ℝ) → ({w // w ≠ w₀} → ℝ) → realSpace K`, `c ↦ (c i) • expMapBasis (fun w =&gt; if w = w₀ then 0 else if ⟨w,_⟩ = i then a else c ⟨w,_⟩)`.
- **What**: Parametrizes the `expMapBasis`-image of a side face `{x | x i = a}` (`i ≠ w₀`, `a ∈ {0,1}`). The unbounded `w₀`-direction (`Iic 0`) is linearized via the substitution `t = exp(x w₀) ∈ (0,1]`, which becomes the freed cube slot `c i`; the scalar `c i` is that `t`.
- **How**: Direct formula using `expMapBasis_apply''` (`expMapBasis x = exp(x w₀) • expMapBasis (x[w₀↦0])`), with `t = c i` factored out as the leading scalar and the face value `a` pinned in slot `i`.
- **Hypotheses**: number field `K`; index `i`, level `a`.
- **Uses from project**: []
- **Used by**: `contDiff_faceMapSide`, `image_boundary_subset_faces`, `frontierCoverFamily`, `frontier_subset_frontierCoverFamily`, `exists_bound_frontierCoverFamily`.
- **Visibility**: public.
- **Lines**: 126–135.
- **Notes**: `open scoped Classical in`.

### `theorem contDiff_faceMapZero`
- **Type**: `ContDiff ℝ 1 (faceMapZero K)`.
- **What**: The `w₀`-face parametrization is `C¹`.
- **How**: `(contDiff_expMapBasis K).comp` of the coordinate-insertion map, which is smooth componentwise (`contDiff_pi`): the `w₀` slot is `contDiff_const`, every other slot is `contDiff_apply` (a projection); `by_cases hw : w = w₀` discharges the `dite`.
- **Hypotheses**: number field `K`.
- **Uses from project**: [`contDiff_expMapBasis`, `faceMapZero`]
- **Used by**: `exists_lipschitzWith_frontierCoverFamily`, `exists_bound_frontierCoverFamily`.
- **Visibility**: public.
- **Lines**: 137–144 (body 138–144, 7 lines).
- **Notes**: `open scoped Classical in`.

### `theorem contDiff_faceMapSide`
- **Type**: `(i : {w // w ≠ w₀}) → (a : ℝ) → ContDiff ℝ 1 (faceMapSide K i a)`.
- **What**: Every side-face parametrization is `C¹`.
- **How**: `(contDiff_apply ℝ ℝ i).smul` (the leading scalar `c i` is smooth) of `(contDiff_expMapBasis K).comp` of the insertion map; the insertion map is smooth slotwise via nested `by_cases` (`w = w₀` → const; else `⟨w,_⟩ = i` → const `a`; else projection `contDiff_apply`).
- **Hypotheses**: number field `K`; `i`, `a`.
- **Uses from project**: [`contDiff_expMapBasis`, `faceMapSide`]
- **Used by**: `exists_lipschitzWith_frontierCoverFamily`, `exists_bound_frontierCoverFamily`.
- **Visibility**: public.
- **Lines**: 146–158 (body 147–158, 12 lines).
- **Notes**: `open scoped Classical in`.

### `theorem frontier_image_paramSet_subset`
- **Type**: `frontier (expMapBasis '' paramSet K) ⊆ expMapBasis '' (closure (paramSet K) \ interior (paramSet K)) ∪ {0}`.
- **What**: **Topological reduction.** The frontier of the parametrized region is contained in the `expMapBasis`-image of the box boundary `closure \ interior`, plus the single escape point `{0}` (norm → 0 as the `w₀`-coordinate → −∞).
- **How**: Three steps. (i) `closure (expMapBasis '' paramSet K) ⊆ compactSet K`: `compactSet K` is closed (`isCompact_compactSet`), and `expMapBasis '' paramSet ⊆ expMapBasis '' closure ⊆ compactSet` via `expMapBasis_closure_subset_compactSet`, so `closure_subset_iff` applies. (ii) `expMapBasis '' interior (paramSet K)` is open since `expMapBasis` is open on its source `univ` (`expMapBasis.isOpen_image_of_subset_source` with `expMapBasis_source`), hence `⊆ interior (expMapBasis '' paramSet)` (`IsOpen.subset_interior_iff`). (iii) `frontier = closure \ interior`, so `frontier ⊆ compactSet K \ (expMapBasis '' interior)` by `Set.diff_subset_diff`; finally `compactSet_eq_union`, `Set.union_diff_distrib`, and `Set.image_diff (injective_expMapBasis K)` rewrite the right side into the claimed `image (closure \ interior) ∪ {0}`.
- **Hypotheses**: number field `K`.
- **Uses from project**: []
- **Used by**: `frontier_subset_frontierCoverFamily`.
- **Visibility**: public.
- **Lines**: 162–186 (body 167–186, 20 lines).
- **Notes**: Heavy reliance on mathlib `compactSet`/`expMapBasis` API: `isCompact_compactSet`, `expMapBasis_closure_subset_compactSet`, `expMapBasis.isOpen_image_of_subset_source`, `expMapBasis_source`, `compactSet_eq_union`, `injective_expMapBasis`.

### `theorem image_boundary_subset_faces`
- **Type**: `expMapBasis '' (closure (paramSet K) \ interior (paramSet K)) ⊆ faceMapZero K '' Icc 0 1 ∪ ⋃ i, ⋃ a ∈ {0,1}, faceMapSide K i a '' Icc 0 1`.
- **What**: **Face covering.** Every image-of-box-boundary point lies in a face parametrization's cube image: a boundary point has `x w₀ = 0` (→ `faceMapZero`) or `x i ∈ {0,1}` for some `i ≠ w₀` (→ `faceMapSide i a`, via `t = exp(x w₀)`).
- **How**: Take a boundary point `expMapBasis y` with `y ∈ closure \ interior`. Rewrite membership via `closure_paramSet`/`interior_paramSet` (`Set.mem_univ_pi`): closure gives `y w₀ ≤ 0` and `y v ∈ [0,1]` for `v ≠ w₀`; failure of interior membership (`push Not`) yields a witness coordinate `w` not in the open box at `w`. `by_cases w = w₀`: **(a)** then `y w₀ = 0` (antisymmetry of `≤`), and the point is `faceMapZero K (fun i =&gt; y i.1)` — `funext` + `dite` case-split closes it. **(b)** else `y w ∈ {0,1}` (from `y w ∈ [0,1]` and the failed open condition `Ioo`, via `not_and_or`/`le_antisymm`); set `i = ⟨w,_⟩` and cube point `c j = if j = i then exp(y w₀) else y j.1`, which lies in the cube (`exp_nonneg`, `exp_le_one_iff` from `y w₀ ≤ 0`); the **key identity** `faceMapSide K i (y w) c = expMapBasis y` is proved by `expMapBasis_apply'' y`, `c i = exp(y w₀)`, and a `funext`-collapse of the nested `dite/ite` to `fun w' =&gt; if w' = w₀ then 0 else y w'`. Conclude with `Set.mem_iUnion`/`mem_iUnion₂`.
- **Hypotheses**: number field `K`.
- **Uses from project**: [`faceMapZero`, `faceMapSide`]
- **Used by**: `frontier_subset_frontierCoverFamily`.
- **Visibility**: public.
- **Lines**: 188–257 (body 193–257, **65 lines**).
- **Notes**: **&gt;30 lines.** `classical`. Uses mathlib `closure_paramSet`, `interior_paramSet`, `expMapBasis_apply''`.

### `def cubeRelabel`
- **Type**: `(Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → ({w : InfinitePlace K // w ≠ w₀} → ℝ)`, `c ↦ fun j =&gt; c (equivFinRank.symm j)`.
- **What**: Relabels cube coordinates indexed by `Fin (r-1)` to the non-distinguished places `{w ≠ w₀}` via the equivalence `equivFinRank`.
- **How**: Direct precomposition with `equivFinRank.symm`.
- **Hypotheses**: number field `K`.
- **Uses from project**: []
- **Used by**: `lipschitzWith_cubeRelabel`, `cubeRelabel_mem_Icc`, `exists_cubeRelabel_eq`, `frontierCoverFamily`, `frontier_subset_frontierCoverFamily`, `exists_bound_frontierCoverFamily`.
- **Visibility**: public.
- **Lines**: 267–271.
- **Notes**: `equivFinRank` is mathlib (Dirichlet unit theorem rank equiv).

### `theorem lipschitzWith_cubeRelabel`
- **Type**: `LipschitzWith 1 (cubeRelabel K)`.
- **What**: The relabelling is a `1`-Lipschitz isometry-like map (it just permutes/selects coordinates).
- **How**: `LipschitzWith.of_edist_le`; unfold `cubeRelabel` and `edist_pi_def`, then `Finset.sup_le` reduces to `edist_le_pi_edist c d (equivFinRank.symm j)` per coordinate.
- **Hypotheses**: number field `K`.
- **Uses from project**: [`cubeRelabel`]
- **Used by**: `exists_lipschitzWith_frontierCoverFamily`.
- **Visibility**: public.
- **Lines**: 273–277 (body 274–277, 4 lines).
- **Notes**: `open scoped Classical in`.

### `theorem cubeRelabel_mem_Icc`
- **Type**: `{c : Fin (card (InfinitePlace K) - 1) → ℝ} → c ∈ Icc 0 1 → cubeRelabel K c ∈ Icc 0 1`.
- **What**: Relabelling maps the unit cube into the unit cube.
- **How**: Coordinatewise: each relabelled coordinate is some original coordinate, so the bounds `hc.1 _`, `hc.2 _` transfer directly.
- **Hypotheses**: `c ∈ Icc 0 1`.
- **Uses from project**: [`cubeRelabel`]
- **Used by**: `frontier_subset_frontierCoverFamily`.
- **Visibility**: public.
- **Lines**: 279–282.
- **Notes**: —

### `theorem exists_cubeRelabel_eq`
- **Type**: `{c' : {w // w ≠ w₀} → ℝ} → c' ∈ Icc 0 1 → ∃ c ∈ Icc 0 1, cubeRelabel K c = c'`.
- **What**: `cubeRelabel` is onto the unit cube: any cube point over `{w ≠ w₀}` is the relabelling of a cube point over `Fin (r-1)`.
- **How**: Witness `c j := c' (equivFinRank j)`; bounds transfer coordinatewise; `cubeRelabel K c = c'` by `funext` + `simp [cubeRelabel]` (using `equivFinRank.symm ∘ equivFinRank = id`).
- **Hypotheses**: `c' ∈ Icc 0 1`.
- **Uses from project**: [`cubeRelabel`]
- **Used by**: `frontier_subset_frontierCoverFamily`.
- **Visibility**: public.
- **Lines**: 284–288.
- **Notes**: —

### `def frontierCoverFamily`
- **Type**: `(Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool)) → (Fin (card (InfinitePlace K) - 1) → ℝ) → realSpace K`.
- **What**: The finite family covering the `realSpace` frontier: index `inl ()` → the constant zero map; `inr (inl ())` → the `w₀`-face map `faceMapZero`; `inr (inr (i,b))` → side-face map `faceMapSide i a` with `a = if b then 1 else 0`. Each non-zero member is post-clamped (`clampUnit`) and relabelled (`cubeRelabel`).
- **How**: Two nested `Sum.elim`s: zero branch `fun _ _ =&gt; 0`; `faceMapZero K ∘ clampUnit _ ∘ cubeRelabel K`; and `fun p =&gt; faceMapSide K p.1 (if p.2 then 1 else 0) ∘ clampUnit _ ∘ cubeRelabel K`.
- **Hypotheses**: number field `K`.
- **Uses from project**: [`faceMapZero`, `faceMapSide`, `clampUnit`, `cubeRelabel`]
- **Used by**: `exists_lipschitzWith_frontierCoverFamily`, `frontier_subset_frontierCoverFamily`, `exists_bound_frontierCoverFamily`, `normLeOne_frontier_lipschitz_cover`, `normLeOne_frontier_lipschitz_cover_mixedSpace`.
- **Visibility**: public.
- **Lines**: 290–299.
- **Notes**: The index type folds three families (zero / `w₀`-face / side faces) into one finite sum type.

### `theorem exists_lipschitzWith_frontierCoverFamily`
- **Type**: `∃ M : ℝ≥0, ∀ s, LipschitzWith M (frontierCoverFamily K s)`.
- **What**: All members of the cover family are `M`-Lipschitz for one common constant `M`.
- **How**: Get a constant `M₀` for the `w₀`-face (`exists_lipschitzWith_comp_clampUnit (contDiff_faceMapZero K)`); `choose` a constant `Ms p` for each side face (`exists_lipschitzWith_comp_clampUnit (contDiff_faceMapSide …)`). Take `M = M₀ ⊔ Finset.univ.sup Ms`. Per index: zero map is `(LipschitzWith.const _).weaken zero_le`; the face maps are `(constant).comp (lipschitzWith_cubeRelabel K)` then `.weaken` (since precomposing with the `1`-Lipschitz relabel keeps the constant, `mul_one`), bounding by `le_sup_left` resp. `Finset.le_sup`.
- **Hypotheses**: number field `K`.
- **Uses from project**: [`frontierCoverFamily`, `exists_lipschitzWith_comp_clampUnit`, `contDiff_faceMapZero`, `contDiff_faceMapSide`, `lipschitzWith_cubeRelabel`]
- **Used by**: `normLeOne_frontier_lipschitz_cover`, `normLeOne_frontier_lipschitz_cover_mixedSpace`.
- **Visibility**: public.
- **Lines**: 301–316 (body 305–316, 12 lines).
- **Notes**: `classical`.

### `theorem frontier_subset_frontierCoverFamily`
- **Type**: `frontier (normAtAllPlaces '' normLeOne K) ⊆ ⋃ s, frontierCoverFamily K s '' Icc 0 1`.
- **What**: The `realSpace`-frontier of the norm-≤1 region is covered by the cube images of `frontierCoverFamily`.
- **How**: Rewrite the region with `normAtAllPlaces_normLeOne_eq_image` (`= expMapBasis '' paramSet K`). Then chain `frontier_image_paramSet_subset` (→ box-image `∪ {0}`) with `image_boundary_subset_faces` (→ face images), and `Set.union_subset` into three obligations: **(i)** a `faceMapZero` cube point — undo relabel via `exists_cubeRelabel_eq`, land in index `inr (inl ())`, and `clampUnit_eq_self (cubeRelabel_mem_Icc …)` removes the clamp; **(ii)** a `faceMapSide i a` cube point — destructure the `⋃ i ⋃ a∈{0,1}`, convert `a` to `if b then 1 else 0` for a `Bool b`, land in `inr (inr (i,b))`, again `clampUnit_eq_self`; **(iii)** `{0}` — the value of the zero map at index `inl ()`.
- **Hypotheses**: number field `K`.
- **Uses from project**: [`frontierCoverFamily`, `frontier_image_paramSet_subset`, `image_boundary_subset_faces`, `exists_cubeRelabel_eq`, `cubeRelabel_mem_Icc`, `clampUnit_eq_self`, `faceMapZero`, `faceMapSide`, `clampUnit`, `cubeRelabel`]
- **Used by**: `normLeOne_frontier_lipschitz_cover`, `normLeOne_frontier_lipschitz_cover_mixedSpace`.
- **Visibility**: public.
- **Lines**: 318–353 (body 324–353, **30 lines**).
- **Notes**: Proof body exactly 30 lines (not &gt;30). `classical`. Uses mathlib `normAtAllPlaces_normLeOne_eq_image`.

### `theorem normLeOne_frontier_lipschitz_cover`
- **Type**: `∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (card (InfinitePlace K) - 1) → ℝ) → realSpace K), (∀ j, LipschitzWith M (φ j)) ∧ frontier (normAtAllPlaces '' normLeOne K) ⊆ ⋃ j, φ j '' Icc 0 1`.
- **What**: **Main `realSpace`-level statement.** Finitely many `M`-Lipschitz maps from `[0,1]^{r-1}` whose cube images cover the frontier of `normAtAllPlaces '' normLeOne K` — the exact `hlip` shape for the lattice-point count.
- **How**: Take `M` from `exists_lipschitzWith_frontierCoverFamily`; reindex the sum-typed family by `Fin (card …)` via `Fintype.equivFin`; transport the union with `e.symm.surjective.iUnion_comp` and discharge the inclusion with `frontier_subset_frontierCoverFamily`.
- **Hypotheses**: number field `K`.
- **Uses from project**: [`exists_lipschitzWith_frontierCoverFamily`, `frontierCoverFamily`, `frontier_subset_frontierCoverFamily`]
- **Used by**: in-file: none. **External**: cited and used in `ZetaProduct.lean` (line 808) and `ForMathlib/IdealCongruenceCount.lean` (docstrings) as the named "Gap A" input.
- **Visibility**: public.
- **Lines**: 357–373 (body 362–373, 12 lines).
- **Notes**: `classical`. This is the headline of the "frontier cover" PR-candidate.

### `theorem lipschitzWith_exp_ofReal_mul_I`
- **Type**: `LipschitzWith 1 (fun t : ℝ =&gt; Complex.exp ((t : ℂ) * Complex.I))`.
- **What**: The unit-circle exponential `t ↦ e^{it}` is globally `1`-Lipschitz.
- **How**: Two analytic lemmas first. (i) `hcos : 2 - 2 cos t ≤ t²` via the half-angle identity `cos t = 1 - 2 sin²(t/2)` (from `Real.cos_add`, `Real.sin_sq_add_cos_sq`, `nlinarith`) and `sin²(t/2) ≤ (t/2)²` (from `Real.abs_sin_le_abs`, `pow_le_pow_left₀`). (ii) `hsub : ‖e^{it} - 1‖ ≤ |t|`: write `e^{it}-1 = (cos t - 1) + (sin t) i` (`Complex.exp_mul_I`), compute the norm via `Complex.normSq_add_mul_I` to `2 - 2 cos t`, rewrite `|t| = √(t²)`, and apply `Real.sqrt_le_sqrt hcos`. Finally `LipschitzWith.of_dist_le_mul`: factor `e^{iα}-e^{iβ} = e^{iβ}(e^{i(α-β)}-1)` (`Complex.exp_add`), use `Complex.norm_exp_ofReal_mul_I = 1`, and finish with `hsub (α-β)`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `lipschitzWith_phase`, `lipschitzWith_liftToMixed` (cited in docstring; the Lipschitz constant for the phase factor).
- **Visibility**: public.
- **Lines**: 391–424 (body 394–424, **31 lines**).
- **Notes**: **&gt;30 lines.** Mathlib-PR-flavoured standalone analytic lemma (no project deps). Uses `Complex.exp_mul_I`, `Complex.normSq_add_mul_I`, `Complex.norm_exp_ofReal_mul_I`, `Real.sqrt_sq_eq_abs`.

### `theorem lipschitzWith_phase`
- **Type**: `LipschitzWith (2 * Real.pi).toNNReal (fun t : ℝ =&gt; Complex.exp ((2 π t - π) * I))`.
- **What**: The phase reparametrization `θ ↦ e^{i(2πθ - π)}` is `2π`-Lipschitz.
- **How**: It is the `1`-Lipschitz unit-circle exponential composed with the affine `θ ↦ 2πθ - π`, which is `2π`-Lipschitz (`haff`: `of_dist_le_mul`, factor out `2π`, `abs_mul`, `abs_of_nonneg`). Rewrite the target as that composition (`hcomp`, via `push_cast`/`ring_nf`) and apply `lipschitzWith_exp_ofReal_mul_I.comp haff` with `one_mul` collapsing `1 · 2π`.
- **Hypotheses**: None.
- **Uses from project**: [`lipschitzWith_exp_ofReal_mul_I`]
- **Used by**: `lipschitzWith_liftToMixed`.
- **Visibility**: public.
- **Lines**: 426–445 (body 429–445, 17 lines).
- **Notes**: —

### `theorem exists_phase_mem_Icc_mul_exp`
- **Type**: `(z : ℂ) → ∃ θ ∈ Icc (0:ℝ) 1, (‖z‖ : ℂ) * Complex.exp ((2 π θ - π) * I) = z`.
- **What**: Polar form with phase in `[0,1]`: every complex `z` equals `‖z‖ · e^{i(2πθ-π)}` for some `θ ∈ [0,1]`.
- **How**: Witness `θ = (arg z + π)/(2π)`, in `[0,1]` since `arg z ∈ (-π, π]` (`Complex.neg_pi_lt_arg`, `Complex.arg_le_pi`; `div_nonneg`, `div_le_one`). The phase reduces: `2π·θ - π = arg z` (`field_simp`/`ring`), so after recasting to ℝ-then-ℂ the identity is exactly `Complex.norm_mul_exp_arg_mul_I z` (mathlib polar form `‖z‖ e^{i arg z} = z`).
- **Hypotheses**: None (`z` arbitrary; for `z = 0` it holds with `arg 0 = 0`).
- **Uses from project**: []
- **Used by**: `mem_iUnion_image_liftToMixed_of_eq`.
- **Visibility**: public.
- **Lines**: 447–462 (body 450–462, 13 lines).
- **Notes**: Uses mathlib `Complex.norm_mul_exp_arg_mul_I`, `Complex.neg_pi_lt_arg`, `Complex.arg_le_pi`.

### `noncomputable def mixedCubeEquiv`
- **Type**: `Fin (Module.finrank ℚ K - 1) ≃ Fin (Fintype.card (InfinitePlace K) - 1) ⊕ {w : InfinitePlace K // IsComplex w}`.
- **What**: The equivalence splitting the `d-1` mixed-cube coordinates (`d = finrank ℚ K`) into `r-1` "modulus" coordinates (over `Fin (card(InfinitePlace K)-1)`) plus `r₂` "phase" coordinates (one per complex place).
- **How**: `Fintype.equivOfCardEq`; the cardinality equation `(d-1) = (r-1) + r₂` is closed by `omega` from `r = r₁ + r₂` (`card_eq_nrRealPlaces_add_nrComplexPlaces`), `r₁ + 2 r₂ = d` (`card_add_two_mul_card_eq_rank`), `r ≥ 1` (`Fintype.card_pos`), and `nrComplexPlaces K = card {w // IsComplex w}` (`rfl`).
- **Hypotheses**: number field `K`.
- **Uses from project**: []
- **Used by**: `liftToMixed`, `mem_iUnion_image_liftToMixed_of_eq`.
- **Visibility**: public.
- **Lines**: 464–481 (body 470–481, 12 lines).
- **Notes**: `open scoped Classical in`. `noncomputable`. Pure cardinality bookkeeping via `omega`.

### `noncomputable def liftToMixed`
- **Type**: `(ψ : (Fin (card (InfinitePlace K) - 1) → ℝ) → realSpace K) → (ε : {w // IsReal w} → Bool) → (c : Fin (finrank ℚ K - 1) → ℝ) → mixedSpace K`.
- **What**: Lifts a `realSpace`-valued cover map `ψ` to a `mixedSpace`-valued map. Uses the first `r-1` cube coords as the modulus input to `ψ`, the last `r₂` as complex-place phases, and the sign pattern `ε` on real places. Real coord at `w`: `±(ψ …) w`; complex coord at `w`: `(ψ …) w · e^{i(2πθ_w - π)}`.
- **How**: Returns the pair: real part `fun w =&gt; (if ε w then 1 else -1) * ψ (modulus input) w.1`; complex part `fun w =&gt; (ψ (modulus input) w.1 : ℂ) * Complex.exp ((2π · c(phase slot) - π) * I)`, where modulus/phase slots are read off through `(mixedCubeEquiv K).symm (Sum.inl i)` / `(Sum.inr w)`.
- **Hypotheses**: number field `K`; cover map `ψ`, signs `ε`.
- **Uses from project**: [`mixedCubeEquiv`]
- **Used by**: `lipschitzWith_liftToMixed`, `mem_iUnion_image_liftToMixed_of_eq`, `normLeOne_frontier_lipschitz_cover_mixedSpace`.
- **Visibility**: public.
- **Lines**: 483–500 (body 491–500, 10 lines).
- **Notes**: `open scoped Classical in`. `noncomputable`. The docstring records the design invariant `normAtAllPlaces (liftToMixed ψ ε c) = ψ(…)` when moduli are nonnegative.

### `theorem lipschitzWith_liftToMixed`
- **Type**: `{ψ …} {M₀ : ℝ≥0} {B : ℝ} → LipschitzWith M₀ ψ → (∀ c, ‖ψ c‖ ≤ B) → (ε : {w // IsReal w} → Bool) → LipschitzWith (M₀ + (B * (2 * Real.pi)).toNNReal) (liftToMixed K ψ ε)`.
- **What**: If `ψ` is `M₀`-Lipschitz and bounded by `B`, its lift is globally `(M₀ + B·2π)`-Lipschitz.
- **How**: `of_dist_le_mul`. Set moduli `yc = ψ(modulus c)`, `yd = ψ(modulus d)`; the modulus map is `M₀`-Lipschitz in the cube point (`hmod`, via `hψ.dist_le_mul` + per-coordinate `dist_le_pi_dist`). `Prod.dist_eq` + `max_le` splits into real and complex blocks. **Real block** (`dist_pi_le_iff`): the sign factor `±1` is an isometry (`hsign`: `abs_mul`, `split_ifs`), so `dist ≤ dist yc yd ≤ M₀·dist c d ≤ N·dist c d`. **Complex block**: per place, with phase exponentials `uc, ud`, use the **product estimate** `dist(a·u)(b·v) ≤ ‖a‖·dist u v + ‖v‖·dist a b` (`hprod`: algebraic split `a u - b v = a(u-v) + (a-b)v`, `norm_add_le`, `norm_mul`). Bound the factors: `‖ud‖ = 1` (`Complex.norm_exp`, real part 0); `‖(yc w : ℂ)‖ ≤ B` (`ha`, via `norm_le_pi_norm` + `hB`); phase `dist uc ud ≤ 2π·dist c d` (`hphase`, from `lipschitzWith_phase.dist_le_mul` + `Real.coe_toNNReal`); modulus `dist (yc w : ℂ)(yd w : ℂ) ≤ M₀·dist c d` (`hmodc`). A final `calc` assembles `B·(2π·dist) + 1·(M₀·dist) = (M₀ + B·2π)·dist = N·dist`.
- **Hypotheses**: `ψ` is `M₀`-Lipschitz; `ψ` uniformly bounded by `B`; sign pattern `ε`. (`B ≥ 0` is derived: `hBnn` from `norm_nonneg` and `hB 0`.)
- **Uses from project**: [`liftToMixed`, `lipschitzWith_phase`]
- **Used by**: `normLeOne_frontier_lipschitz_cover_mixedSpace`.
- **Visibility**: public.
- **Lines**: 502–586 (body 508–586, **79 lines** — longest proof in the file).
- **Notes**: **&gt;30 lines.** Uses mathlib `Complex.norm_exp`, `norm_le_pi_norm`, `dist_le_pi_dist`, `Real.coe_toNNReal`, `NNReal.coe_add`.

### `theorem exists_bound_frontierCoverFamily`
- **Type**: `∃ B : ℝ, ∀ s c, ‖frontierCoverFamily K s c‖ ≤ B`.
- **What**: All members of `frontierCoverFamily` are uniformly bounded by one constant `B` (the boundedness hypothesis feeding `lipschitzWith_liftToMixed`).
- **How**: Helper `hbd`: any continuous `g` precomposed with `clampUnit ∘ cubeRelabel` is bounded, because it is only evaluated on the compact cube (`clampUnit_mem_Icc`), whose continuous image is bounded (`IsCompact.image`, `IsBounded.subset_closedBall`). Apply to `faceMapZero` (continuity from `contDiff_faceMapZero`) for `B₀` and `choose` `Bs p` for each side face (`contDiff_faceMapSide`). Take `B = ↑(B₀.toNNReal ⊔ Finset.univ.sup (Bs ·).toNNReal)`. Per index: zero map has norm `0`; the others bounded by `B₀` / `Bs p` then by the sup via `Real.le_coe_toNNReal`, `le_sup_left`, `Finset.le_sup`.
- **Hypotheses**: number field `K`.
- **Uses from project**: [`frontierCoverFamily`, `clampUnit`, `cubeRelabel`, `clampUnit_mem_Icc`, `contDiff_faceMapZero`, `contDiff_faceMapSide`]
- **Used by**: `normLeOne_frontier_lipschitz_cover_mixedSpace`.
- **Visibility**: public.
- **Lines**: 588–618 (body 592–618, 27 lines).
- **Notes**: `classical`. Uses mathlib `IsCompact.image`, `Metric.mem_closedBall`, `Real.le_coe_toNNReal`.

### `theorem mem_iUnion_image_liftToMixed_of_eq`
- **Type**: `{ψ …} {c' …} (hc' : c' ∈ Icc 0 1) {x : mixedSpace K} (hx : normAtAllPlaces x = ψ c') → x ∈ ⋃ ε : {w // IsReal w} → Bool, liftToMixed K ψ ε '' Icc 0 1`.
- **What**: **Fibre covering.** If a covered `realSpace` point `ψ c'` is `normAtAllPlaces x`, then `x` lies in the cube image of `liftToMixed K ψ ε` for the sign pattern `ε` reading the signs of `x`'s real coordinates.
- **How**: `choose` phases `θ w ∈ [0,1]` with `‖x.2 w‖ e^{i(2πθ_w-π)} = x.2 w` (`exists_phase_mem_Icc_mul_exp`). Set signs `ε w = decide (0 ≤ x.1 w)` and the full cube point `c k = Sum.elim c' θ (mixedCubeEquiv K k)`. The modulus projection recovers `c'` (`hproj`, `Sum.inl` slots). Membership of `c` in the cube is checked slotwise (`rcases (mixedCubeEquiv K k)`: `Sum.inl` → `hc'`, `Sum.inr` → `hθmem`). For `liftToMixed K ψ ε c = x` (`Prod.ext`): the moduli are the place-norms `ψ c' w = |x.1 w|` (real, `normAtPlace_apply_of_isReal`) and `= ‖x.2 w‖` (complex, `normAtPlace_apply_of_isComplex`); the **real** coordinate `±|x.1 w| = x.1 w` follows by `by_cases 0 ≤ x.1 w` with `abs_of_nonneg`/`abs_of_neg`; the **complex** coordinate is exactly `hθeq w`.
- **Hypotheses**: `c' ∈ Icc 0 1`; `normAtAllPlaces x = ψ c'`.
- **Uses from project**: [`liftToMixed`, `mixedCubeEquiv`, `exists_phase_mem_Icc_mul_exp`]
- **Used by**: `normLeOne_frontier_lipschitz_cover_mixedSpace`.
- **Visibility**: public.
- **Lines**: 620–670 (body 626–670, **45 lines**).
- **Notes**: **&gt;30 lines.** `open scoped Classical in`. Uses mathlib `normAtAllPlaces_apply`, `normAtPlace_apply_of_isReal`, `normAtPlace_apply_of_isComplex`.

### `theorem frontier_normLeOne_subset_preimage`
- **Type**: `frontier (normLeOne K) ⊆ normAtAllPlaces ⁻¹' frontier (normAtAllPlaces '' normLeOne K)`.
- **What**: The `mixedSpace` frontier of `normLeOne K` sits inside the `normAtAllPlaces`-preimage of the (already covered) `realSpace` frontier.
- **How**: `normLeOne K` is its own preimage-of-image (`normLeOne_eq_preimage_image`), so `conv_lhs` rewrites the LHS; then `(continuous_normAtAllPlaces K).frontier_preimage_subset _` gives `frontier (f ⁻¹' s) ⊆ f ⁻¹' frontier s`.
- **Hypotheses**: number field `K`.
- **Uses from project**: []
- **Used by**: `normLeOne_frontier_lipschitz_cover_mixedSpace`.
- **Visibility**: public.
- **Lines**: 672–680 (body 676–680, 5 lines).
- **Notes**: Uses mathlib `normLeOne_eq_preimage_image`, `continuous_normAtAllPlaces`, `Continuous.frontier_preimage_subset`.

### `theorem normLeOne_frontier_lipschitz_cover_mixedSpace`
- **Type**: `∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Module.finrank ℚ K - 1) → ℝ) → mixedSpace K), (∀ j, LipschitzWith M (φ j)) ∧ frontier (normLeOne K) ⊆ ⋃ j, φ j '' Icc 0 1`.
- **What**: **`mixedSpace`-level cover.** Finitely many `M`-Lipschitz maps from `[0,1]^{d-1}` (`d = finrank ℚ K`) covering `frontier (normLeOne K)` in `mixedSpace K`, by lifting the `realSpace` cover along the `normAtAllPlaces` fibres.
- **How**: Take `M₀` (`exists_lipschitzWith_frontierCoverFamily`) and `B` (`exists_bound_frontierCoverFamily`). Index over `S = (faces) × (real-sign patterns)`; define `Φ p = liftToMixed K (frontierCoverFamily K p.1) p.2`, each `(M₀ + B·2π)`-Lipschitz (`lipschitzWith_liftToMixed` with `hψ = hM₀ p.1`, `hB = hB p.1`). Coverage `hcover`: chain `frontier_normLeOne_subset_preimage` → preimage-monotone `frontier_subset_frontierCoverFamily` → `Set.preimage_iUnion`; for each `s` and `x` with `normAtAllPlaces x = (cover map) c'`, `mem_iUnion_image_liftToMixed_of_eq` supplies the sign pattern `ε`, landing `x` in `Φ (s,ε)`'s cube image. Finally reindex `S` by `Fin (card S)` (`Fintype.equivFin`) and transport the union (`iUnion_comp`).
- **Hypotheses**: number field `K`.
- **Uses from project**: [`exists_lipschitzWith_frontierCoverFamily`, `exists_bound_frontierCoverFamily`, `frontierCoverFamily`, `liftToMixed`, `lipschitzWith_liftToMixed`, `frontier_normLeOne_subset_preimage`, `frontier_subset_frontierCoverFamily`, `mem_iUnion_image_liftToMixed_of_eq`]
- **Used by**: in-file: `normLeOne_frontier_lipschitz_cover_index`. (No external file refs.)
- **Visibility**: public.
- **Lines**: 682–719 (body 689–719, **31 lines**).
- **Notes**: **&gt;30 lines.** `open Classical MeasureTheory in`.

### `theorem normLeOne_frontier_lipschitz_cover_index`
- **Type**: `∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card (index K) - 1) → ℝ) → (index K → ℝ)), (∀ j, LipschitzWith M (φ j)) ∧ frontier ((mixedEmbedding.stdBasis K).equivFunL '' normLeOne K) ⊆ ⋃ j, φ j '' Icc 0 1`.
- **What**: **Transported cover** on the standard Euclidean coordinate space `index K → ℝ`. The frontier of the `stdBasis`-coordinate image of `normLeOne K` is covered by finitely many Lipschitz cube images — the exact `hlip` hypothesis of `exists_card_coset_inter_smul_sub_volume_mul_rpow_le` with `ι = index K`.
- **How**: Take the `mixedSpace` cover (`normLeOne_frontier_lipschitz_cover_mixedSpace`). Let `Φ = (stdBasis K).equivFunL : mixedSpace K ≃L[ℝ] (index K → ℝ)`. Match cube dimensions: `card (index K) - 1 = finrank ℚ K - 1` (`hcard1`, from `Module.finrank_eq_card_basis (stdBasis K)` and `mixedEmbedding.finrank`), giving `g = finCongr hcard1`; the coordinate relabel `c ↦ (· ∘ g.symm)` is `1`-Lipschitz (`hrelab`). New maps `φ j = Φ ∘ φ_old j ∘ (relabel)`, Lipschitz via `Φ.lipschitz.comp ((hφ j).comp hrelab)` with constant `‖Φ‖₊ · (M · 1)`. Coverage: since `Φ` is a homeomorphism, `Φ.toHomeomorph.image_frontier` turns the goal's frontier into the image of the `mixedSpace` frontier; `Set.image_mono hcov`, `Set.image_iUnion`, and per-`j` cube-point relabelling (`Equiv.apply_symm_apply`) finish.
- **Hypotheses**: number field `K`.
- **Uses from project**: [`normLeOne_frontier_lipschitz_cover_mixedSpace`]
- **Used by**: in-file: none. **External**: `ForMathlib/IdealCongruenceCount.lean` (3 use-sites: lines 1689, 2298, 3585; plus docstring 1669) — feeds the ideal-counting boundary estimate.
- **Visibility**: public.
- **Lines**: 730–764 (body 738–766, 29 lines).
- **Notes**: `open Classical in`. Uses mathlib `(stdBasis K).equivFunL`, `mixedEmbedding.finrank`, `Module.finrank_eq_card_basis`, `Homeomorph.image_frontier`, `ContinuousLinearEquiv.lipschitz`.

---

## File Summary

**Totals**: 31 declarations — **7 `def`** (`clampUnit`, `faceMapZero`, `faceMapSide`, `cubeRelabel`, `frontierCoverFamily`, plus 2 `noncomputable def` `mixedCubeEquiv`, `liftToMixed`) and **24 `theorem`**. All are `public` (file is one `@[expose] public section`). 766 lines total.

**Soundness gates**: **no `sorry`**, **no `axiom`**, **no `admit`**, **no `set_option`**, **no `TODO`/`FIXME`** anywhere. The file is fully proved (a real candidate for upstreaming, per the module docstring — "mathlib-PR-candidate material" / "standalone future-mathlib PR").

**Three externally-consumed (public-facing) results**:
- `normLeOne_frontier_lipschitz_cover` (realSpace) — used in `ZetaProduct.lean` and cited in `IdealCongruenceCount.lean` as "Gap A".
- `normLeOne_frontier_lipschitz_cover_index` (`index K → ℝ`) — used 3× in `IdealCongruenceCount.lean` (the actual lattice-point consumer).
- `normLeOne_frontier_lipschitz_cover_mixedSpace` — used only internally (by `_index`), but is a top-level deliverable in shape.

**Key API used by ≥3 in-file declarations**:
- `clampUnit` (def) — used by 7 decls.
- `cubeRelabel` (def) — used by 6.
- `frontierCoverFamily` (def) — used by 5.
- `faceMapZero`, `faceMapSide` (defs) — used by 5 each.
- mathlib `expMapBasis` + its API (`expMapBasis_apply'`, `_apply''`, `injective_expMapBasis`, `…closure_subset_compactSet`, `…isOpen_image_of_subset_source`, `expMapBasis_source`) — the backbone, threaded through ~6 decls.
- mathlib `normAtAllPlaces` / `normAtPlace_apply_of_isReal`/`_of_isComplex` / `normLeOne_eq_preimage_image` / `normAtAllPlaces_normLeOne_eq_image` — the `realSpace ↔ mixedSpace` bridge.
- mathlib `LipschitzWith.of_dist_le_mul` / `of_edist_le` / `.comp` / `.weaken` — used in essentially every Lipschitz lemma.
- mathlib `equivFinRank`, `Fintype.equivFin`, `Real.coe_toNNReal`, `dist_le_pi_dist`/`dist_pi_le_iff` — recurring across ≥3.

**Unused-in-file** (no in-file consumer; terminal/exported nodes): `normLeOne_frontier_lipschitz_cover`, `normLeOne_frontier_lipschitz_cover_index` (both are external deliverables). Every other declaration has at least one in-file user. (`normLeOne_frontier_lipschitz_cover_mixedSpace` is used in-file by `_index`.)

**`&gt;30`-line proofs (5)**: `lipschitzWith_liftToMixed` (79), `image_boundary_subset_faces` (65), `mem_iUnion_image_liftToMixed_of_eq` (45), `lipschitzWith_exp_ofReal_mul_I` (31), `normLeOne_frontier_lipschitz_cover_mixedSpace` (31). (`frontier_subset_frontierCoverFamily` is exactly 30 — at the boundary, not over.)

**`sorry` list**: none.
**`set_option` list**: none.

**Structural note**: The file is a clean linear pipeline in three layers — (1) `realSpace` cover via `expMapBasis` faces (`clampUnit`/`cubeRelabel`/`faceMap*`/`frontierCoverFamily` → `normLeOne_frontier_lipschitz_cover`); (2) lift through `normAtAllPlaces` fibres (`liftToMixed` + the `e^{it}`/phase Lipschitz lemmas → `..._mixedSpace`); (3) transport along the `stdBasis` chart `≃L[ℝ]` (→ `..._index`). Eight `open scoped Classical in` local modifiers (on the `dite`/`decide`-using decls); two `open Classical (MeasureTheory) in` on the two top mixed-space theorems. The phase-Lipschitz block (`lipschitzWith_exp_ofReal_mul_I`, `lipschitzWith_phase`, `exists_phase_mem_Icc_mul_exp`) is self-contained with zero project dependencies and is the most obviously general/upstreamable sub-unit.</result>
<usage><subagent_tokens>49431</subagent_tokens><tool_uses>7</tool_uses><duration_ms>258949</duration_ms></usage>
</task-notification>