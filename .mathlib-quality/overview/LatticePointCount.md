-of-thought
The file is 434 lines. I've read the entire file. Now let me produce a detailed inventory for every declaration. Let me identify all the declarations:

1. `setFinite_index_image_of_isBounded` (theorem) — lines 56-77
2. `ncard_index_image_le_of_diam_le` (theorem) — lines 82-128
3. `ncard_index_image_chart_le` (theorem) — lines 135-225
4. `ncard_index_image_frontier_le` (theorem) — lines 230-262
5. `abs_card_inter_sub_volume_mul_pow_le` (theorem) — lines 269-400
6. `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` (theorem) — lines 411-429

These are all the top-level declarations. There's also `section Sublemmas` / `variable {ι : Type*} [Fintype ι]`, `@[expose] public section`, etc., but those aren't declarations per se.

Let me analyze each declaration carefully.

The task says "Uses from project" should be complete. I need to distinguish between what's from the project vs what's from mathlib. The project is `Chebotarev` namespace / `CebotarevDensity` module. But this file imports only mathlib things at the top. Let me check what's "from project" — these are declarations defined elsewhere in the project. Let me check what's used.

Looking at the file, the only declaration that's referenced from within the file (in-file uses) are the sub-lemmas referencing each other:
- `setFinite_index_image_of_isBounded` is used by `ncard_index_image_chart_le`, `ncard_index_image_frontier_le`, `abs_card_inter_sub_volume_mul_pow_le`
- `ncard_index_image_le_of_diam_le` is used by `ncard_index_image_chart_le`
- `ncard_index_image_chart_le` is used by `ncard_index_image_frontier_le`
- `ncard_index_image_frontier_le` is used by `exists_card_inter_smul_lattice_sub_volume_mul_pow_le`
- `abs_card_inter_sub_volume_mul_pow_le` is used by `exists_card_inter_smul_lattice_sub_volume_mul_pow_le`

Now for "Uses from project" — these refer to project declarations (within the `Chebotarev` namespace / the `chebotarev-density` codebase). The in-file sub-lemmas are themselves project declarations. But many of the things used are from mathlib: `index`, `box`, `tag`, `setFinite_index`, `tag_index_eq_self_of_mem_smul_span`, `mem_box_iff_index`, `volume_box`, `disjoint`, `tag_mem`, `tag_mem_smul_span`, `index_tag`, `eq_of_mem_smul_span_of_index_eq_index`, etc. These come from `Mathlib.Analysis.BoxIntegral.UnitPartition` (the `BoxIntegral.unitPartition` namespace which is opened).

So "Uses from project" should be the in-file/project declarations used. The "project" here is `chebotarev-density`. Let me be careful. The CLAUDE.md says the project is the Lean formalization. So "Uses from project" = declarations defined within this repository (chebotarev-density), not mathlib. 

Let me verify by checking: are `index`, `box`, `tag`, `setFinite_index`, `unitPartition` from mathlib or from the project? The file imports `Mathlib.Analysis.BoxIntegral.UnitPartition` and opens `BoxIntegral.unitPartition`. So `index`, `box`, `tag`, `setFinite_index`, `tag_index_eq_self_of_mem_smul_span`, `mem_box_iff_index`, `volume_box`, `disjoint`, `tag_mem`, `tag_mem_smul_span`, `index_tag`, `eq_of_mem_smul_span_of_index_eq_index`, `tag_mem_smul_span` are all from mathlib's `BoxIntegral.unitPartition` namespace. So they are NOT "uses from project" — they're mathlib API.

Let me confirm this is the right interpretation. The instruction says "Uses from project [complete; [] if none]". Given the context — this is an inventory of one file in the project — "Uses from project" most naturally means other declarations defined in this project (the chebotarev-density repo). Since this file (`ForMathlib/LatticePointCount.lean`) is "stated here for a future mathlib contribution" and imports only mathlib, the only project declarations it uses are its own in-file sub-lemmas. Let me check if it imports anything else from the project — no, it only imports 4 mathlib files. So the only "uses from project" are the in-file sub-lemmas.

Actually, let me double-check there are no other project imports. Lines 3-6:
```
public import Mathlib.Analysis.BoxIntegral.UnitPartition
public import Mathlib.Data.Pi.Interval
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Topology.MetricSpace.Lipschitz
```
All mathlib. So yes, the only project dependencies are intra-file.

So "Uses from project" for each = the in-file sub-lemmas it calls. For the bottom-up lemmas (`setFinite_index_image_of_isBounded`, `ncard_index_image_le_of_diam_le`) that use no project lemmas, it's `[]`.

Now let me also note the "key API used by 3+" for the summary. This would be mathlib API used 3+ times. Let me track the most-used mathlib lemmas:
- `index` / `index_apply` — used heavily
- `Set.ncard_le_ncard` — used multiple times
- `Int.ceil_le_ceil` — used several times
- `Int.ceil_add_le` — twice
- `mem_box_iff_index` — multiple times
- `dist_le_pi_dist` — twice
- `setFinite_index_image_of_isBounded` (project, in-file) — 3+ times

Let me carefully count usages for the "key API used by 3+" block. Let me note the most prominent ones. Actually I should focus on getting the per-declaration inventory right and then summarize.

Let me carefully go through each proof to write the "How" with specific lemma citations for proofs &gt;10 lines.

Let me write out the inventory now. Let me be precise about line numbers including the docstring. I'll cite the docstring + declaration lines. Typically "Lines" should cover the whole declaration including its docstring. Let me use the span from the docstring start (or the `set_option` for the first one) to the end of the proof.

Let me reconsider line ranges:
1. `setFinite_index_image_of_isBounded`: docstring 57-58, but there's a `set_option ... in` at line 56 and comment 54-55. The declaration proper: theorem at 59, proof ends 77. I'll say lines 56-77 (including the set_option line attached to it) or 57-77 for docstring+decl. Let me give 56–77 since set_option is part of it. Actually the comment at 54-55 explains the set_option. I'll note lines 57-77 for the docstring+decl and mention set_option at 56.

Let me just give inclusive ranges that capture docstring through proof end:
1. 57–77 (set_option at 56, comment 54–55)
2. 79–128
3. 130–225
4. 227–262
5. 264–400
6. 404–429

Now let me write each entry thoroughly.

For entry 1 `setFinite_index_image_of_isBounded`:
- **Type**: `(n : ℕ) {T : Set (ι → ℝ)} (hbdd : Bornology.IsBounded T) : (index n '' T).Finite`
- **What**: The image of a bounded set `T` under the cell-index map `index n` (which sends a point to the integer label of the `n⁻¹ℤ^ι` grid cell containing it) is finite. I.e. only finitely many grid cells meet a bounded set.
- **How**: Since `T` is bounded, `T ⊆ closedBall 0 R` for some `R`. Each coordinate `(index n x) i = ⌈n · x i⌉ - 1` lies in the fixed integer interval `[⌈-(n R)⌉ - 1, ⌈n R⌉ - 1]` because `|x i| ≤ dist x 0 ≤ R` (via `dist_le_pi_dist` for the sup metric). So `index n '' T` is contained in the finite product set `F = Fintype.piFinset (fun _ ↦ Finset.Icc …)`; conclude with `Set.Finite.subset` of `F.finite_toSet`. Monotonicity of `Int.ceil` (`Int.ceil_le_ceil`) plus `nlinarith` give the coordinate bounds.
- **Hypotheses**: `n : ℕ`; `T` a set in `ι → ℝ` (sup metric); `T` bounded.
- **Uses from project**: [] (uses mathlib `index`/`index_apply` from `BoxIntegral.unitPartition`).
- **Used by**: `ncard_index_image_chart_le`, `ncard_index_image_frontier_le`, `abs_card_inter_sub_volume_mul_pow_le`.
- **Visibility**: public (inside `@[expose] public section`).
- **Lines**: 57–77 (set_option at 56).
- **Notes**: `set_option linter.unusedFintypeInType false in` (line 56); proof ~17 lines (&gt;10, cited `dist_le_pi_dist`, `Int.ceil_le_ceil`, `Set.Finite.subset`).

Entry 2 `ncard_index_image_le_of_diam_le`:
- **Type**: `(n : ℕ) [NeZero n] {T : Set (ι → ℝ)} {r : ℝ} (hr : 0 ≤ r) (hdiam : Metric.diam T ≤ r) (hbdd : Bornology.IsBounded T) : (index n '' T).ncard ≤ (2 * ⌈(n:ℝ) * r⌉₊ + 1) ^ Fintype.card ι`
- **What**: A set of diameter `≤ r` meets at most `(2⌈n r⌉₊ + 1)^d` grid cells (`d = #ι`). Bounded-diameter cell incidence.
- **How**: Empty case trivial. Else pick `x₀ ∈ T`, let `K = ⌈n r⌉₊`, `c = index n x₀`. Show `index n '' T ⊆ F` where `F = piFinset (Icc (c i - K) (c i + K))`: for `x ∈ T`, `|x i - x₀ i| ≤ dist x x₀ ≤ diam T ≤ r` (via `dist_le_pi_dist`, `Metric.dist_le_diam_of_mem`), and then `⌈n·x i⌉ ≤ ⌈n·x₀ i⌉ + K` and symmetric, using `Int.ceil_le_ceil`, `Int.ceil_add_le`, and `Int.natCast_ceil_eq_ceil`; so each coordinate `|index n x i - c i| ≤ K` (closed by `omega`/`lia`). Then `ncard ≤ #F` via `Set.ncard_le_ncard` + `Set.ncard_coe_finset`; finally `#F = ∏ (2K+1) = (2K+1)^d` via `Fintype.card_piFinset`, `Int.card_Icc`, `Finset.prod_const`, `Finset.card_univ`.
- **Hypotheses**: `n` nonzero (`NeZero n`); `r ≥ 0`; `diam T ≤ r`; `T` bounded.
- **Uses from project**: [].
- **Used by**: `ncard_index_image_chart_le`.
- **Visibility**: public.
- **Lines**: 79–128.
- **Notes**: &gt;30 lines; uses `lia` tactic.

Wait — `lia`? That's Lean's `omega`-like? Actually `lia` might be a custom tactic or a typo... Let me check: line 119 `constructor &lt;;&gt; lia` and line 257 `by lia`. `lia` is "linear integer arithmetic" — it exists in recent mathlib/Lean as an alias? Actually `lia` is not standard mathlib; hmm. Wait, recent mathlib has `omega`. There's `lia`/`nia` from `Mathlib.Tactic.Linarith`? No. Actually `grind` has been added. Let me not over-think — I'll just report it as it's written. `lia` appears in the source. I'll note it as a tactic used. (It could be a `grind`-family or a locally-available tactic; the inventory just records usage.)

Actually, it's worth being accurate. `lia` — I believe in very recent Lean4/mathlib there's a `lia` tactic? Or it might be `bv_decide` family. I'll just record "uses `lia` and `nlinarith` tactics" without claiming what `lia` is. The task is an inventory, so I report what's in the file.

Entry 3 `ncard_index_image_chart_le`:
- **Type**: `{M : ℝ≥0} {φ : (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)} (hφ : LipschitzWith M φ) {n : ℕ} (hn : 1 ≤ n) : (index n '' (φ '' Set.Icc 0 1)).ncard ≤ (2 * ⌈(M:ℝ)⌉₊ + 1) ^ Fintype.card ι * (n + 1) ^ (Fintype.card ι - 1)`
- **What**: L1a' — single-chart cell count. For one `M`-Lipschitz `φ : ℝ^{d-1} → ℝ^d`, the number of grid cells meeting `φ '' [0,1]^{d-1}` is `≤ (2⌈M⌉₊+1)^d · (n+1)^{d-1} = O(n^{d-1})`.
- **How**: Define domain-grid map `q y k = ⌈n · y k⌉`, and index set `T = Icc 0 (fun _ ↦ n) ⊆ ℤ^{d-1}` of admissible subcubes. Three steps: (i) each fibre `[0,1]^{d-1} ∩ q⁻¹{v}` has diameter `≤ 1/n` (`Metric.diam_le_of_forall_dist_le` + `dist_pi_le_iff`; `⌈n yₖ⌉ = ⌈n y'ₖ⌉` ⇒ `|n yₖ - n y'ₖ| ≤ 1` via `Int.ceil_eq_iff` and `nlinarith`); (ii) the chart image is covered by the union over `v ∈ T` of `index n '' φ '' (fibre)` (`Set.mem_biUnion`; membership `q y ∈ T` from `Int.le_ceil_iff`, `Int.ceil_le`); (iii) each piece has `≤ (2⌈M⌉₊+1)^d` points by `ncard_index_image_le_of_diam_le` since `φ` maps the `1/n`-diameter fibre to a set of diameter `≤ M·(1/n)` (`LipschitzWith.diam_image_le`, `LipschitzWith.isBounded_image`) and `n·(M·(1/n)) = M`. Assemble via `Set.ncard_le_ncard` over the cover, `Finset.set_ncard_biUnion_le`, `Finset.sum_le_sum`, `Finset.sum_const`; finally `#T = (n+1)^{d-1}` via `Pi.card_Icc`, `Int.card_Icc`, `Finset.prod_const`, `Fintype.card_fin`.
- **Hypotheses**: `φ` is `M`-Lipschitz; `1 ≤ n`.
- **Uses from project**: `ncard_index_image_le_of_diam_le`, `setFinite_index_image_of_isBounded`.
- **Used by**: `ncard_index_image_frontier_le`.
- **Visibility**: public.
- **Lines**: 130–225.
- **Notes**: &gt;30 lines (largest single-chart proof, ~90 lines).

Entry 4 `ncard_index_image_frontier_le`:
- **Type**: `{s : Set (ι → ℝ)} {m : ℕ} {M : ℝ≥0} {φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)} (hφ : ∀ j, LipschitzWith M (φ j)) (hcov : frontier s ⊆ ⋃ j, φ j '' Set.Icc 0 1) {n : ℕ} (hn : 1 ≤ n) : (index n '' frontier s).ncard ≤ (m * (2 * ⌈(M:ℝ)⌉₊ + 1)^(card ι) * 2^(card ι - 1)) * n^(card ι - 1)`
- **What**: L1a — boundary-cell count. If `∂s` is covered by `m` `M`-Lipschitz chart images of `[0,1]^{d-1}`, the number of grid cells meeting `∂s` is `O(n^{d-1})`, with explicit constant `m·(2⌈M⌉₊+1)^d·2^{d-1}`.
- **How**: `index n '' ∂s ⊆ ⋃ j, index n '' (φ j '' Icc 0 1)` (`Set.image_iUnion`, `Set.image_mono hcov`). Bound by sum over `j` via `Set.ncard_le_ncard` + `Set.ncard_iUnion_le_of_fintype`, then `Finset.sum_le_sum` applying `ncard_index_image_chart_le` to each chart; `Finset.sum_const`/`Fintype.card_fin` give `m · (Cφ · (n+1)^{d-1})`. Replace `(n+1)^{d-1} ≤ (2n)^{d-1} = 2^{d-1}·n^{d-1}` (`Nat.pow_le_pow_left`, `mul_pow`) and `ring`. Finiteness of chart `index`-images via `setFinite_index_image_of_isBounded` (charts bounded as Lipschitz images of compact `Icc 0 1`).
- **Hypotheses**: family of `m` maps `φ j`, all `M`-Lipschitz; `∂s` covered by their `[0,1]^{d-1}`-images; `1 ≤ n`.
- **Uses from project**: `ncard_index_image_chart_le`, `setFinite_index_image_of_isBounded`.
- **Used by**: `exists_card_inter_smul_lattice_sub_volume_mul_pow_le`.
- **Visibility**: public.
- **Lines**: 227–262.
- **Notes**: &gt;30 lines; uses `lia`.

Entry 5 `abs_card_inter_sub_volume_mul_pow_le`:
- **Type**: `{s : Set (ι → ℝ)} (hbdd : Bornology.IsBounded s) (hmeas : MeasurableSet s) {n : ℕ} (hn : 1 ≤ n) : |(Nat.card ↑(s ∩ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) : ℝ) - volume.real s * (n:ℝ)^(card ι)| ≤ (index n '' frontier s).ncard`
- **What**: L1b — count↔volume bridge. The number of scaled-lattice points `n⁻¹ℤ^ι` in bounded measurable `s` differs from `vol(s)·n^d` by at most the number of grid cells meeting `∂s`.
- **How**: Key geometric fact (`hfront`): a connected cell `box n ν` (convex product of `Ioc`s, `convex_pi`/`isPreconnected`) that meets both `s` and `sᶜ` must meet `∂s` (else `IsPreconnected.subset_or_subset` splits it between `interior s` and `(closure s)ᶜ`, contradicting that it meets `s` and `sᶜ`). Define index sets `Inside = {ν | box ⊆ s}`, `Meet = {ν | box ∩ s ≠ ∅}`, `Bd = index '' ∂s`, `Tag = {ν | tag n ν ∈ s}`; all finite (`setFinite_index`, `setFinite_index_image_of_isBounded`). The counted set corresponds to `Tag` via `index` (bijection: `tag_index_eq_self_of_mem_smul_span`, `index_tag`, `tag_mem_smul_span`, injectivity `eq_of_mem_smul_span_of_index_eq_index`), giving `Nat.card … = Tag.ncard`. Inclusions `Inside ⊆ Tag ⊆ Meet ⊆ Inside ∪ Bd` give the cardinality sandwich (`Set.ncard_le_ncard`, `Set.ncard_union_le`). Volume sandwich: each cell has volume `1/n^d` (`volume_box`); disjoint finite unions give measure `#family / n^d` (`measureReal_biUnion_finset`, `disjoint`); interior cells ⊆ s ⇒ `Inside.ncard ≤ V`, and s ⊆ ⋃ meeting cells ⇒ `V ≤ Meet.ncard` (`measureReal_mono`). Combining the count-sandwich and volume-sandwich (both `N` and `V` in `[Inside.ncard, Inside.ncard + Bd.ncard]`) with `abs_le` and `linarith` yields the bound.
- **Hypotheses**: `s` bounded and measurable; `1 ≤ n`.
- **Uses from project**: `setFinite_index_image_of_isBounded`.
- **Used by**: `exists_card_inter_smul_lattice_sub_volume_mul_pow_le`.
- **Visibility**: public.
- **Lines**: 264–400.
- **Notes**: &gt;30 lines (largest proof, ~130 lines); `finiteness` tactic used.

Entry 6 `exists_card_inter_smul_lattice_sub_volume_mul_pow_le`:
- **Type**: `{ι : Type*} [Fintype ι] (s : Set (ι → ℝ)) (hbdd) (hmeas) (hlip : ∃ m M φ, (∀ j, LipschitzWith M (φ j)) ∧ frontier s ⊆ ⋃ j, φ j '' Set.Icc 0 1) : ∃ C : ℝ, ∀ n, 1 ≤ n → |(Nat.card ↑(s ∩ n⁻¹ • span ℤ …) : ℝ) - volume.real s * n^d| ≤ C * n^(d-1)`
- **What**: The main theorem (Lang/Gun–Ramaré–Sivaraman effective lattice-point count): for bounded measurable `s` with Lipschitz-covered frontier, the scaled-lattice point count equals `vol(s)·n^d` up to `O(n^{d-1})`.
- **How**: Destructure `hlip` to get `m, M, φ`. Take `C = m·(2⌈M⌉₊+1)^d·2^{d-1}` (the L1a constant). For each `n ≥ 1`: chain L1b (`abs_card_inter_sub_volume_mul_pow_le`) to bound the discrepancy by `(index n '' ∂s).ncard`, then L1a (`ncard_index_image_frontier_le`) to bound that by `C·n^{d-1}`; reconcile the cast with `push_cast`, `ring_nf`, `rfl`.
- **Hypotheses**: `s` bounded, measurable; frontier covered by finitely many Lipschitz images of `[0,1]^{d-1}`.
- **Uses from project**: `abs_card_inter_sub_volume_mul_pow_le`, `ncard_index_image_frontier_le`.
- **Used by**: unused in file (it is the file's main export; it's the headline theorem named in the module docstring).
- **Visibility**: public.
- **Lines**: 404–429.
- **Notes**: this is the named "Main statement" of the module; no sorry.

Now the file summary. Let me also double check there are no `sorry`s — there are none. No `axiom`s. set_option appears once (line 56). 

Let me count &gt;30-line proofs: entries 2, 3, 4, 5 (and arguably). Let me count lines of proof bodies:
- Entry 1: ~17 lines (58→77). Not &gt;30.
- Entry 2: 79→128 ≈ 50 lines. &gt;30.
- Entry 3: 130→225 ≈ 96 lines. &gt;30.
- Entry 4: 227→262 ≈ 36 lines. &gt;30.
- Entry 5: 264→400 ≈ 137 lines. &gt;30.
- Entry 6: 404→429 ≈ 26 lines. Not &gt;30 (but borderline; proof body 420-429 is ~10 lines).

So &gt;30-line list: entries 2, 3, 4, 5.

set_option list: entry 1 (linter.unusedFintypeInType false).

sorry list: none.

Key API used by 3+ (mathlib): Let me identify. I'll tally:
- `index` / `index_apply` (BoxIntegral.unitPartition) — appears in nearly every lemma. Definitely 3+.
- `Set.ncard_le_ncard` — entries 2 (×1), 3 (×2: ncard_le_ncard hcover, and the .trans chain), 5 (×3: hcard_IT, hcard_TM, hcard_MIB). Definitely 3+.
- `mem_box_iff_index` — entry 5 multiple times. Only entry 5 though. Used ≥4× but in 1 decl.
- `Int.ceil_le_ceil` — entries 1, 2 (×2). 3+ occurrences.
- `dist_le_pi_dist` — entries 1, 2. 2 occurrences.
- `LipschitzWith.isBounded_image` — entries 3, 4. 
- `setFinite_index_image_of_isBounded` (project, in-file) — entries 3, 4, 5 (and also used inside 3, 4). 3+ decls. This is the key in-project API.
- `box` (BoxIntegral.unitPartition) — entry 5 only but heavily.
- `tag` — entry 5.
- `Metric.isBounded_Icc` — entries 3 (×2), 4 (×1). 3+.
- `volume_box` — entry 5 (×3).

Let me pick the genuine "used by 3+ declarations" for the summary: `index`/`index_apply`, `Set.ncard_le_ncard`, `Int.ceil_le_ceil` (≥3 occ), and the in-project `setFinite_index_image_of_isBounded`. Also `Fintype.card ι` appears everywhere but that's not really "API". I'll list the mathlib API used across 3+ declarations.

Actually let me reconsider "key API used by 3+". It likely means lemmas/defs used in 3+ places (or 3+ declarations). I'll list:
- `BoxIntegral.unitPartition.index` (+ `index_apply`) — used in all 6.
- `Set.ncard_le_ncard` — entries 2,3,5.
- `setFinite_index_image_of_isBounded` (in-file) — entries 3,4,5.
- `Int.ceil_le_ceil` — entries 1,2.  (only 2 decls — drop or note)
- `Metric.isBounded_Icc` — entries 3,4 (2 decls). 

Hmm, to be safe, "used by 3+" — I'll list those appearing in ≥3 declarations: `index`/`index_apply` (6), `Set.ncard_le_ncard` (3), `setFinite_index_image_of_isBounded` (3). And note `Fintype.card ι` is pervasive. Also `LipschitzWith.isBounded_image` (2), `Metric.isBounded_Icc` (3: entries 3 twice, 4 once — that's 2 declarations). Let me be precise: declarations using `Metric.isBounded_Icc` = {3, 4} → 2 declarations. So not 3 declarations. I'll say "3+ occurrences" vs "3+ declarations" — to be safe I'll frame by declarations.

So API used by 3+ declarations:
- `index` (and `index_apply`, `mem_box_iff_index`) from `BoxIntegral.unitPartition` — all/most.
- `Set.ncard_le_ncard` — 3 declarations (2, 3, 5).
- `setFinite_index_image_of_isBounded` (in-file helper) — 3 declarations (3, 4, 5).

That's the honest set. I'll present it.

unused-in-file: only `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` (the top-level export) is not used by anything in-file.

Let me also note the variable lines and section structure in a preamble note. Good.

Let me also double-check the `Nat.card ↑(s ∩ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι)))` — this is the scaled lattice `n⁻¹ · ℤ^ι` where `span ℤ (range (Pi.basisFun ℝ ι))` is the standard integer lattice `ℤ^ι` in `ℝ^ι`.

Now I have all I need. Let me also verify visibility: everything is inside `@[expose] public section` (line 40) ending at `end` (line 431). And `section Sublemmas` (50) … `end Sublemmas` (402) wraps entries 1–5; entry 6 is outside Sublemmas but inside the public/namespace. So all six are `public`. The sub-lemmas 1–5 are within `section Sublemmas` (with the local `variable {ι} [Fintype ι]`), entry 6 re-declares `{ι} [Fintype ι]` in its own signature.

One more: the `@[expose]` attribute — `@[expose] public section` means all defs in the section have their bodies exposed across module boundaries. Worth noting in the summary.

I'm confident. Let me write the final inventory. This is a read-only task; I will not edit. I have already read the whole file, so I don't need further tool calls. Let me produce the final message.

I should make sure not to use a colon before any (nonexistent) tool calls — there are none. Just produce the report.
&lt;/chain-of-thought&gt;

# Inventory — `CebotarevDensity/ForMathlib/LatticePointCount.lean`

**File-level context.** A standalone "for-mathlib" module (imports only mathlib: `BoxIntegral.UnitPartition`, `Data.Pi.Interval`, `Data.Set.Card.Arithmetic`, `Topology.MetricSpace.Lipschitz`). All content is inside `namespace Chebotarev` and an `@[expose] public section` (line 40 → `end` 431), so every declaration is `public` with exposed body. `open … BoxIntegral.unitPartition` brings in the lattice/grid API (`index`, `box`, `tag`, `setFinite_index`, `mem_box_iff_index`, `volume_box`, `disjoint`, `tag_mem`, `tag_mem_smul_span`, `index_tag`, `tag_index_eq_self_of_mem_smul_span`, `eq_of_mem_smul_span_of_index_eq_index`) — these are **mathlib**, not project, so they never appear under "Uses from project". The only intra-project dependencies are this file's own sub-lemmas. Sub-lemmas 1–5 live in `section Sublemmas` with local `variable {ι : Type*} [Fintype ι]` (line 52); the main theorem (6) re-declares `ι` itself. No `sorry`, no `axiom`. Throughout, `d := Fintype.card ι` and the ambient metric on `ι → ℝ` is the sup metric.

---

### `theorem` `setFinite_index_image_of_isBounded`
- **Type** · `(n : ℕ) {T : Set (ι → ℝ)} (hbdd : Bornology.IsBounded T) : (index n '' T).Finite`
- **What** · The image of a bounded set under the cell-index map `index n` (point ↦ integer label of the `n⁻¹ℤ^ι` grid cell containing it) is finite: only finitely many grid cells meet a bounded set.
- **How** · From `hbdd` get `T ⊆ closedBall 0 R`. Each coordinate `(index n x) i = ⌈n·x i⌉ − 1` lies in the fixed integer interval `[⌈−(nR)⌉−1, ⌈nR⌉−1]`, because `|x i| ≤ dist x 0 ≤ R` via `dist_le_pi_dist` (sup metric). Hence `index n '' T ⊆ F` for the product `F = Fintype.piFinset (fun _ ↦ Finset.Icc …)`; close with `Set.Finite.subset` of `F.finite_toSet`. Coordinate bounds use `Int.ceil_le_ceil` + `nlinarith`.
- **Hypotheses** · `T` bounded in `ι → ℝ`.
- **Uses from project** · []
- **Used by** · `ncard_index_image_chart_le`, `ncard_index_image_frontier_le`, `abs_card_inter_sub_volume_mul_pow_le`
- **Visibility** · public
- **Lines** · 57–77 (set_option at 56)
- **Notes** · `set_option linter.unusedFintypeInType false in` (line 56, with explanatory comment 54–55 — `Fintype ι` is needed for the sup metric but only appears in the body).

---

### `theorem` `ncard_index_image_le_of_diam_le`
- **Type** · `(n : ℕ) [NeZero n] {T : Set (ι → ℝ)} {r : ℝ} (hr : 0 ≤ r) (hdiam : Metric.diam T ≤ r) (hbdd : Bornology.IsBounded T) : (index n '' T).ncard ≤ (2 * ⌈(n:ℝ) * r⌉₊ + 1) ^ Fintype.card ι`
- **What** · Bounded-diameter cell incidence: a set of diameter `≤ r` meets at most `(2⌈n·r⌉₊+1)^d` cells of the `n⁻¹ℤ^ι` grid.
- **How** · Empty case by `simp`. Otherwise pick `x₀ ∈ T`, set `K = ⌈n·r⌉₊`, `c = index n x₀`. Show `index n '' T ⊆ F` for `F = piFinset (Icc (c i − K) (c i + K))`: for `x ∈ T`, `|x i − x₀ i| ≤ dist x x₀ ≤ diam T ≤ r` (via `dist_le_pi_dist`, `Metric.dist_le_diam_of_mem`); then `⌈n·x i⌉ ≤ ⌈n·x₀ i⌉ + K` and the reverse, using `Int.ceil_le_ceil`, `Int.ceil_add_le`, `Int.natCast_ceil_eq_ceil`, so `|index n x i − c i| ≤ K` (closed by `lia`). Bound `ncard ≤ #F` (`Set.ncard_le_ncard`, `Set.ncard_coe_finset`); then `#F = ∏ᵢ(2K+1) = (2K+1)^d` via `Fintype.card_piFinset`, `Int.card_Icc`, `Finset.prod_const`, `Finset.card_univ`.
- **Hypotheses** · `n ≠ 0`; `0 ≤ r`; `diam T ≤ r`; `T` bounded.
- **Uses from project** · []
- **Used by** · `ncard_index_image_chart_le`
- **Visibility** · public
- **Lines** · 79–128
- **Notes** · &gt;30 lines (~50). Uses `lia` (line 119) and `nlinarith`.

---

### `theorem` `ncard_index_image_chart_le`
- **Type** · `{M : ℝ≥0} {φ : (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)} (hφ : LipschitzWith M φ) {n : ℕ} (hn : 1 ≤ n) : (index n '' (φ '' Set.Icc 0 1)).ncard ≤ (2 * ⌈(M:ℝ)⌉₊ + 1) ^ Fintype.card ι * (n + 1) ^ (Fintype.card ι - 1)`
- **What** · **L1a′**, the combinatorial heart: for one `M`-Lipschitz chart `φ : ℝ^{d−1} → ℝ^d`, the number of grid cells meeting `φ '' [0,1]^{d−1}` is `≤ (2⌈M⌉₊+1)^d · (n+1)^{d−1} = O(n^{d−1})`.
- **How** · Domain-grid map `q y k = ⌈n·y k⌉`; admissible-subcube index set `T = Icc 0 (fun _ ↦ n) ⊆ ℤ^{d−1}`. (i) **`hdiam`**: each fibre `[0,1]^{d−1} ∩ q⁻¹{v}` has diameter `≤ 1/n` — `Metric.diam_le_of_forall_dist_le` + `dist_pi_le_iff`, with `⌈n·yₖ⌉ = ⌈n·y'ₖ⌉ ⇒ |n·yₖ − n·y'ₖ| ≤ 1` from `Int.ceil_eq_iff` + `nlinarith`, then divide by `n&gt;0`. (ii) **`hcover`**: `index n '' (φ '' [0,1]^{d−1}) ⊆ ⋃_{v∈T} index n '' φ '' (fibre)` — `Set.mem_biUnion`, membership `q y ∈ T` from `Int.le_ceil_iff` / `Int.ceil_le`. (iii) **`hpiece`**: each piece has `≤ (2⌈M⌉₊+1)^d` points via `ncard_index_image_le_of_diam_le`, since `LipschitzWith.diam_image_le` gives `φ`-image diameter `≤ M·(1/n)` and `n·(M·(1/n)) = M`. Assemble: `Set.ncard_le_ncard` over the cover (finiteness from `setFinite_index_image_of_isBounded` via `LipschitzWith.isBounded_image`), `Finset.set_ncard_biUnion_le`, `Finset.sum_le_sum`, `Finset.sum_const`; finally `#T = (n+1)^{d−1}` via `Pi.card_Icc`, `Int.card_Icc`, `Finset.prod_const`, `Fintype.card_fin`.
- **Hypotheses** · `φ` is `M`-Lipschitz; `1 ≤ n`.
- **Uses from project** · `ncard_index_image_le_of_diam_le`, `setFinite_index_image_of_isBounded`
- **Used by** · `ncard_index_image_frontier_le`
- **Visibility** · public
- **Lines** · 130–225
- **Notes** · &gt;30 lines (~96 — the longest sub-lemma). `nlinarith`-heavy.

---

### `theorem` `ncard_index_image_frontier_le`
- **Type** · `{s : Set (ι → ℝ)} {m : ℕ} {M : ℝ≥0} {φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)} (hφ : ∀ j, LipschitzWith M (φ j)) (hcov : frontier s ⊆ ⋃ j, φ j '' Set.Icc 0 1) {n : ℕ} (hn : 1 ≤ n) : (index n '' frontier s).ncard ≤ (m * (2 * ⌈(M:ℝ)⌉₊ + 1) ^ Fintype.card ι * 2 ^ (Fintype.card ι - 1)) * n ^ (Fintype.card ι - 1)`
- **What** · **L1a**, boundary-cell count: if `∂s` is covered by `m` `M`-Lipschitz chart images of `[0,1]^{d−1}`, the number of grid cells meeting `∂s` is `O(n^{d−1})` with explicit constant `m·(2⌈M⌉₊+1)^d·2^{d−1}`.
- **How** · `index n '' ∂s ⊆ ⋃ⱼ index n '' (φ j '' Icc 0 1)` (`Set.image_iUnion`, `Set.image_mono hcov`; finiteness of each chart image via `setFinite_index_image_of_isBounded` from `LipschitzWith.isBounded_image` of compact `Icc 0 1`). Bound by `∑ⱼ` via `Set.ncard_le_ncard` + `Set.ncard_iUnion_le_of_fintype`, then `Finset.sum_le_sum` applying `ncard_index_image_chart_le` to each `φ j`; `Finset.sum_const`/`Fintype.card_fin` give `m·(Cφ·(n+1)^{d−1})`. Finish with `(n+1)^{d−1} ≤ 2^{d−1}·n^{d−1}` (`mul_pow`, `Nat.pow_le_pow_left`) and `gcongr`/`ring`.
- **Hypotheses** · `m` charts `φ j`, all `M`-Lipschitz; `∂s` covered by their `[0,1]^{d−1}`-images; `1 ≤ n`.
- **Uses from project** · `ncard_index_image_chart_le`, `setFinite_index_image_of_isBounded`
- **Used by** · `exists_card_inter_smul_lattice_sub_volume_mul_pow_le`
- **Visibility** · public
- **Lines** · 227–262
- **Notes** · &gt;30 lines (~36). Uses `lia` (line 257), `gcongr`.

---

### `theorem` `abs_card_inter_sub_volume_mul_pow_le`
- **Type** · `{s : Set (ι → ℝ)} (hbdd : Bornology.IsBounded s) (hmeas : MeasurableSet s) {n : ℕ} (hn : 1 ≤ n) : |(Nat.card ↑(s ∩ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) : ℝ) - volume.real s * (n:ℝ) ^ Fintype.card ι| ≤ (index n '' frontier s).ncard`
- **What** · **L1b**, count↔volume bridge: the number of points of the scaled lattice `n⁻¹ℤ^ι` (= `n⁻¹ • span ℤ (range (Pi.basisFun ℝ ι))`) inside bounded measurable `s` differs from `vol(s)·n^d` by at most the number of grid cells meeting `∂s`. The effective sandwich underlying `tendsto_card_div_pow_atTop_volume`.
- **How** · **Geometric core `hfront`**: a connected cell `box n ν` (convex, being a product of `Ioc`s: `Box.coe_eq_pi`, `convex_pi`, `IsPreconnected`) meeting both `s` and `sᶜ` must meet `∂s` — else `IsPreconnected.subset_or_subset` (with `isOpen_interior`, `isClosed_closure.isOpen_compl`, `disjoint_compl_right_iff_subset`) splits the cell between `interior s` and `(closure s)ᶜ`, contradicting that it meets `s`/`sᶜ`. Define `Inside = {ν | box ⊆ s}`, `Meet = {ν | box ∩ s ≠ ∅}`, `Bd = index '' ∂s`, `Tag = {ν | tag n ν ∈ s}`; finiteness via `setFinite_index` (Inside), `setFinite_index_image_of_isBounded` (Bd, Meet). **Count↔Tag**: `index` bijects the counted set with `Tag` (`tag_index_eq_self_of_mem_smul_span`, `tag_mem_smul_span`, `index_tag`; injective by `eq_of_mem_smul_span_of_index_eq_index` via `Set.InjOn.ncard_image`), so `Nat.card … = Tag.ncard`. **Cardinality sandwich** `Inside ⊆ Tag ⊆ Meet ⊆ Inside ∪ Bd` (`Set.ncard_le_ncard`, `Set.ncard_union_le`). **Volume sandwich**: each cell has `volume.real = 1/n^d` (`volume_box`); disjoint finite unions give `#family / n^d` (`measureReal_biUnion_finset` with `disjoint` + `Box.measurableSet_coe`); `Inside`-cells ⊆ s ⇒ `Inside.ncard ≤ V`, and `s ⊆ ⋃ Meet`-cells ⇒ `V ≤ Meet.ncard` (`measureReal_mono`), where `V = vol(s)·n^d`. Both `N=Tag.ncard` and `V` lie in `[Inside.ncard, Inside.ncard + Bd.ncard]`; `abs_le` + `linarith` close it.
- **Hypotheses** · `s` bounded and measurable; `1 ≤ n`.
- **Uses from project** · `setFinite_index_image_of_isBounded`
- **Used by** · `exists_card_inter_smul_lattice_sub_volume_mul_pow_le`
- **Visibility** · public
- **Lines** · 264–400
- **Notes** · &gt;30 lines (~137 — longest proof in file). Uses `finiteness` tactic (lines 366, 390).

---

### `theorem` `exists_card_inter_smul_lattice_sub_volume_mul_pow_le`
- **Type** · `{ι : Type*} [Fintype ι] (s : Set (ι → ℝ)) (hbdd : Bornology.IsBounded s) (hmeas : MeasurableSet s) (hlip : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)), (∀ j, LipschitzWith M (φ j)) ∧ frontier s ⊆ ⋃ j, φ j '' Set.Icc 0 1) : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → |(Nat.card ↑(s ∩ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) : ℝ) - volume.real s * (n:ℝ) ^ Fintype.card ι| ≤ C * (n:ℝ) ^ (Fintype.card ι - 1)`
- **What** · The module's **Main statement** (Lang GTM 110 Ch. V §2 / p. 129; Gun–Ramaré–Sivaraman §3.3–3.5, after Debaene): for bounded measurable `s` whose frontier is covered by finitely many Lipschitz images of `[0,1]^{d−1}`, the scaled-lattice point count equals `vol(s)·n^d` up to `O(n^{d−1})` — the effective form of `tendsto_card_div_pow_atTop_volume`.
- **How** · Destructure `hlip` into `m, M, φ`. Take the witness `C = (m·(2⌈M⌉₊+1)^d·2^{d−1} : ℕ)` (the L1a constant). For each `n ≥ 1`: apply L1b (`abs_card_inter_sub_volume_mul_pow_le`) to bound the discrepancy by `(index n '' ∂s).ncard`, then L1a (`ncard_index_image_frontier_le hφ hcov hn`) to bound that by `C·n^{d−1}`; reconcile the `ℕ→ℝ` cast with `Nat.cast_le`, `push_cast`, `ring_nf`, `rfl`.
- **Hypotheses** · `s` bounded, measurable; frontier covered by finitely many `M`-Lipschitz images of `[0,1]^{d−1}`.
- **Uses from project** · `abs_card_inter_sub_volume_mul_pow_le`, `ncard_index_image_frontier_le`
- **Used by** · unused in file (top-level export; the headline theorem named in the module docstring "## Main statement")
- **Visibility** · public
- **Lines** · 404–429
- **Notes** · — (re-declares `{ι} [Fintype ι]` in its own signature, outside `section Sublemmas`).

---

## File Summary

- **Totals** · 6 declarations, all `theorem`, all `public` (inside `@[expose] public section`). 4 helpers + 1 bridge in `section Sublemmas`; 1 top-level export. 0 `def`, 0 `axiom`, 0 `sorry`.
- **Dependency chain (in-file)** · `setFinite_index_image_of_isBounded` (leaf) → used by chart/frontier/bridge lemmas. `ncard_index_image_le_of_diam_le` (leaf) → `ncard_index_image_chart_le` (L1a′) → `ncard_index_image_frontier_le` (L1a). `ncard_index_image_frontier_le` + `abs_card_inter_sub_volume_mul_pow_le` (L1b) → `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` (main). Two leaves (`setFinite_index_image_of_isBounded`, `ncard_index_image_le_of_diam_le`) have **no project deps**.
- **Key API used by 3+ declarations** ·
  - `BoxIntegral.unitPartition.index` / `index_apply` / `mem_box_iff_index` (mathlib) — pervasive (all 6 declarations).
  - `Set.ncard_le_ncard` (mathlib) — declarations 2, 3, 5.
  - `setFinite_index_image_of_isBounded` (this file's leaf) — declarations 3, 4, 5.
  - (Honourable mentions, in 2 declarations each: `LipschitzWith.isBounded_image`, `Metric.isBounded_Icc`, `dist_le_pi_dist`, `Int.ceil_le_ceil`, `Int.card_Icc`, `Finset.prod_const`.)
- **Unused-in-file** · `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` only (the intended external/mathlib-contribution export).
- **`sorry` list** · none.
- **`set_option` list** · `setFinite_index_image_of_isBounded` — `set_option linter.unusedFintypeInType false in` (line 56).
- **`&gt;30`-line proofs** · `ncard_index_image_le_of_diam_le` (~50), `ncard_index_image_chart_le` (~96), `ncard_index_image_frontier_le` (~36), `abs_card_inter_sub_volume_mul_pow_le` (~137). (`exists_…` main is ~26, `setFinite_…` ~17 — both under 30.)
- **Notable tactics / conventions** · `lia` appears at lines 119 and 257 (alongside the usual `nlinarith`, `omega`-style closing); `finiteness` at 366, 390; `gcongr`, `ring_nf`. All inequalities are oriented `≤` (no `≥`), per project convention. No project-external imports beyond mathlib — this file is self-contained "for-mathlib" infrastructure (the L1/Widmer effective lattice-point count), the deepest analytic input feeding the CFT-free Chebotarev proof.