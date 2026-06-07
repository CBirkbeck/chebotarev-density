# Inventory: `CebotarevDensity/ForMathlib/IdealCongruenceCount.lean`

**File-level note.** This is the project's deepest file — the geometry-of-numbers / equidistribution engine for the abelian Chebotarev step (Gap B / L2). It was built across ~8 worker layers and shows clear stratification, with **substantial redundancy**: e.g. the orthant/region-membership computation (`hreg`) is duplicated verbatim between `card_fibre_eq_card_cell` and `exists_card_fibre_dvd_eq_card_cell`; the per-(orthant,coset) partition is implemented three times (`exists_card_idealSet_residue_le` inline, `exists_card_idealSet_residue_real_le` inline, and extracted as `card_idealSet_residue_eq_sum_cell`); the "residue-constant-on-cell" reasoning appears inline in `exists_card_residue_fibre_sub_mul_rpow_le` and extracted as `residue_fibre_const_aux`; the per-cell workhorse has an "implicit κ" form (`exists_card_cell_sub_mul_rpow_le`) and an "explicit κ" form (`exists_card_cell_sub_mul_rpow_le_explicit`). Most strikingly, **there are two complete, independent proofs of the same L2 fact**: `cardNormLeResidueClassDvd_div_density` (the geometric Route-B/CRT proof) and `cardNormLeResidueClass_div_density` (which routes through the elementary kernel `cardNormLeResidueClassDvd_sub_mul_rpow_le`); only the latter is on the live path. I flag every declaration with no in-file consumer in the summary.

The whole file is inside `@[expose] public section` / `noncomputable section` / `namespace Chebotarev`. **Zero `sorry`. Zero `axiom`. Two `set_option` lines.** All four public theorems are real, fully-proven results; the formerly-`sorry`'d L2 geometric gap is now discharged.

---

### `private theorem ncard_index1_image_smul_chart_le`
- **Type**: For `M`-Lipschitz `φ : (Fin (card ι - 1) → ℝ) → (ι → ℝ)` and real `c ≥ 1`, `(index 1 '' ((fun y ↦ v + c • φ y) '' Icc 0 1)).ncard ≤ (2⌈M⌉₊+1)^(card ι) · (⌈c⌉₊+1)^(card ι - 1)`.
- **What**: The number of unit grid cells meeting a scaled-and-translated chart image of the unit cube is `O(c^(d-1))`.
- **How**: Subdivides `[0,1]^(d-1)` into the `(⌈c⌉₊+1)^(d-1)` fibres of `y ↦ ⌈⌈c⌉₊ yₖ⌉` (domain-grid map `q`, index set `T = Icc 0 N`); each fibre has diameter `≤ 1/N` (`Metric.diam_le_of_forall_dist_le`, `Int.ceil_eq_iff`, `nlinarith`), so the `(v + c•φ·)`-image has diameter `≤ c·M/N ≤ M` (`dist_smul₀`, `hφ.dist_le_mul`), giving `≤ (2⌈M⌉₊+1)^d` cells per fibre via `ncard_index_image_le_of_diam_le`. Assembled by `Set.ncard_le_ncard` over the cover, `Finset.set_ncard_biUnion_le`, `Finset.sum_le_sum`, and `Pi.card_Icc`/`Int.card_Icc` for `#T`.
- **Hypotheses**: `φ` is `M`-Lipschitz; `c ≥ 1`.
- **Uses from project**: []
- **Used by**: `abs_cardR_translate_sub_volume_le`.
- **Visibility**: private · **Lines**: 87–205 · **Notes**: &gt;30 lines.

### `private theorem abs_cardR_translate_sub_volume_le`
- **Type**: For bounded measurable `s` with `frontier s ⊆ ⋃ⱼ φⱼ '' Icc 0 1` (`φⱼ` all `M`-Lipschitz), any translate `w`, any real `c ≥ 1`: `|Nat.card ↑(s ∩ c⁻¹ • (w +ᵥ Λ)) - vol.real s · c^(card ι)| ≤ (m·(2⌈M⌉₊+1)^d·3^(d-1)) · c^(d-1)`, where `Λ = span ℤ (range (Pi.basisFun ℝ ι))`.
- **What**: Translate-uniform real-scale lattice-point count with an **explicit** error constant depending only on the cover data + dimension (not on `w`, `c`, `vol s`).
- **How**: Reduces via a scaling bijection (`x ↦ c•x`, `Equiv.smulRight`) and translation bijection (`x ↦ -w +ᵥ x`) to `#(R ∩ Λ)` for `R = -w +ᵥ c•s`; applies the unit-grid bridge `abs_card_inter_sub_volume_mul_pow_le` (from `LatticePointCount`) at `n=1`; computes `vol.real R = c^d·vol.real s` (`Measure.addHaar_smul`, `Module.finrank_pi`); bounds boundary cells by `ncard_index1_image_smul_chart_le` over the transported charts (`Homeomorph.smulOfNeZero`/`addLeft`.`image_frontier`); converts `⌈c⌉₊+1 ≤ 3c` (`Nat.ceil_lt_add_one`, `nlinarith`).
- **Hypotheses**: `s` bounded + measurable; finite Lipschitz cube cover of `frontier s`; `c ≥ 1`.
- **Uses from project**: [`ncard_index1_image_smul_chart_le`]
- **Used by**: `exists_card_coset_inter_smul_sub_volume_mul_rpow_le`.
- **Visibility**: private · **Lines**: 217–317 · **Notes**: &gt;30 lines.

### `theorem exists_card_coset_inter_smul_sub_volume_mul_rpow_le` — THE WORKHORSE
- **Type**: For a linear automorphism `T : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)`, bounded measurable `D` with finite Lipschitz cube cover of `frontier D`: `∃ C, ∀ ξ t, 1 ≤ t → |Nat.card ↑((ξ +ᵥ T''Λ) ∩ t•D) - vol.real D / |det T| · t^(card ι)| ≤ C · t^(card ι - 1)`, `C` uniform in `ξ`.
- **What**: Effective coset lattice-point count (Widmer/GRS Thm 3 form) — `#((ξ + T''ℤ^ι) ∩ t•D) = vol D/|det T| · t^d + O(t^(d-1))`, implied constant uniform in the translate.
- **How**: Transports data through `T.symm`: `D' = T.symm '' D` is bounded/measurable with a transported Lipschitz cover (compose charts with the continuous-linear `T.symm`, `LipschitzWith.comp`), `vol.real D' = vol.real D/|det T|` (`Measure.addHaar_image_linearMap`, `LinearEquiv.det_symm`). A count identity (linear-image injectivity + scaling bijection) reduces to `abs_cardR_translate_sub_volume_le` applied to `D'` at translate `T.symm ξ`.
- **Hypotheses**: `T` a linear equiv; `D` bounded, measurable, Lipschitz-cube-covered frontier.
- **Uses from project**: [`abs_cardR_translate_sub_volume_le`]
- **Used by**: `exists_card_cell_sub_mul_rpow_le`, `exists_card_cell_sub_mul_rpow_le_explicit`. (Externally referenced by docstrings in `NormLeOneLipschitz.lean`.)
- **Visibility**: public · **Lines**: 330–417 · **Notes**: &gt;30 lines; the central reusable export.

### `private theorem natCast_algebraNorm_add_nsmul_mul`
- **Type**: For `M : ℕ`, `x y : 𝓞 K`: `((Algebra.norm ℤ (x + M·y) : ℤ) : ZMod M) = ((Algebra.norm ℤ x : ℤ) : ZMod M)`.
- **What**: The algebraic norm is coset-constant mod `M` on cosets of `M·𝓞_K`.
- **How**: Writes norm as `det` of `leftMulMatrix` in a chosen `ℤ`-basis (`Algebra.norm_eq_matrix_det`); reduces matrix entries mod `M` (`RingHom.map_det`, `mapMatrix`); the `M·leftMulMatrix y` summand vanishes mod `M` (`ZMod.natCast_self`).
- **Hypotheses**: `K` a number field; `M : ℕ`, `x y : 𝓞 K`.
- **Uses from project**: []
- **Used by**: `norm_zmod_eq_of_emb_sub_mem`.
- **Visibility**: private · **Lines**: 426–448 · **Notes**: —.

### `private theorem norm_eq_prod_real_emb_mul_prod_complex`
- **Type**: For `y : K`: `(Algebra.norm ℚ y : ℝ) = (∏_{w real} embedding_of_isReal w.2 y) · (∏_{w complex} ‖w.embedding y‖²)`.
- **What**: Signed product formula — rational norm = (product of real-embedding values) · (nonneg complex factor); fixes the sign as the product of real-embedding signs.
- **How**: Proves the identity over `ℂ` then casts down (`exact_mod_cast`). Groups `Algebra.norm_eq_prod_embeddings ℚ ℂ` over the fibres of `InfinitePlace.mk` (`Finset.prod_fiberwise`); per place the filter is `{embedding w, conjugate (embedding w)}`; real place → single real value, complex place → `σ·conj σ = ‖σ‖²` (`Complex.mul_conj`, `Complex.normSq_eq_norm_sq`); splits real/complex via `prod_eq_prod_mul_prod`.
- **Hypotheses**: `K` a number field; `y : K`.
- **Uses from project**: []
- **Used by**: `natAbs_norm_eq_neg_one_pow_mul_norm`.
- **Visibility**: private · **Lines**: 460–504 · **Notes**: &gt;30 lines.

### `private theorem prod_eq_neg_one_pow_card_mul_prod_abs`
- **Type**: For `s : Finset ι`, `f : ι → ℝ` with `f w &gt; 0` off `s` and `f w &lt; 0` on `s`: `∏ w, f w = (-1)^(s.card) · ∏ w, |f w|`.
- **What**: The sign of a finite product equals `(-1)^(#negatives)` times the product of absolute values.
- **How**: Splits the product over `s` / `sᶜ` (`Finset.prod_mul_prod_compl`), expands `(-1)^s.card` as `∏_{s} (-1)`; matches factor-wise via `abs_of_neg`/`abs_of_pos`.
- **Hypotheses**: sign pattern: `f` positive off `s`, negative on `s`.
- **Uses from project**: []
- **Used by**: `natAbs_norm_eq_neg_one_pow_mul_norm`.
- **Visibility**: private · **Lines**: 508–517 · **Notes**: —.

### `private theorem natAbs_norm_eq_neg_one_pow_mul_norm`
- **Type**: For `y : 𝓞 K` and `s : Finset {w // IsReal w}` with the real coords of `mixedEmbedding K y` negative exactly on `s`: `((Algebra.norm ℤ y).natAbs : ℤ) = (-1)^(s.card) · (Algebra.norm ℤ y)`.
- **What**: On a sign-orthant the absolute integer norm equals a coset-constant **signed** residue `(-1)^#s · Norm`.
- **How**: Combines `norm_eq_prod_real_emb_mul_prod_complex` with `prod_eq_neg_one_pow_card_mul_prod_abs` (real embeddings = mixed coords, `mixedEmbedding_apply_isReal`); the complex factor is `≥ 0` so `|norm| = (∏|real|)·(complex)`; derives `(norm:ℝ) = (-1)^#s · |norm|`, casts to `ℤ`, inverts using `((-1)^#s)² = 1`.
- **Hypotheses**: real coordinates of `mixedEmbedding K y` are `&lt; 0` on `s` and `&gt; 0` off `s`.
- **Uses from project**: [`norm_eq_prod_real_emb_mul_prod_complex`, `prod_eq_neg_one_pow_card_mul_prod_abs`]
- **Used by**: `residue_iff_signed_on_orthant`.
- **Visibility**: private · **Lines**: 524–572 · **Notes**: &gt;30 lines.

### `private theorem card_norm_le_residue_eq_sum_class`
- **Type**: `Nat.card {I // absNorm I ≤ N ∧ (absNorm I : ZMod c) = a} = ∑_{C : ClassGroup} Nat.card {I // (absNorm I ≤ N ∧ (absNorm I : ZMod c)=a) ∧ mk0 I = C}`.
- **What**: The norm-residue count splits as a finite sum of per-class counts over the class group.
- **How**: Establishes finiteness of all pieces (`Ideal.finite_setOf_absNorm_le₀`, `Finite.of_injective`), converts `Nat.card` to `Fintype.card`, and applies `Equiv.sigmaFiberEquiv` (fibres of `I ↦ mk0 I`) + `Fintype.card_sigma`/`card_congr`.
- **Hypotheses**: `[NeZero c]`; residue `a`, bound `N`.
- **Uses from project**: []
- **Used by**: `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`, `tendsto_cardNormLeResidue_div_eq_sum_class`.
- **Visibility**: private · **Lines**: 581–620 · **Notes**: &gt;30 lines.

### `private theorem natCast_eq_iff_mul_natCast_eq`
- **Type**: For `NJ &gt; 0`: `((m : ZMod cc) = (a : ZMod cc)) ↔ ((m·NJ : ZMod (cc·NJ)) = (a·NJ : ZMod (cc·NJ)))`.
- **What**: Modular cancellation — the residue condition transports through multiplication of both value and modulus by `NJ`.
- **How**: Unfolds `ZMod.natCast_eq_natCast_iff` to `Nat.ModEq`, uses `Nat.mul_mod_mul_right`, then `Nat.eq_of_mul_eq_mul_right`.
- **Hypotheses**: `0 &lt; NJ`.
- **Uses from project**: []
- **Used by**: `principalize_iff`.
- **Visibility**: private · **Lines**: 627–632 · **Notes**: —.

### `private theorem principalize_iff`
- **Type**: With `mk0 J = C⁻¹`, `0 &lt; absNorm J`: the predicate "`absNorm I ≤ N ∧ (absNorm I:ZMod c)=a ∧ mk0 I = C`" ↔ "`IsPrincipal (J·I) ∧ absNorm (J·I) ≤ N·NJ ∧ (absNorm (J·I):ZMod (c·NJ)) = a.val·NJ`" (under `Equiv.dvd J`).
- **What**: Per-ideal principalization correspondence under `I ↦ J·I`.
- **How**: `mk0 I = C ↔ IsPrincipal (J·I)` via `ClassGroup.mk0_eq_one_iff`, `mk0 (J·I) = C⁻¹·mk0 I`; norm scales by `NJ` (`map_mul`); residue transports by `natCast_eq_iff_mul_natCast_eq`; bound by `Nat.mul_le_mul_right_iff`; `tauto`.
- **Hypotheses**: `[NeZero c]`; `mk0 J = C⁻¹`; `0 &lt; absNorm J`.
- **Uses from project**: [`natCast_eq_iff_mul_natCast_eq`]
- **Used by**: `card_principalize`, `card_principalize_dvd`.
- **Visibility**: private · **Lines**: 640–679 · **Notes**: &gt;30 lines.

### `private theorem card_principalize`
- **Type**: With `mk0 J = C⁻¹`, `0 &lt; absNorm J`: `Nat.card {I // (absNorm I ≤ N ∧ res a) ∧ mk0 I = C} = Nat.card {I // J ∣ I ∧ (IsPrincipal I ∧ absNorm I ≤ N·NJ ∧ res (a.val·NJ) mod c·NJ)}`.
- **What**: `Nat.card`-level principalization: class-`C` residue count = `J`-divisible principal residue count at scaled modulus.
- **How**: `nonZeroDivisors_dvd_iff_dvd_coe`, then `Nat.card_congr` of `(Equiv.dvd J).subtypeEquiv principalize_iff` composed with `Equiv.subtypeSubtypeEquivSubtypeInter`.
- **Hypotheses**: `[NeZero c]`; `mk0 J = C⁻¹`; `0 &lt; absNorm J`.
- **Uses from project**: [`principalize_iff`]
- **Used by**: `exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`, `cardNormLeResidueClassDvd_div_density`.
- **Visibility**: private · **Lines**: 686–701 · **Notes**: —.

### `private theorem map_span_int_linearEquiv`
- **Type**: For `f : E ≃ₗ[ℝ] F` and `S : Set E`: `f '' (span ℤ S : Set E) = (span ℤ (f '' S) : Set F)`.
- **What**: An `ℝ`-linear equiv carries `ℤ`-spans to `ℤ`-spans (as sets).
- **How**: `Submodule.map_span` for `f.restrictScalars ℤ`, plus `Submodule.map_coe`.
- **Hypotheses**: `E, F` real modules; `f` an `ℝ`-linear equiv.
- **Uses from project**: []
- **Used by**: `exists_latticeEquiv_image_idealLattice`, `span_image_basisFun_eq`, `smul_chart_lattice_eq`, and inline span-rewrites in `exists_card_fibre_dvd_eq_card_cell`, `chart_lattice_eq_map`, etc. (10 occurrences) — a core utility.
- **Visibility**: private · **Lines**: 714–722 · **Notes**: —.

### `private theorem cone_normLe_eq_smul_normLeOne`
- **Type**: For `t ≥ 1`: `{x : mixedSpace K | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ t^(finrank ℚ K)} = t • normLeOne K`.
- **What**: The norm-`≤ t^d` slice of the fundamental cone is the real dilation `t • normLeOne K`.
- **How**: `smul_mem_iff_mem` preserves the cone under scaling, `mixedEmbedding.norm_smul` multiplies the norm by `t^d` (`|t|=t`); two-directional `ext`.
- **Hypotheses**: `1 ≤ t`.
- **Uses from project**: []
- **Used by**: `card_fibre_eq_card_cell`, `exists_card_fibre_dvd_eq_card_cell` (4 occurrences).
- **Visibility**: private · **Lines**: 729–750 · **Notes**: —.

### `private theorem exists_latticeEquiv_image_idealLattice`
- **Type**: `∃ T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ), T '' Λ = (stdBasis K).equivFunL '' idealLattice K (mk0 K J)`, where `Λ = span ℤ (range (Pi.basisFun ℝ (index K)))`.
- **What**: The ideal lattice, transported through the chart `Φ = (stdBasis K).equivFunL`, is a full standard lattice `T '' ℤ^(index K)`.
- **How**: Builds a basis `c` = `Φ ∘ fractionalIdealLatticeBasis K I` reindexed to `index K` (cardinalities match via `fractionalIdeal_rank`/`RingOfIntegers.rank`/`mixedEmbedding.finrank`); sets `T = (Pi.basisFun).equiv c`; then `T '' ℤ^ι = span ℤ (range c) = Φ '' span ℤ idealLatticeBasis` (`map_span_int_linearEquiv`, `span_idealLatticeBasis`).
- **Hypotheses**: `K` a number field; `J : (Ideal (𝓞 K))⁰`.
- **Uses from project**: [`map_span_int_linearEquiv`]
- **Used by**: `exists_card_idealSet_residue_le`, `exists_card_idealSet_residue_real_le`, `exists_card_idealSet_residue_real_le_dvd` (called twice there) (6 occurrences).
- **Visibility**: private · **Lines**: 760–787 · **Notes**: &gt;30 lines.

### `private theorem exists_lipschitz_cube_cover_hyperplane_slab`
- **Type**: For coordinate `j : ι`, `R ≥ 0`: `∃ M φ, LipschitzWith M φ ∧ {x | x j = 0 ∧ ∀ i, |x i| ≤ R} ⊆ φ '' Icc 0 1`.
- **What**: A bounded coordinate-hyperplane slab is covered by one Lipschitz image of the unit cube (constant `2R`).
- **How**: Parametrises the `card ι - 1` free coordinates affinely `c ↦ 2R·c - R` via a bijection `Fin (card ι - 1) ≃ {i // i ≠ j}` (`Fintype.equivFinOfCardEq`, `card_subtype_compl`), sets coord `j` to `0`; Lipschitz via `dist_pi_le_iff`; containment by `(x(σk)+R)/(2R)` with `R=0` edge case.
- **Hypotheses**: `0 ≤ R`.
- **Uses from project**: []
- **Used by**: `exists_frontier_cover_inter_orthant`.
- **Visibility**: private · **Lines**: 795–838 · **Notes**: &gt;30 lines.

### `private theorem exists_generator_diff_of_coset`
- **Type**: If `a₁, a₂ ∈ idealSet K J` differ by a vector of `m • idealLattice K (mk0 K J)`, then `∃ w ∈ J`, `gen(a₁) = gen(a₂) + m·w` (generators = `preimageOfMemIntegerSet (idealSetMap …)`).
- **What**: A coset translation of cone points translates the algebraic-integer generator by `m·w` with `w ∈ J`.
- **How**: Unpacks the lattice membership (`mem_idealLattice`, `FractionalIdeal.mem_coeIdeal`) to `y ∈ J`; uses `mixedEmbedding K gen = a` (`mixedEmbedding_preimageOfMemIntegerSet`, `idealSetMap_apply`) and `mixedEmbedding`-injectivity (`mixedEmbedding_injective`, `RingOfIntegers.coe_injective`), `linear_combination`.
- **Hypotheses**: `a₁ - a₂ ∈ m • idealLattice`.
- **Uses from project**: []
- **Used by**: **unused in file** — only its own definition occurs (superseded by `sub_mem_nsmul_of_coord_eq` + `norm_zmod_eq_of_emb_sub_mem`, which take the round-coordinate route instead). Dead code.
- **Visibility**: private · **Lines**: 847–874 · **Notes**: &gt;30 lines; DEAD (no consumer).

### `private theorem exists_lipschitz_cover_union`
- **Type**: If `A` and `B` each have a finite Lipschitz cube cover, so does `A ∪ B`.
- **What**: Union combinator for Lipschitz cube covers.
- **How**: Concatenates families over `Fin (m1+m2)` via `finSumFinEquiv`/`Sum.elim`, takes `max M1 M2` (`LipschitzWith.weaken`); `Set.union_subset` + `subset_iUnion_of_subset`.
- **Hypotheses**: cube covers of `A` and of `B`.
- **Uses from project**: []
- **Used by**: `exists_frontier_cover_inter_orthant`.
- **Visibility**: private · **Lines**: 881–902 · **Notes**: —.

### `private theorem exists_lipschitz_cover_iUnion`
- **Type**: A `Fintype`-indexed union of Lipschitz-cube-covered sets is Lipschitz cube-covered.
- **What**: Finite `iUnion` combinator for Lipschitz cube covers.
- **How**: `choose`s per-`g` cover data, concatenates over `Σ g, Fin (mf g)` (`Fintype.equivFin`), takes `Finset.univ.sup Mf` (`Finset.le_sup`, `LipschitzWith.weaken`); `iUnion_subset` + `subset_iUnion_of_subset`.
- **Hypotheses**: a cube cover for each `A g`.
- **Uses from project**: []
- **Used by**: `exists_frontier_cover_inter_orthant`.
- **Visibility**: private · **Lines**: 907–923 · **Notes**: —.

### `private theorem frontier_signOrthant_subset`
- **Type**: `frontier {y | (∀ k ∈ s, y(g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y(g k))} ⊆ ⋃ k, {y | y(g k) = 0}`.
- **What**: The frontier of a closed sign-orthant cut lies in the union of the cut coordinate hyperplanes.
- **How**: The orthant `O` is closed (`isClosed_biInter` of `isClosed_le`), its strict version `Os` open (`isOpen_biInter_finset` of `isOpen_lt`) and `⊆ O`; a frontier point lies in `O` but not `interior O`; if no `y(g k)=0` it would lie in `Os ⊆ interior O` (`mem_interior`), contradiction.
- **Hypotheses**: `g : κ → ι`, `s : Finset κ`.
- **Uses from project**: []
- **Used by**: `exists_frontier_cover_inter_orthant`.
- **Visibility**: private · **Lines**: 929–969 · **Notes**: &gt;30 lines.

### `private theorem exists_frontier_cover_inter_orthant`
- **Type**: If `D₀` is bounded with a Lipschitz-cube-covered frontier, then `frontier (D₀ ∩ orthant_{g,s})` also has a finite Lipschitz cube cover.
- **What**: Orthant-cutting preserves the Lipschitz-cube-covered-frontier property.
- **How**: `frontier_inter_subset` bounds `frontier (D₀ ∩ O)` by `frontier D₀ ∪ (closure D₀ ∩ frontier O)`; `frontier_signOrthant_subset` sends the second part into bounded coordinate-hyperplane slices (`closure D₀` is bounded → uniform `R`); each slice is cube-covered by `exists_lipschitz_cube_cover_hyperplane_slab`; combined via `exists_lipschitz_cover_union`/`exists_lipschitz_cover_iUnion`.
- **Hypotheses**: `D₀` bounded; cube cover of `frontier D₀`.
- **Uses from project**: [`frontier_signOrthant_subset`, `exists_lipschitz_cube_cover_hyperplane_slab`, `exists_lipschitz_cover_union`, `exists_lipschitz_cover_iUnion`]
- **Used by**: `exists_card_cell_sub_mul_rpow_le`, `exists_card_cell_sub_mul_rpow_le_explicit`.
- **Visibility**: private · **Lines**: 977–1006 · **Notes**: &gt;30 lines.

### `private theorem mem_span_int_basisFun_iff`
- **Type**: `v ∈ span ℤ (range (Pi.basisFun ℝ ι)) ↔ ∀ i, ∃ n : ℤ, v i = (n : ℝ)`.
- **What**: Membership in the standard integer lattice ⟺ all coordinates are integers.
- **How**: `Submodule.span_induction` (mem/zero/add/smul cases) for `→`; for `←`, writes `v = ∑ᵢ (n i) • basisFun i` (`Finset.sum_eq_single`) and `sum_mem`/`zsmul_mem`.
- **Hypotheses**: none beyond `[Fintype ι]`.
- **Uses from project**: []
- **Used by**: `exists_int_coord_of_mem`, `sub_mem_nsmul_of_coord_eq`, `mem_coset_iff_cos_eq`, `card_fibre_eq_card_cell`, `exists_card_fibre_dvd_eq_card_cell` (8 occurrences) — core utility.
- **Visibility**: private · **Lines**: 1010–1038 · **Notes**: &gt;30 lines.

### `private theorem card_isPrincipal_dvd_norm_le_residue`
- **Type**: `Nat.card {I // J ∣ I ∧ IsPrincipal I ∧ (absNorm I:ℝ) ≤ s ∧ (absNorm I:ZMod m)=b} · torsionOrder K = Nat.card {a : idealSet K J // mixedEmbedding.norm a ≤ s ∧ (intNorm (idealSetEquiv K J a):ZMod m)=b}`.
- **What**: The residue-decorated torsion bridge: mathlib's `card_isPrincipal_dvd_norm_le` refined by a norm-residue condition.
- **How**: For `s ≥ 0`, fibres over the norm value `i ∈ Iic ⌊s⌋₊` (`Equiv.ofFiberEquiv`), and on each fibre runs the chain `prodSubtypeFstEquivSubtypeProd → subtypeSubtypeEquivSubtypeInter → idealSetEquivNorm.symm → intNorm fibre`, with empty-fibre handling when `(i:ZMod m)≠b`; `s &lt; 0` gives both sides empty.
- **Hypotheses**: `J`, `m b : ℕ`, `s : ℝ`.
- **Uses from project**: []
- **Used by**: `exists_card_dvd_principal_residue_eq_sub_mul_rpow_le`, `exists_card_dvd_principal_residue_real_le`, `cardNormLeResidueClassDvd_div_density` (8 occurrences).
- **Visibility**: private · **Lines**: 1049–1110 · **Notes**: &gt;30 lines; `set_option backward.isDefEq.respectTransparency false` + `open Classical`.

### `private theorem exists_card_cell_sub_mul_rpow_le`
- **Type**: For automorphism `T`, `m` with `(m:ℝ)≠0`, bounded measurable `D₀` (cube-covered frontier), `g : κ → ι`, `s : Finset κ`: `∃ leadC C, ∀ ξ t, 1 ≤ t → |Nat.card ↑((ξ +ᵥ ((m·)∘T)''Λ) ∩ t•(D₀ ∩ orthant)) - leadC·t^d| ≤ C·t^(d-1)`.
- **What**: Per-cell effective count — workhorse specialised to the `m`-sublattice `(m·)∘T` and an orthant-cut region. (Implicit-`κ` form.)
- **How**: Sets `T' = (smulOfNeZero m).trans T`, `Ds = D₀ ∩ orthant`; `Ds` bounded/measurable (orthant closed via `isClosed_biInter`); applies `exists_card_coset_inter_smul_sub_volume_mul_rpow_le T'` with the frontier cover from `exists_frontier_cover_inter_orthant`; reads off `leadC = vol.real Ds/|det T'|`.
- **Hypotheses**: `(m:ℝ)≠0`; `D₀` bounded, measurable, cube-covered frontier.
- **Uses from project**: [`exists_card_coset_inter_smul_sub_volume_mul_rpow_le`, `exists_frontier_cover_inter_orthant`]
- **Used by**: `exists_card_residue_fibre_sub_mul_rpow_le`.
- **Visibility**: private · **Lines**: 1121–1153 · **Notes**: &gt;30 lines; `set_option linter.unusedFintypeInType false`.

### `private theorem exists_int_coord_of_mem`
- **Type**: Given `hT` (the chart identity) and `x ∈ idealLattice K (mk0 K J)`: `∃ n : ℤ, (T.symm (Φ x)) i = (n : ℝ)` for each coordinate `i`.
- **What**: A lattice point has integer coordinates in the chart `T`.
- **How**: `Φ x ∈ T '' ℤ^ι` (by `hT`), so `T.symm (Φ x) = v` with `v ∈ ℤ^ι`; apply `mem_span_int_basisFun_iff`.
- **Hypotheses**: chart identity `hT`; `x ∈ idealLattice`.
- **Uses from project**: [`mem_span_int_basisFun_iff`]
- **Used by**: `sub_mem_nsmul_of_coord_eq`, `mem_coset_iff_cos_eq` (4 occurrences).
- **Visibility**: private · **Lines**: 1161–1176 · **Notes**: —.

### `private theorem sub_mem_nsmul_of_coord_eq`
- **Type**: If `x₁, x₂ ∈ idealLattice` have equal rounded coordinates mod `m` in chart `T`, then `x₁ - x₂ ∈ (m:ℝ) • idealLattice`.
- **What**: Equal reduced coordinates ⟹ difference lies in the `m`-sublattice (coset class collapses to a lattice translation).
- **How**: `round` of integer coordinates recovers `n₁, n₂` (`round_intCast`); the residue equality gives `m ∣ (n₁ᵢ - n₂ᵢ)` (`ZMod.intCast_zmod_eq_zero_iff_dvd`); the integer quotient vector `p` lifts (`mem_span_int_basisFun_iff`) to a lattice element `z` via `hT`; transports the difference back through `Φ` (injectivity).
- **Hypotheses**: both in `idealLattice`; reduced-coordinate equality mod `m`.
- **Uses from project**: [`exists_int_coord_of_mem`, `mem_span_int_basisFun_iff`]
- **Used by**: `norm_zmod_eq_of_emb_sub_mem` (called inside `exists_card_residue_fibre_sub_mul_rpow_le` and `residue_fibre_const_aux`).
- **Visibility**: private · **Lines**: 1182–1231 · **Notes**: &gt;30 lines.

### `private theorem norm_zmod_eq_of_emb_sub_mem`
- **Type**: If `mixedEmbedding K x - mixedEmbedding K y ∈ (m:ℝ)•idealLattice K (mk0 K J)`, then `((Algebra.norm ℤ x:ℤ):ZMod m) = ((Algebra.norm ℤ y:ℤ):ZMod m)`.
- **What**: A lattice-difference of two integers makes their algebraic norms congruent mod `m`.
- **How**: Unpacks lattice membership to `x - y = m·w` in `𝓞 K` (`mixedEmbedding` injective, `RingOfIntegers.coe_injective`); then `natCast_algebraNorm_add_nsmul_mul`.
- **Hypotheses**: embedding difference in the `m`-sublattice.
- **Uses from project**: [`natCast_algebraNorm_add_nsmul_mul`]
- **Used by**: `exists_card_residue_fibre_sub_mul_rpow_le`, `residue_fibre_const_aux`.
- **Visibility**: private · **Lines**: 1239–1262 · **Notes**: —.

### `private theorem residue_iff_signed_on_orthant`
- **Type**: With real coords of `a` negative exactly on `s`: `((intNorm (idealSetEquiv K J a):ZMod m)=b) ↔ (((-1)^s.card · Algebra.norm ℤ gen_a : ℤ):ZMod m)=b`.
- **What**: On a sign-orthant the absolute norm residue becomes the signed residue `(-1)^#s · Norm`.
- **How**: `natAbs_norm_eq_neg_one_pow_mul_norm` applied to the generator `gen_a = preimageOfMemIntegerSet …` (with `mixedEmbedding K gen_a = a`); `intNorm = natAbs (Algebra.norm ℤ gen_a)` by `rfl`; cast through `Int.cast_natCast`.
- **Hypotheses**: real coords of `a` negative on `s`, positive off `s`.
- **Uses from project**: [`natAbs_norm_eq_neg_one_pow_mul_norm`]
- **Used by**: `exists_card_residue_fibre_sub_mul_rpow_le`, `residue_fibre_const_aux`.
- **Visibility**: private · **Lines**: 1269–1286 · **Notes**: —.

### `private theorem mem_coset_iff_cos_eq`
- **Type**: For `x ∈ idealLattice`: `Φ x ∈ (T(k.val) +ᵥ ((m·)∘T)''Λ) ↔ ∀ i, (round((T.symm (Φ x))ᵢ):ZMod m) = kᵢ`.
- **What**: Coset membership in `T(k') + m·(T''ℤ^ι)` ⟺ reduced integer coordinates equal `k` mod `m`.
- **How**: Recovers integer coordinates `n` (`exists_int_coord_of_mem`, `round_intCast`); reduces the class equality `nᵢ ≡ kᵢ` to divisibility `m ∣ (nᵢ - kᵢ.val)`; both directions via the witness `p` with `nᵢ = kᵢ.val + m·pᵢ` (`mem_span_int_basisFun_iff`, `LinearEquiv.eq_symm_apply`, `omega`).
- **Hypotheses**: `[NeZero m]`, `(m:ℝ)≠0`; chart identity; `x ∈ idealLattice`.
- **Uses from project**: [`exists_int_coord_of_mem`, `mem_span_int_basisFun_iff`]
- **Used by**: `card_fibre_eq_card_cell`, `exists_card_fibre_dvd_eq_card_cell`.
- **Visibility**: private · **Lines**: 1294–1347 · **Notes**: &gt;30 lines.

### `private theorem card_fibre_eq_card_cell`
- **Type**: For `t ≥ 1`: `Nat.card {a : idealSet K J // norm a ≤ t^d ∧ orthant(s) ∧ coset(k)} = Nat.card ↑((T(k.val) +ᵥ ((m·)∘T)''Λ) ∩ t•(Φ''normLeOne K ∩ orthant_s))`.
- **What**: Geometric per-cell bijection — cone points of `idealSet K J` in cell `(s,k)` ⟷ lattice points of the dilated orthant cell.
- **How**: Counting map `f a = Φ a` is injective; identifies `range f` with the RHS intersection: cone homogeneity (`cone_normLe_eq_smul_normLeOne`), `Φ`-linearity/scaling (`image_smul_comm`), real coords of `Φ x` = real coords of `x` (`stdBasis_apply_isReal`), region-membership equivalence `hreg` (via `fundamentalCone.normAtPlace_pos_of_mem` for nonzero coords, `Set.mem_smul_set_iff_inv_smul_mem₀`, `nlinarith`), and `mem_coset_iff_cos_eq` for the coset condition; `Nat.card_range_of_injective`.
- **Hypotheses**: `[NeZero m]`, `(m:ℝ)≠0`; chart identity; `1 ≤ t`.
- **Uses from project**: [`cone_normLe_eq_smul_normLeOne`, `mem_coset_iff_cos_eq`, `mem_span_int_basisFun_iff`]
- **Used by**: `exists_card_residue_fibre_sub_mul_rpow_le`, `exists_card_residue_fibre_sub_mul_rpow_le_explicit`, `exists_card_fibre_dvd_eq_card_cell`(docstring) (6 occurrences).
- **Visibility**: private · **Lines**: 1357–1491 · **Notes**: &gt;30 lines; the `hreg` block is duplicated in `exists_card_fibre_dvd_eq_card_cell`.

### `private theorem exists_card_residue_fibre_sub_mul_rpow_le`
- **Type**: For fixed orthant `s`, coset `k`: `∃ L C, ∀ t, 1 ≤ t → |Nat.card {a // (norm a ≤ t^d ∧ residue b) ∧ orthant(s) ∧ coset(k)} - L·t^d| ≤ C·t^(d-1)`.
- **What**: Per-(orthant,coset) effective residue count. (Implicit-`κ` form.)
- **How**: Proves residue is constant on the cell (`hconst`: `residue_iff_signed_on_orthant` + `sub_mem_nsmul_of_coord_eq` + `norm_zmod_eq_of_emb_sub_mem`); case split on whether some cell point carries residue `b`: if yes, the residue filter is redundant so the count equals the cell count (`card_fibre_eq_card_cell` then `exists_card_cell_sub_mul_rpow_le`, with `t^d = t^(card index)` via `finrank`); if no, the cell is empty.
- **Hypotheses**: `[NeZero m]`, `(m:ℝ)≠0`; chart identity; cube cover of `frontier (Φ''normLeOne)`.
- **Uses from project**: [`residue_iff_signed_on_orthant`, `sub_mem_nsmul_of_coord_eq`, `norm_zmod_eq_of_emb_sub_mem`, `card_fibre_eq_card_cell`, `exists_card_cell_sub_mul_rpow_le`]
- **Used by**: `exists_card_idealSet_residue_le`, `exists_card_idealSet_residue_real_le`.
- **Visibility**: private · **Lines**: 1501–1615 · **Notes**: &gt;30 lines.

### `private theorem finite_idealSet_norm_le`
- **Type**: `Finite {a : idealSet K J // mixedEmbedding.norm a ≤ s}`.
- **What**: The cone points of `idealSet K J` of bounded norm form a finite set.
- **How**: Injects (via `integerSetEquiv ∘ idealSetMap`) into the finite product `{I // absNorm I ≤ ⌊s⌋₊} × torsion K` (`Ideal.finite_setOf_absNorm_le₀`, norm bound by `Nat.le_floor` + `absNorm_span_singleton`, injectivity via `integerSetEquiv` and `idealSetMap` injectivity).
- **Hypotheses**: `J`, `s : ℝ`.
- **Uses from project**: []
- **Used by**: `exists_card_idealSet_residue_le`, `exists_card_idealSet_residue_real_le`, `card_idealSet_residue_eq_sum_cell` (4 occurrences).
- **Visibility**: private · **Lines**: 1622–1647 · **Notes**: &gt;30 lines.

### `private theorem exists_card_idealSet_residue_le`
- **Type**: `∃ κ C', ∀ N ≥ 1, |Nat.card {a : idealSet K J // norm a ≤ (N·NJ:ℝ) ∧ residue b} - κ·N| ≤ C'·N^(1 - 1/d)`.
- **What**: Effective count of cone points of `idealSet K J` with a norm residue (the Widmer/GRS geometric core, norm bound coupled to `N·N(J)`).
- **How**: Picks chart `T` (`exists_latticeEquiv_image_idealLattice`) and frontier cover (`normLeOne_frontier_lipschitz_cover_index`); `choose`s per-(orthant,coset) estimates (`exists_card_residue_fibre_sub_mul_rpow_le`); partitions the count over `(orthant, coset)` cells (`Equiv.sigmaFiberEquiv`, `finite_idealSet_norm_le`) at `tN = (N·NJ)^(1/d)`; combines with `Real.rpow` algebra (`htNd`, `htNd1`), `Finset.abs_sum_le_sum_abs`, `Finset.sum_le_sum`.
- **Hypotheses**: `[NeZero m]`; `b : ℕ`; `J`.
- **Uses from project**: [`exists_latticeEquiv_image_idealLattice`, `exists_card_residue_fibre_sub_mul_rpow_le`, `finite_idealSet_norm_le`] (+ external `normLeOne_frontier_lipschitz_cover_index`)
- **Used by**: `exists_card_dvd_principal_residue_eq_sub_mul_rpow_le`.
- **Visibility**: private · **Lines**: 1673–1769 · **Notes**: &gt;30 lines.

### `private theorem exists_card_dvd_principal_residue_eq_sub_mul_rpow_le`
- **Type**: `∃ κ C', ∀ N ≥ 1, |Nat.card {I // J ∣ I ∧ (IsPrincipal I ∧ absNorm I ≤ N·NJ ∧ residue b)} - κ·N| ≤ C'·N^(1-1/d)`.
- **What**: Effective count of `J`-divisible principal ideals with a norm residue (norm-bound coupled to `N·N(J)`).
- **How**: Reduces to `exists_card_idealSet_residue_le` via the torsion bridge `card_isPrincipal_dvd_norm_le_residue` at `s = N·NJ`; divides the cone-point estimate by `torsionOrder K &gt; 0` (`torsionOrder_ne_zero`); scales `κ, C'` by `1/torsionOrder`.
- **Hypotheses**: `[NeZero m]`; `b : ℕ`; `J`.
- **Uses from project**: [`exists_card_idealSet_residue_le`, `card_isPrincipal_dvd_norm_le_residue`]
- **Used by**: `exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`.
- **Visibility**: private · **Lines**: 1782–1833 · **Notes**: &gt;30 lines.

### `private theorem exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`
- **Type**: `∃ κ C', ∀ N ≥ 1, |Nat.card {I // (absNorm I ≤ N ∧ res a) ∧ mk0 I = C} - κ·N| ≤ C'·N^(1-1/d)`.
- **What**: Per-class effective residue count.
- **How**: Picks `J` with `mk0 J = C⁻¹` (`ClassGroup.mk0_surjective`); principalizes (`card_principalize`) and invokes `exists_card_dvd_principal_residue_eq_sub_mul_rpow_le` at modulus `c·N(J)`, residue `a.val·N(J)`.
- **Hypotheses**: `[NeZero c]`; residue `a`, class `C`.
- **Uses from project**: [`card_principalize`, `exists_card_dvd_principal_residue_eq_sub_mul_rpow_le`]
- **Used by**: `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`, `exists_tendsto_cardNormLeResidueClass_div`, `cardNormLeResidueClassDvd_sub_mul_rpow_le` (9 occurrences).
- **Visibility**: private · **Lines**: 1844–1862 · **Notes**: —.

### `private theorem tendsto_div_atTop_of_sub_mul_rpow_le`
- **Type**: For `d ≥ 1`: if `∀ N ≥ 1, |f N - κ·N| ≤ C'·N^(1-1/d)` then `(fun N ↦ f N / N) → κ`.
- **What**: An effective `O(N^(1-1/d))` estimate pins `κ` as the limit of `f N / N`.
- **How**: Dominating sequence `|C'|·N^(-1/d) → 0` (`tendsto_rpow_neg_atTop`, `tendsto_natCast_atTop_atTop`); `squeeze_zero'` on `‖f N/N - κ‖`, using `N^(1-1/d) = N^(-1/d)·N` (`Real.rpow_add`).
- **Hypotheses**: `0 &lt; d`; the effective bound for `N ≥ 1`.
- **Uses from project**: []
- **Used by**: 14 occurrences — `exists_tendsto_cardNormLeResidue_div`, `exists_tendsto_cardNormLeResidueClass_div`, `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`, `tendsto_count_div_of_cone_bridge`, `cardNormLeResidueClassDvd_sub_mul_rpow_le`, `cardNormLeResidueClass_div_density`. Core glue.
- **Visibility**: private · **Lines**: 1870–1897 · **Notes**: &gt;30 lines.

### `theorem exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le` — PUBLIC
- **Type**: `(K) (c) [NeZero c] (a : ZMod c) : ∃ κ C', ∀ N ≥ 1, |Nat.card {I // absNorm I ≤ N ∧ (absNorm I:ZMod c)=a} - κ·N| ≤ C'·N^(1-1/d)`.
- **What**: Effective ideal count by norm residue (per-residue, all classes).
- **How**: Splits by ideal class (`card_norm_le_residue_eq_sum_class`); sums per-class effective counts (`exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`) over the finite class group; bounds the total error by `Finset.abs_sum_le_sum_abs` + `le_abs_self`.
- **Hypotheses**: `[NeZero c]`; residue `a`.
- **Uses from project**: [`card_norm_le_residue_eq_sum_class`, `exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`]
- **Used by**: `exists_tendsto_cardNormLeResidue_div`, `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`.
- **Visibility**: public · **Lines**: 1905–1932 · **Notes**: &gt;30 lines.

### `private def cardNormLeResidue`
- **Type**: `(K) (c : ℕ) (a : ZMod c) (N : ℕ) : ℕ := Nat.card {I // absNorm I ≤ N ∧ (absNorm I:ZMod c)=a}`.
- **What**: Abbreviation — number of nonzero integral ideals of norm `≤ N` with norm `≡ a (mod c)`.
- **How**: Direct `Nat.card` of the subtype (real definition, no sorry).
- **Hypotheses**: number field `K`; `c`, `a`, `N`.
- **Uses from project**: []
- **Used by**: 20 occurrences — `exists_tendsto_cardNormLeResidue_div`, `cardNormLeResidue_density_eq_of_mem_subgroup`, `tendsto_cardNormLeResidue_div_eq_sum_class`, `cardNormLeResidue_density_transfer`, `cardNormLeResidue_density_const_of_realized`, `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`.
- **Visibility**: private · **Lines**: 1938–1941 · **Notes**: —.

### `private theorem exists_tendsto_cardNormLeResidue_div`
- **Type**: `(K) (c) [NeZero c] (a) : ∃ κ, (fun N ↦ cardNormLeResidue K c a N / N) → κ`.
- **What**: The norm-residue density `lim cardNormLeResidue/N` exists.
- **How**: `tendsto_div_atTop_of_sub_mul_rpow_le` applied to `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le` (`Module.finrank_pos`).
- **Hypotheses**: `[NeZero c]`; residue `a`.
- **Uses from project**: [`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`, `tendsto_div_atTop_of_sub_mul_rpow_le`, `cardNormLeResidue`]
- **Used by**: `cardNormLeResidue_density_eq_of_mem_subgroup`, `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`, `cardNormLeResidue_density_const_of_realized`, `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`.
- **Visibility**: private · **Lines**: 1945–1951 · **Notes**: —.

### `private theorem sum_char_apply_eq_zero_of_ne_one`
- **Type**: For finite commutative `G`, `g ≠ 1`: `∑ χ : G →* ℂˣ, ((χ g:ℂˣ):ℂ) = 0`.
- **What**: Character-**column** orthogonality (sum over all characters at a fixed nontrivial `g` vanishes).
- **How**: A separating `χ₀` with `χ₀ g ≠ 1` exists (`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`, with `HasEnoughRootsOfUnity ℂ` from algebraic closedness); reindexing by `χ ↦ χ₀·χ` (`Group.mulLeft_bijective`) scales the sum by `χ₀ g`, forcing it to `0`.
- **Hypotheses**: `[Fintype (G →* ℂˣ)]`; `g ≠ 1`.
- **Uses from project**: []
- **Used by**: `cardNormLeResidue_density_eq_of_mem_subgroup`.
- **Visibility**: private · **Lines**: 1958–1973 · **Notes**: —.

### `private theorem cardNormLeResidue_density_eq_of_mem_subgroup`
- **Type**: Given Fourier-decay `hF` (all nontrivial `S`-character-twisted count averages → 0), `a, a' ∈ S`, densities `κ, κ'` of residues `a, a'`: `κ = κ'`.
- **What**: κ-uniformity over the realized-residue subgroup, derived **from** Fourier decay (Fourier-inversion direction).
- **How**: Both densities are values of `κf` (`exists_tendsto_cardNormLeResidue_div`, `tendsto_nhds_unique`); `hF` says all nontrivial `S`-Fourier coefficients `∑ₛ χ(s)·κf s` vanish (`hhat`); Fourier inversion `card(S→ℂˣ)·κf u = ∑ₛ κf s` for all `u` (column orthogonality `sum_char_apply_eq_zero_of_ne_one`, `Finset.sum_comm`), so `κf` is constant; `mul_left_cancel₀`.
- **Hypotheses**: `[NeZero c]`; `hF`; `a, a' ∈ S`; densities exist.
- **Uses from project**: [`exists_tendsto_cardNormLeResidue_div`, `sum_char_apply_eq_zero_of_ne_one`, `cardNormLeResidue`]
- **Used by**: `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`.
- **Visibility**: private · **Lines**: 2019–2088 · **Notes**: &gt;30 lines; long expository docstring describing the now-superseded gap status.

### `theorem exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform` — PUBLIC
- **Type**: `(K) (c) [NeZero c] (S : Subgroup (ZMod c)ˣ) (hF) : ∃ κ C', ∀ a ∈ S, ∀ N ≥ 1, |Nat.card {I // absNorm I ≤ N ∧ res a} - κ·N| ≤ C'·N^(1-1/d)` — one `(κ,C')` working for all `a ∈ S`.
- **What**: Norm-residue density transfer — a single uniform leading constant `κ` across the realized subgroup `S`.
- **How**: Per-residue constants and densities (`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`, `exists_tendsto_cardNormLeResidue_div`, with `κf a = κlim a` by `tendsto_div_atTop_of_sub_mul_rpow_le`); constancy of `κlim` over `S` (`cardNormLeResidue_density_eq_of_mem_subgroup`); take `κ = κlim 1`, `C' = ∑_b |C'f b|`.
- **Hypotheses**: `[NeZero c]`; subgroup `S`; Fourier-decay `hF`.
- **Uses from project**: [`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`, `exists_tendsto_cardNormLeResidue_div`, `tendsto_div_atTop_of_sub_mul_rpow_le`, `cardNormLeResidue_density_eq_of_mem_subgroup`]
- **Used by**: external — `ZetaProduct.lean:1612` (consumes it at `S = range autToPow`).
- **Visibility**: public · **Lines**: 2109–2140 · **Notes**: &gt;30 lines.

### `private theorem sum_char_self_eq_zero_of_ne_one`
- **Type**: For finite commutative `G`, nontrivial `χ : G →* ℂˣ`: `∑ g : G, ((χ g:ℂˣ):ℂ) = 0`.
- **What**: Character-**row** orthogonality (sum over all group elements of a fixed nontrivial character vanishes).
- **How**: A separating `g₀` with `χ g₀ ≠ 1` exists (else `χ = 1`, `MonoidHom.ext`); reindexing by `g ↦ g₀·g` (`Group.mulLeft_bijective`) scales the sum by `χ g₀`, forcing it to `0`.
- **Hypotheses**: `[Fintype G]`; `χ ≠ 1`.
- **Uses from project**: []
- **Used by**: `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`.
- **Visibility**: private · **Lines**: 2149–2165 · **Notes**: —.

### `private def cardNormLeResidueClass`
- **Type**: `(c) (y : ZMod c) (C : ClassGroup) (N) : ℕ := Nat.card {I // (absNorm I ≤ N ∧ (absNorm I:ZMod c)=y) ∧ mk0 I = C}`.
- **What**: Per-class norm-residue count (norm `≤ N`, residue `y`, class `C`).
- **How**: Direct `Nat.card` (real def).
- **Hypotheses**: number field `K`; `c, y, C, N`.
- **Uses from project**: []
- **Used by**: 32 occurrences — `exists_tendsto_cardNormLeResidueClass_div`, `tendsto_cardNormLeResidue_div_eq_sum_class`, `cardNormLeResidueClass_eq_dvd`, both L2 proofs, `card_principalize_dvd`, the Route-A density, the transfers.
- **Visibility**: private · **Lines**: 2193–2196 · **Notes**: —.

### `private theorem exists_tendsto_cardNormLeResidueClass_div`
- **Type**: `(c) [NeZero c] (y) (C) : ∃ κ, (fun N ↦ cardNormLeResidueClass c y C N / N) → κ`.
- **What**: The per-class density `κ_{C,y}` exists.
- **How**: `tendsto_div_atTop_of_sub_mul_rpow_le` on `exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`.
- **Hypotheses**: `[NeZero c]`; `y, C`.
- **Uses from project**: [`exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`, `tendsto_div_atTop_of_sub_mul_rpow_le`, `cardNormLeResidueClass`]
- **Used by**: `tendsto_cardNormLeResidueClass_div_transfer`, `cardNormLeResidue_density_transfer`.
- **Visibility**: private · **Lines**: 2201–2206 · **Notes**: —.

### `private theorem tendsto_cardNormLeResidue_div_eq_sum_class`
- **Type**: If `cardNormLeResidue` has density `κ` and each `cardNormLeResidueClass` has density `κf C`, then `κ = ∑_C κf C`.
- **What**: The norm-residue density splits over the class group, `κ_y = ∑_C κ_{C,y}`.
- **How**: `card_norm_le_residue_eq_sum_class` makes the count a finite sum; `tendsto_finsetSum` + `tendsto_nhds_unique`.
- **Hypotheses**: `[NeZero c]`; both density limits.
- **Uses from project**: [`cardNormLeResidue`, `card_norm_le_residue_eq_sum_class`, `cardNormLeResidueClass`]
- **Used by**: `cardNormLeResidue_density_transfer` (twice).
- **Visibility**: private · **Lines**: 2212–2224 · **Notes**: —.

### `private def cardNormLeResidueClassDvd`
- **Type**: `(c) (𝔟) (y) (D) (N) : ℕ := Nat.card {J // 𝔟 ∣ J ∧ ((absNorm J ≤ N ∧ (absNorm J:ZMod c)=y) ∧ mk0 J = D)}`.
- **What**: `𝔟`-divisible per-class norm-residue count.
- **How**: Direct `Nat.card` (real def).
- **Hypotheses**: number field; `c, 𝔟, y, D, N`.
- **Uses from project**: []
- **Used by**: 23 occurrences — `cardNormLeResidueClass_eq_dvd`, `cardNormLeResidueClassDvd_floor_collapse`, both L2 proofs, Route A, the kernel `cardNormLeResidueClassDvd_sub_mul_rpow_le`, the transfers.
- **Visibility**: private · **Lines**: 2229–2233 · **Notes**: —.

### `private theorem cardNormLeResidueClass_eq_dvd`
- **Type**: With `N(𝔟) (mod c)` a unit: `cardNormLeResidueClass c x C N = cardNormLeResidueClassDvd c 𝔟 (x·N(𝔟)) (C·[𝔟]) (N·N(𝔟))`.
- **What**: Route A (norm-multiplying bijection, exact) — `I ↦ 𝔟·I` matches class-`C` residue-`x` ideals with `𝔟`-divisible class-`C·[𝔟]` residue-`x·N(𝔟)` ideals at scaled bound.
- **How**: `Nat.card_congr` of `(Equiv.dvd 𝔟).subtypeEquiv` + `subtypeSubtypeEquivSubtypeInter`; the predicate correspondence uses `map_mul` for norm/class scaling, `hu.mul_left_inj` for the residue (unit), `Nat.mul_le_mul_right_iff` for the bound.
- **Hypotheses**: `[NeZero c]`; `IsUnit (N(𝔟):ZMod c)`.
- **Uses from project**: [`cardNormLeResidueClass`, `cardNormLeResidueClassDvd`]
- **Used by**: `cardNormLeResidueClassDvd_div_density_routeA`, `cardNormLeResidueClassDvd_sub_mul_rpow_le`, `cardNormLeResidueClass_density_transfer`.
- **Visibility**: private · **Lines**: 2240–2275 · **Notes**: &gt;30 lines.

### `private theorem exists_card_idealSet_residue_real_le`
- **Type**: `∃ κ C', ∀ s ≥ 1, |Nat.card {a : idealSet K J // norm a ≤ s ∧ residue b} - κ·s| ≤ C'·s^(1-1/d)`.
- **What**: Decoupled-bound (free real bound `s`) cone-point residue count, **same leading constant `κ = ∑ L_p` form** as `exists_card_idealSet_residue_le`.
- **How**: Identical structure to `exists_card_idealSet_residue_le` but with dilation `tN = s^(1/d)` (so `t^d = s`, `t^(d-1) = s^(1-1/d)`); partition over `(orthant,coset)` cells, sum the per-cell estimates (`exists_card_residue_fibre_sub_mul_rpow_le`).
- **Hypotheses**: `[NeZero m]`; `b`, `J`.
- **Uses from project**: [`exists_latticeEquiv_image_idealLattice`, `exists_card_residue_fibre_sub_mul_rpow_le`, `finite_idealSet_norm_le`] (+ external `normLeOne_frontier_lipschitz_cover_index`)
- **Used by**: `exists_card_dvd_principal_residue_real_le`.
- **Visibility**: private · **Lines**: 2285–2372 · **Notes**: &gt;30 lines; the cell-partition body is a near-verbatim copy of `exists_card_idealSet_residue_le` (redundant layer).

### `private theorem exists_card_dvd_principal_residue_real_le`
- **Type**: `∃ κ C', ∀ s ≥ 1, |Nat.card {I // J' ∣ I ∧ (IsPrincipal I ∧ (absNorm I:ℝ) ≤ s ∧ residue b)} - κ·s| ≤ C'·s^(1-1/d)`.
- **What**: Decoupled-bound `J'`-divisible principal residue count.
- **How**: Torsion bridge `card_isPrincipal_dvd_norm_le_residue` at bound `s`, dividing `exists_card_idealSet_residue_real_le` by `torsionOrder K`.
- **Hypotheses**: `[NeZero m]`; `b`, `J'`.
- **Uses from project**: [`exists_card_idealSet_residue_real_le`, `card_isPrincipal_dvd_norm_le_residue`]
- **Used by**: **unused in file** — the only other occurrence is a docstring mention (line 3747 in `cardNormLeResidueClassDvd_div_density`). Dead code (the live L2 path uses `exists_card_idealSet_residue_real_le_dvd` directly).
- **Visibility**: private · **Lines**: 2382–2422 · **Notes**: &gt;30 lines; DEAD (no call site).

### `private theorem Nat.le_iff_le_mul_div_of_dvd`
- **Type**: For `0 &lt; m`, `m ∣ a`: `a ≤ N ↔ a ≤ m·(N/m)`.
- **What**: A bound on a multiple of `m` collapses to the largest multiple of `m` not exceeding `N`.
- **How**: `obtain ⟨k, rfl⟩` from divisibility; `Nat.le_div_iff_mul_le`, `Nat.mul_div_le`.
- **Hypotheses**: `0 &lt; m`, `m ∣ a`.
- **Uses from project**: []
- **Used by**: `cardNormLeResidueClassDvd_floor_collapse`.
- **Visibility**: private (in `Nat` namespace) · **Lines**: 2426–2430 · **Notes**: —.

### `private theorem cardNormLeResidueClassDvd_floor_collapse`
- **Type**: `cardNormLeResidueClassDvd c 𝔟 y D N = cardNormLeResidueClassDvd c 𝔟 y D (N(𝔟)·(N/N(𝔟)))`.
- **What**: Norm-window collapse — the `𝔟`-divisible count at bound `N` equals that at the largest multiple of `N(𝔟)` below `N`.
- **How**: `Nat.card_congr (Equiv.subtypeEquivRight …)`; only the norm bound changes, and every `𝔟`-divisible norm is a multiple of `N(𝔟)` (`map_dvd absNorm`), so `Nat.le_iff_le_mul_div_of_dvd` applies.
- **Hypotheses**: `[NeZero c]`; `𝔟, y, D, N`.
- **Uses from project**: [`cardNormLeResidueClassDvd`, `Nat.le_iff_le_mul_div_of_dvd`]
- **Used by**: `cardNormLeResidueClassDvd_div_density_routeA`, `cardNormLeResidueClassDvd_sub_mul_rpow_le`.
- **Visibility**: private · **Lines**: 2437–2456 · **Notes**: —.

### `private theorem absNorm_coprime_of_isCoprime_span`
- **Type**: If `IsCoprime (J : Ideal) (span {(n:𝓞 K)})` then `(absNorm J).Coprime n`.
- **What**: Ideal-coprimality to `(n)` implies norm-coprimality to `n`.
- **How**: By contradiction: a prime `p ∣ gcd(N(J),n)` yields a maximal `P ∣ J` over `(p)` (`exists_isMaximal_dvd_of_dvd_absNorm'`); then `(n:𝓞 K) ∈ P`, so `J ⊔ span{n} ≤ P ≠ ⊤`, contradicting `isCoprime_iff_sup_eq`.
- **Hypotheses**: `IsCoprime J (span {n})`.
- **Uses from project**: []
- **Used by**: `exists_mk0_eq_absNorm_coprime`.
- **Visibility**: private · **Lines**: 2463–2488 · **Notes**: &gt;30 lines.

### `private theorem span_image_basisFun_eq`
- **Type**: For `T : (ι→ℝ)≃ₗ[ℝ](ι→ℝ)`: `span ℤ (T '' ↑(span ℤ (range (Pi.basisFun ℝ ι)))) = span ℤ (range ((Pi.basisFun ℝ ι).map T))`.
- **What**: The `ℤ`-span of `T` applied to the standard lattice is the span of the mapped basis (so the `IsZLattice`/covolume API applies).
- **How**: `map_span_int_linearEquiv`, `span_coe_eq_restrictScalars`, `Submodule.restrictScalars_self`, and `Module.Basis.map_apply`/`Set.range_comp`.
- **Hypotheses**: `[Finite ι]`; `T`.
- **Uses from project**: [`map_span_int_linearEquiv`]
- **Used by**: `covolume_image_basisFun_eq_abs_det`(via the `← span_image_basisFun_eq` rewrite inside `chart_lattice_eq_map`).
- **Visibility**: private · **Lines**: 2503–2512 · **Notes**: —.

### `private theorem covolume_image_basisFun_eq_abs_det`
- **Type**: `ZLattice.covolume (span ℤ (range ((Pi.basisFun ℝ ι).map T))) = |det T|`.
- **What**: The covolume of the image lattice `T '' ℤ^ι` is `|det T|`.
- **How**: Takes the `ℤ`-basis `(Pi.basisFun).map T` (`Module.Basis.span` of a `LinearIndependent` set via `restrict_scalars`); `ZLattice.covolume_eq_det`; identifies the change-of-basis matrix with the transpose of `toMatrix T` (`LinearMap.det_toMatrix`, `Matrix.det_transpose`).
- **Hypotheses**: `T` a linear equiv.
- **Uses from project**: []
- **Used by**: `abs_det_latticeEquiv_mul` (twice).
- **Visibility**: private · **Lines**: 2519–2537 · **Notes**: —.

### `private theorem relIndex_mul_ideal_eq_absNorm`
- **Type**: `((𝔟·J : Ideal).toAddSubgroup).relIndex ((J : Ideal).toAddSubgroup) = absNorm 𝔟`.
- **What**: The relative additive index of `𝔟J` in `J` is `N(𝔟)`.
- **How**: `AddSubgroup.relIndex_mul_index` with `index = absNorm` (`cardQuot`, `Submodule.cardQuot_apply`) and `N(𝔟J) = N(𝔟)·N(J)`; cancel via `Nat.eq_of_mul_eq_mul_right` (`N(J) &gt; 0`).
- **Hypotheses**: `J, 𝔟`.
- **Uses from project**: []
- **Used by**: `relIndex_idealLattice_eq_absNorm`.
- **Visibility**: private · **Lines**: 2543–2565 · **Notes**: —.

### `private theorem idealLattice_mul_le`
- **Type**: `idealLattice K (mk0 K (𝔟·J)) ≤ idealLattice K (mk0 K J)`.
- **What**: Cone-point inclusion for a divisor multiple (`Λ_{𝔟J} ⊆ Λ_J`).
- **How**: Unpacks `mem_idealLattice`; uses `(𝔟J : FractionalIdeal) ≤ (J : FractionalIdeal)` (`coeIdeal_le_coeIdeal`, `Ideal.mul_le_left`).
- **Hypotheses**: `J, 𝔟`.
- **Uses from project**: []
- **Used by**: `chart_sublattice_le`, and `idealSet (𝔟J) ⊆ idealSet J` inclusions inside `exists_card_fibre_dvd_eq_card_cell`, `exists_card_fibre_dvd_residue_sub_mul_rpow_le` (7 occurrences).
- **Visibility**: private · **Lines**: 2570–2583 · **Notes**: —.

### `private theorem idealLattice_toAddSubgroup_eq`
- **Type**: `(idealLattice K (mk0 K J)).toAddSubgroup = (J.toAddSubgroup).map (mixedEmbedding ∘ algebraMap)`.
- **What**: The ideal lattice (as an additive subgroup) is the image of the ideal under `mixedEmbedding ∘ algebraMap`.
- **How**: `ext`; both directions unpack `mem_idealLattice` / `AddSubgroup.mem_map` and the `FractionalIdeal.coe_mk0` membership.
- **Hypotheses**: `J`.
- **Uses from project**: []
- **Used by**: `relIndex_idealLattice_eq_absNorm` (used twice in one rewrite).
- **Visibility**: private · **Lines**: 2589–2607 · **Notes**: —.

### `private theorem relIndex_idealLattice_eq_absNorm`
- **Type**: `(Λ_{𝔟J}.toAddSubgroup).relIndex (Λ_J.toAddSubgroup) = absNorm 𝔟`.
- **What**: The relative index of the sublattice `Λ_{𝔟J} ⊆ Λ_J` is `N(𝔟)`.
- **How**: Transports the ideal index `relIndex_mul_ideal_eq_absNorm` along the injective additive map `mixedEmbedding ∘ algebraMap` (`AddSubgroup.relIndex_map_map_of_injective`, `idealLattice_toAddSubgroup_eq`).
- **Hypotheses**: `J, 𝔟`.
- **Uses from project**: [`idealLattice_toAddSubgroup_eq`, `relIndex_mul_ideal_eq_absNorm`]
- **Used by**: `relIndex_chart_eq_absNorm`.
- **Visibility**: private · **Lines**: 2613–2625 · **Notes**: —.

### `private theorem chart_lattice_eq_map`
- **Type**: Given chart identity `hT`: `span ℤ (range ((Pi.basisFun).map T)) = (idealLattice K (mk0 K J)).map (Φ.restrictScalars ℤ)`.
- **What**: The chart lattice `T '' ℤ^ι` equals `Λ_J.map Φ` as a submodule.
- **How**: `← span_image_basisFun_eq`, then `hT`, `span_coe_eq_restrictScalars`, `Submodule.restrictScalars_self`, `Submodule.map_coe`.
- **Hypotheses**: chart identity for `J`.
- **Uses from project**: [`span_image_basisFun_eq`]
- **Used by**: `chart_sublattice_le`, `relIndex_chart_eq_absNorm` (each uses it for `J` and `𝔟J`).
- **Visibility**: private · **Lines**: 2630–2647 · **Notes**: —.

### `private theorem chart_sublattice_le`
- **Type**: Given chart identities `hT, hT'`: `span ℤ (range ((Pi.basisFun).map T')) ≤ span ℤ (range ((Pi.basisFun).map T))`.
- **What**: The chart sublattice `T' '' ℤ^ι ⊆ T '' ℤ^ι` (image of `Λ_{𝔟J} ⊆ Λ_J`).
- **How**: `chart_lattice_eq_map` for both, then `Submodule.map_mono (idealLattice_mul_le …)`.
- **Hypotheses**: chart identities for `J` and `𝔟J`.
- **Uses from project**: [`chart_lattice_eq_map`, `idealLattice_mul_le`]
- **Used by**: `abs_det_latticeEquiv_mul`, `exists_card_fibre_dvd_eq_card_cell`.
- **Visibility**: private · **Lines**: 2651–2662 · **Notes**: —.

### `private theorem relIndex_chart_eq_absNorm`
- **Type**: Given chart identities: `(span ℤ (range ((Pi.basisFun).map T'))).toAddSubgroup.relIndex (… T …) = absNorm 𝔟`.
- **What**: The relative index of the chart sublattice is `N(𝔟)` (chart-side transport of `relIndex_idealLattice_eq_absNorm`).
- **How**: `chart_lattice_eq_map` for both, `Submodule.map_toAddSubgroup`, `AddSubgroup.relIndex_map_map_of_injective` (Φ injective), then `relIndex_idealLattice_eq_absNorm`.
- **Hypotheses**: chart identities for `J` and `𝔟J`.
- **Uses from project**: [`chart_lattice_eq_map`, `relIndex_idealLattice_eq_absNorm`]
- **Used by**: `abs_det_latticeEquiv_mul`, `exists_card_fibre_dvd_eq_card_cell`.
- **Visibility**: private · **Lines**: 2667–2686 · **Notes**: —.

### `private theorem abs_det_latticeEquiv_mul`
- **Type**: Given chart identities: `|det T'| = N(𝔟)·|det T|`.
- **What**: Covolume/`|det|` scaling of the sublattice chart.
- **How**: `ZLattice.covolume_div_covolume_eq_relIndex` for `L' ⊆ L` (`chart_sublattice_le`), with `relIndex = N(𝔟)` (`relIndex_chart_eq_absNorm`) and `covol = |det|` (`covolume_image_basisFun_eq_abs_det`); `field_simp` + `linarith` (`|det T| &gt; 0`).
- **Hypotheses**: chart identities for `J` and `𝔟J`.
- **Uses from project**: [`chart_sublattice_le`, `relIndex_chart_eq_absNorm`, `covolume_image_basisFun_eq_abs_det`]
- **Used by**: `abs_det_smulTrans_mul`.
- **Visibility**: private · **Lines**: 2695–2719 · **Notes**: —.

### `private theorem crt_single_coset`
- **Type**: For `L' ≤ L` with finite quotient and `gcd(#(L/L'), m) = 1`, `ξ ∈ L`: `∃ ξ' ∈ L', {a | a ∈ L' ∧ a ∈ ξ +ᵥ m•L} = ξ' +ᵥ m•L'`.
- **What**: CRT single-coset fact — the points of an `m`-coset of `L` lying in `L'` form a single `m`-coset of `L'`.
- **How**: Multiplication by `m` is bijective on the finite quotient `L/L'` (`Nat.Coprime.nsmul_right_bijective`): surjectivity gives `ξ ∈ L' + m·L` (the rep `ξ'`); injectivity gives `(a ∈ L ∧ m·a ∈ L') → a ∈ L'` (`QuotientAddGroup` arithmetic); two-directional `ext`.
- **Hypotheses**: `[Finite ι]`; `L' ≤ L`; finite quotient; coprimality; `ξ ∈ L`.
- **Uses from project**: []
- **Used by**: `exists_card_fibre_dvd_eq_card_cell`.
- **Visibility**: private · **Lines**: 2728–2781 · **Notes**: &gt;30 lines.

### `private theorem exists_mk0_eq_absNorm_coprime`
- **Type**: For class `D`, `n &gt; 0`: `∃ J, mk0 J = D ∧ (absNorm J).Coprime n`.
- **What**: (L1) Every ideal class has an integral representative whose norm is coprime to a prescribed `n`.
- **How**: `n = 1` trivial; else take `J₀` of `D⁻¹`, set `𝔫 = span {n}` (`≠ ⊥, ⊤` via `absNorm_span_natCast ≥ 2`); apply `IsDedekindDomain.exists_sup_span_eq` to `𝔫·J₀ ≤ J₀` to get `a` with `𝔫·J₀ ⊔ span{a} = J₀`; `span{a} = J₀·J₁`; show `𝔫 ⊔ J₁ = ⊤` (cancel `J₀`), `[J₁] = D` (`span{a}` principal ⟹ `[J₀]·[J₁]=1`), norm-coprime via `absNorm_coprime_of_isCoprime_span`.
- **Hypotheses**: `0 &lt; n`.
- **Uses from project**: [`absNorm_coprime_of_isCoprime_span`]
- **Used by**: `cardNormLeResidueClassDvd_div_density` (the geometric L2 proof).
- **Visibility**: private · **Lines**: 2790–2865 · **Notes**: &gt;30 lines.

### `private theorem smul_chart_lattice_eq`
- **Type**: `((smulOfNeZero m).trans T) '' Λ = (m:ℝ) • (span ℤ (range ((Pi.basisFun ℝ ι).map T)) : Set)`.
- **What**: The `m`-sublattice of the chart lattice, in workhorse form: `(m·)∘T '' ℤ^ι = m·(T''ℤ^ι)`.
- **How**: Rewrites `span ℤ (range (basisFun.map T)) = T '' ℤ^ι` (`map_span_int_linearEquiv`), then `ext` over scalar/image membership using `map_smul`.
- **Hypotheses**: `[Finite ι]`; `(m:ℝ)≠0`.
- **Uses from project**: [`map_span_int_linearEquiv`]
- **Used by**: `exists_card_fibre_dvd_eq_card_cell`, `exists_card_fibre_dvd_residue_sub_mul_rpow_le`.
- **Visibility**: private · **Lines**: 2870–2886 · **Notes**: —.

### `private theorem exists_card_fibre_dvd_eq_card_cell`
- **Type**: For `gcd(N(𝔟),m)=1`, `t ≥ 1`, chart identities: `∃ ξ', Nat.card {a : idealSet K (𝔟·J) // norm a ≤ t^d ∧ orthant_s ∧ J-coset(k)} = Nat.card ↑((ξ' +ᵥ m•(T''ℤ^ι)) ∩ t•(Φ''normLeOne ∩ orthant_s))`.
- **What**: Sublattice cell count — partition the `𝔟J`-cone points by the `J`-lattice chart `T`; the qualifying ones biject with a single `m·Λ_{𝔟J}`-coset.
- **How**: `crt_single_coset` for `L' = Λ_{𝔟J} ⊆ L = Λ_J` (finiteness + coprimality from `relIndex_chart_eq_absNorm`); the counting map `f = Φ` is injective and its range is the stated intersection, established via `idealLattice_mul_le` (inclusion `idealSet 𝔟J ⊆ idealSet J`), cone homogeneity, the same `hreg` region equivalence as `card_fibre_eq_card_cell`, `smul_chart_lattice_eq`, and `mem_coset_iff_cos_eq`.
- **Hypotheses**: `[NeZero m]`, `(m:ℝ)≠0`; `gcd(N(𝔟),m)=1`; chart identities; `1 ≤ t`.
- **Uses from project**: [`relIndex_chart_eq_absNorm`, `chart_sublattice_le`, `crt_single_coset`, `mem_span_int_basisFun_iff`, `idealLattice_mul_le`, `cone_normLe_eq_smul_normLeOne`, `smul_chart_lattice_eq`, `mem_coset_iff_cos_eq`]
- **Used by**: `exists_card_fibre_dvd_residue_sub_mul_rpow_le`.
- **Visibility**: private · **Lines**: 2895–3087 · **Notes**: &gt;30 lines; longest single proof in file (~190 lines); `hreg` block duplicated from `card_fibre_eq_card_cell`.

### `private theorem abs_det_smulTrans_mul`
- **Type**: Given chart identities: `|det ((smulOfNeZero m).trans T')| = N(𝔟)·|det ((smulOfNeZero m).trans T)|`.
- **What**: The chart-`det` ratio with the `m`-dilation included (`|det (m·)|` cancels).
- **How**: `abs_det_latticeEquiv_mul`, write `E.trans S = S.comp E` (`htr`), `LinearMap.det_comp`, `abs_mul`, `ring`.
- **Hypotheses**: `m ≠ 0`; chart identities.
- **Uses from project**: [`abs_det_latticeEquiv_mul`]
- **Used by**: `exists_card_fibre_dvd_residue_sub_mul_rpow_le`.
- **Visibility**: private · **Lines**: 3111–3133 · **Notes**: —.

### `private theorem exists_card_cell_sub_mul_rpow_le_explicit`
- **Type**: Same as `exists_card_cell_sub_mul_rpow_le` but the leading constant is the explicit `vol.real(D₀ ∩ orthant)/|det ((m·)∘T)|`; only `C` is existential.
- **What**: STAGE A — per-cell effective count with the explicit leading constant (the existential re-binding removed).
- **How**: Identical setup (`T'`, `Ds`, orthant closedness) and direct `exists_card_coset_inter_smul_sub_volume_mul_rpow_le T'` + `exists_frontier_cover_inter_orthant`.
- **Hypotheses**: `(m:ℝ)≠0`; `D₀` bounded, measurable, cube-covered.
- **Uses from project**: [`exists_card_coset_inter_smul_sub_volume_mul_rpow_le`, `exists_frontier_cover_inter_orthant`]
- **Used by**: `exists_card_residue_fibre_sub_mul_rpow_le_explicit`, `exists_card_fibre_dvd_residue_sub_mul_rpow_le`.
- **Visibility**: private · **Lines**: 3138–3176 · **Notes**: &gt;30 lines; explicit-`κ` twin of `exists_card_cell_sub_mul_rpow_le`.

### `private theorem residue_fibre_const_aux`
- **Type**: For two cone points `a, a' ∈ idealSet K J` sharing orthant `s` and `m`-coset `k`: `((intNorm (idealSetEquiv K J a):ZMod m)=b) ↔ ((intNorm (idealSetEquiv K J a'):ZMod m)=b)`.
- **What**: Residue is constant on an (orthant, coset) cell (extracted constancy step).
- **How**: `residue_iff_signed_on_orthant` reduces each side to a signed residue; `norm_zmod_eq_of_emb_sub_mem` (via `sub_mem_nsmul_of_coord_eq`) makes the two signed norms congruent.
- **Hypotheses**: shared orthant `s` and coset `k`.
- **Uses from project**: [`residue_iff_signed_on_orthant`, `norm_zmod_eq_of_emb_sub_mem`, `sub_mem_nsmul_of_coord_eq`]
- **Used by**: `exists_card_residue_fibre_sub_mul_rpow_le_explicit`, `exists_card_fibre_dvd_residue_sub_mul_rpow_le`.
- **Visibility**: private · **Lines**: 3183–3237 · **Notes**: &gt;30 lines; body duplicates the `hconst`/`hsign` block inside `exists_card_residue_fibre_sub_mul_rpow_le`.

### `private theorem exists_card_residue_fibre_sub_mul_rpow_le_explicit`
- **Type**: Same per-(orthant,coset) effective residue count as `exists_card_residue_fibre_sub_mul_rpow_le`, but with the leading constant explicit: `if cell carries residue b then vol(Φ''normLeOne ∩ orthant)/|det ((m·)∘T)| else 0`.
- **What**: STAGE A (fibre level) — per-cell effective residue count with explicit constant.
- **How**: `residue_fibre_const_aux` for constancy; case split (`if_pos`/`if_neg`) on residue-carrying cell; if yes drop the filter and use `card_fibre_eq_card_cell` + `exists_card_cell_sub_mul_rpow_le_explicit`; if no, empty.
- **Hypotheses**: `[NeZero m]`, `(m:ℝ)≠0`; chart identity; frontier cover.
- **Uses from project**: [`residue_fibre_const_aux`, `exists_card_cell_sub_mul_rpow_le_explicit`, `card_fibre_eq_card_cell`]
- **Used by**: `exists_card_idealSet_residue_real_le_dvd`.
- **Visibility**: private · **Lines**: 3244–3334 · **Notes**: &gt;30 lines; explicit-`κ` twin of `exists_card_residue_fibre_sub_mul_rpow_le`.

### `private theorem exists_card_fibre_dvd_residue_sub_mul_rpow_le`
- **Type**: Per-(orthant,coset) effective `𝔟J`-residue count, with leading constant `(L_J(p) if-expression)/N(𝔟)`.
- **What**: STAGE B (fibre level) — the same cell `(s,k)` of `idealSet K (𝔟J)`, filtered by residue `b`, has leading constant `L_J/N(𝔟)`.
- **How**: Case split on whether the `J`-cell carries residue `b`: if yes, the `𝔟J`-residue filter is redundant (constancy via `residue_fibre_const_aux` through `idealLattice_mul_le`), so the count is the gateway full cell count (`exists_card_fibre_dvd_eq_card_cell`); the det ratio `abs_det_smulTrans_mul` gives `vol/|det((m·)∘T')| = (vol/|det((m·)∘T)|)/N(𝔟)`; if no, the `𝔟J`-count is empty. The `𝔟J`-cell workhorse estimate is from `exists_card_cell_sub_mul_rpow_le_explicit T'`.
- **Hypotheses**: `[NeZero m]`, `(m:ℝ)≠0`; `gcd(N(𝔟),m)=1`; chart identities; frontier cover.
- **Uses from project**: [`exists_card_cell_sub_mul_rpow_le_explicit`, `abs_det_smulTrans_mul`, `residue_fibre_const_aux`, `idealLattice_mul_le`, `exists_card_fibre_dvd_eq_card_cell`, `smul_chart_lattice_eq`]
- **Used by**: `exists_card_idealSet_residue_real_le_dvd`.
- **Visibility**: private · **Lines**: 3346–3453 · **Notes**: &gt;30 lines.

### `private theorem card_idealSet_residue_eq_sum_cell`
- **Type**: `Nat.card {a : idealSet K I₀ // norm a ≤ S ∧ residue b} = ∑_{(s,k)} Nat.card {a // (norm a ≤ S ∧ residue b) ∧ orthant(s) ∧ Tc-coset(k)}`.
- **What**: Cone-point residue count partitions over `(orthant, coset)` cells (extracted, general ideal `I₀` and chart `Tc`).
- **How**: `Equiv.sigmaFiberEquiv` of the classifier `cls` (orthant filter, rounded coords) + `sigmaCongrRight`; finiteness from `finite_idealSet_norm_le`.
- **Hypotheses**: `[NeZero m]`; `b, I₀, Tc, S`.
- **Uses from project**: [`finite_idealSet_norm_le`]
- **Used by**: `card_residue_sum_bound_aux`.
- **Visibility**: private · **Lines**: 3459–3503 · **Notes**: &gt;30 lines; extracts the partition logic duplicated inline in `exists_card_idealSet_residue_le`/`_real_le`.

### `private theorem card_residue_sum_bound_aux`
- **Type**: Given per-cell estimates at `tN = S^(1/d)`, `|Nat.card {a : idealSet K I₀ // norm a ≤ S ∧ residue b} - (∑ Lc)·S| ≤ (∑ Cc)·S^(1-1/d)`.
- **What**: Summed cell estimate → global cone-count estimate (extracted summing step).
- **How**: `card_idealSet_residue_eq_sum_cell` to expand, `Real.rpow` algebra `t^d = S`, `t^(d-1) = S^(1-1/d)`, `Finset.abs_sum_le_sum_abs`, `Finset.sum_le_sum`.
- **Hypotheses**: `[NeZero m]`; `1 ≤ S`; per-cell estimates `hcell`.
- **Uses from project**: [`card_idealSet_residue_eq_sum_cell`]
- **Used by**: `exists_card_idealSet_residue_real_le_dvd` (used twice).
- **Visibility**: private · **Lines**: 3510–3553 · **Notes**: &gt;30 lines.

### `private theorem exists_card_idealSet_residue_real_le_dvd`
- **Type**: For `gcd(N(𝔟),m)=1`: `∃ κ C'`, both the `J`-cone count `≈ κ·S` and the `𝔟J`-cone count `≈ (κ/N(𝔟))·S`, each with `O(S^(1-1/d))` error.
- **What**: STAGE B (summed) — the `J`- and `𝔟J`-cone residue counts share a leading constant up to `N(𝔟)`.
- **How**: Picks charts `T, T'` (`exists_latticeEquiv_image_idealLattice` for `J`, `𝔟J`) and cover; `choose`s the explicit per-cell `J`-constant `L(p)` (the `if`-expression) and the two per-cell bounds (`exists_card_residue_fibre_sub_mul_rpow_le_explicit`, `exists_card_fibre_dvd_residue_sub_mul_rpow_le`); both summed via `card_residue_sum_bound_aux` (`J`-side with `L`, `𝔟J`-side with `L/N(𝔟)` and `Finset.sum_div`).
- **Hypotheses**: `[NeZero m]`, `(m:ℝ)≠0`; `gcd(N(𝔟),m)=1`.
- **Uses from project**: [`exists_latticeEquiv_image_idealLattice`, `exists_card_residue_fibre_sub_mul_rpow_le_explicit`, `exists_card_fibre_dvd_residue_sub_mul_rpow_le`, `card_residue_sum_bound_aux`] (+ external `normLeOne_frontier_lipschitz_cover_index`)
- **Used by**: `cardNormLeResidueClassDvd_div_density` (the geometric L2 proof).
- **Visibility**: private · **Lines**: 3564–3623 · **Notes**: &gt;30 lines.

### `private theorem card_principalize_dvd`
- **Type**: With `mk0 J = D⁻¹`, `0 &lt; absNorm J`: `cardNormLeResidueClassDvd c 𝔟 y D N = Nat.card {I // 𝔟J ∣ I ∧ (IsPrincipal I ∧ absNorm I ≤ N·NJ ∧ res (y.val·NJ) mod c·NJ)}`.
- **What**: STAGE C — principalization of the `𝔟`-divisible count (to `𝔟J`-divisible principal ideals).
- **How**: `Nat.card_congr` of `(Equiv.dvd J).subtypeEquiv principalize_iff` + `subtypeSubtypeEquivSubtype`, with `𝔟 ∣ I ↔ 𝔟J ∣ J·I` by pure cancellation (`mul_dvd_mul_iff_left`, `nonZeroDivisors.coe_ne_zero`); `tauto`.
- **Hypotheses**: `[NeZero c]`; `mk0 J = D⁻¹`; `0 &lt; absNorm J`.
- **Uses from project**: [`cardNormLeResidueClassDvd`, `principalize_iff`]
- **Used by**: `cardNormLeResidueClassDvd_div_density` (the geometric L2 proof).
- **Visibility**: private · **Lines**: 3631–3672 · **Notes**: &gt;30 lines.

### `private theorem tendsto_count_div_of_cone_bridge`
- **Type**: If `cnt N · torsionOrder K = coneR(N·NJ)` and `|coneR S - κ₀·S| ≤ C'·S^(1-1/d)`, then `(fun N ↦ cnt N / N) → κ₀·NJ/torsionOrder K`.
- **What**: STAGE D — from a cone estimate + torsion bridge to the count density.
- **How**: Evaluates the cone estimate at `S = N·NJ`, divides by `torsionOrder K`; the residual error factor `NJ^(1-1/d) ≤ NJ` (`Real.rpow_le_rpow_of_exponent_le`); finishes via `tendsto_div_atTop_of_sub_mul_rpow_le` with `C' = |C'|·NJ/torsionOrder`.
- **Hypotheses**: `0 &lt; NJ`; the bridge `hbridge`; the cone estimate `hcone`.
- **Uses from project**: [`tendsto_div_atTop_of_sub_mul_rpow_le`]
- **Used by**: `cardNormLeResidueClassDvd_div_density` (used twice — `J`-side and `𝔟J`-side).
- **Visibility**: private · **Lines**: 3680–3724 · **Notes**: &gt;30 lines.

### `private theorem cardNormLeResidueClassDvd_div_density` — L2 (geometric proof)
- **Type**: With `IsUnit (N(𝔟):ZMod c)` and full class-`D` residue-`y` density `κfull`: `(fun N ↦ cardNormLeResidueClassDvd c 𝔟 y D N / N) → κfull/N(𝔟)`.
- **What**: (L2) the `𝔟`-divisible density is the full density divided by `N(𝔟)` — proven the **geometric (Route B / CRT covolume) way**.
- **How**: Picks coprime representative `J` of `D⁻¹` (`exists_mk0_eq_absNorm_coprime`, `gcd(N(𝔟),c·N(J))=1`); the shared cone estimate (`exists_card_idealSet_residue_real_le_dvd`); two principalization + torsion bridges (`card_principalize`, `card_principalize_dvd`, `card_isPrincipal_dvd_norm_le_residue`); `tendsto_count_div_of_cone_bridge` for both sides; `tendsto_nhds_unique` pins `κfull = κ·N(J)/torsionOrder K`, yielding `𝔟J`-density `= κfull/N(𝔟)`.
- **Hypotheses**: `[NeZero c]`; `IsUnit (N(𝔟):ZMod c)`; `κfull` density.
- **Uses from project**: [`exists_mk0_eq_absNorm_coprime`, `exists_card_idealSet_residue_real_le_dvd`, `card_principalize`, `card_principalize_dvd`, `card_isPrincipal_dvd_norm_le_residue`, `tendsto_count_div_of_cone_bridge`, `cardNormLeResidueClass`, `cardNormLeResidueClassDvd`]
- **Used by**: `tendsto_cardNormLeResidueClass_div_transfer` (as `hL2`).
- **Visibility**: private · **Lines**: 3758–3836 · **Notes**: &gt;30 lines; the proof discharging the project's deepest leaf (formerly `sorry`); docstring still labels it "the single remaining irreducible gap" (now proven).

### `private theorem cardNormLeResidueClassDvd_div_density_routeA` — L3
- **Type**: With `IsUnit (N(𝔟):ZMod c)` and `κCC` = full class-`CC = D·[𝔟]⁻¹` residue-`xC = y·u⁻¹` density: `(fun N ↦ cardNormLeResidueClassDvd c 𝔟 y D N / N) → κCC/N(𝔟)`.
- **What**: (L3) Route A as a density (elementary, exact) — the `𝔟`-divisible density via the norm-multiplying bijection (no geometry).
- **How**: Count identity `cardNormLeResidueClassDvd c 𝔟 y D N = cardNormLeResidueClass c xC CC (N/N(𝔟))` (`cardNormLeResidueClassDvd_floor_collapse` + `cardNormLeResidueClass_eq_dvd`); splits off the floor `⌊N/N(𝔟)⌋/N → 1/N(𝔟)` (via `(N%N(𝔟))/N → 0`, `squeeze_zero'`); composes `hκCC ∘ (·/N(𝔟))` with the ratio limit.
- **Hypotheses**: `[NeZero c]`; `IsUnit (N(𝔟):ZMod c)`; `κCC` density.
- **Uses from project**: [`cardNormLeResidueClassDvd_floor_collapse`, `cardNormLeResidueClass_eq_dvd`, `cardNormLeResidueClass`, `cardNormLeResidueClassDvd`]
- **Used by**: `tendsto_cardNormLeResidueClass_div_transfer` (as `hL3`).
- **Visibility**: private · **Lines**: 3846–3916 · **Notes**: &gt;30 lines.

### `private theorem tendsto_cardNormLeResidueClass_div_transfer`
- **Type**: With `IsUnit (N(𝔟):ZMod c)` and class-`C` residue-`x` density `κ`: `(fun M ↦ cardNormLeResidueClass c (x·N(𝔟)) (C·[𝔟]) M / M) → κ`.
- **What**: The per-class norm-residue **density** is invariant under `(C,x) ↦ (C·[𝔟], x·N(𝔟))` — the irreducible geometry-of-numbers transfer (now proven, by combining L2-geometric and L3).
- **How**: The RHS density `κ'` exists (`exists_tendsto_cardNormLeResidueClass_div`); proves `κ' = κ`: at the back-shifted data `xC = y·u⁻¹ = x`, `CC = D·[𝔟]⁻¹ = C`, the L2-geometric `cardNormLeResidueClassDvd_div_density` gives `𝔟`-divisible density `κ'/N(𝔟)`, and Route-A `cardNormLeResidueClassDvd_div_density_routeA` gives `κ/N(𝔟)`; `tendsto_nhds_unique` + `div_left_inj'`.
- **Hypotheses**: `[NeZero c]`; `IsUnit (N(𝔟):ZMod c)`; `κ` density.
- **Uses from project**: [`exists_tendsto_cardNormLeResidueClass_div`, `cardNormLeResidueClassDvd_div_density`, `cardNormLeResidueClassDvd_div_density_routeA`, `cardNormLeResidueClass`, `cardNormLeResidueClassDvd`]
- **Used by**: `cardNormLeResidueClassDvd_sub_mul_rpow_le` (as the transfer fact).
- **Visibility**: private · **Lines**: 3941–3977 · **Notes**: &gt;30 lines; docstring labels it "the single irreducible geometry-of-numbers fact / not yet formalised" — outdated: it IS now proven from the two routes.

### `private theorem cardNormLeResidueClassDvd_sub_mul_rpow_le`
- **Type**: With `IsUnit (N(𝔟):ZMod c)` and full density `κfull`: `∃ C', ∀ N ≥ 1, |cardNormLeResidueClassDvd c 𝔟 y D N - (κfull/N(𝔟))·N| ≤ C'·N^(1-1/d)`.
- **What**: The irreducible geometric kernel as an **effective** estimate — the `𝔟`-divisible count with leading constant `κfull/N(𝔟)`.
- **How**: Route-A count identity `= cardNormLeResidueClass c xC CC (N/N(𝔟))` (`cardNormLeResidueClassDvd_floor_collapse` + `cardNormLeResidueClass_eq_dvd`); the `(CC,xC)` effective estimate is `exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`, with `κC = κfull` pinned by `tendsto_cardNormLeResidueClass_div_transfer`; assembles by splitting `count - (κC/N(𝔟))·N = (count_CC(M) - κC·M) + (κC·M - (κC/N(𝔟))·N)`, bounding the floor error `|κC|·{N/N(𝔟)} ≤ |κC|·N^(1-1/d)`; `C' = |C₀| + |κC|`.
- **Hypotheses**: `[NeZero c]`; `IsUnit (N(𝔟):ZMod c)`; `κfull` density.
- **Uses from project**: [`cardNormLeResidueClassDvd_floor_collapse`, `cardNormLeResidueClass_eq_dvd`, `exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`, `tendsto_cardNormLeResidueClass_div_transfer`, `cardNormLeResidueClass`, `cardNormLeResidueClassDvd`]
- **Used by**: `cardNormLeResidueClass_div_density`.
- **Visibility**: private · **Lines**: 4001–4107 · **Notes**: &gt;30 lines.

### `private theorem cardNormLeResidueClass_div_density` — L2 (kernel-routed, live path)
- **Type**: With `IsUnit (N(𝔟):ZMod c)` and full class-`D` residue-`y` density `κfull`: `(fun N ↦ cardNormLeResidueClassDvd c 𝔟 y D N / N) → κfull/N(𝔟)`.
- **What**: Route B (Lang covolume/CRT) as a density — the `𝔟`-divisible density is `1/N(𝔟)` of the full one.
- **How**: One line — the limit form of the effective kernel `cardNormLeResidueClassDvd_sub_mul_rpow_le` via `tendsto_div_atTop_of_sub_mul_rpow_le`.
- **Hypotheses**: `[NeZero c]`; `IsUnit (N(𝔟):ZMod c)`; `κfull` density.
- **Uses from project**: [`cardNormLeResidueClassDvd_sub_mul_rpow_le`, `tendsto_div_atTop_of_sub_mul_rpow_le`, `cardNormLeResidueClassDvd`]
- **Used by**: `cardNormLeResidueClass_density_transfer`.
- **Visibility**: private · **Lines**: 4133–4145 · **Notes**: — (note: this is a SECOND statement of the same conclusion as `cardNormLeResidueClassDvd_div_density`; this kernel-routed one is on the live transfer path used by `cardNormLeResidueClass_density_transfer`, while the geometric one feeds only `tendsto_cardNormLeResidueClass_div_transfer`, which in turn feeds the kernel — see redundancy note in summary).

### `private theorem cardNormLeResidueClass_density_transfer`
- **Type**: With `IsUnit (N(𝔟):ZMod c)`, densities `κ` (class `C`, residue `x`) and `κ'` (class `C·[𝔟]`, residue `x·N(𝔟)`): `κ = κ'`.
- **What**: Per-class realizer transfer (the geometric heart) as a density equality.
- **How**: Two routes whose `N(𝔟)`-factors cancel. Route B (`cardNormLeResidueClass_div_density`): the `𝔟`-divisible density is `κ'/N(𝔟)`. Route A as a limit: `cardNormLeResidueClass x C M / M = N(𝔟)·(Dvd(M·N(𝔟))/(M·N(𝔟)))` (`cardNormLeResidueClass_eq_dvd`, composing with `M ↦ M·N(𝔟)`); `tendsto_nhds_unique` + `mul_div_cancel₀`.
- **Hypotheses**: `[NeZero c]`; `IsUnit (N(𝔟):ZMod c)`; both densities.
- **Uses from project**: [`cardNormLeResidueClass_div_density`, `cardNormLeResidueClass_eq_dvd`, `cardNormLeResidueClass`, `cardNormLeResidueClassDvd`]
- **Used by**: `cardNormLeResidue_density_transfer`.
- **Visibility**: private · **Lines**: 4158–4194 · **Notes**: &gt;30 lines.

### `private theorem cardNormLeResidue_density_transfer`
- **Type**: With `IsUnit (N(𝔟):ZMod c)`, densities `κ` (residue `x`) and `κ'` (residue `x·N(𝔟)`): `κ = κ'`.
- **What**: Global realizer transfer — `κ_x = κ_{x·N(𝔟)}` for the all-class count.
- **How**: Both split over the class group (`tendsto_cardNormLeResidue_div_eq_sum_class`); the per-class transfer `κf C = κf' (C·[𝔟])` (`cardNormLeResidueClass_density_transfer`); reindex the sum by `Equiv.mulRight [𝔟]` (`Equiv.sum_comp`).
- **Hypotheses**: `[NeZero c]`; `IsUnit (N(𝔟):ZMod c)`; both densities.
- **Uses from project**: [`exists_tendsto_cardNormLeResidueClass_div`, `tendsto_cardNormLeResidue_div_eq_sum_class`, `cardNormLeResidueClass_density_transfer`, `cardNormLeResidue`]
- **Used by**: `cardNormLeResidue_density_const_of_realized` (used twice).
- **Visibility**: private · **Lines**: 4200–4227 · **Notes**: &gt;30 lines.

### `private theorem cardNormLeResidue_density_const_of_realized`
- **Type**: If every element of `S ≤ (ZMod c)ˣ` is realized as an ideal-norm residue (`hS`), `a, a' ∈ S` with densities `κ, κ'`: `κ = κ'`.
- **What**: κ-constancy over the realized-residue subgroup (Lang VI §3 Thm 3) — the **realizer** (not Fourier) direction.
- **How**: Realizers `𝔟, 𝔟'` with norm residues `a, a'` (units); transfer `1 → 1·N(𝔟) = a` gives `κ₁ = κ` and `1 → a'` gives `κ₁ = κ'` (`cardNormLeResidue_density_transfer` from the residue-`1` density `κ₁`).
- **Hypotheses**: `[NeZero c]`; realizer hypothesis `hS`; `a, a' ∈ S`; densities.
- **Uses from project**: [`exists_tendsto_cardNormLeResidue_div`, `cardNormLeResidue_density_transfer`, `cardNormLeResidue`]
- **Used by**: `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`.
- **Visibility**: private · **Lines**: 4255–4286 · **Notes**: &gt;30 lines; long docstring sketches the orthant-symmetry / equinumerosity proof (the actual proof is the cleaner realizer-transfer one).

### `theorem tendsto_sum_char_mul_cardNormLeResidue_div_of_realized` — PUBLIC (the `hF` producer)
- **Type**: `(K) (c) [NeZero c] (S) (hS) (χ : S →* ℂˣ) (hχ : χ ≠ 1) :` the `χ`-twisted count average `(∑ₛ χ(s)·#{N(I) ≤ N, N(I)≡s})/N → 0`.
- **What**: Fourier decay from realized residues — discharges exactly the `hF` hypothesis of `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`.
- **How**: Per-residue densities `κf s` (`exists_tendsto_cardNormLeResidue_div`) are constant on `S` (`cardNormLeResidue_density_const_of_realized`); the twisted average tends to `(∑ₛ χ(s))·κf 1` (`tendsto_finsetSum`), which vanishes by row orthogonality `sum_char_self_eq_zero_of_ne_one`.
- **Hypotheses**: `[NeZero c]`; subgroup `S`; realizer `hS`; nontrivial `χ`.
- **Uses from project**: [`exists_tendsto_cardNormLeResidue_div`, `cardNormLeResidue_density_const_of_realized`, `sum_char_self_eq_zero_of_ne_one`, `cardNormLeResidue`]
- **Used by**: external — `ZetaProduct.lean:1613` (supplies `hF` to the uniform count).
- **Visibility**: public · **Lines**: 4308–4348 · **Notes**: &gt;30 lines.

---

## File Summary

**Totals.** 56 declarations: **51 theorems/lemmas** (47 private + **4 public**) and **5 `private def`s** (`cardNormLeResidue`, `cardNormLeResidueClass`, `cardNormLeResidueClassDvd`, plus the helpers are all theorems; the three count-defs + nothing else — actually 3 defs). Precisely: **3 `def`** (`cardNormLeResidue`, `cardNormLeResidueClass`, `cardNormLeResidueClassDvd`), **53 theorems** (49 private + 4 public). All defs have real content (direct `Nat.card`); no `def := sorry`. **0 `sorry`, 0 `axiom`.**

**The 4 public theorems** (the file's API surface):
- `exists_card_coset_inter_smul_sub_volume_mul_rpow_le` (the workhorse; referenced by `NormLeOneLipschitz` docstrings),
- `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`,
- `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform` (consumed by `ZetaProduct.lean`),
- `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized` (the `hF` producer, consumed by `ZetaProduct.lean`).
The latter two are the live exports into the Chebotarev abelian step (Gap B).

**Key API used by ≥3 in-file consumers** (the load-bearing internal spine):
- `tendsto_div_atTop_of_sub_mul_rpow_le` — 14 uses (effective-estimate→limit converter).
- `cardNormLeResidueClass` (def) — 32; `cardNormLeResidueClassDvd` (def) — 23; `cardNormLeResidue` (def) — 20.
- `map_span_int_linearEquiv` — 10 (ℤ-span transport).
- `card_isPrincipal_dvd_norm_le_residue` — 8; `mem_span_int_basisFun_iff` — 8; `exists_card_idealSet_residue_le` — 8.
- `exists_card_norm_le_residue_class_eq_sub_mul_rpow_le` — 9.
- `idealLattice_mul_le` — 7.
- `exists_latticeEquiv_image_idealLattice`, `card_norm_le_residue_eq_sum_class`, `card_principalize`, `card_fibre_eq_card_cell`, `natCast_algebraNorm_add_nsmul_mul` — 6 each.
- `cardNormLeResidue_density_eq_of_mem_subgroup`, `exists_tendsto_cardNormLeResidue_div`, `cardNormLeResidueClass_eq_dvd`, `principalize_iff`, `exists_card_cell_sub_mul_rpow_le`, `norm_zmod_eq_of_emb_sub_mem`, `mem_coset_iff_cos_eq`, `exists_card_residue_fibre_sub_mul_rpow_le` — 5 each.

**Unused-in-file declarations (NO in-file consumer)** — flagged per the layered-accumulation concern:
1. **`exists_generator_diff_of_coset`** (lines 847–874) — truly dead; only its own definition appears. Superseded by the `round`-coordinate route (`sub_mem_nsmul_of_coord_eq` + `norm_zmod_eq_of_emb_sub_mem`). **Candidate for deletion.**
2. **`exists_card_dvd_principal_residue_real_le`** (lines 2382–2422) — dead; its only non-definition occurrence is a docstring mention (line 3747). The live L2 path (`cardNormLeResidueClassDvd_div_density`) uses `exists_card_idealSet_residue_real_le_dvd` directly, bypassing this principalized-but-not-class-split intermediate. **Candidate for deletion.**

All 4 public theorems are used externally (or are the intended export); every other private declaration has ≥1 in-file consumer except the two above.

**Declarations with `set_option`** (2):
- `card_isPrincipal_dvd_norm_le_residue` (line 1041): `set_option backward.isDefEq.respectTransparency false`.
- `exists_card_cell_sub_mul_rpow_le` (line 1114): `set_option linter.unusedFintypeInType false`.

**`sorry` / `TODO`:** none.

**Declarations &gt;30 lines** (the bulk — ~38 of 56): `ncard_index1_image_smul_chart_le`, `abs_cardR_translate_sub_volume_le`, `exists_card_coset_inter_smul_sub_volume_mul_rpow_le`, `norm_eq_prod_real_emb_mul_prod_complex`, `natAbs_norm_eq_neg_one_pow_mul_norm`, `card_norm_le_residue_eq_sum_class`, `principalize_iff`, `exists_latticeEquiv_image_idealLattice`, `exists_lipschitz_cube_cover_hyperplane_slab`, `exists_generator_diff_of_coset`, `frontier_signOrthant_subset`, `exists_frontier_cover_inter_orthant`, `mem_span_int_basisFun_iff`, `card_isPrincipal_dvd_norm_le_residue`, `exists_card_cell_sub_mul_rpow_le`, `sub_mem_nsmul_of_coord_eq`, `mem_coset_iff_cos_eq`, `card_fibre_eq_card_cell`, `exists_card_residue_fibre_sub_mul_rpow_le`, `finite_idealSet_norm_le`, `exists_card_idealSet_residue_le`, `exists_card_dvd_principal_residue_eq_sub_mul_rpow_le`, `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`, `cardNormLeResidue_density_eq_of_mem_subgroup`, `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`, `tendsto_div_atTop_of_sub_mul_rpow_le`, `cardNormLeResidueClass_eq_dvd`, `exists_card_idealSet_residue_real_le`, `exists_card_dvd_principal_residue_real_le`, `absNorm_coprime_of_isCoprime_span`, `crt_single_coset`, `exists_mk0_eq_absNorm_coprime`, `exists_card_fibre_dvd_eq_card_cell`, `exists_card_cell_sub_mul_rpow_le_explicit`, `residue_fibre_const_aux`, `exists_card_residue_fibre_sub_mul_rpow_le_explicit`, `exists_card_fibre_dvd_residue_sub_mul_rpow_le`, `card_idealSet_residue_eq_sum_cell`, `card_residue_sum_bound_aux`, `exists_card_idealSet_residue_real_le_dvd`, `card_principalize_dvd`, `tendsto_count_div_of_cone_bridge`, `cardNormLeResidueClassDvd_div_density`, `cardNormLeResidueClassDvd_div_density_routeA`, `tendsto_cardNormLeResidueClass_div_transfer`, `cardNormLeResidueClassDvd_sub_mul_rpow_le`, `cardNormLeResidueClass_density_transfer`, `cardNormLeResidue_density_transfer`, `cardNormLeResidue_density_const_of_realized`, `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`.

**Layering / redundancy map (the "8 worker layers" stratification, flagged per task):**
- **Layer 1 (lattice workhorse):** `ncard_index1_image_smul_chart_le` → `abs_cardR_translate_sub_volume_le` → `exists_card_coset_inter_smul_sub_volume_mul_rpow_le`.
- **Layer 2 (arithmetic/sign):** `natCast_algebraNorm_add_nsmul_mul`, `norm_eq_prod_real_emb_mul_prod_complex`, `prod_eq_neg_one_pow_card_mul_prod_abs`, `natAbs_norm_eq_neg_one_pow_mul_norm`.
- **Layer 3 (class split + principalization):** `card_norm_le_residue_eq_sum_class`, `natCast_eq_iff_mul_natCast_eq`, `principalize_iff`, `card_principalize`.
- **Layer 4 (chart geometry + cell bijection):** `map_span_int_linearEquiv`, `cone_normLe_eq_smul_normLeOne`, `exists_latticeEquiv_image_idealLattice`, the Lipschitz-cover combinators, the orthant/coset machinery, `card_isPrincipal_dvd_norm_le_residue`, the two `exists_card_cell_*` forms, `card_fibre_eq_card_cell`, `exists_card_residue_fibre_*`.
- **Layer 5 (assembled per-residue counts):** `exists_card_idealSet_residue_le`, `exists_card_dvd_principal_residue_*`, `exists_card_norm_le_residue_class_*`, `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`.
- **Layer 6 (Fourier/density):** the `cardNormLeResidue*` defs, `sum_char_*_eq_zero_of_ne_one`, `cardNormLeResidue_density_eq_of_mem_subgroup`, `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`.
- **Layer 7 (the L2 geometry-of-numbers kernel):** `span_image_basisFun_eq` … `exists_card_idealSet_residue_real_le_dvd`, `crt_single_coset`, `exists_mk0_eq_absNorm_coprime`, the two L2 proofs.
- **Layer 8 (realizer transfer → `hF`):** the `*_transfer` chain, `cardNormLeResidue_density_const_of_realized`, `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`.

**Notable redundancy (accumulated, not yet consolidated):**
- **Two complete L2 proofs of the same conclusion** (`cardNormLeResidueClassDvd c 𝔟 y D N / N → κfull/N(𝔟)`): the **geometric** `cardNormLeResidueClassDvd_div_density` (Route B/CRT, lines 3758) and the **kernel-routed** `cardNormLeResidueClass_div_density` (lines 4133, via `cardNormLeResidueClassDvd_sub_mul_rpow_le`). They are wired into a small cycle: geometric-L2 → `tendsto_cardNormLeResidueClass_div_transfer` → kernel → kernel-routed-L2 → `cardNormLeResidueClass_density_transfer`. Both are reachable; the geometric one is what actually discharges the deep gap, the kernel-routed one is the live transfer-path entry. Consolidating to a single L2 proof would remove a large duplicate.
- **Implicit-κ vs explicit-κ twins:** `exists_card_cell_sub_mul_rpow_le`/`_explicit`; `exists_card_residue_fibre_sub_mul_rpow_le`/`_explicit`.
- **Cell-partition logic triplicated:** inline in `exists_card_idealSet_residue_le` and `exists_card_idealSet_residue_real_le`, then extracted as `card_idealSet_residue_eq_sum_cell`.
- **The `hreg` orthant region-membership block (~40 lines) is duplicated verbatim** between `card_fibre_eq_card_cell` and `exists_card_fibre_dvd_eq_card_cell`.
- **The residue-constancy block** appears inline in `exists_card_residue_fibre_sub_mul_rpow_le` and extracted as `residue_fibre_const_aux`.

These are correctness-neutral (everything builds, 0 sorry) but represent clear consolidation opportunities; the two genuinely-dead declarations (`exists_generator_diff_of_coset`, `exists_card_dvd_principal_residue_real_le`) are safe deletions.</result>
<usage><subagent_tokens>207475</subagent_tokens><tool_uses>22</tool_uses><duration_ms>532035</duration_ms></usage>
</task-notification>