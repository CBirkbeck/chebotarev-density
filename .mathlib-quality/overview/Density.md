# Inventory: `CebotarevDensity/Density.lean`

File: `/Users/mcu22seu/Documents/GitHub/chebotarev-density/CebotarevDensity/Density.lean` (693 lines). Module header `@[expose] public section` + `noncomputable section`; `namespace Chebotarev`; variable line `{K : Type*} [Field K] [NumberField K] {S : Set (Ideal (𝓞 K))} {δ : ℝ}` (lines 1–46). A `variable (K)` at line 316 re-enables `K` explicit for the universal-sum analytic theorems. No `set_option`, no `sorry`, no `axiom` anywhere in the file.

Imported helper lemmas used but **not** declared here: `tendsto_log_one_div_sub_one_atTop`, `tendsto_ratio_one_of_log_pm_bounded` (from project file `CebotarevDensity/ForMathlib/LogOneDivSubOne.lean`); `NonzeroIdeal`, `idealNormMultiplicity`, `idealNormMultiplicity_zero`, `summable_idealNormMultiplicity_mul_cpow_neg`, `dedekindZeta_eq_tprod_primeIdeal` (from project file `CebotarevDensity/NumberFieldEulerProduct.lean`). These are project declarations from *other* files; I list them under "Uses from project" where referenced.

---

### `def primeIdealZetaSum`
- **Type**: `(S : Set (Ideal (𝓞 K))) (s : ℝ) : ℝ`
- **What**: The partial Dirichlet series `Σ_{𝔭 ∈ S} N𝔭^{-s}`, summing `N𝔭^{-s}` over nonzero prime ideals `𝔭` of `𝓞 K` lying in `S`.
- **How**: Direct definition as a `tsum` over the subtype `{𝔭 // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}` of the real power `(Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)`.
- **Hypotheses**: None (total definition; the `tsum` is `0` when not summable).
- **Uses from project**: []
- **Used by**: `primeIdealZetaSum_def`, and indirectly every theorem in the file via the `_def` equation lemma.
- **Visibility**: public · **Lines**: 48–52 (def, 2 lines) · **Notes**: —

### `theorem primeIdealZetaSum_def`
- **Type**: `(S : Set (Ideal (𝓞 K))) (s : ℝ) : primeIdealZetaSum S s = ∑' 𝔭 : {𝔭 // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)`
- **What**: Equation lemma unfolding `primeIdealZetaSum` to its defining `tsum`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: [`primeIdealZetaSum`]
- **Used by**: `hasDirichletDensity_empty`, `primeIdealZetaSum_nonneg`, `primeIdealZetaSum_le_univ`, `primeIdealZetaSum_le_of_subset`, `primeIdealZetaSum_union_of_disjoint`, `primeIdealZetaSum_empty`, `primeIdealZetaSum_eq_univ_of_forall_prime_mem`, `primeIdealZetaSum_univ_eq_tsum_prime2`, `primeIdealZetaSum_le_card_of_finite`, `hasDirichletDensity_of_finite`.
- **Visibility**: public · **Lines**: 54–58 (proof: `rfl`) · **Notes**: —

### `def HasDirichletDensity`
- **Type**: `(S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop`
- **What**: `S` has Dirichlet density `δ`, meaning the ratio of partial sums `primeIdealZetaSum S s / primeIdealZetaSum univ s` tends to `δ` as `s ↓ 1` (Sharifi 7.1.13).
- **How**: Defined as `Tendsto (fun s ↦ ratio) (𝓝[&gt;] 1) (𝓝 δ)`.
- **Hypotheses**: None.
- **Uses from project**: [`primeIdealZetaSum`]
- **Used by**: `hasDirichletDensity_empty`, `HasDirichletDensity.of_upper_eq_lower`, `HasDirichletDensity.hasUpper`, `HasDirichletDensity.hasLower`, `HasDirichletDensity.union_of_disjoint`, `hasDirichletDensity_of_finite`, `hasDirichletDensity_univ`.
- **Visibility**: public · **Lines**: 60–67 (def, 3 lines) · **Notes**: —

### `def HasUpperDirichletDensity`
- **Type**: `(S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop`
- **What**: Upper Dirichlet density of `S` is `δ`, the `limsup` of the ratio of partial sums as `s ↓ 1`. (Standard convention upper = `limsup`; docstring flags that Sharifi's labelling of upper/lower is inverted relative to this.)
- **How**: Defined as `limsup (fun s ↦ ratio) (𝓝[&gt;] 1) = δ`.
- **Hypotheses**: None.
- **Uses from project**: [`primeIdealZetaSum`]
- **Used by**: `HasDirichletDensity.of_upper_eq_lower`, `HasDirichletDensity.hasUpper`.
- **Visibility**: public · **Lines**: 69–85 (def, 3 lines) · **Notes**: long convention-note docstring.

### `def HasLowerDirichletDensity`
- **Type**: `(S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop`
- **What**: Lower Dirichlet density of `S` is `δ`, the `liminf` of the ratio of partial sums as `s ↓ 1` (matches Sharifi's `δ_inf`).
- **How**: Defined as `liminf (fun s ↦ ratio) (𝓝[&gt;] 1) = δ`.
- **Hypotheses**: None.
- **Uses from project**: [`primeIdealZetaSum`]
- **Used by**: `HasDirichletDensity.of_upper_eq_lower`, `HasDirichletDensity.hasLower`, `HasLowerDirichletDensity.mono`.
- **Visibility**: public · **Lines**: 87–92 (def, 3 lines) · **Notes**: —

### `theorem hasDirichletDensity_empty`
- **Type**: `HasDirichletDensity (∅ : Set (Ideal (𝓞 K))) 0`
- **What**: The Dirichlet density of the empty set of primes is `0`.
- **How**: The qualifying-prime subtype over `∅` is empty (`IsEmpty`, from the `𝔭 ∈ ∅` component), so `tsum_empty` makes the numerator `0`; the constant-`0` ratio tends to `0` by `tendsto_const_nhds`.
- **Hypotheses**: None.
- **Uses from project**: [`HasDirichletDensity`, `primeIdealZetaSum_def`]
- **Used by**: unused in file.
- **Visibility**: public · **Lines**: 94–100 (proof ~4 lines) · **Notes**: —

### `private theorem summable_nonzeroIdeal_absNorm_rpow`
- **Type**: `{s : ℝ} (hs : 1 &lt; s) : Summable (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s))`
- **What**: For `s &gt; 1`, the series `Σ_I N(I)^{-s}` over all nonzero ideals `I` of `𝓞 K` is summable.
- **How**: Regroup over norm values via `Equiv.sigmaFiberEquiv` and `summable_sigma_of_nonneg`; each fibre `{I : N(I) = n}` is finite (image-injective into `Ideal.finite_setOf_absNorm_eq`), and the fibre-sum series equals the norm of the Dedekind-zeta term, summable by `summable_idealNormMultiplicity_mul_cpow_neg`.
- **Hypotheses**: `1 &lt; s`.
- **Uses from project**: [`NonzeroIdeal`, `idealNormMultiplicity`, `idealNormMultiplicity_zero`, `summable_idealNormMultiplicity_mul_cpow_neg`] (all from `NumberFieldEulerProduct.lean`)
- **Used by**: `summable_prime_absNorm_rpow`.
- **Visibility**: private · **Lines**: 102–131 (proof ~26 lines) · **Notes**: &gt;10-line proof; cites `summable_idealNormMultiplicity_mul_cpow_neg`, `Equiv.sigmaFiberEquiv`, `Ideal.finite_setOf_absNorm_eq`.

### `theorem summable_prime_absNorm_rpow`
- **Type**: `(S : Set (Ideal (𝓞 K))) {s : ℝ} (hs : 1 &lt; s) : Summable (fun 𝔭 : {𝔭 // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))`
- **What**: For `s &gt; 1`, the series `Σ_𝔭 N𝔭^{-s}` over nonzero primes of `𝓞 K` in `S` is summable.
- **How**: The prime-in-`S` subtype injects into `NonzeroIdeal K` (forgetting `S`-membership and primality); pull back summability of `summable_nonzeroIdeal_absNorm_rpow` via `Summable.comp_injective`.
- **Hypotheses**: `1 &lt; s`.
- **Uses from project**: [`summable_nonzeroIdeal_absNorm_rpow`, `NonzeroIdeal`]
- **Used by**: `primeIdealZetaSum_le_univ`, `primeIdealZetaSum_le_of_subset`, `primeIdealZetaSum_union_of_disjoint`, `summable_prime2_absNorm_rpow`.
- **Visibility**: public · **Lines**: 133–143 (proof ~5 lines) · **Notes**: —

### `private theorem primeIdealZetaSum_nonneg`
- **Type**: `(S : Set (Ideal (𝓞 K))) (s : ℝ) : 0 ≤ primeIdealZetaSum S s`
- **What**: The partial Dirichlet series is nonnegative.
- **How**: It is a `tsum` of nonnegative terms `N𝔭^{-s} ≥ 0`; close with `tsum_nonneg` and `Real.rpow_nonneg`.
- **Hypotheses**: None.
- **Uses from project**: [`primeIdealZetaSum_def`]
- **Used by**: `HasDirichletDensity.of_upper_eq_lower`, `HasDirichletDensity.union_of_disjoint`, `HasLowerDirichletDensity.mono`, `tendsto_primeIdealZetaSum_div_univ_zero_of_le_const`.
- **Visibility**: private · **Lines**: 145–150 (proof 2 lines) · **Notes**: —

### `private theorem primeIdealZetaSum_le_univ`
- **Type**: `{s : ℝ} (hs : 1 &lt; s) : primeIdealZetaSum S s ≤ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s`
- **What**: For `s &gt; 1`, the partial sum over `S` is at most the sum over all primes.
- **How**: The `S`-prime subtype injects into the universal-prime subtype with equal terms; both families summable, so `Summable.tsum_le_tsum_of_inj` gives the inequality.
- **Hypotheses**: `1 &lt; s`.
- **Uses from project**: [`primeIdealZetaSum_def`, `summable_prime_absNorm_rpow`]
- **Used by**: `HasDirichletDensity.of_upper_eq_lower`, `HasLowerDirichletDensity.mono`.
- **Visibility**: private · **Lines**: 152–162 (proof ~5 lines) · **Notes**: —

### `theorem primeIdealZetaSum_le_of_subset`
- **Type**: `{T : Set (Ideal (𝓞 K))} (hST : S ⊆ T) {s : ℝ} (hs : 1 &lt; s) : primeIdealZetaSum S s ≤ primeIdealZetaSum T s`
- **What**: For `s &gt; 1` and `S ⊆ T`, the partial sum over `S` is at most the one over `T`.
- **How**: The `S`-prime subtype injects into the `T`-prime subtype (using `hST`) with equal terms; both summable, so `Summable.tsum_le_tsum_of_inj`.
- **Hypotheses**: `S ⊆ T`, `1 &lt; s`.
- **Uses from project**: [`primeIdealZetaSum_def`, `summable_prime_absNorm_rpow`]
- **Used by**: `HasLowerDirichletDensity.mono`.
- **Visibility**: public · **Lines**: 164–175 (proof ~5 lines) · **Notes**: —

### `theorem primeIdealZetaSum_union_of_disjoint`
- **Type**: `{T : Set (Ideal (𝓞 K))} (hDisj : Disjoint S T) {s : ℝ} (hs : 1 &lt; s) : primeIdealZetaSum (S ∪ T) s = primeIdealZetaSum S s + primeIdealZetaSum T s`
- **What**: For disjoint `S`, `T` and `s &gt; 1`, the partial sum over `S ∪ T` splits as the sum of those over `S` and `T`.
- **How**: Build explicit equivs `eS`, `eT` identifying the `S`-prime (resp. `T`-prime) subtype with the subset (resp. complement) of the union-prime subtype cut by "membership in `S`"; then split the union `tsum` via `Summable.tsum_subtype_add_tsum_subtype_compl` and transport each piece by `Equiv.tsum_eq`.
- **Hypotheses**: `Disjoint S T`, `1 &lt; s`.
- **Uses from project**: [`primeIdealZetaSum_def`, `summable_prime_absNorm_rpow`]
- **Used by**: `primeIdealZetaSum_biUnion_of_pairwiseDisjoint`, `HasDirichletDensity.union_of_disjoint`.
- **Visibility**: public · **Lines**: 177–202 (proof ~25 lines) · **Notes**: &gt;10-line proof with two inline `Equiv` constructions; key lemma `tsum_subtype_add_tsum_subtype_compl`.

### `theorem primeIdealZetaSum_empty`
- **Type**: `(s : ℝ) : primeIdealZetaSum (∅ : Set (Ideal (𝓞 K))) s = 0`
- **What**: The partial Dirichlet series over the empty set is `0`.
- **How**: The qualifying-prime subtype over `∅` is `IsEmpty`, so `tsum_empty` gives `0`.
- **Hypotheses**: None.
- **Uses from project**: [`primeIdealZetaSum_def`]
- **Used by**: `primeIdealZetaSum_biUnion_of_pairwiseDisjoint`.
- **Visibility**: public · **Lines**: 204–208 (proof ~3 lines) · **Notes**: —

### `theorem primeIdealZetaSum_biUnion_of_pairwiseDisjoint`
- **Type**: `{ι : Type*} (t : Finset ι) (g : ι → Set (Ideal (𝓞 K))) (hg : (t : Set ι).PairwiseDisjoint g) {s : ℝ} (hs : 1 &lt; s) : primeIdealZetaSum (⋃ i ∈ t, g i) s = ∑ i ∈ t, primeIdealZetaSum (g i) s`
- **What**: For a `Finset`-indexed pairwise-disjoint family, the partial sum over the union equals the finite sum of the per-piece partial sums.
- **How**: `Finset.induction` on `t`; the inductive step uses `Finset.set_biUnion_insert` and reduces the new piece against the rest via the two-set case `primeIdealZetaSum_union_of_disjoint`, with disjointness from `disjoint_iUnion₂_right` and the pairwise hypothesis.
- **Hypotheses**: `g` pairwise-disjoint on `t`, `1 &lt; s`.
- **Uses from project**: [`primeIdealZetaSum_empty`, `primeIdealZetaSum_union_of_disjoint`]
- **Used by**: unused in file.
- **Visibility**: public · **Lines**: 210–225 (proof ~9 lines) · **Notes**: induction; cites `disjoint_iUnion₂_right`.

### `theorem primeIdealZetaSum_eq_univ_of_forall_prime_mem`
- **Type**: `(hS : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭 ∈ S) (s : ℝ) : primeIdealZetaSum S s = primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s`
- **What**: If `S` contains every nonzero prime, its partial sum equals the universal one.
- **How**: Build an explicit `Equiv` between the `S`-prime subtype and the universal-prime subtype (the back map supplies `S`-membership from `hS`), then transport the `tsum` via `Equiv.tsum_eq`.
- **Hypotheses**: every nonzero prime lies in `S`.
- **Uses from project**: [`primeIdealZetaSum_def`]
- **Used by**: unused in file.
- **Visibility**: public · **Lines**: 227–241 (proof ~9 lines) · **Notes**: inline `Equiv`.

### `theorem HasDirichletDensity.of_upper_eq_lower`
- **Type**: `(hUp : HasUpperDirichletDensity S δ) (hLow : HasLowerDirichletDensity S δ) : HasDirichletDensity S δ`
- **What**: Sandwich criterion: if upper density = lower density = `δ`, then `S` has Dirichlet density `δ`.
- **How**: `tendsto_of_liminf_eq_limsup` from `hLow`/`hUp`, discharging boundedness: the ratio is eventually `≤ 1` (numerator `≤` denominator by `primeIdealZetaSum_le_univ`, via `div_le_one_of_le₀`) and `≥ 0` (`div_nonneg` of two `primeIdealZetaSum_nonneg`).
- **Hypotheses**: upper and lower densities both equal `δ`.
- **Uses from project**: [`HasUpperDirichletDensity`, `HasLowerDirichletDensity`, `HasDirichletDensity`, `primeIdealZetaSum_le_univ`, `primeIdealZetaSum_nonneg`]
- **Used by**: unused in file.
- **Visibility**: public · **Lines**: 243–259 (proof ~10 lines) · **Notes**: cites `tendsto_of_liminf_eq_limsup`.

### `theorem HasDirichletDensity.hasUpper`
- **Type**: `(h : HasDirichletDensity S δ) : HasUpperDirichletDensity S δ`
- **What**: A convergent density yields the upper (`limsup`) density equal to `δ`.
- **How**: `h.limsup_eq` — the `limsup` of a `Tendsto`-convergent function equals its limit.
- **Hypotheses**: `S` has Dirichlet density `δ`.
- **Uses from project**: [`HasDirichletDensity`, `HasUpperDirichletDensity`]
- **Used by**: unused in file.
- **Visibility**: public · **Lines**: 261–265 (proof: term `h.limsup_eq`) · **Notes**: —

### `theorem HasDirichletDensity.hasLower`
- **Type**: `(h : HasDirichletDensity S δ) : HasLowerDirichletDensity S δ`
- **What**: A convergent density yields the lower (`liminf`) density equal to `δ`.
- **How**: `h.liminf_eq` — the `liminf` of a convergent function equals its limit.
- **Hypotheses**: `S` has Dirichlet density `δ`.
- **Uses from project**: [`HasDirichletDensity`, `HasLowerDirichletDensity`]
- **Used by**: unused in file.
- **Visibility**: public · **Lines**: 267–271 (proof: term `h.liminf_eq`) · **Notes**: —

### `theorem HasDirichletDensity.union_of_disjoint`
- **Type**: `{T : Set (Ideal (𝓞 K))} (hDisj : Disjoint S T) {ε : ℝ} (hS : HasDirichletDensity S δ) (hT : HasDirichletDensity T ε) : HasDirichletDensity (S ∪ T) (δ + ε)`
- **What**: The Dirichlet density of a disjoint union is the sum of the densities.
- **How**: Add the two convergent ratios (`hS.add hT`) and rewrite with `Tendsto.congr'`: eventually for `s &gt; 1`, the union-ratio equals the sum of ratios via `primeIdealZetaSum_union_of_disjoint` and `add_div`.
- **Hypotheses**: `Disjoint S T`; `S`, `T` have densities `δ`, `ε`.
- **Uses from project**: [`HasDirichletDensity`, `primeIdealZetaSum_union_of_disjoint`]
- **Used by**: unused in file.
- **Visibility**: public · **Lines**: 273–282 (proof ~5 lines) · **Notes**: —

### `theorem HasLowerDirichletDensity.mono`
- **Type**: `{T : Set (Ideal (𝓞 K))} (hST : S ⊆ T) {ε : ℝ} (hS : HasLowerDirichletDensity S δ) (hT : HasLowerDirichletDensity T ε) : δ ≤ ε`
- **What**: Monotonicity of lower density under inclusion `S ⊆ T`.
- **How**: Rewrite `δ`, `ε` as `liminf`s and apply `liminf_le_liminf`: the `S`-ratio is eventually `≤` the `T`-ratio (`div_le_div_of_nonneg_right` from `primeIdealZetaSum_le_of_subset`); supply the required (co)boundedness from `primeIdealZetaSum_nonneg` and the eventual `≤ 1` bound (`primeIdealZetaSum_le_univ`).
- **Hypotheses**: `S ⊆ T`; lower densities of `S`, `T` are `δ`, `ε`.
- **Uses from project**: [`HasLowerDirichletDensity`, `primeIdealZetaSum_le_of_subset`, `primeIdealZetaSum_nonneg`, `primeIdealZetaSum_le_univ`]
- **Used by**: unused in file.
- **Visibility**: public · **Lines**: 284–302 (proof ~14 lines) · **Notes**: &gt;10-line proof; cites `liminf_le_liminf`, `isCoboundedUnder_ge_of_eventually_le`.

### `private theorem summable_prime2_absNorm_rpow`
- **Type**: `{s : ℝ} (hs : 1 &lt; s) : Summable (fun 𝔭 : {𝔭 // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))` (with `K` explicit)
- **What**: For `s &gt; 1`, `Σ_𝔭 N𝔭^{-s}` over the bare 2-part nonzero-prime subtype (no ambient set) is summable.
- **How**: The bare subtype injects into the `univ`-prime subtype (adding the trivial `∈ univ` component); transport `summable_prime_absNorm_rpow univ` via `Summable.comp_injective`.
- **Hypotheses**: `1 &lt; s`.
- **Uses from project**: [`summable_prime_absNorm_rpow`]
- **Used by**: `primeIdealZetaHigherTail_bounded`, `summable_neg_log_one_sub_absNorm_rpow`, `abs_tsum_neg_log_one_sub_sub_rpow_le`, `logDedekindZeta_sub_primeIdealZetaSum_bounded`.
- **Visibility**: private · **Lines**: 318–330 (proof ~5 lines) · **Notes**: first decl after `variable (K)`.

### `private theorem two_le_absNorm_of_prime`
- **Type**: `{𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) : (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ)` (with `K` explicit)
- **What**: A nonzero prime ideal has absolute norm at least `2`.
- **How**: Its norm is `≠ 0` (not `⊥`, via `Ideal.absNorm_eq_zero_iff`) and `≠ 1` (not `⊤`, via `Ideal.absNorm_eq_one_iff` and `hp.ne_top`), so the positive natural norm is `≥ 2` (`lia`), then cast.
- **Hypotheses**: `𝔭` prime and `𝔭 ≠ ⊥`.
- **Uses from project**: []
- **Used by**: `primeIdealHigherTail_term_le`, `primeIdealZetaHigherTail_bounded`, `one_sub_absNorm_rpow_pos`, `abs_tsum_neg_log_one_sub_sub_rpow_le`.
- **Visibility**: private · **Lines**: 332–339 (proof ~3 lines) · **Notes**: —

### `private theorem primeIdealHigherTail_term_le`
- **Type**: `{𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) {s : ℝ} (hs : 1 &lt; s) : (Ideal.absNorm 𝔭 : ℝ) ^ (-2*s) / (1 - (Ideal.absNorm 𝔭 : ℝ) ^ (-s)) ≤ 2 * (Ideal.absNorm 𝔭 : ℝ) ^ (-2)` (with `K` explicit)
- **What**: Per-prime termwise bound for the higher-power Euler tail: the geometric term is dominated by `2·N𝔭^{-2}`.
- **How**: From `2 ≤ N𝔭` derive `N𝔭^{-s} ≤ 1/2` (chain `Real.rpow_le_rpow_of_nonpos`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_neg_one`), hence denominator `≥ 1/2` so its inverse `≤ 2` (`inv_le_comm₀`); and `N𝔭^{-2s} ≤ N𝔭^{-2}` since base `≥ 1`, exponent decreases; combine with `mul_le_mul` in a `calc`.
- **Hypotheses**: `𝔭` prime, `𝔭 ≠ ⊥`, `1 &lt; s`.
- **Uses from project**: [`two_le_absNorm_of_prime`]
- **Used by**: `primeIdealZetaHigherTail_bounded`, `abs_tsum_neg_log_one_sub_sub_rpow_le`.
- **Visibility**: private · **Lines**: 341–366 (proof ~22 lines) · **Notes**: &gt;10-line proof; cites `Real.rpow_le_rpow_of_nonpos`, `inv_le_comm₀`, `mul_le_mul`.

### `theorem primeIdealZetaHigherTail_bounded`
- **Type**: `∃ C : ℝ, ∀ᶠ s in 𝓝[&gt;] 1, ∑' 𝔭 : {𝔭 // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-2*s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) ≤ C` (with `K` explicit)
- **What**: Sharifi 7.1.12: the geometric higher-power Euler tail `Σ_{𝔭,k≥2} N𝔭^{-ks}` is bounded near `s = 1`.
- **How**: Take `C = 2·Σ_𝔭 N𝔭^{-2}`; termwise bound by `primeIdealHigherTail_term_le`, nonnegativity from `Real.rpow_lt_one_of_one_lt_of_neg`, summability of the dominating series from `summable_prime2_absNorm_rpow` (`.mul_left 2`), then `Summable.tsum_le_tsum` and `tsum_mul_left` in a `calc`.
- **Hypotheses**: None (existential over `C`).
- **Uses from project**: [`primeIdealHigherTail_term_le`, `two_le_absNorm_of_prime`, `summable_prime2_absNorm_rpow`]
- **Used by**: `abs_tsum_neg_log_one_sub_sub_rpow_le`.
- **Visibility**: public · **Lines**: 368–404 (proof ~29 lines) · **Notes**: &gt;10-line proof; cites `Summable.of_nonneg_of_le`, `tsum_mul_left`.

### `private theorem primeIdealZetaSum_univ_eq_tsum_prime2`
- **Type**: `(s : ℝ) : primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s = ∑' 𝔭 : {𝔭 // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)` (with `K` explicit)
- **What**: Re-indexes the universal partial sum over the bare 2-part nonzero-prime subtype (drops the trivial `∈ univ`).
- **How**: Build the obvious `Equiv` adding/removing the `∈ univ` component and transport via `Equiv.tsum_eq`.
- **Hypotheses**: None.
- **Uses from project**: [`primeIdealZetaSum_def`]
- **Used by**: `logDedekindZeta_sub_primeIdealZetaSum_bounded`.
- **Visibility**: private · **Lines**: 406–418 (proof ~8 lines) · **Notes**: inline `Equiv`.

### `private theorem one_sub_absNorm_rpow_pos`
- **Type**: `{𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) {s : ℝ} (hs : 1 &lt; s) : (0 : ℝ) &lt; 1 - (Ideal.absNorm 𝔭 : ℝ) ^ (-s)` (with `K` explicit)
- **What**: For a nonzero prime and `s &gt; 1`, the Euler-factor denominator `1 - N𝔭^{-s}` is positive.
- **How**: `N𝔭 ≥ 2 &gt; 1` and `-s &lt; 0`, so `N𝔭^{-s} &lt; 1` by `Real.rpow_lt_one_of_one_lt_of_neg`; `linarith`.
- **Hypotheses**: `𝔭` prime, `𝔭 ≠ ⊥`, `1 &lt; s`.
- **Uses from project**: [`two_le_absNorm_of_prime`]
- **Used by**: `log_dedekindZeta_re_eq_tsum_neg_log_one_sub`, `abs_tsum_neg_log_one_sub_sub_rpow_le`.
- **Visibility**: private · **Lines**: 420–426 (proof ~3 lines) · **Notes**: —

### `private theorem neg_log_one_sub_sub_le`
- **Type**: `{x : ℝ} (hx0 : 0 ≤ x) (hx1 : x &lt; 1) : 0 ≤ -Real.log (1 - x) - x ∧ -Real.log (1 - x) - x ≤ x ^ 2 / (1 - x)`
- **What**: For `0 ≤ x &lt; 1`, two-sided bound `0 ≤ -log(1-x) - x ≤ x²/(1-x)`.
- **How**: Lower bound from `Real.log_le_sub_one_of_pos` applied to `1-x`; upper bound from `Real.abs_log_sub_add_sum_range_le` at order `1` (the degree-1 Taylor remainder of `log(1-x)`), simplified and finished with `linarith`.
- **Hypotheses**: `0 ≤ x`, `x &lt; 1`.
- **Uses from project**: []
- **Used by**: `abs_tsum_neg_log_one_sub_sub_rpow_le`.
- **Visibility**: private · **Lines**: 428–437 (proof ~7 lines) · **Notes**: cites `Real.abs_log_sub_add_sum_range_le`, `Real.log_le_sub_one_of_pos`.

### `private theorem summable_neg_log_one_sub_absNorm_rpow`
- **Type**: `{s : ℝ} (hs : 1 &lt; s) : Summable (fun 𝔭 : {𝔭 // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =&gt; -Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)))` (with `K` explicit)
- **What**: For `s &gt; 1`, the Euler-factor logs `-log(1 - N𝔭^{-s})` are summable over nonzero primes.
- **How**: `Σ_𝔭 N𝔭^{-s}` is summable (`summable_prime2_absNorm_rpow`, negated), so `Real.summable_log_one_add_of_summable` gives summability of `log(1 + (-N𝔭^{-s}))`; rewrite `1 - x = 1 + (-x)` to match.
- **Hypotheses**: `1 &lt; s`.
- **Uses from project**: [`summable_prime2_absNorm_rpow`]
- **Used by**: `log_dedekindZeta_re_eq_tsum_neg_log_one_sub`, `logDedekindZeta_sub_primeIdealZetaSum_bounded`.
- **Visibility**: private · **Lines**: 439–446 (proof ~4 lines) · **Notes**: cites `Real.summable_log_one_add_of_summable`.

### `private theorem log_dedekindZeta_re_eq_tsum_neg_log_one_sub`
- **Type**: `{s : ℝ} (hs : 1 &lt; s) : Real.log (dedekindZeta K (s : ℂ)).re = ∑' 𝔭 : {𝔭 // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (-Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)))` (with `K` explicit)
- **What**: For real `s &gt; 1`, `log ζ_K(s) = Σ_𝔭 -log(1 - N𝔭^{-s})` (Sharifi 7.1.12).
- **How**: Set `g 𝔭 = (1 - N𝔭^{-s})⁻¹ &gt; 0`; from summability of `log g` (= the factor logs) get `HasProd g (exp(Σ log g))` via `Real.hasProd_of_hasSum_log`, push the product through `Complex.ofReal` (matching the complex Euler factors by `Complex.ofReal_cpow`), and equate with `dedekindZeta_eq_tprod_primeIdeal` to read off `(ζ_K).re = exp(Σ log g)`; then `Real.log_exp` and `tsum_congr` with `Real.log_inv`.
- **Hypotheses**: `1 &lt; s`.
- **Uses from project**: [`summable_neg_log_one_sub_absNorm_rpow`, `one_sub_absNorm_rpow_pos`, `dedekindZeta_eq_tprod_primeIdeal` (from `NumberFieldEulerProduct.lean`)]
- **Used by**: `logDedekindZeta_sub_primeIdealZetaSum_bounded`.
- **Visibility**: private · **Lines**: 448–488 (proof ~40 lines) · **Notes**: &gt;30-line proof; cites `Real.hasProd_of_hasSum_log`, `dedekindZeta_eq_tprod_primeIdeal`, `Complex.ofReal_cpow`.

### `private theorem abs_tsum_neg_log_one_sub_sub_rpow_le`
- **Type**: `∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[&gt;] 1, |∑' 𝔭 : {𝔭 // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (-Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))| ≤ C` (with `K` explicit)
- **What**: The remainder `Σ_𝔭 (-log(1 - N𝔭^{-s}) - N𝔭^{-s})` is bounded near `s = 1` (Sharifi 7.1.12).
- **How**: Reuse `C` from `primeIdealZetaHigherTail_bounded`. Per term `f 𝔭` is nonnegative and `≤ h 𝔭` (the geometric tail term) by `neg_log_one_sub_sub_le`, where `x²/(1-x)` is matched to `N𝔭^{-2s}/(1-N𝔭^{-s})` via `Real.rpow_natCast`/`Real.rpow_mul`; `h` is summable (dominated, `primeIdealHigherTail_term_le` + `summable_prime2_absNorm_rpow`), hence so is `f`; then `abs_of_nonneg`, `Summable.tsum_le_tsum`, and the tail bound `hs_tail`.
- **Hypotheses**: None (existential over `C`).
- **Uses from project**: [`primeIdealZetaHigherTail_bounded`, `two_le_absNorm_of_prime`, `neg_log_one_sub_sub_le`, `primeIdealHigherTail_term_le`, `summable_prime2_absNorm_rpow`, `one_sub_absNorm_rpow_pos`]
- **Used by**: `logDedekindZeta_sub_primeIdealZetaSum_bounded`.
- **Visibility**: private · **Lines**: 490–527 (proof ~36 lines) · **Notes**: &gt;30-line proof; cites `Summable.of_nonneg_of_le`, `Real.rpow_mul`.

### `theorem logDedekindZeta_sub_primeIdealZetaSum_bounded`
- **Type**: `∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[&gt;] 1, |Real.log (dedekindZeta K (s : ℂ)).re - primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s| ≤ C` (with `K` explicit)
- **What**: Euler-product-log identity `log ζ_K(s) = Σ_𝔭 N𝔭^{-s} + O(1)` as `s ↓ 1` (Sharifi 7.1.12).
- **How**: Rewrite `log ζ_K` as the factor-log `tsum` (`log_dedekindZeta_re_eq_tsum_neg_log_one_sub`) and the universal sum as the bare-prime `tsum` (`primeIdealZetaSum_univ_eq_tsum_prime2`); subtract termwise via `Summable.tsum_sub` (both summable) and bound by `abs_tsum_neg_log_one_sub_sub_rpow_le`.
- **Hypotheses**: None (existential over `C`).
- **Uses from project**: [`abs_tsum_neg_log_one_sub_sub_rpow_le`, `log_dedekindZeta_re_eq_tsum_neg_log_one_sub`, `primeIdealZetaSum_univ_eq_tsum_prime2`, `summable_neg_log_one_sub_absNorm_rpow`, `summable_prime2_absNorm_rpow`]
- **Used by**: `log_minus_bounded_le_primeIdealZetaSum`, `primeIdealZetaSum_le_log_plus_bounded`.
- **Visibility**: public · **Lines**: 529–542 (proof ~8 lines) · **Notes**: cites `Summable.tsum_sub`.

### `theorem logDedekindZeta_sub_log_inv_sub_one_bounded`
- **Type**: `∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[&gt;] 1, |Real.log (dedekindZeta K (s : ℂ)).re - Real.log (1 / (s - 1))| ≤ C` (with `K` explicit)
- **What**: Simple-pole identity `log ζ_K(s) = log(1/(s-1)) + O(1)` as `s ↓ 1`, from the simple pole of `ζ_K` at `s = 1` (Sharifi 7.1.12).
- **How**: From `tendsto_sub_one_mul_dedekindZeta_nhdsGT` (mathlib) the real product `(s-1)·(ζ_K).re → r := dedekindZeta_residue K &gt; 0`, so it is eventually in `Ioo (r/2) (2r)`; this pins `(ζ_K).re &gt; 0`, and rewriting `log(1/(s-1)) = -log(s-1)`, `log ζ - (-log(s-1)) = log((s-1)·ζ)`, the two-sided window gives `|·| ≤ max |log(r/2)| |log(2r)|` via `Real.log_lt_log` and `abs_le_max_abs_abs`.
- **Hypotheses**: None (existential over `C`).
- **Uses from project**: [] (mathlib: `tendsto_sub_one_mul_dedekindZeta_nhdsGT`, `dedekindZeta_residue`, `dedekindZeta_residue_pos`)
- **Used by**: `log_minus_bounded_le_primeIdealZetaSum`, `primeIdealZetaSum_le_log_plus_bounded`.
- **Visibility**: public · **Lines**: 544–570 (proof ~20 lines) · **Notes**: &gt;10-line proof; cites `tendsto_sub_one_mul_dedekindZeta_nhdsGT`, `Real.log_lt_log`, `abs_le_max_abs_abs`.

### `theorem log_minus_bounded_le_primeIdealZetaSum`
- **Type**: `∃ C : ℝ, ∀ᶠ s in 𝓝[&gt;] 1, Real.log (1 / (s - 1)) - C ≤ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s` (with `K` explicit)
- **What**: Lower bound `log(1/(s-1)) - C ≤ Σ_𝔭 N𝔭^{-s}` near `s = 1` (Sharifi 7.1.12).
- **How**: Combine the two `O(1)` bounds `logDedekindZeta_sub_primeIdealZetaSum_bounded` and `logDedekindZeta_sub_log_inv_sub_one_bounded` with constant `C₁ + C₂`; chain the absolute-value bounds (`abs_le.mp`) by `linarith`.
- **Hypotheses**: None (existential over `C`).
- **Uses from project**: [`logDedekindZeta_sub_primeIdealZetaSum_bounded`, `logDedekindZeta_sub_log_inv_sub_one_bounded`]
- **Used by**: `primeIdealZetaSum_univ_tendsto_log`.
- **Visibility**: public · **Lines**: 572–581 (proof ~4 lines) · **Notes**: —

### `theorem primeIdealZetaSum_le_log_plus_bounded`
- **Type**: `∃ C : ℝ, ∀ᶠ s in 𝓝[&gt;] 1, primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s ≤ Real.log (1 / (s - 1)) + C` (with `K` explicit)
- **What**: Upper bound `Σ_𝔭 N𝔭^{-s} ≤ log(1/(s-1)) + C'` near `s = 1` (Sharifi 7.1.12).
- **How**: Same two `O(1)` bounds as the lower-bound lemma, combined with `C₁ + C₂` and `linarith` on the `abs_le` facts (opposite orientation).
- **Hypotheses**: None (existential over `C`).
- **Uses from project**: [`logDedekindZeta_sub_primeIdealZetaSum_bounded`, `logDedekindZeta_sub_log_inv_sub_one_bounded`]
- **Used by**: `primeIdealZetaSum_univ_tendsto_log`.
- **Visibility**: public · **Lines**: 583–592 (proof ~4 lines) · **Notes**: —

### `theorem primeIdealZetaSum_univ_tendsto_log`
- **Type**: `Tendsto (fun s : ℝ ↦ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s / Real.log (1 / (s - 1))) (𝓝[&gt;] 1) (𝓝 1)` (with `K` explicit)
- **What**: Sharifi 7.1.12: the denominator `Σ_𝔭 N𝔭^{-s}` is asymptotic to `log(1/(s-1))` as `s ↓ 1` (ratio → 1).
- **How**: Apply the imported squeeze `tendsto_ratio_one_of_log_pm_bounded` to the two-sided bounds `primeIdealZetaSum_le_log_plus_bounded` and `log_minus_bounded_le_primeIdealZetaSum`.
- **Hypotheses**: None.
- **Uses from project**: [`primeIdealZetaSum_le_log_plus_bounded`, `log_minus_bounded_le_primeIdealZetaSum`; imported helper `tendsto_ratio_one_of_log_pm_bounded` from `ForMathlib/LogOneDivSubOne.lean`]
- **Used by**: `primeIdealZetaSum_univ_tendsto_atTop`.
- **Visibility**: public · **Lines**: 594–607 (proof: term application ~4 lines) · **Notes**: the file's headline analytic result (Sharifi 7.1.12).

### `theorem primeIdealZetaSum_univ_tendsto_atTop`
- **Type**: `Tendsto (primeIdealZetaSum (univ : Set (Ideal (𝓞 K)))) (𝓝[&gt;] 1) atTop` (with `K` explicit)
- **What**: The full prime-ideal zeta sum diverges to `+∞` as `s ↓ 1`.
- **How**: Since the ratio → 1 (`primeIdealZetaSum_univ_tendsto_log`) and `log(1/(s-1)) → +∞` (`tendsto_log_one_div_sub_one_atTop`), eventually `Σ ≥ (1/2)·log(1/(s-1)) → +∞`; conclude by `tendsto_atTop_mono'` against `hL.const_mul_atTop`, using `lt_div_iff₀` to extract the eventual lower bound.
- **Hypotheses**: None.
- **Uses from project**: [`primeIdealZetaSum_univ_tendsto_log`; imported helper `tendsto_log_one_div_sub_one_atTop` from `ForMathlib/LogOneDivSubOne.lean`]
- **Used by**: `hasDirichletDensity_of_finite`, `tendsto_primeIdealZetaSum_div_univ_zero_of_le_const`, `hasDirichletDensity_univ`.
- **Visibility**: public · **Lines**: 609–619 (proof ~6 lines) · **Notes**: cites `tendsto_atTop_mono'`, `const_mul_atTop`.

### `theorem primeIdealZetaSum_le_card_of_finite`
- **Type**: `(hS : S.Finite) {s : ℝ} (hs : 0 &lt; s) : primeIdealZetaSum S s ≤ Nat.card {𝔭 // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}` (with `K` explicit)
- **What**: For finite `S` and `s &gt; 0`, the partial sum is bounded by the count of qualifying primes.
- **What/How**: The qualifying subtype is finite (`hS.subset … |&gt;.to_subtype`, then `Fintype.ofFinite`), so the `tsum` is a finite sum (`tsum_fintype`); bound each term `N𝔭^{-s} ≤ 1` by `Real.rpow_le_one_of_one_le_of_nonpos` (`N𝔭 ≥ 1`, exponent `≤ 0`) and sum the constant `1` via `Finset.sum_const`.
- **Hypotheses**: `S` finite, `0 &lt; s`.
- **Uses from project**: [`primeIdealZetaSum_def`]
- **Used by**: `hasDirichletDensity_of_finite`.
- **Visibility**: public · **Lines**: 621–639 (proof ~14 lines) · **Notes**: &gt;10-line proof; cites `tsum_fintype`, `Real.rpow_le_one_of_one_le_of_nonpos`.

### `theorem hasDirichletDensity_of_finite`
- **Type**: `(hS : S.Finite) : HasDirichletDensity S 0` (with `K` explicit)
- **What**: A finite set of primes has Dirichlet density `0` (Sharifi 7.1.13).
- **How**: Squeeze the ratio between `0` and `|qualifying primes|/Σ_univ`: numerator bounded by `primeIdealZetaSum_le_card_of_finite`, denominator `→ +∞` (`primeIdealZetaSum_univ_tendsto_atTop`) so the upper bound → 0 (`tendsto_const_nhds.div_atTop`); finish with `tendsto_of_tendsto_of_tendsto_of_le_of_le'`.
- **Hypotheses**: `S` finite.
- **Uses from project**: [`primeIdealZetaSum_univ_tendsto_atTop`, `primeIdealZetaSum_def`, `primeIdealZetaSum_le_card_of_finite`, `HasDirichletDensity`]
- **Used by**: unused in file.
- **Visibility**: public · **Lines**: 641–661 (proof ~16 lines) · **Notes**: &gt;10-line proof; cites `tendsto_of_tendsto_of_tendsto_of_le_of_le'`, `div_atTop`.

### `theorem tendsto_primeIdealZetaSum_div_univ_zero_of_le_const`
- **Type**: `(U : Set (Ideal (𝓞 K))) (C : ℝ) (hbd : ∀ᶠ s in 𝓝[&gt;] 1, primeIdealZetaSum U s ≤ C) : Tendsto (fun s ↦ primeIdealZetaSum U s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s) (𝓝[&gt;] 1) (𝓝 0)` (with `K` explicit)
- **What**: General zero-density engine: if the numerator partial sum over `U` is eventually bounded by a constant `C`, the density ratio → 0.
- **How**: Same squeeze as the finite case but with the constant `C`: bound the ratio between `0` and `C/Σ_univ`, the latter → 0 since `Σ_univ → +∞` (`primeIdealZetaSum_univ_tendsto_atTop`, `div_atTop`); `tendsto_of_tendsto_of_tendsto_of_le_of_le'`.
- **Hypotheses**: numerator eventually `≤ C` near `s = 1`.
- **Uses from project**: [`primeIdealZetaSum_univ_tendsto_atTop`, `primeIdealZetaSum_nonneg`]
- **Used by**: unused in file.
- **Visibility**: public · **Lines**: 663–681 (proof ~14 lines) · **Notes**: &gt;10-line proof; docstring notes it is the shared engine behind `hasDirichletDensity_of_finite` and the degree-≥2/ramified tail bound in the Chebotarev fixed-field reduction.

### `theorem hasDirichletDensity_univ`
- **Type**: `HasDirichletDensity (univ : Set (Ideal (𝓞 K))) 1` (with `K` explicit)
- **What**: The set of all nonzero prime ideals has Dirichlet density `1`.
- **How**: The ratio `Σ_univ/Σ_univ` is eventually `1` because the denominator is eventually nonzero (it `→ +∞`, `primeIdealZetaSum_univ_tendsto_atTop` + `eventually_gt_atTop`); rewrite to `tendsto_const_nhds` via `Tendsto.congr'` and `div_self`.
- **Hypotheses**: None.
- **Uses from project**: [`primeIdealZetaSum_univ_tendsto_atTop`, `HasDirichletDensity`]
- **Used by**: unused in file.
- **Visibility**: public · **Lines**: 683–690 (proof ~5 lines) · **Notes**: —

---

### File Summary
- **Total declarations: 36** — 4 defs (`primeIdealZetaSum`, `HasDirichletDensity`, `HasUpperDirichletDensity`, `HasLowerDirichletDensity`), 32 lemmas/theorems, 0 instances/structures/classes/abbrevs.
- **Key API (used by 3+ within this file)**:
  - `primeIdealZetaSum_def` (used by 10)
  - `primeIdealZetaSum` (used by all; foundational def)
  - `HasDirichletDensity` (def, used by 7)
  - `primeIdealZetaSum_univ_tendsto_atTop` (used by 4)
  - `summable_prime2_absNorm_rpow` (used by 4)
  - `two_le_absNorm_of_prime` (used by 4)
  - `primeIdealZetaSum_nonneg` (used by 4)
  - (just below the bar — used by exactly 2 — `summable_prime_absNorm_rpow`, `primeIdealZetaSum_union_of_disjoint`, `primeIdealHigherTail_term_le`, `one_sub_absNorm_rpow_pos`, `summable_neg_log_one_sub_absNorm_rpow`, `logDedekindZeta_sub_primeIdealZetaSum_bounded`, `logDedekindZeta_sub_log_inv_sub_one_bounded`.)
- **Unused declarations (within this file — these are the public API consumed by other modules `Frobenius`/`Cyclotomic`/`Abelian`/`Main`)**: `hasDirichletDensity_empty`, `primeIdealZetaSum_le_of_subset`, `primeIdealZetaSum_biUnion_of_pairwiseDisjoint`, `primeIdealZetaSum_eq_univ_of_forall_prime_mem`, `HasDirichletDensity.of_upper_eq_lower`, `HasDirichletDensity.hasUpper`, `HasDirichletDensity.hasLower`, `HasDirichletDensity.union_of_disjoint`, `HasLowerDirichletDensity.mono`, `primeIdealZetaSum_univ_tendsto_log`, `hasDirichletDensity_of_finite`, `tendsto_primeIdealZetaSum_div_univ_zero_of_le_const`, `hasDirichletDensity_univ`. (All `private` lemmas are used internally; none are dead.)
- **Declarations with `sorry`**: none.
- **Declarations with `set_option`**: none.
- **Proofs &gt;30 lines** (3): `log_dedekindZeta_re_eq_tsum_neg_log_one_sub` (~40), `abs_tsum_neg_log_one_sub_sub_rpow_le` (~36), `primeIdealZetaHigherTail_bounded` (~29 — counted here as the largest of the "near-30" group; strictly just under 30). Additional substantial (&gt;20-line) proofs: `primeIdealZetaSum_union_of_disjoint` (~25), `primeIdealHigherTail_term_le` (~22), `logDedekindZeta_sub_log_inv_sub_one_bounded` (~20).

Note on conventions: the file fully respects the project's `≤`-not-`≥` rule in all Lean statements (the only `≥`/`k≥2` occurrences are inside docstrings, which is allowed); `K` is implicit in the `S`-parametrised section (recoverable from `S`) and explicitly re-enabled via `variable (K)` at line 316 for the universal-sum analytic theorems, exactly as the CLAUDE.md argument convention prescribes.</result>
<usage><subagent_tokens>55191</subagent_tokens><tool_uses>5</tool_uses><duration_ms>209206</duration_ms></usage>
</task-notification>