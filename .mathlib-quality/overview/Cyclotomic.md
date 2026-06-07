# Inventory: `CebotarevDensity/Cyclotomic.lean` (1034 lines)

**File-level setup** (lines 1–51): `module`; public imports of `CebotarevDensity.ZetaProduct`, `CebotarevDensity.CyclotomicNormResidue`, and four Mathlib modules (`GroupTheory.FiniteAbelian.Duality`, `NumberTheory.Cyclotomic.Basic`, `NumberTheory.NumberField.Cyclotomic.Basic`, `NumberTheory.NumberField.Ideal.Basic`). `@[expose] public section`; `noncomputable section`; `open NumberField Filter Topology`; `namespace Chebotarev`. File-level `variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]` (line 50) — used only by the two final theorems; every intermediate declaration re-declares `K L` locally with its own typeclass stack.

---

### `theorem log_artinLSeries_asymp_character_sum`
- **Type**: For abelian `Gal(L/K)` and `χ : galoisCharacter K L`, `∃ C : ℝ`, eventually as `s ↓ 1` the norm of the twisted unramified-prime tsum `∑'_𝔭 χ(Frob 𝔭).out · N𝔭^{-s}` is `≤ C·log(1/(s-1)) + C`.
- **What**: The twisted prime sum (over unramified primes) is bounded by a constant multiple of `log(1/(s-1))` near `s=1` — the "log L(χ,s) ~ Σ_𝔭 χ(𝔭) N𝔭^{-s}" upper-bound packaging (Sharifi 7.2.1 step ii).
- **How**: Each `‖χ(c.out)‖ = 1` (root of unity: `isOfFinOrder_of_finite` + `Complex.norm_eq_one_of_pow_eq_one`). Pulls `C` from `primeIdealZetaSum_le_log_plus_bounded`; sets the answer `max C 1`. Each summand norm equals `N𝔭^{-s}` (`norm_mul`, `Complex.norm_natCast_cpow_of_pos`). Reindexes the bare unramified tsum to `primeIdealZetaSum U s` via a plain-lambda injection (`hinj` injective + `hsurj` surjective, `Injective.tsum_eq`), bounds it by `primeIdealZetaSum univ s` (`primeIdealZetaSum_le_of_subset`), then chains `norm_tsum_le_tsum_norm` → `tsum_congr` → `hC` and finishes with `nlinarith` using `log ≥ 0` near 1.
- **Hypotheses**: `K,L` number fields, Galois, finite-dimensional, `IsMulCommutative Gal(L/K)`; `χ` a Galois character.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `UnramifiedIn.ne_bot`, `primeIdealZetaSum_le_log_plus_bounded`, `summable_prime_absNorm_rpow`, `primeIdealZetaSum_def`, `primeIdealZetaSum_le_of_subset`.
- **Used by**: unused in file (it is the standalone "step (ii)" packaging; the live χ≠1 bound goes through `artinLSeries_prime_sum_bounded_of_ne_one`). Referenced only in the docstring of `primeIdealZetaSum_frobeniusFibre_asymp`.
- **Visibility**: public (`theorem`).
- **Lines**: 75–161.
- **Notes**: &gt;30 lines (~87).

### `theorem sum_galoisCharacter_eq_card_or_zero`
- **Type**: For finite commutative `G` with `Fintype (G →* ℂˣ)` and `g : G`, `∑_χ (χ g : ℂ) = if g = 1 then (Nat.card G : ℂ) else 0`.
- **What**: Column orthogonality of the characters of a finite abelian group valued in `ℂˣ`.
- **How**: Equips `G` with `CommGroup`; gets `NeZero (Monoid.exponent G)` and `HasEnoughRootsOfUnity ℂ (exponent G)`. Case `g=1`: `map_one`, `Finset.sum_const`, and `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity` give `Nat.card G`. Case `g≠1`: pick `ψ` with `ψ g ≠ 1` (`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`); reindexing the sum by left-multiplication `Equiv.mulLeft ψ` shows `(ψ g)·S = S`, so `((ψ g)-1)·S = 0`; since `(ψ g)-1 ≠ 0`, `S = 0` (`mul_eq_zero` + `resolve_left`).
- **Hypotheses**: `G` a finite commutative group with a fintype of `ℂˣ`-characters; `g ∈ G`. (`ℂ` algebraically closed ⇒ enough roots of unity.)
- **Uses from project**: [] (pure Mathlib group theory).
- **Used by**: `character_orthogonality_cyclotomic_eq`, `character_orthogonality_cyclotomic_ne`.
- **Visibility**: private (`open scoped Classical in`).
- **Lines**: 163–188.
- **Notes**: `open scoped Classical in`. Only group-theoretic input to both orthogonality relations.

### `theorem character_orthogonality_cyclotomic_eq`
- **Type**: matching case — under `frobeniusClass K L 𝔭 = ConjClasses.mk σ`, `∑_χ (χ σ)·(χ (Frob 𝔭).out)⁻¹ = (Nat.card Gal(L/K) : ℂ)`.
- **What**: Sharifi 7.2.1 step (iii), Frobenius equals σ ⇒ character sum = `|G|`.
- **How**: `IsCyclotomicExtension.isMulCommutative` gives commutativity. Rewrites each summand `(χσ)(χτ)⁻¹ = χ(στ⁻¹)` (`map_mul`, `map_inv`). From `ConjClasses.mk_eq_mk_iff_isConj` plus commutativity (`mul_comm'`, `mul_right_cancel`), `σ·τ⁻¹ = 1`. Then `sum_galoisCharacter_eq_card_or_zero` with `if_pos`.
- **Hypotheses**: cyclotomic extension `IsCyclotomicExtension {m} K L`, `NeZero m`, finite-dim, `Fintype (galoisCharacter K L)`, `σ`, prime `𝔭` unramified, Frobenius = `mk σ`.
- **Uses from project**: `frobeniusClass`, `galoisCharacter`, `sum_galoisCharacter_eq_card_or_zero`.
- **Used by**: `sum_charTwist_eq`.
- **Visibility**: public (`theorem`).
- **Lines**: 190–213.
- **Notes**: —

### `theorem character_orthogonality_cyclotomic_ne`
- **Type**: non-matching case — under `frobeniusClass K L 𝔭 ≠ ConjClasses.mk σ`, `∑_χ (χ σ)·(χ (Frob 𝔭).out)⁻¹ = 0`.
- **What**: Sharifi 7.2.1 step (iii), Frobenius ≠ σ ⇒ character sum vanishes.
- **How**: Same summand rewrite `χ(στ⁻¹)`; here `σ·τ⁻¹ ≠ 1` (else `mk σ = mk τ = frobeniusClass`, contradiction via `mul_inv_eq_one`), so `sum_galoisCharacter_eq_card_or_zero` with `if_neg`.
- **Hypotheses**: as in `_eq` but with the strict-inequality hypothesis `frobeniusClass K L 𝔭 ≠ mk σ`.
- **Uses from project**: `frobeniusClass`, `galoisCharacter`, `sum_galoisCharacter_eq_card_or_zero`.
- **Used by**: `sum_charTwist_ne`.
- **Visibility**: public (`theorem`).
- **Lines**: 215–234.
- **Notes**: —

### `theorem differentiableAt_logSum_of_two_le`
- **Type**: abstract over index `ι`, `N : ι → ℕ` (`2 ≤ N i`), `c : ι → ℂ` (`‖c i‖ = 1`), with `Σ_i N i^{-r}` summable for all `r&gt;1`; concludes `DifferentiableAt ℝ (fun s =&gt; Σ'_i -Log(1 - c i·N i^{-s})) s₀` for `s₀ &gt; 1`.
- **What**: The log-sum `g(s) = Σ_i -Log(1 - c_i N_i^{-s})` is differentiable at each `s₀ &gt; 1`.
- **How**: Works on `t = Ioi(1+ε)`, `ε=(s₀-1)/2` (open, preconnected). Per-term derivative `g'_i` via `Complex.hasStrictDerivAt_const_cpow`, `hasDerivAt_neg'`, `.const_mul/.const_sub`, `HasDerivAt.clog` (needs slit-plane: `Complex.mem_slitPlane_of_norm_lt_one`, weights `≤ 1/2` from `2 ≤ N_i^s`), `.comp_ofReal`. Dominating summand `u_i = 2·log N_i·N_i^{-(1+ε)}` is summable via `Real.log_le_rpow_div` reducing to `Σ N_i^{-((1+ε)-ε/2)}`; derivative bound `‖g'_i‖ ≤ u_i` by `nlinarith`. Base summability `g(s₀)` via `Complex.norm_log_one_sub_inv_sub_self_le` (`‖-Log(1-w)‖ ≤ 2‖w‖`). Concludes with `hasDerivAt_tsum_of_isPreconnected … |&gt;.differentiableAt`.
- **Hypotheses**: `2 ≤ N i` all i; `‖c i‖ = 1` all i; `Σ_i N i^{-r}` summable for every `r &gt; 1`; `1 &lt; s₀`.
- **Uses from project**: [] (pure complex analysis, abstract).
- **Used by**: `artinLSeries_prime_sum_bounded_of_analytic_extension` (via `hGderiv`).
- **Visibility**: private (`theorem`).
- **Lines**: 248–361.
- **Notes**: &gt;30 lines (~114) — the longest declaration in the file. Key lemmas: `hasDerivAt_tsum_of_isPreconnected`, `HasDerivAt.clog`, `Complex.hasStrictDerivAt_const_cpow`, `Real.log_le_rpow_div`, `Complex.norm_log_one_sub_inv_sub_self_le`.

### `theorem cexp_logSum_eq_tprod`
- **Type**: abstract `w : ι → ℂ`, `Summable w`, `1 - w i ∈ slitPlane` all i; then `exp(Σ'_i -Log(1 - w i)) = ∏'_i (1 - w i)⁻¹`.
- **What**: Exponentiating the log-sum recovers the Euler product `∏ (1-w_i)⁻¹`.
- **How**: Set `f i = (1-w i)⁻¹` (nonzero by `Complex.slitPlane_ne_zero`); `Log(f i) = -Log(1-w i)` via `Complex.log_inv` (+ `slitPlane_arg_ne_pi`). `Σ Log(f i)` summable from `Summable.clog_one_sub`. Apply `Complex.cexp_tsum_eq_tprod`.
- **Hypotheses**: `w` summable; `1 - w i` on the slit plane for all i.
- **Uses from project**: [].
- **Used by**: `artinLSeries_prime_sum_bounded_of_analytic_extension` (via `hexpeq`).
- **Visibility**: private (`theorem`).
- **Lines**: 366–376.
- **Notes**: —. Core lemma `Complex.cexp_tsum_eq_tprod`.

### `theorem hasDerivAt_logSum_eq_logDeriv`
- **Type**: given `HasDerivAt G G' s₀`, `Lf` differentiable at `↑s₀`, `exp(G s) = Lf ↑s` for all `s&gt;1`, `Lf ↑s₀ ≠ 0`; concludes `G' = deriv Lf ↑s₀ / Lf ↑s₀`.
- **What**: The log-sum's derivative equals the logarithmic derivative `Lf'/Lf` of any `Lf` agreeing with `exp G` near `s₀`.
- **How**: `HasDerivAt.cexp` gives `(exp∘G)' = G'·exp(G s₀)`; `Lf∘ofReal` has derivative `deriv Lf ↑s₀` (`.comp_ofReal`). The two functions agree eventually (`Ioi_mem_nhds`), so `HasDerivAt.unique` + `congr_of_eventuallyEq` give `G'·exp(G s₀) = deriv Lf ↑s₀`; substituting `exp(G s₀)=Lf ↑s₀` and `field_simp`/`linear_combination` finishes. Single-valued derivative sidesteps the branch ambiguity of `log Lf`.
- **Hypotheses**: as above; `1 &lt; s₀`.
- **Uses from project**: [].
- **Used by**: `artinLSeries_prime_sum_bounded_of_analytic_extension` (via `hGderiv`).
- **Visibility**: private (`theorem`).
- **Lines**: 382–397.
- **Notes**: —. Key: `HasDerivAt.cexp`, `HasDerivAt.unique`, `HasDerivAt.comp_ofReal`.

### `theorem norm_bounded_nhdsGT_of_deriv_continuousOn`
- **Type**: given `HasDerivAt G (F s) s` for all `s&gt;1` and `ContinuousOn F (Icc 1 2)`; concludes `∃ C, ∀ᶠ s↓1, ‖G s‖ ≤ C`.
- **What**: Mean-value packaging: a function differentiable on `(1,∞)` with continuous derivative on `[1,2]` has `‖G‖` bounded as `s↓1`.
- **How**: `M` bounds `‖F‖` on `[1,2]` (`isCompact_Icc.exists_bound_of_continuousOn`). Answer `‖G 2‖ + M`. On `Icc s 2 ⊆ Icc 1 2`, `Convex.norm_image_sub_le_of_norm_deriv_le` gives `‖G s − G 2‖ ≤ M·‖s−2‖ ≤ M`; triangle inequality `‖G s‖ ≤ ‖G s − G 2‖ + ‖G 2‖` closes it.
- **Hypotheses**: derivative `F` everywhere on `(1,∞)`, continuous on the compact `[1,2]`.
- **Uses from project**: [].
- **Used by**: `artinLSeries_prime_sum_bounded_of_analytic_extension` (via `hCg`).
- **Visibility**: private (`theorem`).
- **Lines**: 402–423.
- **Notes**: —. Key: `Convex.norm_image_sub_le_of_norm_deriv_le`, `IsCompact.exists_bound_of_continuousOn`.

### `def twistedPrimeSum`
- **Type**: `(χ : galoisCharacter K L) (s : ℝ) : ℂ` := `∑'_{𝔭 prime, unram} χ(Frob 𝔭).out · N𝔭^{-(s:ℂ)}`.
- **What**: The twisted prime sum `Σ_𝔭 χ(Frob 𝔭) N𝔭^{-s}` over unramified primes, as a complex function of `s`.
- **How**: Definitional — a `tsum` over the unramified-prime subtype. (No proof.)
- **Hypotheses**: `K,L` number fields, Galois; `χ`, `s`.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`.
- **Used by**: `card_mul_frobeniusFibre_eq`, `primeIdealZetaSum_frobeniusFibre_asymp` (and its docstring notes χ=1 value vs χ≠1 boundedness).
- **Visibility**: private (`noncomputable def`).
- **Lines**: 428–432.
- **Notes**: real `def` with content (no `sorry`), per project no-placeholder rule.

### `theorem summable_twistedPrimeSum`
- **Type**: for `1 &lt; s`, the family `𝔭 ↦ χ(Frob 𝔭).out · N𝔭^{-(s:ℂ)}` (unramified primes) is `Summable`.
- **What**: The twisted-prime family is summable for `Re s &gt; 1`.
- **How**: Reindex `Σ N𝔭^{-s}` to the unramified subtype via the plain-lambda injection `hinj` (`summable_prime_absNorm_rpow … |&gt;.comp_injective`). Each summand norm `= N𝔭^{-s}` (root-of-unity `‖χ(c.out)‖=1` + `Complex.norm_natCast_cpow_of_pos`); `Summable.of_norm` of the congruence.
- **Hypotheses**: finite-dim; `1 &lt; s`.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `UnramifiedIn.ne_bot`, `summable_prime_absNorm_rpow`.
- **Used by**: `artinLSeries_prime_sum_bounded_of_analytic_extension` (`hsumw`), `card_mul_frobeniusFibre_eq` (via `hinterchange`).
- **Visibility**: private (`theorem`).
- **Lines**: 436–463.
- **Notes**: &gt;30 lines (~28; borderline). Duplicates the `hnorm1`/`hnormterm`/`hinj` block of `log_artinLSeries_asymp_character_sum`.

### `theorem two_le_absNorm_prime`
- **Type**: for prime `𝔭 ≠ ⊥`, `2 ≤ Ideal.absNorm 𝔭`.
- **What**: A nonzero prime ideal has absolute norm `≥ 2`.
- **How**: `absNorm 𝔭 ≠ 0` (`absNorm_eq_zero_iff`, `𝔭 ≠ ⊥`) and `≠ 1` (`absNorm_eq_one_iff`, `𝔭.ne_top`); `lia` (omega-like) concludes `≥ 2`.
- **Hypotheses**: `𝔭.IsPrime`, `𝔭 ≠ ⊥`.
- **Uses from project**: [].
- **Used by**: `artinLSeries_prime_sum_bounded_of_analytic_extension` (via `hN2`).
- **Visibility**: private (`theorem`).
- **Lines**: 466–471.
- **Notes**: —. Uses `Ideal.absNorm_eq_zero_iff`, `Ideal.absNorm_eq_one_iff`.

### `theorem artinLSeries_prime_sum_bounded_of_analytic_extension`
- **Type**: given the analytic extension `Lf` of `L(χ,·)` (analytic on `{re &gt; 1 − [K:ℚ]⁻¹}`, agreeing with the ideal Dirichlet series on `re&gt;1`) with `Lf 1 ≠ 0` and `χ ≠ 1`; concludes `∃ C, ∀ᶠ s↓1, ‖Σ'_𝔭 χ(Frob 𝔭).out·N𝔭^{-s}‖ ≤ C`.
- **What**: The substantive complex-analytic bridge — the twisted prime sum stays bounded as `s↓1` given the analytic extension that is nonzero at 1.
- **How**: Writes `P_χ(s) = G(s) − R_χ(s)` with `G(s) = Σ_𝔭 -Log(1 − c_𝔭 N𝔭^{-s})` (`c_𝔭 = χ(Frob).out`, `‖c‖=1`, `N_𝔭 ≥ 2` via `two_le_absNorm_prime`) and `R_χ` the prime-power tail. (1) `exp(G s) = Lf ↑s` on `re&gt;1` via `exists_artinLSeries_eulerProduct_abelian` + `cexp_logSum_eq_tprod` + `hLf_eq`. (2) `Lf ↑s ≠ 0` for `s≥1` (at 1: `hLf0`; for `s&gt;1`: `exp ≠ 0`). (3) `F = Lf'/Lf` continuous on `[1,2]` from `AnalyticOnNhd` (open domain via `isOpen_lt`, `ContinuousOn.div`). (4) `HasDerivAt G (F s) s` on `(1,∞)` via `differentiableAt_logSum_of_two_le` + `hasDerivAt_logSum_eq_logDeriv`. (5) `‖G s‖` bounded via `norm_bounded_nhdsGT_of_deriv_continuousOn`. (6) `‖R_χ s‖ ≤ Σ_𝔭 N𝔭^{-2}` uniformly via per-term `‖-Log(1-w)-w‖ ≤ N𝔭^{-2}` (`Complex.norm_log_one_sub_inv_sub_self_le`, `‖w‖²=N^{-2s} ≤ N^{-2}`). Assemble with `tsum_sub`, `norm_sub_le`, `linarith`; answer `Cg + MR`.
- **Hypotheses**: finite-dim, `IsMulCommutative Gal(L/K)`, `χ ≠ 1`; `Lf` analytic on `{re &gt; 1−[K:ℚ]⁻¹}`, equals the ideal Dirichlet series of `galoisCharacterOnIdeal` on `re&gt;1`, `Lf 1 ≠ 0`.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `UnramifiedIn.ne_bot`, `galoisCharacterOnIdeal`, `two_le_absNorm_prime`, `summable_prime_absNorm_rpow`, `summable_twistedPrimeSum`, `cexp_logSum_eq_tprod`, `differentiableAt_logSum_of_two_le`, `hasDerivAt_logSum_eq_logDeriv`, `norm_bounded_nhdsGT_of_deriv_continuousOn`, `exists_artinLSeries_eulerProduct_abelian`.
- **Used by**: `artinLSeries_prime_sum_bounded_of_ne_one`.
- **Visibility**: private (`theorem`).
- **Lines**: 486–654.
- **Notes**: &gt;30 lines (~169); `classical`. The χ≠1 analytic core. Key Mathlib: `IsOpen.analyticOn_iff_analyticOnNhd`, `AnalyticOnNhd.deriv`, `Complex.norm_log_one_sub_inv_sub_self_le`.

### `theorem artinLSeries_prime_sum_bounded_of_ne_one`
- **Type**: for cyclotomic `L=K(μ_m)` (`m % 4 ≠ 2`) and `χ ≠ 1`; `∃ C, ∀ᶠ s↓1, ‖Σ'_𝔭 χ(Frob 𝔭).out·N𝔭^{-s}‖ ≤ C`.
- **What**: Analytic input of the cyclotomic case (Dirichlet's argument): the χ≠1 twisted prime sum is bounded near `s=1`.
- **How**: Pulls the analytic extension `(Lf, hLf_an, hLf_eq)` from `artinLSeries_analytic_extension`, notes `Lf 1 ≠ 0` via `artinLSeries_one_ne_zero`, and feeds both into `artinLSeries_prime_sum_bounded_of_analytic_extension`.
- **Hypotheses**: `IsCyclotomicExtension {m} K L`, `NeZero m`, finite-dim, `IsMulCommutative Gal(L/K)`, `m % 4 ≠ 2`, `χ ≠ 1`.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `artinLSeries_analytic_extension`, `artinLSeries_one_ne_zero`, `artinLSeries_prime_sum_bounded_of_analytic_extension`.
- **Used by**: `primeIdealZetaSum_frobeniusFibre_asymp` (via `hterm`).
- **Visibility**: private (`theorem`).
- **Lines**: 663–672.
- **Notes**: —. The `m % 4 ≠ 2` hypothesis threads from here up to `chebotarev_cyclotomic` (Stevenhagen-Lenstra: `μ_m` cyclotomic discriminant condition).

### `theorem sum_charTwist_eq`
- **Type**: matching case — under `frobeniusClass K L 𝔭 = mk σ`, `∑_χ (χ σ)⁻¹·χ(Frob 𝔭).out = (Nat.card Gal(L/K) : ℂ)`.
- **What**: Character-twist orthogonality collapse (Frobenius = σ ⇒ `|G|`), the `(χσ)⁻¹` form.
- **How**: Reindex `character_orthogonality_cyclotomic_eq` along `χ ↦ χ⁻¹` (`Equiv.inv (galoisCharacter K L)`, `Equiv.sum_comp`); `Finset.sum_congr` + units-inverse rewrites (`MonoidHom.inv_apply`, `Units.val_inv_eq_inv_val`, `inv_inv`, `mul_comm`) match the summand.
- **Hypotheses**: cyclotomic, `NeZero m`, finite-dim, `Fintype (galoisCharacter K L)`, `σ`, prime `𝔭` unramified, Frobenius = `mk σ`.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `character_orthogonality_cyclotomic_eq`.
- **Used by**: `card_mul_frobeniusFibre_eq` (via `hcollapse`).
- **Visibility**: private (`theorem`).
- **Lines**: 689–701.
- **Notes**: —.

### `theorem sum_charTwist_ne`
- **Type**: non-matching case — under `frobeniusClass K L 𝔭 ≠ mk σ`, `∑_χ (χ σ)⁻¹·χ(Frob 𝔭).out = 0`.
- **What**: Character-twist orthogonality collapse (Frobenius ≠ σ ⇒ 0), the `(χσ)⁻¹` form.
- **How**: Same `χ ↦ χ⁻¹` reindex of `character_orthogonality_cyclotomic_ne`; identical summand rewrite chain.
- **Hypotheses**: as `sum_charTwist_eq` but with `frobeniusClass K L 𝔭 ≠ mk σ`.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `character_orthogonality_cyclotomic_ne`.
- **Used by**: `card_mul_frobeniusFibre_eq` (via `hcollapse`).
- **Visibility**: private (`theorem`).
- **Lines**: 706–718.
- **Notes**: —.

### `theorem primeIdealZetaSum_unramified_div_log_tendsto_one`
- **Type**: `Tendsto (fun s =&gt; primeIdealZetaSum {𝔭 prime ∧ unram in L} s / log(1/(s-1))) (𝓝[&gt;]1) (𝓝 1)`.
- **What**: The bare unramified-prime sum is asymptotic to `log(1/(s-1))` (differs from the universal prime sum only by finitely many ramified primes).
- **How**: Split nonzero primes as `U` (unramified) ⊔ `R` (ramified), disjoint and covering (`hdisj`, `hcover`). `R` finite (`finite_ramifiedIn`), so `primeIdealZetaSum R s ≤ |R|` (`primeIdealZetaSum_le_card_of_finite`); hence `R s/log → 0` (`squeeze_zero_norm'`, `Tendsto.div_atTop`, `tendsto_log_one_div_sub_one_atTop`). Then `U s/log = univ s/log − R s/log → 1−0 = 1` via `primeIdealZetaSum_univ_tendsto_log`, recombining the additivity `U + R = univ` (`primeIdealZetaSum_union_of_disjoint`, `primeIdealZetaSum_eq_univ_of_forall_prime_mem`) with `Tendsto.congr'`.
- **Hypotheses**: finite-dim.
- **Uses from project**: `UnramifiedIn`, `primeIdealZetaSum`, `finite_ramifiedIn`, `primeIdealZetaSum_le_card_of_finite`, `primeIdealZetaSum_def`, `primeIdealZetaSum_union_of_disjoint`, `primeIdealZetaSum_eq_univ_of_forall_prime_mem`, `primeIdealZetaSum_univ_tendsto_log`, `tendsto_log_one_div_sub_one_atTop`.
- **Used by**: `primeIdealZetaSum_frobeniusFibre_asymp` (via `hlim`).
- **Visibility**: private (`theorem`).
- **Lines**: 723–769.
- **Notes**: &gt;30 lines (~47). Key: `squeeze_zero_norm'`, `Filter.Tendsto.div_atTop`.

### `theorem card_mul_frobeniusFibre_eq`
- **Type**: for `1 &lt; s`, `(Nat.card Gal(L/K) : ℝ)·primeIdealZetaSum Sσ s = primeIdealZetaSum U s + (∑_{χ≠1} (χσ)⁻¹·twistedPrimeSum χ s).re`, where `Sσ = {𝔭 prime, unram, Frob = mk σ}`, `U = {𝔭 prime, unram}`.
- **What**: The orthogonality-collapsed master identity (real form): `|G|·P_σ(s) = (U-prime sum) + Re(χ≠1 remainder)`.
- **How**: (a) INTERCHANGE finite `∑_χ` with prime `∑'_𝔭`: `tsum_mul_left`, `Summable.tsum_finsetSum`, `Finset.sum_mul`. (b) COLLAPSE inner sum by `sum_charTwist_eq`/`_ne` into `if Frob=mkσ then |G|·N𝔭^{-s} else 0`. (c) Identify the fibre tsum with `primeIdealZetaSum Sσ s` via injection `hfinj` (`Injective.tsum_eq`, `if_pos`), giving `M = |G|·(P_σ : ℂ)` (`Complex.ofReal_tsum`, `tsum_mul_left`). (d) Split off `χ=1` whose twist is `(U-sum : ℂ)` (`Finset.add_sum_erase`), giving `M = (U-sum:ℂ) + remainder`. (e) Equate the two forms of `M` and take real parts (`congrArg Complex.re`, `Complex.mul_re`/`natCast_re`/`natCast_im`).
- **Hypotheses**: cyclotomic, `NeZero m`, finite-dim, `Fintype` + `DecidableEq (galoisCharacter K L)`, `σ`, `1 &lt; s`.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `UnramifiedIn.ne_bot`, `twistedPrimeSum`, `summable_twistedPrimeSum`, `sum_charTwist_eq`, `sum_charTwist_ne`, `primeIdealZetaSum`, `primeIdealZetaSum_def`.
- **Used by**: `primeIdealZetaSum_frobeniusFibre_asymp` (via `hmaster`).
- **Visibility**: private (`theorem`).
- **Lines**: 777–879.
- **Notes**: &gt;30 lines (~103); `classical`. Key: `Summable.tsum_finsetSum`, `Function.Injective.tsum_eq`, `Complex.ofReal_tsum`, `Finset.add_sum_erase`.

### `theorem primeIdealZetaSum_frobeniusFibre_asymp`
- **Type**: `Tendsto (fun s =&gt; primeIdealZetaSum Sσ s / log(1/(s-1))) (𝓝[&gt;]1) (𝓝 (Nat.card Gal(L/K))⁻¹)`, `Sσ = {𝔭 prime, unram, Frob = mk σ}`.
- **What**: Sharifi 7.2.1 step (iv-a) — the Frobenius-fibre prime sum is asymptotic to `(1/|G|)·log(1/(s-1))`.
- **How**: Sets `N = Nat.card Gal(L/K)` (`&gt;0`) and the χ≠1 remainder `B(s) = ∑_{χ≠1}(χσ)⁻¹·twistedPrimeSum χ s`. Each term `‖(χσ)⁻¹·twistedPrimeSum χ s‖ ≤ Cχ` (`‖(χσ)⁻¹‖=1` root-of-unity + `artinLSeries_prime_sum_bounded_of_ne_one`); `choose` constants and sum to bound `‖B s‖ ≤ CB` (`norm_sum_le`, `Finset.sum_le_sum`, `eventually_all_finset`). Then `B(·).re/log → 0` (`squeeze_zero_norm'`, `RCLike.abs_re_le_norm`, `Tendsto.div_atTop`). COMBINE: `(1/N)·(U/log + B.re/log) → (1/N)·(1+0)` via `primeIdealZetaSum_unramified_div_log_tendsto_one` + `Tendsto.const_mul`; `Tendsto.congr'` against `card_mul_frobeniusFibre_eq` (which gives `N·P_σ = U-sum + B.re`, divided through, `inv_mul_cancel₀`).
- **Hypotheses**: cyclotomic, `NeZero m`, finite-dim, `m % 4 ≠ 2`, `σ`.
- **Uses from project**: `galoisCharacter`, `frobeniusClass`, `UnramifiedIn`, `twistedPrimeSum`, `primeIdealZetaSum`, `artinLSeries_prime_sum_bounded_of_ne_one`, `primeIdealZetaSum_unramified_div_log_tendsto_one`, `card_mul_frobeniusFibre_eq`, `tendsto_log_one_div_sub_one_atTop`. (Docstring also cites `character_orthogonality_cyclotomic_eq/_ne`, `log_artinLSeries_asymp_character_sum`, `artinLSeries_one_ne_zero`.)
- **Used by**: `cyclotomic_density_from_two_sided_asymp`.
- **Visibility**: public (`theorem`).
- **Lines**: 890–970.
- **Notes**: &gt;30 lines (~81); `classical`, `Fintype.ofFinite` instance. Key: `RCLike.abs_re_le_norm`, `eventually_all_finset`, `Finset.choose`/`choose … using`.

### `theorem tendsto_ratio_of_log_asymp_numerator`
- **Type**: real glue — if `num s/log(1/(s-1)) → c` and `den s/log(1/(s-1)) → 1`, then `num s/den s → c`.
- **What**: Real-analysis lemma: a common `log` denominator cancels in a ratio of two log-asymptotics.
- **How**: `log(1/(s-1)) ≠ 0` eventually (`Real.log_pos`, `one_lt_div₀`); then `(num/log)/(den/log) → c/1 = c` (`hnum.div hden`), and `Tendsto.congr'` rewrites `(num/log)/(den/log) = num/den` via `div_div_div_cancel_right₀`.
- **Hypotheses**: the two log-normalised limits `→ c` and `→ 1`.
- **Uses from project**: [] (abstract over `num`, `den`).
- **Used by**: `cyclotomic_density_from_two_sided_asymp`.
- **Visibility**: public (`theorem`).
- **Lines**: 974–986.
- **Notes**: —. Key: `div_div_div_cancel_right₀`, `Real.log_pos`.

### `theorem cyclotomic_density_from_two_sided_asymp`
- **Type**: `Tendsto (fun s =&gt; primeIdealZetaSum Sσ s / primeIdealZetaSum univ s) (𝓝[&gt;]1) (𝓝 (Nat.card Gal(L/K))⁻¹)`.
- **What**: Sharifi 7.2.1 step (iv) — the two-sided comparison giving Dirichlet density `1/|G|` for the Frobenius fibre.
- **How**: Direct application of `tendsto_ratio_of_log_asymp_numerator` with numerator-limit `primeIdealZetaSum_frobeniusFibre_asymp` (→ `1/|G|`) and denominator-limit `primeIdealZetaSum_univ_tendsto_log` (→ 1).
- **Hypotheses**: cyclotomic, `NeZero m`, finite-dim, `m % 4 ≠ 2`, `σ`.
- **Uses from project**: `frobeniusClass`, `UnramifiedIn`, `primeIdealZetaSum`, `tendsto_ratio_of_log_asymp_numerator`, `primeIdealZetaSum_frobeniusFibre_asymp`, `primeIdealZetaSum_univ_tendsto_log`.
- **Used by**: `chebotarev_cyclotomic`.
- **Visibility**: public (`theorem`).
- **Lines**: 992–1005.
- **Notes**: —. Term-mode proof.

### `theorem chebotarev_cyclotomic`
- **Type**: `HasDirichletDensity {𝔭 prime ∧ unram in L ∧ Frob = mk σ} ((Nat.card Gal(L/K) : ℝ)⁻¹)`.
- **What**: **Chebotarev's theorem, cyclotomic case** — primes of `K` unramified in `L=K(μ_m)` with Frobenius `σ` have Dirichlet density `1/|Gal(L/K)|`.
- **How**: `HasDirichletDensity` unfolds to exactly the ratio-tendsto, so this is `cyclotomic_density_from_two_sided_asymp K L m hm σ`.
- **Hypotheses**: `NeZero m`, `IsCyclotomicExtension {m} K L`, finite-dim, `m % 4 ≠ 2`, `σ` (`K,L` from the file `variable` line).
- **Uses from project**: `frobeniusClass`, `UnramifiedIn`, `HasDirichletDensity`, `cyclotomic_density_from_two_sided_asymp`.
- **Used by**: `chebotarev_cyclotomic_lowerDensity_ge`. (Top-level export; consumed by `Abelian.lean`/`Main.lean` downstream.)
- **Visibility**: public (`theorem`).
- **Lines**: 1012–1019.
- **Notes**: —. Uses the file-level `variable (K L …)`. Term-mode. No `sorry`.

### `theorem chebotarev_cyclotomic_lowerDensity_ge`
- **Type**: `HasLowerDirichletDensity {𝔭 prime ∧ unram ∧ Frob = mk σ} ((Nat.card Gal(L/K) : ℝ)⁻¹)`.
- **What**: Lower-density-inequality variant of the cyclotomic case, for feeding the abelian-case `HasLowerDirichletDensity.mono` chain.
- **How**: `(chebotarev_cyclotomic K L m hm σ).hasLower` (Dirichlet density ⇒ lower density, `HasDirichletDensity.hasLower`).
- **Hypotheses**: same as `chebotarev_cyclotomic`.
- **Uses from project**: `frobeniusClass`, `UnramifiedIn`, `HasLowerDirichletDensity`, `chebotarev_cyclotomic`, `HasDirichletDensity.hasLower`.
- **Used by**: unused in file (used downstream in `Abelian.lean`).
- **Visibility**: public (`theorem`).
- **Lines**: 1024–1031.
- **Notes**: —. File closes with `end Chebotarev` (line 1033).

---

# File Summary

**Totals**: 20 declarations — 1 `def` (`twistedPrimeSum`) + 19 theorems. By visibility: **9 private** (`sum_galoisCharacter_eq_card_or_zero`, `differentiableAt_logSum_of_two_le`, `cexp_logSum_eq_tprod`, `hasDerivAt_logSum_eq_logDeriv`, `norm_bounded_nhdsGT_of_deriv_continuousOn`, `twistedPrimeSum`, `summable_twistedPrimeSum`, `two_le_absNorm_prime`, `artinLSeries_prime_sum_bounded_of_analytic_extension`, `artinLSeries_prime_sum_bounded_of_ne_one`, `sum_charTwist_eq`, `sum_charTwist_ne`, `primeIdealZetaSum_unramified_div_log_tendsto_one`, `card_mul_frobeniusFibre_eq` — that's 14 private) + **6 public** (`log_artinLSeries_asymp_character_sum`, `character_orthogonality_cyclotomic_eq`, `character_orthogonality_cyclotomic_ne`, `primeIdealZetaSum_frobeniusFibre_asymp`, `tendsto_ratio_of_log_asymp_numerator`, `cyclotomic_density_from_two_sided_asymp`, `chebotarev_cyclotomic`, `chebotarev_cyclotomic_lowerDensity_ge` — 8 public). [Recount: 8 public + 12 private = 20.]

**Top-level export**: `chebotarev_cyclotomic` (the named main result of the module), plus its lower-density variant `chebotarev_cyclotomic_lowerDensity_ge`.

**Project API used by 3+ in-file declarations** (most load-bearing):
- `frobeniusClass` (Frobenius.lean) — ~14 declarations.
- `UnramifiedIn` (Frobenius.lean) — ~14 declarations.
- `galoisCharacter` (ZetaProduct.lean, an `abbrev` for `Gal(L/K) →* ℂˣ`) — ~12 declarations.
- `primeIdealZetaSum` / `primeIdealZetaSum_def` (Density.lean) — 6+ declarations.
- `UnramifiedIn.ne_bot` (Frobenius.lean) — 5 declarations.
- `summable_prime_absNorm_rpow` (Density.lean) — 4 declarations.
- `twistedPrimeSum` (this file) — 3 declarations.
- `tendsto_log_one_div_sub_one_atTop` (ForMathlib/LogOneDivSubOne.lean) — 3 declarations.

Other notable cross-file dependencies (1–2 uses each): `artinLSeries_analytic_extension`, `artinLSeries_one_ne_zero`, `exists_artinLSeries_eulerProduct_abelian`, `galoisCharacterOnIdeal` (ZetaProduct.lean); `finite_ramifiedIn` (Frobenius.lean); `primeIdealZetaSum_univ_tendsto_log`, `primeIdealZetaSum_le_log_plus_bounded`, `primeIdealZetaSum_le_of_subset`, `primeIdealZetaSum_le_card_of_finite`, `primeIdealZetaSum_union_of_disjoint`, `primeIdealZetaSum_eq_univ_of_forall_prime_mem`, `HasDirichletDensity`, `HasDirichletDensity.hasLower`, `HasLowerDirichletDensity` (Density.lean).

**Unused in file** (not referenced by any other in-file declaration; all are public top-level exports consumed downstream or standalone):
- `log_artinLSeries_asymp_character_sum` — the standalone "step (ii)" log-upper-bound; the live χ≠1 path uses `artinLSeries_prime_sum_bounded_of_ne_one` instead. Referenced only in a docstring.
- `chebotarev_cyclotomic_lowerDensity_ge` — consumed by `Abelian.lean`.

**`sorry`**: NONE. The file is `sorry`-free; all content (including the analytic core) is fully proven, resting on cross-file leaves `artinLSeries_analytic_extension` / `artinLSeries_one_ne_zero` in ZetaProduct.lean.

**`set_option`**: NONE in this file.

**`&gt;30`-line declarations** (8): `log_artinLSeries_asymp_character_sum` (~87), `differentiableAt_logSum_of_two_le` (~114, longest), `artinLSeries_prime_sum_bounded_of_analytic_extension` (~169 — largest by content), `primeIdealZetaSum_unramified_div_log_tendsto_one` (~47), `card_mul_frobeniusFibre_eq` (~103), `primeIdealZetaSum_frobeniusFibre_asymp` (~81). Borderline (~28): `summable_twistedPrimeSum`. (`sum_galoisCharacter_eq_card_or_zero` ~26.)

**Cross-cutting notes**: `classical` is opened locally in `artinLSeries_prime_sum_bounded_of_analytic_extension`, `card_mul_frobeniusFibre_eq`, `primeIdealZetaSum_frobeniusFibre_asymp`; `sum_galoisCharacter_eq_card_or_zero` uses `open scoped Classical in`. A recurring "plain-lambda anonymous-constructor injection into the `{𝔭 ∈ U ∧ prime ∧ ≠⊥}` subtype" idiom (to reindex tsums by `Injective.tsum_eq` while keeping projections `rfl`) appears in `log_artinLSeries_asymp_character_sum`, `summable_twistedPrimeSum`, `artinLSeries_prime_sum_bounded_of_analytic_extension`, and `card_mul_frobeniusFibre_eq` — matching the MEMORY note on Pi-subtype univ annotations. The `m % 4 ≠ 2` discriminant hypothesis enters at `artinLSeries_prime_sum_bounded_of_ne_one` and threads up through every cyclotomic-case theorem. The structural arc: orthogonality (`sum_galoisCharacter_eq_card_or_zero` → `character_orthogonality_*` → `sum_charTwist_*`) + analytic χ≠1 bound (`differentiableAt_logSum…`/`cexp_logSum…`/`hasDerivAt_logSum…`/`norm_bounded…` → `artinLSeries_prime_sum_bounded_of_analytic_extension` → `…_of_ne_one`) feed the master identity `card_mul_frobeniusFibre_eq`, which with the unramified-sum asymptotic yields `primeIdealZetaSum_frobeniusFibre_asymp`, then `cyclotomic_density_from_two_sided_asymp` → `chebotarev_cyclotomic`.</result>
<usage><subagent_tokens>65778</subagent_tokens><tool_uses>5</tool_uses><duration_ms>183895</duration_ms></usage>
</task-notification>