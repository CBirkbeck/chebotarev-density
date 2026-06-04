# Ticket Board — linchpin keystone subtree (from decomposition.md, Sharifi 7.1.12)

## Tickets

### [T01] dedekindZeta_re_pos_of_one_lt (L4 — real positivity)
- **Status**: done (proven, build green, axioms clean [propext, Classical.choice, Quot.sound])
- **File**: CebotarevDensity/NumberFieldEulerProduct.lean
- **Depends on**: none
- **Type**: theorem
#### Statement
`(s : ℝ) (hs : 1 < s) : 0 < (NumberField.dedekindZeta L (s : ℂ)).re`
#### Proof sketch
1. `dedekindZeta_eq_tsum_idealNormMultiplicity L` (have, with `1 < (s:ℂ).re`) rewrites ζ_K to `∑' n, mult(n)·(n:ℂ)^{-(s:ℂ)}`.
2. Each term is a nonneg real cast: `(n:ℂ)^{-(s:ℂ)}` for real n,s is `((n:ℝ)^(-s) : ℂ)`; `.re` of the tsum = `∑' n, mult(n)·n^{-s}` (Complex.re_tsum / re continuous-linear).
3. Positive: the `n=1` term is `mult(1)·1 = 1 > 0` (`idealNormMultiplicity_one`), rest ≥ 0; `tsum_pos`.
#### Mathlib lemmas needed
`dedekindZeta_eq_tsum_idealNormMultiplicity` (project), `idealNormMultiplicity_one` (project), `Complex.reCLM`/`ContinuousLinearMap.map_tsum`, `tsum_pos`, `Real.rpow_pos_of_pos`.
#### Generality
`L` number field (file convention); `s : ℝ`.

### [T02] prod_eulerFactor_eq_tsum_of_factors_subset (L1.1 — finite-S Euler factor)
- **Status**: done — proven as `prod_eulerFactor_eq_tsum_exponentVector` (+ `absNorm_prod_pow_of_primeIdeal`, `prod_absNorm_cpow_eq_absNorm_prod_pow_cpow`, `norm_absNorm_cpow_neg_lt_one`); 4 private helpers; build green; axioms clean.
- **File**: CebotarevDensity/NumberFieldEulerProduct.lean
- **Depends on**: none
- **Type**: theorem
#### Statement
For a `Finset S` of nonzero prime ideals and `1 < s.re`: `∏ 𝔭 ∈ S, (1 - (absNorm 𝔭)^{-s})⁻¹ = ∑' over ideals 𝔞 ≠ ⊥ whose prime factors ⊆ S of (absNorm 𝔞)^{-s}`.
#### Proof sketch (Sharifi Prop 7.1.9, p.139, applied to ideals)
1. Each factor `(1-N𝔭⁻ˢ)⁻¹ = ∑' e:ℕ, N𝔭^{-es}` (geometric, `tsum_geometric_of_norm_lt_one`, `‖N𝔭⁻ˢ‖<1` since N𝔭≥2, s.re>1).
2. `∏_{𝔭∈S} ∑'_e (...)` = `∑'` over `(S →₀ ℕ)` of `∏ N𝔭^{-e_𝔭 s}` (`Finset.prod_tsum`/`tsum_prod` for finitely many summable factors).
3. UFD bijection `{𝔞≠⊥ : prime factors ⊆ S} ≃ (S →₀ ℕ)` (`UniqueFactorizationMonoid`/`Ideal.factorization`), `absNorm` multiplicative (`Ideal.absNorm_mul`/`map_prod`), turning the exponent-vector sum into the ideal sum.
#### Mathlib lemmas needed
`tsum_geometric_of_norm_lt_one`, `Finset.prod_tsum`, `Ideal.absNorm_mul`/`MonoidHom` form, `UniqueFactorizationMonoid.factorization`, `Ideal.absNorm_pow`.
#### Generality
`L` number field; `S : Finset {𝔭 // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}`.

### [T03] dedekindZeta_eq_tprod_primeIdeal (L1 — keystone, limit over S)
- **Status**: done — proven via HasProd + S↑⊤ limit (6 private helpers); NumberFieldEulerProduct.lean sorry-free; axioms clean. Commit 80a0f1e.
- **File**: CebotarevDensity/NumberFieldEulerProduct.lean  (skeleton already stated)
- **Depends on**: T02
- **Type**: theorem
#### Statement
`{s : ℂ} (hs : 1 < s.re) : dedekindZeta L s = ∏' 𝔭 : {𝔭 // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (1 - (absNorm 𝔭)^{-s})⁻¹`
#### Proof sketch (Sharifi 7.1.12 / 7.1.9 limit, p.139–140)
1. `Multipliable` of the prime-ideal factors (absolute convergence from `summable` of `Σ N𝔭⁻ˢ`).
2. `∏'_𝔭 = lim_{S↑⊤} ∏_{𝔭∈S}` (`HasProd`/`tprod` as filter limit over finite S).
3. By T02, `∏_{𝔭∈S} = ∑'_{𝔞 factors⊆S}`; as `S↑⊤` every ideal's finite factor set is eventually ⊆ S, so the RHS → `∑'_𝔞 = ζ_K` (`dedekindZeta_eq_tsum_idealNormMultiplicity` regrouped).
#### Mathlib lemmas needed
`Multipliable`, `HasProd`, `tendsto_finset_prod`/`HasProd.tprod_eq`, `tendsto_tsum_of_...`.
#### Generality
`L` number field; `s : ℂ`.

### [T04] log_dedekindZeta_re_eq_tsum_neg_log_one_sub (L2)
- **Status**: done — proven as helper `log_dedekindZeta_re_eq_tsum_neg_log_one_sub` inside T06; Density sorry-free
- **File**: CebotarevDensity/Density.lean
- **Depends on**: T01, T03
- **Type**: theorem
#### Statement
`(s : ℝ) (hs : 1 < s) : Real.log (dedekindZeta K (s:ℂ)).re = ∑' 𝔭 : {𝔭 // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (- Real.log (1 - (absNorm 𝔭.1 : ℝ)^(-s)))`
#### Proof sketch
1. T03 + T01: ζ_K(s) is a positive real equal to the convergent product `∏'_𝔭 (1-N𝔭⁻ˢ)⁻¹`.
2. `Real.log` of a positive convergent `tprod` = `tsum` of logs (`Real.hasProd...`/`Real.log_tprod`), each `Real.log((1-N𝔭⁻ˢ)⁻¹) = -Real.log(1-N𝔭⁻ˢ)` (`Real.log_inv`).
#### Mathlib lemmas needed
`Real.log_tprod`/`HasProd.log`, `Real.log_inv`, `Complex.re` bridge from T03 at real s.
#### Generality
`K` number field; `s : ℝ`.

### [T05] abs_tsum_neg_log_one_sub_sub_rpow_le (L3 — the O(1) tail)
- **Status**: done — proven as helper `abs_tsum_neg_log_one_sub_sub_rpow_le` inside T06; Density sorry-free
- **File**: CebotarevDensity/Density.lean
- **Depends on**: none (uses proven `primeIdealZetaHigherTail_bounded`)
- **Type**: theorem
#### Statement
`∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1:ℝ), |∑' 𝔭 : {𝔭 // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (- Real.log (1 - (absNorm 𝔭.1:ℝ)^(-s)) - (absNorm 𝔭.1:ℝ)^(-s))| ≤ C`
#### Proof sketch
1. Termwise `0 ≤ -log(1-x) - x ≤ x²/(1-x)` for `0 ≤ x < 1` (`-log(1-x)-x = Σ_{k≥2}xᵏ/k ≤ Σ_{k≥2}xᵏ = x²/(1-x)`).
2. So `0 ≤ Σ_𝔭(...) ≤ Σ_𝔭 N𝔭^{-2s}/(1-N𝔭⁻ˢ)`, bounded by `C` via `primeIdealZetaHigherTail_bounded`.
3. `|·| = ·` (nonneg) `≤ C`.
#### Mathlib lemmas needed
`Real.abs_log_sub_add_sum_range_le`/`Real.log_le_sub_one_of_pos`, geometric `Σ_{k≥2}xᵏ`, `primeIdealZetaHigherTail_bounded` (project, proven).
#### Generality
`K` number field.

### [T06] logDedekindZeta_sub_primeIdealZetaSum_bounded (LINCHPIN — assembly)
- **Status**: done — PROVEN. Density.lean sorry-free; #print axioms fully clean (no sorryAx). Downstream hasDirichletDensity_of_finite + ratioSum_frobeniusFibres_tendsto_one DETAINTED (sorryAx cleared). (T04/L2 + T05/L3 absorbed as helpers in this proof.)
- **File**: CebotarevDensity/Density.lean
- **Depends on**: T04, T05, T01
- **Type**: theorem
#### Statement
`∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] 1, |Real.log (dedekindZeta K (s:ℂ)).re - primeIdealZetaSum (univ) s| ≤ C`
#### Proof sketch
1. T04: `log ζ_K = Σ_𝔭 -log(1-N𝔭⁻ˢ)`. `primeIdealZetaSum univ s = Σ_𝔭 N𝔭⁻ˢ` (`primeIdealZetaSum_def`; carrier = the prime subtype).
2. Difference `= Σ_𝔭 (-log(1-N𝔭⁻ˢ) - N𝔭⁻ˢ)`, bounded by T05.
#### Mathlib lemmas needed
T04, T05, `primeIdealZetaSum_def`.
#### Generality
`K` number field.
