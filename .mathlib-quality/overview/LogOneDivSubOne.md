The file is short and self-contained. I've read it in full, including proofs. Here is the detailed inventory.

---

### `theorem tendsto_log_one_div_sub_one_atTop`

- **Type** · `Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[&gt;] (1 : ℝ)) atTop`
- **What** · The real function `s ↦ log(1/(s-1))` diverges to `+∞` as `s` approaches `1` from the right (`s ↓ 1`).
- **How** · Factors the target through `Real.log` via `Real.tendsto_log_atTop.comp`, reducing to showing `1/(s-1) → +∞` as `s ↓ 1`. To get that: first shows `s ↦ s - 1` maps `𝓝[&gt;] 1` into `𝓝[&gt;] 0` using `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within` — the bare convergence `s - 1 → 0` comes from `(continuous_sub_right 1).tendsto'` restricted by `.mono_left nhdsWithin_le_nhds`, and the "stays in `&gt; 0`" side condition is discharged by `filter_upwards [self_mem_nhdsWithin]` + `linarith` (on `s ∈ Ioi 1` ⇒ `s - 1 &gt; 0`). Then `h1.inv_tendsto_nhdsGT_zero` gives `(s-1)⁻¹ → +∞`, and `simpa only [one_div]` rewrites `(s-1)⁻¹` to `1/(s-1)`.
- **Hypotheses** · None (no arguments; a closed statement about a fixed real function).
- **Uses from project** · []
- **Used by** · `tendsto_ratio_one_of_log_pm_bounded` (bound to `hL` at line 50)
- **Visibility** · public (inside `@[expose] public section`); `noncomputable`
- **Lines** · 29–38 (10 lines)
- **Notes** · — (proof exactly 10 lines incl. signature; uses non-default `simpa … using! …` with the `!` elaboration variant)

---

### `theorem tendsto_ratio_one_of_log_pm_bounded`

- **Type** · `(f : ℝ → ℝ) → (h_le : ∃ C : ℝ, ∀ᶠ s in 𝓝[&gt;] (1:ℝ), f s ≤ Real.log (1/(s-1)) + C) → (h_lower : ∃ C : ℝ, ∀ᶠ s in 𝓝[&gt;] (1:ℝ), Real.log (1/(s-1)) - C ≤ f s) → Tendsto (fun s : ℝ ↦ f s / Real.log (1/(s-1))) (𝓝[&gt;] 1) (𝓝 1)`
- **What** · Generic squeeze: if a function `f` agrees with `log(1/(s-1))` up to a two-sided additive bounded error on a right-neighbourhood of `1`, then the ratio `f(s) / log(1/(s-1)) → 1` as `s ↓ 1`. The additive bounded term washes out because the denominator blows up.
- **How** · Destructures the two existentials to get upper bound `f s ≤ log(1/(s-1)) + C₁` (`hle`) and lower bound `log(1/(s-1)) - C₂ ≤ f s` (`hlower`), both eventually in `𝓝[&gt;] 1`. Sets `hL := tendsto_log_one_div_sub_one_atTop` (denominator `→ +∞`). Key step `h0`: the normalized difference `(f s - log(1/(s-1))) / log(1/(s-1)) → 0`, obtained from `tendsto_bdd_div_atTop_nhds_zero` with bounds `b := -C₂`, `B := C₁` — its two bounded-numerator hypotheses are produced by `hlower.mono … linarith` and `hle.mono … linarith` (turning the `f`-bounds into bounds on `f s - log(1/(s-1))`), and its divergence hypothesis is `hL`. Then `h0.const_add 1` gives `1 + (…) → 1 + 0 = 1` (rewritten via `add_zero`), and `.congr'` matches it to the target `f s / log(1/(s-1))`: under `filter_upwards [hL.eventually_gt_atTop 0]` (so the denominator is positive, hence nonzero, `h.ne'`), the algebraic identity `1 + (f s - L)/L = f s / L` is closed by `rw [add_div_eq_mul_add_div _ _ h.ne', one_mul, add_sub_cancel]`.
- **Hypotheses** · `f : ℝ → ℝ`; `h_le`: there exists `C` with `f s ≤ log(1/(s-1)) + C` eventually as `s ↓ 1`; `h_lower`: there exists `C` with `log(1/(s-1)) - C ≤ f s` eventually as `s ↓ 1`. (Both inequalities oriented smaller-side-left per project convention.)
- **Uses from project** · [`tendsto_log_one_div_sub_one_atTop`]
- **Used by** · unused in file
- **Visibility** · public (inside `@[expose] public section`); `noncomputable`
- **Lines** · 44–57 (14 lines)
- **Notes** · — (no sorry/TODO/set_option; 14 lines, under 30)

---

## File Summary

**Totals** · 2 declarations, both `theorem`s (0 defs, 0 instances, 0 axioms, 0 sorries). File length 58 lines.

**Module setup** · `module` file (line 1). Two `public import`s: `Mathlib.Analysis.SpecialFunctions.Log.Basic` and `Mathlib.Topology.Algebra.Order.Field`. Whole body wrapped in `@[expose] public section` (line 21) and `noncomputable section` (line 23). `open Filter Topology` (line 25). Module-level docstring (lines 6–19) describes both lemmas and explicitly states they mention no number-field / density content and are kept in the root namespace as mathlib-upstreaming candidates.

**Namespace** · Root namespace (no `namespace` block) — deliberate, per docstring and per the file's location under `ForMathlib/` (upstream candidates), an exception to the project's usual `Chebotarev` namespace.

**Key API (public surface)**
- `tendsto_log_one_div_sub_one_atTop` — `log(1/(s-1)) → +∞` as `s ↓ 1`. The foundational divergence fact; the only intra-file dependency.
- `tendsto_ratio_one_of_log_pm_bounded` — squeeze lemma: `f`-agrees-with-`log(1/(s-1))`-up-to-bounded ⇒ ratio `→ 1`. This is the file's externally-consumed result (the density-asymptotics application; unused *within* this file).

**Dependency graph (in-file)** · `tendsto_ratio_one_of_log_pm_bounded` → `tendsto_log_one_div_sub_one_atTop`. The base lemma has no project dependencies.

**Unused within file** · `tendsto_ratio_one_of_log_pm_bounded` (intended for external callers — the density asymptotic; consistent with the CLAUDE.md `Density.lean` description of an asymptotic for `Σ_𝔭 N𝔭^{-s}`).

**`sorry` list** · none.

**`set_option` list** · none.

**`&gt;30`-line declarations** · none (largest is `tendsto_ratio_one_of_log_pm_bounded` at 14 lines).

**Notable mathlib lemmas leaned on** · `Real.tendsto_log_atTop`, `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`, `continuous_sub_right`, `Filter.Tendsto.inv_tendsto_nhdsGT_zero`, `self_mem_nhdsWithin`, `tendsto_bdd_div_atTop_nhds_zero`, `Filter.Tendsto.const_add`, `Filter.Tendsto.congr'`, `Filter.Tendsto.eventually_gt_atTop`, `add_div_eq_mul_add_div`, `add_sub_cancel`. (Standard `Filter`/`Topology`/`Real.log` API only — no project-specific dependencies, confirming the upstream-candidate intent.)