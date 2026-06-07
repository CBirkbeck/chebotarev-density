module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Limit lemmas for `log (1 / (s - 1))` near `s = 1`

Two purely analytic limit facts about the function `s ↦ log (1 / (s - 1))`
on a right neighbourhood of `1`:

* `tendsto_log_one_div_sub_one_atTop` — it diverges to `+∞` as `s ↓ 1`.
* `tendsto_ratio_one_of_log_pm_bounded` — a generic squeeze: any `f` that
  agrees with `log (1 / (s - 1))` up to an additive bounded term has
  `f s / log (1 / (s - 1)) → 1`.

Neither lemma mentions number fields or Dirichlet density; they are kept
in the root namespace as candidates for upstreaming to mathlib.
-/

@[expose] public section

noncomputable section

open Filter Topology

/-- `log(1/(s-1)) → +∞` as `s ↓ 1` — the divergence driving the density
asymptotics. -/
theorem tendsto_log_one_div_sub_one_atTop :
    Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop := by
  refine Real.tendsto_log_atTop.comp ?_
  have h1 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_sub_right 1).tendsto' 1 0 (by ring)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s hs ↦ by
        simp only [Set.mem_Ioi] at hs ⊢
        linarith)
  simpa only [one_div] using! h1.inv_tendsto_nhdsGT_zero

/-- Generic squeeze: if `f(s) = log(1/(s-1)) + bounded` on a right
neighbourhood of `1`, then `f(s) / log(1/(s-1)) → 1` as `s ↓ 1`. The
analytic content is just that `log(1/(s-1)) → ∞`, so the additive
bounded term washes out under division. -/
theorem tendsto_ratio_one_of_log_pm_bounded
    (f : ℝ → ℝ)
    (h_le : ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), f s ≤ Real.log (1 / (s - 1)) + C)
    (h_lower : ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), Real.log (1 / (s - 1)) - C ≤ f s) :
    Tendsto (fun s : ℝ ↦ f s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 1) := by
  obtain ⟨C₁, hle⟩ := h_le
  obtain ⟨C₂, hlower⟩ := h_lower
  have hL := tendsto_log_one_div_sub_one_atTop
  have h0 : Tendsto (fun s ↦ (f s - Real.log (1 / (s - 1))) / Real.log (1 / (s - 1)))
      (𝓝[>] (1 : ℝ)) (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero (b := -C₂) (B := C₁)
      (hlower.mono fun s h ↦ by linarith) (hle.mono fun s h ↦ by linarith) hL
  refine (add_zero (1 : ℝ) ▸ h0.const_add 1).congr' ?_
  filter_upwards [hL.eventually_gt_atTop 0] with s h
  rw [add_div_eq_mul_add_div _ _ h.ne', one_mul, add_sub_cancel]
