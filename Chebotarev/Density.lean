module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Dirichlet density of a set of prime ideals

For a number field `K`, the Dirichlet density of a set `S` of prime ideals of
`𝓞 K` is, when it exists,

  δ(S) = lim_{s → 1⁺} ( Σ_{𝔭 ∈ S} N𝔭^{-s} ) / ( Σ_𝔭 N𝔭^{-s} ),

with both sums running over nonzero prime ideals. The denominator is
asymptotic to `log (s - 1)^{-1}` as `s ↓ 1`
(Sharifi, *Algebraic Number Theory*, §7.1.12; `docs/algnum.pdf`).

## Main definitions

* `Chebotarev.primeIdealZetaSum` — the partial Dirichlet
  series `Σ_{𝔭 ∈ S} N𝔭^{-s}`.
* `Chebotarev.HasDirichletDensity` — `S` has Dirichlet
  density `δ`.
* `Chebotarev.HasUpperDirichletDensity`,
  `Chebotarev.HasLowerDirichletDensity` — `limsup` /
  `liminf` variants used in the Chebotarev sandwich argument
  (Sharifi 7.2.2 Step 2).

## References

* Sharifi, *Algebraic Number Theory*, §7.1.13 (`docs/algnum.pdf`).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*
  (`docs/cheb.pdf`).
-/

@[expose] public section

noncomputable section

open Filter NumberField Topology

namespace Chebotarev

/-- Partial Dirichlet series `Σ_{𝔭 ∈ S} N𝔭^{-s}` over nonzero prime ideals
`𝔭` of `𝓞 K` lying in the set `S`. -/
noncomputable def primeIdealZetaSum
    (K : Type*) [Field K] [NumberField K] (S : Set (Ideal (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)

/-- The Dirichlet density of a set `S` of prime ideals of `𝓞 K` is `δ` when
the ratio of partial sums tends to `δ` as `s ↓ 1`.

Sharifi 7.1.13: `δ(S) = lim_{s → 1⁺} (Σ_{𝔭 ∈ S} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s})`. -/
def HasDirichletDensity
    (K : Type*) [Field K] [NumberField K] (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  Tendsto
    (fun s : ℝ ↦ primeIdealZetaSum K S s / primeIdealZetaSum K Set.univ s)
    (𝓝[>] 1) (𝓝 δ)

/-- Upper Dirichlet density (`limsup` of the ratio).

**Convention note.** This uses the standard mathematical convention:
upper = `limsup`. Sharifi *Algebraic Number Theory* §7.1.13 (p. 140)
labels the `limsup` form "lower Dirichlet density" and the `liminf` form
"upper Dirichlet density" — a non-standard labelling. We follow the
standard convention, so:

* this `HasUpperDirichletDensity` (= `limsup`) is what Sharifi calls
  "lower Dirichlet density" and notates `δ_sup`;
* `HasLowerDirichletDensity` (= `liminf`) is what Sharifi calls
  "upper Dirichlet density" and notates `δ_inf`.

When transcribing Sharifi's `δ_inf` to Lean, use `HasLowerDirichletDensity`. -/
def HasUpperDirichletDensity
    (K : Type*) [Field K] [NumberField K] (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  Filter.limsup
    (fun s : ℝ ↦ primeIdealZetaSum K S s / primeIdealZetaSum K Set.univ s)
    (𝓝[>] 1) = δ

/-- Lower Dirichlet density (`liminf` of the ratio). See
`HasUpperDirichletDensity` for the convention note: this matches
Sharifi's `δ_inf` notation despite Sharifi's labelling
inversion. -/
def HasLowerDirichletDensity
    (K : Type*) [Field K] [NumberField K] (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  Filter.liminf
    (fun s : ℝ ↦ primeIdealZetaSum K S s / primeIdealZetaSum K Set.univ s)
    (𝓝[>] 1) = δ

variable (K : Type*) [Field K] [NumberField K]

/-- The Dirichlet density of the empty set is `0`. -/
theorem hasDirichletDensity_empty :
    HasDirichletDensity K (∅ : Set (Ideal (𝓞 K))) 0 := by
  have : IsEmpty {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (∅ : Set (Ideal (𝓞 K))) ∧
      𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := ⟨fun x ↦ (Set.mem_empty_iff_false x.1).mp x.2.1⟩
  simpa only [HasDirichletDensity, primeIdealZetaSum, tsum_empty, zero_div]
    using tendsto_const_nhds

/-- If the upper density of `S` equals the lower density of `S` and both equal
`δ`, then the Dirichlet density of `S` is `δ`. (Sandwich criterion used in the
Chebotarev proof: Sharifi 7.2.2 Step 2 last paragraph.) -/
theorem HasDirichletDensity.of_upper_eq_lower
    {S : Set (Ideal (𝓞 K))} {δ : ℝ} (hUp : HasUpperDirichletDensity K S δ)
    (hLow : HasLowerDirichletDensity K S δ) :
    HasDirichletDensity K S δ := by
  sorry

/-- Existence + value: from `HasDirichletDensity` one extracts the upper and
lower density. -/
theorem HasDirichletDensity.hasUpper
    {S : Set (Ideal (𝓞 K))} {δ : ℝ} (h : HasDirichletDensity K S δ) :
    HasUpperDirichletDensity K S δ :=
  h.limsup_eq

theorem HasDirichletDensity.hasLower
    {S : Set (Ideal (𝓞 K))} {δ : ℝ} (h : HasDirichletDensity K S δ) :
    HasLowerDirichletDensity K S δ :=
  h.liminf_eq

/-- Finite disjoint additivity. -/
theorem HasDirichletDensity.union_of_disjoint
    {S T : Set (Ideal (𝓞 K))} (hDisj : Disjoint S T) {δ ε : ℝ} (hS : HasDirichletDensity K S δ)
    (hT : HasDirichletDensity K T ε) :
    HasDirichletDensity K (S ∪ T) (δ + ε) := by
  sorry

/-- Monotonicity of the lower density under inclusion. -/
theorem HasLowerDirichletDensity.mono
    {S T : Set (Ideal (𝓞 K))} (hST : S ⊆ T) {δ ε : ℝ} (hS : HasLowerDirichletDensity K S δ)
    (hT : HasLowerDirichletDensity K T ε) :
    δ ≤ ε := by
  sorry

/-! ### Sub-lemmas for `primeIdealZetaSum_univ_tendsto_log`

Following Sharifi 7.1.12 proof (p. 140, *Algebraic Number Theory*). The
source's argument decomposes into:

(i) Euler-product identity `ζ_K = ∏(1 - N𝔭^{-s})^{-1}` on `Re s > 1`
    (Sharifi 7.1.12 statement).
(ii) `log ζ_K(s) ~ Σ_𝔭 N𝔭^{-s}` as the principal term, with the
    higher-power tail `Σ_{k≥2,𝔭} N𝔭^{-ks}/k` bounded on `Re s > 1/2`
    (Sharifi 7.1.12 proof: "log ζ_K(s) ~ Σ_𝔭 N𝔭^{-s}").
(iii) `log ζ_K(s) ~ log(1/(s-1))` from the simple pole of `ζ_K` at `s=1`
    (mathlib: `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`).
-/

/-- Sharifi 7.1.12 proof (p. 140), bounded tail step. The higher-power
contribution to the Euler-product logarithm,
`Σ_{𝔭, k≥2} N𝔭^{-ks}/k`, is bounded on a right neighbourhood of `s = 1`
(in fact on `Re s > 1/2`). This is implicit in the source's "`log ζ_K(s) ~
Σ_𝔭 N𝔭^{-s}`" — the `~` collapses the tail into an analytic-at-1 piece. -/
theorem primeIdealZetaHigherTail_bounded :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
          (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s)
            / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) ≤ C := by
  sorry

/-- Sharifi 7.1.12 proof (p. 140), Euler-product-log identity:
`log ζ_K(s) = Σ_𝔭 N𝔭^{-s} + O(1)` as `s ↓ 1`. The `O(1)` is the
higher-power tail `Σ_{𝔭,k≥2} N𝔭^{-ks}/k`, bounded by
`primeIdealZetaHigherTail_bounded`. Source: "`log ζ_K(s) ~ Σ_𝔭 N𝔭^{-s}`". -/
theorem logDedekindZeta_sub_primeIdealZetaSum_bounded :
    ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ),
      |Real.log (dedekindZeta K (s : ℂ)).re
        - primeIdealZetaSum K (Set.univ : Set (Ideal (𝓞 K))) s| ≤ C := by
  sorry

/-- Sharifi 7.1.12 proof (p. 140), simple-pole identity:
`log ζ_K(s) = log(1/(s-1)) + O(1)` as `s ↓ 1`, from the simple pole of
`ζ_K` at `s=1` (mathlib's
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`). -/
theorem logDedekindZeta_sub_log_inv_sub_one_bounded :
    ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ),
      |Real.log (dedekindZeta K (s : ℂ)).re - Real.log (1 / (s - 1))| ≤ C := by
  set r := dedekindZeta_residue K
  have hrpos : 0 < r := dedekindZeta_residue_pos K
  have hF : Tendsto (fun s : ℝ => (s - 1) * (dedekindZeta K (s : ℂ)).re)
      (𝓝[>] (1 : ℝ)) (𝓝 r) := by
    refine ((Complex.continuous_re.tendsto _).comp
      (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)).congr fun s => ?_
    rw [Function.comp_apply, show ((s : ℂ) - 1) = ((s - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
  refine ⟨max |Real.log (r / 2)| |Real.log (2 * r)|, ?_⟩
  have hev : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      (s - 1) * (dedekindZeta K (s : ℂ)).re ∈ Set.Ioo (r / 2) (2 * r) :=
    hF.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hev, self_mem_nhdsWithin] with s hF_s hs1
  simp only [Set.mem_Ioi] at hs1
  have hsm1 : (0 : ℝ) < s - 1 := by linarith
  obtain ⟨hlo, hhi⟩ := hF_s
  have hFpos : (0 : ℝ) < (s - 1) * (dedekindZeta K (s : ℂ)).re := by linarith
  have hζpos : (0 : ℝ) < (dedekindZeta K (s : ℂ)).re := (mul_pos_iff_of_pos_left hsm1).mp hFpos
  rw [one_div, Real.log_inv, sub_neg_eq_add,
    ← Real.log_mul (ne_of_gt hζpos) (ne_of_gt hsm1), mul_comm]
  exact abs_le_max_abs_abs (Real.log_lt_log (by linarith) hlo).le (Real.log_lt_log hFpos hhi).le

/-- Sharifi 7.1.12 proof (p. 140), lower bound: `Σ_𝔭 N𝔭^{-s} ≥
log(1/(s-1)) - C`. -/
theorem primeIdealZetaSum_ge_log_minus_bounded :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      primeIdealZetaSum K (Set.univ : Set (Ideal (𝓞 K))) s
        ≥ Real.log (1 / (s - 1)) - C := by
  obtain ⟨C₁, h₁⟩ := logDedekindZeta_sub_primeIdealZetaSum_bounded K
  obtain ⟨C₂, h₂⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded K
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with s hs₁ hs₂
  linarith [abs_le.mp hs₁, abs_le.mp hs₂]

/-- Sharifi 7.1.12 proof (p. 140), upper bound: `Σ_𝔭 N𝔭^{-s} ≤
log(1/(s-1)) + C'`. -/
theorem primeIdealZetaSum_le_log_plus_bounded :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      primeIdealZetaSum K (Set.univ : Set (Ideal (𝓞 K))) s
        ≤ Real.log (1 / (s - 1)) + C := by
  obtain ⟨C₁, h₁⟩ := logDedekindZeta_sub_primeIdealZetaSum_bounded K
  obtain ⟨C₂, h₂⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded K
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with s hs₁ hs₂
  linarith [abs_le.mp hs₁, abs_le.mp hs₂]

/-- Generic squeeze: if `f(s) = log(1/(s-1)) + bounded` on a right
neighbourhood of `1`, then `f(s) / log(1/(s-1)) → 1` as `s ↓ 1`. The
analytic content is just that `log(1/(s-1)) → ∞`, so the additive
bounded term washes out under division. -/
theorem tendsto_ratio_one_of_log_pm_bounded
    (f : ℝ → ℝ) (h_le : ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), f s ≤ Real.log (1 / (s - 1)) + C)
    (h_ge : ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), f s ≥ Real.log (1 / (s - 1)) - C) :
    Tendsto (fun s : ℝ ↦ f s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 1) := by
  obtain ⟨C₁, hle⟩ := h_le
  obtain ⟨C₂, hge⟩ := h_ge
  have hL : Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[>] (1:ℝ)) atTop := by
    refine Real.tendsto_log_atTop.comp ?_
    have h1 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1:ℝ)) (𝓝[>] (0:ℝ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact ((continuous_sub_right 1).tendsto' 1 0 (by ring)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [Set.mem_Ioi] at hs ⊢
        linarith
    simpa [one_div] using h1.inv_tendsto_nhdsGT_zero
  have hLpos := hL.eventually_gt_atTop 0
  have h0 : Tendsto (fun s ↦ (f s - Real.log (1 / (s - 1))) / Real.log (1 / (s - 1)))
      (𝓝[>] (1:ℝ)) (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero (b := -C₂) (B := C₁)
      (hge.mono fun s h ↦ by linarith) (hle.mono fun s h ↦ by linarith) hL
  refine (add_zero (1:ℝ) ▸ h0.const_add 1).congr' ?_
  filter_upwards [hLpos] with s h
  rw [add_div_eq_mul_add_div _ _ h.ne', one_mul, add_sub_cancel]

/-- **Sharifi 7.1.12**, *Algebraic Number Theory*, p. 140.

The denominator `Σ_𝔭 N𝔭^{-s}` is asymptotic to `log(1/(s-1))` as `s ↓ 1`.
This is the analytic ingredient that makes the Dirichlet-density
definition robust under the L-function comparisons in the Chebotarev
proof. -/
theorem primeIdealZetaSum_univ_tendsto_log :
    Tendsto
      (fun s : ℝ ↦ primeIdealZetaSum K (Set.univ : Set (Ideal (𝓞 K))) s
        / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 1) :=
  tendsto_ratio_one_of_log_pm_bounded
    (primeIdealZetaSum K (Set.univ : Set (Ideal (𝓞 K))))
    (primeIdealZetaSum_le_log_plus_bounded K)
    (primeIdealZetaSum_ge_log_minus_bounded K)

/-- The full prime-ideal zeta sum diverges to `+∞` as `s ↓ 1` (it is asymptotic to
`log(1/(s-1)) → ∞`). -/
theorem primeIdealZetaSum_univ_tendsto_atTop :
    Tendsto (primeIdealZetaSum K (Set.univ : Set (Ideal (𝓞 K)))) (𝓝[>] 1) atTop := by
  have hL : Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop := by
    apply Real.tendsto_log_atTop.comp
    have h1 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1 : ℝ)) (𝓝 (1 - 1)) :=
          (continuous_sub_right 1).continuousWithinAt
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [Set.mem_Ioi] at hs ⊢
        linarith
    have h2 : Tendsto (fun x : ℝ ↦ 1 / x) (𝓝[>] (0 : ℝ)) atTop := by
      simpa [one_div] using tendsto_inv_nhdsGT_zero
    exact h2.comp h1
  have hhalf : Tendsto (fun s : ℝ ↦ (1 / 2 : ℝ) * Real.log (1 / (s - 1))) (𝓝[>] 1) atTop :=
    hL.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' _ ?_ hhalf
  filter_upwards [(primeIdealZetaSum_univ_tendsto_log K).eventually
      (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)), hL.eventually_gt_atTop 0] with s hs hpos
  exact ((lt_div_iff₀ hpos).mp (Set.mem_Ioi.mp hs)).le

/-- For a finite set `S`, the partial sum `Σ_{𝔭 ∈ S} N𝔭^{-s}` is bounded above by the
number of qualifying primes: there are finitely many terms and each `N𝔭^{-s} ≤ 1`
for `s > 0` (since `N𝔭 ≥ 1`). -/
theorem primeIdealZetaSum_le_card_of_finite {S : Set (Ideal (𝓞 K))} (hS : S.Finite)
    {s : ℝ} (hs : 0 < s) :
    primeIdealZetaSum K S s ≤
      Nat.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := by
  haveI : Finite {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
    (hS.subset fun _ hx ↦ hx.1).to_subtype
  haveI : Fintype {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := Fintype.ofFinite _
  rw [primeIdealZetaSum, tsum_fintype, Nat.card_eq_fintype_card]
  calc ∑ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)
      ≤ ∑ _𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (1 : ℝ) := by
        refine Finset.sum_le_sum fun 𝔭 _ ↦ Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔭.2.2.2)
    _ = (Fintype.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- **Density of a finite set of primes is `0`** (Sharifi 7.1.13). The numerator
`Σ_{𝔭 ∈ S} N𝔭^{-s}` is bounded (finitely many terms, each `≤ 1`) while the denominator
`Σ_𝔭 N𝔭^{-s} → ∞`, so the ratio `→ 0`. -/
theorem hasDirichletDensity_of_finite {S : Set (Ideal (𝓞 K))} (hS : S.Finite) :
    HasDirichletDensity K S 0 := by
  have hUniv := primeIdealZetaSum_univ_tendsto_atTop K
  have hUnivPos : ∀ᶠ s in 𝓝[>] (1 : ℝ), 0 < primeIdealZetaSum K Set.univ s :=
    hUniv.eventually_gt_atTop 0
  change Tendsto (fun s ↦ primeIdealZetaSum K S s / primeIdealZetaSum K Set.univ s)
    (𝓝[>] 1) (𝓝 0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ ↦ (0 : ℝ))
    (h := fun s ↦ (Nat.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} : ℝ)
      / primeIdealZetaSum K Set.univ s)
    tendsto_const_nhds (tendsto_const_nhds.div_atTop hUniv) ?_ ?_
  · filter_upwards [hUnivPos] with s hpos
    exact div_nonneg (by unfold primeIdealZetaSum; exact tsum_nonneg fun _ ↦ by positivity)
      hpos.le
  · filter_upwards [hUnivPos, self_mem_nhdsWithin] with s hpos hs1
    simp only [Set.mem_Ioi] at hs1
    exact (div_le_div_iff_of_pos_right hpos).mpr
      (primeIdealZetaSum_le_card_of_finite K hS (by linarith))

/-- The Dirichlet density of the set of all (nonzero) prime ideals is `1`: the ratio
`Σ_𝔭 N𝔭⁻ˢ / Σ_𝔭 N𝔭⁻ˢ` is eventually `1` since the denominator is eventually nonzero
(it `→ ∞`). -/
theorem hasDirichletDensity_univ :
    HasDirichletDensity K (Set.univ : Set (Ideal (𝓞 K))) 1 := by
  change Tendsto (fun s ↦ primeIdealZetaSum K Set.univ s / primeIdealZetaSum K Set.univ s)
    (𝓝[>] 1) (𝓝 1)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(primeIdealZetaSum_univ_tendsto_atTop K).eventually_gt_atTop 0] with s hs
  exact (div_self hs.ne').symm

end Chebotarev
