module

public import CebotarevDensity.ForMathlib.LogOneDivSubOne
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.DedekindZeta
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

open Filter NumberField Topology Set

namespace Chebotarev

variable (K : Type*) [Field K] [NumberField K] {S : Set (Ideal (𝓞 K))} {δ : ℝ}

/-- Partial Dirichlet series `Σ_{𝔭 ∈ S} N𝔭^{-s}` over nonzero prime ideals
`𝔭` of `𝓞 K` lying in the set `S`. -/
def primeIdealZetaSum
    (S : Set (Ideal (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)

/-- Equation lemma unfolding `primeIdealZetaSum` to its defining `tsum`. -/
theorem primeIdealZetaSum_def
    (S : Set (Ideal (𝓞 K))) (s : ℝ) :
    primeIdealZetaSum K S s =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := rfl

/-- The Dirichlet density of a set `S` of prime ideals of `𝓞 K` is `δ` when
the ratio of partial sums tends to `δ` as `s ↓ 1`.

Sharifi 7.1.13: `δ(S) = lim_{s → 1⁺} (Σ_{𝔭 ∈ S} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s})`. -/
def HasDirichletDensity
    (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  Tendsto
    (fun s : ℝ ↦ primeIdealZetaSum K S s / primeIdealZetaSum K univ s)
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
    (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  limsup
    (fun s : ℝ ↦ primeIdealZetaSum K S s / primeIdealZetaSum K univ s)
    (𝓝[>] 1) = δ

/-- Lower Dirichlet density (`liminf` of the ratio). See
`HasUpperDirichletDensity` for the convention note: this matches
Sharifi's `δ_inf` notation despite Sharifi's labelling
inversion. -/
def HasLowerDirichletDensity
    (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  liminf
    (fun s : ℝ ↦ primeIdealZetaSum K S s / primeIdealZetaSum K univ s)
    (𝓝[>] 1) = δ

/-- The Dirichlet density of the empty set is `0`. -/
theorem hasDirichletDensity_empty :
    HasDirichletDensity K (∅ : Set (Ideal (𝓞 K))) 0 := by
  have : IsEmpty {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (∅ : Set (Ideal (𝓞 K))) ∧
      𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := ⟨fun x ↦ x.2.1⟩
  simpa only [HasDirichletDensity, primeIdealZetaSum_def, tsum_empty, zero_div]
    using tendsto_const_nhds

/-- If the upper density of `S` equals the lower density of `S` and both equal
`δ`, then the Dirichlet density of `S` is `δ`. (Sandwich criterion used in the
Chebotarev proof: Sharifi 7.2.2 Step 2 last paragraph.) -/
theorem HasDirichletDensity.of_upper_eq_lower
    (hUp : HasUpperDirichletDensity K S δ)
    (hLow : HasLowerDirichletDensity K S δ) :
    HasDirichletDensity K S δ := by
  sorry

/-- The upper Dirichlet density extracted from `HasDirichletDensity`. -/
theorem HasDirichletDensity.hasUpper
    (h : HasDirichletDensity K S δ) :
    HasUpperDirichletDensity K S δ :=
  h.limsup_eq

/-- The lower Dirichlet density extracted from `HasDirichletDensity`. -/
theorem HasDirichletDensity.hasLower
    (h : HasDirichletDensity K S δ) :
    HasLowerDirichletDensity K S δ :=
  h.liminf_eq

/-- The Dirichlet density of a disjoint union is the sum of the densities. -/
theorem HasDirichletDensity.union_of_disjoint
    {T : Set (Ideal (𝓞 K))} (hDisj : Disjoint S T) {ε : ℝ} (hS : HasDirichletDensity K S δ)
    (hT : HasDirichletDensity K T ε) :
    HasDirichletDensity K (S ∪ T) (δ + ε) := by
  sorry

/-- Monotonicity of the lower density under inclusion. -/
theorem HasLowerDirichletDensity.mono
    {T : Set (Ideal (𝓞 K))} (hST : S ⊆ T) {ε : ℝ} (hS : HasLowerDirichletDensity K S δ)
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

include K

/-- Sharifi 7.1.12 proof (p. 140), bounded tail step. The geometric
higher-power tail `Σ_𝔭 N𝔭^{-2s}/(1 - N𝔭^{-s}) = Σ_{𝔭, k≥2} N𝔭^{-ks}` is
bounded on a right neighbourhood of `s = 1` (in fact on `Re s > 1/2`). It
dominates the weighted Euler-product log-tail `Σ_{𝔭, k≥2} N𝔭^{-ks}/k`, so
bounding it suffices for the source's "`log ζ_K(s) ~ Σ_𝔭 N𝔭^{-s}`". -/
theorem primeIdealZetaHigherTail_bounded :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) ≤ C := by
  sorry

/-- Sharifi 7.1.12 proof (p. 140), Euler-product-log identity:
`log ζ_K(s) = Σ_𝔭 N𝔭^{-s} + O(1)` as `s ↓ 1`. The `O(1)` is the
higher-power tail `Σ_{𝔭,k≥2} N𝔭^{-ks}/k`, bounded by
`primeIdealZetaHigherTail_bounded`. Source: "`log ζ_K(s) ~ Σ_𝔭 N𝔭^{-s}`". -/
theorem logDedekindZeta_sub_primeIdealZetaSum_bounded :
    ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ), |Real.log (dedekindZeta K (s : ℂ)).re
      - primeIdealZetaSum K (univ : Set (Ideal (𝓞 K))) s| ≤ C := by
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
  have hF : Tendsto (fun s : ℝ ↦ (s - 1) * (dedekindZeta K (s : ℂ)).re)
      (𝓝[>] (1 : ℝ)) (𝓝 r) := by
    refine ((Complex.continuous_re.tendsto _).comp
      (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)).congr fun s ↦ ?_
    rw [Function.comp_apply, show ((s : ℂ) - 1) = ((s - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
  refine ⟨max |Real.log (r / 2)| |Real.log (2 * r)|, ?_⟩
  have hev : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      (s - 1) * (dedekindZeta K (s : ℂ)).re ∈ Ioo (r / 2) (2 * r) :=
    hF.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hev, self_mem_nhdsWithin] with s hF_s hs1
  simp only [mem_Ioi] at hs1
  have hsm1 : (0 : ℝ) < s - 1 := by linarith
  obtain ⟨hlo, hhi⟩ := hF_s
  have hFpos : (0 : ℝ) < (s - 1) * (dedekindZeta K (s : ℂ)).re := by linarith
  have hζpos : (0 : ℝ) < (dedekindZeta K (s : ℂ)).re := (mul_pos_iff_of_pos_left hsm1).mp hFpos
  rw [one_div, Real.log_inv, sub_neg_eq_add,
    ← Real.log_mul (ne_of_gt hζpos) (ne_of_gt hsm1), mul_comm]
  exact abs_le_max_abs_abs (Real.log_lt_log (by linarith) hlo).le (Real.log_lt_log hFpos hhi).le

/-- Sharifi 7.1.12 proof (p. 140), lower bound:
`log(1/(s-1)) - C ≤ Σ_𝔭 N𝔭^{-s}`. -/
theorem log_minus_bounded_le_primeIdealZetaSum :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      Real.log (1 / (s - 1)) - C
        ≤ primeIdealZetaSum K (univ : Set (Ideal (𝓞 K))) s := by
  obtain ⟨C₁, h₁⟩ := logDedekindZeta_sub_primeIdealZetaSum_bounded K
  obtain ⟨C₂, h₂⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded K
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with s hs₁ hs₂
  linarith [abs_le.mp hs₁, abs_le.mp hs₂]

/-- Sharifi 7.1.12 proof (p. 140), upper bound: `Σ_𝔭 N𝔭^{-s} ≤
log(1/(s-1)) + C'`. -/
theorem primeIdealZetaSum_le_log_plus_bounded :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      primeIdealZetaSum K (univ : Set (Ideal (𝓞 K))) s
        ≤ Real.log (1 / (s - 1)) + C := by
  obtain ⟨C₁, h₁⟩ := logDedekindZeta_sub_primeIdealZetaSum_bounded K
  obtain ⟨C₂, h₂⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded K
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with s hs₁ hs₂
  linarith [abs_le.mp hs₁, abs_le.mp hs₂]

/-- **Sharifi 7.1.12**, *Algebraic Number Theory*, p. 140.

The denominator `Σ_𝔭 N𝔭^{-s}` is asymptotic to `log(1/(s-1))` as `s ↓ 1`.
This is the analytic ingredient that makes the Dirichlet-density
definition robust under the L-function comparisons in the Chebotarev
proof. -/
theorem primeIdealZetaSum_univ_tendsto_log :
    Tendsto
      (fun s : ℝ ↦ primeIdealZetaSum K (univ : Set (Ideal (𝓞 K))) s
        / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 1) :=
  tendsto_ratio_one_of_log_pm_bounded
    (primeIdealZetaSum K (univ : Set (Ideal (𝓞 K))))
    (primeIdealZetaSum_le_log_plus_bounded K)
    (log_minus_bounded_le_primeIdealZetaSum K)

/-- The full prime-ideal zeta sum diverges to `+∞` as `s ↓ 1` (it is asymptotic to
`log(1/(s-1)) → ∞`). -/
theorem primeIdealZetaSum_univ_tendsto_atTop :
    Tendsto (primeIdealZetaSum K (univ : Set (Ideal (𝓞 K)))) (𝓝[>] 1) atTop := by
  have hL := tendsto_log_one_div_sub_one_atTop
  have hhalf : Tendsto (fun s : ℝ ↦ (1 / 2 : ℝ) * Real.log (1 / (s - 1))) (𝓝[>] 1) atTop :=
    hL.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' _ ?_ hhalf
  filter_upwards [(primeIdealZetaSum_univ_tendsto_log K).eventually
      (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)), hL.eventually_gt_atTop 0] with s hs hpos
  exact ((lt_div_iff₀ hpos).mp (mem_Ioi.mp hs)).le

/-- For a finite set `S`, the partial sum `Σ_{𝔭 ∈ S} N𝔭^{-s}` is bounded above by the
number of qualifying primes: there are finitely many terms and each `N𝔭^{-s} ≤ 1`
for `s > 0` (since `N𝔭 ≥ 1`). -/
theorem primeIdealZetaSum_le_card_of_finite (hS : S.Finite)
    {s : ℝ} (hs : 0 < s) :
    primeIdealZetaSum K S s ≤
      Nat.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := by
  have : Finite {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
    (hS.subset fun _ hx ↦ hx.1).to_subtype
  have : Fintype {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := Fintype.ofFinite _
  rw [primeIdealZetaSum_def, tsum_fintype, Nat.card_eq_fintype_card]
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
theorem hasDirichletDensity_of_finite (hS : S.Finite) :
    HasDirichletDensity K S 0 := by
  have hUniv := primeIdealZetaSum_univ_tendsto_atTop K
  have hUnivPos : ∀ᶠ s in 𝓝[>] (1 : ℝ), 0 < primeIdealZetaSum K univ s :=
    hUniv.eventually_gt_atTop 0
  change Tendsto (fun s ↦ primeIdealZetaSum K S s / primeIdealZetaSum K univ s)
    (𝓝[>] 1) (𝓝 0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ ↦ (0 : ℝ))
    (h := fun s ↦ (Nat.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} : ℝ)
      / primeIdealZetaSum K univ s)
    tendsto_const_nhds (tendsto_const_nhds.div_atTop hUniv) ?_ ?_
  · filter_upwards [hUnivPos] with s hpos
    exact div_nonneg (by rw [primeIdealZetaSum_def]; exact tsum_nonneg fun _ ↦ by positivity)
      hpos.le
  · filter_upwards [hUnivPos, self_mem_nhdsWithin] with s hpos hs1
    simp only [mem_Ioi] at hs1
    exact (div_le_div_iff_of_pos_right hpos).mpr
      (primeIdealZetaSum_le_card_of_finite K hS (by linarith))

/-- The Dirichlet density of the set of all (nonzero) prime ideals is `1`: the ratio
`Σ_𝔭 N𝔭⁻ˢ / Σ_𝔭 N𝔭⁻ˢ` is eventually `1` since the denominator is eventually nonzero
(it `→ ∞`). -/
theorem hasDirichletDensity_univ : HasDirichletDensity K (univ : Set (Ideal (𝓞 K))) 1 := by
  change Tendsto (fun s ↦ primeIdealZetaSum K univ s / primeIdealZetaSum K univ s)
    (𝓝[>] 1) (𝓝 1)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(primeIdealZetaSum_univ_tendsto_atTop K).eventually_gt_atTop 0] with s hs
  exact (div_self hs.ne').symm

end Chebotarev
