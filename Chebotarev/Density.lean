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
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Ideal (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)

/-- The Dirichlet density of a set `S` of prime ideals of `𝓞 K` is `δ` when
the ratio of partial sums tends to `δ` as `s ↓ 1`.

Sharifi 7.1.13: `δ(S) = lim_{s → 1⁺} (Σ_{𝔭 ∈ S} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s})`. -/
def HasDirichletDensity
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  Tendsto
    (fun s : ℝ ↦ primeIdealZetaSum K S s / primeIdealZetaSum K Set.univ s)
    (𝓝[>] 1) (𝓝 δ)

/-- Upper Dirichlet density. -/
def HasUpperDirichletDensity
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  Filter.limsup
    (fun s : ℝ ↦ primeIdealZetaSum K S s / primeIdealZetaSum K Set.univ s)
    (𝓝[>] 1) = δ

/-- Lower Dirichlet density. -/
def HasLowerDirichletDensity
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  Filter.liminf
    (fun s : ℝ ↦ primeIdealZetaSum K S s / primeIdealZetaSum K Set.univ s)
    (𝓝[>] 1) = δ

variable (K : Type*) [Field K] [NumberField K]

/-- The Dirichlet density of the empty set is `0`. -/
theorem hasDirichletDensity_empty :
    HasDirichletDensity K (∅ : Set (Ideal (𝓞 K))) 0 := by
  sorry

/-- The Dirichlet density of the set of all (nonzero) prime ideals is `1`. -/
theorem hasDirichletDensity_univ :
    HasDirichletDensity K (Set.univ : Set (Ideal (𝓞 K))) 1 := by
  sorry

/-- Density of a finite set of primes is `0`. -/
theorem hasDirichletDensity_of_finite
    {S : Set (Ideal (𝓞 K))} (hS : S.Finite) : HasDirichletDensity K S 0 := by
  sorry

/-- If the upper density of `S` equals the lower density of `S` and both equal
`δ`, then the Dirichlet density of `S` is `δ`. (Sandwich criterion used in the
Chebotarev proof: Sharifi 7.2.2 Step 2 last paragraph.) -/
theorem HasDirichletDensity.of_upper_eq_lower
    {S : Set (Ideal (𝓞 K))} {δ : ℝ}
    (hUp : HasUpperDirichletDensity K S δ)
    (hLow : HasLowerDirichletDensity K S δ) :
    HasDirichletDensity K S δ := by
  sorry

/-- Existence + value: from `HasDirichletDensity` one extracts the upper and
lower density. -/
theorem HasDirichletDensity.hasUpper
    {S : Set (Ideal (𝓞 K))} {δ : ℝ} (h : HasDirichletDensity K S δ) :
    HasUpperDirichletDensity K S δ := by
  sorry

theorem HasDirichletDensity.hasLower
    {S : Set (Ideal (𝓞 K))} {δ : ℝ} (h : HasDirichletDensity K S δ) :
    HasLowerDirichletDensity K S δ := by
  sorry

/-- Finite disjoint additivity. -/
theorem HasDirichletDensity.union_of_disjoint
    {S T : Set (Ideal (𝓞 K))} (hDisj : Disjoint S T) {δ ε : ℝ}
    (hS : HasDirichletDensity K S δ) (hT : HasDirichletDensity K T ε) :
    HasDirichletDensity K (S ∪ T) (δ + ε) := by
  sorry

/-- Monotonicity of the lower density under inclusion. -/
theorem HasLowerDirichletDensity.mono
    {S T : Set (Ideal (𝓞 K))} (hST : S ⊆ T) {δ ε : ℝ}
    (hS : HasLowerDirichletDensity K S δ) (hT : HasLowerDirichletDensity K T ε) :
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
(iii) Comparison `Σ_𝔭 N𝔭^{-s} ≤ [K:ℚ] Σ_p p^{-s}` from the bound
    "at most `[K:ℚ]` primes of `𝓞 K` lie over each rational prime"
    (Sharifi 7.1.12 proof: "the latter sum is at most [K:ℚ] Σ_p p^{-s}").
(iv) `log ζ_K(s) ~ log(1/(s-1))` from the simple pole of `ζ_K` at `s=1`
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

/-- Sharifi 7.1.12 proof (p. 140), comparison step: each rational prime `p`
has at most `[K:ℚ]` primes of `𝓞 K` lying above it, so
`Σ_𝔭 N𝔭^{-s} ≤ [K:ℚ] Σ_p p^{-s}`. Source quote: "the latter sum is at most
`[K:ℚ] Σ_p p^{-s}`". -/
theorem primeIdealZetaSum_le_finrank_smul_riemannPrimeSum :
    ∀ᶠ s in 𝓝[>] (1 : ℝ),
      primeIdealZetaSum K (Set.univ : Set (Ideal (𝓞 K))) s
        ≤ (Module.finrank ℚ K : ℝ)
          * ∑' p : Nat.Primes, (p.1 : ℝ) ^ (-s) := by
  sorry

/-- Sharifi 7.1.12 (case `K = ℚ`, p. 139–140): the Riemann prime sum is
asymptotic to `log(1/(s-1))` as `s ↓ 1`. This is the analytic input that
the general case immediately above reduces to. -/
theorem riemannPrimeSum_asymp_log :
    Tendsto
      (fun s : ℝ ↦ (∑' p : Nat.Primes, (p.1 : ℝ) ^ (-s))
        / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 1) := by
  sorry

/-- Sharifi 7.1.12 proof (p. 140), lower bound: from the simple pole of
`ζ_K` at `s=1`
(`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`) one extracts
`Σ_𝔭 N𝔭^{-s} ≥ log(1/(s-1)) - C`. Pair with
`primeIdealZetaSum_le_log_plus_bounded` for the sandwich. -/
theorem primeIdealZetaSum_ge_log_minus_bounded :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      primeIdealZetaSum K (Set.univ : Set (Ideal (𝓞 K))) s
        ≥ Real.log (1 / (s - 1)) - C := by
  sorry

/-- Sharifi 7.1.12 proof (p. 140), upper bound: from the same simple pole
+ the higher-power tail bound, one extracts
`Σ_𝔭 N𝔭^{-s} ≤ log(1/(s-1)) + C'`. The proof is
`log ζ_K = Σ_𝔭 N𝔭^{-s} + (bounded tail) = log(1/(s-1)) + (bounded)`,
which by transposition gives the bound. -/
theorem primeIdealZetaSum_le_log_plus_bounded :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      primeIdealZetaSum K (Set.univ : Set (Ideal (𝓞 K))) s
        ≤ Real.log (1 / (s - 1)) + C := by
  sorry

/-- Generic squeeze: if `f(s) = log(1/(s-1)) + bounded` on a right
neighbourhood of `1`, then `f(s) / log(1/(s-1)) → 1` as `s ↓ 1`. The
analytic content is just that `log(1/(s-1)) → ∞`, so the additive
bounded term washes out under division. -/
theorem tendsto_ratio_one_of_log_pm_bounded
    (f : ℝ → ℝ)
    (h_le : ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), f s ≤ Real.log (1 / (s - 1)) + C)
    (h_ge : ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), f s ≥ Real.log (1 / (s - 1)) - C) :
    Tendsto (fun s : ℝ ↦ f s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 1) := by
  sorry

/-- **Sharifi 7.1.12**, *Algebraic Number Theory*, p. 140.

The denominator `Σ_𝔭 N𝔭^{-s}` is asymptotic to `log(1/(s-1))` as `s ↓ 1`.
This is the analytic ingredient that makes the Dirichlet-density
definition robust under the L-function comparisons in the Chebotarev
proof.

**Composition**: sandwich the two bounds. From
`primeIdealZetaSum_ge_log_minus_bounded` and
`primeIdealZetaSum_le_log_plus_bounded`,
`Σ_𝔭 N𝔭^{-s} = log(1/(s-1)) + O(1)`; dividing by `log(1/(s-1))`
(which → ∞ as `s ↓ 1`) gives a ratio that → 1 by
`tendsto_ratio_one_of_log_pm_bounded`. -/
theorem primeIdealZetaSum_univ_tendsto_log :
    Tendsto
      (fun s : ℝ ↦ primeIdealZetaSum K (Set.univ : Set (Ideal (𝓞 K))) s
        / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 1) :=
  tendsto_ratio_one_of_log_pm_bounded
    (primeIdealZetaSum K (Set.univ : Set (Ideal (𝓞 K))))
    (primeIdealZetaSum_le_log_plus_bounded K)
    (primeIdealZetaSum_ge_log_minus_bounded K)

end Chebotarev
