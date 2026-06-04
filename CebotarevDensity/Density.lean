module

public import CebotarevDensity.ForMathlib.LogOneDivSubOne
public import CebotarevDensity.NumberFieldEulerProduct
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Order.LiminfLimsup

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

variable {K : Type*} [Field K] [NumberField K] {S : Set (Ideal (𝓞 K))} {δ : ℝ}

/-- Partial Dirichlet series `Σ_{𝔭 ∈ S} N𝔭^{-s}` over nonzero prime ideals
`𝔭` of `𝓞 K` lying in the set `S`. -/
def primeIdealZetaSum (S : Set (Ideal (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)

/-- Equation lemma unfolding `primeIdealZetaSum` to its defining `tsum`. -/
theorem primeIdealZetaSum_def (S : Set (Ideal (𝓞 K))) (s : ℝ) :
    primeIdealZetaSum S s =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := rfl

/-- The Dirichlet density of a set `S` of prime ideals of `𝓞 K` is `δ` when
the ratio of partial sums tends to `δ` as `s ↓ 1`.

Sharifi 7.1.13: `δ(S) = lim_{s → 1⁺} (Σ_{𝔭 ∈ S} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s})`. -/
def HasDirichletDensity (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  Tendsto
    (fun s : ℝ ↦ primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s)
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
def HasUpperDirichletDensity (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  limsup
    (fun s : ℝ ↦ primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s)
    (𝓝[>] 1) = δ

/-- Lower Dirichlet density (`liminf` of the ratio). See
`HasUpperDirichletDensity` for the convention note: this matches
Sharifi's `δ_inf` notation despite Sharifi's labelling
inversion. -/
def HasLowerDirichletDensity (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  liminf
    (fun s : ℝ ↦ primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s)
    (𝓝[>] 1) = δ

/-- The Dirichlet density of the empty set is `0`. -/
theorem hasDirichletDensity_empty :
    HasDirichletDensity (∅ : Set (Ideal (𝓞 K))) 0 := by
  have : IsEmpty {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (∅ : Set (Ideal (𝓞 K))) ∧
      𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := ⟨fun x ↦ x.2.1⟩
  simpa only [HasDirichletDensity, primeIdealZetaSum_def, tsum_empty, zero_div]
    using tendsto_const_nhds

/-- Over the nonzero ideals of `𝓞 K`, the series `Σ_I N(I)^{-s}` is summable for
`1 < s`. Grouping by norm value, the fibre `{I : N(I) = n}` is finite and the
fibre-sum series is the (real, norm-grouped) tail of the Dedekind zeta series,
summable by `summable_idealNormMultiplicity_mul_cpow_neg`. -/
private theorem summable_nonzeroIdeal_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s)) := by
  have hf_nonneg : ∀ I : NonzeroIdeal K, 0 ≤ (Ideal.absNorm I.1 : ℝ) ^ (-s) :=
    fun I => Real.rpow_nonneg (by positivity) _
  have hfiber : ∀ n : ℕ, Finite {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} := fun n =>
    Set.Finite.to_subtype <| Set.Finite.of_finite_image
      (f := fun I : NonzeroIdeal K => I.1)
      ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset
        (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
      (fun _ _ _ _ => Subtype.ext)
  have hfiber_sum : ∀ n : ℕ,
      (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n}, (Ideal.absNorm (y.1).1 : ℝ) ^ (-s))
        = ‖(idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : IsEmpty {I : NonzeroIdeal K // Ideal.absNorm I.1 = 0} :=
        ⟨fun y => y.1.2 (Ideal.absNorm_eq_zero_iff.mp y.2)⟩
      simp [idealNormMultiplicity_zero]
    · have hconst : ∀ y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
          (Ideal.absNorm (y.1).1 : ℝ) ^ (-s) = (n : ℝ) ^ (-s) := fun y => by rw [y.2]
      rw [tsum_congr hconst, tsum_const, norm_mul, Complex.norm_natCast,
        Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re, Complex.ofReal_re, nsmul_eq_mul,
        idealNormMultiplicity]
  rw [← (Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal K => Ideal.absNorm I.1)).summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => hf_nonneg _)).mpr ⟨fun _ => Summable.of_finite, ?_⟩
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  exact (summable_idealNormMultiplicity_mul_cpow_neg K hs').congr (fun n => (hfiber_sum n).symm)

/-- Over the nonzero prime ideals of `𝓞 K` lying in any set `S`, the series
`Σ_𝔭 N𝔭^{-s}` is summable for `1 < s`: the prime subtype injects into the
nonzero-ideal type, where summability holds by
`summable_nonzeroIdeal_absNorm_rpow`. -/
private theorem summable_prime_absNorm_rpow (S : Set (Ideal (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) := by
  have hi : Function.Injective
      (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
        (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal K)) :=
    fun a b hab => Subtype.ext (Subtype.mk_eq_mk.mp hab)
  exact ((summable_nonzeroIdeal_absNorm_rpow hs).comp_injective hi).congr fun _ => rfl

/-- The partial Dirichlet series is nonnegative: it is a `tsum` of nonnegative
terms `N𝔭^{-s} ≥ 0`. -/
private theorem primeIdealZetaSum_nonneg (S : Set (Ideal (𝓞 K))) (s : ℝ) :
    0 ≤ primeIdealZetaSum S s := by
  rw [primeIdealZetaSum_def]
  exact tsum_nonneg fun _ => Real.rpow_nonneg (by positivity) _

/-- The partial Dirichlet series over `S` is bounded above by the one over all
primes, for `1 < s`: the `S`-prime subtype injects into the universal prime
subtype, the terms agree, and both families are summable. -/
private theorem primeIdealZetaSum_le_univ {s : ℝ} (hs : 1 < s) :
    primeIdealZetaSum S s ≤ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def]
  refine (summable_prime_absNorm_rpow S hs).tsum_le_tsum_of_inj
    (fun 𝔭 => ⟨𝔭.1, ⟨mem_univ _, 𝔭.2.2.1, 𝔭.2.2.2⟩⟩)
    (fun a b hab => Subtype.ext (Subtype.mk_eq_mk.mp hab))
    (fun c _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun 𝔭 => le_of_eq rfl) (summable_prime_absNorm_rpow (univ : Set (Ideal (𝓞 K))) hs)

/-- The partial Dirichlet series over `S ⊆ T` is bounded above by the one over
`T`, for `1 < s`: the `S`-prime subtype injects into the `T`-prime subtype, the
terms agree, and both families are summable. -/
private theorem primeIdealZetaSum_le_of_subset {T : Set (Ideal (𝓞 K))} (hST : S ⊆ T) {s : ℝ}
    (hs : 1 < s) :
    primeIdealZetaSum S s ≤ primeIdealZetaSum T s := by
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def]
  refine (summable_prime_absNorm_rpow S hs).tsum_le_tsum_of_inj
    (fun 𝔭 => ⟨𝔭.1, hST 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩)
    (fun a b hab => Subtype.ext (Subtype.mk_eq_mk.mp hab))
    (fun c _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun 𝔭 => le_of_eq rfl) (summable_prime_absNorm_rpow T hs)

/-- For disjoint `S` and `T`, the partial Dirichlet series over `S ∪ T` splits
as the sum of those over `S` and `T`, for `1 < s`: the union-prime subtype is the
disjoint union (via the membership-in-`S` set and its complement) of the
`S`-prime and `T`-prime subtypes, so the `tsum` splits by
`tsum_subtype_add_tsum_subtype_compl`. -/
theorem primeIdealZetaSum_union_of_disjoint {T : Set (Ideal (𝓞 K))} (hDisj : Disjoint S T)
    {s : ℝ} (hs : 1 < s) :
    primeIdealZetaSum (S ∪ T) s = primeIdealZetaSum S s + primeIdealZetaSum T s := by
  let eS : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
      ↑{x : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 K)) ∈ S} :=
    { toFun := fun 𝔭 => ⟨⟨𝔭.1, Or.inl 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩, 𝔭.2.1⟩
      invFun := fun x => ⟨x.1.1, x.2, x.1.2.2.1, x.1.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eT : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
      ↑{x : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 K)) ∈ S}ᶜ :=
    { toFun := fun 𝔭 => ⟨⟨𝔭.1, Or.inr 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩,
        fun h => hDisj.le_bot ⟨h, 𝔭.2.1⟩⟩
      invFun := fun x => ⟨x.1.1, x.1.2.1.resolve_left x.2, x.1.2.2.1, x.1.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def, primeIdealZetaSum_def,
    ← (summable_prime_absNorm_rpow (S ∪ T) hs).tsum_subtype_add_tsum_subtype_compl
      {x | (x.1 : Ideal (𝓞 K)) ∈ S},
    ← eS.tsum_eq (fun x => (Ideal.absNorm (x.1 : Ideal (𝓞 K)) : ℝ) ^ (-s)),
    ← eT.tsum_eq (fun x => (Ideal.absNorm (x.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))]
  rfl

/-- The partial Dirichlet series over the empty set is `0`. -/
theorem primeIdealZetaSum_empty (s : ℝ) : primeIdealZetaSum (∅ : Set (Ideal (𝓞 K))) s = 0 := by
  have : IsEmpty {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (∅ : Set (Ideal (𝓞 K))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
    ⟨fun x => x.2.1⟩
  rw [primeIdealZetaSum_def, tsum_empty]

/-- The partial Dirichlet series over a `Finset`-indexed pairwise-disjoint family
`⋃ i ∈ t, g i` splits as the finite sum `∑ i ∈ t, primeIdealZetaSum (g i)`, for
`1 < s`. Proved by induction on `t` from the two-set case
`primeIdealZetaSum_union_of_disjoint`. -/
theorem primeIdealZetaSum_biUnion_of_pairwiseDisjoint {ι : Type*} (t : Finset ι)
    (g : ι → Set (Ideal (𝓞 K))) (hg : (t : Set ι).PairwiseDisjoint g) {s : ℝ} (hs : 1 < s) :
    primeIdealZetaSum (⋃ i ∈ t, g i) s = ∑ i ∈ t, primeIdealZetaSum (g i) s := by
  classical
  induction t using Finset.induction with
  | empty => simp [primeIdealZetaSum_empty]
  | insert a t ha ih =>
      have hdisj : Disjoint (g a) (⋃ i ∈ t, g i) :=
        disjoint_iUnion₂_right.2 fun i hi =>
          hg (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hi)
            (fun h => ha (h ▸ hi))
      rw [Finset.set_biUnion_insert, primeIdealZetaSum_union_of_disjoint hdisj hs,
        Finset.sum_insert ha, ih (hg.subset (Finset.coe_subset.mpr (Finset.subset_insert a t)))]

/-- If `S` contains every nonzero prime ideal of `𝓞 K`, then its partial Dirichlet
series agrees with the one over `univ`: the defining `tsum`s run over the same
subtype (membership in `S` is implied for every nonzero prime). -/
theorem primeIdealZetaSum_eq_univ_of_forall_prime_mem
    (hS : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭 ∈ S) (s : ℝ) :
    primeIdealZetaSum S s = primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
  let e : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
      {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (univ : Set (Ideal (𝓞 K))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
    { toFun := fun 𝔭 => ⟨𝔭.1, mem_univ _, 𝔭.2.2.1, 𝔭.2.2.2⟩
      invFun := fun 𝔭 => ⟨𝔭.1, hS 𝔭.1 𝔭.2.2.1 𝔭.2.2.2, 𝔭.2.2.1, 𝔭.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def,
    ← e.tsum_eq (fun 𝔭 => (Ideal.absNorm (𝔭.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))]
  rfl

/-- If the upper density of `S` equals the lower density of `S` and both equal
`δ`, then the Dirichlet density of `S` is `δ`. (Sandwich criterion used in the
Chebotarev proof: Sharifi 7.2.2 Step 2 last paragraph.) -/
theorem HasDirichletDensity.of_upper_eq_lower
    (hUp : HasUpperDirichletDensity S δ)
    (hLow : HasLowerDirichletDensity S δ) :
    HasDirichletDensity S δ := by
  refine tendsto_of_liminf_eq_limsup hLow hUp ?_ ?_
  · refine ⟨1, ?_⟩
    rw [eventually_map]
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [mem_Ioi] at hs
    exact div_le_one_of_le₀ (primeIdealZetaSum_le_univ hs)
      (primeIdealZetaSum_nonneg (univ : Set (Ideal (𝓞 K))) s)
  · exact isBoundedUnder_of ⟨0, fun s =>
      div_nonneg (primeIdealZetaSum_nonneg S s)
        (primeIdealZetaSum_nonneg (univ : Set (Ideal (𝓞 K))) s)⟩

/-- The upper Dirichlet density extracted from `HasDirichletDensity`. -/
theorem HasDirichletDensity.hasUpper
    (h : HasDirichletDensity S δ) :
    HasUpperDirichletDensity S δ :=
  h.limsup_eq

/-- The lower Dirichlet density extracted from `HasDirichletDensity`. -/
theorem HasDirichletDensity.hasLower
    (h : HasDirichletDensity S δ) :
    HasLowerDirichletDensity S δ :=
  h.liminf_eq

/-- The Dirichlet density of a disjoint union is the sum of the densities. -/
theorem HasDirichletDensity.union_of_disjoint
    {T : Set (Ideal (𝓞 K))} (hDisj : Disjoint S T) {ε : ℝ} (hS : HasDirichletDensity S δ)
    (hT : HasDirichletDensity T ε) :
    HasDirichletDensity (S ∪ T) (δ + ε) := by
  rw [HasDirichletDensity] at hS hT ⊢
  refine (hS.add hT).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [mem_Ioi] at hs
  rw [primeIdealZetaSum_union_of_disjoint hDisj hs, add_div]

/-- Monotonicity of the lower density under inclusion. -/
theorem HasLowerDirichletDensity.mono
    {T : Set (Ideal (𝓞 K))} (hST : S ⊆ T) {ε : ℝ} (hS : HasLowerDirichletDensity S δ)
    (hT : HasLowerDirichletDensity T ε) :
    δ ≤ ε := by
  rw [HasLowerDirichletDensity] at hS hT
  rw [← hS, ← hT]
  refine liminf_le_liminf ?_ ?_ (isCoboundedUnder_ge_of_eventually_le (x := 1) _ ?_)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [mem_Ioi] at hs
    exact div_le_div_of_nonneg_right (primeIdealZetaSum_le_of_subset hST hs)
      (primeIdealZetaSum_nonneg (univ : Set (Ideal (𝓞 K))) s)
  · exact isBoundedUnder_of ⟨0, fun s =>
      div_nonneg (primeIdealZetaSum_nonneg S s)
        (primeIdealZetaSum_nonneg (univ : Set (Ideal (𝓞 K))) s)⟩
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [mem_Ioi] at hs
    exact div_le_one_of_le₀ (primeIdealZetaSum_le_univ hs)
      (primeIdealZetaSum_nonneg (univ : Set (Ideal (𝓞 K))) s)

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

variable (K)

/-- Over the nonzero prime ideals of `𝓞 K` (the 2-part subtype, no ambient set),
the series `Σ_𝔭 N𝔭^{-s}` is summable for `1 < s`: transport
`summable_prime_absNorm_rpow K univ` along the equivalence dropping the trivial
`𝔭 ∈ univ` component. -/
private theorem summable_prime2_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) := by
  have hi : Function.Injective
      (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
        (⟨𝔭.1, mem_univ _, 𝔭.2.1, 𝔭.2.2⟩ :
          {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ univ ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})) :=
    fun a b hab => Subtype.ext (Subtype.mk_eq_mk.mp hab)
  exact ((summable_prime_absNorm_rpow (univ : Set (Ideal (𝓞 K))) hs).comp_injective hi).congr
    fun _ => rfl

/-- A nonzero prime ideal of `𝓞 K` has absolute norm at least `2`: it is neither
`⊥` (norm `0`, by `Ideal.absNorm_eq_zero_iff`) nor `⊤` (norm `1`, by
`Ideal.absNorm_eq_one_iff`), so its positive natural norm is `≠ 1`. -/
private theorem two_le_absNorm_of_prime {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) :
    (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ) := by
  have h0 : Ideal.absNorm 𝔭 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have h1 : Ideal.absNorm 𝔭 ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hp.ne_top
  exact_mod_cast show (2 : ℕ) ≤ Ideal.absNorm 𝔭 by lia

/-- Per-prime termwise bound for the higher-power tail. For `1 < s` and a nonzero
prime `𝔭` (so `2 ≤ N𝔭`), the geometric term is dominated by `2·N𝔭^{-2}`:
`N𝔭^{-s} ≤ 2^{-s} ≤ 1/2` makes the denominator `≥ 1/2`, and `N𝔭^{-2s} ≤ N𝔭^{-2}`
since the base is `≥ 1` and `-2s ≤ -2`. -/
private theorem primeIdealHigherTail_term_le {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥)
    {s : ℝ} (hs : 1 < s) :
    (Ideal.absNorm 𝔭 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭 : ℝ) ^ (-s)) ≤
      2 * (Ideal.absNorm 𝔭 : ℝ) ^ (-(2 : ℝ)) := by
  set x : ℝ := (Ideal.absNorm 𝔭 : ℝ)
  have hx : (2 : ℝ) ≤ x := two_le_absNorm_of_prime K hp hne
  have hx0 : (0 : ℝ) < x := by linarith
  have hxs_le : x ^ (-s) ≤ (2 : ℝ) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos zero_lt_two hx (by linarith)
  have h2s_le : (2 : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have h2half : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  have hxs_half : x ^ (-s) ≤ 1 / 2 := by rw [← h2half]; exact le_trans hxs_le h2s_le
  have hden_pos : (0 : ℝ) < 1 - x ^ (-s) := by linarith
  have hinv_le : (1 - x ^ (-s))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hden_pos (by norm_num)]; linarith
  have hexp : x ^ (-(2 : ℝ) * s) ≤ x ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
  have hx2_nonneg : (0 : ℝ) ≤ x ^ (-(2 : ℝ)) := Real.rpow_nonneg hx0.le _
  rw [div_eq_mul_inv]
  calc x ^ (-(2 : ℝ) * s) * (1 - x ^ (-s))⁻¹
      ≤ x ^ (-(2 : ℝ)) * 2 := mul_le_mul hexp hinv_le (by positivity) hx2_nonneg
    _ = 2 * x ^ (-(2 : ℝ)) := by ring

/-- Sharifi 7.1.12 proof (p. 140), bounded tail step. The geometric
higher-power tail `Σ_𝔭 N𝔭^{-2s}/(1 - N𝔭^{-s}) = Σ_{𝔭, k≥2} N𝔭^{-ks}` is
bounded on a right neighbourhood of `s = 1` (in fact on `Re s > 1/2`). It
dominates the weighted Euler-product log-tail `Σ_{𝔭, k≥2} N𝔭^{-ks}/k`, so
bounding it suffices for the source's "`log ζ_K(s) ~ Σ_𝔭 N𝔭^{-s}`". -/
theorem primeIdealZetaHigherTail_bounded :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) ≤ C := by
  refine ⟨2 * ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ)), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [mem_Ioi] at hs
  have hbound : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) ≤
        2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ)) := fun 𝔭 =>
    primeIdealHigherTail_term_le K 𝔭.2.1 𝔭.2.2 hs
  have hnonneg : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (0 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) :=
    fun 𝔭 => by
      have hx : (2 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := two_le_absNorm_of_prime K 𝔭.2.1 𝔭.2.2
      have hden_pos : (0 : ℝ) < 1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := by
        have := Real.rpow_lt_one_of_one_lt_of_neg (x := (Ideal.absNorm 𝔭.1 : ℝ))
          (by linarith) (by linarith : -s < 0)
        linarith
      exact div_nonneg (Real.rpow_nonneg (by positivity) _) hden_pos.le
  have hsummable_rhs : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
      2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ))) :=
    (summable_prime2_absNorm_rpow K one_lt_two).mul_left 2
  have hsummable_lhs : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))) :=
    Summable.of_nonneg_of_le hnonneg hbound hsummable_rhs
  calc ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))
      ≤ ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
          2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ)) :=
        hsummable_lhs.tsum_le_tsum hbound hsummable_rhs
    _ = 2 * ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
          (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ)) := tsum_mul_left

/-- Sharifi 7.1.12 proof (p. 140), Euler-product-log identity:
`log ζ_K(s) = Σ_𝔭 N𝔭^{-s} + O(1)` as `s ↓ 1`. The `O(1)` is the
higher-power tail `Σ_{𝔭,k≥2} N𝔭^{-ks}/k`, bounded by
`primeIdealZetaHigherTail_bounded`. Source: "`log ζ_K(s) ~ Σ_𝔭 N𝔭^{-s}`". -/
theorem logDedekindZeta_sub_primeIdealZetaSum_bounded :
    ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ), |Real.log (dedekindZeta K (s : ℂ)).re
      - primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s| ≤ C := by
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
        ≤ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
  obtain ⟨C₁, h₁⟩ := logDedekindZeta_sub_primeIdealZetaSum_bounded K
  obtain ⟨C₂, h₂⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded K
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with s hs₁ hs₂
  linarith [abs_le.mp hs₁, abs_le.mp hs₂]

/-- Sharifi 7.1.12 proof (p. 140), upper bound: `Σ_𝔭 N𝔭^{-s} ≤
log(1/(s-1)) + C'`. -/
theorem primeIdealZetaSum_le_log_plus_bounded :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s
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
      (fun s : ℝ ↦ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s
        / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 1) :=
  tendsto_ratio_one_of_log_pm_bounded
    (primeIdealZetaSum (univ : Set (Ideal (𝓞 K))))
    (primeIdealZetaSum_le_log_plus_bounded K)
    (log_minus_bounded_le_primeIdealZetaSum K)

/-- The full prime-ideal zeta sum diverges to `+∞` as `s ↓ 1` (it is asymptotic to
`log(1/(s-1)) → ∞`). -/
theorem primeIdealZetaSum_univ_tendsto_atTop :
    Tendsto (primeIdealZetaSum (univ : Set (Ideal (𝓞 K)))) (𝓝[>] 1) atTop := by
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
    primeIdealZetaSum S s ≤
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
    HasDirichletDensity S 0 := by
  have hUniv := primeIdealZetaSum_univ_tendsto_atTop K
  have hUnivPos : ∀ᶠ s in 𝓝[>] (1 : ℝ), 0 < primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s :=
    hUniv.eventually_gt_atTop 0
  change Tendsto (fun s ↦ primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s)
    (𝓝[>] 1) (𝓝 0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ ↦ (0 : ℝ))
    (h := fun s ↦ (Nat.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} : ℝ)
      / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s)
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
theorem hasDirichletDensity_univ : HasDirichletDensity (univ : Set (Ideal (𝓞 K))) 1 := by
  change Tendsto (fun s ↦ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s
    / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s) (𝓝[>] 1) (𝓝 1)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(primeIdealZetaSum_univ_tendsto_atTop K).eventually_gt_atTop 0] with s hs
  exact (div_self hs.ne').symm

end Chebotarev
