module

public import CebotarevDensity.Frobenius
public import CebotarevDensity.ForMathlib.LatticePointCount
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Zeta factorisation for an abelian extension

For an abelian Galois extension `L/K` of number fields, the Dedekind zeta
function `ζ_L(s)` factors as a product of Artin L-functions over the
characters of `Gal(L/K)`:

  ζ_L(s) = ∏_{χ : Gal(L/K) → ℂ^×} L(χ, s)   on Re s > 1.

The character `χ` is extended to a character on nonzero ideals of `𝓞 K` by
`χ(𝔭) = χ(σ_𝔭)` for `𝔭` unramified in `L`, and `0` otherwise. The
nontrivial-`χ` L-function is holomorphic and nonvanishing on `Re s ≥ 1`
(Sharifi §7.1.19); the trivial-character L-function is `ζ_K(s)`.

This factorisation is the analytic engine of the Chebotarev proof for the
cyclotomic case.

This file does **not** introduce a top-level `artinLSeries` definition —
the L-functions enter the argument only via existence statements packaged
as the theorems below, with the Euler-product / Dirichlet-series content
of each `L(χ, ·)` being an internal detail of the proof of
`dedekindZeta_eq_prod_artinLSeries`. The user can read the proof to see
how each `L(χ, ·)` is constructed.

## Main results

* `Chebotarev.exists_artinLSeries_eulerProduct_abelian` — the Euler product
  `L(χ,s) = ∏_𝔭 (1 - χ(𝔭) N𝔭⁻ˢ)⁻¹ = Σ_𝔞 χ(𝔞) N𝔞⁻ˢ` of an abelian character
  (Sharifi 7.1.18), with `χ(𝔞)` the multiplicative `galoisCharacterOnIdeal`.
* `Chebotarev.dedekindZeta_local_factor_eq_product_artin_local` — the local
  factorisation of `ζ_L` into Artin local factors at an unramified prime
  (Sharifi 7.1.16).
* `Chebotarev.artinLSeries_one_ne_zero` — non-vanishing `L(χ,1) ≠ 0` for
  nontrivial `χ`, via the pole-order argument (Sharifi 7.1.19 step 2), modulo
  the geometry-of-numbers analytic extension `artinLSeries_analytic_extension`.

## References

* Sharifi, *Algebraic Number Theory*, §7.1.15–7.1.19 (`docs/algnum.pdf`).
* The analogous factorisation for the prime cyclotomic field `ℚ(μ_p)/ℚ`
  is available in `flt-regular-bernoulli`'s
  `BernoulliRegular.ZetaFactorisation.EulerProduct`; this module
  generalises it to an arbitrary abelian extension `L/K`.
-/

@[expose] public section

noncomputable section

open NumberField

namespace Chebotarev

/-- A character of `Gal(L/K)` valued in `ℂ^×`. -/
abbrev galoisCharacter
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    Type _ := Gal(L/K) →* ℂˣ

open Classical in
/-- The multiplicative extension of a Galois character `χ` to the nonzero ideals of `𝓞 K`
(Sharifi Notation 7.1.17): on a prime `𝔭` it is `χ(Frob 𝔭)` if `𝔭` is unramified in `L` and `0`
otherwise, extended completely multiplicatively via the prime factorisation. The L-function
coefficient `χ(𝔞)`. -/
noncomputable def galoisCharacterOnIdeal (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] (χ : galoisCharacter K L) (𝔞 : Ideal (𝓞 K)) : ℂ :=
  ∏ 𝔭 ∈ (UniqueFactorizationMonoid.normalizedFactors 𝔞).toFinset,
    (if UnramifiedIn K L 𝔭 then (χ (frobeniusClass K L 𝔭).out : ℂ) else 0)
      ^ (UniqueFactorizationMonoid.normalizedFactors 𝔞).count 𝔭

open Classical in
/-- `galoisCharacterOnIdeal` written as the product over the prime factors **with
multiplicity** — i.e. a `Multiset.map`-product over `normalizedFactors 𝔞` — rather than the
`toFinset`+`count` form of the definition. This form makes the multiplicativity proof immediate
(`Multiset.map_add` + `Multiset.prod_add`). -/
private theorem galoisCharacterOnIdeal_eq_map_prod
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (𝔞 : Ideal (𝓞 K)) :
    galoisCharacterOnIdeal K L χ 𝔞 =
      ((UniqueFactorizationMonoid.normalizedFactors 𝔞).map
        (fun 𝔭 => if UnramifiedIn K L 𝔭 then (χ (frobeniusClass K L 𝔭).out : ℂ) else 0)).prod := by
  rw [galoisCharacterOnIdeal, Finset.prod_multiset_map_count]

open Classical in
/-- On a nonzero prime `𝔭`, the ideal character `χ(𝔭)` is `χ(Frob 𝔭)` when `𝔭` is unramified in
`L` and `0` otherwise (Sharifi Notation 7.1.17). The hypothesis `𝔭 ≠ ⊥` is needed: at the zero
ideal the product is the empty product `1`, whereas the right-hand side is `0` (the zero ideal
is never unramified). -/
theorem galoisCharacterOnIdeal_apply_prime
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) :
    galoisCharacterOnIdeal K L χ 𝔭 =
      if UnramifiedIn K L 𝔭 then (χ (frobeniusClass K L 𝔭).out : ℂ) else 0 := by
  rw [galoisCharacterOnIdeal_eq_map_prod, UniqueFactorizationMonoid.normalizedFactors_irreducible
    (Ideal.prime_of_isPrime h𝔭 ‹_›).irreducible, normalize_eq, Multiset.map_singleton,
    Multiset.prod_singleton]

/-- The ideal character is completely multiplicative: `χ(𝔞 * 𝔟) = χ(𝔞) · χ(𝔟)` for nonzero
ideals `𝔞`, `𝔟` (Sharifi Notation 7.1.17). -/
theorem galoisCharacterOnIdeal_mul
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) {𝔞 𝔟 : Ideal (𝓞 K)} (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥) :
    galoisCharacterOnIdeal K L χ (𝔞 * 𝔟) =
      galoisCharacterOnIdeal K L χ 𝔞 * galoisCharacterOnIdeal K L χ 𝔟 := by
  rw [galoisCharacterOnIdeal_eq_map_prod, galoisCharacterOnIdeal_eq_map_prod,
    galoisCharacterOnIdeal_eq_map_prod, UniqueFactorizationMonoid.normalizedFactors_mul h𝔞 h𝔟,
    Multiset.map_add, Multiset.prod_add]

/-- The ideal character of the unit ideal `⊤` is `1` (empty product). -/
theorem galoisCharacterOnIdeal_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) :
    galoisCharacterOnIdeal K L χ ⊤ = 1 := by
  rw [galoisCharacterOnIdeal_eq_map_prod, ← Ideal.one_eq_top,
    UniqueFactorizationMonoid.normalizedFactors_one, Multiset.map_zero, Multiset.prod_zero]

/-- Summation-by-parts (Dirichlet-test) bound: if `a` is antitone and nonnegative and the
partial sums of `z` are bounded by `B`, then `‖∑_{i<n} a i • z i‖ ≤ B · a 0`. This is the
convergence input (Sharifi Lemma 7.1.5) used to extend `L(χ,·)` past `Re s = 1`. Ported from
`flt-regular-bernoulli` (`BernoulliRegular.LValueAtOne.DirichletBounds`). -/
lemma norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℕ → ℝ} {z : ℕ → E} {B : ℝ}
    (ha : Antitone a) (ha_nonneg : ∀ n, 0 ≤ a n)
    (hbound : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ B) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, a i • z i‖ ≤ B * a 0 := by
  have hB : 0 ≤ B := by simpa using hbound 0
  rcases n.eq_zero_or_pos with rfl | hn
  · simpa using mul_nonneg hB (ha_nonneg 0)
  rw [Finset.sum_range_by_parts (f := a) (g := z) (n := n)]
  have hsum_le :
      ‖∑ i ∈ Finset.range (n - 1), (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖ ≤
        B * (a 0 - a (n - 1)) := by
    calc
      ‖∑ i ∈ Finset.range (n - 1), (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖
          ≤ ∑ i ∈ Finset.range (n - 1),
              ‖(a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖ :=
            norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (n - 1), B * (a i - a (i + 1)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            calc
              ‖(a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖
                  = (a i - a (i + 1)) * ‖∑ j ∈ Finset.range (i + 1), z j‖ := by
                      rw [norm_smul, Real.norm_eq_abs,
                        abs_of_nonpos (sub_nonpos.mpr (ha (Nat.le_succ i)))]
                      ring
              _ ≤ (a i - a (i + 1)) * B := by
                    gcongr
                    · exact sub_nonneg.mpr (ha (Nat.le_succ i))
                    · exact hbound (i + 1)
              _ = B * (a i - a (i + 1)) := by ring
      _ = B * (a 0 - a (n - 1)) := by
            rw [← Finset.mul_sum, Finset.sum_range_sub']
  have hfirst : ‖a (n - 1) • ∑ i ∈ Finset.range n, z i‖ ≤ B * a (n - 1) := by
    calc
      ‖a (n - 1) • ∑ i ∈ Finset.range n, z i‖ = a (n - 1) * ‖∑ i ∈ Finset.range n, z i‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha_nonneg _)]
      _ ≤ a (n - 1) * B := by gcongr; exacts [ha_nonneg _, hbound n]
      _ = B * a (n - 1) := by ring
  calc
    ‖a (n - 1) • ∑ i ∈ Finset.range n, z i -
        ∑ i ∈ Finset.range (n - 1), (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖
        ≤ ‖a (n - 1) • ∑ i ∈ Finset.range n, z i‖ +
            ‖∑ i ∈ Finset.range (n - 1),
                (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖ :=
            norm_sub_le _ _
    _ ≤ B * a (n - 1) + B * (a 0 - a (n - 1)) := add_le_add hfirst hsum_le
    _ = B * a 0 := by ring

/-- Partial sums over a shifted sequence are controlled by the same bound up to a factor `2`.
Ported from `flt-regular-bernoulli`. -/
lemma norm_sum_range_shift_le_of_bounded
    {E : Type*} [NormedAddCommGroup E] {z : ℕ → E} {B : ℝ}
    (hbound : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ B) (m n : ℕ) :
    ‖∑ i ∈ Finset.range n, z (m + i)‖ ≤ 2 * B := by
  have hshift : ∑ i ∈ Finset.range n, z (m + i) =
      ∑ i ∈ Finset.range (m + n), z i - ∑ i ∈ Finset.range m, z i :=
    eq_sub_iff_add_eq.mpr <| (add_comm _ _).trans (Finset.sum_range_add z m n).symm
  rw [hshift]
  calc
    ‖∑ i ∈ Finset.range (m + n), z i - ∑ i ∈ Finset.range m, z i‖
        ≤ ‖∑ i ∈ Finset.range (m + n), z i‖ + ‖∑ i ∈ Finset.range m, z i‖ :=
            norm_sub_le _ _
    _ ≤ B + B := add_le_add (hbound _) (hbound _)
    _ = 2 * B := by ring

/-- Tail sums of a weighted series inherit the same summation-by-parts bound. Ported from
`flt-regular-bernoulli`. -/
lemma norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℕ → ℝ} {z : ℕ → E} {B : ℝ}
    (ha : Antitone a) (ha_nonneg : ∀ n, 0 ≤ a n)
    (hbound : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ B) (m n : ℕ) :
    ‖∑ i ∈ Finset.range n, a (m + i) • z (m + i)‖ ≤ 2 * B * a m := by
  simpa using norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded
    (a := fun k => a (m + k)) (z := fun k => z (m + k)) (B := 2 * B)
    (fun i j hij => ha (Nat.add_le_add_left hij m)) (fun k => ha_nonneg (m + k))
    (fun k => norm_sum_range_shift_le_of_bounded (z := z) (B := B) hbound m k) n

/-! ### Sub-lemmas for `exists_dedekindZeta_factorisation`

Decomposed per Sharifi 7.1.16 (factorisation), 7.1.18 (abelian Euler
product), and 7.1.19 (analytic extension + non-vanishing). Each
sub-lemma is supported by a verbatim source quote in
`.mathlib-quality/chebotarev-decomposition.md`.

(i) Euler product for an abelian character (Sharifi 7.1.18, p. 141):
    `L(χ,s) = ∏_𝔭(1 - χ(𝔭) N𝔭^{-s})^{-1} = Σ_𝔞 χ(𝔞) N𝔞^{-s}` for `Re s > 1`.

(ii) Local Euler-factor decomposition at an unramified `𝔭`:
    `∏_{𝔓|𝔭}(1 - N𝔓^{-s})^{-1} = ∏_χ(1 - χ(σ_𝔭) N𝔭^{-s})^{-1}`. Standard
    identity from finite cyclic group theory applied to the residue
    Galois group.

(iii) Multiplicative assembly: combining (i) and (ii) over all unramified
    `𝔭` yields `ζ_L = ∏_χ L(χ, ·)` (Sharifi 7.1.16 in the abelian case).

(iv) Analytic extension via geometry of numbers (Sharifi 7.1.19 step 1,
    p. 142): `Σ_{N𝔞≤N} χ(𝔞) = O(N^{1-d^{-1}})` where `d = [K:ℚ]`. This
    gives convergence of `L(χ,·)` on `Z(1-d^{-1})` via Lemma 7.1.5.

(v) Non-vanishing `L(χ,1) ≠ 0` for nontrivial `χ` (Sharifi 7.1.19 step 2,
    p. 142): the bounded-function + vanishing-order contradiction
    argument.
-/

/-- The value of a Galois character on the representative of a conjugacy class has norm `1`:
it is a root of unity, since `Gal(L/K)` is finite. -/
private theorem norm_galoisCharacter_out
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (c : ConjClasses Gal(L/K)) :
    ‖(χ c.out : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite c.out)
  refine Complex.norm_eq_one_of_pow_eq_one (n := n) ?_ (by lia)
  simpa using congrArg (Units.val) (show (χ c.out) ^ n = 1 by rw [← map_pow, hpow, map_one])

open Classical in
/-- The ideal character has norm `≤ 1`: each prime-factor contribution is either `0` (ramified)
or a norm-`1` root of unity (unramified), so the product over factors has norm `≤ 1`. -/
private theorem norm_galoisCharacterOnIdeal_le_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (𝔞 : Ideal (𝓞 K)) :
    ‖galoisCharacterOnIdeal K L χ 𝔞‖ ≤ 1 := by
  rw [galoisCharacterOnIdeal, norm_prod]
  refine Finset.prod_le_one (fun i _ => norm_nonneg _) (fun 𝔭 _ => ?_)
  rw [norm_pow]
  by_cases h : UnramifiedIn K L 𝔭
  · rw [if_pos h, norm_galoisCharacter_out, one_pow]
  · rw [if_neg h, norm_zero]
    rcases Nat.eq_zero_or_pos
        ((UniqueFactorizationMonoid.normalizedFactors 𝔞).count 𝔭) with hc | hc
    · rw [hc, pow_zero]
    · rw [zero_pow (by lia)]; norm_num

/-- Sharifi 7.1.18 (p. 141): Euler product for an abelian Galois
character `χ : Gal(L/K) → ℂ^×`. For `Re s > 1` the Euler product over unramified primes
equals the Dirichlet series `Σ_𝔞 χ(𝔞) N𝔞^{-s}`, where `χ(𝔞) = galoisCharacterOnIdeal K L χ 𝔞`
is the completely-multiplicative ideal character.

The proof instantiates the generic weighted prime-ideal Euler product
`weighted_eulerProduct_eq_tsum` with the weight `w = galoisCharacterOnIdeal K L χ`
(completely multiplicative with `‖w‖ ≤ 1`). The product on the left ranges over *unramified*
primes, whereas the weighted Euler product ranges over *all* nonzero primes; the two agree
because `w(𝔭) = 0` at a ramified prime, so its local factor `(1 - 0)⁻¹ = 1` drops out of the
product. At an unramified prime `w(𝔭) = χ(Frob 𝔭)` by `galoisCharacterOnIdeal_apply_prime`. -/
theorem exists_artinLSeries_eulerProduct_abelian
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [_hAb : IsMulCommutative Gal(L/K)] (χ : galoisCharacter K L) :
    ∀ s : ℂ, 1 < s.re →
      (∏' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
          (1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
        = ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
            galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s) := by
  intro s hs
  set w : Ideal (𝓞 K) → ℂ := galoisCharacterOnIdeal K L χ with hw
  rw [← weighted_eulerProduct_eq_tsum K (s := s) hs w (galoisCharacterOnIdeal_one K L χ)
    (fun {𝔞 𝔟} h𝔞 h𝔟 => galoisCharacterOnIdeal_mul K L χ h𝔞 h𝔟)
    (norm_galoisCharacterOnIdeal_le_one K L χ)]
  -- The weighted product over all nonzero primes restricts to the unramified ones: at a ramified
  -- prime the weight is `0`, so the local factor is `1`.
  set g : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} →
      {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := fun 𝔭 => ⟨𝔭.1, 𝔭.2.1, 𝔭.2.2.ne_bot⟩ with hg
  set f : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℂ :=
    fun 𝔭 => (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ with hf
  have hg_inj : Function.Injective g := fun a b hab =>
    Subtype.ext (congrArg (fun x : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} => x.1) hab)
  have hsupp : Function.mulSupport f ⊆ Set.range g := by
    intro 𝔭 hmem
    simp only [Function.mem_mulSupport, hf] at hmem
    haveI := 𝔭.2.1
    have hunr : UnramifiedIn K L 𝔭.1 := by
      by_contra hnr
      apply hmem
      rw [hw, galoisCharacterOnIdeal_apply_prime K L χ 𝔭.1 𝔭.2.2, if_neg hnr, zero_mul, sub_zero,
        inv_one]
    exact ⟨⟨𝔭.1, 𝔭.2.1, hunr⟩, rfl⟩
  rw [← hg_inj.tprod_eq hsupp]
  refine tprod_congr fun 𝔭 => ?_
  simp only [hf, hg, hw]
  haveI := 𝔭.2.1
  rw [galoisCharacterOnIdeal_apply_prime K L χ 𝔭.1 𝔭.2.2.ne_bot, if_pos 𝔭.2.2]

/-! ### Sub-lemmas for `dedekindZeta_local_factor_eq_product_artin_local`

The local-factor identity (Sharifi 7.1.16, p. 141) reduces to a finite-group computation. Both
sides are finite products that evaluate to `(1 - Y ^ f)⁻ᵍ` where `Y = N𝔭^{-s}`, `f = orderOf σ`
is the residue degree and `g = |G| / f` is the number of primes above `𝔭`:

* the left side has `g` factors (`card_primesAbove_mul_orderOf_eq`), each equal to `(1 - Y^f)⁻¹`
  because `N𝔓 = N𝔭^f` (`absNorm_eq_pow_inertiaDeg_of_liesOver`, `inertiaDeg = f`);
* the right side is `∏_{χ : G →* ℂˣ} (1 - χ(σ) Y)⁻¹`, and the evaluation map `χ ↦ χ(σ)`
  surjects `Ĝ` onto the `f`-th roots of unity with uniform fibres of size `g`, so
  `∏_χ (1 - χ(σ) Y) = (∏_{ζ ∈ μ_f} (1 - ζ Y))^g = (1 - Y^f)^g`.
-/

/-- `∏_{ζ ∈ μ_f} (1 - ζ Y) = 1 - Y ^ f` over `ℂ`: the reversed factorisation of `X^f - 1`
(`Polynomial.X_pow_sub_one_eq_prod`), evaluated at `Y⁻¹` and rescaled by `Y^f`. -/
private theorem prod_one_sub_nthRoots (f : ℕ) (hf : 0 < f) (Y : ℂ) :
    ∏ ζ ∈ Polynomial.nthRootsFinset f (1 : ℂ), (1 - ζ * Y) = 1 - Y ^ f := by
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / f)) f :=
    Complex.isPrimitiveRoot_exp f hf.ne'
  have hcard : (Polynomial.nthRootsFinset f (1 : ℂ)).card = f := hprim.card_nthRootsFinset
  have hpoly := Polynomial.X_pow_sub_one_eq_prod (R := ℂ) hf hprim
  rcases eq_or_ne Y 0 with hY | hY
  · subst hY; simp [zero_pow hf.ne']
  · have heval := congrArg (fun p : Polynomial ℂ => Polynomial.eval Y⁻¹ p) hpoly
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
      Polynomial.eval_prod, Polynomial.eval_C] at heval
    have hfac : ∀ ζ ∈ Polynomial.nthRootsFinset f (1 : ℂ), (1 - ζ * Y) = Y * (Y⁻¹ - ζ) := by
      intro ζ _; field_simp
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const, hcard, ← heval,
      inv_pow, mul_sub, mul_one, mul_inv_cancel₀ (pow_ne_zero f hY)]

/-- The evaluation homomorphism `Ĝ → ℂˣ`, `χ ↦ χ σ`, for a finite commutative group `G`.
Realised as `(monoidHomMonoidHomEquiv G ℂ).symm σ` (the double-dual identification). -/
private noncomputable def charEval {G : Type*} [CommGroup G] [Finite G] (σ : G) :
    (G →* ℂˣ) →* ℂˣ := (CommGroup.monoidHomMonoidHomEquiv G ℂ).symm σ

private theorem charEval_apply {G : Type*} [CommGroup G] [Finite G] (σ : G) (φ : G →* ℂˣ) :
    charEval σ φ = φ σ := by rw [charEval, CommGroup.monoidHomMonoidHomEquiv_symm_apply_apply]

/-- The kernel of `χ ↦ χ σ` consists of the characters trivial on `⟨σ⟩`, so it has order
`|G ⧸ ⟨σ⟩| = |G| / orderOf σ` (`CommGroup.card_restrictHom_ker` + Lagrange + `Nat.card_zpowers`). -/
private theorem charEval_ker_card {G : Type*} [CommGroup G] [Finite G] (σ : G) :
    Nat.card (charEval σ).ker = Nat.card G / orderOf σ := by
  have h1 : (charEval σ).ker = (MonoidHom.restrictHom (Subgroup.zpowers σ) ℂˣ).ker := by
    ext φ
    simp only [MonoidHom.mem_ker, MonoidHom.restrictHom_apply, MonoidHom.restrict_eq_one_iff]
    refine ⟨fun hφ y hy => ?_, fun hφ => ?_⟩
    · rw [charEval_apply] at hφ
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [map_zpow, hφ, one_zpow]
    · rw [charEval_apply]; exact hφ σ (Subgroup.mem_zpowers σ)
  rw [h1, CommGroup.card_restrictHom_ker]
  have hpos : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
  have key : Nat.card G = Nat.card (G ⧸ Subgroup.zpowers σ) * orderOf σ := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers σ), Nat.card_zpowers]
  rw [key, Nat.mul_div_cancel _ hpos]

open Finset in
/-- **Character-product identity** (the group-theoretic heart of Sharifi 7.1.16). For a finite
commutative group `G`, an element `σ`, and `Y : ℂ`,
`∏_{χ : G →* ℂˣ} (1 - χ(σ) Y) = (1 - Y ^ orderOf σ) ^ (|G| / orderOf σ)`.
The map `χ ↦ χ(σ)` surjects `Ĝ` onto the `f`-th roots of unity `μ_f` (`f = orderOf σ`) with
uniform fibres of size `g = |G| / f` (`MonoidHom.card_fiber_eq_of_mem_range`, `charEval_ker_card`),
so the product factors over `μ_f` and collapses by `prod_one_sub_nthRoots`. -/
private theorem prod_galoisCharacter_one_sub {G : Type*} [CommGroup G] [Finite G]
    [Fintype (G →* ℂˣ)] (σ : G) (Y : ℂ) :
    ∏ χ : G →* ℂˣ, (1 - ((χ σ : ℂˣ) : ℂ) * Y)
      = (1 - Y ^ orderOf σ) ^ (Nat.card G / orderOf σ) := by
  classical
  set f := orderOf σ with hf
  have hfpos : 0 < f := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
  set evC : (G →* ℂˣ) →* ℂ := (Units.coeHom ℂ).comp (charEval σ) with hevC
  have hevC_apply : ∀ χ : G →* ℂˣ, evC χ = ((χ σ : ℂˣ) : ℂ) := by
    intro χ; rw [hevC, MonoidHom.comp_apply, Units.coeHom_apply, charEval_apply]
  have hfib1 : #{χ : G →* ℂˣ | evC χ = 1} = Nat.card (charEval σ).ker := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun χ => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, MonoidHom.mem_ker, hevC_apply]
    rw [show ((χ σ : ℂˣ) : ℂ) = 1 ↔ (χ σ : ℂˣ) = 1 from by
      rw [← Units.val_one]; exact Units.val_inj, ← charEval_apply σ χ]
  have huniform : ∀ c ∈ Set.range evC, #{χ : G →* ℂˣ | evC χ = c} = Nat.card (charEval σ).ker := by
    intro c hc
    rw [MonoidHom.card_fiber_eq_of_mem_range evC hc (⟨1, map_one _⟩ : (1 : ℂ) ∈ Set.range evC),
      hfib1]
  set t : Finset ℂ := Polynomial.nthRootsFinset f (1 : ℂ) with ht
  have hmaps : ∀ χ ∈ (Finset.univ : Finset (G →* ℂˣ)), evC χ ∈ t := by
    intro χ _
    rw [ht, Polynomial.mem_nthRootsFinset hfpos, hevC_apply,
      ← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  have hsub : Finset.univ.image evC ⊆ t := by
    intro c hc; rw [Finset.mem_image] at hc
    obtain ⟨χ, _, rfl⟩ := hc; exact hmaps χ (Finset.mem_univ χ)
  have hkerpos : 0 < Nat.card (charEval σ).ker := Nat.card_pos
  have hcardG : Nat.card G = (Finset.univ.image evC).card * Nat.card (charEval σ).ker := by
    have hsum := Finset.card_eq_sum_card_image evC (Finset.univ : Finset (G →* ℂˣ))
    rw [show (Finset.univ : Finset (G →* ℂˣ)).card = Nat.card (G →* ℂˣ) from by
      rw [Nat.card_eq_fintype_card, Finset.card_univ],
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity] at hsum
    rw [hsum, Finset.sum_congr rfl (fun c hc => huniform c ?_), Finset.sum_const, smul_eq_mul]
    rw [Finset.mem_image] at hc; obtain ⟨χ, _, rfl⟩ := hc; exact Set.mem_range_self χ
  have himgcard : (Finset.univ.image evC).card = f := by
    have hdvd : f ∣ Nat.card G := orderOf_dvd_natCard σ
    have hkereq : Nat.card (charEval σ).ker = Nat.card G / f := charEval_ker_card σ
    rw [hkereq] at hcardG
    have hkerpos' : 0 < Nat.card G / f := hkereq ▸ hkerpos
    exact Nat.eq_of_mul_eq_mul_right hkerpos'
      (by rw [← hcardG, ← (Nat.mul_div_cancel' hdvd).symm])
  have himg : Finset.univ.image evC = t :=
    Finset.eq_of_subset_of_card_le hsub
      (by rw [himgcard, ht, (Complex.isPrimitiveRoot_exp f hfpos.ne').card_nthRootsFinset])
  have hfiber := Finset.prod_fiberwise_of_maps_to' (s := (Finset.univ : Finset (G →* ℂˣ)))
    (t := t) (g := evC) (f := fun c : ℂ => 1 - c * Y) hmaps
  have hLHS : ∏ χ : G →* ℂˣ, (1 - ((χ σ : ℂˣ) : ℂ) * Y)
      = ∏ χ : G →* ℂˣ, (1 - evC χ * Y) :=
    Finset.prod_congr rfl fun χ _ => by rw [hevC_apply]
  rw [hLHS, ← hfiber]
  have hinner : ∀ c ∈ t, (∏ _χ ∈ {χ ∈ (Finset.univ : Finset (G →* ℂˣ)) | evC χ = c},
      (1 - c * Y)) = (1 - c * Y) ^ Nat.card (charEval σ).ker := by
    intro c hc
    have hrange : c ∈ Set.range evC := by
      rw [← himg, Finset.mem_image] at hc
      obtain ⟨χ, _, rfl⟩ := hc; exact Set.mem_range_self χ
    rw [Finset.prod_const, huniform c hrange]
  rw [Finset.prod_congr rfl hinner, charEval_ker_card σ, Finset.prod_pow, ht,
    prod_one_sub_nthRoots f hfpos Y]

/-- For an unramified prime `𝔭` and a prime `𝔓` of `𝓞 L` above it with residue degree `f`,
`N𝔓 = N𝔭 ^ f`, hence `(N𝔓)^{-s} = ((N𝔭)^{-s})^f`. The complex-power step uses `cpow_mul`
(the branch conditions hold because the base `N𝔭` is a nonnegative real). -/
private theorem cpow_neg_absNorm_eq_pow {a b : ℕ} (f : ℕ) (s : ℂ)
    (h : b = a ^ f) : ((b : ℂ)) ^ (-s) = ((a : ℂ) ^ (-s)) ^ f := by
  have him : (Complex.log (a : ℂ) * (f : ℂ)).im = 0 := by
    simp [Complex.log_im, Complex.natCast_arg]
  have hmul : ((a : ℂ) ^ (f : ℂ)) ^ (-s) = (a : ℂ) ^ ((f : ℂ) * (-s)) :=
    (Complex.cpow_mul (-s) (by rw [him]; linarith [Real.pi_pos])
      (by rw [him]; exact Real.pi_pos.le)).symm
  rw [h, Nat.cast_pow, ← Complex.cpow_natCast (a : ℂ) f, hmul, Complex.cpow_nat_mul]

/-- Sharifi 7.1.16 (p. 141) local step: the local Euler factor at an
unramified prime `𝔭` of `K` factors as a product over characters.
Source quote (paraphrased identity): the local factor
`∏_{𝔓|𝔭}(1-N𝔓^{-s})^{-1}` equals `∏_χ(1-χ(σ_𝔭) N𝔭^{-s})^{-1}`. -/
theorem dedekindZeta_local_factor_eq_product_artin_local
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (_hunr : UnramifiedIn K L 𝔭) (s : ℂ) (_hs : 1 < s.re) :
    ∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥},
        (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹
      = ∏' χ : galoisCharacter K L,
        (1 - (χ (frobeniusClass K L 𝔭).out : ℂ) * (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ := by
  classical
  open scoped IsMulCommutative in
  letI : CommGroup Gal(L/K) := inferInstance
  set σ : Gal(L/K) := (frobeniusClass K L 𝔭).out with hσ
  set Y : ℂ := (Ideal.absNorm 𝔭 : ℂ) ^ (-s) with hY
  set f : ℕ := orderOf σ with hf
  haveI : Fintype Gal(L/K) := Fintype.ofFinite _
  haveI : Fintype (Gal(L/K) →* ℂˣ) := Fintype.ofFinite _
  have hfpos : 0 < f := hf ▸ orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
  -- the splitting count g = |G| / f
  have hcount : Nat.card {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥}
      = Nat.card Gal(L/K) / f := by
    have hmul := card_primesAbove_mul_orderOf_eq K L σ (frobeniusClass K L 𝔭)
      (Quotient.out_eq _) 𝔭 _hunr rfl
    rw [← hf] at hmul
    exact (Nat.div_eq_of_eq_mul_left hfpos hmul.symm).symm
  -- RHS = ((1 - Y^f)^g)⁻¹
  have hRHS : (∏' χ : galoisCharacter K L,
        (1 - ((χ σ : ℂˣ) : ℂ) * Y)⁻¹)
      = ((1 - Y ^ f) ^ (Nat.card Gal(L/K) / f))⁻¹ := by
    rw [tprod_fintype, Finset.prod_inv_distrib, prod_galoisCharacter_one_sub σ Y, hf]
  -- finiteness of the primes above `𝔭`
  have hpbot : 𝔭 ≠ ⊥ := UnramifiedIn.ne_bot K L _hunr
  haveI : 𝔭.IsMaximal := ‹𝔭.IsPrime›.isMaximal hpbot
  haveI : Finite (𝔭.primesOver (𝓞 L)) := (IsDedekindDomain.primesOver_finite 𝔭 (𝓞 L)).to_subtype
  haveI : Finite {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} :=
    Finite.of_injective
      (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} =>
        (⟨𝔓.1, 𝔓.2.1, 𝔓.2.2.1⟩ : 𝔭.primesOver (𝓞 L)))
      fun _ _ hab => Subtype.ext (by simpa using hab)
  haveI : Fintype {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} := Fintype.ofFinite _
  -- each prime above `𝔭` has norm `N𝔭 ^ f`, so its local factor is the constant `(1 - Y^f)⁻¹`
  have hterm : ∀ 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥},
      (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ = (1 - Y ^ f)⁻¹ := by
    intro 𝔓
    haveI := 𝔓.2.1
    haveI hlo : 𝔓.1.LiesOver 𝔭 := 𝔓.2.2.1
    -- inertia degree at `𝔓` equals `f = orderOf σ` (residue degree = Frobenius order)
    have hdeg : (𝔓.1.under (𝓞 K)).inertiaDeg 𝔓.1 = f := by
      rw [Ideal.inertiaDeg_algebraMap, hf]
      exact finrank_residue_eq_orderOf K L σ (frobeniusClass K L 𝔭) (Quotient.out_eq _)
        𝔭 _hunr rfl 𝔓.1 hlo
    haveI : 𝔓.1.LiesOver (𝔓.1.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓.1)
    have hpubot : 𝔓.1.under (𝓞 K) ≠ ⊥ := hlo.over ▸ hpbot
    haveI : (𝔓.1.under (𝓞 K)).IsPrime := hlo.over ▸ ‹𝔭.IsPrime›
    have hnorm : Ideal.absNorm 𝔓.1 = Ideal.absNorm 𝔭 ^ f := by
      rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔓.1 (𝔓.1.under (𝓞 K)) inferInstance hpubot,
        hdeg, ← hlo.over]
    rw [cpow_neg_absNorm_eq_pow f s hnorm, hY]
  rw [tprod_congr hterm, tprod_fintype, Finset.prod_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, hcount, hRHS, Nat.card_eq_fintype_card, inv_pow]

/-! ### Sub-lemmas for `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow` (leaf G)

**The geometry-of-numbers bridge (decomposition.md "Frobenius-fibre chain", 2026-06-05).**

For `L = K(μ_m)` cyclotomic, `galoisCharacterOnIdeal K L χ 𝔞 = χ(Frob_𝔞)` **on
unramified-supported `𝔞`** — i.e. on `𝔞` satisfying `U 𝔞 := ∀ 𝔭 ∈ normalizedFactors 𝔞,
UnramifiedIn K L 𝔭` — where `Frob_𝔞 ∈ Gal(L/K)` is the completely-multiplicative ideal Frobenius
(abelian, so a genuine group element, not just a conjugacy class). `U 𝔞` is the **exact** support
condition `χ(𝔞) ≠ 0`: a single ramified factor zeroes the product. Hence the **value-fibre**
`{𝔞 : χ(𝔞) = ζ}` (for `ζ ≠ 0`) is *exactly* the **unramified-supported Frobenius-value-fibre**
`{𝔞 : U 𝔞 ∧ χ(Frob_𝔞) = ζ}` — an exact set equality (the earlier "thin-error bridge" between
`{χ(𝔞)=ζ}` and the *unconditional* `{χ(Frob_𝔞)=ζ}` was mathematically **false**: the junk-class
`Frob_𝔞` ignores ramified factors, so the unconditional fibre is bigger by a `Θ(N)`, not
`O(N^{1−1/d})`, set). That fibre is then a finite union of **unramified-supported Frobenius-fibres**
`{𝔞 : U 𝔞 ∧ Frob_𝔞 = g}` over `g` in the coset `χ⁻¹(ζ) ⊆ G`. The proof decomposes into:

* **`frobeniusIdeal`** — the `G`-valued completely-multiplicative ideal Frobenius. A genuine
  `def` (no sorry): the `Multiset.map`-product of `(frobeniusClass K L 𝔭).out` over the prime
  factors, mirroring `galoisCharacterOnIdeal`.
* **The support condition is `U`, not coprimality.** An earlier draft used `(N𝔞).Coprime m` as the
  support condition via a claimed iff `unramifiedIn_iff_absNorm_coprime`
  (`UnramifiedIn K L 𝔭 ↔ (N𝔭).Coprime m`). That iff is **false** in the `⟹` direction: if
  `K ⊇ ℚ(μ_{p^a})` and `m = p^a·m'` (`p ∤ m'`), a prime `𝔭` over `p` is unramified in `K(μ_m)/K`
  (the local extension `K_𝔭(μ_m)/K_𝔭` is unramified, `K_𝔭` already containing `μ_{p^a}`) yet
  `N𝔭 = p^f` is **not** coprime to `m`. So the coprime condition is strictly stronger than `U` and
  was dropped; `U` is the genuine support condition and needs **no** cyclotomic-ramification side
  fact — it *is* the `if UnramifiedIn` branch of the product.
* **Helper 1 (`galoisCharacterOnIdeal_eq_char_frobeniusIdeal`)** and **Helper 1a
  (`card_valueFibre_eq_card_unramifiedSupported_frobeniusValueFibre`)** — the cyclotomic identity
  `χ(𝔞) = χ(Frob_𝔞)` on unramified-supported `𝔞` (Sharifi p. 142) and the value-fibre =
  unramified-supported Frobenius-value-fibre set equality. Both are **sorry-free** (`U` is the exact
  support condition, so the `if UnramifiedIn` branch is always taken — no ramification side-fact).
* **L2 (`exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le`)** — unramified-supported
  Frobenius-fibre equidistribution:
  `∃ κ, ∀ g, |#{𝔞 ≠ ⊥ : N𝔞 ≤ N, U 𝔞, Frob_𝔞 = g} − κ·N| ≤ C·N^{1−1/d}` with `κ` **independent of
  `g`**. Proof: split an unramified-supported `𝔞` into its (finitely many possible) **bad-prime
  part** (factors unramified but with `N𝔭` *not* coprime to `m`, i.e. `𝔭 ∣ m`, whose Frobenius is
  not the norm-power) times a **good part** (`N𝔭` coprime to `m`, `Frob = (Frob_p)^f` by
  `cyclotomic_frobenius_acts_as_norm_power`, cut out by `N𝔞 ≡ a mod m`). L1 applied to the ideal
  lattice (`idealLattice`, `normLeOne`, `fundamentalCone` — the mathlib dictionary
  `tendsto_norm_le_and_mk_eq_div_atTop`) intersected with the congruence sublattice counts each good
  part; summing over the finite bad-part set keeps `κ` `g`-independent (each good fibre is an
  equal-covolume union of congruence cosets). **Sub-gap 3** (the bad-prime split + coordinate
  transport of ideals-of-bounded-norm to lattice-points-in-a-set, per congruence coset), **built on
  Sub-gap 2** — the now-extracted **`normLeOne_frontier_lipschitz`**, the Lipschitz-boundary
  hypothesis L1 needs (mathlib proves only `volume_frontier_normLeOne = 0`; the Lipschitz regularity
  is Gun–Ramaré–Sivaraman, *J. Number Theory* 243 (2023) §3.3, a genuine future mathlib-PR — the
  project's deepest gap).

Leaf G is then proved *from* Helper 1a + L2 (exact set equality + coset counting), with **no
residual `sorry` of its own**. -/

open Classical in
/-- The `Gal(L/K)`-valued completely-multiplicative **ideal Frobenius**: on a prime `𝔭` it is the
chosen representative `(frobeniusClass K L 𝔭).out` of the Frobenius conjugacy class (a genuine
group element since `Gal(L/K)` is abelian, so the class is a singleton), extended completely
multiplicatively over the prime factorisation. Companion of `galoisCharacterOnIdeal`: the
character value is `χ` applied to this element (Helper 1). A real `def` (no sorry). The
`Multiset.prod` over the (unordered) prime factors needs commutativity, supplied by the abelian
hypothesis `IsMulCommutative Gal(L/K)`. -/
noncomputable def frobeniusIdeal (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [IsMulCommutative Gal(L/K)]
    (𝔞 : Ideal (𝓞 K)) : Gal(L/K) :=
  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
  ((UniqueFactorizationMonoid.normalizedFactors 𝔞).map
    (fun 𝔭 => (frobeniusClass K L 𝔭).out)).prod

open Classical in
/-- `frobeniusIdeal` of a prime is the chosen Frobenius representative. -/
theorem frobeniusIdeal_apply_prime
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) :
    frobeniusIdeal K L 𝔭 = (frobeniusClass K L 𝔭).out := by
  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
  rw [frobeniusIdeal, UniqueFactorizationMonoid.normalizedFactors_irreducible
    (Ideal.prime_of_isPrime h𝔭 ‹_›).irreducible, normalize_eq, Multiset.map_singleton,
    Multiset.prod_singleton]

/-- `frobeniusIdeal` is completely multiplicative on nonzero ideals. -/
theorem frobeniusIdeal_mul
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] {𝔞 𝔟 : Ideal (𝓞 K)} (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥) :
    frobeniusIdeal K L (𝔞 * 𝔟) = frobeniusIdeal K L 𝔞 * frobeniusIdeal K L 𝔟 := by
  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
  rw [frobeniusIdeal, frobeniusIdeal, frobeniusIdeal,
    UniqueFactorizationMonoid.normalizedFactors_mul h𝔞 h𝔟, Multiset.map_add, Multiset.prod_add]

/-- `frobeniusIdeal` of the unit ideal is `1` (empty product). -/
theorem frobeniusIdeal_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] :
    frobeniusIdeal K L ⊤ = 1 := by
  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
  rw [frobeniusIdeal, ← Ideal.one_eq_top, UniqueFactorizationMonoid.normalizedFactors_one,
    Multiset.map_zero, Multiset.prod_zero]

open Classical in
/-- **Helper 1 (cyclotomic identity `χ(𝔞) = χ(Frob_𝔞)` on unramified-supported `𝔞`).** For
`L = K(μ_m)` cyclotomic, `𝔞 ≠ ⊥` all of whose prime factors are unramified in `L`, the
multiplicative ideal character `χ(𝔞)` equals `χ` of the ideal Frobenius
`Frob_𝔞 = frobeniusIdeal K L 𝔞`.

The support hypothesis `hU : ∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭` is the **exact**
condition under which `galoisCharacterOnIdeal K L χ 𝔞 ≠ 0` (a single ramified factor zeroes the
product), so it is the right hypothesis — and it is *literally* what the multiplicativity proof
needs, with no cyclotomic-ramification side-fact.

**The multiplicativity reduction is fully proved here (no residual `sorry`):** both sides are the
`Multiset`-product of `χ((frobeniusClass 𝔭).out)` over the prime factors of `𝔞` — the left via
`galoisCharacterOnIdeal_eq_map_prod` (the `if UnramifiedIn` branch always taken because `hU` says
every factor is unramified), the right via `frobeniusIdeal` + `map_multiset_prod` — and they match
term by term (`Multiset.map_congr` + `if_pos (hU 𝔭 h𝔭)`). -/
theorem galoisCharacterOnIdeal_eq_char_frobeniusIdeal
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) {𝔞 : Ideal (𝓞 K)}
    (hU : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) :
    galoisCharacterOnIdeal K L χ 𝔞 = (χ (frobeniusIdeal K L 𝔞) : ℂ) := by
  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
  -- With every factor unramified (exactly `hU`), both `χ(𝔞)` and `χ(Frob_𝔞)` are the
  -- multiset-product of `χ((frobeniusClass 𝔭).out)` over the prime factors
  -- (`galoisCharacterOnIdeal_eq_map_prod` resp. `frobeniusIdeal` + `map_multiset_prod`), the
  -- `if unramified` branch always taken.
  have hfrob : (χ (frobeniusIdeal K L 𝔞) : ℂ) =
      ((UniqueFactorizationMonoid.normalizedFactors 𝔞).map
        (fun 𝔭 => (χ (frobeniusClass K L 𝔭).out : ℂ))).prod := by
    rw [frobeniusIdeal, map_multiset_prod, ← Units.coeHom_apply, map_multiset_prod,
      Multiset.map_map, Multiset.map_map]
    rfl
  rw [galoisCharacterOnIdeal_eq_map_prod, hfrob]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun 𝔭 h𝔭 => ?_)
  rw [if_pos (hU 𝔭 h𝔭)]

open Classical in
/-- **Helper 1a (cardinality form) — value-fibre = unramified-supported Frobenius-value-fibre.** For
`ζ ≠ 0`, the **value-fibre** `{𝔞 : χ(𝔞) = ζ}` and the **unramified-supported Frobenius-value-fibre**
`{𝔞 : U 𝔞 ∧ χ(Frob_𝔞) = ζ}`, where `U 𝔞 := ∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭`, are the
**same set** (hence have equal `Nat.card`) — not merely close. `U 𝔞` is the **exact** support
condition `galoisCharacterOnIdeal χ 𝔞 ≠ 0`: a single ramified factor zeroes the product, so the
value-fibre (for `ζ ≠ 0`) contains *only* `𝔞` with every factor unramified, on which
`χ(𝔞) = χ(Frob_𝔞)` by Helper 1. (The `junk`-class `frobeniusIdeal` would otherwise *include*
ramified-divisible `𝔞`, so keeping the `U` field on the Frobenius side is what makes this an exact
equality rather than a count off by a `Θ(N)` set.)

Proof of the set equality (predicate `↔` for fixed `𝔞 ≠ ⊥`, `N𝔞 ≤ N`):
* **⟹** `χ(𝔞) = ζ ≠ 0` ⟹ `χ(𝔞) ≠ 0` ⟹ no `(if unramified … else 0)` factor of the multiset product
  vanishes (`Multiset.prod_eq_zero_iff`) ⟹ every prime factor is unramified, i.e. `U 𝔞`; then
  Helper 1 gives `χ(Frob_𝔞) = χ(𝔞) = ζ`.
* **⟸** `U 𝔞` ⟹ Helper 1 gives `χ(𝔞) = χ(Frob_𝔞) = ζ`.

Fully proved (**no `sorry`**): `U` is the exact support condition, so no cyclotomic-ramification
side-fact is needed. -/
theorem card_valueFibre_eq_card_unramifiedSupported_frobeniusValueFibre
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) (ζ : ℂ) (hζ : ζ ≠ 0) (N : ℕ) :
    Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = ζ}
        = Nat.card {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
            (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
              (χ (frobeniusIdeal K L 𝔞) : ℂ) = ζ} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun 𝔞 => and_congr_right fun h𝔞 =>
    and_congr_right fun _hN => ?_)
  -- Reduce to the core predicate `↔` under `h𝔞 : 𝔞 ≠ ⊥`.
  constructor
  · -- ⟹ : `χ(𝔞) = ζ ≠ 0` forces every factor unramified (`U 𝔞`); then Helper 1.
    intro hval
    have hU : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭 := by
      intro 𝔭 h𝔭
      by_contra hnr
      have hzero : (if UnramifiedIn K L 𝔭 then (χ (frobeniusClass K L 𝔭).out : ℂ) else 0) = 0 :=
        if_neg hnr
      have : galoisCharacterOnIdeal K L χ 𝔞 = 0 := by
        rw [galoisCharacterOnIdeal_eq_map_prod]
        exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨𝔭, h𝔭, hzero⟩)
      exact hζ (this ▸ hval).symm
    refine ⟨hU, ?_⟩
    rw [← galoisCharacterOnIdeal_eq_char_frobeniusIdeal K L m χ hU]
    exact hval
  · -- ⟸ : `U 𝔞` ⟹ Helper 1 ⟹ `χ(𝔞) = χ(Frob_𝔞) = ζ`.
    rintro ⟨hU, hfrob⟩
    rw [galoisCharacterOnIdeal_eq_char_frobeniusIdeal K L m χ hU]
    exact hfrob

/-- **The image of a character `χ` of a finite abelian group is exactly `μ_{orderOf χ}`.** Hence
every `ζ` with `ζ^{orderOf χ} = 1` lies in the image of `χ`. The image `range χ` is a finite —
hence cyclic (`isCyclic_subgroup_units`) — subgroup of `ℂˣ`, of order `orderOf χ` (for a cyclic
group `Nat.card = Monoid.exponent`, and `orderOf χ = exponent (range χ)`), contained in the `n`-th
roots of unity `rootsOfUnity n ℂ` which also has order `n = orderOf χ`
(`Complex.card_rootsOfUnity`); equal cardinality forces equality of the two subgroups.
Fully proved (no sorry). -/
theorem charFibre_mem_range
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (χ : galoisCharacter K L) (ζ : ℂˣ)
    (hζ : ζ ^ orderOf χ = 1) :
    ∃ g : Gal(L/K), χ g = ζ := by
  classical
  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
  haveI : NeZero (orderOf χ) := ⟨(orderOf_pos_iff.mpr (isOfFinOrder_of_finite χ)).ne'⟩
  haveI : Finite (MonoidHom.range χ) :=
    Finite.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective
  have hpow : ∀ g : Gal(L/K), (χ g) ^ orderOf χ = 1 := fun g => by
    rw [← MonoidHom.pow_apply, pow_orderOf_eq_one, MonoidHom.one_apply]
  have hsub : MonoidHom.range χ ≤ rootsOfUnity (orderOf χ) ℂ := by
    rintro x ⟨g, rfl⟩; exact (mem_rootsOfUnity (orderOf χ) (χ g)).mpr (hpow g)
  have hcard_roots : Nat.card (rootsOfUnity (orderOf χ) ℂ) = orderOf χ := by
    rw [Nat.card_eq_fintype_card, Complex.card_rootsOfUnity]
  have hpowexp : ∀ g : Gal(L/K), (χ g) ^ Monoid.exponent (MonoidHom.range χ) = 1 := fun g => by
    have hmem : χ g ∈ MonoidHom.range χ := ⟨g, rfl⟩
    simpa using congrArg Subtype.val (Monoid.pow_exponent_eq_one (⟨χ g, hmem⟩ : MonoidHom.range χ))
  have hoe : orderOf χ = Monoid.exponent (MonoidHom.range χ) := by
    apply Nat.dvd_antisymm
    · rw [orderOf_dvd_iff_pow_eq_one]
      refine MonoidHom.ext fun g => ?_
      rw [MonoidHom.pow_apply, MonoidHom.one_apply]; exact hpowexp g
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      rintro ⟨x, g, rfl⟩
      exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hpow g)
  have hcard_range : Nat.card (MonoidHom.range χ) = orderOf χ := by
    rw [hoe, IsCyclic.exponent_eq_card (α := MonoidHom.range χ)]
  have heq : MonoidHom.range χ = rootsOfUnity (orderOf χ) ℂ :=
    Subgroup.eq_of_le_of_card_ge hsub (by rw [hcard_roots, hcard_range])
  have hmem : ζ ∈ rootsOfUnity (orderOf χ) ℂ := (mem_rootsOfUnity (orderOf χ) ζ).mpr hζ
  rw [← heq] at hmem
  exact hmem

/-- **Helper 1b — the character fibre `{g : χ g = ζ}` has constant cardinality over roots of
unity.** For a character `χ : G →* ℂˣ` of a finite abelian group and any `ζ` with
`ζ^{orderOf χ} = 1`: `ζ` lies in the image of `χ` (`charFibre_mem_range`: the image of `χ` is the
full group `μ_n` of `n`-th roots of unity, `n = orderOf χ`, since it is cyclic of order `n`), and
the fibre `{g : χ g = ζ}` is a coset of `ker χ`, hence
`Nat.card {g : χ g = ζ} = Nat.card (MonoidHom.ker χ)`, **independent of `ζ`**. This is the
`|χ⁻¹(ζ)| = |ker χ|` constancy that makes leaf G's leading constant `C = |ker χ|·κ` independent of
`ζ`. Fully proved (no sorry). -/
theorem card_charFibre_eq_card_ker
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (χ : galoisCharacter K L) (ζ : ℂˣ)
    (hζ : ζ ^ orderOf χ = 1) :
    Nat.card {g : Gal(L/K) // χ g = ζ} = Nat.card (MonoidHom.ker χ) := by
  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
  -- `ζ` lies in the image of `χ` (image = `μ_{orderOf χ}`, since the image is a finite — hence
  -- cyclic — subgroup of `ℂˣ` of order `orderOf χ`, contained in and equal to the `n`-th roots
  -- of unity). **Residual sub-fact** (`ζ ∈ range χ`); the rest of Helper 1b is proved.
  obtain ⟨g₀, hg₀⟩ : ∃ g : Gal(L/K), χ g = ζ := charFibre_mem_range K L χ ζ hζ
  -- The fibre `{g : χ g = ζ}` is the right coset `(ker χ)·g₀`, bijective to `ker χ` via
  -- `k ↦ k·g₀` (inverse `g ↦ g·g₀⁻¹`).
  refine Nat.card_congr (Equiv.ofBijective (fun g => (⟨g.1 * g₀⁻¹, ?_⟩ : MonoidHom.ker χ)) ?_)
  · rw [MonoidHom.mem_ker, map_mul, map_inv, g.2, hg₀, mul_inv_cancel]
  · constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      simp only [Subtype.mk.injEq, mul_left_inj] at hab
      exact Subtype.ext hab
    · rintro ⟨k, hk⟩
      refine ⟨⟨k * g₀, ?_⟩, ?_⟩
      · rw [map_mul, MonoidHom.mem_ker.mp hk, hg₀, one_mul]
      · simp [mul_assoc]

open scoped NNReal in
/-- **Sub-gap 2 (the surfaced deep analytic gap) — Lipschitz frontier of `normLeOne K`.** The
frontier of the norm-`≤ 1` slice `normLeOne K ⊆ mixedSpace K` of the fundamental cone is covered by
**finitely many Lipschitz images of the unit cube** `[0,1]^{d-1}` (`d = finrank ℚ K = finrank ℝ
(mixedSpace K)`). This is the regularity input of the effective lattice-point count: it is the exact
`hlip` hypothesis of `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` (L1), specialized to the
ideal-counting region `normLeOne K`.

It is stated on `realSpace K = InfinitePlace K → ℝ` — the `Pi`-type model on which mathlib's
`NormLeOne` boundary analysis already lives (the frontier-measure step studies the image
`normAtAllPlaces '' normLeOne K ⊆ realSpace K`) and which matches L1's `hlip` codomain `ι → ℝ`
(`ι = InfinitePlace K`): the cube dimension is `Fintype.card (InfinitePlace K) - 1` and the set is
the `realSpace` image `normAtAllPlaces '' normLeOne K`. Mathlib currently has only the
**measure-zero** form `volume_frontier_normLeOne` (`volume (frontier (normLeOne K)) = 0`), which
suffices for the rate-*free* limit `ZLattice.covolume.tendsto_card_le_div'` behind
`tendsto_norm_le_and_mk_eq_div_atTop`, but **not** the Lipschitz cover needed for an effective
`O(N^{1−1/d})` error term. The Lipschitz-boundary regularity is Gun–Ramaré–Sivaraman, *Counting
ideals in ray classes*, J. Number Theory 243 (2023) §3.3 (after Debaene): `∂(normLeOne K)` is a
finite union of images of `[0,1]^{d-1}` under the Lipschitz parametrizations `expMapBasis`/`expMap`
of the cone boundary. **Residual sorry — this is the project's single deepest analytic gap, a
legitimate standalone future-mathlib PR.** -/
theorem normLeOne_frontier_lipschitz (K : Type*) [Field K] [NumberField K] :
    ∃ (m : ℕ) (M : ℝ≥0)
      (φ : Fin m → (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → mixedEmbedding.realSpace K),
      (∀ j, LipschitzWith M (φ j)) ∧
        frontier (mixedEmbedding.normAtAllPlaces ''
          mixedEmbedding.fundamentalCone.normLeOne K) ⊆ ⋃ j, φ j '' Set.Icc 0 1 := by
  sorry

/-- **L2 (Sub-gaps 2+3) — unramified-supported Frobenius-fibre equidistribution.** For
`L = K(μ_m)` cyclotomic, the number of nonzero ideals `𝔞` with `N𝔞 ≤ N`, **every prime factor of
`𝔞` unramified in `L`** (`U 𝔞`) and `Frob_𝔞 = g` is `κ·N + O(N^{1−1/d})` with the leading constant
`κ` **independent of `g`** (`d = finrank ℚ K`).

`U 𝔞` is the exact support condition (`galoisCharacterOnIdeal χ 𝔞 ≠ 0`). The geometry-of-numbers
argument splits an unramified-supported `𝔞` multiplicatively into its **"bad-prime" part** — the
product of factors that are unramified but have `N𝔭` *not* coprime to `m` (so `𝔭 ∣ m`; these are
the finitely many primes lying over the `p ∣ m` for which `K_𝔭` already contains `μ_{p^{v_p(m)}}`,
hence unramified despite ramifying naively over `ℚ`), whose ideal Frobenius is **not** the
norm-power — times a **"good" part** with `N𝔭` coprime to `m`, on which
`cyclotomic_frobenius_acts_as_norm_power` gives `Frob_𝔭 = (Frob_p)^{f_𝔭}` cut out by `N𝔭 mod m`.

The bad-prime part ranges over a **fixed finite set** of ideals (divisors of a power of `rad(m)`),
each contributing a fixed shift `b = Frob` of the bad part and a `O(1)` count beyond a bounded
norm; for each such bad part `b` the residual good factor `𝔞'` (`N𝔞'` coprime to `m`,
`Frob_𝔞' = g·Frob(b)⁻¹`) is counted by L1 applied to the ideal lattice (`idealLattice`, the mathlib
dictionary `tendsto_norm_le_and_mk_eq_div_atTop` puts ideals of norm `≤ N` in bijection with lattice
points of `idealLattice` in the dilate `N^{1/d}·normLeOne`) intersected with the congruence
sublattice cutting out `N𝔞' ≡ a mod m`. Summing the per-good-part congruence count from L1
(`exists_card_inter_smul_lattice_sub_volume_mul_pow_le`, with its `hlip` supplied by
`normLeOne_frontier_lipschitz` — sub-gap 2, Gun–Ramaré–Sivaraman §3.3) over the finite bad-part set
yields the effective `O(N^{1−1/d})` rate, and the leading covolume term is the same ratio for every
`g` — hence `κ` is `g`-independent (the ℚ(i)-trap avoidance: uniformity is over `g ∈ G`, the norm
image, not over all of `(ℤ/m)ˣ`).

**Residual sorry:** the bad-prime split + lattice↔ideal congruence-coset bookkeeping (sub-gap 3),
built on the already-extracted Lipschitz-boundary input `normLeOne_frontier_lipschitz` (sub-gap 2)
feeding the per-good-part L1 application — the residual deep input is
`normLeOne_frontier_lipschitz`. -/
theorem exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] :
    ∃ κ C' : ℝ, ∀ g : Gal(L/K), ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
              (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
                frobeniusIdeal K L 𝔞 = g} : ℝ)
          - κ * (N : ℝ)|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  sorry

/-- **Geometry of numbers (Sharifi 7.1.19, p. 142 — the deferred input).** For a nontrivial
character `χ` of order `n = orderOf χ`, the number of nonzero ideals `𝔞 ⊆ 𝓞 K` with `N𝔞 ≤ N`
and `χ(𝔞) = ζ` is `C·N + O(N^{1-1/d})` (`d = [K:ℚ]`), with the **leading constant `C` independent
of `ζ`**. Verbatim (p. 142):
> "The geometry of numbers can be used to show that the number of ideals `𝔞` of `𝒪_K` with
> `N𝔞 ≤ N` for `N ≥ 1` and `χ(𝔞) = ζ` is `CN + O(N^{1−d⁻¹})`, where `C` is a constant
> independent of `ζ`."

**Restated at cyclotomic generality** (expert review 2026-06-05): the general-abelian value-fibre
count needs class field theory, but for `L = K(μ_m)` it is CFT-free. The reduction is now an
**exact set equality** (not a thin-error bridge): for `ζ ≠ 0` the value-fibre `{χ(𝔞) = ζ}` equals
the **unramified-supported** Frobenius-value-fibre `{U 𝔞 ∧ χ(Frob_𝔞) = ζ}`, where
`U 𝔞 := ∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭`
(`card_valueFibre_eq_card_unramifiedSupported_frobeniusValueFibre`, Helper 1a) — `U` is the exact
support condition `χ(𝔞) ≠ 0`, since `χ(𝔞) = 0` whenever a factor is ramified while the junk-class
`Frob_𝔞` ignores ramified factors. Partitioning that fibre over `S_ζ = {g : χ g = ζ}`
(`|S_ζ| = |ker χ|`, `card_charFibre_eq_card_ker`) and applying the **unramified-supported**
Frobenius-fibre equidistribution (`exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le`, L2) per `g`,
with leading density `κ` independent of `g`, gives `C = |ker χ|·κ` and `C' = |ker χ|·C₂`, both
independent of `ζ`. The
class-independent leading term is mathlib's `tendsto_norm_le_and_mk_eq_div_atTop`; the new content —
the project's single deepest analytic gap — is the effective `O(N^{1-1/d})` boundary rate, supplied
by `Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le` (the effective
Lipschitz-boundary lattice-point count in `ForMathlib/LatticePointCount.lean`, a standalone
mathlib-PR) fed by the Lipschitz-frontier input `normLeOne_frontier_lipschitz`. -/
theorem exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    ∃ C C' : ℝ, ∀ ζ : ℂ, ζ ^ orderOf χ = 1 → ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = ζ} : ℝ)
          - C * (N : ℝ)|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  -- The unramified-supported Frobenius-fibre equidistribution (L2): `κ` is the common leading
  -- density.
  obtain ⟨κ, C₂, hL2⟩ := exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le K L m
  -- The constant fibre cardinality `κ₀ = |ker χ|`.
  set κ₀ : ℕ := Nat.card (MonoidHom.ker χ) with hκ₀
  -- Leading constant `C = κ₀·κ`; error constant `C' = κ₀·C₂` (no bridge term: `A = B` exactly).
  refine ⟨(κ₀ : ℝ) * κ, (κ₀ : ℝ) * C₂, fun ζ hζ N hN => ?_⟩
  set P : ℝ := (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) with hP
  -- `ζ` is a unit (root of unity), lift it to `ℂˣ`.
  have hord : 0 < orderOf χ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite χ)
  have hζ0 : ζ ≠ 0 := by
    intro h; subst h
    rw [zero_pow hord.ne'] at hζ
    exact zero_ne_one hζ
  set ζu : ℂˣ := Units.mk0 ζ hζ0 with hζu
  have hζuval : (ζu : ℂ) = ζ := rfl
  have hζun : ζu ^ orderOf χ = 1 := by
    apply Units.ext; push_cast; rw [hζuval]; exact hζ
  -- **Step (1): value-fibre = unramified-supported Frobenius-value-fibre `B` (exact set
  -- equality, Helper 1a).**
  set B : ℝ := (Nat.card {𝔞 : Ideal (𝓞 K) //
      𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
        (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
          (χ (frobeniusIdeal K L 𝔞) : ℂ) = ζ} : ℝ) with hB
  have hAB : (Nat.card {𝔞 : Ideal (𝓞 K) //
      𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ galoisCharacterOnIdeal K L χ 𝔞 = ζ} : ℝ) = B := by
    rw [hB]
    exact congrArg _
      (card_valueFibre_eq_card_unramifiedSupported_frobeniusValueFibre K L m χ ζ hζ0 N)
  rw [hAB]
  -- **Step (2): partition `B` by the value `g = frobeniusIdeal 𝔞 ∈ S_ζ`.**
  -- `S_ζ := {g : χ g = ζ}` is a Fintype (`Gal(L/K)` finite); the fibre splits as a `Sigma`,
  -- the unramified-support field `U` carried through unchanged.
  have hpart : B = ∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
      (Nat.card {𝔞 : Ideal (𝓞 K) //
        𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
          (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
            frobeniusIdeal K L 𝔞 = g.1} : ℝ) := by
    haveI hfinN : Finite {𝔞 : Ideal (𝓞 K) // Ideal.absNorm 𝔞 ≤ N} :=
      (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) N).to_subtype
    have hfin : ∀ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
        Finite {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
            (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
              frobeniusIdeal K L 𝔞 = g.1} := fun g =>
      Finite.of_injective
        (fun a => (⟨a.1, a.2.2.1⟩ : {𝔞 : Ideal (𝓞 K) // Ideal.absNorm 𝔞 ≤ N}))
        (fun _ _ hab => by ext1; simpa using hab)
    rw [hB, ← Nat.cast_sum, ← Nat.card_sigma]
    congr 1
    -- Build the bijection `(Σ g : S_ζ, {U ∧ frob = g}) ≃ {U ∧ χ(frob) = ζ}` by dropping `g`.
    -- Forward: `⟨⟨g, χg=ζ⟩, ⟨𝔞, _, _, U, frob 𝔞 = g⟩⟩ ↦ 𝔞`, `χ(frob 𝔞) = χ g = ζ`.
    refine (Nat.card_congr (Equiv.ofBijective
      (fun a => (⟨a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.1, by rw [a.2.2.2.2.2]; exact a.1.2⟩ :
        {𝔞 : Ideal (𝓞 K) //
          𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
            (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
              (χ (frobeniusIdeal K L 𝔞) : ℂ) = ζ})) ⟨?_, ?_⟩)).symm
    · -- injective: the underlying ideals agree, and `g` is determined as `frob 𝔞`
      rintro ⟨⟨g₁, hg₁⟩, ⟨𝔞, ha1, ha2, haU, ha3⟩⟩ ⟨⟨g₂, hg₂⟩, ⟨𝔟, hb1, hb2, hbU, hb3⟩⟩ hab
      have h𝔞𝔟 : 𝔞 = 𝔟 := congrArg Subtype.val hab
      subst h𝔞𝔟
      have hg : g₁ = g₂ := ha3.symm.trans hb3
      subst hg
      rfl
    · -- surjective: take `g = frob 𝔞`
      rintro ⟨𝔞, h1, h2, hU, h3⟩
      exact ⟨⟨⟨frobeniusIdeal K L 𝔞, h3⟩, ⟨𝔞, h1, h2, hU, rfl⟩⟩, rfl⟩
  -- **Step (3): apply the unramified-supported L2 to each `g ∈ S_ζ`, sum over the finite fibre.**
  -- `|B − |S_ζ|·κ·N| ≤ |S_ζ|·C₂·P` by the triangle inequality over the fibre.
  have hSκ₀ : Nat.card {g : Gal(L/K) // (χ g : ℂ) = ζ} = κ₀ := by
    rw [hκ₀]
    have heq : {g : Gal(L/K) // (χ g : ℂ) = ζ} = {g : Gal(L/K) // χ g = ζu} := by
      congr 1; ext g
      rw [← hζuval]
      exact ⟨fun h => Units.ext h, fun h => congrArg Units.val h⟩
    rw [heq]
    exact card_charFibre_eq_card_ker K L χ ζu hζun
  have hcardℝ : (Fintype.card {g : Gal(L/K) // (χ g : ℂ) = ζ} : ℝ) = (κ₀ : ℝ) := by
    rw [← Nat.card_eq_fintype_card, hSκ₀]
  -- **Combine (1)+(2)+(3):** `|B − C·N| ≤ κ₀·C₂·P`.
  rw [hpart]
  calc
    |∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
          (Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
              (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
                frobeniusIdeal K L 𝔞 = g.1} : ℝ)
          - (κ₀ : ℝ) * κ * N|
        = |∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
            ((Nat.card {𝔞 : Ideal (𝓞 K) //
              𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
                (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
                  frobeniusIdeal K L 𝔞 = g.1} : ℝ) - κ * N)| := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardℝ]
          ring_nf
    _ ≤ ∑ g : {g : Gal(L/K) // (χ g : ℂ) = ζ},
          |(Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
              (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
                frobeniusIdeal K L 𝔞 = g.1} : ℝ) - κ * N| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _g : {g : Gal(L/K) // (χ g : ℂ) = ζ}, C₂ * P :=
          Finset.sum_le_sum fun g _ => hL2 g.1 N hN
    _ = (κ₀ : ℝ) * C₂ * P := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardℝ]; ring

/-- Sharifi 7.1.19 step 1 (p. 142): geometry-of-numbers bound. The
partial-sum character sum `Σ_{N𝔞≤N} χ(𝔞)` (with `χ(𝔞) = galoisCharacterOnIdeal K L χ 𝔞` the
completely-multiplicative ideal character) is `O(N^{1-1/[K:ℚ]})` for a
nontrivial character `χ`. This is the convergence input that extends
`L(χ,·)` to `Z(1 - [K:ℚ]^{-1})`. -/
theorem character_sum_geometry_of_numbers_bound
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ N : ℕ,
      ‖∑' 𝔞 : {𝔞 : Ideal (𝓞 K) //
                𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N},
        galoisCharacterOnIdeal K L χ 𝔞.1‖
        ≤ C * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  -- Two steps (Sharifi p. 142). (1) Geometry of numbers
  -- (`exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow`): for every `n`-th root of unity
  -- `ζ` (`n = orderOf χ`), `#{N𝔞 ≤ N | χ(𝔞) = ζ} = C·N + O(N^{1-1/d})` with `C` independent of
  -- `ζ`. (2) Cancellation: `Σ_{N𝔞 ≤ N} χ(𝔞) = Σ_{ζ^n = 1} ζ · #fibre_ζ`, and the leading term
  -- vanishes because `Σ_{ζ^n = 1} ζ = 0` for `n ≥ 2`, leaving the `O(N^{1-1/d})` tail.
  obtain ⟨_C, C', _hcount⟩ := exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow K L m χ _hχ
  refine ⟨(orderOf χ : ℝ) * C', fun N => ?_⟩
  sorry

/-- Sharifi 7.1.19 step 1b (p. 142) — analytic extension of `L(χ,·)`.
Combining the geometry-of-numbers bound
`character_sum_geometry_of_numbers_bound`
with Sharifi Lemma 7.1.5 (p. 138, a generic Dirichlet-series
convergence criterion given a polynomial bound on partial sums), the
Dirichlet series `L(χ,s) = Σ_𝔞 χ(𝔞) N𝔞^{-s}` converges absolutely and
uniformly on every compact subset of `Z(1 - 1/[K:ℚ])`, defining an
analytic extension of `L(χ,·)` from `Re s > 1` to that half-plane.

Source quote (verbatim, p. 142):
> "By Lemma 7.1.5, we therefore have that `Σ_𝔞⊂𝓞_K χ(𝔞) N𝔞^{-s}`
> converges absolutely and uniformly on every compact subset of
> `Z(1 - d^{-1})`."

Mathlib analogue of Sharifi Lemma 7.1.5:
`LSeries.summable_of_partial_sums_le_const_mul_rpow` (or the
`LSeries.tendsto_neg_logDerivLSeries_eq_*` machinery in
`Mathlib.NumberTheory.LSeries.*`). -/
theorem artinLSeries_analytic_extension
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (χ : galoisCharacter K L)
    (_hχ : χ ≠ 1) :
    ∃ Lf : ℂ → ℂ,
      AnalyticOn ℂ Lf {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        Lf s =
          ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
            galoisCharacterOnIdeal K L χ 𝔞.1 *
              (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)) := by
  sorry

/-! ### Sub-lemmas for `artinLSeries_one_ne_zero` (Sharifi 7.1.19 step 2, p. 142)

The non-vanishing of `L(χ, 1)` for nontrivial `χ` is Dirichlet's argument, run globally over all
characters. The contradiction is purely real-variable: on real `s ↓ 1`,

* **(B)** `log ζ_L(s) ≥ log(1/(s-1)) - C` diverges to `+∞` (the simple pole of `ζ_L`); this is
  `Density.logDedekindZeta_sub_log_inv_sub_one_bounded` applied to the field `L`.
* **(A)** the factorisation `ζ_L(s) = ∏_χ L_χ(s)` (Sharifi 7.1.16) makes
  `log ζ_L(s) = Σ_χ log‖L_χ(s)‖` (the product is over the *finite* character group and
  `ζ_L(s)` is a positive real for real `s`).
* **(C)** if one nontrivial factor `Lf` has `Lf 1 = 0`, then `log‖Lf(s)‖ ≤ -log(1/(s-1)) + C`
  (an analytic zero of order `≥ 1`), while every other factor is bounded above. Summing, the pole
  of `L_1 = ζ_K` is cancelled by the zero and `log ζ_L(s)` stays bounded — contradicting (B).
-/

open Filter Topology Set in
/-- **Ingredient B.** `log (ζ_L(s)).re → +∞` as the real argument `s ↓ 1`, driven by the simple
pole of the Dedekind zeta of `L` at `s = 1`. This is `logDedekindZeta_sub_log_inv_sub_one_bounded`
(Sharifi 7.1.12, in `Density.lean`) applied to the number field `L`, squeezed against
`log(1/(s-1)) → +∞`. -/
private theorem logDedekindZeta_re_tendsto_atTop
    (L : Type*) [Field L] [NumberField L] :
    Tendsto (fun s : ℝ ↦ Real.log (NumberField.dedekindZeta L (s : ℂ)).re)
      (𝓝[>] (1 : ℝ)) atTop := by
  obtain ⟨C, hC⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded L
  -- The lower bound `log(1/(s-1)) - C` already tends to `+∞`.
  have hlog : Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1)) + -C) (𝓝[>] (1 : ℝ)) atTop :=
    tendsto_log_one_div_sub_one_atTop.atTop_add tendsto_const_nhds
  refine tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [hC] with s hs
  have := (abs_le.mp hs).1
  linarith

open Filter Topology Set in
/-- **Ingredient C.** If `f` is analytic at `1`, has a zero there (`f 1 = 0`), and is not locally
identically zero, then near `s ↓ 1` (real) the log-norm `log‖f s‖` is bounded **above** by
`-log(1/(s-1)) + C`. Proof: `exists_eventuallyEq_pow_smul_nonzero_iff` factors `f z = (z-1)^n g z`
with `g 1 ≠ 0` and (since `f 1 = 0`) `n ≥ 1`; then `log‖f s‖ = n·log(s-1) + log‖g s‖`, and on a
right neighbourhood of `1` we have `s - 1 ∈ (0,1)` (so `log(s-1) < 0`, hence `n·log(s-1) ≤
log(s-1) = -log(1/(s-1))`) and `‖g s‖` is bounded by continuity. -/
private theorem analytic_log_norm_le_of_apply_eq_zero {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 1) (hf0 : f 1 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (1 : ℂ), f z = 0) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖f (s : ℂ)‖ ≤ - Real.log (1 / (s - 1)) + C := by
  obtain ⟨n, g, hg_an, hg_ne, hg_eq⟩ :=
    (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff hf).mpr hne
  -- The order is `≥ 1`: at `n = 0` the factorisation would give `f 1 = g 1 ≠ 0`.
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h; swap; · exact h
    exfalso
    apply hg_ne
    have := hg_eq.self_of_nhds
    rw [h0, pow_zero, one_smul] at this
    rw [← this, hf0]
  -- `g` is continuous at `1` with `g 1 ≠ 0`: near `1`, `‖g‖` is bounded above and `g ≠ 0`.
  have hg_cont : ContinuousAt g 1 := hg_an.continuousAt
  have hCg : ∀ᶠ z in 𝓝 (1 : ℂ), ‖g z‖ ≤ ‖g 1‖ + 1 := by
    filter_upwards [hg_cont.norm.eventually (Metric.ball_mem_nhds ‖g 1‖ one_pos)] with z hz
    rw [Real.dist_eq] at hz
    linarith [(abs_lt.mp hz).2]
  have hg0 : ∀ᶠ z in 𝓝 (1 : ℂ), g z ≠ 0 := hg_cont.eventually_ne hg_ne
  refine ⟨‖g 1‖ + 1, ?_⟩
  -- Pull the complex factorisation and the bounds on `g` back along `s ↦ (s : ℂ)`.
  have hmap : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp nhdsWithin_le_nhds
  -- on `(1, 2)` we have `s - 1 ∈ (0, 1)`
  have hIoo : Set.Ioo (1 : ℝ) 2 ∈ 𝓝[>] (1 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [hmap.eventually hg_eq, hmap.eventually hCg, hmap.eventually hg0, hIoo]
    with s hfeq hgle hgne hsmem
  obtain ⟨hs1, hs2⟩ := hsmem
  have hpos : (0 : ℝ) < s - 1 := by linarith
  have hlt1 : s - 1 < 1 := by linarith
  have hgpos : (0 : ℝ) < ‖g (s : ℂ)‖ := norm_pos_iff.mpr hgne
  -- factor the norm: `‖f s‖ = (s-1)^n · ‖g s‖`
  have hnorm : ‖f (s : ℂ)‖ = (s - 1) ^ n * ‖g (s : ℂ)‖ := by
    rw [hfeq, norm_smul, norm_pow]
    congr 2
    rw [show ((s : ℂ) - 1) = (((s - 1 : ℝ)) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg hpos.le]
  rw [hnorm, Real.log_mul (by positivity) hgpos.ne', Real.log_pow]
  -- `n·log(s-1) ≤ log(s-1) = -log(1/(s-1))` (since `n ≥ 1` and `log(s-1) < 0`), and `log‖g s‖ ≤ Cg`
  have hlog_neg : Real.log (s - 1) < 0 := Real.log_neg hpos hlt1
  have hn_ge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn_step : (n : ℝ) * Real.log (s - 1) ≤ Real.log (s - 1) := by
    nlinarith [hn_ge, hlog_neg]
  have hloginv : - Real.log (1 / (s - 1)) = Real.log (s - 1) := by
    rw [one_div, Real.log_inv, neg_neg]
  rw [hloginv]
  have hgle' : Real.log ‖g (s : ℂ)‖ ≤ ‖g 1‖ + 1 := by
    calc Real.log ‖g (s : ℂ)‖ ≤ Real.log (‖g 1‖ + 1) :=
          Real.log_le_log hgpos hgle
      _ ≤ ‖g 1‖ + 1 := Real.log_le_self (by positivity)
  linarith

/-- The character group `galoisCharacter K L = Gal(L/K) →* ℂˣ` is finite (`Gal(L/K)` is a finite
group). A local `Fintype` instance so the finite products/sums `∏ χ` / `∑ χ` over the character
group parse in the statements below. -/
local instance galoisCharacter.instFintype
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] : Fintype (galoisCharacter K L) :=
  Fintype.ofFinite _

/-- The Dirichlet series `L_χ(s) = ∑'_{𝔞 ≠ ⊥} χ(𝔞) N𝔞^{-s}` of a Galois character, as a function
of `s`. This is the analytic engine of Sharifi 7.1.16–7.1.19; for `1 < Re s` it equals the Euler
product over unramified primes (`exists_artinLSeries_eulerProduct_abelian`). -/
private noncomputable def artinDirichletSeries
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (s : ℂ) : ℂ :=
  ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
    galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)

/-- Pure-`ℂ` Euler-factor estimate: if `‖y‖ ≤ 1/2` then `‖(1 - y)^{-1} - 1‖ ≤ 2‖y‖`.
The shift is `(1 - y)^{-1} - 1 = y · (1 - y)^{-1}`, and `‖(1 - y)^{-1}‖ ≤ 2` because
`‖1 - y‖ ≥ 1 - ‖y‖ ≥ 1/2`. This is the per-factor bound feeding
`multipliable_one_add_of_summable` for both the Dedekind prime product and the χ-twisted local
Euler product. -/
private theorem norm_one_sub_inv_sub_one_le {y : ℂ} (hy : ‖y‖ ≤ 1 / 2) :
    ‖(1 - y)⁻¹ - 1‖ ≤ 2 * ‖y‖ := by
  have hyne1 : (1 : ℂ) - y ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    have : ‖y‖ = 1 := by rw [← h, norm_one]
    rw [this] at hy; norm_num at hy
  have heq : (1 - y)⁻¹ - 1 = y * (1 - y)⁻¹ := by field_simp; ring
  rw [heq, norm_mul]
  have hnorm_lb : (2 : ℝ)⁻¹ ≤ ‖(1 : ℂ) - y‖ :=
    calc (2 : ℝ)⁻¹ = 1 - 1 / 2 := by norm_num
      _ ≤ 1 - ‖y‖ := by linarith
      _ ≤ ‖(1 : ℂ)‖ - ‖y‖ := by rw [norm_one]
      _ ≤ ‖(1 : ℂ) - y‖ := norm_sub_norm_le 1 y
  have hinv : ‖(1 - y)⁻¹‖ ≤ 2 := by
    rw [norm_inv, show (2 : ℝ) = (2⁻¹ : ℝ)⁻¹ by norm_num]
    exact inv_anti₀ (by norm_num) hnorm_lb
  calc ‖y‖ * ‖(1 - y)⁻¹‖ ≤ ‖y‖ * 2 := by gcongr
    _ = 2 * ‖y‖ := by ring

/-- For a nonzero prime `𝔭` of a number ring and `Re s > 1`, `‖N𝔭^{-s}‖ ≤ 1/2` (since `N𝔭 ≥ 2`,
`Re s > 1`). The bound that lets the Euler factors enter `norm_one_sub_inv_sub_one_le`. -/
private theorem norm_absNorm_cpow_neg_le_half {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R] {s : ℂ} (hs : 1 < s.re)
    (𝔭 : {𝔭 : Ideal R // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h => 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
  have h2le : 2 ≤ Ideal.absNorm 𝔭.1 := by
    have hne1 : Ideal.absNorm 𝔭.1 ≠ 1 := fun h => 𝔭.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    have : 0 < Ideal.absNorm 𝔭.1 := by lia
    lia
  have hpos : 0 < Ideal.absNorm 𝔭.1 := by lia
  rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
  have hb1 : (1 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by exact_mod_cast (by lia : 1 ≤ Ideal.absNorm 𝔭.1)
  have hb2 : (2 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by exact_mod_cast h2le
  calc (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re)
      ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
    _ = ((Ideal.absNorm 𝔭.1 : ℝ))⁻¹ := Real.rpow_neg_one _
    _ ≤ (2 : ℝ)⁻¹ := by rw [inv_le_inv₀ (by linarith) (by norm_num)]; exact hb2
    _ = 1 / 2 := by norm_num

/-- The Euler factor `(1 - N𝔓^{-s})^{-1}` of a nonzero prime `𝔓` of `𝓞 L`, written additively as
`1 + g 𝔓` with `g 𝔓 = (1 - N𝔓^{-s})^{-1} - 1`. Its norm is `≤ 2‖N𝔓^{-s}‖`
(`norm_one_sub_inv_sub_one_le`), and `∑_𝔓 ‖N𝔓^{-s}‖` converges (a sub-sum of the absolutely
convergent `ζ_L`). -/
private theorem summable_norm_primeIdeal_factor_sub_one
    (L : Type*) [Field L] [NumberField L] {s : ℂ} (hs : 1 < s.re) :
    Summable fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} =>
      ‖(1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ - 1‖ := by
  -- `∑_𝔞 ‖N𝔞^{-s}‖` over all nonzero ideals converges; restrict to nonzero primes.
  have hsum : Summable fun 𝔞 : NonzeroIdeal L => ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)‖ :=
    (hasSum_nonzeroIdeal_absNorm_cpow L hs).summable.norm
  have hsumP : Summable fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} =>
      ‖(Ideal.absNorm 𝔓.1 : ℂ) ^ (-s)‖ :=
    hsum.comp_injective (i := fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} =>
      (⟨𝔓.1, 𝔓.2.2⟩ : NonzeroIdeal L))
      (fun a b h => by apply Subtype.ext; simpa using h)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun 𝔓 => ?_) (hsumP.mul_left 2)
  exact norm_one_sub_inv_sub_one_le (norm_absNorm_cpow_neg_le_half (R := 𝓞 L) hs 𝔓)

/-- The prime-ideal Euler product of `ζ_L` is `Multipliable`, with `HasProd` value `ζ_L(s)`.
`Multipliable` (hence the partition / fiberwise-regrouping lemmas) follows from absolute
convergence (`summable_norm_primeIdeal_factor_sub_one`), and the value is pinned by the
prime-ideal Euler product `dedekindZeta_eq_tprod_primeIdeal`. -/
private theorem hasProd_primeIdeal_factor
    (L : Type*) [Field L] [NumberField L] {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} =>
        (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹) (NumberField.dedekindZeta L s) := by
  have hmul : Multipliable fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} =>
      (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ := by
    have := multipliable_one_add_of_summable
      (f := fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} =>
        (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ - 1)
      (summable_norm_primeIdeal_factor_sub_one L hs)
    simpa using this
  rw [dedekindZeta_eq_tprod_primeIdeal L hs]
  exact hmul.hasProd

/-- The prime-ideal Euler factor restricted to any predicate-subtype of the nonzero primes is
`Multipliable`. (`Multipliable.subtype` is avoided — it `comp_injective`s and whnf-explodes on the
`Ideal (𝓞 L)` prime subtype; we restrict the *summable* norm via `Summable.subtype`, which does not,
then rebuild multipliability with `multipliable_one_add_of_summable`.) -/
private theorem multipliable_primeIdeal_factor_subtype
    (L : Type*) [Field L] [NumberField L] {s : ℂ} (hs : 1 < s.re)
    (p : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} → Prop) :
    Multipliable fun 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // p 𝔓} =>
      (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹ := by
  have hsum : Summable ((fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} =>
      ‖(1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ - 1‖) ∘ (↑) :
      {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // p 𝔓} → ℝ) :=
    (summable_norm_primeIdeal_factor_sub_one L hs).subtype p
  simpa using multipliable_one_add_of_summable
    (f := fun 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // p 𝔓} =>
      (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹ - 1) hsum

/-- The χ-twisted local Euler product `∏'_{𝔭 unram} (1 - χ(σ_𝔭) N𝔭^{-s})^{-1} = L_χ` is
`Multipliable`. As for `ζ_L`, this is absolute convergence: `‖χ(σ_𝔭)‖ = 1`
(`norm_galoisCharacter_out`), so `‖χ(σ_𝔭) N𝔭^{-s}‖ = ‖N𝔭^{-s}‖ ≤ 1/2`, and `∑_{𝔭 unram} ‖N𝔭^{-s}‖`
is a sub-sum of the absolutely convergent `ζ_K`. -/
private theorem multipliable_artinLocalFactor
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) {s : ℂ} (hs : 1 < s.re) :
    Multipliable fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} =>
      (1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ := by
  -- summability of `∑_{𝔭 unram} ‖N𝔭^{-s}‖`, by injecting into the nonzero ideals of `𝓞 K`
  have hsum : Summable fun 𝔞 : NonzeroIdeal K => ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)‖ :=
    (hasSum_nonzeroIdeal_absNorm_cpow K hs).summable.norm
  have hsumP : Summable fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} =>
      ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ :=
    hsum.comp_injective (i := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} =>
      (⟨𝔭.1, UnramifiedIn.ne_bot K L 𝔭.2.2⟩ : NonzeroIdeal K))
      (fun a b h => by apply Subtype.ext; simpa using h)
  have hsummable : Summable fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} =>
      ‖(1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ - 1‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun 𝔭 => ?_) (hsumP.mul_left 2)
    set y : ℂ := (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s) with hy
    have hynorm : ‖y‖ ≤ 1 / 2 := by
      have hpbot : 𝔭.1 ≠ ⊥ := UnramifiedIn.ne_bot K L 𝔭.2.2
      rw [hy, norm_mul, norm_galoisCharacter_out, one_mul]
      exact norm_absNorm_cpow_neg_le_half (R := 𝓞 K) hs ⟨𝔭.1, 𝔭.2.1, hpbot⟩
    calc ‖(1 - y)⁻¹ - 1‖ ≤ 2 * ‖y‖ := norm_one_sub_inv_sub_one_le hynorm
      _ = 2 * ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ := by
          rw [hy, norm_mul, norm_galoisCharacter_out, one_mul]
  have := multipliable_one_add_of_summable
    (f := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} =>
      (1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ - 1) hsummable
  simpa using this

/-- The map sending an unramified-below `L`-prime `𝔓` to the unramified `K`-prime `𝔓.under` below
it. A fixed `def` (rather than an inline term with `inferInstance`) so the fibre subtypes parse
without instance-resolution headaches. -/
private def underUP
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ UnramifiedIn K L (𝔓.under (𝓞 K))}) :
    {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} :=
  ⟨𝔓.1.under (𝓞 K), by haveI := 𝔓.2.1; exact inferInstance, 𝔓.2.2.2⟩

@[simp] private theorem underUP_val
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ UnramifiedIn K L (𝔓.under (𝓞 K))}) :
    (underUP K L 𝔓).1 = 𝔓.1.under (𝓞 K) := rfl

set_option maxHeartbeats 800000 in
/-- The fibre of `underUP` over an unramified `K`-prime `c` is, after reindexing, the set of primes
`𝔓` of `𝓞 L` lying over `c` (`LiesOver`). Used to match the fibre product against
`dedekindZeta_local_factor_eq_product_artin_local`. -/
private def fiberUnderEquiv
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (c : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭}) :
    {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ UnramifiedIn K L (𝔓.under (𝓞 K))} //
        underUP K L 𝔓 = c} ≃
      {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver c.1 ∧ 𝔓 ≠ ⊥} where
  toFun 𝔓 := ⟨𝔓.1.1, 𝔓.1.2.1, ⟨by
    have h := congrArg Subtype.val 𝔓.2; rw [underUP_val] at h; rw [← h]⟩, 𝔓.1.2.2.1⟩
  invFun 𝔔 := ⟨⟨𝔔.1, 𝔔.2.1, 𝔔.2.2.2, by
      haveI := 𝔔.2.1; haveI := 𝔔.2.2.1; rw [← 𝔔.2.2.1.over]; exact c.2.2⟩,
    by haveI := 𝔔.2.1; haveI := 𝔔.2.2.1; exact Subtype.ext (by rw [underUP_val]; exact 𝔔.2.2.1.over.symm)⟩
  left_inv 𝔓 := by ext; rfl
  right_inv 𝔔 := by ext; rfl

set_option maxHeartbeats 1600000 in
/-- The unramified part of the prime-ideal Euler product equals `∏_χ L_χ`. Regroup the unramified
`L`-primes fibrewise over the `K`-prime below them (`Equiv.sigmaFiberEquiv` +
`Multipliable.tprod_sigma`); each fibre product is `∏_χ (1 - χ(σ_𝔭) N𝔭^{-s})^{-1}`
(`dedekindZeta_local_factor_eq_product_artin_local`, `fiberUnderEquiv`); swap the finite character
product out (`Multipliable.tprod_finsetProd`) and apply the abelian Euler product
(`exists_artinLSeries_eulerProduct_abelian`). -/
private theorem tprod_unramified_eq_prod_artinDirichletSeries
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] {s : ℂ} (hs : 1 < s.re) :
    (∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          UnramifiedIn K L (𝔓.under (𝓞 K))},
        (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹)
      = ∏' χ : galoisCharacter K L, artinDirichletSeries K L χ s := by
  classical
  -- abstract the Euler factor so the reindexing lemmas never unfold `Ideal.absNorm`
  set F : Ideal (𝓞 L) → ℂ := fun 𝔭 => (1 - (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ with hF
  set G : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} → ℂ :=
    fun c => ∏' χ : galoisCharacter K L,
      (1 - (χ (frobeniusClass K L c.1).out : ℂ) * (Ideal.absNorm c.1 : ℂ) ^ (-s))⁻¹ with hG
  -- multipliability of `F` over the unramified-below primes `U`, via absolute convergence.
  -- (`Multipliable.subtype` is avoided — it whnf-explodes on the `Ideal (𝓞 L)` prime subtype;
  -- instead restrict the *summable* norm via `Summable.subtype`, then rebuild multipliability.)
  have hmulU : Multipliable fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      UnramifiedIn K L (𝔓.under (𝓞 K))} => F 𝔓.1 := by
    have hsumU : Summable ((fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} =>
        ‖(1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ - 1‖) ∘ (↑) :
        {x : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
          UnramifiedIn K L (x.1.under (𝓞 K))} → ℝ) :=
      (summable_norm_primeIdeal_factor_sub_one L hs).subtype
        (fun 𝔓 => UnramifiedIn K L (𝔓.1.under (𝓞 K)))
    have hmul1 : Multipliable fun 𝔓 : {x : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
        UnramifiedIn K L (x.1.under (𝓞 K))} => F 𝔓.1.1 := by
      simpa [hF] using multipliable_one_add_of_summable
        (f := fun 𝔓 : {x : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
            UnramifiedIn K L (x.1.under (𝓞 K))} =>
          (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹ - 1) hsumU
    let e : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ UnramifiedIn K L (𝔓.under (𝓞 K))} ≃
        {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
          UnramifiedIn K L (𝔓.1.under (𝓞 K))} :=
      { toFun := fun 𝔓 => ⟨⟨𝔓.1, 𝔓.2.1, 𝔓.2.2.1⟩, 𝔓.2.2.2⟩
        invFun := fun 𝔓 => ⟨𝔓.1.1, 𝔓.1.2.1, 𝔓.1.2.2, 𝔓.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Equiv.multipliable_iff e).mpr hmul1
  -- each fibre over `c` is finite (finitely many primes above `c`) and its product is `G c`
  have hfibHasProd : ∀ c : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
      HasProd (fun 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          UnramifiedIn K L (𝔓.under (𝓞 K))} // underUP K L 𝔓 = c} => F 𝔓.1.1) (G c) := by
    intro c
    haveI : c.1.IsPrime := c.2.1
    haveI : c.1.IsMaximal := c.2.1.isMaximal (UnramifiedIn.ne_bot K L c.2.2)
    haveI : Finite (c.1.primesOver (𝓞 L)) := (IsDedekindDomain.primesOver_finite c.1 (𝓞 L)).to_subtype
    haveI : Finite {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver c.1 ∧ 𝔓 ≠ ⊥} :=
      Finite.of_injective
        (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver c.1 ∧ 𝔓 ≠ ⊥} =>
          (⟨𝔓.1, 𝔓.2.1, 𝔓.2.2.1⟩ : c.1.primesOver (𝓞 L)))
        (fun _ _ hab => Subtype.ext (by simpa using hab))
    haveI : Finite {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
        UnramifiedIn K L (𝔓.under (𝓞 K))} // underUP K L 𝔓 = c} :=
      Finite.of_equiv _ (fiberUnderEquiv K L c).symm
    have hval : (∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          UnramifiedIn K L (𝔓.under (𝓞 K))} // underUP K L 𝔓 = c}, F 𝔓.1.1) = G c := by
      simp only [hG]
      rw [← dedekindZeta_local_factor_eq_product_artin_local K L c.1 c.2.2 s hs,
        ← (fiberUnderEquiv K L c).tprod_eq
          (fun 𝔔 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver c.1 ∧ 𝔓 ≠ ⊥} => F 𝔔.1)]
      rfl
    rw [← hval]
    exact (Multipliable.of_finite).hasProd
  -- regroup the unramified product fibrewise (`HasProd.sigma`), giving `∏'_c G c`
  have hsig : HasProd G (∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      UnramifiedIn K L (𝔓.under (𝓞 K))}, F 𝔓.1) :=
    ((Equiv.sigmaFiberEquiv (underUP K L)).hasProd_iff.mpr hmulU.hasProd).sigma hfibHasProd
  rw [← hsig.tprod_eq]
  simp only [hG]
  -- the inner character product is finite, so rewrite `∏'_χ` as `∏_χ`, then swap with `∏'_c`
  simp_rw [tprod_fintype]
  rw [Multipliable.tprod_finsetProd (s := (Finset.univ : Finset (galoisCharacter K L)))
    (f := fun χ : galoisCharacter K L =>
      fun c : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} =>
        (1 - (χ (frobeniusClass K L c.1).out : ℂ) * (Ideal.absNorm c.1 : ℂ) ^ (-s))⁻¹)
    (fun χ _ => multipliable_artinLocalFactor K L χ hs)]
  refine Finset.prod_congr rfl fun χ _ => ?_
  rw [artinDirichletSeries, ← exists_artinLSeries_eulerProduct_abelian K L χ s hs]

set_option maxHeartbeats 800000 in
/-- **Ingredient A, corrected** (Sharifi 7.1.16, p. 141, with the ramified factor made explicit).
For `1 < Re s`,
`ζ_L(s) = (∏_χ L_χ(s)) · R(s)`, where `L_χ = artinDirichletSeries K L χ` is the Euler product over
**unramified** primes only, and the correction `R(s)` is the (finite) product of the Euler factors
`(1 - N𝔓^{-s})^{-1}` over the primes `𝔓` of `𝓞 L` lying over a **ramified** prime of `𝓞 K`.

The naive identity `ζ_L = ∏_χ L_χ` is FALSE: `L_χ` drops the ramified primes (its ideal coefficient
`χ(𝔭)` is `0` at ramified `𝔭`), whereas `ζ_L = ∏'_{all 𝔓}(1 - N𝔓^{-s})^{-1}` keeps them. `R`
collects exactly the dropped factors. Since only finitely many primes ramify (`finite_ramifiedIn`),
each with finitely many `𝔓` above, `R` is a finite product; it is nonzero for real `s > 1`
(`N𝔓 ≥ 2`).

Proof: the prime-ideal Euler product `ζ_L = ∏'_𝔓 (1 - N𝔓^{-s})^{-1}` is `Multipliable`
(`hasProd_primeIdeal_factor`); regroup it fiberwise over `𝔭 ↦ 𝔓.under` (`HasProd.tprod_fiberwise`)
and partition the outer product into unramified vs ramified `𝔭`
(`Multipliable.tprod_subtype_mul_tprod_subtype_compl`). At an unramified `𝔭` the fibre product is
`∏_χ (1 - χ(σ_𝔭) N𝔭^{-s})^{-1}` (`dedekindZeta_local_factor_eq_product_artin_local`); swapping the
two finite/convergent products (`tprod_comm`) and summing the per-character Euler product over
unramified primes (`exists_artinLSeries_eulerProduct_abelian`) gives `∏_χ L_χ`. The ramified part is
`R` by definition. -/
private theorem dedekindZeta_eq_prod_artinDirichletSeries
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      (∏' χ : galoisCharacter K L, artinDirichletSeries K L χ s) *
        ∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
            ¬ UnramifiedIn K L (𝔓.under (𝓞 K))},
          (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ := by
  classical
  -- partition the prime product into unramified-below vs ramified-below, via `HasProd.mul_compl`
  -- (the off-the-shelf `tprod_subtype_mul_tprod_subtype_compl` `comp_injective`s and times out)
  have hSU := (multipliable_primeIdeal_factor_subtype L hs
    (fun 𝔓 => UnramifiedIn K L (𝔓.1.under (𝓞 K)))).hasProd
  have hSUc := (multipliable_primeIdeal_factor_subtype L hs
    (fun 𝔓 => ¬ UnramifiedIn K L (𝔓.1.under (𝓞 K)))).hasProd
  have hpart : NumberField.dedekindZeta L s =
      (∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
          UnramifiedIn K L (𝔓.1.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹) *
        ∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
          ¬ UnramifiedIn K L (𝔓.1.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹ :=
    ((hSU.mul_compl hSUc).unique (hasProd_primeIdeal_factor L hs)).symm
  rw [hpart]
  -- the unramified part: flatten the nested subtype to `U`, then apply the unramified lemma
  have hunr : (∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
        UnramifiedIn K L (𝔓.1.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹)
      = ∏' χ : galoisCharacter K L, artinDirichletSeries K L χ s := by
    rw [← tprod_unramified_eq_prod_artinDirichletSeries K L hs]
    let e : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // UnramifiedIn K L (𝔓.1.under (𝓞 K))} ≃
        {𝔔 : Ideal (𝓞 L) // 𝔔.IsPrime ∧ 𝔔 ≠ ⊥ ∧ UnramifiedIn K L (𝔔.under (𝓞 K))} :=
      { toFun := fun 𝔓 => ⟨𝔓.1.1, 𝔓.1.2.1, 𝔓.1.2.2, 𝔓.2⟩
        invFun := fun 𝔔 => ⟨⟨𝔔.1, 𝔔.2.1, 𝔔.2.2.1⟩, 𝔔.2.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Equiv.tprod_eq e (fun 𝔔 => (1 - (Ideal.absNorm 𝔔.1 : ℂ) ^ (-s))⁻¹)
  -- the ramified part: flatten the complement subtype to the `R` index
  have hram : (∏' 𝔓 : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} //
          ¬ UnramifiedIn K L (𝔓.1.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1.1 : ℂ) ^ (-s))⁻¹)
      = ∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
            ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ := by
    let e : {𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} // ¬ UnramifiedIn K L (𝔓.1.under (𝓞 K))} ≃
        {𝔔 : Ideal (𝓞 L) // 𝔔.IsPrime ∧ 𝔔 ≠ ⊥ ∧ ¬ UnramifiedIn K L (𝔔.under (𝓞 K))} :=
      { toFun := fun 𝔓 => ⟨𝔓.1.1, 𝔓.1.2.1, 𝔓.1.2.2, 𝔓.2⟩
        invFun := fun 𝔔 => ⟨⟨𝔔.1, 𝔔.2.1, 𝔔.2.2.1⟩, 𝔔.2.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Equiv.tprod_eq e (fun 𝔔 => (1 - (Ideal.absNorm 𝔔.1 : ℂ) ^ (-s))⁻¹)
  rw [hunr, hram]

/-- The primes `𝔓` of `𝓞 L` lying over a **ramified** `K`-prime form a finite set: only finitely
many `K`-primes ramify (`finite_ramifiedIn`), and each has finitely many primes above it. -/
private instance finite_ramifiedAbove
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    Finite {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ ¬ UnramifiedIn K L (𝔓.under (𝓞 K))} := by
  classical
  -- the base set of ramified `K`-primes is finite
  haveI : Finite {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭} :=
    (finite_ramifiedIn K L).to_subtype
  -- each fibre `primesOver 𝔭` is finite, so the sigma is finite
  haveI : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭},
      Finite (𝔭.1.primesOver (𝓞 L)) := fun 𝔭 => by
    haveI : 𝔭.1.IsPrime := 𝔭.2.1
    haveI : 𝔭.1.IsMaximal := 𝔭.2.1.isMaximal 𝔭.2.2.1
    exact (IsDedekindDomain.primesOver_finite 𝔭.1 (𝓞 L)).to_subtype
  refine Finite.of_injective
    (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ ¬ UnramifiedIn K L (𝔓.under (𝓞 K))} =>
      (show Σ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭},
          𝔭.1.primesOver (𝓞 L) from by
        haveI := 𝔓.2.1
        exact ⟨⟨𝔓.1.under (𝓞 K), inferInstance, Ideal.under_ne_bot (A := 𝓞 K) 𝔓.2.2.1, 𝔓.2.2.2⟩,
          ⟨𝔓.1, 𝔓.2.1, Ideal.over_under (A := 𝓞 K) (P := 𝔓.1)⟩⟩))
    (fun a b hab => Subtype.ext (by simpa using congrArg (fun x => (x.2 : Ideal (𝓞 L))) hab))

/-- For real `s > 1`, `ζ_L(s)` is a (positive) **real** number: it equals the real-cast of its real
part. This is the companion of `dedekindZeta_re_pos_of_one_lt` recording that the value, not just
its real part, is real — the Dirichlet series `∑ₙ (mult n) n^{-s}` has real terms. -/
private theorem dedekindZeta_eq_ofReal_re
    (L : Type*) [Field L] [NumberField L] {s : ℝ} (hs : 1 < s) :
    NumberField.dedekindZeta L (s : ℂ) = ((NumberField.dedekindZeta L (s : ℂ)).re : ℂ) := by
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  set g : ℕ → ℝ := fun n => (idealNormMultiplicity L n : ℝ) * (n : ℝ) ^ (-s) with hg
  have key : ∀ n : ℕ,
      (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) = ((g n : ℝ) : ℂ) := by
    intro n
    have hcast : ((n : ℝ) ^ (-s) : ℝ) = ((n : ℂ) ^ (-(s : ℂ))) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n) (-s)]; norm_cast
    rw [hg]; push_cast [hcast]; ring
  have hsumC : Summable fun n : ℕ => (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
    (summable_idealNormMultiplicity_mul_cpow_neg L hs').of_norm
  have hsumR : Summable g := Complex.summable_ofReal.mp (by simpa only [key] using hsumC)
  have hval : NumberField.dedekindZeta L (s : ℂ) = ((∑' n, g n : ℝ) : ℂ) := by
    rw [dedekindZeta_eq_tsum_idealNormMultiplicity L hs', Complex.ofReal_tsum]
    exact tsum_congr key
  rw [hval, Complex.ofReal_re]

open Filter Topology Set in
/-- The ramified correction factor `R(s) = ∏'_{𝔓 ram-below} (1 - N𝔓^{-s})^{-1}` is a finite product
of factors each continuous at `s = 1` and tending to the finite nonzero limit `(1 - N𝔓^{-1})^{-1}`
(`N𝔓 ≥ 2`). Hence `‖R(s)‖` is bounded away from `0` and `∞` near `s ↓ 1`, so `|log ‖R(s)‖| ≤ C`.
This is the `O(1)` gap between `log ζ_L` and `Σ_χ log ‖L_χ‖` in the corrected factorisation. -/
private theorem log_norm_ramified_factor_bounded
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      |Real.log ‖∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹‖| ≤
        C := by
  classical
  haveI : Fintype {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))} := Fintype.ofFinite _
  set R : ℝ → ℂ := fun s => ∏ 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹ with hR
  -- `N𝔓 ≥ 2`, hence the base is nonzero and `‖N𝔓^{-z}‖ ≤ 1/2 < 1` for `Re z ≥ 1`
  have hbase : ∀ 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (Ideal.absNorm 𝔓.1 : ℂ) ≠ 0 := fun 𝔓 => by
    have hne0 : Ideal.absNorm 𝔓.1 ≠ 0 := fun h => 𝔓.2.2.1 (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast hne0
  -- the denominator `1 - N𝔓^{-1}` is nonzero (its `‖N𝔓^{-1}‖ = 1/N𝔓 ≤ 1/2 < 1`)
  have hden1 : ∀ 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(1 : ℂ))) ≠ 0 :=
    fun 𝔓 => by
    have h2 : 2 ≤ Ideal.absNorm 𝔓.1 := by
      have hne0 : Ideal.absNorm 𝔓.1 ≠ 0 := fun h => 𝔓.2.2.1 (Ideal.absNorm_eq_zero_iff.mp h)
      have hne1 : Ideal.absNorm 𝔓.1 ≠ 1 := fun h => 𝔓.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
      have : 0 < Ideal.absNorm 𝔓.1 := by lia
      lia
    have hlt : ‖(Ideal.absNorm 𝔓.1 : ℂ) ^ (-(1 : ℂ))‖ < 1 := by
      rw [Complex.cpow_neg_one, norm_inv, Complex.norm_natCast]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (by lia : 1 < Ideal.absNorm 𝔓.1))
    intro h
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at hlt
    exact lt_irrefl _ hlt
  -- `R` is continuous at `1` (finite product of continuous factors) and `R 1 ≠ 0`
  have hcont : ContinuousAt R 1 := by
    rw [ContinuousAt, hR]
    refine tendsto_finsetProd _ (fun 𝔓 _ => ?_)
    have hcpow : ContinuousAt (fun s : ℝ => (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ))) 1 :=
      (continuousAt_const_cpow (hbase 𝔓)).comp
        (Complex.continuous_ofReal.continuousAt.neg)
    exact ((continuousAt_const.sub hcpow).inv₀ (by simpa using hden1 𝔓))
  have hR1_ne : R 1 ≠ 0 := by
    rw [hR]
    exact Finset.prod_ne_zero_iff.mpr (fun 𝔓 _ => inv_ne_zero (by simpa using hden1 𝔓))
  -- `log ‖R‖` is continuous at `1` with value `log ‖R 1‖`, hence eventually within `±1` of it
  have hlogcont : ContinuousAt (fun s : ℝ => Real.log ‖R s‖) 1 :=
    hcont.norm.log (norm_ne_zero_iff.mpr hR1_ne)
  refine ⟨|Real.log ‖R 1‖| + 1, ?_⟩
  have hev : ∀ᶠ s : ℝ in 𝓝 (1 : ℝ),
      |Real.log ‖R s‖ - Real.log ‖R 1‖| ≤ 1 := by
    filter_upwards [hlogcont (Metric.closedBall_mem_nhds (Real.log ‖R 1‖) one_pos)] with s hs
    simp only [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq] at hs
    exact hs
  filter_upwards [nhdsWithin_le_nhds hev] with s hs
  -- the goal's `∏'` over the finite ramified set is the `Finset.prod` `R s`
  rw [show (∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹) = R s
    from by rw [hR]; exact tprod_fintype _]
  have htri : |Real.log ‖R s‖| ≤ |Real.log ‖R s‖ - Real.log ‖R 1‖| + |Real.log ‖R 1‖| := by
    have := abs_add_le (Real.log ‖R s‖ - Real.log ‖R 1‖) (Real.log ‖R 1‖)
    simpa using this
  linarith

open Filter Topology Set in
/-- **Ingredient A, bounded real-log form.** Taking `log ‖·‖` of the corrected factorisation
`ζ_L(s) = (∏_χ L_χ(s)) · R(s)` and using that `ζ_L(s)` is a positive real gives
`log ζ_L(s) = Σ_χ log‖L_χ(s)‖ + log‖R(s)‖`. Since the ramified correction `‖R(s)‖` is bounded
away from `0` and `∞` near `s ↓ 1` (`log_norm_ramified_factor_bounded`), the gap between
`log ζ_L(s).re` and `Σ_χ log‖L_χ(s)‖` is `O(1)`. This `O(1)` slack is harmless for the pole-order
contradiction in `artinLSeries_one_ne_zero`. -/
private theorem log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      |Real.log (NumberField.dedekindZeta L (s : ℂ)).re -
        ∑ χ : galoisCharacter K L, Real.log ‖artinDirichletSeries K L χ (s : ℂ)‖| ≤ C := by
  obtain ⟨C, hC⟩ := log_norm_ramified_factor_bounded K L
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with s hCs hs1
  simp only [mem_Ioi] at hs1
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs1
  have hpos : 0 < (NumberField.dedekindZeta L (s : ℂ)).re :=
    dedekindZeta_re_pos_of_one_lt L s hs1
  -- the corrected factorisation, with the finite character product written as a `Finset.prod`
  have hfact : NumberField.dedekindZeta L (s : ℂ) =
      (∏ χ : galoisCharacter K L, artinDirichletSeries K L χ (s : ℂ)) *
        ∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
            ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹ := by
    rw [dedekindZeta_eq_prod_artinDirichletSeries K L hs', tprod_fintype]
  -- `‖ζ_L(s)‖ = (ζ_L(s)).re` (positive real); the two product factors are nonzero
  have hnorm : ‖NumberField.dedekindZeta L (s : ℂ)‖ = (NumberField.dedekindZeta L (s : ℂ)).re := by
    rw [dedekindZeta_eq_ofReal_re L hs1, Complex.norm_real, Real.norm_of_nonneg hpos.le,
      Complex.ofReal_re]
  have hprodχ_ne : (∏ χ : galoisCharacter K L, artinDirichletSeries K L χ (s : ℂ)) ≠ 0 := by
    intro h0
    apply hpos.ne'
    rw [hfact, h0, zero_mul, Complex.zero_re]
  have hR_ne : (∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹) ≠ 0 := by
    intro h0
    apply hpos.ne'
    rw [hfact, h0, mul_zero, Complex.zero_re]
  -- every character factor `‖L_χ(s)‖` is nonzero (else the finite product, hence `ζ_L(s)`, is `0`)
  have hχ_ne : ∀ χ ∈ (Finset.univ : Finset (galoisCharacter K L)),
      ‖artinDirichletSeries K L χ (s : ℂ)‖ ≠ 0 := fun χ _ =>
    norm_ne_zero_iff.mpr (fun hχ0 =>
      hprodχ_ne (Finset.prod_eq_zero (Finset.mem_univ χ) hχ0))
  -- `log ζ_L.re = log‖ζ_L‖ = Σ_χ log‖L_χ‖ + log‖R‖`, so the gap is `log‖R‖`, bounded by `C`
  have hsplit : Real.log (NumberField.dedekindZeta L (s : ℂ)).re =
      (∑ χ : galoisCharacter K L, Real.log ‖artinDirichletSeries K L χ (s : ℂ)‖) +
        Real.log ‖∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
          ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-(s : ℂ)))⁻¹‖ := by
    rw [← hnorm, hfact, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hprodχ_ne) (norm_ne_zero_iff.mpr hR_ne),
      norm_prod, Real.log_prod hχ_ne]
  rw [hsplit]
  simpa using hCs

open Filter Topology Set in
/-- **Assembly helper (ii).** For a nontrivial character `χ'`, the L-series `L_{χ'}` extends
analytically across `s = 1` (`artinLSeries_analytic_extension`, the LF4 leaf), hence `‖L_{χ'}(s)‖`
is bounded above on a right neighbourhood of `s = 1`. (Here `L_{χ'}(s) = artinDirichletSeries`,
which agrees with the analytic extension on `Re s > 1`.) -/
private theorem artinDirichletSeries_norm_le_of_ne_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (χ' : galoisCharacter K L)
    (hχ' : χ' ≠ 1) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), ‖artinDirichletSeries K L χ' (s : ℂ)‖ ≤ C := by
  obtain ⟨Lf', hLf'_an, hLf'_eq⟩ := artinLSeries_analytic_extension K L χ' hχ'
  -- `1` lies in the analyticity domain `{1 - d⁻¹ < re s}` (as `d ≥ 1`, `1 - d⁻¹ < 1`).
  have hdpos : (0 : ℝ) < (Module.finrank ℚ K : ℝ)⁻¹ := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    positivity
  have hmem : (1 : ℂ) ∈ {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} := by
    simp only [Set.mem_setOf_eq, Complex.one_re]; linarith
  -- the domain is open, so `AnalyticOn` upgrades to `AnalyticAt` at the interior point `1`.
  have hDopen : IsOpen {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hcont : ContinuousAt Lf' 1 :=
    ((hDopen.analyticOn_iff_analyticOnNhd.mp hLf'_an) 1 hmem).continuousAt
  -- `Lf'` continuous at `1`, so `‖Lf'‖` is bounded by `‖Lf' 1‖ + 1` near `1`.
  have hmap : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp nhdsWithin_le_nhds
  have hbdd : ∀ᶠ z in 𝓝 (1 : ℂ), ‖Lf' z‖ ≤ ‖Lf' 1‖ + 1 := by
    filter_upwards [hcont.norm.eventually (Metric.ball_mem_nhds ‖Lf' 1‖ one_pos)] with z hz
    rw [Real.dist_eq] at hz
    linarith [(abs_lt.mp hz).2]
  refine ⟨‖Lf' 1‖ + 1, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hmap.eventually hbdd] with s hs1 hbdd_s
  simp only [mem_Ioi] at hs1
  -- on `Re s > 1`, `L_{χ'}(s) = artinDirichletSeries`, so the bound transfers
  have heq : artinDirichletSeries K L χ' (s : ℂ) = Lf' (s : ℂ) := by
    rw [artinDirichletSeries, ← hLf'_eq (s : ℂ) (by simpa using hs1)]
  rw [heq]
  exact hbdd_s

open Filter Topology Set in
/-- **Assembly helper (i).** The trivial-character L-series `L_1(s) = artinDirichletSeries K L 1 s`
is bounded above by the simple-pole asymptotic of `ζ_K`:
`log‖L_1(s)‖ ≤ log(1/(s-1)) + C` near `s ↓ 1`.

`L_1(s) = ∑'_{𝔞} χ̃_1(𝔞) N𝔞^{-s}` with `‖χ̃_1(𝔞)‖ ≤ 1` (`norm_galoisCharacterOnIdeal_le_one`), so
termwise `‖χ̃_1(𝔞) N𝔞^{-s}‖ ≤ N𝔞^{-s}` and hence `‖L_1(s)‖ ≤ ∑'_{𝔞} N𝔞^{-s} = ζ_K(s)`
(`hasSum_nonzeroIdeal_absNorm_cpow` for `K`). For real `s > 1`, `ζ_K(s) ≥ 1` (the unit-ideal term),
so `0 ≤ log ζ_K(s)` and `log ‖L_1(s)‖ ≤ log ζ_K(s) ≤ log(1/(s-1)) + C`
(`logDedekindZeta_sub_log_inv_sub_one_bounded` for `K`). -/
private theorem log_norm_artinDirichletSeries_one_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖artinDirichletSeries K L 1 (s : ℂ)‖ ≤ Real.log (1 / (s - 1)) + C := by
  obtain ⟨C, hC⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded K
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with s hCs hs1
  simp only [mem_Ioi] at hs1
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs1
  -- `ζ_K(s)` as the absolutely convergent ideal sum, and its positivity / `≥ 1`
  have hζ := hasSum_nonzeroIdeal_absNorm_cpow K hs'
  have hζpos : 0 < (NumberField.dedekindZeta K (s : ℂ)).re := dedekindZeta_re_pos_of_one_lt K s hs1
  -- `‖N𝔞^{-s}‖ = (N𝔞^{-s}).re` (real positive cpow), so `∑' ‖N𝔞^{-s}‖ = ζ_K(s).re`
  have hnorm_eq : ∀ 𝔞 : NonzeroIdeal K,
      ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ = ((Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))).re := by
    intro 𝔞
    have hpos : 0 < Ideal.absNorm 𝔞.1 := by
      rcases Nat.eq_zero_or_pos (Ideal.absNorm 𝔞.1) with h | h
      · exact absurd (Ideal.absNorm_eq_zero_iff.mp h) 𝔞.2
      · exact h
    have hcast : (Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ)) = (((Ideal.absNorm 𝔞.1 : ℝ) ^ (-s) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by positivity), Complex.ofReal_natCast]; norm_cast
    rw [hcast, Complex.norm_real, Complex.ofReal_re, Real.norm_of_nonneg (by positivity)]
  have hsum_norm : Summable fun 𝔞 : NonzeroIdeal K => ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ :=
    hζ.summable.norm
  have hsum_norm_eq : (∑' 𝔞 : NonzeroIdeal K, ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖)
      = (NumberField.dedekindZeta K (s : ℂ)).re := by
    rw [tsum_congr hnorm_eq, ← Complex.re_tsum hζ.summable, hζ.tsum_eq]
  -- `‖χ̃_1(𝔞) N𝔞^{-s}‖ ≤ ‖N𝔞^{-s}‖`, so the L-series is dominated termwise by `ζ_K`
  have hterm : ∀ 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
      ‖galoisCharacterOnIdeal K L 1 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ ≤
        ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ := by
    intro 𝔞
    rw [norm_mul]
    calc ‖galoisCharacterOnIdeal K L 1 𝔞.1‖ * ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖
        ≤ 1 * ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ := by
          gcongr; exact norm_galoisCharacterOnIdeal_le_one K L 1 𝔞.1
      _ = ‖(Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ := one_mul _
  -- the dominated summand is summable (`≤ ‖N𝔞^{-s}‖`)
  have hsum_term : Summable fun 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥} =>
      ‖galoisCharacterOnIdeal K L 1 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-(s : ℂ))‖ :=
    hsum_norm.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  -- `‖L_1(s)‖ ≤ ∑' ‖term‖ ≤ ∑' ‖N𝔞^{-s}‖ = ζ_K(s).re`
  have hL1_le : ‖artinDirichletSeries K L 1 (s : ℂ)‖ ≤ (NumberField.dedekindZeta K (s : ℂ)).re := by
    rw [artinDirichletSeries]
    refine (norm_tsum_le_tsum_norm hsum_term).trans ?_
    rw [← hsum_norm_eq]
    exact Summable.tsum_le_tsum hterm hsum_term hsum_norm
  -- `ζ_K(s).re ≥ 1`: the `N(⊤)^{-s} = 1` term of the nonnegative sum `∑' ‖N𝔞^{-s}‖`
  have hζ_ge1 : (1 : ℝ) ≤ (NumberField.dedekindZeta K (s : ℂ)).re := by
    rw [← hsum_norm_eq]
    refine le_trans ?_ (hsum_norm.le_tsum (⟨⊤, by simp⟩ : NonzeroIdeal K)
      (fun 𝔞 _ => norm_nonneg _))
    rw [Ideal.absNorm_top, Nat.cast_one, Complex.one_cpow, norm_one]
  -- `log ‖L_1(s)‖ ≤ log ζ_K(s).re ≤ log(1/(s-1)) + C`
  have hlog_le : Real.log ‖artinDirichletSeries K L 1 (s : ℂ)‖ ≤
      Real.log (NumberField.dedekindZeta K (s : ℂ)).re := by
    rcases eq_or_lt_of_le (norm_nonneg (artinDirichletSeries K L 1 (s : ℂ))) with h0 | h0
    · rw [← h0, Real.log_zero]
      exact Real.log_nonneg hζ_ge1
    · exact Real.log_le_log h0 hL1_le
  exact hlog_le.trans (by linarith [abs_le.mp hCs])

open Filter Topology Set in
/-- Sharifi 7.1.19 step 2 (p. 142): non-vanishing of `L(χ,1)` for
nontrivial `χ`. Source argument: if any `L(χ,1) = 0`, the
`log ζ_L = Σ_χ log L(χ,·)` decomposition leads to a sub-asymptotic
strictly weaker than the simple pole `log ζ_L ~ log(1/(s-1))`, a
contradiction. Uses `artinLSeries_analytic_extension` so that
"`L(χ, 1)` is defined" makes sense — the extension brings `s = 1` into
the analyticity domain. -/
theorem artinLSeries_one_ne_zero
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (χ : galoisCharacter K L)
    (_hχ : χ ≠ 1) :
    ∀ Lf : ℂ → ℂ,
      AnalyticOn ℂ Lf {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} →
      (∀ s : ℂ, 1 < s.re →
        Lf s = ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
          galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)) →
      Lf 1 ≠ 0 := by
  classical
  intro Lf hLf_an hLf_eq hLf0
  -- `Lf = L_χ` on `Re s > 1` (the χ-factor of `ζ_L`); it is `artinDirichletSeries K L χ`.
  have hLf_eq' : ∀ s : ℂ, 1 < s.re → Lf s = artinDirichletSeries K L χ s :=
    fun s hs => by rw [hLf_eq s hs, artinDirichletSeries]
  -- `1` is in the analyticity domain and `Lf` is analytic there.
  have hdpos : (0 : ℝ) < (Module.finrank ℚ K : ℝ)⁻¹ := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    positivity
  have hmem1 : (1 : ℂ) ∈ {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} := by
    simp only [Set.mem_setOf_eq, Complex.one_re]; linarith
  have hDopen : IsOpen {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hLf_at : AnalyticAt ℂ Lf 1 := (hDopen.analyticOn_iff_analyticOnNhd.mp hLf_an) 1 hmem1
  -- maps `s ↦ (s:ℂ)` and a "real `s` is in the domain near `1`" fact
  have hmap : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp nhdsWithin_le_nhds
  -- **Ingredient C** for `Lf`: `Lf` is not locally `0` at `1` (else it vanishes at some real
  -- `s > 1`, where `‖L_χ(s)‖ ≠ 0` because `ζ_L(s) = ∏_{χ'} L_{χ'}(s) > 0`).
  have hLf_ne : ¬ ∀ᶠ z in 𝓝 (1 : ℂ), Lf z = 0 := by
    intro hloc
    -- pick a real `s > 1` close to `1` with `Lf (s:ℂ) = 0`
    obtain ⟨s, hs0, hs1⟩ : ∃ s : ℝ, Lf (s : ℂ) = 0 ∧ 1 < s := by
      have : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), Lf (s : ℂ) = 0 := hmap.eventually hloc
      obtain ⟨s, hsz, hs1⟩ := ((this.and self_mem_nhdsWithin).exists)
      exact ⟨s, hsz, hs1⟩
    -- contradiction: `‖L_χ(s)‖ = 0`, but no factor of the positive product `ζ_L(s)` vanishes
    have hpos : 0 < (NumberField.dedekindZeta L (s : ℂ)).re :=
      dedekindZeta_re_pos_of_one_lt L s hs1
    have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs1
    have hzero : artinDirichletSeries K L χ (s : ℂ) = 0 := by rw [← hLf_eq' _ hs', hs0]
    have hprodzero : NumberField.dedekindZeta L (s : ℂ) = 0 := by
      rw [dedekindZeta_eq_prod_artinDirichletSeries K L hs', tprod_fintype,
        Finset.prod_eq_zero (Finset.mem_univ χ) hzero, zero_mul]
    rw [hprodzero, Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨Cχ, hCχ⟩ := analytic_log_norm_le_of_apply_eq_zero hLf_at hLf0 hLf_ne
  -- **Ingredient B**: `log ζ_L(s).re → +∞`.
  have hB := logDedekindZeta_re_tendsto_atTop L
  -- **Helper (i)**: the trivial-character factor `L_1` bound.
  obtain ⟨C1, hC1⟩ := log_norm_artinDirichletSeries_one_le K L
  -- **Helper (ii)** packaged per character: for every `χ'`, an eventual upper bound of the shape
  -- `log‖L_{χ'}(s)‖ ≤ (pole at χ'=1) + (zero at χ'=χ) + C χ'`.
  have hper : ∀ χ' : galoisCharacter K L, ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log ‖artinDirichletSeries K L χ' (s : ℂ)‖ ≤
        (if χ' = 1 then Real.log (1 / (s - 1)) else
          if χ' = χ then - Real.log (1 / (s - 1)) else 0) + C := by
    intro χ'
    by_cases h1 : χ' = 1
    · subst h1
      exact ⟨C1, by filter_upwards [hC1] with s hs; rw [if_pos rfl]; exact hs⟩
    · by_cases hc : χ' = χ
      · subst hc
        refine ⟨Cχ, ?_⟩
        filter_upwards [hCχ, self_mem_nhdsWithin] with s hs hs1
        simp only [mem_Ioi] at hs1
        rw [if_neg h1, if_pos rfl]
        -- `log‖L_χ(s)‖ = log‖Lf(s)‖ ≤ -log(1/(s-1)) + Cχ` (Ingredient C, since `Lf = L_χ`)
        rw [← hLf_eq' (s : ℂ) (by simpa using hs1)]
        exact hs
      · obtain ⟨C, hC⟩ := artinDirichletSeries_norm_le_of_ne_one K L χ' h1
        -- `log‖L_{χ'}(s)‖ ≤ log (max C 1) ≤ 0 + log (max C 1)`, using `max C 1 ≥ 1 > 0`.
        refine ⟨Real.log (max C 1), ?_⟩
        filter_upwards [hC] with s hs
        simp only [if_neg h1, if_neg hc, zero_add]
        have hmax1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
        rcases le_total ‖artinDirichletSeries K L χ' (s : ℂ)‖ 0 with h0 | h0
        · have hz : ‖artinDirichletSeries K L χ' (s : ℂ)‖ = 0 := le_antisymm h0 (norm_nonneg _)
          rw [hz, Real.log_zero]
          exact Real.log_nonneg hmax1
        · rcases eq_or_lt_of_le h0 with h0' | h0'
          · rw [← h0', Real.log_zero]; exact Real.log_nonneg hmax1
          · exact Real.log_le_log h0' (le_trans hs (le_max_left _ _))
  choose C hC using hper
  -- combine the finitely many eventual bounds (the character group is finite)
  have hall : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), ∀ χ' : galoisCharacter K L,
      Real.log ‖artinDirichletSeries K L χ' (s : ℂ)‖ ≤
        (if χ' = 1 then Real.log (1 / (s - 1)) else
          if χ' = χ then - Real.log (1 / (s - 1)) else 0) + C χ' :=
    Filter.eventually_all.2 hC
  -- the bounded log-sum: `log ζ_L(s).re ≤ Σ_{χ'} log‖L_{χ'}(s)‖ + C_R` (the ramified `O(1)` slack)
  obtain ⟨CR, hCR⟩ := log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded K L
  -- on this neighbourhood, `Σ_{χ'} log‖L_{χ'}(s)‖ ≤ Σ_{χ'} (ite) + Σ C χ' = ∑ C χ'`
  -- (the `χ'=1` pole and the `χ'=χ` zero cancel, as `1 ≠ χ`), hence `log ζ_L` is bounded above by
  -- `∑ C χ' + C_R` — contradicting Ingredient B (`→ +∞`).
  have hbound : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      Real.log (NumberField.dedekindZeta L (s : ℂ)).re ≤ (∑ χ', C χ') + CR := by
    filter_upwards [hall, hCR, self_mem_nhdsWithin] with s hs_all hCRs hs1
    simp only [mem_Ioi] at hs1
    have hsumle : ∑ χ' : galoisCharacter K L, Real.log ‖artinDirichletSeries K L χ' (s : ℂ)‖
        ≤ ∑ χ', C χ' := by
      calc ∑ χ' : galoisCharacter K L, Real.log ‖artinDirichletSeries K L χ' (s : ℂ)‖
          ≤ ∑ χ' : galoisCharacter K L,
              ((if χ' = 1 then Real.log (1 / (s - 1)) else
                if χ' = χ then - Real.log (1 / (s - 1)) else 0) + C χ') :=
            Finset.sum_le_sum (fun χ' _ => hs_all χ')
        _ = ∑ χ' : galoisCharacter K L, C χ' := by
            rw [Finset.sum_add_distrib]
            -- the `ite` part sums to `0`: the `χ'=1` pole `+a` and the `χ'=χ` zero `-a` cancel
            -- (they are distinct since `χ ≠ 1`).
            have hsplit : ∀ χ' : galoisCharacter K L,
                (if χ' = 1 then Real.log (1 / (s - 1)) else
                  if χ' = χ then - Real.log (1 / (s - 1)) else 0) =
                (if χ' = 1 then Real.log (1 / (s - 1)) else 0) +
                  (if χ' = χ then - Real.log (1 / (s - 1)) else 0) := by
              intro χ'
              by_cases h1 : χ' = 1
              · rw [if_pos h1, if_pos h1, if_neg (h1 ▸ (Ne.symm _hχ)), add_zero]
              · rw [if_neg h1, if_neg h1]; by_cases hc : χ' = χ <;> simp [hc]
            have hite : (∑ χ' : galoisCharacter K L,
                (if χ' = 1 then Real.log (1 / (s - 1)) else
                  if χ' = χ then - Real.log (1 / (s - 1)) else 0)) = 0 := by
              rw [Finset.sum_congr rfl (fun χ' _ => hsplit χ'), Finset.sum_add_distrib,
                Finset.sum_ite_eq' Finset.univ (1 : galoisCharacter K L),
                Finset.sum_ite_eq' Finset.univ χ]
              simp
            rw [hite, zero_add]
    -- `log ζ_L.re ≤ Σ log‖L_χ‖ + C_R ≤ (∑ C χ') + C_R`
    have := abs_le.mp hCRs
    linarith [this.1, this.2]
  -- the contradiction: a function tending to `+∞` cannot be `≤` a constant on the filter
  have hcontra := (hB.eventually_ge_atTop ((∑ χ', C χ') + CR + 1)).and hbound
  obtain ⟨s, hge, hle⟩ := hcontra.exists
  linarith

end Chebotarev
