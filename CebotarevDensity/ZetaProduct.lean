module

public import CebotarevDensity.Frobenius
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

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

* `Chebotarev.exists_dedekindZeta_factorisation` —
  for an abelian extension `L/K`, there exist holomorphic functions
  `L_χ : ℂ → ℂ` indexed by characters of `Gal(L/K)` such that
  `ζ_L = ∏_χ L_χ` on `Re s > 1`, `L_1 = ζ_K`, and `L_χ(1) ≠ 0` for
  `χ ≠ 1` (Sharifi 7.1.16 + 7.1.19).
* `Chebotarev.exists_chebotarev_cyclotomic_residue_identity` —
  the orthogonality-of-characters identity that the cyclotomic case of
  Chebotarev hinges on (Sharifi 7.2.1).

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

/-- Sharifi 7.1.19 step 1 (p. 142): geometry-of-numbers bound. The
partial-sum character sum `Σ_{N𝔞≤N} χ(𝔞)` (with `χ(𝔞) = galoisCharacterOnIdeal K L χ 𝔞` the
completely-multiplicative ideal character) is `O(N^{1-1/[K:ℚ]})` for a
nontrivial character `χ`. This is the convergence input that extends
`L(χ,·)` to `Z(1 - [K:ℚ]^{-1})`. -/
theorem character_sum_geometry_of_numbers_bound
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (χ : galoisCharacter K L)
    (_hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ N : ℕ,
      ‖∑' 𝔞 : {𝔞 : Ideal (𝓞 K) //
                𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N},
        galoisCharacterOnIdeal K L χ 𝔞.1‖
        ≤ C * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
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
  sorry

/-- **Zeta factorisation for an abelian extension** (Sharifi 7.1.16 + 7.1.19).

For an abelian Galois extension `L/K` of number fields, there is a family
of functions `L_χ : ℂ → ℂ` indexed by the characters of `Gal(L/K)`, each
analytic on `Re s ≥ 1` (with `L_1` having a simple pole at `s = 1` matching
`ζ_K`), such that:

* `ζ_L(s) = ∏_χ L_χ(s)` for `Re s > 1`,
* `L_1(s) = ζ_K(s)` (the trivial-character L-function is the Dedekind zeta
  of `K`),
* `L_χ(1) ≠ 0` for every nontrivial `χ`.

The `L_χ` are the Artin / Hecke L-series of the abelian extension. -/
theorem exists_dedekindZeta_factorisation
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] :
    ∃ Lf : galoisCharacter K L → ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re → dedekindZeta L s = ∏' χ : galoisCharacter K L, Lf χ s) ∧
      (∀ s : ℂ, Lf 1 s = dedekindZeta K s) ∧
      (∀ χ : galoisCharacter K L, χ ≠ 1 → Lf χ 1 ≠ 0) := by
  sorry

/-- **Cyclotomic-case orthogonality identity** (Sharifi 7.2.1 step).

For an abelian extension `L/K` with `L = K(μ_m)`, the family `Lf` from
`exists_dedekindZeta_factorisation` satisfies the asymptotic
`Σ_χ χ(σ)⁻¹ log L_χ(s) ∼ |G| · Σ_{𝔭 : σ_𝔭 = σ} N𝔭^{-s}` as `s ↓ 1`. This is
the orthogonality identity that lets one extract the density of primes
with a given Frobenius. -/
theorem exists_chebotarev_cyclotomic_residue_identity
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) :
    ∃ c : ℝ,
      Filter.Tendsto
        (fun s : ℝ ↦
          primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
            - (Nat.card Gal(L/K) : ℝ)⁻¹ * Real.log (1 / (s - 1)))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds c) := by
  sorry

end Chebotarev
