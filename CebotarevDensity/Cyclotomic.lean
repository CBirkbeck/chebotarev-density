module

public import CebotarevDensity.ZetaProduct
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-!
# Chebotarev's theorem: cyclotomic case

For a number field `K`, an integer `m ≥ 1`, and the cyclotomic extension
`L = K(μ_m)`, the Dirichlet density of primes `𝔭` of `𝓞 K` (unramified in `L`)
whose Frobenius equals a given `σ ∈ Gal(L/K)` is `1 / |Gal(L/K)|`.

The proof is the direct generalisation of Dirichlet's theorem (Sharifi
§7.2.1; Stevenhagen–Lenstra Appendix paragraph 3). The argument:

1. By Frobenius reciprocity for cyclotomic extensions, `χ(σ_𝔭)` depends only
   on `N𝔭 mod m` for every character `χ` of `Gal(L/K)`.
2. The orthogonality relation `Σ_χ χ(σ)^{-1} χ(σ_𝔭) = |G|` if `σ_𝔭 = σ` (and
   `0` otherwise) holds character-by-character.
3. Combining the two and using `log ζ_K(s) ~ Σ_𝔭 N𝔭^{-s}`,
   `log L(χ, s)` bounded for `χ ≠ 1`, and `L(χ, 1) ≠ 0` from
   `ZetaProduct.artinLSeries_one_ne_zero`, the Dirichlet density of
   `{𝔭 : σ_𝔭 = σ}` equals `1 / |G|`.

## Main results

* `Chebotarev.chebotarev_cyclotomic` — the density of
  primes of `K` unramified in `K(μ_m)` with Frobenius equal to `σ` is
  `1 / |Gal(K(μ_m)/K)|`.

## References

* Sharifi, *Algebraic Number Theory*, §7.2.1 (`docs/algnum.pdf`, p. 142).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, Appendix
  paragraph 3 (`docs/cheb.pdf`, p. 18).
-/

@[expose] public section

noncomputable section

open NumberField Filter Topology

namespace Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-! ### Sub-lemmas for `chebotarev_cyclotomic`

Decomposed per Sharifi 7.2.1 proof (p. 142–143). Source quote
(verbatim, p. 142):

> "For a prime 𝔭 of K unramified in L, we have φ_𝔭(ζ_m) = ζ_m^{N𝔭} for a
> primitive mth root of unity ζ_m, and therefore χ(φ_𝔭) depends only on
> N𝔭 modulo m. Much as before, we have log L(χ,s) ~ Σ_𝔭 χ(𝔭) N𝔭^{-s}
> for Re(s) > 1. Given σ ∈ Gal(F(μ_m)/F) with σ(ζ_m) = ζ_m^a for some a
> prime to m, we have Σ_χ χ(σ)χ(𝔭)^{-1} = { 0 if a ≢ N𝔭 mod m, |G|
> otherwise. Now, on the one hand we have Σ_χ χ(σ)^{-1} log L(χ,s) ~ |G|
> Σ_{N𝔭≡a mod m} N𝔭^{-s}, whereas on the other we have Σ_χ χ(σ)^{-1}
> log L(χ,s) ~ log ζ_K(s) ~ log(s-1)^{-1}, since we know that L(χ,1) ≠ 0
> for all nontrivial χ."

Four sub-lemmas:
(i) Cyclotomic Frobenius formula `φ_𝔭(ζ_m) = ζ_m^{N𝔭}`.
(ii) Log-asymptotic `log L(χ,s) ~ Σ_𝔭 χ(𝔭) N𝔭^{-s}`.
(iii) Character orthogonality `Σ_χ χ(σ)χ(𝔭)^{-1} = |G|·[a ≡ N𝔭 mod m]`.
(iv) Two-sided asymptotic comparison yielding the density.
-/

/-- Sharifi 7.2.1 step (i) — cyclotomic Frobenius formula (p. 142).
Verbatim source quote: "we have φ_𝔭(ζ_m) = ζ_m^{N𝔭} for a primitive mth root of
unity ζ_m". The coprimality `hcop : (N𝔭).Coprime m` is Sharifi's implicit
hypothesis made explicit — it is genuinely necessary: if `μ_m ⊆ K` then `L = K`,
`φ_𝔭 = id`, and *every* prime is unramified, yet the formula would force
`N𝔭 ≡ 1 (mod m)`. For a nontrivial extension it is the statement that an
unramified prime does not divide `m`; mathlib currently provides that only over
`ℚ` (`IsCyclotomicExtension.Rat.*`), so over a general base `K` the caller
supplies the coprimality. -/
theorem cyclotomic_frobenius_acts_as_norm_power
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] [FiniteDimensional K L] (𝔭 : Ideal (𝓞 K))
    [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hcop : (Ideal.absNorm 𝔭).Coprime m)
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭) :
    haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
      (ne_bot_of_ramificationIdx_eq_one K L (UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓 hP))
    ∀ ζ : L, ζ ∈ primitiveRoots m L →
      arithFrobAt (𝓞 K) Gal(L/K) 𝔓 ζ = ζ ^ Ideal.absNorm 𝔭 := by
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
    (ne_bot_of_ramificationIdx_eq_one K L (UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓 hP))
  intro ζ hζmem
  set φ := arithFrobAt (𝓞 K) Gal(L/K) 𝔓
  have hζ : IsPrimitiveRoot ζ m := (mem_primitiveRoots (NeZero.pos m)).mp hζmem
  set z : 𝓞 L := hζ.toInteger
  have hzc : (algebraMap (𝓞 L) L) z = ζ := rfl
  have hzpr : IsPrimitiveRoot z m := hζ.toInteger_isPrimitiveRoot
  have hzpow : z ^ m = 1 := hzpr.pow_eq_one
  set q := Ideal.absNorm 𝔭
  have h𝔭ne : 𝔭 ≠ ⊥ := UnramifiedIn.ne_bot K L hunr
  have hcopP : (Ideal.absNorm 𝔓).Coprime m := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔓 𝔭 ‹𝔭.IsPrime› h𝔭ne]
    exact Nat.Coprime.pow_left _ hcop
  have hN1 : Ideal.absNorm 𝔓 ≠ 1 := fun h => ‹𝔓.IsPrime›.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hinj := Ideal.rootsOfUnityMapQuot_injective (I := 𝔓) m hN1 hcopP
  have hLpow : (φ • z) ^ m = 1 := by rw [← smul_pow', hzpow, smul_one]
  have hRpow : (z ^ q) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hzpow, one_pow]
  set uL := rootsOfUnity.mkOfPowEq (φ • z) hLpow
  set uR := rootsOfUnity.mkOfPowEq (z ^ q) hRpow
  have hcoeL : ((uL : (𝓞 L)ˣ) : 𝓞 L) = φ • z := rootsOfUnity.coe_mkOfPowEq _
  have hcoeR : ((uR : (𝓞 L)ˣ) : 𝓞 L) = z ^ q := rootsOfUnity.coe_mkOfPowEq _
  -- `φ • z ≡ z^q (mod 𝔓)`: the residue characterisation of `arithFrobAt` (`mk_apply`), with
  -- `q = N𝔭 = N(𝔓 ∩ 𝓞 K) = Nat.card (𝓞 K ⧸ 𝔓 ∩ 𝓞 K)`.
  have hqcard : q = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K)) := by
    show Ideal.absNorm 𝔭 = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K))
    rw [show 𝔭 = 𝔓.under (𝓞 K) from (Ideal.LiesOver.over (p := 𝔭) (P := 𝔓)),
      Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hmkeq : Ideal.Quotient.mk 𝔓 (arithFrobAt (𝓞 K) Gal(L/K) 𝔓 • z)
      = Ideal.Quotient.mk 𝔓 (z ^ q) := by
    rw [Ideal.Quotient.eq, hqcard]
    exact IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓 z
  have hmapeq : Ideal.rootsOfUnityMapQuot 𝔓 m uL = Ideal.rootsOfUnityMapQuot 𝔓 m uR := by
    apply Units.ext
    rwa [Ideal.rootsOfUnityMapQuot_apply 𝔓 m uL.2, Ideal.rootsOfUnityMapQuot_apply 𝔓 m uR.2,
      hcoeL, hcoeR]
  have hfinal : φ • z = z ^ q := by rw [← hcoeL, ← hcoeR, hinj hmapeq]
  have hmap : (algebraMap (𝓞 L) L) (φ • z) = (algebraMap (𝓞 L) L) (z ^ q) := by rw [hfinal]
  rwa [show (algebraMap (𝓞 L) L) (φ • z) = φ ζ from rfl, map_pow, hzc] at hmap

/-- Sharifi 7.2.1 step (ii) — log of an Artin L-function on the
half-plane `Re s > 1` (p. 142). Verbatim source quote: "log L(χ,s) ~
Σ_𝔭 χ(𝔭) N𝔭^{-s} for Re(s) > 1". -/
theorem log_artinLSeries_asymp_character_sum
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (χ : galoisCharacter K L) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      ‖(∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
          (χ (frobeniusClass K L 𝔭.1).out : ℂ) *
            (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)))‖
        ≤ C * Real.log (1 / (s - 1)) + C := by
  -- The value of `χ` on any conjugacy-class representative is a root of unity, hence norm `1`.
  have hnorm1 : ∀ c : ConjClasses Gal(L/K), ‖(χ c.out : ℂ)‖ = 1 := fun c => by
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite c.out)
    refine Complex.norm_eq_one_of_pow_eq_one (n := n) ?_ (by lia)
    simpa using congrArg (Units.val) (show (χ c.out) ^ n = 1 by rw [← map_pow, hpow, map_one])
  obtain ⟨C, hC⟩ := primeIdealZetaSum_le_log_plus_bounded K
  refine ⟨max C 1, ?_⟩
  -- Near `s ↓ 1`, `1/(s-1) → +∞`, so `log (1/(s-1)) ≥ 0`.
  have hlogpos : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), 0 ≤ Real.log (1 / (s - 1)) := by
    have h2 : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), s < 2 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [self_mem_nhdsWithin, h2] with s hs1 hs2
    simp only [Set.mem_Ioi] at hs1
    have hpos : (0 : ℝ) < s - 1 := sub_pos.mpr hs1
    exact Real.log_nonneg ((one_le_div₀ hpos).2 (by linarith))
  filter_upwards [hC, hlogpos, self_mem_nhdsWithin] with s hCs hlog hs1
  simp only [Set.mem_Ioi] at hs1
  -- Triangle inequality: `‖∑' χ(Frob)·N𝔭⁻ˢ‖ ≤ ∑' ‖χ(Frob)·N𝔭⁻ˢ‖ = ∑' N𝔭⁻ˢ` (real, nonneg).
  -- The summand norm `‖χ(Frob 𝔭) · N𝔭⁻ˢ‖ = N𝔭^{-s}` (since `‖χ(Frob)‖ = 1`).
  have hnormterm : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
      ‖(χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))‖ =
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := fun 𝔭 => by
    have hpos : 0 < Ideal.absNorm 𝔭.1 := by
      have hne : Ideal.absNorm 𝔭.1 ≠ 0 := fun h =>
        UnramifiedIn.ne_bot K L 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
      lia
    rw [norm_mul, hnorm1, one_mul, Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re,
      Complex.ofReal_re]
  -- Identify the bare unramified-prime tsum with `primeIdealZetaSum U s` for the unramified set `U`,
  -- via a plain-lambda injection into the `U`-prime subtype (as in `summable_prime2_absNorm_rpow`):
  -- the anonymous-constructor projection reduces by `rfl`, unlike an `Equiv` coercion, avoiding both
  -- the leftover `↑(heU 𝔭)` mismatch and the heavy `comp_injective` whnf-explosion.
  set U : Set (Ideal (𝓞 K)) := {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} with hU
  have hinj : Function.Injective
      (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} =>
        (⟨𝔭.1, ⟨𝔭.2.1, 𝔭.2.2⟩, 𝔭.2.1, UnramifiedIn.ne_bot K L 𝔭.2.2⟩ :
          {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ U ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})) :=
    fun a b hab => Subtype.ext (Subtype.mk_eq_mk.mp hab)
  -- the injection is also surjective (`U`-membership gives prime + unramified), so it reindexes the
  -- whole `U`-prime tsum.
  have hsurj : Function.Surjective
      (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} =>
        (⟨𝔭.1, ⟨𝔭.2.1, 𝔭.2.2⟩, 𝔭.2.1, UnramifiedIn.ne_bot K L 𝔭.2.2⟩ :
          {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ U ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})) :=
    fun 𝔮 => ⟨⟨𝔮.1, 𝔮.2.1.1, 𝔮.2.1.2⟩, Subtype.ext rfl⟩
  have hs0 : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} =>
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) :=
    ((summable_prime_absNorm_rpow U hs1).comp_injective hinj).congr fun 𝔭 => rfl
  have hUtsum : primeIdealZetaSum U s =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := by
    rw [primeIdealZetaSum_def]
    exact (hinj.tsum_eq (f := fun 𝔮 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ U ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
      (Ideal.absNorm 𝔮.1 : ℝ) ^ (-s))
      (by rw [hsurj.range_eq]; exact Set.subset_univ _)).symm
  have hsumnorm : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} =>
      ‖(χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))‖) :=
    hs0.congr fun 𝔭 => (hnormterm 𝔭).symm
  -- `∑' N𝔭⁻ˢ` over unramified primes = `primeIdealZetaSum U s ≤ primeIdealZetaSum univ s`.
  have hle : (∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) ≤ primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s := by
    rw [← hUtsum]
    exact primeIdealZetaSum_le_of_subset (Set.subset_univ U) hs1
  calc ‖(∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
          (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)))‖
      ≤ ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
          ‖(χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))‖ :=
        norm_tsum_le_tsum_norm hsumnorm
    _ = ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
          (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := tsum_congr hnormterm
    _ ≤ primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s := hle
    _ ≤ Real.log (1 / (s - 1)) + C := hCs
    _ ≤ max C 1 * Real.log (1 / (s - 1)) + max C 1 := by
        have h1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
        have hC' : C ≤ max C 1 := le_max_left _ _
        nlinarith [hlog]

open scoped Classical in
/-- Column orthogonality of the characters of a finite commutative group valued in `ℂˣ`:
`Σ_χ χ(g) = |G|` if `g = 1` and `0` otherwise. This is the only group-theoretic input to the
two cyclotomic orthogonality relations below; `ℂ` has enough roots of unity because it is
algebraically closed. -/
private theorem sum_galoisCharacter_eq_card_or_zero
    (G : Type*) [Group G] [IsMulCommutative G] [Finite G] [Fintype (G →* ℂˣ)] (g : G) :
    (∑ χ : G →* ℂˣ, (χ g : ℂ)) = if g = 1 then (Nat.card G : ℂ) else 0 := by
  let : CommGroup G := { mul_comm := mul_comm' }
  have : NeZero (Monoid.exponent G) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent G) := inferInstance
  by_cases hg : g = 1
  · subst hg
    rw [if_pos rfl]
    simp only [map_one, Units.val_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [← Nat.card_eq_fintype_card, CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ]
  · rw [if_neg hg]
    obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hg
    set S : ℂ := ∑ χ : G →* ℂˣ, (χ g : ℂ) with hS
    have key : (ψ g : ℂ) * S = S := by
      rw [hS, Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft ψ) fun χ : G →* ℂˣ => (χ g : ℂ)]
      refine Finset.sum_congr rfl fun χ _ => ?_
      simp only [Equiv.coe_mulLeft, MonoidHom.mul_apply, Units.val_mul]
    have hfactor : ((ψ g : ℂ) - 1) * S = 0 := by linear_combination key
    have hne : (ψ g : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr fun h => hψ (Units.val_eq_one.mp h)
    exact (mul_eq_zero.mp hfactor).resolve_left hne

/-- Sharifi 7.2.1 step (iii) — character orthogonality for the cyclotomic
case (p. 142), **matching case**: when `frobeniusClass K L 𝔭 =
ConjClasses.mk σ`, the character sum equals `|G|`. -/
theorem character_orthogonality_cyclotomic_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] [FiniteDimensional K L]
    [Fintype (galoisCharacter K L)] (σ : Gal(L/K)) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (_hunr : UnramifiedIn K L 𝔭) (_h : frobeniusClass K L 𝔭 = ConjClasses.mk σ) :
    (∑ χ : galoisCharacter K L,
        (χ σ : ℂ) * ((χ (frobeniusClass K L 𝔭).out : ℂ))⁻¹)
      = (Nat.card Gal(L/K) : ℂ) := by
  have : IsMulCommutative Gal(L/K) := IsCyclotomicExtension.isMulCommutative (S := {m}) K L
  set τ := (frobeniusClass K L 𝔭).out
  have hsummand : ∀ χ : galoisCharacter K L,
      (χ σ : ℂ) * ((χ τ : ℂ))⁻¹ = (χ (σ * τ⁻¹) : ℂ) := fun χ => by
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  have hmk : ConjClasses.mk τ = frobeniusClass K L 𝔭 := Quotient.out_eq _
  have heq : σ * τ⁻¹ = 1 := by
    obtain ⟨c, hc⟩ : IsConj τ σ :=
      ConjClasses.mk_eq_mk_iff_isConj.mp (hmk.trans _h)
    rw [SemiconjBy, mul_comm' (c : Gal(L/K))] at hc
    rw [mul_right_cancel hc, mul_inv_cancel]
  simp_rw [hsummand]
  rw [sum_galoisCharacter_eq_card_or_zero Gal(L/K) (σ * τ⁻¹), if_pos heq]

/-- Sharifi 7.2.1 character orthogonality, **non-matching case**:
when `frobeniusClass K L 𝔭 ≠ ConjClasses.mk σ`, the character sum
vanishes. -/
theorem character_orthogonality_cyclotomic_ne
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] [FiniteDimensional K L]
    [Fintype (galoisCharacter K L)] (σ : Gal(L/K)) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (_hunr : UnramifiedIn K L 𝔭) (_h : frobeniusClass K L 𝔭 ≠ ConjClasses.mk σ) :
    (∑ χ : galoisCharacter K L,
        (χ σ : ℂ) * ((χ (frobeniusClass K L 𝔭).out : ℂ))⁻¹) = 0 := by
  have : IsMulCommutative Gal(L/K) := IsCyclotomicExtension.isMulCommutative (S := {m}) K L
  set τ := (frobeniusClass K L 𝔭).out
  have hsummand : ∀ χ : galoisCharacter K L,
      (χ σ : ℂ) * ((χ τ : ℂ))⁻¹ = (χ (σ * τ⁻¹) : ℂ) := fun χ => by
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  have hmk : ConjClasses.mk τ = frobeniusClass K L 𝔭 := Quotient.out_eq _
  have hne : σ * τ⁻¹ ≠ 1 := fun hσ =>
    _h <| hmk.symm.trans (congrArg ConjClasses.mk (mul_inv_eq_one.mp hσ)).symm
  simp_rw [hsummand]
  rw [sum_galoisCharacter_eq_card_or_zero Gal(L/K) (σ * τ⁻¹), if_neg hne]

/-- **Complex-analytic bridge of Dirichlet's argument (the substantive content of the cyclotomic
case).** Given the analytic extension `Lf` of `L(χ,·)` — analytic on `Z(1-[K:ℚ]⁻¹)` and agreeing
with the ideal Dirichlet series on `Re s > 1` (the `artinLSeries_analytic_extension` / LF4 leaf) —
which is nonzero at `s = 1` (`artinLSeries_one_ne_zero` / LF5), the twisted prime sum
`Σ_𝔭 χ(Frob 𝔭) N𝔭⁻ˢ` stays bounded as `s ↓ 1`.

Proof (pure complex analysis; see decomposition.md "χ≠1 chain"): write `P_χ(s) = g_χ(s) - R_χ(s)`
with `g_χ(s) = Σ_𝔭 -Log(1 - χ(Frob 𝔭) N𝔭⁻ˢ)` and `R_χ` the prime-power tail
(`‖R_χ‖ ≤ Σ_𝔭 N𝔭⁻² < ∞`, uniformly on `Re s ≥ 1`). By the Euler product
(`exists_artinLSeries_eulerProduct_abelian`) and `Complex.cexp_tsum_eq_tprod`, `exp(g_χ(s)) = Lf(s)`
on `Re s > 1`, so `g_χ' = logDeriv Lf = Lf'/Lf`, continuous at `1` (`Lf` analytic, `Lf 1 ≠ 0`) hence
bounded near `1`; the mean value inequality (`Convex.norm_image_sub_le_of_norm_deriv_le`) then
bounds `g_χ`. The derivative is single-valued, sidestepping the branch/monodromy of `log Lf`. -/
private theorem artinLSeries_prime_sum_bounded_of_analytic_extension
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (χ : galoisCharacter K L)
    (hχ : χ ≠ 1) (Lf : ℂ → ℂ)
    (hLf_an : AnalyticOn ℂ Lf {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re})
    (hLf_eq : ∀ s : ℂ, 1 < s.re →
      Lf s = ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
        galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s))
    (hLf0 : Lf 1 ≠ 0) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      ‖∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
          (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))‖ ≤ C := by
  sorry

/-- **Analytic input of the cyclotomic case (Dirichlet's argument).** For a nontrivial abelian
character `χ`, the twisted prime sum `Σ_𝔭 χ(Frob 𝔭) N𝔭⁻ˢ` stays bounded as `s ↓ 1`. Now discharged
modulo the complex-analytic bridge: produce the analytic extension `Lf` (LF4
`artinLSeries_analytic_extension`, itself ⟸ the geometry-of-numbers leaf
`character_sum_geometry_of_numbers_bound`), note `Lf 1 ≠ 0` (LF5 `artinLSeries_one_ne_zero`), and
feed both to `artinLSeries_prime_sum_bounded_of_analytic_extension`. So this gap is **downstream of
the same geometry-of-numbers leaf** as LF4/LF5; its only extra content is the bridge. -/
private theorem artinLSeries_prime_sum_bounded_of_ne_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (χ : galoisCharacter K L)
    (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      ‖∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
          (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))‖ ≤ C := by
  obtain ⟨Lf, hLf_an, hLf_eq⟩ := artinLSeries_analytic_extension K L χ hχ
  exact artinLSeries_prime_sum_bounded_of_analytic_extension K L χ hχ Lf hLf_an hLf_eq
    (artinLSeries_one_ne_zero K L χ hχ Lf hLf_an hLf_eq)

/-! ### Assembly helpers for `primeIdealZetaSum_frobeniusFibre_asymp`

The orthogonality collapse runs the character sum `∑_χ (χ σ)⁻¹ · (∑'_𝔭 χ(Frob 𝔭) N𝔭⁻ˢ)` two ways:

* interchanging the finite `∑_χ` with the prime `∑'_𝔭` and collapsing the inner character sum by
  orthogonality gives `|G| · P_σ(s)` (the fibre prime sum, real and nonnegative);
* splitting `∑_χ` into the trivial character `χ = 1` (contributing `∑'_𝔭 N𝔭⁻ˢ` over unramified
  primes, asymptotic to `log(1/(s-1))`) and the nontrivial characters (each bounded by
  `artinLSeries_prime_sum_bounded_of_ne_one`).

Comparing the two yields `|G| · P_σ(s) = log(1/(s-1)) + O(1)`, hence `P_σ(s)/log → 1/|G|`. -/

/-- The twisted prime sum `∑'_𝔭 χ(Frob 𝔭) N𝔭⁻ˢ` over the unramified primes, as a complex function of
`s`. The `χ = 1` value is the real prime sum `∑'_𝔭 N𝔭⁻ˢ`; the `χ ≠ 1` values are bounded near
`s = 1`. -/
private noncomputable def twistedPrimeSum
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (s : ℝ) : ℂ :=
  ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
    (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))

/-- Each summand of `twistedPrimeSum` has norm `N𝔭⁻ˢ` (since `‖χ(Frob)‖ = 1`), so the family is
summable: it is dominated by the summable real prime sum `Σ_𝔭 N𝔭^{-s}` (for `1 < s`). -/
private theorem summable_twistedPrimeSum
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (χ : galoisCharacter K L) {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
      (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))) := by
  set U : Set (Ideal (𝓞 K)) := {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} with hU
  have hinj : Function.Injective
      (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} =>
        (⟨𝔭.1, ⟨𝔭.2.1, 𝔭.2.2⟩, 𝔭.2.1, UnramifiedIn.ne_bot K L 𝔭.2.2⟩ :
          {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ U ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})) :=
    fun a b hab => Subtype.ext (Subtype.mk_eq_mk.mp hab)
  have hs0 : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} =>
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) :=
    ((summable_prime_absNorm_rpow U hs).comp_injective hinj).congr fun 𝔭 => rfl
  have hnorm1 : ∀ c : ConjClasses Gal(L/K), ‖(χ c.out : ℂ)‖ = 1 := fun c => by
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite c.out)
    refine Complex.norm_eq_one_of_pow_eq_one (n := n) ?_ (by lia)
    simpa using congrArg (Units.val) (show (χ c.out) ^ n = 1 by rw [← map_pow, hpow, map_one])
  have hnormterm : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
      ‖(χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))‖ =
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := fun 𝔭 => by
    have hpos : 0 < Ideal.absNorm 𝔭.1 := by
      have hne : Ideal.absNorm 𝔭.1 ≠ 0 := fun h =>
        UnramifiedIn.ne_bot K L 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
      lia
    rw [norm_mul, hnorm1, one_mul, Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re,
      Complex.ofReal_re]
  exact Summable.of_norm (hs0.congr fun 𝔭 => (hnormterm 𝔭).symm)

/-- The character-twist orthogonality collapse, matching case. When `frobeniusClass K L 𝔭 =
ConjClasses.mk σ`, the inner sum `∑_χ (χ σ)⁻¹ · χ(Frob 𝔭)` equals `|G|`. Reindexes the proven
`character_orthogonality_cyclotomic_eq` along `χ ↦ χ⁻¹`. -/
private theorem sum_charTwist_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] [FiniteDimensional K L]
    [Fintype (galoisCharacter K L)] (σ : Gal(L/K)) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (hunr : UnramifiedIn K L 𝔭) (h : frobeniusClass K L 𝔭 = ConjClasses.mk σ) :
    (∑ χ : galoisCharacter K L,
        ((χ σ : ℂ))⁻¹ * (χ (frobeniusClass K L 𝔭).out : ℂ)) = (Nat.card Gal(L/K) : ℂ) := by
  rw [← character_orthogonality_cyclotomic_eq K L m σ 𝔭 hunr h,
    ← Equiv.sum_comp (Equiv.inv (galoisCharacter K L))
      fun χ : galoisCharacter K L => (χ σ : ℂ) * ((χ (frobeniusClass K L 𝔭).out : ℂ))⁻¹]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Equiv.inv_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    Units.val_inv_eq_inv_val, inv_inv, mul_comm]

/-- The character-twist orthogonality collapse, non-matching case. When `frobeniusClass K L 𝔭 ≠
ConjClasses.mk σ`, the inner sum `∑_χ (χ σ)⁻¹ · χ(Frob 𝔭)` vanishes. Reindexes the proven
`character_orthogonality_cyclotomic_ne` along `χ ↦ χ⁻¹`. -/
private theorem sum_charTwist_ne
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] [FiniteDimensional K L]
    [Fintype (galoisCharacter K L)] (σ : Gal(L/K)) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (hunr : UnramifiedIn K L 𝔭) (h : frobeniusClass K L 𝔭 ≠ ConjClasses.mk σ) :
    (∑ χ : galoisCharacter K L,
        ((χ σ : ℂ))⁻¹ * (χ (frobeniusClass K L 𝔭).out : ℂ)) = 0 := by
  rw [← character_orthogonality_cyclotomic_ne K L m σ 𝔭 hunr h,
    ← Equiv.sum_comp (Equiv.inv (galoisCharacter K L))
      fun χ : galoisCharacter K L => (χ σ : ℂ) * ((χ (frobeniusClass K L 𝔭).out : ℂ))⁻¹]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Equiv.inv_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    Units.val_inv_eq_inv_val, inv_inv, mul_comm]

/-- The bare prime sum over the unramified primes is asymptotic to `log(1/(s-1))`: it differs from
the universal prime sum (`primeIdealZetaSum_univ_tendsto_log`) by the finitely-many ramified primes
(`finite_ramifiedIn`), whose contribution is bounded and so negligible against `log → ∞`. -/
private theorem primeIdealZetaSum_unramified_div_log_tendsto_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] :
    Tendsto
      (fun s : ℝ ↦
        primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s
          / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 1) := by
  set U : Set (Ideal (𝓞 K)) := {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} with hU
  set R : Set (Ideal (𝓞 K)) := {𝔭 | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭} with hR
  -- `U` and `R` are disjoint and together exhaust the nonzero primes.
  have hdisj : Disjoint U R :=
    Set.disjoint_left.mpr fun 𝔭 hu hr => hr.2.2 hu.2
  have hcover : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭 ∈ U ∪ R := fun 𝔭 hp hne => by
    by_cases hunr : UnramifiedIn K L 𝔭
    · exact Or.inl ⟨hp, hunr⟩
    · exact Or.inr ⟨hp, hne, hunr⟩
  have hRfin : R.Finite := finite_ramifiedIn K L
  -- The ramified contribution is bounded by the number of ramified primes.
  obtain ⟨CR, hCR⟩ : ∃ CR : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), primeIdealZetaSum R s ≤ CR := by
    refine ⟨Nat.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ R ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_Ioi] at hs
    exact primeIdealZetaSum_le_card_of_finite K hRfin (by linarith)
  -- `R s / log → 0` (bounded numerator, `log → ∞`).
  have hRzero : Tendsto (fun s : ℝ ↦ primeIdealZetaSum R s / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 0) := by
    have hL := tendsto_log_one_div_sub_one_atTop
    refine squeeze_zero_norm' ?_ (Filter.Tendsto.div_atTop tendsto_const_nhds hL (a := CR))
    filter_upwards [hCR, hL.eventually_gt_atTop 0] with s hub hLpos
    have hRnn : 0 ≤ primeIdealZetaSum R s := by
      rw [primeIdealZetaSum_def]; exact tsum_nonneg fun _ => Real.rpow_nonneg (by positivity) _
    rw [Real.norm_of_nonneg (div_nonneg hRnn hLpos.le)]
    gcongr -- `R s / log ≤ CR / log`
  -- `U s / log = univ s / log − R s / log → 1 − 0 = 1`.
  have hcomb : Tendsto (fun s : ℝ ↦
      primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s / Real.log (1 / (s - 1))
        - primeIdealZetaSum R s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 1) := by
    simpa using (primeIdealZetaSum_univ_tendsto_log K).sub hRzero
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  have hadd : primeIdealZetaSum U s + primeIdealZetaSum R s =
      primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s := by
    rw [← primeIdealZetaSum_union_of_disjoint hdisj hs,
      primeIdealZetaSum_eq_univ_of_forall_prime_mem hcover s]
  rw [← sub_div, ← hadd, add_sub_cancel_right]

/-- The orthogonality-collapsed master identity (real form). Summing the twisted prime sums against
`(χ σ)⁻¹` over all characters and collapsing the inner character sum by orthogonality
(`sum_charTwist_eq`/`_ne`) gives `|G| · P_σ(s)`; splitting off the trivial character `χ = 1` (whose
twisted sum is the bare unramified prime sum `primeIdealZetaSum U s`) leaves a remainder bounded by
the `χ ≠ 1` Artin sums. This packages both sides into the single real equation
`|G| · P_σ(s) = primeIdealZetaSum U s + (remainder).re`. -/
private theorem card_mul_frobeniusFibre_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] [FiniteDimensional K L]
    [Fintype (galoisCharacter K L)] [DecidableEq (galoisCharacter K L)] (σ : Gal(L/K))
    {s : ℝ} (hs : 1 < s) :
    (Nat.card Gal(L/K) : ℝ) *
        primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
          frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
      = primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s
        + (∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L),
            ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s).re := by
  classical
  haveI : IsMulCommutative Gal(L/K) := IsCyclotomicExtension.isMulCommutative (S := {m}) K L
  set U : Set (Ideal (𝓞 K)) := {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} with hU
  set Sσ : Set (Ideal (𝓞 K)) := {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
    frobeniusClass K L 𝔭 = ConjClasses.mk σ} with hSσ
  -- `N𝔭⁻ˢ` over the unramified prime subtype, as a complex cast.
  have hfreal : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
      (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)) = ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) : ℝ) := fun 𝔭 => by
    rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow (by positivity), Complex.ofReal_natCast]
  -- INTERCHANGE: `∑_χ (χσ)⁻¹ ∑'_𝔭 χ(Frob) N𝔭⁻ˢ = ∑'_𝔭 (∑_χ (χσ)⁻¹ χ(Frob)) N𝔭⁻ˢ`.
  have hinterchange : (∑ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s)
      = ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
          (∑ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * (χ (frobeniusClass K L 𝔭.1).out : ℂ))
            * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)) := by
    have hstep : ∀ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s
        = ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
            ((χ σ : ℂ))⁻¹ * (χ (frobeniusClass K L 𝔭.1).out : ℂ)
              * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)) := fun χ => by
      rw [twistedPrimeSum, ← tsum_mul_left]
      exact tsum_congr fun 𝔭 => by ring
    rw [Finset.sum_congr rfl fun χ _ => hstep χ,
      ← Summable.tsum_finsetSum (fun χ _ =>
        ((summable_twistedPrimeSum K L χ hs).mul_left ((χ σ : ℂ))⁻¹).congr fun 𝔭 => by ring)]
    exact tsum_congr fun 𝔭 => (Finset.sum_mul _ _ _).symm
  -- COLLAPSE: the inner character sum is `N` on the fibre `Sσ`, else `0`.
  have hcollapse : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
      (∑ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * (χ (frobeniusClass K L 𝔭.1).out : ℂ))
          * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))
        = if frobeniusClass K L 𝔭.1 = ConjClasses.mk σ then
            (Nat.card Gal(L/K) : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)) else 0 := fun 𝔭 => by
    haveI := 𝔭.2.1
    by_cases h : frobeniusClass K L 𝔭.1 = ConjClasses.mk σ
    · rw [sum_charTwist_eq K L m σ 𝔭.1 𝔭.2.2 h, if_pos h]
    · rw [sum_charTwist_ne K L m σ 𝔭.1 𝔭.2.2 h, if_neg h, zero_mul]
  -- FIBRE TSUM (real): `P_σ s = ∑'_𝔭 (if frob=mkσ then N𝔭⁻ˢ else 0)` over the unramified subtype.
  -- plain-lambda injection (anonymous-constructor projections reduce by `rfl`).
  have hfinj : Function.Injective
      (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ Sσ ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
        (⟨𝔭.1, 𝔭.2.1.1, 𝔭.2.1.2.1⟩ : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭})) :=
    fun a b hab => Subtype.ext (Subtype.mk_eq_mk.mp hab)
  have hfibre : primeIdealZetaSum Sσ s =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
        (if frobeniusClass K L 𝔭.1 = ConjClasses.mk σ then (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) else 0) :=
    by
    rw [primeIdealZetaSum_def, ← hfinj.tsum_eq
      (f := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} =>
        if frobeniusClass K L 𝔭.1 = ConjClasses.mk σ then (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) else 0)
      ?_]
    · exact tsum_congr fun 𝔭 => (if_pos 𝔭.2.1.2.2).symm
    · rintro 𝔭 h𝔭
      have h : frobeniusClass K L 𝔭.1 = ConjClasses.mk σ := by
        by_contra hne; exact h𝔭 (if_neg hne)
      exact ⟨⟨𝔭.1, ⟨𝔭.2.1, 𝔭.2.2, h⟩, 𝔭.2.1, UnramifiedIn.ne_bot K L 𝔭.2.2⟩, rfl⟩
  -- `M s = N · (P_σ s : ℂ)` (computation a).
  have hMa : (∑ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s)
      = (Nat.card Gal(L/K) : ℂ) * (primeIdealZetaSum Sσ s : ℂ) := by
    rw [hinterchange, tsum_congr hcollapse, hfibre, Complex.ofReal_tsum, ← tsum_mul_left]
    refine tsum_congr fun 𝔭 => ?_
    rw [apply_ite (Complex.ofReal), mul_ite, Complex.ofReal_zero, mul_zero, hfreal 𝔭]
  -- `M s = (U-sum : ℂ) + remainder` (computation b): split off the trivial character.
  have h1inj : Function.Injective
      (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ U ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
        (⟨𝔭.1, 𝔭.2.1.1, 𝔭.2.1.2⟩ : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭})) :=
    fun a b hab => Subtype.ext (Subtype.mk_eq_mk.mp hab)
  have h1surj : Function.Surjective
      (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ U ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
        (⟨𝔭.1, 𝔭.2.1.1, 𝔭.2.1.2⟩ : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭})) :=
    fun 𝔭 => ⟨⟨𝔭.1, ⟨𝔭.2.1, 𝔭.2.2⟩, 𝔭.2.1, UnramifiedIn.ne_bot K L 𝔭.2.2⟩, rfl⟩
  have h1term : ((1 : galoisCharacter K L) σ : ℂ)⁻¹ * twistedPrimeSum K L 1 s
      = (primeIdealZetaSum U s : ℂ) := by
    rw [show ((1 : galoisCharacter K L) σ : ℂ) = 1 by simp, inv_one, one_mul, twistedPrimeSum,
      primeIdealZetaSum_def, Complex.ofReal_tsum,
      ← h1inj.tsum_eq (f := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} =>
        ((1 : galoisCharacter K L) (frobeniusClass K L 𝔭.1).out : ℂ)
          * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)))
        (by rw [h1surj.range_eq]; exact Set.subset_univ _)]
    refine tsum_congr fun 𝔭 => ?_
    rw [show ((1 : galoisCharacter K L) (frobeniusClass K L 𝔭.1).out : ℂ) = 1 by simp, one_mul,
      hfreal ⟨𝔭.1, 𝔭.2.1.1, 𝔭.2.1.2⟩]
  have hMb : (∑ χ : galoisCharacter K L, ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s)
      = (primeIdealZetaSum U s : ℂ)
        + ∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L),
            ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s := by
    rw [← h1term, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : galoisCharacter K L))]
  -- take real parts: `U-sum` and `N · P_σ` are real, so the real equation falls out.
  have heq : (Nat.card Gal(L/K) : ℂ) * (primeIdealZetaSum Sσ s : ℂ) = (primeIdealZetaSum U s : ℂ)
      + ∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L),
          ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s := hMa.symm.trans hMb
  have := congrArg Complex.re heq
  simpa [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im] using this

/-- Sharifi 7.2.1 step (iv-a) — the numerator asymptotic. The prime-sum
over the Frobenius fibre `{σ_𝔭 = σ}` is asymptotic to
`(1/|G|) log(1/(s-1))` as `s ↓ 1`. This packages the orthogonality
relations (`character_orthogonality_cyclotomic_eq`/`_ne`) summed against
the log-asymptotic of the Artin L-functions
(`log_artinLSeries_asymp_character_sum`) with the simple pole of `ζ_K`
(only `χ = 1` contributes a pole, by `artinLSeries_one_ne_zero`):
`Σ_χ χ(σ)⁻¹ log L(χ,s) ~ |G| Σ_{σ_𝔭=σ} N𝔭^{-s}` on one side and
`~ log ζ_K(s) ~ log(1/(s-1))` on the other. -/
theorem primeIdealZetaSum_frobeniusFibre_asymp
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] [FiniteDimensional K L] (σ : Gal(L/K)) :
    Tendsto
      (fun s : ℝ ↦
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 ((Nat.card Gal(L/K) : ℝ)⁻¹)) := by
  classical
  haveI : Fintype (galoisCharacter K L) := Fintype.ofFinite _
  haveI : IsMulCommutative Gal(L/K) := IsCyclotomicExtension.isMulCommutative (S := {m}) K L
  set N : ℕ := Nat.card Gal(L/K) with hN
  have hNpos : 0 < N := Nat.card_pos
  -- the `χ ≠ 1` remainder and its boundedness near `s = 1`.
  set B : ℝ → ℂ := fun s => ∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L),
    ((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s with hB
  -- each `‖(χσ)⁻¹ · twistedPrimeSum χ s‖ ≤ Cχ` (norm-1 coefficient × bounded Artin sum).
  have hterm : ∀ χ : galoisCharacter K L, χ ≠ 1 → ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      ‖((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s‖ ≤ C := fun χ hχ => by
    obtain ⟨C, hC⟩ := artinLSeries_prime_sum_bounded_of_ne_one K L χ hχ
    refine ⟨C, ?_⟩
    filter_upwards [hC] with s hs
    have hnorm1 : ‖((χ σ : ℂ))⁻¹‖ = 1 := by
      rw [norm_inv]
      obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite σ)
      rw [Complex.norm_eq_one_of_pow_eq_one (n := n)
        (by simpa using congrArg Units.val (show (χ σ) ^ n = 1 by rw [← map_pow, hpow, map_one]))
        (by lia), inv_one]
    rw [norm_mul, hnorm1, one_mul]
    exact hs
  -- total bounding function (junk `0` off the `χ ≠ 1` set).
  have hCfun : ∀ χ : galoisCharacter K L, ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      χ ∈ Finset.univ.erase (1 : galoisCharacter K L) →
        ‖((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s‖ ≤ C := fun χ => by
    by_cases hχ : χ = 1
    · refine ⟨0, ?_⟩
      filter_upwards with s hmem
      exact absurd (Finset.mem_erase.mp hmem).1 (not_not.mpr hχ)
    · obtain ⟨C, hC⟩ := hterm χ hχ
      refine ⟨C, ?_⟩
      filter_upwards [hC] with s hs _
      exact hs
  choose C hC using hCfun
  obtain ⟨CB, hCB⟩ : ∃ CB : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖B s‖ ≤ CB := by
    refine ⟨∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L), C χ, ?_⟩
    have hall : ∀ᶠ s in 𝓝[>] (1 : ℝ), ∀ χ ∈ Finset.univ.erase (1 : galoisCharacter K L),
        ‖((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s‖ ≤ C χ :=
      (eventually_all_finset _).mpr fun χ hmem => (hC χ).mono fun s hs => hs hmem
    filter_upwards [hall] with s hs
    calc ‖B s‖ ≤ ∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L),
          ‖((χ σ : ℂ))⁻¹ * twistedPrimeSum K L χ s‖ := norm_sum_le _ _
      _ ≤ ∑ χ ∈ Finset.univ.erase (1 : galoisCharacter K L), C χ :=
        Finset.sum_le_sum fun χ hχ => hs χ hχ
  -- `B(·).re / log → 0` (bounded numerator, `log → ∞`).
  have hBlog : Tendsto (fun s : ℝ ↦ (B s).re / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 0) := by
    have hL := tendsto_log_one_div_sub_one_atTop
    refine squeeze_zero_norm' ?_ (Filter.Tendsto.div_atTop tendsto_const_nhds hL (a := CB))
    filter_upwards [hCB, hL.eventually_gt_atTop 0] with s hub hLpos
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hLpos]
    gcongr
    exact (RCLike.abs_re_le_norm (B s)).trans hub
  -- COMBINE: `P_σ/log = (1/N)·(U/log + B.re/log) → (1/N)·(1 + 0) = (N:ℝ)⁻¹`.
  have hlim : Tendsto (fun s : ℝ ↦ (N : ℝ)⁻¹ *
      (primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s
          / Real.log (1 / (s - 1))
        + (B s).re / Real.log (1 / (s - 1)))) (𝓝[>] 1) (𝓝 ((N : ℝ)⁻¹)) := by
    have := ((primeIdealZetaSum_unramified_div_log_tendsto_one K L).add hBlog).const_mul (N : ℝ)⁻¹
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  have hmaster : (N : ℝ) *
      primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
      = primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s + (B s).re := by
    rw [hN]; exact card_mul_frobeniusFibre_eq K L m σ hs
  rw [← add_div, ← hmaster, mul_div_assoc, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hNpos.ne'), one_mul]

/-- Pure real-analysis glue: if `num(s) / log(1/(s-1)) → c` and
`den(s) / log(1/(s-1)) → 1` as `s ↓ 1`, then `num(s) / den(s) → c`. -/
theorem tendsto_ratio_of_log_asymp_numerator
    (num den : ℝ → ℝ) (c : ℝ)
    (hnum : Tendsto (fun s : ℝ ↦ num s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 c))
    (hden : Tendsto (fun s : ℝ ↦ den s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 1)) :
    Tendsto (fun s : ℝ ↦ num s / den s) (𝓝[>] 1) (𝓝 c) := by
  have hL : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), Real.log (1 / (s - 1)) ≠ 0 := by
    have h2 : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), s < 2 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [self_mem_nhdsWithin, h2] with s hs1 hs2
    have hpos : (0 : ℝ) < s - 1 := sub_pos.mpr hs1
    exact (Real.log_pos ((one_lt_div₀ hpos).2 (by linarith))).ne'
  exact (div_one c ▸ hnum.div hden one_ne_zero).congr'
    (hL.mono fun s hs ↦ div_div_div_cancel_right₀ hs (num s) (den s))

/-- Sharifi 7.2.1 step (iv) — two-sided log-asymptotic comparison (p. 142).
Source: "on the one hand we have Σ_χ χ(σ)^{-1} log L(χ,s) ~ |G|
Σ_{φ_𝔭=σ} N𝔭^{-s}, whereas on the other we have Σ_χ χ(σ)^{-1} log L(χ,s)
~ log ζ_K(s) ~ log(s-1)^{-1}". Comparing yields density `1/|G|`. -/
theorem cyclotomic_density_from_two_sided_asymp
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] [FiniteDimensional K L] (σ : Gal(L/K)) :
    Tendsto
      (fun s : ℝ ↦
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
      (𝓝[>] 1) (𝓝 ((Nat.card Gal(L/K) : ℝ)⁻¹)) :=
  tendsto_ratio_of_log_asymp_numerator _ _ _
    (primeIdealZetaSum_frobeniusFibre_asymp K L m σ)
    (primeIdealZetaSum_univ_tendsto_log K)

/-- **Chebotarev's theorem, cyclotomic case** (Sharifi §7.2.1).

For `K` a number field, `m ≥ 1`, and `L = K(μ_m)` the `m`-th cyclotomic
extension of `K`, every `σ ∈ Gal(L/K)` is the Frobenius of a set of primes
of `𝓞 K` (unramified in `L`) of Dirichlet density `1 / |Gal(L/K)|`. -/
theorem chebotarev_cyclotomic
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] [FiniteDimensional K L] (σ : Gal(L/K)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card Gal(L/K) : ℝ)⁻¹) :=
  cyclotomic_density_from_two_sided_asymp K L m σ

/-- A variant of the cyclotomic-case theorem stated as a lower-density
inequality. Used in the abelian case to feed into the
`HasLowerDirichletDensity.mono` chain. -/
theorem chebotarev_cyclotomic_lowerDensity_ge
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] [FiniteDimensional K L] (σ : Gal(L/K)) :
    HasLowerDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card Gal(L/K) : ℝ)⁻¹) :=
  (chebotarev_cyclotomic K L m σ).hasLower

end Chebotarev
