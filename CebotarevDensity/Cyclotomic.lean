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
    ∀ ζ : L, ζ ∈ primitiveRoots m L →
      frobeniusAt K L 𝔓 (UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓 hP) ζ
        = ζ ^ Ideal.absNorm 𝔭 := by
  intro ζ hζmem
  set hram := UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓 hP with hram_def
  set φ := frobeniusAt K L 𝔓 hram with hφ_def
  have hζ : IsPrimitiveRoot ζ m := (mem_primitiveRoots (NeZero.pos m)).mp hζmem
  set z : 𝓞 L := hζ.toInteger with hz_def
  have hzc : (algebraMap (𝓞 L) L) z = ζ := rfl
  have hzpr : IsPrimitiveRoot z m := hζ.toInteger_isPrimitiveRoot
  have hzpow : z ^ m = 1 := hzpr.pow_eq_one
  have hunder : 𝔓.under (𝓞 K) = 𝔭 := (Ideal.LiesOver.over (p := 𝔭) (P := 𝔓)).symm
  set q := Ideal.absNorm 𝔭 with hq_def
  have hspec := (frobeniusAt_spec K L 𝔓 hram).2 z
  rw [hunder] at hspec
  have h𝔭ne : 𝔭 ≠ ⊥ := UnramifiedIn.ne_bot K L hunr
  have hcopP : (Ideal.absNorm 𝔓).Coprime m := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔓 𝔭 ‹𝔭.IsPrime› h𝔭ne]
    exact Nat.Coprime.pow_left _ hcop
  have hN1 : Ideal.absNorm 𝔓 ≠ 1 := fun h => ‹𝔓.IsPrime›.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hinj := Ideal.rootsOfUnityMapQuot_injective (I := 𝔓) m hN1 hcopP
  have hLpow : (φ • z) ^ m = 1 := by rw [← smul_pow', hzpow, smul_one]
  have hRpow : (z ^ q) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hzpow, one_pow]
  set uL := rootsOfUnity.mkOfPowEq (φ • z) hLpow with huL
  set uR := rootsOfUnity.mkOfPowEq (z ^ q) hRpow with huR
  have hcoeL : ((uL : (𝓞 L)ˣ) : 𝓞 L) = φ • z := rootsOfUnity.coe_mkOfPowEq _
  have hcoeR : ((uR : (𝓞 L)ˣ) : 𝓞 L) = z ^ q := rootsOfUnity.coe_mkOfPowEq _
  have hmapeq : Ideal.rootsOfUnityMapQuot 𝔓 m uL = Ideal.rootsOfUnityMapQuot 𝔓 m uR := by
    apply Units.ext
    rw [Ideal.rootsOfUnityMapQuot_apply 𝔓 m uL.2, Ideal.rootsOfUnityMapQuot_apply 𝔓 m uR.2,
      hcoeL, hcoeR]
    exact hspec
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
  sorry

open scoped Classical in
/-- Column orthogonality of the characters of a finite commutative group valued in `ℂˣ`:
`Σ_χ χ(g) = |G|` if `g = 1` and `0` otherwise. This is the only group-theoretic input to the
two cyclotomic orthogonality relations below; `ℂ` has enough roots of unity because it is
algebraically closed. -/
private theorem sum_galoisCharacter_eq_card_or_zero
    (G : Type*) [Group G] [IsMulCommutative G] [Finite G] [Fintype (G →* ℂˣ)] (g : G) :
    (∑ χ : G →* ℂˣ, (χ g : ℂ)) = if g = 1 then (Nat.card G : ℂ) else 0 := by
  letI : CommGroup G := { mul_comm := mul_comm' }
  haveI : NeZero (Monoid.exponent G) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent G) := inferInstance
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
  haveI : IsMulCommutative Gal(L/K) := IsCyclotomicExtension.isMulCommutative (S := {m}) K L
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
  haveI : IsMulCommutative Gal(L/K) := IsCyclotomicExtension.isMulCommutative (S := {m}) K L
  set τ := (frobeniusClass K L 𝔭).out
  have hsummand : ∀ χ : galoisCharacter K L,
      (χ σ : ℂ) * ((χ τ : ℂ))⁻¹ = (χ (σ * τ⁻¹) : ℂ) := fun χ => by
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  have hmk : ConjClasses.mk τ = frobeniusClass K L 𝔭 := Quotient.out_eq _
  have hne : σ * τ⁻¹ ≠ 1 := fun hσ =>
    _h <| hmk.symm.trans (congrArg ConjClasses.mk (mul_inv_eq_one.mp hσ)).symm
  simp_rw [hsummand]
  rw [sum_galoisCharacter_eq_card_or_zero Gal(L/K) (σ * τ⁻¹), if_neg hne]

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
        primeIdealZetaSum K
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 ((Nat.card Gal(L/K) : ℝ)⁻¹)) := by
  sorry

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
        primeIdealZetaSum K
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / primeIdealZetaSum K (Set.univ : Set (Ideal (𝓞 K))) s)
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
    HasDirichletDensity K
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card Gal(L/K) : ℝ)⁻¹) :=
  cyclotomic_density_from_two_sided_asymp K L m σ

/-- A variant of the cyclotomic-case theorem stated as a lower-density
inequality. Used in the abelian case to feed into the
`HasLowerDirichletDensity.mono` chain. -/
theorem chebotarev_cyclotomic_lowerDensity_ge
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] [FiniteDimensional K L] (σ : Gal(L/K)) :
    HasLowerDirichletDensity K
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card Gal(L/K) : ℝ)⁻¹) :=
  (chebotarev_cyclotomic K L m σ).hasLower

end Chebotarev
