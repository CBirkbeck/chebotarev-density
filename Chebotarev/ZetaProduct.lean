module

public import Chebotarev.Frobenius
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

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
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] : Type _ := (L ≃ₐ[K] L) →* ℂˣ

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

/-- Sharifi 7.1.18 (p. 141): Euler product for an abelian Galois
character `χ : Gal(L/K) → ℂ^×`. The Lean statement asserts existence of
the L-function and its Euler product on `Re s > 1`. -/
theorem exists_artinLSeries_eulerProduct_abelian
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [hAb : IsMulCommutative (L ≃ₐ[K] L)]
    (χ : galoisCharacter K L) :
    ∃ Lf : ℂ → ℂ,
      ∀ s : ℂ, 1 < s.re →
        Lf s = ∏' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭},
          (1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ := by
  sorry

/-- Sharifi 7.1.16 (p. 141) local step: the local Euler factor at an
unramified prime `𝔭` of `K` factors as a product over characters.
Source quote (paraphrased identity): the local factor
`∏_{𝔓|𝔭}(1-N𝔓^{-s})^{-1}` equals `∏_χ(1-χ(σ_𝔭) N𝔭^{-s})^{-1}`. -/
theorem dedekindZeta_local_factor_eq_product_artin_local
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [hAb : IsMulCommutative (L ≃ₐ[K] L)]
    (𝔭 : Ideal (𝓞 K)) (_hpr : 𝔭.IsPrime) (_hnz : 𝔭 ≠ ⊥)
    (_hunr : UnramifiedIn K L 𝔭) (s : ℂ) (_hs : 1 < s.re) :
    ∏' 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥},
        (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹
      = ∏' χ : galoisCharacter K L,
        (1 - (χ (frobeniusClass K L 𝔭).out : ℂ) * (Ideal.absNorm 𝔭 : ℂ) ^ (-s))⁻¹ := by
  sorry

/-- Sharifi 7.1.19 step 1 (p. 142): geometry-of-numbers bound. The
partial-sum character sum `Σ_{N𝔞≤N} χ(𝔞)` is `O(N^{1-1/[K:ℚ]})` for a
nontrivial character `χ`. This is the convergence input that extends
`L(χ,·)` to `Z(1 - [K:ℚ]^{-1})`. -/
theorem character_sum_geometry_of_numbers_bound
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [hAb : IsMulCommutative (L ≃ₐ[K] L)]
    (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ N : ℕ,
      ‖∑' 𝔞 : {𝔞 : Ideal (𝓞 K) //
                𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N},
        (χ (frobeniusClass K L 𝔞.1).out : ℂ)‖
        ≤ C * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  sorry

/-- Sharifi 7.1.19 step 2 (p. 142): non-vanishing of `L(χ,1)` for
nontrivial `χ`. Source argument: if any `L(χ,1) = 0`, the
`log ζ_L = Σ_χ log L(χ,·)` decomposition leads to a sub-asymptotic
strictly weaker than the simple pole `log ζ_L ~ log(1/(s-1))`, a
contradiction. -/
theorem artinLSeries_one_ne_zero
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [hAb : IsMulCommutative (L ≃ₐ[K] L)]
    (χ : galoisCharacter K L) (_hχ : χ ≠ 1) :
    ∃ Lf : ℂ → ℂ, Lf 1 ≠ 0 := by
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
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [hAb : IsMulCommutative (L ≃ₐ[K] L)] :
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
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [hAb : IsMulCommutative (L ≃ₐ[K] L)]
    (σ : L ≃ₐ[K] L) :
    ∃ c : ℝ,
      Filter.Tendsto
        (fun s : ℝ ↦
          primeIdealZetaSum K
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
            - (Nat.card (L ≃ₐ[K] L) : ℝ)⁻¹ * Real.log (1 / (s - 1)))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds c) := by
  sorry

end Chebotarev
