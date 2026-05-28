module

public import Chebotarev.Abelian

/-!
# Chebotarev's density theorem

For a finite Galois extension `L/K` of number fields with Galois group
`G = Gal(L/K)` and a conjugacy class `C` of `G`, the Dirichlet density of
primes `𝔭` of `𝓞 K` (unramified in `L`) whose Frobenius conjugacy class is
`C` equals `|C| / |G|`.

The proof (Sharifi 7.2.2 Step 1; Stevenhagen–Lenstra Appendix paragraph 2)
reduces the conjugacy-class statement to the cyclic case via the
intermediate field `E = L^⟨σ⟩` for `σ ∈ C`:

- `L/E` is cyclic of degree `f = |⟨σ⟩|`, hence abelian, so the abelian case
  (`chebotarev_abelian`) gives density `1/f` for primes of `E` with
  Frobenius `σ`.
- A counting argument over the primes of `L` lying above a prime of `K`
  shows that, for the set `S` of primes `𝔭` of `K` whose Frobenius class is
  `C`, and `T_σ` the set of primes `P` of `E` with `σ_P = σ`,

      δ_K(S) = (f · |C| / |G|) · δ_E(T_σ).

  With `δ_E(T_σ) = 1/f` from the cyclic case, this gives `δ_K(S) = |C|/|G|`.

## Main results

* `Chebotarev.chebotarev_density` — Chebotarev's density
  theorem in conjugacy-class form.
* `Chebotarev.dirichlet_primes_in_AP` — Dirichlet's theorem
  on primes in arithmetic progressions, as a corollary.
* `Chebotarev.density_split_completely` — the density of
  primes of `K` that split completely in `L` is `1/[L:K]`.

## References

* Sharifi, *Algebraic Number Theory*, Theorem 7.2.2 (`docs/algnum.pdf`,
  pp. 142–144).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, Appendix
  (`docs/cheb.pdf`, p. 18).
-/

@[expose] public section

noncomputable section

open NumberField

namespace Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-! ### Sub-lemmas for `chebotarev_density`

Decomposed per Sharifi 7.2.2 Step 1 (p. 143). Source quote (verbatim):

> "Let σ ∈ C and E = L^⟨σ⟩ so that L/E is cyclic of degree f = |⟨σ⟩|.
> […] Let T_σ be the set of primes P of E unramified in L and over K
> with Frobenius φ_P at a prime of L over P equal to σ. If P ∈ T_σ,
> then φ_P = σ fixes E, so P has degree one over K. As P is by
> definition inert in L, there are exactly |G|/f primes of L over
> P ∩ K. As the Frobenius elements of such primes are distributed
> evenly among the elements of the conjugacy class C of σ, exactly
> |G|/f|C| of these have Frobenius σ. We may then compute the
> Dirichlet density of S: δ(S) = lim_{s→1+} Σ_𝔭∈S N𝔭^{-s} / Σ_𝔭
> N𝔭^{-s} = (f|C|/|G|) lim_{s→1+} Σ_P∈T_σ NP^{-s} / Σ_P NP^{-s} =
> (f|C|/|G|) δ(T_σ), recalling once again that Σ_𝔭 N𝔭^{-s} ~ Σ_P
> NP^{-s}. Supposing the theorem for K/E, we have δ(T_σ) = 1/f, and
> we therefore obtain δ(S) = |C|/|G|."

Four sub-lemmas:
(i) Cyclic subextension: `E = L^⟨σ⟩`, `[L:E] = |⟨σ⟩| = ord(σ)`.
(ii) Above-counting: for `𝔭 ∈ S`, exactly `|G|/(f|C|)` primes `𝔓` of
    `𝓞 L` over `𝔭` have `Frob_𝔓 = σ`, each "below" a unique `P ∈ T_σ`.
(iii) Density relation `δ_K(S) = (f|C|/|G|) · δ_E(T_σ)` (uses
    `Σ N𝔭^{-s} ~ Σ NP^{-s}` from Density.lean).
(iv) Apply `chebotarev_abelian` to `L/E` (cyclic): `δ_E(T_σ) = 1/f`.
-/

/-- Sharifi 7.2.2 Step 1, above-counting (p. 143). Verbatim source quote:
"exactly `|G|/f|C|` of these have Frobenius σ". For a prime `𝔭` of
`𝓞 K` with Frobenius class `C` and a representative `σ ∈ C`, the count
of primes `𝔓` of `𝓞 L` above `𝔭` with `Frob_𝔓 = σ` is `|G|/(f·|C|)`.

This is the substantive new sub-lemma for the conjugacy-class →
cyclic reduction; the fixed-field cyclic-subextension setup
(`E = L^⟨σ⟩`, `[L:E] = ord σ`) is mathlib's `IntermediateField.fixedField`
and `IsGalois.card_aut_eq_finrank` applied at `⟨σ⟩`, and the density-lift
formula `δ_K(S) = (f|C|/|G|) δ_E(T_σ)` follows from this counting
together with `Σ N𝔭^{-s} ~ Σ NP^{-s}` (Sharifi 7.1.12 applied to both
`K` and `E`). -/
theorem count_primes_above_with_frobenius_eq_sigma
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) (C : ConjClasses (L ≃ₐ[K] L)) (_hσ : ConjClasses.mk σ = C)
    (𝔭 : Ideal (𝓞 K)) (_hpr : 𝔭.IsPrime) (_hnz : 𝔭 ≠ ⊥)
    (_hunr : UnramifiedIn K L 𝔭) (_hCfrob : frobeniusClass K L 𝔭 = C) :
    Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (hp : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭)
        (hnz : 𝔓 ≠ ⊥),
        frobeniusAt K L 𝔓 hp hnz (by sorry) = σ}
      * orderOf σ * Nat.card C.carrier
      = Nat.card (L ≃ₐ[K] L) := by
  sorry

/-- **Chebotarev's density theorem** (Sharifi 7.2.2; SL Appendix).

For a finite Galois extension `L/K` of number fields with Galois group `G`
and a conjugacy class `C ⊆ G`, the Dirichlet density of the set of primes
`𝔭` of `𝓞 K` (unramified in `L`) such that the Frobenius conjugacy class of
`𝔭` is `C` equals `|C| / |G|`. -/
theorem chebotarev_density
    [FiniteDimensional K L]
    (C : ConjClasses (L ≃ₐ[K] L)) :
    HasDirichletDensity K
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = C}
      ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L)) := by
  sorry

/-- Existence of *infinitely many* primes with each Frobenius conjugacy class
— a qualitative corollary of `chebotarev_density`. -/
theorem infinite_setOf_frobenius_class
    [FiniteDimensional K L]
    (C : ConjClasses (L ≃ₐ[K] L)) :
    Set.Infinite
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = C} := by
  sorry

/-- **Density of completely split primes** (Sharifi 7.1.14, as a corollary of
Chebotarev applied to the identity conjugacy class).

The Dirichlet density of primes `𝔭` of `𝓞 K` that split completely in `L`
equals `1 / [L : K]`. -/
theorem density_split_completely
    [FiniteDimensional K L] :
    HasDirichletDensity K
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk 1}
      ((Module.finrank K L : ℝ)⁻¹) := by
  sorry

/-- **Dirichlet's theorem on primes in arithmetic progressions**, as a
density refinement of `Nat.infinite_setOf_prime_and_eq_mod`.

For coprime integers `a, n` with `1 ≤ n` and `gcd a n = 1`, the Dirichlet
density of primes `p` with `p ≡ a mod n` equals `1 / φ(n)`. This is the
specialisation of Chebotarev to `K = ℚ`, `L = ℚ(μ_n)` (Sharifi 7.2.3). -/
theorem dirichlet_primes_in_AP (n : ℕ) (hn : 1 ≤ n) (a : ZMod n)
    (ha : IsUnit a) :
    HasDirichletDensity ℚ
      ((fun p : ℕ ↦ Ideal.span {(p : 𝓞 ℚ)}) ''
        {p : ℕ | p.Prime ∧ (p : ZMod n) = a})
      ((Nat.totient n : ℝ)⁻¹) := by
  sorry

end Chebotarev
