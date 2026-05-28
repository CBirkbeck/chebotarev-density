module

public import Chebotarev.Cyclotomic
public import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Chebotarev's theorem: abelian case

For an abelian Galois extension `L/K` of number fields and any
`σ ∈ Gal(L/K)`, the Dirichlet density of primes `𝔭` of `𝓞 K` (unramified in
`L`) whose Frobenius equals `σ` is `1 / |Gal(L/K)|`.

The proof reduces to the cyclotomic case by *crossing with cyclotomic
extensions* (Chebotarev's original technique). For `m` coprime to the
discriminant of `L`, the field `L(μ_m)` is Galois over `K` with
`Gal(L(μ_m)/K) ≅ G × H` where `H = Gal(K(μ_m)/K) ⊆ (ℤ/mℤ)^×`. For `τ ∈ H`
with `|G| | ord(τ)`, the subgroup `⟨(σ, τ)⟩` has trivial intersection with
`G × {1}`, so its fixed field `F` satisfies `F(μ_m) = L(μ_m)` — making
`L(μ_m)/F` cyclotomic. The cyclotomic case applied to `L(μ_m)/F` and
`(σ, τ)` gives
`δ_F(primes P with σ_P = (σ, τ)) = 1/(|G| · |H|)`, and the (cyclic)
reduction lifts this through `F/K` to a lower-density bound on the primes
of `K` with Frobenius `σ`. Summing over `τ ∈ H_n = {τ : n | ord(τ)}`,

  δ_inf,K({𝔭 : σ_𝔭 = σ}) ≥ |H_n| / (|G| · |H|).

As `m` varies (chosen via Dirichlet's theorem to satisfy `m ≡ 1 mod n^k` for
large `k`), `|H_n|/|H| → 1`, so `δ_inf ≥ 1/|G|`. Summing over `σ ∈ G` then
forces equality.

## Main results

* `Chebotarev.chebotarev_abelian` — the density of primes
  of `K` unramified in an abelian extension `L/K` with Frobenius equal to
  `σ` is `1/|Gal(L/K)|`.

## References

* Sharifi, *Algebraic Number Theory*, §7.2.2 Step 2 (`docs/algnum.pdf`,
  pp. 143–144).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, Appendix
  paragraph 4 (`docs/cheb.pdf`, p. 18).
-/

@[expose] public section

noncomputable section

open NumberField Filter Topology

namespace Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-! ### Sub-lemmas for `chebotarev_abelian`

Decomposed per Sharifi 7.2.2 Step 2 (p. 143–144). Source quote
(verbatim, p. 143):

> "Choose m ≥ 1 not dividing the discriminant of L so that H =
> Gal(L(μ_m)/L) is isomorphic to (ℤ/mℤ)^× via the mod m cyclotomic
> character, and Gal(L(μ_m)/K) ≅ G × H. For σ ∈ G and τ ∈ H, let S_σ be
> the set of primes of K unramified in L with Frobenius σ in G, and let
> S_{σ,τ} be the set of primes of K unramified in L(μ_m) with Frobenius
> (σ,τ) ∈ G × H. Then δ_inf(S_σ) = Σ_{τ∈H} δ_inf(S_{σ,τ})."

And (p. 144):
> "Now suppose that |G| divides the order of τ. Then ⟨(σ,τ)⟩ ∩ (G × {1})
> = 1, which implies that L(μ_m) is given by adjoining μ_m to F =
> K(μ_m)^⟨(σ,τ)⟩."
>
> "[…] δ(S_{σ,τ}) exists and equals 1/|G||H|."
>
> "|H_n|/|H| = ∏_{i=1}^r (1 - p_i^{k_i-1}/p_i^{j_i k_i}) ≥ ∏_{i=1}^r
> (1 - 1/p^{(j-1)k_i + 1}) so |H_n|/|H| tends to 1 as j increases."

Five sub-lemmas (mirror Sharifi's structure):
-/

/-- Sharifi 7.2.2 Step 2 sub-lemma (i) — cyclic subgroup trivial meet
(p. 144). Source quote: "if `|G|` divides the order of `τ`, then
`⟨(σ,τ)⟩ ∩ (G × {1}) = 1`". This is the only place where the
`|G| | ord(τ)` hypothesis is used in Step 2. -/
theorem cyclic_subgroup_meets_G_times_one_trivially
    (G H : Type*) [Group G] [Group H] [Finite G] [Finite H]
    (σ : G) (τ : H) (_hn : Nat.card G ∣ orderOf τ) :
    (Subgroup.zpowers (σ, τ)) ⊓
        ((⊤ : Subgroup G).prod (⊥ : Subgroup H)) = ⊥ := by
  sorry

/-- Sharifi 7.2.2 Step 2 sub-lemma (ii) — for `n | ord(τ)`, the
cyclotomic case at `F(μ_m)/F` combined with Step 1's lifting yields the
per-`(σ,τ)` density. Source quote: "δ(S_{σ,τ}) exists and equals
1/|G||H|". The hypothesis `n | ord(τ)` (where `n = |G|`) is needed by
`cyclic_subgroup_meets_G_times_one_trivially` above. -/
theorem density_S_sigma_tau_eq_inv_card_GH
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [hAb : IsMulCommutative (L ≃ₐ[K] L)]
    (σ : L ≃ₐ[K] L) (m : ℕ) (_hm : 1 ≤ m) :
    HasDirichletDensity K
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card (L ≃ₐ[K] L) * Nat.card ((ZMod m)ˣ) : ℝ)⁻¹) := by
  sorry

/-- Sharifi 7.2.2 Step 2 sub-lemma (iv) — explicit lower bound on
`|H_n|/|H|` via the prime-power factorisation of `n` (p. 144).
Verbatim source quote: "`|H_n|/|H| = ∏_{i=1}^r (1 - p_i^{k_i-1} /
p_i^{j_i k_i}) ≥ ∏_{i=1}^r (1 - 1/p^{(j-1)k_i + 1})`". -/
theorem H_n_over_H_lower_bound_via_prime_factorisation
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (_hm_one_mod : m % n = 1 % n) :
    (Nat.card {τ : (ZMod m)ˣ // n ∣ orderOf τ} : ℝ) / Nat.card ((ZMod m)ˣ)
      ≥ (n.factorization.support.prod fun p ↦
          1 - 1 / (p : ℝ) ^ (Nat.factorization (m - 1) p - 1)) := by
  sorry

/-- Sharifi 7.2.2 Step 2 sub-lemma (v) — `|H_n|/|H| → 1` as `m ≡ 1 mod
n^k` for `k → ∞`. Verbatim source quote: "so `|H_n|/|H|` tends to 1 as
`j` increases". -/
theorem H_n_over_H_tends_to_one
    (n : ℕ) (_hn : 1 ≤ n) :
    Tendsto
      (fun k : ℕ ↦ (Nat.card {τ : (ZMod (n ^ k))ˣ // n ∣ orderOf τ} : ℝ)
        / Nat.card ((ZMod (n ^ k))ˣ))
      Filter.atTop (𝓝 1) := by
  sorry

/-- **Chebotarev's theorem, abelian case** (Sharifi 7.2.2 Step 2).

For an abelian Galois extension `L/K` of number fields and any
`σ ∈ Gal(L/K)`, the Dirichlet density of primes `𝔭` of `𝓞 K` unramified in
`L` whose Frobenius equals `σ` is `1 / |Gal(L/K)|`. -/
theorem chebotarev_abelian
    [FiniteDimensional K L]
    [hAb : IsMulCommutative (L ≃ₐ[K] L)]
    (σ : L ≃ₐ[K] L) :
    HasDirichletDensity K
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card (L ≃ₐ[K] L) : ℝ)⁻¹) := by
  sorry

/-- The lower-density bound `δ_inf ≥ |H_n|/(|G|·|H|)` obtained from a single
choice of cyclotomic crossing modulus `m`, before passing to the limit. This
is the per-`m` inequality at the heart of Sharifi 7.2.2 Step 2. -/
theorem chebotarev_abelian_lowerDensity_per_m
    [FiniteDimensional K L]
    [hAb : IsMulCommutative (L ≃ₐ[K] L)]
    (σ : L ≃ₐ[K] L) (m : ℕ) (hm : 1 ≤ m) :
    HasLowerDirichletDensity K
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card (L ≃ₐ[K] L) : ℝ)⁻¹) := by
  sorry

/-- The auxiliary fact `|H_n|/|H| → 1` as `m` varies through residues `m ≡ 1
mod n^k`. This is the analytic input from Dirichlet's theorem
(`Nat.infinite_setOf_prime_and_eq_mod`) used at the end of Sharifi 7.2.2
Step 2. -/
theorem ratio_order_divisible_tendsto_one (n : ℕ) (hn : 1 ≤ n) :
    Filter.Tendsto
      (fun k : ℕ ↦
        (Nat.card {τ : (ZMod (n ^ k))ˣ // n ∣ orderOf τ} : ℝ) /
          Nat.card (ZMod (n ^ k))ˣ)
      Filter.atTop (nhds 1) := by
  sorry

end Chebotarev
