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
    (G H : Type*) [Group G] [Group H] [Finite G] [Finite H] (σ : G) (τ : H)
    (_hn : Nat.card G ∣ orderOf τ) :
    (Subgroup.zpowers (σ, τ)) ⊓
        ((⊤ : Subgroup G).prod (⊥ : Subgroup H)) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨g, h⟩ hmem
  rw [Subgroup.mem_inf, Subgroup.mem_prod, Subgroup.mem_bot] at hmem
  obtain ⟨⟨k, hk⟩, _, (hh : h = 1)⟩ := hmem
  have h2 : τ ^ k = 1 := by simpa [hh] using congrArg Prod.snd hk
  have hg2 : σ ^ k = 1 := orderOf_dvd_iff_zpow_eq_one.mp
    (((orderOf_dvd_natCard σ).trans _hn).natCast.trans (orderOf_dvd_iff_zpow_eq_one.mpr h2))
  rw [Subgroup.mem_bot, Prod.mk_eq_one]
  exact ⟨by simpa [hg2] using (congrArg Prod.fst hk).symm, hh⟩

/-- Sharifi 7.2.2 Step 2 — partial **lower bound** on `δ_inf(S_σ)`
coming from one choice of cyclotomic crossing modulus `m`. Source quote
(p. 144): "δ_inf(S_σ) ≥ |H_n|/(|G|·|H|)".

Sketch: for each `τ ∈ H_n` (i.e., `|G| ∣ ord(τ)`), apply the cyclotomic
case to `L(μ_m)/F` where `F = K(μ_m)^{⟨(σ,τ)⟩}`; this yields density
`1/(|G|·|H|)` of primes of `K` whose Frobenius in `Gal(L(μ_m)/K) = G×H`
equals `(σ,τ)`. Each such prime contributes to `S_σ` (the
`K`-projection drops the `τ` component to `σ`), and the contributions
from distinct `τ` are disjoint. Summing over `τ ∈ H_n` gives the
lower bound.

**Previous form** (corrected 2026-05-28): the earlier statement claimed
`δ(S_σ) = 1/(|G|·|H|)` with the set `S_σ` (= primes with Frobenius `σ`
in `Gal(L/K)`), which was mathematically wrong — that set has density
`1/|G|` (Chebotarev abelian), not `1/(|G|·|H|)`. The actual sub-step
Sharifi uses is the per-`m` lower bound on `δ_inf(S_σ)`, captured by
the present statement.

Without `L(μ_m)` explicitly in scope, we state the conclusion of the
per-`m` summation step directly: a lower bound `|H_n(m)|/(|G|·|H(m)|)`
on the `liminf` of the density ratio for `S_σ` in `K`. -/
theorem liminf_density_S_sigma_ge_card_H_n_div_GH
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) (m : ℕ) (_hm : 1 ≤ m) :
    (Nat.card {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} : ℝ)
        / (Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ))
      ≤ Filter.liminf
          (fun s : ℝ ↦
            primeIdealZetaSum K
                {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 ∧
                  frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
              / primeIdealZetaSum K (Set.univ : Set (Ideal (𝓞 K))) s)
          (𝓝[>] 1) := by
  sorry

/-- Sharifi 7.2.2 Step 2 sub-lemma (iv) — explicit lower bound on
`|H_n|/|H|` via the prime-power factorisation of `n` (p. 144).
Verbatim source quote: "`|H_n|/|H| = ∏_{i=1}^r (1 - p_i^{k_i-1} /
p_i^{j_i k_i}) ≥ ∏_{i=1}^r (1 - 1/p^{(j-1)k_i + 1})`". -/
theorem H_n_over_H_lower_bound_via_prime_factorisation
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (_hm_one_mod : m % n = 1 % n) :
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

/-- Per-`σ` lower bound `δ_inf(S_σ) ≥ 1/|G|`, the limit of the per-`m`
bound `liminf_density_S_sigma_ge_card_H_n_div_GH` as `m → ∞` along
`m ≡ 1 mod n^k` using `H_n_over_H_tends_to_one` (so `|H_n|/|H| → 1`).
This is the lower half of Sharifi 7.2.2 Step 2 (p. 144). -/
theorem liminf_ratio_ge_inv_card_G
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) :
    (Nat.card Gal(L/K) : ℝ)⁻¹
      ≤ Filter.liminf
          (fun s : ℝ ↦
            primeIdealZetaSum K
                {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 ∧
                  frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
              / primeIdealZetaSum K (Set.univ : Set (Ideal (𝓞 K))) s)
          (𝓝[>] 1) := by
  sorry

/-- The density ratios of the `|G|` Frobenius-fibres `S_σ` (over
`σ ∈ Gal(L/K)`) sum to the ratio for the unramified primes, which tends
to `1` as `s ↓ 1` since the ramified primes are finite
(`finite_ramifiedIn`, density `0`). Sharifi 7.2.2 Step 2: the `S_σ`
partition the unramified primes. -/
theorem ratioSum_frobeniusFibres_tendsto_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] :
    Filter.Tendsto
      (fun s : ℝ ↦ ∑ σ : Gal(L/K),
        primeIdealZetaSum K
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / primeIdealZetaSum K (Set.univ : Set (Ideal (𝓞 K))) s)
      (𝓝[>] 1) (𝓝 1) := by
  sorry

/-- Pure real-analysis glue: a finite family `gᵢ` of functions, each with
`liminf gᵢ ≥ 1/N` (where `N` is the family size), whose sum tends to `1`,
must each tend to `1/N`. (The lower bounds and the sum-limit pin every
`gᵢ` to `1/N` by a pigeonhole on `liminf`/`limsup`.) -/
theorem tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one
    {ι : Type*} [Fintype ι] (g : ι → ℝ → ℝ)
    (hlo : ∀ i, (Fintype.card ι : ℝ)⁻¹ ≤ Filter.liminf (g i) (𝓝[>] (1 : ℝ)))
    (hsum : Filter.Tendsto (fun s ↦ ∑ i, g i s) (𝓝[>] (1 : ℝ)) (𝓝 1)) (i₀ : ι) :
    Filter.Tendsto (g i₀) (𝓝[>] (1 : ℝ)) (𝓝 (Fintype.card ι : ℝ)⁻¹) := by
  sorry

/-- **Chebotarev's theorem, abelian case** (Sharifi 7.2.2 Step 2).

For an abelian Galois extension `L/K` of number fields and any
`σ ∈ Gal(L/K)`, the Dirichlet density of primes `𝔭` of `𝓞 K` unramified in
`L` whose Frobenius equals `σ` is `1 / |Gal(L/K)|`.

**Composition**: the `|G|` fibres `S_σ` each have `liminf ≥ 1/|G|`
(`liminf_ratio_ge_inv_card_G`) and their density ratios sum to `1`
(`ratioSum_frobeniusFibres_tendsto_one`); the pigeonhole glue
`tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one` forces each to the
limit `1/|G|`. -/
theorem chebotarev_abelian
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) :
    HasDirichletDensity K
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card Gal(L/K) : ℝ)⁻¹) := by
  simp only [HasDirichletDensity, Nat.card_eq_fintype_card]
  refine tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one
    (fun τ s ↦
      primeIdealZetaSum K
          {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 ∧
            frobeniusClass K L 𝔭 = ConjClasses.mk τ} s
        / primeIdealZetaSum K (Set.univ : Set (Ideal (𝓞 K))) s)
    (fun τ ↦ ?_) (ratioSum_frobeniusFibres_tendsto_one K L) σ
  simpa only [Nat.card_eq_fintype_card] using liminf_ratio_ge_inv_card_G K L τ

/-- The lower-density bound `δ_inf ≥ |H_n|/(|G|·|H|)` from the full abelian
density, extracted via `HasDirichletDensity.hasLower`. -/
theorem chebotarev_abelian_lowerDensity_per_m
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) :
    HasLowerDirichletDensity K
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card Gal(L/K) : ℝ)⁻¹) :=
  (chebotarev_abelian K L σ).hasLower

end Chebotarev
