module

public import CebotarevDensity.Cyclotomic
public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

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
            primeIdealZetaSum
                {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ (𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal),
                    𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt (𝓞 K) 𝔓) ∧
                  frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
              / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
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

/-! #### Number-theoretic helpers for `H_n_over_H_tends_to_one`

The proof is a direct CRT-free argument: writing `total k = φ(n^k)`,
`good k = #{τ : n ∣ ord τ}` and `bad k = #{τ : n ∤ ord τ}` in the unit group
`(ZMod (n^k))ˣ`, we bound `bad k / total k → 0` and conclude `good k / total k → 1`.
The key is a *uniform* (cyclicity-free) torsion bound `torsion_card_le`, fed at the
exponent `E = λ(n^k)`. The `p = 2` non-cyclic prime power needs no special handling:
the argument stays at the level of the relatively-negligible "bad" set. -/

/-- Uniform torsion bound in any finite commutative group:
`#{x : xᴹ = 1} · (E / gcd(E, M)) ≤ |G|`, where `E = Monoid.exponent G`. -/
private theorem torsion_card_le (G : Type*) [CommGroup G] [Finite G] (M : ℕ) :
    Nat.card {x : G // x ^ M = 1} * (Monoid.exponent G / Nat.gcd (Monoid.exponent G) M)
      ≤ Nat.card G := by
  classical
  set f : G →* G := powMonoidHom M with hf
  have hker : Nat.card f.ker = Nat.card {x : G // x ^ M = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [MonoidHom.mem_ker]; rfl))
  have hcard : Nat.card f.ker * Nat.card f.range = Nat.card G := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]; ring
  obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent (Monoid.ExponentExists.of_finite (G := G))
  have hord : orderOf (g ^ M) = Monoid.exponent G / Nat.gcd (Monoid.exponent G) M := by
    rw [orderOf_pow, hg]
  have hle : orderOf (g ^ M) ≤ Nat.card f.range := by
    rw [← Nat.card_zpowers]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion (by
      rw [Subgroup.zpowers_le]; exact ⟨g, rfl⟩)) (Subgroup.inclusion_injective _)
  rw [← hord]
  calc Nat.card {x : G // x ^ M = 1} * orderOf (g ^ M)
      = Nat.card f.ker * orderOf (g ^ M) := by rw [hker]
    _ ≤ Nat.card f.ker * Nat.card f.range := Nat.mul_le_mul_left _ hle
    _ = Nat.card G := hcard

/-- If `d ∣ E` and the `p`-adic valuation of `d` is `≤ v - 1`, then `d` divides the
"capped" modulus `ordCompl[p] E * p ^ (v - 1)` (which replaces `E`'s `p`-part by
`p ^ (v - 1)`). Used to land a small-order element in an `M`-torsion subgroup. -/
private theorem dvd_capped (E d p v : ℕ) (hp : p.Prime) (hE : E ≠ 0) (hd : d ∣ E)
    (hvp : d.factorization p ≤ v - 1) : d ∣ ordCompl[p] E * p ^ (v - 1) := by
  have hdne : d ≠ 0 := fun h => by subst h; exact hE (Nat.eq_zero_of_zero_dvd hd)
  have hMne : ordCompl[p] E * p ^ (v - 1) ≠ 0 :=
    mul_ne_zero (Nat.ordCompl_pos p hE).ne' (pow_ne_zero _ hp.ne_zero)
  rw [← Nat.factorization_le_iff_dvd hdne hMne]
  intro q
  rw [Nat.factorization_mul (Nat.ordCompl_pos p hE).ne' (pow_ne_zero _ hp.ne_zero)]
  simp only [Finsupp.coe_add, Pi.add_apply, hp.factorization_pow, Finsupp.single_apply,
    Nat.factorization_ordCompl]
  by_cases hq : q = p
  · subst hq; rw [Finsupp.erase_same]; simp only [if_pos, zero_add]; exact hvp
  · rw [Finsupp.erase_ne hq, if_neg (fun h => hq h.symm), add_zero]
    exact (Nat.factorization_le_iff_dvd hdne hE).mpr hd q

/-- The capped modulus `ordCompl[p] E * p ^ (v - 1)` divides `E` when `v - 1 ≤ v_p(E)`. -/
private theorem M_dvd_E (E p v : ℕ) (hp : p.Prime) (hE : E ≠ 0) (hle : v - 1 ≤ E.factorization p) :
    ordCompl[p] E * p ^ (v - 1) ∣ E := by
  have hMne : ordCompl[p] E * p ^ (v - 1) ≠ 0 :=
    mul_ne_zero (Nat.ordCompl_pos p hE).ne' (pow_ne_zero _ hp.ne_zero)
  rw [← Nat.factorization_le_iff_dvd hMne hE]
  intro q
  rw [Nat.factorization_mul (Nat.ordCompl_pos p hE).ne' (pow_ne_zero _ hp.ne_zero)]
  simp only [Finsupp.coe_add, Pi.add_apply, hp.factorization_pow, Finsupp.single_apply,
    Nat.factorization_ordCompl]
  by_cases hq : q = p
  · subst hq; rw [Finsupp.erase_same, if_pos rfl]; omega
  · rw [Finsupp.erase_ne hq, if_neg (fun h => hq h.symm)]; omega

/-- Factoring out the complementary `p`-power: `E = (ordCompl[p] E * p ^ (v - 1)) *
p ^ (v_p(E) - (v - 1))`, used to compute `E / M = p ^ (v_p(E) - (v - 1))`. -/
private theorem E_eq_M_mul (E p v : ℕ) (hle : v - 1 ≤ E.factorization p) :
    E = ordCompl[p] E * p ^ (v - 1) * p ^ (E.factorization p - (v - 1)) := by
  rw [mul_assoc, ← pow_add,
    show v - 1 + (E.factorization p - (v - 1)) = E.factorization p by omega,
    mul_comm (ordCompl[p] E), Nat.ordProj_mul_ordCompl_eq_self]

/-- For a prime `p ∣ n`, the Carmichael function satisfies
`p ^ (k · v_p(n) - 2) ∣ λ(n^k)`. -/
private theorem pk_dvd_carmichael (n k p : ℕ) (hp : p.Prime) (hpn : p ∣ n) :
    p ^ (k * n.factorization p - 2) ∣ ArithmeticFunction.carmichael (n ^ k) := by
  set v := n.factorization p with hv
  have hdvd1 : p ^ (k * v) ∣ n ^ k := by
    calc p ^ (k * v) = (p ^ v) ^ k := by rw [← pow_mul, mul_comm]
      _ ∣ n ^ k := pow_dvd_pow_of_dvd (Nat.ordProj_dvd n p) k
  have hdvd2 := ArithmeticFunction.carmichael_dvd hdvd1
  have hdvd3 : p ^ (k * v - 2) ∣ ArithmeticFunction.carmichael (p ^ (k * v)) := by
    by_cases h2 : p = 2
    · subst h2
      by_cases hj2 : k * v = 2
      · rw [hj2]; norm_num
      · rw [ArithmeticFunction.carmichael_two_pow_of_ne_two hj2]
    · rw [ArithmeticFunction.carmichael_pow_of_prime_ne_two (k * v) hp h2]
      rcases Nat.eq_zero_or_pos (k * v) with h0 | hpos
      · rw [h0]; simp
      · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        rw [hm] at *
        rw [Nat.totient_prime_pow_succ hp]
        exact (pow_dvd_pow p (show m + 1 - 2 ≤ m by omega)).trans (dvd_mul_right (p ^ m) (p - 1))
  exact hdvd3.trans hdvd2

/-- Cardinality monotonicity for the "bad at `p`" set sitting inside an `M`-torsion
subgroup, given each bad element satisfies `xᴹ = 1`. -/
private theorem bad_le_torsion (G : Type*) [Finite G] [Monoid G] (M p v : ℕ)
    (h : ∀ x : G, ¬ p ^ v ∣ orderOf x → x ^ M = 1) :
    Nat.card {x : G // ¬ p ^ v ∣ orderOf x} ≤ Nat.card {x : G // x ^ M = 1} :=
  Nat.card_le_card_of_injective (fun x => ⟨x.1, h x.1 x.2⟩)
    (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))

/-- If `n ∤ d` (with `n, d ≠ 0`) then some prime power `p ^ v_p(n)` already fails to
divide `d`: the contrapositive of the prime-power criterion `n ∣ d`. -/
private theorem exists_prime_pow_not_dvd (n d : ℕ) (hn : n ≠ 0) (hd : d ≠ 0) (hndvd : ¬ n ∣ d) :
    ∃ p ∈ n.primeFactors, ¬ p ^ (n.factorization p) ∣ d := by
  by_contra hcon
  push Not at hcon
  apply hndvd
  rw [← Nat.factorization_le_iff_dvd hn hd]
  intro p
  by_cases hp : p ∈ n.primeFactors
  · have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    exact (Nat.Prime.pow_dvd_iff_le_factorization hpp hd).mp (hcon p hp)
  · have hzero : n.factorization p = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hp
    rw [hzero]; exact Nat.zero_le _

/-- A subtype carved by `P` injects into a finite union of subtypes carved by `Q i`
whenever `P x` forces some `Q i x` with `i ∈ s`; hence its card is `≤ Σ_i #{Q i}`. -/
private theorem card_le_sum_card {G : Type*} [Finite G] {ι : Type*} (s : Finset ι)
    (P : G → Prop) (Q : ι → G → Prop) (h : ∀ x, P x → ∃ i ∈ s, Q i x) :
    Nat.card {x : G // P x} ≤ ∑ i ∈ s, Nat.card {x : G // Q i x} := by
  classical
  have : Fintype G := Fintype.ofFinite G
  simp only [Nat.card_eq_fintype_card]
  calc Fintype.card {x : G // P x}
      = (Finset.univ.filter P).card := by rw [Fintype.card_subtype]
    _ ≤ (s.biUnion (fun i => Finset.univ.filter (Q i))).card := by
        refine Finset.card_le_card (fun x hx => ?_)
        rw [Finset.mem_filter] at hx
        obtain ⟨i, hi, hqi⟩ := h x hx.2
        exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hqi⟩⟩
    _ ≤ ∑ i ∈ s, (Finset.univ.filter (Q i)).card := Finset.card_biUnion_le
    _ = ∑ i ∈ s, Fintype.card {x : G // Q i x} :=
        Finset.sum_congr rfl (fun i _ => by rw [Fintype.card_subtype])

/-- Each per-prime tail `1 / p ^ (k · v - v - 1) → 0` as `k → ∞` (base `p ≥ 2`,
exponent `→ ∞`). -/
private theorem summand_tendsto (p v : ℕ) (hp : 2 ≤ p) (hv : 1 ≤ v) :
    Tendsto (fun k : ℕ => (1 : ℝ) / (p : ℝ) ^ (k * v - v - 1)) atTop (𝓝 0) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hpinv1 : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one₀ hp0]; exact_mod_cast hp.trans_lt' Nat.one_lt_two
  have hbase : Tendsto (fun m : ℕ => ((p : ℝ)⁻¹) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hpinv1
  have hexp : Tendsto (fun k : ℕ => k * v - v - 1) atTop atTop := by
    refine tendsto_atTop_mono (f := fun k : ℕ => k - (v + 1)) (fun k => ?_)
      (tendsto_sub_atTop_nat (v + 1))
    have : k ≤ k * v := Nat.le_mul_of_pos_right k hv; omega
  refine (hbase.comp hexp).congr (fun k => ?_)
  simp [Function.comp_apply, one_div, inv_pow]

/-- The "bad" ratio is bounded by the sum of per-prime tails: from a cover
`bad ≤ Σ_p badp` and the per-prime bounds `badp · P p ^ e ≤ total`, conclude
`bad / total ≤ Σ_p 1 / P p ^ e` in `ℝ`. -/
private theorem ratio_bound (bad total : ℕ) (s : Finset ℕ) (badp : ℕ → ℕ) (e : ℕ → ℕ) (P : ℕ → ℕ)
    (htot : 0 < total) (hcover : bad ≤ ∑ p ∈ s, badp p) (hP : ∀ p ∈ s, 0 < P p)
    (hbound : ∀ p ∈ s, badp p * (P p) ^ (e p) ≤ total) :
    (bad : ℝ) / total ≤ ∑ p ∈ s, (1 : ℝ) / (P p : ℝ) ^ (e p) := by
  have htotR : (0 : ℝ) < total := by exact_mod_cast htot
  have hnum : (bad : ℝ) ≤ ∑ p ∈ s, (badp p : ℝ) := by
    calc (bad : ℝ) ≤ ((∑ p ∈ s, badp p : ℕ) : ℝ) := by exact_mod_cast hcover
      _ = ∑ p ∈ s, (badp p : ℝ) := by push_cast; ring
  calc (bad : ℝ) / total
      ≤ (∑ p ∈ s, (badp p : ℝ)) / total := by gcongr
    _ = ∑ p ∈ s, (badp p : ℝ) / total := by rw [Finset.sum_div]
    _ ≤ ∑ p ∈ s, (1 : ℝ) / (P p : ℝ) ^ (e p) := by
        refine Finset.sum_le_sum (fun p hps => ?_)
        have hPp : (0 : ℝ) < (P p : ℝ) ^ (e p) := by have := hP p hps; positivity
        rw [div_le_div_iff₀ htotR hPp, one_mul]
        calc (badp p : ℝ) * (P p : ℝ) ^ (e p) = ((badp p * (P p) ^ (e p) : ℕ) : ℝ) := by
              push_cast; ring
          _ ≤ (total : ℝ) := by exact_mod_cast hbound p hps

/-- The number of units of `ZMod (n^k)` with `p ^ v_p(n) ∤ ord τ`, times
`p ^ (k v_p(n) - v_p(n) - 1)`, is at most `φ(n^k)`. -/
private theorem perprime_bound (n k p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (hn2 : 2 ≤ n) (hk : 2 ≤ k) :
    Nat.card {τ : (ZMod (n ^ k))ˣ // ¬ p ^ n.factorization p ∣ orderOf τ}
      * p ^ (k * n.factorization p - n.factorization p - 1)
      ≤ Nat.card (ZMod (n ^ k))ˣ := by
  classical
  have hnk : NeZero (n ^ k) := ⟨pow_ne_zero k (by omega)⟩
  set G := (ZMod (n ^ k))ˣ with hG
  set v := n.factorization p with hv
  have hv1 : 1 ≤ v := hv ▸ Nat.Prime.factorization_pos_of_dvd hp (by omega) hpn
  set E := Monoid.exponent G with hE
  have hEne : E ≠ 0 := hE ▸ (Monoid.ExponentExists.of_finite (G := G)).exponent_ne_zero
  set M := ordCompl[p] E * p ^ (v - 1) with hM
  have hMne : M ≠ 0 := mul_ne_zero (Nat.ordCompl_pos p hEne).ne' (pow_ne_zero _ hp.ne_zero)
  have h2v : 2 * v ≤ k * v := Nat.mul_le_mul_right v hk
  have hvpE : k * v - 2 ≤ E.factorization p := by
    have hdvd : p ^ (k * v - 2) ∣ E := by
      rw [hE, ← ArithmeticFunction.carmichael_eq_exponent' (n ^ k)]
      exact pk_dvd_carmichael n k p hp hpn
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp hEne).mp hdvd
  have hle1 : v - 1 ≤ E.factorization p := by omega
  have hMdvdE : M ∣ E := M_dvd_E E p v hp hEne hle1
  have hgcd : Nat.gcd E M = M := Nat.gcd_eq_right hMdvdE
  have hEdivM : E / M = p ^ (E.factorization p - (v - 1)) :=
    Nat.div_eq_of_eq_mul_right (Nat.pos_of_ne_zero hMne) (E_eq_M_mul E p v hle1)
  have hbad_sub : Nat.card {τ : G // ¬ p ^ v ∣ orderOf τ} ≤ Nat.card {τ : G // τ ^ M = 1} := by
    refine bad_le_torsion G M p v (fun x hx => ?_)
    rw [← orderOf_dvd_iff_pow_eq_one]
    refine dvd_capped E (orderOf x) p v hp hEne ?_ ?_
    · rw [hE]; exact Monoid.order_dvd_exponent x
    · by_contra hcon
      push Not at hcon
      exact hx ((Nat.Prime.pow_dvd_iff_le_factorization hp (orderOf_pos x).ne').mpr (by omega))
  have hEM : p ^ (k * v - v - 1) ≤ E / M := by
    rw [hEdivM]; exact pow_le_pow_right₀ hp.one_le (by omega)
  calc Nat.card {τ : G // ¬ p ^ v ∣ orderOf τ} * p ^ (k * v - v - 1)
      ≤ Nat.card {τ : G // τ ^ M = 1} * p ^ (k * v - v - 1) := Nat.mul_le_mul_right _ hbad_sub
    _ ≤ Nat.card {τ : G // τ ^ M = 1} * (E / M) := Nat.mul_le_mul_left _ hEM
    _ = Nat.card {τ : G // τ ^ M = 1} * (E / Nat.gcd E M) := by rw [hgcd]
    _ ≤ Nat.card G := torsion_card_le G M

/-- Sharifi 7.2.2 Step 2 sub-lemma (v) — `|H_n|/|H| → 1` as `m ≡ 1 mod
n^k` for `k → ∞`. Verbatim source quote: "so `|H_n|/|H|` tends to 1 as
`j` increases". -/
theorem H_n_over_H_tends_to_one (n : ℕ) (_hn : 1 ≤ n) :
    Tendsto
      (fun k : ℕ ↦ (Nat.card {τ : (ZMod (n ^ k))ˣ // n ∣ orderOf τ} : ℝ)
        / Nat.card ((ZMod (n ^ k))ˣ))
      Filter.atTop (𝓝 1) := by
  classical
  rcases eq_or_lt_of_le _hn with hn1 | hn2'
  · have hn1' : n = 1 := hn1.symm
    subst hn1'
    have hconst : ∀ k : ℕ, (Nat.card {τ : (ZMod (1 ^ k))ˣ // (1 : ℕ) ∣ orderOf τ} : ℝ)
        / Nat.card ((ZMod (1 ^ k))ˣ) = 1 := by
      intro k
      have hg : Nat.card {τ : (ZMod (1 ^ k))ˣ // (1 : ℕ) ∣ orderOf τ}
          = Nat.card ((ZMod (1 ^ k))ˣ) := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact Fintype.card_congr (Equiv.subtypeUnivEquiv (fun x => one_dvd _))
      rw [hg]
      have hpos : 0 < Nat.card ((ZMod (1 ^ k))ˣ) := Nat.card_pos
      field_simp
    rw [tendsto_congr hconst]; exact tendsto_const_nhds
  · have hn2 : 2 ≤ n := hn2'
    set total : ℕ → ℕ := fun k => Nat.card ((ZMod (n ^ k))ˣ) with htotal
    set good : ℕ → ℕ := fun k => Nat.card {τ : (ZMod (n ^ k))ˣ // n ∣ orderOf τ} with hgood
    set bad : ℕ → ℕ := fun k => Nat.card {τ : (ZMod (n ^ k))ˣ // ¬ n ∣ orderOf τ} with hbad
    have hnk : ∀ k, NeZero (n ^ k) := fun k => ⟨pow_ne_zero k (by omega)⟩
    have htotpos : ∀ k, 0 < total k := fun k => by have := hnk k; exact Nat.card_pos
    have hgb : ∀ k, good k + bad k = total k := fun k => by
      have := hnk k
      rw [hgood, hbad, htotal]
      simp only [Nat.card_eq_fintype_card]
      rw [Fintype.card_subtype_compl]
      have hle : Fintype.card {τ : (ZMod (n ^ k))ˣ // n ∣ orderOf τ}
          ≤ Fintype.card ((ZMod (n ^ k))ˣ) := Fintype.card_subtype_le _
      omega
    set S : ℕ → ℝ := fun k => ∑ p ∈ n.primeFactors,
      (1 : ℝ) / (p : ℝ) ^ (k * n.factorization p - n.factorization p - 1) with hSdef
    have hStendsto : Tendsto S atTop (𝓝 0) := by
      rw [hSdef, show (0 : ℝ) = ∑ _p ∈ n.primeFactors, (0 : ℝ) by simp]
      refine tendsto_finsetSum _ (fun p hp => ?_)
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      exact summand_tendsto p (n.factorization p) hpp.two_le
        (Nat.Prime.factorization_pos_of_dvd hpp (by omega) hpdvd)
    have hbadratio : Tendsto (fun k => (bad k : ℝ) / total k) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hStendsto
        (Filter.Eventually.of_forall (fun k => by positivity)) ?_
      filter_upwards [Filter.eventually_ge_atTop 2] with k hk
      refine ratio_bound (bad k) (total k) n.primeFactors
        (fun p => Nat.card {τ : (ZMod (n ^ k))ˣ // ¬ p ^ n.factorization p ∣ orderOf τ})
        (fun p => k * n.factorization p - n.factorization p - 1) (fun p => p)
        (htotpos k) ?_ ?_ ?_
      · rw [hbad]
        refine card_le_sum_card n.primeFactors (fun τ => ¬ n ∣ orderOf τ)
          (fun p τ => ¬ p ^ n.factorization p ∣ orderOf τ) (fun τ hτ => ?_)
        have := hnk k
        exact exists_prime_pow_not_dvd n (orderOf τ) (by omega) (orderOf_pos τ).ne' hτ
      · exact fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
      · intro p hp
        have := hnk k
        exact perprime_bound n k p (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp) hn2 hk
    have heq : ∀ k, (good k : ℝ) / total k = 1 - (bad k : ℝ) / total k := by
      intro k
      have hgbk : (good k : ℝ) + (bad k : ℝ) = (total k : ℝ) := by exact_mod_cast hgb k
      have htk : (total k : ℝ) ≠ 0 := by exact_mod_cast (htotpos k).ne'
      field_simp
      linarith [hgbk]
    rw [tendsto_congr heq]
    simpa using hbadratio.const_sub (1 : ℝ)

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
            primeIdealZetaSum
                {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ (𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal),
                    𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt (𝓞 K) 𝔓) ∧
                  frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
              / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
          (𝓝[>] 1) := by
  sorry

/-- The density ratios of the `|G|` Frobenius-fibres `S_σ` (over
`σ ∈ Gal(L/K)`) sum to the ratio for the unramified primes, which tends
to `1` as `s ↓ 1` since the ramified primes are finite
(`finite_ramifiedIn`, density `0`). Sharifi 7.2.2 Step 2: the `S_σ`
partition the unramified primes. -/
theorem ratioSum_frobeniusFibres_tendsto_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] :
    Filter.Tendsto
      (fun s : ℝ ↦ ∑ σ : Gal(L/K),
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ (𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal),
                𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt (𝓞 K) 𝔓) ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
      (𝓝[>] 1) (𝓝 1) := by
  classical
  set S : Gal(L/K) → Set (Ideal (𝓞 K)) := fun σ =>
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ (𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal),
        𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt (𝓞 K) 𝔓) ∧
      frobeniusClass K L 𝔭 = ConjClasses.mk σ}
    with hS
  set R : Set (Ideal (𝓞 K)) :=
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ (𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal),
      𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt (𝓞 K) 𝔓)} with hR
  set D : ℝ → ℝ := primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) with hD
  have hmk_inj : Function.Injective (ConjClasses.mk : Gal(L/K) → ConjClasses Gal(L/K)) := by
    intro a b hab
    obtain ⟨c, hc⟩ : IsConj a b := ConjClasses.mk_eq_mk_iff_isConj.mp hab
    rw [SemiconjBy, mul_comm' (c : Gal(L/K))] at hc
    exact mul_right_cancel hc
  have hpd : ((Finset.univ : Finset Gal(L/K)) : Set Gal(L/K)).PairwiseDisjoint S := by
    intro a _ b _ hab
    refine Set.disjoint_left.mpr fun 𝔭 ha hb => hab (hmk_inj ?_)
    rw [hS] at ha hb
    exact ha.2.2.symm.trans hb.2.2
  have hdisjR : Disjoint (⋃ σ ∈ (Finset.univ : Finset Gal(L/K)), S σ) R := by
    refine Set.disjoint_left.mpr fun 𝔭 hmem hbad => ?_
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨σ, -, hσ⟩ := hmem
    exact hbad.2.2 (hS ▸ hσ).2.1
  have hcover : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
      𝔭 ∈ (⋃ σ ∈ (Finset.univ : Finset Gal(L/K)), S σ) ∪ R := by
    intro 𝔭 hp hne
    by_cases hunr : 𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal), 𝔓.LiesOver 𝔭 →
        Algebra.IsUnramifiedAt (𝓞 K) 𝔓
    · obtain ⟨σ, hσ⟩ := ConjClasses.mk_surjective (frobeniusClass K L 𝔭)
      exact Or.inl <| Set.mem_iUnion.mpr ⟨σ, Set.mem_iUnion.mpr ⟨Finset.mem_univ σ,
        hS ▸ ⟨hp, hunr, hσ.symm⟩⟩⟩
    · exact Or.inr ⟨hp, hne, hunr⟩
  have hRfin : R.Finite := finite_ramifiedIn K L
  have hR0 : Filter.Tendsto (fun s ↦ primeIdealZetaSum R s / D s) (𝓝[>] 1) (𝓝 0) :=
    hasDirichletDensity_of_finite K hRfin
  have hDpos : ∀ᶠ s in 𝓝[>] (1 : ℝ), 0 < D s :=
    (primeIdealZetaSum_univ_tendsto_atTop K).eventually_gt_atTop 0
  have hcomp : Filter.Tendsto (fun s ↦ 1 - primeIdealZetaSum R s / D s) (𝓝[>] 1) (𝓝 1) := by
    simpa using hR0.const_sub 1
  refine hcomp.congr' ?_
  filter_upwards [hDpos, self_mem_nhdsWithin] with s hpos hs1
  simp only [Set.mem_Ioi] at hs1
  have hsum : ∑ σ : Gal(L/K), primeIdealZetaSum (S σ) s
      = primeIdealZetaSum (⋃ σ ∈ (Finset.univ : Finset Gal(L/K)), S σ) s :=
    (primeIdealZetaSum_biUnion_of_pairwiseDisjoint Finset.univ S hpd hs1).symm
  have hadd : primeIdealZetaSum (⋃ σ ∈ (Finset.univ : Finset Gal(L/K)), S σ) s
      + primeIdealZetaSum R s = D s := by
    rw [← primeIdealZetaSum_union_of_disjoint hdisjR hs1, hD]
    exact primeIdealZetaSum_eq_univ_of_forall_prime_mem hcover s
  rw [← Finset.sum_div, hsum]
  field_simp
  linarith [hadd]

section LiminfSumGlue

/-! Generic real-analysis helpers for the pigeonhole glue below. They live in a
conditionally complete linearly ordered topological additive group; the only
instance we apply them at is `ℝ`. -/

variable {ι α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
  [DenselyOrdered α] [AddLeftMono α] {l : Filter ι} [l.NeBot]

omit [DenselyOrdered α] [l.NeBot] in
/-- A finite sum of below-bounded functions is below-bounded. -/
private lemma sum_isBoundedUnder_ge {κ : Type*} (g : κ → ι → α) (t : Finset κ)
    (h : ∀ j ∈ t, l.IsBoundedUnder (· ≥ ·) (g j)) :
    l.IsBoundedUnder (· ≥ ·) (fun x ↦ ∑ j ∈ t, g j x) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using (isBoundedUnder_const (r := (· ≥ ·)) (l := l) (a := (0 : α)))
  | insert a s ha ih =>
      simpa [Finset.sum_insert ha, Pi.add_def] using
        isBoundedUnder_ge_add (h a (Finset.mem_insert_self a s))
          (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

omit [DenselyOrdered α] [l.NeBot] in
/-- A finite sum of above-bounded functions is above-bounded. -/
private lemma sum_isBoundedUnder_le {κ : Type*} (g : κ → ι → α) (t : Finset κ)
    (h : ∀ j ∈ t, l.IsBoundedUnder (· ≤ ·) (g j)) :
    l.IsBoundedUnder (· ≤ ·) (fun x ↦ ∑ j ∈ t, g j x) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using (isBoundedUnder_const (r := (· ≤ ·)) (l := l) (a := (0 : α)))
  | insert a s ha ih =>
      simpa [Finset.sum_insert ha, Pi.add_def] using
        isBoundedUnder_le_add (h a (Finset.mem_insert_self a s))
          (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

/-- Superadditivity of `liminf` over a `Finset.sum`: the sum of the `liminf`s is
at most the `liminf` of the sum. -/
private lemma sum_liminf_le_liminf_sum {κ : Type*} (g : κ → ι → α) (t : Finset κ)
    (hbelow : ∀ j ∈ t, l.IsBoundedUnder (· ≥ ·) (g j))
    (habove : ∀ j ∈ t, l.IsBoundedUnder (· ≤ ·) (g j)) :
    ∑ j ∈ t, liminf (g j) l ≤ liminf (fun x ↦ ∑ j ∈ t, g j x) l := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hbS : l.IsBoundedUnder (· ≥ ·) (fun x ↦ ∑ j ∈ s, g j x) :=
        sum_isBoundedUnder_ge g s (fun j hj ↦ hbelow j (Finset.mem_insert_of_mem hj))
      have haS : l.IsBoundedUnder (· ≤ ·) (fun x ↦ ∑ j ∈ s, g j x) :=
        sum_isBoundedUnder_le g s (fun j hj ↦ habove j (Finset.mem_insert_of_mem hj))
      have step : liminf (g a) l + liminf (fun x ↦ ∑ j ∈ s, g j x) l
          ≤ liminf (fun x ↦ g a x + ∑ j ∈ s, g j x) l :=
        le_liminf_add (hbelow a (Finset.mem_insert_self a s))
          (habove a (Finset.mem_insert_self a s)) hbS (IsBoundedUnder.isCoboundedUnder_ge haS)
      calc liminf (g a) l + ∑ j ∈ s, liminf (g j) l
          ≤ liminf (g a) l + liminf (fun x ↦ ∑ j ∈ s, g j x) l := by
            gcongr
            exact ih (fun j hj ↦ hbelow j (Finset.mem_insert_of_mem hj))
              (fun j hj ↦ habove j (Finset.mem_insert_of_mem hj))
        _ ≤ liminf (fun x ↦ g a x + ∑ j ∈ s, g j x) l := step
        _ = liminf (fun x ↦ ∑ j ∈ insert a s, g j x) l := by simp_rw [Finset.sum_insert ha]

end LiminfSumGlue

/-- Pure real-analysis glue: a finite family `gᵢ` of functions, each with
`liminf gᵢ ≥ 1/N` (where `N` is the family size) and bounded below, whose sum
tends to `1`, must each tend to `1/N`. (The lower bounds and the sum-limit pin
every `gᵢ` to `1/N` by a pigeonhole on `liminf`/`limsup`.)

The below-boundedness hypothesis `hbelow` is genuinely needed: a finite `liminf`
lower bound alone does not force below-boundedness in a conditionally complete
order, so without it the statement is false (one `gᵢ` could dip to `-∞` while
keeping a spurious `liminf` and the sum still converging). At the only call site
(`chebotarev_abelian`) each `gᵢ` is a ratio of nonnegative Dirichlet sums, hence
`0 ≤ gᵢ`, so `hbelow` is immediate. -/
theorem tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one {ι : Type*} [Fintype ι] (g : ι → ℝ → ℝ)
    (hlo : ∀ i, (Fintype.card ι : ℝ)⁻¹ ≤ Filter.liminf (g i) (𝓝[>] (1 : ℝ)))
    (hbelow : ∀ i, Filter.IsBoundedUnder (· ≥ ·) (𝓝[>] (1 : ℝ)) (g i))
    (hsum : Filter.Tendsto (fun s ↦ ∑ i, g i s) (𝓝[>] (1 : ℝ)) (𝓝 1)) (i₀ : ι) :
    Filter.Tendsto (g i₀) (𝓝[>] (1 : ℝ)) (𝓝 (Fintype.card ι : ℝ)⁻¹) := by
  classical
  set l : Filter ℝ := 𝓝[>] (1 : ℝ) with hl
  set N : ℕ := Fintype.card ι with hN
  set F : ℝ → ℝ := fun s ↦ ∑ i, g i s with hF
  have hFle : l.IsBoundedUnder (· ≤ ·) F := hsum.isBoundedUnder_le
  have hFlimsup : limsup F l = 1 := hsum.limsup_eq
  have hgle : ∀ i, l.IsBoundedUnder (· ≤ ·) (g i) := by
    intro i
    have hdecomp : ∀ s, g i s = F s - ∑ j ∈ Finset.univ.erase i, g j s := by
      intro s
      have := Finset.add_sum_erase Finset.univ (fun j ↦ g j s) (Finset.mem_univ i)
      simp only [hF]
      linarith [this]
    obtain ⟨a, ha⟩ := hFle.eventually_le
    have hrestge : l.IsBoundedUnder (· ≥ ·) (fun s ↦ ∑ j ∈ Finset.univ.erase i, g j s) :=
      sum_isBoundedUnder_ge g (Finset.univ.erase i) (fun j _ ↦ hbelow j)
    obtain ⟨b, hb⟩ := hrestge.eventually_ge
    refine isBoundedUnder_of_eventually_le (a := a - b) ?_
    filter_upwards [ha, hb] with s hsa hsb
    rw [hdecomp s]; linarith
  haveI : Nonempty ι := ⟨i₀⟩
  have hNpos : 0 < N := Fintype.card_pos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  set t : Finset ι := Finset.univ.erase i₀ with ht
  have hrestge : l.IsBoundedUnder (· ≥ ·) (fun s ↦ ∑ j ∈ t, g j s) :=
    sum_isBoundedUnder_ge g t (fun j _ ↦ hbelow j)
  have hrestle : l.IsBoundedUnder (· ≤ ·) (fun s ↦ ∑ j ∈ t, g j s) :=
    sum_isBoundedUnder_le g t (fun j _ ↦ hgle j)
  have hcard : t.card = N - 1 := Finset.card_erase_of_mem (Finset.mem_univ i₀)
  have hliminf_rest : ((N : ℝ) - 1) / N ≤ liminf (fun s ↦ ∑ j ∈ t, g j s) l := by
    have hsuper : ∑ j ∈ t, liminf (g j) l ≤ liminf (fun s ↦ ∑ j ∈ t, g j s) l :=
      sum_liminf_le_liminf_sum g t (fun j _ ↦ hbelow j) (fun j _ ↦ hgle j)
    have hlb : ∑ j ∈ t, ((N : ℝ))⁻¹ ≤ ∑ j ∈ t, liminf (g j) l :=
      Finset.sum_le_sum (fun j _ ↦ hlo j)
    have hconst : ∑ _j ∈ t, ((N : ℝ))⁻¹ = (t.card : ℝ) * (N : ℝ)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst, hcard] at hlb
    have hcast : ((N : ℝ) - 1) / N = ((N - 1 : ℕ) : ℝ) * (N : ℝ)⁻¹ := by
      have hsub : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        have : (1 : ℕ) ≤ N := hNpos
        push_cast [Nat.cast_sub this]; ring
      rw [hsub]; ring
    rw [hcast]
    exact le_trans hlb hsuper
  have hFeq : (fun s ↦ g i₀ s + ∑ j ∈ t, g j s) = F := by
    funext s
    rw [hF]
    exact Finset.add_sum_erase Finset.univ (fun j ↦ g j s) (Finset.mem_univ i₀)
  have hadd : limsup (g i₀) l + liminf (fun s ↦ ∑ j ∈ t, g j s) l
      ≤ limsup (fun s ↦ g i₀ s + ∑ j ∈ t, g j s) l :=
    le_limsup_add (hgle i₀) (IsBoundedUnder.isCoboundedUnder_le (hbelow i₀)) hrestle hrestge
  rw [hFeq, hFlimsup] at hadd
  have hlimsup_le : limsup (g i₀) l ≤ (N : ℝ)⁻¹ := by
    have hrest_le : liminf (fun s ↦ ∑ j ∈ t, g j s) l ≤ 1 - limsup (g i₀) l := by linarith
    have h1 : limsup (g i₀) l ≤ 1 - ((N : ℝ) - 1) / N := by
      linarith [le_trans hliminf_rest hrest_le]
    have h2 : 1 - ((N : ℝ) - 1) / N = (N : ℝ)⁻¹ := by field_simp; ring
    rw [h2] at h1; exact h1
  exact tendsto_of_le_liminf_of_limsup_le (hlo i₀) hlimsup_le (hgle i₀) (hbelow i₀)

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
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ (𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal),
          𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt (𝓞 K) 𝔓) ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card Gal(L/K) : ℝ)⁻¹) := by
  simp only [HasDirichletDensity, Nat.card_eq_fintype_card]
  refine tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one
    (fun τ s ↦
      primeIdealZetaSum
          {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ (𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal),
              𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt (𝓞 K) 𝔓) ∧
            frobeniusClass K L 𝔭 = ConjClasses.mk τ} s
        / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
    (fun τ ↦ ?_) (fun τ ↦ ?_) (ratioSum_frobeniusFibres_tendsto_one K L) σ
  · simpa only [Nat.card_eq_fintype_card] using liminf_ratio_ge_inv_card_G K L τ
  -- each ratio of nonnegative Dirichlet sums is `≥ 0`, hence bounded below by `0`
  · have hzeta_nonneg : ∀ (S : Set (Ideal (𝓞 K))) (s : ℝ), 0 ≤ primeIdealZetaSum S s := by
      intro S s
      rw [primeIdealZetaSum_def]
      exact tsum_nonneg fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
    exact isBoundedUnder_of_eventually_ge (a := 0)
      (Filter.Eventually.of_forall fun s ↦ div_nonneg (hzeta_nonneg _ s) (hzeta_nonneg _ s))

/-- The lower-density bound `δ_inf ≥ |H_n|/(|G|·|H|)` from the full abelian
density, extracted via `HasDirichletDensity.hasLower`. -/
theorem chebotarev_abelian_lowerDensity_per_m
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) :
    HasLowerDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ (𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal),
          𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt (𝓞 K) 𝔓) ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card Gal(L/K) : ℝ)⁻¹) :=
  (chebotarev_abelian K L σ).hasLower

end Chebotarev
