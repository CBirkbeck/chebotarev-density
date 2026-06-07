module

public import CebotarevDensity.Cyclotomic
public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
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

/-- The Dirichlet density of a finite pairwise-disjoint union of sets, each of the
*same* density `c`, is `|t| • c`. Pure `Density.lean`-API assembly (induction on `t`
from `HasDirichletDensity.union_of_disjoint`), used to sum the `|H_n|` equal cyclotomic-
crossing fibre densities `1/(|G|·|H|)` in `liminf_density_S_sigma_ge_card_H_n_div_GH`. -/
private theorem hasDirichletDensity_biUnion_const {F : Type*} [Field F] [NumberField F]
    {ι : Type*} (t : Finset ι) (S : ι → Set (Ideal (𝓞 F))) (c : ℝ)
    (hdisj : (t : Set ι).PairwiseDisjoint S)
    (hdens : ∀ i ∈ t, HasDirichletDensity (S i) c) :
    HasDirichletDensity (⋃ i ∈ t, S i) ((t.card : ℝ) • c) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using hasDirichletDensity_empty (K := F)
  | insert a t ha ih =>
      have hdisj' : (t : Set ι).PairwiseDisjoint S :=
        hdisj.subset (Finset.coe_subset.mpr (Finset.subset_insert a t))
      have hdisjUnion : Disjoint (S a) (⋃ i ∈ t, S i) :=
        Set.disjoint_iUnion₂_right.2 fun i hi =>
          hdisj (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hi) fun h => ha (h ▸ hi)
      have hbase := hdens a (Finset.mem_insert_self a t)
      have hrec := ih hdisj' (fun i hi => hdens i (Finset.mem_insert_of_mem hi))
      have hcard : ((insert a t).card : ℝ) • c = c + (t.card : ℝ) • c := by
        rw [Finset.card_insert_of_notMem ha]; push_cast; ring
      rw [Finset.set_biUnion_insert, hcard]
      exact hbase.union_of_disjoint hdisjUnion hrec

/-! ### Cyclotomic-crossing core `exists_cyclotomicCrossing_fibres` (Sharifi 7.2.2 Step 2)

Sharifi 7.2.2 Step 2 cyclotomic-crossing core (p. 144). For `m ≥ 1` and `σ ∈ G`,
there is a family of prime sets `S_{σ,τ}` of `K` indexed by `τ ∈ H_n(m) =
{τ : (ℤ/mℤ)ˣ // |G| ∣ ord τ}`, pairwise disjoint, each contained in the Frobenius
fibre `S_σ`, and each of Dirichlet density exactly `1/(|G|·|H(m)|)` (with
`H(m) = (ℤ/mℤ)ˣ`).
This is the substantive geometric content of the crossing: introduce the compositum
`M = L(μ_m)` (`Gal(M/K) ≅ G × H` via the mod-`m` cyclotomic character, valid since `m`
coprime to `disc L` makes `L` and `K(μ_m)` linearly disjoint over `K`). For each such
`τ`, the subgroup `⟨(σ,τ)⟩` meets `G × {1}` trivially
(`cyclic_subgroup_meets_G_times_one_trivially`), so `M = F(μ_m)` with
`F = K(μ_m)^{⟨(σ,τ)⟩}`, making `M/F` cyclotomic; `chebotarev_cyclotomic` applied to
`M/F` at `(σ,τ)` together with the Step-1 cyclic reduction through `F/K` gives a set
`S_{σ,τ}` of primes of `K` with `Gal(M/K)`-Frobenius `(σ,τ)` of density
`1/(|G|·|H|)`. Such primes have `Gal(L/K)`-Frobenius the `G`-projection `σ`, so
`S_{σ,τ} ⊆ S_σ`; distinct `τ` give disjoint sets.

This existence statement isolates the compositum infrastructure (`Gal(L(μ_m)/K) ≅ G × H`
and the density transfer `F/K`) that is not yet available in mathlib/this project; the
`liminf` lower bound `liminf_density_S_sigma_ge_card_H_n_div_GH` is assembled sorry-free
around it (mirroring how the analytic gap is isolated in the cyclotomic case).

**Hypotheses.** The crossing is only valid at *admissible* `m`:
* `hcop : ((NumberField.discr L).natAbs).Coprime m` — coprimality of `m` to the
  discriminant of `L` is exactly what makes `L` and `K(μ_m)` linearly disjoint over `K`
  (`[K(μ_m):K] = φ(m)` and `Gal(L(μ_m)/K) ≅ G × (ZMod m)ˣ`): the intersection
  `L ∩ K(μ_m)` is unramified everywhere over `K` — the `K`-side via
  `NumberField.discr_dvd_discr` (a prime ramifying in `K(μ_m)` divides `m`, hence not
  `disc L`) and the `L`-side dually — so it is `K` itself (Minkowski).
* `hm4 : m % 4 ≠ 2` — fed verbatim into the downstream `chebotarev_cyclotomic` application
  (its `B2`-repaired signature carries this hypothesis ruling out the degenerate
  `m ≡ 2 mod 4` cyclotomic field).
As stated with `∀ m ≥ 1` the conclusion is false/unprovable at degenerate `m`; the
consumer `liminf_ratio_ge_inv_card_G` chooses `m` prime with `m ≡ 1 mod 4·|G|^k`, which
secures both hypotheses (`m % 4 = 1`; a prime exceeding `|disc L|` is coprime to it). -/
/-! #### Internal decomposition of `exists_cyclotomicCrossing_fibres`

The crossing's geometric content is isolated in the *tagged-family* master leaf
`exists_crossing_family_tagged` below: it produces the per-`τ` fibre sets `S_{σ,τ}` of `K`
*together with a single global tag* `t : Ideal (𝓞 K) → (ℤ/mℤ)ˣ` recording the
`H`-component of each prime's `Gal(M/K) = G × H`-Frobenius. The tag makes distinct-`τ` fibres
disjoint (a prime has one well-defined `M`-Frobenius), so `exists_cyclotomicCrossing_fibres`
reduces to that master leaf by a generic *distinct-tags ⟹ pairwise-disjoint* argument
(`pairwiseDisjoint_of_tag`), with no further geometry.

The master leaf is in turn intended to be discharged from the following five TRUE
infrastructure leaves (Sharifi 7.2.2 Step 2, p. 144), each independently attackable and
stated against the compositum `M = L(μ_m)` (carrier `CyclotomicField m L` with its
`K`-algebra/scalar-tower structure). They are pinned here as the decomposition targets:

* `cyclotomicField_finrank_eq` (C2a) — `[K(μ_m):K] = φ(m)` from `hcop` (the deep
  ramification/Minkowski input: a prime ramifying in `K(μ_m)` divides `m`, hence is coprime
  to `disc L`, so `K ∩ L = K` and `Gal(K(μ_m)/K) ≅ (ℤ/mℤ)ˣ` has full order `φ(m)`).
* `gal_compositum_prod_iso` (C1) — `Gal(M/K) ≅ G × Gal(M/L)` via the restriction-pair, the
  linear-disjointness `G × H` splitting (uses the degree count C2a / `hcop`).
* `compositum_isCyclotomic_over_fixedField` (C3) — for any `g ∈ Gal(M/K)` the fixed field
  `F = M^⟨g⟩` has `M/F` cyclotomic; applied at `g = (σ,τ)`, where the trivial meet
  `⟨(σ,τ)⟩ ∩ (G × {1}) = 1` (`cyclic_subgroup_meets_G_times_one_trivially`, needs
  `|G| ∣ ord τ`) gives `M = F(μ_m)`. **Gate-fix (2026-06-07):** the Lean encoding of
  `G × {1} = Gal(M/K(μ_m))` is `(IntermediateField.adjoin K {b | b^m=1}).fixingSubgroup`, NOT
  `ker(restrictNormalHom L)` (which is `{1} × H = Gal(M/L)`); see the C3 docstring for the
  necessity/sufficiency argument. The master leaf must supply the corrected gate.
* `frobeniusClass_proj` (C4) — a prime with `Gal(M/K)`-Frobenius `(σ,τ)` has
  `Gal(L/K)`-Frobenius the projection `σ` (restriction-compatibility of `frobeniusClass`,
  the `M/L/K`-tower analogue of `Main.arithFrobAt_restrictScalars_eq`; replicated in
  `Abelian` because `Main` imports `Abelian`).
* `density_lift_through_fixedField_repl` (C5) — the Step-1 cyclic density transfer through
  `F/K`, applied to `M/F` (so `chebotarev_cyclotomic` at `M/F` and `(σ,τ)`, density
  `1/|Gal(M/F)|` of primes of `F`, lifts to density `1/(|G|·|H|)` of primes of `K`). This is
  a verbatim replica of `Main.density_lift_through_fixedField` (stated for top field `M`):
  `Main` is below `Abelian` in the import DAG, so the lemma cannot be imported; the
  orchestrator should reconcile (move the shared statement to a common ancestor, or have
  `Main` re-export). `hm4` threads into the `chebotarev_cyclotomic` application; `hcop`
  threads into C1/C2a. -/

/-- Generic disjointness from a global tag: if every member of `S i` carries the same tag
`f i` under a single function `t`, and `f` is injective, the family `S` is pairwise disjoint.
Pure set-theory assembly used to derive `exists_cyclotomicCrossing_fibres` from the tagged
master leaf `exists_crossing_family_tagged`. -/
private theorem pairwiseDisjoint_of_tag {α ι κ : Type*} (t : α → κ) (f : ι → κ)
    (hf : Function.Injective f) (S : ι → Set α) (htag : ∀ i, ∀ a ∈ S i, t a = f i) :
    (Set.univ : Set ι).PairwiseDisjoint S := by
  intro i _ j _ hij
  simp only [Function.onFun, Set.disjoint_left]
  intro a hi hj
  exact hij (hf ((htag i a hi).symm.trans (htag j a hj)))

/-- **Cyclotomic-crossing tagged master leaf** (Sharifi 7.2.2 Step 2, p. 144). For admissible
`m` (`hm4 : m % 4 ≠ 2`, `hcop : (disc L).natAbs.Coprime m`) and `σ ∈ G = Gal(L/K)`, there is a
single global tag `t : Ideal (𝓞 K) → (ℤ/mℤ)ˣ` — the `H`-component of the prime's
`Gal(M/K) = G × H`-Frobenius, `M = L(μ_m)` — and a family of prime sets `S_{σ,τ}` indexed by
`τ ∈ H_n = {τ : |G| ∣ ord τ}` such that:
* each `S_{σ,τ}` lies in the `σ`-Frobenius fibre of `K` (`frobeniusClass_proj`, C4);
* every prime of `S_{σ,τ}` has tag exactly `τ` (its `M`-Frobenius `H`-component);
* each `S_{σ,τ}` has Dirichlet density `1/(|G|·|H|)` (`chebotarev_cyclotomic` at `M/F` with
  `F = M^⟨(σ,τ)⟩`, C3, lifted through `F/K` by `density_lift_through_fixedField_repl`, C5).

The global tag makes the distinct-`τ` fibres disjoint (`pairwiseDisjoint_of_tag`), which is the
only extra fact `exists_cyclotomicCrossing_fibres` needs on top of this leaf.

This packages the compositum infrastructure (`gal_compositum_prod_iso` (C1),
`cyclotomicField_finrank_eq` (C2a)) and the per-`τ` density chain (C3/C4/C5); see the
decomposition note above. `hm4`/`hcop` are threaded verbatim into those leaves. -/
private theorem exists_crossing_family_tagged
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) (m : ℕ) (_hm : 1 ≤ m)
    (hm4 : m % 4 ≠ 2) (hcop : ((NumberField.discr L).natAbs).Coprime m) :
    ∃ (t : Ideal (𝓞 K) → (ZMod m)ˣ)
      (S : {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} → Set (Ideal (𝓞 K))),
      (∀ τ, S τ ⊆ {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
          frobeniusClass K L 𝔭 = ConjClasses.mk σ}) ∧
      (∀ τ, ∀ 𝔭 ∈ S τ, t 𝔭 = (τ : (ZMod m)ˣ)) ∧
      (∀ τ, HasDirichletDensity (S τ)
          ((Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ) : ℝ)⁻¹)) := by
  sorry

/-! #### Infrastructure leaves for `exists_crossing_family_tagged` (C1–C5)

The five TRUE, independently-attackable leaves the master leaf composes (Sharifi 7.2.2 Step 2,
p. 144), stated against the compositum `M = L(μ_m)`. Recommended carrier: `CyclotomicField m L`
(it carries `[IsCyclotomicExtension {m} L M]`, `[NumberField M]`, `[FiniteDimensional L M]`
automatically; its `K`-algebra/scalar-tower structure comes from `RingHom.comp` /
`IsScalarTower.of_algebraMap_eq`). The leaves below abstract `M` as a hypothesis with the
relevant instance binders so they do not depend on that carrier choice. -/

/-- **C2a-ramif — primes ramifying in a rational cyclotomic field divide `m`.** A prime `p`
dividing the discriminant of an `{m}`-cyclotomic extension `E/ℚ` necessarily divides `m`: for
`p ∤ m` every prime `P` of `𝓞 E` over `p` is unramified
(`IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd` gives `e = 1`, lifted to
`Algebra.IsUnramifiedAt` via `isUnramifiedAt_iff_of_isDedekindDomain`), so by
`not_dvd_discr_iff_forall_mem` we get `p ∤ discr E`. -/
private theorem prime_dvd_natAbs_discr_cyclotomic_dvd
    (E : Type*) [Field E] [NumberField E] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} ℚ E]
    {p : ℕ} (hp : p.Prime) (hpd : p ∣ (NumberField.discr E).natAbs) : p ∣ m := by
  by_contra hpm
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpd' : (p : ℤ) ∣ NumberField.discr E := Int.ofNat_dvd_left.mpr hpd
  refine absurd hpd' ?_
  rw [NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hpprime]
  intro P hP hmem
  haveI hPp : P.IsPrime := hP
  -- `P` lies over the rational prime `p`: its contraction to `ℤ` is `span {p}`.
  have hunder : Ideal.under ℤ P = Ideal.span {(p : ℤ)} := by
    haveI hUP : (Ideal.under ℤ P).IsPrime := inferInstance
    have hmem' : (p : ℤ) ∈ Ideal.under ℤ P := by rw [Ideal.mem_under]; simpa using hmem
    have hspan_le : Ideal.span {(p : ℤ)} ≤ Ideal.under ℤ P := by
      rw [Ideal.span_le]; simpa using hmem'
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    exact (hmax.eq_of_le hUP.ne_top hspan_le).symm
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mem_bot] at hmem
    have hne : ((p : ℤ) : 𝓞 E) ≠ 0 := by
      simp only [ne_eq, Int.cast_natCast, Nat.cast_eq_zero]; exact hp.pos.ne'
    exact hne hmem
  -- Unramifiedness reduces to ramification index `1`, which the cyclotomic
  -- theory supplies for any prime not dividing `m`.
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := ℤ) (S := 𝓞 E) hPbot, hunder]
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨by rw [← hunder]⟩
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p E P hpm

/-- **C2a — cyclotomic degree over the base** (the deep ramification/Minkowski leaf). Source
(Sharifi p. 144): "Choose `m` not dividing the discriminant of `L` so that
`H = Gal(L(μ_m)/L) ≅ (ℤ/mℤ)ˣ` … and `Gal(L(μ_m)/K) ≅ G × H`." The full order `φ(m)`
of `H = (ℤ/mℤ)ˣ` is exactly `[K(μ_m):K] = φ(m)`, equivalently irreducibility of the `m`-th
cyclotomic polynomial over `K`; this holds because `m` is coprime to `disc L` (`hcop`): a
prime ramifying in `K(μ_m)` divides `m`, hence does not divide `disc L`, so `K ∩ L` is
unramified everywhere over `K` and equals `K` (Minkowski / `NumberField.discr_dvd_discr`),
giving linear disjointness of `L` and `K(μ_m)`. **This is the isolated deep leaf.** -/
private theorem cyclotomicField_finrank_eq
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K M]
    (hcop : ((NumberField.discr K).natAbs).Coprime m) :
    Module.finrank K M = m.totient := by
  -- A primitive `m`-th root of unity in `M`.
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) K M
    (Set.mem_singleton m) (NeZero.ne m)
  -- The cyclotomic copy `K₁ = ℚ(ζ)` and the base copy `K₂ = image of K`, as intermediate
  -- fields of `M` over `ℚ`.
  set K₁ : IntermediateField ℚ M := IntermediateField.adjoin ℚ {ζ} with hK₁def
  set K₂ : IntermediateField ℚ M := (IsScalarTower.toAlgHom ℚ K M).fieldRange with hK₂def
  haveI hK₁cyc : IsCyclotomicExtension {m} ℚ K₁ :=
    hζ.intermediateField_adjoin_isCyclotomicExtension (K := ℚ)
  haveI : IsGalois ℚ K₁ := IsCyclotomicExtension.isGalois (S := {m}) (K := ℚ) (L := K₁)
  have hfinK₁ : Module.finrank ℚ K₁ = m.totient :=
    IsCyclotomicExtension.finrank K₁ (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))
  -- `K₁ ⊔ K₂ = ⊤`: the compositum is generated over `ℚ` by `ζ` and the image of `K`,
  -- and `M = K(ζ)` is generated over `K` by `ζ` alone.
  have hsup : K₁ ⊔ K₂ = ⊤ := by
    have hζalg : IsAlgebraic ℚ ζ := Algebra.IsAlgebraic.isAlgebraic ζ
    have hsubalg : (IsScalarTower.toAlgHom ℚ K M).range ⊔ Algebra.adjoin ℚ {ζ}
        = (⊤ : Subalgebra ℚ M) := by
      have htop : (Algebra.adjoin K {ζ} : Subalgebra K M) = ⊤ :=
        IsCyclotomicExtension.adjoin_primitive_root_eq_top (n := m) hζ
      rw [← Algebra.Subalgebra.restrictScalars_adjoin (R := ℚ) (S := K) (s := {ζ}), htop,
        Subalgebra.restrictScalars_top]
    apply IntermediateField.toSubalgebra_injective
    rw [hK₁def, hK₂def, IntermediateField.sup_toSubalgebra_of_isAlgebraic_left,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζalg,
      AlgHom.fieldRange_toSubalgebra, IntermediateField.top_toSubalgebra, sup_comm]
    exact hsubalg
  -- The ring isomorphism `K ≃+* K₂` restricting `algebraMap K M` to its field range.
  let eK₂ : K ≃+* K₂ := ((IsScalarTower.toAlgHom ℚ K M : K →+* M)).rangeRestrictFieldEquiv
  -- `discr K₂ = discr K` since `K ≃+* K₂`.
  have hdiscrK₂ : NumberField.discr K₂ = NumberField.discr K :=
    (NumberField.discr_eq_discr_of_ringEquiv (f := eK₂)).symm
  -- The deep input: `discr K₁` (ramified only at primes dividing `m`) is coprime to `discr K`.
  have hcoprime : IsCoprime (NumberField.discr K₁) (NumberField.discr K₂) := by
    rw [hdiscrK₂, Int.isCoprime_iff_gcd_eq_one, Int.gcd]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    rw [Nat.dvd_gcd_iff] at hpdvd
    obtain ⟨hpa, hpb⟩ := hpdvd
    have hpm : p ∣ m := prime_dvd_natAbs_discr_cyclotomic_dvd K₁ m hp hpa
    have hpgcd : p ∣ Nat.gcd (NumberField.discr K).natAbs m := Nat.dvd_gcd hpb hpm
    rw [hcop] at hpgcd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpgcd)
  -- Linear disjointness of the cyclotomic copy and the base copy over `ℚ`.
  have hld : K₁.LinearDisjoint K₂ :=
    NumberField.linearDisjoint_of_isGalois_isCoprime_discr (L := M) K₁ K₂ hcoprime
  have hfr : Module.finrank K₂ M = Module.finrank ℚ K₁ :=
    hld.finrank_right_eq_finrank hsup
  -- Relabel `finrank K M = finrank K₂ M` along `K ≃+* K₂`.
  have hrelabel : Module.finrank K M = Module.finrank K₂ M := by
    refine Algebra.finrank_eq_of_equiv_equiv eK₂ (RingEquiv.refl M) ?_
    ext x
    change ((eK₂ x : M)) = (IsScalarTower.toAlgHom ℚ K M : K →+* M) x
    rfl
  rw [hrelabel, hfr, hfinK₁]

/-- **C1 — the `G × H` splitting of the compositum** (Sharifi p. 144):
`Gal(M/K) ≅ G × Gal(M/L)`
with `G = Gal(L/K)`, where `M = L(μ_m)`. The isomorphism is the restriction-pair
`α ↦ (α.restrictScalars K on L, α on M/L)`; it is injective because `L` and `K(μ_m)` are
linearly disjoint over `K` and surjective by the degree count
`[M:K] = [L:K]·φ(m) = [L:K]·[M:L]` (which uses `cyclotomicField_finrank_eq`, hence `hcop`).
Here `Gal(M/L) ≅ H = (ℤ/mℤ)ˣ` via the mod-`m` cyclotomic character. -/
private theorem gal_compositum_prod_iso
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]
    (_hcop : ((NumberField.discr L).natAbs).Coprime m) :
    Nonempty (Gal(M/K) ≃* (Gal(L/K) × Gal(M/L))) :=
  sorry

/-- **C3 — the compositum is cyclotomic over the `(σ,τ)`-fixed field** (Sharifi p. 144):
"… `L(μ_m)` is given by adjoining `μ_m` to `F = K(μ_m)^⟨(σ,τ)⟩`", i.e. `M = F(μ_m)`.
Stated for `g ∈ Gal(M/K)` and `F = M^⟨g⟩`: then `M/F` is the `m`-th cyclotomic extension.

**Gate correction (statement-fix, 2026-06-07).** The decomposition originally gated this leaf
by `⟨g⟩ ⊓ ker(restrictNormalHom L) = ⊥`. That is FALSE-as-stated: `ker(restrictNormalHom L)`
is `Gal(M/L) = {1} × H` (the `L`-fixers), whereas Sharifi's `⟨(σ,τ)⟩ ∩ (G × {1}) = 1` is about
`G × {1} = Gal(M/K(μ_m))`, the `μ_m`-fixers. Concretely with `g = (σ,τ)`: the *stated* meet
`⟨g⟩ ⊓ ({1}×H)` is trivial iff `ord τ ∣ ord σ`, which `|G| ∣ ord τ` does NOT give; the
*correct* meet `⟨g⟩ ⊓ (G×{1})` is trivial iff `ord σ ∣ ord τ`, which `ord σ ∣ |G| ∣ ord τ`
DOES give (matching `cyclic_subgroup_meets_G_times_one_trivially`). Moreover `M = F(μ_m)`
needs exactly `⟨g⟩ ⊓ Gal(M/K(μ_m)) = ⊥` (it is necessary and sufficient: `M = F ⊔ K(μ_m)`
⟺ `fixingSubgroup(F ⊔ K(μ_m)) = ⊥` ⟺ `⟨g⟩ ⊓ K(μ_m).fixingSubgroup = ⊥`). The hypothesis is
therefore corrected to `⟨g⟩ ⊓ (adjoin K μ_m).fixingSubgroup = ⊥`, where
`adjoin K {b | b^m = 1} = K(μ_m)` is the cyclotomic subfield (its fixing subgroup is
`Gal(M/K(μ_m)) = G × {1}`). The master-leaf assembly (`exists_crossing_family_tagged`) must
supply this corrected gate at `g = (σ,τ)`: from `|G| ∣ ord τ` via
`cyclic_subgroup_meets_G_times_one_trivially` transported across the `Gal(M/K) ≅ G × H`
splitting (C1) so that `G × {1}` is identified with `(adjoin K μ_m).fixingSubgroup`.

Proof: a primitive root `ζ ∈ M` exists (from `[IsCyclotomicExtension {m} L M]`);
`adjoin K {ζ} = adjoin K {b | b^m=1} = K(μ_m)`; the corrected meet gives `F ⊔ K(μ_m) = ⊤`
(`fixingSubgroup_sup` + `fixingSubgroup_fixedField` + the Galois correspondence
`fixedField_fixingSubgroup`); hence `adjoin F {ζ} = ⊤` over `F` (`restrictScalars_adjoin_eq_sup`),
and `adjoin F {ζ}` is `{m}`-cyclotomic over `F`
(`IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`), transported to `M` along
`adjoin F {ζ} = ⊤ ≃ₐ M` (`IsCyclotomicExtension.equiv`, `IntermediateField.topEquiv`).
`[IsCyclotomicExtension {m} L M]` guarantees `μ_m ⊆ M` so the adjunction makes sense. -/
private theorem compositum_isCyclotomic_over_fixedField
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]
    (g : Gal(M/K))
    (_hmeet : Subgroup.zpowers g ⊓
      (IntermediateField.adjoin K {b : M | b ^ m = 1}).fixingSubgroup = ⊥) :
    letI := (IntermediateField.fixedField (Subgroup.zpowers g)).isScalarTower_mid'
    IsCyclotomicExtension {m} ↥(IntermediateField.fixedField (Subgroup.zpowers g)) M := by
  set F : IntermediateField K M := IntermediateField.fixedField (Subgroup.zpowers g) with hF
  set Kμ : IntermediateField K M := IntermediateField.adjoin K {b : M | b ^ m = 1} with hKμ
  -- a primitive `m`-th root `ζ ∈ M` (from the `L`-cyclotomic structure on `M`).
  obtain ⟨ζ, hζ⟩ : ∃ r : M, IsPrimitiveRoot r m :=
    IsCyclotomicExtension.exists_isPrimitiveRoot (S := {m}) L M (Set.mem_singleton m) (NeZero.ne m)
  -- `adjoin K {ζ} = Kμ` (the roots of unity are exactly the powers of `ζ`).
  have hadjζ : IntermediateField.adjoin K {ζ} = Kμ := by
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      intro x hx
      rw [Set.mem_singleton_iff] at hx; subst hx
      exact IntermediateField.subset_adjoin K _ hζ.pow_eq_one
    · apply IntermediateField.adjoin_le_iff.mpr
      intro x hx
      obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one (Set.mem_setOf_eq ▸ hx)
      exact pow_mem (IntermediateField.subset_adjoin K _ (Set.mem_singleton ζ)) i
  -- `F ⊔ Kμ = ⊤` via the Galois correspondence and the (corrected) meet hypothesis.
  have hsup : (F ⊔ Kμ).fixingSubgroup = ⊥ := by
    rw [IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_fixedField, _hmeet]
  have htop : F ⊔ Kμ = ⊤ := by
    have := congrArg IntermediateField.fixedField hsup
    rwa [IsGalois.fixedField_fixingSubgroup, IntermediateField.fixedField_bot] at this
  -- transport to `adjoin F {ζ} = ⊤` (over `F`), via `restrictScalars`.
  have htopF : IntermediateField.adjoin (↥F) {ζ} = ⊤ := by
    apply IntermediateField.restrictScalars_injective K
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, hadjζ, htop]
    rfl
  -- `adjoin F {ζ}` is `{m}`-cyclotomic over `F`; transport along `adjoin F {ζ} = ⊤ ≅ M`.
  haveI : Algebra.IsIntegral ↥F M := Algebra.IsIntegral.of_finite ↥F M
  haveI hcyc : IsCyclotomicExtension {m} ↥F (IntermediateField.adjoin (↥F) {ζ}) :=
    IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (K := ↥F) hζ
  rw [htopF] at hcyc
  exact IsCyclotomicExtension.equiv (S := {m}) (A := ↥F) (f := IntermediateField.topEquiv)

/-- **Action intertwining for the downward normal restriction** (replica of
`CyclotomicNormResidue.smul_algebraMap_eq`, adapted to the abstract tower `K ⊆ L ⊆ M` with
`M` on top). The embedding `𝓞 L → 𝓞 M` intertwines the action of `σ : Gal(M/K)` with that of
its normal restriction `σ ↾ L : Gal(L/K)`:
`σ • algebraMap (𝓞 L) (𝓞 M) y = algebraMap (𝓞 L) (𝓞 M) (σ↾L • y)`. The CNR original is
`private`, hence unreachable here; replicated `_repl`. -/
private theorem smul_algebraMap_eq_repl
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (σ : Gal(M/K)) (y : 𝓞 L) :
    σ • (algebraMap (𝓞 L) (𝓞 M) y) = algebraMap (𝓞 L) (𝓞 M) ((σ.restrictNormal L) • y) := by
  haveI : IsScalarTower (𝓞 K) (𝓞 L) (𝓞 M) := inferInstance
  have hbridgeM : ∀ (g : M ≃ₐ[K] M) (x : 𝓞 M), ((g • x : 𝓞 M) : M) = g • (x : M) := fun g x =>
    by simpa [Algebra.smul_def] using
      (smul_distrib_smul (G := M ≃ₐ[K] M) (R := 𝓞 M) (S := M) g x 1).symm
  have hbridgeL : ∀ (g : L ≃ₐ[K] L) (z : 𝓞 L), ((g • z : 𝓞 L) : L) = g • ((z : L)) := fun g z =>
    by simpa [Algebra.smul_def] using
      (smul_distrib_smul (G := L ≃ₐ[K] L) (R := 𝓞 L) (S := L) g z 1).symm
  have hcoe : ∀ z : 𝓞 L, ((algebraMap (𝓞 L) (𝓞 M) z : 𝓞 M) : M) = algebraMap L M (z : L) :=
    fun z => by
      rw [show ((algebraMap (𝓞 L) (𝓞 M) z : 𝓞 M) : M)
            = algebraMap (𝓞 M) M (algebraMap (𝓞 L) (𝓞 M) z) from rfl,
        ← IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 M) M,
        show ((z : L)) = algebraMap (𝓞 L) L z from rfl,
        ← IsScalarTower.algebraMap_apply (𝓞 L) L M]
  rw [RingOfIntegers.ext_iff]
  rw [hbridgeM, hcoe y, hcoe ((σ.restrictNormal L) • y), hbridgeL, AlgEquiv.smul_def,
    AlgEquiv.smul_def, AlgEquiv.restrictNormal_commutes]

/-- **Downward Frobenius restriction** (replica of
`CyclotomicNormResidue.isArithFrobAt_restrictNormal`
for the tower `K ⊆ L ⊆ M`). If `σ : Gal(M/K)` is an arithmetic Frobenius at a prime `𝔓` of `𝓞 M`,
its normal restriction `σ ↾ L` is an arithmetic Frobenius at `𝔮 = 𝔓 ∩ 𝓞 L`. The defining
congruence descends along `𝓞 L → 𝓞 M` via `smul_algebraMap_eq_repl` and `Ideal.under_under`. -/
private theorem isArithFrobAt_restrictNormal_repl
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (σ : Gal(M/K)) (𝔓 : Ideal (𝓞 M))
    (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) :
    IsArithFrobAt (𝓞 K) (σ.restrictNormal L) (𝔓.under (𝓞 L)) := by
  haveI : IsScalarTower (𝓞 K) (𝓞 L) (𝓞 M) := inferInstance
  have hunder : (𝔓.under (𝓞 L)).under (𝓞 K) = 𝔓.under (𝓞 K) := Ideal.under_under 𝔓
  intro y
  rw [hunder, Ideal.under, Ideal.mem_comap, map_sub, map_pow]
  rw [show (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) (σ.restrictNormal L)) y
        = (σ.restrictNormal L) • y from rfl, ← smul_algebraMap_eq_repl K L M σ y]
  exact hσ (algebraMap (𝓞 L) (𝓞 M) y)

/-- **C4 — Frobenius projects along the compositum tower** `M/L/K`. A prime `𝔭` of `K`
unramified in `M` (hence in `L`) whose `Gal(M/K)`-Frobenius class is `(σ,τ)` — i.e. equal to
`ConjClasses.mk τM` for `τM` restricting to `σ` over `L` — has `Gal(L/K)`-Frobenius class `σ`.
This is the restriction-compatibility of `frobeniusClass` along `K ⊆ L ⊆ M`, the tower
analogue of `Main.arithFrobAt_restrictScalars_eq` (replicated in `Abelian` because `Main`
imports `Abelian`). It is what makes each crossing fibre `S_{σ,τ}` land inside the
`σ`-Frobenius fibre `S_σ`. Proof: pick `𝔓 ∣ 𝔭` in `𝓞 M`, set `σM = arithFrobAt 𝔓`; then
`IsConj σM τM` (both represent `frobeniusClass K M 𝔭`); `σM ↾ L` is an `L`-Frobenius at
`𝔓 ∩ 𝓞 L` (`isArithFrobAt_restrictNormal_repl`), so `frobeniusClass K L 𝔭 = mk (σM ↾ L)`; and
conjugacy descends through the hom `restrictNormalHom L` (`MonoidHom.map_isConj`), with
`restrictNormalHom L τM = σ`. -/
private theorem frobeniusClass_proj
    (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M]
    (σ : Gal(L/K)) (τM : Gal(M/K)) (_hτM : AlgEquiv.restrictNormalHom L τM = σ)
    (𝔭 : Ideal (𝓞 K)) (_hunrM : UnramifiedIn K M 𝔭) (_hunrL : UnramifiedIn K L 𝔭)
    (_hfr : frobeniusClass K M 𝔭 = ConjClasses.mk τM) :
    frobeniusClass K L 𝔭 = ConjClasses.mk σ := by
  by_cases hp : 𝔭.IsPrime
  · haveI := hp
    obtain ⟨𝔓, h𝔓p, h𝔓lo, -⟩ := exists_prime_liesOver K M 𝔭 (UnramifiedIn.ne_bot K M _hunrM)
    haveI := h𝔓p
    haveI := h𝔓lo
    haveI : Finite (𝓞 M ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
      (ne_bot_of_ramificationIdx_eq_one K M (UnramifiedIn.ramificationIdx_eq_one K M _hunrM 𝔓 h𝔓lo))
    set σM : Gal(M/K) := arithFrobAt (𝓞 K) Gal(M/K) 𝔓 with hσM
    have hMfrobσM : IsArithFrobAt (𝓞 K) σM 𝔓 := IsArithFrobAt.arithFrobAt (𝓞 K) Gal(M/K) 𝔓
    have hMclass : frobeniusClass K M 𝔭 = ConjClasses.mk σM :=
      frobeniusClass_eq_mk_of_isArithFrobAt K M 𝔭 _hunrM σM 𝔓 hMfrobσM h𝔓lo
    have hconjM : IsConj σM τM :=
      ConjClasses.mk_eq_mk_iff_isConj.mp (hMclass.symm.trans _hfr)
    have hLfrob : IsArithFrobAt (𝓞 K) (σM.restrictNormal L) (𝔓.under (𝓞 L)) :=
      isArithFrobAt_restrictNormal_repl K L M σM 𝔓 hMfrobσM
    haveI : (𝔓.under (𝓞 L)).IsPrime := Ideal.IsPrime.under (𝓞 L) 𝔓
    haveI : (𝔓.under (𝓞 L)).LiesOver 𝔭 :=
      ⟨(Ideal.under_under 𝔓).trans h𝔓lo.over.symm |>.symm⟩
    have hLclass : frobeniusClass K L 𝔭 = ConjClasses.mk (σM.restrictNormal L) :=
      frobeniusClass_eq_mk_of_isArithFrobAt K L 𝔭 _hunrL (σM.restrictNormal L) (𝔓.under (𝓞 L))
        hLfrob inferInstance
    rw [hLclass]
    have hconjL : IsConj (AlgEquiv.restrictNormalHom L σM) (AlgEquiv.restrictNormalHom L τM) :=
      MonoidHom.map_isConj _ hconjM
    rw [_hτM] at hconjL
    have hrn : σM.restrictNormal L = AlgEquiv.restrictNormalHom L σM := rfl
    rw [hrn]
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr hconjL
  · have hMjunk : frobeniusClass K M 𝔭 = ConjClasses.mk 1 := by
      rw [frobeniusClass, dif_neg (fun h => hp h.1)]
    have hLjunk : frobeniusClass K L 𝔭 = ConjClasses.mk 1 := by
      rw [frobeniusClass, dif_neg (fun h => hp h.1)]
    have hconj : IsConj (1 : Gal(M/K)) τM :=
      ConjClasses.mk_eq_mk_iff_isConj.mp (hMjunk.symm.trans _hfr)
    have hτM1 : τM = 1 := isConj_one_right.mp hconj
    have hσ1 : σ = 1 := by rw [← _hτM, hτM1, map_one]
    rw [hLjunk, hσ1]

/-- **C5 — density transfer through a fixed field** (Sharifi 7.2.2 Step 2 ⇒ Step 1 reuse,
p. 143–144). A verbatim replica of `Main.density_lift_through_fixedField`, restated with the
top field `M` (the compositum), so that the crossing can be assembled inside `Abelian`:
`Main` is *below* `Abelian` in the import DAG (`Main` imports `Abelian`), so the original
cannot be imported here. Given `σM ∈ Gal(M/K)`, the fixed field `E = M^⟨σM⟩`, a lift `σE`
`σM` to `Gal(M/E)`, and the cyclic-case density `1/|Gal(M/E)|` of the `σE`-Frobenius fibre of
`E`, the transfer yields density `|C|/|Gal(M/K)|` of the `σM`-Frobenius fibre of `K`. In the
crossing, `σM = (σ,τ)`, `E = F`, and `chebotarev_cyclotomic` (at the cyclotomic `M/F`, valid by
`hm4`) supplies the `_hab` input; the resulting density is `1/(|G|·|H|)`.
**Orchestrator note (enriched 2026-06-07).** This duplicates the *proven*
`Main.density_lift_through_fixedField` (Main.lean ~1152), available only by `L ↦ M` renaming.
A naive in-file replica is NOT a "small port": the proof transitively pulls in the ENTIRE
Step-1 reduction of `Main.lean` — ~18 declarations, ~1050 lines — none of which is importable
(`Main` imports `Abelian`):
  * public-form (already `(K L)`-explicit, copy verbatim with `L ↦ M`):
    `frobeniusFibre_card_eq_of_isConj`, `card_primesAbove_eq_card_carrier_mul_frobeniusFibre`,
    `count_frobenius_eq_sigma_mul_card_carrier`, `count_primes_above_with_frobenius_eq_sigma`,
    `arithFrobAt_restrictScalars_eq`;
  * private (suffix `_repl`): `univ_ratio_E_K_tendsto_one`,
    `stabilizer_intermediate_eq_top_of_frobenius`, `inertiaDeg_under_E_eq_one_of_frobenius`,
    `eq_of_liesOver_under_E_of_frobenius`, `arithFrobAt_E_eq_of_isArithFrobAt`,
    `card_fibre_E_eq_card_fibre_L`, `frobeniusClass_under_eq_of_mem_fibre`,
    `primeIdealZetaSum_fibre_eq_smul`, `tsum_comp_le_card_fibre_mul`,
    `primeIdealZetaSum_degTwo_le`, `ramifiedBelow_finite`,
    `primeIdealZetaSum_T2_div_univ_tendsto_zero`, and the lemma itself.
**Key structural finding:** that entire chain is *Abelian-independent* — `Main`'s only use of
`Abelian` is `chebotarev_abelian` (Main.lean:1289, inside `chebotarev_density`, AFTER all the
Step-1 helpers). So the CLEAN orchestrator fix (requires editing `Main`, which this agent does
NOT own) is to MOVE `density_lift_through_fixedField` + its Step-1 dependency block to a module
strictly below `Abelian` (a new `CebotarevDensity/FixedFieldTransfer.lean` imported by both, or
relocate into `Frobenius`), then DELETE this replica and have the master leaf call the shared
lemma. Left `sorry` here rather than duplicate ~1050 verified lines unverifiably (the project
`lake build` was concurrently broken in `ForMathlib/IdealCongruenceCount.lean`). -/
private theorem density_lift_through_fixedField_repl
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    [FiniteDimensional K M] (σM : Gal(M/K)) (E : IntermediateField K M) (σE : Gal(M/E))
    (_hσE : letI : IsScalarTower K ↥E M := E.isScalarTower_mid'; σE.restrictScalars K = σM)
    (_hEfix : E = IntermediateField.fixedField (Subgroup.zpowers σM))
    (_hab : HasDirichletDensity
        {P : Ideal (𝓞 ↥E) | P.IsPrime ∧ UnramifiedIn ↥E M P ∧
          frobeniusClass ↥E M P = ConjClasses.mk σE}
        ((Nat.card Gal(M/E) : ℝ)⁻¹)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K M 𝔭 ∧
        frobeniusClass K M 𝔭 = ConjClasses.mk σM}
      ((Nat.card (ConjClasses.mk σM).carrier : ℝ) / Nat.card Gal(M/K)) :=
  sorry

private theorem exists_cyclotomicCrossing_fibres
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) (m : ℕ) (hm : 1 ≤ m)
    (hm4 : m % 4 ≠ 2) (hcop : ((NumberField.discr L).natAbs).Coprime m) :
    ∃ S : {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} → Set (Ideal (𝓞 K)),
      (Set.univ : Set {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ}).PairwiseDisjoint S ∧
      (∀ τ, S τ ⊆ {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
          frobeniusClass K L 𝔭 = ConjClasses.mk σ}) ∧
      (∀ τ, HasDirichletDensity (S τ)
          ((Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ) : ℝ)⁻¹)) := by
  obtain ⟨t, S, hsub, htag, hd⟩ := exists_crossing_family_tagged K L σ m hm hm4 hcop
  -- Distinct `τ` give disjoint fibres because the global `M`-Frobenius tag separates them.
  refine ⟨S, pairwiseDisjoint_of_tag t (Subtype.val) Subtype.val_injective S htag, hsub, hd⟩

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
on the `liminf` of the density ratio for `S_σ` in `K`.

The crossing is only valid at *admissible* `m`, so this per-`m` bound carries the same
two hypotheses as `exists_cyclotomicCrossing_fibres`: `hm4 : m % 4 ≠ 2` (feeding the
repaired cyclotomic case) and `hcop : ((NumberField.discr L).natAbs).Coprime m` (the
linear-disjointness via the everywhere-unramified intersection / `discr_dvd_discr`). The
consumer `liminf_ratio_ge_inv_card_G` drives `m` along admissible primes. -/
theorem liminf_density_S_sigma_ge_card_H_n_div_GH
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) (m : ℕ) (_hm : 1 ≤ m)
    (hm4 : m % 4 ≠ 2) (hcop : ((NumberField.discr L).natAbs).Coprime m) :
    (Nat.card {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} : ℝ)
        / (Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ))
      ≤ Filter.liminf
          (fun s : ℝ ↦
            primeIdealZetaSum
                {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
                  frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
              / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
          (𝓝[>] 1) := by
  classical
  -- The Frobenius fibre `S_σ` and the crossing constant `c = 1/(|G|·|H|)`.
  set Sσ : Set (Ideal (𝓞 K)) :=
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = ConjClasses.mk σ}
    with hSσ
  set c : ℝ := (Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ) : ℝ)⁻¹ with hc
  -- The cyclotomic-crossing fibres (substantive content isolated in the sub-lemma).
  obtain ⟨S, hpd, hsub, hd⟩ := exists_cyclotomicCrossing_fibres K L σ m _hm hm4 hcop
  -- Index type `H_n(m)` is finite; work over its `Finset.univ`.
  have : Fintype {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} := Fintype.ofFinite _
  set t : Finset {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} := Finset.univ with ht
  -- The finite disjoint union of the fibres has density `|t| • c = |H_n|/(|G|·|H|)`.
  have hpd' : (t : Set {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ}).PairwiseDisjoint S := by
    rw [ht, Finset.coe_univ]; exact hpd
  have hUdens : HasDirichletDensity (⋃ i ∈ t, S i) ((t.card : ℝ) • c) :=
    hasDirichletDensity_biUnion_const t S c hpd' (fun i _ => hd i)
  -- The union sits inside `S_σ`, so its lower density bounds `liminf(P_{S_σ}/P_univ)`.
  have hUsub : (⋃ i ∈ t, S i) ⊆ Sσ := Set.iUnion₂_subset fun i _ => hsub i
  have hUlow : HasLowerDirichletDensity (⋃ i ∈ t, S i) ((t.card : ℝ) • c) := hUdens.hasLower
  have hSσlow : HasLowerDirichletDensity Sσ
      (Filter.liminf
        (fun s : ℝ ↦ primeIdealZetaSum Sσ s / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
        (𝓝[>] 1)) := rfl
  have hmono := HasLowerDirichletDensity.mono hUsub hUlow hSσlow
  -- Identify `|t| • c` with the goal's left-hand side `|H_n|/(|G|·|H|)`.
  have htcard : (t.card : ℝ) • c
      = (Nat.card {τ : (ZMod m)ˣ // Nat.card Gal(L/K) ∣ orderOf τ} : ℝ)
          / (Nat.card Gal(L/K) * Nat.card ((ZMod m)ˣ)) := by
    rw [ht, Finset.card_univ, hc, smul_eq_mul, ← Nat.card_eq_fintype_card, div_eq_mul_inv]
  rw [htcard] at hmono
  exact hmono

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

/-- Exponent-keyed per-prime bound — the generalisation of `perprime_bound` from the
specific group `(ZMod (n^k))ˣ` to *any* finite commutative group `G`, keyed on a
divisibility `p ^ a ∣ Monoid.exponent G` rather than on the Carmichael function of `n^k`.
The number of `x : G` with `p ^ v ∤ ord x`, times `p ^ (a - v - 1)`, is at most `|G|`.

Used at the admissible-prime sequence `m ≡ 1 (mod 4·n^k)` of `liminf_ratio_ge_inv_card_G`:
there `G = (ZMod m)ˣ` is cyclic of exponent `m - 1`, and `n^k ∣ m - 1`, so
`p ^ (k·v_p(n)) ∣ m - 1 = exponent`. The proof is `perprime_bound`'s, with the
`pk_dvd_carmichael` input replaced by the hypothesis `hdvd`. -/
private theorem perprime_bound_exp (G : Type*) [CommGroup G] [Finite G] (p a v : ℕ)
    (hp : p.Prime) (hv1 : 1 ≤ v) (hav : v ≤ a) (hdvd : p ^ a ∣ Monoid.exponent G) :
    Nat.card {x : G // ¬ p ^ v ∣ orderOf x} * p ^ (a - v - 1) ≤ Nat.card G := by
  classical
  set E := Monoid.exponent G with hE
  have hEne : E ≠ 0 := hE ▸ (Monoid.ExponentExists.of_finite (G := G)).exponent_ne_zero
  set M := ordCompl[p] E * p ^ (v - 1) with hM
  have hMne : M ≠ 0 := mul_ne_zero (Nat.ordCompl_pos p hEne).ne' (pow_ne_zero _ hp.ne_zero)
  have haE : a ≤ E.factorization p := (Nat.Prime.pow_dvd_iff_le_factorization hp hEne).mp hdvd
  have hle1 : v - 1 ≤ E.factorization p := by omega
  have hMdvdE : M ∣ E := M_dvd_E E p v hp hEne hle1
  have hgcd : Nat.gcd E M = M := Nat.gcd_eq_right hMdvdE
  have hEdivM : E / M = p ^ (E.factorization p - (v - 1)) :=
    Nat.div_eq_of_eq_mul_right (Nat.pos_of_ne_zero hMne) (E_eq_M_mul E p v hle1)
  have hbad_sub : Nat.card {x : G // ¬ p ^ v ∣ orderOf x} ≤ Nat.card {x : G // x ^ M = 1} := by
    refine bad_le_torsion G M p v (fun x hx => ?_)
    rw [← orderOf_dvd_iff_pow_eq_one]
    refine dvd_capped E (orderOf x) p v hp hEne ?_ ?_
    · rw [hE]; exact Monoid.order_dvd_exponent x
    · by_contra hcon
      push Not at hcon
      exact hx ((Nat.Prime.pow_dvd_iff_le_factorization hp (orderOf_pos x).ne').mpr (by omega))
  have hEM : p ^ (a - v - 1) ≤ E / M := by
    rw [hEdivM]; exact pow_le_pow_right₀ hp.one_le (by omega)
  calc Nat.card {x : G // ¬ p ^ v ∣ orderOf x} * p ^ (a - v - 1)
      ≤ Nat.card {x : G // x ^ M = 1} * p ^ (a - v - 1) := Nat.mul_le_mul_right _ hbad_sub
    _ ≤ Nat.card {x : G // x ^ M = 1} * (E / M) := Nat.mul_le_mul_left _ hEM
    _ = Nat.card {x : G // x ^ M = 1} * (E / Nat.gcd E M) := by rw [hgcd]
    _ ≤ Nat.card G := torsion_card_le G M

/-- Single-group form of the `H_n` ratio lower bound — the generalisation of (the per-`k`
step inside) `H_n_over_H_tends_to_one` to *any* finite commutative group `G` whose
exponent is divisible by `p ^ (k·v_p(n))` for every prime `p ∣ n`. Then
`|{τ : n ∣ ord τ}| / |G| ≥ 1 - Σ_{p ∣ n} 1/p^(k·v_p(n) - v_p(n) - 1)`. Used at the
admissible-prime sequence (`G = (ZMod m)ˣ`, exponent `m - 1`, `n^k ∣ m - 1`) to drive
the ratio to `1` by `k → ∞`. Built from `card_le_sum_card`, `exists_prime_pow_not_dvd`,
`ratio_bound` and the exponent-keyed `perprime_bound_exp`. -/
private theorem H_n_ratio_ge (G : Type*) [CommGroup G] [Finite G] (n k : ℕ) (hn2 : 2 ≤ n)
    (hk : 1 ≤ k)
    (hexp : ∀ p ∈ n.primeFactors, p ^ (k * n.factorization p) ∣ Monoid.exponent G) :
    1 - (∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ) ^ (k * n.factorization p - n.factorization p - 1))
      ≤ (Nat.card {τ : G // n ∣ orderOf τ} : ℝ) / Nat.card G := by
  classical
  set total : ℕ := Nat.card G with htotal
  set good : ℕ := Nat.card {τ : G // n ∣ orderOf τ} with hgood
  set bad : ℕ := Nat.card {τ : G // ¬ n ∣ orderOf τ} with hbad
  have htotpos : 0 < total := Nat.card_pos
  have hgb : good + bad = total := by
    have : Fintype G := Fintype.ofFinite G
    rw [hgood, hbad, htotal]
    simp only [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype_compl]
    have hle : Fintype.card {τ : G // n ∣ orderOf τ} ≤ Fintype.card G := Fintype.card_subtype_le _
    omega
  have hbadratio : (bad : ℝ) / total
      ≤ ∑ p ∈ n.primeFactors,
          (1 : ℝ) / (p : ℝ) ^ (k * n.factorization p - n.factorization p - 1) := by
    refine ratio_bound bad total n.primeFactors
      (fun p => Nat.card {τ : G // ¬ p ^ n.factorization p ∣ orderOf τ})
      (fun p => k * n.factorization p - n.factorization p - 1) (fun p => p)
      htotpos ?_ ?_ ?_
    · rw [hbad]
      refine card_le_sum_card n.primeFactors (fun τ => ¬ n ∣ orderOf τ)
        (fun p τ => ¬ p ^ n.factorization p ∣ orderOf τ) (fun τ hτ => ?_)
      exact exists_prime_pow_not_dvd n (orderOf τ) (by omega) (orderOf_pos τ).ne' hτ
    · exact fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
    · intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have hv1 : 1 ≤ n.factorization p := Nat.Prime.factorization_pos_of_dvd hpp (by omega) hpn
      have hav : n.factorization p ≤ k * n.factorization p := Nat.le_mul_of_pos_left _ hk
      exact perprime_bound_exp G p (k * n.factorization p) (n.factorization p) hpp hv1 hav
        (hexp p hp)
  have htk : (total : ℝ) ≠ 0 := by exact_mod_cast htotpos.ne'
  have heq : (good : ℝ) / total = 1 - (bad : ℝ) / total := by
    have hgbk : (good : ℝ) + (bad : ℝ) = (total : ℝ) := by exact_mod_cast hgb
    field_simp
    linarith [hgbk]
  rw [heq]
  linarith [hbadratio]

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
bound `liminf_density_S_sigma_ge_card_H_n_div_GH` as `m → ∞` along a sequence of
*admissible primes* `m_k ≡ 1 (mod 4·n^k)` with `m_k > |disc L|` (Dirichlet's theorem on
primes in arithmetic progression, `Nat.forall_exists_prime_gt_and_modEq`). Such `m_k`
satisfy both hypotheses of the per-`m` bound: `m_k % 4 = 1 ≠ 2`, and a prime exceeding
`|disc L|` is coprime to it. For prime `m_k`, the unit group `(ZMod m_k)ˣ` is cyclic of
exponent `m_k - 1`, and `n^k ∣ m_k - 1`, so `H_n_ratio_ge` gives
`|H_n|/|H| ≥ 1 - Σ_{p ∣ n} p^{-(k·v_p(n) - v_p(n) - 1)} → 1` as `k → ∞` (each summand
`→ 0` by `summand_tendsto`). This replaces the earlier `m = n^k` route, which is invalid
here because `n^k` need not be admissible. This is the lower half of Sharifi 7.2.2 Step 2
(p. 144). -/
theorem liminf_ratio_ge_inv_card_G
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [hAb : IsMulCommutative Gal(L/K)] (σ : Gal(L/K)) :
    (Nat.card Gal(L/K) : ℝ)⁻¹
      ≤ Filter.liminf
          (fun s : ℝ ↦
            primeIdealZetaSum
                {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
                  frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
              / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
          (𝓝[>] 1) := by
  classical
  set n : ℕ := Nat.card Gal(L/K) with hn
  set L_inf : ℝ :=
    Filter.liminf
      (fun s : ℝ ↦
        primeIdealZetaSum
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
      (𝓝[>] 1) with hLinf
  have hnpos : 0 < n := hn ▸ Nat.card_pos
  have hn1 : 1 ≤ n := hnpos
  -- The discriminant bound `dB = |disc L|`, which is positive.
  set dB : ℕ := (NumberField.discr L).natAbs with hdB
  have hdBpos : 0 < dB := by rw [hdB, Int.natAbs_pos]; exact NumberField.discr_ne_zero L
  -- For each `k`, choose an admissible prime `m_k > max dB 1` with `m_k ≡ 1 (mod 4·n^k)`.
  have hchoose : ∀ k : ℕ, ∃ m : ℕ, m.Prime ∧ dB < m ∧ m % 4 ≠ 2 ∧ n ^ k ∣ m - 1 := by
    intro k
    have hq : (4 * n ^ k) ≠ 0 := by positivity
    obtain ⟨m, hmgt, hmp, hmeq⟩ :=
      Nat.forall_exists_prime_gt_and_modEq (max dB 1) hq (Nat.coprime_one_left _)
    have hm1 : 1 ≤ m := hmp.one_lt.le
    have hdvd : 4 * n ^ k ∣ m - 1 := (Nat.modEq_iff_dvd' hm1).mp hmeq.symm
    refine ⟨m, hmp, by omega, ?_, dvd_trans ⟨4, by ring⟩ hdvd⟩
    have h4 : (4 : ℕ) ∣ m - 1 := dvd_trans ⟨n ^ k, rfl⟩ hdvd
    omega
  choose m hmp hmgt hm4 hmdvd using hchoose
  -- Admissibility consequences: each `m k` is `≥ 1`, nonzero, and coprime to `dB`.
  have hm1 : ∀ k, 1 ≤ m k := fun k => (hmp k).one_lt.le
  have hmne : ∀ k, m k ≠ 0 := fun k => (hmp k).pos.ne'
  have hmNeZero : ∀ k, NeZero (m k) := fun k => ⟨hmne k⟩
  have hmcop : ∀ k, dB.Coprime (m k) := fun k => by
    rw [Nat.coprime_comm, (hmp k).coprime_iff_not_dvd]
    exact fun hdvd => absurd (Nat.le_of_dvd hdBpos hdvd) (Nat.not_le.mpr (hmgt k))
  -- The exponent of `(ZMod (m k))ˣ` (cyclic, `m k` prime) is `m k - 1`, divisible by `n^k`.
  have hexp : ∀ k, Monoid.exponent (ZMod (m k))ˣ = m k - 1 := fun k => by
    haveI : Fact (m k).Prime := ⟨hmp k⟩
    rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime (hmp k)]
  -- Each lower-bound term `(|H_n(m k)|/|H(m k)|)·n⁻¹ ≤ L_inf` from the per-`m` bound (LF10).
  have hbound : ∀ k : ℕ,
      (Nat.card {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} : ℝ)
          / Nat.card ((ZMod (m k))ˣ) * (n : ℝ)⁻¹ ≤ L_inf := by
    intro k
    have hLF10 := liminf_density_S_sigma_ge_card_H_n_div_GH K L σ (m k) (hm1 k) (hm4 k)
      (hdB ▸ hmcop k)
    rw [← hn] at hLF10
    rw [← hLinf] at hLF10
    refine le_trans (le_of_eq ?_) hLF10
    have hHpos : (0 : ℝ) < Nat.card ((ZMod (m k))ˣ) := by
      have := hmNeZero k
      exact_mod_cast Nat.card_pos
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    field_simp
  -- The sequence of lower bounds tends to `n⁻¹`. Branch on `n = 1` vs `n ≥ 2`.
  have htends : Filter.Tendsto
      (fun k : ℕ ↦ (Nat.card {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} : ℝ)
          / Nat.card ((ZMod (m k))ˣ) * (n : ℝ)⁻¹)
      Filter.atTop (𝓝 ((n : ℝ)⁻¹)) := by
    -- The ratio `r k = |H_n(m k)|/|H(m k)|` tends to `1`.
    have hr1 : Filter.Tendsto
        (fun k : ℕ ↦ (Nat.card {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} : ℝ)
            / Nat.card ((ZMod (m k))ˣ)) Filter.atTop (𝓝 1) := by
      rcases eq_or_lt_of_le hn1 with hn1' | hn2'
      · -- `n = 1`: `H_n = univ`, ratio `≡ 1`.
        have hconst : ∀ k, (Nat.card {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} : ℝ)
            / Nat.card ((ZMod (m k))ˣ) = 1 := by
          intro k
          have := hmNeZero k
          have hg : Nat.card {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} = Nat.card ((ZMod (m k))ˣ) := by
            rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
            exact Fintype.card_congr (Equiv.subtypeUnivEquiv (fun x => hn1'.symm ▸ one_dvd _))
          have hposc : (0 : ℝ) < Nat.card ((ZMod (m k))ˣ) := by exact_mod_cast Nat.card_pos
          rw [hg, div_self hposc.ne']
        rw [tendsto_congr hconst]; exact tendsto_const_nhds
      · -- `n ≥ 2`: squeeze `1 - S(k) ≤ r k ≤ 1` with `S(k) → 0`.
        have hn2 : 2 ≤ n := hn2'
        set S : ℕ → ℝ := fun k => ∑ p ∈ n.primeFactors,
          (1 : ℝ) / (p : ℝ) ^ (k * n.factorization p - n.factorization p - 1) with hSdef
        have hSt : Filter.Tendsto S Filter.atTop (𝓝 0) := by
          rw [hSdef, show (0 : ℝ) = ∑ _p ∈ n.primeFactors, (0 : ℝ) by simp]
          refine tendsto_finsetSum _ (fun p hp => ?_)
          have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
          exact summand_tendsto p (n.factorization p) hpp.two_le
            (Nat.Prime.factorization_pos_of_dvd hpp (by omega) (Nat.dvd_of_mem_primeFactors hp))
        have hlo : Filter.Tendsto (fun k => 1 - S k) Filter.atTop (𝓝 1) := by
          simpa using hSt.const_sub 1
        -- Upper bound `r k ≤ 1` holds for all `k`; lower bound `1 - S k ≤ r k` for `k ≥ 1`.
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_
          (Filter.Eventually.of_forall (fun k => ?_))
        · filter_upwards [Filter.eventually_ge_atTop 1] with k hk1
          -- `1 - S k ≤ r k` from `H_n_ratio_ge`, using `n^k ∣ exponent (ZMod (m k))ˣ`.
          have hexpdvd : ∀ p ∈ n.primeFactors,
              p ^ (k * n.factorization p) ∣ Monoid.exponent (ZMod (m k))ˣ := by
            intro p hp
            rw [hexp k]
            refine dvd_trans ?_ (hmdvd k)
            calc p ^ (k * n.factorization p) = (p ^ n.factorization p) ^ k := by
                  rw [← pow_mul, mul_comm]
              _ ∣ n ^ k := pow_dvd_pow_of_dvd (Nat.ordProj_dvd n p) k
          exact H_n_ratio_ge (ZMod (m k))ˣ n k hn2 hk1 hexpdvd
        · -- `r k ≤ 1`.
          have := hmNeZero k
          have hpos : 0 < Nat.card ((ZMod (m k))ˣ) := Nat.card_pos
          rw [div_le_one (by exact_mod_cast hpos)]
          have hle : Nat.card {τ : (ZMod (m k))ˣ // n ∣ orderOf τ} ≤ Nat.card ((ZMod (m k))ˣ) :=
            Nat.card_le_card_of_injective (Subtype.val) Subtype.val_injective
          exact_mod_cast hle
    simpa using hr1.mul_const ((n : ℝ)⁻¹)
  -- Hence `n⁻¹ ≤ L_inf` by `le_of_tendsto` (the limit of the lower bounds is `n⁻¹`).
  exact le_of_tendsto htends (Filter.Eventually.of_forall hbound)

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
            {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
              frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
          / primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s)
      (𝓝[>] 1) (𝓝 1) := by
  classical
  set S : Gal(L/K) → Set (Ideal (𝓞 K)) := fun σ =>
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = ConjClasses.mk σ}
    with hS
  set R : Set (Ideal (𝓞 K)) :=
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭} with hR
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
    by_cases hunr : UnramifiedIn K L 𝔭
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
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card Gal(L/K) : ℝ)⁻¹) := by
  simp only [HasDirichletDensity, Nat.card_eq_fintype_card]
  refine tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one
    (fun τ s ↦
      primeIdealZetaSum
          {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
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
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card Gal(L/K) : ℝ)⁻¹) :=
  (chebotarev_abelian K L σ).hasLower

end Chebotarev
