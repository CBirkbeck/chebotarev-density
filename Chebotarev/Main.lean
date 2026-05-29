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
    (hunr : UnramifiedIn K L 𝔭) (_hCfrob : frobeniusClass K L 𝔭 = C) :
    Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (hp : 𝔓.IsPrime) (hP : 𝔓.LiesOver 𝔭)
        (hnz : 𝔓 ≠ ⊥),
        frobeniusAt K L 𝔓 hp hnz
            (by rw [show 𝔓.under (𝓞 K) = 𝔭 from hP.over.symm]; exact hunr 𝔓 hp hP)
          = σ}
      * orderOf σ * Nat.card C.carrier
      = Nat.card (L ≃ₐ[K] L) := by
  sorry

/-- **Density-lift through the fixed-field subextension** (Sharifi 7.2.2
Step 1, p. 143). Let `σ ∈ Gal(L/K)`, `E = L^⟨σ⟩` the fixed field of the
cyclic subgroup `⟨σ⟩`, and `σ_E ∈ Gal(L/E)` the corresponding element.
Given the abelian-case density over `E` for the Frobenius-fibre of `σ_E`
(value `1/|Gal(L/E)|`), the density over `K` of the Frobenius **class** of
`σ` is `|C|/|G|`.

Source quote (verbatim, p. 143): "δ(S) = … = (f|C|/|G|) δ(T_σ),
recalling once again that `Σ_𝔭 N𝔭^{-s} ~ Σ_P NP^{-s}`. Supposing the
theorem for K/E, we have δ(T_σ) = 1/f, and we therefore obtain δ(S) =
|C|/|G|." Here `f = ord σ = |Gal(L/E)|`, and the counting factor is
`count_primes_above_with_frobenius_eq_sigma`.

The hypothesis `hEfix` records that `E` is the fixed field of `⟨σ⟩`; the
hypothesis `hab` is the abelian-case output for `L/E` from
`chebotarev_abelian`. -/
theorem density_lift_through_fixedField
    [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L)
    (E : IntermediateField K L)
    (σE : L ≃ₐ[↥E] L)
    (_hEfix : E = IntermediateField.fixedField (Subgroup.zpowers σ))
    (_hab : HasDirichletDensity ↥E
        {P : Ideal (𝓞 ↥E) | P.IsPrime ∧ P ≠ ⊥ ∧ UnramifiedIn ↥E L P ∧
          frobeniusClass ↥E L P = ConjClasses.mk σE}
        ((Nat.card (L ≃ₐ[↥E] L) : ℝ)⁻¹)) :
    HasDirichletDensity K
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card (ConjClasses.mk σ).carrier : ℝ) / Nat.card (L ≃ₐ[K] L)) := by
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
  -- Step 1 (Sharifi 7.2.2): pick a representative σ ∈ C and reduce to the
  -- cyclic subextension L / E where E = L^⟨σ⟩.
  obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective C
  -- `Gal(L/E) ≃* ⟨σ⟩`, so `Gal(L/E)` is commutative (⟨σ⟩ is cyclic).
  have e := IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)
  letI : CommMonoid ↥(Subgroup.zpowers σ) := IsMulCommutative.instCommMonoid
  haveI :
      IsMulCommutative (L ≃ₐ[↥(IntermediateField.fixedField (Subgroup.zpowers σ))] L) :=
    ⟨⟨fun a b => by
      obtain ⟨x, rfl⟩ := e.surjective a
      obtain ⟨y, rfl⟩ := e.surjective b
      rw [← map_mul e x y, ← map_mul e y x, mul_comm x y]⟩⟩
  -- L / E is abelian, so the abelian case applies to its Frobenius σ_E.
  exact density_lift_through_fixedField K L σ
    (IntermediateField.fixedField (Subgroup.zpowers σ))
    (e ⟨σ, Subgroup.mem_zpowers σ⟩) rfl
    (chebotarev_abelian _ L (e ⟨σ, Subgroup.mem_zpowers σ⟩))

/-- In a commutative finite group every conjugacy class is a singleton,
so `|C| = 1`. (Uses `isConj_iff_eq`.) -/
theorem ConjClasses_carrier_card_eq_one_of_comm
    {G : Type*} [Group G] [IsMulCommutative G] [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier = 1 := by
  letI : CommMonoid G := IsMulCommutative.instCommMonoid
  have h : (ConjClasses.mk g).carrier = {g} := by
    ext a
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj,
      Set.mem_singleton_iff]
    exact isConj_iff_eq
  rw [h, Nat.card_coe_set_eq, Set.ncard_singleton]

/-- **Chebotarev's density theorem, abelian case** — a genuine top-down
consequence of `chebotarev_abelian`. When `G = Gal(L/K)` is abelian,
every conjugacy class `C` is a singleton `{σ}`, so the Frobenius-class
condition `σ_𝔭 = C` is `σ_𝔭 = σ`, `|C| = 1`, and the density `|C|/|G| =
1/|G|` is exactly the abelian-case value. -/
theorem chebotarev_density_of_comm
    [FiniteDimensional K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (C : ConjClasses (L ≃ₐ[K] L)) :
    HasDirichletDensity K
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = C}
      ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L)) := by
  obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective C
  rw [ConjClasses_carrier_card_eq_one_of_comm σ, Nat.cast_one, one_div]
  exact chebotarev_abelian K L σ

/-- Sub-lemma: a set of prime ideals with positive Dirichlet density is
infinite. Contrapositive: a finite set has density `0` (by
`hasDirichletDensity_of_finite` from `Density.lean`). -/
theorem infinite_of_hasDirichletDensity_pos
    {S : Set (Ideal (𝓞 K))} {δ : ℝ}
    (h : HasDirichletDensity K S δ) (hδ : 0 < δ) :
    S.Infinite := by
  sorry

/-- Sub-lemma: the size of a conjugacy class in a finite group is at
least `1` (the class always contains at least its own representative). -/
theorem ConjClasses_carrier_card_pos
    {G : Type*} [Group G] [Finite G] (C : ConjClasses G) :
    0 < Nat.card C.carrier := by
  obtain ⟨a, ha⟩ := ConjClasses.mk_surjective C
  have hmem : a ∈ C.carrier := ConjClasses.mem_carrier_iff_mk_eq.mpr ha
  have : Nonempty C.carrier := ⟨⟨a, hmem⟩⟩
  exact Nat.card_pos

/-- Existence of *infinitely many* primes with each Frobenius conjugacy class
— a qualitative corollary of `chebotarev_density`.

**Composition**: positive Dirichlet density (numerator `|C| ≥ 1`,
denominator `|G|`, so `|C|/|G| > 0`) implies the set is infinite, by
`infinite_of_hasDirichletDensity_pos`. -/
theorem infinite_setOf_frobenius_class
    [FiniteDimensional K L]
    (C : ConjClasses (L ≃ₐ[K] L)) :
    Set.Infinite
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = C} := by
  refine infinite_of_hasDirichletDensity_pos K (chebotarev_density K L C) ?_
  -- Show `(Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L) > 0`.
  apply div_pos
  · exact_mod_cast ConjClasses_carrier_card_pos C
  · exact_mod_cast Nat.card_pos (α := L ≃ₐ[K] L)

/-- Sub-lemma for `density_split_completely`: the identity conjugacy class
in a finite group has carrier of cardinality `1`. (`Nat.card.carrier` of
`ConjClasses.mk (1 : G)` is `1`.) -/
theorem ConjClasses_mk_one_carrier_card_eq_one
    (G : Type*) [Group G] [Finite G] :
    Nat.card (ConjClasses.mk (1 : G)).carrier = 1 := by
  have h : (ConjClasses.mk (1 : G)).carrier = {1} := by
    ext a
    simp only [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj,
      isConj_one_left, Set.mem_singleton_iff]
  rw [h, Nat.card_coe_set_eq, Set.ncard_singleton]

/-- Sub-lemma for `density_split_completely`: for a finite Galois
extension, the cardinality of the Galois group equals the degree.
Direct from mathlib's `IsGalois.card_aut_eq_finrank`. -/
theorem nat_card_galois_eq_finrank
    [FiniteDimensional K L] :
    (Nat.card (L ≃ₐ[K] L) : ℝ) = (Module.finrank K L : ℝ) := by
  rw [IsGalois.card_aut_eq_finrank K L]

/-- **Density of completely split primes** (Sharifi 7.1.14, as a corollary of
Chebotarev applied to the identity conjugacy class).

The Dirichlet density of primes `𝔭` of `𝓞 K` that split completely in `L`
equals `1 / [L : K]`.

**Composition**: apply `chebotarev_density` to the trivial conjugacy class
`ConjClasses.mk 1`, then simplify the value via
`ConjClasses_mk_one_carrier_card_eq_one` (numerator = 1) and
`nat_card_galois_eq_finrank` (denominator = `[L:K]`). -/
theorem density_split_completely
    [FiniteDimensional K L] :
    HasDirichletDensity K
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk 1}
      ((Module.finrank K L : ℝ)⁻¹) := by
  have h := chebotarev_density K L (ConjClasses.mk (1 : L ≃ₐ[K] L))
  rw [ConjClasses_mk_one_carrier_card_eq_one (L ≃ₐ[K] L)] at h
  rw [nat_card_galois_eq_finrank K L] at h
  simpa [one_div] using h

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
