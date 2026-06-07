module

public import Mathlib.RingTheory.Ideal.Over
public import CebotarevDensity.Cyclotomic

/-!
# Density transfer through a fixed-field subextension (Sharifi 7.2.2 Step 1)

The cyclic-reduction core of Chebotarev's density theorem. For `σ ∈ Gal(L/K)` and the
fixed field `E = L^⟨σ⟩` (so `L/E` is cyclic of degree `f = ord σ`), a counting argument
over the primes of `L` above a prime of `K` relates the Dirichlet density of the
`σ`-Frobenius fibre of `K` to that of the `σ_E`-Frobenius fibre of `E`:

  δ_K(S) = (f·|C|/|G|)·δ_E(T_σ).

The key result `density_lift_through_fixedField` packages this transfer: given the abelian
(cyclic) density `1/|Gal(L/E)|` of the `E`-fibre, it yields the `K`-fibre density
`|C|/|Gal(L/K)|`.

This is the Step-1 reduction of Sharifi 7.2.2 (p. 143), placed in its own module strictly
below both `Main.lean` (which consumes it for `chebotarev_density`) and `Abelian.lean`
(whose cyclotomic-crossing master leaf reuses it via the compositum `M/F`). The block is
independent of `chebotarev_abelian`: its only ingredients are the Frobenius/inertia counting
of `Frobenius.lean` and the Dirichlet-sum asymptotics of `Density.lean`/`ZetaProduct.lean`.

## Main results

* `Chebotarev.density_lift_through_fixedField` — the cyclic density transfer through `E/K`.

## References

* Sharifi, *Algebraic Number Theory*, Theorem 7.2.2 Step 1 (`docs/algnum.pdf`, p. 143).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, Appendix (`docs/cheb.pdf`, p. 18).
-/

@[expose] public section

noncomputable section

open Filter NumberField Topology Set

open scoped ENNReal

namespace Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

open scoped Pointwise in
/-- **Equipotent Frobenius fibres** (the "distributed evenly" of Sharifi 7.2.2, p. 143).
For `IsConj σ σ'`, conjugating by the witnessing element is a bijection between the primes
above `𝔭` with `Frob_𝔓 = σ` and those with `Frob_𝔓 = σ'` (via `IsArithFrobAt.conj`), so the
two Frobenius fibres have equal cardinality. -/
theorem frobeniusFibre_card_eq_of_isConj
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (_hunr : UnramifiedIn K L 𝔭)
    (σ σ' : Gal(L/K)) (hc : IsConj σ σ') :
    Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
        IsArithFrobAt (𝓞 K) σ 𝔓}
      = Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
        IsArithFrobAt (𝓞 K) σ' 𝔓} := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm c) fun 𝔓 ↦ ?_)
  simp only [MulAction.toPerm_apply]
  constructor
  · rintro ⟨hp, hP, hne, hfrob⟩
    haveI := hp
    haveI := hP
    refine ⟨inferInstance, inferInstance, ?_, ?_⟩
    · rw [← Ideal.smul_bot c]
      exact (MulAction.injective c).ne hne
    · exact hc ▸ hfrob.conj c
  · rintro ⟨hp, hP, hne, hfrob⟩
    haveI := hp
    haveI := hP
    have hsmul : c⁻¹ • (c • 𝔓) = 𝔓 := inv_smul_smul c 𝔓
    haveI hp' : 𝔓.IsPrime := hsmul ▸ (inferInstance : (c⁻¹ • (c • 𝔓)).IsPrime)
    haveI hP' : 𝔓.LiesOver 𝔭 := hsmul ▸ (inferInstance : (c⁻¹ • (c • 𝔓)).LiesOver 𝔭)
    have hne' : 𝔓 ≠ ⊥ := by
      rw [← hsmul, ← Ideal.smul_bot c⁻¹]
      exact (MulAction.injective c⁻¹).ne hne
    refine ⟨hp', hP', hne', ?_⟩
    have hconj := hfrob.conj c⁻¹
    rwa [hsmul, ← hc, show c⁻¹ * (c * σ * c⁻¹) * c⁻¹⁻¹ = σ by group] at hconj

/-- **Balanced fibre count.** If every prime above `𝔭` has Frobenius in the class `C = [σ]`
and conjugate Frobenius values occur equally often (`hequi`), the total number of primes
above `𝔭` is `|C|` times the number with `Frob_𝔓 = σ`: partition by the (class-`C`-valued)
Frobenius via `Finset.card_eq_sum_card_fiberwise`, then `Finset.sum_const` using `hequi`. -/
theorem card_primesAbove_eq_card_carrier_mul_frobeniusFibre
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (hσ : ConjClasses.mk σ = C)
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hCfrob : frobeniusClass K L 𝔭 = C)
    (hequi : ∀ σ' : Gal(L/K), IsConj σ σ' →
      Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
          IsArithFrobAt (𝓞 K) σ 𝔓}
        = Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
          IsArithFrobAt (𝓞 K) σ' 𝔓}) :
    Nat.card {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥}
      = Nat.card C.carrier
        * Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
          IsArithFrobAt (𝓞 K) σ 𝔓} := by
  have hpbot : 𝔭 ≠ ⊥ := UnramifiedIn.ne_bot K L hunr
  haveI : 𝔭.IsMaximal := ‹𝔭.IsPrime›.isMaximal hpbot
  haveI : Finite (𝔭.primesOver (𝓞 L)) := (IsDedekindDomain.primesOver_finite 𝔭 (𝓞 L)).to_subtype
  haveI : Finite {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} :=
    Finite.of_injective
      (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} ↦
        (⟨𝔓.1, 𝔓.2.1, 𝔓.2.2.1⟩ : 𝔭.primesOver (𝓞 L)))
      fun _ _ hab ↦ Subtype.ext (by simpa using hab)
  haveI : Fintype C.carrier := Fintype.ofFinite _
  have hfinP : ∀ (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭), Finite (𝓞 L ⧸ 𝔓) :=
    fun 𝔓 _ hP ↦ Ideal.finiteQuotientOfFreeOfNeBot 𝔓
      (ne_bot_of_ramificationIdx_eq_one K L (UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓 hP))
  have hmem : ∀ (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭),
      haveI := hfinP 𝔓 hP
      arithFrobAt (𝓞 K) Gal(L/K) 𝔓 ∈ C.carrier := by
    intro 𝔓 _ hP
    haveI := hfinP 𝔓 hP
    rw [ConjClasses.mem_carrier_iff_mk_eq, ← frobeniusClass_eq_mk_of_isArithFrobAt K L 𝔭 hunr _ 𝔓
      (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) hP, hCfrob]
  have hconj : ∀ g : C.carrier, IsConj σ g.1 := by
    rintro ⟨g, hg⟩
    rw [ConjClasses.mem_carrier_iff_mk_eq] at hg
    exact ConjClasses.mk_eq_mk_iff_isConj.mp (hσ.trans hg.symm)
  let F : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} → C.carrier := fun 𝔓 ↦
    haveI := 𝔓.2.1
    haveI := hfinP 𝔓.1 𝔓.2.2.1
    ⟨arithFrobAt (𝓞 K) Gal(L/K) 𝔓.1, hmem 𝔓.1 𝔓.2.2.1⟩
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv F), Nat.card_sigma]
  have hfib : ∀ g : C.carrier,
      Nat.card {𝔓 // F 𝔓 = g}
        = Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
            IsArithFrobAt (𝓞 K) σ 𝔓} := by
    intro g
    rw [hequi g.1 (hconj g)]
    refine Nat.card_congr ⟨fun x ↦ ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2, ?_⟩,
      fun x ↦ ⟨⟨x.1, by obtain ⟨hp, hP, hne, _⟩ := x.2; exact ⟨hp, hP, hne⟩⟩, ?_⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩
    · haveI := x.1.2.1
      haveI := hfinP x.1.1 x.1.2.2.1
      rw [← Subtype.ext_iff.mp x.2]
      exact IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) x.1.1
    · obtain ⟨hp, hP, hne, hg⟩ := x.2
      haveI := hp
      haveI := hP
      haveI := hfinP x.1 hP
      haveI : Algebra.IsUnramifiedAt (𝓞 K) x.1 :=
        (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hne).mpr
          (UnramifiedIn.ramificationIdx_eq_one K L hunr x.1 hP)
      exact Subtype.ext (eq_arithFrobAt_of_isArithFrobAt K L x.1 g.1 hg).symm
  simp_rw [hfib]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]

/-- **Even distribution of Frobenius over the conjugacy class** (Sharifi 7.2.2 Step 1,
p. 143). The Frobenius elements of the primes above `𝔭` sweep out the conjugacy class
`C = [σ]` evenly, so the number of primes above `𝔭` with `Frob_𝔓 = σ` times `|C|` equals
the total number of primes above `𝔭`. -/
theorem count_frobenius_eq_sigma_mul_card_carrier
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (_hσ : ConjClasses.mk σ = C)
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (_hCfrob : frobeniusClass K L 𝔭 = C) :
    Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭)
        (_ : 𝔓 ≠ ⊥), IsArithFrobAt (𝓞 K) σ 𝔓}
      * Nat.card C.carrier
      = Nat.card {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} :=
  (mul_comm _ _).trans (card_primesAbove_eq_card_carrier_mul_frobeniusFibre K L σ C _hσ 𝔭 hunr
    _hCfrob fun σ' hc ↦ frobeniusFibre_card_eq_of_isConj K L 𝔭 hunr σ σ' hc).symm

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
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (_hσ : ConjClasses.mk σ = C)
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (_hCfrob : frobeniusClass K L 𝔭 = C) :
    Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭)
        (_ : 𝔓 ≠ ⊥), IsArithFrobAt (𝓞 K) σ 𝔓}
      * orderOf σ * Nat.card C.carrier
      = Nat.card Gal(L/K) := by
  rw [mul_right_comm,
    count_frobenius_eq_sigma_mul_card_carrier K L σ C _hσ 𝔭 hunr _hCfrob]
  exact card_primesAbove_mul_orderOf_eq K L σ C _hσ 𝔭 hunr _hCfrob

omit [IsGalois K L] in
/-- The ratio of the full prime-ideal zeta sums over an intermediate field `E` and
over `K` tends to `1` as `s ↓ 1`. Both `Σ_univ^{↥E}` and `Σ_univ^K` are asymptotic to
`log(1/(s-1))` (`primeIdealZetaSum_univ_tendsto_log`, the `↥E` instance via
`NumberField.of_intermediateField`), so their ratio of ratios cancels. This is the
Lean form of Sharifi's "`Σ_𝔭 N𝔭^{-s} ~ Σ_P NP^{-s}`" (p. 143). -/
private theorem univ_ratio_E_K_tendsto_one [FiniteDimensional K L] (E : IntermediateField K L) :
    Tendsto (fun s : ℝ ↦ primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥E))) s
        / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s) (𝓝[>] 1) (𝓝 1) := by
  have hcancel := (primeIdealZetaSum_univ_tendsto_log (↥E)).div
    (primeIdealZetaSum_univ_tendsto_log K) one_ne_zero
  rw [one_div_one] at hcancel
  refine hcancel.congr' ?_
  filter_upwards [tendsto_log_one_div_sub_one_atTop.eventually_gt_atTop 0] with s hs
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hs.ne']

open scoped Pointwise in
/-- **Frobenius restricts through the tower** (the E-bridge core, Sharifi 7.2.2 p. 143).
For an intermediate field `E` and an unramified prime `𝔓` of `𝓞 L` whose residue field over
`𝓞 ↥E` has the same cardinality as over `𝓞 K` (`hnorm`; the "`𝔓 ∩ E` has degree one over
`K`" condition of Sharifi p. 143), the `E`-Frobenius `Frob^E_𝔓` restricted to `Gal(L/K)`
equals the `K`-Frobenius `Frob^K_𝔓`.

Both are characterized as raising residue classes to a fixed power
(`IsArithFrobAt`): `Frob^K_𝔓` to the `N(𝔓 ∩ 𝓞 K)`-th and `Frob^E_𝔓` to the
`N(𝔓 ∩ 𝓞 ↥E)`-th. The restricted automorphism `(Frob^E_𝔓).restrictScalars K` acts on `𝓞 L`
exactly as `Frob^E_𝔓` does (`AlgEquiv.restrictScalars_apply`), so by `hnorm` it raises
residue classes to the `N(𝔓 ∩ 𝓞 K)`-th power too, i.e. it is a `K`-Frobenius at `𝔓`. The two
`K`-Frobenii then coincide by the uniqueness at an unramified prime
(`IsArithFrobAt.mul_inv_mem_inertia` + trivial inertia).

mathlib has only `isConj_arithFrobAt` (conjugacy of `arithFrobAt` at primes over the same
base); the restriction-through-a-subextension identity is the new tower content. -/
theorem arithFrobAt_restrictScalars_eq [FiniteDimensional K L] (E : IntermediateField K L)
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hunrK : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1)
    (_hunrE : Ideal.ramificationIdx (𝔓.under (𝓞 ↥E)) 𝔓 = 1)
    (hnorm : Nat.card (𝓞 ↥E ⧸ 𝔓.under (𝓞 ↥E)) = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K))) :
    haveI : IsScalarTower K ↥E L := E.isScalarTower_mid'
    haveI : Finite (𝓞 L ⧸ 𝔓) :=
      Ideal.finiteQuotientOfFreeOfNeBot 𝔓 (ne_bot_of_ramificationIdx_eq_one K L hunrK)
    haveI : IsGalois (↥E) L := IsGalois.tower_top_intermediateField E
    (arithFrobAt (𝓞 ↥E) Gal(L/(↥E)) 𝔓).restrictScalars K = arithFrobAt (𝓞 K) Gal(L/K) 𝔓 := by
  haveI : IsScalarTower K ↥E L := E.isScalarTower_mid'
  haveI : IsGalois (↥E) L := IsGalois.tower_top_intermediateField E
  haveI : IsGaloisGroup Gal(L/(↥E)) (↥E) L := IsGaloisGroup.of_isGalois (↥E) L
  haveI hPbot : 𝔓 ≠ ⊥ := ne_bot_of_ramificationIdx_eq_one K L hunrK
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  set σE := arithFrobAt (𝓞 ↥E) Gal(L/(↥E)) 𝔓 with hσE
  have hKfrob1 : IsArithFrobAt (𝓞 K) (σE.restrictScalars K) 𝔓 := by
    intro x
    have hact : (σE.restrictScalars K) • x = σE • x := Subtype.ext (by
      change (σE.restrictScalars K) • (x : L) = σE • (x : L)
      rw [AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.restrictScalars_apply])
    change (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) (σE.restrictScalars K)) x
      - x ^ Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K)) ∈ 𝔓
    rw [show x ^ Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K))
          = x ^ Nat.card (𝓞 ↥E ⧸ 𝔓.under (𝓞 ↥E)) by rw [hnorm],
      show (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) (σE.restrictScalars K)) x = σE • x by
        rw [← hact]
        rfl]
    exact IsArithFrobAt.arithFrobAt (𝓞 ↥E) Gal(L/(↥E)) 𝔓 x
  have hmem := hKfrob1.mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓)
  rw [inertiaGroup_trivial_of_unramified K L 𝔓 hunrK, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

open scoped Pointwise in
/-- **The decomposition group of `𝔓` equals `Gal(L/E)`** (Sharifi 7.2.2 p. 143, "`P` is by
definition inert in `L`"). For an unramified `𝔓` of `𝓞 L` over `𝔭 = 𝔓 ∩ 𝓞 K` whose
`K`-Frobenius is `σ`, with `E = L^⟨σ⟩` and `f = ord σ = [L : E]`, the decomposition group
`D_𝔓 = stab_{Gal(L/K)} 𝔓` is cyclic of order `f` generated by `Frob^K_𝔓 = σ`, hence equals
`⟨σ⟩ = fixingSubgroup E`. Therefore the stabiliser of `𝔓` inside `Gal(L/E)` is everything:
every `E`-automorphism fixes `𝔓` (its restriction to `K` lies in `⟨σ⟩ = D_𝔓`). In particular
`𝔓` is the unique prime of `𝓞 L` above `𝔓 ∩ 𝓞 E`. -/
private theorem stabilizer_intermediate_eq_top_of_frobenius
    [FiniteDimensional K L] (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hunrK : UnramifiedIn K L (𝔓.under (𝓞 K))) (hPK : 𝔓.LiesOver (𝔓.under (𝓞 K)))
    (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓)
    (_horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    MulAction.stabilizer
        Gal(L/↥(IntermediateField.fixedField (Subgroup.zpowers σ))) 𝔓 = ⊤ := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  have hraK := UnramifiedIn.ramificationIdx_eq_one K L hunrK 𝔓 hPK
  have hPbot : 𝔓 ≠ ⊥ := ne_bot_of_ramificationIdx_eq_one K L hraK
  have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := UnramifiedIn.ne_bot K L hunrK
  haveI : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
  haveI : (𝔓.under (𝓞 K)).IsMaximal :=
    (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  haveI : Algebra.IsSeparable (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
    letI : Field (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.Quotient.field _
    letI : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
    exact IsGalois.to_isSeparable
  have hmem : σ ∈ MulAction.stabilizer Gal(L/K) 𝔓 := hfrob.mem_stabilizer
  have hinertK : (𝔓.under (𝓞 K)).inertiaDeg 𝔓 = orderOf σ := by
    rw [Ideal.inertiaDeg_algebraMap, orderOf_eq_finrank_of_isArithFrobAt K L σ 𝔓 hraK hfrob]
  have hcardstab' : Nat.card (MulAction.stabilizer Gal(L/K) 𝔓) = orderOf σ := by
    rw [Ideal.card_stabilizer_eq (𝔓.under (𝓞 K)) hpbot 𝔓,
      Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 Gal(L/K), hraK, one_mul,
      Ideal.inertiaDegIn_eq_inertiaDeg (𝔓.under (𝓞 K)) 𝔓 Gal(L/K), hinertK]
  have hstab : Subgroup.zpowers σ = MulAction.stabilizer Gal(L/K) 𝔓 :=
    Subgroup.eq_of_le_of_card_ge (by rwa [Subgroup.zpowers_le])
      (by rw [Nat.card_zpowers, hcardstab'])
  rw [eq_top_iff]
  intro τ _
  rw [MulAction.mem_stabilizer_iff]
  change τ • 𝔓 = 𝔓
  have hmemfix : τ.restrictScalars K
      ∈ IntermediateField.fixingSubgroup (IntermediateField.fixedField (Subgroup.zpowers σ)) :=
    fun x ↦ τ.commutes x
  rw [IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers σ)] at hmemfix
  have hstabmem : τ.restrictScalars K ∈ MulAction.stabilizer Gal(L/K) 𝔓 := hstab ▸ hmemfix
  exact MulAction.mem_stabilizer_iff.mp hstabmem

open scoped Pointwise in
/-- **The fixed-field prime below `𝔓` has degree one over `K`** (Sharifi 7.2.2 p. 143, "`P` has
degree one over `K`"). Continuing from `stabilizer_intermediate_eq_top_of_frobenius`: with
`P = 𝔓 ∩ 𝓞 E`, since `𝔓` is unramified over `K` the ramification index `e(𝔓 ∣ P) = 1`, and the
decomposition group of `𝔓` in `Gal(L/E)` being all of `Gal(L/E)` forces the inertia degree
`f(𝔓 ∣ P) = [L : E] = f`, hence by the tower law `f(P ∣ 𝔭) = f(𝔓 ∣ 𝔭)/f(𝔓 ∣ P) = f/f = 1`.
The residue field of `P` over `K` is therefore trivial, i.e. `N P = N 𝔭`. -/
private theorem inertiaDeg_under_E_eq_one_of_frobenius
    [FiniteDimensional K L] (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hunrK : UnramifiedIn K L (𝔓.under (𝓞 K))) (hPK : 𝔓.LiesOver (𝔓.under (𝓞 K)))
    (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓)
    (horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    Ideal.ramificationIdx
        (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓 = 1
      ∧ (𝔓.under (𝓞 K)).inertiaDeg
          (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) = 1
      ∧ Nat.card (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))
            ⧸ 𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
          = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K)) := by
  set E := IntermediateField.fixedField (Subgroup.zpowers σ) with hE
  haveI : IsScalarTower K ↥E L := E.isScalarTower_mid'
  haveI : IsGalois (↥E) L := IsGalois.tower_top_intermediateField _
  have hraK := UnramifiedIn.ramificationIdx_eq_one K L hunrK 𝔓 hPK
  have hPbot : 𝔓 ≠ ⊥ := ne_bot_of_ramificationIdx_eq_one K L hraK
  have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := UnramifiedIn.ne_bot K L hunrK
  haveI : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
  haveI : (𝔓.under (𝓞 K)).IsMaximal :=
    (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  haveI hPEp : (𝔓.under (𝓞 ↥E)).IsPrime := inferInstance
  haveI hPK' : 𝔓.LiesOver (𝔓.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓)
  haveI hPEK : (𝔓.under (𝓞 ↥E)).LiesOver (𝔓.under (𝓞 K)) := inferInstance
  haveI hPPE : 𝔓.LiesOver (𝔓.under (𝓞 ↥E)) := Ideal.over_under (A := 𝓞 ↥E) (P := 𝔓)
  have hpEbot : 𝔓.under (𝓞 ↥E) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 ↥E) hPbot
  haveI : (𝔓.under (𝓞 ↥E)).IsMaximal := hPEp.isMaximal hpEbot
  have hraE : Ideal.ramificationIdx (𝔓.under (𝓞 ↥E)) 𝔓 = 1 := by
    have htower := Ideal.ramificationIdx_algebra_tower' (𝔓.under (𝓞 K)) (𝔓.under (𝓞 ↥E)) 𝔓
    rw [hraK] at htower
    exact Nat.eq_one_of_mul_eq_one_left htower.symm
  haveI : Algebra.IsSeparable (𝓞 ↥E ⧸ 𝔓.under (𝓞 ↥E)) (𝓞 L ⧸ 𝔓) := by
    letI : Field (𝓞 ↥E ⧸ 𝔓.under (𝓞 ↥E)) := Ideal.Quotient.field _
    letI : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
    exact IsGalois.to_isSeparable
  have hstabE : MulAction.stabilizer Gal(L/(↥E)) 𝔓 = ⊤ :=
    stabilizer_intermediate_eq_top_of_frobenius σ 𝔓 hunrK hPK hfrob horderE
  have hcardE : Nat.card (MulAction.stabilizer Gal(L/(↥E)) 𝔓)
      = (𝔓.under (𝓞 ↥E)).ramificationIdxIn (𝓞 L) * (𝔓.under (𝓞 ↥E)).inertiaDegIn (𝓞 L) :=
    Ideal.card_stabilizer_eq (𝔓.under (𝓞 ↥E)) hpEbot 𝔓
  rw [hstabE, Subgroup.card_top,
    Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 ↥E)) 𝔓 Gal(L/(↥E)), hraE, one_mul,
    Ideal.inertiaDegIn_eq_inertiaDeg (𝔓.under (𝓞 ↥E)) 𝔓 Gal(L/(↥E)),
    Ideal.inertiaDeg_algebraMap] at hcardE
  have hinertTower : (𝔓.under (𝓞 K)).inertiaDeg 𝔓
      = (𝔓.under (𝓞 K)).inertiaDeg (𝔓.under (𝓞 ↥E))
        * (𝔓.under (𝓞 ↥E)).inertiaDeg 𝔓 := by
    rw [Ideal.inertiaDeg_eq_inertiaDeg' (𝔓.under (𝓞 K)) 𝔓,
      Ideal.inertiaDeg_eq_inertiaDeg' (𝔓.under (𝓞 K)) (𝔓.under (𝓞 ↥E)),
      Ideal.inertiaDeg_eq_inertiaDeg' (𝔓.under (𝓞 ↥E)) 𝔓]
    exact Ideal.inertiaDeg'_tower (R := 𝓞 K) (S := 𝓞 ↥E) (𝔓.under (𝓞 ↥E)) 𝔓
  have hinertK : (𝔓.under (𝓞 K)).inertiaDeg 𝔓 = orderOf σ := by
    rw [Ideal.inertiaDeg_algebraMap, orderOf_eq_finrank_of_isArithFrobAt K L σ 𝔓 hraK hfrob]
  have hfPE : (𝔓.under (𝓞 ↥E)).inertiaDeg 𝔓 = orderOf σ := by
    rw [Ideal.inertiaDeg_algebraMap, ← hcardE, horderE]
  have hpos : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
  have hinertPK : (𝔓.under (𝓞 K)).inertiaDeg (𝔓.under (𝓞 ↥E)) = 1 := by
    rw [hinertK, hfPE] at hinertTower
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [one_mul]; exact hinertTower.symm)
  refine ⟨hraE, hinertPK, ?_⟩
  have hnormP : Nat.card (𝓞 ↥E ⧸ 𝔓.under (𝓞 ↥E))
      = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K)) ^ (𝔓.under (𝓞 K)).inertiaDeg (𝔓.under (𝓞 ↥E)) := by
    simpa [Submodule.cardQuot_apply, Ideal.absNorm_apply] using
      Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver (𝔓.under (𝓞 ↥E)) (𝔓.under (𝓞 K))
        inferInstance hpbot
  rw [hnormP, hinertPK, pow_one]

open scoped Pointwise in
/-- **`𝔓` is the unique prime of `𝓞 L` above `𝔓 ∩ 𝓞 E`** (Sharifi 7.2.2 p. 143, "`P` is by
definition inert in `L`"). Since `stabilizer Gal(L/E) 𝔓 = ⊤` and `Gal(L/E)` acts transitively
on the primes above `𝔓 ∩ 𝓞 E`, any prime `𝔔` of `𝓞 L` above `𝔓 ∩ 𝓞 E` equals `𝔓`. -/
private theorem eq_of_liesOver_under_E_of_frobenius
    [FiniteDimensional K L] (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hunrK : UnramifiedIn K L (𝔓.under (𝓞 K))) (hPK : 𝔓.LiesOver (𝔓.under (𝓞 K)))
    (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓)
    (horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (𝔔 : Ideal (𝓞 L)) [𝔔.IsPrime]
    (hQ : haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      𝔔.LiesOver (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))) :
    𝔔 = 𝔓 := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  haveI : IsGaloisGroup Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
      (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L := IsGaloisGroup.of_isGalois _ L
  set E := IntermediateField.fixedField (Subgroup.zpowers σ) with hE
  haveI := hQ
  haveI : 𝔓.LiesOver (𝔓.under (𝓞 ↥E)) := Ideal.over_under (A := 𝓞 ↥E) (P := 𝔓)
  have hstabE : MulAction.stabilizer Gal(L/(↥E)) 𝔓 = ⊤ :=
    stabilizer_intermediate_eq_top_of_frobenius σ 𝔓 hunrK hPK hfrob horderE
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (𝔓.under (𝓞 ↥E)) 𝔓 𝔔 Gal(L/(↥E))
  rw [← hτ, MulAction.mem_stabilizer_iff.mp (hstabE ▸ Subgroup.mem_top τ)]

/-- **The fixed-field Frobenius below `𝔓` is `σ_E`** (Sharifi 7.2.2 p. 143). For an L-prime
`𝔓` with `Frob^K_𝔓 = σ` lying over a degree-one (over `K`) prime `P = 𝔓 ∩ 𝓞 E`, the
`E`-Frobenius `Frob^E_𝔓` restricts to `σ`, hence (as `σ_E` also restricts to `σ` and
`restrictScalars` is injective) `Frob^E_𝔓 = σ_E`. -/
private theorem arithFrobAt_E_eq_of_isArithFrobAt
    [FiniteDimensional K L] (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hσE : letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      σE.restrictScalars K = σ)
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hunrK : UnramifiedIn K L (𝔓.under (𝓞 K)))
    (hPK : 𝔓.LiesOver (𝔓.under (𝓞 K)))
    (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓)
    (_horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hraE : Ideal.ramificationIdx
        (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓 = 1)
    (hnorm : Nat.card (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))
          ⧸ 𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
        = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K))) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
      (ne_bot_of_ramificationIdx_eq_one K L (UnramifiedIn.ramificationIdx_eq_one K L hunrK 𝔓 hPK))
    haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
      IsGalois.tower_top_intermediateField _
    arithFrobAt (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
      Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓 = σE := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  have hPbot : 𝔓 ≠ ⊥ :=
    ne_bot_of_ramificationIdx_eq_one K L (UnramifiedIn.ramificationIdx_eq_one K L hunrK 𝔓 hPK)
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hPbot).mpr
      (UnramifiedIn.ramificationIdx_eq_one K L hunrK 𝔓 hPK)
  have hbridge := arithFrobAt_restrictScalars_eq
    (IntermediateField.fixedField (Subgroup.zpowers σ)) 𝔓
    (UnramifiedIn.ramificationIdx_eq_one K L hunrK 𝔓 hPK) hraE hnorm
  rw [(eq_arithFrobAt_of_isArithFrobAt K L 𝔓 σ hfrob).symm] at hbridge
  exact AlgEquiv.restrictScalars_injective K (hbridge.trans hσE.symm)

/-- **Fibre bijection: degree-one `E`-primes with Frobenius `σ_E` ↔ `L`-primes with
Frobenius `σ`** (Sharifi 7.2.2 p. 143). For a prime `𝔭` of `𝓞 K` unramified in `L` with
Frobenius class `[σ]`, the map `𝔓 ↦ 𝔓 ∩ 𝓞 E` is a bijection from the primes `𝔓` of `𝓞 L`
above `𝔭` with `Frob^K_𝔓 = σ` onto the primes `P` of `𝓞 E` above `𝔭`, unramified in `L`,
with `Frob^E_P = [σ_E]` and `f(P ∣ 𝔭) = 1`. Hence the two fibres are equinumerous; combined
with the proven count `count_primes_above_with_frobenius_eq_sigma` this gives the number of
such `P` over `𝔭` as `|G|/(f·|C|)`. -/
private theorem card_fibre_E_eq_card_fibre_L
    [FiniteDimensional K L] (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hσE : letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      σE.restrictScalars K = σ)
    [IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))]
    (horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (_hCfrob : frobeniusClass K L 𝔭 = ConjClasses.mk σ) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    Nat.card {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
        P ∈ {P | P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
              ∧ frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
                = ConjClasses.mk σE
              ∧ (P.under (𝓞 K)).inertiaDeg P = 1} ∧ P.LiesOver 𝔭 ∧ P ≠ ⊥}
      = Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
          IsArithFrobAt (𝓞 K) σ 𝔓} := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  have hpbot : 𝔭 ≠ ⊥ := UnramifiedIn.ne_bot K L hunr
  have hPmem : ∀ (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
      IsArithFrobAt (𝓞 K) σ 𝔓 →
      (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) ∈
          {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
            P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
            frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
              = ConjClasses.mk σE ∧ (P.under (𝓞 K)).inertiaDeg P = 1}
        ∧ (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))).LiesOver 𝔭
        ∧ (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) ≠ ⊥ := by
    intro 𝔓 _ hP hPbot hfrob
    haveI := hP
    have hunderK : 𝔓.under (𝓞 K) = 𝔭 := hP.over.symm
    have hunrK : UnramifiedIn K L (𝔓.under (𝓞 K)) := hunderK ▸ hunr
    haveI : 𝔓.LiesOver (𝔓.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓)
    haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
    obtain ⟨hraE, hinPK, hnorm⟩ :=
      inertiaDeg_under_E_eq_one_of_frobenius σ 𝔓 hunrK inferInstance hfrob horderE
    have hfrE := arithFrobAt_E_eq_of_isArithFrobAt σ σE hσE 𝔓 hunrK inferInstance hfrob horderE
      hraE hnorm
    have hunram : UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L
        (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) := by
      refine ⟨Ideal.IsIntegral.comap_ne_bot _ hPbot, fun 𝔔 h𝔔max h𝔔lo ↦ ?_⟩
      haveI := h𝔔max.isPrime
      have h𝔔eq : 𝔔 = 𝔓 := eq_of_liesOver_under_E_of_frobenius σ 𝔓 hunrK inferInstance hfrob
        horderE 𝔔 h𝔔lo
      subst h𝔔eq
      exact (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hPbot).mpr hraE
    haveI hPEK : (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))).LiesOver 𝔭 := by
      haveI : (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))).LiesOver
          (𝔓.under (𝓞 K)) := inferInstance
      rwa [hunderK] at this
    haveI hPPE : 𝔓.LiesOver (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
      Ideal.over_under (A := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) (P := 𝔓)
    refine ⟨⟨inferInstance, hunram, ?_, ?_⟩, hPEK, Ideal.IsIntegral.comap_ne_bot _ hPbot⟩
    · rw [frobeniusClass_eq_mk_of_isArithFrobAt
        (↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
        L (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) hunram _ 𝔓
        (IsArithFrobAt.arithFrobAt (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
          Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓) hPPE,
        ConjClasses.mk_eq_mk_iff_isConj]
      exact isConj_iff.mpr ⟨1, by simp [hfrE]⟩
    · rw [show (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))).under (𝓞 K)
          = 𝔓.under (𝓞 K) from Ideal.under_under 𝔓]
      exact hinPK
  refine (Nat.card_congr (Equiv.ofBijective
      (fun 𝔓 ↦ ⟨𝔓.1.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))),
        by obtain ⟨_, hP, hPbot, hfrob⟩ := 𝔓.2; exact hPmem 𝔓.1 hP hPbot hfrob⟩)
      ⟨?_, ?_⟩)).symm
  · rintro ⟨𝔓₁, h𝔓₁, hP₁, hP₁bot, hfrob₁⟩ ⟨𝔓₂, h𝔓₂, hP₂, hP₂bot, hfrob₂⟩ hΦ
    haveI := h𝔓₁
    haveI := h𝔓₂
    haveI := hP₁
    haveI := hP₂
    have hunderK₁ : 𝔓₁.under (𝓞 K) = 𝔭 := hP₁.over.symm
    have hunrK₁ : UnramifiedIn K L (𝔓₁.under (𝓞 K)) := hunderK₁ ▸ hunr
    haveI : 𝔓₁.LiesOver (𝔓₁.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓₁)
    have hΦ' : 𝔓₂.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
        = 𝔓₁.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) :=
      congrArg Subtype.val hΦ |>.symm
    haveI hP₂lo : 𝔓₂.LiesOver
        (𝔓₁.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) := by
      haveI : 𝔓₂.LiesOver
        (𝔓₂.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
        Ideal.over_under (A := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) (P := 𝔓₂)
      rwa [hΦ'] at this
    exact Subtype.ext (eq_of_liesOver_under_E_of_frobenius σ 𝔓₁ hunrK₁ inferInstance hfrob₁
      horderE 𝔓₂ hP₂lo).symm
  · rintro ⟨P, ⟨hPp, hPunr, hPfrob, hPdeg⟩, hPlo, hPbot⟩
    haveI := hPp
    haveI := hPlo
    obtain ⟨𝔓, h𝔓p, h𝔓lo, h𝔓bot⟩ := exists_prime_liesOver
      (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L P hPbot
    haveI := h𝔓p
    haveI := h𝔓lo
    have hPeq : 𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) = P :=
      h𝔓lo.over.symm
    haveI hPPE : 𝔓.LiesOver (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
      Ideal.over_under (A := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) (P := 𝔓)
    have hunderK : 𝔓.under (𝓞 K) = 𝔭 := by
      rw [← Ideal.under_under (B := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) 𝔓,
        hPeq]
      exact hPlo.over.symm
    haveI hPK𝔓 : 𝔓.LiesOver 𝔭 := hunderK ▸ Ideal.over_under (A := 𝓞 K) (P := 𝔓)
    have hunrK : UnramifiedIn K L (𝔓.under (𝓞 K)) := hunderK ▸ hunr
    haveI : 𝔓.LiesOver (𝔓.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓)
    have hinertPK1 : (𝔓.under (𝓞 K)).inertiaDeg
        (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) = 1 := by
      rw [hPeq, ← Ideal.under_under (B := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
        𝔓, hPeq]
      exact hPdeg
    have hraE : Ideal.ramificationIdx
        (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓 = 1 :=
      (Algebra.isUnramifiedAt_iff_of_isDedekindDomain h𝔓bot).mp
        (hPunr.2 𝔓 (h𝔓p.isMaximal h𝔓bot) (hPeq ▸ hPPE))
    have hnorm : Nat.card (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))
          ⧸ 𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
        = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K)) := by
      have hnP : Nat.card (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))
            ⧸ 𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
          = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K))
            ^ (𝔓.under (𝓞 K)).inertiaDeg
                (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) := by
        simpa [Submodule.cardQuot_apply, Ideal.absNorm_apply] using
          Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver
            (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) (𝔓.under (𝓞 K))
            inferInstance (hunderK ▸ hpbot)
      rw [hnP, hinertPK1, pow_one]
    haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 h𝔓bot
    have hfrEeqσE : arithFrobAt (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
        Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓 = σE := by
      letI : CommMonoid Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
        IsMulCommutative.instCommMonoid
      have hcl := frobeniusClass_eq_mk_of_isArithFrobAt
        (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L P hPunr _ 𝔓
        (IsArithFrobAt.arithFrobAt (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
          Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓) (hPeq ▸ hPPE)
      rw [hPfrob] at hcl
      exact isConj_iff_eq.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hcl.symm)
    have hfrobK : arithFrobAt (𝓞 K) Gal(L/K) 𝔓 = σ := by
      have hbridge := arithFrobAt_restrictScalars_eq
        (IntermediateField.fixedField (Subgroup.zpowers σ)) 𝔓
        (UnramifiedIn.ramificationIdx_eq_one K L hunrK 𝔓 inferInstance) hraE hnorm
      rw [hfrEeqσE, hσE] at hbridge
      exact hbridge.symm
    exact ⟨⟨𝔓, h𝔓p, hPK𝔓, h𝔓bot, hfrobK ▸ IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓⟩,
      Subtype.ext hPeq⟩

/-- **A degree-one fibre prime has `K`-Frobenius class `[σ]`** (Sharifi 7.2.2 p. 143). If `P`
is a prime of `𝓞 E` above an unramified-in-`L` prime `𝔭 = P ∩ 𝓞 K`, unramified in `L`, with
`Frob^E_P = [σ_E]` and degree one over `K`, then the `K`-Frobenius class of `𝔭` is `[σ]`. -/
private theorem frobeniusClass_under_eq_of_mem_fibre
    [FiniteDimensional K L] (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hσE : letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      σE.restrictScalars K = σ)
    [IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))]
    (_horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) [P.IsPrime]
    (hunrP : UnramifiedIn K L (P.under (𝓞 K)))
    (hPunr : UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P)
    (hPfrob : frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
      = ConjClasses.mk σE)
    (hPdeg : (P.under (𝓞 K)).inertiaDeg P = 1) (hPbot : P ≠ ⊥) :
    frobeniusClass K L (P.under (𝓞 K)) = ConjClasses.mk σ := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  haveI : (P.under (𝓞 K)).IsPrime := inferInstance
  obtain ⟨𝔓, h𝔓p, h𝔓lo, h𝔓bot⟩ := exists_prime_liesOver
    (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L P hPbot
  haveI := h𝔓p
  haveI := h𝔓lo
  have hPeq : 𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) = P :=
    h𝔓lo.over.symm
  haveI hPPE : 𝔓.LiesOver (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
    Ideal.over_under (A := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) (P := 𝔓)
  have hunderK : 𝔓.under (𝓞 K) = P.under (𝓞 K) := by
    rw [← Ideal.under_under (B := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) 𝔓, hPeq]
  haveI hPK𝔓 : 𝔓.LiesOver (P.under (𝓞 K)) := hunderK ▸ Ideal.over_under (A := 𝓞 K) (P := 𝔓)
  have hunrK : UnramifiedIn K L (𝔓.under (𝓞 K)) := hunderK ▸ hunrP
  haveI : 𝔓.LiesOver (𝔓.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓)
  have hinertPK1 : (𝔓.under (𝓞 K)).inertiaDeg
      (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) = 1 := by
    rw [hPeq, hunderK]
    exact hPdeg
  have hraE : Ideal.ramificationIdx
      (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓 = 1 :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain h𝔓bot).mp
      (hPunr.2 𝔓 (h𝔓p.isMaximal h𝔓bot) (hPeq ▸ hPPE))
  have hnorm : Nat.card (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))
        ⧸ 𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
      = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K)) := by
    have hnP := Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver
      (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) (𝔓.under (𝓞 K))
      inferInstance (UnramifiedIn.ne_bot K L hunrK)
    simp only [Submodule.cardQuot_apply, Ideal.absNorm_apply] at hnP ⊢
    rw [hnP, hinertPK1, pow_one]
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 h𝔓bot
  have hfrEeqσE : arithFrobAt (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
      Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓 = σE := by
    letI : CommMonoid Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
      IsMulCommutative.instCommMonoid
    have hcl := frobeniusClass_eq_mk_of_isArithFrobAt
      (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L P hPunr _ 𝔓
      (IsArithFrobAt.arithFrobAt (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
        Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓) (hPeq ▸ hPPE)
    rw [hPfrob] at hcl
    exact isConj_iff_eq.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hcl.symm)
  have hfrobK : arithFrobAt (𝓞 K) Gal(L/K) 𝔓 = σ := by
    have hbridge := arithFrobAt_restrictScalars_eq
      (IntermediateField.fixedField (Subgroup.zpowers σ)) 𝔓
      (UnramifiedIn.ramificationIdx_eq_one K L hunrK 𝔓 inferInstance) hraE hnorm
    rw [hfrEeqσE, hσE] at hbridge
    exact hbridge.symm
  rw [show P.under (𝓞 K) = 𝔓.under (𝓞 K) from hunderK.symm,
    frobeniusClass_eq_mk_of_isArithFrobAt K L (𝔓.under (𝓞 K)) hunrK _ 𝔓
      (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) inferInstance, hfrobK]

/-- **LEAF A: the degree-one part of `T` carries the main term** (Sharifi 7.2.2 p. 143). For
`1 < s`, the partial Dirichlet sum over the set `T₁` of degree-one (over `K`) primes `P` of
`𝓞 E` above an unramified-in-`L` prime, with `Frob^E_P = [σ_E]`, equals `|G|/(f·|C|)` times the
partial sum over `S` (the primes of `𝓞 K` with `K`-Frobenius class `[σ]`).  The fibre over
each `𝔭 ∈ S` has exactly `|G|/(f·|C|)` such primes `P` (the fibre bijection
`card_fibre_E_eq_card_fibre_L` together with the proven count
`count_primes_above_with_frobenius_eq_sigma`), and `N P = N 𝔭` for degree-one `P`. -/
private theorem primeIdealZetaSum_fibre_eq_smul
    [FiniteDimensional K L] (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hσE : letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      σE.restrictScalars K = σ)
    [IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))]
    (horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    {s : ℝ} (hs : 1 < s) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    primeIdealZetaSum
        {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
          P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
          frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
            = ConjClasses.mk σE ∧ (P.under (𝓞 K)).inertiaDeg P = 1 ∧
          UnramifiedIn K L (P.under (𝓞 K))} s
      = ((Nat.card Gal(L/K) : ℝ) / (orderOf σ * Nat.card (ConjClasses.mk σ).carrier))
        * primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
            frobeniusClass K L 𝔭 = ConjClasses.mk σ} s := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  set Sset := {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
    frobeniusClass K L 𝔭 = ConjClasses.mk σ} with hSset
  set T₁set := {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
    P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
    frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P = ConjClasses.mk σE ∧
    (P.under (𝓞 K)).inertiaDeg P = 1 ∧ UnramifiedIn K L (P.under (𝓞 K))} with hT₁set
  set S' := {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ Sset ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} with hS'
  have hgmem : ∀ P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥},
      P.1.under (𝓞 K) ∈ Sset ∧ (P.1.under (𝓞 K)).IsPrime ∧ P.1.under (𝓞 K) ≠ ⊥ := by
    rintro ⟨P, ⟨hPp, hPunr, hPfrob, hPdeg, hunrP⟩, _, hPbot⟩
    haveI := hPp
    refine ⟨⟨inferInstance, hunrP, ?_⟩, inferInstance, UnramifiedIn.ne_bot K L hunrP⟩
    exact frobeniusClass_under_eq_of_mem_fibre σ σE hσE horderE P hunrP hPunr hPfrob hPdeg hPbot
  set g : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥} → S' :=
    fun P ↦ ⟨P.1.under (𝓞 K), hgmem P⟩ with hg
  have hnormeq : ∀ P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥},
      (Ideal.absNorm P.1 : ℝ) = (Ideal.absNorm (P.1.under (𝓞 K)) : ℝ) := by
    rintro ⟨P, ⟨hPp, _, _, hPdeg, _⟩, _, hPbot⟩
    haveI := hPp
    have hpbot : P.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
    haveI : P.LiesOver (P.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := P)
    have hpow := Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver P (P.under (𝓞 K)) inferInstance hpbot
    rw [hPdeg, pow_one] at hpow
    rw [hpow]
  have hcardfib : ∀ 𝔭 : S', (orderOf σ * Nat.card (ConjClasses.mk σ).carrier) *
      Nat.card {P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥} // g P = 𝔭} = Nat.card Gal(L/K) := by
    intro 𝔭
    obtain ⟨hp𝔭, hunr𝔭, hfrob𝔭⟩ := 𝔭.2.1
    haveI := hp𝔭
    have hreindex : Nat.card {P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥} // g P = 𝔭}
        = Nat.card {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
            P ∈ {P | P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ))
                  L P ∧ frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
                  = ConjClasses.mk σE ∧ (P.under (𝓞 K)).inertiaDeg P = 1}
              ∧ P.LiesOver 𝔭.1 ∧ P ≠ ⊥} := by
      refine Nat.card_congr ⟨fun x ↦ ⟨x.1.1, ?_, ?_, x.1.2.2.2⟩,
        fun y ↦ ⟨⟨y.1, ?_, y.2.1.1, y.2.2.2⟩, ?_⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
      · exact ⟨x.1.2.1.1, x.1.2.1.2.1, x.1.2.1.2.2.1, x.1.2.1.2.2.2.1⟩
      · exact ⟨(congrArg Subtype.val x.2).symm ▸ (Ideal.over_under (A := 𝓞 K) (P := x.1.1)).over⟩
      · haveI := y.2.1.1
        have hunderK : y.1.under (𝓞 K) = 𝔭.1 := (y.2.2.1).over.symm
        exact ⟨y.2.1.1, y.2.1.2.1, y.2.1.2.2.1, y.2.1.2.2.2, by rw [hunderK]; exact hunr𝔭⟩
      · exact Subtype.ext (y.2.2.1).over.symm
    rw [hreindex, card_fibre_E_eq_card_fibre_L σ σE hσE horderE 𝔭.1 hunr𝔭 hfrob𝔭, mul_comm,
      ← mul_assoc]
    exact count_primes_above_with_frobenius_eq_sigma K L σ (ConjClasses.mk σ) rfl 𝔭.1 hunr𝔭 hfrob𝔭
  have hfibfin : ∀ 𝔭 : S', Finite {P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥} // g P = 𝔭} := by
    intro 𝔭
    haveI := 𝔭.2.2.1
    haveI : 𝔭.1.IsMaximal := 𝔭.2.2.1.isMaximal 𝔭.2.2.2
    haveI : Finite (𝔭.1.primesOver
        (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
      (IsDedekindDomain.primesOver_finite 𝔭.1 _).to_subtype
    refine Finite.of_injective (β := 𝔭.1.primesOver
        (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
      (fun P ↦ ⟨P.1.1, P.1.2.2.1, ?_⟩) ?_
    · haveI := P.1.2.2.1
      exact ⟨(congrArg Subtype.val P.2).symm ▸ (Ideal.over_under (A := 𝓞 K) (P := P.1.1)).over⟩
    · rintro ⟨⟨P, hP⟩, hgP⟩ ⟨⟨Q, hQ⟩, hgQ⟩ hPQ
      simpa using hPQ
  have hordC_pos : (0 : ℝ) < orderOf σ * Nat.card (ConjClasses.mk σ).carrier := by
    have h₁ : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
    have : Nonempty (ConjClasses.mk σ).carrier := ⟨⟨σ, ConjClasses.mem_carrier_mk⟩⟩
    have h₂ : 0 < Nat.card (ConjClasses.mk σ).carrier := Nat.card_pos
    positivity
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def]
  set h : S' → ℝ := fun 𝔭 ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) with hh
  have hFsumm : Summable (fun P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥} ↦ h (g P)) :=
    (summable_prime_absNorm_rpow T₁set hs).congr fun P ↦ congrArg (· ^ (-s)) (hnormeq P)
  rw [tsum_congr (fun P ↦ congrArg (· ^ (-s)) (hnormeq P)),
    show (fun P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥} ↦
      (Ideal.absNorm (P.1.under (𝓞 K)) : ℝ) ^ (-s)) = (fun P ↦ h (g P)) from rfl,
    (hFsumm.hasSum.tsum_fiberwise g).tsum_eq.symm]
  have hequivfib : ∀ 𝔭 : S', (g ⁻¹' {𝔭} : Set _) ≃
      {P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥} // g P = 𝔭} :=
    fun 𝔭 ↦ Equiv.subtypeEquivRight fun _ ↦ Iff.rfl
  have hinner : ∀ 𝔭 : S', ∑' P : (g ⁻¹' {𝔭} : Set _), h (g P)
      = ((Nat.card Gal(L/K) : ℝ) / (orderOf σ * Nat.card (ConjClasses.mk σ).carrier)) * h 𝔭 := by
    intro 𝔭
    haveI := hfibfin 𝔭
    haveI : Finite (g ⁻¹' {𝔭} : Set _) := Finite.of_equiv _ (hequivfib 𝔭).symm
    letI := Fintype.ofFinite (g ⁻¹' {𝔭} : Set _)
    have hval : ∀ P : (g ⁻¹' {𝔭} : Set _), h (g P.1) = h 𝔭 := fun P ↦ by
      rw [show g P.1 = 𝔭 from P.2]
    rw [tsum_congr hval, tsum_fintype, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, nsmul_eq_mul]
    congr 1
    have hcard : (orderOf σ * Nat.card (ConjClasses.mk σ).carrier) *
        Nat.card (g ⁻¹' {𝔭} : Set _) = Nat.card Gal(L/K) := by
      rw [Nat.card_congr (hequivfib 𝔭)]
      exact hcardfib 𝔭
    rw [eq_div_iff hordC_pos.ne', mul_comm, ← hcard]
    push_cast
    ring
  rw [tsum_congr hinner, tsum_mul_left]

/-! ### Sub-lemmas for `primeIdealZetaSum_T2_div_univ_tendsto_zero` (LEAF B)

The complement `T₂ = T ∖ T₁` of degree-one primes splits into

* `A`: primes `P` of `𝓞 E` whose underlying `K`-prime `𝔭 = P ∩ 𝓞 K` is unramified in `L` but
  whose inertia degree `f(P ∣ 𝔭) ≥ 2`, so `N P = N𝔭^f ≥ N𝔭²` and `N P^{-s} ≤ N𝔭^{-2}`; and
* `B`: primes `P` over one of the finitely many `K`-primes ramified in `L`.

The sum over `A` is bounded by `[E:K]·Σ_𝔭 N𝔭^{-2}` (a fibre-counting argument: each `𝔭` has at
most `[E:K]` primes of `𝓞 E` above it, by `Ideal.card_primesOverFinset_le_finrank`), and the sum
over `B` is bounded by the finite cardinality of `B`. Both are constants in `s`, so
`Σ_{T₂} s ≤ C` for all `s > 1`, whence `Σ_{T₂}/Σ_univ^E → 0` since `Σ_univ^E → ∞`. -/

/-- **Fibre-counting bound for `ℝ≥0∞`-valued sums.** If every fibre `g ⁻¹' {y}` is finite with at
most `d` elements, then `Σ_b f(g b) ≤ d · Σ_y f y`: group `b` by its image `g b`, on each fibre
the summand is the constant `f y`, and the fibre has `≤ d` terms. -/
private theorem tsum_comp_le_card_fibre_mul {β γ : Type*} (g : β → γ) (f : γ → ℝ≥0∞) (d : ℕ)
    (hfin : ∀ y, Finite (g ⁻¹' {y} : Set β)) (hfib : ∀ y, Nat.card (g ⁻¹' {y} : Set β) ≤ d) :
    ∑' b, f (g b) ≤ (d : ℝ≥0∞) * ∑' y, f y := by
  rw [← ENNReal.tsum_fiberwise (fun b ↦ f (g b)) g, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum (fun y ↦ ?_)
  rw [tsum_congr (fun b : (g ⁻¹' {y} : Set β) ↦ by rw [b.2])]
  haveI := hfin y
  letI := Fintype.ofFinite (g ⁻¹' {y} : Set β)
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]
  gcongr
  exact_mod_cast hfib y

/-- **The degree-`≥ 2` part of `T₂` is bounded by a constant.** For `1 < s`, the partial sum over
the set `A` of primes `P` of `𝓞 E` whose underlying `K`-prime is unramified in `L` but of inertia
degree `≥ 2` is bounded by `[E:K]·Σ_𝔭 N𝔭^{-2}`. Indeed `N P = N𝔭^{f}` with `f ≥ 2`
(`Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver`), so `N P^{-s} ≤ N𝔭^{-2}` for `s ≥ 1` and
`N𝔭 ≥ 2`; grouping the `E`-primes by their `K`-prime fibre (each of size `≤ [E:K]` via
`Ideal.card_primesOverFinset_le_finrank`) gives the bound. -/
private theorem primeIdealZetaSum_degTwo_le [FiniteDimensional K L] (σ : Gal(L/K)) {s : ℝ}
    (hs : 1 < s) (Aset : Set (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))))
    (hA : Aset = {P | P.IsPrime ∧ P ≠ ⊥ ∧
      UnramifiedIn K L (P.under (𝓞 K)) ∧ 2 ≤ (P.under (𝓞 K)).inertiaDeg P}) :
    primeIdealZetaSum Aset s
      ≤ (Module.finrank K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) : ℝ)
        * primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) 2 := by
  letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : NoZeroSMulDivisors (𝓞 K)
      (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) :=
    ⟨fun {c x} h ↦ by
      rw [Algebra.smul_def, mul_eq_zero] at h
      exact h.imp (fun h ↦ RingOfIntegers.algebraMap.injective K _ (by rwa [map_zero])) id⟩
  set AP := {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
    P ∈ Aset ∧ P.IsPrime ∧ P ≠ ⊥} with hAP
  set KP := {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (univ : Set (Ideal (𝓞 K))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} with hKP
  have hunder : ∀ P : AP, (P.1.under (𝓞 K)).IsPrime ∧ P.1.under (𝓞 K) ≠ ⊥ := by
    rintro ⟨P, hPA, hPp, hPb⟩
    haveI := hPp
    exact ⟨inferInstance, Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPb⟩
  set g : AP → KP := fun P ↦ ⟨P.1.under (𝓞 K), mem_univ _, (hunder P).1, (hunder P).2⟩ with hg
  set FA : AP → ℝ≥0∞ := fun P ↦ ENNReal.ofReal ((Ideal.absNorm P.1 : ℝ) ^ (-s)) with hFA
  set FK : KP → ℝ≥0∞ := fun 𝔭 ↦ ENNReal.ofReal ((Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ))) with hFK
  have hterm : ∀ P : AP, FA P ≤ FK (g P) := by
    rintro ⟨P, hPA, hPp, hPb⟩
    haveI := hPp
    rw [hA] at hPA
    obtain ⟨-, -, _, hdeg⟩ := hPA
    have hppr : (P.under (𝓞 K)).IsPrime := inferInstance
    have hpbot : P.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPb
    haveI : P.LiesOver (P.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := P)
    have hpow := Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver P (P.under (𝓞 K)) hppr hpbot
    have hn2 : 2 ≤ Ideal.absNorm (P.under (𝓞 K)) := by
      have h0 : Ideal.absNorm (P.under (𝓞 K)) ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hpbot
      have h1 : Ideal.absNorm (P.under (𝓞 K)) ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr hppr.ne_top
      omega
    change ENNReal.ofReal ((Ideal.absNorm P : ℝ) ^ (-s))
      ≤ ENNReal.ofReal ((Ideal.absNorm (P.under (𝓞 K)) : ℝ) ^ (-(2 : ℝ)))
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hpow]
    set n := Ideal.absNorm (P.under (𝓞 K))
    set f := (P.under (𝓞 K)).inertiaDeg P
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_of_lt hn2
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    rw [Nat.cast_pow, ← Real.rpow_natCast (n : ℝ) f, ← Real.rpow_mul hnpos.le]
    refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
    have hfs : (2 : ℝ) * 1 ≤ (f : ℝ) * s :=
      mul_le_mul (by exact_mod_cast hdeg) hs.le (by norm_num) (by positivity)
    nlinarith [hfs]
  have hinj : ∀ 𝔭 : KP, Finite (g ⁻¹' {𝔭} : Set AP) ∧
      Nat.card (g ⁻¹' {𝔭} : Set AP)
        ≤ Module.finrank K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) := by
    intro 𝔭
    haveI := 𝔭.2.2.1
    haveI : 𝔭.1.IsMaximal := 𝔭.2.2.1.isMaximal 𝔭.2.2.2
    set PO := {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
      P.IsPrime ∧ P.LiesOver 𝔭.1} with hPO
    have hmem : ∀ P : (g ⁻¹' {𝔭} : Set AP), P.1.1.IsPrime ∧ P.1.1.LiesOver 𝔭.1 := by
      rintro ⟨⟨P, hPA, hPp, hPb⟩, hgP⟩
      haveI := hPp
      have hund : P.under (𝓞 K) = 𝔭.1 := congrArg Subtype.val hgP
      exact ⟨hPp, ⟨hund ▸ (Ideal.over_under (A := 𝓞 K) (P := P)).over⟩⟩
    set hmap : (g ⁻¹' {𝔭} : Set AP) → PO := fun P ↦ ⟨P.1.1, hmem P⟩ with hhmap
    have hmapinj : Function.Injective hmap := by
      rintro ⟨⟨P, hP⟩, hgP⟩ ⟨⟨Q, hQ⟩, hgQ⟩ hPQ
      have hPeqQ : P = Q := congrArg Subtype.val hPQ
      exact Subtype.ext (Subtype.ext hPeqQ)
    haveI hPOfin : Finite PO :=
      (IsDedekindDomain.primesOver_finite 𝔭.1
        (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))).to_subtype
    refine ⟨Finite.of_injective hmap hmapinj, (Nat.card_le_card_of_injective hmap hmapinj).trans ?_⟩
    have hcard : Nat.card PO
        = (IsDedekindDomain.primesOverFinset 𝔭.1
            (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))).card := by
      rw [show PO = ↥(𝔭.1.primesOver
          (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) from rfl,
        Nat.card_coe_set_eq, ← IsDedekindDomain.coe_primesOverFinset 𝔭.2.2.2,
        Set.ncard_coe_finset]
    rw [hcard]
    exact Ideal.card_primesOverFinset_le_finrank (R := 𝓞 K)
      (S := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
      (K := K) (L := ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) 𝔭.2.2.2
  have hsummA : Summable (fun P : AP ↦ (Ideal.absNorm P.1 : ℝ) ^ (-s)) :=
    summable_prime_absNorm_rpow Aset (by linarith)
  have hsummK : Summable (fun 𝔭 : KP ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ))) :=
    summable_prime_absNorm_rpow (univ : Set (Ideal (𝓞 K))) (by norm_num)
  have hnonnegA : ∀ P : AP, 0 ≤ (Ideal.absNorm P.1 : ℝ) ^ (-s) := fun P ↦ by positivity
  have hnonnegK : ∀ 𝔭 : KP, 0 ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ)) := fun 𝔭 ↦ by positivity
  have hAreal : primeIdealZetaSum Aset s = (∑' P : AP, FA P).toReal := by
    rw [primeIdealZetaSum_def, hFA, ← ENNReal.ofReal_tsum_of_nonneg hnonnegA hsummA,
      ENNReal.toReal_ofReal (tsum_nonneg hnonnegA)]
  have hKreal : primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) 2 = (∑' 𝔭 : KP, FK 𝔭).toReal := by
    rw [primeIdealZetaSum_def, hFK, ← ENNReal.ofReal_tsum_of_nonneg hnonnegK hsummK,
      ENNReal.toReal_ofReal (tsum_nonneg hnonnegK)]
  have hchain : ∑' P : AP, FA P
      ≤ (Module.finrank K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) : ℝ≥0∞)
        * ∑' 𝔭 : KP, FK 𝔭 :=
    calc ∑' P : AP, FA P ≤ ∑' P : AP, FK (g P) := ENNReal.tsum_le_tsum hterm
      _ ≤ (Module.finrank K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) : ℝ≥0∞)
            * ∑' 𝔭 : KP, FK 𝔭 :=
          tsum_comp_le_card_fibre_mul g FK _ (fun 𝔭 ↦ (hinj 𝔭).1) (fun 𝔭 ↦ (hinj 𝔭).2)
  rw [hAreal, hKreal]
  have hfin : ∑' 𝔭 : KP, FK 𝔭 ≠ ∞ := by
    rw [hFK, ← ENNReal.ofReal_tsum_of_nonneg hnonnegK hsummK]
    exact ENNReal.ofReal_ne_top
  have hbtop : (Module.finrank K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) : ℝ≥0∞)
      * ∑' 𝔭 : KP, FK 𝔭 ≠ ∞ := ENNReal.mul_ne_top (by simp) hfin
  refine le_of_le_of_eq (ENNReal.toReal_mono hbtop hchain) ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]

/-- **The ramified part of `T₂` is a finite set.** The primes `P` of `𝓞 E` whose underlying
`K`-prime is ramified in `L` lie over one of the finitely many ramified `K`-primes
(`finite_ramifiedIn`), and each `K`-prime has finitely many primes of `𝓞 E` above it
(`IsDedekindDomain.primesOver_finite`); hence the set is finite. -/
private theorem ramifiedBelow_finite [FiniteDimensional K L] (σ : Gal(L/K))
    (Bset : Set (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))))
    (hB : Bset = {P | P.IsPrime ∧ P ≠ ⊥ ∧ ¬ UnramifiedIn K L (P.under (𝓞 K))}) :
    Bset.Finite := by
  apply Set.Finite.subset ((finite_ramifiedIn K L).biUnion (t := fun 𝔭 ↦
    (𝔭.primesOver (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))) ?_)
  · rw [hB]
    rintro P ⟨hPp, hPb, hPnu⟩
    haveI := hPp
    exact Set.mem_biUnion ⟨inferInstance, Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPb, hPnu⟩
      ⟨hPp, Ideal.over_under (A := 𝓞 K) (P := P)⟩
  · rintro 𝔭 ⟨hp, hb, -⟩
    haveI := hp
    haveI : 𝔭.IsMaximal := hp.isMaximal hb
    exact IsDedekindDomain.primesOver_finite 𝔭 _

/-- **LEAF B: the degree-`≥ 2` part of `T` vanishes in the density ratio** (Sharifi 7.2.2
p. 143, "`Σ_𝔭 N𝔭⁻ˢ ~ Σ_P NP⁻ˢ`"). The complement `T₂ = T ∖ T₁` consists of primes `P` of `𝓞 E`
that are either of inertia degree `≥ 2` over `K` (so `N P = N(P ∩ 𝓞 K)^{≥2}`, contributing a
`Θ(Σ_𝔭 N𝔭⁻²ˢ)` tail that is bounded near `s = 1`) or lie over one of the finitely many primes
of `𝓞 K` ramified in `L` (a finite contribution).  Both are `o(Σ_univ^E)` since
`Σ_univ^E → ∞`, so `Σ_{T₂}/Σ_univ^E → 0`.

This is the asymptotic content that the (false) exact identity
`Σ_S = (f|C|/|G|)·Σ_T` elided: the relation `Σ_𝔭 N𝔭⁻ˢ ~ Σ_P NP⁻ˢ` holds only in the
`s → 1⁺` limit, with the higher-degree primes of `E` over `K` forming the discrepancy. -/
private theorem primeIdealZetaSum_T2_div_univ_tendsto_zero
    [FiniteDimensional K L] (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (T₂set : Set (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))))
    (hT₂ : T₂set = {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
        P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
        frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
          = ConjClasses.mk σE} \
      {P ∈ {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
          P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
          frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
            = ConjClasses.mk σE} |
        (P.under (𝓞 K)).inertiaDeg P = 1 ∧ UnramifiedIn K L (P.under (𝓞 K))}) :
    Tendsto (fun s : ℝ ↦ primeIdealZetaSum T₂set s
      / primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField
        (Subgroup.zpowers σ))))) s) (𝓝[>] 1) (𝓝 0) := by
  haveI : IsGalois ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    IsGalois.tower_top_intermediateField _
  set Aset := {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
    P.IsPrime ∧ P ≠ ⊥ ∧ UnramifiedIn K L (P.under (𝓞 K)) ∧
    2 ≤ (P.under (𝓞 K)).inertiaDeg P} with hAdef
  set Bset := {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
    P.IsPrime ∧ P ≠ ⊥ ∧ ¬ UnramifiedIn K L (P.under (𝓞 K))} with hBdef
  have hsub : T₂set ⊆ Aset ∪ Bset := by
    rw [hT₂]
    rintro P ⟨⟨hPp, hPunr, hPfr⟩, hPnotT1⟩
    haveI := hPp
    simp only [Set.mem_setOf_eq, not_and] at hPnotT1
    have hPb : P ≠ ⊥ := UnramifiedIn.ne_bot _ L hPunr
    by_cases hunrK : UnramifiedIn K L (P.under (𝓞 K))
    · refine Or.inl ⟨hPp, hPb, hunrK, ?_⟩
      have hdegne : (P.under (𝓞 K)).inertiaDeg P ≠ 1 := fun hdeg1 ↦
        hPnotT1 ⟨hPp, hPunr, hPfr⟩ hdeg1 hunrK
      have hppr : (P.under (𝓞 K)).IsPrime := inferInstance
      haveI : (P.under (𝓞 K)).IsMaximal :=
        hppr.isMaximal (Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPb)
      haveI : P.LiesOver (P.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := P)
      have hpos : 0 < (P.under (𝓞 K)).inertiaDeg P := Ideal.inertiaDeg_pos' _ _
      omega
    · exact Or.inr ⟨hPp, hPb, hunrK⟩
  have hdisj : Disjoint Aset Bset := by
    rw [Set.disjoint_left]
    rintro P ⟨-, -, hunrK, -⟩ ⟨-, -, hnunrK⟩
    exact hnunrK hunrK
  have hBfin : Bset.Finite := ramifiedBelow_finite σ Bset hBdef
  refine tendsto_primeIdealZetaSum_div_univ_zero_of_le_const
    (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) T₂set
    ((Module.finrank K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) : ℝ)
        * primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) 2
      + (Nat.card {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
          P ∈ Bset ∧ P.IsPrime ∧ P ≠ ⊥} : ℝ)) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  calc primeIdealZetaSum T₂set s ≤ primeIdealZetaSum (Aset ∪ Bset) s :=
        primeIdealZetaSum_le_of_subset hsub hs
    _ = primeIdealZetaSum Aset s + primeIdealZetaSum Bset s :=
        primeIdealZetaSum_union_of_disjoint hdisj hs
    _ ≤ _ := add_le_add (primeIdealZetaSum_degTwo_le σ hs Aset hAdef)
        (primeIdealZetaSum_le_card_of_finite
          (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) hBfin (by linarith))

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
hypothesis `hσE` records that `σ_E` restricts to `σ` over `K` (so `σ_E`
generates `Gal(L/E)` and a prime with `Frob^E_𝔓 = σ_E` has `Frob^K_𝔓 = σ`);
the hypothesis `hab` is the abelian-case output for `L/E` from
`chebotarev_abelian`. -/
theorem density_lift_through_fixedField
    [FiniteDimensional K L] (σ : Gal(L/K)) (E : IntermediateField K L) (σE : Gal(L/E))
    (hσE : letI : IsScalarTower K ↥E L := E.isScalarTower_mid'; σE.restrictScalars K = σ)
    (_hEfix : E = IntermediateField.fixedField (Subgroup.zpowers σ))
    (_hab : HasDirichletDensity
        {P : Ideal (𝓞 ↥E) | P.IsPrime ∧ UnramifiedIn ↥E L P ∧
          frobeniusClass ↥E L P = ConjClasses.mk σE}
        ((Nat.card Gal(L/E) : ℝ)⁻¹)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ}
      ((Nat.card (ConjClasses.mk σ).carrier : ℝ) / Nat.card Gal(L/K)) := by
  subst _hEfix
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  have horder : (Nat.card Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) : ℝ)
      = orderOf σ := by
    rw [← Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)).toEquiv,
      Nat.card_zpowers]
  haveI : IsMulCommutative Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
    .of_comm fun a b ↦ by
      obtain ⟨x, rfl⟩ := (IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)).surjective a
      obtain ⟨y, rfl⟩ := (IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)).surjective b
      rw [← map_mul _ x y, ← map_mul _ y x, mul_comm' x y]
  set Tset := {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
    P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
    frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
      = ConjClasses.mk σE} with hTset
  set T₁set := {P ∈ Tset | (P.under (𝓞 K)).inertiaDeg P = 1 ∧ UnramifiedIn K L (P.under (𝓞 K))}
    with hT₁set
  set T₂set := Tset \ T₁set with hT₂set
  have horderE' : orderOf σ = Nat.card Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
      := by
    rw [← Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)).toEquiv,
      Nat.card_zpowers]
  have hT₁sub : T₁set ⊆ Tset := fun x hx ↦ hx.1
  have hsplit : ∀ {s : ℝ}, 1 < s → primeIdealZetaSum Tset s
      = primeIdealZetaSum T₁set s + primeIdealZetaSum T₂set s := by
    intro s hs
    rw [(Set.union_diff_cancel hT₁sub).symm,
      primeIdealZetaSum_union_of_disjoint (Set.disjoint_sdiff_right) hs]
  have hleafB : Tendsto (fun s : ℝ ↦ primeIdealZetaSum T₂set s
      / primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField
        (Subgroup.zpowers σ))))) s) (𝓝[>] 1) (𝓝 0) :=
    primeIdealZetaSum_T2_div_univ_tendsto_zero σ σE T₂set hT₂set
  have htendT₁ : Tendsto (fun s : ℝ ↦ primeIdealZetaSum T₁set s
      / primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField
        (Subgroup.zpowers σ))))) s) (𝓝[>] 1)
      (𝓝 ((Nat.card Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) : ℝ)⁻¹)) := by
    have := _hab.sub hleafB
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [mem_Ioi] at hs
    rw [hsplit hs]
    ring
  rw [HasDirichletDensity]
  have hmain : Tendsto
      (fun s : ℝ ↦ ((orderOf σ : ℝ) * Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K))
        * (primeIdealZetaSum T₁set s
              / primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField
                (Subgroup.zpowers σ))))) s)
          * (primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField
              (Subgroup.zpowers σ))))) s
              / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s))
      (𝓝[>] 1)
      (𝓝 (((orderOf σ : ℝ) * Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K))
        * (Nat.card Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) : ℝ)⁻¹ * 1)) :=
    ((htendT₁.const_mul _).mul (univ_ratio_E_K_tendsto_one _))
  have hval : ((orderOf σ : ℝ) * Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K))
        * (Nat.card Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) : ℝ)⁻¹ * 1
      = (Nat.card (ConjClasses.mk σ).carrier : ℝ) / Nat.card Gal(L/K) := by
    have hordpos : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
    rw [horder, mul_one]
    field_simp
  rw [hval] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    (primeIdealZetaSum_univ_tendsto_atTop (↥(IntermediateField.fixedField
      (Subgroup.zpowers σ)))).eventually_gt_atTop 0] with s hs hEpos
  simp only [mem_Ioi] at hs
  have hT₁flat : T₁set = {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
      P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
      frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P = ConjClasses.mk σE ∧
      (P.under (𝓞 K)).inertiaDeg P = 1 ∧ UnramifiedIn K L (P.under (𝓞 K))} := by
    rw [hT₁set, hTset]
    ext P
    simp only [Set.mem_setOf_eq]
    tauto
  have hleafA := primeIdealZetaSum_fibre_eq_smul σ σE hσE horderE' hs
  rw [← hT₁flat] at hleafA
  have hc_pos : (0 : ℝ) < orderOf σ * Nat.card (ConjClasses.mk σ).carrier := by
    have h₁ : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
    have : Nonempty (ConjClasses.mk σ).carrier := ⟨⟨σ, ConjClasses.mem_carrier_mk⟩⟩
    have h₂ : 0 < Nat.card (ConjClasses.mk σ).carrier := Nat.card_pos
    positivity
  have hG_pos : (0 : ℝ) < Nat.card Gal(L/K) := by exact_mod_cast Nat.card_pos
  have hAB : ((orderOf σ : ℝ) * Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K))
      * ((Nat.card Gal(L/K) : ℝ) / (orderOf σ * Nat.card (ConjClasses.mk σ).carrier)) = 1 := by
    rw [div_mul_div_comm, mul_comm ((orderOf σ : ℝ) * _), div_self (by positivity)]
  have hSeq : primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk σ} s
      = ((orderOf σ : ℝ) * Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K))
        * primeIdealZetaSum T₁set s := by
    rw [hleafA, ← mul_assoc, hAB, one_mul]
  rw [hSeq, mul_assoc ((orderOf σ : ℝ) * Nat.card (ConjClasses.mk σ).carrier / Nat.card Gal(L/K)),
    div_mul_div_cancel₀ hEpos.ne']
  ring

end Chebotarev
