module

public import CebotarevDensity.Frobenius
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-!
# The cyclotomic Frobenius as a norm residue, and Frobenii generate

Two arithmetic inputs of the Frobenius-fibre equidistribution (Gap B / L2), placed *below*
`ZetaProduct.lean` in the import order (the lemma `cyclotomic_frobenius_acts_as_norm_power`
currently lives in `Cyclotomic.lean`, which imports `ZetaProduct.lean` — the relevant content
is (re)stated here so that `ZetaProduct.lean` can consume it without an import cycle).

* `autToPow_frobeniusClass_out`: for `L = K(μ_m)` and a prime `𝔭` of `K` unramified in `L`
  with `N𝔭` coprime to `m`, the image of the Frobenius under the (faithful) cyclotomic
  character `Gal(L/K) →* (ℤ/m)ˣ` (`IsPrimitiveRoot.autToPow`) is the norm residue
  `N𝔭 mod m`. This is the multiplicative-dictionary form of the element-level fact
  `Frob_𝔭(ζ) = ζ^{N𝔭}` (Sharifi Prop. 7.1.15-adjacent; the element-level statement is
  `cyclotomic_frobenius_acts_as_norm_power`).

* `subgroup_eq_top_of_forall_frobenius_mem`: **Frobenii generate the Galois group** — a
  subgroup of `Gal(L/K)` containing the Frobenius representative of every unramified prime
  is the whole group. CFT-free proof via the project's zeta asymptotics: the fixed field `F`
  of such a subgroup has every unramified prime of `K` split completely; comparing
  `Σ_𝔭 N𝔭^{-s} ~ log (1/(s-1))` for `K` and for `F` (`primeIdealZetaSum_univ_tendsto_log`,
  both fields) against the `[F:K]`-fold multiplicity of split primes forces `[F:K] = 1`.
  (Used to realize every residue in the image of the cyclotomic character as a product of
  prime norm residues — the input `hS` of the κ-uniformity transfer.)
-/

@[expose] public section

noncomputable section

namespace Chebotarev

open NumberField

/-- Sharifi 7.2.1 step (i) — cyclotomic Frobenius formula (p. 142).
Verbatim source quote: "we have φ_𝔭(ζ_m) = ζ_m^{N𝔭} for a primitive mth root of
unity ζ_m". The coprimality `hcop : (N𝔭).Coprime m` is Sharifi's implicit
hypothesis made explicit — it is genuinely necessary: if `μ_m ⊆ K` then `L = K`,
`φ_𝔭 = id`, and *every* prime is unramified, yet the formula would force
`N𝔭 ≡ 1 (mod m)`. For a nontrivial extension it is the statement that an
unramified prime does not divide `m`; mathlib currently provides that only over
`ℚ` (`IsCyclotomicExtension.Rat.*`), so over a general base `K` the caller
supplies the coprimality.

(Relocated here from `Cyclotomic.lean` so that `ZetaProduct.lean` — which `Cyclotomic.lean`
imports — can consume it without an import cycle.) -/
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
    change Ideal.absNorm 𝔭 = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K))
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

/-- Powers of a primitive `n`-th root of unity agree iff the exponents are congruent mod `n`
(the easy direction: equal powers force congruent exponents). Reduce both exponents mod `n`
(killing `μ^n = 1`) and apply injectivity of `i ↦ μ^i` below `n` (`IsPrimitiveRoot.pow_inj`). -/
private theorem pow_natModEq_of_pow_eq {S : Type*} [CommRing S] [IsDomain S] {μ : S} {n : ℕ}
    [NeZero n] (hμ : IsPrimitiveRoot μ n) {a b : ℕ} (h : μ ^ a = μ ^ b) : a ≡ b [MOD n] := by
  have hpos : 0 < n := NeZero.pos n
  have ha : μ ^ a = μ ^ (a % n) := by
    conv_lhs => rw [← Nat.div_add_mod a n, pow_add, pow_mul, hμ.pow_eq_one, one_pow, one_mul]
  have hb : μ ^ b = μ ^ (b % n) := by
    conv_lhs => rw [← Nat.div_add_mod b n, pow_add, pow_mul, hμ.pow_eq_one, one_pow, one_mul]
  exact hμ.pow_inj (Nat.mod_lt a hpos) (Nat.mod_lt b hpos) (by rw [← ha, ← hb, h])

/-- A `MonoidHom` into a commutative group is constant on conjugacy classes: conjugate elements
have the same image (cancel the conjugator, which commutes with everything in the target). -/
private theorem MonoidHom.map_eq_of_isConj {G H : Type*} [Group G] [CommGroup H] (f : G →* H)
    {a b : G} (h : IsConj a b) : f a = f b := by
  obtain ⟨c, hc⟩ := h
  have hcc : f (↑c * a) = f (b * ↑c) := by rw [hc.eq]
  rw [map_mul, map_mul] at hcc
  exact mul_right_cancel ((mul_comm (f ↑c) (f a)).symm ▸ hcc)

/-- **The cyclotomic Frobenius is the norm residue** (multiplicative form). For `L = K(μ_m)`,
a primitive `m`-th root `ζ` of unity in `L`, and a prime `𝔭` of `K` unramified in `L` with
`N𝔭` coprime to `m`, the cyclotomic character `IsPrimitiveRoot.autToPow` sends the Frobenius
representative `(frobeniusClass K L 𝔭).out` to the unit `N𝔭 mod m`. Follows from the
element-level action `Frob_𝔭 ζ = ζ^{N𝔭}` (`cyclotomic_frobenius_acts_as_norm_power`), which pins
the `autToPow` value by definition. `autToPow` lands in the abelian group `(ZMod m)ˣ`, so it is
conjugation-invariant: the value on the class representative `.out` equals the value on an honest
arithmetic Frobenius `arithFrobAt 𝔓` at some prime `𝔓 | 𝔭`, to which the element-level action
applies. -/
theorem autToPow_frobeniusClass_out
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] [FiniteDimensional K L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ m) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (hunr : UnramifiedIn K L 𝔭) (hcop : (Ideal.absNorm 𝔭).Coprime m) :
    hζ.autToPow K ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) =
      ZMod.unitOfCoprime (Ideal.absNorm 𝔭) hcop := by
  -- An honest Frobenius `φ = arithFrobAt 𝔓` at a chosen prime `𝔓 | 𝔭`.
  obtain ⟨𝔓, h𝔓prime, h𝔓lo, _⟩ := exists_prime_liesOver K L 𝔭 (UnramifiedIn.ne_bot K L hunr)
  haveI := h𝔓prime
  haveI := h𝔓lo
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
    (ne_bot_of_ramificationIdx_eq_one K L (UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓 h𝔓lo))
  set φ : L ≃ₐ[K] L := arithFrobAt (𝓞 K) Gal(L/K) 𝔓 with hφ
  -- `.out` is conjugate to `φ`, and `autToPow` (into the abelian `(ZMod m)ˣ`) is conj-invariant.
  have hclass : frobeniusClass K L 𝔭 = ConjClasses.mk φ :=
    frobeniusClass_eq_mk_of_isArithFrobAt K L 𝔭 hunr φ 𝔓
      (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) h𝔓lo
  have hconj : IsConj ((frobeniusClass K L 𝔭).out) φ := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj, ← hclass, ConjClasses.mk, Quotient.out_eq]
  rw [MonoidHom.map_eq_of_isConj (hζ.autToPow K) hconj]
  -- Element-level action `φ ζ = ζ ^ N𝔭`, then the multiplicative dictionary.
  have hact : φ ζ = ζ ^ Ideal.absNorm 𝔭 :=
    cyclotomic_frobenius_acts_as_norm_power K L m 𝔭 hunr hcop 𝔓 h𝔓lo ζ
      ((mem_primitiveRoots (NeZero.pos m)).mpr hζ)
  -- `ζ ^ (autToPow φ).val = φ ζ = ζ ^ N𝔭` pins `(autToPow φ).val ≡ N𝔭 [MOD m]`.
  have hspec := hζ.autToPow_spec K φ
  rw [hact] at hspec
  have hmod : ((hζ.autToPow K φ : ZMod m)).val ≡ Ideal.absNorm 𝔭 [MOD m] :=
    pow_natModEq_of_pow_eq hζ hspec
  apply Units.ext
  rw [ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val ((hζ.autToPow K φ : (ZMod m)ˣ) : ZMod m)]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod

/-! ### Sub-lemmas for `finrank_fixedField_le_one_of_forall_frobenius_mem`

The deep splitting/comparison content of the fixed-field reduction, established CFT-free. Step (A)
(splitting) factors through a *downward Frobenius restriction* lemma
(`isArithFrobAt_restrictNormal`,
the mirror of the upward `arithFrobAt_restrictScalars_eq` in `Main.lean`, replicated here because
`Main.lean` is below this file in the import order); step (B) (comparison) regroups the `F`-prime
zeta sum along the fibration `𝔮 ↦ 𝔮 ∩ 𝓞 K`; step (C) (limit) divides by `log(1/(s-1))` and passes
to the limit. -/

open scoped Pointwise in
/-- **Action intertwining for the normal restriction.** For an intermediate field `F` Galois over
`K`, the embedding `𝓞 F → 𝓞 L` intertwines the action of `σ : Gal(L/K)` with that of its normal
restriction `σ ↾ F : Gal(F/K)`: `σ • algebraMap (𝓞 F) (𝓞 L) y = algebraMap (𝓞 F) (𝓞 L) (σ↾F • y)`.
Checked after the (injective) embedding `𝓞 L → L`, via `AlgEquiv.restrictNormal_commutes`. -/
private theorem smul_algebraMap_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (F : IntermediateField K L) [IsGalois K F]
    (σ : L ≃ₐ[K] L) (y : 𝓞 F) :
    haveI : IsScalarTower K F L := F.isScalarTower_mid'
    σ • (algebraMap (𝓞 F) (𝓞 L) y) = algebraMap (𝓞 F) (𝓞 L) ((σ.restrictNormal F) • y) := by
  haveI : IsScalarTower K F L := F.isScalarTower_mid'
  have hbridgeL : ∀ (g : L ≃ₐ[K] L) (x : 𝓞 L), ((g • x : 𝓞 L) : L) = g • (x : L) := fun g x =>
    by simpa [Algebra.smul_def] using
      (smul_distrib_smul (G := L ≃ₐ[K] L) (R := 𝓞 L) (S := L) g x 1).symm
  have hbridgeF : ∀ (g : F ≃ₐ[K] F) (z : 𝓞 F), ((g • z : 𝓞 F) : F) = g • ((z : F)) := fun g z =>
    by simpa [Algebra.smul_def] using
      (smul_distrib_smul (G := F ≃ₐ[K] F) (R := 𝓞 F) (S := F) g z 1).symm
  have hcoe : ∀ z : 𝓞 F, ((algebraMap (𝓞 F) (𝓞 L) z : 𝓞 L) : L) = algebraMap F L (z : F) :=
    fun z => by
      rw [show ((algebraMap (𝓞 F) (𝓞 L) z : 𝓞 L) : L)
            = algebraMap (𝓞 L) L (algebraMap (𝓞 F) (𝓞 L) z) from rfl,
        ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 L) L,
        show ((z : F)) = algebraMap (𝓞 F) F z from rfl,
        ← IsScalarTower.algebraMap_apply (𝓞 F) F L]
  rw [RingOfIntegers.ext_iff]
  change ((σ • algebraMap (𝓞 F) (𝓞 L) y : 𝓞 L) : L)
      = ((algebraMap (𝓞 F) (𝓞 L) ((σ.restrictNormal F) • y) : 𝓞 L) : L)
  rw [hbridgeL, hcoe y, hcoe ((σ.restrictNormal F) • y), hbridgeF, AlgEquiv.smul_def,
    AlgEquiv.smul_def, AlgEquiv.restrictNormal_commutes]

/-- **Downward Frobenius restriction** (mirror of `Main.lean`'s upward
`arithFrobAt_restrictScalars_eq`). If `σ : Gal(L/K)` is an arithmetic Frobenius at a prime `𝔓` of
`𝓞 L`, then its normal restriction `σ ↾ F : Gal(F/K)` is an arithmetic Frobenius at `𝔮 = 𝔓 ∩ 𝓞 F`.
The defining congruence `σ x ≡ x^{N𝔭} (mod 𝔓)` descends along `𝓞 F → 𝓞 L` to `𝓞 F`, using the
action intertwining (`smul_algebraMap_eq`) and `(𝔓 ∩ 𝓞 F) ∩ 𝓞 K = 𝔓 ∩ 𝓞 K` (`Ideal.under_under`). -/
private theorem isArithFrobAt_restrictNormal
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (F : IntermediateField K L) [IsGalois K F] (σ : L ≃ₐ[K] L)
    (𝔓 : Ideal (𝓞 L)) (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) :
    haveI : IsScalarTower K F L := F.isScalarTower_mid'
    IsArithFrobAt (𝓞 K) (σ.restrictNormal F) (𝔓.under (𝓞 F)) := by
  haveI : IsScalarTower K F L := F.isScalarTower_mid'
  haveI : IsScalarTower (𝓞 K) (𝓞 F) (𝓞 L) := inferInstance
  have hunder : (𝔓.under (𝓞 F)).under (𝓞 K) = 𝔓.under (𝓞 K) := Ideal.under_under 𝔓
  intro y
  rw [hunder, Ideal.under, Ideal.mem_comap, map_sub, map_pow]
  rw [show (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 F) (σ.restrictNormal F)) y
        = (σ.restrictNormal F) • y from rfl, ← smul_algebraMap_eq K L F σ y]
  exact hσ (algebraMap (𝓞 F) (𝓞 L) y)

/-- An automorphism of `L` fixing the intermediate field `F` pointwise (i.e. lying in the fixing
subgroup of `F`) restricts to the identity of `F`. -/
private theorem restrictNormal_eq_one_of_mem_fixingSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (F : IntermediateField K L) [Normal K F] (g : L ≃ₐ[K] L) (hg : g ∈ F.fixingSubgroup) :
    g.restrictNormal F = 1 := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hg
  ext x
  have key : ((g.restrictNormal F x : F) : L) = g (x : L) := AlgEquiv.restrictNormal_commutes g F x
  rw [AlgEquiv.one_apply]
  exact_mod_cast key.trans (hg (x : L) x.2)

/-- A prime of `𝓞 K` unramified in `L` is unramified in any intermediate field `F` Galois over `K`:
for a prime `𝔮` of `𝓞 F` over `𝔭`, pick `𝔓` of `𝓞 L` over `𝔮`; then `e(𝔮 ∣ 𝔭)` divides
`e(𝔓 ∣ 𝔭) = 1` (`Ideal.ramificationIdx_algebra_tower'`). -/
private theorem unramifiedIn_intermediateField
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (F : IntermediateField K L) [IsGalois K F]
    (𝔭 : Ideal (𝓞 K)) (hunr : UnramifiedIn K L 𝔭) :
    UnramifiedIn K (↥F) 𝔭 := by
  haveI : IsScalarTower K F L := F.isScalarTower_mid'
  haveI : IsScalarTower (𝓞 K) (𝓞 F) (𝓞 L) := inferInstance
  refine ⟨hunr.1, fun 𝔮 h𝔮max h𝔮lo => ?_⟩
  haveI := h𝔮lo
  haveI := h𝔮max.isPrime
  have h𝔮bot : 𝔮 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔮
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain h𝔮bot]
  obtain ⟨𝔓, h𝔓prime, h𝔓lo, -⟩ := exists_prime_liesOver (↥F) L 𝔮 h𝔮bot
  haveI := h𝔓prime
  haveI := h𝔓lo
  have h𝔮u : 𝔮.under (𝓞 K) = 𝔭 := h𝔮lo.over.symm
  have h𝔓Fu : 𝔓.under (𝓞 F) = 𝔮 := h𝔓lo.over.symm
  have h𝔓Ku : 𝔓.under (𝓞 K) = 𝔭 := by rw [← Ideal.under_under (B := 𝓞 F) 𝔓, h𝔓Fu, h𝔮u]
  haveI : 𝔓.LiesOver 𝔭 := ⟨by rw [h𝔓Ku]⟩
  have heL : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1 :=
    UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓 inferInstance
  have htower := Ideal.ramificationIdx_algebra_tower' (𝔓.under (𝓞 K)) (𝔓.under (𝓞 F)) 𝔓
  rw [heL, h𝔓Fu, h𝔓Ku] at htower
  rw [h𝔮u]
  exact Nat.eq_one_of_mul_eq_one_right htower.symm

/-- **Step (A): a Frobenius-trivial prime splits completely.** For `F = fixedField H` with `H`
abelian (hence normal) and a nonzero prime `𝔭` of `𝓞 K` unramified in `L` whose Frobenius
representative lies in `H`, the `F`-Frobenius class of `𝔭` is trivial: `frobeniusClass K F 𝔭 = [1]`.

In the abelian group `Gal(L/K)`, conjugate elements are equal, so a genuine Frobenius
`σ = arithFrobAt 𝔓` (`𝔓 ∣ 𝔭`) equals `(frobeniusClass 𝔭).out ∈ H = fixingSubgroup F`; its normal
restriction to `F` is the identity (`restrictNormal_eq_one_of_mem_fixingSubgroup`), and by the
downward restriction `isArithFrobAt_restrictNormal` it is the `F`-Frobenius at `𝔮 = 𝔓 ∩ 𝓞 F`. -/
private theorem frobeniusClass_fixedField_eq_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (hmem : ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    haveI : IsGalois K (IntermediateField.fixedField H) :=
      IsGalois.of_fixedField_normal_subgroup H
    frobeniusClass K (↥(IntermediateField.fixedField H)) 𝔭 = ConjClasses.mk 1 := by
  set F := IntermediateField.fixedField H with hF
  haveI : IsScalarTower K F L := F.isScalarTower_mid'
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  obtain ⟨𝔓, h𝔓p, h𝔓lo, -⟩ := exists_prime_liesOver K L 𝔭 (UnramifiedIn.ne_bot K L hunr)
  haveI := h𝔓p
  haveI := h𝔓lo
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
    (ne_bot_of_ramificationIdx_eq_one K L (UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓 h𝔓lo))
  set σ : L ≃ₐ[K] L := arithFrobAt (𝓞 K) Gal(L/K) 𝔓 with hσdef
  have hclass : frobeniusClass K L 𝔭 = ConjClasses.mk σ :=
    frobeniusClass_eq_mk_of_isArithFrobAt K L 𝔭 hunr σ 𝔓
      (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) h𝔓lo
  -- In the abelian group, `σ` and `(frobeniusClass 𝔭).out` are conjugate, hence equal.
  have hconj : IsConj σ ((frobeniusClass K L 𝔭).out) := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj, hclass.symm, ConjClasses.mk, Quotient.out_eq]
  have hσeq : σ = (frobeniusClass K L 𝔭).out := by
    obtain ⟨c, hc⟩ := hconj
    rw [SemiconjBy, mul_comm' (c : Gal(L/K)) σ] at hc
    exact mul_right_cancel hc
  have hσfix : σ ∈ F.fixingSubgroup := by
    rw [hF, IntermediateField.fixingSubgroup_fixedField]; exact hσeq ▸ hmem
  have hrestr : σ.restrictNormal F = 1 := restrictNormal_eq_one_of_mem_fixingSubgroup K L F σ hσfix
  have h𝔮lo : (𝔓.under (𝓞 F)).LiesOver 𝔭 :=
    ⟨by rw [← Ideal.under_under (B := 𝓞 F) 𝔓]; exact h𝔓lo.over⟩
  haveI := h𝔮lo
  have hfrobF : IsArithFrobAt (𝓞 K) (σ.restrictNormal F) (𝔓.under (𝓞 F)) :=
    isArithFrobAt_restrictNormal K L F σ 𝔓 (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓)
  rw [frobeniusClass_eq_mk_of_isArithFrobAt K (↥F) 𝔭 (unramifiedIn_intermediateField K L F 𝔭 hunr)
    (σ.restrictNormal F) (𝔓.under (𝓞 F)) hfrobF h𝔮lo, hrestr]

/-- **Step (A), count + norm form.** For `F = fixedField H` with the hypotheses of
`frobeniusClass_fixedField_eq_one`, the prime `𝔭` splits completely in `F`: there are exactly
`[F : K]` primes of `𝓞 F` above `𝔭`, and every prime `𝔮` of `𝓞 F` above `𝔭` has `N𝔮 = N𝔭`. The
count follows from `card_primesAbove_mul_finrank_eq` (`Frobenius.lean`) with residue degree
`ord (1 : Gal(F/K)) = 1` (`finrank_residue_eq_orderOf`); the norm from `f(𝔮 ∣ 𝔭) = 1` via
`Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver`. -/
private theorem splitsCompletely_fixedField
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (hmem : ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    Nat.card {𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)) //
          𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭 ∧ 𝔮 ≠ ⊥} = Module.finrank K ↥(IntermediateField.fixedField H)
      ∧ ∀ 𝔮 : Ideal (𝓞 ↥(IntermediateField.fixedField H)), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 →
          Ideal.absNorm 𝔮 = Ideal.absNorm 𝔭 := by
  set F := IntermediateField.fixedField H with hF
  haveI : IsScalarTower K F L := F.isScalarTower_mid'
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  have hunrF : UnramifiedIn K (↥F) 𝔭 := unramifiedIn_intermediateField K L F 𝔭 hunr
  have hpbot : 𝔭 ≠ ⊥ := UnramifiedIn.ne_bot K L hunr
  have hfc : frobeniusClass K (↥F) 𝔭 = ConjClasses.mk (1 : Gal(↥F/K)) :=
    frobeniusClass_fixedField_eq_one K L H 𝔭 hunr hmem
  -- residue degree of any prime `𝔮 ∣ 𝔭` is `ord (1) = 1`.
  have hresdeg : ∀ 𝔮 : Ideal (𝓞 F), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 →
      Module.finrank (𝓞 K ⧸ 𝔮.under (𝓞 K)) (𝓞 F ⧸ 𝔮) = 1 := fun 𝔮 h𝔮p h𝔮lo => by
    haveI := h𝔮p
    haveI := h𝔮lo
    rw [finrank_residue_eq_orderOf K (↥F) (1 : Gal(↥F/K)) (ConjClasses.mk 1) rfl 𝔭 hunrF hfc 𝔮
      h𝔮lo, orderOf_one]
  refine ⟨?_, fun 𝔮 h𝔮p h𝔮lo => ?_⟩
  · -- count: pick a prime above `𝔭`, apply `card_primesAbove_mul_finrank_eq`.
    obtain ⟨𝔮₀, h𝔮₀p, h𝔮₀lo, -⟩ := exists_prime_liesOver K (↥F) 𝔭 hpbot
    haveI := h𝔮₀p
    haveI := h𝔮₀lo
    have hcard := card_primesAbove_mul_finrank_eq K (↥F) 𝔭 hunrF 𝔮₀ h𝔮₀lo
    rw [hresdeg 𝔮₀ h𝔮₀p h𝔮₀lo, mul_one] at hcard
    rw [hcard, IsGalois.card_aut_eq_finrank K (↥F)]
  · -- norm: `N𝔮 = N(𝔮 ∩ 𝓞 K)^{f(𝔮∣𝔭)} = N𝔭^1`.
    haveI := h𝔮p
    haveI := h𝔮lo
    have hinert : (𝔮.under (𝓞 K)).inertiaDeg 𝔮 = 1 := by
      rw [Ideal.inertiaDeg_algebraMap]; exact hresdeg 𝔮 h𝔮p h𝔮lo
    have hunder : 𝔮.under (𝓞 K) = 𝔭 := h𝔮lo.over.symm
    rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔮 (𝔮.under (𝓞 K)) inferInstance
      (hunder ▸ hpbot), hinert, pow_one, hunder]

/-- **Step (B): the fibred zeta comparison.** For `F = fixedField H` and `1 < s`,
`[F : K] · Σ_{𝔭 unramified-in-L} N𝔭^{-s} ≤ Σ_{𝔮 of F} N𝔮^{-s}`. The `F`-prime sum restricted to
primes lying over an unramified-in-`L` base regroups (along `𝔮 ↦ 𝔮 ∩ 𝓞 K`, an
`Equiv.sigmaFiberEquiv`) into `Σ_𝔭 (#{𝔮 ∣ 𝔭}) · N𝔭^{-s} = [F : K] · Σ_𝔭 N𝔭^{-s}` by
`splitsCompletely_fixedField`, and that restricted sum is `≤` the full `F`-prime sum. -/
private theorem finrank_mul_unramified_le_univ
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (hH : ∀ 𝔭 : Ideal (𝓞 K), ∀ _ : 𝔭.IsPrime, 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 →
      ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H)
    {s : ℝ} (hs : 1 < s) :
    (Module.finrank K ↥(IntermediateField.fixedField H) : ℝ) *
        primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s
      ≤ primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 ↥(IntermediateField.fixedField H)))) s := by
  set F := IntermediateField.fixedField H with hF
  haveI : IsScalarTower K F L := F.isScalarTower_mid'
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  set U : Set (Ideal (𝓞 K)) := {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} with hU
  set V : Set (Ideal (𝓞 F)) := {𝔮 | 𝔮.IsPrime ∧ UnramifiedIn K L (𝔮.under (𝓞 K))} with hV
  -- packaged splitting data
  have hcount : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → UnramifiedIn K L 𝔭 →
      Nat.card {𝔮 : Ideal (𝓞 F) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭 ∧ 𝔮 ≠ ⊥}
        = Module.finrank K ↥F := fun 𝔭 h𝔭p h𝔭unr => by
    haveI := h𝔭p
    exact (splitsCompletely_fixedField K L H 𝔭 h𝔭unr
      (hH 𝔭 h𝔭p (UnramifiedIn.ne_bot K L h𝔭unr) h𝔭unr)).1
  have hnorm : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → UnramifiedIn K L 𝔭 →
      ∀ 𝔮 : Ideal (𝓞 F), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 →
        Ideal.absNorm 𝔮 = Ideal.absNorm 𝔭 := fun 𝔭 h𝔭p h𝔭unr 𝔮 h𝔮p h𝔮lo => by
    haveI := h𝔭p
    exact (splitsCompletely_fixedField K L H 𝔭 h𝔭unr
      (hH 𝔭 h𝔭p (UnramifiedIn.ne_bot K L h𝔭unr) h𝔭unr)).2 𝔮 h𝔮p h𝔮lo
  -- V ⊆ univ, so its sum is `≤` the universal `F`-prime sum.
  have hVle : primeIdealZetaSum V s ≤
      primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 F))) s :=
    primeIdealZetaSum_le_of_subset (Set.subset_univ V) hs
  rw [show primeIdealZetaSum V s = (Module.finrank K ↥F : ℝ) * primeIdealZetaSum U s
      from ?_] at hVle
  · exact hVle
  -- the regrouping equality
  set IU := {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ U ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}
  set IV := {𝔮 : Ideal (𝓞 F) // 𝔮 ∈ V ∧ 𝔮.IsPrime ∧ 𝔮 ≠ ⊥}
  have hφ_mem : ∀ 𝔮 : IV, (𝔮.1.under (𝓞 K)) ∈ U ∧ (𝔮.1.under (𝓞 K)).IsPrime
      ∧ (𝔮.1.under (𝓞 K)) ≠ ⊥ := fun 𝔮 => by
    haveI := 𝔮.2.2.1
    exact ⟨⟨inferInstance, 𝔮.2.1.2⟩, inferInstance, Ideal.IsIntegral.comap_ne_bot (𝓞 K) 𝔮.2.2.2⟩
  set φ : IV → IU := fun 𝔮 => ⟨𝔮.1.under (𝓞 K), hφ_mem 𝔮⟩ with hφdef
  have hsummV : Summable (fun 𝔮 : IV => (Ideal.absNorm 𝔮.1 : ℝ) ^ (-s)) :=
    summable_prime_absNorm_rpow V hs
  set e := Equiv.sigmaFiberEquiv φ
  have hsummSig : Summable (fun p : Σ 𝔭 : IU, {𝔮 : IV // φ 𝔮 = 𝔭} =>
      (Ideal.absNorm (e p).1 : ℝ) ^ (-s)) :=
    (e.summable_iff (f := fun 𝔮 : IV => (Ideal.absNorm 𝔮.1 : ℝ) ^ (-s))).mpr hsummV
  rw [primeIdealZetaSum_def, ← e.tsum_eq (fun 𝔮 : IV => (Ideal.absNorm (𝔮.1) : ℝ) ^ (-s)),
    hsummSig.tsum_sigma, primeIdealZetaSum_def, ← tsum_mul_left]
  refine tsum_congr (fun 𝔭 => ?_)
  haveI := 𝔭.2.2.1
  have hfibeq : {𝔮 : IV // φ 𝔮 = 𝔭} ≃
      {𝔮 : Ideal (𝓞 F) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭.1 ∧ 𝔮 ≠ ⊥} :=
    { toFun := fun x => ⟨x.1.1, x.1.2.2.1, ⟨(Subtype.ext_iff.mp x.2).symm⟩, x.1.2.2.2⟩
      invFun := fun y => ⟨⟨y.1, ⟨y.2.1, by
          haveI := y.2.1; haveI := y.2.2.1
          exact (y.2.2.1.over ▸ 𝔭.2.1.2 : UnramifiedIn K L (y.1.under (𝓞 K)))⟩, y.2.1, y.2.2.2⟩,
        Subtype.ext (haveI := y.2.2.1; y.2.2.1.over.symm)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hconst : ∀ x : {𝔮 : IV // φ 𝔮 = 𝔭}, (Ideal.absNorm (e ⟨𝔭, x⟩).1 : ℝ) ^ (-s)
      = (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := fun x => by
    change (Ideal.absNorm x.1.1 : ℝ) ^ (-s) = (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)
    rw [hnorm 𝔭.1 𝔭.2.2.1 𝔭.2.1.2 x.1.1 x.1.2.2.1 ⟨(Subtype.ext_iff.mp x.2).symm⟩]
  -- the target prime set is finite, and `hfibeq` transports finiteness to the fibre
  haveI : 𝔭.1.IsMaximal := 𝔭.2.2.1.isMaximal 𝔭.2.2.2
  haveI : Finite (𝔭.1.primesOver (𝓞 F)) :=
    (IsDedekindDomain.primesOver_finite 𝔭.1 (𝓞 F)).to_subtype
  haveI hfinHC : Finite {𝔮 : Ideal (𝓞 F) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭.1 ∧ 𝔮 ≠ ⊥} := by
    refine Finite.of_injective (β := 𝔭.1.primesOver (𝓞 F))
      (fun y => ⟨y.1, y.2.1, y.2.2.1⟩) (fun a b hab => ?_)
    apply Subtype.ext
    have : (⟨a.1, a.2.1, a.2.2.1⟩ : 𝔭.1.primesOver (𝓞 F)).1
        = (⟨b.1, b.2.1, b.2.2.1⟩ : 𝔭.1.primesOver (𝓞 F)).1 := congrArg Subtype.val hab
    exact this
  haveI : Finite {𝔮 : IV // φ 𝔮 = 𝔭} := Finite.of_equiv _ hfibeq.symm
  rw [tsum_congr hconst, tsum_const, Nat.card_congr hfibeq,
    hcount 𝔭.1 𝔭.2.2.1 𝔭.2.1.2, nsmul_eq_mul, mul_comm]

/-- The bare prime sum over the unramified primes is asymptotic to `log(1/(s-1))`: it differs from
the universal prime sum (`primeIdealZetaSum_univ_tendsto_log`) by the finitely-many ramified primes
(`finite_ramifiedIn`), whose contribution is bounded and so negligible against `log → ∞`. (Replayed
here from the private `Cyclotomic.lean` version, since `Cyclotomic.lean` imports this file.) -/
private theorem primeIdealZetaSum_unramified_div_log_tendsto_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] :
    Filter.Tendsto
      (fun s : ℝ ↦
        primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s
          / Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  set U : Set (Ideal (𝓞 K)) := {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} with hU
  set R : Set (Ideal (𝓞 K)) := {𝔭 | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭} with hR
  have hdisj : Disjoint U R :=
    Set.disjoint_left.mpr fun 𝔭 hu hr => hr.2.2 hu.2
  have hcover : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭 ∈ U ∪ R := fun 𝔭 hp hne => by
    by_cases hunr : UnramifiedIn K L 𝔭
    · exact Or.inl ⟨hp, hunr⟩
    · exact Or.inr ⟨hp, hne, hunr⟩
  have hRfin : R.Finite := finite_ramifiedIn K L
  obtain ⟨CR, hCR⟩ : ∃ CR : ℝ, ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1), primeIdealZetaSum R s ≤ CR := by
    refine ⟨Nat.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ R ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_Ioi] at hs
    exact primeIdealZetaSum_le_card_of_finite K hRfin (by linarith)
  have hRzero : Filter.Tendsto (fun s : ℝ ↦ primeIdealZetaSum R s / Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    have hL := tendsto_log_one_div_sub_one_atTop
    refine squeeze_zero_norm' ?_ (Filter.Tendsto.div_atTop tendsto_const_nhds hL (a := CR))
    filter_upwards [hCR, hL.eventually_gt_atTop 0] with s hub hLpos
    have hRnn : 0 ≤ primeIdealZetaSum R s := by
      rw [primeIdealZetaSum_def]; exact tsum_nonneg fun _ => Real.rpow_nonneg (by positivity) _
    rw [Real.norm_of_nonneg (div_nonneg hRnn hLpos.le)]
    gcongr
  have hcomb : Filter.Tendsto (fun s : ℝ ↦
      primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s / Real.log (1 / (s - 1))
        - primeIdealZetaSum R s / Real.log (1 / (s - 1))) (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
    simpa using (primeIdealZetaSum_univ_tendsto_log K).sub hRzero
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  have hadd : primeIdealZetaSum U s + primeIdealZetaSum R s =
      primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 K))) s := by
    rw [← primeIdealZetaSum_union_of_disjoint hdisj hs,
      primeIdealZetaSum_eq_univ_of_forall_prime_mem hcover s]
  rw [← sub_div, ← hadd, add_sub_cancel_right]

/-- **The fixed field of a Frobenius-saturated subgroup is trivial** (CFT-free analytic core of
`subgroup_eq_top_of_forall_frobenius_mem`, abelian case). If `H ≤ Gal(L/K)` contains the
Frobenius `(frobeniusClass 𝔭).out` of every nonzero unramified prime `𝔭`, then `F = fixedField H`
has degree `≤ 1` over `K`.

In the abelian case every Frobenius conjugacy class is a singleton, so `(frobeniusClass 𝔭).out`
is the genuine Frobenius and lies in `H = fixingSubgroup F` (`fixingSubgroup_fixedField`); hence
its restriction to `F` is trivial and `𝔭` splits completely in `F`, contributing `[F:K]` primes of
`F` of norm `N𝔭`. Comparing `Σ_{𝔮 of F} N𝔮^{-s}` with `[F:K] · Σ_{𝔭 of K unramified} N𝔭^{-s}`
(both `~ log(1/(s-1))`) forces `[F:K] ≤ 1`.

The reduction `[F:K] ≤ 1 ⇒ H = ⊤` is in `subgroup_eq_top_of_forall_frobenius_mem`. All
field-theoretic instances for `F = fixedField H` are available (`IsGalois K F` via
`IsGalois.of_fixedField_normal_subgroup` from `[IsMulCommutative]`; `NumberField F` via
`NumberField.of_intermediateField`; `FiniteDimensional K F`). The proof has three pieces:

* **(A) Splitting** (`splitsCompletely_fixedField`). For unramified `𝔭` with
  `(frobeniusClass K L 𝔭).out ∈ H`, the number of primes of `𝓞 F` above `𝔭` is `[F:K]`, each of
  absolute norm `N𝔭`. Routed through the *downward* Frobenius restriction
  `isArithFrobAt_restrictNormal` (the mirror of the *upward* `arithFrobAt_restrictScalars_eq` in
  `Main.lean`): composed with `σ_𝔭 ∈ H = fixingSubgroup F` it gives `frobeniusClass K ↥F 𝔭 = [1]`,
  whence `card_primesAbove_mul_finrank_eq`/`finrank_residue_eq_orderOf` (`Frobenius.lean`) with
  `F`-Frobenius of order `1`.
* **(B) Comparison** (`finrank_mul_unramified_le_univ`).
  `[F:K] · Σ_{unram 𝔭} N𝔭^{-s} ≤ Σ_{𝔮 of F} N𝔮^{-s}` via the prime fibration `𝔮 ↦ 𝔮 ∩ 𝓞 K`
  (a `tsum`-over-`Sigma` regrouping `Σ_{𝔮 over unram 𝔭} N𝔮^{-s} = Σ_𝔭 (#𝔮∣𝔭) · N𝔭^{-s}`).
* **(C) Limit.** Divide (B) by `log(1/(s-1))` and pass to the limit: the `K`-side ratio `→ 1`
  (`primeIdealZetaSum_unramified_div_log_tendsto_one`, replayed locally) and the `F`-side `→ 1`
  (`primeIdealZetaSum_univ_tendsto_log`, `Density.lean`), forcing `[F:K] · 1 ≤ 1`. -/
private theorem finrank_fixedField_le_one_of_forall_frobenius_mem
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (hH : ∀ 𝔭 : Ideal (𝓞 K), ∀ _ : 𝔭.IsPrime, 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 →
      ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    Module.finrank K (IntermediateField.fixedField H) ≤ 1 := by
  set F := IntermediateField.fixedField H with hF
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  haveI : NumberField F := NumberField.of_intermediateField F
  set d : ℕ := Module.finrank K ↥F with hd
  -- It suffices to show `(d : ℝ) ≤ 1`.
  rw [← Nat.cast_le (α := ℝ), Nat.cast_one]
  -- The `K`-unramified ratio and the `F`-universal ratio both tend to `1`.
  set A : ℝ → ℝ := fun s ↦
    primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} s with hA
  set B : ℝ → ℝ := fun s ↦
    primeIdealZetaSum (Set.univ : Set (Ideal (𝓞 ↥F))) s with hB
  have hAtend : Filter.Tendsto (fun s ↦ A s / Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    primeIdealZetaSum_unramified_div_log_tendsto_one K L
  have hBtend : Filter.Tendsto (fun s ↦ B s / Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    primeIdealZetaSum_univ_tendsto_log (↥F)
  -- Step (B) inequality `d · A s ≤ B s` divided by the eventually-positive `log(1/(s-1))`.
  have hLpos : ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1), 0 < Real.log (1 / (s - 1)) :=
    tendsto_log_one_div_sub_one_atTop.eventually_gt_atTop 0
  have hev : ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1),
      (d : ℝ) * (A s / Real.log (1 / (s - 1))) ≤ B s / Real.log (1 / (s - 1)) := by
    filter_upwards [hLpos, self_mem_nhdsWithin] with s hLs hs1
    simp only [Set.mem_Ioi] at hs1
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (finrank_mul_unramified_le_univ K L H hH hs1) hLs.le
  -- Pass to the limit: `d · 1 ≤ 1`.
  have hlim := le_of_tendsto_of_tendsto (hAtend.const_mul (d : ℝ)) hBtend hev
  simpa using hlim

/-- **Frobenii generate the Galois group** (CFT-free, via the zeta asymptotics; abelian case). A
subgroup of `Gal(L/K)` that contains the Frobenius representative of every nonzero prime of `K`
unramified in `L` is all of `Gal(L/K)`.

**Statement change (authorized by the orchestrator).** The hypothesis `[IsMulCommutative Gal(L/K)]`
has been added (after `[FiniteDimensional K L]`). It is genuinely needed: the hypothesis only
provides the chosen class *representative* `(frobeniusClass 𝔭).out ∈ H`, which suffices precisely
when conjugacy classes are singletons, i.e. when `Gal(L/K)` is abelian (the only case the project
consumes — `L = K(μ_m)`). For a general (non-abelian) `G` the out-only membership is too weak: a
non-normal `H` containing one Frobenius conjugate per prime need not contain the whole class, and
the split-completely transfer (hence the `[F:K]`-fold zeta multiplicity) fails. The general form
would have to quantify over the entire class, not just `.out`.

Proof: reduce `H = ⊤` to `[F:K] ≤ 1` for `F = fixedField H`
(`Subgroup.card_eq_iff_eq_top` + `finrank_fixedField_eq_card` + `card_aut_eq_finrank`), then apply
`finrank_fixedField_le_one_of_forall_frobenius_mem`. -/
theorem subgroup_eq_top_of_forall_frobenius_mem
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K))
    (hH : ∀ 𝔭 : Ideal (𝓞 K), ∀ _ : 𝔭.IsPrime, 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 →
      ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    H = ⊤ := by
  -- Reduce to `[F:K] ≤ 1` for `F = fixedField H`.
  have hfk1 := finrank_fixedField_le_one_of_forall_frobenius_mem K L H hH
  rw [← Subgroup.card_eq_iff_eq_top]
  have hpos : 1 ≤ Module.finrank K (IntermediateField.fixedField H) := Module.finrank_pos
  have hfk : Module.finrank K (IntermediateField.fixedField H) = 1 := le_antisymm hfk1 hpos
  have htower := Module.finrank_mul_finrank K (IntermediateField.fixedField H) L
  rw [hfk, one_mul] at htower
  rw [IsGalois.card_aut_eq_finrank K L, ← htower, IntermediateField.finrank_fixedField_eq_card H]

end Chebotarev
