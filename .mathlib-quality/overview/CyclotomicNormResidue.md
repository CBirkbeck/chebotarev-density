# Inventory: `CebotarevDensity/CyclotomicNormResidue.lean`

**File-level framing**: `module` with `@[expose] public section` and `noncomputable section`, all inside `namespace Chebotarev`, `open NumberField`. Imports: `CebotarevDensity.Frobenius`, `Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots`, `Mathlib.NumberTheory.NumberField.Ideal.Basic`. Total 674 lines. **No `sorry`, no `set_option`, no `axiom`, no TODO anywhere.** The file packages two arithmetic inputs to Frobenius-fibre equidistribution (the cyclotomic Frobenius-as-norm-residue dictionary, and CFT-free Frobenii-generation), positioned *below* `ZetaProduct.lean` in import order so that file can consume them without a cycle. Content is deliberately (re)stated/replicated here from `Cyclotomic.lean` and `ZetaProduct.lean`.

---

### `theorem cyclotomic_frobenius_acts_as_norm_power`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] [FiniteDimensional K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hcop : (Ideal.absNorm 𝔭).Coprime m) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭) : ... ∀ ζ : L, ζ ∈ primitiveRoots m L → arithFrobAt (𝓞 K) Gal(L/K) 𝔓 ζ = ζ ^ Ideal.absNorm 𝔭` (with a `haveI : Finite (𝓞 L ⧸ 𝔓)` in the conclusion).
- **What**: Sharifi 7.2.1(i) — the element-level cyclotomic Frobenius formula: the arithmetic Frobenius at `𝔓 | 𝔭` raises every primitive `m`-th root of unity to the `N𝔭`-th power, `φ_𝔭(ζ) = ζ^{N𝔭}`.
- **How**: Lifts `ζ` to `z = hζ.toInteger ∈ 𝓞 L` (with `z^m = 1`), shows `(m : 𝓞 L) ∉ 𝔓` (else its norm-divisibility forces `N𝔓 = 1`, contradicting coprimality), and applies the abstract Frobenius characterization `IsArithFrobAt.apply_of_pow_eq_one` with `N𝔭 = card(𝓞 K ⧸ 𝔓.under (𝓞 K))`; transports the integer-level identity back to `L` via `algebraMap` and `map_pow`.
- **Hypotheses**: cyclotomic extension `L = K(μ_m)`, `𝔭` prime unramified in `L`, `(N𝔭).Coprime m`, `𝔓 | 𝔭`.
- **Uses from project**: `UnramifiedIn` (the predicate, via `hunr`), `UnramifiedIn.ramificationIdx_eq_one`, `ne_bot_of_ramificationIdx_eq_one`, `UnramifiedIn.ne_bot`.
- **Used by**: `autToPow_frobeniusClass_out` (line 122).
- **Visibility**: public
- **Lines**: 52–90 (proof body 61–90, 30 lines)
- **Notes**: proof exactly 30 lines (the `haveI : Finite …` is restated in conclusion and reproven in body). Externally consumed by name only as documentation in `ZetaProduct.lean` (lines 558, 2144) and the blueprint `Chapters/Cyclotomic.lean` (`:::lemma "cyclotomic-frobenius-norm-power"`); the *callable* consumer is `autToPow_frobeniusClass_out` in this file.

---

### `private theorem pow_natModEq_of_pow_eq`
- **Type**: `{S : Type*} [CommRing S] [IsDomain S] {μ : S} {n : ℕ} [NeZero n] (hμ : IsPrimitiveRoot μ n) {a b : ℕ} (h : μ ^ a = μ ^ b) : a ≡ b [MOD n]`
- **What**: Easy direction of the primitive-root exponent dictionary: equal powers of a primitive `n`-th root of unity have exponents congruent mod `n`.
- **How**: One-line term proof: rewrites `n = orderOf μ` (`hμ.eq_orderOf`) and applies `IsOfFinOrder.pow_eq_pow_iff_modEq`.
- **Hypotheses**: `μ` a primitive `n`-th root in a domain, `NeZero n`.
- **Uses from project**: none (pure mathlib).
- **Used by**: `autToPow_frobeniusClass_out` (line 128).
- **Visibility**: private
- **Lines**: 94–96 (proof 1 line, term-mode)
- **Notes**: none.

---

### `theorem autToPow_frobeniusClass_out`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] [FiniteDimensional K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hcop : (Ideal.absNorm 𝔭).Coprime m) : hζ.autToPow K ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) = ZMod.unitOfCoprime (Ideal.absNorm 𝔭) hcop`
- **What**: The cyclotomic Frobenius as a norm residue in *multiplicative-dictionary* form: the cyclotomic character `IsPrimitiveRoot.autToPow : Gal(L/K) →* (ℤ/m)ˣ` sends the Frobenius class representative `(frobeniusClass K L 𝔭).out` to the unit `N𝔭 mod m`.
- **How**: Picks a prime `𝔓 | 𝔭`, sets `φ = arithFrobAt 𝔓`; shows `frobeniusClass 𝔭 = mk φ` (`frobeniusClass_eq_mk_of_isArithFrobAt`) so `(frobeniusClass 𝔭).out` is conjugate to `φ`, and a group hom respects `IsConj` (`autToPow.map_isConj` + `isConj_iff_eq`) so the two characters agree. The value is then computed from the element-level `φ(ζ) = ζ^{N𝔭}` (`cyclotomic_frobenius_acts_as_norm_power`) combined with `autToPow_spec` and `pow_natModEq_of_pow_eq` to read off `N𝔭 mod m`.
- **Hypotheses**: `L = K(μ_m)`, `ζ` primitive `m`-th root, `𝔭` prime unramified with `(N𝔭).Coprime m`.
- **Uses from project**: `frobeniusClass` (the def), `exists_prime_liesOver`, `UnramifiedIn.ne_bot`, `UnramifiedIn.ramificationIdx_eq_one`, `ne_bot_of_ramificationIdx_eq_one`, `frobeniusClass_eq_mk_of_isArithFrobAt`, `cyclotomic_frobenius_acts_as_norm_power`, `pow_natModEq_of_pow_eq`.
- **Used by**: unused in file (it is a top-level export).
- **Visibility**: public
- **Lines**: 102–128 (proof body 109–128, 20 lines)
- **Notes**: **Heavily externally consumed.** Callable uses: `Main.lean:348`, `ZetaProduct.lean:929`, `ZetaProduct.lean:1408`. Doc mentions: `ZetaProduct.lean` (815, 898, 1360, 1392), `Main.lean:337`, `ForMathlib/IdealCongruenceCount.lean` (2016, 2101). This is a key API lemma of the file.

---

### `private theorem smul_algebraMap_eq`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] (F : IntermediateField K L) [IsGalois K F] (σ : L ≃ₐ[K] L) (y : 𝓞 F) : ... σ • (algebraMap (𝓞 F) (𝓞 L) y) = algebraMap (𝓞 F) (𝓞 L) ((σ.restrictNormal F) • y)` (with `haveI : IsScalarTower K F L`).
- **What**: Action intertwining for normal restriction: the integers embedding `𝓞 F → 𝓞 L` intertwines `σ : Gal(L/K)` with its normal restriction `σ ↾ F`.
- **How**: Reduces (via `RingOfIntegers.ext_iff`) to the identity after the injective `𝓞 L ↪ L`; bridges the `𝓞`-action to the field action on both `L` and `F` (`smul_distrib_smul`), pushes everything to `L` through `IsScalarTower.algebraMap_apply`, and closes with `AlgEquiv.restrictNormal_commutes`.
- **Hypotheses**: `F` intermediate, Galois over `K`.
- **Uses from project**: none (mathlib `RingOfIntegers`/`AlgEquiv` API only).
- **Used by**: `isArithFrobAt_restrictNormal` (line 183).
- **Visibility**: private
- **Lines**: 145–166 (proof body 151–166, 16 lines)
- **Notes**: `open scoped Pointwise in` modifier on the declaration.

---

### `private theorem isArithFrobAt_restrictNormal`
- **Type**: `(K L : Type*) [...] [FiniteDimensional K L] (F : IntermediateField K L) [IsGalois K F] (σ : L ≃ₐ[K] L) (𝔓 : Ideal (𝓞 L)) (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) : ... IsArithFrobAt (𝓞 K) (σ.restrictNormal F) (𝔓.under (𝓞 F))` (with `IsScalarTower K F L`).
- **What**: Downward Frobenius restriction (mirror of `Main.lean`'s upward `arithFrobAt_restrictScalars_eq`): if `σ` is an arithmetic Frobenius at `𝔓` of `𝓞 L`, its normal restriction `σ ↾ F` is an arithmetic Frobenius at `𝔮 = 𝔓 ∩ 𝓞 F`.
- **How**: The defining congruence `σ x ≡ x^{N𝔭} (mod 𝔓)` is pulled back through `𝓞 F → 𝓞 L`: rewrites with `Ideal.under_under` (so `(𝔓∩𝓞 F)∩𝓞 K = 𝔓∩𝓞 K`), uses the intertwining `smul_algebraMap_eq` to move the restricted action across the embedding, and applies `hσ` at `algebraMap y`.
- **Hypotheses**: `F` Galois over `K`, `hσ : IsArithFrobAt (𝓞 K) σ 𝔓`.
- **Uses from project**: `smul_algebraMap_eq`.
- **Used by**: `frobeniusClass_fixedField_eq_one` (line 252).
- **Visibility**: private
- **Lines**: 173–184 (proof body 179–184, 6 lines)
- **Notes**: none.

---

### `private theorem unramifiedIn_intermediateField`
- **Type**: `(K L : Type*) [...] [FiniteDimensional K L] (F : IntermediateField K L) [IsGalois K F] (𝔭 : Ideal (𝓞 K)) (hunr : UnramifiedIn K L 𝔭) : UnramifiedIn K (↥F) 𝔭`
- **What**: A prime of `𝓞 K` unramified in `L` is unramified in every intermediate field `F` Galois over `K`.
- **How**: For a prime `𝔮` of `𝓞 F` over `𝔭`, picks `𝔓` of `𝓞 L` over `𝔮`; this `𝔓` lies over `𝔭` (via `Ideal.under_under`), unramifiedness of `𝔓/𝓞 K` is supplied by `hunr.2`, and it descends to `𝔮` via mathlib's `Algebra.IsUnramifiedAt.of_liesOver`.
- **Hypotheses**: `F` Galois over `K`, `hunr : UnramifiedIn K L 𝔭`.
- **Uses from project**: `UnramifiedIn` (predicate + `.1`, `.2` projections), `exists_prime_liesOver`. (`Ideal.ne_bot_of_liesOver_of_ne_bot` and `Algebra.IsUnramifiedAt.of_liesOver` are mathlib.)
- **Used by**: `frobeniusClass_fixedField_eq_one` (line 253), `finrank_residue_fixedField_eq_one` (line 275), `card_primesOver_fixedField_eq_finrank` (line 299).
- **Visibility**: private
- **Lines**: 189–206 (proof body 194–206, 13 lines)
- **Notes**: none.

---

### `private theorem frobeniusClass_fixedField_eq_one`
- **Type**: `(K L : Type*) [...] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K)) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hmem : ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) : ... frobeniusClass K (↥(IntermediateField.fixedField H)) 𝔭 = ConjClasses.mk 1`
- **What**: **Step (A) splitting.** For `F = fixedField H` (`H` abelian hence normal) and `𝔭` unramified with Frobenius rep in `H`, the `F`-Frobenius class of `𝔭` is trivial — `𝔭` splits completely in `F`.
- **How**: In the abelian group `Gal(L/K)`, conjugacy is trivial, so a genuine Frobenius `σ = arithFrobAt 𝔓` equals `(frobeniusClass 𝔭).out`, which lies in `H = fixingSubgroup F` (`fixingSubgroup_fixedField`); hence its normal restriction is `1` (`restrictNormalHom_ker`). By the downward restriction `isArithFrobAt_restrictNormal`, that `1` is the `F`-Frobenius at `𝔮 = 𝔓 ∩ 𝓞 F`, so the class is `mk 1`.
- **Hypotheses**: `IsMulCommutative Gal(L/K)`, `𝔭` prime unramified, Frobenius rep `∈ H`.
- **Uses from project**: `frobeniusClass` (def), `UnramifiedIn` (predicate), `UnramifiedIn.ne_bot`, `UnramifiedIn.ramificationIdx_eq_one`, `ne_bot_of_ramificationIdx_eq_one`, `exists_prime_liesOver`, `frobeniusClass_eq_mk_of_isArithFrobAt`, `isArithFrobAt_restrictNormal`, `unramifiedIn_intermediateField`. (`IsGalois.of_fixedField_normal_subgroup`, `NumberField.of_intermediateField`, `IntermediateField.restrictNormalHom_ker` are mathlib.)
- **Used by**: `finrank_residue_fixedField_eq_one` (line 277).
- **Visibility**: private
- **Lines**: 216–254 (proof body 224–254, 31 lines)
- **Notes**: proof &gt;30 lines (31).

---

### `private theorem finrank_residue_fixedField_eq_one`
- **Type**: `(K L : Type*) [...] [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K)) (𝔭 ...) (hunr ...) (hmem ...) : ... ∀ 𝔮 : Ideal (𝓞 ↥(fixedField H)), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 → Module.finrank (𝓞 K ⧸ 𝔮.under (𝓞 K)) (𝓞 ↥(fixedField H) ⧸ 𝔮) = 1`
- **What**: **Step (A), residue degree.** Under the splitting hypotheses, every prime `𝔮` of `𝓞 F` over `𝔭` has residue degree one, `[κ(𝔮):κ(𝔭)] = 1`.
- **How**: The `F`-Frobenius class of `𝔭` is trivial (`frobeniusClass_fixedField_eq_one`), so by `finrank_residue_eq_orderOf` the residue degree equals `orderOf (1 : Gal(F/K)) = 1` (`orderOf_one`).
- **Hypotheses**: same as `frobeniusClass_fixedField_eq_one`.
- **Uses from project**: `frobeniusClass`, `UnramifiedIn`, `unramifiedIn_intermediateField`, `frobeniusClass_fixedField_eq_one`, `finrank_residue_eq_orderOf`.
- **Used by**: `card_primesOver_fixedField_eq_finrank` (line 300), `absNorm_eq_of_liesOver_fixedField` (line 326).
- **Visibility**: private
- **Lines**: 261–282 (proof body 272–282, 11 lines)
- **Notes**: none.

---

### `private theorem card_primesOver_fixedField_eq_finrank`
- **Type**: `(K L : Type*) [...] [IsMulCommutative Gal(L/K)] (H ...) (𝔭 ...) (hunr ...) (hmem ...) : Nat.card {𝔮 : Ideal (𝓞 ↥(fixedField H)) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭 ∧ 𝔮 ≠ ⊥} = Module.finrank K ↥(fixedField H)`
- **What**: **Step (A), count form.** Under the splitting hypotheses, there are exactly `[F:K]` primes of `𝓞 F` above `𝔭`.
- **How**: From `card_primesAbove_mul_finrank_eq` (`Frobenius.lean`) — count × residue-degree = `card_aut` — with residue degree `1` (`finrank_residue_fixedField_eq_one`, then `mul_one`); rewrites `card_aut_eq_finrank` to get `[F:K]`.
- **Hypotheses**: same as Step (A).
- **Uses from project**: `UnramifiedIn`, `UnramifiedIn.ne_bot`, `unramifiedIn_intermediateField`, `finrank_residue_fixedField_eq_one`, `exists_prime_liesOver`, `card_primesAbove_mul_finrank_eq`.
- **Used by**: `finrank_mul_unramified_coprime_le_univ` (line 536).
- **Visibility**: private
- **Lines**: 288–306 (proof body 296–306, 11 lines)
- **Notes**: none.

---

### `private theorem absNorm_eq_of_liesOver_fixedField`
- **Type**: `(K L : Type*) [...] [IsMulCommutative Gal(L/K)] (H ...) (𝔭 ...) (hunr ...) (hmem ...) : ... ∀ 𝔮 : Ideal (𝓞 ↥(fixedField H)), 𝔮.IsPrime → 𝔮.LiesOver 𝔭 → Ideal.absNorm 𝔮 = Ideal.absNorm 𝔭`
- **What**: **Step (A), norm form.** Under the splitting hypotheses, every prime `𝔮` of `𝓞 F` over `𝔭` has equal norm `N𝔮 = N𝔭`.
- **How**: Residue/inertia degree `f(𝔮 | 𝔭) = 1` (`finrank_residue_fixedField_eq_one` via `Ideal.inertiaDeg_algebraMap`) feeds `Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver` with `pow_one`, giving `N𝔮 = N𝔭^1`.
- **Hypotheses**: same as Step (A).
- **Uses from project**: `UnramifiedIn`, `UnramifiedIn.ne_bot`, `finrank_residue_fixedField_eq_one`.
- **Used by**: `finrank_mul_unramified_coprime_le_univ` (line 538).
- **Visibility**: private
- **Lines**: 312–335 (proof body 323–335, 13 lines)
- **Notes**: none.

---

### `private theorem exists_prime_dvd_natCast_mem'`
- **Type**: `(K : Type*) [Field K] [NumberField K] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (n : ℕ) (hn1 : 1 &lt; n) (hmem : (n : 𝓞 K) ∈ 𝔭) : ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ (r : 𝓞 K) ∈ 𝔭` — note `omit [NumberField K]`.
- **What**: If the integer cast `(n : 𝓞 K)` lies in a prime `𝔭` and `1 &lt; n`, some rational prime factor `r ∣ n` already casts into `𝔭`. (Replicated from `ZetaProduct.lean`.)
- **How**: Strong induction on `n`: factor `n = r·k` (`Nat.exists_prime_and_dvd`); the prime property `𝔭.IsPrime.mem_or_mem` sends the cast into `r` (done) or into `k`; if `k = 1` the unit lies in `𝔭` (contradiction), else recurse on `k &lt; r·k`.
- **Hypotheses**: `𝔭` prime, `1 &lt; n`, `(n : 𝓞 K) ∈ 𝔭`. (`NumberField K` omitted.)
- **Uses from project**: none (mathlib `Ideal`/`Nat` API only).
- **Used by**: `exists_primeFactor_natCast_mem_of_not_coprime'` (line 383).
- **Visibility**: private
- **Lines**: 355–372 (proof body 358–372, 15 lines)
- **Notes**: inside `section CoprimeRestricted` (variables `K m`); uses `lia` (lean's `omega` alias). Replicated from `ZetaProduct.lean`.

---

### `private theorem exists_primeFactor_natCast_mem_of_not_coprime'`
- **Type**: `(K : Type*) [Field K] [NumberField K] (m : ℕ) [NeZero m] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) (hncop : ¬ (Ideal.absNorm 𝔭).Coprime m) : ∃ p ∈ m.primeFactors, (p : 𝓞 K) ∈ 𝔭`
- **What**: A nonzero prime with norm not coprime to `m` contains `(p : 𝓞 K)` for some `p ∈ m.primeFactors`. (Replicated from `ZetaProduct.lean`.)
- **How**: From `Ideal.absNorm_mem` and `exists_prime_dvd_natCast_mem'`, get a rational prime `r` with `(r:𝓞 K) ∈ 𝔭`, and `N𝔭 ∣ r^{rank}` (via `absNorm_span_singleton` + `Algebra.norm_algebraMap`). A prime `p ∣ gcd(N𝔭, m)` then divides `r^{rank}`, so `p = r` by primality, and `p ∈ m.primeFactors` with `(p:𝓞 K) ∈ 𝔭`.
- **Hypotheses**: `NeZero m`, `𝔭 ≠ ⊥` prime, `¬(N𝔭).Coprime m`.
- **Uses from project**: `exists_prime_dvd_natCast_mem'`.
- **Used by**: `finite_badPrimes'` (line 423).
- **Visibility**: private
- **Lines**: 376–393 (proof body 380–393, 14 lines)
- **Notes**: `section CoprimeRestricted`. Replicated from `ZetaProduct.lean`.

---

### `private theorem finite_primes_natCast_mem'`
- **Type**: `(K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p ≠ 0) : {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ (p : 𝓞 K) ∈ 𝔭}.Finite`
- **What**: The nonzero primes containing a fixed nonzero integer cast `(p : 𝓞 K)` form a finite set. (Replicated from `ZetaProduct.lean`.)
- **How**: Such primes divide the nonzero ideal `span {(p:𝓞 K)}`, which has finitely many prime factors (`Ideal.finite_factors`); injects the set into that finite factor set via `Ideal.dvd_iff_le` ↔ membership.
- **Hypotheses**: `p ≠ 0`.
- **Uses from project**: none (mathlib Dedekind-domain factor finiteness only).
- **Used by**: `finite_badPrimes'` (line 419).
- **Visibility**: private
- **Lines**: 397–411 (proof body 399–411, 13 lines)
- **Notes**: `classical`. `section CoprimeRestricted`. Replicated from `ZetaProduct.lean`.

---

### `private theorem finite_badPrimes'`
- **Type**: `(K : Type*) [Field K] [NumberField K] (m : ℕ) [NeZero m] : {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ (Ideal.absNorm 𝔭).Coprime m}.Finite`
- **What**: The "bad prime" set — nonzero primes whose norm is not coprime to `m` — is finite. (Replicated from `ZetaProduct.lean`.)
- **How**: Covers it by the finite union over `p ∈ m.primeFactors` of `{𝔭 : (p:𝓞 K) ∈ 𝔭}` (each finite by `finite_primes_natCast_mem'`), the cover map being `exists_primeFactor_natCast_mem_of_not_coprime'`.
- **Hypotheses**: `NeZero m`.
- **Uses from project**: `finite_primes_natCast_mem'`, `exists_primeFactor_natCast_mem_of_not_coprime'`.
- **Used by**: `primeIdealZetaSum_unramified_coprime_div_log_tendsto_one` (line 456).
- **Visibility**: private
- **Lines**: 414–424 (proof body 416–424, 9 lines)
- **Notes**: `classical`. End of `section CoprimeRestricted` (line 426). Replicated from `ZetaProduct.lean`.

---

### `private theorem primeIdealZetaSum_unramified_coprime_div_log_tendsto_one`
- **Type**: `(K L : Type*) [...] (m : ℕ) [NeZero m] : Filter.Tendsto (fun s : ℝ ↦ primeIdealZetaSum {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ (Ideal.absNorm 𝔭).Coprime m} s / Real.log (1 / (s - 1))) (nhdsWithin 1 (Set.Ioi 1)) (nhds 1)` — note `omit [FiniteDimensional K L]`.
- **What**: The coprime-norm-unramified prime sum divided by `log(1/(s-1))` tends to `1` as `s → 1⁺`; i.e. that restricted sum is asymptotic to the full universal log-pole.
- **How**: Splits the universal prime sum as disjoint `Uc ∪ D` where `D` = (ramified) ∪ (bad norm). `D` is finite (`finite_ramifiedIn` ∪ `finite_badPrimes'`), so `primeIdealZetaSum D` is bounded (`primeIdealZetaSum_le_card_of_finite`) and `(D-sum)/log → 0` (squeeze, `tendsto_log_one_div_sub_one_atTop` → ∞). Subtracting from the universal limit `1` (`primeIdealZetaSum_univ_tendsto_log`) and using `Uc + D = univ` (`primeIdealZetaSum_union_of_disjoint`, `primeIdealZetaSum_eq_univ_of_forall_prime_mem`) gives the `Uc` ratio → 1 via `Tendsto.congr'`.
- **Hypotheses**: `NeZero m`. (`FiniteDimensional K L`, `IsGalois K L` are used only through `UnramifiedIn`/finiteness, with `FiniteDimensional` omitted.)
- **Uses from project**: `primeIdealZetaSum` (def, via `primeIdealZetaSum_def`), `UnramifiedIn` (predicate), `finite_ramifiedIn`, `finite_badPrimes'`, `primeIdealZetaSum_le_card_of_finite`, `tendsto_log_one_div_sub_one_atTop`, `primeIdealZetaSum_univ_tendsto_log`, `primeIdealZetaSum_union_of_disjoint`, `primeIdealZetaSum_eq_univ_of_forall_prime_mem`.
- **Used by**: `finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime` (line 607).
- **Visibility**: private
- **Lines**: 438–487 (proof body 445–487, 43 lines)
- **Notes**: **proof &gt;30 lines (43)**. Opens `section CoprimeRestrictedComparison` (line 428, variables `K L m`).

---

### `private theorem finite_primesLiesOver_ne_bot`
- **Type**: `(K L : Type*) [...] (F : IntermediateField K L) [IsGalois K F] (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal] : ... Finite {𝔮 : Ideal (𝓞 ↥F) // 𝔮.IsPrime ∧ 𝔮.LiesOver 𝔭 ∧ 𝔮 ≠ ⊥}` — note `omit [IsGalois K L] [FiniteDimensional K L] [NeZero m]`.
- **What**: For `F` intermediate Galois over `K`, the nonzero primes of `𝓞 F` lying over a fixed maximal `𝔭` of `𝓞 K` form a finite type.
- **How**: Injects the subtype into the finite `𝔭.primesOver (𝓞 F)` (finite by `IsDedekindDomain.primesOver_finite`) via the obvious forgetful map, with injectivity from `Subtype.ext`.
- **Hypotheses**: `𝔭` maximal, `F` Galois over `K`.
- **Uses from project**: none (mathlib `primesOver_finite` only).
- **Used by**: `finrank_mul_unramified_coprime_le_univ` (line 581).
- **Visibility**: private
- **Lines**: 492–505 (proof body 496–505, 10 lines)
- **Notes**: `section CoprimeRestrictedComparison`.

---

### `private theorem finrank_mul_unramified_coprime_le_univ`
- **Type**: `(K L : Type*) [...] [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K)) (hH : ∀ 𝔭, 𝔭.IsPrime → 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 → (Ideal.absNorm 𝔭).Coprime m → ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) {s : ℝ} (hs : 1 &lt; s) : (Module.finrank K ↥(fixedField H) : ℝ) * primeIdealZetaSum {coprime-unram 𝔭} s ≤ primeIdealZetaSum (univ : Set (Ideal (𝓞 ↥(fixedField H)))) s` — note `omit [NeZero m]`.
- **What**: **Coprime-restricted fibred zeta comparison.** With the Frobenius-membership hypothesis required only on coprime-norm unramified primes, `[F:K] · Σ_{coprime unram 𝔭} N𝔭^{-s} ≤ Σ_{𝔮 of F} N𝔮^{-s}`.
- **How**: Regroups the `F`-prime sum `V` (restricted to primes over a coprime-norm-unramified base) along the fibration `φ : 𝔮 ↦ 𝔮 ∩ 𝓞 K`, using `Equiv.sigmaFiberEquiv` and `tsum_sigma`. Each fibre over `𝔭` has exactly `[F:K]` primes (`card_primesOver_fixedField_eq_finrank`) all of equal norm `N𝔭` (`absNorm_eq_of_liesOver_fixedField`), so the fibre sum is `[F:K]·N𝔭^{-s}` (`tsum_const`, `Nat.card_congr` over a hand-built fibre equivalence `hfibeq`); fibre finiteness comes from `finite_primesLiesOver_ne_bot`. Summability is `summable_prime_absNorm_rpow`; the `V`-sum is `≤` the full `F`-sum by `primeIdealZetaSum_le_of_subset`.
- **Hypotheses**: `IsMulCommutative Gal(L/K)`, `hH` on coprime-norm unramified primes, `1 &lt; s`.
- **Uses from project**: `frobeniusClass` (def), `UnramifiedIn` (predicate), `UnramifiedIn.ne_bot`, `primeIdealZetaSum` (def, via `primeIdealZetaSum_def`), `card_primesOver_fixedField_eq_finrank`, `absNorm_eq_of_liesOver_fixedField`, `primeIdealZetaSum_le_of_subset`, `summable_prime_absNorm_rpow`, `finite_primesLiesOver_ne_bot`. (`IsGalois.of_fixedField_normal_subgroup`, `NumberField.of_intermediateField`, `Ideal.IsIntegral.comap_ne_bot` are mathlib.)
- **Used by**: `finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime` (line 618).
- **Visibility**: private
- **Lines**: 515–584 (proof body 524–584, **61 lines**)
- **Notes**: **longest proof in file (61 lines)**. Builds an explicit fibre `Equiv` (`hfibeq`, lines 564–574) inline. `section CoprimeRestrictedComparison`.

---

### `private theorem finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime`
- **Type**: `(K L : Type*) [...] [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K)) (hH : ∀ 𝔭, 𝔭.IsPrime → 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 → (Ideal.absNorm 𝔭).Coprime m → (frobeniusClass K L 𝔭).out ∈ H) : Module.finrank K (IntermediateField.fixedField H) ≤ 1`
- **What**: **Coprime-restricted bound on the fixed-field degree.** Under the coprime-norm Frobenius hypothesis, `[fixedField H : K] ≤ 1`.
- **How**: Compares `A s = Σ_{coprime unram} N𝔭^{-s}` (ratio → 1 by `primeIdealZetaSum_unramified_coprime_div_log_tendsto_one`) against `B s = Σ_{𝔮 of F} N𝔮^{-s}` (ratio → 1 by `primeIdealZetaSum_univ_tendsto_log`): the comparison `[F:K]·A ≤ B` (`finrank_mul_unramified_coprime_le_univ`), divided by the positive `log(1/(s-1))` and passed to the limit (`le_of_tendsto_of_tendsto`), forces `[F:K]·1 ≤ 1`.
- **Hypotheses**: `IsMulCommutative Gal(L/K)`, `hH` on coprime-norm unramified primes.
- **Uses from project**: `frobeniusClass` (def), `UnramifiedIn` (predicate), `primeIdealZetaSum` (def), `primeIdealZetaSum_unramified_coprime_div_log_tendsto_one`, `primeIdealZetaSum_univ_tendsto_log`, `tendsto_log_one_div_sub_one_atTop`, `finrank_mul_unramified_coprime_le_univ`. (`NumberField.of_intermediateField`, `IsGalois.of_fixedField_normal_subgroup` mathlib.)
- **Used by**: `subgroup_eq_top_of_forall_frobenius_mem_of_coprime` (line 639).
- **Visibility**: private
- **Lines**: 591–620 (proof body 596–620, 25 lines)
- **Notes**: this is the parent declaration whose sub-lemmas occupy lines 130–584 (its `### Sub-lemmas for …` block is at line 130).

---

### `theorem subgroup_eq_top_of_forall_frobenius_mem_of_coprime`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m] (H : Subgroup Gal(L/K)) (hH : ∀ 𝔭, 𝔭.IsPrime → 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 → (Ideal.absNorm 𝔭).Coprime m → (frobeniusClass K L 𝔭).out ∈ H) : H = ⊤`
- **What**: **Frobenii of coprime-norm primes generate the Galois group** (abelian case): a subgroup containing the Frobenius rep of every nonzero unramified prime *of coprime norm* is all of `Gal(L/K)`.
- **How**: Reduces `H = ⊤` to `[fixedField H : K] = 1` (`Subgroup.card_eq_iff_eq_top`, `IntermediateField.finrank_fixedField_eq_card`, `card_aut_eq_finrank`, the tower law `Module.finrank_mul_finrank`), and gets `[F:K] ≤ 1` (hence `= 1` with `finrank_pos`) from `finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime`.
- **Hypotheses**: `IsMulCommutative Gal(L/K)`, `NeZero m`, `hH` on coprime-norm unramified primes.
- **Uses from project**: `frobeniusClass` (def), `UnramifiedIn` (predicate), `finrank_fixedField_le_one_of_forall_frobenius_mem_of_coprime`. (`IntermediateField.finrank_fixedField_eq_card`, `IsGalois.card_aut_eq_finrank` mathlib.)
- **Used by**: `subgroup_eq_top_of_forall_frobenius_mem` (line 671).
- **Visibility**: public
- **Lines**: 633–645 (proof body 638–645, 8 lines). End of `section CoprimeRestrictedComparison` at line 647.
- **Notes**: **Externally consumed.** Callable use: `ZetaProduct.lean:1403` (`refine subgroup_eq_top_of_forall_frobenius_mem_of_coprime K L m H …`). Doc mentions: `ZetaProduct.lean` (1358, 1390, 2154). This is the file's other key export.

---

### `theorem subgroup_eq_top_of_forall_frobenius_mem`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (H : Subgroup Gal(L/K)) (hH : ∀ 𝔭, 𝔭.IsPrime → 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 → (frobeniusClass K L 𝔭).out ∈ H) : H = ⊤`
- **What**: **Frobenii generate the Galois group** (CFT-free, abelian case): a subgroup containing the Frobenius rep of every nonzero unramified prime (no coprimality restriction) is all of `Gal(L/K)`.
- **How**: One-line specialization of `subgroup_eq_top_of_forall_frobenius_mem_of_coprime` at `m = 1` (where `(N𝔭).Coprime 1` is automatic), discharging the extra coprimality argument trivially.
- **Hypotheses**: `IsMulCommutative Gal(L/K)` (documented as a *deliberate added hypothesis*, authorized by the orchestrator — the `.out`-only membership is only strong enough in the abelian case; for non-abelian `G` one would need to quantify over the whole conjugacy class), `hH` on all unramified primes.
- **Uses from project**: `frobeniusClass` (def), `UnramifiedIn` (predicate), `subgroup_eq_top_of_forall_frobenius_mem_of_coprime`.
- **Used by**: unused in file (top-level export).
- **Visibility**: public
- **Lines**: 665–672 (proof body 671–672, 2 lines, term-mode)
- **Notes**: **No callable external consumer found** — referenced only in prose/docstrings in `ZetaProduct.lean` (1358, 1390, 2154); the actually-called generation lemma is the `_of_coprime` variant. Long docstring (649–664) documents the `[IsMulCommutative]` statement change rationale.

---

## File Summary
- **Total declarations: 20** (0 defs, 20 lemmas/theorems, 0 instances/structures/classes). Of these: **4 public** theorems (`cyclotomic_frobenius_acts_as_norm_power`, `autToPow_frobeniusClass_out`, `subgroup_eq_top_of_forall_frobenius_mem_of_coprime`, `subgroup_eq_top_of_forall_frobenius_mem`) and **16 private** helper theorems.
- **Key API (used by 3+ others)**:
  - `unramifiedIn_intermediateField` — used by 3 in-file lemmas (`frobeniusClass_fixedField_eq_one`, `finrank_residue_fixedField_eq_one`, `card_primesOver_fixedField_eq_finrank`).
  - `autToPow_frobeniusClass_out` — the file's flagship export: 3 callable external consumers (`Main.lean:348`, `ZetaProduct.lean:929`, `ZetaProduct.lean:1408`) plus many doc references.
  - (Borderline) `finrank_residue_fixedField_eq_one` — used by 2 in-file lemmas.
- **Unused declarations (not used by anything in this file)**:
  - `autToPow_frobeniusClass_out` — top-level export; **externally consumed** (callable: `Main.lean`, `ZetaProduct.lean` ×2).
  - `subgroup_eq_top_of_forall_frobenius_mem` — top-level export; **only consumed in prose/docstrings externally** (no callable consumer found; its `_of_coprime` sibling is the one actually called by `ZetaProduct.lean:1403`). Worth flagging in consolidation: this convenience wrapper currently has no live call site.
  - (`subgroup_eq_top_of_forall_frobenius_mem_of_coprime` and `cyclotomic_frobenius_acts_as_norm_power` are unused *in-file* but each has a live in-file caller? — `cyclotomic_frobenius_acts_as_norm_power` is called by `autToPow_frobeniusClass_out`; `subgroup_eq_top_of_forall_frobenius_mem_of_coprime` is called by `subgroup_eq_top_of_forall_frobenius_mem` in-file AND externally by `ZetaProduct.lean:1403`.)
- **Declarations with sorry**: none.
- **Declarations with set_option**: none. (`smul_algebraMap_eq` carries an `open scoped Pointwise in` modifier; several decls carry `omit […] in` modifiers — `exists_prime_dvd_natCast_mem'`, `primeIdealZetaSum_unramified_coprime_div_log_tendsto_one`, `finite_primesLiesOver_ne_bot`, `finrank_mul_unramified_coprime_le_univ` — but no `set_option`.)
- **Proofs &gt;30 lines**:
  - `finrank_mul_unramified_coprime_le_univ` — 61 lines (515–584).
  - `primeIdealZetaSum_unramified_coprime_div_log_tendsto_one` — 43 lines (438–487).
  - `frobeniusClass_fixedField_eq_one` — 31 lines (216–254).
  - `cyclotomic_frobenius_acts_as_norm_power` — exactly 30 lines body (52–90); borderline.

**Cross-file note**: Lines 337–425 of this file deliberately **replicate** four finiteness helpers (`exists_prime_dvd_natCast_mem'`, `exists_primeFactor_natCast_mem_of_not_coprime'`, `finite_primes_natCast_mem'`, `finite_badPrimes'`) from `ZetaProduct.lean` (the `'`-suffixed copies), and `isArithFrobAt_restrictNormal` mirrors `Main.lean`'s `arithFrobAt_restrictScalars_eq` — all because this file sits *below* both `ZetaProduct.lean` and `Main.lean` in the import order. These are prime candidates for de-duplication if the import DAG is ever reorganized (e.g. by hoisting the shared finiteness lemmas into `Frobenius.lean` or a new low-level utility module).