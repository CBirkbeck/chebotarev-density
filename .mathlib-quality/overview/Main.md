# Inventory: `CebotarevDensity/Main.lean`

File path: `/Users/mcu22seu/Documents/GitHub/chebotarev-density/CebotarevDensity/Main.lean` (532 lines)

Module-level setup (lines 1–64): `module`; six `public import`s from Mathlib (`FieldTheory.Finite.Basic`, `RingTheory.Ideal.Over`, `RingTheory.Ideal.NatInt`, `NumberTheory.Cyclotomic.Basic`, `NumberTheory.Cyclotomic.Gal`, `NumberTheory.Cyclotomic.CyclotomicCharacter`) and two from the project (`CebotarevDensity.Abelian`, `CebotarevDensity.FixedFieldDensity`). `@[expose] public section`, `noncomputable section`. Opens `Filter NumberField Topology Set` and `scoped ENNReal`. `namespace Chebotarev`. Top-level `variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]` (lines 63–64).

---

### `theorem chebotarev_density`
- **Type** · `[FiniteDimensional K L] (C : ConjClasses Gal(L/K)) → HasDirichletDensity {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = C} ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K))`
- **What** · The headline theorem: for finite Galois `L/K` of number fields and a conjugacy class `C` of `G = Gal(L/K)`, the set of primes `𝔭` of `𝓞 K` unramified in `L` with Frobenius class `C` has Dirichlet density `|C|/|G|`.
- **How** · Reduces the conjugacy-class statement to the abelian case via the fixed-field subextension. Pick a representative `σ` with `C = ConjClasses.mk σ` (`ConjClasses.mk_surjective`). Set `e := IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)`, the iso `⟨σ⟩ ≃ Gal(L / L^⟨σ⟩)`. Establish `IsMulCommutative Gal(L / fixedField ⟨σ⟩)` via `.of_comm`: transport two Galois elements back through `e.surjective` and use `mul_comm'` in the cyclic group `⟨σ⟩` (a `zpowers` subgroup is commutative). Then invoke `density_lift_through_fixedField σ (fixedField (Subgroup.zpowers σ)) (e ⟨σ, …⟩) … (chebotarev_abelian _ L (e ⟨σ, …⟩))` — i.e. the fixed-field density-lifting lemma fed the abelian-case density `1/f` for `L / L^⟨σ⟩`.
- **Hypotheses** · `L/K` finite-dimensional Galois extension of number fields; `C` a conjugacy class of `Gal(L/K)`.
- **Uses from project** · `HasDirichletDensity`, `UnramifiedIn`, `frobeniusClass`, `density_lift_through_fixedField`, `chebotarev_abelian`
- **Used by** · `chebotarev_density_of_comm` (in docstring/concept only — actually `chebotarev_density` is used by `infinite_setOf_frobenius_class`, `density_split_completely`)
- **Visibility** · public (theorem, exposed)
- **Lines** · 99–115
- **Notes** · —

---

### `theorem ConjClasses_carrier_card_eq_one_of_comm`
- **Type** · `{G : Type*} [Group G] [IsMulCommutative G] [Finite G] (g : G) → Nat.card (ConjClasses.mk g).carrier = 1`
- **What** · In a commutative finite group, every conjugacy class is a singleton, so its carrier has cardinality `1`.
- **How** · Install the `CommMonoid G` instance (`IsMulCommutative.instCommMonoid`). Show `(ConjClasses.mk g).carrier = {g}` by `ext`/`simp` with `ConjClasses.mem_carrier_iff_mk_eq`, `ConjClasses.mk_eq_mk_iff_isConj`, `isConj_iff_eq` (conjugacy collapses to equality in a commutative group). Then `Nat.card_coe_set_eq` + `Set.ncard_singleton` give cardinality `1`.
- **Hypotheses** · `G` a finite commutative group; `g : G`.
- **Uses from project** · [] (only Mathlib lemmas)
- **Used by** · `chebotarev_density_of_comm`
- **Visibility** · public (theorem)
- **Lines** · 119–126
- **Notes** · —

---

### `theorem chebotarev_density_of_comm`
- **Type** · `[FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (C : ConjClasses Gal(L/K)) → HasDirichletDensity {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = C} ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K))`
- **What** · The abelian-case specialisation of Chebotarev: for abelian `Gal(L/K)`, the density of unramified primes with Frobenius class `C` is `|C|/|G|` (and since `|C| = 1`, effectively `1/|G|`).
- **How** · Pick representative `σ` (`ConjClasses.mk_surjective`). Rewrite `|C| = 1` using `ConjClasses_carrier_card_eq_one_of_comm σ`, then `simpa … using chebotarev_abelian K L σ` — the abelian case directly gives density `1/|G|` for the Frobenius fibre of `σ`.
- **Hypotheses** · `L/K` finite-dimensional with abelian Galois group; `C` a conjugacy class.
- **Uses from project** · `HasDirichletDensity`, `UnramifiedIn`, `frobeniusClass`, `ConjClasses_carrier_card_eq_one_of_comm`, `chebotarev_abelian`
- **Used by** · unused in file
- **Visibility** · public (theorem)
- **Lines** · 131–138
- **Notes** · —

---

### `theorem infinite_of_hasDirichletDensity_pos`
- **Type** · `{S : Set (Ideal (𝓞 K))} {δ : ℝ} (h : HasDirichletDensity S δ) (hδ : 0 &lt; δ) → S.Infinite`
- **What** · A set of prime ideals with strictly positive Dirichlet density is infinite (contrapositive of: a finite set has density `0`).
- **How** · Term-mode. Assume `S` finite (`hfin`); then `hδ.ne'` contradicts the density value: by `tendsto_nhds_unique`, the density `δ` from `h` must equal the density `0` produced by `hasDirichletDensity_of_finite K hfin` — but `δ ≠ 0` since `0 &lt; δ`.
- **Hypotheses** · `S` a set of ideals of `𝓞 K` with Dirichlet density `δ`; `0 &lt; δ`.
- **Uses from project** · `HasDirichletDensity`, `hasDirichletDensity_of_finite`
- **Used by** · `infinite_setOf_frobenius_class`
- **Visibility** · public (theorem)
- **Lines** · 143–146
- **Notes** · —

---

### `theorem ConjClasses_carrier_card_pos`
- **Type** · `{G : Type*} [Group G] [Finite G] (C : ConjClasses G) → 0 &lt; Nat.card C.carrier`
- **What** · The carrier of a conjugacy class in a finite group is nonempty (cardinality `&gt; 0`).
- **How** · Pick representative `a` (`ConjClasses.mk_surjective`). The carrier is nonempty because `a` itself lies in it (`ConjClasses.mem_carrier_mk`), giving `Nonempty (ConjClasses.mk a).carrier`; conclude with `Nat.card_pos`.
- **Hypotheses** · `G` a finite group; `C` a conjugacy class of `G`.
- **Uses from project** · [] (only Mathlib lemmas)
- **Used by** · `infinite_setOf_frobenius_class`
- **Visibility** · public (theorem)
- **Lines** · 149–154
- **Notes** · —

---

### `theorem infinite_setOf_frobenius_class`
- **Type** · `[FiniteDimensional K L] (C : ConjClasses Gal(L/K)) → Set.Infinite {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = C}`
- **What** · Qualitative corollary: there are infinitely many primes of `𝓞 K` (unramified in `L`) with any prescribed Frobenius conjugacy class `C`.
- **How** · Apply `infinite_of_hasDirichletDensity_pos` to `chebotarev_density C`, reducing to positivity of `|C|/|G|`. Then `div_pos` splits into: numerator `0 &lt; Nat.card C.carrier` (cast of `ConjClasses_carrier_card_pos C`) and denominator `0 &lt; Nat.card Gal(L/K)` (cast of `Nat.card_pos`).
- **Hypotheses** · `L/K` finite-dimensional Galois extension of number fields; `C` a conjugacy class.
- **Uses from project** · `UnramifiedIn`, `frobeniusClass`, `infinite_of_hasDirichletDensity_pos`, `chebotarev_density`, `ConjClasses_carrier_card_pos`
- **Used by** · unused in file
- **Visibility** · public (theorem)
- **Lines** · 158–166
- **Notes** · —

---

### `theorem ConjClasses_mk_one_carrier_card_eq_one`
- **Type** · `(G : Type*) [Group G] [Finite G] → Nat.card (ConjClasses.mk (1 : G)).carrier = 1`
- **What** · The identity conjugacy class `{1}` in a finite group has carrier of cardinality `1`.
- **How** · Show `(ConjClasses.mk 1).carrier = {1}` by `simp` with `Set.ext_iff`, `ConjClasses.mem_carrier_iff_mk_eq`, `ConjClasses.mk_eq_mk_iff_isConj` (anything conjugate to `1` equals `1`). Then `Nat.card_coe_set_eq` + `Set.ncard_singleton`.
- **Hypotheses** · `G` a finite group.
- **Uses from project** · [] (only Mathlib lemmas)
- **Used by** · `density_split_completely`
- **Visibility** · public (theorem)
- **Lines** · 169–174
- **Notes** · —

---

### `theorem density_split_completely`
- **Type** · `HasDirichletDensity {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = ConjClasses.mk 1} ((Module.finrank K L : ℝ)⁻¹)`
- **What** · The Dirichlet density of primes of `𝓞 K` that split completely in `L` (Frobenius class = identity) equals `1/[L:K]`.
- **How** · Instantiate `chebotarev_density` at `C = ConjClasses.mk 1`. Rewrite the numerator `|C| = 1` via `ConjClasses_mk_one_carrier_card_eq_one`, and `|Gal(L/K)| = [L:K]` via `IsGalois.card_aut_eq_finrank K L`; then `simpa` turns `1/[L:K]` into `([L:K])⁻¹`.
- **Hypotheses** · (from the top-level `variable` line) `L/K` Galois extension of number fields. Note: relies on `chebotarev_density` whose `FiniteDimensional K L` is supplied — here it is available via the ambient instances.
- **Uses from project** · `HasDirichletDensity`, `UnramifiedIn`, `frobeniusClass`, `chebotarev_density`, `ConjClasses_mk_one_carrier_card_eq_one`
- **Used by** · unused in file
- **Visibility** · public (theorem)
- **Lines** · 181–188
- **Notes** · "split completely" identified with identity-Frobenius via the set definition; no explicit splitting predicate.

---

`section DirichletAP` opens at line 203 with a local `variable {K : Type*} [Field K] [NumberField K]` (line 205), shadowing the file-level `K L`. Closes at line 258.

---

### `private theorem primeIdealZetaSum_eq_add_sub_sdiff`
- **Type** · `{S T : Set (Ideal (𝓞 K))} {s : ℝ} (hs : 1 &lt; s) → primeIdealZetaSum T s = primeIdealZetaSum S s + primeIdealZetaSum (T \ S) s - primeIdealZetaSum (S \ T) s`
- **What** · Inclusion–exclusion for the partial Dirichlet series at `s &gt; 1`: `Σ_T = Σ_S + Σ_{T∖S} − Σ_{S∖T}`.
- **How** · Two disjoint-union decompositions. `hdisj`: `(A∩B)` and `(A∖B)` are disjoint (`disjoint_of_subset_left inter_subset_right disjoint_sdiff_right`). `hT`: rewrite `T = (T∩S) ∪ (T∖S)` (`inter_union_diff`) and split the sum via `primeIdealZetaSum_union_of_disjoint`. `hS`: same for `S = (T∩S) ∪ (S∖T)` (using `inter_comm`). Substitute both and close with `ring`.
- **Hypotheses** · `S, T` sets of ideals of `𝓞 K`; `1 &lt; s`.
- **Uses from project** · `primeIdealZetaSum`, `primeIdealZetaSum_union_of_disjoint`
- **Used by** · `hasDirichletDensity_of_finite_symmDiff`
- **Visibility** · private (theorem)
- **Lines** · 209–223
- **Notes** · —

---

### `private theorem hasDirichletDensity_of_finite_symmDiff`
- **Type** · `{S T : Set (Ideal (𝓞 K))} {δ : ℝ} (hST : (S \ T).Finite) (hTS : (T \ S).Finite) (hS : HasDirichletDensity S δ) → HasDirichletDensity T δ`
- **What** · Dirichlet density is insensitive to finite symmetric differences: if `S∖T` and `T∖S` are finite and `S` has density `δ`, then `T` also has density `δ`.
- **How** · The finite diffs `T∖S` and `S∖T` have density `0` (`hasDirichletDensity_of_finite`). Unfold `HasDirichletDensity` (a tendsto statement). Form `h := (hS.add hTSden).sub hSTden` (density `δ + 0 − 0`); rewrite that scalar to `δ` and transfer the limit along `h.congr'`. The eventual-equality of the ratio functions is proved with `filter_upwards [self_mem_nhdsWithin]`, reducing (for `s ∈ Ioi 1`, i.e. `1 &lt; s`) to the algebraic identity `primeIdealZetaSum_eq_add_sub_sdiff` followed by `ring`.
- **Hypotheses** · `S∖T`, `T∖S` finite; `S` has Dirichlet density `δ`.
- **Uses from project** · `HasDirichletDensity`, `hasDirichletDensity_of_finite`, `primeIdealZetaSum_eq_add_sub_sdiff`
- **Used by** · `dirichlet_AP_main`, `dirichlet_primes_in_AP`
- **Visibility** · private (theorem)
- **Lines** · 228–238
- **Notes** · —

---

### `private theorem zmod_eq_of_castHom_eq`
- **Type** · `{m k : ℕ} (hcop : Nat.Coprime m k) (x y : ZMod (m * k)) (h1 : castHom_m x = castHom_m y) (h2 : castHom_k x = castHom_k y) → x = y`  (where `castHom_m = ZMod.castHom (dvd_mul_right m k) (ZMod m)`, `castHom_k = ZMod.castHom (dvd_mul_left k m) (ZMod k)`)
- **What** · Chinese-remainder injectivity: two elements of `ZMod (m·k)` (with `m, k` coprime) that agree under both coordinate reduction maps are equal.
- **How** · Apply injectivity of `ZMod.chineseRemainder hcop`. Two helper identities `e1`, `e2` express the two components of `chineseRemainder z` as the two `castHom` reductions (`simp` unfolding `ZMod.chineseRemainder`, `Prod.fst_zmod_cast`/`Prod.snd_zmod_cast`). Conclude `chineseRemainder x = chineseRemainder y` by `Prod.ext`, rewriting each component with `e1`/`e2` and the hypotheses `h1`/`h2`.
- **Hypotheses** · `m, k` coprime; `x, y ∈ ZMod (m·k)` agreeing mod `m` and mod `k`.
- **Uses from project** · [] (only Mathlib `ZMod` API)
- **Used by** · `residue_iff_half`
- **Visibility** · private (theorem)
- **Lines** · 242–256
- **Notes** · —

---

### `private theorem absNorm_span_nat`
- **Type** · `(p : ℕ) → Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) = p`
- **What** · The absolute norm of the principal ideal `(p)` in `𝓞 ℚ` equals `p`.
- **How** · `Ideal.absNorm_span_singleton` reduces to the algebra norm of `(p : 𝓞 ℚ)`. Compute `Algebra.norm ℤ ((p:ℕ) : 𝓞 ℚ) = (p : ℤ)`: write `(p : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (p : ℤ)` and apply `Algebra.norm_algebraMap`, using `NumberField.RingOfIntegers.rank` ( `= 1` for `ℚ`). Final `simp` takes `Int.natAbs (p:ℤ) = p`.
- **Hypotheses** · `p : ℕ`.
- **Uses from project** · [] (only Mathlib; `NumberField.RingOfIntegers.rank` is Mathlib)
- **Used by** · `dirichlet_AP_main` (via `hnorm`), `dirichlet_AP_main`'s `hIF` branch
- **Visibility** · private (theorem)
- **Lines** · 262–268
- **Notes** · Note: this sits OUTSIDE `section DirichletAP` (after line 258), so `K` here is concrete `ℚ`, not the section variable.

---

### `private theorem ratPrime_eq_span`
- **Type** · `(𝔭 : Ideal (𝓞 ℚ)) (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) → ∃ p : ℕ, p.Prime ∧ 𝔭 = Ideal.span {(p : 𝓞 ℚ)}`
- **What** · Every nonzero prime ideal of `𝓞 ℚ` is `(p)` for a rational prime `p`.
- **How** · Transport `𝔭` through `e := Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ`. `Ideal.map e 𝔭` is prime (`Ideal.map_isPrime_of_equiv`) and nonzero (using `Ideal.comap_map_of_bijective` to recover `𝔭`, plus `Ideal.comap_bot_of_injective`). By `Ideal.isPrime_int_iff`, the image is either `⊥` (ruled out) or `span {(p:ℤ)}` for a prime `p`. Pull back: rewrite via `Ideal.map_symm`, `Ideal.map_span`, `Set.image_singleton`, and `map_natCast` to identify the preimage as `span {(p : 𝓞 ℚ)}`.
- **Hypotheses** · `𝔭` a nonzero prime ideal of `𝓞 ℚ`.
- **Uses from project** · [] (only Mathlib; `Rat.ringOfIntegersEquiv` is Mathlib)
- **Used by** · `dirichlet_AP_main` (the `hFI` branch)
- **Visibility** · private (theorem)
- **Lines** · 273–285
- **Notes** · —

---

### `private theorem span_nat_isPrime`
- **Type** · `{p : ℕ} (hpp : p.Prime) → (Ideal.span {(p : 𝓞 ℚ)}).IsPrime`
- **What** · Converse classification ingredient: for a rational prime `p`, the ideal `(p)` of `𝓞 ℚ` is prime.
- **How** · `(p:ℤ)` is prime (`Nat.prime_iff_prime_int`), so `span {(p:ℤ)}` is prime (`Ideal.span_singleton_prime`). Show `span {(p:𝓞 ℚ)} = comap Rat.ringOfIntegersEquiv (span {(p:ℤ)})` (`Ideal.map_symm`, `Ideal.map_span`, `Set.image_singleton`, `map_natCast`). Conclude with `Ideal.comap_isPrime`.
- **Hypotheses** · `p` a (natural) prime.
- **Uses from project** · [] (only Mathlib)
- **Used by** · `dirichlet_AP_main` (the `hIF` branch)
- **Visibility** · private (theorem)
- **Lines** · 289–298
- **Notes** · —

---

### `private theorem unramifiedIn_cyclotomic_of_coprime`
- **Type** · `{K} [Field K] [NumberField K] (L) [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) (hcop : (Ideal.absNorm 𝔭).Coprime m) → UnramifiedIn K L 𝔭`
- **What** · A prime `𝔭` of `𝓞 K` whose norm is coprime to `m` is unramified in the cyclotomic extension `L = K(μ_m)`.
- **How** · (&gt;30 lines.) Suppose `𝔓 ∣ 𝔭` ramifies. Reduce to "`𝔓` divides the different ideal" via `not_dvd_differentIdeal_iff` and derive a contradiction. Take a primitive `m`-th root `ζ` (`IsCyclotomicExtension.exists_isPrimitiveRoot`) with integer model `ζ𝓞`, `ζ𝓞^m = 1`. Since `minpoly (𝓞 K) ζ𝓞 ∣ X^m − 1` (`minpoly.isIntegrallyClosed_dvd`), write `X^m−1 = minpoly · g`; differentiating (`congrArg (aeval ζ𝓞 ∘ derivative)`, `Polynomial.derivative_X_pow`, `derivative_mul`, `minpoly.aeval`) yields `m·ζ𝓞^{m−1} = aeval ζ𝓞 (derivative (minpoly)) · aeval ζ𝓞 g` (`hkey`). The conductor–different identity (`conductor_mul_differentIdeal`, with `adjoin_primitive_root_eq_top` giving `hadj`) shows the different divides `span {aeval ζ𝓞 (derivative minpoly)}`, so `m·ζ𝓞^{m−1} ∈ 𝔓`, hence `(m : 𝓞 L) ∈ 𝔓` (the root factor is a unit, `IsUnit.of_pow_eq_one`). Pushing down (`h𝔓lo.over`, `Ideal.mem_comap`) gives `(m : 𝓞 K) ∈ 𝔭`, so `N𝔭 ∣ m^{finrank ℤ (𝓞 K)}` (`Ideal.absNorm_dvd_absNorm_of_le`, `Algebra.norm_algebraMap`). Coprimality forces `N𝔭 = 1` (`Nat.eq_one_of_dvd_coprimes`), contradicting `𝔭` prime (`Ideal.absNorm_eq_one_iff` vs `ne_top`).
- **Hypotheses** · `L = K(μ_m)` cyclotomic Galois over `K`; `𝔭` a nonzero prime of `𝓞 K` with `gcd(N𝔭, m) = 1`.
- **Uses from project** · `UnramifiedIn`
- **Used by** · `dirichlet_AP_main` (the `hIF` branch)
- **Visibility** · private (theorem)
- **Lines** · 305–361
- **Notes** · &gt;30 lines; `classical`. Docstring flags it as a replica of the private `unramifiedIn_of_coprime_absNorm` in `ZetaProduct.lean` (not importable).

---

### `private theorem frobeniusClass_eq_iff_residue`
- **Type** · `(n : ℕ) [NeZero n] (L) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L] [IsCyclotomicExtension {n} ℚ L] [FiniteDimensional ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)] {ζ : L} (hζ : IsPrimitiveRoot ζ n) (a : ZMod n) (ha : IsUnit a) (σ : L ≃ₐ[ℚ] L) (hσ : hζ.autToPow ℚ σ = ha.unit) (𝔭 : Ideal (𝓞 ℚ)) [𝔭.IsPrime] (hunr : UnramifiedIn ℚ L 𝔭) (hcop : (Ideal.absNorm 𝔭).Coprime n) → frobeniusClass ℚ L 𝔭 = ConjClasses.mk σ ↔ (Ideal.absNorm 𝔭 : ZMod n) = a`
- **What** · Frobenius ↔ residue dictionary for `L = ℚ(μ_n)`: with `σ` chosen so the cyclotomic character `autToPow` sends `σ` to the unit `a`, a coprime-norm unramified prime `𝔭` has Frobenius class `mk σ` iff `N𝔭 ≡ a [n]`.
- **How** · Install `CommMonoid (L ≃ₐ[ℚ] L)`. Get `hdict := autToPow_frobeniusClass_out ℚ L n hζ 𝔭 hunr hcop` realising the Frobenius representative's image under `autToPow` as `N𝔭 mod n`. Rewrite the class equality `mk(out) = mk σ` to `out = σ` (`Quotient.out_eq`, `ConjClasses.mk_eq_mk_iff_isConj`, `isConj_iff_eq`). Forward: from `out = σ` apply `autToPow`, rewrite by `hdict`,`hσ`, take `Units.val` (`ZMod.coe_unitOfCoprime`, `IsUnit.unit_spec`) to get `(N𝔭 : ZMod n) = a`. Backward: apply `autToPow_injective`; rewrite by `hdict`,`hσ`, `Units.ext`, finishing with the residue hypothesis.
- **Hypotheses** · `L = ℚ(μ_n)` cyclotomic abelian over `ℚ`; primitive root `ζ`; unit `a`; `σ` with `autToPow σ = a`; `𝔭` an unramified prime with `gcd(N𝔭, n) = 1`.
- **Uses from project** · `frobeniusClass`, `UnramifiedIn`, `autToPow_frobeniusClass_out`
- **Used by** · `dirichlet_AP_main` (both `hFI` and `hIF` branches)
- **Visibility** · private (theorem)
- **Lines** · 367–389
- **Notes** · —

---

### `private theorem residue_iff_half`
- **Type** · `(n' : ℕ) (hcop : Nat.Coprime 2 n') (a : ZMod (2 * n')) (ha : IsUnit a) (p : ℕ) (hpp : p.Prime) (hodd : p ≠ 2) → ((p : ZMod (2 * n')) = a ↔ (p : ZMod n') = (ZMod.castHom (dvd_mul_left n' 2) (ZMod n')) a)`
- **What** · For `n = 2·n'` with `n'` odd and `p` an odd prime, the residue condition `p ≡ a [2n']` is equivalent to its reduction `p ≡ a [n']`.
- **How** · Forward: reduce `h` along `ZMod.castHom … (ZMod n')` (`map_natCast`). Backward: apply `zmod_eq_of_castHom_eq hcop` to compare mod `2` and mod `n'`. The mod-`n'` coordinate is the hypothesis (`map_natCast`); the mod-`2` coordinate uses `(p : ZMod 2) = 1` (since odd `p`, via `Nat.Prime.eq_two_or_odd` and `ZMod.natCast_mod`) and that a unit of `ZMod 2` is `1` (proved by reverting to `z` and `decide`).
- **Hypotheses** · `n'` coprime to `2`; unit `a ∈ ZMod (2n')`; `p` an odd prime.
- **Uses from project** · `zmod_eq_of_castHom_eq`
- **Used by** · `dirichlet_primes_in_AP` (the `n ≡ 2 [4]` corner)
- **Visibility** · private (theorem)
- **Lines** · 394–412
- **Notes** · uses `decide` for the `ZMod 2` unit fact.

---

### `private theorem dirichlet_AP_main`
- **Type** · `(n : ℕ) (hn4 : n % 4 ≠ 2) (hn : 1 ≤ n) (a : ZMod n) (ha : IsUnit a) → HasDirichletDensity ((fun p : ℕ ↦ Ideal.span {(p : 𝓞 ℚ)}) '' {p : ℕ | p.Prime ∧ (p : ZMod n) = a}) ((Nat.totient n : ℝ)⁻¹)`
- **What** · Main case of Dirichlet's AP theorem (where `n ≢ 2 [4]`, so `chebotarev_cyclotomic` applies): the density of rational primes `p ≡ a [n]` (as ideals `(p)` of `𝓞 ℚ`) is `1/φ(n)`.
- **How** · (&gt;30 lines.) Supply `NeZero n` and `NeZero ((n:ℕ):ℚ)`. Set `L := CyclotomicField n ℚ` with its instances (`CyclotomicField.isCyclotomicExtension`, `IsCyclotomicExtension.isGalois`, `IsCyclotomicExtension.isMulCommutative`). Take primitive root `ζ` and the iso `E := IsCyclotomicExtension.autEquivPow L hirr` (`Polynomial.cyclotomic.irreducible_rat` gives `hirr`). Define `σ := E.symm ha.unit`; verify `autToPow σ = a` (`hσ`) via `autEquivPow_apply` and `autToPow_eq_modularCyclotomicCharacter`. Get `hfib := chebotarev_cyclotomic ℚ L n hn4 σ` (density `1/|Gal|`), and rewrite `|Gal| = φ(n)` (`hcard`: `Nat.card_congr E.toEquiv`, `ZMod.card_units_eq_totient`). Set `F` = the Chebotarev Frobenius fibre of `σ`, `I` = the target image-set, `Bad` = image of primes dividing `n` (finite: subset of `Icc 0 n` via `Nat.le_of_dvd`). Show `F∖I ⊆ Bad` and `I∖F ⊆ Bad`: for each prime, use `ratPrime_eq_span` / `span_nat_isPrime` to get the underlying rational prime, `absNorm_span_nat` for its norm, split on coprimality / divisibility, and translate Frobenius ↔ residue via `frobeniusClass_eq_iff_residue` (and `unramifiedIn_cyclotomic_of_coprime` for the unramifiedness in the `hIF` branch). Conclude with `hasDirichletDensity_of_finite_symmDiff` applied to `hfib`.
- **Hypotheses** · `1 ≤ n`, `n ≢ 2 [4]`; `a` a unit mod `n`.
- **Uses from project** · `HasDirichletDensity`, `UnramifiedIn` (via `UnramifiedIn.ne_bot`), `frobeniusClass`, `chebotarev_cyclotomic`, `hasDirichletDensity_of_finite_symmDiff`, `ratPrime_eq_span`, `span_nat_isPrime`, `absNorm_span_nat`, `frobeniusClass_eq_iff_residue`, `unramifiedIn_cyclotomic_of_coprime`
- **Used by** · `dirichlet_primes_in_AP` (both branches)
- **Visibility** · private (theorem)
- **Lines** · 417–489
- **Notes** · &gt;30 lines; the analytic engine of the AP corollary. Inline comment (lines 423–424) on why `NeZero ((n:ℕ):ℚ)` is supplied manually.

---

### `theorem dirichlet_primes_in_AP`
- **Type** · `(n : ℕ) (hn : 1 ≤ n) (a : ZMod n) (ha : IsUnit a) → HasDirichletDensity ((fun p : ℕ ↦ Ideal.span {(p : 𝓞 ℚ)}) '' {p : ℕ | p.Prime ∧ (p : ZMod n) = a}) ((Nat.totient n : ℝ)⁻¹)`
- **What** · Dirichlet's theorem on primes in arithmetic progressions, as a density statement: for `gcd(a,n) = 1`, the Dirichlet density of primes `p ≡ a [n]` equals `1/φ(n)`. (Specialisation of Chebotarev to `K = ℚ`, `L = ℚ(μ_n)`.)
- **How** · Case split on `n % 4 = 2`. Easy case (`n % 4 ≠ 2`): directly `dirichlet_AP_main n hn4 hn a ha`. Degenerate corner (`n ≡ 2 [4]`): write `n = 2·n'` with `n'` odd (so `Coprime 2 n'`), set `a' = a mod n'` (a unit via `ha.map`). Get `hmain := dirichlet_AP_main n' … a' ha'` and rewrite `φ(2n') = φ(n')` (`Nat.totient_mul`, `Nat.totient_two`). The target image-sets `I2` (mod `2n'`) and `I'` (mod `n'`) differ only by the prime `2`: show both `I2∖I' ⊆ {(2)}` and `I'∖I2 ⊆ {(2)}`, splitting each prime on `p = 2` vs odd and using `residue_iff_half` for the equivalence. Conclude with `hasDirichletDensity_of_finite_symmDiff` (finite singleton diffs) applied to `hmain`.
- **Hypotheses** · `1 ≤ n`; `a` a unit mod `n` (i.e. `gcd(a,n) = 1`).
- **Uses from project** · `HasDirichletDensity`, `dirichlet_AP_main`, `hasDirichletDensity_of_finite_symmDiff`, `residue_iff_half`
- **Used by** · unused in file
- **Visibility** · public (theorem)
- **Lines** · 497–529
- **Notes** · &gt;30 lines.

---

`end Chebotarev` at line 531.

---

## File Summary

**Totals.** 16 declarations, all `theorem`s (no `def`, `instance`, `lemma`, `abbrev`, `structure`). 6 public + 10 `private`. No `sorry`, no `axiom`, no `set_option` anywhere in this file. The file closes both the `noncomputable section`/`@[expose] public section` (implicitly at EOF) and `namespace Chebotarev`.

**Public theorems (6):** `chebotarev_density`, `ConjClasses_carrier_card_eq_one_of_comm`, `chebotarev_density_of_comm`, `infinite_of_hasDirichletDensity_pos`, `ConjClasses_carrier_card_pos`, `infinite_setOf_frobenius_class`, `ConjClasses_mk_one_carrier_card_eq_one`, `density_split_completely`, `dirichlet_primes_in_AP` — (these are the non-`private` ones; the 6-vs-10 split: actually 9 are non-private and 7 are private — see correction below).

Correction on visibility tally: Non-`private` (9): `chebotarev_density`, `ConjClasses_carrier_card_eq_one_of_comm`, `chebotarev_density_of_comm`, `infinite_of_hasDirichletDensity_pos`, `ConjClasses_carrier_card_pos`, `infinite_setOf_frobenius_class`, `ConjClasses_mk_one_carrier_card_eq_one`, `density_split_completely`, `dirichlet_primes_in_AP`. `private` (7): `primeIdealZetaSum_eq_add_sub_sdiff`, `hasDirichletDensity_of_finite_symmDiff`, `zmod_eq_of_castHom_eq`, `absNorm_span_nat`, `ratPrime_eq_span`, `span_nat_isPrime`, `unramifiedIn_cyclotomic_of_coprime`, `frobeniusClass_eq_iff_residue`, `residue_iff_half`, `dirichlet_AP_main` — that is 10 private. Total 9 + 10 = 19. Re-counting the declarations themselves: there are exactly **19 theorems** in the file (I under-counted as 16 above). The 19: lines 99, 119, 131, 143, 149, 158, 169, 181, 209, 228, 242, 262, 273, 289, 305, 367, 394, 417, 497.

**Project API used by 3+ declarations:**
- `HasDirichletDensity` — used by 7 (`chebotarev_density`, `chebotarev_density_of_comm`, `infinite_of_hasDirichletDensity_pos`, `density_split_completely`, `hasDirichletDensity_of_finite_symmDiff`, `dirichlet_AP_main`, `dirichlet_primes_in_AP`).
- `UnramifiedIn` — used by 6 (`chebotarev_density`, `chebotarev_density_of_comm`, `infinite_setOf_frobenius_class`, `density_split_completely`, `unramifiedIn_cyclotomic_of_coprime`, `frobeniusClass_eq_iff_residue`, `dirichlet_AP_main`).
- `frobeniusClass` — used by 6 (`chebotarev_density`, `chebotarev_density_of_comm`, `infinite_setOf_frobenius_class`, `density_split_completely`, `frobeniusClass_eq_iff_residue`, `dirichlet_AP_main`).
- `hasDirichletDensity_of_finite_symmDiff` (in-file) — used by 3 (`dirichlet_AP_main`, `dirichlet_primes_in_AP`; defined once) — plus `primeIdealZetaSum_eq_add_sub_sdiff` underneath it.
- `chebotarev_density` (in-file) — used by 3 (`infinite_setOf_frobenius_class`, `density_split_completely`; `chebotarev_density_of_comm` is independent).

**Key external (Mathlib/other-project) dependencies driving the proofs:** `chebotarev_abelian` (the abelian case, from `Abelian.lean`), `density_lift_through_fixedField` (from `FixedFieldDensity.lean`), `chebotarev_cyclotomic` (from `Cyclotomic.lean`), `autToPow_frobeniusClass_out` (the cyclotomic Frobenius dictionary), `hasDirichletDensity_of_finite` and `primeIdealZetaSum_union_of_disjoint` (from `Density.lean`), and `Rat.ringOfIntegersEquiv` / `IsCyclotomicExtension.*` / `IsPrimitiveRoot.autToPow*` / `conductor_mul_differentIdeal` from Mathlib.

**Unused-in-file declarations (terminal results / corollaries — 5):** `chebotarev_density_of_comm`, `infinite_setOf_frobenius_class`, `density_split_completely`, `dirichlet_primes_in_AP` (all public final corollaries), and `ConjClasses_carrier_card_pos` IS used (`infinite_setOf_frobenius_class`), so it is not unused. Truly unused within this file: `chebotarev_density_of_comm`, `infinite_setOf_frobenius_class`, `density_split_completely`, `dirichlet_primes_in_AP`. (These are the public-facing API of the module, expected to be consumed downstream / by the blueprint, not internally.)

**`sorry` / `set_option` lists:** none of either — the file is `sorry`-free and `set_option`-free. (Note: per CLAUDE.md the *project's theorem proofs* are described as `sorry`, but this `Main.lean` discharges its results by composing imported lemmas; the remaining `sorry`s live in the imported files such as `Abelian.lean`, `Cyclotomic.lean`, `FixedFieldDensity.lean`, `Density.lean`, not here.)

**`&gt;30`-line proofs (4):** `unramifiedIn_cyclotomic_of_coprime` (305–361, ~57 lines), `dirichlet_AP_main` (417–489, ~73 lines), `dirichlet_primes_in_AP` (497–529, ~33 lines); borderline `frobeniusClass_eq_iff_residue` (367–389, ~23 lines) and `hasDirichletDensity_of_finite_symmDiff` (228–238) are under 30. Each &gt;30-line proof cites specific lemmas above (e.g. `conductor_mul_differentIdeal`, `chebotarev_cyclotomic`, `frobeniusClass_eq_iff_residue`, `residue_iff_half`).

**Structural note.** The file is two layers: (1) the Chebotarev capstone + qualitative corollaries (lines 99–188), each a thin composition over `chebotarev_abelian` / `density_lift_through_fixedField`; and (2) the Dirichlet-AP corollary (lines 190–529), a self-contained development specialising to `ℚ(μ_n)`, with its own prime-ideal-of-`𝓞 ℚ` dictionary (`ratPrime_eq_span`, `span_nat_isPrime`, `absNorm_span_nat`), CRT plumbing (`zmod_eq_of_castHom_eq`, `residue_iff_half`), a re-proved unramifiedness lemma, the Frobenius↔residue bridge, and the `n ≡ 2 [4]` corner handled by symmetric-difference stability.</result>
<usage><subagent_tokens>34728</subagent_tokens><tool_uses>1</tool_uses><duration_ms>152225</duration_ms></usage>
</task-notification>