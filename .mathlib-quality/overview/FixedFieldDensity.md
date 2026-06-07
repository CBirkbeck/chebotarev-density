# Inventory: `CebotarevDensity/FixedFieldDensity.lean`

**File role:** Step-1 fixed-field density transfer of Chebotarev (Sharifi 7.2.2 Step 1, p. 143). Establishes `δ_K(S) = (f·|C|/|G|)·δ_E(T_σ)` and packages it as `density_lift_through_fixedField`. Module header: `module` / `@[expose] public section` / `noncomputable section`; opens `Filter NumberField Topology Set`, scoped `ENNReal`; `namespace Chebotarev`. File-level `variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]` (lines 46–47).

Imports (lines 3–4): `Mathlib.RingTheory.Ideal.Over`, `CebotarevDensity.Cyclotomic` (transitively brings `Frobenius.lean`, `Density.lean`, `ZetaProduct.lean`).

---

### `theorem frobeniusFibre_card_eq_of_isConj`
- **Type:** For `𝔭` prime in `𝓞 K` unramified, `σ σ' : Gal(L/K)` with `IsConj σ σ'`, the Frobenius fibres `{𝔓 over 𝔭 : Frob_𝔓 = σ}` and `{… = σ'}` have equal `Nat.card`.
- **What:** Conjugate Frobenius values occur on equally many primes above `𝔭` ("distributed evenly", Sharifi p. 143).
- **How:** From `isConj_iff.mp hc` extract conjugator `c` with `c*σ*c⁻¹ = σ'`. Builds `Equiv.subtypeEquiv (MulAction.toPerm c)` and transports via `Nat.card_congr`. Forward: `𝔓 ≠ ⊥` is preserved by `Ideal.smul_bot` + injectivity of the action; `IsArithFrobAt σ' (c•𝔓)` from `hfrob.conj c`. Backward: uses `inv_smul_smul c 𝔓`, transports primality/`LiesOver` along `hsmul`, and `group` normalizes `c⁻¹*(c*σ*c⁻¹)*c⁻¹⁻¹ = σ`.
- **Hypotheses:** `[FiniteDimensional K L]`, `𝔭.IsPrime`, `UnramifiedIn K L 𝔭` (unused, `_hunr`), `IsConj σ σ'`. (Re-declares `K L` explicitly in signature.)
- **Uses from project:** `[]` (only mathlib: `IsArithFrobAt.conj`, `MulAction.toPerm`, `Ideal.smul_bot`, `isConj_iff`).
- **Used by:** `count_frobenius_eq_sigma_mul_card_carrier` (via the `hequi` argument).
- **Visibility:** public (`theorem`). **Lines:** 49–84 (decl 54–84). **Notes:** `open scoped Pointwise`; &gt;30 lines.

### `theorem card_primesAbove_eq_card_carrier_mul_frobeniusFibre`
- **Type:** `Nat.card {𝔓 over 𝔭} = Nat.card C.carrier * Nat.card {𝔓 over 𝔭 : Frob_𝔓 = σ}`.
- **What:** Total primes above `𝔭` equal `|C|` times the `σ`-fibre count, given every prime's Frobenius is in `C = [σ]` and conjugate values occur equally often (`hequi`).
- **How:** Partition the prime set by the class-valued Frobenius `F : 𝔓 ↦ ⟨arithFrobAt 𝔓, …⟩ : C.carrier` via `Equiv.sigmaFiberEquiv` + `Nat.card_sigma`. Membership `arithFrobAt 𝔓 ∈ C.carrier` from `ConjClasses.mem_carrier_iff_mk_eq` + `frobeniusClass_eq_mk_of_isArithFrobAt` + `hCfrob`. Each fibre `{F 𝔓 = g}` is bijective with the `σ`-fibre using `hequi g.1 (hconj g)`; the forward/back maps use `IsArithFrobAt.arithFrobAt` and uniqueness `eq_arithFrobAt_of_isArithFrobAt` (needing `Algebra.IsUnramifiedAt` via `isUnramifiedAt_iff_of_isDedekindDomain`). Closes with `Finset.sum_const`, `Finset.card_univ`. Finiteness of the prime set is injected from `IsDedekindDomain.primesOver_finite`.
- **Hypotheses:** `[FiniteDimensional K L]`, `ConjClasses.mk σ = C`, `𝔭.IsPrime`, `UnramifiedIn K L 𝔭`, `frobeniusClass K L 𝔭 = C`, and `hequi` (conjugate-fibre equality).
- **Uses from project:** `UnramifiedIn.ne_bot`, `UnramifiedIn.ramificationIdx_eq_one`, `ne_bot_of_ramificationIdx_eq_one`, `frobeniusClass_eq_mk_of_isArithFrobAt`, `eq_arithFrobAt_of_isArithFrobAt`.
- **Used by:** `count_frobenius_eq_sigma_mul_card_carrier`.
- **Visibility:** public. **Lines:** 86–154. **Notes:** `classical`; &gt;30 lines (uses `Ideal.finiteQuotientOfFreeOfNeBot`, `ConjClasses.mem_carrier_iff_mk_eq`, `Equiv.sigmaFiberEquiv`).

### `theorem count_frobenius_eq_sigma_mul_card_carrier`
- **Type:** `Nat.card {𝔓 over 𝔭 : Frob_𝔓 = σ} * Nat.card C.carrier = Nat.card {𝔓 over 𝔭}`.
- **What:** Same balanced count, written `σ`-fibre × |C| = total (commuted form).
- **How:** `(mul_comm _ _).trans (card_primesAbove_eq_card_carrier_mul_frobeniusFibre … fun σ' hc ↦ frobeniusFibre_card_eq_of_isConj …).symm` — supplies `frobeniusFibre_card_eq_of_isConj` as the `hequi` witness.
- **Hypotheses:** As the prior lemma (`_hσ`, `hunr`, `_hCfrob`).
- **Uses from project:** `[]` (composes two in-file lemmas + `frobeniusFibre_card_eq_of_isConj`).
- **Used by:** `count_primes_above_with_frobenius_eq_sigma`.
- **Visibility:** public. **Lines:** 156–170. **Notes:** —

### `theorem count_primes_above_with_frobenius_eq_sigma`
- **Type:** `Nat.card {𝔓 over 𝔭 : Frob_𝔓 = σ} * orderOf σ * Nat.card C.carrier = Nat.card Gal(L/K)`.
- **What:** The substantive count: the number of primes above `𝔭` with Frobenius exactly `σ` is `|G|/(f·|C|)` (Sharifi: "exactly `|G|/f|C|` of these have Frobenius σ", p. 143).
- **How:** `mul_right_comm`, then rewrite by `count_frobenius_eq_sigma_mul_card_carrier` to collapse the `σ`-fibre × |C| into total-primes-above, then apply `card_primesAbove_mul_orderOf_eq` (which is `|{𝔓 over 𝔭}|·f = |G|`).
- **Hypotheses:** As above.
- **Uses from project:** `card_primesAbove_mul_orderOf_eq`.
- **Used by:** `primeIdealZetaSum_fibre_eq_smul` (LEAF A), via `hcardfib`.
- **Visibility:** public. **Lines:** 172–195. **Notes:** docstring carries verbatim Sharifi quote.

### `theorem univ_ratio_E_K_tendsto_one`
- **Type:** `Tendsto (fun s ↦ Σ_univ^{𝓞 E} s / Σ_univ^{𝓞 K} s) (𝓝[&gt;] 1) (𝓝 1)`.
- **What:** Ratio of full prime-ideal zeta sums over intermediate field `E` and over `K` tends to 1 (Lean form of `Σ_𝔭 N𝔭⁻ˢ ~ Σ_P NP⁻ˢ`).
- **How:** Both numerator and denominator are asymptotic to `log(1/(s-1))` via `primeIdealZetaSum_univ_tendsto_log` (the `↥E` instance through `NumberField.of_intermediateField`); takes `.div … one_ne_zero`, rewrites `one_div_one`, then `congr'` on the eventually-positive set (`tendsto_log_one_div_sub_one_atTop.eventually_gt_atTop 0`) with `div_div_div_cancel_right₀`.
- **Hypotheses:** `omit [IsGalois K L]`; `[FiniteDimensional K L]`; `E : IntermediateField K L`.
- **Uses from project:** `primeIdealZetaSum_univ_tendsto_log`, `tendsto_log_one_div_sub_one_atTop` (both from `Density.lean`).
- **Used by:** `density_lift_through_fixedField` (`hmain`).
- **Visibility:** `private`. **Lines:** 197–212 (decl 203–212). **Notes:** `omit [IsGalois K L]`.

### `theorem arithFrobAt_restrictScalars_eq`
- **Type:** Under instances injected in the result type, `(arithFrobAt (𝓞 E) Gal(L/E) 𝔓).restrictScalars K = arithFrobAt (𝓞 K) Gal(L/K) 𝔓`.
- **What:** The E-bridge: the `E`-Frobenius restricted to `K` equals the `K`-Frobenius, when `N(𝔓∩𝓞 E) = N(𝔓∩𝓞 K)` (the "P ∩ E has degree one" condition). This is the new tower content mathlib lacks (it has only `isConj_arithFrobAt`).
- **How:** Set `σE, σK`. Shows `σE.restrictScalars K` is itself a `K`-Frobenius (`hKfrob1`): for each `x`, `(σE.restrictScalars K)•x = σE•x` (`AlgEquiv.restrictScalars_apply` + `AlgEquiv.smul_def`), and `x^N(𝔓∩K) = x^N(𝔓∩E)` by `hnorm`, reducing to `IsArithFrobAt.arithFrobAt (𝓞 E)`. Then two `K`-Frobenii agree by `IsArithFrobAt.mul_inv_mem_inertia` landing in the inertia group, which is trivial by `inertiaGroup_trivial_of_unramified` (so `mul_inv_eq_one`).
- **Hypotheses:** `[FiniteDimensional K L]`, `E : IntermediateField K L`, `𝔓.IsPrime`, `e(𝔓∣𝔓∩K)=1` (`hunrK`), `e(𝔓∣𝔓∩E)=1` (`_hunrE`, unused), `hnorm` (norm equality). Result type sets `IsScalarTower K ↥E L` (`isScalarTower_mid'`), `Finite (𝓞 L⧸𝔓)`, `IsGalois ↥E L`.
- **Uses from project:** `ne_bot_of_ramificationIdx_eq_one`, `inertiaGroup_trivial_of_unramified`. (mathlib: `IsArithFrobAt.arithFrobAt`, `.mul_inv_mem_inertia`, `Ideal.finiteQuotientOfFreeOfNeBot`, `IsGalois.tower_top_intermediateField`, `IsGaloisGroup.of_isGalois`.)
- **Used by:** `arithFrobAt_E_eq_of_isArithFrobAt`, `card_fibre_E_eq_card_fibre_L` (`hfrobK`), `frobeniusClass_under_eq_of_mem_fibre` (`hfrobK`).
- **Visibility:** public. **Lines:** 214–262 (decl 231–262). **Notes:** `open scoped Pointwise`; &gt;30 lines; instance-binders in the statement type.

### `theorem stabilizer_intermediate_eq_top_of_frobenius`
- **Type:** Under `IsScalarTower K ↥E L` (`E = fixedField ⟨σ⟩`), `MulAction.stabilizer Gal(L/E) 𝔓 = ⊤`.
- **What:** Decomposition group of `𝔓` equals `Gal(L/E)` ("P is by definition inert in L"); every `E`-automorphism fixes `𝔓`.
- **How:** Shows `D_𝔓 = ⟨σ⟩` in `Gal(L/K)`: `σ ∈ stab` (`hfrob.mem_stabilizer`); `|stab Gal(L/K) 𝔓| = orderOf σ` via `Ideal.card_stabilizer_eq` with `ramificationIdxIn=1` (`hraK`) and `inertiaDegIn = inertiaDeg = orderOf σ` (`Ideal.inertiaDeg_algebraMap` + `orderOf_eq_finrank_of_isArithFrobAt`); then `Subgroup.eq_of_le_of_card_ge` + `Nat.card_zpowers` gives `zpowers σ = stab`. Transfer to `Gal(L/E)`: any `τ` has `τ.restrictScalars K ∈ fixingSubgroup E` (`τ.commutes`), and `IntermediateField.fixingSubgroup_fixedField` turns this into membership in `zpowers σ = stab`, so `τ • 𝔓 = 𝔓`.
- **Hypotheses:** `[FiniteDimensional K L]`, `σ`, `𝔓.IsPrime`, `UnramifiedIn K L (𝔓∩𝓞K)` (`hunrK`), `𝔓.LiesOver (𝔓∩𝓞K)` (`hPK`), `IsArithFrobAt σ 𝔓`, `_horderE` (`ord σ = |Gal(L/E)|`, unused).
- **Uses from project:** `UnramifiedIn.ramificationIdx_eq_one`, `ne_bot_of_ramificationIdx_eq_one`, `UnramifiedIn.ne_bot`, `orderOf_eq_finrank_of_isArithFrobAt`.
- **Used by:** `inertiaDeg_under_E_eq_one_of_frobenius`, `eq_of_liesOver_under_E_of_frobenius`.
- **Visibility:** `private`. **Lines:** 264–315 (decl 272–315). **Notes:** `open scoped Pointwise`; &gt;30 lines (uses `IsGalois.to_isSeparable`, `Ideal.card_stabilizer_eq`).

### `theorem inertiaDeg_under_E_eq_one_of_frobenius`
- **Type:** Under `IsScalarTower K ↥E L`: conjunction `e(𝔓∣P)=1 ∧ f(P∣𝔭)=1 ∧ N P = N 𝔭`, where `P = 𝔓∩𝓞E`.
- **What:** The fixed-field prime below `𝔓` has degree one over `K` ("P has degree one over K", p. 143).
- **How:** `e(𝔓∣P)=1` from `Ideal.ramificationIdx_algebra_tower'` with `e(𝔓∣𝔭)=1` (`Nat.eq_one_of_mul_eq_one_left`). `f(𝔓∣P)=[L:E]` from `stabilizer_intermediate_eq_top_of_frobenius` fed into `Ideal.card_stabilizer_eq` (`Subgroup.card_top`, `ramificationIdxIn/inertiaDegIn = …`). Inertia tower `f(𝔓∣𝔭)=f(P∣𝔭)·f(𝔓∣P)` via `Ideal.inertiaDeg_eq_inertiaDeg'` + `Ideal.inertiaDeg'_tower`; with `f(𝔓∣𝔭)=ord σ` (`orderOf_eq_finrank_of_isArithFrobAt`) and `f(𝔓∣P)=ord σ` (from `horderE`), cancel `ord σ &gt; 0` (`Nat.eq_of_mul_eq_mul_right`) to get `f(P∣𝔭)=1`. Finally `N P = N 𝔭` from `Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver` + `pow_one`.
- **Hypotheses:** `[FiniteDimensional K L]`, `σ`, `𝔓.IsPrime`, `hunrK`, `hPK`, `IsArithFrobAt σ 𝔓`, `horderE` (used).
- **Uses from project:** `stabilizer_intermediate_eq_top_of_frobenius`, `UnramifiedIn.ramificationIdx_eq_one`, `ne_bot_of_ramificationIdx_eq_one`, `UnramifiedIn.ne_bot`, `orderOf_eq_finrank_of_isArithFrobAt`.
- **Used by:** `card_fibre_E_eq_card_fibre_L` (`hPmem`).
- **Visibility:** `private`. **Lines:** 317–397 (decl 324–397). **Notes:** `open scoped Pointwise`; &gt;30 lines (`Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver`, `Ideal.inertiaDeg'_tower`).

### `theorem eq_of_liesOver_under_E_of_frobenius`
- **Type:** Under `IsScalarTower K ↥E L`: for `𝔔.IsPrime` with `𝔔.LiesOver (𝔓∩𝓞E)`, `𝔔 = 𝔓`.
- **What:** `𝔓` is the unique prime of `𝓞 L` above `𝔓∩𝓞 E` ("P is by definition inert in L").
- **How:** `stabilizer Gal(L/E) 𝔓 = ⊤` (from `stabilizer_intermediate_eq_top_of_frobenius`) + transitivity of the Galois action on primes above `𝔓∩𝓞E` (`Ideal.exists_smul_eq_of_isGaloisGroup` gives `τ` with `τ•𝔓 = 𝔔`); since `τ ∈ ⊤ = stab`, `τ•𝔓 = 𝔓`, so `𝔔 = 𝔓`.
- **Hypotheses:** `[FiniteDimensional K L]`, `σ`, `𝔓.IsPrime`, `hunrK`, `hPK`, `IsArithFrobAt σ 𝔓`, `horderE`, `𝔔.IsPrime`, `hQ` (`𝔔.LiesOver (𝔓∩𝓞E)`, under instance binder).
- **Uses from project:** `stabilizer_intermediate_eq_top_of_frobenius`.
- **Used by:** `card_fibre_E_eq_card_fibre_L` (`hunram`, injectivity).
- **Visibility:** `private`. **Lines:** 399–425 (decl 403–425). **Notes:** `open scoped Pointwise`; uses `IsGaloisGroup.of_isGalois`, `Ideal.exists_smul_eq_of_isGaloisGroup`.

### `theorem arithFrobAt_E_eq_of_isArithFrobAt`
- **Type:** Under injected instances: `arithFrobAt (𝓞 E) Gal(L/E) 𝔓 = σE`.
- **What:** The fixed-field Frobenius below `𝔓` is `σ_E`, when `Frob^K_𝔓 = σ`, `σE` restricts to `σ`, and `P` has degree one.
- **How:** `arithFrobAt_restrictScalars_eq` gives `(Frob^E_𝔓).restrictScalars K = Frob^K_𝔓`; rewrite `Frob^K_𝔓 = σ` via `eq_arithFrobAt_of_isArithFrobAt`. So `(Frob^E_𝔓).restrictScalars K = σ = σE.restrictScalars K` (`hσE`), and `AlgEquiv.restrictScalars_injective K` concludes.
- **Hypotheses:** `[FiniteDimensional K L]`, `σ`, `σE`, `hσE` (restriction, under instance binder), `𝔓.IsPrime`, `hunrK`, `hPK`, `IsArithFrobAt σ 𝔓`, `_horderE` (unused), `hraE` (`e(𝔓∣P)=1`), `hnorm`. Result sets `IsScalarTower`, `Finite (𝓞 L⧸𝔓)`, `IsGalois ↥E L`.
- **Uses from project:** `arithFrobAt_restrictScalars_eq`, `eq_arithFrobAt_of_isArithFrobAt`, `UnramifiedIn.ramificationIdx_eq_one`, `ne_bot_of_ramificationIdx_eq_one`.
- **Used by:** `card_fibre_E_eq_card_fibre_L` (`hPmem`, via `hfrE`).
- **Visibility:** `private`. **Lines:** 427–471 (decl 432–471). **Notes:** `open scoped Pointwise`; &gt;30 lines; uses `Algebra.isUnramifiedAt_iff_of_isDedekindDomain`, `AlgEquiv.restrictScalars_injective`.

### `theorem card_fibre_E_eq_card_fibre_L`
- **Type:** Under `IsScalarTower K ↥E L`: `Nat.card {P of 𝓞E over 𝔭 : P prime, unram in L, Frob^E_P = [σE], f(P∣𝔭)=1} = Nat.card {𝔓 of 𝓞L over 𝔭 : Frob^K_𝔓 = σ}`.
- **What:** Fibre bijection — degree-one `E`-primes above `𝔭` with Frobenius `σ_E` correspond bijectively to `L`-primes above `𝔭` with Frobenius `σ` (Sharifi p. 143).
- **How:** The map is `𝔓 ↦ 𝔓∩𝓞E`. Membership (`hPmem`): bundles `inertiaDeg_under_E_eq_one_of_frobenius` (degree one + norm), `arithFrobAt_E_eq_of_isArithFrobAt` (Frob^E = σE), and unramified-in-L of `P` via `eq_of_liesOver_under_E_of_frobenius` (uniqueness of `𝔓` over `P`); `frobeniusClass = mk σE` via `frobeniusClass_eq_mk_of_isArithFrobAt` + `ConjClasses.mk_eq_mk_iff_isConj`; `under_under` aligns the base. Bijectivity via `Equiv.ofBijective`: injectivity uses `eq_of_liesOver_under_E_of_frobenius` (both `𝔓₁,𝔓₂` lie over the same `E`-prime ⟹ equal); surjectivity picks `𝔓` over `P` (`exists_prime_liesOver`), establishes `e(𝔓∣P)=1` from `UnramifiedIn ↥E L P`, `N P = N 𝔭` from `f(P∣𝔭)=1`, `Frob^E_𝔓 = σE` (abelian + `frobeniusClass P = mk σE`, via `isConj_iff_eq`), then `Frob^K_𝔓 = σ` from `arithFrobAt_restrictScalars_eq` + `hσE`.
- **Hypotheses:** `[FiniteDimensional K L]`, `σ`, `σE`, `hσE`, `[IsMulCommutative Gal(L/E)]`, `horderE`, `𝔭.IsPrime`, `UnramifiedIn K L 𝔭`, `_hCfrob` (unused).
- **Uses from project:** `UnramifiedIn.ne_bot`, `inertiaDeg_under_E_eq_one_of_frobenius`, `arithFrobAt_E_eq_of_isArithFrobAt`, `eq_of_liesOver_under_E_of_frobenius`, `frobeniusClass_eq_mk_of_isArithFrobAt`, `exists_prime_liesOver`, `arithFrobAt_restrictScalars_eq`, `UnramifiedIn.ramificationIdx_eq_one`.
- **Used by:** `primeIdealZetaSum_fibre_eq_smul` (LEAF A, `hreindex`).
- **Visibility:** `private`. **Lines:** 473–634 (decl 481–634). **Notes:** `open scoped Pointwise`; &gt;30 lines (the largest sub-lemma — full bijection construction with `Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver`, `Ideal.under_under`, `Algebra.isUnramifiedAt_iff_of_isDedekindDomain`).

### `theorem frobeniusClass_under_eq_of_mem_fibre`
- **Type:** `frobeniusClass K L (P.under (𝓞 K)) = ConjClasses.mk σ`.
- **What:** A degree-one fibre prime `P` of `𝓞 E` (unram in L, `Frob^E_P = [σE]`) has `K`-Frobenius class `[σ]` for `𝔭 = P∩𝓞K` (Sharifi p. 143).
- **How:** Pick `𝔓` over `P` (`exists_prime_liesOver`); align bases with `under_under`. Degree-one ⟹ `N P = N 𝔭`; `P`-unramified ⟹ `e(𝔓∣P)=1` (`isUnramifiedAt_iff_of_isDedekindDomain` via `hPunr.2`); `Frob^E_𝔓 = σE` (abelian + `frobeniusClass P = mk σE`, `isConj_iff_eq`); then `arithFrobAt_restrictScalars_eq` + `hσE` give `Frob^K_𝔓 = σ`. Conclude with `frobeniusClass_eq_mk_of_isArithFrobAt K L (𝔓∩𝓞K) …`.
- **Hypotheses:** `[FiniteDimensional K L]`, `σ`, `σE`, `hσE`, `[IsMulCommutative Gal(L/E)]`, `_horderE` (unused), `P.IsPrime`, `UnramifiedIn K L (P∩𝓞K)`, `UnramifiedIn ↥E L P`, `frobeniusClass ↥E L P = mk σE`, `f(P∩𝓞K, P)=1`, `P ≠ ⊥`.
- **Uses from project:** `exists_prime_liesOver`, `arithFrobAt_restrictScalars_eq`, `UnramifiedIn.ramificationIdx_eq_one`, `UnramifiedIn.ne_bot`, `frobeniusClass_eq_mk_of_isArithFrobAt`.
- **Used by:** `primeIdealZetaSum_fibre_eq_smul` (LEAF A, `hgmem`).
- **Visibility:** `private`. **Lines:** 636–708 (decl 640–708). **Notes:** `open scoped Pointwise`; &gt;30 lines; `Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver`, `Ideal.under_under`.

### `theorem primeIdealZetaSum_fibre_eq_smul` (LEAF A)
- **Type:** For `1 &lt; s`: `Σ_{T₁} s = (|G| / (ord σ · |C|)) · Σ_S s`, where `T₁` = degree-one (over K) `E`-primes with `Frob^E = [σE]` (and base unram in L) and `S` = `K`-primes with `Frob^K-class = [σ]`.
- **What:** The degree-one part of `T` carries the main term (Sharifi 7.2.2 p. 143): each `𝔭 ∈ S` has exactly `|G|/(f·|C|)` fibre primes `P`, and `N P = N 𝔭`.
- **How:** Fibre projection `g : T₁' → S'`, `P ↦ P∩𝓞K`; membership in `S` from `frobeniusClass_under_eq_of_mem_fibre`. Per-fibre count `(ord σ · |C|)·|fibre| = |G|` (`hcardfib`): reindexes the `g`-fibre to `card_fibre_E_eq_card_fibre_L`'s set, then `count_primes_above_with_frobenius_eq_sigma`. Each fibre finite via `IsDedekindDomain.primesOver_finite`. `N P = N(P∩𝓞K)` for degree-one `P` (`hnormeq`, `Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver` + `pow_one`). Unfolds `primeIdealZetaSum_def`, regroups the `T₁`-summand `N P⁻ˢ = h(g P)` over the `K`-prime fibre via `HasSum.tsum_fiberwise`/`tsum_fiberwise`; inner sum is constant `h 𝔭` on each finite fibre (`tsum_fintype`, `Finset.sum_const`), giving the scalar `|G|/(ord σ·|C|)` (`eq_div_iff`), then `tsum_mul_left`.
- **Hypotheses:** `[FiniteDimensional K L]`, `σ`, `σE`, `hσE`, `[IsMulCommutative Gal(L/E)]`, `horderE`, `1 &lt; s`.
- **Uses from project:** `frobeniusClass_under_eq_of_mem_fibre`, `card_fibre_E_eq_card_fibre_L`, `count_primes_above_with_frobenius_eq_sigma`, `summable_prime_absNorm_rpow`, `primeIdealZetaSum_def`.
- **Used by:** `density_lift_through_fixedField` (`hleafA`).
- **Visibility:** `private`. **Lines:** 710–848 (decl 718–848). **Notes:** `open scoped Pointwise`; `classical`; &gt;30 lines (`Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver`, `HasSum.tsum_fiberwise`, `Equiv.subtypeEquivRight`).

### `theorem tsum_comp_le_card_fibre_mul`
- **Type:** For `g : β → γ`, `f : γ → ℝ≥0∞`, `d : ℕ` with each fibre finite of size `≤ d`: `∑' b, f (g b) ≤ d · ∑' y, f y`.
- **What:** Generic fibre-counting bound for `ℝ≥0∞`-valued sums.
- **How:** `ENNReal.tsum_fiberwise` regroups `b` by `g b`; `ENNReal.tsum_mul_left` pulls out `d`; on each fibre the summand is constant `f y` (`tsum_fintype`, `Finset.sum_const`), and `gcongr` + `hfib` bounds the count by `d`.
- **Hypotheses:** `{β γ : Type*}`; `hfin` (fibres finite), `hfib` (`Nat.card ≤ d`).
- **Uses from project:** `[]` (pure mathlib).
- **Used by:** `primeIdealZetaSum_degTwo_le` (`hchain`).
- **Visibility:** `private`. **Lines:** 863–876 (decl 866–876). **Notes:** generic helper, not field-specific.

### `theorem primeIdealZetaSum_degTwo_le`
- **Type:** For `1 &lt; s` and `Aset` = `E`-primes with base unram in `L` but `f(P∣𝔭) ≥ 2`: `Σ_A s ≤ [E:K] · Σ_univ^{𝓞 K} 2`.
- **What:** The degree-≥2 part of `T₂` is bounded by a constant (Sharifi p. 143).
- **How:** Per-term `N P⁻ˢ ≤ N(P∩𝓞K)⁻²` (`hterm`): `N P = N𝔭^f` (`Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver`), `N𝔭 ≥ 2` (`absNorm_eq_zero/one_iff` + `omega`), then `Real.rpow_le_rpow_of_exponent_le` with `2·1 ≤ f·s` (`nlinarith`). Each `K`-prime fibre is finite with `≤ [E:K]` primes above (`hinj`): injects into `primesOver`, `Nat.card_le_card_of_injective`, then `Ideal.card_primesOverFinset_le_finrank`. Converts both sums to `ℝ≥0∞` (`ENNReal.ofReal_tsum_of_nonneg`, `summable_prime_absNorm_rpow`), chains via `tsum_comp_le_card_fibre_mul`, and `ENNReal.toReal_mono` + `toReal_mul`/`toReal_natCast`.
- **Hypotheses:** `[FiniteDimensional K L]`, `σ`, `1 &lt; s`, `Aset`, `hA` (defining equation).
- **Uses from project:** `tsum_comp_le_card_fibre_mul`, `summable_prime_absNorm_rpow`, `primeIdealZetaSum_def`.
- **Used by:** `primeIdealZetaSum_T2_div_univ_tendsto_zero` (LEAF B).
- **Visibility:** `private`. **Lines:** 878–996 (decl 885–996). **Notes:** `open scoped Pointwise`; `classical`; &gt;30 lines (`Ideal.card_primesOverFinset_le_finrank`, `IsDedekindDomain.coe_primesOverFinset`, local `NoZeroSMulDivisors` instance).

### `theorem ramifiedBelow_finite`
- **Type:** For `Bset` = `E`-primes whose `K`-base is ramified in `L`: `Bset.Finite`.
- **What:** The ramified part of `T₂` is a finite set.
- **How:** `Bset ⊆ ⋃_{𝔭 ∈ ramified} primesOver 𝔭`, and the ramified `K`-primes are finite (`finite_ramifiedIn`); each `K`-prime has finitely many `E`-primes above (`IsDedekindDomain.primesOver_finite`), so `Set.Finite.biUnion` + `Set.Finite.subset`. Membership uses `Ideal.IsIntegral.comap_ne_bot` and `Ideal.over_under`.
- **Hypotheses:** `[FiniteDimensional K L]`, `σ`, `Bset`, `hB`.
- **Uses from project:** `finite_ramifiedIn`.
- **Used by:** `primeIdealZetaSum_T2_div_univ_tendsto_zero` (LEAF B, `hBfin`).
- **Visibility:** `private`. **Lines:** 998–1018 (decl 1003–1018). **Notes:** `open scoped Pointwise`; `classical`.

### `theorem primeIdealZetaSum_T2_div_univ_tendsto_zero` (LEAF B)
- **Type:** `Tendsto (fun s ↦ Σ_{T₂} s / Σ_univ^{𝓞 E} s) (𝓝[&gt;] 1) (𝓝 0)`, where `T₂ = T ∖ T₁`.
- **What:** The non-degree-one part of `T` vanishes in the density ratio — the asymptotic content `Σ_𝔭 N𝔭⁻ˢ ~ Σ_P NP⁻ˢ` that the (false) exact identity elided (Sharifi p. 143).
- **How:** `T₂ ⊆ A ∪ B` (disjoint), with `A` = unramified-below but `f ≥ 2`, `B` = ramified-below (`hsub` by `by_cases hunrK`, using `Ideal.inertiaDeg_pos'` + `omega`; `hdisj` by `Set.disjoint_left`). `B` finite (`ramifiedBelow_finite`). Bounds `Σ_{T₂} s` by the constant `C = [E:K]·Σ_univ^K 2 + |B|` via `primeIdealZetaSum_le_of_subset`, `primeIdealZetaSum_union_of_disjoint`, `primeIdealZetaSum_degTwo_le`, `primeIdealZetaSum_le_card_of_finite`; then `tendsto_primeIdealZetaSum_div_univ_zero_of_le_const` (since `Σ_univ^E → ∞`).
- **Hypotheses:** `[FiniteDimensional K L]`, `σ`, `σE`, `T₂set`, `hT₂` (defining equation).
- **Uses from project:** `ramifiedBelow_finite`, `primeIdealZetaSum_le_of_subset`, `primeIdealZetaSum_union_of_disjoint`, `primeIdealZetaSum_degTwo_le`, `primeIdealZetaSum_le_card_of_finite`, `tendsto_primeIdealZetaSum_div_univ_zero_of_le_const`.
- **Used by:** `density_lift_through_fixedField` (`hleafB`).
- **Visibility:** `private`. **Lines:** 1020–1093 (decl 1031–1093). **Notes:** `open scoped Pointwise`; &gt;30 lines; `IsGalois.tower_top_intermediateField`.

### `theorem density_lift_through_fixedField` (terminal export)
- **Type:** Given the abelian-case density `1/|Gal(L/E)|` of the `σE`-Frobenius fibre over `E`, `HasDirichletDensity {𝔭 : K-prime unram, Frob^K-class = [σ]} (|C| / |G|)`.
- **What:** The complete Step-1 density lift: `δ_K(S) = (f·|C|/|G|)·δ_E(T_σ) = |C|/|G|` (Sharifi 7.2.2 Step 1, p. 143, with verbatim source quote in docstring).
- **How:** `subst _hEfix` (so `E = fixedField ⟨σ⟩`). Establishes `|Gal(L/E)| = ord σ` (`horder`, via `IntermediateField.subgroupEquivAlgEquiv` + `Nat.card_zpowers`) and `IsMulCommutative Gal(L/E)` (from `mul_comm'` through the subgroup-equiv). Splits `Σ_T = Σ_{T₁} + Σ_{T₂}` (`hsplit`, disjoint). `hleafB`: `Σ_{T₂}/Σ_univ^E → 0`. `htendT₁`: `Σ_{T₁}/Σ_univ^E → 1/f` (`_hab.sub hleafB`, `sub_zero`, `congr'` with `hsplit`). Assembles `δ_K(S)` as `(f|C|/|G|)·(Σ_{T₁}/Σ_univ^E)·(Σ_univ^E/Σ_univ^K)` (`hmain`, via `htendT₁.const_mul` + `univ_ratio_E_K_tendsto_one`), evaluates the limit constant to `|C|/|G|` (`hval`, `field_simp`). Final `congr'` uses LEAF A flattened (`hT₁flat` + `primeIdealZetaSum_fibre_eq_smul`): `Σ_S = (f|C|/|G|)·Σ_{T₁}` (`hSeq`, with `hAB` cancellation), then `div_mul_div_cancel₀` to clear `Σ_univ^E` and `ring`.
- **Hypotheses:** `[FiniteDimensional K L]`, `σ : Gal(L/K)`, `E : IntermediateField K L`, `σE : Gal(L/E)`, `hσE` (`σE` restricts to `σ`), `_hEfix` (`E = fixedField ⟨σ⟩`), `_hab` (abelian density over E, value `1/|Gal(L/E)|`).
- **Uses from project:** `univ_ratio_E_K_tendsto_one`, `primeIdealZetaSum_fibre_eq_smul` (LEAF A), `primeIdealZetaSum_T2_div_univ_tendsto_zero` (LEAF B), `primeIdealZetaSum_union_of_disjoint`, `primeIdealZetaSum_univ_tendsto_atTop`. (mathlib: `HasDirichletDensity`, `IntermediateField.subgroupEquivAlgEquiv`, `Nat.card_zpowers`, `IsMulCommutative.of_comm`.)
- **Used by:** unused in file. **External consumers:** `Main.lean:112` (`chebotarev_density`) and `Abelian.lean:640` (via `density_lift_through_fixedField_repl`).
- **Visibility:** public (terminal export). **Lines:** 1095–1226 (decl 1113–1226). **Notes:** &gt;30 lines; carries verbatim Sharifi quote in docstring.

---

## File Summary

**Totals:** 16 declarations, all `theorem` (no `def`, no `structure`, no `instance`). 6 public, 10 `private`. **0 `sorry`, 0 `set_option`, 0 `axiom`, 0 `TODO`** in this file.

**Visibility split:**
- Public (6): `frobeniusFibre_card_eq_of_isConj`, `card_primesAbove_eq_card_carrier_mul_frobeniusFibre`, `count_frobenius_eq_sigma_mul_card_carrier`, `count_primes_above_with_frobenius_eq_sigma`, `arithFrobAt_restrictScalars_eq`, `density_lift_through_fixedField`.
- Private (10): `univ_ratio_E_K_tendsto_one`, `stabilizer_intermediate_eq_top_of_frobenius`, `inertiaDeg_under_E_eq_one_of_frobenius`, `eq_of_liesOver_under_E_of_frobenius`, `arithFrobAt_E_eq_of_isArithFrobAt`, `card_fibre_E_eq_card_fibre_L`, `frobeniusClass_under_eq_of_mem_fibre`, `primeIdealZetaSum_fibre_eq_smul`, `tsum_comp_le_card_fibre_mul`, `primeIdealZetaSum_degTwo_le`, `ramifiedBelow_finite`, `primeIdealZetaSum_T2_div_univ_tendsto_zero`. (Note: that lists 12 — recount: the 10 private are `univ_ratio_E_K_tendsto_one`, `stabilizer_intermediate_eq_top_of_frobenius`, `inertiaDeg_under_E_eq_one_of_frobenius`, `eq_of_liesOver_under_E_of_frobenius`, `arithFrobAt_E_eq_of_isArithFrobAt`, `card_fibre_E_eq_card_fibre_L`, `frobeniusClass_under_eq_of_mem_fibre`, `primeIdealZetaSum_fibre_eq_smul`, `tsum_comp_le_card_fibre_mul`, `primeIdealZetaSum_degTwo_le`, `ramifiedBelow_finite`, `primeIdealZetaSum_T2_div_univ_tendsto_zero` — that is **12 private**, so totals are **16 declarations, 4 public + 12 private**. The 4 public are the four counting lemmas `frobeniusFibre_card_eq_of_isConj`, `card_primesAbove_eq_card_carrier_mul_frobeniusFibre`, `count_frobenius_eq_sigma_mul_card_carrier`, `count_primes_above_with_frobenius_eq_sigma`, `arithFrobAt_restrictScalars_eq`, and `density_lift_through_fixedField` — that is **6 public**. Recounting cleanly below.)

**Authoritative count:** 18 theorems total. **6 public** (`frobeniusFibre_card_eq_of_isConj`, `card_primesAbove_eq_card_carrier_mul_frobeniusFibre`, `count_frobenius_eq_sigma_mul_card_carrier`, `count_primes_above_with_frobenius_eq_sigma`, `arithFrobAt_restrictScalars_eq`, `density_lift_through_fixedField`); **12 private** (the remaining). No defs/instances/axioms.

**Project API used by ≥3 in-file declarations (key shared dependencies):**
- `UnramifiedIn.ramificationIdx_eq_one` (Frobenius.lean) — 6 uses
- `ne_bot_of_ramificationIdx_eq_one` (Frobenius.lean) — 5 uses
- `UnramifiedIn.ne_bot` (Frobenius.lean) — 5 uses
- `frobeniusClass_eq_mk_of_isArithFrobAt` (Frobenius.lean) — 4 uses
- `arithFrobAt_restrictScalars_eq` (in-file) — 3 uses
- `orderOf_eq_finrank_of_isArithFrobAt` (Frobenius.lean) — 3 uses
- `stabilizer_intermediate_eq_top_of_frobenius` (in-file) — used by 2; `exists_prime_liesOver`, `summable_prime_absNorm_rpow`, `primeIdealZetaSum_def` each used by ≥2.

Heavy mathlib API across the file: `Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver`, `Ideal.over_under`, `Ideal.under_under`, `Ideal.IsIntegral.comap_ne_bot`, `Ideal.finiteQuotientOfFreeOfNeBot`, `IsArithFrobAt.arithFrobAt`, `Algebra.isUnramifiedAt_iff_of_isDedekindDomain`, `IsGalois.tower_top_intermediateField`, `IntermediateField.isScalarTower_mid'`, `IsDedekindDomain.primesOver_finite`.

**Unused-in-file declarations:** only `density_lift_through_fixedField` (the terminal export — consumed externally by `Main.lean` for `chebotarev_density` and by `Abelian.lean` via `density_lift_through_fixedField_repl`). Every other declaration is consumed by a later declaration in this file (linear dependency chain bottoming out at the two LEAVES → `density_lift_through_fixedField`).

**`sorry` list:** none.
**`set_option` list:** none.
**`axiom` list:** none.

**&gt;30-line declarations (12):** `frobeniusFibre_card_eq_of_isConj` (49–84), `card_primesAbove_eq_card_carrier_mul_frobeniusFibre` (86–154), `arithFrobAt_restrictScalars_eq` (214–262), `stabilizer_intermediate_eq_top_of_frobenius` (264–315), `inertiaDeg_under_E_eq_one_of_frobenius` (317–397), `arithFrobAt_E_eq_of_isArithFrobAt` (427–471), `card_fibre_E_eq_card_fibre_L` (473–634, the largest), `frobeniusClass_under_eq_of_mem_fibre` (636–708), `primeIdealZetaSum_fibre_eq_smul` (710–848), `primeIdealZetaSum_degTwo_le` (878–996), `primeIdealZetaSum_T2_div_univ_tendsto_zero` (1020–1093), `density_lift_through_fixedField` (1095–1226).

**`open scoped Pointwise in` decorators:** on 11 declarations (all the Frobenius/fixed-field geometry lemmas — from `frobeniusFibre_card_eq_of_isConj` through `primeIdealZetaSum_T2_div_univ_tendsto_zero` and the terminal `density_lift_through_fixedField`).

**`classical` tactic:** used in `card_primesAbove_eq_card_carrier_mul_frobeniusFibre`, `primeIdealZetaSum_fibre_eq_smul`, `primeIdealZetaSum_degTwo_le`, `ramifiedBelow_finite`.

**Structural note:** The file is a single proof spine. Two LEAVES (`primeIdealZetaSum_fibre_eq_smul` = LEAF A, the exact main-term identity; `primeIdealZetaSum_T2_div_univ_tendsto_zero` = LEAF B, the vanishing asymptotic tail) feed the terminal `density_lift_through_fixedField`. The four public counting lemmas (`frobeniusFibre…` → `card_primesAbove…` → `count_frobenius…` → `count_primes_above_with_frobenius_eq_sigma`) form the combinatorial backbone that LEAF A consumes; the geometric tower lemmas (`arithFrobAt_restrictScalars_eq`, `stabilizer_intermediate_eq_top_of_frobenius`, `inertiaDeg_under_E_eq_one_of_frobenius`, `eq_of_liesOver_under_E_of_frobenius`, `arithFrobAt_E_eq_of_isArithFrobAt`) build the fibre bijection `card_fibre_E_eq_card_fibre_L` and the back-direction class lemma `frobeniusClass_under_eq_of_mem_fibre`, also consumed by LEAF A. The whole file is `sorry`-free.</result>
<usage><subagent_tokens>72358</subagent_tokens><tool_uses>8</tool_uses><duration_ms>195413</duration_ms></usage>
</task-notification>