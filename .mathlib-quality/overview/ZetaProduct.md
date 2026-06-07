# Inventory: `CebotarevDensity/ZetaProduct.lean` (3598 lines)

All declarations live in `namespace Chebotarev`. Section wrapper: `@[expose] public section` + `noncomputable section`, `open NumberField`. Project-external dependencies referenced throughout: `UnramifiedIn`, `frobeniusClass`, `finrank_residue_eq_orderOf`, `card_primesAbove_mul_orderOf_eq`, `finite_ramifiedIn` (Frobenius.lean); `NonzeroIdeal`, `idealNormMultiplicity`, `weighted_eulerProduct_eq_tsum`, `hasSum_nonzeroIdeal_absNorm_cpow`, `dedekindZeta_eq_tprod_primeIdeal`, `dedekindZeta_re_pos_of_one_lt`, `dedekindZeta_eq_tsum_idealNormMultiplicity`, `summable_idealNormMultiplicity_mul_cpow_neg`, `sum_idealNormMultiplicity_isBigO` (NumberFieldEulerProduct.lean); `logDedekindZeta_sub_log_inv_sub_one_bounded` (Density.lean); `autToPow_frobeniusClass_out`, `subgroup_eq_top_of_forall_frobenius_mem_of_coprime` (CyclotomicNormResidue.lean); `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`, `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized` (IdealCongruenceCount.lean); `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` (LatticePointCount.lean); `normLeOne_frontier_lipschitz_cover` (NormLeOneLipschitz.lean); `tendsto_log_one_div_sub_one_atTop` (ForMathlib/LogOneDivSubOne.lean).

---

### `abbrev galoisCharacter`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] : Type _ := Gal(L/K) →* ℂˣ`
- **What**: A character of the Galois group `Gal(L/K)` valued in `ℂˣ`.
- **How**: Definitional abbreviation for the monoid-hom type `Gal(L/K) →* ℂˣ`.
- **Hypotheses**: `L/K` a Galois extension of number fields.
- **Uses from project**: []
- **Used by**: nearly every declaration in the file (the central object).
- **Visibility** public · **Lines** 70–73 · **Notes** —

### `def galoisCharacterOnIdeal`
- **Type**: `(K L …) (χ : galoisCharacter K L) (𝔞 : Ideal (𝓞 K)) : ℂ`
- **What**: The completely-multiplicative extension of `χ` to nonzero ideals (Sharifi Notation 7.1.17): the L-function coefficient `χ(𝔞)`.
- **How**: Product over `(normalizedFactors 𝔞).toFinset` of `(if UnramifiedIn then χ(Frob 𝔭) else 0)` raised to the multiplicity `count 𝔭`.
- **Hypotheses**: none beyond the `variable` typeclasses.
- **Uses from project**: `UnramifiedIn`, `frobeniusClass`
- **Used by**: `galoisCharacterOnIdeal_eq_map_prod`, `galoisCharacterOnIdeal_apply_prime`, `norm_galoisCharacterOnIdeal_le_one`, and ~25 downstream lemmas
- **Visibility** public (noncomputable, `open Classical`) · **Lines** 80–84 · **Notes** —

### `theorem galoisCharacterOnIdeal_eq_map_prod`
- **Type**: `… : galoisCharacterOnIdeal K L χ 𝔞 = ((normalizedFactors 𝔞).map (fun 𝔭 =&gt; if UnramifiedIn K L 𝔭 then χ(Frob 𝔭) else 0)).prod`
- **What**: Rewrites `galoisCharacterOnIdeal` as a `Multiset.map`-product over prime factors with multiplicity (instead of `toFinset`+`count`).
- **How**: Single rewrite by `Finset.prod_multiset_map_count`.
- **Hypotheses**: none.
- **Uses from project**: `galoisCharacterOnIdeal`
- **Used by**: `galoisCharacterOnIdeal_apply_prime`, `galoisCharacterOnIdeal_mul`, `galoisCharacterOnIdeal_one`, `galoisCharacterOnIdeal_eq_char_frobeniusIdeal`, `card_valueFibre_…`, `galoisCharacterOnIdeal_mem_insert_zero_nthRootsFinset`
- **Visibility** private (`open Classical`) · **Lines** 91–97 · **Notes** —

### `theorem galoisCharacterOnIdeal_apply_prime`
- **Type**: `… (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) : galoisCharacterOnIdeal K L χ 𝔭 = if UnramifiedIn K L 𝔭 then χ(Frob 𝔭) else 0`
- **What**: On a nonzero prime, the ideal character equals `χ(Frob 𝔭)` if unramified and `0` otherwise.
- **How**: `normalizedFactors` of a prime is the singleton `{𝔭}` (`normalizedFactors_irreducible`), so the map-product collapses to one factor.
- **Hypotheses**: `𝔭` a nonzero prime (the `≠ ⊥` is essential: empty product is `1`).
- **Uses from project**: `galoisCharacterOnIdeal_eq_map_prod`, `UnramifiedIn`, `frobeniusClass`
- **Used by**: `exists_artinLSeries_eulerProduct_abelian`
- **Visibility** public (`open Classical`) · **Lines** 104–111 · **Notes** —

### `theorem galoisCharacterOnIdeal_mul`
- **Type**: `… {𝔞 𝔟} (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥) : galoisCharacterOnIdeal K L χ (𝔞 * 𝔟) = galoisCharacterOnIdeal K L χ 𝔞 * galoisCharacterOnIdeal K L χ 𝔟`
- **What**: The ideal character is completely multiplicative on nonzero ideals.
- **How**: `normalizedFactors_mul` makes the factor multiset additive; `Multiset.map_add` + `Multiset.prod_add` split the product.
- **Hypotheses**: both ideals nonzero.
- **Uses from project**: `galoisCharacterOnIdeal_eq_map_prod`
- **Used by**: `exists_artinLSeries_eulerProduct_abelian`
- **Visibility** public · **Lines** 115–122 · **Notes** —

### `theorem galoisCharacterOnIdeal_one`
- **Type**: `… : galoisCharacterOnIdeal K L χ ⊤ = 1`
- **What**: The ideal character of the unit ideal is `1`.
- **How**: `normalizedFactors_one = 0`, so the map-product is the empty product `1`.
- **Hypotheses**: none.
- **Uses from project**: `galoisCharacterOnIdeal_eq_map_prod`
- **Used by**: `exists_artinLSeries_eulerProduct_abelian`
- **Visibility** public · **Lines** 125–130 · **Notes** —

### `lemma norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded`
- **Type**: `{E} [NormedAddCommGroup E] [NormedSpace ℝ E] {a : ℕ→ℝ} {z : ℕ→E} {B} (ha : Antitone a) (ha_nonneg) (hbound : ∀n, ‖∑_{i&lt;n} z i‖ ≤ B) (n) : ‖∑_{i&lt;n} a i • z i‖ ≤ B * a 0`
- **What**: Summation-by-parts (Dirichlet test) bound for a weighted sum with antitone nonnegative weights and bounded partial sums.
- **How**: `Finset.sum_range_by_parts`, then bound the Abel-summed difference sum by a telescoping `Finset.sum_range_sub'` and the leading term; `gcongr`/`norm_sub_le`. (&gt;30-line proof; cites `Finset.sum_range_by_parts`.)
- **Hypotheses**: `a` antitone, `a ≥ 0`, partial sums of `z` bounded by `B`.
- **Uses from project**: []
- **Used by**: `norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded`
- **Visibility** public · **Lines** 136–183 · **Notes** &gt;30-line proof; ported from flt-regular-bernoulli

### `lemma norm_sum_range_shift_le_of_bounded`
- **Type**: `{E} [NormedAddCommGroup E] {z : ℕ→E} {B} (hbound) (m n) : ‖∑_{i&lt;n} z (m+i)‖ ≤ 2 * B`
- **What**: Partial sums of a shifted sequence are bounded by `2B`.
- **How**: Writes the shifted sum as a difference of two ordinary partial sums (`Finset.sum_range_add`), then triangle inequality.
- **Hypotheses**: partial sums of `z` bounded by `B`.
- **Uses from project**: []
- **Used by**: `norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded`
- **Visibility** public · **Lines** 187–200 · **Notes** —

### `lemma norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded`
- **Type**: `… (ha) (ha_nonneg) (hbound) (m n) : ‖∑_{i&lt;n} a (m+i) • z (m+i)‖ ≤ 2 * B * a m`
- **What**: Tail sums of a weighted series inherit the summation-by-parts bound (up to factor 2).
- **How**: Applies `norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded` to the shifted sequences with bound `2B` from `norm_sum_range_shift_le_of_bounded`.
- **Hypotheses**: as the base lemma.
- **Uses from project**: `norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded`, `norm_sum_range_shift_le_of_bounded`
- **Used by**: unused in file (Dirichlet-test API; consumers are downstream/other files)
- **Visibility** public · **Lines** 204–213 · **Notes** —

### `theorem norm_galoisCharacter_out`
- **Type**: `… (χ) (c : ConjClasses Gal(L/K)) : ‖(χ c.out : ℂ)‖ = 1`
- **What**: A Galois character on the chosen representative of a conjugacy class has norm 1 (it is a root of unity).
- **How**: `c.out` has finite order (finite group), so `χ c.out` is a root of unity; `Complex.norm_eq_one_of_pow_eq_one`.
- **Hypotheses**: `Gal(L/K)` finite (from `IsGalois` + number fields).
- **Uses from project**: []
- **Used by**: `norm_galoisCharacterOnIdeal_le_one`, `multipliable_artinLocalFactor`
- **Visibility** private · **Lines** 244–250 · **Notes** —

### `theorem norm_galoisCharacterOnIdeal_le_one`
- **Type**: `… (χ) (𝔞) : ‖galoisCharacterOnIdeal K L χ 𝔞‖ ≤ 1`
- **What**: The ideal character has norm `≤ 1`.
- **How**: `norm_prod`; each factor is either a norm-1 root of unity (unramified, via `norm_galoisCharacter_out`) or `0` (ramified), so `Finset.prod_le_one`.
- **Hypotheses**: none.
- **Uses from project**: `galoisCharacterOnIdeal`, `norm_galoisCharacter_out`, `UnramifiedIn`
- **Used by**: `norm_galoisCharacterCoeff_le`, `lseries_galoisCharacterCoeff_eq_tsum`, `log_norm_artinDirichletSeries_one_le`
- **Visibility** private (`open Classical`) · **Lines** 255–268 · **Notes** —

### `theorem exists_artinLSeries_eulerProduct_abelian`
- **Type**: `… [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (χ) : ∀ s, 1 &lt; s.re → (∏' 𝔭 unram, (1 - χ(Frob 𝔭)·N𝔭^{-s})⁻¹) = ∑' 𝔞≠⊥, χ(𝔞)·N𝔞^{-s}`
- **What**: Sharifi 7.1.18 — Euler product of an abelian character equals its Dirichlet series, for `Re s &gt; 1`.
- **How**: Instantiates the generic `weighted_eulerProduct_eq_tsum` with weight `galoisCharacterOnIdeal`; the all-primes product restricts to unramified primes because the weight is `0` (factor `=1`) at ramified primes (`tprod_eq` over `Set.range g`, mulSupport argument). (&gt;30-line proof.)
- **Hypotheses**: `L/K` finite abelian; `Re s &gt; 1`.
- **Uses from project**: `weighted_eulerProduct_eq_tsum`, `galoisCharacterOnIdeal`, `galoisCharacterOnIdeal_one`, `galoisCharacterOnIdeal_mul`, `norm_galoisCharacterOnIdeal_le_one`, `galoisCharacterOnIdeal_apply_prime`, `UnramifiedIn`, `frobeniusClass`
- **Used by**: `tprod_unramified_eq_prod_artinDirichletSeries`
- **Visibility** public · **Lines** 281–316 · **Notes** &gt;30-line proof

### `theorem prod_one_sub_nthRoots`
- **Type**: `(f : ℕ) (hf : 0 &lt; f) (Y : ℂ) : ∏_{ζ ∈ nthRootsFinset f 1} (1 - ζ·Y) = 1 - Y^f`
- **What**: Over `ℂ`, the product over `f`-th roots of unity of `(1 - ζY)` is `1 - Y^f`.
- **How**: Evaluates `Polynomial.X_pow_sub_one_eq_prod` at `Y⁻¹` and rescales by `Y^f` (after handling `Y=0`); `field_simp` per factor + `Finset.prod_const`.
- **Hypotheses**: `f &gt; 0`.
- **Uses from project**: []
- **Used by**: `prod_galoisCharacter_one_sub`
- **Visibility** private · **Lines** 333–347 · **Notes** —

### `def charEval`
- **Type**: `{G} [CommGroup G] [Finite G] (σ : G) : (G →* ℂˣ) →* ℂˣ`
- **What**: The evaluation homomorphism `Ĝ → ℂˣ`, `χ ↦ χ σ`, for a finite commutative group.
- **How**: Defined as `(CommGroup.monoidHomMonoidHomEquiv G ℂ).symm σ` (the double-dual identification).
- **Hypotheses**: `G` finite commutative.
- **Uses from project**: []
- **Used by**: `charEval_apply`, `charEval_ker_card`, `prod_galoisCharacter_one_sub`
- **Visibility** private (noncomputable) · **Lines** 351–352 · **Notes** —

### `theorem charEval_apply`
- **Type**: `… (σ) (φ) : charEval σ φ = φ σ`
- **What**: `charEval σ` evaluates a character at `σ`.
- **How**: Unfolds via `monoidHomMonoidHomEquiv_symm_apply_apply`.
- **Hypotheses**: `G` finite commutative.
- **Uses from project**: `charEval`
- **Used by**: `charEval_ker_card`, `prod_galoisCharacter_one_sub`
- **Visibility** private · **Lines** 354–355 · **Notes** —

### `theorem charEval_ker_card`
- **Type**: `… (σ) : Nat.card (charEval σ).ker = Nat.card G / orderOf σ`
- **What**: The kernel of `χ ↦ χ σ` has order `|G| / orderOf σ`.
- **How**: Identifies `(charEval σ).ker` with `(restrictHom (zpowers σ)).ker`, then `CommGroup.card_restrictHom_ker` + Lagrange (`card_eq_card_quotient_mul_card_subgroup`) + `Nat.card_zpowers`.
- **Hypotheses**: `G` finite commutative.
- **Uses from project**: `charEval`, `charEval_apply`
- **Used by**: `prod_galoisCharacter_one_sub`
- **Visibility** private · **Lines** 359–373 · **Notes** —

### `theorem prod_galoisCharacter_one_sub`
- **Type**: `{G} [CommGroup G] [Finite G] [Fintype (G →* ℂˣ)] (σ) (Y) : ∏_{χ : G→*ℂˣ} (1 - (χσ)·Y) = (1 - Y^{orderOf σ})^{|G|/orderOf σ}`
- **What**: The character-product identity at the heart of Sharifi 7.1.16.
- **How**: The evaluation map `χ ↦ χσ` surjects `Ĝ` onto `μ_f` (`f = orderOf σ`) with uniform fibres of size `|G|/f` (`MonoidHom.card_fiber_eq_of_mem_range`, `charEval_ker_card`, `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`); `Finset.prod_fiberwise_of_maps_to'` collapses via `prod_one_sub_nthRoots`. (&gt;30-line proof.)
- **Hypotheses**: `G` finite commutative with enough roots of unity (here `ℂ`).
- **Uses from project**: `charEval`, `charEval_apply`, `charEval_ker_card`, `prod_one_sub_nthRoots`
- **Used by**: `dedekindZeta_local_factor_eq_product_artin_local`
- **Visibility** private (`open Finset`) · **Lines** 382–442 · **Notes** &gt;30-line proof

### `theorem cpow_neg_absNorm_eq_pow`
- **Type**: `{a b : ℕ} (f : ℕ) (s : ℂ) (h : b = a^f) : (b:ℂ)^(-s) = ((a:ℂ)^(-s))^f`
- **What**: If `N𝔓 = N𝔭^f` then `(N𝔓)^{-s} = ((N𝔭)^{-s})^f` over `ℂ`.
- **How**: Reduces to `Complex.cpow_mul` / `cpow_nat_mul`; the branch condition holds because the base is a nonnegative real (`log_im = 0`).
- **Hypotheses**: `b = a^f`.
- **Uses from project**: []
- **Used by**: `dedekindZeta_local_factor_eq_product_artin_local`
- **Visibility** private · **Lines** 447–454 · **Notes** —

### `theorem dedekindZeta_local_factor_eq_product_artin_local`
- **Type**: `… [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (𝔭) [𝔭.IsPrime] (_hunr : UnramifiedIn K L 𝔭) (s) (_hs : 1 &lt; s.re) : ∏'_{𝔓|𝔭} (1 - N𝔓^{-s})⁻¹ = ∏'_χ (1 - χ(Frob 𝔭)·N𝔭^{-s})⁻¹`
- **What**: Sharifi 7.1.16 local step — the local Euler factor of `ζ_L` at an unramified prime factors as a product over characters.
- **How**: RHS evaluates to `((1-Y^f)^g)⁻¹` via `prod_galoisCharacter_one_sub` (`f = orderOf Frob`, `g = |G|/f`); LHS has `g` equal factors since each `N𝔓 = N𝔭^f` (`absNorm_eq_pow_inertiaDeg_of_liesOver`, `inertiaDeg = f` via `finrank_residue_eq_orderOf`), counted by `card_primesAbove_mul_orderOf_eq`. (&gt;30-line proof.)
- **Hypotheses**: `𝔭` an unramified prime; `Re s &gt; 1`.
- **Uses from project**: `UnramifiedIn`, `frobeniusClass`, `prod_galoisCharacter_one_sub`, `cpow_neg_absNorm_eq_pow`, `card_primesAbove_mul_orderOf_eq`, `finrank_residue_eq_orderOf`, `UnramifiedIn.ne_bot`
- **Used by**: `tprod_unramified_eq_prod_artinDirichletSeries`
- **Visibility** public · **Lines** 460–518 · **Notes** &gt;30-line proof; `open scoped IsMulCommutative`

### `def frobeniusIdeal`
- **Type**: `(K L …) [IsMulCommutative Gal(L/K)] (𝔞 : Ideal (𝓞 K)) : Gal(L/K)`
- **What**: The `Gal(L/K)`-valued completely-multiplicative ideal Frobenius (abelian, so a genuine group element).
- **How**: `Multiset.prod` of `(frobeniusClass K L 𝔭).out` over `normalizedFactors 𝔞` (with the `CommGroup` instance from `mul_comm'`).
- **Hypotheses**: `Gal(L/K)` abelian.
- **Uses from project**: `frobeniusClass`
- **Used by**: `frobeniusIdeal_apply_prime`, `_mul`, `_one`, `galoisCharacterOnIdeal_eq_char_frobeniusIdeal`, and ~20 leaf-G lemmas
- **Visibility** public (noncomputable, `open Classical`) · **Lines** 580–585 · **Notes** —

### `theorem frobeniusIdeal_apply_prime`
- **Type**: `… (𝔭) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) : frobeniusIdeal K L 𝔭 = (frobeniusClass K L 𝔭).out`
- **What**: On a nonzero prime, the ideal Frobenius is the chosen Frobenius representative.
- **How**: `normalizedFactors` of a prime is `{𝔭}`, so the product collapses.
- **Hypotheses**: `𝔭` a nonzero prime.
- **Uses from project**: `frobeniusIdeal`, `frobeniusClass`
- **Used by**: `autToPow_frobeniusIdeal`, `autToPow_range_le_realizedResidues`
- **Visibility** public (`open Classical`) · **Lines** 589–596 · **Notes** —

### `theorem frobeniusIdeal_mul`
- **Type**: `… (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥) : frobeniusIdeal K L (𝔞*𝔟) = frobeniusIdeal K L 𝔞 * frobeniusIdeal K L 𝔟`
- **What**: The ideal Frobenius is completely multiplicative on nonzero ideals.
- **How**: `normalizedFactors_mul` + `Multiset.map_add` + `Multiset.prod_add`.
- **Hypotheses**: both ideals nonzero.
- **Uses from project**: `frobeniusIdeal`
- **Used by**: `autToPow_frobeniusIdeal`, `card_fibre_eq_card_good_fibre`
- **Visibility** public · **Lines** 599–605 · **Notes** —

### `theorem frobeniusIdeal_one`
- **Type**: `… : frobeniusIdeal K L ⊤ = 1`
- **What**: The ideal Frobenius of the unit ideal is `1`.
- **How**: `normalizedFactors_one = 0`, empty product.
- **Hypotheses**: none.
- **Uses from project**: `frobeniusIdeal`
- **Used by**: `autToPow_frobeniusIdeal`, `card_fibre_bound_eq_one`
- **Visibility** public · **Lines** 608–614 · **Notes** —

### `theorem galoisCharacterOnIdeal_eq_char_frobeniusIdeal`
- **Type**: `… [IsCyclotomicExtension {m} K L] (χ) {𝔞} (hU : ∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) : galoisCharacterOnIdeal K L χ 𝔞 = χ(frobeniusIdeal K L 𝔞)`
- **What**: Helper 1 — on unramified-supported `𝔞` the ideal character equals `χ` of the ideal Frobenius.
- **How**: Both sides are the `Multiset`-product of `χ((Frob 𝔭).out)` over the factors (`galoisCharacterOnIdeal_eq_map_prod` resp. `frobeniusIdeal` + `map_multiset_prod`), matched termwise by `Multiset.map_congr` + `if_pos (hU …)`.
- **Hypotheses**: `L = K(μ_m)` cyclotomic; every prime factor of `𝔞` unramified.
- **Uses from project**: `galoisCharacterOnIdeal`, `frobeniusIdeal`, `galoisCharacterOnIdeal_eq_map_prod`, `frobeniusClass`, `UnramifiedIn`
- **Used by**: `card_valueFibre_…`, `galoisCharacterOnIdeal_mem_insert_zero_nthRootsFinset`
- **Visibility** public (`open Classical`) · **Lines** 632–651 · **Notes** —

### `theorem card_valueFibre_eq_card_unramifiedSupported_frobeniusValueFibre`
- **Type**: `… (χ) (ζ : ℂ) (hζ : ζ ≠ 0) (N) : Nat.card {𝔞 ≠ ⊥, N𝔞 ≤ N, χ(𝔞)=ζ} = Nat.card {𝔞 ≠ ⊥, N𝔞 ≤ N, U 𝔞, χ(Frob 𝔞)=ζ}`
- **What**: Helper 1a — for `ζ ≠ 0`, the value-fibre and the unramified-supported Frobenius-value-fibre are the same set.
- **How**: Predicate `↔`: forward, `χ(𝔞)=ζ≠0` forces no factor ramified (`Multiset.prod_eq_zero`), so `U 𝔞` holds and Helper 1 applies; backward, `U 𝔞` ⟹ Helper 1. `Equiv.subtypeEquivRight`.
- **Hypotheses**: cyclotomic; `ζ ≠ 0`.
- **Uses from project**: `galoisCharacterOnIdeal`, `galoisCharacterOnIdeal_eq_map_prod`, `galoisCharacterOnIdeal_eq_char_frobeniusIdeal`, `frobeniusIdeal`, `frobeniusClass`, `UnramifiedIn`
- **Used by**: `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow`
- **Visibility** public (`open Classical`) · **Lines** 672–703 · **Notes** —

### `theorem charFibre_mem_range`
- **Type**: `… [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (χ) (ζ : ℂˣ) (hζ : ζ^{orderOf χ}=1) : ∃ g, χ g = ζ`
- **What**: The image of a character of a finite abelian group is exactly `μ_{orderOf χ}`; so every `ζ` with `ζ^{orderOf χ}=1` is hit.
- **How**: `range χ` is finite hence cyclic, of order `orderOf χ` (`IsCyclic.exponent_eq_card`, `orderOf χ = exponent (range χ)`), contained in `rootsOfUnity (orderOf χ) ℂ` of the same cardinality (`Complex.card_rootsOfUnity`); equal cardinality forces equality (`Subgroup.eq_of_le_of_card_ge`). (&gt;30-line proof.)
- **Hypotheses**: `Gal(L/K)` finite abelian.
- **Uses from project**: []
- **Used by**: `card_charFibre_eq_card_ker`
- **Visibility** public · **Lines** 712–745 · **Notes** &gt;30-line proof

### `theorem card_charFibre_eq_card_ker`
- **Type**: `… (χ) (ζ : ℂˣ) (hζ : ζ^{orderOf χ}=1) : Nat.card {g // χ g = ζ} = Nat.card (MonoidHom.ker χ)`
- **What**: Helper 1b — the character fibre `{g : χ g = ζ}` has constant cardinality `|ker χ|` over roots of unity.
- **How**: `ζ ∈ range χ` (`charFibre_mem_range`) gives `g₀`; the fibre is the coset `(ker χ)·g₀`, bijective to `ker χ` via `k ↦ k·g₀` (`Equiv.ofBijective`).
- **Hypotheses**: finite abelian; `ζ^{orderOf χ}=1`.
- **Uses from project**: `charFibre_mem_range`
- **Used by**: `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow`
- **Visibility** public · **Lines** 755–776 · **Notes** —

### `theorem normLeOne_frontier_lipschitz`
- **Type**: `(K) [Field K] [NumberField K] : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (card (InfinitePlace K) - 1) → ℝ) → realSpace K), (∀ j, LipschitzWith M (φ j)) ∧ frontier (normAtAllPlaces '' normLeOne K) ⊆ ⋃ j, φ j '' Icc 0 1`
- **What**: Sub-gap 2 — the frontier of the norm-`≤1` cone slice is covered by finitely many Lipschitz images of the unit cube `[0,1]^{d-1}`.
- **How**: Direct application of the external `normLeOne_frontier_lipschitz_cover K`.
- **Hypotheses**: `K` a number field.
- **Uses from project**: `normLeOne_frontier_lipschitz_cover` (ForMathlib/NormLeOneLipschitz.lean)
- **Used by**: unused in file (it is the `hlip` interface the LatticePointCount machinery consumes upstream; surfaced here as the named deep gap)
- **Visibility** public (`open scoped NNReal`) · **Lines** 802–808 · **Notes** —

### `theorem unramifiedIn_of_coprime_absNorm`
- **Type**: `… [IsCyclotomicExtension {m} K L] (𝔭) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) (hcop : (N𝔭).Coprime m) : UnramifiedIn K L 𝔭`
- **What**: A nonzero prime of `𝓞 K` whose norm is coprime to `m` is unramified in `L = K(μ_m)`.
- **How**: A ramified prime divides the different, which divides `(aeval ζ (minpoly).derivative)` (`conductor_mul_differentIdeal`); since `minpoly ∣ X^m−1`, differentiating gives `m ∈ 𝔓`, so `(m) ≤ 𝔭` and `N𝔭 ∣ m^d` — contradicting coprimality. (&gt;30-line proof; uses `not_dvd_differentIdeal_iff`, `conductor_mul_differentIdeal`.)
- **Hypotheses**: cyclotomic; `N𝔭` coprime to `m`.
- **Uses from project**: `UnramifiedIn`
- **Used by**: `autToPow_frobeniusIdeal`, `card_fibre_eq_card_good_fibre`
- **Visibility** private · **Lines** 831–895 · **Notes** &gt;30-line proof

### `theorem autToPow_frobeniusIdeal`
- **Type**: `… (hζ : IsPrimitiveRoot ζ m) (𝔠) (h𝔠 : 𝔠 ≠ ⊥) (hcop : (N𝔠).Coprime m) : hζ.autToPow K (frobeniusIdeal K L 𝔠) = ZMod.unitOfCoprime (N𝔠) hcop`
- **What**: The cyclotomic character sends the ideal Frobenius of a coprime-norm ideal to its norm residue `N𝔠 mod m`.
- **How**: Multiplicative induction (`UniqueFactorizationMonoid.induction_on_prime`) reducing to the per-prime `autToPow_frobeniusClass_out` (external CNR), with `frobeniusIdeal_mul`/`_one`. (&gt;30-line proof.)
- **Hypotheses**: cyclotomic; `N𝔠` coprime to `m`.
- **Uses from project**: `frobeniusIdeal`, `frobeniusIdeal_mul`, `frobeniusIdeal_apply_prime`, `frobeniusIdeal_one`, `autToPow_frobeniusClass_out`, `unramifiedIn_of_coprime_absNorm`
- **Used by**: `card_good_fibre_eq_card_residue`
- **Visibility** private · **Lines** 900–932 · **Notes** &gt;30-line proof

### `theorem card_good_fibre_eq_card_residue`
- **Type**: `… (hζ) (h : Gal(L/K)) (X) : Nat.card {𝔠 ≠ ⊥, N𝔠 ≤ X, (N𝔠).Coprime m, frobeniusIdeal=h} = Nat.card {I : (Ideal (𝓞 K))⁰, N I ≤ X, (N I mod m) = (autToPow K h : ZMod m)}`
- **What**: The good-fibre count equals a norm-residue count: coprime-norm ideals with `Frob = h` ↔ ideals with the residue `autToPow K h`.
- **How**: `Nat.card_congr` of an explicit bijection; coprimality/unramifiedness come free from the residue being a unit, the Frobenius condition is the residue condition by injectivity (`autToPow_injective`) of the cyclotomic character + `autToPow_frobeniusIdeal`. (&gt;30-line proof.)
- **Hypotheses**: cyclotomic.
- **Uses from project**: `frobeniusIdeal`, `autToPow_frobeniusIdeal`
- **Used by**: `card_L2_eq_sum_residue`
- **Visibility** private (`open nonZeroDivisors`) · **Lines** 940–969 · **Notes** &gt;30-line proof

### `def badPart`
- **Type**: `(K) [Field K] [NumberField K] (m : ℕ) (𝔞 : Ideal (𝓞 K)) : Ideal (𝓞 K)`
- **What**: The bad part of `𝔞` at level `m`: product of prime factors whose norm is not coprime to `m`.
- **How**: `Multiset.prod` of the filtered (`¬ Coprime`) sub-multiset of `normalizedFactors 𝔞`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `goodPart_mul_badPart`, `badPart_ne_bot`, `mem_factors_badPart`, `badPart_mul_eq`, `card_fibre_eq_card_good_fibre`, `card_L2_eq_sum_fibres`
- **Visibility** private (noncomputable) · **Lines** 974–977 · **Notes** —

### `def goodPart`
- **Type**: `(K) … (m) (𝔞) : Ideal (𝓞 K)`
- **What**: The good part: product of prime factors whose norm is coprime to `m`.
- **How**: `Multiset.prod` of the filtered (`Coprime`) sub-multiset of `normalizedFactors 𝔞`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `goodPart_mul_badPart`, `goodPart_ne_bot`, `absNorm_goodPart_coprime`, `goodPart_mul_eq`, `card_fibre_eq_card_good_fibre`
- **Visibility** private (noncomputable) · **Lines** 980–983 · **Notes** —

### `theorem goodPart_mul_badPart`
- **Type**: `(K) (m) (𝔞) (h𝔞 : 𝔞 ≠ ⊥) : goodPart K m 𝔞 * badPart K m 𝔞 = 𝔞`
- **What**: Good · bad reconstructs the ideal.
- **How**: `Multiset.filter_add_not` recombines the two filtered multisets; `Ideal.prod_normalizedFactors_eq_self`.
- **Hypotheses**: `𝔞 ≠ ⊥`.
- **Uses from project**: `goodPart`, `badPart`
- **Used by**: `card_fibre_eq_card_good_fibre`
- **Visibility** private · **Lines** 989–993 · **Notes** —

### `theorem badPart_ne_bot`
- **Type**: `(K) (m) (𝔞) : badPart K m 𝔞 ≠ ⊥`
- **What**: The bad part is nonzero.
- **How**: `Multiset.prod_ne_zero`: each filtered factor is a (nonzero) prime.
- **Hypotheses**: none.
- **Uses from project**: `badPart`
- **Used by**: `card_L2_eq_sum_fibres`
- **Visibility** private · **Lines** 995–999 · **Notes** —

### `theorem goodPart_ne_bot`
- **Type**: `(K) (m) (𝔞) : goodPart K m 𝔞 ≠ ⊥`
- **What**: The good part is nonzero.
- **How**: `Multiset.prod_ne_zero`: each filtered factor is a nonzero prime.
- **Hypotheses**: none.
- **Uses from project**: `goodPart`
- **Used by**: `card_fibre_eq_card_good_fibre`
- **Visibility** private · **Lines** 1001–1005 · **Notes** —

### `theorem absNorm_goodPart_coprime`
- **Type**: `(K) (m) (𝔞) : (Ideal.absNorm (goodPart K m 𝔞)).Coprime m`
- **What**: The norm of the good part is coprime to `m`.
- **How**: `map_multiset_prod` + `Multiset.prod_induction` on `Coprime`, each filtered factor coprime by construction.
- **Hypotheses**: none.
- **Uses from project**: `goodPart`
- **Used by**: `card_fibre_eq_card_good_fibre`
- **Visibility** private · **Lines** 1007–1014 · **Notes** —

### `theorem normalizedFactors_multiset_prod'`
- **Type**: `(K) {s : Multiset (Ideal (𝓞 K))} (hs : ∀ 𝔭 ∈ s, Prime 𝔭) : normalizedFactors s.prod = s`
- **What**: A multiset of prime ideals recovers itself as the normalized factors of its product.
- **How**: `normalizedFactors_multiset_prod` + each prime's `normalizedFactors` is `{𝔭}` (`normalize_eq`); `Multiset.sum_map_singleton`.
- **Hypotheses**: every element of `s` prime.
- **Uses from project**: []
- **Used by**: `mem_factors_badPart`
- **Visibility** private · **Lines** 1018–1028 · **Notes** —

### `theorem mem_factors_badPart`
- **Type**: `(K) (m) {𝔞 𝔭} (h𝔭 : 𝔭 ∈ normalizedFactors (badPart K m 𝔞)) : 𝔭 ∈ normalizedFactors 𝔞 ∧ ¬(N𝔭).Coprime m`
- **What**: A factor of the bad part is a factor of `𝔞` with non-coprime norm.
- **How**: `normalizedFactors_multiset_prod'` identifies the bad-part factors with the filtered multiset; `Multiset.mem_of_mem_filter` / `mem_filter`.
- **Hypotheses**: none.
- **Uses from project**: `badPart`, `normalizedFactors_multiset_prod'`
- **Used by**: `card_L2_eq_sum_fibres`
- **Visibility** private · **Lines** 1030–1037 · **Notes** —

### `theorem coprime_absNorm_of_mem_factors_of_coprime`
- **Type**: `(K) (m) {𝔠} (hcop : (N𝔠).Coprime m) {𝔮} (h𝔮 : 𝔮 ∈ normalizedFactors 𝔠) : (N𝔮).Coprime m`
- **What**: Every prime factor of a coprime-norm ideal has coprime norm.
- **How**: `N𝔮 ∣ N𝔠` (`absNorm_dvd_absNorm_of_le` from `dvd_of_mem_normalizedFactors`), then `Nat.Coprime.coprime_dvd_left`.
- **Hypotheses**: `N𝔠` coprime to `m`.
- **Uses from project**: []
- **Used by**: `card_fibre_eq_card_good_fibre`, `card_L2_eq_sum_residue` (via `card_fibre…`), `sum_rpow_badFinset_le` (indirectly)
- **Visibility** private · **Lines** 1041–1047 · **Notes** —

### `theorem goodPart_mul_eq`
- **Type**: `(K) (m) {𝔠 𝔟} (h𝔠) (h𝔟) (hc : all factors of 𝔠 coprime) (hb : all factors of 𝔟 non-coprime) : goodPart K m (𝔠*𝔟) = 𝔠`
- **What**: If `𝔠` is all-coprime and `𝔟` all-non-coprime, the good part of `𝔠·𝔟` is `𝔠`.
- **How**: `normalizedFactors_mul` + `Multiset.filter_add`; `filter_eq_self` on `𝔠`, `filter_eq_nil` on `𝔟`; `prod_normalizedFactors_eq_self`.
- **Hypotheses**: factor-coprimality split.
- **Uses from project**: `goodPart`
- **Used by**: `card_fibre_eq_card_good_fibre`
- **Visibility** private · **Lines** 1052–1059 · **Notes** —

### `theorem badPart_mul_eq`
- **Type**: `(K) (m) {𝔠 𝔟} (h𝔠) (h𝔟) (hc) (hb) : badPart K m (𝔠*𝔟) = 𝔟`
- **What**: Symmetrically, the bad part of `𝔠·𝔟` is `𝔟`.
- **How**: As `goodPart_mul_eq` with the filters swapped (`filter_eq_nil` on `𝔠`, `filter_eq_self` on `𝔟`).
- **Hypotheses**: factor-coprimality split.
- **Uses from project**: `badPart`
- **Used by**: `card_fibre_eq_card_good_fibre`
- **Visibility** private · **Lines** 1062–1070 · **Notes** —

### `theorem exists_prime_dvd_natCast_mem`
- **Type**: `(K) (𝔭) [𝔭.IsPrime] (n : ℕ) (hn1 : 1 &lt; n) (hmem : (n:𝓞 K) ∈ 𝔭) : ∃ r, r.Prime ∧ r ∣ n ∧ (r:𝓞 K) ∈ 𝔭`
- **What**: If `(n:𝓞 K) ∈ 𝔭` (prime) and `n &gt; 1`, some rational prime factor `r ∣ n` already casts into `𝔭`.
- **How**: Strong induction on `n`: factor `n = r·k`, the prime swallows `r` or `k`, recurse on `k &lt; n`.
- **Hypotheses**: `n &gt; 1`.
- **Uses from project**: []
- **Used by**: `exists_primeFactor_natCast_mem_of_not_coprime`
- **Visibility** private (`omit [NumberField K]`) · **Lines** 1089–1111 · **Notes** —

### `theorem exists_primeFactor_natCast_mem_of_not_coprime`
- **Type**: `(K) (m) [NeZero m] (𝔭) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) (hncop : ¬(N𝔭).Coprime m) : ∃ p ∈ m.primeFactors, (p:𝓞 K) ∈ 𝔭`
- **What**: A nonzero prime with non-coprime norm contains `(p:𝓞 K)` for some `p ∈ m.primeFactors`.
- **How**: `N𝔭` is a power of the single rational prime `r` below `𝔭` (`absNorm_dvd_absNorm_of_le`); a prime `p ∣ gcd(N𝔭,m)` divides `r^d` so `p = r ∣ m` (`exists_prime_dvd_natCast_mem`).
- **Hypotheses**: `𝔭` nonzero prime, norm not coprime to `m`.
- **Uses from project**: `exists_prime_dvd_natCast_mem`
- **Used by**: `finite_badPrimes`, `coprime_absNorm_of_unramified_of_finrank_eq_one`
- **Visibility** private · **Lines** 1116–1133 · **Notes** —

### `theorem finite_primes_natCast_mem`
- **Type**: `(K) (p : ℕ) (hp : p ≠ 0) : {𝔭 | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ (p:𝓞 K) ∈ 𝔭}.Finite`
- **What**: The nonzero primes containing a fixed nonzero integer cast form a finite set.
- **How**: They are the prime divisors of `(p)`; `Ideal.finite_factors` gives finiteness, transported by `Set.Finite.ofFinset`.
- **Hypotheses**: `p ≠ 0`.
- **Uses from project**: []
- **Used by**: `finite_badPrimes`
- **Visibility** private · **Lines** 1137–1152 · **Notes** —

### `theorem finite_badPrimes`
- **Type**: `(K) (m) [NeZero m] : {𝔭 | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬(N𝔭).Coprime m}.Finite`
- **What**: The bad-prime set (nonzero primes with norm not coprime to `m`) is finite.
- **How**: Covered by the finite union over `p ∈ m.primeFactors` of `finite_primes_natCast_mem` (via `exists_primeFactor_natCast_mem_of_not_coprime`).
- **Hypotheses**: `m ≠ 0`.
- **Uses from project**: `finite_primes_natCast_mem`, `exists_primeFactor_natCast_mem_of_not_coprime`
- **Used by**: `sum_rpow_badFinset_le`, `card_fibre_bound_two_le`
- **Visibility** private · **Lines** 1156–1166 · **Notes** —

### `theorem card_fibre_eq_card_good_fibre`
- **Type**: `… (g) (N) {𝔟} (h𝔟 : 𝔟 ≠ ⊥) (hbU : all factors of 𝔟 unramified) (hbn : all factors of 𝔟 non-coprime) : Nat.card {𝔞 : U 𝔞, Frob=g, badPart=𝔟, N𝔞≤N} = Nat.card {𝔠 coprime, Frob=g·Frob(𝔟)⁻¹, N𝔠 ≤ ⌊N/N𝔟⌋}`
- **What**: Per-bad-part fibre bijection — unramified-supported `𝔞` with `Frob 𝔞=g` and `badPart 𝔞=𝔟` ↔ coprime-norm `𝔠` with `Frob 𝔠 = g·(Frob 𝔟)⁻¹`, via `𝔞 ↦ goodPart 𝔞`.
- **How**: `Nat.card_congr` with explicit `𝔞 ↦ goodPart 𝔞` / `𝔠 ↦ 𝔠·𝔟`; norm bound via `N(goodPart)·N𝔟 = N𝔞` (`Nat.le_div_iff_mul_le`), Frobenius via multiplicativity + cancellation, split via `goodPart_mul_eq`/`badPart_mul_eq`. (&gt;30-line proof.)
- **Hypotheses**: cyclotomic; `𝔟` bad-supported.
- **Uses from project**: `badPart`, `goodPart`, `goodPart_ne_bot`, `goodPart_mul_badPart`, `absNorm_goodPart_coprime`, `frobeniusIdeal`, `frobeniusIdeal_mul`, `unramifiedIn_of_coprime_absNorm`, `coprime_absNorm_of_mem_factors_of_coprime`, `goodPart_mul_eq`, `badPart_mul_eq`, `UnramifiedIn`
- **Used by**: `card_L2_eq_sum_residue`
- **Visibility** private (`open UniqueFactorizationMonoid`) · **Lines** 1183–1251 · **Notes** &gt;30-line proof

### `def IsBadPart`
- **Type**: `(K L …) (m) (N : ℕ) (𝔟 : Ideal (𝓞 K)) : Prop := 𝔟 ≠ ⊥ ∧ (∀ 𝔭 ∈ normalizedFactors 𝔟, UnramifiedIn K L 𝔭 ∧ ¬(N𝔭).Coprime m) ∧ N𝔟 ≤ N`
- **What**: Predicate for "bad-supported ideals of norm `≤ N`": nonzero, every factor unramified with non-coprime norm, bounded norm.
- **How**: A conjunction of the three conditions.
- **Hypotheses**: cyclotomic context (in the `variable` line).
- **Uses from project**: `UnramifiedIn`
- **Used by**: `finite_isBadPart`, `card_L2_eq_sum_fibres`
- **Visibility** private (`open UniqueFactorizationMonoid`) · **Lines** 1260–1262 · **Notes** —

### `theorem finite_isBadPart`
- **Type**: `(K L …) (N) : {𝔟 | IsBadPart K L m N 𝔟}.Finite`
- **What**: The bad-supported ideals of norm `≤ N` form a finite set.
- **How**: Subset of the finitely many ideals of norm `≤ N` (`Ideal.finite_setOf_absNorm_le`).
- **Hypotheses**: none beyond context.
- **Uses from project**: `IsBadPart`
- **Used by**: `card_L2_eq_sum_fibres`, `card_L2_eq_sum_residue`, `badFinset_subset_of_le`, `sum_rpow_badFinset_le`, `card_fibre_bound_two_le`, `card_fibre_bound_eq_one`
- **Visibility** private (with many `omit`s) · **Lines** 1268–1269 · **Notes** —

### `instance finite_L2`
- **Type**: `(K L …) (g : Gal(L/K)) (N) : Finite {𝔞 ≠ ⊥, N𝔞 ≤ N, U 𝔞, frobeniusIdeal=g}`
- **What**: The L2 Frobenius-fibre subtype at `g` is finite.
- **How**: Injects into the finite `{I // N I ≤ N}` (`Ideal.finite_setOf_absNorm_le`).
- **Hypotheses**: none beyond context.
- **Uses from project**: `frobeniusIdeal`, `UnramifiedIn`
- **Used by**: implicitly by `Nat.card`/`Fintype` of the L2 fibres downstream
- **Visibility** private instance (`open UniqueFactorizationMonoid`) · **Lines** 1273–1280 · **Notes** —

### `theorem card_L2_eq_sum_fibres`
- **Type**: `… (g) (N) : Nat.card {𝔞 : U 𝔞, N𝔞≤N, Frob=g} = ∑_{𝔟 ∈ badFinset N} Nat.card {𝔞 : U 𝔞, N𝔞≤N, Frob=g, badPart 𝔞=𝔟}`
- **What**: The partition (Sharifi 7.2.2 step B) — the L2 count is the sum over the finite bad-part set of per-bad-part fibre counts.
- **How**: Fibration `𝔞 ↦ badPart 𝔞` (`Equiv.sigmaFiberEquiv` + `Nat.card_sigma`); membership `badPart 𝔞 ∈ B_N` via `badPart_ne_bot`/`mem_factors_badPart` and `N(badPart) ∣ N𝔞`. (&gt;30-line proof.)
- **Hypotheses**: none beyond context.
- **Uses from project**: `badPart`, `IsBadPart`, `finite_isBadPart`, `badPart_ne_bot`, `mem_factors_badPart`, `frobeniusIdeal`, `UnramifiedIn`
- **Used by**: `card_L2_eq_sum_residue`
- **Visibility** private (`omit …`, `open UniqueFactorizationMonoid`) · **Lines** 1288–1322 · **Notes** &gt;30-line proof

### `theorem card_L2_eq_sum_residue`
- **Type**: `… {ζ} (hζ : IsPrimitiveRoot ζ m) (g) (N) : Nat.card {𝔞 : U 𝔞, N𝔞≤N, Frob=g} = ∑_{𝔟 ∈ badFinset N} Nat.card {I : (Ideal (𝓞 K))⁰, N I ≤ ⌊N/N𝔟⌋, (N I mod m) = autToPow K (g·Frob(𝔟)⁻¹)}`
- **What**: The L2 count as a sum of norm-residue counts (over the finite bad-part set, at residue `autToPow(g·Frob𝔟⁻¹)`).
- **How**: Chains `card_L2_eq_sum_fibres` → `card_fibre_eq_card_good_fibre` → `card_good_fibre_eq_card_residue`.
- **Hypotheses**: cyclotomic; `ζ` a primitive `m`-th root.
- **Uses from project**: `card_L2_eq_sum_fibres`, `card_fibre_eq_card_good_fibre`, `card_good_fibre_eq_card_residue`, `finite_isBadPart`, `frobeniusIdeal`, `UnramifiedIn`
- **Used by**: `card_fibre_bound_two_le`, `card_fibre_bound_eq_one`
- **Visibility** private (`open UniqueFactorizationMonoid nonZeroDivisors`) · **Lines** 1330–1344 · **Notes** —

### `def realizedResidues`
- **Type**: `(K) [Field K] [NumberField K] (m) [NeZero m] : Subgroup (ZMod m)ˣ`
- **What**: The subgroup of residues `a ∈ (ℤ/m)ˣ` that arise as the norm residue `N𝔟 mod m` of some nonzero ideal.
- **How**: Carrier `{a : ∃ 𝔟 ∈ (Ideal (𝓞 K))⁰, N𝔟 ≡ a}`; `one_mem` via `⊤` (`N⊤=1`), `mul_mem` via ideal products, `inv_mem` via the finite-order power `𝔟^{ord a − 1}`.
- **Hypotheses**: `m ≠ 0`.
- **Uses from project**: []
- **Used by**: `autToPow_range_le_realizedResidues`
- **Visibility** private (noncomputable, `open nonZeroDivisors`) · **Lines** 1368–1384 · **Notes** —

### `theorem autToPow_range_le_realizedResidues`
- **Type**: `… (hζ : IsPrimitiveRoot ζ m) : (hζ.autToPow K).range ≤ realizedResidues K m`
- **What**: Every cyclotomic-character value is a realized norm residue.
- **How**: Sets `H = comap autToPow (realizedResidues)`; every coprime-norm unramified prime's Frobenius lies in `H` (`autToPow_frobeniusClass_out`, prime as realizer), so `subgroup_eq_top_of_forall_frobenius_mem_of_coprime` forces `H = ⊤`.
- **Hypotheses**: cyclotomic.
- **Uses from project**: `realizedResidues`, `frobeniusIdeal_apply_prime` (via `frobeniusClass`), `subgroup_eq_top_of_forall_frobenius_mem_of_coprime`, `autToPow_frobeniusClass_out`, `frobeniusClass`
- **Used by**: `realizes_autToPow_range`
- **Visibility** private (`open nonZeroDivisors`) · **Lines** 1394–1413 · **Notes** —

### `theorem realizes_autToPow_range`
- **Type**: `… (hζ) : ∀ a ∈ (hζ.autToPow K).range, ∃ 𝔟 : (Ideal (𝓞 K))⁰, (N𝔟 : ZMod m) = (a : ZMod m)`
- **What**: The realizer hypothesis `hS` for `S = range autToPow` in the shape consumed by the ICC producer.
- **How**: Directly unfolds `autToPow_range_le_realizedResidues`.
- **Hypotheses**: cyclotomic.
- **Uses from project**: `autToPow_range_le_realizedResidues`, `realizedResidues`
- **Used by**: `exists_kappa_uniform`
- **Visibility** private (`open nonZeroDivisors`) · **Lines** 1419–1426 · **Notes** —

### `theorem pow_count_dvd_prod`
- **Type**: `{α} [CommMonoid α] [DecidableEq α] (a : α) (s : Multiset α) : a^{s.count a} ∣ s.prod`
- **What**: `a^{count a s}` divides `s.prod`.
- **How**: `Multiset.replicate (count a s) a ≤ s`, then `Multiset.prod_dvd_prod_of_le` + `prod_replicate`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `sum_rpow_le_euler_prod`
- **Visibility** private · **Lines** 1439–1447 · **Notes** —

### `theorem sum_rpow_le_euler_prod`
- **Type**: `(K) (P : Finset (Ideal (𝓞 K))) (hPprime) (N) (BF : Finset) (hBF : each 𝔟 nonzero, P-supported, N𝔟≤N) (e : ℝ) (hxlt : ∀ 𝔭 ∈ P, (N𝔭)^e &lt; 1) : ∑_{𝔟∈BF} (N𝔟)^e ≤ ∏_{𝔭∈P} (1 - (N𝔭)^e)⁻¹`
- **What**: The bad-part Euler bound — a negative-exponent norm-sum over `P`-supported ideals is dominated by the geometric Euler product over `P`.
- **How**: Each `𝔟 = ∏_{𝔭∈P} 𝔭^{count}`, so `(N𝔟)^e = ∏ ((N𝔭)^e)^{count}`; the count map injects into bounded exponent vectors (`count ≤ ⌊log₂ N⌋` via `pow_count_dvd_prod`, `N𝔭 ≥ 2`), and `Finset.prod_sum` + geometric partial sum `geom_sum_mul` bound it. (&gt;30-line proof.)
- **Hypotheses**: `P` finite set of nonzero primes; each `(N𝔭)^e &lt; 1`.
- **Uses from project**: `pow_count_dvd_prod`
- **Used by**: `sum_rpow_badFinset_le`
- **Visibility** private · **Lines** 1461–1562 · **Notes** `set_option maxHeartbeats 1600000`; &gt;30-line proof

### `theorem badFinset_subset_of_le`
- **Type**: `(K L …) {N M} (hNM : N ≤ M) : (finite_isBadPart K L m N).toFinset ⊆ (finite_isBadPart K L m M).toFinset`
- **What**: The bad-part finset grows monotonically in the norm bound.
- **How**: Membership transfers since only the `N𝔟 ≤ N` field changes (`le_trans`).
- **Hypotheses**: `N ≤ M`.
- **Uses from project**: `finite_isBadPart`
- **Used by**: `card_fibre_bound_two_le`
- **Visibility** private (`omit …`, `open UniqueFactorizationMonoid`) · **Lines** 1572–1576 · **Notes** —

### `theorem sum_rpow_badFinset_le`
- **Type**: `(K L …) (N) (e : ℝ) (hxlt : ∀ 𝔭 ∈ badPrimes, (N𝔭)^e &lt; 1) : ∑_{𝔟 ∈ badFinset N} (N𝔟)^e ≤ ∏_{𝔭 ∈ badPrimes} (1 - (N𝔭)^e)⁻¹`
- **What**: The Euler bound specialised to `BF = badFinset N`, `P = badPrimes`, uniform in `N`.
- **How**: Applies `sum_rpow_le_euler_prod` with `P = (finite_badPrimes).toFinset`; bad-supported factors are bad primes by construction.
- **Hypotheses**: each `(N𝔭)^e &lt; 1` on the bad primes.
- **Uses from project**: `sum_rpow_le_euler_prod`, `finite_badPrimes`, `finite_isBadPart`
- **Used by**: `card_fibre_bound_two_le`
- **Visibility** private (`omit …`, `open UniqueFactorizationMonoid`) · **Lines** 1584–1595 · **Notes** —

### `theorem exists_kappa_uniform`
- **Type**: `(K L …) {ζ} (hζ : IsPrimitiveRoot ζ m) : ∃ κ₀ C₀, ∀ a ∈ (autToPow K).range, ∀ N ≥ 1, |Nat.card {I : (Ideal (𝓞 K))⁰, N I ≤ N, N I ≡ a} − κ₀·N| ≤ C₀·N^{1−1/d}`
- **What**: The `g`-uniform per-residue ideal count — one `(κ₀,C₀)` governs every residue in `range autToPow`.
- **How**: Applies the external ICC κ-uniform count `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`, feeding its Fourier-decay hypothesis via the ICC producer `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized` + the realizer `realizes_autToPow_range`.
- **Hypotheses**: cyclotomic.
- **Uses from project**: `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`, `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`, `realizes_autToPow_range`
- **Used by**: `card_fibre_bound_two_le`, `card_fibre_bound_eq_one`
- **Visibility** private (`open nonZeroDivisors`) · **Lines** 1606–1614 · **Notes** —

### `theorem card_fibre_bound_two_le`
- **Type**: `(K L …) {ζ} (hζ) (hd : 2 ≤ finrank ℚ K) : ∃ κ C', ∀ g, ∀ N ≥ 1, |Nat.card {𝔞 : U 𝔞, N𝔞≤N, Frob=g} − κ·N| ≤ C'·N^{1−1/d}`
- **What**: The L2 fibre bound, `d ≥ 2` branch (bad-part Euler tail converges), with `κ` independent of `g`.
- **How**: Writes the count as the bad-part residue sum (`card_L2_eq_sum_residue`); a triangle inequality splits it into per-bad-part effective errors (via `exists_kappa_uniform`), floor-rounding slack, and the bad-part tail `T − T_N ≤ N^{−1/d}·E₂` (from `sum_rpow_badFinset_le` at exponents `−1` and `1/d−1`); `κ = κ₀·T`. (Very long ~280-line proof.)
- **Hypotheses**: cyclotomic; `finrank ℚ K ≥ 2`.
- **Uses from project**: `finite_badPrimes`, `finite_isBadPart`, `exists_kappa_uniform`, `sum_rpow_badFinset_le`, `badFinset_subset_of_le`, `card_L2_eq_sum_residue`, `frobeniusIdeal`, `UnramifiedIn`
- **Used by**: `exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le`
- **Visibility** private (`open UniqueFactorizationMonoid nonZeroDivisors`) · **Lines** 1632–1908 · **Notes** &gt;30-line proof (≈277 lines)

### `theorem associated_natCast_sub_one_pow`
- **Type**: `{A} [CommRing A] [IsDomain A] {p k} [Fact p.Prime] {ζ'} (hζ' : IsPrimitiveRoot ζ' (p^{k+1})) : Associated (p:A) ((ζ'−1)^{p^k(p−1)})`
- **What**: Cyclotomic Eisenstein identity (element level): `p` is associated to `(ζ'−1)^{φ(p^{k+1})}`.
- **How**: Evaluates `cyclotomic (p^{k+1}) = ∏ (X−μ)` at `1` giving `p = ∏(1−μ)`; each `1−μ` is associated to `ζ'−1` (`associated_sub_one_pow_sub_one_of_coprime`); `Finset.prod_const` + totient count.
- **Hypotheses**: `ζ'` a primitive `p^{k+1}`-th root in a domain.
- **Uses from project**: []
- **Used by**: `coprime_absNorm_of_unramified_of_finrank_eq_one`
- **Visibility** private (`open Polynomial Finset`) · **Lines** 1925–1947 · **Notes** —

### `theorem two_le_pow_mul_pred`
- **Type**: `{p k} (hp : p.Prime) (hbad : ¬(p=2 ∧ k=0)) : 2 ≤ p^k(p−1)`
- **What**: Totient lower bound away from the degenerate case `(p,k)=(2,0)`.
- **How**: Case split on `p = 2` (then `k ≥ 1`) vs `p ≥ 3`; monotonicity of `Nat.pow`/`mul`.
- **Hypotheses**: `p` prime, not `(2,0)`.
- **Uses from project**: []
- **Used by**: `coprime_absNorm_of_unramified_of_finrank_eq_one`
- **Visibility** private · **Lines** 1950–1958 · **Notes** —

### `theorem factorization_two_ne_one_of_mod_four`
- **Type**: `{m} (hm0 : m ≠ 0) (hm : m%4 ≠ 2) : m.factorization 2 ≠ 1`
- **What**: The degenerate case `2 ∥ m` is exactly `m ≡ 2 mod 4`, ruled out by `hm`.
- **How**: If `factorization 2 = 1` then `2 ∣ m` but `¬ 4 ∣ m` (`pow_dvd_iff_le_factorization`), so `m % 4 = 2` by `omega`.
- **Hypotheses**: `m ≠ 0`, `m % 4 ≠ 2`.
- **Uses from project**: []
- **Used by**: `coprime_absNorm_of_unramified_of_finrank_eq_one`
- **Visibility** private · **Lines** 1962–1975 · **Notes** —

### `theorem span_singleton_natCast_eq_of_finrank_eq_one`
- **Type**: `(K) (hd1 : finrank ℚ K = 1) (p) (hp : p.Prime) (𝔭) [𝔭.IsPrime] (hmem : (p:𝓞 K) ∈ 𝔭) : Ideal.span {(p:𝓞 K)} = 𝔭`
- **What**: At `[K:ℚ]=1`, a rational prime contained in a prime `𝔭` spans `𝔭`.
- **How**: `N((p)) = p^{[K:ℚ]} = p`; since `𝔭 ∣ (p)` with `N𝔭 &gt; 1`, the cofactor has norm 1 (`absNorm_eq_one_iff`), so `(p) = 𝔭`.
- **Hypotheses**: `finrank ℚ K = 1`; `p` prime in `𝔭`.
- **Uses from project**: []
- **Used by**: `coprime_absNorm_of_unramified_of_finrank_eq_one`
- **Visibility** private · **Lines** 1979–1996 · **Notes** —

### `theorem coprime_absNorm_of_unramified_of_finrank_eq_one`
- **Type**: `(K L …) (hd1 : finrank ℚ K = 1) (𝔭) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) (hunr : UnramifiedIn K L 𝔭) (hm : m%4 ≠ 2) : (N𝔭).Coprime m`
- **What**: At `[K:ℚ]=1`, an unramified prime cannot have norm sharing a factor with `m` (bad primes are empty when `K = ℚ`).
- **How**: K-internally via the different: extract `p ∣ m` with `(p:𝓞 K) ∈ 𝔭`; the Eisenstein identity `(p) = (ζ'−1)^{φ(p^v)}` (`associated_natCast_sub_one_pow`, `φ ≥ 2` by `two_le_pow_mul_pred`) gives `𝔓² ∣ (𝔭)·𝓞 L`, so `𝔓 ∣ differentIdeal` (`pow_sub_one_dvd_differentIdeal`) — contradicting unramifiedness. (&gt;30-line proof.)
- **Hypotheses**: `finrank ℚ K = 1`; `𝔭` unramified; `m % 4 ≠ 2`.
- **Uses from project**: `UnramifiedIn`, `exists_primeFactor_natCast_mem_of_not_coprime`, `factorization_two_ne_one_of_mod_four`, `associated_natCast_sub_one_pow`, `two_le_pow_mul_pred`, `span_singleton_natCast_eq_of_finrank_eq_one`
- **Used by**: `card_fibre_bound_eq_one`
- **Visibility** private (`omit …`) · **Lines** 2014–2082 · **Notes** &gt;30-line proof; the single sanctioned cyclotomic-ramification gap-style fact (here proven)

### `theorem card_fibre_bound_eq_one`
- **Type**: `(K L …) {ζ} (hζ) (hd1 : finrank ℚ K = 1) (hm : m%4 ≠ 2) : ∃ κ C', ∀ g, ∀ N ≥ 1, |Nat.card {𝔞 : U 𝔞, N𝔞≤N, Frob=g} − κ·N| ≤ C'·N^{1−1/d}`
- **What**: The L2 fibre bound, `d = 1` branch — bad set is `{⊤}`, count is one good-fibre residue count.
- **How**: Shows `badFinset N = {⊤}` (no bad primes by `coprime_absNorm_of_unramified_of_finrank_eq_one`), so `card_L2_eq_sum_residue` collapses to `RC(autToPow g, N)`, bounded by `exists_kappa_uniform` with `κ=κ₀`, `C'=C₀`. (&gt;30-line proof.)
- **Hypotheses**: cyclotomic; `finrank ℚ K = 1`; `m % 4 ≠ 2`.
- **Uses from project**: `exists_kappa_uniform`, `finite_isBadPart`, `coprime_absNorm_of_unramified_of_finrank_eq_one`, `card_L2_eq_sum_residue`, `frobeniusIdeal_one`, `frobeniusIdeal`, `UnramifiedIn`
- **Used by**: `exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le`
- **Visibility** private (`open UniqueFactorizationMonoid nonZeroDivisors`) · **Lines** 2089–2129 · **Notes** &gt;30-line proof

### `theorem exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le`
- **Type**: `(K L …) [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m) [NeZero m] [IsCyclotomicExtension {m} K L] (hm : m%4 ≠ 2) : ∃ κ C', ∀ g, ∀ N ≥ 1, |Nat.card {𝔞 : 𝔞≠⊥, N𝔞≤N, U 𝔞, Frob=g} − κ·N| ≤ C'·N^{1−1/d}`
- **What**: L2 (Sub-gaps 2+3) — unramified-supported Frobenius-fibre equidistribution with leading density `κ` independent of `g`.
- **How**: Dispatches on `finrank ℚ K`: `= 1` via `card_fibre_bound_eq_one`, `≥ 2` via `card_fibre_bound_two_le` (after extracting a primitive `m`-th root).
- **Hypotheses**: `L = K(μ_m)` cyclotomic; `m % 4 ≠ 2`.
- **Uses from project**: `frobeniusIdeal`, `card_fibre_bound_eq_one`, `card_fibre_bound_two_le`, `UnramifiedIn`
- **Used by**: `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow`
- **Visibility** public · **Lines** 2162–2181 · **Notes** —

### `theorem exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow`
- **Type**: `(K L …) (m) [IsCyclotomicExtension {m} K L] (hm : m%4 ≠ 2) (χ) (_hχ : χ ≠ 1) : ∃ C C', ∀ ζ : ℂ, ζ^{orderOf χ}=1 → ∀ N ≥ 1, |Nat.card {𝔞 : 𝔞≠⊥, N𝔞≤N, χ(𝔞)=ζ} − C·N| ≤ C'·N^{1−1/d}`
- **What**: Sharifi 7.1.19 step 1 — the value-fibre count is `C·N + O(N^{1−1/d})` with `C` independent of `ζ` (cyclotomic restatement).
- **How**: For `ζ ≠ 0`, the value-fibre equals the unramified-supported Frobenius-value-fibre (`card_valueFibre_…`), partitioned over `S_ζ = {g : χ g = ζ}` (`|S_ζ| = |ker χ|`, `card_charFibre_eq_card_ker`); applies L2 (`exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le`) per `g`; `C = |ker χ|·κ`. (Long ~140-line proof.)
- **Hypotheses**: cyclotomic; `χ ≠ 1`.
- **Uses from project**: `galoisCharacterOnIdeal`, `exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le`, `card_valueFibre_eq_card_unramifiedSupported_frobeniusValueFibre`, `card_charFibre_eq_card_ker`, `frobeniusIdeal`, `UnramifiedIn`
- **Used by**: `character_sum_geometry_of_numbers_bound`
- **Visibility** public · **Lines** 2208–2323 · **Notes** &gt;30-line proof

### `theorem sum_nthRootsFinset_eq_zero`
- **Type**: `{R} [CommRing R] [IsDomain R] {ζ n} (hζ : IsPrimitiveRoot ζ n) (hn : 1 &lt; n) : ∑_{v ∈ nthRootsFinset n 1} v = 0`
- **What**: The sum of all `n`-th roots of unity (`n &gt; 1`) is `0`.
- **How**: Multiplying the root set by `ζ` permutes it (`Finset.image`), so the sum equals `ζ·(sum)`; `(ζ−1)·sum = 0` with `ζ ≠ 1` gives `sum = 0`.
- **Hypotheses**: `ζ` a primitive `n`-th root, `n &gt; 1`.
- **Uses from project**: []
- **Used by**: `sum_galoisCharacterOnIdeal_eq_sum_card_sub_mul`
- **Visibility** private · **Lines** 2325–2346 · **Notes** —

### `theorem galoisCharacterOnIdeal_mem_insert_zero_nthRootsFinset`
- **Type**: `… (χ) (𝔞) : galoisCharacterOnIdeal K L χ 𝔞 ∈ insert 0 (nthRootsFinset (orderOf χ) 1)`
- **What**: The ideal character value is either `0` (ramified factor present) or an `orderOf χ`-th root of unity.
- **How**: Case split on `U 𝔞`: if all unramified, `χ(𝔞) = χ(Frob 𝔞)` is a root of unity (`pow_orderOf_eq_one`); else a factor is `0` so the product is `0` (`Multiset.prod_eq_zero`).
- **Hypotheses**: cyclotomic.
- **Uses from project**: `galoisCharacterOnIdeal`, `galoisCharacterOnIdeal_eq_char_frobeniusIdeal`, `galoisCharacterOnIdeal_eq_map_prod`, `UnramifiedIn`
- **Used by**: `sum_galoisCharacterOnIdeal_eq_sum_card_sub_mul`
- **Visibility** private · **Lines** 2348–2365 · **Notes** —

### `theorem sum_galoisCharacterOnIdeal_eq_sum_card_sub_mul`
- **Type**: `… (χ) (hord2 : 1 &lt; orderOf χ) (C₀ : ℝ) (N) [Fintype …] : ∑_{𝔞≠⊥,N𝔞≤N} χ(𝔞) = ∑_{v ∈ nthRootsFinset (orderOf χ) 1} ((Nat.card {𝔞 : χ(𝔞)=v} − C₀·N : ℝ) : ℂ)·v`
- **What**: Regroups the bounded-norm character sum fiberwise by value `v`, with each fibre count recentred by `C₀·N`.
- **How**: `Finset.sum_fiberwise_of_maps_to'` over `insert 0 (nthRoots)`; the `v=0` fibre drops; the recentring term `C₀·N·∑ v` vanishes by `sum_nthRootsFinset_eq_zero`. (&gt;30-line proof.)
- **Hypotheses**: cyclotomic; `orderOf χ &gt; 1`.
- **Uses from project**: `galoisCharacterOnIdeal`, `galoisCharacterOnIdeal_mem_insert_zero_nthRootsFinset`, `sum_nthRootsFinset_eq_zero`
- **Used by**: `character_sum_geometry_of_numbers_bound`
- **Visibility** private · **Lines** 2367–2416 · **Notes** &gt;30-line proof

### `theorem character_sum_geometry_of_numbers_bound`
- **Type**: `(K L …) (m) [IsCyclotomicExtension {m} K L] (hm : m%4 ≠ 2) (χ) (_hχ : χ ≠ 1) : ∃ C, ∀ N, ‖∑'_{𝔞≠⊥,N𝔞≤N} χ(𝔞)‖ ≤ C·N^{1−1/d}`
- **What**: Sharifi 7.1.19 step 1 — the partial character sum is `O(N^{1−1/[K:ℚ]})` for nontrivial `χ`.
- **How**: Rewrites the sum via `sum_galoisCharacterOnIdeal_eq_sum_card_sub_mul`; each fibre term has `‖v‖=1` (root of unity) and `|count − C₀N| ≤ C'·N^{1−1/d}` (`exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow`); `norm_sum_le`. (&gt;30-line proof.)
- **Hypotheses**: cyclotomic; `χ ≠ 1`.
- **Uses from project**: `galoisCharacterOnIdeal`, `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow`, `sum_galoisCharacterOnIdeal_eq_sum_card_sub_mul`
- **Used by**: `sum_galoisCharacterCoeff_isBigO`
- **Visibility** public · **Lines** 2423–2470 · **Notes** &gt;30-line proof

### `def galoisCharacterCoeff`
- **Type**: `(K L …) (χ) (n : ℕ) : ℂ`
- **What**: The `n`-th Dirichlet coefficient of `L(χ,·)` — sum of `χ(𝔞)` over nonzero ideals with `N𝔞 = n`.
- **How**: `∑'` of `galoisCharacterOnIdeal` over the (finite) norm-fibre `{𝔞 : NonzeroIdeal K // N𝔞 = n}`.
- **Hypotheses**: none.
- **Uses from project**: `galoisCharacterOnIdeal`, `NonzeroIdeal`
- **Used by**: `galoisCharacterCoeff_zero`, `norm_galoisCharacterCoeff_le`, `sum_galoisCharacterCoeff_eq_tsum_absNorm_le`, and the LSeries lemmas
- **Visibility** private (noncomputable) · **Lines** 2475–2478 · **Notes** —

### `theorem finite_nonzeroIdeal_absNorm_eq`
- **Type**: `(K) (n : ℕ) : Finite {𝔞 : NonzeroIdeal K // N𝔞 = n}`
- **What**: Each norm-fibre of nonzero ideals is finite.
- **How**: Injects into the finite `{I // N I = n}` (`Ideal.finite_setOf_absNorm_eq`) via `Set.Finite.of_finite_image`.
- **Hypotheses**: none.
- **Uses from project**: `NonzeroIdeal`
- **Used by**: `norm_galoisCharacterCoeff_le`, `sum_galoisCharacterCoeff_eq_tsum_absNorm_le`
- **Visibility** private · **Lines** 2482–2487 · **Notes** —

### `theorem galoisCharacterCoeff_zero`
- **Type**: `(K L …) (χ) : galoisCharacterCoeff K L χ 0 = 0`
- **What**: The `0`-th coefficient vanishes.
- **How**: No nonzero ideal has norm `0`, so the fibre is empty (`tsum_empty`).
- **Hypotheses**: none.
- **Uses from project**: `galoisCharacterCoeff`, `NonzeroIdeal`
- **Used by**: `lseries_galoisCharacterCoeff_eq_tsum`
- **Visibility** private · **Lines** 2490–2495 · **Notes** —

### `theorem norm_galoisCharacterCoeff_le`
- **Type**: `(K L …) (χ) (n) : ‖galoisCharacterCoeff K L χ n‖ ≤ (idealNormMultiplicity K n : ℝ)`
- **What**: The `n`-th coefficient is bounded by the ideal-norm multiplicity.
- **How**: `norm_tsum_le_tsum_norm`; each `‖χ(𝔞)‖ ≤ 1` (`norm_galoisCharacterOnIdeal_le_one`), so the fibre sum has norm `≤` the fibre cardinality `= idealNormMultiplicity`.
- **Hypotheses**: none.
- **Uses from project**: `galoisCharacterCoeff`, `galoisCharacterOnIdeal`, `norm_galoisCharacterOnIdeal_le_one`, `finite_nonzeroIdeal_absNorm_eq`, `idealNormMultiplicity`, `NonzeroIdeal`
- **Used by**: `sum_norm_galoisCharacterCoeff_isBigO`
- **Visibility** private · **Lines** 2499–2516 · **Notes** —

### `theorem sum_galoisCharacterCoeff_eq_tsum_absNorm_le`
- **Type**: `(K L …) (χ) (n) : ∑_{k ∈ Icc 1 n} galoisCharacterCoeff K L χ k = ∑'_{𝔞≠⊥, N𝔞≤n} χ(𝔞)`
- **What**: Partial sum of coefficients equals the bounded-norm character sum.
- **How**: Fibrewise regrouping of the bounded-norm ideal sum by `N𝔞 ∈ [1,n]` (`Finset.sum_fiberwise_of_maps_to`), matched against each coefficient's fibre `tsum` (`Fintype.sum_equiv`). (&gt;30-line proof.)
- **Hypotheses**: none.
- **Uses from project**: `galoisCharacterCoeff`, `galoisCharacterOnIdeal`, `finite_nonzeroIdeal_absNorm_eq`, `NonzeroIdeal`
- **Used by**: `sum_galoisCharacterCoeff_isBigO`, `artinLSeries_analytic_extension` (via `S`)
- **Visibility** private · **Lines** 2522–2552 · **Notes** &gt;30-line proof

### `theorem sum_galoisCharacterCoeff_isBigO`
- **Type**: `(K L …) (m) [IsCyclotomicExtension {m} K L] (hm) (χ) (_hχ) : (fun n =&gt; ∑_{k∈Icc 1 n} coeff k) =O[atTop] (fun n =&gt; n^{1−1/d})`
- **What**: Step 1 (LF3 input) — partial sums of coefficients are `O(n^{1−1/d})`.
- **How**: Rewrites partial sums via `sum_galoisCharacterCoeff_eq_tsum_absNorm_le` and applies the character-sum bound `character_sum_geometry_of_numbers_bound`.
- **Hypotheses**: cyclotomic; `χ ≠ 1`.
- **Uses from project**: `galoisCharacterCoeff`, `character_sum_geometry_of_numbers_bound`, `sum_galoisCharacterCoeff_eq_tsum_absNorm_le`
- **Used by**: `artinLSeries_analytic_extension`
- **Visibility** private · **Lines** 2557–2567 · **Notes** —

### `theorem sum_norm_galoisCharacterCoeff_isBigO`
- **Type**: `(K L …) (χ) : (fun n =&gt; ∑_{k∈Icc 1 n} ‖coeff k‖) =O[atTop] (fun n =&gt; n^1)`
- **What**: Step 2 — partial sums of coefficient norms are `O(n)` (crude absolute-convergence bound).
- **How**: Pointwise `‖coeff k‖ ≤ idealNormMultiplicity` (`norm_galoisCharacterCoeff_le`), whose partial sums are `O(n)` (`sum_idealNormMultiplicity_isBigO`).
- **Hypotheses**: none.
- **Uses from project**: `galoisCharacterCoeff`, `norm_galoisCharacterCoeff_le`, `sum_idealNormMultiplicity_isBigO`, `idealNormMultiplicity`
- **Used by**: `artinLSeries_analytic_extension`
- **Visibility** private · **Lines** 2573–2582 · **Notes** —

### `theorem lseries_galoisCharacterCoeff_eq_tsum`
- **Type**: `(K L …) (χ) (s) (hs : 1 &lt; s.re) : LSeries (galoisCharacterCoeff K L χ) s = ∑'_{𝔞≠⊥} χ(𝔞)·N𝔞^{-s}`
- **What**: Step 3 — on `Re s &gt; 1` the L-series of the coefficient function equals the absolutely-convergent ideal sum.
- **How**: `Equiv.sigmaFiberEquiv` partitions the ideal sum by `N𝔞`; the per-fibre sum collapses to `coeff n · n^{-s}`; `LSeries.term_def₀` identifies the L-series. Absolute summability by comparison `‖χ(𝔞)N𝔞^{-s}‖ ≤ N𝔞^{-s}` against `ζ_K`. (&gt;30-line proof.)
- **Hypotheses**: `Re s &gt; 1`.
- **Uses from project**: `galoisCharacterCoeff`, `galoisCharacterOnIdeal`, `galoisCharacterCoeff_zero`, `norm_galoisCharacterOnIdeal_le_one`, `hasSum_nonzeroIdeal_absNorm_cpow`, `NonzeroIdeal`
- **Used by**: `artinLSeries_analytic_extension`
- **Visibility** private · **Lines** 2590–2622 · **Notes** &gt;30-line proof

### `theorem setIntegral_Ioi_one_mul_cpow_eq_mellin`
- **Type**: `(S : ℝ→ℂ) (hS : ∀ t &lt; 1, S t = 0) (s : ℂ) : ∫ t in Ioi 1, S t · t^{-(s+1)} = mellin S (-s)`
- **What**: Rewrites a Mellin transform of a function vanishing below `1` as an integral over `(1,∞)`.
- **How**: Unfolds `mellin`; the `(0,1)` part vanishes (`hS`) so the integral over `Ioi 0` equals that over `Ioi 1` (`setIntegral_indicator`, a.e. on `t ≠ 1`); commutes the scalar.
- **Hypotheses**: `S` vanishes on `t &lt; 1`.
- **Uses from project**: []
- **Used by**: `artinLSeries_analytic_extension`
- **Visibility** private (`open MeasureTheory Set`) · **Lines** 2625–2641 · **Notes** —

### `theorem locallyIntegrableOn_Ioi_comp_nat_floor`
- **Type**: `(g : ℕ→ℂ) : LocallyIntegrableOn (fun t =&gt; g ⌊t⌋₊) (Ioi 0)`
- **What**: A step function `t ↦ g ⌊t⌋₊` is locally integrable on `(0,∞)`.
- **How**: It is measurable (`Nat.measurable_floor`) and bounded on each compact subset (by the finite sup of `‖g n‖` over `n ≤ ⌊b⌋₊`); `Measure.integrableOn_of_bounded`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `artinLSeries_analytic_extension`
- **Visibility** private (`open MeasureTheory Set`) · **Lines** 2644–2659 · **Notes** —

### `theorem artinLSeries_analytic_extension`
- **Type**: `(K L …) (m) [IsCyclotomicExtension {m} K L] (hm) (χ) (_hχ) : ∃ Lf, AnalyticOn ℂ Lf {s : 1−1/d &lt; s.re} ∧ (∀ s, 1 &lt; s.re → Lf s = ∑'_{𝔞≠⊥} χ(𝔞)·N𝔞^{-s})`
- **What**: Sharifi 7.1.19 step 1b — `L(χ,·)` extends analytically from `Re s &gt; 1` to the half-plane `Re s &gt; 1 − 1/[K:ℚ]` (cyclotomic restatement).
- **How**: Defines `Lf s = s·mellin S (−s)` with `S` the coefficient partial-sum step function; analyticity via `mellin_differentiableAt_of_isBigO_rpow` (the `O(t^r)` bound from `sum_galoisCharacterCoeff_isBigO`); the value identity via `LSeries_eq_mul_integral` + `setIntegral_Ioi_one_mul_cpow_eq_mellin`. (Long proof.)
- **Hypotheses**: cyclotomic; `χ ≠ 1`.
- **Uses from project**: `galoisCharacterOnIdeal`, `galoisCharacterCoeff`, `sum_galoisCharacterCoeff_isBigO`, `sum_norm_galoisCharacterCoeff_isBigO`, `lseries_galoisCharacterCoeff_eq_tsum`, `setIntegral_Ioi_one_mul_cpow_eq_mellin`, `locallyIntegrableOn_Ioi_comp_nat_floor`, `NonzeroIdeal`
- **Used by**: `artinDirichletSeries_norm_le_of_ne_one`; and consumed by `artinLSeries_one_ne_zero`'s callers (the `Lf` hypothesis)
- **Visibility** public (`open Filter Topology Set MeasureTheory Asymptotics`) · **Lines** 2686–2734 · **Notes** &gt;30-line proof

### `theorem logDedekindZeta_re_tendsto_atTop`
- **Type**: `(L) [Field L] [NumberField L] : Tendsto (fun s : ℝ =&gt; Real.log (dedekindZeta L s).re) (𝓝[&gt;] 1) atTop`
- **What**: Ingredient B — `log (ζ_L(s)).re → +∞` as `s ↓ 1` (driven by the simple pole).
- **How**: `logDedekindZeta_sub_log_inv_sub_one_bounded` gives a lower bound `log(1/(s−1)) − C` which itself `→ +∞` (`tendsto_log_one_div_sub_one_atTop`); `tendsto_atTop_mono'`.
- **Hypotheses**: `L` a number field.
- **Uses from project**: `logDedekindZeta_sub_log_inv_sub_one_bounded`, `tendsto_log_one_div_sub_one_atTop`
- **Used by**: `artinLSeries_one_ne_zero`
- **Visibility** private (`open Filter Topology Set`) · **Lines** 2756–2767 · **Notes** —

### `theorem analytic_log_norm_le_of_apply_eq_zero`
- **Type**: `{f : ℂ→ℂ} (hf : AnalyticAt ℂ f 1) (hf0 : f 1 = 0) (hne : ¬∀ᶠ z in 𝓝 1, f z = 0) : ∃ C, ∀ᶠ s in 𝓝[&gt;] 1, Real.log ‖f s‖ ≤ −log(1/(s−1)) + C`
- **What**: Ingredient C — near `s ↓ 1`, an analytic function with a zero at `1` has log-norm bounded above by `−log(1/(s−1)) + C`.
- **How**: `exists_eventuallyEq_pow_smul_nonzero_iff` factors `f z = (z−1)^n g z` with `g 1 ≠ 0`, `n ≥ 1` (else `f 1 = g 1 ≠ 0`); `log‖f s‖ = n·log(s−1) + log‖g s‖`, with `n·log(s−1) ≤ log(s−1)` (negative) and `‖g s‖` bounded by continuity. (&gt;30-line proof.)
- **Hypotheses**: `f` analytic at `1`, `f 1 = 0`, not locally zero.
- **Uses from project**: []
- **Used by**: `artinLSeries_one_ne_zero`
- **Visibility** private (`open Filter Topology Set`) · **Lines** 2776–2829 · **Notes** &gt;30-line proof

### `instance galoisCharacter.instFintype`
- **Type**: `(K L …) [FiniteDimensional K L] : Fintype (galoisCharacter K L)`
- **What**: A `Fintype` instance on the character group (so `∏ χ`/`∑ χ` parse).
- **How**: `Fintype.ofFinite` (the character group of a finite group is finite).
- **Hypotheses**: `L/K` finite-dimensional.
- **Uses from project**: `galoisCharacter`
- **Used by**: all the finite character products/sums in the non-vanishing section
- **Visibility** local instance · **Lines** 2834–2837 · **Notes** —

### `def artinDirichletSeries`
- **Type**: `(K L …) (χ) (s : ℂ) : ℂ`
- **What**: The Dirichlet series `L_χ(s) = ∑'_{𝔞≠⊥} χ(𝔞)·N𝔞^{-s}` as a function of `s`.
- **How**: Direct `∑'` over nonzero ideals.
- **Hypotheses**: none.
- **Uses from project**: `galoisCharacterOnIdeal`
- **Used by**: `tprod_unramified_eq_prod_artinDirichletSeries`, `dedekindZeta_eq_prod_artinDirichletSeries`, and all the log-bound helpers
- **Visibility** private (noncomputable) · **Lines** 2842–2846 · **Notes** —

### `theorem norm_one_sub_inv_sub_one_le`
- **Type**: `{y : ℂ} (hy : ‖y‖ ≤ 1/2) : ‖(1−y)⁻¹ − 1‖ ≤ 2‖y‖`
- **What**: Pure-`ℂ` Euler-factor estimate.
- **How**: `(1−y)⁻¹ − 1 = y·(1−y)⁻¹`, and `‖(1−y)⁻¹‖ ≤ 2` because `‖1−y‖ ≥ 1−‖y‖ ≥ 1/2` (`norm_sub_norm_le`, `inv_anti₀`).
- **Hypotheses**: `‖y‖ ≤ 1/2`.
- **Uses from project**: []
- **Used by**: `summable_norm_primeIdeal_factor_sub_one`, `multipliable_artinLocalFactor`
- **Visibility** private · **Lines** 2853–2871 · **Notes** —

### `theorem norm_absNorm_cpow_neg_le_half`
- **Type**: `{R} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] {s} (hs : 1 &lt; s.re) (𝔭 : {𝔭 // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) : ‖(N𝔭 : ℂ)^{-s}‖ ≤ 1/2`
- **What**: For a nonzero prime and `Re s &gt; 1`, `‖N𝔭^{-s}‖ ≤ 1/2` (since `N𝔭 ≥ 2`).
- **How**: `Complex.norm_natCast_cpow_of_pos` reduces to `(N𝔭)^{-s.re} ≤ (N𝔭)^{-1} ≤ 1/2` via `rpow` monotonicity and `N𝔭 ≥ 2`.
- **Hypotheses**: `𝔭` nonzero prime; `Re s &gt; 1`.
- **Uses from project**: []
- **Used by**: `summable_norm_primeIdeal_factor_sub_one`, `multipliable_artinLocalFactor`
- **Visibility** private · **Lines** 2875–2893 · **Notes** —

### `theorem summable_norm_primeIdeal_factor_sub_one`
- **Type**: `(L) [Field L] [NumberField L] {s} (hs : 1 &lt; s.re) : Summable (fun 𝔓 : {𝔓 // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} =&gt; ‖(1 − N𝔓^{-s})⁻¹ − 1‖)`
- **What**: The prime-ideal Euler factor of `ζ_L`, shifted by `1`, is absolutely summable.
- **How**: `∑_𝔞 ‖N𝔞^{-s}‖` over nonzero ideals converges (`hasSum_nonzeroIdeal_absNorm_cpow`); restrict to primes; per-factor `‖(1−y)⁻¹−1‖ ≤ 2‖y‖` (`norm_one_sub_inv_sub_one_le` + `norm_absNorm_cpow_neg_le_half`).
- **Hypotheses**: `Re s &gt; 1`.
- **Uses from project**: `hasSum_nonzeroIdeal_absNorm_cpow`, `norm_one_sub_inv_sub_one_le`, `norm_absNorm_cpow_neg_le_half`, `NonzeroIdeal`
- **Used by**: `hasProd_primeIdeal_factor`, `multipliable_primeIdeal_factor_subtype`, `tprod_unramified_eq_prod_artinDirichletSeries`
- **Visibility** private · **Lines** 2899–2912 · **Notes** —

### `theorem hasProd_primeIdeal_factor`
- **Type**: `(L) {s} (hs : 1 &lt; s.re) : HasProd (fun 𝔓 // … =&gt; (1−N𝔓^{-s})⁻¹) (dedekindZeta L s)`
- **What**: The prime-ideal Euler product of `ζ_L` is multipliable with value `ζ_L(s)`.
- **How**: `multipliable_one_add_of_summable` (from `summable_norm_primeIdeal_factor_sub_one`); value pinned by `dedekindZeta_eq_tprod_primeIdeal`.
- **Hypotheses**: `Re s &gt; 1`.
- **Uses from project**: `summable_norm_primeIdeal_factor_sub_one`, `dedekindZeta_eq_tprod_primeIdeal`
- **Used by**: `dedekindZeta_eq_prod_artinDirichletSeries`
- **Visibility** private · **Lines** 2918–2930 · **Notes** —

### `theorem multipliable_primeIdeal_factor_subtype`
- **Type**: `(L) {s} (hs) (p : {𝔓 // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥} → Prop) : Multipliable (fun 𝔓 : {𝔓 // p 𝔓} =&gt; (1 − N𝔓^{-s})⁻¹)`
- **What**: The prime Euler factor restricted to any predicate-subtype is multipliable.
- **How**: Restricts the *summable norm* via `Summable.subtype` (avoiding the whnf-exploding `Multipliable.subtype`), then rebuilds with `multipliable_one_add_of_summable`.
- **Hypotheses**: `Re s &gt; 1`.
- **Uses from project**: `summable_norm_primeIdeal_factor_sub_one`
- **Used by**: `dedekindZeta_eq_prod_artinDirichletSeries`
- **Visibility** private · **Lines** 2936–2947 · **Notes** —

### `theorem multipliable_artinLocalFactor`
- **Type**: `(K L …) (χ) {s} (hs : 1 &lt; s.re) : Multipliable (fun 𝔭 : {𝔭 // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} =&gt; (1 − χ(Frob 𝔭)·N𝔭^{-s})⁻¹)`
- **What**: The χ-twisted local Euler product over unramified primes is multipliable.
- **How**: `‖χ(Frob 𝔭)‖=1` (`norm_galoisCharacter_out`), so `‖χ(Frob 𝔭)N𝔭^{-s}‖ = ‖N𝔭^{-s}‖ ≤ 1/2`; summability from the nonzero-ideal sum; `multipliable_one_add_of_summable`.
- **Hypotheses**: `Re s &gt; 1`.
- **Uses from project**: `hasSum_nonzeroIdeal_absNorm_cpow`, `norm_galoisCharacter_out`, `norm_absNorm_cpow_neg_le_half`, `norm_one_sub_inv_sub_one_le`, `UnramifiedIn`, `UnramifiedIn.ne_bot`, `frobeniusClass`, `NonzeroIdeal`
- **Used by**: `tprod_unramified_eq_prod_artinDirichletSeries`
- **Visibility** private · **Lines** 2953–2980 · **Notes** —

### `def underUP`
- **Type**: `(K L …) (𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ UnramifiedIn K L (𝔓.under (𝓞 K))}) : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭}`
- **What**: Maps an unramified-below `L`-prime to the unramified `K`-prime below it (`𝔓.under`).
- **How**: Builds the subtype element `⟨𝔓.under, _, 𝔓.2.2.2⟩` with `inferInstance` for primality.
- **Hypotheses**: none.
- **Uses from project**: `UnramifiedIn`
- **Used by**: `underUP_val`, `fiberUnderEquiv`, `tprod_unramified_eq_prod_artinDirichletSeries`
- **Visibility** private · **Lines** 2985–2989 · **Notes** —

### `theorem underUP_val`
- **Type**: `(K L …) (𝔓) : (underUP K L 𝔓).1 = 𝔓.1.under (𝓞 K)`
- **What**: The underlying `K`-ideal of `underUP 𝔓` is `𝔓.under`.
- **How**: `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `underUP`
- **Used by**: `fiberUnderEquiv`
- **Visibility** private (`@[simp]`) · **Lines** 2991–2994 · **Notes** —

### `def fiberUnderEquiv`
- **Type**: `(K L …) (c : {𝔭 // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭}) : {𝔓 // underUP K L 𝔓 = c} ≃ {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver c.1 ∧ 𝔓 ≠ ⊥}`
- **What**: Reindexes the fibre of `underUP` over `c` as the primes of `𝓞 L` lying over `c`.
- **How**: Explicit `Equiv` translating `underUP 𝔓 = c` into `𝔓.LiesOver c.1` (via `underUP_val` and `LiesOver.over`).
- **Hypotheses**: none.
- **Uses from project**: `underUP`, `underUP_val`, `UnramifiedIn`
- **Used by**: `tprod_unramified_eq_prod_artinDirichletSeries`
- **Visibility** private · **Lines** 3000–3012 · **Notes** `set_option maxHeartbeats 800000`

### `theorem tprod_unramified_eq_prod_artinDirichletSeries`
- **Type**: `(K L …) [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] {s} (hs : 1 &lt; s.re) : (∏' 𝔓 unram-below, (1 − N𝔓^{-s})⁻¹) = ∏'_χ artinDirichletSeries K L χ s`
- **What**: The unramified part of the prime-ideal Euler product equals `∏_χ L_χ`.
- **How**: Regroup the unramified `L`-primes fiberwise over `K`-primes (`Equiv.sigmaFiberEquiv` + `HasProd.sigma`); each fibre is `∏_χ (1 − χ(σ_𝔭)N𝔭^{-s})⁻¹` (`dedekindZeta_local_factor_eq_product_artin_local`, `fiberUnderEquiv`); swap the finite character product (`Multipliable.tprod_finsetProd`) and apply `exists_artinLSeries_eulerProduct_abelian`. (Long proof.)
- **Hypotheses**: finite abelian; `Re s &gt; 1`.
- **Uses from project**: `artinDirichletSeries`, `underUP`, `fiberUnderEquiv`, `dedekindZeta_local_factor_eq_product_artin_local`, `exists_artinLSeries_eulerProduct_abelian`, `multipliable_artinLocalFactor`, `summable_norm_primeIdeal_factor_sub_one`, `frobeniusClass`, `UnramifiedIn`
- **Used by**: `dedekindZeta_eq_prod_artinDirichletSeries`
- **Visibility** private · **Lines** 3021–3098 · **Notes** `set_option maxHeartbeats 1600000`; &gt;30-line proof

### `theorem dedekindZeta_eq_prod_artinDirichletSeries`
- **Type**: `(K L …) {s} (hs : 1 &lt; s.re) : dedekindZeta L s = (∏'_χ artinDirichletSeries K L χ s) · ∏'_{𝔓 ram-below} (1 − N𝔓^{-s})⁻¹`
- **What**: Ingredient A (corrected) — `ζ_L = (∏_χ L_χ) · R`, with `R` the finite product over ramified-below primes (the factors dropped by the `L_χ`).
- **How**: The prime product (`hasProd_primeIdeal_factor`) splits into unramified-below vs ramified-below (`HasProd.mul_compl`, `multipliable_primeIdeal_factor_subtype`); the unramified part is `∏_χ L_χ` (`tprod_unramified_eq_prod_artinDirichletSeries`), flattened by explicit subtype `Equiv`s. (Long proof.)
- **Hypotheses**: finite abelian; `Re s &gt; 1`.
- **Uses from project**: `artinDirichletSeries`, `hasProd_primeIdeal_factor`, `multipliable_primeIdeal_factor_subtype`, `tprod_unramified_eq_prod_artinDirichletSeries`, `UnramifiedIn`
- **Used by**: `log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded`, `artinLSeries_one_ne_zero`
- **Visibility** private · **Lines** 3121–3167 · **Notes** `set_option maxHeartbeats 800000`; &gt;30-line proof

### `instance finite_ramifiedAbove`
- **Type**: `(K L …) : Finite {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ ¬ UnramifiedIn K L (𝔓.under (𝓞 K))}`
- **What**: The primes of `𝓞 L` lying over a ramified `K`-prime form a finite set.
- **How**: Finitely many ramified `K`-primes (`finite_ramifiedIn`), each with finitely many primes above (`primesOver_finite`); injects into the sigma.
- **Hypotheses**: none.
- **Uses from project**: `UnramifiedIn`, `finite_ramifiedIn`
- **Used by**: `log_norm_ramified_factor_bounded`, `log_dedekindZeta_re_sub_sum_…` (Fintype of the ramified set)
- **Visibility** private instance · **Lines** 3171–3191 · **Notes** —

### `theorem dedekindZeta_eq_ofReal_re`
- **Type**: `(L) {s : ℝ} (hs : 1 &lt; s) : dedekindZeta L (s : ℂ) = ((dedekindZeta L (s:ℂ)).re : ℂ)`
- **What**: For real `s &gt; 1`, `ζ_L(s)` is a real number (equals the cast of its real part).
- **How**: The Dirichlet series `∑ₙ (mult n) n^{-s}` has real terms; `Complex.ofReal_tsum` after rewriting each term as a real cast (`dedekindZeta_eq_tsum_idealNormMultiplicity`).
- **Hypotheses**: `s &gt; 1` real.
- **Uses from project**: `dedekindZeta_eq_tsum_idealNormMultiplicity`, `summable_idealNormMultiplicity_mul_cpow_neg`, `idealNormMultiplicity`
- **Used by**: `log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded`
- **Visibility** private · **Lines** 3196–3213 · **Notes** —

### `theorem log_norm_ramified_factor_bounded`
- **Type**: `(K L …) : ∃ C, ∀ᶠ s in 𝓝[&gt;] 1, |Real.log ‖∏'_{𝔓 ram-below} (1 − N𝔓^{-s})⁻¹‖| ≤ C`
- **What**: The ramified correction factor `R(s)` has `|log‖R(s)‖|` bounded near `s ↓ 1` (the `O(1)` slack).
- **How**: `R` is a finite product (`finite_ramifiedAbove`) of factors continuous at `1` with nonzero limit (`N𝔓 ≥ 2` ⟹ denominators `≠ 0`); `log‖R‖` is continuous at `1`, hence eventually within `±1` of `log‖R 1‖`. (&gt;30-line proof.)
- **Hypotheses**: finite abelian.
- **Uses from project**: `UnramifiedIn`, `finite_ramifiedAbove`
- **Used by**: `log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded`
- **Visibility** private (`open Filter Topology Set`) · **Lines** 3220–3281 · **Notes** &gt;30-line proof

### `theorem log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded`
- **Type**: `(K L …) : ∃ C, ∀ᶠ s in 𝓝[&gt;] 1, |Real.log (dedekindZeta L s).re − ∑_χ Real.log ‖artinDirichletSeries K L χ s‖| ≤ C`
- **What**: Ingredient A (bounded real-log form) — the gap between `log ζ_L.re` and `∑_χ log‖L_χ‖` is `O(1)`.
- **How**: Takes `log‖·‖` of the corrected factorisation `ζ_L = (∏_χ L_χ)·R` (`dedekindZeta_eq_prod_artinDirichletSeries`), using `ζ_L(s)` positive real (`dedekindZeta_eq_ofReal_re`, `dedekindZeta_re_pos_of_one_lt`); the remaining gap is `log‖R‖`, bounded by `log_norm_ramified_factor_bounded`. (&gt;30-line proof.)
- **Hypotheses**: finite abelian.
- **Uses from project**: `artinDirichletSeries`, `dedekindZeta_eq_prod_artinDirichletSeries`, `log_norm_ramified_factor_bounded`, `dedekindZeta_eq_ofReal_re`, `dedekindZeta_re_pos_of_one_lt`, `UnramifiedIn`
- **Used by**: `artinLSeries_one_ne_zero`
- **Visibility** private (`open Filter Topology Set`) · **Lines** 3290–3336 · **Notes** &gt;30-line proof

### `theorem artinDirichletSeries_norm_le_of_ne_one`
- **Type**: `(K L …) (m) [IsCyclotomicExtension {m} K L] (hm) (χ') (hχ' : χ' ≠ 1) : ∃ C, ∀ᶠ s in 𝓝[&gt;] 1, ‖artinDirichletSeries K L χ' (s:ℂ)‖ ≤ C`
- **What**: Assembly helper (ii) — for nontrivial `χ'`, `‖L_{χ'}(s)‖` is bounded above near `s = 1`.
- **How**: `L_{χ'}` extends analytically across `1` (`artinLSeries_analytic_extension`), so it is continuous there, hence bounded by `‖Lf' 1‖+1`; the extension agrees with `artinDirichletSeries` on `Re s &gt; 1`.
- **Hypotheses**: cyclotomic; `χ' ≠ 1`.
- **Uses from project**: `artinDirichletSeries`, `artinLSeries_analytic_extension`
- **Used by**: `artinLSeries_one_ne_zero`
- **Visibility** private (`open Filter Topology Set`) · **Lines** 3343–3374 · **Notes** &gt;30-line proof

### `theorem log_norm_artinDirichletSeries_one_le`
- **Type**: `(K L …) : ∃ C, ∀ᶠ s in 𝓝[&gt;] 1, Real.log ‖artinDirichletSeries K L 1 (s:ℂ)‖ ≤ Real.log (1/(s−1)) + C`
- **What**: Assembly helper (i) — the trivial-character factor `L_1` is bounded above by the `ζ_K` simple-pole asymptotic.
- **How**: Termwise `‖χ̃_1(𝔞)N𝔞^{-s}‖ ≤ N𝔞^{-s}` (`norm_galoisCharacterOnIdeal_le_one`), so `‖L_1(s)‖ ≤ ζ_K(s) ≥ 1`; `log‖L_1‖ ≤ log ζ_K ≤ log(1/(s−1))+C` (`logDedekindZeta_sub_log_inv_sub_one_bounded` for `K`). (&gt;30-line proof.)
- **Hypotheses**: finite abelian.
- **Uses from project**: `artinDirichletSeries`, `galoisCharacterOnIdeal`, `norm_galoisCharacterOnIdeal_le_one`, `hasSum_nonzeroIdeal_absNorm_cpow`, `dedekindZeta_re_pos_of_one_lt`, `logDedekindZeta_sub_log_inv_sub_one_bounded`, `NonzeroIdeal`
- **Used by**: `artinLSeries_one_ne_zero`
- **Visibility** private (`open Filter Topology Set`) · **Lines** 3386–3448 · **Notes** &gt;30-line proof

### `theorem artinLSeries_one_ne_zero`
- **Type**: `(K L …) (m) [IsCyclotomicExtension {m} K L] (hm) (χ) (_hχ : χ ≠ 1) : ∀ Lf, AnalyticOn ℂ Lf {s : 1−1/d &lt; s.re} → (∀ s, 1 &lt; s.re → Lf s = ∑'_{𝔞≠⊥} χ(𝔞)·N𝔞^{-s}) → Lf 1 ≠ 0`
- **What**: Sharifi 7.1.19 step 2 — non-vanishing `L(χ,1) ≠ 0` for nontrivial `χ` (cyclotomic restatement). The key analytic input of the cyclotomic Chebotarev case.
- **How**: Dirichlet's argument run over all characters. If `Lf 1 = 0`, Ingredient C (`analytic_log_norm_le_of_apply_eq_zero`) bounds `log‖L_χ‖` above by `−log(1/(s−1))`, every other factor is bounded (helpers i/ii), and the ramified slack is `O(1)`; summing, `log ζ_L` stays bounded — contradicting Ingredient B (`logDedekindZeta_re_tendsto_atTop`, `→ +∞`). The `χ'=1` pole and `χ'=χ` zero cancel since `χ ≠ 1`. (Very long ~130-line proof.)
- **Hypotheses**: cyclotomic; `χ ≠ 1`; `Lf` the analytic extension agreeing with the Dirichlet series on `Re s &gt; 1`.
- **Uses from project**: `galoisCharacterOnIdeal`, `artinDirichletSeries`, `dedekindZeta_eq_prod_artinDirichletSeries`, `logDedekindZeta_re_tendsto_atTop`, `analytic_log_norm_le_of_apply_eq_zero`, `log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded`, `log_norm_artinDirichletSeries_one_le`, `artinDirichletSeries_norm_le_of_ne_one`, `dedekindZeta_re_pos_of_one_lt`
- **Used by**: unused in file (top-level export consumed by Cyclotomic.lean / Main.lean)
- **Visibility** public (`open Filter Topology Set`) · **Lines** 3464–3597 · **Notes** &gt;30-line proof

---

## File Summary

**Totals**: ~73 top-level declarations — 8 `def`s (`galoisCharacterOnIdeal`, `charEval`, `frobeniusIdeal`, `badPart`, `goodPart`, `IsBadPart`, `realizedResidues`, `artinDirichletSeries`, `galoisCharacterCoeff`, `underUP`, `fiberUnderEquiv` — 11 if counting all), 1 `abbrev` (`galoisCharacter`), 3 `instance`s (`galoisCharacter.instFintype`, `finite_L2`, `finite_ramifiedAbove`), and ~58 `theorem`/`lemma`s. Mix of `public` (the ~14 named Sharifi-milestone theorems + the multiplicativity API) and `private` (~50 internal helpers). The file proves the abelian zeta-factorisation engine: the abelian Euler product (7.1.18), the local-factor identity (7.1.16), the geometry-of-numbers value-fibre count (7.1.19 step 1) via the long leaf-G Frobenius-fibre chain, the analytic extension (7.1.19 step 1b), and the non-vanishing `L(χ,1) ≠ 0` (7.1.19 step 2).

**Key project API used by 3+ in-file consumers**:
- `galoisCharacterOnIdeal` (the central coefficient) — used by ~25 declarations
- `galoisCharacterOnIdeal_eq_map_prod` — 6 consumers
- `frobeniusIdeal` (+ `_mul`, `_one`, `_apply_prime`) — the leaf-G workhorse, ~20 consumers
- `UnramifiedIn` / `frobeniusClass` (cross-file, Frobenius.lean) — pervasive
- `finite_isBadPart` — 6 consumers; `card_L2_eq_sum_residue` — 2; `exists_kappa_uniform` — 2
- `artinDirichletSeries` — 7 consumers (the non-vanishing section)
- `norm_galoisCharacterOnIdeal_le_one` — 3; `galoisCharacterCoeff` — 6
- cross-file: `hasSum_nonzeroIdeal_absNorm_cpow` (4), `NonzeroIdeal` (many), `idealNormMultiplicity` (4), `dedekindZeta_re_pos_of_one_lt` (3)

**`sorry`**: NONE. The file is `sorry`-free. (The narrative docstrings reference "the project's deepest gap" — the Lipschitz-frontier regularity — but it is discharged here by delegating to the external `normLeOne_frontier_lipschitz_cover` in `ForMathlib/NormLeOneLipschitz.lean`; `normLeOne_frontier_lipschitz` is a one-line wrapper, not a `sorry`.)

**`set_option maxHeartbeats` overrides** (5):
- `sum_rpow_le_euler_prod` — 1600000 (line 1449)
- `fiberUnderEquiv` — 800000 (line 2996)
- `tprod_unramified_eq_prod_artinDirichletSeries` — 1600000 (line 3014)
- `dedekindZeta_eq_prod_artinDirichletSeries` — 800000 (line 3100)
- `card_fibre_bound_two_le` — no option but is the longest proof (~277 lines)

**Unused-in-file (top-level exports / interfaces consumed downstream or in sibling files)**:
- `norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded` (Dirichlet-test API)
- `normLeOne_frontier_lipschitz` (named deep-gap interface)
- `artinLSeries_one_ne_zero` (consumed by Cyclotomic.lean/Main.lean)
(All other declarations have at least one in-file consumer.)

**`&gt;30-line proofs`** (substantial; ~30 of them): `norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded`, `exists_artinLSeries_eulerProduct_abelian`, `prod_galoisCharacter_one_sub`, `dedekindZeta_local_factor_eq_product_artin_local`, `charFibre_mem_range`, `unramifiedIn_of_coprime_absNorm`, `autToPow_frobeniusIdeal`, `card_good_fibre_eq_card_residue`, `card_fibre_eq_card_good_fibre`, `card_L2_eq_sum_fibres`, `sum_rpow_le_euler_prod`, `card_fibre_bound_two_le` (≈277 lines, the largest), `coprime_absNorm_of_unramified_of_finrank_eq_one`, `card_fibre_bound_eq_one`, `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow` (≈140 lines), `sum_galoisCharacterOnIdeal_eq_sum_card_sub_mul`, `character_sum_geometry_of_numbers_bound`, `sum_galoisCharacterCoeff_eq_tsum_absNorm_le`, `lseries_galoisCharacterCoeff_eq_tsum`, `artinLSeries_analytic_extension`, `analytic_log_norm_le_of_apply_eq_zero`, `tprod_unramified_eq_prod_artinDirichletSeries`, `dedekindZeta_eq_prod_artinDirichletSeries`, `log_norm_ramified_factor_bounded`, `log_dedekindZeta_re_sub_sum_log_norm_artinDirichlet_bounded`, `artinDirichletSeries_norm_le_of_ne_one`, `log_norm_artinDirichletSeries_one_le`, `artinLSeries_one_ne_zero` (≈133 lines).

**TODO / scaffolding**: none. No `axiom`s, no placeholder `def := sorry` (consistent with the project's hard constraints).</result>
<usage><subagent_tokens>190610</subagent_tokens><tool_uses>16</tool_uses><duration_ms>584475</duration_ms></usage>
</task-notification>