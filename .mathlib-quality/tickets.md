# L-function chain — ticket board (from decomposition.md, /develop --decompose 2026-06-04)

Dependency order. Full specs (statement / verbatim source quote / sketch / discharge / attacks)
are in `.mathlib-quality/decomposition.md` under "L-function chain decomposition". All proofs may
use **L3** (`character_sum_geometry_of_numbers_bound`, the geometry-of-numbers API gap) as a sorried
dependency — L3 itself is left sorried/blocked (its own sub-project); everything else is proven so
the chain is sorry-free *modulo L3*.

## Tickets

### [LF1] exists_artinLSeries_eulerProduct_abelian — Status: open
- File: ZetaProduct.lean:176 · Depends on: none · Discharge: project (mirror `dedekindZeta_eq_tprod_primeIdeal`)
- Sketch: decomposition.md L1 (Prop 7.1.18) — `L(χ,s)=∏_𝔭(1-χ(𝔭)N𝔭⁻ˢ)⁻¹=Σ_𝔞 χ(𝔞)N𝔞⁻ˢ`, χ multiplicative on ideals, UFD/abs-conv.

### [LF2] dedekindZeta_local_factor_eq_product_artin_local — Status: open
- File: ZetaProduct.lean:189 · Depends on: none · Discharge: project (finite abelian char theory)
- Sketch: decomposition.md L2 (Prop 7.1.16 local) — `∏_χ(1-χ(σ)X)=(1-X^{ordσ})^{|G|/ordσ}` matches split of 𝔭.

### [LF3] character_sum_geometry_of_numbers_bound — Status: done (2026-06-05, /beastmode)
- File: ZetaProduct.lean:1084 · Discharge: PROVED — partition-by-value + leaf G + `Σ_{ζ^n=1} ζ = 0`.
- **Progress**:
  - 2026-06-05: PROVED. Partition `Σ_{N𝔞≤N} χ(𝔞)` by value `v ∈ {0} ∪ μ_n` (`n = orderOf χ ≥ 2`,
    fiberwise over `insert 0 (nthRootsFinset n 1)`), 0-fibre drops, per-fibre count from leaf G
    (`exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow`), leading term cancels via the new
    sorry-free helper `sum_nthRootsFinset_eq_zero` (mult-by-ζ₀ permutation; mathlib has only the
    geom-series form — upstream candidate). `C = orderOf χ · C'`. /cleanup ran (3 private helpers
    extracted, body 137→39 lines, all gates pass). Verified: lake env lean + axioms
    `[propext, sorryAx, Classical.choice, Quot.sound]` (sorryAx = the 2 intended deep gaps only;
    helpers sorry-free). Elaboration pitfall recorded: annotate `Finset.univ` type under `with`
    binders or `Fintype {𝔞 // ?p}` instance search whnf-times-out.
- The stale BLOCKED-NEXT B2 note (frobeniusClass.out junk-on-composites) was already resolved by
  the `galoisCharacterOnIdeal`/`frobeniusIdeal` defs (commit 8f33578) — see HANDOVER §6.

### [LF4] artinLSeries_analytic_extension — Status: done (2026-06-05, /beastmode)
- File: ZetaProduct.lean:~1320 · Depends on: LF3 (done) · Discharge: PROVED — Abel summation + Mellin.
- **Progress**:
  - 2026-06-05: restated at cyclotomic generality (m-threading through LF4/helper-ii/LF5/Cyclotomic
    prime-sum lemma; commit 1761fbe) — same CFT-free rationale as leaf G's expert-review restatement.
  - 2026-06-05: PROVED (commit 8f824c5, cleanup 69b8f8d). `Lf s := s · mellin S (-s)`,
    `S t = Σ_{k ≤ ⌊t⌋} galoisCharacterCoeff k`. Coefficient partial sums = LF3 sum (fibrewise
    regroup) ⟹ O(n^{1-1/d}); mathlib `LSeries_eq_mul_integral` (Roblot Abel summation) on
    `Re s > 1`; `mellin_differentiableAt_of_isBigO_rpow` ⟹ analytic on `Re s > 1 - 1/d`.
    Extracted `sum_idealNormMultiplicity_isBigO` (NumberFieldEulerProduct refactor). Axioms:
    sorryAx only via the 2 deep gaps; all structural helpers sorry-free. Verified lake env lean.

### [LF5] artinLSeries_one_ne_zero — Status: done (proven pre-2026-06-05; m-threaded 1761fbe)
- File: ZetaProduct.lean:2125 · sorry-free in-file (carries sorryAx only via LF4 → deep gaps).

### [LF6] exists_dedekindZeta_factorisation — Status: superseded (board-stale)
- Planned decl does not exist; its role is covered by `dedekindZeta_eq_prod_artinDirichletSeries`
  (ZetaProduct, proven) + LF5 used directly at the call sites.

### [LF7] exists_chebotarev_cyclotomic_residue_identity — Status: superseded (board-stale)
- Planned decl does not exist; covered by the proven Cyclotomic.lean chain
  (`sum_charTwist_eq/_ne`, `primeIdealZetaSum_frobeniusFibre_asymp`, `chebotarev_cyclotomic`).

### [LF8] log_artinLSeries_asymp_character_sum — Status: done (proven pre-2026-06-05)
- File: Cyclotomic.lean:135 · sorry-free in-file.

### [LF9] primeIdealZetaSum_frobeniusFibre_asymp — Status: done (proven pre-2026-06-05)
- File: Cyclotomic.lean:947 · sorry-free in-file (m-threaded call updated, commit 1761fbe).

### [LF10] liminf_density_S_sigma_ge_card_H_n_div_GH — Status: done modulo AB1
- File: Abelian.lean:181 · assembled sorry-free around `exists_cyclotomicCrossing_fibres` (= AB1).

### [LF11] H_n_over_H_lower_bound_via_prime_factorisation — Status: superseded (board-stale)
- Planned decl does not exist; covered by the proven `H_n_over_H_tends_to_one` chain in Abelian.lean.

### [LF12] liminf_ratio_ge_inv_card_G — Status: done modulo AB1
- File: Abelian.lean:523 · proven in-file; inherits AB1's sorryAx.

## The real remaining work (the 4 project sorries, 2026-06-05 after LF3+LF4)

### [GA] normLeOne_frontier_lipschitz (Gap A) — Status: in_progress (2026-06-05, /beastmode)
- File: ZetaProduct.lean:793 (sorry at 799) · Depends on: none · THE foundational deep gap.
- Statement: `frontier (normAtAllPlaces '' fundamentalCone.normLeOne K)` is covered by finitely
  many Lipschitz images of `[0,1]^{r-1}`, `r = #InfinitePlace K` — L1's `hlip` hypothesis shape.
- Source: Gun–Ramaré–Sivaraman JNT 243 (2023) §3.3 (Lemmas 5–8), after Debaene; mathlib has only
  the measure-zero form `volume_frontier_normLeOne`. Fresh mathlib-PR-scale development on
  `mixedEmbedding`/`fundamentalCone`/`logMap`/`expMapBasis`.

### [GB] exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le (Gap B = L2) — Status: open
- File: ZetaProduct.lean:831 (sorry at 842) · Depends on: GA + L1 (proven) · bad-prime split +
  congruence-coset lattice counting; see L2 docstring + HANDOVER §5.2 (U-predicate, import cycle §5.3).

### [AB1] exists_cyclotomicCrossing_fibres — Status: open
- File: Abelian.lean:148 (sorry at 157) · Depends on: chebotarev_cyclotomic (proven mod gaps) ·
  compositum `Gal(L(μ_m)/K) ≅ G × H` (linear disjointness, m coprime to disc(L)) + fixed-field
  density transfer. Sharifi 7.2.2 Step 2 pp. 143–144.

### [M1] chebotarev_density assembly — Status: open
- File: Main.lean:~1370 (sorry at 1375) · Depends on: AB1 chain + fixed-field reduction (Main.lean
  sub-lemmas) · Sharifi 7.2.2 Step 1 counting argument + assembly.
- Sketch: decomposition.md L12.
