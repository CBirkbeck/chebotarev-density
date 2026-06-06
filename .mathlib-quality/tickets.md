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

### [GA] normLeOne_frontier_lipschitz (Gap A) — Status: done (2026-06-06, /beastmode)
- File: ZetaProduct.lean (discharged) ⟸ ForMathlib/NormLeOneLipschitz.lean (the development).
- **Progress**:
  - 2026-06-06: PROVED sorry-free + axiom-clean `[propext, Classical.choice, Quot.sound]`
    (commits f4e305a + 414da77 + 5e3ad0a). Architecture: mathlib's
    `normAtAllPlaces '' normLeOne = expMapBasis '' paramSet` (Roblot); frontier ⊆ image of box
    boundary ∪ {0} (openness + injectivity + compactSet); each face cube-parametrized — the
    `t = exp(x w₀)` substitution linearizes the unbounded `Iic 0` direction, `t` taking the cube
    slot freed by pinning `x i = a`, `t = 0` absorbing `{0}`; C¹ face maps Lipschitz on the cube
    (`LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`) made global by the 1-Lipschitz
    `clampUnit`; assembly over `Unit ⊕ Unit ⊕ ({w ≠ w₀} × Bool)` with the `equivFinRank`
    relabeling isometry. Future-mathlib-PR material. /cleanup ran (body 79→7, helpers extracted).

### [GB] exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le (Gap B = L2) — Status: in_progress
- File: ZetaProduct.lean (sorry at ~846) · ALL INPUTS PROVEN as of 2026-06-06 except one:
  - DONE sorry-free: coset workhorse; mixed-space GA-lift; index-transport; per-residue effective
    ideal count `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le` (axiom-clean!);
    CyclotomicNormResidue.lean (norm-residue dictionary + Frobenii-generate).
  - LAST ICC sorry: `cardNormLeResidue_density_eq_of_mem_subgroup` (the κ-transfer core).
    **Route F (FINAL DESIGN, 2026-06-06):** restate with an S-character coset-translate decay
    hypothesis `hF : ∀ χ : S →* ℂˣ, χ ≠ 1 → ∀ w, Tendsto (Σ_{s ∈ S} χ(s)·count_{w·s}(N)/N) → 0`;
    prove by S-internal finite-abelian Fourier inversion (separating character + translation
    trick, `Mathlib.GroupTheory.FiniteAbelian.Duality`); thread hF into `_uniform` (conclusion
    unchanged). Consumer discharges hF via PROVEN LF3 + `autToPow_frobeniusClass_out`.
    DISCARDED routes (lossy/walled — do not retry): ideal-multiplication limit transfer (N𝔟
    factor); element-orbit permutation (S ⊄ unit-norm-residues from ideal realizers).
    ⚠ CIRCULARITY (2026-06-06, caught pre-assembly): hF CANNOT be discharged via LF3 — LF3
    is proven FROM leaf G FROM L2 (the statement being assembled). The non-circular source is
    Lang VI §3 Thm 3 (per-ray-class counts; covolume cancellation covol(Λ_J) = N(J)·covol₀
    makes the per-cell constant class-independent; fibres of the ray-class→residue group hom
    are equinumerous). Bridge worker dispatched: `hS ⟹ hF` in ICC (pure geometry of numbers
    + finite group theory; two candidate routes — per-class κ-refinement, or the direct
    unit-orbit twisted-cell-sum argument; ℚ(i)/c=5 sanity passes via local norm surjectivity
    on split primes).
    ⚠ 3 consecutive worker dispatches died to API-529 overload (0 work done each, tree clean
    at e57e823) — retry the dispatch when capacity returns; the full worker brief is in the
    session transcript and reconstructible from this note.
  - 2026-06-06 (late): **IdealCongruenceCount.lean fully sorry-free** — κ-uniformity proven via
    Fourier inversion (Route F, in-session after 4 dispatch deaths to API overload); `_uniform`
    takes the hF Fourier-decay hypothesis (consumer discharges via LF3 + autToPow). Axioms clean.
  - ⚠ **B2 LOGGED (8d46789): the L2 statement (and leaf G, LF3) are FALSE at the degenerate
    corner `K = ℚ (d=1), m ≡ 2 mod 4`** — infinite 2-power bad parts contribute Θ(log N) total
    error vs the claimed O(N⁰); CRT-alignment counterexample in b2_log.jsonl. TRUE for d ≥ 2 and
    for d=1 with m ≢ 2 mod 4 (bad set empty). **REPAIR (mechanical): thread `hm : m % 4 ≠ 2`
    through L2 → leaf G → LF3 → LF4 → artinDirichletSeries_norm_le_of_ne_one → LF5 →
    Cyclotomic consumers** (chebotarev_cyclotomic chain); the Abelian m-choosers pick
    `m ≡ 1 mod lcm(4, n^k)` prime via Dirichlet-in-AP (mathlib PrimesInAP), so every use
    survives; the corner is mathematically redundant (`ℚ(μ_m) = ℚ(μ_{m/2})`).
  - THEN the assembly (ZetaProduct:846, with hm): (1) import ICC + CyclotomicNormResidue into
    ZetaProduct; (2) bad-prime split: bad primes = {𝔭 unram, N𝔭 not coprime m} FINITE (divisors
    of m); bad-supported parts 𝔟 = products of bad primes — the 𝔟-tail Σ N𝔟^{-(1-1/d)}
    converges for d ≥ 2; for d = 1 with hm the bad set is EMPTY (K=ℚ: a p ∣ m unramified in
    ℚ(μ_m) forces p = 2 ∧ 2∥m, excluded) — case split d=1/d≥2 or handle uniformly via the
    convergent-tail argument with the d=1-empty observation; (3) per fixed 𝔟: good-part fibre =
    norm-residue class via autToPow_frobeniusClass_out + frobeniusIdeal_mul (Frobenius shifts);
    (4) per-residue counts from ICC `_uniform` with S := the image of the cyclotomic character
    (range of autToPow ∘ Frob — equals the full character image by
    subgroup_eq_top_of_forall_frobenius_mem), hF discharged via LF3
    character_sum_geometry_of_numbers_bound pulled back along autToPow (the twisted coset sums
    = galoisCharacterOnIdeal partial sums up to the FINITE bad-prime corrections — same split);
    (5) κ independent of g since the residue-fibre is a single class χ_cyc(g) and `_uniform`
    gives one κ across the image subgroup; sum the 𝔟-tail.

### [AB1] exists_cyclotomicCrossing_fibres — Status: open (⚠ statement review FIRST)
- File: Abelian.lean:148 (sorry at 157) · Depends on: chebotarev_cyclotomic (proven mod gaps) ·
  compositum `Gal(L(μ_m)/K) ≅ G × H` (linear disjointness, m coprime to disc(L)) + fixed-field
  density transfer. Sharifi 7.2.2 Step 2 pp. 143–144.
- **⚠ Adversarial statement analysis (2026-06-06, pre-attack):** the statement quantifies over ALL
  `m ≥ 1` with NO disjointness hypothesis, but the intended proof needs `L ∩ K(μ_m) = K`
  (`Gal(L(μ_m)/K) ≅ G × H` FAILS otherwise — e.g. `K(μ_m) ⊆ L`); for bad `m` the
  exact-density-`1/(|G||H|)` fibres are not produced by the compositum route (whether the bare
  existence survives via density interpolation is doubtful-to-formalize). Sharifi's proof CHOOSES
  `m ≡ 1 mod n^k` PRIME (Dirichlet primes-in-AP — mathlib HAS it,
  `Mathlib.NumberTheory.LSeries.PrimesInAP`), hence coprime to `disc L`. EXPECTED FIX before
  proving: add a disjointness/coprimality hypothesis to AB1 (and thread through LF10
  `liminf_density_S_sigma_ge_card_H_n_div_GH` + the `m`-chooser in `chebotarev_abelian`'s proof,
  which must pick `m` prime large via Dirichlet-in-AP — check `H_n_over_H_tends_to_one`'s
  compatibility with restricting to prime `m ≡ 1 mod n^k`). Do the restatement cascade FIRST,
  then the compositum infrastructure (M = L(μ_m) as `IsCyclotomicExtension {m} L M` +
  `Gal(M/K) ≃* G × H` via restriction-product, injectivity from disjointness, surjectivity by
  order; per-(σ,τ) fixed field F + `chebotarev_cyclotomic` at M/F + `density_lift_through_fixedField`).

### [M1] chebotarev_density assembly — Status: open
- File: Main.lean:~1370 (sorry at 1375) · Depends on: AB1 chain + fixed-field reduction (Main.lean
  sub-lemmas) · Sharifi 7.2.2 Step 1 counting argument + assembly.
- Sketch: decomposition.md L12.
