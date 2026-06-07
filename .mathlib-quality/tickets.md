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

### [GB] exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le (Gap B = L2) — Status: done (2026-06-07)
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
    is proven FROM leaf G FROM L2. Non-circular source: Lang VI §3 (geometry only).
  - 2026-06-06 (later): bridge worker landed `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`
    (hS ⟹ hF) sorry-free MODULO one isolated core `cardNormLeResidue_density_const_of_realized`
    (κ-constancy over realized S). **THE CELL-LEVEL TRANSFER DESIGN THAT CLOSES IT (orchestrator,
    2026-06-06)**: per class C with rep J and realizer 𝔟 of t (N𝔟 coprime c AUTOMATIC — its
    residue is a unit): (1) the window bijection 𝔄 ↦ 𝔄𝔟 gives A_{C,x}(N) = A^{÷𝔟}_{C[𝔟],xt}(N·N𝔟)
    EXACTLY; (2) choosing the C[𝔟]-rep J' coprime to the primes over N𝔟 (rep-choice lemma, CRT)
    makes 𝔟J' + cNJ'·J' = J', so the finer-coset map (𝔟J')/(cNJ')(𝔟J') → J'/(cNJ')J' is
    BIJECTIVE and the 𝔟-divisible count is a (𝔟J')-divisor instance of the SAME geometric core
    with covol(𝔟J'-lattice) = N𝔟·covol(J'-lattice) ⟹ κ^{÷𝔟} = κ_full/N𝔟 EXACTLY (needs the
    explicit-κ cell-formula refinement R1a of the cone-point count + mathlib
    volume_fundamentalDomain_fractionalIdealLatticeBasis); (3) compose: κ_{C,x} = κ_{C[𝔟],xt};
    (4) reindex the class group (·[𝔟]) and sum: κ_x = κ_{xt}; (5) closure-induction over S.
    Worker a8a5264 dispatched with the full design.
  - The L2 ASSEMBLY (ZetaProduct): dictionary layer PROVEN (unramifiedIn_of_coprime_absNorm via
    the different ideal + conductor_mul_differentIdeal; autToPow_frobeniusIdeal; the good-fibre =
    residue-count Equiv; badPart/goodPart split with 6 proven helpers). Worker adf8e2ee dispatched
    on the remainder: σ-partition over bad parts, per-fibre Equiv, the coprime-restricted
    Frobenii-generation variant (bad-prime Frobenii are NOT norm-residues — μ_m doesn't inject
    mod 𝔓 when p ∣ m — so generation must be re-proven from coprime primes only, density
    argument unaffected by finitely many exclusions), Euler-tail bounds (iSup-based, no tsum;
    Finset.prod_sum expansion + geometric ≤ (1−x)⁻¹), d=1 ⟹ badPrimes = ∅ under hm (the one
    sanctioned fallback sorry if ℚ-cyclotomic ramification inputs resist).
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

### [DONE-2026-06-07] PROJECT MAIN LINE COMPLETE
- `chebotarev_density`, `chebotarev_density_of_comm`, `density_split_completely`,
  `dirichlet_primes_in_AP`, `chebotarev_abelian`, `chebotarev_cyclotomic`: ALL proven,
  axioms exactly [propext, Classical.choice, Quot.sound], zero sorries project-wide
  (independent cache-bypassing audit at commit c1eb32c; build green 3805 jobs).
- GB: closed via 8 ICC worker-layers + the ZetaProduct assembly (see HANDOVER §2).
- AB1: closed via the decomposition (master/C1-C5) — C2a via
  linearDisjoint_of_isGalois_isCoprime_discr; C5 by relocating Main's Step-1 block into
  the new module CebotarevDensity/FixedFieldDensity.lean.
- M-corollary `dirichlet_primes_in_AP`: closed (CyclotomicField n ℚ instantiation, the
  finite-symmDiff density transfer, the 2-mod-4 CRT reduction).

### [CL1] /cleanup campaign over the session's new code — Status: in progress
- **Done**: CyclotomicNormResidue (6 commits, 909→674 lines); Main batch 1 (file-level
  + 8 public theorems, −33 lines, 3 ConjClasses renames queued to renames.jsonl).
- **In flight** (2026-06-07): Main batch 2 (remaining 11 decls), LatticePointCount.
- **Queued**: Density, Frobenius, NumberFieldEulerProduct, LogOneDivSubOne,
  NormLeOneLipschitz, FixedFieldDensity, Cyclotomic, Abelian, ZetaProduct,
  ForMathlib/IdealCongruenceCount (largest last — fold in PROJECT_OVERVIEW.md's
  consolidation clusters A–C and the dead-code deletes for ICC).
- **Per-file riders from PROJECT_OVERVIEW.md Part 7** (verified dead code — delete in
  that file's batch): ZetaProduct (Dirichlet-test trio, normLeOne_frontier_lipschitz
  wrapper), ICC (exists_generator_diff_of_coset, exists_card_dvd_principal_residue_real_le),
  Cyclotomic (log_artinLSeries_asymp_character_sum), Abelian (gal_compositum_prod_iso,
  cyclic_subgroup_meets_G_times_one_trivially, H_n_over_H_tends_to_one — blueprint-linked,
  re-point chapter first —, chebotarev_abelian_lowerDensity_per_m, inline
  map_eq_of_isConj_comm), NFEP (insertPiEquiv → mathlib composition; verify
  tsum_symGeometric).
- **Type**: cleanup. Invoke /cleanup per file (full 10-phase workflow). Expect
  long-line/unused-variable warnings (a few pre-existing), naming-gate renames on
  worker-generated helper names, and structure-gate decomposition flags on the larger
  assembly proofs.
- **Orchestrator ruling (2026-06-07, binding for all CL1 workers)**: in-file
  `/-! ### Sub-lemmas for … -/` blocks and verbatim Sharifi/Stevenhagen–Lenstra
  citation blocks are CLAUDE.md-sanctioned ("Source quotes are binding"; the
  Sub-lemmas convention is documented there) and OVERRIDE the generic
  no-subsection-dividers style rule — keep them. Strippable: pure proof-strategy
  narration inside such a block, if separable from the citations.
- Depends on: nothing (main line done).

### [BP1] blueprint sync — Status: **done** (superseded by the verso migration, 2026-06-07)
- The LaTeX leanblueprint was migrated wholesale to verso-blueprint:
  `CebotarevBlueprint/Chapters/{Density,Frobenius,ZetaProduct,Cyclotomic,Abelian,Main}.lean`
  + `Blueprint.lean`, all 1:1 from blueprint/src. `lake build CebotarevBlueprint` green
  (0 warnings); HTML site generates to `_out/site/html-multi/` (index + dep-graph +
  summary: 72 completed entries, 0 sorries). Stale `\lean{}` refs repointed during
  migration (IsArithFrobAt, MulAction.stabilizer, Ideal.inertia, the le-orientation
  renames). The legacy `blueprint/src` LaTeX tree is now redundant — decide with Chris
  whether to delete it or keep it frozen.
- Residual (folds into CL1 per-file batches): `dedekind-zeta-factorisation` entry is
  Lean-unlinked (its decl `dedekindZeta_eq_prod_artinDirichletSeries` is private —
  re-link if made public); item (i)–(iv) content enrichment (hm-hypotheses prose, GB
  narrative chapter) can be incremental on the verso side.

### [UP1] mathlib-upstream candidates — Status: open
- Strongest candidates surfaced this session: sum_nthRootsFinset_eq_zero;
  normLeOne_frontier_lipschitz_cover (+ the mixedSpace lift); the ξ-uniform coset
  workhorse exists_card_coset_inter_smul_sub_volume_mul_rpow_le; the per-residue
  effective ideal count chain; exists_mk0_eq_absNorm_coprime (coprime class reps);
  the finite-symmDiff density transfer; subgroup_eq_top_of_forall_frobenius_mem(_of_coprime).
- From /overview (PROJECT_OVERVIEW.md Part 5, full ranked list there): LogOneDivSubOne
  (trivial first PR), the NLOL phase block (t ↦ e^{it} 1-Lipschitz; zero deps),
  LatticePointCount (whole file), the finite-abelian character cluster (G →* ℂˣ
  row/column orthogonality + prod_one_sub_nthRoots + prod_galoisCharacter_one_sub +
  charEval_ker_card), crt_single_coset, tendsto_div_atTop_of_sub_mul_rpow_le, and
  Main's three ConjClasses lemmas (carrier_card_eq_one_of_comm / carrier_card_pos /
  mk_one_carrier_card_eq_one — relocate to a root-namespace home so `ConjClasses.`
  dot-names are real; rename deferred in renames.jsonl pending that move).
- Depends on: CL1.

