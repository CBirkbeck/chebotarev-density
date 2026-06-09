# Cleanup campaign (2026-06-07/08) — findings & flags

Deep per-declaration `/cleanup` pass over every proven lemma, with an API-extraction lens.
Orchestrator + per-file (per-decl-range) workers. Statements byte-protected; axiom gate after
every commit (PASS 4/4 throughout).

## ForMathlib group — DONE (5/5 files)

| File | Lines | Net | Highlights |
|---|---|---|---|
| CharacterOrthogonality | 68→53 | −15 | shared `sum_eq_zero_of_mulLeft_mul_const_aux`; adopted `eq_zero_of_mul_eq_self_left` |
| LogOneDivSubOne | 69→~68 | ~0 | docstring completed; already optimal |
| LatticePointCount | 401→384 | −17 | 4 helpers extracted |
| NormLeOneLipschitz | 736→673 | −63 | `lipschitzWith_one_of_edist_apply_le` + frontier helper; adopted `lipschitzWith_circleMap` (38→6), `IsometryEquiv.piCongrLeft'`, projIcc edist API, `fun_prop` |
| IdealCongruenceCount | 3605→3461 | −144 | 8 helpers; adopted `Int.cast_det`, `image_smul_set`, `Basis.mem_span_iff_repr_mem`, `Submodule.map_span`, `isClosed_iInter`, `Nat.cast_sum`, `Finset.sum_eq_single_of_mem`, `Ideal.absNorm_eq_index`, `absNorm_pos_of_nonZeroDivisors`, `Module.Basis.coe_map`, `LinearEquiv.coe_trans`, `absNorm_eq_one_iff` |

~15 new reusable private helpers; ~17 mathlib lemmas newly adopted; ~240 net lines removed.

## /decompose-proof candidates (long bodies, irreducible after honest extraction)
- LatticePointCount: `abs_card_inter_sub_volume_mul_pow_le` (~82)
- ICC: `ncard_index1_image_smul_chart_le` (~80), `abs_cardR_translate_sub_volume_le` (~82),
  `exists_card_fibre_dvd_eq_card_cell` (~106), `exists_card_fibre_dvd_residue_sub_mul_rpow_le` (~63),
  `exists_card_residue_fibre_sub_mul_rpow_le_explicit` (29-line branch)

## mathlib UPSTREAM candidates (confirmed absent via 5-method search; sorry-free, general)
- `tendsto_ratio_one_of_div_atTop_pm_bounded` (generic ratio squeeze) — PR material already prepared
  in worktree `mathlib4-up1` (branch up1-log-limits) as `tendsto_div_atTop_nhds_one_of_bdd_sub`; SHELVED
- CharacterOrthogonality lemmas (restate via `AddChar`/`Multiplicative` bridge for mathlib)
- `lipschitzWith_one_of_edist_apply_le` (pi-coordinatewise 1-Lipschitz); the phase block
  (`dist_mul_le_norm_mul_dist`, `dist_mul_exp_phase_le`)
- ICC: `exists_card_coset_inter_smul_sub_volume_mul_rpow_le` (Widmer/GRS coset count),
  `prod_eq_neg_one_pow_card_mul_prod_abs`, `norm_eq_prod_real_emb_mul_prod_complex`,
  `tendsto_div_atTop_of_sub_mul_rpow_le`, `crt_single_coset`, `exists_mk0_eq_absNorm_coprime`,
  `Nat.le_iff_le_mul_div_of_dvd`, `absNorm_coprime_of_isCoprime_span`, `exists_sub_mul_rpow_le_of_div`

## cross-file / refactor opportunities (NOT yet applied)
- ICC `cardNormLeResidue_density_eq_of_mem_subgroup`: a general finite-abelian Fourier-inversion ⟹
  constant fact is inlined here; belongs in `CharacterOrthogonality.lean` as reusable API.
- ICC `exists_card_fibre_dvd_eq_card_cell` ≈95% identical to `card_fibre_eq_card_cell` — a shared
  helper would dedup ~30 lines (cross-block, needs editing both).
- Grep main files (Frobenius etc.) for hand-rolled `absNorm = index` / `absNorm > 0` to adopt
  `Ideal.absNorm_eq_index` / `absNorm_pos_of_nonZeroDivisors`.
- NormLeOneLipschitz `dist_mul_le_norm_mul_dist`: `NormedField` → `NormedDivisionRing` (borderline).

## Remaining: 9 MAIN files (332 decls) — NOT upstream-bound
Density(40), NumberFieldEulerProduct(40), Frobenius(21), CyclotomicNormResidue(16),
ZetaProduct(107), Cyclotomic(24), FixedFieldDensity(19), Abelian(43), Main(22).
