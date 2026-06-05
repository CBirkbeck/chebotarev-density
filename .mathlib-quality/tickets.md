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

### [LF4] artinLSeries_analytic_extension — Status: open
- File: ZetaProduct.lean:232 · Depends on: LF3(sorried) · Discharge: project + Lemma 7.1.5 (verify mathlib `LSeries.abscissaOfAbsConv`)
- Sketch: decomposition.md L4 — partial-sum bound (LF3) ⟹ Dirichlet series converges on `Z(1-1/d)`.

### [LF5] artinLSeries_one_ne_zero — Status: open
- File: ZetaProduct.lean:252 · Depends on: LF4 · Discharge: project (pole-order, Sharifi 7.1.19 step 2)
- Sketch: decomposition.md L5 — `log ζ_L=Σ_χ log L_χ`; vanishing factor over-cancels ζ_L simple pole ⟹ all `m_χ=0`.

### [LF6] exists_dedekindZeta_factorisation — Status: open
- File: ZetaProduct.lean:277 · Depends on: LF1, LF2, LF5 · Discharge: project assembly
- Sketch: decomposition.md L6 — package factorisation + `L_1=ζ_K` + non-vanishing.

### [LF7] exists_chebotarev_cyclotomic_residue_identity — Status: open
- File: ZetaProduct.lean:293 · Depends on: LF6 · Discharge: project (orthogonality + L8 + LF5)
- Sketch: decomposition.md L7 (Prop 7.2.1).

### [LF8] log_artinLSeries_asymp_character_sum — Status: open
- File: Cyclotomic.lean:135 · Depends on: LF1 · Discharge: project (mirror `log_dedekindZeta_re_eq_tsum_neg_log_one_sub`)
- Sketch: decomposition.md L8 — `log L(χ,s) ~ Σ_𝔭 χ(𝔭)N𝔭⁻ˢ`.

### [LF9] primeIdealZetaSum_frobeniusFibre_asymp — Status: open
- File: Cyclotomic.lean:227 · Depends on: LF8, LF5 · Discharge: project (orthogonality assembly → density 1/|G|)
- Sketch: decomposition.md L9.

### [LF10] liminf_density_S_sigma_ge_card_H_n_div_GH — Status: open
- File: Abelian.lean:125 · Depends on: chebotarev_cyclotomic · Discharge: project (cyclotomic crossing)
- Sketch: decomposition.md L10 (Thm 7.2.2 Step 2).

### [LF11] H_n_over_H_lower_bound_via_prime_factorisation — Status: open
- File: Abelian.lean:143 · Depends on: none · Discharge: project (elementary `(ZMod m)ˣ` order count)
- Sketch: decomposition.md L11.

### [LF12] liminf_ratio_ge_inv_card_G — Status: open
- File: Abelian.lean:448 · Depends on: LF10, H_n_over_H_tends_to_one(proven) · Discharge: project assembly
- Sketch: decomposition.md L12.
