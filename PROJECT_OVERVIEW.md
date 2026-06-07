# Project Overview: chebotarev-density

Generated: 2026-06-07 (post-completion review — the main theorem `Chebotarev.chebotarev_density`
is fully proven, zero sorries project-wide, axiom-clean at `[propext, Classical.choice, Quot.sound]`).

Full per-declaration inventories (every declaration, with What/How/Hypotheses/Uses/Used-by):
`.mathlib-quality/overview/<File>.md` — one file per module, 13 files. This document is the
Phase-2 synthesis over those inventories.

## Executive Summary

The project is a CFT-free Lean 4/Mathlib formalisation of Chebotarev's density theorem
(conjugacy-class form, Dirichlet density), following Sharifi §7.1–7.2 / Stevenhagen–Lenstra.
The proof pipeline is: Dirichlet density + `ζ_K` log-asymptotics (`Density`), arithmetic
Frobenius via mathlib's `IsArithFrobAt` (`Frobenius`), the abelian factorisation
`ζ_L = ∏_χ L(χ,·)` + non-vanishing `L(χ,1) ≠ 0` (`NumberFieldEulerProduct` + `ZetaProduct`),
the cyclotomic case (`Cyclotomic`), the compositum crossing (`Abelian`), the fixed-field
reduction (`FixedFieldDensity`), and the capstone + corollaries (`Main`, including Dirichlet
primes-in-AP). The analytic deep end — effective geometry-of-numbers equidistribution of
Frobenius fibres — lives in `ForMathlib/` (`LatticePointCount`, `NormLeOneLipschitz`,
`IdealCongruenceCount`).

Key findings of this review: (1) the project's definitional choices are sound — `UnramifiedIn`
and `frobeniusClass` are built directly on mathlib's `Algebra.IsUnramifiedAt` / `IsArithFrobAt`,
`HasDirichletDensity` has no mathlib counterpart, and mathlib's `dedekindZeta` is consumed
rather than duplicated; (2) there is a stratum of **dead code** (~400 lines across 10
declarations) left by superseded proof routes, all safe deletes; (3) the deepest file
(`IdealCongruenceCount`, 56 declarations) carries visible **worker-layer redundancy** — two
complete proofs of the L2 divisible-density fact, implicit/explicit-constant twin lemmas, and
a 40-line region-membership block duplicated verbatim — consolidation would remove ~300–400
lines; (4) four `ForMathlib` units plus several self-contained lemma clusters are genuine
**mathlib-PR candidates** (effective lattice-point count, Lipschitz frontier covers, the
`t ↦ e^{it}` Lipschitz block, character orthogonality for `G →* ℂˣ`).

## Statistics

- Source files: 13 modules (9 main + 4 `ForMathlib/`), 16 474 lines total.
- Declarations: ≈ 350 (16 Frobenius, 36 Density, 25 NFEP, 20 CNR, ~73 ZetaProduct,
  20 Cyclotomic, 43 Abelian, 18 FixedFieldDensity, 19 Main, 56 ICC, 6 LPC, 2 LOSO, 31 NLOL).
- `sorry`: **0**. `axiom`: **0**. `def := sorry`: **0**.
- `set_option` overrides: 8 project-wide (5 `maxHeartbeats` in ZetaProduct, 1 in ICC
  `backward.isDefEq.respectTransparency`, 2 `linter.unusedFintypeInType`).
- Confirmed-dead declarations: 10 (~400 lines). Moral duplications: 6 clusters.
- Mathlib-PR candidate units: 7.

---

## Part 1: Declaration Inventory

Per-file inventories with full per-declaration entries are in
`.mathlib-quality/overview/`:

| File | Decls | Lines | Role | Health |
|---|---|---|---|---|
| `Density.lean` | 36 | ~900 | Dirichlet density + `Σ N𝔭^{-s} ~ log 1/(s-1)` | clean; no dead code |
| `ForMathlib/LogOneDivSubOne.lean` | 2 | 58 | `log(1/(s-1)) → ∞` + ratio squeeze | upstream candidate |
| `NumberFieldEulerProduct.lean` | 25 | ~1000 | `ζ_K` Euler products (plain + χ-weighted) | unweighted ⊂ weighted (dedup candidate) |
| `Frobenius.lean` | 16 | ~450 | `UnramifiedIn`, `frobeniusClass` on `IsArithFrobAt` | clean |
| `CyclotomicNormResidue.lean` | 20 | 674 | `autToPow`-Frobenius dictionary | CL1-cleaned; 4 helpers replicated from ZetaProduct (Cluster G) |
| `ZetaProduct.lean` | ~73 | 3598 | `ζ_L = ∏ L_χ`, leaf-G fibre counts, `L(χ,1) ≠ 0` | 4 dead decls; 5 maxHeartbeats |
| `Cyclotomic.lean` | 20 | 1034 | cyclotomic Chebotarev | 1 dead decl |
| `Abelian.lean` | 43 | 1751 | compositum crossing + `H_n` ratio | 4 dead decls |
| `FixedFieldDensity.lean` | 18 | ~1226 | fixed-field density lift | clean, single export |
| `Main.lean` | 19 | ~530 | capstone + corollaries + Dirichlet AP | clean |
| `ForMathlib/LatticePointCount.lean` | 6 | ~420 | unit-grid effective count (L1 core) | upstream candidate |
| `ForMathlib/NormLeOneLipschitz.lean` | 31 | 766 | Lipschitz frontier covers of `normLeOne` | upstream candidate |
| `ForMathlib/IdealCongruenceCount.lean` | 56 | ~4350 | Widmer count → κ-transfer → Fourier | heavy redundancy (below) |

## Part 2: Cross-File Dependencies

Import DAG (project-internal):

```
ForMathlib/LogOneDivSubOne ──→ Density ──→ Frobenius ──→ CyclotomicNormResidue
NumberFieldEulerProduct  ───→ Density
ForMathlib/LatticePointCount ─→ ForMathlib/IdealCongruenceCount ←─ ForMathlib/NormLeOneLipschitz
{Frobenius, CNR, ICC, LPC, NLOL} ──→ ZetaProduct ──→ Cyclotomic ──→ {FixedFieldDensity, Abelian}
{Cyclotomic, FixedFieldDensity} ──→ Abelian ──→ Main ←── FixedFieldDensity
```

Load-bearing cross-file exports (consumer counts from the inventories):

- `Density`: `HasDirichletDensity` (+upper/lower), `primeIdealZetaSum` API,
  `logDedekindZeta_sub_log_inv_sub_one_bounded`, `primeIdealZetaSum_univ_tendsto_log` —
  consumed by Frobenius/Cyclotomic/Abelian/FixedFieldDensity/Main.
- `Frobenius`: `UnramifiedIn` (+`.ne_bot`, `.ramificationIdx_eq_one`), `frobeniusClass`
  (+`_eq_mk_of_isArithFrobAt`), `finrank_residue_eq_orderOf`,
  `card_primesAbove_mul_orderOf_eq`, `finite_ramifiedIn` — pervasive downstream.
- `NFEP`: `NonzeroIdeal`, `idealNormMultiplicity`, `weighted_eulerProduct_eq_tsum`,
  `dedekindZeta_eq_tprod_primeIdeal`, `hasSum_nonzeroIdeal_absNorm_cpow`,
  `dedekindZeta_re_pos_of_one_lt` — ZetaProduct is the heaviest consumer.
- `CNR`: `autToPow_frobeniusClass_out`, `subgroup_eq_top_of_forall_frobenius_mem_of_coprime`
  — consumed by ZetaProduct (realized residues) and Main (Dirichlet AP).
- `ICC`: `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le[_uniform]`,
  `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized` — consumed at
  `ZetaProduct.lean:1612-1613` (the Gap-B engine handoff).
- `NLOL`: `normLeOne_frontier_lipschitz_cover[_index]` — consumed by ICC (3 sites).
- `ZetaProduct`: `artinLSeries_analytic_extension`, `artinLSeries_one_ne_zero`,
  `exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le` (L2),
  `character_sum_geometry_of_numbers_bound` — consumed by Cyclotomic.
- `Cyclotomic`: `chebotarev_cyclotomic`, `chebotarev_cyclotomic_lowerDensity_ge` — consumed
  by Abelian and Main.
- `FixedFieldDensity`: `density_lift_through_fixedField` (single terminal export) — consumed
  by Main:112 and Abelian:640.
- `Abelian`: `chebotarev_abelian` — consumed by Main.

## Part 3: Mathlib API Audit

**Verdicts on every project definition** (search methods: local mathlib grep at the pinned
rev + the project's own delegation history):

| Definition | Verdict | Evidence |
|---|---|---|
| `HasDirichletDensity`/`Upper`/`Lower` (Density) | **KEEP — novel** | No `DirichletDensity` anywhere in mathlib. Formulated via `Filter.Tendsto` on `𝓝[>] 1` (API-rich choice). |
| `primeIdealZetaSum` (Density) | KEEP | Plain `tsum` wrapper with the project's asymptotics; nothing comparable in mathlib. |
| `UnramifiedIn` (Frobenius) | **KEEP — already mathlib-aligned** | Defined as `𝔭 ≠ ⊥ ∧ ∀ 𝔓 maximal over 𝔭, Algebra.IsUnramifiedAt (𝓞 K) 𝔓`; same shape as mathlib's `NumberField.not_dvd_discr_iff_forall_liesOver`. |
| `frobeniusClass` (Frobenius) | **KEEP** | `Classical.choose` over `exists_frobeniusClass`, itself built on mathlib `IsArithFrobAt` (`RingTheory/Frobenius.lean`). Conventions-compliant (no placeholder, no axiom). |
| `dedekindZeta` | **Not a project def** — mathlib's `NumberField.dedekindZeta` is consumed. NFEP/Density add the Euler product, ideal-sum form, positivity, and log-asymptotic on top — none in mathlib (`Mathlib/NumberTheory/NumberField/DedekindZeta.lean` has only the residue limit). **Upstream candidates.** |
| `NonzeroIdeal` (NFEP) | **FLAG — encoding split** | `{I // I ≠ ⊥}` here vs `(Ideal (𝓞 K))⁰` (nonZeroDivisors) in ICC/ZetaProduct vs raw `{𝔞 // 𝔞 ≠ ⊥ ∧ …}` subtypes in ZetaProduct. Three encodings of one concept; `(Ideal _)⁰` is the mathlib-idiomatic one. See Part 4. |
| `idealNormMultiplicity` (NFEP) | KEEP | Counting function `#{I : N(I) = n}`; no mathlib counterpart. |
| `insertPiEquiv` (NFEP, private) | **REPLACE** | Exactly `(Equiv.piCongrLeft' _ (Finset.subtypeInsertEquivOption h)).trans (Equiv.piOptionEquivProd …)` — both pieces exist (`Data/Finset/Insert.lean:531`, `Logic/Equiv/Basic.lean:44`). Deletes ~25 lines + 2 simp lemmas. |
| `galoisCharacter`, `galoisCharacterOnIdeal`, `frobeniusIdeal`, `galoisCharacterCoeff`, `artinDirichletSeries` (ZetaProduct) | KEEP | Ideal-level Hecke-character data; mathlib's `DirichletCharacter` is `ZMod`-only. The completely-multiplicative-extension pattern (product over `normalizedFactors`) is the standard design. |
| `charEval` (ZetaProduct, private) | KEEP | Thin wrapper over mathlib `CommGroup.monoidHomMonoidHomEquiv`; used 3×. |
| `badPart`/`goodPart`/`IsBadPart`/`realizedResidues` (ZetaProduct, private) | KEEP | Proof-local notions of the L2 bad-part partition. |
| `twistedPrimeSum` (Cyclotomic, private) | KEEP | χ-twisted prime sum, proof-local. |
| `cardNormLeResidue`/`Class`/`ClassDvd` (ICC, private) | KEEP | Count abbreviations (real `Nat.card` defs). |
| `clampUnit` (NLOL) | **SIMPLIFY** | `= fun c i => (Set.projIcc 0 1 zero_le_one (c i) : ℝ)`. Mathlib has `LipschitzWith.projIcc` (`Topology/MetricSpace/Lipschitz.lean:199`), `projIcc_of_mem` — replaces `clampUnit_mem_Icc`/`clampUnit_eq_self`/`lipschitzWith_clampUnit` bodies. Low priority (the file is upstream-bound anyway; mathlib reviewers will ask for this). |
| `faceMapZero`/`faceMapSide`/`cubeRelabel`/`frontierCoverFamily`/`mixedCubeEquiv`/`liftToMixed` (NLOL) | KEEP | Genuine new constructions over mathlib's `expMapBasis`/`paramSet` parametrization. |

**Hand-rolled patterns audit** (Step 4d): the project is largely clean — limits are
`Filter.Tendsto`, sums are `tsum`/`HasSum`, products `HasProd`/`Multipliable`, Lipschitz via
`LipschitzWith`, counts via `Nat.card` + explicit `Equiv`s. Two observations:

1. **Character orthogonality is hand-rolled 3×** (see Part 4, cluster D). Mathlib has
   `AddChar` orthogonality over ℂ (`Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean`:
   `AddChar.sum_apply_eq_zero_iff_ne_zero`) and `MulChar.sum_eq_zero_of_ne_one` (finite
   fields). The project's `G →* ℂˣ` versions are not literally in mathlib, but
   `sum_nthRootsFinset_eq_zero` (ZetaProduct:2325) is morally
   `IsPrimitiveRoot.geom_sum_eq_zero` transported along the powers-enumerate-roots bijection
   — worth one consolidation pass, and the `G →* ℂˣ` row/column orthogonality pair is itself
   a small mathlib PR.
2. `prod_one_sub_nthRoots` (ZetaProduct:333, `∏_{ζ^f=1} (1 - ζY) = 1 - Y^f`) — no mathlib
   counterpart found; clean PR candidate alongside `prod_galoisCharacter_one_sub`.

## Part 4: Moral Duplications

**Cluster A — ICC: two complete proofs of L2** (the `𝔟`-divisible density
`κ_div = κ_full / N(𝔟)`):

- `cardNormLeResidueClassDvd_div_density` (ICC:3758, geometric Route-B/CRT — the deep proof)
- `cardNormLeResidueClass_div_density` (ICC:4133, one line from the effective kernel)

They state the **same conclusion**. The wiring is: geometric-L2 → `tendsto_…_div_transfer` →
kernel (`cardNormLeResidueClassDvd_sub_mul_rpow_le`) → kernel-L2 →
`cardNormLeResidueClass_density_transfer`. Re-pointing `cardNormLeResidueClass_density_transfer`
at the geometric L2 directly makes the 3-declaration chain
{`tendsto_cardNormLeResidueClass_div_transfer`, `cardNormLeResidueClassDvd_sub_mul_rpow_le`,
`cardNormLeResidueClass_div_density`} dead (~250 lines), **unless** the effective (kernel)
form is wanted as future API. **Action**: consolidate to ONE L2 statement; keep the effective
kernel only if upstreaming wants effective error terms (it does — Widmer-style statements are
effective; alternative action: delete the *geometric* density wrapper and keep the kernel as
the single L2, deriving the density form once).

**Cluster B — ICC: implicit/explicit-constant twins**:
`exists_card_cell_sub_mul_rpow_le` vs `…_explicit`; `exists_card_residue_fibre_sub_mul_rpow_le`
vs `…_explicit`. The implicit form is a 2-line `obtain` from the explicit one. **Action**:
derive implicit from explicit (or inline), −2 declarations, ~150 lines.

**Cluster C — ICC: copy-pasted proof blocks**:
- the ~40-line `hreg` orthant/region-membership block appears verbatim in
  `card_fibre_eq_card_cell` and `exists_card_fibre_dvd_eq_card_cell` → extract a private
  region-equivalence lemma;
- the cell-partition logic appears inline in `exists_card_idealSet_residue_le` and
  `…_real_le` *and* extracted as `card_idealSet_residue_eq_sum_cell` → retrofit both inline
  copies onto the extracted lemma (note `…_le` and `…_real_le` are themselves twins — the
  `N·NJ`-coupled one is the `s := N·NJ` instance of the decoupled one);
- the residue-constancy block appears inline in `exists_card_residue_fibre_sub_mul_rpow_le`
  and extracted as `residue_fibre_const_aux` → retrofit.

**Cluster D — character orthogonality, 3 implementations across 2 files**:
`sum_char_apply_eq_zero_of_ne_one` (ICC:1958, column), `sum_char_self_eq_zero_of_ne_one`
(ICC:2149, row), `sum_galoisCharacter_eq_card_or_zero` + `character_orthogonality_*`
(Cyclotomic). All instances of finite-abelian `G →* ℂˣ` orthogonality, each re-proving the
translation-reindexing trick. **Action**: one shared pair (row + column) in a small
`ForMathlib/CharacterOrthogonality.lean`, consumed by both; mathlib PR thereafter.

**Cluster E — NFEP: unweighted ⊂ weighted Euler product**:
`dedekindZeta_eq_tprod_primeIdeal` (~90 lines) is morally `weighted_eulerProduct_eq_tsum`
(~95 lines) at `w ≡ 1` (its proof duplicates the injection/membership blocks). **Action**:
derive the unweighted theorem from the weighted one at the trivial weight; −~70 lines.

**Cluster F — Abelian: `map_eq_of_isConj_comm`** = mathlib's
`isConj_iff_eq.mp (f.map_isConj h)` (exactly the composition found during the CNR cleanup).
Single consumer (`exists_crossing_family_tagged:836`). **Action**: inline, delete the lemma.

**Cluster G — CNR ↔ ZetaProduct: four replicated finiteness helpers.**
`CyclotomicNormResidue.lean:337–425` carries `'`-suffixed verbatim copies of ZetaProduct's
`exists_prime_dvd_natCast_mem`, `exists_primeFactor_natCast_mem_of_not_coprime`,
`finite_primes_natCast_mem`, `finite_badPrimes` (CNR sits *below* ZetaProduct in the import
DAG, so it could not import them). `isArithFrobAt_restrictNormal` (CNR) likewise mirrors
`arithFrobAt_restrictScalars_eq` (FixedFieldDensity) in the opposite direction
(restriction vs extension — related but not identical). **Action**: hoist the four
finiteness helpers into `Frobenius.lean` (both consumers import it); drop both copies.
~90 lines deduplicated. Also note: CNR's `subgroup_eq_top_of_forall_frobenius_mem`
(the `m = 1` headline wrapper) has **no live caller** — only the `_of_coprime` variant is
consumed (`ZetaProduct.lean:1403`). Keep (2-line intentional headline export,
blueprint-cited) but record the fact.

## Part 5: Generalization / Upstreaming Opportunities

Ranked by mathlib value (all are sorry-free, axiom-clean today):

1. **`ForMathlib/LatticePointCount.lean`** (whole file, 6 thms) — effective unit-grid
   lattice-point count `|#(R ∩ ℤ^d) − vol R| ≤ C(d,M,m)·…` for Lipschitz-bounded frontiers.
   Generic over `ι` finite; no number-field content. Target: `Mathlib/Analysis/…/Lattice…`.
2. **ICC `exists_card_coset_inter_smul_sub_volume_mul_rpow_le`** — Widmer/GRS-form coset
   count `#((ξ + TΛ) ∩ tD) = vol D/|det T|·t^d + O_ξ-uniform(t^{d-1})`. Together with (1),
   this is the citable "Theorem 3 of GRS". Needs (1) + ICC's private chart helpers only.
3. **`ForMathlib/NormLeOneLipschitz.lean`** — the Lipschitz frontier cover of `normLeOne K`;
   the module docstring already frames it as a mathlib PR onto
   `NumberField.CanonicalEmbedding.NormLeOne`. The phase block
   (`lipschitzWith_exp_ofReal_mul_I`, `lipschitzWith_phase`, `exists_phase_mem_Icc_mul_exp`)
   is a standalone zero-dependency PR (`t ↦ e^{it}` is 1-Lipschitz; polar form with phase in
   `[0,1]`).
4. **`ForMathlib/LogOneDivSubOne.lean`** — two `Filter`-level lemmas, root namespace already.
5. **Character orthogonality for `G →* ℂˣ`** (after Cluster-D consolidation) + `charEval_ker_card`
   (`#ker(eval_σ) = #G / ord σ`) + `charFibre_mem_range`/`card_charFibre_eq_card_ker` —
   finite-abelian character theory; generalizes from `Gal(L/K)` to any finite `CommGroup`
   with `HasEnoughRootsOfUnity` (the ZetaProduct proofs already work at that generality —
   they are *stated* for `G` generic, only used at Galois groups).
6. **`prod_one_sub_nthRoots` / `prod_galoisCharacter_one_sub`** — the Sharifi-7.1.16
   character-product identity `∏_χ (1 − χ(σ)Y) = (1 − Y^f)^{#G/f}`, again finite-abelian
   generic.
7. **ICC `tendsto_div_atTop_of_sub_mul_rpow_le`** (effective bound ⟹ density limit) and
   `crt_single_coset` (CRT for nested lattices with coprime index) — small generic lemmas.
8. **NFEP Euler-product infrastructure** — the ideal-indexed (vs ℕ-indexed) Euler product
   `ζ_K = ∏_𝔭 (1−N𝔭^{-s})^{-1}` and its χ-weighted form, on top of mathlib's new
   `NumberField.dedekindZeta`; plus `Density`'s `logDedekindZeta_sub_log_inv_sub_one_bounded`.

Generality check on the main theorems: number fields are `Type*` (universe-polymorphic),
`K`-`L` argument conventions follow the maintainers' `variable`-line rule, and the analytic
results are stated at the typeclass level they need (e.g. NFEP's
`norm_absNorm_cpow_neg_le_half` is already over any `[CommRing R] [IsDedekindDomain R]
[Module.Free ℤ R] [Module.Finite ℤ R]`). No further weakening found that mathlib would want.

## Part 6: API Improvements

1. **`clampUnit` via `Set.projIcc`** (NLOL) — see Part 3; replaces 3 lemma proofs.
2. **`insertPiEquiv` via `subtypeInsertEquivOption` + `piOptionEquivProd`** (NFEP) — see Part 3.
3. **`@[simp]` coverage**: `galoisCharacterOnIdeal_one`, `frobeniusIdeal_one`,
   `frobeniusIdeal_apply_prime`, `galoisCharacterCoeff_zero` are natural simp lemmas
   (currently used via explicit `rw`). Minor.
4. **Visibility tightening**: FixedFieldDensity exports 6 public theorems but only
   `density_lift_through_fixedField` is consumed externally — the 4 counting lemmas +
   `arithFrobAt_restrictScalars_eq` could be `private` (they are, however, milestone-named
   and blueprint-linked; keep public iff the blueprint cites them — it does).
   Same question for ZetaProduct's public middle layer (`exists_artinLSeries_eulerProduct_abelian`,
   `dedekindZeta_local_factor_eq_product_artin_local` are blueprint-cited milestones — keep).
5. **`set_option maxHeartbeats` debt** (5 sites, all ZetaProduct: 1600000×2, 800000×2 + the
   ~277-line `card_fibre_bound_two_le`): the /cleanup pass should attempt removal after the
   planned decompositions; `sum_rpow_le_euler_prod` and
   `tprod_unramified_eq_prod_artinDirichletSeries` are the two genuinely heavy elaborations.
6. **Recurring idiom worth one helper**: the "plain-lambda anonymous-constructor injection
   into `{𝔭 // 𝔭 ∈ U ∧ IsPrime ∧ ≠ ⊥}` to reindex tsums with `rfl` projections" appears 4×
   in Cyclotomic and ~3× in ZetaProduct (and is the source of the Pi-subtype whnf-timeout
   memory note). A single `Equiv`-producing helper would remove the sharpest recurring
   friction in the analytic files.

## Part 7: Junk / Removable (all verified project-wide by grep)

| # | Declaration | File:Line | Lines | Why dead | Action |
|---|---|---|---|---|---|
| 1 | `norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded` | ZetaProduct:136 | ~48 | Dirichlet-test route superseded by Mellin route | DELETE (trio with 2, 3) |
| 2 | `norm_sum_range_shift_le_of_bounded` | ZetaProduct:187 | ~14 | only feeds 3 | DELETE |
| 3 | `norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded` | ZetaProduct:204 | ~10 | zero consumers project-wide | DELETE |
| 4 | `normLeOne_frontier_lipschitz` | ZetaProduct:802 | ~7 | 1-line wrapper of NLOL's `…_cover`; zero consumers (docstrings only) | DELETE, repoint docstrings at `normLeOne_frontier_lipschitz_cover` |
| 5 | `exists_generator_diff_of_coset` | ICC:847 | ~28 | superseded by round-coordinate route | DELETE |
| 6 | `exists_card_dvd_principal_residue_real_le` | ICC:2382 | ~41 | live L2 path bypasses it | DELETE |
| 7 | `log_artinLSeries_asymp_character_sum` | Cyclotomic:886 | ~87 | live path uses `artinLSeries_prime_sum_bounded_of_ne_one` | DELETE |
| 8 | `gal_compositum_prod_iso` | Abelian | ~40 | crossing leaf uses the two bijectivity lemmas directly | DELETE |
| 9 | `cyclic_subgroup_meets_G_times_one_trivially` | Abelian | ~30 | inlined as `hgate` in the master leaf | DELETE |
| 10 | `H_n_over_H_tends_to_one` | Abelian | ~60 | superseded by admissible-prime route (`H_n_ratio_ge`) | DELETE |
| 11 | `chebotarev_abelian_lowerDensity_per_m` | Abelian | ~50 | zero consumers | DELETE |
| 12 | `map_eq_of_isConj_comm` | Abelian:687 | 6 | = `isConj_iff_eq.mp ∘ MonoidHom.map_isConj` | INLINE at single call site |

Caveats: items 8–11 are blueprint-named entries (C1, the C3-gate prose, the per-m lower
density) — when deleting, update the corresponding `CebotarevBlueprint/Chapters/Abelian.lean`
entries to `{bpref}`-style prose or drop the `(lean := …)` link. Item 4's docstrings at
ZetaProduct:564/2207 need re-pointing. NFEP's `tsum_symGeometric` was flagged "unused in
file" by the inventory but the grep is confounded by the `summable_tsum_symGeometric`
substring — verify during the NFEP cleanup batch before touching it.

---

## Recommended Action Plan

### Priority 1: Quick wins (mechanical, zero mathematical risk)
1. Delete the 11 dead declarations + 1 inline (Part 7) — ~415 lines. Fold into the running
   per-file `/cleanup` batches (ZetaProduct, ICC, Cyclotomic, Abelian) so each deletion is
   build-verified in its batch.
2. Replace `insertPiEquiv` by the mathlib composition (NFEP batch).
3. `clampUnit` → `Set.projIcc` (NLOL batch).

### Priority 2: API improvements
4. Extract the `hreg` region-equivalence helper; retrofit the two ICC cell bijections
   (Cluster C) — removes ~80 duplicated lines from the two longest ICC proofs.
5. Derive ICC implicit-κ twins from the explicit forms (Cluster B).
6. Consolidate character orthogonality into one shared pair (Cluster D).
7. Tag the natural `@[simp]` lemmas (Part 6.3).

### Priority 3: Generalizations / upstreaming (mathlib PRs, in dependency order)
8. PR `LogOneDivSubOne` (trivial), the NLOL phase block, then `LatticePointCount`,
   then the NLOL cover, then the ICC Widmer workhorse (Part 5, items 1–4).
9. PR the finite-abelian character cluster (orthogonality + `prod_one_sub_nthRoots` +
   `prod_galoisCharacter_one_sub` + `charEval_ker_card`).

### Priority 4: Structural (mathematical thought required)
10. Consolidate the two ICC L2 proofs (Cluster A) — decide which of the
    geometric-density vs effective-kernel forms is the canonical export; ~250 lines.
11. Re-derive the unweighted Euler product from the weighted one (Cluster E).
12. Unify the nonzero-ideal encodings on `(Ideal (𝓞 K))⁰` (Part 3) — touches NFEP's public
    signatures, so coordinate with the slice-PR plan.
