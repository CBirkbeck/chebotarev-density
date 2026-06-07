# Handover — Chebotarev density formalisation

*Updated 2026-06-06 (supersedes the 2026-06-05 version). Read this first, then `CLAUDE.md`
(project conventions), then `.mathlib-quality/tickets.md` (the live board) and
`.mathlib-quality/decomposition.md` (the proof plan; "Frobenius-fibre chain" section).*

---

## 1. What this project is

A Lean 4 / Mathlib formalisation of **Chebotarev's density theorem** (conjugacy-class form,
finite Galois extension of number fields), deliberately **avoiding class field theory** —
following Sharifi *Algebraic Number Theory* §7.1–7.2 and Stevenhagen–Lenstra. Target:
`Chebotarev.chebotarev_density` in `CebotarevDensity/Main.lean`.

Branch: **`development`**. Many local commits are unpushed — push with
`LEAN4_GUARDRAILS_BYPASS=1 git push` when Chris confirms.

---

## 2. Current state (2026-06-07): THE THEOREM IS COMPLETE

**PROVEN this session (2026-06-05/06), all verified by cache-bypassing `lake env lean` +
`#print axioms` + an adversarial read:**

| What | Where | Status |
|---|---|---|
| **LF3** `character_sum_geometry_of_numbers_bound` | ZetaProduct.lean | proven (partition by value over `μ_n ∪ {0}`, per-fibre leaf G, `Σ_{ζ^n=1} ζ = 0` via the mult-by-ζ₀ shift; new sorry-free helper `sum_nthRootsFinset_eq_zero` — upstream candidate) |
| **LF4** `artinLSeries_analytic_extension` | ZetaProduct.lean | proven (`Lf s := s · mellin S (-s)`; coefficient regrouping; mathlib `LSeries_eq_mul_integral` (Roblot) + `mellin_differentiableAt_of_isBigO_rpow`); LF4/LF5 chain restated at cyclotomic generality (m-threading — same rationale as leaf G's expert-review restatement) |
| **Gap A** `normLeOne_frontier_lipschitz` | **`ForMathlib/NormLeOneLipschitz.lean`** | **proven sorry-free, axiom-clean** `[propext, Classical.choice, Quot.sound]`. The former "deepest gap". Frontier of `expMapBasis '' paramSet` ⊆ image of box boundary ∪ {0}; faces cube-parametrized (`t = exp (x w₀)` linearizes the unbounded direction, `t = 0` absorbs `{0}`); C¹ face maps Lipschitz on the cube + global via `clampUnit`. Mathlib-PR material. |

**MILESTONE 2026-06-07 (the marathon session, 40+ commits): GAP B IS CLOSED.** Audit
(cache-bypassing `lake env lean`, full build green):

```
chebotarev_cyclotomic                                   [propext, Classical.choice, Quot.sound]
exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le (L2)  same
character_sum_geometry_of_numbers_bound (LF3)           same
dirichlet_primes_in_AP                                  same axioms as chebotarev_cyclotomic
```

**ZERO sorries project-wide** (commit c1eb32c). The completion audit (independent,
cache-bypassing `lake env lean`; build green 3805 jobs):

```
chebotarev_density           [propext, Classical.choice, Quot.sound]
chebotarev_density_of_comm   same
density_split_completely     same
dirichlet_primes_in_AP       same
```

AB1 closed via the leaf decomposition: C2a by mathlib's
`linearDisjoint_of_isGalois_isCoprime_discr` (Minkowski internalized) + the new
`prime_dvd_natAbs_discr_cyclotomic_dvd`; C5 by RELOCATING Main's Abelian-independent Step-1
block (18 decls) into the new module `CebotarevDensity/FixedFieldDensity.lean` (imported by
Abelian and Main — no cycle); C1 = the joint-restriction product iso (injective on
generators, surjective by the C2a-at-L degree count); the master assembles the tag (the
cyclotomic character of the M-Frobenius), the τ-dictionary through the C1-inverse, the C3
gate from `|G| ∣ ord τ`, `chebotarev_cyclotomic` at `M/F`, and the relocated transfer.

Remaining board: CL1 (the /cleanup campaign over the session's ~6000 new lines), BP1
(blueprint sync — the new modules + the hm/hcop restatements), UP1 (mathlib-upstream
candidates). Push to origin/development needs Chris (LEAN4_GUARDRAILS_BYPASS=1 git push).

**2026-06-07 follow-on session (this update):**

- **BP1 / verso migration COMPLETE end-to-end**: `lake build CebotarevBlueprint` green
  (4086 jobs, 0 warnings) and the HTML site generates
  (`lake env lean --run CebotarevBlueprintMain.lean --output _out/site`;
  `_out/site/html-multi/index.html` + preview manifest both present; summary shows 72
  completed entries / 0 sorries). Hard-won build facts: `tex_prelude` is a *command*
  (before `#doc`, not in the body); chapters must `import CebotarevDensity` for
  `(lean := …)` resolution; the lemma directive is spelled `:::lemma_`; the KaTeX
  validator shares a macro context across spans so the prelude must be idempotent
  (`\def`, not `\newcommand`); mathlib linter options are scoped to the
  `CebotarevDensity` lib in lakefile.toml (the Verso closure doesn't define them).
- **verso-blueprint v4.30.0 vs toolchain v4.31.0-rc1**: one upstream proof breaks
  (`HoverRender.lean` `hexDigits.size` reducibility). Local patch applied in
  `.lake/packages/VersoBlueprint` (volatile!) and checked in at
  `scripts/patches/verso-blueprint-v4.30-on-v4.31-toolchain.patch`;
  `scripts/ci-pages.sh` applies it idempotently. Drop when upstream publishes v4.31.
- **DO NOT re-run `lake update VersoBlueprint`** without re-checking pins: it downgrades
  mathlib's `proofwidgets` (v0.0.100→v0.0.98) and `plausible` in lake-manifest.json
  (cache-poisoning). They were restored by hand; the warning "putting require mathlib
  last" from lake refers to this.
- **/overview COMPLETE**: 13 per-file inventories in `.mathlib-quality/overview/` +
  `PROJECT_OVERVIEW.md` (mathlib API audit, 7 duplication clusters, 12-item verified
  dead-code list ~415 lines, 8 upstream units, prioritised plan). Fold the dead-code
  deletes into each file's CL1 batch.
- **CL1 progress**: CNR done (pre-existing); Main batch 1 committed (−33 lines, gates
  green, 3 ConjClasses renames queued in `.mathlib-quality/renames.jsonl`); Main batch 2
  + LatticePointCount workers in flight at handover-write time. Remaining: Density,
  Frobenius, NFEP, LogOneDivSubOne, NormLeOneLipschitz, FixedFieldDensity, Cyclotomic,
  Abelian, ZetaProduct, ICC.

Gap B's proof (the session centerpiece; ~8 worker-layers in ICC + the ZetaProduct assembly):
ξ-uniform coset workhorse → explicit-constant cone-point cell counts → per-residue effective
equidistribution → the κ-transfer via the cell-level divisible-density ratio (coprime class
reps via `IsDedekindDomain.exists_sup_span_eq`; covolume ratio `covol(𝔟J) = N𝔟·covol(J)`;
CRT single-coset equidistribution; the vacuous-filter qualifying-match) → Fourier inversion
over the realized-residue subgroup → the `realizedResidues` comap-trick with the
coprime-restricted Frobenii generation (CNR) → the bad-part Euler-tail assembly with the
d = 1 branch (K-internal Eisenstein different-ideal argument).

## 3. Gap B: the arithmetic engine is DONE; assembly remains

The Gap-B decomposition is pinned as compiling sorried statements (commit `137adc8`):

The per-residue effective ideal count — Gap B's engine — is **fully proven and axiom-clean**
(2026-06-06, commits f8aebdd…d34f766): `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`
has axioms exactly `[propext, Classical.choice, Quot.sound]`. The chain: the ξ-uniform coset
workhorse (real dilations, L1-transport) → the mixed-space lift of Gap A's cover (phase tori)
→ the index-coordinate transport → principalization with the residue threaded (novel: the
`leftMulMatrix`/`RingHom.map_det` norm-congruence on cosets; the signed product formula over
embedding pairs; the natAbs↔signed conversion on sign-orthants) → the cone-point count by
(sign-orthant × m-coset) partition feeding the workhorse. Also proven sorry-free
(CyclotomicNormResidue.lean): `cyclotomic_frobenius_acts_as_norm_power` (relocated, breaking
the import cycle), `autToPow_frobeniusClass_out` (Frobenius = norm residue under the
cyclotomic character), and `subgroup_eq_top_of_forall_frobenius_mem` (Frobenii generate;
abelian hypothesis added — the non-abelian out-only form is not CFT-free provable; proof via
a fresh downward Frobenius-restriction lemma + the fibred zeta comparison).

**In flight / remaining for Gap B:**
1. `..._uniform` (IdealCongruenceCount.lean, last sorry): κ-uniformity across realized
   residues. ⚠ The naive ideal-multiplication limit transfer is LOSSY (an `N𝔟` factor); the
   sound route (worked out 2026-06-06, in the dispatched worker's brief): per-cell leading
   terms are (orthant, coset)-independent — `vol(D_s)` is equal across orthants by the
   sign-symmetry of `normLeOne` (mathlib `volume_negAt_plusPart`-adjacent) — so
   `κ_b = #(qualifying cells for b) · κ_cell`, and multiplication by an ELEMENT `y` invertible
   mod the modulus permutes `J/(cNJ)J` shifting the norm residue by `Norm y`, giving
   equinumerosity of qualifying-cell sets. The hypothesis may need strengthening from
   ideal-realizers to element-realizers (authorized; the Gap-B consumer adapts — element
   realizers come from the Frobenius/cyclotomic side).
2. **The Gap B assembly** (ZetaProduct.lean:846, `exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le`):
   bad-prime multiplicative split (`𝔞 = 𝔟·𝔞'`, 𝔟 over the finite unramified-but-`𝔭∣m` set,
   Frobenius shifts via `frobeniusIdeal_mul`) + per `g` the fibre is the norm-residue class
   `χ_cyc(g)` (`autToPow_frobeniusClass_out` + leaf-G's `U`-support machinery) + the uniform
   count over the image subgroup (`subgroup_eq_top_of_forall_frobenius_mem` realizes every
   residue in the image as a product of prime norms, feeding the `hS` hypothesis).

## 4. AB1 and M1 (not started)

- **AB1** `exists_cyclotomicCrossing_fibres` (Abelian.lean:148): compositum
  `Gal(L(μ_m)/K) ≅ G × H` (linear disjointness, `m` coprime to `disc L`), per-`τ` fixed-field
  + `chebotarev_cyclotomic` at `(σ,τ)`, density transfer through `F/K`
  (`density_lift_through_fixedField`, Main.lean:1152, proven). Sharifi 7.2.2 Step 2
  pp. 143–144. The `liminf` scaffolding around it is already proven (LF10/LF12).
- **M1** `chebotarev_density` (Main.lean:1370): Sharifi 7.2.2 Step 1 counting argument
  (fixed-field cyclic reduction; Main.lean's sub-lemmas incl.
  `arithFrobAt_restrictScalars_eq`, `density_split_completely` are proven) + assembly with
  AB1's chain.

---

## 5. CRITICAL LESSONS (unchanged + new)

1. **Verify every delegated proof**: (a) `lake env lean <file>` (cache-bypassing); (b)
   `#print axioms` (no custom axioms; `sorryAx` only via intended gaps); (c) READ the proof —
   false-but-compiling helper *statements* are the classic failure (two caught 2026-06-05,
   both Θ(N) off). This session's delegations were all verified clean; one frozen statement
   (Frobenii-generate) was caught as unprovable-as-stated *before* delegation — adversarial
   statement-reads pay.
2. **Whnf-timeout pitfall**: under a `with`-binder over a subtype, ALWAYS ascribe
   `(Finset.univ : Finset {…})`, else `Fintype {x // ?p}` instance search deterministically
   times out. (Cost 30 min on LF3.)
3. **`push Not` not `push_neg`** (deprecated); **`change` not goal-changing `show`**
   (linter.style.show); `≤`/`<` only, smaller side left; no axioms; no new `sorry` in fills.
4. **The bad primes subtlety** (load-bearing for Gap B): `U 𝔞` = "all prime factors
   unramified" is the exact support of `galoisCharacterOnIdeal`; unramified does NOT imply
   `N𝔭` coprime to `m` (K ⊇ ℚ(μ_{p^a}) case). Gap B's assembly must split off the finite
   bad-prime part.
5. **`lake build` job counts ~3790; baseline green.** Pre-existing warnings (hAb unused,
   3 longLines, 3 maxHeartbeats in old decls) are NOT from this session's work.

---

## 6. Background machinery

- **PR-poll cron**: recreate at EVERY session start — `CronCreate` `durable: true` is
  silently unsupported (verified 2026-06-05). Schedule `23 */2 * * *`; the full poll prompt
  and STATE-file spec are in the git history of this file (2026-06-05 version, §7) and the
  memory `pr-poll-cron-not-durable`. Open PRs #4, #2; flag riccardobrasca/xroblot only.
- **Beastmode sentinel**: `.mathlib-quality/beastmode_active` keeps the marathon alive;
  remove only at a genuine session terminal.
- Build: `lake exe cache get`, `lake build`; genuine check `lake env lean <file>`. Commit on
  `development`; no backticks/apostrophes in `git commit -m`; footer
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`.

## 7. One-paragraph status for a cold reader

The analytic core of the CFT-free Chebotarev proof is complete: Widmer's effective
lattice-point count (L1), the Lipschitz frontier cover of the ideal fundamental domain
(Gap A, GRS §3.3), the character-sum cancellation (LF3) and the analytic continuation of the
abelian L-functions past `s = 1` (LF4, Abel summation + Mellin) are all proven and
axiom-clean, and the non-vanishing/density chain built on them was already in place. Three
sorries remain: Gap B (Frobenius-fibre equidistribution — skeleton pinned, the coset-counting
workhorse and the norm-residue/generation dictionary in flight), the compositum crossing
(AB1), and the final assembly (M1).
