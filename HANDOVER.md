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

## 2. Current state (2026-06-06): the analytic chain is DONE; 3 sorries remain

**PROVEN this session (2026-06-05/06), all verified by cache-bypassing `lake env lean` +
`#print axioms` + an adversarial read:**

| What | Where | Status |
|---|---|---|
| **LF3** `character_sum_geometry_of_numbers_bound` | ZetaProduct.lean | proven (partition by value over `μ_n ∪ {0}`, per-fibre leaf G, `Σ_{ζ^n=1} ζ = 0` via the mult-by-ζ₀ shift; new sorry-free helper `sum_nthRootsFinset_eq_zero` — upstream candidate) |
| **LF4** `artinLSeries_analytic_extension` | ZetaProduct.lean | proven (`Lf s := s · mellin S (-s)`; coefficient regrouping; mathlib `LSeries_eq_mul_integral` (Roblot) + `mellin_differentiableAt_of_isBigO_rpow`); LF4/LF5 chain restated at cyclotomic generality (m-threading — same rationale as leaf G's expert-review restatement) |
| **Gap A** `normLeOne_frontier_lipschitz` | **`ForMathlib/NormLeOneLipschitz.lean`** | **proven sorry-free, axiom-clean** `[propext, Classical.choice, Quot.sound]`. The former "deepest gap". Frontier of `expMapBasis '' paramSet` ⊆ image of box boundary ∪ {0}; faces cube-parametrized (`t = exp (x w₀)` linearizes the unbounded direction, `t = 0` absorbs `{0}`); C¹ face maps Lipschitz on the cube + global via `clampUnit`. Mathlib-PR material. |

**The 3 remaining sorries** (the whole project):

```
ZetaProduct.lean:846   Gap B = exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le (L2)
Abelian.lean:157       AB1  = exists_cyclotomicCrossing_fibres (compositum crossing)
Main.lean:1375         M1   = chebotarev_density (top-level assembly)
```

Everything else — the full L-function chain, leaf G, LF1–LF12, L1 (Widmer), Gap A — is proven.
Gap B is the only remaining *analytic* mathematics; AB1/M1 are algebraic infrastructure + glue.

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
