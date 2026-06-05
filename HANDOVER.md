# Handover — Chebotarev density formalisation

*Written 2026-06-05 for the next worker picking up this proof. Read this first, then
`CLAUDE.md` (project conventions), then `.mathlib-quality/decomposition.md` (the proof plan).*

---

## 1. What this project is

A Lean 4 / Mathlib formalisation of **Chebotarev's density theorem** (conjugacy-class form,
finite Galois extension of number fields), deliberately **avoiding class field theory** —
following Sharifi *Algebraic Number Theory* §7.1–7.2 and Stevenhagen–Lenstra. Target:
`Chebotarev.chebotarev_density` in `CebotarevDensity/Main.lean`.

Three reductions (see `CLAUDE.md` "Proof structure"): general → cyclic (fixed-field), cyclic/
abelian → cyclotomic (compositum trick), cyclotomic (Dirichlet's argument via `ζ_L = ∏ L(χ,·)`).

Branch: **`development`** (this tree). Progress ships to `master` as slice-PRs later.

---

## 2. Current frontier — the whole proof now rests on TWO deep geometry-of-numbers gaps

The hard analytic content has been driven down to two standalone, **correctly-stated** lemmas
(everything else is glue or already proven). In dependency order:

### Gap A — `normLeOne_frontier_lipschitz`  (`ZetaProduct.lean:793`, sorry at ~799)
*The ideal fundamental domain has Lipschitz boundary.* States: `frontier (normAtAllPlaces ''
normLeOne K)` is covered by finitely many Lipschitz images of the unit cube `[0,1]^{d-1}`
(in L1's `hlip` shape). **Source: Gun–Ramaré–Sivaraman, JNT 243 (2023), §3.3 (Lemmas 5–8).**
mathlib has only `volume_frontier_normLeOne = 0` (measure-zero), NOT the Lipschitz cover. This
is a fresh **mathlib-PR-scale** development (like L1 was) using `mixedEmbedding`/`fundamentalCone`/
`logMap`/`expMapBasis` — the explicit parametrisation of the cone boundary.

### Gap B — `exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le` (L2)  (`ZetaProduct.lean:831`, sorry at ~842)
*Frobenius-fibre equidistribution.* `∃ κ C', ∀ g, |#{𝔞 : U 𝔞 ∧ N𝔞 ≤ N ∧ frobeniusIdeal 𝔞 = g}
− κN| ≤ C'·N^{1−1/d}`, κ **independent of g** (`U 𝔞 := all prime factors of 𝔞 unramified`).
**Builds on Gap A + L1** (apply the effective lattice count to the ideal lattice ∩ congruence
sublattice). The proof must handle the **bad-prime split** (see §5 lesson 2). Source: GRS Thm 1 /
§3.1+3.6 specialised; `cyclotomic_frobenius_acts_as_norm_power` (Cyclotomic.lean:83) for
`Frob_𝔞 = g ⟺ N𝔞 ≡ … mod m` — BUT note the import cycle below.

**These two are the only real mathematics left in the L-function chain.** Both are isolated as
clean sorried lemmas; the reduction *to* them is proven and committed.

---

## 3. What is already PROVEN (committed, on `development`, NOT yet pushed)

| Commit | What |
|---|---|
| `b1cbc5f` | **L1 = Widmer's effective lattice-point count** (`exists_card_inter_smul_lattice_sub_volume_mul_pow_le`, `ForMathlib/LatticePointCount.lean`) — sorry-free, axiom-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]`). The project's deepest gap. 5 helper lemmas; boundary-cell argument. **Verified** by genuine `lake env lean` + axiom check + full read. |
| `d9d0b99` | board note (LF3 mountain climbed) |
| `8f33578` | **Leaf G soundly reduced** (`exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow`) to Gap A + Gap B, via sorry-free helpers: `galoisCharacterOnIdeal_eq_char_frobeniusIdeal` (Helper 1), `card_valueFibre_eq_card_unramifiedSupported_frobeniusValueFibre` (set-equality), `frobeniusIdeal` (+`_mul`/`_one`), `charFibre_mem_range`, `card_charFibre_eq_card_ker`. |

**3 commits are local-only.** Push them with `LEAN4_GUARDRAILS_BYPASS=1 git push` when ready
(prior sessions pushed to `origin/development`; this session held the push — confirm with Chris).

---

## 4. The remaining sorries (6 total) and how to continue, in priority order

```
ZetaProduct.lean:799  normLeOne_frontier_lipschitz          Gap A  (deep — GRS §3.3 mountain)
ZetaProduct.lean:842  exists_card_frobeniusIdeal_fibre_…    Gap B = L2 (deep — builds on A + L1)
ZetaProduct.lean:1007 character_sum_geometry_of_numbers…    LF3 (GLUE — do this next, tractable)
ZetaProduct.lean:1038 artinLSeries_analytic_extension       LF4 (GLUE — Abel summation from LF3)
Abelian.lean:157      (chebotarev_abelian piece)            glue / compositum crossing
Main.lean:1375        chebotarev_density                    top-level assembly
```

**Recommended next step (tractable, was about to be done when this handover was requested):**
complete **LF3** (`character_sum_geometry_of_numbers_bound`, sorry at line 1007). It already
`obtain`s leaf G and sets `C := orderOf χ · C'`; only the cancellation remains: partition the
finite sum `Σ_{N𝔞≤N} galoisCharacterOnIdeal χ 𝔞` by value `ζ ∈ μ_n` (the 0-fibre drops), apply
leaf G per fibre, leading term cancels because `Σ_{ζ^n=1} ζ = 0` for `n = orderOf χ ≥ 2`. Then
**LF4** via Abel summation (Sharifi Lemma 7.1.5) — the project's own
`norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded` (~ZetaProduct.lean:128) is the
Dirichlet-test lemma; look for a mathlib `LSeries.summable_of_…` partial-sums criterion. Doing
LF3+LF4 collapses the entire analytic chain onto Gaps A+B.

**Then the deep mountains (A, then B).** These are genuine multi-session geometry-of-numbers
developments. Gap A (normLeOne Lipschitz boundary) is the foundational one — B and L1's
*application* both need it.

### Workflow for continuing
- **Plan first:** `/develop --decompose` writes/refreshes `.mathlib-quality/decomposition.md`
  with verbatim source quotes per leaf. **`/beastmode`** executes (marathon mode; auto-picks the
  next ticket; has a Stop hook that keeps it alive across turn-ends via the
  `.mathlib-quality/beastmode_active` sentinel — remove the sentinel to end a session).
- **Delegate hard proofs** to `lean4:sorry-filler-deep` sub-agents (they have Lean LSP; the main
  Claude session here did NOT). Give them the exact statement, the reduction plan, the mathlib
  API names, and L1's statement. **But see §5 — VERIFY their output, they produce
  plausible-but-sometimes-unsound proofs.**

---

## 5. CRITICAL LESSONS (read before trusting any delegated proof)

1. **Sub-agents (`sorry-filler-deep`) lack Lean LSP** in this environment — they validate with
   `lake build`/`lake env lean` only. They produced **3 errors this session** that I caught by
   careful verification:
   - a **false thin-set bridge** (`|#value-fibre − #Frobenius-value-fibre| ≤ O(N^{1−1/d})` — actually
     **Θ(N)**, because ramified-divisible ideals number Θ(N), not O(N^{1−1/d}));
   - a **false iff** `UnramifiedIn 𝔭 ↔ (N𝔭).Coprime m` (fails when K contains local p-power roots
     of unity, e.g. K ⊇ ℚ(μ_{p^a}), m = p^a·m′ — then primes over p are unramified but N𝔭 not
     coprime to m);
   - a **false claim that L1 was sorried** (it is not — pure report confusion).
   **Always verify a delegated proof:** (a) `lake env lean <file>` (cache-bypassing — `lake build`
   can replay stale `.olean`); (b) `#print axioms <decl>` (no custom axioms; `sorryAx` only from
   intended gaps); (c) **READ the proof** for subtle math bugs (the two Θ(N) errors compiled fine
   because their lemmas were sorried — the *statements* were false).

2. **The "bad primes" subtlety (load-bearing for Gap B).** For `L = K(μ_m)`, a prime can be
   **unramified yet have N𝔭 not coprime to m** (when K already contains the local p-power roots).
   The correct support condition is **U = "all prime factors unramified"** (the exact support of
   `galoisCharacterOnIdeal ≠ 0`), NOT "coprime to m". Gap B's proof must split an
   unramified-supported 𝔞 into its finite "bad-prime part" (unramified, Frobenius ≠ norm-power)
   × "good part" (coprime to m, Frobenius = norm-power via `cyclotomic_frobenius_acts_as_norm_power`)
   and sum the per-good-part congruence counts. The L2 docstring (ZetaProduct.lean ~827) records this.

3. **Import cycle:** `Cyclotomic.lean` **imports** `ZetaProduct.lean`, so
   `cyclotomic_frobenius_acts_as_norm_power` (in Cyclotomic) **cannot** be called from ZetaProduct
   (where Gap B lives). To prove Gap B you must either move that lemma (+ deps) up to ZetaProduct/an
   earlier file, or relocate Gap B. (Leaf G's *value-fibre* side avoided this — Helper 1 needs only
   the U-predicate, no cyclotomic Frobenius fact.)

4. **Mathlib conventions (enforced):** `≤`/`<` never `≥`/`>` in Lean code; no placeholder
   `def := sorry`; no `axiom`s anywhere; no `: True := by`. Number fields universe-polymorphic.
   See CLAUDE.md "Conventions".

---

## 6. Where the proof plans and references live

- **`.mathlib-quality/decomposition.md`** — THE plan. Key sections: L1 (line 758, marked
  `STATUS: PROVED`), the **"Frobenius-fibre chain"** (line 682 — the leaner CFT-free route:
  L1/L2/L3, the ℚ(i)-trap analysis, the orthogonality-over-G argument), the L-function chain.
- **`.mathlib-quality/tickets.md`** — the LF1–LF12 board (somewhat out of sync with the actual
  ZetaProduct structure; the real work-items are the sorries in §4).
- **`.mathlib-quality/b2_log.jsonl`** — logged false-statement findings (a *stale* entry about
  `frobeniusClass.out` junk-on-composites — already fixed by `galoisCharacterOnIdeal`; don't
  re-action it).
- **`.mathlib-quality/learnings.jsonl`** — golf/cleanup/simplify learnings.
- **References:** Sharifi §7.1–7.2 = `docs/algnum.pdf` (pp. 138–144 cover everything);
  Stevenhagen–Lenstra = `docs/cheb.pdf`. **GRS** (Gun–Ramaré–Sivaraman, *Counting ideals in ray
  classes*, JNT 243 (2023)) is the geometry-of-numbers source for Gaps A/B — §3.3 (Lipschitz
  boundary), §3.5 (counting); it cites **Widmer**, Trans. AMS 362 (2010) for the lattice count
  (= L1). Lang GTM 110 Ch. V§2 / Ch. VI§3 Thm 3, p. 129 (boundary-cell estimate).
- **`CLAUDE.md`** — conventions, file layout, build, blueprint, branch workflow. Read it.
- **Always read the actual PDFs / `.lean` files, never memory/summaries** — that is how the stale
  b2_log slipped in. (CLAUDE.md and the memory both stress this.)

---

## 7. The PR-comment workflow (background cron)

A background cron **polls all open GitHub PRs** on `CBirkbeck/chebotarev-density` for NEW
reviewer comments each time it fires. You'll see it arrive as a message starting *"Background
poll of ALL open GitHub PRs …"*. It is **read-only** — do NOT edit code or push *during the poll*.

- **STATE file:** `/Users/mcu22seu/.claude3/projects/-Users-mcu22seu-Documents-GitHub-chebotarev-density/pr4-last-seen.txt`
  — per-PR JSON `{"<pr#>": {"review": <id>, "issue": <id>}}` (review and issue comment IDs are
  tracked **separately** — different ID ranges). Current: `{"4": {…}, "2": {…}}`. Open PRs: **#4, #2.**
- **Logic:** list open PRs (`gh pr list --repo CBirkbeck/chebotarev-density --state open`); for each,
  fetch review comments (`gh api …/pulls/N/comments`) and issue comments (`gh api …/issues/N/comments`);
  a comment is NEW iff `id > stored` AND `author != "CBirkbeck"`. First time a PR is seen, **seed**
  its IDs without flagging history. If new comments: print them + `PushNotification`, update STATE.
  If none: print exactly `PRs: no new comments.` (the poll prompt has the full spec.)
- **When a reviewer comment IS new:** per the standing directive (memory `action-pr-feedback-at-once`),
  implement it **immediately on both branches** (build + commit + push + reply, same session) — don't
  defer. But the poll message itself says read-only; act on the comment in a *separate* working turn.

### Set up the cron AT SESSION START — it does NOT survive (do this first thing)

The poll is driven by a **session-only** cron job (schedule `23 */2 * * *` = every 2 hours at :23,
recurring). **Session-only = it dies when the Claude session exits**, so it is gone now — you must
recreate it at the start of your session, or it will never fire. Recreate it with the `CronCreate`
tool (pass `durable: true` if you want it persisted to `.claude/scheduled_tasks.json` so it survives
restarts; note recurring crons auto-expire after 7 days regardless). Store this exact prompt:

```
CronCreate(
  cron = "23 */2 * * *",
  recurring = true,
  durable = true,          # optional — survives restarts; otherwise session-only like now
  prompt = <<the full poll prompt below>>
)
```

Full poll prompt to store (verbatim):

```
Background poll of ALL open GitHub PRs (CBirkbeck/chebotarev-density) for NEW reviewer comments. Be concise; do NOT edit code or push.

1. Working dir: /Users/mcu22seu/Documents/GitHub/chebotarev-density
2. STATE file: /Users/mcu22seu/.claude3/projects/-Users-mcu22seu-Documents-GitHub-chebotarev-density/pr4-last-seen.txt — per-PR JSON {"<pr#>": {"review": <id>, "issue": <id>}, ...}. Read it; if missing/unparseable, treat as {}. (Review and issue comments use DIFFERENT id ranges — track separately per PR.)
3. List open PRs: gh pr list --repo CBirkbeck/chebotarev-density --state open --json number -q '.[].number'
4. For EACH open PR N:
   a. SEED-ON-FIRST-SIGHT: if N is ABSENT from STATE, set STATE[N] = {"review": <current max review id for N>, "issue": <current max issue id for N>} and do NOT flag any existing comment (avoids flagging historical comments when a PR first comes under watch). Then continue.
   b. Else fetch — review: gh api repos/CBirkbeck/chebotarev-density/pulls/N/comments --paginate -q '.[] | [.id, .path, (.line // .original_line), .user.login, .body] | @json'  ; issue: gh api repos/CBirkbeck/chebotarev-density/issues/N/comments --paginate -q '.[] | [.id, "(issue)", 0, .user.login, .body] | @json'
   c. A review comment is NEW iff id > STATE[N].review AND author != "CBirkbeck". An issue comment is NEW iff id > STATE[N].issue AND author != "CBirkbeck".
5. If NO new comments across all PRs (seeding a PR is NOT a "new comment"): print exactly "PRs: no new comments." and stop — no notification, no edits.
6. If ANY PR has NEW comments: print each (PR#, author, path:line, full body). Then update STATE — for every open PR set "review" to the max id across ALL its review comments (including CBirkbeck replies) and "issue" to the max across ALL its issue comments; drop entries for PRs no longer open; write the per-PR JSON back. Send ONE concise PushNotification (status proactive): "PR #<n>: N new comment(s) from <authors> on <files>" (combine across PRs). Do NOT edit code or push — just surface them for Chris to review next session.
```

Current STATE (as of 2026-06-05): open PRs are **#4** and **#2**, both seeded —
`{"4": {"review": 3358378028, "issue": 4630264902}, "2": {"review": 3325972136, "issue": 0}}`.
Reviewers to watch: `riccardobrasca`, `xroblot` (comments by `CBirkbeck` are never flagged).

---

## 8. Build / git mechanics

```bash
lake exe cache get                              # fetch mathlib artefacts
lake build                                      # whole project
lake build CebotarevDensity.ZetaProduct         # one module
lake env lean CebotarevDensity/ZetaProduct.lean # GENUINE compile (cache-bypassing — use to verify)
```
- Baseline is **green** (3791 jobs); the 6 sorries above are the only ones (all warned, none error).
- **Git:** on `development`. Commit progress here (project norm). Push:
  `LEAN4_GUARDRAILS_BYPASS=1 git push`. In `git commit -m`, **no backticks** (shell substitution)
  and avoid apostrophes inside `'…'` strings. Footer every commit with:
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`. `git checkout -- <file>`
  / `git restore` are blocked — use `git stash` to discard.
- **Clean as you go:** run `/cleanup` on new declarations before committing (memory
  `cleanup-before-pr-commits`); the LINE PACKING gate fills docstring prose to ~100 cols too.

---

## 9. One-paragraph status for a cold reader

L1 (Widmer's effective lattice-point count — the deepest analytic input) is **fully proven and
axiom-clean**. Leaf G (the ideal-character value-fibre count) is **soundly reduced** to two
clean sorried lemmas: Gap A (`normLeOne_frontier_lipschitz`, the ideal fundamental domain's
Lipschitz boundary — GRS §3.3) and Gap B (L2, the Frobenius-fibre equidistribution built from
L1 + the congruence sublattice). Above leaf G, two tractable glue lemmas remain (LF3 character-sum
cancellation via `Σζ = 0`, LF4 analytic extension via Abel summation), then the compositum
crossing and the top-level assembly. The next concrete move is LF3; the real remaining mathematics
is Gaps A and B. Verify every delegated proof against `lake env lean` + `#print axioms` + a read —
two false-but-compiling statements were caught this session.
