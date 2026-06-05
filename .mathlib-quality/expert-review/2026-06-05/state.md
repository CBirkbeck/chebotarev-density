# Expert-review session state

- Generated: 2026-06-05
- Audience: senior expert in analytic algebraic number theory (geometry of numbers / ideal-counting)
- Goal of brief: specific blocker — obtain the text proof (or precise reference) of the one analytic
  leaf both source texts defer (the effective ideal count), plus confirmation of the CFT-avoidance
  subtlety
- Scope: a single leaf — the geometry-of-numbers ideal-counting estimate A_χ(N, ζ) = CN + O(N^{1−1/d}),
  C independent of ζ (Sharifi 7.1.19's deferred "geometry of numbers can be used to show …")
- Reply received: true (2026-06-05)
- Reply integrated: true (2026-06-05)

## Questions in the brief

| # | Question (verbatim from §9 of the brief) |
|---|------------------------------------------|
| Q1 | Cleanest self-contained statement and proof (or precise monograph reference + exact theorem number, e.g. Lang GTM 110) of the effective ideal count #{N𝔞 ≤ N in a fixed class / fixed norm-residue mod m} = CN + O(N^{1−1/d}), C class-independent. Is 1−1/d the optimal "easy" exponent, and is it what we should formalise vs a weaker O(N^{1−δ})? |
| Q2 | The geometry-of-numbers boundary-error argument producing O(N^{1−1/d}): counting Λ-points in a dilated region t·𝒟 within O(t^{d−1}) of ∂𝒟 — what boundary regularity is used (Lipschitz / finite perimeter / semialgebraic), and the cleanest argument over the leading-term lattice-point limit already in the library? |
| Q3 | Is the CFT-avoidance analysis correct — cyclotomic case: χ̃(𝔞) depends only on N𝔞 mod m so fibres are norm-congruence classes (CFT-free); general-abelian would need Artin reciprocity? I.e. is the right statement to formalise the cyclotomic/norm-congruence count? |
| Q4 | Uniformity of the leading constant C across residue classes mod m: prove per-class with class-independent leading term + uniform error, or prove the total count once then equidistribute by orthogonality? Which is more economical and does either hide a non-elementary input? |

## Ticket-board snapshot at brief time

No active per-leaf ticket board (the old L-function-chain board predates the current state and is
stale). The project is assembled top-to-bottom with five named open leaves:

- `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow` — the geometry-of-numbers count (THE
  subject of this brief; deferred by both sources).
- `character_sum_geometry_of_numbers_bound` — the Σ_ζ ζ = 0 character-sum collapse (full text in
  Sharifi 7.1.19; scaffolded to reduce to the count above).
- `artinLSeries_analytic_extension` — the analytic extension via the Abel criterion (full text:
  Sharifi Lemma 7.1.5; reduces to the count above).
- `exists_cyclotomicCrossing_fibres` — the abelian compositum crossing (full prose in Sharifi 7.2.2
  Step 2 / SL appendix; pure formalisation).
- `dirichlet_primes_in_AP` — the Dirichlet-AP corollary (full text: Sharifi Cor 7.2.3).

Only the first is mathematically open in the sources.

## Stuck points (from §6/§8 of brief)

1. The effective ideal count A_χ(N, ζ) = CN + O(N^{1−1/d}), C independent of ζ — deferred by both
   Sharifi ("geometry of numbers can be used to show") and Stevenhagen–Lenstra (cite Lang). Library
   has the leading term + ideal↔lattice dictionary; missing the O(N^{1−1/d}) boundary error.
2. The CFT-avoidance subtlety: cyclotomic case is norm-congruence (CFT-free); general-abelian would
   need reciprocity. Need confirmation the cyclotomic/norm-congruence statement is the right one.

## Reference list (from §2.2 of brief)

- [Sharifi] Sharifi, *Algebraic Number Theory* notes, Ch. 7 §7.1–7.2 (pp. 138–145).
- [SL] Stevenhagen–Lenstra, "Chebotarëv and his density theorem," Math. Intelligencer 18 (1996),
  appendix.
- [Lang] Lang, *Algebraic Number Theory*, GTM 110 — cited by [SL] for the analytic input ([VIII.4],
  [VII.4]); the precise theorem is what Q1 asks for.
