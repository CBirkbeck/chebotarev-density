# Review brief — Chebotarev density theorem (CFT-free, geometry-of-numbers input)

*Prepared 2026-06-05 for a senior expert in analytic algebraic number theory (geometry of
numbers / ideal-counting). Self-contained: no repository access required.*

---

## 1. Goal

We are producing a complete, machine-checked proof of **Chebotarev's density theorem** in
conjugacy-class form for a finite Galois extension L/K of number fields. With G = Gal(L/K)
and C ⊆ G a conjugacy class, the statement is: the set of primes 𝔭 of 𝓞_K that are
unramified in L and whose Frobenius conjugacy class σ_𝔭 equals C has Dirichlet density
|C|/|G|.

A hard design constraint is that the proof **avoids class field theory** entirely: it
follows the classical route (Dirichlet for the cyclotomic case; Chebotarev's "crossing with
cyclotomic extensions" for the abelian case; a fixed-field reduction for the general case),
exactly as presented in Sharifi's notes and the Stevenhagen–Lenstra survey (citations in
§2.2). No Artin reciprocity, no idele class groups, no Hilbert/ray class fields are used.

The entire proof is assembled and almost entirely complete. **One analytic input is the sole
remaining mathematical gap**, and both of our source texts explicitly defer it ("the geometry
of numbers can be used to show…"). This brief asks you to supply, or point us precisely to,
its proof — and to confirm a subtlety about how it stays within the no-class-field-theory
constraint.

---

## 2. Background and references

### 2.1. Setting and notation

- K is a number field, d = [K : ℚ], with ring of integers 𝓞_K.
- For a nonzero integral ideal 𝔞 ⊆ 𝓞_K, N𝔞 = |𝓞_K / 𝔞| is the absolute norm.
- For a set S of primes of 𝓞_K, the **Dirichlet density** δ(S) is the limit, if it exists, of
  (Σ_{𝔭 ∈ S} N𝔭^{−s}) / log(1/(s−1)) as s → 1⁺ along the reals. Equivalently
  Σ_{𝔭 ∈ S} N𝔭^{−s} ∼ δ(S)·log(1/(s−1)).
- For 𝔭 unramified in L, σ_𝔭 ⊆ G denotes the **Frobenius conjugacy class** (the conjugacy
  class of any Frobenius automorphism at a prime of L above 𝔭).
- When G is abelian and χ : G → ℂˣ is a character, we write χ̃ for the **completely
  multiplicative ideal character**: χ̃(𝔭) = χ(Frob_𝔭) for 𝔭 unramified, χ̃(𝔭) = 0 for 𝔭
  ramified, extended multiplicatively to all integral ideals. The Artin L-function is then
  L(χ, s) = ∏_𝔭 (1 − χ̃(𝔭) N𝔭^{−s})^{−1} = Σ_𝔞 χ̃(𝔞) N𝔞^{−s} for Re s > 1.

### 2.2. References

- **[Sharifi]** Romyar Sharifi. *Algebraic Number Theory* (lecture notes), Chapter 7
  ("Global class field theory via ideals"), §7.1–7.2. The proof we formalise is §7.1.16
  through §7.2.3 (pp. 138–145). This is the primary substrate.
- **[SL]** Peter Stevenhagen and Hendrik W. Lenstra, Jr. "Chebotarëv and his density
  theorem." *Math. Intelligencer* 18 (1996), no. 2, 26–37. The appendix (their pp. 18,
  internal numbering) gives the same proof with slightly different framing, citing **Lang**
  for the analytic input.
- **[Lang]** Serge Lang. *Algebraic Number Theory*, 2nd ed., GTM 110, Springer, 1994.
  [SL] cites "[VIII.4, Corollary to Theorem 8]" and "[VII.4]" of (an edition of) Lang for
  the cyclotomic/analytic step; we have not been able to extract a self-contained statement
  of the effective ideal count from our texts, which is the point of this brief.

### 2.3. State of the art

The mathematics here is entirely classical (1920s–1930s) and is not in question. The gap is
purely one of having a **precise, self-contained, formalisation-ready statement and proof**
of the ideal-counting estimate below — the kind of thing textbooks state as "by the geometry
of numbers" and leave to the reader or to a cited monograph. In the proof assistant's library
(Mathlib) we already have the **leading-term** version of this count (the analytic
class-number-formula main term, obtained as a lattice-point limit), together with the full
ideal ↔ lattice dictionary (fundamental domain in the Minkowski/mixed embedding, covolume of
the ideal lattice, Dirichlet's unit theorem). **What is missing in the library, and in our
texts, is the effective version with an explicit power-saving error term** — and a
confirmation that the version we need stays free of class field theory.

---

## 3. Strategy (the three reductions)

The proof reduces the general theorem to the cyclotomic case in three steps, all classical:

1. **General → cyclic.** For σ ∈ C, let E = L^{⟨σ⟩} be the fixed field of ⟨σ⟩. Then L/E is
   cyclic, and a counting argument relates δ_K of the C-fibre to δ_E of the σ-fibre. (Done.)
2. **Cyclic/abelian → cyclotomic.** For the abelian case, choose m coprime to disc(L) and
   form the compositum M = L(μ_m); then Gal(M/K) ≅ G × H with H = (ℤ/mℤ)ˣ. For each
   admissible τ ∈ H (those with |G| | ord τ), the cyclic group ⟨(σ, τ)⟩ meets G × {1}
   trivially, so the fixed field F = K(μ_m)^{⟨(σ,τ)⟩} makes M/F **cyclotomic**; applying the
   cyclotomic case to M/F and summing over τ recovers density 1/|G|. (Done, modulo the
   compositum infrastructure, which has a full prose proof in both texts.)
3. **Cyclotomic.** This is Dirichlet's analytic argument: factor ζ_L = ∏_χ L(χ, ·) over the
   characters of G; the trivial character contributes the pole of ζ_K, every nontrivial
   character contributes a bounded term because L(χ, 1) ≠ 0; character orthogonality then
   extracts the density 1/|G|. (Done — see §5 — **except** for the one analytic input in §6.)

---

## 4. Definitions used in the blocker

**Definition 4.1 (the value-fibre count).** Fix a nontrivial character χ of G of order n, and
let ζ be an n-th root of unity. Define

  A_χ(N, ζ) = #{ integral ideals 𝔞 ⊆ 𝓞_K : N𝔞 ≤ N and χ̃(𝔞) = ζ }.

(χ̃ is as in §2.1: completely multiplicative, equal to χ(Frob_𝔭) on unramified primes and 0
on ramified ones, so χ̃ takes values in μ_n ∪ {0}.)

**Definition 4.2 (the partial character sum).** S_χ(N) = Σ_{N𝔞 ≤ N} χ̃(𝔞), the sum over all
integral ideals of norm ≤ N.

---

## 5. Established results (the argument surrounding the gap is in hand)

To make clear that the gap below is genuinely the *only* remaining mathematical input, here is
what is already formally proven (each statement is fully machine-checked unless noted):

- **(Euler product / Dirichlet-series form.)** For Re s > 1, L(χ, s) = ∏_𝔭(1 − χ̃(𝔭)N𝔭^{−s})^{−1}
  = Σ_𝔞 χ̃(𝔞)N𝔞^{−s}, with χ̃ completely multiplicative on ideals (Sharifi 7.1.18).
- **(Local factorisation.)** ∏_χ (1 − χ(σ)X) = (1 − X^{ord σ})^{|G|/ord σ}, matching the
  splitting of a prime, hence the character-product factorisation of the local Euler factor
  of ζ_L (Sharifi 7.1.16).
- **(Non-vanishing L(χ, 1) ≠ 0.)** For nontrivial χ, via the pole-order argument: if some
  L(χ, 1) = 0, the factorisation log ζ_L = Σ_χ log L(χ, ·) would over-cancel the simple pole
  of ζ_L, contradiction (Sharifi 7.1.19, step 2). *Proven conditionally on the analytic
  extension below.*
- **(Boundedness of the twisted prime sum near s = 1.)** For nontrivial χ, the sum
  Σ_𝔭 χ(Frob_𝔭) N𝔭^{−s} stays bounded as s ↓ 1⁺. *Newly proven in full:* write it as
  g_χ(s) − R_χ(s) where g_χ = Σ_𝔭 −Log(1 − χ̃(𝔭)N𝔭^{−s}) is the Euler-product logarithm and
  R_χ a uniformly bounded prime-power tail; exp(g_χ) = L(χ, ·), so g_χ′ = L′/L is the
  single-valued logarithmic derivative (sidestepping the branch ambiguity of log L), which is
  continuous hence bounded near s = 1 by analyticity and non-vanishing, and the mean-value
  inequality bounds g_χ. This is the substantive complex-analytic content of the cyclotomic
  case and it is complete.
- **(Character orthogonality and density extraction.)** Σ_χ χ(σ)^{−1} log L(χ, s) is computed
  two ways — as |G| times the σ-fibre prime sum, and as ∼ log ζ_K(s) ∼ log(1/(s−1)) — yielding
  density 1/|G| (Sharifi 7.2.1).
- **(Fixed-field reduction; compositum crossing.)** Steps 1 and 2 of §3 are assembled; the
  compositum-crossing existence statement (Gal(L(μ_m)/K) ≅ G × H and the density transfer) has
  a complete prose proof in both [Sharifi] and [SL] and is being formalised from that text.

The only analytic ingredient our texts state without proof is the following.

---

## 6. The blocker — the geometry-of-numbers ideal count

In the analytic extension of L(χ, ·) past Re s = 1 (Sharifi 7.1.19), one needs the partial
character sum S_χ(N) (Definition 4.2) to be O(N^{1−1/d}). Given that bound, an Abel-summation
criterion (Sharifi's Lemma 7.1.5: bounded partial sums Σ_{k≤n} a_k ≤ Cn^u imply Σ a_k k^{−s}
converges absolutely on Re s > u) immediately yields that L(χ, s) = Σ_𝔞 χ̃(𝔞)N𝔞^{−s}
converges, hence is analytic, on the half-plane Re s > 1 − 1/d. That Abel-summation criterion
**is** proven (and is exactly Mathlib's `LSeriesSummable_of_sum_norm_bigO`); the O(N^{1−1/d})
bound on S_χ(N) is what is missing.

Sharifi derives that bound (7.1.19) from the following counting statement, which he attributes
to "the geometry of numbers" and does not prove:

> **The deferred estimate.** There is a constant C > 0, **independent of ζ**, such that for
> every n-th root of unity ζ and every N ≥ 1,
>
>   A_χ(N, ζ) = C·N + O(N^{1−1/d}),     d = [K : ℚ].
>
> Given this, S_χ(N) = Σ_{ζ ∈ μ_n} ζ · A_χ(N, ζ) = (Σ_{ζ ∈ μ_n} ζ)·C·N + O(N^{1−1/d}) =
> O(N^{1−1/d}), since Σ_{ζ ∈ μ_n} ζ = 0 for n ≥ 2.

The last computation (the character-sum collapse) is elementary and formalised. The deferred
estimate itself is the gap.

[SL] do not fill it either: their cyclotomic step expresses ζ_K as a product of L-functions
and "finishes with a traditional argument as in [Lang VIII.4, Corollary to Theorem 8]" — i.e.
they cite Lang rather than reproduce the count.

### What the library already provides (so you can calibrate the gap)

The ideal ↔ lattice dictionary and the **leading-term** asymptotic are already available:

- The number of integral ideals 𝔞 in a fixed ideal class with N𝔞 ≤ t is asymptotically
  κ·t + o(t), where κ = (2^{r₁}(2π)^{r₂} Reg) / (w √|disc K|) is the standard
  class-number-formula constant (r₁, r₂ real/complex places, Reg the regulator, w the number
  of roots of unity); this is obtained as a lattice-point count in a fundamental domain of the
  ideal lattice under the Minkowski/mixed embedding, via a covolume limit.
- The constant κ is the **same for every ideal class** (it does not depend on the class) — so
  the "C independent of ζ" requirement is, at the leading-term level, already visible.
- What is absent is any **error term**: the available statement is a bare limit (count/t → κ),
  with no rate. The O(t^{1−1/d}) boundary error — the count of lattice points within O(t^{1−1/d})
  of the boundary of the dilated fundamental region — is exactly the missing analytic content.

---

## 7. The class-field-theory subtlety (the second thing we need confirmed)

For "C independent of ζ" to hold, the values of χ̃ must equidistribute across the ideals — i.e.
χ̃ must factor through a finite quotient of the ideal monoid on which ideals are
equidistributed by norm. This is where the no-class-field-theory constraint bites, and we want
to be sure the formalised statement does not smuggle in Artin reciprocity:

- **Cyclotomic case (where the estimate is actually used).** When L = K(μ_m) is cyclotomic over
  K, χ is a character of Gal(K(μ_m)/K), a subquotient of (ℤ/mℤ)ˣ, and the Frobenius of an
  unramified prime 𝔭 depends only on N𝔭 mod m (Sharifi 7.2.1; [SL] make the same observation:
  "the Frobenius substitution of a prime 𝔭 depends only on the norm of 𝔭 modulo the order of
  ζ"). Hence χ̃(𝔞) depends only on **N𝔞 mod m**, and the value-fibre {χ̃(𝔞) = ζ} is a union of
  **norm-congruence classes** {N𝔞 ≡ c (mod m)}. Counting A_χ(N, ζ) then reduces to counting
  ideals with N𝔞 ≤ N in a fixed residue class of the norm modulo m — which is geometry of
  numbers plus a congruence condition, with no reciprocity needed.
- **General abelian case.** For a general abelian L/K (not cyclotomic), the statement "χ̃ = χ∘Frob
  factors through a finite quotient of the ideal monoid" is, as far as we can see, exactly the
  content of Artin reciprocity. Our architecture avoids this: the abelian case is reduced to the
  cyclotomic case by the compositum crossing (§3 step 2), so the deferred estimate is only ever
  invoked when χ is a **cyclotomic** character (χ̃ a function of the norm modulo m).

So we believe the right formalised statement of the estimate is the **cyclotomic / norm-congruence
form**, not the general-abelian form, and that in that form it is genuinely class-field-theory-free.
We would like this confirmed (or corrected).

---

## 8. Where we are stuck — summary

The whole Chebotarev proof is assembled and machine-checked except for one classical analytic
estimate that both of our sources defer: the effective count A_χ(N, ζ) = C·N + O(N^{1−1/d}) with
C independent of ζ (§6), specialised to the cyclotomic/norm-congruence setting (§7). We have the
leading term and the full ideal↔lattice machinery in the library; we lack the error term and a
clean, formalisation-ready, class-field-theory-free statement and proof.

---

## 9. Questions for the reviewer

**Q1 (statement + proof or precise reference).** What is the cleanest self-contained statement
and proof of the effective ideal count — for K a number field of degree d, the number of integral
ideals 𝔞 with N𝔞 ≤ N lying in a fixed class (or, more relevantly for us, with N𝔞 in a fixed
residue class modulo m) is C·N + O(N^{1−1/d}), with C independent of the class? If a monograph
proof is the right thing to point us at, what is the exact statement and location (e.g. the precise
theorem number in Lang GTM 110, or in another standard reference such as Narkiewicz or Murty)? Is
the exponent 1 − 1/d the optimal "easy" geometry-of-numbers error, and is it what we should aim to
formalise (as opposed to a weaker O(N^{1−δ}) that would still suffice)?

**Q2 (the geometry-of-numbers argument).** At the level of detail needed to formalise it, what is
the boundary-error estimate that produces O(N^{1−1/d})? Concretely: counting lattice points of a
full lattice Λ ⊂ ℝ^d in a dilated region t·𝒟 (𝒟 the fundamental region for ideals of bounded norm,
intersected with a norm-congruence condition), the error is the number of lattice points within
O(t^{d−1}) of ∂𝒟. What regularity of ∂𝒟 is actually used (Lipschitz-parametrisable boundary?
finite perimeter? semialgebraic?), and what is the cleanest argument for that bound that does not
route through heavy machinery — ideally one we could reproduce on top of the leading-term
lattice-point limit already available?

**Q3 (the class-field-theory subtlety).** Is the analysis in §7 correct — namely that in the
cyclotomic case χ̃(𝔞) depends only on N𝔞 mod m, so the value-fibres are norm-congruence classes and
the count is class-field-theory-free; and that a general-abelian formulation would, by contrast,
require Artin reciprocity to know χ̃ factors through a finite quotient? Equivalently: is the right,
genuinely-CFT-free, statement to formalise the **cyclotomic/norm-congruence** count rather than a
general-abelian ideal-character count?

**Q4 (uniformity across congruence classes).** In the norm-congruence form, we need the leading
constant C to be the **same** for every residue class c mod m (that is what makes the Σ_ζ ζ = 0
cancellation work). Is the cleanest route to (i) prove the count for each fixed class with a class-
independent leading term and a uniform error, or (ii) prove the total count #{N𝔞 ≤ N} = C₀N +
O(N^{1−1/d}) once and then equidistribute over residue classes by an orthogonality argument? Which
is more economical to formalise, and does either hide a non-elementary input?

---

## 10. Document metadata

- Project: Chebotarev's density theorem (conjugacy-class form), class-field-theory-free,
  formalised in Lean 4 / Mathlib.
- Brief generated: 2026-06-05.
- Status at time of writing: the full theorem is assembled and machine-checked except for five
  named leaves, four of which have complete prose proofs in [Sharifi]/[SL] (the character-sum
  collapse, the analytic-extension Abel criterion, the compositum crossing, the Dirichlet-AP
  corollary) and are pure formalisation work; the fifth — the effective ideal count of §6 — is the
  one mathematically deferred by both sources and the subject of this brief.
- The complex-analytic boundedness of the twisted prime sum (§5) was completed immediately before
  this brief; with the geometry-of-numbers estimate in hand, the cyclotomic case — and through the
  two reductions, the whole theorem — closes.
