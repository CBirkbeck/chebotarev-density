# Reply integration — 2026-06-05

Reply received from an external analytic-number-theory reviewer on 2026-06-05.
Brief: ./brief.md · Reply: ./reply.md

## Interpretation summary

| # | Reviewer point | Maps to | Type |
|---|----------------|---------|------|
| 1 | The right object is **Lang's ray/generalized ideal-class count** (Lang GTM 110 Ch. VI §3 Thm 3; modern: Gun–Ramaré–Sivaraman JNT 243 (2023) Thm 1), NOT a bare norm-residue count. `#{(𝔞,𝔮)=1, [𝔞]_𝔮=A, N𝔞≤X} = ρ_𝔮X + O(X^{1−1/d})`, ρ_𝔮 class-independent. | Q1 | direct answer + precise refs |
| 2 | Proof: Lipschitz-boundary lattice-point count `#((v+Λ)∩tD)=(vol/covol)tᵈ+O(tᵈ⁻¹)` (Lang p.129), then t=X^{1/d}. Boundary regularity to formalise = **finite Lipschitz parametrisability of ∂D**. 1−1/d is the natural exponent. | Q2 | direct answer |
| 3 | **CORRECTION:** norm-residue framing is FALSE (ℚ(i): odd norms always ≡1 mod 4). Ray classes are the equidistributed object; norm-residue fibres are unions of ray classes. Cyclotomic χ̃ factors through a ray class group via θ(𝔞)=ζ_m^{N𝔞} — ELEMENTARY (norm/Frobenius), no CFT. General-abelian factorisation IS Artin reciprocity → must stay in the cyclotomic case. | Q3 | direct answer + corrects brief §7 |
| 4 | Route (i): ray-class count → nontrivial ray-class char sums O(X^{1−1/d}) → specialise cyclotomic char to ray-class char. Cleaner than total-count-then-equidistribute. | Q4 | direct answer |

All four questions answered; no UNANSWERED items.

## Architecture change applied

The single general-abelian geometry-of-numbers leaf
`exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow` (value-fibre count of a general-abelian
ideal character — TRUE but only CFT-provable, hence wrong generality for this CFT-free project) is
**superseded** by a four-leaf CFT-free ray-class chain:

1. **lattice-point count** — `#((v+Λ)∩tD) = (vol D/covol Λ)tᵈ + O(tᵈ⁻¹)` for Λ a full lattice and ∂D
   covered by finitely many Lipschitz charts. The deep, mathlib-PR-able core (upgrades mathlib's
   leading-term `ZLattice.covolume.tendsto_card_div_pow`). Source: Lang GTM 110 Ch. V §2 / p.129;
   Widmer's lattice-point theorem (via GRS).
2. **ray-class count** — `∀ A ∈ Cl_𝔮, #{(𝔞,𝔮)=1, [𝔞]_𝔮=A, N𝔞≤X} = ρ_𝔮X + O(X^{1−1/d})`, ρ_𝔮
   class-independent. Source: Lang Ch. VI §3 Thm 3; GRS Thm 1. Built from leaf 1 + the ideal↔lattice
   dictionary (mostly in mathlib).
3. **ray-class character sum** — nontrivial ray-class character ψ ⟹ `Σ_{N𝔞≤X} ψ(𝔞) = O(X^{1−1/d})`.
   Elementary orthogonality on leaf 2.
4. **cyclotomic factorisation** — `χ̃ = χ∘Frob` for K(μ_m)/K factors through `Cl_𝔮` via
   `θ(𝔞)=ζ_m^{N𝔞}`. Elementary norm/Frobenius, no CFT.

`character_sum_geometry_of_numbers_bound` (and, where it consumes the count, the analytic-extension
leaf) are **restated at cyclotomic generality** — they are only ever used cyclotomically (the abelian
case reduces to cyclotomic via the compositum crossing before invoking the L-function machinery), so
this is a scope-tightening to match where the CFT-free path exists.

## References added

- Lang, *Algebraic Number Theory*, 2nd ed., GTM 110, Springer 1994 — Ch. V §2 (lattice-point
  theorem), Ch. VI §3 Thm 3 (ray-class count), p.129 (boundary-error argument).
- Gun, Ramaré, Sivaraman, "Counting ideals in ray classes," J. Number Theory 243 (2023), Thm 1.
  https://ramare-olivier.github.io/Maths/CountingIdeals-jnt.pdf
- Widmer, lattice-point theorem for bounded sets with Lipschitz boundary (cited by GRS).

## Open questions remaining

None — all four questions answered.

## Decisions recorded

- Formalise route (i): ray-class count → ray-class char sum → cyclotomic specialisation.
- Formalise the **norm-congruence/cyclotomic** statement via **ray classes**, never the
  false general norm-residue equidistribution.
- Next step: `/develop --decompose` on the four-leaf ray-class chain (lay out the skeleton with
  Lang/GRS source locators per leaf + adversarial attacks).
