import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import CebotarevDensity.Frobenius

/-!
# Comparator challenge: the headline Chebotarev statements

The four main results of the project, stated with `sorry` proofs, for
verification by [leanprover/comparator](https://github.com/leanprover/comparator)
against the real proofs in `CebotarevDensity.Main` (the solution module):
identical statements, axiom budget `[propext, Classical.choice, Quot.sound]`,
and kernel acceptance.

This module imports only the definition layer (`CebotarevDensity.Frobenius`,
transitively `Density`) — NOT `Main` — so the statements here are independent
restatements. It is intentionally excluded from the default build targets.
-/

set_option linter.unusedVariables false

open Filter NumberField Topology Set

namespace Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- Chebotarev density, conjugacy-class form. -/
theorem chebotarev_density
    [FiniteDimensional K L] (C : ConjClasses Gal(L/K)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = C}
      ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K)) := by
  sorry

/-- Chebotarev density, abelian case. -/
theorem chebotarev_density_of_comm
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (C : ConjClasses Gal(L/K)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = C}
      ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K)) := by
  sorry

/-- The density of primes splitting completely is `1/[L:K]`. -/
theorem density_split_completely :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = ConjClasses.mk 1}
      ((Module.finrank K L : ℝ)⁻¹) := by
  sorry

/-- Dirichlet's theorem on primes in arithmetic progressions, in
Dirichlet-density form over `𝓞 ℚ`. -/
theorem dirichlet_primes_in_AP (n : ℕ) (hn : 1 ≤ n) (a : ZMod n) (ha : IsUnit a) :
    HasDirichletDensity
      ((fun p : ℕ ↦ Ideal.span {(p : 𝓞 ℚ)}) ''
        {p : ℕ | p.Prime ∧ (p : ZMod n) = a})
      ((Nat.totient n : ℝ)⁻¹) := by
  sorry

end Chebotarev
