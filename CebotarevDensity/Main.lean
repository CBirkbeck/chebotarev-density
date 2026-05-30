module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Algebra.Group.Conj

/-!
# Chebotarev density theorem

This branch contains only the theorem-level statement of Chebotarev's
density theorem. The supporting definitions are declared as the public
interface needed to state the result; the theorem proof is intentionally
left as `sorry`.
-/

@[expose] public section

noncomputable section

open NumberField

namespace Chebotarev

/-- The assertion that a set of prime ideals of `𝓞 K` has Dirichlet density `δ`. -/
axiom HasDirichletDensity
    (K : Type*) [Field K] [NumberField K] (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop

/-- A prime of `𝓞 K` is unramified in the extension `L/K`. -/
axiom UnramifiedIn
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (𝔭 : Ideal (𝓞 K)) : Prop

/-- The Frobenius conjugacy class of a prime of `𝓞 K` in `Gal(L/K)`. -/
axiom frobeniusClass
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (𝔭 : Ideal (𝓞 K)) : ConjClasses Gal(L/K)

/-- **Chebotarev's density theorem.**

For a finite Galois extension `L/K` of number fields with Galois group `G`
and a conjugacy class `C ⊆ G`, the Dirichlet density of the set of primes
`𝔭` of `𝓞 K` unramified in `L` such that the Frobenius conjugacy class of
`𝔭` is `C` equals `|C| / |G|`. -/
theorem chebotarev_density
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (C : ConjClasses Gal(L/K)) :
    HasDirichletDensity K
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = C}
      ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K)) := by
  sorry

end Chebotarev
