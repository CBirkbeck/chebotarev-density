module

public import CebotarevDensity.Frobenius

/-!
# Chebotarev's density theorem — statement

The theorem-level statement of Chebotarev's density theorem. The
supporting notions `HasDirichletDensity`, the unramified condition, and
`frobeniusClass` are the **real definitions** from
`CebotarevDensity.Density` and `CebotarevDensity.Frobenius` (no axioms);
the proof is left as `sorry`.
-/

@[expose] public section

noncomputable section

open NumberField

namespace Chebotarev

/-- **Chebotarev's density theorem.**

For a finite Galois extension `L/K` of number fields with Galois group `G`
and a conjugacy class `C ⊆ G`, the Dirichlet density of the set of primes
`𝔭` of `𝓞 K` unramified in `L` such that the Frobenius conjugacy class of
`𝔭` is `C` equals `|C| / |G|`. -/
theorem chebotarev_density
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (C : ConjClasses Gal(L/K)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ (𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal),
          𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt (𝓞 K) 𝔓) ∧
        frobeniusClass K L 𝔭 = C}
      ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K)) := by
  sorry

end Chebotarev
