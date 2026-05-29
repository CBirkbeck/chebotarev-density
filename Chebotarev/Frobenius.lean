module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Algebra.Group.Conj
public import Chebotarev.Density

/-!
# Frobenius element of a Galois extension of number fields

For a Galois extension `L/K` of number fields and a prime `𝔓` of `𝓞 L` that
is unramified over its image `𝔭 = 𝔓 ∩ 𝓞 K`, the Frobenius automorphism
`Frob 𝔓 ∈ Gal(L/K)` is the unique element of the decomposition group whose
action on `𝓞 L / 𝔓` is the `N𝔭`-th power. As `𝔓` ranges over the primes of
`𝓞 L` above a fixed `𝔭`, the Frobenius elements form a single conjugacy
class in `Gal(L/K)`. This conjugacy class is the *Frobenius substitution* of
`𝔭` and is the object whose distribution Chebotarev describes.

The mathlib counterpart `ValuationSubring.decompositionSubgroup`
(`Mathlib.RingTheory.Valuation.RamificationGroup`) is defined for valuation
subrings of `L`, not for prime ideals of `𝓞 L`; we restate using ideals,
exploiting the `Pointwise` action `Ideal.pointwiseDistribMulAction`.

## Main definitions

* `Chebotarev.UnramifiedIn` — `𝔭` is unramified in `L`.
* `Chebotarev.decompositionGroup` — the stabilizer of `𝔓`
  under the natural action of `Gal(L/K)` on ideals of `𝓞 L`.
* `Chebotarev.inertiaGroup` — the subgroup of
  `decompositionGroup` acting trivially on the residue field.
* `Chebotarev.frobeniusAt` — the Frobenius automorphism at
  an unramified prime `𝔓`, extracted via `Classical.choose` from the
  existence theorem `exists_unique_frobeniusAt`.
* `Chebotarev.frobeniusClass` — the conjugacy class of
  Frobenius elements above a prime `𝔭` of `K`.

## References

* Sharifi, *Algebraic Number Theory*, §2.6 (decomposition groups) and §7.2
  (`docs/algnum.pdf`).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, §3 (the
  Frobenius substitution) (`docs/cheb.pdf`).
-/

@[expose] public section

noncomputable section

open NumberField
open scoped Pointwise

namespace Chebotarev

/-- A prime `𝔭` of `𝓞 K` is unramified in `L` if every prime `𝔓` of `𝓞 L`
lying over `𝔭` has ramification index `1`. -/
def UnramifiedIn
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) : Prop :=
  ∀ (𝔓 : Ideal (𝓞 L)), 𝔓.IsPrime → 𝔓.LiesOver 𝔭 →
    Ideal.ramificationIdx 𝔭 𝔓 = 1

/-- The decomposition group at a prime `𝔓` of `𝓞 L`: the stabilizer of `𝔓`
under the natural `MulSemiringAction` of `Gal(L/K)` on ideals of `𝓞 L`
(via the action on the ring of integers and `Ideal.pointwiseMulSemiringAction`). -/
def decompositionGroup
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) : Subgroup Gal(L/K) :=
  MulAction.stabilizer Gal(L/K) 𝔓

/-- The inertia group at a prime `𝔓` of `𝓞 L`: the subgroup of `Gal(L/K)`
acting trivially modulo `𝔓` on every element of `𝓞 L`. This is mathlib's
`Ideal.inertia` instantiated at the natural action of `Gal(L/K)` on
`𝓞 L`; we keep the wrapper name for the Chebotarev-namespace API. -/
def inertiaGroup
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) : Subgroup Gal(L/K) :=
  Ideal.inertia Gal(L/K) 𝔓

/-! ### Sub-lemmas for `exists_unique_frobeniusAt`

Sharifi *Algebraic Number Theory* §2.6 (decomposition groups, not
reproduced in §7); standard textbook content. The proof decomposes as:

(i) For any prime `𝔓` of `𝓞 L`, the decomposition group surjects onto
    the residue Galois group via `IsFractionRing.stabilizerHom` (mathlib
    `Mathlib.RingTheory.Invariant.Basic`,
    `IsFractionRing.stabilizerHom_surjective`).
(ii) The kernel of this surjection is exactly the inertia group `I_𝔓`.
(iii) When `𝔓` is unramified over `𝔭 = 𝔓 ∩ 𝓞 K`, the inertia is trivial,
    so the surjection is an isomorphism.
(iv) The residue Galois group `Gal(κ(𝔓)/κ(𝔭))` is cyclic of order
    `f(𝔓|𝔭) = [κ(𝔓):κ(𝔭)]`, with canonical generator the absolute
    Frobenius `x ↦ x^{N𝔭}` (mathlib
    `FiniteField.frobeniusAlgEquivOfAlgebraic`).
(v) The unique preimage of the absolute Frobenius is the Frobenius
    `Frob_𝔓`.
-/

/-- For an unramified prime `𝔓`, the inertia group is trivial. This is
the substantive new content of the Frobenius-existence proof in the
unramified case: the other ingredients (surjection
`IsFractionRing.stabilizerHom_surjective`, residue-Galois Frobenius
`FiniteField.frobeniusAlgEquivOfAlgebraic`) are mathlib. -/
theorem inertiaGroup_trivial_of_unramified
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) (_hp : 𝔓.IsPrime) (_hnz : 𝔓 ≠ ⊥)
    (_hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) :
    inertiaGroup K L 𝔓 = ⊥ := by
  sorry

/-- **Frobenius existence when inertia is trivial** (the substantive
content of Sharifi Prop. 2.6.*). Given that the inertia group at `𝔓` is
trivial, the decomposition group surjects isomorphically onto the
residue Galois group `Gal(κ(𝔓)/κ(𝔭))`
(`IsFractionRing.stabilizerHom_surjective` + trivial kernel), which is
cyclic generated by the absolute Frobenius `x ↦ x^{N𝔭}`
(`FiniteField.frobeniusAlgEquivOfAlgebraic`); the unique preimage of that
generator is the desired `σ`. -/
theorem exists_unique_frobeniusAt_of_inertia_trivial
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) (_hp : 𝔓.IsPrime) (_hnz : 𝔓 ≠ ⊥) (_hI : inertiaGroup K L 𝔓 = ⊥) :
    ∃! σ : Gal(L/K), σ ∈ decompositionGroup K L 𝔓 ∧
      ∀ x : 𝓞 L,
        (Ideal.Quotient.mk 𝔓) (σ • x) =
          ((Ideal.Quotient.mk 𝔓) x) ^ Ideal.absNorm (𝔓.under (𝓞 K)) := by
  sorry

/-- **Existence and uniqueness of Frobenius at an unramified prime**.

For a Galois extension `L/K` of number fields and a nonzero prime `𝔓` of
`𝓞 L` lying over `𝔭 = 𝔓.under (𝓞 K)` with `𝔓` unramified over `𝓞 K`, there
is a unique `σ ∈ Gal(L/K)` stabilising `𝔓` and acting as the `N𝔭`-th power
on the residue field `𝓞 L / 𝔓`. This packages Sharifi Proposition 2.6.*
(over Dedekind domains). -/
theorem exists_unique_frobeniusAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) (hp : 𝔓.IsPrime) (hnz : 𝔓 ≠ ⊥)
    (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) :
    ∃! σ : Gal(L/K), σ ∈ decompositionGroup K L 𝔓 ∧
      ∀ x : 𝓞 L,
        (Ideal.Quotient.mk 𝔓) (σ • x) =
          ((Ideal.Quotient.mk 𝔓) x) ^ Ideal.absNorm (𝔓.under (𝓞 K)) :=
  exists_unique_frobeniusAt_of_inertia_trivial K L 𝔓 hp hnz <|
    inertiaGroup_trivial_of_unramified K L 𝔓 hp hnz hunr

/-- The Frobenius automorphism at a nonzero unramified prime `𝔓` of `𝓞 L`. -/
noncomputable def frobeniusAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) (hp : 𝔓.IsPrime) (hnz : 𝔓 ≠ ⊥)
    (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) :
    Gal(L/K) :=
  (exists_unique_frobeniusAt K L 𝔓 hp hnz hunr).exists.choose

/-- The Frobenius automorphism stabilises `𝔓` and acts as the `N𝔭`-th power
on the residue field. -/
theorem frobeniusAt_spec
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) (hp : 𝔓.IsPrime) (hnz : 𝔓 ≠ ⊥)
    (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) :
    frobeniusAt K L 𝔓 hp hnz hunr ∈ decompositionGroup K L 𝔓 ∧
      ∀ x : 𝓞 L,
        (Ideal.Quotient.mk 𝔓) (frobeniusAt K L 𝔓 hp hnz hunr • x) =
          ((Ideal.Quotient.mk 𝔓) x) ^ Ideal.absNorm (𝔓.under (𝓞 K)) :=
  (exists_unique_frobeniusAt K L 𝔓 hp hnz hunr).exists.choose_spec

/-- For a prime `𝔭` of `𝓞 K` unramified in `L`, any two Frobenius elements
above `𝔭` are conjugate in `Gal(L/K)` — the conjugating element witnesses
transitivity of the Galois action on primes above `𝔭`. -/
theorem frobeniusAt_isConj_of_liesOver
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) (_hpr : 𝔭.IsPrime) (_hnz_𝔭 : 𝔭 ≠ ⊥) (hunr : UnramifiedIn K L 𝔭)
    (𝔓 𝔓' : Ideal (𝓞 L)) (hp : 𝔓.IsPrime) (hP : 𝔓.LiesOver 𝔭) (hnz : 𝔓 ≠ ⊥) (hp' : 𝔓'.IsPrime)
    (hP' : 𝔓'.LiesOver 𝔭) (hnz' : 𝔓' ≠ ⊥) :
    IsConj
      (frobeniusAt K L 𝔓 hp hnz
        (by rw [show 𝔓.under (𝓞 K) = 𝔭 from hP.over.symm]; exact hunr 𝔓 hp hP))
      (frobeniusAt K L 𝔓' hp' hnz'
        (by rw [show 𝔓'.under (𝓞 K) = 𝔭 from hP'.over.symm]; exact hunr 𝔓' hp' hP')) := by
  sorry

/-- Existence (and uniqueness, by conjugacy-class collapse) of the Frobenius
conjugacy class of an unramified prime `𝔭` of `𝓞 K`.
Sharifi §7.2 + SL Appendix paragraph 1. -/
theorem exists_frobeniusClass
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) (hpr : 𝔭.IsPrime) (hnz_𝔭 : 𝔭 ≠ ⊥) (hunr : UnramifiedIn K L 𝔭) :
    ∃ C : ConjClasses Gal(L/K),
      ∀ (𝔓 : Ideal (𝓞 L)) (hp : 𝔓.IsPrime) (hP : 𝔓.LiesOver 𝔭) (hnz : 𝔓 ≠ ⊥),
        C = ConjClasses.mk (frobeniusAt K L 𝔓 hp hnz
          (by rw [show 𝔓.under (𝓞 K) = 𝔭 from hP.over.symm]; exact hunr 𝔓 hp hP)) := by
  sorry

/-- The Frobenius conjugacy class of a prime `𝔭` of `𝓞 K`. When `𝔭` is a
nonzero unramified prime, this is the conjugacy class of `frobeniusAt 𝔓` for
any prime `𝔓` of `𝓞 L` above `𝔭` (well-definedness from
`exists_frobeniusClass`). For other primes the value is the trivial class —
a junk value never used in the Chebotarev statement (which always restricts
to unramified nonzero primes). -/
noncomputable def frobeniusClass
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) : ConjClasses Gal(L/K) := by
  classical
  exact
    if h : 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 then
      (exists_frobeniusClass K L 𝔭 h.1 h.2.1 h.2.2).choose
    else
      ConjClasses.mk 1

/-- `frobeniusClass K L 𝔭` is the conjugacy class of `frobeniusAt 𝔓` for any
prime `𝔓` of `𝓞 L` above `𝔭`. -/
theorem frobeniusClass_eq_mk_frobeniusAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) (hpr : 𝔭.IsPrime) (hnz_𝔭 : 𝔭 ≠ ⊥) (hunr : UnramifiedIn K L 𝔭)
    (𝔓 : Ideal (𝓞 L)) (hp : 𝔓.IsPrime) (hP : 𝔓.LiesOver 𝔭) (hnz : 𝔓 ≠ ⊥) :
    frobeniusClass K L 𝔭 =
      ConjClasses.mk (frobeniusAt K L 𝔓 hp hnz
        (by rw [show 𝔓.under (𝓞 K) = 𝔭 from hP.over.symm]; exact hunr 𝔓 hp hP)) := by
  rw [frobeniusClass, dif_pos ⟨hpr, hnz_𝔭, hunr⟩]
  exact (exists_frobeniusClass K L 𝔭 hpr hnz_𝔭 hunr).choose_spec 𝔓 hp hP hnz

/-- Only finitely many nonzero primes of `K` ramify in `L`. -/
theorem finite_ramifiedIn
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭}.Finite := by
  sorry

end Chebotarev
