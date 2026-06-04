module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.RamificationInertia.Inertia

public import CebotarevDensity.Density

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

* `Chebotarev.frobeniusAt` — the Frobenius automorphism at
  an unramified prime `𝔓`, namely mathlib's `arithFrobAt` for the
  action of `Gal(L/K)` on `𝓞 L`.
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

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
/-- A prime of `𝓞 L` with ramification index `1` over its image in `𝓞 K` is nonzero:
the zero ideal has ramification index `0` (`Ideal.ramificationIdx_bot`). -/
theorem ne_bot_of_ramificationIdx_eq_one
    {𝔓 : Ideal (𝓞 L)} (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) : 𝔓 ≠ ⊥ := by
  rintro rfl
  simp at hunr

/-- For a prime `𝔓` of `𝓞 L` lying over a nonzero prime `𝔭` of `𝓞 K`, all of whose maximal
primes over `𝔭` are unramified over `𝓞 K` (`Algebra.IsUnramifiedAt`), the ramification index
`e(𝔓 ∣ 𝔭)` equals `1`. The nonzeroness of `𝔭` forces `𝔓 ≠ ⊥` (hence `𝔓` maximal), and then
`Algebra.isUnramifiedAt_iff_of_isDedekindDomain` converts unramifiedness to `e = 1`. -/
theorem ramificationIdx_eq_one_of_isUnramifiedAt
    [IsGalois K L]
    {𝔭 : Ideal (𝓞 K)}
    (hunr : 𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal), 𝔓.LiesOver 𝔭 →
      Algebra.IsUnramifiedAt (𝓞 K) 𝔓)
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭) :
    Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1 := by
  have h𝔓 : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓
  exact (Algebra.isUnramifiedAt_iff_of_isDedekindDomain h𝔓).mp
    (hunr.2 𝔓 (‹𝔓.IsPrime›.isMaximal h𝔓) hP)

/-- The Frobenius automorphism at an unramified prime `𝔓` of `𝓞 L`: mathlib's
`arithFrobAt` for the `𝓞 K`-action of `Gal(L/K)` on `𝓞 L`. -/
def frobeniusAt
    [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) :
    Gal(L/K) :=
  haveI : Finite (𝓞 L ⧸ 𝔓) :=
    Ideal.finiteQuotientOfFreeOfNeBot 𝔓 (ne_bot_of_ramificationIdx_eq_one K L hunr)
  arithFrobAt (𝓞 K) Gal(L/K) 𝔓

/-- The Frobenius automorphism stabilises `𝔓` and acts as the `N𝔭`-th power
on the residue field. -/
theorem frobeniusAt_spec
    [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) :
    frobeniusAt K L 𝔓 hunr ∈ MulAction.stabilizer Gal(L/K) 𝔓 ∧
      ∀ x : 𝓞 L,
        (Ideal.Quotient.mk 𝔓) (frobeniusAt K L 𝔓 hunr • x) =
          ((Ideal.Quotient.mk 𝔓) x) ^ Ideal.absNorm (𝔓.under (𝓞 K)) := by
  haveI : Finite (𝓞 L ⧸ 𝔓) :=
    Ideal.finiteQuotientOfFreeOfNeBot 𝔓 (ne_bot_of_ramificationIdx_eq_one K L hunr)
  exact ⟨IsArithFrobAt.arithFrobAt_mem_stabilizer (𝓞 K) Gal(L/K) 𝔓,
    (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓).mk_apply⟩

/-- For a prime `𝔭` of `𝓞 K` unramified in `L`, any two Frobenius elements
above `𝔭` are conjugate in `Gal(L/K)`: both are `arithFrobAt` at primes lying over the
same prime `𝔭`, so `isConj_arithFrobAt` applies. -/
theorem frobeniusAt_isConj_of_liesOver
    [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (hunr : 𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal), 𝔓.LiesOver 𝔭 →
      Algebra.IsUnramifiedAt (𝓞 K) 𝔓)
    (𝔓 𝔓' : Ideal (𝓞 L)) [𝔓.IsPrime] [𝔓'.IsPrime] (hP : 𝔓.LiesOver 𝔭) (hP' : 𝔓'.LiesOver 𝔭) :
    IsConj (frobeniusAt K L 𝔓 (ramificationIdx_eq_one_of_isUnramifiedAt K L hunr 𝔓 hP))
      (frobeniusAt K L 𝔓' (ramificationIdx_eq_one_of_isUnramifiedAt K L hunr 𝔓' hP')) := by
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
    (ne_bot_of_ramificationIdx_eq_one K L (ramificationIdx_eq_one_of_isUnramifiedAt K L hunr 𝔓 hP))
  haveI : Finite (𝓞 L ⧸ 𝔓') := Ideal.finiteQuotientOfFreeOfNeBot 𝔓'
    (ne_bot_of_ramificationIdx_eq_one K L
      (ramificationIdx_eq_one_of_isUnramifiedAt K L hunr 𝔓' hP'))
  exact isConj_arithFrobAt (𝓞 K) Gal(L/K) 𝔓 𝔓' (hP.over.symm.trans hP'.over)

omit [NumberField K] [NumberField L] in
/-- A nonzero prime `𝔭` of `𝓞 K` has at least one prime `𝔓` of `𝓞 L` lying
over it, and any such `𝔓` is nonzero (going-up for the integral extension
`𝓞 K ⊆ 𝓞 L`; nonzero because `𝔭` is and `algebraMap (𝓞 K) (𝓞 L)` is injective). -/
theorem exists_prime_liesOver
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hnz : 𝔭 ≠ ⊥) :
    ∃ 𝔓 : Ideal (𝓞 L), 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥ := by
  obtain ⟨𝔓, hp, hcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔭 (by simp)
  haveI : 𝔓.LiesOver 𝔭 := ⟨hcomap.symm⟩
  exact ⟨𝔓, hp, ⟨hcomap.symm⟩, Ideal.ne_bot_of_liesOver_of_ne_bot hnz 𝔓⟩

/-- Existence and well-definedness of the Frobenius
conjugacy class of an unramified prime `𝔭` of `𝓞 K`.
Sharifi §7.2 + SL Appendix paragraph 1. -/
theorem exists_frobeniusClass
    [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (hunr : 𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal), 𝔓.LiesOver 𝔭 →
      Algebra.IsUnramifiedAt (𝓞 K) 𝔓) :
    ∃ C : ConjClasses Gal(L/K),
      ∀ (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭),
        C = ConjClasses.mk (frobeniusAt K L 𝔓
          (ramificationIdx_eq_one_of_isUnramifiedAt K L hunr 𝔓 hP)) := by
  obtain ⟨𝔓₀, hp₀, hlo₀, _⟩ := exists_prime_liesOver K L 𝔭 hunr.1
  refine ⟨ConjClasses.mk (frobeniusAt K L 𝔓₀
    (ramificationIdx_eq_one_of_isUnramifiedAt K L hunr 𝔓₀ hlo₀)), ?_⟩
  intro 𝔓 _ hP
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (frobeniusAt_isConj_of_liesOver K L 𝔭 hunr 𝔓₀ 𝔓 hlo₀ hP)

/-- The Frobenius conjugacy class of a prime `𝔭` of `𝓞 K`. When `𝔭` is a
nonzero unramified prime, this is the conjugacy class of `frobeniusAt 𝔓` for
any prime `𝔓` of `𝓞 L` above `𝔭` (well-definedness from
`exists_frobeniusClass`). For other primes the value is the trivial class —
a junk value never used in the Chebotarev statement (which always restricts
to unramified nonzero primes). -/
def frobeniusClass
    [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) : ConjClasses Gal(L/K) :=
  open Classical in
  if h : 𝔭.IsPrime ∧ (𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal), 𝔓.LiesOver 𝔭 →
      Algebra.IsUnramifiedAt (𝓞 K) 𝔓) then
    haveI := h.1
    (exists_frobeniusClass K L 𝔭 h.2).choose
  else
    ConjClasses.mk 1

/-- `frobeniusClass K L 𝔭` is the conjugacy class of `frobeniusAt 𝔓` for any
prime `𝔓` of `𝓞 L` above `𝔭`. -/
theorem frobeniusClass_eq_mk_frobeniusAt
    [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (hunr : 𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal), 𝔓.LiesOver 𝔭 →
      Algebra.IsUnramifiedAt (𝓞 K) 𝔓)
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭) :
    frobeniusClass K L 𝔭 =
      ConjClasses.mk (frobeniusAt K L 𝔓
        (ramificationIdx_eq_one_of_isUnramifiedAt K L hunr 𝔓 hP)) := by
  rw [frobeniusClass, dif_pos ⟨‹𝔭.IsPrime›, hunr⟩]
  exact (exists_frobeniusClass K L 𝔭 hunr).choose_spec 𝔓 hP

/-- Only finitely many nonzero primes of `K` ramify in `L`. -/
theorem finite_ramifiedIn
    [IsGalois K L] :
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ (𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal),
      𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt (𝓞 K) 𝔓)}.Finite := by
  letI : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
    FractionRing.liftAlgebra (𝓞 K) (FractionRing (𝓞 L))
  haveI : IsScalarTower (𝓞 K) (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
    FractionRing.isScalarTower_liftAlgebra (𝓞 K) (FractionRing (𝓞 L))
  haveI : Algebra.IsSeparable (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := inferInstance
  have hbot : differentIdeal (𝓞 K) (𝓞 L) ≠ 0 := by
    rw [Ideal.zero_eq_bot]; exact differentIdeal_ne_bot
  apply Set.Finite.subset
    ((Ideal.finite_factors hbot).image (fun v => (v.asIdeal).under (𝓞 K)))
  rintro 𝔭 ⟨-, h𝔭bot, hnunr⟩
  rw [not_and, not_forall] at hnunr
  obtain ⟨𝔓, h𝔓⟩ := hnunr h𝔭bot
  rw [not_forall] at h𝔓
  obtain ⟨h𝔓max, h𝔓⟩ := h𝔓
  rw [not_forall] at h𝔓
  obtain ⟨h𝔓lo, h𝔓nu⟩ := h𝔓
  haveI := h𝔓max.isPrime
  haveI := h𝔓lo
  have h𝔓bot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭bot 𝔓
  have hdvd : 𝔓 ∣ differentIdeal (𝓞 K) (𝓞 L) := by
    by_contra h
    exact h𝔓nu (not_dvd_differentIdeal_iff.mp h)
  exact ⟨⟨𝔓, h𝔓max.isPrime, h𝔓bot⟩, hdvd, h𝔓lo.over.symm⟩

end Chebotarev
