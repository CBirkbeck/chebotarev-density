module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Frobenius

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

* `Chebotarev.UnramifiedIn` — `𝔭` is unramified in `L`.
* `Chebotarev.frobeniusClass` — the conjugacy class of
  Frobenius elements above a prime `𝔭` of `K`.

The Frobenius automorphism itself is mathlib's `arithFrobAt (𝓞 K) Gal(L/K) 𝔓`,
characterised among elements of `Gal(L/K)` by `IsArithFrobAt (𝓞 K) · 𝔓`; this
file does not wrap it.

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

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- A prime `𝔭` of `𝓞 K` is unramified in `L` if every **maximal** prime `𝔓` of `𝓞 L`
lying over `𝔭` is unramified over `𝓞 K` (`Algebra.IsUnramifiedAt`). The `∀ 𝔓` clause has the
same shape as the unramified condition in mathlib's
`NumberField.not_dvd_discr_iff_forall_liesOver`. Nonzeroness of `𝔭` is **not** part of this
predicate: lemmas that need a finite residue field `𝓞 L ⧸ 𝔓` (e.g. for the Frobenius
`arithFrobAt 𝔓`) take `𝔭 ≠ ⊥` as a separate hypothesis. For nonzero `𝔭` the maximal primes
over `𝔭` are exactly its prime divisors, so each has `e(𝔓 ∣ 𝔭) = 1`
(`Algebra.isUnramifiedAt_iff_of_isDedekindDomain`). -/
def UnramifiedIn [IsGalois K L] (𝔭 : Ideal (𝓞 K)) : Prop :=
  ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal), 𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt (𝓞 K) 𝔓

/-- A prime of `𝓞 L` with ramification index `1` over its image in `𝓞 K` is nonzero:
the zero ideal has ramification index `0` (`Ideal.ramificationIdx_bot`). -/
theorem ne_bot_of_ramificationIdx_eq_one {𝔓 : Ideal (𝓞 L)}
    (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) : 𝔓 ≠ ⊥ := by
  rintro rfl
  simp at hunr

variable [NumberField K] [NumberField L]

/-- For a prime `𝔓` of `𝓞 L` lying over an unramified prime `𝔭` of `𝓞 K`,
the ramification index `e(𝔓 ∣ 𝔭)` equals `1`. -/
theorem UnramifiedIn.ramificationIdx_eq_one [IsGalois K L] {𝔭 : Ideal (𝓞 K)} [NeZero 𝔭]
    (hunr : UnramifiedIn K L 𝔭) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hP : 𝔓.LiesOver 𝔭) :
    Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1 := by
  have h𝔭 : 𝔭 ≠ ⊥ := NeZero.ne 𝔭
  have h𝔓 : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 𝔓
  exact (Algebra.isUnramifiedAt_iff_of_isDedekindDomain h𝔓).mp
    (hunr 𝔓 (‹𝔓.IsPrime›.isMaximal h𝔓) hP)

/-- A Frobenius element at an unramified prime `𝔓` is the canonical `arithFrobAt 𝔓`: the
residue-field characterisation pins it down uniquely
(`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`, transferred to `Gal(L/K)` via the faithful
action on `𝓞 L`). -/
private theorem eq_arithFrobAt_of_isArithFrobAt [IsGalois K L] (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    [Finite (𝓞 L ⧸ 𝔓)] [Algebra.IsUnramifiedAt (𝓞 K) 𝔓] (σ : Gal(L/K))
    (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) :
    σ = arithFrobAt (𝓞 K) Gal(L/K) 𝔓 := by
  haveI : FaithfulSMul Gal(L/K) (𝓞 L) := IsGaloisGroup.faithful (𝓞 K)
  apply MulSemiringAction.toAlgHom_injective (𝓞 K) (𝓞 L)
  exact AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hσ
    (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) 𝔓.primeCompl_le_nonZeroDivisors

/-- For a prime `𝔭` of `𝓞 K` unramified in `L`, any two elements `σ`, `σ'` of `Gal(L/K)`
that are arithmetic Frobenius elements (`IsArithFrobAt`) at primes `𝔓`, `𝔓'` above `𝔭` are
conjugate: each equals `arithFrobAt` at its prime (`eq_arithFrobAt_of_isArithFrobAt`), and
the two `arithFrobAt`s lie over the same `𝔭`, so `isConj_arithFrobAt` applies. -/
theorem isConj_of_isArithFrobAt [IsGalois K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] [NeZero 𝔭]
    (hunr : UnramifiedIn K L 𝔭) (σ σ' : Gal(L/K))
    (𝔓 𝔓' : Ideal (𝓞 L)) [𝔓.IsPrime] [𝔓'.IsPrime]
    (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) (hσ' : IsArithFrobAt (𝓞 K) σ' 𝔓') (hP : 𝔓.LiesOver 𝔭)
    (hP' : 𝔓'.LiesOver 𝔭) :
    IsConj σ σ' := by
  have h𝔭 : 𝔭 ≠ ⊥ := NeZero.ne 𝔭
  have : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
    (ne_bot_of_ramificationIdx_eq_one K L (UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓 hP))
  have : Finite (𝓞 L ⧸ 𝔓') := Ideal.finiteQuotientOfFreeOfNeBot 𝔓'
    (ne_bot_of_ramificationIdx_eq_one K L (UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓' hP'))
  have : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
    hunr 𝔓 (‹𝔓.IsPrime›.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 𝔓)) hP
  have : Algebra.IsUnramifiedAt (𝓞 K) 𝔓' :=
    hunr 𝔓' (‹𝔓'.IsPrime›.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 𝔓')) hP'
  rw [eq_arithFrobAt_of_isArithFrobAt K L 𝔓 σ hσ,
    eq_arithFrobAt_of_isArithFrobAt K L 𝔓' σ' hσ']
  exact isConj_arithFrobAt (𝓞 K) Gal(L/K) 𝔓 𝔓' (hP.over.symm.trans hP'.over)

/-- Existence and well-definedness of the Frobenius conjugacy class of an unramified
prime `𝔭` of `𝓞 K`: there is a single conjugacy class `C` such that `C = ConjClasses.mk σ`
for every `σ` that is an arithmetic Frobenius (`IsArithFrobAt`) at some prime `𝔓` of
`𝓞 L` above `𝔭`.
Sharifi §7.2 + SL Appendix paragraph 1. -/
theorem exists_frobeniusClass [IsGalois K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] [NeZero 𝔭]
    (hunr : UnramifiedIn K L 𝔭) :
    ∃ C : ConjClasses Gal(L/K),
      ∀ (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (_ : IsArithFrobAt (𝓞 K) σ 𝔓)
        (_ : 𝔓.LiesOver 𝔭), C = ConjClasses.mk σ := by
  obtain ⟨𝔓₀, hp₀, hcomap₀⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔭 (by simp)
  have hlo₀ : 𝔓₀.LiesOver 𝔭 := ⟨hcomap₀.symm⟩
  have : Finite (𝓞 L ⧸ 𝔓₀) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓₀
    (ne_bot_of_ramificationIdx_eq_one K L
      (UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓₀ hlo₀))
  refine ⟨ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀), fun σ 𝔓 _ hσ hP => ?_⟩
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_of_isArithFrobAt K L 𝔭 hunr
    (arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀) σ 𝔓₀ 𝔓
    (hσ := IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀) (hσ' := hσ) (hP := hlo₀) (hP' := hP))

/-- The Frobenius conjugacy class of a prime `𝔭` of `𝓞 K`. When `𝔭` is a
nonzero unramified prime, this is the conjugacy class of any arithmetic Frobenius `σ`
(`IsArithFrobAt`) at any prime `𝔓` of `𝓞 L` above `𝔭` (well-definedness from
`exists_frobeniusClass`). For other primes the value is the trivial class —
a junk value never used in the Chebotarev statement (which always restricts
to unramified nonzero primes). -/
def frobeniusClass [IsGalois K L] (𝔭 : Ideal (𝓞 K)) : ConjClasses Gal(L/K) :=
  open Classical in
  if h : 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ UnramifiedIn K L 𝔭 then
    haveI := h.1
    haveI : NeZero 𝔭 := ⟨h.2.1⟩
    (exists_frobeniusClass K L 𝔭 h.2.2).choose
  else
    ConjClasses.mk 1

/-- `frobeniusClass K L 𝔭` is the conjugacy class of any arithmetic Frobenius `σ`
(`IsArithFrobAt (𝓞 K) σ 𝔓`) at any prime `𝔓` of `𝓞 L` above `𝔭`. -/
theorem frobeniusClass_eq_mk_of_isArithFrobAt [IsGalois K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    [NeZero 𝔭] (hunr : UnramifiedIn K L 𝔭) (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) (hP : 𝔓.LiesOver 𝔭) :
    frobeniusClass K L 𝔭 = ConjClasses.mk σ := by
  have h𝔭 : 𝔭 ≠ ⊥ := NeZero.ne 𝔭
  rw [frobeniusClass, dif_pos ⟨‹𝔭.IsPrime›, h𝔭, hunr⟩]
  exact (exists_frobeniusClass K L 𝔭 hunr).choose_spec σ 𝔓 hσ hP

/-- Only finitely many nonzero primes of `K` ramify in `L`. -/
theorem finite_ramifiedIn [IsGalois K L] :
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭}.Finite := by
  have hbot : differentIdeal (𝓞 K) (𝓞 L) ≠ 0 := by
    rw [Ideal.zero_eq_bot]; exact differentIdeal_ne_bot
  apply Set.Finite.subset ((Ideal.finite_factors hbot).image (fun v ↦ (v.asIdeal).under (𝓞 K)))
  rintro 𝔭 ⟨-, h𝔭bot, hnunr⟩
  rw [UnramifiedIn, not_forall] at hnunr
  obtain ⟨𝔓, h𝔓⟩ := hnunr
  rw [not_forall] at h𝔓
  obtain ⟨h𝔓max, h𝔓⟩ := h𝔓
  rw [not_forall] at h𝔓
  obtain ⟨h𝔓lo, h𝔓nu⟩ := h𝔓
  have h𝔓bot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭bot 𝔓
  have hdvd : 𝔓 ∣ differentIdeal (𝓞 K) (𝓞 L) := by
    by_contra h
    exact h𝔓nu (not_dvd_differentIdeal_iff.mp h)
  exact ⟨⟨𝔓, h𝔓max.isPrime, h𝔓bot⟩, hdvd, h𝔓lo.over.symm⟩

end Chebotarev
