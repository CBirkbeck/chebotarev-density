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

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- A prime `𝔭` of `𝓞 K` is unramified in `L` if it is nonzero and every **maximal** prime
`𝔓` of `𝓞 L` lying over `𝔭` is unramified over `𝓞 K` (`Algebra.IsUnramifiedAt`). The `∀ 𝔓`
clause has the same shape as the unramified condition in mathlib's
`NumberField.not_dvd_discr_iff_forall_liesOver`. The `𝔭 ≠ ⊥` clause (on the base prime) is
kept because the Frobenius `arithFrobAt 𝔓` needs a finite residue field `𝓞 L ⧸ 𝔓`; for nonzero
`𝔭` the maximal primes over `𝔭` are exactly its prime divisors, so each has `e(𝔓 ∣ 𝔭) = 1`
(`Algebra.isUnramifiedAt_iff_of_isDedekindDomain`). -/
def UnramifiedIn
    [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) : Prop :=
  𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal), 𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt (𝓞 K) 𝔓

omit [NumberField K] [NumberField L] in
/-- A prime of `𝓞 L` with ramification index `1` over its image in `𝓞 K` is nonzero:
the zero ideal has ramification index `0` (`Ideal.ramificationIdx_bot`). -/
theorem ne_bot_of_ramificationIdx_eq_one
    {𝔓 : Ideal (𝓞 L)} (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) : 𝔓 ≠ ⊥ := by
  rintro rfl
  simp at hunr

omit [NumberField K] [NumberField L] in
/-- An unramified prime is nonzero — the first clause of `UnramifiedIn`. -/
theorem UnramifiedIn.ne_bot
    [IsGalois K L]
    {𝔭 : Ideal (𝓞 K)} (hunr : UnramifiedIn K L 𝔭) : 𝔭 ≠ ⊥ :=
  hunr.1

/-- For a prime `𝔓` of `𝓞 L` lying over an unramified prime `𝔭` of `𝓞 K`,
the ramification index `e(𝔓 ∣ 𝔭)` equals `1`. -/
theorem UnramifiedIn.ramificationIdx_eq_one
    [IsGalois K L]
    {𝔭 : Ideal (𝓞 K)} (hunr : UnramifiedIn K L 𝔭) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hP : 𝔓.LiesOver 𝔭) : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1 := by
  haveI := hP
  have h𝔓 : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓
  exact (Algebra.isUnramifiedAt_iff_of_isDedekindDomain h𝔓).mp
    (hunr.2 𝔓 (‹𝔓.IsPrime›.isMaximal h𝔓) hP)

/-- For an unramified prime `𝔓`, the inertia group is trivial: by
`Ideal.card_inertia_eq_ramificationIdxIn` its cardinality equals the ramification index
`e(𝔓 ∣ 𝔭) = 1`, and a subgroup of cardinality one is trivial (`Subgroup.eq_bot_iff_card`). -/
theorem inertiaGroup_trivial_of_unramified
    [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) :
    Ideal.inertia Gal(L/K) 𝔓 = ⊥ := by
  have hPbot : 𝔓 ≠ ⊥ := ne_bot_of_ramificationIdx_eq_one K L hunr
  have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
  haveI : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
  haveI : (𝔓.under (𝓞 K)).IsMaximal :=
    (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  haveI : Algebra.IsSeparable (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
    letI : Field (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.Quotient.field _
    letI : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
    exact IsGalois.to_isSeparable
  rwa [Subgroup.eq_bot_iff_card,
      Ideal.card_inertia_eq_ramificationIdxIn (𝔓.under (𝓞 K)) hpbot 𝔓,
      Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 Gal(L/K)]

/-- The Galois group acts faithfully on `𝓞 L`. The action factors through the faithful
action on `L` — an automorphism of `L` is determined by its values on `𝓞 L`, since
`L = Frac(𝓞 L)` (`IsFractionRing.ringHom_ext`). Needed so that the uniqueness of the
Frobenius `AlgHom` (`eq_of_isUnramifiedAt`) transfers to the group `Gal(L/K)`. -/
private instance faithfulSMul_galois
    [IsGalois K L] : FaithfulSMul Gal(L/K) (𝓞 L) := by
  refine ⟨fun {σ τ} h => ?_⟩
  have hbridge : ∀ (g : Gal(L/K)) (x : 𝓞 L), ((g • x : 𝓞 L) : L) = g • (x : L) := fun g x => by
    simpa [Algebra.smul_def] using
      (smul_distrib_smul (G := Gal(L/K)) (R := 𝓞 L) (S := L) g x 1).symm
  have hL : ∀ x : 𝓞 L, σ • (x : L) = τ • (x : L) := fun x => by rw [← hbridge, ← hbridge, h x]
  refine eq_of_smul_eq_smul (α := L) fun y => ?_
  have heq : (σ : L →+* L) = (τ : L →+* L) :=
    IsFractionRing.ringHom_ext (A := 𝓞 L) (K := L) (L := L) (by simpa using hL)
  exact congrFun (congrArg DFunLike.coe heq) y

/-- A Frobenius element at an unramified prime `𝔓` is the canonical `arithFrobAt 𝔓`: the
residue-field characterisation pins it down uniquely
(`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`, transferred to `Gal(L/K)` via the faithful
action on `𝓞 L`). -/
theorem eq_arithFrobAt_of_isArithFrobAt
    [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] [Finite (𝓞 L ⧸ 𝔓)] [Algebra.IsUnramifiedAt (𝓞 K) 𝔓]
    (σ : Gal(L/K)) (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) :
    σ = arithFrobAt (𝓞 K) Gal(L/K) 𝔓 := by
  apply MulSemiringAction.toAlgHom_injective (𝓞 K) (𝓞 L)
  exact AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hσ
    (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) 𝔓.primeCompl_le_nonZeroDivisors

/-- For a prime `𝔭` of `𝓞 K` unramified in `L`, any two elements `σ`, `σ'` of `Gal(L/K)`
that are arithmetic Frobenius elements (`IsArithFrobAt`) at primes `𝔓`, `𝔓'` above `𝔭` are
conjugate: each equals `arithFrobAt` at its prime (`eq_arithFrobAt_of_isArithFrobAt`), and
the two `arithFrobAt`s lie over the same `𝔭`, so `isConj_arithFrobAt` applies. -/
theorem isConj_of_isArithFrobAt
    [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (σ σ' : Gal(L/K)) (𝔓 𝔓' : Ideal (𝓞 L)) [𝔓.IsPrime] [𝔓'.IsPrime]
    (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) (hσ' : IsArithFrobAt (𝓞 K) σ' 𝔓')
    (hP : 𝔓.LiesOver 𝔭) (hP' : 𝔓'.LiesOver 𝔭) :
    IsConj σ σ' := by
  haveI := hP
  haveI := hP'
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
    (ne_bot_of_ramificationIdx_eq_one K L (UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓 hP))
  haveI : Finite (𝓞 L ⧸ 𝔓') := Ideal.finiteQuotientOfFreeOfNeBot 𝔓'
    (ne_bot_of_ramificationIdx_eq_one K L (UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓' hP'))
  haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
    hunr.2 𝔓 (‹𝔓.IsPrime›.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓)) hP
  haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓' :=
    hunr.2 𝔓' (‹𝔓'.IsPrime›.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓')) hP'
  rw [eq_arithFrobAt_of_isArithFrobAt K L 𝔓 σ hσ,
    eq_arithFrobAt_of_isArithFrobAt K L 𝔓' σ' hσ']
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
conjugacy class of an unramified prime `𝔭` of `𝓞 K`: there is a single conjugacy class `C`
such that `C = ConjClasses.mk σ` for every `σ` that is an arithmetic Frobenius
(`IsArithFrobAt`) at some prime `𝔓` of `𝓞 L` above `𝔭`.
Sharifi §7.2 + SL Appendix paragraph 1. -/
theorem exists_frobeniusClass
    [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) :
    ∃ C : ConjClasses Gal(L/K),
      ∀ (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (_ : IsArithFrobAt (𝓞 K) σ 𝔓)
        (_ : 𝔓.LiesOver 𝔭), C = ConjClasses.mk σ := by
  obtain ⟨𝔓₀, hp₀, hlo₀, _⟩ := exists_prime_liesOver K L 𝔭 (UnramifiedIn.ne_bot K L hunr)
  haveI := hp₀
  haveI := hlo₀
  haveI : Finite (𝓞 L ⧸ 𝔓₀) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓₀
    (ne_bot_of_ramificationIdx_eq_one K L (UnramifiedIn.ramificationIdx_eq_one K L hunr 𝔓₀ hlo₀))
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
def frobeniusClass
    [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) : ConjClasses Gal(L/K) :=
  open Classical in
  if h : 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 then
    haveI := h.1
    (exists_frobeniusClass K L 𝔭 h.2).choose
  else
    ConjClasses.mk 1

/-- `frobeniusClass K L 𝔭` is the conjugacy class of any arithmetic Frobenius `σ`
(`IsArithFrobAt (𝓞 K) σ 𝔓`) at any prime `𝔓` of `𝓞 L` above `𝔭`. -/
theorem frobeniusClass_eq_mk_of_isArithFrobAt
    [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hσ : IsArithFrobAt (𝓞 K) σ 𝔓)
    (hP : 𝔓.LiesOver 𝔭) :
    frobeniusClass K L 𝔭 = ConjClasses.mk σ := by
  rw [frobeniusClass, dif_pos ⟨‹𝔭.IsPrime›, hunr⟩]
  exact (exists_frobeniusClass K L 𝔭 hunr).choose_spec σ 𝔓 hσ hP

/-- Only finitely many nonzero primes of `K` ramify in `L`. A ramified prime `𝔭` has some prime
`𝔓` of `𝓞 L` above it that is not unramified, hence divides the relative different
`differentIdeal (𝓞 K) (𝓞 L)` (`not_dvd_differentIdeal_iff`). That different is nonzero
(`differentIdeal_ne_bot`), so only finitely many `𝔓` divide it (`Ideal.finite_factors`), and the
ramified `𝔭` are their images under `Ideal.under (𝓞 K)`. -/
theorem finite_ramifiedIn
    [IsGalois K L] :
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭}.Finite := by
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
  simp only [UnramifiedIn, not_and, not_forall] at hnunr
  obtain ⟨𝔓, h𝔓max, h𝔓lo, h𝔓nu⟩ := hnunr h𝔭bot
  haveI := h𝔓max.isPrime
  haveI := h𝔓lo
  have h𝔓bot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭bot 𝔓
  have hdvd : 𝔓 ∣ differentIdeal (𝓞 K) (𝓞 L) := by
    by_contra h
    exact h𝔓nu (not_dvd_differentIdeal_iff.mp h)
  exact ⟨⟨𝔓, h𝔓max.isPrime, h𝔓bot⟩, hdvd, h𝔓lo.over.symm⟩

end Chebotarev
