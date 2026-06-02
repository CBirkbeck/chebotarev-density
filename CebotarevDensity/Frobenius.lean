module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Algebra.Group.Conj
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
  ∀ (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime], 𝔓.LiesOver 𝔭 → Ideal.ramificationIdx 𝔭 𝔓 = 1

/-- A prime of `𝓞 L` with ramification index `1` over its image in `𝓞 K` is nonzero:
the zero ideal has ramification index `0` (`Ideal.ramificationIdx_bot`). -/
theorem ne_bot_of_ramificationIdx_eq_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {𝔓 : Ideal (𝓞 L)} (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) : 𝔓 ≠ ⊥ := by
  rintro rfl
  simp at hunr

/-- An unramified prime is nonzero: the zero ideal of `𝓞 L` lies over the zero ideal of
`𝓞 K` with ramification index `0` (`Ideal.ramificationIdx_bot`), not `1`. -/
theorem UnramifiedIn.ne_bot
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    {𝔭 : Ideal (𝓞 K)} (hunr : UnramifiedIn K L 𝔭) : 𝔭 ≠ ⊥ := by
  rintro rfl
  simpa [Ideal.ramificationIdx_bot] using hunr ⊥ inferInstance

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

/-- For an unramified prime `𝔓`, the inertia group is trivial: by
`Ideal.card_inertia_eq_ramificationIdxIn` its cardinality equals the ramification index
`e(𝔓∣𝔭) = 1`, and a subgroup of cardinality one is trivial (`Subgroup.eq_bot_iff_card`). -/
theorem inertiaGroup_trivial_of_unramified
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) :
    Ideal.inertia Gal(L/K) 𝔓 = ⊥ := by
  have hPbot : 𝔓 ≠ ⊥ := ne_bot_of_ramificationIdx_eq_one K L hunr
  have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
  haveI : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
  haveI : (𝔓.under (𝓞 K)).IsMaximal :=
    (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  -- `Ideal.Quotient.field` is deliberately NOT a global instance: it would clash with
  -- `Ideal.Quotient.commRing` as a `CommRing (R ⧸ 𝔭)` diamond (the two are only defeq, not
  -- syntactically equal), so mathlib keeps the field structure explicit. Hence we must
  -- `letI` the residue-field structures by hand before `IsGalois.to_isSeparable` fires.
  haveI : Algebra.IsSeparable (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
    letI : Field (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.Quotient.field _
    letI : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
    exact IsGalois.to_isSeparable
  rw [Subgroup.eq_bot_iff_card,
      Ideal.card_inertia_eq_ramificationIdxIn (𝔓.under (𝓞 K)) hpbot 𝔓,
      Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 Gal(L/K)]
  exact hunr

/-- **Frobenius existence when inertia is trivial**. Given that the inertia group
at `𝔓` is trivial, there is a unique `σ ∈ Gal(L/K)` stabilising `𝔓` and acting as
the `N𝔭`-th power on the residue field `𝓞 L / 𝔓`. -/
theorem exists_unique_frobeniusAt_of_inertia_trivial
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hnz : 𝔓 ≠ ⊥) (hI : Ideal.inertia Gal(L/K) 𝔓 = ⊥) :
    ∃! σ : Gal(L/K), σ ∈ MulAction.stabilizer Gal(L/K) 𝔓 ∧
      ∀ x : 𝓞 L,
        (Ideal.Quotient.mk 𝔓) (σ • x) =
          ((Ideal.Quotient.mk 𝔓) x) ^ Ideal.absNorm (𝔓.under (𝓞 K)) := by
  have : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hnz
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) Gal(L/K) 𝔓
  refine ⟨σ, ⟨hσ.mem_stabilizer, hσ.mk_apply⟩, ?_⟩
  rintro τ ⟨-, hτ_pow⟩
  have hτ : IsArithFrobAt (𝓞 K) τ 𝔓 := fun x ↦ by
    simpa [← Ideal.Quotient.eq_zero_iff_mem, sub_eq_zero,
      Ideal.absNorm_apply, Submodule.cardQuot_apply] using hτ_pow x
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp (hI ▸ IsArithFrobAt.mul_inv_mem_inertia hτ hσ))

/-- **Existence and uniqueness of Frobenius at an unramified prime**.

For a Galois extension `L/K` of number fields and a prime `𝔓` of `𝓞 L`
unramified over `𝓞 K`, there is a unique `σ ∈ Gal(L/K)` stabilising `𝔓` and acting
as the `N𝔭`-th power on the residue field `𝓞 L / 𝔓` (`𝔓 ≠ ⊥` is automatic from
`ramificationIdx = 1`). This packages Sharifi Proposition 2.6.* (over Dedekind domains). -/
theorem exists_unique_frobeniusAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) :
    ∃! σ : Gal(L/K), σ ∈ MulAction.stabilizer Gal(L/K) 𝔓 ∧
      ∀ x : 𝓞 L,
        (Ideal.Quotient.mk 𝔓) (σ • x) =
          ((Ideal.Quotient.mk 𝔓) x) ^ Ideal.absNorm (𝔓.under (𝓞 K)) :=
  exists_unique_frobeniusAt_of_inertia_trivial K L 𝔓 (ne_bot_of_ramificationIdx_eq_one K L hunr)
    (inertiaGroup_trivial_of_unramified K L 𝔓 hunr)

/-- The Frobenius automorphism at an unramified prime `𝔓` of `𝓞 L`. -/
noncomputable def frobeniusAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) :
    Gal(L/K) :=
  (exists_unique_frobeniusAt K L 𝔓 hunr).exists.choose

/-- The Frobenius automorphism stabilises `𝔓` and acts as the `N𝔭`-th power
on the residue field. -/
theorem frobeniusAt_spec
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) :
    frobeniusAt K L 𝔓 hunr ∈ MulAction.stabilizer Gal(L/K) 𝔓 ∧
      ∀ x : 𝓞 L,
        (Ideal.Quotient.mk 𝔓) (frobeniusAt K L 𝔓 hunr • x) =
          ((Ideal.Quotient.mk 𝔓) x) ^ Ideal.absNorm (𝔓.under (𝓞 K)) :=
  (exists_unique_frobeniusAt K L 𝔓 hunr).exists.choose_spec

/-- **Frobenius conjugation formula** (Stevenhagen–Lenstra p. 14:
`Frob_{ψ∘τ} = τ⁻¹ ∘ Frob_ψ ∘ τ`). If `σ • 𝔓 = 𝔓'`, then `Frob_{𝔓'} = σ · Frob_𝔓 · σ⁻¹`:
the conjugate `σ · Frob_𝔓 · σ⁻¹` stabilises `𝔓'` and acts as the `N𝔭`-th power on the
residue field `κ(𝔓')`, so by the uniqueness in `exists_unique_frobeniusAt` it is the
Frobenius at `𝔓'`. -/
theorem frobeniusAt_conj_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔓 𝔓' : Ideal (𝓞 L)) [𝔓.IsPrime] [𝔓'.IsPrime]
    (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1)
    (hunr' : Ideal.ramificationIdx (𝔓'.under (𝓞 K)) 𝔓' = 1)
    (σ : Gal(L/K)) (hσ : σ • 𝔓 = 𝔓') :
    frobeniusAt K L 𝔓' hunr' = σ * frobeniusAt K L 𝔓 hunr * σ⁻¹ := by
  sorry

/-- For a prime `𝔭` of `𝓞 K` unramified in `L`, any two Frobenius elements
above `𝔭` are conjugate in `Gal(L/K)` — the conjugating element witnesses
transitivity of the Galois action on primes above `𝔭`. -/
theorem frobeniusAt_isConj_of_liesOver
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (𝔓 𝔓' : Ideal (𝓞 L)) [𝔓.IsPrime] [𝔓'.IsPrime] (hP : 𝔓.LiesOver 𝔭) (hP' : 𝔓'.LiesOver 𝔭) :
    IsConj
      (frobeniusAt K L 𝔓
        (by rw [show 𝔓.under (𝓞 K) = 𝔭 from hP.over.symm]; exact hunr 𝔓 hP))
      (frobeniusAt K L 𝔓'
        (by rw [show 𝔓'.under (𝓞 K) = 𝔭 from hP'.over.symm]; exact hunr 𝔓' hP')) := by
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup 𝔭 𝔓 𝔓' Gal(L/K)
  rw [frobeniusAt_conj_eq K L 𝔓 𝔓'
      (by rw [show 𝔓.under (𝓞 K) = 𝔭 from hP.over.symm]; exact hunr 𝔓 hP)
      (by rw [show 𝔓'.under (𝓞 K) = 𝔭 from hP'.over.symm]; exact hunr 𝔓' hP') σ hσ]
  exact isConj_iff.mpr ⟨σ, rfl⟩

/-- A nonzero prime `𝔭` of `𝓞 K` has at least one prime `𝔓` of `𝓞 L` lying
over it, and any such `𝔓` is nonzero (going-up for the integral extension
`𝓞 K ⊆ 𝓞 L`; nonzero because `𝔭` is and `algebraMap (𝓞 K) (𝓞 L)` is injective). -/
theorem exists_prime_liesOver
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hnz : 𝔭 ≠ ⊥) :
    ∃ 𝔓 : Ideal (𝓞 L), 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥ := by
  obtain ⟨𝔓, hp, hcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔭 (by simp)
  refine ⟨𝔓, hp, ⟨hcomap.symm⟩, ?_⟩
  rintro rfl
  rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp
    (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))] at hcomap
  exact hnz hcomap.symm

/-- Existence (and uniqueness, by conjugacy-class collapse) of the Frobenius
conjugacy class of an unramified prime `𝔭` of `𝓞 K`.
Sharifi §7.2 + SL Appendix paragraph 1. -/
theorem exists_frobeniusClass
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) :
    ∃ C : ConjClasses Gal(L/K),
      ∀ (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭),
        C = ConjClasses.mk (frobeniusAt K L 𝔓
          (by rw [show 𝔓.under (𝓞 K) = 𝔭 from hP.over.symm]; exact hunr 𝔓 hP)) := by
  obtain ⟨𝔓₀, hp₀, hlo₀, _⟩ := exists_prime_liesOver K L 𝔭 (UnramifiedIn.ne_bot K L hunr)
  refine ⟨ConjClasses.mk (frobeniusAt K L 𝔓₀
    (by rw [show 𝔓₀.under (𝓞 K) = 𝔭 from hlo₀.over.symm]; exact hunr 𝔓₀ hlo₀)), ?_⟩
  intro 𝔓 _ hP
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  exact frobeniusAt_isConj_of_liesOver K L 𝔭 hunr 𝔓₀ 𝔓 hlo₀ hP

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
    if h : 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 then
      haveI := h.1
      (exists_frobeniusClass K L 𝔭 h.2).choose
    else
      ConjClasses.mk 1

/-- `frobeniusClass K L 𝔭` is the conjugacy class of `frobeniusAt 𝔓` for any
prime `𝔓` of `𝓞 L` above `𝔭`. -/
theorem frobeniusClass_eq_mk_frobeniusAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭) :
    frobeniusClass K L 𝔭 =
      ConjClasses.mk (frobeniusAt K L 𝔓
        (by rw [show 𝔓.under (𝓞 K) = 𝔭 from hP.over.symm]; exact hunr 𝔓 hP)) := by
  rw [frobeniusClass, dif_pos ⟨‹𝔭.IsPrime›, hunr⟩]
  exact (exists_frobeniusClass K L 𝔭 hunr).choose_spec 𝔓 hP

/-- Only finitely many nonzero primes of `K` ramify in `L`. -/
theorem finite_ramifiedIn
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭}.Finite := by
  sorry

end Chebotarev
