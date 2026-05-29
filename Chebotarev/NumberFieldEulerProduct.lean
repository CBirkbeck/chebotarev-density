module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Data.Finite.Vector
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.Card
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Generic number-field Euler-product infrastructure

The analytic number-field machinery for `ζ_K(s) = Σ_𝔞 N𝔞^{-s} = ∏_𝔭
(1 - N𝔭^{-s})^{-1}` and the per-prime-power decomposition used by
the Chebotarev cyclotomic and abelian cases.

Originally developed in `flt-regular-bernoulli`; portable to this
project unchanged (depends only on mathlib).
-/

@[expose] public section

noncomputable section

open NumberField
open scoped Topology nonZeroDivisors

noncomputable instance instFintypeSym (α : Type*) [Finite α] (n : ℕ) :
    Fintype (Sym α n) :=
  Fintype.ofFinite (Sym α n)

namespace Chebotarev

section NumberFieldEulerProduct

variable (L : Type*) [Field L] [NumberField L]

abbrev NonzeroIdeal : Type _ := {I : Ideal (𝓞 L) // I ≠ ⊥}

noncomputable def idealNormMultiplicity (n : ℕ) : ℕ :=
  Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 = n}

lemma idealNormMultiplicity_zero : idealNormMultiplicity L 0 = 0 := by
  unfold idealNormMultiplicity
  rw [Nat.card_eq_zero]
  exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ => hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩

lemma idealNormMultiplicity_one : idealNormMultiplicity L 1 = 1 := by
  unfold idealNormMultiplicity
  have : Unique {I : NonzeroIdeal L // Ideal.absNorm I.1 = 1} :=
    { default := ⟨⟨⊤, by simp⟩, Ideal.absNorm_top⟩
      uniq := fun ⟨⟨I, hI⟩, hnorm⟩ =>
        Subtype.ext (Subtype.ext (Ideal.absNorm_eq_one_iff.mp hnorm)) }
  exact Nat.card_unique

lemma idealNormMultiplicity_mul {m n : ℕ} (hcop : Nat.Coprime m n) :
    idealNormMultiplicity L (m * n) =
      idealNormMultiplicity L m * idealNormMultiplicity L n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.Coprime, Nat.gcd_zero_left] at hcop
    subst hcop
    simp [idealNormMultiplicity_zero, idealNormMultiplicity_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.Coprime, Nat.gcd_zero_right] at hcop
    subst hcop
    simp [idealNormMultiplicity_zero, idealNormMultiplicity_one]
  rcases Nat.lt_or_ge 1 m with hm1 | hm1
  all_goals rcases Nat.lt_or_ge 1 n with hn1 | hn1
  · classical
    have h_cop_spans : (Ideal.span {(m : 𝓞 L)}) ⊔ (Ideal.span {(n : 𝓞 L)}) = ⊤ := by
      rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
      simpa using (Nat.Coprime.isCoprime hcop).map (algebraMap ℤ (𝓞 L))
    have h_mul_sup : ∀ (I : Ideal (𝓞 L)),
        (I ⊔ Ideal.span {(m : 𝓞 L)}) * (I ⊔ Ideal.span {(n : 𝓞 L)}) =
          I ⊔ Ideal.span {(m : 𝓞 L) * (n : 𝓞 L)} := fun I => by
      rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup,
        mul_comm (Ideal.span {(m : 𝓞 L)}) I,
        Ideal.span_singleton_mul_span_singleton,
        show I * I ⊔ I * Ideal.span {(n : 𝓞 L)} ⊔
            (I * Ideal.span {(m : 𝓞 L)} ⊔ Ideal.span {(m : 𝓞 L) * (n : 𝓞 L)}) =
            (I * I ⊔ I * Ideal.span {(n : 𝓞 L)} ⊔ I * Ideal.span {(m : 𝓞 L)}) ⊔
              Ideal.span {(m : 𝓞 L) * (n : 𝓞 L)} by ac_rfl,
        ← Ideal.mul_sup, ← Ideal.mul_sup,
        show I ⊔ Ideal.span {(n : 𝓞 L)} ⊔ Ideal.span {(m : 𝓞 L)} = ⊤ by
          rw [sup_assoc, sup_comm (Ideal.span {(n : 𝓞 L)}) _, h_cop_spans, sup_top_eq],
        Ideal.mul_top]
    have h_sup_absNorm : ∀ (I : Ideal (𝓞 L)), Ideal.absNorm I = m * n →
        I ⊔ Ideal.span {(m : 𝓞 L) * (n : 𝓞 L)} = I := fun I hI => by
      refine le_antisymm (sup_le le_rfl ?_) le_sup_left
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact_mod_cast hI ▸ Ideal.absNorm_mem I
    have h_abs_span_nat : ∀ (r : ℕ), Ideal.absNorm (Ideal.span {(r : 𝓞 L)}) =
        r ^ Module.finrank ℤ (𝓞 L) := fun r => by
      rw [Ideal.absNorm_span_singleton,
        show ((r : 𝓞 L)) = algebraMap ℤ (𝓞 L) (r : ℤ) by push_cast; rfl,
        Algebra.norm_algebraMap_of_basis (Module.finBasis ℤ (𝓞 L))]
      simp
    have h_fwd_norms : ∀ (I : Ideal (𝓞 L)), Ideal.absNorm I = m * n →
        Ideal.absNorm (I ⊔ Ideal.span {(m : 𝓞 L)}) = m ∧
          Ideal.absNorm (I ⊔ Ideal.span {(n : 𝓞 L)}) = n := fun I hI => by
      set a := Ideal.absNorm (I ⊔ Ideal.span {(m : 𝓞 L)}) with ha_def
      set b := Ideal.absNorm (I ⊔ Ideal.span {(n : 𝓞 L)}) with hb_def
      have h_prod : (I ⊔ Ideal.span {(m : 𝓞 L)}) * (I ⊔ Ideal.span {(n : 𝓞 L)}) = I := by
        rw [h_mul_sup I, h_sup_absNorm I hI]
      have h_ab : a * b = m * n := by
        rw [ha_def, hb_def, ← map_mul, h_prod, hI]
      have h_a_dvd_md : a ∣ m ^ Module.finrank ℤ (𝓞 L) := by
        rw [← h_abs_span_nat m]
        exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
      have h_b_dvd_nd : b ∣ n ^ Module.finrank ℤ (𝓞 L) := by
        rw [← h_abs_span_nat n]
        exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
      have h_cop_an : Nat.Coprime a n :=
        (hcop.pow_left _).coprime_dvd_left h_a_dvd_md
      have h_cop_bm : Nat.Coprime b m :=
        (hcop.symm.pow_left _).coprime_dvd_left h_b_dvd_nd
      have h_a_dvd_m : a ∣ m :=
        h_cop_an.dvd_of_dvd_mul_right ⟨b, h_ab.symm⟩
      have h_b_dvd_n : b ∣ n :=
        h_cop_bm.dvd_of_dvd_mul_right ⟨a, by linarith [h_ab, mul_comm a b, mul_comm m n]⟩
      have ha_le : a ≤ m := Nat.le_of_dvd hm h_a_dvd_m
      have hb_le : b ≤ n := Nat.le_of_dvd hn h_b_dvd_n
      refine ⟨Nat.le_antisymm ha_le ?_, Nat.le_antisymm hb_le ?_⟩ <;>
        nlinarith [h_ab, ha_le, hb_le, hm, hn]
    have h_cop_m_L : ∀ (L' : Ideal (𝓞 L)), Ideal.absNorm L' = n →
        IsCoprime (Ideal.span {(m : 𝓞 L)}) L' := fun L' hL => by
      rw [Ideal.isCoprime_iff_sup_eq]
      refine top_le_iff.mp ?_
      calc
        ⊤ = Ideal.span {(m : 𝓞 L)} ⊔ Ideal.span {(n : 𝓞 L)} := h_cop_spans.symm
        _ ≤ Ideal.span {(m : 𝓞 L)} ⊔ L' := sup_le_sup_left (by
            rw [Ideal.span_le, Set.singleton_subset_iff]
            exact_mod_cast hL ▸ Ideal.absNorm_mem L') _
    have h_cop_n_J : ∀ (J : Ideal (𝓞 L)), Ideal.absNorm J = m →
        IsCoprime (Ideal.span {(n : 𝓞 L)}) J := fun J hJ => by
      rw [Ideal.isCoprime_iff_sup_eq]
      refine top_le_iff.mp ?_
      calc
        ⊤ = Ideal.span {(n : 𝓞 L)} ⊔ Ideal.span {(m : 𝓞 L)} :=
            ((sup_comm _ _).trans h_cop_spans).symm
        _ ≤ Ideal.span {(n : 𝓞 L)} ⊔ J := sup_le_sup_left (by
            rw [Ideal.span_le, Set.singleton_subset_iff]
            exact_mod_cast hJ ▸ Ideal.absNorm_mem J) _
    have h_inv_m : ∀ (J L' : Ideal (𝓞 L)), Ideal.absNorm J = m → Ideal.absNorm L' = n →
        J * L' ⊔ Ideal.span {(m : 𝓞 L)} = J := fun J L' hJ hL => by
      have h_cop_mL_sup : Ideal.span {(m : 𝓞 L)} ⊔ L' = ⊤ :=
        Ideal.isCoprime_iff_sup_eq.mp (h_cop_m_L L' hL)
      refine le_antisymm (sup_le Ideal.mul_le_right ?_) ?_
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        exact_mod_cast hJ ▸ Ideal.absNorm_mem J
      · calc
          J = J * ⊤ := (Ideal.mul_top J).symm
          _ = J * (Ideal.span {(m : 𝓞 L)} ⊔ L') := by rw [h_cop_mL_sup]
          _ = J * Ideal.span {(m : 𝓞 L)} ⊔ J * L' := Ideal.mul_sup _ _ _
          _ ≤ Ideal.span {(m : 𝓞 L)} ⊔ J * L' := sup_le_sup_right Ideal.mul_le_left _
          _ = J * L' ⊔ Ideal.span {(m : 𝓞 L)} := sup_comm _ _
    have h_inv_n : ∀ (J L' : Ideal (𝓞 L)), Ideal.absNorm J = m → Ideal.absNorm L' = n →
        J * L' ⊔ Ideal.span {(n : 𝓞 L)} = L' := fun J L' hJ hL => by
      have h_cop_nJ_sup : Ideal.span {(n : 𝓞 L)} ⊔ J = ⊤ :=
        Ideal.isCoprime_iff_sup_eq.mp (h_cop_n_J J hJ)
      refine le_antisymm (sup_le Ideal.mul_le_left ?_) ?_
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        exact_mod_cast hL ▸ Ideal.absNorm_mem L'
      · calc
          L' = ⊤ * L' := (Ideal.top_mul L').symm
          _ = (Ideal.span {(n : 𝓞 L)} ⊔ J) * L' := by rw [h_cop_nJ_sup]
          _ = Ideal.span {(n : 𝓞 L)} * L' ⊔ J * L' := Ideal.sup_mul _ _ _
          _ ≤ Ideal.span {(n : 𝓞 L)} ⊔ J * L' := sup_le_sup_right Ideal.mul_le_right _
          _ = J * L' ⊔ Ideal.span {(n : 𝓞 L)} := sup_comm _ _
    let fwd : {I : NonzeroIdeal L // Ideal.absNorm I.1 = m * n} →
        {J : NonzeroIdeal L // Ideal.absNorm J.1 = m} ×
          {L' : NonzeroIdeal L // Ideal.absNorm L'.1 = n} :=
      fun ⟨⟨I, hI_ne⟩, hI_norm⟩ =>
        ⟨⟨⟨I ⊔ Ideal.span {(m : 𝓞 L)}, fun h => hI_ne (le_bot_iff.mp (h ▸ le_sup_left))⟩,
          (h_fwd_norms I hI_norm).1⟩,
         ⟨⟨I ⊔ Ideal.span {(n : 𝓞 L)}, fun h => hI_ne (le_bot_iff.mp (h ▸ le_sup_left))⟩,
          (h_fwd_norms I hI_norm).2⟩⟩
    let bwd : {J : NonzeroIdeal L // Ideal.absNorm J.1 = m} ×
        {L' : NonzeroIdeal L // Ideal.absNorm L'.1 = n} →
        {I : NonzeroIdeal L // Ideal.absNorm I.1 = m * n} :=
      fun ⟨⟨⟨J, hJ_ne⟩, hJ_norm⟩, ⟨⟨L', hL_ne⟩, hL_norm⟩⟩ =>
        ⟨⟨J * L', fun h => (Ideal.mul_eq_bot.mp h).elim hJ_ne hL_ne⟩,
         by rw [map_mul, hJ_norm, hL_norm]⟩
    have h_equiv :
        {I : NonzeroIdeal L // Ideal.absNorm I.1 = m * n} ≃
          {J : NonzeroIdeal L // Ideal.absNorm J.1 = m} ×
            {L' : NonzeroIdeal L // Ideal.absNorm L'.1 = n} :=
      { toFun := fwd
        invFun := bwd
        left_inv := fun ⟨⟨I, hI_ne⟩, hI_norm⟩ => by
          simp only [fwd, bwd]
          exact Subtype.ext (Subtype.ext ((h_mul_sup I).trans (h_sup_absNorm I hI_norm)))
        right_inv := fun ⟨⟨⟨J, hJ_ne⟩, hJ_norm⟩, ⟨⟨L', hL_ne⟩, hL_norm⟩⟩ => by
          simp only [fwd, bwd]
          exact Prod.ext (Subtype.ext (Subtype.ext (h_inv_m J L' hJ_norm hL_norm)))
            (Subtype.ext (Subtype.ext (h_inv_n J L' hJ_norm hL_norm))) }
    unfold idealNormMultiplicity
    rw [Nat.card_congr h_equiv, Nat.card_prod]
  · interval_cases n
    simp [idealNormMultiplicity_one]
  · interval_cases m
    simp [idealNormMultiplicity_one]
  · interval_cases m
    interval_cases n
    simp [idealNormMultiplicity_one]

lemma dedekindZeta_eq_tsum_idealNormMultiplicity {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∑' n : ℕ, (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) := by
  unfold NumberField.dedekindZeta LSeries
  refine tsum_congr fun n => ?_
  unfold LSeries.term
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
    simp [idealNormMultiplicity_zero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  · simp only [hn.ne', ↓reduceIte]
    rw [Complex.cpow_neg, div_eq_mul_inv]
    congr 1
    unfold idealNormMultiplicity
    have hequiv : {I : Ideal (𝓞 L) // Ideal.absNorm I = n} ≃
        {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} := by
      refine {
        toFun := fun ⟨I, hI⟩ => ⟨⟨I, ?_⟩, hI⟩
        invFun := fun ⟨⟨I, _⟩, hI⟩ => ⟨I, hI⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      intro h
      rw [h, Ideal.absNorm_bot] at hI
      lia
    exact_mod_cast Nat.card_congr hequiv

lemma summable_tsum_symGeometric (α : Type*) [Fintype α] [Finite α] {z : ℂ}
    (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => (Fintype.card (Sym α n) : ℂ) * z ^ n) ∧
      (∑' n : ℕ, (Fintype.card (Sym α n) : ℂ) * z ^ n) = ((1 - z)⁻¹) ^ Fintype.card α := by
  by_cases hα : Fintype.card α = 0
  · haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp hα
    let term : ℕ → ℂ := fun n => (Fintype.card (Sym α n) : ℂ) * z ^ n
    have hzero : ∀ n ≠ 0, term n = 0 := by
      intro n hn
      cases n with
      | zero => contradiction
      | succ n => simp [term, Sym.card_sym_eq_multichoose, Nat.multichoose_zero_succ]
    have hsupport : {n : ℕ | term n ≠ 0}.Finite :=
      Set.Finite.subset ({0} : Set ℕ).toFinite fun n hn => not_imp_comm.mp (hzero n) hn
    refine ⟨summable_of_hasFiniteSupport hsupport, ?_⟩
    simpa [term, hα, Sym.card_sym_eq_multichoose] using tsum_eq_single 0 hzero
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hα
    have hterm : ∀ n : ℕ, ((n + k).choose k : ℂ) * z ^ n =
        (Fintype.card (Sym α n) : ℂ) * z ^ n := fun n => by
      rw [Sym.card_sym_eq_choose, hk, Nat.succ_add_sub_one, Nat.add_comm k n, Nat.choose_symm_add]
    refine ⟨(summable_choose_mul_geometric_of_norm_lt_one k hz).congr hterm, ?_⟩
    rw [tsum_congr fun n => (hterm n).symm, tsum_choose_mul_geometric_of_norm_lt_one k hz, one_div,
      hk, inv_pow]

lemma tsum_symGeometric (α : Type*) [Fintype α] [Finite α] {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' n : ℕ, (Fintype.card (Sym α n) : ℂ) * z ^ n) = ((1 - z)⁻¹) ^ Fintype.card α :=
  (summable_tsum_symGeometric α hz).2

lemma summable_idealNormMultiplicity_mul_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => ‖(idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)‖ := by
  classical
  have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal L | Ideal.absNorm I.1 = b}.Finite := fun b =>
    Set.Finite.preimage (f := fun I : NonzeroIdeal L => I.1) (fun _ _ _ _ => Subtype.ext)
      (Ideal.finite_setOf_absNorm_eq (S := 𝓞 L) b)
  have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity L k =
      Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 ≤ n} := fun n => by
    have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal L =>
      Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ => h_finite b)
    rw [show ((fun I : NonzeroIdeal L => Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
        {I : NonzeroIdeal L | Ideal.absNorm I.1 ≤ n} by
      ext ⟨I, hI⟩
      simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
      exact ⟨fun h => h.2, fun h =>
        ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
    exact key.symm
  have h_bigO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity L k : ℝ))
      =O[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    have h_card_bridge : ∀ n : ℕ,
        Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 ≤ n} =
        Nat.card {I : (Ideal (𝓞 L))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
      fun n => Nat.card_congr
        { toFun := fun ⟨⟨I, hI⟩, hn⟩ =>
            ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
          invFun := fun ⟨⟨I, hI⟩, hn⟩ =>
            ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
      (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ L).comp
        tendsto_natCast_atTop_atTop).congr' ?_)
    filter_upwards with n
    simp only [Function.comp_apply, Real.rpow_one]
    rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
    push_cast
    rfl
  have h_lss : LSeriesSummable (fun n : ℕ => ((idealNormMultiplicity L n : ℝ) : ℂ)) s :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg
      (f := fun n => (idealNormMultiplicity L n : ℝ))
      h_bigO (fun _ => Nat.cast_nonneg _) zero_le_one (by exact_mod_cast hs)
  have h_term_eq : LSeries.term (fun n : ℕ => ((idealNormMultiplicity L n : ℝ) : ℂ)) s =
      fun n => (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) := by
    funext n
    simp only [LSeries.term]
    split_ifs with hn
    · subst hn
      simp [idealNormMultiplicity_zero]
    · simp [Complex.cpow_neg, div_eq_mul_inv]
  exact (h_term_eq ▸ h_lss :
    Summable fun n => (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)).norm

lemma dedekindZeta_eq_tprod_primePowerSeries {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∏' q : Nat.Primes,
        (∑' k : ℕ, (idealNormMultiplicity L ((q : ℕ) ^ k) : ℂ) *
          ((((q : ℕ) ^ k : ℕ) : ℂ) ^ (-s))) := by
  let f : ℕ → ℂ := fun n => (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)
  have hf_zero : f 0 = 0 := by simp [f, idealNormMultiplicity_zero L]
  have hf_one : f 1 = 1 := by simp [f, idealNormMultiplicity_one L]
  have hf_mul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := fun {m n} hcop => by
    simp only [f, idealNormMultiplicity_mul L hcop, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
    ring
  have hf_sum : Summable fun n => ‖f n‖ := summable_idealNormMultiplicity_mul_cpow_neg L hs
  rw [dedekindZeta_eq_tsum_idealNormMultiplicity L hs,
    ← EulerProduct.eulerProduct_tprod hf_one hf_mul hf_sum hf_zero]

end NumberFieldEulerProduct

end Chebotarev
