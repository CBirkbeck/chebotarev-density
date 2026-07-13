module

public import CebotarevDensity.ForMathlib.IndexImageCount

/-!
# Effective lattice-point count: the per-scale count↔volume bridge

First half (1/2) of the effective, `O(nᵈ⁻¹)`-rate strengthening of
`tendsto_card_div_pow_atTop_volume`. This file supplies the per-scale bridge: for a bounded
measurable `s ⊆ ι → ℝ`, the number of points of the scaled integer lattice `n⁻¹·ℤ^ι` in `s`
differs from `vol(s)·nᵈ` by at most the number of grid cells of the `n⁻¹ℤ^ι` grid meeting the
frontier `∂s`.

Following Lang, GTM 110 Ch. VI §3 Theorem 3 (p. 129) and Widmer / Gun–Ramaré–Sivaraman. The
follow-up (part 2/2) bounds that boundary-cell count by `O(nᵈ⁻¹)` — because `∂s` is a finite
union of Lipschitz images of `[0,1]ᵈ⁻¹` (`ncard_index_image_frontier_le`, in
`IndexImageCount.lean`) — to assemble the rate-effective count.

## Main results

* `Chebotarev.abs_card_inter_sub_volume_mul_pow_le`: the per-scale count↔volume bridge.

## References

* Serge Lang, *Algebraic Number Theory*, 2nd ed., GTM 110, Springer 1994, Ch. V §2 and Ch. VI §3.
* S. Gun, O. Ramaré, J. Sivaraman, *Counting ideals in ray classes*, J. Number Theory 243 (2023)
  §3.3–3.5, after K. Debaene.
-/

open Submodule Pointwise MeasureTheory Set BoxIntegral BoxIntegral.unitPartition

open scoped NNReal

namespace Chebotarev

@[expose] public section

section Sublemmas

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
private lemma index_mem_image_frontier_of_box_meet_not_subset {n : ℕ} [NeZero n]
    {s : Set (ι → ℝ)} {ν : ι → ℤ} (hmeet : ((box n ν : Set (ι → ℝ)) ∩ s).Nonempty)
    (hnsub : ¬ (box n ν : Set (ι → ℝ)) ⊆ s) : ν ∈ index n '' frontier s := by
  have hconn : IsPreconnected (box n ν : Set (ι → ℝ)) := by
    rw [BoxIntegral.Box.coe_eq_pi]
    exact (convex_pi fun _ _ ↦ convex_Ioc _ _).isPreconnected
  obtain ⟨xc, hxcb, hxcs⟩ : ((box n ν : Set (ι → ℝ)) ∩ sᶜ).Nonempty := by
    rw [Set.not_subset] at hnsub
    exact hnsub.imp fun _ ⟨hx, hxs⟩ ↦ ⟨hx, hxs⟩
  by_contra hcon
  have hcon' : (box n ν : Set (ι → ℝ)) ∩ frontier s = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxb, hxf⟩
    exact hcon ⟨x, hxf, mem_box_iff_index.mp hxb⟩
  have hsplit : (box n ν : Set (ι → ℝ)) ⊆ interior s ∪ (closure s)ᶜ := by
    intro x hx
    by_contra hxc
    rw [Set.mem_union, not_or, Set.notMem_compl_iff] at hxc
    exact (Set.eq_empty_iff_forall_notMem.mp hcon' x) ⟨hx, hxc.2, hxc.1⟩
  rcases hconn.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl
    (disjoint_compl_right_iff_subset.mpr (interior_subset.trans subset_closure)) hsplit
    with hsub | hsub
  · exact hxcs (interior_subset (hsub hxcb))
  · obtain ⟨x, hxb, hxs⟩ := hmeet
    exact (hsub hxb) (subset_closure hxs)

private lemma measureReal_biUnion_box (n : ℕ) [NeZero n] (t : Finset (ι → ℤ)) :
    volume.real (⋃ ν ∈ t, (box n ν : Set (ι → ℝ))) = t.card / (n : ℝ) ^ Fintype.card ι := by
  have hvol_box : ∀ ν : ι → ℤ,
      volume.real (box n ν : Set (ι → ℝ)) = 1 / (n : ℝ) ^ Fintype.card ι := by
    intro ν
    rw [measureReal_def, volume_box]
    simp
  rw [measureReal_biUnion_finset (fun ν _ ν' _ h ↦ disjoint.mp h)
    (fun ν _ ↦ (box n ν).measurableSet_coe) (fun ν _ ↦ (box n ν).isBounded.measure_lt_top.ne)]
  simp_rw [hvol_box]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Count ↔ volume bridge.** The number of points of `n⁻¹ℤ^ι` in a bounded measurable `s`
differs from `vol(s)·nᵈ` by at most the number of grid cells meeting `∂s`. This is the
effective form of the sandwich behind `tendsto_card_div_pow_atTop_volume`. -/
theorem abs_card_inter_sub_volume_mul_pow_le {s : Set (ι → ℝ)}
    (hbdd : Bornology.IsBounded s) (hmeas : MeasurableSet s) {n : ℕ} (hn : 1 ≤ n) :
    |(Nat.card ↑(s ∩ (n : ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) : ℝ)
        - volume.real s * (n : ℝ) ^ Fintype.card ι|
      ≤ (index n '' frontier s).ncard := by
  have hne : NeZero n := ⟨Nat.one_le_iff_ne_zero.mp hn⟩
  have hvs : volume s ≠ ⊤ := hbdd.measure_lt_top.ne
  set Inside : Set (ι → ℤ) := {ν | (box n ν : Set (ι → ℝ)) ⊆ s}
  set Meet : Set (ι → ℤ) := {ν | ((box n ν : Set (ι → ℝ)) ∩ s).Nonempty}
  set Bd : Set (ι → ℤ) := index n '' frontier s
  have hInsideFin : Inside.Finite := setFinite_index n hmeas.nullMeasurableSet hvs
  have hBdFin : Bd.Finite :=
    setFinite_index_image_of_isBounded n (hbdd.closure.subset frontier_subset_closure)
  have hMeetSub : Meet ⊆ index n '' s := by
    rintro ν ⟨x, hxb, hxs⟩
    exact ⟨x, hxs, mem_box_iff_index.mp hxb⟩
  have hMeetFin : Meet.Finite :=
    (setFinite_index_image_of_isBounded n hbdd).subset hMeetSub
  set Tag : Set (ι → ℤ) := {ν | tag n ν ∈ s} with hTag
  have himg : index n '' (s ∩ (n : ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) = Tag := by
    ext ν
    simp only [hTag, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, ⟨hxs, hxL⟩, rfl⟩
      rwa [tag_index_eq_self_of_mem_smul_span n hxL]
    · intro hν
      exact ⟨tag n ν, ⟨hν, tag_mem_smul_span n ν⟩, index_tag n ν⟩
  have hNeq : Nat.card ↑(s ∩ (n : ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) = Tag.ncard := by
    rw [Nat.card_coe_set_eq, ← himg]
    refine (Set.InjOn.ncard_image ?_).symm
    intro x hx y hy h
    exact eq_of_mem_smul_span_of_index_eq_index n hx.2 hy.2 h
  have hIT : Inside ⊆ Tag := fun ν hν ↦ hν (tag_mem n ν)
  have hTM : Tag ⊆ Meet := fun ν hν ↦ ⟨tag n ν, tag_mem n ν, hν⟩
  have hMIB : Meet ⊆ Inside ∪ Bd := by
    intro ν hν
    by_cases hsub : (box n ν : Set (ι → ℝ)) ⊆ s
    · exact Or.inl hsub
    · exact Or.inr (index_mem_image_frontier_of_box_meet_not_subset hν hsub)
  have hcard_IT : Inside.ncard ≤ Tag.ncard :=
    Set.ncard_le_ncard hIT (hMeetFin.subset hTM)
  have hcard_TM : Tag.ncard ≤ Meet.ncard := Set.ncard_le_ncard hTM hMeetFin
  have hcard_MIB : Meet.ncard ≤ Inside.ncard + Bd.ncard :=
    (Set.ncard_le_ncard hMIB (hInsideFin.union hBdFin)).trans (Set.ncard_union_le _ _)
  set V : ℝ := volume.real s * (n : ℝ) ^ Fintype.card ι with hV
  have hnpow : (0 : ℝ) < (n : ℝ) ^ Fintype.card ι := by positivity
  have hcardI : (hInsideFin.toFinset).card = Inside.ncard :=
    (Set.ncard_eq_toFinset_card _ hInsideFin).symm
  have hcardM : (hMeetFin.toFinset).card = Meet.ncard :=
    (Set.ncard_eq_toFinset_card _ hMeetFin).symm
  have hvol_lower : (Inside.ncard : ℝ) ≤ V := by
    have hsub : (⋃ ν ∈ hInsideFin.toFinset, (box n ν : Set (ι → ℝ))) ⊆ s :=
      Set.iUnion₂_subset fun ν hν ↦ hInsideFin.mem_toFinset.mp hν
    have hle := measureReal_mono hsub hvs
    rw [measureReal_biUnion_box n hInsideFin.toFinset, hcardI, div_le_iff₀ hnpow] at hle
    rw [hV]
    linarith
  have hvol_upper : V ≤ (Meet.ncard : ℝ) := by
    have hsub : s ⊆ ⋃ ν ∈ hMeetFin.toFinset, (box n ν : Set (ι → ℝ)) := by
      intro x hxs
      refine Set.mem_iUnion₂.mpr ⟨index n x, hMeetFin.mem_toFinset.mpr ?_,
        mem_box_iff_index.mpr rfl⟩
      exact ⟨x, mem_box_iff_index.mpr rfl, hxs⟩
    have hfinU : volume (⋃ ν ∈ hMeetFin.toFinset, (box n ν : Set (ι → ℝ))) ≠ ⊤ :=
      (measure_biUnion_finset_le _ _).trans_lt (by
        simp only [volume_box]
        exact ENNReal.sum_lt_top.mpr fun _ _ ↦ by finiteness) |>.ne
    have hle := measureReal_mono hsub hfinU
    rw [measureReal_biUnion_box n hMeetFin.toFinset, hcardM, le_div_iff₀ hnpow] at hle
    rw [hV]
    linarith
  have hITr : (Inside.ncard : ℝ) ≤ (Tag.ncard : ℝ) := by exact_mod_cast hcard_IT
  have hMIBr : (Meet.ncard : ℝ) ≤ (Inside.ncard : ℝ) + (Bd.ncard : ℝ) := by
    exact_mod_cast hcard_MIB
  have hTMr : (Tag.ncard : ℝ) ≤ (Meet.ncard : ℝ) := by exact_mod_cast hcard_TM
  rw [hNeq, abs_le]
  exact ⟨by linarith, by linarith⟩

end Sublemmas

end

end Chebotarev
