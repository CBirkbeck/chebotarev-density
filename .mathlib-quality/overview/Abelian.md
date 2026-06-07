# Inventory: `CebotarevDensity/Abelian.lean`

**File:** `/Users/mcu22seu/Documents/GitHub/chebotarev-density/CebotarevDensity/Abelian.lean` (1751 lines). Chebotarev's theorem, abelian case (Sharifi §7.2.2 Step 2). Sorry-free; no `axiom`; no `set_option`. All declarations live in `namespace Chebotarev` under `noncomputable section` with `@[expose] public section`. File-level `variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]` (lines 58–59) supplies `K L` to the public theorems that take them implicitly via the `variable` line; the private compositum leaves re-declare `K L M` explicitly in their own signatures.

Throughout, "comment/docstring mentions" of a name are excluded from "Used by" — only real call sites count.

---

### `theorem cyclic_subgroup_meets_G_times_one_trivially`
- **Type** · For finite groups `G H`, `σ : G`, `τ : H` with `Nat.card G ∣ orderOf τ`: `Subgroup.zpowers (σ,τ) ⊓ (⊤.prod ⊥) = ⊥`.
- **What** · Sharifi 7.2.2 Step 2 (i): the cyclic subgroup `⟨(σ,τ)⟩` meets `G × {1}` trivially when `|G| ∣ ord τ`.
- **How** · `eq_bot_iff`; take `(g,h)` in the meet; `Subgroup.mem_inf`/`mem_prod`/`mem_bot` give `h = 1` and `(g,h) = (σ,τ)^k`. From `h = τ^k = 1` and the chain `orderOf σ ∣ Nat.card G ∣ orderOf τ`, deduce `σ^k = 1` via `orderOf_dvd_iff_zpow_eq_one` / `orderOf_dvd_natCard`; hence `(g,h) = 1`.
- **Hypotheses** · `G`, `H` finite groups; `Nat.card G ∣ orderOf τ`.
- **Uses from project** · []
- **Used by** · unused in actual code (all four mentions at lines 141, 188, 445, 452 are docstring references; its mathematical role is inlined as `hgate` inside `exists_crossing_family_tagged`).
- **Visibility** · public (no `private`).
- **Lines** · 90–103.
- **Notes** · —

### `private theorem hasDirichletDensity_biUnion_const`
- **Type** · Over a number field `F`, finite `t : Finset ι`, `S : ι → Set (Ideal (𝓞 F))`, `c : ℝ`, with pairwise-disjoint `S` on `t` and `HasDirichletDensity (S i) c` for `i ∈ t`: `HasDirichletDensity (⋃ i ∈ t, S i) (t.card • c)`.
- **What** · A finite pairwise-disjoint union of sets each of density `c` has density `|t|·c`.
- **How** · `Finset.induction` on `t`. Base: `hasDirichletDensity_empty`. Step: `Set.disjoint_iUnion₂_right` for disjointness of the new piece from the union, then `HasDirichletDensity.union_of_disjoint`; the cardinality bookkeeping `(insert a t).card • c = c + t.card • c` via `Finset.card_insert_of_notMem` + `push_cast; ring`.
- **Hypotheses** · `[NumberField F]`; `(t : Set ι).PairwiseDisjoint S`; each `S i` (i ∈ t) has density `c`.
- **Uses from project** · [`HasDirichletDensity` (Density.lean), `hasDirichletDensity_empty` (Density.lean), `HasDirichletDensity.union_of_disjoint` (Density.lean)]
- **Used by** · `liminf_density_S_sigma_ge_card_H_n_div_GH` (line 966).
- **Visibility** · private.
- **Lines** · 109–128.
- **Notes** · —

### `private theorem pairwiseDisjoint_of_tag`
- **Type** · For `t : α → κ`, `f : ι → κ` injective, `S : ι → Set α`, with `∀ i, ∀ a ∈ S i, t a = f i`: `(Set.univ : Set ι).PairwiseDisjoint S`.
- **What** · A global tag `t` that is constant `= f i` on each `S i`, with `f` injective, forces the family pairwise disjoint.
- **How** · `Set.disjoint_left`; a common `a ∈ S i ∩ S j` would give `f i = t a = f j`, so `i = j` by injectivity of `f`, contradicting `i ≠ j`.
- **Hypotheses** · `f` injective; tag constant on each fibre.
- **Uses from project** · []
- **Used by** · `exists_cyclotomicCrossing_fibres` (line 908).
- **Visibility** · private.
- **Lines** · 209–215.
- **Notes** · —

### `private theorem prime_dvd_natAbs_discr_cyclotomic_dvd`
- **Type** · For a number field `E` with `[IsCyclotomicExtension {m} ℚ E]`, prime `p` with `p ∣ (discr E).natAbs`: `p ∣ m`.
- **What** · C2a-ramif: a prime ramifying in a rational `{m}`-cyclotomic field divides `m`.
- **How** · Contrapositive: assume `p ∤ m`. Reduce to showing `(p:ℤ) ∤ discr E` via `NumberField.not_dvd_discr_iff_forall_mem`, i.e. every prime `P ∣ p` of `𝓞 E` is unramified. Show `Ideal.under ℤ P = span {p}` (it is maximal by `PrincipalIdealRing.isMaximal_of_irreducible`, and `≤ under`), `P ≠ ⊥`, then `Algebra.isUnramifiedAt_iff_of_isDedekindDomain` reduces unramifiedness to `ramificationIdx = 1`, supplied by `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd` (the key cyclotomic input).
- **Hypotheses** · `[NumberField E]`, `[NeZero m]`, `[IsCyclotomicExtension {m} ℚ E]`; `p.Prime`; `p ∣ (discr E).natAbs`.
- **Uses from project** · []
- **Used by** · `cyclotomicField_finrank_eq` (line 316).
- **Visibility** · private.
- **Lines** · 232–262.
- **Notes** · &gt;30 lines.

### `private theorem cyclotomicField_finrank_eq`
- **Type** · For `K, M` number fields, `[Algebra K M]`, `[IsCyclotomicExtension {m} K M]`, `hcop : (discr K).natAbs.Coprime m`: `Module.finrank K M = m.totient`.
- **What** · C2a (the deep ramification/Minkowski leaf): `[K(μ_m):K] = φ(m)` when `m` is coprime to `disc K`.
- **How** · Pick primitive root `ζ ∈ M`. Form intermediate fields over `ℚ`: cyclotomic copy `K₁ = ℚ(ζ)` (`[IsCyclotomicExtension {m} ℚ K₁]`, so `finrank ℚ K₁ = φ(m)` by `IsCyclotomicExtension.finrank` + `cyclotomic.irreducible_rat`) and base copy `K₂ = range(K→M)`. Show `K₁ ⊔ K₂ = ⊤` (since `adjoin K {ζ} = ⊤` by `adjoin_primitive_root_eq_top` + `restrictScalars`). Transport `discr K₂ = discr K` along the ring equiv `eK₂` (`discr_eq_discr_of_ringEquiv`); the deep step proves `IsCoprime (discr K₁) (discr K₂)` using `prime_dvd_natAbs_discr_cyclotomic_dvd` + `hcop`. Linear disjointness `NumberField.linearDisjoint_of_isGalois_isCoprime_discr` gives `finrank K₂ M = finrank ℚ K₁ = φ(m)` (via `LinearDisjoint.finrank_right_eq_finrank`); relabel `finrank K M = finrank K₂ M` by `Algebra.finrank_eq_of_equiv_equiv`.
- **Hypotheses** · `[NumberField K]`, `[NumberField M]`, `[Algebra K M]`, `[NeZero m]`, `[IsCyclotomicExtension {m} K M]`; `hcop`.
- **Uses from project** · [`prime_dvd_natAbs_discr_cyclotomic_dvd` (in-file)]
- **Used by** · `compositum_charProd_bijective` (351), `autToPow_L_bijective` (407), `exists_crossing_family_tagged` (891).
- **Visibility** · private.
- **Lines** · 272–331.
- **Notes** · &gt;30 lines; the project's isolated "deep leaf" (linear-disjointness via coprime discriminants).

### `private theorem compositum_charProd_bijective`
- **Type** · Tower `K ⊆ L ⊆ M` (all number fields, `IsGalois K L`, `IsGalois K M`, `[IsCyclotomicExtension {m} L M]`), `hcop : (discr L).natAbs.Coprime m`, primitive root `ζ`: `Function.Bijective ((restrictNormalHom L).prod (hζ.autToPow K))`.
- **What** · C1's analytic heart: the joint map `Φ : Gal(M/K) → Gal(L/K) × (ℤ/mℤ)ˣ` is bijective.
- **How** · `IsGalois.tower_top_of_isGalois` gives `IsGalois L M`. Cardinality count `card Gal(M/K) = card Gal(L/K) · card (ZMod m)ˣ` from `IsGalois.card_aut_eq_finrank`, `finrank_mul_finrank`, `cyclotomicField_finrank_eq L M m hcop` (`[M:L]=φ(m)`), `ZMod.card_units_eq_totient`. Injectivity: `σ` with `Φ σ = 1` fixes `ζ` (its `autToPow K`-value is 1, via `autToPow_spec`, handling `m=1` separately) and fixes `L` pointwise (`restrictNormal_commutes` with trivial `L`-restriction); since `M = adjoin L {ζ}` (`adjoin_primitive_root_eq_top`), `Algebra.adjoin_induction` forces `σ = 1`. Conclude with `Nat.bijective_iff_injective_and_card`.
- **Hypotheses** · full tower + Galois + cyclotomic instances; `hcop`; `IsPrimitiveRoot ζ m`.
- **Uses from project** · [`cyclotomicField_finrank_eq` (in-file)]
- **Used by** · `gal_compositum_prod_iso` (432), `exists_crossing_family_tagged` (796).
- **Visibility** · private.
- **Lines** · 339–392.
- **Notes** · &gt;30 lines.

### `private theorem autToPow_L_bijective`
- **Type** · Same tower hypotheses; `hcop`, primitive root `ζ`: `Function.Bijective (hζ.autToPow L)`.
- **What** · The cyclotomic character `Gal(M/L) → (ℤ/mℤ)ˣ` is bijective (the `H ≅ (ℤ/mℤ)ˣ` half of C1).
- **How** · Injectivity is `IsPrimitiveRoot.autToPow_injective`; surjectivity from cardinality `card Gal(M/L) = card (ZMod m)ˣ` (via `card_aut_eq_finrank L M`, `cyclotomicField_finrank_eq L M m hcop`, `ZMod.card_units_eq_totient`); `Nat.bijective_iff_injective_and_card`.
- **Hypotheses** · full tower + Galois + cyclotomic; `hcop`; `IsPrimitiveRoot ζ m`.
- **Uses from project** · [`cyclotomicField_finrank_eq` (in-file)]
- **Used by** · `gal_compositum_prod_iso` (431), `exists_crossing_family_tagged` (800).
- **Visibility** · private.
- **Lines** · 399–411.
- **Notes** · —

### `private theorem gal_compositum_prod_iso`
- **Type** · Same tower; `_hcop`: `Nonempty (Gal(M/K) ≃* Gal(L/K) × Gal(M/L))`.
- **What** · C1: the `G × H` splitting of the compositum, `Gal(M/K) ≅ Gal(L/K) × Gal(M/L)`.
- **How** · Pick `ζ`. Build `e2 : Gal(M/L) ≃* (ZMod m)ˣ` from `autToPow_L_bijective` via `MulEquiv.ofBijective`. Compose `MulEquiv.ofBijective Φ (compositum_charProd_bijective …)` (giving `≃* Gal(L/K) × (ZMod m)ˣ`) with `(MulEquiv.refl _).prodCongr e2.symm` to restore the `Gal(M/L)` factor.
- **Hypotheses** · full tower + Galois + cyclotomic; `_hcop` (passed through to the bijectivity leaves).
- **Uses from project** · [`compositum_charProd_bijective` (in-file), `autToPow_L_bijective` (in-file)]
- **Used by** · unused in actual code (mentioned only in docstrings at lines 184, 769; `exists_crossing_family_tagged` instead uses `compositum_charProd_bijective` and `autToPow_L_bijective` directly).
- **Visibility** · private.
- **Lines** · 422–433.
- **Notes** · —

### `private theorem compositum_isCyclotomic_over_fixedField`
- **Type** · Same tower; `g : Gal(M/K)`; `_hmeet : zpowers g ⊓ (adjoin K {b | b^m=1}).fixingSubgroup = ⊥`: `IsCyclotomicExtension {m} ↥(fixedField (zpowers g)) M` (with the mid scalar-tower instance).
- **What** · C3: `M` is `{m}`-cyclotomic over the fixed field `F = M^⟨g⟩`, given the corrected gate `⟨g⟩ ∩ Gal(M/K(μ_m)) = ⊥`.
- **How** · Pick `ζ`; show `adjoin K {ζ} = Kμ := adjoin K {b|b^m=1}` (roots of unity are powers of `ζ`, via `eq_pow_of_pow_eq_one`). From `_hmeet`: `(F ⊔ Kμ).fixingSubgroup = ⊥` (`fixingSubgroup_sup` + `fixingSubgroup_fixedField`), hence `F ⊔ Kμ = ⊤` (Galois correspondence `IsGalois.fixedField_fixingSubgroup` + `fixedField_bot`). Transport to `adjoin F {ζ} = ⊤` via `restrictScalars_adjoin_eq_sup`. Finally `IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension` over `F`, transported to `M` along `IntermediateField.topEquiv` by `IsCyclotomicExtension.equiv`.
- **Hypotheses** · full tower + Galois + cyclotomic; the corrected meet `_hmeet`.
- **Uses from project** · []
- **Used by** · `exists_crossing_family_tagged` (872).
- **Visibility** · private.
- **Lines** · 463–504.
- **Notes** · &gt;30 lines; carries a long "Gate correction (2026-06-07)" docstring documenting why the gate is `K(μ_m).fixingSubgroup` (= `G × {1}`) and not `ker(restrictNormalHom L)`.

### `private theorem smul_algebraMap_eq_repl`
- **Type** · Same tower; `σ : Gal(M/K)`, `y : 𝓞 L`: `σ • algebraMap (𝓞 L) (𝓞 M) y = algebraMap (𝓞 L) (𝓞 M) ((σ.restrictNormal L) • y)`.
- **What** · The embedding `𝓞 L → 𝓞 M` intertwines `σ` with its normal restriction `σ ↾ L`.
- **How** · Via `RingOfIntegers.ext_iff`, push everything to `M`: two "bridge" lemmas `(g • x : 𝓞·) : · = g • (x:·)` (from `smul_distrib_smul`) for `M` and `L`, a coercion-compatibility lemma through `IsScalarTower.algebraMap_apply`, then `AlgEquiv.restrictNormal_commutes`.
- **Hypotheses** · full tower + Galois.
- **Uses from project** · []
- **Used by** · `isArithFrobAt_restrictNormal_repl` (551).
- **Visibility** · private.
- **Lines** · 512–533.
- **Notes** · Replica of the `private` mathlib/CNR lemma `CyclotomicNormResidue.smul_algebraMap_eq` (unreachable), adapted to abstract `K⊆L⊆M`.

### `private theorem isArithFrobAt_restrictNormal_repl`
- **Type** · Same tower; `σ : Gal(M/K)`, `𝔓 : Ideal (𝓞 M)`, `hσ : IsArithFrobAt (𝓞 K) σ 𝔓`: `IsArithFrobAt (𝓞 K) (σ.restrictNormal L) (𝔓.under (𝓞 L))`.
- **What** · Downward Frobenius restriction: `σ ↾ L` is an arithmetic Frobenius at `𝔓 ∩ 𝓞 L`.
- **How** · `Ideal.under_under` aligns the base contractions; unfold the defining congruence (`Ideal.mem_comap`, `map_sub`, `map_pow`); rewrite `MulSemiringAction.toAlgHom … = (σ.restrictNormal L) • ·` and apply `smul_algebraMap_eq_repl` to push to `𝓞 M`, then invoke `hσ` at `algebraMap (𝓞 L) (𝓞 M) y`.
- **Hypotheses** · full tower + Galois; `hσ`.
- **Uses from project** · [`smul_algebraMap_eq_repl` (in-file)]
- **Used by** · `frobeniusClass_proj` (587).
- **Visibility** · private.
- **Lines** · 540–552.
- **Notes** · Replica of `private` `CyclotomicNormResidue.isArithFrobAt_restrictNormal`.

### `private theorem frobeniusClass_proj`
- **Type** · Same tower; `σ : Gal(L/K)`, `τM : Gal(M/K)` with `restrictNormalHom L τM = σ`; prime `𝔭`, `UnramifiedIn K M 𝔭`, `UnramifiedIn K L 𝔭`, `frobeniusClass K M 𝔭 = mk τM`: `frobeniusClass K L 𝔭 = mk σ`.
- **What** · C4: a prime with `Gal(M/K)`-Frobenius `(σ,τ)` has `Gal(L/K)`-Frobenius the `G`-projection `σ`; this lands each crossing fibre in `S_σ`.
- **How** · `by_cases 𝔭.IsPrime`. Prime case: pick `𝔓 ∣ 𝔭` in `𝓞 M` (`exists_prime_liesOver`, finiteness of `𝓞 M ⧸ 𝔓` from `ne_bot_of_ramificationIdx_eq_one` + `UnramifiedIn.ramificationIdx_eq_one`); set `σM = arithFrobAt 𝔓`. Then `frobeniusClass K M 𝔭 = mk σM` (`frobeniusClass_eq_mk_of_isArithFrobAt`), so `IsConj σM τM`. `isArithFrobAt_restrictNormal_repl` makes `σM ↾ L` a Frobenius at `𝔓 ∩ 𝓞 L`, giving `frobeniusClass K L 𝔭 = mk (σM ↾ L)`. Conjugacy descends through `restrictNormalHom L` (`MonoidHom.map_isConj`), and `restrictNormalHom L τM = σ` closes it. Non-prime case: both classes are the junk value `mk 1` (`frobeniusClass` `dif_neg`), forcing `τM = 1` (`isConj_one_right`) hence `σ = 1`.
- **Hypotheses** · full tower + Galois; restriction equation; both unramifiedness facts; the `M`-Frobenius equation.
- **Uses from project** · [`exists_prime_liesOver` (Frobenius.lean), `UnramifiedIn.ne_bot` (Frobenius.lean), `ne_bot_of_ramificationIdx_eq_one` (Frobenius.lean), `UnramifiedIn.ramificationIdx_eq_one` (Frobenius.lean), `arithFrobAt` / `IsArithFrobAt.arithFrobAt` (mathlib), `frobeniusClass_eq_mk_of_isArithFrobAt` (Frobenius.lean), `frobeniusClass` (Frobenius.lean), `isArithFrobAt_restrictNormal_repl` (in-file)]
- **Used by** · `exists_crossing_family_tagged` (828).
- **Visibility** · private.
- **Lines** · 565–609.
- **Notes** · &gt;30 lines; tower analogue of `Main.arithFrobAt_restrictScalars_eq`, replicated here because `Main` imports `Abelian`.

### `private theorem density_lift_through_fixedField_repl`
- **Type** · `K, M` number fields, `[IsGalois K M]`, `[FiniteDimensional K M]`; `σM : Gal(M/K)`, `E : IntermediateField K M`, `σE : Gal(M/E)` with `σE.restrictScalars K = σM`, `E = fixedField (zpowers σM)`, and density `(card Gal(M/E))⁻¹` of `E`'s `σE`-fibre: yields density `(card (mk σM).carrier)/(card Gal(M/K))` of `K`'s `σM`-fibre.
- **What** · C5: the Step-1 cyclic density transfer through a fixed field, restated with top field `M`.
- **How** · One-line application of the shared lemma `density_lift_through_fixedField` (relocated to `CebotarevDensity.FixedFieldDensity`) at `L ↦ M`.
- **Hypotheses** · as above.
- **Uses from project** · [`density_lift_through_fixedField` (FixedFieldDensity.lean), plus the `HasDirichletDensity`/`UnramifiedIn`/`frobeniusClass` API in the statement]
- **Used by** · `exists_crossing_family_tagged` (879).
- **Visibility** · private.
- **Lines** · 627–640.
- **Notes** · Long "Resolution (relocation, 2026-06-07)" docstring; the body is genuinely one line (no longer a replica).

### `private theorem isGalois_compositum_base`
- **Type** · `L/K` Galois number fields, `M` a number field with `[Algebra K M]`, `[Algebra L M]`, `[IsScalarTower K L M]`, `[IsCyclotomicExtension {m} L M]`: `IsGalois K M`.
- **What** · The compositum `M = L(μ_m)` is Galois over the base `K`.
- **How** · Separability is automatic (char 0). For normality, pick `ζ`; set `A = range(K→M)` (normal via `Normal.of_algEquiv` of `AlgEquiv.ofInjectiveField`) and `B = adjoin K {ζ} = K(μ_m)` (cyclotomic hence Galois/normal). Show `A ⊔ B = ⊤` (`adjoin_primitive_root_eq_top` + `restrictScalars`); `IntermediateField.normal_sup` gives `Normal K (A ⊔ B) = Normal K ⊤`, transported to `M` by `topEquiv`. Conclude `IsGalois.mk`.
- **Hypotheses** · tower + cyclotomic instances.
- **Uses from project** · []
- **Used by** · `exists_crossing_family_tagged` (787).
- **Visibility** · private.
- **Lines** · 649–682.
- **Notes** · &gt;30 lines.

### `private theorem map_eq_of_isConj_comm` ⚠ FLAGGED
- **Type** · `χ : G →* A` with `A` a `CommGroup`, `IsConj a b`: `χ a = χ b`.
- **What** · A hom into a commutative group is conjugacy-invariant.
- **How** · Write `b = u·a·u⁻¹` from `IsConj`; `map_mul`/`map_inv` + `mul_comm` to cancel `χ u`.
- **Hypotheses** · `[Group G]`, `[CommGroup A]`; `IsConj a b`.
- **Uses from project** · []
- **Used by** · `exists_crossing_family_tagged` (line 836 — its **sole** consumer, used to read the tag `χK (Frob).out` off any conjugate representative).
- **Visibility** · private.
- **Lines** · 687–692.
- **Notes** · **Flag (per task):** known replica of a deleted CNR lemma. Current state: exactly one live consumer (`exists_crossing_family_tagged`); it is not dead code. The generic mathlib name for this is `MonoidHom.apply_eq_of_isConj`/conjugacy-invariance of abelian-target homs — if that exists upstream it could replace this replica, but as of this tree it has a real in-file use, so deleting it would break `exists_crossing_family_tagged`.

### `private theorem unramifiedIn_tower_descend`
- **Type** · Tower `K ⊆ L ⊆ M` (number fields, `IsGalois K L`, `IsGalois K M`); prime `𝔭`, `UnramifiedIn K M 𝔭`: `UnramifiedIn K L 𝔭`.
- **What** · Unramifiedness in the top field descends to the intermediate field.
- **How** · Take maximal `𝔮 ∣ 𝔭` in `𝓞 L`; pick `𝔓 ∣ 𝔮` in `𝓞 M` (`Ideal.exists_ideal_over_prime_of_isIntegral`); transfer non-bottom/maximality via `Ideal.ne_bot_of_liesOver_of_ne_bot`. From the `M`-side, `e(𝔓/𝔭) = 1` (`isUnramifiedAt_iff_of_isDedekindDomain`); `Ideal.ramificationIdx_algebra_tower` factors `1 = e(𝔮/𝔭)·e(𝔓/𝔮)`, so `Nat.eq_one_of_mul_eq_one_right` gives `e(𝔮/𝔭) = 1`; reconvert via `isUnramifiedAt_iff_of_isDedekindDomain`.
- **Hypotheses** · tower + Galois; `UnramifiedIn K M 𝔭`.
- **Uses from project** · [`UnramifiedIn` (Frobenius.lean) — used via `.1`/`.2` accessors]
- **Used by** · `exists_crossing_family_tagged` (826).
- **Visibility** · private.
- **Lines** · 699–728.
- **Notes** · &gt;30 lines.

### `private theorem autToPow_eq_one_of_fixes`
- **Type** · `[Algebra K M]`, primitive root `ζ` of order `m`, `g : Gal(M/K)` with `g ζ = ζ`: `hζ.autToPow K g = 1`.
- **What** · An automorphism fixing a primitive root has trivial cyclotomic character (no cyclotomic-over-`K` hypothesis needed).
- **How** · `autToPow_spec` gives `g ζ = ζ^(u.val)` with `u = autToPow K g`; from `g ζ = ζ` get `ζ^(u.val) = ζ^1`. Lift `ζ` to `Mˣ`, use `orderOf z = m` (`IsPrimitiveRoot.eq_orderOf`) and `pow_eq_pow_iff_modEq` to get `u.val ≡ 1 [MOD m]`, hence `(u : ZMod m) = 1` (`ZMod.natCast_val`/`cast_id`), so `u = 1` (`Units.ext`).
- **Hypotheses** · `[Field K]`, `[Field M]`, `[Algebra K M]`, `[NeZero m]`; `IsPrimitiveRoot ζ m`; `g ζ = ζ`.
- **Uses from project** · []
- **Used by** · `exists_crossing_family_tagged` (853).
- **Visibility** · private.
- **Lines** · 735–754.
- **Notes** · —

### `private theorem exists_crossing_family_tagged`
- **Type** · `L/K` Galois number fields, `[FiniteDimensional K L]`, `[IsMulCommutative Gal(L/K)]`, `σ : Gal(L/K)`, `m ≥ 1`, `hm4 : m % 4 ≠ 2`, `hcop : (discr L).natAbs.Coprime m`: existence of a global tag `t : Ideal (𝓞 K) → (ZMod m)ˣ` and a fibre family `S : {τ // card Gal(L/K) ∣ ord τ} → Set (Ideal (𝓞 K))` with (a) each `S τ ⊆ S_σ`, (b) tag `= τ` on `S τ`, (c) each `S τ` has density `(card Gal(L/K) · card (ZMod m)ˣ)⁻¹`.
- **What** · The cyclotomic-crossing tagged master leaf (Sharifi 7.2.2 Step 2): packages the full compositum construction with a separating tag.
- **How** · Carrier `M = CyclotomicField m L`; `isGalois_compositum_base` gives `IsGalois K M`, `tower_top` gives `IsGalois L M`. Pick `ζ`; `χK = autToPow K`. Bijectivity `Φ` (`compositum_charProd_bijective`) → `equivΦ : Gal(M/K) ≃* Gal(L/K) × (ZMod m)ˣ`; `e2` (`autToPow_L_bijective`); derive commutativity of `Gal(M/L)` and `Gal(M/K)`. Define `σM τ = equivΦ.symm (σ,τ)` (restricts to `σ`, has character `τ`). Tag `t 𝔭 = χK (frobeniusClass K M 𝔭).out`; fibre `S τ = {𝔭 : prime ∧ UnramifiedIn K M 𝔭 ∧ frobeniusClass K M 𝔭 = mk (σM τ)}`. (a) via `unramifiedIn_tower_descend` + `frobeniusClass_proj`. (b) `map_eq_of_isConj_comm` (out is conjugate to `σM τ`) + `hσMchar`. (c) prove the C3 gate `zpowers (σM τ) ⊓ (adjoin K {b|b^m=1}).fixingSubgroup = ⊥` inline (`g` fixes `ζ` ⇒ `χK g = 1` via `autToPow_eq_one_of_fixes`; with `g = (σM τ)^k`, `τ^k=1` ⇒ `|G| ∣ k` ⇒ `σ^k=1` ⇒ `Φ g = 1` ⇒ `g = 1` by injectivity); then `compositum_isCyclotomic_over_fixedField` makes `M/F` cyclotomic, `chebotarev_cyclotomic` gives the `F`-density, `density_lift_through_fixedField_repl` lifts it; arithmetic `card carrier = 1` (abelian) and `card Gal(M/K) = |G|·|H|` (`cyclotomicField_finrank_eq`) simplify the constant.
- **Hypotheses** · as above (`hm4` feeds `chebotarev_cyclotomic`; `hcop` feeds C1/C2a).
- **Uses from project** · [`isGalois_compositum_base`, `compositum_charProd_bijective`, `autToPow_L_bijective`, `unramifiedIn_tower_descend`, `frobeniusClass_proj`, `map_eq_of_isConj_comm`, `autToPow_eq_one_of_fixes`, `compositum_isCyclotomic_over_fixedField`, `density_lift_through_fixedField_repl`, `cyclotomicField_finrank_eq` (all in-file); `chebotarev_cyclotomic` (Cyclotomic.lean); `UnramifiedIn`, `frobeniusClass` (Frobenius.lean); `HasDirichletDensity` (Density.lean)]
- **Used by** · `exists_cyclotomicCrossing_fibres` (906).
- **Visibility** · private.
- **Lines** · 772–894.
- **Notes** · &gt;30 lines (~120). The central assembly leaf of the AB1 machinery; sorry-free.

### `private theorem exists_cyclotomicCrossing_fibres`
- **Type** · Same hypotheses as the tagged leaf: existence of `S : {τ // card Gal(L/K) ∣ ord τ} → Set (Ideal (𝓞 K))` that is (univ-)pairwise-disjoint, each `⊆ S_σ`, each of density `(card Gal(L/K)·card (ZMod m)ˣ)⁻¹`.
- **What** · The cyclotomic-crossing core (drops the tag, exposing only disjointness).
- **How** · Destructure `exists_crossing_family_tagged`; produce disjointness via `pairwiseDisjoint_of_tag t Subtype.val Subtype.val_injective S htag`.
- **Hypotheses** · `m ≥ 1`, `hm4`, `hcop`, abelian `Gal(L/K)`.
- **Uses from project** · [`exists_crossing_family_tagged` (in-file), `pairwiseDisjoint_of_tag` (in-file), `UnramifiedIn`/`frobeniusClass`/`HasDirichletDensity` in the statement]
- **Used by** · `liminf_density_S_sigma_ge_card_H_n_div_GH` (958).
- **Visibility** · private.
- **Lines** · 896–908.
- **Notes** · —

### `theorem liminf_density_S_sigma_ge_card_H_n_div_GH`
- **Type** · `L/K` Galois, `[FiniteDimensional K L]`, abelian `Gal(L/K)`, `σ`, `m ≥ 1`, `hm4`, `hcop`: `(card {τ // card Gal(L/K) ∣ ord τ}) / (card Gal(L/K) · card (ZMod m)ˣ) ≤ liminf (P_{S_σ}/P_univ) (𝓝[&gt;] 1)`.
- **What** · Sharifi 7.2.2 Step 2: the per-`m` lower bound `δ_inf(S_σ) ≥ |H_n|/(|G|·|H|)`.
- **How** · Get the crossing fibres `S` (`exists_cyclotomicCrossing_fibres`); make the index `Fintype`; their disjoint union has density `|t|•c = |H_n|/(|G|·|H|)` (`hasDirichletDensity_biUnion_const`). The union `⊆ S_σ` (`Set.iUnion₂_subset`), so its lower density bounds that of `S_σ` (`HasDirichletDensity.hasLower` + `HasLowerDirichletDensity.mono`); the lower density of `S_σ` is definitionally the target `liminf`. Identify `|t|•c` with the LHS (`Finset.card_univ`, `smul_eq_mul`, `div_eq_mul_inv`).
- **Hypotheses** · as above (carries the same admissibility hypotheses `hm4`/`hcop` as the crossing).
- **Uses from project** · [`exists_cyclotomicCrossing_fibres` (in-file), `hasDirichletDensity_biUnion_const` (in-file), `UnramifiedIn`/`frobeniusClass` (Frobenius.lean), `primeIdealZetaSum`, `HasDirichletDensity.hasLower`, `HasLowerDirichletDensity` + `.mono` (Density.lean)]
- **Used by** · `liminf_ratio_ge_inv_card_G` (1433).
- **Visibility** · public.
- **Lines** · 938–981.
- **Notes** · &gt;30 lines.

### `private theorem torsion_card_le`
- **Type** · Finite `CommGroup G`, `M : ℕ`: `card {x // x^M = 1} · (E / gcd E M) ≤ card G`, where `E = Monoid.exponent G`.
- **What** · Uniform (cyclicity-free) torsion bound.
- **How** · Let `f = powMonoidHom M`; `card f.ker = card {x // x^M=1}` and `card f.ker · card f.range = card G` (`card_eq_card_quotient_mul_card_subgroup` + `quotientKerEquivRange`). Take `g` with `orderOf g = E` (`exists_orderOf_eq_exponent`); then `orderOf (g^M) = E / gcd E M` (`orderOf_pow`) and `orderOf (g^M) ≤ card f.range` (zpowers of `g^M` inject into the range). Combine in a `calc`.
- **Hypotheses** · `[CommGroup G]`, `[Finite G]`.
- **Uses from project** · []
- **Used by** · `perprime_bound` (1202), `perprime_bound_exp` (1241).
- **Visibility** · private.
- **Lines** · 994–1015.
- **Notes** · —

### `private theorem dvd_capped`
- **Type** · `E d p v : ℕ`, `p.Prime`, `E ≠ 0`, `d ∣ E`, `d.factorization p ≤ v - 1`: `d ∣ ordCompl[p] E * p^(v-1)`.
- **What** · `d` divides the modulus with `E`'s `p`-part capped at `p^(v-1)`.
- **How** · `Nat.factorization_le_iff_dvd`; compute factorizations of the product (`factorization_mul`, `factorization_pow`, `factorization_ordCompl`); split `q = p` (gives `≤ v-1`, by hypothesis) vs `q ≠ p` (matches `d`'s factorization at `q`).
- **Hypotheses** · as above.
- **Uses from project** · []
- **Used by** · `perprime_bound` (1191), `perprime_bound_exp` (1230).
- **Visibility** · private.
- **Lines** · 1020–1033.
- **Notes** · —

### `private theorem M_dvd_E`
- **Type** · `E p v : ℕ`, `p.Prime`, `E ≠ 0`, `v - 1 ≤ E.factorization p`: `ordCompl[p] E * p^(v-1) ∣ E`.
- **What** · The capped modulus divides `E`.
- **How** · `factorization_le_iff_dvd`; compare factorizations componentwise (split `q=p` via `omega`, `q≠p` trivial).
- **Hypotheses** · as above.
- **Uses from project** · []
- **Used by** · `perprime_bound` (1184), `perprime_bound_exp` (1223).
- **Visibility** · private.
- **Lines** · 1036–1047.
- **Notes** · —

### `private theorem E_eq_M_mul`
- **Type** · `E p v : ℕ`, `v - 1 ≤ E.factorization p`: `E = ordCompl[p] E * p^(v-1) * p^(E.factorization p - (v-1))`.
- **What** · Factor out the complementary `p`-power (to compute `E/M`).
- **How** · `mul_assoc`, `pow_add` (sum of exponents `= E.factorization p`, by `omega`), then `Nat.ordProj_mul_ordCompl_eq_self`.
- **Hypotheses** · as above.
- **Uses from project** · []
- **Used by** · `perprime_bound` (1187), `perprime_bound_exp` (1226).
- **Visibility** · private.
- **Lines** · 1051–1055.
- **Notes** · —

### `private theorem pk_dvd_carmichael`
- **Type** · `n k p : ℕ`, `p.Prime`, `p ∣ n`: `p^(k·v_p(n) - 2) ∣ carmichael (n^k)`.
- **What** · Power-of-`p` divisibility of the Carmichael function of `n^k`.
- **How** · `p^(k·v) ∣ n^k` (`pow_dvd_pow_of_dvd` of `ordProj_dvd`), so `carmichael (p^(k·v)) ∣ carmichael (n^k)` (`carmichael_dvd`). Then `p^(k·v-2) ∣ carmichael (p^(k·v))`: split `p=2` (`carmichael_two_pow_of_ne_two`, and `k·v=2` by `norm_num`) vs `p≠2` (`carmichael_pow_of_prime_ne_two` then `totient_prime_pow_succ`). Chain the two divisibilities.
- **Hypotheses** · `p.Prime`, `p ∣ n`.
- **Uses from project** · []
- **Used by** · `perprime_bound` (1181).
- **Visibility** · private.
- **Lines** · 1059–1079.
- **Notes** · &gt;30 lines.

### `private theorem bad_le_torsion`
- **Type** · Finite monoid `G`, `M p v : ℕ`, `∀ x, ¬ p^v ∣ orderOf x → x^M = 1`: `card {x // ¬ p^v ∣ orderOf x} ≤ card {x // x^M = 1}`.
- **What** · The "bad at `p`" set injects into the `M`-torsion subgroup.
- **How** · `Nat.card_le_card_of_injective` with `x ↦ ⟨x.1, h …⟩` (injective on the underlying value).
- **Hypotheses** · `[Finite G]`, `[Monoid G]`; the implication `h`.
- **Uses from project** · []
- **Used by** · `perprime_bound` (1189), `perprime_bound_exp` (1228).
- **Visibility** · private.
- **Lines** · 1083–1087.
- **Notes** · —

### `private theorem exists_prime_pow_not_dvd`
- **Type** · `n d : ℕ`, `n ≠ 0`, `d ≠ 0`, `¬ n ∣ d`: `∃ p ∈ n.primeFactors, ¬ p^(n.factorization p) ∣ d`.
- **What** · If `n ∤ d`, some prime power `p^{v_p(n)}` already fails to divide `d`.
- **How** · Contrapositive: assuming all such prime powers divide `d`, prove `n ∣ d` via `factorization_le_iff_dvd`, splitting `p ∈ primeFactors` (`pow_dvd_iff_le_factorization`) vs not (factorization `0`).
- **Hypotheses** · `n, d ≠ 0`; `¬ n ∣ d`.
- **Uses from project** · []
- **Used by** · `H_n_ratio_ge` (1277), `H_n_over_H_tends_to_one` (1352).
- **Visibility** · private.
- **Lines** · 1091–1103.
- **Notes** · —

### `private theorem card_le_sum_card`
- **Type** · Finite `G`, `s : Finset ι`, predicates `P, Q i`, with `∀ x, P x → ∃ i ∈ s, Q i x`: `card {x // P x} ≤ ∑ i ∈ s, card {x // Q i x}`.
- **What** · A `P`-subtype injects into a finite union of `Q i`-subtypes, bounding its cardinality by the sum.
- **How** · `Fintype` instances; `Fintype.card_subtype` rewrites to filtered-`Finset` cardinalities; the `P`-filter sits inside `s.biUnion (filter (Q i))` (each `x` lands in some `i`), bounded by `Finset.card_biUnion_le`.
- **Hypotheses** · `[Finite G]`; the covering implication.
- **Uses from project** · []
- **Used by** · `H_n_ratio_ge` (1275), `H_n_over_H_tends_to_one` (1349).
- **Visibility** · private.
- **Lines** · 1107–1122.
- **Notes** · —

### `private theorem summand_tendsto`
- **Type** · `p v : ℕ`, `2 ≤ p`, `1 ≤ v`: `Tendsto (fun k ↦ 1/p^(k·v - v - 1)) atTop (𝓝 0)`.
- **What** · Each per-prime tail `→ 0` as `k → ∞`.
- **How** · `p⁻¹ &lt; 1`, so `(p⁻¹)^m → 0` (`tendsto_pow_atTop_nhds_zero_of_lt_one`); the exponent `k·v-v-1 → ∞` (dominates `k-(v+1)`); compose and rewrite `1/p^· = (p⁻¹)^·`.
- **Hypotheses** · `2 ≤ p`, `1 ≤ v`.
- **Uses from project** · []
- **Used by** · `H_n_over_H_tends_to_one` (1338, 1472); `liminf_ratio_ge_inv_card_G` (1472 is inside the latter — see below). (Real callers: `H_n_over_H_tends_to_one` and `liminf_ratio_ge_inv_card_G`.)
- **Visibility** · private.
- **Lines** · 1126–1138.
- **Notes** · —

### `private theorem ratio_bound`
- **Type** · `bad total : ℕ`, `s : Finset ℕ`, `badp e P : ℕ → ℕ`, `0 &lt; total`, `bad ≤ ∑ badp p`, `∀ p ∈ s, 0 &lt; P p`, `∀ p ∈ s, badp p · (P p)^(e p) ≤ total`: `(bad : ℝ)/total ≤ ∑ p ∈ s, 1/(P p)^(e p)`.
- **What** · The bad ratio is bounded by the sum of per-prime tails.
- **How** · `(bad:ℝ) ≤ ∑ badp p` (cast of `hcover`); `gcongr` and `Finset.sum_div`; termwise `div_le_div_iff₀` reduces `badp p / total ≤ 1/(P p)^(e p)` to the hypothesis `hbound` (after casting the product to `ℝ`).
- **Hypotheses** · as above.
- **Uses from project** · []
- **Used by** · `H_n_ratio_ge` (1270), `H_n_over_H_tends_to_one` (1344).
- **Visibility** · private.
- **Lines** · 1143–1160.
- **Notes** · —

### `private theorem perprime_bound`
- **Type** · `n k p : ℕ`, `p.Prime`, `p ∣ n`, `2 ≤ n`, `2 ≤ k`: `card {τ : (ZMod (n^k))ˣ // ¬ p^{v_p(n)} ∣ ord τ} · p^{k·v_p(n) - v_p(n) - 1} ≤ card (ZMod (n^k))ˣ`.
- **What** · The Carmichael-keyed per-prime bound in the unit group of `ZMod (n^k)`.
- **How** · Set `E = exponent G`, `M = ordCompl[p] E · p^(v-1)`. From `pk_dvd_carmichael` (via `carmichael_eq_exponent'`) get `k·v - 2 ≤ v_p(E)`, hence `v-1 ≤ v_p(E)`, so `M ∣ E` (`M_dvd_E`), `gcd E M = M`, `E/M = p^(v_p(E)-(v-1))` (`E_eq_M_mul`). The bad set injects into `M`-torsion (`bad_le_torsion` via `dvd_capped`), and `p^(k·v-v-1) ≤ E/M`. Chain through `torsion_card_le`.
- **Hypotheses** · as above.
- **Uses from project** · [`pk_dvd_carmichael`, `M_dvd_E`, `E_eq_M_mul`, `bad_le_torsion`, `dvd_capped`, `torsion_card_le` (all in-file)]
- **Used by** · `H_n_over_H_tends_to_one` (1356).
- **Visibility** · private.
- **Lines** · 1164–1202.
- **Notes** · &gt;30 lines.

### `private theorem perprime_bound_exp`
- **Type** · Finite `CommGroup G`, `p a v : ℕ`, `p.Prime`, `1 ≤ v`, `v ≤ a`, `p^a ∣ exponent G`: `card {x // ¬ p^v ∣ ord x} · p^(a - v - 1) ≤ card G`.
- **What** · Exponent-keyed generalisation of `perprime_bound` to any finite commutative group.
- **How** · Identical to `perprime_bound` but with the Carmichael input replaced by the hypothesis `p^a ∣ exponent G` (so `a ≤ v_p(E)`); `M_dvd_E`, `E_eq_M_mul`, `bad_le_torsion` (+ `dvd_capped`), `torsion_card_le`.
- **Hypotheses** · as above.
- **Uses from project** · [`M_dvd_E`, `E_eq_M_mul`, `bad_le_torsion`, `dvd_capped`, `torsion_card_le` (all in-file)]
- **Used by** · `H_n_ratio_ge` (1284).
- **Visibility** · private.
- **Lines** · 1213–1241.
- **Notes** · &gt;30 lines.

### `private theorem H_n_ratio_ge`
- **Type** · Finite `CommGroup G`, `n k : ℕ`, `2 ≤ n`, `1 ≤ k`, `∀ p ∈ n.primeFactors, p^(k·v_p(n)) ∣ exponent G`: `1 - ∑_{p ∣ n} 1/p^(k·v_p(n) - v_p(n) - 1) ≤ (card {τ // n ∣ ord τ})/card G`.
- **What** · Single-group form of the `H_n`-ratio lower bound.
- **How** · `good + bad = total` (subtype complement count); `bad/total ≤ ∑ tails` (`ratio_bound` with cover from `card_le_sum_card` + `exists_prime_pow_not_dvd`, per-prime bound from `perprime_bound_exp`); `good/total = 1 - bad/total` (`field_simp`/`linarith`); finish by `linarith`.
- **Hypotheses** · as above.
- **Uses from project** · [`card_le_sum_card`, `exists_prime_pow_not_dvd`, `ratio_bound`, `perprime_bound_exp` (all in-file)]
- **Used by** · `liminf_ratio_ge_inv_card_G` (1489).
- **Visibility** · private.
- **Lines** · 1250–1292.
- **Notes** · &gt;30 lines.

### `theorem H_n_over_H_tends_to_one`
- **Type** · `n : ℕ`, `1 ≤ n`: `Tendsto (fun k ↦ (card {τ : (ZMod (n^k))ˣ // n ∣ ord τ})/card (ZMod (n^k))ˣ) atTop (𝓝 1)`.
- **What** · Sharifi 7.2.2 Step 2 (v): `|H_n|/|H| → 1` along `m = n^k` as `k → ∞`.
- **How** · `n = 1`: ratio `≡ 1` (`subtypeUnivEquiv` since `1 ∣ ·`). `n ≥ 2`: `good+bad = total`; `bad/total → 0` squeezed by `S(k) = ∑ tails → 0` (`tendsto_finsetSum` + `summand_tendsto`), the upper bound via `ratio_bound`/`card_le_sum_card`/`exists_prime_pow_not_dvd`/`perprime_bound`; then `good/total = 1 - bad/total → 1`.
- **Hypotheses** · `1 ≤ n`.
- **Uses from project** · [`summand_tendsto`, `ratio_bound`, `card_le_sum_card`, `exists_prime_pow_not_dvd`, `perprime_bound` (all in-file)]
- **Used by** · **unused in file** (and unused project-wide). The two name occurrences at lines 983, 1244 are docstring/section-header references. The live density argument uses the admissible-prime route via `H_n_ratio_ge` instead (see `liminf_ratio_ge_inv_card_G`); this `m = n^k` form is documented as superseded.
- **Visibility** · public.
- **Lines** · 1297–1365.
- **Notes** · &gt;30 lines; dead/legacy in the live proof chain.

### `theorem liminf_ratio_ge_inv_card_G`
- **Type** · `L/K` Galois, `[FiniteDimensional K L]`, abelian `Gal(L/K)`, `σ`: `(card Gal(L/K))⁻¹ ≤ liminf (P_{S_σ}/P_univ) (𝓝[&gt;] 1)`.
- **What** · Per-`σ` lower bound `δ_inf(S_σ) ≥ 1/|G|` (lower half of Sharifi 7.2.2 Step 2).
- **How** · `n = card Gal(L/K)`, `dB = |disc L|`. For each `k`, pick an admissible prime `m_k &gt; dB` with `m_k ≡ 1 (mod 4·n^k)` (`Nat.forall_exists_prime_gt_and_modEq`), giving `m_k % 4 = 1 ≠ 2` and `n^k ∣ m_k - 1`; `m_k` coprime to `dB`. For prime `m_k`, `exponent (ZMod m_k)ˣ = m_k - 1` (`IsCyclic.exponent_eq_card` + `totient_prime`). The per-`m` bound `liminf_density_S_sigma_ge_card_H_n_div_GH` gives `(|H_n(m_k)|/|H|)·n⁻¹ ≤ L_inf` for all `k`. The ratio `→ 1`: `n=1` trivial; `n ≥ 2` squeezed by `1 - S(k) ≤ r k ≤ 1` with `S(k) → 0` (`summand_tendsto`) and the lower bound from `H_n_ratio_ge` (feeding `p^(k·v_p(n)) ∣ exponent`). Hence the lower bounds tend to `n⁻¹`, so `n⁻¹ ≤ L_inf` by `le_of_tendsto`.
- **Hypotheses** · as above (no `hm4`/`hcop`: these are secured by the admissible-prime choice).
- **Uses from project** · [`liminf_density_S_sigma_ge_card_H_n_div_GH` (in-file), `H_n_ratio_ge` (in-file), `summand_tendsto` (in-file), `primeIdealZetaSum`/`UnramifiedIn`/`frobeniusClass` in the statement]
- **Used by** · `chebotarev_abelian` (1732).
- **Visibility** · public.
- **Lines** · 1378–1499.
- **Notes** · &gt;30 lines (~120). This is the live replacement for `H_n_over_H_tends_to_one`'s role.

### `theorem ratioSum_frobeniusFibres_tendsto_one`
- **Type** · `L/K` Galois, `[FiniteDimensional K L]`, abelian `Gal(L/K)`: `Tendsto (fun s ↦ ∑ σ, P_{S_σ}(s)/P_univ(s)) (𝓝[&gt;] 1) (𝓝 1)`.
- **What** · The `|G|` Frobenius fibres' density ratios sum to 1 (they partition the unramified primes).
- **How** · `ConjClasses.mk` is injective on the abelian group (`mul_right_cancel` after `mul_comm'`), so the fibres `S σ` are pairwise disjoint (`hpd`) and disjoint from the ramified set `R` (`hdisjR`); together they cover all nonzero primes (`hcover`). `R` is finite (`finite_ramifiedIn`) so `P_R/D → 0` (`hasDirichletDensity_of_finite`), giving `1 - P_R/D → 1`. Match via `congr'`: on `s &gt; 1` with `D s &gt; 0`, `∑_σ P_{S_σ} = P_{⋃ S_σ}` (`primeIdealZetaSum_biUnion_of_pairwiseDisjoint`) and `P_{⋃} + P_R = D` (`primeIdealZetaSum_union_of_disjoint` + `primeIdealZetaSum_eq_univ_of_forall_prime_mem`); `field_simp`/`linarith`.
- **Hypotheses** · as above.
- **Uses from project** · [`UnramifiedIn`/`frobeniusClass` (Frobenius.lean), `finite_ramifiedIn` (Frobenius.lean), `primeIdealZetaSum`, `hasDirichletDensity_of_finite`, `primeIdealZetaSum_univ_tendsto_atTop`, `primeIdealZetaSum_biUnion_of_pairwiseDisjoint`, `primeIdealZetaSum_union_of_disjoint`, `primeIdealZetaSum_eq_univ_of_forall_prime_mem` (Density.lean)]
- **Used by** · `chebotarev_abelian` (1731).
- **Visibility** · public.
- **Lines** · 1506–1565.
- **Notes** · &gt;30 lines.

---

**`section LiminfSumGlue`** (lines 1567–1629). Generic real-analysis helpers in a conditionally-complete linearly-ordered topological additive group; `variable {ι α} [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [DenselyOrdered α] [AddLeftMono α] {l : Filter ι} [l.NeBot]`.

### `private lemma sum_isBoundedUnder_ge`
- **Type** · `g : κ → ι → α`, `t : Finset κ`, each `g j` (j ∈ t) bounded below under `l`: `l.IsBoundedUnder (·≥·) (fun x ↦ ∑ j ∈ t, g j x)`.
- **What** · A finite sum of below-bounded functions is below-bounded.
- **How** · `Finset.induction`: empty → `isBoundedUnder_const`; insert → `isBoundedUnder_ge_add`.
- **Hypotheses** · per-summand below-boundedness; `omit [DenselyOrdered α] [l.NeBot]`.
- **Uses from project** · []
- **Used by** · `sum_liminf_le_liminf_sum` (1614), `tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one` (1662, 1672).
- **Visibility** · private.
- **Lines** · 1578–1587.
- **Notes** · —

### `private lemma sum_isBoundedUnder_le`
- **Type** · dual of the above: each `g j` above-bounded ⇒ the sum is above-bounded.
- **What** · A finite sum of above-bounded functions is above-bounded.
- **How** · `Finset.induction`; empty → `isBoundedUnder_const`; insert → `isBoundedUnder_le_add`.
- **Hypotheses** · per-summand above-boundedness; `omit [DenselyOrdered α] [l.NeBot]`.
- **Uses from project** · []
- **Used by** · `sum_liminf_le_liminf_sum` (1616), `tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one` (1674).
- **Visibility** · private.
- **Lines** · 1591–1600.
- **Notes** · —

### `private lemma sum_liminf_le_liminf_sum`
- **Type** · `g : κ → ι → α`, `t : Finset κ`, each `g j` (j ∈ t) bounded below and above: `∑ j ∈ t, liminf (g j) l ≤ liminf (fun x ↦ ∑ j ∈ t, g j x) l`.
- **What** · Superadditivity of `liminf` over a `Finset.sum`.
- **How** · `Finset.induction`; the inductive step uses `le_liminf_add` (the two-term superadditivity, needing the below/above bounds on the head and the tail-sum bounds supplied by `sum_isBoundedUnder_ge`/`_le` + `isCoboundedUnder_ge`), assembled in a `calc`.
- **Hypotheses** · per-summand below- and above-boundedness.
- **Uses from project** · [`sum_isBoundedUnder_ge`, `sum_isBoundedUnder_le` (in-file)]
- **Used by** · `tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one` (1678).
- **Visibility** · private.
- **Lines** · 1604–1627.
- **Notes** · —

---

### `theorem tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one`
- **Type** · `[Fintype ι]`, `g : ι → ℝ → ℝ`, with each `liminf (g i) ≥ (card ι)⁻¹`, each `g i` bounded below, and `∑ i, g i → 1` (all at `𝓝[&gt;] 1`), `i₀`: `Tendsto (g i₀) (𝓝[&gt;] 1) (𝓝 (card ι)⁻¹)`.
- **What** · Pigeonhole glue: a finite family each with `liminf ≥ 1/N` whose sum `→ 1` must each tend to `1/N`.
- **How** · `N = card ι`, `F = ∑ g i`; `limsup F = 1` (`hsum.limsup_eq`). Each `g i` is above-bounded: `g i = F - ∑_{j≠i} g j` with `F` bounded above and the rest bounded below (`sum_isBoundedUnder_ge`). For `i₀`: the rest-sum `t = univ.erase i₀` has `liminf ≥ (N-1)/N` (`sum_liminf_le_liminf_sum` + the per-`g` lower bounds). `le_limsup_add` gives `limsup (g i₀) + liminf rest ≤ limsup F = 1`, so `limsup (g i₀) ≤ 1 - (N-1)/N = N⁻¹`. Combined with `liminf (g i₀) ≥ N⁻¹` (hypothesis), `tendsto_of_le_liminf_of_limsup_le` concludes.
- **Hypotheses** · per-`i` `liminf` lower bound, per-`i` below-boundedness (`hbelow` — genuinely needed, per docstring), sum-limit.
- **Uses from project** · [`sum_isBoundedUnder_ge`, `sum_isBoundedUnder_le`, `sum_liminf_le_liminf_sum` (all in-file)]
- **Used by** · `chebotarev_abelian` (1725).
- **Visibility** · public.
- **Lines** · 1642–1705.
- **Notes** · &gt;30 lines.

### `theorem chebotarev_abelian`
- **Type** · (uses the file `variable` `K L`) `[FiniteDimensional K L]`, abelian `Gal(L/K)`, `σ`: `HasDirichletDensity {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧ frobeniusClass K L 𝔭 = mk σ} (card Gal(L/K))⁻¹`.
- **What** · Chebotarev's theorem, abelian case: density `1/|Gal(L/K)|`.
- **How** · Unfold `HasDirichletDensity`; apply `tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one` to the family `τ ↦ (P_{S_τ}/P_univ)` with: the per-`τ` lower bound `liminf_ratio_ge_inv_card_G`, below-boundedness from nonnegativity of `primeIdealZetaSum` (`primeIdealZetaSum_def` + `tsum_nonneg` + `Real.rpow_nonneg`, so each ratio `≥ 0`), and the sum-to-1 `ratioSum_frobeniusFibres_tendsto_one`; instantiate at `i₀ = σ`.
- **Hypotheses** · `[FiniteDimensional K L]`, abelian `Gal(L/K)`.
- **Uses from project** · [`tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one`, `liminf_ratio_ge_inv_card_G`, `ratioSum_frobeniusFibres_tendsto_one` (all in-file); `HasDirichletDensity`, `primeIdealZetaSum`, `primeIdealZetaSum_def` (Density.lean); `UnramifiedIn`, `frobeniusClass` (Frobenius.lean)]
- **Used by** · in-file: `chebotarev_abelian_lowerDensity_per_m` (1749). **Outside file:** `Main.lean` (real uses at lines 115, 138, inside `chebotarev_density`). FixedFieldDensity.lean mentions are docstring-only.
- **Visibility** · public; the project's main exported result of this file.
- **Lines** · 1718–1739.
- **Notes** · —

### `theorem chebotarev_abelian_lowerDensity_per_m`
- **Type** · `[FiniteDimensional K L]`, abelian `Gal(L/K)`, `σ`: `HasLowerDirichletDensity {…S_σ…} (card Gal(L/K))⁻¹`.
- **What** · The lower-density bound `δ_inf ≥ 1/|G|`, extracted from the full density.
- **How** · `(chebotarev_abelian K L σ).hasLower`.
- **Hypotheses** · as above.
- **Uses from project** · [`chebotarev_abelian` (in-file), `HasLowerDirichletDensity` + `HasDirichletDensity.hasLower` (Density.lean), `UnramifiedIn`/`frobeniusClass` (Frobenius.lean)]
- **Used by** · unused in file; not referenced elsewhere in the project.
- **Visibility** · public.
- **Lines** · 1743–1749.
- **Notes** · —

---

## File Summary

**Totals.** 1751 lines. 43 declarations: 5 public top-level results (`chebotarev_abelian`, `chebotarev_abelian_lowerDensity_per_m`, `liminf_density_S_sigma_ge_card_H_n_div_GH`, `liminf_ratio_ge_inv_card_G`, `ratioSum_frobeniusFibres_tendsto_one`) plus 3 more public theorems (`cyclic_subgroup_meets_G_times_one_trivially`, `H_n_over_H_tends_to_one`, `tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one`) = 8 public; 35 `private`. One `section LiminfSumGlue` (3 lemmas) over a general ordered group. **Sorry-free; no `axiom`; no `set_option`** (the single "sorry" string in the file is a docstring word at line 150).

**Two macro-blocks of machinery:** (1) AB1 compositum-crossing (C1–C5 + master leaf), lines ~86–908; (2) the `H_n`-ratio number theory + analytic glue, lines ~994–1705.

**Key project API used by ≥3 declarations:**
- `cyclotomicField_finrank_eq` (in-file, the deep leaf) — used by 3 (`compositum_charProd_bijective`, `autToPow_L_bijective`, `exists_crossing_family_tagged`).
- `torsion_card_le`, `dvd_capped`, `M_dvd_E`, `E_eq_M_mul`, `bad_le_torsion` (in-file) — each used by 2; together they are the shared core of `perprime_bound` and `perprime_bound_exp`.
- `summand_tendsto`, `ratio_bound`, `card_le_sum_card`, `exists_prime_pow_not_dvd` (in-file) — each used by 2 of {`H_n_ratio_ge`, `H_n_over_H_tends_to_one`} (and `summand_tendsto` also in `liminf_ratio_ge_inv_card_G`).
- `sum_isBoundedUnder_ge` (in-file) — used by 3 (`sum_liminf_le_liminf_sum`, `tendsto_inv_card_…` twice).
- `frobeniusClass` (Frobenius.lean) — referenced across the C4 / fibre / partition theorems (≥3).
- `primeIdealZetaSum` (Density.lean) — pervasive in the density theorems (≥4).
- `UnramifiedIn` (Frobenius.lean) — pervasive (≥4).

**Unused declarations (dead in this file):**
- `cyclic_subgroup_meets_G_times_one_trivially` — public; no real call site (its argument is inlined as `hgate` in `exists_crossing_family_tagged`). All 4 mentions are docstrings.
- `gal_compositum_prod_iso` (C1) — private; no real call site (`exists_crossing_family_tagged` uses `compositum_charProd_bijective`/`autToPow_L_bijective` directly). Mentions only in docstrings.
- `H_n_over_H_tends_to_one` — public; superseded by the admissible-prime route (`H_n_ratio_ge` in `liminf_ratio_ge_inv_card_G`); not used in code anywhere.
- `chebotarev_abelian_lowerDensity_per_m` — public; no in-file or project consumer.

**`sorry` list:** none. **`set_option` list:** none. **`&gt;30`-line declarations:** `prime_dvd_natAbs_discr_cyclotomic_dvd`, `cyclotomicField_finrank_eq`, `compositum_charProd_bijective`, `compositum_isCyclotomic_over_fixedField`, `frobeniusClass_proj`, `isGalois_compositum_base`, `unramifiedIn_tower_descend`, `exists_crossing_family_tagged`, `liminf_density_S_sigma_ge_card_H_n_div_GH`, `pk_dvd_carmichael`, `perprime_bound`, `perprime_bound_exp`, `H_n_ratio_ge`, `H_n_over_H_tends_to_one`, `liminf_ratio_ge_inv_card_G`, `ratioSum_frobeniusFibres_tendsto_one`, `tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one` (17 total).

**FLAG — `map_eq_of_isConj_comm` (lines 687–692):** known replica of a deleted CNR lemma (conjugacy-invariance of a hom into a commutative group). **Current consumers: exactly one** — `exists_crossing_family_tagged` at line 836 (reads the `H`-component tag off any conjugate representative of the `M`-Frobenius class). It is **not dead**; removing it would break the master crossing leaf. If mathlib has an equivalent (`MonoidHom` conjugacy-invariance for abelian targets), it is a candidate to dedupe against, but the in-file dependency is live.</result>
<usage><subagent_tokens>89794</subagent_tokens><tool_uses>11</tool_uses><duration_ms>316485</duration_ms></usage>
</task-notification>