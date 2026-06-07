# Inventory: `CebotarevDensity/Frobenius.lean`

File header (lines 1-57): `module` with `public import`s of mathlib (Conj groups, GaloisField, Galois.Basic, RamificationInertia.Galois/Unramified, DedekindDomain.Different/Factorization, RingTheory.Frobenius, Ideal.Pointwise, RamificationInertia.Inertia) plus `CebotarevDensity.Density`. Wrapped in `@[expose] public section` and `noncomputable section`. Opens `NumberField`, `open scoped Pointwise`. Namespace `Chebotarev`. File-level `variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]` (line 59).

---

### `def UnramifiedIn`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (𝔭 : Ideal (𝓞 K)) : Prop`
- **What**: A prime `𝔭` of `𝓞 K` is unramified in `L`: it is nonzero, and every maximal prime `𝔓` of `𝓞 L` lying over `𝔭` is unramified over `𝓞 K`.
- **How**: Definitional conjunction `𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal), 𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt (𝓞 K) 𝔓`, using mathlib's `Algebra.IsUnramifiedAt`.
- **Hypotheses**: `L/K` Galois; `𝔭` a (possibly arbitrary) ideal of `𝓞 K`.
- **Uses from project**: []
- **Used by**: `UnramifiedIn.ne_bot`, `UnramifiedIn.ramificationIdx_eq_one`, `isConj_of_isArithFrobAt`, `exists_frobeniusClass`, `frobeniusClass`, `frobeniusClass_eq_mk_of_isArithFrobAt`, `card_primesAbove_mul_finrank_eq`, `finrank_residue_eq_orderOf`, `card_primesAbove_mul_orderOf_eq`, `finite_ramifiedIn`
- **Visibility** (public/exposed) · **Lines** 68-71 · **Notes** —

---

### `theorem ne_bot_of_ramificationIdx_eq_one`
- **Type**: `(K L : Type*) [Field K] [Field L] [Algebra K L] {𝔓 : Ideal (𝓞 L)} (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) : 𝔓 ≠ ⊥` (NumberField instances omitted via `omit`)
- **What**: A prime of `𝓞 L` whose ramification index over its image in `𝓞 K` is `1` is nonzero.
- **How**: Contrapositive — substitute `𝔓 = ⊥` (`rintro rfl`) and `simp` derives a contradiction from `Ideal.ramificationIdx_bot` (the zero ideal has ramification index `0 ≠ 1`).
- **Hypotheses**: `e(𝔓 ∣ 𝔭) = 1`.
- **Uses from project**: []
- **Used by**: `inertiaGroup_trivial_of_unramified`, `isConj_of_isArithFrobAt`, `exists_frobeniusClass`, `orderOf_eq_finrank_of_isArithFrobAt`, `card_primesAbove_mul_finrank_eq`, `finrank_residue_eq_orderOf`
- **Visibility** (public) · **Lines** 73-79 · **Notes** `omit [NumberField K] [NumberField L]`

---

### `theorem UnramifiedIn.ne_bot`
- **Type**: `(K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L] {𝔭 : Ideal (𝓞 K)} (hunr : UnramifiedIn K L 𝔭) : 𝔭 ≠ ⊥` (NumberField omitted)
- **What**: An unramified prime is nonzero — extracts the first clause of `UnramifiedIn`.
- **How**: Projection `hunr.1` onto the left conjunct of the `UnramifiedIn` definition.
- **Hypotheses**: `𝔭` unramified in `L`.
- **Uses from project**: `UnramifiedIn`
- **Used by**: `exists_frobeniusClass`, `card_primesAbove_mul_finrank_eq`, `card_primesAbove_mul_orderOf_eq`
- **Visibility** (public) · **Lines** 81-86 · **Notes** `omit [NumberField K] [NumberField L]`

---

### `theorem UnramifiedIn.ramificationIdx_eq_one`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] {𝔭 : Ideal (𝓞 K)} (hunr : UnramifiedIn K L 𝔭) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭) : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1`
- **What**: For a prime `𝔓` lying over an unramified prime `𝔭`, the ramification index `e(𝔓 ∣ 𝔭)` equals `1`.
- **How**: `𝔓 ≠ ⊥` from `Ideal.ne_bot_of_liesOver_of_ne_bot` (using `hunr.1`); then a prime `𝔓` is maximal, so `Algebra.isUnramifiedAt_iff_of_isDedekindDomain` converts the `IsUnramifiedAt` fact `hunr.2 𝔓 …` into `e = 1`.
- **Hypotheses**: `𝔭` unramified; `𝔓` prime lying over `𝔭`.
- **Uses from project**: `UnramifiedIn` (via `hunr.1`, `hunr.2`)
- **Used by**: `isConj_of_isArithFrobAt`, `exists_frobeniusClass`, `card_primesAbove_mul_finrank_eq`, `finrank_residue_eq_orderOf`
- **Visibility** (public) · **Lines** 88-97 · **Notes** —

---

### `theorem inertiaGroup_trivial_of_unramified`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) : Ideal.inertia Gal(L/K) 𝔓 = ⊥`
- **What**: At an unramified prime `𝔓`, the inertia subgroup of `Gal(L/K)` is trivial.
- **How**: `Subgroup.eq_bot_iff_card` reduces to cardinality `1`; `Ideal.card_inertia_eq_ramificationIdxIn` rewrites `|I_𝔓|` to the ramification-index-in, which `Ideal.ramificationIdxIn_eq_ramificationIdx` identifies with `e(𝔓∣𝔭) = 1`. Needs finite residue field (`Ideal.finiteQuotientOfFreeOfNeBot`), maximality of `𝔓` and its under-ideal, and separability (`IsGalois.to_isSeparable`).
- **Hypotheses**: `𝔓` prime with `e(𝔓 ∣ 𝔭) = 1`.
- **Uses from project**: `ne_bot_of_ramificationIdx_eq_one`
- **Used by**: `orderOf_eq_finrank_of_isArithFrobAt`, `card_primesAbove_mul_finrank_eq`
- **Visibility** (public) · **Lines** 99-118 · **Notes** &gt;30-line/19-line proof block; multiple `haveI`/`letI` instance setup

---

### `private instance faithfulSMul_galois`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] : FaithfulSMul Gal(L/K) (𝓞 L)`
- **What**: `Gal(L/K)` acts faithfully on the ring of integers `𝓞 L`.
- **How**: Two automorphisms agreeing on `𝓞 L` agree on `L = Frac(𝓞 L)`: a bridge lemma `((g • x : 𝓞 L) : L) = g • (x : L)` (via `smul_distrib_smul` and `Algebra.smul_def`) transports the hypothesis to `L`, then `IsFractionRing.ringHom_ext` extends the equality of ring homs from `𝓞 L` to `L`, and `eq_of_smul_eq_smul` concludes.
- **Hypotheses**: `L/K` Galois (number-field setting).
- **Uses from project**: []
- **Used by**: unused in file (instance — consumed implicitly by typeclass resolution, e.g. `eq_arithFrobAt_of_isArithFrobAt`'s injectivity argument; no explicit named reference)
- **Visibility** **private** instance · **Lines** 124-134 · **Notes** &gt;10-line proof; uses `smul_distrib_smul`, `IsFractionRing.ringHom_ext`

---

### `theorem eq_arithFrobAt_of_isArithFrobAt`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] [Finite (𝓞 L ⧸ 𝔓)] [Algebra.IsUnramifiedAt (𝓞 K) 𝔓] (σ : Gal(L/K)) (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) : σ = arithFrobAt (𝓞 K) Gal(L/K) 𝔓`
- **What**: Any element that is an arithmetic Frobenius at an unramified prime `𝔓` equals the canonical `arithFrobAt 𝔓`.
- **How**: Apply faithfulness `MulSemiringAction.toAlgHom_injective (𝓞 K) (𝓞 L)` to reduce to equality of `AlgHom`s, then mathlib's `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt` (residue-degree uniqueness) with `𝔓.primeCompl_le_nonZeroDivisors`.
- **Hypotheses**: `𝔓` prime, finite residue field, unramified at `𝔓`; `σ` is an arithmetic Frobenius at `𝔓`.
- **Uses from project**: [] (relies on `faithfulSMul_galois` instance only implicitly)
- **Used by**: `isConj_of_isArithFrobAt`, `orderOf_eq_finrank_of_isArithFrobAt`
- **Visibility** (public) · **Lines** 136-146 · **Notes** —

---

### `theorem isConj_of_isArithFrobAt`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (σ σ' : Gal(L/K)) (𝔓 𝔓' : Ideal (𝓞 L)) [𝔓.IsPrime] [𝔓'.IsPrime] (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) (hσ' : IsArithFrobAt (𝓞 K) σ' 𝔓') (hP : 𝔓.LiesOver 𝔭) (hP' : 𝔓'.LiesOver 𝔭) : IsConj σ σ'`
- **What**: Two arithmetic Frobenius elements at primes `𝔓`, `𝔓'` both above an unramified prime `𝔭` are conjugate in `Gal(L/K)`.
- **How**: Each `σ`, `σ'` is rewritten as `arithFrobAt` at its prime (`eq_arithFrobAt_of_isArithFrobAt`); since both primes lie over the same `𝔭` (`hP.over.symm.trans hP'.over`), mathlib's `isConj_arithFrobAt` gives conjugacy. Sets up finite residue fields and `IsUnramifiedAt` instances from `hunr`.
- **Hypotheses**: `𝔭` unramified prime; `𝔓, 𝔓'` primes above `𝔭`; `σ, σ'` arithmetic Frobenii there.
- **Uses from project**: `UnramifiedIn` (via `hunr`), `ne_bot_of_ramificationIdx_eq_one`, `UnramifiedIn.ramificationIdx_eq_one`, `eq_arithFrobAt_of_isArithFrobAt`
- **Used by**: `exists_frobeniusClass`
- **Visibility** (public) · **Lines** 149-172 · **Notes** &gt;30-line/24-line proof; heavy instance setup

---

### `theorem exists_prime_liesOver`
- **Type**: `(K L : Type*) [Field K] [Field L] [Algebra K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hnz : 𝔭 ≠ ⊥) : ∃ 𝔓 : Ideal (𝓞 L), 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥` (NumberField omitted)
- **What**: A nonzero prime `𝔭` of `𝓞 K` has at least one prime `𝔓` of `𝓞 L` lying over it, and any such `𝔓` is nonzero.
- **How**: Going-up `Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain` for the integral extension `𝓞 K ⊆ 𝓞 L` produces `𝔓`; `LiesOver` is built from the comap equality; nonzero from `Ideal.ne_bot_of_liesOver_of_ne_bot`.
- **Hypotheses**: `𝔭` nonzero prime of `𝓞 K`.
- **Uses from project**: []
- **Used by**: `exists_frobeniusClass`, `card_primesAbove_mul_orderOf_eq`
- **Visibility** (public) · **Lines** 174-184 · **Notes** `omit [NumberField K] [NumberField L]`

---

### `theorem exists_frobeniusClass`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) : ∃ C : ConjClasses Gal(L/K), ∀ (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (_ : IsArithFrobAt (𝓞 K) σ 𝔓) (_ : 𝔓.LiesOver 𝔭), C = ConjClasses.mk σ`
- **What**: For an unramified prime `𝔭`, there is a single conjugacy class `C` that equals `[σ]` for every arithmetic Frobenius `σ` at any prime `𝔓` above `𝔭` — existence/well-definedness of the Frobenius class.
- **How**: Pick a witness prime `𝔓₀` above `𝔭` (`exists_prime_liesOver`), take `C := [arithFrobAt 𝔓₀]`; for any other Frobenius `σ` at `𝔓`, conjugacy follows from `isConj_of_isArithFrobAt` (comparing the canonical `arithFrobAt 𝔓₀` with `σ`) via `ConjClasses.mk_eq_mk_iff_isConj`.
- **Hypotheses**: `𝔭` unramified prime.
- **Uses from project**: `exists_prime_liesOver`, `UnramifiedIn.ne_bot`, `ne_bot_of_ramificationIdx_eq_one`, `UnramifiedIn.ramificationIdx_eq_one`, `isConj_of_isArithFrobAt`
- **Used by**: `frobeniusClass`, `frobeniusClass_eq_mk_of_isArithFrobAt`
- **Visibility** (public) · **Lines** 186-205 · **Notes** &gt;10-line proof

---

### `def frobeniusClass`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (𝔭 : Ideal (𝓞 K)) : ConjClasses Gal(L/K)`
- **What**: The Frobenius conjugacy class of a prime `𝔭`: for a nonzero unramified prime it is the class of any arithmetic Frobenius above `𝔭`; otherwise the trivial class `[1]` (junk value never used by the Chebotarev statement).
- **How**: `Classical`-decidable `if` on `𝔭.IsPrime ∧ UnramifiedIn K L 𝔭`; in the positive branch returns `(exists_frobeniusClass K L 𝔭 h.2).choose`, otherwise `ConjClasses.mk 1`. A real definition (no placeholder sorry).
- **Hypotheses**: `L/K` Galois; `𝔭` arbitrary ideal.
- **Uses from project**: `UnramifiedIn`, `exists_frobeniusClass`
- **Used by**: `frobeniusClass_eq_mk_of_isArithFrobAt`, `finrank_residue_eq_orderOf`, `card_primesAbove_mul_orderOf_eq`
- **Visibility** (public) · **Lines** 207-221 · **Notes** uses `open Classical in`; `Classical.choose`-based definition

---

### `theorem frobeniusClass_eq_mk_of_isArithFrobAt`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) (hP : 𝔓.LiesOver 𝔭) : frobeniusClass K L 𝔭 = ConjClasses.mk σ`
- **What**: `frobeniusClass K L 𝔭` equals the conjugacy class `[σ]` of any arithmetic Frobenius `σ` at any prime `𝔓` above `𝔭`.
- **How**: Unfold `frobeniusClass` and take the positive `dif_pos ⟨IsPrime, hunr⟩` branch, then apply `(exists_frobeniusClass …).choose_spec` to `σ, 𝔓, hσ, hP`.
- **Hypotheses**: `𝔭` unramified prime; `σ` arithmetic Frobenius at `𝔓 ∣ 𝔭`.
- **Uses from project**: `frobeniusClass`, `UnramifiedIn`, `exists_frobeniusClass`
- **Used by**: `finrank_residue_eq_orderOf`
- **Visibility** (public) · **Lines** 223-232 · **Notes** —

---

### `theorem orderOf_eq_finrank_of_isArithFrobAt`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (h : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) : orderOf σ = Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓)`
- **What**: The order of a Frobenius element `σ` at an unramified prime `𝔓` equals the residue degree `f = [κ(𝔓) : κ(𝔭)]` (flagged in docstring as an "API gap" filled here).
- **How**: Rewrite `σ = arithFrobAt 𝔓` (`eq_arithFrobAt_of_isArithFrobAt`), lift to the stabilizer element `g₀`; `Ideal.Quotient.stabilizerHom` is injective (kernel = inertia = `⊥` via `Ideal.Quotient.ker_stabilizerHom` + `inertiaGroup_trivial_of_unramified`); identifies the image with the finite-field Frobenius `FiniteField.frobeniusAlgEquivOfAlgebraic` (both raise classes to the `N𝔭`-th power: `IsArithFrobAt.mk_apply` and `FiniteField.coe_frobeniusAlgEquivOfAlgebraic`); concludes by `FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic` through an `orderOf_injective`/`Subgroup.orderOf_mk` calc.
- **Hypotheses**: `L/K` finite Galois; `𝔓` prime with `e = 1`; `σ` arithmetic Frobenius at `𝔓`.
- **Uses from project**: `ne_bot_of_ramificationIdx_eq_one`, `eq_arithFrobAt_of_isArithFrobAt`, `inertiaGroup_trivial_of_unramified`
- **Used by**: `finrank_residue_eq_orderOf`
- **Visibility** (public) · **Lines** 234-290 · **Notes** `open scoped Pointwise in`; redeclares `(K L : Type*)` explicitly; long proof (~40 lines) with `set`/`calc`; docstring marks it an API-gap leaf

---

### `theorem card_primesAbove_mul_finrank_eq`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (𝔓₀ : Ideal (𝓞 L)) [𝔓₀.IsPrime] (hlo : 𝔓₀.LiesOver 𝔭) : Nat.card {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} * Module.finrank (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) (𝓞 L ⧸ 𝔓₀) = Nat.card Gal(L/K)`
- **What**: (Number of primes above `𝔭`) × (residue degree of `𝔓₀`) = `|Gal(L/K)|` — the orbit–stabilizer count specialized to an unramified prime.
- **How**: mathlib's `Ideal.ncard_primesOver_mul_card_inertia_mul_finrank` with inertia trivial (`inertiaGroup_trivial_of_unramified`, `Subgroup.card_bot`, `mul_one`); then identifies the subtype `{𝔓 // IsPrime ∧ LiesOver 𝔭 ∧ ≠ ⊥}` with `(𝔓₀.under).primesOver (𝓞 L)` via a `Set`-extensionality (`hset`) and `Nat.card_coe_set_eq`. Uses `e = 1` (`UnramifiedIn.ramificationIdx_eq_one`) and `hlo.over`.
- **Hypotheses**: `L/K` finite Galois; `𝔭` unramified; `𝔓₀` prime above `𝔭`.
- **Uses from project**: `UnramifiedIn.ne_bot`, `UnramifiedIn.ramificationIdx_eq_one`, `ne_bot_of_ramificationIdx_eq_one`, `inertiaGroup_trivial_of_unramified`, `UnramifiedIn` (via `hunr`)
- **Used by**: `card_primesAbove_mul_orderOf_eq`
- **Visibility** (public) · **Lines** 292-328 · **Notes** redeclares `(K L : Type*)`; long proof (~36 lines)

---

### `theorem finrank_residue_eq_orderOf`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (hσ : ConjClasses.mk σ = C) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hCfrob : frobeniusClass K L 𝔭 = C) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hlo : 𝔓.LiesOver 𝔭) : Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) = orderOf σ`
- **What**: When the Frobenius class of `𝔭` is `C = [σ]`, the residue degree at any prime `𝔓` above `𝔭` equals `orderOf σ`.
- **How**: `arithFrobAt 𝔓` is conjugate to `σ` because `frobeniusClass K L 𝔭 = [arithFrobAt 𝔓]` (`frobeniusClass_eq_mk_of_isArithFrobAt`) and `= C = [σ]`; conjugates have equal order (`IsConj.orderOf_eq`), and `orderOf (arithFrobAt 𝔓) = finrank` by `orderOf_eq_finrank_of_isArithFrobAt`.
- **Hypotheses**: `𝔭` unramified, `frobeniusClass 𝔭 = C`, `[σ] = C`; `𝔓` prime above `𝔭`.
- **Uses from project**: `UnramifiedIn.ramificationIdx_eq_one`, `ne_bot_of_ramificationIdx_eq_one`, `frobeniusClass_eq_mk_of_isArithFrobAt`, `orderOf_eq_finrank_of_isArithFrobAt`, `frobeniusClass` (via `hCfrob`), `UnramifiedIn` (via `hunr`)
- **Used by**: `card_primesAbove_mul_orderOf_eq`
- **Visibility** (public) · **Lines** 330-348 · **Notes** redeclares `(K L : Type*)`

---

### `theorem card_primesAbove_mul_orderOf_eq`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (_hσ : ConjClasses.mk σ = C) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (_hCfrob : frobeniusClass K L 𝔭 = C) : Nat.card {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} * orderOf σ = Nat.card Gal(L/K)`
- **What**: (Number of primes above `𝔭`) × `orderOf σ` = `|Gal(L/K)|`, where `σ` generates the Frobenius class of the unramified prime `𝔭` (Sharifi 7.2.2 Step 1).
- **How**: Pick a witness prime `𝔓₀` above `𝔭` (`exists_prime_liesOver`), replace `orderOf σ` by the residue degree (`finrank_residue_eq_orderOf`), then apply the finrank-form count `card_primesAbove_mul_finrank_eq`.
- **Hypotheses**: `L/K` finite Galois; `𝔭` unramified; `[σ] = C = frobeniusClass 𝔭`.
- **Uses from project**: `exists_prime_liesOver`, `UnramifiedIn.ne_bot`, `finrank_residue_eq_orderOf`, `card_primesAbove_mul_finrank_eq`, `frobeniusClass` (via `_hCfrob`), `UnramifiedIn` (via `hunr`)
- **Used by**: unused in file
- **Visibility** (public) · **Lines** 350-364 · **Notes** redeclares `(K L : Type*)`

---

### `theorem finite_ramifiedIn`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] : {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭}.Finite`
- **What**: Only finitely many nonzero primes of `𝓞 K` ramify in `L`.
- **How**: A ramified `𝔭` has a prime `𝔓` above it that is not unramified, hence divides the relative different `differentIdeal (𝓞 K) (𝓞 L)` (`not_dvd_differentIdeal_iff`); the different is nonzero (`differentIdeal_ne_bot`), so its factors are finite (`Ideal.finite_factors`), and the ramified `𝔭` are images under `Ideal.under (𝓞 K)` — so the set embeds in a finite image via `Set.Finite.subset`. Sets up the `FractionRing` scalar tower and separability of the fraction fields.
- **Hypotheses**: `L/K` Galois.
- **Uses from project**: `UnramifiedIn` (unfolds the definition via `simp only [UnramifiedIn, …]`)
- **Used by**: unused in file
- **Visibility** (public) · **Lines** 366-392 · **Notes** &gt;30-line/27-line proof; builds `FractionRing.liftAlgebra` tower; uses `differentIdeal_ne_bot`, `Ideal.finite_factors`, `not_dvd_differentIdeal_iff`

---

## File Summary

- **Totals**: 16 declarations — 2 `def` (`UnramifiedIn`, `frobeniusClass`), 1 `private instance` (`faithfulSMul_galois`), 13 `theorem`. No `structure`/`class`/`abbrev`. No `axiom`.
- **`sorry`**: none. **`set_option`**: none. **`omit` modifiers**: 4 (lines 73, 81, 174 region — on `ne_bot_of_ramificationIdx_eq_one`, `UnramifiedIn.ne_bot`, `exists_prime_liesOver`; each `omit [NumberField K] [NumberField L]`).
- **`&gt;30`-line proofs** (notable long ones): `inertiaGroup_trivial_of_unramified` (≈19), `isConj_of_isArithFrobAt` (≈24), `orderOf_eq_finrank_of_isArithFrobAt` (≈40, the marked "API gap" leaf), `card_primesAbove_mul_finrank_eq` (≈36), `finite_ramifiedIn` (≈27). (`isConj`, `orderOf_eq_finrank`, `card_primesAbove_mul_finrank`, `finite_ramifiedIn` clearly exceed 20–30 source lines.)

- **Key project API used by 3+ consumers**:
  - `UnramifiedIn` — used by 10 declarations (the central definition).
  - `ne_bot_of_ramificationIdx_eq_one` — used by 6 (`inertiaGroup_trivial_of_unramified`, `isConj_of_isArithFrobAt`, `exists_frobeniusClass`, `orderOf_eq_finrank_of_isArithFrobAt`, `card_primesAbove_mul_finrank_eq`, `finrank_residue_eq_orderOf`).
  - `UnramifiedIn.ramificationIdx_eq_one` — used by 4 (`isConj_of_isArithFrobAt`, `exists_frobeniusClass`, `card_primesAbove_mul_finrank_eq`, `finrank_residue_eq_orderOf`).
  - `UnramifiedIn.ne_bot` — used by 3 (`exists_frobeniusClass`, `card_primesAbove_mul_finrank_eq`, `card_primesAbove_mul_orderOf_eq`).
  - `frobeniusClass` — referenced by 3 (`frobeniusClass_eq_mk_of_isArithFrobAt`, `finrank_residue_eq_orderOf`, `card_primesAbove_mul_orderOf_eq`).
  - `inertiaGroup_trivial_of_unramified` — used by 2; `eq_arithFrobAt_of_isArithFrobAt`, `isConj_of_isArithFrobAt`, `exists_prime_liesOver`, `exists_frobeniusClass`, `orderOf_eq_finrank_of_isArithFrobAt`, `card_primesAbove_mul_finrank_eq`, `frobeniusClass_eq_mk_of_isArithFrobAt`, `finrank_residue_eq_orderOf` each used by 1–2.

- **Unused in file (terminal / exported results)**: `faithfulSMul_galois` (private instance, consumed only by typeclass resolution), `card_primesAbove_mul_orderOf_eq` (top-level count exported for `Main.lean`/`Abelian.lean`), `finite_ramifiedIn` (exported finiteness lemma). These are the file's outward-facing leaves; everything else feeds them.

- **Notes / observations**: The file is `sorry`-free and `axiom`-free (consistent with project hard requirements). `frobeniusClass` uses `Classical.choose` of the real existence theorem `exists_frobeniusClass` rather than a placeholder `def := sorry`, matching the "no scaffolding" convention. The five later theorems (`orderOf_eq_finrank_of_isArithFrobAt` onward) re-declare `(K L : Type*) …` explicitly in their signatures rather than relying on the file `variable` line. Inequalities are not present (no `≥`/`≤` issues). The central dependency spine is `UnramifiedIn` → `ramificationIdx_eq_one`/`ne_bot` → `inertiaGroup_trivial`/`eq_arithFrobAt` → `isConj`/`orderOf_eq_finrank` → `exists_frobeniusClass`/`frobeniusClass` → the two `card_primesAbove_*` counts.</result>
<usage><subagent_tokens>32754</subagent_tokens><tool_uses>1</tool_uses><duration_ms>115099</duration_ms></usage>
</task-notification>