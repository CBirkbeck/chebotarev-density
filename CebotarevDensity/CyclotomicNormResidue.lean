module

public import CebotarevDensity.Frobenius
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# The cyclotomic Frobenius as a norm residue, and Frobenii generate

Two arithmetic inputs of the Frobenius-fibre equidistribution (Gap B / L2), placed *below*
`ZetaProduct.lean` in the import order (the lemma `cyclotomic_frobenius_acts_as_norm_power`
currently lives in `Cyclotomic.lean`, which imports `ZetaProduct.lean` — the relevant content
is (re)stated here so that `ZetaProduct.lean` can consume it without an import cycle).

* `autToPow_frobeniusClass_out`: for `L = K(μ_m)` and a prime `𝔭` of `K` unramified in `L`
  with `N𝔭` coprime to `m`, the image of the Frobenius under the (faithful) cyclotomic
  character `Gal(L/K) →* (ℤ/m)ˣ` (`IsPrimitiveRoot.autToPow`) is the norm residue
  `N𝔭 mod m`. This is the multiplicative-dictionary form of the element-level fact
  `Frob_𝔭(ζ) = ζ^{N𝔭}` (Sharifi Prop. 7.1.15-adjacent; the element-level statement is
  `cyclotomic_frobenius_acts_as_norm_power`).

* `subgroup_eq_top_of_forall_frobenius_mem`: **Frobenii generate the Galois group** — a
  subgroup of `Gal(L/K)` containing the Frobenius representative of every unramified prime
  is the whole group. CFT-free proof via the project's zeta asymptotics: the fixed field `F`
  of such a subgroup has every unramified prime of `K` split completely; comparing
  `Σ_𝔭 N𝔭^{-s} ~ log (1/(s-1))` for `K` and for `F` (`primeIdealZetaSum_univ_tendsto_log`,
  both fields) against the `[F:K]`-fold multiplicity of split primes forces `[F:K] = 1`.
  (Used to realize every residue in the image of the cyclotomic character as a product of
  prime norm residues — the input `hS` of the κ-uniformity transfer.)
-/

@[expose] public section

noncomputable section

namespace Chebotarev

open NumberField

/-- **The cyclotomic Frobenius is the norm residue** (multiplicative form). For `L = K(μ_m)`,
a primitive `m`-th root `ζ` of unity in `L`, and a prime `𝔭` of `K` unramified in `L` with
`N𝔭` coprime to `m`, the cyclotomic character `IsPrimitiveRoot.autToPow` sends the Frobenius
representative `(frobeniusClass K L 𝔭).out` to the unit `N𝔭 mod m`. Follows from the
element-level action `Frob_𝔭 ζ = ζ^{N𝔭}` (`cyclotomic_frobenius_acts_as_norm_power`, to be
relocated here from `Cyclotomic.lean`), which pins the `autToPow` value by definition. -/
theorem autToPow_frobeniusClass_out
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] [FiniteDimensional K L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ m) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (hunr : UnramifiedIn K L 𝔭) (hcop : (Ideal.absNorm 𝔭).Coprime m) :
    hζ.autToPow K ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) =
      ZMod.unitOfCoprime (Ideal.absNorm 𝔭) hcop := by
  sorry

/-- **Frobenii generate the Galois group** (CFT-free, via the zeta asymptotics). A subgroup of
`Gal(L/K)` that contains the Frobenius representative of every nonzero prime of `K`
unramified in `L` is all of `Gal(L/K)`. Proof plan: let `F` be the fixed field of `H`; for
every unramified `𝔭` the restriction of `Frob_𝔭` to `F` is trivial, so `𝔭` splits completely
in `F/K`, contributing `[F:K]` primes of `F` with the same norm; hence
`Σ_{𝔮 of F} N𝔮^{-s} ⪆ [F:K] · Σ_{𝔭 of K unramified} N𝔭^{-s}`, and both universal prime sums
are `~ log (1/(s-1))` (`primeIdealZetaSum_univ_tendsto_log` for `F` and `K`, with the
finitely many ramified primes negligible by `finite_ramifiedIn`), forcing `[F:K] ≤ 1`,
i.e. `H = ⊤`. -/
theorem subgroup_eq_top_of_forall_frobenius_mem
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (H : Subgroup Gal(L/K))
    (hH : ∀ 𝔭 : Ideal (𝓞 K), ∀ _ : 𝔭.IsPrime, 𝔭 ≠ ⊥ → UnramifiedIn K L 𝔭 →
      ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) ∈ H) :
    H = ⊤ := by
  sorry

end Chebotarev
