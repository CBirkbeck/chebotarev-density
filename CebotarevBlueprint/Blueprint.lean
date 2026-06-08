import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import CebotarevBlueprint.Chapters.Density
import CebotarevBlueprint.Chapters.Frobenius
import CebotarevBlueprint.Chapters.ZetaProduct
import CebotarevBlueprint.Chapters.Engine
import CebotarevBlueprint.Chapters.Cyclotomic
import CebotarevBlueprint.Chapters.Abelian
import CebotarevBlueprint.Chapters.Main
import CebotarevBlueprint.Refs
import CebotarevDensity

open Verso.Genre
open Verso.Genre.Manual
open Informal

tex_prelude r#"\def\Z{\mathbb{Z}}\def\Q{\mathbb{Q}}\def\R{\mathbb{R}}\def\C{\mathbb{C}}\def\N{\mathbb{N}}\def\F{\mathbb{F}}\def\OK{\mathcal{O}_K}\def\Ocirc{\mathcal{O}}\def\Gal#1{\mathrm{Gal}(#1)}\def\Norm#1{\mathrm{N}(#1)}\def\fp{\mathfrak{p}}\def\fP{\mathfrak{P}}\def\Frob{\mathrm{Frob}}\def\Re{\operatorname{Re}}\def\re{\operatorname{Re}}\def\set#1{\left\{#1\right\}}\def\setof#1#2{\left\{#1\;\middle|\;#2\right\}}\def\abs#1{\left\lvert#1\right\rvert}\def\norm#1{\left\lVert#1\right\rVert}\def\ang#1{\left\langle#1\right\rangle}"#

#doc (Manual) "Chebotarev density theorem" =>

This blueprint tracks a Lean 4 / Mathlib formalisation of the *Chebotarev density
theorem* in conjugacy-class form. For a finite Galois extension $`L/K` of number
fields with Galois group $`G=\Gal{L/K}` and a conjugacy class $`C\subseteq G`, the
Dirichlet density of the set of primes $`\fp` of $`\OK` whose Frobenius conjugacy
class is $`C` equals $`\abs{C}/\abs{G}`.

*The formalisation is complete.* Every declaration is fully proved — zero
`sorry`s anywhere in the project — and the four headline theorems
(`chebotarev_density`, `chebotarev_cyclotomic`, `chebotarev_abelian`,
`density_split_completely`) rest on exactly the three standard Lean/Mathlib
axioms `propext`, `Classical.choice`, and `Quot.sound`, with no project-specific
axioms. This has been certified by `leanprover/comparator` (statement-identity
against the intended statements, axiom-budget audit, and kernel replay of every
proof term).

The proof follows the modern exposition of {Informal.citet "stevenhagen-lenstra"}[]
(*Chebotarëv and his density theorem*, Appendix) and
{Informal.citet sharifi (kind := section) (index := "7.2")}[]
(*Algebraic Number Theory*). Both references are included under `docs/`.

*Outline.* The proof proceeds in three reductions, and needs no class field
theory — it is essentially Chebotarev's original strategy as expounded by
{Informal.citet "stevenhagen-lenstra"}[]:

1. *Foundations.* We define the Dirichlet density of a set of prime ideals via the
   Dirichlet series $`\sum_{\fp\in S} \Norm{\fp}^{-s}` normalised against the same
   sum over all primes, and we set up the Frobenius element at an unramified prime
   $`\fP` of $`\Ocirc_L` together with its conjugacy class as $`\fP` varies above a
   $`K`-prime $`\fp`.
2. *Cyclotomic case.* The analytic engine is the factorisation
   $`\zeta_L(s) = \prod_{\chi\in\widehat{G}} L(\chi, s)` of the Dedekind zeta
   function of $`L` into Hecke (Artin) $`L`-functions indexed by characters of
   $`G`, valid when $`G` is abelian, together with the non-vanishing
   $`L(\chi, 1)\ne 0` for nontrivial $`\chi`. Applied to a cyclotomic extension
   $`L=K(\zeta_m)`, this yields the cyclotomic case of Chebotarev directly from
   Dirichlet's argument.
3. *Abelian case.* For a general abelian $`L/K`, we use Chebotarev's crossing
   trick: pick $`m` coprime to the discriminant of $`L` so that
   $`\Gal{L(\zeta_m)/K}\cong G\times H` with $`H=\Gal{K(\zeta_m)/K}`; for
   $`\tau\in H` with $`\abs{G}\mid\mathrm{ord}(\tau)`, the cyclic subgroup
   $`\ang{(\sigma,\tau)}\subseteq G\times H` has trivial intersection with
   $`G\times\{1\}`, so the fixed-field extension is cyclotomic; the cyclotomic case
   applies; summing over admissible $`\tau` and letting $`m\equiv 1\pmod{n^k}` for
   $`k\to\infty` recovers the abelian density.
4. *General case.* The conjugacy-class form is reduced to the cyclic-extension case
   via the intermediate field $`E=L^{\ang\sigma}`: the counting "exactly
   $`\abs{G}/(f\abs{C})` primes of $`L` above $`\fp` have Frobenius $`\sigma`"
   yields the density relation
   $`\delta_K(S) = (f\abs{C}/\abs{G})\,\delta_E(T_\sigma)`, which combines with the
   abelian case for $`L/E`.

{include 0 CebotarevBlueprint.Chapters.Density}
{include 0 CebotarevBlueprint.Chapters.Frobenius}
{include 0 CebotarevBlueprint.Chapters.ZetaProduct}
{include 0 CebotarevBlueprint.Chapters.Engine}
{include 0 CebotarevBlueprint.Chapters.Cyclotomic}
{include 0 CebotarevBlueprint.Chapters.Abelian}
{include 0 CebotarevBlueprint.Chapters.Main}

{blueprint_graph}
{blueprint_summary}

# References

{blueprint_bibliography}
