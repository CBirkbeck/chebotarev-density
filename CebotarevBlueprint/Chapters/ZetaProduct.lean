import Verso
import VersoManual
import VersoBlueprint
import CebotarevDensity
import CebotarevBlueprint.Refs

open Verso.Genre
open Verso.Genre.Manual
open Informal

tex_prelude r#"\def\Z{\mathbb{Z}}\def\Q{\mathbb{Q}}\def\R{\mathbb{R}}\def\C{\mathbb{C}}\def\N{\mathbb{N}}\def\F{\mathbb{F}}\def\OK{\mathcal{O}_K}\def\Ocirc{\mathcal{O}}\def\Gal#1{\mathrm{Gal}(#1)}\def\Norm#1{\mathrm{N}(#1)}\def\fp{\mathfrak{p}}\def\fP{\mathfrak{P}}\def\Frob{\mathrm{Frob}}\def\Re{\operatorname{Re}}\def\re{\operatorname{Re}}\def\set#1{\left\{#1\right\}}\def\setof#1#2{\left\{#1\;\middle|\;#2\right\}}\def\abs#1{\left\lvert#1\right\rvert}\def\norm#1{\left\lVert#1\right\rVert}\def\ang#1{\left\langle#1\right\rangle}"#

#doc (Manual) "Zeta factorisation for abelian extensions" =>

For an abelian Galois extension $`L/K` of number fields with
$`G=\Gal{L/K}`, the Dedekind zeta function $`\zeta_L` factors as a
product of Hecke $`L`-functions indexed by characters of $`G`. This is
the analytic engine of the cyclotomic case of Chebotarev.

:::definition "galois-character" (lean := "Chebotarev.galoisCharacter")

A *character of $`G`* is a group homomorphism
$`\chi: G \to \C^\times`.

:::

:::lemma_ "artin-euler-product-abelian" (lean := "Chebotarev.exists_artinLSeries_eulerProduct_abelian")

For an abelian character $`\chi: G \to \C^\times`, there is a function
$`L(\chi, \cdot): \C \to \C` such that on $`\re(s) > 1`,
$$`
  L(\chi, s) \;=\; \prod_\fp \bigl(1-\chi(\Frob_\fp) \Norm{\fp}^{-s}\bigr)^{-1},
`
where the product runs over primes $`\fp` of $`\OK` unramified in $`L`,
with the convention $`\chi(\fp) = 0` on ramified primes.

{uses "galois-character"}[]
{uses "frobenius-class"}[]

:::

:::proof "artin-euler-product-abelian"

{Informal.citet sharifi (kind := proposition) (index := "7.1.18")}[] (p.~141). The Euler product converges
absolutely on $`\re(s) > 1` by comparison with $`\zeta_K`.

:::

:::lemma_ "dedekind-local-factor" (lean := "Chebotarev.dedekindZeta_local_factor_eq_product_artin_local")

For each unramified prime $`\fp` of $`\OK`, the local Euler factor of
$`\zeta_L` at $`\fp` factors as
$$`
  \prod_{\fP\mid\fp}\bigl(1-\Norm{\fP}^{-s}\bigr)^{-1}
  \;=\; \prod_\chi \bigl(1-\chi(\Frob_\fp)\Norm{\fp}^{-s}\bigr)^{-1}.
`

{uses "artin-euler-product-abelian"}[]

:::

:::proof "dedekind-local-factor"

Standard cyclic-group character theory applied to the residue Galois
group: the characters of $`\Gal{(\Ocirc_L/\fP)/(\OK/\fp)}` separate
elements, and the indicated product over $`\chi` recovers the local
factor ({Informal.citet sharifi (kind := theorem) (index := "7.1.16")}[] step at $`\fp`).

:::

:::lemma_ "character-sum-geom-numbers" (lean := "Chebotarev.character_sum_geometry_of_numbers_bound")

For a nontrivial character $`\chi: G \to \C^\times`, there is a
constant $`C` such that
$$`
  \biggl\lVert\sum_{\Norm{\mathfrak{a}}\le N}\chi(\mathfrak{a})\biggr\rVert
  \;\le\; C \cdot N^{1 - 1/[K:\Q]} \qquad\text{for all }N\ge 1.
`

{uses "ideal-count-uniform"}[]
{uses "fourier-decay-realized"}[]
{uses "autopow-frobenius-residue"}[]
:::

:::proof "character-sum-geom-numbers"

Geometry-of-numbers count of ideals in a norm-bounded region
({Informal.citet sharifi (kind := theorem) (index := "7.1.19")}[], p.~142, step~1). The character value
$`\chi(\mathfrak a)` depends only on the Frobenius
$`\sigma_{\mathfrak a}`, which the cyclotomic dictionary
{bpref "autopow-frobenius-residue"}[] identifies with the norm residue
$`\Norm{\mathfrak a}\bmod m`; so $`\sum_{\Norm{\mathfrak a}\le
N}\chi(\mathfrak a)` is a $`\chi`-weighted sum of the per-norm-residue
ideal counts. The effective count
{bpref "ideal-count-uniform"}[], made uniform over the realized
residue subgroup by the Fourier-decay input
{bpref "fourier-decay-realized"}[], gives each residue class the count
$`\kappa N + O(N^{1-1/[K:\Q]})` with a common leading constant
$`\kappa`. Summing over $`\chi(\mathfrak a) = \zeta` for $`\zeta` a root
of unity, the equal $`\kappa N` main terms cancel by $`\sum_\zeta\zeta =
0`, leaving only the $`O(N^{1-1/[K:\Q]})` errors.

:::

:::lemma_ "artin-analytic-extension" (lean := "Chebotarev.artinLSeries_analytic_extension")

For every nontrivial character $`\chi: G \to \C^\times`, the
Dirichlet series
$`L(\chi, s) = \sum_{\mathfrak{a}} \chi(\mathfrak{a})\Norm{\mathfrak{a}}^{-s}`
extends to a function analytic on $`\re(s) > 1 - 1/[K:\Q]`, agreeing
with the Euler product on $`\re(s) > 1`. In particular, $`L(\chi, 1)`
is well-defined.

{uses "artin-euler-product-abelian"}[]
{uses "character-sum-geom-numbers"}[]

:::

:::proof "artin-analytic-extension"

Combine {bpref "character-sum-geom-numbers"}[] ({Informal.citet sharifi (kind := theorem) (index := "7.1.19")}[] step 1a)
with {Informal.citet sharifi (kind := lemma) (index := "7.1.5")}[] (p.~138, a generic Dirichlet-series
convergence criterion from a polynomial bound on partial sums):
given $`\bigl|\sum_{n\le N}a_n\bigr|\le CN^{u}`, the Dirichlet series
$`\sum_n a_n n^{-s}` converges absolutely and uniformly on every
compact subset of $`\re(s) > u`. Applied to
$`a_{\mathfrak{a}} = \chi(\mathfrak{a})` with $`u = 1 - 1/[K:\Q]`, the
series defines an analytic function on
$`\re(s) > 1 - 1/[K:\Q]`.

:::

:::lemma_ "artin-one-ne-zero" (lean := "Chebotarev.artinLSeries_one_ne_zero")

For every nontrivial character $`\chi: G \to \C^\times`,
$`L(\chi, 1) \ne 0`. (Here $`L(\chi, 1)` refers to the analytic
extension of {bpref "artin-analytic-extension"}[].)

{uses "artin-analytic-extension"}[]

:::

:::proof "artin-one-ne-zero"

{Informal.citet sharifi (kind := theorem) (index := "7.1.19")}[] step 2 (p.~142). Write
$`\log\zeta_L(t) = \sum_\chi \log L(\chi, t)` for $`t > 1`. Up to a
bounded function as $`t \to 1^+`, the right side has absolute value
at least $`\bigl(1 - \sum_\chi m_\chi\bigr)\log(t-1)^{-1}`, where
$`m_\chi` is the order of vanishing of $`L(\chi, s)` at $`s = 1`. If
any $`m_\chi \ge 1`, this is at most $`0\cdot\log(t-1)^{-1}`,
contradicting $`\log\zeta_L(s) \sim \log(s-1)^{-1}`.

:::

:::theorem "dedekind-zeta-factorisation"

Let $`L/K` be a finite abelian Galois extension of number fields.
There is a family of functions
$`\set{L(\chi, \cdot) : \chi\in\widehat{G}}`, each holomorphic on
$`\re(s) > 1`, satisfying:

1. $`\displaystyle\zeta_L(s)
   \;=\; \prod_{\chi\in\widehat{G}} L(\chi, s)` for $`\re(s) > 1`;
2. $`L(\mathbf{1}, s) = \zeta_K(s)`;
3. $`L(\chi, 1) \ne 0` for every $`\chi \ne \mathbf{1}`.

{uses "galois-character"}[]
{uses "dedekind-local-factor"}[]
{uses "artin-one-ne-zero"}[]

:::

:::proof "dedekind-zeta-factorisation"

Compose {bpref "dedekind-local-factor"}[] prime by prime, using the
absolute convergence of the global Euler product; combine with the
non-vanishing {bpref "artin-one-ne-zero"}[].

{uses "dedekind-local-factor"}[]
{uses "artin-one-ne-zero"}[]

:::
