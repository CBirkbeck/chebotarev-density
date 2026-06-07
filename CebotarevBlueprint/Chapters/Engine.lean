import Verso
import VersoManual
import VersoBlueprint
import CebotarevDensity
import CebotarevBlueprint.Refs

open Verso.Genre
open Verso.Genre.Manual
open Informal

tex_prelude r#"\def\Z{\mathbb{Z}}\def\Q{\mathbb{Q}}\def\R{\mathbb{R}}\def\C{\mathbb{C}}\def\N{\mathbb{N}}\def\F{\mathbb{F}}\def\OK{\mathcal{O}_K}\def\Ocirc{\mathcal{O}}\def\Gal#1{\mathrm{Gal}(#1)}\def\Norm#1{\mathrm{N}(#1)}\def\fp{\mathfrak{p}}\def\fP{\mathfrak{P}}\def\Frob{\mathrm{Frob}}\def\Re{\operatorname{Re}}\def\re{\operatorname{Re}}\def\set#1{\left\{#1\right\}}\def\setof#1#2{\left\{#1\;\middle|\;#2\right\}}\def\abs#1{\left\lvert#1\right\rvert}\def\norm#1{\left\lVert#1\right\rVert}\def\ang#1{\left\langle#1\right\rangle}"#

#doc (Manual) "The effective ideal-count engine" =>

The abelian case of Chebotarev is, in this development, fed not by class
field theory but by an effective geometry-of-numbers count of integral
ideals in a norm-residue class. This chapter assembles the public layer
of that engine: an effective lattice-point count with a Lipschitz-boundary
error term (Widmer; {Informal.citet "gun-ramare-sivaraman"}[]), its transport to the ideal
lattice, a Fourier/realizer argument that makes the leading constant
uniform over the residues that actually occur as ideal norms, and the
CFT-free dictionary tying Frobenius elements to norm residues in a
cyclotomic extension. The chapter closes with the fixed-field density
transfer ({Informal.citet sharifi (kind := theorem) (index := "7.2.2")}[] Step 1) and the log-asymptotic ratio lemma.

Throughout, $`\Lambda` denotes the standard integer lattice
$`\Z^\iota\subseteq\R^\iota` and $`d` an ambient dimension (the degree
$`[K:\Q]` once the engine is applied to the ideal lattice). We write
$`\operatorname{vol}(s)` for the Lebesgue measure of a region $`s` and
$`\det T` for the determinant of a linear automorphism $`T`.

# Effective lattice-point count

:::theorem "unit-grid-lattice-count" (lean := "Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le")

Let $`s\subseteq\R^\iota` be a bounded measurable set whose frontier is
covered by finitely many Lipschitz images of the unit cube
$`[0,1]^{d-1}`. Then there is a constant $`C` such that, for every
$`n\ge 1`,
$$`
  \abs{\#\bigl(s\cap n^{-1}\Lambda\bigr)
       - \operatorname{vol}(s)\,n^{d}}
  \;\le\; C\,n^{d-1}.
`
That is, the number of points of the scaled lattice $`n^{-1}\Lambda` in
$`s` equals $`\operatorname{vol}(s)\,n^{d}` up to an error of order
$`n^{d-1}`.

:::

:::proof "unit-grid-lattice-count"

Tile $`\R^\iota` by the unit cells of the grid $`n^{-1}\Lambda`. A cell
entirely inside $`s` contributes its tag point to the count and its
volume $`n^{-d}` to $`\operatorname{vol}(s)`; a cell entirely outside
contributes neither. The discrepancy
$`\#(s\cap n^{-1}\Lambda) - \operatorname{vol}(s)\,n^{d}` is therefore
controlled by the cells that straddle the boundary $`\partial s`: each
such cell is connected and meets both $`s` and its complement, hence
meets $`\partial s`. The number of boundary-meeting cells is at most the
number of grid cells that intersect $`\partial s`. Since $`\partial s` is
covered by finitely many $`M`-Lipschitz images of $`[0,1]^{d-1}`, a
single chart image meets $`O(n^{d-1})` cells (subdivide the cube into
$`(n+1)^{d-1}` subcubes of diameter $`\le 1/n`, each mapped into a set of
diameter $`\le M/n` that meets at most $`(2\lceil M\rceil+1)^{d}` cells),
so the whole frontier meets $`O(n^{d-1})` cells. Taking $`C` to be the
resulting explicit constant gives the bound.

:::

:::theorem "normleone-frontier-cover" (lean := "Chebotarev.normLeOne_frontier_lipschitz_cover")

For a number field $`K`, the frontier of the image
$`\operatorname{normAtAllPlaces}(\{x : \norm{x}\le 1\})` inside the real
place-space is covered by finitely many $`M`-Lipschitz maps from the
unit cube $`[0,1]^{r-1}` (one common Lipschitz constant $`M`), where
$`r` is the number of infinite places.

:::

:::proof "normleone-frontier-cover"

mathlib parametrizes the norm-$`\le 1` region of the fundamental cone by
$`\operatorname{normAtAllPlaces}(\{\norm{x}\le 1\})
= \operatorname{expMapBasis}(\text{paramSet})`, where the parameter set
is a box. The frontier of an image is contained in the image of the box
boundary together with the single escape point $`0`. The box boundary
splits into the $`w_0`-face (set the distinguished coordinate to $`0`)
and the side faces (set some other coordinate to $`0` or $`1`), and on
the unbounded direction the substitution $`t=\exp(x_{w_0})\in(0,1]`
linearizes the exponential. Each face is the image of $`[0,1]^{r-1}`
under a globally $`C^1` map; precomposing with a coordinate clamp onto
the cube makes each map globally Lipschitz, with a common constant
obtained as the maximum over the finitely many faces. Bundling the zero
map, the $`w_0`-face, and the side faces into one finite family gives the
cover.

:::

:::theorem "normleone-frontier-cover-index" (lean := "Chebotarev.normLeOne_frontier_lipschitz_cover_index")

Transported to the standard Euclidean coordinate space of the chosen
$`\Z`-basis of the ideal lattice, the frontier of the coordinate image
of the norm-$`\le 1` region is again covered by finitely many
$`M`-Lipschitz cube images. This is the exact Lipschitz-boundary
hypothesis consumed by the coset lattice count.

{uses "normleone-frontier-cover"}[]
:::

:::proof "normleone-frontier-cover-index"

Lift the real-place cover {bpref "normleone-frontier-cover"}[] to the
mixed space by adjoining phase coordinates: each complex place
contributes a unit-circle phase $`\theta\mapsto e^{i(2\pi\theta-\pi)}`
(globally Lipschitz) and each real place a sign, so a bounded Lipschitz
real-place map lifts to a bounded Lipschitz mixed-space map covering the
fibres over $`\operatorname{normAtAllPlaces}`. Then push forward along
the standard-basis coordinate isomorphism
$`(\operatorname{stdBasis})\colon \text{mixedSpace} \simeq
(\text{index}\to\R)`, a homeomorphism that carries frontiers to
frontiers and Lipschitz maps to Lipschitz maps; matching cube dimensions
through $`\#\text{index} - 1 = [K:\Q] - 1` yields the transported cover.

:::

:::theorem "coset-lattice-count" (lean := "Chebotarev.exists_card_coset_inter_smul_sub_volume_mul_rpow_le")

Let $`T` be a linear automorphism of $`\R^\iota` and $`D` a bounded
measurable set with a finite Lipschitz cube cover of $`\partial D`. Then
there is a constant $`C` such that, for every translate $`\xi` and every
$`t\ge 1`,
$$`
  \abs{\#\bigl((\xi + T\Lambda)\cap t\,D\bigr)
       - \frac{\operatorname{vol}(D)}{\abs{\det T}}\,t^{d}}
  \;\le\; C\,t^{d-1},
`
with the implied constant $`C` uniform in $`\xi`. This is the
Widmer / {Informal.citet "gun-ramare-sivaraman"}[] $`\xi`-uniform coset count.

{uses "unit-grid-lattice-count"}[]
{uses "normleone-frontier-cover"}[]
{uses "normleone-frontier-cover-index"}[]
:::

:::proof "coset-lattice-count"

Transport the data through $`T^{-1}`: the set $`D' = T^{-1}(D)` is again
bounded and measurable with a Lipschitz-covered frontier (compose the
charts with the continuous-linear $`T^{-1}`), and
$`\operatorname{vol}(D') = \operatorname{vol}(D)/\abs{\det T}`. Under the
same change of variables the coset $`\xi + T\Lambda` becomes a translate
$`T^{-1}\xi + \Lambda` of the standard lattice. A scaling bijection
$`x\mapsto t\,x` and the translation reduce the count to
$`\#(\Lambda\cap R)` for $`R = -T^{-1}\xi + t\,D'`, to which the unit-grid
bridge {bpref "unit-grid-lattice-count"}[] applies at $`n=1`; the
boundary cells are controlled by the transported Lipschitz cover (whose
existence, when $`D` is the norm-$`\le 1` region, is
{bpref "normleone-frontier-cover-index"}[], itself transported from
{bpref "normleone-frontier-cover"}[]). The error constant produced by the
bridge depends only on the cover data and the dimension, hence is uniform
in $`\xi`.

:::

# From lattice cells to ideal counts

:::theorem "ideal-count-by-norm-residue" (lean := "Chebotarev.exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le")

Fix a modulus $`c\ge 1` and a residue $`a\in\Z/c\Z`. There are constants
$`\kappa, C'` such that, for every $`N\ge 1`,
$$`
  \abs{\#\setof{I\subseteq\OK}{\Norm{I}\le N,\;\Norm{I}\equiv a\!\!\pmod c}
       - \kappa\,N}
  \;\le\; C'\,N^{1-1/d}.
`
The count of integral ideals of norm at most $`N` in a fixed norm-residue
class grows linearly in $`N` with an effective $`O(N^{1-1/d})` error.

{uses "coset-lattice-count"}[]
:::

:::proof "ideal-count-by-norm-residue"

Split the count over the ideal class group: in each class $`\mathcal C`,
multiplication by a fixed integral representative $`\mathfrak b` of
$`\mathcal C^{-1}` principalizes the ideals (matching class-$`\mathcal C`
ideals of norm $`\le N` with $`\mathfrak b`-divisible *principal* ideals
of norm $`\le N\,\Norm{\mathfrak b}`), and a principal ideal is the norm-$`\le t^{d}`
slice of the fundamental cone scaled by $`t = (N\Norm{\mathfrak
b})^{1/d}`. Choosing the standard $`\Z`-basis of the ideal lattice
realizes this slice as $`t\,D` for $`D` the coordinate image of the
norm-$`\le 1` region, and the algebraic norm is constant on each
$`(\text{sign-orthant},\text{coset})` cell modulo $`c`; the coset count
{bpref "coset-lattice-count"}[] gives each cell an estimate
$`L\,t^{d} + O(t^{d-1})`. Summing the finitely many cells and the finitely
many classes, and converting $`t^{d}=N\Norm{\mathfrak b}` and
$`t^{d-1}=O(N^{1-1/d})`, yields the linear main term $`\kappa N` with the
stated error.

:::

:::theorem "ideal-count-uniform" (lean := "Chebotarev.exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform")

Let $`S\subseteq(\Z/c\Z)^\times` be a subgroup, and suppose every element
of $`S` actually occurs as an ideal-norm residue (the realized-residue
hypothesis, supplied by {bpref "fourier-decay-realized"}[]). Then a
*single* pair $`\kappa, C'` works simultaneously for all $`a\in S`:
$$`
  \abs{\#\setof{I}{\Norm{I}\le N,\;\Norm{I}\equiv a\!\!\pmod c}
       - \kappa\,N}
  \;\le\; C'\,N^{1-1/d}
  \qquad(a\in S,\ N\ge 1).
`

{uses "ideal-count-by-norm-residue"}[]
{uses "fourier-decay-realized"}[]
:::

:::proof "ideal-count-uniform"

By {bpref "ideal-count-by-norm-residue"}[] each residue $`a` has a
leading constant $`\kappa_a` (the limit of $`\#\{\dots\}/N`) and an
effective bound. It remains to see $`\kappa_a` is constant on $`S`. The
$`\chi`-twisted residue averages
$`\sum_{a}\chi(a)\,\kappa_a` vanish for every nontrivial character
$`\chi` of $`S` — this is the Fourier-decay input
{bpref "fourier-decay-realized"}[]. By Fourier inversion over the finite
abelian group $`S` (column orthogonality of characters), the vanishing of
all nontrivial Fourier coefficients forces $`\kappa_a` to be independent
of $`a\in S`. Taking $`\kappa = \kappa_1` and $`C' = \sum_a\abs{C'_a}`
gives the common pair.

:::

:::theorem "fourier-decay-realized" (lean := "Chebotarev.tendsto_sum_char_mul_cardNormLeResidue_div_of_realized")

Let $`S\le(\Z/c\Z)^\times` be a subgroup all of whose elements are
realized as ideal-norm residues, and let $`\chi\colon S\to\C^\times` be a
nontrivial character. Then the $`\chi`-twisted count average tends to
zero:
$$`
  \frac{1}{N}\sum_{a\in S}\chi(a)\,
    \#\setof{I}{\Norm{I}\le N,\;\Norm{I}\equiv a\!\!\pmod c}
  \;\xrightarrow[N\to\infty]{}\; 0.
`

{uses "ideal-count-by-norm-residue"}[]
:::

:::proof "fourier-decay-realized"

Each residue $`a\in S` has a well-defined density $`\kappa_a =
\lim_N \#\{\Norm{I}\le N, \Norm{I}\equiv a\}/N`
({bpref "ideal-count-by-norm-residue"}[]). The realizer transfer
({Informal.citet "lang-ant"}[], Ch. VI §3) shows these densities are *constant* on $`S`: if $`\mathfrak b` has
norm residue $`u\in S`, then $`I\mapsto\mathfrak b\,I` is a measure-preserving
correspondence shifting the residue by $`u`, so $`\kappa_{a} =
\kappa_{a\cdot u}` for all $`a`, and every $`u\in S` is so realized.
Hence $`\frac{1}{N}\sum_a\chi(a)\#\{\dots\}\to\bigl(\sum_{a\in
S}\chi(a)\bigr)\kappa_1`, and $`\sum_{a\in S}\chi(a) = 0` by row
orthogonality for the nontrivial character $`\chi`. The average tends to
zero.

:::

# The cyclotomic dictionary and Frobenii generation

:::theorem "autopow-frobenius-residue" (lean := "Chebotarev.autToPow_frobeniusClass_out")

Let $`L = K(\zeta_m)` and $`\fp` a nonzero prime of $`\OK` unramified in
$`L` with $`\Norm{\fp}` coprime to $`m`. Under the cyclotomic character
$`\Gal{L/K}\to(\Z/m\Z)^\times`, the Frobenius class representative
$`\sigma_\fp^{\,\mathrm{out}}` is sent to the unit $`\Norm{\fp}\bmod m`.
This is the CFT-free dictionary identifying the Frobenius with its norm
residue.

{uses "frobenius-class"}[]
:::

:::proof "autopow-frobenius-residue"

Pick a prime $`\fP\mid\fp` and let $`\varphi = \Frob_\fP`. The cyclotomic
Frobenius acts on roots of unity as the $`\Norm{\fp}`-power map,
$`\varphi(\zeta) = \zeta^{\Norm{\fp}}` ({Informal.citet sharifi (kind := theorem) (index := "7.2.1")}[](i)); since the
cyclotomic character $`\chi_{\mathrm{cyc}}` is defined by
$`\sigma(\zeta) = \zeta^{\chi_{\mathrm{cyc}}(\sigma)}` and $`\zeta` has
exact order $`m`, equal powers of $`\zeta` have congruent exponents mod
$`m`, so $`\chi_{\mathrm{cyc}}(\varphi) = \Norm{\fp}\bmod m`. The
cyclotomic character is a group homomorphism, hence constant on conjugacy
classes, so it sends the class representative
$`\sigma_\fp^{\,\mathrm{out}}` (conjugate to $`\varphi`) to the same unit
$`\Norm{\fp}\bmod m`.

:::

:::theorem "frobenii-generate" (lean := "Chebotarev.subgroup_eq_top_of_forall_frobenius_mem_of_coprime")

Let $`L/K` be a finite abelian Galois extension and $`H\le\Gal{L/K}` a
subgroup. If $`H` contains the Frobenius class representative of every
nonzero unramified prime $`\fp` whose norm is coprime to a fixed integer
$`m`, then $`H = \Gal{L/K}`. The Frobenii of coprime-norm primes generate
the Galois group — with no recourse to class field theory.

{uses "frobenius-class"}[]
:::

:::proof "frobenii-generate"

Reduce $`H = \top` to $`[F:K] = 1` for the fixed field $`F = L^{H}`. If
$`\fp` is a coprime-norm unramified prime whose Frobenius lies in
$`H = \mathrm{Fix}(F)`, its restriction to $`F` is trivial, so $`\fp`
splits completely in $`F` and every prime of $`\Ocirc_F` above it has
residue degree one and norm $`\Norm{\fp}`; thus there are exactly
$`[F:K]` primes of $`\Ocirc_F` above each such $`\fp`. Comparing the
zeta-sum
$`\sum_{\mathfrak q\subseteq\Ocirc_F}\Norm{\mathfrak q}^{-s}` against the
coprime-norm $`K`-sum gives $`[F:K]\sum_{\fp}\Norm{\fp}^{-s}\le
\sum_{\mathfrak q}\Norm{\mathfrak q}^{-s}`; since both sides are
asymptotic to $`\log\frac{1}{s-1}` (the coprime restriction discards only
finitely many primes, so it is asymptotically the full pole), dividing
and letting $`s\downarrow 1` forces $`[F:K]\le 1`, i.e. $`[F:K]=1`.

:::

# Fixed-field density transfer and the log-asymptotic ratio

:::theorem "density-lift-fixed-field" (lean := "Chebotarev.density_lift_through_fixedField")

Let $`\sigma\in\Gal{L/K}`, $`E = L^{\ang\sigma}` the fixed field of the
cyclic subgroup $`\ang\sigma`, and $`\sigma_E\in\Gal{L/E}` the
corresponding element. Given the abelian-case density
$`1/\abs{\Gal{L/E}}` for the Frobenius fibre of $`\sigma_E` over $`E`,
the $`K`-density of the Frobenius class $`[\sigma]` is
$`\abs{[\sigma]}/\abs{G}`:
$$`
  \delta_K(S) \;=\; \frac{f\abs{[\sigma]}}{\abs{G}}\,\delta_E(T_\sigma)
  \;=\; \frac{\abs{[\sigma]}}{\abs{G}},
  \qquad f = \mathrm{ord}(\sigma).
`
This is {Informal.citet sharifi (kind := theorem) (index := "7.2.2")}[] Step 1.

{uses "dirichlet-density"}[]
{uses "frobenius-class"}[]
:::

:::proof "density-lift-fixed-field"

Write $`S = \setof{\fp}{\sigma_\fp = [\sigma]}` and $`T_\sigma` for the
$`\sigma_E`-fibre over $`E`. The primes of $`E` above an $`\fp\in S`
split into a degree-one part $`T_1` (where $`\Norm{P} = \Norm{\fp}` and
$`\Frob_P^{E}` restricts to $`\sigma`) and a higher-degree/ramified part
$`T_2`. A transitivity count shows each $`\fp\in S` has exactly
$`\abs{G}/(f\abs{[\sigma]})` primes $`P\in T_1` above it, giving the exact
identity $`\sum_{T_1}\Norm{P}^{-s} = \frac{\abs{G}}{f\abs{[\sigma]}}
\sum_{S}\Norm{\fp}^{-s}` once $`\Norm{P}=\Norm{\fp}` is used. The tail
$`T_2` is a sum over primes of residue degree $`\ge 2` plus finitely many
ramified primes, hence negligible: $`\sum_{T_2}\Norm{P}^{-s}/\sum_{\mathfrak
q\subseteq\Ocirc_E}\Norm{\mathfrak q}^{-s}\to 0`. Combining with the
abelian density $`\delta_E(T_\sigma) = 1/\abs{\Gal{L/E}} = 1/f` and the
asymptotic $`\sum_{\mathfrak q}\Norm{\mathfrak q}^{-s}\sim\sum_\fp
\Norm{\fp}^{-s}` over $`E` and $`K`, the limit evaluates to
$`\delta_K(S) = (f\abs{[\sigma]}/\abs{G})\cdot(1/f) = \abs{[\sigma]}/\abs{G}`.

:::

:::theorem "log-asymptotic-ratio" (lean := "tendsto_ratio_one_of_log_pm_bounded")

Let $`f\colon(1,\infty)\to\R`. If $`f` is sandwiched on a right
neighbourhood of $`1` as
$$`
  \log\frac{1}{s-1} - C \;\le\; f(s) \;\le\; \log\frac{1}{s-1} + C',
`
then $`f(s)/\log\frac{1}{s-1}\to 1` as $`s\downarrow 1`.

:::

:::proof "log-asymptotic-ratio"

The denominator $`\log\frac{1}{s-1}` tends to $`+\infty` as
$`s\downarrow 1`, so the bounded additive constants $`C, C'` wash out
under division: the normalized difference
$`\bigl(f(s)-\log\frac{1}{s-1}\bigr)/\log\frac{1}{s-1}` is squeezed
between $`-C/\log\frac{1}{s-1}` and $`C'/\log\frac{1}{s-1}`, both of which
tend to $`0`. Adding back $`1` gives the limit
$`f(s)/\log\frac{1}{s-1}\to 1`.

:::
