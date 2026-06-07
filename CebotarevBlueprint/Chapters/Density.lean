import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Dirichlet density" =>

tex_prelude r#"\newcommand{\Z}{\mathbb{Z}}\newcommand{\Q}{\mathbb{Q}}\newcommand{\R}{\mathbb{R}}\newcommand{\C}{\mathbb{C}}\newcommand{\N}{\mathbb{N}}\newcommand{\F}{\mathbb{F}}\newcommand{\OK}{\mathcal{O}_K}\newcommand{\Ocirc}{\mathcal{O}}\newcommand{\Gal}[1]{\mathrm{Gal}(#1)}\newcommand{\Norm}[1]{\mathrm{N}(#1)}\newcommand{\fp}{\mathfrak{p}}\newcommand{\fP}{\mathfrak{P}}\newcommand{\Frob}{\mathrm{Frob}}\renewcommand{\Re}{\operatorname{Re}}\newcommand{\re}{\operatorname{Re}}\newcommand{\set}[1]{\left\{ #1 \right\}}\newcommand{\setof}[2]{\left\{ #1 \;\middle|\; #2 \right\}}\newcommand{\abs}[1]{\left\lvert #1 \right\rvert}\newcommand{\norm}[1]{\left\lVert #1 \right\rVert}\newcommand{\ang}[1]{\left\langle #1 \right\rangle}"#

Throughout, $`K` denotes a number field, $`\OK` its ring of integers, and
$`\fp` ranges over nonzero prime ideals of $`\OK` with absolute norm
$`N\fp=[\OK:\fp]`.

:::definition "dirichlet-density" (lean := "Chebotarev.HasDirichletDensity")

A set $`S` of nonzero prime ideals of $`\OK` has *Dirichlet
density* $`\delta\in\R`, written $`\delta(S)=\delta`, if
$$`
    \lim_{s\to 1^+}
    \frac{\displaystyle\sum_{\fp\in S} N\fp^{-s}}
         {\displaystyle\sum_{\fp} N\fp^{-s}}
    = \delta,
`
where the denominator sum runs over all nonzero prime ideals of
$`\OK`.

:::

The denominator is asymptotically $`\log\bigl(1/(s-1)\bigr)` as
$`s\downarrow 1` (Sharifi Prop.~7.1.12, p.~140); the lemmas below break
out the analytic ingredients.

:::theorem "prime-zeta-higher-tail-bounded" (lean := "Chebotarev.primeIdealZetaHigherTail_bounded")

The higher-power tail of the log-Euler-product
$`\sum_{\fp,k\ge 2}\frac{N\fp^{-2s}}{1-N\fp^{-s}}` is bounded on a
right neighbourhood of $`s=1`.

:::

:::theorem "logzeta-eq-primesum-bounded" (lean := "Chebotarev.logDedekindZeta_sub_primeIdealZetaSum_bounded")

Euler-product-log identity:
$`\bigl|\log\zeta_K(s) - \sum_\fp N\fp^{-s}\bigr| \le C` on a right
neighbourhood of $`1`.

{uses "prime-zeta-higher-tail-bounded"}[]

:::

:::proof "logzeta-eq-primesum-bounded"

$`\log\zeta_K(s) = \sum_\fp N\fp^{-s} +
\sum_{\fp,k\ge2} N\fp^{-ks}/k`; the tail is bounded by
{bpref "prime-zeta-higher-tail-bounded"}[].

:::

:::theorem "logzeta-eq-loginv-bounded" (lean := "Chebotarev.logDedekindZeta_sub_log_inv_sub_one_bounded")

Simple-pole identity:
$`\bigl|\log\zeta_K(s) - \log(1/(s-1))\bigr| \le C` on a right
neighbourhood of $`1`.

:::

:::proof "logzeta-eq-loginv-bounded"

From the simple pole of $`\zeta_K` at $`s=1` (mathlib's
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`):
$`(s-1)\zeta_K(s) \to r > 0` (the residue,
`dedekindZeta_residue_pos`), so
$`\log\zeta_K(s) - \log(1/(s-1)) = \log\bigl((s-1)\zeta_K(s)\bigr)`
converges to $`\log r` and is therefore bounded near $`1`.

:::

:::theorem "prime-zeta-ge-log-minus-bounded" (lean := "Chebotarev.primeIdealZetaSum_ge_log_minus_bounded")

There is a constant $`C` such that, for $`s>1` in a right neighbourhood
of $`1`,
$$`
    \sum_{\fp} N\fp^{-s} \;\ge\; \log\frac{1}{s-1} - C.
`

{uses "logzeta-eq-primesum-bounded"}[] {uses "logzeta-eq-loginv-bounded"}[]

:::

:::proof "prime-zeta-ge-log-minus-bounded"

Chain the two identities
{bpref "logzeta-eq-primesum-bounded"}[] {bpref "logzeta-eq-loginv-bounded"}[]:
$`\sum_\fp N\fp^{-s} \ge \log\zeta_K(s) - C_1 \ge \log(1/(s-1)) - C_1 - C_2`.

:::

:::theorem "prime-zeta-le-log-plus-bounded" (lean := "Chebotarev.primeIdealZetaSum_le_log_plus_bounded")

There is a constant $`C'` such that, for $`s>1` in a right neighbourhood
of $`1`,
$$`
    \sum_{\fp} N\fp^{-s} \;\le\; \log\frac{1}{s-1} + C'.
`

{uses "logzeta-eq-primesum-bounded"}[] {uses "logzeta-eq-loginv-bounded"}[]

:::

:::proof "prime-zeta-le-log-plus-bounded"

Same two identities
{bpref "logzeta-eq-primesum-bounded"}[] {bpref "logzeta-eq-loginv-bounded"}[],
transposed.

:::

:::theorem "tendsto-ratio-one-of-log-pm-bounded" (lean := "Chebotarev.tendsto_ratio_one_of_log_pm_bounded")

Let $`f : (1,\infty) \to \R`. If $`f` is sandwiched as
$`\log\bigl(1/(s-1)\bigr) - C \le f(s) \le \log\bigl(1/(s-1)\bigr) + C'`
on a right neighbourhood of $`1`, then
$`f(s)/\log\bigl(1/(s-1)\bigr) \to 1` as $`s \downarrow 1`.

:::

:::proof "tendsto-ratio-one-of-log-pm-bounded"

Since $`\log\bigl(1/(s-1)\bigr) \to \infty` as $`s \downarrow 1`, the
additive constants $`C, C'` wash out under division, and the squeeze
gives the limit $`1`.

:::

:::theorem "prime-ideal-sum-log" (lean := "Chebotarev.primeIdealZetaSum_univ_tendsto_log")

As $`s\downarrow 1`,
$$`
    \sum_{\fp} N\fp^{-s} \sim \log\frac{1}{s-1}.
`

{uses "prime-zeta-ge-log-minus-bounded"}[] {uses "prime-zeta-le-log-plus-bounded"}[] {uses "tendsto-ratio-one-of-log-pm-bounded"}[]

:::

:::proof "prime-ideal-sum-log"

Combine the lower bound {bpref "prime-zeta-ge-log-minus-bounded"}[] and
the upper bound {bpref "prime-zeta-le-log-plus-bounded"}[] into a
two-sided $`\log\bigl(1/(s-1)\bigr) \pm O(1)` sandwich, then apply
{bpref "tendsto-ratio-one-of-log-pm-bounded"}[] to extract the ratio
limit.

:::

## Density API

The following routine API lemmas are used by the proofs of the
corollaries in {bpref "ch:main"}[].

:::theorem "has-density-finite" (lean := "Chebotarev.hasDirichletDensity_of_finite")

A finite set of prime ideals has Dirichlet density $`0`.

{uses "dirichlet-density"}[]

:::

:::proof "has-density-finite"

The numerator $`\sum_{\fp\in S}\Norm{\fp}^{-s}` is bounded as $`s \to
1^+` (a finite sum of bounded terms), while the denominator
$`\sum_\fp \Norm{\fp}^{-s}\to\infty` by
{bpref "prime-ideal-sum-log"}[]; the ratio tends to $`0`.

:::

:::theorem "density-implies-lower" (lean := "Chebotarev.HasDirichletDensity.hasLower")

If $`S` has Dirichlet density $`\delta`, then its lower Dirichlet
density is also $`\delta`.

{uses "dirichlet-density"}[]

:::

:::proof "density-implies-lower"

Convergence of the ratio implies the liminf and limsup coincide with
the limit; specifically the liminf equals $`\delta`.

:::
