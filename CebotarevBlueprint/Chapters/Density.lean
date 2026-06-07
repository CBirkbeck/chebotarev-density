import Verso
import VersoManual
import VersoBlueprint
import CebotarevDensity

open Verso.Genre
open Verso.Genre.Manual
open Informal

tex_prelude r#"\def\Z{\mathbb{Z}}\def\Q{\mathbb{Q}}\def\R{\mathbb{R}}\def\C{\mathbb{C}}\def\N{\mathbb{N}}\def\F{\mathbb{F}}\def\OK{\mathcal{O}_K}\def\Ocirc{\mathcal{O}}\def\Gal#1{\mathrm{Gal}(#1)}\def\Norm#1{\mathrm{N}(#1)}\def\fp{\mathfrak{p}}\def\fP{\mathfrak{P}}\def\Frob{\mathrm{Frob}}\def\Re{\operatorname{Re}}\def\re{\operatorname{Re}}\def\set#1{\left\{#1\right\}}\def\setof#1#2{\left\{#1\;\middle|\;#2\right\}}\def\abs#1{\left\lvert#1\right\rvert}\def\norm#1{\left\lVert#1\right\rVert}\def\ang#1{\left\langle#1\right\rangle}"#

#doc (Manual) "Dirichlet density" =>

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

:::proof "prime-zeta-higher-tail-bounded"

Summing the geometric series $`\sum_{k\ge 2} N\fp^{-ks}` over $`k`
gives the per-prime term $`N\fp^{-2s}/(1-N\fp^{-s})`, so the tail of the
log-Euler-product is dominated termwise by $`\sum_\fp
N\fp^{-2s}/(1-N\fp^{-s})`. For $`s>1` (indeed already for
$`\re(s)>1/2`) each prime has $`N\fp\ge 2`, whence $`N\fp^{-s}\le 1/2`,
so $`(1-N\fp^{-s})^{-1}\le 2` and the term is bounded above by
$`2\,N\fp^{-2}`. The majorant $`\sum_\fp 2\,N\fp^{-2}` is a convergent
series independent of $`s` — it is dominated by $`\zeta_K(2)` — so the
constant $`C = 2\sum_\fp N\fp^{-2}` bounds the tail uniformly on a right
neighbourhood of $`1`.

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

:::theorem "prime-zeta-ge-log-minus-bounded" (lean := "Chebotarev.log_minus_bounded_le_primeIdealZetaSum")

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

:::theorem "tendsto-ratio-one-of-log-pm-bounded" (lean := "tendsto_ratio_one_of_log_pm_bounded")

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

# Density API

The following routine API lemmas are used by the proofs of the
corollaries in the final chapter ({bpref "chebotarev-density"}[]).

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
