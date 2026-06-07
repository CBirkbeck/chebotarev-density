import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Chebotarev: abelian case" =>

tex_prelude r#"\newcommand{\Z}{\mathbb{Z}}\newcommand{\Q}{\mathbb{Q}}\newcommand{\R}{\mathbb{R}}\newcommand{\C}{\mathbb{C}}\newcommand{\N}{\mathbb{N}}\newcommand{\F}{\mathbb{F}}\newcommand{\OK}{\mathcal{O}_K}\newcommand{\Ocirc}{\mathcal{O}}\newcommand{\Gal}[1]{\mathrm{Gal}(#1)}\newcommand{\Norm}[1]{\mathrm{N}(#1)}\newcommand{\fp}{\mathfrak{p}}\newcommand{\fP}{\mathfrak{P}}\newcommand{\Frob}{\mathrm{Frob}}\renewcommand{\Re}{\operatorname{Re}}\newcommand{\re}{\operatorname{Re}}\newcommand{\set}[1]{\left\{ #1 \right\}}\newcommand{\setof}[2]{\left\{ #1 \;\middle|\; #2 \right\}}\newcommand{\abs}[1]{\left\lvert #1 \right\rvert}\newcommand{\norm}[1]{\left\lVert #1 \right\rVert}\newcommand{\ang}[1]{\left\langle #1 \right\rangle}"#

The abelian case is reduced to the cyclotomic case by Chebotarev's
original crossing trick. Source: Sharifi 7.2.2 Step 2 (pp.~143--144).

:::lemma "cyclic-subgroup-trivial-meet" (lean := "Chebotarev.cyclic_subgroup_meets_G_times_one_trivially")

Let $`G, H` be finite groups, $`\sigma \in G`, $`\tau \in H`. If
$`\abs{G}\mid\mathrm{ord}(\tau)`, then
$`\ang{(\sigma,\tau)}\cap (G\times\{1\}) = \{1\}`.

:::

:::proof "cyclic-subgroup-trivial-meet"

Pure group theory. If $`(\sigma^k, \tau^k) \in G\times\{1\}` then
$`\tau^k = 1`, so $`\mathrm{ord}(\tau)\mid k`, hence
$`\abs{G}\mid k`, hence $`\sigma^k = 1`.

:::

:::lemma "density-S-sigma-tau" (lean := "Chebotarev.liminf_density_S_sigma_ge_card_H_n_div_GH")

Let $`L/K` be a finite abelian Galois extension with $`G=\Gal{L/K}`,
$`\sigma\in G`, and $`m\ge 1` coprime to the discriminant of $`L`, so
that $`\Gal{L(\zeta_m)/K}\cong G\times H` with
$`H=\Gal{K(\zeta_m)/K}\subseteq(\Z/m\Z)^\times`. Set
$`H_n = \setof{\tau\in H}{\abs{G}\mid\mathrm{ord}(\tau)}`. Then
$$`
    \delta_{\mathrm{inf}}\bigl(\setof{\fp\subset\OK}{
      \sigma_\fp = \sigma}\bigr)
    \;\ge\; \frac{\abs{H_n}}{\abs{G}\cdot\abs{H}}.
`
*Corrected.* An earlier draft of this lemma claimed
$`\delta\bigl(\set{\fp : \sigma_\fp = \sigma}\bigr) = 1/(\abs{G}\cdot\abs{H})`
— that is mathematically wrong (the set $`\set{\sigma_\fp = \sigma}`
has density $`1/\abs{G}`, not $`1/(\abs{G}\cdot\abs{H})`). The actual
per-$`m` step that feeds into the proof of $`\delta(\sigma_\fp = \sigma)
= 1/\abs{G}` is the $`\liminf` lower bound above (Sharifi p.~144).

{uses "cyclic-subgroup-trivial-meet"}[]
{uses "chebotarev-cyclotomic"}[]
:::

:::proof "density-S-sigma-tau"

By {bpref "cyclic-subgroup-trivial-meet"}[], the fixed field
$`F = L(\zeta_m)^{\ang{(\sigma,\tau)}}` satisfies
$`F(\zeta_m) = L(\zeta_m)`, so the extension $`L(\zeta_m)/F` is
cyclotomic. Apply the cyclotomic case
{bpref "chebotarev-cyclotomic"}[] to $`L(\zeta_m)/F` to obtain
$`\delta_F = 1/\abs{\ang{(\sigma,\tau)}}`. The conjugacy-class
reduction ({bpref "chebotarev-density"}[] below, Step~1's counting)
lifts this to a $`K`-density of $`1/(\abs{G}\cdot\abs{H})`.

:::

:::lemma "H-n-over-H-formula" (lean := "Chebotarev.H_n_over_H_lower_bound_via_prime_factorisation")

Let $`n = p_1^{k_1}\cdots p_r^{k_r}` with $`p_i` distinct primes,
$`k_i\ge 1`. For an integer $`m \ge 1` with $`m \equiv 1 \pmod{n^j}`,
setting $`j_i = v_{p_i}(m-1) \ge j` and
$`H_n = \setof{\tau\in(\Z/m\Z)^\times}{n\mid\mathrm{ord}(\tau)}`,
$$`
    \frac{\abs{H_n}}{\abs{(\Z/m\Z)^\times}}
    \;=\; \prod_{i=1}^r\!\biggl(1-\frac{p_i^{k_i-1}}{p_i^{j_i k_i}}\biggr)
    \;\ge\; \prod_{i=1}^r\!\biggl(1-\frac{1}{p_i^{(j-1)k_i+1}}\biggr).
`

:::

:::proof "H-n-over-H-formula"

Direct combinatorial computation on $`(\Z/m\Z)^\times` using CRT and
the prime-power factorisation of $`n` (Sharifi p.~144).

:::

:::lemma "H-n-over-H-tends-one" (lean := "Chebotarev.H_n_over_H_tends_to_one")

As $`k \to \infty`,
$`\abs{H_n}/\abs{(\Z/n^k\Z)^\times} \to 1`.

{uses "H-n-over-H-formula"}[]
:::

:::proof "H-n-over-H-tends-one"

Limit of the product formula {bpref "H-n-over-H-formula"}[] as
$`j \to \infty`: each factor tends to $`1`.

:::

:::lemma "liminf-ratio-ge-inv-card-G" (lean := "Chebotarev.liminf_ratio_ge_inv_card_G")

For every $`\sigma\in G`,
$`\delta_{\mathrm{inf}}\bigl(\setof{\fp}{\sigma_\fp = \sigma}\bigr)
\ge 1/\abs{G}`.

{uses "density-S-sigma-tau"}[]
{uses "H-n-over-H-tends-one"}[]
:::

:::proof "liminf-ratio-ge-inv-card-G"

Take the limit of the per-$`m` bound
{bpref "density-S-sigma-tau"}[] as $`m \to \infty` along
$`m \equiv 1\pmod{\abs{G}^k}`, where $`\abs{H_n}/\abs{H}\to 1` by
{bpref "H-n-over-H-tends-one"}[].

:::

:::lemma "ratiosum-fibres-tendsto-one" (lean := "Chebotarev.ratioSum_frobeniusFibres_tendsto_one")

As $`s\downarrow 1`, the sum over $`\sigma\in G` of the density ratios
of the fibres $`\setof{\fp}{\sigma_\fp=\sigma}` tends to $`1`.

{uses "frobenius-class"}[]
{uses "finite-ramified-primes"}[]
:::

:::proof "ratiosum-fibres-tendsto-one"

The fibres partition the unramified primes; the ramified primes are
finite ({bpref "finite-ramified-primes"}[]) hence contribute density
$`0`, so the partial sums of the fibre ratios equal the ratio for the
unramified primes, which $`\to 1`.

:::

:::lemma "pigeonhole-density" (lean := "Chebotarev.tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one")

Let $`g_i` ($`i` in a finite index set of size $`N`) be real functions
with $`\liminf_{s\downarrow 1} g_i \ge 1/N` for each $`i`, and
$`\sum_i g_i(s) \to 1` as $`s\downarrow 1`. Then $`g_i(s) \to 1/N` for
every $`i`.

:::

:::proof "pigeonhole-density"

Pure real analysis: the lower bounds and the sum-limit pin every
$`g_i` to $`1/N` by a $`\liminf`/$`\limsup` pigeonhole.

:::

:::theorem "chebotarev-abelian" (lean := "Chebotarev.chebotarev_abelian")

For a finite abelian Galois extension $`L/K` of number fields with
$`G=\Gal{L/K}` and every $`\sigma\in G`,
$$`
    \delta\bigl(\setof{\fp\subset\OK}{\sigma_\fp = \sigma}\bigr)
    \;=\; \frac{1}{\abs{G}}.
`

{uses "dirichlet-density"}[]
{uses "frobenius-class"}[]
{uses "liminf-ratio-ge-inv-card-G"}[]
{uses "ratiosum-fibres-tendsto-one"}[]
{uses "pigeonhole-density"}[]
:::

:::proof "chebotarev-abelian"

The $`\abs{G}` fibres each have $`\liminf \ge 1/\abs{G}`
({bpref "liminf-ratio-ge-inv-card-G"}[]) and their density ratios sum
to $`1` ({bpref "ratiosum-fibres-tendsto-one"}[]); the pigeonhole glue
{bpref "pigeonhole-density"}[] forces each fibre's ratio to the limit
$`1/\abs{G}`.

:::
