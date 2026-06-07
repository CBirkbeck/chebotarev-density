import Verso
import VersoManual
import VersoBlueprint
import CebotarevDensity

open Verso.Genre
open Verso.Genre.Manual
open Informal

tex_prelude r#"\def\Z{\mathbb{Z}}\def\Q{\mathbb{Q}}\def\R{\mathbb{R}}\def\C{\mathbb{C}}\def\N{\mathbb{N}}\def\F{\mathbb{F}}\def\OK{\mathcal{O}_K}\def\Ocirc{\mathcal{O}}\def\Gal#1{\mathrm{Gal}(#1)}\def\Norm#1{\mathrm{N}(#1)}\def\fp{\mathfrak{p}}\def\fP{\mathfrak{P}}\def\Frob{\mathrm{Frob}}\def\Re{\operatorname{Re}}\def\re{\operatorname{Re}}\def\set#1{\left\{#1\right\}}\def\setof#1#2{\left\{#1\;\middle|\;#2\right\}}\def\abs#1{\left\lvert#1\right\rvert}\def\norm#1{\left\lVert#1\right\rVert}\def\ang#1{\left\langle#1\right\rangle}"#

#doc (Manual) "Chebotarev: cyclotomic case" =>

For a cyclotomic extension $`L = K(\zeta_m)`, Chebotarev's theorem
reduces directly to Dirichlet's argument. Source: Sharifi 7.2.1
(pp.~142--143).

:::lemma_ "cyclotomic-frobenius-norm-power" (lean := "Chebotarev.cyclotomic_frobenius_acts_as_norm_power")

Let $`L = K(\zeta_m)`, $`\fp` a nonzero prime of $`\OK` unramified in
$`L`, and $`\fP` a prime of $`\Ocirc_L` above $`\fp`. Then for every
primitive $`m`-th root of unity $`\zeta \in L`,
$$`
  \Frob_\fP(\zeta) \;=\; \zeta^{N\fp}.
`

{uses "frobenius-at"}[]
:::

:::proof "cyclotomic-frobenius-norm-power"

By the defining property of $`\Frob_\fP` (acts as $`N\fp`-power on
$`\Ocirc_L/\fP`) combined with the fact that $`\zeta_m` lifts
isomorphically from the residue field for $`\fp\nmid m`.
:::

:::lemma_ "log-artin-asymp-character-sum" (lean := "Chebotarev.log_artinLSeries_asymp_character_sum")

For every character $`\chi` of $`G`, the partial sum
$`\sum_\fp \chi(\Frob_\fp) N\fp^{-s}` over $`\fp` unramified in $`L` is
bounded by $`C\log(1/(s-1)) + C` for some constant $`C`, in a right
neighbourhood of $`s = 1`.

{uses "dedekind-zeta-factorisation"}[]
{uses "frobenius-class"}[]
:::

:::proof "log-artin-asymp-character-sum"

Expand $`\log L(\chi, s)` via the Euler product
{bpref "artin-euler-product-abelian"}[]; the higher-power tail is
bounded analogously to {bpref "prime-zeta-higher-tail-bounded"}[].
:::

:::lemma_ "character-orthogonality-eq" (lean := "Chebotarev.character_orthogonality_cyclotomic_eq")

Let $`L = K(\zeta_m)`, $`\sigma \in G`, and $`\fp` a nonzero prime of
$`\OK` unramified in $`L` with $`\sigma_\fp` the conjugacy class of
$`\sigma`. Then
$$`
  \sum_{\chi\in\widehat G} \chi(\sigma)\chi(\Frob_\fp)^{-1}
  \;=\; \abs{G}.
`

{uses "galois-character"}[]
{uses "frobenius-class"}[]
:::

:::proof "character-orthogonality-eq"

Since $`G` is abelian, each character is multiplicative and
$`\chi(\sigma)\chi(\Frob_\fp)^{-1} = \chi(\sigma\Frob_\fp^{-1})`, so the
sum is $`\sum_{\chi\in\widehat G}\chi(g)` with $`g = \sigma\Frob_\fp^{-1}`.
The hypothesis $`\sigma_\fp = [\sigma]` means $`\Frob_\fp` is conjugate
to $`\sigma`, hence (in the abelian group) equal to $`\sigma`, so
$`g = 1` and every summand is $`\chi(1) = 1`; the sum is $`\abs{\widehat
G} = \abs{G}`. The supporting orthogonality fact — $`\sum_\chi \chi(g)`
equals $`\abs{G}` if $`g = 1` and $`0` otherwise — is the standard
finite-abelian relation: for $`g\ne 1` pick a separating character
$`\chi_0` with $`\chi_0(g)\ne 1`; reindexing the sum by the translation
$`\chi\mapsto\chi_0\chi` multiplies it by $`\chi_0(g)`, forcing it to
vanish.

:::

:::lemma_ "character-orthogonality-ne" (lean := "Chebotarev.character_orthogonality_cyclotomic_ne")

Let $`L = K(\zeta_m)`, $`\sigma \in G`, and $`\fp` a nonzero prime of
$`\OK` unramified in $`L` whose Frobenius class is not the conjugacy
class of $`\sigma`. Then
$$`
  \sum_{\chi\in\widehat G} \chi(\sigma)\chi(\Frob_\fp)^{-1} \;=\; 0.
`

{uses "galois-character"}[]
{uses "frobenius-class"}[]
:::

:::proof "character-orthogonality-ne"

Standard finite-group character orthogonality for the dual of $`G`
(Sharifi 7.2.1 step at p.~142). Under the isomorphism
$`G\cong(\Z/m\Z)^\times` from {bpref "cyclotomic-frobenius-norm-power"}[],
$`\chi(\Frob_\fp)` depends only on $`N\fp\bmod m`, and the sum reduces to
the orthogonality relation on the cyclic group $`(\Z/m\Z)^\times`.
:::

:::lemma_ "primesum-fibre-asymp" (lean := "Chebotarev.primeIdealZetaSum_frobeniusFibre_asymp")

Let $`L = K(\zeta_m)` and $`\sigma \in G`. The Frobenius-fibre prime sum
is asymptotic to $`(1/\abs{G})\log(1/(s-1))`:
$$`
  \lim_{s\downarrow 1}
  \frac{\sum_{\fp:\,\sigma_\fp = \sigma} N\fp^{-s}}{\log(1/(s-1))}
  \;=\; \frac{1}{\abs{G}}.
`

{uses "log-artin-asymp-character-sum"}[]
{uses "character-orthogonality-eq"}[]
{uses "character-orthogonality-ne"}[]
{uses "artin-one-ne-zero"}[]
:::

:::proof "primesum-fibre-asymp"

Multiply $`\log L(\chi, s)` by $`\chi(\sigma)^{-1}` and sum over $`\chi`:
the orthogonality relations
({bpref "character-orthogonality-eq"}[], {bpref "character-orthogonality-ne"}[])
pick out the primes with Frobenius $`\sigma`, giving
$`\sum_\chi \chi(\sigma)^{-1}\log L(\chi, s) \sim
\abs{G}\sum_{\sigma_\fp=\sigma} N\fp^{-s}`; on the other hand it
$`\sim \log\zeta_K(s) \sim \log(1/(s-1))` (only $`\chi=1` contributes a
pole, by {bpref "artin-one-ne-zero"}[]). Divide.

{uses "character-orthogonality-eq"}[]
{uses "character-orthogonality-ne"}[]
{uses "artin-one-ne-zero"}[]
:::

:::lemma_ "ratio-glue-numerator" (lean := "Chebotarev.tendsto_ratio_of_log_asymp_numerator")

If $`\mathrm{num}(s)/\log(1/(s-1)) \to c` and
$`\mathrm{den}(s)/\log(1/(s-1)) \to 1` as $`s\downarrow 1`, then
$`\mathrm{num}(s)/\mathrm{den}(s) \to c`.
:::

:::proof "ratio-glue-numerator"

Write $`\mathrm{num}/\mathrm{den} = (\mathrm{num}/L)/(\mathrm{den}/L)`
with $`L = \log(1/(s-1))`, which is positive (hence nonzero) for
$`s\in(1,2)` since $`1/(s-1) > 1`; apply the quotient rule for limits
and cancel $`L`.
:::

:::lemma_ "cyclotomic-density-two-sided" (lean := "Chebotarev.cyclotomic_density_from_two_sided_asymp")

Let $`L = K(\zeta_m)` and $`\sigma \in G`. Then
$$`
  \lim_{s\downarrow 1}
  \frac{\sum_{\fp:\,\sigma_\fp = \sigma} N\fp^{-s}}
       {\sum_\fp N\fp^{-s}}
  \;=\; \frac{1}{\abs{G}}.
`

{uses "primesum-fibre-asymp"}[]
{uses "prime-ideal-sum-log"}[]
{uses "ratio-glue-numerator"}[]
:::

:::proof "cyclotomic-density-two-sided"

The numerator asymptotic {bpref "primesum-fibre-asymp"}[]
($`\mathrm{num}\sim(1/\abs{G})\log(1/(s-1))`) and the denominator
asymptotic {bpref "prime-ideal-sum-log"}[]
($`\mathrm{den}\sim\log(1/(s-1))`) feed the ratio glue
{bpref "ratio-glue-numerator"}[].

{uses "primesum-fibre-asymp"}[]
{uses "prime-ideal-sum-log"}[]
{uses "ratio-glue-numerator"}[]
:::

:::theorem "chebotarev-cyclotomic" (lean := "Chebotarev.chebotarev_cyclotomic")

For $`K` a number field, $`m\ge 1`, $`L=K(\zeta_m)`, and every
$`\sigma \in G = \Gal{L/K}`,
$$`
  \delta\bigl(\setof{\fp\subset\OK}{\sigma_\fp = \sigma}\bigr)
  \;=\; \frac{1}{\abs{G}}.
`

{uses "dirichlet-density"}[]
{uses "frobenius-class"}[]
{uses "cyclotomic-density-two-sided"}[]
:::

:::proof "chebotarev-cyclotomic"

Fix $`\sigma\in G`. By character orthogonality over
$`\widehat G = \widehat{\Gal{K(\zeta_m)/K}}`
({bpref "character-orthogonality-eq"}[] in the matching case,
{bpref "character-orthogonality-ne"}[] otherwise), the indicator of the
condition $`\sigma_\fp = \sigma` is the character average
$`\frac{1}{\abs{G}}\sum_{\chi}\chi(\sigma)\chi(\Frob_\fp)^{-1}`. Summing
against $`N\fp^{-s}` turns the Frobenius-fibre prime sum into
$$`
  \sum_{\sigma_\fp = \sigma} N\fp^{-s}
  \;=\; \frac{1}{\abs{G}}\sum_{\chi\in\widehat G}\chi(\sigma)^{-1}
        \sum_\fp \chi(\Frob_\fp)\,N\fp^{-s},
`
and each inner sum is, up to a bounded error, $`\log L(\chi, s)`
{uses "artin-euler-product-abelian"}[]. For $`\chi\ne\mathbf{1}` the
$`L`-function extends analytically across $`s=1`
({bpref "artin-analytic-extension"}[]) and is non-vanishing there
({bpref "artin-one-ne-zero"}[]){uses "artin-one-ne-zero"}[], so
$`\log L(\chi, s)` stays bounded as $`s\downarrow 1`; only the trivial
character $`\chi=\mathbf{1}`, whose $`L`-function is $`\zeta_K`, carries
the pole $`\log L(\mathbf{1}, s)\sim\log\frac{1}{s-1}`. Hence the fibre
sum is asymptotic to $`\frac{1}{\abs{G}}\log\frac{1}{s-1}`
({bpref "primesum-fibre-asymp"}[]). Dividing by the universal sum
$`\sum_\fp N\fp^{-s}\sim\log\frac{1}{s-1}` ({bpref "prime-ideal-sum-log"}[])
gives the Dirichlet density $`1/\abs{G}`
({bpref "cyclotomic-density-two-sided"}[]).

:::
