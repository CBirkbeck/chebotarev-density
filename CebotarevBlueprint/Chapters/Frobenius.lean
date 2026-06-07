import Verso
import VersoManual
import VersoBlueprint
import CebotarevDensity
import CebotarevBlueprint.Refs

open Verso.Genre
open Verso.Genre.Manual
open Informal

tex_prelude r#"\def\Z{\mathbb{Z}}\def\Q{\mathbb{Q}}\def\R{\mathbb{R}}\def\C{\mathbb{C}}\def\N{\mathbb{N}}\def\F{\mathbb{F}}\def\OK{\mathcal{O}_K}\def\Ocirc{\mathcal{O}}\def\Gal#1{\mathrm{Gal}(#1)}\def\Norm#1{\mathrm{N}(#1)}\def\fp{\mathfrak{p}}\def\fP{\mathfrak{P}}\def\Frob{\mathrm{Frob}}\def\Re{\operatorname{Re}}\def\re{\operatorname{Re}}\def\set#1{\left\{#1\right\}}\def\setof#1#2{\left\{#1\;\middle|\;#2\right\}}\def\abs#1{\left\lvert#1\right\rvert}\def\norm#1{\left\lVert#1\right\rVert}\def\ang#1{\left\langle#1\right\rangle}"#

#doc (Manual) "Decomposition, inertia, Frobenius" =>

Let $`L/K` be a finite Galois extension of number fields with
$`G=\Gal{L/K}`. The Galois group acts on ideals of $`\Ocirc_L` (via the
canonical $`G`-action restricted to $`\Ocirc_L` and extended
multiplicatively), and in particular permutes the primes lying above
a given prime $`\fp` of $`\OK`.

:::definition "unramified-in" (lean := "Chebotarev.UnramifiedIn")

A nonzero prime ideal $`\fp` of $`\OK` is *unramified in $`L`* if
every prime $`\fP` of $`\Ocirc_L` lying over $`\fp` has ramification
index $`1`, i.e. $`\fp\Ocirc_L` factors into distinct primes.

:::

:::definition "decomposition-group" (lean := "MulAction.stabilizer")

For a prime $`\fP` of $`\Ocirc_L`, the *decomposition group* at
$`\fP` is
$$`
  D_\fP \;=\; \set{\sigma\in G : \sigma(\fP)=\fP}
  \;=\; \mathrm{Stab}_G(\fP).
`

:::

:::definition "inertia-group" (lean := "Ideal.inertia")

The *inertia group* at $`\fP` is
$$`
  I_\fP \;=\;
  \setof{\sigma\in G}{\forall x\in\Ocirc_L,\;\sigma(x)\equiv x\pmod\fP}.
`
This is the generic ideal-inertia subgroup `Ideal.inertia`
from mathlib, instantiated at the natural action of $`G` on $`\Ocirc_L`;
acting trivially mod~$`\fP` forces stabilising $`\fP`, so $`I_\fP` sits
inside $`D_\fP`, and is the kernel of the action of $`D_\fP` on the
residue field $`\Ocirc_L/\fP`.

{uses "decomposition-group"}[]
:::

When $`\fP` is unramified the inertia group is trivial:
$`\abs{I_\fP}=e(\fP\mid\fp)=1`. Hence the surjection
$`D_\fP\to\Gal{(\Ocirc_L/\fP)/(\OK/\fp)}` (mathlib's
`IsFractionRing.stabilizerHom_surjective`) is an isomorphism, and the
residue Galois group of a finite-field extension is cyclic with distinguished
generator the absolute Frobenius $`x\mapsto x^{N\fp}`. So $`D_\fP` contains a
unique element acting as $`x\mapsto x^{N\fp}` on $`\Ocirc_L/\fP`. In the
formalisation this existence and uniqueness is supplied directly by mathlib's
arithmetic-Frobenius API (`IsArithFrobAt.exists_of_isInvariant` for
existence, `IsArithFrobAt.mul_inv_mem_inertia` together with trivial
inertia for uniqueness), so it is not restated as a separate project result.

:::definition "frobenius-at" (lean := "IsArithFrobAt")

For an unramified nonzero prime $`\fP` of $`\Ocirc_L`, the
*Frobenius automorphism* $`\Frob_\fP\in G` is mathlib's
`arithFrobAt` for the action of $`G` on $`\Ocirc_L`: the unique
element of $`D_\fP` characterised by $`\Frob_\fP(x)\equiv x^{N\fp}\pmod\fP`
for all $`x\in\Ocirc_L`.

{uses "decomposition-group"}[]
{uses "unramified-in"}[]
:::

:::definition "frobenius-class" (lean := "Chebotarev.frobeniusClass")

For a nonzero prime $`\fp` of $`\OK` unramified in $`L`, the
*Frobenius conjugacy class* is
$$`
  \sigma_\fp \;=\; \set{\Frob_\fP : \fP\mid\fp}
  \;\in\; \mathrm{Conj}(G),
`
the conjugacy class in $`G` containing $`\Frob_\fP` for any (equivalently
every) prime $`\fP` of $`\Ocirc_L` above $`\fp`. The class is independent
of the choice of $`\fP`.

{uses "frobenius-at"}[]
:::

:::lemma_ "exists-frobenius-class" (lean := "Chebotarev.exists_frobeniusClass")

For a nonzero prime $`\fp` of $`\OK` unramified in $`L`, there exists a
conjugacy class $`C \subseteq \Gal{L/K}` such that for every prime
$`\fP` of $`\Ocirc_L` above $`\fp`, $`C = [\Frob_\fP]`. (Equivalently, the
Frobenius elements above $`\fp` are all conjugate.)

{uses "frobenius-at"}[]
:::

:::proof "exists-frobenius-class"

The Galois group $`G` acts transitively on the primes $`\fP` of
$`\Ocirc_L` above $`\fp`, so any two such primes are related by some
$`\sigma\in G`: $`\fP' = \sigma(\fP)`. Conjugation transports the
Frobenius: if $`\Frob_\fP` is a Frobenius at $`\fP` (an element of
$`D_\fP` {uses "decomposition-group"}[] acting as $`x\mapsto x^{N\fp}`
on the residue field), then $`\sigma\,\Frob_\fP\,\sigma^{-1}` is a
Frobenius at $`\sigma(\fP)`, since it lies in
$`D_{\sigma(\fP)} = \sigma D_\fP\sigma^{-1}` and induces the same
$`N\fp`-power map on $`\Ocirc_L/\sigma(\fP)`. Because $`\fp` is
unramified, the inertia at each $`\fP` is trivial, so the Frobenius
$`\Frob_\fP` {uses "frobenius-at"}[] is the *unique* element of $`D_\fP`
with this residue action; hence the Frobenius elements above $`\fp` form
a single $`G`-conjugacy class. Taking $`C = [\Frob_{\fP_0}]` for any
fixed $`\fP_0\mid\fp` gives the required class, independent of the
choice of $`\fP_0`.

:::

:::lemma_ "frobenius-class-eq-mk" (lean := "Chebotarev.frobeniusClass_eq_mk_of_isArithFrobAt")

For a nonzero prime $`\fp` of $`\OK` unramified in $`L`, and any prime
$`\fP` of $`\Ocirc_L` above $`\fp`,
$$`
  \sigma_\fp \;=\; [\Frob_\fP].
`

{uses "frobenius-class"}[]
{uses "frobenius-at"}[]
{uses "exists-frobenius-class"}[]
:::

:::proof "frobenius-class-eq-mk"

Unfold $`\sigma_\fp` at the unramified positive case to expose the
$`\mathrm{choose}` from {bpref "exists-frobenius-class"}[]{uses "exists-frobenius-class"}[]; the witness
property of $`\mathrm{choose\_spec}` at $`\fP` closes the goal.

:::

:::lemma_ "finite-ramified-primes" (lean := "Chebotarev.finite_ramifiedIn")

Only finitely many nonzero primes of $`\OK` ramify in $`L`.

{uses "unramified-in"}[]
:::

:::proof "finite-ramified-primes"

The primes ramifying in $`L` are exactly the divisors of the relative
different ideal $`\mathfrak{d}_{L/K}\subseteq\Ocirc_L`, which has a
finite prime factorisation in the Dedekind domain $`\Ocirc_L`.

:::
