import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Decomposition, inertia, Frobenius" =>

tex_prelude r#"\newcommand{\Z}{\mathbb{Z}}\newcommand{\Q}{\mathbb{Q}}\newcommand{\R}{\mathbb{R}}\newcommand{\C}{\mathbb{C}}\newcommand{\N}{\mathbb{N}}\newcommand{\F}{\mathbb{F}}\newcommand{\OK}{\mathcal{O}_K}\newcommand{\Ocirc}{\mathcal{O}}\newcommand{\Gal}[1]{\mathrm{Gal}(#1)}\newcommand{\Norm}[1]{\mathrm{N}(#1)}\newcommand{\fp}{\mathfrak{p}}\newcommand{\fP}{\mathfrak{P}}\newcommand{\Frob}{\mathrm{Frob}}\renewcommand{\Re}{\operatorname{Re}}\newcommand{\re}{\operatorname{Re}}\newcommand{\set}[1]{\left\{ #1 \right\}}\newcommand{\setof}[2]{\left\{ #1 \;\middle|\; #2 \right\}}\newcommand{\abs}[1]{\left\lvert #1 \right\rvert}\newcommand{\norm}[1]{\left\lVert #1 \right\rVert}\newcommand{\ang}[1]{\left\langle #1 \right\rangle}"#

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

:::definition "decomposition-group" (lean := "Chebotarev.decompositionGroup")

For a prime $`\fP` of $`\Ocirc_L`, the *decomposition group* at
$`\fP` is
$$`
  D_\fP \;=\; \set{\sigma\in G : \sigma(\fP)=\fP}
  \;=\; \mathrm{Stab}_G(\fP).
`

:::

:::definition "inertia-group" (lean := "Chebotarev.inertiaGroup")

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

:::definition "frobenius-at" (lean := "Chebotarev.frobeniusAt")

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

:::lemma "exists-frobenius-class" (lean := "Chebotarev.exists_frobeniusClass")

For a nonzero prime $`\fp` of $`\OK` unramified in $`L`, there exists a
conjugacy class $`C \subseteq \Gal{L/K}` such that for every prime
$`\fP` of $`\Ocirc_L` above $`\fp`, $`C = [\Frob_\fP]`. (Equivalently, the
Frobenius elements above $`\fp` are all conjugate.)

{uses "frobenius-at"}[]
:::

:::lemma "frobenius-class-eq-mk" (lean := "Chebotarev.frobeniusClass_eq_mk_frobeniusAt")

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

:::lemma "finite-ramified-primes" (lean := "Chebotarev.finite_ramifiedIn")

Only finitely many nonzero primes of $`\OK` ramify in $`L`.

{uses "unramified-in"}[]
:::

:::proof "finite-ramified-primes"

The primes ramifying in $`L` are exactly the divisors of the relative
different ideal $`\mathfrak{d}_{L/K}\subseteq\Ocirc_L`, which has a
finite prime factorisation in the Dedekind domain $`\Ocirc_L`.

:::
