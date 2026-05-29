# CLAUDE.md

Context for Claude Code (claude.ai/code) working in this repo.

## What this is

Lean 4 / Mathlib formalisation of **Chebotarev's density theorem** in
conjugacy-class form for a finite Galois extension of number fields.

The target statement (in `Chebotarev/Main.lean`):

```
For L/K a finite Galois extension of number fields with G = Gal(L/K),
and for any conjugacy class C ⊆ G,
  δ({𝔭 ⊂ 𝓞_K : σ_𝔭 = C}) = |C| / |G|.
```

All theorem proofs are currently `sorry`. All definitions have real
content (`MulAction.stabilizer`, `Ideal.inertia`, `Classical.choose` of
existence theorems) — there are **no placeholder `def := sorry`**.

## Proof structure

Three reductions following Sharifi §7.2 / Stevenhagen–Lenstra appendix:

1. **General → cyclic via fixed-field subextension** (`Main.lean`).
   For `σ ∈ C`, set `E = L^⟨σ⟩`. Then `L/E` is cyclic of degree
   `f = ord(σ)`. A counting argument (Sharifi 7.2.2 Step 1, p. 143)
   gives `δ_K(S) = (f|C|/|G|) · δ_E(T_σ)`. Combine with step 2.

2. **Cyclic / abelian → cyclotomic via compositum trick**
   (`Abelian.lean`). For `m` coprime to `disc(L)`,
   `Gal(L(μ_m)/K) ≅ G × H` with `H = Gal(K(μ_m)/K)`. For
   `n | ord(τ)`, the cyclic subgroup `⟨(σ,τ)⟩` meets `G × {1}`
   trivially, so the fixed-field extension is cyclotomic. Density at
   each `(σ,τ)` is `1/(|G|·|H|)` (Sharifi 7.2.2 Step 2, pp. 143–144).
   Sum over admissible `τ`, take `m ≡ 1 mod n^k → ∞`, recover
   `1/|G|`.

3. **Cyclotomic** (`Cyclotomic.lean`). `ζ_L = ∏_χ L(χ,·)`
   (`ZetaProduct.lean`) + log-asymptotic + character orthogonality
   yield density `1/|G|` directly. The substantive analytic input is
   non-vanishing `L(χ, 1) ≠ 0` for nontrivial `χ` (Sharifi 7.1.19).

## File layout

| File | Role |
|---|---|
| `Chebotarev/Density.lean` | Dirichlet density definition + asymptotic for `Σ_𝔭 N𝔭^{-s}` |
| `Chebotarev/Frobenius.lean` | Decomposition / inertia / Frobenius element / Frobenius conjugacy class |
| `Chebotarev/ZetaProduct.lean` | `ζ_L = ∏_χ L(χ,·)` factorisation for abelian L/K + non-vanishing |
| `Chebotarev/Cyclotomic.lean` | Chebotarev cyclotomic case (Sharifi 7.2.1) |
| `Chebotarev/Abelian.lean` | Chebotarev abelian case via cyclotomic crossing (Sharifi 7.2.2 Step 2) |
| `Chebotarev/Main.lean` | Main theorem + corollaries (Dirichlet AP, splitting density) |
| `Chebotarev/NumberFieldEulerProduct.lean` | Generic `ζ_K = ∏(1-N𝔭^{-s})^{-1}` Euler-product infrastructure |
| `Chebotarev.lean` | Umbrella module |

## References

Included as PDFs in `docs/`:

- **Sharifi**, *Algebraic Number Theory* §7.1–7.2 (`docs/algnum.pdf`).
- **Stevenhagen–Lenstra**, *Chebotarëv and his density theorem*,
  Appendix (`docs/cheb.pdf`).

Pages 138–144 of Sharifi are the primary substrate; the appendix of
Stevenhagen–Lenstra (p. 18) gives the same proof with slightly
different framing.

## Sub-lemmas vs top-level theorems

Each top-level theorem (`exists_unique_frobeniusAt`,
`primeIdealZetaSum_univ_tendsto_log`,
`exists_dedekindZeta_factorisation`, `chebotarev_cyclotomic`,
`chebotarev_abelian`, `chebotarev_density`) is decomposed into
sub-lemmas that mirror Sharifi's proof structure. The sub-lemmas are
stated in the same file as their parent, prefixed by a docstring
`### Sub-lemmas for ...` block with verbatim source quotes.

When discharging a `sorry`, prefer composing the existing sub-lemmas
rather than re-deriving from scratch — the decomposition was done in
`/develop --decompose` mode against the references; each leaf was
chosen because the source itself proves it explicitly.

## Build

```
lake exe cache get        # fetch mathlib build artefacts
lake build                # build the whole project
lake build Chebotarev.Main   # build a single module
```

The toolchain is pinned to mathlib master via `lean-toolchain` and
`lakefile.toml` (mathlib `rev = "master"`). `lake update` bumps mathlib
+ aligns the toolchain.

`lakefile.toml` enables strict mathlib options: `autoImplicit = false`,
`relaxedAutoImplicit = false`, `linter.mathlibStandardSet`,
`linter.flexible`, `maxSynthPendingDepth = 3`. Expect linter warnings
if these are ignored.

## Blueprint

LaTeX-source blueprint under `blueprint/src/`:

- One chapter per file under `subsections/`: `density.tex`,
  `frobenius.tex`, `zeta-product.tex`, `cyclotomic.tex`,
  `abelian.tex`, `main.tex`.
- `content.tex` ties the chapters together with the proof outline.
- Common macros in `macros/common.tex`. Project notation:
  `\fp = 𝔭`, `\fP = 𝔓`, `\Frob = Frob`, `\OK = 𝓞_K`,
  `\Gal{L/K} = Gal(L/K)`.

Every blueprint entry uses `\lean{Chebotarev.<name>}` to link the
prose statement to its Lean declaration. `\uses{...}` tracks
dependencies for the dep-graph.

Build:

```
leanblueprint pdf          # → blueprint/print/print.pdf
leanblueprint web          # → blueprint/web/
leanblueprint checkdecls   # verify Lean refs in blueprint
```

CI deploys to GitHub Pages at https://cbirkbeck.github.io/chebotarev-density/

## Conventions

- **Namespace**: everything sits in `namespace Chebotarev`. Don't
  introduce sub-namespaces unless there's a clear sub-topic.
- **Argument convention**: `K L` (number fields) are **explicit
  positional** arguments in every definition and theorem. Don't
  switch to implicit `{K L}` — the helper `variable (K L : Type*) …`
  block from earlier projects doesn't always propagate cleanly here.
- **No placeholder `def := sorry`**. Real definitions only. The user
  is allergic to scaffolding. Either use mathlib's API directly
  (`MulAction.stabilizer`, `Ideal.inertia`), inline the formula, or
  reach for `Classical.choose` of an existence theorem (where the
  existence theorem is itself a real proposition that can be
  sorried).
- **Source quotes are binding**. When stating a new sub-lemma, the
  docstring should quote Sharifi or Stevenhagen–Lenstra verbatim (in
  English) and cite the page. If the cited passage doesn't match the
  Lean statement, the Lean statement is wrong — fix it before
  proceeding.
- **No CFT**. The proof deliberately sidesteps class field theory.
  The cyclotomic case is via Dirichlet's argument; the abelian case
  via Chebotarev's compositum trick; the general case via fixed-field
  reduction to cyclic. Do not introduce Artin reciprocity, idele class
  groups, or Hilbert class fields — the user picked this path
  specifically.
- **Generality**: prefer the most general typeclass that works.
  Number fields are universe-polymorphic `(K : Type*)`.

## What this proof does NOT need

- **Artin L-functions for non-abelian Galois groups**. The reduction
  through fixed-field subextensions keeps us in the abelian regime
  for L-function arguments; only abelian L(χ,·) is needed.
- **Class field theory**. Same reason.
- **Effective bounds / natural density**. Only Dirichlet (analytic)
  density is treated.
- **Functional equation of L(χ,·)**. Only non-vanishing at `s = 1`
  (Sharifi 7.1.19) is used.

## Provenance

Originally developed in
[`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli)
under `BernoulliRegular/Chebotarev/`. Spun out to a standalone repo
on 2026-05-28 to keep Chebotarev as a general-purpose theorem
independent of the Kummer-criterion / FLT37 narrative of the parent
project.

## When working on this repo

- Read the relevant Sharifi pages BEFORE attempting a sorry. Pages
  138–144 cover everything.
- Sub-lemmas under each top-level theorem are not optional steps to
  skip — they ARE the proof structure.
- When `lake build` fails with a Lean-elaboration error, the issue
  is almost always missing imports or namespace resolution; check
  these first before redesigning the statement.
- After a successful proof, re-run `lake build BernoulliRegular.Main`
  on the parent `flt-regular-bernoulli` repo IS NOT NEEDED — the two
  repos are fully independent. (No shared code; no cross-imports.)
