# Stanley: acyclic orientations and chromatic reciprocity

Lean 4 formalizations of **Theorem 1.2 and Corollary 1.3** of Richard P. Stanley,
*Acyclic orientations of graphs*, Discrete Mathematics 5 (1973), 171–178,
[doi:10.1016/0012-365X(73)90108-8](https://doi.org/10.1016/0012-365X(73)90108-8).
The [author-hosted reprint](https://math.mit.edu/~rstan/pubs/pubfiles/18.pdf) was consulted
for the statements and numbering.

For every finite simple graph G on n vertices and every natural number k:

\[
(-1)^n\chi_G(-k)=\#\{(D,c):D\text{ is an acyclic orientation of }G,
\ c:V(G)\to\{0,\ldots,k-1\},\ u\to v\Rightarrow c(u)\le c(v)\}.
\]

In particular, **\((-1)^n\chi_G(-1)\) is the number of acyclic orientations**. Empty
vertex sets and k = 0 are included. Compatibility is weak monotonicity; these colorings
can assign the same color to adjacent vertices.

## Precise definitions and selected statements

`Stanley/Definitions.lean` defines the chromatic polynomial by Whitney's edge-subset
formula, over the integers. Every edge subset gives a spanning graph on the entire
vertex type, so isolated vertices are retained. The notation `∑ᶠ` denotes a finitely
supported sum; on the finite vertex types used in the theorems it is an ordinary finite
sum. The polynomial is defined independently of orientations and their counts.

An orientation is a binary relation choosing a direction for each edge, with
well-foundedness excluding directed cycles. The finite equivalence with the usual
no-directed-cycle condition is itself proved. `CompatiblePair` consists of an orientation,
a map into `Fin k`, and the weak monotonicity condition. Counts use `Nat.card`, cast to ℤ.

| Selected theorem in namespace `Stanley` | Meaning |
| --- | --- |
| `eval_card` | Positive evaluations count Mathlib proper colorings with any finite palette |
| `convolution` | Splitting a palette gives the induced-subgraph convolution identity |
| `compatible_count_eq` | Stanley, Theorem 1.2: chromatic reciprocity for every k ≥ 0 |
| `acyclic_count_eq` | Stanley, Corollary 1.3: the evaluation at −1 counts acyclic orientations |
| `wellFounded_iff_no_cycle` | Well-foundedness is equivalent to absence of directed cycles on finite types |

The paper uses colors 1 through k and weakly decreasing colors along arcs. We use
`Fin k` and increasing colors. `CompatiblePair.paperConventionEquiv` proves that reversing
the finite palette converts the conventions while keeping the orientation.

This covers the two stated results and their infrastructure. The paper's later results
on enumerating labeled digraphs and constructing a binomial algebra are outside this scope.

## Proof and reused infrastructure

The positive evaluation theorem is ported from Angelo Lucia's Apache-2.0
[ChromaticPolynomial](https://github.com/anlucia/ChromaticPolynomial) at commit
`6fe1fcdab3684ad78cbdf08d1124b4f0fdac7a8b`; see [THIRD_PARTY.md](THIRD_PARTY.md).
An explicit isomorphism bridges its spanning-subgraph presentation to our edge-subset
definition. We use the existing Mathlib graph, coloring, connected-component, polynomial,
finite-counting, and well-founded-relation infrastructure.

The new argument first counts acyclic orientations using inclusion–exclusion on their
nonempty set of sources. Splitting a palette establishes chromatic convolution, initially
at nonnegative integers and then at all integers by polynomial extensionality. Induction
on the number of vertices gives the evaluation at −1. Finally, splitting a compatible
pair into its zero-colored vertices and the remaining vertices gives a recurrence;
induction on k and convolution yield full reciprocity. This is a different proof route
from the paper's deletion–contraction argument.

## Verification and reproducibility

Pinned toolchain: Lean `v4.35.0-rc3`; Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`. Run:

```sh
./scripts/check.sh
```

The script runs strict compilation, the axiom/boundary audit, the independent Challenge,
and sandboxed Comparator with both Lean and NanoDa enabled. Comparator checks five
theorem types and four explicit definitions. `Challenge.lean` imports only Mathlib and
repeats the definitions; its five theorem placeholders are intentional. There are no
placeholders in definitions, Solution, or proof modules and no custom axioms. The only
permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

`Audit.lean` independently obtains χ(K₂, X) = X(X − 1) by counting embeddings, then
checks its two acyclic orientations and its six compatible pairs with two colors.
It also checks empty and zero-color cases. See [VERIFICATION.md](VERIFICATION.md) and
[formalization.yaml](formalization.yaml).

Author and responsible maintainer: Juan Pablo Traverso Gianini. Adapted code is credited
to Angelo Lucia. New proofs and packaging were produced with OpenAI Codex and mechanically
verified. No independent human mathematical review or mathematical novelty is claimed.
License: Apache-2.0. Mechanical preflight and registry registration are separate steps.
