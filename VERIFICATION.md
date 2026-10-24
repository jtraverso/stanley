# Verification record

The local project uses Lean v4.35.0-rc3 and Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`.

- Strict Solution build: `lake build --wfail`.
- Axiom and boundary-case audit: `lake build Audit --wfail`.
- Independent statements: `lake build Challenge`; five intentional placeholder warnings.
- Sandboxed theorem/definition comparison and kernel checking:
  `lake comparator --config comparator.json`.

The five selected results and four selected definitions pass Comparator. Both the NanoDa
kernel and Lean's default kernel accept the solution. The axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound` for every selected theorem. The successful
local logs are saved in `verification/`.

The canonical polynomial is defined from edge subsets and connected-component counts,
without reference to orientations. Comparator also checks its definition, the orientation
predicate, and the two count definitions against the independent Challenge. CompatiblePair
and all other custom definitions are explicitly repeated in that module. Definitions
contain no placeholders, and proof modules import no Challenge declarations.

Boundary cases cover the empty graph with zero colors, a nonempty vertex set with zero
colors, and K₂. For K₂, an independent count of proper colorings via injective maps proves
χ(X) = X(X − 1), which yields two acyclic orientations and six compatible pairs with two
colors. The finite equivalence between well-foundedness and absence of directed cycles
and the paper's reversed-color convention are proved in the library.

The GitHub workflows are prepared to run strict compilation and the official full
Palomar mechanical pipeline pinned at `c02bbeaed888df45c4e28c4e99dba540ad21552a`, using
`palomar-standard-v1`. A prepared workflow is not a completed remote check; consult its
run result for publication evidence. Mechanical preflight is not registry submission,
acceptance, or independent human review.
