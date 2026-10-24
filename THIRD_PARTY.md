# Third-party source provenance

The three files in `ChromaticPolynomial/` are adapted from
[anlucia/ChromaticPolynomial](https://github.com/anlucia/ChromaticPolynomial), commit
[`6fe1fcdab3684ad78cbdf08d1124b4f0fdac7a8b`](https://github.com/anlucia/ChromaticPolynomial/commit/6fe1fcdab3684ad78cbdf08d1124b4f0fdac7a8b)
(2024-08-25; author in Git history: Angelo Lucia). Upstream is licensed under Apache-2.0;
its license text is preserved in this repository's `LICENSE` (identical upstream blob
`261eeb9e9f8b2b4b0d119366dda99c6fd7d35c64`). Upstream contains no separate NOTICE file.

The inherited contribution is the edge-subset chromatic polynomial and the proof that
positive integer evaluations count proper colorings, together with spanning-subgraph and
connected-component helpers. These contributions are reused, not claimed as new proofs
by this project. Each adapted module retains a source-and-license header.

Porting changes include Lean's current module/export syntax, renamed or split Mathlib
imports and lemmas, explicit finite connected-component instances, current quotient
elimination, finite-set coercions and product lemmas, and local removal of unused
section assumptions. Aggregate `import Mathlib` imports are replaced with specific
dependencies. The argument for the positive evaluation theorem is retained.

All modules under `Stanley/`, the independent Challenge, and the verification packaging
are new work for this project. They add the source inclusion–exclusion identity, acyclic
orientation splitting and reindexing, palette convolution, the −1 identity, and the full
compatible-coloring reciprocity proof. New source headers use the project author's
copyright and Apache-2.0 license.
