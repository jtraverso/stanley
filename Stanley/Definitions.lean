/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.BigOperators.Finprod

@[expose] public section

namespace Stanley

open SimpleGraph Polynomial

variable {V : Type*} (G : SimpleGraph V)

/-- Whitney's edge-subset formula. The finitely supported sum is an ordinary finite sum
when V is finite. All spanning subgraphs retain every vertex, including isolated ones. -/
noncomputable def chromaticPolynomial : ℤ[X] :=
  ∑ᶠ F : {F : Set (Sym2 V) // F ⊆ G.edgeSet},
    (-1 : ℤ[X]) ^ Nat.card F.val * X ^ Nat.card (fromEdgeSet F.val).ConnectedComponent

/-- Each edge receives a direction. On finite vertex sets, well-foundedness is exactly
the absence of directed cycles. -/
def IsAcyclicOrientation (r : V → V → Prop) : Prop :=
  (∀ u v, r u v → G.Adj u v) ∧
  (∀ u v, G.Adj u v → r u v ∨ r v u) ∧ WellFounded r

abbrev AcyclicOrientation := {r : V → V → Prop // IsAcyclicOrientation G r}

noncomputable def orientationCount : ℤ := Nat.card (AcyclicOrientation G)

/-- An acyclic orientation paired with a weakly increasing coloring along each arc. -/
@[ext] structure CompatiblePair (k : ℕ) where
  orientation : AcyclicOrientation G
  color : V → Fin k
  compatible : ∀ u v, orientation.val u v → color u ≤ color v

noncomputable def compatibleCount (k : ℕ) : ℤ := Nat.card (CompatiblePair G k)

end Stanley
