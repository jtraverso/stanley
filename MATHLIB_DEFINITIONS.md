# Mathlib definitions used by the independent Challenge

The custom definitions are explicitly repeated in `Challenge.lean`. The following
verbatim excerpts document imported notions at Mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e` (Apache-2.0). Line numbers refer to that
revision. Lean primitive types, propositions, functions, and natural/integer arithmetic
have their usual meanings. Counts and theorems are restricted to finite vertex types.

## Mathlib/Combinatorics/SimpleGraph/Basic.lean:95

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Combinatorics/SimpleGraph/Basic.lean#L95)

```lean
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Std.Symm Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph

```

## Mathlib/Combinatorics/SimpleGraph/Basic.lean:647

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Combinatorics/SimpleGraph/Basic.lean#L647)

```lean
def fromEdgeSet : SimpleGraph V where
  Adj := Sym2.ToRel s ⊓ Ne
  symm.symm u v h := ⟨Sym2.toRel_symm s |>.symm u v h.left, h.right.symm⟩

```

## Mathlib/Combinatorics/SimpleGraph/Basic.lean:483

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Combinatorics/SimpleGraph/Basic.lean#L483)

```lean
abbrev edgeSet (G : SimpleGraph V) : Set (Sym2 V) := edgeSetEmbedding V G
```

## Mathlib/Combinatorics/SimpleGraph/Maps.lean:227

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Combinatorics/SimpleGraph/Maps.lean#L227)

```lean
abbrev induce (s : Set V) (G : SimpleGraph V) : SimpleGraph s :=
  G.comap (Function.Embedding.subtype _)

variable {G} in
lemma induce_adj {s : Set V} {u v : s} : (G.induce s).Adj u v ↔ G.Adj u v := .rfl
```

## Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean:52

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean#L52)

```lean
def Reachable (u v : V) : Prop := Nonempty (G.Walk u v)

```

## Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean:390

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean#L390)

```lean
def ConnectedComponent := Quot G.Reachable

/-- Gives the connected component containing a particular vertex. -/
def connectedComponentMk (v : V) : G.ConnectedComponent := Quot.mk G.Reachable v

```

## Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean:74

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean#L74)

```lean
abbrev Coloring (α : Type v) := G →g completeGraph α
```

## Mathlib/SetTheory/Cardinal/Finite.lean:39

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/SetTheory/Cardinal/Finite.lean#L39)

```lean
/-- `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`. -/
protected def card (α : Type*) : ℕ :=
  toNat (mk α)
```

## Mathlib/Data/Fintype/Card.lean:38

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Data/Fintype/Card.lean#L38)

```lean

/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [Fintype α] : ℕ :=
  (@univ α _).card

```

## Mathlib/Algebra/Polynomial/Basic.lean:73

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Algebra/Polynomial/Basic.lean#L73)

```lean
structure Polynomial (R : Type*) [Semiring R] where ofFinsupp ::
  /-- The coefficients `ℕ →₀ R` of a polynomial in `R[X]`. -/
  toFinsupp : AddMonoidAlgebra R ℕ

@[inherit_doc] scoped[Polynomial] notation:9000 R "[X]" => Polynomial R
```

## Mathlib/Algebra/Polynomial/Eval/Defs.lean:250

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Algebra/Polynomial/Eval/Defs.lean#L250)

```lean
def eval (x : R) (p : R[X]) : R :=
  eval₂ (RingHom.id _) x p
```

## Mathlib/Algebra/BigOperators/Finprod.lean:100

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Algebra/BigOperators/Finprod.lean#L100)

```lean
noncomputable irreducible_def finsum (lemma := finsum_def') [AddCommMonoid M] (f : α → M) : M :=
  if h : HasFiniteSupport (f ∘ PLift.down) then ∑ i ∈ h.toFinset, f i.down else 0
```

## Lean well-foundedness

Lean `v4.35.0-rc3`, `Init/WF.lean`:60 (Lean community license).

```lean
inductive WellFounded {α : Sort u} (r : α → α → Prop) : Prop where
  /--
  If all elements are accessible via `r`, then `r` is well-founded.
  -/
  | intro (h : ∀ a, Acc r a) : WellFounded r
```

`WellFounded r` means every element is accessible under predecessors for r.
`Relation.TransGen r` is the transitive closure through one or more r-steps; hence
`TransGen r v v` expresses a directed cycle. The equivalence with well-foundedness on
finite types is a selected proved theorem, not an additional hypothesis.

`G →g H` denotes an adjacency-preserving graph homomorphism. `completeGraph α`
has an edge precisely between distinct vertices, so `G.Coloring α` has the standard
meaning of a proper coloring. `Sym2 V` is the type of unordered pairs of vertices.
`edgeSet` contains those pairs whose endpoints are adjacent.
