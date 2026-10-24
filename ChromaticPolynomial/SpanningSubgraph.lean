/-
Adapted from anlucia/ChromaticPolynomial (Apache-2.0), revision
6fe1fcdab3684ad78cbdf08d1124b4f0fdac7a8b. See THIRD_PARTY.md.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Logic.Function.Basic

/-!
# Spanning subgraphs of a simple graph
-/

@[expose] public section

universe u

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

abbrev SpanningSubgraph (G : SimpleGraph V) :=
  {H : G.Subgraph // H.IsSpanning}

lemma edgeSet_eq_edgeSet_diff_setOf_isDiag : G.edgeSet = G.edgeSet \ { e | e.IsDiag } := by
  apply Set.Subset.antisymm
  · rw [Set.subset_def]
    rintro x hx
    apply Set.mem_sdiff_of_mem
    · exact hx
    · dsimp
      apply not_isDiag_of_mem_edgeSet
      exact hx
  · exact Set.sdiff_subset

namespace SpanningSubgraph

def edgeSet (H : G.SpanningSubgraph) := (H : G.Subgraph).edgeSet
def coe (H : G.SpanningSubgraph) := (H : G.Subgraph).spanningCoe

/- Two spanning subgraphs of G are equal iff their edgeset are equal -/
lemma edgeSet_injective :
  Function.Injective fun (H : G.SpanningSubgraph) => H.edgeSet := by
    intro H₁ H₂ edgeseteq
    let ⟨G₁, G₁spanning⟩ := H₁
    let ⟨G₂, G₂spanning⟩ := H₂
    apply Subtype.ext
    change G₁ = G₂
    change G₁.edgeSet = G₂.edgeSet at edgeseteq
    rw [Subgraph.ext_iff]
    constructor
    exact Set.Subset.antisymm (fun ⦃a⦄ _ ↦ G₂spanning a) fun ⦃a⦄ _ ↦ G₁spanning a
    rw [← Subgraph.spanningCoe_inj, ← SimpleGraph.edgeSet_inj]
    exact edgeseteq

@[simp]
lemma edgeSet_inj (H₁ H₂ : G.SpanningSubgraph) :
  H₁.edgeSet = H₂.edgeSet ↔ H₁ = H₂ :=
  Function.Injective.eq_iff (SpanningSubgraph.edgeSet_injective G)

end SpanningSubgraph

section FromPowerset

variable (F : 𝒫 G.edgeSet)

lemma powerset_edgeSet_eq_diff_setOf_isDiag : (F : Set (Sym2 V)) = ↑F \ Sym2.diagSet := by
  let ⟨F', hFsubset⟩ := F
  apply Set.subset_of_mem_powerset at hFsubset
  rw [edgeSet_eq_edgeSet_diff_setOf_isDiag] at hFsubset
  rw [Set.subset_sdiff] at hFsubset
  rcases hFsubset with ⟨_, hFnondiag⟩
  exact Eq.symm (Disjoint.sdiff_eq_right (id (Disjoint.symm hFnondiag)))

lemma fromEdgeSet_Subgraph : fromEdgeSet (F : Set (Sym2 V)) ≤ G := by
  intro u v h
  exact F.property h.1

def spanningSubgraph_fromEdgeSet' : G.Subgraph where
  verts := Set.univ
  Adj := (fromEdgeSet F).Adj
  adj_sub := by
    have h' : fromEdgeSet F ≤ G := by
      exact fromEdgeSet_Subgraph G F
    exact fun {v w} a ↦ h' a
  edge_vert _ := Set.mem_univ _
  symm := (fromEdgeSet (F : Set (Sym2 V))).symm

lemma spanningSubgraph_fromEdgeSet_isSpanning :
    (G.spanningSubgraph_fromEdgeSet' F).IsSpanning := by
  exact fun _ ↦ trivial

def spanningSubgraph_fromEdgeSet : G.SpanningSubgraph :=
  ⟨G.spanningSubgraph_fromEdgeSet' F, G.spanningSubgraph_fromEdgeSet_isSpanning F⟩

end FromPowerset


open Function

def powerset_edgeSet_equiv_SpanningSubgraph : 𝒫 G.edgeSet ≃ G.SpanningSubgraph where
  toFun := G.spanningSubgraph_fromEdgeSet
  invFun H := ⟨H.edgeSet, Subgraph.edgeSet_subset (H : G.Subgraph)⟩
  left_inv F := by
    let H := G.spanningSubgraph_fromEdgeSet F
    let H' := fromEdgeSet (F : Set (Sym2 V))
    let h := Subgraph.edgeSet_subset (H : G.Subgraph)
    change ⟨H'.edgeSet, h⟩ = F
    apply Subtype.ext
    simp
    rw [edgeSet_fromEdgeSet, ← powerset_edgeSet_eq_diff_setOf_isDiag]
  right_inv H := by
    let F : 𝒫 G.edgeSet :=
      ⟨(H : G.Subgraph).edgeSet, Subgraph.edgeSet_subset (H : G.Subgraph)⟩
    simp
    change G.spanningSubgraph_fromEdgeSet F = H
    rw [← SpanningSubgraph.edgeSet_inj]
    change (fromEdgeSet F).edgeSet = (H : G.Subgraph).edgeSet
    rw [edgeSet_fromEdgeSet, ← powerset_edgeSet_eq_diff_setOf_isDiag]

namespace Finite

variable [Fintype V] [DecidablePred (· ∈ 𝒫 G.edgeSet)]

instance : Fintype G.SpanningSubgraph :=
  Fintype.ofBijective G.powerset_edgeSet_equiv_SpanningSubgraph G.powerset_edgeSet_equiv_SpanningSubgraph.bijective

end Finite

end SimpleGraph
