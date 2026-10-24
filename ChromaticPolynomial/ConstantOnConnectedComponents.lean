/-
Adapted from anlucia/ChromaticPolynomial (Apache-2.0), revision
6fe1fcdab3684ad78cbdf08d1124b4f0fdac7a8b. See THIRD_PARTY.md.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

universe u

namespace SimpleGraph

variable {V : Type u} [Fintype V] (G : SimpleGraph V)
/- We will consider α-colorings of G -/
variable {α : Type*} [Fintype α]

open Classical

omit [Fintype V] [Fintype α] in
lemma constant_on_cc (π : V → α) : (∀ {v w : V}, G.Adj v w → π v = π w) ↔
  (∀ (v w : V) (p : G.Walk v w), p.IsPath → π v = π w) := by
  constructor
  · intro hconstant _ _ walk hpath
    induction walk with
    | nil => rfl
    | cons h p ih =>
      rw [hconstant h]
      exact ih (Walk.IsPath.of_cons hpath)
  · intro hpath v w hadj
    have p := (Adj.toWalk hadj).toPath
    exact hpath v w p p.prop


def equiv_constant_on_cc :
  {π : V → α // ∀ {v w : V}, G.Adj v w → π v = π w } ≃ (G.ConnectedComponent → α) where
  toFun π := ConnectedComponent.lift π.val ((G.constant_on_cc π.val).mp π.prop)
  invFun P := ⟨fun v ↦ P (G.connectedComponentMk v), by {
    intro v w hadj
    simp
    rw [ConnectedComponent.connectedComponentMk_eq_of_adj hadj]
  }⟩
  left_inv _ := by simp
  right_inv P := by
    simp
    apply funext_iff.mpr
    intro c
    induction c using Quot.induction_on with
    | _ v => rfl

end SimpleGraph
