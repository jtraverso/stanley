/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

import Solution
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Factorial.Cast

open SimpleGraph Polynomial Stanley

#print axioms Stanley.eval_card
#print axioms Stanley.convolution
#print axioms Stanley.compatible_count_eq
#print axioms Stanley.acyclic_count_eq
#print axioms Stanley.wellFounded_iff_no_cycle

namespace Audit

def completeColoringEquiv (n k : ℕ) :
    (⊤ : SimpleGraph (Fin n)).Coloring (Fin k) ≃ (Fin n ↪ Fin k) where
  toFun c := ⟨c, fun _ _ h => by
    by_contra hn
    exact c.valid hn h⟩
  invFun f := Coloring.mk f (fun h => f.injective.ne h)
  left_inv c := by ext v; rfl
  right_inv f := by ext v; rfl

theorem polynomial_K2 : chromaticPolynomial (⊤ : SimpleGraph (Fin 2)) = X * (X - 1) := by
  classical
  apply polynomial_ext_nat
  intro k
  have h := Fintype.card_congr (completeColoringEquiv 2 k)
  rw [Fintype.card_embedding_eq] at h
  have hp := eval_card (⊤ : SimpleGraph (Fin 2)) (Fin k)
  simp only [Fintype.card_fin] at hp h
  rw [h, Nat.cast_descFactorial_two] at hp
  simpa using hp

-- Empty vertex set, including the zero-color convention.
example : (chromaticPolynomial (⊥ : SimpleGraph (Fin 0))).eval (-1) = 1 := by
  simp [chromaticPolynomial_empty]

example : compatibleCount (⊥ : SimpleGraph (Fin 0)) 0 = 1 :=
  compatibleCount_empty _ _

-- A nonempty graph has no zero-color pairs.
example : compatibleCount (⊥ : SimpleGraph (Fin 1)) 0 = 0 := compatibleCount_zero _

-- An actual edge has exactly two acyclic orientations.
example : orientationCount (⊤ : SimpleGraph (Fin 2)) = 2 := by
  have h := acyclic_count_eq (⊤ : SimpleGraph (Fin 2))
  rw [polynomial_K2] at h
  norm_num at h
  exact h.symm

-- Weak compatibility allows equal colors: for one edge and two colors there are six pairs.
example : compatibleCount (⊤ : SimpleGraph (Fin 2)) 2 = 6 := by
  have h := compatible_count_eq (⊤ : SimpleGraph (Fin 2)) 2
  rw [polynomial_K2] at h
  norm_num at h
  exact h.symm

end Audit
