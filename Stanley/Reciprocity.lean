/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Stanley.Compatible
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Stanley

open SimpleGraph Finset Polynomial

universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)

theorem compatibleCount_empty [IsEmpty V] (k : ℕ) : compatibleCount G k = 1 := by
  let d : AcyclicOrientation G := ⟨fun _ _ => False,
    (fun _ _ h => h.elim), (fun u => isEmptyElim u), ⟨fun u => isEmptyElim u⟩⟩
  let p : CompatiblePair G k := ⟨d, (fun u => isEmptyElim u), (fun u => isEmptyElim u)⟩
  have : Subsingleton (CompatiblePair G k) := ⟨fun A B => by
    apply CompatiblePair.ext
    · apply Subtype.ext
      funext v
      exact isEmptyElim v
    · funext v
      exact isEmptyElim v⟩
  let : Unique (CompatiblePair G k) :=
    { default := p, uniq := fun _ => Subsingleton.elim _ _ }
  simp [compatibleCount, Nat.card_eq_fintype_card]

theorem compatibleCount_zero [Nonempty V] : compatibleCount G 0 = 0 := by
  have : IsEmpty (CompatiblePair G 0) :=
    ⟨fun p => Fin.elim0 (p.color (Classical.choice (inferInstance : Nonempty V)))⟩
  simp [compatibleCount, Nat.card_eq_fintype_card]

/-- Stanley's chromatic reciprocity for all nonnegative integers k. The colorings in
CompatiblePair are weakly increasing along the arcs, and need not be proper. -/
theorem reciprocity (k : ℕ) :
    (chromaticPolynomial G).eval (-(k : ℤ)) =
      (-1 : ℤ) ^ Fintype.card V * compatibleCount G k := by
  classical
  have aux : ∀ k : ℕ, ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      (chromaticPolynomial H).eval (-(k : ℤ)) =
        (-1 : ℤ) ^ Fintype.card W * compatibleCount H k := by
    intro k
    induction k with
    | zero =>
      intro W _ H
      cases isEmpty_or_nonempty W with
      | inl h => simp [chromaticPolynomial_empty, compatibleCount_empty]
      | inr h => simp [eval_zero, compatibleCount_zero]
    | succ k ih =>
      intro W _ H
      have harg : -((k + 1 : ℕ) : ℤ) = -1 + -(k : ℤ) := by push_cast; ring
      rw [harg, convolution, compatibleCount_succ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [eval_neg_one, ih]
      have hc : Fintype.card (s : Set W) + Fintype.card ↥((s : Set W)ᶜ) =
          Fintype.card W := by
        calc
          _ = Fintype.card {v : W // v ∈ (s : Set W)} +
              Fintype.card {v : W // v ∉ (s : Set W)} := by
            congr 1
          _ = Fintype.card W := by
            rw [Fintype.card_subtype_compl]
            exact Nat.add_sub_cancel' (Fintype.card_subtype_le _)
      calc
        _ = ((-1 : ℤ) ^ Fintype.card (s : Set W) *
            (-1 : ℤ) ^ Fintype.card ↥((s : Set W)ᶜ)) *
            (orientationCount (H.induce (s : Set W)) *
              compatibleCount (H.induce (s : Set W)ᶜ) k) := by ring
        _ = _ := by rw [← pow_add, hc]
  exact aux k V G

/-- The signed negative evaluation counts compatible orientation/coloring pairs. -/
theorem compatible_count_eq (k : ℕ) :
    (-1 : ℤ) ^ Fintype.card V * (chromaticPolynomial G).eval (-(k : ℤ)) =
      compatibleCount G k := by
  rw [reciprocity, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- The absolute value of the evaluation at -1 counts acyclic orientations. -/
theorem acyclic_count_eq :
    (-1 : ℤ) ^ Fintype.card V * (chromaticPolynomial G).eval (-1) =
      orientationCount G := by
  rw [eval_neg_one, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

end Stanley
