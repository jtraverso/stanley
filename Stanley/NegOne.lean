/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Stanley.Convolution
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Stanley

open SimpleGraph Finset Polynomial

universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)

@[simp] theorem orientationCount_induce_univ :
    orientationCount (G.induce Set.univ) = orientationCount G := by
  simp only [orientationCount, Nat.card_eq_fintype_card]
  exact_mod_cast Fintype.card_congr
    (AcyclicOrientation.mapEquiv (SimpleGraph.induceUnivIso G))

theorem orientationCount_empty [IsEmpty V] : orientationCount G = 1 := by
  let d : AcyclicOrientation G := ⟨fun _ _ => False,
    (fun _ _ h => h.elim), (fun u => isEmptyElim u),
    ⟨fun u => isEmptyElim u⟩⟩
  have : Subsingleton (AcyclicOrientation G) := ⟨fun A B => by
    apply Subtype.ext
    funext u
    exact isEmptyElim u⟩
  let : Unique (AcyclicOrientation G) :=
    { default := d, uniq := fun _ => Subsingleton.elim _ _ }
  simp [orientationCount, Nat.card_eq_fintype_card]

theorem chromaticPolynomial_empty [IsEmpty V] : chromaticPolynomial G = 1 := by
  apply polynomial_ext_nat
  intro n
  let c : G.Coloring (Fin n) := Coloring.mk (fun v => isEmptyElim v)
    (fun {v} => isEmptyElim v)
  let : Unique (G.Coloring (Fin n)) :=
    { default := c, uniq := fun _ => Subsingleton.elim _ _ }
  simpa using eval_card G (Fin n)

open Classical in
theorem signed_sources [Nonempty V] :
    ∑ s : Finset V, (if Independent G (s : Set V) then
      (-1 : ℤ) ^ Fintype.card ↥((s : Set V)ᶜ) *
        orientationCount (G.induce (s : Set V)ᶜ) else 0) = 0 := by
  classical
  have hsign (s : Finset V) :
      (-1 : ℤ) ^ Fintype.card V * (-1 : ℤ) ^ s.card =
        (-1 : ℤ) ^ Fintype.card ↥((s : Set V)ᶜ) := by
    have hc : Fintype.card ↥((s : Set V)ᶜ) + s.card = Fintype.card V := by
      have hcomp : Fintype.card ↥((s : Set V)ᶜ) = Fintype.card V - s.card := by
        calc
          _ = Fintype.card {x : V // x ∉ (s : Set V)} :=
            Fintype.card_congr (Equiv.refl _)
          _ = Fintype.card V - s.card := by
            rw [Fintype.card_subtype_compl]
            congr 1
            exact Fintype.card_coe s
      rw [hcomp]
      exact Nat.sub_add_cancel (Finset.card_le_univ s)
    rw [← pow_add]
    have hn : Fintype.card V + s.card = 2 * s.card +
        Fintype.card ↥((s : Set V)ᶜ) := by omega
    rw [hn, pow_add, pow_mul]
    norm_num
  calc
    _ = (-1 : ℤ) ^ Fintype.card V *
        ∑ s : Finset V, (if Independent G (s : Set V) then
          (-1 : ℤ) ^ s.card * orientationCount (G.induce (s : Set V)ᶜ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : Independent G (s : Set V) <;> simp [hs, ← mul_assoc, hsign]
    _ = 0 := by rw [alternating_independent G, mul_zero]

/-- Stanley's acyclic-orientation identity, expressed as a signed integer evaluation. -/
theorem eval_neg_one : (chromaticPolynomial G).eval (-1) =
    (-1 : ℤ) ^ Fintype.card V * orientationCount G := by
  classical
  have aux : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      Fintype.card W = n → (chromaticPolynomial H).eval (-1) =
        (-1 : ℤ) ^ Fintype.card W * orientationCount H := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro W _ H hn
      by_cases hzero : n = 0
      · have : IsEmpty W := Fintype.card_eq_zero_iff.mp (hn.trans hzero)
        simp [chromaticPolynomial_empty, orientationCount_empty]
      · have : Nonempty W := Fintype.card_pos_iff.mp (by omega)
        let f (s : Finset W) : ℤ := if Independent H (s : Set W) then
          (chromaticPolynomial (H.induce (s : Set W)ᶜ)).eval (-1) else 0
        let g (s : Finset W) : ℤ := if Independent H (s : Set W) then
          (-1 : ℤ) ^ Fintype.card ↥((s : Set W)ᶜ) *
            orientationCount (H.induce (s : Set W)ᶜ) else 0
        have hdiff : ∑ s : Finset W, (f s - g s) = 0 := by
          rw [Finset.sum_sub_distrib]
          change (∑ s : Finset W, f s) - (∑ s : Finset W, g s) = 0
          rw [show (∑ s : Finset W, f s) = 0 from independent_recurrence H,
            show (∑ s : Finset W, g s) = 0 from signed_sources H, sub_self]
        have hsingle : (∑ s : Finset W, (f s - g s)) = f ∅ - g ∅ := by
          apply Finset.sum_eq_single ∅
          · intro s _ hs
            have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
            obtain ⟨v, hv⟩ := hsne
            have hcard : Fintype.card ↥((s : Set W)ᶜ) < n := by
              rw [← hn]
              exact Fintype.card_subtype_lt (p := fun v => v ∉ (s : Set W)) (by simpa)
            have h := ih _ hcard _ (H.induce (s : Set W)ᶜ) rfl
            simp only [f, g, h, sub_self]
          · simp
        rw [hsingle] at hdiff
        let e : H.induce (((∅ : Finset W) : Set W)ᶜ) ≃g H :=
          { toEquiv :=
              { toFun := Subtype.val
                invFun := fun v => ⟨v, by simp⟩
                left_inv := fun _ => rfl
                right_inv := fun _ => rfl }
            map_rel_iff' := by intros; rfl }
        have hp := chromaticPolynomial_iso _ _ e
        have ha : orientationCount (H.induce (((∅ : Finset W) : Set W)ᶜ)) =
            orientationCount H := by
          unfold orientationCount
          exact_mod_cast Nat.card_congr (AcyclicOrientation.mapEquiv e)
        have hc := Fintype.card_congr e.toEquiv
        have hi : Independent H ((∅ : Finset W) : Set W) := by
          intro u hu
          simp at hu
        simp only [f, g, ite_eq_left hi] at hdiff
        rw [hp, hc, ha] at hdiff
        exact sub_eq_zero.mp hdiff
  exact aux _ V G rfl

end Stanley
