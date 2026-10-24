/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ChromaticPolynomial.ChromaticPolynomial
public import Stanley.SourceSum
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

namespace Stanley

open SimpleGraph Finset Polynomial

universe u v w
variable {V : Type u} {α : Type v} {β : Type w} [Fintype V] (G : SimpleGraph V)

noncomputable def joinColor (s : Finset V)
    (A : (G.induce (s : Set V)).Coloring α)
    (B : (G.induce (s : Set V)ᶜ).Coloring β) : G.Coloring (α ⊕ β) := by
  classical
  refine Coloring.mk (fun v => if hv : v ∈ s then Sum.inl (A ⟨v, hv⟩)
    else Sum.inr (B ⟨v, hv⟩)) ?_
  intro u v h
  by_cases hu : u ∈ s <;> by_cases hv : v ∈ s
  · simpa [hu, hv] using A.valid (show (G.induce (s : Set V)).Adj ⟨u, hu⟩ ⟨v, hv⟩ from h)
  · simp [hu, hv]
  · simp [hu, hv]
  · simpa [hu, hv] using B.valid (show (G.induce (s : Set V)ᶜ).Adj ⟨u, hu⟩ ⟨v, hv⟩ from h)

noncomputable def colorSumEquiv :
    (Σ s : Finset V, (G.induce (s : Set V)).Coloring α ×
      (G.induce (s : Set V)ᶜ).Coloring β) ≃ G.Coloring (α ⊕ β) := by
  classical
  apply Equiv.ofBijective (fun x => joinColor G x.1 x.2.1 x.2.2)
  constructor
  · rintro ⟨s, A, B⟩ ⟨t, C, D⟩ h
    have hst : s = t := by
      ext v
      have hv := congrArg (fun c : G.Coloring (α ⊕ β) => (c v).isLeft) h
      simpa [joinColor, Coloring.mk, apply_dite Sum.isLeft] using hv
    subst t
    have hA : A = C := by
      ext v
      have hv := congrArg (fun c : G.Coloring (α ⊕ β) => c v.val) h
      simpa [joinColor, Coloring.mk, v.property] using hv
    have hB : B = D := by
      ext v
      have hv := congrArg (fun c : G.Coloring (α ⊕ β) => c v.val) h
      have hn : v.val ∉ s := v.property
      simpa [joinColor, Coloring.mk, hn] using hv
    cases hA
    cases hB
    rfl
  · intro c
    let s : Finset V := univ.filter (fun v => (c v).isLeft)
    have hl (v : (s : Set V)) : (c v.val).isLeft := (mem_filter.mp v.property).2
    have hr (v : ((s : Set V)ᶜ : Set V)) : (c v.val).isRight := by
      apply Sum.not_isLeft.mp
      intro h
      exact v.property (mem_filter.mpr ⟨mem_univ _, h⟩)
    let A : (G.induce (s : Set V)).Coloring α := Coloring.mk
      (fun v => (c v.val).getLeft (hl v)) (by
        intro u v h he
        apply c.valid (show G.Adj u.val v.val from h)
        change c u.val = c v.val
        rw [← Sum.inl_getLeft (c u.val) (hl u), ← Sum.inl_getLeft (c v.val) (hl v), he])
    let B : (G.induce (s : Set V)ᶜ).Coloring β := Coloring.mk
      (fun v => (c v.val).getRight (hr v)) (by
        intro u v h he
        apply c.valid (show G.Adj u.val v.val from h)
        change c u.val = c v.val
        rw [← Sum.inr_getRight (c u.val) (hr u), ← Sum.inr_getRight (c v.val) (hr v), he])
    refine ⟨⟨s, A, B⟩, ?_⟩
    ext v
    by_cases hv : v ∈ s
    · simp [joinColor, Coloring.mk, hv, A]
    · simp [joinColor, Coloring.mk, hv, B]

theorem chromaticPolynomial_eq_external : chromaticPolynomial G = G.ChromaticPolynomial ℤ := by
  classical
  rw [chromaticPolynomial, finsum_eq_sum_of_fintype]
  unfold SimpleGraph.ChromaticPolynomial
  apply Finset.sum_congr rfl
  intro F _
  have e : (G.spanningSubgraph_fromEdgeSet' F).coe ≃g fromEdgeSet F.val :=
    { toEquiv := Equiv.Set.univ V, map_rel_iff' := by intros; rfl }
  have hc := Fintype.card_congr e.connectedComponentEquiv
  simp only [Nat.card_eq_fintype_card]
  unfold SimpleGraph.edge_subset_ConnectedComponent_card
  rw [hc]

theorem eval_card (α : Type v) [Fintype α] :
    (chromaticPolynomial G).eval (Fintype.card α : ℤ) = Fintype.card (G.Coloring α) :=
  by rw [chromaticPolynomial_eq_external]; exact G.ChromaticPolynomial_eval ℤ α

theorem polynomial_ext_nat (p q : ℤ[X])
    (h : ∀ n : ℕ, p.eval (n : ℤ) = q.eval (n : ℤ)) : p = q := by
  apply p.eq_of_infinite_eval_eq q
  apply (Set.infinite_range_of_injective Int.ofNat_injective).mono
  rintro _ ⟨n, rfl⟩
  exact h n

open Classical in
theorem eval_add_nat (n m : ℕ) :
    (chromaticPolynomial G).eval ((n : ℤ) + m) =
      ∑ s : Finset V, (chromaticPolynomial (G.induce (s : Set V))).eval (n : ℤ) *
        (chromaticPolynomial (G.induce (s : Set V)ᶜ)).eval (m : ℤ) := by
  classical
  have h := Fintype.card_congr (colorSumEquiv (α := Fin n) (β := Fin m) G)
  rw [Fintype.card_sigma] at h
  simpa [Fintype.card_prod, ← eval_card, Fintype.card_sum, Nat.cast_sum, Nat.cast_mul] using
    congrArg (fun k : ℕ => (k : ℤ)) h.symm

open Classical in
theorem convolution (a b : ℤ) :
    (chromaticPolynomial G).eval (a + b) =
      ∑ s : Finset V, (chromaticPolynomial (G.induce (s : Set V))).eval a *
        (chromaticPolynomial (G.induce (s : Set V)ᶜ)).eval b := by
  classical
  have step (m : ℕ) :
      (chromaticPolynomial G).comp (X + C (m : ℤ)) =
        ∑ s : Finset V, chromaticPolynomial (G.induce (s : Set V)) *
          C ((chromaticPolynomial (G.induce (s : Set V)ᶜ)).eval (m : ℤ)) := by
    apply polynomial_ext_nat
    intro n
    simpa [Polynomial.eval_comp, Polynomial.eval_finsetSum] using eval_add_nat G n m
  have step' (a : ℤ) (m : ℕ) :
      (chromaticPolynomial G).eval (a + (m : ℤ)) =
        ∑ s : Finset V, (chromaticPolynomial (G.induce (s : Set V))).eval a *
          (chromaticPolynomial (G.induce (s : Set V)ᶜ)).eval (m : ℤ) := by
    simpa [Polynomial.eval_comp, Polynomial.eval_finsetSum] using congrArg (Polynomial.eval a) (step m)
  have final : (chromaticPolynomial G).comp (C a + X) =
      ∑ s : Finset V, C ((chromaticPolynomial (G.induce (s : Set V))).eval a) *
        chromaticPolynomial (G.induce (s : Set V)ᶜ) := by
    apply polynomial_ext_nat
    intro m
    simpa [Polynomial.eval_comp, Polynomial.eval_finsetSum] using step' a m
  simpa [Polynomial.eval_comp, Polynomial.eval_finsetSum] using congrArg (Polynomial.eval b) final

open Classical in
theorem chromaticPolynomial_iso {W : Type*} [Fintype W] (H : SimpleGraph W) (e : G ≃g H) :
    chromaticPolynomial G = chromaticPolynomial H := by
  apply polynomial_ext_nat
  intro n
  have h := Fintype.card_congr (SimpleGraph.coloringCongr e (Equiv.refl (Fin n)))
  simpa [← eval_card] using congrArg (fun k : ℕ => (k : ℤ)) h

@[simp] theorem chromaticPolynomial_induce_univ :
    chromaticPolynomial (G.induce Set.univ) = chromaticPolynomial G :=
  chromaticPolynomial_iso _ _ (SimpleGraph.induceUnivIso G)

open Classical in
theorem eval_zero [Nonempty V] : (chromaticPolynomial G).eval 0 = 0 := by
  have : IsEmpty (G.Coloring (Fin 0)) :=
    ⟨fun c => Fin.elim0 (c (Classical.choice (inferInstance : Nonempty V)))⟩
  simpa using eval_card G (Fin 0)

open Classical in
omit [Fintype V] in
theorem eval_one_induce (s : Finset V) :
    (chromaticPolynomial (G.induce (s : Set V))).eval 1 =
      if Independent G (s : Set V) then 1 else 0 := by
  classical
  have hc := eval_card (G.induce (s : Set V)) (Fin 1)
  by_cases hs : Independent G (s : Set V)
  · let c : (G.induce (s : Set V)).Coloring (Fin 1) :=
      Coloring.mk (fun _ => 0) (fun {u v} h => (hs u.val u.property v.val v.property h).elim)
    have : Nonempty ((G.induce (s : Set V)).Coloring (Fin 1)) := ⟨c⟩
    let : Unique ((G.induce (s : Set V)).Coloring (Fin 1)) :=
      { default := c, uniq := fun _ => Subsingleton.elim _ _ }
    simpa [hs] using hc
  · have : IsEmpty ((G.induce (s : Set V)).Coloring (Fin 1)) := ⟨fun c => hs (by
      intro u hu v hv h
      exact c.valid (show (G.induce (s : Set V)).Adj ⟨u, hu⟩ ⟨v, hv⟩ from h)
        (Subsingleton.elim _ _))⟩
    simpa [hs] using hc

open Classical in
theorem independent_recurrence [Nonempty V] :
    ∑ s : Finset V, (if Independent G (s : Set V) then
      (chromaticPolynomial (G.induce (s : Set V)ᶜ)).eval (-1) else 0) = 0 := by
  have h := convolution G 1 (-1)
  simpa only [add_neg_cancel, eval_zero, eval_one_induce, ite_mul, one_mul, zero_mul] using h.symm

end Stanley
