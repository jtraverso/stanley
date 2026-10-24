/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Stanley.Orientation

@[expose] public section

namespace Stanley

open SimpleGraph Finset

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

open Classical in
theorem count_allSources (s : Finset V) :
    (Fintype.card {D : AcyclicOrientation G // D.AllSources (s : Set V)} : ℤ) =
      if Independent G (s : Set V) then orientationCount (G.induce (s : Set V)ᶜ) else 0 := by
  classical
  rw [Fintype.card_congr (AcyclicOrientation.sourceEquiv (s : Set V))]
  by_cases hs : Independent G (s : Set V) <;> simp [hs, orientationCount, Nat.card_eq_fintype_card]

open Classical in
theorem alternating_sources [Nonempty V] :
    ∑ s : Finset V, (-1 : ℤ) ^ s.card *
      (Fintype.card {D : AcyclicOrientation G // D.AllSources (s : Set V)} : ℤ) = 0 := by
  classical
  have hcard (s : Finset V) :
      (Fintype.card {D : AcyclicOrientation G // D.AllSources (s : Set V)} : ℤ) =
        ∑ D : AcyclicOrientation G, if D.AllSources (s : Set V) then 1 else 0 := by
    simp [Fintype.card_subtype, Finset.sum_boole]
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro D _
  let sources : Finset V := univ.filter D.Source
  have hsources : sources.Nonempty := by
    obtain ⟨v, hv⟩ := D.exists_source
    exact ⟨v, mem_filter.mpr ⟨mem_univ v, hv⟩⟩
  have hsets : univ.filter (fun s : Finset V => D.AllSources (s : Set V)) =
      sources.powerset := by
    ext s
    simp [AcyclicOrientation.AllSources, sources, Finset.subset_iff]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, hsets]
  exact Finset.sum_powerset_neg_one_pow_card_of_nonempty hsources

open Classical in
theorem alternating_independent [Nonempty V] :
    ∑ s : Finset V, (if Independent G (s : Set V) then
      (-1 : ℤ) ^ s.card * orientationCount (G.induce (s : Set V)ᶜ) else 0) = 0 := by
  have h := alternating_sources G
  simp_rw [count_allSources, mul_ite, mul_zero] at h
  exact h

end Stanley
