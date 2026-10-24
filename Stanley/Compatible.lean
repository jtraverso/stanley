/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Stanley.NegOne

@[expose] public section

namespace Stanley

open SimpleGraph Finset

variable {V : Type*} (G : SimpleGraph V)

noncomputable instance [Fintype V] (k : ℕ) : Fintype (CompatiblePair G k) := by
  classical
  apply Fintype.ofInjective (fun p : CompatiblePair G k => (p.orientation, p.color))
  intro p q h
  exact CompatiblePair.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

namespace CompatiblePair

noncomputable def join [Fintype V] (k : ℕ) (s : Finset V)
    (A : AcyclicOrientation (G.induce (s : Set V)))
    (B : CompatiblePair (G.induce (s : Set V)ᶜ) k) : CompatiblePair G (k + 1) := by
  classical
  refine ⟨AcyclicOrientation.join (s : Set V) A B.orientation,
    (fun v => if hv : v ∈ s then 0 else (B.color ⟨v, hv⟩).succ), ?_⟩
  intro u v h
  rcases h with ⟨hu, hv, h⟩ | ⟨hu, hv, _⟩ | ⟨hu, hv, h⟩
  · change u ∈ s at hu
    change v ∈ s at hv
    simp [hu, hv]
  · change u ∈ s at hu
    change v ∉ s at hv
    simp [hu, hv]
  · change u ∉ s at hu
    change v ∉ s at hv
    simpa [hu, hv] using B.compatible ⟨u, hu⟩ ⟨v, hv⟩ h

noncomputable def splitEquiv [Fintype V] (k : ℕ) :
    (Σ s : Finset V, AcyclicOrientation (G.induce (s : Set V)) ×
      CompatiblePair (G.induce (s : Set V)ᶜ) k) ≃ CompatiblePair G (k + 1) := by
  classical
  apply Equiv.ofBijective (fun x => join G k x.1 x.2.1 x.2.2)
  constructor
  · rintro ⟨s, A, B⟩ ⟨t, C, D⟩ h
    have hst : s = t := by
      ext v
      have hv := congrArg (fun p : CompatiblePair G (k + 1) => p.color v = 0) h
      simpa [join] using hv
    subst t
    have hd := congrArg CompatiblePair.orientation h
    have hA : A = C := by
      simpa [join] using congrArg (fun d : AcyclicOrientation G => d.restrict (s : Set V)) hd
    have hB : B = D := by
      apply CompatiblePair.ext
      · simpa [join] using
          congrArg (fun d : AcyclicOrientation G => d.restrict (s : Set V)ᶜ) hd
      · funext v
        have hv := congrArg (fun p : CompatiblePair G (k + 1) => p.color v.val) h
        have hn : v.val ∉ s := v.property
        simpa [join, hn] using hv
    cases hA
    cases hB
    rfl
  · intro p
    let s : Finset V := univ.filter (fun v => p.color v = 0)
    have hs (v : V) : v ∈ s ↔ p.color v = 0 := by simp [s]
    have hn (v : ((s : Set V)ᶜ : Set V)) : p.color v.val ≠ 0 := by
      intro h
      exact v.property ((hs v.val).mpr h)
    let A := p.orientation.restrict (s : Set V)
    let B : CompatiblePair (G.induce (s : Set V)ᶜ) k :=
      ⟨p.orientation.restrict (s : Set V)ᶜ, (fun v => (p.color v.val).pred (hn v)), by
        intro u v h
        apply Fin.succ_le_succ_iff.mp
        simpa using p.compatible u.val v.val h⟩
    have hout (u v : V) (hu : u ∉ (s : Set V)) (hv : v ∈ (s : Set V)) :
        ¬p.orientation.val u v := by
      intro h
      have hle := p.compatible u v h
      rw [(hs v).mp hv] at hle
      exact hu ((hs u).mpr (Fin.le_zero_iff.mp hle))
    refine ⟨⟨s, A, B⟩, ?_⟩
    apply CompatiblePair.ext
    · exact p.orientation.join_restrict (s : Set V) hout
    · funext v
      by_cases hv : v ∈ s
      · simpa [join, hv] using ((hs v).mp hv).symm
      · simp [join, hv, B]

/-- Reversing the finite palette converts our increasing convention to the paper's
weakly decreasing convention, without changing the orientation. -/
def paperConventionEquiv (k : ℕ) : CompatiblePair G k ≃
    {p : AcyclicOrientation G × (V → Fin k) //
      ∀ u v, p.1.val u v → p.2 v ≤ p.2 u} where
  toFun p := ⟨(p.orientation, fun v => (p.color v).rev),
    fun u v h => Fin.rev_le_rev.mpr (p.compatible u v h)⟩
  invFun p := ⟨p.val.1, (fun v => (p.val.2 v).rev),
    fun u v h => Fin.rev_le_rev.mpr (p.property u v h)⟩
  left_inv p := by apply CompatiblePair.ext; rfl; funext v; simp
  right_inv p := by apply Subtype.ext; apply Prod.ext; rfl; funext v; simp

end CompatiblePair

open Classical in
theorem compatibleCount_succ [Fintype V] (k : ℕ) :
    compatibleCount G (k + 1) =
      ∑ s : Finset V, orientationCount (G.induce (s : Set V)) *
        compatibleCount (G.induce (s : Set V)ᶜ) k := by
  classical
  have h := Fintype.card_congr (CompatiblePair.splitEquiv G k)
  rw [Fintype.card_sigma] at h
  simpa [compatibleCount, orientationCount, Nat.card_eq_fintype_card,
    Fintype.card_prod, Nat.cast_sum, Nat.cast_mul] using
    congrArg (fun n : ℕ => (n : ℤ)) h.symm

end Stanley
