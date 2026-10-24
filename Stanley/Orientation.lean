/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Stanley.Definitions
public import Mathlib.Order.WellFounded
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

namespace Stanley

open SimpleGraph Finset

universe u
variable {V : Type u} (G : SimpleGraph V)

noncomputable instance [Fintype V] : Fintype (AcyclicOrientation G) := Fintype.ofFinite _

/-- On finite types, well-foundedness is equivalent to having no directed cycle. -/
theorem wellFounded_iff_no_cycle [Finite V] (r : V → V → Prop) :
    WellFounded r ↔ ∀ v, ¬ Relation.TransGen r v v := by
  constructor
  · intro h v hv
    have : WellFounded (Relation.TransGen r) := h.transGen
    exact irrefl v hv
  · intro h
    have : Std.Irrefl (Relation.TransGen r) := ⟨h⟩
    have hwf := Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen r)
    exact Subrelation.wf (fun h => Relation.TransGen.single h) hwf

namespace AcyclicOrientation

variable {G}

theorem sound (D : AcyclicOrientation G) {u v : V} (h : D.val u v) : G.Adj u v :=
  D.property.1 u v h

theorem directs (D : AcyclicOrientation G) {u v : V} (h : G.Adj u v) :
    D.val u v ∨ D.val v u := D.property.2.1 u v h

theorem wf (D : AcyclicOrientation G) : WellFounded D.val := D.property.2.2

def Source (D : AcyclicOrientation G) (v : V) : Prop := ∀ u, ¬D.val u v

theorem exists_source [Nonempty V] (D : AcyclicOrientation G) : ∃ v, D.Source v := by
  obtain ⟨v, _, hv⟩ := D.wf.has_min Set.univ Set.univ_nonempty
  exact ⟨v, fun u => hv u (Set.mem_univ u)⟩

def restrict (D : AcyclicOrientation G) (s : Set V) : AcyclicOrientation (G.induce s) :=
  ⟨fun u v => D.val u.val v.val,
    (fun _ _ h => D.sound h), (fun _ _ h => D.directs h), D.wf.onFun⟩

/-- Transport an orientation across a graph isomorphism. -/
def map {W : Type*} {H : SimpleGraph W} (e : G ≃g H)
    (D : AcyclicOrientation G) : AcyclicOrientation H :=
  ⟨fun u v => D.val (e.symm u) (e.symm v),
    (fun _ _ h => e.symm.map_adj_iff.mp (D.sound h)),
    (fun _ _ h => D.directs (e.symm.map_adj_iff.mpr h)), D.wf.onFun⟩

def mapEquiv {W : Type*} {H : SimpleGraph W} (e : G ≃g H) :
    AcyclicOrientation G ≃ AcyclicOrientation H where
  toFun := map e
  invFun := map e.symm
  left_inv D := by apply Subtype.ext; funext u v; simp [map]
  right_inv D := by apply Subtype.ext; funext u v; simp [map]

/-- Orient every crossing edge from s to its complement. -/
def joinRel (s : Set V) (A : AcyclicOrientation (G.induce s))
    (B : AcyclicOrientation (G.induce sᶜ)) (u v : V) : Prop :=
  (∃ hu hv, A.val ⟨u, hu⟩ ⟨v, hv⟩) ∨
    (u ∈ s ∧ v ∉ s ∧ G.Adj u v) ∨
    (∃ hu hv, B.val ⟨u, hu⟩ ⟨v, hv⟩)

theorem joinRel_inside (s : Set V) (A : AcyclicOrientation (G.induce s))
    (B : AcyclicOrientation (G.induce sᶜ)) (u v : s) :
    joinRel s A B u v ↔ A.val u v := by
  simp [joinRel, u.property, v.property]

theorem joinRel_outside (s : Set V) (A : AcyclicOrientation (G.induce s))
    (B : AcyclicOrientation (G.induce sᶜ)) (u v : (sᶜ : Set V)) :
    joinRel s A B u v ↔ B.val u v := by
  have hu : u.val ∉ s := u.property
  have hv : v.val ∉ s := v.property
  simp [joinRel, hu, hv]

theorem joinRel_wf (s : Set V) (A : AcyclicOrientation (G.induce s))
    (B : AcyclicOrientation (G.induce sᶜ)) : WellFounded (joinRel s A B) := by
  have accS (u : s) : Acc (joinRel s A B) u.val := by
    induction A.wf.apply u with
    | intro u _ ih =>
      refine Acc.intro _ (fun v hv => ?_)
      have hvs : v ∈ s := by
        by_contra hn
        simp [joinRel, hn, u.property] at hv
      exact ih ⟨v, hvs⟩ ((joinRel_inside s A B ⟨v, hvs⟩ u).mp hv)
  have accT (u : (sᶜ : Set V)) : Acc (joinRel s A B) u.val := by
    induction B.wf.apply u with
    | intro u _ ih =>
      refine Acc.intro _ (fun v hv => ?_)
      by_cases hvs : v ∈ s
      · exact accS ⟨v, hvs⟩
      · exact ih ⟨v, hvs⟩ ((joinRel_outside s A B ⟨v, hvs⟩ u).mp hv)
  exact ⟨fun u => by
    by_cases hu : u ∈ s
    · exact accS ⟨u, hu⟩
    · exact accT ⟨u, hu⟩⟩

def join (s : Set V) (A : AcyclicOrientation (G.induce s))
    (B : AcyclicOrientation (G.induce sᶜ)) : AcyclicOrientation G := by
  refine ⟨joinRel s A B, ?_, ?_, joinRel_wf s A B⟩
  · intro u v h
    rcases h with ⟨hu, hv, h⟩ | ⟨_, _, h⟩ | ⟨hu, hv, h⟩
    · exact A.sound h
    · exact h
    · exact B.sound h
  · intro u v h
    by_cases hu : u ∈ s <;> by_cases hv : v ∈ s
    · rcases A.directs (show (G.induce s).Adj ⟨u, hu⟩ ⟨v, hv⟩ from h) with h | h
      · exact Or.inl (Or.inl ⟨hu, hv, h⟩)
      · exact Or.inr (Or.inl ⟨hv, hu, h⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨hu, hv, h⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hv, hu, h.symm⟩))
    · rcases B.directs (show (G.induce sᶜ).Adj ⟨u, hu⟩ ⟨v, hv⟩ from h) with h | h
      · exact Or.inl (Or.inr (Or.inr ⟨hu, hv, h⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hv, hu, h⟩))

@[simp] theorem restrict_join_left (s : Set V) (A : AcyclicOrientation (G.induce s))
    (B : AcyclicOrientation (G.induce sᶜ)) : (join s A B).restrict s = A := by
  apply Subtype.ext
  funext u v
  exact propext (joinRel_inside s A B u v)

@[simp] theorem restrict_join_right (s : Set V) (A : AcyclicOrientation (G.induce s))
    (B : AcyclicOrientation (G.induce sᶜ)) : (join s A B).restrict sᶜ = B := by
  apply Subtype.ext
  funext u v
  exact propext (joinRel_outside s A B u v)

theorem join_restrict (D : AcyclicOrientation G) (s : Set V)
    (hout : ∀ u v, u ∉ s → v ∈ s → ¬ D.val u v) :
    join s (D.restrict s) (D.restrict sᶜ) = D := by
  apply Subtype.ext
  funext u v
  apply propext
  constructor
  · intro h
    rcases h with ⟨hu, hv, h⟩ | ⟨hu, hv, h⟩ | ⟨hu, hv, h⟩
    · exact h
    · exact (D.directs h).resolve_right (hout v u hv hu)
    · exact h
  · intro h
    by_cases hu : u ∈ s <;> by_cases hv : v ∈ s
    · exact Or.inl ⟨hu, hv, h⟩
    · exact Or.inr (Or.inl ⟨hu, hv, D.sound h⟩)
    · exact (hout u v hu hv h).elim
    · exact Or.inr (Or.inr ⟨hu, hv, h⟩)

end AcyclicOrientation

/-- A vertex subset is independent when it contains no edge. -/
def Independent (s : Set V) : Prop := ∀ u ∈ s, ∀ v ∈ s, ¬ G.Adj u v

namespace AcyclicOrientation

variable {G}

def ofIndependent (s : Set V) (hs : Independent G s) :
    AcyclicOrientation (G.induce s) :=
  ⟨fun _ _ => False,
    (fun _ _ h => h.elim),
    (fun u v h => (hs u.val u.property v.val v.property h).elim),
    ⟨fun v => Acc.intro v (fun _ h => h.elim)⟩⟩

def AllSources (D : AcyclicOrientation G) (s : Set V) : Prop :=
  ∀ v ∈ s, D.Source v

theorem independent_of_allSources (D : AcyclicOrientation G) (s : Set V)
    (h : D.AllSources s) : Independent G s := by
  intro u hu v hv hadj
  rcases D.directs hadj with huv | hvu
  · exact h v hv u huv
  · exact h u hu v hvu

theorem allSources_join (s : Set V) (hs : Independent G s)
    (B : AcyclicOrientation (G.induce sᶜ)) :
    (join s (ofIndependent s hs) B).AllSources s := by
  intro v hv u h
  rcases h with ⟨_, _, h⟩ | ⟨_, hn, _⟩ | ⟨_, hn, _⟩
  · exact h
  · exact hn hv
  · exact hn hv

def sourceEquiv (s : Set V) :
    {D : AcyclicOrientation G // D.AllSources s} ≃
      {_B : AcyclicOrientation (G.induce sᶜ) // Independent G s} where
  toFun D := ⟨D.val.restrict sᶜ, D.val.independent_of_allSources s D.property⟩
  invFun B := ⟨join s (ofIndependent s B.property) B.val,
    allSources_join s B.property B.val⟩
  left_inv D := by
    apply Subtype.ext
    have he : ofIndependent s (D.val.independent_of_allSources s D.property) =
        D.val.restrict s := by
      apply Subtype.ext
      funext u v
      apply propext
      exact ⟨False.elim, fun h => D.property v.val v.property u.val h⟩
    change join s _ _ = D.val
    rw [he]
    exact D.val.join_restrict s (fun u v _ hv => D.property v hv u)
  right_inv B := by
    apply Subtype.ext
    exact restrict_join_right s _ _

end AcyclicOrientation

end Stanley
