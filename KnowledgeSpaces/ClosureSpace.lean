/-
Copyright (c) 2026 David Allen. All rights reserved.
Not for public release.
Authors: David Allen
-/

module

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Order.SetNotation
public import KnowledgeSpaces.Family

/-!
# Closure Space

Basic definition of a closure space.
-/

@[expose] public section

universe u

class ClosureSpace (X : Type u) extends Family X where
  ground_in_carrier : IsMember Set.univ
  closed_sInter :
    ∀ S : Set (Set X), S.Nonempty ->
      (∀ s ∈ S, IsMember s) ->
      IsMember (⋂₀ S)

variable {X : Type u} [ClosureSpace X]

def IsMember : Set X -> Prop := Family.IsMember

namespace ClosureSpace

variable {x y : Set X} {p q : X}

theorem exists_min :
    ∃ min : Set X -> Set X,
    ∀ x y,
      IsMember (min x)
      ∧ x ⊆ min x
      ∧ (∀ c, IsMember c -> x ⊆ c -> min x ⊆ c)
      ∧ (x ⊆ y → min x ⊆ min y)
      ∧ min (min x) = min x := by
  let min x := ⋂₀ {c : Set X | IsMember c ∧ x ⊆ c}
  have min_closed : ∀ x : Set X, IsMember (min x) := by
    intro x
    apply closed_sInter
    · let h : x ⊆ Set.univ := by
        intro p hp
        trivial
      exact ⟨ Set.univ, ground_in_carrier, h ⟩
    · intro c hc
      exact hc.left
  use min
  intro x y
  apply And.intro
  · exact min_closed x
  apply And.intro
  · intro p hp
    have h: ∀ c ∈ {c | IsMember c ∧ x ⊆ c}, p ∈ c := by
      intro c hc
      exact hc.right hp
    exact Set.mem_sInter.mpr h
  apply And.intro
  · intro c hc hxc p hp
    exact Set.mem_sInter.mp hp c ⟨ hc, hxc ⟩
  apply And.intro
  · intro hxy p hp
    have h: ∀ c ∈ {c | IsMember c ∧ y ⊆ c}, p ∈ c := by
      intro c hc
      exact Set.mem_sInter.mp hp c ⟨ hc.left, subset_trans hxy hc.right ⟩
    exact Set.mem_sInter.mpr h
  · ext p
    constructor
    · intro hp
      exact Set.mem_sInter.mp hp (min x) ⟨ min_closed x, subset_refl _ ⟩
    · intro hp
      have h: ∀ c ∈ {c | IsMember c ∧ min x ⊆ c}, p ∈ c := by
        intro c hc
        exact hc.right hp
      exact Set.mem_sInter.mpr h

structure ClosureOperator (X : Type u) where
  min : Set X → Set X
  extensive : ∀ A, A ⊆ min A
  monotone : ∀ {A B}, A ⊆ B → min A ⊆ min B
  idempotent : ∀ A, min (min A) = min A

namespace ClosureOperator

@[instance_reducible]
def toClosureSpace (C : ClosureOperator X) : ClosureSpace X :=
  let fam : Family X := Family.mk (fun A => C.min A = A)
  letI : Family X := fam
  {
    ground_in_carrier := by
      apply subset_antisymm
      · intro x hx
        trivial
      · exact C.extensive Set.univ

    closed_sInter := by
      intro S hS hClosed
      apply subset_antisymm
      · intro x hx
        rw [Set.mem_sInter]
        intro A hA
        have hsubset : ⋂₀ S ⊆ A := by
          intro y hy
          exact Set.mem_sInter.mp hy A hA
        have hcl_subset : C.min (⋂₀ S) ⊆ C.min A :=
          C.monotone hsubset
        rw [hClosed A hA] at hcl_subset
        exact hcl_subset hx
      · exact C.extensive (⋂₀ S)
  }

theorem toClosureSpace_unique
    (h : ∀ A, C.min A = A ↔ Family.IsMember A) :
    ∀ A, @Family.IsMember X (ClosureOperator.toClosureSpace C).toFamily A ↔
    @Family.IsMember X ClosureSpace.toFamily A := by
  intro A
  exact h A

omit [ClosureSpace X] in theorem mem_toClosureSpace_iff :
    @Family.IsMember X (ClosureOperator.toClosureSpace C).toFamily A ↔
    C.min A = A := by
  rfl

omit [ClosureSpace X] in theorem empty_closed_iff :
    C.min ∅ = ∅ ↔
    @Family.IsMember X (ClosureOperator.toClosureSpace C).toFamily ∅ := by
  rfl

end ClosureOperator

end ClosureSpace
