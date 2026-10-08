/-
Copyright (c) 2026 David Allen. All rights reserved.
Not for public release.
Authors: David Allen
-/

module

import Mathlib.Data.Set.Basic
public import KnowledgeSpaces.KnowledgeSpace
public import KnowledgeSpaces.Util

/-!
# RelationSet

Basic definition of a Set induced on a space by a Relation. Note that the space must be nonempty.
-/

@[expose] public section

universe u

class RelationSet (X : Type u) where
  r : Relation (Set X)
  univ_nonempty : Nonempty X

section Defs

namespace RelationSet

variable {X : Type u} [RelationSet X] {x y : Set X} {p q : X}

def IsState : Set X -> Prop := fun (k) =>
  ∀ x y : Set X,
  ∀ z ∈ 𝒫 x, ∀ w ∈ 𝒫 y,
  z.Nonempty -> w.Nonempty ->
  r z w ->
  z ∩ k = ∅ -> w ∩ k = ∅

def States : Set (Set X) := {x | IsState x}

def Univ : Set X := Set.univ

theorem contains_empty :
  IsState (∅ : Set X) := by
  intro x y z hz w hw zne wne rzw zde
  rw [Set.inter_comm]
  exact Set.empty_inter w

theorem nonempty :
  Set.Nonempty (States : Set (Set X)) := by
  exact Set.nonempty_of_mem contains_empty

theorem contains_q :
  Univ ∈ (States : Set (Set X)) := by
  intro x y z hz w hw zne wne rzw zde
  rcases zne with ⟨ p, hp ⟩
  have hp_empty : p ∈ (∅ : Set X) := by
    rw [← zde]
    exact ⟨ hp, trivial ⟩
  exfalso
  exact hp_empty

theorem closed_union :
  x ∈ States -> y ∈ States -> x ∪ y ∈ States := by
  intro hx hy v u z hz w hw zne wne rzw zde
  have hzdx : z ∩ x = ∅ := by
    ext a
    constructor
    · intro ha
      have : a ∈ z ∩ (x ∪ y) := ⟨ ha.left, Or.inl ha.right ⟩
      rw [zde] at this
      exact this
    · intro ha
      exact False.elim ha
  have hzdy : z ∩ y = ∅ := by
    ext a
    constructor
    · intro ha
      have : a ∈ z ∩ (x ∪ y) := ⟨ ha.left, Or.inr ha.right ⟩
      rw [zde] at this
      exact this
    · intro ha
      exact False.elim ha
  have hwdx : w ∩ x = ∅ := hx v u z hz w hw zne wne rzw hzdx
  have hwdy : w ∩ y = ∅ := hy v u z hz w hw zne wne rzw hzdy
  ext p
  constructor
  · intro hp
    rcases hp.right with hpx | hpy
    · have : p ∈ w ∩ x := ⟨ hp.left, hpx ⟩
      rw [hwdx] at this
      exact this
    · have : p ∈ w ∩ y := ⟨ hp.left, hpy ⟩
      rw [hwdy] at this
      exact this
  · intro ha
    exact False.elim ha

theorem sunion_q :
  ⋃₀ (States : Set (Set X)) = Univ := by
    ext z
    constructor
    · simp only [Set.mem_sUnion, forall_exists_index, and_imp]
      intro x hx hz
      rw [States] at hx
      rw [Univ]
      exact Set.mem_univ x
    · intro hz
      rw [Set.mem_sUnion]
      exact ⟨ Univ, contains_q, hz⟩

theorem closed_sunion :
  ⋃₀ (States : Set (Set X)) ∈ States := by
  rw [sunion_q]
  exact contains_q

theorem union_nonempty : (⋃₀ (States : Set (Set X))).Nonempty := by
  simp only [Set.nonempty_sUnion]
  exact ⟨ Univ, contains_q, Set.nonempty_iff_univ_nonempty.mp univ_nonempty ⟩

instance {X : Type u} : Coe (RelationSet X) (Family X) where
  coe k := Family.mk k.IsState

instance {X : Type u} : Coe (RelationSet X) (KnowledgeSpace X) where
  coe k :=
    let fam : Family X := k
    letI : Family X := fam
    have h₁: (⋃₀ {x : Set X | Family.IsMember x}).Nonempty := union_nonempty
    have h₂: Family.IsMember (∅ : Set X) := contains_empty
    have h₃: Family.IsMember (⋃₀ {x : Set X | Family.IsMember x}) := closed_sunion
    have h₄ : ∀ {x y},
      Family.IsMember x → Family.IsMember y → Family.IsMember (x ∪ y) := by
      intro x y hx hy
      exact closed_union hx hy
    let kstruct : KnowledgeStructure X := KnowledgeStructure.mk h₁ h₂ h₃
    letI : KnowledgeStructure X := kstruct
    KnowledgeSpace.mk h₄

end RelationSet
