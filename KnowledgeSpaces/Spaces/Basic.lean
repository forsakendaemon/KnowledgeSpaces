/-
Copyright (c) 2026 David Allen. All rights reserved.
Not for public release.
Authors: David Allen
-/

module

public import KnowledgeSpaces.Structures.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.BooleanAlgebra.Set

/-!
# Knowledge Spaces

This file is a fairly on-to-one conversion of the later portions of
Chapter 1 - "Knowledge Structures and Spaces" of Knowledge Spaces by Doignon and Falmagne
having to do with Knowledge Spaces.

Doignon, J.-P., & Falmagne, J.-C. (1999). *Knowledge spaces*. Springer.
-/

universe u

variable {α : Type u}

public section

structure KSpace {α} extends @KStruct α where
  closed_union : ∀ x ∈ States, ∀ y ∈ States, x ∪ y ∈ States

lemma empty_in_powerset :
  ∅ ∈ 𝒫 X := by
    apply Set.mem_powerset
    apply Set.empty_subset

lemma self_in_powerset :
  X ∈ 𝒫 X := by
    apply Set.mem_powerset
    apply subset_refl


def KStruct.Dual {α} {k : @KStruct α} : @KStruct α :=
  let D := ⋃₀ k.States
  let Kbar := {x ∈ 𝒫 D | (D \ x) ∈ k.States}
  have h₁ : D ∈ Kbar := by
    constructor
    · exact Set.mem_powerset (subset_refl D)
    · rw [Set.sdiff_self]
      exact k.empty_in_states
  have h₂ : ⋃₀ Kbar = D := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_sUnion.mp hx with ⟨s, hsKbar, hxs⟩
      exact hsKbar.left hxs
    · intro hx
      exact Set.mem_sUnion.mpr ⟨D, h₁, hx⟩
  let hkbne : (⋃₀ Kbar).Nonempty := by
    rcases k.domain_nonempty with ⟨x, hx⟩
    exact ⟨x, Set.mem_sUnion.mpr ⟨D, h₁, hx⟩⟩
  let hkbce: ∅ ∈ Kbar := by
    constructor
    · exact empty_in_powerset
    · rw [Set.sdiff_empty]
      exact k.domain_in_states
  let hkbcu: ⋃₀ Kbar ∈ Kbar := by
    rw [h₂]
    exact h₁
  KStruct.mk Kbar hkbne hkbce hkbcu

abbrev Relation α := α -> α -> Prop

def relset (q : Set α) (r : Relation (Set α)) : Set (Set α) :=
  {k ∈ 𝒫 q | ∀ x ∈ 𝒫 q, ∀ y ∈ 𝒫 q, x.Nonempty -> y.Nonempty -> r x y -> x ∩ k = ∅ -> y ∩ k = ∅}

lemma relset_elem_subs_q (q : Set α) (r : Relation (Set α)) :
  ∀ x ∈ relset q r, x ⊆ q := by
  intro x hx
  rcases hx with ⟨ left, _ ⟩
  apply Set.mem_powerset left

theorem relset_contains_empty (q : Set α) (r : Relation (Set α)) :
  ∅ ∈ relset q r := by
  constructor
  · exact empty_in_powerset
  · intro x hx y hy xne yne rxy xde
    rw [Set.inter_comm]
    exact Set.empty_inter y

theorem relset_nonempty (q : Set α) (r : Relation (Set α)) :
  (relset q r).Nonempty := by
  exact Set.nonempty_of_mem (relset_contains_empty q r)

theorem relset_contains_q (q : Set α) (r : Relation (Set α)) :
  q ∈ relset q r := by
  constructor
  · exact self_in_powerset
  · intro x hx y hy xne yne rxy xde
    rcases xne with ⟨ a, ha ⟩
    have ha_empty : a ∈ (∅ : Set α) := by
      rw [← xde]
      exact ⟨ ha, hx ha ⟩
    exfalso
    exact ha_empty

theorem relset_union_nonempty (q : Set α) (r : Relation (Set α)) {hq : q.Nonempty} :
  (⋃₀ relset q r).Nonempty := by
  have h : q ∈ relset q r := relset_contains_q q r
  rcases hq with ⟨ a, ha ⟩ -- Creates an existence proof from Nonempty
  exact ⟨ a, Set.mem_sUnion.mpr ⟨ q, h, ha ⟩ ⟩

theorem relset_closed_union (q : Set α) (r : Relation (Set α)) :
  let rs := relset q r
  ∀ x ∈ rs, ∀ y ∈ rs, x ∪ y ∈ rs := by
  intro rs x hx y hy
  constructor
  · simp only [Set.mem_powerset_iff, Set.union_subset_iff]
    apply And.intro
    · exact relset_elem_subs_q q r x hx
    · exact relset_elem_subs_q q r y hy
  · intro z hz w hw zne wne rzw zde
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
    have hwdx : w ∩ x = ∅ := hx.right z hz w hw zne wne rzw hzdx
    have hwdy : w ∩ y = ∅ := hy.right z hz w hw zne wne rzw hzdy
    ext a
    constructor
    · intro ha
      rcases ha.right with hax | hay
      · have : a ∈ w ∩ x := ⟨ ha.left, hax ⟩
        rw [hwdx] at this
        exact this
      · have : a ∈ w ∩ y := ⟨ ha.left, hay ⟩
        rw [hwdy] at this
        exact this
    · intro ha
      exact False.elim ha

theorem relset_sunion_q (q : Set α) (r : Relation (Set α)) :
  ⋃₀ relset q r = q := by
    ext z
    constructor
    · simp only [Set.mem_sUnion, forall_exists_index, and_imp]
      intro x hx hz
      rw [relset] at hx
      rcases hx with ⟨ a, ha ⟩
      apply Set.mem_powerset a
      exact hz
    · intro hz
      rw [Set.mem_sUnion]
      exact ⟨ q, relset_contains_q q r, hz⟩

theorem relset_closed_sunion (q : Set α) (r : Relation (Set α)) :
  ⋃₀ relset q r ∈ relset q r := by
  rw [relset_sunion_q]
  exact relset_contains_q q r

def kspace_from_rel (q : Set α) (r : Relation (Set α)) {hq : q.Nonempty} : @KSpace α :=
  let rs := relset q r
  let kstruct := KStruct.mk
    rs
    (@relset_union_nonempty α q r hq)
    (relset_contains_empty q r)
    (relset_closed_sunion q r)
  let kscu :
    ∀ (x : Set α), x ∈ kstruct.States →
    ∀ (y : Set α), y ∈ kstruct.States →
    x ∪ y ∈ kstruct.States := by
      intro x hx y hy
      exact relset_closed_union q r x hx y hy
  KSpace.mk kstruct kscu
