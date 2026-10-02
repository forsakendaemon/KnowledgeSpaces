/-
Copyright (c) 2026 David Allen. All rights reserved.
Not for public release.
Authors: David Allen
-/

module

public import KnowledgeSpaces.Structures.Basic
import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Fintype.Powerset
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

structure RelSet where
  q : Set α
  r : Relation (Set α)

def RelSet.states (rs : @RelSet α) : Set (Set α) :=
  {
    k ∈ 𝒫 rs.q |
    ∀ x ∈ 𝒫 rs.q, ∀ y ∈ 𝒫 rs.q,
    x.Nonempty -> y.Nonempty ->
    rs.r x y ->
    x ∩ k = ∅ -> y ∩ k = ∅
  }

theorem RelSet.elem_subs_q (rs : @RelSet α) :
  ∀ x ∈ rs.states, x ⊆ rs.q := by
  intro x hx
  rcases hx with ⟨ left, _ ⟩
  apply Set.mem_powerset left

theorem RelSet.contains_empty (rs : @RelSet α) :
  ∅ ∈ rs.states := by
  constructor
  · exact empty_in_powerset
  · intro x hx y hy xne yne rxy xde
    rw [Set.inter_comm]
    exact Set.empty_inter y

theorem RelSet.nonempty (rs : @RelSet α) :
  rs.states.Nonempty := by
  exact Set.nonempty_of_mem rs.contains_empty

theorem RelSet.contains_q (rs : @RelSet α) :
  rs.q ∈ rs.states := by
  constructor
  · exact self_in_powerset
  · intro x hx y hy xne yne rxy xde
    rcases xne with ⟨ a, ha ⟩
    have ha_empty : a ∈ (∅ : Set α) := by
      rw [← xde]
      exact ⟨ ha, hx ha ⟩
    exfalso
    exact ha_empty

theorem RelSet.closed_union (rs : @RelSet α) :
  x ∈ rs.states -> y ∈ rs.states -> x ∪ y ∈ rs.states := by
  intro hx hy
  constructor
  · simp only [Set.mem_powerset_iff, Set.union_subset_iff]
    apply And.intro
    · exact rs.elem_subs_q x hx
    · exact rs.elem_subs_q y hy
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

theorem RelSet.sunion_q (rs : @RelSet α) :
  ⋃₀ rs.states = rs.q := by
    ext z
    constructor
    · simp only [Set.mem_sUnion, forall_exists_index, and_imp]
      intro x hx hz
      rw [RelSet.states] at hx
      rcases hx with ⟨ a, ha ⟩
      apply Set.mem_powerset a
      exact hz
    · intro hz
      rw [Set.mem_sUnion]
      exact ⟨ rs.q, rs.contains_q, hz⟩

theorem RelSet.closed_sunion (rs : @RelSet α) :
  ⋃₀ rs.states ∈ rs.states := by
  rw [rs.sunion_q]
  exact rs.contains_q

theorem RelSet.union_nonempty (rs : @RelSet α) {hq : rs.q.Nonempty} :
  (⋃₀ rs.states).Nonempty := by
  rcases hq with ⟨ a, ha ⟩ -- Creates an existence proof from Nonempty
  exact ⟨ a, Set.mem_sUnion.mpr ⟨ rs.q, rs.contains_q, ha ⟩ ⟩

def kspace_from_rel (rs : @RelSet α) {hq : rs.q.Nonempty} : @KSpace α :=
  let kstruct := KStruct.mk
    rs.states
    (rs.union_nonempty (hq := hq))
    rs.contains_empty
    rs.closed_sunion
  let kscu :
    ∀ (x : Set α), x ∈ kstruct.States →
    ∀ (y : Set α), y ∈ kstruct.States →
    x ∪ y ∈ kstruct.States := by
      intro x hx y hy
      exact rs.closed_union hx hy
  KSpace.mk kstruct kscu

def q : Set ℕ := {1, 2, 3}
def r (x y : Set ℕ) : Prop :=
  let test : Set (Set ℕ × Set ℕ):= {({1, 2}, {3})}
  (x, y) ∈ test
def rs := RelSet.mk q r

lemma finite_powerset_of_finite {s : Set α} (hs : Set.Finite s) :
  Set.Finite (𝒫 s) := by
  classical
  let _ : Finite s := hs.to_subtype
  let f : Set s → Set α := fun t => Subtype.val '' t
  have hf : Set.Finite (f '' Set.univ) := (Set.finite_univ (α := Set s)).image f
  rw [show 𝒫 s = f '' Set.univ by
    ext t
    constructor
    · intro ht
      refine ⟨Subtype.val ⁻¹' t, trivial, ?_⟩
      ext a
      constructor
      · intro ha
        rcases ha with ⟨a', ha't, rfl⟩
        exact ha't
      · intro ha
        exact ⟨⟨a, ht ha⟩, ha, rfl⟩
    · intro ht
      rcases ht with ⟨u, _hu, rfl⟩
      intro a ha
      rcases ha with ⟨a', _ha'u, rfl⟩
      exact a'.property]
  exact hf

theorem rs_states_finite : Set.Finite rs.states := by
  have hq : Set.Finite rs.q := by
    unfold rs q
    simp
  exact (finite_powerset_of_finite hq).subset (rs.elem_subs_q)


#check rs_states_finite.toFinset
