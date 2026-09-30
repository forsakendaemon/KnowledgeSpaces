/-
Copyright (c) 2026 David Allen. All rights reserved.
Not for public release.
Authors: David Allen
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Disjoint
import Mathlib.Order.SetNotation
import Mathlib.Order.Partition.Basic
-- import Mathlib.Data.Setoid.Partition

/-!
# Knowledge Spaces

-/

structure KStruct {α} (States : Set (Set α)) where
  domain_nonempty : (⋃₀ States).Nonempty
  empty_in_states : ∅ ∈ States
  domain_in_states : ⋃₀ States ∈ States

def Domain {α} {K : Set (Set α)} (_k : KStruct K) : Set α := ⋃₀ K

def States {α} {K : Set (Set α)} (_k : KStruct K) : Set (Set α) := K

theorem states_subset_domain {α} {K : Set (Set α)} :
  (k : KStruct K) -> ∀ s ∈ K, s ⊆ Domain k :=
  by
    intro struct s h x hx
    exact Set.mem_sUnion.mpr ⟨ s, h, hx ⟩

theorem items_in_states_in_domain {α} {K : Set (Set α)} :
  (k : KStruct K) -> ∀ s ∈ K, ∀ i ∈ s, i ∈ (Domain k) :=
  by
    intro struct s h x hx
    exact states_subset_domain struct s h hx

def K_q {α} {K : Set (Set α)} (k : KStruct K) (q : α) : Set (Set α) :=
  { x ∈ States k | q ∈ x }

def Notion {α} {K : Set (Set α)} (k : KStruct K) (q : α) : Set α :=
  { x ∈ Domain k | K_q k x = K_q k q}

lemma notion_contains_q {α} {K : Set (Set α)} (k : KStruct K) :
  ∀ x ∈ Domain k, x ∈ Notion k x :=
  by
    intro x hx
    constructor
    · exact hx
    · rfl

theorem notion_disjoint {α} {K : Set (Set α)} (k : KStruct K) :
  ∀ x ∈ Domain k, ∀ y ∈ Domain k,
  (Notion k x = Notion k y) ∨ (Disjoint (Notion k x) (Notion k y)) :=
  by
    intro x hx y hy
    by_cases h : K_q k x = K_q k y
    · left
      ext z
      constructor
      · intro hz
        exact ⟨hz.left, hz.right.trans h⟩
      · intro hz
        exact ⟨hz.left, hz.right.trans h.symm⟩
    · right
      rw [Set.disjoint_left]
      intro z hzx hzy
      exact h (hzx.right.symm.trans hzy.right)

theorem notion_cover {α} {K : Set (Set α)} (k : KStruct K) :
  ⋃₀ {Notion k x | x ∈ Domain k} = Domain k :=
  by
    ext z
    constructor
    · intro hz
      rcases Set.mem_sUnion.mp hz with ⟨ n, hn, hzn ⟩
      rcases hn with ⟨ x, hx, rfl ⟩
      exact hzn.left
    · intro hz
      let hzn := notion_contains_q k z hz
      exact Set.mem_sUnion.mpr ⟨ Notion k z, ⟨ z, hz, rfl ⟩, hzn ⟩

variable {α : Type} (r : α → α → Prop)

def notion_rel {α} {K : Set (Set α)} (k : KStruct K) : α -> α -> Prop :=
  fun a b => (Notion k a) = (Notion k b)

theorem notion_equiv {α} {K : Set (Set α)} {k : KStruct K} : Equivalence (notion_rel k) := {
  refl := by    -- Prove ∀ x, r x x
    intro x
    rfl,
  symm := by    -- Prove ∀ x y, r x y → r y x
    intro x y h
    exact h.symm,
  trans := by   -- Prove ∀ x y z, r x y → r y z → r x z
    intro x y z hxy hyz
    exact hxy.trans hyz
}

-- structure DiscKStruct (States : Set (Set α)) extends KStruct States where
--   atomic_notions := {Notion x | x ∈ ⋃₀ States}
