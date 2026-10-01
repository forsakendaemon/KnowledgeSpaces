/-
Copyright (c) 2026 David Allen. All rights reserved.
Not for public release.
Authors: David Allen
-/

module

import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Order.SetNotation
import Mathlib.Order.Partition.Basic
import Mathlib.Basic.Countable.Basic

/-!
# Knowledge Structures

This file is a fairly on-to-one conversion of the initial portions of
Chapter 1 - "Knowledge Structures and Spaces" of Knowledge Spaces by Doignon and Falmagne
having to do with Knowledge Structures.

Doignon, J.-P., & Falmagne, J.-C. (1999). *Knowledge spaces*. Springer.
-/

public section

universe u

variable {α : Type u}

public structure KStruct {α} where
  States : Set (Set α)
  domain_nonempty : (⋃₀ States).Nonempty
  empty_in_states : ∅ ∈ States
  domain_in_states : ⋃₀ States ∈ States

public def Domain {α} (K : Set (Set α)) : Set α := ⋃₀ K

public def KStruct.Domain {α} {k : @KStruct α} : Set α := ⋃₀ k.States

public theorem states_subset_domain {α} {K : Set (Set α)} :
  ∀ s ∈ K, s ⊆ Domain K := by
    intro s h x hx
    exact Set.mem_sUnion.mpr ⟨ s, h, hx ⟩

public theorem items_in_states_in_domain {α} {K : Set (Set α)} :
  ∀ s ∈ K, ∀ i ∈ s, i ∈ (Domain K) := by
    intro s h x hx
    exact states_subset_domain s h hx

public def KStruct.K_q {α} {k : @KStruct α} (q : α) : Set (Set α) :=
    { x ∈ k.States | q ∈ x }

public def KStruct.Notion {α} {k : @KStruct α} (q : α) : Set α :=
  { x ∈ k.Domain | k.K_q x = k.K_q q}

public def KStruct.Notions {α} {k : @KStruct α} : Set (Set α) :=
  { k.Notion x | x ∈ k.Domain}

public lemma notion_contains_q {α} {k : @KStruct α} :
  ∀ x ∈ k.Domain, x ∈ k.Notion x := by
    intro x hx
    constructor
    · exact hx
    · rfl

public theorem notion_nonempty {α} {k : @KStruct α} :
  ∀ x ∈ k.Domain, (k.Notion x).Nonempty := by
    intro x hx
    let h := notion_contains_q x hx
    exact Set.nonempty_def.mpr ⟨ x, h ⟩

public theorem notions_disjoint {α} {k : @KStruct α} :
  ∀ x ∈ k.Domain, ∀ y ∈ k.Domain,
  (k.Notion x = k.Notion y) ∨ (Disjoint (k.Notion x) (k.Notion y)) := by
    intro x hx y hy
    by_cases h : k.K_q x = k.K_q y
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

public theorem notions_cover {α}
  (k : @KStruct α) : ⋃₀ k.Notions = k.Domain := by
    ext z
    constructor
    · intro hz
      rcases Set.mem_sUnion.mp hz with ⟨ n, hn, hzn ⟩
      rcases hn with ⟨ x, hx, rfl ⟩
      exact hzn.left
    · intro hz
      let hzn := notion_contains_q z hz
      exact Set.mem_sUnion.mpr ⟨ k.Notion z, ⟨ z, hz, rfl ⟩, hzn ⟩

public theorem notions_nonempty {α}
  (k : @KStruct α) : (⋃₀ k.Notions).Nonempty := by
    rw [notions_cover k]
    exact k.domain_nonempty

public def notion_rel {α} (k : @KStruct α) : α -> α -> Prop :=
  fun a b => (k.Notion a) = (k.Notion b)

public theorem notion_equiv {α} {k : @KStruct α} :
  Equivalence (notion_rel k) := {
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

public lemma notion_eq_of_K_q_eq {α} {k : @KStruct α} {x y : α}
    (h : k.K_q x = k.K_q y) : k.Notion x = k.Notion y := by
  ext z
  constructor
  · intro hz
    exact ⟨hz.left, hz.right.trans h⟩
  · intro hz
    exact ⟨hz.left, hz.right.trans h.symm⟩

public lemma notion_eq_of_mem_notion {α} {k : @KStruct α} {x y : α}
  (h : y ∈ k.Notion x) : k.Notion y = k.Notion x :=
  notion_eq_of_K_q_eq h.right

public lemma notions_state_singleton {α} {k : @KStruct α} {y : Set α}
  (hy : y ∈ k.Notions) : {k.Notion z | z ∈ y} = {y} := by
  rcases hy with ⟨x, hx, rfl⟩
  ext n
  constructor
  · intro hn
    rcases hn with ⟨z, hz, rfl⟩
    exact Set.mem_singleton_iff.mpr (notion_eq_of_mem_notion hz)
  · intro hn
    have hn' : n = k.Notion x := Set.mem_singleton_iff.mp hn
    subst n
    exact ⟨x, notion_contains_q x hx, rfl⟩

public structure DiscKStruct {α} extends @KStruct α where
  atomic_notions : ∀ x ∈ toKStruct.Domain, (toKStruct.Notion x) = {x}

public instance : Coe (@KStruct α) (@DiscKStruct (Set α)) where
  coe k :=
    let Kstar := {{k.Notion x | x ∈ y} | y ∈ k.Notions}
    let Ustar := ⋃₀ Kstar
    let Kcomp : Set (Set (Set α)):= Kstar ∪ {Ustar, ∅}
    let hkcne : (⋃₀ Kcomp).Nonempty := by
      rcases k.domain_nonempty with ⟨ x, hx ⟩
      refine ⟨ k.Notion x, ?_ ⟩
      exact Set.mem_sUnion.mpr
        ⟨ {k.Notion z | z ∈ k.Notion x},
          Or.inl ⟨ k.Notion x, ⟨ x, hx, rfl ⟩, rfl ⟩,
          ⟨ x, notion_contains_q x hx, rfl ⟩ ⟩
    let hkcce : ∅ ∈ Kcomp := by
      exact Or.inr (by simp)
    let hkccu : ⋃₀ Kcomp ∈ Kcomp := by
      exact Or.inr (by simp [Kcomp, Ustar])
    let ks : KStruct := KStruct.mk Kcomp hkcne hkcce hkccu
    let hksan : ∀ x ∈ ks.Domain, (ks.Notion x) = {x} := by
      intro x hx
      ext y
      constructor
      · intro hy
        have hxKcomp : x ∈ ⋃₀ Kcomp := by
          change x ∈ ⋃₀ Kcomp at hx
          exact hx
        have hxUstar : x ∈ Ustar := by
          rcases Set.mem_sUnion.mp hxKcomp with ⟨ s, hsKcomp, hxs ⟩
          rcases hsKcomp with hsKstar | hsRight
          · exact Set.mem_sUnion.mpr ⟨ s, hsKstar, hxs ⟩
          · rcases (by simpa using hsRight : s = Ustar ∨ s = ∅) with rfl | rfl
            · exact hxs
            · simp at hxs
        rcases Set.mem_sUnion.mp hxUstar with ⟨ s, hsKstar, hxs ⟩
        rcases hsKstar with ⟨ n, hnNotions, rfl ⟩
        have hsingle : {k.Notion z | z ∈ n} = {n} :=
          notions_state_singleton hnNotions
        have hstate_mem : {k.Notion z | z ∈ n} ∈ Kcomp :=
          Or.inl ⟨ n, hnNotions, rfl ⟩
        have hstate_in_Kqx : {k.Notion z | z ∈ n} ∈ ks.K_q x :=
          ⟨ hstate_mem, hxs ⟩
        have hstate_in_Kqy : {k.Notion z | z ∈ n} ∈ ks.K_q y := by
          simpa [hy.right] using hstate_in_Kqx
        have hx_single : x ∈ ({n} : Set (Set α)) := by
          simpa [hsingle] using hxs
        have hy_single : y ∈ ({n} : Set (Set α)) := by
          simpa [hsingle] using hstate_in_Kqy.right
        have hx_eq : x = n := Set.mem_singleton_iff.mp hx_single
        have hy_eq : y = n := Set.mem_singleton_iff.mp hy_single
        exact Set.mem_singleton_iff.mpr (hy_eq.trans hx_eq.symm)
      · intro hy
        have hyx : y = x := Set.mem_singleton_iff.mp hy
        subst y
        exact notion_contains_q x hx
    DiscKStruct.mk ks hksan

public def KStruct.isFinite {α} {k : @KStruct α} : Prop := Finite (k.Domain)

public def KStruct.isEssentiallyFinite {α} {k : @KStruct α} : Prop := Countable (k.States)

public def KStruct.isCountable {α} {k : @KStruct α} : Prop := Finite (k.Domain)

public def KStruct.isEssentiallyCountable {α} {k : @KStruct α} : Prop := Countable (k.States)
