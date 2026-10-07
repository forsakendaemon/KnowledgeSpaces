/-
Copyright (c) 2026 David Allen. All rights reserved.
Not for public release.
Authors: David Allen
-/

module

import Mathlib.Data.Set.Basic
public import KnowledgeSpaces.Util
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Order.SetNotation
public import KnowledgeSpaces.Family
public import Mathlib.Basic.Rel
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Countable.Basic

/-!
# Knowledge Structure

Basic definition of a knowledge structure.
-/

@[expose] public section

universe u

class KnowledgeStructure (X : Type u) extends Family X where
  domain_nonempty : (⋃₀ {x | IsMember x}).Nonempty
  empty_in_states : IsMember ∅
  domain_in_states : IsMember (⋃₀ {x | IsMember x})

section Defs

variable {X : Type u} [KnowledgeStructure X] {x y : Set X} {p q : X}

def IsMember : Set X -> Prop := Family.IsMember

def States : Set (Set X) := {x | IsMember x}

def Domain : Set X := ⋃₀ States

theorem states_subset_domain :
  IsMember x -> x ⊆ Domain := by
    intro h y hy
    exact Set.mem_sUnion.mpr ⟨ x, h, hy ⟩

theorem items_in_states_in_domain :
  IsMember x -> p ∈ x -> p ∈ Domain := by
    intro hx hp
    exact states_subset_domain hx hp

def K_q (q : X) : Set (Set X) :=
    { x | IsMember x ∧ q ∈ x }

def Notion (q : X) : Set X :=
  { p ∈ Domain | K_q p = K_q q}

def Notions : Set (Set X) :=
  { Notion x | x ∈ Domain}

lemma notion_contains_q :
  q ∈ Domain -> q ∈ Notion q := by
    intro hx
    constructor
    · exact hx
    · rfl

theorem notion_nonempty :
  p ∈ Domain -> (Notion p).Nonempty := by
    intro hp
    let h := notion_contains_q hp
    exact Set.nonempty_def.mpr ⟨ p, h ⟩

theorem notions_disjoint :
  p ∈ Domain -> q ∈ Domain ->
  (Notion p = Notion q) ∨ (Disjoint (Notion p) (Notion q)) := by
    intro hp hq
    by_cases h : K_q p = K_q q
    · left
      ext z
      constructor
      · intro hz
        exact ⟨hz.left, hz.right.trans h⟩
      · intro hz
        exact ⟨hz.left, hz.right.trans h.symm⟩
    · right
      rw [Set.disjoint_left]
      intro z hzp hzq
      exact h (hzp.right.symm.trans hzq.right)

theorem notions_cover :
  ⋃₀ (Notions : Set (Set X)) = Domain := by
    ext z
    constructor
    · intro hz
      rcases Set.mem_sUnion.mp hz with ⟨ n, hn, hzn ⟩
      rcases hn with ⟨ x, hx, rfl ⟩
      exact hzn.left
    · intro hz
      let hzn := notion_contains_q hz
      exact Set.mem_sUnion.mpr ⟨ Notion z, ⟨ z, hz, rfl ⟩, hzn ⟩

theorem notions_nonempty :
  (⋃₀ (Notions : Set (Set X))).Nonempty := by
    rw [notions_cover]
    exact KnowledgeStructure.domain_nonempty

def notion_rel : Relation X :=
  fun (p q) => Notion p = Notion q

theorem notion_equiv :
  Equivalence (notion_rel : Relation X) := {
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

lemma notion_eq_of_K_q_eq :
  K_q p = K_q q -> Notion p = Notion q := by
  intro h
  ext z
  constructor
  · intro hz
    exact ⟨hz.left, hz.right.trans h⟩
  · intro hz
    exact ⟨hz.left, hz.right.trans h.symm⟩

lemma notion_eq_of_mem_notion :
  p ∈ Notion q -> Notion p = Notion q := by
  intro h
  exact notion_eq_of_K_q_eq h.right

lemma notions_state_singleton :
  x ∈ Notions -> {Notion p | p ∈ x} = {x} := by
  intro hx
  rcases hx with ⟨y, hy, rfl⟩
  ext n
  constructor
  · intro hn
    rcases hn with ⟨z, hz, rfl⟩
    exact Set.mem_singleton_iff.mpr (notion_eq_of_mem_notion hz)
  · intro hn
    have hn' : n = Notion y := Set.mem_singleton_iff.mp hn
    subst n
    exact ⟨y, notion_contains_q hy, rfl⟩

structure DiscriminativeKStructure (X : Type u) extends KnowledgeStructure X where
  atomic_notions :
    ∀ p, p ∈ @Domain X toKnowledgeStructure ->
    @Notion X toKnowledgeStructure p = {p}

instance {X : Type u} : Coe (KnowledgeStructure X) (DiscriminativeKStructure (Set X)) where
  coe k :=
    letI : KnowledgeStructure X := k
    let Kstar := {{Notion x | x ∈ y} | y ∈ Notions}
    let Ustar := ⋃₀ Kstar
    let Kcomp : Set (Set (Set X)):= Kstar ∪ {Ustar, ∅}
    let hkcne : (⋃₀ Kcomp).Nonempty := by
      rcases k.domain_nonempty with ⟨ x, hx ⟩
      refine ⟨ Notion x, ?_ ⟩
      exact Set.mem_sUnion.mpr
        ⟨ {Notion z | z ∈ Notion x},
          Or.inl ⟨ Notion x, ⟨ x, hx, rfl ⟩, rfl ⟩,
          ⟨ x, notion_contains_q hx, rfl ⟩ ⟩
    let hkcce : ∅ ∈ Kcomp := by
      exact Or.inr (by simp)
    let hkccu : ⋃₀ Kcomp ∈ Kcomp := by
      have hUnion : ⋃₀ Kcomp = Ustar := by
        ext a
        constructor
        · intro ha
          rcases Set.mem_sUnion.mp ha with ⟨s, hsKcomp, has⟩
          rcases hsKcomp with hsKstar | hsRight
          · exact Set.mem_sUnion.mpr ⟨s, hsKstar, has⟩
          · rcases (by simpa using hsRight : s = Ustar ∨ s = ∅) with rfl | rfl
            · exact has
            · simp at has
        · intro ha
          exact Set.mem_sUnion.mpr ⟨Ustar, Or.inr (by simp), ha⟩
      exact Or.inr (by simp [hUnion])
    let fam : Family (Set X) := Family.mk (fun s => s ∈ Kcomp)
    let ks : KnowledgeStructure (Set X) := by
      letI : Family (Set X) := fam
      exact KnowledgeStructure.mk hkcne hkcce hkccu
    let hksan : ∀ x, x ∈ @Domain (Set X) ks -> (@Notion (Set X) ks x) = {x} := by
      intro x hx
      ext y
      constructor
      · intro hy
        have hxKcomp : x ∈ ⋃₀ Kcomp := by
          rcases Set.mem_sUnion.mp hx with ⟨s, hs, hxs⟩
          exact Set.mem_sUnion.mpr ⟨s, by
            change s ∈ Kcomp at hs
            exact hs, hxs⟩
        have hxUstar : x ∈ Ustar := by
          rcases Set.mem_sUnion.mp hxKcomp with ⟨ s, hsKcomp, hxs ⟩
          rcases hsKcomp with hsKstar | hsRight
          · exact Set.mem_sUnion.mpr ⟨ s, hsKstar, hxs ⟩
          · rcases (by simpa using hsRight : s = Ustar ∨ s = ∅) with rfl | rfl
            · exact hxs
            · simp at hxs
        rcases Set.mem_sUnion.mp hxUstar with ⟨ s, hsKstar, hxs ⟩
        rcases hsKstar with ⟨ n, hnNotions, rfl ⟩
        have hsingle : {Notion z | z ∈ n} = {n} :=
          notions_state_singleton (X := X) (x := n) hnNotions
        have hstate_mem : {Notion z | z ∈ n} ∈ Kcomp :=
          Or.inl ⟨ n, hnNotions, rfl ⟩
        have hstate_in_Kqx : {Notion z | z ∈ n} ∈ @K_q (Set X) ks x := by
          constructor
          · change {Notion z | z ∈ n} ∈ Kcomp
            exact hstate_mem
          · exact hxs
        have hstate_in_Kqy : {Notion z | z ∈ n} ∈ @K_q (Set X) ks y := by
          simpa [hy.right] using hstate_in_Kqx
        have hx_single : x ∈ ({n} : Set (Set X)) := by
          simpa [hsingle] using hxs
        have hy_single : y ∈ ({n} : Set (Set X)) := by
          simpa [hsingle] using hstate_in_Kqy.right
        have hx_eq : x = n := Set.mem_singleton_iff.mp hx_single
        have hy_eq : y = n := Set.mem_singleton_iff.mp hy_single
        exact Set.mem_singleton_iff.mpr (hy_eq.trans hx_eq.symm)
      · intro hy
        have hyx : y = x := Set.mem_singleton_iff.mp hy
        subst y
        exact @notion_contains_q (Set X) ks x hx
    DiscriminativeKStructure.mk ks hksan

structure FiniteKStructure X extends KnowledgeStructure X where
  domain_finite : Finite X

structure EssentiallyFiniteKStructure X extends KnowledgeStructure X where
  states_finite : Finite {x | IsMember x}

structure CountableKStructure X extends KnowledgeStructure X where
  domain_finite : Countable X

structure EssentiallyCountableKStructure X extends KnowledgeStructure X where
  states_finite : Countable {x | IsMember x}
