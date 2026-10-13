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
public import Mathlib.Algebra.Quotient

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

variable {X : Type u} [KnowledgeStructure X]

def IsMember : Set X -> Prop := Family.IsMember

namespace KnowledgeStructure

variable {x y : Set X} {p q : X}

public def States : Set (Set X) := {x | IsMember x}

public def Domain : Set X := ⋃₀ States

theorem states_subset_domain :
  IsMember x -> x ⊆ Domain := by
    intro h y hy
    exact Set.mem_sUnion.mpr ⟨ x, h, hy ⟩

theorem items_in_states_in_domain :
  IsMember x -> p ∈ x -> p ∈ Domain := by
    intro hx hp
    exact states_subset_domain hx hp

public def K_q (q : X) : Set (Set X) :=
    { x | IsMember x ∧ q ∈ x }

public def Notion (q : X) : Set X :=
  { p ∈ Domain | K_q p = K_q q}

public def Notions : Set (Set X) :=
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

def notionSetoid (X : Type u) [KnowledgeStructure X] : Setoid X where
  r p q := Notion p = Notion q
  iseqv := notion_equiv

abbrev QuotientDomain (X : Type u) [KnowledgeStructure X] :=
  Quotient (notionSetoid X)

def quotientMap (X : Type u) [KnowledgeStructure X] : X → QuotientDomain X :=
  Quotient.mk (notionSetoid X)

def quotientState (s : Set X) : Set (QuotientDomain X) :=
  quotientMap X '' s

def quotientStates (X : Type u) [KnowledgeStructure X] : Set (Set (QuotientDomain X)) :=
  {t | ∃ s, IsMember s ∧ t = quotientState s}

@[instance_reducible]
def quotientKnowledgeStructureByNotion (X : Type u) [KnowledgeStructure X] :
    KnowledgeStructure (QuotientDomain X) :=
  let Q := quotientStates X
  let fam : Family (QuotientDomain X) :=
    Family.mk (fun t => t ∈ Q)
  have h_empty : ∅ ∈ Q := by
    refine ⟨∅, KnowledgeStructure.empty_in_states, ?_⟩
    simp [quotientState]
  have h_domain_eq :
      ⋃₀ Q = quotientState Domain := by
    ext z
    constructor
    · intro hz
      rcases Set.mem_sUnion.mp hz with ⟨t, htQ, hzt⟩
      rcases htQ with ⟨s, hs, rfl⟩
      rcases hzt with ⟨x, hxs, rfl⟩
      exact ⟨x, items_in_states_in_domain hs hxs, rfl⟩
    · intro hz
      rcases hz with ⟨x, hxD, rfl⟩
      rcases Set.mem_sUnion.mp hxD with ⟨s, hs, hxs⟩
      exact Set.mem_sUnion.mpr
        ⟨quotientState s, ⟨s, hs, rfl⟩, ⟨x, hxs, rfl⟩⟩
  have h_nonempty : (⋃₀ Q).Nonempty := by
    rw [h_domain_eq]
    rcases (KnowledgeStructure.domain_nonempty (X := X)) with ⟨x, hx⟩
    exact ⟨quotientMap X x, ⟨x, hx, rfl⟩⟩
  have h_domain : ⋃₀ Q ∈ Q := by
    rw [h_domain_eq]
    exact ⟨Domain, KnowledgeStructure.domain_in_states (X := X), rfl⟩
  letI : Family (QuotientDomain X) := fam
  KnowledgeStructure.mk h_nonempty h_empty h_domain

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

public def restrict (A : Set X) : Set (Set A) :=
  {h | ∃ k : Set X, IsMember k ∧ h = Subtype.val ⁻¹' k}

@[instance_reducible]
def subKnowledgeStructure
    (A : Set X)
    (hAne : A.Nonempty)
    (hAsub : A ⊆ Domain) :
    KnowledgeStructure A :=
  let Q := restrict A
  have hne : (⋃₀ Q).Nonempty := by
    rcases hAne with ⟨ x, hxA ⟩
    refine ⟨ ⟨ x, hxA ⟩, ?_ ⟩
    let b : Set ↑A := Subtype.val ⁻¹' Domain
    have h₁ : b ∈ Q := ⟨ Domain, domain_in_states, rfl ⟩
    have h₂ : ∃ t ∈ Q, ⟨ x, hxA ⟩ ∈ t := ⟨ b, h₁, hAsub hxA ⟩
    exact Set.mem_sUnion.mpr h₂
  have hempty : ∅ ∈ Q := by
    exact ⟨ ∅, empty_in_states, rfl ⟩
  have hdomain : ⋃₀ Q ∈ Q := by
    refine ⟨ Domain, domain_in_states, ?_ ⟩
    ext a
    constructor
    · intro ha
      rw [Set.mem_preimage]
      rcases Set.mem_sUnion.mp ha with ⟨ s, hsQ, has ⟩
      rcases hsQ with ⟨ k, hk, rfl ⟩
      exact items_in_states_in_domain hk has
    · intro ha
      let b : Set ↑A := Subtype.val ⁻¹' Domain
      have h₁ : b ∈ Q := ⟨ Domain, domain_in_states, rfl ⟩
      have h₂ : ∃ t ∈ Q, a ∈ t := ⟨ b, h₁, hAsub a.property ⟩
      exact Set.mem_sUnion.mpr h₂
  let fam : Family A := Family.mk (fun h => h ∈ Q)
  letI : Family A := fam
  mk hne hempty hdomain

end KnowledgeStructure

public class CountableKStructure X extends KnowledgeStructure X where
  domain_countable : Countable X

public class EssentiallyCountableKStructure X extends KnowledgeStructure X where
  states_countable : Countable {x | IsMember x}

public class FiniteKStructure X extends
  KnowledgeStructure X, CountableKStructure X where
  domain_finite : Finite X
  domain_countable := by
    exact Countable.of_finite domain_finite

public class EssentiallyFiniteKStructure X extends
  KnowledgeStructure X, EssentiallyCountableKStructure X where
  states_finite : Finite {x | IsMember x}
  states_countable := by
    exact Countable.of_finite states_finite
