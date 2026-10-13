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
public import KnowledgeSpaces.KnowledgeStructure
public import Mathlib.Basic.Rel
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Algebra.Quotient

/-!
# Discriminative Knowledge Structure

Basic definition of a discriminative knowledge structure.
-/

@[expose] public section

universe u

structure DiscriminativeKStructure (X : Type u) extends KnowledgeStructure X where
  atomic_notions :
    ∀ p, p ∈ toKnowledgeStructure.Domain ->
    toKnowledgeStructure.Notion p = {p}

section Defs

variable {X : Type u} [KnowledgeStructure X]

def Domain : Set X := KnowledgeStructure.Domain

def Notion : X -> Set X := KnowledgeStructure.Notion

def Notions : Set (Set X) := KnowledgeStructure.Notions

def K_q : X -> Set (Set X) := KnowledgeStructure.K_q

namespace DiscriminativeKStructure

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
          ⟨ x, k.notion_contains_q hx, rfl ⟩ ⟩
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
          k.notions_state_singleton (X := X) (x := n) hnNotions
        have hstate_mem : {Notion z | z ∈ n} ∈ Kcomp :=
          Or.inl ⟨ n, hnNotions, rfl ⟩
        have hstate_in_Kqx : {Notion z | z ∈ n} ∈ @K_q (Set X) ks x := by
          constructor
          · change {Notion z | z ∈ n} ∈ Kcomp
            exact hstate_mem
          · exact hxs
        have hstate_in_Kqy : {Notion z | z ∈ n} ∈ @K_q (Set X) ks y := by
          have hK :
              @K_q (Set X) ks y = @K_q (Set X) ks x := hy.right
          exact hK.symm ▸ hstate_in_Kqx
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
        exact @ks.notion_contains_q (Set X) x hx
    mk ks hksan

def subKnowledgeStructure
    (dk : DiscriminativeKStructure X)
    (A : Set X)
    (hAne : A.Nonempty)
    (hAsub : A ⊆ dk.Domain) :
    DiscriminativeKStructure A :=
  letI : KnowledgeStructure X := dk.toKnowledgeStructure
  let ks : KnowledgeStructure A := .subKnowledgeStructure A hAne hAsub
  let hatomic : ∀ p, p ∈ ks.Domain -> ks.Notion p = {p} := by
    intro p hp
    ext q
    constructor
    · intro hq
      have hK : dk.K_q q.val = dk.K_q p.val := by
        ext s
        constructor
        · intro hs
          have hsSubQ : Subtype.val ⁻¹' s ∈ ks.K_q q := by
            constructor
            · have hmem : Subtype.val ⁻¹' s ∈ dk.restrict A :=
                ⟨ s, hs.left, rfl ⟩
              change Subtype.val ⁻¹' s ∈ KnowledgeStructure.restrict A
              exact hmem
            · exact hs.right
          have hsSubP : Subtype.val ⁻¹' s ∈ ks.K_q p := by
            have hEq : ks.K_q q = ks.K_q p := hq.right
            exact hEq ▸ hsSubQ
          exact ⟨ hs.left, hsSubP.right ⟩
        · intro hs
          have hsSubP : Subtype.val ⁻¹' s ∈ ks.K_q p := by
            constructor
            · have hmem : Subtype.val ⁻¹' s ∈ KnowledgeStructure.restrict A :=
                ⟨ s, hs.left, rfl ⟩
              change Subtype.val ⁻¹' s ∈ KnowledgeStructure.restrict A
              exact hmem
            · exact hs.right
          have hsSubQ : Subtype.val ⁻¹' s ∈ ks.K_q q := by
            have hEq : ks.K_q q = ks.K_q p := hq.right
            exact hEq.symm ▸ hsSubP
          exact ⟨ hs.left, hsSubQ.right ⟩
      have hqOrig : q.val ∈ dk.Notion p.val :=
        ⟨ hAsub q.property, hK ⟩
      have hqSingleton : q.val ∈ ({p.val} : Set X) := by
        simpa [dk.atomic_notions p.val (hAsub p.property)] using hqOrig
      exact Set.mem_singleton_iff.mpr
        (Subtype.ext (Set.mem_singleton_iff.mp hqSingleton))
    · intro hq
      have hqp : q = p := Set.mem_singleton_iff.mp hq
      subst q
      exact ks.notion_contains_q hp
  mk ks hatomic

end DiscriminativeKStructure

class FiniteDKStructure X extends
  DiscriminativeKStructure X, FiniteKStructure X

class EssentiallyFiniteDKStructure X extends
  DiscriminativeKStructure X, EssentiallyFiniteKStructure X

class CountableDKStructure X extends
  DiscriminativeKStructure X, CountableKStructure X

class EssentiallyCountableDKStructure X extends
  DiscriminativeKStructure X, EssentiallyCountableKStructure X
