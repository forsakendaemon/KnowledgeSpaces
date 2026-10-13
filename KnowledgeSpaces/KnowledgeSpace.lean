/-
Copyright (c) 2026 David Allen. All rights reserved.
Not for public release.
Authors: David Allen
-/

module

import Mathlib.Data.Set.Basic
import KnowledgeSpaces.Util
public import KnowledgeSpaces.KnowledgeStructure

/-!
# Knowledge Space

Basic definition of a knowledge space.
-/

@[expose] public section

universe u

class KnowledgeSpace (X : Type u) extends KnowledgeStructure X where
  closed_union : IsMember x -> IsMember y -> IsMember (x ∪ y)

section Defs

namespace KnowledgeSpace

variable {X : Type u} [KnowledgeSpace X] {x y : Set X} {p q : X}

def Domain : Set X := KnowledgeStructure.Domain

def States : Set (Set X) := KnowledgeStructure.States

def restrict : (A : Set X) -> Set (Set ↑A) := KnowledgeStructure.restrict

@[instance_reducible]
def Dual :=
  let Kbar := {x ∈ 𝒫 Domain | (Domain \ x) ∈ States}
  have h₁ : Domain ∈ Kbar := by
    constructor
    · exact Set.mem_powerset (subset_refl Domain)
    · rw [Set.sdiff_self]
      exact KnowledgeStructure.empty_in_states
  have h₂ : ⋃₀ Kbar = Domain := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_sUnion.mp hx with ⟨ s, hsKbar, hxs ⟩
      exact hsKbar.left hxs
    · intro hx
      exact Set.mem_sUnion.mpr ⟨ Domain, h₁, hx ⟩
  let hkbne : (⋃₀ Kbar).Nonempty := by
    rw [h₂]
    exact KnowledgeStructure.domain_nonempty
  let hkbce: ∅ ∈ Kbar := by
    constructor
    · exact empty_in_powerset
    · rw [Set.sdiff_empty]
      exact KnowledgeStructure.domain_in_states
  let hkbcu: ⋃₀ Kbar ∈ Kbar := by
    rw [h₂]
    exact h₁
  let fam : Family X := Family.mk (fun s => s ∈ Kbar)
  letI : Family X := fam
  KnowledgeStructure.mk hkbne hkbce hkbcu

@[instance_reducible]
def subKnowledgeStructure
    (dk : KnowledgeSpace X)
    (A : Set X)
    (hAne : A.Nonempty)
    (hAsub : A ⊆ dk.Domain) :
    KnowledgeSpace A :=
  letI : KnowledgeStructure X := dk.toKnowledgeStructure
  let ks : KnowledgeStructure A := .subKnowledgeStructure A hAne hAsub
  let h : (∀ {x y : Set A}, ks.IsMember x → ks.IsMember y → ks.IsMember (x ∪ y)) := by
    intro x y hx hy
    change x ∈ restrict A at hx
    change y ∈ restrict A at hy
    change x ∪ y ∈ restrict A
    rcases hx with ⟨ kx, hkx, rfl ⟩
    rcases hy with ⟨ ky, hky, rfl ⟩
    refine ⟨ kx ∪ ky, closed_union hkx hky, ?_ ⟩
    ext a
    rfl
  mk h

end KnowledgeSpace
