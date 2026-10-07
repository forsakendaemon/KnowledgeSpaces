/-
Copyright (c) 2026 David Allen. All rights reserved.
Not for public release.
Authors: David Allen
-/

module

public import Mathlib.Data.Set.Basic
public import Mathlib.Basic.Rel

/-!
# Knowledge Space

Basic definition of a knowledge space.
-/

@[expose] public section

lemma empty_in_powerset :
  ∅ ∈ 𝒫 x := by
    apply Set.mem_powerset
    apply Set.empty_subset

lemma self_in_powerset :
  x ∈ 𝒫 x := by
    apply Set.mem_powerset
    apply subset_refl

abbrev Relation α := Rel α α
