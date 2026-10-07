/-
Copyright (c) 2026 David Allen. All rights reserved.
Not for public release.
Authors: David Allen
-/

module

import Mathlib.Data.Set.Basic
public import Mathlib.Order.SetNotation
public import KnowledgeSpaces.Family

/-!
# Closure Space

Basic definition of a closure space.
-/

@[expose] public section

universe u

class ClosureSpace (X : Type u) extends Family X where
  ground_in_carrier : IsMember (⋃₀ {x : Set X | IsMember x})
  closed_intersect : IsMember x -> IsMember y -> IsMember (x ∩ y)
