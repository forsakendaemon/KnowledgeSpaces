/-
Copyright (c) 2026 David Allen. All rights reserved.
Not for public release.
Authors: David Allen
-/

module

import Mathlib.Data.Set.Basic
public import Mathlib.Order.SetNotation
public import KnowledgeSpaces.ClosureSpace

/-!
# Simple Closure Space

Basic definition of a simple closure space.
-/

@[expose] public section

universe u

class SimpleClosureSpace (X : Type u) extends ClosureSpace X where
  contains_empty : IsMember ∅
