/-
Copyright (c) 2026 David Allen. All rights reserved.
Not for public release.
Authors: David Allen
-/

module

import Mathlib.Data.Set.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.Basic.Rel

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort

/-!
# Knowledge Spaces

This file is a fairly on-to-one conversion of the later portions of
Chapter 1 - "Knowledge Structures and Spaces" of Knowledge Spaces by Doignon and Falmagne
having to do with Knowledge Spaces.

Doignon, J.-P., & Falmagne, J.-C. (1999). *Knowledge spaces*. Springer.
-/

public section

variable {α : Type}
abbrev Relation α := Rel α α

inductive TestType
  | A
  | B
  | C
  deriving DecidableEq, Repr

instance TestType.Fintype : Fintype TestType :=
  ⟨⟨{A, B, C}, by simp⟩, fun x => by cases x <;> simp⟩
