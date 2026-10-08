/-
Copyright (c) 2026 David Allen. All rights reserved.
Not for public release.
Authors: David Allen
-/

module

import Mathlib.Data.Set.Basic
public import Mathlib.Order.SetNotation

/-!
# Family

Basic definition of a family of sets.
-/

@[expose] public section

universe u

class Family (X : Type u) where
  IsMember : Set X -> Prop
