/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Discrete.Basic
/-!

# Discrete categories are groupoids
-/

public section

namespace CategoryTheory

variable {C : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Groupoid (Discrete C)
  body: { inv := fun h => ⟨⟨h.1.1.symm⟩⟩ }

中文:
实例 :
  签名: 群胚 (离散 C)
  定义体: { inv := fun h => ⟨⟨h.1.1.symm⟩⟩ }
-/
instance : Groupoid (Discrete C) := { inv := fun h => ⟨⟨h.1.1.symm⟩⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Category*
  signature: C] [IsDiscrete C] : IsGroupoid C where

中文:
实例 [范畴*
  签名: C] [是离散 C] : 是群胚 C where
-/
instance [Category* C] [IsDiscrete C] : IsGroupoid C where

end CategoryTheory
