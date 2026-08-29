/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.WithTerminal.Basic

/-!
# Further lemmas on `WithTerminal`

These lemmas and instances need more imports.
-/

public section

namespace CategoryTheory

variable {C : Type*} [Category* C]

namespace WithTerminal

open IsCofiltered in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCofilteredOrEmpty
  signature: C] : IsCofiltered (WithTerminal C) where
  body: match x, y with
    | star, y => ⟨y, default, 𝟙 y, trivial⟩
    | x, star => ⟨x, 𝟙 x, default, trivial⟩
| of x, of y => ⟨.of min x y, minToLeft _ _, minToRight _ _, trivial⟩
  cone_maps x y f g :=
    match x, y with
    | star, _ => ⟨star, 𝟙 _, (IsIso.eq_comp_inv f).mp rfl⟩
    | x, star => ⟨x, 𝟙 _

中文:
实例 [IsCofilteredOrEmpty
  签名: C] : IsCofiltered (WithTerminal C) where
  定义体: match x, y with
    | star, y => ⟨y, default, 𝟙 y, trivial⟩
    | x, star => ⟨x, 𝟙 x, default, trivial⟩
| of x, of y => ⟨.of min x y, minToLeft _ _, minToRight _ _, trivial⟩
  cone_maps x y f g :=
    match x, y with
    | star, _ => ⟨star, 𝟙 _, (IsIso.eq_comp_inv f).mp rfl⟩
    | x, star => ⟨x, 𝟙 _

Depends on / 依赖: IsIso.eq_comp_inv, Subsingleton, Subsingleton.elim, cone_maps, eq_comp_inv, eq_condition, minToLeft, minToRight
-/
instance [IsCofilteredOrEmpty C] : IsCofiltered (WithTerminal C) where
  cone_objs x y :=
    match x, y with
    | star, y => ⟨y, default, 𝟙 y, trivial⟩
    | x, star => ⟨x, 𝟙 x, default, trivial⟩
| of x, of y => ⟨.of min x y, minToLeft _ _, minToRight _ _, trivial⟩
  cone_maps x y f g :=
    match x, y with
    | star, _ => ⟨star, 𝟙 _, (IsIso.eq_comp_inv f).mp rfl⟩
    | x, star => ⟨x, 𝟙 _, Subsingleton.elim _ _⟩
| of _, of _ => ⟨.of eq f g, eqHom _ _, eq_condition _ _⟩

end WithTerminal

namespace WithInitial

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFilteredOrEmpty
  signature: C] : IsFiltered (WithInitial C)
  body: have := IsCofiltered.of_equivalence (opEquiv C).symm
  isFiltered_of_isCofiltered_op _

中文:
实例 [IsFilteredOrEmpty
  签名: C] : IsFiltered (WithInitial C)
  定义体: have := IsCofiltered.of_equivalence (opEquiv C).symm
  isFiltered_of_isCofiltered_op _

Depends on / 依赖: IsCofiltered, IsCofiltered.of_equivalence, isFiltered_of_isCofiltered_op, of_equivalence, opEquiv
-/
instance [IsFilteredOrEmpty C] : IsFiltered (WithInitial C) :=
  have := IsCofiltered.of_equivalence (opEquiv C).symm
  isFiltered_of_isCofiltered_op _

end WithInitial

end CategoryTheory
