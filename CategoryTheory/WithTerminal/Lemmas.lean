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
/-
**CategoryTheory.WithTerminal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.WithTer
minal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCofilteredOrEmpty C] : IsCofiltered (WithTerminal C) where
  cone_objs x y :=
    match x, y with
    | star, y => ⟨y, default, 𝟙 y, trivial⟩
    | x, star => ⟨x, 𝟙 x, default, trivial⟩
    | of x, of y => ⟨.of <| min x y, minToLeft _ _, minToRight _ _, trivial⟩
  cone_maps x y f g :=
    match x, y with
    | star, _ => ⟨star, 𝟙 _, (IsIso.eq_comp_inv f).mp rfl⟩
    | x, star => ⟨x, 𝟙 _, Subsingleton.elim _ _⟩
    | of _, of _ => ⟨.of <| eq f g, eqHom _ _, eq_condition _ _⟩

end WithTerminal

namespace WithInitial

/-
**CategoryTheory.WithInitial.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.WithInit
ial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsFilteredOrEmpty C] : IsFiltered (WithInitial C) :=
  have := IsCofiltered.of_equivalence (opEquiv C).symm
  isFiltered_of_isCofiltered_op _

end WithInitial

end CategoryTheory

