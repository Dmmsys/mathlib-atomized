/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Transport

/-!

# Transporting a closed monoidal structure along an equivalence of categories
-/

public section

open CategoryTheory Monoidal

namespace CategoryTheory.MonoidalClosed

/-
**CategoryTheory.MonoidalClosed.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monoi
dalClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {C D : Type*} [Category* C] [Category* D]
    (e : C ≌ D) [MonoidalCategory C] [MonoidalClosed C] :
    MonoidalClosed (Transported e) :=
  MonoidalClosed.ofEquiv _ (equivalenceTransported e).symm.toAdjunction

end CategoryTheory.MonoidalClosed

