/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# Cardinality of Subobject

If `X ⟶ Y` is a monomorphism, and the cardinality of `Subobject Y`
is `< κ`, then the cardinality of `Subobject X` is also `< κ`.

-/

public section

universe w v u

namespace CategoryTheory.Subobject

variable {C : Type u} [Category.{v} C]

/-
**CategoryTheory.Subobject.hasCardinalLT_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Subobject`。
形式化陈述：hasCardinalLT_of_mono {Y : C} {κ : Cardinal.{w}} (h : HasCardinalLT (Subob
ject Y) κ) {X : C} (f : X ⟶ Y) [Mono f] : HasCardinalLT (Subobject X) κ
参数：h : HasCardinalLT (Subobject Y) κ；f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasCardinalLT.of_injective`：of_injective (f : Y -> X) (hf : Function.Inj
ective f) : HasCardinalLT Y κ
· 使用引理 `CategoryTheory.Subobject.map_obj_injective`：map_obj_injective {X Y : C} 
(f : X ⟶ Y) [Mono f] : Function.Injective (Subobject.map f).obj
-/
lemma hasCardinalLT_of_mono {Y : C} {κ : Cardinal.{w}}
    (h : HasCardinalLT (Subobject Y) κ) {X : C} (f : X ⟶ Y) [Mono f] :
    HasCardinalLT (Subobject X) κ :=
  h.of_injective _ (map_obj_injective f)

end CategoryTheory.Subobject

