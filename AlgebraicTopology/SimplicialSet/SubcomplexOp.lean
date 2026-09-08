/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# The opposite of a subcomplex

-/

@[expose] public section

universe u

namespace SSet.Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

/-- The opposite of subcomplex, as a subcomplex of the opposite simplicial set. -/
/-
**SSet.Subcomplex.op** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：{X : _root_.SSet} → X.Subcomplex → X.op.Subcomplex
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of subcomplex, as a subcomplex of the opposite simplicial set.
-/
protected def op : X.op.Subcomplex where
  obj := A.obj
  map _ := A.map _
/-
**SSet.Subcomplex.mem_op_obj_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：mem_op_obj_iff {d : SimplexCategoryᵒᵖ} (x : X.op.obj d) : x in A.op.obj d 
↔ X.opObjEquiv x in A.obj d
参数：x : X.op.obj d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_op_obj_iff {d : SimplexCategoryᵒᵖ} (x : X.op.obj d) :
    x ∈ A.op.obj d ↔ X.opObjEquiv x ∈ A.obj d := Iff.rfl

end SSet.Subcomplex

