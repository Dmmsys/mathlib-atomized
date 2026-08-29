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

/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: : X.op.Subcomplex where
  body: A.obj
  map _ := A.map _

中文:
定义 op
  签名: : X.op.Subcomplex where
  定义体: A.obj
  map _ := A.map _
-/
protected def op : X.op.Subcomplex where
  obj := A.obj
  map _ := A.map _

/--
lemma `mem_op_obj_iff` / 引理 `mem_op_obj_iff`

English:
lemma mem_op_obj_iff
  given: {d : SimplexCategoryᵒᵖ} (x : X.op.obj d)
  proof: Iff.rfl

中文:
引理 mem_op_obj_iff
  条件: {d : SimplexCategoryᵒᵖ} (x : X.op.obj d)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_op_obj_iff {d : SimplexCategoryᵒᵖ} (x : X.op.obj d) :
    x in A.op.obj d ↔ X.opObjEquiv x in A.obj d := Iff.rfl

end SSet.Subcomplex
