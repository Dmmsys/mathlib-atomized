/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Order.Interval.Set.Defs

/-!
# The submonoid of positive elements
-/

@[expose] public section

assert_not_exists RelIso Ring

namespace Submonoid
variable (α) [MulZeroOneClass α] [PartialOrder α] [PosMulStrictMono α] [ZeroLEOneClass α]
  [NeZero (1 : α)] {a : α}

/--
Definition of `pos` / `pos` 的定义

English:
definition pos
  signature: : Submonoid α where
  body: Set.Ioi 0
  one_mem' := zero_lt_one
  mul_mem' := mul_pos

中文:
定义 pos
  签名: : 子幺半群 α where
  定义体: Set.Ioi 0
  one_mem' := zero_lt_one
  mul_mem' := mul_pos
-/
@[simps] def pos : Submonoid α where
  carrier := Set.Ioi 0
  one_mem' := zero_lt_one
  mul_mem' := mul_pos

variable {α}

/--
lemma `mem_pos` / 引理 `mem_pos`

English:
lemma mem_pos
  statement: a in pos α ↔ 0 < a
  proof: Iff.rfl

中文:
引理 mem_pos
  结论: a in pos α ↔ 0 < a
  证明: Iff.rfl
-/
@[simp] lemma mem_pos : a in pos α ↔ 0 < a := Iff.rfl

end Submonoid
