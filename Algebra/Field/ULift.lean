/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.ULift
public import Mathlib.Algebra.Ring.ULift

/-!
# Field instances for `ULift`

This file defines instances for fields, semifields, and related structures on `ULift` types.

(Recall `ULift α` is just a "copy" of a type `α` in a higher universe.)
-/

@[expose] public section

universe u
variable {α : Type u}

namespace ULift

/-
**ULift.instNNRatCast** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：instNNRatCast [NNRatCast α] : NNRatCast (ULift α) where nnratCast q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNNRatCast [NNRatCast α] : NNRatCast (ULift α) where nnratCast q := up q
/-
**ULift.instRatCast** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：instRatCast [RatCast α] : RatCast (ULift α) where ratCast q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRatCast [RatCast α] : RatCast (ULift α) where ratCast q := up q
/-
**ULift.up_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} [inst : NNRatCast α] (q : ℚ≥0), { down := ↑q } = ↑q
参数：q : ℚ≥0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma up_nnratCast [NNRatCast α] (q : ℚ≥0) : up (q : α) = q := rfl
/-
**ULift.down_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} [inst : NNRatCast α] (q : ℚ≥0), (↑q).down = ↑q
参数：q : ℚ≥0；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma down_nnratCast [NNRatCast α] (q : ℚ≥0) : down (q : ULift α) = q := rfl
/-
**ULift.up_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} [inst : RatCast α] (q : ℚ), { down := ↑q } = ↑q
参数：q : ℚ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma up_ratCast [RatCast α] (q : ℚ) : up (q : α) = q := rfl
/-
**ULift.down_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} [inst : RatCast α] (q : ℚ), (↑q).down = ↑q
参数：q : ℚ；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma down_ratCast [RatCast α] (q : ℚ) : down (q : ULift α) = q := rfl
/-
**ULift.divisionSemiring** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：divisionSemiring [DivisionSemiring α] : DivisionSemiring (ULift α) where n
nqsmul q x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance divisionSemiring [DivisionSemiring α] : DivisionSemiring (ULift α) where
  nnqsmul q x := up (DivisionSemiring.nnqsmul q x.down)
  nnqsmul_def _ _ := congrArg up <| DivisionSemiring.nnqsmul_def _ _
  nnratCast_def _ := congrArg up <| DivisionSemiring.nnratCast_def _
/-
**ULift.semifield** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：semifield [Semifield α] : Semifield (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semifield [Semifield α] : Semifield (ULift α) :=
  { ULift.divisionSemiring, ULift.commGroupWithZero with }
/-
**ULift.divisionRing** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：divisionRing [DivisionRing α] : DivisionRing (ULift α) where toRing
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance divisionRing [DivisionRing α] : DivisionRing (ULift α) where
  toRing := ring
  __ := groupWithZero
  nnqsmul q x := up (DivisionSemiring.nnqsmul q x.down)
  nnqsmul_def _ _ := congrArg up <| DivisionSemiring.nnqsmul_def _ _
  nnratCast_def _ := congrArg up <| DivisionSemiring.nnratCast_def _
  qsmul q x := up (DivisionRing.qsmul q x.down)
  qsmul_def _ _ := congrArg up <| DivisionRing.qsmul_def _ _
  ratCast_def _ := congrArg up <| DivisionRing.ratCast_def _
/-
**ULift.field** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：field [Field α] : Field (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance field [Field α] : Field (ULift α) := {}

end ULift

