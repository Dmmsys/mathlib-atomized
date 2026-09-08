/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Field structure on the multiplicative/additive opposite
-/

@[expose] public section

assert_not_exists RelIso

variable {α : Type*}

namespace MulOpposite

/-
**MulOpposite.instNNRatCast** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：{α : Type u_1} → [NNRatCast α] → NNRatCast αᵐᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance instNNRatCast [NNRatCast α] : NNRatCast αᵐᵒᵖ := ⟨fun q ↦ op q⟩
/-
**MulOpposite.instRatCast** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：{α : Type u_1} → [RatCast α] → RatCast αᵐᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance instRatCast [RatCast α] : RatCast αᵐᵒᵖ := ⟨fun q ↦ op q⟩

@[to_additive (attr := simp, norm_cast)]
/-
**MulOpposite.op_nnratCast** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：op_nnratCast [NNRatCast α] (q : Rat>=0) : op (q : α) = q
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma op_nnratCast [NNRatCast α] (q : ℚ≥0) : op (q : α) = q := rfl

@[to_additive (attr := simp, norm_cast)]
/-
**MulOpposite.unop_nnratCast** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：unop_nnratCast [NNRatCast α] (q : Rat>=0) : unop (q : αᵐᵒᵖ) = q
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unop_nnratCast [NNRatCast α] (q : ℚ≥0) : unop (q : αᵐᵒᵖ) = q := rfl

@[to_additive (attr := simp, norm_cast)]
/-
**MulOpposite.op_ratCast** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：op_ratCast [RatCast α] (q : Rat) : op (q : α) = q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma op_ratCast [RatCast α] (q : ℚ) : op (q : α) = q := rfl

@[to_additive (attr := simp, norm_cast)]
/-
**MulOpposite.unop_ratCast** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：unop_ratCast [RatCast α] (q : Rat) : unop (q : αᵐᵒᵖ) = q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unop_ratCast [RatCast α] (q : ℚ) : unop (q : αᵐᵒᵖ) = q := rfl
/-
**MulOpposite.instDivisionSemiring** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instDivisionSemiring [DivisionSemiring α] : DivisionSemiring αᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDivisionSemiring [DivisionSemiring α] : DivisionSemiring αᵐᵒᵖ where
  __ := instSemiring
  __ := instGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  nnratCast_def q := unop_injective <| by rw [unop_nnratCast, unop_div, unop_natCast, unop_natCast,
    NNRat.cast_def, div_eq_mul_inv, Nat.cast_comm]
/-
**MulOpposite.instDivisionRing** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instDivisionRing [DivisionRing α] : DivisionRing αᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDivisionRing [DivisionRing α] : DivisionRing αᵐᵒᵖ where
  __ := instRing
  __ := instDivisionSemiring
  qsmul := _
  qsmul_def := fun _ _ => rfl
  ratCast_def q := unop_injective <| by rw [unop_ratCast, Rat.cast_def, unop_div,
    unop_natCast, unop_intCast, Int.commute_cast, div_eq_mul_inv]
/-
**MulOpposite.instSemifield** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instSemifield [Semifield α] : Semifield αᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemifield [Semifield α] : Semifield αᵐᵒᵖ where
  __ := instCommSemiring
  __ := instDivisionSemiring
/-
**MulOpposite.instField** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instField [Field α] : Field αᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instField [Field α] : Field αᵐᵒᵖ where
  __ := instCommRing
  __ := instDivisionRing

end MulOpposite

namespace AddOpposite

/-
**AddOpposite.instDivisionSemiring** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instDivisionSemiring [DivisionSemiring α] : DivisionSemiring αᵃᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDivisionSemiring [DivisionSemiring α] : DivisionSemiring αᵃᵒᵖ where
  __ := instSemiring
  __ := instGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  nnratCast_def q := unop_injective <| by rw [unop_nnratCast, unop_div, unop_natCast, unop_natCast,
    NNRat.cast_def, div_eq_mul_inv]
/-
**AddOpposite.instDivisionRing** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instDivisionRing [DivisionRing α] : DivisionRing αᵃᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDivisionRing [DivisionRing α] : DivisionRing αᵃᵒᵖ where
  __ := instRing
  __ := instDivisionSemiring
  qsmul := _
  qsmul_def := fun _ _ => rfl
  ratCast_def q := unop_injective <| by rw [unop_ratCast, Rat.cast_def, unop_div, unop_natCast,
    unop_intCast, div_eq_mul_inv]
/-
**AddOpposite.instSemifield** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instSemifield [Semifield α] : Semifield αᵃᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemifield [Semifield α] : Semifield αᵃᵒᵖ where
  __ := instCommSemiring
  __ := instDivisionSemiring
/-
**AddOpposite.instField** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instField [Field α] : Field αᵃᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instField [Field α] : Field αᵃᵒᵖ where
  __ := instCommRing
  __ := instDivisionRing

end AddOpposite

